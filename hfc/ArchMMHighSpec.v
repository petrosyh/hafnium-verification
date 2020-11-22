From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     RelDec
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Data.Option
     Data.Monads.OptionMonad.


From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Require Import Coqlib sflib.

Require Import Values.
Require Import Integers.
Require Import Constant.
Require Import Lang.
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Require Import Maps.
Set Implicit Arguments.

(* Strategy of this high-level modeling is as follow. This file needs to support entire 
   and complete interfaces for Arch MM file, but with soem tweaks. *)

(* All functions in this file are basically figuring out something about a page table entry or 
   updating some flags of the entry. *)

(*** PTE TYPES *)
(** PTE has the following four types, so the abstract state of each PTE will be categorized as four. 

  A page table entry (PTE) will take one of the following forms:

  1. absent        : There is no mapping.
  2. invalid block : Represents a block that is not in the address space.
  3. valid block   : Represents a block that is in the address space.
  4. table         : Represents a reference to a table of PTEs.

A block entry maps the virtual address space covered by the table entry to some physical memory. A table (descriptor) entry points out the next level page table. Bascially, when we have 3 level page tables with 48-bit virtual address space, 4KB translation granule, they are used as follows.

level 0 : root page table and it will be either
- fault (all accesses to these address range trigger an abort)
- table (pointer to level 1 table) - Each entry in this table descriptor covers 512GB of address space

level 1-2 : 
- fault (all accesses to these address range trigger an abort)
- table (pointer to level 2-3 table)  - Each entry in this table descriptor covers 1GB or 2MB of address space
- block 

level 3:
- fault (all accesses to these address range trigger an abort)
- page descriptor (address) - Each entry in this page descriptor covers 4KB. This page descriptor is somewhat similar to the block entry at level 1-2, but their formats are different. See the below to figure the their differences. 

Basic idea of high-level modeling is making a data type for each entities of PTE (define inductive types that contains absent, invalid block, valid block, and table as its constructor). However, inductive types that only covers those types of PTEs may not sufficient. For each stage, their formats are slightly different (we discuss it in the below). Therefore, It is better for us to model them as different inductive types. In addition, "absent" differs from "not initialized". Therefore, we add one more inductive, which represents "not initialized".

In this sense, an inductive type for pate table entries may have the following constructors. Among all possible cases, we do not model block entires for intermediate levels because we believe they are not used in Hafnium (according to the mask value for output addresses, they should not use block entries for intermediate levels).

1. not initialized
2. absent 
3. invalid block
4. stage 1 table descriptor for the top and intermediate levels (max level is 2, so for level 0 and level 1)
5. stage 1 page descriptor for the bottom level (level 2)
6. stage 2 table descriptor for the top and intermediate levels (we assume the level is 3, so for level 0-2)
7. stage 2 page descriptor for the bottom level (level 3)

Different entries may have different attribute flags and values, and our high-level modeling needs to decide which attributes are associated with which constructors based on the possible format that each entry format can have. See the below for more details. 

*)

(*** Attributes for PTE *)
(**
Different page table entry may have differnt formats. I summarize key parts of them in the below, and they should be relfected in our page table entry representations. For more details about them, please look at D5 in [Arm Architecture Reference Manual Armv8, for Armv8-A architecture profile] (https://developer.arm.com/documentation/ddi0487/latest/). Some attribute flags might have conflicts with other flags. However, this file does not consider those possible inconsistency. That's because the design strategy of this file is not checking the consistency, but provides interface to handle page table entries. Providing consistent flag values is the obligation of a memory management module. 

-----
1. VMSAv8-64 translation table level 0 level 1 and level 2 descriptor format. 

The following diagram shows key features that we need to consider for translation table level 0 level 1 and level 2 descriptor format. The following diagram shows the ARMv8 level 0, level 1, and level 2 descriptor formats:

          63                       1 0
 INVALID [          IGNORED         |0]

        63              50 49      48 47                    n n-1        16 15     12  11                     2 1 0
 BLOCK [ upper attributes | reserved | output address [47:n] | reserved |nT| reserved | lower block attributes |0|1]

 - With the 4KB granule size, for the level 1 descriptor n is 30, and for the level 2 descriptor, n is 21.
 - With the 16KB granule size, for the level 2 descriptor, n is 25.
 - With the 64KB granule size,, for the level 2 descriptor, n is 29.

        63  62 61 60  59  58     52 51       48 47                                m m-1     12 11         2 1 0
 Table [(1)| (2) |(3)|(4)| IGNORED | reserved  | next-level table addresses [47:m] | reserved | IGNORED    |1|1]

 - Those things ((1)1 ... (4))are only for stage1.
 - Bits for them are reserved at stage2.
   (1) NSTable 
   (2) APTable
   (3) XNTable
   (4) PXNTable 

  - With the 4KB granule m is 12, wiht the 16KB granule m is 14, and with the 64KB granule, m is 16.
  - A level 0 table descriptor returens the address of the level 1 table.
  - A level 1 table descriptor returens the address of the level 2 table.
  - A level 2 table descriptor returens the address of the level 3 table.

-----
2. Armv8 translation table level 3 descriptor formats

 - For the 4KB granule size, each entry in a level 3 table describes the mapping of the associated 4KB input address range.
 - For the 16KB granule size, each entry in a level 3 table describes the mapping of the associated 16KB input address range.
 - For the 64KB granule size, each entry in a level 3 table describes the mapping of the associated 64KB input address range.

          63                       1 0
 INVALID [          IGNORED         |0]

          63                         1 0
 RESERVED [          reserved       |0 |1]

                    63              51 50      48 47                    12 11               2 1 0
 Page, 4KB granule [ upper attributes | reserved | output address [47:12] | lower attributes |1|1]

                     63              51 50      48 47                    14 13  12  11               2 1 0
 Page, 16KB granule [ upper attributes | reserved | output address [47:14] |(0)|(0)| lower attributes |1|1]

                     63              51 50      48 47                    16 15                  12 11               2 1 0
 Page, 64KB granule [ upper attributes | reserved | output address [47:16] | output address [51:48| lower attributes |1|1]

-----
3. Memory attribute fields in the VMSAv8-64 translation table format descriptors

- Table descriptor: Table descriptors for stage 2 translations do not include any attribute field. For a summary of the attribute fields in a stage 1 table descriptor, that define the attributes for the next lookup level, see the below.

- Block and page descriptors: These descriptors define memory attributes for the target block or page of memory. Stage 1 and
stage 2 translations have some differences in these attributes, see the below.

3.1. Next-level attributes in stage 1 VMSAv8-64 Table descriptors

In a Table descriptor for a stage 1 translation, bits[63:59] of the descriptor define the attributes for the next-level
translation table access, and bits[58:51] are IGNORED:

 63  62 61 60  59  58     51
[(1)| (2) |(3)|(4)| IGNORED | ... ]

(1) NSTable
(2) APTable 
(3) UXNTable or XNTable: UXNTable for a translation regime that can apply to execution at EL0, otherwise XNTable.
(4) PXNTable: Reserved for a translation regime that cannot apply to execution at EL0.

3.2. Attribute fields in stage 1 VMSAv8-64 Block and Page descriptors

 63  62  59 58     55 54  53  52  51  50          16 15  12 11 10 9  8 7  6 5  4      2   
[(1)| PBHA | IGNORED |(2)|(3)|(4)|(5)|GP| ...... |nT|  OA  |nG|AF| SH | AP |NS|AttrIndx| ... ]

(1) IGNORED
(2) UXN or XN: UXN for a translation regime that can apply to execution at EL0, otherwise XN.
(3) PXN: Reserved for a translation regime that cannot apply to execution at EL0.
(4) Contiguous
(5) DBM: Reserved if FEAT_HAFDBS is not implemented.


- PBHA: IGNORED if FEAT_HPDS2 is not implemented
- 58-55 IGNORED: Reserved for software use 
- 15-12 OA: Reserved if FEAT_LPA is not implemented.

3.3. Attribute fields in stage 2 VMSAv8-64 Block and Page descriptors

 63  62  59 58     55 54  53  52  51          16 15  12 11 10 9  8 7    6 5       2   
[(1)| PBHA | IGNORED | (2)  |(3)|(4)| ...... |nT|  OA  | 0|AF| SH | S2AP | MemAttr | ... ]

(1) Reserved for use by a System MMU
(2) XN[1:0]: Bit[53] is reserved if FEAT_XNX is not implemented. 
(3) Contiguous
(4) DBM: Reserved if FEAT_HAFDBS is not implemented.


- PBHA:  Bits [62:60] are IGNORED and reserved for use by System MMU if FEAT_HPDS2 is not implemented. Bits [59] is IGNORED if FEAT_HPDS2 is not implemented.
- 15-12 OA: Reserved if FEAT_LPA is not implemented.
 *)

(*** Address Translation *)

(* 
Address translation is not directly related to this file, but it helps us to find out which format is allowed in each level of page table descriptor entries. To see how translation works, see Appendix K7 Address Translation Examples in 
[Arm Architecture Reference Manual Armv8, for Armv8-A architecture profile] (https://developer.arm.com/documentation/ddi0487/latest/).

[XXX] - we can link more documents in here 
*)

(*** Comparison with Hafnium Arch MM *)
(** In the arch mm implementation of Hafnium, thereare multiple macro values either to represent those values or to assign, update, and find out attributes with the given PTE. Modeling PTE in a high-level spec requires distinguish them from each other and which one belongs to which type of page table entries. In this sense, following enumerates those values and describe the purpose of them.


(*** Additional Attributes *) 

1. The followings are for shareable conditions in stage 1 and stage 2. They are parameters of STAGE2_SH and STAGE1_SH. This implies that they are not directly modeled in the constructor. 
#define NON_SHAREABLE   UINT64_C(0)
#define OUTER_SHAREABLE UINT64_C(2)
#define INNER_SHAREABLE UINT64_C(3)

2. The followings are attribute bits on 0 and 1 on all ptes. But, we have divided them into different constructores, they can be directly inferred from each constructor in our inductive type. So, we do not add their values in our constructors. PTE_LEVEL0_BLOCK actually has the same value with PTE_TABLE. Thus, PTE_LEVEL0_BLOCK is actually pointing out not a block entry but a table descriptor. 
#define PTE_VALID        (UINT64_C(1) << 0)
#define PTE_LEVEL0_BLOCK (UINT64_C(1) << 1)
#define PTE_TABLE        (UINT64_C(1) << 1)

3. The followings are attribute fields in stage 1 VMSAv8-64 Block and Page descriptors
#define STAGE1_XN          (UINT64_C(1) << 54)
#define STAGE1_PXN         (UINT64_C(1) << 53)
#define STAGE1_CONTIGUOUS  (UINT64_C(1) << 52)
#define STAGE1_DBM         (UINT64_C(1) << 51)
#define STAGE1_NG          (UINT64_C(1) << 11)
#define STAGE1_AF          (UINT64_C(1) << 10)
#define STAGE1_SH(x)       ((x) << 8)
#define STAGE1_AP2         (UINT64_C(1) << 7)
#define STAGE1_AP1         (UINT64_C(1) << 6)
#define STAGE1_AP(x)       ((x) << 6)
#define STAGE1_NS          (UINT64_C(1) << 5)
#define STAGE1_ATTRINDX(x) ((x) << 2)

4. The followings are parameters of STAGE1_AP
#define STAGE1_READONLY  UINT64_C(2)
#define STAGE1_READWRITE UINT64_C(0)

5. The followings are parameters of STAGE1_ATTRINDX
#define STAGE1_DEVICEINDX UINT64_C(0)
#define STAGE1_NORMALINDX UINT64_C(1)

6.  The followings are attribute fields in stage 2 VMSAv8-64 Block and Page descriptors
#define STAGE2_XN(x)      ((x) << 53)
#define STAGE2_CONTIGUOUS (UINT64_C(1) << 52)
#define STAGE2_DBM        (UINT64_C(1) << 51)
#define STAGE2_AF         (UINT64_C(1) << 10)
#define STAGE2_SH(x)      ((x) << 8)
#define STAGE2_S2AP(x)    ((x) << 6)

7. The followings are parameters of STAGE2_XN, and a mask value for XN
#define STAGE2_EXECUTE_ALL  UINT64_C(0)
#define STAGE2_EXECUTE_EL0  UINT64_C(1)
#define STAGE2_EXECUTE_NONE UINT64_C(2)
#define STAGE2_EXECUTE_EL1  UINT64_C(3)
#define STAGE2_EXECUTE_MASK UINT64_C(3) - This is a mask value 

8. The followings are next-level attributes in stage 1 VMSAv8-64 Table descriptors
/* Table attributes only apply to stage 1 translations. */
#define TABLE_NSTABLE  (UINT64_C(1) << 63)
#define TABLE_APTABLE1 (UINT64_C(1) << 62)
#define TABLE_APTABLE0 (UINT64_C(1) << 61)
#define TABLE_XNTABLE  (UINT64_C(1) << 60)
#define TABLE_PXNTABLE (UINT64_C(1) << 59)

9. The followings are software defined attributes fields for stage 2 VMSAv8-64 Block and Page descriptors. 
/* The following are stage-2 software defined attributes. */
#define STAGE2_SW_OWNED     (UINT64_C(1) << 55)
#define STAGE2_SW_EXCLUSIVE (UINT64_C(1) << 56)

10.The followings are parameters of MEMATTR in the below
/* The following are stage-2 memory attributes for normal memory. */
#define STAGE2_DEVICE_MEMORY UINT64_C(0)
#define STAGE2_NONCACHEABLE  UINT64_C(1)
#define STAGE2_WRITETHROUGH  UINT64_C(2)
#define STAGE2_WRITEBACK     UINT64_C(3)

11. The followings are parameters of MEMATTR in the below
/* The following are stage-2 memory attributes for device memory. */
#define STAGE2_MEMATTR_DEVICE_nGnRnE UINT64_C(0)
#define STAGE2_MEMATTR_DEVICE_nGnRE  UINT64_C(1)
#define STAGE2_MEMATTR_DEVICE_nGRE   UINT64_C(2)
#define STAGE2_MEMATTR_DEVICE_GRE    UINT64_C(3)

12. Attribute fields in stage 2 VMSAv8-64 Block and Page descriptors
/* The following construct and destruct stage-2 memory attributes. */
#define STAGE2_MEMATTR(outer, inner) ((((outer) << 2) | (inner)) << 2)
#define STAGE2_MEMATTR_TYPE_MASK UINT64_C(3 << 4)

13. The followings are parameters of STAGE2_S2AP
#define STAGE2_ACCESS_READ  UINT64_C(1)
#define STAGE2_ACCESS_WRITE UINT64_C(2)

14. The followings are a cahche word size and and tlb related things. we will ignore them in this version. 
#define CACHE_WORD_SIZE 4

/**
 * Threshold number of pages in TLB to invalidate after which we invalidate all
 * TLB entries on a given level.
 * Constant is the number of pointers per page table entry, also used by Linux.
 */
#define MAX_TLBI_OPS  MM_PTE_PER_PAGE

/* clang-format on */

#define tlbi(op)                               \
	do {                                   \
		__asm__ volatile("tlbi " #op); \
	} while (0)
#define tlbi_reg(op, reg)                                              \
	do {                                                           \
		__asm__ __volatile__("tlbi " #op ", %0" : : "r"(reg)); \
	} while (0)

15. The following is a address mask value. Our high-level modeling does not need to explicitly model them, but the modeling requires a safety check for them.  
/** Mask for the address bits of the pte. */
#define PTE_ADDR_MASK \
	(((UINT64_C(1) << 48) - 1) & ~((UINT64_C(1) << PAGE_BITS) - 1))

16. A mask value for attributes.
/** Mask for the attribute bits of the pte. */
#define PTE_ATTR_MASK (~(PTE_ADDR_MASK | (UINT64_C(1) << 1)))
 *)

(* XXX : Add it into a library file *)
Section PTreePtr.

  Definition PtrTree := (PTree.t (ZTree.t positive)).
  
  Definition PtrTree_set (b: block) (ofs: ptrofs) (v: positive) (map: PtrTree) :=
    let zt := match PTree.get b map with
              | Some zt => zt
              | None => (ZTree.empty positive)
              end in
    PTree.set b (ZTree.set (Ptrofs.unsigned ofs) v zt) map
  .
  
  Definition PtrTree_get (b: block) (ofs: ptrofs) (map: PtrTree) :=
    match PTree.get b map with
    | Some zt => ZTree.get (Ptrofs.unsigned ofs) zt
    | None => None
    end
  .
  
  Definition PtrTree_remove (b: block) (ofs: ptrofs) (map: PtrTree) :=
    match PTree.get b map with
    | Some zt => PTree.set b (ZTree.remove (Ptrofs.unsigned ofs) zt) map
    | None => map
    end
  .

  Inductive PtrVal :=
  | ptr_val (b: block) (ofs: ptrofs).
  
End PTreePtr.  

Section ABSTSTATE.
  
  (* abstract type definitions *)
  Inductive BLOCK_SHAREABLE :=
  | NON_SHAREABLE | OUTER_SHAREABLE | INNER_SHAREABLE.

  Inductive STAGE1_BLOCK_PERM :=
  | STAGE1_READONLY | STAGE1_READWRITE.

  Inductive STAGE1_BLOCK_TYPE :=
  | STAGE1_DEVICEINDX | STAGE1_NORMALINDX.

  Record Stage1BlockAttributes :=
    mkStage1BlockAttributes {
        STAGE1_XN: bool;
        STAGE1_PXN: bool;
        STAGE1_CONTIGUOUS: bool;
        STAGE1_DBM: bool;
        STAGE1_NG: bool;
        STAGE1_AF: bool;
        STAGE1_SH: BLOCK_SHAREABLE;
        STAGE1_AP: STAGE1_BLOCK_PERM;
        STAGE1_NS: bool;
        STAGE1_ATTRINDX: STAGE1_BLOCK_TYPE
      }.

  Definition init_stage1_block_attributes :=
    mkStage1BlockAttributes false false false false false false NON_SHAREABLE STAGE1_READWRITE false STAGE1_DEVICEINDX.
  
  Record Stage1TableAttributes :=
    mkStage1TableAttributes {
        TABLE_NSTABLE: bool;
        TABLE_APTABLE1: bool;
        TABLE_APTABLE0: bool;
        TABLE_XNTABLE: bool;
        TABLE_PXNTABLE: bool
      }.

  Definition init_stage1_table_attributes := mkStage1TableAttributes false false false false false.

  Inductive STAGE2_BLOCK_EXECUTE_MODE :=
  | STAGE2_EXECUTE_ALL
  | STAGE2_EXECUTE_EL0
  | STAGE2_EXECUTE_NONE
  | STAGE2_EXECUTE_EL1.

  Inductive STAGE2_BLOCK_PERM :=
  | STAGE2_ACCESS_NOPERM | STAGE2_ACCESS_READ | STAGE2_ACCESS_WRITE | STAGE2_ACCESS_READWRITE.

  Inductive STAGE2_MEMATTR_VALUES :=
  | MEMATTR_ZERO | MEMATTR_ONE | MEMATTR_TWO | MEMATTR_THREE.

  (* The following are stage-2 memory attributes for normal memory *)
  Inductive MMATTR_STAGE2_NORMAL_MEMORY_ATTR :=
  | STAGE2_DEVICE_MEMORY
  | STAGE2_NONCACHEABLE
  | STAGE2_WRITETHROUGH
  | STAGE2_WRITEBACK.

  (* The following are stage-2 memory attributes for device memory. *)
  Inductive MMATTR_STAGE2_DEVICE_MEMORY_ATTR :=
  | STAGE2_MEMATTR_DEVICE_nGnRnE
  | STAGE2_MEMATTR_DEVICE_nGnRE
  | STAGE2_MEMATTR_DEVICE_nGRE
  | STAGE2_MEMATTR_DEVICE_GRE.

  Inductive STAGE2_MEMAATR_TYPES := 
  | MEMATTR_TYPES_NORMAL (attr: MMATTR_STAGE2_NORMAL_MEMORY_ATTR) 
  | MEMATTR_TYPES_DEVICE (attr: MMATTR_STAGE2_DEVICE_MEMORY_ATTR).

  (* The following function defines only two things that are used in arch mm module now. It can be extended later. *)
  Definition STAGE2_MEMATTR_GEN (outer inner: STAGE2_MEMAATR_TYPES) : option STAGE2_MEMATTR_VALUES :=
    match (outer, inner) with
    | (MEMATTR_TYPES_NORMAL STAGE2_DEVICE_MEMORY, 
       MEMATTR_TYPES_DEVICE STAGE2_MEMATTR_DEVICE_GRE) => Some MEMATTR_ZERO
    | (MEMATTR_TYPES_NORMAL STAGE2_WRITEBACK, 
       MEMATTR_TYPES_NORMAL STAGE2_WRITEBACK) => Some MEMATTR_TWO
    | _ => None
    end.

  Record Stage2BlockAttributes :=
    mkStage2BlockAttributes {
        STAGE2_XN: STAGE2_BLOCK_EXECUTE_MODE;
        STAGE2_CONTIGUOUS: bool;
        STAGE2_DBM: bool;
        STAGE2_SW_OWNED: bool;
        STAGE2_SW_EXCLUSIVE: bool;            
        STAGE2_AF: bool;
        STAGE2_SH: BLOCK_SHAREABLE;
        STAGE2_S2AP: STAGE2_BLOCK_PERM;
        STAGE2_MEMATTR: STAGE2_MEMATTR_VALUES
      }.

  Definition init_stage2_block_attributes := mkStage2BlockAttributes STAGE2_EXECUTE_ALL false false false false false
                                                                     NON_SHAREABLE STAGE2_ACCESS_NOPERM MEMATTR_ZERO.

  Inductive PTE_TYPES :=
  | UNDEFINED (* not initialized *)
  | ABSENT
  | INVALID_BLOCK (* invalid block. XXX: we may be able to delete it and can combine this one with absent one *)
  | STAGE1_TABLE (output_address : Z) (attributes: Stage1TableAttributes)
  | STAGE1_PAGE (output_address : Z) (attributes: Stage1BlockAttributes)
  | STAGE2_TABLE (output_address : Z)
  | STAGE2_PAGE (output_address : Z) (attributes: Stage2BlockAttributes).

  Inductive CURRENT_STAGE := STAGE1 | STAGE2.
  
  Record ArchMMAbstractState :=
    mkArchMMAbstractState {
        pte_pool: PMap.t PTE_TYPES;
        addr_to_pte_pool_key: PtrTree;
        pte_pool_key_to_addr: PMap.t PtrVal;
        next_id: positive;
        stage: CURRENT_STAGE
      }.

End ABSTSTATE.

Section FLAG_TO_VALUE_and_VALUE_TO_FLAG.

  Definition Stage1TableAttributes_to_ATTR_VALUES (stage1_table_attributes : Stage1TableAttributes) : Z :=
    match stage1_table_attributes with
    |  mkStage1TableAttributes nstable aptable1 aptable2 xntable pxntable
       => let nstable_to_z := if (nstable) then Z.shiftl 1 63 else 0 in 
         let aptable1_to_z := if (aptable1) then Z.shiftl 1 62 else 0 in
         let aptable2_to_z := if (aptable2) then Z.shiftl 1 61 else 0 in
         let xntable_to_z := if (xntable) then Z.shiftl 1 60 else 0 in
         let pxntable_to_z := if (pxntable) then Z.shiftl 1 59 else 0 in
         nstable_to_z + aptable1_to_z + aptable2_to_z + xntable_to_z + pxntable_to_z
    end.

  Definition ATTR_VALUES_to_Stage1TableAttributes (stage1_table_attributes_value : Z) : Stage1TableAttributes :=
    let nstable_of_z := if (zeq 0 (Z.land (Z.shiftl 1 63) stage1_table_attributes_value)) then false else true in
    let aptable1_of_z := if (zeq 0 (Z.land (Z.shiftl 1 62) stage1_table_attributes_value)) then false else true in
    let aptable2_of_z := if (zeq 0 (Z.land (Z.shiftl 1 61) stage1_table_attributes_value)) then false else true in
    let xntable_of_z := if (zeq 0 (Z.land (Z.shiftl 1 60) stage1_table_attributes_value)) then false else true in
    let pxntable_of_z := if (zeq 0 (Z.land (Z.shiftl 1 59) stage1_table_attributes_value)) then false else true in
    mkStage1TableAttributes nstable_of_z aptable1_of_z aptable2_of_z xntable_of_z pxntable_of_z.

  Definition Stage1BlockAttributes_to_ATTR_VALUES (stage1_block_attributes : Stage1BlockAttributes) : Z :=
    match stage1_block_attributes with
    | mkStage1BlockAttributes xn pxn contiguous dbm ng af sh ap ns attrindx
      => let xn_to_n := if (xn) then Z.shiftl 1 54 else 0 in
        let pxn_to_n := if (pxn) then Z.shiftl 1 53 else 0 in
        let contiguous_to_n := if (contiguous) then Z.shiftl 1 52 else 0 in
        let dbm_to_n := if (dbm) then Z.shiftl 1 51 else 0 in
        let ng_to_n := if (ng) then Z.shiftl 1 11 else 0 in
        let af_to_n := if (af) then Z.shiftl 1 10 else 0 in
        let sh_to_n := match sh with
                       | NON_SHAREABLE => Z.shiftl 0 8
                       | OUTER_SHAREABLE => Z.shiftl 2 8
                       | INNER_SHAREABLE => Z.shiftl 3 8
                       end in
        let ap_to_n := match ap with
                       | STAGE1_READONLY => Z.shiftl 2 6
                       | STAGE1_READWRITE => Z.shiftl 0 6
                       end in
        let ns_to_n := if (ns) then Z.shiftl 1 5 else 0 in
        let attrindx_to_n := match attrindx with
                             | STAGE1_DEVICEINDX => Z.shiftl 0 2
                             | STAGE1_NORMALINDX => Z.shiftl 1 2
                             end in
        xn_to_n + pxn_to_n + contiguous_to_n + dbm_to_n + ng_to_n + af_to_n + sh_to_n + ap_to_n + ns_to_n + attrindx_to_n
    end.
           
  Definition ATTR_VALUES_to_Stage1BlockAttributes (stage1_block_attributes_value : Z) : option Stage1BlockAttributes :=
    let xn_of_z := if (zeq 0 (Z.land (Z.shiftl 1 54) stage1_block_attributes_value)) then false else true in
    let pxn_of_z := if (zeq 0 (Z.land (Z.shiftl 1 53) stage1_block_attributes_value)) then false else true in
    let contiguous_of_z := if (zeq 0 (Z.land (Z.shiftl 1 52) stage1_block_attributes_value)) then false else true in
    let dbm_of_z := if (zeq 0 (Z.land (Z.shiftl 1 51) stage1_block_attributes_value)) then false else true in
    let ng_of_z := if (zeq 0 (Z.land (Z.shiftl 1 11) stage1_block_attributes_value)) then false else true in
    let af_of_z := if (zeq 0 (Z.land (Z.shiftl 1 10) stage1_block_attributes_value)) then false else true in
    let sh_of_z := if (zeq 0 (Z.land (Z.shiftl 1 8) stage1_block_attributes_value))
                   then if (zeq 0 (Z.land (Z.shiftl 2 8) stage1_block_attributes_value))
                        then (* 0 << 8 *) Some NON_SHAREABLE
                        else (* 2 << 8 *) Some OUTER_SHAREABLE
                   else if (zeq 0 (Z.land (Z.shiftl 2 8) stage1_block_attributes_value))
                        then (* 1 << 8 *) None
                        else (* 3 << 8 *) Some INNER_SHAREABLE in
    let ap_of_z := if (zeq 0 (Z.land (Z.shiftl 1 6) stage1_block_attributes_value))
                   then if (zeq 0 (Z.land (Z.shiftl 2 6) stage1_block_attributes_value))
                        then (* 0 << 6 *) Some STAGE1_READWRITE
                        else (* 2 << 6 *) Some STAGE1_READONLY
                   else (* 1 << 6 or 3 << 6 *) None in
    let ns_of_z := if (zeq 0 (Z.land (Z.shiftl 1 5)  stage1_block_attributes_value)) then false else true in
    let attrindx_of_n := if (zeq 0 (Z.land (Z.shiftl 1 2) stage1_block_attributes_value))
                         then if (zeq 0 (Z.land (Z.shiftl 2 2) stage1_block_attributes_value))
                              then (* 0 << 2 *) Some STAGE1_DEVICEINDX
                              else (* 2 << 2 *) None
                         else if (zeq 0 (Z.land (Z.shiftl 2 2) stage1_block_attributes_value))
                              then (* 1 << 2 *) Some STAGE1_NORMALINDX
                              else (* 3 << 2 *) None in
    match (sh_of_z, ap_of_z, attrindx_of_n) with
    | (Some sh_of_z', Some ap_of_z', Some attrindx_of_z') =>
      Some (mkStage1BlockAttributes xn_of_z pxn_of_z contiguous_of_z dbm_of_z
                                    ng_of_z af_of_z sh_of_z' ap_of_z' ns_of_z attrindx_of_z')
    | (_, _, _) => None
    end.

  Definition Stage2BlockAttributes_to_ATTR_VALUES (stage2_block_attributes : Stage2BlockAttributes) : Z :=
    match stage2_block_attributes with
    | mkStage2BlockAttributes xn contiguous dbm sw_owned sw_exclusive af sh s2ap memattr
      => let xn_to_n := match xn with
                       | STAGE2_EXECUTE_ALL => (Z.shiftl 0 53)
                       | STAGE2_EXECUTE_EL0 => (Z.shiftl 1 53)
                       | STAGE2_EXECUTE_NONE => (Z.shiftl 2 53)
                       | STAGE2_EXECUTE_EL1 => (Z.shiftl 3 53)
                       end in
        let contiguous_to_n := if (contiguous) then Z.shiftl 1 52 else 0 in
        let dbm_to_n := if (dbm) then Z.shiftl 1 51 else 0 in
        let sw_owned_n := if (sw_owned) then Z.shiftl 1 55 else 0 in
        let sw_exclusive := if (sw_exclusive) then Z.shiftl 1 56 else 0 in 
        let af_to_n := if (dbm) then Z.shiftl 1 10 else 0 in
        let sh_to_n := match sh with
                       | NON_SHAREABLE => Z.shiftl 0 8
                       | OUTER_SHAREABLE => Z.shiftl 2 8
                       | INNER_SHAREABLE => Z.shiftl 3 8
                       end in
        let s2ap_to_n := match s2ap with
                         | STAGE2_ACCESS_NOPERM => Z.shiftl 0 6
                         | STAGE2_ACCESS_READ => Z.shiftl 1 6
                         | STAGE2_ACCESS_WRITE => Z.shiftl 2 6
                         | STAGE2_ACCESS_READWRITE => Z.shiftl 3 6
                         end in 
        let memattr_to_n := match memattr with
                            | MEMATTR_ZERO => Z.shiftl 0 2
                            | MEMATTR_ONE => Z.shiftl 1 2
                            | MEMATTR_TWO => Z.shiftl 2 2
                            | MEMATTR_THREE => Z.shiftl 3 2
                            end in
        xn_to_n + contiguous_to_n + dbm_to_n + af_to_n + sh_to_n + s2ap_to_n + memattr_to_n
    end.

  Definition ATTR_VALUES_to_Stage2BlockAttributes (stage2_block_attributes_value : Z) : option Stage2BlockAttributes :=
    let xn_of_z := if (zeq 0 (Z.land (Z.shiftl 1 53) stage2_block_attributes_value))
                   then if (zeq 0 (Z.land (Z.shiftl 2 53) stage2_block_attributes_value))
                        then (* 0 << 53 *) STAGE2_EXECUTE_ALL
                        else (* 2 << 53 *) STAGE2_EXECUTE_NONE
                   else if (zeq 0 (Z.land (Z.shiftl 2 53) stage2_block_attributes_value))
                        then (* 1 << 53 *) STAGE2_EXECUTE_EL0
                        else (* 3 << 53 *) STAGE2_EXECUTE_EL1 in
    let contiguous_of_z := if (zeq 0 (Z.land (Z.shiftl 1 52) stage2_block_attributes_value)) then false else true in
    let dbm_of_z := if (zeq 0 (Z.land (Z.shiftl 1 51) stage2_block_attributes_value)) then false else true in
    let sw_owned_of_z := if (zeq 0 (Z.land (Z.shiftl 1 55) stage2_block_attributes_value)) then false else true in
    let sw_exclusive_of_z := if (zeq 0 (Z.land (Z.shiftl 1 56) stage2_block_attributes_value)) then false else true in
    let af_of_z := if (zeq 0 (Z.land (Z.shiftl 1 10) stage2_block_attributes_value)) then false else true in
    let sh_of_z := if (zeq 0 (Z.land (Z.shiftl 1 8) stage2_block_attributes_value))
                   then if (zeq 0 (Z.land (Z.shiftl 2 8) stage2_block_attributes_value))
                        then (* 0 << 8 *) Some NON_SHAREABLE
                        else (* 2 << 8 *) Some OUTER_SHAREABLE
                   else if (zeq 0 (Z.land (Z.shiftl 2 8) stage2_block_attributes_value))
                        then (* 1 << 8 *) None
                        else (* 3 << 8 *) Some INNER_SHAREABLE in
    let s2ap_of_z := if (zeq 0 (Z.land (Z.shiftl 1 6) stage2_block_attributes_value))
                   then if (zeq 0 (Z.land (Z.shiftl 2 6) stage2_block_attributes_value))
                        then (* 0 << 6 *) STAGE2_ACCESS_NOPERM
                        else (* 2 << 6 *) STAGE2_ACCESS_WRITE
                   else if (zeq 0 (Z.land (Z.shiftl 2 6) stage2_block_attributes_value))
                        then (* 1 << 6 *) STAGE2_ACCESS_READ
                        else (* 3 << 6 *) STAGE2_ACCESS_READWRITE in
    let memattr_of_z := if (zeq 0 (Z.land (Z.shiftl 1 2) stage2_block_attributes_value))
                        then if (zeq 0 (Z.land (Z.shiftl 2 2) stage2_block_attributes_value))
                             then (* 0 << 2 *) MEMATTR_ZERO
                             else (* 2 << 2 *) MEMATTR_TWO
                        else if (zeq 0 (Z.land (Z.shiftl 2 2) stage2_block_attributes_value))
                             then (* 1 << 2 *) MEMATTR_ONE
                             else (* 3 << 2 *) MEMATTR_THREE in
    match sh_of_z with
    | Some sh_of_z' =>
      Some (mkStage2BlockAttributes xn_of_z contiguous_of_z dbm_of_z af_of_z sw_owned_of_z sw_exclusive_of_z
                                    sh_of_z' s2ap_of_z memattr_of_z)
    | None => None
    end.
        
  Definition PTE_TYPES_to_ATTR_VALUES (pte_value : PTE_TYPES) : Z :=
    match pte_value with
    | UNDEFINED => 0
    | ABSENT => 0
    | INVALID_BLOCK => 0
    | STAGE1_TABLE _ attributes => Stage1TableAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 1 + Z.shiftl 1 0
    | STAGE1_PAGE _ attributes => Stage1BlockAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 1 + Z.shiftl 1 0 
    | STAGE2_TABLE _ => Z.shiftl 1 1 + Z.shiftl 1 0
    | STAGE2_PAGE _ attributes => Stage2BlockAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 1 + Z.shiftl 1 0
    end.

  Definition PTE_TYPES_to_VALUES (pte : PTE_TYPES) : Z :=
    match pte with
    | UNDEFINED => 0
    | ABSENT => 0
    | INVALID_BLOCK => 0
    | STAGE1_TABLE oa attr => Z.shiftl oa 12 + Stage1TableAttributes_to_ATTR_VALUES attr + Z.shiftl 1 1 + Z.shiftl 1 0
    | STAGE1_PAGE oa attr => Z.shiftl oa 12 + Stage1BlockAttributes_to_ATTR_VALUES attr + Z.shiftl 1 1 + Z.shiftl 1 0
    | STAGE2_TABLE oa => Z.shiftl oa 12 + Z.shiftl 1 1 + Z.shiftl 1 0
    | STAGE2_PAGE oa attr => Z.shiftl oa 12 + Stage2BlockAttributes_to_ATTR_VALUES attr + Z.shiftl 1 1 + Z.shiftl 1 0
    end.

End FLAG_TO_VALUE_and_VALUE_TO_FLAG.

Section SPECS.

Variable st: ArchMMAbstractState.
Context {eff : Type -> Type}.
Context {HasEvent : Event -< eff}.

(*
/**
 * Returns the encoding of a page table entry that isn't present.
 */
pte_t arch_mm_absent_pte(uint8_t level)
{
	(void)level;
	return 0;
}
*)

Definition arch_mm_absent_pte (level: val) : itree eff (ArchMMAbstractState * val) :=
  match level with
  | Vcomp (Vlong level) =>
    Ret (st, Vcomp (Vlong  (Int64.repr 0)))
  | _ => triggerNB "level <> integer"
  end
.

(*  
/**
 * Converts a physical address to a table PTE.
 *
 * The spec says that 'Table descriptors for stage 2 translations do not
 * include any attribute field', so we don't take any attributes as arguments.
 */
pte_t arch_mm_table_pte(uint8_t level, paddr_t pa)
{
	/* This is the same for all levels on aarch64. */
	(void)level;
	return pa_addr(pa) | PTE_TABLE | PTE_VALID;
}
 *)

Definition arch_mm_table_pte (level pa: val) : itree eff (ArchMMAbstractState * val) :=
  match level with
  | Vcomp (Vlong level) =>
    match pa with
    | Vcomp (Vptr b ptrofs) =>
      match PtrTree_get b ptrofs st.(addr_to_pte_pool_key) with
      | Some key =>
        let new_pte := 
            match st.(stage), PMap.get key st.(pte_pool) with
            | STAGE1, ABSENT  =>
              if zeq (Int64.unsigned level) 2
              then STAGE1_PAGE 0 init_stage1_block_attributes
              else STAGE1_TABLE 0 init_stage1_table_attributes
            | STAGE2, ABSENT  =>
              if zeq (Int64.unsigned level) 3
              then STAGE2_PAGE 0 init_stage2_block_attributes
              else STAGE2_TABLE 0
            | _, pte => pte
            end in
        let new_pte_pool := PMap.set key new_pte st.(pte_pool) in
        let new_st := mkArchMMAbstractState new_pte_pool st.(addr_to_pte_pool_key) st.(pte_pool_key_to_addr) st.(next_id) st.(stage) in
        Ret (new_st, Vcomp (Vlong (Int64.repr (PTE_TYPES_to_VALUES new_pte))))
      | _ => triggerNB "no pte table"
      end
    | _ => triggerNB "pa <> pointer"
    end
  | _ => triggerNB "level <> integer"
  end
.

(*  
/**
 * Converts a physical address to a block PTE.
 *
 * The level must allow block entries.
 */
pte_t arch_mm_block_pte(uint8_t level, paddr_t pa, uint64_t attrs)
{
	pte_t pte = pa_addr(pa) | attrs;

	if (level == 0) {
		/* A level 0 'block' is actually a page entry. */
		pte |= PTE_LEVEL0_BLOCK;
	}
	return pte;
}
*)


(*
/**
 * Specifies whether block mappings are acceptable at the given level.
 *
 * Level 0 must allow block entries.
 */
bool arch_mm_is_block_allowed(uint8_t level)
{
	return level <= 2;
}
*)


(*
/**
 * Determines if the given pte is present, i.e., if it is valid or it is invalid
 * but still holds state about the memory so needs to be present in the table.
 */
bool arch_mm_pte_is_present(pte_t pte, uint8_t level)
{
	return arch_mm_pte_is_valid(pte, level) || (pte & STAGE2_SW_OWNED) != 0;
}
*)

(*
/**
 * Determines if the given pte is valid, i.e., if it points to another table,
 * to a page, or a block of pages that can be accessed.
 */
bool arch_mm_pte_is_valid(pte_t pte, uint8_t level)
{
	(void)level;
	return (pte & PTE_VALID) != 0;
}
*)

(*
/**
 * Determines if the given pte references a block of pages.
 */
bool arch_mm_pte_is_block(pte_t pte, uint8_t level)
{
	/* We count pages at level 0 as blocks. */
	return arch_mm_is_block_allowed(level) &&
	       (level == 0 ? (pte & PTE_LEVEL0_BLOCK) != 0
			   : arch_mm_pte_is_present(pte, level) &&
				     !arch_mm_pte_is_table(pte, level));
}
*)

(*
/**
 * Determines if the given pte references another table.
 */
bool arch_mm_pte_is_table(pte_t pte, uint8_t level)
{
	return level != 0 && arch_mm_pte_is_valid(pte, level) &&
	       (pte & PTE_TABLE) != 0;
}
*)

(*
static uint64_t pte_addr(pte_t pte)
{
	return pte & PTE_ADDR_MASK;
}
*)

(*
/**
 * Clears the given physical address, i.e., clears the bits of the address that
 * are not used in the pte.
 */
paddr_t arch_mm_clear_pa(paddr_t pa)
{
	return pa_init(pte_addr(pa_addr(pa)));
}
*)

(*
/**
 * Extracts the physical address of the block referred to by the given page
 * table entry.
 */
paddr_t arch_mm_block_from_pte(pte_t pte, uint8_t level)
{
	(void)level;
	return pa_init(pte_addr(pte));
}
*)

(*
/**
 * Extracts the physical address of the page table referred to by the given page
 * table entry.
 */
paddr_t arch_mm_table_from_pte(pte_t pte, uint8_t level)
{
	(void)level;
	return pa_init(pte_addr(pte));
}
*)

(*
/**
 * Extracts the architecture-specific attributes applies to the given page table
 * entry.
 */
uint64_t arch_mm_pte_attrs(pte_t pte, uint8_t level)
{
	(void)level;
	return pte & PTE_ATTR_MASK;
}
*)

(*
/**
 * Returns the encoding of a page table entry that isn't present.
 */
pte_t arch_mm_absent_pte(uint8_t level)
{
	(void)level;
	return 0;
}
*)

(*
/**
 * Converts a physical address to a table PTE.
 *
 * The spec says that 'Table descriptors for stage 2 translations do not
 * include any attribute field', so we don't take any attributes as arguments.
 */
pte_t arch_mm_table_pte(uint8_t level, paddr_t pa)
{
	/* This is the same for all levels on aarch64. */
	(void)level;
	return pa_addr(pa) | PTE_TABLE | PTE_VALID;
}
*)

(*
/**
 * Converts a physical address to a block PTE.
 *
 * The level must allow block entries.
 */
pte_t arch_mm_block_pte(uint8_t level, paddr_t pa, uint64_t attrs)
{
	pte_t pte = pa_addr(pa) | attrs;

	if (level == 0) {
		/* A level 0 'block' is actually a page entry. */
		pte |= PTE_LEVEL0_BLOCK;
	}
	return pte;
}
*)

(*
/**
 * Specifies whether block mappings are acceptable at the given level.
 *
 * Level 0 must allow block entries.
 */
bool arch_mm_is_block_allowed(uint8_t level)
{
	return level <= 2;
}
*)

(*
/**
 * Determines if the given pte is present, i.e., if it is valid or it is invalid
 * but still holds state about the memory so needs to be present in the table.
 */
bool arch_mm_pte_is_present(pte_t pte, uint8_t level)
{
	return arch_mm_pte_is_valid(pte, level) || (pte & STAGE2_SW_OWNED) != 0;
}
*)

(* 
/**
 * Determines if the given pte is valid, i.e., if it points to another table,
 * to a page, or a block of pages that can be accessed.
 */
bool arch_mm_pte_is_valid(pte_t pte, uint8_t level)
{
	(void)level;
	return (pte & PTE_VALID) != 0;
}
*)

(*
/**
 * Determines if the given pte references a block of pages.
 */
bool arch_mm_pte_is_block(pte_t pte, uint8_t level)
{
	/* We count pages at level 0 as blocks. */
	return arch_mm_is_block_allowed(level) &&
	       (level == 0 ? (pte & PTE_LEVEL0_BLOCK) != 0
			   : arch_mm_pte_is_present(pte, level) &&
				     !arch_mm_pte_is_table(pte, level));
}
*)

(*
/**
 * Determines if the given pte references another table.
 */
bool arch_mm_pte_is_table(pte_t pte, uint8_t level)
{
	return level != 0 && arch_mm_pte_is_valid(pte, level) &&
	       (pte & PTE_TABLE) != 0;
}
*)

(*
static uint64_t pte_addr(pte_t pte)
{
	return pte & PTE_ADDR_MASK;
}
*)

(*
/**
 * Clears the given physical address, i.e., clears the bits of the address that
 * are not used in the pte.
 */
paddr_t arch_mm_clear_pa(paddr_t pa)
{
	return pa_init(pte_addr(pa_addr(pa)));
}
*)

(*
/**
 * Extracts the physical address of the block referred to by the given page
 * table entry.
 */
paddr_t arch_mm_block_from_pte(pte_t pte, uint8_t level)
{
	(void)level;
	return pa_init(pte_addr(pte));
}
*)

(*
/**
 * Extracts the physical address of the page table referred to by the given page
 * table entry.
 */
paddr_t arch_mm_table_from_pte(pte_t pte, uint8_t level)
{
	(void)level;
	return pa_init(pte_addr(pte));
}
*)

(*
/**
 * Extracts the architecture-specific attributes applies to the given page table
 * entry.
 */
uint64_t arch_mm_pte_attrs(pte_t pte, uint8_t level)
{
	(void)level;
	return pte & PTE_ATTR_MASK;
}
*)

  
(*
/**
 * Given the attrs from a table at some level and the attrs from all the blocks
 * in that table, returns equivalent attrs to use for a block which will replace
 * the entire table.
 */
uint64_t arch_mm_combine_table_entry_attrs(uint64_t table_attrs,
					   uint64_t block_attrs)
{
	/*
	 * Only stage 1 table descriptors have attributes, but the bits are res0
	 * for stage 2 table descriptors so this code is safe for both.
	 */
	if (table_attrs & TABLE_NSTABLE) {
		block_attrs |= STAGE1_NS;
	}
	if (table_attrs & TABLE_APTABLE1) {
		block_attrs |= STAGE1_AP2;
	}
	if (table_attrs & TABLE_APTABLE0) {
		block_attrs &= ~STAGE1_AP1;
	}
	if (table_attrs & TABLE_XNTABLE) {
		block_attrs |= STAGE1_XN;
	}
	if (table_attrs & TABLE_PXNTABLE) {
		block_attrs |= STAGE1_PXN;
	}
	return block_attrs;
}
*)

End SPECS.
