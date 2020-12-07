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


Inductive terminate {E} {R} (it:itree E R) : Prop :=
| TermRet
    v
    (RET: observe it = RetF v)
| TermTau
    (TAU: observe it = TauF it).

(* From HafniumCore *)
Require Import Lang.
Require Import Values.
Require Import Integers.
Require Import Constant.
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


Notation "'do' X <- A ;;; B" := (match A with Some X => B | None => triggerUB "None" end)
  (at level 200, X ident, A at level 100, B at level 200)
  : itree_monad_scope.

Notation "'do' X , Y <- A ;;; B" := (match A with Some (X, Y) => B | None => triggerUB "None" end)
  (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : itree_monad_scope.

Notation "'do' X , Y , Z <- A ;;; B" := (match A with Some (X, Y, Z) => B | None => triggerUB "None" end)
  (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : itree_monad_scope.

Notation " 'check' A ;;; B" := (if A then B else Ret None)
  (at level 200, A at level 100, B at level 200)
  : itree_monad_scope.

Local Open Scope itree_monad_scope.


Definition PtrTree_set (ptr: positive * Z) (v: positive) (map: PTree.t (ZTree.t positive)) :=
  let zt := match PTree.get (fst ptr) map with
            | Some zt => zt
            | None => (ZTree.empty positive)
            end in
  PTree.set (fst ptr) (ZTree.set (snd ptr) v zt) map
.

Definition PtrTree_get (ptr: positive * Z) (map: PTree.t (ZTree.t positive)) :=
  zt <- PTree.get (fst ptr) map;;
  ZTree.get (snd ptr) zt
.

Definition PtrTree_remove (ptr: positive * Z) (map: PTree.t (ZTree.t positive)) :=
  match PTree.get (fst ptr) map with
  | Some zt => PTree.set (fst ptr) (ZTree.remove (snd ptr) zt) map
  | None => map
  end
.

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
  (* XXX: invalid block for stage 1 and 2 . It seems it is used in some places, 
     so we have to keep track of the invalid block. Currently, I implement that 
     this invalid block is only in the bottom level of page tables, but it may need to be 
     in the intermediate level as well.  *)      
  | STAGE1_INVALID_BLOCK (output_address : Z) (attributes: Stage1BlockAttributes) (is_table: bool)
  | STAGE1_TABLE (output_address : Z) (attributes: Stage1TableAttributes)
  | STAGE1_PAGE (output_address : Z) (attributes: Stage1BlockAttributes)
  | STAGE2_INVALID_BLOCK (output_address : Z) (attributes: Stage2BlockAttributes) (is_table: bool)
  | STAGE2_TABLE (output_address : Z)
  | STAGE2_PAGE (output_address : Z) (attribuctes: Stage2BlockAttributes).

  Inductive CURRENT_STAGE := STAGE1 | STAGE2.
  
  Record ArchMMAbstractState :=
    mkArchMMAbstractState {
        pte_pool: PTree.t PTE_TYPES;
        addr_to_id : PTree.t (ZTree.t positive); (* block -> offset -> id *)
        id_to_addr : PTree.t (positive * Z); (* id -> (block, offset *)
        next_id: positive;
        stage: CURRENT_STAGE
      }.


  Definition initial_state : ArchMMAbstractState :=
    mkArchMMAbstractState (PTree.empty PTE_TYPES) (PTree.empty (ZTree.t positive)) (PTree.empty (positive * Z))
                          1%positive STAGE2.  

  Definition update_pte_pool (a : ArchMMAbstractState) b :=
    mkArchMMAbstractState b a.(addr_to_id) a.(id_to_addr) a.(next_id) a.(stage).

  Definition update_addr_to_id (a : ArchMMAbstractState) b :=
    mkArchMMAbstractState a.(pte_pool) b a.(id_to_addr) a.(next_id) a.(stage).

  Definition update_id_to_addr (a : ArchMMAbstractState) b :=
    mkArchMMAbstractState a.(pte_pool) a.(addr_to_id) b a.(next_id) a.(stage).

  Definition update_next_id (a : ArchMMAbstractState) b :=
    mkArchMMAbstractState a.(pte_pool) a.(addr_to_id) a.(id_to_addr) b a.(stage).

  Definition update_stage (a : ArchMMAbstractState) b :=
    mkArchMMAbstractState a.(pte_pool) a.(addr_to_id) a.(id_to_addr) a.(next_id) b.
  
End ABSTSTATE.

Notation "a {PTE_POOL : b }" := (update_pte_pool a b) (at level 1).
Notation "a {addr_to_id : b }" := (update_addr_to_id a b) (at level 1).
Notation "a {id_to_addr : b }" := (update_id_to_addr a b) (at level 1).
Notation "a {next_id : b }" := (update_next_id a b) (at level 1).
Notation "a {stage : b }" := (update_stage a b) (at level 1).

Section FLAG_TO_VALUE_and_VALUE_TO_FLAG.

  Definition x_zshift_or_0 := fun (cond: bool) (x: Z) (shift : Z) => if cond then Z.shiftl x shift else 0.
  Definition zshift_or_0 := fun (cond: bool) (shift : Z) => x_zshift_or_0 cond 1 shift.

  Definition x_bit_no_exist :=
    fun (x : Z) (shift : Z) (attribute_values: Z) => (zeq 0 (Z.land (Z.shiftl x 63) attribute_values)).
  Definition x_gen_true_false := 
    fun (x : Z) (shift : Z) (attribute_values: Z) => if x_bit_no_exist x shift attribute_values then false else true.
  Definition bit_no_exist :=    
    fun (shift : Z) (attribute_values: Z) => x_bit_no_exist 1 shift attribute_values.
  Definition gen_true_false := 
    fun (shift : Z) (attribute_values: Z) => if bit_no_exist shift attribute_values then false else true.
  
  Definition Stage1TableAttributes_to_ATTR_VALUES (stage1_table_attributes : Stage1TableAttributes) : Z :=
    match stage1_table_attributes with
    |  mkStage1TableAttributes nstable aptable1 aptable2 xntable pxntable
       => let nstable_to_z := zshift_or_0 nstable 63 in 
         let aptable1_to_z := zshift_or_0 aptable1 62 in
         let aptable2_to_z := zshift_or_0 aptable2 61 in
         let xntable_to_z := zshift_or_0 xntable 60 in
         let pxntable_to_z :=  zshift_or_0 pxntable 59 in 
         nstable_to_z + aptable1_to_z + aptable2_to_z + xntable_to_z + pxntable_to_z
    end.
  
  Definition ATTR_VALUES_to_Stage1TableAttributes (stage1_table_attributes_value : Z)
    : Stage1TableAttributes :=
    let nstable_of_z := gen_true_false 63 stage1_table_attributes_value in
    let aptable1_of_z := gen_true_false 62 stage1_table_attributes_value in
    let aptable2_of_z := gen_true_false 61 stage1_table_attributes_value in
    let xntable_of_z := gen_true_false 60 stage1_table_attributes_value in
    let pxntable_of_z := gen_true_false 59 stage1_table_attributes_value in
    mkStage1TableAttributes nstable_of_z aptable1_of_z aptable2_of_z xntable_of_z pxntable_of_z.

  Definition Stage1BlockAttributes_to_ATTR_VALUES (stage1_block_attributes : Stage1BlockAttributes) : Z :=
    match stage1_block_attributes with
    | mkStage1BlockAttributes xn pxn contiguous dbm ng af sh ap ns attrindx
      => let xn_to_n := zshift_or_0 xn 54 in
        let pxn_to_n := zshift_or_0 pxn 53 in
        let contiguous_to_n := zshift_or_0 contiguous 52 in
        let dbm_to_n := zshift_or_0 dbm 51 in
        let ng_to_n := zshift_or_0 ng 11 in
        let af_to_n := zshift_or_0 af 10 in
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
    let xn_of_z := gen_true_false 54 stage1_block_attributes_value in
    let pxn_of_z := gen_true_false 53 stage1_block_attributes_value in
    let contiguous_of_z := gen_true_false 52 stage1_block_attributes_value in
    let dbm_of_z := gen_true_false 51 stage1_block_attributes_value in
    let ng_of_z := gen_true_false 11 stage1_block_attributes_value in
    let af_of_z := gen_true_false 10 stage1_block_attributes_value in
    let sh_of_z := if x_bit_no_exist 1 8 stage1_block_attributes_value
                   then if x_bit_no_exist 2 8 stage1_block_attributes_value
                        then (* 0 << 8 *) Some NON_SHAREABLE
                        else (* 2 << 8 *) Some OUTER_SHAREABLE
                   else if x_bit_no_exist 2 8 stage1_block_attributes_value
                        then (* 1 << 8 *) None
                        else (* 3 << 8 *) Some INNER_SHAREABLE in
    let ap_of_z := if x_bit_no_exist 1 6 stage1_block_attributes_value
                   then if x_bit_no_exist 2 6 stage1_block_attributes_value
                        then (* 0 << 6 *) Some STAGE1_READWRITE
                        else (* 2 << 6 *) Some STAGE1_READONLY
                   else (* 1 << 6 or 3 << 6 *) None in
    let ns_of_z := gen_true_false 5 stage1_block_attributes_value in
    let attrindx_of_n := if x_bit_no_exist 1 2 stage1_block_attributes_value
                         then if x_bit_no_exist 2 2 stage1_block_attributes_value
                              then (* 0 << 2 *) Some STAGE1_DEVICEINDX
                              else (* 2 << 2 *) None
                         else if x_bit_no_exist 2 2 stage1_block_attributes_value
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
        let contiguous_to_n := zshift_or_0 contiguous 52  in
        let dbm_to_n := zshift_or_0 dbm 51 in
        let sw_owned_n := zshift_or_0 sw_owned 55 in
        let sw_exclusive := zshift_or_0 sw_exclusive 56 in
        let af_to_n := zshift_or_0 af 10 in
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
    let xn_of_z := if  x_bit_no_exist 1 53 stage2_block_attributes_value
                   then if  x_bit_no_exist 2 53 stage2_block_attributes_value
                        then (* 0 << 53 *) STAGE2_EXECUTE_ALL
                        else (* 2 << 53 *) STAGE2_EXECUTE_NONE
                   else if  x_bit_no_exist 2 53 stage2_block_attributes_value
                        then (* 1 << 53 *) STAGE2_EXECUTE_EL0
                        else (* 3 << 53 *) STAGE2_EXECUTE_EL1 in
    let contiguous_of_z := gen_true_false 52 stage2_block_attributes_value in
    let dbm_of_z := gen_true_false 51 stage2_block_attributes_value in
    let sw_owned_of_z := gen_true_false 55 stage2_block_attributes_value in
    let sw_exclusive_of_z := gen_true_false 56 stage2_block_attributes_value in
    let af_of_z := gen_true_false 10 stage2_block_attributes_value in
    let sh_of_z := if  x_bit_no_exist 1 8 stage2_block_attributes_value
                   then if  x_bit_no_exist 2 8 stage2_block_attributes_value
                        then (* 0 << 8 *) Some NON_SHAREABLE
                        else (* 2 << 8 *) Some OUTER_SHAREABLE
                   else if x_bit_no_exist 2 8 stage2_block_attributes_value
                        then (* 1 << 8 *) None
                        else (* 3 << 8 *) Some INNER_SHAREABLE in
    let s2ap_of_z := if x_bit_no_exist 1 6 stage2_block_attributes_value
                     then if x_bit_no_exist 2 6 stage2_block_attributes_value
                          then (* 0 << 6 *) STAGE2_ACCESS_NOPERM
                          else (* 2 << 6 *) STAGE2_ACCESS_WRITE
                     else if x_bit_no_exist 2 6 stage2_block_attributes_value
                          then (* 1 << 6 *) STAGE2_ACCESS_READ
                          else (* 3 << 6 *) STAGE2_ACCESS_READWRITE in
    let memattr_of_z := if x_bit_no_exist 1 2 stage2_block_attributes_value
                        then if x_bit_no_exist 2 2 stage2_block_attributes_value
                             then (* 0 << 2 *) MEMATTR_ZERO
                             else (* 2 << 2 *) MEMATTR_TWO
                        else if x_bit_no_exist 2 2 stage2_block_attributes_value
                             then (* 1 << 2 *) MEMATTR_ONE
                             else (* 3 << 2 *) MEMATTR_THREE in
    match sh_of_z with
    | Some sh_of_z' =>
      Some (mkStage2BlockAttributes xn_of_z contiguous_of_z dbm_of_z af_of_z sw_owned_of_z sw_exclusive_of_z
                                    sh_of_z' s2ap_of_z memattr_of_z)
    | None => None
    end.

  Definition IS_VALID_VALUE_TO_PTE_Attributes (attributes_value : Z) : bool :=
    gen_true_false 0 attributes_value.

  Definition IS_TABLE_VALUE_TO_PTE_Attributes (attributes_value : Z) : bool :=
    gen_true_false 1 attributes_value.
  
  Definition PTE_TYPES_to_IS_VALID_VALUE (pte_value : PTE_TYPES) : Z :=
    match pte_value with
    | UNDEFINED => 0
    | ABSENT => 0
    | STAGE1_INVALID_BLOCK _ _ _ => 0
    | STAGE1_TABLE _ _ => Z.shiftl 1 0
    | STAGE1_PAGE _ _ => Z.shiftl 1 0 
    | STAGE2_INVALID_BLOCK _ _ _ => 0
    | STAGE2_TABLE _ => Z.shiftl 1 0
    | STAGE2_PAGE _ _ => Z.shiftl 1 0
    end.

  Definition PTE_TYPES_TO_IS_TABLE_VALUE (pte_value : PTE_TYPES) : Z :=
    match pte_value with
    | UNDEFINED => 0
    | ABSENT => 0
    | STAGE1_INVALID_BLOCK _ _ is_table => zshift_or_0 is_table 1
    | STAGE1_TABLE _ _ => Z.shiftl 1 1
    | STAGE1_PAGE _ _ => Z.shiftl 1 1
    | STAGE2_INVALID_BLOCK _ _ is_table => zshift_or_0 is_table 1
    | STAGE2_TABLE _ => Z.shiftl 1 1
    | STAGE2_PAGE _ _ => Z.shiftl 1 1
    end.
  
  Definition PTE_TYPES_to_ATTR_VALUES (pte_value : PTE_TYPES) : Z :=
    match pte_value with
    | UNDEFINED => 0
    | ABSENT => 0
    | STAGE1_INVALID_BLOCK _ attributes is_table => Stage1BlockAttributes_to_ATTR_VALUES attributes + zshift_or_0 is_table 1
    | STAGE1_TABLE _ attributes => Stage1TableAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 1 + Z.shiftl 1 0
    | STAGE1_PAGE _ attributes => Stage1BlockAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 1 + Z.shiftl 1 0 
    | STAGE2_INVALID_BLOCK _ attributes is_table => Stage2BlockAttributes_to_ATTR_VALUES attributes + zshift_or_0 is_table 1
    | STAGE2_TABLE _ => Z.shiftl 1 1 + Z.shiftl 1 0
    | STAGE2_PAGE _ attributes => Stage2BlockAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 1 + Z.shiftl 1 0
    end.

  Definition PTE_TYPES_to_VALUES (pte : PTE_TYPES) : Z :=
    match pte with
    | UNDEFINED => 0
    | ABSENT => 0
    | STAGE1_INVALID_BLOCK oa attributes is_table => Z.shiftl oa 12 + Stage1BlockAttributes_to_ATTR_VALUES attributes +
                                                    zshift_or_0 is_table 1
    | STAGE1_TABLE oa attr => Z.shiftl oa 12 + Stage1TableAttributes_to_ATTR_VALUES attr + Z.shiftl 1 1 + Z.shiftl 1 0
    | STAGE1_PAGE oa attr => Z.shiftl oa 12 + Stage1BlockAttributes_to_ATTR_VALUES attr + Z.shiftl 1 1 + Z.shiftl 1 0
    | STAGE2_INVALID_BLOCK oa attributes is_table => Z.shiftl oa 12 + Stage2BlockAttributes_to_ATTR_VALUES attributes +
                                                    zshift_or_0 is_table 1
    | STAGE2_TABLE oa => Z.shiftl oa 12 + Z.shiftl 1 1 + Z.shiftl 1 0
    | STAGE2_PAGE oa attr => Z.shiftl oa 12 + Stage2BlockAttributes_to_ATTR_VALUES attr + Z.shiftl 1 1 + Z.shiftl 1 0
    end.

  Definition PTE_TYPES_to_ADDRESS (pte : PTE_TYPES) : Z :=
    match pte with
    | UNDEFINED => 0
    | ABSENT => 0
    | STAGE1_INVALID_BLOCK oa _ _
    | STAGE1_TABLE oa _
    | STAGE1_PAGE oa _
    | STAGE2_INVALID_BLOCK oa _ _
    | STAGE2_TABLE oa
    | STAGE2_PAGE oa _ => oa
    end.

  
  Definition PTE_TYPES_to_ADDRESS_WITH_SHIFT (pte : PTE_TYPES) : Z :=
    match pte with
    | UNDEFINED => 0
    | ABSENT => 0
    | STAGE1_INVALID_BLOCK oa _ _
    | STAGE1_TABLE oa _
    | STAGE1_PAGE oa _
    | STAGE2_INVALID_BLOCK oa _ _
    | STAGE2_TABLE oa
    | STAGE2_PAGE oa _ => Z.shiftl oa 12
    end.

End FLAG_TO_VALUE_and_VALUE_TO_FLAG.

Section HIGHSPECITREE.

Definition state := ArchMMAbstractState.

Inductive updateStateE: Type -> Type :=
| GetState : updateStateE (ArchMMAbstractState)
| SetState (st1:ArchMMAbstractState): updateStateE unit.

Definition updateState_handler {E: Type -> Type}
  : updateStateE ~> stateT (ArchMMAbstractState) (itree E) :=
  fun _ e st =>
    match e with
    | GetState => Ret (st, st)
    | SetState st' => Ret (st', tt)
    end.

Definition ArchMME := CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event.

Section MM_MODE_VALUE.

(*
/* The following are arch-independent page mapping modes. */
#define MM_MODE_R UINT32_C(0x0001) /* read */
#define MM_MODE_W UINT32_C(0x0002) /* write */
#define MM_MODE_X UINT32_C(0x0004) /* execute */
#define MM_MODE_D UINT32_C(0x0008) /* device */

#define MM_MODE_INVALID UINT32_C(0x0010)
#define MM_MODE_UNOWNED UINT32_C(0x0020)
#define MM_MODE_SHARED  UINT32_C(0x0040)
*)
  
Definition MM_MODE_R : Z := 1.
Definition MM_MODE_W : Z := 2. 
Definition MM_MODE_X : Z := 4.
Definition MM_MODE_D : Z := 8.

Definition MM_MODE_INVALID : Z := 16.
Definition MM_MODE_UNOWNED : Z := 32.
Definition MM_MODE_SHARED : Z := 64.
 
End MM_MODE_VALUE.

Section SPECS.
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

  Definition arch_mm_absent_pte_spec (level: Z) : itree ArchMME (PTE_TYPES) :=
    Ret (ABSENT).

  Definition arch_mm_absent_pte_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong level)] =>
      res <-  arch_mm_absent_pte_spec (Int64.unsigned level);;
      Ret (Vcomp (Vlong (Int64.repr (PTE_TYPES_to_VALUES res))), args)
    | _ => triggerNB "arch_mm_absent_pte_call: wrong arguments"
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

  (* By referring the comment, it is only for stage 2 table descriptors. But, I am not currently restrict 
     its usage *)
  (* This one is actually the place that creates the PTE, so we add a new page table entry in here *)
  Definition arch_mm_table_pte_spec (level : Z) (pa: positive * Z) : itree ArchMME (PTE_TYPES) :=
    st <- trigger GetState;;
    (* create a new page table entry *) 
    do new_pte <-
       match st.(stage) with
       | STAGE1 =>
         if zeq level 2
         then None
         else Some (STAGE1_TABLE 0 init_stage1_table_attributes)
       | STAGE2  =>
         if zeq level 3
         then None
         else Some (STAGE2_TABLE 0)
       end;;;
    let next_id := st.(next_id) in 
    let new_pte_pool := PTree.set next_id new_pte st.(pte_pool) in
    let new_addr_to_id := (PtrTree_set pa next_id st.(addr_to_id)) in
    let new_id_to_addr := (PTree.set next_id pa st.(id_to_addr)) in
    let new_next_id := Pos.succ next_id in
    let new_st := st {PTE_POOL : new_pte_pool} {addr_to_id : new_addr_to_id} {id_to_addr: new_id_to_addr}
                     {next_id : new_next_id} in
    trigger (SetState new_st);; Ret (new_pte)
  .
  
  Definition arch_mm_table_pte_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong level); Vcomp (Vptr b ptrofs)] =>
      pte <- arch_mm_table_pte_spec (Int64.unsigned level) (b, (Ptrofs.unsigned ptrofs));;
      Ret (Vcomp (Vlong (Int64.repr (PTE_TYPES_to_VALUES pte))), args)
    | _ => triggerUB "arch_mm_table_pte_call: wrong arguments"
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

  Definition arch_mm_block_pte_spec (level : Z) (pa: positive * Z) (attrs: Z) : itree ArchMME (PTE_TYPES) :=
    st <- trigger GetState;;
    (* create a new page table entry *) 
    do new_pte <- 
    (match st.(stage) with
        | STAGE1 =>
          if IS_VALID_VALUE_TO_PTE_Attributes attrs then 
            match IS_TABLE_VALUE_TO_PTE_Attributes attrs, ATTR_VALUES_to_Stage1BlockAttributes attrs with
            | true, Some attributes => Some (STAGE1_PAGE 0 attributes)
            | _, _ => None
            end
          else
            match IS_TABLE_VALUE_TO_PTE_Attributes attrs, ATTR_VALUES_to_Stage1BlockAttributes attrs with
            | true, Some attributes => Some (STAGE1_INVALID_BLOCK 0 attributes true)
            | false, Some attributes => Some (STAGE1_INVALID_BLOCK 0 attributes false)
            | _, _ => None
            end
        | STAGE2  =>
          if IS_VALID_VALUE_TO_PTE_Attributes attrs then 
            match IS_TABLE_VALUE_TO_PTE_Attributes attrs, ATTR_VALUES_to_Stage2BlockAttributes attrs with
            | true, Some attributes => Some (STAGE2_PAGE 0 attributes)
            | _, _ => None
            end
          else
            match IS_TABLE_VALUE_TO_PTE_Attributes attrs, ATTR_VALUES_to_Stage2BlockAttributes attrs with
            | true, Some attributes => Some (STAGE2_INVALID_BLOCK 0 attributes true)
            | false, Some attributes => Some (STAGE2_INVALID_BLOCK 0 attributes false)
            | _, _ => None
            end
     end) ;;;
    let next_id := st.(next_id) in 
    let new_pte_pool := PTree.set next_id new_pte st.(pte_pool) in
    let new_addr_to_id := (PtrTree_set pa next_id st.(addr_to_id)) in
    let new_id_to_addr := (PTree.set next_id pa st.(id_to_addr)) in
    let new_next_id := Pos.succ next_id in
    let new_st := st {PTE_POOL : new_pte_pool} {addr_to_id : new_addr_to_id} {id_to_addr: new_id_to_addr}
                     {next_id : new_next_id} in
    trigger (SetState new_st);; Ret (new_pte).
  
  Definition arch_mm_block_pte_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong level); Vcomp (Vptr b ptrofs); Vcomp (Vlong attrs)] =>
      pte <- arch_mm_block_pte_spec (Int64.unsigned level) (b, (Ptrofs.unsigned ptrofs)) (Int64.unsigned attrs);;
      Ret (Vcomp (Vlong (Int64.repr (PTE_TYPES_to_VALUES pte))), args)
    | _ => triggerUB "arch_mm_block_pte: wrong arguments"
    end
  .
  
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

  Definition arch_mm_is_block_allowed_spec (level : Z) : itree ArchMME (bool) :=
    let res := if zle level 2 then true else false in Ret res
  .

  Definition arch_mm_is_block_allowed_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong level)] =>
      res  <- arch_mm_is_block_allowed_spec (Int64.unsigned level) ;;
      let res' :=
          match res with
          | true => 1
          | false => 0
          end in
      Ret (Vcomp (Vlong (Int64.repr res')), args)
    | _ => triggerUB "arch_mm_is_block_allowed_call: wrong arguments"
    end
  .
  
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

  Definition arch_mm_pte_is_valid_spec (pte: positive * Z)  (level : Z) : itree ArchMME (bool) :=
    st <- trigger GetState;;
    do key <- PtrTree_get pte st.(addr_to_id);;;  (* UB *)
    do pte <- PTree.get key st.(pte_pool);;; (* Some *)
    let res := match pte with
               | ABSENT => false
               | STAGE1_INVALID_BLOCK _ _ _ => false
               | STAGE2_INVALID_BLOCK _ _ _ => false
               | _ => true
               end in
    Ret (res)
       .
       
  Definition arch_mm_pte_is_valid_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vptr b ptrofs); Vcomp (Vlong level)] =>
      res <- arch_mm_pte_is_valid_spec (b, (Ptrofs.unsigned ptrofs)) (Int64.unsigned level);;
      let res' :=
          match res with
          | true => 1
          | false => 0
          end in
      Ret (Vcomp (Vlong (Int64.repr res')), args)
    | _ => triggerUB "arch_mm_pte_is_valid_call: wrong arguments"
    end
  .
  
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

  Definition arch_mm_pte_is_present_spec (pte: positive * Z)  (level : Z) : itree ArchMME (bool) :=
    st <- trigger GetState;;
    do key <- PtrTree_get pte st.(addr_to_id);;;  (* UB *)
    do pte <- PTree.get key st.(pte_pool);;; (* Some *)
    let res :=                                                    
        match pte with
        | ABSENT => false
        | STAGE1_INVALID_BLOCK _ _ _ => false
        | STAGE2_INVALID_BLOCK _ attributes _ => attributes.(STAGE2_SW_OWNED)
        | _ => true
        end in
    Ret (res)
       .

  Definition arch_mm_pte_is_present_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vptr b ptrofs); Vcomp (Vlong level)] =>
      res <- arch_mm_pte_is_valid_spec (b, (Ptrofs.unsigned ptrofs)) (Int64.unsigned level);;
      let res' :=
          match res with
          | true => 1
          | false => 0
          end in
      Ret (Vcomp (Vlong (Int64.repr res')), args)
    | _ => triggerUB "arch_mm_pte_is_present_call: wrong arguments"
    end
  .

  
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

  Definition arch_mm_pte_is_table_spec (pte: positive * Z)  (level : Z) : itree ArchMME (bool) :=
    st <- trigger GetState;;
    do key <- PtrTree_get pte st.(addr_to_id);;;  (* UB *)
    do pte <- PTree.get key st.(pte_pool);;; (* Some *)
    let res :=                                                    
        if zeq level 0
        then false
        else match pte with
               | ABSENT => false
               | STAGE1_INVALID_BLOCK _ _ _ => false
               | STAGE2_INVALID_BLOCK _ _ _ => false
               | _ => true
             end in
    Ret (res)
       .

  Definition arch_mm_pte_is_table_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vptr b ptrofs); Vcomp (Vlong level)] =>
      res <- arch_mm_pte_is_table_spec (b, (Ptrofs.unsigned ptrofs)) (Int64.unsigned level);;
      let res' :=
          match res with
          | true => 1
          | false => 0
          end in
      Ret (Vcomp (Vlong (Int64.repr res')), args)
    | _ => triggerUB "arch_mm_pte_is_table: wrong arguments"
    end
  .
  
  
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

  Definition arch_mm_pte_is_block_spec (pte: positive * Z)  (level : Z) : itree ArchMME (bool) :=
    st <- trigger GetState;;
    do key <- PtrTree_get pte st.(addr_to_id);;;  (* UB *)
    do pte <- PTree.get key st.(pte_pool);;; (* Some *)
    let res :=     
        if zle level 2 
        then if zeq level 0
             then match pte with
                  | ABSENT => false
                  | STAGE1_INVALID_BLOCK _ _ res => res
                  | STAGE2_INVALID_BLOCK _ _ res => res
                  | _ => true
                  end 
             else let res1 :=
                      match pte with
                      | ABSENT => false
                      | STAGE1_INVALID_BLOCK _ _ _ => false
                      | STAGE2_INVALID_BLOCK _ attributes _ => attributes.(STAGE2_SW_OWNED)
                      | _ => true
                      end in
                  let res2 :=
                      (if zeq level 0
                      then false
                      else match pte with
                           | ABSENT => false
                           | STAGE1_INVALID_BLOCK _ _ _ => false
                           | STAGE2_INVALID_BLOCK _ _ _ => false
                           | _ => true
                           end) in
                  res1 && res2
        else false in
        
        Ret (res)
             .

  Definition arch_mm_pte_is_block_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vptr b ptrofs); Vcomp (Vlong level)] =>
      res <- arch_mm_pte_is_block_spec (b, (Ptrofs.unsigned ptrofs)) (Int64.unsigned level);;
      let res' :=
          match res with
          | true => 1
          | false => 0
          end in
      Ret (Vcomp (Vlong (Int64.repr res')), args)
    | _ => triggerUB "arch_mm_pte_is_block_call: wrong arguments"
    end
  .
      
  

(*
static uint64_t pte_addr(pte_t pte)
{
	return pte & PTE_ADDR_MASK;
}
*)

  Definition pte_addr_spec (pte: positive * Z) : itree ArchMME (Z) :=
    st <- trigger GetState;;
    do key <- PtrTree_get pte st.(addr_to_id);;;  (* UB *)
    do pte <- PTree.get key st.(pte_pool);;; (* Some *)
    Ret (PTE_TYPES_to_ADDRESS pte)
       .
       
  Definition pte_addr_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vptr b ptrofs)] =>
      res <- pte_addr_spec (b, (Ptrofs.unsigned ptrofs));;
      Ret (Vcomp (Vlong (Int64.repr (Z.shiftl res 12))), args)
    | _ => triggerUB "pte_addr_spec: wrong arguments"
    end
  .
  
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

  Definition arch_mm_clear_pa_spec (pa: positive * Z) : itree ArchMME (positive * Z) :=
    st <- trigger GetState;;
    do key <- PtrTree_get pa st.(addr_to_id);;;  (* UB *)
    let new_pte_pool := (PTree.remove key st.(pte_pool)) in 
    let new_addr_to_id := (PtrTree_remove pa st.(addr_to_id)) in 
    let new_id_to_addr := (PTree.remove key st.(id_to_addr)) in 
    let new_st := st {PTE_POOL : new_pte_pool} {addr_to_id : new_addr_to_id} {id_to_addr: new_id_to_addr} in
    trigger (SetState new_st);; Ret (pa)
       .
       
  Definition arch_mm_clear_pa_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vptr b ptrofs)] =>
      pa <- arch_mm_clear_pa_spec (b, (Ptrofs.unsigned ptrofs));;
      Ret (Vcomp (Vptr (fst pa) (Ptrofs.repr (snd pa))), args)
    | _ => triggerUB "arch_mm_clear_pa_call: wrong arguments"
    end
  .

(* XXX: The following two things actually do the same thing *)
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

 Definition arch_mm_block_from_pte_spec (pte: positive * Z) (level : Z) : itree ArchMME (PTE_TYPES * (positive * Z)) :=
   st <- trigger GetState;;
   do key <- PtrTree_get pte st.(addr_to_id);;;  (* UB *)
   do pte_t <- PTree.get key st.(pte_pool);;; (* Some *)
   let addr := Z.shiftl (PTE_TYPES_to_ADDRESS pte_t) 12 in
   do key' <- PtrTree_get ((fst pte), addr) st.(addr_to_id);;; 
   do pte_t' <- PTree.get key st.(pte_pool);;; (* Some *) 
   Ret (pte_t', (fst pte, addr))
      .

 Definition arch_mm_block_from_pte_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
   match args with 
   | [Vcomp (Vptr b ptrofs); Vcomp (Vlong level)] =>
     res <- arch_mm_block_from_pte_spec (b, (Ptrofs.unsigned ptrofs)) (Int64.unsigned level);;
     Ret (Vcomp (Vptr (fst (snd res)) (Ptrofs.repr (snd (snd res)))), args)
   | _ => triggerUB "arch_mm_pte_attrs_call: wrong arguments"
   end
       .
  
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

 Definition arch_mm_table_from_pte_spec (pte: positive * Z) (level : Z) : itree ArchMME (PTE_TYPES * (positive * Z)) :=
   st <- trigger GetState;;
   do key <- PtrTree_get pte st.(addr_to_id);;;  (* UB *)
   do pte_t <- PTree.get key st.(pte_pool);;; (* Some *)
   let addr := Z.shiftl (PTE_TYPES_to_ADDRESS pte_t) 12 in
   do key' <- PtrTree_get ((fst pte), addr) st.(addr_to_id);;; 
   do pte_t' <- PTree.get key st.(pte_pool);;; (* Some *) 
   Ret (pte_t', (fst pte, addr))
      .

 Definition arch_mm_table_from_pte_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
   match args with 
   | [Vcomp (Vptr b ptrofs); Vcomp (Vlong level)] =>
     res <- arch_mm_table_from_pte_spec (b, (Ptrofs.unsigned ptrofs)) (Int64.unsigned level);;
     Ret (Vcomp (Vptr (fst (snd res)) (Ptrofs.repr (snd (snd res)))), args)
   | _ => triggerUB "arch_mm_pte_attrs_call: wrong arguments"
   end
       .
  
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

 Definition arch_mm_pte_attrs_spec (pte: positive * Z) (level : Z) : itree ArchMME (Z) :=
    st <- trigger GetState;;
    do key <- PtrTree_get pte st.(addr_to_id);;;  (* UB *)
    do pte <- PTree.get key st.(pte_pool);;; (* Some *)
    Ret (PTE_TYPES_to_ATTR_VALUES pte)
       .
       
  Definition arch_mm_pte_attrs_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vptr b ptrofs); Vcomp (Vlong level)] =>
      res <- arch_mm_pte_attrs_spec (b, (Ptrofs.unsigned ptrofs)) (Int64.unsigned level);;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerUB "arch_mm_pte_attrs_call: wrong arguments"
    end
       .
  
(*  
uint64_t arch_mm_mode_to_stage1_attrs(uint32_t mode)
{
	uint64_t attrs = 0;

	attrs |= STAGE1_AF | STAGE1_SH(OUTER_SHAREABLE);

	/* Define the execute bits. */
	if (!(mode & MM_MODE_X)) {
		attrs |= STAGE1_XN;
	}

	/* Define the read/write bits. */
	if (mode & MM_MODE_W) {
		attrs |= STAGE1_AP(STAGE1_READWRITE);
	} else {
		attrs |= STAGE1_AP(STAGE1_READONLY);
	}

	/* Define the memory attribute bits. */
	if (mode & MM_MODE_D) {
		attrs |= STAGE1_ATTRINDX(STAGE1_DEVICEINDX);
	} else {
		attrs |= STAGE1_ATTRINDX(STAGE1_NORMALINDX);
	}

	/* Define the valid bit. */
	if (!(mode & MM_MODE_INVALID)) {
		attrs |= PTE_VALID;
	}

	return attrs;
}
*)

  Definition arch_mm_mode_to_stage1_attrs_spec (mode : Z) : itree ArchMME (Z) :=
    let attrs0 := 0 in
    let attrs1 := Z.lor attrs0 (Z.lor (zshift_or_0 true 10) (x_zshift_or_0 true 2 8)) in
                  (* STAGE1_AF *)  (* STAGE1_SH(OUTER_SHAREABLE) *)
    let attrs2 := if zeq 0 (Z.land mode MM_MODE_X)
                  then attrs1
                  else Z.lor attrs1 (zshift_or_0 true 54) in (* STAGE1_XN *)
    let attrs3 := if zeq 0 (Z.land mode MM_MODE_W)
                  then Z.lor attrs2 (x_zshift_or_0 true 2 6) (* STAGE1_AP(STAGE1_READONLY) *)
                  else attrs2 in (* STAGE1_AP(STAGE1_READWRITE) *)
    let attrs4 := if zeq 0 (Z.land mode MM_MODE_D)
                  then Z.lor attrs3 (zshift_or_0 true 2) (* STAGE1_ATTRINDX(STAGE1_NORMALINDX) *)
                  else attrs3 in (* STAGE1_ATTRINDX(STAGE1_DEVICEINDX) *)
    let attrs5 := if zeq 0 (Z.land mode MM_MODE_INVALID)
                  then Z.lor attrs4 (zshift_or_0 true 0) (* PTE_VALID *)
                  else attrs4 in
    Ret (attrs5)
       .
         
  Definition arch_mm_mode_to_stage1_attrs_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong mode)] =>
      res <- arch_mm_mode_to_stage1_attrs_spec (Int64.unsigned mode)  ;;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "arch_mm_mode_to_stage1_attrs_call: wrong arguments"
    end
  .
  
(*
uint64_t arch_mm_mode_to_stage2_attrs(uint32_t mode)
{
	uint64_t attrs = 0;
	uint64_t access = 0;

	/*
	 * Non-shareable is the "neutral" share mode, i.e., the shareability
	 * attribute of stage 1 will determine the actual attribute.
	 */
	attrs |= STAGE2_AF | STAGE2_SH(NON_SHAREABLE);

	/* Define the read/write bits. */
	if (mode & MM_MODE_R) {
		access |= STAGE2_ACCESS_READ;
	}

	if (mode & MM_MODE_W) {
		access |= STAGE2_ACCESS_WRITE;
	}

	attrs |= STAGE2_S2AP(access);

	/* Define the execute bits. */
	if (mode & MM_MODE_X) {
		attrs |= STAGE2_XN(STAGE2_EXECUTE_ALL);
	} else {
		attrs |= STAGE2_XN(STAGE2_EXECUTE_NONE);
	}

	/*
	 * Define the memory attribute bits, using the "neutral" values which
	 * give the stage-1 attributes full control of the attributes.
	 */
	if (mode & MM_MODE_D) {
		attrs |= STAGE2_MEMATTR(STAGE2_DEVICE_MEMORY,
					STAGE2_MEMATTR_DEVICE_GRE);
	} else {
		attrs |= STAGE2_MEMATTR(STAGE2_WRITEBACK, STAGE2_WRITEBACK);
	}

	/* Define the ownership bit. */
	if (!(mode & MM_MODE_UNOWNED)) {
		attrs |= STAGE2_SW_OWNED;
	}

	/* Define the exclusivity bit. */
	if (!(mode & MM_MODE_SHARED)) {
		attrs |= STAGE2_SW_EXCLUSIVE;
	}

	/* Define the valid bit. */
	if (!(mode & MM_MODE_INVALID)) {
		attrs |= PTE_VALID;
	}

	return attrs;
}
 *)

  (* XXX: TODO *)
  
(*
uint32_t arch_mm_stage2_attrs_to_mode(uint64_t attrs)
{
	uint32_t mode = 0;

	if (attrs & STAGE2_S2AP(STAGE2_ACCESS_READ)) {
		mode |= MM_MODE_R;
	}

	if (attrs & STAGE2_S2AP(STAGE2_ACCESS_WRITE)) {
		mode |= MM_MODE_W;
	}

	if ((attrs & STAGE2_XN(STAGE2_EXECUTE_MASK)) ==
	    STAGE2_XN(STAGE2_EXECUTE_ALL)) {
		mode |= MM_MODE_X;
	}

	if ((attrs & STAGE2_MEMATTR_TYPE_MASK) == STAGE2_DEVICE_MEMORY) {
		mode |= MM_MODE_D;
	}

	if (!(attrs & STAGE2_SW_OWNED)) {
		mode |= MM_MODE_UNOWNED;
	}

	if (!(attrs & STAGE2_SW_EXCLUSIVE)) {
		mode |= MM_MODE_SHARED;
	}

	if (!(attrs & PTE_VALID)) {
		mode |= MM_MODE_INVALID;
	}

	return mode;
}
*)

  (* XXX: TODO *)
  

(*
// JIEUNG: This is for stage 1 - STAGE 1 always has 2 level -
// This is for virtual machine
uint8_t arch_mm_stage1_max_level(void)
{
	/*
	 * For stage 1 we hard-code this to 2 for now so that we can
	 * save one page table level at the expense of limiting the
	 * physical memory to 512GB.
	 */
	return 2;
}
*)

  Definition arch_mm_stage1_max_level_spec  : itree ArchMME (Z) :=
    Ret (2).

  Definition arch_mm_stage1_max_level_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      res <- arch_mm_stage1_max_level_spec ;;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "level <> integer"
    end
  .  

(* 
// JIEUNG: This is defined in initialization phases
uint8_t arch_mm_stage2_max_level(void)
{
	return mm_s2_max_level;
}
*)

  Definition arch_mm_stage2_max_level_spec  : itree ArchMME (Z) :=
    Ret (3).

  Definition  arch_mm_stage2_max_level_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      res <- arch_mm_stage2_max_level_spec ;;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "level <> integer"
    end
  .

  

(*  
// JIEUNG: Stage 1 always have one...?
uint8_t arch_mm_stage1_root_table_count(void)
{
	/* Stage 1 doesn't concatenate tables. */
	return 1;
}
*)

  Definition arch_mm_stage1_root_table_count_spec  : itree ArchMME (Z) :=
    Ret (1).

  Definition arch_mm_stage1_root_table_count_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      res <- arch_mm_stage1_root_table_count_spec ;;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "level <> integer"
    end
  .  
  
(*  
uint8_t arch_mm_stage2_root_table_count(void)
{
	return mm_s2_root_table_count;
}
 *)

  Definition arch_mm_stage2_root_table_count_spec  : itree ArchMME (Z) :=
    Ret (1).

  Definition arch_mm_stage2_root_table_count_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      res <- arch_mm_stage2_root_table_count_spec ;;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "level <> integer"
    end
  .  
  
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

  Definition arch_mm_combine_table_entry_attrs_spec (table_attrs block_attrs: Z)  : itree ArchMME (Z) :=
    let tattrs := ATTR_VALUES_to_Stage1TableAttributes table_attrs  in
    let block_attrs1 := Z.lor block_attrs (zshift_or_0 tattrs.(TABLE_NSTABLE) 63) in
    let block_attrs2 := Z.lor block_attrs (zshift_or_0 tattrs.(TABLE_APTABLE1) 62) in
    let block_attrs3 := Z.land block_attrs (Z.lnot (zshift_or_0 tattrs.(TABLE_APTABLE0) 61)) in
    let block_attrs4 := Z.lor block_attrs (zshift_or_0 tattrs.(TABLE_XNTABLE) 60) in
    let block_attrs' := Z.lor block_attrs (zshift_or_0 tattrs.(TABLE_PXNTABLE) 59) in
    Ret (block_attrs1).
      
  Definition arch_mm_combine_table_entry_attrs_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong table_attrs); Vcomp (Vlong block_attrs)] =>
      res <- arch_mm_combine_table_entry_attrs_spec (Int64.unsigned table_attrs) (Int64.unsigned block_attrs);;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "arch_mm_combine_table_entry_attrs_call: wrong arguments"
    end
  .  


  Definition funcs :=
    [
      ("ARCHMM.arch_mm_absent_pte", arch_mm_absent_pte_call) ;
    ("ARCHMM.arch_mm_table_pte", arch_mm_table_pte_call) ;
    ("ARCHMM.arch_mm_block_pte", arch_mm_block_pte_call) ;
    ("ARCHMM.arch_mm_is_block_allowed", arch_mm_is_block_allowed_call) ;
    ("ARCHMM.arch_mm_pte_is_valid", arch_mm_pte_is_valid_call) ;
    ("ARCHMM.arch_mm_pte_is_present", arch_mm_pte_is_present_call) ;
    ("ARCHMM.arch_mm_pte_is_table", arch_mm_pte_is_table_call) ;
    ("ARCHMM.arch_mm_pte_is_block", arch_mm_pte_is_block_call) ;
    ("ARCHMM.pte_addr",  pte_addr_call) ;
    ("ARCHMM.arch_mm_clear_pa", arch_mm_clear_pa_call) ;
    ("ARCHMM.arch_mm_block_from_pte",  arch_mm_block_from_pte_call) ;
    ("ARCHMM.arch_mm_table_from_pte", arch_mm_table_from_pte_call) ;
    ("ARCHMM.arch_mm_pte_attrs", arch_mm_pte_attrs_call) ;
    ("ARCHMM.arch_mm_mode_to_stage1_attrs", arch_mm_mode_to_stage1_attrs_call) ;
    (*
    ("ARCHMM.arch_mm_mode_to_stage2_attrs",  arch_mm_mode_to_stage2_attrs_call) ;
    ("ARCHMM.arch_mm_stage2_attrs_to_mode",  arch_mm_stage2_attrs_to_mode_call) ;
     ...
     *)
    ("ARCHMM.arch_mm_stage1_max_level", arch_mm_stage1_max_level_call) ;
    ("ARCHMM.arch_mm_stage2_max_level", arch_mm_stage2_max_level_call) ;
    ("ARCHMM.arch_mm_stage1_root_table_count", arch_mm_stage1_root_table_count_call) ;
    ("ARCHMM.arch_mm_stage2_root_table_count", arch_mm_stage2_root_table_count_call) ;
    ("ARCHMM.arch_mm_combine_table_entry_attrs", arch_mm_combine_table_entry_attrs_call) 
    ].

  Definition archmm_modsem : ModSem :=
    mk_ModSem
      (fun s => existsb (string_dec s) (List.map fst funcs))
      _
      (initial_state)
      updateStateE
      updateState_handler
      (fun T (c: CallExternalE T) =>
         let '(CallExternal func_name args) := c in
         let fix find_func l :=
             match l with
             | (f, body)::tl =>
               if (string_dec func_name f)
               then body args
               else find_func tl
             | nil => triggerNB "Not mpool func"
             end
         in
         find_func funcs
      )
  .
  
End SPECS.

End HIGHSPECITREE.
