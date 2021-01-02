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
#define STAGE2_MEMATTR(outer, inner) ((((outer) << 4) | (inner)) << 2)
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

(*
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
 *)

Variable Z_to_string: Z -> string.

Extract Constant Z_to_string =>
"fun z -> (HexString.of_Z z)"
.

Definition bool_to_string (b: bool) : string :=
  match b with
  | true => "On"
  | _ => "Off"
  end.

Definition string_indent : string := "    ".

(* Variable A: Type. *)
Definition pointer_value_type : Type := positive * Z.

Fixpoint appends_all (ls : list string) : string :=
  match ls with
  | [] => ""
  | hd::tl => append hd (appends_all tl)
  end.

Definition pointer_values_to_string (a: pointer_value_type): string :=
  appends_all ["("; (Z_to_string (Zpos' (fst a))); ", "; (Z_to_string (snd a)); ")"]
.

Section ABSTSTATE.
  
  (* abstract type definitions *)
  Inductive BLOCK_SHAREABLE :=
  | NON_SHAREABLE (*0*) | OUTER_SHAREABLE (*2*) | INNER_SHAREABLE (*3*).

  Inductive STAGE1_BLOCK_PERM :=
  | STAGE1_READONLY (*2*) | STAGE1_READWRITE (*0*).

  Inductive STAGE1_BLOCK_TYPE :=
  | STAGE1_DEVICEINDX (*0*) | STAGE1_NORMALINDX (*1*).

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

  (* The following are stage-2 memory attributes for normal memory *)
  Inductive MMATTR_STAGE2_MEM_TYPE :=
  | STAGE2_DEVICE_MEMORY
  | STAGE2_NONCACHEABLE
  | STAGE2_WRITETHROUGH
  | STAGE2_WRITEBACK.

  (* The following are stage-2 memory attributes for device memory. *)
  Inductive MMATTR_STAGE2_DEVICE_MEMORY_TYPE :=
  | STAGE2_DEVICE_nGnRnE
  | STAGE2_DEVICE_nGnRE
  | STAGE2_DEVICE_nGRE
  | STAGE2_DEVICE_GRE.


  (* UNINITIALIZED: they are actually same with STAGE2_DEVICE_MEMORY and STAGE2_MEMATTR_DEVICE_nGnRnE, but  
                    I made them explicitly *) 
  Inductive MMATTR_STAGE2_OUTER_ATTR :=
  | MEMATTR_STAGE2_OUTER_ATTR_UNINITIALIZED
  | OUTER_MEM_TYPE_ATTR (mem_type: MMATTR_STAGE2_MEM_TYPE).
  
  Inductive MMATTR_STAGE2_INNER_ATTR :=
  | MMATTR_STAGE2_INNER_ATTR_UNINITIALIZED
  | INNER_MEM_TYPE_ATTR (mem_type : MMATTR_STAGE2_MEM_TYPE)
  | INNER_DEVICE_MEM_TYPE_ATTR (device_mem_type: MMATTR_STAGE2_DEVICE_MEMORY_TYPE).
  
  (* The following function defines only two things that are used in arch mm module now. It can be extended later. *)
  Inductive STAGE2_MEMATTR_VALUE :=
  | STAGE2_MEM_ATTR_GEN (outer_attr : MMATTR_STAGE2_OUTER_ATTR) (inner_attr :  MMATTR_STAGE2_INNER_ATTR).

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
        STAGE2_MEMATTR: STAGE2_MEMATTR_VALUE
      }.

  Definition init_stage2_block_attributes := mkStage2BlockAttributes
                                               STAGE2_EXECUTE_ALL false false false false false
                                               NON_SHAREABLE STAGE2_ACCESS_NOPERM
                                               (STAGE2_MEM_ATTR_GEN MEMATTR_STAGE2_OUTER_ATTR_UNINITIALIZED
                                                                    MMATTR_STAGE2_INNER_ATTR_UNINITIALIZED).

  (* One tip: 
     Since we have to convert Z values into this PTE_TYPES without any additional information, 
     we need to make them exclusive. I am currently assume that 
     block is only used at the last level (it is actually a page) of the address translation phase.
     When it is not true, we need to change them later *)
  Inductive PTE_TYPES :=
  | UNDEFINED
  | ABSENT
  (* XXX: invalid block for stage 1 and 2 . It seems it is used in some places, 
     so we have to keep track of the invalid block. Currently, I implement that 
     this invalid block is only in the bottom level of page tables, but it may need to be 
     in the intermediate level as well.  *)
  (* for level 0 - IS_TAbLE is on, IS_VALID is off *)      
  | STAGE1_INVALID_BLOCK_LEVEL0 (output_address : Z) (attributes: Stage1TableAttributes)
  (* for level 1, 2 - IS_TABLE is off, IS_VALID is off *)      
  | STAGE1_INVALID_BLOCK (output_address : Z) (attributes: Stage1BlockAttributes)
  (* for level 0, 1 - IS_TABLE is on and IS_VALID is on *)
  | STAGE1_TABLE (output_address : Z) (attributes: Stage1TableAttributes)
  (* for level 1 - IS_TABLE is off and IS_VALID is on *)
  | STAGE1_BLOCK (output_address : Z) (attributes: Stage1BlockAttributes)
  (* for level 2 - IS_TABLE is on and IS_VALID is on *)
  | STAGE1_PAGE (output_address : Z) (attributes: Stage1BlockAttributes)                 
  (* for level 0 - IS_TAbLE is on, IS_VALID is off *)      
  | STAGE2_INVALID_BLOCK_LEVEL0 (output_address : Z)
  (* for level 1, 2, 3 - IS_TABLE is off, IS_VALID is off *)
  | STAGE2_INVALID_BLOCK (output_address : Z) (attributes: Stage2BlockAttributes)
  (* for level 0, 1, 2 - IS_TABLE is on and IS_VALID is on *)
  | STAGE2_TABLE (output_address : Z)
  (* for level 1, 2 - IS_TABLE is off and IS_VALID is on *)                 
  | STAGE2_BLOCK (output_address : Z) (attribuctes: Stage2BlockAttributes)
  (* for level 3 - IS_TABLE is on and IS_VALID is on *)
  | STAGE2_PAGE (output_address : Z) (attribuctes: Stage2BlockAttributes).

  Inductive CURRENT_STAGE := STAGE1 | STAGE2.

  (* This module is an actually stateless module. We memorizes stage to distinguish whether the system
     is in stage 1 or 2. *)
  Record ArchMMAbstractState :=
    mkArchMMAbstractState {
        initialized: bool;
        stage: CURRENT_STAGE
      }.

  (* initialized is to distinguish UNDEFINED / ABSENT in PTE_TYPES and other UNINITIALIZED values 
     in other places. for the simplicity, we assume initialized is true in here. *)
  Definition initial_state : ArchMMAbstractState :=
    mkArchMMAbstractState true STAGE2.  

  Definition update_stage (a : ArchMMAbstractState) b :=
    mkArchMMAbstractState a.(initialized) b.
  
End ABSTSTATE.

Notation "a {stage : b }" := (update_stage a b) (at level 1).

(* TODO: we can combine the following values with the definitions in the Constant.v file. 
   1) define Z macro values in Constant.v 
   2) define int64 macro values in a different file (e.g., LowConstant.v) by using Constant.v *) 
Section FLAGVALUES.

  Definition Z_MM_S2_MAX_LEVEL := 3.
  Definition Z_MM_S2_ROOT_TABLE_COUNT := 1.

  Definition Z_NON_SHAREABLE := 0.
  Definition Z_OUTER_SHAREABLE := 2.
  Definition Z_INNER_SHAREABLE := 3.

  Definition Z_PTE_VALID := 0.
  Definition Z_PTE_LEVEL0_BLOCK := 1.
  Definition Z_PTE_TABLE := 1.

  Definition Z_STAGE1_XN := 54.
  Definition Z_STAGE1_PXN := 53.
  Definition Z_STAGE1_CONTIGUOUS := 52.
  Definition Z_STAGE1_DBM := 51.
  Definition Z_STAGE1_NG := 11.
  Definition Z_STAGE1_AF := 10.
  Definition Z_STAGE1_SH_GEN (x : Z) := Z.shiftl x 8.
  Definition Z_STAGE1_SH := 8.
  Definition Z_STAGE1_AP2 := 7.
  Definition Z_STAGE1_AP1 := 6.
  Definition Z_STAGE1_AP_GEN (x: Z) := Z.shiftl x 6.
  Definition Z_STAGE1_AP := 6.
  Definition Z_STAGE1_NS := 5.
  Definition Z_STAGE1_ATTRINDX_GEN (x: Z) := Z.shiftl x 2.
  Definition Z_STAGE1_ATTRINDX := 2.

  Definition Z_STAGE1_READONLY := 2.
  Definition Z_STAGE1_READWRITE := 0.

  Definition Z_STAGE1_DEVICEINDX := 0.
  Definition Z_STAGE1_NORMALINDX := 1.

  Definition Z_STAGE2_XN_GEN (x : Z) := Z.shiftl x 53.
  Definition Z_STAGE2_XN := 53.
  Definition Z_STAGE2_CONTIGUOUS := 52.
  Definition Z_STAGE2_DBM := 51.
  Definition Z_STAGE2_AF := 10.
  Definition Z_STAGE2_SH_GEN (x : Z) := Z.shiftl x 8.
  Definition Z_STAGE2_SH := 8.
  Definition Z_STAGE2_S2AP_GEN (x : Z) := Z.shiftl x 6.
  Definition Z_STAGE2_S2AP := 6.

  Definition Z_STAGE2_EXECUTE_ALL := 0.
  Definition Z_STAGE2_EXECUTE_EL0 := 1.
  Definition Z_STAGE2_EXECUTE_NONE := 2.
  Definition Z_STAGE2_EXECUTE_EL1 := 3.
  Definition Z_STAGE2_EXECUTE_MASK := 3.

  Definition Z_TABLE_NSTABLE := 63.
  Definition Z_TABLE_APTABLE1 := 62.
  Definition Z_TABLE_APTABLE0 := 61.
  Definition Z_TABLE_XNTABLE := 60.
  Definition Z_TABLE_PXNTABLE := 59.

  Definition Z_STAGE2_SW_OWNED := 55.
  Definition Z_STAGE2_SW_EXCLUSIVE := 56.

  Definition Z_STAGE2_DEVICE_MEMORY := 0.
  Definition Z_STAGE2_NONCACHEABLE := 1.
  Definition Z_STAGE2_WRITETHROUGH := 2.
  Definition Z_STAGE2_WRITEBACK := 3.

  Definition Z_STAGE2_DEVICE_nGnRnE := 0.
  Definition Z_STAGE2_DEVICE_nGnRE := 1.
  Definition Z_STAGE2_DEVICE_nGRE := 2.
  Definition Z_STAGE2_DEVICE_GRE := 3.

  Definition Z_STAGE2_MEMATTR_OUTER := 4.
  Definition Z_STAGE2_MEMATTR_INNER := 2.
  Definition Z_STAGE2_MEMATTR_GEN (outer inner : Z) := Z.lor (Z.shiftl outer Z_STAGE2_MEMATTR_OUTER)
                                                             (Z.shiftl inner Z_STAGE2_MEMATTR_INNER).

  Definition Z_STAGE2_MEMATTR_MASK := (Z.shiftl 3 Z_STAGE2_MEMATTR_OUTER).
  
  Definition Z_STAGE2_ACCESS_READ := 1.
  Definition Z_STAGE2_ACCESS_WRITE := 2.
  Definition Z_PAGE_BITS := 12.
  Definition Z_64MAX := ((Z.pow 2 64) - 1)%Z.
  Definition Z_not := fun val => (Z.lxor Z_64MAX val).
  (* Test code to check Z operations. 
     Z_shiftl is not necessary if we use Z.shiftl with well defined values. 
  Definition Z_shiftl (val shift : Z) := Z.modulo (Z.shiftl val shift) (Z.pow 2 64).
  Eval compute in (((Z.pow 2 64) - 1)%Z).
  Eval compute in (Z_not Z_64MAX).
  Eval compute in (Z.land Z_64MAX 1).
  Eval compute in (Z.land Z_64MAX 8).
  Eval compute in (Z.land Z_64MAX 16).
  Eval compute in (Z.lor 8 16).
  Eval compute in (Z.lor 24 16).
  Eval compute in (Z.modulo 1 3).
  Eval compute in (Z.shiftl 111 63).
  Eval compute in (Z_shiftl 111 63).
  *) 
  Definition Z_PTE_ADDR_MASK := (Z.land ((Z.shiftl 1 48) - 1) (Z_not ((Z.shiftl 1 Z_PAGE_BITS) - 1))).
  Definition Z_PTE_ATTR_MASK := (Z_not (Z.lor Z_PTE_ADDR_MASK (Z.shiftl 1 1))).

End FLAGVALUES.

Section FLAG_TO_VALUE_and_VALUE_TO_FLAG.

  Definition x_zshift_or_0 := fun (cond: bool) (x: Z) (shift : Z) => if cond then Z.shiftl x shift else 0.
  Definition zshift_or_0 := fun (cond: bool) (shift : Z) => x_zshift_or_0 cond 1 shift.

  Definition x_bit_no_exist :=
    fun (x shift attribute_values: Z) => (zeq 0 (Z.land (Z.shiftl x shift) attribute_values)).
  Definition x_gen_true_false := 
    fun (x shift attribute_values: Z) => if x_bit_no_exist x shift attribute_values then false else true.
  Definition bit_no_exist :=    
    fun (shift : Z) (attribute_values: Z) => x_bit_no_exist 1 shift attribute_values.
  Definition gen_true_false := 
    fun (shift : Z) (attribute_values: Z) => if bit_no_exist shift attribute_values then false else true.
  
  Definition Stage1TableAttributes_to_ATTR_VALUES (stage1_table_attributes : Stage1TableAttributes) : Z :=
    match stage1_table_attributes with
    |  mkStage1TableAttributes nstable aptable1 aptable2 xntable pxntable
       => let nstable_to_z := zshift_or_0 nstable Z_TABLE_NSTABLE in 
         let aptable1_to_z := zshift_or_0 aptable1 Z_TABLE_APTABLE1 in
         let aptable0_to_z := zshift_or_0 aptable2 Z_TABLE_APTABLE0 in
         let xntable_to_z := zshift_or_0 xntable Z_TABLE_XNTABLE in
         let pxntable_to_z :=  zshift_or_0 pxntable Z_TABLE_PXNTABLE in 
         nstable_to_z + aptable1_to_z + aptable0_to_z + xntable_to_z + pxntable_to_z
    end.
  
  Definition ATTR_VALUES_to_Stage1TableAttributes (stage1_table_attributes_value : Z)
    : Stage1TableAttributes :=
    let nstable_of_z := gen_true_false Z_TABLE_NSTABLE stage1_table_attributes_value in
    let aptable1_of_z := gen_true_false Z_TABLE_APTABLE1 stage1_table_attributes_value in
    let aptable0_of_z := gen_true_false Z_TABLE_APTABLE0 stage1_table_attributes_value in
    let xntable_of_z := gen_true_false Z_TABLE_XNTABLE stage1_table_attributes_value in
    let pxntable_of_z := gen_true_false Z_TABLE_PXNTABLE stage1_table_attributes_value in
    mkStage1TableAttributes nstable_of_z aptable1_of_z aptable0_of_z xntable_of_z pxntable_of_z.

  Definition Stage1BlockAttributes_to_ATTR_VALUES (stage1_block_attributes : Stage1BlockAttributes) : Z :=
    match stage1_block_attributes with
    | mkStage1BlockAttributes xn pxn contiguous dbm ng af sh ap ns attrindx
      => let xn_to_n := zshift_or_0 xn Z_STAGE1_XN in
        let pxn_to_n := zshift_or_0 pxn Z_STAGE1_PXN in
        let contiguous_to_n := zshift_or_0 contiguous Z_STAGE1_CONTIGUOUS in
        let dbm_to_n := zshift_or_0 dbm Z_STAGE1_DBM in
        let ng_to_n := zshift_or_0 ng Z_STAGE1_NG in
        let af_to_n := zshift_or_0 af Z_STAGE1_AF in
        let sh_to_n := Z_STAGE1_SH_GEN (match sh with
                                        | NON_SHAREABLE =>  Z_NON_SHAREABLE
                                        | OUTER_SHAREABLE => Z_OUTER_SHAREABLE 
                                        | INNER_SHAREABLE => Z_INNER_SHAREABLE 
                                        end) in
        let ap_to_n := Z_STAGE1_AP_GEN (match ap with
                                        | STAGE1_READONLY => Z_STAGE1_READONLY
                                        | STAGE1_READWRITE => Z_STAGE1_READWRITE
                                        end) in
        let ns_to_n := zshift_or_0 ns Z_STAGE1_NS in
        let attrindx_to_n := Z_STAGE1_ATTRINDX_GEN (match attrindx with
                                                    | STAGE1_DEVICEINDX => Z_STAGE1_DEVICEINDX
                                                    | STAGE1_NORMALINDX => Z_STAGE1_NORMALINDX
                                                    end) in
        xn_to_n + pxn_to_n + contiguous_to_n + dbm_to_n + ng_to_n + af_to_n + sh_to_n + ap_to_n + ns_to_n + attrindx_to_n
    end.

  Definition ATTR_VALUES_to_Stage1BlockAttributes (stage1_block_attributes_value : Z) : option Stage1BlockAttributes :=
    let xn_of_z := gen_true_false Z_STAGE1_XN stage1_block_attributes_value in
    let pxn_of_z := gen_true_false Z_STAGE1_PXN stage1_block_attributes_value in
    let contiguous_of_z := gen_true_false Z_STAGE1_CONTIGUOUS stage1_block_attributes_value in
    let dbm_of_z := gen_true_false Z_STAGE1_DBM stage1_block_attributes_value in
    let ng_of_z := gen_true_false Z_STAGE1_NG stage1_block_attributes_value in
    let af_of_z := gen_true_false Z_STAGE1_AF stage1_block_attributes_value in
    let sh_of_z := if x_bit_no_exist 1 Z_STAGE1_SH stage1_block_attributes_value
                   then if x_bit_no_exist 2 Z_STAGE1_SH stage1_block_attributes_value
                        then (* 0 << 8 *) Some NON_SHAREABLE
                        else (* 2 << 8 *) Some OUTER_SHAREABLE
                   else if x_bit_no_exist 2 Z_STAGE1_SH stage1_block_attributes_value
                        then (* 1 << 8 *) None
                        else (* 3 << 8 *) Some INNER_SHAREABLE in
    let ap_of_z := if x_bit_no_exist 1 Z_STAGE1_AP stage1_block_attributes_value
                   then if x_bit_no_exist 2 Z_STAGE1_AP stage1_block_attributes_value
                        then (* 0 << 6 *) Some STAGE1_READWRITE
                        else (* 2 << 6 *) Some STAGE1_READONLY
                   else (* 1 << 6 or 3 << 6 *) None in
    let ns_of_z := gen_true_false Z_STAGE1_NS stage1_block_attributes_value in
    let attrindx_of_n := if x_bit_no_exist 1 Z_STAGE1_ATTRINDX stage1_block_attributes_value
                         then if x_bit_no_exist 2 Z_STAGE1_ATTRINDX stage1_block_attributes_value
                              then (* 0 << 2 *) Some STAGE1_DEVICEINDX
                              else (* 2 << 2 *) None
                         else if x_bit_no_exist 2 Z_STAGE1_ATTRINDX stage1_block_attributes_value
                              then (* 1 << 2 *) Some STAGE1_NORMALINDX
                              else (* 3 << 2 *) None in
    match (sh_of_z, ap_of_z, attrindx_of_n) with
    | (Some sh_of_z', Some ap_of_z', Some attrindx_of_z') =>
      Some (mkStage1BlockAttributes xn_of_z pxn_of_z contiguous_of_z dbm_of_z
                                    ng_of_z af_of_z sh_of_z' ap_of_z' ns_of_z attrindx_of_z')
    | (_, _, _) => None
    end.

  Definition STAGE2_MEMATTR_VALUE_to_ATTR_VALUES (stage2_memattr_value: STAGE2_MEMATTR_VALUE) : Z :=
    match stage2_memattr_value with
    | STAGE2_MEM_ATTR_GEN outer_attr inner_attr =>
      let outer_val :=
          match outer_attr with
          | MEMATTR_STAGE2_OUTER_ATTR_UNINITIALIZED => 0
          | OUTER_MEM_TYPE_ATTR mem_type =>
            match mem_type with 
            | STAGE2_DEVICE_MEMORY => Z_STAGE2_DEVICE_MEMORY
            | STAGE2_NONCACHEABLE => Z_STAGE2_NONCACHEABLE
            | STAGE2_WRITETHROUGH => Z_STAGE2_WRITETHROUGH
            | STAGE2_WRITEBACK => Z_STAGE2_WRITEBACK
            end
          end in
      let inner_val :=
          match inner_attr with
          | MMATTR_STAGE2_INNER_ATTR_UNINITIALIZED => 0
          | INNER_MEM_TYPE_ATTR mem_type =>
            match mem_type with 
            | STAGE2_DEVICE_MEMORY => Z_STAGE2_DEVICE_MEMORY
            | STAGE2_NONCACHEABLE => Z_STAGE2_NONCACHEABLE
            | STAGE2_WRITETHROUGH => Z_STAGE2_WRITETHROUGH
            | STAGE2_WRITEBACK => Z_STAGE2_WRITEBACK
            end
          | INNER_DEVICE_MEM_TYPE_ATTR device_mem_type =>
            match device_mem_type with
            | STAGE2_DEVICE_nGnRnE => Z_STAGE2_DEVICE_nGnRnE
            | STAGE2_DEVICE_nGnRE => Z_STAGE2_DEVICE_nGnRE
            | STAGE2_DEVICE_nGRE =>  Z_STAGE2_DEVICE_nGRE
            | STAGE2_DEVICE_GRE =>  Z_STAGE2_DEVICE_GRE
            end
          end in
      Z_STAGE2_MEMATTR_GEN outer_val inner_val
    end.

  Definition Stage2BlockAttributes_to_ATTR_VALUES (stage2_block_attributes : Stage2BlockAttributes) : Z :=
    match stage2_block_attributes with
    | mkStage2BlockAttributes xn contiguous dbm sw_owned sw_exclusive af sh s2ap memattr
      => let xn_to_n := Z_STAGE2_XN_GEN (match xn with
                                        | STAGE2_EXECUTE_ALL => Z_STAGE2_EXECUTE_ALL
                                        | STAGE2_EXECUTE_EL0 => Z_STAGE2_EXECUTE_EL0
                                        | STAGE2_EXECUTE_NONE => Z_STAGE2_EXECUTE_NONE
                                        | STAGE2_EXECUTE_EL1 => Z_STAGE2_EXECUTE_EL1
                                        end) in
        let contiguous_to_n := zshift_or_0 contiguous Z_STAGE2_CONTIGUOUS  in
        let dbm_to_n := zshift_or_0 dbm Z_STAGE2_DBM in
        let sw_owned_n := zshift_or_0 sw_owned Z_STAGE2_SW_OWNED in
        let sw_exclusive_n := zshift_or_0 sw_exclusive Z_STAGE2_SW_EXCLUSIVE in
        let af_to_n := zshift_or_0 af Z_STAGE2_AF in
        let sh_to_n := Z_STAGE2_SH_GEN (match sh with
                                        | NON_SHAREABLE => Z_NON_SHAREABLE
                                        | OUTER_SHAREABLE => Z_OUTER_SHAREABLE
                                        | INNER_SHAREABLE => Z_INNER_SHAREABLE
                                        end) in
        let s2ap_to_n := Z_STAGE2_S2AP_GEN (match s2ap with
                                            | STAGE2_ACCESS_NOPERM => 0
                                            | STAGE2_ACCESS_READ => Z_STAGE2_ACCESS_READ
                                            | STAGE2_ACCESS_WRITE => Z_STAGE2_ACCESS_WRITE
                                            | STAGE2_ACCESS_READWRITE => Z_STAGE2_ACCESS_READ + Z_STAGE2_ACCESS_WRITE
                                            end) in 
        let memattr_to_n := STAGE2_MEMATTR_VALUE_to_ATTR_VALUES memattr in
        xn_to_n + contiguous_to_n + dbm_to_n + sw_owned_n + sw_exclusive_n + af_to_n + sh_to_n + s2ap_to_n + memattr_to_n
    end.
  
  (* The following function defines only two things that are used in arch mm module now. It can be extended later. *)  
  Definition ATTR_VALUES_to_Stage2BlockAttributes (stage2_block_attributes_value : Z) : option Stage2BlockAttributes :=
    let xn_of_z := if x_bit_no_exist 1 Z_STAGE2_XN stage2_block_attributes_value
                   then if  x_bit_no_exist 2 Z_STAGE2_XN stage2_block_attributes_value
                        then (* 0 << 53 *) STAGE2_EXECUTE_ALL
                        else (* 2 << 53 *) STAGE2_EXECUTE_NONE
                   else if  x_bit_no_exist 2 Z_STAGE2_XN stage2_block_attributes_value
                        then (* 1 << 53 *) STAGE2_EXECUTE_EL0
                        else (* 3 << 53 *) STAGE2_EXECUTE_EL1 in
    let contiguous_of_z := gen_true_false Z_STAGE2_CONTIGUOUS stage2_block_attributes_value in
    let dbm_of_z := gen_true_false Z_STAGE2_DBM stage2_block_attributes_value in
    let sw_owned_of_z := gen_true_false Z_STAGE2_SW_OWNED stage2_block_attributes_value in
    let sw_exclusive_of_z := gen_true_false Z_STAGE2_SW_EXCLUSIVE stage2_block_attributes_value in
    let af_of_z := gen_true_false Z_STAGE2_AF stage2_block_attributes_value in
    let sh_of_z := if  x_bit_no_exist 1 Z_STAGE2_SH stage2_block_attributes_value
                   then if  x_bit_no_exist 2 Z_STAGE2_SH stage2_block_attributes_value
                        then (* 0 << 8 *) Some NON_SHAREABLE
                        else (* 2 << 8 *) Some OUTER_SHAREABLE
                   else if x_bit_no_exist 2 Z_STAGE2_SH stage2_block_attributes_value
                        then (* 1 << 8 *) None
                        else (* 3 << 8 *) Some INNER_SHAREABLE in
    let s2ap_of_z := if x_bit_no_exist 1 Z_STAGE2_S2AP stage2_block_attributes_value
                     then if x_bit_no_exist 2 Z_STAGE2_S2AP stage2_block_attributes_value
                          then (* 0 << 6 *) STAGE2_ACCESS_NOPERM
                          else (* 2 << 6 *) STAGE2_ACCESS_WRITE
                     else if x_bit_no_exist 2 Z_STAGE2_S2AP stage2_block_attributes_value
                          then (* 1 << 6 *) STAGE2_ACCESS_READ
                          else (* 3 << 6 *) STAGE2_ACCESS_READWRITE in
    let memattr_outer_of_z := if x_bit_no_exist 1 Z_STAGE2_MEMATTR_OUTER stage2_block_attributes_value
                              then if x_bit_no_exist 2 Z_STAGE2_MEMATTR_OUTER stage2_block_attributes_value
                                   then (* 0 << 4 *) STAGE2_DEVICE_MEMORY
                                   else (* 2 << 4 *) STAGE2_WRITETHROUGH
                              else if x_bit_no_exist 2 Z_STAGE2_MEMATTR_OUTER stage2_block_attributes_value
                                   then (* 1 << 4 *) STAGE2_NONCACHEABLE
                                   else (* 3 << 4 *) STAGE2_WRITEBACK in
    let memattr_inner_of_z :=
        match memattr_outer_of_z with
        | STAGE2_DEVICE_MEMORY =>
          let inner_device_mem_type := 
              if x_bit_no_exist 1 Z_STAGE2_MEMATTR_OUTER stage2_block_attributes_value
              then if x_bit_no_exist 2 Z_STAGE2_MEMATTR_INNER stage2_block_attributes_value
                   then (* 0 << 4 *) STAGE2_DEVICE_nGnRnE
                   else (* 2 << 4 *) STAGE2_DEVICE_nGnRE
              else if x_bit_no_exist 2 Z_STAGE2_MEMATTR_INNER stage2_block_attributes_value
                   then (* 1 << 4 *) STAGE2_DEVICE_nGnRE
                   else (* 3 << 4 *) STAGE2_DEVICE_GRE in
          INNER_DEVICE_MEM_TYPE_ATTR inner_device_mem_type
        | _ =>
          let inner_mem_type := 
              if x_bit_no_exist 1 Z_STAGE2_MEMATTR_INNER stage2_block_attributes_value
              then if x_bit_no_exist 2 Z_STAGE2_MEMATTR_INNER stage2_block_attributes_value
                   then (* 0 << 4 *) STAGE2_DEVICE_MEMORY
                   else (* 2 << 4 *) STAGE2_WRITETHROUGH
              else if x_bit_no_exist 2 Z_STAGE2_MEMATTR_INNER stage2_block_attributes_value
                   then (* 1 << 4 *) STAGE2_NONCACHEABLE
                   else (* 3 << 4 *) STAGE2_WRITEBACK in
          INNER_MEM_TYPE_ATTR inner_mem_type
        end in
    let memattr_of_z := STAGE2_MEM_ATTR_GEN (OUTER_MEM_TYPE_ATTR memattr_outer_of_z) memattr_inner_of_z in
    match sh_of_z with
    | Some sh_of_z' =>
      Some (mkStage2BlockAttributes xn_of_z contiguous_of_z dbm_of_z sw_owned_of_z sw_exclusive_of_z
                                    af_of_z sh_of_z' s2ap_of_z memattr_of_z)
    | None => None
    end.                                            

  Definition HAS_PTE_TABLE (value : Z) :=
    if (bit_no_exist Z_PTE_TABLE value) then false else true.
    
  Definition HAS_PTE_VALID (value : Z) := 
    if (bit_no_exist Z_PTE_VALID value) then false else true.

  Definition GET_ADDRESS (value : Z) :=
    let address_with_shift := Z.land value Z_PTE_ADDR_MASK in
    Z.shiftr address_with_shift Z_PAGE_BITS.
  
  Definition PTE_TYPES_to_IS_VALID_VALUE (pte_value : PTE_TYPES) : Z :=
    match pte_value with
    | UNDEFINED => 0
    | ABSENT => 0
    (* for level 0 - IS_TABLE is on, IS_VALID is off *)      
    | STAGE1_INVALID_BLOCK_LEVEL0 _ _  => 0
    (* for level 1, 2 - IS_TABLE is off, IS_VALID is off *)      
    | STAGE1_INVALID_BLOCK _ _  =>  0
    (* for level 0, 1 - IS_TABLE is on and IS_VALID is on *)                                     
    | STAGE1_TABLE _ _ => Z.shiftl 1 Z_PTE_VALID
    (* for level 1 - IS_TABLE is off and IS_VALID is on *)
    | STAGE1_BLOCK _ _ => Z.shiftl 1 Z_PTE_VALID
    (* for level 2 - IS_TABLE is on and IS_VALID is on *)
    | STAGE1_PAGE _ _ => Z.shiftl 1 Z_PTE_VALID
    (* for level 0 - IS_TABLE is on, IS_VALID is off *)
    | STAGE2_INVALID_BLOCK_LEVEL0 _  => 0
    (* for level 1, 2, 3 - IS_TABLE is off, IS_VALID is off *)
    | STAGE2_INVALID_BLOCK _ _ => 0
    (* for level 0, 1, 2 - IS_TABLE is on and IS_VALID is on *)
    | STAGE2_TABLE _ => Z.shiftl 1 Z_PTE_VALID
    (* for level 1, 2 - IS_TABLE is off and IS_VALID is on *)
    | STAGE2_BLOCK _ _ => Z.shiftl 1 Z_PTE_VALID
    (* for level 3 - IS_TABLE is on and IS_VALID is on *)
    | STAGE2_PAGE _ _ => Z.shiftl 1 Z_PTE_VALID
    end.

  Definition PTE_TYPES_to_IS_TABLE_VALUE (pte_value : PTE_TYPES) : Z :=
    match pte_value with
    | UNDEFINED => 0
    | ABSENT => 0
    (* for level 0 - IS_TABLE is on, IS_VALID is off *)      
    | STAGE1_INVALID_BLOCK_LEVEL0 _ _  => Z.shiftl 1 Z_PTE_TABLE
    (* for level 1, 2 - IS_TABLE is off, IS_VALID is off *)
    | STAGE1_INVALID_BLOCK _ _ => 0
    (* for level 0, 1 - IS_TABLE is on and IS_VALID is on *)                                   
    | STAGE1_TABLE _ _ => Z.shiftl 1 Z_PTE_TABLE
    (* for level 1 - IS_TABLE is off and IS_VALID is on *)                                  
    | STAGE1_BLOCK _ _  =>  0
    (* for level 2 - IS_TABLE is on and IS_VALID is on *)
    | STAGE1_PAGE _ _ => Z.shiftl 1 Z_PTE_TABLE
    (* for level 0 - IS_TABLE is on, IS_VALID is off *)                                 
    | STAGE2_INVALID_BLOCK_LEVEL0 _  => Z.shiftl 1 Z_PTE_TABLE
    (* for level 1, 2, 3 - IS_TABLE is off, IS_VALID is off *)                                 
    | STAGE2_INVALID_BLOCK _ _ => 0
    (* for level 0, 1, 2 - IS_TABLE is on and IS_VALID is on *)                                   
    | STAGE2_TABLE _  => Z.shiftl 1 Z_PTE_TABLE
    (* for level 1, 2 - IS_TABLE is off and IS_VALID is on *)                                 
    | STAGE2_BLOCK _ _  =>  0
    (* for level 3 - IS_TABLE is on and IS_VALID is on *)                             
    | STAGE2_PAGE _ _ => Z.shiftl 1 Z_PTE_TABLE
    end.
  
  Definition PTE_TYPES_to_ATTR_VALUES (pte_value : PTE_TYPES) : Z :=
    match pte_value with
    | UNDEFINED => 0
    | ABSENT => 0
    (* for level 0 - IS_TABLE is on, IS_VALID is off *)      
    | STAGE1_INVALID_BLOCK_LEVEL0 _ attributes  => Stage1TableAttributes_to_ATTR_VALUES attributes
    (* for level 1, 2 - IS_TABLE is off, IS_VALID is off *)
    | STAGE1_INVALID_BLOCK _ attributes =>  Stage1BlockAttributes_to_ATTR_VALUES attributes 
    (* for level 0, 1 - IS_TABLE is on and IS_VALID is on *)                                   
    | STAGE1_TABLE _ attributes => Stage1TableAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 Z_PTE_VALID
    (* for level 1 - IS_TABLE is off and IS_VALID is on *)                                  
    | STAGE1_BLOCK _ attributes => Stage1BlockAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 Z_PTE_VALID
    (* for level 2 - IS_TABLE is on and IS_VALID is on *)
    | STAGE1_PAGE _ attributes => Stage1BlockAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 Z_PTE_VALID
    (* for level 0 - IS_TABLE is on, IS_VALID is off *)                                 
    | STAGE2_INVALID_BLOCK_LEVEL0 _ => 0
    (* for level 1, 2, 3 - IS_TABLE is off, IS_VALID is off *)       
    | STAGE2_INVALID_BLOCK _ attributes => Stage2BlockAttributes_to_ATTR_VALUES attributes
    (* for level 0, 1, 2 - IS_TABLE is on and IS_VALID is on *)                                   
    | STAGE2_TABLE _  => Z.shiftl 1 Z_PTE_VALID
    (* for level 1, 2 - IS_TABLE is off and IS_VALID is on *)                                 
    | STAGE2_BLOCK _ attributes => Stage2BlockAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 Z_PTE_VALID
    (* for level 3 - IS_TABLE is on and IS_VALID is on *)                             
    | STAGE2_PAGE _ attributes => Stage2BlockAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 Z_PTE_VALID
    end.

  Definition PTE_TYPES_to_OUTPUT_ADDRESS (pte : PTE_TYPES) : Z :=
    match pte with
    | UNDEFINED => 0
    | ABSENT => 0
    | STAGE1_INVALID_BLOCK_LEVEL0 oa _
    | STAGE1_INVALID_BLOCK oa _
    | STAGE1_TABLE oa _
    | STAGE1_BLOCK oa _
    | STAGE1_PAGE oa _
    | STAGE2_INVALID_BLOCK_LEVEL0 oa
    | STAGE2_INVALID_BLOCK oa _
    | STAGE2_TABLE oa
    | STAGE2_BLOCK oa _ 
    | STAGE2_PAGE oa _ => oa
    end.
  
  Definition PTE_TYPES_to_OUTPUT_ADDRESS_WITH_SHIFT (pte : PTE_TYPES) : Z :=
    Z.shiftl (PTE_TYPES_to_OUTPUT_ADDRESS pte) Z_PAGE_BITS.

  Definition PTE_TYPES_to_VALUES (pte : PTE_TYPES) : Z :=
    PTE_TYPES_to_OUTPUT_ADDRESS_WITH_SHIFT pte +
    PTE_TYPES_to_ATTR_VALUES pte +
    PTE_TYPES_to_IS_TABLE_VALUE pte.  


  Definition VALUES_to_PTE_TYPES_STAGE1 (level : Z) (value: Z) : option PTE_TYPES  :=
    if zeq level 0 then
      match HAS_PTE_TABLE value with
      | true => 
        match HAS_PTE_VALID value with
        | true => match ATTR_VALUES_to_Stage1TableAttributes value with
                 | attrs =>  Some (STAGE1_TABLE  (GET_ADDRESS value) attrs)
                 end
        | false => match ATTR_VALUES_to_Stage1TableAttributes value with
                  | attrs =>  Some (STAGE1_INVALID_BLOCK_LEVEL0  (GET_ADDRESS value) attrs)
                  end
        end
      | false => None
      end
    else 
      match HAS_PTE_VALID value with
      | true =>
        match HAS_PTE_TABLE value with
        | true => if zeq level 1 then
                   match ATTR_VALUES_to_Stage1TableAttributes value with
                   | attrs =>  Some (STAGE1_TABLE  (GET_ADDRESS value) attrs)
                   end
                 else if zeq level 2 then
                        match ATTR_VALUES_to_Stage1BlockAttributes value with
                        | Some attrs =>  Some (STAGE1_PAGE  (GET_ADDRESS value) attrs)
                        | None => None
                        end
                      else None
        | false =>  if zeq level 1 then
                     match ATTR_VALUES_to_Stage1BlockAttributes value with
                     | Some attrs =>  Some (STAGE1_BLOCK (GET_ADDRESS value) attrs)
                     | None => None
                     end
                   else None
        end
      | false =>
        match HAS_PTE_TABLE value with
        | true => None
        | false =>
          if zeq level 1 || zeq level 2
          then
            match ATTR_VALUES_to_Stage1BlockAttributes value with
            | Some attrs =>  Some (STAGE1_INVALID_BLOCK (GET_ADDRESS value) attrs)
            | None => None
            end
          else None
        end
      end.

  Definition VALUES_to_PTE_TYPES_STAGE2 (level : Z) (value: Z) : option PTE_TYPES  :=
    if zeq level 0 then
      match HAS_PTE_TABLE value with
      | true => 
        match HAS_PTE_VALID value with
        | true => Some (STAGE2_TABLE  (GET_ADDRESS value))
        | false => Some (STAGE2_INVALID_BLOCK_LEVEL0  (GET_ADDRESS value))
        end
      | false => None
      end
    else 
      match HAS_PTE_VALID value with
      | true =>
        match HAS_PTE_TABLE value with
        | true => if zeq level 1 || zeq level 2 then
                   Some (STAGE2_TABLE (GET_ADDRESS value))
                 else if zeq level 3 then
                        match ATTR_VALUES_to_Stage2BlockAttributes value with
                        | Some attrs =>  Some (STAGE2_PAGE  (GET_ADDRESS value) attrs)
                        | None => None
                        end
                      else None
        | false =>  if zeq level 1 || zeq level 2 then
                     match ATTR_VALUES_to_Stage2BlockAttributes value with
                     | Some attrs =>  Some (STAGE2_BLOCK (GET_ADDRESS value) attrs)
                     | None => None
                     end
                   else None
        end
      | false =>
        match HAS_PTE_TABLE value with
        | true => None
        | false =>
          if zeq level 1 || zeq level 2 || zeq level 3
          then
            match ATTR_VALUES_to_Stage2BlockAttributes value with
            | Some attrs =>  Some (STAGE2_INVALID_BLOCK (GET_ADDRESS value) attrs)
            | None => None
            end
          else None
        end
      end.

  
  Definition VALUES_to_PTE_TYPES (level : Z) (stage : CURRENT_STAGE) (value: Z) : option PTE_TYPES :=
    match stage with
    | STAGE1 => VALUES_to_PTE_TYPES_STAGE1 level value
    | STAGE2 => VALUES_to_PTE_TYPES_STAGE2 level value
    end.

End FLAG_TO_VALUE_and_VALUE_TO_FLAG.

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
  
Definition Z_MM_MODE_R : Z := 1.
Definition Z_MM_MODE_W : Z := 2. 
Definition Z_MM_MODE_X : Z := 4.
Definition Z_MM_MODE_D : Z := 8.

Definition Z_MM_MODE_UNOWNED : Z := 16.
Definition Z_MM_MODE_INVALID : Z := 32.
Definition Z_MM_MODE_SHARED : Z := 64.
 
End MM_MODE_VALUE.

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

Section ArchMMHighSpec.
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

  Definition arch_mm_absent_pte_spec (level: Z) : itree ArchMME (Z) :=
    Ret (0).

  Definition arch_mm_absent_pte_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong level)] =>
      res <-  arch_mm_absent_pte_spec (Int64.unsigned level);;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
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
  
  Definition arch_mm_table_pte_spec (level : Z) (pa: Z) : itree ArchMME (PTE_TYPES) :=
    st <- trigger GetState;;
    let no_address := Z.land pa (Z_not Z_PTE_ADDR_MASK) in      
    let address := Z.shiftr (Z.land pa Z_PTE_ADDR_MASK) Z_PAGE_BITS in
    (* create a new page table entry *)
    let new_pte :=
        match st.(stage) with
        | STAGE1 =>
          if zeq level 0 || zeq level 1
          then Some (STAGE1_TABLE address init_stage1_table_attributes)
          else if zeq level 2
               then Some (STAGE1_PAGE address init_stage1_block_attributes)
               else None
        | STAGE2 =>
          if zeq level 0 || zeq level 1 || zeq level 2
          then Some (STAGE2_TABLE address)
          else if zeq level 3
               then Some (STAGE2_PAGE address init_stage2_block_attributes)
               else None
        end in
    if zeq no_address 0 then 
      match new_pte with
      | Some pte' => Ret (pte')
      | None => triggerUB "wrong result"
      end
    else triggerUB "wrong result".
                   
       
  Definition arch_mm_table_pte_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong level); Vcomp (Vlong pa)] =>
      pte <- arch_mm_table_pte_spec (Int64.unsigned level) (Int64.unsigned pa);;
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

  
  Definition arch_mm_block_pte_spec (level : Z) (pa: Z) (attrs: Z) : itree ArchMME (PTE_TYPES) :=
    st <- trigger GetState;;
    let no_address := Z.land pa (Z_not Z_PTE_ADDR_MASK) in      
    let address := Z.shiftr (Z.land pa Z_PTE_ADDR_MASK) Z_PAGE_BITS in
    (* create a new page table entry *)
    let new_pte :=
        match st.(stage) with
        | STAGE1 =>
          match HAS_PTE_VALID attrs, HAS_PTE_TABLE attrs with
          | true, true => if zeq level 1 || zeq level 0 then
                           Some (STAGE1_TABLE address (ATTR_VALUES_to_Stage1TableAttributes attrs))
                         else if zeq level 2 then  
                                match ATTR_VALUES_to_Stage1BlockAttributes attrs with
                                | Some attrs' => Some (STAGE1_PAGE address attrs')
                                | None => None
                                end
                              else None
          | true, false => if zeq level 1 then
                            match ATTR_VALUES_to_Stage1BlockAttributes attrs with
                            | Some attrs' => Some (STAGE1_BLOCK address attrs')
                            | None => None
                            end
                            else None
          | false, true => if zeq level 0 then
                            Some (STAGE1_INVALID_BLOCK_LEVEL0 address (ATTR_VALUES_to_Stage1TableAttributes attrs))
                          else None
          | false, false =>  if zeq level 1 || zeq level 2 then
                              match ATTR_VALUES_to_Stage1BlockAttributes attrs with
                              | Some attrs' => Some (STAGE1_INVALID_BLOCK address attrs')
                              | None => None
                              end
                            else None
          end
        | STAGE2 =>
          match HAS_PTE_VALID attrs, HAS_PTE_TABLE attrs with
          | true, true => if zeq level 1 || zeq level 0 || zeq level 2 then
                           Some (STAGE2_TABLE address)
                         else if zeq level 3 then  
                                match ATTR_VALUES_to_Stage2BlockAttributes attrs with
                                | Some attrs' => Some (STAGE2_PAGE address attrs')
                                | None => None
                                end
                              else None
          | true, false => if zeq level 1 || zeq level 2 then
                            match ATTR_VALUES_to_Stage2BlockAttributes attrs with
                            | Some attrs' => Some (STAGE2_BLOCK address attrs')
                            | None => None
                            end
                            else None
          | false, true => if zeq level 0 then
                            Some (STAGE2_INVALID_BLOCK_LEVEL0 address)
                          else None
          | false, false =>  if zeq level 1 || zeq level 2 || zeq level 3 then
                              match ATTR_VALUES_to_Stage2BlockAttributes attrs with
                              | Some attrs' => Some (STAGE2_INVALID_BLOCK address attrs')
                              | None => None
                              end
                            else None
          end
        end in
    if zeq no_address 0 then 
      match new_pte with
      | Some pte' => Ret (pte')
      | None => triggerUB "wrong result"
      end
    else triggerUB "wrong result".

  
  Definition arch_mm_block_pte_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong level); Vcomp (Vlong pa); Vcomp (Vlong attrs)] =>
      pte <- arch_mm_block_pte_spec (Int64.unsigned level) (Int64.unsigned pa)  (Int64.unsigned attrs);;
      Ret (Vcomp (Vlong (Int64.repr (PTE_TYPES_to_VALUES pte))), args)
    | _ => triggerUB "arch_mm_table_pte_call: wrong arguments"
    end.
  
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

  Definition arch_mm_pte_is_valid_spec (pte: Z)  (level : Z) : itree ArchMME (bool) :=
    st <- trigger GetState;;
    match VALUES_to_PTE_TYPES  level st.(stage) pte with
    | Some pte =>
      match pte with
      | STAGE1_TABLE _ _
      | STAGE1_BLOCK _ _ 
      | STAGE1_PAGE _ _
      | STAGE2_TABLE _
      | STAGE2_BLOCK _ _
      | STAGE2_PAGE _ _ => Ret (true)
      | _ => Ret (false)
      end
    | None => triggerUB "wrong results"
    end.

  Definition arch_mm_pte_is_valid_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong pte); Vcomp (Vlong level)] =>
      res <- arch_mm_pte_is_valid_spec (Int64.unsigned pte) (Int64.unsigned level);;
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

  Definition arch_mm_pte_is_present_spec (pte: Z)  (level : Z) : itree ArchMME (bool) :=
    st <- trigger GetState;;
    match VALUES_to_PTE_TYPES level st.(stage) pte with
    | Some pte =>
      match pte with
      | STAGE1_TABLE _ _
      | STAGE1_BLOCK _ _ 
      | STAGE1_PAGE _ _
      | STAGE2_TABLE _
      | STAGE2_BLOCK _ _
      | STAGE2_PAGE _ _ => Ret (true)
      | STAGE2_INVALID_BLOCK _ attributes => match attributes.(STAGE2_SW_OWNED) with
                                            | true => Ret (true)
                                            | _ => Ret (false)
                                            end
      | _ => Ret (false)
      end
    | None => triggerUB "wrong results"
    end.
  
  Definition arch_mm_pte_is_present_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong pte); Vcomp (Vlong level)] =>
      res <- arch_mm_pte_is_present_spec (Int64.unsigned pte) (Int64.unsigned level);;
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

  Definition arch_mm_pte_is_table_spec (pte: Z)  (level : Z) : itree ArchMME (bool) :=
    st <- trigger GetState;;
    if (zle level 0)
    then Ret (false)
    else
      match VALUES_to_PTE_TYPES  level st.(stage) pte with
      | Some pte =>
        match pte with
        | STAGE1_TABLE _ _ 
        | STAGE1_PAGE _ _
        | STAGE2_TABLE _
        | STAGE2_PAGE _ _ => Ret (true)
        | _ => Ret (false)
        end
      | None => triggerUB "wrong results"
      end.
      

  Definition arch_mm_pte_is_table_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong pte); Vcomp (Vlong level)] =>
      res <- arch_mm_pte_is_table_spec (Int64.unsigned pte) (Int64.unsigned level);;
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

  
  Definition arch_mm_pte_is_block_spec (pte: Z)  (level : Z) : itree ArchMME (bool) :=
    st <- trigger GetState;;
    if (zle level 2)
    then
      match VALUES_to_PTE_TYPES  level st.(stage) pte with
      | Some pte =>
        match pte with
        | STAGE1_INVALID_BLOCK_LEVEL0 _ _ => Ret (true)
        | STAGE1_TABLE _ _ => if zeq level 0 then Ret (true) else Ret (false)
        | STAGE2_INVALID_BLOCK_LEVEL0 _ => Ret (true)
        | STAGE2_TABLE _ => if zeq level 0 then Ret (true) else Ret (false)
        | _ => Ret (false)
        end
      | None => triggerUB "wrong results"
      end
    else Ret (false).
    

  Definition arch_mm_pte_is_block_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong pte); Vcomp (Vlong level)] =>
      res <- arch_mm_pte_is_block_spec (Int64.unsigned pte) (Int64.unsigned level);;
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

  (* IT does not have level information, so we cannot convert it into PTE_TYPES at 
     this moment *)
  Definition pte_addr_spec (pte: Z) : itree ArchMME (Z) :=
    Ret (Z.land pte Z_PTE_ADDR_MASK).
       
  Definition pte_addr_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong pte)] =>
      res <- pte_addr_spec (Int64.unsigned pte);;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
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

  (* It does not have level information, so we cannot convert it into PTE_TYPES at 
     this moment *)
  Definition arch_mm_clear_pa_spec (pa: Z) : itree ArchMME (Z) :=
    st <- trigger GetState;;
    Ret (Z.land pa Z_PTE_ADDR_MASK).
       
  Definition arch_mm_clear_pa_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong pa)] =>
      res <- arch_mm_clear_pa_spec (Int64.unsigned pa);;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
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

 Definition arch_mm_block_from_pte_spec (pte: Z) (level : Z) : itree ArchMME (Z) :=
    Ret (Z.land pte Z_PTE_ADDR_MASK).

 Definition arch_mm_block_from_pte_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
   match args with 
   | [Vcomp (Vlong pte); Vcomp (Vlong level)] =>
     res <- arch_mm_block_from_pte_spec (Int64.unsigned pte) (Int64.unsigned level);;
     Ret (Vcomp (Vlong (Int64.repr res)), args)
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

 Definition arch_mm_table_from_pte_spec (pte: Z) (level : Z) : itree ArchMME (Z) :=
   st <- trigger GetState;;
   match VALUES_to_PTE_TYPES  level st.(stage) pte with
   | Some pte =>
     match pte with
     | STAGE1_TABLE oa _
     | STAGE2_TABLE oa => Ret (Z.shiftl oa Z_PAGE_BITS)
     | _ => triggerUB "wrong results"
     end
   | None => triggerUB "wrong results"
   end.
     
 Definition arch_mm_table_from_pte_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
   match args with 
   | [Vcomp (Vlong pte); Vcomp (Vlong level)] =>
     res <- arch_mm_table_from_pte_spec (Int64.unsigned pte) (Int64.unsigned level);;
     Ret (Vcomp (Vlong (Int64.repr res)), args)
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

       
  Definition arch_mm_pte_attrs_spec (pte: Z) (level : Z) : itree ArchMME (Z) :=
   st <- trigger GetState;;
   match VALUES_to_PTE_TYPES  level st.(stage) pte with
   | Some pte_types => Ret (PTE_TYPES_to_ATTR_VALUES pte_types)
   | _ => triggerUB "wrong results"
   end.
    
       (*
    (* TODO : need to fix for the sanity check *)
    Ret (Z.land pte Z_PTE_ATTR_MASK).
        *)
       
  Definition arch_mm_pte_attrs_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong pte); Vcomp (Vlong level)] =>
      res <- arch_mm_pte_attrs_spec (Int64.unsigned pte) (Int64.unsigned level);;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerUB "arch_mm_pte_attrs_call: wrong arguments"
    end
       .

  (*
/**
 * Invalidates stage-1 TLB entries referring to the given virtual address range.
 */
void arch_mm_invalidate_stage1_range(vaddr_t va_begin, vaddr_t va_end)
{
    uintvaddr_t begin = va_addr(va_begin);
    uintvaddr_t end = va_addr(va_end);
    uintvaddr_t it;

    /* Sync with page table updates. */
    dsb(ishst);

    /*
     * Revisions prior to Armv8.4 do not support invalidating a range of
     * addresses, which means we have to loop over individual pages. If
     * there are too many, it is quicker to invalidate all TLB entries.
     */
    if ((end - begin) > (MAX_TLBI_OPS * PAGE_SIZE)) {
        if (VM_TOOLCHAIN == 1) {
            tlbi(vmalle1is);
        } else {
            tlbi(alle2is);
        }
    } else {
        begin >>= 12;
        end >>= 12;
        /* Invalidate stage-1 TLB, one page from the range at a time. */
        for (it = begin; it < end;
             it += (UINT64_C(1) << (PAGE_BITS - 12))) {
            if (VM_TOOLCHAIN == 1) {
                tlbi_reg(vae1is, it);
            } else {
                tlbi_reg(vae2is, it);
            }
        }
    }

    /* Sync data accesses with TLB invalidation completion. */
    dsb(ish);

    /* Sync instruction fetches with TLB invalidation completion. */
    isb();
}

   *)

 Definition arch_mm_invalidate_stage1_range_spec (va_begin va_end : Z) : itree ArchMME (unit) :=
    st <- trigger GetState;;
    Ret (tt)
       .
       
  Definition arch_mm_invalidate_stage1_range_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong va_begin); Vcomp (Vlong va_end)] =>
      res <- arch_mm_invalidate_stage1_range_spec (Int64.unsigned va_begin) (Int64.unsigned va_end);;
      Ret (Vnull, args)
    | _ => triggerUB "arch_mm_invalidate_stage1_range_call: wrong arguments"
    end
       .

  (*
/**
 * Invalidates stage-2 TLB entries referring to the given intermediate physical
 * address range.
 */
void arch_mm_invalidate_stage2_range(ipaddr_t va_begin, ipaddr_t va_end)
{
    uintpaddr_t begin = ipa_addr(va_begin);
    uintpaddr_t end = ipa_addr(va_end);
    uintpaddr_t it;

    /* TODO: This only applies to the current VMID. */

    /* Sync with page table updates. */
    dsb(ishst);

    /*
     * Revisions prior to Armv8.4 do not support invalidating a range of
     * addresses, which means we have to loop over individual pages. If
     * there are too many, it is quicker to invalidate all TLB entries.
     */
    if ((end - begin) > (MAX_TLBI_OPS * PAGE_SIZE)) {
        /*
         * Invalidate all stage-1 and stage-2 entries of the TLB for
         * the current VMID.
         */
        tlbi(vmalls12e1is);
    } else {
        begin >>= 12;
        end >>= 12;

        /*
         * Invalidate stage-2 TLB, one page from the range at a time.
         * Note that this has no effect if the CPU has a TLB with
         * combined stage-1/stage-2 translation.
         */
        for (it = begin; it < end;
             it += (UINT64_C(1) << (PAGE_BITS - 12))) {
            tlbi_reg(ipas2e1is, it);
        }

        /*
         * Ensure completion of stage-2 invalidation in case a page
         * table walk on another CPU refilled the TLB with a complete
         * stage-1 + stage-2 walk based on the old stage-2 mapping.
         */
        dsb(ish);

        /*
         * Invalidate all stage-1 TLB entries. If the CPU has a combined
         * TLB for stage-1 and stage-2, this will invalidate stage-2 as
         * well.
         */
        tlbi(vmalle1is);
    }

    /* Sync data accesses with TLB invalidation completion. */
    dsb(ish);

    /* Sync instruction fetches with TLB invalidation completion. */
    isb();
}

   *)
       
 Definition arch_mm_invalidate_stage2_range_spec (va_begin va_end : Z) : itree ArchMME (unit) :=
    st <- trigger GetState;;
    Ret (tt)
       .
       
  Definition arch_mm_invalidate_stage2_range_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [Vcomp (Vlong va_begin); Vcomp (Vlong va_end)] =>
      res <- arch_mm_invalidate_stage2_range_spec (Int64.unsigned va_begin) (Int64.unsigned va_end);;
      Ret (Vnull, args)
    | _ => triggerUB "arch_mm_invalidate_stage2_range_call: wrong arguments"
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
    let attrs1 := Z.lor attrs0 (Z.lor (zshift_or_0 true Z_STAGE1_AF) (Z_STAGE1_SH_GEN Z_OUTER_SHAREABLE)) in
                  (* STAGE1_AF *)  (* STAGE1_SH(OUTER_SHAREABLE) *)
    let attrs2 := if zeq 0 (Z.land mode Z_MM_MODE_X)
                  then Z.lor attrs1 (zshift_or_0 true Z_STAGE1_XN)  (* STAGE1_XN *)
                  else attrs1 in
    let attrs3 := if zeq 0 (Z.land mode Z_MM_MODE_W)
                  then Z.lor attrs2 (Z_STAGE1_AP_GEN Z_STAGE1_READONLY) (* STAGE1_AP(STAGE1_READONLY) *)
                  else Z.lor attrs2  (Z_STAGE1_AP_GEN Z_STAGE1_READWRITE) in (* STAGE1_AP(STAGE1_READWRITE) *)
    let attrs4 := if zeq 0 (Z.land mode Z_MM_MODE_D)
                  then Z.lor attrs3 (Z_STAGE1_ATTRINDX_GEN Z_STAGE1_NORMALINDX) (* STAGE1_ATTRINDX(STAGE1_NORMALINDX) *)
                  else Z.lor attrs3 (Z_STAGE1_ATTRINDX_GEN Z_STAGE1_DEVICEINDX) in (* STAGE1_ATTRINDX(STAGE1_DEVICEINDX) *)
    let attrs5 := if zeq 0 (Z.land mode Z_MM_MODE_INVALID)
                  then Z.lor attrs4 (zshift_or_0 true Z_PTE_VALID) (* PTE_VALID *)
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
  
  Definition arch_mm_mode_to_stage2_attrs_spec (mode : Z) : itree ArchMME (Z) :=
    let attrs0 := 0 in
    let access0 := 0 in 
    let attrs1 := Z.lor attrs0 (Z.lor (zshift_or_0 true Z_STAGE2_AF) (Z_STAGE2_SH_GEN Z_NON_SHAREABLE)) in
    let access1 := if zeq 0 (Z.land mode Z_MM_MODE_R)
                   then access0
                   else Z.lor access0 Z_STAGE2_ACCESS_READ in
    let access2 := if zeq 0 (Z.land mode Z_MM_MODE_W)
                   then access1
                   else Z.lor access1 Z_STAGE2_ACCESS_WRITE in
    let attrs2 := Z.lor attrs1 (Z_STAGE2_S2AP_GEN access2) in
    let attrs3 := if zeq 0 (Z.land mode Z_MM_MODE_X)
                  then Z.lor attrs2 (Z_STAGE2_XN_GEN Z_STAGE2_EXECUTE_NONE)
                  else Z.lor attrs2 (Z_STAGE2_XN_GEN Z_STAGE2_EXECUTE_ALL) in
    let attrs4 := if zeq 0 (Z.land mode Z_MM_MODE_D)
                  then Z.lor attrs3 (Z_STAGE2_MEMATTR_GEN Z_STAGE2_WRITEBACK Z_STAGE2_WRITEBACK)
                  else Z.lor attrs3 (Z_STAGE2_MEMATTR_GEN Z_STAGE2_DEVICE_MEMORY Z_STAGE2_DEVICE_GRE) in
    let attrs5 := if zeq 0 (Z.land mode Z_MM_MODE_UNOWNED)
                  then Z.lor attrs4 (zshift_or_0 true Z_STAGE2_SW_OWNED)
                  else attrs4 in
    let attrs6 := if zeq 0 (Z.land mode Z_MM_MODE_SHARED)
                  then Z.lor attrs5 (zshift_or_0 true Z_STAGE2_SW_EXCLUSIVE)
                  else attrs5 in
    let attrs7 := if zeq 0 (Z.land mode Z_MM_MODE_INVALID)
                  then Z.lor attrs6 (zshift_or_0 true Z_PTE_VALID)
                  else attrs6 in Ret (attrs7). 


  Definition arch_mm_mode_to_stage2_attrs_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong mode)] =>
      res <- arch_mm_mode_to_stage2_attrs_spec (Int64.unsigned mode);;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "arch_mm_mode_to_stage2_attrs: wrong arguments"
    end
  .  
  
  
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

  Definition arch_mm_stage2_attrs_to_mode_spec (attrs : Z) : itree ArchMME (Z) :=
    let mode0 := 0 in
    let mode1 := if zeq 0 (Z.land attrs (Z_STAGE2_S2AP_GEN Z_STAGE2_ACCESS_READ))
                 then mode0
                 else Z.lor mode0 Z_MM_MODE_R in
    let mode2 := if zeq 0 (Z.land attrs (Z_STAGE2_S2AP_GEN Z_STAGE2_ACCESS_WRITE))
                 then mode1
                 else Z.lor mode1 Z_MM_MODE_W in
    let mode3 := if zeq (Z.land attrs (Z_STAGE2_XN_GEN Z_STAGE2_EXECUTE_MASK))
                        (Z_STAGE2_XN_GEN Z_STAGE2_EXECUTE_ALL)
                 then Z.lor mode2 Z_MM_MODE_X
                 else mode2 in
    let mode4 := if zeq (Z.land attrs (Z_STAGE2_MEMATTR_MASK)) (Z.shiftl Z_STAGE2_DEVICE_MEMORY Z_STAGE2_MEMATTR_OUTER)
                 then Z.lor mode3 Z_MM_MODE_D
                 else mode3 in
    let mode5 := if zeq 0 (Z.land attrs (zshift_or_0 true Z_STAGE2_SW_OWNED))
                 then Z.lor mode4 Z_MM_MODE_UNOWNED
                 else mode4 in
    let mode6 := if zeq 0 (Z.land attrs (zshift_or_0 true Z_STAGE2_SW_EXCLUSIVE))
                 then Z.lor mode5 Z_MM_MODE_SHARED
                 else mode5 in
    let mode7 := if zeq 0 (Z.land attrs (zshift_or_0 true Z_PTE_VALID))
                 then Z.lor mode6 Z_MM_MODE_INVALID
                 else mode6 in Ret (mode7).

  Definition arch_mm_stage2_attrs_to_mode_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong attrs)] =>
      res <- arch_mm_stage2_attrs_to_mode_spec (Int64.unsigned attrs);;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "arch_mm_stage2_attrs_to_mode: wrong arguments"
    end
  .    

  
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
    | _ => triggerNB "arch_mm_stage1_max_level: wrong arguments"
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
    Ret (Z_MM_S2_MAX_LEVEL).

  Definition  arch_mm_stage2_max_level_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      res <- arch_mm_stage2_max_level_spec ;;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "arch_mm_stage2_max_level: wrong arguments"
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
    | _ => triggerNB "arch_mm_stage1_root_table_count: wrong arguments"
    end
  .  
  
(*  
uint8_t arch_mm_stage2_root_table_count(void)
{
	return mm_s2_root_table_count;
}
 *)

  Definition arch_mm_stage2_root_table_count_spec  : itree ArchMME (Z) :=
    Ret (Z_MM_S2_ROOT_TABLE_COUNT).

  Definition arch_mm_stage2_root_table_count_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      res <- arch_mm_stage2_root_table_count_spec ;;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "arch_mm_stage2_root_table_count: wrong arguments"
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
    let block_attrs1 := if zeq 0 (Z.land table_attrs (zshift_or_0 true Z_TABLE_NSTABLE))
                        then block_attrs
                        else Z.lor block_attrs (zshift_or_0 true Z_STAGE1_NS) in
    let block_attrs2 := if zeq 0 (Z.land table_attrs (zshift_or_0 true Z_TABLE_APTABLE1))
                        then block_attrs1
                        else Z.lor block_attrs1 (zshift_or_0 true Z_STAGE1_AP2) in
    let block_attrs3 := if zeq 0 (Z.land table_attrs (zshift_or_0 true Z_TABLE_APTABLE0))
                        then block_attrs2
                        else Z.land block_attrs2 (Z_not (zshift_or_0 true Z_STAGE1_AP1)) in
    let block_attrs4 := if zeq 0 (Z.land table_attrs (zshift_or_0 true Z_TABLE_XNTABLE))
                        then block_attrs3
                        else Z.lor block_attrs3 (zshift_or_0 true Z_STAGE1_XN) in
    let block_attrs5 := if zeq 0 (Z.land table_attrs (zshift_or_0 true Z_TABLE_PXNTABLE))
                        then block_attrs4
                        else Z.lor block_attrs4 (zshift_or_0 true Z_STAGE1_PXN) in
    Ret (block_attrs5).

  Definition arch_mm_combine_table_entry_attrs_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong table_attrs); Vcomp (Vlong block_attrs)] =>
      res <- arch_mm_combine_table_entry_attrs_spec (Int64.unsigned table_attrs) (Int64.unsigned block_attrs);;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "arch_mm_combine_table_entry_attrs_call: wrong arguments"
    end
  .
  
  Definition arch_mm_set_stage1_spec : itree ArchMME unit :=
    st <- trigger GetState;;
    trigger (SetState (st {stage: STAGE1})).
  
  Definition arch_mm_set_stage1_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [] =>
      arch_mm_set_stage1_spec;;
      Ret (Vnull, args)
    | _ => triggerUB "arch_mm_set_stage1_call: wrong arguments"
    end
  .
  
  Definition arch_mm_set_stage2_spec : itree ArchMME unit :=
    st <- trigger GetState;;
    trigger (SetState (st {stage: STAGE2})).
  
 
  Definition arch_mm_set_stage2_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with 
    | [] =>
      arch_mm_set_stage2_spec;;
      Ret (Vnull, args)
    | _ => triggerUB "arch_mm_set_stage1_call: wrong arguments"
    end
  .


  Definition arch_mm_empty_call (args: list Lang.val): itree ArchMME (Lang.val * list Lang.val) :=
    Ret (Vnull, args).


  (* arch mm pretty printer *) 

  Definition BLOCK_SHAREABLE_to_string (value: BLOCK_SHAREABLE) :=
    match value with
    | NON_SHAREABLE => "non_shareable" 
    | OUTER_SHAREABLE => "outer_shareable"
    | INNER_SHAREABLE => "inner_shareable"
    end.

  Definition STAGE1_BLOCK_PERM_to_string (value: STAGE1_BLOCK_PERM) :=
    match value with
    | STAGE1_READONLY => "readonly"
    | STAGE1_READWRITE => "readwrite"
    end.

  Definition STAGE1_BLOCK_TYPE_to_string (value: STAGE1_BLOCK_TYPE) :=
    match value with 
    | STAGE1_DEVICEINDX => "device"
    | STAGE1_NORMALINDX => "normal"
    end.

  Definition STAGE2_BLOCK_EXECUTE_MODE_to_string (value: STAGE2_BLOCK_EXECUTE_MODE) :=
    match value with 
    | STAGE2_EXECUTE_ALL => "all"
    | STAGE2_EXECUTE_EL0 => "el0"
    | STAGE2_EXECUTE_NONE => "none"
    | STAGE2_EXECUTE_EL1 => "el1"
    end.

  Definition STAGE2_BLOCK_PERM_to_string (value: STAGE2_BLOCK_PERM) :=
    match value with
    | STAGE2_ACCESS_NOPERM => "noperm"
    | STAGE2_ACCESS_READ => "read"
    | STAGE2_ACCESS_WRITE => "write"
    | STAGE2_ACCESS_READWRITE => "readwrite"
    end.
  
  Definition STAGE2_MEMATTR_MEM_TYPE_to_string (value: MMATTR_STAGE2_MEM_TYPE) :=
    match value with
    | STAGE2_DEVICE_MEMORY => "device memory"
    | STAGE2_NONCACHEABLE => "non cacheable"
    | STAGE2_WRITETHROUGH => "writethrough"
    | STAGE2_WRITEBACK => "writeback"
    end.

  Definition STAGE2_MEMATTR_DEVICE_MEM_TYPE_to_string (value: MMATTR_STAGE2_DEVICE_MEMORY_TYPE) :=
    match value with
    | STAGE2_DEVICE_nGnRnE => "nGnRnE"
    | STAGE2_DEVICE_nGnRE => "nGnRE"
    | STAGE2_DEVICE_nGRE => "nGRE"
    | STAGE2_DEVICE_GRE => "GRE"
    end.

  Definition Stage1BlockAttributes_to_string (attributes: Stage1BlockAttributes) :=
    match attributes with
    | mkStage1BlockAttributes xn pxn contiguous dbm ng af sh ap ns attrindx =>
      appends_all [string_indent;
                  "attributes: ";
                  "[xn: "; bool_to_string xn; "] ";
                  "[pxn: "; bool_to_string pxn; "] ";
                  "[contiguous: "; bool_to_string contiguous; "] ";
                  "[dbm: "; bool_to_string dbm; "] ";
                  "[ng: "; bool_to_string ng; "] ";
                  "[af: "; bool_to_string af; "] ";
                  "[sh: "; BLOCK_SHAREABLE_to_string sh; "] ";
                  "[ap: "; STAGE1_BLOCK_PERM_to_string ap; "] ";
                  "[ns: "; bool_to_string ns; "] ";
                  "[attrindx: "; STAGE1_BLOCK_TYPE_to_string attrindx; "] "]
    end.

  Definition Stage1TableAttributes_to_string (attributes: Stage1TableAttributes) :=
    match attributes with
    | mkStage1TableAttributes ns ap1 ap0 xn pxn =>
      appends_all [string_indent;
                  "attributes: ";
                  "[ns: "; bool_to_string ns; "] ";
                  "[ap1: "; bool_to_string ap1; "] ";
                  "[ap0: "; bool_to_string ap0; "] ";
                  "[xn: "; bool_to_string xn; "] ";
                  "[pxn: "; bool_to_string pxn; "] "]
    end.


  Definition STAGE2_MEMATTR_VALUE_to_string (attributes: STAGE2_MEMATTR_VALUE) :=
    match attributes with
    | STAGE2_MEM_ATTR_GEN outer inner =>
      match outer, inner with
      | MEMATTR_STAGE2_OUTER_ATTR_UNINITIALIZED, MMATTR_STAGE2_INNER_ATTR_UNINITIALIZED => "Uninitialized" 
      | _, MMATTR_STAGE2_INNER_ATTR_UNINITIALIZED => "wrong uninitialized version" 
      | MEMATTR_STAGE2_OUTER_ATTR_UNINITIALIZED, _ => "wrong uninitialized version" 
      | OUTER_MEM_TYPE_ATTR outer_mem_type, INNER_MEM_TYPE_ATTR inner_mem_type =>
        appends_all [STAGE2_MEMATTR_MEM_TYPE_to_string outer_mem_type; " "; STAGE2_MEMATTR_MEM_TYPE_to_string inner_mem_type]
      | OUTER_MEM_TYPE_ATTR outer_mem_type,  INNER_DEVICE_MEM_TYPE_ATTR  inner_mem_type =>
        appends_all [STAGE2_MEMATTR_MEM_TYPE_to_string outer_mem_type; " "; STAGE2_MEMATTR_DEVICE_MEM_TYPE_to_string inner_mem_type]
      end
    end.
  
  Definition Stage2BlockAttributes_to_string (attributes: Stage2BlockAttributes) :=
    match attributes with
    | mkStage2BlockAttributes xn contiguous dbm sw_owned sw_exclusive af sh s2ap memattr =>
      appends_all [string_indent;
                  "attributes: ";
                  "[xn : "; STAGE2_BLOCK_EXECUTE_MODE_to_string xn;"] ";
                  "[contiguous: "; bool_to_string contiguous;"] ";
                  "[dbm : "; bool_to_string dbm;"] ";
                  "[sw_owned : "; bool_to_string sw_owned;"] ";
                  "[sw_exclusive : "; bool_to_string sw_exclusive;"] ";
                  "[af : "; bool_to_string af;"] ";
                  "[sh : "; BLOCK_SHAREABLE_to_string sh;"] ";
                  "[s2ap : "; STAGE2_BLOCK_PERM_to_string s2ap;"] ";
                  "[memattr : "; STAGE2_MEMATTR_VALUE_to_string memattr ;"] "]
    end.


  
  Definition arch_mm_print_arch_mm_call (args: list Lang.val): itree ArchMME (Lang.val * list Lang.val) :=
    st <- trigger GetState;;
    match st.(stage) with
    | STAGE1 => 
      triggerSyscall "hd" ("current_stage: STAGE1 ") [Vnull]            
    | STAGE2 =>
      triggerSyscall "hd" ("current_stage: STAGE2 ") [Vnull]
    end ;;
    match args with
    | [Vcomp (Vlong value) ; Vcomp (Vlong level)] =>
      match VALUES_to_PTE_TYPES (Int64.unsigned level) st.(stage) (Int64.unsigned value) with      
      | Some pte =>
        match pte with
          | UNDEFINED =>
            triggerSyscall "hd" ("[Undefined]") [Vnull]                         
          | ABSENT =>
            triggerSyscall "hd" (appends_all [string_indent;
                                             "[ABSENT]"]) [Vnull]
                           (*
          | STAGE1_INVALID_BLOCK_LEVEL0 oa attributes  =>
            triggerSyscall "hd" (appends_all [string_indent;
                                             "[STAGE1_INVALID_BLOCK_LEVEL0: ";
                                             "[output_address: "; Z_to_string oa; "] ";
                                             "["; Stage1BlcokAttributes_to_string attributes; "] ";
                                             "[is_table: "; bool_to_string is_table; "]"]) [Vnull]
          | STAGE1_INVALID_BLOCK ba oa attributes is_table =>
            triggerSyscall "hd" (appends_all [string_indent;
                                             "[STAGE1_INVALID_BLOCK: ";
                                             "[base_address: "; Z_to_string ba; "] ";
                                             "[output_address: "; Z_to_string oa; "] ";
                                             "["; Stage1BlockAttributes_to_string attributes; "] ";
                                             "[is_table: "; bool_to_string is_table; "]"]) [Vnull]
          | STAGE1_TABLE ba oa attributes =>
            triggerSyscall "hd" (appends_all [string_indent;
                                             "[STAGE1_TABLE: ";
                                             "[base_address: "; Z_to_string ba; "] ";
                                             "[output_address: "; Z_to_string oa; "] ";
                                             "["; Stage1TableAttributes_to_string attributes; "]"]) [Vnull]
          | STAGE1_PAGE ba oa attributes =>
            triggerSyscall "hd" (appends_all [string_indent;
                                             "[STAGE1_TABLE: ";
                                             "[base_address: "; Z_to_string ba; "] ";
                                             "[output_address: "; Z_to_string oa; "] ";
                                             "["; Stage1BlockAttributes_to_string attributes; "]"]) [Vnull]
          | STAGE2_INVALID_BLOCK ba oa attributes is_table =>
            triggerSyscall "hd" (appends_all [string_indent;
                                             "[STAGE2_INVALID_BLOCK: ";
                                             "[base_address: "; Z_to_string ba; "] ";
                                             "[output_address: "; Z_to_string oa; "] ";
                                             "["; Stage2BlockAttributes_to_string attributes; "] ";
                                             "[is_table: "; bool_to_string is_table; "]"]) [Vnull]
          | STAGE2_TABLE ba oa =>
            triggerSyscall "hd" (appends_all [string_indent;
                                             "[STAGE2_TABLE: ";
                                             "[base_address: "; Z_to_string ba; "] ";
                                             "[output_address: "; Z_to_string oa; "]"]) [Vnull]
          | STAGE2_PAGE ba oa attributes =>
            triggerSyscall "hd" (appends_all [string_indent;
                                             "[STAGE1_TABLE: ";
                                             "[base_address: "; Z_to_string ba; "] ";
                                             "[output_address: "; Z_to_string oa; "] ";
                                             "["; Stage2BlockAttributes_to_string attributes; "]"]) [Vnull] *)
          | _ =>
            triggerSyscall "hd" (appends_all [string_indent;
                                             "[NOTIMPLEMENTED]"]) [Vnull]
        end
      | None =>  triggerUB "Wrong conversion: print_archmm"
      end ;;
      Ret (Vnull, args)
    | _ => triggerUB "Wrong args: print_archmm"
  end.

  
  
  (* XXX: auxiliary functions for testing *)
  Definition set_new_address (pte: PTE_TYPES) (address : Z) : option PTE_TYPES :=
    match pte with 
    | _ => None
            (*
    | ABSENT => None
    | STAGE1_INVALID_BLOCK oa attributes is_table
                 
    | STAGE1_INVALID_BLOCK oa attributes is_table
      =>  (STAGE1_INVALID_BLOCK ba address attributes is_table)
      =>  if zeq oa 0
         then Some (STAGE1_INVALID_BLOCK ba address attributes is_table)
         else None
    | STAGE1_TABLE ba oa attributes
      =>  if zeq oa 0
         then Some (STAGE1_TABLE ba address attributes)
         else None
    | STAGE1_PAGE ba oa attributes
      =>  if zeq oa 0
         then Some (STAGE1_PAGE ba address attributes)
         else None
    | STAGE2_INVALID_BLOCK ba oa attributes is_table
      =>  if zeq oa 0
         then Some (STAGE2_INVALID_BLOCK ba address attributes is_table)
         else None
    | STAGE2_TABLE ba oa
      =>  if zeq oa 0
         then Some (STAGE2_TABLE ba address)
         else None
    | STAGE2_PAGE ba oa attributes 
      =>  if zeq oa 0
         then Some (STAGE2_PAGE ba address attributes)
         else None *)
    end.
    
  Definition arch_mm_set_pte_addr_spec (pte : Z) (address : Z) :  itree ArchMME (unit)  :=
    st <- trigger GetState;;
    triggerUB "arch_mm_set_pte_addr_spec: not_implemented".

  Definition arch_mm_set_pte_addr_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong pte); Vcomp (Vlong address)] =>
      arch_mm_set_pte_addr_spec  (Int64.unsigned pte) (Int64.unsigned address);;
      Ret (Vnull, args)
    | _ => triggerNB "arch_mm_combine_table_entry_addr_call: wrong arguments"
    end
  .

  (* XXX: auxiliary functions for testing *)
  Definition set_new_attributes (pte: PTE_TYPES) (attributes : Z) : option PTE_TYPES :=
    (*
    match pte with 
    | UNDEFINED
    | ABSENT _ => None
    | STAGE1_INVALID_BLOCK ba oa _ is_table =>
      match ATTR_VALUES_to_Stage1BlockAttributes attributes with
      | Some attrs => Some (STAGE1_INVALID_BLOCK ba oa attrs is_table)
      | None  => None
      end
    | STAGE1_TABLE ba oa _ =>
      Some (STAGE1_TABLE ba oa (ATTR_VALUES_to_Stage1TableAttributes attributes))
    | STAGE1_PAGE ba oa _ =>
      match ATTR_VALUES_to_Stage1BlockAttributes attributes with
      | Some attrs => Some (STAGE1_PAGE ba oa attrs)
      | None => None
      end
    | STAGE2_INVALID_BLOCK ba oa _ is_table =>
      match ATTR_VALUES_to_Stage2BlockAttributes attributes with
      | Some attrs => Some (STAGE2_INVALID_BLOCK ba oa attrs is_table)
      | None => None
      end
    | STAGE2_TABLE ba oa
      => Some (STAGE2_TABLE ba oa)
    | STAGE2_PAGE ba oa _ =>
      match ATTR_VALUES_to_Stage2BlockAttributes attributes with
      | Some attrs => Some (STAGE2_PAGE ba oa attrs)
      | None => None
      end 
    end. *)
    None.
      
  Definition arch_mm_set_pte_attrs_spec (pte : Z) (attrs : Z) :  itree ArchMME (unit)  :=
    st <- trigger GetState;;
    triggerUB "arch_mm_set_pte_attrs_spec: not implemented".
  (*
    match (PtrTree_get ((fst pte), ((snd pte))) st.(addr_to_id)) with
    | None =>
      triggerUB "arch_mm_set_pte_attrs_spec: pte does not exist"
    | Some key =>
      match PTree.get key st.(pte_pool) with
      | Some pte =>
        do new_pte <- set_new_attributes pte attrs ;;;
        trigger (SetState (st {PTE_POOL : PTree.set key new_pte st.(pte_pool)})) ;;
        Ret (tt)
      | None => triggerUB "arch_mm_set_pte_attrs_spec: invalid case"
      end
    end. *)
  
  Definition arch_mm_set_pte_attrs_call (args: list Lang.val) : itree ArchMME (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong pte); Vcomp (Vlong attrs)] =>
      arch_mm_set_pte_attrs_spec  (Int64.unsigned pte) (Int64.unsigned attrs);;
      Ret (Vnull, args)
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
    ("ARCHMM.arch_mm_invalidate_stage1_range", arch_mm_invalidate_stage1_range_call) ;
    ("ARCHMM.arch_mm_invalidate_stage2_range", arch_mm_invalidate_stage2_range_call) ;
    ("ARCHMM.arch_mm_mode_to_stage1_attrs", arch_mm_mode_to_stage1_attrs_call) ;
    ("ARCHMM.arch_mm_mode_to_stage2_attrs",  arch_mm_mode_to_stage2_attrs_call) ;
    ("ARCHMM.arch_mm_stage2_attrs_to_mode",  arch_mm_stage2_attrs_to_mode_call) ;
    ("ARCHMM.arch_mm_stage1_max_level", arch_mm_stage1_max_level_call) ;
    ("ARCHMM.arch_mm_stage2_max_level", arch_mm_stage2_max_level_call) ;
    ("ARCHMM.arch_mm_stage1_root_table_count", arch_mm_stage1_root_table_count_call) ;
    ("ARCHMM.arch_mm_stage2_root_table_count", arch_mm_stage2_root_table_count_call) ;
    ("ARCHMM.arch_mm_combine_table_entry_attrs", arch_mm_combine_table_entry_attrs_call) ;
    ("ARCHMM.arch_mm_set_stage1", arch_mm_set_stage1_call) ;
    ("ARCHMM.arch_mm_set_stage2", arch_mm_set_stage2_call) ;
    ("ARCHMM.arch_mm_empty_call", arch_mm_empty_call) ;
    ("ARCHMM.arch_mm_print_archmm_call", arch_mm_print_arch_mm_call) ;
    ("ARCHMM.arch_mm_set_pte_addr", arch_mm_set_pte_addr_call) ;
    ("ARCHMM.arch_mm_set_pte_attr", arch_mm_set_pte_attrs_call)
    ].

  Definition arch_mm_modsem : ModSem :=
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
  
End ArchMMHighSpec.
