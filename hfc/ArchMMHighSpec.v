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


(* Memory attributes (
#define NON_SHAREABLE   UINT64_C(0)
#define OUTER_SHAREABLE UINT64_C(2)
#define INNER_SHAREABLE UINT64_C(3)

#define PTE_VALID        (UINT64_C(1) << 0)
#define PTE_LEVEL0_BLOCK (UINT64_C(1) << 1)
#define PTE_TABLE        (UINT64_C(1) << 1)

#define STAGE1_XN          (UINT64_C() << 54)
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

#define STAGE1_READONLY  UINT64_C(2)
#define STAGE1_READWRITE UINT64_C(0)

#define STAGE1_DEVICEINDX UINT64_C(0)
#define STAGE1_NORMALINDX UINT64_C(1)

#define STAGE2_XN(x)      ((x) << 53)
#define STAGE2_CONTIGUOUS (UINT64_C(1) << 52)
#define STAGE2_DBM        (UINT64_C(1) << 51)
#define STAGE2_AF         (UINT64_C(1) << 10)
#define STAGE2_SH(x)      ((x) << 8)
#define STAGE2_S2AP(x)    ((x) << 6)

#define STAGE2_EXECUTE_ALL  UINT64_C(0)
#define STAGE2_EXECUTE_EL0  UINT64_C(1)
#define STAGE2_EXECUTE_NONE UINT64_C(2)
#define STAGE2_EXECUTE_EL1  UINT64_C(3)
#define STAGE2_EXECUTE_MASK UINT64_C(3)

/* Table attributes only apply to stage 1 translations. */
#define TABLE_NSTABLE  (UINT64_C(1) << 63)
#define TABLE_APTABLE1 (UINT64_C(1) << 62)
#define TABLE_APTABLE0 (UINT64_C(1) << 61)
#define TABLE_XNTABLE  (UINT64_C(1) << 60)
#define TABLE_PXNTABLE (UINT64_C(1) << 59)

/* The following are stage-2 software defined attributes. */
#define STAGE2_SW_OWNED     (UINT64_C(1) << 55)
#define STAGE2_SW_EXCLUSIVE (UINT64_C(1) << 56)

/* The following are stage-2 memory attributes for normal memory. */
#define STAGE2_DEVICE_MEMORY UINT64_C(0)
#define STAGE2_NONCACHEABLE  UINT64_C(1)
#define STAGE2_WRITETHROUGH  UINT64_C(2)
#define STAGE2_WRITEBACK     UINT64_C(3)

/* The following are stage-2 memory attributes for device memory. */
#define STAGE2_MEMATTR_DEVICE_nGnRnE UINT64_C(0)
#define STAGE2_MEMATTR_DEVICE_nGnRE  UINT64_C(1)
#define STAGE2_MEMATTR_DEVICE_nGRE   UINT64_C(2)
#define STAGE2_MEMATTR_DEVICE_GRE    UINT64_C(3)

/* The following construct and destruct stage-2 memory attributes. */
#define STAGE2_MEMATTR(outer, inner) ((((outer) << 2) | (inner)) << 2)
#define STAGE2_MEMATTR_TYPE_MASK UINT64_C(3 << 4)

#define STAGE2_ACCESS_READ  UINT64_C(1)
#define STAGE2_ACCESS_WRITE UINT64_C(2)

#define CACHE_WORD_SIZE 4
*)


(* There are other attributes defined in the mm.h file. We are not currently sure that 
   whether they have some redundant features with the following ones, and whether 
   they have to be modeled in here (or the place that we model MM. Those attributes are 
   as follows *)
(* 
#define PAGE_SIZE (1 << PAGE_BITS)
#define MM_PTE_PER_PAGE (PAGE_SIZE / sizeof(pte_t))

/* The following are arch-independent page mapping modes. */
#define MM_MODE_R UINT32_C(0x0001) /* read */
#define MM_MODE_W UINT32_C(0x0002) /* write */
#define MM_MODE_X UINT32_C(0x0004) /* execute */
#define MM_MODE_D UINT32_C(0x0008) /* device */

/*
 * Memory in stage-1 is either valid (present) or invalid (absent).
 *
 * Memory in stage-2 has more states to track sharing, borrowing and giving of
 * memory. The states are made up of three parts:
 *
 *  1. V = valid/invalid    : Whether the memory is part of the VM's address
 *                            space. A fault will be generated if accessed when
 *                            invalid.
 *  2. O = owned/unowned    : Whether the memory is owned by the VM.
 *  3. X = exclusive/shared : Whether access is exclusive to the VM or shared
 *                            with at most one other.
 *
 * These parts compose to form the following state:
 *
 *  -  V  O  X : Owner of memory with exclusive access.
 *  -  V  O !X : Owner of memory with access shared with at most one other VM.
 *  -  V !O  X : Borrower of memory with exclusive access.
 *  -  V !O !X : Borrower of memory where access is shared with the owner.
 *  - !V  O  X : Owner of memory lent to a VM that has exclusive access.
 *
 *  - !V  O !X : Unused. Owner of shared memory always has access.
 *  - !V !O  X : Unused. Next entry is used for invalid memory.
 *
 *  - !V !O !X : Invalid memory. Memory is unrelated to the VM.
 *
 *  Modes are selected so that owner of exclusive memory is the default.
 */
#define MM_MODE_INVALID UINT32_C(0x0010)
#define MM_MODE_UNOWNED UINT32_C(0x0020)
#define MM_MODE_SHARED  UINT32_C(0x0040)

/* The mask for a mode that is considered unmapped. */
#define MM_MODE_UNMAPPED_MASK (MM_MODE_INVALID | MM_MODE_UNOWNED)

#define MM_FLAG_COMMIT  0x01
#define MM_FLAG_UNMAP   0x02
#define MM_FLAG_STAGE1  0x04
*)

Section ABSTSTATE.


(* Memory value for each table entry *)
Variable A: Type.

(* possible attributes in the low level *)
(** 
TODO: 
1. Some attributes are overlapped with others, so we do not need them 
2. Categorized the attribute as threes 
   1) only for stage1 
   2) only for stage2
   3) both 
   We can do fine-grained categories (e.g., device / normal) 
3. Some are omitted to the higher level specifications. We need to provide the document about it 
*)
Inductive MMATTTR_SHAREABLE :=
| NON_SHAREABLE | OUTER_SHAREABLE | INNER_SHAREABLE.


Inductive MMATTR_PTE_VALID := 
| PTE_VALID | PTE_INVALID.


(* They are same values *)
Inductive MMATTR_PTE_TABLE :=
| PTE_TABLE | PTE_IS_NOT_TABLE.
Inductive MMATTR_PTE_LEVEL0_BLOCK :=
| PTE_LEVEL0_BLOCK | PTE_LEVEL0_NOT_BLOCK.

Inductive MMATTR_STAGE1_ATTR_FLAGS :=
| STAGE1_XN (x : Z)
| STAGE1_PXN
| STAGE1_CONTIGUOUS
| STAGE1_DBM
| STAGE1_NG
| STAGE1_AF
| STAGE1_SH (x : Z)
| STAGE1_AP2
| STAGE1_AP1
| STAGE1_AP (x : Z)
| STAGE1_NS
| STAGE1_ATTRINDX (x : Z).

Inductive MMATTR_STAGE1_READWRITEPERM :=
| STAGE1_READONLY | STAGE1_READWRITE.

Inductive MMATTR_STAGE1_INDX :=
| STAGE1_DEVICEINDX | STAGE1_NORMALINDX.

Inductive MMATTR_STAGE2_ATTR_FLAGS :=
| STAGE2_XN (x : Z)
| STAGE2_CONTIGUOUS
| STAGE2_DBM
| STAGE2_AF
| STAGE2_SH (x : Z)
| STAGE2_S2AP (x : Z).

Inductive MMATTR_STAGE2_EXECUTE_ATTR_FLAGS :=
| STAGE2_EXECUTE_ALL
| STAGE2_EXECUTE_EL0
| STAGE2_EXECUTE_NONE
| STAGE2_EXECUTE_EL1
| STAGE2_EXECUTE_MASK.

(* Table attributes only apply to stage 1 translations. *)
Inductive MMATTR_STAGE1_TABLE_ATTR_FLAGS :=
| TABLE_NSTABLE
| TABLE_APTABLE1
| TABLE_APTABLE2
| TABLE_XNTABLE
| TABLE_PXNTABLE.

(* The following are stage-2 software defined attributes *)
Inductive MMATTR_STAGE2_ONWERSHIP_FLAGS :=
| STAGE2_SW_OWNED
| STAGE2_SW_EXCLUSIVE.

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

(* The following construct and destruct stage-2 memory attributes. *)
Inductive MMATTR_STAGE2_MEMORY_ATTR :=
| STAGE2_MEMATTR (outer : Z) (inner : Z)
| STAGE2_MEMATTR_TYPE_MASK.

Inductive MMATTR_STAGE2_READWRITEPERM :=
| STAGE2_ACCESS_READ | STAGE2_ACCESS_WRITE.



(* collecting stage1 specific attr *)
Record MM_STAGE1_ATTR_COLLECT :=
  mkMMStage1AttrCollect {
      mm_attr_stage1_attr_flags: MMATTR_STAGE1_ATTR_FLAGS;
      mm_attr_stage1_read_write_perm: MMATTR_STAGE1_READWRITEPERM;
      mm_attr_stage1_indx : MMATTR_STAGE1_INDX;
      mm_attr_stage1_table_attr_flags: MMATTR_STAGE1_TABLE_ATTR_FLAGS;
    }.

(* collecting stage2 specific attr *)
Record MM_STAGE2_ATTR_COLLECT :=
  mkMMStage2AttrCollect {
      mm_attr_stage2_attr_flags: MMATTR_STAGE2_ATTR_FLAGS;
      mm_attr_stage2_execute_attr_flags: MMATTR_STAGE2_EXECUTE_ATTR_FLAGS;
      mm_attr_stage2_ownership_flags: MMATTR_STAGE2_ONWERSHIP_FLAGS;
      mm_attr_stage2_normal_memory_attr:  MMATTR_STAGE2_NORMAL_MEMORY_ATTR;
      mm_attr_stage2_device_memory_attr: MMATTR_STAGE2_DEVICE_MEMORY_ATTR;
      mm_attr_stage2_memory_attr: MMATTR_STAGE2_MEMORY_ATTR;
      mm_attr_stage2_read_writer_prem: MMATTR_STAGE2_READWRITEPERM;
    }.

(* collecting stage2 specific attr *)
Record MM_COMMON_ATTR_COLLECT :=
  mkMMCOMMONAttrCollect {
      mm_attr_sharable: MMATTTR_SHAREABLE;
      mm_attr_pte_valid: MMATTR_PTE_VALID;
      mm_attr_pte_table: MMATTR_PTE_TABLE;
      mm_attr_pte_level0_block: MMATTR_PTE_LEVEL0_BLOCK
    }.

Inductive MM_ATTR_COLLECT :=
| MM_STAGE1_ATTR_COLLECT_DEF
    (mm_common_attr_collect: MM_COMMON_ATTR_COLLECT)
    (mm_stage1_attr_collect: MM_STAGE1_ATTR_COLLECT)
| MM_STAGE2_ATTR_COLLECT_DEF
    (mm_common_attr_collect: MM_COMMON_ATTR_COLLECT)
    (mm_stage2_attr_collect: MM_STAGE2_ATTR_COLLECT).

(* obviously there are some overlaps between value and attributee. But it is ok at this stage because 
   we do not care too much about the internal details of value *)
Record PTE_VALUE :=
  mkPTEVALUE {
      value : A;
      attr: MM_ATTR_COLLECT;
    }.


Record ArchMMAbstractState :=
  mkArchMMAbstractState {
      pte_value_pool: ZMap.t PTE_VALUE;
      addr_to_pte_value_pool: ZMap.t Z
    }.
 
End ABSTSTATE.


