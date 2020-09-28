(*
 * Copyright 2020 Youngju Song/ Jieung Kim
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Structures.Foldable
     Structures.Reducible
     Data.List.

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
Require Import sflib.

Require Import ClassicalDescription.
About excluded_middle_informative.

(** From CompCert *)
Require Import AST.
Require Import Memory.
Require Import Integers.
(* Require Import Floats. *)
Require Import Values.
Require Import LangType Op.

(* From HafniumCore *)
Require Import Lang Any.
Import LangNotations.

Require Import ZArith.

Import Int64.


Set Implicit Arguments.

(* Some operations *)
(* #define UINT64_C(x)  ((x) + (UINT64_MAX - UINT64_MAX)) *)
(* #define UINT64_MAX  0xffffffffffffffff [exact] *)

(* JIEUNG (TODO): It requires check that the value is in the range. and the value is well-typed. *)
(* JIEUNG (TODO): I also hope to use quantifiers in assume and guarantee. Otherwise, I think we need 
   another method to express invariants? *) 
Definition UINT64_C (val : int64) := val.

Definition UINT32_C (val : int64) := val.

(* XXX: There are some platform related constat values in the system. which are defined in [build/BUILD.dn].
   How can we define them in our system? 
 defines = [ 
    "HEAP_PAGES=${plat_heap_pages}",
    "MAX_CPUS=${plat_max_cpus}",
    "MAX_VMS=${plat_max_vms}",
    "LOG_LEVEL=${log_level}",
  ]
 *)

(* XXX: I first set them as dummy values *)
Definition HEAP_PAGES : int64 := Int64.repr 100000.
Definition MAX_CPUS : int64 := Int64.repr 32.
Definition MAX_VMS : int64 := Int64.repr 32.
Definition LOG_LEVEL : int64 := Int64.repr 10000.

(* From the definition in [inc/vmapi/hf/types.h:#define] 
#define HF_HYPERVISOR_VM_ID 0

/**
 * An offset to use when assigning VM IDs.
 * The offset is needed because VM ID 0 is reserved.
 */
#define HF_VM_ID_OFFSET 1

/**
 * The index and ID of the primary VM, which is responsible for scheduling.
 *
 * These are not equal because ID 0 is reserved for the hypervisor itself.
 * Primary VM therefore gets ID 1 and all other VMs come after that.
 */
#define HF_PRIMARY_VM_INDEX 0
#define HF_PRIMARY_VM_ID (HF_VM_ID_OFFSET + HF_PRIMARY_VM_INDEX)
...
*)

Definition HF_VM_ID_OFFSET : int64 := one.
Definition HF_PRIMARY_VM_INDEX : int64 := zero.
Definition HF_PRIMARY_VM_ID : int64 := (Int64.add HF_VM_ID_OFFSET HF_PRIMARY_VM_INDEX).

(* From the definition in [src/arch/aarch64/inc/hf/arch/types.h] 
#define PAGE_LEVEL_BITS 9 
#define PAGE_BITS 12
#define STACK_ALIGN 16
#define FLOAT_REG_BYTES 16
#define NUM_GP_REGS 31
...
*)

Definition PAGE_LEVEL_BITS : int64 := Int64.repr 9.
Definition PAGE_BITS : int64 := Int64.repr 12.
Definition STACK_ALIGN : int64 := Int64.repr 16.
Definition FLOAT_REG_BYTES : int64 := Int64.repr 16.
Definition NUM_GP_REGS : int64 := Int64.repr 31.


(* typedef uint64_t pte_t; *)

Definition sizeof_pte_t : int64 := Int64.repr 8.

(* From the definition in [inc/hf/mm.h]
#define PAGE_SIZE (1 << PAGE_BITS)
...
*)
Definition PAGE_SIZE : int64 := (shl one PAGE_BITS).

(*
/* The following are arch-independent page mapping modes. */
#define MM_MODE_R UINT32_C(0x0001) /* read */
#define MM_MODE_W UINT32_C(0x0002) /* write */
#define MM_MODE_X UINT32_C(0x0004) /* execute */
#define MM_MODE_D UINT32_C(0x0008) /* device */
 *)
Definition MM_MODE_R : int64 := one.
Definition MM_MODE_W : int64 := Int64.repr 2. 
Definition MM_MODE_X : int64 := Int64.repr 4.
Definition MM_MODE_D : int64 := Int64.repr 8.

(*
#define MM_PTE_PER_PAGE (PAGE_SIZE / sizeof(pte_t))
*)

Definition MM_PTE_PER_PAGE : int64 := (divu PAGE_SIZE sizeof_pte_t). (* 512 *)
 
(* From the definition in [inc/hf/mm.h]
#define MM_MODE_INVALID UINT32_C(0x0010)
#define MM_MODE_UNOWNED UINT32_C(0x0020)
#define MM_MODE_SHARED  UINT32_C(0x0040)

(* #define MM_MODE_UNMAPPED_MASK (MM_MODE_INVALID | MM_MODE_UNOWNED) *)
 
#define MM_FLAG_COMMIT  0x01
#define MM_FLAG_UNMAP   0x02
#define MM_FLAG_STAGE1  0x04

*)

(* JIEUNG: FIXED -- coercion is not working very well in here. We need to fix that *)

(* Constants for ArchMM *)
Definition MM_MODE_UNOWNED : int64 := UINT32_C (repr 16).
Definition MM_MODE_INVALID : int64 := UINT32_C (repr 32).
Definition MM_MODE_SHARED : int64 := UINT32_C (repr 64).

Definition MM_MODE_UNMAPPED_MASK : int64 := repr 48.


Definition MM_FLAG_COMMIT : int64 := Int64.repr 1.
Definition MM_FLAG_UNMAP : int64 := Int64.repr 2.
Definition MM_FLAG_STAGE1 : int64 := Int64.repr 4.


  Definition UINT64_C_1 := UINT64_C (repr 1).

  Definition PTE_ADDR_MASK :=
    (BAnd (Minus (ShiftL UINT64_C_1 (repr 48)) (repr 1)) (BNot (Minus (ShiftL UINT64_C_1 PAGE_BITS) (repr 1)))).
  Definition PTE_ATTR_MASK :=
    (BNot (BOr PTE_ADDR_MASK (ShiftL UINT64_C_1 (repr 1)))). 

  Definition MAX_TLBI_OPS := MM_PTE_PER_PAGE.

  Definition CACHE_WORD_SIZE :expr := (repr 4).
  Definition UINT16_C (val : Z) := val.
  Definition UINT16_C_1 := UINT16_C 1.

  Definition NON_SHAREABLE := UINT64_C (repr 0).
  Definition OUTER_SHAREABLE := UINT64_C (repr 2).
  Definition INNER_SHAREABLE := UINT64_C (repr 3).

  Definition PTE_VALID := ShiftL UINT64_C_1 (repr 0).
  Definition PTE_LEVEL0_BLOCK := ShiftL UINT64_C_1 (repr 1).
  Definition PTE_TABLE := ShiftL UINT64_C_1 (repr 1).

  Definition STAGE2_SW_OWNED := ShiftL UINT64_C_1 (repr 55).
  Definition STAGE2_SW_EXCLUSIVE := ShiftL UINT64_C_1 (repr 56).

  Definition STAGE1_XN := ShiftL UINT64_C_1 (repr 54).
  Definition STAGE1_PXN := ShiftL UINT64_C_1 (repr 53).
  Definition STAGE1_CONTIGUOUS := ShiftL UINT64_C_1 (repr 52).
  Definition STAGE1_DBM := ShiftL UINT64_C_1 (repr 51).
  Definition STAGE1_NG := ShiftL UINT64_C_1 (repr 11).
  Definition STAGE1_AF := ShiftL UINT64_C_1 (repr 10).
  Definition STAGE1_SH := fun x => ShiftL x (repr 8).
  Definition STAGE1_AP2 := ShiftL UINT64_C_1 (repr 7).
  Definition STAGE1_AP1 := ShiftL UINT64_C_1 (repr 6).
  Definition STAGE1_AP := fun x => ShiftL x (repr 6).
  Definition STAGE1_NS := ShiftL UINT64_C_1 (repr 5).
  Definition STAGE1_ATTRINDX := fun x => ShiftL x (repr 2).

  Definition STAGE1_READONLY := UINT64_C (repr 2).
  Definition STAGE1_READWRITE := UINT64_C (repr 0).

  Definition STAGE1_DEVICEINDX := UINT64_C (repr 0).
  Definition STAGE1_NORMALINDX := UINT64_C (repr 1).

  Definition STAGE2_XN := fun x => ShiftL x (repr 53).
  Definition STAGE2_CONTIGUOUS := ShiftL UINT64_C_1 (repr 52).
  Definition STAGE2_DBM := ShiftL UINT64_C_1 (repr 51).
  Definition STAGE2_AF := ShiftL UINT64_C_1 (repr 10).
  Definition STAGE2_SH := fun x => ShiftL x (repr 8).
  Definition STAGE2_S2AP := fun x => ShiftL x (repr 6).

  Definition STAGE2_EXECUTE_ALL := UINT64_C (repr 0).
  Definition STAGE2_EXECUTE_EL0 := UINT64_C (repr 1).
  Definition STAGE2_EXECUTE_NONE := UINT64_C (repr 2).
  Definition STAGE2_EXECUTE_EL1 := UINT64_C (repr 3).
  Definition STAGE2_EXECUTE_MASK := UINT64_C (repr 3).

  Definition STAGE2_ACCESS_READ := UINT64_C (repr 1).
  Definition STAGE2_ACCESS_WRITE := UINT64_C (repr 2).

  Definition STAGE2_DEVICE_MEMORY := UINT64_C (repr 0).
  Definition STAGE2_NONCACHEABLE := UINT64_C (repr 1).
  Definition STAGE2_WRITETHROUGH := UINT64_C (repr 2).
  Definition STAGE2_WRITEBACK := UINT64_C (repr 3).

  Definition STAGE2_MEMATTR_DEVICE_nGnRnE := UINT64_C (repr 0).
  Definition STAGE2_MEMATTR_DEVICE_nGnRE := UINT64_C (repr 1).
  Definition STAGE2_MEMATTR_DEVICE_nGRE := UINT64_C (repr 2).
  Definition STAGE2_MEMATTR_DEVICE_GRE := UINT64_C (repr 3).

  Definition STAGE2_MEMATTR (outer inner: expr) := (Or (ShiftL outer (repr 2)) (ShiftL inner (repr 2))).
  Definition STAGE2_MEMATTR_TYPE_MASK := UINT64_C (repr (Z.shiftl 3 4)).

  Definition TABLE_NSTABLE := ShiftL UINT64_C_1 (repr 63).
  Definition TABLE_APTABLE1 := ShiftL UINT64_C_1 (repr 62).
  Definition TABLE_APTABLE0 := ShiftL UINT64_C_1 (repr 61).
  Definition TABLE_XNTABLE := ShiftL UINT64_C_1 (repr 60).
  Definition TABLE_PXNTABLE := ShiftL UINT64_C_1 (repr 59).


(* XXX: I manually calculate the result. I may need some way? *)





