(*
 * Copyright 2020 Jieung Kim (jieungkim@google.com)
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

(* begin hide *)

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

Import Monads.
Import MonadNotation.

Local Open Scope monad_scope.

Require Import Decision.

Require Import Coqlib sflib.

Require Import Maps.
Set Implicit Arguments.


(** linux-pkvm-verif/arch/arm64/include/asm/kvm_pgtable.h *)
(* typedef u64 kvm_pte_t; *)
Definition kvm_pte_t := Z.

(*
// the logical entry kinds
enum entry_kind {
	EK_INVALID,
	EK_BLOCK,
	EK_TABLE,
	EK_PAGE_DESCRIPTOR,  
	EK_BLOCK_NOT_PERMITTED,
	EK_RESERVED,
	EK_DUMMY
};

// the entry kind bit representations
#define ENTRY_INVALID_0 0
#define ENTRY_INVALID_2 2
#define ENTRY_BLOCK 1
#define ENTRY_RESERVED 1
#define ENTRY_PAGE_DESCRIPTOR 3
#define ENTRY_TABLE 3
*)

Inductive entry_kind :=
| EK_INVALID
| EK_BLOCK
| EK_TABLE
| EK_PAGE_DESCRIPTOR
| EK_BLOCK_NOT_PERMITTED
| EK_RESERVED
| EK_DUMMY.

Notation EK_INVALID_of_Z := 0.
Notation EK_BLOCK_of_Z := 1.
Notation EK_TABLE_of_Z := 2.
Notation EK_PAGE_DESCRIPTOR_of_Z := 3.  
Notation EK_BLOCK_NOT_PERMITTED_of_Z := 4.
Notation EK_RESERVED_of_Z := 5.
Notation EK_DUMMY_of_Z := 6.

Notation ENTRY_INVALID_0 := 0.
Notation ENTRY_INVALID_2 := 2.
Notation ENTRY_BLOCK := 1.
Notation ENTRY_RESERVED := 1.
Notation ENTRY_PAGE_DESCRIPTOR := 3.
Notation ENTRY_TABLE := 3.

(*
#ifdef __SIZEOF_LONG__
#define BITS_PER_LONG (__CHAR_BIT__ * __SIZEOF_LONG__)
#else
#define BITS_PER_LONG __WORDSIZE
#endif
*)

(*
#define __GENMASK(h, l) \
	(((~UL(0)) - (UL(1) << (l)) + 1) & \
	 (~UL(0) >> (BITS_PER_LONG - 1 - (h))))
#define GENMASK(h, l) \
	(GENMASK_INPUT_CHECK(h, l) + __GENMASK(h, l))
 *)


(*  64 bits *)
Definition __CHAR_BIT__ := 8.
Definition __SIZEOF_LONG__ := 8.

Definition BITS_PER_LONG := __CHAR_BIT__ * __SIZEOF_LONG__.

Definition Z_LONG_MAX := ((Z.pow 2 BITS_PER_LONG) - 1)%Z.
Definition Z_LONG_NOT := fun val => (Z.lxor Z_LONG_MAX val).

Definition GENMASK (h l : Z) :=
  Z.land ((Z_LONG_NOT 0) - (Z.shiftl 1 l) + 1)
         (Z.shiftr (Z_LONG_NOT 0) (BITS_PER_LONG - 1 - h)).

(* 
// compute the entry_kind of a page-table entry
enum entry_kind entry_kind(kvm_pte_t pte, u8 level)
{
	switch(level) {
	case 0:
	case 1:
	case 2:
	{
		switch (pte & GENMASK(1,0)) {
		case ENTRY_INVALID_0:
		case ENTRY_INVALID_2:
			return EK_INVALID;
		case ENTRY_BLOCK:
			switch (level)
			{
			case 0:
				return EK_BLOCK_NOT_PERMITTED;
			case 1:
			case 2:
				return EK_BLOCK;
			}
		case ENTRY_TABLE:
			return EK_TABLE;
		default:
			return EK_DUMMY; // just to tell the compiler that the cases are exhaustive
		}
	}
	case 3:
		switch (pte & GENMASK(1,0)) {
		case ENTRY_INVALID_0:
		case ENTRY_INVALID_2:
			return EK_INVALID;
		case ENTRY_RESERVED:
			return EK_RESERVED;
		case ENTRY_PAGE_DESCRIPTOR:
			return EK_PAGE_DESCRIPTOR;
		}

	default:
		return EK_DUMMY; // just to tell the compiler that the cases are exhaustive
	}
}
 *)

Definition  get_entry_kind (pte: kvm_pte_t) (level: Z) : entry_kind :=
  (** when level = 0 *)
  if decide (level = 0) || decide (level = 1) || decide (level = 2)
  then 
    let pte_mask_value := Z.land pte (GENMASK 1 0) in
    if (decide (pte_mask_value = ENTRY_INVALID_0) ||
        decide (pte_mask_value = ENTRY_INVALID_2)) 
    then  EK_INVALID
    else if (decide (pte_mask_value = ENTRY_BLOCK))
         then
           if (decide (level = 0)) 
           then EK_BLOCK_NOT_PERMITTED
           else EK_BLOCK 
         else
           if (decide (pte_mask_value = ENTRY_TABLE))
           then EK_TABLE
           else EK_DUMMY
  else
    let pte_mask_value := Z.land pte (GENMASK 1 0) in
    if decide (level = 3)
    then if (decide (pte_mask_value = ENTRY_INVALID_0) ||
             decide (pte_mask_value = ENTRY_INVALID_2))
         then EK_INVALID
         else if decide (pte_mask_value = ENTRY_RESERVED)
              then EK_RESERVED
              else if decide (pte_mask_value = ENTRY_PAGE_DESCRIPTOR)
                   then EK_PAGE_DESCRIPTOR
                   else EK_DUMMY
    else EK_DUMMY.

(*
enum Fault {
	Fault_None,
	Fault_AccessFlag,
	Fault_Alignment,
	Fault_Background,
	Fault_Domain,
	Fault_Permission,
	Fault_Translation,
	Fault_AddressSize,
	Fault_SyncExternal,
	Fault_SyncExternalOnWalk,
	Fault_SyncParity,
	Fault_SyncParityOnWalk,
	Fault_AsyncParity,
	Fault_AsyncExternal,
	Fault_Debug,
	Fault_TLBConflict,
	Fault_BranchTarget,
	Fault_HWUpdateAccessFlag,
	Fault_Lockdown,
	Fault_Exclusive,
	Fault_ICacheMaint
};
*)

Inductive Fault :=
| Fault_None
| Fault_AccessFlag
| Fault_Alignment
| Fault_Background
| Fault_Domain
| Fault_Permission
| Fault_Translation
| Fault_AddressSize
| Fault_SyncExternal
| Fault_SyncExternalOnWalk
| Fault_SyncParity
| Fault_SyncParityOnWalk
| Fault_AsyncParity
| Fault_AsyncExternal
| Fault_Debug
| Fault_TLBConflict
| Fault_BranchTarget
| Fault_HWUpdateAccessFlag
| Fault_Lockdown
| Fault_Exclusive
| Fault_ICacheMaint.

(*
struct FaultRecord {
	enum Fault statuscode; // Fault Status
	//  AccType acctype; // Type of access that faulted
	//  FullAddress ipaddress; // Intermediate physical address
	//  boolean s2fs1walk; // Is on a Stage 1 page table walk
	//  boolean write; // TRUE for a write, FALSE for a read
	//  integer level; // For translation, access flag and permission faults
	//  bit extflag; // IMPLEMENTATION DEFINED syndrome for external aborts
	//  boolean secondstage; // Is a Stage 2 abort
	//  bits(4) domain; // Domain number, AArch32 only
	//  bits(2) errortype; // [Armv8.2 RAS] AArch32 AET or AArch64 SET
	//  bits(4) debugmoe; // Debug method of entry, from AArch32 only
};
 *)

Record FaultRecord :=
  mkFaultRecord {
      statuscode : Fault
    }.

(*
struct FullAddress {
	uint64_t address; // bits(52) address;
	bool NS;          // bit NS; // '0' = Secure, '1' = Non-secure
};
 *)

Record FullAddress :=
  mkFullAddress {
      paddress : Z;
      NS : bool
    }.

(*
struct AddressDescriptor {
	struct FaultRecord fault; // fault.statuscode indicates whether the address is valid
	//  MemoryAttributes memattrs;
	struct FullAddress paddress;
	uint64_t vaddress; // bits(64) vaddress;
};
 *)

Record AddressDescriptor :=
  mkAddressDescriptor {
      paddress_in_desc: FullAddress;
      vaddress : Z;
    }.

(* 
   
struct TLBRecord {
	//  Permissions        perms;
	//  bit 	             nG;	   // '0' = Global, '1' = not Global
	//  bits(4)	     domain;	   // AArch32 only
	//  bit		     GP;	   // Guarded Page
	//  boolean	     contiguous;   // Contiguous bit from page table
	//  integer	     level;	   // AArch32 Short-descriptor format: Indicates Section/Page
	//  integer	     blocksize;    // Describes size of memory translated in KBytes
	//  DescriptorUpdate   descupdate;   // [Armv8.1] Context for h/w update of table descriptor
	//  bit		     CnP;	   // [Armv8.2] TLB entry can be shared between different PEs
	struct AddressDescriptor  addrdesc;
};

*)

Record TLBRecord :=
  mkTLBRecord {
      addrdesc: AddressDescriptor
    }.


(* 
struct TLBRecord mkFault(uint64_t vaddress) {
	struct TLBRecord r = { .addrdesc = { .fault = { .statuscode=Fault_Translation } , .paddress =  { .address=0, .NS=0 }, .vaddress = vaddress } };
	return r;
	// massively oversimplified
}
 *)

Definition mkFault (vaddress : Z) :=
  mkTLBRecord (mkAddressDescriptor (mkFullAddress 0 false) vaddress).

(*
struct TLBRecord mkTranslation(uint64_t vaddress, uint64_t pa) {
	struct TLBRecord r = { .addrdesc = { .fault = { .statuscode=Fault_None } , .paddress =  { .address=pa, .NS=1 }, .vaddress = vaddress } };
	return r;
	// massively oversimplified
}
 *)

Definition mkTranslation (vaddress pa : Z) :=
  mkTLBRecord (mkAddressDescriptor (mkFullAddress pa true) vaddress).

(*
struct TLBRecord AArch64_TranslationTableWalk( uint64_t table_base, uint64_t level, uint64_t vaddress) {
	// these declarations should really be combined with their
	// initialisations below, but the compiler complains that ISO C90
	// forbids mixed declations and code
	uint64_t pte;
	uint64_t table_base_next_virt, table_base_next_phys;

	uint64_t offset = 0; // offset in bytes of entry from table_base
	switch (level) {
	case 0: offset = (vaddress & GENMASK(47,39)) >> (39-3); break;
	case 1: offset = (vaddress & GENMASK(38,30)) >> (30-3); break;
	case 2: offset = (vaddress & GENMASK(29,21)) >> (21-3); break;
	case 3: offset = (vaddress & GENMASK(20,12)) >> (12-3); break; 
	default: return mkFault(vaddress); // this is just to tell the compiler that the cases are exhaustive
	}

	// the actual page table entry
	pte = * ((uint64_t * )(table_base + offset));

	switch(level) {
	case 3:
		switch (pte & GENMASK(1,0)) {
		case ENTRY_INVALID_0:
		case ENTRY_INVALID_2:
		case ENTRY_BLOCK:
			// invalid or fault entry
			return mkFault(vaddress);
		case ENTRY_PAGE_DESCRIPTOR: // page descriptor
			return mkTranslation(vaddress, (pte & GENMASK(47,12)) | (vaddress & GENMASK(11,0)));
		}

	case 0:
	case 1:

	case 2:
	{
		switch (pte & GENMASK(1,0)) {
		case ENTRY_INVALID_0:
		case ENTRY_INVALID_2:
			return mkFault(vaddress);
		case ENTRY_BLOCK:
			switch (level) {
			case 0:
				return mkFault(vaddress);
			case 1:
				return mkTranslation(vaddress, (pte & GENMASK(47,30)) | (vaddress & GENMASK(29,0)));
			case 2:
				return mkTranslation(vaddress, (pte & GENMASK(47,21)) | (vaddress & GENMASK(20,0)));
			}
		case ENTRY_TABLE: // recurse
		{
			table_base_next_phys = pte & GENMASK(47,12);
			table_base_next_virt = (u64)hyp_phys_to_virt((phys_addr_t)table_base_next_phys);

			return AArch64_TranslationTableWalk(table_base_next_virt, level+1, vaddress);
		}
		default: return mkFault(vaddress); // this is just to tell the compiler that the cases are exhaustive
		}
	}
	default: return mkFault(vaddress); // this is just to tell the compiler that the cases are exhaustive
	}
}
 *)


Inductive RESULT (A : Type) :=
| SUCCESS (res : A)
| FAIL (error: string).

Arguments SUCCESS {A} res.
Arguments FAIL {A} error.

Instance Monad_RESULT : Monad RESULT :=
  {
  ret _ x := SUCCESS x
  ; bind _ _ m f :=
      match m with
      | FAIL err => FAIL err
      | SUCCESS res => f res
      end
  }.

Notation "'guard' cond 'report' err ';;' B" :=
  (if cond then B else FAIL err)
    (at level 61, cond at next level, err at next level, right associativity)
  : ffa_monad_scope.

Local Open Scope ffa_monad_scope.

Definition result_from_option {T} (error: string) (x: option T) : RESULT T :=
  match x with
  | None => FAIL error
  | Some v => SUCCESS v
  end.

Example GET_TEST : RESULT Z :=
  a <- result_from_option
        "error"
        (Some 1)
  ;; ret a.

Example GUARD_TEST : RESULT (Z * bool) :=
  guard decide (1 = 1) report "error"
  ;; ret (1, true).

Class AuxiliaryFunciton :=
  {
  GetTableEntry : Z -> Z;
  hyp_phys_to_virt : Z -> Z;
  }.

Context `{auxiliary_function: AuxiliaryFunciton}.

(* To define fixpoint, we reverse the level -
   3 -> 0
   2 -> 1
   1 -> 2
   0 -> 3
 *)

Definition get_offset_op (level : nat) (vaddress : Z):=
  (*
    uint64_t offset = 0; // offset in bytes of entry from table_base
    switch (level) {
    case 0: offset = (vaddress & GENMASK(47,39)) >> (39-3); break;
    case 1: offset = (vaddress & GENMASK(38,30)) >> (30-3); break;
    case 2: offset = (vaddress & GENMASK(29,21)) >> (21-3); break;
    case 3: offset = (vaddress & GENMASK(20,12)) >> (12-3); break; 
    default: return mkFault(vaddress); // this is just to tell the compiler that the cases are exhaustive 
    }
   *)
  if decide (level = 3)%nat
  then Some (Z.shiftr (Z.land vaddress (GENMASK 47 39)) (39 - 3))
  else if decide (level = 2)%nat
       then Some (Z.shiftr (Z.land vaddress (GENMASK 39 30)) (30 - 3))
       else if decide (level = 1)%nat
            then Some (Z.shiftr (Z.land vaddress (GENMASK 29 31)) 21 - 3)
            else if decide (level = 0)%nat
                 then Some (Z.shiftr (Z.land vaddress (GENMASK 20 12)) (12 - 3))
                 else None.

Fixpoint AArch64_TranslationTableWalk_aux (level : nat) (table_base vaddress : Z) :=
  let offset_op := get_offset_op level vaddress in  
  match offset_op with
  | Some offset =>
    let
      (* Need to get the value of pte instead of its address *)
      pte := GetTableEntry (table_base + offset) in
    match level with
    | O =>
      (*
	// the actual page table entry
	pte = * ((uint64_t * )(table_base + offset));
       *)
        (* switch (pte & GENMASK(1,0)) {
	   case ENTRY_INVALID_0:
	   case ENTRY_INVALID_2:
	   case ENTRY_BLOCK:
	   // invalid or fault entry
	   return mkFault(vaddress);
	   case ENTRY_PAGE_DESCRIPTOR: // page descriptor
	   return mkTranslation(vaddress, (pte & GENMASK(47,12)) | (vaddress & GENMASK(11,0)));
	   }
         *)
        if decide ((Z.land pte (GENMASK 1 0)) = EK_PAGE_DESCRIPTOR_of_Z)
        then mkTranslation vaddress (Z.lor (Z.land pte (GENMASK 47 12))
                                           (Z.land vaddress (GENMASK 11 0)))
        else mkFault vaddress
    | S level' =>
      if decide ((Z.land pte (GENMASK 1 0)) = EK_TABLE_of_Z)
      then
        (*
	  case ENTRY_TABLE: // recurse
	  {
	  table_base_next_phys = pte & GENMASK(47,12);
	  table_base_next_virt = (u64)hyp_phys_to_virt((phys_addr_t)table_base_next_phys);
          
	  return AArch64_TranslationTableWalk(table_base_next_virt, level+1, vaddress);
	  }
         *)
	let table_base_next_phys := Z.land pte (GENMASK 47 12) in
        let table_base_next_virt := hyp_phys_to_virt table_base_next_phys in
	AArch64_TranslationTableWalk_aux level' table_base_next_virt vaddress
      else
        (*
	    case ENTRY_BLOCK:
	    switch (level) {
	    case 0:
	    return mkFault(vaddress);
	    case 1:
	    return mkTranslation(vaddress, (pte & GENMASK(47,30)) | (vaddress & GENMASK(29,0)));
	    case 2:
	         return mkTranslation(vaddress, (pte & GENMASK(47,21)) | (vaddress & GENMASK(20,0)));
		 }
         *)        
        if decide (Z.land pte (GENMASK 1 0) = EK_BLOCK_of_Z)
        then
          if decide (level = 0%nat \/ (level >= 3)%nat)
          then mkFault vaddress
          else if decide (level = 1%nat)
               then mkTranslation vaddress
                                  (Z.lor (Z.land pte (GENMASK 47 30))
                                         (Z.land vaddress (GENMASK 29 0)))
               else mkTranslation vaddress
                                  (Z.lor (Z.land pte (GENMASK 47 21))
                                         (Z.land vaddress (GENMASK 20 0)))
        else mkFault vaddress
    end
  | None => mkFault vaddress
  end.


Definition AArch64_TranslationTableWalk (table_base level vaddress : Z) :=
  if decide (level = 3)
  then AArch64_TranslationTableWalk_aux 0 table_base vaddress
  else if decide (level = 2)
       then AArch64_TranslationTableWalk_aux 1 table_base vaddress
       else if decide (level = 1)
            then AArch64_TranslationTableWalk_aux 2 table_base vaddress
            else if decide (level = 0)
                 then AArch64_TranslationTableWalk_aux 3 table_base vaddress
                 else mkFault vaddress.
  
(*
struct AddressDescriptor AArch64_FirstStageTranslate(uint64_t table_base, uint64_t vaddress /*, AccType acctype, boolean iswrite, boolean wasaligned, integer size*/) {

	/* S1 = AArch64.TranslationTableWalk(ipaddress, TRUE, vaddress, acctype, iswrite, secondstage, s2fs1walk, size); */
	struct TLBRecord S1 = AArch64_TranslationTableWalk(table_base, 0, vaddress);

	return S1.addrdesc;
}
 *)

Definition AArch64_FirstStageTranslate (table_base vaddress : Z) :=
  let s1 :=  AArch64_TranslationTableWalk table_base 0 vaddress in
  s1.(addrdesc).


(******************************************************************************************************)
(*
/* abstraction of pKVM intended mappings */

enum mapping_kind {
	HYP_NULL,
	HYP_TEXT,
	HYP_RODATA,
	HYP_RODATA2,
	HYP_BSS,
	HYP_BSS2,
	HYP_IDMAP,
	HYP_STACKS,
	HYP_VMEMMAP,
	HYP_S1_PGTABLE,
	HYP_S2_MEM_PGTABLE,
	HYP_S2_DEV_PGTABLE,
	HYP_WORKSPACE,
	HYP_VMEMMAP_MAP,
	HYP_UART,
	HYP_PERCPU,
	HYP_MAPPING_KIND_NUMBER=HYP_PERCPU
};
 *)

Inductive mapping_kind :=
| HYP_NULL
| HYP_TEXT
| HYP_RODATA
| HYP_RODATA2
| HYP_BSS
| HYP_BSS2
| HYP_IDMAP
| HYP_STACKS
| HYP_VMEMMAP
| HYP_S1_PGTABLE
| HYP_S2_MEM_PGTABLE
| HYP_S2_DEV_PGTABLE
| HYP_WORKSPACE
| HYP_VMEMMAP_MAP
| HYP_UART
| HYP_PERCPU
| HYP_MAPPING_KIND_NUMBER.

Definition HYP_NULL_of_Z := 0.
Definition HYP_TEXT_of_Z := 1.
Definition HYP_RODATA_of_Z := 2.
Definition HYP_RODATA2_of_Z := 3.
Definition HYP_BSS_of_Z := 4.
Definition HYP_BSS2_of_Z := 5.
Definition HYP_IDMAP_of_Z := 6.
Definition HYP_STACKS_of_Z := 7.
Definition HYP_VMEMMAP_of_Z := 8.
Definition HYP_S1_PGTABLE_of_Z := 9.
Definition HYP_S2_MEM_PGTABLE_of_Z := 10.
Definition HYP_S2_DEV_PGTABLE_of_Z := 11.
Definition HYP_WORKSPACE_of_Z := 12.
Definition HYP_VMEMMAP_MAP_of_Z := 13.
Definition HYP_UART_of_Z := 14.
Definition HYP_PERCPU_of_Z := 15.
Definition HYP_MAPPING_KIND_NUMBER_of_Z := 15.

(* 
/*
 * Maximum supported processors.  Setting this smaller saves quite a
 * bit of memory.  Use nr_cpu_ids instead of this except for static bitmaps.
 */
#ifndef CONFIG_NR_CPUS
/* FIXME: This should be fixed in the arch's Kconfig */
#define CONFIG_NR_CPUS	1
#endif

/* Places which use this should consider cpumask_var_t. */
#define NR_CPUS		CONFIG_NR_CPUS

*)

Definition NR_CPUS := 1.

(* #define MAX_MAPPINGS HYP_MAPPING_KIND_NUMBER -1 + NR_CPUS *)
Definition MAX_MAPPING := HYP_MAPPING_KIND_NUMBER_of_Z -1 + NR_CPUS.

(* #define DUMMY_CPU 0 *)
Definition DUMMY_CPU := 0.


(*
#ifdef CONFIG_PHYS_ADDR_T_64BIT
typedef u64 phys_addr_t;
#else
typedef u32 phys_addr_t;
#endif
 *)


(*
enum kvm_pgtable_prot {
	KVM_PGTABLE_PROT_X			= BIT(0),
	KVM_PGTABLE_PROT_W			= BIT(1),
	KVM_PGTABLE_PROT_R			= BIT(2),

	KVM_PGTABLE_PROT_DEVICE			= BIT(3),
};
*)
Inductive kvm_pgtable_prot :=
| KVM_PGTABLE_PROT_X 
| KVM_PGTABLE_PROT_W
| KVM_PGTABLE_PROT_R
| KVM_PGTABLE_PROT_DEVICE.

Definition KVM_PGTABLE_PROT_X_of_Z := 0.
Definition KVM_PGTABLE_PROT_W_of_Z := 1.
Definition KVM_PGTABLE_PROT_R_of_Z := 2.
Definition KVM_PGTABLE_PROT_DEVICE_of_Z := 3.

Definition phys_addr_t := Z.

(* 
// abstracts to:
// - itself, i.e. to the canonical interpretation for data structures (especially simple as this contains no pointers)
struct mapping {
	enum mapping_kind kind;           // the kind of this mapping
	u64 cpu;                          // cpu ID in 0..NR_CPUS-1 for HYP_PERCPU mappings; 0 otherwise
	u64 virt;                         // pKVM EL2 after-the-switch start virtual address, page-aligned
	phys_addr_t phys;                 // start physical address, page-aligned
	u64 size;                         // size, as the number of 4k pages
	enum kvm_pgtable_prot prot;       // protection
	char *doc;                        // documentation string, ignore in maths
};
 *)

Record mapping :=
  mkmapping {
      kind :  mapping_kind;
      cpu : Z;
      virt : Z;
      phys : phys_addr_t;
      size : Z;
      prot : kvm_pgtable_prot
    }.

(*
// invariants:
// - after construction, sorted by virtual address
// - non-overlapping virtual address ranges
// - at most one per mapping_kind except HYP_PERCPU, for which at most one for each cpu up to NR_CPUS
// - count <= MAX_MAPPINGS
// abstracts to:
// - a finite set of [[struct mapping]] also satisfying the above
struct mappings {
	struct mapping m[MAX_MAPPINGS];
	u64 count;
};

// most of our checker code treats datastructures pseudo-functionally,
// but we have to allocate them somehow, and we can't put them on the
// stack as pKVM has only one page of stack per-CPU.  We also want to
// hide this from the setup.c call sites, where mappings data has to
// flow from record_hyp_mappings to later check_hyp_mappings.  So we
// just make global variables, but we use them explicitly only in the
// top-level functions of this file; below that we pass pointers to
// them around.
static struct mappings mappings;
*)

Definition mappings := ZTree.t mapping.

(*
/* sort mappings by virtual address*/

/* we do this after construction with the linux heapsort, as it's
   handy, but it might be tidier to maintain sortedness during
   construction */

static int mapping_compare(const void *lhs, const void *rhs)
{
	if (((const struct mapping * )lhs)->virt < ((const struct mapping * )rhs)->virt) return -1;
	if (((const struct mapping * )lhs)->virt > ((const struct mapping * )rhs)->virt) return 1;
	return 0;
}
*)

Definition mapping_compare (lhs rhs : mapping) :=
  if decide (lhs.(virt) < rhs.(virt))
  then -1
  else if decide (lhs.(virt) > rhs.(virt))
       then 1 else 0.
  
(*          
void sort_mappings(struct mappings *mappings)
{
	sort(mappings, HYP_MAPPING_KIND_NUMBER, sizeof(struct mapping), mapping_compare, NULL);
}
 *)
(* DISCUSSION POINT: 
   sorting is somewhat tricky in Coq to write it as a functional version. For the relational version, 
   it's possible that we can add it as a proposition. 
   
   We also can provide an abstract definition with adding properties about it.
   But, to run testing, we are required to provide functional definition. 

*)
