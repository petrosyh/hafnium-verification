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

Require Import Decision.

Require Import Coqlib sflib.

(* FFA Memory management related parts *)
Require Export FFAMemoryHypCall.
Require Import FFAMemoryHypCallIntro.

Require Import Maps.
Set Implicit Arguments.

Definition Z_64MAX := ((Z.pow 2 64) - 1)%Z.
Definition Z_not := fun val => (Z.lxor Z_64MAX val).
 
(*************************************************************)
(** *                Introduction                            *) 
(*************************************************************)

(** This file contains formalizations for FFA memory management descriptors. The most relavant parts regarding 
    this file is from Section 5.10 to Section 5.12 in the document.
*)

(** **** *)

(*************************************************************)
(** *      Types and Constant values that are used in FF     *) 
(*************************************************************)
Section FFA_TYPES_AND_CONSTANT.

  (** Value types are mostly type aliasing for the readability of our modeling. 
      Several types are simply Z or bool types. *)
  Class FFA_TYPES_AND_CONSTANTS :=
    {
    (** - 2.8. Partition identification and discovery 
        - 2.9. An execution context is identified by using a 16-bit ID. This ID is referred
        to as the vCPU or execution context ID *)
    ffa_UUID_t : Type := Z;
    ffa_VCPU_ID_t : Type := Z;
    (** - 8.1. FFA_VERSION: 
        The first one is a major version number and the second one is for the minor version *)
    ffa_version_number_t : Type := (Z * Z)%type; 

    (** - For CPU ID values *)
    ffa_CPU_ID_t : Type := Z;
    (** - A bare address value that represent the memory PA *)
    ffa_address_t := Z;
    ffa_granuale_size_t := Z;
    (** - Parts of return value types of FFA calls *)
    ffa_memory_handle_t := Z;
    (** - Type for one of descriptor information. They are only used in two FFA interfaces, 
        [FFA_MEM_RETRIEVE_REQ] and [FFA_MEM_RETRIEVE_RESP] *)
    ffa_memory_receiver_flags_t := bool;

    (** - Type for an implementation defined values that are used in 
        [FFA_MEM_DONATE], [FFA_MEM_SHARE], and [FFA_MEM_LEND]. So, we cannot specify the value by
        defining inductive types. In this sense, we define it as a general Type *)
    ffa_memory_region_tag_t : Type;

    (** - Granuale value. It is usually a multiplication of 4096 (4KiB) *)
    granuale : ffa_granuale_size_t;
    init_ffa_memory_region_tag : ffa_memory_region_tag_t;
    }.

End FFA_TYPES_AND_CONSTANT.

(*************************************************************)
(** *                         FFA  keyword                   *) 
(*************************************************************)
Section FFA_DATATYPES.
  (** This section defines several keywords that are necessary to model 
      FFA memory management interfaces *)
  
  Context `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}.

  (** The following types are defined in Chapter 11 (Memory management interfaces document).
      Integer values are not actually used in our formal definitions. However, those details are 
      handled in our test interface, [FFAMemoryHypCallTestingInterface.v]. 
      FFA Memory management related ABIs are as follows:
   - [FFA_MEM_DONATE]
     - Defined in Table 11.3 FFA_MEM_DONATE function syntax         
   - [FFA_MEM_LEND]
     - Defined in Table 11.8 FFA_MEM_LEND function syntax           
   - [FFA_MEM_SHARE]
     - Defined in Table 11.13: FFA_MEM_SHARE function syntax        
   - [FFA_MEM_RETRIEVE_REQ]
     - Defined in Table 11.18 FFA_MEM_RETRIEVE_REQ function syntax  
   - [FFA_MEM_RETRIEVE_RESP]
     - Defined in Table 11.22: FFA_MEM_RETRIEVE_RESP function synta 
   - [FFA_MEM_RELINQUISH]
     - Defined in Table 11.27: FFA_MEM_RELINQUISH function syntax   
   - [FFA_MEM_RECLAIM]
     - Defined in Table 11.31: FFA_MEM_RECLAIM function syntax      
   *)
  
  (** **** *)

  (** **** FFA Function Type Coq Definition *)
  Inductive FFA_FUNCTION_TYPE :=
  | FFA_MEM_DONATE
  | FFA_MEM_LEND
  | FFA_MEM_SHARE
  | FFA_MEM_RETREIVE_REQ
  | FFA_MEM_RETREIVE_RESP
  | FFA_MEM_RELINQUISH
  | FFA_MEM_RECLAIM.

  (** The following parts are not defined in Chapter 5, but in Chapter 7.

  Error codes are defined in Table 7.2: Error status codes
   - [FFA_NOT_SUPPORTED]
   - [FFA_INVALID_PARAMETERS]
   - [FFA_NO_MEMORY]
   - [FFA_BUSY]
   - [FFA_INTERRUPTED]
   - [FFA_DENIED]
   - [FFA_RETRY]
   - [FFA_ABORTED]
  *)

  (** **** *)

  (** **** FFA Error Code Type Coq Definition *)  
  Inductive FFA_ERROR_CODE_TYPE :=
  | FFA_NOT_SUPPORTED
  | FFA_INVALID_PARAMETERS
  | FFA_NO_MEMORY
  | FFA_BUSY
  | FFA_INTERRUPTED
  | FFA_DENIED
  | FFA_RETRY
  | FFA_ABORTED.  
  
  (** The following numbers are also defined in Chapter 7
      - [FFA_ERROR]
        - Defined in Table 7.4: FFA_ERROR function syntax
      - [FFA_SUCCESS] 
        - Defined in Table 7.7: FFA_SUCCESS function syntax
  *)

  (** *** FFA Result Code Type Coq Definition *)  
  Inductive FFA_RESULT_CODE_TYPE :=
  | FFA_ERROR (ffa_error_value : FFA_ERROR_CODE_TYPE) 
  | FFA_SUCCESS (ffa_handle : ffa_memory_handle_t).

  (** *** FFA Identifier Type Coq Definition *)    
  (** This version only focus on two FFA interfaces, memory management related interfaces and interfaces for 
     the result of memory management related parts *) 
  Inductive FFA_IDENTIFIER_TYPE :=
  | FFA_IDENTIFIER_DEFAULT
  | FFA_FUNCTION_IDENTIFIER (func: FFA_FUNCTION_TYPE)
  | FFA_RESULT_CODE_IDENTIFIER (func: FFA_RESULT_CODE_TYPE).

End FFA_DATATYPES.
  
(*************************************************************)
(** *                 FFA value structures                   *) 
(*************************************************************)
(** This one is related to the interface definitions in Section 11 of the document.

    The following definitions are not parts of Section 5 in the document. However, they are essential when 
    defining memory management interfaces. *)
Section FFA_STRUCTURES.

  Context `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}.
  
  (**
  Most A64 instructions operate on registers. The architecture provides 31 general purpose registers. 
  Each register can be used as a 64-bit X register (X0..X30), or as a 32-bit W register
  (W0..W30). These are two separate ways of looking at the same register. For example, this
  register diagram shows that W0 is the bottom 32 bits of X0, and W1 is the bottom 32 bits of X1:

  However, we model the minimum registers that are necessary for us to define FFA memory management interfaces. 
  We also referred Hafnium to find out the minimum registers that we need. 

  Register values are all Z types *)
  Definition reg_t := PMap.t Z.

  (** The minimum register model that are necessary for modeling FFA memory management interfaces 
      - The first value (func) contains FFA identifiers
        - [uint64_t func;]  
      - Other 7 regiters contains several arguments of the FFA call (or, return value after serving the FFA call).
        - [uint64_t arg1;]
        - [uint64_t arg2;]
        - [uint64_t arg3;]
        - [uint64_t arg4;]
        - [uint64_t arg5;]
        - [uint64_t arg6;]
        - [uint64_t arg7;]

  *)
  
  (** *** Formal definition of FFA value *)
  Record FFA_value_type :=
    mkFFA_value_type{
        (** - This one is actually a register value, but we only use that as a FFA_IDENTIFIER_TYPE. Therefore, 
         *) 
        ffa_type : FFA_IDENTIFIER_TYPE;
        (** - [TODO: do we need to make a conversion from each arg into the corresponding descriptors?] *)
        vals : ZMap.t Z
      }.
  
  (** Default value *)
  Definition init_FFA_value_type :=
    mkFFA_value_type FFA_IDENTIFIER_DEFAULT (ZMap.init 0).

End FFA_STRUCTURES.

(*************************************************************)
(** *                       Descriptors                      *) 
(*************************************************************)
(** [The following parts are related to "5.10 Memory region description" and "5.11 Memory region properties"] *)
Section FFA_DESCRIPTIONS.

  (**************************************)
  (** ** 5.10 Memory region description *)
  (**************************************)

  (** 
      A memory region is described in a memory management transaction either through a Composite memory region
      descriptor (see 5.10.1 Composite memory region descriptor) or a globally unique Handle (see 5.10.2 Memory
      region handle).
      
      The former is used to describe a memory region when a transaction to share, lend or donate memory is 
      initiated by the Owner and when the memory region is retrieved by the Receiver.

      The latter is used to describe a memory region when it is retrieved by a Receiver, relinquished by a 
      Borrower and reclaimed by the Owner.
   *)
  Context `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}.

  (****************************************************************************)
  (** ***  Constituent memory region and composite_memory_region descriptors  *) 
  (****************************************************************************)  
  (** [We define descriptors that are used in FFA interfaces. Sender, Relayer, and Borrower use them 
      to figure out the information and check validity of the query by using them] *)
  (** A memory region is described in a memory management transaction by specifying the list and count of 4K sized
      pages that constitute it (see Table 5.13). 

      [JIEUNG: due to the dependency, we reordered the table. we first introduce Table 5.14, then 
      introduce Table 5.13] *)
     
  (** 
      The list is specified by using one or more constituent memory region descriptors (see Table 5.14). 
      Each descriptor specifies the base address and size of a virtually or physically contiguous memory region.

      Table 5.14: Constituent memory region descriptor
      - [uint64_t address;]: base IPA of the constituent memory region, aligned to 4 kiB page size granularity.
        The number of 4 kiB pages in the constituent memory region. 
      - [uint32_t page_count;]
      - [uint32_t reserved;]: Reserved field, must be 0.
   *)
  (* 
     Field              Byte length     Byte offset     Description
     Address            8               -               - Base VA, PA or IPA of constituent memory region aligned to
                                                          the page size (4K) granularity.
     Page count         4               8               - Number of 4K pages in constituent memory region.
     Reserved (MBZ)     4               12 
   *)

  (**
     The pages are addressed using VAs, IPAs or PAs depending on the FF-A instance at which the transaction is taking
     place. This is as follows.
     - VAs are used at a Secure virtual FF-A instance if the partition runs in Secure EL0 or Secure User mode.
     - IPAs are used at a virtual FF-A instance if the partition runs in one of the following Exception levels.
       - Secure EL1.
       - Secure Supervisor mode.
       - EL1.
       - Supervisor mode.
     - PAs are used at all physical FF-A instances.

     Figure 5.2 describes a virtually contiguous memory region range VA_0 of size 16K through its composite memory
     region descriptors at the virtual and physical FF-A instances. VA_0 was allocated through a dynamic memory
     management mechanism inside an endpoint for example, malloc. It is composed of:

     - Two constituent IPA regions IPA_0 and IPA_1 of size 8K each at the virtual FF-A instance.
     - IPA_0 is comprised of two PA regions PA_0 and PA_1 at the physical FF-A instance. Each PA region is of
       size 4K.
     - IPA_1 is comprised of two PA regions PA_2 and PA_3 at the physical FF-A instance. Each PA region is of
       size 4K.
   *)
  
  (** **** FFA Memory Region Constituent Coq Definition *)
  Record FFA_memory_region_constituent_struct :=
    mkFFA_memory_region_constituent_struct {
        (** - length: 8 bytes / offset: 0 bytes *)
        FFA_memory_region_constituent_struct_address : ffa_address_t;
        (** - length: 4 bytes / offset: 4 bytes *)
        FFA_memory_region_constituent_struct_page_count : Z;
        (** - reserved MBZ - length: 4 bytes / offset: 12 byte *) 
      }.

  Definition init_FFA_memory_region_constituent_struct :=
    mkFFA_memory_region_constituent_struct 0 0.
  
  (** Table 5.13: Composite memory region descriptor - A set of pages comprising a memory region. 
      - [uint32_t page_count;]: The total number of 4 kiB pages included in this memory region. 
        This must be equal to the sum of page counts specified in each 
        [ffa_memory_region_constituent] which is defined the above. 
      - [uint32_t constituent_count;]: The number of constituents ([ffa_memory_region_constituent]) 
        included in this memory region range.
      - [uint64_t reserved_0;]: Reserved field, must be 0. 
      - [struct ffa_memory_region_constituent* constituents;]: An array of `constituent_count` memory region constituents.
   *)

  (*
    Field                Byte length     Byte offset     Description
    Total page count     4               0               - Size of the memory region described as the count
                                                           of 4K pages.
                                                         - Must be equal to the sum of page counts specified
                                                           in each constituent memory region descriptor. See
                                                           Table 5.14.
    Address range count  4               4               - Count of address ranges specified using
                                                           constituent memory region descriptors.
    Reserved (MBZ)       8               8
    Address range array  –               16              - Array of address ranges specified using
                                                           constituent memory region descriptors.
   *)

  (** **** FFA Composition Memory Region Coq Definition *)  
  Record FFA_composite_memory_region_struct :=
    mkFFA_composite_memory_region_struct {
        (** - length: 4 bytes / offset: 0 bytes  *)
        FFA_composite_memory_region_struct_page_count : Z;
        (** - [FFA_composite_memory_region_struct_constituent_count : Z; 
              - we ignored this one by representing constituents one as a list 
              - length: 4 bytes / offset: 4 bytes *)
        (** - reserved - legnth: 8 bytes / offset: 8 bytes *)
        (** - length: 16 bytes * num of elements / offset: 16 bytes *)
        FFA_composite_memory_region_struct_constituents :
          list FFA_memory_region_constituent_struct
      }.
     
  Definition init_FFA_composite_memory_region_struct := 
    mkFFA_composite_memory_region_struct 0 nil.
  
  (** Basic well-formedness condition
      - "Figure 5.2: Example memory region description" shows how those two are related 
      - Some parts in 5.12 also explains invariants that the above definitions has to satisfy 
        (addresses should not be overlapped)
      - [TODO: Need to add more conditions]
   *)

  (** **** Well formed conditions *)
  (** Check addresses in multiple constituents to see whether they are disjoint *)
  Fixpoint check_overlap_in_ranges
    (ranges : list (Z * Z)) (range : (Z * Z)) :=
    match ranges with
    | nil => true
    | hd::tl =>
      check_overlap_in_ranges tl range &&
      (decide ((fst hd) > (snd range)) || decide ((fst range) > snd (hd)))
    end.
  
  Fixpoint check_overlap_of_constituents_aux
           (constituents : list FFA_memory_region_constituent_struct)
           (ranges : list (Z * Z)) : option (list (Z * Z)) :=
    match constituents with
    | nil => Some ranges
    | hd::tl =>
      match check_overlap_of_constituents_aux tl ranges with
      | Some ranges' =>
        let first_addr := hd.(FFA_memory_region_constituent_struct_address) in
        let last_addr :=
            (first_addr +
            granuale *
            hd.(FFA_memory_region_constituent_struct_page_count))%Z in
        if check_overlap_in_ranges ranges' (first_addr, last_addr)
        then Some ((first_addr, last_addr)::ranges')
        else None
      | _ => None
      end
    end.
      
  Definition check_overlap_of_constituents
             (constituents : list FFA_memory_region_constituent_struct) :=
    match check_overlap_of_constituents_aux constituents nil with
    | Some _ => true
    | _ => false
    end.

  (** Check well formed conditions 
      - Page count needs to be consistent
      - All addresses can be divided by granuale *)
  Fixpoint well_formed_FFA_composite_memory_region_struct_aux
           (page_counts : Z)
           (constituents : list FFA_memory_region_constituent_struct) :=
    match constituents with
    | nil => if decide (page_counts = 0) then true else false
    | hd::tl =>
      match hd with
      | mkFFA_memory_region_constituent_struct address page_count =>
        if decide (Z.modulo address granuale = 0) &&
           decide ((page_counts - page_count)%Z >= 0) 
        then well_formed_FFA_composite_memory_region_struct_aux
               (page_counts - page_count) tl
        else false
      end
    end.

  (** Return INVALID_PARAMETER when it is not satisfied *)
  Definition well_formed_FFA_composite_memory_region_struct
             (composite: FFA_composite_memory_region_struct) :=
    if (well_formed_FFA_composite_memory_region_struct_aux
          (composite.(FFA_composite_memory_region_struct_page_count))
          (composite.(FFA_composite_memory_region_struct_constituents)) &&
        check_overlap_of_constituents 
          composite.(FFA_composite_memory_region_struct_constituents))
    then None else Some (FFA_INVALID_PARAMETERS).
  
  (***********************************************************************)
  (** ***                       Memory region handle                     *) 
  (***********************************************************************)  
  (** Handle : 64-bit, and the handle is allocated by teh replayer 
     - A 64-bit Handle is used to identify a composite memory region description for example, VA_0 described in
       Figure 5.2
     - The Handle is allocated by the Relayer as follows.
       – The SPM must allocate the Handle if any Receiver participating in the memory management transaction
         is an SP or SEPID associated with a Secure Stream ID in the SMMU.
       – The Hypervisor must allocate the Handle if no Receiver participating in the memory management
         transaction is an SP or SEPID associated with a Secure Stream ID in the SMMU.
     - A Handle is allocated once a transaction to lend, share or donate memory is successfully 
       initiated by the Owner.
     - Each Handle identifies a single unique composite memory region description that is, 
       there is a 1:1 mapping between the two.
     - A Handle is freed by the Relayer after it has been reclaimed by its Owner at the end 
       of a successful transaction to relinquish the corresponding memory region description.
     - Encoding of a Handle is as follows.
       – Bit(63): Handle allocator.
         - b0: Allocated by SPM.
         - b1: Allocated by Hypervisor.
       - Bit(62:0): IMPLEMENTATION DEFINED.
     - A Handle must be encoded as a register parameter in any ABI that requires it as follows.
       - Two 32-bit general-purpose registers must be used such that if Rx and Ry are used, such that x < y,
         - Rx = Handle(31:0).
         - Ry = Handle(63:32). *)

  (** Memory region handle in Hafnium is actually the index of "share_state_pool" 
      defined in FFAMemoryHypCallState.v) 
      which contains the information that receivers has to look up. *)

  (* Abstract functions for those things are defined in the below (DescriptorContext *)

  (**************************************)
  (** ** 5.11 Memory region properties  *)
  (**************************************)  
  (****************************************************************************)
  (** ***  Constituent memory region and composite_memory_region descriptors  *) 
  (****************************************************************************)
  
  (** From here, most parts are related to 5.11 Memory region properties.
     - Instruction and data access permissions describe the type of access permitted on the memory region.
     - One or more endpoint IDs that have access to the memory region specified by a combination of access
       permissions and memory region attributes.
     - Memory region attributes control the memory type, accesses to the caches, and whether 
       the memory region is Shareable and therefore is coherent.
  
     ffa data access and instruction access permission values are used in the memory access
     permissions descriptor (In Table 5.15: Memory access permissions descriptor). 
   *)

  (** There is a 1:1 association between an endpoint and the permissions with which it can access a memory region.
      This is specified in Table 5.15. *)
  
  (**
    Execute permission is more permissive than Execute-never permission. 
     - 5.11.3 Instruction access permissions usage 
     - Table 5.15: Memory access permissions descriptor 
  *)

  (** **** FFA Instruction Access Coq Definition *)    
  Inductive FFA_INSTRUCTION_ACCESS_TYPE :=
  | FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED
  | FFA_INSTRUCTION_ACCESS_NX
  | FFA_INSTRUCTION_ACCESS_X
  | FFA_INSTRUCTION_ACCESS_RESERVED.
  
  (**
    Read-write permission is more permissive than Read-only permission. 
     - 5.11.2 Data access permissions usage shows invariants about this fields 
   *)

  (** **** FFA Data Access Coq Definition *)    
  Inductive FFA_DATA_ACCESS_TYPE :=
  | FFA_DATA_ACCESS_NOT_SPECIFIED
  | FFA_DATA_ACCESS_RO
  | FFA_DATA_ACCESS_RW
  | FFA_DATA_ACCESS_RESERVED.

 (** FFA memory access permissions descriptor
     - [ffa_vm_id_t receiver;]: The ID of the VM to which the memory is being given or shared. 
     - [ffa_memory_access_permissions_t permissions;]: 
       The permissions with which the memory region should be mapped in the receiver's page table.       
     - [ffa_memory_receiver_flags_t flags;]:
       Flags used during FFA_MEM_RETRIEVE_REQ and FFA_MEM_RETRIEVE_RESP for memory regions with multiple borrowers.
  *)

  (**
   A composite memory region description is referenced by specifying an offset to it as described in Table 5.16.
   This enables one or more endpoints to be associated with the same memory region but with different memory
   access permissions for example, SP0 could have RO data access permission and SP1 could have RW data access
   permission to the same memory region.
   *)

  (** **** Order of instruction access and data access to check
      whether a is more permissive. 
      - It will return true if a is more permissive than b. 
      - It will return false in the following two cases.
        - When b is more permissive than a.
        - When a or b has an invalid value. 
          [JIEUNG: We can easily add option type when it is required later, but handling them
                   as false might be good at this moment] *)
  
  Definition instruction_access_permissive
             (a b: FFA_INSTRUCTION_ACCESS_TYPE) : bool :=
    match a, b with
    | FFA_INSTRUCTION_ACCESS_X, FFA_INSTRUCTION_ACCESS_X
    | FFA_INSTRUCTION_ACCESS_X, FFA_INSTRUCTION_ACCESS_NX
    | FFA_INSTRUCTION_ACCESS_NX, FFA_INSTRUCTION_ACCESS_NX => true
    | FFA_INSTRUCTION_ACCESS_NX, FFA_INSTRUCTION_ACCESS_X => false
    (** invalid pairs *)
    | _, _ => false
    end.

  Definition data_access_permissive (a b: FFA_DATA_ACCESS_TYPE) : bool :=
    match a, b with
    | FFA_DATA_ACCESS_RW, FFA_DATA_ACCESS_RW
    | FFA_DATA_ACCESS_RW, FFA_DATA_ACCESS_RO
    | FFA_DATA_ACCESS_RO, FFA_DATA_ACCESS_RO => true
    | FFA_DATA_ACCESS_RO, FFA_DATA_ACCESS_RW => false
    (** invalid pairs *)
    | _, _ => false
    end.

  
  (* Table 5.15: Memory access permissions descriptor 
     Field       Byte length   Byte offset            Description
     Endpoint    2             -                      - 16-bit ID of endpoint to which the memory access
     ID                                                 permissions apply. 
     Memory      1             2                      - Permissions used to access a memory region.
     access                                             – bits[7:4]: Reserved (MBZ).
     permissions                                        – bits[3:2]: Instruction access permission.
                                                          - b’00: Not specified and must be ignored.
                                                          - b’01: Not executable.
                                                          - b’10: Executable.
                                                          - b’11: Reserved. Must not be used.
                                                        – bits[1:0]: Data access permission.
                                                          - b’00: Not specified and must be ignored.
                                                          - b’01: Read-only.
                                                          - b’10: Read-write.
                                                          - b’11: Reserved. Must not be used.
     Flags       1             3                        - ABI specific flags as described in 5.11.1 ABI-specific 
                                                          flags usage.
   *)

  (** **** FFA Memory Access Permissions Descriptor Coq Definitoin *)
  Record FFA_memory_access_permissions_descriptor_struct :=
    mkFFA_memory_access_permissions_descriptor_struct {
        FFA_memory_access_permissions_descriptor_struct_receiver :
          (** - length: 2 bytes / offset: 0 bytes *)          
          ffa_UUID_t;
        (**
           - memory access permissions: length: 1 bytes / offset: 2 bytes
             - bits(7:4): Reserved (MBZ).
             - bits(3:2): Instruction access permission.
               - b00: Not specified and must be ignored.
               - b01: Not executable.
               - b10: Executable.
               - b11: Reserved. Must not be used.
             - bits(1:0): Data access permission.
               - b00: Not specified and must be ignored.
               - b01: Read-only.
               - b10: Read-write.
               - b11: Reserved. Must not be used. *)
        FFA_memory_access_permissions_descriptor_struct_permisions_instruction :
          FFA_INSTRUCTION_ACCESS_TYPE;
        FFA_memory_access_permissions_descriptor_struct_permisions_data :
          FFA_DATA_ACCESS_TYPE;
        (**
           - the flag value is only used for [FFA_MEM_RETRIEVE_REQ] and [FFA_MEM_RETRIEVE_RESP]. For 
             [FFA_MEM_DONATE], [FFA_MEM_LEND], and [FFA_MEM_SHARE], this field is empty. They need to be 
             enforced as invariants.

           - ABI-specific flags usage [JIEUNG: Check for the flag field is required]
           - An endpoint can specify properties specific to the memory management ABI being invoked through 
             this field. In this version of the Framework, the Flags field MBZ and is reserved in an 
             invocation of the following ABIs.
             - FFA_MEM_DONATE.
             - FFA_MEM_LEND.
             - FFA_MEM_SHARE.
           - The Flags field must be encoded by the Receiver and the Relayer as specified in Table 5.17 in an 
             invocation of the following ABIs.
             - FFA_MEM_RETRIEVE_REQ.
             - FFA_MEM_RETRIEVE_RESP.
           - The Relayer must return INVALID_PARAMETERS if the Flags field has been incorrectly encoded.

           - Table 5.17: Flags usage in FFA_MEM_RETRIEVE_REQ and FFA_MEM_RETRIEVE_RESP ABIs

           - Bit(0): Non-retrieval Borrower flag.
             - In a memory management transaction with multiple Borrowers, during the retrieval
               of the memory region, this flag specifies if the memory region must be or was
               retrieved on behalf of this endpoint or if the endpoint is another Borrower.
               - b0: Memory region must be or was retrieved on behalf of this endpoint.
               - b1: Memory region must not be or was not retrieved on behalf of this endpoint.
                 It is another Borrower of the memory region.
             - This field MBZ if this endpoint:
               - Is the only PE endpoint Borrower/Receiver in the transaction.
               - Is a Stream endpoint and the caller of the FFA_MEM_RETRIEVE_REQ ABI is
                 its proxy endpoint.
           - Bit(7:1) - Reserved (MBZ). *)
        FFA_memory_access_permissions_descriptor_struct_flags:
          ffa_memory_receiver_flags_t;
      }.
  
  Definition init_FFA_memory_access_permissions_descriptor_struct :=
    mkFFA_memory_access_permissions_descriptor_struct
      0 FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED
      FFA_DATA_ACCESS_NOT_SPECIFIED false.


  (** **** Well formed conditions *)  
  (** The call should return INVALID_PARAMETERS when the following is not satisfied *)
  Definition FFA_memory_access_permissions_descriptor_struct_flags_check
             (function_type : FFA_FUNCTION_TYPE)
             (descriptor: FFA_memory_access_permissions_descriptor_struct)
             (receiver_number: Z) :=
    match function_type with
    | FFA_MEM_DONATE
    | FFA_MEM_LEND
    | FFA_MEM_SHARE =>
      if (descriptor
          .(FFA_memory_access_permissions_descriptor_struct_flags))
      then Some (FFA_INVALID_PARAMETERS) else None
    | FFA_MEM_RETREIVE_REQ
    | FFA_MEM_RETREIVE_RESP =>
      if decide (receiver_number > 1) then  None
      else if (descriptor
               .(FFA_memory_access_permissions_descriptor_struct_flags))
           then Some (FFA_INVALID_PARAMETERS)
           else None
    (** - Don't care about this case *)
    | _ => None
    end.
  
  (**
     Table 5.16 specifies the data structure that is used in memory management transactions to create an association
     between an endpoint, memory access permissions and a composite memory region description.

     This data structure must be included in other data structures that are used in memory management transactions
     instead of being used as a stand alone data structure (see 5.12 Lend, donate, and share transaction descriptor).
     A composite memory region description is referenced by specifying an offset to it as described in Table 5.16.
     This enables one or more endpoints to be associated with the same memory region but with different memory
     access permissions for example, SP0 could have RO data access permission and SP1 could have RW data access
     permission to the same memory region. *)

  
  (** Table 5.16: Endpoint memory access descriptor 
      - [struct ffa_memory_region_attributes receiver_permissions;]: 
        Offset in bytes from the start of the outer [ffa_memory_region] to an [ffa_composite_memory_region] struct.
      - [uint32_t composite_memory_region_offset;]
      - [uint64_t reserved_0;]
   *)

  (* 
     Table 5.16: Endpoint memory access descriptor
     Field                       Byte length     Byte offset    Description
     Memory access               4               -              - Memory access permissions descriptor as
     permissions descriptor                                       specified in Table 5.15.
     Composite memory            4               4              - Offset to the composite memory region descriptor
     region descriptor offset                                     to which the endpoint access permissions apply
                                                                  (see Table 5.13).
                                                                - Offset must be calculated from the base address of
                                                                  the data structure this descriptor is included in.
                                                                - An offset value of 0 indicates that the endpoint
                                                                  access permissions apply to a memory region
                                                                  description identified by the Handle parameter
                                                                  specified in the data structure that includes this
                                                                  one.
     Reserved (MBZ)              8               8
     *)
  
  (** **** FFA Endpoint Memory Access Descriptor Coq Definitoin *)  
  Record FFA_endpoint_memory_access_descriptor_struct :=
    mkFFA_endpoint_memory_access_descriptor_struct {
        (** - length: 4 bytes / offset: 0 bytes *)        
        FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor :
          FFA_memory_access_permissions_descriptor_struct;
        
        (** - length: 4 bytes / offset: 4 bytes *)
        (** - It indicates one of constituents inside the composite_memory_region_struct to 
            retrieve specific memory region *)
        (** - 0 and 1 is used for the specific purpose in this offset 
              - 0 : points out this data structure 
              - 1 : points out the composite descriptor 
              - 2 : points out constituents that the composite descriptor holds
         *)
        FFA_memory_access_descriptor_struct_composite_memory_region_offset : nat;
        
        (** - memory region struct is created and destroyed when hypervisor starts/finishes 
            their handling. Instead of merging it into  
            
            - NOTE: the original size of the above offset value is as follows *)

        (** - Reserved (MBZ) - length: 8 bytes / offset: 8 bytes *)
      }.
  
  Definition init_FFA_endpoint_memory_access_descriptor_struct :=
    mkFFA_endpoint_memory_access_descriptor_struct
      init_FFA_memory_access_permissions_descriptor_struct 0.

  (** **** Well formed conditions *)  
  (** [JIEUNG: The error code is not defined when the following offset is not correct. 
      I will return INVALID_PARAMETER for this case] *)
  Definition well_formed_FFA_endpoint_memory_access_descriptor_struct
             (access_descriptor : FFA_endpoint_memory_access_descriptor_struct)
             (composite_descriptor : FFA_composite_memory_region_struct) :=
    let offset :=
        (access_descriptor
         .(FFA_memory_access_descriptor_struct_composite_memory_region_offset))%nat in
    if decide
         (((length (composite_descriptor
                    .(FFA_composite_memory_region_struct_constituents)) + 2)%nat >=
           offset)%nat)
    then true
    else false.
  
  (*******************************************************)
  (** *** 5.11.2 Data access permissions usage           *)
  (*******************************************************)
  (**
      An endpoint could have either Read-only or Read-write data access permission to a memory region from the
      highest Exception level it runs in.

      - Read-write permission is more permissive than Read-only permission.
      - Data access permission is specified by setting Bits(1:0) in Table 5.15 to the appropriate value

      This access control is used in memory management transactions as follows.

      [JIEUNG: We do not model the case when endpoints are independent peripheral device or
      they are in secure regime]
   *)

  (**
      Restrictions in lend or share memory:
      - The Lender must specify the level of access that the Borrower is permitted to have on the memory region.
        This is done while invoking the FFA_MEM_SHARE or FFA_MEM_LEND ABIs.
      - The Relayer must validate the permission specified by the Lender as follows. This is done in response
        to an invocation of the FFA_MEM_SHARE or FFA_MEM_LEND ABIs. The Relayer must return the
        DENIED error code if the validation fails.
        - At the Non-secure physical FF-A instance, an IMPLEMENTATION DEFINED mechanism is used to perform validation.
          - [JIEUNG: The above sentence is vague]
        - At any virtual FF-A instance, if the endpoint is running in EL1 or S-EL1 in either Execution state,
          the permission specified by the Lender is considered valid only if it is the same or less permissive
          than the permission used by the Relayer in the S2AP (RW permissions) field in the stage 2 translation 
          table descriptors for the memory region in one of the following translation regimes:
          - Secure EL1&0 translation regime, when S-EL2 is enabled.
          - Non-secure EL1&0 translation regime, when EL2 is enabled.
          - [JIEUNG: S2AP should be modeled - It is about read / write permissions]
        – At the Secure virtual FF-A instance, if the endpoint is running in S-EL0 in either Execution state,
          the permission specified by the Lender is considered valid only if it is the same or less permissive
          than the permission used by the Relayer in the AP(1) field in the stage 1 translation table descriptors
          for the memory region in one of the following translation regimes:
          - Secure EL1&0 translation regime, when EL2 is disabled.
          - Secure PL1&0 translation regime, when EL2 is disabled.
          - Secure EL2&0 translation regime, when Armv8.1-VHE is enabled.
          - [JIEUNG: AP in Stage 1 should be modeled - It is about read / write permissions]
          If the Borrower is an independent peripheral device, then the validated permission is used to map the
          memory region into the address space of the device.
        - The Borrower (if a PE or Proxy endpoint) should specify the level of access that it would like to have on
          the memory region.
          
          In a transaction to share or lend memory with more than one Borrower, 
          each Borrower (if a PE or Proxy endpoint) could also specify the level of access that other 
          Borrowers have on the memory region.
          
          This is done while invoking the FFA_MEM_RETRIEVE_REQ ABI.
        - The Relayer must validate the permissions, if specified by the Borrower (if a PE or Proxy endpoint) in
          response to an invocation of the FFA_MEM_RETRIEVE_REQ ABI.
          
          It must ensure that the permission of the Borrower is the same or less permissive than the permission
          that was specified by the Lender and validated by the Relayer.
          
          It must ensure that the permissions for other Borrowers are the same as those specified by the Lender
          and validated by the Relayer. The Relayer must return the DENIED error code if the validation fails.
   *)


  (**
     Restrictions in dontate memory: 
     - Whether the Owner is allowed to specify the level of access that the Receiver is permitted to have on the
       memory region depends on the type of Receiver.
       – If the Receiver is a PE or Proxy endpoint, the Owner must not specify the level of access.
       – If the Receiver is an independent peripheral device, the Owner could specify the level of access.
       The Owner must specify its choice in an invocation of the FFA_MEM_DONATE ABI.
     - The value of data access permission field specified by the Owner must be interpreted by the Relayer as
       follows. This is done in response to an invocation of the FFA_MEM_DONATE ABI.
       – If the Receiver is a PE or Proxy endpoint, the Relayer must return INVALID_PARAMETERS if the
         value is not b00.
       – If the Receiver is an independent peripheral device and the value is not b00, the Relayer must take
         one of the following actions.
         - Return DENIED if the permission is determined to be invalid through an IMPLEMENTATION DEFINED mechanism.
         - Use the permission specified by the Owner to map the memory region into the address space of the device.
       - If the Receiver is an independent peripheral device and the value is b00, the Relayer must determine
         the permission value through an IMPLEMENTATION DEFINED mechanism.
     - The Receiver (if a PE or Proxy endpoint) should specify the level of access that it would like to have on
       the memory region. This is done while invoking the FFA_MEM_RETRIEVE_REQ ABI.
     - The Relayer must validate the permission specified by the Receiver to ensure that it is the same or less
       permissive than the permission determined by the Relayer through an IMPLEMENTATION DEFINED
       mechanism. This is done in response to an invocation of the FFA_MEM_RETRIEVE_REQ ABI. The
       Relayer must return the DENIED error code if the validation fails.

      Restrictions in retrieve response:
      - The Relayer must specify the permission that was used to map the memory region in the translation regime
        of the Receiver or Borrower. This must be done in an invocation of the FFA_MEM_RETRIEVE_RESP ABI.

      Restrictions on reclaim:
      - In a transaction to relinquish memory that was lent to one or more Borrowers, the memory region must be
        mapped back into the translation regime of the Lender with the same data access permission that was used
        at the start of the transaction to lend the memory region. This is done in response to an invocation of the
        FFA_MEM_RECLAIM ABI.
      - [JIEUNG: We need a way to store the previous permissions] 
   *)

  (** **** Access permission checker *)
  (** Definitions to check access permissions.

      Summarized rules (LEND and SHARE) 
      - The Relayer must validate the permission specified by the Lender
      - the permission specified by the Lender is considered valid only if it is the same or less permissive
        than the permission used by the Relayer in the S2AP (RW permissions) field in the stage 2 translation 
        table descriptors for the memory region
      - the permission of the Borrower is the same or less permissive than the permission
        that was specified by the Lender and validated by the Relayer
        
      - [JIEUNG: It does not mention that when Relayer check the premissions of Borrowers. I assume it will be checked
        during retrieve] 

      Summarized rules (DONATE)
      - If the Receiver is a PE or Proxy endpoint, the Relayer must return INVALID_PARAMETERS if the
        value is not b00.
      - The Receiver (if a PE or Proxy endpoint) should specify the level of access that it would like to have on
        the memory region. This is done while invoking the FFA_MEM_RETRIEVE_REQ ABI.
      - The Relayer must validate the permission specified by the Receiver to ensure that it is the same or less
        permissive than the permission determined by the Relayer through an IMPLEMENTATION DEFINED
        mechanism. This is done in response to an invocation of the FFA_MEM_RETRIEVE_REQ ABI. The
        Relayer must return the DENIED error code if the validation fails.
   *)

  (** **** Well formed conditions *)
  (** I added the following checkers, but some of them may not be used due to the redundancy *)
  (** Returns DENIED, when it returns false *)
  Definition data_permissions_lend_and_share_lender_check
             (descriptor global lender: FFA_DATA_ACCESS_TYPE) :=
    if (data_access_permissive global descriptor &&
        data_access_permissive lender descriptor)
    then None else Some (FFA_DENIED).
        
  (** When it is not satisfied, the spec needs to return INVALID_PARAMETER *)
  (** Return INVALID_PARAMETER when it returns false *)
  Definition data_permissions_check_donate_lender_check
             (descriptor global lender: FFA_DATA_ACCESS_TYPE) :=
    match descriptor with
    | FFA_DATA_ACCESS_NOT_SPECIFIED =>
      if (data_access_permissive global descriptor &&
          data_access_permissive lender descriptor)
      then None else Some (FFA_INVALID_PARAMETERS)
    | _ => Some (FFA_INVALID_PARAMETERS)
    end.
  
  (** Return INVALID_PARAMETER when it returns false *)
  Definition data_permissions_borrower_check
             (global descriptor: FFA_DATA_ACCESS_TYPE) :=
    if (data_access_permissive global descriptor)
    then None
    else Some (FFA_INVALID_PARAMETERS).

  (** [JIEUNG: This does not specify which we have to store in resp.] *)

  (*******************************************************)
  (** *** 5.11.3 Instruction access permissions usage    *)
  (*******************************************************)
  (** [JIEUNG: The following things need to be implemented in the transition rules]

      An endpoint could have either Execute (X) or Execute-never (XN) instruction access permission to a memory
      region from the highest Exception level it runs in.
      - Execute permission is more permissive than Execute-never permission.
      - Instruction access permission is specified by setting Bits(3:2) in Table 5.15 to the appropriate value.
      This access control is used in memory management transactions as follows.

      - Only XN permission must be used in the following transactions.
         - In a transaction to share memory with one or more Borrowers.
         - In a transaction to lend memory to more than one Borrower.
         Bits(3:2) in Table 5.15 must be set to b00 as follows.
         - By the Lender in an invocation of FFA_MEM_SHARE or FFA_MEM_LEND ABIs.
         - By the Borrower in an invocation of the FFA_MEM_RETRIEVE_REQ ABI.
         The Relayer must set Bits(3:2) in Table 5.15 to b01 while invoking the FFA_MEM_RETRIEVE_RESP ABI.
   *)
  
  (** **** Well formed conditions *)
  (** [JIEUNG: it is not specified, but return INVALID_PARAMETER when it returns false] *)
  (** Return INVALID_PARAMETER when it is not specified *)
  Definition instruction_permissions_share_and_lend_multiple_borrower_lender_descriptor_check
             (global descriptor: FFA_INSTRUCTION_ACCESS_TYPE) :=
    match descriptor with
    | FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED =>
      if (instruction_access_permissive global descriptor)
      then None else Some (FFA_INVALID_PARAMETERS)
    | _  => Some (FFA_INVALID_PARAMETERS)
    end.

  (** [JIEUNG: it is not specified, but return DENIED when it returns false] *)
  (** Return DENIED when it is not specified *)
  Definition instruction_permissions_share_and_lend_multiple_borrower_lender_check
             (global lender: FFA_INSTRUCTION_ACCESS_TYPE) :=
    match lender with
    | FFA_INSTRUCTION_ACCESS_NX =>
      if instruction_access_permissive global lender
      then None else Some (FFA_DENIED)
    | _ => Some (FFA_DENIED)
    end.

  (** [JIEUNG: it is not specified, but return INVALID_PARAMETER when it returns false *)
  (** Return DENIED when it is not specified *)  
  Definition instruction_permissions_share_and_lend_multiple_borrower_borrower_descriptor_check
             (global descriptor: FFA_INSTRUCTION_ACCESS_TYPE) :=
    match descriptor with
    | FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED =>
      if (instruction_access_permissive global descriptor)
      then None else Some (FFA_DENIED)
    | _ => Some (FFA_DENIED)
    end.
  
  (** for resp's descriptor - FFA_MEM_SHARE and FFA_MEM_LEND for multiple borrowers *)
  (** Return INVALID_PARAMETER when it is not specified *)  
  Definition instruction_permissions_share_and_lend_multiple_borrower_resp_check
             (descriptor: FFA_INSTRUCTION_ACCESS_TYPE) :=
    match descriptor with
    | FFA_INSTRUCTION_ACCESS_NX => None
    | _ => Some (FFA_INVALID_PARAMETERS)
    end.

  (**
      - In a transaction to donate memory or lend memory to a single Borrower,
         - Whether the Owner/Lender is allowed to specify the level of access that the Receiver is permitted to
           have on the memory region depends on the type of Receiver.
           - If the Receiver is a PE or Proxy endpoint, the Owner must not specify the level of access.
           - If the Receiver is an independent peripheral device, the Owner could specify the level of access.
           The Owner must specify its choice in an invocation of the FFA_MEM_DONATE or FFA_MEM_LEND ABIs.
         - The value of instruction access permission field specified by the Owner/Lender must be interpreted   
           by the Relayer as follows. This is done in response to an invocation of the
           FFA_MEM_DONATE or FFA_MEM_LEND ABIs.
           - If the Receiver is a PE or Proxy endpoint, the Relayer must return INVALID_PARAMETERS if the 
             value is not b00.
           - If the Receiver is an independent peripheral device and the value is not b00, the Relayer must take 
             one of the following actions.
             - Return DENIED if the permission is determined to be invalid through an IMPLEMENTATION DEFINED mechanism.
             - Use the permission specified by the Owner to map the memory region into the address space of the device.
           - If the Receiver is an independent peripheral device and the value is b00, the Relayer must determine 
             the permission value through an IMPLEMENTATION DEFINED mechanism.
         - The Receiver (if a PE or Proxy endpoint) should specify the level of access that it would like to 
           have on the memory region. This must be done in an invocation of the FFA_MEM_RETRIEVE_REQ ABI.
         - The Relayer must validate the permission specified by the Receiver (if a PE or Proxy endpoint) to
           ensure that it is the same or less permissive than the permission determined by the Relayer through an       
           IMPLEMENTATION DEFINED mechanism.
           - For example, the Relayer could deny executable access to a Borrower on a memory region of Device
             memory type.
           This is done in response to an invocation of the FFA_MEM_RETRIEVE_REQ ABI. The Relayer must
           return the DENIED error code if the validation fails.

           If the invocation of FFA_MEM_RETRIEVE_REQ succeeds, the Relayer must set Bits(3:2) in Table
           5.15 to either b01 or b10 while invoking the FFA_MEM_RETRIEVE_RESP ABI.

      - In a transaction to relinquish memory that was lent to one or more Borrowers, the memory region must be
        mapped back into the translation regime of the Lender with the same instruction access permission that was
        used at the start of the transaction to lend the memory region. This is done in response to an 
        invocation of the FFA_MEM_RECLAIM ABI.
   *)

  (** **** Well formed conditions *)
  (** for borower's descriptor - FFA_MEM_DONATE and FFA_MEM_LEND for single borrowers *)
  (** Return INVALID_PARAMETER when it returns false *)
  Definition instruction_permissions_donate_and_lend_single_borrower_lender_descriptor_check
             (global descriptor: FFA_INSTRUCTION_ACCESS_TYPE) :=
    match descriptor with
    | FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED =>
      if (instruction_access_permissive global descriptor)
      then None else Some (FFA_INVALID_PARAMETERS)
    | _ => Some (FFA_INVALID_PARAMETERS)
    end.

  (** for borower's descriptor - FFA_MEM_DONATE and FFA_MEM_LEND for single borrowers *)
  (** Return DENIED when it returns false *)
  Definition instruction_permissions_donate_and_lend_single_borrower_lender_check
             (global lender: FFA_INSTRUCTION_ACCESS_TYPE) :=
    if (instruction_access_permissive global lender)
    then None else Some (FFA_DENIED).
  
  (** When it is not satisfied, the spec needs to return DENIED *)
  (** Return DENIED when it is not possible *)
  Definition instruction_permissions_donate_and_lend_single_borrower_borrower_descriptor_check
             (global descriptor: FFA_INSTRUCTION_ACCESS_TYPE) :=
    if (instruction_access_permissive global descriptor)
    then None else Some (FFA_DENIED).

  (** Return INVALID_PARAMETER when it is not possible *)
  Definition instruction_permissions_donate_and_lend_single_borrower_resp_check
             (global descriptor borrower: FFA_INSTRUCTION_ACCESS_TYPE) :=
    match borrower, descriptor with
    | FFA_INSTRUCTION_ACCESS_NX,
      FFA_INSTRUCTION_ACCESS_NX 
    | FFA_INSTRUCTION_ACCESS_X,
      FFA_INSTRUCTION_ACCESS_X =>
      if (instruction_access_permissive global borrower)
      then None else Some (FFA_INVALID_PARAMETERS)
    | _, _ => Some (FFA_INVALID_PARAMETERS)
    end.
  
  (*******************************************************)
  (** *** 5.11.4 Memory region attributes usage          *)
  (*******************************************************)
  (** Memory type : Device-nGnRnE < Device-nGnRE < Device-nGRE < Device-GRE < Normal.
      
      - Cacheability attribute : Non-cacheable < Write-Back Cacheable.
      - Shareability attribute : Non-Shareable < Inner Shareable < Outer shareable. *)
  (** 
      An endpoint can access a memory region by specifying attributes as follows.
      - Memory type. This could be Device or Normal. Device memory type could be one of the following types.
        - Device-nGnRnE.
        - Device-nGnRE.
        - Device-nGRE.
        - Device-GRE.
        The precedence rules for memory types are as follows. < should be read as is less permissive than.
        - Device-nGnRnE < Device-nGnRE < Device-nGRE < Device-GRE < Normal.
      - Cacheability attribute. This could be one of the following types.
        - Non-cacheable.
        - Write-Back Cacheable.
        These attributes are used to specify both inner and outer cacheability. The precedence rules are as follows.
        - Non-cacheable < Write-Back Cacheable.
      - Shareability attribute. This could be one of the following types.
        - Non-shareable.
        - Outer Shareable.
        - Inner Shareable.
        The precedence rules are as follows.
        - Non-Shareable < Inner Shareable < Outer shareable.

      Memory region attributes are specified by an endpoint by setting Bits[5:0] in Table 5.18 to appropriate values.
      The data structure to encode memory region attributes is specified in Table 5.18.
   *)

  Inductive FFA_MEMORY_CACHEABILITY_TYPE_1 :=
  | FFA_MEMORY_CACHE_RESERVED
  | FFA_MEMORY_CACHE_NON_CACHEABLE
  | FFA_MEMORY_CACHE_RESERVED_1
  | FFA_MEMORY_CACHE_WRITE_BACK.

  Inductive FFA_MEMORY_CACHEABILITY_TYPE_2 :=
  | FFA_MEMORY_DEV_NGNRNE
  | FFA_MEMORY_DEV_NGNRE
  | FFA_MEMORY_DEV_NGRE
  | FFA_MEMORY_DEV_GRE.

  Inductive FFA_MEMORY_SHAREABILITY :=
  | FFA_MEMORY_SHARE_NON_SHAREABLE
  | FFA_MEMORY_SHARE_RESERVED
  | FFA_MEMORY_OUTER_SHAREABLE
  | FFA_MEMORY_INNER_SHAREABLE.


  Definition FFA_MEMORY_CACHEABILITY_TYPE_1_permissive
             (a b: FFA_MEMORY_CACHEABILITY_TYPE_1) :=
    match a, b with
    | FFA_MEMORY_CACHE_WRITE_BACK,
      FFA_MEMORY_CACHE_WRITE_BACK
    | FFA_MEMORY_CACHE_WRITE_BACK,
      FFA_MEMORY_CACHE_NON_CACHEABLE
    | FFA_MEMORY_CACHE_NON_CACHEABLE,
      FFA_MEMORY_CACHE_NON_CACHEABLE => true
    | FFA_MEMORY_CACHE_NON_CACHEABLE,
      FFA_MEMORY_CACHE_WRITE_BACK => false
    | _, _ => false
    end.
                                                                       
  Definition FFA_MEMORY_CACHEABILITY_TYPE_2_permissive
             (a b: FFA_MEMORY_CACHEABILITY_TYPE_2) :=
    match a, b with
    | FFA_MEMORY_DEV_GRE, _ => true
    | FFA_MEMORY_DEV_NGRE,
      FFA_MEMORY_DEV_GRE => false
    | FFA_MEMORY_DEV_NGRE, _ => true
    | FFA_MEMORY_DEV_NGNRE,
      FFA_MEMORY_DEV_GRE
    | FFA_MEMORY_DEV_NGNRE,
      FFA_MEMORY_DEV_NGRE => false
    | FFA_MEMORY_DEV_NGNRE, _ => true
    | FFA_MEMORY_DEV_NGNRNE,
      FFA_MEMORY_DEV_NGNRNE => true
    | _, _ => false
    end.

  Definition FFA_MEMORY_SHAREABILITY_permissive
             (a b : FFA_MEMORY_SHAREABILITY) :=
    match a, b with
    | FFA_MEMORY_OUTER_SHAREABLE,
      FFA_MEMORY_SHARE_RESERVED => false
    | FFA_MEMORY_OUTER_SHAREABLE, _ => true
    | FFA_MEMORY_INNER_SHAREABLE,
      FFA_MEMORY_INNER_SHAREABLE
    | FFA_MEMORY_INNER_SHAREABLE,
      FFA_MEMORY_SHARE_NON_SHAREABLE => true
    | FFA_MEMORY_INNER_SHAREABLE, _ => false
    | FFA_MEMORY_SHARE_NON_SHAREABLE,
      FFA_MEMORY_SHARE_NON_SHAREABLE => true
    | _, _ => false
    end.
      
  Inductive FFA_MEMORY_TYPE :=
  | FFA_MEMORY_NOT_SPECIFIED_MEM
  | FFA_MEMORY_DEVICE_MEM
      (cacheability_type: FFA_MEMORY_CACHEABILITY_TYPE_2)
  | FFA_MEMORY_NORMAL_MEM
      (cacheability_type: FFA_MEMORY_CACHEABILITY_TYPE_1)
      (shareability_type: FFA_MEMORY_SHAREABILITY)
  | FFA_MEMORY_MEM_RESERVED.


  Definition FFA_MEMORY_TYPE_permissive
             (a b : FFA_MEMORY_TYPE) :=
    match a, b with
    | FFA_MEMORY_DEVICE_MEM cacheability_type_a,
      FFA_MEMORY_DEVICE_MEM cacheability_type_b
      => FFA_MEMORY_CACHEABILITY_TYPE_2_permissive
          cacheability_type_a cacheability_type_b
    | FFA_MEMORY_NORMAL_MEM
        cacheability_type_a shareability_type_a,
      FFA_MEMORY_NORMAL_MEM
        cacheability_type_b shareability_type_b =>
      FFA_MEMORY_CACHEABILITY_TYPE_1_permissive
        cacheability_type_a cacheability_type_b && 
      FFA_MEMORY_SHAREABILITY_permissive
        shareability_type_a shareability_type_b
    | _, _ => false
    end.

  (** **** FFA Memory Region Attributes Descriptor Coq definition *)
  Record FFA_memory_region_attributes_descriptor_struct :=
    mkFFA_memory_region_attributes_descriptor_struct {
        (** - bits(7:6): Reserved (MBZ).
            - bits(5:4): Memory type.
              - b00: Not specified and must be ignored.
              - b01: Device memory.
              - b10: Normal memory.
              - b11: Reserved. Must not be used.
            - bits(3:2):
              - Cacheability attribute if bit(5:4) = b10.
                - b00: Reserved. Must not be used.
                - b01: Non-cacheable.
                - b10: Reserved. Must not be used.
                - b11: Write-Back.
              - Device memory attributes if bit(5:4) = b01.
                - b00: Device-nGnRnE.
                - b01: Device-nGnRE.
                - b10: Device-nGRE.
                - b11: Device-GRE. 
            - bits(1:0):
              - Shareability attribute if bit(5:4) = b10.
                - b00: Non-shareable.
                - b01: Reserved. Must not be used.
                - b10: Outer Shareable.
                - b11: Inner Shareable.
              - Reserved & MBZ if bit(5:4) = b01. *)
        FFA_memory_region_attributes_descriptor_struct_memory_type :
          FFA_MEMORY_TYPE;
      }.

  Definition init_FFA_memory_region_attributes_descriptor_struct :=
    mkFFA_memory_region_attributes_descriptor_struct
      FFA_MEMORY_NOT_SPECIFIED_MEM.
  
  (** [JIEUNG: The following things need to be implemented in the transition rules] 
      
      Memory region attributes are used in memory management transactions as follows.

      - In a transaction to share memory with one or more Borrowers and to lend memory to more than one Borrower,
        - The Lender specifies the attributes that each Borrower must access the memory region with. This is
          done by invoking the FFA_MEM_SHARE or FFA_MEM_LEND ABIs. The same attributes are used for
          all Borrowers.
        - The Relayer validates the attributes specified by the Lender as follows. This is done in response to an
          invocation of the FFA_MEM_SHARE or FFA_MEM_LEND ABIs. The Relayer must return the DENIED
          error code if the validation fails.
          - At the Non-secure physical FF-A instance, an IMPLEMENTATION DEFINED mechanism is used.
          - At any virtual FF-A instance, if the endpoint is running in EL1 or S-EL1 in either Execution state,
            the attributes specified by the Lender are considered valid only if they are the same or less permissive
            than the attributes used by the Relayer in the stage 2 translation table descriptors for the memory
            region in one of the following translation regimes:
            - Secure EL1&0 translation regime, when S-EL2 is enabled.
            - Non-secure EL1&0 translation regime, when EL2 is enabled.
          - At the Secure virtual FF-A instance, if the endpoint is running in S-EL0 in either Execution state,
            the attributes specified by the Lender are considered valid only if they are either the same or less
            permissive than the attributes used by the Relayer in the stage 1 translation table descriptors for the
            memory region in one of the following translation regimes:
            - Secure EL1&0 translation regime, when EL2 is disabled.
            - Secure PL1&0 translation regime, when EL2 is disabled.
            - Secure EL2&0 translation regime, when Armv8.1-VHE is enabled.
          If the Borrower is an independent peripheral device, then the validated attributes are used to map the
          memory region into the address space of the device.
        - The Borrower (if a PE or Proxy endpoint) should specify the attributes that it would like to access the
          memory region with. This is done by invoking the FFA_MEM_RETRIEVE_REQ ABI.
        - The Relayer must validate the attributes specified by the Borrower (if a PE or Proxy endpoint) to ensure
          that they are the same or less permissive than the attributes that were specified by the Lender and
          validated by the Relayer. This is done in response to an invocation of the FFA_MEM_RETRIEVE_REQ
          ABI. The Relayer must return the DENIED error code if the validation fails.
   *)

  (** **** Well formed conditions *)
  (** Return DENIED when it is not satisfied *)
  Definition attributes_share_and_multiple_borrowers_lender_check
             (descriptor lender global : FFA_MEMORY_TYPE) :=
    if (FFA_MEMORY_TYPE_permissive lender descriptor &&
        FFA_MEMORY_TYPE_permissive global descriptor &&
        FFA_MEMORY_TYPE_permissive global lender)
    then None else Some (FFA_DENIED).
        
  (** Return DENIED when it is not satisfied *)
  Definition attributes_share_and_multiple_borrowers_borrower_check
             (descriptor global : FFA_MEMORY_TYPE) :=
    if (FFA_MEMORY_TYPE_permissive global descriptor)
    then None else Some (FFA_DENIED).
  
  (**
      - In a transaction to donate memory or lend memory to a single Borrower,
        - Whether the Owner/Lender is allowed to specify the memory region attributes that the Receiver must
          use to access the memory region depends on the type of Receiver.
          - If the Receiver is a PE or Proxy endpoint, the Owner must not specify the attributes.
          - If the Receiver is an independent peripheral device, the Owner could specify the attributes.
          The Owner must specify its choice in an invocation of the FFA_MEM_DONATE or FFA_MEM_LEND ABIs.
        - The values in the memory region attributes field specified by the Owner/Lender must be interpreted
          by the Relayer as follows. This is done in response to an invocation of the FFA_MEM_DONATE or
          FFA_MEM_LEND ABIs.
          - If the Receiver is a PE or Proxy endpoint, the Relayer must return INVALID_PARAMETERS if the
            value in bits(5:4) != b00.
          - If the Receiver is an independent peripheral device and the value is not b00, the Relayer must take
            one of the following actions.
            - Return DENIED if the attributes are determined to be invalid through an IMPLEMENTATION
              DEFINED mechanism.
            - Use the attributes specified by the Owner to map the memory region into the address space of the
              device.
          - If the Receiver is an independent peripheral device and the value is b00, the Relayer must determine
            the attributes through an IMPLEMENTATION DEFINED mechanism.
        - The Receiver (if a PE or Proxy endpoint) should specify the memory region attributes it would like to
          use to access the memory region. This is done while invoking the FFA_MEM_RETRIEVE_REQ ABI.
        - The Relayer must validate the attributes specified by the Receiver (if a PE or Proxy endpoint) to ensure
          that they are the same or less permissive than the attributes determined by the Relayer through an
          IMPLEMENTATION DEFINED mechanism.
      
          This is done in response to an invocation of the FFA_MEM_RETRIEVE_REQ ABI. The Relayer must
          return the DENIED error code if the validation fails.

        - The Relayer must specify the memory region attributes that were used to map the memory region
          in the translation regime of the Receiver or Borrower. This must be done while invoking the
          FFA_MEM_RETRIEVE_RESP ABI.
    
        - In a transaction to relinquish memory that was lent to one or more Borrowers, the memory region must be
          mapped back into the translation regime of the Lender with the same attributes that were used at the start of the
          transaction to lend the memory region. This is done in response to an invocation of the FFA_MEM_RECLAIM ABI.
   *)

  (** **** Well formed conditions *)  
  (** Return INVALID_PARAMETERS when it is not statisfied *)
  Definition attributes_donate_and_single_borrower_lender_check
             (descriptor lender global : FFA_MEMORY_TYPE) :=
    match descriptor with
    | FFA_MEMORY_NOT_SPECIFIED_MEM =>
      if (FFA_MEMORY_TYPE_permissive global lender)
      then None else Some (FFA_INVALID_PARAMETERS)
    | _ => Some (FFA_INVALID_PARAMETERS)
    end.
  
  (** Return DENIED when it is not statisfied *)
  Definition attributes_donate_and_single_borrower_borrower_check
             (descriptor global : FFA_MEMORY_TYPE) :=
    if (FFA_MEMORY_TYPE_permissive global descriptor)
    then None else Some (FFA_DENIED).
  
End FFA_DESCRIPTIONS.

(*************************************************************)
(** *          transaction descriptors                       *)
(*************************************************************)
Section FFA_MEMORY_REGION_DESCRIPTOR.

  Context `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}.
  (**************************************************************)
  (** **  5.12 Lend, donate, and share transaction descriptor   *)
  (**************************************************************)
  
  (***************************************************************)
  (** *** 5.12.4 Flags usage                                     *)
  (***************************************************************)

  (** This flag should be defined before defining [ffa_memory_region descriptor]

     - Flags are used to govern the behavior of a memory management transaction.

     - Usage of the Flags field in an invocation of the following ABIs is specified in Table 5.20.
        - FFA_MEM_DONATE.
        - FFA_MEM_LEND.
        - FFA_MEM_SHARE.
     - Usage of the Flags field in an invocation of the FFA_MEM_RETRIEVE_REQ ABI is specified in Table 5.21.
     - Usage of the Flags field in an invocation of the FFA_MEM_RETRIEVE_RESP ABI is specified in Table 5.22.
   *)

  (** **** Zero memory flag
      In some ABI invocations, the caller could set a 
      flag to request the Relayer to zero a memory region. To do this, the Relayer must:

       - Map the memory region in its translation regime once it is not mapped in the translation regime of any other 
       FF-A component.

       The caller must ensure that the memory region fulfills the size and alignment requirements listed in 2.7
       Memory granularity and alignment to allow the Relayer to map this memory region. It must discover these
       requirements by invoking the FFA_FEATURES interface with the function ID of the FFA_RXTX_MAP
       interface (see 8.2 FFA_FEATURES).
       
       The Relayer must return INVALID_PARAMETERS if the memory region does not meet these requirements.

       - Zero the memory region and perform cache maintenance such that the memory regions contents are coherent
         between any PE caches, system caches and system memory.
       - Unmap the memory region from its translation regime before it is mapped in the translation regime of any
         other FF-A component.
   *)

  (** [FFA_MEM_DONATE], [FFA_MEM_LEND], and [FFA_MEM_SHARE]
      
      Table 5.20: Flags usage in [FFA_MEM_DONATE], [FFA_MEM_LEND] and [FFA_MEM_SHARE] ABIs *)
  (* 
     Field      Description
     Bit(1)     - Operation time slicing flag.
                  - In an invocation of FFA_MEM_DONATE, FFA_MEM_LEND or
                    FFA_MEM_SHARE, this flag specifies if the Relayer can time slice this operation.
                    - b0: Relayer must not time slice this operation.
                    - b1: Relayer can time slice this operation.
                  – MBZ if the Relayer does not support time slicing of memory management
                    operations (see 12.2.3 Time slicing of memory management operations), else the
                    Relayer must return INVALID_PARAMETERS.
     Bit(31:2)  - Reserved (MBZ).
     *)


  (** **** FFA Mem Default Flags *)  
  Record FFA_mem_default_flags_struct :=
    mkFFA_mem_default_flags_struct {
        (** - Bit(0): Zero memory flag.
              - In an invocation of FFA_MEM_DONATE or FFA_MEM_LEND, this flag specifies
                if the memory region contents must be zeroed by the Relayer after the memory
                region has been unmapped from the translation regime of the Owner.
                - b0: Relayer must not zero the memory region contents.
                - b1: Relayer must zero the memory region contents.
              - MBZ in an invocation of FFA_MEM_SHARE, else the Relayer must return INVALID_PARAMETERS.
              - MBZ if the Owner has Read-only access to the memory region , else the Relayer must return DENIED. *)
        FFA_mem_default_flags_struct_zero_memory_flag: bool;
        (** - Bit(1): Operation time slicing flag.
              - In an invocation of FFA_MEM_DONATE, FFA_MEM_LEND or
                FFA_MEM_SHARE, this flag specifies if the Relayer can time slice this operation.
                - b0: Relayer must not time slice this operation.
                - b1: Relayer can time slice this operation.
              -  MBZ if the Relayer does not support time slicing of memory management
                 operations (see 12.2.3 Time slicing of memory management operations), else the
                 Relayer must return INVALID_PARAMETERS. *)
        FFA_mem_default_flags_struct_operation_time_slicing_flag: bool;
        (** - Bit(31:2): Reserved (MBZ). *)
      }.

  (** **** Well formed conditions *)  
  (** Return INVALID_PARAMETER or DENIED when it is not satisfied *)
  Definition check_FFA_mem_default_flags_struct_for_donate_and_lend
             (default_flag: FFA_mem_default_flags_struct)
             (data_access : FFA_DATA_ACCESS_TYPE)
             (time_slice_enabled : bool) :=
    let time_slice_check :=
        if default_flag.(FFA_mem_default_flags_struct_operation_time_slicing_flag)
        then true
        else if time_slice_enabled then false else true in
    if time_slice_check then
      if default_flag.(FFA_mem_default_flags_struct_zero_memory_flag)
      then match data_access with
           | FFA_DATA_ACCESS_RW => None
           | FFA_DATA_ACCESS_RO => Some (FFA_DENIED)
           | _ => Some (FFA_INVALID_PARAMETERS)
           end
      else None
    else Some (FFA_INVALID_PARAMETERS).
  
  (** Return INVALID_PARAMETER when it is not satisfied *)
  Definition check_FFA_mem_default_flags_struct_for_share
             (default_flag: FFA_mem_default_flags_struct)
             (time_slice_enabled : bool) :=
    let time_slice_check :=
        if default_flag.(FFA_mem_default_flags_struct_operation_time_slicing_flag)
        then true
        else if time_slice_enabled then false else true in
    if time_slice_check then
      if default_flag.(FFA_mem_default_flags_struct_zero_memory_flag)
      then Some (FFA_INVALID_PARAMETERS)
      else None
    else Some (FFA_INVALID_PARAMETERS).


  (** **** Well formed conditions for retrieve (when it is not using retrieve flags *)  
  (** Return INVALID_PARAMETER or DENIED when it is not satisfied *)
  Definition check_FFA_mem_default_flags_struct_for_donate_and_lend_retrieve
             (default_flag: FFA_mem_default_flags_struct)
             (time_slice_enabled : bool) :=
    let time_slice_check :=
        if default_flag.(FFA_mem_default_flags_struct_operation_time_slicing_flag)
        then true
        else if time_slice_enabled then false else true in
    if time_slice_check then None      
    else Some (FFA_INVALID_PARAMETERS).
  
  (** Return INVALID_PARAMETER when it is not satisfied *)
  Definition check_FFA_mem_default_flags_struct_for_share_retrieve
             (default_flag: FFA_mem_default_flags_struct)
             (time_slice_enabled : bool) :=
    let time_slice_check :=
        if default_flag.(FFA_mem_default_flags_struct_operation_time_slicing_flag)
        then true
        else if time_slice_enabled then false else true in
    if time_slice_check then
      if default_flag.(FFA_mem_default_flags_struct_zero_memory_flag)
      then Some (FFA_INVALID_PARAMETERS)
      else None
    else Some (FFA_INVALID_PARAMETERS).

  
  (** FFA_MEM_RETRIEVE_REQ 
      Table 5.21: Flags usage in FFA_MEM_RETRIEVE_REQ ABI *)
  (* 
     Field      Description
     Bit(0)     - Zero memory before retrieval flag.
                  - In an invocation of FFA_MEM_RETRIEVE_REQ, during a transaction to lend or
                    donate memory, this flag is used by the Receiver to specify whether the memory
                    region must be retrieved with or without zeroing its contents first.
                    - b0: Retrieve the memory region irrespective of whether the Sender requested
                      the Relayer to zero its contents prior to retrieval.
                    - b1: Retrieve the memory region only if the Sender requested the Relayer to
                      zero its contents prior to retrieval by setting the Bit[0] in Table 5.20).
                  - MBZ in a transaction to share a memory region, else the Relayer must return
                    INVALID_PARAMETER.
                  - If the Sender has Read-only access to the memory region and the Receiver sets
                    Bit(0), the Relayer must return DENIED.
                  - MBZ if the Receiver has previously retrieved this memory region, else the Relayer
                    must return INVALID_PARAMETERS (see 11.4.2 Support for multiple retrievals by
                    a Borrower).

     Bit(1)     - Operation time slicing flag.
                  - In an invocation of FFA_MEM_RETRIEVE_REQ, this flag specifies if the Relayer
                    can time slice this operation.
                    - b0: Relayer must not time slice this operation.
                    - b1: Relayer can time slice this operation.
                  - MBZ if the Relayer does not support time slicing of memory management
                    operations (see 12.2.3 Time slicing of memory management operations), else the
                    Relayer must return INVALID_PARAMETERS.


     Bit(2)     - Zero memory after relinquish flag.
                  - In an invocation of FFA_MEM_RETRIEVE_REQ, this flag specifies whether the
                    Relayer must zero the memory region contents after unmapping it from the
                    translation regime of the Borrower or if the Borrower crashes.
                    - b0: Relayer must not zero the memory region contents.
                    - b1: Relayer must zero the memory region contents.
                  - If the memory region is lent to multiple Borrowers, the Relayer must clear memory
                    region contents after unmapping it from the translation regime of each Borrower, if
                    any Borrower including the caller sets this flag.
                  - This flag could be overridden by the Receiver in an invocation of
                    FFA_MEM_RELINQUISH (see Flags field in Table 11.25).
                  - MBZ if the Receiver has Read-only access to the memory region, else the Relayer
                    must return DENIED. The Receiver could be a PE endpoint or a dependent
                    peripheral device.
                  – MBZ in a transaction to share a memory region, else the Relayer must return
                    INVALID_PARAMETER.

     Bit(4:3)   - Memory management transaction type flag.
                  - In an invocation of FFA_MEM_RETRIEVE_REQ, this flag is used by the Receiver
                    to either specify the memory management transaction it is participating in or indicate
                    that it will discover this information in the invocation of
                    FFA_MEM_RETRIEVE_RESP corresponding to this request.
                    - b00: Relayer must specify the transaction type in FFA_MEM_RETRIEVE_RESP.
                    - b01: Share memory transaction.
                    - b10: Lend memory transaction.
                    - b11: Donate memory transaction.
                  - Relayer must return INVALID_PARAMETERS if the transaction type specified by the
                    Receiver is not the same as that specified by the Sender for the memory region
                    identified by the Handle value specified in the transaction descriptor.

     Bit(9:5)   - Address range alignment hint.
                  - In an invocation of FFA_MEM_RETRIEVE_REQ, this flag is used by the Receiver
                    to specify the boundary, expressed as multiples of 4KB, to which the address ranges
                    allocated by the Relayer to map the memory region must be aligned.
                  - Bit(9): Hint valid flag.
                    - b0: Relayer must choose the alignment boundary. Bits[8:5] are reserved and MBZ.
                    - b1: Relayer must use the alignment boundary specified in Bits[8:5].
                  – Bit(8:5): Alignment hint.
                  - If the value in this field is n, then the address ranges must be aligned to the 2*n
                    x 4KB boundary.
                  - MBZ if the Receiver specifies the IPA or VA address ranges that must be used by the
                    Relayer to map the memory region, else the Relayer must return
                    INVALID_PARAMETERS.
                  – Relayer must return DENIED if it is not possible to allocate the address ranges at the
                    alignment boundary specified by the Receiver.
                  – Relayer must return INVALID_PARAMETERS if a reserved value is specified by the
                    Receiver.

     Bit(31:10) - Reserved (MBZ)
   *)

  Inductive FFA_memory_management_transaction_type :=
  | MEMORY_MANAGEMENT_DEFAULT_TRANSACTION
  | MEMORY_MANAGEMENT_SHARE_TRANSACTION
  | MEMORY_MANAGEMENT_LEND_TRANSACTION
  | MEMORY_MANAGEMENT_DONATE_TRANSACTION.

  (** **** FFA Mem Relinquish Req Flags Coq Definition *)
  Record FFA_mem_relinquish_req_flags_struct :=
    mkFFA_mem_relinquish_req_flags_struct {
        (** - Bit(0): Zero memory before retrieval flag.
              – In an invocation of FFA_MEM_RETRIEVE_REQ, during a transaction to lend or donate memory, 
                this flag is used by the Receiver to specify whether the memory
                region must be retrieved with or without zeroing its contents first.
                - b0: Retrieve the memory region irrespective of whether the Sender requested
                  the Relayer to zero its contents prior to retrieval.
                - b1: Retrieve the memory region only if the Sender requested the Relayer to
                  zero its contents prior to retrieval by setting the Bit[0] in Table 5.20).
              - MBZ in a transaction to share a memory region, else the Relayer must return
                INVALID_PARAMETER.
              - If the Sender has Read-only access to the memory region and the Receiver sets
                Bit(0), the Relayer must return DENIED.
              - MBZ if the Receiver has previously retrieved this memory region, else the Relayer
                must return INVALID_PARAMETERS (see 11.4.2 Support for multiple retrievals by
                a Borrower). *)
        FFA_mem_relinquish_req_flags_struct_zero_memory_before_retrieval_flag:
          bool;
        (** - Bit(1): Operation time slicing flag.
              – In an invocation of FFA_MEM_RETRIEVE_REQ, this flag specifies if the Relayer can time slice this operation.
                - b0: Relayer must not time slice this operation.
                - b1: Relayer can time slice this operation.
              - MBZ if the Relayer does not support time slicing of memory management
                operations (see 12.2.3 Time slicing of memory management operations), else the
                Relayer must return INVALID_PARAMETERS. *)
        FFA_mem_relinquish_req_flags_struct_operation_time_slicing_flag: bool;
        (** [JIEUNG: This one has to be reflected in our spec]
            - Bit(2): Zero memory after relinquish flag.
              – In an invocation of FFA_MEM_RETRIEVE_REQ, this flag specifies whether the Relayer must zero the memory 
                region contents after unmapping it from the translation regime of the Borrower or if the Borrower crashes.
                - b0: Relayer must not zero the memory region contents.
                - b1: Relayer must zero the memory region contents.
              – If the memory region is lent to multiple Borrowers, the Relayer must clear memory region contents after 
                unmapping it from the translation regime of each Borrower, if any Borrower including the caller sets this flag.
              – This flag could be overridden by the Receiver in an invocation of FFA_MEM_RELINQUISH
                (see Flags field in Table 11.25).
              - MBZ if the Receiver has Read-only access to the memory region, else the Relayer must return DENIED. 
                The Receiver could be a PE endpoint or a dependent peripheral device.
              - MBZ in a transaction to share a memory region, else the Relayer must return
                INVALID_PARAMETER. *)
        FFA_mem_relinquish_req_flags_struct_zero_memory_after_retrieval_flag: bool;
        (** [JIEUNG: This one has to be reflected in our spec]
            - Bit(4:3): Memory management transaction type flag.
               – In an invocation of FFA_MEM_RETRIEVE_REQ, this flag is used by the Receiver
                 to either specify the memory management transaction it is participating in or indicate
                 that it will discover this information in the invocation of
                 FFA_MEM_RETRIEVE_RESP corresponding to this request.
                 - b00: Relayer must specify the transaction type in FFA_MEM_RETRIEVE_RESP.
                 - b01: Share memory transaction.
                 - b10: Lend memory transaction.
                 - b11: Donate memory transaction.
               - Relayer must return INVALID_PARAMETERS if the transaction type specified by the
                 Receiver is not the same as that specified by the Sender for the memory region
                 identified by the Handle value specified in the transaction descriptor. *)
        FFA_mem_relinquish_req_flags_struct_memory_management_transaction_type_flag:
          FFA_memory_management_transaction_type;
        (** - Bit(9:5): Address range alignment hint.
              – In an invocation of FFA_MEM_RETRIEVE_REQ, this flag is used by the Receiver to specify the boundary, 
                expressed as multiples of 4KB, to which the address ranges
                allocated by the Relayer to map the memory region must be aligned.
              – Bit(9): Hint valid flag.
                - b0: Relayer must choose the alignment boundary. Bits[8:5] are reserved and MBZ.
                - b1: Relayer must use the alignment boundary specified in Bits(8:5).
              - Bit(8:5): Alignment hint.
                - If the value in this field is n, then the address ranges must be aligned to the 2*n x 4KB boundary.
              - MBZ if the Receiver specifies the IPA or VA address ranges that must be used by the
                Relayer to map the memory region, else the Relayer must return
                INVALID_PARAMETERS.
              - Relayer must return DENIED if it is not possible to allocate the address ranges at the
                alignment boundary specified by the Receiver.
              - Relayer must return INVALID_PARAMETERS if a reserved value is specified by the Receiver. *)
        FFA_mem_relinquish_req_flags_struct_address_range_alignment_hint:
          (bool (* Bit(9) *) * Z (* Bit(8:5) *) )%type;
        (** - Bit[31:10] - Reserved (MBZ) *)
      }.

  Definition init_FFA_mem_relinquish_req_flags_struct :=
    mkFFA_mem_relinquish_req_flags_struct
      false false false
      MEMORY_MANAGEMENT_DEFAULT_TRANSACTION
      (false, 0).

  
  (** **** Well formed conditions *)
  (** Return INVALID_PARAMETER or DENIED if it is not satisfied *)
  Definition FFA_mem_relinquish_req_zero_flags_for_donate_and_lend_check
             (relinquish_flag: FFA_mem_relinquish_req_flags_struct)
             (sender_data_access : FFA_DATA_ACCESS_TYPE)
             (time_slice_enabled : bool) :=
    let time_slice_check :=
        if relinquish_flag
           .(FFA_mem_relinquish_req_flags_struct_operation_time_slicing_flag)
        then true
        else if time_slice_enabled then false else true in
    if time_slice_check then
      if relinquish_flag
         .(FFA_mem_relinquish_req_flags_struct_zero_memory_before_retrieval_flag)
      then match sender_data_access with
           | FFA_DATA_ACCESS_RW => None
           | FFA_DATA_ACCESS_RO => Some (FFA_DENIED)
           | _ => Some (FFA_INVALID_PARAMETERS)
           end
      else None
    else Some (FFA_INVALID_PARAMETERS).

  (** Return INVALID_PARAMETER or DENIED if it is not satisfied *)
  Definition FFA_mem_relinquish_req_zero_after_flags_for_donate_and_lend_check
             (relinquish_flag: FFA_mem_relinquish_req_flags_struct)
             (receiver_data_access : FFA_DATA_ACCESS_TYPE) :=
    if relinquish_flag
       .(FFA_mem_relinquish_req_flags_struct_zero_memory_after_retrieval_flag)
    then match receiver_data_access with
         | FFA_DATA_ACCESS_RW => None
         | FFA_DATA_ACCESS_RO => Some (FFA_DENIED)
         | _ => Some (FFA_INVALID_PARAMETERS)
         end
    else None.
  
  (** Return INVALID_PARAMETER if it is not satisfied *)
  Definition FFA_mem_relinquish_req_zero_flags_for_share_check
             (relinquish_flag: FFA_mem_relinquish_req_flags_struct) :=
    if relinquish_flag
       .(FFA_mem_relinquish_req_flags_struct_zero_memory_after_retrieval_flag)
    then Some (FFA_INVALID_PARAMETERS)
    else None.

  (** Return INVALID_PARAMETER if it is not satisfied *)
  Definition FFA_mem_relinquish_req_zero_after_flags_for_share_check 
             (relinquish_flag: FFA_mem_relinquish_req_flags_struct) :=
    if relinquish_flag
       .(FFA_mem_relinquish_req_flags_struct_zero_memory_after_retrieval_flag)
    then Some (FFA_INVALID_PARAMETERS)
    else None.
      

  (** Return INVALID_PARAMETER if it is not satisfied *)
  Definition FFA_mem_relinquish_req_transaction_type_check 
             (relinquish_flag: FFA_mem_relinquish_req_flags_struct)
             (function_type : option FFA_FUNCTION_TYPE) :=
    match relinquish_flag
          .(FFA_mem_relinquish_req_flags_struct_memory_management_transaction_type_flag) with
    | MEMORY_MANAGEMENT_DEFAULT_TRANSACTION =>
      match function_type with
      | None => None
      | _ => Some (FFA_INVALID_PARAMETERS)
      end
    | MEMORY_MANAGEMENT_SHARE_TRANSACTION =>
      match function_type with
      | Some FFA_MEM_SHARE => None
      | _ => Some (FFA_INVALID_PARAMETERS)
      end        
    | MEMORY_MANAGEMENT_LEND_TRANSACTION =>
      match function_type with
      | Some FFA_MEM_LEND => None
      | _ => Some (FFA_INVALID_PARAMETERS)
      end        
    | MEMORY_MANAGEMENT_DONATE_TRANSACTION =>
      match function_type with
      | Some FFA_MEM_DONATE => None
      | _ => Some (FFA_INVALID_PARAMETERS)
      end        
    end.
  
  (** Return DENIED if it is not satisfied *)
  (** - Relayer must return INVALID_PARAMETERS if a reserved value is specified by the Receiver.
        [JIEUNG: This one needs to be dealt in the transition rules] *)
  Definition FFA_mem_relinquish_req_alignment_hint_check
             (relinquish_flag: FFA_mem_relinquish_req_flags_struct)
             (address : Z) :=
    if fst (relinquish_flag
            .(FFA_mem_relinquish_req_flags_struct_address_range_alignment_hint))
    then let alignment :=
             snd (relinquish_flag
                  .(FFA_mem_relinquish_req_flags_struct_address_range_alignment_hint)) in
         if (decide (0 = Z.modulo address (Z.mul 2 (Z.mul alignment 4096))))
         then None else Some (FFA_DENIED)
    else Some (FFA_DENIED).

  (** FFA_MEM_RETRIEVE_RESP
      Table 5.22: Flags usage in FFA_MEM_RETRIEVE_RESP ABI *)
  (*
    Field       Description
    Bit(0)      - Zero memory before retrieval flag.
                  - In an invocation of FFA_MEM_RETRIEVE_RESP during a transaction to lend or
                    donate memory, this flag is used by the Relayer to specify whether the memory
                    region was retrieved with or without zeroing its contents first.
                    - b0: Memory region was retrieved without zeroing its contents.
                    - b1: Memory region was retrieved after zeroing its contents.
                  - MBZ in a transaction to share a memory region.
                  - MBZ if the Sender has Read-only access to the memory region.
    Bit(2:1)    - Reserved (MBZ).
    Bit(4:3)    - Memory management transaction type flag.
                  - In an invocation of FFA_MEM_RETRIEVE_RESP, this flag is used by the Relayer
                    to specify the memory management transaction the Receiver is participating in.
                    - b00: Reserved.
                    - b01: Share memory transaction.
                    - b10: Lend memory transaction.
                    - b11: Donate memory transaction.
    Bit(31:5)   - Reserved (MBZ).
   *)
  
  (** **** FFA Mem Relinquish Resp Flags Coq Definition *)
  Record FFA_mem_relinquish_resp_flags_struct :=
    mkFFA_mem_relinquish_resp_flags_struct {
        (** - Bit(0): Zero memory before retrieval flag.
            - In an invocation of FFA_MEM_RETRIEVE_RESP during a transaction to lend or
              donate memory, this flag is used by the Relayer to specify whether the memory
              region was retrieved with or without zeroing its contents first.
              - b0: Memory region was retrieved without zeroing its contents.
              - b1: Memory region was retrieved after zeroing its contents.
            - MBZ in a transaction to share a memory region.
            - MBZ if the Sender has Read-only access to the memory region. *)
        zero_memory_before_retrieval_flag_in_FFA_mem_relinquish_resp_flags_struct:
          bool;
        (** - Bit(2:1) - Reserved (MBZ). 

            - Bit(4:3): Memory management transaction type flag.
              – In an invocation of FFA_MEM_RETRIEVE_RESP, this flag is used by the Relayer
                to specify the memory management transaction the Receiver is participating in.
                - b00: Reserved.
                - b01: Share memory transaction.
                - b10: Lend memory transaction.
                - b11: Donate memory transaction.
            *)
        memory_management_transaction_type_flag_in_FFA_mem_relinquish_resp_flags_struct:
          FFA_memory_management_transaction_type;        
        (** - Bit(31:5) - Reserved (MBZ). *)
      }.

  (** **** Well formed conditions *)
  (** [JIEUNG: The return value is not specified, but I will follow the rule that
      previous flag checks use *)
  (** Return INVALID_PARAMETER or DENIED if it is not satisfied *)
  Definition check_FFA_mem_relinquish_resp_flags_for_donate_and_lend
             (relinquish_resp_flag: FFA_mem_relinquish_resp_flags_struct)
             (sender_data_access : FFA_DATA_ACCESS_TYPE) :=
    if relinquish_resp_flag
       .(zero_memory_before_retrieval_flag_in_FFA_mem_relinquish_resp_flags_struct)
    then match sender_data_access with
         | FFA_DATA_ACCESS_RW => None
         | FFA_DATA_ACCESS_RO => Some (FFA_DENIED)
         | _ => Some (FFA_INVALID_PARAMETERS)
         end
    else None.

  (** Return INVALID_PARAMETER if it is not satisfied *)
  Definition check_FFA_mem_relinquish_resp_flags_for_share
             (relinquish_resp_flag: FFA_mem_relinquish_resp_flags_struct) :=
    if relinquish_resp_flag
       .(zero_memory_before_retrieval_flag_in_FFA_mem_relinquish_resp_flags_struct)
    then Some (FFA_INVALID_PARAMETERS)
    else None.

  (** Return INVALID_PARAMETER if it is not satisfied *)
  Definition FFA_mem_relinquish_resp_transaction_type_check 
             (relinquish_resp_flag: FFA_mem_relinquish_resp_flags_struct)
             (function_type : option FFA_FUNCTION_TYPE) :=
    match relinquish_resp_flag
          .(memory_management_transaction_type_flag_in_FFA_mem_relinquish_resp_flags_struct) with
    | MEMORY_MANAGEMENT_DEFAULT_TRANSACTION =>
      match function_type with
      | None => None
      | _ => Some (FFA_INVALID_PARAMETERS)
      end
    | MEMORY_MANAGEMENT_SHARE_TRANSACTION =>
      match function_type with
      | Some FFA_MEM_SHARE => None
      | _ => Some (FFA_INVALID_PARAMETERS)
      end        
    | MEMORY_MANAGEMENT_LEND_TRANSACTION =>
      match function_type with
      | Some FFA_MEM_LEND => None
      | _ => Some (FFA_INVALID_PARAMETERS)
      end        
    | MEMORY_MANAGEMENT_DONATE_TRANSACTION =>
      match function_type with
      | Some FFA_MEM_DONATE => None
      | _ => Some (FFA_INVALID_PARAMETERS)
      end        
    end.  

  Definition init_FFA_mem_relinquish_resp_flags_struct :=
    mkFFA_mem_relinquish_resp_flags_struct
      false
      MEMORY_MANAGEMENT_DEFAULT_TRANSACTION.

  (** **** FFA Mem Region Flags Coq Definition *)  
  Inductive ffa_memory_region_flags_t :=
  | MEMORY_REGION_FLAG_DEFAULT
  | MEMORY_REGION_FLAG_NORMAL
      (flag: FFA_mem_default_flags_struct)
  | MEMORY_REGION_FLAG_RELINQUISH_REQ
      (flag: FFA_mem_relinquish_req_flags_struct)
  | MEMORY_REGION_FLAG_RELINQUISH_RESP
      (flag: FFA_mem_relinquish_resp_flags_struct).
  
  (** The following descriptor specifies the data structure that must be used by the 
      Owner/Lender and a Borrower/Receiver in a transaction to donate, lend or share a memory region. 
      It specifies the memory region description (see 5.10 Memory region description), 
      properties (see 5.11 Memory region properties) and other transaction attributes in an
      invocation of the following ABIs.
      - [FFA_MEM_DONATE]
      - [FFA_MEM_LEND]
      - [FFA_MEM_SHARE]
      - [FFA_MEM_RETRIEVE_REQ]
      - [FFA_MEM_RETRIEVE_RESP]

      The interpretation of some fields in Table 5.19 depends on the ABI this table is used with. This variance in
      behavior is also specified in Table 5.19.
   *)

  (**************************************************************************)
  (** **  Table 5.19: Lend, donate or share memory transaction descriptor   *)
  (**************************************************************************)
  (** Table 5.19: Lend, donate or share memory transaction descriptor *)
  (** Note that it is also used for retrieve requests and responses. The ID of the VM which originally sent the memory region, i.e. the  owner.
      - [ffa_vm_id_t sender;]
      - [ffa_memory_attributes_t attributes;]: 5.11.4 Memory region attributes usage.
      - [uint8_t reserved_0;]: Reserved field, must be 0. Flags to control behaviour of the transaction.
      - [ffa_memory_region_flags_t flags;]
      - [ffa_memory_handle_t handle;]: An implementation defined value associated with the receiver and the memory region.
      - [uint64_t tag;]: Reserved field, must be 0.
      - [uint32_t reserved_1;]: The number of `ffa_memory_access` entries included in this transaction.
      - [uint32_t receiver_count;]: An array of `attribute_count` endpoint memory access descriptors.
        Each one specifies a memory region offset, an endpoint and the
        attributes with which this memory region should be mapped in that
        endpoint's page table.
      - [struct ffa_memory_access receivers[];]
   *)
  (* 
     Field              Byte length     Byte offset     Description
     Sender endpoint ID 2               0               - ID of the Owner endpoint.
     Memory region      1               2               - Attributes must be encoded as specified in 5.11.4
     attributes                                           Memory region attributes usage.
                                                        - Attribute usage is subject to validation at the
                                                          virtual and physical FF-A instances as specified in
                                                          5.11.4 Memory region attributes usage.
     Reserved (MBZ)     1               3
     Flags              4               4               - Flags must be encoded as specified in in 5.12.4
                                                          Flags usage.
     Handle             8               8               - Memory region handle in ABI invocations
                                                          specified in 5.12.1 Handle usage.
     Tag                8               16              - This field must be encoded as specified in 5.12.2
                                                          Tag usage.
     Reserved (MBZ)     4               24
     Endpoint memory    4               28              - Count of endpoint memory access descriptors.
     access descriptor 
     count
     Endpoint memory    –               32              - Each entry in the array must be encoded as
     access descriptor                                    specified in 5.12.3 Endpoint memory access
     array                                                descriptor array usage. See Table 5.16 for the
                                                          encoding of the endpoint memory access
                                                          descriptor.
   *)

  (** **** FFA Memory Region Coq Definition *)
  Record FFA_memory_region_struct :=
    mkFFA_memory_region_struct {
        (** - length: 2 bytes / offset: 0 bytes *)        
        FFA_memory_region_struct_sender : ffa_UUID_t;
        (** - length: 1 bytes / offset: 2 bytes *)
        FFA_memory_region_struct_attributes :
          FFA_memory_region_attributes_descriptor_struct;
        (** - length: 1 bytes / offset: 3 bytes (Reserved (MBZ)) *)
        FFA_memory_region_struct_flags : ffa_memory_region_flags_t;
        (** [JIEUNG: The following two things has to be handled in the specification] *)
        (** - length: 8 bytes / offset: 8 bytes
           
            - length: 4 bytes / offset: 4 bytes
            - This field must be zero (MBZ) in an invocation of the following ABIs.
              - FFA_MEM_DONATE.
              - FFA_MEM_LEND.
              - FFA_MEM_SHARE.
              A successful invocation of each of the preceding ABIs returns a Handle (see 5.10.2 Memory region handle)
              to identify the memory region in the transaction.
            - The Sender must convey the Handle to the Receiver through a Partition message.
            - This field must be used by the Receiver to encode this Handle in an invocation of the FFA_MEM_RETRIEVE_REQ
              ABI.
            - A Relayer must validate this field in an invocation of the FFA_MEM_RETRIEVE_REQ ABI as follows.
              – Ensure that it holds a Handle value that was previously allocated and has not been reclaimed by the
                Owner.
              – Ensure that the Handle identifies a memory region that was shared, lent or donated to the Receiver.
              – Ensure that the Handle was allocated to the Owner specified in the Sender endpoint ID field of the
                transaction descriptor.
                It must return INVALID_PARAMETERS if the validation fails.
            - This field must be used by the Relayer to encode the Handle in an invocation of the FFA_MEM_RETRIEVE_RESP
              ABI.
         *)
        FFA_memory_region_struct_handle : ffa_memory_handle_t;
        (** - length : 8 bytes / offset 16 bytes

            - This 64-bit field must be used to specify an IMPLEMENTATION DEFINED value associated with the transaction
              and known to participating endpoints.
            - The Sender must specify this field to the Relayer in an invocation of the following ABIs.
              - FFA_MEM_DONATE.
              - FFA_MEM_LEND.
              - FFA_MEM_SHARE.
            - The Sender must convey the Tag to the Receiver through a Partition message.
            - This field must be used by the Receiver to encode the Tag in an invocation of the FFA_MEM_RETRIEVE_REQ
              ABI.
            - The Relayer must ensure the Tag value specified by the Receiver is equal to the value that was specified by
              the Sender. It must return INVALID_PARAMETERS if the validation fails.
            - This field must be used by the Relayer to encode the Tag value in an invocation of the FFA_MEM_RETRIEVE_RESP
              ABI.
        *)
        FFA_memory_region_struct_tag : ffa_memory_region_tag_t; 
        (** - length: 4 bytes / offset: 24 bytes (Reserved (MBZ))

            - length: 4 bytes / offset: 28 bytes
              - FFA_memory_region_struct_receiver_count : Z;
              - we ignored this by representing receivers as a list

            - length: FFA_memory_region_struct_receiver_count * 16 bytes / offset: 32 bytes *)
        FFA_memory_region_struct_receivers :
          list FFA_endpoint_memory_access_descriptor_struct;


        (** - This one is not actually mentioned in the document, and it is stored in
              different locations. However, we included this one in the region descriptor 
              for simplification at this moment *)
        FFA_memory_region_struct_composite:
          FFA_composite_memory_region_struct;
      }.

  Definition init_FFA_memory_region_struct :=
    mkFFA_memory_region_struct
      0 init_FFA_memory_region_attributes_descriptor_struct
      MEMORY_REGION_FLAG_DEFAULT 0 init_ffa_memory_region_tag nil init_FFA_composite_memory_region_struct.

  (** **** well formed conditions *)
  Fixpoint well_formed_FFA_memory_region_struct_receivers
           (access_descriptors:
              list FFA_endpoint_memory_access_descriptor_struct)
           (composite_descriptors:
              FFA_composite_memory_region_struct) :=
    match access_descriptors with
    | nil => true
    | hd::tl =>
      well_formed_FFA_endpoint_memory_access_descriptor_struct
        hd composite_descriptors &&
      well_formed_FFA_memory_region_struct_receivers
        tl composite_descriptors
    end.

  Definition FFA_memory_region_receivers_number_donate_check
             (ffa_memory_region: FFA_memory_region_struct) :=
    if decide ((length ffa_memory_region
                .(FFA_memory_region_struct_receivers) = 1)%nat)
    then true
    else false.

  Definition FFA_memory_region_receivers_number_lend_and_share_check
             (ffa_memory_region: FFA_memory_region_struct) :=
    if decide ((length ffa_memory_region
                .(FFA_memory_region_struct_receivers) > 0)%nat)
    then true
    else false.


  (** Return INVALID_PARAMETERS when it is not satisfied *)
  (** - For Tag, the following thing is not captured in our well-formed conditions 
        - The Relayer must ensure the Tag value specified by the Receiver is equal to the value that was specified by
          the Sender. It must return INVALID_PARAMETERS if the validation fails. *)
  (** - For offset, the following thing is not captured in our well-formed conditions (in terms of Receiver's view)
        - The value 0 must be specified in the Offset field of the corresponding endpoint memory access descriptor in the
          array. This implies that the Handle specified in Table 5.19 must be used to identify the memory region (see 5.12.1
          Handle usage) *)
  Definition well_formed_FFA_memory_region_struct (sender: ffa_UUID_t)
             (memory_region : FFA_memory_region_struct)
             (function_type : FFA_FUNCTION_TYPE) :=
    let handle_value_check :=
        if decide (memory_region.(FFA_memory_region_struct_handle) = 0)
        then true else false in
    let handle_value_and_receiver_num_check :=
        match function_type with
        | FFA_MEM_DONATE =>
          FFA_memory_region_receivers_number_donate_check
            memory_region && handle_value_check 
        | FFA_MEM_LEND
        | FFA_MEM_SHARE =>
          FFA_memory_region_receivers_number_lend_and_share_check
            memory_region &&
          handle_value_check 
          (** - [JIEUNG: We can think about adding more constraints in here] *)
        | _ => true
        end
    in
    if handle_value_check then
      if decide (sender = memory_region.(FFA_memory_region_struct_sender)) 
      then if (well_formed_FFA_memory_region_struct_receivers
                 (memory_region.(FFA_memory_region_struct_receivers))
                 (memory_region.(FFA_memory_region_struct_composite)))
           then None else Some (FFA_INVALID_PARAMETERS)
      else  Some (FFA_INVALID_PARAMETERS)
    else Some (FFA_INVALID_PARAMETERS).

  
  (*************************************************************************)
  (** **           Handle Usage                                            *)
  (*************************************************************************)
  (** 
      - This field must be zero (MBZ) in an invocation of the following ABIs.
        - FFA_MEM_DONATE.
        - FFA_MEM_LEND.
        - FFA_MEM_SHARE.
      - A successful invocation of each of the preceding ABIs returns a Handle (see 5.10.2 Memory region handle)
        to identify the memory region in the transaction.
      - The Sender must convey the Handle to the Receiver through a Partition message.
      - This field must be used by the Receiver to encode this Handle in an invocation of the FFA_MEM_RETRIEVE_REQ
        ABI.
      - A Relayer must validate this field in an invocation of the FFA_MEM_RETRIEVE_REQ ABI as follows.
        - Ensure that it holds a Handle value that was previously allocated and has not been reclaimed by the
          Owner.
        - Ensure that the Handle identifies a memory region that was shared, lent or donated to the Receiver.
        - Ensure that the Handle was allocated to the Owner specified in the Sender endpoint ID field of the
          transaction descriptor.
        It must return INVALID_PARAMETERS if the validation fails.
      - This field must be used by the Relayer to encode the Handle in an invocation of the FFA_MEM_RETRIEVE_RESP
        ABI.
   *)

  (** [See well_formed_FFA_memory_region_struct] *)
  
  (*************************************************************************)
  (** **           Tag usage                                               *)
  (*************************************************************************)
  (**
     - This 64-bit field must be used to specify an IMPLEMENTATION DEFINED value associated with the transaction
       and known to participating endpoints.
     - The Sender must specify this field to the Relayer in an invocation of the following ABIs.
       - FFA_MEM_DONATE.
       - FFA_MEM_LEND.
       - FFA_MEM_SHARE.
     - The Sender must convey the Tag to the Receiver through a Partition message.
     - This field must be used by the Receiver to encode the Tag in an invocation of the FFA_MEM_RETRIEVE_REQ
       ABI.
     - The Relayer must ensure the Tag value specified by the Receiver is equal to the value that was specified by
       the Sender. It must return INVALID_PARAMETERS if the validation fails.
     - This field must be used by the Relayer to encode the Tag value in an invocation of the FFA_MEM_RETRIEVE_RESP
       ABI. 
   *)

  (** [See well_formed_FFA_memory_region_struct] *)  
    
  (*************************************************************************)
  (** **  Endpoint memory access descriptor array usage                    *)
  (*************************************************************************)
  (** [JIEUNG: similar to the previous usage descriptions, the following 
      things has to be defined as invariants] *)
  (** *** Sender usage *)
  (** A Sender must use this field to specify one or more Receivers and the access permissions each should have on the
      memory region it is donating, lending or sharing through an invocation of one of the following ABIs.
      - FFA_MEM_DONATE.
      - FFA_MEM_LEND.
      - FFA_MEM_SHARE.

      The access permissions and flags are subject to validation at the virtual and physical FF-A instances as specified in
      5.11.3 Instruction access permissions usage, 5.11.2 Data access permissions usage and 5.11.1 ABI-specific flags
      usage.

      In a FFA_MEM_SHARE ABI invocation, the Sender could request the memory region to be mapped with different
      data access permission in its own translation regime. It must specify these permissions and its endpoint ID in a
      separate Endpoint memory access descriptor.

      A Sender must describe the memory region in a composite memory region descriptor (see Table 5.13) with the
      following non-exhaustive list of checks.
      - Ensure that the address ranges specified in the composite memory region descriptor do not overlap each other.
      - Total page count is equal to the sum of the Page count fields in each Constituent memory region descriptor.
        [JIEUNG: It is already checked with our well-formedness]

      The offset to this descriptor from the base of Table 5.19 must be specified in the Offset field of the Endpoint
      memory access descriptor as follows.
      
      - In a FFA_MEM_DONATE ABI invocation,
        - The Endpoint memory access descriptor count field in the transaction descriptor must be set to 1. This
          implies that the Owner must specify a single Receiver endpoint in a transaction to donate memory.
        - The Offset field of the Endpoint memory access descriptor must be set to the offset of the composite
          memory region descriptor
      - In a FFA_MEM_LEND and FFA_MEM_SHARE ABI invocation,
        - The Endpoint memory access descriptor count field in the transaction descriptor must be set to a non-zero
          value. This implies that the Owner must specify at least a single Borrower endpoint in a transaction to
          lend or share memory.
        - The Offset field in the Endpoint memory access descriptor of each Borrower must be set to the offset of
          the composite memory region descriptor. This implies that all values of the Offset field must be equal.
   *)

  (** [See well_formed_FFA_memory_region_struct] *)
  
  (** *** Receiver usage *)  
  (** A Receiver must use this field to specify the access permissions it should have on the memory region
      being donated,
      lent or shared in an invocation of the FFA_MEM_RETRIEVE_REQ ABI. This is specified in 5.11.3 Instruction
      access permissions usage and 5.11.2 Data access permissions usage.
      - A Receiver could do this on its behalf if it is a PE endpoint.
      - A Receiver could do this on the behalf of its dependent peripheral devices if it is a proxy endpoint.

      A Receiver could specify the address ranges that must be used to map the memory region in its translation regime
      by describing them in a composite memory region descriptor. The Receiver must perform the same checks as a
      Sender. These checks are described in 5.12.3.1 Sender usage.
      
      The offset to this descriptor from the base of Table 5.19 must be specified in the Offset field of the corresponding
      endpoint memory access descriptor in the array. This implies that all values of the Offset field could be different
      from each other.

      A Receiver could let the Relayer allocate the address ranges that must be used to map the memory region in its
      translation regime and optionally provide an alignment hint (see Address range alignment hint in Table 5.21).
      
      The value 0 must be specified in the Offset field of the corresponding endpoint memory access descriptor in the
      array. This implies that the Handle specified in Table 5.19 must be used to identify the memory region (see 5.12.1
      Handle usage).
      A memory management transaction could be to lend or share memory with multiple Borrowers. The Receiver
      must use this field to specify:
      - The SEPIDs and data access permissions of any dependent peripheral devices (if any) that the Receiver is a
        proxy endpoint for. 
        If the Relayer must allocate the address ranges to map the memory region in the Stream endpoints, the value
        0 must be specified in the Offset field of the corresponding endpoint memory access descriptor in the array.
        If the Receiver specifies the address ranges to map the memory region in the Stream endpoints, then it must
        follow the preceding guidance to specify the address ranges that must be used to map the memory region in
        its translation regime.
      - The identity of any other Borrowers and their data access permissions on the memory region (see 5.11.2
        Data access permissions usage and 5.11.1 ABI-specific flags usage).
        The value 0 must be specified in the Offset field of the corresponding endpoint memory access descriptor in
        the array.
   *)
  
  (** *** Relayer usage *)  
  (** A Relayer must validate the Endpoint memory access descriptor count and each entry in the Endpoint memory
      access descriptor array as follows.
      - The Relayer could support memory management transactions targeted to only a single Receiver endpoint.
        It must return INVALID_PARAMETERS if the Sender or Receiver specifies an Endpoint memory access
        descriptor count != 1.
        
        - [JIEUNG: This one is captured in our well formed condition]

      - It must ensure that these fields have been populated by the Sender as specified in 5.12.3.1 Sender usage in an
        invocation of any of the following ABIs.
        - FFA_MEM_DONATE.
        - FFA_MEM_LEND.
        - FFA_MEM_SHARE.
        The Relayer must return INVALID_PARAMETERS in case of an error.
        
        - [JIEUNG: This one is captured in our well formed condition]

      - It must ensure that the Endpoint ID field in each Memory access permissions descriptor specifies a valid
        endpoint. The Relayer must return INVALID_PARAMETERS in case of an error.
        
        - [JIEUNG: Additional checks required - it is maybe in the argument checks... not in here]

      - In an invocation of the FFA_MEM_RETRIEVE_REQ ABI,
        - It must ensure that these fields have been populated by the Receiver as specified in 5.12.3.2 Receiver
          usage.
        - If the memory region has been lent or shared with multiple Borrowers, the Relayer must ensure that the
          identity of each Borrower specified by the Receiver is the same as that specified by the Sender.
        - If one or more Borrowers are dependent peripheral devices, the Relayer must ensure that the Receiver is
          their proxy endpoint.
        - If the Receiver specifies the address ranges that must be used to map the memory region in its translation
          regime, the Relayer must ensure that the size of the memory region is equal to that specified by the
          Sender.
      
      The Relayer must return INVALID_PARAMETERS in case of an error.
      
      - It must validate the access permissions in the Memory access permissions descriptor in each Endpoint
        memory access descriptor as specified in 5.11.2 Data access permissions usage and 5.11.3 Instruction
        access permissions usage.
      
      A Relayer must use this field in an invocation of the FFA_MEM_RETRIEVE_RESP ABI in response to successful
      validation of a FFA_MEM_RETRIEVE_REQ ABI invocation as follows.
      - To specify the access permissions with which the memory region has been mapped in the translation regime
        of the Receiver.
      - A Receiver could let the Relayer allocate the address ranges to map the memory region. In this case, the
        Relayer must describe the address ranges in a composite memory region descriptor. The Relayer must
        perform the same checks as a Sender. These checks are described in 5.12.3.1 Sender usage.
        The offset to this descriptor from the base of Table 5.19 must be specified in the Offset field of the
        corresponding endpoint memory access descriptor in the array. This implies that all values of the Offset field
        could be different from each other.
      - A Receiver could specify the address ranges that must be used to map the memory region in its translation
        regime. The Relayer must specify the value 0 in the Offset field of the corresponding endpoint memory
        access descriptor in the array.
   *)
  
  (*************************************************************************)
  (** **  Table 11.25: Descriptor to relinquish a memory region             *)
  (*************************************************************************)  

  (** For Relinquish, One more additional tables are defined in Section 11. *)
  (** Table 11.25: Descriptor to relinquish a memory region
      - [ffa_memory_handle_t handle;]
      - [ffa_memory_region_flags_t flags;]
      - [uint32_t endpoint_count;]
      - [ffa_vm_id_t * endpoints;]
   *)
  (* 
     Field              Byte length     Byte offset     Description
     Handle             8               0               - Globally unique Handle to identify a memory
                                                          region.
     Flags              4               8               - Bit(0): Zero memory after relinquish flag.
                                                          - This flag specifies if the Relayer must clear
                                                            memory region contents after unmapping it
                                                            from from the translation regime of the
                                                            Borrower.
                                                            - b0: Relayer must not zero the memory
                                                              region contents.
                                                            - b1: Relayer must zero the memory
                                                              region contents.
                                                          - If the memory region was lent to multiple
                                                            Borrowers, the Relayer must clear memory
                                                            region contents after unmapping it from the
                                                            translation regime of each Borrower, if any
                                                            Borrower including the caller sets this flag.
                                                          - MBZ if the memory region was shared, else
                                                            the Relayer must return
                                                            INVALID_PARAMETERS.
                                                          - MBZ if the Borrower has Read-only access
                                                            to the memory region, else the Relayer must
                                                            return DENIED.
                                                          - Relayer must fulfill memory zeroing
                                                            requirements listed in 5.12.4 Flags usage.
                                                        - Bit(1): Operation time slicing flag.
                                                          - This flag specifies if the Relayer can time
                                                            slice this operation.
                                                            - b0: Relayer must not time slice this
                                                              operation .
                                                            - b1: Relayer can time slice this
                                                              operation.
                                                          - MBZ if the Relayer does not support time slicing
                                                            of memory management operations (see 12.2.3
                                                            Time slicing of memory management operations).

                                                        - Bit(31:2): Reserved (MBZ).

     Endpoint count     4               12              - Count of endpoints.
     Endpoint array     -               16              - Array of endpoint IDs. Each entry contains a
                                                          16-bit ID.
   *)

  Record FFA_memory_relinquish_struct :=
    mkFFA_memory_relinquish_struct {
        (** - length: 8 bytes / offset: 0 bytes 
              - Globally unique Handle to identify a memory region. *)
        FFA_memory_relinquish_struct_handle : ffa_memory_handle_t;
        (** - length: 3 bytes / offset: 8 bytes

            - Bit(0): Zero memory after relinquish flag.
              - This flag specifies if the Relayer must clear memory region contents after unmapping it
                from from the translation regime of the Borrower.
                - b0: Relayer must not zero the memory region contents.
                - b1: Relayer must zero the memory region contents.
              - If the memory region was lent to multiple Borrowers, the Relayer must clear memory
                region contents after unmapping it from the translation regime of each Borrower, if any
                Borrower including the caller sets this flag.
              - MBZ if the memory region was shared, else the Relayer must return INVALID_PARAMETERS.
              - MBZ if the Borrower has Read-only access to the memory region, else the Relayer must return DENIED.
              - Relayer must fulfill memory zeroing requirements listed in 5.12.4 Flags usage.

            - Bit(1): Operation time slicing flag.
              – This flag specifies if the Relayer can time slice this operation.
                - b0: Relayer must not time slice this operation.
                - b1: Relayer can time slice this operation.
              - MBZ if the Relayer does not support time slicing of memory management operations
                (see 12.2.3 Time slicing of memory management operations). 

            - Bit(31:2): Reserved (MBZ). *)
        FFA_memory_relinquish_struct_flags : ffa_memory_region_flags_t;

        (** - length: 4 bytes / offset: 12 bytes
              - Count of endpoints. 
              - we ignored this one by representing endpoints as a list
              - FFA_mem_relinquish_struct_endpoint_count : Z; 

            - length: FFA_mem_relinquish_struct_endpoint_count * 2 bytes / offset: 16 bytes
              - Array of endpoint IDs. Each entry contains a 16-bit ID. *)
        FFA_memory_relinquish_struct_endpoints : list ffa_UUID_t;
      }.

  Definition init_FFA_mem_relinquish_struct :=
    mkFFA_memory_relinquish_struct 0 MEMORY_REGION_FLAG_DEFAULT nil.

  (** **** well formed *)
  (** for FFA_memory_relinquish_struct_flags,
      we can check flag values using the previous well-formed checks *)
  (** for FFA_memory_relinquish_struct_endpoints,
      we need to check whether all endpoints are valid *)
  
  
End FFA_MEMORY_REGION_DESCRIPTOR.

Section FFA_MEMORY_REGION_DESCRIPTOR_CONTEXT.

  Class DescriptorContext `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS} :=
    {
    make_handle (vid: ffa_UUID_t) (value: Z) : option Z;
    get_value (handle: Z) : Z;
    get_sender (handle: Z) : ffa_UUID_t;
    }.
  
End FFA_MEMORY_REGION_DESCRIPTOR_CONTEXT.

