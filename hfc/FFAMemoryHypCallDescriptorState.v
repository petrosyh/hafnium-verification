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
Require Import Decision.

(* FFA Memory management related parts *)
Require Export FFAMemoryHypCall.
Require Import FFAMemoryHypCallIntro.

Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

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


  (** Value types that are related to our modeling. Several types are simply Z types, but we 
   made type aliasing for better readabilitiy. *)
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
    ffa_memory_receiver_flags_t := (option bool);

    (** - Type for an implementation defined values that are used in 
        [FFA_MEM_DONATE], [FFA_MEM_SHARE], and [FFA_MEM_LEND]. So, we cannot specify the value by
        defining inductive types. In this sense, we define it as a general Type *)
    ffa_memory_region_tag_t := Type;
    (** - The following two types are for message passings. We use them to record and 
        retrieve descriptor information *)
    ffa_mailbox_send_msg_t := Type;
    ffa_mailbox_recv_msg_t := Type;

    (** - Granuale value. It is usually a multiplication of 4096 (4KiB) *)
    granuale : ffa_granuale_size_t;
    init_ffa_memory_region_tag : ffa_memory_region_tag_t;
    init_ffa_mailbox_send_msg: ffa_mailbox_send_msg_t;
    init_ffa_mailbox_recv_msg: ffa_mailbox_recv_msg_t;
    }.

  (** Some basic properties of the above values. *)
  Class FFA_TYPES_AND_CONSTANTS_CONTEXTS
        `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS} := 
    {
    (** - Basic decidability properties of them *)
    ffa_memory_region_tag_t_dec : forall (tag1 tag2: ffa_memory_region_tag_t),
        {tag1 = tag2} + {tag1 <> tag2};
    ffa_mailbox_send_msg_t_dec :
      forall (mailbox_send_msg1 mailbox_send_msg2: ffa_mailbox_send_msg_t),
        {mailbox_send_msg1 = mailbox_send_msg2} +
        {mailbox_send_msg1 <> mailbox_send_msg2};
    ffa_mailbox_recv_msg_t_dec :
      forall (mailbox_recv_msg1 mailbox_recv_msg2: ffa_mailbox_recv_msg_t),
        {mailbox_recv_msg1 = mailbox_recv_msg2} +
        {mailbox_recv_msg1 <> mailbox_recv_msg2};    
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
(** The following parts are related to "5.10 Memory region description" and "5.11 Memory region properties" *)
Section FFA_DESCRIPTIONS.

  (**************************************)
  (** ** 5.10 Memory region description *)
  (**************************************)
  Context `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}.

  (****************************************************************************)
  (** ***  Constituent memory region and composite_memory_region descriptors  *) 
  (****************************************************************************)  
  (** We define descriptors that are used in FFA interfaces. Sender, Relayer, and Borrower use them 
      to figure out the information and check validity of the query by using them *) 
     
  (** Table 5.14: Constituent memory region descriptor
      - [uint64_t address;]: base IPA of the constituent memory region, aligned to 4 kiB page size granularity.
        The number of 4 kiB pages in the constituent memory region. 
      - [uint32_t page_count;]
      - [uint32_t reserved;]: Reserved field, must be 0.
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
      - [TODO: Need to add more conditions]
   *)

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

  Definition well_formed_FFA_composite_memory_region_struct
             (composite: FFA_composite_memory_region_struct) :=
    well_formed_FFA_composite_memory_region_struct_aux
      (composite.(FFA_composite_memory_region_struct_page_count))
      (composite.(FFA_composite_memory_region_struct_constituents)).
  
  (***********************************************************************)
  (** ***                       Memory region handle                     *) 
  (***********************************************************************)  
  (** Handle : 64-bit, and the handle is allocated by teh replayer 
     - The Hypervisor must allocate the Handle if no Receiver participating in the memory management
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

  (** Memory region handle in Hafnium is actually the index of "share_state_pool" (defined in FFAMemoryHypCallState.v) 
      which contains the information that receivers has to look up. *)

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
       The permissions with which the memory region should be mapped in the receiver's page table.
     - [ffa_memory_access_permissions_t permissions;]: 
       Flags used during FFA_MEM_RETRIEVE_REQ and FFA_MEM_RETRIEVE_RESP for memory regions with multiple borrowers.
     - [ffa_memory_receiver_flags_t flags;]
  *)

  (**
   A composite memory region description is referenced by specifying an offset to it as described in Table 5.16.
   This enables one or more endpoints to be associated with the same memory region but with different memory
   access permissions for example, SP0 could have RO data access permission and SP1 could have RW data access
   permission to the same memory region.
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
             – bits(3:2): Instruction access permission.
               - b00: Not specified and must be ignored.
               - b01: Not executable.
               - b10: Executable.
               - b11: Reserved. Must not be used.
             – bits(1:0): Data access permission.
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
      FFA_DATA_ACCESS_NOT_SPECIFIED None.
  
  (** Table 5.16: Endpoint memory access descriptor 
      - [struct ffa_memory_region_attributes receiver_permissions;]: 
        Offset in bytes from the start of the outer [ffa_memory_region] to an [ffa_composite_memory_region] struct.
      - [uint32_t composite_memory_region_offset;]
      - [uint64_t reserved_0;]
   *)

  (** **** FFA Endpoint Memory Access Descriptor Coq Definitoin *)  
  Record FFA_endpoint_memory_access_descriptor_struct :=
    mkFFA_endpoint_memory_access_descriptor_struct {
        (** - length: 4 bytes / offset: 0 bytes *)        
        FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor :
          FFA_memory_access_permissions_descriptor_struct;
        
        (** - length: 4 bytes / offset: 4 bytes

           - NOTE: In Hafnium and FF-A document, the following field is defined as an offset 
           to point out the memory region that contains [FFA_composite_memory_region]. 
           In stead of following them, we explicitly map [FFA_composite_memory_region_struct] 
           in here with option type to handle the case when offset points out NULL *)
        FFA_memory_access_descriptor_struct_composite_memory_region_struct :
          option FFA_composite_memory_region_struct;
        (** - It indicates one of constituents inside the composite_memory_region_struct to 
            retrieve specific memory region *)
        FFA_memory_access_descriptor_struct_composite_memory_region_offset : nat;
        
        (** - memory region struct is created and destroyed when hypervisor starts/finishes 
            their handling. Instead of merging it into  
            
            - NOTE: the original size of the above offset value is as follows *)

        (** - Reserved (MBZ) - length: 8 bytes / offset: 8 bytes *)
      }.
  
  Definition init_FFA_endpoint_memory_access_descriptor_struct :=
    mkFFA_endpoint_memory_access_descriptor_struct
      init_FFA_memory_access_permissions_descriptor_struct None 0.


  Definition well_formed_FFA_endpoint_memory_access_descriptor_struct
             (descriptor : FFA_endpoint_memory_access_descriptor_struct) :=
    match descriptor.(FFA_memory_access_descriptor_struct_composite_memory_region_struct) with
    | None =>
      if decide
           (descriptor.(FFA_memory_access_descriptor_struct_composite_memory_region_offset)
            = 0%nat)
      then true else false
    | Some composite =>
      if decide
           ((length (composite.(FFA_composite_memory_region_struct_constituents)) >=
             descriptor.(FFA_memory_access_descriptor_struct_composite_memory_region_offset))%nat)
      then well_formed_FFA_composite_memory_region_struct composite
      else false
    end.
  
  (*******************************************************)
  (** *** 5.11.2 Data access permissions usage           *)
  (*******************************************************)
  (** [JIEUNG: The following things need to be implemented in the transition rules] 
  
      - Read-write permission is more permissive than Read-only permission.
      - Data access permission is specified by setting Bits[1:0] in Table 5.15 to the appropriate value

      Restrictions in lend or share memory:
      - The Lender must specify the level of access that the Borrower is permitted to have on the memory region.
        This is done while invoking the FFA_MEM_SHARE or FFA_MEM_LEND ABIs.
      - The Relayer must validate the permission specified by the Lender as follows. This is done in response
        to an invocation of the FFA_MEM_SHARE or FFA_MEM_LEND ABIs. The Relayer must return the
        DENIED error code if the validation fails.
        - At the Non-secure physical FF-A instance, an IMPLEMENTATION DEFINED mechanism is used to perform validation.
        - At any virtual FF-A instance, if the endpoint is running in EL1 or S-EL1 in either Execution state,
          the permission specified by the Lender is considered valid only if it is the same or less permissive
          than the permission used by the Relayer in the S2AP field in the stage 2 translation table descriptors
          for the memory region in one of the following translation regimes:
          - Secure EL1&0 translation regime, when S-EL2 is enabled.
          - Non-secure EL1&0 translation regime, when EL2 is enabled.
        – At the Secure virtual FF-A instance, if the endpoint is running in S-EL0 in either Execution state,
          the permission specified by the Lender is considered valid only if it is the same or less permissive
          than the permission used by the Relayer in the AP[1] field in the stage 1 translation table descriptors
          for the memory region in one of the following translation regimes:
          - Secure EL1&0 translation regime, when EL2 is disabled.
          - Secure PL1&0 translation regime, when EL2 is disabled.
          - Secure EL2&0 translation regime, when Armv8.1-VHE is enabled.
          If the Borrower is an independent peripheral device, then the validated permission is used to map the
          memory region into the address space of the device.
        - The Borrower (if a PE or Proxy endpoint) should specify the level of access that it would like to have on
          the memory region. In a transaction to share or lend memory with more than one Borrower, each Borrower (if a PE or Proxy
          endpoint) could also specify the level of access that other Borrowers have on the memory region.
          This is done while invoking the FFA_MEM_RETRIEVE_REQ ABI.
        - The Relayer must validate the permissions, if specified by the Borrower (if a PE or Proxy endpoint) in
          response to an invocation of the FFA_MEM_RETRIEVE_REQ ABI.
          It must ensure that the permission of the Borrower is the same or less permissive than the permission
          that was specified by the Lender and validated by the Relayer.
          It must ensure that the permissions for other Borrowers are the same as those specified by the Lender
          and validated by the Relayer. The Relayer must return the DENIED error code if the validation fails.

     Restrictions in dontate memory: 
     - Whether the Owner is allowed to specify the level of access that the Receiver is permitted to have on the
       memory region depends on the type of Receiver.
       – If the Receiver is a PE or Proxy endpoint, the Owner must not specify the level of access.
       – If the Receiver is an independent peripheral device, the Owner could specify the level of access.
       The Owner must specify its choice in an invocation of the FFA_MEM_DONATE ABI.
     - The value of data access permission field specified by the Owner must be interpreted by the Relayer as
       follows. This is done in response to an invocation of the FFA_MEM_DONATE ABI.
       – If the Receiver is a PE or Proxy endpoint, the Relayer must return INVALID_PARAMETERS if the
         value is not b’00.
       – If the Receiver is an independent peripheral device and the value is not b’00, the Relayer must take
         one of the following actions.
         - Return DENIED if the permission is determined to be invalid through an IMPLEMENTATION DEFINED mechanism.
         - Use the permission specified by the Owner to map the memory region into the address space of the device.
       - If the Receiver is an independent peripheral device and the value is b’00, the Relayer must determine
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
   *)

  (*******************************************************)
  (** *** 5.11.3 Instruction access permissions usage    *)
  (*******************************************************)
  (** [JIEUNG: The following things need to be implemented in the transition rules]

      An endpoint could have either Execute (X) or Execute-never (XN) instruction access permission to a memory
      region from the highest Exception level it runs in.
      - Execute permission is more permissive than Execute-never permission.
      - Instruction access permission is specified by setting Bits[3:2] in Table 5.15 to the appropriate value.
        This access control is used in memory management transactions as follows.

      - Only XN permission must be used in the following transactions.
         - In a transaction to share memory with one or more Borrowers.
         - In a transaction to lend memory to more than one Borrower.
         Bits(3:2) in Table 5.15 must be set to b00 as follows.
         - By the Lender in an invocation of FFA_MEM_SHARE or FFA_MEM_LEND ABIs.
         - By the Borrower in an invocation of the FFA_MEM_RETRIEVE_REQ ABI.
         The Relayer must set Bits[3:2] in Table 5.15 to b01 while invoking the FFA_MEM_RETRIEVE_RESP ABI.
      - In a transaction to donate memory or lend memory to a single Borrower,
         - Whether the Owner/Lender is allowed to specify the level of access that the Receiver is permitted to
           have on the memory region depends on the type of Receiver.
           - If the Receiver is a PE or Proxy endpoint, the Owner must not specify the level of access.
           - If the Receiver is an independent peripheral device, the Owner could specify the level of access.
           The Owner must specify its choice in an invocation of the FFA_MEM_DONATE or FFA_MEM_LEND ABIs.
         - The value of instruction access permission field specified by the Owner/Lender must be interpreted   
           by the Relayer as follows. This is done in response to an invocation of the FFA_MEM_DONATE or FFA_MEM_LEND ABIs.
           - If the Receiver is a PE or Proxy endpoint, the Relayer must return INVALID_PARAMETERS if the value is not b’00.
           - If the Receiver is an independent peripheral device and the value is not b’00, the Relayer must take 
             one of the following actions.
             - Return DENIED if the permission is determined to be invalid through an IMPLEMENTATION DEFINED mechanism.
             - Use the permission specified by the Owner to map the memory region into the address space of the device.
           - If the Receiver is an independent peripheral device and the value is b’00, the Relayer must determine 
             the permission value through an IMPLEMENTATION DEFINED mechanism.
         - The Receiver (if a PE or Proxy endpoint) should specify the level of access that it would like to 
           have on the memory region. This must be done in an invocation of the FFA_MEM_RETRIEVE_REQ ABI.
         - The Relayer must validate the permission specified by the Receiver (if a PE or Proxy endpoint) to
           ensure that it is the same or less permissive than the permission determined by the Relayer through an       
           IMPLEMENTATION DEFINED mechanism.
           - For example, the Relayer could deny executable access to a Borrower on a memory region of Device
             memory type.
         - This is done in response to an invocation of the FFA_MEM_RETRIEVE_REQ ABI. The Relayer must
           return the DENIED error code if the validation fails.
  *)
  
  (*******************************************************)
  (** *** 5.11.4 Memory region attributes usage          *)
  (*******************************************************)
  (** Memory type : Device-nGnRnE < Device-nGnRE < Device-nGRE < Device-GRE < Normal.
      
      - Cacheability attribute : Non-cacheable < Write-Back Cacheable.
      - Shareability attribute : Non-Shareable < Inner Shareable < Outer shareable. *)

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

  Inductive FFA_MEMORY_TYPE :=
  | FFA_MEMORY_NOT_SPECIFIED_MEM
  | FFA_MEMORY_DEVICE_MEM
      (cacheability_type: FFA_MEMORY_CACHEABILITY_TYPE_2)
  | FFA_MEMORY_NORMAL_MEM
      (cacheability_type: FFA_MEMORY_CACHEABILITY_TYPE_1)
      (shareability_type: FFA_MEMORY_SHAREABILITY)
  | FFA_MEMORY_MEM_RESERVED.

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
    mkFFA_memory_region_attributes_descriptor_struct FFA_MEMORY_NOT_SPECIFIED_MEM.
  
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

     - 5.12.4.1 Zero memory flag: In some ABI invocations, the caller could set a 
       flag to request the Relayer to zero a memory region. To do this, the Relayer must:

       - Map the memory region in its translation regime once it is not mapped in the translation regime of any other 
       FF-A component.

       - The caller must ensure that the memory region fulfills the size and alignment requirements listed in 2.7
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
  
  (** FFA_MEM_RETRIEVE_REQ 
      Table 5.21: Flags usage in FFA_MEM_RETRIEVE_REQ ABI *)

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
              – MBZ in a transaction to share a memory region, else the Relayer must return
                INVALID_PARAMETER.
              – If the Sender has Read-only access to the memory region and the Receiver sets
                Bit(0), the Relayer must return DENIED.
              – MBZ if the Receiver has previously retrieved this memory region, else the Relayer
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
        (** - Bit(2): Zero memory after relinquish flag.
              – In an invocation of FFA_MEM_RETRIEVE_REQ, this flag specifies whether the Relayer must zero the memory 
                region contents after unmapping it from the translation regime of the Borrower or if the Borrower crashes.
                - b0: Relayer must not zero the memory region contents.
                - b1: Relayer must zero the memory region contents.
              – If the memory region is lent to multiple Borrowers, the Relayer must clear memory region contents after 
                unmapping it from the translation regime of each Borrower, if any Borrower including the caller sets this flag.
              – This flag could be overridden by the Receiver in an invocation of FFA_MEM_RELINQUISH
                (see Flags field in Table 11.25).
              - MBZ if the Receiver has Read-only access to the memory region, else the Relayer  must return DENIED. 
                The Receiver could be a PE endpoint or a dependent peripheral device.
              - MBZ in a transaction to share a memory region, else the Relayer must return
                INVALID_PARAMETER. *)
        FFA_mem_relinquish_req_flags_struct_zero_memory_after_retrieval_flag: bool;
        (**  - Bit(4:3): Memory management transaction type flag.
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
                - b1: Relayer must use the alignment boundary specified in Bits[8:5].
              – Bit(8:5): Alignment hint.
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

  (** FFA_MEM_RETRIEVE_RESP
      Table 5.22: Flags usage in FFA_MEM_RETRIEVE_RESP ABI *)

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

  (** **** FFA Memory Region Coq Definition *)
  Record FFA_memory_region_struct :=
    mkFFA_memory_region_struct {
        (** - length: 2 bytes / offset: 0 bytes *)        
        FFA_memory_region_struct_sender : ffa_UUID_t;
        (** - length: 1 bytes / offset: 2 bytes *)        
        FFA_memory_region_struct_attributes :
          FFA_memory_region_attributes_descriptor_struct;
        (** - length: 1 bytes / offset: 3 bytes (Reserved (MBZ))

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
        FFA_memory_region_struct_flags : ffa_memory_region_flags_t;

        (** - length: 8 bytes / offset: 8 bytes

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
        FFA_memory_region_struct_handle : ffa_memory_handle_t;
        (** - length : 8 bytes / offset 16 bytes *)
        FFA_memory_region_struct_tag : ffa_memory_region_tag_t; 
        (** - length: 4 bytes / offset: 24 bytes (Reserved (MBZ))

            - length: 4 bytes / offset: 28 bytes
              - FFA_memory_region_struct_receiver_count : Z;
              - we ignored this by representing receivers as a list

            - length: FFA_memory_region_struct_receiver_count * 16 bytes / offset: 32 bytes *)
        FFA_memory_region_struct_receivers :
          list FFA_endpoint_memory_access_descriptor_struct;
      }.

  Definition init_FFA_memory_region_struct :=
    mkFFA_memory_region_struct
      0 init_FFA_memory_region_attributes_descriptor_struct
      MEMORY_REGION_FLAG_DEFAULT 0 init_ffa_memory_region_tag nil.

  Fixpoint well_formed_FFA_memory_region_struct_receivers
           (access_descriptors:
              list FFA_endpoint_memory_access_descriptor_struct) :=
    match access_descriptors with
    | nil => true
    | hd::tl =>
      well_formed_FFA_endpoint_memory_access_descriptor_struct hd &&
      well_formed_FFA_memory_region_struct_receivers tl
    end.
  
  (* TODO: need more constraints in here *)
  Definition well_formed_FFA_memory_region_struct
             (memory_region : FFA_memory_region_struct) :=
    well_formed_FFA_memory_region_struct_receivers
      (memory_region.(FFA_memory_region_struct_receivers)).
    
  (*************************************************************************)
  (** **  Endpoint memory access descriptor array usage                     *)
  (*************************************************************************)
  (** [JIEUNG: similar to the previous usage descriptions, the following 
      things has to be defined as invariants] *)
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

  (** A Receiver must use this field to specify the access permissions it should have on the memory region being donated,
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

  (** A Relayer must validate the Endpoint memory access descriptor count and each entry in the Endpoint memory
      access descriptor array as follows.
      - The Relayer could support memory management transactions targeted to only a single Receiver endpoint.
        It must return INVALID_PARAMETERS if the Sender or Receiver specifies an Endpoint memory access
        descriptor count != 1.
      - It must ensure that these fields have been populated by the Sender as specified in 5.12.3.1 Sender usage in an
        invocation of any of the following ABIs.
        - FFA_MEM_DONATE.
        - FFA_MEM_LEND.
        - FFA_MEM_SHARE.
        The Relayer must return INVALID_PARAMETERS in case of an error.
      - It must ensure that the Endpoint ID field in each Memory access permissions descriptor specifies a valid
        endpoint. The Relayer must return INVALID_PARAMETERS in case of an error.
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

  Record FFA_memory_relinquish_struct :=
    mkFFA_memory_relinquish_struct {
        (** - length: 8 bytes / offset: 0 bytes 
              - Globally unique Handle to identify a memory region. *)
        FFA_memory_relinquish_struct_handle : ffa_memory_handle_t;
        (** - length: 3 bytes / offset: 8 bytes

            - Bit(0): Zero memory after relinquish flag.
              – This flag specifies if the Relayer must clear memory region contents after unmapping it
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

  (* TODO: need more constraints in here *)
  Definition well_formed_FFA_memory_relinquish_struct
             (memory_region : FFA_memory_relinquish_struct) := true.
  
End FFA_MEMORY_REGION_DESCRIPTOR.

