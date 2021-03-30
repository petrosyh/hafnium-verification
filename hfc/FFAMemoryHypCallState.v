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
Require Import FFAMemoryHypCall.
Require Import FFAMemoryHypCallIntro.
Require Export FFAMemoryHypCallDescriptorState.

Require Import Maps.
Set Implicit Arguments.
(*************************************************************)
(** * Introduction - state definition                        *)
(*************************************************************)
(** This file provides a state definition for FF-A memory management interfaces. *)


(*************************************************************)
(** **      VM CONTEXT                                       *)
(*************************************************************)
(** This one is necessary to model context saving/restoring of FFA ABI.  
    To model these parts, we refer Hafnium. However, the following model 
    should be quite general enough to use them in other hypervisor implementations. 

  - When looking at Hafnium, related definitions are in
    - "/inc/hf/vm.h"
    - "/inc/hf/.h"
    - "/src/arch/aarch64/inc/hf/arch/types.h" 
*)
Section FFA_VM.

  Class FFA_VM_CONTEXT `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}  :=
    {
    (** - The following two types are for message passings. We use them to record and 
        retrieve descriptor information *)
    ffa_mailbox_send_msg_t : Type;
    ffa_mailbox_recv_msg_t : Type;
    init_ffa_mailbox_send_msg: ffa_mailbox_send_msg_t;
    init_ffa_mailbox_recv_msg: ffa_mailbox_recv_msg_t;

    vcpu_max_num : Z;

    (** mailbox to/from descriptors *)
    mailbox_send_msg_to_region_struct :
      ffa_mailbox_send_msg_t -> option FFA_memory_region_struct;
    mailbox_send_msg_to_relinqiush_struct:
      ffa_mailbox_send_msg_t -> option FFA_memory_relinquish_struct;
    mailbox_send_msg_to_Z :
      ffa_mailbox_send_msg_t -> option Z;
    region_struct_to_mailbox_send_msg :
      FFA_memory_region_struct -> option ffa_mailbox_send_msg_t;
    relinqiush_struct_to_mailbox_send_msg :
      FFA_memory_relinquish_struct -> option ffa_mailbox_send_msg_t;
    Z_to_mailbox_send_msg :
      Z -> option ffa_mailbox_send_msg_t;

    mailbox_recv_msg_to_region_struct :
      ffa_mailbox_recv_msg_t -> option FFA_memory_region_struct;
    mailbox_recv_msg_to_relinqiush_struct:
      ffa_mailbox_recv_msg_t -> option FFA_memory_relinquish_struct;
    mailbox_recv_msg_to_Z:
      ffa_mailbox_recv_msg_t -> option Z;
    region_struct_to_mailbox_recv_msg :
      FFA_memory_region_struct -> option ffa_mailbox_recv_msg_t;
    relinqiush_struct_to_mailbox_recv_msg :
      FFA_memory_relinquish_struct -> option ffa_mailbox_recv_msg_t;
    Z_to_mailbox_recv_msg :
      Z -> option ffa_mailbox_recv_msg_t;

    hafnium_id : ffa_UUID_t := 0;
    primary_vm_id: ffa_UUID_t;
    secondary_vm_ids : list ffa_UUID_t;
    vm_ids := primary_vm_id::secondary_vm_ids;
    number_of_vm := Zlength vm_ids;    
    entity_list : list ffa_UUID_t := hafnium_id::vm_ids;
    
    FFA_memory_region_struct_size
      (contituents: Z) : Z; (* probably 36 *)
    }.

  Context `{ffa_vm_context: FFA_VM_CONTEXT}.
  
  (** In Hafnium: registers in "/src/arch/aarch64/inc/hf/arch/types.h" 
      
      Type to represent the register state of a vCPU. 
      - [uintreg_t r(NUM_GP_REGS);]: General purpose registers.
      - [uintreg_t pc;]
      - [uintreg_t spsr;]
  *)

  (** In Hafnium: VM struct in "/inc/hf/vm.h" 

      - [ffa_vm_id_t id;]
      - [struct smc_whitelist smc_whitelist;]: See api.c for the partial ordering on locks.        
      - [struct spinlock lock;]
      - [ffa_vcpu_count_t vcpu_count;]
      - [struct vcpu vcpus(MAX_CPUS);]
      - [struct mm_ptable ptable;]
      - [struct mailbox mailbox;]
      - [char log_buffer(LOG_BUFFER_SIZE);]
      - [uint16_t log_buffer_length;]
      - [struct wait_entry wait_entries(MAX_VMS);]: Wait entries to be used when waiting on other VM mailboxes. 
        See comments on `struct wait_entry` for the lock discipline of these.
      - [atomic_bool aborting;]
      - [struct arch_vm arch;]: Arch-specific VM information.
   *)

  (** Simplified vcpu context - we only includes some registers - actually only FFA related values *)
  Record ArchRegs :=
    mkArchRegs {
        regs: FFA_value_type;
      }.
  Record VCPU_struct :=
    mkVCPU_struct{
        (** the vm that is currently associated with this vcpu - the connect *)
        cpu_id : option ffa_CPU_ID_t; 
        vm_id: option ffa_UUID_t;
        vcpu_regs: ArchRegs;
      }.

  Record MAILBOX_struct :=
    mkMAILBOX_struct {
        send : ffa_mailbox_send_msg_t;
        recv : ffa_mailbox_recv_msg_t;
        recv_sender : option ffa_UUID_t;
        recv_size : Z;
        recv_func : option FFA_FUNCTION_TYPE;
      }.

  Record VM_COMMON_struct :=
    mkVM_COMMON_struct {
        cur_vcpu_index : option ffa_VCPU_ID_t;
        (** vcpus that are assigned into this VM *)
        vcpus: list ffa_VCPU_ID_t;
        (** vcpu does not need to be allocated into one VM in a consecutive manner. 
            For example, when vcpu_num is 3 for this VM, and assinged vcpu ids can be 0, 3, and 5. *)
        vcpus_contexts : ZTree.t VCPU_struct;
        (** ptable for each VM is defined in AddressTranslation class *)
      }.

  (** Adding several things in here is possible, but we focus on 
      FFA-related things in this VM userspace modeling. We are able to add
      any other things according to our decision *)
  Record VM_USERSPACE_struct :=
    mkVM_USERSPACE_struct {
        vm_userspace_context: VM_COMMON_struct;
        (** all other parts are ignored at this moment *)
      }.
  
  (** Simplified VM context - we assume VM only has own vcpu *)
  Record VM_KERNEL_struct :=
    mkVM_KERNEL_struct {
        vm_kernelspace_context : VM_COMMON_struct;
        (** Each VM has its own mailbox. *)
        (** IN FFA ABI handling, the actual information for the handling is in mailboxes. 
           In this sense, we includes this informaiton in this state definition *)
        mailbox : MAILBOX_struct;
        (** all other parts are ignored at this moment *)        
      }.

End FFA_VM.

(*************************************************************)
(** **        memory and ptable                              *)
(*************************************************************)
Section MEM_AND_PTABLE.

  Context `{ffa_vm_context: FFA_VM_CONTEXT}.
  
  (** memory states on memory addresses 

     We do not consider contents inside the memory, but we do care about its properties -
     and those properties are necessary for us to prove whether each component in the system
     accesses memory in a valid way. Therefore, we have the following mapping from
     each memory address to several properties. 

     There are several dependencies between those properties. 
     So, Those information are somewhat redundant, but 
     we keep them in terms of explicit information that we can easily infer the curretn state of 
     each address in the memory.
   
   *)

  (** Indicates who is the owner of the memory *)
  Inductive OWNERSHIP_STATE_TYPE :=
  | Owned (id : ffa_UUID_t)
  | NotOwned.
  
  (** Indicates access state of each memory address *)
  Inductive ACCESS_STATE_TYPE :=
  | NoAccess 
  | ExclusiveAccess (accessor: ffa_UUID_t)
  (** SharedAccess with one UUID differs from ExclusiveAccess - Note that accesssors will not be nil *)
  | SharedAccess (accessors : list ffa_UUID_t).

  (** Check whether the page is dirty or clean. Some FFA calls clean the memory, and it is 
      one of important behaviours that we have to observe. In this sense, we explicitly 
      model them. 
      
      Those values are necessary for us to distinguish behaviours caused by zero memory flags values 
      in the descriptor 
   *)
  Inductive MEM_DIRTY_TYPE := 
  | MemClean
  (** We can treat "MemWritten nil" as a MemClean, but we try to explicitly distinguish them.
      writers:
      - who wrote values in the address
      - Note that accesssors will not be nil *)
  | MemWritten (writers: list ffa_UUID_t).
                              
  (** This memory properties are key features that we may hope to guarantee in our system -
      There are some redundant information in between them, and we may need to 
      make invariants to guarantee well-formed relations between the following different properties 
      (and other parts of the abstract state). 
   *)

  
  Record MemGlobalProperties :=
    mkMemGlobalProperties {
        (** - there can be only one owner *)
        owned_by : OWNERSHIP_STATE_TYPE;
        (** - access information *)
        accessible_by : ACCESS_STATE_TYPE;

        (** They specifies executable / non-executalbe and read / writer permissions *)
        global_instruction_access_property : FFA_INSTRUCTION_ACCESS_TYPE;
        global_data_access_property: FFA_DATA_ACCESS_TYPE;
        (** memory attributes - e.g., sharable or cacheability *)
        global_mem_attribute : FFA_MEMORY_TYPE;
        
        (** - check whether there are written contents in the memory or not *)
        mem_dirty: MEM_DIRTY_TYPE;        
      }.

  (** key is a base address of memory region *)
  Definition mem_global_properties_pool := ZTree.t MemGlobalProperties.

  (** It indicates the owned infromation in memory local properties.
      This needs to be consistent with OwnershipState. *)
  Inductive MEM_LOCAL_OWNED_TYPE :=
  | LocalOwned
  | LocalBorrowed (owner : ffa_UUID_t).
  (* [TODO: we need to check whether the following MemAttributes needs to be a global attributes 
     or a local attributes]

     Indicates whether the memory is device memory or normal memory, and corresponding 
     attributes of that page. If the page is a normal memory, the memory is shareable if the 
     shareability flag indicates it is possible. 

     This memory attributes need to be consistent with AccessState. *)
  
  Record MemLocalProperties :=
    mkMemLocalProperties {
        mem_local_owned:  MEM_LOCAL_OWNED_TYPE;
        (** Instruction and data access property *)
        (** They specifies executable / non-executalbe and read / writer permissions *)
        instruction_access_property : FFA_INSTRUCTION_ACCESS_TYPE;
        data_access_property: FFA_DATA_ACCESS_TYPE;
        (** memory attributes - e.g., sharable or cacheability *)
        mem_attribute : FFA_MEMORY_TYPE;
      }.

  Definition gen_borrow_mem_local_properties
             (lender : ffa_UUID_t) (iap : FFA_INSTRUCTION_ACCESS_TYPE)
             (dap : FFA_DATA_ACCESS_TYPE) (attr: FFA_MEMORY_TYPE) :=
    mkMemLocalProperties (LocalBorrowed lender) iap dap attr.
  
  Definition gen_borrow_mem_local_properties_wrapper
             (lender : ffa_UUID_t) (local_props: MemLocalProperties) :=
    gen_borrow_mem_local_properties
      lender (local_props.(instruction_access_property))
      (local_props.(data_access_property))
      (local_props.(mem_attribute)).
  
  Definition own_mem_local_properties (iap : FFA_INSTRUCTION_ACCESS_TYPE)
             (dap : FFA_DATA_ACCESS_TYPE) (attr: FFA_MEMORY_TYPE) :=
    mkMemLocalProperties LocalOwned iap dap attr.

  Definition gen_own_mem_local_properties_wrapper
             (local_props: MemLocalProperties) :=
    own_mem_local_properties
      (local_props.(instruction_access_property))
      (local_props.(data_access_property)) (local_props.(mem_attribute)).

 
  (** key is an address of memory *)
  Definition mem_local_properties_pool := ZTree.t MemLocalProperties.
  (** key is a entity id of the system *)  
  Definition mem_local_properties_global_pool
    := ZTree.t mem_local_properties_pool.

  (** There are relations between mem_global_properties and mem_local_properties.
      For example, if a certain address in access_state of MemGlobalProperties is mapped with 
      SharedAccess 1, then there should be a valid element for the address in the mem local properties pool for entity 1.
      And, the corresponding mem_local_owned of the MemLocalProperties for entity 1 has to be
      either Owned or LocalBorrowed with the valid owner value that are marked in OwnershipState of the MemGlobalProperties. 

      There are some redundant information in MemGlobalProperties and MemLocalProperties.
      However, those redundancies sometimes help us to prove memory related properties easy
      (when we have invariants about relations between those redundant information).

      TODO: add those constraints in HafniumMemoryManagementContext *)
  Record MemProperties :=
    mkMemProperties {
        mem_global_properties: mem_global_properties_pool;
        mem_local_properties: mem_local_properties_global_pool;
      }.

End MEM_AND_PTABLE.

Section MEM_AND_PTABLE_CONTEXT.
  (** In top level, we do not need to specify ptable in detail. 
     In this sense, we try to abstract the definition of ptable. 
     => gets the input address (e.g., va or ipa) and return the address (e.g., ipa or pa) 

     Filling out details of those definitions are user's obligations *)       
  Class MemoryManagementBasicContext
        `{ffa_vm_context: FFA_VM_CONTEXT} :=
    {
    (** address low and high *)
    address_low : ffa_address_t;
    address_high : ffa_address_t;

    (** usually 4096 *)
    alignment_value : Z;
    }.
  
  Class MemoryManagementContext
        `{memory_management_basic_context
          : MemoryManagementBasicContext} :=
    {
    (** address translation funciton in ptable. There are two possible cases 
        1. provides the entire address translation from 
           the root level to the bottom level 
        2. provides the only one level address translation. 
           Among them, our high-level model assumes the following ptable uses the second approach *)
    stage2_address_translation_table
      (input_addr:  ffa_address_t) : option ffa_address_t;
    (** This address translation won't be used in the current setting.
        We may be able to use this one depending on the definition *)
    stage1_address_translation_table
      (vm_id : ffa_UUID_t) (input_addr: ffa_address_t) : option ffa_address_t;
    }.

End MEM_AND_PTABLE_CONTEXT.

(*************************************************************)
(** **     AbstractState for FFA modeling                    *)
(*************************************************************)
Section AbstractState.

  Context `{ffa_vm_context: FFA_VM_CONTEXT}.
  
  (** It represents CPU object, but it is currently empty. *)
  Record CPU_struct :=
    mkCPU_struct { 
      }.
  

  (* TODO: FF-A document does not explicitly define this structure, so we need abstractions for the following definition 
 
   Hafnium's data structure for FFA memory management ABI handling 

   - [struct ffa_memory_region *memory_region;]: The memory region being shared, or NULL if this share state is unallocated.
   - [uint32_t share_func;]: The FF-A function used for sharing the memory. Must be one of 
     FFA_MEM_DONATE_32, FFA_MEM_LEND_32 or FFA_MEM_SHARE_32 if the share state is allocated, or 0.
   - [bool retrieved(MAX_MEM_SHARE_RECIPIENTS);]: Whether each recipient has retrieved the memory region yet. The order
     of this array matches the order of the attribute descriptors in the
     memory region descriptor. Any entries beyond the attribute_count will
     always be false.
 *)
  
  Record FFA_memory_share_state_struct :=
    mkFFA_memory_share_state_struct {
        memory_region : FFA_memory_region_struct;
        share_func : FFA_FUNCTION_TYPE;
        (** - The first key is ffa_UUID_t, and the second key is address *)
        retrieved : ZTree.t (ZTree.t bool);
        relinquished : ZTree.t (ZTree.t bool);
        retrieve_count : ZTree.t (ZTree.t Z);
      }.

  Definition share_state_pool := ZTree.t FFA_memory_share_state_struct.
  
  Record hypervisor_struct :=
    mkHypervisor_struct {
        (** - For cpu information *)
        current_cpu_id : Z;
        cpu_num : Z;
        cpus: ZTree.t CPU_struct;

        time_slice_enabled: bool;

        (** - Registers that we have to keep to handle FFA ABIs 

            - The following register keeps the currently existing VCPU information that is 
              associated with the current hvc_call. via that VCPU, it is possible for us to find out 
              the sender's information for ABI calls 
           
            - The related part in the Hafnium code is the following function in
              "/src/arch/aarch64/hypervisor/handler.c"
            
              - [static struct vcpu *current(void){]
                - [return (struct vcpu * )read_msr(tpidr_el2);]
              - [}]

            - List of registers  will be increasing to model other behaviours
              - e.g., the register for TLB invalidate *)
        tpidr_el2 : option VCPU_struct;
        
        (** - For API - FFA ABI handlings 

            = Free pages at the top level. those pages need to be used for the 
            FFA ABI handlings. But, to simplify it (like what we have currently doing in
            page_table, we represent it as a size of free pages. Then, we will only increase / decrease
            the number when we allocate pages or free those pages while handling FFA ABIs *)
        api_page_pool_size : Z;
        
        (** - ffa_share_state is for ffa communications  *)
        ffa_share_state: share_state_pool;
        fresh_index_for_ffa_share_state : Z;
        
        (** - ptable is defined in AddressTranslation class *)
        (** - Memory attributes for key is an address *) 
        mem_properties : MemProperties;
        
        (** - vm count *)
        vm_count : Z;
        (** - VM contexts saved in hafnium *)
        (** - VM ids are consecutively assigned. *) 
        vms_contexts :  ZTree.t VM_KERNEL_struct;
      }.
  
  (** Log file to easily print out system's change history. 
      This definition can be abstracted if it is preferred *)
  Inductive log_type :=
    (** - Scheduling *)
  | ChangeCurEntityID (from_id to_id : ffa_UUID_t) (* by scheduler *)
    (** - Context switching *)
  | UserToKernel (vid: ffa_UUID_t)
                 (vcpu_id : ffa_VCPU_ID_t)
                 (reg_values: ArchRegs)
  | KernelToUser (vid: ffa_UUID_t)
                 (vcpu_id : ffa_VCPU_ID_t)
                 (reg_values: ArchRegs)
    (** - Dispatch Information *)                 
  | DispathFFAInterface (reg_values: ArchRegs)      
    (** - Mem property change *)
  | SetOwner (entity_id : ffa_UUID_t) (address : ffa_address_t)
             (owner: OWNERSHIP_STATE_TYPE)
  | SetAccessible (vm_id : ffa_UUID_t) (address: ffa_address_t)
                  (access:  ACCESS_STATE_TYPE)
  | SetDirty (vm_id: ffa_UUID_t) (address: ffa_address_t)
             (dirty: MEM_DIRTY_TYPE)                  
  | SetInstructionAccess (vm_id : ffa_UUID_t) (address: ffa_address_t)
                         (access: FFA_INSTRUCTION_ACCESS_TYPE)
  | SetDataAccess (vm_id : ffa_UUID_t) (address: ffa_address_t)
                  (access: FFA_DATA_ACCESS_TYPE)
  | SetAttributes (vm_id : ffa_UUID_t) (address: ffa_address_t)
                  (attributes: FFA_MEMORY_TYPE)
    (** - Send and receiver Msg *)
  | SendMsg (sender receiver: ffa_UUID_t)
            (msg : MAILBOX_struct)
  | RecvMsg (receiver: ffa_UUID_t)
            (msg : MAILBOX_struct).

  
  Record AbstractState :=
    mkAbstractState{
        (** - The number to memorize the version of FFA - See 8.1 FFA_VERSION of the document and 
            - FFAMemoryHypCallIntro.v file for more details *)
        FFA_version_number: ffa_version_number_t;
        (** - If it is true, hypervisor owns the control. If it is not, 
              one entity in the user space owns the control *)
        is_hvc_mode: bool;
        (** - It indicates whether we use stage 1 address translation or not. *)
        use_stage1_table: bool;
        (** - the entity that is currently running user vm ID
              - When is_hvc_mode is true, the following value implies the last VM that gives 
                up its evaluation control to the kernel *)
        cur_user_entity_id: ffa_UUID_t;
        (** - hafnium global stage *)
        hypervisor_context: hypervisor_struct;
        (** - VM clinets *) 
        vms_userspaces : ZTree.t VM_USERSPACE_struct;

        (** - a log field to memorize operation histories *)
        system_log: list log_type;        
      }.

End AbstractState.

(*************************************************************)
(** **  Several abstract definitions and invariants          *)
(*************************************************************)

Section AbstractStateContext.

  (** All contexts for high-level modeling. We currently merge all contexts that we have declared in here 
      to avoid conflicts due to type classes *)
  Class AbstractStateContext
        `{ffa_types_and_constants:
            !FFA_TYPES_AND_CONSTANTS}
        `{descriptor_context: !DescriptorContext
                               (ffa_types_and_constants :=
                                  ffa_types_and_constants)}
        `{ffa_vm_context: !FFA_VM_CONTEXT
                           (ffa_types_and_constants
                              := ffa_types_and_constants)}
        `{memory_management_basic_context :
            !MemoryManagementBasicContext
             (ffa_vm_context
                := ffa_vm_context)}
        `{memory_management_context :
            !MemoryManagementContext
             (memory_management_basic_context
                := memory_management_basic_context)} :=
    {
    (** We may be able to use some feature of interaction tree for this scheduling? *)
    scheduler : AbstractState -> ffa_UUID_t; 
    
    initial_state : AbstractState;    
    }.

End AbstractStateContext.

(** There are update functions and notations for those update functions. 
    However, I hide them in the generated doc *)

(* begin hide *)

(*************************************************************)
(** **        Update functions for readability               *)
(*************************************************************)

Section AbstractStateUpdate.  

  Context `{abstract_state_context: AbstractStateContext}.
  (** update functions for better readability *)
  
  (** update memory global properties *)
  Definition update_owned_by_in_mem_global_properties
             (a : MemGlobalProperties) b :=
    mkMemGlobalProperties b
                          (a.(accessible_by))
                          (a.(global_instruction_access_property))
                          (a.(global_data_access_property))
                          (a.(global_mem_attribute))
                          (a.(mem_dirty)).
  
  Definition update_accessible_by_in_mem_global_properties
             (a : MemGlobalProperties) b :=
    mkMemGlobalProperties (a.(owned_by))
                          b
                          (a.(global_instruction_access_property))
                          (a.(global_data_access_property))
                          (a.(global_mem_attribute))
                          (a.(mem_dirty)).

  Definition update_global_instruction_access_property_in_mem_global_properties
             (a : MemGlobalProperties) b :=
    mkMemGlobalProperties (a.(owned_by))
                          (a.(accessible_by))
                          b
                          (a.(global_data_access_property))
                          (a.(global_mem_attribute))
                          (a.(mem_dirty)).
             
  Definition update_global_data_access_property_in_mem_global_properties
             (a : MemGlobalProperties) b :=
    mkMemGlobalProperties (a.(owned_by))
                          (a.(accessible_by))
                          (a.(global_instruction_access_property))
                          b
                          (a.(global_mem_attribute))
                          (a.(mem_dirty)).

  Definition update_global_mem_attribute_in_mem_global_properties
             (a : MemGlobalProperties) b :=
    mkMemGlobalProperties (a.(owned_by))
                          (a.(accessible_by))
                          (a.(global_instruction_access_property))
                          (a.(global_data_access_property))
                          b
                          (a.(mem_dirty)).

    
  Definition update_mem_dirty_in_mem_global_properties
             (a : MemGlobalProperties) b :=
    mkMemGlobalProperties (a.(owned_by))
                          (a.(accessible_by))
                          (a.(global_instruction_access_property))
                          (a.(global_data_access_property))
                          (a.(global_mem_attribute))
                          b.
  
  (** update memory local properties *)
  Definition update_mem_local_owned_in_mem_local_properties
             (a: MemLocalProperties) b :=
    mkMemLocalProperties b
                         (a.(instruction_access_property))
                         (a.(data_access_property))
                         (a.(mem_attribute)).
  
  Definition update_instruction_access_property_in_mem_local_properties
             (a : MemLocalProperties) b :=
    mkMemLocalProperties (a.(mem_local_owned))
                         b
                         (a.(data_access_property))
                         (a.(mem_attribute)).
  
  Definition update_data_access_property_in_mem_local_properties
             (a : MemLocalProperties) b :=
    mkMemLocalProperties (a.(mem_local_owned))
                         (a.(instruction_access_property))
                         b
                         (a.(mem_attribute)).

  Definition update_mem_attribute_in_mem_local_properties
             (a : MemLocalProperties) b :=
    mkMemLocalProperties (a.(mem_local_owned))
                         (a.(instruction_access_property))
                         (a.(data_access_property))
                         b.

  (** update memory properties *)
  Definition update_mem_global_properties_in_mem_properties
             (a : MemProperties) b :=
    mkMemProperties b
                    (a.(mem_local_properties)). 

  Definition update_mem_local_properties_in_mem_properties
             (a : MemProperties) b :=
    mkMemProperties (a.(mem_global_properties))
                    b.

  (* vm_common_context update *)
  Definition update_cur_vcpu_index_in_vm_common_context
             (a : VM_COMMON_struct) b :=
    mkVM_COMMON_struct b
                       (a.(vcpus))
                       (a.(vcpus_contexts)).
  
  Definition update_vcpus_in_vm_common_context
             (a : VM_COMMON_struct) b :=
    mkVM_COMMON_struct (a.(cur_vcpu_index))
                       b
                       (a.(vcpus_contexts)).
  
  Definition update_vcpus_contexts_in_vm_common_context
             (a : VM_COMMON_struct) b :=
    mkVM_COMMON_struct (a.(cur_vcpu_index))
                       (a.(vcpus))
                       b.

  (* vm_kernel_context update *)
  Definition update_cur_vcpu_index_in_vm_kernel_context
             (a : VM_KERNEL_struct) b :=
    mkVM_KERNEL_struct
      (update_cur_vcpu_index_in_vm_common_context
         (a.(vm_kernelspace_context)) b)
      (a.(mailbox)).

  Definition update_vcpus_in_vm_kernel_context
             (a : VM_KERNEL_struct) b :=
    mkVM_KERNEL_struct
      (update_vcpus_in_vm_common_context
         (a.(vm_kernelspace_context)) b)
      (a.(mailbox)).

  Definition update_vcpus_contexts_in_vm_kernel_context
             (a : VM_KERNEL_struct) b :=
    mkVM_KERNEL_struct
      (update_vcpus_contexts_in_vm_common_context
         (a.(vm_kernelspace_context)) b)
      (a.(mailbox)).

  Definition update_mailbox_in_vm_kernel_context
             (a : VM_KERNEL_struct) b :=
    mkVM_KERNEL_struct (a.(vm_kernelspace_context)) b.

  (* vm_userspace_context update *)
  Definition update_cur_vcpu_index_in_vm_userspace_context
             (a : VM_USERSPACE_struct) b :=
    mkVM_USERSPACE_struct
      (update_cur_vcpu_index_in_vm_common_context
         (a.(vm_userspace_context)) b).

  Definition update_vcpus_in_vm_userspace_context
             (a : VM_USERSPACE_struct) b :=
    mkVM_USERSPACE_struct
      (update_vcpus_in_vm_common_context
         (a.(vm_userspace_context)) b).

  Definition update_vcpus_contexts_in_vm_userspace_context
             (a : VM_USERSPACE_struct) b :=
    mkVM_USERSPACE_struct
      (update_vcpus_contexts_in_vm_common_context
         (a.(vm_userspace_context)) b).  
  
  (** update hafnium context *)
  Definition update_current_cpu_id_in_hafnium_context
             (a: hypervisor_struct) b :=
    mkHypervisor_struct b (a.(cpu_num)) (a.(cpus))
                        (a.(time_slice_enabled))
                        (a.(tpidr_el2))
                        (a.(api_page_pool_size))
                        (a.(ffa_share_state))
                        (a.(fresh_index_for_ffa_share_state))
                        (a.(mem_properties)) (a.(vm_count))
                        (a.(vms_contexts)).

  Definition update_cpu_num_in_hafnium_context
             (a: hypervisor_struct) b :=
    mkHypervisor_struct (a.(current_cpu_id)) b (a.(cpus))
                        (a.(time_slice_enabled))
                        (a.(tpidr_el2))
                        (a.(api_page_pool_size))
                        (a.(ffa_share_state))
                        (a.(fresh_index_for_ffa_share_state))
                        (a.(mem_properties)) (a.(vm_count))
                        (a.(vms_contexts)).

  Definition update_cpus_in_hafnium_context
             (a: hypervisor_struct) b :=
    mkHypervisor_struct (a.(current_cpu_id)) (a.(cpu_num)) b
                        (a.(time_slice_enabled))
                        (a.(tpidr_el2))
                        (a.(api_page_pool_size))
                        (a.(ffa_share_state))
                        (a.(fresh_index_for_ffa_share_state))
                        (a.(mem_properties)) (a.(vm_count))
                        (a.(vms_contexts)).

  Definition update_time_slice_enabled_in_hafnium_context
             (a: hypervisor_struct) b :=
    mkHypervisor_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus)) b
                        (a.(tpidr_el2))
                        (a.(api_page_pool_size))
                        (a.(ffa_share_state))
                        (a.(fresh_index_for_ffa_share_state))
                        (a.(mem_properties)) (a.(vm_count))
                        (a.(vms_contexts)).
  
  Definition update_tpidr_el2_in_hafnium_context
             (a: hypervisor_struct) b :=
    mkHypervisor_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus))
                        (a.(time_slice_enabled)) b
                        (a.(api_page_pool_size))
                        (a.(ffa_share_state))
                        (a.(fresh_index_for_ffa_share_state))
                        (a.(mem_properties)) (a.(vm_count))
                        (a.(vms_contexts)).

  Definition update_api_page_pool_size_in_hafnium_context
             (a: hypervisor_struct) b :=
    mkHypervisor_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus))
                        (a.(time_slice_enabled))                        
                        (a.(tpidr_el2)) b
                        (a.(ffa_share_state))
                        (a.(fresh_index_for_ffa_share_state))
                        (a.(mem_properties)) (a.(vm_count))
                        (a.(vms_contexts)).

  Definition update_ffa_share_state_in_hafnium_context
             (a: hypervisor_struct) b :=
    mkHypervisor_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus))
                        (a.(time_slice_enabled))                        
                        (a.(tpidr_el2))
                        (a.(api_page_pool_size)) b
                        (a.(fresh_index_for_ffa_share_state))
                        (a.(mem_properties)) (a.(vm_count))
                        (a.(vms_contexts)).

  Definition update_fresh_index_for_ffa_share_state_in_hafnium_context
             (a: hypervisor_struct) b :=
    mkHypervisor_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus))
                        (a.(time_slice_enabled))                        
                        (a.(tpidr_el2))
                        (a.(api_page_pool_size)) (a.(ffa_share_state)) b
                        (a.(mem_properties)) (a.(vm_count))
                        (a.(vms_contexts)).
  
  Definition update_mem_properties_in_hafnium_context
             (a: hypervisor_struct) b :=
    mkHypervisor_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus))
                        (a.(time_slice_enabled))                        
                        (a.(tpidr_el2))
                        (a.(api_page_pool_size)) (a.(ffa_share_state))
                        (a.(fresh_index_for_ffa_share_state))
                        b (a.(vm_count)) (a.(vms_contexts)).
  
  Definition update_vm_count_in_hafnium_context
             (a: hypervisor_struct) b :=
    mkHypervisor_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus))
                        (a.(time_slice_enabled))                        
                        (a.(tpidr_el2))
                        (a.(api_page_pool_size)) (a.(ffa_share_state))
                        (a.(fresh_index_for_ffa_share_state))
                        (a.(mem_properties)) b
                        (a.(vms_contexts)).

  Definition update_vms_contexts_in_hafnium_context
             (a: hypervisor_struct) b :=
    mkHypervisor_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus))
                        (a.(time_slice_enabled))                        
                        (a.(tpidr_el2))
                        (a.(api_page_pool_size)) (a.(ffa_share_state))
                        (a.(fresh_index_for_ffa_share_state))
                        (a.(mem_properties))
                        (a.(vm_count)) b.
  (** update *)
  Definition update_FFA_version_number (a: AbstractState) b := 
    mkAbstractState
      b (a.(is_hvc_mode))
      (a.(use_stage1_table))
      (a.(cur_user_entity_id))
      (a.(hypervisor_context)) (a.(vms_userspaces))
      (a.(system_log)).

  Definition update_is_hvc_mode (a: AbstractState) b := 
    mkAbstractState
      (a.(FFA_version_number)) b
      (a.(use_stage1_table))
      (a.(cur_user_entity_id)) 
      (a.(hypervisor_context)) (a.(vms_userspaces))
      (a.(system_log)).

  Definition update_use_stage1_table (a: AbstractState) b := 
    mkAbstractState
      (a.(FFA_version_number))
      (a.(is_hvc_mode))
      b
      (a.(cur_user_entity_id)) 
      (a.(hypervisor_context)) (a.(vms_userspaces))
      (a.(system_log)).
  
  Definition update_cur_user_entity_id (a : AbstractState) b :=
    mkAbstractState
      (a.(FFA_version_number)) (a.(is_hvc_mode))
      (a.(use_stage1_table))
      b
      (a.(hypervisor_context)) (a.(vms_userspaces))
      (a.(system_log)).

  Definition update_hypervisor_context (a : AbstractState) b :=
    mkAbstractState
      (a.(FFA_version_number))
      (a.(use_stage1_table))
      (a.(is_hvc_mode))
      (a.(cur_user_entity_id))
      b (a.(vms_userspaces))
      (a.(system_log)).

  Definition update_hypervisor_current_cpu_id
             (a: AbstractState) b :=
    update_hypervisor_context
      a (update_current_cpu_id_in_hafnium_context
           a.(hypervisor_context) b).

  Definition update_hypervisor_cpu_num (a: AbstractState) b :=
    update_hypervisor_context
      a (update_cpu_num_in_hafnium_context
           a.(hypervisor_context) b).

  Definition update_hypervisor_cpus (a: AbstractState) b :=
    update_hypervisor_context
      a (update_cpus_in_hafnium_context
           a.(hypervisor_context) b).
  
  Definition update_hypervisor_tpidr_el2 (a: AbstractState) b :=
    update_hypervisor_context
      a (update_tpidr_el2_in_hafnium_context
           a.(hypervisor_context) b).

  Definition update_hypervisor_api_page_pool_size (a: AbstractState) b :=
    update_hypervisor_context
      a (update_api_page_pool_size_in_hafnium_context
           a.(hypervisor_context) b).

  Definition update_hypervisor_ffa_share_state
             (a: AbstractState) b :=
    update_hypervisor_context
      a (update_ffa_share_state_in_hafnium_context
           a.(hypervisor_context) b).

  Definition update_hypervisor_fresh_index_for_ffa_share_state
             (a: AbstractState) b :=
    update_hypervisor_context
      a (update_fresh_index_for_ffa_share_state_in_hafnium_context
           a.(hypervisor_context) b).

  Definition update_hypervisor_mem_properties
             (a: AbstractState) b :=
    update_hypervisor_context
      a (update_mem_properties_in_hafnium_context
           a.(hypervisor_context) b).
  
  Definition update_hypervisor_vm_count
             (a: AbstractState) b :=
    update_hypervisor_context
      a (update_vm_count_in_hafnium_context
           a.(hypervisor_context) b).
  
  Definition update_hypervisor_vms_contexts
             (a: AbstractState) b :=
    update_hypervisor_context
      a (update_vms_contexts_in_hafnium_context
           a.(hypervisor_context) b).
  
  Definition update_vms_userspaces
             (a : AbstractState) b :=
    mkAbstractState
      (a.(FFA_version_number)) (a.(is_hvc_mode))
      (a.(use_stage1_table))
      (a.(cur_user_entity_id))      
      (a.(hypervisor_context)) b
      (a.(system_log)).

  Definition update_system_log
             (a : AbstractState) b :=
    mkAbstractState
      (a.(FFA_version_number)) (a.(is_hvc_mode))
      (a.(use_stage1_table))
      (a.(cur_user_entity_id))
      (a.(hypervisor_context))
      (a.(vms_userspaces)) b.  
  
End AbstractStateUpdate.

(** update memory global properties *)
Notation "a '{' 'owned_by' : b '}'" :=
  (update_owned_by_in_mem_global_properties a b) (at level 1).
Notation "a '{' 'accessible_by' : b '}'" :=
  (update_accessible_by_in_mem_global_properties a b) (at level 1).
Notation "a '{' 'global_instruction_access_property' : b '}'" :=
  (update_global_instruction_access_property_in_mem_global_properties a b) (at level 1).
Notation "a '{' 'global_data_access_property' : b '}'" :=
  (update_global_data_access_property_in_mem_global_properties a b) (at level 1).
Notation "a '{' 'global_mem_attribute' : b '}'" :=
  (update_global_mem_attribute_in_mem_global_properties a b) (at level 1).
Notation "a '{' 'mem_dirty' : b '}'" :=
  (update_mem_dirty_in_mem_global_properties a b) (at level 1).
  
(** update memory local properties *)
Notation "a '{' 'mem_local_owned' : b '}'" :=
  (update_mem_local_owned_in_mem_local_properties a b) (at level 1).
Notation "a '{' 'instruction_access_property' : b '}'" :=
  (update_instruction_access_property_in_mem_local_properties a b) (at level 1).
Notation "a '{' 'data_access_property' : b '}'" :=
  (update_data_access_property_in_mem_local_properties a b) (at level 1).
Notation "a '{' 'mem_attribute' : b '}'" :=
  (update_mem_attribute_in_mem_local_properties a b) (at level 1).

(** update memory properties *)
Notation "a '{' 'mem_global_properties' : b '}'" :=
  (update_mem_global_properties_in_mem_properties a b) (at level 1).
Notation "a '{' 'mem_local_properties' : b '}'" :=
  (update_mem_local_properties_in_mem_properties a b) (at level 1).

(** update vm context *)
Notation "a '{' 'vm_cur_vcpu_index' : b '}'"
  := (update_cur_vcpu_index_in_vm_kernel_context a b) (at level 1).
Notation "a '{' 'vm_vcpus' : b '}'"
  := (update_vcpus_in_vm_kernel_context a b) (at level 1).
Notation "a '{' 'vm_vcpus_contexts' : b '}'"
  := (update_vcpus_contexts_in_vm_kernel_context a b) (at level 1).
Notation "a '{' 'vm_mailbox' : b '}'"
  := (update_mailbox_in_vm_kernel_context a b) (at level 1).

(** update hafnium context *)
Notation "a '{' 'hypervisor_context' '/' 'current_cpu_id' : b '}'"
  := (update_hypervisor_current_cpu_id a b) (at level 1).
Notation "a '{' 'hypervisor_context' '/' 'cpu_num' : b '}'"
  := (update_hypervisor_cpu_num a b) (at level 1).
Notation "a '{' 'hypervisor_context' '/' 'cpus' : b '}'"
  := (update_hypervisor_cpus a b) (at level 1).
Notation "a '{' 'hypervisor_context' '/' 'tpidr_el2' : b '}'"
  := (update_hypervisor_tpidr_el2 a b) (at level 1).
Notation "a '{' 'hypervisor_context' '/' 'api_page_pool_size' : b '}'"
  := (update_hypervisor_api_page_pool_size a b) (at level 1).
Notation "a '{' 'hypervisor_context' '/' 'ffa_share_state' : b '}'"
  := (update_hypervisor_ffa_share_state a b) (at level 1).
Notation "a '{' 'hypervisor_context' '/' 'fresh_index_for_ffa_share_state' : b '}'"
  := (update_hypervisor_fresh_index_for_ffa_share_state a b) (at level 1).
Notation "a '{' 'hypervisor_context' '/' 'mem_properties' : b '}'"
  := (update_hypervisor_mem_properties a b) (at level 1).
Notation "a '{' 'hypervisor_context' '/' 'vm_count' : b '}'"
  := (update_hypervisor_vm_count a b) (at level 1).
Notation "a '{' 'hypervisor_context' '/' 'vms_contexts' : b '}'"
  := (update_hypervisor_vms_contexts a b) (at level 1).

(** update vm userspace context *)
Notation "a '{' 'client_cur_vcpu_index' : b '}'"
  := (update_cur_vcpu_index_in_vm_userspace_context a b) (at level 1).
Notation "a '{' 'client_vcpus' : b '}'"
  := (update_vcpus_in_vm_userspace_context a b) (at level 1).
Notation "a '{' 'client_vcpus_contexts' : b '}'"
  := (update_vcpus_contexts_in_vm_userspace_context a b) (at level 1).

(** update abstract state *)
Notation "a '{' 'FFA_version_number' : b '}'" :=
  (update_FFA_version_number a b) (at level 1).
Notation "a '{' 'is_hvc_mode' : b '}'" :=
  (update_is_hvc_mode a b) (at level 1).
Notation "a '{' 'use_stage1_table' : b '}'" :=
  (update_use_stage1_table a b) (at level 1).
Notation "a '{' 'cur_user_entity_id' : b '}'" :=
  (update_cur_user_entity_id a b) (at level 1).
Notation "a '{' 'hypervisor_context' : b '}'" :=
  (update_hypervisor_context a b) (at level 1).
Notation "a '{' 'vms_userspaces' : b '}'" :=
  (update_vms_userspaces a b) (at level 1).
Notation "a '{' 'system_log' : b '}'" :=
  (update_system_log a b) (at level 1).
 
(* end hide *)
