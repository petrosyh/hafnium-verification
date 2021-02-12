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
Require Import FFAMemoryHypCall.
Require Import FFAMemoryHypCallIntro.
Require Export FFAMemoryHypCallDescriptorState.

Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Require Import Maps.
Set Implicit Arguments.

(*************************************************************)
(** *         State definitions                              *)
(*************************************************************)
Section PtrTreeLibrary.

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

End PtrTreeLibrary.

Variable Z_to_string: Z -> string.
Extract Constant Z_to_string =>
"fun z -> (HexString.of_Z z)"
.

(* Variable A: Type. *)
Definition A : Type := positive * Z.

Definition A_to_string (a: A): string :=
  "(" ++ (Z_to_string (Zpos' (fst a))) ++ ", " ++ (Z_to_string (snd a)) ++ ")"
.

(*************************************************************)
(** *         memory and ptable                              *)
(*************************************************************)
Section MEM_AND_PTABLE.

  Context `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}.
  
  (** memory states on memory addresses *)
  (** 
     We do not consider contents inside the memory, but we do care about its properties -
     and those properties are necessary for us to prove whether each component in the system
     accesses memory in a valid way. Therefore, we have the following mapping from
     each memory address to several properties. 

     There are several dependencies between those properties. 
     So, Those information are somewhat redundant, but 
     we keep them in terms of explicit information that we can easily infer the curretn state of 
     each address in the memory. *)
  (** Indicates who is the owner of the memory *)
  Inductive OWNERSHIP_STATE_TYPE :=
  | Owned (id : ffa_UUID_t)
  | NotOwned.
  
  (** Indicates access state of each memory address *)
  Inductive ACCESS_STATE_TYPE :=
  | NoAccess 
  | ExclusiveAccess (accessor: ffa_UUID_t)
  (** Note that accesssors will not be nil 
   - SharedAccess with one UUID differs from ExclusiveAccess *)
  | SharedAccess (accessors : list ffa_UUID_t).

  (** Check whether the page is dirty or clean. Some FFA calls clean the memory, and it is 
      one of important behaviours that we have to observe. In this sense, we explicitly 
      model them. 
      
      Those values are necessary for us to distinguish behaviours caused by zero memory flags values 
      in the descriptor 
   *)
  Inductive MEM_DIRTY_TYPE := 
  | MemClean
  (** Note that accesssors will not be nil
   - We can treat "MemWritten nil" as a MemClean, but we try to explicitly distinguish them *)                    
  | MemWritten (writer: list ffa_UUID_t). (** who wrote values in the address *)
  
  (** This memory properties are key features that we may hope to guarantee in our system -
      There are some redundant information in between them, and we may need to 
      make invariants to guarantee well-formed relations between the following different properties 
      (and other parts of the abstract state *)
  Record MemGlobalProperties :=
    mkMemGlobalProperties {
        (** there can be only one owner *)
        owned_by : OWNERSHIP_STATE_TYPE;
        (** access information *)
        accessible_by : ACCESS_STATE_TYPE;
        (** check whether there are written contents in the memory or not *)
        mem_dirty: MEM_DIRTY_TYPE;
      }.

  (** key is a base address of memory region *)
  Definition mem_global_properties_pool := ZTree.t MemGlobalProperties.

  (** It indicates the owned infromation in memory local properties.
      This needs to be consistent with OwnershipState. *)
  Inductive MEM_LOCAL_OWNED_TYPE :=
  | LocalOwned
  | LocalBorrowed (owner : ffa_UUID_t).
  (* TODO: we need to check whether the following MemAttributes needs to be a global attributes 
     or a local attributes *)
  (** Indicates whether the memory is device memory or normal memory, and corresponding 
     attributes of that page. If the page is a normal memory, the memory is shareable if the 
     shareability flag indicates it is possible. *)
  (** This memory attributes need to be consistent with AccessState. *)
  Inductive MEM_ATTRIBUTES_TYPE :=
  | MemAttributes_Undef (** initial value *)
  | MemAttributes_DeviceMem (cacheability_type: FFA_MEMORY_CACHEABILITY_TYPE_2)
  | MemAttributes_NormalMem (cacheability_type: FFA_MEMORY_CACHEABILITY_TYPE_1)
                            (shareability_type: FFA_MEMORY_SHAREABILITY).  
  
  Record MemLocalProperties :=
    mkMemLocalProperties {
        mem_local_owned:  MEM_LOCAL_OWNED_TYPE;
        (** Instruction and data access property *)
        (** They specifies executable / non-executalbe and read / writer permissions *)
        instruction_access_property : FFA_INSTRUCTION_ACCESS_TYPE;
        data_access_property: FFA_DATA_ACCESS_TYPE;
        (** memory attributes - e.g., sharable or cacheability *)
        mem_attribute : MEM_ATTRIBUTES_TYPE;
      }.

  Definition gen_borrow_mem_local_properties (lender : ffa_UUID_t) (iap : FFA_INSTRUCTION_ACCESS_TYPE)
             (dap : FFA_DATA_ACCESS_TYPE) (attr: MEM_ATTRIBUTES_TYPE) :=
    mkMemLocalProperties (LocalBorrowed lender) iap dap attr.
  
  Definition gen_borrow_mem_local_properties_wrapper (lender : ffa_UUID_t) (local_props: MemLocalProperties) :=
    gen_borrow_mem_local_properties lender (local_props.(instruction_access_property))
                                    (local_props.(data_access_property)) (local_props.(mem_attribute)).
  
  Definition own_mem_local_properties (iap : FFA_INSTRUCTION_ACCESS_TYPE)
             (dap : FFA_DATA_ACCESS_TYPE) (attr: MEM_ATTRIBUTES_TYPE) :=
    mkMemLocalProperties LocalOwned iap dap attr.

  Definition gen_own_mem_local_properties_wrapper (local_props: MemLocalProperties) :=
     own_mem_local_properties (local_props.(instruction_access_property))
                              (local_props.(data_access_property)) (local_props.(mem_attribute)).

 
  (** key is an address of memory *)
  Definition mem_local_properties_pool := ZTree.t MemLocalProperties.
  (** key is a entity id of the system *)  
  Definition mem_local_properties_global_pool := ZTree.t mem_local_properties_pool.

  (** There are relations between mem_global_properties and mem_local_properties.
      For example, if a certain address in access_state of MemGlobalProperties is mapped with 
      SharedAccess 1, then there should be a valid element for the address in the mem local properties pool for entity 1.
      And, the corresponding mem_local_owned of the MemLocalProperties for entity 1 has to be
      either Owned or LocalBorrowed with the valid owner value that are marked in OwnershipState of the MemGlobalProperties. *)
  (** There are some redundant information in MemGlobalProperties and MemLocalProperties.
      However, those redundancies sometimes help us to prove memory related properties easy
      (when we have invariants about relations between those redundant information). *)
  (* TODO: add those constraints in HafniumMemoryManagementContext *)
  Record MemProperties :=
    mkMemProperties {
        mem_global_properties: mem_global_properties_pool;
        mem_local_properties: mem_local_properties_global_pool;
      }.

End MEM_AND_PTABLE.

Section MEM_AND_PTABLE_CONTEXT.
  (** In top level, we do not need to specify ptable in detail. 
     In this sense, we try to abstract the definition of ptable. 
     => gets the input address (e.g., va or ipa) and return the address (e.g., ipa or pa) *)
  (** Filling out details of those definitions are user's obligations *)
  Class AddressTranslation `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS} :=
    {
    (** address translation funciton in ptable. There are two possible cases 
       1. provides the entire address translation from 
       the root level to the bottom level 
       2. provides the only one level address translation. 
       Among them, our high-level model assumes the following ptable uses the second approach *)
    hafnium_address_translation_table
      (input_addr:  ffa_address_t) : option ffa_address_t;
    vm_address_translation_table
      (vm_id : ffa_UUID_t) (input_addr: ffa_address_t) : option ffa_address_t;
    }.

  
  Class HafniumMemoryManagementContext `{address_translation: AddressTranslation} :=
    {
    (** address low and high *)
    address_low : ffa_address_t;
    address_high : ffa_address_t;

    alignment_value : Z; (** usually 4096 *)

    (** properties *)
    well_formed_granuale : Z.modulo granuale alignment_value = 0;
    alignment_value_non_zero_prop :
      alignment_value > 0;
    address_low_alignment_prop :
      (Z.modulo address_low alignment_value)%Z = 0;
    address_high_alignment_prop :
      (Z.modulo (address_high + 1) alignment_value)%Z = 0;

    (** all results of  the address translation needs to be in betweeen low and high *)
    address_translation_table_prop :
      forall addr,
        match hafnium_address_translation_table addr with
        | Some addr' => (address_low <= addr' <= address_high)
        | _ => True
        end;
    (* TODO: add more invariants *)    
    }.

End MEM_AND_PTABLE_CONTEXT.

(*************************************************************)
(**         VM CONTEXT                                       *)
(*************************************************************)
(** This one is necessary to model context saving/restoring of FFA ABI 
  - When looking at Hafnium, related definitions are in
   1) "/inc/hf/vm.h"
   2) "/inc/hf/.h"
   2) "/src/arch/aarch64/inc/hf/arch/types.h" 
*)
Section FFA_VM.

  Context `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}.
  
  (** In Hafnium: registers in "/src/arch/aarch64/inc/hf/arch/types.h" 
  /** Type to represent the register state of a vCPU. */
  struct arch_regs {
          /* General purpose registers. */
          uintreg_t r[NUM_GP_REGS];
          uintreg_t pc;
          uintreg_t spsr;
  *)

  (** In Hafnium: VM struct in "/inc/hf/vm.h" 
   struct vm {
           ffa_vm_id_t id;
           struct smc_whitelist smc_whitelist;
    
           /** See api.c for the partial ordering on locks. */
           struct spinlock lock;
           ffa_vcpu_count_t vcpu_count;
           struct vcpu vcpus[MAX_CPUS];
           struct mm_ptable ptable;
           struct mailbox mailbox;
           char log_buffer[LOG_BUFFER_SIZE];
           uint16_t log_buffer_length;
    
           /**
            * Wait entries to be used when waiting on other VM mailboxes. See
            * comments on `struct wait_entry` for the lock discipline of these.
            */
           struct wait_entry wait_entries[MAX_VMS];
    
           atomic_bool aborting;
    
           /** Arch-specific VM information. */
           struct arch_vm arch;
   };
   *)

  (** Simplified vcpu context - we only includes some registers - actually only FFA related values *)
  Record ArchRegs :=
    mkArchRegs {
        regs: FFA_value_type;
      }.
  Record VCPU_struct :=
    mkVCPU_struct{
        (** the vm that is currently associated with this vcpu*)
        cpu_id : option ffa_CPU_ID_t; (** the connect *)
        vm_id: option ffa_UUID_t;
        vcpu_regs: ArchRegs;
      }.

  Record MAILBOX_struct :=
    mkMAILBOX_struct {
        send : ffa_mailbox_send_msg_t;
        recv : ffa_mailbox_recv_msg_t;
        recv_sender : ffa_UUID_t;
        recv_size : Z;
        recv_func : FFA_FUNCTION_TYPE;
      }.
                      
  
  (** Simplified VM context - we assume VM only has own vcpu *)
  Record VM_struct :=
    mkVM_struct {
        cur_vcpu_index : ffa_VCPU_ID_t;
        (** number of vcpus that are assigned into this VM *)
        vcpu_num: Z;
        vcpus : ZTree.t VCPU_struct;
        (** ptable for each VM is defined in AddressTranslation class *)

        (** Each VM has its own mailbox. *)
        (** IN FFA ABI handling, the actual information for the handling is in mailboxes. 
           In this sense, we includes this informaiton in this state definition *)
        mailbox : MAILBOX_struct;
        (** all other parts are ignored at this moment *)        
      }.

End FFA_VM.

Section FFA_VM_CONTEXT.
  
  Class VMContext `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS} := 
    {
    vcpu_max_num : Z;
    vcpu_num_prop (vm: VM_struct) : 0 < vm.(vcpu_num) <= vcpu_max_num;
    cur_vcpu_id_prop (vm: VM_struct) : 0 <= vm.(cur_vcpu_index) < vm.(vcpu_num);
    (* TODO: add more invariants *)
    }.

End FFA_VM_CONTEXT.

(*************************************************************)
(** *                   VM user space                        *)
(*************************************************************)
(** Adding several things in here is possible, but we focus on 
    FFA-related things in this VM userspace modeling. We are able to add
    any other things according to our decision *)
Section VM_CLIENTS.

  Context `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}.
  
  Record VM_USERSPACE_struct :=
    mkVM_USERSPACE_struct {
        userspace_cur_vcpu_index : ffa_VCPU_ID_t;
        (** number of vcpus that are assigned into this VM *)
        userspace_vcpu_num: Z;
        (** vcpu does not need to be allocated into one VM in a consecutive manner. 
            For example, when vcpu_num is 3 for this VM, and assinged vcpu ids can be 0, 3, and 5. *)
        userspace_vcpus : ZTree.t VCPU_struct;
        (** all other parts are ignored at this moment *)
      }.

End VM_CLIENTS.

Section VM_CLIENTS_CONTEXT.

  Class VMUserSpaceContext `{vm_context: VMContext} := 
    {
    userspace_vcpu_num_prop (vm_userspace: VM_USERSPACE_struct) :
      0 < vm_userspace.(userspace_cur_vcpu_index) <= vcpu_max_num;
    userspace_cur_vcpu_id_prop (vm_userspace: VM_USERSPACE_struct) :
      0 <= vm_userspace.(userspace_cur_vcpu_index) < vm_userspace.(userspace_vcpu_num);
    (* TODO: add more invariants *)
    }.
  
End VM_CLIENTS_CONTEXT.

(*************************************************************)
(** *      AbstractState for FFA modeling                    *)
(*************************************************************)
Section AbstractState.

  Context `{ffa_types_and_constants: !FFA_TYPES_AND_CONSTANTS}.
  
  (** It represents CPU object, but it is currently empty. *)
  Record CPU_struct :=
    mkCPU_struct { 
      }.
  
  (** In Hafnium: Hafnium specific values *)
  (**
  /** The maximum number of recipients a memory region may be sent to. */
  #define MAX_MEM_SHARE_RECIPIENTS 1
   
  /**
   * The maximum number of memory sharing handles which may be active at once. A
   * DONATE handle is active from when it is sent to when it is retrieved; a SHARE
   * or LEND handle is active from when it is sent to when it is reclaimed.
   */
  #define MAX_MEM_SHARES 100
   *)

  Definition MAX_MEM_SHARE_RECIPIENTS_Z := 1.
  Definition MAX_MEM_SHARE_Z := 100.

  (* TODO: FF-A document does not explicitly define this structure, so we need abstractions for the following definition  *)
  (** Hafnium's data structure for FFA memory management ABI handling 
  struct ffa_memory_share_state {
          /**
           * The memory region being shared, or NULL if this share state is
           * unallocated.
           */
          struct ffa_memory_region *memory_region;
   
          /**
           * The FF-A function used for sharing the memory. Must be one of
           * FFA_MEM_DONATE_32, FFA_MEM_LEND_32 or FFA_MEM_SHARE_32 if the
           * share state is allocated, or 0.
           */
          uint32_t share_func;
   
          /**
           * Whether each recipient has retrieved the memory region yet. The order
           * of this array matches the order of the attribute descriptors in the
           * memory region descriptor. Any entries beyond the attribute_count will
           * always be false.
           */
          bool retrieved[MAX_MEM_SHARE_RECIPIENTS];
  };
   
  static struct ffa_memory_share_state share_states[MAX_MEM_SHARES];
 *)

  Record FFA_memory_share_state_struct :=
    mkFFA_memory_share_state_struct {
        memory_region : FFA_memory_region_struct;
        share_func : FFA_FUNCTION_TYPE;
        retrieved : ZMap.t bool;
      }.

  Definition share_state_pool := ZTree.t FFA_memory_share_state_struct.
  
  Record Hafnium_struct :=
    mkHafnium_struct {
        (** For cpu information *)
        current_cpu_id : Z;
        cpu_num : Z;
        cpus: ZTree.t CPU_struct;

        (** Registers that we have to keep to handle FFA ABIs *)
        (** The following register keeps the currently existing VCPU information that is 
            associated with the current hvc_call. via that VCPU, it is possible for us to find out 
            the sender's information for ABI calls 
           
            The related part in the Hafnium code is the following function in
            "/src/arch/aarch64/hypervisor/handler.c"
            static struct vcpu *current(void)
            {
                    return (struct vcpu * )read_msr(tpidr_el2);
            }
            *)
        (** List of registers  will be increasing to model other behaviours
            - e.g., the register for TLB invalidate *)
        tpidr_el2 : option VCPU_struct;
        
        (** For API - FFA ABI handlings *) 
        (** Free pages at the top level. those pages need to be used for the 
            FFA ABI handlings. But, to simplify it (like what we have currently doing in
            page_table, we represent it as a size of free pages. Then, we will only increase / decrease
            the number when we allocate pages or free those pages while handling FFA ABIs *)
        api_page_pool_size : Z;
        (** ffa_share_state is for ffa communications  *)
        ffa_share_state: share_state_pool;

        fresh_index_for_ffa_share_state : Z;
        
        (** ptable is defined in AddressTranslation class *)
        (** Memory attributes for key is an address *) 
        mem_properties : MemProperties;
        
        (** vm count *)
        vm_count : Z;
        (** vm contexts saved in hafnium *)
        (** VM ids are consecutively assigned. *) 
        vms_contexts :  ZTree.t VM_struct;
      }.
  
  Record AbstractState :=
    mkAbstractState{
        (** The number to memorize the version of FFA - See 8.1 FFA_VERSION of the document and 
            FFAMemoryHypCallIntro.v file for more details *)
        FFA_version_number: ffa_version_number_t; 
        (** the entity that is currently running. *)
        cur_entity_id: ffa_UUID_t;
        (** hafnium global stage *)
        hafnium_context: Hafnium_struct;
        (** vm clinets *) 
        vms_userspaces : ZTree.t VM_USERSPACE_struct; 
      }.

End AbstractState.

Section AbstractStateContext.

  (** All contexts for high-level modeling. We currently merge all contexts that we have declared in here 
      to avoid conflicts due to type classes *)
  Class AbstractStateContext
        `{ffa_types_and_constants: !FFA_TYPES_AND_CONSTANTS}
        `{address_translation: !AddressTranslation (ffa_types_and_constants := ffa_types_and_constants)}
        `{hafnium_memory_management_context : !HafniumMemoryManagementContext (address_translation := address_translation)}
        `{vm_context : !VMContext (ffa_types_and_constants := ffa_types_and_constants)} 
        `{vm_user_space_context : !VMUserSpaceContext (vm_context := vm_context)} :=
    {
    hafnium_id : ffa_UUID_t := 0;
    primary_vm_id: ffa_UUID_t;
    secondary_vm_ids : list ffa_UUID_t;
    vm_ids := primary_vm_id::secondary_vm_ids; 
    entity_list : list ffa_UUID_t := hafnium_id::vm_ids;

    (** mailbox to/from descriptors *)
    mailbox_send_msg_to_region_struct : ffa_mailbox_send_msg_t -> option FFA_memory_region_struct;
    mailbox_send_msg_to_relinqiush_struct: ffa_mailbox_send_msg_t -> option FFA_memory_relinquish_struct;
    mailbox_send_msg_to_Z : ffa_mailbox_send_msg_t -> option Z;
    region_struct_to_mailbox_send_msg : FFA_memory_region_struct -> option ffa_mailbox_send_msg_t;
    relinqiush_struct_to_mailbox_send_msg : FFA_memory_relinquish_struct -> option ffa_mailbox_send_msg_t;
    Z_to_mailbox_send_msg : Z -> option ffa_mailbox_send_msg_t;

    mailbox_recv_msg_to_region_struct : ffa_mailbox_recv_msg_t -> option FFA_memory_region_struct;
    mailbox_recv_msg_to_relinqiush_struct: ffa_mailbox_recv_msg_t -> option FFA_memory_relinquish_struct;
    mailbox_recv_msg_to_Z: ffa_mailbox_recv_msg_t -> option Z;
    region_struct_to_mailbox_recv_msg : FFA_memory_region_struct -> option ffa_mailbox_recv_msg_t;
    relinqiush_struct_to_mailbox_recv_msg : FFA_memory_relinquish_struct -> option ffa_mailbox_recv_msg_t;
    Z_to_mailbox_recv_msg : Z -> option ffa_mailbox_recv_msg_t;
    
    (** We may be able to use some feature of interaction tree for this scheduling? *)
    scheduler : AbstractState -> ffa_UUID_t; 
    
    entity_list_prop := NoDup entity_list;

    cur_entity_id_prop (state : AbstractState) : In state.(cur_entity_id) entity_list;

    initial_state : AbstractState;
    
    (* TODO: we need invariants about fileds, cpu_id and vm_id, in VCPU_struct *)

    (* TODO: add more invariants in here. *)
    (** Separate this well_formedness as two parts - 
       1. Computable parts - return bool
       2. Uncomputable parts - return Prop *)
    well_formed (state: AbstractState) : Prop;
    initial_state_well_formed : well_formed initial_state;
    
    well_formed_guarantee_well_formed_scheduler_result :
      forall st next_id, well_formed st -> scheduler st = next_id -> In next_id vm_ids;

    mem_properties_prop_low_out_of_bound :
      forall addr st, (addr < address_low)%Z ->
                 ZTree.get addr (st.(hafnium_context)).(mem_properties).(mem_global_properties) = None;
    mem_properties_prop_high_out_of_bound :
      forall addr st, (address_high < addr)%Z ->
                 ZTree.get addr (st.(hafnium_context)).(mem_properties).(mem_global_properties) = None;
    mem_properties_prop_not_aligned :
      forall addr st, (Z.modulo addr alignment_value)%Z <> 0 ->
                 ZTree.get addr (st.(hafnium_context)).(mem_properties).(mem_global_properties) = None;
    mem_global_properties_well_formed1 :
      forall addr st,
        (address_low <= addr <= address_high)%Z ->
        (Z.modulo addr alignment_value)%Z = 0 ->
        exists global_properties,
          ZTree.get addr (st.(hafnium_context)).(mem_properties).(mem_global_properties) = Some global_properties;

    mem_properties_consistency1 :
      forall addr st global_properties owner, 
        ZTree.get addr (st.(hafnium_context)).(mem_properties).(mem_global_properties) = Some global_properties ->
        global_properties.(owned_by) = Owned owner ->
        exists local_properties_pool local_properties,
          ZTree.get owner  (st.(hafnium_context)).(mem_properties).(mem_local_properties) = Some local_properties_pool /\
          ZTree.get addr local_properties_pool = Some local_properties /\
          local_properties.(mem_local_owned) = LocalOwned;
    mem_properties_consistency2 :
      forall addr st global_properties owner, 
        ZTree.get addr (st.(hafnium_context)).(mem_properties).(mem_global_properties) = Some global_properties ->
        global_properties.(owned_by) = Owned owner ->
        forall other,
          other <> owner ->
          ((ZTree.get other  (st.(hafnium_context)).(mem_properties).(mem_local_properties) = None) \/
           (exists local_properties_pool,
               ZTree.get other  (st.(hafnium_context)).(mem_properties).(mem_local_properties) = Some local_properties_pool /\
               ZTree.get addr local_properties_pool = None) \/
           (exists local_properties_pool local_properties,
               ZTree.get owner  (st.(hafnium_context)).(mem_properties).(mem_local_properties) = Some local_properties_pool /\
               ZTree.get addr local_properties_pool = Some local_properties /\
               local_properties.(mem_local_owned) <> LocalOwned));

    }.

End AbstractStateContext.

Section AbstractStateUpdate.  

  Context `{ffa_types_and_constants: !FFA_TYPES_AND_CONSTANTS}.
  (** update functions for better readability *)
  
  (** update memory global properties *)
  Definition update_owned_by_in_mem_global_properties (a : MemGlobalProperties) b :=
    mkMemGlobalProperties b (a.(accessible_by)) (a.(mem_dirty)).
  
  Definition update_accessible_by_in_mem_global_properties (a : MemGlobalProperties) b :=
    mkMemGlobalProperties (a.(owned_by)) b (a.(mem_dirty)).
  
  Definition update_mem_dirty_in_mem_global_properties (a : MemGlobalProperties) b :=
    mkMemGlobalProperties (a.(owned_by)) (a.(accessible_by)) b.
  
  (** update memory local properties *)
  Definition update_mem_local_owned_in_mem_local_properties (a: MemLocalProperties) b :=
    mkMemLocalProperties b (a.(instruction_access_property))  (a.(data_access_property)) (a.(mem_attribute)).
  
  Definition update_instruction_access_property_in_mem_local_properties (a : MemLocalProperties) b :=
    mkMemLocalProperties (a.(mem_local_owned)) b (a.(data_access_property)) (a.(mem_attribute)).
  
  Definition update_data_access_property_in_mem_local_properties (a : MemLocalProperties) b :=
    mkMemLocalProperties (a.(mem_local_owned)) (a.(instruction_access_property)) b (a.(mem_attribute)).

  Definition update_mem_attributes_in_mem_local_properties (a : MemLocalProperties) b :=
    mkMemLocalProperties (a.(mem_local_owned)) (a.(instruction_access_property)) (a.(data_access_property)) b.

  (** update memory properties *)
  Definition update_mem_global_properties_in_mem_properties (a : MemProperties) b :=
    mkMemProperties b a.(mem_local_properties). 

  Definition update_mem_local_properties_in_mem_properties (a : MemProperties) b :=
    mkMemProperties a.(mem_global_properties) b.

  (* vm_context update *)
  Definition update_cur_vcpu_index_in_vm_context (a : VM_struct) b :=
    mkVM_struct b (a.(vcpu_num)) (a.(vcpus)) (a.(mailbox)).

  Definition update_vcpu_num_in_vm_context (a : VM_struct) b :=
    mkVM_struct (a.(cur_vcpu_index)) b (a.(vcpus)) (a.(mailbox)).

  Definition update_vcpus_in_vm_context (a : VM_struct) b :=
    mkVM_struct (a.(cur_vcpu_index)) (a.(vcpu_num)) b (a.(mailbox)).

  Definition update_mailbox_in_vm_context (a : VM_struct) b :=
    mkVM_struct (a.(cur_vcpu_index)) (a.(vcpu_num)) (a.(vcpus)) b.  
  
  
  (** update hafnium context *)
  Definition update_current_cpu_id_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct b (a.(cpu_num)) (a.(cpus)) (a.(tpidr_el2)) (a.(api_page_pool_size))
                     (a.(ffa_share_state))
                     (a.(fresh_index_for_ffa_share_state))
                     (a.(mem_properties)) (a.(vm_count)) (a.(vms_contexts)).

  Definition update_cpu_num_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct (a.(current_cpu_id)) b (a.(cpus)) (a.(tpidr_el2)) (a.(api_page_pool_size))
                     (a.(ffa_share_state))
                     (a.(fresh_index_for_ffa_share_state))
                     (a.(mem_properties)) (a.(vm_count)) (a.(vms_contexts)).

  Definition update_cpus_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct (a.(current_cpu_id)) (a.(cpu_num)) b (a.(tpidr_el2)) (a.(api_page_pool_size))
                     (a.(ffa_share_state))
                     (a.(fresh_index_for_ffa_share_state))
                     (a.(mem_properties)) (a.(vm_count)) (a.(vms_contexts)).
  
  Definition update_tpidr_el2_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus)) b (a.(api_page_pool_size))
                     (a.(ffa_share_state))
                     (a.(fresh_index_for_ffa_share_state))
                     (a.(mem_properties)) (a.(vm_count)) (a.(vms_contexts)).

  Definition update_api_page_pool_size_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus)) (a.(tpidr_el2)) b
                     (a.(ffa_share_state))
                     (a.(fresh_index_for_ffa_share_state))
                     (a.(mem_properties)) (a.(vm_count)) (a.(vms_contexts)).

  Definition update_ffa_share_state_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus)) (a.(tpidr_el2))
                     (a.(api_page_pool_size)) b
                     (a.(fresh_index_for_ffa_share_state))
                     (a.(mem_properties)) (a.(vm_count)) (a.(vms_contexts)).

  Definition update_fresh_index_for_ffa_share_state_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus)) (a.(tpidr_el2))
                     (a.(api_page_pool_size)) (a.(ffa_share_state)) b
                     (a.(mem_properties)) (a.(vm_count)) (a.(vms_contexts)).

  
  Definition update_mem_properties_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus)) (a.(tpidr_el2))
                     (a.(api_page_pool_size)) (a.(ffa_share_state))
                     (a.(fresh_index_for_ffa_share_state))
                     b (a.(vm_count)) (a.(vms_contexts)).
  
  Definition update_vm_count_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus)) (a.(tpidr_el2))
                     (a.(api_page_pool_size)) (a.(ffa_share_state))
                     (a.(fresh_index_for_ffa_share_state))
                     (a.(mem_properties)) b
                     (a.(vms_contexts)).

  Definition update_vms_contexts_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct (a.(current_cpu_id)) (a.(cpu_num)) (a.(cpus)) (a.(tpidr_el2))
                     (a.(api_page_pool_size)) (a.(ffa_share_state))
                     (a.(fresh_index_for_ffa_share_state))
                     (a.(mem_properties))
                     (a.(vm_count)) b.
   

  (** vm_userspace update *)
  Definition update_cur_vcpu_index_in_vm_userspace (a : VM_USERSPACE_struct) b :=
    mkVM_USERSPACE_struct b (a.(userspace_vcpu_num)) (a.(userspace_vcpus)).

  Definition update_vcpu_num_in_vm_userspace (a : VM_USERSPACE_struct) b :=
    mkVM_USERSPACE_struct (a.(userspace_cur_vcpu_index)) b (a.(userspace_vcpus)).

  Definition update_vcpus_in_vm_userspace (a : VM_USERSPACE_struct) b :=
    mkVM_USERSPACE_struct (a.(userspace_cur_vcpu_index)) (a.(userspace_vcpu_num)) b.

  (** update *)
  Definition update_FFA_version_number (a: AbstractState) b := 
    mkAbstractState b a.(cur_entity_id) a.(hafnium_context) a.(vms_userspaces).
  
  Definition update_cur_entity_id (a : AbstractState) b :=
    mkAbstractState a.(FFA_version_number) b a.(hafnium_context) a.(vms_userspaces).

  Definition update_hafnium_context (a : AbstractState) b :=
    mkAbstractState a.(FFA_version_number) a.(cur_entity_id) b a.(vms_userspaces).

  Definition update_hafnium_current_cpu_id (a: AbstractState) b :=
    update_hafnium_context a (update_current_cpu_id_in_hafnium_context a.(hafnium_context) b).

  Definition update_hafnium_cpu_num (a: AbstractState) b :=
    update_hafnium_context a (update_cpu_num_in_hafnium_context a.(hafnium_context) b).

  Definition update_hafnium_cpus (a: AbstractState) b :=
    update_hafnium_context a (update_cpus_in_hafnium_context a.(hafnium_context) b).
  
  Definition update_hafnium_tpidr_el2 (a: AbstractState) b :=
    update_hafnium_context a (update_tpidr_el2_in_hafnium_context a.(hafnium_context) b).

  Definition update_hafnium_api_page_pool_size (a: AbstractState) b :=
    update_hafnium_context a (update_api_page_pool_size_in_hafnium_context a.(hafnium_context) b).

  Definition update_hafnium_ffa_share_state (a: AbstractState) b :=
    update_hafnium_context a (update_ffa_share_state_in_hafnium_context a.(hafnium_context) b).

  Definition update_hafnium_fresh_index_for_ffa_share_state (a: AbstractState) b :=
    update_hafnium_context a (update_fresh_index_for_ffa_share_state_in_hafnium_context
                                a.(hafnium_context) b).

  Definition update_hafnium_mem_properties (a: AbstractState) b :=
    update_hafnium_context a (update_mem_properties_in_hafnium_context a.(hafnium_context) b).
  
  Definition update_hafnium_vm_count (a: AbstractState) b :=
    update_hafnium_context a (update_vm_count_in_hafnium_context a.(hafnium_context) b).
  
  Definition update_hafnium_vms_contexts (a: AbstractState) b :=
    update_hafnium_context a (update_vms_contexts_in_hafnium_context a.(hafnium_context) b).
  
  Definition update_vms_userspaces (a : AbstractState) b :=
    mkAbstractState a.(FFA_version_number) a.(cur_entity_id) a.(hafnium_context) b.
  
End AbstractStateUpdate.

(** update memory global properties *)
Notation "a '{' 'owned_by' : b '}'" := (update_owned_by_in_mem_global_properties a b) (at level 1).
Notation "a '{' 'accessible_by' : b '}'" := (update_accessible_by_in_mem_global_properties a b) (at level 1).
Notation "a '{' 'mem_dirty' : b '}'" := (update_mem_dirty_in_mem_global_properties a b) (at level 1).
  
(** update memory local properties *)
Notation "a '{' 'mem_local_owned' : b '}'" := (update_mem_local_owned_in_mem_local_properties a b) (at level 1).
Notation "a '{' 'instruction_access_property' : b '}'" := (update_instruction_access_property_in_mem_local_properties a b) (at level 1).
Notation "a '{' 'data_access_property' : b '}'" := (update_data_access_property_in_mem_local_properties a b) (at level 1).
Notation "a '{' 'mem_attributes' : b '}'" := (update_mem_attributes_in_mem_local_properties a b) (at level 1).

(** update memory properties *)
Notation "a '{' 'mem_global_properties' : b '}'" := (update_mem_global_properties_in_mem_properties a b) (at level 1).
Notation "a '{' 'mem_local_properties' : b '}'" := (update_mem_local_properties_in_mem_properties a b) (at level 1).

(** update vm context *)
Notation "a '{' 'vm_cur_vcpu_index' : b '}'"
  := (update_cur_vcpu_index_in_vm_context a b) (at level 1).
Notation "a '{' 'vm_vcpu_num' : b '}'"
  := (update_vcpu_num_in_vm_context a b) (at level 1).
Notation "a '{' 'vm_vcpus' : b '}'"
  := (update_vcpus_in_vm_context a b) (at level 1).
Notation "a '{' 'vm_mailbox' : b '}'"
  := (update_mailbox_in_vm_context a b) (at level 1).

(** update hafnium context *)
Notation "a '{' 'hafnium_context' '/' 'current_cpu_id' : b '}'"
  := (update_hafnium_current_cpu_id a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'cpu_num' : b '}'"
  := (update_hafnium_cpu_num a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'cpus' : b '}'"
  := (update_hafnium_cpus a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'tpidr_el2' : b '}'"
  := (update_hafnium_tpidr_el2 a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'api_page_pool_size' : b '}'"
  := (update_hafnium_api_page_pool_size a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'ffa_share_state' : b '}'"
  := (update_hafnium_ffa_share_state a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'fresh_index_for_ffa_share_state' : b '}'"
  := (update_hafnium_fresh_index_for_ffa_share_state a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'mem_properties' : b '}'"
  := (update_hafnium_mem_properties a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'vm_count' : b '}'"
  := (update_hafnium_vm_count a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'vms_contexts' : b '}'"
  := (update_hafnium_vms_contexts a b) (at level 1).


(** update vm userspace context *)
Notation "a '{' 'userspace_cur_vcpu_index' : b '}'"
  := (update_cur_vcpu_index_in_vm_userspace a b) (at level 1).
Notation "a '{' 'userspace_vcpu_num' : b '}'"
  := (update_vcpu_num_in_vm_userspace a b) (at level 1).
Notation "a '{' 'userspace_vcpus' : b '}'"
  := (update_vcpus_in_vm_userspace a b) (at level 1).

(** update abstract state *)
Notation "a '{' 'FFA_version_number' : b '}'" := (update_FFA_version_number a b) (at level 1).
Notation "a '{' 'cur_entity_id' : b '}'" := (update_cur_entity_id a b) (at level 1).
Notation "a '{' 'hafnium_context' : b '}'" := (update_hafnium_context a b) (at level 1).
Notation "a '{' 'vms_userspaces' : b '}'" := (update_vms_userspaces a b) (at level 1).

 
