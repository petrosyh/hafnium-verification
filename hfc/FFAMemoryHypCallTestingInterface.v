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
Require Import Any.
Require Import Lang.
Require Import Values.
Require Import Integers.
Require Import Constant.
Require Import Decision.

(* FFA Memory management related parts *)
Require Export FFAMemoryHypCall.
Require Export FFAMemoryHypCallIntro.
Require Export FFAMemoryHypCallDescriptorState.
Require Export FFAMemoryHypCallState.
Require Export FFAMemoryHypCallCoreTransition.
Require Export FFAMemoryHypCallAdditionalStepsAuxiliaryFunctions.
Require Export FFAMemoryHypCallAdditionalSteps.


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

(** This file contains definitions that are necessary for providing testing interfaces. 
    They are usually contains Z type (or integer type) values that are relevant to several 
    inductive type values in other files. 
*)

(*************************************************************)
(** *                 FFA Interface Values                   *) 
(*************************************************************)
(** This section defines Z type interface values for FFA calls *)

Section FFA_DATATYPES.

  Context `{abstract_state_context: AbstractStateContext}.
  
  (** The following types are defined in Chapter 11 (Memory management interfaces document) 
      They are ignored in our modeling. 
   - [FFA_MEM_DONATE]: 0x84000071
   - [FFA_MEM_LEND]: 0x84000072
   - [FFA_MEM_SHARE]: 0x84000073
   - [FFA_MEM_RETRIEVE_REQ]: 0x84000074
   - [FFA_MEM_RETRIEVE_RESP]: 0x84000075
   - [FFA_MEM_RELINQUISH]: 0x84000076
   - [FFA_MEM_RECLAIM]: 0x84000077
   *)
      
  Definition FFA_MEM_DONATE_32 : Z := 2214592625.
  Definition FFA_MEM_LEND_32 : Z := 2214592626.
  Definition FFA_MEM_SHARE_32 : Z := 2214592627.
  Definition FFA_MEM_RETRIEVE_REQ_32 : Z := 2214592628.
  Definition FFA_MEM_RETRIEVE_RESP_32 : Z := 2214592629.
  Definition FFA_MEM_RELINGQUISH_32 : Z := 2214592630.
  Definition FFA_MEM_RECLAIM_32 : Z := 2214592631.

  (** The followings are for return values of FFA interface calls. *)
  (** The following numbers are defined in Chapter 7, especially in Table 7.2: Error status codes
   - [FFA_NOT_SUPPORTED]: -1
   - [FFA_INVALID_PARAMETERS]: -2
   - [FFA_NO_MEMORY]: -3
   - [FFA_BUSY]: -4
   - [FFA_INTERRUPTED]: -5
   - [FFA_DENIED]: -6
   - [FFA_RETRY]: -7
   - [FFA_ABORTED]: -8
  *)

  Definition FFA_NOT_SUPPORTED_32 : Z := -1.
  Definition FFA_INVALID_PARAMETERS_32 : Z := -2.
  Definition FFA_NO_MEMORY_32 : Z := -3.
  Definition FFA_BUSY_32 : Z := -4.
  Definition FFA_INTERRUPTED_32 : Z := -5.
  Definition FFA_DENIED_32 : Z := -6.
  Definition FFA_RETRY_32 : Z := -7.
  Definition FFA_ABORTED_32 : Z := -8.

  (** The following numbers are also defined in Chapter 7
      - [FFA_ERROR]: 0x84000060
      - [FFA_SUCCESS]: 0x84000061
   *)
  Definition FFA_ERROR_32 : Z := 2214592608.
  Definition FFA_SUCCESS_32 : Z := 2214592609.

  (** In Hafnium: Defined in "inc/hf/ffa_internal.h" *)
  Definition ffa_error (ffa_error_code: FFA_ERROR_CODE_TYPE) : FFA_value_type :=
    let error_z_value := 
        match ffa_error_code with
        | FFA_NOT_SUPPORTED => -1
        | FFA_INVALID_PARAMETERS => -2 
        | FFA_NO_MEMORY => -3
        | FFA_BUSY => -4
        | FFA_INTERRUPTED => -5
        | FFA_DENIED => -6
        | FFA_RETRY => -7
        | FFA_ABORTED => -8
        end in
    (mkFFA_value_type (FFA_RESULT_CODE_IDENTIFIER (FFA_ERROR ffa_error_code))
                      (ZMap.set 1 error_z_value (ZMap.init 0))). 

  (** In Hafnium: Defined in "inc/vmapi/hf/ffa.h" *)
  Definition ffa_success (handle: Z) :=
    (mkFFA_value_type (FFA_RESULT_CODE_IDENTIFIER (FFA_SUCCESS handle))
                      (ZMap.set 2 (Z.land handle ((Z.shiftl 1 32) - 1)%Z)
                                (ZMap.set 3 (Z.shiftr handle 32) (ZMap.init 0)))).

  Definition ffa_value_gen (ffa_result_value : FFA_RESULT_CODE_TYPE) :=
    match ffa_result_value with
    | FFA_ERROR ffa_error_code => ffa_error ffa_error_code
    | FFA_SUCCESS handle => ffa_success handle
    end.
  
  (** In Hafnium: Hafnium specific values *)

  Definition MAX_MEM_SHARE_RECIPIENTS_Z := 1.
  Definition MAX_MEM_SHARE_Z := 100.

End FFA_DATATYPES.

Notation "'do' X <- A ;;; B" :=
  (match A with Some X => B |
           None => triggerUB "None" end)
    (at level 200, X ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation "'do' X , Y <- A ;;; B" :=
  (match A with Some (X, Y) => B |
           None => triggerUB "None" end)
    (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation "'do' X , Y , Z <- A ;;; B" :=
  (match A with Some (X, Y, Z) => B | None => triggerUB "None" end)
    (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation " 'check' A ;;; B" :=
  (if A then B else Ret None)
    (at level 200, A at level 100, B at level 200)
  : itree_monad_scope.
 
Local Open Scope itree_monad_scope.



(***********************************************************************)
(** *                 Instantiations for contexts                      *)
(***********************************************************************)
(** We provides instantiations for the context that our specifiction
    relies on. *)

(***********************************************************************)
(** **            FFA_TYPES_AND_CONSTANTS instance                     *)
(***********************************************************************)
Definition ffa_memory_region_tag_t := Z.
Definition granuale_shift := 12.

Global Instance ffa_types_and_constants : FFA_TYPES_AND_CONSTANTS :=
  {
  ffa_memory_region_tag_t := ffa_memory_region_tag_t;
  (** - The following two types are for message passings. We use them to record and 
        retrieve descriptor information *)

  (** - Granuale value. It is usually a multiplication of 4096 (4KiB) *)
  granuale := Z.shiftl 1 granuale_shift;
  init_ffa_memory_region_tag := 0;
  }.

(***********************************************************************)
(** **                  DescriptorContext instance                     *)
(***********************************************************************)
Global Instance descriptor_context :
  DescriptorContext (ffa_types_and_constants := ffa_types_and_constants) :=
  {
  make_handle := fun vid value =>
                   if decide (0 <= vid < (Z.shiftl 1 16))
                   then if decide (0 <= value < (Z.shiftl 1 16))
                        then Some (Z.lor (Z.shiftl vid 16) value)
                        else None
                   else None;
  get_value := fun handle =>
                 let mask := ((Z.shiftl 1 16) - 1)%Z in
                 Z.land mask handle;
  get_sender := fun handle =>
                  Z.shiftr handle 16;
  }.


(***********************************************************************)
(** **                  FFA_VM_CONTEXT instance                        *)
(***********************************************************************)
Inductive ffa_mailbox_msg_t : Type :=
| mailbox_memory_init_value
| mailbox_memory_region (region_descriptor: FFA_memory_region_struct)
| mailbox_memory_relinquish (relinquish_descriptor: FFA_memory_relinquish_struct)
| mailbox_z (value : Z).

Definition init_ffa_mailbox_msg := mailbox_memory_init_value.
Definition vcpu_max_num := 4.

Definition mailbox_msg_to_region_struct :=
  fun x =>
    match x with
    | mailbox_memory_region region_descriptor =>
      Some region_descriptor
    | _ => None
    end.

Definition mailbox_msg_to_relinquish_struct :=
  fun x =>
    match x with
    | mailbox_memory_relinquish relinquish_descriptor =>
      Some relinquish_descriptor
    | _ => None
    end.

Definition mailbox_msg_to_z :=
  fun x =>
    match x with
    | mailbox_z value =>
      Some value
    | _ => None
    end.

Definition region_struct_to_mailbox_msg :=
  fun x => Some (mailbox_memory_region x).

Definition relinquish_struct_to_mailbox_msg :=
  fun x => Some (mailbox_memory_relinquish x).

Definition z_to_mailbox_msg := 
  fun x => Some (mailbox_z x).

Global Instance ffa_vm_context :
  FFA_VM_CONTEXT (ffa_types_and_constants := ffa_types_and_constants)  :=
    {
    (** - The following two types are for message passings. We use them to record and 
        retrieve descriptor information *)
    ffa_mailbox_send_msg_t := ffa_mailbox_msg_t;
    ffa_mailbox_recv_msg_t := ffa_mailbox_msg_t;
    init_ffa_mailbox_send_msg := init_ffa_mailbox_msg;
    init_ffa_mailbox_recv_msg := init_ffa_mailbox_msg;

    vcpu_max_num := vcpu_max_num;

    (** mailbox to/from descriptors *)
    mailbox_send_msg_to_region_struct := mailbox_msg_to_region_struct;
    mailbox_send_msg_to_relinqiush_struct := mailbox_msg_to_relinquish_struct;
    mailbox_send_msg_to_Z := mailbox_msg_to_z;
    region_struct_to_mailbox_send_msg := region_struct_to_mailbox_msg;
    relinqiush_struct_to_mailbox_send_msg := relinquish_struct_to_mailbox_msg;
    Z_to_mailbox_send_msg := z_to_mailbox_msg;

    mailbox_recv_msg_to_region_struct := mailbox_msg_to_region_struct;
    mailbox_recv_msg_to_relinqiush_struct := mailbox_msg_to_relinquish_struct;
    mailbox_recv_msg_to_Z := mailbox_msg_to_z;
    region_struct_to_mailbox_recv_msg := region_struct_to_mailbox_msg;
    relinqiush_struct_to_mailbox_recv_msg := relinquish_struct_to_mailbox_msg;
    Z_to_mailbox_recv_msg := z_to_mailbox_msg;

    primary_vm_id := 1;
    secondary_vm_ids := 2::3::4::nil;

    (* TODO: Need to fix *)
    FFA_memory_region_struct_size := fun x => 36;
    }.
    
(** TODO: The following values are dummy representations. We have to provide 
    proper values later if we want to connect this one with the real Hafnium / other 
    hypervisor implementations *)

(***********************************************************************)
(** **       HafniumMemoryManagementContext instance                   *)
(***********************************************************************)

Definition address_low_shift := 30.
Definition address_high_shift := 32.

Global Instance hafnium_memory_management_basic_context
  : HafniumMemoryManagementBasicContext
      (ffa_vm_context := ffa_vm_context) :=
  {
  address_low := (Z.shiftl 1 address_low_shift)%Z;
  address_high := (Z.shiftl 1 address_high_shift - 1)%Z;
  alignment_value := granuale; (* 4096 *)
  }.

Definition hafnium_address_translation_table :=
  fun (x : ffa_address_t) =>
    if decide (address_low <= x)%Z && decide (x < address_high)%Z
    then Some x else None.

Definition vm_address_translation_table :=
  fun (vid : ffa_UUID_t) (x : ffa_address_t) =>
    if decide (0 <= vid)%Z && decide (vid < number_of_vm)%Z
    then if decide (address_low <= x)%Z && decide (x < address_high)%Z
         then Some x
         else None
    else None.  

Global Instance hafnium_memory_management_context
  : HafniumMemoryManagementContext
      (hafnium_memory_management_basic_context
         := hafnium_memory_management_basic_context) :=
  {
  hafnium_address_translation_table :=
    hafnium_address_translation_table;
  vm_address_translation_table :=
    vm_address_translation_table;
  }.

(***********************************************************************)
(** **                 AbstractStateContext instance                   *)
(***********************************************************************)

Definition init_cpu_id := 0.
Definition num_of_cpus := 8.

Definition init_CPU_struct := mkCPU_struct.

Fixpoint cal_init_cpus (cpu_nums : nat) :=
  match cpu_nums with
  | O =>  (ZTree.empty CPU_struct)
  | S n' =>
    let res :=  cal_init_cpus n' in
    ZTree.set (Z.of_nat cpu_nums) 
              init_CPU_struct res
  end.

Definition init_cpus := cal_init_cpus (Z.to_nat num_of_cpus).

Definition init_api_page_pool_size_shift := 14.

Definition init_mem_global_properties :=
  mkMemGlobalProperties
    NotOwned NoAccess 
    FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED
    FFA_DATA_ACCESS_NOT_SPECIFIED
    FFA_MEMORY_NOT_SPECIFIED_MEM
    MemClean.
    
Fixpoint cal_init_global_properties_pool
         (address : nat)  :=
  match address with 
  | O => if decide (0 >= address_low)
        then ZTree.set (Z.shiftl 0 granuale_shift)  
                       init_mem_global_properties
                       (ZTree.empty MemGlobalProperties)
        else (ZTree.empty MemGlobalProperties)
  | S n' =>
    let converted_addr := Z.shiftl (Z.of_nat address) granuale_shift in
    if decide (converted_addr >= address_low)
    then let res := cal_init_global_properties_pool n' in
         ZTree.set converted_addr  
                   init_mem_global_properties
                   res
    else (ZTree.empty MemGlobalProperties)
  end.         
  
Definition init_mem_global_properties_pool
  : mem_global_properties_pool
  := cal_init_global_properties_pool
       (Z.to_nat (Z.shiftr address_high granuale_shift)).

Fixpoint cal_init_local_properties_pool
         (vms : list Z) :=
  match vms with 
  | nil => (ZTree.empty
             (ZTree.t MemLocalProperties))
  | hd::tl =>
    let res := cal_init_local_properties_pool tl in
    ZTree.set hd (ZTree.empty MemLocalProperties) res
  end.         

Definition init_mem_local_properties_global_pool 
  : mem_local_properties_global_pool
  :=  cal_init_local_properties_pool vm_ids.

Definition init_mem_properties :=
  mkMemProperties
    init_mem_global_properties_pool
    init_mem_local_properties_global_pool.

Definition init_VM_COMMON_struct (vcpu_ids: list Z) 
  := mkVM_COMMON_struct
       None
       vcpu_ids 
       (ZTree.empty VCPU_struct).

Definition init_MAILBOX_struct :=
  mkMAILBOX_struct
    init_ffa_mailbox_msg
    init_ffa_mailbox_msg
    None (* recv_sender *)
    0 (* recv_size *)
    None (* recv func *)
.

Definition init_VM_KERNEL_context (vcpu_ids: list Z) :=
 mkVM_KERNEL_struct 
   (init_VM_COMMON_struct vcpu_ids)
   init_MAILBOX_struct.

Fixpoint cal_init_VM_KERNEL_contexts (vm_ids: list Z) := 
  match vm_ids with
  | nil =>  (ZTree.empty VM_KERNEL_struct)
  | hd::tl =>
    let res :=  cal_init_VM_KERNEL_contexts tl in
    ZTree.set hd (init_VM_KERNEL_context (hd::nil)) res
  end.

Definition init_VM_KERNEL_contexts :=
  cal_init_VM_KERNEL_contexts vm_ids.

Fixpoint cal_init_VM_USERSPACE_contexts (vm_ids: list Z) :=
  match vm_ids with
  | nil =>  (ZTree.empty VM_USERSPACE_struct)
  | hd::tl =>
    let res :=  cal_init_VM_USERSPACE_contexts tl in
    ZTree.set hd (mkVM_USERSPACE_struct (init_VM_COMMON_struct (hd::nil))) res
  end.

Definition init_VM_USERSPACE_contexts :=
  cal_init_VM_USERSPACE_contexts vm_ids.

Definition init_hypervisor_struct :=
  mkHypervisor_struct
    init_cpu_id
    num_of_cpus
    init_cpus
    false (* time slice enabled *)
    None (* tpidr_el2 *)
    (Z.shiftl 1 init_api_page_pool_size_shift) (* api_page_pool_size *)
    (ZTree.empty FFA_memory_share_state_struct) (* ffa_share_state *)
    0 (* fresh_index_for_ffa_share_state *)
    init_mem_properties (* mem_properties *)
    number_of_vm  (* vm_count *)
    init_VM_KERNEL_contexts.

(* TODO: it is a dummy value *)
Definition version_number := (1, 1).

Definition init_abstract_state :=
  mkAbstractState
    (1, 1) (* dummy version number *)
    1 (*  cur_entity_id - primary VM *)
    init_hypervisor_struct
    init_VM_USERSPACE_contexts.

Fixpoint find_next_entity (vm_ids : list ffa_UUID_t)
         (current_entity_id : ffa_UUID_t) :=
  match vm_ids with
  | nil => primary_vm_id
  | hd::tl =>
    if decide (current_entity_id = hd)
    then match tl with
         | nil => primary_vm_id
         | hd'::_ => hd'
         end
    else find_next_entity tl current_entity_id
  end.

Definition scheduler (st: AbstractState) : ffa_UUID_t :=
  let cur_entity_id := st.(cur_entity_id) in
  find_next_entity vm_ids cur_entity_id.  

Global Instance abstract_state_context :
  AbstractStateContext
    (ffa_types_and_constants := ffa_types_and_constants)
    (descriptor_context := descriptor_context)
    (ffa_vm_context := ffa_vm_context)
    (hafnium_memory_management_basic_context
       := hafnium_memory_management_basic_context)
    (hafnium_memory_management_context
       := hafnium_memory_management_context) :=
  {
      scheduler := scheduler;
      initial_state := init_abstract_state;
  }.



Instance abstract_state_Showable: Showable AbstractState :=
  {
  show :=
    fun x => " "
  }.

(***********************************************************************)
(** *                 Context switching related parts                  *)
(***********************************************************************)

Section FFAContextSwitching.

  Inductive updateStateE: Type -> Type :=
  | GetState : updateStateE (AbstractState)
  | SetState (st1: AbstractState): updateStateE unit.

  Definition updateState_handler {E: Type -> Type}
    : updateStateE ~> stateT (AbstractState) (itree E) :=
    fun _ e st =>
      match e with
      | GetState => Ret (st, st)
      | SetState st' => Ret (st', tt)
      end.

  
  Notation HypervisorEE := (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).
  (**
     [JIEUNG:We referred context switchigns in Hafnium, but we believe it could be similar when 
     we provide abstract models for different implementations]
     
     In Hafnium, most parts are related to save registers in "/src/arch/aarch64/hypervisor/exceptions.S"
     We dramatically simplify them by saving and restoring FFA-related register values. 
     In reality, we may need to reflect the entire register save and recovery in the file:
     "save_volatile_to_vcpu", "save_register_access", "vcpu_switch", "vcpu_restore_all_and_run",
     "vcpu_restore_lazy_and_run", "vcpu_restore_nonvolatile_and_run", and 
     "vcpu_restore_volatile_and_run" in  "/src/arch/aarch64/hypervisor/exceptions.S". 
    
     In addition to that, "handle_system_register_access" in "/src/arch/aarch64/hypervisor/handler.c"
     also a function that handles register values when handling exceptions. 
    
     How it works:
     When an exception occurs, it first checks the exception value in the register ("vector_table_el2" 
     in the file). Then, if the exception number is either "sync_lower_64" or "sync_lower_32", 
     it calls "lower_sync_exception" defined in the same file. 
     
     Then, "lower_sync_exception" performs context switching and calls a C handler function to
     service the exception.
   *)
  (** Save contexts *)    
  Definition save_regs_to_vcpu_spec  :
    itree HypervisorEE (unit) := 
    st <- trigger GetState;;
    (* check whether the current running entity is one of VMs *)
    if decide (st.(cur_entity_id) <> hafnium_id) &&
       in_dec zeq st.(cur_entity_id) vm_ids
    then (* get contexts for the currently running entity ID *)
      do vm_userspace <- ZTree.get st.(cur_entity_id) st.(vms_userspaces) ;;;
      do cur_vcpu_index <- (vm_userspace.(vm_userspace_context).(cur_vcpu_index)) ;;;
      do vcpu_regs <- ZTree.get cur_vcpu_index 
                       (vm_userspace.(vm_userspace_context).(vcpus_contexts)) ;;;
                                                                         
      (* get vm contexts in Hanfium to save the userspace information in it *)              
      do vm_context <- ZTree.get st.(cur_entity_id) st.(hypervisor_context).(vms_contexts) ;;;
      if decide (list_eq_dec zeq (vm_context.(vm_kernelspace_context).(vcpus)) 
                             (vm_userspace.(vm_userspace_context).(vcpus))) &&
         decide (vcpu_regs.(vm_id) = Some st.(cur_entity_id))
      then
        let new_vm_context :=
            vm_context {vm_cur_vcpu_index: Some cur_vcpu_index}
                       {vm_vcpus_contexts:
                          ZTree.set cur_vcpu_index vcpu_regs
                                    vm_context.(vm_kernelspace_context).(vcpus_contexts)} in
        let new_vms_contexts :=
            ZTree.set st.(cur_entity_id)
                           new_vm_context
                           st.(hypervisor_context).(vms_contexts) in
        let new_st := st {cur_entity_id: hafnium_id}
                         {hypervisor_context/tpidr_el2: Some vcpu_regs}
                         {hypervisor_context/vms_contexts: new_vms_contexts} in 
        trigger (SetState new_st)
      else triggerUB "save_resg_to_vcpu_spec: inconsistency in total vcpu number"
    else triggerUB "save_resg_to_vcpu_spec: wrong cur entity id".
  
  Definition save_regs_to_vcpu_call (args : list Lang.val) :=
    match args with
    | nil => save_regs_to_vcpu_spec
    | _ => triggerUB "save_regs_to_vcpu_call: wrong arguments"
    end.
  
  (** Restore contexts and run.
     It also contains choosing the next vm to run by using an abstract scheduler  
   *)
  Definition vcpu_restore_and_run_spec  :
    itree HypervisorEE (unit) := 
    st <- trigger GetState;;
    (** find out the next vm to be scheduled *)
    (** - Since we do not have any scheduler implementations, we introduced abstract scheduler *)
    let next_vm_id := scheduler st in
    (** check whether the current running entity is Hafnium *)
    if decide (st.(cur_entity_id) = hafnium_id) && in_dec zeq next_vm_id vm_ids
    then
      (** get the userspace information *)
      do vm_userspace <- ZTree.get next_vm_id st.(vms_userspaces) ;;;
      (** get vm context to restore the userspace information *)
      do vm_context <- ZTree.get next_vm_id st.(hypervisor_context).(vms_contexts) ;;;
      (** get vcpu register information *)
      do cur_kernel_vcpu_index <- (vm_context.(vm_kernelspace_context).(cur_vcpu_index)) ;;;
      do cur_user_vcpu_index <- (vm_userspace.(vm_userspace_context).(cur_vcpu_index)) ;;;
      do vcpu_regs <- ZTree.get cur_kernel_vcpu_index
                               (vm_context.(vm_kernelspace_context).(vcpus_contexts)) ;;;
         if decide (list_eq_dec zeq (vm_context.(vm_kernelspace_context).(vcpus))
                                vm_userspace.(vm_userspace_context).(vcpus)) &&
            decide (cur_kernel_vcpu_index = cur_user_vcpu_index) &&
            decide (vcpu_regs.(vm_id) = Some next_vm_id)
            (* TODO: add cpu connection check with vcpu_regs later *)
         then
           let new_vm_userspace := 
               vm_userspace
                 {client_vcpus_contexts :
                    (ZTree.set cur_kernel_vcpu_index
                               vcpu_regs
                               (vm_userspace.(vm_userspace_context).(vcpus_contexts)))} in
           let new_vms_userspaces :=
               ZTree.set next_vm_id new_vm_userspace st.(vms_userspaces) in
           let new_st := st {cur_entity_id: next_vm_id}
                            {hypervisor_context/tpidr_el2: None}
                            {vms_userspaces: new_vms_userspaces} in 
           trigger (SetState new_st)
         else triggerUB "vcpu_restore_and_run__spec: inconsistency in vcpu number"
    else triggerUB "vcpu_restore_and_run__spec: wrong cur entity id".
  
  Definition vcpu_restore_and_run_call (args : list Lang.val) :=
    match args with
    | nil => vcpu_restore_and_run_spec
    | _ => triggerUB "vcpu_restore_and_run_call: wrong arguments"
    end.
  
End FFAContextSwitching.

(***********************************************************************)
(** *                       FFA Dispatch                               *)
(***********************************************************************)
Section FFADispatch.
   
  Notation HypervisorEE := (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).

  Definition function_dispatcher
             (ffa_function_type: FFA_FUNCTION_TYPE)
             (vid: ffa_UUID_t)
             (vals: ZMap.t Z) (st : AbstractState) :=
    match ffa_function_type with
    | FFA_MEM_DONATE 
      => ffa_mem_donate_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                            (ZMap.get 3 vals) (ZMap.get 4 vals) st
    | FFA_MEM_LEND
      => ffa_mem_lend_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                          (ZMap.get 3 vals) (ZMap.get 4 vals) st
    | FFA_MEM_SHARE
      => ffa_mem_share_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                           (ZMap.get 3 vals) (ZMap.get 4 vals) st
    | FFA_MEM_RETREIVE_REQ
      => ffa_mem_retrieve_req_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                                  (ZMap.get 3 vals) (ZMap.get 4 vals) st
    | FFA_MEM_RETREIVE_RESP
      => ffa_mem_retrieve_resp_spec vid (ZMap.get 1 vals)
                                   (ZMap.get 2 vals) st
    | FFA_MEM_RELINQUISH 
      => ffa_mem_relinquish_spec vid st
    | FFA_MEM_RECLAIM
      => ffa_mem_reclaim_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                             (ZMap.get 3 vals) st
    end.
  
  Definition ffa_dispatch_spec :  itree HypervisorEE (unit) := 
    (** - Extract the curretnt vcpu *)
    st <- trigger GetState;;
    (** - Get the information in tpidr_el2 register to find out the current VM to be served *)
    let vcpu_regs := st.(hypervisor_context).(tpidr_el2) in
    match vcpu_regs with
    | Some vcpu_regs' =>
      match vcpu_regs' with
      | mkVCPU_struct (Some cid) (Some vid) arch_regs =>
        match arch_regs with
        | mkArchRegs (mkFFA_value_type func_type vals) =>
          match func_type with
          | FFA_FUNCTION_IDENTIFIER ffa_function_type =>
            (** - Find out the result of the FFA ABI calls by using the proper handling functions *)
            do result <- function_dispatcher ffa_function_type
                                            vid vals st ;;;
             match result with                                
            | (updated_st, ffa_result) =>
              (** - Set the result inside the updated state *)
              do vm_context <-
                 ZTree.get
                   vid
                   updated_st.(hypervisor_context).(vms_contexts);;;
              do cur_kernel_vcpu_index <-
                 vm_context.(vm_kernelspace_context).(cur_vcpu_index) ;;;
              do vcpu_reg <-
                 ZTree.get cur_kernel_vcpu_index 
                    vm_context.(vm_kernelspace_context).(vcpus_contexts);;;
              let new_vcpu_reg :=
                  mkVCPU_struct (vcpu_reg.(cpu_id)) (vcpu_reg.(vm_id))
                                (mkArchRegs (ffa_value_gen ffa_result)) in
              let new_vm_context := 
                  vm_context
                    {vm_vcpus_contexts:
                       ZTree.set
                         cur_kernel_vcpu_index
                         new_vcpu_reg 
                         vm_context.(vm_kernelspace_context).(vcpus_contexts)} in
              let new_st :=
                  updated_st
                    {hypervisor_context / vms_contexts:
                       ZTree.set vid new_vm_context
                                 (updated_st.(hypervisor_context).(vms_contexts))} in
              trigger (SetState new_st)
            end                                     


             | _ => triggerUB "ffa_dispatch_spec: impossible case happens"
          end
        end
      | _ => triggerUB "ffa_dispatch_spec: impossible case happens"
      end
    | None => triggerUB "ffa_dispatch_spec: impossible case happens" 
    end.
                        
  Definition ffa_dispatch_call (args : list Lang.val) :=
    match args with
    | nil => ffa_dispatch_spec
    | _ => triggerUB "ffa_dispatch_call: wrong arguments"
    end.
      
End FFADispatch.  

