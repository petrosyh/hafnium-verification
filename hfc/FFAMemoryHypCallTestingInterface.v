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
Require Export FFAMemoryHypCallIntro.
Require Export FFAMemoryHypCallDescriptorState.
Require Export FFAMemoryHypCallState.
Require Export FFAMemoryHypCallCoreTransition.

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
(** *                 Context switching related parts                  *)
(***********************************************************************)
Section FFAContextSwitching.
  
  Context `{abstract_state_context: AbstractStateContext}.

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
    if decide (st.(cur_entity_id) <> hafnium_id) && in_dec zeq st.(cur_entity_id) vm_ids
    then (* get contexts for the currently running entity ID *)
      do vm_userspace <- ZTree.get st.(cur_entity_id) st.(vms_userspaces) ;;;
      do vcpu_regs <- ZTree.get vm_userspace.(userspace_cur_vcpu_index) vm_userspace.(userspace_vcpus) ;;;
      (* get vm contexts in Hanfium to save the userspace information in it *)              
      do vm_context <- ZTree.get st.(cur_entity_id) st.(hypervisor_context).(vms_contexts) ;;;
      if decide (vm_context.(vcpu_num) = vm_userspace.(userspace_vcpu_num)) &&
         decide (vcpu_regs.(vm_id) = Some st.(cur_entity_id))
      then
        let new_vcpu_id := vm_userspace.(userspace_cur_vcpu_index) in
        let new_vm_context := vm_context {vm_cur_vcpu_index: new_vcpu_id}
                                         {vm_vcpus:
                                            ZTree.set new_vcpu_id vcpu_regs vm_context.(vcpus)} in
        let new_vms_contexts :=
            ZTree.set st.(cur_entity_id) new_vm_context st.(hypervisor_context).(vms_contexts) in
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
      do vcpu_regs <- ZTree.get vm_context.(cur_vcpu_index) vm_context.(vcpus) ;;;
         if decide (vm_context.(vcpu_num) = vm_userspace.(userspace_vcpu_num)) &&
            decide (vm_context.(cur_vcpu_index) = vm_userspace.(userspace_cur_vcpu_index)) &&
            decide (vcpu_regs.(vm_id) = Some next_vm_id)
            (* TODO: add cpu connection check with vcpu_regs later *)
         then
           let new_vm_userspace := 
               vm_userspace {userspace_vcpus :
                               (ZTree.set (vm_userspace.(userspace_cur_vcpu_index))
                                          vcpu_regs (vm_userspace.(userspace_vcpus)))} in
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
  
  Context `{abstract_state_context: AbstractStateContext}.
  
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
              do vcpu_reg <-
                 ZTree.get
                   vm_context.(cur_vcpu_index) vm_context.(vcpus);;;
              let new_vcpu_reg :=
                  mkVCPU_struct (vcpu_reg.(cpu_id)) (vcpu_reg.(vm_id))
                                (mkArchRegs (ffa_value_gen ffa_result)) in
              let new_vm_context := 
                  vm_context
                    {vm_vcpus: ZTree.set (vm_context.(cur_vcpu_index))
                                         new_vcpu_reg 
                                         vm_context.(vcpus)} in
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

