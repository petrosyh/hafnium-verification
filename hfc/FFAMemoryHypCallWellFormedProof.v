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

(* FFA Memory management related parts *)
Require Export FFAMemoryHypCall.
Require Export FFAMemoryHypCallIntro.
Require Export FFAMemoryHypCallDescriptorState.
Require Export FFAMemoryHypCallState.
Require Export FFAMemoryHypCallCoreTransition.
Require Export FFAMemoryHypCallTestingInterface.
Require Export FFAMemoryHypCallAdditionalStepsAuxiliaryFunctions.
Require Export FFAMemoryHypCallAdditionalSteps.

Require Import Maps.

(* end hide *)


Section AbstractStateContextProps.


  Class AbstractStateContextBasicProp `{abstract_state_context: AbstractStateContext} :=
    {
    (** - Basic decidability properties of them *)
    ffa_memory_region_tag_t_dec : forall (tag1 tag2: ffa_memory_region_tag_t),
        {tag1 = tag2} + {tag1 <> tag2};
    ffa_buffer_msg_t_dec :
      forall (buffer_msg1 buffer_msg2: ffa_buffer_msg_t),
        {buffer_msg1 = buffer_msg2} +
        {buffer_msg1 <> buffer_msg2};

    
    entity_list_prop := NoDup entity_list;

    well_formed_granuale : Z.modulo granuale alignment_value = 0;
    alignment_value_non_zero_prop :
      alignment_value > 0;
    address_low_alignment_prop :
      (Z.modulo page_low alignment_value)%Z = 0;
    address_high_alignment_prop : 
      (Z.modulo (page_high + 1) alignment_value)%Z = 0;

    (** all results of  the address translation needs to be in betweeen low and high *)
    address_translation_table_prop :
      forall addr,
        match stage2_address_translation_table addr with
        | Some addr' => (page_low <= addr' <= page_high)
        | _ => True
        end;
    (* TODO: add more invariants *)    
    
    (* vcpu_num_prop (vm: VM_struct) : 0 < vm.(vcpu_num) <= vcpu_max_num;
    cur_vcpu_id_prop (vm: VM_struct) : 0 <= vm.(cur_vcpu_index) < vm.(vcpu_num); *)
    (* TODO: add more invariants *)

    (*
    userspace_vcpu_num_prop (vm_userspace: VM_USERSPACE_struct) :
      0 < vm_userspace.(userspace_cur_vcpu_index) <= vcpu_max_num;
    userspace_cur_vcpu_id_prop (vm_userspace: VM_USERSPACE_struct) :
      0 <= vm_userspace.(userspace_cur_vcpu_index)
      < vm_userspace.(userspace_vcpu_num); *)
    (* TODO: add more invariants *)

    (**
       - Bit(63): Handle allocator.
         - b0: Allocated by SPM.
         - b1: Allocated by Hypervisor. *)
    make_handle_allocator_prop :
      forall vid value handle,
        make_handle vid value = Some handle ->
        Z.land (Z.shiftl 1 63) handle <> 0;      
    (* TODO: add more invariants *)
        
    cur_entity_id_prop (state : AbstractState) :
      In state.(cur_user_entity_id) vm_ids;
    }.

  (** ** Invariants for memory *)
  (** We specified several (basic) invariants for memory attributes, properties, etc *)
  (* TODO: add more invariants in here. *)
  (* TODO: Separate this well_formedness as two parts - 
      - Computable parts - return bool
      - Uncomputable parts - return Prop *)
  
  (* TODO: we need invariants about fileds, cpu_id and vm_id, in VCPU_struct *)


  Context `{abstract_state_context: !AbstractStateContext}.
  
  Definition mem_properties_prop_low_out_of_bound (st : AbstractState) :=
    forall addr,
      (addr < page_low)%Z ->
      ZTree.get
        addr
        (st.(hypervisor_context)).(mem_properties).(mem_global_properties)
      = None.
  
  Definition mem_properties_prop_high_out_of_bound (st : AbstractState) :=
    forall addr,
      (page_high < addr)%Z ->
      ZTree.get
        addr
        (st.(hypervisor_context)).(mem_properties).(mem_global_properties)
      = None.
  
  Definition mem_properties_prop_not_aligned  (st : AbstractState) :=
    forall addr,
      (Z.modulo addr alignment_value)%Z <> 0 ->
      ZTree.get
        addr
        (st.(hypervisor_context)).(mem_properties).(mem_global_properties)
      = None.
  
  Definition mem_properties_global_properties_existence  (st : AbstractState) :=
    forall addr,
      (page_low <= addr <= page_high)%Z ->
      (Z.modulo addr alignment_value)%Z = 0 ->
      exists global_properties,
        ZTree.get
          addr
          (st.(hypervisor_context)).(mem_properties).(mem_global_properties)
        = Some global_properties.

  Definition mem_properties_consistency_owner  (st : AbstractState) :=
    forall addr global_properties owner, 
      ZTree.get
        addr
        (st.(hypervisor_context)).(mem_properties).(mem_global_properties)
      = Some global_properties ->
      global_properties.(owned_by) = Owned owner ->
      exists local_properties_pool local_properties,
        ZTree.get
          owner
          (st.(hypervisor_context)).(mem_properties).(mem_local_properties)
        = Some local_properties_pool /\
        ZTree.get addr local_properties_pool = Some local_properties /\
        local_properties.(mem_local_owned) = LocalOwned /\
        data_access_permissive (global_properties.(global_data_access_property))
                               (local_properties.(data_access_property)) /\
        instruction_access_permissive (global_properties.(global_instruction_access_property))
                                      (local_properties.(instruction_access_property)) /\
        FFA_MEMORY_TYPE_permissive (global_properties.(global_mem_attribute))
                                   (local_properties.(mem_attribute)).
  
  Definition mem_properties_consistency_no_owner  (st : AbstractState) :=
    forall addr global_properties owner, 
      ZTree.get
        addr
        (st.(hypervisor_context)).(mem_properties).(mem_global_properties)
      = Some global_properties ->
      global_properties.(owned_by) = Owned owner ->
      forall other,
        other <> owner ->
        ((ZTree.get
            other
            (st.(hypervisor_context)).(mem_properties).(mem_local_properties)
          = None) \/
         (exists local_properties_pool,
             ZTree.get
               other
               (st.(hypervisor_context)).(mem_properties).(mem_local_properties)
             = Some local_properties_pool /\
             ZTree.get addr local_properties_pool = None) \/
         (exists local_properties_pool local_properties,
             ZTree.get
               owner
               (st.(hypervisor_context)).(mem_properties).(mem_local_properties)
             = Some local_properties_pool /\
             ZTree.get addr local_properties_pool = Some local_properties /\
             local_properties.(mem_local_owned) <> LocalOwned /\
             data_access_permissive (global_properties.(global_data_access_property))
                                    (local_properties.(data_access_property)) /\
             instruction_access_permissive (global_properties.(global_instruction_access_property))
                                           (local_properties.(instruction_access_property)) /\
             FFA_MEMORY_TYPE_permissive (global_properties.(global_mem_attribute))
                                        (local_properties.(mem_attribute)))).
  
  Record well_formed (state : AbstractState) :=
    {
    low_out_of_bound_property := mem_properties_prop_low_out_of_bound state;
    (* TODO: add more invariants in here. *)
    high_out_of_bound := mem_properties_prop_high_out_of_bound state;
    not_aligned := mem_properties_prop_not_aligned state;
    global_properties_existence := mem_properties_global_properties_existence state;
    consistency_owner := mem_properties_consistency_owner state;
    consistency_no_owner := mem_properties_consistency_no_owner state;
    }.
  
  Class WellFormedConext :=
    {
    initial_state_well_formed : well_formed initial_state;    
    well_formed_guarantee_well_formed_scheduler_result :
      forall st next_id, well_formed st -> scheduler st = next_id -> In next_id vm_ids;
    }.
  
End AbstractStateContextProps.


Section WELLFORMED.

  Context `{abstract_state_context: AbstractStateContext}.  
  Notation HypervisorEE :=
    (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).

  (** ** Wrapper spec *)
  (** The following definition is a wrapper spec to easily find out 
      input and output states *)

  Context `{WellFormedConext}.
  
  Lemma ffa_mem_donate_well_formed_preserve:
    forall st caller total_length fragment_length address count st' res
      (Hspec: ffa_mem_donate_spec
                caller total_length fragment_length address count st
              = SUCCESS (st', res))
      (Hwell_formed: well_formed st),
    well_formed st'.
  Proof.
    intros.
    unfold ffa_mem_donate_spec in Hspec.
  Admitted.
  
End WELLFORMED.

