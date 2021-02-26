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


Require Import Maps.

Section WELLFORMED.

  Context `{abstract_state_context: AbstractStateContext}.  
  Notation HypervisorEE :=
    (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).

  (** ** Wrapper spec *)
  (** The following definition is a wrapper spec to easily find out 
      input and output states *)
  Definition get_input_output_donate_state_spec
             (caller total_length fragment_length address count : Z) :
    itree HypervisorEE
          (AbstractState * AbstractState) :=
    input <- trigger GetState;;
    ffa_mem_donate_spec caller total_length fragment_length address count;;
    output <- trigger GetState;;
    Ret (input, output).

  (** ** Invariants for memory *)
  (** We specified several (basic) invariants for memory attributes, properties, etc *)
  (* TODO: add more invariants in here. *)
  (* TODO: Separate this well_formedness as two parts - 
      - Computable parts - return bool
      - Uncomputable parts - return Prop *)
  
  (* TODO: we need invariants about fileds, cpu_id and vm_id, in VCPU_struct *)

    Definition mem_properties_prop_low_out_of_bound (st : AbstractState) :=
      forall addr,
        (addr < address_low)%Z ->
        ZTree.get
          addr
          (st.(hypervisor_context)).(mem_properties).(mem_global_properties)
        = None.
    
    Definition mem_properties_prop_high_out_of_bound (st : AbstractState) :=
      forall addr,
        (address_high < addr)%Z ->
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
        (address_low <= addr <= address_high)%Z ->
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
          MEM_ATTRIBUTES_TYPE_permissive (global_properties.(global_mem_attribute))
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
               MEM_ATTRIBUTES_TYPE_permissive (global_properties.(global_mem_attribute))
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

  Context `{well_formed_context :  WellFormedConext}.
  
  Lemma ffa_mem_donate_well_formed_preserve:
    forall caller total_length fragment_length address count,
      match get_input_output_donate_state_spec caller total_length fragment_length address count with 
      | Ret (input, output) => well_formed input -> well_formed output
      | _ => True
      end.
  Proof.
    intros.
    destruct (_observe) eqn:?; auto.
    unfold _observe in Heqi.
    unfold x in Heqi.
    unfold get_input_output_donate_state_spec in Heqi.
    unfold ffa_mem_donate_spec in Heqi.
    simpl in Heqi.
    
  Admitted.
  
End WELLFORMED.

