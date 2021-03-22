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

Require Import Coqlib sflib.

Require Import Decision.

Require Import Maps.
Set Implicit Arguments.

(* FFA Memory management related parts *)
Require Import FFAMemoryHypCall.
Require Import FFAMemoryHypCallIntro.
Require Export FFAMemoryHypCallDescriptorState.
Require Export FFAMemoryHypCallState.
Require Export FFAMemoryHypCallCoreTransition.

Notation "'do' X <- A ;;; B" :=
  (match A with Some X => B |
           None => None
   end)
    (at level 200, X ident, A at level 100, B at level 200) : ffa_monad_scope.
 
Notation " 'check' A ;;; B" :=
  (if A then B else None)
    (at level 200, A at level 100, B at level 200) : ffa_monad_scope.

Local Open Scope ffa_monad_scope.


(***********************************************************************)
(** *    Auxiliary Functions for additional transition Rules           *)
(***********************************************************************)
Section FFA_MEMORY_INTERFACE_ADDITIONAL_STEPS_AUXILIARY_FUNCTIONS.

  Context `{abstract_state_context: AbstractStateContext}.

  (** TODO: when TX/RX buffers are used to trasmit descriptors, 
      [length], [fragement_length], [address], and [page_count] 
      are not actually used. Do we need to define the following definitions even for that case? *)
  Definition ffa_mem_general_check_arguments
             (total_length fragment_length address page_count: Z) : bool :=
    if decide (total_length = 0) && decide (fragment_length = 0) &&
       decide (address  = 0) && decide (page_count = 0)
    then true
    else false. 

  Definition ffa_mem_retrieve_resp_check_arguments
             (total_length fragment_length: Z) : bool :=
    if decide (total_length = 0) && decide (fragment_length = 0)
    then true
    else false. 

  
  (***********************************************************************)
  (** **   Getter and setter functions for RX/TX buffers                 *)
  (***********************************************************************)
  (** Get a memory region descriptor for send (donate, lend, share) operations *)
  Definition get_send_memory_region_descriptor
             (caller : Z) (state: AbstractState)
    : option FFA_memory_region_struct := 
    do vm_context <- ZTree.get caller state.(hypervisor_context).(vms_contexts) ;;;
    mailbox_send_msg_to_region_struct vm_context.(mailbox).(send).
       
  (** Set a memory region descriptor for receivers (donate, lend, share) *)
  Definition set_send_memory_region_descriptor
             (sender receiver : ffa_UUID_t) (size : Z)
             (region_descriptor: FFA_memory_region_struct)
             (recv_func : FFA_FUNCTION_TYPE)
             (state: AbstractState)
    : option AbstractState := 
    do vm_context <- ZTree.get receiver state.(hypervisor_context).(vms_contexts) ;;;
    do message <- region_struct_to_mailbox_recv_msg region_descriptor ;;; 
    let new_vm_context := vm_context {vm_mailbox :
                                        mkMAILBOX_struct 
                                          (vm_context.(mailbox).(send))
                                          message sender size recv_func } in
    let new_vm_contexts :=
        ZTree.set receiver new_vm_context
                  state.(hypervisor_context).(vms_contexts) in
    Some state {hypervisor_context / vms_contexts : new_vm_contexts}.

  (** Set a memory region descriptor for receivers (donate, lend, share) *)
    Fixpoint set_send_memory_region_descriptors_for_multiple_receivers
             (receivers: list ffa_UUID_t)
             (sender: ffa_UUID_t) (size : Z)
             (region_descriptor: FFA_memory_region_struct)
             (recv_func : FFA_FUNCTION_TYPE)
             (state: AbstractState)
      : option AbstractState :=
      match receivers with
      | nil => Some state
      | hd::tl =>
        do new_st <- 
           set_send_memory_region_descriptors_for_multiple_receivers tl sender size region_descriptor
                                                                     recv_func state ;;;
        set_send_memory_region_descriptor sender hd size  region_descriptor recv_func new_st
      end.

  (** Get a memory region descriptor for send (donate, lend, share) operations *)
  Definition get_send_handle_value
             (caller : Z) (state: AbstractState)
    : option Z := 
    do vm_context <- ZTree.get caller state.(hypervisor_context).(vms_contexts) ;;;
    mailbox_send_msg_to_Z vm_context.(mailbox).(send).

  (** Set a memory region descriptor for receivers (donate, lend, share) *)
  Definition set_send_handle
             (sender receiver : ffa_UUID_t) (size : Z)
             (handle: Z)
             (recv_func : FFA_FUNCTION_TYPE)
             (state: AbstractState)
    : option AbstractState := 
    do vm_context <- ZTree.get receiver state.(hypervisor_context).(vms_contexts) ;;;
    do message <- Z_to_mailbox_recv_msg handle ;;; 
    let new_vm_context := vm_context {vm_mailbox :
                                        mkMAILBOX_struct 
                                          (vm_context.(mailbox).(send))
                                          message sender size recv_func } in
    let new_vm_contexts :=
        ZTree.set receiver new_vm_context
                  state.(hypervisor_context).(vms_contexts) in
    Some state {hypervisor_context / vms_contexts : new_vm_contexts}.

  (** Get a relinquish descriptor for send (donate, lend, share) operations *)
  Definition get_send_relinquish_descriptor
             (caller : Z) (state: AbstractState)
    : option FFA_memory_relinquish_struct := 
    do vm_context <- ZTree.get caller state.(hypervisor_context).(vms_contexts) ;;;
    mailbox_send_msg_to_relinqiush_struct vm_context.(mailbox).(send).
       
  (** Set a memory region descriptor for receivers (donate, lend, share) *)
  Definition set_send_relinquish_descriptor
             (sender receiver : ffa_UUID_t) (size : Z)
             (relinquish_descriptor: FFA_memory_relinquish_struct)
             (state: AbstractState)
    : option AbstractState := 
    do vm_context <- ZTree.get receiver state.(hypervisor_context).(vms_contexts) ;;;
    do message <- relinqiush_struct_to_mailbox_send_msg relinquish_descriptor ;;; 
    let new_vm_context := vm_context {vm_mailbox :
                                        mkMAILBOX_struct
                                          message 
                                          (vm_context.(mailbox).(recv))
                                          sender size FFA_MEM_RELINQUISH } in
    let new_vm_contexts :=
        ZTree.set receiver new_vm_context
                  state.(hypervisor_context).(vms_contexts) in
    Some state {hypervisor_context / vms_contexts : new_vm_contexts}.
       
  Fixpoint set_send_handle_for_multiple_receivers
             (receivers: list ffa_UUID_t)
             (sender : ffa_UUID_t) (size : Z)
             (handle: Z)
             (recv_func : FFA_FUNCTION_TYPE)
             (state: AbstractState)
    : option AbstractState :=
      match receivers with
      | nil => Some state
      | hd::tl =>
        do new_st <- 
           set_send_handle_for_multiple_receivers tl sender size handle
                                                  recv_func state ;;;
        set_send_handle sender hd size handle recv_func new_st
      end.

  Definition get_handle_information (handle: ffa_memory_handle_t) (st : AbstractState)      
    : option FFA_memory_share_state_struct :=
    let share_state_pool_index := get_value handle in 
    do share_state <- ZTree.get share_state_pool_index
                               st.(hypervisor_context).(ffa_share_state) ;;;
    Some share_state.    
       
  (***********************************************************************)
  (** **   Getter for memory accessibility and attributes                *)
  (***********************************************************************)
  (** Get memory attributes and access infomation from descriptor *) 
  Definition get_instruction_access_information_from_descriptor
             (receiver: FFA_endpoint_memory_access_descriptor_struct) :=
    receiver
    .(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor)
    .(FFA_memory_access_permissions_descriptor_struct_permisions_instruction).

  Definition get_data_access_information_from_descriptor
             (receiver: FFA_endpoint_memory_access_descriptor_struct) :=
    receiver
    .(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor)
    .(FFA_memory_access_permissions_descriptor_struct_permisions_data).

  Definition get_attributes_information_from_descriptor
             (region: FFA_memory_region_struct) :=
    region.(FFA_memory_region_struct_attributes)
    .(FFA_memory_region_attributes_descriptor_struct_memory_type).
  
  (** Get memory attributes and access infomation from local pools *) 
  Definition get_instruction_access_from_global_local_pool_props
             (id : ffa_UUID_t) (address : Z)
             (global_local_props: mem_local_properties_global_pool) :=
    do local_props <- ZTree.get id global_local_props ;;;
    do local_prop <- ZTree.get address local_props ;;;
    Some local_prop.(instruction_access_property).

  Definition get_data_access_from_global_local_pool_props
             (id : ffa_UUID_t) (address : Z)
             (global_local_props: mem_local_properties_global_pool) :=
    do local_props <- ZTree.get id global_local_props ;;;
    do local_prop <- ZTree.get address local_props ;;;
    Some local_prop.(data_access_property).

  Definition get_attributes_from_global_local_pool_props
             (id : ffa_UUID_t) (address : Z)
             (global_local_props: mem_local_properties_global_pool) :=
    do local_props <- ZTree.get id global_local_props ;;;
    do local_prop <- ZTree.get address local_props ;;;
    Some local_prop.(mem_attribute).
       
  (** Get memory attributes and access infomation from global pools *)        
  Definition get_instruction_access_from_global_props
             (id : ffa_UUID_t) (address : Z)
             (global_props: mem_global_properties_pool) :=
    do global_prop <- ZTree.get address global_props ;;;
    Some global_prop.(global_instruction_access_property).

  Definition get_data_access_from_global_props
             (id : ffa_UUID_t) (address : Z)
             (global_props: mem_global_properties_pool) :=
    do global_prop <- ZTree.get address global_props ;;;
    Some global_prop.(global_data_access_property).
       
  Definition get_attributes_from_global_props
             (id : ffa_UUID_t) (address : Z)
             (global_props: mem_global_properties_pool) :=
    do global_prop <- ZTree.get address global_props ;;;
                               Some global_prop.(global_mem_attribute).

  Definition get_permissions_and_attributes
             (vid : ffa_UUID_t) (address: Z)
             (mem_properties: MemProperties) :=
    do local_inst_access <-
        get_instruction_access_from_global_local_pool_props
          vid address mem_properties.(mem_local_properties) ;;;
    do local_data_access <-
        get_data_access_from_global_local_pool_props
          vid address mem_properties.(mem_local_properties) ;;;
    do local_attributes <-
        get_attributes_from_global_local_pool_props
          vid address mem_properties.(mem_local_properties) ;;;
  
    do global_inst_access <-
        get_instruction_access_from_global_props
          vid address mem_properties.(mem_global_properties) ;;;
    do global_data_access <-
        get_data_access_from_global_props
          vid address mem_properties.(mem_global_properties) ;;;
    do global_attributes <-
        get_attributes_from_global_props
          vid address mem_properties.(mem_global_properties) ;;;
    Some (local_inst_access, local_data_access, local_attributes,
          global_inst_access, global_data_access, global_attributes).       

  (***********************************************************************)
  (** **   Get addresses                                                 *)
  (***********************************************************************)
  Fixpoint get_addresses (base_address :Z) (page_count : nat) :=
    match page_count with
    | O => nil
    | S page_count' =>
      let res := get_addresses base_address page_count' in
      res ++ (base_address + (Z.of_nat page_count) * 4096)::nil
    end.
       
  Definition get_addreses_from_single_constituent 
           (constituent: FFA_memory_region_constituent_struct) := 
    get_addresses
      constituent.(FFA_memory_region_constituent_struct_address)     
      (Z.to_nat (constituent.(FFA_memory_region_constituent_struct_page_count))).

  Fixpoint get_addreses_from_constituents
           (constituents: list FFA_memory_region_constituent_struct) :=
    match constituents with
    | nil => nil
    | hd::tl =>
      (get_addreses_from_single_constituent hd)
        ++ (get_addreses_from_constituents tl)
    end.

  Definition get_addreses_from_composite
             (offset : nat)
             (composite: FFA_composite_memory_region_struct) :=
    if (decide (offset = O)%nat) 
    then
      Some 
        (get_addreses_from_constituents
           composite.(FFA_composite_memory_region_struct_constituents))
    else None.


  Fixpoint remove_nth {A : Type} (a : list A) (n : nat) : option (list A) :=
    match n with
    | O => Some a
    | S n' =>
      match a with
      | nil => None
      | hd::tl => remove_nth tl n'
      end
    end.

  Definition get_addreses_from_composite_with_offsets
             (offset: nat) (composite: FFA_composite_memory_region_struct)
    : option (list Z) :=
    if (decide (offset < 2)%nat)
    then
      do res<- remove_nth
                (composite
                 .(FFA_composite_memory_region_struct_constituents))
                (offset - 2) ;;;
      Some (get_addreses_from_constituents res)
    else None.

  Definition get_all_addresses
             (region_descriptor: FFA_memory_region_struct) :=
    get_addreses_from_constituents
      (region_descriptor.(FFA_memory_region_struct_composite)
       .(FFA_composite_memory_region_struct_constituents)).
  
  (***********************************************************************)
  (** **   Get receiver IDs                                              *)
  (***********************************************************************)  
  Definition get_receiver_id
             (receiver : FFA_endpoint_memory_access_descriptor_struct) :=
    receiver
    .(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor)
    .(FFA_memory_access_permissions_descriptor_struct_receiver).
  
  Definition get_receivers (memory_region_descriptor: FFA_memory_region_struct)
    : list FFA_endpoint_memory_access_descriptor_struct :=
    memory_region_descriptor.(FFA_memory_region_struct_receivers).

  (***********************************************************************)
  (** **   Get receiver IDs and addresses pair                           *)
  (***********************************************************************)
  Definition get_offset
             (receiver : FFA_endpoint_memory_access_descriptor_struct) :=
    let offset :=
        receiver
        .(FFA_memory_access_descriptor_struct_composite_memory_region_offset) in
    offset.

  Fixpoint get_receivers_receiver_ids_and_addresses
           (receivers : list FFA_endpoint_memory_access_descriptor_struct)
           (composite: FFA_composite_memory_region_struct) :=
    match receivers with
    | nil => Some nil
    | hd::tl =>
      do tl_res <- get_receivers_receiver_ids_and_addresses tl composite ;;;
      do hd_addresses <- get_addreses_from_composite_with_offsets (get_offset hd) composite ;;;
      Some ((hd, get_receiver_id hd, hd_addresses)::tl_res)
    end.
           
  Definition get_recievers_receiver_ids_and_addresses_tuple
             (region_descriptor: FFA_memory_region_struct) :=
    get_receivers_receiver_ids_and_addresses
      (region_descriptor.(FFA_memory_region_struct_receivers))
      (region_descriptor.(FFA_memory_region_struct_composite)).

  
  Fixpoint get_receiver_tuple_aux
             (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct *
                                 ffa_UUID_t * list Z))
             (receiver_id : ffa_UUID_t) :=
    match info_tuple with
    | nil => None
    | (descriptor, id, addrs)::tl =>
      if decide (receiver_id = id)
      then Some (descriptor, id, addrs)
      else get_receiver_tuple_aux tl receiver_id
    end.
  
  Definition get_receiver_tuple (receiver_id : ffa_UUID_t)
             (region_descriptor: FFA_memory_region_struct) :=
    do info_tuple <- get_receivers_receiver_ids_and_addresses
                      (region_descriptor.(FFA_memory_region_struct_receivers))
                      (region_descriptor.(FFA_memory_region_struct_composite)) ;;;
    get_receiver_tuple_aux info_tuple receiver_id.

  Definition get_receiver_id_addrs_pair
             (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z)) :=
    map (fun '(receiver, id, addrs) => (id, addrs)) info_tuple.

  Definition get_receiver_ids
             (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z)) :=
    map (fun '(receiver, id, addrs) => id) info_tuple.
  

  (***********************************************************************)
  (** **   Auxiliary functions to construct retrieve information         *)
  (***********************************************************************)  
  Fixpoint init_retrieve_relinquish_info_maps_per_receivers
           (addresses : list Z) : ZTree.t bool :=
    match addresses with
    | nil => ZTree.empty bool
    | hd::tl =>
      let res := init_retrieve_relinquish_info_maps_per_receivers tl in
      ZTree.set hd false res
    end.
  
  Fixpoint init_retrieve_relinquish_info_maps
           (receivers_and_addresses: list (ffa_UUID_t * list Z)) :=
    match receivers_and_addresses with
    | nil => ZTree.empty (ZTree.t bool)
    | hd::tl =>
      let res := init_retrieve_relinquish_info_maps tl in
      ZTree.set (fst hd)
                (init_retrieve_relinquish_info_maps_per_receivers (snd hd))
                res 
    end.

  Fixpoint init_retrieve_relinquish_num_info_maps_per_receivers
           (addresses : list Z) : ZTree.t Z :=
    match addresses with
    | nil => ZTree.empty Z
    | hd::tl =>
      let res := init_retrieve_relinquish_num_info_maps_per_receivers tl in
      ZTree.set hd 1 res
    end.
  
  Fixpoint init_retrieve_relinquish_num_info_maps
           (receivers_and_addresses: list (ffa_UUID_t * list Z)) :=
    match receivers_and_addresses with
    | nil => ZTree.empty (ZTree.t Z)
    | hd::tl =>
      let res := init_retrieve_relinquish_num_info_maps tl in
      ZTree.set (fst hd)
                (init_retrieve_relinquish_num_info_maps_per_receivers (snd hd))
                res 
    end.
  
  (***********************************************************************)
  (** **   Setter for memory region descriptor in the hypervisor         *)
  (***********************************************************************)
  (** Set memory region when sender tries to send the message to receivers *)

  Definition update_flags_in_FFA_memory_region_struct
             (flags : ffa_memory_region_flags_t) (region_descriptor: FFA_memory_region_struct) :=
    mkFFA_memory_region_struct
      (region_descriptor.(FFA_memory_region_struct_sender))
      (region_descriptor.(FFA_memory_region_struct_attributes))
      flags
      (region_descriptor.(FFA_memory_region_struct_handle))
      (region_descriptor.(FFA_memory_region_struct_tag))
      (region_descriptor.(FFA_memory_region_struct_receivers))
      (region_descriptor.(FFA_memory_region_struct_composite)).

  Definition update_handle_in_FFA_memory_region_struct
             (handle : ffa_memory_handle_t) (region_descriptor: FFA_memory_region_struct) :=
    mkFFA_memory_region_struct
      (region_descriptor.(FFA_memory_region_struct_sender))
      (region_descriptor.(FFA_memory_region_struct_attributes))
      (region_descriptor.(FFA_memory_region_struct_flags))
      handle
      (region_descriptor.(FFA_memory_region_struct_tag))
      (region_descriptor.(FFA_memory_region_struct_receivers))
      (region_descriptor.(FFA_memory_region_struct_composite)).
  
  Definition set_memory_region_in_shared_state
             (caller : ffa_UUID_t)
             (size : Z)
             (func_type: FFA_FUNCTION_TYPE)
             (receivers_and_addresses: list (ffa_UUID_t * (list Z)))
             (flags_arg : option ffa_memory_region_flags_t)
             (set_handle: bool) 
             (memory_region: FFA_memory_region_struct)
             (st : AbstractState) : option (AbstractState * Z) :=
    let flags :=
        match flags_arg with
        | Some flags' => flags'
        | _ =>  (memory_region.(FFA_memory_region_struct_flags))
        end in
    let new_index :=
        st.(hypervisor_context).(fresh_index_for_ffa_share_state) in
    do handle_value <- make_handle caller new_index;;;
    let handle := if set_handle then handle_value
                  else (memory_region.(FFA_memory_region_struct_handle)) in
    let new_shared_state :=
        mkFFA_memory_share_state_struct
          (update_handle_in_FFA_memory_region_struct handle memory_region)
          func_type
          (init_retrieve_relinquish_info_maps receivers_and_addresses)
          (init_retrieve_relinquish_info_maps receivers_and_addresses)
          (init_retrieve_relinquish_num_info_maps receivers_and_addresses) in
    let next_index := new_index + 1 in
    let new_api_page_pool_size :=
        st.(hypervisor_context).(api_page_pool_size) - size in
    let new_shared_state_pool :=
        ZTree.set new_index
                  new_shared_state
                  st.(hypervisor_context).(ffa_share_state) in
    Some (st { hypervisor_context / api_page_pool_size : new_api_page_pool_size }
             { hypervisor_context / ffa_share_state : new_shared_state_pool }
             { hypervisor_context / fresh_index_for_ffa_share_state : next_index },
          handle).

  Definition remove_share_state (index : Z) (st : AbstractState) :
    option AbstractState :=
    do share_state <- ZTree.get index st.(hypervisor_context).(ffa_share_state) ;;;
    match share_state with 
    | mkFFA_memory_share_state_struct 
        memory_region _ _ _ _ =>
      let region_size
          := (FFA_memory_region_struct_size
                (Zlength
                   (memory_region
                    .(FFA_memory_region_struct_composite)
                    .(FFA_composite_memory_region_struct_constituents)))) in
      let new_share_state_pool
          := ZTree.remove index st.(hypervisor_context).(ffa_share_state) in
      let new_api_page_pool_size :=
          st.(hypervisor_context).(api_page_pool_size) + region_size in
      Some (st { hypervisor_context / api_page_pool_size : new_api_page_pool_size }
               { hypervisor_context / ffa_share_state : new_share_state_pool })
    end.

  Definition unset_retrieve
             (index : Z) (addr : Z) (receiver: ffa_UUID_t) (st: AbstractState) :
    option AbstractState :=
    do share_state <- ZTree.get index st.(hypervisor_context).(ffa_share_state) ;;;
    do receiver_retrieve_pool <- ZTree.get receiver share_state.(retrieved);;; 
    let new_retrieved := ZTree.set receiver  
                                   (ZTree.set addr false  receiver_retrieve_pool)
                                   share_state.(retrieved) in
    let new_shared_state :=
        mkFFA_memory_share_state_struct
          (share_state.(memory_region)) (share_state.(share_func)) new_retrieved
          (share_state.(relinquished)) (share_state.(retrieve_count)) in
    let new_shared_state_pool :=
        ZTree.set index
                  new_shared_state
                  st.(hypervisor_context).(ffa_share_state) in
    Some (st { hypervisor_context / ffa_share_state : new_shared_state_pool }).
    
  (***********************************************************************)
  (** **   Flag value getters         *)
  (***********************************************************************)

    Definition get_zero_flag_value (region_descriptor: FFA_memory_region_struct) :=
      match region_descriptor.(FFA_memory_region_struct_flags) with
      | MEMORY_REGION_FLAG_NORMAL flags =>
        Some flags.(FFA_mem_default_flags_struct_zero_memory_flag)
      | _ => None
      end.        

       
End FFA_MEMORY_INTERFACE_ADDITIONAL_STEPS_AUXILIARY_FUNCTIONS.
