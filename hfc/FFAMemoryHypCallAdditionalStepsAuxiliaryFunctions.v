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
     RelationClasses
     HexString
     String.

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

Import Monads.
Import MonadNotation.

Local Open Scope monad_scope.
Local Open Scope string_scope.
Require Import Coqlib sflib.

Require Import HexString.

(* FFA Memory management related parts *)
Require Import FFAMemoryHypCall.
Require Import FFAMemoryHypCallIntro.
Require Export FFAMemoryHypCallDescriptorState.
Require Export FFAMemoryHypCallState.
Require Export FFAMemoryHypCallCoreTransition.

Local Open Scope ffa_monad_scope.

(***********************************************************************)
(** *    Auxiliary Functions for Print                                 *)
(***********************************************************************)
Section PRINT_AUXILIARY_FUNCTIONS.

  Definition newline :=
    "
".

  Definition tabspace := "    ".
  
  Definition append_all (cls: list string) : string :=
    List.fold_right append "" cls.

  Definition list_z_to_string (vals : list Z) :=
    match List.map HexString.of_Z vals with
    | nil => ""
    | hd::tl => append_all (hd::(List.map (append ", ") tl))
    end.

  Example list_z_to_string_ex1 :
    list_z_to_string [1; 2; 3] = "0x1, 0x2, 0x3".
  Proof. reflexivity. Qed.

  Definition print_vals (len : nat) (vals :ZMap.t Z) :=
    let print_val (pos : Z) :=
        append_all ["("; HexString.of_Z pos; ": ";
                   HexString.of_Z (ZMap.get pos vals); ")"] in
    append_all (List.map print_val (List.map Z.of_nat (List.rev (List.seq 0 len)))).

  Definition print_ffa_vals (vals :ZMap.t Z) :=
    print_vals 8 vals.

  Example print_ffa_vals_ex1 :
    print_ffa_vals (ZMap.set 7 5 (ZMap.set 1 4 (ZMap.init 0))) =
    "(0x7: 0x5)(0x6: 0x0)(0x5: 0x0)(0x4: 0x0)(0x3: 0x0)(0x2: 0x0)(0x1: 0x4)(0x0: 0x0)".
  Proof. reflexivity. Qed.

End PRINT_AUXILIARY_FUNCTIONS.

(* end hide *)

(***********************************************************************)
(** *    Auxiliary Functions for additional transition Rules           *)
(***********************************************************************)
Section FFA_MEMORY_INTERFACE_ADDITIONAL_STEPS_AUXILIARY_FUNCTIONS.

  Context `{abstract_state_context: AbstractStateContext}.

  (***********************************************************************)
  (** **   Check functions for arguments                                 *)
  (***********************************************************************)
  (** The following two functions check the validity of argument values transferred by registers. 
      In the current implementation, all of them should be 0. This is because 
      the current version only considers the interface that uses TX/RX buffers. 
      We do not allow the case that directly uses registers to pass the information of the 
      hypervisor call.

      TODO: when TX/RX buffers are used to trasmit descriptors, 
      [length], [fragement_length], [address], and [page_count] 
      are not actually used. Do we need to define the following definitions even for that case? *)
  Definition ffa_mem_general_check_arguments
             (total_length fragment_length address page_count: Z) : bool :=
    isTrue (total_length = 0 /\ fragment_length = 0 /\ address = 0 /\ page_count = 0).

  Definition ffa_mem_retrieve_resp_check_arguments
             (total_length fragment_length: Z) : bool :=
    isTrue (total_length = 0 /\ fragment_length = 0).

  (***********************************************************************)
  (** **   Getter and setter functions for RX/TX buffers                 *)
  (***********************************************************************)
  (** Auxiliary functions to send and receive messages in the RX/TX buffers. *)

  (** Getter and setters for memory region descriptors in the RX/TX buffers *)
  Definition get_send_memory_region_descriptor
             (caller : Z) (state: AbstractState)
    : RESULT ((AbstractState * FFA_memory_region_struct)%type) :=
    vm_context <- result_from_option
                   "cannot get vm_context"
                   (ZTree.get caller
                              state.(hypervisor_context).(vms_contexts))
    ;; memory_region <- result_from_option
                         "cannot get memory_region"
                         (buffer_msg_to_region_struct
                            (vm_context.(buffer).(message)))
    ;; ret (state
              {system_log: state.(system_log)
                                   ++(GetBuffer caller vm_context.(buffer))::nil},
            memory_region).
  
  Definition set_send_memory_region_descriptor
             (sender receiver : ffa_UUID_t) (size : Z)
             (region_descriptor: FFA_memory_region_struct)
             (recv_func : FFA_FUNCTION_TYPE)
             (state: AbstractState)
    : RESULT AbstractState :=
    vm_context <- result_from_option
                   "cannot get vm_context"
                   (ZTree.get
                      receiver state.(hypervisor_context).(vms_contexts))
    ;; message <- result_from_option
                   "cannot get message"
                   (region_struct_to_buffer_msg region_descriptor)
    ;; let buffer_contents := mkBUFFER_struct
                                 message (Some sender) size (Some recv_func) in
       let vm_context := vm_context {vm_buffer : buffer_contents} in
       let vms_contexts :=
        ZTree.set receiver vm_context
                  state.(hypervisor_context).(vms_contexts) in
       ret (state {hypervisor_context / vms_contexts : vms_contexts}
                  {system_log: state.(system_log)
                                       ++(SetBuffer sender receiver buffer_contents)::nil}).

  Definition set_send_memory_region_descriptors_for_multiple_receivers
             (receivers: list ffa_UUID_t)
             (sender: ffa_UUID_t) (size : Z)
             (region_descriptor: FFA_memory_region_struct)
             (recv_func : FFA_FUNCTION_TYPE)
             (state: AbstractState)
    : RESULT AbstractState :=
    List.fold_right
      (fun receiver res_state =>
         state <- res_state
         ;; set_send_memory_region_descriptor sender receiver size
                                              region_descriptor recv_func state)
      (SUCCESS state)
      receivers.

  (** Getter and setters for the handle value in the RX/TX buffers *)           
  Definition get_send_handle_value
             (caller : Z) (state: AbstractState)
    : RESULT (AbstractState * Z) :=
    vm_context <- result_from_option
                   "cannot get vm_context"
                   (ZTree.get caller state.(hypervisor_context).(vms_contexts))
    ;; handle <- result_from_option
                  "cannot get handle"
                  (buffer_msg_to_Z vm_context.(buffer).(message))
    ;; ret (state {system_log: state.(system_log)
                                       ++(GetBuffer caller vm_context.(buffer))::nil},
            handle).
                                                          
  Definition set_send_handle
             (sender receiver : ffa_UUID_t) (size : Z)
             (handle: Z)
             (recv_func : FFA_FUNCTION_TYPE)
             (state: AbstractState)
    : RESULT AbstractState :=
    vm_context <- result_from_option
                   "cannot get vm_context"
                   (ZTree.get receiver state.(hypervisor_context).(vms_contexts))
    ;; message <- result_from_option
                   "cannot get message"
                   (Z_to_buffer_msg handle)
    ;; let buffer_contents := mkBUFFER_struct
                                 message (Some sender) size (Some recv_func) in
       let vm_context := vm_context {vm_buffer : buffer_contents} in
       let vms_contexts :=
           ZTree.set receiver vm_context
                  state.(hypervisor_context).(vms_contexts) in
       ret (state {hypervisor_context / vms_contexts : vms_contexts}
                  {system_log: state.(system_log)
                                       ++(SetBuffer sender receiver buffer_contents)::nil}).
         
  Definition set_send_handle_for_multiple_receivers
             (receivers: list ffa_UUID_t)
             (sender : ffa_UUID_t) (size : Z)
             (handle: Z)
             (recv_func : FFA_FUNCTION_TYPE)
             (state: AbstractState)
    : RESULT AbstractState :=
    List.fold_right
      (fun receiver res_state =>
         state <- res_state
         ;; set_send_handle sender receiver size handle recv_func state)
      (SUCCESS state)
      receivers.

  (** The unwrapper to retrieve the actual information from the handle value *)
  Definition get_handle_information (handle: ffa_memory_handle_t) (st : AbstractState)      
    : RESULT FFA_memory_share_state_struct :=
    let share_state_pool_index := get_value handle in 
    result_from_option
      "cannot get share state"
      (ZTree.get share_state_pool_index
                 (st.(hypervisor_context).(ffa_share_state))).

  (** Getter and setters for the relinquish descriptor in the RX/TX buffers *)
  Definition get_send_relinquish_descriptor
             (caller : Z) (state: AbstractState)
    : RESULT (AbstractState * FFA_memory_relinquish_struct) :=
    vm_context <- result_from_option
                   "cannot get vm_context"
                   (ZTree.get caller state.(hypervisor_context).(vms_contexts))
    ;; relinquish_descriptor <- result_from_option
                                 "cannot get relinquish_descriptor"
                                 (buffer_msg_to_relinqiush_struct vm_context.(buffer).(message))
    ;; ret (state {system_log: state.(system_log)
                                       ++(GetBuffer caller vm_context.(buffer))::nil},
            relinquish_descriptor).
       
  Definition set_send_relinquish_descriptor
             (sender receiver : ffa_UUID_t) (size : Z)
             (relinquish_descriptor: FFA_memory_relinquish_struct)
             (state: AbstractState)
    : RESULT AbstractState :=
    vm_context <- result_from_option
                   "cannot get vm_contxt"
                   (ZTree.get receiver state.(hypervisor_context).(vms_contexts))
    ;; message <- result_from_option
                   "cannot get message"
                   (relinqiush_struct_to_buffer_msg relinquish_descriptor)
    ;; let buffer_contents := mkBUFFER_struct
                                 message
                                 (Some sender) size (Some FFA_MEM_RELINQUISH) in
       let vm_context := vm_context {vm_buffer : buffer_contents} in
       let vms_contexts :=
           ZTree.set receiver vm_context
                     state.(hypervisor_context).(vms_contexts) in
       ret (state
              {hypervisor_context / vms_contexts : vms_contexts}
              {system_log: state.(system_log)
                                   ++(SetBuffer sender receiver buffer_contents)::nil}).
       
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
    local_props <- result_from_option
                    "cannot get local props"
                    (ZTree.get id global_local_props)
    ;; local_prop <- result_from_option
                      "cannot get local prop"
                      (ZTree.get address local_props)
    ;; ret local_prop.(instruction_access_property).

  Definition get_data_access_from_global_local_pool_props
             (id : ffa_UUID_t) (address : Z)
             (global_local_props: mem_local_properties_global_pool) :=
    local_props <- result_from_option
                    "cannot get local props"
                    (ZTree.get id global_local_props)
    ;; local_prop <- result_from_option
                      "cannot get local prop"
                      (ZTree.get address local_props)
    ;; ret local_prop.(data_access_property).

  Definition get_attributes_from_global_local_pool_props
             (id : ffa_UUID_t) (address : Z)
             (global_local_props: mem_local_properties_global_pool) :=
    local_props <- result_from_option
                    "cannot get local props"
                    (ZTree.get id global_local_props)
    ;; local_prop <- result_from_option
                      "cannot get local prop"
                      (ZTree.get address local_props)
    ;; ret local_prop.(mem_attribute).
       
  (** Get memory attributes and access infomation from global pools *)        
  Definition get_instruction_access_from_global_props
             (id : ffa_UUID_t) (address : Z)
             (global_props: mem_global_properties_pool) :=
    global_prop <- result_from_option
                    "cannot get global props"
                    (ZTree.get address global_props)
    ;; ret global_prop.(global_instruction_access_property).

  Definition get_data_access_from_global_props
             (id : ffa_UUID_t) (address : Z)
             (global_props: mem_global_properties_pool) :=
    global_prop <- result_from_option
                    "cannot get global props"
                    (ZTree.get address global_props)
    ;; ret global_prop.(global_data_access_property).
       
  Definition get_attributes_from_global_props
             (id : ffa_UUID_t) (address : Z)
             (global_props: mem_global_properties_pool) :=
    global_prop <- result_from_option
                    "cannot get global props"
                    (ZTree.get address global_props)
    ;; ret global_prop.(global_mem_attribute).

  Definition PERM_AND_ATTR_TYPE :=
    (FFA_INSTRUCTION_ACCESS_TYPE * FFA_DATA_ACCESS_TYPE * FFA_MEMORY_TYPE *
     FFA_INSTRUCTION_ACCESS_TYPE * FFA_DATA_ACCESS_TYPE * FFA_MEMORY_TYPE)%type.
  
  Definition get_permissions_and_attributes
             (vid : ffa_UUID_t) (address: Z)
             (mem_properties: MemProperties) : RESULT  PERM_AND_ATTR_TYPE :=
    local_inst_access <- get_instruction_access_from_global_local_pool_props
                          vid address mem_properties.(mem_local_properties)
    ;; local_data_access <- get_data_access_from_global_local_pool_props
                             vid address mem_properties.(mem_local_properties)
    ;; local_attributes <- get_attributes_from_global_local_pool_props
                            vid address mem_properties.(mem_local_properties)
    ;; global_inst_access <- get_instruction_access_from_global_props
                              vid address mem_properties.(mem_global_properties)
    ;; global_data_access <- get_data_access_from_global_props
                              vid address mem_properties.(mem_global_properties)
    ;; global_attributes <- get_attributes_from_global_props
                             vid address mem_properties.(mem_global_properties)
    ;; ret (local_inst_access, local_data_access, local_attributes,
            global_inst_access, global_data_access, global_attributes).

  (***********************************************************************)
  (** **   Get addresses from the descriptor                             *)
  (***********************************************************************)
  Definition get_addresses (base_address :Z) (page_count : nat) : list Z :=
    List.map (fun page => base_address + (Z.of_nat page) * 4096) (List.seq 1 page_count).

  Example get_addresses_ex1 : get_addresses 4096%Z 3%nat = [8192; 12288; 16384].
  Proof. reflexivity. Qed.

  Definition get_addreses_from_single_constituent 
           (constituent: FFA_memory_region_constituent_struct) := 
    get_addresses
      constituent.(FFA_memory_region_constituent_struct_address)     
      (Z.to_nat (constituent.(FFA_memory_region_constituent_struct_page_count))).

  Definition get_addreses_from_constituents
           (constituents: list FFA_memory_region_constituent_struct) :=
    List.concat (List.map get_addreses_from_single_constituent constituents).

  Definition get_addreses_from_composite
             (offset : nat)
             (composite: FFA_composite_memory_region_struct) : RESULT (list Z) :=
    guard decide (offset = O)%nat report "invalid offset"
    ;; ret (get_addreses_from_constituents
               composite.(FFA_composite_memory_region_struct_constituents)).
  
  Fixpoint skipn_error {A : Type} (a : list A) (n : nat) : option (list A) :=
    match n with
    | O => Some a
    | S n' =>
      match a with
      | nil => None
      | hd::tl => skipn_error tl n'
      end
    end.

  Definition get_addreses_from_composite_with_offsets
             (offset: nat) (composite: FFA_composite_memory_region_struct)
    : RESULT (list Z) :=
    guard decide (offset < 2)%nat report "invalid offset"
    ;; res <- result_from_option
                "invalid skipn_error"
                (skipn_error
                   composite.(FFA_composite_memory_region_struct_constituents)
                               (offset - 2))
    ;; ret (get_addreses_from_constituents res).

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


  Definition receiver_tuple
    := (FFA_endpoint_memory_access_descriptor_struct *
        ffa_UUID_t * (list Z))%type.

  Definition get_receivers_receiver_ids_and_addresses
           (receivers : list FFA_endpoint_memory_access_descriptor_struct)
           (composite: FFA_composite_memory_region_struct) : RESULT (list receiver_tuple) :=
    List.fold_right
      (fun receiver res_tuples =>
         tuples <- res_tuples
         ;; addresses <- get_addreses_from_composite_with_offsets
                          (get_offset receiver) composite
         ;; let tuple := (receiver, get_receiver_id receiver, addresses) in
            ret (tuple::tuples))
      (SUCCESS nil)
      receivers.

  Definition get_recievers_receiver_ids_and_addresses_tuple
             (region_descriptor: FFA_memory_region_struct) :=
    get_receivers_receiver_ids_and_addresses
      (region_descriptor.(FFA_memory_region_struct_receivers))
      (region_descriptor.(FFA_memory_region_struct_composite)).

  Definition GetPAsFromIPAs (addresses : list Z) : RESULT (list Z) :=
    List.fold_right
      (fun address res_paddrs =>
         paddrs <- res_paddrs
         ;; paddr <- result_from_option
                      "cannot get a translation result"
                      (stage2_address_translation_table address)
         ;; ret (paddr::paddrs))
      (SUCCESS nil)
      addresses.

  Definition get_receiver_tuple_aux
             (info_tuples : list (FFA_endpoint_memory_access_descriptor_struct *
                                  ffa_UUID_t * list Z))
             (receiver_id : ffa_UUID_t) :=
    List.find
      (fun '(_, id, _) => decide (receiver_id = id))
      info_tuples.

  Definition SubstIPAsIntoPAs
           (info_tuples : list (FFA_endpoint_memory_access_descriptor_struct *
                               ffa_UUID_t * list Z)) : 
    RESULT (list receiver_tuple) :=
    List.fold_right
      (fun '(descriptor, id, addrs) res_pinfos =>
         pinfos <- res_pinfos
         ;; paddrs <- GetPAsFromIPAs addrs
         ;; ret ((descriptor, id, paddrs)::pinfos))
      (SUCCESS nil)
      info_tuples.

  Definition get_receiver_tuple (receiver_id : ffa_UUID_t)
             (region_descriptor: FFA_memory_region_struct) :=
    info_tuple <-
      get_receivers_receiver_ids_and_addresses
         region_descriptor.(FFA_memory_region_struct_receivers)
                             region_descriptor.(FFA_memory_region_struct_composite)
    ;; result_from_option
         "get_receiver_tuple_aux"
         (get_receiver_tuple_aux info_tuple receiver_id).

  Definition get_receiver_id_addrs_pair
             (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct
                                 * ffa_UUID_t * list Z)) :=
    map (fun '(receiver, id, addrs) => (id, addrs)) info_tuple.

  Definition get_receiver_ids
             (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct
                                 * ffa_UUID_t * list Z)) :=
    map (fun '(receiver, id, addrs) => id) info_tuple.
  
  Definition convert_addresses_to_page_numbers
             (addresses: list Z) :=
    map (fun addr => Z.div addr granuale) addresses.


  Definition convert_addresses_in_info_tuple_to_page_numbers
             (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct
                                 * ffa_UUID_t * list Z)) :=
    map (fun '(receiver, id, addrs) =>
           (receiver, id, convert_addresses_to_page_numbers addrs)) info_tuple.
  
  (***********************************************************************)
  (** **   Auxiliary functions to construct retrieve information         *)
  (***********************************************************************)  
  Definition init_retrieve_relinquish_info_maps_per_receivers
             (addresses : list Z) : ZTree.t bool :=
    List.fold_right
      (fun address res => ZTree.set address false res)
      (ZTree.empty bool)
      addresses.

  Definition init_retrieve_relinquish_info_maps
             (receivers_and_addresses: list (ffa_UUID_t * list Z)) :=
    List.fold_right
      (fun '(uuid, addrs) res =>
         ZTree.set uuid
                   (init_retrieve_relinquish_info_maps_per_receivers addrs)
                   res)
      (ZTree.empty (ZTree.t bool))
      receivers_and_addresses.

  Definition init_retrieve_relinquish_num_info_maps_per_receivers
             (addresses : list Z) : ZTree.t Z :=
    List.fold_right
      (fun addr res => ZTree.set addr 1 res)
      (ZTree.empty Z)
      addresses.

  Definition init_retrieve_relinquish_num_info_maps
             (receivers_and_addresses: list (ffa_UUID_t * list Z)) :=
    List.fold_right
      (fun '(uuid, addrs) res =>
         ZTree.set uuid
                   (init_retrieve_relinquish_num_info_maps_per_receivers addrs)
                   res)
      (ZTree.empty (ZTree.t Z))
      receivers_and_addresses.

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
             (st : AbstractState) : RESULT (AbstractState * Z) :=
    let flags :=
        match flags_arg with
        | Some flags' => flags'
        | _ => memory_region.(FFA_memory_region_struct_flags)
        end in
    let new_index :=
        st.(hypervisor_context).(fresh_index_for_ffa_share_state) in
    handle_value <- result_from_option
                     "cannot get handle"
                     (make_handle caller new_index)
    ;; let handle :=
           if set_handle then handle_value
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
       ret (st { hypervisor_context / api_page_pool_size : new_api_page_pool_size }
               { hypervisor_context / ffa_share_state : new_shared_state_pool }
               { hypervisor_context / fresh_index_for_ffa_share_state : next_index },
            handle).

  Definition remove_share_state (index : Z) (st : AbstractState) :
    RESULT AbstractState :=
    share_state <- result_from_option
                    "remove share state"
                    (ZTree.get index st.(hypervisor_context).(ffa_share_state))
    ;; let '(mkFFA_memory_share_state_struct memory_region _ _ _ _) := share_state in
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
       ret (st { hypervisor_context / api_page_pool_size : new_api_page_pool_size }
               { hypervisor_context / ffa_share_state : new_share_state_pool }).

  Definition unset_retrieve
             (index : Z) (addr : Z) (receiver: ffa_UUID_t) (st: AbstractState) :
    RESULT AbstractState :=
    share_state <- result_from_option
                    "cannot get share state"
                    (ZTree.get index st.(hypervisor_context).(ffa_share_state))
    ;; receiver_retrieve_pool <- result_from_option
                                  "cannot get receiver_retrive_pool"
                                  (ZTree.get receiver share_state.(retrieved))
    ;; let new_retrieved :=
           ZTree.set receiver
                     (ZTree.set addr false  receiver_retrieve_pool)
                     share_state.(retrieved) in
       let new_shared_state :=
           mkFFA_memory_share_state_struct
             share_state.(memory_region) share_state.(share_func) new_retrieved
                                                                  share_state.(relinquished) share_state.(retrieve_count) in
       let new_shared_state_pool :=
           ZTree.set index
                     new_shared_state
                     st.(hypervisor_context).(ffa_share_state) in
       ret (st { hypervisor_context / ffa_share_state : new_shared_state_pool }).
    
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
