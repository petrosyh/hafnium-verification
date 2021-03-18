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
Require Export FFAMemoryHypCallAdditionalStepsAuxiliaryFunctions.

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
(** *  Additional Step Rules for Memory Management                     *)
(***********************************************************************)

Section FFA_MEMORY_INTERFACE_ADDITIONAL_STEPS.

  Context `{abstract_state_context: AbstractStateContext}.
  
  (***********************************************************************)
  (** **   11.1 FFA_MEM_DONATE                                           *)
  (***********************************************************************)
  (***********************************************************************)
  (** **   11.2 FFA_MEM_LEND                                             *)
  (***********************************************************************)
  (***********************************************************************)
  (** **   11.3 FFA_MEM_SHARE                                            *)
  (***********************************************************************)
  
  (** 
      - Structure
        - paramemter
          - stored register
          - description 

      - Table 11.3, 11.8, 11.13: FFA_MEM_DONATE, FFA_MEM_LEND, and FFA_MEM_SHARE function syntax
        - uint32 Function ID
          - w0 
          - 0x84000071
        - uint32 total length
          - w1
          - Total length of the memory transaction descriptor in bytes
        - uint32 Fragment length
          - w2
          - Length in bytes of the memory transaction descriptor passed in this ABI invocation.
          - Fragment length must be <= Total length.
          - If Fragment length < Total length then see 12.2.2 Transmission of transaction 
            descriptor in fragments about how the remainder of the descriptor will be transmitted.
        - uint32/uint64 Address
          - w3
          - Base address of a buffer allocated by the Owner and 
            distinct from the TX buffer. More information is
            in 12.2.1. MBZ if the TX buffer is used.
          - MBZ if the TX buffer is used.
        - uint32 Page count
          - w4
          - Number of 4K page in the buffer allocated by the 
            Owner and distinct from the TX buffer. More details
            are in 12.2.1. MBZ if the TX buffer is used
          - MBZ if the TX buffer is used
        - Other Parameter registers
          - w5-w7
          - Reserved (MBZ).

      - Table 11.4, 11.9, 11.14: FFA_SUCCESS encoding
        - uint64 Handle
          - w2/w3
          - Globally unique Handle to identify the memory 
            region on successful transmission of the transaction descriptor.
        - Other Result registers
          - w4-w7 
          - Reserved (MBZ)
      
      - Table 11.5, 11.10, 11.15: FFA_ERROR encoding
        - int32 Error code
          - w2
          - INVALID_PARAMETERS / DENIED / NO_MEMORY / BUSY / ABORTED
   *)

  (** [JIEUNG: From Section 11.1 to Section 11.3 describe roles of sender and relayer. 
      Those things are captured in the below, so we ignore those texts in here] *)

  Section FFA_MEM_DONATE_ADDITIONAL_STEPS.

    (** - Check each address in constituents to see whether 
          descriptor values are proper for donate operation *)
    Fixpoint donate_checks_per_address
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (addrs: list Z)
             (descriptor_inst_access: FFA_INSTRUCTION_ACCESS_TYPE)
             (descriptor_data_access: FFA_DATA_ACCESS_TYPE)
             (descriptor_attributes: FFA_MEMORY_TYPE)
      : option (FFA_ERROR_CODE_TYPE) :=
      match addrs with
      | nil => None
      | hd::tl =>
        (** - Exctract memory properties and accessibilities *)
        match get_permissions_and_attributes vid hd mem_properties,
              memory_region_descriptor.(FFA_memory_region_struct_flags)with
        | Some (local_inst_access, local_data_access, local_attributes,
                global_inst_access, global_data_access,  global_attributes),
          MEMORY_REGION_FLAG_NORMAL flags =>
          (** - Check descriptor's values are valid with memory properties and accessibilities *)
          match data_permissions_check_donate_lender_check
                  descriptor_data_access global_data_access local_data_access,
                instruction_permissions_donate_and_lend_single_borrower_lender_descriptor_check
                  descriptor_inst_access global_inst_access,
                attributes_donate_and_single_borrower_lender_check
                  descriptor_attributes local_attributes global_attributes,
                check_FFA_mem_default_flags_struct_for_donate_and_lend
                  flags  local_data_access time_slice_enabled with 
          | Some res, _, _, _ 
          | None, Some res, _, _
          | None, None, Some res, _
          | None, None, None, Some res => Some res
          | None, None, None, None =>
            (** - If there are all valid, check the next address *)
            donate_checks_per_address
              vid time_slice_enabled mem_properties
              memory_region_descriptor tl
              descriptor_inst_access
              descriptor_data_access
              descriptor_attributes
          end
        | _, _ => Some (FFA_INVALID_PARAMETERS)
        end
      end.
    
    (** There are some redundancies, but we do not car  e it *)
    (** check additional properties *)
    Definition donate_check
               (vid : ffa_UUID_t)
               (time_slice_enabled: bool)
               (mem_properties: MemProperties)
               (memory_region_descriptor: FFA_memory_region_struct)
               (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z))
      : option (FFA_ERROR_CODE_TYPE) := 
      match decide (memory_region_descriptor.(FFA_memory_region_struct_sender) = vid),
            memory_region_descriptor.(FFA_memory_region_struct_flags),
            info_tuple with
      (** - Donate operation allows only one receiver *)
      | left _, MEMORY_REGION_FLAG_NORMAL flags,  (receiver, receiver_id, addrs)::nil =>
        (** - Check well formed of memory region descriptor *)
        let descriptor_inst_access :=
            get_instruction_access_information_from_descriptor receiver in
        let descriptor_data_access :=
            get_data_access_information_from_descriptor receiver in
        let descriptor_attributes :=
            get_attributes_information_from_descriptor memory_region_descriptor in
        
        match well_formed_FFA_memory_region_struct
                vid memory_region_descriptor FFA_MEM_DONATE,
              donate_checks_per_address
                vid time_slice_enabled
                mem_properties memory_region_descriptor addrs
                descriptor_inst_access descriptor_data_access
                descriptor_attributes with
        | Some res, _
        | None, Some res => Some res
        | None, None =>
          (** - Check access and attributes *)
          (** - Extract descriptor's access and attribute values *)
          (FFA_memory_access_permissions_descriptor_struct_flags_check
             FFA_MEM_DONATE
             (receiver
              .(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor))
             (Zlength info_tuple))
        end
      | _, _, _ => Some (FFA_INVALID_PARAMETERS)
      end.
    
    (** - Change memory ownership and accessibilities for all addresses. 
          If it encouter errors, it will revert the change and return the original state *)
    Fixpoint apply_ffa_mem_donate_core_transition_spec
             (caller receiver_id : ffa_UUID_t) (addresses : list Z)
             (st : AbstractState) :=
      match addresses with
      | nil => Some (st, true)
      | hd::tl =>
        match apply_ffa_mem_donate_core_transition_spec
                caller receiver_id tl st with
        | Some st'' =>
          ffa_mem_donate_core_transition_spec
            caller receiver_id hd (fst st'') 
        | None => None
        end
      end.
                   
    Definition ffa_mem_donate_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (st: AbstractState)
      : option (AbstractState * FFA_RESULT_CODE_TYPE) :=
      (** - Check the arguments *)
      if ffa_mem_send_check_arguments total_length fragment_length address count
      then
        (** - Get the current memory region descriptor *)
        do memory_region_descriptor <-
           get_send_memory_region_descriptor caller st ;;;
        do receivers_info <-
           get_recievers_receiver_ids_and_addresses_tuple
             memory_region_descriptor ;;;
           (** - Check the well_formed conditions of the memory region descriptor *)
          if decide ((length (get_receivers memory_region_descriptor) = 1)%nat)
          then
            let region_size
                := (FFA_memory_region_struct_size
                      (Zlength
                         (memory_region_descriptor
                          .(FFA_memory_region_struct_composite)
                          .(FFA_composite_memory_region_struct_constituents)))) in
            if decide ((st.(hypervisor_context).(api_page_pool_size)
                        < region_size)%Z)
            then
              match receivers_info with
              | (receiver, receiver_id, cur_addresses)::nil =>
                (* TODO: add cases to handle multiple address transfer *)
                match (donate_check
                         caller
                         (st.(hypervisor_context).(time_slice_enabled))
                         (st.(hypervisor_context).(mem_properties))
                         memory_region_descriptor receivers_info) with 
                | None =>
                  do res <- apply_ffa_mem_donate_core_transition_spec
                             caller receiver_id cur_addresses st ;;;
                  match res with  
                  (* TODO: need to creage handle! - 0 is the wrong value  *)
                  (* TODO: need to reduce mpool size *) 
                  | (st', true) =>
                    match set_memory_region_in_shared_state
                            caller
                            region_size FFA_MEM_DONATE
                            ((receiver_id, cur_addresses)::nil)
                            None false
                            memory_region_descriptor st' with
                    | Some (st'', handle_value) =>
                      do res_st <- set_send_handle caller receiver_id
                                                  region_size handle_value FFA_MEM_DONATE
                                                  st'' ;;;
                      Some (res_st, FFA_SUCCESS handle_value)
                    | _ => Some (st, FFA_ERROR FFA_DENIED)
                    end
                  | (_, false) => Some (st, FFA_ERROR FFA_DENIED)
                  end
                | Some res => Some (st, FFA_ERROR res)
                end
              | _ => Some (st, FFA_ERROR FFA_INVALID_PARAMETERS)
              end
            else Some (st, FFA_ERROR FFA_NO_MEMORY)
          else Some (st, FFA_ERROR FFA_DENIED)
      else Some (st, FFA_ERROR FFA_INVALID_PARAMETERS).
    
  End FFA_MEM_DONATE_ADDITIONAL_STEPS.

  Section FFA_MEM_LEND_ADDITIONAL_STEPS.

    Fixpoint lend_checks_per_address 
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (addrs: list Z)
             (descriptor_inst_access: FFA_INSTRUCTION_ACCESS_TYPE)
             (descriptor_data_access: FFA_DATA_ACCESS_TYPE)
             (descriptor_attributes: FFA_MEMORY_TYPE)
             (receiver_number : Z)             
      : option (FFA_ERROR_CODE_TYPE) :=
      match addrs with
      | nil => None                
      | hd::tl =>
        match get_permissions_and_attributes vid hd mem_properties,
              memory_region_descriptor.(FFA_memory_region_struct_flags) with        
        | Some (local_inst_access, local_data_access, local_attributes,
                global_inst_access, global_data_access,  global_attributes),
          MEMORY_REGION_FLAG_NORMAL flags =>
          match data_permissions_lend_and_share_lender_check
                  descriptor_data_access global_data_access local_data_access,
                check_FFA_mem_default_flags_struct_for_donate_and_lend
                  flags local_data_access time_slice_enabled with
          | Some res, _ 
          | None, Some res => Some res
          | None, None =>
            if (decide (receiver_number = 1))
            then 
              match instruction_permissions_donate_and_lend_single_borrower_lender_descriptor_check
                      descriptor_inst_access global_inst_access,
                    attributes_donate_and_single_borrower_lender_check
                      descriptor_attributes local_attributes global_attributes with
              | Some res, _
              | None, Some res => Some res
              | None, None =>
                lend_checks_per_address
                  vid time_slice_enabled mem_properties memory_region_descriptor
                  tl descriptor_inst_access descriptor_data_access descriptor_attributes
                  receiver_number
              end
            else
              match instruction_permissions_share_and_lend_multiple_borrower_lender_check
                      descriptor_inst_access global_inst_access,
                    attributes_share_and_multiple_borrowers_borrower_check
                      descriptor_attributes global_attributes with
              | Some res, _
              | None, Some res => Some res
              | None, None =>
                lend_checks_per_address
                  vid time_slice_enabled mem_properties memory_region_descriptor
                  tl descriptor_inst_access descriptor_data_access descriptor_attributes
                  receiver_number
              end
          end
        | _, _ => Some (FFA_INVALID_PARAMETERS)
        end
      end.


    (** There are some redundancies, but we do not care it *)
    (** check additional properties *)
    Fixpoint lend_check_iterations 
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z))
             (receiver_number : Z)             
      : option (FFA_ERROR_CODE_TYPE) := 
      match info_tuple with
      | nil => None
      | (receiver, receiver_id, addrs)::tl => 
        (** - Extract descriptor's access and attribute values *)
        let descriptor_inst_access :=
            get_instruction_access_information_from_descriptor receiver in
        let descriptor_data_access :=
            get_data_access_information_from_descriptor receiver in
        let descriptor_attributes :=
            get_attributes_information_from_descriptor memory_region_descriptor in
        match lend_check_iterations vid time_slice_enabled mem_properties
                                    memory_region_descriptor tl receiver_number,
              lend_checks_per_address vid time_slice_enabled
                                      mem_properties memory_region_descriptor addrs
                                      descriptor_inst_access descriptor_data_access
                                      descriptor_attributes receiver_number with
        | Some res, _
        | None, Some res => Some res
        | None, None =>
          (FFA_memory_access_permissions_descriptor_struct_flags_check
             FFA_MEM_LEND
             (receiver
              .(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor))
             (Zlength info_tuple))
        end
      end.
    
    Definition lend_check
               (vid : ffa_UUID_t)
               (time_slice_enabled: bool)
               (mem_properties: MemProperties)
               (memory_region_descriptor: FFA_memory_region_struct)
               (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z))
      : option (FFA_ERROR_CODE_TYPE) := 
      if decide (memory_region_descriptor.(FFA_memory_region_struct_sender) = vid) &&
         decide (Zlength info_tuple <> 0) 
      then
        (** - Check well formed of memory region descriptor *)
        match well_formed_FFA_memory_region_struct
                vid memory_region_descriptor FFA_MEM_DONATE with
        | None =>
          lend_check_iterations vid time_slice_enabled
                                mem_properties memory_region_descriptor
                                info_tuple (Zlength info_tuple)
        | Some res => Some res
        end
      else Some (FFA_INVALID_PARAMETERS).
    
    (** - Change memory ownership and accessibilities for all addresses. 
          If it encouter errors, it will revert the change and return the original state *)
    Fixpoint apply_ffa_mem_lend_core_transition_spec
             (caller : ffa_UUID_t) (receivers: list ffa_UUID_t) (addresses : list Z)
             (st : AbstractState) :=
      match addresses with
      | nil => Some (st, true)
      | hd::tl =>
        match apply_ffa_mem_lend_core_transition_spec
                caller receivers tl st with
        | Some st'' =>
          ffa_mem_lend_core_transition_spec
            caller receivers hd (fst st'') 
        | None => None
        end
      end.
    
    Definition ffa_mem_lend_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (st: AbstractState)
      : option (AbstractState * FFA_RESULT_CODE_TYPE) :=
      (** - Check the arguments *)
      if ffa_mem_send_check_arguments total_length fragment_length address count
      then
        (** - Get the current memory region descriptor *)
        do memory_region_descriptor <-
           get_send_memory_region_descriptor caller st ;;;
        do receivers_info <-
           get_recievers_receiver_ids_and_addresses_tuple
             memory_region_descriptor ;;;
           (** - Check the well_formed conditions of the memory region descriptor *)
          if decide ((length (get_receivers memory_region_descriptor) = 1)%nat)
          then
            let region_size
                := (FFA_memory_region_struct_size
                      (Zlength
                         (memory_region_descriptor
                          .(FFA_memory_region_struct_composite)
                          .(FFA_composite_memory_region_struct_constituents)))) in
            if decide ((st.(hypervisor_context).(api_page_pool_size)
                        < region_size)%Z)
            then
              match (lend_check
                       caller
                       (st.(hypervisor_context).(time_slice_enabled))
                       (st.(hypervisor_context).(mem_properties))
                       memory_region_descriptor receivers_info) with 
              | None =>
                (* TODO: add cases to handle multiple address transfer *)
                do res <- apply_ffa_mem_lend_core_transition_spec
                           caller (get_receiver_ids receivers_info)
                           (get_all_addresses memory_region_descriptor)
                           st ;;;
                match res with  
                (* TODO: need to creage handle! - 0 is the wrong value  *)
                (* TODO: need to reduce mpool size *) 
                | (st', true) =>
                  match set_memory_region_in_shared_state
                          caller
                          region_size FFA_MEM_LEND
                          (get_receiver_id_addrs_pair receivers_info)
                          None false
                          memory_region_descriptor st' with
                  | Some (st'', handle_value) =>
                    do res_st <- set_send_handle_for_multiple_receivers
                                  (get_receiver_ids receivers_info)
                                  caller
                                  region_size handle_value FFA_MEM_LEND
                                  st'' ;;;
                    Some (res_st, FFA_SUCCESS handle_value)
                  | _ => Some (st, FFA_ERROR FFA_DENIED)
                  end
                  | (_, false) => Some (st, FFA_ERROR FFA_DENIED)
                end
              | Some res => Some (st, FFA_ERROR res)
              end
            else Some (st, FFA_ERROR FFA_NO_MEMORY)
          else Some (st, FFA_ERROR FFA_DENIED)
      else Some (st, FFA_ERROR FFA_INVALID_PARAMETERS).
    
  End FFA_MEM_LEND_ADDITIONAL_STEPS.
  
  Section FFA_MEM_SHARE_ADDITIONAL_STEPS.
    
    Fixpoint share_checks_per_address 
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (addrs: list Z)
             (descriptor_inst_access: FFA_INSTRUCTION_ACCESS_TYPE)
             (descriptor_data_access: FFA_DATA_ACCESS_TYPE)
             (descriptor_attributes: FFA_MEMORY_TYPE)
             (receiver_number : Z)             
      : option (FFA_ERROR_CODE_TYPE) :=
      match addrs with
      | nil => None
      | hd::tl =>
        match get_permissions_and_attributes vid hd mem_properties,
              memory_region_descriptor.(FFA_memory_region_struct_flags)with
        | Some (local_inst_access, local_data_access, local_attributes,
                global_inst_access, global_data_access,  global_attributes),
          MEMORY_REGION_FLAG_NORMAL flags =>
          match data_permissions_lend_and_share_lender_check
                  descriptor_data_access global_data_access local_data_access,
                check_FFA_mem_default_flags_struct_for_share flags time_slice_enabled,
                instruction_permissions_share_and_lend_multiple_borrower_lender_check
                  descriptor_inst_access global_inst_access,
                attributes_share_and_multiple_borrowers_borrower_check
                  descriptor_attributes global_attributes with
          | Some res, _, _, _
          | None, Some res, _, _
          | None, None, Some res, _
          | None, None, None, Some res => Some res
          | None, None, None, None =>
            lend_checks_per_address
              vid time_slice_enabled mem_properties memory_region_descriptor
              tl descriptor_inst_access descriptor_data_access descriptor_attributes
              receiver_number
          end
        | _, _ => Some (FFA_INVALID_PARAMETERS)
        end
      end.

    (** There are some redundancies, but we do not care it *)
    (** check additional properties *)
    Fixpoint share_check_iterations 
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z))
             (receiver_number : Z)             
      : option (FFA_ERROR_CODE_TYPE) := 

      match info_tuple with
      | nil => None
      | (receiver, receiver_id, addrs)::tl =>
        (** - Extract descriptor's access and attribute values *)
        let descriptor_inst_access :=
            get_instruction_access_information_from_descriptor receiver in
        let descriptor_data_access :=
            get_data_access_information_from_descriptor receiver in
        let descriptor_attributes :=
            get_attributes_information_from_descriptor memory_region_descriptor in
        match share_check_iterations vid time_slice_enabled mem_properties memory_region_descriptor
                                     tl receiver_number,
              share_checks_per_address vid time_slice_enabled
                                       mem_properties memory_region_descriptor addrs
                                       descriptor_inst_access descriptor_data_access
                                       descriptor_attributes receiver_number with 
        | Some res, _
        | None, Some res => Some res
        | None, None => 
          (FFA_memory_access_permissions_descriptor_struct_flags_check
             FFA_MEM_SHARE
             (receiver
              .(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor))
             (Zlength info_tuple))
        end
      end.
    
    Definition share_check
               (vid : ffa_UUID_t)
               (time_slice_enabled: bool)
               (mem_properties: MemProperties)
               (memory_region_descriptor: FFA_memory_region_struct)
               (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z))
      : option (FFA_ERROR_CODE_TYPE) := 
      if decide (memory_region_descriptor.(FFA_memory_region_struct_sender) = vid) &&
         decide (Zlength info_tuple <> 0)
      then
        (** - Check well formed of memory region descriptor *)
        match well_formed_FFA_memory_region_struct
                vid memory_region_descriptor FFA_MEM_DONATE with
        | None =>
          match memory_region_descriptor
                .(FFA_memory_region_struct_flags) with
          | MEMORY_REGION_FLAG_NORMAL flags =>
            (** - Check access and attributes *)
            share_check_iterations vid time_slice_enabled
                                   mem_properties memory_region_descriptor
                                   info_tuple (Zlength info_tuple)
          | _ => Some (FFA_INVALID_PARAMETERS)
          end
        | Some res => Some res
        end
      else Some (FFA_INVALID_PARAMETERS).

    (** - Change memory ownership and accessibilities for all addresses. 
          If it encouter errors, it will revert the change and return the original state *)
    Fixpoint apply_ffa_mem_share_core_transition_spec
             (caller : ffa_UUID_t) (receivers: list ffa_UUID_t) (addresses : list Z)
             (st : AbstractState) :=
      match addresses with
      | nil => Some (st, true)
      | hd::tl =>
        match apply_ffa_mem_share_core_transition_spec
                caller receivers tl st with
        | Some st'' =>
          ffa_mem_share_core_transition_spec
            caller receivers hd (fst st'') 
        | None => None
        end
      end.
   
    Definition ffa_mem_share_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (st: AbstractState)
      : option (AbstractState * FFA_RESULT_CODE_TYPE) :=
      (** - Check the arguments *)
      if ffa_mem_send_check_arguments total_length fragment_length address count
      then
        (** - Get the current memory region descriptor *)
        do memory_region_descriptor <-
           get_send_memory_region_descriptor caller st ;;;
        do receivers_info <-
           get_recievers_receiver_ids_and_addresses_tuple
             memory_region_descriptor ;;;
           (** - Check the well_formed conditions of the memory region descriptor *)
          if decide ((length (get_receivers memory_region_descriptor) = 1)%nat)
          then
            let region_size
                := (FFA_memory_region_struct_size
                      (Zlength
                         (memory_region_descriptor
                          .(FFA_memory_region_struct_composite)
                          .(FFA_composite_memory_region_struct_constituents)))) in
            if decide ((st.(hypervisor_context).(api_page_pool_size)
                        < region_size)%Z)
            then
              match (share_check
                       caller
                       (st.(hypervisor_context).(time_slice_enabled))
                       (st.(hypervisor_context).(mem_properties))
                       memory_region_descriptor receivers_info) with 
              | None =>
                (* TODO: add cases to handle multiple address transfer *)
                do res <- apply_ffa_mem_share_core_transition_spec
                           caller (get_receiver_ids receivers_info)
                           (get_all_addresses memory_region_descriptor)
                           st ;;;
                match res with  
                (* TODO: need to creage handle! - 0 is the wrong value  *)
                (* TODO: need to reduce mpool size *) 
                | (st', true) =>
                  match set_memory_region_in_shared_state
                          caller
                          region_size FFA_MEM_SHARE
                          (get_receiver_id_addrs_pair receivers_info)
                          None false
                          memory_region_descriptor st' with
                  | Some (st'', handle_value) =>
                    do res_st <- set_send_handle_for_multiple_receivers
                                  (get_receiver_ids receivers_info)
                                  caller
                                  region_size handle_value FFA_MEM_SHARE
                                  st'' ;;;
                    Some (res_st, FFA_SUCCESS handle_value)
                  | _ => Some (st, FFA_ERROR FFA_DENIED) 
                  end
                | (_, false) => Some (st, FFA_ERROR FFA_DENIED)
                end
              | _ => Some (st, FFA_ERROR FFA_INVALID_PARAMETERS)
              end
            else Some (st, FFA_ERROR FFA_NO_MEMORY)
          else Some (st, FFA_ERROR FFA_DENIED)
      else Some (st, FFA_ERROR FFA_INVALID_PARAMETERS).
    
  End FFA_MEM_SHARE_ADDITIONAL_STEPS.

  Section FFA_MEM_RETRIEVE_REQ_ARGUMENT_CHECKS.
    (***********************************************************************)
    (** ***  11.4 FFA_MEM_RETRIEVE_REQ                                     *)
    (***********************************************************************)
    (** 
      - Structure
        - paramemter
          - stored register
          - description 

      - Table 11.18: FFA_MEM_RETRIEVE_REQ function syntax
        - uint32 Function ID
          - w0
          - 0x84000074
        - uint32 Total length
          - w1
          - Total length of the memory transaction descriptor in bytes.
        - uint32 Fragment length 
          - w2
          - Length in bytes of the memory transaction descriptor passed in this ABI invocation.
          - Fragment length must be <= Total length.
          - If Fragment length < Total length then see 12.2.2 Transmission of transaction 
            descriptor in fragments about how the remainder of the descriptor will be
            transmitted.
        - uint32/uint64 Address
          - w3
          - Base address of a buffer allocated by the Owner and distinct from the TX buffer. See 12.2.1
            Transmission of transaction descriptor in dynamically allocated buffers.
          - MBZ if the TX buffer is used.
        - uint32 Page count
          - w4
          - Number of 4K pages in the buffer allocated by the 
            Owner and distinct from the TX buffer. See 12.2.1
            Transmission of transaction descriptor in dynamically allocated buffers.
          - MBZ if the TX buffer is used.
        - Other Parameter registers 
          - w5-w7
          - Reserved (MBZ)

      - Table 11.19: FFA_ERROR encoding
        - int32 Error code 
          - w2
          - INVALID_PARAMETERS / DENIED / NO_MEMORY / BUSY / ABORTED
     *)

    Fixpoint donate_retrieve_req_checks_per_address
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (addrs: list Z)
             (descriptor_inst_access: FFA_INSTRUCTION_ACCESS_TYPE)
             (descriptor_data_access: FFA_DATA_ACCESS_TYPE)
             (descriptor_attributes: FFA_MEMORY_TYPE)
      : option (FFA_ERROR_CODE_TYPE) :=
      match addrs with
      | nil => None
      | hd::tl =>
        (** - Exctract memory properties and accessibilities *)
        match get_permissions_and_attributes vid hd mem_properties,
              memory_region_descriptor.(FFA_memory_region_struct_flags) with
        | Some (local_inst_access, local_data_access, local_attributes,
                global_inst_access, global_data_access,  global_attributes),
          MEMORY_REGION_FLAG_NORMAL flags =>
          (** - Check descriptor's values are valid with memory properties and accessibilities *)
          match data_permissions_borrower_check
                  global_data_access descriptor_data_access,
                instruction_permissions_donate_and_lend_single_borrower_borrower_descriptor_check
                  global_inst_access descriptor_inst_access,
                attributes_donate_and_single_borrower_borrower_check
                  descriptor_attributes global_attributes,
                check_FFA_mem_default_flags_struct_for_donate_and_lend_retrieve
                  flags time_slice_enabled with 
          | Some res, _, _, _ 
          | None, Some res, _, _
          | None, None, Some res, _
          | None, None, None, Some res => Some res
          | None, None, None, None =>
            (** - If there are all valid, check the next address *)
            donate_retrieve_req_checks_per_address
              vid time_slice_enabled mem_properties
              memory_region_descriptor tl
              descriptor_inst_access
              descriptor_data_access
              descriptor_attributes
          end
        | _, _ => Some (FFA_INVALID_PARAMETERS)
        end
      end.

    (** There are some redundancies, but we do not car  e it *)
    (** check additional properties *)
    Definition donate_retrieve_req_check
               (vid : ffa_UUID_t)
               (time_slice_enabled: bool)
               (mem_properties: MemProperties)
               (memory_region_descriptor: FFA_memory_region_struct)
               (receiver_ids : list ffa_UUID_t)
               (receiver_tuple : (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z))
               (receiver_num: Z)
      : option (FFA_ERROR_CODE_TYPE) :=
      match decide (in_dec zeq vid receiver_ids),
            memory_region_descriptor.(FFA_memory_region_struct_flags),
            receiver_tuple with
      (** - Donate operation allows only one receiver *)
      | left _, MEMORY_REGION_FLAG_NORMAL flags,  (receiver, receiver_id, addrs) =>
        (** - Check well formed of memory region descriptor *)
        let descriptor_inst_access :=
            get_instruction_access_information_from_descriptor receiver in
        let descriptor_data_access :=
            get_data_access_information_from_descriptor receiver in
        let descriptor_attributes :=
            get_attributes_information_from_descriptor memory_region_descriptor in
        
        match donate_retrieve_req_checks_per_address
                vid time_slice_enabled
                mem_properties memory_region_descriptor addrs
                descriptor_inst_access descriptor_data_access
                descriptor_attributes with
        | Some res => Some res
        | None =>
          (** - Check access and attributes *)
          (** - Extract descriptor's access and attribute values *)
          (FFA_memory_access_permissions_descriptor_struct_flags_check
             FFA_MEM_RETREIVE_REQ
             (receiver
              .(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor))
             receiver_num)
        end
      | _, _, _ => Some (FFA_INVALID_PARAMETERS)
      end.

    (** - Change memory ownership and accessibilities for all addresses. 
          If it encouter errors, it will revert the change and return the original state *)
    Fixpoint apply_ffa_mem_donate_retrieve_req_core_transition_spec
             (lender borrower : ffa_UUID_t) (addresses : list Z) (clean : bool)
             (st : AbstractState) :=
      match addresses with
      | nil => Some (st, true)
      | hd::tl =>
        match apply_ffa_mem_donate_retrieve_req_core_transition_spec
                lender borrower tl clean st with
        | Some st' =>
          ffa_mem_donate_retrieve_req_core_transition_spec
            lender borrower hd clean (fst st')
        | None => None
        end
      end.
    
    Definition ffa_mem_retrieve_req_donate_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (region_descriptor : FFA_memory_region_struct)
               (st : AbstractState)
      : option (AbstractState * FFA_RESULT_CODE_TYPE) :=
        (** - Get the current memory region descriptor *)
      do receivers_info <-
         get_recievers_receiver_ids_and_addresses_tuple region_descriptor ;;;
     (** - Check the well_formed conditions of the memory region descriptor *)
     if decide ((length (get_receivers region_descriptor) = 1)%nat)
     then
       match receivers_info with
       | (receiver, receiver_id, cur_addresses)::nil =>
         (* TODO: add cases to handle multiple address transfer *)
         match (donate_retrieve_req_check
                  caller
                  (st.(hypervisor_context).(time_slice_enabled))
                  (st.(hypervisor_context).(mem_properties))
                  region_descriptor
                  (get_receiver_ids receivers_info)
                  (receiver, receiver_id, cur_addresses)
                  (Zlength (get_receivers region_descriptor))) with 
         | None =>
           do res <- apply_ffa_mem_donate_core_transition_spec
                      caller receiver_id cur_addresses st ;;;
           match res with  
           (* TODO: need to creage handle! - 0 is the wrong value  *)
           (* TODO: need to reduce mpool size *) 
           | (st', true) =>
             let region_size
                 := (FFA_memory_region_struct_size
                       (Zlength
                          (region_descriptor
                           .(FFA_memory_region_struct_composite)
                           .(FFA_composite_memory_region_struct_constituents)))) in                    
             match set_memory_region_in_shared_state
                     caller
                     region_size FFA_MEM_DONATE
                     ((receiver_id, cur_addresses)::nil)
                     None true
                     region_descriptor st' with                    
             | Some (st'', value) =>
               do handle_value <- make_handle caller value;;;
               do res_st <- set_send_handle caller receiver_id
                                           region_size handle_value FFA_MEM_RETREIVE_RESP
                                           st'' ;;;
               Some (res_st, FFA_SUCCESS value)
             | None => Some (st, FFA_ERROR FFA_DENIED)
             end
           | (_, false) => Some (st, FFA_ERROR FFA_DENIED)
           end
         | Some res => Some (st, FFA_ERROR res)
         end
       | _ => Some (st, FFA_ERROR FFA_INVALID_PARAMETERS)
       end
     else Some (st, FFA_ERROR FFA_DENIED).


    Fixpoint lend_retrieve_req_checks_per_address
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (addrs: list Z)
             (descriptor_inst_access: FFA_INSTRUCTION_ACCESS_TYPE)
             (descriptor_data_access: FFA_DATA_ACCESS_TYPE)
             (descriptor_attributes: FFA_MEMORY_TYPE)
             (borrower_number : Z)
      : option (FFA_ERROR_CODE_TYPE) :=
      match addrs with
      | nil => None
      | hd::tl =>
        (** - Exctract memory properties and accessibilities *)
        match get_permissions_and_attributes vid hd mem_properties,
              memory_region_descriptor.(FFA_memory_region_struct_flags) with
        | Some (local_inst_access, local_data_access, local_attributes,
                global_inst_access, global_data_access,  global_attributes),
          MEMORY_REGION_FLAG_NORMAL flags =>
          (** - Check descriptor's values are valid with memory properties and accessibilities *)
          match data_permissions_borrower_check
                  global_data_access descriptor_data_access,
                check_FFA_mem_default_flags_struct_for_donate_and_lend_retrieve
                  flags time_slice_enabled with 
          | Some res, _ 
          | None, Some res => Some res
          | None, None =>
            if decide (borrower_number = 1)
            then
              match instruction_permissions_donate_and_lend_single_borrower_borrower_descriptor_check
                      global_inst_access descriptor_inst_access,
                    attributes_donate_and_single_borrower_borrower_check
                      descriptor_attributes global_attributes with
              | Some res, _ 
              | None, Some res => Some res
              | None, None =>
                (** - If there are all valid, check the next address *)
                lend_retrieve_req_checks_per_address
                  vid time_slice_enabled mem_properties
                  memory_region_descriptor tl
                  descriptor_inst_access
                  descriptor_data_access
                  descriptor_attributes
                  borrower_number
              end
            else
              match instruction_permissions_share_and_lend_multiple_borrower_borrower_descriptor_check
                      global_inst_access descriptor_inst_access,
                    attributes_share_and_multiple_borrowers_borrower_check
                      descriptor_attributes global_attributes with
              | Some res, _ 
              | None, Some res => Some res
              | None, None =>
                (** - If there are all valid, check the next address *)
                lend_retrieve_req_checks_per_address
                  vid time_slice_enabled mem_properties
                  memory_region_descriptor tl
                  descriptor_inst_access
                  descriptor_data_access
                  descriptor_attributes
                  borrower_number
              end
          end
        | _, _ => Some (FFA_INVALID_PARAMETERS)
        end
      end.

    (** There are some redundancies, but we do not car  e it *)
    (** check additional properties *)
    Definition lend_retrieve_req_check
               (vid : ffa_UUID_t)
               (time_slice_enabled: bool)
               (mem_properties: MemProperties)
               (memory_region_descriptor: FFA_memory_region_struct)
               (receiver_ids : list ffa_UUID_t)
               (receiver_tuple : (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z))
               (receiver_num: Z)
      : option (FFA_ERROR_CODE_TYPE) :=
      match decide (in_dec zeq vid receiver_ids),
            memory_region_descriptor.(FFA_memory_region_struct_flags),
            receiver_tuple with
      (** - Donate operation allows only one receiver *)
      | left _, MEMORY_REGION_FLAG_NORMAL flags,  (receiver, receiver_id, addrs) =>
        (** - Check well formed of memory region descriptor *)
        let descriptor_inst_access :=
            get_instruction_access_information_from_descriptor receiver in
        let descriptor_data_access :=
            get_data_access_information_from_descriptor receiver in
        let descriptor_attributes :=
            get_attributes_information_from_descriptor memory_region_descriptor in
        
        match lend_retrieve_req_checks_per_address
                vid time_slice_enabled
                mem_properties memory_region_descriptor addrs
                descriptor_inst_access descriptor_data_access
                descriptor_attributes receiver_num with
        | Some res => Some res
        | None =>
          (** - Check access and attributes *)
          (** - Extract descriptor's access and attribute values *)
          (FFA_memory_access_permissions_descriptor_struct_flags_check
             FFA_MEM_RETREIVE_REQ
             (receiver
              .(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor))
             receiver_num)
        end
      | _, _, _ => Some (FFA_INVALID_PARAMETERS)
      end.
         
    Fixpoint apply_ffa_mem_lend_retrieve_req_core_transition_spec
             (lender borrower : ffa_UUID_t) (borrower_num : Z) (addresses : list Z) (clean : bool)
             (st : AbstractState) :=
      match addresses with
      | nil => Some (st, true)
      | hd::tl =>
        match apply_ffa_mem_lend_retrieve_req_core_transition_spec
                lender borrower borrower_num tl clean st with
        | Some st' =>
          ffa_mem_lend_retrieve_req_core_transition_spec
            lender borrower borrower_num hd clean (fst st')
        | None => None
        end
      end.
    
    Definition ffa_mem_retrieve_req_lend_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (region_descriptor : FFA_memory_region_struct)
               (st : AbstractState)
    : option (AbstractState * FFA_RESULT_CODE_TYPE) :=
        (** - Get the current memory region descriptor *)
      do receivers_info <-
         get_recievers_receiver_ids_and_addresses_tuple region_descriptor ;;;
      do receiver_info <-
         get_receiver_tuple caller region_descriptor ;;;
     (** - Check the well_formed conditions of the memory region descriptor *)
     match receiver_info with
     | (receiver, receiver_id, cur_addresses) =>
       (* TODO: add cases to handle multiple address transfer *)
       match (lend_retrieve_req_check
                caller
                (st.(hypervisor_context).(time_slice_enabled))
                (st.(hypervisor_context).(mem_properties))
                region_descriptor
                (get_receiver_ids receivers_info)
                (receiver, receiver_id, cur_addresses)
                (Zlength (get_receivers region_descriptor))) with 
       | None =>
         do zero_flag_value <- get_zero_flag_value region_descriptor;;;
         do res <- apply_ffa_mem_lend_retrieve_req_core_transition_spec
                    caller receiver_id
                    (Zlength (get_receivers region_descriptor))
                    cur_addresses
                    zero_flag_value
                    st ;;;
         match res with  
         (* TODO: need to creage handle! - 0 is the wrong value  *)
         (* TODO: need to reduce mpool size *) 
         | (st', true) =>
           let region_size
               := (FFA_memory_region_struct_size
                     (Zlength
                        (region_descriptor
                         .(FFA_memory_region_struct_composite)
                         .(FFA_composite_memory_region_struct_constituents)))) in                    
           match set_memory_region_in_shared_state
                   caller
                   region_size FFA_MEM_LEND
                   ((receiver_id, cur_addresses)::nil)
                   None true
                   region_descriptor st' with                    
           | Some (st'', value) =>
             do handle_value <- make_handle caller value;;;
             do res_st <- set_send_handle caller receiver_id
                                         region_size handle_value FFA_MEM_RETREIVE_RESP
                                         st'' ;;;
             Some (res_st, FFA_SUCCESS value)
           | None => Some (st, FFA_ERROR FFA_DENIED)
           end
         | (_, false) => Some (st, FFA_ERROR FFA_DENIED)
         end
       | Some res => Some (st, FFA_ERROR res)
       end
     end. 


    Fixpoint share_retrieve_req_checks_per_address
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (addrs: list Z)
             (descriptor_inst_access: FFA_INSTRUCTION_ACCESS_TYPE)
             (descriptor_data_access: FFA_DATA_ACCESS_TYPE)
             (descriptor_attributes: FFA_MEMORY_TYPE)
      : option (FFA_ERROR_CODE_TYPE) :=
      match addrs with
      | nil => None
      | hd::tl =>
        (** - Exctract memory properties and accessibilities *)
        match get_permissions_and_attributes vid hd mem_properties,
              memory_region_descriptor.(FFA_memory_region_struct_flags) with
        | Some (local_inst_access, local_data_access, local_attributes,
                global_inst_access, global_data_access,  global_attributes),
          MEMORY_REGION_FLAG_NORMAL flags =>
          (** - Check descriptor's values are valid with memory properties and accessibilities *)
          match data_permissions_borrower_check
                  global_data_access descriptor_data_access,
                check_FFA_mem_default_flags_struct_for_donate_and_lend_retrieve
                  flags time_slice_enabled,
                instruction_permissions_share_and_lend_multiple_borrower_borrower_descriptor_check
                  global_inst_access descriptor_inst_access,
                attributes_share_and_multiple_borrowers_borrower_check
                  descriptor_attributes global_attributes with                 
          | Some res, _, _, _ 
          | None, Some res, _, _
          | None, None, Some res, _
          | None, None, None, Some res => Some res
          | None, None, None, None =>
            (** - If there are all valid, check the next address *)
            share_retrieve_req_checks_per_address
              vid time_slice_enabled mem_properties
              memory_region_descriptor tl
              descriptor_inst_access
              descriptor_data_access
              descriptor_attributes
          end
        | _, _ => Some (FFA_INVALID_PARAMETERS)
        end
      end.

    (** There are some redundancies, but we do not car  e it *)
    (** check additional properties *)
    Definition share_retrieve_req_check
               (vid : ffa_UUID_t)
               (time_slice_enabled: bool)
               (mem_properties: MemProperties)
               (memory_region_descriptor: FFA_memory_region_struct)
               (receiver_ids : list ffa_UUID_t)
               (receiver_tuple : (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z))
               (receiver_num: Z)
      : option (FFA_ERROR_CODE_TYPE) :=
      match decide (in_dec zeq vid receiver_ids),
            memory_region_descriptor.(FFA_memory_region_struct_flags),
            receiver_tuple with
      (** - Donate operation allows only one receiver *)
      | left _, MEMORY_REGION_FLAG_NORMAL flags,  (receiver, receiver_id, addrs) =>
        (** - Check well formed of memory region descriptor *)
        let descriptor_inst_access :=
            get_instruction_access_information_from_descriptor receiver in
        let descriptor_data_access :=
            get_data_access_information_from_descriptor receiver in
        let descriptor_attributes :=
            get_attributes_information_from_descriptor memory_region_descriptor in
        
        match share_retrieve_req_checks_per_address
                vid time_slice_enabled
                mem_properties memory_region_descriptor addrs
                descriptor_inst_access descriptor_data_access
                descriptor_attributes with
        | Some res => Some res
        | None =>
          (** - Check access and attributes *)
          (** - Extract descriptor's access and attribute values *)
          (FFA_memory_access_permissions_descriptor_struct_flags_check
             FFA_MEM_RETREIVE_REQ
             (receiver
              .(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor))
             receiver_num)
        end
      | _, _, _ => Some (FFA_INVALID_PARAMETERS)
      end.
                
    Fixpoint apply_ffa_mem_share_retrieve_req_core_transition_spec
             (lender borrower : ffa_UUID_t) (addresses : list Z) (clean : bool)
             (st : AbstractState) :=
      match addresses with
      | nil => Some (st, true)
      | hd::tl =>
        match apply_ffa_mem_share_retrieve_req_core_transition_spec
                lender borrower tl clean st with
        | Some st' =>
          ffa_mem_share_retrieve_req_core_transition_spec
            lender borrower hd clean (fst st')
        | None => None
        end
      end.
    
    Definition ffa_mem_retrieve_req_share_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (region_descriptor : FFA_memory_region_struct)
               (st : AbstractState)
      : option (AbstractState * FFA_RESULT_CODE_TYPE) :=
        (** - Get the current memory region descriptor *)
      do receivers_info <-
         get_recievers_receiver_ids_and_addresses_tuple region_descriptor ;;;
      do receiver_info <-
         get_receiver_tuple caller region_descriptor ;;;
     (** - Check the well_formed conditions of the memory region descriptor *)
     match receiver_info with
     | (receiver, receiver_id, cur_addresses) =>
       (* TODO: add cases to handle multiple address transfer *)
       match (lend_retrieve_req_check
                caller
                (st.(hypervisor_context).(time_slice_enabled))
                (st.(hypervisor_context).(mem_properties))
                region_descriptor
                (get_receiver_ids receivers_info)
                (receiver, receiver_id, cur_addresses)
                (Zlength (get_receivers region_descriptor))) with 
       | None =>
         do zero_flag_value <- get_zero_flag_value region_descriptor;;;
         do res <- apply_ffa_mem_share_retrieve_req_core_transition_spec
                    caller receiver_id
                    cur_addresses
                    zero_flag_value
                    st ;;;
         match res with  
         (* TODO: need to creage handle! - 0 is the wrong value  *)
         (* TODO: need to reduce mpool size *) 
         | (st', true) =>
           let region_size
               := (FFA_memory_region_struct_size
                     (Zlength
                        (region_descriptor
                         .(FFA_memory_region_struct_composite)
                         .(FFA_composite_memory_region_struct_constituents)))) in                    
           match set_memory_region_in_shared_state
                   caller
                   region_size FFA_MEM_SHARE
                   ((receiver_id, cur_addresses)::nil)
                   None true
                   region_descriptor st' with                    
           | Some (st'', value) =>
             do handle_value <- make_handle caller value;;;
             do res_st <- set_send_handle caller receiver_id
                                         region_size handle_value FFA_MEM_RETREIVE_RESP
                                         st'' ;;;
             Some (res_st, FFA_SUCCESS value)
           | None => Some (st, FFA_ERROR FFA_DENIED)
           end
         | (_, false) => Some (st, FFA_ERROR FFA_DENIED)
         end
       | Some res => Some (st, FFA_ERROR res)
       end
     end. 
    
    Definition ffa_mem_retrieve_req_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (st : AbstractState)
    : option (AbstractState * FFA_RESULT_CODE_TYPE) :=
      if ffa_mem_send_check_arguments total_length fragment_length address count
      then
        do handle <- get_send_handle_value caller st ;;;
        do share_state <- get_handle_information handle st ;;;
        match share_state with 
        | mkFFA_memory_share_state_struct
            memory_region share_func retrieved relinquished retrieve_count
          => match ZTree.get caller retrieved with 
            (** TODO: need to add retrieve_count and relinquished later *)
            | Some is_retrieved =>
              if is_retrieved
              then Some (st, FFA_ERROR FFA_DENIED)
              else match share_func with
                   | FFA_MEM_DONATE
                     => ffa_mem_retrieve_req_donate_spec
                         caller total_length fragment_length address count
                         memory_region st
                   | FFA_MEM_LEND
                     => ffa_mem_retrieve_req_lend_spec
                         caller total_length fragment_length address count
                         memory_region st                       
                   | FFA_MEM_SHARE
                     => ffa_mem_retrieve_req_share_spec
                         caller total_length fragment_length address count
                         memory_region st                                              
                   | _ => Some (st, FFA_ERROR FFA_DENIED)
                   end
            | _ => Some (st, FFA_ERROR FFA_DENIED)
            end
        end
      else Some (st, FFA_ERROR FFA_INVALID_PARAMETERS).
    
  End FFA_MEM_RETRIEVE_REQ_ARGUMENT_CHECKS.

  Section FFA_MEM_RETRIEVE_RESP_ARGUMENT_CHECKS.
    (***********************************************************************)
    (** ***  11.5 FFA_MEM_RETRIEVE_RESP                                    *)
    (***********************************************************************)
    (** 
      - Structure
        - paramemter
          - stored register
          - description 

      - Table 11.22: FFA_MEM_RETRIEVE_RESP function syntax
        - uint32 Function ID
          - w0
          - 0x84000075
        - uint32 Total length
          - w1
          - Total length of the memory transaction descriptor in bytes.
        - uint32 Fragment length 
          - w2
          - Length in bytes of the memory transaction descriptor passed in this ABI invocation.
          - Fragment length must be <= Total length.
          - If Fragment length < Total length then see 12.2.2 Transmission of transaction 
            descriptor in fragments about how the remainder of the descriptor will be
            transmitted.
        - uint32/uint64 Parameter
          - w3
          - Reserved (MBZ)
        - uint32/uint64 Parameter
          - w4
          - Reserved (MBZ)
        - Other Parameter registers 
          - w5-w7
          - Reserved (MBZ)

      - Table 11.23: FFA_ERROR encoding
        - int32 Error code 
          - w2
          - INVALID_PARAMETERS / NO_MEMORY
     *)
    
    Definition ffa_mem_retrieve_resp_spec
               (caller : ffa_UUID_t)               
               (total_length fragment_length : Z)
               (st : AbstractState)
    : option (AbstractState * FFA_RESULT_CODE_TYPE) :=
      None.
    
  End FFA_MEM_RETRIEVE_RESP_ARGUMENT_CHECKS.

  Section FFA_MEM_RELINQUISH_ARGUMENT_CHECKS.
    (***********************************************************************)
    (** ***  11.6 FFA_MEM_RELINQUISH                                       *)
    (***********************************************************************)
    (** 
      - Structure
        - paramemter
          - stored register
          - description 

      - Table 11.27: FFA_MEM_RELINQUISH function syntax
        - uint32 Function ID
          - w0
          - 0x84000076
        - Other Parameter registers
          - w1-w7
          - Reserved (MBZ)

      - Table 11.28: FFA_ERROR encoding
        - int32 Error code 
          - w2
          - INVALID_PARAMETERS / DENIED / NO_MEMORY / ABORTED
     *)

    Definition ffa_mem_relinquish_spec
               (caller : ffa_UUID_t)
               (st : AbstractState)
    : option (AbstractState * FFA_RESULT_CODE_TYPE) :=
      None.
    
  End FFA_MEM_RELINQUISH_ARGUMENT_CHECKS.
    
  Section FFA_MEM_RECLAIM_ARGUMENT_CHECKS.
    (***********************************************************************)
    (** ***  11.7 FFA_MEM_RECLAIM                                          *)
    (***********************************************************************)
    (** 
      - Structure
        - paramemter
          - stored register
          - description 

      - Table 11.31: FFA_MEM_RECLAIM function syntax
        - uint32 Function ID
          - w0
          - 0x84000077
        - uint64 Handle
          - w1/w2
          - Globally unique Handle to identify the memory region (see 5.10.2 Memory region handle).
        - uint32 Flags
          - w3
          - Bit(0): Zero memory before reclaim flag.
            – This flag specifies if the Relayer must clear memory region contents before mapping it in
              the Owner translation regime.
              - b0: Relayer must not zero the memory region contents.
              - b1: Relayer must zero the memory region contents.
            – Relayer must fulfill memory zeroing requirements listed in in 5.12.4 Flags usage.
            – MBZ if the Owner has Read-only access to the memory region, else the Relayer must return DENIED.
          - Bit(1): Operation time slicing flag.
            – This flag specifies if the Relayer can time slice this operation.
              - b0: Relayer must not time slice this operation.
              - b1: Relayer can time slice this operation.
            - MBZ if the Relayer does not support time slicing of memory management operations (see 12.2.3 Time
              slicing of memory management operations) .
          - Bit(31:2): Reserved (MBZ).
        - Other Parameter registers
          - w4-w7
          - Reserved (MBZ)

      - Table 11.32: FFA_ERROR encoding
        - int32 Error code 
          - w2
          - INVALID_PARAMETERS / DENIED / NO_MEMORY / ABORTED
     *)

    Definition ffa_mem_reclaim_spec
               (caller : ffa_UUID_t)
               (handle_high handle_low flags : Z)
               (st : AbstractState)
    : option (AbstractState * FFA_RESULT_CODE_TYPE) :=
      None.
    
  End FFA_MEM_RECLAIM_ARGUMENT_CHECKS.
    
End FFA_MEMORY_INTERFACE_ADDITIONAL_STEPS.

