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
        do local_inst_access <-
            get_instruction_access_from_global_local_pool_props
              vid hd mem_properties.(mem_local_properties) ;;;
        do local_data_access <-
            get_data_access_from_global_local_pool_props
              vid hd mem_properties.(mem_local_properties) ;;;
        do local_attributes <-
            get_attributes_from_global_local_pool_props
              vid hd mem_properties.(mem_local_properties) ;;;
   
        do global_inst_access <-
            get_instruction_access_from_global_props
              vid hd mem_properties.(mem_global_properties) ;;;
        do global_data_access <-
            get_data_access_from_global_props
              vid hd mem_properties.(mem_global_properties) ;;;
        do global_attributes <-
            get_attributes_from_global_props
              vid hd mem_properties.(mem_global_properties) ;;;

        (** - Check descriptor's values are valid with memory properties and accessibilities *)                                                            
        match data_permissions_check_donate_lender_check
                descriptor_data_access global_data_access local_data_access with
        | Some res => Some res
        | None =>
          match
            instruction_permissions_donate_and_lend_single_borrower_lender_descriptor_check
              descriptor_inst_access global_inst_access with
          | Some res => Some res
          | None =>
            match attributes_donate_and_single_borrower_lender_check
                    descriptor_attributes local_attributes
                    global_attributes with
            | Some res => Some res
            | None =>
              match memory_region_descriptor.(FFA_memory_region_struct_flags) with
              | MEMORY_REGION_FLAG_NORMAL flags =>
                match check_FFA_mem_default_flags_struct_for_donate_and_lend
                        flags  local_data_access time_slice_enabled with
                | Some res => Some res
                (** - If there are all valid, check the next address *)
                | None => 
                  donate_checks_per_address
                    vid time_slice_enabled mem_properties
                    memory_region_descriptor tl
                    descriptor_inst_access
                    descriptor_data_access
                    descriptor_attributes
                end
              | _ => Some (FFA_INVALID_PARAMETERS)
              end
            end
          end 
        end
      end.       

    (** There are some redundancies, but we do not care it *)
    (** check additional properties *)
    Definition donate_check
               (vid : ffa_UUID_t)
               (time_slice_enabled: bool)
               (mem_properties: MemProperties)
               (memory_region_descriptor: FFA_memory_region_struct)
               (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z))
      : option (FFA_ERROR_CODE_TYPE) := 
      if decide (memory_region_descriptor.(FFA_memory_region_struct_sender) = vid)
      then
        (** - Check well formed of memory region descriptor *)
        match well_formed_FFA_memory_region_struct
                vid memory_region_descriptor FFA_MEM_DONATE with
        | None =>
          match memory_region_descriptor
                .(FFA_memory_region_struct_flags) with
          | MEMORY_REGION_FLAG_NORMAL flags =>
            (** - Check access and attributes *)
            match info_tuple with
            (** - Donate operation allows only one receiver *)
            | (receiver, receiver_id, addrs)::nil
              =>
              (** - Extract descriptor's access and attribute values *)
              let descriptor_inst_access :=
                  get_instruction_access_information_from_descriptor receiver in
              let descriptor_data_access :=
                  get_data_access_information_from_descriptor receiver in
              let descriptor_attributes :=
                  get_attributes_information_from_descriptor memory_region_descriptor in
              match donate_checks_per_address
                      vid time_slice_enabled
                      mem_properties memory_region_descriptor addrs
                      descriptor_inst_access descriptor_data_access
                      descriptor_attributes with 
              | None =>
                (FFA_memory_access_permissions_descriptor_struct_flags_check
                   FFA_MEM_DONATE
                   (receiver
                    .(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor))
                   (Zlength info_tuple))
              | res => res
              end
            | _ => Some (FFA_INVALID_PARAMETERS)
            end
          | _ => Some (FFA_INVALID_PARAMETERS)
          end
        | res => res
        end
      else Some (FFA_INVALID_PARAMETERS).
    
    (** - Change memory ownership and accessibilities for all addresses. 
          If it encouter errors, it will revert the change and return the original state *)
    Fixpoint apply_ffa_mem_donate_core_transition_spec
             (caller receiver_id : ffa_UUID_t) (addresses : list Z)
             (st : AbstractState) :=
      match addresses with
      | nil => Some (st, true)
      | hd::tl =>
        let st' := apply_ffa_mem_donate_core_transition_spec
                     caller receiver_id tl st in
        match st' with
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
              match (donate_check
                       caller
                       (st.(hypervisor_context).(time_slice_enabled))
                       (st.(hypervisor_context).(mem_properties))
                       memory_region_descriptor receivers_info) with 
              | None =>
                match receivers_info with
                | (receiver, receiver_id, cur_addresses)::nil =>
                  (* TODO: add cases to handle multiple address transfer *)
                  do res <- apply_ffa_mem_donate_core_transition_spec
                             caller receiver_id cur_addresses st ;;;
                  match res with  
                  (* TODO: need to creage handle! - 0 is the wrong value  *)
                  (* TODO: need to reduce mpool size *) 
                  | (st', true) =>
                    match set_memory_region_in_shared_state
                            region_size FFA_MEM_DONATE
                            ((receiver_id, cur_addresses)::nil)
                            memory_region_descriptor st' with
                    | (st'', value) =>
                      do handle_value <- make_handle caller value;;;
                      do res_st <- set_send_handle caller receiver_id
                                                  region_size handle_value FFA_MEM_DONATE
                                                  st'' ;;;
                      Some (res_st, FFA_SUCCESS value)
                    end
                  | (_, false) => Some (st, FFA_ERROR FFA_DENIED)
                  end
                | _ => Some (st, FFA_ERROR FFA_INVALID_PARAMETERS)
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
        do local_inst_access <-
            get_instruction_access_from_global_local_pool_props
              vid hd mem_properties.(mem_local_properties) ;;;
        do local_data_access <-
            get_data_access_from_global_local_pool_props
              vid hd mem_properties.(mem_local_properties) ;;;
        do local_attributes <-
            get_attributes_from_global_local_pool_props
              vid hd mem_properties.(mem_local_properties) ;;;
   
        do global_inst_access <-
            get_instruction_access_from_global_props
              vid hd mem_properties.(mem_global_properties) ;;;
        do global_data_access <-
            get_data_access_from_global_props
              vid hd mem_properties.(mem_global_properties) ;;;
        do global_attributes <-
            get_attributes_from_global_props
              vid hd mem_properties.(mem_global_properties) ;;;
   
        match data_permissions_lend_and_share_lender_check
                descriptor_data_access global_data_access local_data_access with
        | Some res => Some res
        | None =>
          match memory_region_descriptor.(FFA_memory_region_struct_flags) with
          | MEMORY_REGION_FLAG_NORMAL flags =>
            match check_FFA_mem_default_flags_struct_for_donate_and_lend
                    flags local_data_access time_slice_enabled with
            | Some res => Some res
            | None =>
              if (decide (receiver_number = 1))
              then 
                match instruction_permissions_donate_and_lend_single_borrower_lender_descriptor_check
                        descriptor_inst_access global_inst_access with
                | Some res => Some res
                | None =>
                  match attributes_donate_and_single_borrower_lender_check
                          descriptor_attributes local_attributes
                          global_attributes with
                  | Some res => Some res
                  | None =>
                    lend_checks_per_address
                      vid time_slice_enabled mem_properties memory_region_descriptor
                      tl descriptor_inst_access descriptor_data_access descriptor_attributes
                      receiver_number
                  end
                end
              else
                match instruction_permissions_share_and_lend_multiple_borrower_lender_check
                        descriptor_inst_access global_inst_access with
                | Some res => Some res
                | None =>
                  match attributes_share_and_multiple_borrowers_borrower_check
                          descriptor_attributes global_attributes with
                  | Some res => Some res
                  | None =>
                    lend_checks_per_address
                      vid time_slice_enabled mem_properties memory_region_descriptor
                      tl descriptor_inst_access descriptor_data_access descriptor_attributes
                      receiver_number
                  end
                end
            end
          | _ => Some (FFA_INVALID_PARAMETERS)
          end
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
        match lend_check_iterations vid time_slice_enabled mem_properties memory_region_descriptor
                                    tl receiver_number with
        | None =>
          (** - Extract descriptor's access and attribute values *)
          let descriptor_inst_access :=
              get_instruction_access_information_from_descriptor receiver in
          let descriptor_data_access :=
              get_data_access_information_from_descriptor receiver in
          let descriptor_attributes :=
              get_attributes_information_from_descriptor memory_region_descriptor in
          match lend_checks_per_address
                  vid time_slice_enabled
                  mem_properties memory_region_descriptor addrs
                  descriptor_inst_access descriptor_data_access
                  descriptor_attributes receiver_number with 
          | None =>
            (FFA_memory_access_permissions_descriptor_struct_flags_check
               FFA_MEM_LEND
               (receiver
                .(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor))
               (Zlength info_tuple))
          | res => res
          end
        | res => res
        end
      end.
    
    Definition lend_check
               (vid : ffa_UUID_t)
               (time_slice_enabled: bool)
               (mem_properties: MemProperties)
               (memory_region_descriptor: FFA_memory_region_struct)
               (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z))
      : option (FFA_ERROR_CODE_TYPE) := 
      if decide (memory_region_descriptor.(FFA_memory_region_struct_sender) = vid)
      then
        (** - Check well formed of memory region descriptor *)
        match well_formed_FFA_memory_region_struct
                vid memory_region_descriptor FFA_MEM_DONATE with
        | None =>
          match memory_region_descriptor
                .(FFA_memory_region_struct_flags) with
          | MEMORY_REGION_FLAG_NORMAL flags =>
            (** - Check access and attributes *)
            match info_tuple with
            | nil => Some (FFA_INVALID_PARAMETERS)
            | _ => lend_check_iterations vid time_slice_enabled
                                        mem_properties memory_region_descriptor
                                        info_tuple (Zlength info_tuple)
            end
          | _ => Some (FFA_INVALID_PARAMETERS)
          end
        | res => res
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
        let st' := apply_ffa_mem_lend_core_transition_spec
                     caller receivers tl st in
        match st' with
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
                          region_size FFA_MEM_DONATE
                          (get_receiver_id_addrs_pair receivers_info)
                          memory_region_descriptor st' with
                  | (st'', value) =>
                    do handle_value <- make_handle caller value;;;                    
                    do res_st <- set_send_handle_for_multiple_receivers
                                  (get_receiver_ids receivers_info)
                                  caller
                                  region_size handle_value FFA_MEM_LEND
                                  st'' ;;;
                    Some (res_st, FFA_SUCCESS value)
                  end
                | _ => Some (st, FFA_ERROR FFA_INVALID_PARAMETERS)
                end
              | _ => Some (st, FFA_ERROR FFA_INVALID_PARAMETERS)
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
        do local_inst_access <-
            get_instruction_access_from_global_local_pool_props
              vid hd mem_properties.(mem_local_properties) ;;;
        do local_data_access <-
            get_data_access_from_global_local_pool_props
              vid hd mem_properties.(mem_local_properties) ;;;
        do local_attributes <-
            get_attributes_from_global_local_pool_props
              vid hd mem_properties.(mem_local_properties) ;;;
   
        do global_inst_access <-
            get_instruction_access_from_global_props
              vid hd mem_properties.(mem_global_properties) ;;;
        do global_data_access <-
            get_data_access_from_global_props
              vid hd mem_properties.(mem_global_properties) ;;;
        do global_attributes <-
            get_attributes_from_global_props
              vid hd mem_properties.(mem_global_properties) ;;;
   
        match data_permissions_lend_and_share_lender_check
                descriptor_data_access global_data_access local_data_access with
        | Some res => Some res
        | None =>
          match memory_region_descriptor.(FFA_memory_region_struct_flags) with
          | MEMORY_REGION_FLAG_NORMAL flags =>
            match check_FFA_mem_default_flags_struct_for_share
                    flags time_slice_enabled with
            | Some res => Some res
            | None =>
              match instruction_permissions_share_and_lend_multiple_borrower_lender_check
                      descriptor_inst_access global_inst_access with
              | Some res => Some res
              | None =>
                match attributes_share_and_multiple_borrowers_borrower_check
                        descriptor_attributes global_attributes with
                | Some res => Some res
                | None =>
                  lend_checks_per_address
                    vid time_slice_enabled mem_properties memory_region_descriptor
                    tl descriptor_inst_access descriptor_data_access descriptor_attributes
                    receiver_number
                end
              end
            end
          | _ => Some (FFA_INVALID_PARAMETERS)
          end
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
        match share_check_iterations vid time_slice_enabled mem_properties memory_region_descriptor
                                     tl receiver_number with
        | None =>
          (** - Extract descriptor's access and attribute values *)
          let descriptor_inst_access :=
              get_instruction_access_information_from_descriptor receiver in
          let descriptor_data_access :=
              get_data_access_information_from_descriptor receiver in
          let descriptor_attributes :=
              get_attributes_information_from_descriptor memory_region_descriptor in
          match share_checks_per_address
                  vid time_slice_enabled
                  mem_properties memory_region_descriptor addrs
                  descriptor_inst_access descriptor_data_access
                  descriptor_attributes receiver_number with 
          | None =>
            (FFA_memory_access_permissions_descriptor_struct_flags_check
               FFA_MEM_SHARE
               (receiver
                .(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor))
               (Zlength info_tuple))
          | res => res
          end
        | res => res
        end
      end.
    
    Definition share_check
               (vid : ffa_UUID_t)
               (time_slice_enabled: bool)
               (mem_properties: MemProperties)
               (memory_region_descriptor: FFA_memory_region_struct)
               (info_tuple : list (FFA_endpoint_memory_access_descriptor_struct * ffa_UUID_t * list Z))
      : option (FFA_ERROR_CODE_TYPE) := 
      if decide (memory_region_descriptor.(FFA_memory_region_struct_sender) = vid)
      then
        (** - Check well formed of memory region descriptor *)
        match well_formed_FFA_memory_region_struct
                vid memory_region_descriptor FFA_MEM_DONATE with
        | None =>
          match memory_region_descriptor
                .(FFA_memory_region_struct_flags) with
          | MEMORY_REGION_FLAG_NORMAL flags =>
            (** - Check access and attributes *)
            match info_tuple with
            | nil => Some (FFA_INVALID_PARAMETERS)
            | _ => share_check_iterations vid time_slice_enabled
                                         mem_properties memory_region_descriptor
                                         info_tuple (Zlength info_tuple)
            end
          | _ => Some (FFA_INVALID_PARAMETERS)
          end
        | res => res
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
        let st' := apply_ffa_mem_share_core_transition_spec
                     caller receivers tl st in
        match st' with
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
                          region_size FFA_MEM_DONATE
                          (get_receiver_id_addrs_pair receivers_info)
                          memory_region_descriptor st' with
                  | (st'', value) =>
                    do handle_value <- make_handle caller value;;;                    
                    do res_st <- set_send_handle_for_multiple_receivers
                                  (get_receiver_ids receivers_info)
                                  caller
                                  region_size handle_value FFA_MEM_SHARE
                                  st'' ;;;
                    Some (res_st, FFA_SUCCESS value)
                  end
                | _ => Some (st, FFA_ERROR FFA_INVALID_PARAMETERS)
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

    Definition ffa_mem_retrieve_req_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (st : AbstractState)
    : option (AbstractState * FFA_RESULT_CODE_TYPE) :=
      None.
    
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

