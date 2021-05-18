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

(* begin hide *)

Notation "'get' T ',' E ',' X <- A ';;;' B" :=
  (match A with Some X => B |
           None => @FAIL T E end)
    (at level 200, X ident, A at level 100, B at level 200)
  : ffa_monad_scope.

Notation "'get_r' T ',' X <- A ';;;' B" :=
  (match A with SUCCESS X => B |
           FAIL E => @FAIL T E end)
    (at level 200, X ident, A at level 100, B at level 200)
  : ffa_monad_scope.

Notation " 'check' T ',' E ',' A ';;;' B" :=
  (if A then B else @FAIL T E)
    (at level 200, A at level 100, B at level 200) : ffa_monad_scope.

Local Open Scope ffa_monad_scope.

(* end hide *)

(***********************************************************************)
(** *  Additional Step Rules for Memory Management                     *)
(***********************************************************************)

Section FFA_MEMORY_INTERFACE_ADDITIONAL_STEPS.

  Context `{abstract_state_context: AbstractStateContext}.

  (***********************************************************************)
  (** **  FFA_MEM_DONATE, FFA_MEM_LEND, and FFA_MEM_SHARE                *)
  (***********************************************************************)
  (** This section is related to three sections in the FF-A document, 
      11.1 FFA_MEM_DONATE, 11.2 FFA_MEM_LEND, and 11.3 FFA_MEM_SHARE    
  *)
  
  (**  The followings describe how those three hypervisor calls use 
       registers 

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

  (***********************************************************************)
  (** ***             FFA_MEM_DONATE                                     *)
  (***********************************************************************)  
  Section FFA_MEM_DONATE_ADDITIONAL_STEPS.

    (** - Check each page in constituents to see whether 
          all values in the descriptor are valid for the donate operation,
          and return a proper error message when it cannot proceed evaluations.
     *)
    Fixpoint donate_checks_per_page
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (pages: list Z)
             (descriptor_inst_access: FFA_INSTRUCTION_ACCESS_TYPE)
             (descriptor_data_access: FFA_DATA_ACCESS_TYPE)
             (descriptor_attributes: FFA_MEMORY_TYPE)
    : option (FFA_ERROR_CODE_TYPE) :=
      (** - Check for all pages *)
      match pages with
      | nil => None
      | hd::tl =>
        (** - Exctract properties and accessibilities for the page *)
        match get_permissions_and_attributes vid hd mem_properties,
              memory_region_descriptor.(FFA_memory_region_struct_flags)with
        | SUCCESS (local_inst_access, local_data_access, local_attributes,
                global_inst_access, global_data_access,  global_attributes),
          MEMORY_REGION_FLAG_NORMAL flags =>
          (** - Check descriptor's values are valid with page properties and accessibilities *)
          match data_permissions_check_donate_lender_check
                  descriptor_data_access global_data_access local_data_access,
                instruction_permissions_donate_and_lend_single_borrower_lender_descriptor_check
                  descriptor_inst_access global_inst_access,
                attributes_donate_and_single_borrower_lender_check
                  descriptor_attributes local_attributes global_attributes,
                check_FFA_mem_default_flags_struct_for_donate_and_lend
                  flags local_data_access time_slice_enabled with 
          | Some res, _, _, _ 
          | None, Some res, _, _
          | None, None, Some res, _
          | None, None, None, Some res => Some res
          | None, None, None, None =>
            (** - If there are all valid, check the next page in the descriptor *)
            donate_checks_per_page
              vid time_slice_enabled mem_properties
              memory_region_descriptor tl
              descriptor_inst_access
              descriptor_data_access
              descriptor_attributes
          end
        | SUCCESS _, _ => Some (FFA_INVALID_PARAMETERS
                        (append_all ["donate_checks_per_page with ";
                                    HexString.of_Z hd; " due to invalid flag"]))
        | FAIL msg, _ =>  Some (FFA_INVALID_PARAMETERS
                        (append_all ["donate_checks_per_page with ";
                                    HexString.of_Z hd; " due to "; msg]))
        end
      end.

    (** Check memory region descriptor, attributes, and accessibilities to see
        whether all values are valid for the donate operation.
        - Check well-formedness of the memory region descriptor 
        - Check values for each page by calling donate_checks_per_page *)
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
      | left _, MEMORY_REGION_FLAG_NORMAL flags,  (receiver, receiver_id, pages)::nil =>
        (** - Check well formed of memory region descriptor *)
        let descriptor_inst_access :=
            get_instruction_access_information_from_descriptor receiver in
        let descriptor_data_access :=
            get_data_access_information_from_descriptor receiver in
        let descriptor_attributes :=
            get_attributes_information_from_descriptor memory_region_descriptor in
        match well_formed_FFA_memory_region_struct
                vid memory_region_descriptor FFA_MEM_DONATE,
              donate_checks_per_page
                vid time_slice_enabled
                mem_properties memory_region_descriptor pages
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
      | _, _, _ => Some (FFA_INVALID_PARAMETERS "donate_check")
      end.
    
    (** - Change memory ownership and accessibilities for all pages. 
          If it encouter errors, it will revert the change and return the original state *)
    Fixpoint apply_ffa_mem_donate_core_transition_spec
             (caller receiver_id : ffa_UUID_t) (page_numbers : list Z)
             (st : AbstractState) : RESULT (AbstractState * bool) :=
      match page_numbers with
      | nil => SUCCESS (st, true)
      | hd::tl =>
        match apply_ffa_mem_donate_core_transition_spec
                caller receiver_id tl st with
        | SUCCESS st'' =>
          ffa_mem_donate_core_transition_spec
            caller receiver_id hd (fst st'') 
        | FAIL msg => FAIL msg
        end
      end.

    Definition ffa_mem_donate_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (st: AbstractState)
      : RESULT (AbstractState * FFA_RESULT_CODE_TYPE) :=
      (** - Check the arguments *)
      if ffa_mem_general_check_arguments total_length fragment_length address count
      then
        (** - Get the current memory region descriptor *)
        get_r (AbstractState * FFA_RESULT_CODE_TYPE),
        state_and_memory_region_descriptor
        <- (get_send_memory_region_descriptor caller st)
            ;;;
            let (state, memory_region_descriptor)
                := state_and_memory_region_descriptor in
            (** - Extract information from the descriptor  *) 
            get_r (AbstractState *FFA_RESULT_CODE_TYPE),
            ipa_info_tuple <-
            (get_recievers_receiver_ids_and_addresses_tuple
               memory_region_descriptor)
              ;;; get_r (AbstractState * FFA_RESULT_CODE_TYPE),
              pa_info_tuple
              <- (SubstIPAsIntoPAs ipa_info_tuple)
                  ;;; let info_tuple
                          := convert_addresses_in_info_tuple_to_page_numbers              
                               pa_info_tuple in
                      (** - Check the well_formed conditions of the memory region descriptor *)
                      if decide ((length (get_receivers memory_region_descriptor) = 1)%nat)
                      then
                        let region_size
                            := (FFA_memory_region_struct_size
                                  (Zlength
                                     (memory_region_descriptor
                                      .(FFA_memory_region_struct_composite)
                                      .(FFA_composite_memory_region_struct_constituents)))) in
                        if decide ((region_size < state.(hypervisor_context).(api_page_pool_size))%Z)
                        then
                          match info_tuple with
                          | (receiver, receiver_id, cur_addresses)::nil =>
                            (* TODO: add cases to handle multiple address transfer *)
                            match (donate_check
                                     caller
                                     (state.(hypervisor_context).(time_slice_enabled))
                                     (state.(hypervisor_context).(mem_properties))
                                     memory_region_descriptor info_tuple) with 
                            | None =>
                              get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                              res
                              <- (apply_ffa_mem_donate_core_transition_spec
                                   caller receiver_id cur_addresses state)
                                  ;;;
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
                                    | SUCCESS (st'', handle_value) =>
                                      get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                                      res_st
                                      <- (set_send_handle caller receiver_id
                                                         region_size handle_value FFA_MEM_DONATE
                                                         st'')
                                          ;;;
                                          SUCCESS (res_st, FFA_SUCCESS handle_value)
                                    | FAIL msg => SUCCESS (st, FFA_ERROR
                                                                (FFA_DENIED
                                                                   ("ffa_mem_general_check_arguments: "
                                                                      ++ msg)))
                                    end
                                  | (_, false) =>
                                    SUCCESS (st, FFA_ERROR
                                                (FFA_DENIED
                                                   "apply_ffa_mem_donate_core_transition_spec"))
                                  end
                            | Some res => SUCCESS (st, FFA_ERROR res)
                            end
                          | _ => SUCCESS (st, FFA_ERROR
                                            (FFA_INVALID_PARAMETERS
                                               "info_tuple invalid"))
                          end
                        else SUCCESS (st, FFA_ERROR
                                         (FFA_NO_MEMORY
                                            "mpool size is too small"))
                      else SUCCESS (st, FFA_ERROR
                                       (FFA_DENIED
                                          "wrong receiver number"))
      else SUCCESS (st, FFA_ERROR
                          (FFA_INVALID_PARAMETERS
                             "ffa_mem_general_check_arguments")).
    
  End FFA_MEM_DONATE_ADDITIONAL_STEPS.

  (***********************************************************************)
  (** ***             FFA_LEND_DONATE                                    *)
  (***********************************************************************)    
  Section FFA_MEM_LEND_ADDITIONAL_STEPS.

    (** - Check each page in constituents to see whether 
          all values in the descriptor are valid for the lend operation,
          and return a proper error message when it cannot proceed evaluations.
     *)    
    Fixpoint lend_checks_per_page
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (pages: list Z)
             (descriptor_inst_access: FFA_INSTRUCTION_ACCESS_TYPE)
             (descriptor_data_access: FFA_DATA_ACCESS_TYPE)
             (descriptor_attributes: FFA_MEMORY_TYPE)
             (receiver_number : Z)             
      : option (FFA_ERROR_CODE_TYPE) :=
      match pages with
      | nil => None
      | hd::tl =>
        (** - Check properties that are not relevant to the number of receivers *)
        match get_permissions_and_attributes vid hd mem_properties,
              memory_region_descriptor.(FFA_memory_region_struct_flags) with        
        | SUCCESS (local_inst_access, local_data_access, local_attributes,
                global_inst_access, global_data_access,  global_attributes),
          MEMORY_REGION_FLAG_NORMAL flags =>
          match data_permissions_lend_and_share_lender_check
                  descriptor_data_access global_data_access local_data_access,
                check_FFA_mem_default_flags_struct_for_donate_and_lend
                  flags local_data_access time_slice_enabled with
          | Some res, _ 
          | None, Some res => Some res
          | None, None =>
            (** - Check number of receivers *)            
            if (decide (receiver_number = 1))
            then 
              (** - Check for the lend operation with the single receiver *)
              match instruction_permissions_donate_and_lend_single_borrower_lender_descriptor_check
                      descriptor_inst_access global_inst_access,
                    attributes_donate_and_single_borrower_lender_check
                      descriptor_attributes local_attributes global_attributes with
              | Some res, _
              | None, Some res => Some res
              | None, None =>
                (** - If there are all valid, check the next page in the descriptor *)
                lend_checks_per_page
                  vid time_slice_enabled mem_properties memory_region_descriptor
                  tl descriptor_inst_access descriptor_data_access descriptor_attributes
                  receiver_number
              end
            else
              (** - Check for the lend operation with multiple receivers *)
              match instruction_permissions_share_and_lend_multiple_borrower_lender_check
                      descriptor_inst_access global_inst_access,
                    attributes_share_and_multiple_borrowers_borrower_check
                      descriptor_attributes global_attributes with
              | Some res, _
              | None, Some res => Some res
              | None, None =>
                (** - If there are all valid, check the next page in the descriptor *)                
                lend_checks_per_page
                  vid time_slice_enabled mem_properties memory_region_descriptor
                  tl descriptor_inst_access descriptor_data_access descriptor_attributes
                  receiver_number
              end
          end
        | SUCCESS _, _ => Some (FFA_INVALID_PARAMETERS
                                 (append_all ["lend_checks_per_page with ";
                                             HexString.of_Z hd; " due to invalid flag"]))
        | FAIL msg, _ =>  Some (FFA_INVALID_PARAMETERS
                                 (append_all ["lend_checks_per_page with ";
                                             HexString.of_Z hd; " due to "; msg]))
        end
      end.

    (** Check memory region descriptor, attributes, and accessibilities to see
        whether all values are valid for the lend operation.
        - Check well-formedness of the memory region descriptor 
        - Check values for each page by calling lend_checks_per_page *)
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
      | (receiver, receiver_id, pages)::tl =>
        (** - Check well formed of memory region descriptor *)
        let descriptor_inst_access :=
            get_instruction_access_information_from_descriptor receiver in
        let descriptor_data_access :=
            get_data_access_information_from_descriptor receiver in
        let descriptor_attributes :=
            get_attributes_information_from_descriptor memory_region_descriptor in
        match lend_check_iterations vid time_slice_enabled mem_properties
                                    memory_region_descriptor tl receiver_number,
              lend_checks_per_page vid time_slice_enabled
                                   mem_properties memory_region_descriptor pages
                                   descriptor_inst_access descriptor_data_access
                                   descriptor_attributes receiver_number with
        | Some res, _
        | None, Some res => Some res
        | None, None =>
          (** - Check access and attributes *)
          (** - Extract descriptor's access and attribute values *)          
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
                vid memory_region_descriptor FFA_MEM_LEND with
        | None =>
          lend_check_iterations vid time_slice_enabled
                                mem_properties memory_region_descriptor
                                info_tuple (Zlength info_tuple)
        | Some res => Some res
        end
      else Some (FFA_INVALID_PARAMETERS
                   "lend_check").
    
    (** - Change memory ownership and accessibilities for all addresses. 
          If it encouter errors, it will revert the change and return the original state *)
    Fixpoint apply_ffa_mem_lend_core_transition_spec
             (caller : ffa_UUID_t) (receivers: list ffa_UUID_t) (pages : list Z)
             (st : AbstractState) :=
      match pages with
      | nil => SUCCESS (st, true)
      | hd::tl =>
        match apply_ffa_mem_lend_core_transition_spec
                caller receivers tl st with
        | SUCCESS st'' =>
          ffa_mem_lend_core_transition_spec
            caller receivers hd (fst st'') 
        | FAIL msg => FAIL msg
        end
      end.
    
    Definition ffa_mem_lend_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (st: AbstractState)
      : RESULT (AbstractState * FFA_RESULT_CODE_TYPE) :=
      (** - Check the arguments *)
      if ffa_mem_general_check_arguments total_length fragment_length address count
      then
        (** - Get the current memory region descriptor *)
        get_r (AbstractState * FFA_RESULT_CODE_TYPE),
        state_and_memory_region_descriptor
        <- (get_send_memory_region_descriptor caller st)
            ;;; let (state, memory_region_descriptor) := state_and_memory_region_descriptor in
                get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                ipa_info_tuple
                <- (get_recievers_receiver_ids_and_addresses_tuple
                     memory_region_descriptor)
                    ;;; get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                pa_info_tuple
                <- (SubstIPAsIntoPAs ipa_info_tuple)
                    ;;;
                    let info_tuple := convert_addresses_in_info_tuple_to_page_numbers              
                                        pa_info_tuple in
                    (** - Check the well_formed conditions of the memory region descriptor *)
                    if decide ((length (get_receivers memory_region_descriptor) = 1)%nat)
                    then
                      let region_size
                          := (FFA_memory_region_struct_size
                                (Zlength
                                   (memory_region_descriptor
                                    .(FFA_memory_region_struct_composite)
                                    .(FFA_composite_memory_region_struct_constituents)))) in
                      if decide ((region_size <
                                  state.(hypervisor_context).(api_page_pool_size))%Z)
                      then
                        match (lend_check
                                 caller
                                 (state.(hypervisor_context).(time_slice_enabled))
                                 (state.(hypervisor_context).(mem_properties))
                                 memory_region_descriptor info_tuple) with 
                        | None =>
                          (* TODO: add cases to handle multiple address transfer *)
                          get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                          res
                          <- (apply_ffa_mem_lend_core_transition_spec
                               caller (get_receiver_ids info_tuple)
                               (get_all_addresses memory_region_descriptor)
                               state)
                              ;;; match res with  
                                  (* TODO: need to creage handle! - 0 is the wrong value  *)
                                  (* TODO: need to reduce mpool size *) 
                                  | (st', true) =>
                                    match set_memory_region_in_shared_state
                                            caller
                                            region_size FFA_MEM_LEND
                                            (get_receiver_id_addrs_pair info_tuple)
                                            None false
                                            memory_region_descriptor st' with
                                    | SUCCESS (st'', handle_value) =>
                                      get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                                      res_st
                                      <- (set_send_handle_for_multiple_receivers
                                           (get_receiver_ids info_tuple)
                                           caller
                                           region_size handle_value FFA_MEM_LEND
                                           st'')
                                          ;;;
                                          SUCCESS (res_st, FFA_SUCCESS handle_value)
                                    | FAIL msg => SUCCESS (st,
                                                   FFA_ERROR
                                                     (FFA_DENIED
                                                        ("set_memory_region_in_shared_state"
                                                           ++ msg)))
                                    end
                                  | (_, false) =>
                                    SUCCESS (st, FFA_ERROR
                                                   (FFA_DENIED
                                                      "apply_ffa_mem_lend_core_transition_spec"))
                                  end
                        | Some res => SUCCESS (st, FFA_ERROR res)
                        end
                      else SUCCESS (st, FFA_ERROR
                                          (FFA_NO_MEMORY
                                             "mpool size is too small"))
                    else SUCCESS (st, FFA_ERROR
                                        (FFA_DENIED
                                           "wrong receiver number"))
      else SUCCESS (st, FFA_ERROR
                          (FFA_INVALID_PARAMETERS
                             "ffa_mem_general_check_arguments")).
    
  End FFA_MEM_LEND_ADDITIONAL_STEPS.

  (***********************************************************************)
  (** ***             FFA_SHARE_DONATE                                   *)
  (***********************************************************************)      
  Section FFA_MEM_SHARE_ADDITIONAL_STEPS.
    
    Fixpoint share_checks_per_page
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (pages: list Z)
             (descriptor_inst_access: FFA_INSTRUCTION_ACCESS_TYPE)
             (descriptor_data_access: FFA_DATA_ACCESS_TYPE)
             (descriptor_attributes: FFA_MEMORY_TYPE)
             (receiver_number : Z)             
      : option (FFA_ERROR_CODE_TYPE) :=
      match pages with
      | nil => None
      | hd::tl =>
        match get_permissions_and_attributes vid hd mem_properties,
              memory_region_descriptor.(FFA_memory_region_struct_flags)with
        | SUCCESS (local_inst_access, local_data_access, local_attributes,
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
            share_checks_per_page
              vid time_slice_enabled mem_properties memory_region_descriptor
              tl descriptor_inst_access descriptor_data_access descriptor_attributes
              receiver_number
          end
        | SUCCESS _, _ => Some (FFA_INVALID_PARAMETERS
                                 (append_all ["share_checks_per_page with ";
                                             HexString.of_Z hd; " due to invalid flag"]))
        | FAIL msg, _ =>  Some (FFA_INVALID_PARAMETERS
                                 (append_all ["share_checks_per_page with ";
                                             HexString.of_Z hd; " due to "; msg]))

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
      | (receiver, receiver_id, pages)::tl =>
        (** - Extract descriptor's access and attribute values *)
        let descriptor_inst_access :=
            get_instruction_access_information_from_descriptor receiver in
        let descriptor_data_access :=
            get_data_access_information_from_descriptor receiver in
        let descriptor_attributes :=
            get_attributes_information_from_descriptor memory_region_descriptor in
        match share_check_iterations
                vid time_slice_enabled mem_properties
                memory_region_descriptor
                tl receiver_number,
              share_checks_per_page
                vid time_slice_enabled
                mem_properties memory_region_descriptor pages
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
          | _ => Some (FFA_INVALID_PARAMETERS "share_check")
          end
        | Some res => Some res
        end
      else Some (FFA_INVALID_PARAMETERS "share_check").

    (** - Change memory ownership and accessibilities for all addresses. 
          If it encouter errors, it will revert the change and return the original state *)
    Fixpoint apply_ffa_mem_share_core_transition_spec
             (caller : ffa_UUID_t) (receivers: list ffa_UUID_t) (pages : list Z)
             (st : AbstractState) :=
      match pages with
      | nil => SUCCESS (st, true)
      | hd::tl =>
        match apply_ffa_mem_share_core_transition_spec
                caller receivers tl st with
        | SUCCESS st'' =>
          ffa_mem_share_core_transition_spec
            caller receivers hd (fst st'') 
        | FAIL msg => FAIL msg
        end
      end.
   
    Definition ffa_mem_share_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (st: AbstractState)
      : RESULT (AbstractState * FFA_RESULT_CODE_TYPE) :=
      (** - Check the arguments *)
      if ffa_mem_general_check_arguments total_length fragment_length address count
      then
        (** - Get the current memory region descriptor *)
        get_r (AbstractState * FFA_RESULT_CODE_TYPE),
        state_and_memory_region_descriptor
        <- (get_send_memory_region_descriptor caller st)
            ;;; let '(state, memory_region_descriptor) := state_and_memory_region_descriptor in
                get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                ipa_info_tuple
                <- (get_recievers_receiver_ids_and_addresses_tuple
                     memory_region_descriptor)
                    ;;; get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                pa_info_tuple
                <- (SubstIPAsIntoPAs ipa_info_tuple)
                    ;;;
                    let info_tuple := convert_addresses_in_info_tuple_to_page_numbers              
                                        pa_info_tuple in
                    (** - Check the well_formed conditions of the memory region descriptor *)
                    if decide ((length (get_receivers memory_region_descriptor) = 1)%nat)
                    then
                      let region_size
                          := (FFA_memory_region_struct_size
                                (Zlength
                                   (memory_region_descriptor
                                    .(FFA_memory_region_struct_composite)
                                    .(FFA_composite_memory_region_struct_constituents)))) in
                      if decide ((region_size <
                                  state.(hypervisor_context).(api_page_pool_size))%Z)
                      then
                        match (share_check
                                 caller
                                 (state.(hypervisor_context).(time_slice_enabled))
                                 (state.(hypervisor_context).(mem_properties))
                                 memory_region_descriptor info_tuple) with 
                        | None =>
                          (* TODO: add cases to handle multiple address transfer *)
                          get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                          res
                          <- (apply_ffa_mem_share_core_transition_spec
                               caller (get_receiver_ids info_tuple)
                               (get_all_addresses memory_region_descriptor)
                               state)
                              ;;; match res with  
                                  (* TODO: need to creage handle! - 0 is the wrong value  *)
                                  (* TODO: need to reduce mpool size *) 
                                  | (st', true) =>
                                    match set_memory_region_in_shared_state
                                            caller
                                            region_size FFA_MEM_SHARE
                                            (get_receiver_id_addrs_pair info_tuple)
                                            None false
                                            memory_region_descriptor st' with
                                    | SUCCESS (st'', handle_value) =>
                                      get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                                      res_st
                                      <- (set_send_handle_for_multiple_receivers
                                           (get_receiver_ids info_tuple)
                                           caller
                                           region_size handle_value FFA_MEM_SHARE
                                           st'')
                                          ;;;
                                          SUCCESS (res_st, FFA_SUCCESS handle_value)
                                    | FAIL msg => SUCCESS (st, FFA_ERROR
                                                                (FFA_DENIED
                                                                   ("set_memory_region_in_shared_state: "
                                                                      ++ msg)))
                                    end
                                  | (_, false) =>
                                    SUCCESS (st, FFA_ERROR
                                                   (FFA_DENIED
                                                      "apply_ffa_mem_share_core_transition_spec"))
                                  end
                        | _ => SUCCESS (st, FFA_ERROR
                                             (FFA_INVALID_PARAMETERS
                                                "share_check"))
                        end
                      else SUCCESS (st, FFA_ERROR
                                          (FFA_NO_MEMORY
                                             "not enough mpool size"))
                    else SUCCESS (st, FFA_ERROR
                                        (FFA_DENIED
                                           "invalid number of receivers"))
      else
        SUCCESS (st, FFA_ERROR
                       (FFA_INVALID_PARAMETERS
                          "ffa_mem_general_check_arguments")).
    
  End FFA_MEM_SHARE_ADDITIONAL_STEPS.

  (***********************************************************************)
  (** **   11.4 FFA_MEM_RETRIEVE_REQ                                     *)
  (***********************************************************************)  
  Section FFA_MEM_RETRIEVE_REQ_ARGUMENT_CHECKS.
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
      
    (***********************************************************************)
    (** ***      FFA_MEM_RETRIEVE_REQ - DONATE                             *)
    (***********************************************************************)  
    Fixpoint donate_retrieve_req_checks_per_page
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (pages: list Z)
             (descriptor_inst_access: FFA_INSTRUCTION_ACCESS_TYPE)
             (descriptor_data_access: FFA_DATA_ACCESS_TYPE)
             (descriptor_attributes: FFA_MEMORY_TYPE)
      : option (FFA_ERROR_CODE_TYPE) :=
      match pages with
      | nil => None
      | hd::tl =>
        (** - Exctract memory properties and accessibilities *)
        match get_permissions_and_attributes vid hd mem_properties,
              memory_region_descriptor.(FFA_memory_region_struct_flags) with
        | SUCCESS (local_inst_access, local_data_access, local_attributes,
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
            donate_retrieve_req_checks_per_page
              vid time_slice_enabled mem_properties
              memory_region_descriptor tl
              descriptor_inst_access
              descriptor_data_access
              descriptor_attributes
          end
        | SUCCESS _, _ => Some (FFA_INVALID_PARAMETERS
                                 (append_all ["donate_retrieve_req_checks_per_page with";
                                             HexString.of_Z hd; " due to invalid flag"]))
        | FAIL msg, _ =>  Some (FFA_INVALID_PARAMETERS
                                 (append_all ["donate_retrieve_req_checks_per_page with ";
                                             HexString.of_Z hd; " due to "; msg]))
                      
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
      | left _, MEMORY_REGION_FLAG_NORMAL flags,  (receiver, receiver_id, pages) =>
        (** - Check well formed of memory region descriptor *)
        let descriptor_inst_access :=
            get_instruction_access_information_from_descriptor receiver in
        let descriptor_data_access :=
            get_data_access_information_from_descriptor receiver in
        let descriptor_attributes :=
            get_attributes_information_from_descriptor memory_region_descriptor in
        
        match donate_retrieve_req_checks_per_page
                vid time_slice_enabled
                mem_properties memory_region_descriptor pages
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
      | _, _, _ =>
        Some (FFA_INVALID_PARAMETERS
                "donate_retrieve_req_check")
      end.

    (** - Change memory ownership and accessibilities for all addresses. 
          If it encouter errors, it will revert the change and return the original state *)
    Fixpoint apply_ffa_mem_donate_retrieve_req_core_transition_spec
             (lender borrower : ffa_UUID_t) (pages : list Z) (clean : bool)
             (st : AbstractState) :=
      match pages with
      | nil => SUCCESS (st, true)
      | hd::tl =>
        match apply_ffa_mem_donate_retrieve_req_core_transition_spec
                lender borrower tl clean st with
        | SUCCESS st' =>
          ffa_mem_donate_retrieve_req_core_transition_spec
            lender borrower hd clean (fst st')
        | FAIL msg => FAIL msg
        end
      end.
    
    Definition ffa_mem_retrieve_req_donate_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (region_descriptor : FFA_memory_region_struct)
               (st : AbstractState)
      : RESULT (AbstractState * FFA_RESULT_CODE_TYPE) :=
        (** - Get the current memory region descriptor *)
      get_r (AbstractState * FFA_RESULT_CODE_TYPE),
      ipa_info_tuple
      <- (get_recievers_receiver_ids_and_addresses_tuple
           region_descriptor)
          ;;; get_r (AbstractState * FFA_RESULT_CODE_TYPE),
      pa_info_tuple
      <- (SubstIPAsIntoPAs ipa_info_tuple)
          ;;; let info_tuple := convert_addresses_in_info_tuple_to_page_numbers              
                                  pa_info_tuple in
              (** - Check the well_formed conditions of the memory region descriptor *)
              if decide ((length (get_receivers region_descriptor) = 1)%nat)
              then
                match info_tuple with
                | (receiver, receiver_id, cur_addresses)::nil =>
                  (* TODO: add cases to handle multiple address transfer *)
                  match (donate_retrieve_req_check
                           caller
                           (st.(hypervisor_context).(time_slice_enabled))
                           (st.(hypervisor_context).(mem_properties))
                           region_descriptor
                           (get_receiver_ids info_tuple)
                           (receiver, receiver_id, cur_addresses)
                           (Zlength (get_receivers region_descriptor))) with 
                  | None =>
                    get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                    res
                    <- (apply_ffa_mem_donate_core_transition_spec
                         caller receiver_id cur_addresses st)
                        ;;;
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
                          | SUCCESS (st'', value) =>
                            get (AbstractState * FFA_RESULT_CODE_TYPE),
                            "fail to make handle",
                            handle_value
                            <- (make_handle caller value)
                                ;;; get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                            res_st
                            <- (set_send_handle caller receiver_id
                                               region_size handle_value FFA_MEM_RETREIVE_RESP
                                               st'')
                                ;;; SUCCESS (res_st, FFA_SUCCESS value)
                          | FAIL msg => SUCCESS (st, FFA_ERROR
                                                      (FFA_DENIED
                                                         ("set_memory_region_in_shared_state"
                                                            ++
                                                            msg)))
                          end
                        | (_, false) =>
                          SUCCESS (st, FFA_ERROR
                                         (FFA_DENIED
                                            "apply_ffa_mem_donate_core_transition_spec"))
                        end
                  | Some res => SUCCESS (st, FFA_ERROR res)
                  end
                | _ => SUCCESS (st, FFA_ERROR
                                     (FFA_INVALID_PARAMETERS
                                        "donate_retrieve_req_check"))
                end
              else SUCCESS (st, FFA_ERROR
                                  (FFA_DENIED
                                     "invalid receiver number")).

    (***********************************************************************)
    (** ***      FFA_MEM_RETRIEVE_REQ - LEND                               *)
    (***********************************************************************)    
    Fixpoint lend_retrieve_req_checks_per_page
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (pages: list Z)
             (descriptor_inst_access: FFA_INSTRUCTION_ACCESS_TYPE)
             (descriptor_data_access: FFA_DATA_ACCESS_TYPE)
             (descriptor_attributes: FFA_MEMORY_TYPE)
             (borrower_number : Z)
      : option (FFA_ERROR_CODE_TYPE) :=
      match pages with
      | nil => None
      | hd::tl =>
        (** - Exctract memory properties and accessibilities *)
        match get_permissions_and_attributes vid hd mem_properties,
              memory_region_descriptor.(FFA_memory_region_struct_flags) with
        | SUCCESS (local_inst_access, local_data_access, local_attributes,
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
                lend_retrieve_req_checks_per_page
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
                lend_retrieve_req_checks_per_page
                  vid time_slice_enabled mem_properties
                  memory_region_descriptor tl
                  descriptor_inst_access
                  descriptor_data_access
                  descriptor_attributes
                  borrower_number
              end
          end
        | SUCCESS _, _ => Some (FFA_INVALID_PARAMETERS
                                 (append_all ["lend_retrieve_req_checks_per_page with";
                                             HexString.of_Z hd; " due to invalid flag"]))
        | FAIL msg, _ =>  Some (FFA_INVALID_PARAMETERS
                                 (append_all ["lend_retrieve_req_checks_per_page with ";
                                             HexString.of_Z hd; " due to "; msg]))
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
               (receiver_tuple : (FFA_endpoint_memory_access_descriptor_struct
                                  * ffa_UUID_t * list Z))
               (receiver_num: Z)
      : option (FFA_ERROR_CODE_TYPE) :=
      match decide (in_dec zeq vid receiver_ids),
            memory_region_descriptor.(FFA_memory_region_struct_flags),
            receiver_tuple with
      (** - Donate operation allows only one receiver *)
      | left _, MEMORY_REGION_FLAG_NORMAL flags,  (receiver, receiver_id, pages) =>
        (** - Check well formed of memory region descriptor *)
        let descriptor_inst_access :=
            get_instruction_access_information_from_descriptor receiver in
        let descriptor_data_access :=
            get_data_access_information_from_descriptor receiver in
        let descriptor_attributes :=
            get_attributes_information_from_descriptor memory_region_descriptor in
        
        match lend_retrieve_req_checks_per_page
                vid time_slice_enabled
                mem_properties memory_region_descriptor pages
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
      | _, _, _ => Some (FFA_INVALID_PARAMETERS
                          "lend_retrieve_req_check")
      end.
         
    Fixpoint apply_ffa_mem_lend_retrieve_req_core_transition_spec
             (lender borrower : ffa_UUID_t) (borrower_num : Z) (pages : list Z) (clean : bool)
             (st : AbstractState) :=
      match pages  with
      | nil => SUCCESS (st, true)
      | hd::tl =>
        match apply_ffa_mem_lend_retrieve_req_core_transition_spec
                lender borrower borrower_num tl clean st with
        | SUCCESS st' =>
          ffa_mem_lend_retrieve_req_core_transition_spec
            lender borrower borrower_num hd clean (fst st')
        | FAIL msg => FAIL msg
        end
      end.
    
    Definition ffa_mem_retrieve_req_lend_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (region_descriptor : FFA_memory_region_struct)
               (st : AbstractState)
    : RESULT (AbstractState * FFA_RESULT_CODE_TYPE) :=
        (** - Get the current memory region descriptor *)
      get_r (AbstractState * FFA_RESULT_CODE_TYPE),
      ipa_info_tuple
      <- (get_recievers_receiver_ids_and_addresses_tuple
           region_descriptor)
          ;;; get_r (AbstractState * FFA_RESULT_CODE_TYPE),
      info_tuple
      <- (SubstIPAsIntoPAs ipa_info_tuple)
          ;;; get_r (AbstractState * FFA_RESULT_CODE_TYPE),
      pa_info_tuple
      <- (SubstIPAsIntoPAs ipa_info_tuple)
          ;;; let info_tuple := convert_addresses_in_info_tuple_to_page_numbers              
                                  pa_info_tuple in
              get_r (AbstractState * FFA_RESULT_CODE_TYPE),
              receiver_info
              <- (get_receiver_tuple caller region_descriptor)
                  ;;;
                  (** - Check the well_formed conditions of the memory region descriptor *)
                  match receiver_info with
                  | (receiver, receiver_id, cur_addresses) =>
                    (* TODO: add cases to handle multiple address transfer *)
                    match (lend_retrieve_req_check
                             caller
                             (st.(hypervisor_context).(time_slice_enabled))
                             (st.(hypervisor_context).(mem_properties))
                             region_descriptor
                             (get_receiver_ids info_tuple)
                             (receiver, receiver_id, cur_addresses)
                             (Zlength (get_receivers region_descriptor))) with 
                    | None =>
                      get (AbstractState * FFA_RESULT_CODE_TYPE),
                      "fail to ge zero flag value",
                      zero_flag_value
                      <- (get_zero_flag_value region_descriptor)
                          ;;; get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                      res
                      <- (apply_ffa_mem_lend_retrieve_req_core_transition_spec
                           caller receiver_id
                           (Zlength (get_receivers region_descriptor))
                           cur_addresses
                           zero_flag_value
                           st)
                          ;;;
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
                            | SUCCESS (st'', value) =>
                              get (AbstractState * FFA_RESULT_CODE_TYPE),
                              "fail to get handle value",
                              handle_value
                              <- (make_handle caller value)
                                  ;;; get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                              res_st
                              <- (set_send_handle caller receiver_id
                                                 region_size handle_value FFA_MEM_RETREIVE_RESP
                                                 st'')
                                  ;;; SUCCESS (res_st, FFA_SUCCESS value)
                            | FAIL msg => SUCCESS (st, FFA_ERROR
                                                 (FFA_DENIED
                                                    ("set_memory_region_in_shared_state"
                                                 ++msg)))
                            end
                          | (_, false) =>
                            SUCCESS (st, FFA_ERROR
                                        (FFA_DENIED
                                           "apply_ffa_mem_lend_retrieve_req_core_transition_spec"))
                          end
                    | Some res => SUCCESS (st, FFA_ERROR res)
                    end
                  end. 

    (***********************************************************************)
    (** ***      FFA_MEM_RETRIEVE_REQ - SHARE                              *)
    (***********************************************************************)
    Fixpoint share_retrieve_req_checks_per_page
             (vid : ffa_UUID_t)
             (time_slice_enabled: bool)
             (mem_properties: MemProperties)
             (memory_region_descriptor: FFA_memory_region_struct)
             (pages: list Z)
             (descriptor_inst_access: FFA_INSTRUCTION_ACCESS_TYPE)
             (descriptor_data_access: FFA_DATA_ACCESS_TYPE)
             (descriptor_attributes: FFA_MEMORY_TYPE)
      : option (FFA_ERROR_CODE_TYPE) :=
      match pages with
      | nil => None
      | hd::tl =>
        (** - Exctract memory properties and accessibilities *)
        match get_permissions_and_attributes vid hd mem_properties,
              memory_region_descriptor.(FFA_memory_region_struct_flags) with
        | SUCCESS (local_inst_access, local_data_access, local_attributes,
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
            share_retrieve_req_checks_per_page
              vid time_slice_enabled mem_properties
              memory_region_descriptor tl
              descriptor_inst_access
              descriptor_data_access
              descriptor_attributes
          end
        | SUCCESS _, _ => Some (FFA_INVALID_PARAMETERS
                                 (append_all ["share_retrieve_req_checks_per_page with";
                                             HexString.of_Z hd; " due to invalid flag"]))
        | FAIL msg, _ =>  Some (FFA_INVALID_PARAMETERS
                                 (append_all ["share_retrieve_req_checks_per_page with ";
                                             HexString.of_Z hd; " due to "; msg]))
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
      | left _, MEMORY_REGION_FLAG_NORMAL flags,  (receiver, receiver_id, pages) =>
        (** - Check well formed of memory region descriptor *)
        let descriptor_inst_access :=
            get_instruction_access_information_from_descriptor receiver in
        let descriptor_data_access :=
            get_data_access_information_from_descriptor receiver in
        let descriptor_attributes :=
            get_attributes_information_from_descriptor memory_region_descriptor in
        
        match share_retrieve_req_checks_per_page
                vid time_slice_enabled
                mem_properties memory_region_descriptor pages
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
      | _, _, _ => Some (FFA_INVALID_PARAMETERS
                          "share_retrieve_req_check")
      end.
                
    Fixpoint apply_ffa_mem_share_retrieve_req_core_transition_spec
             (lender borrower : ffa_UUID_t) (pages : list Z) (clean : bool)
             (st : AbstractState) :=
      match pages with
      | nil => SUCCESS (st, true)
      | hd::tl =>
        match apply_ffa_mem_share_retrieve_req_core_transition_spec
                lender borrower tl clean st with
        | SUCCESS st' =>
          ffa_mem_share_retrieve_req_core_transition_spec
            lender borrower hd clean (fst st')
        | FAIL msg => FAIL msg
        end
      end.
    
    Definition ffa_mem_retrieve_req_share_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (region_descriptor : FFA_memory_region_struct)
               (st : AbstractState)
      : RESULT (AbstractState * FFA_RESULT_CODE_TYPE) :=
      (** - Get the current memory region descriptor *)
      get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
      ipa_info_tuple
      <- (get_recievers_receiver_ids_and_addresses_tuple
           region_descriptor)
          ;;; get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
      pa_info_tuple
      <- (SubstIPAsIntoPAs ipa_info_tuple)
          ;;; let info_tuple := convert_addresses_in_info_tuple_to_page_numbers              
                                  pa_info_tuple in
              get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
              receiver_info
              <- (get_receiver_tuple caller region_descriptor)
                  ;;;
                  (** - Check the well_formed conditions of the memory region descriptor *)
                  match receiver_info with
                  | (receiver, receiver_id, cur_addresses) =>
                    (* TODO: add cases to handle multiple address transfer *)
                    match (lend_retrieve_req_check
                             caller
                             (st.(hypervisor_context).(time_slice_enabled))
                             (st.(hypervisor_context).(mem_properties))
                             region_descriptor
                             (get_receiver_ids info_tuple)
                             (receiver, receiver_id, cur_addresses)
                             (Zlength (get_receivers region_descriptor))) with 
                    | None =>
                      get  (AbstractState * FFA_RESULT_CODE_TYPE),
                      "fail to get zero flag value",
                      zero_flag_value
                      <- (get_zero_flag_value region_descriptor)
                          ;;; get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
                      res
                      <- (apply_ffa_mem_share_retrieve_req_core_transition_spec
                           caller receiver_id
                           cur_addresses
                           zero_flag_value
                           st)
                          ;;; match res with  
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
                                | SUCCESS (st'', value) =>
                                  get (AbstractState * FFA_RESULT_CODE_TYPE),
                                  "fail to get handle value",
                                  handle_value
                                  <- (make_handle caller value)
                                      ;;; get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
                                  res_st
                                  <- (set_send_handle caller receiver_id
                                                     region_size handle_value FFA_MEM_RETREIVE_RESP
                                                     st'')
                                      ;;;  SUCCESS (res_st, FFA_SUCCESS value)
                                | FAIL msg => SUCCESS (st, FFA_ERROR
                                                            (FFA_DENIED
                                                               ("set_memory_region_in_shared_state"
                                                                  ++ msg)))
                                end
                              | (_, false) =>
                                SUCCESS (st, FFA_ERROR
                                               (FFA_DENIED
                                                  "apply_ffa_mem_share_retrieve_req_core_transition_spec"))
                              end
                    | Some res => SUCCESS (st, FFA_ERROR res)
                    end
                  end. 


    (***********************************************************************)
    (** ***      FFA_MEM_RETRIEVE_REQ - MERGED                             *)
    (***********************************************************************)    
    Definition ffa_mem_retrieve_req_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (st : AbstractState)
      : RESULT (AbstractState * FFA_RESULT_CODE_TYPE) :=
      if ffa_mem_general_check_arguments total_length fragment_length address count
      then
        get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
        state_and_handle
        <- (get_send_handle_value caller st)
            ;;; let '(state, handle) := state_and_handle in
                get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
                share_state
                <- (get_handle_information handle state)
                    ;;; match share_state with 
                        | mkFFA_memory_share_state_struct
                            memory_region share_func retrieved relinquished retrieve_count
                          => match ZTree.get caller retrieved with 
                            (** TODO: need to add retrieve_count and relinquished later *)
                            | Some is_retrieved =>
                              if is_retrieved
                              then SUCCESS (st, FFA_ERROR
                                                  (FFA_DENIED
                                                     "already retrieved"))
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
                                   | _ => SUCCESS (st, FFA_ERROR
                                                        (FFA_DENIED
                                                           "invalid share function"))
                                   end
                            | _ => SUCCESS (st, FFA_ERROR
                                                 (FFA_DENIED
                                                    "invalid share state"))
                            end
                        end
      else SUCCESS (st, FFA_ERROR
                          (FFA_INVALID_PARAMETERS
                             "ffa_mem_general_check_arguments")).
    
  End FFA_MEM_RETRIEVE_REQ_ARGUMENT_CHECKS.

  (***********************************************************************)
  (** **  11.5 FFA_MEM_RETRIEVE_RESP                                    *)
  (***********************************************************************)
  Section FFA_MEM_RETRIEVE_RESP_ARGUMENT_CHECKS.
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
    : RESULT (AbstractState * FFA_RESULT_CODE_TYPE) :=
      if ffa_mem_retrieve_resp_check_arguments total_length fragment_length 
      then SUCCESS (st, FFA_SUCCESS 0)
      else SUCCESS (st, FFA_ERROR
                          (FFA_INVALID_PARAMETERS " ")).
    
  End FFA_MEM_RETRIEVE_RESP_ARGUMENT_CHECKS.

  (***********************************************************************)
  (** **   11.6 FFA_MEM_RELINQUISH                                       *)
  (***********************************************************************)
  Section FFA_MEM_RELINQUISH_ARGUMENT_CHECKS.
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

    Fixpoint apply_ffa_mem_relinquish_core_transition_spec
             (index : Z) (lender borrower : ffa_UUID_t)
             (pages : list Z) (clean : bool)
             (st : AbstractState) :=
      match pages  with
      | nil => SUCCESS (st, true)
      | hd::tl =>
        match apply_ffa_mem_relinquish_core_transition_spec
                index lender borrower tl clean st with
        | SUCCESS st' =>
          get_r (AbstractState * bool),
          st''
          <- (unset_retrieve index borrower hd (fst st'))
              ;;;
              ffa_mem_relinquish_core_transition_spec
              lender borrower hd clean st''
        | FAIL msg => FAIL msg
        end
      end.
    Fixpoint FFA_mem_relinquish_req_alignment_hint_check_iter 
             (relinquish_flag: FFA_mem_relinquish_req_flags_struct)
             (addrs  : list Z) :=
      match addrs with
      | nil => None
      | hd::tl =>
        match FFA_mem_relinquish_req_alignment_hint_check_iter
                relinquish_flag tl with
        | Some res => Some res
        | _ => FFA_mem_relinquish_req_alignment_hint_check
                relinquish_flag hd
        end
      end.
    
    Fixpoint FFA_mem_relinquish_req_zero_flags_for_donate_and_lend_check_per_page
             (relinquish_flag: FFA_mem_relinquish_req_flags_struct)
             (mem_properties: MemProperties)
             (sender : ffa_UUID_t)
             (pages: list Z)
             (time_slice_enabled : bool) :=
      match pages with
      | nil => None
      | hd::tl => 
        match FFA_mem_relinquish_req_zero_flags_for_donate_and_lend_check_per_page
                relinquish_flag mem_properties sender tl time_slice_enabled with
        | None =>
          match get_data_access_from_global_local_pool_props
                  sender hd mem_properties.(mem_local_properties) with
          | FAIL msg => Some (FFA_INVALID_PARAMETERS msg)
          | SUCCESS sender_data_access =>
            FFA_mem_relinquish_req_zero_flags_for_donate_and_lend_check
              relinquish_flag sender_data_access time_slice_enabled
          end
        | Some res => Some res
        end
      end. 

    Fixpoint FFA_mem_relinquish_req_zero_after_flags_for_donate_and_lend_check_per_page
               (relinquish_flag: FFA_mem_relinquish_req_flags_struct)
               (mem_properties: MemProperties)
               (receiver : ffa_UUID_t)
               (pages: list Z) :=
      match pages with
      | nil => None
      | hd::tl => 
        match FFA_mem_relinquish_req_zero_after_flags_for_donate_and_lend_check_per_page
                relinquish_flag mem_properties receiver tl with
        | None =>
          match get_data_access_from_global_local_pool_props
                  receiver hd mem_properties.(mem_local_properties) with
          | FAIL msg => Some (FFA_INVALID_PARAMETERS msg)
          | SUCCESS receiver_data_access =>
            FFA_mem_relinquish_req_zero_after_flags_for_donate_and_lend_check
              relinquish_flag receiver_data_access
          end
        | Some res => Some res
        end
      end. 
      
    Definition ffa_mem_relinquish_spec
               (caller : ffa_UUID_t)
               (st : AbstractState)
      : RESULT (AbstractState * FFA_RESULT_CODE_TYPE) :=
      get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
      state_and_relinquish_descriptor
      <- (get_send_relinquish_descriptor caller st)
          ;;;
          let '(state, relinquish_descriptor) := state_and_relinquish_descriptor in
          let handle_value := relinquish_descriptor.(FFA_memory_relinquish_struct_handle) in
          let flags := relinquish_descriptor.(FFA_memory_relinquish_struct_flags ) in
          let receivers := relinquish_descriptor.(FFA_memory_relinquish_struct_endpoints) in
          get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
          share_state
          <- (get_handle_information handle_value state)
              ;;;
              match share_state, flags with
              | mkFFA_memory_share_state_struct
                  memory_region share_func retrieved relinquished retrieve_count,
                MEMORY_REGION_FLAG_RELINQUISH_REQ flags            
                => match ZTree.get caller retrieved with 
                  (** TODO: need to add retrieve_count and relinquished later - Need to do for reclaim *)
                  | Some is_retrieved =>
                    if is_retrieved
                    then
                      match FFA_mem_relinquish_req_zero_after_flags_for_share_check flags,
                            FFA_mem_relinquish_req_transaction_type_check flags (Some share_func) with
                      | Some res, _
                      | None, Some res =>  SUCCESS (st, FFA_ERROR res)
                      | None, None =>
                        let sender := memory_region.(FFA_memory_region_struct_sender) in
                        get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
                        ipa_info_tuple
                        <- (get_recievers_receiver_ids_and_addresses_tuple memory_region)
                            ;;;
                            get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
                        info_tuple
                        <- (SubstIPAsIntoPAs ipa_info_tuple)
                            ;;;
                            let receiver_tuple :=
                                get_receiver_tuple
                                  caller memory_region in
                            let receiver_ids_in_region_des :=
                                get_receiver_ids info_tuple in
                            match decide (list_eq_dec zeq receiver_ids_in_region_des receivers), receiver_tuple with
                            | left _, SUCCESS (receiver, receiver_id, addrs) =>
                              let check_res :=
                                  match FFA_mem_relinquish_req_alignment_hint_check_iter flags addrs with
                                  | Some res => Some res
                                  | _ => 
                                    match share_func with
                                    | FFA_MEM_DONATE
                                    | FFA_MEM_LEND
                                      => match FFA_mem_relinquish_req_zero_flags_for_donate_and_lend_check_per_page
                                                flags (st.(hypervisor_context).(mem_properties))
                                                sender addrs (st.(hypervisor_context).(time_slice_enabled)),
                                              FFA_mem_relinquish_req_zero_after_flags_for_donate_and_lend_check_per_page
                                                flags (st.(hypervisor_context).(mem_properties)) caller
                                                (convert_addresses_to_page_numbers addrs) with
                                        | Some res, _
                                        | None, Some res => Some res
                                        | None, None => None
                                        end
                                    | FFA_MEM_SHARE => FFA_mem_relinquish_req_zero_flags_for_share_check flags 
                                    | _ => Some
                                            (FFA_INVALID_PARAMETERS
                                               "share_func")
                                    end
                                  end in
                              match check_res with
                              | Some res => SUCCESS (st, FFA_ERROR res)
                              | None =>
                                get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
                                st'
                                <- (apply_ffa_mem_relinquish_core_transition_spec
                                     (get_value handle_value) sender caller
                                     (convert_addresses_to_page_numbers addrs)
                                     (flags.(FFA_mem_relinquish_req_flags_struct_zero_memory_before_retrieval_flag))
                                     st)
                                    ;;;
                                    match st' with
                                    | (st'', true) => SUCCESS (st'', FFA_SUCCESS 0)
                                    | (_, false) =>
                                      SUCCESS (st, FFA_ERROR
                                                     (FFA_DENIED
                                                        "apply_ffa_mem_relinquish_core_transition_spec"))
                                    end
                              end
                            | _, _ =>
                              SUCCESS (st, FFA_ERROR
                                             (FFA_INVALID_PARAMETERS
                                                "invalid receiver"))
                            end
                      end                                 
                    else SUCCESS (st, FFA_ERROR
                                        (FFA_INVALID_PARAMETERS
                                           "already retrieved"))
                  | _ => SUCCESS (st, FFA_ERROR
                                       (FFA_INVALID_PARAMETERS
                                          "cannot find retrieved info"))
                  end
              | _,_ => SUCCESS (st, FFA_ERROR
                                     (FFA_INVALID_PARAMETERS
                                        "share_state"))
              end.
    
  End FFA_MEM_RELINQUISH_ARGUMENT_CHECKS.
    
  (***********************************************************************)
  (** **   11.7 FFA_MEM_RECLAIM                                          *)
  (***********************************************************************)
  Section FFA_MEM_RECLAIM_ARGUMENT_CHECKS.
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


    Fixpoint mem_reclaim_check_per_page (pages: list Z) (receiver_retrieved_map : ZTree.t bool) :=
      match pages with
      | nil => None
      | hd::tl =>
        match mem_reclaim_check_per_page tl receiver_retrieved_map with
        | None =>  
          match ZTree.get hd receiver_retrieved_map with
          | Some false => None
          | _ => Some (FFA_DENIED
                        "denied")
          end
        | Some res => Some res
        end
      end.

    Fixpoint mem_reclaim_check
             (info_tuple: list (FFA_endpoint_memory_access_descriptor_struct *
                                ffa_UUID_t * list Z))
             (retrieved_map : ZTree.t (ZTree.t bool)) : option FFA_ERROR_CODE_TYPE :=
      match info_tuple with
      | nil => None
      | (receiver, receiver_id, pages)::tl =>
        match mem_reclaim_check tl retrieved_map with
        | None => 
          match ZTree.get receiver_id retrieved_map with
          | Some receiver_retrieved_map =>
            mem_reclaim_check_per_page pages receiver_retrieved_map
          | None => Some (FFA_DENIED
                           "mem_reclaim_check")
          end
        | Some res => Some res
        end
      end.


    Definition remove_local_memory_property_per_receiver
               (receiver : ffa_UUID_t) 
               (addr : Z) 
               (st : AbstractState) : AbstractState :=
      match ZTree.get receiver st.(hypervisor_context).(mem_properties).(mem_local_properties) with
      | Some local_prop =>
        match ZTree.get addr local_prop with
        | Some _ => let new_local_prop := ZTree.remove addr local_prop in
                   let new_local_global_pool :=
                       ZTree.set receiver new_local_prop
                                 st.(hypervisor_context).(mem_properties).(mem_local_properties) in
                   let new_memory_props :=
                       mkMemProperties
                         (st.(hypervisor_context).(mem_properties).(mem_global_properties))
                         new_local_global_pool in
                   st {hypervisor_context / mem_properties : new_memory_props}
        | _ => st
        end
      | None => st
      end.

    Fixpoint remove_local_memory_property_for_receivers
               (receivers : list ffa_UUID_t) 
               (page : Z) 
               (st : AbstractState) : AbstractState :=
      match receivers with
      | nil => st
      | hd::tl =>
        let st' := remove_local_memory_property_for_receivers tl page st in
        remove_local_memory_property_per_receiver hd page st
      end.
    
    Definition ffa_mem_reclaim_core_transition
               (sender :ffa_UUID_t)
               (receivers : list ffa_UUID_t) 
               (page : Z) 
               (clean: bool)
               (st : AbstractState) : RESULT AbstractState :=
      let new_st := remove_local_memory_property_for_receivers
                      receivers page st in
      get  AbstractState,
      "cannot get global property",
      global_property
      <- (ZTree.get page (hyp_mem_global_props st))
          ;;; get  AbstractState,
      "cannot get sender properties",
      sender_properties_pool
      <- (ZTree.get sender (hyp_mem_local_props st))
          ;;; get  AbstractState,
      "cannot gett sender property",
      sender_property
      <- (ZTree.get page sender_properties_pool)
          ;;;
          let new_global_properties :=
              ZTree.set page
                        (global_property
                           {owned_by: Owned sender}
                           {accessible_by: ExclusiveAccess sender}
                           {mem_dirty : if clean then MemClean
                                        else global_property.(mem_dirty)})
                        (hyp_mem_global_props st) in
          let new_sender_properties_pool :=
              ZTree.set page
                        (gen_own_mem_local_properties_wrapper sender_property) 
                        sender_properties_pool in
          let new_local_properties_global_pool :=
              ZTree.set sender
                        new_sender_properties_pool
                        (hyp_mem_local_props st) in
          let new_st :=
              st {hypervisor_context / mem_properties :
                    mkMemProperties new_global_properties
                                    new_local_properties_global_pool} in
          SUCCESS new_st.
               
    Fixpoint apply_ffa_mem_reclaim_core_transition
               (sender :ffa_UUID_t)
               (receivers : list ffa_UUID_t) 
               (pages : list Z) 
               (clean: bool)
               (st : AbstractState) : RESULT AbstractState :=
      match pages with
      | nil => SUCCESS st
      | hd::tl =>
        match  apply_ffa_mem_reclaim_core_transition
                 sender receivers tl clean st with
        | SUCCESS st' => ffa_mem_reclaim_core_transition
                       sender receivers hd clean st'
        | FAIL msg => FAIL msg
        end
      end.
    
    Definition ffa_mem_reclaim_spec
               (caller : ffa_UUID_t)
               (handle_high handle_low flags : Z)
               (st : AbstractState)
    : RESULT (AbstractState * FFA_RESULT_CODE_TYPE) :=
      let handle := (Z.lor (Z.shiftl handle_high 32) handle_low) in
      let zero_flag := if decide ((Z.land flags 0) <> 0) then true else false in
      let time_slice_flags := if decide ((Z.land flags 1) <> 0) then true else false in
      get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
      share_state <-
      (get_handle_information handle st)
        ;;;
      match share_state with
      | mkFFA_memory_share_state_struct
          memory_region share_func retrieved relinquished retrieve_count =>
        if decide (memory_region.(FFA_memory_region_struct_sender) <> caller)
        then SUCCESS (st, FFA_ERROR
                         (FFA_INVALID_PARAMETERS
                            " "))
        else
          get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
        ipa_info_tuple
        <- (get_recievers_receiver_ids_and_addresses_tuple memory_region)
            ;;; get_r  (AbstractState * FFA_RESULT_CODE_TYPE),
        pa_info_tuple
        <- (SubstIPAsIntoPAs ipa_info_tuple)
            ;;; let info_tuple := convert_addresses_in_info_tuple_to_page_numbers              
                                    pa_info_tuple in
                match mem_reclaim_check info_tuple retrieved with
                | None =>
                  match apply_ffa_mem_reclaim_core_transition
                          caller (get_receiver_ids info_tuple)
                          (get_all_addresses memory_region)
                          zero_flag st with
                  | SUCCESS st' =>
                    match remove_share_state (get_value handle) st' with
                    | SUCCESS st'' => SUCCESS (st'', FFA_SUCCESS 0)
                    | FAIL msg => SUCCESS (st, FFA_ERROR
                                                (FFA_DENIED
                                                   ("remove_share_state due to "
                                                      ++msg)))
                    end
                  | FAIL msg => SUCCESS (st, FFA_ERROR
                                       (FFA_DENIED
                                          ("mem_reclaim_check due to "
                                             ++msg)))
                  end
                | Some res => SUCCESS (st, FFA_ERROR res)
                end
      end.
    
  End FFA_MEM_RECLAIM_ARGUMENT_CHECKS.
    
End FFA_MEMORY_INTERFACE_ADDITIONAL_STEPS.

(***********************************************************************)
(** *  Wrong Step Rules for Memory Management                          *)
(***********************************************************************)
Section FFA_MEMORY_INTERFACE_ADDITIONA_STEPS_ERROR_TESTING.

  Context `{abstract_state_context: AbstractStateContext}.

  Section FFA_MEM_DONATE_ADDITIONAL_STEPS_ERROR.
  
    Definition ffa_mem_donate_wrong_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
               (st: AbstractState)
      : RESULT (AbstractState * FFA_RESULT_CODE_TYPE) :=
      (** - Check the arguments *)
      if ffa_mem_general_check_arguments total_length fragment_length address count
      then
        (** - Get the current memory region descriptor *)
        get_r (AbstractState * FFA_RESULT_CODE_TYPE),
        state_and_memory_region_descriptor
        <- (get_send_memory_region_descriptor caller st)
            ;;;
            let (state, memory_region_descriptor)
                := state_and_memory_region_descriptor in
            (** - Extract information from the descriptor  *) 
            get_r (AbstractState * FFA_RESULT_CODE_TYPE),
            ipa_info_tuple <-
            (get_recievers_receiver_ids_and_addresses_tuple
               memory_region_descriptor)
              ;;; get_r (AbstractState * FFA_RESULT_CODE_TYPE),
              pa_info_tuple
              <- (SubstIPAsIntoPAs ipa_info_tuple)
                  ;;; let info_tuple
                          := convert_addresses_in_info_tuple_to_page_numbers              
                               pa_info_tuple in
                      (** - Check the well_formed conditions of the memory region descriptor *)
                      (***********************************************************************)
                      (** This part is wrong - num. of receivers should be 1 *)                      
                      (***********************************************************************)                                
                      if decide ((length (get_receivers memory_region_descriptor) = 2)%nat)
                      then
                        let region_size
                            := (FFA_memory_region_struct_size
                                  (Zlength
                                     (memory_region_descriptor
                                      .(FFA_memory_region_struct_composite)
                                      .(FFA_composite_memory_region_struct_constituents)))) in
                        if decide ((region_size < state.(hypervisor_context).(api_page_pool_size))%Z)
                        then
                          match info_tuple with
                          | (receiver, receiver_id, cur_addresses)::nil =>
                            (* TODO: add cases to handle multiple address transfer *)
                            (***********************************************************************)
                            (** This part is wrong - it uses lend_check instead of donate_check *)
                            (***********************************************************************)
                            match (lend_check
                                     caller
                                     (state.(hypervisor_context).(time_slice_enabled))
                                     (state.(hypervisor_context).(mem_properties))
                                     memory_region_descriptor info_tuple) with 
                            | None =>
                              get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                              res
                              <- (apply_ffa_mem_donate_core_transition_spec
                                   caller receiver_id cur_addresses state)
                                  ;;;
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
                                    | SUCCESS (st'', handle_value) =>
                                      get_r (AbstractState * FFA_RESULT_CODE_TYPE),
                                      res_st
                                      <- (set_send_handle caller receiver_id
                                                         region_size handle_value FFA_MEM_DONATE
                                                         st'')
                                          ;;;
                                          SUCCESS (res_st, FFA_SUCCESS handle_value)
                                    | FAIL msg => SUCCESS (st, FFA_ERROR
                                                                (FFA_DENIED
                                                                   ("ffa_mem_general_check_arguments: "
                                                                      ++ msg)))
                                    end
                                  | (_, false) =>
                                    SUCCESS (st, FFA_ERROR
                                                (FFA_DENIED
                                                   "apply_ffa_mem_donate_core_transition_spec"))
                                  end
                            | Some res => SUCCESS (st, FFA_ERROR res)
                            end
                          | _ => SUCCESS (st, FFA_ERROR
                                            (FFA_INVALID_PARAMETERS
                                               "info_tuple invalid"))
                          end
                        else SUCCESS (st, FFA_ERROR
                                         (FFA_NO_MEMORY
                                            "mpool size is too small"))
                      else SUCCESS (st, FFA_ERROR
                                       (FFA_DENIED
                                          "wrong receiver number"))
      else SUCCESS (st, FFA_ERROR
                          (FFA_INVALID_PARAMETERS
                             "ffa_mem_general_check_arguments")).
    
  End FFA_MEM_DONATE_ADDITIONAL_STEPS_ERROR.

End FFA_MEMORY_INTERFACE_ADDITIONA_STEPS_ERROR_TESTING.
