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


Inductive terminate {E} {R} (it:itree E R) : Prop :=
| TermRet
    v
    (RET: observe it = RetF v)
| TermTau
    (TAU: observe it = TauF it).

(* From HafniumCore *)
Require Import Lang.
Require Import Values.
Require Import Integers.
Require Import Constant.
Require Import Decision.

Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Require Import Maps.
Set Implicit Arguments.

Require Export FFAMemoryHypCallState.

(*************************************************************)
(*         Auxiliary functions                               *)
(*************************************************************)
Section FFAAuxiliaryFunctions.
  
  (* Auxiliary functions *)
  (*
  static inline ffa_vm_id_t ffa_msg_send_sender(struct ffa_value args)
         {
	   return (args.arg1 >> 16) & 0xffff;
         }
   *)

  Definition ffa_msg_send_sender (args: FFA_value_type) : Z :=
    Z.land (Z.shiftr (ZMap.get 1 (args.(vals))) 16) 65535.


  (*
  static inline ffa_vm_id_t ffa_msg_send_receiver(struct ffa_value args)
  {
          return args.arg1 & 0xffff;
  }
   *)
  Definition ffa_msg_receiver_sender (args: FFA_value_type) : Z :=
    Z.land (ZMap.get 1 (args.(vals))) 65535.

  
  (*
  static inline uint32_t ffa_msg_send_size(struct ffa_value args)
  {
          return args.arg3;
  }
   *)
  Definition ffa_msg_send_size (args: FFA_value_type) : Z :=
    ZMap.get 3 args.(vals).

  (*
  static inline uint32_t ffa_msg_send_attributes(struct ffa_value args)
  {
          return args.arg4;
  }
   *)
  Definition ffa_msg_send_attributes (args: FFA_value_type) : Z :=
    ZMap.get 4 args.(vals).

  (*
  static inline ffa_memory_handle_t ffa_assemble_handle(uint32_t a1, uint32_t a2)
  {
          return (uint64_t)a1 | (uint64_t)a2 << 32;
  }
   *)
  Definition ffa_assemble_handle (a1 a2 : Z) : ffa_memory_handle_t :=
    Z.lor a1 (Z.shiftl a2 32).
  

  (*
  static inline ffa_memory_handle_t ffa_mem_success_handle(struct ffa_value args)
  {
          return ffa_assemble_handle(args.arg2, args.arg3);
  }
  *)
  Definition ffa_mem_success_handle (args : FFA_value_type) : ffa_memory_handle_t :=
    ffa_assemble_handle (ZMap.get 2 args.(vals)) (ZMap.get 3 args.(vals)).

  (*
  static inline struct ffa_value ffa_mem_success(ffa_memory_handle_t handle)
  {
          return (struct ffa_value){.func = FFA_SUCCESS_32,
          			  .arg2 = (uint32_t)handle,
          			  .arg3 = (uint32_t)(handle >> 32)};
  }
   *)

  Definition ffa_mem_success (handle : ffa_memory_handle_t) : FFA_value_type :=
    mkFFA_value_type (FFA_RESULT_CODE_IDENTIFIER FFA_SUCCESS)
                     (ZMap.set 2 handle (ZMap.set 3 (Z.shiftr handle 32) (ZMap.init 0))).
    

  (*
  static inline ffa_vm_id_t ffa_vm_id(struct ffa_value args)
  {
          return (args.arg1 >> 16) & 0xffff;
  }
   *)

  Definition ffa_vm_id (args : FFA_value_type) : ffa_vm_id_t :=
    Z.land (ZMap.get 1 (args.(vals))) 65535.
    
  
  (*
  static inline ffa_vcpu_index_t ffa_vcpu_index(struct ffa_value args)
  {
          return args.arg1 & 0xffff;
  }
   *)
  Definition ffa_vcpu_index (args : FFA_value_type) : ffa_vcpu_index_t :=
    Z.land (ZMap.get 1 (args.(vals))) 65535.
    
  (*
  static inline uint64_t ffa_vm_vcpu(ffa_vm_id_t vm_id,
          			   ffa_vcpu_index_t vcpu_index)
  {
          return ((uint32_t)vm_id << 16) | vcpu_index;
  }
   *)
  Definition ffa_vm_vcpu (vm_id : ffa_vm_id_t) (vcpu_index : ffa_vcpu_index_t) : Z :=
    Z.lor (Z.shiftl vm_id 16) vcpu_index.

  (*
  /**
   * Clear memory region contents after unmapping it from the sender and before
   * mapping it for any receiver.
   */
  #define FFA_MEMORY_REGION_FLAG_CLEAR 0x1
   
  /**
   * Whether the hypervisor may time slice the memory sharing or retrieval
   * operation.
   */
  #define FFA_MEMORY_REGION_FLAG_TIME_SLICE 0x2
   
  /**
   * Whether the hypervisor should clear the memory region after the receiver
   * relinquishes it or is aborted.
   */
  #define FFA_MEMORY_REGION_FLAG_CLEAR_RELINQUISH 0x4
   
  #define FFA_MEMORY_REGION_TRANSACTION_TYPE_MASK ((0x3U) << 3)
  #define FFA_MEMORY_REGION_TRANSACTION_TYPE_UNSPECIFIED ((0x0U) << 3)
  #define FFA_MEMORY_REGION_TRANSACTION_TYPE_SHARE ((0x1U) << 3)
  #define FFA_MEMORY_REGION_TRANSACTION_TYPE_LEND ((0x2U) << 3)
  #define FFA_MEMORY_REGION_TRANSACTION_TYPE_DONATE ((0x3U) << 3)
   *)


  Definition FFA_MEMORY_REGION_FLAG_CLEAR_Z := 1.
  Definition FFA_MEMORY_REGION_FLAAG_TIME_SLICE_Z := 2.
  Definition FFA_MEMORY_REGION_FLAG_CLEAR_RELINGQUISH_Z := 4.

  Definition FFA_MEMORY_REGION_TRANSACTION_TYPE_MASK_Z := Z.shiftl 3 3.
  Definition FFA_MEMORY_REGION_TRANSACTION_TYPE_UNSPECIFIED_Z := Z.shiftl 0 3.
  Definition FFA_MEMORY_REGION_TRANSACTION_TYPE_SHARE_Z := Z.shiftl 1 3.
  Definition FFA_MEMORY_REGION_TRANSACTION_TYPE_LEND_Z := Z.shiftl 2 3.
  Definition FFA_MEMORY_REGION_TRANSACTION_TYPE_DONATE_Z := Z.shiftl 3 3.

  (* TODO : need to do something with the following functions *) 
  (*
  /**
   * Gets the `ffa_composite_memory_region` for the given receiver from an
   * `ffa_memory_region`, or NULL if it is not valid.
   */
  static inline struct ffa_composite_memory_region *
  ffa_memory_region_get_composite(struct ffa_memory_region *memory_region,
          			uint32_t receiver_index)
  {
          uint32_t offset = memory_region->receivers[receiver_index]
          			  .composite_memory_region_offset;
   
          if (offset == 0) {
          	return NULL;
          }
   
          return (struct ffa_composite_memory_region * )((uint8_t * )memory_region +
          					      offset);
  }
   
  static inline uint32_t ffa_mem_relinquish_init(
          struct ffa_mem_relinquish *relinquish_request,
          ffa_memory_handle_t handle, ffa_memory_region_flags_t flags,
          ffa_vm_id_t sender)
  {
          relinquish_request->handle = handle;
          relinquish_request->flags = flags;
          relinquish_request->endpoint_count = 1;
          relinquish_request->endpoints[0] = sender;
          return sizeof(struct ffa_mem_relinquish) + sizeof(ffa_vm_id_t);
  }
  *)
   
End FFAAuxiliaryFunctions.


Inductive updateStateE: Type -> Type :=
| GetState : updateStateE AbstractState
| SetState (st: AbstractState): updateStateE unit.
 
Definition updateState_handler {E: Type -> Type}
  : updateStateE ~> stateT AbstractState (itree E) :=
  fun _ e st =>
    match e with
    | GetState => Ret (st, st)
    | SetState st' => Ret (st', tt)
    end.
 
Notation HafniumEE := (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).
 
Notation "'do' X <- A ;;; B" := (match A with Some X => B | None => triggerUB "None" end)
  (at level 200, X ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation "'do' X , Y <- A ;;; B" := (match A with Some (X, Y) => B | None => triggerUB "None" end)
  (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation "'do' X , Y , Z <- A ;;; B" := (match A with Some (X, Y, Z) => B | None => triggerUB "None" end)
  (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation " 'check' A ;;; B" := (if A then B else Ret None)
  (at level 200, A at level 100, B at level 200)
  : itree_monad_scope.
 
Local Open Scope itree_monad_scope.

Section FFAMemoryHypCall.

  Context `{address_translation: AddressTranslation}.
  Context `{hafnium_memory_management_context :
              !HafniumMemoryManagementContext (address_translation := address_translation)}.
  Context `{vm_context : VMContext}.
  Context `{abstract_state_context: !AbstractStateContext
                                     (hafnium_memory_management_context
                                        := hafnium_memory_management_context)}.

  (************************************************************************)
  (*                 Context switching related parts                      *)
  (************************************************************************)
  (* most parts are related to save registers in "/src/arch/aarch64/hypervisor/exceptions.S"
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
  Section FFAContextSwitching.

    (* Save contexts *)
    Definition save_regs_to_vcpu_spec  :
      itree HafniumEE (unit) := 
      st <- trigger GetState;;
      (* check whether the current running entity is one of VMs *)
      if decide (st.(cur_entity_id) <> hafnium_id) && in_dec zeq st.(cur_entity_id) vm_ids
      then (* get contexts for the currently running entity ID *)
        do vm_userspace <- ZTree.get st.(cur_entity_id) st.(vms_userspaces) ;;;
        do vcpu_regs <- ZTree.get vm_userspace.(userspace_cur_vcpu_index) vm_userspace.(userspace_vcpus) ;;;
        (* get vm contexts in Hanfium to save the userspace information in it *)              
        do vm_context <- ZTree.get st.(cur_entity_id) st.(hafnium_context).(vms_contexts) ;;;
        if decide (vm_context.(vcpu_num) = vm_userspace.(userspace_vcpu_num)) &&
           decide (vcpu_regs.(vm_id) = Some st.(cur_entity_id))
        then
          let new_vcpu_id := vm_userspace.(userspace_cur_vcpu_index) in
          let new_vm_context := vm_context {vm_cur_vcpu_index: new_vcpu_id}
                                           {vm_vcpus:
                                              ZTree.set new_vcpu_id vcpu_regs vm_context.(vcpus)} in
          let new_vms_contexts :=
              ZTree.set st.(cur_entity_id) new_vm_context st.(hafnium_context).(vms_contexts) in
          let new_st := st {cur_entity_id: hafnium_id}
                           {hafnium_context/tpidr_el2: Some vcpu_regs}
                           {hafnium_context/vms_contexts: new_vms_contexts} in 
          trigger (SetState new_st)
        else triggerUB "save_resg_to_vcpu_spec: inconsistency in total vcpu number"
      else triggerUB "save_resg_to_vcpu_spec: wrong cur entity id".

    
    Definition save_regs_to_vcpu_call (args : list Lang.val) :=
      match args with
      | nil => save_regs_to_vcpu_spec
      | _ => triggerUB "save_regs_to_vcpu_call: wrong arguments"
      end.

    (* Restore contexts and run.
       It also contains choosing the next vm to run by using an abstract scheduler  
     *)
    Definition vcpu_restore_and_run_spec  :
      itree HafniumEE (unit) := 
      st <- trigger GetState;;
      (* find out the next vm to be scheduled *)
      let next_vm_id := scheduler st in
      (* check whether the current running entity is Hafnium *)
      if decide (st.(cur_entity_id) = hafnium_id) && in_dec zeq next_vm_id vm_ids
      then
        (* get the userspace information *)
        do vm_userspace <- ZTree.get next_vm_id st.(vms_userspaces) ;;;
        (* get vm context to restore the userspace information *)
        do vm_context <- ZTree.get next_vm_id st.(hafnium_context).(vms_contexts) ;;;
        (* get vcpu register information *)
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
                              {hafnium_context/tpidr_el2: None}
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

  (************************************************************************)
  (*                 FFA ABI for memory management                        *)
  (************************************************************************)
  (* All the following things are calls via "struct vcpu *sync_lower_exception(uintreg_t esr)" 
     defined in "/src/arch/aarch64/hypervisor/handler.c". 

     Depending on "uintreg_t ec = GET_ESR_EC(esr);", the exception case, the function calls
     the proper handler. The main focus of our prototyping is when "EC_HVC", which are for 
     hypervisor calls.
     
     "struct vcpu *hvc_handler(struct vcpu *vcpu)" is also a function that is defined in the same file.

     For all cases that we consider in here, "(ffa_handler(&args, &next))" is a function 
     that handles ffa related exceptions and return true.

     "static bool ffa_handler(struct ffa_value *args, struct vcpu **next)" is also a function in the
     the same file. Among all cases, cases they we are considering are as follows.

     <<
	case FFA_MEM_DONATE_32:
	case FFA_MEM_LEND_32:
	case FFA_MEM_SHARE_32:
		*args = api_ffa_mem_send(func, args->arg1, args->arg2,
					 ipa_init(args->arg3), args->arg4,
					 current(), next);
		return true;
	case FFA_MEM_RETRIEVE_REQ_32:
		*args = api_ffa_mem_retrieve_req(args->arg1, args->arg2,
						 ipa_init(args->arg3),
						 args->arg4, current());
		return true;
	case FFA_MEM_RELINQUISH_32:
		*args = api_ffa_mem_relinquish(current());
		return true;
	case FFA_MEM_RECLAIM_32:
		*args = api_ffa_mem_reclaim(
			ffa_assemble_handle(args->arg1, args   ->arg2), args->arg3,
			current());     
    >>
  *)


  Section FFADispatch.
    
    
  End FFADispatch.  
  
  (* Send is for three FFA ABIs, SHARE, DONATE, and LEND. *)
  Section FFAMemoryHypCallSend.

    (* FFA_MEM_DONATE, FFA_MEM_LEND, and FFA_MEM_SHARE shares the common features. 
       Therefore, Hafnium provides a uniform interface for that. *)

    (* 
       Chapter 11 of "https://developer.arm.com/documentation/den0077/latest" provides interfaces for 
       those FFA ABIs

       Table 11.3: FFA_MEM_DONATE function syntax 
       Table 11.8: FFA_MEM_LEND function syntax 
       Table 11.13: FFA_MEM_SHARE function syntax 

       parameter                  register        value                  
       uint32 Function ID         w0              0x84000071 for FFA_MEM_DONATE
                                                  0x84000072 for FFA_MEM_LEND
                                                  0x84000073 for FFA_MEM_SHARE
       uint32 total length        w1              Total length of the memory transaction descriptor in
                                                  bytes
       uint32 Fragment length     w2              It's for more fine-grained control, but it will be 
                                                  ignored in here (the value in w1 has to be equal to 
                                                  be the value in w2).
       uint32/uint64 Address      w3              Base address of a buffer allocated by the Owner and
                                                  distinct from the TX buffer. More information is
                                                  in 12.2.1. MBZ if the TX buffer is used.
       uint32 Page count          w4              Number of 4K page in the buffer allocated by the 
                                                  Owner and distinct from the TX buffer. More details
                                                  are in 12.2.1. MBZ if the TX buffer is used

     *)

    
    (* FFA_SUCCESS encoding 
       Table 11.4, Table 11.9, Table 11.14

       uint64 Handle           w2/w3            Global unique Handle to identify the memory region on 
                                                successful transition of the transaction descriptor. 
                                                MBZ otherwise. Details about Handle is in 5.10.2. *)
    
    (* FFA_ERROR encoding 
       Table 11.5, Table 11.10, Table 11.15

       uint32 Error Code        w2              INVALID_PARAMETER / DENIED / NO_MEMORY /
                                                BUSY / ABORTED *)

    (* 
       1. Check arguments
       2. Read tpidr_el2 to find out the sender 
       3. Read the mailbox to find out the region information.
       4. Read receivers 
       5. validate check
       6. Check mem properties
       7. Update mem properties 
     *)

    (* 
       It is dramatically simplified version. It does the following things. 
       1. check the arguments 
       2. check the arguments with the memory_region descriptor 
          check the memory attributes 
       3.  change the memory attributes
       4. record the value in the buffer to deliver it to the receiver 
       5. return the result
     *)

    (* check arguments
       - Check basic arguments that are given by VMs (by registers
     *)
    Definition ffa_mem_send_check_arguments_spec
               (func_type : FFA_FUNCTION_TYPE) 
               (length fragment_length address page_count: Z)
    : itree HafniumEE (FFA_value_type) :=
      match func_type with
      | FFA_MEM_DONATE 
      | FFA_MEM_LEND 
      | FFA_MEM_SHARE =>
        if decide (address = 0) || decide (page_count = 0) ||
                  decide (length <> fragment_length) ||
                  decide (length >  HF_MAILBOX_SIZE) ||
                  decide (length >  MM_PPOOL_ENTRY_SIZE)
        then Ret (ffa_error FFA_INVALID_PARAMETERS)
        else Ret (init_FFA_value_type)
      (* This case cannot happen if we look at the calling sequence of this spec *)
      | _ => triggerUB "ffa_mem_send_check_arguments: wrong arguments"
      end.

    Definition get_receiver (access_descriptors: list FFA_endpoint_memory_access_descriptor_struct)
      : option FFA_endpoint_memory_access_descriptor_struct :=
      match access_descriptors with
      | hd::nil => Some hd
      | _ => None
      end.

    (* check the given descriptor and return some necessary values for the further process *)
    (* Since Hafnium only uses its RX/TX buffers for memory transitions, it requires several checks 
       by using the given descriptors recorded in RX/TX buffers. The following one also extracts 
       several information from the descriptor. 
     *)
    Definition ffa_mem_send_check_memory_region_descriptor_spec (func_type : FFA_FUNCTION_TYPE)
               (current_vm_id : Z)
      : itree HafniumEE (FFA_value_type * FFA_memory_region_struct *
                         ffa_vm_id_t (* receiver *) * bool (* clear or not-clear *) *
                         FFA_INSTRUCTION_ACCESS_TYPE * FFA_DATA_ACCESS_TYPE (* permission *)) :=
      st <- trigger GetState;; 
      (* Check mailbox and convert it into the region descriptor *)
      do sender_vm_context <- ZTree.get current_vm_id st.(hafnium_context).(vms_contexts);;;
      match mailbox_send_msg_to_region_struct (sender_vm_context.(mailbox).(send)) with 
      | None => Ret (ffa_error FFA_INVALID_PARAMETERS, init_FFA_memory_region_struct, 0, false,
                    FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)
      | Some region_descriptor =>
        (* Check whether we have a proper free memory *) 
        if decide ((st.(hafnium_context).(api_page_pool_size) < FFA_memory_region_struct_size)%Z)
        then Ret (ffa_error FFA_NO_MEMORY, init_FFA_memory_region_struct, 0, false,
                  FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)
        else
          if decide (region_descriptor.(FFA_memory_region_struct_sender) <> current_vm_id) ||
             decide ((length region_descriptor.(FFA_memory_region_struct_receivers) <> 1%nat))
          then Ret (ffa_error FFA_INVALID_PARAMETERS, init_FFA_memory_region_struct, 0, false,
                    FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)                    
          else
            do receiver <-  get_receiver (region_descriptor.(FFA_memory_region_struct_receivers)) ;;;
            let receiver_id := receiver.(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor).(FFA_memory_access_permissions_descriptor_struct_receiver) in
            if in_dec zeq receiver_id vm_ids || decide (current_vm_id <> receiver_id)
            then
              (* check clear flags *)
              let clear_flag := if decide ((Z.land region_descriptor.(FFA_memory_region_struct_flags)
                                                                       FFA_MEMORY_REGION_FLAG_CLEAR_Z) <> 0)
                                then true else false in
              let other_flags := if decide ((Z.land region_descriptor.(FFA_memory_region_struct_flags)
                                                                       (Z_not FFA_MEMORY_REGION_FLAG_CLEAR_Z)) <> 0)
                                then true else false in
              match func_type, clear_flag, other_flags with
              | FFA_MEM_SHARE, true, _ 
              | _, _, true =>
                Ret (ffa_error FFA_INVALID_PARAMETERS, init_FFA_memory_region_struct, 0, false,
                     FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)
              | _, _, _ =>
                (* check instruction permissions *)
                let permissions :=
                    receiver.(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor) in
                let instruction_permissions :=
                    permissions.(FFA_memory_access_permissions_descriptor_struct_permisions_instruction) in
                let data_permissions :=
                    permissions.(FFA_memory_access_permissions_descriptor_struct_permisions_data) in
                match func_type, instruction_permissions, data_permissions with
                (* valid case 
                   - TODO(XXX): It is not actually correct... we need to update the instruction_access 
                   in region_descriptor as FFA_INSTRUCTION_ACCESS_NX *)
                |  FFA_MEM_SHARE,  FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED
                   => Ret (init_FFA_value_type, region_descriptor, receiver_id, clear_flag,
                          FFA_INSTRUCTION_ACCESS_NX, data_permissions)

                |  FFA_MEM_LEND, _, FFA_DATA_ACCESS_NOT_SPECIFIED
                |  FFA_MEM_DONATE, _, FFA_DATA_ACCESS_NOT_SPECIFIED
                   => Ret (ffa_error FFA_INVALID_PARAMETERS, init_FFA_memory_region_struct, 0, false,
                          FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)

                (* valid case *)
                |  FFA_MEM_DONATE, FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, _
                   => Ret (init_FFA_value_type, region_descriptor, receiver_id, clear_flag,
                          instruction_permissions, data_permissions)
                (* valid case *)
                |  FFA_MEM_LEND, FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, _
                   => Ret (init_FFA_value_type, region_descriptor, receiver_id, clear_flag,
                          instruction_permissions, data_permissions)
                | _, _, _ 
                  => Ret (ffa_error FFA_INVALID_PARAMETERS, init_FFA_memory_region_struct, 0, false,
                         FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)
                end
              end
            else Ret (ffa_error FFA_INVALID_PARAMETERS, init_FFA_memory_region_struct, 0, false,
                      FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)
      end.

    (* update memory properties for all addresses in the region descriptor *)             
    Fixpoint update_memory_properties_in_constituent_iter (page_count : nat) (base_address: Z) (attributes: MemProperties)
             (state : AbstractState) : AbstractState :=
      match page_count with
      | O => state {hafnium_context / mem_properties:
                     ZTree.set base_address attributes state.(hafnium_context).(mem_properties)}
      | S n' =>
        let state' := update_memory_properties_in_constituent_iter n' base_address attributes state in
        state' {hafnium_context / mem_properties:
                  ZTree.set ((base_address + (Z.of_nat (S n')) * FFA_PAGE_SIZE)%Z)
                            attributes state.(hafnium_context).(mem_properties)}
      end.
                               
                     
    Definition update_memory_properties_in_constituent (constituent_info: FFA_memory_region_constituent_struct)
               (properties: MemProperties) (state : AbstractState) : AbstractState :=
      match constituent_info with
      | mkFFA_memory_region_constituent_struct base_address page_count
        => update_memory_properties_in_constituent_iter page_count base_address properties state
      end.

    Fixpoint update_memory_properties_in_composite_iter (constituents: list FFA_memory_region_constituent_struct)
               (properties: MemProperties) (state : AbstractState) : AbstractState :=
      match constituents with
      | nil => state
      | hd::tl =>
        let state' := update_memory_properties_in_composite_iter tl properties state in
        update_memory_properties_in_constituent hd properties state'
      end.
        
    Definition update_memory_properties_in_composite (composite_info: FFA_composite_memory_region_struct)
               (properties: MemProperties) (state : AbstractState) : AbstractState :=
      match composite_info with
      | mkFFA_composite_memory_region_struct page_count constituents =>
        update_memory_properties_in_composite_iter constituents properties state
      end.


    Definition find_first_constituent (constituents: list FFA_memory_region_constituent_struct) :=
      match constituents with
      | nil => None
      | hd::tl => Some hd
      end.
    
    (* TODO(XXX): need to modify them *)
    Definition ffa_mem_send_change_mem_spec
               (func_type : FFA_FUNCTION_TYPE)               
               (region_descriptor: FFA_memory_region_struct)
               (receiver_id : ffa_vm_id_t)
               (clear_flag: bool)
               (instruction_access_type: FFA_INSTRUCTION_ACCESS_TYPE)
               (data_access_type: FFA_DATA_ACCESS_TYPE)
      : itree HafniumEE (Z) :=
      (* get the mode of the base address *)
      do receiver <- get_receiver region_descriptor.(FFA_memory_region_struct_receivers) ;;;
      (* TODO(XXX): need to see the consistency of all addresses by checking all properties of all 
         areas *)
      do composite <- receiver.(FFA_memory_access_descriptor_struct_composite_memory_region_offset) ;;;
      do first_constituent <- find_first_constituent 
                               composite.(FFA_composite_memory_region_struct_constituents) ;;;
      let base_address := first_constituent.(FFA_memory_region_constituent_struct_address) in 
      st <- trigger GetState;;
      (* find out the new mode *)      
      do mem_property <- ZTree.get base_address st.(hafnium_context).(mem_properties) ;;;
      match mem_property.(accessible_by) with 
      | NoAccess => triggerUB "wrong access"
      | HasAccess owner others =>
        let new_mem_property := 
            mkMemProperties (mem_property.(owned_by)) (HasAccess owner (others++receiver_id::nil))
                            (instruction_access_type) (data_access_type) (mem_property.(mem_attribute))
                            (if clear_flag then MemClean else mem_property.(mem_dirty)) in
        (* update the memory state *)
        let updated_st := update_memory_properties_in_composite composite new_mem_property st in
        (* update the share state *)
        let new_ffa_memory_share_state :=
            mkFFA_memory_share_state_struct region_descriptor func_type                                 
                                            (ZMap.set 0 (* first receiver *) false (ZMap.init true)) in
        let cur_share_state_index := (updated_st.(hafnium_context).(fresh_index_for_ffa_share_state)) in 
        let updated_st' :=
            updated_st {hafnium_context / ffa_share_state :
                          ZTree.set cur_share_state_index new_ffa_memory_share_state
                                    (updated_st.(hafnium_context).(ffa_share_state))}
                       {hafnium_context / fresh_index_for_ffa_share_state :
                          (cur_share_state_index + 1)%Z} in
        trigger (SetState updated_st');;
        Ret (Z.lor cur_share_state_index FFA_MEMORY_HANDLE_ALLOCATOR_HYPERVISOR_Z)
      end.
      
    Definition ffa_mem_send_deliver_msg_to_receivers (reciever_id handle : Z) 
      : itree HafniumEE (unit) :=
      st <- trigger GetState;;
      (* record the message *)
      (* TODO(XXX): need to modify the following parts to 
         properly create a message and update the mailbox for retrieve *)
      trigger (SetState st);;
      triggerUB "ffa_mem_send_change_memory_attributes_spec: Not implemented yet".
    
    (* Note that we ignored next pointer in our modeling because it is not quite necessary.
       - TODO: figure out the functionality of the "update_vi" function call in "hvc_handler" 
         
    struct ffa_value api_ffa_mem_send(uint32_t share_func, uint32_t length,
            			  uint32_t fragment_length, ipaddr_t address,
            			  uint32_t page_count, struct vcpu *current,
            			  struct vcpu **next)
     *)
    Definition api_ffa_mem_send_spec (func_type:  FFA_FUNCTION_TYPE)
               (length fragment_length address page_count current_vm_id : Z)
      : itree HafniumEE (FFA_value_type) :=
      argument_check_res <- ffa_mem_send_check_arguments_spec func_type length
                                                             fragment_length address page_count ;;
      match argument_check_res.(ffa_type) with
      | FFA_RESULT_CODE_IDENTIFIER FFA_ERROR => Ret (argument_check_res)
      | _ =>
        check_result <- ffa_mem_send_check_memory_region_descriptor_spec func_type current_vm_id ;;
        let '(descriptor_check_res, region_descriptor, receiver_id, clear_flag,
              instruction_access_permissions, data_access_permissions) := check_result in
        match descriptor_check_res.(ffa_type) with 
        |  FFA_RESULT_CODE_IDENTIFIER FFA_ERROR => Ret (descriptor_check_res)
        | _ =>
          handle <- ffa_mem_send_change_mem_spec
                         func_type region_descriptor receiver_id clear_flag
                         instruction_access_permissions data_access_permissions ;;          
          ffa_mem_send_deliver_msg_to_receivers receiver_id handle;;
          Ret (ffa_mem_success handle)
        end
      end.
    
  End FFAMemoryHypCallSend.

  Section FFAMemoryHypCallRetrieve.
  (*
    struct ffa_value api_ffa_mem_retrieve_req(uint32_t length,
           				  uint32_t fragment_length,
           				  ipaddr_t address, uint32_t page_count,
           				  struct vcpu *current)    
   *)
    Definition api_ffa_mem_retrieve_req (length fragment_length address page_count current_vm_id : Z)
      : itree HafniumEE (FFA_value_type) := 
      triggerUB "api_ffa_mem_retrieve_req: Not implemented yet".

  End FFAMemoryHypCallRetrieve.


  Section FFAMemoryHypCallRelinquish.
    (*
    struct ffa_value api_ffa_mem_relinquish(struct vcpu *current)                              
    *) 
    Definition api_ffa_mem_relinquish_spec (current_vm_id : Z)
    : itree HafniumEE (FFA_value_type) :=
      triggerUB "api_ffa_mem_retrieve_req: Not implemented yet".
    
  End FFAMemoryHypCallRelinquish.

  Section FFAMemoryHypCallReclaim.
    (*
    struct ffa_value api_ffa_mem_reclaim(ffa_memory_handle_t handle,
            			     ffa_memory_region_flags_t flags,
            			     struct vcpu *current)    
    *)
    Definition api_ffa_mem_reclaim_spec (handle flags current_vm_id : Z)
    : itree HafniumEE (FFA_value_type) :=
      triggerUB "api_ffa_mem_retrieve_req: Not implemented yet".

  End FFAMemoryHypCallReclaim.

  Section FFADispatch.
  
    Definition ffa_dispatch_spec :  itree HafniumEE (unit) := 
      (* extract the curretnt vcpu *)
      st <- trigger GetState;;
      (* Get the information in tpidr_el2 register to find out the current VM to be served *)
      let vcpu_regs := st.(hafnium_context).(tpidr_el2) in
      match vcpu_regs with
      | Some vcpu_regs' =>
        match vcpu_regs' with
        | mkVCPU_struct (Some cid) (Some vid) vcpu_regs =>
          match vcpu_regs with
          | mkArchRegs (mkFFA_value_type func_type vals) =>
            match func_type with
            | FFA_FUNCTION_IDENTIFIER ffa_function_type =>
              (* Find out the result of the FFA ABI calls by using the proper handling functions *)
              ret_ffa_value <- 
              match ffa_function_type with
              | FFA_MEM_DONATE 
              | FFA_MEM_LEND 
              | FFA_MEM_SHARE
                (* For the above three FFA ABI, call the following functions, and update 
                   the VCPU value for the caller to record the result *)
                (* 
		*args = api_ffa_mem_send(func, args->arg1, args->arg2,
					 ipa_init(args->arg3), args->arg4,
					 current(), next);
                 *)
                => api_ffa_mem_send_spec ffa_function_type (ZMap.get 1 vals) (ZMap.get 2 vals)
                                        (ZMap.get 3 vals) (ZMap.get 4 vals) vid
              | FFA_MEM_RETREIVE_REQ
                (*
		*args = api_ffa_mem_retrieve_req(args->arg1, args->arg2,
						 ipa_init(args->arg3),
						 args->arg4, current());
                 *)
                => api_ffa_mem_retrieve_req (ZMap.get 1 vals) (ZMap.get 2 vals) (ZMap.get 3 vals)
                                           (ZMap.get 4 vals) vid
              | FFA_MEM_RELINQUISH
                (*
		*args = api_ffa_mem_relinquish(current());
                *)
                => api_ffa_mem_relinquish_spec vid
              | FFA_MEM_RECLAIM
                (*
		*args = api_ffa_mem_reclaim(
			ffa_assemble_handle(args->arg1, args->arg2), args->arg3,
			current());                  
                *)
                => api_ffa_mem_reclaim_spec (Z.lor (ZMap.get 1 vals) (Z.shiftl (ZMap.get 2 vals) 32))
                                           (ZMap.get 3 vals) vid
              | FFA_MEM_RETREIVE_RESP
                => triggerUB "ffa_dispatch_spec: not a proper FFA ABI function name 
                  to be called in this level"                            
              end;;
              (* get the updated state after the handling *)
              updated_st <- trigger GetState;;
              do vm_context <- ZTree.get vid updated_st.(hafnium_context).(vms_contexts);;;
              do vcpu_reg <- ZTree.get vm_context.(cur_vcpu_index) vm_context.(vcpus);;;
              let new_vcpu_reg := mkVCPU_struct (vcpu_reg.(cpu_id)) (vcpu_reg.(vm_id))
                                                (mkArchRegs ret_ffa_value) in
              let new_vm_context := 
                  vm_context {vm_vcpus: ZTree.set (vm_context.(cur_vcpu_index))
                                                  new_vcpu_reg 
                                                  vm_context.(vcpus)} in
              let new_st := updated_st {hafnium_context / vms_contexts:
                                  ZTree.set vid new_vm_context
                                            (updated_st.(hafnium_context).(vms_contexts))} in
              trigger (SetState new_st)
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
  
End FFAMemoryHypCall.

