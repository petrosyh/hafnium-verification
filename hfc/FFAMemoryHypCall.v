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


    (* 1. Check arguments
       2. Read tpidr_el2 to find out the sender 
       3. Read the mailbox to find out the region information.
       4. Read receivers 
       5. validate check
       6. Check mem properties
       7. Update mem properties 
     *)

    (* It is dramatically simplified version. It does the following things. 
       1. check the arguments 
       2. check the arguments with the memory_region descriptor 
       3. check the memory attributes 
       4. change the memory attributes
       5. record the value in the buffer to deliver it to the receiver 
       5. return the result *)

    Definition ffa_mem_send_check_arguments (st : AbstractState) : option bool := Some true.
    Definition ffa_mem_send_check_arguments_with_memory_region_descriptor
               (st : AbstractState) : bool := true.
    Definition ffa_mem_send_check_memory_attributes (st : AbstractState) : option bool := Some true.
    Definition ffa_mem_send_change_memory_attributes (st : AbstractState) :
      option (AbstractState * bool) :=
      Some (st, true).
    Definition ffa_mem_send_deliver_msg_to_receivers (st : AbstractState) :
      option (AbstractState * bool) :=
      Some (st, true).
    
    Definition api_ffa_mem_send_spec  : itree HafniumEE (FFA_value_type) := 
      st <- trigger GetState;;
      Ret (mkFFA_value_type FFA_IDENTIFIER_DEFAULT (ZMap.init 0)).
    
  End FFAMemoryHypCallSend.


  Section FFAMemoryHypCallRetrieve.

  End FFAMemoryHypCallRetrieve.


  Section FFAMemoryHypCallRelingquish.

  End FFAMemoryHypCallRelingquish.


  Section FFAMemoryHypCallReclaim.

  End FFAMemoryHypCallReclaim.


  Section FFADispatch.
  
    Definition ffa_dispatch_spec :  itree HafniumEE (unit) := 
      st <- trigger GetState;;
      (* extract the curretnt vcpu *)
      let vcpu_regs := st.(hafnium_context).(tpidr_el2) in
      match vcpu_regs with
      | Some vcpu_regs' =>
        match vcpu_regs' with
        | mkVCPU_struct (Some cid) (Some vid) vcpu_regs =>
          match vcpu_regs with
          | mkArchRegs (mkFFA_value_type func_type vals) =>
            match func_type with
            | FFA_FUNCTION_IDENTIFIER ffa_function_type =>
              match ffa_function_type with
              | FFA_MEM_DONATE 
              | FFA_MEM_LEND 
              | FFA_MEM_SHARE
                (* update vm_id's context to record the result *)
                => ret_ffa_value <- api_ffa_mem_send_spec;;
                  do vm_context <- ZTree.get vid st.(hafnium_context).(vms_contexts);;;
                  do vcpu_reg <- ZTree.get vm_context.(cur_vcpu_index) vm_context.(vcpus);;;
                  let new_vcpu_reg := mkVCPU_struct (vcpu_reg.(cpu_id)) (vcpu_reg.(vm_id))
                                                    (mkArchRegs ret_ffa_value) in
                  let new_vm_context := 
                      vm_context {vm_vcpus: ZTree.set (vm_context.(cur_vcpu_index))
                                                      new_vcpu_reg 
                                                      vm_context.(vcpus)} in
                  let new_st := st {hafnium_context / vms_contexts:
                                      ZTree.set vid new_vm_context
                                                (st.(hafnium_context).(vms_contexts))} in
                  trigger (SetState st)
              | FFA_MEM_RELINQUISH
              | FFA_MEM_RETREIVE_REQ
              | FFA_MEM_RETREIVE_RESP
              | FFA_MEM_RELINGQUISH
              | FFA_MEM_RECLAIM             
                => triggerUB "ffa_dispatch_spec: not implemented yet"
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
  
End FFAMemoryHypCall.
