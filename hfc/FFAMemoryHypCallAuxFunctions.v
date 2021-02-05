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

(* FFA Memory management related parts *)
Require Import FFAMemoryHypCallIntro.
Require Export FFAMemoryHypCallDescriptorState.
Require Export FFAMemoryHypCallState.


Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Require Import Maps.
Set Implicit Arguments.

(*************************************************************)
(*         Auxiliary functions                               *)
(*************************************************************)
Section FFAAuxiliaryFunctions.

  Context `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}.
  
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

  Definition ffa_vm_id (args : FFA_value_type) : ffa_UUID_t :=
    Z.land (ZMap.get 1 (args.(vals))) 65535.
    
  
  (*
  static inline ffa_vcpu_index_t ffa_vcpu_index(struct ffa_value args)
  {
          return args.arg1 & 0xffff;
  }
   *)
  Definition ffa_vcpu_index (args : FFA_value_type) : ffa_VCPU_ID_t :=
    Z.land (ZMap.get 1 (args.(vals))) 65535.
    
  (*
  static inline uint64_t ffa_vm_vcpu(ffa_vm_id_t vm_id,
          			   ffa_vcpu_index_t vcpu_index)
  {
          return ((uint32_t)vm_id << 16) | vcpu_index;
  }
   *)
  Definition ffa_vm_vcpu (vm_id : ffa_UUID_t) (vcpu_index : ffa_VCPU_ID_t) : Z :=
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

