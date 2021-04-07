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

Require Import HexString.

(* From HafniumCore *)
Require Import Any.
Require Import Lang.
Require Import Values.
Require Import Integers.
Require Import Constant.
Require Import Decision.

(* FFA Memory management related parts *)
Require Export FFAMemoryHypCall.
Require Export FFAMemoryHypCallIntro.
Require Export FFAMemoryHypCallDescriptorState.
Require Export FFAMemoryHypCallState.
Require Export FFAMemoryHypCallCoreTransition.
Require Export FFAMemoryHypCallAdditionalStepsAuxiliaryFunctions.
Require Export FFAMemoryHypCallAdditionalSteps.


Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Require Import Maps.
Set Implicit Arguments.

Definition Z_64MAX := ((Z.pow 2 64) - 1)%Z.
Definition Z_not := fun val => (Z.lxor Z_64MAX val).

(*************************************************************)
(** *                Introduction                            *) 
(*************************************************************)

(** This file contains definitions that are necessary for providing testing interfaces. 
    They are usually contains Z type (or integer type) values that are relevant to several 
    inductive type values in other files. 
*)

Notation "'do' X <- A ;;; B" :=
  (match A with Some X => B |
           None => triggerUB "None" end)
    (at level 200, X ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation "'do' X , Y <- A ;;; B" :=
  (match A with Some (X, Y) => B |
           None => triggerUB "None" end)
    (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation "'do' X , Y , Z <- A ;;; B" :=
  (match A with Some (X, Y, Z) => B | None => triggerUB "None" end)
    (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation " 'check' A ;;; B" :=
  (if A then B else Ret None)
    (at level 200, A at level 100, B at level 200)
  : itree_monad_scope.
 
Local Open Scope itree_monad_scope.

(***********************************************************************)
(** *                 Instantiations for contexts                      *)
(***********************************************************************)
(** We provides instantiations for the context that our specifiction
    relies on. *)

(***********************************************************************)
(** **            FFA_TYPES_AND_CONSTANTS instance                     *)
(***********************************************************************)
Definition ffa_memory_region_tag_t := Z.

(** This is the valule that we have to use. 
    However, due to the stack overflow in the recursion, 
    we reduce the number as 4. *)
(*
Definition granuale_shift := 12.
*)

Definition granuale_shift := 1.

Global Instance ffa_types_and_constants : FFA_TYPES_AND_CONSTANTS :=
  {
  ffa_memory_region_tag_t := ffa_memory_region_tag_t;
  (** - The following two types are for message passings. We use them to record and 
        retrieve descriptor information *)

  (** - Granuale value. It is usually a multiplication of 4096 (4KiB) *)
  granuale := Z.shiftl 1 granuale_shift;
  init_ffa_memory_region_tag := 0;
  }.

(***********************************************************************)
(** **                  DescriptorContext instance                     *)
(***********************************************************************)
Global Instance descriptor_context :
  DescriptorContext (ffa_types_and_constants := ffa_types_and_constants) :=
  {
  (** Commented out the more realistic version and provided
      simplified (with the small number) version to avoid buffer
      overflow 
  make_handle := fun vid value =>
                   if decide (0 <= vid < (Z.shiftl 1 16))
                   then if decide (0 <= value < (Z.shiftl 1 16))
                        then Some (Z.lor (Z.shiftl vid 16) value)
                        else None
                   else None;
  get_value := fun handle =>
                 let mask := ((Z.shiftl 1 16) - 1)%Z in
                 Z.land mask handle;
  get_sender := fun handle =>
                  Z.shiftr handle 16;
   *)
  make_handle := fun vid value =>
                   if decide (0 <= vid < (Z.shiftl 1 4))
                   then if decide (0 <= value < (Z.shiftl 1 4))
                        then Some (Z.lor (Z.shiftl vid 4) value)
                        else None
                   else None;
  get_value := fun handle =>
                 let mask := ((Z.shiftl 1 4) - 1)%Z in
                 Z.land mask handle;
  get_sender := fun handle =>
                  Z.shiftr handle 4;  
  }.


(***********************************************************************)
(** **                  FFA_VM_CONTEXT instance                        *)
(***********************************************************************)
Inductive ffa_mailbox_msg_t : Type :=
| mailbox_memory_init_value
| mailbox_memory_region (region_descriptor: FFA_memory_region_struct)
| mailbox_memory_relinquish (relinquish_descriptor: FFA_memory_relinquish_struct)
| mailbox_z (value : Z).

Definition init_ffa_mailbox_msg := mailbox_memory_init_value.
Definition vcpu_max_num := 2.

Definition mailbox_msg_to_region_struct :=
  fun x =>
    match x with
    | mailbox_memory_region region_descriptor =>
      Some region_descriptor
    | _ => None
    end.

Definition mailbox_msg_to_relinquish_struct :=
  fun x =>
    match x with
    | mailbox_memory_relinquish relinquish_descriptor =>
      Some relinquish_descriptor
    | _ => None
    end.

Definition mailbox_msg_to_z :=
  fun x =>
    match x with
    | mailbox_z value =>
      Some value
    | _ => None
    end.

Definition region_struct_to_mailbox_msg :=
  fun x => Some (mailbox_memory_region x).

Definition relinquish_struct_to_mailbox_msg :=
  fun x => Some (mailbox_memory_relinquish x).

Definition z_to_mailbox_msg := 
  fun x => Some (mailbox_z x).

Global Instance ffa_vm_context :
  FFA_VM_CONTEXT (ffa_types_and_constants := ffa_types_and_constants)  :=
    {
    (** - The following two types are for message passings. We use them to record and 
        retrieve descriptor information *)
    ffa_mailbox_send_msg_t := ffa_mailbox_msg_t;
    ffa_mailbox_recv_msg_t := ffa_mailbox_msg_t;
    init_ffa_mailbox_send_msg := init_ffa_mailbox_msg;
    init_ffa_mailbox_recv_msg := init_ffa_mailbox_msg;

    vcpu_max_num := vcpu_max_num;

    (** mailbox to/from descriptors *)
    mailbox_send_msg_to_region_struct := mailbox_msg_to_region_struct;
    mailbox_send_msg_to_relinqiush_struct := mailbox_msg_to_relinquish_struct;
    mailbox_send_msg_to_Z := mailbox_msg_to_z;
    region_struct_to_mailbox_send_msg := region_struct_to_mailbox_msg;
    relinqiush_struct_to_mailbox_send_msg := relinquish_struct_to_mailbox_msg;
    Z_to_mailbox_send_msg := z_to_mailbox_msg;

    mailbox_recv_msg_to_region_struct := mailbox_msg_to_region_struct;
    mailbox_recv_msg_to_relinqiush_struct := mailbox_msg_to_relinquish_struct;
    mailbox_recv_msg_to_Z := mailbox_msg_to_z;
    region_struct_to_mailbox_recv_msg := region_struct_to_mailbox_msg;
    relinqiush_struct_to_mailbox_recv_msg := relinquish_struct_to_mailbox_msg;
    Z_to_mailbox_recv_msg := z_to_mailbox_msg;

    primary_vm_id := 1;
    secondary_vm_ids := 2::nil;

    (* TODO: Need to fix *)
    FFA_memory_region_struct_size := fun x => 1;
    }.
    
(** TODO: The following values are dummy representations. We have to provide 
    proper values later if we want to connect this one with the real Hafnium / other 
    hypervisor implementations *)

(***********************************************************************)
(** **       HafniumMemoryManagementContext instance                   *)
(***********************************************************************)

(** Commented out the realistic version and provide the simplified (with small numbers)
    version 
Definition address_low_shift := 30.
Definition address_high_shift := 32.
*)
Definition page_low_shift := 0.
Definition page_high_shift := 4.

Global Instance memory_management_basic_context
  : MemoryManagementBasicContext
      (ffa_vm_context := ffa_vm_context) :=
  {
  page_low := (Z.shiftl 1 page_low_shift)%Z;
  page_high := (Z.shiftl 1 page_high_shift)%Z;
  alignment_value := granuale;
  }.
 
Definition stage2_address_translation_table :=
  fun (x : ffa_address_t) =>
    if decide ((page_low * granuale) <= x)%Z && decide (x < (page_high * granuale))%Z
    then Some x else None.

Definition stage1_address_translation_table :=
  fun (vid : ffa_UUID_t) (x : ffa_address_t) =>
    if decide (0 <= vid)%Z && decide (vid < number_of_vm)%Z
    then if decide ((page_low * granuale) <= x)%Z &&
            decide (x < (page_high * granuale))%Z
         then Some x
         else None
    else None.  

Global Instance memory_management_context
  : MemoryManagementContext
      (memory_management_basic_context
         := memory_management_basic_context) :=
  {
  stage2_address_translation_table :=
    stage2_address_translation_table;
  stage1_address_translation_table :=
    stage1_address_translation_table;
  }.

(***********************************************************************)
(** **                 AbstractStateContext instance                   *)
(***********************************************************************)

Definition init_cpu_id := 0.
Definition num_of_cpus := 4.

Definition init_CPU_struct := mkCPU_struct.

Fixpoint cal_init_cpus (cpu_nums : nat) :=
  match cpu_nums with
  | O =>  (ZTree.empty CPU_struct)
  | S n' =>
    let res :=  cal_init_cpus n' in
    ZTree.set (Z.of_nat cpu_nums) 
              init_CPU_struct res
  end.

Definition init_cpus := cal_init_cpus (Z.to_nat num_of_cpus).

Definition init_api_page_pool_size_shift := 4.

Definition init_mem_global_properties :=
  mkMemGlobalProperties
    false
    NotOwned
    NoAccess 
    FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED
    FFA_DATA_ACCESS_NOT_SPECIFIED
    FFA_MEMORY_NOT_SPECIFIED_MEM
    MemClean.
    
Fixpoint cal_init_global_properties_pool
         (address : nat)  :=
  match address with 
  | O => if decide (0 >= page_low)
        then ZTree.set (Z.shiftl 0 granuale_shift)  
                       init_mem_global_properties
                       (ZTree.empty MemGlobalProperties)
        else (ZTree.empty MemGlobalProperties)
  | S n' =>
    let converted_addr := Z.shiftl (Z.of_nat address) granuale_shift in
    if decide (converted_addr >= page_low)
    then let res := cal_init_global_properties_pool n' in
         ZTree.set converted_addr  
                   init_mem_global_properties
                   res
    else (ZTree.empty MemGlobalProperties)
  end.         
  
Definition init_mem_global_properties_pool
  : mem_global_properties_pool
  := cal_init_global_properties_pool
       (Z.to_nat page_high).

Fixpoint cal_init_local_properties_pool
         (vms : list Z) :=
  match vms with 
  | nil => (ZTree.empty
             (ZTree.t MemLocalProperties))
  | hd::tl =>
    let res := cal_init_local_properties_pool tl in
    ZTree.set hd (ZTree.empty MemLocalProperties) res
  end.         

Definition init_mem_local_properties_global_pool 
  : mem_local_properties_global_pool
  :=  cal_init_local_properties_pool vm_ids.

Definition init_mem_properties :=
  mkMemProperties
    init_mem_global_properties_pool
    init_mem_local_properties_global_pool.

Definition init_VM_COMMON_struct (vcpu_ids: list Z) 
  := mkVM_COMMON_struct
       None
       vcpu_ids 
       (ZTree.empty VCPU_struct).

Definition init_MAILBOX_struct :=
  mkMAILBOX_struct
    init_ffa_mailbox_msg
    init_ffa_mailbox_msg
    None (* recv_sender *)
    0 (* recv_size *)
    None (* recv func *)
.

Definition init_VM_KERNEL_context (vcpu_ids: list Z) :=
 mkVM_KERNEL_struct 
   (init_VM_COMMON_struct vcpu_ids)
   init_MAILBOX_struct.

Fixpoint cal_init_VM_KERNEL_contexts (vm_ids: list Z) := 
  match vm_ids with
  | nil =>  (ZTree.empty VM_KERNEL_struct)
  | hd::tl =>
    let res :=  cal_init_VM_KERNEL_contexts tl in
    ZTree.set hd (init_VM_KERNEL_context (hd::nil)) res
  end.

Definition init_VM_KERNEL_contexts :=
  cal_init_VM_KERNEL_contexts vm_ids.

Fixpoint cal_init_VM_USERSPACE_contexts (vm_ids: list Z) :=
  match vm_ids with
  | nil =>  (ZTree.empty VM_USERSPACE_struct)
  | hd::tl =>
    let res :=  cal_init_VM_USERSPACE_contexts tl in
    ZTree.set hd (mkVM_USERSPACE_struct (init_VM_COMMON_struct (hd::nil))) res
  end.

Definition init_VM_USERSPACE_contexts :=
  cal_init_VM_USERSPACE_contexts vm_ids.

Definition init_hypervisor_struct :=
  mkHypervisor_struct
    init_cpu_id
    num_of_cpus
    init_cpus
    false (* time slice enabled *)
    None (* tpidr_el2 *)
    (Z.shiftl 1 init_api_page_pool_size_shift) (* api_page_pool_size *)
    (ZTree.empty FFA_memory_share_state_struct) (* ffa_share_state *)
    0 (* fresh_index_for_ffa_share_state *)
    init_mem_properties (* mem_properties *)
    number_of_vm  (* vm_count *)
    init_VM_KERNEL_contexts.

(* TODO: it is a dummy value *)
Definition version_number := (1, 1).

Definition init_abstract_state :=
  mkAbstractState
    (1, 1) (* dummy version number *)
    false (* is_hvc_mode *)
    false (* use_stage1_table *)
    1 (*  cur_entity_id - primary VM *)
    init_hypervisor_struct
    init_VM_USERSPACE_contexts
    nil (* system_log *)
.    

Fixpoint find_next_entity (vm_ids : list ffa_UUID_t)
         (current_entity_id : ffa_UUID_t) :=
  match vm_ids with
  | nil => primary_vm_id
  | hd::tl =>
    if decide (current_entity_id = hd)
    then match tl with
         | nil => primary_vm_id
         | hd'::_ => hd'
         end
    else find_next_entity tl current_entity_id
  end.

Definition scheduler (st: AbstractState) : ffa_UUID_t :=
  let cur_entity_id := st.(cur_user_entity_id) in
  find_next_entity vm_ids cur_entity_id.  

Global Instance abstract_state_context :
  AbstractStateContext
    (ffa_types_and_constants := ffa_types_and_constants)
    (descriptor_context := descriptor_context)
    (ffa_vm_context := ffa_vm_context)
    (memory_management_basic_context
       := memory_management_basic_context)
    (memory_management_context
       := memory_management_context) :=
  {
      scheduler := scheduler;
      initial_state := init_abstract_state;
  }.

(***********************************************************************)
(** *                 Showable function for the log                    *)
(***********************************************************************)
Fixpoint append_all (cls: list string) :=
  match cls with
  | nil => ""
  | hd::tl =>
    let res := append_all tl in
    append hd res
  end.

Fixpoint list_z_to_string (vals : list Z) :=
  match vals with
  | nil => ""
  | hd::nil =>
    HexString.of_Z hd
  | hd::tl =>
    append_all [HexString.of_Z hd; ", "; list_z_to_string tl]
  end.

Fixpoint print_vals (position : nat) (vals :ZMap.t Z) :=
  let print_val_fun :=
      fun (x : nat) =>
        append_all ["["; HexString.of_Z (Z.of_nat position); ": ";
                   HexString.of_Z (ZMap.get (Z.of_nat position) vals); "]"] in
  match position with
  | O => print_val_fun position
  | S position' =>
    let res := print_vals position' vals in
    append (print_val_fun position) res
  end.

Definition print_ffa_vals (vals :ZMap.t Z) :=
  print_vals 7 vals.

Definition FFA_value_type_to_string (ffa_value: FFA_value_type) :=
  match ffa_value with
  | mkFFA_value_type ffa_type vals =>
    let ffa_value_string :=
        match ffa_type with
        | FFA_IDENTIFIER_DEFAULT => "FFA Identifier Default"
        | FFA_FUNCTION_IDENTIFIER function_name =>
          let function_name_string :=
              match function_name with
              | FFA_MEM_DONATE => " FFA_MEM_DONATE "
              | FFA_MEM_LEND => " FFA_MEM_LEND "
              | FFA_MEM_SHARE => " FFA_MEM_SHARE "
              | FFA_MEM_RETREIVE_REQ => " FFA_MEM_RETRIEVE_REQ "
              | FFA_MEM_RETREIVE_RESP => " FFA_MEM_RETRIEVE_RESP "
              | FFA_MEM_RELINQUISH => " FFA_MEM_RELINQUISH "
              | FFA_MEM_RECLAIM => " FFA_MEM_RECLAIM "
              end in
          (append "FFA_FUNCTION_IDENTIFIER " function_name_string)
        | FFA_RESULT_CODE_IDENTIFIER result_name =>
          match result_name with
          | FFA_ERROR error_type =>
            match error_type with
            | FFA_NOT_SUPPORTED => " FFA_NOT_SUPPROTED"
            | FFA_INVALID_PARAMETERS => " FFA_INVALID_PARAMETERS " 
            | FFA_NO_MEMORY => " FFA_NO_MEMORY "
            | FFA_BUSY => " FFA_BUSY "
            | FFA_INTERRUPTED => " FFA_INTERRUPTED " 
            | FFA_DENIED => " FFA_DENIED "
            | FFA_RETRY => " FFA_RETRY "
            | FFA_ABORTED => " FFA_ABORTED " 
            end
          | FFA_SUCCESS value =>
            (append_all [" FFA_SUCCESS (" ; HexString.of_Z value; ") "])
          end
        end in
    append ffa_value_string (print_ffa_vals vals)
  end.

Definition onwership_state_type_to_string
           (ownership_state_type : OWNERSHIP_STATE_TYPE) :=
  match ownership_state_type with
  | Owned id => append_all ["(Owned by "; HexString.of_Z id; ")"]
  | NotOwned => "(Not Owned)"
  end.

Definition access_state_type_to_string 
           (access_state_type : ACCESS_STATE_TYPE) :=
  match access_state_type with
  | NoAccess => "(NoAccess)"
  | ExclusiveAccess accessor
    => append_all ["(ExclusiveAccess "; HexString.of_Z accessor; ")"]
  | SharedAccess accessors
    => append_all ["(ExclusiveAccess "; list_z_to_string accessors; ")"]
  end.

Definition mem_dirty_type_to_string 
           (mem_dirty_type :  MEM_DIRTY_TYPE) :=
  match mem_dirty_type with
  | MemClean => "(MemClean)"
  | MemWritten writers
    => append_all ["(MemWritten "; list_z_to_string writers; ")"]
  end.

Definition ffa_instruction_access_type_to_string
           (ffa_instruction_access_type : FFA_INSTRUCTION_ACCESS_TYPE) :=
  match ffa_instruction_access_type with
  | FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED => "ACCESS_NOT_SPECIFIED" 
  | FFA_INSTRUCTION_ACCESS_NX => "ACCESS_NX"
  | FFA_INSTRUCTION_ACCESS_X => "ACCESS_X"
  | FFA_INSTRUCTION_ACCESS_RESERVED => "ACCESS_RESERVED"
  end.

Definition ffa_data_access_type_to_string 
           (ffa_data_access_type: FFA_DATA_ACCESS_TYPE) :=
  match ffa_data_access_type with 
  | FFA_DATA_ACCESS_NOT_SPECIFIED => "ACCESS_NOT_SPECIFIED"
  | FFA_DATA_ACCESS_RO => "ACCESS_RO"
  | FFA_DATA_ACCESS_RW => "ACCESS_RW"
  | FFA_DATA_ACCESS_RESERVED => "ACCESS_RESERVED"
  end.

Definition ffa_memory_type_to_string
           (ffa_memory_type: FFA_MEMORY_TYPE) :=
  match ffa_memory_type with
  | FFA_MEMORY_NOT_SPECIFIED_MEM => "NOT_SPECIFIED_MEM"
  | FFA_MEMORY_DEVICE_MEM cacheability_type
    => let ctype_string := match cacheability_type with
                   | FFA_MEMORY_DEV_NGNRNE => "nGnRnE"
                   | FFA_MEMORY_DEV_NGNRE => "nGnRE"
                   | FFA_MEMORY_DEV_NGRE => "nGRE"
                   | FFA_MEMORY_DEV_GRE => "GRE"
                   end in
      append_all  ["DEVICE_MEM"; " "; ctype_string]
  | FFA_MEMORY_NORMAL_MEM cacheability_type shareability_type
    => let ctype_string := match cacheability_type with
                          | FFA_MEMORY_CACHE_RESERVED => "RESERVED"
                          | FFA_MEMORY_CACHE_NON_CACHEABLE => "CACHEABLE"
                          | FFA_MEMORY_CACHE_RESERVED_1 => "RESERVED_ONE" 
                          | FFA_MEMORY_CACHE_WRITE_BACK => "WRITE_BACK"
                          end  in
      let stype_string := match shareability_type with
                          | FFA_MEMORY_SHARE_NON_SHAREABLE => "SHAREABLE"
                          | FFA_MEMORY_SHARE_RESERVED => "RESERVED"
                          | FFA_MEMORY_OUTER_SHAREABLE => "OUTER_SHAREABLE"
                          | FFA_MEMORY_INNER_SHAREABLE => "INNER_SHAREABLE"
                          end in
      append_all  ["NORMAL_MEM"; " "; ctype_string; " "; stype_string]
  | FFA_MEMORY_MEM_RESERVED => "RESERVED"
  end.

(* TODO: need to add more things *)
Definition print_mailbox_msg (mailbox : MAILBOX_struct) :=
  "omitted at this moment".

Definition system_log_entity_showable (log_entity : log_type) :=
  match log_entity with
  | ChangeCurEntityID from_id to_id
    => append_all ["(change from "; HexString.of_Z from_id; " ";
                 HexString.of_Z to_id; ")\n"]
  | UserToKernel vid vcpu_id reg_vals
    => append_all ["(From User to Kernel:\n";
                 "    vm id: "; HexString.of_Z vid; "\n";
                 "    vcpu id: "; HexString.of_Z vcpu_id; "\n";
                 "    reg_vals: "; FFA_value_type_to_string reg_vals.(regs); ")\n"]
  | KernelToUser vid vcpu_id reg_vals
    => append_all ["(From Kernel to User:\n";
                 "    vm id: "; HexString.of_Z vid; "\n";
                 "    vcpu id: "; HexString.of_Z vcpu_id; "\n";
                 "    reg_vals: "; FFA_value_type_to_string reg_vals.(regs); ")\n"]
  | DispathFFAInterface reg_vals
    => append_all ["(Dispatch hyp call:\n";
                 "    reg_vals: "; FFA_value_type_to_string reg_vals.(regs); ")\n"]
  | SetOwner entity_id address owner 
    => append_all ["(SetOwner:\n";
                 "    vm_id: "; HexString.of_Z entity_id; "\n";
                 "    address: "; HexString.of_Z address; "\n";
                 "    onwership: "; onwership_state_type_to_string owner; ")\n"]
                 
  | SetAccessible vm_id address access
    => append_all ["(SetAccessibility:\n";
                 "    vm_id: "; HexString.of_Z vm_id; "\n";
                 "    address: "; HexString.of_Z address; "\n";
                 "    access: "; access_state_type_to_string access; ")\n"]

  | SetInstructionAccess vm_id address access
    => append_all ["(SetInstructionAccess:\n";
                 "    vm_id: "; HexString.of_Z vm_id; "\n";
                 "    address: "; HexString.of_Z address; "\n";
                 "    access: "; ffa_instruction_access_type_to_string access; ")\n"]

  | SetDataAccess vm_id address access
    => append_all ["(SetDataAccess:\n";
                 "    vm_id: "; HexString.of_Z vm_id; "\n";
                 "    address: "; HexString.of_Z address; "\n";
                 "    access: "; ffa_data_access_type_to_string access; ")\n"]

  | SetDirty vm_id address dirty
    => append_all ["(SetDirty:\n";
                 "    vm_id: "; HexString.of_Z vm_id; "\n";
                 "    address: "; HexString.of_Z address; "\n";
                 "    dirty: "; mem_dirty_type_to_string dirty; ")\n"]

  | SetAttributes vm_id address attributes
    => append_all ["(SetAttributes:\n";
                 "    vm_id: "; HexString.of_Z vm_id; "\n";
                 "    address: "; HexString.of_Z address; "\n";
                 "    attributes: "; ffa_memory_type_to_string attributes; ")\n"]

  | SendMsg sender receiver msg
    => append_all ["(SendMsg:\n";
                 "    sender: "; HexString.of_Z sender; "\n";
                 "    receiver: "; HexString.of_Z receiver; "\n";
                 "    msg: "; print_mailbox_msg msg; ")\n"]

  | RecvMsg receiver msg 
    => append_all ["(RecvMsg:\n";
                 "    receiver: "; HexString.of_Z receiver; "\n";
                 "    msg: "; print_mailbox_msg msg; ")\n"]
  end.
                  
Fixpoint system_log_showable (system_log: list log_type) :=
  match system_log with
  | nil => " "
  | hd::tl =>
    append (system_log_entity_showable hd)
           (system_log_showable tl)
  end.

Definition abstract_state_showable (st : AbstractState) : string :=
  system_log_showable st.(system_log).

Instance abstract_state_Showable:
  Showable AbstractState := { show := abstract_state_showable }.

(***********************************************************************)
(** *      Additional  Specifications for testing                      *)
(***********************************************************************)
(***********************************************************************)
(** **           Event and Update functions                            *)
(***********************************************************************)

Inductive updateStateE: Type -> Type :=
| GetState : updateStateE (AbstractState)
| SetState (st1: AbstractState): updateStateE unit.

Definition updateState_handler {E: Type -> Type}
  : updateStateE ~> stateT (AbstractState) (itree E) :=
  fun _ e st =>
    match e with
    | GetState => Ret (st, st)
    | SetState st' => Ret (st', tt)
    end.


Notation HypervisorEE := (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).

(***********************************************************************)
(** **                Context switching                                *)
(***********************************************************************)
Section FFAContextSwitching.

  (**
     [JIEUNG:We referred context switchigns in Hafnium, but we believe it could be similar when 
     we provide abstract models for different implementations]
     
     In Hafnium, most parts are related to save registers in "/src/arch/aarch64/hypervisor/exceptions.S"
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
  (** Save contexts *)    
  Definition save_regs_to_vcpu_spec  :
    itree HypervisorEE (unit) := 
    st <- trigger GetState;;
    (* check whether the current running entity is one of VMs *)
    if decide (st.(is_hvc_mode) = true) &&
       in_dec zeq st.(cur_user_entity_id) vm_ids
    then (* get contexts for the currently running entity ID *)
      do vm_userspace <- ZTree.get st.(cur_user_entity_id) st.(vms_userspaces) ;;;
      do cur_vcpu_index <- (vm_userspace.(vm_userspace_context).(cur_vcpu_index)) ;;;
      do cur_vcpu_regs <- ZTree.get cur_vcpu_index 
                                   (vm_userspace.(vm_userspace_context).(vcpus_contexts)) ;;;
                                                                         
      (* get vm contexts in Hanfium to save the userspace information in it *)              
      do vm_context <- ZTree.get st.(cur_user_entity_id) st.(hypervisor_context).(vms_contexts) ;;;
      if decide (list_eq_dec zeq (vm_context.(vm_kernelspace_context).(vcpus)) 
                             (vm_userspace.(vm_userspace_context).(vcpus))) &&
         decide (cur_vcpu_regs.(vm_id) = Some st.(cur_user_entity_id))
      then
        let new_vm_context :=
            vm_context {vm_cur_vcpu_index: Some cur_vcpu_index}
                       {vm_vcpus_contexts:
                          ZTree.set cur_vcpu_index cur_vcpu_regs
                                    vm_context.(vm_kernelspace_context).(vcpus_contexts)} in
        let new_vms_contexts :=
            ZTree.set st.(cur_user_entity_id)
                           new_vm_context
                           st.(hypervisor_context).(vms_contexts) in
        let new_st := st {is_hvc_mode: true}
                         {hypervisor_context/tpidr_el2: Some cur_vcpu_regs}
                         {hypervisor_context/vms_contexts: new_vms_contexts}
                         {system_log : st.(system_log)
                                            ++(UserToKernel (st.(cur_user_entity_id))
                                                            cur_vcpu_index
                                                            cur_vcpu_regs.(vcpu_regs)::nil)} in
                                                                     
        trigger (SetState new_st)
      else triggerUB "save_resg_to_vcpu_spec: inconsistency in total vcpu number"
    else triggerUB "save_resg_to_vcpu_spec: wrong cur entity id".

  Definition save_regs_to_vcpu_call (args : list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val)  :=
    match args with
    | nil => save_regs_to_vcpu_spec;;
            Ret (Vnull, args)
    | _ => triggerUB "save_regs_to_vcpu_call: wrong arguments"
    end.
  
  (** Restore contexts and run.
     It also contains choosing the next vm to run by using an abstract scheduler  
   *)
  Definition vcpu_restore_and_run_spec  :
    itree HypervisorEE (unit) := 
    st <- trigger GetState;;
    (** find out the next vm to be scheduled *)
    (** - Since we do not have any scheduler implementations, we introduced abstract scheduler *)
    let next_vm_id := scheduler st in
    (** check whether the current running entity is Hafnium *)
    if decide (st.(is_hvc_mode) = true) && in_dec zeq next_vm_id vm_ids
    then
      (** get the userspace information *)
      do vm_userspace <- ZTree.get next_vm_id st.(vms_userspaces) ;;;
      (** get vm context to restore the userspace information *)
      do vm_context <- ZTree.get next_vm_id st.(hypervisor_context).(vms_contexts) ;;;
      (** get vcpu register information *)
      do cur_kernel_vcpu_index <- (vm_context.(vm_kernelspace_context).(cur_vcpu_index)) ;;;
      do cur_user_vcpu_index <- (vm_userspace.(vm_userspace_context).(cur_vcpu_index)) ;;;
      do cur_vcpu_regs <- ZTree.get cur_kernel_vcpu_index
                               (vm_context.(vm_kernelspace_context).(vcpus_contexts)) ;;;
         if decide (list_eq_dec zeq (vm_context.(vm_kernelspace_context).(vcpus))
                                vm_userspace.(vm_userspace_context).(vcpus)) &&
            decide (cur_kernel_vcpu_index = cur_user_vcpu_index) &&
            decide (cur_vcpu_regs.(vm_id) = Some next_vm_id)
            (* TODO: add cpu connection check with vcpu_regs later *)
         then
           let new_vm_userspace := 
               vm_userspace
                 {client_vcpus_contexts :
                    (ZTree.set cur_kernel_vcpu_index
                               cur_vcpu_regs
                               (vm_userspace.(vm_userspace_context).(vcpus_contexts)))} in
           let new_vms_userspaces :=
               ZTree.set next_vm_id new_vm_userspace st.(vms_userspaces) in
           let new_st := st {is_hvc_mode: false}
                            {cur_user_entity_id: next_vm_id}
                            {hypervisor_context/tpidr_el2: None}
                            {vms_userspaces: new_vms_userspaces}
                            {system_log : st.(system_log)
                                               ++(ChangeCurEntityID
                                                    st.(cur_user_entity_id)
                                                         next_vm_id)
                                               ::(KernelToUser next_vm_id
                                                               cur_user_vcpu_index
                                                               cur_vcpu_regs.(vcpu_regs))::nil} in
           trigger (SetState new_st)
         else triggerUB "vcpu_restore_and_run__spec: inconsistency in vcpu number"
    else triggerUB "vcpu_restore_and_run__spec: wrong cur entity id".

  Definition vcpu_restore_and_run_call (args : list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val)  :=             
    match args with
    | nil => vcpu_restore_and_run_spec;;
            Ret (Vnull, args)
    | _ => triggerUB "vcpu_restore_and_run_call: wrong arguments"
    end.
  
End FFAContextSwitching.

(***********************************************************************)
(** **                       FFA Dispatch                              *)
(***********************************************************************)
Section FFADispatch.  
   
  Notation HypervisorEE := (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).

  Definition function_dispatcher
             (ffa_function_type: FFA_FUNCTION_TYPE)
             (vid: ffa_UUID_t)
             (vals: ZMap.t Z) (st : AbstractState) :=
    match ffa_function_type with
    | FFA_MEM_DONATE 
      => ffa_mem_donate_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                            (ZMap.get 3 vals) (ZMap.get 4 vals) st
    | FFA_MEM_LEND
      => ffa_mem_lend_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                          (ZMap.get 3 vals) (ZMap.get 4 vals) st
    | FFA_MEM_SHARE
      => ffa_mem_share_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                           (ZMap.get 3 vals) (ZMap.get 4 vals) st
    | FFA_MEM_RETREIVE_REQ
      => ffa_mem_retrieve_req_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                                  (ZMap.get 3 vals) (ZMap.get 4 vals) st
    | FFA_MEM_RETREIVE_RESP
      => ffa_mem_retrieve_resp_spec vid (ZMap.get 1 vals)
                                   (ZMap.get 2 vals) st
    | FFA_MEM_RELINQUISH 
      => ffa_mem_relinquish_spec vid st
    | FFA_MEM_RECLAIM
      => ffa_mem_reclaim_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                             (ZMap.get 3 vals) st
    end.

  (** In Hafnium: Defined in "inc/hf/ffa_internal.h" *)
  Definition ffa_error (ffa_error_code: FFA_ERROR_CODE_TYPE) : FFA_value_type :=
    let error_z_value := 
        match ffa_error_code with
        | FFA_NOT_SUPPORTED => -1
        | FFA_INVALID_PARAMETERS => -2 
        | FFA_NO_MEMORY => -3
        | FFA_BUSY => -4
        | FFA_INTERRUPTED => -5
        | FFA_DENIED => -6
        | FFA_RETRY => -7
        | FFA_ABORTED => -8
        end in
    (mkFFA_value_type (FFA_RESULT_CODE_IDENTIFIER (FFA_ERROR ffa_error_code))
                      (ZMap.set 1 error_z_value (ZMap.init 0))). 

  (** In Hafnium: Defined in "inc/vmapi/hf/ffa.h" *)
  Definition ffa_success (handle: Z) :=
    (mkFFA_value_type (FFA_RESULT_CODE_IDENTIFIER (FFA_SUCCESS handle))
                      (ZMap.set 2 (Z.land handle ((Z.shiftl 1 32) - 1)%Z)
                                (ZMap.set 3 (Z.shiftr handle 32) (ZMap.init 0)))).
  
  Definition ffa_value_gen (ffa_result_value : FFA_RESULT_CODE_TYPE) :=
    match ffa_result_value with
    | FFA_ERROR ffa_error_code => ffa_error ffa_error_code
    | FFA_SUCCESS handle => ffa_success handle
    end.
  
  Definition ffa_dispatch_spec :  itree HypervisorEE (unit) := 
    (** - Extract the curretnt vcpu *)
    st <- trigger GetState;;
    (** - Get the information in tpidr_el2 register to find out the current VM to be served *)
    let vcpu_regs := st.(hypervisor_context).(tpidr_el2) in
    match vcpu_regs with
    | Some vcpu_regs' =>
      match vcpu_regs' with
      | mkVCPU_struct (Some cid) (Some vid) arch_regs =>
        match arch_regs with
        | mkArchRegs (mkFFA_value_type func_type vals) =>
          match func_type with
          | FFA_FUNCTION_IDENTIFIER ffa_function_type =>
            (** - Find out the result of the FFA ABI calls by using the proper handling functions *)

            let new_st := st {system_log: st.(system_log)
                                               ++(DispathFFAInterface arch_regs)::nil} in     
            do result <- function_dispatcher ffa_function_type
                                            vid vals new_st ;;;
             match result with                                
            | (updated_st, ffa_result) =>
              (** - Set the result inside the updated state *)
              do vm_context <-
                 ZTree.get
                   vid
                   updated_st.(hypervisor_context).(vms_contexts);;;
              do cur_kernel_vcpu_index <-
                 vm_context.(vm_kernelspace_context).(cur_vcpu_index) ;;;
              do vcpu_reg <-
                 ZTree.get cur_kernel_vcpu_index 
                    vm_context.(vm_kernelspace_context).(vcpus_contexts);;;
              let new_vcpu_reg :=
                  mkVCPU_struct (vcpu_reg.(cpu_id)) (vcpu_reg.(vm_id))
                                (mkArchRegs (ffa_value_gen ffa_result)) in
              let new_vm_context := 
                  vm_context
                    {vm_vcpus_contexts:
                       ZTree.set
                         cur_kernel_vcpu_index
                         new_vcpu_reg 
                         vm_context.(vm_kernelspace_context).(vcpus_contexts)} in
              let new_st :=
                  updated_st
                    {hypervisor_context / vms_contexts:
                       ZTree.set vid new_vm_context
                                 (updated_st.(hypervisor_context).(vms_contexts))} in
              trigger (SetState new_st)
            end                                     


             | _ => triggerUB "ffa_dispatch_spec: impossible case happens"
          end
        end
      | _ => triggerUB "ffa_dispatch_spec: impossible case happens"
      end
    | None => triggerUB "ffa_dispatch_spec: impossible case happens" 
    end.
                        
  Definition ffa_dispatch_call (args : list Lang.val) 
    : itree HypervisorEE (Lang.val * list Lang.val)  :=             
    match args with
    | nil => ffa_dispatch_spec;;
            Ret (Vnull, args)
    | _ => triggerUB "ffa_dispatch_call: wrong arguments"
    end.
      
End FFADispatch.  

(***********************************************************************)
(** **          Client Setter and Getter                               *)
(***********************************************************************)
(*************************************************************)
(** ***               FFA Interface Values                   *) 
(*************************************************************)
(** This section defines Z type interface values for FFA calls *)

Section FFA_DATATYPES.

  Context `{abstract_state_context: AbstractStateContext}.
  
  (** The following types are defined in Chapter 11 (Memory management interfaces document) 
      They are ignored in our modeling. 
   - [FFA_MEM_DONATE]: 0x84000071
   - [FFA_MEM_LEND]: 0x84000072
   - [FFA_MEM_SHARE]: 0x84000073
   - [FFA_MEM_RETRIEVE_REQ]: 0x84000074
   - [FFA_MEM_RETRIEVE_RESP]: 0x84000075
   - [FFA_MEM_RELINQUISH]: 0x84000076
   - [FFA_MEM_RECLAIM]: 0x84000077
   *)
      
  Definition FFA_MEM_DONATE_32 : Z := 2214592625.
  Definition FFA_MEM_LEND_32 : Z := 2214592626.
  Definition FFA_MEM_SHARE_32 : Z := 2214592627.
  Definition FFA_MEM_RETRIEVE_REQ_32 : Z := 2214592628.
  Definition FFA_MEM_RETRIEVE_RESP_32 : Z := 2214592629.
  Definition FFA_MEM_RELINGQUISH_32 : Z := 2214592630.
  Definition FFA_MEM_RECLAIM_32 : Z := 2214592631.

  (** The followings are for return values of FFA interface calls. *)
  (** The following numbers are defined in Chapter 7, especially in Table 7.2: Error status codes
   - [FFA_NOT_SUPPORTED]: -1
   - [FFA_INVALID_PARAMETERS]: -2
   - [FFA_NO_MEMORY]: -3
   - [FFA_BUSY]: -4
   - [FFA_INTERRUPTED]: -5
   - [FFA_DENIED]: -6
   - [FFA_RETRY]: -7
   - [FFA_ABORTED]: -8
  *)

  Definition FFA_NOT_SUPPORTED_32 : Z := -1.
  Definition FFA_INVALID_PARAMETERS_32 : Z := -2.
  Definition FFA_NO_MEMORY_32 : Z := -3.
  Definition FFA_BUSY_32 : Z := -4.
  Definition FFA_INTERRUPTED_32 : Z := -5.
  Definition FFA_DENIED_32 : Z := -6.
  Definition FFA_RETRY_32 : Z := -7.
  Definition FFA_ABORTED_32 : Z := -8.

  (** The following numbers are also defined in Chapter 7
      - [FFA_ERROR]: 0x84000060
      - [FFA_SUCCESS]: 0x84000061
   *)
  Definition FFA_ERROR_32 : Z := 2214592608.
  Definition FFA_SUCCESS_32 : Z := 2214592609.

  Definition Z_to_FFA_Function_Type (value : Z) :=
    if decide (value = FFA_MEM_DONATE_32)
    then Some FFA_MEM_DONATE
    else if decide (value = FFA_MEM_LEND_32)
         then Some FFA_MEM_LEND
         else if decide (value = FFA_MEM_SHARE_32)
              then Some FFA_MEM_SHARE
              else if decide (value = FFA_MEM_RETRIEVE_REQ_32)
                   then Some FFA_MEM_RETREIVE_REQ
                   else if decide (value = FFA_MEM_RETRIEVE_RESP_32)
                        then Some FFA_MEM_RETREIVE_RESP
                        else if decide (value = FFA_MEM_RELINGQUISH_32)
                             then Some FFA_MEM_RELINQUISH
                             else if decide (value = FFA_MEM_RECLAIM_32)
                                  then Some FFA_MEM_RECLAIM
                                  else None.


  Definition FFA_Result_Type_to_Z (res : FFA_RESULT_CODE_TYPE) :=
    match res with
    | FFA_SUCCESS _ => FFA_SUCCESS_32
    | FFA_ERROR _ => FFA_ERROR_32
    end.
  
End FFA_DATATYPES.

(***********************************************************************)
(** **      Client modeling                                            *)
(***********************************************************************)
Section InterfaceFunctions.
  
  (** Memory load and store operations *)
  Definition stage2_get_physical_address_spec (st: AbstractState) (addr : ffa_address_t)
  : itree HypervisorEE (ffa_UUID_t) := 
    match stage2_address_translation_table addr with
    | Some res =>
      match
        ZTree.get res st.(hypervisor_context).(mem_properties).(mem_global_properties) with
      | Some property =>
        match
          ZTree.get res st.(hypervisor_context).(mem_properties).(mem_global_properties) with
        | Some property =>
          match property.(accessible_by) with
          | ExclusiveAccess accessor
            => if (decide (st.(cur_user_entity_id) = accessor))
              then Ret (res)
              else triggerNB "stage2_address_translation_table error"
          | SharedAccess accessors
            => if (in_dec zeq (st.(cur_user_entity_id)) accessors)
              then Ret (res)
              else triggerNB "stage2_address_translation_table error"
          | _ => triggerNB "stage2_address_translation_table error"
          end
        | _ => triggerNB "stage2_address_translation_table error"
        end
      | _ => triggerNB "stage2_address_translation_table error"
      end
    | _ => triggerNB "stage2_address_translation_table error"
    end.

    
  Definition get_physical_address_spec (addr : ffa_address_t)
    : itree HypervisorEE (ffa_UUID_t) := 
    st <- trigger GetState;;
    if st.(is_hvc_mode)
    then Ret (addr)
    else if st.(use_stage1_table)
         then
           match stage1_address_translation_table st.(cur_user_entity_id) addr with
           | Some res' => stage2_get_physical_address_spec st res'
           | None => triggerNB "stage1_address_translation_table error"
           end
         else stage2_get_physical_address_spec st addr.
  
  Definition get_physical_address_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong addr))]  =>
      res <- get_physical_address_spec (Int64.unsigned addr) ;;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "get_current_entity_id_call: wrong arguments"
    end.

  Definition set_is_hvc_mode_spec
    : itree HypervisorEE (unit) := 
    st <- trigger GetState;;
    if st.(is_hvc_mode)
    then triggerNB "error"
    else trigger (SetState (st {is_hvc_mode : true})).

  Definition set_is_hvc_mode_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | []  => set_is_hvc_mode_spec;;
            Ret (Vnull, args)
    | _ => triggerNB "set_use_stage2_table_call: wrong arguments"
    end.
  
  Definition unset_is_hvc_mode_spec
    : itree HypervisorEE (unit) := 
    st <- trigger GetState;;
    if st.(is_hvc_mode)
    then trigger (SetState (st {is_hvc_mode : false}))
    else triggerNB "error".

  Definition unset_is_hvc_mode_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | []  => unset_is_hvc_mode_spec;;
            Ret (Vnull, args)
    | _ => triggerNB "unset_use_stage2_table_call: wrong arguments"
    end.

  Definition set_use_stage1_table_spec
    : itree HypervisorEE (unit) := 
    st <- trigger GetState;;
    if st.(use_stage1_table)
    then triggerNB "error"
    else trigger (SetState (st {use_stage1_table : true})).

  Definition set_use_stage1_table_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | []  => set_use_stage1_table_spec;;
            Ret (Vnull, args)
    | _ => triggerNB "set_use_stage2_table_call: wrong arguments"
    end.
  
  Definition unset_use_stage1_table_spec
    : itree HypervisorEE (unit) := 
    st <- trigger GetState;;
    if st.(use_stage1_table)
    then trigger (SetState (st {use_stage1_table : false}))
    else triggerNB "error".

  Definition unset_use_stage1_table_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | []  => unset_use_stage1_table_spec;;
            Ret (Vnull, args)
    | _ => triggerNB "unset_use_stage2_table_call: wrong arguments"
    end.
  
  Definition send_msg_spec
             (receiver size: ffa_UUID_t)
             (msg : ffa_mailbox_send_msg_t)
             (recv_func : FFA_FUNCTION_TYPE) 
    : itree HypervisorEE (unit) := 
    state <- trigger GetState;;
    let sender := state.(cur_user_entity_id) in
    do vm_context <- ZTree.get receiver state.(hypervisor_context).(vms_contexts) ;;;
    let mailbox_contents := mkMAILBOX_struct 
                              (vm_context.(mailbox).(send))
                              msg (Some sender) size (Some recv_func) in
    let new_vm_context := vm_context {vm_mailbox : mailbox_contents} in
    let new_vm_contexts :=
        ZTree.set receiver new_vm_context
                  state.(hypervisor_context).(vms_contexts) in
    trigger (SetState (state {hypervisor_context / vms_contexts : new_vm_contexts})).
    
  Definition send_msg_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong receiver)); (Vcomp (Vlong size)); (Vabs mailbox_msg); (Vabs recv_func)] =>
        match downcast mailbox_msg ffa_mailbox_send_msg_t, downcast recv_func FFA_FUNCTION_TYPE with
        | Some msg, Some func_type =>
          res <- send_msg_spec (Int64.unsigned receiver) (Int64.unsigned size) msg func_type ;;
          Ret (Vnull, args)
        | _, _ => triggerNB "send_msg_call: impossible conversion"
        end
    | _ => triggerNB "send_msg_call: wrong arguments"
    end.

  Definition recv_msg_spec
    : itree HypervisorEE (ffa_mailbox_send_msg_t) :=
    st <- trigger GetState;;
    let current_vm_id := st.(cur_user_entity_id) in
    do vm_context <- ZTree.get current_vm_id st.(hypervisor_context).(vms_contexts) ;;;
    Ret (vm_context.(mailbox).(send)).
  
  Definition recv_msg_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      res <- recv_msg_spec;;  
      Ret (Vabs (upcast res), args)
    | _ => triggerNB "send_msg_call: wrong arguments"
    end.
  
End InterfaceFunctions.

(***********************************************************************)
(** **    FFA Memory Management Interface Module                       *)
(***********************************************************************)
Section MemSetterGetter.
  
  Definition global_properties_getter_spec
             (addr: ffa_address_t)
  : itree HypervisorEE (MemGlobalProperties) :=
    st <- trigger GetState;;
    match ZTree.get
            addr 
            st.(hypervisor_context).(mem_properties)
          .(mem_global_properties) with
    | Some v => Ret(v)
    | _ => triggerNB "error"
    end.

  Definition global_properties_getter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong addr))] =>
      res <- global_properties_getter_spec (Int64.unsigned addr) ;;
      Ret (Vabs (upcast res), args)
    | _ => triggerNB "send_msg_call: wrong arguments"
    end.
  
  Definition global_properties_setter_spec
             (addr: ffa_address_t)
             (global_properties: MemGlobalProperties) 
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    let mem_props := st.(hypervisor_context).(mem_properties) in
    let new_mem_global_props_pool
        := ZTree.set addr global_properties
                     mem_props.(mem_global_properties) in
    let new_mem_props :=
        mkMemProperties 
          new_mem_global_props_pool
          mem_props.(mem_local_properties) in
    trigger (SetState (st {hypervisor_context
                             / mem_properties: new_mem_props})).

  Definition global_properties_setter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong addr)); (Vabs global_properties)] =>
      match downcast global_properties MemGlobalProperties with
      | Some global_props =>
        global_properties_setter_spec (Int64.unsigned addr) global_props;;
        Ret (Vnull, args)
      | _ => triggerNB "send_msg_call: impossible conversion"
      end
    | _ => triggerNB "send_msg_call: wrong arguments"
    end.
  
  Definition local_properties_getter_spec
             (owner : ffa_UUID_t) (addr: ffa_address_t)
    : itree HypervisorEE (MemLocalProperties) :=
    st <- trigger GetState;;
    match ZTree.get
            owner
            st.(hypervisor_context).(mem_properties)
          .(mem_local_properties) with
    | Some local_props_pool =>
      match ZTree.get addr local_props_pool with
      | Some v => Ret(v)
      | _ => triggerNB "error"
      end
    | _ => triggerNB "error"
    end.

  Definition local_properties_getter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong owner)); (Vcomp (Vlong addr))] =>
      res <-  local_properties_getter_spec (Int64.unsigned owner) (Int64.unsigned addr) ;;
      Ret (Vnull, args)
    | _ => triggerNB "send_msg_call: wrong arguments"
    end.

  Definition local_properties_setter_spec
             (owner : ffa_UUID_t) (addr: ffa_address_t)
             (local_properties: MemLocalProperties)
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    match ZTree.get
            owner
            st.(hypervisor_context).(mem_properties)
          .(mem_local_properties) with
    | Some local_props_local_pool =>
      let new_local_props :=
          ZTree.set addr local_properties 
                    local_props_local_pool in
      let new_local_props_pool :=
          ZTree.set owner new_local_props
                    st.(hypervisor_context).(mem_properties)
          .(mem_local_properties) in
      let new_mem_props :=
          mkMemProperties
            st.(hypervisor_context).(mem_properties)
          .(mem_global_properties)
             new_local_props_pool in
      trigger (SetState (st {hypervisor_context
                               / mem_properties: new_mem_props}))
    | _ => triggerNB "error"
    end.

  Definition local_properties_setter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong owner));(Vcomp (Vlong addr)); (Vabs local_properties)] =>
      match downcast local_properties MemLocalProperties with
      | Some local_props =>
        local_properties_setter_spec (Int64.unsigned owner)
                                 (Int64.unsigned addr) local_props;;
        Ret (Vnull, args)
      | _ => triggerNB "send_msg_call: impossible conversion"
      end
    | _ => triggerNB "send_msg_call: wrong arguments"
    end.

  Definition set_mem_dirty_spec (writer: ffa_UUID_t) (addr: ffa_address_t)
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    match ZTree.get
            addr
            st.(hypervisor_context).(mem_properties)
          .(mem_global_properties) with
    | Some (mkMemGlobalProperties is_ns owner access inst_access
                                  data_access mem_attr mem_dirty)
      => let new_mem_dirty := match mem_dirty with
                             | MemClean => MemWritten (writer::nil)
                             | MemWritten writers =>
                               if decide (in_dec zeq writer writers)
                               then MemWritten writers
                               else MemWritten (writer::writers)
                             end in
        let new_global_prop :=
            mkMemGlobalProperties is_ns owner access inst_access
                                  data_access mem_attr
                                  new_mem_dirty in
        let new_global_props :=
            ZTree.set
              addr new_global_prop 
              st.(hypervisor_context).(mem_properties)
            .(mem_global_properties) in
        let new_mem_props :=
            mkMemProperties 
              new_global_props
              st.(hypervisor_context).(mem_properties)
            .(mem_local_properties) in
        trigger (SetState (st {hypervisor_context
                                 / mem_properties: new_mem_props}))
    | _ => triggerNB "error"
    end.

  Definition set_mem_dirty_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong writer)); (Vcomp (Vlong addr))] =>
      set_mem_dirty_spec (Int64.unsigned writer) (Int64.unsigned addr) ;;
      Ret (Vnull, args)
    | _ => triggerNB "set_mem_dirty_call: wrong arguments"
    end.

  Definition clean_mem_dirty_spec (writer: ffa_UUID_t) (addr: ffa_address_t)
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    match ZTree.get
            addr
            st.(hypervisor_context).(mem_properties)
          .(mem_global_properties) with
    | Some (mkMemGlobalProperties is_ns owner access inst_access
                                  data_access mem_attr mem_dirty)
      => let new_global_prop :=
            mkMemGlobalProperties is_ns owner access inst_access
                                  data_access mem_attr
                                  MemClean in
        let new_global_props :=
            ZTree.set
              addr new_global_prop 
              st.(hypervisor_context).(mem_properties)
            .(mem_global_properties) in
        let new_mem_props :=
            mkMemProperties 
              new_global_props
              st.(hypervisor_context).(mem_properties)
            .(mem_local_properties) in
        trigger (SetState (st {hypervisor_context
                                 / mem_properties: new_mem_props}))
    | _ => triggerNB "error"
    end.

  Definition clean_mem_dirty_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong writer)); (Vcomp (Vlong addr))] =>
      clean_mem_dirty_spec (Int64.unsigned writer) (Int64.unsigned addr) ;;
      Ret (Vnull, args)
    | _ => triggerNB "set_mem_dirty_call: wrong arguments"
    end.

  Definition get_current_entity_id_spec
    : itree HypervisorEE (ffa_UUID_t) :=
    st <- trigger GetState;;
    if (st.(is_hvc_mode)) then Ret (hypervisor_id)
    else Ret (st.(cur_user_entity_id)).

  Definition get_current_entity_id_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      entity_id <- get_current_entity_id_spec;;
      Ret (Vcomp (Vlong (Int64.repr entity_id)), args)
    | _ => triggerNB "get_current_entity_id_call: wrong arguments"
    end.
  
End MemSetterGetter.

(***********************************************************************)
(** **    FFA Memory Management Interface Module                       *)
(***********************************************************************)
Section FFAMemoryManagementInterfaceModule.

  Definition funcs :=
    [
      ("HVCTopLevel.save_regs_to_vcpu_call", save_regs_to_vcpu_call) ;
    ("HVCTopLevel.vcpu_restore_and_run_call", vcpu_restore_and_run_call) ;
    ("HVCTopLevel.ffa_dispatch_call", ffa_dispatch_call) ;
    
    ("HVCTopLevel.get_physical_address", get_physical_address_call);
    ("HVCTopLevel.set_is_hvc_mode", set_is_hvc_mode_call);
    ("HVCTopLevel.unset_is_hvc_mode", unset_is_hvc_mode_call);
    ("HVCTopLevel.set_use_stage1_table", set_use_stage1_table_call);
    ("HVCTopLevel.unset_use_stage1_table", unset_use_stage1_table_call);

    ("HVCToplevel.get_current_entity_id", get_current_entity_id_call);
    
    ("HVCTopLevel.send_msg", send_msg_call);
    ("HVCTopLevel.recv_msg", recv_msg_call);
    ("HVCTopLevel.global_properties_getter", global_properties_getter_call);
    ("HVCTopLevel.global_properties_setter", global_properties_setter_call);
    ("HVCTopLevel.local_properties_getter", local_properties_getter_call);
    ("HVCTopLevel.local_properties_setter", local_properties_setter_call);
    ("HVCTopLevel.set_mem_dirty", set_mem_dirty_call);
    ("HVCTopLevel.clean_mem_dirty", clean_mem_dirty_call)
      (* TODO: add more getter/setter functions for clients *)
    ].

  Definition top_level_modsem : ModSem :=
    mk_ModSem
      (fun s => existsb (string_dec s) (List.map fst funcs))
      _
      (initial_state)
      updateStateE
      updateState_handler
      (fun T (c: CallExternalE T) =>
         let '(CallExternal func_name args) := c in
         let fix find_func l :=
             match l with
             | (f, body)::tl =>
               if (string_dec func_name f)
               then body args
               else find_func tl
             | nil => triggerNB "Not mpool func"
             end
         in
         find_func funcs
      )
  .
  
End FFAMemoryManagementInterfaceModule.

Require Import Lang.
Require Import Values.
Require Import Integers.
Require Import Constant.
Import LangNotations.
Local Open Scope expr_scope.

Import Int64.

(***********************************************************************)
(** **                  Hypervisor Call                                *)
(***********************************************************************)
Section HypervisorCall.
  
  Definition hypervisor_call :=
    (Call "HVCTopLevel.save_regs_to_vcpu" []) #;
    (Call "HVCTopLevel.function_dispatcher" []) #;
    (Call "HVCTopLevel.vcpu_restore_and_run_spec" []).

  Definition hypervisor_callF : function.
    mk_function_tac hypervisor_call ([]: list var) ([]: list var).
  Defined.  
  
End HypervisorCall.

(***********************************************************************)
(** **    FFA Memory Management Interface Module With Mem Accessor     *)
(***********************************************************************)
Section FFAMemoryManagementInterfaceWithMemAccessorModule.

  (** Arbitrarily assign the block number for users *)
  Definition flat_mem_block_ptr := (Vptr 2%positive (Ptrofs.repr 0)).

  Definition mem_store_spec (addr value : var) (entity_id paddr : var) : stmt :=
    entity_id #= (Call "HVCToplevel.get_current_entity_id" []) #;
              paddr #= (Call "HVCTopLevel.get_physical_address" [CBV addr]) #;
              (Call "HVCTopLevel.set_mem_dirty" [CBV entity_id; CBV addr]) #;
              (flat_mem_block_ptr @ paddr #:= value).
                                          
  Definition mem_load_spec (addr : var) (paddr: var): stmt :=
    paddr #= (Call "HVCTopLevel.get_physical_address" [CBV addr]) #;    
    Return (flat_mem_block_ptr  #@ paddr).

  Definition mem_store_specF: function.
    mk_function_tac mem_store_spec ["addr"; "value"] ["entity_id "; "paddr"].
  Defined.

  Definition mem_load_specF: function.
    mk_function_tac mem_load_spec ["addr"] ["paddr"].
  Defined.

  Definition mem_funcs :=
    [
      ("HVCTopLevel.mem_store", mem_store_specF) ;
    ("HVCTopLevel.mem_load", mem_load_specF);
    ("HVCTopLevel.hypervisor_call", hypervisor_callF)
    ].
  
  Definition top_level_accessor_modsem : ModSem := program_to_ModSem mem_funcs.
  
End FFAMemoryManagementInterfaceWithMemAccessorModule.

