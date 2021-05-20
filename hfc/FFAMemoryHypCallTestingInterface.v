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

(* end hide *)

Definition Z_64MAX := ((Z.pow 2 64) - 1)%Z.
Definition Z_not := fun val => (Z.lxor Z_64MAX val).

(*************************************************************)
(** *                Introduction                            *) 
(*************************************************************)

(** This file contains definitions that are necessary for providing testing interfaces. 
    They are usually contains Z type (or integer type) values that are relevant to several 
    inductive type values in other files. 
*)

Notation "'get' E ',' X <- A ';;;' B" :=
  (match A with Some X => B |
           None => triggerNB E end)
    (at level 200, X ident, A at level 100, B at level 200)
  : itree_monad_scope.

Notation "'get' X <- A ';;;' B" :=
  (match A with Some X => B |
           None => triggerNB "None" end)
    (at level 200, X ident, A at level 100, B at level 200)
  : itree_monad_scope.

Notation "'check' E ',' A ';;;' B" :=
  (if A then B else triggerNB E)
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
Definition granuale_shift := 12.

Global Instance ffa_types_and_constants : FFA_TYPES_AND_CONSTANTS :=
  {
  ffa_memory_region_tag_t := ffa_memory_region_tag_t;
  (** - The following two types are for message passings. We use them to record and 
        retrieve descriptor information *)

  (** - Granuale value. It is usually a multiplication of 4096 (4KiB) *)
  granuale := Z.shiftl 1 granuale_shift;
  init_ffa_memory_region_tag := 0;
  }.

Eval compute in granuale.

(***********************************************************************)
(** **                  DescriptorContext instance                     *)
(***********************************************************************)
Global Instance descriptor_context :
  DescriptorContext (ffa_types_and_constants := ffa_types_and_constants) :=
  {
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
  }.

(***********************************************************************)
(** **                  FFA_VM_CONTEXT instance                        *)
(***********************************************************************)
(** buffer message could be either the initial value, memory region descriptor, relinquish descriptor,
    or handle value (Z type value). *)
Inductive ffa_buffer_msg_instance_t : Type :=
| buffer_memory_init_value
| buffer_memory_region (region_descriptor: FFA_memory_region_struct)
| buffer_memory_relinquish (relinquish_descriptor: FFA_memory_relinquish_struct)
| buffer_z (value : Z).

(** We assume there are four VCPUs in the system *)
Definition init_ffa_buffer_msg := buffer_memory_init_value.
Definition vcpu_max_num := 4.

(** Conversions to/from mailbox messages from/to memory region descriptor/relinquish descriptor/handle value *) 
Definition buffer_msg_to_region_struct :=
  fun x =>
    match x with
    | buffer_memory_region region_descriptor =>
      Some region_descriptor
    | _ => None
    end.

Definition buffer_msg_to_relinquish_struct :=
  fun x =>
    match x with
    | buffer_memory_relinquish relinquish_descriptor =>
      Some relinquish_descriptor
    | _ => None
    end.

Definition buffer_msg_to_z :=
  fun x =>
    match x with
    | buffer_z value =>
      Some value
    | _ => None
    end.

Definition region_struct_to_buffer_msg :=
  fun x => Some (buffer_memory_region x).

Definition relinquish_struct_to_buffer_msg :=
  fun x => Some (buffer_memory_relinquish x).

Definition z_to_buffer_msg := 
  fun x => Some (buffer_z x).

Global Instance ffa_vm_context :
  FFA_VM_CONTEXT (ffa_types_and_constants := ffa_types_and_constants)  :=
    {
    (** - The following two types are for message passings. We use them to record and 
        retrieve descriptor information *)
    ffa_buffer_msg_t := ffa_buffer_msg_instance_t;
    init_ffa_buffer_msg := init_ffa_buffer_msg;

    vcpu_max_num := vcpu_max_num;

    (** mailbox to/from descriptors *)
    buffer_msg_to_region_struct := buffer_msg_to_region_struct;
    buffer_msg_to_relinqiush_struct := buffer_msg_to_relinquish_struct;
    buffer_msg_to_Z := buffer_msg_to_z;
    region_struct_to_buffer_msg := region_struct_to_buffer_msg;
    relinqiush_struct_to_buffer_msg := relinquish_struct_to_buffer_msg;
    Z_to_buffer_msg := z_to_buffer_msg;

    primary_vm_id := 1;
    secondary_vm_ids := 2::3::4::nil;

    (* TODO: Need to fix *)
    FFA_memory_region_struct_size := fun x => 1;
    }.
    
(** TODO: The following values are dummy representations. We have to provide 
    proper values later if we want to connect this one with the real Hafnium / other 
    hypervisor implementations *)

(***********************************************************************)
(** **       HafniumMemoryManagementContext instance                   *)
(***********************************************************************)
(** Note that we cannot use a large number in here to avoid stack overflow. 
    I have tested with 16, but it raised stack overflow. 

    With the current instance, the memory address range that we can represent 
    is from (0 * 2^12) to (2^12 * 2^12) since the granuale is 2^12.
 *)
Definition page_high_shift := 12.

Global Instance memory_management_basic_context
  : MemoryManagementBasicContext
      (ffa_vm_context := ffa_vm_context) :=
  {
  page_low := 0;
  page_high := (Z.shiftl 1 page_high_shift)%Z;
  alignment_value := granuale;
  }.

Eval compute in (page_low * granuale)%Z.
Eval compute in (page_high * granuale)%Z.
 
Definition stage2_address_translation_table :=
  fun (x : ffa_address_t) =>
    if decide ((page_low * granuale) <= x)%Z
       && decide (x < (page_high * granuale))%Z
    then Some x else None.

Definition  stage1_address_translation_table :=
  fun (vid : ffa_UUID_t) (x : ffa_address_t) =>
    let address_low := (page_low * granuale)%Z in
    let address_high := (page_high * granuale)%Z in
    if decide (0 <= vid)%Z && decide (vid < number_of_vm)%Z
    then if decide (address_low <= x)%Z &&
            decide (x < address_high)%Z
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

(** We assume number of CPUs as 4 *)
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

Definition init_cpus := cal_init_cpus (Z.to_nat (num_of_cpus - 1)).

Definition init_api_page_pool_size_shift := 32.

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
  := cal_init_local_properties_pool vm_ids.

Definition init_mem_properties :=
  mkMemProperties
    init_mem_global_properties_pool
    init_mem_local_properties_global_pool.

Definition init_VM_COMMON_struct (vcpu_index : Z) (vcpu_ids: list Z) 
  := mkVM_COMMON_struct
       (Some vcpu_index)
       vcpu_ids 
       (ZTree.empty VCPU_struct).

Definition init_BUFFER_struct :=
  mkBUFFER_struct
    init_ffa_buffer_msg
    None (* sender *)
    0 (* size *)
    None (* recv func *)
.

Definition init_VM_KERNEL_context (vcpu_index : Z) (vcpu_ids: list Z) :=
 mkVM_KERNEL_struct 
   (init_VM_COMMON_struct vcpu_index vcpu_ids)
   init_BUFFER_struct.

Fixpoint cal_init_VM_KERNEL_contexts (vm_ids: list Z) := 
  match vm_ids with
  | nil =>  (ZTree.empty VM_KERNEL_struct)
  | hd::tl =>
    let res :=  cal_init_VM_KERNEL_contexts tl in
    ZTree.set hd (init_VM_KERNEL_context hd (hd::nil)) res
  end.

Definition init_VM_KERNEL_contexts :=
  cal_init_VM_KERNEL_contexts vm_ids.

Fixpoint cal_init_VM_USERSPACE_contexts (vm_ids: list Z) :=
  match vm_ids with
  | nil =>  (ZTree.empty VM_USERSPACE_struct)
  | hd::tl =>
    let res :=  cal_init_VM_USERSPACE_contexts tl in
    ZTree.set hd (mkVM_USERSPACE_struct (init_VM_COMMON_struct hd (hd::nil))) res
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
(** *                 Showable functions for system log                *)
(***********************************************************************)

(** Showable functions for system log are hidden in the document. *)

(* begin hide *)


(** print FFA values. for the simplicity, we only print the result of the operation *)
Definition print_FFA_value_type (ffa_value: FFA_value_type) :=
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
            | FFA_NOT_SUPPORTED res => append_all [" FFA_NOT_SUPPROTED" ; " (" ; res; ")"]
            | FFA_INVALID_PARAMETERS res => append_all [" FFA_INVALID_PARAMETERS"; " ("; res; ")"]
            | FFA_NO_MEMORY res => append_all [" FFA_NO_MEMORY "; " ("; res; ")"]
            | FFA_BUSY res => append_all [" FFA_BUSY "; " ("; res; ")"]
            | FFA_INTERRUPTED res => append_all [" FFA_INTERRUPTED "; " ("; res; ")"]
            | FFA_DENIED res => append_all [" FFA_DENIED "; " ("; res; ")"]
            | FFA_RETRY res => append_all [" FFA_RETRY "; " ("; res; ")"]
            | FFA_ABORTED res => append_all [" FFA_ABORTED "; " ("; res; ")"] 
            end
          | FFA_SUCCESS value =>
            (append_all [" FFA_SUCCESS (" ; HexString.of_Z value; ") "])
          end
        end
    in ffa_value_string
    (* append ffa_value_string (print_ffa_vals vals) *)
  end.

Definition print_onwership_state_type
           (ownership_state_type : OWNERSHIP_STATE_TYPE) :=
  match ownership_state_type with
  | Owned id => append_all ["(Owned by "; HexString.of_Z id; ")"]
  | NotOwned => "(Not Owned)"
  end.

Definition print_access_state_type
           (access_state_type : ACCESS_STATE_TYPE) :=
  match access_state_type with
  | NoAccess => "(NoAccess)"
  | ExclusiveAccess accessor
    => append_all ["(ExclusiveAccess "; HexString.of_Z accessor; ")"]
  | SharedAccess accessors
    => append_all ["(ExclusiveAccess "; list_z_to_string accessors; ")"]
  end.

Definition print_mem_dirty_type
           (mem_dirty_type :  MEM_DIRTY_TYPE) :=
  match mem_dirty_type with
  | MemClean => "(MemClean)"
  | MemWritten writers
    => append_all ["(MemWritten "; list_z_to_string writers; ")"]
  end.

Definition print_ffa_instruction_access_type
           (ffa_instruction_access_type : FFA_INSTRUCTION_ACCESS_TYPE) :=
  match ffa_instruction_access_type with
  | FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED => "ACCESS_NOT_SPECIFIED" 
  | FFA_INSTRUCTION_ACCESS_XN => "ACCESS_XN"
  | FFA_INSTRUCTION_ACCESS_X => "ACCESS_X"
  | FFA_INSTRUCTION_ACCESS_RESERVED => "ACCESS_RESERVED"
  end.

Definition print_ffa_data_access_type
           (ffa_data_access_type: FFA_DATA_ACCESS_TYPE) :=
  match ffa_data_access_type with 
  | FFA_DATA_ACCESS_NOT_SPECIFIED => "ACCESS_NOT_SPECIFIED"
  | FFA_DATA_ACCESS_RO => "ACCESS_RO"
  | FFA_DATA_ACCESS_RW => "ACCESS_RW"
  | FFA_DATA_ACCESS_RESERVED => "ACCESS_RESERVED"
  end.

Definition print_ffa_memory_type
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


Definition print_permissions_descriptor_struct
           (permissions_descriptor: FFA_memory_access_permissions_descriptor_struct) :=
  match permissions_descriptor with
    mkFFA_memory_access_permissions_descriptor_struct
      receiver instruction_access data_access flags =>
    append_all ["Reciever: "; HexString.of_Z receiver;
               tabspace;
               "Instruction Perm: ";
               print_ffa_instruction_access_type instruction_access;
               tabspace;
               "Data Perm: ";
               print_ffa_data_access_type data_access;
               tabspace;
               "Flag: "; match flags with true => "true" | false => "false" end]
  end.

Definition print_endpoint_memory_access_descriptor_struct
           (endpoint: FFA_endpoint_memory_access_descriptor_struct) :=
  match endpoint with
    mkFFA_endpoint_memory_access_descriptor_struct permissions offset
    => 
    append_all ["(End-Permissions: ";
               print_permissions_descriptor_struct  permissions;
               tabspace;
               "Offset: "; HexString.of_nat offset; ")"]
  end.
                
Fixpoint print_endpoints
           (endpoints: list FFA_endpoint_memory_access_descriptor_struct) :=
  match endpoints with
  | nil => ""
  | hd::nil =>
    append_all ["<"; HexString.of_nat (length endpoints); ">: ";
               print_endpoint_memory_access_descriptor_struct hd]    
  | hd::tl =>
    let res := print_endpoints tl in
    append_all
      ["<"; HexString.of_nat (length endpoints); ">: ";
      print_endpoint_memory_access_descriptor_struct hd;
      tabspace;
      res]
  end.

Definition print_constituent_struct
           (constituent: FFA_memory_region_constituent_struct) :=
  match constituent with
  | mkFFA_memory_region_constituent_struct
      address page_count =>
    append_all ["("; "Address: "; HexString.of_Z address;
               tabspace; "PageCount "; HexString.of_Z page_count ; ")"]
  end.

Fixpoint print_constituents
         (constituents: list FFA_memory_region_constituent_struct) :=
  match constituents with
  | nil => ""
  | hd::nil =>
    append_all ["<"; HexString.of_nat (length constituents); ">: ";
               print_constituent_struct hd]
  | hd::tl =>
    let res := print_constituents tl in
    append_all ["<"; HexString.of_nat (length constituents); ">: ";
               print_constituent_struct hd; tabspace;
               res]
  end.

Definition print_composite_memory_region_struct
           (composite: FFA_composite_memory_region_struct) :=
  match composite with
  | mkFFA_composite_memory_region_struct page_count constituents
    => 
    append_all ["PageCount: "; HexString.of_Z page_count;
               tabspace;
               "Composite: "; "[";
               print_constituents constituents; "]"]
  end.
  
Definition print_memory_region_descriptor
           (region_desc: FFA_memory_region_struct)
  :=
    match region_desc with
    | mkFFA_memory_region_struct
        sender
        attributes
        flags
        handle
        tag
        receivers
        composite  =>
      append_all ["Region Descriptor:";
                 newline; tabspace;
                 "Sender: "; HexString.of_Z sender;
                 newline; tabspace;
                 "Attributes: ";
                 print_ffa_memory_type
                   attributes
                 .(FFA_memory_region_attributes_descriptor_struct_memory_type);
                 newline; tabspace;
                 "Receivers: "; "["; print_endpoints receivers; "]";
                 newline; tabspace;                 
                 "Composite: ";
                 print_composite_memory_region_struct composite
                 ]
    end.

(* TODO: need to add more things *)
Definition print_relinquish_region_descriptor
           (relinquish_desc: FFA_memory_relinquish_struct)
  := " ".

Definition print_buffer_msg (buffer : BUFFER_struct) :=
  match buffer with
  | mkBUFFER_struct message sender size func =>
    let intro_str := append_all [newline;"BUFFER: "] in
    let message_str :=        
    match message with
    | buffer_memory_init_value
      => append_all [newline; tabspace; "init value"]
    | buffer_memory_region region_desc =>
      append_all [newline; tabspace;
                 "region_desc: ";
                  print_memory_region_descriptor region_desc]
    | buffer_memory_relinquish relinquish_desc =>
      append_all [newline; tabspace;
                 "relinquish_desc: ";
                 print_relinquish_region_descriptor relinquish_desc]
    | buffer_z value => append_all [newline; tabspace; "z value: "; HexString.of_Z value]
    end in
    let sender_str :=
        append_all [newline; tabspace; "Sender: "; 
                   match sender with
                   | Some sender' => HexString.of_Z sender'
                   | None => "none"
                   end] in
    let size_str := 
        append_all [newline; tabspace; "Size: "; HexString.of_Z size] in
    let func_str := 
        append_all [newline; tabspace; "Function: ";
                   match func with
                   | Some func' =>
                     match func' with
                     | FFA_MEM_DONATE => " FFA_MEM_DONATE "
                     | FFA_MEM_LEND => " FFA_MEM_LEND "
                     | FFA_MEM_SHARE => " FFA_MEM_SHARE "
                     | FFA_MEM_RETREIVE_REQ => " FFA_MEM_RETRIEVE_REQ "
                     | FFA_MEM_RETREIVE_RESP => " FFA_MEM_RETRIEVE_RESP "
                     | FFA_MEM_RELINQUISH => " FFA_MEM_RELINQUISH "
                     | FFA_MEM_RECLAIM => " FFA_MEM_RECLAIM "
                     end 
                   | None => "none"
                   end] in    
    append_all [intro_str; message_str; sender_str; size_str; func_str]
  end.
  
Definition print_system_log_entity (log_entity : log_type) :=
  match log_entity with
  | ChangeCurEntityID from_id to_id
    => append_all [newline;
                 "(change from ";
                 HexString.of_Z from_id;
                 " ";
                 HexString.of_Z to_id;
                 ")"]
                 
  | UserToKernel vid vcpu_id reg_vals
    => append_all [newline;
                 "(From User to Kernel:";
                 newline;
                 tabspace;
                 "vm id: ";
                 HexString.of_Z vid;
                 newline;
                 tabspace;
                 "vcpu id: ";
                 HexString.of_Z vcpu_id;
                 newline;
                 tabspace;
                 "reg_vals: ";
                 print_FFA_value_type reg_vals.(regs);
                 ")"]
                 
  | KernelToUser vid vcpu_id reg_vals
    => append_all [newline;
                 "(From Kernel to User:";
                 newline;
                 tabspace;
                 "vm id: ";
                 HexString.of_Z vid;
                 newline;
                 tabspace;
                 "vcpu id: ";
                 HexString.of_Z vcpu_id;
                 newline;
                 tabspace;
                 "reg_vals: ";
                 print_FFA_value_type reg_vals.(regs);
                 ")"]
                 
  | DispathFFAInterface reg_vals
    => append_all [newline;
                 "(Dispatch hyp call:";
                 newline;
                 tabspace;
                 "reg_vals: ";
                 print_FFA_value_type reg_vals.(regs);
                 ")"]
                 
  | SetOwner entity_id address owner 
    => append_all [newline;
                 "(SetOwner:";
                 newline;
                 tabspace;
                 "vm_id: ";
                 HexString.of_Z entity_id;
                 newline;
                 tabspace;
                 "address: ";
                 HexString.of_Z address;
                 newline;
                 tabspace;
                 "onwership: ";
                 print_onwership_state_type owner;
                 ")"]
                 
  | SetAccessible vm_id address access
    => append_all [newline;
                 "(SetAccessibility:";
                 newline;
                 tabspace;                 
                 "vm_id: ";
                 HexString.of_Z vm_id;
                 newline;
                 tabspace;                 
                 "address: ";
                 HexString.of_Z address;
                 newline;
                 tabspace;                 
                 "access: ";
                 print_access_state_type access;
                 ")"]

  | SetInstructionAccess vm_id address access
    => append_all [newline;
                 "(SetInstructionAccess:";
                 newline;
                 tabspace;                 
                 "vm_id: ";
                 HexString.of_Z vm_id;
                 newline;
                 tabspace;                 
                 "address: ";
                 HexString.of_Z address;
                 newline;
                 tabspace;                 
                 "access: ";
                 print_ffa_instruction_access_type access;
                 ")"]

  | SetDataAccess vm_id address access
    => append_all [newline;
                 "(SetDataAccess:";
                 newline;
                 tabspace;                 
                 "vm_id: ";
                 HexString.of_Z vm_id;
                 newline;
                 tabspace;                 
                 "address: ";
                 HexString.of_Z address;
                 newline;
                 tabspace;                 
                 "access: ";
                 print_ffa_data_access_type access;
                 ")"]

  | SetDirty vm_id address dirty
    => append_all [newline;
                 "(SetDirty:";
                 newline;
                 tabspace;
                 "vm_id: ";
                 HexString.of_Z vm_id;
                 newline;
                 tabspace;
                 "address: ";
                 HexString.of_Z address;
                 newline;
                 tabspace;
                 "dirty: ";
                 print_mem_dirty_type dirty;
                 ")"]

  | SetAttributes vm_id address attributes
    => append_all [newline;
                 "(SetAttributes:";
                 newline;
                 tabspace;                 
                 "vm_id: ";
                 HexString.of_Z vm_id;
                 newline;
                 tabspace;                 
                 "address: ";
                 HexString.of_Z address;
                 newline;
                 tabspace;                 
                 "attributes: ";
                 print_ffa_memory_type attributes;
                 ")"]

  | SetBuffer sender receiver msg
    => append_all [newline;
                 "(SetBuffer:";
                 newline;
                 tabspace;
                 "sender: ";
                 HexString.of_Z sender;
                 newline;
                 tabspace;                 
                 "receiver: ";
                 HexString.of_Z receiver;
                 newline;
                 tabspace;
                 "msg: ";
                 print_buffer_msg msg;
                 ")"]
                 
  | GetBuffer receiver msg 
    => append_all [newline;
                 "(GetBuffer:";
                 newline;
                 tabspace;
                 "receiver: ";
                 HexString.of_Z receiver;
                 newline;
                 tabspace;
                 "msg: ";
                 print_buffer_msg msg;
                 ")"]
  end.
                  
Fixpoint print_system_log (system_log: list log_type) :=
  match system_log with
  | nil => " "
  | hd::tl =>
    append (print_system_log_entity hd)
           (print_system_log tl)
  end.

Notation system_log_type := (list log_type)%type.

Instance system_log_Showable:
  Showable  system_log_type := { show := print_system_log }.

Definition print_abstract_state (st : AbstractState) : string :=
  print_system_log st.(system_log).

Instance abstract_state_Showable:
  Showable AbstractState := { show := print_abstract_state }.

(* end hide *)

(***********************************************************************)
(** *   Showable function for other abstract values                    *)
(***********************************************************************)

(***********************************************************************)
(** **   Showable function for global memory property                  *)
(***********************************************************************)


(** Showable functions for global memory property are hidden in the document. *)

(* begin hide *)

Definition print_OWNERSHIP_STATE_TYPE
           (ownership: OWNERSHIP_STATE_TYPE) :=
  match ownership with
  | Owned id => append_all ["owned by "; HexString.of_Z id]
  | NotOwned => "not owned by anyone"
  end.

Definition print_ACCESS_STATE_TYPE
           (access_state: ACCESS_STATE_TYPE) :=
  match access_state with
  | NoAccess => "no accessibility"
  | ExclusiveAccess accessor =>
    append_all ["exclusive access by "; HexString.of_Z accessor]
  | SharedAccess accessors =>
    append_all ["shared access by ";
               append_all (List.map (fun x => append_all [HexString.of_Z x; " "])
                                    accessors)]
  end.

Definition print_FFA_INSTRUCTION_ACCESS_TYPE
           (instruction_access_type: FFA_INSTRUCTION_ACCESS_TYPE) :=
  match instruction_access_type with
  | FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED => "not specified"
  | FFA_INSTRUCTION_ACCESS_XN => "xn"
  | FFA_INSTRUCTION_ACCESS_X => "x" 
  | FFA_INSTRUCTION_ACCESS_RESERVED => "reserved"
  end.

Definition print_FFA_DATA_ACCESS_TYPE
           (data_access_type: FFA_DATA_ACCESS_TYPE) :=
  match data_access_type with
  | FFA_DATA_ACCESS_NOT_SPECIFIED => "not specified"
  | FFA_DATA_ACCESS_RO => "ro"
  | FFA_DATA_ACCESS_RW => "rw"
  | FFA_DATA_ACCESS_RESERVED => "reserved"
  end.

Definition print_FFA_MEMORY_CACHEABILITY_TYPE_1
           (cacheability: FFA_MEMORY_CACHEABILITY_TYPE_1) :=
  match cacheability with
  | FFA_MEMORY_CACHE_RESERVED => "reserved"
  | FFA_MEMORY_CACHE_NON_CACHEABLE => "non_cacheable"
  | FFA_MEMORY_CACHE_RESERVED_1 => "reserved1"
  | FFA_MEMORY_CACHE_WRITE_BACK => "write back"
  end.

Definition print_FFA_MEMORY_CACHEABILITY_TYPE_2
           (cacheability: FFA_MEMORY_CACHEABILITY_TYPE_2) :=
  match cacheability with
  | FFA_MEMORY_DEV_NGNRNE => "nGnRnE"
  | FFA_MEMORY_DEV_NGNRE => "nGnRE"
  | FFA_MEMORY_DEV_NGRE => "nGRE"
  | FFA_MEMORY_DEV_GRE => "GRE"
  end.

Definition print_FFA_MEMORY_SHAREABILITY
           (shareability: FFA_MEMORY_SHAREABILITY) :=
  match shareability with 
  | FFA_MEMORY_SHARE_NON_SHAREABLE => "non shareable"
  | FFA_MEMORY_SHARE_RESERVED => "reserved"
  | FFA_MEMORY_OUTER_SHAREABLE => "outer shareable"
  | FFA_MEMORY_INNER_SHAREABLE => "inner shareable"
  end.

Definition print_FFA_MEMORY_TYPE
           (memory_type: FFA_MEMORY_TYPE) :=
  match memory_type with
  | FFA_MEMORY_NOT_SPECIFIED_MEM => "not specified"
  | FFA_MEMORY_DEVICE_MEM cacheability =>
    append_all ["device mem ("; 
               print_FFA_MEMORY_CACHEABILITY_TYPE_2 
                 cacheability;
               ")"]
  | FFA_MEMORY_NORMAL_MEM cacheability shareability =>
    append_all ["device mem ("; 
               print_FFA_MEMORY_CACHEABILITY_TYPE_1 
                 cacheability;
               " ";
               print_FFA_MEMORY_SHAREABILITY
                 shareability;
                 ")"]
  | FFA_MEMORY_MEM_RESERVED =>
    "reserved"
  end.

Definition print_MEM_DIRTY_TYPE
           (mem_dirty: MEM_DIRTY_TYPE) :=
  match mem_dirty with
  | MemClean => "mem clean"
  | MemWritten writers =>
    append_all ["mem written by ";
               append_all (List.map
                             (fun x => append_all [HexString.of_Z x; " "])
                             writers)]
  end.
  
Definition print_mem_global_properties
           (mem_global_prop: MemGlobalProperties) :=
  match mem_global_prop with
  | mkMemGlobalProperties ns owned accessible instr_access
                          data_access mem_attr dirty
    => let ns_str := if ns then "true" else "false" in
      let owned_str := print_OWNERSHIP_STATE_TYPE owned in
      let accessible_str := print_ACCESS_STATE_TYPE accessible in
      let instr_access_str := print_FFA_INSTRUCTION_ACCESS_TYPE instr_access in
      let data_access_str := print_FFA_DATA_ACCESS_TYPE data_access in
      let mem_attr_str := print_FFA_MEMORY_TYPE mem_attr in
      let dirty_str := print_MEM_DIRTY_TYPE dirty in
      append_all
        [newline;
        "Global Prop:"; newline;
        tabspace; "NSecure: "; ns_str; newline;
        tabspace; "Owned: "; owned_str; newline;
        tabspace; "Accessible: "; accessible_str; newline;
        tabspace; "InstrAccess: "; instr_access_str; newline;
        tabspace; "DataAccess: "; data_access_str; newline;
        tabspace; "MemAttr: "; mem_attr_str; newline;
        tabspace; "MemDirty: "; dirty_str]
  end.

Instance mem_global_properties_Showable:
  Showable MemGlobalProperties := { show := print_mem_global_properties }.

(* end hide *)


(***********************************************************************)
(** **   Showable function for local memory property                   *)
(***********************************************************************)

(** Showable functions for local memory property are hidden in the document. *)

(* begin hide *)


Definition print_mem_local_properties
           (mem_local_prop: MemLocalProperties) :=
  match mem_local_prop with
  | mkMemLocalProperties local_owned instr_access data_access mem_attr
    => let local_owned_str := "" in
      let instr_access_str := print_FFA_INSTRUCTION_ACCESS_TYPE instr_access in
      let data_access_str := print_FFA_DATA_ACCESS_TYPE data_access in
      let mem_attr_str := print_FFA_MEMORY_TYPE mem_attr in
      append_all
        [newline;
        "Local Prop:"; newline;
        tabspace; "Owned: "; local_owned_str; newline;
        tabspace; "InstrAccess: "; instr_access_str; newline;
        tabspace; "DataAccess: "; data_access_str; newline;
        tabspace; "MemAttr: "; mem_attr_str; newline]        
  end.
     
Instance mem_local_properties_Showable:
  Showable MemLocalProperties := { show := print_mem_local_properties }.

(* end hide *)

(***********************************************************************)
(** **   Showable function for vcpu structure                          *)
(***********************************************************************)

(** Showable functions for vcpu struct are hidden in the document. *)

(* begin hide *)

Definition print_vcpu_struct
           (vcpu_struct: VCPU_struct) :=
  match vcpu_struct with
  | mkVCPU_struct cpu_id vm_id vcpu_regs
    => let cpu_id_str := match cpu_id with
                        | None => "No CPU Connected"
                        | Some cpu_id' => HexString.of_Z  cpu_id'
                        end in
      let vm_id_str := match vm_id with
                       | None => "No VM Connected"
                       | Some vm_id' => HexString.of_Z vm_id'
                       end in
      let vcpu_regs_str :=
          print_FFA_value_type vcpu_regs.(regs) in
      append_all
        [newline;
        "VCPU value:"; newline;
        tabspace; "CPU ID: "; cpu_id_str; newline;
        tabspace; "VM ID: "; vm_id_str; newline;
        tabspace; "Reg value: "; vcpu_regs_str; newline]
  end.

Instance vcpu_struct_Showable:
  Showable VCPU_struct := { show := print_vcpu_struct }.

(* end hide *)


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
    (** - Extract state *)
    st <- trigger GetState;;

    (** - Check validities *)
    (** - Check whether the current running entity is one of VMs *)
    check "save_regs_to_vcpu: Wrong cur entity id" ,
    (decide (st.(is_hvc_mode) = false) && (in_dec zeq st.(cur_user_entity_id) vm_ids))
      
      (** - Extracts the VM userspace information with the given entity ID *)
      ;;; get "save_regs_to_vcpu: cannot find vm_userspace for the entity id",
    vm_userspace
    <- (ZTree.get st.(cur_user_entity_id) st.(vms_userspaces))
        
        (** - Get the current VCPU index for the VM *)        
        ;;; get "save_regs_to_vcpu: cannot find vcpu_index information of the vm userspace",
    cur_vcpu_index
    <- (vm_userspace.(vm_userspace_context).(cur_vcpu_index))
        
        (** - Copy the VCPU register information to the kernel to perform hypervisor calls *)
        ;;; get (append_all ["save_regs_to_vcpu: cannot find vcpu information for ";
                HexString.of_Z cur_vcpu_index]) ,
    cur_vcpu_regs
    <- (ZTree.get cur_vcpu_index
                 (vm_userspace.(vm_userspace_context).(vcpus_contexts)))
        ;;; get "save_regs_to_vcpu: cannot find vm context",
    vm_context
    <- (ZTree.get st.(cur_user_entity_id) st.(hypervisor_context).(vms_contexts))
        ;;;
        check "save_regs_to_vcpu: inconsistency between saved context and user context",
    (decide (list_eq_dec zeq (vm_context.(vm_kernelspace_context).(vcpus)) 
                         (vm_userspace.(vm_userspace_context).(vcpus))) &&
     decide (cur_vcpu_regs.(vm_id) = Some st.(cur_user_entity_id)))
      (** - Trigger transitions in the state *)
      ;;; let new_vm_context :=
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
          
          trigger (SetState new_st).
 
  Definition save_regs_to_vcpu_call (args : list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val)  :=
    match args with
    | nil => save_regs_to_vcpu_spec;;
            Ret (Vnull, args)
    | _ => triggerUB "save_regs_to_vcpu: wrong arguments"
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
    check "vcpu_restore_and_run: wrong cur entity id" ,
    (decide (st.(is_hvc_mode) = true) && (in_dec zeq next_vm_id vm_ids))
      ;;; (** get the userspace information *)
      get "vcpu_restore_and_run: Cannot find userspace information",
    vm_userspace
    <- (ZTree.get next_vm_id st.(vms_userspaces))
        ;;; (** get vm context to restore the userspace information *)
      get "vcpu_restore_and_run: Cannot find vm context",
    vm_context
    <- (ZTree.get next_vm_id st.(hypervisor_context).(vms_contexts))
        ;;;  (** get vcpu register information *)
        get  "vcpu_restore_and_run: Cannot find vcpu index from kernel vm context",
    cur_kernel_vcpu_index
    <- (vm_context.(vm_kernelspace_context).(cur_vcpu_index))
        ;;; get  "vcpu_restore_and_run: cannot find vcpu index from user vm context",
    cur_user_vcpu_index
    <- (vm_userspace.(vm_userspace_context).(cur_vcpu_index))        
        ;;; get
        (append_all ["vcpu_restore_and_run: Extract the curretnt vcpu context ";
                    HexString.of_Z next_vm_id; " ";
                    HexString.of_Z cur_kernel_vcpu_index; " ";
                    HexString.of_Z cur_user_vcpu_index; " "]),
    cur_vcpu_regs
    <- (ZTree.get cur_user_vcpu_index
                 (vm_context.(vm_kernelspace_context).(vcpus_contexts)))
        ;;;
        check "vcpu_restore_and_run: inconsistency between kernel vm context and user vm context" ,
    (decide (list_eq_dec zeq (vm_context.(vm_kernelspace_context).(vcpus))
                         vm_userspace.(vm_userspace_context).(vcpus)) &&
     decide (cur_kernel_vcpu_index = cur_user_vcpu_index) &&
     decide (cur_vcpu_regs.(vm_id) = Some next_vm_id))
      ;;; 
      (* TODO: add cpu connection check with vcpu_regs later *)
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
      trigger (SetState new_st). 
  
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
  
  (** Function dispatch. It dispatch the proper specification based on 
      the value in the VCPU context *)
      
  Notation HypervisorEE := (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).
  
  Definition dispatch_ffa_function
             (ffa_function_type: FFA_FUNCTION_TYPE)
             (vid: ffa_UUID_t)
             (vals: ZMap.t Z) (st : AbstractState) :=
    match ffa_function_type with
      (**  - FFA_MEM_DONATE gets four arguments.
             See FFAMemoryHypCallAdditionalSteps.v for more details.
             - Total length
             - Fragment length
             - Address
             - Page count *)
    | FFA_MEM_DONATE 
      => ffa_mem_donate_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                            (ZMap.get 3 vals) (ZMap.get 4 vals) st
      (**  - FFA_MEM_LEND gets four arguments.
             See FFAMemoryHypCallAdditionalSteps.v for more details.
             - Total length
             - Fragment length
             - Address
             - Page count *)
    | FFA_MEM_LEND
      => ffa_mem_lend_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                          (ZMap.get 3 vals) (ZMap.get 4 vals) st
      (**  - FFA_MEM_SHARE gets four arguments.
             See FFAMemoryHypCallAdditionalSteps.v for more details.
             - Total length
             - Fragment length
             - Address
             - Page count *)
    | FFA_MEM_SHARE
      => ffa_mem_share_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                           (ZMap.get 3 vals) (ZMap.get 4 vals) st
      (**  - FFA_MEM_RETREIVE_REQ gets four arguments.
             See FFAMemoryHypCallAdditionalSteps.v for more details.
             - Total length
             - Fragment length
             - Address
             - Page count *)
    | FFA_MEM_RETREIVE_REQ
      => ffa_mem_retrieve_req_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                                  (ZMap.get 3 vals) (ZMap.get 4 vals) st
      (**  - FFA_MEM_RETREIVE_RESP gets two arguments.
             See FFAMemoryHypCallAdditionalSteps.v for more details.
             - Total length
             - Fragment length *)
    | FFA_MEM_RETREIVE_RESP
      => ffa_mem_retrieve_resp_spec vid (ZMap.get 1 vals)
                                   (ZMap.get 2 vals) st
      (**  - FFA_MEM_RETREIVE_RESP doesn't have any arguments.
             See FFAMemoryHypCallAdditionalSteps.v for more details. *)
    | FFA_MEM_RELINQUISH 
      => ffa_mem_relinquish_spec vid st
      (**  - FFA_MEM_RECLAIM gets three arguments.
             See FFAMemoryHypCallAdditionalSteps.v for more details.
             - Handle (first half)
             - Handle (second half)
             - Falgs *)
    | FFA_MEM_RECLAIM
      => ffa_mem_reclaim_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                             (ZMap.get 3 vals) st
    end.

  Definition wrong_dispatch_ffa_function
             (ffa_function_type: FFA_FUNCTION_TYPE)
             (vid: ffa_UUID_t)
             (vals: ZMap.t Z) (st : AbstractState) :=
    match ffa_function_type with
      (**  - FFA_MEM_DONATE gets four arguments.
             See FFAMemoryHypCallAdditionalSteps.v for more details.
             - Total length
             - Fragment length
             - Address
             - Page count *)
    | FFA_MEM_DONATE 
      => ffa_mem_donate_wrong_spec vid (ZMap.get 1 vals) (ZMap.get 2 vals)
                                  (ZMap.get 3 vals) (ZMap.get 4 vals) st
    | _ => dispatch_ffa_function ffa_function_type vid vals st
    end.
  

  (** In Hafnium: Defined in "inc/hf/ffa_internal.h" *)
  Definition ffa_error (ffa_error_code: FFA_ERROR_CODE_TYPE) : FFA_value_type :=
    let error_z_value := 
        match ffa_error_code with
        | FFA_NOT_SUPPORTED _ => -1
        | FFA_INVALID_PARAMETERS _ => -2 
        | FFA_NO_MEMORY _ => -3
        | FFA_BUSY _ => -4
        | FFA_INTERRUPTED _ => -5
        | FFA_DENIED _ => -6
        | FFA_RETRY _ => -7
        | FFA_ABORTED _ => -8
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


  Notation dispatch_ffa_function_type :=
    (FFA_FUNCTION_TYPE -> ffa_UUID_t -> ZMap.t Z -> AbstractState -> RESULT (AbstractState * FFA_RESULT_CODE_TYPE))%type.
  
  Definition ffa_dispatch_spec (dispatch_func : dispatch_ffa_function_type)
    :  itree HypervisorEE (bool) := 
    (** - Extract the current vcpu *)
    st <- trigger GetState;;
    (** - Get the information in tpidr_el2 register to find out the current VM to be served *)
    get "ffa_dispatch: vcpu value is not proper",
    vcpu_regs
    <- (st.(hypervisor_context).(tpidr_el2))
        ;;;
        match vcpu_regs with
        | mkVCPU_struct (Some cid) (Some vid) arch_regs =>
          match arch_regs with
          | mkArchRegs (mkFFA_value_type func_type vals) =>
            match func_type with
            | FFA_FUNCTION_IDENTIFIER ffa_function_type =>
              (** - Find out the result of the FFA ABI calls by using the proper handling functions *)

              let new_st := st {system_log: st.(system_log)
                                                 ++(DispathFFAInterface arch_regs)::nil} in     
              match dispatch_func ffa_function_type vid vals new_st with
              | SUCCESS result =>
                match result with
                | (updated_st, ffa_result) =>
                  (** - Set the result inside the updated state *)
                  get "ffa_dispatch: error in getting vm_context",
                  vm_context
                  <- (ZTree.get
                       vid
                       updated_st.(hypervisor_context).(vms_contexts))
                      ;;; get "ffa_dispatch: error in getting vcpu index",
                  cur_kernel_vcpu_index
                  <- (vm_context.(vm_kernelspace_context).(cur_vcpu_index))
                      ;;; get "ffa_dispatch: error in getting saved vcpu index",
                  vcpu_reg
                  <- (ZTree.get cur_kernel_vcpu_index 
                               vm_context.(vm_kernelspace_context).(vcpus_contexts))
                      ;;; let new_vcpu_reg :=
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
                          trigger (SetState new_st);;
                          Ret (new_st.(is_hvc_mode))
                end
              | FAIL msg => triggerUB msg
              end
            | _ => triggerUB "ffa_dispatch_spec: function identifier is not proper"
            end
          end
        | _ => triggerUB "ffa_dispatch_spec: erros in vcpu struct value"
        end.
  
  Definition ffa_dispatch_call (args : list Lang.val) 
    : itree HypervisorEE (Lang.val * list Lang.val)  :=
    match args with
    | nil =>
      result <- (ffa_dispatch_spec dispatch_ffa_function);;
      let val := match result with 
                 | true => Vcomp (Vlong (Int64.repr 1))
                 | _ => Vcomp (Vlong (Int64.repr 0))
                 end in
      Ret (val, args)
    | _ => triggerUB "ffa_dispatch_call: wrong arguments"
    end.

  Definition wrong_ffa_dispatch_call (args : list Lang.val) 
    : itree HypervisorEE (Lang.val * list Lang.val)  :=
    match args with
    | nil =>
      result <- (ffa_dispatch_spec wrong_dispatch_ffa_function);;
      let val := match result with 
                 | true => Vcomp (Vlong (Int64.repr 1))
                 | _ => Vcomp (Vlong (Int64.repr 0))
                 end in
      Ret (val, args)
    | _ => triggerUB "wrong_ffa_dispatch_call: wrong arguments"
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


  (***********************************************************************)
  (** ***      Address translation                                       *)
  (***********************************************************************)  
  (** Memory load and store operations *)
  Definition stage2_get_physical_address_spec (st: AbstractState) (addr : ffa_address_t)
  : itree HypervisorEE (ffa_UUID_t) := 
    match stage2_address_translation_table addr with
    | Some res =>
      let page_num := Z.div res granuale in
      match
        ZTree.get page_num st.(hypervisor_context).(mem_properties).(mem_global_properties) with
      | Some property =>
        match property.(accessible_by) with
        | ExclusiveAccess accessor
          => check "stage2_address_translation_table error",
            (decide (st.(cur_user_entity_id) = accessor))
              ;;; Ret (res)
        | SharedAccess accessors
          => check "stage2_address_translation_table error",
            (in_dec zeq (st.(cur_user_entity_id)) accessors)
              ;;; Ret (res)
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
    then stage2_get_physical_address_spec st addr
    else if st.(use_stage1_table)
         then
           get "stage1_address_translation_table error",
           res'
           <- (stage1_address_translation_table st.(cur_user_entity_id) addr)
               ;;; stage2_get_physical_address_spec st res'
         else stage2_get_physical_address_spec st addr.
  
  Definition get_physical_address_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong addr))]  =>
      res <- get_physical_address_spec (Int64.unsigned addr) ;;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "get_physical_address_call: wrong arguments"
    end.

  (***********************************************************************)
  (** ***      Logical flag changes                                      *)
  (***********************************************************************)  

  Definition set_is_hvc_mode_spec
    : itree HypervisorEE (unit) := 
    st <- trigger GetState;;
    check "set_is_hvc_mode: invalid mode",
    (negb st.(is_hvc_mode))
      ;;; trigger (SetState (st {is_hvc_mode : true})).

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
    check "unset_is_hvc_mode: invalid mode",
    (st.(is_hvc_mode))
      ;;; trigger (SetState (st {is_hvc_mode : false})).

  Definition unset_is_hvc_mode_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | []  => unset_is_hvc_mode_spec;;
            Ret (Vnull, args)
    | _ => triggerNB "unset_is_hvc_mode_call: wrong arguments"
    end.

  Definition is_hvc_mode_getter_spec
    : itree HypervisorEE (Z) := 
    st <- trigger GetState;;
    if (st.(is_hvc_mode)) then Ret (1) else Ret (0).
                                              
  Definition is_hvc_mode_getter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | []  =>
      res <- is_hvc_mode_getter_spec;;
      Ret (Vcomp (Vlong (Int64.repr res)), args)
    | _ => triggerNB "unset_is_hvc_mode_call: wrong arguments"
    end.
  
  Definition set_use_stage1_table_spec
    : itree HypervisorEE (unit) := 
    st <- trigger GetState;;
    check "set_use_stage1_table: invalid mode",
    (negb st.(use_stage1_table))
      ;;; trigger (SetState (st {use_stage1_table : true})).

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
    check "unset_use_stage1_table: invalid mode",
    (st.(use_stage1_table))
      ;;; trigger (SetState (st {use_stage1_table : false})).

  Definition unset_use_stage1_table_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | []  => unset_use_stage1_table_spec;;
            Ret (Vnull, args)
    | _ => triggerNB "unset_use_stage2_table_call: wrong arguments"
    end.

  (***********************************************************************)
  (** ***      Setter/Getter for buffer                                   *)
  (***********************************************************************)
  
  Definition set_buffer_spec
             (receiver: ffa_UUID_t)
             (size : Z)
             (msg : ffa_buffer_msg_t)
             (recv_func : FFA_FUNCTION_TYPE) 
    : itree HypervisorEE (unit) := 
    state <- trigger GetState;;
    check "set_buffer: invalid receiver",
    (decide (in_dec zeq receiver entity_list))
      ;;;
      let sender := state.(cur_user_entity_id) in
      let receiver_buffer_id :=
          if decide (receiver = hypervisor_id) then sender else receiver in 
      get (append_all ["set_buffer: error in getting vm_context";
                      HexString.of_Z receiver_buffer_id]),
      vm_context
      <- (ZTree.get receiver_buffer_id state.(hypervisor_context).(vms_contexts))
          ;;;
          let buffer_contents := mkBUFFER_struct 
                                    msg (Some sender) size (Some recv_func) in
          let new_vm_context := vm_context {vm_buffer : buffer_contents} in
          let new_vm_contexts :=
              ZTree.set receiver_buffer_id new_vm_context
                        state.(hypervisor_context).(vms_contexts) in
          trigger (SetState (state {hypervisor_context / vms_contexts : new_vm_contexts}
                                   {system_log: (SetBuffer sender receiver buffer_contents)
                                                  ::(state.(system_log))})).
    
  Definition set_buffer_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong receiver)); (Vcomp (Vlong size)); (Vabs buffer_msg); (Vabs recv_func)] =>
        match downcast buffer_msg ffa_buffer_msg_t, downcast recv_func FFA_FUNCTION_TYPE with
        | Some msg, Some func_type =>
          res <- set_buffer_spec (Int64.unsigned receiver) (Int64.unsigned size) msg func_type ;;
          Ret (Vnull, args)
        | _, _ => triggerNB "set_buffer_call: impossible conversion"
        end
    | _ => triggerNB "set_buffer_call: wrong arguments"
    end.

  Definition get_buffer_spec
    : itree HypervisorEE (FFAMemoryHypCallState.ffa_buffer_msg_t) :=
    st <- trigger GetState;;
    let current_vm_id := st.(cur_user_entity_id) in
    get "get_buffer: error in getting vm_context",
    vm_context
    <- (ZTree.get current_vm_id st.(hypervisor_context).(vms_contexts))
        ;;; Ret (vm_context.(buffer).(message)).
  
  Definition get_buffer_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      res <- get_buffer_spec;;  
      Ret (Vabs (upcast res), args)
    | _ => triggerNB "get_buffer_call: wrong arguments"
    end.
  
  (***********************************************************************)
  (** ***      Setter/Getter for buffer with ID                           *)
  (***********************************************************************)

  Definition set_buffer_with_sender_id_spec
             (sender: ffa_UUID_t)
             (receiver: ffa_UUID_t)
             (size : Z)
             (msg : ffa_buffer_msg_t)
             (recv_func : FFA_FUNCTION_TYPE) 
    : itree HypervisorEE (unit) := 
    state <- trigger GetState;;
    check "set_buffer_with_sender: invalid sender and/or receiver" ,
    (decide (in_dec zeq sender entity_list) && decide (in_dec zeq receiver entity_list))
      ;;; let sender := state.(cur_user_entity_id) in
          let receiver_buffer_id :=
              if decide (receiver = hypervisor_id) then sender else receiver in 
          get (append_all ["set_buffer_with_sender: error in getting vm_context";
                          HexString.of_Z receiver_buffer_id]),
          vm_context
          <- (ZTree.get receiver_buffer_id state.(hypervisor_context).(vms_contexts))
              ;;;
              let buffer_contents := mkBUFFER_struct 
                                       msg (Some sender) size (Some recv_func) in
              let new_vm_context := vm_context {vm_buffer : buffer_contents} in
              let new_vm_contexts :=
                  ZTree.set receiver_buffer_id new_vm_context
                            state.(hypervisor_context).(vms_contexts) in
              trigger (SetState (state {hypervisor_context / vms_contexts : new_vm_contexts}
                                       {system_log: (SetBuffer sender receiver buffer_contents)
                                                      ::(state.(system_log))})).
    
  Definition  set_buffer_with_sender_id_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong sender)); (Vcomp (Vlong receiver)); (Vcomp (Vlong size));
      (Vabs buffer_msg); (Vabs recv_func)] =>
      match downcast buffer_msg ffa_buffer_msg_t,
            downcast recv_func FFA_FUNCTION_TYPE with
        | Some msg, Some func_type =>
          res <- set_buffer_with_sender_id_spec
                  (Int64.unsigned sender)
                  (Int64.unsigned receiver)
                  (Int64.unsigned size) msg func_type ;;
          Ret (Vnull, args)
        | _, _ => triggerNB "set_buffer_with_sender_call: impossible conversion"
        end
    | _ => triggerNB "set_buffer_with_sender_call: wrong arguments"
    end.

  Definition get_buffer_with_receiver_id_spec (receiver: ffa_UUID_t)
    : itree HypervisorEE (FFAMemoryHypCallState.ffa_buffer_msg_t) :=
    st <- trigger GetState;;
    check "get_buffer: invalid receiver",
    (decide (in_dec zeq receiver vm_ids))
      ;;;    
      get "get_buffer: error in getting vm_context",
    vm_context
    <- (ZTree.get receiver st.(hypervisor_context).(vms_contexts))
        ;;; Ret (vm_context.(buffer).(message)).
  
  Definition get_buffer_with_receiver_id_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong receiver))] =>
      res <- get_buffer_with_receiver_id_spec (Int64.unsigned receiver);;  
      Ret (Vabs (upcast res), args)
    | _ => triggerNB "get_buffer_call: wrong arguments"
    end.
  
End InterfaceFunctions.

(***********************************************************************)
(** **    FFA Memory Management Interface Module                       *)
(***********************************************************************)
Section MemSetterGetter.

  (***********************************************************************)
  (** ***    Global property getter / setter                             *)
  (***********************************************************************)
  Definition global_properties_getter_spec
             (page_num: Z)
  : itree HypervisorEE (MemGlobalProperties) :=
    st <- trigger GetState;;
    check "global_properties_getter: page number out of range",
    (decide (page_low <= page_num)%Z && decide (page_num < page_high)%Z)
      ;;; get "global_properties_getter_spec: no properties in the map",
    v <- ZTree.get
          page_num
          st.(hypervisor_context).(mem_properties)
        .(mem_global_properties)
           ;;; Ret (v).

  Definition global_properties_getter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong page_num))] =>
      res <- global_properties_getter_spec (Int64.unsigned page_num) ;;
      Ret (Vabs (upcast res), args)
    | _ => triggerNB "global_properties_getter: wrong arguments"
    end.
  
  Definition global_properties_setter_spec
             (page_num: Z)
             (global_properties: MemGlobalProperties) 
    : itree HypervisorEE (unit) :=
    st <- trigger GetState ;;
    check "global_properties_setter: page number out of range",
    (decide (page_low <= page_num)%Z && decide (page_num < page_high)%Z)
      ;;; let mem_props := st.(hypervisor_context).(mem_properties) in
          let new_mem_global_props_pool
              := ZTree.set page_num global_properties
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
      | _ => triggerNB "global_properties_setter: impossible conversion"
      end
    | _ => triggerNB "global_properties_setter: wrong arguments"
    end.

  (***********************************************************************)
  (** ***    Local property getter / setter                              *)
  (***********************************************************************)  
  Definition local_properties_getter_spec
             (owner : ffa_UUID_t) (page_num: Z)
    : itree HypervisorEE (MemLocalProperties) :=
    st <- trigger GetState;;
    check "local_properties_getter: page number out of range",
    (decide (page_low <= page_num)%Z && decide (page_num < page_high)%Z)
      ;;; get "local_properties_getter: no local property pool in the map",
    local_props_pool
    <- (ZTree.get
         owner
         st.(hypervisor_context).(mem_properties)
       .(mem_local_properties))
        ;;; get "local_properties_getter: no properties in the map",
    value
    <- (ZTree.get page_num local_props_pool)
        ;;; Ret(value).

  Definition local_properties_getter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong owner)); (Vcomp (Vlong page_num))] =>
      res <-  local_properties_getter_spec (Int64.unsigned owner) (Int64.unsigned page_num) ;;
      Ret (Vnull, args)
    | _ => triggerNB "local_properties_getter: wrong arguments"
    end.

  Definition local_properties_setter_spec
             (owner : ffa_UUID_t) (page_num: Z)
             (local_properties: MemLocalProperties)
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    check "local_properties_setter: page number out of range",
    (decide (page_low <= page_num)%Z && decide (page_num < page_high)%Z)
      ;;; get "local_properties_setter: no local property pool in the map",
    local_props_local_pool
    <- (ZTree.get
         owner
         st.(hypervisor_context).(mem_properties)
       .(mem_local_properties))
        ;;;     
        let new_local_props :=
            ZTree.set page_num local_properties 
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
                                 / mem_properties: new_mem_props})).

  Definition local_properties_setter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong owner));(Vcomp (Vlong page_num)); (Vabs local_properties)] =>
      match downcast local_properties MemLocalProperties with
      | Some local_props =>
        local_properties_setter_spec (Int64.unsigned owner)
                                 (Int64.unsigned page_num) local_props;;
        Ret (Vnull, args)
      | _ => triggerNB "local_properties_setter: impossible conversion"
      end
    | _ => triggerNB "local_properties_setter: wrong arguments"
    end.

  (***********************************************************************)
  (** ***  Set / clean mem dirty + mem dirty getter                      *)
  (***********************************************************************)
  
  Definition set_mem_dirty_spec (writer: ffa_UUID_t) (page_num: Z)
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    match ZTree.get
            page_num
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
              page_num new_global_prop 
              st.(hypervisor_context).(mem_properties)
            .(mem_global_properties) in
        let new_mem_props :=
            mkMemProperties 
              new_global_props
              st.(hypervisor_context).(mem_properties)
            .(mem_local_properties) in
        trigger (SetState (st {hypervisor_context
                                 / mem_properties: new_mem_props}))
    | _ => triggerNB "set_mem_dirty: cannot find property"
    end.

  Definition set_mem_dirty_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong writer)); (Vcomp (Vlong addr))] =>
      set_mem_dirty_spec (Int64.unsigned writer) (Int64.unsigned addr) ;;
      Ret (Vnull, args)
    | _ => triggerNB "set_mem_dirty_call: wrong arguments"
    end.

  Definition clean_mem_dirty_spec (writer: ffa_UUID_t) (page_num: Z)
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    match ZTree.get
            page_num
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
              page_num new_global_prop 
              st.(hypervisor_context).(mem_properties)
            .(mem_global_properties) in
        let new_mem_props :=
            mkMemProperties 
              new_global_props
              st.(hypervisor_context).(mem_properties)
            .(mem_local_properties) in
        trigger (SetState (st {hypervisor_context
                                 / mem_properties: new_mem_props}))
    | _ => triggerNB "clean_mem_dirty: cannot find property"
    end.

  Definition clean_mem_dirty_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong writer)); (Vcomp (Vlong addr))] =>
      clean_mem_dirty_spec (Int64.unsigned writer) (Int64.unsigned addr) ;;
      Ret (Vnull, args)
    | _ => triggerNB "set_mem_dirty_call: wrong arguments"
    end.

  Definition mem_dirty_getter_spec (writer: ffa_UUID_t) (page_num: Z)
    : itree HypervisorEE (MEM_DIRTY_TYPE) :=
    st <- trigger GetState;;
    match ZTree.get
            page_num
            st.(hypervisor_context).(mem_properties)
          .(mem_global_properties) with
    | Some (mkMemGlobalProperties is_ns owner access inst_access
                                  data_access mem_attr mem_dirty)
      => Ret (mem_dirty)
    | _ => triggerNB "clean_mem_dirty: cannot find property"
    end.

  Definition mem_dirty_getter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong writer)); (Vcomp (Vlong addr))] =>
      res <- mem_dirty_getter_spec (Int64.unsigned writer) (Int64.unsigned addr) ;;
      Ret (Vabs (upcast res), args)
    | _ => triggerNB "set_mem_dirty_call: wrong arguments"
    end.

End MemSetterGetter.
  
Section EntityIDSetterGetter.
  (***********************************************************************)
  (** *** current entity id getter / setter                              *)
  (***********************************************************************)
  
  Definition current_entity_id_getter_spec
    : itree HypervisorEE (ffa_UUID_t) :=
    st <- trigger GetState;;
    if (st.(is_hvc_mode)) then Ret (hypervisor_id)
    else Ret (st.(cur_user_entity_id)).

  Definition  current_entity_id_getter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      entity_id <- current_entity_id_getter_spec;;
      Ret (Vcomp (Vlong (Int64.repr entity_id)), args)
    | _ => triggerNB "get_current_entity_id_call: wrong arguments"
    end.
  
  Definition current_entity_id_setter_spec
             (entity_id : ffa_UUID_t)
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    check "current_entity_id_setter_spec: invalid input",
    (decide (in_dec zeq entity_id vm_ids))
      ;;; trigger (SetState (st {cur_user_entity_id: entity_id})).

  Definition current_entity_id_setter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong entity_id)] =>
      current_entity_id_setter_spec (Int64.unsigned entity_id);;
      Ret (Vnull, args)
    | _ => triggerNB "get_current_entity_id_call: wrong arguments"
    end.
  
End EntityIDSetterGetter.
  
Section VCPUSetterGetter.

  (***********************************************************************)
  (** ***  userspace vcpu index getter / setter                          *)
  (***********************************************************************)
  Definition userspace_vcpu_index_getter_spec
    : itree HypervisorEE (ffa_VCPU_ID_t) :=
    st <- trigger GetState;;
    check "userspace_vcpu_index_getter: invalid mode for this operation",
    (negb st.(is_hvc_mode))
      ;;;
      let cur_user_entity_id :=
          (st.(cur_user_entity_id)) in
      get "userspace_vcpu_index_getter: current user vm context does not exist",
      cur_user_vm_context
      <- (ZTree.get cur_user_entity_id
                   st.(vms_userspaces))
          ;;; get "userspace_vcpu_index_getter: current user vcpu id is invalid",
      cur_user_vcpu_id
      <- (cur_user_vm_context.(vm_userspace_context).(cur_vcpu_index))
          ;;; Ret (cur_user_vcpu_id).

  Definition userspace_vcpu_index_getter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      vcpu_index <- userspace_vcpu_index_getter_spec;;
      Ret (Vcomp (Vlong (Int64.repr vcpu_index)), args)
    | _ => triggerNB "userspace_vcpu_index_getter_call: wrong arguments"
    end.

  Definition userspace_vcpu_index_setter_spec
             (vcpu_index : ffa_VCPU_ID_t) 
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    check "userspace_vcpu_index_setter: invalid mode for this operation",
    (negb st.(is_hvc_mode))
      ;;;
      let cur_user_entity_id :=
          (st.(cur_user_entity_id)) in
      get "userspace_vcpu_index_setter: current user vm context does not exist",
      cur_user_vm_context
      <- (ZTree.get cur_user_entity_id
                   st.(vms_userspaces))
          ;;;
          let new_user_vm_context :=
              mkVM_USERSPACE_struct
                (mkVM_COMMON_struct
                   (Some vcpu_index)
                   (cur_user_vm_context.(vm_userspace_context).(vcpus))
                   (cur_user_vm_context.(vm_userspace_context).(vcpus_contexts))) in
          let new_vm_contexts :=
              (ZTree.set cur_user_entity_id 
                         new_user_vm_context
                         st.(vms_userspaces)) in
          let new_state := st {vms_userspaces : new_vm_contexts} in
          trigger (SetState (new_state)).

  Definition userspace_vcpu_index_setter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong value)] =>
      userspace_vcpu_index_setter_spec (Int64.unsigned value);;
      Ret (Vnull, args)
    | _ => triggerNB "userspace_vcpu_index_setter_call: wrong arguments"
    end.

  (***********************************************************************)
  (** **   userspace vcpu index getter / setter with entity id           *)
  (***********************************************************************)
  Definition userspace_vcpu_index_getter_with_entity_id_spec
             (cur_user_entity_id : ffa_UUID_t)
    : itree HypervisorEE (ffa_VCPU_ID_t) :=
    st <- trigger GetState;;
    check "userspace_vcpu_index_getter_with_entity_id: invalid mode for this operation",
    (negb st.(is_hvc_mode))
      ;;;
      check "userspace_vcpu_index_getter_with_entity_id: invalid entity ID",
    (decide (in_dec zeq cur_user_entity_id vm_ids))
      ;;;
      get "userspace_vcpu_index_getter_with_entity_id: current user vm context does not exist",
    cur_user_vm_context
    <- (ZTree.get cur_user_entity_id
                 st.(vms_userspaces))
        ;;; get "userspace_vcpu_index_getter_with_entity_id: current user vcpu id is invalid",
    cur_user_vcpu_id
    <- (cur_user_vm_context.(vm_userspace_context).(cur_vcpu_index))
        ;;; Ret (cur_user_vcpu_id).

  Definition userspace_vcpu_index_getter_with_entity_id_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong entity_id))] =>
      vcpu_index <- userspace_vcpu_index_getter_with_entity_id_spec
                     (Int64.unsigned entity_id);;
      Ret (Vcomp (Vlong (Int64.repr vcpu_index)), args)
    | _ => triggerNB "userspace_vcpu_index_getter_with_entity_id_call: wrong arguments"
    end.

  Definition userspace_vcpu_index_setter_with_entity_id_spec
             (cur_user_entity_id: ffa_UUID_t)
             (vcpu_index : ffa_VCPU_ID_t) 
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    check "userspace_vcpu_index_setter_with_entity_id: invalid mode for this operation",
    (negb st.(is_hvc_mode))
      ;;;
      check "userspace_vcpu_index_setter_with_entity_id: invalid entity ID",
    (decide (in_dec zeq cur_user_entity_id vm_ids))
      ;;;
      get "userspace_vcpu_index_setter_with_entity_id: current user vm context does not exist",
    cur_user_vm_context
    <- (ZTree.get cur_user_entity_id
                 st.(vms_userspaces))
        ;;;
        let new_user_vm_context :=
            mkVM_USERSPACE_struct
              (mkVM_COMMON_struct
                 (Some vcpu_index)
                 (cur_user_vm_context.(vm_userspace_context).(vcpus))
                 (cur_user_vm_context.(vm_userspace_context).(vcpus_contexts))) in
        let new_vm_contexts :=
            (ZTree.set cur_user_entity_id 
                       new_user_vm_context
                       st.(vms_userspaces)) in
        let new_state := st {vms_userspaces : new_vm_contexts} in
        trigger (SetState (new_state)).

  Definition userspace_vcpu_index_setter_with_entity_id_call
             (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong entity_id); Vcomp (Vlong value)] =>
      userspace_vcpu_index_setter_with_entity_id_spec
        (Int64.unsigned entity_id) (Int64.unsigned value);;
      Ret (Vnull, args)
    | _ => triggerNB "userspace_vcpu_index_setter_with_entity_id_call: wrong arguments"
    end.  
  
  (***********************************************************************)
  (** **   kernel vcpu index getter / setter with entity id              *)
  (***********************************************************************)
  Definition kernel_vcpu_index_getter_with_entity_id_spec
             (cur_user_entity_id : ffa_UUID_t)
    : itree HypervisorEE (ffa_VCPU_ID_t) :=
    st <- trigger GetState;;
    check "kernel_vcpu_index_getter_with_entity_id: invalid entity ID",
    (decide (in_dec zeq cur_user_entity_id vm_ids))
      ;;;
      get "kernel_vcpu_index_getter_with_entity_id: current user vm context does not exist",
    cur_kernel_vm_context
    <- (ZTree.get cur_user_entity_id
                 st.(hypervisor_context).(vms_contexts))
        ;;; get "kernel_vcpu_index_getter_with_entity_id: current user vcpu id is invalid",
    cur_kernel_vcpu_id
    <- (cur_kernel_vm_context.(vm_kernelspace_context).(cur_vcpu_index))
        ;;; Ret (cur_kernel_vcpu_id).

  Definition kernel_vcpu_index_getter_with_entity_id_call
             (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [(Vcomp (Vlong entity_id))] =>
      vcpu_index <- kernel_vcpu_index_getter_with_entity_id_spec
                     (Int64.unsigned entity_id);;
      Ret (Vcomp (Vlong (Int64.repr vcpu_index)), args)
    | _ => triggerNB "kernel_vcpu_index_getter_with_entity_id_call: wrong arguments"
    end.

  Definition kernel_vcpu_index_setter_with_entity_id_spec
             (cur_user_entity_id: ffa_UUID_t)
             (vcpu_index : ffa_VCPU_ID_t) 
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    check "kernel_vcpu_index_setter_with_entity_id: invalid entity ID",
    (decide (in_dec zeq cur_user_entity_id vm_ids))
      ;;;
      get "kernel_vcpu_index_setter_with_entity_id: current user vm context does not exist",
    cur_kernel_vm_context
    <- (ZTree.get cur_user_entity_id
                 st.(hypervisor_context).(vms_contexts))
        ;;;
        let new_kernel_vm_context :=
            mkVM_KERNEL_struct
              (mkVM_COMMON_struct
                 (Some vcpu_index)
                 (cur_kernel_vm_context.(vm_kernelspace_context).(vcpus))
                 (cur_kernel_vm_context.(vm_kernelspace_context).(vcpus_contexts)))
              cur_kernel_vm_context.(buffer) in
        let new_vm_contexts :=
            (ZTree.set cur_user_entity_id 
                       new_kernel_vm_context
                       st.(hypervisor_context).(vms_contexts)) in
        let new_state := st {hypervisor_context / vms_contexts : new_vm_contexts} in
        trigger (SetState (new_state)).

  Definition kernel_vcpu_index_setter_with_entity_id_call
             (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong entity_id); Vcomp (Vlong value)] =>
      kernel_vcpu_index_setter_with_entity_id_spec
        (Int64.unsigned entity_id) (Int64.unsigned value);;
      Ret (Vnull, args)
    | _ => triggerNB "kernel_vcpu_index_setter_with_entity_id_call: wrong arguments"
    end.
  
  (***********************************************************************)
  (** **   userspace vcpu getter / setter                                *)
  (***********************************************************************)
  Definition userspace_vcpu_struct_getter_spec
    : itree HypervisorEE (VCPU_struct) :=
      st <- trigger GetState;;
      check "userspace_vcpu_struct_getter: invalid mode for this operation",
      (negb st.(is_hvc_mode))
        ;;;
        let cur_user_entity_id :=
            (st.(cur_user_entity_id)) in
        get "userspace_vcpu_struct_getter: current user vm context does not exist",
        cur_user_vm_context
        <- (ZTree.get cur_user_entity_id
                     st.(vms_userspaces))
            ;;; get "userspace_vcpu_struct_getter: current user vcpu id is invalid",
        cur_user_vcpu_id
        <- (cur_user_vm_context.(vm_userspace_context).(cur_vcpu_index))
            ;;; get "userspace_vcpu_struct_getter: does not have vcpu values",
        cur_vcpu_values 
        <- (ZTree.get
             cur_user_vcpu_id
             (cur_user_vm_context.(vm_userspace_context).(vcpus_contexts)))
            ;;; Ret (cur_vcpu_values).
  
  Definition userspace_vcpu_struct_getter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      vcpu_values<- userspace_vcpu_struct_getter_spec;;
      Ret (Vabs (upcast vcpu_values), args)
    | _ => triggerNB "userspace_vcpu_struct_getter_call: wrong arguments"
    end.
  
  Definition userspace_vcpu_struct_setter_spec (vcpu_values: VCPU_struct)
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    check "userspace_vcpu_struct_setter: invalid mode for this operation",
    (negb st.(is_hvc_mode))
      ;;;
      let cur_user_entity_id :=
          (st.(cur_user_entity_id)) in
      get "userspace_vcpu_struct_setter: current user vm context does not exist",
      cur_user_vm_context
      <- (ZTree.get cur_user_entity_id
                   st.(vms_userspaces))
          ;;; get "userspace_vcpu_struct_setter: current user vcpu id is invalid",
      cur_user_vcpu_id
      <- (cur_user_vm_context.(vm_userspace_context).(cur_vcpu_index))
          ;;;
          let new_vcpu_contexts :=
              (ZTree.set
                 cur_user_vcpu_id
                 vcpu_values
                 (cur_user_vm_context.(vm_userspace_context).(vcpus_contexts))) in
          let new_user_vm_contexts :=
              mkVM_USERSPACE_struct
                (mkVM_COMMON_struct
                   (Some cur_user_vcpu_id)
                   (cur_user_vm_context.(vm_userspace_context).(vcpus))
                   new_vcpu_contexts) in
          let new_vm_contexts :=
              (ZTree.set cur_user_entity_id 
                         new_user_vm_contexts
                         st.(vms_userspaces)) in
          let new_state := st {vms_userspaces : new_vm_contexts} in
          trigger (SetState (new_state)).
  
  Definition userspace_vcpu_struct_setter_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [Vabs vcpu_struct_val] =>
        match downcast vcpu_struct_val VCPU_struct with
        | Some vcpu_val =>
          userspace_vcpu_struct_setter_spec vcpu_val ;;
          Ret (Vnull, args)
        | _ => triggerNB "userspace_vcpu_struct_setter_call: impossible conversion"
        end
    | _ => triggerNB "userspace_vcpu_struct_setter_call: wrong arguments"
    end.  

  (***********************************************************************)
  (** **   userspace vcpu getter / setter with entity ID                 *)
  (***********************************************************************)  
  Definition userspace_vcpu_struct_getter_with_entity_id_spec
             (cur_user_entity_id : ffa_UUID_t)
    : itree HypervisorEE (VCPU_struct) :=
    st <- trigger GetState;;
    check "userspace_vcpu_struct_getter_with_entity_id: invalid mode for this operation",
    (negb st.(is_hvc_mode))
      ;;;
      check "userspace_vcpu_getter_with_entity_id: invalid entity ID",
    (decide (in_dec zeq cur_user_entity_id vm_ids))
      ;;;      
      get "userspace_vcpu_struct_getter_with_entity_id: 
      current user vm context does not exist",
    cur_user_vm_context
    <- (ZTree.get cur_user_entity_id
                 st.(vms_userspaces))
        ;;; get "userspace_vcpu_struct_getter_with_entity_id: 
        current user vcpu id is invalid",
    cur_user_vcpu_id
    <- (cur_user_vm_context.(vm_userspace_context).(cur_vcpu_index))
        ;;; get "userspace_vcpu_struct_getter_with_entity_id: 
        does not have vcpu values",
    cur_vcpu_values 
    <- (ZTree.get
         cur_user_vcpu_id
         (cur_user_vm_context.(vm_userspace_context).(vcpus_contexts)))
        ;;; Ret (cur_vcpu_values).
  
  Definition userspace_vcpu_struct_getter_with_entity_id_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong entity_id)] =>
      vcpu_values<- userspace_vcpu_struct_getter_with_entity_id_spec
                     (Int64.unsigned entity_id);;
      Ret (Vabs (upcast vcpu_values), args)
    | _ => triggerNB "userspace_vcpu_struct_getter_with_entity_id_call: wrong arguments"
    end.

  
  Definition userspace_vcpu_struct_setter_with_entity_id_spec
             (cur_user_entity_id: ffa_UUID_t) (vcpu_values: VCPU_struct)
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    check "userspace_vcpu_struct_setter_with_entity_id: invalid mode for this operation",
    (negb st.(is_hvc_mode))
      ;;;
      check "userspace_vcpu_struct_setter_with_entity_id: invalid entity ID",
    (decide (in_dec zeq cur_user_entity_id vm_ids))
      ;;;      
      get "userspace_vcpu_struct_setter: current user vm context does not exist",
      cur_user_vm_context
      <- (ZTree.get cur_user_entity_id
                   st.(vms_userspaces))
          ;;; get "userspace_vcpu_struct_setter_with_entity_id: current user vcpu id is invalid",
      cur_user_vcpu_id
      <- (cur_user_vm_context.(vm_userspace_context).(cur_vcpu_index))
          ;;;
          let new_vcpu_contexts :=
              (ZTree.set
                 cur_user_vcpu_id
                 vcpu_values
                 (cur_user_vm_context.(vm_userspace_context).(vcpus_contexts))) in
          let new_user_vm_contexts :=
              mkVM_USERSPACE_struct
                (mkVM_COMMON_struct
                   (Some cur_user_vcpu_id)
                   (cur_user_vm_context.(vm_userspace_context).(vcpus))
                   new_vcpu_contexts) in
          let new_vm_contexts :=
              (ZTree.set cur_user_entity_id 
                         new_user_vm_contexts
                         st.(vms_userspaces)) in
          let new_state := st {vms_userspaces : new_vm_contexts} in
          trigger (SetState (new_state)).
  
  Definition userspace_vcpu_struct_setter_with_entity_id_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong entity_id); Vabs vcpu_struct_val] =>
        match downcast vcpu_struct_val VCPU_struct with
        | Some vcpu_val =>
          userspace_vcpu_struct_setter_with_entity_id_spec
            (Int64.unsigned entity_id) vcpu_val ;;
          Ret (Vnull, args)
        | _ => triggerNB "userspace_vcpu_struct_setter_with_entity_id_call: impossible conversion"
        end
    | _ => triggerNB "userspace_vcpu_struct_setter_with_entity_id_call: wrong arguments"
    end.

  (***********************************************************************)
  (** **      kernel vcpu getter / setter with entity ID                 *)
  (***********************************************************************)  
  Definition kernel_vcpu_struct_getter_with_entity_id_spec
             (cur_user_entity_id : ffa_UUID_t)
    : itree HypervisorEE (VCPU_struct) :=
    st <- trigger GetState;;
    check "kernel_vcpu_getter_with_entity_id: invalid entity ID",
    (decide (in_dec zeq cur_user_entity_id vm_ids))
      ;;;      
      get "kernel_vcpu_struct_getter_with_entity_id: 
      current user vm context does not exist",
    cur_kernel_vm_context
    <- (ZTree.get cur_user_entity_id
                 st.(hypervisor_context).(vms_contexts))
        ;;; get "kernel_vcpu_struct_getter_with_entity_id: 
        current user vcpu id is invalid",
    cur_kernel_vcpu_id
    <- (cur_kernel_vm_context.(vm_kernelspace_context).(cur_vcpu_index))
        ;;; get "kernel_vcpu_struct_getter_with_entity_id: 
        does not have vcpu values",
    cur_vcpu_values 
    <- (ZTree.get
         cur_kernel_vcpu_id
         (cur_kernel_vm_context.(vm_kernelspace_context).(vcpus_contexts)))
        ;;; Ret (cur_vcpu_values).
  
  Definition kernel_vcpu_struct_getter_with_entity_id_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong entity_id)] =>
      vcpu_values<- kernel_vcpu_struct_getter_with_entity_id_spec
                     (Int64.unsigned entity_id);;
      Ret (Vabs (upcast vcpu_values), args)
    | _ => triggerNB "kernel_vcpu_struct_getter_with_entity_id_call: wrong arguments"
    end.
  
  Definition kernel_vcpu_struct_setter_with_entity_id_spec
             (cur_user_entity_id: ffa_UUID_t) (vcpu_values: VCPU_struct)
    : itree HypervisorEE (unit) :=
    st <- trigger GetState;;
    check "userspace_vcpu_struct_setter_with_entity_id: invalid entity ID",
    (decide (in_dec zeq cur_user_entity_id vm_ids))
      ;;;      
      get "kernel_vcpu_struct_setter: current user vm context does not exist",
      cur_kernel_vm_context
      <- (ZTree.get cur_user_entity_id
                   st.(hypervisor_context).(vms_contexts))
          ;;; get "kernel_vcpu_struct_setter_with_entity_id: current user vcpu id is invalid",
      cur_kernel_vcpu_id
      <- (cur_kernel_vm_context.(vm_kernelspace_context).(cur_vcpu_index))
          ;;;
          let new_vcpu_contexts :=
              (ZTree.set
                 cur_kernel_vcpu_id
                 vcpu_values
                 (cur_kernel_vm_context.(vm_kernelspace_context).(vcpus_contexts))) in
          let new_kernel_vm_contexts :=
              mkVM_KERNEL_struct
                (mkVM_COMMON_struct
                   (Some cur_kernel_vcpu_id)
                   (cur_kernel_vm_context.(vm_kernelspace_context).(vcpus))
                   new_vcpu_contexts)
                cur_kernel_vm_context.(buffer) in
          let new_vm_contexts :=
              (ZTree.set cur_user_entity_id 
                         new_kernel_vm_contexts
                         st.(hypervisor_context).(vms_contexts)) in
          let new_state := st {hypervisor_context / vms_contexts : new_vm_contexts} in
          trigger (SetState (new_state)).
  
  Definition kernel_vcpu_struct_setter_with_entity_id_call (args: list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [Vcomp (Vlong entity_id); Vabs vcpu_struct_val] =>
        match downcast vcpu_struct_val VCPU_struct with
        | Some vcpu_val =>
          kernel_vcpu_struct_setter_with_entity_id_spec
            (Int64.unsigned entity_id) vcpu_val ;;
          Ret (Vnull, args)
        | _ => triggerNB "kernel_vcpu_struct_setter_with_entity_id_call: impossible conversion"
        end
    | _ => triggerNB "kernel_vcpu_struct_setter_with_entity_id_call: wrong arguments"
    end.

End VCPUSetterGetter.

Section StateAndLogGetter.

  Definition state_getter_spec
  : itree HypervisorEE (AbstractState) :=
    st <- trigger GetState;;
    Ret (st).

  Definition state_getter_call (args : list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      st <- state_getter_spec;;
      Ret (Vabs (upcast st), args)
    | _ => triggerNB "state_getter_call: wrong arguments"
    end.
             

  Definition system_log_getter_spec
  : itree HypervisorEE (system_log_type) :=
    st <- trigger GetState;;
    Ret (st.(system_log)).

  Definition system_log_getter_call (args : list Lang.val)
    : itree HypervisorEE (Lang.val * list Lang.val) :=
    match args with
    | [] =>
      system_log <- system_log_getter_spec;;
      Ret (Vabs (upcast system_log), args)
    | _ => triggerNB "state_getter_call: wrong arguments"
    end.
  

End StateAndLogGetter.

(***********************************************************************)
(** **    FFA Memory Management Interface Module                       *)
(***********************************************************************)
Section FFAMemoryManagementInterfaceModule.

  Definition funcs :=
    [
      ("HVCTopLevel.save_regs_to_vcpu", save_regs_to_vcpu_call) ;
    ("HVCTopLevel.vcpu_restore_and_run", vcpu_restore_and_run_call) ;
    ("HVCTopLevel.ffa_dispatch", ffa_dispatch_call) ;
    ("HVCTopLevel.wrong_ffa_dispatch", wrong_ffa_dispatch_call) ;
    
    ("HVCTopLevel.get_physical_address", get_physical_address_call);
    ("HVCTopLevel.set_is_hvc_mode", set_is_hvc_mode_call);
    ("HVCTopLevel.unset_is_hvc_mode", unset_is_hvc_mode_call);
    ("HVCTopLevel.is_hvc_mode_getter", is_hvc_mode_getter_call);
    ("HVCTopLevel.set_use_stage1_table", set_use_stage1_table_call);
    ("HVCTopLevel.unset_use_stage1_table", unset_use_stage1_table_call);

    ("HVCToplevel.current_entity_id_getter", current_entity_id_getter_call);
    ("HVCToplevel.current_entity_id_setter", current_entity_id_setter_call);
    
    ("HVCTopLevel.set_buffer", set_buffer_call);
    ("HVCTopLevel.get_buffer", get_buffer_call);
    ("HVCTopLevel.set_buffer_with_sender_id", set_buffer_with_sender_id_call);
    ("HVCTopLevel.get_buffer_with_receiver_id", get_buffer_with_receiver_id_call);
    
    ("HVCTopLevel.global_properties_getter", global_properties_getter_call);
    ("HVCTopLevel.global_properties_setter", global_properties_setter_call);
    ("HVCTopLevel.local_properties_getter", local_properties_getter_call);
    ("HVCTopLevel.local_properties_setter", local_properties_setter_call);
    ("HVCTopLevel.set_mem_dirty", set_mem_dirty_call);
    ("HVCTopLevel.clean_mem_dirty", clean_mem_dirty_call);

    ("HVCToplevel.userspace_vcpu_index_getter", userspace_vcpu_index_getter_call);
    ("HVCToplevel.userspace_vcpu_index_setter", userspace_vcpu_index_setter_call);

    ("HVCToplevel.userspace_vcpu_index_getter_with_entity_id", userspace_vcpu_index_getter_with_entity_id_call);
    ("HVCToplevel.userspace_vcpu_index_setter_with_entity_id", userspace_vcpu_index_setter_with_entity_id_call);

    ("HVCToplevel.kernel_vcpu_index_getter_with_entity_id", kernel_vcpu_index_getter_with_entity_id_call);
    ("HVCToplevel.kernel_vcpu_index_setter_with_entity_id", kernel_vcpu_index_setter_with_entity_id_call);
    
    ("HVCTopLevel.userspace_vcpu_struct_getter", userspace_vcpu_struct_getter_call);
    ("HVCTopLevel.userspace_vcpu_struct_setter", userspace_vcpu_struct_setter_call);

    ("HVCTopLevel.userspace_vcpu_struct_getter_with_entity_id", userspace_vcpu_struct_getter_with_entity_id_call);
    ("HVCTopLevel.userspace_vcpu_struct_setter_with_entity_id", userspace_vcpu_struct_setter_with_entity_id_call);

    ("HVCTopLevel.kernel_vcpu_struct_getter_with_entity_id", kernel_vcpu_struct_getter_with_entity_id_call);
    ("HVCTopLevel.kernel_vcpu_struct_setter_with_entity_id", kernel_vcpu_struct_setter_with_entity_id_call);

    ("HVCToplevel.state_getter", state_getter_call); 
    ("HVCToplevel.system_log_getter", system_log_getter_call)
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
    (Call "HVCTopLevel.save_regs_to_vcpu" [])
      #; (Put "hyp mode after entering kernel" (Call "HVCTopLevel.is_hvc_mode_getter" []))
      #; (Put "result" (Call "HVCTopLevel.ffa_dispatch" []))
      #; (Put "function_dispatcher has be invoked" Vnull) 
      (** Jieung: I do not figure out the reason, but it is required *)
      #; (Put "hyp mode after dispatching" (Call "HVCTopLevel.is_hvc_mode_getter" []))
      #; (Call "HVCTopLevel.vcpu_restore_and_run" [])
      #; (Put "hyp mode after restore" (Call "HVCTopLevel.is_hvc_mode_getter" [])).

  Definition wrong_hypervisor_call :=
    (Call "HVCTopLevel.save_regs_to_vcpu" [])
      #; (Put "hyp mode after entering kernel" (Call "HVCTopLevel.is_hvc_mode_getter" []))
      #; (Put "result" (Call "HVCTopLevel.wrong_ffa_dispatch" []))
      #; (Put "function_dispatcher has be invoked" Vnull) 
      (** Jieung: I do not figure out the reason, but it is required *)
      #; (Put "hyp mode after dispatching" (Call "HVCTopLevel.is_hvc_mode_getter" []))
      #; (Call "HVCTopLevel.vcpu_restore_and_run" [])
      #; (Put "hyp mode after restore" (Call "HVCTopLevel.is_hvc_mode_getter" [])).

  Definition scheduling :=
    (Call "HVCTopLevel.save_regs_to_vcpu" [])
      #; (Call "HVCTopLevel.vcpu_restore_and_run" []).
  
  Definition hypervisor_callF : function.
    mk_function_tac hypervisor_call ([]: list var) ([]: list var).
  Defined.

  Definition wrong_hypervisor_callF : function.
    mk_function_tac wrong_hypervisor_call ([]: list var) ([]: list var).
  Defined.
  
  Definition schedulingF : function.
    mk_function_tac scheduling ([]: list var) ([]: list var).
  Defined.  
  
End HypervisorCall.

(***********************************************************************)
(** **    FFA Memory Management Interface Module With Mem Accessor     *)
(***********************************************************************)
Section FFAMemoryManagementInterfaceWithMemAccessorModule.

  (** Arbitrarily assign the block number for users *)
  Definition flat_mem_block_ptr := (Vptr 2%positive (Ptrofs.repr 0)).

  Definition mem_store_spec (addr value : var) (entity_id paddr : var) : stmt :=
    entity_id #= (Call "HVCToplevel.current_entity_id_getter" []) #;
              paddr #= (Call "HVCTopLevel.get_physical_address" [CBV addr]) #;
              (Call "HVCTopLevel.set_mem_dirty" [CBV entity_id; CBV (addr / (Int64.repr granuale))]) #;
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
    ("HVCTopLevel.hypervisor_call", hypervisor_callF);
    ("HVCTopLevel.wrong_hypervisor_call", wrong_hypervisor_callF);
    ("HVCTopLevel.scheduling", schedulingF)
    ].
  
  Definition top_level_accessor_modsem : ModSem := program_to_ModSem mem_funcs.
  
End FFAMemoryManagementInterfaceWithMemAccessorModule.

