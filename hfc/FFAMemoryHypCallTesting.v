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

(* From HafniumCore *)
Require Import Lang.
Require Import Any.
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
Require Export FFAMemoryHypCallTestingInterface.

Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Require Import Maps.
Set Implicit Arguments.

(* end hide *)

(*************************************************************)
(** *                Introduction                            *) 
(*************************************************************)

(** This file provides several test cases. 

    This file first includes several test cases for multiple getter/setter. 
    In addiiton, it provides simple test cases that one VM tries to donate one page
    to another VM. For those cases, this file contains not only cases 
    that succeed its operation but also cases that raise errors during the evaluation.
    By doing that, we can see how error messages are visible for our formal specifications. 

    In addiiton to the proper formal specifications, we define one specification that 
    is slightly modified to add an error in it. By doing that, we show how our test can 
    detect errors when specifications have bugs in it.
*)

(*************************************************************)
(** **   YIELD                                               *) 
(*************************************************************)

(** Utility function to add Yield in between each statement of test cases. Having yield statements 
    will provide test cases with concurrency in a limited setting (sequential consistency *)

Fixpoint INSERT_YIELD (s: stmt): stmt :=
  match s with
  | Seq s0 s1 => Seq (INSERT_YIELD s0) (INSERT_YIELD s1)
  | If c s0 s1 => If c (INSERT_YIELD s0) (INSERT_YIELD s1)
  | While c s => While c (INSERT_YIELD s)
  | _ => Yield #; s
  end
.

(*************************************************************)
(** **   Auxiliary definitions for initializations           *) 
(*************************************************************)
Section FFAMemoryHypCallInitialization.

  (** Since we assume there are four VMs in the system, we divide the entire memory (from page_low_int to page_high_int) 
    into four regions. Then, we allocate each quater into one VM *)

  (*************************************************************)
  (** ***    Address values           *) 
  (*************************************************************)

  Definition page_low_int := Int64.repr page_low.
  Definition page_quater_value :=
    ((Int64.repr page_high -  Int64.repr page_low) / (Int64.repr 4)).  
  Definition page_1st_quater_int :=
    Int64.repr page_low + page_quater_value.
  Definition page_2nd_quater_int :=
    Int64.repr page_low + (page_quater_value * (Int64.repr 2)).
  Definition page_3rd_quater_int :=
    Int64.repr page_low + (page_quater_value * (Int64.repr 3)).
  Definition page_high_int := Int64.repr page_high.


  (*************************************************************)
  (** ***    Initial values for memory property tables and vcpu            *) 
  (*************************************************************)

  (** Initial value for global memory properties. We divide the entire memory into four sub-regions. 
      Each region will be associated with one VM (VM 1, 2, 3, and 4). 
      Initial permissions and memory attributes are as follows, even though
      they can be changed quite easily. 
      - Owner: owned by each VM. 
      - accessibility: exclusive access by the owner 
      - instruction permissions: XN
      - data permissions: RW
      - memory type: normal memory with non cacheable and shareable
  *)

  Definition InitialGlobalMemAttributeValue (owner : Z) := 
    mkMemGlobalProperties false
                          (Owned owner)
                          (ExclusiveAccess owner)
                          (FFA_INSTRUCTION_ACCESS_XN)
                          (FFA_DATA_ACCESS_RW)
                          (FFA_MEMORY_NORMAL_MEM
                             FFA_MEMORY_CACHE_NON_CACHEABLE
                             FFA_MEMORY_OUTER_SHAREABLE)
                          MemClean.               
  
  Definition InitialGlobalAttributesForVMOne :=
    InitialGlobalMemAttributeValue primary_vm_id.
  
  Definition InitialGlobalAttributesForVMTwo :=
    InitialGlobalMemAttributeValue 2.

  Definition InitialGlobalAttributesForVMThree :=
    InitialGlobalMemAttributeValue 3.
  
  Definition InitialGlobalAttributesForVMFour :=
    InitialGlobalMemAttributeValue 4.

  (** Initial value of local memory properties. We set the initial local attributes as follows
      - local owner: onwed (among onwed and borrowed)  
      - instruction permissions: XN
      - data permissions: RW
      - memory type: normal memory with non cacheable and shareable
      *)
  
  Definition InitialLocalAttributes :=
    mkMemLocalProperties (LocalOwned)
                         (FFA_INSTRUCTION_ACCESS_XN)
                         (FFA_DATA_ACCESS_RW)
                          (FFA_MEMORY_NORMAL_MEM
                             FFA_MEMORY_CACHE_NON_CACHEABLE
                             FFA_MEMORY_OUTER_SHAREABLE).

  Definition InitialGlobalAttributesForVMOneDonate :=
    mkMemGlobalProperties false
                          (Owned primary_vm_id)
                          (ExclusiveAccess primary_vm_id)
                          (FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED)
                          (FFA_DATA_ACCESS_NOT_SPECIFIED)
                          (FFA_MEMORY_NOT_SPECIFIED_MEM)
                          MemClean.               

  Definition InitialLocalAttributesForDonate :=
    mkMemLocalProperties (LocalOwned)
                         (FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED)
                         (FFA_DATA_ACCESS_NOT_SPECIFIED)
                         (FFA_MEMORY_NOT_SPECIFIED_MEM).

  (** Initial value for vcpu *)  
  Definition initial_vcpu_struct (cpu_id : ffa_CPU_ID_t) (vm_id : ffa_UUID_t) :=
    (mkVCPU_struct
       (Some cpu_id)
       (Some vm_id)
       (mkArchRegs
          (mkFFA_value_type
             FFA_IDENTIFIER_DEFAULT
             (ZMap.init 0)))).

  (*************************************************************)
  (** ***    Initialization Statements           *) 
  (*************************************************************)

  (** Initialization statements. 
      It initializes the following things.
      - Global memory property pool
      - Local memory property pool for each VM
      - VCPU context values stored in the kernel (hypervisor)
      - VCPU values in userpsace
   *)

  Definition initialize_owners (cur_address initial_global_value initial_local_value : var): stmt :=
    Put "start initializaiton" (Vnull) #;
        cur_address #= page_low_int

        (** VCPU initialization for VM 1 *)
        #; (Call "HVCToplevel.kernel_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr primary_vm_id); CBV (Int64.repr primary_vm_id)])              
        #; (Call "HVCTopLevel.kernel_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr primary_vm_id); CBV (Vabs (upcast (initial_vcpu_struct 1 primary_vm_id)))])
        #; (Call "HVCToplevel.userspace_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr primary_vm_id); CBV (Int64.repr primary_vm_id)])              
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr primary_vm_id); CBV (Vabs (upcast (initial_vcpu_struct 1 primary_vm_id)))]) 

        (** VCPU initialization for VM 2 *)
        #; (Call "HVCToplevel.kernel_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr 2); CBV (Int64.repr 2)])              
        #; (Call "HVCTopLevel.kernel_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr 2); CBV (Vabs (upcast (initial_vcpu_struct 2 2)))])                            
        #; (Call "HVCToplevel.userspace_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr 2); CBV (Int64.repr 2)])              
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr 2); CBV (Vabs (upcast (initial_vcpu_struct 2 2)))]) 

        (** VCPU initialization for VM 3 *)        
        #; (Call "HVCToplevel.kernel_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr 3); CBV (Int64.repr 3)])              
        #; (Call "HVCTopLevel.kernel_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr 3); CBV (Vabs (upcast (initial_vcpu_struct 3 3)))])              
        #; (Call "HVCToplevel.userspace_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr 3); CBV (Int64.repr 3)])              
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr 3); CBV (Vabs (upcast (initial_vcpu_struct 3 3)))])              

        (** VCPU initialization for VM 4 *)        
        #; (Call "HVCToplevel.kernel_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr 4); CBV (Int64.repr 4)])                            
        #; (Call "HVCTopLevel.kernel_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr 4); CBV (Vabs (upcast (initial_vcpu_struct 4 4)))])              
        #; (Call "HVCToplevel.userspace_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr 4); CBV (Int64.repr 4)])                            
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr 4); CBV (Vabs (upcast (initial_vcpu_struct 4 4)))])                      
        #; (initial_local_value #= (Vabs (upcast InitialLocalAttributesForDonate)))

        (* Initializations for memory properties *)        
        #;
        #while (cur_address < page_1st_quater_int)
        do (
            (** Memory property initialization for the first quater of the entire memory (memory region owned by VM 1) *)
            (initial_global_value #= (Vabs (upcast InitialGlobalAttributesForVMOneDonate)))
              #; (Call "HVCTopLevel.global_properties_setter"
                       [CBV cur_address; CBV initial_global_value])
              #; (Call "HVCTopLevel.local_properties_setter"
                       [CBV (Int64.repr primary_vm_id); CBV cur_address; CBV initial_local_value])
              (* #; (Put "initialization for" cur_address) *)
              #; cur_address #= cur_address + (Int64.repr 1))
             #; (initial_local_value #= (Vabs (upcast InitialLocalAttributes)))
             #;
             (** Memory property initialization for the first quater of the entire memory (memory region owned by VM 2) *)
             #while (cur_address < page_2nd_quater_int)
             do (
                 (initial_global_value #=  (Vabs (upcast InitialGlobalAttributesForVMTwo)))
              #; (Call "HVCTopLevel.global_properties_setter"
                       [CBV cur_address; CBV initial_global_value])
              #; (Call "HVCTopLevel.local_properties_setter"
                       [CBV (Int64.repr 2); CBV cur_address; CBV initial_local_value])
              (* #; (Put "initialization for" cur_address) *) 
              #; cur_address #= cur_address + (Int64.repr 1))
             #; (initial_local_value #= (Vabs (upcast InitialLocalAttributes)))
             #;                  
             (** Memory property initialization for the first quater of the entire memory (memory region owned by VM 3) *)
             #while (cur_address < page_3rd_quater_int)
             do (
                 (initial_global_value #=  (Vabs (upcast InitialGlobalAttributesForVMThree)))
                   #; (Call "HVCTopLevel.global_properties_setter"
                            [CBV cur_address; CBV initial_global_value])
                   #; (Call "HVCTopLevel.local_properties_setter"
                            [CBV (Int64.repr 3); CBV cur_address; CBV initial_local_value])
                   (* #; (Put "initialization for" cur_address) *) 
                   #; cur_address #= cur_address + (Int64.repr 1))
                  #; (initial_local_value #= (Vabs (upcast InitialLocalAttributes)))
                  #;
                  (** Memory property initialization for the first quater of the entire memory (memory region owned by VM 4) *)
                  #while (cur_address < page_high_int)
                  do (
                      (initial_global_value #=  (Vabs (upcast InitialGlobalAttributesForVMFour)))
                        #; (Call "HVCTopLevel.global_properties_setter"
                                 [CBV cur_address; CBV initial_global_value])
                        #; (Call "HVCTopLevel.local_properties_setter"
                                 [CBV (Int64.repr 4); CBV cur_address; CBV initial_local_value])
                        (* #; (Put "initialization for" cur_address)  *)
                        #; cur_address #= cur_address + (Int64.repr 1)).

End  FFAMemoryHypCallInitialization.

(*************************************************************)
(** **   Auxiliary definitions for Memory Donate Descriptors   *) 
(*************************************************************)
Section DescriptorGenerator.

  Definition MemoryRegionConstituentGeneratorForDonate
             (address : ffa_address_t)
             (page: Z) :=
    mkFFA_memory_region_constituent_struct address page.

  Definition MemoryRegionCompositeGeneratorForDonate
             (address : ffa_address_t) (page : Z) :=
    mkFFA_composite_memory_region_struct
      page
      ((MemoryRegionConstituentGeneratorForDonate address page)::nil).
  
  Definition AccessPermissionsDescriptorGeneratorForDonate
             (receiver : ffa_UUID_t) := 
    mkFFA_memory_access_permissions_descriptor_struct
      receiver
       FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED
       FFA_DATA_ACCESS_NOT_SPECIFIED
       false.

  Definition EndpointMemoryAccessDescriptorGeneratorForDonate
             (receiver : ffa_UUID_t) := 
    mkFFA_endpoint_memory_access_descriptor_struct
      (AccessPermissionsDescriptorGeneratorForDonate receiver) 0.  
    
  Definition DonateDescriptorGenerator (sender receiver: ffa_UUID_t)
             (address :ffa_address_t) (page: Z):=
    mkFFA_memory_region_struct
      (* sender *)
      sender 
      (mkFFA_memory_region_attributes_descriptor_struct 
         (FFA_MEMORY_NOT_SPECIFIED_MEM))
      (MEMORY_REGION_FLAG_NORMAL
         (mkFFA_mem_default_flags_struct false false))
      0
      0
      ((EndpointMemoryAccessDescriptorGeneratorForDonate receiver)::nil)
      (MemoryRegionCompositeGeneratorForDonate address page).


  Definition WrongDonateDescriptorGenerator (sender receiver: ffa_UUID_t)
             (address :ffa_address_t) (page: Z):=
    mkFFA_memory_region_struct
      (* sender *)
      sender 
      (mkFFA_memory_region_attributes_descriptor_struct 
         (FFA_MEMORY_NORMAL_MEM
            FFA_MEMORY_CACHE_WRITE_BACK FFA_MEMORY_INNER_SHAREABLE))
      (MEMORY_REGION_FLAG_NORMAL
         (mkFFA_mem_default_flags_struct false false))
      0
      0
      ((EndpointMemoryAccessDescriptorGeneratorForDonate receiver)::nil)
      (MemoryRegionCompositeGeneratorForDonate address page).
  
  Definition buffer_msg
             (sender receiver: ffa_UUID_t)
             (address :ffa_address_t) (page: Z)
    := buffer_memory_region (DonateDescriptorGenerator sender receiver address page).

  Definition wrong_buffer_msg
             (sender receiver: ffa_UUID_t)
             (address :ffa_address_t) (page: Z)
    := buffer_memory_region (WrongDonateDescriptorGenerator sender receiver address page).

  Definition donate_vcpu_struct (cpu_id : ffa_CPU_ID_t) (vm_id : ffa_UUID_t)  :=
    (mkVCPU_struct
       (Some cpu_id)
       (Some vm_id)
       (mkArchRegs
          (mkFFA_value_type
             (FFA_FUNCTION_IDENTIFIER FFA_MEM_DONATE)
             (ZMap.init 0)))).

  Definition retrieve_req_vcpu_struct (cpu_id : ffa_CPU_ID_t) (vm_id : ffa_UUID_t)  :=
    (mkVCPU_struct
       (Some cpu_id)
       (Some vm_id)
       (mkArchRegs
          (mkFFA_value_type
             (FFA_FUNCTION_IDENTIFIER FFA_MEM_RETREIVE_REQ)
             (ZMap.init 0)))).
  
End DescriptorGenerator.

(*************************************************************)
(** **   Test Cases    *) 
(*************************************************************)
Module FFAMEMORYHYPCALLTESTING.


  (*************************************************************)
  (** **   Initialization Test    *) 
  (*************************************************************)  
  Module INITIALIZATION.

    Definition main (cur_address initial_global_value initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value initial_local_value).

    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ;
                       top_level_accessor_modsem ;
                       top_level_modsem].        
    
  End INITIALIZATION.

  (*************************************************************)
  (** **   Flag value Setter/Getter Test    *) 
  (*************************************************************)    
  Module DUMMYTEST1.
    
    Definition main (cur_address initial_global_value initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value initial_local_value)
        #; (Call "HVCTopLevel.mem_store" [CBV (page_low_int + (Int64.repr 4)); CBV (Int64.repr 16)])
        #; Put "read value" (Call "HVCTopLevel.mem_load" [CBV (page_low_int + (Int64.repr 4))]).

    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ;
                       top_level_accessor_modsem ;
                       top_level_modsem].        
    
  End DUMMYTEST1.

  Module DUMMYTEST2.
    
    Definition main (cur_address initial_global_value initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value initial_local_value)
        #; (Call "HVCTopLevel.set_is_hvc_mode" [])
        #; (Put "Succeeed in setting hvc mode" Vnull)
        #; (Call "HVCTopLevel.unset_is_hvc_mode" [])
        #; (Put "Succeeed in unsetting hvc mode" Vnull)
        #; (Call "HVCTopLevel.set_use_stage1_table" [])
        #; (Put "Succeeed in setting stage1 table" Vnull)
        #; (Call "HVCTopLevel.unset_use_stage1_table" [])
        #; (Put "Succeeed in unsetting stage1 table" Vnull).

    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ;
                       top_level_accessor_modsem ;
                       top_level_modsem].

  End DUMMYTEST2.

  (*************************************************************)
  (** **   VCPU Index Setter/Getter Test    *) 
  (*************************************************************)      
  Module DUMMYTEST3.
    
    Definition main (cur_address initial_global_value initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value initial_local_value)
        #; (Call "HVCToplevel.userspace_vcpu_index_setter" [CBV (Int64.repr 10)])
        #; (Put "getter result: " (Call "HVCToplevel.userspace_vcpu_index_getter" [])).

    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ;
                       top_level_accessor_modsem ;
                       top_level_modsem].

  End DUMMYTEST3.

  (*************************************************************)
  (** **   Current Entity ID Setter/Getter Test    *) 
  (*************************************************************)      
  Module DUMMYTEST4.
    
    Definition main (cur_address initial_global_value initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value initial_local_value)
        #; (Put "getter result: "
                (Call "HVCToplevel.current_entity_id_setter" [CBV (Int64.repr 3)]))
        #; (Put "getter result: "
                (Call "HVCToplevel.current_entity_id_getter" [])).

    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ;
                       top_level_accessor_modsem ;
                       top_level_modsem].

  End DUMMYTEST4.

  (*************************************************************)
  (** **  Set/Get Msg Test    *) 
  (*************************************************************)        
  Module DUMMYTEST5.
    
    Definition main (cur_address initial_global_value initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value initial_local_value)
        #; (Call "HVCTopLevel.set_buffer" [CBV (Int64.repr 0);
                                        CBV (Int64.repr 36);
                                        CBV (Vabs (upcast (buffer_msg
                                                             primary_vm_id 2
                                                             page_low 1)));
                                        CBV (Vabs (upcast (FFA_MEM_DONATE)))])
        #; (Call "HVCTopLevel.get_buffer" []).
        
    
    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ;
                       top_level_accessor_modsem ;
                       top_level_modsem].

  End DUMMYTEST5.
  
  (*************************************************************)
  (** **  Memory Property Setter/Getter Test    *) 
  (*************************************************************)            
  Module DUMMYTEST6.
    
    
    Definition main (cur_address initial_global_value initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value initial_local_value)
        #; (Call "HVCTopLevel.local_properties_setter" [CBV (Vcomp (Vlong (Int64.repr primary_vm_id)));
                                                       CBV (Vcomp (Vlong (Int64.repr 1)));
                                                       CBV (Vabs (upcast InitialLocalAttributes))])
        #; (Call "HVCTopLevel.local_properties_getter" [CBV (Vcomp (Vlong (Int64.repr primary_vm_id)));
                                                       CBV (Vcomp (Vlong (Int64.repr 1)))])
        #; (Call "HVCTopLevel.global_properties_setter" [CBV (Vcomp (Vlong (Int64.repr 1)));
                                                        CBV (Vabs (upcast InitialGlobalAttributesForVMOne))])
        #; (Call "HVCTopLevel.global_properties_getter" [CBV (Vcomp (Vlong (Int64.repr 1)))])
        #; (Call "HVCTopLevel.set_mem_dirty" [CBV (Vcomp (Vlong (Int64.repr primary_vm_id)));
                                             CBV (Vcomp (Vlong (Int64.repr 1)))])
        #; (Call "HVCTopLevel.clean_mem_dirty" [CBV (Vcomp (Vlong (Int64.repr primary_vm_id)));
                                               CBV (Vcomp (Vlong (Int64.repr 1)))]).
    
    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ;
                       top_level_accessor_modsem ;
                       top_level_modsem].

  End DUMMYTEST6.
  
  (*************************************************************)
  (** **  Context Switchin Test    *) 
  (*************************************************************)              
  Module CONTEXTSWITCHINGTEST1.

    Definition main (cur_address initial_global_value initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value initial_local_value)
        #; (Call "HVCToplevel.userspace_vcpu_index_setter" [CBV (Int64.repr 1)])
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter"
                 [CBV (Vabs (upcast (donate_vcpu_struct 1 primary_vm_id)))])
        #; (Put "hyp mode" (Call "HVCTopLevel.is_hvc_mode_getter" []))
        #; (Call "HVCTopLevel.save_regs_to_vcpu" [])
        #; (Put "kernel vcpu values for 1" (Call "HVCTopLevel.kernel_vcpu_struct_getter_with_entity_id"
                                          [CBV (Int64.repr 1)]))
        #; (Put "kernel vcpu values for 2" (Call "HVCTopLevel.kernel_vcpu_struct_getter_with_entity_id"
                                          [CBV (Int64.repr 2)]))
        #; (Put "kernel vcpu values for 3" (Call "HVCTopLevel.kernel_vcpu_struct_getter_with_entity_id"
                                          [CBV (Int64.repr 3)]))
        #; (Call "HVCTopLevel.vcpu_restore_and_run" []).


    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ;
                       top_level_accessor_modsem ;
                       top_level_modsem].        
    
  End CONTEXTSWITCHINGTEST1.

  (*************************************************************)
  (** **  Donate test (Sequential)    *) 
  (*************************************************************)              
  Module DONATETEST1.

    (** Donate test with sequential setting. The testing scenario of this test case is as follows.
        - VM tries to donate one memory page to VM 2 
        - VM 1 sets up the descriptor and write the descriptor inside the buffer
        - VM 1 triggers the hypervisor call. 
          - Context switching from the user space to the kernel space
          - hypervisor looks up the descriptor, and performs its operation.
          - Check the validity of the descriptor
          - Change the accessibility of the page as no-access (the proper behavior that FF-A document describes)
          - Store the descriptor information and notify VM 2 that there is a page that VM 2 can retrieve 
          - Perform scheduling (change the execution entity ID from 1 to 2)
          - Context switching from the kernel space to the user space
        - After performing it, it performs pseudo scheduling, which only change the execution entity ID.
          - We do not model the remaing operation for the memory donate (retrieve_req call) via VM 2 in our
            test cases. 
     *)
        
    Definition main (cur_address initial_global_value
                                 initial_local_value: var): stmt :=
      (** - Initialization *)
      (initialize_owners cur_address initial_global_value
                         initial_local_value)
        (** - Set up descriptor *)
        #; (Call "HVCTopLevel.set_buffer"
                 [CBV (Int64.repr 0);
                 CBV (Int64.repr 36);
                 CBV (Vabs (upcast (buffer_msg
                                      primary_vm_id  2
                                      1 1)));
                 CBV (Vabs (upcast (FFA_MEM_DONATE)))])
        #; (Call "HVCToplevel.userspace_vcpu_index_setter" [CBV (Int64.repr 0)])
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter"
                 [CBV (Vabs (upcast (donate_vcpu_struct 1 primary_vm_id)))])
        (** - Trigger hypervisor call *)
        #; (Put "hyp mode" (Call "HVCTopLevel.is_hvc_mode_getter" []))
        #; (Call "HVCTopLevel.hypervisor_call" [])
        #; (Put "hyp mode" (Call "HVCTopLevel.is_hvc_mode_getter" []))
        (* begin hide *)
        (*
        #; (Call "HVCToplevel.userspace_vcpu_index_setter" [CBV (Int64.repr 2)])
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter"
                 [CBV (Vabs (upcast (retrieve_req_vcpu_struct 2 2)))])
        #; (Call "HVCTopLevel.hypervisor_call" [])
         *)
        (* end hide *)
        (** - Change the running entity ID *)
        #; (Call "HVCTopLevel.scheduling" []) 
        #; (Call "HVCTopLevel.scheduling" []) 
        #; (Call "HVCTopLevel.scheduling" []) 
        (** - Print out the system log *)
        (* begin hide *)
        (*
        #; (Put "kernel vcpu values for 1" (Call "HVCTopLevel.kernel_vcpu_struct_getter_with_entity_id"
                                                 [CBV (Int64.repr 1)]))
        #; (Put "current state print" (Call "HVCToplevel.system_log_getter" [])) *)
        (* end hide *)        
        #; (Put "current state print"
                (Call "HVCToplevel.state_getter" [])).


    (** - Program definition of this test *)
    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.

    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    (** - Connecting top-level testing interfaces with this test main funciton. *)
    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ;
                       top_level_accessor_modsem ;
                       top_level_modsem].
    
  End DONATETEST1.

  (*************************************************************)
  (** **  Donate test (Concurrent)    *) 
  (*************************************************************)                
  Module DONATETEST2.

    (** Donate test with concurrent setting. The testing scenario of this test case is quite 
        similar to the previous sequential example.
        However, it introduces concurrency in it. The YIELD statement is inserted in between
        every line, and one thread will be picked up randomly when evaluating YIELD statements.
        By doing that, we could model and test threads that run concurrently.
     *)

    (** - Global variables  *)
    Definition GLOBAL_START := "GLOBAL_START".
    Definition SIGNAL := "SIGNAL".
    Definition CNT := "CNT".
    
    Definition LIMIT := Int64.repr 4.

    (** - Main thread that initializes all kernel values *)
    Definition main (cur_address initial_global_value
                                 initial_local_value: var): stmt :=
      Eval compute in
        INSERT_YIELD (
            GLOBAL_START
              #= (Int64.zero)
              #; SIGNAL #= (Int64.one)
              (** - Initialization *)
              #; (initialize_owners cur_address initial_global_value
                                    initial_local_value)
              #; GLOBAL_START #= (Int64.one)
              #;
              (** - Wait other threads' evaluation until number of their evaluations reaches the limit *)
              #while (SIGNAL < LIMIT) 
              do ( Skip )
                   (** - Print the log *)
                   #; (Put "current state print"
                           (Call "HVCToplevel.state_getter" []))
          ).

    (** - Main function of the primary VM *)
    Definition primary_vm_main :=
      Eval compute in
        INSERT_YIELD (
            CNT #= Int64.zero
                #;
                (** - Wait until the main thread initialize kernel structures *) 
                #while (GLOBAL_START == Int64.zero)
                do ( Skip )
                     #;
                     #while (SIGNAL < LIMIT)
                     do (
                         (** - Check whether this VM is scheduled *)
                         #if ((Call "HVCToplevel.current_entity_id_getter" []) ==
                              Int64.one)
                          then
                            (** - If this VM is first scheduled, set up the descriptor for the donate hypervisor call *)
                            #if (CNT == Int64.zero) then
                               SIGNAL
                                 #= (SIGNAL + Int64.one)                               
                                 #; (Call "HVCTopLevel.set_buffer"
                                          [CBV (Int64.repr 0);
                                          CBV (Int64.repr 36);
                                          CBV (Vabs (upcast (buffer_msg
                                                               primary_vm_id  2
                                                               9065
                                                               1)));
                                          CBV (Vabs (upcast (FFA_MEM_DONATE)))])
                                 #; (Call "HVCToplevel.userspace_vcpu_index_setter"
                                          [CBV (Int64.repr 1)])
                                 #; (Call "HVCTopLevel.userspace_vcpu_struct_setter"
                                          [CBV (Vabs (upcast
                                                        (donate_vcpu_struct 1 primary_vm_id)))])
                                      (** - Trigger hypervisor call *)
                                 #; (Call "HVCTopLevel.hypervisor_call" [])
                                 #; CNT #= CNT + Int64.one
                             else
                               (** - Trigger scheduling *)
                               SIGNAL #=
                                      SIGNAL + Int64.one
                                                 #; (Call "HVCTopLevel.scheduling" [])                               
                          else
                            Skip
                       )
          ).
    
    (** - Main function of secondary VMs *)
    Definition  vms_main (tid: Z) :=
      Eval compute in
        INSERT_YIELD (
            (** - Wait until the main thread initialize kernel structures *)
            #while (GLOBAL_START == Int64.zero)
             do ( Skip )
                  #;
                  #while (SIGNAL < LIMIT)
                  do (
                      (** - Check whether this VM is scheduled *)
                      #if ((Call "HVCToplevel.current_entity_id_getter" []) ==
                           (Int64.repr tid))
                       then
                         (** - Trigger scheduling *)
                         SIGNAL #= (SIGNAL + Int64.one)
                                #; (Call "HVCTopLevel.scheduling" [])
                       else Skip
                    )
          ).



    (** - Program definition of this test *)
    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.

    Definition primary_vm_mainF: function.
      mk_function_tac primary_vm_main ([]: list var)  ([]: list var).
    Defined.

    Definition vm_2_mainF: function.
      mk_function_tac (vms_main 2) ([]: list var)  ([]: list var).
    Defined.

    Definition vm_3_mainF: function.
      mk_function_tac (vms_main 3) ([]: list var)  ([]: list var).
    Defined.
    
    Definition vm_4_mainF: function.
      mk_function_tac (vms_main 4) ([]: list var)  ([]: list var).
    Defined.

    Definition main_program: program :=
      [
        ("main", mainF) ;
        ("primary_vm_main", primary_vm_mainF) ;
      ("vm_2_main", vm_2_mainF) ;
      ("vm_3_main", vm_3_mainF) ;
      ("vm_4_main", vm_4_mainF) 
      ].

    Definition modsems: list ModSem :=
      [program_to_ModSem main_program ;top_level_accessor_modsem ;
      top_level_modsem]. 

    (** - Connecting top-level testing interfaces with this test main funciton. *)
    Definition isem: itree Event unit :=
      eval_multimodule_multicore
        modsems [ "main" ; "primary_vm_main" ; "vm_2_main";
                "vm_3_main"; "vm_4_main"].
    
  End DONATETEST2.

  (*************************************************************)
  (** **  Donate test - invalid descriptor     *) 
  (*************************************************************)
  Module DONATETEST3.

    (** Donate test with the invalid descriptor. The descriptor in this example uses invalid memory attributes. 
        Therefore, it returns FFA_INVALID_PARAMETERS instead of FFA_SUCCESS. In this example, 
        we only print out vcpu value, the result of the hypervisor call, instead of the entire system log. 
     *)
    Definition main (cur_address initial_global_value
                                 initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value
                         initial_local_value)
        #; (Call "HVCTopLevel.set_buffer"
                 [CBV (Int64.repr 0);
                 CBV (Int64.repr 36);
                 CBV (Vabs (upcast (wrong_buffer_msg
                                      primary_vm_id 2
                                      1 1)));
                 CBV (Vabs (upcast (FFA_MEM_DONATE)))])
        #; (Call "HVCToplevel.userspace_vcpu_index_setter" [CBV (Int64.repr 0)])
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter"
                 [CBV (Vabs (upcast (donate_vcpu_struct 1 primary_vm_id)))])
        #; (Put "hyp mode" (Call "HVCTopLevel.is_hvc_mode_getter" []))
        #; (Call "HVCTopLevel.hypervisor_call" [])
        #; (Put "hyp mode" (Call "HVCTopLevel.is_hvc_mode_getter" []))
        (* begin hide *) (*
        #; (Call "HVCTopLevel.scheduling" []) 
        #; (Call "HVCTopLevel.scheduling" []) 
        #; (Call "HVCTopLevel.scheduling" []) 
        #; (Put "current state print" (Call "HVCToplevel.state_getter" [])) *)
        (* end hide *)
        #; (Put "kernel vcpu values for 1"
                (Call "HVCTopLevel.kernel_vcpu_struct_getter_with_entity_id"
                      [CBV (Int64.repr 1)])).

    (** - Program definition of this test *)
    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    (** - Connecting top-level testing interfaces with this test main funciton. *)
    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ;
                       top_level_accessor_modsem ;
                       top_level_modsem].
    
  End DONATETEST3.

  (*************************************************************)
  (** **  Donate test - invalid descriptor     *) 
  (*************************************************************)  
  Module DONATETEST4.

    (** Donate test with the invalid memory address. In this example, VM 2 tries to donate the page 
        that is owned by VM 1. Therefore, it reaises an error with the message that they cannot
        find out local memory attributes associated with VM 2 for the page 
     *)
    Definition main (cur_address initial_global_value
                                 initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value
                         initial_local_value)
        #; (Call "HVCTopLevel.scheduling" []) 
        #; (Call "HVCTopLevel.set_buffer"
                 [CBV (Int64.repr 0);
                 CBV (Int64.repr 36);
                 CBV (Vabs (upcast (buffer_msg
                                      2 3
                                      1 1)));
                 CBV (Vabs (upcast (FFA_MEM_DONATE)))])
        #; (Call "HVCToplevel.userspace_vcpu_index_setter" [CBV (Int64.repr 0)])
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter"
                 [CBV (Vabs (upcast (donate_vcpu_struct 1 2)))])
        #; (Put "hyp mode" (Call "HVCTopLevel.is_hvc_mode_getter" []))
        #; (Call "HVCTopLevel.hypervisor_call" [])
        #; (Put "hyp mode" (Call "HVCTopLevel.is_hvc_mode_getter" []))
        (* begin hide *) (*
        #; (Call "HVCTopLevel.scheduling" []) 
        #; (Call "HVCTopLevel.scheduling" []) 
        #; (Call "HVCTopLevel.scheduling" []) 
        #; (Put "current state print" (Call "HVCToplevel.state_getter" [])) *)
        (* end hide *)
        #; (Put "kernel vcpu values for 2"
                (Call "HVCTopLevel.kernel_vcpu_struct_getter_with_entity_id"
                      [CBV (Int64.repr 2)])).

    (** - Program definition of this test *)    
    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    (** - Connecting top-level testing interfaces with this test main funciton. *)
    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ;
                       top_level_accessor_modsem ;
                       top_level_modsem].
    
  End DONATETEST4.

  (*************************************************************)
  (** ** Donate test with specs that has a bug           *) 
  (*************************************************************)    
  Module DONATETEST5.

    (** Donate test with the spec that has an error in it. The checking for the number of receivers in
        the spec is written in a wrong way, so it will return an error that the number of receivers 
        is incorrect 
     *)    
    Definition main (cur_address initial_global_value
                                 initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value
                         initial_local_value)
        #; (Call "HVCTopLevel.set_buffer"
                 [CBV (Int64.repr 0);
                 CBV (Int64.repr 36);
                 CBV (Vabs (upcast (buffer_msg
                                      primary_vm_id 2
                                      1 1)));
                 CBV (Vabs (upcast (FFA_MEM_DONATE)))])
        #; (Call "HVCToplevel.userspace_vcpu_index_setter" [CBV (Int64.repr 0)])
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter"
                 [CBV (Vabs (upcast (donate_vcpu_struct 1 primary_vm_id)))])
        #; (Put "hyp mode" (Call "HVCTopLevel.is_hvc_mode_getter" []))
        #; (Call "HVCTopLevel.wrong_hypervisor_call" [])
        #; (Put "hyp mode" (Call "HVCTopLevel.is_hvc_mode_getter" []))
        #; (Call "HVCTopLevel.scheduling" []) 
        #; (Call "HVCTopLevel.scheduling" []) 
        #; (Call "HVCTopLevel.scheduling" [])
        #; (Put "kernel vcpu values for 1"
                (Call "HVCTopLevel.kernel_vcpu_struct_getter_with_entity_id"
                      [CBV (Int64.repr 1)])).
    
    (** - Program definition of this test *)    
    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address";
                                            "initial_global_value";
                                            "initial_local_value"]: list var).
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    (** - Connecting top-level testing interfaces with this test main funciton. *)
    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ;
                       top_level_accessor_modsem ;
                       top_level_modsem].        
    
  End DONATETEST5.
  
End FFAMEMORYHYPCALLTESTING.

