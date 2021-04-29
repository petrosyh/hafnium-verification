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

Section FFAMemoryHypCallInitialization.

  (** address low differs from address low in the memory context. 
      I am trying to use subset of  *)
  Definition InitialGlobalAttributesForVMOne :=
    mkMemGlobalProperties false
                          (Owned primary_vm_id)
                          (ExclusiveAccess primary_vm_id)
                          (FFA_INSTRUCTION_ACCESS_NX)
                          (FFA_DATA_ACCESS_RW)
                          (FFA_MEMORY_NORMAL_MEM
                             FFA_MEMORY_CACHE_NON_CACHEABLE
                             FFA_MEMORY_OUTER_SHAREABLE)
                          MemClean.               
  
  Definition InitialGlobalAttributesForVMTwo :=
    mkMemGlobalProperties false
                          (Owned 2)
                          (ExclusiveAccess 2)
                          (FFA_INSTRUCTION_ACCESS_NX)
                          (FFA_DATA_ACCESS_RW)
                          (FFA_MEMORY_NORMAL_MEM
                             FFA_MEMORY_CACHE_NON_CACHEABLE
                             FFA_MEMORY_OUTER_SHAREABLE)
                          MemClean.

  Definition InitialGlobalAttributesForVMThree :=
    mkMemGlobalProperties false
                          (Owned 3)
                          (ExclusiveAccess 3)
                          (FFA_INSTRUCTION_ACCESS_NX)
                          (FFA_DATA_ACCESS_RW)
                          (FFA_MEMORY_NORMAL_MEM
                             FFA_MEMORY_CACHE_NON_CACHEABLE
                             FFA_MEMORY_OUTER_SHAREABLE)
                          MemClean.


  Definition InitialGlobalAttributesForVMFour :=
    mkMemGlobalProperties false
                          (Owned 4)
                          (ExclusiveAccess 4)
                          (FFA_INSTRUCTION_ACCESS_NX)
                          (FFA_DATA_ACCESS_RW)
                          (FFA_MEMORY_NORMAL_MEM
                             FFA_MEMORY_CACHE_NON_CACHEABLE
                             FFA_MEMORY_OUTER_SHAREABLE)
                          MemClean.
  
  Definition InitialLocalAttributes :=
    mkMemLocalProperties (LocalOwned)
                         (FFA_INSTRUCTION_ACCESS_NX)
                         (FFA_DATA_ACCESS_RW)
                          (FFA_MEMORY_NORMAL_MEM
                             FFA_MEMORY_CACHE_NON_CACHEABLE
                             FFA_MEMORY_OUTER_SHAREABLE).

  Definition initial_vcpu_struct (cpu_id : ffa_CPU_ID_t) (vm_id : ffa_UUID_t) :=
    (mkVCPU_struct
       (Some cpu_id)
       (Some vm_id)
       (mkArchRegs
          (mkFFA_value_type
             FFA_IDENTIFIER_DEFAULT
             (ZMap.init 0)))).
  
  Definition initialize_owners (cur_address initial_global_value initial_local_value : var): stmt :=
    Put "start initializaiton" (Vnull) #;
        cur_address #= page_low_int #;
        (initial_local_value #= (Vabs (upcast InitialLocalAttributes)))
        #; (Call "HVCToplevel.kernel_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr primary_vm_id); CBV (Int64.repr primary_vm_id)])              
        #; (Call "HVCTopLevel.kernel_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr primary_vm_id); CBV (Vabs (upcast (initial_vcpu_struct 1 primary_vm_id)))])
        #; (Call "HVCToplevel.userspace_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr primary_vm_id); CBV (Int64.repr primary_vm_id)])              
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr primary_vm_id); CBV (Vabs (upcast (initial_vcpu_struct 1 primary_vm_id)))]) 

        #; (Call "HVCToplevel.kernel_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr 2); CBV (Int64.repr 2)])              
        #; (Call "HVCTopLevel.kernel_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr 2); CBV (Vabs (upcast (initial_vcpu_struct 2 2)))])                            
        #; (Call "HVCToplevel.userspace_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr 2); CBV (Int64.repr 2)])              
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr 2); CBV (Vabs (upcast (initial_vcpu_struct 2 2)))]) 

        #; (Call "HVCToplevel.kernel_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr 3); CBV (Int64.repr 3)])              
        #; (Call "HVCTopLevel.kernel_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr 3); CBV (Vabs (upcast (initial_vcpu_struct 3 3)))])              
        #; (Call "HVCToplevel.userspace_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr 3); CBV (Int64.repr 3)])              
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr 3); CBV (Vabs (upcast (initial_vcpu_struct 3 3)))])              

        #; (Call "HVCToplevel.kernel_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr 4); CBV (Int64.repr 4)])                            
        #; (Call "HVCTopLevel.kernel_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr 4); CBV (Vabs (upcast (initial_vcpu_struct 4 4)))])              
        #; (Call "HVCToplevel.userspace_vcpu_index_setter_with_entity_id"
                 [CBV (Int64.repr 4); CBV (Int64.repr 4)])                            
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter_with_entity_id"
                 [CBV (Int64.repr 4); CBV (Vabs (upcast (initial_vcpu_struct 4 4)))])                      
        #;
        #while (cur_address < page_1st_quater_int)
        do (
            (initial_global_value #= (Vabs (upcast InitialGlobalAttributesForVMOne)))
              #; (Call "HVCTopLevel.global_properties_setter"
                       [CBV cur_address; CBV initial_global_value])
              #; (Call "HVCTopLevel.local_properties_setter"
                       [CBV (Int64.repr primary_vm_id); CBV cur_address; CBV initial_local_value])
              #; cur_address #= cur_address + (Int64.repr alignment_value)) #;
        #while (cur_address < page_2nd_quater_int)
        do (
            (initial_global_value #=  (Vabs (upcast InitialGlobalAttributesForVMTwo)))
              #; (Call "HVCTopLevel.global_properties_setter"
                       [CBV cur_address; CBV initial_global_value])
              #; (Call "HVCTopLevel.local_properties_setter"
                       [CBV (Int64.repr 2); CBV cur_address; CBV initial_local_value])
              #; cur_address #= cur_address + (Int64.repr alignment_value)) #;
        #while (cur_address < page_3rd_quater_int)
        do (
            (initial_global_value #=  (Vabs (upcast InitialGlobalAttributesForVMThree)))
              #; (Call "HVCTopLevel.global_properties_setter"
                       [CBV cur_address; CBV initial_global_value])
              #; (Call "HVCTopLevel.local_properties_setter"
                       [CBV (Int64.repr 3); CBV cur_address; CBV initial_local_value])
              #; cur_address #= cur_address + (Int64.repr alignment_value)) #;
        #while (cur_address < page_high_int)
        do (
            (initial_global_value #=  (Vabs (upcast InitialGlobalAttributesForVMFour)))
              #; (Call "HVCTopLevel.global_properties_setter"
                       [CBV cur_address; CBV initial_global_value])
              #; (Call "HVCTopLevel.local_properties_setter"
                       [CBV (Int64.repr 4); CBV cur_address; CBV initial_local_value])
              #; cur_address #= cur_address + (Int64.repr alignment_value)).

End  FFAMemoryHypCallInitialization.

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
       FFA_INSTRUCTION_ACCESS_NX
       FFA_DATA_ACCESS_RW
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
         (FFA_MEMORY_NORMAL_MEM
            FFA_MEMORY_CACHE_NON_CACHEABLE
            FFA_MEMORY_OUTER_SHAREABLE))
      (MEMORY_REGION_FLAG_NORMAL
         (mkFFA_mem_default_flags_struct false false))
      0
      0
      ((EndpointMemoryAccessDescriptorGeneratorForDonate receiver)::nil)
      (MemoryRegionCompositeGeneratorForDonate address page).

  Definition mailbox_msg
             (sender receiver: ffa_UUID_t)
             (address :ffa_address_t) (page: Z)
    := mailbox_memory_region (DonateDescriptorGenerator sender receiver address page).


  Definition donate_vcpu_struct (cpu_id : ffa_CPU_ID_t) (vm_id : ffa_UUID_t)  :=
    (mkVCPU_struct
       (Some cpu_id)
       (Some vm_id)
       (mkArchRegs
          (mkFFA_value_type
             (FFA_FUNCTION_IDENTIFIER FFA_MEM_DONATE)
             (ZMap.init 0)))).

  
End DescriptorGenerator.

Module FFAMEMORYHYPCALLTESTING.

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

  Module DUMMYTEST5.
    
    Definition main (cur_address initial_global_value initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value initial_local_value)
        #; (Call "HVCTopLevel.send_msg" [CBV (Int64.repr primary_vm_id);
                                        CBV (Int64.repr 36);
                                        CBV (Vabs (upcast (mailbox_msg
                                                             primary_vm_id primary_vm_id
                                                             page_low 1)));
                                        CBV (Vabs (upcast (FFA_MEM_DONATE)))])
        #; (Call "HVCTopLevel.recv_msg" []).
        
    
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
  
  Module DUMMYTEST6.


    Definition main (cur_address initial_global_value initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value initial_local_value)
        #; (Call "HVCToplevel.userspace_vcpu_index_setter" [CBV (Int64.repr 1)])
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter"
                 [CBV (Vabs (upcast (donate_vcpu_struct 1 primary_vm_id)))])
        #; (Call "HVCTopLevel.userspace_vcpu_struct_getter" []).
    
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
    
  Module DUMMYTEST7.
    
    
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

  End DUMMYTEST7.
  
  
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
    
  Module DONATETEST1.

    Definition main (cur_address initial_global_value initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value initial_local_value)
        #; (Call "HVCTopLevel.send_msg" [CBV (Int64.repr primary_vm_id);
                                        CBV (Int64.repr 36);
                                        CBV (Vabs (upcast (mailbox_msg
                                                             primary_vm_id primary_vm_id
                                                             page_low 1)));
                                        CBV (Vabs (upcast (FFA_MEM_DONATE)))])
        #; (Call "HVCToplevel.userspace_vcpu_index_setter" [CBV (Int64.repr 0)])
        #; (Call "HVCTopLevel.userspace_vcpu_struct_setter"
                 [CBV (Vabs (upcast (donate_vcpu_struct 1 primary_vm_id)))])
        #; (Put "hyp mode" (Call "HVCTopLevel.is_hvc_mode_getter" []))
        #; (Call "HVCTopLevel.hypervisor_call" [])
        #; (Put "hyp mode" (Call "HVCTopLevel.is_hvc_mode_getter" []))        
        #; (Call "HVCTopLevel.scheduling" []) 
        #; (Put "current state print" (Call "HVCToplevel.state_getter" []))
        #; (Put "kernel vcpu values for 1" (Call "HVCTopLevel.kernel_vcpu_struct_getter_with_entity_id"
                                                 [CBV (Int64.repr 1)]))
    (*
        #; (Put "current state print" (Call "HVCToplevel.system_log_getter" [])) *) .

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
    
  End DONATETEST1.
  
End FFAMEMORYHYPCALLTESTING.

