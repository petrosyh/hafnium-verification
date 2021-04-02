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

Definition address_low_int := Int64.repr address_low.
Definition address_mid_int :=
  ((Int64.repr address_high -  Int64.repr address_low) / (Int64.repr 2))
  + Int64.repr address_low.
Definition address_high_int := Int64.repr address_high.

Section FFAMemoryHypCallInitialization.

  (** address low differs from address low in the memory context. 
      I am trying to use subset of  *)
  Definition InitialGlobalAttributesForVMOne :=
    mkMemGlobalProperties (Owned primary_vm_id)
                          (ExclusiveAccess primary_vm_id)
                          (FFA_INSTRUCTION_ACCESS_NX)
                          (FFA_DATA_ACCESS_RW)
                          (FFA_MEMORY_NORMAL_MEM
                             FFA_MEMORY_CACHE_NON_CACHEABLE
                             FFA_MEMORY_OUTER_SHAREABLE)
                          MemClean.               
  
  Definition InitialGlobalAttributesForVMTwo :=
    mkMemGlobalProperties (Owned 2)
                          (ExclusiveAccess 2)
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

  Definition initialize_owners (cur_address initial_global_value initial_local_value : var): stmt :=
    Put "start initializaiton" (Vnull) #;
        cur_address #= address_low_int #;
        (initial_local_value #= (Vabs (upcast InitialLocalAttributes))) #;
        #while (cur_address < address_mid_int)
        do (
            (initial_global_value #=  (Vabs (upcast InitialGlobalAttributesForVMOne)))
              #; (Call "HVCTopLevel.global_properties_setter"
                       [CBV cur_address; CBV initial_global_value])
              #; (Call "HVCTopLevel.local_properties_setter"
                       [CBV (Int64.repr primary_vm_id); CBV cur_address; CBV initial_local_value])              
              #; cur_address #= cur_address + (Int64.repr alignment_value)) #;
        #while (cur_address <= address_high_int)
        do (
            (initial_global_value #=  (Vabs (upcast InitialGlobalAttributesForVMTwo)))
              #; (Call "HVCTopLevel.global_properties_setter"
                       [CBV cur_address; CBV initial_global_value])
              #; (Call "HVCTopLevel.local_properties_setter"
                       [CBV (Int64.repr 2); CBV cur_address; CBV initial_local_value])              
              #; cur_address #= cur_address + (Int64.repr alignment_value)).

End  FFAMemoryHypCallInitialization.

Module FFAMEMORYHYPCALLTESTING.

  Module DUMMYTEST1.
    
    Definition main (cur_address initial_global_value initial_local_value: var): stmt :=
      (initialize_owners cur_address initial_global_value initial_local_value)
        #; (Call "HVCTopLevel.mem_store" [CBV (address_low_int + (Int64.repr 4)); CBV (Int64.repr 16)])
        #; Put "read value" (Call "HVCTopLevel.mem_load" [CBV (address_low_int + (Int64.repr 4))]).

    Definition mainF: function.
      mk_function_tac main ([]: list var) (["cur_address"; "initial_global_value"; "initial_local_value"]: list var).
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; top_level_accessor_modsem ; top_level_modsem].        
        
  End DUMMYTEST1.
  
End FFAMEMORYHYPCALLTESTING.

