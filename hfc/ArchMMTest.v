(*
 * Copyright 2020 Youngju Song / Jieung Kim
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
Require Import Values.
Require Import Integers.
Require Import Constant.
Require Import ArchMM.
Require Import ArchMMHighSpec.
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import ArchMM.
Import Int64.

Set Implicit Arguments.


Module ArchMMTEST.

  (* some unit tests *)


  Module ABSENT.

    Definition main res: stmt :=
      res #= (Call "ARCHMM.arch_mm_absent_pte" [CBV (Int.repr 0)]) #;
          Put "res: " res.

    Definition mainF: function. mk_function_tac main ([]: list var) ["res"]. Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem1: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMM.arch_mm_modsem].


    Definition isem2: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMMHighSpec.arch_mm_modsem].
    
  End ABSENT.

  Module ARCHMMPTETABLE.

    Definition main res: stmt :=
      res #= (Call "ARCHMM.arch_mm_pte_table" [CBV (Int.repr 0)]) #;
          Put "res: " res.

    Definition mainF: function. mk_function_tac main ([]: list var) ["res"]. Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].
    
    Definition isem1: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMM.arch_mm_modsem].


    Definition isem2: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMMHighSpec.arch_mm_modsem].
    
  End ARCHMMPTETABLE.


End ArchMMTEST.


