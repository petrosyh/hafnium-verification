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
Require Import ADDR.
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Set Implicit Arguments.


Module ADDRTEST.


  Module PA_ADDR_TEST.

    Definition main (p res: var): stmt :=
      Alloc p (Int.repr 5) #;
            res #= (Call "ADDR.pa_init" [CBR p]) #;
            Put "return value" p.

    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "res"]. Defined.

    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem1: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ADDR.addr_modsem].
    
  End PA_ADDR_TEST.
    
End ADDRTEST.