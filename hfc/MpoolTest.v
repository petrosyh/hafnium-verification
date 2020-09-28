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
Require Import Lock.
Require Import Mpool.
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import LOCK.
Import MPOOLCONCURSTRUCT.
Import MPOOLCONCUR.

Import Int64.

Set Implicit Arguments.

(****** TODO: move to Lang *****)
Fixpoint INSERT_YIELD (s: stmt): stmt :=
  match s with
  | Seq s0 s1 => Seq (INSERT_YIELD s0) (INSERT_YIELD s1)
  | If c s0 s1 => If c (INSERT_YIELD s0) (INSERT_YIELD s1)
  | While c s => While c (INSERT_YIELD s)
  | _ => Yield #; s
  end
.

Module MPOOLTEST.

  Module MPOOLTEST_ONE.

    Definition main (p begin res r1 r2 r3: var) : stmt :=
      (* Put "test plus" (Plus (Vnormal (Vint (repr 1))) (Vnormal (Vint (repr 5)))) #; *)
      (Call "MPOOL.mpool_init_locks" [])
        #;
        (Call "MPOOL.mpool_enable_locks" [])
        #;
        #assume mpool_locks_enabled #;        
        p #= Vnormal (Vptr 1%positive (Ptrofs.repr 80)) #;
        Put "main: before init: " p #;
        (* initialize it with the entry size - 8 *)
        Call "MPOOL.mpool_init" [CBR p; CBV (Vlong (Int64.repr 8))] #;
        Put "main: after init: " p #;
        begin #= (Vnormal (Vptr 1%positive (Ptrofs.repr 160))) #;
        res #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBR begin; CBV (Int64.repr 32)])
        #;
        begin #= (Vnormal (Vptr 1%positive (Ptrofs.repr 240))) #;
        res #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBV begin; CBV (Int64.repr 32)])
        #;
        begin #= (Vnormal (Vptr 1%positive (Ptrofs.repr 320))) #;
        res #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBV begin; CBV (Int64.repr 32)])
        #;
        (*
        Put "main: add_chunk done: " p #;
        r1 #= (Call "MPOOL.mpool_alloc_contiguous" [CBR p; CBV (repr 12); CBV (repr 4)]) #;
        Put "main: alloc_contiguous done: " r1 #;
        Put "main: alloc 1 done: succeed" r1 #;
        #assume r1 #; *)
        (* 
        r2 #= Call "MPOOL.mpool_alloc_contiguous" [CBR p ; CBV (repr 8); CBV (repr 4)] #;
        Put "main: alloc_contiguous done: " r2 #;
        Put "main: alloc 2 done: succeed " r3 #;
        #assume r2 #;
        r3 #= Call "MPOOL.mpool_alloc_contiguous" [CBR p ; CBV (repr 4); CBV (repr 4)] #;
        Put "main: alloc_contiguous done: " r3 #; 
        Put "main: alloc 3 done: fail " r3 #;
        #assume (!r3) #; *)
        Skip.


    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "begin" ; "res"; "r1"; "r2"; "r3"]. Defined.

    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; MPOOLCONCUR.mpool_modsem ; LOCK.lock_modsem].
    
  End MPOOLTEST_ONE. 

  
End MPOOLTEST.
