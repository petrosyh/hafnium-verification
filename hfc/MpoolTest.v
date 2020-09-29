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

    Definition main (p begin res r1 r2: var) : stmt :=
      (* Put "test plus" (Plus (Vnormal (Vint (repr 1))) (Vnormal (Vint (repr 5)))) #; *)
      (Call "MPOOL.mpool_init_locks" [])
        #;
        (Call "MPOOL.mpool_enable_locks" [])
        #;
        #assume mpool_locks_enabled #;        
        p #= Vnormal (Vptr 1%positive (Ptrofs.repr 80)) #;
        Put "main: before init: " p #;
        (* initialize it with the entry size - 8 *)
        Call "MPOOL.mpool_init" [CBV p; CBV (Int64.repr 8)] #;
        Put "main: after init: " p #;
        begin #= (Vnormal (Vptr 1%positive (Ptrofs.repr 160))) #;
        res #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBR begin; CBV (Int64.repr 64)])
        #;
        begin #= (Vnormal (Vptr 1%positive (Ptrofs.repr 240))) #;
        res #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBR begin; CBV (Int64.repr 64)])
        #;
        Put "main: add_chunk done: " p #;
        r1 #= (Call "MPOOL.mpool_alloc_contiguous" [CBV p; CBV (Int64.repr 8); CBV (Int64.repr 1)]) #;
        Put "main: alloc 1 done: succeed" r1 #;
        r2 #= Call "MPOOL.mpool_alloc_contiguous" [CBV p ; CBV (Int64.repr 8); CBV (Int64.repr 1)]  #;
        Put "main: alloc 2 done: succeed " r2 #;
        (Call "MPOOL.mpool_free" [CBV p; CBV r1]) #;
        (Call "MPOOL.mpool_free" [CBV p; CBV r2]) #;
        Skip.


    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "begin" ; "res"; "r1"; "r2"]. Defined.

    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; MPOOLCONCUR.mpool_modsem ; LOCK.lock_modsem].
    
  End MPOOLTEST_ONE. 


  Fixpoint INSERT_YIELD (s: stmt): stmt :=
    match s with
    | Seq s0 s1 => Seq (INSERT_YIELD s0) (INSERT_YIELD s1)
    | If c s0 s1 => If c (INSERT_YIELD s0) (INSERT_YIELD s1)
    | While c s => While c (INSERT_YIELD s)
    | _ => Yield #; s
    end
  .

  Module MPOOLTEST_TWO.

    Definition GMPOOL := "GMPOOL".
    Definition SIGNAL := "SIGNAL".
    Definition GLOBAL_START := "GLOBAL_START".
    
    Definition main (p i r next_chunk: var): stmt :=
      Eval compute
      in INSERT_YIELD (
             GLOBAL_START #= (Int.zero) #;    
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
                          next_chunk #= (Vnormal (Vptr 1%positive (Ptrofs.repr 160))) #;
                          r #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBR next_chunk; CBV (Int64.repr 160)])
                          #;               
                          GMPOOL #= p #;
                          (Put "GMPOOL_result" GMPOOL) #;
                          SIGNAL #= (Int.zero) #;
                          GLOBAL_START #= (Int.one) #;
                          (#while (SIGNAL <= (Int.repr 1))
                            do
                              (Debug "waiting for SIGNAL" Vnull))
                          #;
                          i #= (Int.repr 3) #;
                          #while (i)
                          do (
                              i #= (i - (Int.repr 1)) #;
                                r #= (Call "MPOOL.mpool_alloc_contiguous"
                                      [CBR p ; CBV (Int64.repr 8); CBV (Int64.repr 1)])
                                #;
                                (Put "allocation is done" r) #;
                                p #= Vnormal (Vptr 1%positive (Ptrofs.repr 80)) 
                            ) #;
                              Put "Test Passed " Vnull #;
                              Skip
           ).
    
    Definition alloc_and_free (sz : N) (p i r0 r1 r2: var) : stmt :=
      Eval compute in
        INSERT_YIELD (
            (Put "Start" Int.zero) #;
            (#while (GLOBAL_START == Int.zero)
              do
                (Debug "waiting for GMPOOL" GMPOOL))
            #;
            p #= Vnormal (Vptr 1%positive (Ptrofs.repr ((Z.of_N sz) * 320))) #;
            
              (Call "MPOOL.mpool_init_with_fallback" [CBR p; CBR GMPOOL]) #;
              Put "(Local Mpool) After init-with-fallback" p #;
              r0 #= (Call "MPOOL.mpool_alloc_contiguous"
                          [CBV p ; CBV (Int64.repr 8); CBV (Int64.repr 1)]) #;
              (*
              r1 #= (Call "MPOOL.mpool_alloc_contiguous"
                    [CBR p ; CBV (Int64.repr 8); CBV (Int64.repr 1)]) #;
              r2 #= (Call "MPOOL.mpool_alloc_contiguous"
                    [CBR p ; CBV (Int64.repr 8); CBV (Int64.repr 1)]) #; *)
              (Call "MPOOL.mpool_free" [CBR p; CBR r0]) #;
              (*
              (Call "MPOOL.mpool_free" [CBR p; CBR r1]) #;
              *)
              SIGNAL #= (SIGNAL + Int.one) #;
              Skip
          ).


    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "i" ; "r"; "next_chunk"]. Defined.
    Definition alloc_and_free2F: function.
      mk_function_tac (alloc_and_free 1) ([]: list var) ["p" ; "i" ; "r0" ; "r1" ; "r2"].
    Defined.
    Definition alloc_and_free3F: function.
      mk_function_tac (alloc_and_free 2) ([]: list var) ["p" ; "i" ; "r0" ; "r1" ; "r2"].
    Defined.

    Definition main_program: program :=
      [
        ("main", mainF) ;
          ("alloc_and_free2", alloc_and_free2F) ;
          ("alloc_and_free3", alloc_and_free3F) 
      ].

    Definition modsems: list ModSem :=
      [program_to_ModSem main_program ; MPOOLCONCUR.mpool_modsem ; LOCK.lock_modsem].

    Definition isem: itree Event unit :=
      eval_multimodule_multicore
        modsems [ "main" ; "alloc_and_free2" ; "alloc_and_free3" ].
    
  End MPOOLTEST_TWO.
  
End MPOOLTEST.
