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
Require Import MpoolHighSpec.
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

    (* Concurrent mpool_add_chunk in the same mpool *)

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
                          p #= Vcomp (Vptr 2%positive (Ptrofs.repr 80)) #;
                          Put "main: before init: " p #;
                          (* initialize it with the entry size - 8 *)
                          Call "MPOOL.mpool_init" [CBR p; CBV (Vlong (Int64.repr 8))] #;
                          Put "main: after init: " p #;
                          next_chunk #= (Vcomp (Vptr 2%positive (Ptrofs.repr 160))) #;
                          r #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBR next_chunk; CBV (Int64.repr 160)])
                          #;
                          GMPOOL #= p #;
                          (Put "main: GMPOOL_result" GMPOOL) #;
                          SIGNAL #= (Int.zero) #;
                          GLOBAL_START #= (Int.one) #;
                          (#while (SIGNAL <= (Int.repr 1))
                            do
                              (Debug "waiting for SIGNAL" Vnull))
                          #;
                          Skip
           ).
    
    Definition alloc_by_thread (tid : N) (p p1 r new_chunk: var) : stmt :=
      Eval compute in
        INSERT_YIELD (
            (Put "Start" (Int64.repr (Z.of_N tid))) #;
            (#while (GLOBAL_START == Int.zero)
              do
                (Debug "Waiting for GMPOOL" GMPOOL))
            #;
            p #= GMPOOL #;
            new_chunk #= (Vcomp (Vptr 2%positive (Ptrofs.repr ((Z.of_N tid * 320) + 80)))) #;
            r #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBR new_chunk; CBV (Int64.repr 160)]) #;
            p1 #= Vcomp (Vptr 2%positive (Ptrofs.repr ((Z.of_N tid) * 320))) #;
            (Call "MPOOL.mpool_init_with_fallback" [CBR p1; CBR GMPOOL]) #;
            new_chunk #= (Vcomp (Vptr 2%positive (Ptrofs.repr ((Z.of_N tid * 320) + 16)))) #;
            r #= (Call "MPOOL.mpool_add_chunk" [CBR p1; CBR new_chunk; CBV (Int64.repr 16)]) #;
            Put "(Local Mpool) After init-with-fallback" p #;
            (Call "MPOOL.mpool_free" [CBV p; CBV p1]) #;
            Put "alloc_by_thread : next_chunk_loc" (p #@ entry_list_loc) #;
            SIGNAL #= (SIGNAL + Int.one) #;
            Skip
            ).


    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "i" ; "r"; "next_chunk"]. Defined.
    Definition alloc_by_thread1F: function.
      mk_function_tac (alloc_by_thread 1) ([]: list var) ["p" ; "p1" ; "r"; "new_chunk"].
    Defined.
    Definition alloc_by_thread2F: function.
      mk_function_tac (alloc_by_thread 2) ([]: list var) ["p" ; "p1" ; "r"; "new_chunk"].
    Defined.

    Definition main_program: program :=
      [
        ("main", mainF) ;
      ("alloc_by_thread1", alloc_by_thread1F) ;
      ("alloc_by_thread2", alloc_by_thread2F) 
      ].

    Definition modsems: list ModSem :=
      [program_to_ModSem main_program ; MPOOLCONCUR.mpool_modsem ; LOCK.lock_modsem].

    Definition isem: itree Event unit :=
      eval_multimodule_multicore
        modsems [ "main" ; "alloc_by_thread1" ; "alloc_by_thread2" ].
    
  End MPOOLTEST_ONE.

  Module MPOOLTEST_TWO.

    (* mpool_add_chunk and mpool_fini *)
    
    Definition main (p p_fallback begin res r1 r2: var) : stmt :=
      (* Put "test plus" (Plus (Vcomp (Vint (repr 1))) (Vcomp (Vint (repr 5)))) #; *)
      (Call "MPOOL.mpool_init_locks" [])
        #;
        (Call "MPOOL.mpool_enable_locks" [])
        #;
        #assume mpool_locks_enabled #;        
        p #= Vcomp (Vptr 2%positive (Ptrofs.repr 80)) #;
        Put "main: before init: " p #;
        (* initialize it with the entry size - 8 *)
        Call "MPOOL.mpool_init" [CBV p; CBV (Int64.repr 8)] #;
        p_fallback #= Vcomp (Vptr 2%positive (Ptrofs.repr 160)) #;
        (Call "MPOOL.mpool_init_with_fallback" [CBR p_fallback; CBR p]) #;        
        Put "main: after init: " p #;
        begin #= (Vcomp (Vptr 2%positive (Ptrofs.repr 240))) #;
        res #= (Call "MPOOL.mpool_add_chunk" [CBR p_fallback; CBR begin; CBV (Int64.repr 32)])
        #;
        begin #= (Vcomp (Vptr 2%positive (Ptrofs.repr 280))) #;
        res #= (Call "MPOOL.mpool_add_chunk" [CBR p_fallback; CBR begin; CBV (Int64.repr 32)])
        #;
        begin #= (Vcomp (Vptr 2%positive (Ptrofs.repr 320))) #;
        res #= (Call "MPOOL.mpool_add_chunk" [CBR p_fallback; CBR begin; CBV (Int64.repr 64)])
        #;
        begin #= (Vcomp (Vptr 2%positive (Ptrofs.repr 400))) #;
        res #= (Call "MPOOL.mpool_add_chunk" [CBR p_fallback; CBR begin; CBV (Int64.repr 64)])
        #;
        (Call "MPOOL.mpool_fini" [CBR p_fallback]) #;
        Skip.


    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "p_fallback" ; "begin" ; "res"; "r1"; "r2"]. Defined.

    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; MPOOLCONCUR.mpool_modsem ; LOCK.lock_modsem].
    
  End MPOOLTEST_TWO. 

  Module MPOOLTEST_THREE.

    (* mpool add chunk and mpool alloc *) 
    Definition main (p begin res r1 r2 r3: var) : stmt :=
      (* Put "test plus" (Plus (Vcomp (Vint (repr 1))) (Vcomp (Vint (repr 5)))) #; *)
      (Call "MPOOL.mpool_init_locks" [])
        #;
        (Call "MPOOL.mpool_enable_locks" [])
        #;
        #assume mpool_locks_enabled #;        
        p #= Vcomp (Vptr 2%positive (Ptrofs.repr 80)) #;
        Put "main: before init: " p #;
        (* initialize it with the entry size - 8 *)
        Call "MPOOL.mpool_init" [CBV p; CBV (Int64.repr 8)] #;
        Put "main: after init: " p #;
        begin #= (Vcomp (Vptr 2%positive (Ptrofs.repr 160))) #;
        res #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBR begin; CBV (Int64.repr 64)])
        #;
        begin #= (Vcomp (Vptr 2%positive (Ptrofs.repr 240))) #;
        res #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBR begin; CBV (Int64.repr 64)])
        #;
        Put "main: add_chunk done: " p #;
        r1 #= (Call "MPOOL.mpool_alloc_contiguous" [CBV p; CBV (Int64.repr 2); CBV (Int64.repr 1)]) #;
        Put "main: alloc 1 done: succeed" r1 #;
        r2 #= Call "MPOOL.mpool_alloc_contiguous" [CBV p ; CBV (Int64.repr 2); CBV (Int64.repr 1)]  #;
        Put "main: alloc 2 done: succeed " r2 #;
        r3 #= Call "MPOOL.mpool_alloc_contiguous" [CBV p ; CBV (Int64.repr 8); CBV (Int64.repr 1)]  #;
        Put "main: alloc 3 done: succeed " r3 #;
        (Call "MPOOL.mpool_free" [CBV p; CBV r1]) #;
        (Call "MPOOL.mpool_free" [CBV p; CBV r2]) #;
        (Call "MPOOL.mpool_free" [CBV p; CBV r3]) #;
        Skip.


    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "begin" ; "res"; "r1"; "r2"; "r3"]. Defined.

    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; MPOOLCONCUR.mpool_modsem ; LOCK.lock_modsem].
    
  End MPOOLTEST_THREE. 

  Module MPOOLTEST_FOUR.

    (* concurrent mpool add chunk and mpool alloc *) 
    
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
                          p #= Vcomp (Vptr 2%positive (Ptrofs.repr 80)) #;
                          Put "main: before init: " p #;
                          (* initialize it with the entry size - 8 *)
                          Call "MPOOL.mpool_init" [CBR p; CBV (Vlong (Int64.repr 8))] #;
                          Put "main: after init: " p #;
                          next_chunk #= (Vcomp (Vptr 2%positive (Ptrofs.repr 160))) #;
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
                                      [CBR p ; CBV (Int64.repr 4); CBV (Int64.repr 1)])
                                #;
                                (Put "allocation is done" r) #;
                                p #= Vcomp (Vptr 2%positive (Ptrofs.repr 80))
                            ) #;
                              Put "Test Passed " Vnull #;
                              Skip
           ).
    
    Definition alloc_and_free (tid : N) (p i r r0 r1 r2 new_chunk: var) : stmt :=
      Eval compute in
        INSERT_YIELD (
            (Put "Start" Int.zero) #;
            (#while (GLOBAL_START == Int.zero)
              do
                (Debug "waiting for GMPOOL" GMPOOL))
            #;
            p #= Vcomp (Vptr 2%positive (Ptrofs.repr ((Z.of_N tid) * 320))) #;
            
              (Call "MPOOL.mpool_init_with_fallback" [CBR p; CBR GMPOOL]) #;
              Put "(Local Mpool) After init-with-fallback" p #;
              new_chunk #= (Vcomp (Vptr 2%positive (Ptrofs.repr ((Z.of_N tid * 320) + 16)))) #;
              r #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBR new_chunk; CBV (Int64.repr 160)]) #;
              r0 #= (Call "MPOOL.mpool_alloc_contiguous"
                          [CBV p ; CBV (Int64.repr 8); CBV (Int64.repr 1)]) #;
              r1 #= (Call "MPOOL.mpool_alloc_contiguous"
                          [CBR p ; CBV (Int64.repr 8); CBV (Int64.repr 1)]) #;
              (Call "MPOOL.mpool_free" [CBR p; CBR r0]) #;
              (Call "MPOOL.mpool_free" [CBR p; CBR r1]) #;
              SIGNAL #= (SIGNAL + Int.one) #;
              Skip
          ).


    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "i" ; "r"; "next_chunk"]. Defined.
    Definition alloc_and_free1F: function.
      mk_function_tac (alloc_and_free 1) ([]: list var) ["p" ; "i" ; "r"; "r0" ; "r1" ; "r2"; "new_chunk"].
    Defined.
    Definition alloc_and_free2F: function.
      mk_function_tac (alloc_and_free 2) ([]: list var) ["p" ; "i" ; "r"; "r0" ; "r1" ; "r2"; "new_chunk"].
    Defined.

    Definition main_program: program :=
      [
        ("main", mainF) ;
      ("alloc_and_free1", alloc_and_free1F) ;
      ("alloc_and_free2", alloc_and_free2F) 
      ].

    Definition modsems: list ModSem :=
      [program_to_ModSem main_program ; MPOOLCONCUR.mpool_modsem ; LOCK.lock_modsem].

    Definition isem: itree Event unit :=
      eval_multimodule_multicore
        modsems [ "main" ; "alloc_and_free1" ; "alloc_and_free2" ].
    
  End MPOOLTEST_FOUR.

  Module MPOOLTEST_FIVE.

    (* Test with HighSpec *)

    Definition main (p p_fallback p_fallback2 begin res: var) : stmt :=
      (* Put "test plus" (Plus (Vcomp (Vint (repr 1))) (Vcomp (Vint (repr 5)))) #; *)
      (Call "MPOOL.mpool_init_locks" []) #;
      (Call "MPOOL.mpool_enable_locks" []) #;
      (* #assume mpool_locks_enabled #; *)
      Alloc p (Int.repr 5) #;
      Put "main: before init: " p #;
      (* initialize it with the entry size - 8 *)
      Call "MPOOL.mpool_init" [CBV p; CBV (Int64.repr 8)] #;
      Alloc p_fallback (Int.repr 5) #;
      (Call "MPOOL.mpool_init_with_fallback" [CBR p_fallback; CBR p]) #;
      Put "main: after init: " p #;
      begin #= (Vcomp (Vptr 2%positive (Ptrofs.repr 160))) #;
      res #= (Call "MPOOL.mpool_add_chunk" [CBR p_fallback; CBR begin; CBV (Int64.repr 24)]) #;
      Alloc p_fallback2 (Int.repr 5) #;
      (Call "MPOOL.mpool_init_from" [CBR p_fallback2; CBR p_fallback]) #;
      begin #= (Vcomp (Vptr 2%positive (Ptrofs.repr 184))) #;
      res #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBR begin; CBV (Int64.repr 16)]) #;
      begin #= (Vcomp (Vptr 2%positive (Ptrofs.repr 200))) #;
      res #= (Call "MPOOL.mpool_add_chunk" [CBR p_fallback2; CBR begin; CBV (Int64.repr 16)]) #;
      (* begin #= (Vcomp (Vptr 2%positive (Ptrofs.repr 216))) #; *)
      (* res #= (Call "MPOOL.mpool_free" [CBR p; CBR begin]) #; *)
      (* begin #= (Vcomp (Vptr 2%positive (Ptrofs.repr 224))) #; *)
      (* res #= (Call "MPOOL.mpool_free" [CBR p_fallback2; CBR begin]) #; *)
      (* begin #= (Vcomp (Vptr 2%positive (Ptrofs.repr 232))) #; *)
      (* res #= (Call "MPOOL.mpool_free" [CBR p_fallback2; CBR begin]) #; *)
      (Call "MPOOL.mpool_fini" [CBR p_fallback2]) #;
      (Call "MPOOL.print_mpool" [CBR p]) #;
      Skip.

    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "p_fallback" ; "p_fallback2" ; "begin" ; "res"]. Defined.

    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem1: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; MPOOLCONCUR.mpool_modsem ; LOCK.lock_modsem].

    Definition isem2: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; (MpoolHighSpec.mpool_modsem)].

  End MPOOLTEST_FIVE.

End MPOOLTEST.
