(*
 * Copyright 2020 Jieung Kim
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
Require Import Types.
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Set Implicit Arguments.

(* XXX: Need to move this part into Lang.v file *)
Section STORELOADSYNTACTICSUGAR.
  
  Definition store_at_i (p : var) (offset : Z) (e: expr) : stmt :=
    (* Put " " i#; *)
    Store (Cast (Plus (Cast p tint) (repr offset)) tptr) e.

  Definition load_at_i (p : var) (offset : Z) : expr :=
    (* Put " " i#; *)
    Load (Cast (Plus (Cast p tint) (repr offset)) tptr).
  
End STORELOADSYNTACTICSUGAR.

(* Some dependencies: 
   1. inc/hf/addr.h - some address translations and type definitions such as paddr_t and so on 
   2. inc/hf/arch/cpu.h - 5 depends on this file
   3. src/arch/arch64/cpu.c - 5 depends on this file
   4. inc/hf/arch/mm.h - a header file for 4. 
   5. src/arch/arch64/mm.c - several simple functions are used in src/mm.c
   6. inc/hf/mm.h - a header file for this mm.c
   7. src/mpool.c 
   8. inc/hf/mpool
   9. inc/hf/layout.c
  10. src/layout.c
*)

Section MM.
  
  


End MM.
