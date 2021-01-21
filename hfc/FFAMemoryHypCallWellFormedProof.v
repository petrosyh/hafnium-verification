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
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Require Export FFAMemoryHypCallState.
Require Export FFAMemoryHypCall.

Section WELLFORMEDLEMMA.
  
  (*
  Lemma ffa_mem_send_well_formed_preserve:
    forall (st: AbstractState) (share_func : FFA_FUNCTION_TYPE) (length address page_count: Z),
      well_formed st ->
      match api_ffa_mem_send share_func length address page_count st with
      | Ret (_, st') => well_formed st 
      | _ => True
      end.
  Admitted.
   *)
  
End WELLFORMEDLEMMA.


Section WELLFORMEDPROOF.
  
  (*
  Lemma ffa_mem_send_well_formed_preserve:
    forall (st: AbstractState) (share_func : FFA_FUNCTION_TYPE) (length address page_count: Z),
      well_formed st ->
      match api_ffa_mem_send share_func length address page_count st with
      | Ret (_, st') => well_formed st 
      | _ => True
      end.
  Admitted.
   *)
  
End WELLFORMEDPROOF.

