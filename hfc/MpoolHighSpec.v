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

Import Int64.

Require Import Maps.
Set Implicit Arguments.

Section ABSTSTATE.

Variable A: Type.
Definition chunk : Type := list A.
Definition entry : Type := list A.
    
Inductive Mpool : Type :=
  mkMpool {
      entry_size : Z;
      chunk_list : list chunk;
      entry_list : list entry;
      fallback: option positive
    }.

Record MpoolAbstState : Type :=
  mkMpoolAbstState {
      mpool_map : PMap.t Mpool; (* id -> mpool *)
      addr_to_id : ZMap.t positive; (* mem addr -> id *)
      next_id : positive; (* new mpool id *)
    }.

End ABSTSTATE.

Section HIGHSPEC.

Variable A: Type.
Variable st: MpoolAbstState A.



Definition mpool_init_spec (p entry_size:Z) : MpoolAbstState A :=
  let mp := mkMpool entry_size [] [] None in
  let i := next_id st in
  mkMpoolAbstState (PMap.set i mp (mpool_map st)) (ZMap.set p i (addr_to_id st)) (Pos.succ i).
                    
Definition mpool_free_spec (p:Z) (ptr:list A) :=
  let i := ZMap.get p (addr_to_id st) in
  let mp := (mpool_map st) !! i in
  let mp' := mkMpool (entry_size mp) (chunk_list mp) (ptr::entry_list mp) (fallback mp) in
  mkMpoolAbstState (PMap.set i mp' (mpool_map st)) (addr_to_id st) i.

Definition mpool_add_chunk_spec (p:Z) (c:chunk A) (size:Z) :=
  let i := ZMap.get p (addr_to_id st) in
  let mp := (mpool_map st) !! i in
  let mp' := mkMpool (entry_size mp) (c::(chunk_list mp)) (entry_list mp) (fallback mp) in
  (mkMpoolAbstState (PMap.set i mp' (mpool_map st)) (addr_to_id st) i, true).

Definition mpool_alloc_no_fallback_spec (p:Z) :=
  let i := ZMap.get p (addr_to_id st) in
  let mp := (mpool_map st) !! i in
  let entry := (entry_list mp) in
  if negb (Nat.eqb (length entry) O)
  then (
      let mp' := mkMpool (entry_size mp) (chunk_list mp) (tl (entry_list mp)) (fallback mp) in
      (mkMpoolAbstState (PMap.set i mp' (mpool_map st)) (addr_to_id st) i, Some (hd entry))
    )
  else
    (
      let chunk := (chunk_list mp) in
      if (Nat.eqb (length chunk) O)
      then (st, None)
      else
    (* should handle ugly case *)
      let mp' := mkMpool (entry_size mp) (tl (chunk_list mp)) (entry_list mp) (fallback mp) in
      ((mkMpoolAbstState (PMap.set i mp' (mpool_map st)) (addr_to_id st) i), (Some (hd chunk)))
    ). 

End HIGHSPEC.

Section AA.
  
Context {iteration_bound: nat}.
Variable A: Type.
Hypothesis id_to_addr : positive -> Z.

Fixpoint mpool_alloc_spec_aux (st:MpoolAbstState A) (p:Z) (n:nat) :=
  if Nat.eqb iteration_bound n then (st, None) else
  let i := ZMap.get p (addr_to_id st) in
  let mp := (mpool_map st) !! i in
  let (st', ret) := mpool_alloc_no_fallback_spec st p in
  match ret with
  | Some ret => (st', Some ret)
  | None => match (fallback mp) with
           | None => (st', None)
           | Some mp' => mpool_alloc_spec_aux st' (id_to_addr mp') (S n)
           end
  end.

Definition mpool_alloc_spec (p:Z) :=
    
(* Definition mpool_fini_spec (p:Z) := *)
(*   let i := ZMap.get p (addr_to_id st) in *)
(*   let mp := (mpool_map st) !! i in *)
(*   match (fallback mp) with *)
(*   | None => st *)
(*   | Some fb => *)
    
(*   end *)


Definition mpool_alloc_fallback (

End MPOOLHIGHSPEC.
