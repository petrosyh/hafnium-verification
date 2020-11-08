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


Inductive terminate {E} {R} (it:itree E R) : Prop :=
| TermRet
    v
    (RET: observe it = RetF v)
| TermTau
    (TAU: observe it = TauF it).

Definition E := void1.

(* Definition fact_body (x : nat) : itree (callE nat nat +' E) nat := *)
(*  match x with *)
(*   | O => Ret 1%nat *)
(*   | S m => *)
(*     y <- call m ;;  (* Recursively compute [y := m!] *) *)
(*     Ret (x * y)%nat *)
(*   end. *)

(* Definition factorial (n : nat) : itree E nat := *)
(*   rec fact_body n. *)

(* Lemma unfold_factorial : forall x, *)
(*     factorial x ≈ match x with *)
(*                   | O => Ret 1%nat *)
(*                   | S m => *)
(*                     y <- factorial m ;; *)
(*                     Ret (x * y)%nat *)
(*                   end. *)
(* Proof. *)
(*   intros x. *)
(*   unfold factorial. *)
(*   induction x; simpl in *. *)
(*   - rewrite rec_as_interp. ss. *)
(*     unfold interp. ss. *)

(* Lemma aa *)
(*       n *)
(*   : *)
(*     terminate (factorial n). *)
(* Proof. *)
(*   destruct n. *)
(*   - econs. instantiate (1:=1%nat). *)
    

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
      mpool_map : PTree.t Mpool; (* id -> mpool *)
      addr_to_id : ZTree.t positive; (* mem addr -> id *)
      next_id : positive; (* new mpool id *)
    }.

Definition initial_state : MpoolAbstState :=
  mkMpoolAbstState (PTree.empty Mpool) (ZTree.empty positive) 1%positive.

End ABSTSTATE.

(** Error monad with options or lists *)

(* Notation "'do' X <- A ; B" := (match A with Some X => B | None => None end) *)
(*   (at level 200, X ident, A at level 100, B at level 200) *)
(*   : option_monad_scope. *)

(* Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => None end) *)
(*   (at level 200, X ident, Y ident, A at level 100, B at level 200) *)
(*   : option_monad_scope. *)

(* Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => None end) *)
(*   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200) *)
(*   : option_monad_scope. *)

(* Notation " 'check' A ; B" := (if A then B else None) *)
(*   (at level 200, A at level 100, B at level 200) *)
(*   : option_monad_scope. *)

(* Notation "'do' X <- A ; B" := (match A with Some X => B | None => nil end) *)
(*   (at level 200, X ident, A at level 100, B at level 200) *)
(*   : list_monad_scope. *)

(* Notation " 'check' A ; B" := (if A then B else nil) *)
(*   (at level 200, A at level 100, B at level 200) *)
(*   : list_monad_scope. *)

Section HIGHSPEC.

Variable A: Type.
Variable st: MpoolAbstState A.

Definition mpool_init_spec (p entry_size:Z) : MpoolAbstState A :=
  let mp := mkMpool entry_size [] [] None in
  let i := next_id st in
  mkMpoolAbstState (PTree.set i  mp (mpool_map st)) (ZTree.set p i (addr_to_id st)) (Pos.succ i).

Definition mpool_init_from_spec (p from:Z) :=
  i <- ZTree.get from (addr_to_id st);;
  mp <- PTree.get i (mpool_map st);;
  mp' <- Some (mkMpool (entry_size mp) (chunk_list mp) (entry_list mp) None);;
  Some (mkMpoolAbstState
          (PTree.set (next_id st) mp' (PTree.remove i (mpool_map st)))
          (ZTree.set p (next_id st) (ZTree.remove from (addr_to_id st)))
          (Pos.succ i)).

Definition mpool_init_with_fallback_spec (p fallback:Z) :=
  i <- ZTree.get fallback (addr_to_id st);;
  mp <- (mpool_map st) ! i;;
  mp' <- Some (mkMpool (entry_size mp) [] [] (Some i));;
  Some (mkMpoolAbstState (PTree.set (next_id st) mp' (mpool_map st))
                         (ZTree.set p (next_id st) (addr_to_id st))
                         (Pos.succ i)).

Definition mpool_fini_spec (p:Z) :=
  i <- ZTree.get p (addr_to_id st);;
  mp <- (mpool_map st) ! i;;
  mpool_map' <-
  Some (match fallback mp with
        | Some i_fallback =>
          match (mpool_map st) ! i_fallback with
          | Some mp_fallback =>
            (PTree.set i_fallback (mkMpool (entry_size mp_fallback)
                                           ((rev (chunk_list mp)) ++ (chunk_list mp_fallback))
                                           ((rev (entry_list mp)) ++ (entry_list mp_fallback))
                                           (fallback mp_fallback))
                       (mpool_map st))
          | None => (mpool_map st) (* Can't reachable *)
          end
        | None => (mpool_map st)
        end);;
  Some (mkMpoolAbstState (PTree.remove i mpool_map') (ZTree.remove p (addr_to_id st))
                         (next_id st)).

Definition mpool_free_spec (p:Z) (ptr:list A) :=
  i <- ZTree.get p (addr_to_id st);;
  mp <- PTree.get i (mpool_map st);;
  mp' <- Some (mkMpool (entry_size mp) (chunk_list mp) (ptr::entry_list mp) (fallback mp));;
  Some (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) i).

Definition mpool_add_chunk_spec (p:Z) (c:chunk A) (size:Z) :=
  i <- ZTree.get p (addr_to_id st);;
  mp <- PTree.get i (mpool_map st);;
  mp' <- Some (mkMpool (entry_size mp) (c::(chunk_list mp)) (entry_list mp) (fallback mp));;
  Some (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) i, true).

Definition mpool_alloc_no_fallback_spec (p:Z) :=
  i <- ZTree.get p (addr_to_id st);;
  mp <- PTree.get i (mpool_map st);;
  entry <- Some (entry_list mp);;
  if negb (Nat.eqb (length entry) O)
  then (
      let mp' := mkMpool (entry_size mp) (chunk_list mp) (tl (entry_list mp)) (fallback mp) in
      Some (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) i, Some (hd entry))
    )
  else
    (
      let chunk := (chunk_list mp) in
      if (Nat.eqb (length chunk) O)
      then Some (st, None)
      else
    (* should handle ugly case *)
      let mp' := mkMpool (entry_size mp) (tl (chunk_list mp)) (entry_list mp) (fallback mp) in
      Some ((mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) i), (Some (hd chunk)))
    ). 

End HIGHSPEC.

(* Section ALLOC. *)

(* Context {iteration_bound: nat}. *)
(* Variable A: Type. *)
(* Hypothesis id_to_addr : positive -> Z. *)

(* Fixpoint mpool_alloc_spec_aux (st:MpoolAbstState A) (p:Z) (n:nat) := *)
(*   match n with *)
(*   | O => (st, None) *)
(*   | S n' => *)
(*     let i := ZMap.get p (addr_to_id st) in *)
(*     let mp := (mpool_map st) !! i in *)
(*     let (st', ret) := mpool_alloc_no_fallback_spec st p in *)
(*     match ret with *)
(*     | Some ret => (st', Some ret) *)
(*     | None => match (fallback mp) with *)
(*              | None => (st', None) *)
(*              | Some mp' => mpool_alloc_spec_aux st' (id_to_addr mp') n' *)
(*              end *)
(*     end *)
(*   end. *)

(* Definition mpool_alloc_spec (st:MpoolAbstState A) (p:Z) := *)
(*   mpool_alloc_spec_aux st p iteration_bound. *)

(* End ALLOC. *)

Section ALLOC2.

(* Definition fact_body (x : nat) : itree (callE nat nat +' E) nat := *)
(*  match x with *)
(*   | O => Ret 1%nat *)
(*   | S m => *)
(*     y <- call m ;;  (* Recursively compute [y := m!] *) *)
(*     Ret (x * y)%nat *)
(*   end. *)

Variable A: Type.
Hypothesis id_to_addr : positive -> Z.

(* Definition mpool_alloc_spec_body (stp: MpoolAbstState A * Z) : itree *)
(*                                                                ((callE ((MpoolAbstState A) * Z) ((MpoolAbstState A) * option (list (list (entry A)) -> list (entry A)))) +' E) *)
(*                                                                ((MpoolAbstState A) * option (list (list (entry A)) -> list (entry A))) := *)
  
(*   let st := fst stp in *)
(*   let p := snd stp in *)
(*   let i := ZTree.get p (addr_to_id st) in *)
(*   match i with *)
(*   | None => Ret None *)
(*   | Some i => *)
(*     let mp := PTree.get i (mpool_map st) in *)
(*     match mp with *)
(*     | None => Ret None *)
(*     | Some mp => *)
(*       let stret := mpool_alloc_no_fallback_spec st p in *)
(*       match stret with *)
(*       | None => Ret None *)
(*       | Some stret => *)
(*         let (st', ret) := (fst stret, snd stret) in *)
(*         match ret with *)
(*         | Some ret => Ret (st', Some ret) *)
(*         | None => match (fallback mp) with *)
(*                  | None => Ret (st', None) *)
(*                  | Some mp' => call (st', (id_to_addr mp')) *)
(*                  end *)
(*         end *)
(*       end *)
(*     end *)
(*   end. *)

(* Definition mpool_alloc_spec' (st:MpoolAbstState A) (p:Z) := *)
(*   rec mpool_alloc_spec_body (st, p). *)


End ALLOC2.                                                          

(* Definition fact_body (x : nat) : itree (callE nat nat +' E) nat := *)
(*   match x with *)
(*   | 0 => Ret 1 *)
(*   | S m => *)
(*     y <- call m ;;  (* Recursively compute [y := m!] *) *)
(*     Ret (x * y) *)
(*   end. *)



(* Definition mpool_alloc_spec_body : (MpoolAbstState A * Z) -> itree E (MpoolAbstState A * option (entry A)) := *)
(*   rec-fix mpool_alloc_body stp := *)
(*     let st := fst stp in *)
(*     let p := snd stp in *)
(*     let i := ZMap.get p (addr_to_id st) in *)
(*     let mp := (mpool_map st) !! i in *)
(*     let (st', ret) := mpool_alloc_no_fallback_spec st p in *)
(*     match ret with *)
(*     | Some ret => Ret (st', Some ret) *)
(*     | None => match (fallback mp) with *)
(*              | None => Ret (st', None) *)
(*              | Some mp' => mpool_alloc_body (st', (id_to_addr mp')) *)
(*              end *)
(*     end. *)

(*     match x with *)
(*     | 0 => Ret 1 *)
(*     | S m => y <- fact m ;; Ret (x * y) *)
(*     end. *)

(* Definition mpool_alloc_body (ST:MpoolAbstState A) (p:Z) : itree (callE  *)


(* Fixpoint mpool_alloc_spec_aux (st:MpoolAbstState A) (p:Z) (n:nat) := *)
(*   match n with *)
(*   | O => (st, None) *)
(*   | S n' => *)
(*     let i := ZMap.get p (addr_to_id st) in *)
(*     let mp := (mpool_map st) !! i in *)
(*     let (st', ret) := mpool_alloc_no_fallback_spec st p in *)
(*     match ret with *)
(*     | Some ret => (st', Some ret) *)
(*     | None => match (fallback mp) with *)
(*              | None => (st', None) *)
(*              | Some mp' => mpool_alloc_spec_aux st' (id_to_addr mp') n' *)
(*              end *)
(*     end *)
(*   end. *)


(* Definition mpool_alloc_spec (st:MpoolAbstState A) (p:Z) := *)
(*   mpool_alloc_spec_aux st p iteration_bound. *)

(* End MPOOLHIGHSPEC. *)

(* Section AA. *)
  
(* Context {iteration_bound: nat}. *)
(* Variable A: Type. *)
(* Hypothesis id_to_addr : positive -> Z. *)

(* Fixpoint mpool_alloc_spec_aux (st:MpoolAbstState A) (p:Z) (n:nat) := *)
(*   if Nat.eqb iteration_bound n then (st, None) else *)
(*   let i := ZMap.get p (addr_to_id st) in *)
(*   let mp := (mpool_map st) !! i in *)
(*   let (st', ret) := mpool_alloc_no_fallback_spec st p in *)
(*   match ret with *)
(*   | Some ret => (st', Some ret) *)
(*   | None => match (fallback mp) with *)
(*            | None => (st', None) *)
(*            | Some mp' => mpool_alloc_spec_aux st' (id_to_addr mp') (S n) *)
(*            end *)
(*   end. *)

(* Definition mpool_alloc_spec (p:Z) := *)
    
(* (* Definition mpool_fini_spec (p:Z) := *) *)
(* (*   let i := ZMap.get p (addr_to_id st) in *) *)
(* (*   let mp := (mpool_map st) !! i in *) *)
(* (*   match (fallback mp) with *) *)
(* (*   | None => st *) *)
(* (*   | Some fb => *) *)
    
(* (*   end *) *)


(* Definition mpool_alloc_fallback ( *)
