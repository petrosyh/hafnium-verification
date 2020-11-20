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
Require Import Values.
Require Import Integers.
Require Import Constant.
Require Import Lang.
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Require Import Maps.
Set Implicit Arguments.

Section ABSTSTATE.

Definition chunk : Type := Values.val.
Definition entry : Type := Values.val.

Definition PtrTree := (PTree.t (ZTree.t positive)).
    
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
      addr_to_id : PtrTree; (* memory ptr -> id *)
      next_id : positive; (* new mpool id *)
    }.

Definition initial_state : MpoolAbstState :=
  mkMpoolAbstState (PTree.empty Mpool) (PTree.empty (ZTree.t positive)) 1%positive.

Definition PtrTree_set (b: block) (ofs: ptrofs) (v: positive) (map: PtrTree) :=
  let zt := match PTree.get b map with
            | Some zt => zt
            | None => (ZTree.empty positive)
            end in
  PTree.set b (ZTree.set (Ptrofs.unsigned ofs) v zt) map
.

Definition PtrTree_get (b: block) (ofs: ptrofs) (map: PtrTree) :=
  match PTree.get b map with
  | Some zt => ZTree.get (Ptrofs.unsigned ofs) zt
  | None => None
  end
.

Definition PtrTree_remove (b: block) (ofs: ptrofs) (map: PtrTree) :=
  match PTree.get b map with
  | Some zt => PTree.set b (ZTree.remove (Ptrofs.unsigned ofs) zt) map
  | None => map
  end
.

(* m1: child, m2:parent *)
Inductive child_mpool (st:MpoolAbstState) (m1: Mpool) : Mpool -> Prop :=
| child_base
    id m2
    (FB: (fallback m1) = Some id)
    (CHILD: PTree.get id (mpool_map st) = Some m2)
  :
    child_mpool st m1 m2
| child_step
    id m2 m3
    (CHILD1: (fallback m1) = Some id)
    (CHILD: PTree.get id (mpool_map st) = Some m2)
    (CHILD2: child_mpool st m2 m3)
  :
    child_mpool st m1 m3.

Record wf_state (st:MpoolAbstState) : Prop :=
  mkWfState {
      no_cycle:
        forall id mp, PTree.get id (mpool_map st) = Some mp -> ~ child_mpool st mp mp;
      map_addr:
        forall id mp, PTree.get id (mpool_map st) = Some mp ->
                 exists b ofs, PtrTree_get b ofs (addr_to_id st) = Some id;
      addr_map:
        forall b ofs id, PtrTree_get b ofs (addr_to_id st) = Some id ->
                    exists mp, PTree.get id (mpool_map st) = Some mp
  }.

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

Variable st: MpoolAbstState.
Context {eff : Type -> Type}.
Context {HasEvent : Event -< eff}.

Definition mpool_init_spec (p entry_size: val) : itree eff MpoolAbstState :=
  match p with
  | Vcomp (Vptr b ofs) =>
    let i := next_id st in
    match entry_size with
    | Vcomp (Vint entry_size) =>
      let mp := mkMpool (Int.signed entry_size) [] [] None in
      Ret (mkMpoolAbstState (PTree.set i mp (mpool_map st))
                            (PtrTree_set b ofs i (addr_to_id st)) (Pos.succ i))
    | Vcomp (Vlong entry_size) =>
      let mp := mkMpool (Int64.signed entry_size) [] [] None in
      Ret (mkMpoolAbstState (PTree.set i mp (mpool_map st))
                            (PtrTree_set b ofs i (addr_to_id st)) (Pos.succ i))
    | _ => triggerNB "entry_size <> integer"
    end
  | _ => triggerNB "p <> Ptr"
  end
.

Definition main (p i r next_chunk: var): stmt :=
  (Call "MPOOL.mpool_init_locks" []) #;
  (Call "MPOOL.mpool_enable_locks" []) #;
  Alloc p (Int.repr 5) #;
  Put "main: before init: " p #;
  Call "MPOOL.mpool_init" [CBR p; CBV (Int.repr 8)] #;
  Put "main: after init: " p #;
  next_chunk #= (Vcomp (Vptr 2%positive (Ptrofs.repr 160))) #;
  r #= (Call "MPOOL.mpool_add_chunk" [CBR p; CBR next_chunk; CBV (Int64.repr 160)]).

  
(* Definition mpool_init_from_spec (p from: val) := *)
(*   match from with *)
(*   | Vcomp (Vptr b ofs) => *)
(*     let i := PtrTree_get b ofs (addr_to_id st) in *)
(*     let mp := PTree.get i (mpool_map st) in *)
(*     let mp' := (mkMpool (entry_size mp) (chunk_list mp) (entry_list mp) (fallback mp)) in *)
(*     match p with *)
(*     | Vcomp (Vptr b2 ofs2) => *)
(*       Ret (mkMpoolAbstState *)
(*              (PTree.set (next_id st) mp' (PTree.remove i (mpool_map st))) *)
(*              (PtrTree_set b2 ofs2 (next_id st) (PtrTree_remove b ofs (addr_to_id st))) *)
(*              (Pos.succ (next_id st))) *)
(*     | _ => triggerNB "p <> Ptr" *)
(*     end *)
(*   | _ => triggerNB "from <> Ptr" *)
(*   end *)
(* . *)
(*   i <- ZTree.get from (addr_to_id st);; *)
(*   mp <- PTree.get i (mpool_map st);; *)
(*   mp' <- Some (mkMpool (entry_size mp) (chunk_list mp) (entry_list mp) (fallback mp));; *)
(*   Some (mkMpoolAbstState *)
(*           (PTree.set (next_id st) mp' (PTree.remove i (mpool_map st))) *)
(*           (ZTree.set p (next_id st) (ZTree.remove from (addr_to_id st))) *)
(*           (Pos.succ (next_id st))). *)

(* Definition mpool_init_with_fallback_spec (p fallback:Z) := *)
(*   i <- ZTree.get fallback (addr_to_id st);; *)
(*   mp <- PTree.get i (mpool_map st);; *)
(*   mp' <- Some (mkMpool (entry_size mp) [] [] (Some i));; *)
(*   Some (mkMpoolAbstState (PTree.set (next_id st) mp' (mpool_map st)) *)
(*                          (ZTree.set p (next_id st) (addr_to_id st)) *)
(*                          (Pos.succ (next_id st))). *)

(* Definition mpool_fini_spec (p:Z) := *)
(*   i <- ZTree.get p (addr_to_id st);; *)
(*   mp <- PTree.get i (mpool_map st);; *)
(*   mpool_map' <- *)
(*   Some (match fallback mp with *)
(*         | Some i_fallback => *)
(*           match PTree.get i_fallback (mpool_map st) with *)
(*           | Some mp_fallback => *)
(*             (PTree.set i_fallback (mkMpool (entry_size mp_fallback) *)
(*                                            ((rev (chunk_list mp)) ++ (chunk_list mp_fallback)) *)
(*                                            ((rev (entry_list mp)) ++ (entry_list mp_fallback)) *)
(*                                            (fallback mp_fallback)) *)
(*                        (mpool_map st)) *)
(*           | None => (mpool_map st) (* Can't reachable *) *)
(*           end *)
(*         | None => (mpool_map st) *)
(*         end);; *)
(*   Some (mkMpoolAbstState (PTree.remove i mpool_map') (ZTree.remove p (addr_to_id st)) *)
(*                          (next_id st)). *)

(* Definition mpool_free_spec (p:Z) (ptr:list A) := *)
(*   i <- ZTree.get p (addr_to_id st);; *)
(*   mp <- PTree.get i (mpool_map st);; *)
(*   mp' <- Some (mkMpool (entry_size mp) (chunk_list mp) (ptr::entry_list mp) (fallback mp));; *)
(*   Some (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) i). *)

(* Definition mpool_add_chunk_spec (p:Z) (c:chunk A) (size:Z) := *)
(*   i <- ZTree.get p (addr_to_id st);; *)
(*   mp <- PTree.get i (mpool_map st);; *)
(*   mp' <- Some (mkMpool (entry_size mp) (c::(chunk_list mp)) (entry_list mp) (fallback mp));; *)
(*   Some (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) i, true). *)

(* Definition mpool_alloc_no_fallback_spec (p:Z) := *)
(*   i <- ZTree.get p (addr_to_id st);; *)
(*   mp <- PTree.get i (mpool_map st);; *)
(*   entry <- Some (entry_list mp);; *)
(*   if negb (Nat.eqb (length entry) O) *)
(*   then ( *)
(*       let mp' := mkMpool (entry_size mp) (chunk_list mp) (tl (entry_list mp)) (fallback mp) in *)
(*       Some (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) i, Some (hd entry)) *)
(*     ) *)
(*   else *)
(*     ( *)
(*       let chunk := (chunk_list mp) in *)
(*       if (Nat.eqb (length chunk) O) *)
(*       then Some (st, None) *)
(*       else *)
(*     (* should handle ugly case *) *)
(*       let mp' := mkMpool (entry_size mp) (tl (chunk_list mp)) (entry_list mp) (fallback mp) in *)
(*       Some ((mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) i), (Some (hd chunk))) *)
(*     ). *)

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

(* Section TEST. *)

(*   Definition p := 3. *)
(*   Definition p_fallback := 4. *)
(*   Definition p_fallback2 := 5. *)
  
(*   Definition main := *)
(*     st1 <- mpool_init_spec (initial_state Z) p 8;; *)
(*     st2 <- mpool_init_with_fallback_spec st1 p_fallback p;; *)
(*     res_st3 <- mpool_add_chunk_spec st2 p_fallback [1;2;3] 3;; *)
(*     st3 <- Some (fst res_st3);; *)
(*     st4 <- mpool_init_from_spec st3 p_fallback2 p_fallback;; *)
(*     res_st5 <- mpool_add_chunk_spec st4 p_fallback2 [4;5] 2;; *)
(*     st5 <- Some (fst res_st5);; *)
(*     res_st6 <- mpool_add_chunk_spec st5 p [6;7] 2;; *)
(*     st6 <- Some (fst res_st6);; *)
(*     st7 <- mpool_free_spec st6 p [8];; *)
(*     st8 <- mpool_free_spec st7 p_fallback2 [9];; *)
(*     st9 <- mpool_free_spec st8 p_fallback2 [10];; *)
(*     st10 <- mpool_fini_spec st9 p_fallback2;; *)
(*     Some st10 *)
(*   . *)

(*   Compute main. *)

(* End TEST. *)

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
(*                                                                ((callE ((MpoolAbstState A) * Z) (option ((MpoolAbstState A) * option (list (list (entry A)) -> list (entry A))))) +' E) *)
(*                                                                (option ((MpoolAbstState A) * option (list (list (entry A)) -> list (entry A)))) := *)
  
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
(*         | Some ret => Ret (Some (st', Some ret)) *)
(*         | None => match (fallback mp) with *)
(*                  | None => Ret (Some (st', None)) *)
(*                  | Some mp' => call (st', (id_to_addr mp')) *)
(*                  end *)
(*         end *)
(*       end *)
(*     end *)
(*   end. *)

(* Definition mpool_alloc_spec (st:MpoolAbstState A) (p:Z) := *)
(*   rec mpool_alloc_spec_body (st, p). *)

(* Lemma mpool_alloc_spec_terminate *)
(*       st p *)
(*       (WF: wf_state st) *)
(*   : *)
(*     exists v, mpool_alloc_spec st p = Ret v. *)
(* Proof. *)
(*   admit "". *)
(* Admitted. *)
      

End ALLOC2.                     

(* Definition fact_body (x : nat) : itree (callE nat nat +' E) nat := *)
(*   match x with *)
(*   | 0 => Ret 1 *)
(*   | S m => *)
(*     y <- call m ;;  (* Recursively compute [y := m!] *) *)
(*     Ret (x * y) *)
(*   end. *)



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
