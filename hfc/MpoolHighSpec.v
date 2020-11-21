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
      addr_to_id : PTree.t (ZTree.t positive); (* block -> offset -> id *)
      id_to_addr : PTree.t (positive * Z); (* id -> (block, offset *)
      next_id : positive; (* new mpool id *)
    }.

Definition initial_state : MpoolAbstState :=
  mkMpoolAbstState (PTree.empty Mpool) (PTree.empty (ZTree.t positive)) (PTree.empty (positive * Z)) 1%positive.

Definition PtrTree_set (ptr: positive * Z) (v: positive) (map: PTree.t (ZTree.t positive)) :=
  let zt := match PTree.get (fst ptr) map with
            | Some zt => zt
            | None => (ZTree.empty positive)
            end in
  PTree.set (fst ptr) (ZTree.set (snd ptr) v zt) map
.

Definition PtrTree_get (ptr: positive * Z) (map: PTree.t (ZTree.t positive)) :=
  match PTree.get (fst ptr) map with
  | Some zt => ZTree.get (snd ptr) zt
  | None => None
  end
.

Definition PtrTree_remove (ptr: positive * Z) (map: PTree.t (ZTree.t positive)) :=
  match PTree.get (fst ptr) map with
  | Some zt => PTree.set (fst ptr) (ZTree.remove (snd ptr) zt) map
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
        forall id mp, PTree.get id (mpool_map st) = Some mp -> ~ child_mpool st mp mp
  }.

End ABSTSTATE.

Variable Z_to_string: Z -> string.
Extract Constant Z_to_string =>
"fun z -> (HexString.of_Z z)"
.

Section HIGHSPECITREE.

Variable A: Type.
Definition state := MpoolAbstState A.
Variable a: A. (* neede when we make chunk *)

Inductive updateStateE: Type -> Type :=
| GetState : updateStateE (MpoolAbstState A)
| SetState (st1:MpoolAbstState A): updateStateE unit.

Definition updateState_handler {E: Type -> Type}
  : updateStateE ~> stateT (MpoolAbstState A) (itree E) :=
  fun _ e st =>
    match e with
    | GetState => Ret (st, st)
    | SetState st' => Ret (st', tt)
    end.

(* Variable st: MpoolAbstState A. *)
(* return type is needed? *)

Definition mpoolE := CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event.

Definition mpool_init_spec (p: positive * Z) (entry_size: Z) : itree mpoolE unit :=
  st <- trigger GetState;;
  let i := next_id st in
  let mp := mkMpool entry_size [] [] None in
  let st' := (mkMpoolAbstState (PTree.set i mp (mpool_map st))
                               (PtrTree_set p i (addr_to_id st))
                               (PTree.set i p (id_to_addr st))
                               (Pos.succ i)) in
  trigger (SetState st')
.

Definition mpool_init_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr blk ofs); args2] =>
    match args2 with
    | Vcomp (Vint entry_size) =>
      mpool_init_spec (blk, Ptrofs.unsigned ofs) (Int.unsigned entry_size);;
      Ret (Vnull, args)
    | Vcomp (Vlong entry_size) =>
      mpool_init_spec (blk, Ptrofs.unsigned ofs) (Int64.unsigned entry_size);;
      Ret (Vnull, args)
    | _ => triggerUB "Wrong args: mpool_init"
    end
  | _ => triggerUB "Wrong args: mpool_init"
  end
.

Definition mpool_init_from_spec (p: positive * Z) (from: positive * Z) : itree mpoolE unit :=
  st <- trigger GetState;;
  match (PtrTree_get from (addr_to_id st)) with
  | None => Ret tt
  | Some from_id =>
    match (PTree.get from_id (mpool_map st)) with
    | None => Ret tt (* Can't reachable with wf state *)
    | Some from_mp =>
      mpool_init_spec p (entry_size from_mp);;
      st' <- trigger GetState;;
      match PtrTree_get p (addr_to_id st') with
      | Some p_id =>
        let mp := (mkMpool (entry_size from_mp) (chunk_list from_mp)
                           (entry_list from_mp) (fallback from_mp)) in
        let st'' := (mkMpoolAbstState (PTree.remove from_id (PTree.set p_id mp (mpool_map st')))
                                      (PtrTree_remove from (addr_to_id st'))
                                      (PTree.remove from_id (id_to_addr st'))
                                      (next_id st')) in
        trigger (SetState st'');; Ret tt
      | None => Ret tt (* Can't reachable *)
      end
    end
  end
.

Definition mpool_init_from_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr p_blk p_ofs); Vcomp (Vptr from_blk from_ofs)] =>
      mpool_init_from_spec (p_blk, Ptrofs.unsigned p_ofs) (from_blk, Ptrofs.unsigned from_ofs);;
      Ret (Vnull, args)
  | _ => triggerUB "Wrong args: mpool_init_from"
  end
.

Definition mpool_init_with_fallback_spec (p fallback: positive * Z) : itree mpoolE unit :=
  st <- trigger GetState;;
  match (PtrTree_get fallback (addr_to_id st)) with
  | None => Ret tt
  | Some fallback_id =>
    match PTree.get fallback_id (mpool_map st) with
    | None => Ret tt
    | Some mp =>
      let mp' := (mkMpool (entry_size mp) [] [] (Some fallback_id)) in
      let st' := (mkMpoolAbstState (PTree.set (next_id st) mp' (mpool_map st))
                                   (PtrTree_set p (next_id st) (addr_to_id st))
                                   (PTree.set (next_id st) p (id_to_addr st))
                                   (Pos.succ (next_id st))) in
      trigger (SetState st')
    end
  end
.

Definition mpool_init_with_fallback_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr p_blk p_ofs); Vcomp (Vptr fb_blk fb_ofs)] =>
      mpool_init_with_fallback_spec (p_blk, Ptrofs.unsigned p_ofs) (fb_blk, Ptrofs.unsigned fb_ofs);;
      Ret (Vnull, args)
  | _ => triggerUB "Wrong args: mpool_init_fallback"
  end
.

Definition mpool_add_chunk_spec (p: positive * Z) (c:chunk A) (size:Z) : itree mpoolE unit :=
  st <- trigger GetState;;
  match (PtrTree_get p (addr_to_id st)) with
  | None => Ret tt
  | Some id =>
    match PTree.get id (mpool_map st) with
    | None => Ret tt
    | Some mp =>
      let mp' := (mkMpool (entry_size mp) (c::(chunk_list mp)) (entry_list mp) (fallback mp)) in
      let st' := (mkMpoolAbstState (PTree.set id mp' (mpool_map st))
                                   (addr_to_id st)
                                   (id_to_addr st)
                                   id) in
      trigger (SetState st')
    end
  end.

(* YH:problem *)
Fixpoint make_chunk {A} (a:A) (len: nat) :=
  match len with
  | O => []
  | S n => a::make_chunk a n
  end.

Definition mpool_add_chunk_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr p_blk p_ofs); Vcomp (Vptr begin_blk begin_ofs); args2] =>
    (* only chunk is well-align *)
    match args2 with
    | Vcomp (Vint chunk_size) =>
      mpool_add_chunk_spec (p_blk, Ptrofs.unsigned p_ofs) (make_chunk a (Z.abs_nat (Int.unsigned chunk_size))) (Int.unsigned chunk_size);;
      Ret (Vcomp Vtrue, args)
    | Vcomp (Vlong chunk_size) =>
      mpool_add_chunk_spec (p_blk, Ptrofs.unsigned p_ofs) (make_chunk a (Z.abs_nat (Int64.unsigned chunk_size))) (Int64.unsigned chunk_size);;
      Ret (Vcomp Vtrue, args)
    | _ => triggerUB "Wrong args: mpool_add_chunk"
    end
  | _ => triggerUB "Wrong args: mpool_add_chunk"
  end
.

Definition mpool_fini_spec (p: positive * Z) : itree mpoolE unit :=
  st <- trigger GetState;;
  match (PtrTree_get p (addr_to_id st)) with
  | None => Ret tt
  | Some i =>
    match PTree.get i (mpool_map st) with
    | None => Ret tt
    | Some mp =>
      let mpool_map' :=
          (match fallback mp with
           | Some i_fallback =>
             match PTree.get i_fallback (mpool_map st) with
             | Some mp_fallback =>
               (PTree.set i_fallback (mkMpool (entry_size mp_fallback)
                                              ((rev (chunk_list mp)) ++ (chunk_list mp_fallback))
                                              ((rev (entry_list mp)) ++ (entry_list mp_fallback))
                                              (fallback mp_fallback))
                          (mpool_map st))
             | None => (mpool_map st) (* Can't reachable *)
             end
           | None => (mpool_map st)
           end) in      
      let st' := (mkMpoolAbstState (PTree.remove i mpool_map')
                                   (PtrTree_remove p (addr_to_id st))
                                   (PTree.remove i (id_to_addr st))
                                   (next_id st)) in
      trigger (SetState st')
    end
  end.

Definition mpool_fini_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr p_blk p_ofs)] =>
      mpool_fini_spec (p_blk, Ptrofs.unsigned p_ofs);;
      Ret (Vnull, args)
  | _ => triggerUB "Wrong args: mpool_fini"
  end.

Definition mpool_alloc_no_fallback_spec {E} (p: positive * Z) : itree (E +' mpoolE) (option (list A)) :=
  st <- trigger GetState;;
  match (PtrTree_get p (addr_to_id st)) with
  | None => Ret None (* UB *)
  | Some i =>
    match PTree.get i (mpool_map st) with
    | None => Ret None (* UB *)
    | Some mp =>
      match (entry_list mp) with
      | ethd :: ettl =>
        let mp' := mkMpool (entry_size mp) (chunk_list mp) ettl (fallback mp) in
        let st' := (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) (id_to_addr st) i) in
        trigger (SetState st');; Ret (Some ethd)
      | [] =>
        match (chunk_list mp) with
        | [] => Ret None
        | chhd::chtl =>
          if ((Zlength chhd) <=? (entry_size mp))
          then
            let mp' := mkMpool (entry_size mp) chtl (entry_list mp) (fallback mp) in
            let st' := (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) (id_to_addr st) i) in
            trigger (SetState st');; Ret (Some chhd)
          else
            let new_chunk := (skipn (Z.abs_nat (entry_size mp)) chhd)::chtl in
            let mp' := mkMpool (entry_size mp) new_chunk (entry_list mp) (fallback mp) in
            let st' := (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) (id_to_addr st) i) in
            trigger (SetState st');; Ret (Some chhd)
        end
      end
    end
  end.

Definition mpool_alloc_spec_body (p: positive * Z) : itree ((callE (positive * Z) (option (list A))) +' mpoolE) (option (list A)) :=
  st <- trigger GetState;;
  match (PtrTree_get p (addr_to_id st)) with
  | None => Ret None
  | Some i =>
    match PTree.get i (mpool_map st) with
    | None => Ret None
    | Some mp =>
      v <-  mpool_alloc_no_fallback_spec p;;
        match v with
        | Some v' => Ret (Some v')
        | None =>
          match (fallback mp) with
          | None => Ret None
          | Some fallback_id =>
            st' <- trigger GetState;;
                match (PTree.get fallback_id (id_to_addr st')) with
                | None => Ret None
                | Some p =>
                  let (fb_b, fb_ofs) := p in
                  (* Ret None (* inf loop ... idk why *) *)
                  call (fb_b, fb_ofs)
                end
          end
        end
    end
  end.

Definition mpool_alloc_spec (p: positive * Z) : itree mpoolE (option (list A)) :=
  rec mpool_alloc_spec_body p.

Definition mpool_alloc_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr p_blk p_ofs)] =>
      v <- mpool_alloc_spec (p_blk, Ptrofs.unsigned p_ofs);;
      Ret (Vabs (Any.upcast v), args)
  | _ => triggerUB "Wrong args: mpool_alloc"
  end.

Definition mpool_free_spec (p: positive * Z) (ptr:list A) : itree mpoolE unit :=
  st <- trigger GetState;;
  match (PtrTree_get p (addr_to_id st)) with
  | None => Ret tt
  | Some i =>
    match PTree.get i (mpool_map st) with
    | None => Ret tt
    | Some mp =>
      let mp' := (mkMpool (entry_size mp) (chunk_list mp) (ptr::entry_list mp) (fallback mp)) in
      let st' := (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) (id_to_addr st) i) in
      trigger (SetState st')
    end
  end.

Definition mpool_free_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr p_blk p_ofs); Vcomp (Vptr ptr_blk ptr_ofs)] =>
      st <- trigger GetState;;
      match PtrTree_get (p_blk, Ptrofs.unsigned p_ofs) (addr_to_id st) with
      | None => triggerUB "Wrong args: mpool_free"
      | Some id =>
        match PTree.get id (mpool_map st) with
        | None => triggerUB "Wrong args: mpool_free"
        | Some mp =>
          v <- mpool_free_spec (p_blk, Ptrofs.unsigned p_ofs) (make_chunk a (Z.abs_nat (entry_size mp)));;
            Ret (Vnull, args)
        end
      end
  | _ => triggerUB "Wrong args: mpool_free"
  end.

Definition empty_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  Ret (Vnull, args).

Definition print_mpool_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  st <- trigger GetState;;
  match args with
  | [Vcomp (Vptr p_blk p_ofs)] =>
    match (PtrTree_get (p_blk, (Ptrofs.unsigned p_ofs)) (addr_to_id st)) with
    | None => Ret (Vnull, args)
    | Some id =>
      match (PTree.get id (mpool_map st)) with
      | None => Ret (Vnull, args) (* Can't reachable with wf state *)
      | Some mp =>
        let entry := (append "entry_size: " (Z_to_string (entry_size mp))) in
        triggerSyscall "hd" entry [Vnull];;
        let fix print_chunk l i :=
            match l with
            | [] => triggerSyscall "hd" "" [Vnull]
            | hd::tl =>
              triggerSyscall "hd" (append "  chunk " (Z_to_string i)) [Vnull];;
              triggerSyscall "hd" (append "    start " "ASDF") [Vnull];;
              triggerSyscall "hd" (append "    end " "ASDF") [Vnull];;
              triggerSyscall "hd" (append "    size " "ASDF") [Vnull];;
              print_chunk tl (i + 1)%Z
            end
        in
        print_chunk (chunk_list mp) 0;;
        let fix print_entry l i :=
            match l with
            | [] => triggerSyscall "hd" "" [Vnull]
            | hd::tl =>
              triggerSyscall "hd" (append "  entry " (Z_to_string i)) [Vnull];;
              triggerSyscall "hd" "ASDF" [Vnull];;
              print_chunk tl (i + 1)%Z
            end
        in
        print_entry (entry_list mp) 0;;
        let fallback := match fallback mp with
                        | Some p => append "fallback: " (Z_to_string (Zpos' p))
                        | None => "fallback: None"
                        end
        in
        triggerSyscall "hd" fallback [Vnull];;
        Ret (Vnull, args)
      end
    end
  | _ => triggerUB "Wrong args: print_mpool"
  end.

Definition funcs :=
  [
    ("MPOOL.mpool_init", mpool_init_call);
    ("MPOOL.mpool_init_from", mpool_init_from_call);
    ("MPOOL.mpool_init_with_fallback", mpool_init_with_fallback_call);
    ("MPOOL.mpool_add_chunk", mpool_add_chunk_call);
    ("MPOOL.mpool_fini", mpool_fini_call);
    ("MPOOL.mpool_alloc", mpool_alloc_call);
    ("MPOOL.mpool_free", mpool_free_call);
    ("MPOOL.mpool_init_locks", empty_call);
    ("MPOOL.mpool_enable_locks", empty_call);
    ("MPOOL.print_mpool", print_mpool_call)
  ]
.

Definition mpool_modsem : ModSem :=
  mk_ModSem
    (fun s => existsb (string_dec s) (List.map fst funcs))
    _
    (initial_state A)
    updateStateE
    updateState_handler
    (fun T (c: CallExternalE T) =>
       let '(CallExternal func_name args) := c in
       let fix find_func l :=
           match l with
           | (f, body)::tl =>
             if (string_dec func_name f)
             then body args
             else find_func tl
           | nil => triggerNB "Not mpool func"
           end
       in
       find_func funcs
    )
.

End HIGHSPECITREE.


(* Definition main := *)
(*     st1 <- mpool_init_spec (initial_state Z) 400 8;; *)
(*     st2 <- mpool_init_with_fallback_spec st1 200 400;; *)
(*     st3 <- mpool_init_from_spec st2 100 200;; *)
(*     res_st4 <- mpool_add_chunk_spec st3 100 [1;2;3] 3;; *)
(*     st4 <- Some (fst res_st4);; *)
(*     res_st5 <- mpool_add_chunk_spec st4 100 [4;5] 2;; *)
(*     st5 <- Some (fst res_st5);; *)
(*     res_st6 <- mpool_add_chunk_spec st5 400 [6;7] 2;; *)
(*     st6 <- Some (fst res_st6);; *)
(*     st7 <- mpool_fini_spec st6 100;; *)
(*     Some st6 *)
(*   . *)

(* Section HIGHSPEC. *)

(* Variable A: Type. *)
(* Variable st: MpoolAbstState A. *)

(* Definition mpool_init_spec (p entry_size:Z) := *)
(*   let i := next_id st in *)
(*   let mp := mkMpool entry_size [] [] None in *)
(*   Some (mkMpoolAbstState (PTree.set i mp (mpool_map st)) *)
(*                          (ZTree.set p i (addr_to_id st)) (Pos.succ i)). *)

(* Definition mpool_init_from_spec (p from:Z) := *)
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
(*     ).  *)

(* End HIGHSPEC. *)

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
  
(*   Definition main := *)
(*     st1 <- mpool_init_spec (initial_state Z) 400 8;; *)
(*     st2 <- mpool_init_with_fallback_spec st1 200 400;; *)
(*     st3 <- mpool_init_from_spec st2 100 200;; *)
(*     res_st4 <- mpool_add_chunk_spec st3 100 [1;2;3] 3;; *)
(*     st4 <- Some (fst res_st4);; *)
(*     res_st5 <- mpool_add_chunk_spec st4 100 [4;5] 2;; *)
(*     st5 <- Some (fst res_st5);; *)
(*     res_st6 <- mpool_add_chunk_spec st5 400 [6;7] 2;; *)
(*     st6 <- Some (fst res_st6);; *)
(*     st7 <- mpool_fini_spec st6 100;; *)
(*     Some st6 *)
(*   . *)

(*   Compute main. *)

(*   Fixpoint print_mpool_aux {A} (mpool_map: PTree.t (Mpool A)) (n: nat):= *)
(*     match n with *)
(*     | S n => append "Mpool %d" (print_mpool_aux mpool_map n) *)
(*     | O => "" *)
(*     end. *)

(*   Definition print_mpool {A} (mpool: option (MpoolAbstState A)) := *)
(*     match mpool with *)
(*     | None => "ERROR" *)
(*     | Some mpool => print_mpool_aux (mpool_map mpool) (Pos.to_nat (next_id mpool)) *)
(*     end. *)

(*   Compute (print_mpool main). *)
  
(* End TEST. *)

(* Section ALLOC2. *)

(* (* Definition fact_body (x : nat) : itree (callE nat nat +' E) nat := *) *)
(* (*  match x with *) *)
(* (*   | O => Ret 1%nat *) *)
(* (*   | S m => *) *)
(* (*     y <- call m ;;  (* Recursively compute [y := m!] *) *) *)
(* (*     Ret (x * y)%nat *) *)
(* (*   end. *) *)

(* Variable A: Type. *)
(* Hypothesis id_to_addr : positive -> Z. *)

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
      

(* End ALLOC2.                      *)

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
