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

Notation "'do' X <- A ;;; B" := (match A with Some X => B | None => triggerUB "None" end)
  (at level 200, X ident, A at level 100, B at level 200)
  : itree_monad_scope.

Notation "'do' X , Y <- A ;;; B" := (match A with Some (X, Y) => B | None => triggerUB "None" end)
  (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : itree_monad_scope.

Notation "'do' X , Y , Z <- A ;;; B" := (match A with Some (X, Y, Z) => B | None => triggerUB "None" end)
  (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : itree_monad_scope.

Notation " 'check' A ;;; B" := (if A then B else Ret None)
  (at level 200, A at level 100, B at level 200)
  : itree_monad_scope.

Local Open Scope itree_monad_scope.

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
  zt <- PTree.get (fst ptr) map;;
  ZTree.get (snd ptr) zt
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

(* Variable A: Type. *)
Definition A : Type := positive * Z.

Definition A_to_string (a: A): string :=
  "(" ++ (Z_to_string (Zpos' (fst a))) ++ ", " ++ (Z_to_string (snd a)) ++ ")"
.

Definition state := MpoolAbstState A.
Definition null: A := (xH, 0).
(* Variable a: A. (* neede when we make chunk *) *)

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

Definition mpool_init_from_spec (p: positive * Z) (from: positive * Z) :=
  st <- trigger GetState;;
  do from_id <- PtrTree_get from (addr_to_id st);;; (* UB *)
  do from_mp <- PTree.get from_id (mpool_map st);;; (* Must Some *)
  mpool_init_spec p (entry_size from_mp);;
  st' <- trigger GetState;;
  do p_id <- PtrTree_get p (addr_to_id st');;; (* Must Some *)
  let st'' := (mkMpoolAbstState (PTree.remove from_id (PTree.set p_id from_mp (mpool_map st')))
                                (PtrTree_remove from (addr_to_id st'))
                                (PTree.remove from_id (id_to_addr st'))
                                (next_id st')) in
  trigger (SetState st'');; Ret (Some tt)
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
  do fallback_id <- PtrTree_get fallback (addr_to_id st);;; (* UB *)
  do mp <- PTree.get fallback_id (mpool_map st);;; (* Must Some *)
  let mp' := (mkMpool (entry_size mp) [] [] (Some fallback_id)) in
  let st' := (mkMpoolAbstState (PTree.set (next_id st) mp' (mpool_map st))
                               (PtrTree_set p (next_id st) (addr_to_id st))
                               (PTree.set (next_id st) p (id_to_addr st))
                               (Pos.succ (next_id st))) in
  trigger (SetState st');; Ret tt
.

Definition mpool_init_with_fallback_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr p_blk p_ofs); Vcomp (Vptr fb_blk fb_ofs)] =>
      mpool_init_with_fallback_spec (p_blk, Ptrofs.unsigned p_ofs) (fb_blk, Ptrofs.unsigned fb_ofs);;
      Ret (Vnull, args)
  | _ => triggerUB "Wrong args: mpool_init_fallback"
  end
.

Definition mpool_add_chunk_spec (p: positive * Z) (c:chunk A) (size:Z) : itree mpoolE bool :=
  (* only chunk is well-align *)
  st <- trigger GetState;;
  do id <- PtrTree_get p (addr_to_id st);;; (* UB *)
  do mp <- PTree.get id (mpool_map st);;; (* Must Some *)
  let mp' := (mkMpool (entry_size mp) (c::(chunk_list mp)) (entry_list mp) (fallback mp)) in
  let st' := (mkMpoolAbstState (PTree.set id mp' (mpool_map st))
                               (addr_to_id st)
                               (id_to_addr st)
                               (next_id st)) in
  trigger (SetState st');; Ret true
.

(* YH:problem *)
Fixpoint make_chunk (a:A) (len: nat) :=
  match len with
  | O => []
  | S n => a::make_chunk (fst a, (snd a + 1)%Z) n
  end.

Definition mpool_add_chunk_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr p_blk p_ofs); Vcomp (Vptr begin_blk begin_ofs); args2] =>
    match args2 with
    | Vcomp (Vint chunk_size) =>
      mpool_add_chunk_spec (p_blk, Ptrofs.unsigned p_ofs) (make_chunk (begin_blk, Ptrofs.unsigned begin_ofs) (Z.abs_nat (Int.unsigned chunk_size))) (Int.unsigned chunk_size);;
      Ret (Vcomp Vtrue, args)
    | Vcomp (Vlong chunk_size) =>
      mpool_add_chunk_spec (p_blk, Ptrofs.unsigned p_ofs) (make_chunk (begin_blk, Ptrofs.unsigned begin_ofs) (Z.abs_nat (Int64.unsigned chunk_size))) (Int64.unsigned chunk_size);;
      Ret (Vcomp Vtrue, args)
    | _ => triggerUB "Wrong args: mpool_add_chunk"
    end
  | _ => triggerUB "Wrong args: mpool_add_chunk"
  end
.

Definition mpool_fini_spec (p: positive * Z) : itree mpoolE unit :=
  st <- trigger GetState;;
  do i <- PtrTree_get p (addr_to_id st);;; (* UB *)
  do mp <- PTree.get i (mpool_map st);;; (* Must Some *)
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
  trigger (SetState st');; Ret tt
.

Definition mpool_fini_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr p_blk p_ofs)] =>
      mpool_fini_spec (p_blk, Ptrofs.unsigned p_ofs);;
      Ret (Vnull, args)
  | _ => triggerUB "Wrong args: mpool_fini"
  end.

Definition mpool_alloc_no_fallback_spec (p: positive * Z) : itree mpoolE (option A) :=
  st <- trigger GetState;;
  do i <- PtrTree_get p (addr_to_id st);;; (* UB *)
  do mp <- PTree.get i (mpool_map st);;; (* Must Some *)
  match (entry_list mp) with
  | ethd :: ettl =>
    let mp' := mkMpool (entry_size mp) (chunk_list mp) ettl (fallback mp) in
    let st' := (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) (id_to_addr st) i) in
    trigger (SetState st');; Ret (Some (hd null ethd))
  | [] =>
    match (chunk_list mp) with
    | [] => Ret None
    | chhd::chtl =>
      if ((Zlength chhd) <=? (entry_size mp))
      then
        let mp' := mkMpool (entry_size mp) chtl (entry_list mp) (fallback mp) in
        let st' := (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) (id_to_addr st) i) in
        trigger (SetState st');; Ret (Some (hd null chhd))
      else
        let new_chunk := (skipn (Z.abs_nat (entry_size mp)) chhd)::chtl in
        let mp' := mkMpool (entry_size mp) new_chunk (entry_list mp) (fallback mp) in
        let st' := (mkMpoolAbstState (PTree.set i mp' (mpool_map st)) (addr_to_id st) (id_to_addr st) i) in
        trigger (SetState st');; Ret (Some (hd null chhd))
    end
  end
.

Definition mpool_alloc_spec (p: positive * Z) : itree mpoolE (option A) :=
  ITree.iter
  (fun p =>
     st <- trigger GetState;;
     do i <- PtrTree_get p (addr_to_id st);;; (* UB *)
     do mp <- PTree.get i (mpool_map st);;; (* Must Some *)
     v <-  mpool_alloc_no_fallback_spec p;;
     match v with
     | Some v' => Ret (inr (Some v'))
     | None =>
       match fallback mp with
       | Some fallback_id =>
         do p <- PTree.get fallback_id (id_to_addr st);;; (* Must Some *)
         ret (inl p)
       | _ => Ret (inr None)
       end
     end
  ) p.

Definition mpool_alloc_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr p_blk p_ofs)] =>
    v <- mpool_alloc_spec (p_blk, Ptrofs.unsigned p_ofs);;
    match v with
    | None => Ret (Vnull, args)
    | Some (b, ofs) => Ret (Vcomp (Vptr b (Ptrofs.repr ofs)), args)
    end
  | _ => triggerUB "Wrong args: mpool_alloc"
  end.

Definition mpool_alloc_contiguous_no_fallback_spec (p: positive * Z) (count align: Z)
  : itree mpoolE (option A) :=
  (* ignore align *)
  st <- trigger GetState;;
  do i <- PtrTree_get p (addr_to_id st);;; (* UB *)
  do mp <- PTree.get i (mpool_map st);;; (* Must Some *)
  ITree.iter
  (fun '(prev, acc) =>
     match prev with
     | [] => Ret (inr None)
     | chhd::chtl =>
       if (count * (entry_size mp) <=? (Zlength chhd))
       then
         if ((Zlength chhd) =? count * (entry_size mp))%Z
         then
           let mp' := mkMpool (entry_size mp) (acc ++ chtl) (entry_list mp) (fallback mp) in
           let st' := (mkMpoolAbstState (PTree.set i mp' (mpool_map st))
                                        (addr_to_id st) (id_to_addr st) i) in
           trigger (SetState st');; Ret (inr (Some (hd null chhd)))
         else
           let new_chunk := (skipn (Z.abs_nat ((entry_size mp) * count)) chhd)::chtl in
           let mp' := mkMpool (entry_size mp) (acc ++ new_chunk) (entry_list mp) (fallback mp) in
           let st' := (mkMpoolAbstState (PTree.set i mp' (mpool_map st))
                                        (addr_to_id st) (id_to_addr st) i) in
           trigger (SetState st');; Ret (inr (Some (hd null chhd)))
       else
         Ret (inl (chtl, acc ++ [chhd]))
     end
  ) (chunk_list mp, nil).

Definition mpool_alloc_contiguous_spec (p: positive * Z) (count align: Z)
  : itree mpoolE (option A) :=
  ITree.iter
  (fun p =>
     st <- trigger GetState;;
     do i <- PtrTree_get p (addr_to_id st);;; (* UB *)
     do mp <- PTree.get i (mpool_map st);;; (* Must Some *)
     v <-  mpool_alloc_contiguous_no_fallback_spec p count align;;
     match v with
     | Some v' => ret (inr (Some v'))
     | None =>
       match fallback mp with
       | Some fallback_id =>
         do p <- PTree.get fallback_id (id_to_addr st);;; (* Must Some *)
         ret (inl p)
       | _ => ret (inr None)
       end
     end
  ) p.

Definition mpool_alloc_contiguous_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr p_blk p_ofs); args2; args3] =>
    match args2, args3 with
    | Vcomp (Vint count), Vcomp (Vint align) =>
      v <- mpool_alloc_contiguous_spec (p_blk, Ptrofs.unsigned p_ofs)
        (Int.unsigned count) (Int.unsigned align);;
        match v with
        | None => Ret (Vnull, args)
        | Some (b, ofs) => Ret (Vcomp (Vptr b (Ptrofs.repr ofs)), args)
        end
    | Vcomp (Vint count), Vcomp (Vlong align) =>
      v <- mpool_alloc_contiguous_spec (p_blk, Ptrofs.unsigned p_ofs)
        (Int.unsigned count) (Int64.unsigned align);;
        match v with
        | None => Ret (Vnull, args)
        | Some (b, ofs) => Ret (Vcomp (Vptr b (Ptrofs.repr ofs)), args)
        end
    | Vcomp (Vlong count), Vcomp (Vint align) =>
      v <- mpool_alloc_contiguous_spec (p_blk, Ptrofs.unsigned p_ofs)
        (Int64.unsigned count) (Int.unsigned align);;
        match v with
        | None => Ret (Vnull, args)
        | Some (b, ofs) => Ret (Vcomp (Vptr b (Ptrofs.repr ofs)), args)
        end
    | Vcomp (Vlong count), Vcomp (Vlong align) =>
      v <- mpool_alloc_contiguous_spec (p_blk, Ptrofs.unsigned p_ofs)
        (Int64.unsigned count) (Int64.unsigned align);;
        match v with
        | None => Ret (Vnull, args)
        | Some (b, ofs) => Ret (Vcomp (Vptr b (Ptrofs.repr ofs)), args)
        end
    | _, _ => triggerUB "Wrong args: mpool_alloc_contiguous"
    end
  | _ => triggerUB "Wrong args: mpool_alloc_contiguous"
  end.

Definition mpool_free_spec (p ptr: positive * Z) : itree mpoolE unit :=
  st <- trigger GetState;;
  do i <- PtrTree_get p (addr_to_id st);;; (* UB *)
  do mp <- PTree.get i (mpool_map st);;; (* Must Some *)
  let ptr_list := (make_chunk (fst ptr, snd ptr) (Z.abs_nat (entry_size mp))) in
  let mp' := (mkMpool (entry_size mp) (chunk_list mp)
                      (ptr_list::entry_list mp) (fallback mp)) in
  let st' := (mkMpoolAbstState (PTree.set i mp' (mpool_map st))
                               (addr_to_id st) (id_to_addr st) i) in
  trigger (SetState st');; Ret tt.

Definition mpool_free_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr p_blk p_ofs); Vcomp (Vptr ptr_blk ptr_ofs)] =>
    v <- mpool_free_spec (p_blk, Ptrofs.unsigned p_ofs) (ptr_blk, Ptrofs.unsigned ptr_ofs);;
    Ret (Vnull, args)
  | _ => triggerUB "Wrong args: mpool_free"
  end.

Definition empty_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  Ret (Vnull, args).

Definition print_mpool_call (args: list Lang.val): itree mpoolE (Lang.val * list Lang.val) :=
  st <- trigger GetState;;
  match args with
  | [Vcomp (Vptr p_blk p_ofs)] =>
    triggerSyscall "hd" "------------print mpool------------" [Vnull];;
    triggerSyscall "hd" (append "mpool pointer: " (A_to_string (p_blk, (Ptrofs.unsigned p_ofs)))) [Vnull];;
    match (PtrTree_get (p_blk, (Ptrofs.unsigned p_ofs)) (addr_to_id st)) with
    | None => Ret (Vnull, args)
    | Some id =>
      match (PTree.get id (mpool_map st)) with
      | None => Ret (Vnull, args) (* Can't reachable with wf state *)
      | Some mp =>
        triggerSyscall "hd" (append "entry_size: " (Z_to_string (entry_size mp))) [Vnull];;
        let fix print_chunk l i :=
            match l with
            | [] => triggerSyscall "hd" "" [Vnull]
            | hd::tl =>
              triggerSyscall "hd" (append "  chunk " (Z_to_string i)) [Vnull];;
              triggerSyscall "hd" (append "    start " (A_to_string (List.hd null hd))) [Vnull];;
              triggerSyscall "hd" (append "    size " (Z_to_string (Zlength hd))) [Vnull];;
              print_chunk tl (i + 1)%Z
            end
        in
        print_chunk (chunk_list mp) 0;;
        let fix print_entry l i :=
            match l with
            | [] => triggerSyscall "hd" "" [Vnull]
            | hd::tl =>
              triggerSyscall "hd" (append "  entry " (Z_to_string i)) [Vnull];;
              triggerSyscall "hd" (append "    " (A_to_string (List.hd null hd))) [Vnull];;
              print_entry tl (i + 1)%Z
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
    ("MPOOL.mpool_alloc_contiguous", mpool_alloc_contiguous_call);
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

