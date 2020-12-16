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

Section ABSTSTATE.

Variable ptable: positive * Z.

Definition entry : Type := Z.

(* Constants for MM *)
Definition PAGE_BITS := 12.
Definition PAGE_SIZE := Z.shiftl 1 PAGE_BITS.
Definition MM_PTE_PER_PAGE := (PAGE_SIZE / 8)%Z.
  
(* The following are arch-independent page mapping modes. *)
Record MM_Mode :=
  mkMM_Mode {
      MM_MODE_R: bool; (* read *)
      MM_MODE_W: bool; (* write *)
      MM_MODE_X: bool; (* execute *)
      MM_MODE_D: bool; (* device *)
      MM_MODE_INVALID: bool;
      MM_MODE_UNOWNED: bool;
      MM_MODE_SHARED: bool;
    }.

Record MM_Flag :=
  mkMM_Flag {
      MM_FLAG_COMMIT: bool;
      MM_FLAG_UNMAP: bool;
      MM_FLAG_STAGE1: bool;
    }.

Inductive MM_Page_Table : Type :=
  mkMM_Page_Table {
      entires : list entry;
    }.

Record MMAbstState : Type :=
  mkMMAbstState {
      mm_page_table_map : PTree.t MM_Page_Table; (* id -> MM_PAGE_TABLE *)
      addr_to_id : PTree.t (ZTree.t positive); (* block -> offset -> id *)
      id_to_addr : PTree.t (positive * Z); (* id -> (block, offset *)
      next_id : positive; (* new MM id *)
      mm_stage1_locked: positive * Z;
      (* the currently locked stage-1 page table of the hypervisor. *)
    }.

Definition initial_state : MMAbstState :=
  mkMMAbstState (PTree.empty MM_Page_Table) (PTree.empty (ZTree.t positive)) (PTree.empty (positive * Z)) 1%positive ptable.

End ABSTSTATE.

Variable Z_to_string: Z -> string.
Extract Constant Z_to_string =>
"fun z -> (HexString.of_Z z)"
.

(* modify ArchMMHighSpec's *)
Section MM_FLAG_to_VALUE.
  
  Definition x_zshift_or_0 := fun (cond: bool) (x: Z) (shift : Z) => if cond then Z.shiftl x shift else 0.
  Definition zshift_or_0 := fun (cond: bool) (shift : Z) => x_zshift_or_0 cond 1 shift.

  Definition x_bit_no_exist :=
    fun (x : Z) (shift : Z) (attribute_values: Z) => (zeq 0 (Z.land (Z.shiftl x 63) attribute_values)).
  Definition x_gen_true_false := 
    fun (x : Z) (shift : Z) (attribute_values: Z) => if x_bit_no_exist x shift attribute_values then false else true.
  Definition bit_no_exist :=    
    fun (shift : Z) (attribute_values: Z) => x_bit_no_exist 1 shift attribute_values.
  Definition gen_true_false := 
    fun (shift : Z) (attribute_values: Z) => if bit_no_exist shift attribute_values then false else true.
  
  Definition MM_Mode_to_ATTR_VALUES (mode : MM_Mode) : Z :=
    match mode with
    |  mkMM_Mode r w x d invalid unowned shared
       => let r_to_z := zshift_or_0 r 0 in 
         let w_to_z := zshift_or_0 w 1 in
         let x_to_z := zshift_or_0 x 2 in
         let d_to_z := zshift_or_0 d 3 in
         let invalid_to_z :=  zshift_or_0 invalid 4 in 
         let unowned_to_z :=  zshift_or_0 unowned 5 in 
         let shared_to_z :=  zshift_or_0 shared 6 in 
         r_to_z + w_to_z + x_to_z + d_to_z + invalid_to_z + unowned_to_z + shared_to_z
    end.
  
  Definition ATTR_VALUES_to_MM_Mode (mm_mode_value : Z)
    : MM_Mode :=
    let r_of_z := gen_true_false 0 mm_mode_value in
    let w_of_z := gen_true_false 1 mm_mode_value in
    let x_of_z := gen_true_false 2 mm_mode_value in
    let d_of_z := gen_true_false 3 mm_mode_value in
    let invalid_of_z := gen_true_false 4 mm_mode_value in
    let unowned_of_z := gen_true_false 5 mm_mode_value in
    let shared_of_z := gen_true_false 6 mm_mode_value in
    mkMM_Mode r_of_z w_of_z x_of_z d_of_z invalid_of_z unowned_of_z shared_of_z.
  
  Definition MM_Flag_to_ATTR_VALUES (flags : MM_Flag) : Z :=
    match flags with
    |  mkMM_Flag commit unmap stage1
       => let commit_to_z := zshift_or_0 commit 0 in 
         let unmap_to_z := zshift_or_0 unmap 1 in
         let stage1_to_z := zshift_or_0 stage1 2 in
         commit_to_z + unmap_to_z + stage1_to_z
    end.
  
  Definition ATTR_VALUES_to_MM_Flag (flags_value : Z)
    : MM_Flag :=
    let commit_of_z := gen_true_false 0 flags_value in
    let unmap_of_z := gen_true_false 1 flags_value in
    let stage1_of_z := gen_true_false 2 flags_value in
    mkMM_Flag commit_of_z unmap_of_z stage1_of_z.

End MM_FLAG_to_VALUE.

Section HIGHSPECITREE.

(* Variable A: Type. *)
(* Definition A : Type := positive * Z. *)

(* Definition A_to_string (a: A): string := *)
(*   "(" ++ (Z_to_string (Zpos' (fst a))) ++ ", " ++ (Z_to_string (snd a)) ++ ")" *)
(* . *)
Definition eqb_ptr (x y: positive * Z) := andb (fst x =? fst y)%positive (snd x =? snd y)%Z.

Definition null: positive * Z := (xH, 0).

Inductive updateStateE: Type -> Type :=
| GetState : updateStateE MMAbstState
| SetState (st1:MMAbstState): updateStateE unit.

Definition updateState_handler {E: Type -> Type}
  : updateStateE ~> stateT MMAbstState (itree E) :=
  fun _ e st =>
    match e with
    | GetState => Ret (st, st)
    | SetState st' => Ret (st', tt)
    end.

Definition mmE := CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event.

(* TODO: move val2Z *)
Definition val2Z {E} `{Event -< E} (v: Lang.val) : itree E Z :=
  match v with
  | Vcomp (Vint i) => Ret (Int.unsigned i)
  | Vcomp (Vlong i) => Ret (Int64.unsigned i)
  | _ => triggerUB "Wrong args"
  end.

Definition mm_root_table_count_spec (flags: MM_Flag) : itree mmE Z :=
  let ext_call := if (MM_FLAG_STAGE1 flags)
                  then CallExternal "ARCHMM.arch_mm_stage1_root_table_count" []
                  else CallExternal "ARCHMM.arch_mm_stage2_root_table_count" []
  in
  '(ret, _) <- trigger ext_call;;
   v <- val2Z ret;;
   Ret v
.

Definition mm_alloc_page_tables_spec (count: Z) (ppool: positive * Z)
  : itree mmE (positive * Z) :=
  let mpool := (Vcomp (Vptr (fst ppool) (Ptrofs.repr (snd ppool)))) in
  let ext_call := if (count =? 1)%Z
                  then CallExternal "MM.mpool_alloc" [mpool]
                  else CallExternal "MM.mpool_alloc_contiguous"
                                    [mpool; Vcomp (Vint (Int.repr count))]
  in
  '(ret, _) <- trigger ext_call;;
   match ret with
   | Vcomp (Vptr b ofs) => Ret (b, Ptrofs.unsigned ofs)
   | _ => triggerUB ""
   end
.

Definition mm_max_level_spec (flags: MM_Flag) : itree mmE Z :=
  let ext_call := if (MM_FLAG_STAGE1 flags)
                  then CallExternal "ARCHMM.arch_mm_stage1_max_level" []
                  else CallExternal "ARCHMM.arch_mm_stage2_max_level" []
  in
  '(ret, _) <- trigger ext_call;;
   v <- val2Z ret;;
   Ret v
.

Definition mm_ptable_init_spec (t: positive * Z) (flags: MM_Flag) (ppool: positive * Z)
  : itree mmE bool :=
  root_table_count <- (mm_root_table_count_spec flags);;
  tables <- (mm_alloc_page_tables_spec root_table_count ppool);;
  if eqb_ptr tables null
  then Ret false
  else
  max_level <- mm_max_level_spec flags;;
  '(ret, _) <- trigger (CallExternal "ARCHMM.arch_mm_absent_pte"
                                    [Vcomp (Vint (Int.repr max_level))]);;
  absent_block <- val2Z ret;;
  ITree.iter
  (fun i =>
     if (i =? root_table_count)%Z
     then
       trigger (StoreE (fst t) (snd t) (Vptr (fst tables) (Ptrofs.repr (snd tables))));;
       Ret (inr true)
     else
       st <- trigger GetState;;
       let id := (next_id st) in
       let table_ptr := (fst tables, ((snd tables) + int_sz * i * MM_PTE_PER_PAGE)%Z) in
       let mm_page_table := mkMM_Page_Table (repeat absent_block (Z.to_nat MM_PTE_PER_PAGE)) in
       let st' := (mkMMAbstState (PTree.set id mm_page_table (mm_page_table_map st))
                                 (PtrTree_set table_ptr id (addr_to_id st))
                                 (PTree.set id table_ptr (id_to_addr st))
                                 (Pos.succ id)
                                 (mm_stage1_locked st)) in
       trigger (SetState st);;
       Ret (inl (i + 1)%Z)
  ) 0.
  
Definition mm_ptable_init_call (args: list Lang.val): itree mmE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr t_blk t_ofs); args2; Vcomp (Vptr ppool_blk ppool_ofs)] =>
    i <- val2Z args2;;
    b <- mm_ptable_init_spec (t_blk, Ptrofs.unsigned t_ofs)
                             (ATTR_VALUES_to_MM_Flag i)
                             (ppool_blk, Ptrofs.unsigned ppool_ofs);;
    Ret (bool_to_val b, args)
  | _ => triggerUB "Wrong args: mm_ptable_init"
  end.

(* DJ: How to call internally in recursive function? *)
Definition mm_page_table_from_pa (pa: Z) : itree (callE (Z * (Z * (positive * Z))) unit +' mmE) (positive * Z) :=
  '(t, _) <- trigger (CallExternal "ADDR.va_from_pa" [Vcomp (Vlong (Int64.repr pa))]);;
  '(ret, _) <- trigger (CallExternal "ADDR.ptr_from_va" [t]);;
  match ret with
  | Vcomp (Vptr block ofs) => Ret (block, Ptrofs.unsigned ofs)
  | _ => triggerUB "Wrong pointer: mm_page_table_from_pa"
  end
.

Definition mm_free_page_pte_body (args: (Z * (Z * (positive * Z))))
  : itree (callE (Z * (Z * (positive * Z))) unit +' mmE) unit :=
  let '(pte, (level, ppool)) := args in
  '(b, _) <- trigger (CallExternal "ARCHMM.arch_mm_pte_is_table"
                                  [Vcomp (Vint (Int.repr pte));
                                   Vcomp (Vint (Int.repr level))]);;
   if negb (Lang.is_true b)
   then
     Ret tt
   else
     '(ret, _) <- trigger (CallExternal "ARCHMM.arch_mm_table_from_pte"
                                       [Vcomp (Vint (Int.repr pte));
                                        Vcomp (Vint (Int.repr level))]);;
     t <- val2Z ret;;
     tables_ptr <- mm_page_table_from_pa t;;
     st <- trigger GetState;;
     do id <- PtrTree_get tables_ptr (addr_to_id st);;;
     do mm_page_table <- PTree.get id (mm_page_table_map st);;;
     _ <- ITree.iter
     (fun i =>
        if (i <? MM_PTE_PER_PAGE)%Z
        then
          call (pte, ((level - 1)%Z, ppool));;
          Ret (inl (i + 1)%Z)
        else
          Ret (inr tt)
     ) 0;;
     trigger (CallExternal "MPOOL.mpool_free"
                           [Vcomp (Vptr (fst ppool) (Ptrofs.repr (snd ppool)));
                            Vcomp (Vptr (fst tables_ptr) (Ptrofs.repr (snd tables_ptr)))]);;
     Ret tt
.

Definition mm_free_page_pte_spec (pte: Z) (level: Z) (ppool: positive * Z)
  : itree mmE unit :=
  rec mm_free_page_pte_body (pte, (level, ppool)).

Definition mm_ptable_fini_spec (t: positive * Z) (flags: MM_Flag) (ppool: positive * Z)
  : itree mmE unit :=
  tables <- trigger (LoadE (fst t) (snd t));;
  match tables with
  | Some (Vptr tables_blk tables_ofs) =>
    level <- mm_max_level_spec flags;;
    root_table_count <- mm_root_table_count_spec flags;;
    ITree.iter
    (fun i =>
       if (i =? root_table_count)%Z
       then
         trigger (CallExternal "MPOOL.mpool_add_chunk"
                               [Vcomp (Vptr (fst ppool) (Ptrofs.repr (snd ppool)));
                                Vcomp (Vptr tables_blk tables_ofs);
                                Vcomp (Vint (Int.repr ((8 * MM_PTE_PER_PAGE) * root_table_count)))]);;
                                (* need to modify sizeof(MM_PAGE_TABLE) *)
         Ret (inr tt)
       else
         st <- trigger GetState;;
         let table_ptr := (tables_blk, ((Ptrofs.unsigned tables_ofs) +
                                        int_sz * i * MM_PTE_PER_PAGE)%Z) in
         do id <- PtrTree_get table_ptr (addr_to_id st);;;
         do mm_page_table <- PTree.get id (mm_page_table_map st);;;
         _ <- ITree.iter
           (fun j =>
              if (j =? MM_PTE_PER_PAGE)%Z
              then
                let entry := nth_default 0 (entires mm_page_table) (Z.to_nat j) in
                (* DJ: use nth_default is correct? *)
                mm_free_page_pte_spec entry level ppool;;
                Ret (inl (j + 1)%Z)
              else
                Ret (inr tt)
           ) 0;;
         let st' := (mkMMAbstState (PTree.remove id (mm_page_table_map st))
                                   (PtrTree_remove table_ptr (addr_to_id st))
                                   (PTree.remove id (id_to_addr st))
                                   (next_id st)
                                   (mm_stage1_locked st)) in
         trigger (SetState st');;
         Ret (inl (i + 1)%Z)
   ) 0
  | _ => triggerUB ""
  end.
  
Definition mm_ptable_free_call (args: list Lang.val): itree mmE (Lang.val * list Lang.val) :=
  match args with
  | [Vcomp (Vptr t_blk t_ofs); args2; Vcomp (Vptr ppool_blk ppool_ofs)] =>
    i <- val2Z args2;;
    mm_ptable_fini_spec (t_blk, Ptrofs.unsigned t_ofs)
                        (ATTR_VALUES_to_MM_Flag i)
                        (ppool_blk, Ptrofs.unsigned ppool_ofs);;
    Ret (Vnull, args)
  | _ => triggerUB "Wrong args: mm_ptable_init"
  end.

Definition empty_call (args: list Lang.val): itree mmE (Lang.val * list Lang.val) :=
  Ret (Vnull, args).

Definition funcs :=
  [
    ("MM.mm_ptable_init", mm_ptable_init_call);
    ("MM.mm_ptable_free", mm_ptable_free_call)
  ]
.

Definition mpool_modsem : ModSem :=
  mk_ModSem
    (fun s => existsb (string_dec s) (List.map fst funcs))
    _
    (initial_state null)
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
           | nil => triggerNB "Not MM func"
           end
       in
       find_func funcs
    )
.

End HIGHSPECITREE.

