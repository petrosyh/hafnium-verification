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

Definition PtrTree_set {t} (ptr: positive * Z) (v: t) (map: PTree.t (ZTree.t t)) :=
  let zt := match PTree.get (fst ptr) map with
            | Some zt => zt
            | None => (ZTree.empty t)
            end in
  PTree.set (fst ptr) (ZTree.set (snd ptr) v zt) map
.

Definition PtrTree_get {t} (ptr: positive * Z) (map: PTree.t (ZTree.t t)) :=
  zt <- PTree.get (fst ptr) map;;
  ZTree.get (snd ptr) zt
.

Definition PtrTree_remove {t} (ptr: positive * Z) (map: PTree.t (ZTree.t t)) :=
  match PTree.get (fst ptr) map with
  | Some zt => PTree.set (fst ptr) (ZTree.remove (snd ptr) zt) map
  | None => map
  end
.

(* TODO: move this section *)
Section AUX.

Definition val2Z {E} `{Event -< E} (v: Lang.val) : itree E Z :=
  match v with
  | Vcomp (Vint i) => Ret (Int.unsigned i)
  | Vcomp (Vlong i) => Ret (Int64.unsigned i)
  | _ => triggerUB "Wrong args - not integer"
  end.

Definition Z2val (z: Z) := Vcomp (Vlong (Int64.repr z)).

Definition val2ptr {E} `{Event -< E} (v: Lang.val) : itree E (positive * Z) :=
  match v with
  | Vcomp (Vptr b ofs) => Ret (b, Ptrofs.unsigned ofs)
  | _ => triggerUB "Wrong args - not ptr"
  end.

Definition ptr2val (ptr: positive * Z) := Vcomp (Vptr (fst ptr) (Ptrofs.repr (snd ptr))).

End AUX.

Section ABSTSTATE.

Variable ptable: positive * Z.

Definition entry : Type := Z.

(* Constants for MM *)
Definition PAGE_BITS := 12.
Definition PAGE_LEVEL_BITS := 9.
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
      entries_map : PTree.t (ZTree.t entry); (* direct access to entry *)
      mm_stage2_invalidate: bool
    }.

Definition initial_state : MMAbstState :=
  mkMMAbstState (PTree.empty MM_Page_Table) (PTree.empty (ZTree.t positive)) (PTree.empty (positive * Z)) 1%positive ptable (PTree.empty (ZTree.t entry)) false.

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

Notation mmE := (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).

Definition mm_root_table_count_spec (flags: MM_Flag) : itree mmE Z :=
  let ext_call := if (MM_FLAG_STAGE1 flags)
                  then CallExternal "ARCHMM.arch_mm_stage1_root_table_count" []
                  else CallExternal "ARCHMM.arch_mm_stage2_root_table_count" []
  in
  '(ret, _) <- trigger ext_call;;
   v <- val2Z ret;;
   Ret v
.

Definition mm_invalidate_tlb_spec (a_begin a_end: Z) (flags: MM_Flag) : itree mmE unit :=
  let begin_call := if (MM_FLAG_STAGE1 flags)
                    then CallExternal "ADDR.va_init" [Z2val a_begin]
                    else CallExternal "ADDR.ipa_init" [Z2val a_begin]
  in
  let end_call := if (MM_FLAG_STAGE1 flags)
                    then CallExternal "ADDR.va_init" [Z2val a_end]
                    else CallExternal "ADDR.ipa_init" [Z2val a_end]
  in
  '(vbegin, _) <- trigger begin_call;;
  '(vend, _) <- trigger end_call;;
  let ext_call := if (MM_FLAG_STAGE1 flags)
                  then CallExternal "ARCHMM.arch_mm_stage1_root_table_count" [vbegin; vend]
                  else CallExternal "ARCHMM.arch_mm_stage2_root_table_count" [vbegin; vend]
  in
  '(ret, _) <- trigger ext_call;;
   Ret tt
.

Definition mm_entry_size_spec (level: Z) : itree mmE Z :=
  Ret (Z.shiftl 1 (PAGE_BITS + (level * PAGE_LEVEL_BITS))%Z).

Definition mm_start_of_next_block_spec (addr block_size: Z) : itree mmE Z :=
  Ret (Z.land (addr + block_size) (Z.lnot (block_size - 1)))%Z.

(* Definition mm_pa_start_of_next_block (pa block_size: Z) : itree mmE unit := *)
(*   let pa_init_call1 := CallExternal "ADDR.pa_addr" [Z2val pa] in *)
(*   '(pa_init, _) <- trigger pa_init_call1;; *)
(*   let pa' := (pa_init + block_size)%Z in *)
(*   let pa_init_call2 := CallExternal "ADDR.pa_init" [Z2val pa'] in *)
(*   '(ret, _) <- trigger pa_init_call2;; *)
(*   v <- val2Z ret;; *)
(*   Ret v. *)
  
  (* (*  *)
  (* /** *)
  (*  * For a given address, calculates the maximum (plus one) address that can be *)
  (*  * represented by the same table at the given level. *)
  (*  */ *)
  (* static ptable_addr_t mm_level_end(ptable_addr_t addr, uint8_t level) *)
  (* { *)
  (*         size_t offset = PAGE_BITS + (level + 1) * PAGE_LEVEL_BITS; *)
   
  (*         return ((addr >> offset) + 1) << offset; *)
  (* } *)
  (* *) *)

Definition mm_level_end_spec (addr level: Z) : itree mmE Z :=
  let offset := (PAGE_BITS + (level + 1) * PAGE_LEVEL_BITS)%Z in
  let ret := Z.shiftl ((Z.shiftr addr offset) + 1)%Z offset in
  Ret ret.

Definition mm_index_spec (addr level: Z) : itree mmE Z :=
  let v := (Z.shiftl addr (Z.add PAGE_BITS (Z.mul level PAGE_LEVEL_BITS))) in
  Ret (Z.land v (Z.sub (Z.shiftl 1 PAGE_LEVEL_BITS) 1)).

Definition mm_alloc_page_tables_spec (count: Z) (ppool: positive * Z)
  : itree mmE (positive * Z) :=
  let mpool := (ptr2val ppool) in
  let ext_call := if (count =? 1)%Z
                  then CallExternal "MM.mpool_alloc" [mpool]
                  else CallExternal "MM.mpool_alloc_contiguous"
                                    [mpool; Z2val count]
  in
  '(ret, _) <- trigger ext_call;;
   val2ptr ret
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

Definition mm_map_level_spec (begin end pa attrs level: Z) (table ppool: positive * Z) (flags: MM_Flag) : itree mmE bool :=
  

  (*
  /**
   * Updates the page table at the given level to map the given address range to a
   * physical range using the provided (architecture-specific) attributes. Or if
   * MM_FLAG_UNMAP is set, unmap the given range instead.
   *
   * This function calls itself recursively if it needs to update additional
   * levels, but the recursion is bound by the maximum number of levels in a page
   * table.
   */
  static bool mm_map_level(ptable_addr_t begin, ptable_addr_t end, paddr_t pa,
          		 uint64_t attrs, struct mm_page_table *table,
          		 uint8_t level, int flags, struct mpool *ppool)
  {
          pte_t *pte = &table->entries[mm_index(begin, level)];
          ptable_addr_t level_end = mm_level_end(begin, level);
          size_t entry_size = mm_entry_size(level);
          bool commit = flags & MM_FLAG_COMMIT;
          bool unmap = flags & MM_FLAG_UNMAP;
   
          /* Cap end so that we don't go over the current level max. */
          if (end > level_end) {
          	end = level_end;
          }
   
          /* Fill each entry in the table. */
          while (begin < end) {
          	if (unmap ? !arch_mm_pte_is_present( *pte, level)
          		  : arch_mm_pte_is_block( *pte, level) &&
          			    arch_mm_pte_attrs( *pte, level) == attrs) {
          		/*
          		 * If the entry is already mapped with the right
          		 * attributes, or already absent in the case of
          		 * unmapping, no need to do anything; carry on to the
          		 * next entry.
          		 */
          	} else if ((end - begin) >= entry_size &&
          		   (unmap || arch_mm_is_block_allowed(level)) &&
          		   (begin & (entry_size - 1)) == 0) {
          		/*
          		 * If the entire entry is within the region we want to
          		 * map, map/unmap the whole entry.
          		 */
          		if (commit) {
          			pte_t new_pte =
          				unmap ? arch_mm_absent_pte(level)
          				      : arch_mm_block_pte(level, pa,
          							  attrs);
          			mm_replace_entry(begin, pte, new_pte, level,
          					 flags, ppool);
          		}
          	} else {
          		/*
          		 * If the entry is already a subtable get it; otherwise
          		 * replace it with an equivalent subtable and get that.
          		 */
          		struct mm_page_table *nt = mm_populate_table_pte(
          			begin, pte, level, flags, ppool);
          		if (nt == NULL) {
          			return false;
          		}
   
          		/*
          		 * Recurse to map/unmap the appropriate entries within
          		 * the subtable.
          		 */
          		if (!mm_map_level(begin, end, pa, attrs, nt, level - 1,
          				  flags, ppool)) {
          			return false;
          		}
          	}
   
          	begin = mm_start_of_next_block(begin, entry_size);
          	pa = mm_pa_start_of_next_block(pa, entry_size);
          	pte++;
          }
   
          return true;
  }
   *)

  Definition mm_map_level (a_begin a_end pa attrs table level flags ppool n: var) 
             (pte level_end entry_size commit unmap new_pte nt cond: var) :=
    (* XXX: How can we handle this aliasing? *)
    pte #= (table #@ (Call "MM.mm_index" [CBV a_begin; CBV level])) #;
        level_end #= (Call "MM.mm_level_end" [CBV a_begin; CBV level]) #;
        entry_size #= (Call "MM.mm_entry_size" [CBV level]) #;
        commit #= (flags #& MM_FLAG_COMMIT) #;
        unmap #= (flags #& MM_FLAG_UNMAP) #;
        (#if (level_end < a_end)
          then a_end #= level_end
          else Skip) #;
        #while (a_begin < a_end)
        do (
            (* XXX: Need to check the precedence of each operator - e.g. == ? && ? *)
            (* move this condition due to our syntax *)
            (#if (unmap)
              then cond #= (#! (Call "ARCHMM.arch_mm_pte_is_present" [CBR pte; CBV level]))
              else cond #= ((Call "ARCHMM.arch_mm_pte_is_block" [CBR pte; CBV level])
                              #&& ((Call "ARCHMM.arch_mm_pte_attrs" [CBR pte; CBV level]) == attrs)))
              #;
                            
            (#if (cond)
              then Skip
              else (#if ((entry_size <= (a_end - a_begin))
                           #&& (unmap #|| (Call "ARCHMM.arch_mm_is_block_allowed" [CBV level]))
                           #&& (a_begin #& (entry_size - one) == zero))
                     then (#if (commit)
                            then (#if (unmap)
                                   then new_pte #= (Call "ARCHMM.arch_mm_absent_pte" [CBV level])
                                   else new_pte #= (Call "ARCHMM.arch_mm_block_pte" [CBV level; CBV pa; CBV attrs]))
                                   #;
                                   (Call "MM.mm_replace_entry" [CBV a_begin; CBR pte; CBR new_pte; CBV level;
                                                               CBV flags; CBR ppool])
                            else Skip)
                     else nt #= (Call "MM.mm_populate_table_pte" [CBV a_begin; CBR pte; CBV level; CBV flags; CBR ppool]) #;
                             (#if #! (nt)
                               then Return Vfalse
                               else Skip) #;
                             (#if (#! (Call "MM.mm_map_level" [CBV a_begin; CBV a_end; CBV pa; CBV attrs; CBR nt;
                                                              CBV (level - one); CBV flags; CBR ppool]))
                               then Return Vfalse
                               else Skip) #;
                             a_begin #= (Call "MM.mm_start_of_next_block" [CBV a_begin; CBV entry_size]) #;
                             pa #= (Call "MM.mm_pa_start_of_next_block" [CBV pa; CBV entry_size]) #;
                             pte #= (Cast ((Cast pte tint) + one) tptr)))
          ) #;
            Return Vtrue.


Fixpoint setEntries (ptr: positive * Z) (entries: list entry)
         (entries_map: PTree.t (ZTree.t entry))
  : PTree.t (ZTree.t entry) :=
  match entries with
  | [] => entries_map
  | hd::tl => setEntries (fst ptr, ((snd ptr) + int_sz)%Z) tl
                        (PtrTree_set ptr hd entries_map)
  end.

Fixpoint removeEntries (ptr: positive * Z) (n: nat) (entries_map: PTree.t (ZTree.t entry))
  : PTree.t (ZTree.t entry) :=
  match n with
  | O => entries_map
  | S n' => removeEntries (fst ptr, ((snd ptr) + 1)%Z) n' (PtrTree_remove ptr entries_map)
  end.

Fixpoint mkEntries (new_pte inc: entry) (n: nat) : list entry :=
  match n with
  | O => nil
  | S n' => new_pte::(mkEntries (new_pte + inc)%Z inc n')
  end.

Definition mm_ptable_init_spec (t: positive * Z) (flags: MM_Flag) (ppool: positive * Z)
  : itree mmE bool :=
  root_table_count <- (mm_root_table_count_spec flags);;
  tables <- (mm_alloc_page_tables_spec root_table_count ppool);;
  if eqb_ptr tables null
  then Ret false
  else
  max_level <- mm_max_level_spec flags;;
  '(ret, _) <- trigger (CallExternal "ARCHMM.arch_mm_absent_pte"
                                    [Z2val  max_level]);;
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
       let entries := repeat absent_block (Z.to_nat MM_PTE_PER_PAGE) in
       let mm_page_table := mkMM_Page_Table entries in
       let entries_map' := setEntries table_ptr entries (entries_map st) in
       let st' := (mkMMAbstState (PTree.set id mm_page_table (mm_page_table_map st))
                                 (PtrTree_set table_ptr id (addr_to_id st))
                                 (PTree.set id table_ptr (id_to_addr st))
                                 (Pos.succ id)
                                 (mm_stage1_locked st)
                                 entries_map'
                                 (mm_stage2_invalidate st)) in
       trigger (SetState st');;
       Ret (inl (i + 1)%Z)
  ) 0.
  
Definition mm_ptable_init_call (args: list Lang.val): itree mmE (Lang.val * list Lang.val) :=
  match args with
  | [arg1; arg2; arg3] =>
    t <- val2ptr arg1;;
    flag <- val2Z arg2;;
    ppool <- val2ptr arg3;;
    b <- mm_ptable_init_spec t (ATTR_VALUES_to_MM_Flag flag) ppool;;
    Ret (bool_to_val b, args)
  | _ => triggerUB "Wrong args: mm_ptable_init"
  end.

Set Printing Universes.

(* TODO: need to solve universe inconsistency *)
(* Definition mm_page_table_from_pa {E} `{CallExternalE -< E} `{Event -< E} (pa: Z) *)
Definition mm_page_table_from_pa {E} (pa: Z)
  : itree (E +' mmE) (positive * Z) :=
  '(t, _) <- trigger (CallExternal "ADDR.va_from_pa" [Z2val pa]);;
  '(ret, _) <- trigger (CallExternal "ADDR.ptr_from_va" [t]);;
  val2ptr ret
. 

Definition mm_page_table_from_pa2 (pa: Z)
  : itree mmE (positive * Z) :=
  '(t, _) <- trigger (CallExternal "ADDR.va_from_pa" [Z2val pa]);;
  '(ret, _) <- trigger (CallExternal "ADDR.ptr_from_va" [t]);;
  val2ptr ret
.

Definition mm_free_page_pte_body (args: (Z * (Z * (positive * Z))))
  : itree (callE (Z * (Z * (positive * Z))) unit +' mmE) unit :=
  let '(pte, (level, ppool)) := args in
  '(b, _) <- trigger (CallExternal "ARCHMM.arch_mm_pte_is_table"
                                  [Z2val pte; Z2val level]);;
   if negb (Lang.is_true b)
   then
     Ret tt
   else
     '(ret, _) <- trigger (CallExternal "ARCHMM.arch_mm_table_from_pte"
                                        [Z2val pte; Z2val level]);;
     t <- val2Z ret;;
     tables_ptr <- mm_page_table_from_pa t;;
     st <- trigger GetState;;
     do id <- PtrTree_get tables_ptr (addr_to_id st);;;
     do mm_page_table <- PTree.get id (mm_page_table_map st);;;
     ITree.iter
     (fun i =>
        if (i <? MM_PTE_PER_PAGE)%Z
        then
          call (pte, ((level - 1)%Z, ppool));;
          Ret (inl (i + 1)%Z)
        else
          Ret (inr tt)
     ) 0;;
     trigger (CallExternal "MPOOL.mpool_free" [ptr2val ppool; ptr2val tables_ptr]);;
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
                               [ptr2val ppool;
                                Vcomp (Vptr tables_blk tables_ofs);
                                Z2val ((8 * MM_PTE_PER_PAGE) * root_table_count)]);;
                                (* need to modify sizeof(MM_PAGE_TABLE) *)
         Ret (inr tt)
       else
         st <- trigger GetState;;
         let table_ptr := (tables_blk, ((Ptrofs.unsigned tables_ofs) +
                                        int_sz * i * MM_PTE_PER_PAGE)%Z) in
         do id <- PtrTree_get table_ptr (addr_to_id st);;;
         do mm_page_table <- PTree.get id (mm_page_table_map st);;;
         ITree.iter
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
         let entries_map' := (removeEntries table_ptr (Z.to_nat MM_PTE_PER_PAGE)
                                            (entries_map st)) in
         let st' := (mkMMAbstState (PTree.remove id (mm_page_table_map st))
                                   (PtrTree_remove table_ptr (addr_to_id st))
                                   (PTree.remove id (id_to_addr st))
                                   (next_id st)
                                   (mm_stage1_locked st)
                                   entries_map'
                                   (mm_stage2_invalidate st)) in
         trigger (SetState st');;
         Ret (inl (i + 1)%Z)
   ) 0
  | _ => triggerUB ""
  end.
  
Definition mm_ptable_fini_call (args: list Lang.val): itree mmE (Lang.val * list Lang.val) :=
  match args with
  | [arg1; arg2; arg3] =>
    t <- val2ptr arg1;;
    flag <- val2Z arg2;;
    ppool <- val2ptr arg3;;
    mm_ptable_fini_spec t (ATTR_VALUES_to_MM_Flag flag) ppool;;
    Ret (Vnull, args)
  | _ => triggerUB "Wrong args: mm_ptable_init"
  end.

Definition mm_entry_size (level: Z) : itree mmE Z :=
  Ret (Z.shiftl 1 (PAGE_BITS + level * PAGE_LEVEL_BITS)).

Definition mm_populate_table_pte_spec (begin: Z) (pte: positive * Z) (level: Z) (flag: MM_Flag) (ppool: positive * Z)
  : itree mmE (positive * Z) :=
  (* TODO: load pte using abstract state not memory *)
  st <- trigger GetState;;
  do v <- PtrTree_get pte (entries_map st);;;
  let level_below := (level - 1)%Z in
  '(t, _) <- trigger (CallExternal "ARCHMM.arch_mm_pte_is_table"
                                   [Z2val v; Z2val level]);;
  if (Lang.is_true t)
  then
    '(t, _) <- trigger (CallExternal "ARCHMM.arch_mm_table_from_pte"
                                     [Z2val v; Z2val level]);;
    t <- val2Z t;;
    (* use origin func when solve universe inconsistency in mm_page_table_from_pa *)
    ret <- mm_page_table_from_pa2 t;;
    Ret ret
  else
    ntable <- mm_alloc_page_tables_spec 1%Z ppool;;
    if (eqb_ptr ntable null)
    then
      (* dlog_error("Failed to allocate memory for page table\n"); *)
      Ret null
    else
      '(t, _) <- trigger (CallExternal "ARCHMM.arch_mm_pte_is_block"
                                       [Z2val v; Z2val level]);;
       '(inc, new_pte) <-
         (if (Lang.is_true t)
          then
            inc <- mm_entry_size level_below;;
            '(pa, _) <- trigger (CallExternal "ARCHMM.arch_mm_block_from_pte"
                                              [Z2val v; Z2val level]);;
            '(attrs, _) <- trigger (CallExternal "ARCHMM.arch_mm_block_from_pte"
                                                 [Z2val v; Z2val level]);;
            '(ret, _) <- trigger (CallExternal "ARCHMM.arch_mm_block_pte"
                                               [Z2val level_below; pa; attrs]);;
            new_pte <- val2Z ret;;
            Ret (inc, new_pte)
          else
            let inc := 0 in
            '(ret, _) <- trigger (CallExternal "ARCHMM.arch_mm_absent_pte"
                                              [Z2val level_below]);;
             new_pte <- val2Z ret;;
             Ret (inc, new_pte)
         );;
         let id := (next_id st) in
         let entries := mkEntries new_pte inc (Z.to_nat MM_PTE_PER_PAGE) in
         let mm_page_table := mkMM_Page_Table entries in
         let entries_map' := setEntries ntable entries (entries_map st) in
         let st' := (mkMMAbstState (PTree.set id mm_page_table (mm_page_table_map st))
                                   (PtrTree_set ntable id (addr_to_id st))
                                   (PTree.set id ntable (id_to_addr st))
                                   (Pos.succ id)
                                   (mm_stage1_locked st)
                                   entries_map'
                                   (mm_stage2_invalidate st)) in
         trigger (SetState st');;
         (* atomic_thread_fence(memory_order_release); *)
         '(pa, _) <- trigger (CallExternal "ADDR.pa_init" []);;
         '(t, _) <- trigger (CallExternal "ARCHMM.arch_mm_table_pte"
                                         [Z2val level; pa]);;
         new_pte <- val2Z t;;
         (* mm_replace_entry begin pte new_pte level flag ppool;; *)
         Ret ntable
.

Definition empty_call (args: list Lang.val): itree mmE (Lang.val * list Lang.val) :=
  Ret (Vnull, args).

Definition mm_vm_enable_invalidation_call (args: list Lang.val)
  : itree mmE (Lang.val * list Lang.val) :=
  st <- trigger GetState;;
  let st' := (mkMMAbstState (mm_page_table_map st) (addr_to_id st) (id_to_addr st)
                            (next_id st) (mm_stage1_locked st) (entries_map st) true) in
  trigger (SetState st');;
  Ret (Vnull, args)
.

Definition funcs :=
  [
    ("MM.mm_vm_enable_invalidation", mm_vm_enable_invalidation_call);
    ("MM.mm_ptable_init", mm_ptable_init_call);
    ("MM.mm_ptable_fini", mm_ptable_fini_call)
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

