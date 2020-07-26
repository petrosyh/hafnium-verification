(*
 * Copyright 2020 Jieung Kim (jieungkim@google.com)
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
     Data.List.

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
Require Import Coqlib sflib Coq.Arith.Peano_dec.
  

(* From HafniumCore *)
Require Import TestAux.
Require Import Lang.
Require Import Types.
Require Import MpoolConcur.
Require Import ArchMM.
Require Import Lock.

(* This is to define abstract types *)
Require Import IntMap.Map.


Import LangNotations.


Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Local Open Scope N_scope.


Section NOTATIONTEST.
  Local Close Scope itree_scope.
  Local Open Scope monad_scope.
  From ExtLib Require Import OptionMonad.
  Print Instances Monad.
  Print Instances PMonad.
  Variable oa: option nat.
  Fail Check (a <- oa ;; a).
  Local Existing Instance Monad_option | 100.
  Local Existing Instance Monad_option | 0.
  Notation "x ?? c1 !! c2" := (@pbind _ _ _ _ _ c1 (fun x => c2))
                                (at level 61, c1 at next level, right associativity).
  Fail Check ((a ?? oa !! a): option nat).
  Notation "x <- c1 ;; c2" := (@pbind _ (PMonad_Monad Monad_option) _ _ _ c1 (fun x => c2))
                                (at level 61, c1 at next level, right associativity).
  Check ((a <- oa ;; Some a): option nat).
End NOTATIONTEST.

Notation "x <- c1 ;; c2" := (@pbind _ (PMonad_Monad Monad_option) _ _ _ c1 (fun x => c2))
                              (at level 61, c1 at next level, right associativity).
Require Import Any.




Module DummyAbsData.
  
  Inductive PTE_TY :=
  | PTENONE
  | PTE (owner: option N) (paddr : N) (level : N) (vaddr: option N).
  Instance PTE_TY_Showable: Showable PTE_TY := { show := fun x => match x with
                                                                  | PTENONE => "PTENONE" |
                                                                  PTE owner paddr level vaddr => "PTE" 
                                                                  end }.

  Record pt_entry: Type := mkPTE {value: list PTE_TY}.

  Definition pt_manager : Type := N-> option pt_entry.
  Definition inital_pt_manager: pt_manager := fun _ => None.
  Definition pt_update (m: pt_manager) (k0: N) (v: option pt_entry): pt_manager :=
    fun k1 => if rel_dec k0 k1 then v else m k1
  .

End DummyAbsData.

Module HighSpecDummyTest.

  Include DummyAbsData.
  
  Fixpoint pte_init_iter (base_addr: N) (level : N) (esize : N) (length : nat): list PTE_TY :=
    match length with
    | O => nil
    | S O => (PTE None base_addr level None)::nil
    | S n =>
      let prev := pte_init_iter base_addr level esize n in
      let len := List.length prev in 
      prev ++ (PTE None (base_addr + (esize * (N.of_nat len))) level None)::nil
    end.

  (* initialization of the pte entry *)
  Definition pte_init (vs : list val@{expr.u1}): (val@{expr.u2} * list val@{expr.u3}) :=
    let retv := match vs with
                | [(Vnat base_addr) ; (Vnat level) ; (Vnat esize) ;(Vnat len)] =>
                  unwrap (let new_ptes := pte_init_iter base_addr level esize (N.to_nat len) in
                          Some (Vabs (upcast new_ptes))
                         ) Vnodef
                | _ => Vnodef
                end
    in (retv, nil).

  Definition main res : stmt :=
    (DebugHigh "[high-model] Calling" Vnull) #;
    res #= (CoqCode [CBV (Vnat 4000) ; CBV (Vnat 1) ; CBV (Vnat 4) ; CBV (Vnat 4)] pte_init) #;
    DebugHigh "[high-model] Calling" res #;
    DebugHigh "[high-model] Call End" res.
    (* Put "high level test end:" res. *)

  Definition mainF: function.
      mk_function_tac main ([]: list var) (["res"] : list var).
  Defined.
  
  Definition program: program :=
    [
      ("main", mainF)
    ].
  
  Definition modsems: list ModSem := [program_to_ModSem program]. 
   
End HighSpecDummyTest.

Module AbsData.

  (* MPOOL_DEFINITION *)

  Definition ident := N.

  Instance RelDec_ident: RelDec (@eq ident) :=
    { rel_dec := fun n0 n1 => if (N.eqb n0 n1) then true else false}.

  (* mpool *)

  Record mpool: Type :=
    mkMPOOL {
        chunk_addr: option N;
        chunk_limit: N;
        fallback: option ident; (* mpoolid *)
      }
  .
  

  Definition GMPOOL := (Map mpool).
    
  Definition mp_manager: Type := ident -> option GMPOOL.
  Definition inital_mp_manager: mp_manager := fun _ => None.
  Definition mp_update (m: mp_manager) (k0: ident) (v: option GMPOOL): mp_manager :=
    fun k1 => if rel_dec k0 k1 then v else m k1
  .



  (* PTE Definition *)
  (* 
  /* The following are arch-independent page mapping modes. */
  #define MM_MODE_R UINT32_C(0x0001) /* read */
  #define MM_MODE_W UINT32_C(0x0002) /* write */
  #defi   ne MM_MODE_X UINT32_C(0x0004) /* execute */
  #define    MM_MODE_D UINT32_C(0x0008) /* device */
   *)
  
  (* The following are arch-independent page mapping modes. *)
  Inductive ModeFlag :=
  | MM_MODE_UNDEF (* nothing *)
  | MM_MODE_R (* read *)
  | MM_MODE_W (* write *)
  | MM_MODE_X (* execute *)
  | MM_MODE_D (* device *)
  .
  
  (*
/*
 * Memory in stage-1 is either valid (present) or invalid (absent).
 *
 * Memory in stage-2 has more states to track sharing, borrowing and giving of
 * memory. The states are made up of three parts:
 *
 *  1. V = valid/invalid    : Whether the memory is part of the VM's address
 *                            space. A fault will be generated if accessed when
 *                            invalid.
 *  2. O = owned/unowned    : Whether the memory is owned by the VM.
 *  3. X = exclusive/shared : Whether access is exclusive to the VM or shared
 *                            with at most one other.
 *
 * These parts compose to form the following state:
 *
 *  -  V  O  X : Owner of memory with exclusive access.
 *  -  V  O !X : Owner of memory with access shared with at most one other VM.
 *  -  V !O  X : Borrower of memory with exclusive access.
 *  -  V !O !X : Borrower of memory where access is shared with the owner.
 *  - !V  O  X : Owner of memory lent to a VM that has exclusive access.
 *
 *  - !V  O !X : Unused. Owner of shared memory always has access.
 *  - !V !O  X : Unused. Next entry is used for invalid memory.
 *
 *  - !V !O !X : Invalid memory. Memory is unrelated to the VM.
 *
 *  Modes are selected so that owner of exclusive memory is the default.
 */
#define MM_MODE_INVALID UINT32_C(0x0010)
#define MM_MODE_UNOWNED UINT32_C(0x0020)
#define MM_MODE_SHARED  UINT32_C(0x0040)
   *)
  
  Inductive OwnModeFlag :=
  | MM_OWN_MODE_UNDEF
  | MM_MODE_INVALID
  | MM_MODE_UNOWNED
  | MM_MODE_SHARED.

  Definition ADDR_VAL :=  N. (* we may need an invariant to figure out the range of the address *)

  Inductive PTE_TY :=
  | PTE_UNDEF
  | PTE_ABSENT (addr: N)
  | PTE_VALID (addr: N) (block_addr: N) (mf: ModeFlag) (omf: OwnModeFlag).
  (* addr is the base address of the PTE *)
  
  Definition PT := (Map PTE_TY).
  
  Record ST1PTP :=
    mkST1PTP {
        st1_root_table: PTE_TY;
        st1l1pt : PT;
        st1l0pt : PT
      }.
  
  Record ST2PTP :=
    mkST2PTP {
        st2_root_table: PTE_TY;
        st2l2pt : PT;
        st2l1pt : PT;
        st2l0pt : PT
      }.

  Inductive PTP_TY :=
  | PTP_ST1 (ptp_st1: ST1PTP)
  | PTP_ST2 (ptp_st2: ST2PTP).

 
  Definition GPTP := (Map PTP_TY).

  Definition pt_manager : Type := ident -> option GPTP.
  Definition inital_pt_manager: mp_manager := fun _ => None.
  Definition pt_update (m: pt_manager) (k0: ident) (v: option GPTP): pt_manager :=
    fun k1 => if rel_dec k0 k1 then v else m k1
  .

End AbsData.

Module PTHIGH.

  Include AbsData.

  Definition TEST_HEAP_SIZE := 1024%N. 
  Definition pte_paddr_begin := 4000%N.
  Definition entry_size := 16.
  Definition root_id := 0.
  Definition thread_set := [1; 2].
  
  Definition init_mpool (base_addr: option N) (curid : ident) (pid: ident) (limit: N) : mpool :=
    {| chunk_addr := base_addr;
       chunk_limit := (entry_size * limit)%N;
       fallback := if (eq_dec root_id curid) then None else Some pid |}.

  Definition init_ST1PTP (addr: N) :=
    {| st1_root_table := PTE_ABSENT addr;
       st1l1pt := (newMap PTE_TY);
       st1l0pt := (newMap PTE_TY) |}.                    

  Definition init_ST2PTP (addr: N) :=
    {| st2_root_table := PTE_ABSENT addr;
       st2l2pt := (newMap PTE_TY);
       st2l1pt := (newMap PTE_TY);
       st2l0pt := (newMap PTE_TY) |}.                    
  
  Definition init_ptp (nid: ident) (stage: N) (addr: N) :=
    if (eq_dec stage 1)
    then (PTP_ST1 (init_ST1PTP addr))
    else (PTP_ST2 (init_ST2PTP addr)).

  Definition root_map := (MapPut mpool) (newMap mpool) root_id (init_mpool (Some  pte_paddr_begin) root_id root_id TEST_HEAP_SIZE).

  Fixpoint initialize_mpool (l: list N) (init_map : (Map mpool)) :=
    match l with
    | nil => init_map
    | hd::tl => let res := initialize_mpool tl init_map in
                (MapPut mpool) res hd (init_mpool None hd root_id 0)
    end.
                
  Definition init_mp := initialize_mpool thread_set root_map.

  Let mpool_init  (vs : list val@{expr.u1}): (val@{expr.u2} * list val@{expr.u3}) :=
    let retv := match vs with
                | nil =>
                  unwrap (let new_mp := init_mp in
                          Some (Vabs (upcast new_mp))) Vnodef
                | _ => Vnodef
                end
    in
    (retv, nil).

  Let ptp_init  (vs : list val@{expr.u1}): (val@{expr.u2} * list val@{expr.u3}) :=
    let retv := match vs with
                | nil =>
                  unwrap (let new_mp := init_mp in
                          Some (Vabs (upcast (newMap PTP_TY)))) Vnodef
                | _ => Vnodef
                end
    in
    (retv, nil).
  
End PTHIGH.

Module PTHIGHTEST.

  Include PTHIGH.
   
  Definition main mp ptp : stmt :=
    Eval compute in INSERT_YIELD (    
      (DebugHigh "[high-model] Calling ptable_init" Vnull) #;
      mp #= (CoqCode [] mpool_init) #;
      ptp #= (CoqCode [] ptp_init) #;
      (DebugHigh "[high-model] End ptable_init" Vnull)).


  Definition ptable_init : stmt :=
    Eval compute in INSERT_YIELD (Skip).    


  Definition mainF: function.
    mk_function_tac main ([]: list var) (["mp" ; "ptp"] : list var).
  Defined.

  Definition ptable_initF: function.
    mk_function_tac ptable_init ([]: list var) ([] : list var).
  Defined.

  
  Definition program: program :=
    [
      ("main", mainF) ;
    ("ptable_init", ptable_initF)
    ].
  
  Definition isem: itree Event unit :=
    eval_multimodule [program_to_ModSem program]
      (* eval_multimodule [LOCK.modsem ; program_to_ModSem program] *)
  .

End PTHIGHTEST.


Section ADDR_TRANSLATION.
    
  (* This one is for later implementation *)
  
  (*  This is the wrapper definition for va_addr to distinguish it with normal natural numbers -
     We can remove some of them later *)
  Inductive va_addr :=
  | VA_ADDR (va: N).

  Inductive ipa_addr :=
  | IPA_ADDR (ipa: N).

  (* Low level functional model for mm_index *)
  (*
  Definition mm_index (addr level: var) (v  : var) : stmt :=
    v #= addr #>> (PAGE_BITS + (level * PAGE_LEVEL_BITS)) #;
      Return (v #& ((UINT64_C(1) #<< PAGE_LEVEL_BITS) - 1)).
   *)

  (* high-level functional model for mm_index - It is quite same. we just change the definition as a normal Coq definition  *)
  Definition h_mm_index  (va : va_addr) (level : N) : N :=
    match va with
    | VA_ADDR va' =>
      let v := (N.shiftr va' ((level * PAGE_LEVEL_BITS)%N + PAGE_BITS)%N) in
      let mask := (N.shiftl 1 PAGE_LEVEL_BITS) - 1 in
      (N.land v mask) 
    end.

  Definition va_page_bits (va: va_addr) : N :=
    match va with
    | VA_ADDR va' =>
      let mask := (N.shiftl 1 PAGE_BITS) - 1 in
      (N.land va' mask)
    end.

  Definition ipa_block_idx (level : N) (ipa : ipa_addr) : N :=
    match ipa with
    | IPA_ADDR ipa' =>
      let mask := (N.shiftl 1 PAGE_LEVEL_BITS) - 1 in
      (N.land (N.shiftr ipa' ((level * PAGE_LEVEL_BITS)%N + PAGE_BITS)%N) mask) 
    end.
 
End ADDR_TRANSLATION.

