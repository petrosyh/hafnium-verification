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
Require Import MemoryManagement.
Require Import ADDR.
Require Import ArchMM.

Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int.
Import MMCONCURSTRUCT.
Import MMCONCUR.
Import ADDR.
Import ArchMM.

Set Implicit Arguments.

Module MMTEST.

(* some unit tests *)

Module PageTableFromPa.

  Definition main pa pt: stmt :=
    pa #= (Vlong (Int64.repr 3500)) #;
    Put "pa: " pa#;
    pt #= (Call "MM.mm_page_table_from_pa" [CBV pa]) #;
    Put "pt: " pt#;
    Skip.

  Definition mainF: function. mk_function_tac main ([]: list var) ["pa" ; "pt"]. Defined.
  
  Definition main_program: program :=
    [
      ("main", mainF)
    ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; MMCONCUR.mm_modsem ; ADDR.addr_modsem].

End PageTableFromPa.

Module PaStartOfNextBlk.

  Definition main pa blk_sz res: stmt :=
    pa #= (Vlong (Int64.repr 3500)) #;
    Put "pa: " pa#;
    blk_sz #= (Vlong (Int64.repr 8)) #;
    Put "block size: " blk_sz#;
    res #= (Call "MM.mm_pa_start_of_next_block" [CBV pa; CBV blk_sz]) #; 
    Put "res: " res#;
    Skip.

  Definition mainF: function. mk_function_tac main ([]: list var) ["pa" ; "blk_sz" ; "res"]. Defined.
  
  Definition main_program: program :=
    [
      ("main", mainF)
    ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; MMCONCUR.mm_modsem ; ADDR.addr_modsem].

End PaStartOfNextBlk.

Module MaxLv.

  Definition main flag res: stmt :=
    flag #= Vlong (Int64.repr 0) #;
    Put "flag: " flag#;
    res #= (Call "MM.mm_max_level" [CBV flag]) #; 
    Put "res: " res#;
    Skip.

  Definition mainF: function. mk_function_tac main ([]: list var) ["flag" ; "res"]. Defined.
  
  Definition main_program: program :=
    [
      ("main", mainF)
    ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; MMCONCUR.mm_modsem ; ArchMM.arch_mm_modsem; ADDR.addr_modsem].

End MaxLv.

Module RootTableCount.

  Definition main flag res: stmt :=
    flag #= Vlong (Int64.repr 0) #;
    Put "flag: " flag#;
    res #= (Call "MM.mm_root_table_count" [CBV flag]) #; 
    Put "res: " res#;
    Skip.

  Definition mainF: function. mk_function_tac main ([]: list var) ["flag" ; "res"]. Defined.
  
  Definition main_program: program :=
    [
      ("main", mainF)
    ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; MMCONCUR.mm_modsem ; ArchMM.arch_mm_modsem; ADDR.addr_modsem].

End RootTableCount.

Module TLBI.

  Definition main flag res: stmt :=
    flag #= Vlong (Int64.repr 0) #;
    Put "flag: " flag#;
    res #= (Call "MM.mm_invalidate_tlb" [CBV flag]) #; 
    Put "res: " res#;
    Skip.

  Definition mainF: function. mk_function_tac main ([]: list var) ["flag" ; "res"]. Defined.
  
  Definition main_program: program :=
    [
      ("main", mainF)
    ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; MMCONCUR.mm_modsem ; ArchMM.arch_mm_modsem; ADDR.addr_modsem].

End TLBI.

End MMTEST.
