(*
 * Copyright 2020 Youngju Song / Jieung Kim
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
Require Import Constant.
Require Import ADDR.
Require Import ArchMM.
Require Import ArchMMHighSpec.
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import ArchMM.
Import ADDR.
Import Int64.

Set Implicit Arguments.



(* XXX: Some tests that is not defined yet: 
    ("ARCHMM.arch_mm_block_from_pte",  arch_mm_block_from_pte_call) ;
    ("ARCHMM.arch_mm_table_from_pte", arch_mm_table_from_pte_call) ;
    ("ARCHMM.arch_mm_clear_pa", arch_mm_clear_pa_call) ;
*)

Module ArchMMTEST.
  
  Module ARCHMMSIMPLE.

    Definition main p1  res1: stmt :=
      p1 #= (Vcomp (Vlong (Int64.repr 0))) #;
         (* p1 #= (Vcomp (Vptr 2%positive (Ptrofs.repr 0))) #; *)
         res1 #= (Call "ARCHMM.arch_mm_table_pte" [CBV (Int64.repr 0); CBV p1]) #;
         Put "res1: " res1 #;
         (Call "ARCHMM.arch_mm_print_archmm_call" [CBR p1]) #;
         p1 #= (Vcomp (Vlong (Int64.repr 72))) #;
         res1 #= (Call "ARCHMM.arch_mm_table_pte" [CBV (Int64.repr 0); CBR p1]) #;
         Put "res1: " res1 #;
         (Call "ARCHMM.arch_mm_print_archmm_call" [CBR p1]) #;
         p1 #= (Vcomp (Vlong (Int64.repr 64))) #;
         res1 #= (Call "ARCHMM.arch_mm_block_pte" [CBV (Vcomp (Vlong (Int64.repr 0))) ; CBR p1;
                                                  CBV (Vcomp (Vlong (Int64.repr 16)))] ) #;
         Put "p1: " p1 #;
         Put "res1: " res1 #;
         p1 #= (Vcomp (Vlong (Int64.repr 64))) #;
         res1 #= (Call "ARCHMM.arch_mm_block_pte" [CBV (Vcomp (Vlong (Int64.repr 1))) ; CBR p1;
                                                  CBV (Vcomp (Vlong (Int64.repr 16)))] ) #;
         Put "p1: " p1 #;
         Put "res1: " res1 #;
         Put "block_allowed" (Call "ARCHMM.arch_mm_is_block_allowed" [CBV (Vcomp (Vlong (Int64.repr 0)))]) #;
         Put "block_allowed" (Call "ARCHMM.arch_mm_is_block_allowed" [CBV (Vcomp (Vlong (Int64.repr 1)))]) #;
         Put "block_allowed" (Call "ARCHMM.arch_mm_is_block_allowed" [CBV (Vcomp (Vlong (Int64.repr 2)))]).
         
    (*
    Definition arch_mm_is_block_allowed (level:var) :=
    Return (level <= (repr 2)).
  Definition arch_mm_pte_is_present (pte level:var) :=
    #if (((Call "ARCHMM.arch_mm_pte_is_valid" [CBV pte; CBV level]) #|| (pte #& STAGE2_SW_OWNED)) == (repr 0))
     then Return (repr 0)
     else Return (repr 1).


  Definition arch_mm_pte_is_valid (pte level:var) (pte_valid :var) :=
    #if ((pte #& PTE_VALID) == (repr 0))
     then Return (repr 0)
     else Return (repr 1).
  Definition arch_mm_pte_is_block (pte level:var) (blk_allowed ret is_blk is_present is_table:var) :=
    #if (Call "ARCHMM.arch_mm_is_block_allowed" [CBV level])
     then (#if (level == (repr 0))
    *)
    

    Definition mainF: function. mk_function_tac main ([]: list var) ["p1"; "res1"]. Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem1: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMM.arch_mm_modsem ; ADDR.addr_modsem].
    
    (*
    Definition isem2: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMMHighSpec.arch_mm_modsem].
    *)
   
  End ARCHMMSIMPLE.
  
  (*
  (* some unit tests *)
  Module ABSENT.

    Definition main res: stmt :=
      res #= (Call "ARCHMM.arch_mm_absent_pte" [CBV (Int64.repr 0)]) #;
          Put "res: " res.

    Definition mainF: function. mk_function_tac main ([]: list var) ["res"]. Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem1: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMM.arch_mm_modsem].


    Definition isem2: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMMHighSpec.arch_mm_modsem].
    
  End ABSENT.

  Module ARCHMMPTETABLE.

    Definition main p1 p2 p3 p4 p5 res1 res2 res3 res4 res5: stmt :=
      p1 #= (Vcomp (Vptr 2%positive (Ptrofs.repr 0))) #;
         res1 #= (Call "ARCHMM.arch_mm_table_pte" [CBV (Int64.repr 0); CBR p1]) #;
         Put "res1: " res1 #;
         (Call "ARCHMM.arch_mm_print_archmm_call" [CBR p1]) #; 

         p2 #= (Vcomp (Vptr 2%positive (Ptrofs.repr 64))) #;
         res2 #= (Call "ARCHMM.arch_mm_table_pte" [CBV (Int64.repr 2); CBR p2]) #;
         Put "res2: " res2 #;
         (Call "ARCHMM.arch_mm_print_archmm_call" [CBR p2]) #; 
         
         (Call "ARCHMM.arch_mm_set_stage1" []) #;
         
         p3 #= (Vcomp (Vptr 2%positive (Ptrofs.repr 128))) #;
         res3 #= (Call "ARCHMM.arch_mm_table_pte" [CBV (Int64.repr 0); CBR p3]) #;
         Put "res3: " res3 #;
         (Call "ARCHMM.arch_mm_print_archmm_call" [CBR p3]) #;

         p4 #= (Vcomp (Vptr 2%positive (Ptrofs.repr 256))) #;
         res4 #= (Call "ARCHMM.arch_mm_table_pte" [CBV (Int64.repr 3); CBR p4]) #;
         Put "res4: " res4 #;
         (Call "ARCHMM.arch_mm_print_archmm_call" [CBR p4]) #;
         
         (Call "ARCHMM.arch_mm_set_stage2" []) #;
         p5 #= (Vcomp (Vptr 2%positive (Ptrofs.repr 320))) #;
         res5 #= (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); CBR p5; CBV (Int64.repr 7)]) #;
         Put "res5: " res5 #;
         (Call "ARCHMM.arch_mm_print_archmm_call" [CBR p5]) #; 

         (* XXX : Something went wrong in here - need to fix for the following things *)
         Put "p1 present" (Call "ARCHMM.arch_mm_pte_is_present" [CBR p1; CBV (Int64.repr 1)]) #;
         Put "p2 present" (Call "ARCHMM.arch_mm_pte_is_present" [CBR p2; CBV (Int64.repr 1)]) #;
         Put "p3 present" (Call "ARCHMM.arch_mm_pte_is_present" [CBR p3; CBV (Int64.repr 1)]) #;
         Put "p4 present" (Call "ARCHMM.arch_mm_pte_is_present" [CBR p4; CBV (Int64.repr 1)]) #;
         Put "p5 present" (Call "ARCHMM.arch_mm_pte_is_present" [CBR p5; CBV (Int64.repr 1)]) #;
         Put "p1 valid" (Call "ARCHMM.arch_mm_pte_is_valid" [CBR p5; CBV (Int64.repr 1)]) #;
         Put "p2 valid" (Call "ARCHMM.arch_mm_pte_is_valid" [CBR p5; CBV (Int64.repr 1)]) #;
         Put "p3 valid" (Call "ARCHMM.arch_mm_pte_is_valid" [CBR p5; CBV (Int64.repr 1)]) #;
         Put "p4 valid" (Call "ARCHMM.arch_mm_pte_is_valid" [CBR p5; CBV (Int64.repr 1)]) #;
         Put "p5 valid" (Call "ARCHMM.arch_mm_pte_is_valid" [CBR p5; CBV (Int64.repr 1)]) #;
         Put "p1 table" (Call "ARCHMM.arch_mm_pte_is_table" [CBR p1; CBV (Int64.repr 1)]) #;
         Put "p2 table" (Call "ARCHMM.arch_mm_pte_is_table" [CBR p2; CBV (Int64.repr 1)]) #;
         Put "p3 table" (Call "ARCHMM.arch_mm_pte_is_table" [CBR p3; CBV (Int64.repr 1)]) #;
         Put "p4 table" (Call "ARCHMM.arch_mm_pte_is_table" [CBR p4; CBV (Int64.repr 1)]) #;
         Put "p5 table" (Call "ARCHMM.arch_mm_pte_is_table" [CBR p5; CBV (Int64.repr 1)]) #;
         Put "p1 block" (Call "ARCHMM.arch_mm_pte_is_block" [CBR p1; CBV (Int64.repr 1)]) #;
         Put "p2 block" (Call "ARCHMM.arch_mm_pte_is_block" [CBR p2; CBV (Int64.repr 1)]) #;
         Put "p3 block" (Call "ARCHMM.arch_mm_pte_is_block" [CBR p3; CBV (Int64.repr 1)]) #;
         Put "p4 block" (Call "ARCHMM.arch_mm_pte_is_block" [CBR p4; CBV (Int64.repr 1)]) #;
         Put "p5 block" (Call "ARCHMM.arch_mm_pte_is_block" [CBR p5; CBV (Int64.repr 1)]).
          
    Definition mainF: function. mk_function_tac
                                  main
                                  ([]: list var)
                                  ["p1"; "p2"; "p3"; "p4"; "p5" ; "res1"; "res2"; "res3"; "res4" ; "res5"].
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].
    
    Definition isem1: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMM.arch_mm_modsem ; ADDR.addr_modsem].
    
    Definition isem2: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMMHighSpec.arch_mm_modsem].
    
  End ARCHMMPTETABLE.

  
  Module ARCHMMADDRATTRS.
    
    Definition main p1 p2 p3 p4 p5 res1 res2 res3 res4 res5: stmt :=
      p1 #= (Vcomp (Vptr 2%positive (Ptrofs.repr 0))) #;
         res1 #= (Call "ARCHMM.arch_mm_table_pte" [CBV (Int64.repr 1); CBR p1]) #;
         Put "res1: " res1 #;

         p2 #= (Vcomp (Vptr 2%positive (Ptrofs.repr 64))) #;
         res2 #= (Call "ARCHMM.arch_mm_table_pte" [CBV (Int64.repr 2); CBR p2]) #;
         Put "res2: " res2 #;
         
         (Call "ARCHMM.arch_mm_set_stage1" []) #;
         
         p3 #= (Vcomp (Vptr 2%positive (Ptrofs.repr 128))) #;
         res3 #= (Call "ARCHMM.arch_mm_table_pte" [CBV (Int64.repr 1); CBR p3]) #;
         Put "res3: " res3 #;

         p4 #= (Vcomp (Vptr 2%positive (Ptrofs.repr 256))) #;
         res4 #= (Call "ARCHMM.arch_mm_table_pte" [CBV (Int64.repr 3); CBR p4]) #;
         Put "res4: " res4 #;
         
         (Call "ARCHMM.arch_mm_set_stage2" []) #;
         p5 #= (Vcomp (Vptr 2%positive (Ptrofs.repr 320))) #;
         res5 #= (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); CBR p5; CBV (Int64.repr 7)]) #;
         Put "res5: " res5 #;
         
         (Call "ARCHMM.arch_mm_set_pte_addr" [CBR p1; CBV (Int64.repr 320)]) #;
         (Call "ARCHMM.arch_mm_set_pte_addr" [CBR p2; CBV (Int64.repr 480)]) #;
         (Call "ARCHMM.arch_mm_set_pte_addr" [CBR p3; CBV (Int64.repr 640)]) #;
         (Call "ARCHMM.arch_mm_set_pte_addr" [CBR p4; CBV (Int64.repr 2048)]) #;
         (Call "ARCHMM.arch_mm_set_pte_addr" [CBR p5; CBV (Int64.repr 4096)]) #;
         Put "p1: " p1 #;
         Put "p2: " p2 #;
         Put "p3: " p3 #;
         Put "p4: " p4 #;
         Put "p5: " p5 #;
         Put "p1 address"  (Call "ARCHMM.pte_addr" [CBR p1]) #;
         Put "p2 address"  (Call "ARCHMM.pte_addr" [CBR p2]) #;
         Put "p3 address"  (Call "ARCHMM.pte_addr" [CBR p3]) #;
         Put "p4 address"  (Call "ARCHMM.pte_addr" [CBR p4]) #;
         Put "p5 address"  (Call "ARCHMM.pte_addr" [CBR p5]) #;

         (Call "ARCHMM.arch_mm_set_pte_attr" [CBR p1; CBV (Int64.repr 4)]) #;
         (Call "ARCHMM.arch_mm_set_pte_attr" [CBR p2; CBV (Int64.repr 4)]) #;
         (Call "ARCHMM.arch_mm_set_pte_attr" [CBR p3; CBV (Int64.repr 12)]) #;
         (Call "ARCHMM.arch_mm_set_pte_attr" [CBR p4; CBV (Int64.repr 12)]) #;
         (Call "ARCHMM.arch_mm_set_pte_attr" [CBR p5; CBV (Int64.repr 47)]) #;
         Put "p1: " p1 #;
         Put "p2: " p2 #;
         Put "p3: " p3 #;
         Put "p4: " p4 #;
         Put "p5: " p5 #;
         Put "p1 attr"  (Call "ARCHMM.arch_mm_pte_attrs" [CBR p1; CBV (Int64.repr 1)]) #;
         Put "p2 attr"  (Call "ARCHMM.arch_mm_pte_attrs" [CBR p2; CBV (Int64.repr 1)]) #;
         Put "p3 attr"  (Call "ARCHMM.arch_mm_pte_attrs" [CBR p3; CBV (Int64.repr 1)]) #;
         Put "p4 attr"  (Call "ARCHMM.arch_mm_pte_attrs" [CBR p4; CBV (Int64.repr 1)]) #;
         Put "p5 attr"  (Call "ARCHMM.arch_mm_pte_attrs" [CBR p5; CBV (Int64.repr 1)]) #;
         Put "Finish" (Vnull).
         

    Definition mainF: function. mk_function_tac
                                  main
                                  ([]: list var)
                                  ["p1"; "p2"; "p3"; "p4"; "p5" ; "res1"; "res2"; "res3"; "res4" ; "res5"].
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].
    
    Definition isem1: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMM.arch_mm_modsem ; ADDR.addr_modsem].
    
    Definition isem2: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMMHighSpec.arch_mm_modsem].
    
  End ARCHMMADDRATTRS.
  
  Module MM_MODE_PTE_ATTRIBUTES.

  
    Definition main (mode1 mode2 mode3 mode4 mode5 mode6 attr1 attr2 attr3 attr4 attr5 attr6 table_attrs1
                           table_attrs2 block_attrs1 block_attrs2 combined_attrs1 combined_attrs2 : var) : stmt :=
      mode1 #= ((Vcomp (Vlong MM_MODE_R)) #| (Vcomp (Vlong MM_MODE_W)))  #;
            attr1 #= (Call "ARCHMM.arch_mm_mode_to_stage1_attrs" [CBV mode1]) #;
            attr2 #= (Call "ARCHMM.arch_mm_mode_to_stage2_attrs" [CBV mode1]) #;
            mode2 #= (((Vcomp (Vlong MM_MODE_R)) #| (Vcomp (Vlong MM_MODE_W)) #| (Vcomp (Vlong MM_MODE_X))))  #;
            attr3 #= (Call "ARCHMM.arch_mm_mode_to_stage1_attrs" [CBV mode2]) #;
            attr4 #= (Call "ARCHMM.arch_mm_mode_to_stage2_attrs" [CBV mode2]) #;
            mode3 #=  (((Vcomp (Vlong MM_MODE_R)) #| (Vcomp (Vlong MM_MODE_W)) #| (Vcomp (Vlong MM_MODE_X))))
            #| (Vcomp (Vlong MM_MODE_D)) #| (Vcomp (Vlong MM_MODE_UNOWNED))
            #| (Vcomp (Vlong MM_MODE_SHARED)) #| (Vcomp (Vlong MM_MODE_INVALID)) #;
            attr5 #= (Call "ARCHMM.arch_mm_mode_to_stage1_attrs" [CBV mode3]) #;
            attr6 #= (Call "ARCHMM.arch_mm_mode_to_stage2_attrs" [CBV mode3]) #;
            (* XXX: Need to fix the following things 
            mode4 #= (Call "ArchMM.arch_mm_stage2_attrs_to_mode" [CBV attr2]) #;
            mode5 #= (Call "ArchMM.arch_mm_stage2_attrs_to_mode" [CBV attr4]) #; 
            mode6 #= (Call "ArchMM.arch_mm_stage2_attrs_to_mode" [CBV attr6]) #; *) 
            Put "mode1 : " mode1 #;
            Put "mode2 : " mode2 #;
            Put "mode3 : " mode3 #;
            (*
            Put "mode4 : " mode4 #;
            Put "mode5 : " mode5 #;
            Put "mode6 : " mode6 #;
            *)
            Put "attr1 : " attr1 #;
            Put "attr2 : " attr2 #;
            Put "attr3 : " attr3 #;
            Put "attr4 : " attr4 #;
            table_attrs1 #= (Vcomp (Vlong Constant.TABLE_NSTABLE)) #| (Vcomp (Vlong Constant.TABLE_APTABLE0)) #;
            block_attrs1 #= (Vcomp (Vlong Constant.STAGE1_AP2)) #;
            combined_attrs1 #= (Call "ARCHMM.arch_mm_combine_table_entry_attrs" [CBV table_attrs1; CBV block_attrs1]) #;
            table_attrs2 #=
            (((((Vcomp (Vlong Constant.TABLE_NSTABLE))
                  #| (Vcomp (Vlong Constant.TABLE_APTABLE1)))
                 #| (Vcomp (Vlong Constant.TABLE_APTABLE0)))
                #| (Vcomp (Vlong Constant.TABLE_XNTABLE)))
               #| (Vcomp (Vlong Constant.TABLE_PXNTABLE))) #;
            block_attrs2 #=
            ((((Vcomp (Vlong Constant.STAGE1_AP2))
                 #| (Vcomp (Vlong Constant.STAGE1_AP1)))
                #| (Vcomp (Vlong Constant.STAGE1_XN)))
               #| (Vcomp (Vlong Constant.STAGE1_PXN))) #;
            combined_attrs1 #= (Call "ARCHMM.arch_mm_combine_table_entry_attrs" [CBV table_attrs1; CBV block_attrs1]) #;
            Put "combined attrs1 : " combined_attrs1 #;
            Put "combined attrs2 : " combined_attrs2.
            
    Definition mainF: function.
      mk_function_tac main ([]: list var)
                      ["mode1"; "mode2"; "mode3"; "mode4"; "mode5"; "mode6";
                       "attr1"; "attr2"; "attr3"; "attr4"; "attr5"; "attr6";
                       "table_attrs1"; "table_attrs2"; "block_attrs1"; "block_attrs2";
                       "combined_attrs1"; "combined_attrs2"]. Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].
    
    Definition isem1: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMM.arch_mm_modsem ; ADDR.addr_modsem].
    
    Definition isem2: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMMHighSpec.arch_mm_modsem].
    

  End MM_MODE_PTE_ATTRIBUTES.
  
  Module ARCHMM_STAGE_MAX_LEVEL_ROOT_TABLE_COUNT.

    Definition main res1 res2 res3 res4 res5 res6: stmt :=
         res1 #= (Call "ARCHMM.arch_mm_stage1_max_level" []) #;
         res2 #= (Call "ARCHMM.arch_mm_stage2_max_level" []) #;
         res3 #= (Call "ARCHMM.arch_mm_stage1_root_table_count" []) #;
         res4 #= (Call "ARCHMM.arch_mm_stage2_root_table_count" []) #;
         res5 #= (Call "ARCHMM.arch_mm_is_block_allowed" [CBV (Vcomp (Vlong (Int64.repr 2)))]) #;
         res6 #= (Call "ARCHMM.arch_mm_is_block_allowed" [CBV (Vcomp (Vlong (Int64.repr 0)))]) #;
         Put "res1" res1 #;
         Put "res2" res2 #;
         Put "res3" res3 #;
         Put "res4" res4 #;
         Put "res5" res5 #;
         Put "res6" res6.
          
    Definition mainF: function. mk_function_tac main ([]: list var) ["res1"; "res2"; "res3"; "res4"; "res5"; "res6"]. Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].
    
    Definition isem1: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMM.arch_mm_modsem ; ADDR.addr_modsem].
    
    Definition isem2: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMMHighSpec.arch_mm_modsem].
    
  End ARCHMM_STAGE_MAX_LEVEL_ROOT_TABLE_COUNT.
  *)
  
End ArchMMTEST.


