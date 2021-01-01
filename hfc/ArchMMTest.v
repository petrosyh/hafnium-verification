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
  
  Module ARCHMMFULLTEST.
    
    Definition main address1 address2 stage2_sw_owned mode attrs access block_attrs table_attrs: stmt :=
      (* expect 0 *)
      address1 #=  ((Int64.repr 123456) #<< PAGE_BITS) #;
               address2 #= ((Int64.repr 12381234) #<< PAGE_BITS) #;
               
               Put "calling ARCHMM.arch_mm_absent_pte" (Vnull) #;
               Put "arch_mm_absent_pte" (Call "ARCHMM.arch_mm_absent_pte" [CBV (Int64.repr 0)]) #;
               
               Put "calling ARCHMM.arch_mm_table_pte" (Vnull) #;
               Put "arch_mm_table_pte" (Call "ARCHMM.arch_mm_table_pte"
                                             [CBV (Int64.repr 0); CBV (Int64.repr 0)]) #;

              Put "calling ARCHMM.arch_mm_table_pte" (Vnull) #;
               Put "arch_mm_table_pte" (Call "ARCHMM.arch_mm_table_pte"
                                             [CBV (Int64.repr 0); CBV address1]) #;
               
               Put "calling ARCHMM.arch_mm_block_pte" (Vnull) #;
               stage2_sw_owned  #= Constant.STAGE2_SW_OWNED #;
               Put "arch_mm_block_pte" (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 3); 
                                                                        CBV address1; CBV stage2_sw_owned]) #;
               Put "arch_mm_block_pte" (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 3); 
                                                                        CBV address1; CBV stage2_sw_owned]) #;
               Put "arch_mm_block_pte" (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 3); 
                                                                        CBV (Int64.repr 0); CBV (Int64.repr 0)]) #;
               Put "arch_mm_block_pte" (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 2); 
                                                                        CBV  (Int64.repr 0); CBV stage2_sw_owned]) #;
               
               Put "Calling ARCHMM.arch_mm_is_block_allowed" (Vnull) #;
               Put "arch_mm_is_block_allowed"
               (Call "ARCHMM.arch_mm_is_block_allowed" [CBV (Int64.repr 1)]) #;
               Put "arch_mm_is_block_allowed"
               (Call "ARCHMM.arch_mm_is_block_allowed" [CBV (Int64.repr 3)]) #;

               Put "Calling ARCHMM.arch_mm_pte_is_valid" (Vnull) #;
               Put "arch_mm_pte_is_valid"
               (Call "ARCHMM.arch_mm_pte_is_valid"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Int64.repr 0)]) #;               
               Put "arch_mm_pte_is_valid"
               (Call "ARCHMM.arch_mm_pte_is_valid"
                     [CBV (Call "ARCHMM.arch_mm_table_pte"
                                [CBV (Int64.repr 0); CBV (Int64.repr 0)]);
                     CBV (Int64.repr 0)]) #;
               
               Put "Calling ARCHMM.arch_mm_pte_is_present" (Vnull) #;
               Put "arch_mm_pte_is_present"
               (Call "ARCHMM.arch_mm_pte_is_present"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Int64.repr 1)]) #;
               Put "arch_mm_pte_is_present"
               (Call "ARCHMM.arch_mm_pte_is_present"
                     [CBV (Call "ARCHMM.arch_mm_table_pte"
                                [CBV (Int64.repr 0); CBV (Int64.repr 0)]);
                     CBV (Int64.repr 0)]) #;

               Put "Calling ARCHMM.arch_mm_pte_is_block" (Vnull) #;

               Put "arch_mm_pte_is_block"
               (Call "ARCHMM.arch_mm_pte_is_block"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Int64.repr 1)]) #;
               Put "arch_mm_pte_is_block"
               (Call "ARCHMM.arch_mm_pte_is_block"
                     [CBV (Call "ARCHMM.arch_mm_table_pte"
                                [CBV (Int64.repr 0); CBV (Int64.repr 0)]);
                     CBV (Int64.repr 0)]) #;

               Put "Calling ARCHMM.pte_addr" (Vnull) #;
               Put "pte_addr"
               (Call "ARCHMM.pte_addr"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 0); 
                                                           CBV address1; CBV stage2_sw_owned])]) #;
               Put "pte_addr"
               (Call "ARCHMM.pte_addr"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned])]) #;
               
               Put "Calling ARCHMM.arch_mm_clear_pa" (Vnull) #;
               Put "arch_mm_clear_pa"
               (Call "ARCHMM.arch_mm_clear_pa"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned])]) #;
               
               Put "Calling ARCHMM.arch_mm_block_from_pte" (Vnull) #;
               Put "arch_mm_block_from_pte"
               (Call "ARCHMM.arch_mm_block_from_pte"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Int64.repr 0)]) #;

               Put "Calling ARCHMM.arch_mm_table_from_pte" (Vnull) #;
               Put "arch_mm_table_from_pte"
               (Call "ARCHMM.arch_mm_table_from_pte"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Int64.repr 0)]) #;

               Put "Calling ARCHMM.arch_mm_pte_attrs" (Vnull) #;
               Put "arch_mm_pte_attrs"
               (Call "ARCHMM.arch_mm_pte_attrs"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Int64.repr 0)]) #;

               Put "Calling ARCHMM.arch_mm_invalidate_stage1_range " (Vnull) #;
               (Call "ARCHMM.arch_mm_invalidate_stage1_range"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                          CBV address2; CBV stage2_sw_owned])]) #;

               Put "Calling ARCHMM.arch_mm_invalidate_stage2_range " (Vnull) #;
               (Call "ARCHMM.arch_mm_invalidate_stage2_range"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                          CBV address2; CBV stage2_sw_owned])]) #;

               Put "Calling ARCHMM.arch_mm_mode_to_stage1_attrs" (Vnull) #;
               mode #= (Constant.MM_MODE_W #| Constant.MM_MODE_D) #;
               attrs #= (Constant.STAGE1_AF #| (Constant.STAGE1_SH Constant.OUTER_SHAREABLE)
                                            #| Constant.STAGE1_XN
                                            #| (Constant.STAGE1_AP Constant.STAGE1_READWRITE)
                                            #| (Constant.STAGE1_ATTRINDX Constant.STAGE1_DEVICEINDX)
                                            #| (Constant.PTE_VALID)) #;
               Put "arch_mm_mode_to_stage1_attrs" 
               (Call "ARCHMM.arch_mm_mode_to_stage1_attrs" [CBV mode]) #;
               Put "arch_mm_mode_to_stage1_attrs valid check" attrs #;
               mode #= (Constant.MM_MODE_X #| Constant.MM_MODE_W #| Constant.MM_MODE_D #|
                                           Constant.MM_MODE_INVALID) #;
               attrs #= (Constant.STAGE1_AF #| (Constant.STAGE1_SH Constant.OUTER_SHAREABLE)
                                            #| (Constant.STAGE1_AP Constant.STAGE1_READWRITE)
                                            #| (Constant.STAGE1_ATTRINDX Constant.STAGE1_DEVICEINDX)) #;
               Put "arch_mm_mode_to_stage1_attrs" 
               (Call "ARCHMM.arch_mm_mode_to_stage1_attrs" [CBV mode]) #;
               Put "arch_mm_mode_to_stage1_attrs valid check" attrs #;
               mode #= (Int64.repr 0) #;
               attrs #= (Constant.STAGE1_AF #| (Constant.STAGE1_SH Constant.OUTER_SHAREABLE)
                                            #| Constant.STAGE1_XN                                            
                                            #| (Constant.STAGE1_AP Constant.STAGE1_READONLY)
                                            #| (Constant.STAGE1_ATTRINDX Constant.STAGE1_NORMALINDX)
                                            #| (Constant.PTE_VALID)) #;
               Put "arch_mm_mode_to_stage1_attrs" 
               (Call "ARCHMM.arch_mm_mode_to_stage1_attrs" [CBV mode]) #;
               Put "arch_mm_mode_to_stage1_attrs valid check" attrs #;
               

               Put "Calling ARCHMM.arch_mm_mode_to_stage2_attrs" (Vnull) #;
               mode #= (Constant.MM_MODE_R #| Constant.MM_MODE_W #|
                                           MM_MODE_UNOWNED #| MM_MODE_SHARED #| MM_MODE_INVALID) #;
               access #= (access #| Constant.STAGE2_ACCESS_READ #| Constant.STAGE2_ACCESS_WRITE) #;
               attrs #=  (Constant.STAGE2_AF #| (Constant.STAGE2_SH Constant.NON_SHAREABLE)
                                             #| (Constant.STAGE2_S2AP_DSL access)
                                             #| (Constant.STAGE2_XN Constant.STAGE2_EXECUTE_NONE)
                                             #| (Constant.STAGE2_MEMATTR Constant.STAGE2_WRITEBACK
                                                                         Constant.STAGE2_WRITEBACK)) #;
               Put "arch_mm_mode_to_stage2_attrs" 
               (Call "ARCHMM.arch_mm_mode_to_stage2_attrs" [CBV mode]) #;
               Put "arch_mm_mode_to_stage2_attrs valid check" attrs #;

               Put "Calling ARCHMM.arch_mm_stage2_attrs_to_mode" (Vnull) #;

               mode #= (Constant.MM_MODE_R) #;
               
               Put "arch_mm_stage2_attrs_to_mode"
               (Call "ARCHMM.arch_mm_stage2_attrs_to_mode"
                     [CBV (Call "ARCHMM.arch_mm_mode_to_stage2_attrs" [CBV mode])]) #;
               Put "arch_mm_stage2_attr_to_mode valid check" mode #;
               
               
               mode #= (Constant.MM_MODE_R #| Constant.MM_MODE_W #|
                                           MM_MODE_UNOWNED #| MM_MODE_SHARED #| MM_MODE_INVALID) #;
               
               Put "arch_mm_stage2_attrs_to_mode"
               (Call "ARCHMM.arch_mm_stage2_attrs_to_mode"
                     [CBV (Call "ARCHMM.arch_mm_mode_to_stage2_attrs" [CBV mode])]) #;
               Put "arch_mm_stage2_attr_to_mode valid check" mode #;

               Put "auxiliary functions" (Vnull) #;
               Put "arch_mm_stage1_max_level" (Call "ARCHMM.arch_mm_stage1_max_level" []) #;
               Put "arch_mm_stage2_max_level" (Call "ARCHMM.arch_mm_stage2_max_level" []) #;
               Put "arch_mm_stage1_root_table_count" (Call "ARCHMM.arch_mm_stage1_root_table_count" []) #;
               Put "arch_mm_stage2_root_table_count" (Call "ARCHMM.arch_mm_stage2_root_table_count" []) #;
               
               Put "Calling ARCHMM.arch_mm_mode_to_stage2_attrs" (Vnull) #;
               block_attrs #= (Constant.STAGE1_AF #| (Constant.STAGE1_SH Constant.OUTER_SHAREABLE)
                                                  #| Constant.STAGE1_XN
                                                  #| (Constant.STAGE1_AP Constant.STAGE1_READONLY)
                                                  #| (Constant.STAGE1_ATTRINDX
                                                        Constant.STAGE1_NORMALINDX)
                                                  #| (Constant.PTE_VALID)) #;
               
               table_attrs #= (Constant.TABLE_NSTABLE #| Constant.TABLE_APTABLE1
                                                      #| Constant.TABLE_APTABLE0
                                                      #| Constant.TABLE_XNTABLE
                                                      #| Constant.TABLE_PXNTABLE) #;
                Put "arch_mm_combine_table_entry_attrs"
                (Call "ARCHMM.arch_mm_combine_table_entry_attrs" [CBV table_attrs; CBV block_attrs]) #;
                block_attrs #= (((block_attrs #| Constant.STAGE1_NS
                                              #| Constant.STAGE1_AP2)
                                   #& (Not (Constant.STAGE1_AP1)))
                                  #| Constant.STAGE1_XN #| Constant.STAGE1_PXN) #;
                Put "arch_mm_combine_table_entry_attrs valid check" block_attrs.

    Definition mainF: function.
      mk_function_tac main ([]: list var) ["address1"; "address2"; "stage2_sw_owned";
                                           "mode"; "attrs"; "access";
                                           "block_attrs"; "table_attrs"].
    Defined.
    
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
   
  End ARCHMMFULLTEST.

  
  Module ARCHMMPARTIALTEST.
    
    Definition main address1 address2 stage2_sw_owned pte_valid_val pte_table_val mode attrs access block_attrs table_attrs: stmt :=
      (* expect 0 *)
      address1 #=  ((Int64.repr 123456) #<< PAGE_BITS) #;
               address2 #= ((Int64.repr 12381234) #<< PAGE_BITS) #;
               
               Put "calling ARCHMM.arch_mm_absent_pte" (Vnull) #;
               Put "arch_mm_absent_pte" (Call "ARCHMM.arch_mm_absent_pte" [CBV (Int64.repr 0)]) #;

               Put "calling ARCHMM.arch_mm_table_pte" (Vnull) #;
               Put "arch_mm_table_pte" (Call "ARCHMM.arch_mm_table_pte"
                                             [CBV (Int64.repr 0); CBV (Int64.repr 0)]) #;
               Put "calling ARCHMM.arch_mm_table_pte" (Vnull) #;
               Put "arch_mm_table_pte" (Call "ARCHMM.arch_mm_table_pte"
                                             [CBV (Int64.repr 0); CBV address1]) #;

               Put "calling ARCHMM.arch_mm_block_pte" (Vnull) #;
               stage2_sw_owned  #= Constant.STAGE2_SW_OWNED #;
               pte_valid_val   #= stage2_sw_owned  #| Constant.PTE_VALID #;
               pte_table_val   #= pte_valid_val #| Constant.PTE_TABLE #;
               Put "arch_mm_block_pte" (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                                        CBV address1; CBV stage2_sw_owned]) #;
               Put "arch_mm_block_pte" (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                                        CBV address1;
                                                                        CBV pte_valid_val]) #;
               Put "arch_mm_block_pte" (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 3); 
                                                                        CBV address1;
                                                                        CBV pte_table_val]) #;

               
               Put "Calling ARCHMM.arch_mm_is_block_allowed" (Vnull) #;
               Put "arch_mm_is_block_allowed"
               (Call "ARCHMM.arch_mm_is_block_allowed" [CBV (Int64.repr 1)]) #;
               Put "arch_mm_is_block_allowed"
               (Call "ARCHMM.arch_mm_is_block_allowed" [CBV (Int64.repr 3)]) #;

               Put "Calling ARCHMM.arch_mm_pte_is_valid" (Vnull) #;
               Put "arch_mm_pte_is_valid"
               (Call "ARCHMM.arch_mm_pte_is_valid"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV pte_table_val]);
                     CBV (Int64.repr 1)]) #;     
               Put "arch_mm_pte_is_valid"
               (Call "ARCHMM.arch_mm_pte_is_valid"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Int64.repr 1)]) #;

               (Call "ARCHMM.arch_mm_set_stage1" []) #;
               
               Put "arch_mm_pte_is_valid"
               (Call "ARCHMM.arch_mm_pte_is_valid"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV pte_valid_val]);
                     CBV (Int64.repr 1)]) #;
               (Call "ARCHMM.arch_mm_set_stage2" []) #;

               Put "Calling ARCHMM.arch_mm_pte_is_present" (Vnull) #;
               Put "arch_mm_pte_is_present"
               (Call "ARCHMM.arch_mm_pte_is_present"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 3); 
                                                           CBV address1; CBV pte_table_val]);
                     CBV (Int64.repr 3)]) #;
               Put "arch_mm_pte_is_present"               
               (Call "ARCHMM.arch_mm_pte_is_present"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV (Int64.repr 0)]);
                     CBV (Int64.repr 1)]) #;

               Put "arch_mm_pte_attrs"               
               (Call "ARCHMM.arch_mm_pte_attrs" [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 2); 
                                                           CBV address1; CBV stage2_sw_owned]);
                                                CBV (Int64.repr 2)]) #;
               
               Put "arch_mm_pte_is_present"               
               (Call "ARCHMM.arch_mm_pte_is_present"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 2); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Int64.repr 2)]) #;
               Put "arch_mm_pte_is_present"               
               (Call "ARCHMM.arch_mm_pte_is_present"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Int64.repr 1)]) #;               
               
               Put "arch_mm_pte_is_present"
               (Call "ARCHMM.arch_mm_pte_is_present"
                     [CBV (Call "ARCHMM.arch_mm_table_pte"
                                [CBV (Int64.repr 3); CBV address1]);
                     CBV (Int64.repr 3)]) #;

               Put "Calling ARCHMM.arch_mm_pte_is_block" (Vnull) #;
               Put "arch_mm_pte_is_block"
               (Call "ARCHMM.arch_mm_pte_is_block"
                     [CBV (Call "ARCHMM.arch_mm_table_pte" [CBV (Int64.repr 2); 
                                                           CBV address1]);
                     CBV (Int64.repr 2)]) #;
               Put "arch_mm_pte_is_block"
               (Call "ARCHMM.arch_mm_pte_is_block"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 3); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Int64.repr 3)]) #;
               Put "arch_mm_pte_is_block"
               (Call "ARCHMM.arch_mm_pte_is_block"
                     [CBV (Call "ARCHMM.arch_mm_table_pte"
                                [CBV (Int64.repr 0); CBV (Int64.repr 0)]);
                     CBV (Int64.repr 1)]) #;

               Put "Calling ARCHMM.pte_addr" (Vnull) #;
               Put "pte_addr"
               (Call "ARCHMM.pte_addr"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned])]) #;
               Put "pte_addr"
               (Call "ARCHMM.pte_addr"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned])]) #;

               Put "Calling ARCHMM.arch_mm_clear_pa" (Vnull) #;
               Put "arch_mm_clear_pa"
               (Call "ARCHMM.arch_mm_clear_pa"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned])]) #;

               Put "Calling ARCHMM.arch_mm_block_from_pte" (Vnull) #;
               Put "arch_mm_block_from_pte"
               (Call "ARCHMM.arch_mm_block_from_pte"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV pte_table_val]);
                     CBV (Int64.repr 1)]) #;

               Put "Calling ARCHMM.arch_mm_pte_attrs" (Vnull) #;
               Put "arch_mm_pte_attrs"
               (Call "ARCHMM.arch_mm_pte_attrs"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Int64.repr 1)]) #;

               Put "Calling ARCHMM.arch_mm_invalidate_stage1_range " (Vnull) #;
               (Call "ARCHMM.arch_mm_invalidate_stage1_range"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                          CBV address2; CBV stage2_sw_owned])]) #;

               Put "Calling ARCHMM.arch_mm_invalidate_stage2_range " (Vnull) #;
               (Call "ARCHMM.arch_mm_invalidate_stage2_range"
                     [CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                           CBV address1; CBV stage2_sw_owned]);
                     CBV (Call "ARCHMM.arch_mm_block_pte" [CBV (Int64.repr 1); 
                                                          CBV address2; CBV stage2_sw_owned])]) #;
               
               Put "Calling ARCHMM.arch_mm_mode_to_stage1_attrs" (Vnull) #;
               mode #= (Constant.MM_MODE_W #| Constant.MM_MODE_D) #;
               attrs #= (Constant.STAGE1_AF #| (Constant.STAGE1_SH Constant.OUTER_SHAREABLE)
                                            #| Constant.STAGE1_XN
                                            #| (Constant.STAGE1_AP Constant.STAGE1_READWRITE)
                                            #| (Constant.STAGE1_ATTRINDX Constant.STAGE1_DEVICEINDX)
                                            #| (Constant.PTE_VALID)) #;
               Put "arch_mm_mode_to_stage1_attrs" 
               (Call "ARCHMM.arch_mm_mode_to_stage1_attrs" [CBV mode]) #;
               Put "arch_mm_mode_to_stage1_attrs valid check" attrs #;
               mode #= (Constant.MM_MODE_X #| Constant.MM_MODE_W #| Constant.MM_MODE_D #|
                                           Constant.MM_MODE_INVALID) #;
               attrs #= (Constant.STAGE1_AF #| (Constant.STAGE1_SH Constant.OUTER_SHAREABLE)
                                            #| (Constant.STAGE1_AP Constant.STAGE1_READWRITE)
                                            #| (Constant.STAGE1_ATTRINDX Constant.STAGE1_DEVICEINDX)) #;
               Put "arch_mm_mode_to_stage1_attrs" 
               (Call "ARCHMM.arch_mm_mode_to_stage1_attrs" [CBV mode]) #;
               Put "arch_mm_mode_to_stage1_attrs valid check" attrs #;
               mode #= (Int64.repr 0) #;
               attrs #= (Constant.STAGE1_AF #| (Constant.STAGE1_SH Constant.OUTER_SHAREABLE)
                                            #| Constant.STAGE1_XN                                            
                                            #| (Constant.STAGE1_AP Constant.STAGE1_READONLY)
                                            #| (Constant.STAGE1_ATTRINDX Constant.STAGE1_NORMALINDX)
                                            #| (Constant.PTE_VALID)) #;
               Put "arch_mm_mode_to_stage1_attrs" 
               (Call "ARCHMM.arch_mm_mode_to_stage1_attrs" [CBV mode]) #;
               Put "arch_mm_mode_to_stage1_attrs valid check" attrs #;
               
               Put "Calling ARCHMM.arch_mm_mode_to_stage2_attrs" (Vnull) #;
               mode #= (Constant.MM_MODE_R #| Constant.MM_MODE_W #|
                                           MM_MODE_UNOWNED #| MM_MODE_SHARED #| MM_MODE_INVALID) #;
               access #= (access #| Constant.STAGE2_ACCESS_READ #| Constant.STAGE2_ACCESS_WRITE) #;
               attrs #=  (Constant.STAGE2_AF #| (Constant.STAGE2_SH Constant.NON_SHAREABLE)
                                             #| (Constant.STAGE2_S2AP_DSL access)
                                             #| (Constant.STAGE2_XN Constant.STAGE2_EXECUTE_NONE)
                                             #| (Constant.STAGE2_MEMATTR Constant.STAGE2_WRITEBACK
                                                                         Constant.STAGE2_WRITEBACK)) #;
               Put "arch_mm_mode_to_stage2_attrs" 
               (Call "ARCHMM.arch_mm_mode_to_stage2_attrs" [CBV mode]) #;
               Put "arch_mm_mode_to_stage2_attrs valid check" attrs #;

               Put "Calling ARCHMM.arch_mm_stage2_attrs_to_mode" (Vnull) #;

               mode #= (Constant.MM_MODE_R) #;
               
               Put "arch_mm_stage2_attrs_to_mode"
               (Call "ARCHMM.arch_mm_stage2_attrs_to_mode"
                     [CBV (Call "ARCHMM.arch_mm_mode_to_stage2_attrs" [CBV mode])]) #;
               Put "arch_mm_stage2_attr_to_mode valid check" mode #;
               
               
               mode #= (Constant.MM_MODE_R #| Constant.MM_MODE_W #|
                                           MM_MODE_UNOWNED #| MM_MODE_SHARED #| MM_MODE_INVALID) #;
               
               Put "arch_mm_stage2_attrs_to_mode"
               (Call "ARCHMM.arch_mm_stage2_attrs_to_mode"
                     [CBV (Call "ARCHMM.arch_mm_mode_to_stage2_attrs" [CBV mode])]) #;
               Put "arch_mm_stage2_attr_to_mode valid check" mode #;

               Put "auxiliary functions" (Vnull) #;
               Put "arch_mm_stage1_max_level" (Call "ARCHMM.arch_mm_stage1_max_level" []) #;
               Put "arch_mm_stage2_max_level" (Call "ARCHMM.arch_mm_stage2_max_level" []) #;
               Put "arch_mm_stage1_root_table_count" (Call "ARCHMM.arch_mm_stage1_root_table_count" []) #;
               Put "arch_mm_stage2_root_table_count" (Call "ARCHMM.arch_mm_stage2_root_table_count" []) #;
               
               Put "Calling ARCHMM.arch_mm_mode_to_stage2_attrs" (Vnull) #;
               block_attrs #= (Constant.STAGE1_AF #| (Constant.STAGE1_SH Constant.OUTER_SHAREABLE)
                                                  #| Constant.STAGE1_XN
                                                  #| (Constant.STAGE1_AP Constant.STAGE1_READONLY)
                                                  #| (Constant.STAGE1_ATTRINDX
                                                        Constant.STAGE1_NORMALINDX)
                                                  #| (Constant.PTE_VALID)) #;
               
               table_attrs #= (Constant.TABLE_NSTABLE #| Constant.TABLE_APTABLE1
                                                      #| Constant.TABLE_APTABLE0
                                                      #| Constant.TABLE_XNTABLE
                                                      #| Constant.TABLE_PXNTABLE) #;
                Put "arch_mm_combine_table_entry_attrs"
                (Call "ARCHMM.arch_mm_combine_table_entry_attrs" [CBV table_attrs; CBV block_attrs]) #;
                block_attrs #= (block_attrs #| Constant.STAGE1_NS
                                              #| Constant.STAGE1_AP2
                                              #& (Not Constant.STAGE1_AP1)
                                              #| Constant.STAGE1_XN #| Constant.STAGE1_PXN) #;
                Put "arch_mm_combine_table_entry_attrs valid check" block_attrs #;
                block_attrs #= (Constant.STAGE1_AF #| (Constant.STAGE1_SH Constant.OUTER_SHAREABLE)
                                                   #| Constant.STAGE1_XN
                                                   #| (Constant.STAGE1_AP Constant.STAGE1_READONLY)
                                                   #| (Constant.STAGE1_ATTRINDX
                                                         Constant.STAGE1_NORMALINDX)
                                                   #| (Constant.PTE_VALID)) #;
                
                table_attrs #= (Constant.TABLE_NSTABLE #| Constant.TABLE_APTABLE1
                                                       #| Constant.TABLE_APTABLE0 
                                                       #| Constant.TABLE_XNTABLE
                                                       #| Constant.TABLE_PXNTABLE) #;
                Put "arch_mm_combine_table_entry_attrs"
                (Call "ARCHMM.arch_mm_combine_table_entry_attrs" [CBV table_attrs; CBV block_attrs]) #;
                block_attrs #= (block_attrs #| Constant.STAGE1_NS
                                              #| Constant.STAGE1_AP2
                                              #| Constant.STAGE1_XN #| Constant.STAGE1_PXN) #;    
                Put "arch_mm_combine_table_entry_attrs valid check" block_attrs.


    Definition mainF: function.
      mk_function_tac main ([]: list var) ["address1"; "address2"; "stage2_sw_owned"; "pte_valid_val";
                                           "pte_table_val"; "mode"; "attrs"; "access";
                                           "block_attrs"; "table_attrs"].
    Defined.
    
    Definition main_program: program :=
      [
        ("main", mainF)
      ].

    Definition isem1: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMM.arch_mm_modsem ; ADDR.addr_modsem].
    
    Definition isem2: itree Event unit :=
      eval_multimodule [program_to_ModSem main_program ; ArchMMHighSpec.arch_mm_modsem].
   
  End ARCHMMPARTIALTEST.

End ArchMMTEST.

