(*
 * Copyright 2020 Youngju Song
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
Require Extraction.

(* From HafniumCore *)
(* YJ: Having some makefile problem. (dependency checking) need to solve that !! *)
Require Import Lang LangTest BinaryString.
(* Require Import MpoolSeq MpoolConcur CPUSeq MM MMStageOne MMHighStageOne. *)
Require Import Lock Mpool MpoolTest MemoryManagement MemoryManagementTest ArchMMTest FFAMemoryHypCallTesting.

Require Import
        ExtrOcamlBasic
        ExtrOcamlString.
        (* ExtrOcamlZInt. *)
(* Require Import ExtrOcamlNatInt. *)

(* Avoid name clashes *)
Extraction Blacklist List String Int.

Require Import Toy.

Cd "extract".

(*** TODO: I just want to write as below, but it does NOT work!!!!! ***)
(* Separate Extraction MpoolSeq MpoolConcur Lang LangTest. *)

Separate Extraction
         BinaryString
         Any.string_of_Any
         Lang.eval_whole_program
         Lang.eval_single_program
         Values.Vtrue
         Values.Vfalse
         LangTest.IntPtr.program
         LangTest.LoadStore.program
         LangTest.CBVCBR.program
         LangTest.Rec.program
         LangTest.MutRec.program
         LangTest.Move.program
         LangTest.CoqCode.program
         LangTest.CoqCodeCBR.isem
         LangTest.Control.program
         LangTest.DoubleReturn.program
         LangTest.MultiCore.programs
         LangTest.MultiCore2.sem
         LangTest.MultiCoreMPSC.sem
         LangTest.MultiModule.isem
         LangTest.MultiModuleGenv.isem
         LangTest.MultiModuleLocalState.isem
         LangTest.MultiModuleLocalStateSimple.isem1
         LangTest.MultiModuleLocalStateSimple.isem2
         LangTest.MultiModuleLocalStateSimpleLang.isem
         LangTest.MultiModuleMultiCore.sem
         LangTest.MultiModuleMultiCoreLocalState.isem
         LangTest.PrintAny.isem
         LangTest.PrintTest.string_gen
         LangTest.PrintTest.z_gen
         LangTest.PrintTest.Z_to_string_gen
         LangTest.HexPrintTest.string_gen
         LangTest.HexPrintTest.z_gen
         LangTest.HexPrintTest.Z_to_string_gen
         (* LangTest.print_val *)
         (* LangTest.main *)
         (* LangTest.handle_Event *)
         (* LangTest.cl2s *)

         MpoolTest.MPOOLTEST.MPOOLTEST_ONE.isem1
         MpoolTest.MPOOLTEST.MPOOLTEST_TWO.isem1
         MpoolTest.MPOOLTEST.MPOOLTEST_THREE.isem1
         MpoolTest.MPOOLTEST.MPOOLTEST_FOUR.isem1
         MpoolTest.MPOOLTEST.MPOOLTEST_FIVE.isem1
         MpoolTest.MPOOLTEST.MPOOLTEST_ONE.isem2
         MpoolTest.MPOOLTEST.MPOOLTEST_TWO.isem2
         MpoolTest.MPOOLTEST.MPOOLTEST_THREE.isem2
         MpoolTest.MPOOLTEST.MPOOLTEST_FOUR.isem2
         MpoolTest.MPOOLTEST.MPOOLTEST_FIVE.isem2
         (* MpoolSeq.TEST.TEST1.program *)
         (* MpoolSeq.TEST.TEST2.program *)
         (* MpoolSeq.TEST.TEST3.program *)
         (* MpoolSeq.TEST.TEST4.program *)

         (* MpoolConcur.TEST.TEST1.isem *)
         (* MpoolConcur.TEST.TEST2.isem *)
         (* MpoolConcur.TEST.TEST3.isem1 *)
         (* MpoolConcur.TEST.TEST3.isem2 *)
         (* MpoolConcur.TEST.TEST4.isem *)

         (* CPUSeq.CPUTEST.program *)

         ArchMMTest.ArchMMTEST.ARCHMMFULLTEST.isem1
         ArchMMTest.ArchMMTEST.ARCHMMPARTIALTEST.isem1
         ArchMMTest.ArchMMTEST.ARCHMMPARTIALTEST.isem2
         
         MemoryManagementTest.MMTEST.PageTableFromPa.isem
         MemoryManagementTest.MMTEST.PaStartOfNextBlk.isem
         MemoryManagementTest.MMTEST.MaxLv.isem
         MemoryManagementTest.MMTEST.RootTableCount.isem
         MemoryManagementTest.MMTEST.TLBI.isem
         MemoryManagementTest.MMTEST.INIT.isem
         MemoryManagementTest.MMTEST.INITFINI.isem
         MemoryManagementTest.MMTEST.INITFINI.isem2

         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.INITIALIZATION.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.DUMMYTEST1.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.DUMMYTEST2.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.DUMMYTEST3.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.DUMMYTEST4.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.DUMMYTEST5.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.DUMMYTEST6.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.DUMMYTEST7.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.CONTEXTSWITCHINGTEST1.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.DONATETEST1.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.DONATETEST2.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.DONATETEST3.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.DONATETEST4.isem
         FFAMemoryHypCallTesting.FFAMEMORYHYPCALLTESTING.DONATETEST5.isem
         (* MMStageOne.MMTEST1.isem *)
         (* MMStageOne.MMTESTAUX.isem *)
         (* MMStageOne.MMTEST3.isem *)
         (* MMStageOne.POPULATE.isem *)
         
         (* MMHighStageOne.HighSpecDummyTest.program *)
         (* MMHighStageOne.PTHIGHTEST.isem *)
         
         Lang.round_robin
         Lang.run_till_yield
         Lang.my_rr_match
         
         ITreeDefinition.observe

         Toy.FACTTEST.isem1
         Toy.FACTTEST.isem2
         Toy.FACTTEST.isem3
.

Cd "..".
