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

(** * Formalizations on FFA Memory Management Interfaces *)

(** This work formalizes memroy management interfaces described in 
    Arm Firmware Framework for Armv8-A 
    (https://developer.arm.com/documentation/den0077/latest). 
    The following files are relavant to this formalization.


   - [FFAMemoryHypCallIntro.v]
     - This file introduces several relavant concepts that are necessary in the FF-A memory 
       management interface formalization (e.g., FFA version number, identifiers in FFA)
   - [FFAMemoryHypCallDescriptorState.v]
     - This file introduces formal definitions of descriptor data structures. 
       They are related to Sections 5.10, 5.11, and 5.12 in the document. 
   - [FFAMemoryHypCallState.v]
     - This file introduces abstract states of our formalizations.
   - [FFAMemoryHypCallCoreTransition.v]
     - This file contains core transition rules of FFA memory management interfaces. 
       They changes ownership and accessibility information of the adress that interfaces
       want to handle. The relevant parts in the document with this file are Chapters 5 and 11. 
   - [FFAMemoryHypCallTransition.v]
     - This file contains the full transition rules of FFA memory management interfaces.
       Those transition rules can be treated as wrappers of core transition rules in
       [FFAMemoryHypCallCoreTransition.v] by adding several safety checks and/or 
       invariants that the document contains.
   - [FFAMemoryHypCallWellFormedProof.v]
     - This file contains the safety proof of our specifications, especially 
       proofs related to [well-formedness] conditions that FFA memory management 
       transitions have to preserve (e.g., safety of memory ownership and accessibility) 
*)
