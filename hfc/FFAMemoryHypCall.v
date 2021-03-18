(** * Formalizations on FFA Memory Management Interfaces *)


(** This work formalizes memroy management interfaces described in Arm Firmware
    Framework for Armv8-A (https://developer.arm.com/documentation/den0077/latest). The
    following files are relavant to this formalization. 

- [FFAMemoryHypCallIntro.v]
  - This file introduces several relavant concepts that are necessary in the FF-A
    memory management interface formalization (e.g., FFA version number, identifiers in FFA) 
- [FFAMemoryHypCallDescriptorState.v]
  - This file introduces formal definitions of descriptor data structures. They are 
    related to Sections 5.10, 5.11, and 5.12 in the document.
- [FFAMemoryHypCallState.v]
  - This file introduces abstract states of our formalizations.
- [FFAMemoryHypCallCoreTransition.v]
  - This file contains transition rules of FFA memory management interfaces. 
  - Core transition rules in this file change ownership and accessibility information of the memory adress 
    that interfaces want to handle.
- [FFAMemoryHypCallAdditionalStepsAuxiliaryFunctions.v]
- [FFAMemoryHypCallAdditionalSteps.v]
  - Other transition rules can be treated as wrappers of core transition rules
    by adding several safety checks and/or invariants that the document contains.
  - The relevant parts with this file in the FF-A document are Chapters 5 and 11.
- [FFAMemoryHypCallTestingInterface.v]
  - This file provides testing interfaces (e.g., context switchings, dispatch, and so on).
- [FFAMemoryHypCallTesting.v]
  - This file provides test cases.
- [FFAMemoryHypCallWellFormedProof.v]
  - This file contains the safety proof of our specifications, especially proofs
    related to well-formedness conditions that FFA memory management
    transitions have to preserve (e.g., safety of memory ownership and
    accessibility).
*)

