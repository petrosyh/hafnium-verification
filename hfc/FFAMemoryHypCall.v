(** * Formalizations on FFA Memory Management Interfaces *)


(** This work formalizes memroy management interfaces described in Arm Firmware
    Framework for Armv8-A (https://developer.arm.com/documentation/den0077/latest). The
    following files are relavant to this formalization. 

- [FFAMemoryHypCallIntro.v]
  - This file introduces several concepts that are closely related to the FF-A
    memory management interface. 
    Other files that contain formal definitions rely on concepts that this file describes. 
    Therefore, looking at this file may help readers understand our formal definitions. 

- [FFAMemoryHypCallDescriptorState.v]
  - This file contains formal definitions of descriptor data structures defined in
    Sections 5.10, 5.11, and 5.12 of the FF-A document. 
    Those descriptors contain several information that 
    memory management hypervisor calls have to look at during its evaluations.

- [FFAMemoryHypCallState.v]
  - This file introduces the abstract state definition, the mathematical view of 
    the entire system with hiding unnecessary details. 

- [FFAMemoryHypCallCoreTransition.v]
  - This file contains core transition rules of FFA memory management interfaces. 
  - Core transition rules in this file change ownership and accessibility information 
    of the memory adress that interfaces want to handle.

- [FFAMemoryHypCallAdditionalStepsAuxiliaryFunctions.v]
  - Auxiliary functions that makes the entire specifications more readable 
    and structured.

- [FFAMemoryHypCallAdditionalSteps.v]
  - Transition rules in this file can be treated as wrappers of core transition rules
    by adding several safety checks and/or invariants that the document contains.
  - The relevant parts in the FF-A document are Chapters 5 and 11.

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

