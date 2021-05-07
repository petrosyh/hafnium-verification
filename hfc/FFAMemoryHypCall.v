(** * Formalizations on FFA Memory Management Interfaces *)


(** This work formalizes memory management interfaces described in Arm Firmware
    Framework for Armv8-A (https://developer.arm.com/documentation/den0077/a/). The
    following files are relevant to this formalization.

- [FFAMemoryHypCallIntro.v]
  - Concepts that are closely related to the FF-A
    memory management interface. 
  - Other files that contain formal definitions rely on concepts that this file describes.
    Therefore, looking at this file may help readers understand our formal definitions. 

- [FFAMemoryHypCallDescriptorState.v]
  - Formal definitions of descriptor data structures defined in
    Sections 5.10, 5.11, and 5.12 of the FF-A document. 
    Those descriptors contain information that
    memory management hypervisor calls have to look at during their evaluation.

- [FFAMemoryHypCallState.v]
  - Abstract state definition, the mathematical view of
    the entire system, hiding unnecessary details.

- [FFAMemoryHypCallCoreTransition.v]
  - Core transition rules of the FF-A memory management interfaces.
    Those transition rules change ownership and accessibility information
    of the memory address that interfaces want to handle.

- [FFAMemoryHypCallAdditionalStepsAuxiliaryFunctions.v]
  - Auxiliary functions that make the specifications more readable
    and structured.

- [FFAMemoryHypCallAdditionalSteps.v]
  - Transition rules in this file can be treated as wrappers of core transition rules
    by adding several safety checks and/or invariants that the document contains.
  - The relevant parts in the FF-A document are Chapters 5 and 11.

- [FFAMemoryHypCallTestingInterface.v]
   - Testing interfaces (e.g., context switching, dispatch, and so on).

- [FFAMemoryHypCallTesting.v]
  - Test cases.

- [FFAMemoryHypCallWellFormedProof.v]
  - Safety proof of our specifications, especially proofs
    related to well-formedness conditions that FFA memory management
    transitions have to preserve (e.g., safety of memory ownership and
    accessibility).
*)

