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


(** * FFAMemoryHypCallIntro

   This file does not have any Coq definitions, but it is an intro of other files that are related 
   to FFA Section 5 formalization. 
   - FFAMemoryHypCallDescriptorState.v
   - FFAMemoryHypCallState.v
   - FFAMemoryHypCallAuxFunctions.v
   - FFAMemoryHypCall.v

   The following explanations are mostly copied from the FF-A document. If there are something that we hope to mention, 
   we add [...] to distinguish them with the original texts.
*)

Section BasicConcepts.

  (** This section provides several basic concepts that are necessary to model FFA memory management interfaces *) 
  
  (** * FFA Version number - Parts of 8.1 FFA_VERSION

    The version number of a Firmware Framework implementation is a 31-bit unsigned integer, 
    with the upper 15 bits denoting the major revision, and the lower 16 bits denoting the minor revision.

    With the given version number, the following two rules has to be satisfied.
    - All the functions that are described in this specification must be implemented, 
      unless it is explicitly stated that a function is optional.
    - A partition manager could implement an optional interface and make it available to a subset of 
      endpoints it manages.

    The following rules apply to the version numbering.
    - Different major revision values indicate possibly incompatible functions.
    - For two revisions, A and B, for which the major revision values are identical, 
      if the minor revision value of revision B is greater than the minor revision value of revision A, 
      then every function in revision A must work in a compatible way with revision B. 
      However, it is possible for revision B to have a higher function count than revision A.
      In an invocation of this function, the compatibility of the version number (x.y) of the caller with the 
      version number (a.b) of the callee can also be as follows.
      1. If x != a, then the versions are incompatible.
      - The caller cannot inter-operate with the callee.
      2. If x == a and y > b, then the versions are incompatible.
      - The caller can inter-operate with the callee only if it downgrades its minor revision such that y <= b.
      3. If x == a and y <= b, then the versions are compatible. A version number (x.y) is less than a version 
         number (a.b) if one of the following conditions is true.
      - x < a.
      - y < b if x == a.
   *)

  (** * 2.3 FF-A instances 

     An FF-A instance is a valid combination of two FF-A components at an Exception level boundary. These instances
     are used to describe the interfaces specified by the Firmware Framework.

     An instance is physical if:
     – Each component can independently manage its translation regime.
     – The translation regimes of each component map virtual addresses to physical addresses.
       * An instance is virtual if it is not physical.
       * The instance between the SPMC and SPMD is called the Secure physical FF-A instance.
       * The instance between the SPMC and an SP is called the Secure virtual FF-A instance.
       * In the Normal world, the instance between:
     – The Hypervisor and a VM is called the Non-secure virtual FF-A instance.
     – The Hypervisor and SPMD is called the Non-secure physical FF-A instance.
     – The OS kernel and SPMD, in the absence of a Hypervisor is called the Non-secure physical FF-A instance.
   *)
  
  (** * 2.6 Memory types 

     [JIEUNG: Based on the following descriptions, a NS attribute bit for each page is required in our abstract definition.]
    
     Each memory region is assigned to either the Secure or Non-secure physical address space at system 
     reset or during system boot. Normal world can only access memory regions in the Non-secure physical 
     address space. Secure world can access memory regions in both address spaces. 

     The Non-secure (NS) attribute bit in the translation table descriptor determines whether an access 
     is to Secure or Non-secure memory. In this version of the Framework:
     - Memory that is accessed with the NS bit set in the translation regime of any component 
       is called Normal memory.
     - Memory that is accessed with the NS bit cleared in the component translation regime is called Secure memory.
   *)

  (** * 2.7 Memory granularity and alignment 

     [JIEUNG: Similar to the following description. we can introduce a context variable that represents arbitrary 
     number. And based on that, expressing several invariants are also possible.]

    - If X is the larger translation granule size used by the two translation regimes, 
      then the size of the memory region must be a multiple of X.
    - The base address of the memory region must be aligned to X.
    
    An endpoint could specify its translation granule size in its partition manifest as described in 3.2 Partition manifest
    at virtual FF-A instance. 
   *)

  (** * 2.8. Partition identification and discovery 
 
     [JIEUNG: This section describes identifiers for each entity. Entities can be divided into sub types, such as 
      SEPID, VM ID, and so on.]

     Partitions are identified by a 16-bit ID and a UUID (Unique Universal Identifier) (see [6]). This helps partitions
     discover the presence of other partitions and their properties. A unique ID must be assigned to each partition in the system. 
     The id value 0 is reserved for the Hypervisor as described in. The id value assigned to the SPM is IMPLEMENTATION DEFINED.
   *)

  (** * 2.9. Execution Context 
     Each endpoint has one or more execution contexts depending on its implementation. An execution context
     comprises of general-purpose, system, and any memory mapped register state that must be maintained by a
     partition manager.
     A partition manager is responsible for allocating, initializing, and running the execution context of an endpoint on
     a physical or virtual PE in the system. An execution context is identified by using a 16-bit ID. This ID is referred
     to as the vCPU or execution context ID.
     
     An endpoint must be one of the following types:
     - Implements a single execution context and is not capable of Symmetric multi-processing. It runs only on a
       single PE in the system at any point of time. This type of endpoint is called a UP endpoint.
     - Implements multiple execution contexts and is capable of Symmetric multi-processing. These contexts run
       concurrently on separate PEs in the system. These endpoints are called MP endpoints.
       An execution context of an endpoint could be capable of migrating. Migration capability means that the partition
       manager could save the execution context of an endpoint on one PE. It could then restore the saved execution
       context on another PE and resume endpoint execution. The endpoint must not make any assumptions about the PE
       it runs on.

     [JIEUNG: the following requirements need to be reflected in our specifications, but we currently don't need to 
      deal with them]
     This version of the Framework requires the following:
     - UP endpoints must be capable of migrating.
     - Execution contexts of MP endpoints could be capable of migrating between PEs or could be fixed to a
       particular PE. The latter are called pinned contexts.
     - The migration capability must be specified in the endpoint manifest (see 3.2 Partition manifest at virtual
       FF-A instance).
     - S-EL0 partitions must be UP.
       The number of execution contexts an endpoint implements can differ from the number of PEs in the system. This
       must be specified in the manifest of the endpoint (see 2.10 System resource management). For example, a VM in
       the Normal world must use the manifest to inform the Hypervisor how many vCPUs it implements. The Hypervisor
       must maintain an execution context for each vCPU. 
   *)

  (** * 2.10 System resource management
 
      [JIEUNG: Among them, "memory regions" and "devices" are closely related to our draft. 
      But, among two things, we only focus on "memory regions" parts. Our draft excludes memory management
      interface transitions for device related parts (SMMU, MMIO, independent peripheral and dependent peripheral).
      Even though we ignore them, our memory attributes divides memory into normal and device memories for the future
      extension and basic separations between normal memory and device memories 
  
     Components in the Firmware Framework require access to the following system resources.
     - Memory regions.
     - Devices.
     - CPU cycles.
     
     The Framework associates the attributes of ownership and access with these resources. The Owner governs the
     following capabilities of non-Owners for each resource.
     - The level of access a non-Owner has for using the resource. This could be exclusive, shared or no-access.
     - The ability to grant access to the resource to other non-Owners. This is called access forwarding.
     
     Also, the Owner could relinquish ownership to another component.
     The Framework also specifies the transitions that result in a change of ownership and access attributes associated
     with a resource. A combination of these attributes and transitions determines how a resource is managed among
     components.
     
     Rules associated with ownership and access of memory regions are described in Chapter 5 Memory Management.
     Rules associated with ownership and access of CPU cycles are described in 2.11 Primary scheduler.
     For a device that is upstream of an SMMU, its access to the physical address space is managed using the rules
     associated with management of memory regions (also see 5.2 Direct memory access).
     For all devices, ownership and access attributes are associated with its MMIO region. A partition could request
     access and/or ownership of a device through its manifest (see Table 3.3). This is done through one of the following
     ways.
     - A partition requests ownership and exclusive access to the MMIO region of a device during boot time
       (see Chapter 3 Partition setup). The corresponding partition manager assigns the MMIO region with these
       attributes to the partition.
     - One or more partitions request access to the MMIO region of a device during boot time. The corresponding
       partition manager is the Owner of the MMIO region and grants access to all the partitions.

     [JIEUNG: the following requirements need to be reflected in our specifications, but we currently don't need to 
      deal with them]     
     This version of the Framework does not permit:
     - Ownership of a device MMIO region to be transferred to another partition during run-time.
     - Access to a device MMIO region to be granted to another partition during run-time.
     - Access to a device MMIO region to be revoked from a partition during run-time.
   *)

  (** * 3. Partition setup 

     [JIEUNG: Section 3 provides multiple details about how we can set up and which information has to be stored (or required) 
      for each partition. We try to include simple details about them here 

     The following information must be specified in the manifest of a partition.
     - Partition properties as described in Table 3.1.
     - Memory regions as described in Table 3.2.
     - Devices as described in Table 3.3.
     - Partition boot protocol as described in Table 3.10.
     
     [JIEUNG: Among the entire things, we focus on Table 3.2. and Table 3.3. 
     The following parts need to be reflected in our state definition, but with some modifications.
     For example. we model that each page in the entire memory has its own ownership, accessibility, and attributes. 
     If they are in the same region, our spec requires sonsistency check. The check is basically figure out whether
     the entire pages in the region have the same attributes or not.]
     
     Table 3.2: Memory regions

     Information fields        Mandatory  Description
     Base address              No         - Absence of this field indicates that a memory region of specified size and attributes 
                                            must be mapped into the partition translation regime. 
                                          - If present, this field could specify a PA, VA (for S-EL0 partitions) or IPA
                                            (for S-EL1 and EL1 partitions). 
                                            * If a PA is specified, then the memory region must be identity mapped
                                              with the same IPA or VA as the PA.
                                            * If a VA or IPA is specified, then the memory could be identity or non-identity mapped.
                                          - If present, the address must be aligned to the Translation granule size.
     Page count                Yes        - Size of memory region expressed as a count of 4K pages.
                                          - For example, if the memory region size is 16K, value of this field is 4.
     Attributes                Yes        - Memory access permissions.
                                            * Instruction access permission.
                                            * Data access permission.
                                          - Memory region attributes.
                                            * Memory type.
                                            * Shareability attributes.
                                            * Cacheability attributes.
                                          - Memory Security state.
                                            * Non-secure for a NS-Endpoint.
                                            * Non-secure or Secure for an S-Endpoint.
     Name                      No         - Name of the memory region for example, for debugging purposes

     Table 3.3: Device regions
     Information fields        Mandatory  Description
     Physical base address     Yes        - PA of base of a device MMIO region.
                                          - If the MMIO region is not physically contiguous, then an entry for each
                                            physically contiguous constituent region must be specified.
                                          - Each entry must specify the PA and size of the constituent region. The size
                                            must be expressed as a count of 4K pages.
     Page count                Yes        - Total size of MMIO region expressed as a count of 4K pages.
                                          - For example, if the MMIO region size is 16K, value of this field is 4.
     Attributes                Yes        - Memory attributes must be Device-nGnRnE.
                                          - Instruction access permission must be not executable.
                                          - Data access permissions must be one of the following:
                                            * Read/write.
                                            * Read-only.
                                          - Security attributes must be:
                                            * Non-secure for a NS-Endpoint.
                                            * Non-secure or Secure for an S-Endpoint.
     Interrupts                No         - List of physical interrupt IDs.
                                          - Attributes of each interrupt ID.
                                            * Interrupt type: SPI / PPI / SGI
                                            * Interrupt configuration: Edge triggered /  Level triggered
                                            * Interrupt Security state: Secure /  Non-secure.
                                            * Interrupt priority value.
                                            * Target execution context/vCPU for each SPI:  This field is optional even if other 
                                              interrupt properties are specified 
     SMMU ID                   No         - If present, then on a system with multiple SMMUs, this field must help the partition 
                                            manager determine which SMMU instance is this device upstream of.
                                          - Absence of this field implies that the device is not upstream of an SMMU.
     Stream IDs                No         - List of Stream IDs assigned to this device.
                                          - Absence of Stream ID list indicates that the device is not upstream of an SMMU.
     Exclusive access          No         - If present, this field implies that this endpoint must be granted exclusive
     and ownership                          access and ownership of the MMIO region of the device.
                                          - Absence of this field implies that access to the MMIO region of the device
                                            could be shared among multiple endpoints.
     Name                      No         - Name of the device region for example, for debugging purposes.
*)

End BasicConcepts.

(** * 5. Memory Management *)
Section MemoryManagementIntro. 

  Section Overview.
  (** * 5.1 Overview

    FF-A components to manage access and ownership of memory regions in the physical address space 
     to fulfill use cases such as:
     - DRM protected video path.
     - Communication with a VM with pre-configured machine learning frameworks,
       - Biometric authentication and Secure payments.
       
     There are several possible scenarios:
     1. The Owner of a memory region can transfer its ownership to another FF-A component.
     2. The Owner of a memory region can relinquish access to it and grant access to one 
     or more FF-A components.
     3. The Owner of a memory region can share access to it with one or more FF-A components.
     4. The Owner of a memory region can reclaim access to it by requesting FF-A components 
     to relinquish access to the memory region.
   *)

  End Overview.

  Section DirectMemoryAccess.
    (** * 5.2 Direct memory access

       [JIEUNG: At this moment, we ignore the following parts].
       
       In this section, and the folloiwng related parts, this document describes memory managements
       for device related memory regions. However, most of them will be ignored in our draft. We do not 
       include Stream ID, SEPID, ownership transfers, and access controls when the page region is related 
       to the direct access on devices. 
       
       This implies that we try to focus on communications between two PEs. In addition that, we try to
       ignore other FFA interfaces. For example, our modeling is related to getting a ID for each PE by
       using "FFA_ID_GET". However, we will ignore that in our current version 
      
       The Framework enables FF-A components to manage access to the physical address space from a device 
       that is upstream of an SMMU using the memory management transactions described in 5.5 Memory 
       management transactions *)
    
  End DirectMemoryAccess.

  Section AddressTranslationRegimes.
    (** * 5.3 Address translation regimes 

        [JIEUNG: This part mentions about address translation. It will be hidden in our address translation abstract definition.
        However, we can make some high-level invariants for this address translations]

       Memory management relies on the two fundamental operations of mapping and un-mapping a memory region
       from the stage of a translation regime managed by a partition manager on behalf of a partition. The translation
       regime and the stage depends on the type of partition. The types of partitions are as follows.

       1. Hypervisor, stage 2 translations on behalf of a EL1 PE endpoint, 
          in the Non-secure EL1&0 translation regime, when EL2 is enabled
       2. Hypervisor, stage 2 translations for a Non-secure Stream ID assigned to an
          independent or dependent peripheral device, in the Non-secure EL1&0 translation regime in the SMMU. 
          A SEPID is used to identify the stage 2 translation tables
       3. SPMC, stage 2 translations on behalf of a S-EL1 PE endpoint in the Secure EL1&0 translation regime, 
          when S-EL2 is enabled.
       4. SPMC, stage 1 translations on behalf of a S-EL0 PE endpoint in the Secure EL1&0 translation regime, 
          when S-EL2 is disabled.
       5. SPMC, stage 2 translations for a Secure Stream ID assigned to an independent or dependent peripheral device in 
          the Secure EL1&0 translation regime in the SMMU. A SEPID is used to identify the stage 2 translation tables. *)
    
  End AddressTranslationRegimes.

  Section OwnershipAndAccessAttributes.
  (** * 5.4 Ownership and access attributes 

     [JIEUNG: This section is one of the most important section to provides abstract view of memory ownership and 
     attributes. And, descriptions in this section has to be reflected in our formalized version. Please look at the MemProperties 
     definition (MemProperties) and valid_combination definitions (mem_states_valid_combination)]

    The Hypervisor, SPM, and all endpoints have access and ownership attributes associated with every memory region in the 
    physical ddress space. Access determines the data and instruction access permissions to the memory region. 
    A component can have the following access permissions to a memory region.
    • No access.
    • Read-only, Execute-never.
    • Read-only, Executable.
    • Read/write, Execute-never.

    Ownership is a software attribute that determines if a component can grant access to a memory region to another
    component. A component that has access to a memory region without ownership is called the Borrower. A
    component that lends access to a memory region it owns is called the Lender.
   *)
    
  End OwnershipAndAccessAttributes.

  Section RemainingParts.

    (** * Remaining parts 
        
       [JIEUNG: From 5.5 to the end of Section 5., and for the details in Section 11, we write comments 
       on our mechanized versions.]
     *)
    
  End RemainingParts.
  
End MemoryManagementIntro.

