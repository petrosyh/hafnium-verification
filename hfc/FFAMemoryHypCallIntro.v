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

Require Import FFAMemoryHypCall.


(** * Introduction *)

(**
   This file introduces several relavant concepts that are necessary in the FF-A memory 
   management interface formalization. Those things include "FFA version number", "FF-A instances", 
   "Memory types", "Memory granularity and alignment", "Partition identification and discovery", "execution context",
   "System resource management", "Partition setup", and "FFA memory management interface introduction". 
   
   With the given descriptions, we formalize our target with the following four files. 

   The following explanations are mostly copied from the FF-A document. If there are something that we hope to mention, 
   we add [JIEUNG:...] to distinguish them with the original texts.
*)

Section BasicConcepts.

  (** This section provides several basic concepts that are necessary to model FFA memory management interfaces *) 
  
  (** ** FFA Version number - Parts of Section 8.1

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

  (** ** FF-A instances - Parts of Section 2.3

     An FF-A instance is a valid combination of two FF-A components at an Exception level boundary. These instances
     are used to describe the interfaces specified by the Firmware Framework.

     An instance is physical if:
     – Each component can independently manage its translation regime.
     – The translation regimes of each component map virtual addresses to physical addresses.
       - An instance is virtual if it is not physical.
       - The instance between the SPMC and SPMD is called the Secure physical FF-A instance.
       - The instance between the SPMC and an SP is called the Secure virtual FF-A instance.
       - In the Normal world, the instance between:
     – The Hypervisor and a VM is called the Non-secure virtual FF-A instance.
     – The Hypervisor and SPMD is called the Non-secure physical FF-A instance.
     – The OS kernel and SPMD, in the absence of a Hypervisor is called the Non-secure physical FF-A instance.
   *)
  
  (** ** Memory types - Parts of Section 2.6

     [JIEUNG: Based on the following descriptions, a NS attribute bit for each page is required 
     in our abstract definition.]
    
     Each memory region is assigned to either the Secure or Non-secure physical address space at system 
     reset or during system boot. Normal world can only access memory regions in the Non-secure physical 
     address space. Secure world can access memory regions in both address spaces. 

     The Non-secure (NS) attribute bit in the translation table descriptor determines whether an access 
     is to Secure or Non-secure memory. In this version of the Framework:
     - Memory that is accessed with the NS bit set in the translation regime of any component 
       is called Normal memory.
     - Memory that is accessed with the NS bit cleared in the component translation regime is called Secure memory.
   *)

  (** ** Memory granularity and alignment - Parts of Section 2.7

     [JIEUNG: Similar to the following description. we can introduce a context variable that represents
     arbitrary number. And based on that, expressing several invariants are also possible.]

    - If X is the larger translation granule size used by the two translation regimes, 
      then the size of the memory region must be a multiple of X.
    - The base address of the memory region must be aligned to X.
    
    An endpoint could specify its translation granule size in its partition manifest as described
    in 3.2 Partition manifest at virtual FF-A instance. 
   *)

  (** ** Partition identification and discovery - Parts of Section 2.8
 
     [JIEUNG: This section describes identifiers for each entity. Entities can be divided into sub types,
     such as SEPID, VM ID, and so on.]

     Partitions are identified by a 16-bit ID and a UUID (Unique Universal Identifier) (see [6]). This helps partitions
     discover the presence of other partitions and their properties. A unique ID must be assigned to
     each partition in the system. The ID value 0 is reserved for the Hypervisor as described in. 
     The ID value assigned to the SPM is IMPLEMENTATION DEFINED.
   *)

  (** ** Execution Context - Parts of Section 2.9

     Each endpoint has one or more execution contexts depending on its implementation. An execution context
     comprises of general-purpose, system, and any memory mapped register state that must be maintained by a
     partition manager.
     A partition manager is responsible for allocating, initializing, and running the execution
     context of an endpoint on a physical or virtual PE in the system. An execution context is identified 
     by using a 16-bit ID. This ID is referred to as the vCPU or execution context ID.
     
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

  (** ** System resource management - Parts of Section 2.10
 
      [JIEUNG: Among them, "memory regions" and "devices" are closely related to our draft. 
      But, among two things, we only focus on "memory regions" parts. Our draft excludes memory management
      interface transitions for device related parts (SMMU, MMIO, independent peripheral and dependent peripheral).
      Even though we ignore them, our memory attributes divides memory into normal and device
      memories for the future extension]
  
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

  (** ** Partition setup - Parts of Section 3. 

     [JIEUNG: Section 3 provides multiple details about how we can set up and which information has to
     be stored (or required) for each partition. We try to include simple details about them here]

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

     Coq source file contains Table 3.2. and Table 3.3., but they are omitted in the generated file due to 
     format issues *)

  (*
     Table 3.2: Memory regions                                                                                     
     Information fields        Mandatory  Description                                                              
     Base address              No         - Absence of this field indicates that a memory region of                
                                            specified size and attributes                                          
                                            must be mapped into the partition translation regime.                  
                                          - If present, this field could specify a PA, VA                          
                                            (for S-EL0 partitions) or IPA (for S-EL1 and EL1 partitions).          
                                            - If a PA is specified, then the memory region must be identity        
                                              mapped with the same IPA or VA as the PA.                            
                                            - If a VA or IPA is specified, then the memory could be identity       
                                              or non-identity mapped.                                              
                                          - If present, the address must be aligned to the Translation             
                                            granule size.                                                          
     Page count                Yes        - Size of memory region expressed as a count of 4K pages.                
                                          - For example, if the memory region size is 16K, value of                
                                            this field is 4.                                                       
     Attributes                Yes        - Memory access permissions.                                             
                                            - Instruction access permission.                                       
                                            - Data access permission.                                              
                                          - Memory region attributes.                                              
                                            - Memory type.                                                         
                                            - Shareability attributes.                                             
                                            - Cacheability attributes.                                             
                                          - Memory Security state.                                                 
                                            - Non-secure for a NS-Endpoint.                                        
                                            - Non-secure or Secure for an S-Endpoint.                              
     Name                      No         - Name of the memory region for example, for debugging purposes    
     *)
  (*
     Table 3.3: Device regions                                                                                     
     Information fields        Mandatory  Description                                                              
     Physical base address     Yes        - PA of base of a device MMIO region.                                    
                                          - If the MMIO region is not physically contiguous,                       
                                            then an entry for each                                                 
                                            physically contiguous constituent region must be specified.            
                                          - Each entry must specify the PA and size of the constituent region.     
                                            The size must be expressed as a count of 4K pages.                     
     Page count                Yes        - Total size of MMIO region expressed as a count of 4K pages.            
                                          - For example, if the MMIO region size is 16K, value of this field is 4. 
     Attributes                Yes        - Memory attributes must be Device-nGnRnE.                               
                                          - Instruction access permission must be not executable.                  
                                          - Data access permissions must be one of the following:                  
                                            - Read/write.                                                          
                                            - Read-only.                                                           
                                          - Security attributes must be:                                           
                                            - Non-secure for a NS-Endpoint.                                        
                                            - Non-secure or Secure for an S-Endpoint.                              
     Interrupts                No         - List of physical interrupt IDs.                                        
                                          - Attributes of each interrupt ID.                                       
                                            - Interrupt type: SPI / PPI / SGI                                      
                                            - Interrupt configuration: Edge triggered /  Level triggered           
                                            - Interrupt Security state: Secure /  Non-secure.                      
                                            - Interrupt priority value.                                            
                                            - Target execution context/vCPU for each SPI:  This field is           
                                              optional even if other interrupt properties are specified            
     SMMU ID                   No         - If present, then on a system with multiple SMMUs, this field           
                                            must help the partition manager determine which SMMU instance          
                                            is this device upstream of.                                            
                                          - Absence of this field implies that the device is not                   
                                            upstream of an SMMU.                                                   
     Stream IDs                No         - List of Stream IDs assigned to this device.                            
                                          - Absence of Stream ID list indicates that the device                    
                                            is not upstream of an SMMU.                                            
     Exclusive access          No         - If present, this field implies that this endpoint must                 
     and ownership                          be granted exclusive access and ownership of the MMIO region           
                                            of the device.                                                         
                                          - Absence of this field implies that access to the MMIO region           
                                            of the device could be shared among multiple endpoints.                
     Name                      No         - Name of the device region for example, for debugging purposes.         
   *)

End BasicConcepts.


(** * Memory Management - Chapter 5. *)
(** [JIEUNG] For Chapter 5, I copied and pasted all comments 
    even though they are not totally related to our implementation. This is due to 
    I hope to make the following specs as self-contained ones as much as possible.]
*)

Section MemoryManagementIntro. 

  Section Overview.
  (** ** Overview - Section 5.1.

    FF-A components to manage access and ownership of memory regions in the physical address space 
     to fulfill use cases such as:
     - DRM protected video path.
     - Communication with a VM with pre-configured machine learning frameworks,
     - Biometric authentication and Secure payments.
       
     There are several possible scenarios:
     - The Owner of a memory region can transfer its ownership to another FF-A component.
     - The Owner of a memory region can relinquish access to it and grant access to one 
     or more FF-A components.
     - The Owner of a memory region can share access to it with one or more FF-A components.
     - The Owner of a memory region can reclaim access to it by requesting FF-A components 
     to relinquish access to the memory region.
   *)

  End Overview.

  Section DirectMemoryAccess.
    (** ** Direct memory access - Section 5.2.

       [JIEUNG: At this moment, we ignore the following parts
       
       - In this section, and the folloiwng related parts, this document describes memory managements
       for device related memory regions. However, most of them will be ignored in our draft. We do not 
       include Stream ID, SEPID, ownership transfers, and access controls when the page region is related 
       to the direct access on devices. 
       
       - This implies that we try to focus on communications between two PEs. In addition that, we try to
       ignore other FFA interfaces. For example, our modeling is related to getting a ID for each PE by
       using "FFA_ID_GET". However, we will ignore that in our current version]
     *)
    
    (**
       The Framework enables FF-A components to manage access to the physical address space from a device that
       is upstream of an SMMU using the memory management transactions described in 5.5 Memory management
       transactions.

       As per the Arm SMMU architecture, each transaction generated by a device is associated with a Stream ID. 
       This Stream ID could be one of many that a the device is configured to use. A Stream ID is used to 
       determine the stage 1 and stage 2 address translations that must be used for the transaction. It is also 
       possible that one or both stages of translation could be bypassed for a Stream ID in the SMMU.
       
       If enabled, the stage 2 translations corresponding to a Stream ID control access to the physical 
       address space that the device has. A set of stage 2 translation tables could map to one or more 
       Stream IDs. The Framework manages stage 2 translations in the SMMU as described in 5.3 Address 
       translation regimes.

       The Hypervisor programs the SMMU to create and manage the association between 
       a Non-secure Stream ID and the stage 2 translations its transactions must use.

       The SPM programs the SMMU to create and manage the association between a Secure Stream ID and the stage 2
       translations its transactions must use.

       The Framework does not manage the stage 1 translations and their association with Stream IDs in the SMMU on
       behalf of the device. This should be done by an endpoint through an IMPLEMENTATION DEFINED mechanism.
     *)

    (** *** Stream endpoint - Section 5.2.1
        
        A set of SMMU stage 2 translations maintained by a partition manager is called a Stream endpoint. 
        Each Stream endpoint is assigned a 16-bit ID called the Stream endpoint ID or SEPID.

        Stream endpoints associated with a Secure Stream ID are called Secure SEPIDs
        
        Stream endpoints associated with a Non-secure Stream ID are called Non-secure SEPIDs

        Endpoints that run on a PE are referred to as PE endpoints to differentiate them from Stream endpoints. 
        The term endpoint is used when it is not required to distinguish between these types of endpoints.

        There is a 1:N (N >= 1) mapping between a SEPID and Stream IDs assigned to different devices that is, 
        the stage 2 translations corresponding to the SEPID could be shared by one or more Stream IDs.

        SEPIDs are used in memory management transactions to:
        - Grant and revoke access to a physical memory region to a device.
        - Transfer ownership of a physical memory region from or to a device

        SEPID values must be distinct from those assigned to PE endpoints. 
        A SEPID is not discoverable through the FFA_ID_GET interface (also see 8.7 FFA_ID_GET).

        This version of the Framework considers two types of devices.

        - Devices that can act as initiators and recipients of memory management transactions. 
          These devices are called independent peripheral devices. 
          Each device must specify the following information in its partition manifest 
          (see 3.4 Independent peripheral device manifest).
          - A SEPID assigned to the device at boot time.
          - The SMMU ID that the device is upstream of.
          - Each Stream ID the device can generate.
          - Regions in the physical address space that must be mapped in the translation tables 
            corresponding to the SEPID at boot time.

          This information enables the partition manager to create an association between a device and a 
          SEPID at boot time. A partition manager or PE endpoint and an independent device must use an 
          IMPLEMENTATION DEFINED mechanism to notify each other about a memory management transaction 
          targeted to a SEPID used by the device (see 5.5.2 Transaction life cycle).

        -  Devices that cannot act as initiators and recipients of memory management transactions. 
           These devices are called dependent peripheral devices. They rely on a PE endpoint to initiate and 
           receive memory management transactions on their behalf. The PE endpoint is called a proxy endpoint.

           A dependent device could be assigned to a PE endpoint. This implies,
           - Access to its MMIO regions is assigned to the endpoint during boot (see 2.10 System resource
             management & Table 3.3).
           - The endpoint manages the association between Stream IDs generated by the device and stage 1
             translations in the SMMU that the device is upstream of (see Table 3.3).
           The device could be either assigned to its proxy endpoint or a different PE endpoint.

           When assigned to its proxy endpoint, this version of the Framework assumes that all the 
           Stream IDs generated by the device have the same visibility of the physical address space 
           as the endpoint. The stage 2 translations in the SMMU for these Stream IDs are the same as 
           those maintained by the partition manager on behalf of the endpoint. They are not assigned a SEPID. 
           The partition ID of the proxy endpoint is used instead. All memory management transactions with 
           this partition ID effect both sets of translations. When assigned to a different endpoint, 
           the partition manifest of the proxy endpoint (see 3.2 Partition manifest at virtual FF-A instance) 
           must specify the following information to enable the partition manager to create an
           association between a device and a SEPID at boot time.
           - The SMMU ID that the device is upstream of.
           - Each Stream ID the device can generate.
           - The SEPID corresponding to each Stream ID.

           The partition ID of the proxy endpoint must be distinct from the SEPID allocated to manage the 
           preceding association. The SEPID must be specified in the partition manifest of the proxy 
           endpoint (see Table 3.1). 

           The stage 2 translations corresponding to the SEPID are configured at boot time with no access 
           to the physical address space.

           A memory management transaction targeted to the SEPID must be allowed to complete only if it is either
           initiated or authorized by the proxy endpoint for the device (see 5.5.2 Transaction life cycle).
        
        The SEPIDs used by an independent device must be distinct from the SEPIDs used by a dependent device.
        This constraint avoids the scenario where a memory management transaction is allowed to change the stage 2
        translations before the proxy endpoint has authorized it.
     *)
    
  End DirectMemoryAccess.

  Section AddressTranslationRegimes.
    (** ** Address translation regimes - Section 5.3.

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
  (** ** Ownership and access attributes - Section 5.4.

     [JIEUNG: This section is one of the most important section to provides abstract view of memory ownership and 
     attributes. And, descriptions in this section has to be reflected in our formalized version. Please look at the MemProperties 
     definition (MemProperties) and valid_combination definitions (mem_states_valid_combination)]

    The Hypervisor, SPM, and all endpoints have access and ownership attributes associated with every memory 
    region in the physical address space.

    Access determines the data and instruction access permissions to the memory region. 
    A component can have the following access permissions to a memory region.
    - No access.
    - Read-only, Execute-never.
    - Read-only, Executable.
    - Read/write, Execute-never.

    Access control must be enforced through an IMPLEMENTATION DEFINED mechanism and/or by encoding these
    permissions in the translation regime of an endpoint managed by the partition manager (see 5.3 
    Address translation regimes).

    Ownership is a software attribute that determines if a component can grant access to a memory region to another
    component. A component that has access to a memory region without ownership is called the Borrower. A
    component that lends access to a memory region it owns is called the Lender.

    Ownership of a memory region is initially assigned to the component that it is allocated to. At boot time all
    memory regions are owned by Secure firmware. A memory region could be configured as Secure or normal
    memory either statically at reset, or by Secure firmware during boot. Secure firmware transfers ownership of
    normal memory to Normal world software. It sub-divides Secure memory such that:
    - It owns and has exclusive access to some memory regions.
    - It owns but grants access to some memory regions to SPs.
    - It transfers ownership of some memory regions to SPs.
    If virtualization is enabled in the Normal world, the Hypervisor divides a subset of normal memory among VMs
    and transfers ownership to them. In the absence of virtualization, all normal memory donated by the Secure world
    is owned by the OS kernel.

    An endpoint requests access to and/or ownership of a memory region through its partition manifest 
    (also see Table 3.2).
   *)

    (** *** Ownership and access rules - Section 5.4.1 
        
        The SPM and Hypervisor must enforce the following general ownership and access rules to memory regions.
        - The size of a memory region to which ownership and access rules apply must be a multiple of the smallest
          translation granule size supported on the system.
          - It is 4K in the AArch32 Execution state.
          - A EL1 or S-EL1 partition must discover this by reading the ID_AA64MMFR0_EL1 System register in
            the AArch64 Execution state.
          - A S-EL0 SP must determine this through an IMPLEMENTATION DEFINED discovery mechanism for
            example, DT or ACPI tables.
        - A normal memory region must be mapped with the Non-secure security attribute in any component that is
          granted access to it.
        - A Secure memory region must be mapped with the Secure security attribute in any component that is granted
          access to it.
        - Each memory region in the physical address space must have a single Owner.
        - A FF-A component must have access to a memory region it owns unless it has granted exclusive access to
          the region to another FF-A component.
        - Only the Owner of a memory region can grant access to it to one or more Borrowers in the system.
        - Only the Owner of a memory region can transfer its ownership to another endpoint in the system.
        - If an SP is terminated ’cause of a fatal error condition, access to the memory regions of the SP is
          transferred to the SPM.
        - If a VM is terminated ’cause of a fatal error condition, access to the memory regions of the VM
          and their ownership are transferred to the Hypervisor.
        - If the Hypervisor or OS kernel are terminated ’cause of a fatal error condition, access to the 
          their memory regions and ownership are transferred to the SPM.
        - The number of distinct components to whom an Owner can grant access to a memory region is 
          IMPLEMENTATION DEFINED.
        - The Owner of a memory region must not be able to change its ownership or access attributes until all
          Borrowers have relinquished access to it.
     *)

    (** ***  Ownership and access states - Section 5.4.2 
        
        Table 5.1 describes the ownership states applicable to an FF-A component for a memory region.
     *)
    (* Table 5.1: Ownership states
       No.        Ownership state       Acronym         Description
       1          Owner                 Owner           Component owns the memory region.
       2          Not Owner             !Owner          Component does not own the memory region.
     *)

    (** Table 5.2 describes the access states applicable to an FF-A component for a memory region. *)
    (* Table 5.2: Access states
       No.        Access state          Acronym         Description
       1          No access             NA              A component has no access to a memory region. 
                                                        It is not mapped in its translation regime.
       2         Exclusive access       EA              A component has exclusive access to a memory region. 
                                                        It is mapped only in its translation regime.
       3         Shared access          SA              A component has shared access to a memory. It is mapped 
                                                        in its translation regime and the translation regime of 
                                                        at least one other component
     *)

    (** Table 5.3 describes the valid combination of access and ownership states applicable to an FF-A 
        component for a memory region. *)
    (* Table 5.3: Valid combinations of ownership and access states
       No.   Ownership state       Access state       Acronym            Description
       1     Not Owner             No access          !Owner-NA          Component has neither
                                                                         ownership nor access to the
                                                                         memory region.
       2     Not Owner             Exclusive access   !Owner-EA          Component has exclusive access
                                                                         without ownership of the
                                                                         memory region.
       3     Not Owner             Shared access      !Owner-SA          Component has shared access
                                                                         with one or more components
                                                                         without ownership of the
                                                                         memory region
       4     Owner                 No access          Owner-NA           Component owns the memory
                                                                         region and has granted:
                                                                         - Either exclusive access to
                                                                           the memory region to
                                                                           another component.
                                                                         - Or shared access to the
                                                                           memory region among
                                                                           other components.
       5     Owner                 Exclusive access   Owner-EA           Component owns the memory
                                                                         region and has exclusive access
                                                                         to it.
       6     Owner                 Shared access      Owner-SA           Component owns the memory
                                                                         region and shares access to it
                                                                         with one or more components
     *)

    (** For two FF-A components A and B and a memory region, valid combinations of states defined in 
        Table 5.3 are described in Table 5.4. Other combinations of states are considered invalid. *)

    (* Table 5.4: Valid combinations of ownership and access states between two components 
       No.   Component  Component    Description
             A state    B state       
       1     Owner-EA   !Owner-NA     Component A has exclusive access and ownership of a memory
                                      region that is inaccessible from component B.
       2     Owner-NA   !Owner-NA     Component A has granted exclusive access to a memory region it
                                      owns to another component. It is inaccessible from component B.
       3     Owner-NA   !Owner-EA     Component A has granted exclusive access to a memory region it
                                      owns to component B.
       4     Owner-NA   !Owner-SA     Component A has relinquished access to a memory region it owns.
                                      Access to the memory region is shared between component B and at
                                      least one other component
       5     Owner-SA   !Owner-NA     Component A shares access to a region of memory it owns with
                                      another component. Component B cannot access the memory
                                      region.
       6     Owner-SA   !Owner-SA     Component A shares access to a region of memory it owns with
                                      component B and possibly other components.
     *)

    (** [JIEUNG: The following things has to be captured in the memory property]
    Implementation Note

    To fulfill the use cases and enforce the rules listed earlier, FF-A components should track the state of a memory
    region. This could be done as follows,
    - An Owner tracks the level of access it has to a memory region.
    - An Owner tracks the level of access that Borrowers have to a memory region along with the identity of the
      Borrowers.
    - A Borrower tracks the level of access the Owner has to a memory region along with the identity of the Owner.
    - A Borrower tracks the level of access it has to a memory region.
    - A Borrower tracks the level of access that other Borrowers have to a memory region along with the identity
      of the Borrowers.
    - For each memory region, the SPM and Hypervisor track the following.
      – The identity of each Borrower.
      – The identity of the Owner.
      – The level of access of each Borrower.
      – The level of access of the Owner.
     *)
    
  End OwnershipAndAccessAttributes.

  Section RemainingParts.

    (** ** Remaining parts  *)

    (** 
        From 5.5 to the end of Section 5., and for the details in Section 11, 
        we write comments on our mechanized versions.
     *)
    
  End RemainingParts.
  
End MemoryManagementIntro.

