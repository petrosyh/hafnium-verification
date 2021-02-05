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
Require Import Decision.

(* FFA Memory management related parts *)
Require Import FFAMemoryHypCallIntro.

Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Require Import Maps.
Set Implicit Arguments.

Definition Z_64MAX := ((Z.pow 2 64) - 1)%Z.
Definition Z_not := fun val => (Z.lxor Z_64MAX val).

(*************************************************************)
(** *                 FFA function keyword                   *) 
(*************************************************************)
Section FFA_DATATYPES.
  

  (** This section provides FFA memory management related definitions, which can be mostly observed 
     in the Arm Firmware Framework for Armv8-A (https://developer.arm.com/documentation/den0077/latest) 
     document. 
  *)

  (** The following numbers are defined in Chapter 11 (Memory management interfaces document) 
   #define FFA_MEM_DONATE_32            0x84000071 - Defined in Table 11.3 FFA_MEM_DONATE function syntax         
   #define FFA_MEM_LEND_32              0x84000072 - Defined in Table 11.8 FFA_MEM_LEND function syntax           
   #define FFA_MEM_SHARE_32             0x84000073 - Defined in Table 11.13: FFA_MEM_SHARE function syntax        
   #define FFA_MEM_RETRIEVE_REQ_32      0x84000074 - Defined in Table 11.18 FFA_MEM_RETRIEVE_REQ function syntax  
   #define FFA_MEM_RETRIEVE_RESP_32     0x84000075 - Defined in Table 11.22: FFA_MEM_RETRIEVE_RESP function synta 
   #define FFA_MEM_RELINQUISH_32        0x84000076 - Defined in Table 11.27: FFA_MEM_RELINQUISH function syntax   
   #define FFA_MEM_RECLAIM_32           0x84000077 - Defined in Table 11.31: FFA_MEM_RECLAIM function syntax      
   *)
  
  Definition FFA_MEM_DONATE_32 : Z := 2214592625.
  Definition FFA_MEM_LEND_32 : Z := 2214592626.
  Definition FFA_MEM_SHARE_32 : Z := 2214592627.
  Definition FFA_MEM_RETRIEVE_REQ_32 : Z := 2214592628.
  Definition FFA_MEM_RETRIEVE_RESP_32 : Z := 2214592629.
  Definition FFA_MEM_RELINGQUISH_32 : Z := 2214592630.
  Definition FFA_MEM_RECLAIM_32 : Z := 2214592631.

  Inductive FFA_FUNCTION_TYPE :=
  | FFA_MEM_DONATE
  | FFA_MEM_LEND
  | FFA_MEM_SHARE
  | FFA_MEM_RETREIVE_REQ
  | FFA_MEM_RETREIVE_RESP
  | FFA_MEM_RELINQUISH
  | FFA_MEM_RECLAIM.


  (** The followings are for return values of FFA interface calls. *)
  (** The following numbers are defined in Chapter 7, especially in Table 7.2: Error status codes
   /* FF-A error codes. */ 
   #define FFA_NOT_SUPPORTED      INT32_C(-1)
   #define FFA_INVALID_PARAMETERS INT32_C(-2)
   #define FFA_NO_MEMORY          INT32_C(-3)
   #define FFA_BUSY               INT32_C(-4)
   #define FFA_INTERRUPTED        INT32_C(-5)
   #define FFA_DENIED             INT32_C(-6)
   #define FFA_RETRY              INT32_C(-7)
   #define FFA_ABORTED            INT32_C(-8)
  *)

  Definition FFA_NOT_SUPPORTED_32 : Z := -1.
  Definition FFA_INVALID_PARAMETERS_32 : Z := -2.
  Definition FFA_NO_MEMORY_32 : Z := -3.
  Definition FFA_BUSY_32 : Z := -4.
  Definition FFA_INTERRUPTED_32 : Z := -5.
  Definition FFA_DENIED_32 : Z := -6.
  Definition FFA_RETRY_32 : Z := -7.
  Definition FFA_ABORTED_32 : Z := -8.

  Inductive FFA_ERROR_CODE_TYPE :=
  | FFA_NOT_SUPPORTED
  | FFA_INVALID_PARAMETERS
  | FFA_NO_MEMORY
  | FFA_BUSY
  | FFA_INTERRUPTED
  | FFA_DENIED
  | FFA_RETRY
  | FFA_ABORTED.  
  
  (** The following numbers are also defined in Chapter 7
  #define FFA_ERROR_32                 0x84000060 - Defined in Table 7.4: FFA_ERROR function syntax
  #define FFA_SUCCESS_32               0x84000061 - Defined in Table 7.7: FFA_SUCCESS function syntax
  *)

  Definition FFA_ERROR_32 : Z := 2214592608.
  Definition FFA_SUCCESS_32 : Z := 2214592609.

  (* XXX : need to determine whether we have to encapsulate error code in here or not *)
  Inductive FFA_RESULT_CODE_TYPE :=
  (* | FFA_ERROR (error_type: FFA_ERROR_CODE_TYPE) *)
  | FFA_ERROR
  | FFA_SUCCESS.


  (** This version only focus on two FFA interfaces, memory management related interfaces and interfaces for 
     the result of memory management related parts *) 
  Inductive FFA_IDENTIFIER_TYPE :=
  | FFA_IDENTIFIER_DEFAULT
  | FFA_FUNCTION_IDENTIFIER (func: FFA_FUNCTION_TYPE)
  | FFA_RESULT_CODE_IDENTIFIER (func: FFA_RESULT_CODE_TYPE).

End FFA_DATATYPES.


(*************************************************************)
(** *      Types and Constant values that are used in FF     *) 
(*************************************************************)

Section FFA_TYPES_AND_CONSTANT.

  (** Basic constraints about thoset types *)
  Class FFA_TYPES_AND_CONSTANTS :=
    {
    (** The type aliasing for readability: *)
    (** 2.8. Partition identification and discovery *)
    (** 2.9. An execution context is identified by using a 16-bit ID. This ID is referred
        to as the vCPU or execution context ID *)
    ffa_UUID_t : Type := Z;
    ffa_VCPU_ID_t : Type := Z;
    (** 8.1. FFA_VERSION: 
        The first one is a major version number and the second one is for the minor version *)
    ffa_version_number_t : Type := (Z * Z)%type; 

    (** Things that we have added *)
    (** The following type is for CPU ID values *)
    ffa_CPU_ID_t : Type := Z;
    (** This is a bare address value that represent the memory PA *)
    ffa_address_t := Z;
    ffa_granuale_size_t := Z;
    ffa_memory_handle_t := Z;
    ffa_memory_access_permissions_t := Z;
    ffa_memory_receiver_flags_t := (option bool);
    
    ffa_memory_attributes_t := Type;
    ffa_memory_region_tag_t := Type;
    ffa_mailbox_send_msg_t := Type;
    ffa_mailbox_recv_msg_t := Type;
    
    granuale : ffa_granuale_size_t;
    init_ffa_memory_attributes : ffa_memory_attributes_t;
    init_ffa_memory_region_tag : ffa_memory_region_tag_t;
    init_ffa_mailbox_send_msg: ffa_mailbox_send_msg_t;
    init_ffa_mailbox_recv_msg: ffa_mailbox_recv_msg_t;

    ffa_memory_attributes_t_dec : forall (attributes1 attributes2: ffa_memory_attributes_t),
        {attributes1 = attributes2} + {attributes1 <> attributes2};
    ffa_memory_region_tag_t_dec : forall (tag1 tag2: ffa_memory_region_tag_t),
        {tag1 = tag2} + {tag1 <> tag2};
    ffa_mailbox_send_msg_t_dec : forall (mailbox_send_msg1 mailbox_send_msg2: ffa_mailbox_send_msg_t),
        {mailbox_send_msg1 = mailbox_send_msg2} + {mailbox_send_msg1 <> mailbox_send_msg2};
    ffa_mailbox_recv_msg_t_dec : forall (mailbox_recv_msg1 mailbox_recv_msg2: ffa_mailbox_recv_msg_t),
        {mailbox_recv_msg1 = mailbox_recv_msg2} + {mailbox_recv_msg1 <> mailbox_recv_msg2};    
    }.


  (** The following values are specific values for Hafnium. *)
  (** The following options are for message send and receive. So we ignore them in the current setting 
  /* FF-A function specific constants. */
  <<
  #define FFA_MSG_RECV_BLOCK 0x1
  #define FFA_MSG_RECV_BLOCK_MASK 0x1 

  #define FFA_MSG_SEND_NOTIFY 0x1
  #define FFA_MSG_SEND_NOTIFY_MASK 0x1

  #define FFA_SLEEP_INDEFINITE 0
  >>
  *)

  (** This one is used as a flag value for reclaim (FFA_MEM_RECLAIM). 
  <<
  #define FFA_MEM_RECLAIM_CLEAR 0x1
  >>
   *)
  
  Definition FFA_MEM_RECLAIM_CLEAR := 1.
  
  (**
  <<
  /** 
   * For use where the FF-A specification refers explicitly to '4K pages'. Not to
   * be confused with PAGE_SIZE, which is the translation granule Hafnium is
   * configured to use.
   */
  #define FFA_PAGE_SIZE 4096

  /* The maximum length possible for a single message. */
  #define FFA_MSG_PAYLOAD_MAX HF_MAILBOX_SIZE

  Definition FFA_PAGE_SIZE := 4096.
  Definition HF_MAILBOX_SIZE := 4096.
  Definition FFA_MSG_PAYLOAD_MAX := HF_MAILBOX_SIZE.
  >>
  *)
   

  Context `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}.
  Definition FFA_PAGE_SIZE := granuale.
  Definition HF_MAILBOX_SIZE := granuale.
  Definition FFA_MSG_PAYLOAD_MAX := HF_MAILBOX_SIZE.
  
End FFA_TYPES_AND_CONSTANT.

(*************************************************************)
(** *                       Descriptors                      *) 
(*************************************************************)
(** The following parts are related to "5.10 Memory region description" and "5.11 Memory region properties" *)
Section FFA_DESCRIPTIONS.

  (*************************************)
  (** * 5.10 Memory region description *)
  (*************************************)
  Context `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}.

  (**************************************************************************)
  (** *  Constituent memory region and composite_memory_region descriptors  *) 
  (**************************************************************************)  
  (** We define descriptors that are used in FFA interfaces. Sender, Relayer, and Borrower use them 
      to figure out the information and check validity of the query by using them *) 
     
  (** Table 5.14: Constituent memory region descriptor
  /**
   * A set of contiguous pages which is part of a memory region. This corresponds
   * to table 40 of the FF-A 1.0 EAC specification, "Constituent memory region
   * descriptor".
   */
  <<
  struct ffa_memory_region_constituent {
          /**
           * The base IPA of the constituent memory region, aligned to 4 kiB page
           * size granularity.
           */
          uint64_t address;
          /** The number of 4 kiB pages in the constituent memory region. */
          uint32_t page_count;
          /** Reserved field, must be 0. */
          uint32_t reserved;
  };
  >>
   *)

  Record FFA_memory_region_constituent_struct :=
    mkFFA_memory_region_constituent_struct {
        FFA_memory_region_constituent_struct_address : ffa_address_t; (** length: 8 bytes / offset: 0 bytes *)
        FFA_memory_region_constituent_struct_page_count : Z; (** length: 4 bytes / offset: 4 bytes *)
        (** reserved MBZ - length: 4 bytes / offset: 12 byte *) 
      }.

  (** Table 5.13: Composite memory region descriptor - A set of pages comprising a memory region. 
      struct ffa_composite_memory_region {
              /**
               * The total number of 4 kiB pages included in this memory region. This
               * must be equal to the sum of page counts specified in each
               * `ffa_memory_region_constituent`.
               */
              uint32_t page_count;
              /**
               * The number of constituents (`ffa_memory_region_constituent`)
               * included in this memory region range.
               */
              uint32_t constituent_count;
              /** Reserved field, must be 0. */
              uint64_t reserved_0;
              /** An array of `constituent_count` memory region constituents. */
              struct ffa_memory_region_constituent constituents[];
      };
   *)

  Definition init_FFA_memory_region_constituent_struct :=
    mkFFA_memory_region_constituent_struct 0 0.
  
  Record FFA_composite_memory_region_struct :=
    mkFFA_composite_memory_region_struct {
        FFA_composite_memory_region_struct_page_count : Z; (** length: 4 bytes / offset: 0 bytes  *)
        (** we ignored this one by representing constituents one as a list
        FFA_composite_memory_region_struct_constituent_count : Z; 
        - length: 4 bytes / offset: 4 bytes  *)
        (** reserved - legnth: 8 bytes / offset: 8 bytes *)
        FFA_composite_memory_region_struct_constituents :
          list FFA_memory_region_constituent_struct
               (** length: 16 bytes * num of elements / offset: 16 bytes *)
      }.

  (** "Figure 5.2: Example memory region description" shows how those two are related *)
     
  Definition init_FFA_composite_memory_region_struct := 
    mkFFA_composite_memory_region_struct 0 nil.

  (** Basic well-formedness condition *)
  Fixpoint well_formed_FFA_composite_memory_region_struct_aux (page_counts : Z)
           (constituents : list FFA_memory_region_constituent_struct) :=
    match constituents with
    | nil => if decide (page_counts = 0) then true else false
    | hd::tl =>
      match hd with
      | mkFFA_memory_region_constituent_struct address page_count =>
        if decide (Z.modulo address granuale = 0) &&
           decide ((page_counts - page_count)%Z >= 0) 
        then well_formed_FFA_composite_memory_region_struct_aux (page_counts - page_count) tl
        else false
      end
    end.

  Definition well_formed_FFA_composite_memory_region_struct (composite: FFA_composite_memory_region_struct) :=
    well_formed_FFA_composite_memory_region_struct_aux
      (composite.(FFA_composite_memory_region_struct_page_count))
      (composite.(FFA_composite_memory_region_struct_constituents)).

  (***********************************************************************)
  (** *                         Memory region handle                     *) 
  (***********************************************************************)  
  (** Handle : 64-bit, and the handle is allocated by teh replayer 
     - The Hypervisor must allocate the Handle if no Receiver participating in the memory management
       transaction is an SP or SEPID associated with a Secure Stream ID in the SMMU.
     - A Handle is allocated once a transaction to lend, share or donate memory is successfully 
       initiated by the Owner.
     - Each Handle identifies a single unique composite memory region description that is, 
       there is a 1:1 mapping between the two.
     - A Handle is freed by the Relayer after it has been reclaimed by its Owner at the end 
       of a successful transaction to relinquish the corresponding memory region description.
     - Encoding of a Handle is as follows.
       – Bit[63]: Handle allocator.
         * b’0: Allocated by SPM.
         * b’1: Allocated by Hypervisor.
       – Bit[62:0]: IMPLEMENTATION DEFINED.
     - A Handle must be encoded as a register parameter in any ABI that requires it as follows.
       – Two 32-bit general-purpose registers must be used such that if Rx and Ry are used, such that x < y,
         * Rx = Handle[31:0].
         * Ry = Handle[63:32]. *)

  (** Memory region handle in Hafnium is actually the index of "share_state_pool" (defined in FFAMemoryHypCallState.v) 
      which contains the information that receivers has to look up. *)

  (*************************************)
  (** * 5.11 Memory region properties  *)
  (*************************************)  
  (**************************************************************************)
  (** *  Constituent memory region and composite_memory_region descriptors  *) 
  (**************************************************************************)
  
  (** From here, most parts are related to 5.11 Memory region properties. *)
  (**
     - Instruction and data access permissions describe the type of access permitted on the memory region.
     - One or more endpoint IDs that have access to the memory region specified by a combination of access
       permissions and memory region attributes.
     - Memory region attributes control the memory type, accesses to the caches, and whether 
       the memory region is Shareable and therefore is coherent.
  
     ffa data access and instruction access permission values are used in the memory access
     permissions descriptor (In Table 5.15: Memory access permissions descriptor). 
   *)

  (** Table 5.15: Memory access permissions descriptor *)
  (**
  enum ffa_instruction_access {
          FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED,
          FFA_INSTRUCTION_ACCESS_NX,
          FFA_INSTRUCTION_ACCESS_X,
          FFA_INSTRUCTION_ACCESS_RESERVED,
  };
  *)

  Definition FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED_Z := 0.
  Definition FFA_INSTRUCTION_ACCESS_NX_Z := 1.
  Definition FFA_INSTRUCTION_ACCESS_X_Z := 2.
  Definition FFA_INSTRUCTION_ACCESS_RESERVED_Z := 3.

  (**
    Execute permission is more permissive than Execute-never permission. 
     - 5.11.3 Instruction access permissions usage *)  
  Inductive FFA_INSTRUCTION_ACCESS_TYPE :=
  | FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED
  | FFA_INSTRUCTION_ACCESS_NX
  | FFA_INSTRUCTION_ACCESS_X
  | FFA_INSTRUCTION_ACCESS_RESERVED.
  
  (**
  enum ffa_data_access {
          FFA_DATA_ACCESS_NOT_SPECIFIED,
          FFA_DATA_ACCESS_RO,
          FFA_DATA_ACCESS_RW,
          FFA_DATA_ACCESS_RESERVED,
  };
   *)

  Definition FFA_DATA_ACCESS_NOT_SPECIFIED_Z := 0.
  Definition FFA_DATA_ACCESS_RO_Z := 1.
  Definition FFA_DATA_ACCESS_RW_Z := 2.
  Definition FFA_DATA_ACCESS_RESERVED_Z := 3.

  (**
    Read-write permission is more permissive than Read-only permission. 
     - 5.11.2 Data access permissions usage shows invariants about this fields *)
  Inductive FFA_DATA_ACCESS_TYPE :=
  | FFA_DATA_ACCESS_NOT_SPECIFIED
  | FFA_DATA_ACCESS_RO
  | FFA_DATA_ACCESS_RW
  | FFA_DATA_ACCESS_RESERVED.

 (**
  /** Flags to indicate properties of receivers during memory region retrieval. */
  typedef uint8_t ffa_memory_receiver_flags_t;
   
  [JIEUNG: The name in Hafnium is somewhat wierd. I changed the name for my impl.]

  struct ffa_memory_region_attributes {
          /** The ID of the VM to which the memory is being given or shared. */
          ffa_vm_id_t receiver;
          /**
           * The permissions with which the memory region should be mapped in the
           * receiver's page table.
           */
          ffa_memory_access_permissions_t permissions;
          /**
           * Flags used during FFA_MEM_RETRIEVE_REQ and FFA_MEM_RETRIEVE_RESP
           * for memory regions with multiple borrowers.
           */
          ffa_memory_receiver_flags_t flags;
  };
   
  *)

  (**
   A composite memory region description is referenced by specifying an offset to it as described in Table 5.16.
   This enables one or more endpoints to be associated with the same memory region but with different memory
   access permissions for example, SP0 could have RO data access permission and SP1 could have RW data access
   permission to the same memory region.
   *)
  Record FFA_memory_access_permissions_descriptor_struct :=
    mkFFA_memory_access_permissions_descriptor_struct {
        FFA_memory_access_permissions_descriptor_struct_receiver :
          ffa_UUID_t; (** length: 2 bytes / offset: 0 bytes *)
        (**
           memory access permissions: length: 1 bytes / offset: 2 bytes -
           bits[7:4]: Reserved (MBZ).
           – bits[3:2]: Instruction access permission.
           * b’00: Not specified and must be ignored.
           * b’01: Not executable.
           * b’10: Executable.
           * b’11: Reserved. Must not be used.
           – bits[1:0]: Data access permission.
           * b’00: Not specified and must be ignored.
           * b’01: Read-only.
           * b’10: Read-write.
           * b’11: Reserved. Must not be used. *)
        FFA_memory_access_permissions_descriptor_struct_permisions_instruction : FFA_INSTRUCTION_ACCESS_TYPE;
        FFA_memory_access_permissions_descriptor_struct_permisions_data : FFA_DATA_ACCESS_TYPE;
        (**
           the flag value is only used for "FFA_MEM_RETRIEVE_REQ / FFA_MEM_RETRIEVE_RESP". For 
           "FFA_MEM_DONATE / FFA_MEM_LEND / FFA_MEM_SHARE" this field is empty *)
        (**
           Bit[0]: Non-retrieval Borrower flag.
                   – In a memory management transaction with multiple Borrowers, during the retrieval
                   of the memory region, this flag specifies if the memory region must be or was
                   retrieved on behalf of this endpoint or if the endpoint is another Borrower.
                   * b’0: Memory region must be or was retrieved on behalf of this endpoint.
                   * b’1: Memory region must not be or was not retrieved on behalf of this endpoint.
                   It is another Borrower of the memory region.
                   – This field MBZ if this endpoint:
                   * Is the only PE endpoint Borrower/Receiver in the transaction.
                   * Is a Stream endpoint and the caller of the FFA_MEM_RETRIEVE_REQ ABI is
                   its proxy endpoint.
           Bit[7:1] • Reserved (MBZ). *)
        FFA_memory_access_permissions_descriptor_struct_flags: ffa_memory_receiver_flags_t;
      }.

  Definition init_FFA_memory_access_permissions_descriptor_struct :=
    mkFFA_memory_access_permissions_descriptor_struct 0 FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED
                                                      FFA_DATA_ACCESS_NOT_SPECIFIED None.
  
  (** Table 5.16: Endpoint memory access descriptor *)
  (**
  struct ffa_memory_access {
          struct ffa_memory_region_attributes receiver_permissions;
          /**
           * Offset in bytes from the start of the outer `ffa_memory_region` to
           * an `ffa_composite_memory_region` struct.
           */
          uint32_t composite_memory_region_offset;
          uint64_t reserved_0;
  };
   *)
  Record FFA_endpoint_memory_access_descriptor_struct :=
    mkFFA_endpoint_memory_access_descriptor_struct {
        FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor :
          FFA_memory_access_permissions_descriptor_struct; (** length: 4 bytes / offset: 0 bytes *)

        (* TODO: the following things are somewhat vauge for me how to use them. 
           If it points one constituent in the list of constituents, will it use only one constituent? 
           Or, can we provide a length that represents the number of constituents that we hope to use? *)
        (**
           NOTE: In Hafnium and FF-A document, the following field is defined as an offset 
           to point out the memory region that contains "FFA_composite_memory_region". 
           Instead of following them, we explicitly map "FFA_composite_memory_region_struct" 
           in here with option type to handle the case when offset points out NULL *)
        FFA_memory_access_descriptor_struct_composite_memory_region_struct :
          option FFA_composite_memory_region_struct;
        (** It indicates one of constituents inside the composite_memory_region_struct to 
            retrieve specific memory region *)
        FFA_memory_access_descriptor_struct_composite_memory_region_offset : nat;
        
        (** memory region struct is created and destroyed when hypervisor starts/finishes 
            their handling. Instead of merging it into  *)
        (** NOTE: the original size of the above offset value is as follows *)
        (** length: 4 bytes / offset: 4 bytes *)
        (** Reserved (MBZ) - length: 8 bytes / offset: 8 bytes *)
      }.
  
  Definition init_FFA_endpoint_memory_access_descriptor_struct :=
    mkFFA_endpoint_memory_access_descriptor_struct
      init_FFA_memory_access_permissions_descriptor_struct None 0.


  Definition well_formed_FFA_endpoint_memory_access_descriptor_struct
             (descriptor : FFA_endpoint_memory_access_descriptor_struct) :=
    match descriptor.(FFA_memory_access_descriptor_struct_composite_memory_region_struct) with
    | None => if decide (descriptor.(FFA_memory_access_descriptor_struct_composite_memory_region_offset) = 0%nat)
             then true else false
    | Some composite =>
      if decide ((length (composite.(FFA_composite_memory_region_struct_constituents)) >=
                 descriptor.(FFA_memory_access_descriptor_struct_composite_memory_region_offset))%nat)
      then well_formed_FFA_composite_memory_region_struct composite
      else false
    end.
  
  (*****************************************************)
  (** * 5.11.2 Data access permissions usage           *)
  (*****************************************************)
  (** [JIEUNG: The following things need to be implemented in the transition rules] *)
  
  (** 
      - Read-write permission is more permissive than Read-only permission.
      - Data access permission is specified by setting Bits[1:0] in Table 5.15 to the appropriate value
   *)

  (**
      Restrictions in lend or share memory:
      - The Lender must specify the level of access that the Borrower is permitted to have on the memory region.
        This is done while invoking the FFA_MEM_SHARE or FFA_MEM_LEND ABIs.
      - The Relayer must validate the permission specified by the Lender as follows. This is done in response
        to an invocation of the FFA_MEM_SHARE or FFA_MEM_LEND ABIs. The Relayer must return the
        DENIED error code if the validation fails.
        - At the Non-secure physical FF-A instance, an IMPLEMENTATION DEFINED mechanism is used to perform validation.
        – At any virtual FF-A instance, if the endpoint is running in EL1 or S-EL1 in either Execution state,
          the permission specified by the Lender is considered valid only if it is the same or less permissive
          than the permission used by the Relayer in the S2AP field in the stage 2 translation table descriptors
          for the memory region in one of the following translation regimes:
          * Secure EL1&0 translation regime, when S-EL2 is enabled.
          * Non-secure EL1&0 translation regime, when EL2 is enabled.
        – At the Secure virtual FF-A instance, if the endpoint is running in S-EL0 in either Execution state,
          the permission specified by the Lender is considered valid only if it is the same or less permissive
          than the permission used by the Relayer in the AP[1] field in the stage 1 translation table descriptors
          for the memory region in one of the following translation regimes:
          * Secure EL1&0 translation regime, when EL2 is disabled.
          * Secure PL1&0 translation regime, when EL2 is disabled.
          * Secure EL2&0 translation regime, when Armv8.1-VHE is enabled.
          If the Borrower is an independent peripheral device, then the validated permission is used to map the
          memory region into the address space of the device.
        - The Borrower (if a PE or Proxy endpoint) should specify the level of access that it would like to have on
          the memory region. In a transaction to share or lend memory with more than one Borrower, each Borrower (if a PE or Proxy
          endpoint) could also specify the level of access that other Borrowers have on the memory region.
          This is done while invoking the FFA_MEM_RETRIEVE_REQ ABI.
        - The Relayer must validate the permissions, if specified by the Borrower (if a PE or Proxy endpoint) in
          response to an invocation of the FFA_MEM_RETRIEVE_REQ ABI.
          It must ensure that the permission of the Borrower is the same or less permissive than the permission
          that was specified by the Lender and validated by the Relayer.
          It must ensure that the permissions for other Borrowers are the same as those specified by the Lender
          and validated by the Relayer. The Relayer must return the DENIED error code if the validation fails.
   *)

  (**
     Restrictions in dontate memory: 
     - Whether the Owner is allowed to specify the level of access that the Receiver is permitted to have on the
       memory region depends on the type of Receiver.
       – If the Receiver is a PE or Proxy endpoint, the Owner must not specify the level of access.
       – If the Receiver is an independent peripheral device, the Owner could specify the level of access.
       The Owner must specify its choice in an invocation of the FFA_MEM_DONATE ABI.
     - The value of data access permission field specified by the Owner must be interpreted by the Relayer as
       follows. This is done in response to an invocation of the FFA_MEM_DONATE ABI.
       – If the Receiver is a PE or Proxy endpoint, the Relayer must return INVALID_PARAMETERS if the
         value is not b’00.
       – If the Receiver is an independent peripheral device and the value is not b’00, the Relayer must take
         one of the following actions.
         * Return DENIED if the permission is determined to be invalid through an IMPLEMENTATION DEFINED mechanism.
         * Use the permission specified by the Owner to map the memory region into the address space of the device.
       – If the Receiver is an independent peripheral device and the value is b’00, the Relayer must determine
         the permission value through an IMPLEMENTATION DEFINED mechanism.
     - The Receiver (if a PE or Proxy endpoint) should specify the level of access that it would like to have on
       the memory region. This is done while invoking the FFA_MEM_RETRIEVE_REQ ABI.
     - The Relayer must validate the permission specified by the Receiver to ensure that it is the same or less
       permissive than the permission determined by the Relayer through an IMPLEMENTATION DEFINED
       mechanism. This is done in response to an invocation of the FFA_MEM_RETRIEVE_REQ ABI. The
       Relayer must return the DENIED error code if the validation fails.
  *)

  (** 
      Restrictions in retrieve response:
      - The Relayer must specify the permission that was used to map the memory region in the translation regime
        of the Receiver or Borrower. This must be done in an invocation of the FFA_MEM_RETRIEVE_RESP ABI.
   *)

  (** 
      Restrictions on reclaim:
      - In a transaction to relinquish memory that was lent to one or more Borrowers, the memory region must be
        mapped back into the translation regime of the Lender with the same data access permission that was used
        at the start of the transaction to lend the memory region. This is done in response to an invocation of the
        FFA_MEM_RECLAIM ABI.
   *)

  (*****************************************************)
  (** * 5.11.3 Instruction access permissions usage    *)
  (*****************************************************)
  (** [JIEUNG: The following things need to be implemented in the transition rules] *)

  (** An endpoint could have either Execute (X) or Execute-never (XN) instruction access permission to a memory
      region from the highest Exception level it runs in.
      - Execute permission is more permissive than Execute-never permission.
      - Instruction access permission is specified by setting Bits[3:2] in Table 5.15 to the appropriate value.
        This access control is used in memory management transactions as follows.

      1. Only XN permission must be used in the following transactions.
         - In a transaction to share memory with one or more Borrowers.
         - In a transaction to lend memory to more than one Borrower.
         Bits[3:2] in Table 5.15 must be set to b’00 as follows.
         - By the Lender in an invocation of FFA_MEM_SHARE or FFA_MEM_LEND ABIs.
         - By the Borrower in an invocation of the FFA_MEM_RETRIEVE_REQ ABI.
         The Relayer must set Bits[3:2] in Table 5.15 to b’01 while invoking the FFA_MEM_RETRIEVE_RESP ABI.
      2. In a transaction to donate memory or lend memory to a single Borrower,
         - Whether the Owner/Lender is allowed to specify the level of access that the Receiver is permitted to
           have on the memory region depends on the type of Receiver.
           * If the Receiver is a PE or Proxy endpoint, the Owner must not specify the level of access.
           * If the Receiver is an independent peripheral device, the Owner could specify the level of access.
           The Owner must specify its choice in an invocation of the FFA_MEM_DONATE or FFA_MEM_LEND ABIs.
         - The value of instruction access permission field specified by the Owner/Lender must be interpreted   
           by the Relayer as follows. This is done in response to an invocation of the FFA_MEM_DONATE or FFA_MEM_LEND ABIs.
           * If the Receiver is a PE or Proxy endpoint, the Relayer must return INVALID_PARAMETERS if the value is not b’00.
           * If the Receiver is an independent peripheral device and the value is not b’00, the Relayer must take 
             one of the following actions.
             - Return DENIED if the permission is determined to be invalid through an IMPLEMENTATION DEFINED mechanism.
             - Use the permission specified by the Owner to map the memory region into the address space of the device.
           * If the Receiver is an independent peripheral device and the value is b’00, the Relayer must determine 
             the permission value through an IMPLEMENTATION DEFINED mechanism.
         - The Receiver (if a PE or Proxy endpoint) should specify the level of access that it would like to 
           have on the memory region. This must be done in an invocation of the FFA_MEM_RETRIEVE_REQ ABI.
         - The Relayer must validate the permission specified by the Receiver (if a PE or Proxy endpoint) to
           ensure that it is the same or less permissive than the permission determined by the Relayer through an       
           IMPLEMENTATION DEFINED mechanism.
           * For example, the Relayer could deny executable access to a Borrower on a memory region of Device
             memory type.
         - This is done in response to an invocation of the FFA_MEM_RETRIEVE_REQ ABI. The Relayer must
           return the DENIED error code if the validation fails.
  *)
  
  (*****************************************************)
  (** * 5.11.4 Memory region attributes usage          *)
  (*****************************************************)
  (** Memory type : – Device-nGnRnE < Device-nGnRE < Device-nGRE < Device-GRE < Normal.
     Cacheability attribute : – Non-cacheable < Write-Back Cacheable.
     Shareability attribute : – Non-Shareable < Inner Shareable < Outer shareable. *)
  (** length : 1 bytes *)
  (** More details can be found in 5.11.4 Memory region attributes usage *)
  (**
  enum ffa_memory_cacheability {
          FFA_MEMORY_CACHE_RESERVED = 0x0,
          FFA_MEMORY_CACHE_NON_CACHEABLE = 0x1,
          FFA_MEMORY_CACHE_RESERVED_1 = 0x2,
          FFA_MEMORY_CACHE_WRITE_BACK = 0x3,
          FFA_MEMORY_DEV_NGNRNE = 0x0,
          FFA_MEMORY_DEV_NGNRE = 0x1,
          FFA_MEMORY_DEV_NGRE = 0x2,
          FFA_MEMORY_DEV_GRE = 0x3,
  };
   *)

  Inductive FFA_MEMORY_CACHEABILITY_TYPE_1 :=
  | FFA_MEMORY_CACHE_RESERVED
  | FFA_MEMORY_CACHE_NON_CACHEABLE
  | FFA_MEMORY_CACHE_RESERVED_1
  | FFA_MEMORY_CACHE_WRITE_BACK.

  Inductive FFA_MEMORY_CACHEABILITY_TYPE_2 :=
  | FFA_MEMORY_DEV_NGNRNE
  | FFA_MEMORY_DEV_NGNRE
  | FFA_MEMORY_DEV_NGRE
  | FFA_MEMORY_DEV_GRE.

  Definition FFA_MEMORY_CACHE_RESERVED_Z := 0.
  Definition FFA_MEMORY_CACHE_NON_CACHEABLE_z := 1.
  Definition FFA_MEMORY_CACHE_RESERVED_1_Z := 2.
  Definition FFA_MEMORY_CACHE_WRITE_BACK_Z := 3.

  Definition FFA_MEMORY_DEV_NGNRNE_Z := 0.
  Definition FFA_MEMORY_DEV_NGNRE_Z := 1.
  Definition FFA_MEMORY_DEV_NGRE_Z := 2.
  Definition  FFA_MEMORY_DEV_GRE_Z := 3.

  (** The followings are values for 
  enum ffa_memory_type {
          FFA_MEMORY_NOT_SPECIFIED_MEM,
          FFA_MEMORY_DEVICE_MEM,
          FFA_MEMORY_NORMAL_MEM,
  };
   *)

  Definition FFA_MEMORY_NOT_SPECIFIED_MEM_Z := 0.
  Definition FFA_MEMORY_DEVICE_MEM_Z := 1.
  Definition FFA_MEMORY_NORMAL_MEM_Z := 2.
  
  (**
  enum ffa_memory_shareability {
          FFA_MEMORY_SHARE_NON_SHAREABLE,
          FFA_MEMORY_SHARE_RESERVED,
          FFA_MEMORY_OUTER_SHAREABLE,
          FFA_MEMORY_INNER_SHAREABLE,
  };
   *)

  Inductive FFA_MEMORY_SHAREABILITY :=
  | FFA_MEMORY_SHARE_NON_SHAREABLE
  | FFA_MEMORY_SHARE_RESERVED
  | FFA_MEMORY_OUTER_SHAREABLE
  | FFA_MEMORY_INNER_SHAREABLE.

  Definition FFA_MEMORY_SHARE_NON_SHAREABLE_Z := 0.
  Definition FFA_MEMORY_SHARE_RESERVED_Z := 1.
  Definition FFA_MEMORY_OUTER_SHAREABLE_Z := 2.
  Definition FFA_MEMORY_INNER_SHAREABLE_Z := 3.  

  Inductive FFA_MEMORY_TYPE :=
  | FFA_MEMORY_NOT_SPECIFIED_MEM
  | FFA_MEMORY_DEVICE_MEM (cacheability_type: FFA_MEMORY_CACHEABILITY_TYPE_2)
  | FFA_MEMORY_NORMAL_MEM (cacheability_type: FFA_MEMORY_CACHEABILITY_TYPE_1)
                          (shareability_type: FFA_MEMORY_SHAREABILITY)
  | FFA_MEMORY_MEM_RESERVED.
  
  Record FFA_memory_region_attributes_descriptor_struct :=
    mkFFA_memory_region_attributes_descriptor_struct {
        (** - bits[7:6]: Reserved (MBZ). *)
        (** - bits[5:4]: Memory type.
             * b’00: Not specified and must be ignored.
             * b’01: Device memory.
             * b’10: Normal memory.
             * b’11: Reserved. Must not be used. *)
        (** - bits[3:2]:
             * Cacheability attribute if bit[5:4] = b’10.
             - b’00: Reserved. Must not be used.
               b’01: Non-cacheable.
               b’10: Reserved. Must not be used.
               b’11: Write-Back.
             * Device memory attributes if bit[5:4] = b’01.
               b’00: Device-nGnRnE.
               b’01: Device-nGnRE.
               b’10: Device-nGRE.
               b’11: Device-GRE. *)
        (** - bits[1:0]:
             * Shareability attribute if bit[5:4] = b’10.
              b’00: Non-shareable.
              b’01: Reserved. Must not be used.
              b’10: Outer Shareable.
              b’11: Inner Shareable.
             * Reserved & MBZ if bit[5:4] = b’01. *)
        FFA_memory_region_attributes_descriptor_struct_memory_type : FFA_MEMORY_TYPE;
      }.

  Definition init_FFA_memory_region_attributes_descriptor_struct :=
    mkFFA_memory_region_attributes_descriptor_struct FFA_MEMORY_NOT_SPECIFIED_MEM.
  
  (** [JIEUNG: The following things need to be implemented in the transition rules] *)
  (** Memory region attributes are used in memory management transactions as follows.

      1. In a transaction to share memory with one or more Borrowers and to lend memory to more than one Borrower,
      - The Lender specifies the attributes that each Borrower must access the memory region with. This is
        done by invoking the FFA_MEM_SHARE or FFA_MEM_LEND ABIs. The same attributes are used for
        all Borrowers.
      - The Relayer validates the attributes specified by the Lender as follows. This is done in response to an
        invocation of the FFA_MEM_SHARE or FFA_MEM_LEND ABIs. The Relayer must return the DENIED
        error code if the validation fails.
        – At the Non-secure physical FF-A instance, an IMPLEMENTATION DEFINED mechanism is used.
        – At any virtual FF-A instance, if the endpoint is running in EL1 or S-EL1 in either Execution state,
          the attributes specified by the Lender are considered valid only if they are the same or less permissive
          than the attributes used by the Relayer in the stage 2 translation table descriptors for the memory
          region in one of the following translation regimes:
          * Secure EL1&0 translation regime, when S-EL2 is enabled.
          * Non-secure EL1&0 translation regime, when EL2 is enabled.
        – At the Secure virtual FF-A instance, if the endpoint is running in S-EL0 in either Execution state,
          the attributes specified by the Lender are considered valid only if they are either the same or less
          permissive than the attributes used by the Relayer in the stage 1 translation table descriptors for the
          memory region in one of the following translation regimes:
          * Secure EL1&0 translation regime, when EL2 is disabled.
          * Secure PL1&0 translation regime, when EL2 is disabled.
          * Secure EL2&0 translation regime, when Armv8.1-VHE is enabled.
        If the Borrower is an independent peripheral device, then the validated attributes are used to map the
        memory region into the address space of the device.
      - The Borrower (if a PE or Proxy endpoint) should specify the attributes that it would like to access the
        memory region with. This is done by invoking the FFA_MEM_RETRIEVE_REQ ABI.
      - The Relayer must validate the attributes specified by the Borrower (if a PE or Proxy endpoint) to ensure
        that they are the same or less permissive than the attributes that were specified by the Lender and
        validated by the Relayer. This is done in response to an invocation of the FFA_MEM_RETRIEVE_REQ
        ABI. The Relayer must return the DENIED error code if the validation fails.

      2. In a transaction to donate memory or lend memory to a single Borrower,
      - Whether the Owner/Lender is allowed to specify the memory region attributes that the Receiver must
        use to access the memory region depends on the type of Receiver.
      – If the Receiver is a PE or Proxy endpoint, the Owner must not specify the attributes.
      – If the Receiver is an independent peripheral device, the Owner could specify the attributes.
        The Owner must specify its choice in an invocation of the FFA_MEM_DONATE or FFA_MEM_LEND ABIs.
      - The values in the memory region attributes field specified by the Owner/Lender must be interpreted
        by the Relayer as follows. This is done in response to an invocation of the FFA_MEM_DONATE or
        FFA_MEM_LEND ABIs.
        – If the Receiver is a PE or Proxy endpoint, the Relayer must return INVALID_PARAMETERS if the
          value in bits[5:4] != b’00.
        – If the Receiver is an independent peripheral device and the value is not b’00, the Relayer must take
          one of the following actions.
          * Return DENIED if the attributes are determined to be invalid through an IMPLEMENTATION
            DEFINED mechanism.
          * Use the attributes specified by the Owner to map the memory region into the address space of the
            device.
        – If the Receiver is an independent peripheral device and the value is b’00, the Relayer must determine
          the attributes through an IMPLEMENTATION DEFINED mechanism.
      - The Receiver (if a PE or Proxy endpoint) should specify the memory region attributes it would like to
        use to access the memory region. This is done while invoking the FFA_MEM_RETRIEVE_REQ ABI.
      - The Relayer must validate the attributes specified by the Receiver (if a PE or Proxy endpoint) to ensure
        that they are the same or less permissive than the attributes determined by the Relayer through an
        IMPLEMENTATION DEFINED mechanism.
      
        This is done in response to an invocation of the FFA_MEM_RETRIEVE_REQ ABI. The Relayer must
        return the DENIED error code if the validation fails.

      3. The Relayer must specify the memory region attributes that were used to map the memory region
      in the translation regime of the Receiver or Borrower. This must be done while invoking the
      FFA_MEM_RETRIEVE_RESP ABI.
    
      4. In a transaction to relinquish memory that was lent to one or more Borrowers, the memory region must be
      mapped back into the translation regime of the Lender with the same attributes that were used at the start of the
      transaction to lend the memory region. This is done in response to an invocation of the FFA_MEM_RECLAIM ABI.
    *)
  
  (** Definitions from here are implementation specific definitions in Hafnium *)
  (* XXX: We may be able to remove them later *)
 (**
  #define FFA_DATA_ACCESS_OFFSET (0x0U)
  #define FFA_DATA_ACCESS_MASK ((0x3U) << FFA_DATA_ACCESS_OFFSET)
   
  #define FFA_INSTRUCTION_ACCESS_OFFSET (0x2U)
  #define FFA_INSTRUCTION_ACCESS_MASK ((0x3U) << FFA_INSTRUCTION_ACCESS_OFFSET)
   
  #define FFA_MEMORY_TYPE_OFFSET (0x4U)
  #define FFA_MEMORY_TYPE_MASK ((0x3U) << FFA_MEMORY_TYPE_OFFSET)
   
  #define FFA_MEMORY_CACHEABILITY_OFFSET (0x2U)
  #define FFA_MEMORY_CACHEABILITY_MASK ((0x3U) << FFA_MEMORY_CACHEABILITY_OFFSET)
   
  #define FFA_MEMORY_SHAREABILITY_OFFSET (0x0U)
  #define FFA_MEMORY_SHAREABILITY_MASK ((0x3U) << FFA_MEMORY_SHAREABILITY_OFFSET)
  *)

  Definition FFA_DATA_ACCESS_OFFSET_Z :=  0.
  Definition FFA_DATA_ACCESS_MASK_Z := Z.shiftl 3 FFA_DATA_ACCESS_OFFSET_Z.

  Definition FFA_INSTRUCTION_ACCESS_OFFSET_Z := 2.
  Definition FFA_INSTRUCTION_ACCESS_MASK_Z := Z.shiftl 3 FFA_INSTRUCTION_ACCESS_OFFSET_Z.

  Definition FFA_MEMORY_TYPE_OFFSET_Z := 4.
  Definition FFA_MEMORY_TYPE_MASK_Z := Z.shiftl 3 FFA_MEMORY_TYPE_OFFSET_Z.

  Definition FFA_MEMORY_CACHEABILITY_OFFSET_Z := 2.
  Definition FFA_MEMORY_CACHEABILITY_MASK_Z := Z.shiftl 3 FFA_MEMORY_CACHEABILITY_OFFSET_Z.

  Definition FFA_MEMORY_SHAREABILITY_OFFSET_Z := 0.
  Definition FFA_MEMORY_SHAREABILITY_MASK_Z := Z.shiftl 3 FFA_MEMORY_SHAREABILITY_OFFSET_Z.  
  
  (**
  #define ATTR_FUNCTION_SET(name, container_type, offset, mask)                \
          static inline void ffa_set_##name##_attr(container_type *attr,       \
          					 const enum ffa_##name perm) \
          {                                                                    \
          	*attr = ( *attr & ~(mask)) | ((perm << offset) & mask);       \
          }
   
  #define ATTR_FUNCTION_GET(name, container_type, offset, mask)      \
          static inline enum ffa_##name ffa_get_##name##_attr(       \
          	container_type attr)                               \
          {                                                          \
          	return (enum ffa_##name)((attr & mask) >> offset); \
          }
  ATTR_FUNCTION_SET(data_access, ffa_memory_access_permissions_t,
          	  FFA_DATA_ACCESS_OFFSET, FFA_DATA_ACCESS_MASK)
  ATTR_FUNCTION_GET(data_access, ffa_memory_access_permissions_t,
          	  FFA_DATA_ACCESS_OFFSET, FFA_DATA_ACCESS_MASK)
   
  ATTR_FUNCTION_SET(instruction_access, ffa_memory_access_permissions_t,
          	  FFA_INSTRUCTION_ACCESS_OFFSET, FFA_INSTRUCTION_ACCESS_MASK)
  ATTR_FUNCTION_GET(instruction_access, ffa_memory_access_permissions_t,
          	  FFA_INSTRUCTION_ACCESS_OFFSET, FFA_INSTRUCTION_ACCESS_MASK)
   
  ATTR_FUNCTION_SET(memory_type, ffa_memory_attributes_t, FFA_MEMORY_TYPE_OFFSET,
          	  FFA_MEMORY_TYPE_MASK)
  ATTR_FUNCTION_GET(memory_type, ffa_memory_attributes_t, FFA_MEMORY_TYPE_OFFSET,
          	  FFA_MEMORY_TYPE_MASK)
   
  ATTR_FUNCTION_SET(memory_cacheability, ffa_memory_attributes_t,
          	  FFA_MEMORY_CACHEABILITY_OFFSET, FFA_MEMORY_CACHEABILITY_MASK)
  ATTR_FUNCTION_GET(memory_cacheability, ffa_memory_attributes_t,
          	  FFA_MEMORY_CACHEABILITY_OFFSET, FFA_MEMORY_CACHEABILITY_MASK)
   
  ATTR_FUNCTION_SET(memory_shareability, ffa_memory_attributes_t,
          	  FFA_MEMORY_SHAREABILITY_OFFSET, FFA_MEMORY_SHAREABILITY_MASK)
  ATTR_FUNCTION_GET(memory_shareability, ffa_memory_attributes_t,
          	  FFA_MEMORY_SHAREABILITY_OFFSET, FFA_MEMORY_SHAREABILITY_MASK)
   *)

  (**
  #define FFA_MEMORY_HANDLE_ALLOCATOR_MASK \
          ((ffa_memory_handle_t)(UINT64_C(1) << 63))
  #define FFA_MEMORY_HANDLE_ALLOCATOR_HYPERVISOR \
          ((ffa_memory_handle_t)(UINT64_C(1) << 63))
   *)

  Definition FFA_MEMORY_HANDLE_ALLOCATOR_MASK_Z := Z.shiftl 1 63.
  Definition FFA_MEMORY_HANDLE_ALLOCATOR_HYPERVISOR_Z := Z.shiftl 1 63.

  Definition FFA_MEMORY_REGION_FLAG_CLEAR_Z := 1.
  
End FFA_DESCRIPTIONS.

(*************************************************************)
(** *                  FFA Structure                         *) 
(*************************************************************)
(** This one is related to the interface definitions in Section 11 of the document *)
(** The following definitions are not parts of Section 5 in the document. However, they are essential when 
    defining memory management interfaces. *)
Section FFA_STRUCTURES_AND_AUX_FUNCTIONS.
  (**
  Most A64 instructions operate on registers. The architecture provides 31 general purpose registers. 
  Each register can be used as a 64-bit X register (X0..X30), or as a 32-bit W register
  (W0..W30). These are two separate ways of looking at the same register. For example, this
  register diagram shows that W0 is the bottom 32 bits of X0, and W1 is the bottom 32 bits of X1:
   *)

  (** In Hafnium:
  In "src/arch/aarch64/inc/hf/arch/types.h" file, we defines vcpu.h, which defines all necessary registers
  for context switching (and ABIs). In here, we model contxt switchings as well, but only 
  focus on the smallest subset of the entire context 
  *)
  Definition reg_t := PMap.t Z.

  (**
  struct ffa_value {
          uint64_t func;
          uint64_t arg1;
          uint64_t arg2;
          uint64_t arg3;
          uint64_t arg4;
          uint64_t arg5;
          uint64_t arg6;
          uint64_t arg7;
  };
  *)
  
  Record FFA_value_type :=
    mkFFA_value_type{
        (** This one is actually a value in the register, but we only use that as a FFA_IDENTIFIER_TYPE *) 
        ffa_type : FFA_IDENTIFIER_TYPE;
        (* TODO: do we need to make a conversion from each arg into the corresponding descriptors? *)
        vals : ZMap.t Z
      }.
  
  (** default value *)
  Definition init_FFA_value_type := mkFFA_value_type FFA_IDENTIFIER_DEFAULT (ZMap.init 0).

  (** In Hafnium: Defined in "inc/hf/ffa_internal.h" *)
  Definition ffa_error (ffa_error_code: FFA_ERROR_CODE_TYPE) : FFA_value_type :=
    let error_z_value := 
        match ffa_error_code with
        | FFA_NOT_SUPPORTED => -1
        | FFA_INVALID_PARAMETERS => -2 
        | FFA_NO_MEMORY => -3
        | FFA_BUSY => -4
        | FFA_INTERRUPTED => -5
        | FFA_DENIED => -6
        | FFA_RETRY => -7
        | FFA_ABORTED => -8
        end in
    (mkFFA_value_type (FFA_RESULT_CODE_IDENTIFIER FFA_ERROR)
                      (ZMap.set 1 error_z_value (ZMap.init 0))). 

  (** In Hafnium: Defined in "inc/vmapi/hf/ffa.h" *)
  Definition ffa_mem_success (handle: Z) :=
    (mkFFA_value_type (FFA_RESULT_CODE_IDENTIFIER FFA_SUCCESS)
                      (ZMap.set 2 (Z.land handle ((Z.shiftl 1 32) - 1)%Z)
                                (ZMap.set 3 (Z.shiftr handle 32) (ZMap.init 0)))).

End FFA_STRUCTURES_AND_AUX_FUNCTIONS.

(*************************************************************)
(** *          transaction descriptors                       *)
(*************************************************************)
Section FFA_MEMORY_REGION_DESCRIPTOR.

  Context `{ffa_types_and_constants: FFA_TYPES_AND_CONSTANTS}.
  (*************************************************************)
  (** *  5.12 Lend, donate, and share transaction descriptor   *)
  (*************************************************************)
  
  (*************************************************************)
  (** * 5.12.4 Flags usage                                     *)
  (*************************************************************)

  (** This flag should be defined before defining ffa_memory_region descriptor *)
  (**
     - Flags are used to govern the behavior of a memory management transaction.

     5.12.4.1 Zero memory flag
     In some ABI invocations, the caller could set a flag to request the Relayer to zero a memory region. To do this, the
     Relayer must:
     - Map the memory region in its translation regime once it is not mapped in the translation regime of any other 
       FF-A component.

       The caller must ensure that the memory region fulfills the size and alignment requirements listed in 2.7
       Memory granularity and alignment to allow the Relayer to map this memory region. It must discover these
       requirements by invoking the FFA_FEATURES interface with the function ID of the FFA_RXTX_MAP
       interface (see 8.2 FFA_FEATURES).
       The Relayer must return INVALID_PARAMETERS if the memory region does not meet these requirements.

       - Zero the memory region and perform cache maintenance such that the memory regions contents are coherent
         between any PE caches, system caches and system memory.
       - Unmap the memory region from its translation regime before it is mapped in the translation regime of any
         other FF-A component.
   *)

  (** FFA_MEM_DONATE / FFA_MEM_LEND / FFA_MEM_SHARE 
      Table 5.20: Flags usage in FFA_MEM_DONATE, FFA_MEM_LEND and FFA_MEM_SHARE ABIs *)
  Record FFA_mem_default_flags_struct :=
    mkFFA_mem_default_flags_struct {
        (** Bit[0]
            Zero memory flag.
            * In an invocation of FFA_MEM_DONATE or FFA_MEM_LEND, this flag specifies
              if the memory region contents must be zeroed by the Relayer after the memory
              region has been unmapped from the translation regime of the Owner.
              - b’0: Relayer must not zero the memory region contents.
              - b’1: Relayer must zero the memory region contents.
            * MBZ in an invocation of FFA_MEM_SHARE, else the Relayer must return INVALID_PARAMETERS.
            * MBZ if the Owner has Read-only access to the memory region , else the Relayer must return DENIED. *)
        FFA_mem_default_flags_struct_zero_memory_flag: bool;
        (** Bit[1]
            Operation time slicing flag.
            * In an invocation of FFA_MEM_DONATE, FFA_MEM_LEND or
              FFA_MEM_SHARE, this flag specifies if the Relayer can time slice this operation.
              - b’0: Relayer must not time slice this operation.
              - b’1: Relayer can time slice this operation.
            *  MBZ if the Relayer does not support time slicing of memory management
              operations (see 12.2.3 Time slicing of memory management operations), else the
              Relayer must return INVALID_PARAMETERS. *)
        FFA_mem_default_flags_struct_operation_time_slicing_flag: bool;
        (** Bit[31:2] - Reserved (MBZ). *)
      }.
  
  (** FFA_MEM_RETRIEVE_REQ 
      Table 5.21: Flags usage in FFA_MEM_RETRIEVE_REQ ABI *)

  Inductive FFA_memory_management_transaction_type :=
  | MEMORY_MANAGEMENT_DEFAULT_TRANSACTION
  | MEMORY_MANAGEMENT_SHARE_TRANSACTION
  | MEMORY_MANAGEMENT_LEND_TRANSACTION
  | MEMORY_MANAGEMENT_DONATE_TRANSACTION.
  
  Record FFA_mem_relinquish_req_flags_struct :=
    mkFFA_mem_relinquish_req_flags_struct {
        (** Bit[0]
            Zero memory before retrieval flag.
            – In an invocation of FFA_MEM_RETRIEVE_REQ, during a transaction to lend or donate memory, 
              this flag is used by the Receiver to specify whether the memory
              region must be retrieved with or without zeroing its contents first.
              * b’0: Retrieve the memory region irrespective of whether the Sender requested
                the Relayer to zero its contents prior to retrieval.
              * b’1: Retrieve the memory region only if the Sender requested the Relayer to
                zero its contents prior to retrieval by setting the Bit[0] in Table 5.20).
            – MBZ in a transaction to share a memory region, else the Relayer must return
              INVALID_PARAMETER.
            – If the Sender has Read-only access to the memory region and the Receiver sets
              Bit[0], the Relayer must return DENIED.
            – MBZ if the Receiver has previously retrieved this memory region, else the Relayer
              must return INVALID_PARAMETERS (see 11.4.2 Support for multiple retrievals by
              a Borrower). *)
        FFA_mem_relinquish_req_flags_struct_zero_memory_before_retrieval_flag: bool;
        (** Bit[1]
            Operation time slicing flag.
            – In an invocation of FFA_MEM_RETRIEVE_REQ, this flag specifies if the Relayer can time slice this operation.
              * b’0: Relayer must not time slice this operation.
              * b’1: Relayer can time slice this operation.
            – MBZ if the Relayer does not support time slicing of memory management
              operations (see 12.2.3 Time slicing of memory management operations), else the
              Relayer must return INVALID_PARAMETERS. *)
        FFA_mem_relinquish_req_flags_struct_operation_time_slicing_flag: bool;
        (** Bit[2]
            Zero memory after relinquish flag.
            – In an invocation of FFA_MEM_RETRIEVE_REQ, this flag specifies whether the Relayer must zero the memory 
              region contents after unmapping it from the translation regime of the Borrower or if the Borrower crashes.
              * b’0: Relayer must not zero the memory region contents.
              * b’1: Relayer must zero the memory region contents.
            – If the memory region is lent to multiple Borrowers, the Relayer must clear memory region contents after 
              unmapping it from the translation regime of each Borrower, if any Borrower including the caller sets this flag.
            – This flag could be overridden by the Receiver in an invocation of FFA_MEM_RELINQUISH
              (see Flags field in Table 11.25).
            – MBZ if the Receiver has Read-only access to the memory region, else the Relayer  must return DENIED. 
              The Receiver could be a PE endpoint or a dependent peripheral device.
            – MBZ in a transaction to share a memory region, else the Relayer must return
              INVALID_PARAMETER. *)
        FFA_mem_relinquish_req_flags_struct_zero_memory_after_retrieval_flag: bool;
        (**  Bit[4:3]
             Memory management transaction type flag.
             – In an invocation of FFA_MEM_RETRIEVE_REQ, this flag is used by the Receiver
               to either specify the memory management transaction it is participating in or indicate
               that it will discover this information in the invocation of
               FFA_MEM_RETRIEVE_RESP corresponding to this request.
               * b’00: Relayer must specify the transaction type in FFA_MEM_RETRIEVE_RESP.
               * b’01: Share memory transaction.
               * b’10: Lend memory transaction.
               * b’11: Donate memory transaction.
             – Relayer must return INVALID_PARAMETERS if the transaction type specified by the
               Receiver is not the same as that specified by the Sender for the memory region
               identified by the Handle value specified in the transaction descriptor. *)
        FFA_mem_relinquish_req_flags_struct_memory_management_transaction_type_flag:
          FFA_memory_management_transaction_type;
        (** Bit[9:5]
            Address range alignment hint.
            – In an invocation of FFA_MEM_RETRIEVE_REQ, this flag is used by the Receiver to specify the boundary, 
              expressed as multiples of 4KB, to which the address ranges
              allocated by the Relayer to map the memory region must be aligned.
            – Bit[9]: Hint valid flag.
              * b’0: Relayer must choose the alignment boundary. Bits[8:5] are reserved and MBZ.
              * b’1: Relayer must use the alignment boundary specified in Bits[8:5].
            – Bit[8:5]: Alignment hint.
              * If the value in this field is n, then the address ranges must be aligned to the 2*n x 4KB boundary.
            – MBZ if the Receiver specifies the IPA or VA address ranges that must be used by the
              Relayer to map the memory region, else the Relayer must return
              INVALID_PARAMETERS.
            – Relayer must return DENIED if it is not possible to allocate the address ranges at the
              alignment boundary specified by the Receiver.
            – Relayer must return INVALID_PARAMETERS if a reserved value is specified by the Receiver. *)
        FFA_mem_relinquish_req_flags_struct_address_range_alignment_hint: (bool (** Bit[9] *) * Z (** Bit[8:5] *) )%type;
        (** Bit[31:10] - Reserved (MBZ) *)
      }.

  Definition init_FFA_mem_relinquish_req_flags_struct :=
     mkFFA_mem_relinquish_req_flags_struct false false false MEMORY_MANAGEMENT_DEFAULT_TRANSACTION (false, 0).

  (** FFA_MEM_RETRIEVE_RESP
      Table 5.22: Flags usage in FFA_MEM_RETRIEVE_RESP ABI *)
  Record FFA_mem_relinquish_resp_flags_struct :=
    mkFFA_mem_relinquish_resp_flags_struct {
        (** Bit[0]
            Zero memory before retrieval flag.
            – In an invocation of FFA_MEM_RETRIEVE_RESP during a transaction to lend or
              donate memory, this flag is used by the Relayer to specify whether the memory
              region was retrieved with or without zeroing its contents first.
              * b’0: Memory region was retrieved without zeroing its contents.
              * b’1: Memory region was retrieved after zeroing its contents.
            – MBZ in a transaction to share a memory region.
            – MBZ if the Sender has Read-only access to the memory region. *)
        zero_memory_before_retrieval_flag_in_FFA_mem_relinquish_resp_flags_struct: bool;
        (** Bit[2:1] - Reserved (MBZ). *)
        (** Bit[4:3]
            Memory management transaction type flag.
            – In an invocation of FFA_MEM_RETRIEVE_RESP, this flag is used by the Relayer
              to specify the memory management transaction the Receiver is participating in.
            * b’00: Reserved.
            * b’01: Share memory transaction.
            * b’10: Lend memory transaction.
            * b’11: Donate memory transaction.
            *)
        memory_management_transaction_type_flag_in_FFA_mem_relinquish_resp_flags_struct:
          FFA_memory_management_transaction_type;        
        (** Bit[31:5] - Reserved (MBZ). *)
      }.

  Definition init_FFA_mem_relinquish_resp_flags_struct :=
     mkFFA_mem_relinquish_resp_flags_struct false MEMORY_MANAGEMENT_DEFAULT_TRANSACTION.

  Inductive ffa_memory_region_flags_t :=
  | MEMORY_REGION_FLAG_DEFAULT
  | MEMORY_REGION_FLAG_NORMAL (flag: FFA_mem_default_flags_struct)
  | MEMORY_REGION_FLAG_RELINQUISH_REQ (flag: FFA_mem_relinquish_req_flags_struct)
  | MEMORY_REGION_FLAG_RELINQUISH_RESP (flag: FFA_mem_relinquish_resp_flags_struct).
  
  
  (** The following descriptor specifies the data structure that must be used by the 
      Owner/Lender and a Borrower/Receiver in a transaction to donate, lend or share a memory region. 
      It specifies the memory region description (see 5.10 Memory region description), 
      properties (see 5.11 Memory region properties) and other transaction attributes in an
      invocation of the following ABIs.
      - FFA_MEM_DONATE.
      - FFA_MEM_LEND.
      - FFA_MEM_SHARE.
      - FFA_MEM_RETRIEVE_REQ.
      - FFA_MEM_RETRIEVE_RESP.

      The interpretation of some fields in Table 5.19 depends on the ABI this table is used with. This variance in
      behavior is also specified in Table 5.19.
   *)


  (*************************************************************************)
  (** *  Table 5.19: Lend, donate or share memory transaction descriptor   *)
  (*************************************************************************)
  (** Table 5.19: Lend, donate or share memory transaction descriptor *)
  (** 
      Note that it is also used for retrieve requests and responses.

      struct ffa_memory_region {
              /**
               * The ID of the VM which originally sent the memory region, i.e. the
               * owner.
               */
              ffa_vm_id_t sender;
              ffa_memory_attributes_t attributes; - 5.11.4 Memory region attributes usage.
              /** Reserved field, must be 0. */
              uint8_t reserved_0;
              /** Flags to control behaviour of the transaction. */
              ffa_memory_region_flags_t flags; 
              ffa_memory_handle_t handle;
              /**
               * An implementation defined value associated with the receiver and the
               * memory region.
               */
              uint64_t tag;
              /** Reserved field, must be 0. */
              uint32_t reserved_1;
              /**
               * The number of `ffa_memory_access` entries included in this
               * transaction.
               */
              uint32_t receiver_count;
              /**
               * An array of `attribute_count` endpoint memory access descriptors.
               * Each one specifies a memory region offset, an endpoint and the
               * attributes with which this memory region should be mapped in that
               * endpoint's page table.
               */
              struct ffa_memory_access receivers[];
      };
   *)

  Record FFA_memory_region_struct :=
    mkFFA_memory_region_struct {
        FFA_memory_region_struct_sender : ffa_UUID_t; (** length: 2 bytes / offset: 0 bytes *)
        FFA_memory_region_struct_attributes :
          FFA_memory_region_attributes_descriptor_struct; (** length: 1 bytes / offset: 2 bytes *)
        (** Reserved (MBZ) - length: 1 bytes / offset: 3 bytes *)
        FFA_memory_region_struct_flags : ffa_memory_region_flags_t; (** length: 4 bytes / offset: 4 bytes *)
        (** 
           - This field must be zero (MBZ) in an invocation of the following ABIs.
             – FFA_MEM_DONATE.
             – FFA_MEM_LEND.
             – FFA_MEM_SHARE.
           - A successful invocation of each of the preceding ABIs returns a Handle (see 5.10.2 Memory region handle)
             to identify the memory region in the transaction.
           - The Sender must convey the Handle to the Receiver through a Partition message.
           - This field must be used by the Receiver to encode this Handle in an invocation of the FFA_MEM_RETRIEVE_REQ
             ABI.
           - A Relayer must validate this field in an invocation of the FFA_MEM_RETRIEVE_REQ ABI as follows.
             – Ensure that it holds a Handle value that was previously allocated and has not been reclaimed by the
               Owner.
             – Ensure that the Handle identifies a memory region that was shared, lent or donated to the Receiver.
             – Ensure that the Handle was allocated to the Owner specified in the Sender endpoint ID field of the
               transaction descriptor.
             It must return INVALID_PARAMETERS if the validation fails.
           - This field must be used by the Relayer to encode the Handle in an invocation of the FFA_MEM_RETRIEVE_RESP
             ABI.
        *)        
        FFA_memory_region_struct_handle : ffa_memory_handle_t; (** length: 8 bytes / offset: 8 bytes *)
        (** 
           This 64-bit field must be used to specify an IMPLEMENTATION DEFINED value associated with the transaction
           and known to participating endpoints.
           - The Sender must specify this field to the Relayer in an invocation of the following ABIs.
           – FFA_MEM_DONATE.
           – FFA_MEM_LEND.
           – FFA_MEM_SHARE.
             - The Sender must convey the Tag to the Receiver through a Partition message.
             - This field must be used by the Receiver to encode the Tag in an invocation of the FFA_MEM_RETRIEVE_REQ
               ABI.
             - The Relayer must ensure the Tag value specified by the Receiver is equal to the value that was specified by
               the Sender. It must return INVALID_PARAMETERS if the validation fails.
             - This field must be used by the Relayer to encode the Tag value in an invocation of the FFA_MEM_RETRIEVE_RESP
               ABI.
         *)
        FFA_memory_region_struct_tag : ffa_memory_region_tag_t; (** length : 8 bytes / offset 16 bytes *)
        (** Reserved (MBZ) - length: 4 bytes / offset: 24 bytes *)
        (** we ignored this by representing receivers as a list
           FFA_memory_region_struct_receiver_count : Z;  - length: 4 bytes / offset: 28 bytes
         *)
        FFA_memory_region_struct_receivers :
          list FFA_endpoint_memory_access_descriptor_struct;
        (** length: FFA_memory_region_struct_receiver_count * 16 bytes / 
            offset: 32 bytes *)
      }.

  Definition init_FFA_memory_region_struct :=
    mkFFA_memory_region_struct 0 init_FFA_memory_region_attributes_descriptor_struct
                               MEMORY_REGION_FLAG_DEFAULT 0 init_ffa_memory_region_tag nil.


  Fixpoint well_formed_FFA_memory_region_struct_receivers
           (access_descriptors: list FFA_endpoint_memory_access_descriptor_struct) :=
    match access_descriptors with
    | nil => true
    | hd::tl => well_formed_FFA_endpoint_memory_access_descriptor_struct hd &&
              well_formed_FFA_memory_region_struct_receivers tl
    end.
  
  (* TODO: need more constraints in here *)
  Definition well_formed_FFA_memory_region_struct
             (memory_region : FFA_memory_region_struct) :=
    well_formed_FFA_memory_region_struct_receivers (memory_region.(FFA_memory_region_struct_receivers)).
    

  (** The following value is a struct size of C, but it may not need in this high-level modeling *)
  Definition FFA_memory_region_struct_size := 36%Z.

  (*************************************************************************)
  (** *  Endpoint memory access descriptor array usage                     *)
  (*************************************************************************)
  (** [JIEUNG: similar to the previous usage descriptions, the following 
      things has to be defined as invariants] *)
  (** A Sender must use this field to specify one or more Receivers and the access permissions each should have on the
      memory region it is donating, lending or sharing through an invocation of one of the following ABIs.
      - FFA_MEM_DONATE.
      - FFA_MEM_LEND.
      - FFA_MEM_SHARE.

      The access permissions and flags are subject to validation at the virtual and physical FF-A instances as specified in
      5.11.3 Instruction access permissions usage, 5.11.2 Data access permissions usage and 5.11.1 ABI-specific flags
      usage.

      In a FFA_MEM_SHARE ABI invocation, the Sender could request the memory region to be mapped with different
      data access permission in its own translation regime. It must specify these permissions and its endpoint ID in a
      separate Endpoint memory access descriptor.

      A Sender must describe the memory region in a composite memory region descriptor (see Table 5.13) with the
      following non-exhaustive list of checks.
      - Ensure that the address ranges specified in the composite memory region descriptor do not overlap each other.
      - Total page count is equal to the sum of the Page count fields in each Constituent memory region descriptor.
     
     The offset to this descriptor from the base of Table 5.19 must be specified in the Offset field of the Endpoint
      memory access descriptor as follows.
      
      - In a FFA_MEM_DONATE ABI invocation,
        – The Endpoint memory access descriptor count field in the transaction descriptor must be set to 1. This
          implies that the Owner must specify a single Receiver endpoint in a transaction to donate memory.
        – The Offset field of the Endpoint memory access descriptor must be set to the offset of the composite
          memory region descriptor
      - In a FFA_MEM_LEND and FFA_MEM_SHARE ABI invocation,
        – The Endpoint memory access descriptor count field in the transaction descriptor must be set to a non-zero
          value. This implies that the Owner must specify at least a single Borrower endpoint in a transaction to
          lend or share memory.
        – The Offset field in the Endpoint memory access descriptor of each Borrower must be set to the offset of
          the composite memory region descriptor. This implies that all values of the Offset field must be equal.
   *)

  (** A Receiver must use this field to specify the access permissions it should have on the memory region being donated,
      lent or shared in an invocation of the FFA_MEM_RETRIEVE_REQ ABI. This is specified in 5.11.3 Instruction
      access permissions usage and 5.11.2 Data access permissions usage.
      - A Receiver could do this on its behalf if it is a PE endpoint.
      - A Receiver could do this on the behalf of its dependent peripheral devices if it is a proxy endpoint.

      A Receiver could specify the address ranges that must be used to map the memory region in its translation regime
      by describing them in a composite memory region descriptor. The Receiver must perform the same checks as a
      Sender. These checks are described in 5.12.3.1 Sender usage.
      
      The offset to this descriptor from the base of Table 5.19 must be specified in the Offset field of the corresponding
      endpoint memory access descriptor in the array. This implies that all values of the Offset field could be different
      from each other.

      A Receiver could let the Relayer allocate the address ranges that must be used to map the memory region in its
      translation regime and optionally provide an alignment hint (see Address range alignment hint in Table 5.21).
      
      The value 0 must be specified in the Offset field of the corresponding endpoint memory access descriptor in the
      array. This implies that the Handle specified in Table 5.19 must be used to identify the memory region (see 5.12.1
      Handle usage).
      A memory management transaction could be to lend or share memory with multiple Borrowers. The Receiver
      must use this field to specify:
      - The SEPIDs and data access permissions of any dependent peripheral devices (if any) that the Receiver is a
        proxy endpoint for. 
        If the Relayer must allocate the address ranges to map the memory region in the Stream endpoints, the value
        0 must be specified in the Offset field of the corresponding endpoint memory access descriptor in the array.
        If the Receiver specifies the address ranges to map the memory region in the Stream endpoints, then it must
        follow the preceding guidance to specify the address ranges that must be used to map the memory region in
        its translation regime.
      - The identity of any other Borrowers and their data access permissions on the memory region (see 5.11.2
        Data access permissions usage and 5.11.1 ABI-specific flags usage).
        The value 0 must be specified in the Offset field of the corresponding endpoint memory access descriptor in
        the array.
   *)

  (** A Relayer must validate the Endpoint memory access descriptor count and each entry in the Endpoint memory
      access descriptor array as follows.
      - The Relayer could support memory management transactions targeted to only a single Receiver endpoint.
        It must return INVALID_PARAMETERS if the Sender or Receiver specifies an Endpoint memory access
        descriptor count != 1.
      - It must ensure that these fields have been populated by the Sender as specified in 5.12.3.1 Sender usage in an
        invocation of any of the following ABIs.
        – FFA_MEM_DONATE.
        – FFA_MEM_LEND.
        – FFA_MEM_SHARE.
        The Relayer must return INVALID_PARAMETERS in case of an error.
      - It must ensure that the Endpoint ID field in each Memory access permissions descriptor specifies a valid
        endpoint. The Relayer must return INVALID_PARAMETERS in case of an error.
      - In an invocation of the FFA_MEM_RETRIEVE_REQ ABI,
        – It must ensure that these fields have been populated by the Receiver as specified in 5.12.3.2 Receiver
          usage.
        – If the memory region has been lent or shared with multiple Borrowers, the Relayer must ensure that the
          identity of each Borrower specified by the Receiver is the same as that specified by the Sender.
        – If one or more Borrowers are dependent peripheral devices, the Relayer must ensure that the Receiver is
          their proxy endpoint.
        – If the Receiver specifies the address ranges that must be used to map the memory region in its translation
          regime, the Relayer must ensure that the size of the memory region is equal to that specified by the
          Sender.
      
      The Relayer must return INVALID_PARAMETERS in case of an error.
      
      - It must validate the access permissions in the Memory access permissions descriptor in each Endpoint
        memory access descriptor as specified in 5.11.2 Data access permissions usage and 5.11.3 Instruction
        access permissions usage.
      
      A Relayer must use this field in an invocation of the FFA_MEM_RETRIEVE_RESP ABI in response to successful
      validation of a FFA_MEM_RETRIEVE_REQ ABI invocation as follows.
      - To specify the access permissions with which the memory region has been mapped in the translation regime
        of the Receiver.
      - A Receiver could let the Relayer allocate the address ranges to map the memory region. In this case, the
        Relayer must describe the address ranges in a composite memory region descriptor. The Relayer must
        perform the same checks as a Sender. These checks are described in 5.12.3.1 Sender usage.
        The offset to this descriptor from the base of Table 5.19 must be specified in the Offset field of the
        corresponding endpoint memory access descriptor in the array. This implies that all values of the Offset field
        could be different from each other.
      - A Receiver could specify the address ranges that must be used to map the memory region in its translation
        regime. The Relayer must specify the value 0 in the Offset field of the corresponding endpoint memory
        access descriptor in the array.
   *)
  
  (*************************************************************************)
  (** *  Table 11.25: Descriptor to relinquish a memory region             *)
  (*************************************************************************)  

  (** For Relinquish, One more additional tables are defined in Section 11. *)
  (** Table 11.25: Descriptor to relinquish a memory region
  struct ffa_mem_relinquish {
          ffa_memory_handle_t handle;
          ffa_memory_region_flags_t flags;
          uint32_t endpoint_count;
          ffa_vm_id_t endpoints[];
  };
   *)

  Record FFA_memory_relinquish_struct :=
    mkFFA_memory_relinquish_struct {
        (** Globally unique Handle to identify a memory region. *)
        FFA_memory_relinquish_struct_handle : ffa_memory_handle_t; (** length: 8 bytes / offset: 0 bytes *)
        (** Bit[0]: Zero memory after relinquish flag.
            – This flag specifies if the Relayer must clear memory region contents after unmapping it
              from from the translation regime of the Borrower.
              * b’0: Relayer must not zero the memory region contents.
              * b’1: Relayer must zero the memory region contents.
            – If the memory region was lent to multiple Borrowers, the Relayer must clear memory
              region contents after unmapping it from the translation regime of each Borrower, if any
              Borrower including the caller sets this flag.
            – MBZ if the memory region was shared, else the Relayer must return INVALID_PARAMETERS.
            – MBZ if the Borrower has Read-only access to the memory region, else the Relayer must return DENIED.
            – Relayer must fulfill memory zeroing requirements listed in 5.12.4 Flags usage.

            Bit[1]: Operation time slicing flag.
            – This flag specifies if the Relayer can time slice this operation.
              * b’0: Relayer must not time slice this operation.
              * b’1: Relayer can time slice this operation.
            - MBZ if the Relayer does not support time slicing of memory management operations
            (see 12.2.3 Time slicing of memory management operations). 

            Bit[31:2]: Reserved (MBZ). *)
        FFA_memory_relinquish_struct_flags : ffa_memory_region_flags_t;
        (** length: 3 bytes / offset: 8 bytes *)
        (** Count of endpoints. *)
        (** we ignored this one by representing endpoints as a list 
           FFA_mem_relinquish_struct_endpoint_count : Z; (* length: 4 bytes / offset: 12 bytes *) 
         *)
        (** Array of endpoint IDs. Each entry contains a 16-bit ID. *)
        FFA_memory_relinquish_struct_endpoints : list ffa_UUID_t;
        (** length: FFA_mem_relinquish_struct_endpoint_count * 2 bytes / offset: 16 bytes *)
      }.

  Definition init_FFA_mem_relinquish_struct :=
    mkFFA_memory_relinquish_struct 0 MEMORY_REGION_FLAG_DEFAULT nil.

  (* TODO: need more constraints in here *)
  Definition well_formed_FFA_memory_relinquish_struct
             (memory_region : FFA_memory_relinquish_struct) := true.
  
End FFA_MEMORY_REGION_DESCRIPTOR.

