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

(*************************************************************)
(*                 FFA function keyword                      *) 
(*************************************************************)
Section FFA_DATATYPES.
  

  (* This section provides FFA memory management related definitions, which can be mostly observed 
     in the Arm Firmware Framework for Armv8-A (https://developer.arm.com/documentation/den0077/latest) 
     document. 
  *)

  (* The following numbers are defined in Chapter 11 (Memory management interfaces document) 
   #define FFA_MEM_DONATE_32            0x84000071 - Defined in Table 11.3 FFA_MEM_DONATE function syntax
   #define FFA_MEM_LEND_32              0x84000072 - Defined in Table 11.8 FFA_MEM_LEND function syntax
   #define FFA_MEM_SHARE_32             0x84000073 - Defined in Table 11.13: FFA_MEM_SHARE function syntax
   #define FFA_MEM_RETRIEVE_REQ_32      0x84000074 - Defined in Table 11.18 FFA_MEM_RETRIEVE_REQ function syntax
   #define FFA_MEM_RETRIEVE_RESP_32     0x84000075 - Defined in Table 11.22: FFA_MEM_RETRIEVE_RESP function syntax
   #define FFA_MEM_RELINQUISH_32        0x84000076 - Defined in Table 11.27: FFA_MEM_RELINQUISH function syntax
   #define FFA_MEM_RECLAIM_32           0x84000077 - Defined in Table 11.31: FFA_MEM_RECLAIM function syntax
   *)
  
  Definition FFA_MEM_DONATE_32 : Z := 2214592625.
  Definition FFA_MEM_LEND_32 : Z := 2214592626.
  Definition FFA_MEM_SHARE_32 : Z := 2214592627.
  Definition FFA_MEM_RELINQUISH_32 : Z := 2214592630.
  Definition FFA_MEM_RETRIEVE_REQ_32 : Z := 2214592631.
  Definition FFA_MEM_RETRIEVE_RESP_32 : Z := 2214592632.
  Definition FFA_MEM_RELINGQUISH_32 : Z := 2214592633.
  Definition FFA_MEM_RECLAIM_32 : Z := 2214592634.

  Inductive FFA_FUNCTION_TYPE :=
  | FFA_MEM_DONATE
  | FFA_MEM_LEND
  | FFA_MEM_SHARE
  | FFA_MEM_RELINQUISH
  | FFA_MEM_RETREIVE_REQ
  | FFA_MEM_RETREIVE_RESP
  | FFA_MEM_RELINGQUISH
  | FFA_MEM_RECLAIM.


  (* The followings are for return values of FFA interface calls. *)
  (* The following numbers are defined in Chapter 7, especially in Table 7.2: Error status codes
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
  
  (* The following numbers are also defined in Chapter 7
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


  (* This version only focus on two FFA interfaces, memory management related interfaces and interfaces for 
     the result of memory management related parts *) 
  Inductive FFA_IDENTIFIER_TYPE :=
  | FFA_IDENTIFIER_DEFAULT
  | FFA_FUNCTION_IDENTIFIER (func: FFA_FUNCTION_TYPE)
  | FFA_RESULT_CODE_IDENTIFIER (func: FFA_RESULT_CODE_TYPE).

End FFA_DATATYPES.


(*************************************************************)
(*          Constant values that are used in FFA             *) 
(*************************************************************)
Section FFA_CONSTANTS.
  
  (* The following options are for message send and receive. So we ignore them in the current setting 
  /* FF-A function specific constants. */
  #define FFA_MSG_RECV_BLOCK 0x1
  #define FFA_MSG_RECV_BLOCK_MASK 0x1 

  #define FFA_MSG_SEND_NOTIFY 0x1
  #define FFA_MSG_SEND_NOTIFY_MASK 0x1

  #define FFA_SLEEP_INDEFINITE 0
  *)

  (* This one is used as a flag value for reclaim (FFA_MEM_RECLAIM). 
  #define FFA_MEM_RECLAIM_CLEAR 0x1
   *)
  
  Definition FFA_MEM_RECLAIM_CLEAR := 1.

  (*
  /** 
   * For use where the FF-A specification refers explicitly to '4K pages'. Not to
   * be confused with PAGE_SIZE, which is the translation granule Hafnium is
   * configured to use.
   */
  #define FFA_PAGE_SIZE 4096

  /* The maximum length possible for a single message. */
  #define FFA_MSG_PAYLOAD_MAX HF_MAILBOX_SIZE
  *)
  Definition FFA_PAGE_SIZE := 4096.
  Definition HF_MAILBOX_SIZE := 4096.
  Definition FFA_MSG_PAYLOAD_MAX := HF_MAILBOX_SIZE.

End FFA_CONSTANTS.

Section FFA_TYPE_ALAISING.

  Definition ffa_address_t := Z.
  Definition ffa_vm_id_t := Z.
  Definition ffa_vcpu_index_t := Z.
  Definition ffa_hafnium_id_t := Z.
  Definition ffa_memory_handle_t := Z.
  Definition ffa_memory_access_permissions_t := Z.
  Definition ffa_memory_attributes_t := Z.
  Definition ffa_memory_receiver_flags_t := Z.
  Definition ffa_memory_region_flags_t := Z.

End FFA_TYPE_ALAISING.

(*************************************************************)
(*                       Descriptors                         *) 
(*************************************************************)
Section FFA_DESCRIPTIONS.

  (***********************************************************************)
  (*  Constituent memory region and composite_memory_region descriptors  *) 
  (***********************************************************************)  
  (* We define descriptors that are used in FFA interfaces. Sender, Relayer, and Borrower use them 
     to figure out the information and check validity of the query by using them *) 
     
  (* Table 5.14: Constituent memory region descriptor
  /**
   * A set of contiguous pages which is part of a memory region. This corresponds
   * to table 40 of the FF-A 1.0 EAC specification, "Constituent memory region
   * descriptor".
   */
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
   *)

  Record FFA_memory_region_constituent_struct :=
    mkFFA_memory_region_constituent_struct {
        FFA_memory_region_constituent_struct_address : ffa_address_t; (* length: 8 bytes / offset: 0 bytes *)
        FFA_memory_region_constituent_struct_page_count : Z; (* length: 4 bytes / offset: 4 bytes *)
        (* reserved MBZ *) (* length: 4 bytes / offset: 12 byte *) 
      }.

  (* Table 5.13: Composite memory region descriptor
  /**
   * A set of pages comprising a memory region. This corresponds to table 39 of
   * the FF-A 1.0 EAC specification, "Composite memory region descriptor".
   */
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

  Record FFA_composite_memory_region_struct :=
    mkFFA_composite_memory_region_struct {
        FFA_composite_memory_region_struct_page_count : Z; (* length: 4 bytes / offset: 0 bytes  *)
        FFA_composite_memory_region_struct_constituent_count : Z; (* length: 4 bytes / offset: 4 bytes  *)
        (* reserved *) (* legnth: 8 bytes / offset: 8 bytes *)
        FFA_composite_memory_region_struct_constituents :
          ZTree.t FFA_memory_region_constituent_struct
                 (* length: 16 bytes * num of elements / offset: 16 bytes *)
      }.

  (***********************************************************************)
  (*                         Memory region handle                        *) 
  (***********************************************************************)  
  (* Handle : 64-bit, and the handle is allocated by teh replayer 
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

  (***********************************************************************)
  (*  Constituent memory region and composite_memory_region descriptors  *) 
  (***********************************************************************)
  
  (* From here, most parts are related to 5.11 Memory region properties. *)
  (* - Instruction and data access permissions describe the type of access permitted on the memory region.
     - One or more endpoint IDs that have access to the memory region specified by a combination of access
       permissions and memory region attributes.
     - Memory region attributes control the memory type, accesses to the caches, and whether 
       the memory region is Shareable and therefore is coherent. *)
  
  (* ffa data access and instruction access permission values are used in the memory access
     permissions descriptor (In Table 5.15: Memory access permissions descriptor). 
   *)


  (* Table 5.15: Memory access permissions descriptor *)
  (*
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

  (* Execute permission is more permissive than Execute-never permission. 
     - 5.11.3 Instruction access permissions usage *)  
  Inductive FFA_INSTRUCTION_ACCESS_TYPE :=
  | FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED
  | FFA_INSTRUCTION_ACCESS_NX
  | FFA_INSTRUCTION_ACCESS_X
  | FFA_INSTRUCTION_ACCESS_RESERVED.
  
  (*
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

  (* Read-write permission is more permissive than Read-only permission. 
     - 5.11.2 Data access permissions usage shows invariants about this fields *)
  Inductive FFA_DATA_ACCESS_TYPE :=
  | FFA_DATA_ACCESS_NOT_SPECIFIED
  | FFA_DATA_ACCESS_RO
  | FFA_DATA_ACCESS_RW
  | FFA_DATA_ACCESS_RESERVED.

 (*
  /** Flags to indicate properties of receivers during memory region retrieval. */
  typedef uint8_t ffa_memory_receiver_flags_t;
   
  /**
   * This corresponds to table 41 of the FF-A 1.0 EAC specification, "Memory
   * access permissions descriptor". - The name is somewhat wierd. I changed the name for my impl.
   */
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
  Record FFA_memory_access_permissions_descriptor_struct :=
    mkFFA_memory_access_permissions_descriptor_struct {
        FFA_memory_access_permissions_descriptor_struct_receiver :
          ffa_vm_id_t; (* length: 2 bytes / offset: 0 bytes *)
        (* memory access permissions: length: 1 bytes / offset: 2 bytes -
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
        (* the flag value is only used for "FFA_MEM_RETRIEVE_REQ / FFA_MEM_RETRIEVE_RESP". For 
           "FFA_MEM_DONATE / FFA_MEM_LEND / FFA_MEM_SHARE" this field is empty *)
        (* Bit[0]: Non-retrieval Borrower flag.
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
  
  (* Table 5.16: Endpoint memory access descriptor *)
  (*
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
          FFA_memory_access_permissions_descriptor_struct; (* length: 4 bytes / offset: 0 bytes *)

        (* NOTE: In Hafnium and FF-A document, the following field is defined as an offset 
           to point out the memory region that contains "FFA_composite_memory_region". 
           Instead of following them, we explicitly map "FFA_composite_memory_region_struct" 
           in here with option type to handle the case when offset points out NULL *)
        FFA_memory_access_descriptor_struct_composite_memory_region_offset :
        (* memory region struct is created and destroyed when hypervisor starts/finishes 
           their handling. Instead of merging it into  *)
          option FFA_composite_memory_region_struct;
        (* NOTE: the original size of the above offset value is as follows *)
        (* length: 4 bytes / offset: 4 bytes *)
        (* Reserved (MBZ) *) (* length: 8 bytes / offset: 8 bytes *)
      }.
  

  (**************************************************)
  (* 5.11.4 Memory region attributes usage          *)
  (**************************************************)
  (* Memory type : – Device-nGnRnE < Device-nGnRE < Device-nGRE < Device-GRE < Normal.
     Cacheability attribute : – Non-cacheable < Write-Back Cacheable.
     Shareability attribute : - – Non-Shareable < Inner Shareable < Outer shareable. *)
  (* length : 1 bytes *)
  (* More details can be found in 5.11.4 Memory region attributes usage *)
  (*
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

  (* The followings are values for 
  enum ffa_memory_type {
          FFA_MEMORY_NOT_SPECIFIED_MEM,
          FFA_MEMORY_DEVICE_MEM,
          FFA_MEMORY_NORMAL_MEM,
  };
   *)

  Definition FFA_MEMORY_NOT_SPECIFIED_MEM_Z := 0.
  Definition FFA_MEMORY_DEVICE_MEM_Z := 1.
  Definition FFA_MEMORY_NORMAL_MEM_Z := 2.
  
  (*
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
        (* - bits[7:6]: Reserved (MBZ). *)
        (* - bits[5:4]: Memory type.
             * b’00: Not specified and must be ignored.
             * b’01: Device memory.
             * b’10: Normal memory.
             * b’11: Reserved. Must not be used. *)
        (* - bits[3:2]:
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
        (* - bits[1:0]:
             * Shareability attribute if bit[5:4] = b’10.
              b’00: Non-shareable.
              b’01: Reserved. Must not be used.
              b’10: Outer Shareable.
              b’11: Inner Shareable.
             * Reserved & MBZ if bit[5:4] = b’01. *)
        FFA_memory_region_attributes_descriptor_struct_memory_type : FFA_MEMORY_TYPE;
      }.

 (*
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
  Definition FFA_DATA_ACCESS_MASK_Z :=  Z.shiftl 3 FFA_DATA_ACCESS_OFFSET_Z.

  Definition FFA_INSTRUCTION_ACCESS_OFFSET_Z := 2.
  Definition FFA_INSTRUCTION_ACCESS_MASK_Z := Z.shiftl 3 FFA_INSTRUCTION_ACCESS_OFFSET_Z.

  Definition FFA_MEMORY_TYPE_OFFSET_Z := 4.
  Definition FFA_MEMORY_TYPE_MASK_Z := Z.shiftl 3 FFA_MEMORY_TYPE_OFFSET_Z.

  Definition FFA_MEMORY_CACHEABILITY_OFFSET_Z := 2.
  Definition FFA_MEMORY_CACHEABILITY_MASK_Z := Z.shiftl 3 FFA_MEMORY_CACHEABILITY_OFFSET_Z.

  Definition FFA_MEMORY_SHAREABILITY_OFFSET_Z := 0.
  Definition FFA_MEMORY_SHAREABILITY_MASK_Z := Z.shiftl 3 FFA_MEMORY_SHAREABILITY_OFFSET_Z.  
  
  (*
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

  (* 
  #define FFA_MEMORY_HANDLE_ALLOCATOR_MASK \
          ((ffa_memory_handle_t)(UINT64_C(1) << 63))
  #define FFA_MEMORY_HANDLE_ALLOCATOR_HYPERVISOR \
          ((ffa_memory_handle_t)(UINT64_C(1) << 63))
   *)

  Definition FFA_MEMORY_HANDLE_ALLOCATOR_MASK_Z := Z.shiftl 1 63.
  Definition FFA_MEMORY_HANDLE_ALLOCATOR_HYPERVISOR_Z := Z.shiftl 1 63.
  
End FFA_DESCRIPTIONS.

(*************************************************************)
(*                     FFA Structure                         *) 
(*************************************************************)
(* This one is related to the interface definitions in Section 11 of the document *) 
Section FFA_STRUCTURES_AND_AUX_FUNCTIONS.
  (*
  Most A64 instructions operate on registers. The architecture provides 31 general purpose registers. 
  Each register can be used as a 64-bit X register (X0..X30), or as a 32-bit W register
  (W0..W30). These are two separate ways of looking at the same register. For example, this
  register diagram shows that W0 is the bottom 32 bits of X0, and W1 is the bottom 32 bits of X1:
  
  In "src/arch/aarch64/inc/hf/arch/types.h" file, we defines vcpu.h, which defines all necessary registers
  for context switching (and ABIs). In here, we model contxt switchings as well, but only 
  focus on the smallest subset of the entire context 
  *)
  Definition reg_t := PMap.t Z.

  (* 
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
        (* This one is actually a value in the register, but we only use that as a FFA_IDENTIFIER_TYPE *) 
        share_function : FFA_IDENTIFIER_TYPE;
        (* TODO: do we need to make a conversion from each arg into the corresponding descriptors? *)
        vals : ZMap.t Z
      }.

  (* default value *)
  Definition init_FFA_value_type := mkFFA_value_type FFA_IDENTIFIER_DEFAULT (ZMap.init 0).

End FFA_STRUCTURES_AND_AUX_FUNCTIONS.

(*************************************************************)
(*          transaction descriptors                          *)
(*************************************************************)
Section FFA_MEMORY_REGION_DESCRIPTOR.

  (*************************************************************)
  (*    5.12 Lend, donate, and share transaction descriptor    *)
  (*************************************************************)

  (* Table 5.19: Lend, donate or share memory transaction descriptor *)
  (* Note that it is also used for retrieve requests and responses.
  struct ffa_memory_region {
          /**
           * The ID of the VM which originally sent the memory region, i.e. the
           * owner.
           */
          ffa_vm_id_t sender;
          ffa_memory_attributes_t attributes;
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
        FFA_memory_region_struct_sender : ffa_vm_id_t; (* length: 2 bytes / offset: 0 bytes *)
        FFA_memory_region_struct_attributes :
          FFA_memory_region_attributes_descriptor_struct; (* length: 1 bytes / offset: 2 bytes *)
        (* Reserved (MBZ) *) (* length: 1 bytes / offset: 3 bytes *)
        (* TODO: Need to modify flags based on the 5.12.4 Flags usage *)
        FFA_memory_region_struct_flags : ffa_memory_region_flags_t; (* length: 4 bytes / offset: 4 bytes *)
        FFA_memory_region_struct_handle : ffa_memory_handle_t; (* length: 8 bytes / offset: 8 bytes *)
        FFA_memory_region_struct_tag : Z; (* length : 8 bytes / offset 16 bytes *)
        (* Reserved (MBZ) *) (* length: 4 bytes / offset: 24 bytes *)
        FFA_memory_region_struct_receiver_count : Z; (* length: 4 bytes / offset: 28 bytes *)
        FFA_memory_region_struct_receivers :
          ZTree.t FFA_endpoint_memory_access_descriptor_struct;
        (* length: FFA_memory_region_struct_receiver_count * 16 bytes / 
           offset: 32 bytes *)                             
      }.

  (* Table 11.25: Descriptor to relinquish a memory region
  struct ffa_mem_relinquish {
          ffa_memory_handle_t handle;
          ffa_memory_region_flags_t flags;
          uint32_t endpoint_count;
          ffa_vm_id_t endpoints[];
  };
   *)

  Record FFA_mem_relinquish_struct :=
    {
    FFA_mem_relinquish_struct_handle : ffa_memory_handle_t; (* length: 8 bytes / offset: 0 bytes *)
    FFA_mem_relinquish_struct_flags : ffa_memory_region_flags_t; (* length: 3 bytes / offset: 8 bytes *)
    FFA_mem_relinquish_struct_endpoint_count : Z; (* length: 4 bytes / offset: 12 bytes *)
    FFA_mem_relinquish_struct_endpoints : ZTree.t ffa_vm_id_t;
    (* length: FFA_mem_relinquish_struct_endpoint_count * 2 bytes / offset: 16 bytes *)
    }.


End FFA_MEMORY_REGION_DESCRIPTOR.


(*************************************************************)
(*         State definitions                                 *)
(*************************************************************)
Section PtrTreeLibrary.

Definition PtrTree_set (ptr: positive * Z) (v: positive) (map: PTree.t (ZTree.t positive)) :=
  let zt := match PTree.get (fst ptr) map with
            | Some zt => zt
            | None => (ZTree.empty positive)
            end in
  PTree.set (fst ptr) (ZTree.set (snd ptr) v zt) map
.

Definition PtrTree_get (ptr: positive * Z) (map: PTree.t (ZTree.t positive)) :=
  zt <- PTree.get (fst ptr) map;;
  ZTree.get (snd ptr) zt
.

Definition PtrTree_remove (ptr: positive * Z) (map: PTree.t (ZTree.t positive)) :=
  match PTree.get (fst ptr) map with
  | Some zt => PTree.set (fst ptr) (ZTree.remove (snd ptr) zt) map
  | None => map
  end
.

End PtrTreeLibrary.

Variable Z_to_string: Z -> string.
Extract Constant Z_to_string =>
"fun z -> (HexString.of_Z z)"
.

(* Variable A: Type. *)
Definition A : Type := positive * Z.

Definition A_to_string (a: A): string :=
  "(" ++ (Z_to_string (Zpos' (fst a))) ++ ", " ++ (Z_to_string (snd a)) ++ ")"
.



(* it is actually Z type, but we define this type for better readability *)
Definition ffa_entity_id_t : Type := Z. 

(*
Definition ffa_entity_id_t : Type :=ffa_vm_id_t + ffa_hafnium_id_t.
(* boilerplate: convert vm_ids and hafnium_id to entity_id if needed *)
Local Definition inl_entity : ffa_vm_id_t -> ffa_entity_id_t
  := @inl ffa_vm_id_t ffa_hafnium_id_t.
Local Definition inr_entity : ffa_hafnium_id_t -> ffa_entity_id_t
  := @inr ffa_vm_id_t ffa_hafnium_id_t.
Local Coercion inl_entity : ffa_vm_id_t >-> ffa_entity_id_t.
Local Coercion inr_entity : ffa_hafnium_id_t >-> ffa_entity_id_t.
Hint Unfold inl_entity inr_entity.
Set Printing Coercions.
 *)

(*************************************************************)
(*         memory and ptable                                 *)
(*************************************************************)
Section MEM_AND_PTABLE.
  
  (* memory states on memory addresses *)
  (* We do not consider contents inside the memory, but we do care about its properties -
     and those properties are necessary for us to prove whether each component in the system
     accesses memory in a valid way. Therefore, we have the following mapping from
     each memory address to several properties. 

     There are several dependencies between those properties. 
     So, Those information are somewhat redundant, but 
     we keep them in terms of explicit information that we can easily infer the curretn state of 
     each address in the memory. To handle them, 
     we also introduce a function variable, which we can fill out later *)
  Inductive OwnershipState :=
  | Owned (id : ffa_entity_id_t)
  | NotOwned.
  
  Inductive AccessState :=
  | NoAccess
  | HasAccess (owner: ffa_entity_id_t) (borrowers : list ffa_entity_id_t).

  Inductive MemAttributes :=
  | MemAttributes_UNDEF
  | MemAttributes_DeviceMem (cacheability_type: FFA_MEMORY_CACHEABILITY_TYPE_2)
  | MemAttributes_NormalMem (cacheability_type: FFA_MEMORY_CACHEABILITY_TYPE_1)
                            (shareability_type: FFA_MEMORY_SHAREABILITY).

  Inductive MemDirty := 
  | MemClean
  | MemWritten (writer: ffa_entity_id_t).
      
  Record MemProperties :=
    mkMemProperties {
        (* there can be only one owner *)
        owned_by : OwnershipState;
        (* access information *)
        accessible_by : AccessState;
        (* instruction and data access property *)
        instruction_access_property : FFA_INSTRUCTION_ACCESS_TYPE;
        data_access_property: FFA_DATA_ACCESS_TYPE;
        (* memory attributes *)
        mem_attribute : MemAttributes;
        mem_dirty: MemDirty;
    }.

  (* In top level, we do not need to specify ptable in detail. 
     In this sense, we try to abstract the definition of ptable. 
     => gets the input address (e.g., va or ipa) and return the address (e.g., ipa or pa) *)
  Class AddressTranslation :=
    {
    (* address translation funciton in ptable. There are two possible cases 
       1. provides the entire address translation from 
       the root level to the bottom level 
       2. provides the only one level address translation. 
       Among them, our high-level model assumes the following ptable uses the second approach *)
    hafnium_address_translation_table
      (input_addr:  ffa_address_t) : option ffa_address_t;
    vm_address_translation_table
      (vm_id : ffa_vm_id_t)  (input_addr: ffa_address_t) : option ffa_address_t;
    }.
 
  Class HafniumMemoryManagementContext `{address_translation: AddressTranslation} :=
    {
    (* address low and high *)
    address_low : ffa_address_t;
    address_high : ffa_address_t;
    (* alignment_value : Z; (* usually 4096 *) *)
    alignment_value : Z := 4096;
    alignment_value_non_zero_prop :
      alignment_value > 0;
    address_low_alignment_prop :
      (Z.modulo address_low alignment_value)%Z = 0;
    address_high_alignment_prop :
      (Z.modulo address_high alignment_value)%Z = 0;

    (* all results of  the address translation needs to be in betweeen low and high *)
    address_translation_table_prop :
      forall addr,
        match hafnium_address_translation_table addr with
        | Some addr' => (address_low <= addr' <= address_high)
        | _ => True
        end;
    (* TODO: add more invariants *)    
    }.

End MEM_AND_PTABLE.

(*************************************************************)
(*         VM context                                        *)
(*************************************************************)
(* This one is necessary to model context saving/restoring of FFA ABI - Related definitions are in
   1) "/inc/hf/vm.h"
   2) "/inc/hf/.h"
   2) "/src/arch/aarch64/inc/hf/arch/types.h" 
*)
Section FFA_VM_CONTEXT.


  (* registers in "/src/arch/aarch64/inc/hf/arch/types.h" 
  /** Type to represent the register state of a vCPU. */
  struct arch_regs {
          /* General purpose registers. */
          uintreg_t r[NUM_GP_REGS];
          uintreg_t pc;
          uintreg_t spsr;
  *)

  (* VM struct in "/inc/hf/vm.h" 
   struct vm {
           ffa_vm_id_t id;
           struct smc_whitelist smc_whitelist;
    
           /** See api.c for the partial ordering on locks. */
           struct spinlock lock;
           ffa_vcpu_count_t vcpu_count;
           struct vcpu vcpus[MAX_CPUS];
           struct mm_ptable ptable;
           struct mailbox mailbox;
           char log_buffer[LOG_BUFFER_SIZE];
           uint16_t log_buffer_length;
    
           /**
            * Wait entries to be used when waiting on other VM mailboxes. See
            * comments on `struct wait_entry` for the lock discipline of these.
            */
           struct wait_entry wait_entries[MAX_VMS];
    
           atomic_bool aborting;
    
           /** Arch-specific VM information. */
           struct arch_vm arch;
   };
   *)

  (* Simplified vcpu context - we only includes some registers - actually only FFA related values *)
  Record ArchRegs :=
    mkArchRegs {
        regs: FFA_value_type;
      }.

  Record VCPU_struct :=
    mkVCPU{
        vcpu_regs: ArchRegs;
      }.     
  
  (* Simplified VM context - we assume VM only has own vcpu *)
  Record VM_struct :=
    mkVM_struct {
        cur_vcpu_id : Z;
        vcpu_num: Z;
        vcpu_struct : ZTree.t VCPU_struct;
        (* all other parts are ignored at this moment *)
        (* ptable for each VM is defined in AddressTranslation class *)
      }.

  Class VMContext := 
    {
    vcpu_max_num : Z;
    vcpu_num_prop (vm: VM_struct) : 0 < vm.(vcpu_num) <= vcpu_max_num;
    cur_vcpu_id_prop (vm: VM_struct) : 0 <= vm.(cur_vcpu_id) < vm.(vcpu_num);
    (* TODO: add more invariants *)    
    }.
    
End FFA_VM_CONTEXT.

(*************************************************************)
(*                             VM Clients                    *)
(*************************************************************)
(* Adding several things in here is possible, but we focus on 
   FFA-related things in this VM clinets. We are able to add
   any other things according to our decision *)
Section VM_CLIENTS.

  Record VM_CLIENT_struct :=
    mkVMClinet_struct {
        client_cur_vcpu_id : Z;
        client_vcpu_num: Z;
        client_vcpu_struct : ZTree.t VCPU_struct;
      }.
  
End VM_CLIENTS.

(*************************************************************)
(*         AbstractState for FFA modeling                    *)
(*************************************************************)
Section AbstractState.
  
  (* Hafnium specific values *)
  (*
  /** The maximum number of recipients a memory region may be sent to. */
  #define MAX_MEM_SHARE_RECIPIENTS 1
   
  /**
   * The maximum number of memory sharing handles which may be active at once. A
   * DONATE handle is active from when it is sent to when it is retrieved; a SHARE
   * or LEND handle is active from when it is sent to when it is reclaimed.
   */
  #define MAX_MEM_SHARES 100
   *)

  Definition MAX_MEM_SHARE_RECIPIENTS_Z := 1.
  Definition MAX_MEM_SHARE_Z := 100.
   
  (*
  struct ffa_memory_share_state {
          /**
           * The memory region being shared, or NULL if this share state is
           * unallocated.
           */
          struct ffa_memory_region *memory_region;
   
          /**
           * The FF-A function used for sharing the memory. Must be one of
           * FFA_MEM_DONATE_32, FFA_MEM_LEND_32 or FFA_MEM_SHARE_32 if the
           * share state is allocated, or 0.
           */
          uint32_t share_func;
   
          /**
           * Whether each recipient has retrieved the memory region yet. The order
           * of this array matches the order of the attribute descriptors in the
           * memory region descriptor. Any entries beyond the attribute_count will
           * always be false.
           */
          bool retrieved[MAX_MEM_SHARE_RECIPIENTS];
  };
   
  static struct ffa_memory_share_state share_states[MAX_MEM_SHARES];
 *)

  Record FFA_memory_share_state_struct :=
    mkFFA_memory_share_state_struct {
        memory_region : FFA_memory_region_struct;
        share_func : FFA_FUNCTION_TYPE;
        retrieved : ZTree.t bool;
      }.

  Definition share_state_pool := ZMap.t (option FFA_memory_share_state_struct).

  Record Hafnium_struct :=
    mkHafnium_struct {
        mem_properties : ZTree.t MemProperties; (* key is an address *) 
        hafnium_vm_regs : ArchRegs;
        (* mailbox will be currently ignored at this moment 
        hafnium_mailbox : mailbox_t; *)
        (* ffa_share_state is for ffa communications  *)
        ffa_share_state: share_state_pool;
        (* vm contexts saved in hafnium *)        
        vms_contexts :  ZTree.t VM_struct;
      }.


  (* The following abstract state provides the global state of Hafnium.
     It consists of two things 
     - Objects that do not belong to any VM 
       - Physical CPUs // ignored (since our main focus at this moment is not concurreny)
       - Memory pool // ignored (since we can focus on 
       - Hafnium's page table // address translation function
     - VMs and their objects 
       - VCPUs 
         - saved registers  // dramatically simplified in here
         - virtual interrupts  // ignored in here 
         - page table 
         - mailbox 
   *)

  (* This abstract state also contains abstract VM clients in it. *)
  
  Record AbstractState :=
    mkAbstractState{
        cur_entity_id: ffa_entity_id_t;
        (* hafnium global stage *)
        hafnium_context: Hafnium_struct;
        (* vm clinets *) 
        vms_clients : ZTree.t VM_CLIENT_struct; 
      }.

  Class AbstractStateContext `{hafnium_memory_management_context : HafniumMemoryManagementContext} :=
    {
    hafnium_id : ffa_entity_id_t;
    primary_vm_id: ffa_entity_id_t;
    secondary_vm_ids : list ffa_entity_id_t;
    vm_ids := primary_vm_id::secondary_vm_ids; 
    entity_list : list ffa_entity_id_t := hafnium_id::vm_ids;

    (* We may be able to use some feature of interaction tree for this scheduling? *)
    scheduler : AbstractState -> ffa_entity_id_t; 
    
    entity_list_prop := NoDup entity_list;

    cur_entity_id_prop (state : AbstractState) : In state.(cur_entity_id) entity_list;

    initial_state : AbstractState;

    (* TODO: add more invariants in here. *)
    well_formed (state: AbstractState) : Prop;
    initial_state_well_formed : well_formed initial_state;
    
    well_formed_guarantee_well_formed_scheduler_result :
      forall st next_id, well_formed st -> scheduler st = next_id -> In next_id vm_ids;
    
    mem_properties_prop_low_out_of_bound :
      forall addr st, (addr < address_low)%Z ->
                 ZTree.get addr (st.(hafnium_context)).(mem_properties) = None;
    mem_properties_prop_high_out_of_bound :
      forall addr st, (address_high < addr)%Z ->
                 ZTree.get addr (st.(hafnium_context)).(mem_properties) = None;
    mem_properties_prop_not_aligned :
      forall addr st, (Z.modulo addr alignment_value)%Z <> 0 ->
                 ZTree.get addr (st.(hafnium_context)).(mem_properties) = None;
    mem_properties_prop_well_formed :
      forall addr st,
        (address_low <= addr <= address_high)%Z ->
        (Z.modulo addr alignment_value)%Z = 0 ->
        exists properties, ZTree.get addr (st.(hafnium_context)).(mem_properties) = Some properties;    
    }.

  (* update hafnium context *)
  Definition update_mem_properties_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct b a.(hafnium_vm_regs) a.(ffa_share_state) a.(vms_contexts).

  Definition update_vm_regs_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct a.(mem_properties) b a.(ffa_share_state) a.(vms_contexts).
  
  Definition update_ffa_share_state_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct a.(mem_properties) a.(hafnium_vm_regs) b a.(vms_contexts).

  Definition update_vms_contexts_in_hafnium_context (a: Hafnium_struct) b :=
    mkHafnium_struct a.(mem_properties) a.(hafnium_vm_regs) a.(ffa_share_state) b.

  (* update *)
  Definition update_cur_entity_id (a : AbstractState) b :=
    mkAbstractState b a.(hafnium_context) a.(vms_clients).

  Definition update_hafnium_context (a : AbstractState) b :=
    mkAbstractState a.(cur_entity_id) b a.(vms_clients).

  Definition update_hafnium_mem_properties (a: AbstractState) b :=
    update_hafnium_context a (update_mem_properties_in_hafnium_context a.(hafnium_context) b).
      
  Definition update_hafnium_vm_regs (a: AbstractState) b :=
    update_hafnium_context a (update_vm_regs_in_hafnium_context a.(hafnium_context) b).

  Definition update_hafnium_ffa_share_state (a: AbstractState) b :=
    update_hafnium_context a (update_ffa_share_state_in_hafnium_context a.(hafnium_context) b).

  Definition update_hafnium_vms_contexts (a: AbstractState) b :=
    update_hafnium_context a (update_vms_contexts_in_hafnium_context a.(hafnium_context) b).
   
  Definition update_vms_clients (a : AbstractState) b :=
    mkAbstractState a.(cur_entity_id) a.(hafnium_context) b.
    
End AbstractState.

Notation "a '{' 'cur_entity_id' : b '}'" := (update_cur_entity_id a b) (at level 1).
Notation "a '{' 'hafnium_context' : b '}'" := (update_hafnium_context a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'mem_properties' : b '}'"
  := (update_hafnium_mem_properties a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'vm_regs' : b '}'"
  := (update_hafnium_vm_regs a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'ffa_share_state' : b '}'"
  := (update_hafnium_ffa_share_state a b) (at level 1).
Notation "a '{' 'hafnium_context' '/' 'vms_contexts' : b '}'"
  := (update_hafnium_vms_contexts a b) (at level 1).
Notation "a '{' 'vms_clients' : b '}'" := (update_vms_clients a b) (at level 1).

