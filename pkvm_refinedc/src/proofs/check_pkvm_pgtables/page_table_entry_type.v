From refinedc.lang Require Import base.
From refinedc.typing Require Import typing.
From refinedc.project.pkvm_refinedc.src.check_pkvm_pgtables
     Require Import Decision.

Set Default Proof Using "Type".


Notation BITS_PER_LONG := (64%Z) (only parsing).

Notation _GENMASK :=
  (fun (h l : Z) => 
  (Z.land ((Z_lunot 64 0) - ((Z.shiftl 1 l) + 1))
          (Z.shiftr (Z_lunot 64 0) (BITS_PER_LONG - 1 - h)))).

Notation GENMASK := (fun (h l : Z) => _GENMASK h l).


Notation GENMASK_0_1 :=
  (fun (pte: Z) =>
     (Z.land pte (GENMASK 0 1))).

Notation ENTRY_INVALID_0 := 0.
Notation ENTRY_INVALID_2 := 2.
Notation ENTRY_BLOCK := 1.
Notation ENTRY_RESERVED := 1.
Notation ENTRY_PAGE_DESCRIPTOR := 3.
Notation ENTRY_TABLE := 3.

  
Section PTE_TEYP_SECTION.
  Context `{!typeG Σ} `{!globalG Σ}.

  Definition ATTR_TYPE := Z.
  Definition ADDRESS_TYPE := Z.
  
  Inductive PTE_TYPES : Type :=
  | INVALID_PTE
  | BLOCK_PTE (attr: ATTR_TYPE) (address : ADDRESS_TYPE)
  | TABLE_PTE (attr : ATTR_TYPE) (addrress: ADDRESS_TYPE) 
  | PAGE_DESCRIPTOR_PTE  (attr: ATTR_TYPE) (address : ADDRESS_TYPE)
  | RESERVED_PTE.
  
  Inductive ENTRY_TYPE: Type :=
  | PTE_TYPE_INVALID
  | PTE_TYPE_BLOCK
  | PTE_TYPE_TABLE
  | PTE_TYPE_PAGE_DESCRIPTOR
  | PTE_TYPE_RESERVED.

  Definition GET_PTE_TYPES (pte: PTE_TYPES) :=
    match pte with
    | INVALID_PTE => PTE_TYPE_INVALID
    | BLOCK_PTE _ _ => PTE_TYPE_BLOCK
    | TABLE_PTE _ _ => PTE_TYPE_TABLE
    | PAGE_DESCRIPTOR_PTE _ _ => PTE_TYPE_PAGE_DESCRIPTOR
    | RESERVED_PTE =>  PTE_TYPE_RESERVED
    end.

  (* get address values in the entry *)
  (*
  Definition Z_to_PTE_ADDR (pte : Z) (level : Z) :=
    if decide (level = 0 \/ level = 1 \/ level = 2)
    then if decide (GENMASK_0_1 pte = ENTRY_INVALID_0 \/
                    GENMASK_0_1 pte = ENTRY_INVALID_2)
         then None
         else if decide (GENMASK_0_1 pte = ENTRY_BLOCK)
              then if decide (level = 1)
                   then Some (Z.land pte (GENMASK 47 30))
                   else if decide (level = 2)
                        then Some (Z.land pte (GENMASK 47 21))
                        else None 
              else None
    else if decide (level = 3)
         then if decide (GENMASK_0_1 pte = ENTRY_PAGE_DESCRIPTOR)
              then Some (Z.land pte (GENMASK 47 12))
              else None
         else None.
   *)

  (** Currently, it is a dummy function *)
  Definition Z_to_PTE_ATTR (pte : Z) (level : Z) :=
    Some 0.
  
  Definition Z_to_PTE_TYPES (pte : Z) (level : Z) : option PTE_TYPES :=
    if decide (level = 0 \/ level = 1 \/ level = 2)
    then if decide (GENMASK_0_1 pte = ENTRY_INVALID_0 \/
                    GENMASK_0_1 pte = ENTRY_INVALID_2)
         then Some INVALID_PTE
         else if decide (GENMASK_0_1 pte = ENTRY_BLOCK)
              then if decide (level = 1)
                   then
                     match Z_to_PTE_ATTR pte level with
                     | Some attr' =>
                       Some (BLOCK_PTE
                               attr' (Z.land pte (GENMASK 47 30)))
                     | None => None 
                     end
                   else if decide (level = 2)
                        then
                          match Z_to_PTE_ATTR pte level with
                          | Some attr' =>
                            Some (BLOCK_PTE
                                    attr' (Z.land pte (GENMASK 47 21)))
                          | None => None 
                          end                           
                        else None 
              else None
    else if decide (level = 3)
         then if decide (GENMASK_0_1 pte = ENTRY_PAGE_DESCRIPTOR)
              then
                match Z_to_PTE_ATTR pte level with
                | Some attr' =>
                  Some (PAGE_DESCRIPTOR_PTE
                          attr' (Z.land pte (GENMASK 47 12)))
                | None => None 
                end 
              else None
         else None.
  
  Definition PTE_TYPE_VALUE_EQUIV
             (entry_type : ENTRY_TYPE)
             (entry_type_value: Z) :=
    match entry_type with
    | PTE_TYPE_INVALID => entry_type_value = ENTRY_INVALID_0 \/
                         entry_type_value = ENTRY_INVALID_2
    | PTE_TYPE_BLOCK => entry_type_value = ENTRY_BLOCK
    | PTE_TYPE_TABLE => entry_type_value = ENTRY_RESERVED
    | PTE_TYPE_PAGE_DESCRIPTOR => entry_type_value = ENTRY_PAGE_DESCRIPTOR
    | PTE_TYPE_RESERVED => entry_type_value = ENTRY_TABLE
    end.

  Definition well_formed_page_table_entry
             (pte level : Z) :=
    match Z_to_PTE_TYPES pte level with
    | Some _ => True
    | _ => False
    end.

  Hint Unfold  well_formed_page_table_entry.
  
End PTE_TEYP_SECTION.


Section FAULT_TYPE_SECTION.

  Inductive FAULT_TYPE :=
  | FAULT_NONE
  | FAULT_ACCESS_FLAG
  | FAULT_ALIGNMENT
  | FAULT_DOMAIN
  | FAULT_PERMISSION
  | FAULT_TRANSLATION
  | FAULT_ADDRESSSIZE
  | FAULT_SYNCEXTERNAL
  | FAULT_SYNCEXTERNALONWALK
  | FAULT_SYNCPARITY
  | FAULT_SYNCPARITYONWALK
  | FAULT_ASYNCPARITY
  | FAULT_ASYNCEXTERNAL
  | FAULT_DEBUG
  | FAULT_TLBCONFLICT
  | FAULT_BRANCHTARGET
  | FAULT_HWUPDATEACCESSFLAG
  | FAULT_LOCKDOWN
  | FAULT_EXCLUSIVE
  | FAULT_ICACHEMAINT.

  Record FaultRecord :=
    mkFaultRecord {
        statuscode : FAULT_TYPE
      }.

  Record FullAddress :=
    mkFullAddress {
        address : Z;
        NS : bool
      }.

  Record AddressDescriptor :=
    mkAddressDescriptor {
        fault : FaultRecord;
        paddress : FullAddress;
        vaddress : Z
      }.

  Record TLBRecord :=
    mkTLBRecord {
        addrdesc : AddressDescriptor
      }.

  
        
End FAULT_TYPE_SECTION.


  



(**
Section ABSTSTATE.
  
  (* abstract type definitions *)
  Inductive BLOCK_SHAREABLE :=
  | NON_SHAREABLE (*0*) | OUTER_SHAREABLE (*2*) | INNER_SHAREABLE (*3*).

  Inductive STAGE1_BLOCK_PERM :=
  | STAGE1_READONLY (*2*) | STAGE1_READWRITE (*0*).

  Inductive STAGE1_BLOCK_TYPE :=
  | STAGE1_DEVICEINDX (*0*) | STAGE1_NORMALINDX (*1*).

  Record Stage1BlockAttributes :=
    mkStage1BlockAttributes {
        STAGE1_XN: bool;
        STAGE1_PXN: bool;
        STAGE1_CONTIGUOUS: bool;
        STAGE1_DBM: bool;
        STAGE1_NG: bool;
        STAGE1_AF: bool;
        STAGE1_SH: BLOCK_SHAREABLE;
        STAGE1_AP: STAGE1_BLOCK_PERM;
        STAGE1_NS: bool;
        STAGE1_ATTRINDX: STAGE1_BLOCK_TYPE
      }.

  Definition init_stage1_block_attributes :=
    mkStage1BlockAttributes false false false false false false NON_SHAREABLE STAGE1_READWRITE false STAGE1_DEVICEINDX.
  
  Record Stage1TableAttributes :=
    mkStage1TableAttributes {
        TABLE_NSTABLE: bool;
        TABLE_APTABLE1: bool;
        TABLE_APTABLE0: bool;
        TABLE_XNTABLE: bool;
        TABLE_PXNTABLE: bool
      }.

  Definition init_stage1_table_attributes := mkStage1TableAttributes false false false false false.

  Inductive STAGE2_BLOCK_EXECUTE_MODE :=
  | STAGE2_EXECUTE_ALL
  | STAGE2_EXECUTE_EL0
  | STAGE2_EXECUTE_NONE
  | STAGE2_EXECUTE_EL1.

  Inductive STAGE2_BLOCK_PERM :=
  | STAGE2_ACCESS_NOPERM | STAGE2_ACCESS_READ | STAGE2_ACCESS_WRITE | STAGE2_ACCESS_READWRITE.

  (* The following are stage-2 memory attributes for normal memory *)
  Inductive MMATTR_STAGE2_MEM_TYPE :=
  | STAGE2_DEVICE_MEMORY
  | STAGE2_NONCACHEABLE
  | STAGE2_WRITETHROUGH
  | STAGE2_WRITEBACK.

  (* The following are stage-2 memory attributes for device memory. *)
  Inductive MMATTR_STAGE2_DEVICE_MEMORY_TYPE :=
  | STAGE2_DEVICE_nGnRnE
  | STAGE2_DEVICE_nGnRE
  | STAGE2_DEVICE_nGRE
  | STAGE2_DEVICE_GRE.


  (* UNINITIALIZED: they are actually same with STAGE2_DEVICE_MEMORY and STAGE2_MEMATTR_DEVICE_nGnRnE, but  
                    I made them explicitly *) 
  Inductive MMATTR_STAGE2_OUTER_ATTR :=
  | MEMATTR_STAGE2_OUTER_ATTR_UNINITIALIZED
  | OUTER_MEM_TYPE_ATTR (mem_type: MMATTR_STAGE2_MEM_TYPE).
  
  Inductive MMATTR_STAGE2_INNER_ATTR :=
  | MMATTR_STAGE2_INNER_ATTR_UNINITIALIZED
  | INNER_MEM_TYPE_ATTR (mem_type : MMATTR_STAGE2_MEM_TYPE)
  | INNER_DEVICE_MEM_TYPE_ATTR (device_mem_type: MMATTR_STAGE2_DEVICE_MEMORY_TYPE).
  
  (* The following function defines only two things that are used in arch mm module now. It can be extended later. *)
  Inductive STAGE2_MEMATTR_VALUE :=
  | STAGE2_MEM_ATTR_GEN (outer_attr : MMATTR_STAGE2_OUTER_ATTR) (inner_attr :  MMATTR_STAGE2_INNER_ATTR).

  Record Stage2BlockAttributes :=
    mkStage2BlockAttributes {
        STAGE2_XN: STAGE2_BLOCK_EXECUTE_MODE;
        STAGE2_CONTIGUOUS: bool;
        STAGE2_DBM: bool;
        STAGE2_SW_OWNED: bool;
        STAGE2_SW_EXCLUSIVE: bool;            
        STAGE2_AF: bool;
        STAGE2_SH: BLOCK_SHAREABLE;
        STAGE2_S2AP: STAGE2_BLOCK_PERM;
        STAGE2_MEMATTR: STAGE2_MEMATTR_VALUE
      }.

  Definition init_stage2_block_attributes := mkStage2BlockAttributes
                                               STAGE2_EXECUTE_ALL false false false false false
                                               NON_SHAREABLE STAGE2_ACCESS_NOPERM
                                               (STAGE2_MEM_ATTR_GEN MEMATTR_STAGE2_OUTER_ATTR_UNINITIALIZED
                                                                    MMATTR_STAGE2_INNER_ATTR_UNINITIALIZED).

  (* One tip: 
     Since we have to convert Z values into this PTE_TYPES without any additional information, 
     we need to make them exclusive. I am currently assume that 
     block is only used at the last level (it is actually a page) of the address translation phase.
     When it is not true, we need to change them later *)
  Inductive PTE_TYPES :=
  | UNDEFINED
  | ABSENT
  (* XXX: invalid block for stage 1 and 2 . It seems it is used in some places, 
     so we have to keep track of the invalid block. Currently, I implement that 
     this invalid block is only in the bottom level of page tables, but it may need to be 
     in the intermediate level as well.  *)
  (* for level 0 - IS_TAbLE is on, IS_VALID is off *)      
  | STAGE1_INVALID_BLOCK_LEVEL0 (output_address : Z) (attributes: Stage1TableAttributes)
  (* for level 1, 2 - IS_TABLE is off, IS_VALID is off *)      
  | STAGE1_INVALID_BLOCK (output_address : Z) (attributes: Stage1BlockAttributes)
  (* for level 0, 1 - IS_TABLE is on and IS_VALID is on *)
  | STAGE1_TABLE (output_address : Z) (attributes: Stage1TableAttributes)
  (* for level 1 - IS_TABLE is off and IS_VALID is on *)
  | STAGE1_BLOCK (output_address : Z) (attributes: Stage1BlockAttributes)
  (* for level 2 - IS_TABLE is on and IS_VALID is on *)
  | STAGE1_PAGE (output_address : Z) (attributes: Stage1BlockAttributes)                 
  (* for level 0 - IS_TAbLE is on, IS_VALID is off *)      
  | STAGE2_INVALID_BLOCK_LEVEL0 (output_address : Z)
  (* for level 1, 2, 3 - IS_TABLE is off, IS_VALID is off *)
  | STAGE2_INVALID_BLOCK (output_address : Z) (attributes: Stage2BlockAttributes)
  (* for level 0, 1, 2 - IS_TABLE is on and IS_VALID is on *)
  | STAGE2_TABLE (output_address : Z)
  (* for level 1, 2 - IS_TABLE is off and IS_VALID is on *)                 
  | STAGE2_BLOCK (output_address : Z) (attribuctes: Stage2BlockAttributes)
  (* for level 3 - IS_TABLE is on and IS_VALID is on *)
  | STAGE2_PAGE (output_address : Z) (attribuctes: Stage2BlockAttributes).

  Inductive CURRENT_STAGE := STAGE1 | STAGE2.

  (* This module is an actually stateless module. We memorizes stage to distinguish whether the system
     is in stage 1 or 2. *)
  Record ArchMMAbstractState :=
    mkArchMMAbstractState {
        initialized: bool;
        stage: CURRENT_STAGE
      }.

  (* initialized is to distinguish UNDEFINED / ABSENT in PTE_TYPES and other UNINITIALIZED values 
     in other places. for the simplicity, we assume initialized is true in here. *)
  Definition initial_state : ArchMMAbstractState :=
    mkArchMMAbstractState true STAGE2.  

  Definition update_stage (a : ArchMMAbstractState) b :=
    mkArchMMAbstractState a.(initialized) b.
  
End ABSTSTATE.

Notation "a {stage : b }" := (update_stage a b) (at level 1).

(* TODO: we can combine the following values with the definitions in the Constant.v file. 
   1) define Z macro values in Constant.v 
   2) define int64 macro values in a different file (e.g., LowConstant.v) by using Constant.v *) 
Section FLAGVALUES.

  Definition Z_MM_S2_MAX_LEVEL := 3.
  Definition Z_MM_S2_ROOT_TABLE_COUNT := 1.

  Definition Z_NON_SHAREABLE := 0.
  Definition Z_OUTER_SHAREABLE := 2.
  Definition Z_INNER_SHAREABLE := 3.

  Definition Z_PTE_VALID := 0.
  Definition Z_PTE_LEVEL0_BLOCK := 1.
  Definition Z_PTE_TABLE := 1.

  Definition Z_STAGE1_XN := 54.
  Definition Z_STAGE1_PXN := 53.
  Definition Z_STAGE1_CONTIGUOUS := 52.
  Definition Z_STAGE1_DBM := 51.
  Definition Z_STAGE1_NG := 11.
  Definition Z_STAGE1_AF := 10.
  Definition Z_STAGE1_SH_GEN (x : Z) := Z.shiftl x 8.
  Definition Z_STAGE1_SH := 8.
  Definition Z_STAGE1_AP2 := 7.
  Definition Z_STAGE1_AP1 := 6.
  Definition Z_STAGE1_AP_GEN (x: Z) := Z.shiftl x 6.
  Definition Z_STAGE1_AP := 6.
  Definition Z_STAGE1_NS := 5.
  Definition Z_STAGE1_ATTRINDX_GEN (x: Z) := Z.shiftl x 2.
  Definition Z_STAGE1_ATTRINDX := 2.

  Definition Z_STAGE1_READONLY := 2.
  Definition Z_STAGE1_READWRITE := 0.

  Definition Z_STAGE1_DEVICEINDX := 0.
  Definition Z_STAGE1_NORMALINDX := 1.

  Definition Z_STAGE2_XN_GEN (x : Z) := Z.shiftl x 53.
  Definition Z_STAGE2_XN := 53.
  Definition Z_STAGE2_CONTIGUOUS := 52.
  Definition Z_STAGE2_DBM := 51.
  Definition Z_STAGE2_AF := 10.
  Definition Z_STAGE2_SH_GEN (x : Z) := Z.shiftl x 8.
  Definition Z_STAGE2_SH := 8.
  Definition Z_STAGE2_S2AP_GEN (x : Z) := Z.shiftl x 6.
  Definition Z_STAGE2_S2AP := 6.

  Definition Z_STAGE2_EXECUTE_ALL := 0.
  Definition Z_STAGE2_EXECUTE_EL0 := 1.
  Definition Z_STAGE2_EXECUTE_NONE := 2.
  Definition Z_STAGE2_EXECUTE_EL1 := 3.
  Definition Z_STAGE2_EXECUTE_MASK := 3.

  Definition Z_TABLE_NSTABLE := 63.
  Definition Z_TABLE_APTABLE1 := 62.
  Definition Z_TABLE_APTABLE0 := 61.
  Definition Z_TABLE_XNTABLE := 60.
  Definition Z_TABLE_PXNTABLE := 59.

  Definition Z_STAGE2_SW_OWNED := 55.
  Definition Z_STAGE2_SW_EXCLUSIVE := 56.

  Definition Z_STAGE2_DEVICE_MEMORY := 0.
  Definition Z_STAGE2_NONCACHEABLE := 1.
  Definition Z_STAGE2_WRITETHROUGH := 2.
  Definition Z_STAGE2_WRITEBACK := 3.

  Definition Z_STAGE2_DEVICE_nGnRnE := 0.
  Definition Z_STAGE2_DEVICE_nGnRE := 1.
  Definition Z_STAGE2_DEVICE_nGRE := 2.
  Definition Z_STAGE2_DEVICE_GRE := 3.

  Definition Z_STAGE2_MEMATTR_OUTER := 4.
  Definition Z_STAGE2_MEMATTR_INNER := 2.
  Definition Z_STAGE2_MEMATTR_GEN (outer inner : Z) := Z.lor (Z.shiftl outer Z_STAGE2_MEMATTR_OUTER)
                                                             (Z.shiftl inner Z_STAGE2_MEMATTR_INNER).

  Definition Z_STAGE2_MEMATTR_MASK := (Z.shiftl 3 Z_STAGE2_MEMATTR_OUTER).
  
  Definition Z_STAGE2_ACCESS_READ := 1.
  Definition Z_STAGE2_ACCESS_WRITE := 2.
  Definition Z_PAGE_BITS := 12.
  Definition Z_64MAX := ((Z.pow 2 64) - 1)%Z.
  Definition Z_not := fun val => (Z.lxor Z_64MAX val).
  (* Test code to check Z operations. 
     Z_shiftl is not necessary if we use Z.shiftl with well defined values. 
  Definition Z_shiftl (val shift : Z) := Z.modulo (Z.shiftl val shift) (Z.pow 2 64).
  Eval compute in (((Z.pow 2 64) - 1)%Z).
  Eval compute in (Z_not Z_64MAX).
  Eval compute in (Z.land Z_64MAX 1).
  Eval compute in (Z.land Z_64MAX 8).
  Eval compute in (Z.land Z_64MAX 16).
  Eval compute in (Z.lor 8 16).
  Eval compute in (Z.lor 24 16).
  Eval compute in (Z.modulo 1 3).
  Eval compute in (Z.shiftl 111 63).
  Eval compute in (Z_shiftl 111 63).
  *) 
  Definition Z_PTE_ADDR_MASK := (Z.land ((Z.shiftl 1 48) - 1) (Z_not ((Z.shiftl 1 Z_PAGE_BITS) - 1))).
  Definition Z_PTE_ATTR_MASK := (Z_not (Z.lor Z_PTE_ADDR_MASK (Z.shiftl 1 1))).

End FLAGVALUES.

Section FLAG_TO_VALUE_and_VALUE_TO_FLAG.

  Definition x_zshift_or_0 := fun (cond: bool) (x: Z) (shift : Z) => if cond then Z.shiftl x shift else 0.
  Definition zshift_or_0 := fun (cond: bool) (shift : Z) => x_zshift_or_0 cond 1 shift.

  Definition x_bit_no_exist :=
    fun (x shift attribute_values: Z) => (zeq 0 (Z.land (Z.shiftl x shift) attribute_values)).
  Definition x_gen_true_false := 
    fun (x shift attribute_values: Z) => if x_bit_no_exist x shift attribute_values then false else true.
  Definition bit_no_exist :=    
    fun (shift : Z) (attribute_values: Z) => x_bit_no_exist 1 shift attribute_values.
  Definition gen_true_false := 
    fun (shift : Z) (attribute_values: Z) => if bit_no_exist shift attribute_values then false else true.
  
  Definition Stage1TableAttributes_to_ATTR_VALUES (stage1_table_attributes : Stage1TableAttributes) : Z :=
    match stage1_table_attributes with
    |  mkStage1TableAttributes nstable aptable1 aptable2 xntable pxntable
       => let nstable_to_z := zshift_or_0 nstable Z_TABLE_NSTABLE in 
         let aptable1_to_z := zshift_or_0 aptable1 Z_TABLE_APTABLE1 in
         let aptable0_to_z := zshift_or_0 aptable2 Z_TABLE_APTABLE0 in
         let xntable_to_z := zshift_or_0 xntable Z_TABLE_XNTABLE in
         let pxntable_to_z :=  zshift_or_0 pxntable Z_TABLE_PXNTABLE in 
         nstable_to_z + aptable1_to_z + aptable0_to_z + xntable_to_z + pxntable_to_z
    end.
  
  Definition ATTR_VALUES_to_Stage1TableAttributes (stage1_table_attributes_value : Z)
    : Stage1TableAttributes :=
    let nstable_of_z := gen_true_false Z_TABLE_NSTABLE stage1_table_attributes_value in
    let aptable1_of_z := gen_true_false Z_TABLE_APTABLE1 stage1_table_attributes_value in
    let aptable0_of_z := gen_true_false Z_TABLE_APTABLE0 stage1_table_attributes_value in
    let xntable_of_z := gen_true_false Z_TABLE_XNTABLE stage1_table_attributes_value in
    let pxntable_of_z := gen_true_false Z_TABLE_PXNTABLE stage1_table_attributes_value in
    mkStage1TableAttributes nstable_of_z aptable1_of_z aptable0_of_z xntable_of_z pxntable_of_z.

  Definition Stage1BlockAttributes_to_ATTR_VALUES (stage1_block_attributes : Stage1BlockAttributes) : Z :=
    match stage1_block_attributes with
    | mkStage1BlockAttributes xn pxn contiguous dbm ng af sh ap ns attrindx
      => let xn_to_n := zshift_or_0 xn Z_STAGE1_XN in
        let pxn_to_n := zshift_or_0 pxn Z_STAGE1_PXN in
        let contiguous_to_n := zshift_or_0 contiguous Z_STAGE1_CONTIGUOUS in
        let dbm_to_n := zshift_or_0 dbm Z_STAGE1_DBM in
        let ng_to_n := zshift_or_0 ng Z_STAGE1_NG in
        let af_to_n := zshift_or_0 af Z_STAGE1_AF in
        let sh_to_n := Z_STAGE1_SH_GEN (match sh with
                                        | NON_SHAREABLE =>  Z_NON_SHAREABLE
                                        | OUTER_SHAREABLE => Z_OUTER_SHAREABLE 
                                        | INNER_SHAREABLE => Z_INNER_SHAREABLE 
                                        end) in
        let ap_to_n := Z_STAGE1_AP_GEN (match ap with
                                        | STAGE1_READONLY => Z_STAGE1_READONLY
                                        | STAGE1_READWRITE => Z_STAGE1_READWRITE
                                        end) in
        let ns_to_n := zshift_or_0 ns Z_STAGE1_NS in
        let attrindx_to_n := Z_STAGE1_ATTRINDX_GEN (match attrindx with
                                                    | STAGE1_DEVICEINDX => Z_STAGE1_DEVICEINDX
                                                    | STAGE1_NORMALINDX => Z_STAGE1_NORMALINDX
                                                    end) in
        xn_to_n + pxn_to_n + contiguous_to_n + dbm_to_n + ng_to_n + af_to_n + sh_to_n + ap_to_n + ns_to_n + attrindx_to_n
    end.

  Definition ATTR_VALUES_to_Stage1BlockAttributes (stage1_block_attributes_value : Z) : option Stage1BlockAttributes :=
    let xn_of_z := gen_true_false Z_STAGE1_XN stage1_block_attributes_value in
    let pxn_of_z := gen_true_false Z_STAGE1_PXN stage1_block_attributes_value in
    let contiguous_of_z := gen_true_false Z_STAGE1_CONTIGUOUS stage1_block_attributes_value in
    let dbm_of_z := gen_true_false Z_STAGE1_DBM stage1_block_attributes_value in
    let ng_of_z := gen_true_false Z_STAGE1_NG stage1_block_attributes_value in
    let af_of_z := gen_true_false Z_STAGE1_AF stage1_block_attributes_value in
    let sh_of_z := if x_bit_no_exist 1 Z_STAGE1_SH stage1_block_attributes_value
                   then if x_bit_no_exist 2 Z_STAGE1_SH stage1_block_attributes_value
                        then (* 0 << 8 *) Some NON_SHAREABLE
                        else (* 2 << 8 *) Some OUTER_SHAREABLE
                   else if x_bit_no_exist 2 Z_STAGE1_SH stage1_block_attributes_value
                        then (* 1 << 8 *) None
                        else (* 3 << 8 *) Some INNER_SHAREABLE in
    let ap_of_z := if x_bit_no_exist 1 Z_STAGE1_AP stage1_block_attributes_value
                   then if x_bit_no_exist 2 Z_STAGE1_AP stage1_block_attributes_value
                        then (* 0 << 6 *) Some STAGE1_READWRITE
                        else (* 2 << 6 *) Some STAGE1_READONLY
                   else (* 1 << 6 or 3 << 6 *) None in
    let ns_of_z := gen_true_false Z_STAGE1_NS stage1_block_attributes_value in
    let attrindx_of_n := if x_bit_no_exist 1 Z_STAGE1_ATTRINDX stage1_block_attributes_value
                         then if x_bit_no_exist 2 Z_STAGE1_ATTRINDX stage1_block_attributes_value
                              then (* 0 << 2 *) Some STAGE1_DEVICEINDX
                              else (* 2 << 2 *) None
                         else if x_bit_no_exist 2 Z_STAGE1_ATTRINDX stage1_block_attributes_value
                              then (* 1 << 2 *) Some STAGE1_NORMALINDX
                              else (* 3 << 2 *) None in
    match (sh_of_z, ap_of_z, attrindx_of_n) with
    | (Some sh_of_z', Some ap_of_z', Some attrindx_of_z') =>
      Some (mkStage1BlockAttributes xn_of_z pxn_of_z contiguous_of_z dbm_of_z
                                    ng_of_z af_of_z sh_of_z' ap_of_z' ns_of_z attrindx_of_z')
    | (_, _, _) => None
    end.

  Definition STAGE2_MEMATTR_VALUE_to_ATTR_VALUES (stage2_memattr_value: STAGE2_MEMATTR_VALUE) : Z :=
    match stage2_memattr_value with
    | STAGE2_MEM_ATTR_GEN outer_attr inner_attr =>
      let outer_val :=
          match outer_attr with
          | MEMATTR_STAGE2_OUTER_ATTR_UNINITIALIZED => 0
          | OUTER_MEM_TYPE_ATTR mem_type =>
            match mem_type with 
            | STAGE2_DEVICE_MEMORY => Z_STAGE2_DEVICE_MEMORY
            | STAGE2_NONCACHEABLE => Z_STAGE2_NONCACHEABLE
            | STAGE2_WRITETHROUGH => Z_STAGE2_WRITETHROUGH
            | STAGE2_WRITEBACK => Z_STAGE2_WRITEBACK
            end
          end in
      let inner_val :=
          match inner_attr with
          | MMATTR_STAGE2_INNER_ATTR_UNINITIALIZED => 0
          | INNER_MEM_TYPE_ATTR mem_type =>
            match mem_type with 
            | STAGE2_DEVICE_MEMORY => Z_STAGE2_DEVICE_MEMORY
            | STAGE2_NONCACHEABLE => Z_STAGE2_NONCACHEABLE
            | STAGE2_WRITETHROUGH => Z_STAGE2_WRITETHROUGH
            | STAGE2_WRITEBACK => Z_STAGE2_WRITEBACK
            end
          | INNER_DEVICE_MEM_TYPE_ATTR device_mem_type =>
            match device_mem_type with
            | STAGE2_DEVICE_nGnRnE => Z_STAGE2_DEVICE_nGnRnE
            | STAGE2_DEVICE_nGnRE => Z_STAGE2_DEVICE_nGnRE
            | STAGE2_DEVICE_nGRE =>  Z_STAGE2_DEVICE_nGRE
            | STAGE2_DEVICE_GRE =>  Z_STAGE2_DEVICE_GRE
            end
          end in
      Z_STAGE2_MEMATTR_GEN outer_val inner_val
    end.

  Definition Stage2BlockAttributes_to_ATTR_VALUES (stage2_block_attributes : Stage2BlockAttributes) : Z :=
    match stage2_block_attributes with
    | mkStage2BlockAttributes xn contiguous dbm sw_owned sw_exclusive af sh s2ap memattr
      => let xn_to_n := Z_STAGE2_XN_GEN (match xn with
                                        | STAGE2_EXECUTE_ALL => Z_STAGE2_EXECUTE_ALL
                                        | STAGE2_EXECUTE_EL0 => Z_STAGE2_EXECUTE_EL0
                                        | STAGE2_EXECUTE_NONE => Z_STAGE2_EXECUTE_NONE
                                        | STAGE2_EXECUTE_EL1 => Z_STAGE2_EXECUTE_EL1
                                        end) in
        let contiguous_to_n := zshift_or_0 contiguous Z_STAGE2_CONTIGUOUS  in
        let dbm_to_n := zshift_or_0 dbm Z_STAGE2_DBM in
        let sw_owned_n := zshift_or_0 sw_owned Z_STAGE2_SW_OWNED in
        let sw_exclusive_n := zshift_or_0 sw_exclusive Z_STAGE2_SW_EXCLUSIVE in
        let af_to_n := zshift_or_0 af Z_STAGE2_AF in
        let sh_to_n := Z_STAGE2_SH_GEN (match sh with
                                        | NON_SHAREABLE => Z_NON_SHAREABLE
                                        | OUTER_SHAREABLE => Z_OUTER_SHAREABLE
                                        | INNER_SHAREABLE => Z_INNER_SHAREABLE
                                        end) in
        let s2ap_to_n := Z_STAGE2_S2AP_GEN (match s2ap with
                                            | STAGE2_ACCESS_NOPERM => 0
                                            | STAGE2_ACCESS_READ => Z_STAGE2_ACCESS_READ
                                            | STAGE2_ACCESS_WRITE => Z_STAGE2_ACCESS_WRITE
                                            | STAGE2_ACCESS_READWRITE => Z_STAGE2_ACCESS_READ + Z_STAGE2_ACCESS_WRITE
                                            end) in 
        let memattr_to_n := STAGE2_MEMATTR_VALUE_to_ATTR_VALUES memattr in
        xn_to_n + contiguous_to_n + dbm_to_n + sw_owned_n + sw_exclusive_n + af_to_n + sh_to_n + s2ap_to_n + memattr_to_n
    end.
  
  (* The following function defines only two things that are used in arch mm module now. It can be extended later. *)  
  Definition ATTR_VALUES_to_Stage2BlockAttributes (stage2_block_attributes_value : Z) : option Stage2BlockAttributes :=
    let xn_of_z := if x_bit_no_exist 1 Z_STAGE2_XN stage2_block_attributes_value
                   then if  x_bit_no_exist 2 Z_STAGE2_XN stage2_block_attributes_value
                        then (* 0 << 53 *) STAGE2_EXECUTE_ALL
                        else (* 2 << 53 *) STAGE2_EXECUTE_NONE
                   else if  x_bit_no_exist 2 Z_STAGE2_XN stage2_block_attributes_value
                        then (* 1 << 53 *) STAGE2_EXECUTE_EL0
                        else (* 3 << 53 *) STAGE2_EXECUTE_EL1 in
    let contiguous_of_z := gen_true_false Z_STAGE2_CONTIGUOUS stage2_block_attributes_value in
    let dbm_of_z := gen_true_false Z_STAGE2_DBM stage2_block_attributes_value in
    let sw_owned_of_z := gen_true_false Z_STAGE2_SW_OWNED stage2_block_attributes_value in
    let sw_exclusive_of_z := gen_true_false Z_STAGE2_SW_EXCLUSIVE stage2_block_attributes_value in
    let af_of_z := gen_true_false Z_STAGE2_AF stage2_block_attributes_value in
    let sh_of_z := if  x_bit_no_exist 1 Z_STAGE2_SH stage2_block_attributes_value
                   then if  x_bit_no_exist 2 Z_STAGE2_SH stage2_block_attributes_value
                        then (* 0 << 8 *) Some NON_SHAREABLE
                        else (* 2 << 8 *) Some OUTER_SHAREABLE
                   else if x_bit_no_exist 2 Z_STAGE2_SH stage2_block_attributes_value
                        then (* 1 << 8 *) None
                        else (* 3 << 8 *) Some INNER_SHAREABLE in
    let s2ap_of_z := if x_bit_no_exist 1 Z_STAGE2_S2AP stage2_block_attributes_value
                     then if x_bit_no_exist 2 Z_STAGE2_S2AP stage2_block_attributes_value
                          then (* 0 << 6 *) STAGE2_ACCESS_NOPERM
                          else (* 2 << 6 *) STAGE2_ACCESS_WRITE
                     else if x_bit_no_exist 2 Z_STAGE2_S2AP stage2_block_attributes_value
                          then (* 1 << 6 *) STAGE2_ACCESS_READ
                          else (* 3 << 6 *) STAGE2_ACCESS_READWRITE in
    let memattr_outer_of_z := if x_bit_no_exist 1 Z_STAGE2_MEMATTR_OUTER stage2_block_attributes_value
                              then if x_bit_no_exist 2 Z_STAGE2_MEMATTR_OUTER stage2_block_attributes_value
                                   then (* 0 << 4 *) STAGE2_DEVICE_MEMORY
                                   else (* 2 << 4 *) STAGE2_WRITETHROUGH
                              else if x_bit_no_exist 2 Z_STAGE2_MEMATTR_OUTER stage2_block_attributes_value
                                   then (* 1 << 4 *) STAGE2_NONCACHEABLE
                                   else (* 3 << 4 *) STAGE2_WRITEBACK in
    let memattr_inner_of_z :=
        match memattr_outer_of_z with
        | STAGE2_DEVICE_MEMORY =>
          let inner_device_mem_type := 
              if x_bit_no_exist 1 Z_STAGE2_MEMATTR_OUTER stage2_block_attributes_value
              then if x_bit_no_exist 2 Z_STAGE2_MEMATTR_INNER stage2_block_attributes_value
                   then (* 0 << 4 *) STAGE2_DEVICE_nGnRnE
                   else (* 2 << 4 *) STAGE2_DEVICE_nGnRE
              else if x_bit_no_exist 2 Z_STAGE2_MEMATTR_INNER stage2_block_attributes_value
                   then (* 1 << 4 *) STAGE2_DEVICE_nGnRE
                   else (* 3 << 4 *) STAGE2_DEVICE_GRE in
          INNER_DEVICE_MEM_TYPE_ATTR inner_device_mem_type
        | _ =>
          let inner_mem_type := 
              if x_bit_no_exist 1 Z_STAGE2_MEMATTR_INNER stage2_block_attributes_value
              then if x_bit_no_exist 2 Z_STAGE2_MEMATTR_INNER stage2_block_attributes_value
                   then (* 0 << 4 *) STAGE2_DEVICE_MEMORY
                   else (* 2 << 4 *) STAGE2_WRITETHROUGH
              else if x_bit_no_exist 2 Z_STAGE2_MEMATTR_INNER stage2_block_attributes_value
                   then (* 1 << 4 *) STAGE2_NONCACHEABLE
                   else (* 3 << 4 *) STAGE2_WRITEBACK in
          INNER_MEM_TYPE_ATTR inner_mem_type
        end in
    let memattr_of_z := STAGE2_MEM_ATTR_GEN (OUTER_MEM_TYPE_ATTR memattr_outer_of_z) memattr_inner_of_z in
    match sh_of_z with
    | Some sh_of_z' =>
      Some (mkStage2BlockAttributes xn_of_z contiguous_of_z dbm_of_z sw_owned_of_z sw_exclusive_of_z
                                    af_of_z sh_of_z' s2ap_of_z memattr_of_z)
    | None => None
    end.                                            

  Definition HAS_PTE_TABLE (value : Z) :=
    if (bit_no_exist Z_PTE_TABLE value) then false else true.
    
  Definition HAS_PTE_VALID (value : Z) := 
    if (bit_no_exist Z_PTE_VALID value) then false else true.

  Definition GET_ADDRESS (value : Z) :=
    let address_with_shift := Z.land value Z_PTE_ADDR_MASK in
    Z.shiftr address_with_shift Z_PAGE_BITS.
  
  Definition PTE_TYPES_to_IS_VALID_VALUE (pte_value : PTE_TYPES) : Z :=
    match pte_value with
    | UNDEFINED => 0
    | ABSENT => 0
    (* for level 0 - IS_TABLE is on, IS_VALID is off *)      
    | STAGE1_INVALID_BLOCK_LEVEL0 _ _  => 0
    (* for level 1, 2 - IS_TABLE is off, IS_VALID is off *)      
    | STAGE1_INVALID_BLOCK _ _  =>  0
    (* for level 0, 1 - IS_TABLE is on and IS_VALID is on *)                                     
    | STAGE1_TABLE _ _ => Z.shiftl 1 Z_PTE_VALID
    (* for level 1 - IS_TABLE is off and IS_VALID is on *)
    | STAGE1_BLOCK _ _ => Z.shiftl 1 Z_PTE_VALID
    (* for level 2 - IS_TABLE is on and IS_VALID is on *)
    | STAGE1_PAGE _ _ => Z.shiftl 1 Z_PTE_VALID
    (* for level 0 - IS_TABLE is on, IS_VALID is off *)
    | STAGE2_INVALID_BLOCK_LEVEL0 _  => 0
    (* for level 1, 2, 3 - IS_TABLE is off, IS_VALID is off *)
    | STAGE2_INVALID_BLOCK _ _ => 0
    (* for level 0, 1, 2 - IS_TABLE is on and IS_VALID is on *)
    | STAGE2_TABLE _ => Z.shiftl 1 Z_PTE_VALID
    (* for level 1, 2 - IS_TABLE is off and IS_VALID is on *)
    | STAGE2_BLOCK _ _ => Z.shiftl 1 Z_PTE_VALID
    (* for level 3 - IS_TABLE is on and IS_VALID is on *)
    | STAGE2_PAGE _ _ => Z.shiftl 1 Z_PTE_VALID
    end.

  Definition PTE_TYPES_to_IS_TABLE_VALUE (pte_value : PTE_TYPES) : Z :=
    match pte_value with
    | UNDEFINED => 0
    | ABSENT => 0
    (* for level 0 - IS_TABLE is on, IS_VALID is off *)      
    | STAGE1_INVALID_BLOCK_LEVEL0 _ _  => Z.shiftl 1 Z_PTE_TABLE
    (* for level 1, 2 - IS_TABLE is off, IS_VALID is off *)
    | STAGE1_INVALID_BLOCK _ _ => 0
    (* for level 0, 1 - IS_TABLE is on and IS_VALID is on *)                                   
    | STAGE1_TABLE _ _ => Z.shiftl 1 Z_PTE_TABLE
    (* for level 1 - IS_TABLE is off and IS_VALID is on *)                                  
    | STAGE1_BLOCK _ _  =>  0
    (* for level 2 - IS_TABLE is on and IS_VALID is on *)
    | STAGE1_PAGE _ _ => Z.shiftl 1 Z_PTE_TABLE
    (* for level 0 - IS_TABLE is on, IS_VALID is off *)                                 
    | STAGE2_INVALID_BLOCK_LEVEL0 _  => Z.shiftl 1 Z_PTE_TABLE
    (* for level 1, 2, 3 - IS_TABLE is off, IS_VALID is off *)                                 
    | STAGE2_INVALID_BLOCK _ _ => 0
    (* for level 0, 1, 2 - IS_TABLE is on and IS_VALID is on *)                                   
    | STAGE2_TABLE _  => Z.shiftl 1 Z_PTE_TABLE
    (* for level 1, 2 - IS_TABLE is off and IS_VALID is on *)                                 
    | STAGE2_BLOCK _ _  =>  0
    (* for level 3 - IS_TABLE is on and IS_VALID is on *)                             
    | STAGE2_PAGE _ _ => Z.shiftl 1 Z_PTE_TABLE
    end.
  
  Definition PTE_TYPES_to_ATTR_VALUES (pte_value : PTE_TYPES) : Z :=
    match pte_value with
    | UNDEFINED => 0
    | ABSENT => 0
    (* for level 0 - IS_TABLE is on, IS_VALID is off *)      
    | STAGE1_INVALID_BLOCK_LEVEL0 _ attributes  => Stage1TableAttributes_to_ATTR_VALUES attributes
    (* for level 1, 2 - IS_TABLE is off, IS_VALID is off *)
    | STAGE1_INVALID_BLOCK _ attributes =>  Stage1BlockAttributes_to_ATTR_VALUES attributes 
    (* for level 0, 1 - IS_TABLE is on and IS_VALID is on *)                                   
    | STAGE1_TABLE _ attributes => Stage1TableAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 Z_PTE_VALID
    (* for level 1 - IS_TABLE is off and IS_VALID is on *)                                  
    | STAGE1_BLOCK _ attributes => Stage1BlockAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 Z_PTE_VALID
    (* for level 2 - IS_TABLE is on and IS_VALID is on *)
    | STAGE1_PAGE _ attributes => Stage1BlockAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 Z_PTE_VALID
    (* for level 0 - IS_TABLE is on, IS_VALID is off *)                                 
    | STAGE2_INVALID_BLOCK_LEVEL0 _ => 0
    (* for level 1, 2, 3 - IS_TABLE is off, IS_VALID is off *)       
    | STAGE2_INVALID_BLOCK _ attributes => Stage2BlockAttributes_to_ATTR_VALUES attributes
    (* for level 0, 1, 2 - IS_TABLE is on and IS_VALID is on *)                                   
    | STAGE2_TABLE _  => Z.shiftl 1 Z_PTE_VALID
    (* for level 1, 2 - IS_TABLE is off and IS_VALID is on *)                                 
    | STAGE2_BLOCK _ attributes => Stage2BlockAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 Z_PTE_VALID
    (* for level 3 - IS_TABLE is on and IS_VALID is on *)                             
    | STAGE2_PAGE _ attributes => Stage2BlockAttributes_to_ATTR_VALUES attributes + Z.shiftl 1 Z_PTE_VALID
    end.

  Definition PTE_TYPES_to_OUTPUT_ADDRESS (pte : PTE_TYPES) : Z :=
    match pte with
    | UNDEFINED => 0
    | ABSENT => 0
    | STAGE1_INVALID_BLOCK_LEVEL0 oa _
    | STAGE1_INVALID_BLOCK oa _
    | STAGE1_TABLE oa _
    | STAGE1_BLOCK oa _
    | STAGE1_PAGE oa _
    | STAGE2_INVALID_BLOCK_LEVEL0 oa
    | STAGE2_INVALID_BLOCK oa _
    | STAGE2_TABLE oa
    | STAGE2_BLOCK oa _ 
    | STAGE2_PAGE oa _ => oa
    end.
  
  Definition PTE_TYPES_to_OUTPUT_ADDRESS_WITH_SHIFT (pte : PTE_TYPES) : Z :=
    Z.shiftl (PTE_TYPES_to_OUTPUT_ADDRESS pte) Z_PAGE_BITS.

  Definition PTE_TYPES_to_VALUES (pte : PTE_TYPES) : Z :=
    PTE_TYPES_to_OUTPUT_ADDRESS_WITH_SHIFT pte +
    PTE_TYPES_to_ATTR_VALUES pte +
    PTE_TYPES_to_IS_TABLE_VALUE pte.  


  Definition VALUES_to_PTE_TYPES_STAGE1 (level : Z) (value: Z) : option PTE_TYPES  :=
    if zeq level 0 then
      match HAS_PTE_TABLE value with
      | true => 
        match HAS_PTE_VALID value with
        | true => match ATTR_VALUES_to_Stage1TableAttributes value with
                 | attrs =>  Some (STAGE1_TABLE  (GET_ADDRESS value) attrs)
                 end
        | false => match ATTR_VALUES_to_Stage1TableAttributes value with
                  | attrs =>  Some (STAGE1_INVALID_BLOCK_LEVEL0  (GET_ADDRESS value) attrs)
                  end
        end
      | false => None
      end
    else 
      match HAS_PTE_VALID value with
      | true =>
        match HAS_PTE_TABLE value with
        | true => if zeq level 1 then
                   match ATTR_VALUES_to_Stage1TableAttributes value with
                   | attrs =>  Some (STAGE1_TABLE  (GET_ADDRESS value) attrs)
                   end
                 else if zeq level 2 then
                        match ATTR_VALUES_to_Stage1BlockAttributes value with
                        | Some attrs =>  Some (STAGE1_PAGE  (GET_ADDRESS value) attrs)
                        | None => None
                        end
                      else None
        | false =>  if zeq level 1 then
                     match ATTR_VALUES_to_Stage1BlockAttributes value with
                     | Some attrs =>  Some (STAGE1_BLOCK (GET_ADDRESS value) attrs)
                     | None => None
                     end
                   else None
        end
      | false =>
        match HAS_PTE_TABLE value with
        | true => None
        | false =>
          if zeq level 1 || zeq level 2
          then
            match ATTR_VALUES_to_Stage1BlockAttributes value with
            | Some attrs =>  Some (STAGE1_INVALID_BLOCK (GET_ADDRESS value) attrs)
            | None => None
            end
          else None
        end
      end.

  Definition VALUES_to_PTE_TYPES_STAGE2 (level : Z) (value: Z) : option PTE_TYPES  :=
    if zeq level 0 then
      match HAS_PTE_TABLE value with
      | true => 
        match HAS_PTE_VALID value with
        | true => Some (STAGE2_TABLE  (GET_ADDRESS value))
        | false => Some (STAGE2_INVALID_BLOCK_LEVEL0  (GET_ADDRESS value))
        end
      | false => None
      end
    else 
      match HAS_PTE_VALID value with
      | true =>
        match HAS_PTE_TABLE value with
        | true => if zeq level 1 || zeq level 2 then
                   Some (STAGE2_TABLE (GET_ADDRESS value))
                 else if zeq level 3 then
                        match ATTR_VALUES_to_Stage2BlockAttributes value with
                        | Some attrs =>  Some (STAGE2_PAGE  (GET_ADDRESS value) attrs)
                        | None => None
                        end
                      else None
        | false =>  if zeq level 1 || zeq level 2 then
                     match ATTR_VALUES_to_Stage2BlockAttributes value with
                     | Some attrs =>  Some (STAGE2_BLOCK (GET_ADDRESS value) attrs)
                     | None => None
                     end
                   else None
        end
      | false =>
        match HAS_PTE_TABLE value with
        | true => None
        | false =>
          if zeq level 1 || zeq level 2 || zeq level 3
          then
            match ATTR_VALUES_to_Stage2BlockAttributes value with
            | Some attrs =>  Some (STAGE2_INVALID_BLOCK (GET_ADDRESS value) attrs)
            | None => None
            end
          else None
        end
      end.

  
  Definition VALUES_to_PTE_TYPES (level : Z) (stage : CURRENT_STAGE) (value: Z) : option PTE_TYPES :=
    match stage with
    | STAGE1 => VALUES_to_PTE_TYPES_STAGE1 level value
    | STAGE2 => VALUES_to_PTE_TYPES_STAGE2 level value
    end.

End FLAG_TO_VALUE_and_VALUE_TO_FLAG.
 **)
