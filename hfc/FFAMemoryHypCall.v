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


Inductive terminate {E} {R} (it:itree E R) : Prop :=
| TermRet
    v
    (RET: observe it = RetF v)
| TermTau
    (TAU: observe it = TauF it).

(* From HafniumCore *)
Require Import Lang.
Require Import Values.
Require Import Integers.
Require Import Constant.
Require Import Decision.

Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Require Import Maps.
Set Implicit Arguments.

(* FFA Memory management related parts *)
Require Import FFAMemoryHypCallIntro.
Require Export FFAMemoryHypCallDescriptorState.
Require Export FFAMemoryHypCallState.
Require Export FFAMemoryHypCallAuxFunctions.

(*************************************************************)
(** *             Hafnium State                              *)
(*************************************************************)
Section HAFNIUM_EE.

  Context `{ffa_types_and_constants : FFA_TYPES_AND_CONSTANTS}.

  Inductive updateStateE: Type -> Type :=
  | GetState : updateStateE AbstractState
  | SetState (st: AbstractState): updateStateE unit.
 
  Definition updateState_handler {E: Type -> Type}
    : updateStateE ~> stateT AbstractState (itree E) :=
    fun _ e st =>
      match e with
      | GetState => Ret (st, st)
      | SetState st' => Ret (st', tt)
      end.

End HAFNIUM_EE.
  
 
Notation "'do' X <- A ;;; B" := (match A with Some X => B | None => triggerUB "None" end)
  (at level 200, X ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation "'do' X , Y <- A ;;; B" := (match A with Some (X, Y) => B | None => triggerUB "None" end)
  (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation "'do' X , Y , Z <- A ;;; B" := (match A with Some (X, Y, Z) => B | None => triggerUB "None" end)
  (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation " 'check' A ;;; B" := (if A then B else Ret None)
  (at level 200, A at level 100, B at level 200)
  : itree_monad_scope.
 
Local Open Scope itree_monad_scope.

(** Three roles in the FFA_XXX communications, and endpoints in the communications *)
(**
   In all transactions, an endpoint must be a Sender or Receiver. 
   This depends on the type of transaction as follows.

   - In a transaction to donate ownership of a memory region, 
     the Sender is the current Owner and the Receiver is the new Owner.
   - In a transaction to lend or share access to a memory region, 
     the Sender is the Lender and the Receiver is the Borrower.
   - In a transaction to relinquish access to a memory region, 
     the Sender is the Borrower and the Receiver is the Lender.
*)

(** 5.4.1 Ownership and access rules
   - There are invariants that we have to enforce 
   *)

(*************************************************************)
(** *             Valid Combinations                         *)
(*************************************************************)
Section VALID_COMBINATIONS.

  Context `{ffa_types_and_constants : FFA_TYPES_AND_CONSTANTS}.
  
  (** This part is one of the most important parts that describe ownership and accessibility options. 
       It is similar to "valid" check in the abstract model by Jade *)
  
  (** Related parts: 
       Table 5.3: Valid combinations of ownership and access states     
       Table 5.4: Valid combinations of ownership and access states between two components

     No.     Component  Component       Descriptions
             A state    B state
     1       Owner-EA   !Owner-NA       Component A has exclusive access and ownership of 
                                        a memory region that is inaccessible from component B.
     2       Owner-NA   !Owner-NA       Component A has granted exclusive access to 
                                        a memory region it owns to another component. 
                                        It is inaccessible from component B.
     3       Owner-NA   !Owner-EA       Component A has granted exclusive access to a memory 
                                        region it owns to component B.
     4       Owner-NA   !Owner-SA       Component A has relinquished access to a memory 
                                        region it owns. Access to the memory region is shared
                                        between component B and at least one other component
     5       Owner-SA   !Owner-NA       Component A shares access to a region of memory it owns
                                        with another component. Component B cannot access the memory region.
     6       Owner-SA    !Owner-SA      Component A shares access to a region of memory it
                                        owns with component B and possibly other components.
   *)
  
  (** There are valid combinations of ownership and access states for each endpoint and 
       between two components. 
       
       To directly translate them, our state definition needs to contain ownership and access 
       states for each endpoint. However, our MemProperties is a global data structure that are 
       shared by all endpoints. Therefore, we re-interpret table 5.3. and 5.4. to represent them 
       with our MemProperties. For the local behaviours of each endpoint, we may be able to make a 
       project function from the global MemProperties (when we have a valid address range) or 
       we can add local MemProperties pool and always check consistency between that local pools
       with the global MemProperties later *)

  Definition mem_states_valid_combination
             (a b : ffa_UUID_t) (ownership: OWNERSHIP_STATE_TYPE) (access: ACCESS_STATE_TYPE) :=
    if decide (a <> b) 
    then match ownership, access with
         | Owned id, NoAccess =>
           if decide (a = id) || decide (b = id) then true else false                                  
         | Owned id, ExclusiveAccess id' =>
           if decide (a = id) || decide (b = id)
           then if decide (a = id') || decide (b = id') then true else false
           else false
         | Owned id, SharedAccess ids =>
           if decide (a = id) || decide (b = id)
           then if (in_dec zeq a ids) || (in_dec zeq b ids) then true else false
           else false
         | _, _ => false (* at least one component has ownerhsip *)
         end
    else false.
 
End VALID_COMBINATIONS.

(*************************************************************)
(** *                  step rules                            *)
(*************************************************************)
(** Multiple sections in the FF-A document are related to step rules in here. 

    From section 5.1 to section 5.5, they provide introductions.
    Parts of them are described in "FFAMemoryhypcallintro.v" file, while 
    some of them are also described at the beginning of this file as well. 
    
    Among them, contents in Section 5.5 needs to be captured in the transition rules. 
    
    From section 5.6 to section 5.9, they define state changes and lifecycles of 
    each FFA memory management call, but they are defined in a coarse-grained manner.
    In this sense, only referring those sections are not sufficient for us to define 
    top-level transition rules in the below. 

    Instead of that, we looked at chapter 11 (memory management interfaces) together to 
    find out the proper fine-grained transition rules. Chapter 11 provides syntax, sanity checks,
    and desired behaviors of each FFA interface. 

    From section 5.10 to 5.12, they provide data structures that FFA memory management interfaces
    have to use. They are defined in the "FFAMemoryHypCallDescriptorState.v" file. Among them,
    several sections, "5.11.2 Data access permissions usage", "5.11.3 Instruction access permissions usage",
    "5.11.4 Memory region attributes usage", and so on, describe invariants and proper usages of 
    descriptors. They also need to be reflected in our transition rules.

    Instead of writing all of them in a single definition per each FFA interface, 
    we divide the entire specs as multiple things as follows. 
    1. Core memory changes including ownership, access state, dirty bit in memory global properties and 
       local ownership flag in memory local properties. 
       - It only handles memory ownership, access, and dirty bit changes during transitions 
       - Instead of interpreting all descriptor values, it will pass the flag value as an argument to indicate 
         whether the memory region needs to be cleaned.
    2. Additional memory attributes and properties change.
       - It requires referring descriptors and the current attributes of the memory region.
    3. Check validity of descriptors and the current memory properties 
       - seciton 5.10, 5.11, 5.12 provide multiple constraints about descriptor information.
    4. Check validity of arguments and other related states except descriptor values
       - There are multiple constraints that section 11.x mentions for each interface. 
 *)

(** For the top-level modeling, we also provide specifications for dispatching. It reads the value from the current
    registers (abstract registers specified for FFA memory management specifications), and call proper specifications
    to trigger transitions. 

    To do that, we referred Hafinum's dispatch code (but we did not strictly follow the code).
*)
    

(*************************************************************)
(** *   1. Core memory ownership and access state change     *)
(*************************************************************)
(** This file contains a core transition rules of each FFA interface related to memory managements. 
   This does not include any safety check on arguments, attributes, and descriptors or consider 
   transitions on multiple pages. It only consider memory ownership and accessibility. *)

(** Transition rules in this file are similar to those in Jade's abstract machine definition. 
   - https://github.com/project-oak/hafnium-verification/tree/hfo2/coq-verification/src
*)
Section FFA_MEMORY_INTERFACE_CORE_STEPS.

  (** From section 5.7 to section 5.9, they provide valid before/after tables for the memory ownership and access states 
      according to FFA types. They are, however, focus on the end-to-end transitions bewteen two endpoints. Therefore, 
      they need to be divided into fine-grained steps. In this sense, we did not include all tables presented in
      section 5.7 to section 5.9 as comments in here. 
      However, our core transition rules try to faithfully reflect them. 
      
      In here, we discuss transaction lifecycles for each operations based on "5.6.2 Donate memory transaction lifecycle",
      "5.7.2 Lend memory transaction lifecycle", "5.8.2 Share memory transaction lifecycle", 
      and "5.9.2 Relinquish memory transaction lifecycle". 
   *)
  Context `{abstract_state_context: AbstractStateContext}.

  Notation HafniumEE := (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).

  Section FFA_MEM_DONATE_CORE_STEPS.    

    (*************************************************************)
    (** *             FFA_MEM_DONATE                             *)
    (*************************************************************)

    (** Related parts
     - 11.1.1.2 Relayer responsibilities
       There are two cases, but we only consider the case mentioned in 12.1.1, 
       the case when a Borrower is a PE endpoint.
       * Owner-NA for the Owner.
       * !Owner-NA for the Receiver.
     - Note that it differs from the well-defined transition in
       Table 5.9: Donate memory transaction state machine.
       This is due to the fact that the transition defined in "Table 5.9" is actually 
       divided into two parts, FFA_MEM_DONATE and FFA_MEM_RETRIEVE_REQ

       But, the possible initial state of two endpoints are defined in Table 5.10:
       Owner-EA !Owner-NA

       In here, we describe simple lifcycles mentioned in "5.6.2 Donate memory transaction lifecycle". 
       We discuss rules defined in section 11.1 in the below (the next section in this file).

       This transaction takes place as follows (also see 5.5.2 Transaction life cycle).
       1. The Owner uses the FFA_MEM_DONATE interface to describe the memory region and convey the
          identity of the Receiver to the Relayer as specified in Table 5.19. This interface is described in 11.1
          FFA_MEM_DONATE.
       2. If the Receiver is a PE endpoint or a SEPID associated with a dependent peripheral device,
          1. The Owner uses a Partition message to request the Receiver to retrieve the donated memory region. This
             message contains a description of the memory region relevant to the Receiver.
          2. The Receiver uses the FFA_MEM_RETRIEVE_REQ and FFA_MEM_RETRIEVE_RESP interfaces to
             map the memory region in its translation regime and complete the transaction. These interfaces are
             described in 11.4 FFA_MEM_RETRIEVE_REQ & 11.5 FFA_MEM_RETRIEVE_RESP respectively.
         In case of an error, the Sender can abort the transaction before the Receiver retrieves the memory region
         by calling the FFA_MEM_RECLAIM ABI (see 11.7 FFA_MEM_RECLAIM).
       3. If the Receiver is a SEPID associated with an independent peripheral device, an IMPLEMENTATION DEFINED
          mechanism is used by the Sender and Relayer to map and describe the memory region to the Receiver (see
          11.1.1 Component responsibilities for FFA_MEM_DONATE).
     *)
    
    Definition ffa_mem_donate_core_transition_spec (lender borrower : ffa_UUID_t) (address: Z) (clean: bool)
    : itree HafniumEE (unit) :=
      st <- trigger GetState ;;
      (** Find out memory properties *) 
      do global_property <- ZTree.get address st.(hafnium_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <- ZTree.get address lender_properties_pool ;;;
      (** check memory properties :
          1. lender has to have onwership
          2. lender has to have exclusive access to the address
          3. borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property, ZTree.get address borrower_properties_pool  with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None =>
        (** Check the valid onwership and accessibility combination for lender and borrower *)
        match mem_states_valid_combination lender borrower owned accessible,
              owned, accessible, local_owned with
        | true, Owned owner, ExclusiveAccess ex_accessor, LocalOwned =>
          if decide (owner = lender) && decide (ex_accessor = lender)
          then let new_dirty := if clean then MemClean else dirty in
               (** Only change accessibility option of the lender. The remaining operations will
                   be performed in the retrieve *)
               let new_global_properties := ZTree.set address (global_property {accessible_by: NoAccess}
                                                                               {mem_dirty : new_dirty})
                                                      st.(hafnium_context).(mem_properties).(mem_global_properties) in
               let new_st := st {hafnium_context / mem_properties :
                                   mkMemProperties new_global_properties
                                                   st.(hafnium_context).(mem_properties).(mem_local_properties)} in
               trigger (SetState new_st)
          else triggerUB "wrong behavior"
        | _, _, _, _ => triggerUB "wrong behavior"
        end
      | _, _, _ => triggerUB "wrong behavior"
      end.
         
  End FFA_MEM_DONATE_CORE_STEPS.

  Section FFA_MEM_LEND_CORE_STEPS.
    
  (* Related parts
     - 11.2.1.2 Relayer responsibilities
       There are two cases, but we only consider the case mentioned in 12.1.1, 
       the case when a Borrower is a PE endpoint.
       * Owner-NA for the Owner.
       * !Owner-NA for the Receiver.
     - Note that it differs from the well-defined transition in
       Table 5.10: Lend memory transaction state machine.
       This is due to the fact that the transition defined in "Table 5.10" is actually 
       divided into two parts, FFA_MEM_LEND and FFA_MEM_RETRIEVE_REQ

       But, the possible initial state of two endpoints are defined in Table 5.10:
       Owner-EA !Owner-NA

       In here, we describe simple lifcycles mentioned in "5.7.2 Lend memory transaction lifecycle". 
       We discuss rules defined in section 11.2 in the below (the next section in this file).

       This transaction takes place as follows (also see 5.5.2 Transaction life cycle).
       1. The Lender uses the FFA_MEM_LEND interface to describe the memory region and convey the identities of
          the Borrowers to the Relayer as specified in Table 5.19. This interface is described in 11.2 FFA_MEM_LEND.
       2. If a Borrower is a PE endpoint or a SEPID associated with a dependent peripheral device,
          1. The Lender uses a Partition message to request each Borrower to retrieve the lent memory region. This
             message contains a description of the memory region relevant to the Borrower.
          2. Each Borrower uses the FFA_MEM_RETRIEVE_REQ and FFA_MEM_RETRIEVE_RESP interfaces
             to map the memory region in its translation regime and complete the transaction. These interfaces are
             described in 11.4 FFA_MEM_RETRIEVE_REQ & 11.5 FFA_MEM_RETRIEVE_RESP respectively.
       3. If the Borrower is a SEPID associated with an independent peripheral device, an IMPLEMENTATION DEFINED
          mechanism is used by the Lender and Relayer to map and describe the memory region to the Borrower (see
          11.2.1 Component responsibilities for FFA_MEM_LEND).
       4. In case of an error, the Lender can abort the transaction before the Borrower retrieves the memory region by
          calling the FFA_MEM_RECLAIM ABI (see 11.7 FFA_MEM_RECLAIM).
   *)

    Definition ffa_mem_lend_core_transition_spec (lender borrower : ffa_UUID_t) (borrower_num : Z) (address: Z) (clean: bool)
    : itree HafniumEE (unit) :=
      st <- trigger GetState ;;
      (** Find out memory properties *) 
      do global_property <- ZTree.get address st.(hafnium_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <- ZTree.get address lender_properties_pool ;;;
      (** check memory properties :
          1. lender has to have onwership
          2. lender has to have exclusive access to the address
          3. borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property, ZTree.get address borrower_properties_pool, decide (borrower_num >= 1) with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None, left _ =>
        (** Check the valid onwership and accessibility combination for lender and borrower *)        
        match mem_states_valid_combination lender borrower owned accessible,
              owned, accessible, local_owned with
        | true, Owned owner, ExclusiveAccess ex_accessor, LocalOwned =>
          if decide (owner = lender) && decide (ex_accessor = lender)
          then let new_dirty := if clean then MemClean else dirty in
               (** Only change accessibility option of the lender. The remaining operations will
                   be performed in the retrieve *)                 
               let new_global_properties := ZTree.set address (global_property {accessible_by: NoAccess}
                                                                               {mem_dirty : new_dirty})
                                                      st.(hafnium_context).(mem_properties).(mem_global_properties) in
               let new_st := st {hafnium_context / mem_properties :
                                   mkMemProperties new_global_properties
                                                   st.(hafnium_context).(mem_properties).(mem_local_properties)} in
               trigger (SetState new_st)
          else triggerUB "wrong behavior"
        | _, _, _, _ => triggerUB "wrong behavior"
        end
      | _, _, _, _ => triggerUB "wrong behavior"
      end.
    
  End FFA_MEM_LEND_CORE_STEPS.
    
  Section FFA_MEM_SHARE_CORE_STEPS.

  (* Related parts
     - 11.3.1.2 Relayer responsibilities
       There are two cases, but we only consider the case mentioned in 12.1.1, 
       the case when a Borrower is a PE endpoint.
       * Owner-SA for the Owner.
       * !Owner-NA for the Receiver.
     - Note that it differs from the well-defined transition in
       Table 5.11: Share memory transaction state machine.
       This is due to the fact that the transition defined in "Table 5.11" is actually 
       divided into two parts, FFA_MEM_SHARE and FFA_MEM_RETRIEVE_REQ 

       But, the possible initial state of two endpoints are defined in Table 5.10:
       Owner-EA !Owner-NA

       In here, we describe simple lifcycles mentioned in "5.8.2 Share memory transaction lifecycle". 
       We discuss rules defined in section 11.3 in the below (the next section in this file).

       This transaction takes place as follows (also see 5.5.2 Transaction life cycle).
       1. The Lender uses the FFA_MEM_SHARE interface to describe the memory region and convey the identities of
          the Borrowers to the Relayer as specified in Table 5.19. This interface is described in 11.2 FFA_MEM_LEND.
       2. If a Borrower is a PE endpoint or a SEPID associated with a dependent peripheral device,
          1. The Lender uses a Partition message to request each Borrower to retrieve the shared memory region.
             This message contains a description of the memory region relevant to the Borrower.
          2. Each Borrower uses the FFA_MEM_RETRIEVE_REQ and FFA_MEM_RETRIEVE_RESP interfaces
             to map the memory region in its translation regime and complete the transaction. These interfaces are
             described in 11.4 FFA_MEM_RETRIEVE_REQ & 11.5 FFA_MEM_RETRIEVE_RESP respectively.
       3. If the Borrower is a SEPID associated with an independent peripheral device, an IMPLEMENTATION DEFINED
          mechanism is used by the Lender and Relayer to map and describe the memory region to the Borrower (see
          11.3.1 Component responsibilities for FFA_MEM_SHARE).
       4. In case of an error, the Lender can abort the transaction before the Borrower retrieves the memory region by
          calling the FFA_MEM_RECLAIM ABI (see 11.7 FFA_MEM_RECLAIM).
   *)
    Definition ffa_mem_share_core_transition_spec (lender borrower : ffa_UUID_t) (address: Z) (clean: bool)
    : itree HafniumEE (unit) :=
      st <- trigger GetState ;;
      (** Find out memory properties *) 
      do global_property <- ZTree.get address st.(hafnium_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <- ZTree.get address lender_properties_pool ;;;
      (** check memory properties :
          1. lender has to have onwership
          2. lender has to have exclusive access to the address
          3. borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property, ZTree.get address borrower_properties_pool with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None =>
        (** Check the valid onwership and accessibility combination for lender and borrower *)        
        match mem_states_valid_combination lender borrower owned accessible,
              owned, accessible, local_owned with
        | true, Owned owner, ExclusiveAccess ex_accessor, LocalOwned =>
          if decide (owner = lender) && decide (ex_accessor = lender)
          then let new_dirty := if clean then MemClean else dirty in
               (** Only change accessibility option of the lender. The remaining operations will
                   be performed in the retrieve *)                 
               let new_global_properties := ZTree.set address (global_property {accessible_by: SharedAccess (lender::nil)}
                                                                               {mem_dirty : new_dirty})
                                                      st.(hafnium_context).(mem_properties).(mem_global_properties) in
               let new_st := st {hafnium_context / mem_properties :
                                   mkMemProperties new_global_properties
                                                   st.(hafnium_context).(mem_properties).(mem_local_properties)} in
               trigger (SetState new_st)
          else triggerUB "wrong behavior"
        | _, _, _, _ => triggerUB "wrong behavior"
        end
      | _, _, _ => triggerUB "wrong behavior"
      end.

  End FFA_MEM_SHARE_CORE_STEPS.

  Section FFA_MEM_RETRIEVE_REQ_CORE_STEP.

  (* Related parts
     - 11.4.1.2 Relayer responsibilities
       Depending on the previous call and recipient numbers, retrieve request has 
       different behaviors. 
       
       If the transaction type is FFA_MEM_DONATE,
       – !Owner-NA for the Owner.
       – Owner-EA for the Receiver
   
       If the transaction type is FFA_MEM_LEND, and the count of Borrowers in the transaction is = 1,
       – Owner-NA for the Lender.
       – !Owner-EA for the Borrower

       If the transaction type is FFA_MEM_LEND, and the count of Borrowers in the transaction is > 1,
       – Owner-SA for the Lender.
       – !Owner-SA for the Borrower.

       If the transaction type is FFA_MEM_SHARE,
       – Owner-SA for the Lender.
       – !Owner-SA for the Borrower.

       - Note that it describes the second half behaviors of the following transitions.
       Table 5.9: Donate memory transaction state machine.
       Table 5.10: Lend memory transaction state machine.
       Table 5.11: Share memory transaction state machine.

       We discuss rules defined in section 11.4 in the below (the next section in this file).
   *)

    Definition ffa_mem_donate_retrieve_req_core_transition_spec (lender borrower : ffa_UUID_t) (address: Z) (clean: bool)
    : itree HafniumEE (unit) :=
      st <- trigger GetState ;;
      (** Find out memory properties *) 
      do global_property <- ZTree.get address st.(hafnium_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <- ZTree.get address lender_properties_pool ;;;
      (** check memory properties :
          1. lender has to have onwership
          2. lender has to have exclusive access to the address
          3. borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property, ZTree.get address borrower_properties_pool  with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None =>
        (** Check the valid onwership and accessibility combination for lender and borrower *)
        match mem_states_valid_combination lender borrower owned accessible,
              owned, accessible, local_owned with
        | true, Owned owner, NoAccess, LocalOwned =>
          if decide (owner = lender)
          then let new_dirty := if clean then MemClean else dirty in
               (** Only change accessibility option of the lender. The remaining operations will
                   be performed in the retrieve *)
               let new_global_properties := ZTree.set address (global_property
                                                                 {owned_by: Owned borrower}
                                                                 {accessible_by: ExclusiveAccess borrower}
                                                                 {mem_dirty : new_dirty})
                                                      st.(hafnium_context).(mem_properties).(mem_global_properties) in
               (** Remove the corresponding map in the lender memory local properties pool *)
               let new_lender_properties_pool := ZTree.remove address lender_properties_pool in
               (** Create the new  memory local properties pool for the borrower.
                Instead of making a new initial state, we copied the previous local properties that lender had. 
                Next opeartions can adjust the properties if it is necessary *)
               let new_borrower_properties_pool := ZTree.set address (gen_own_mem_local_properties_wrapper lender_property) 
                                                             borrower_properties_pool in
               let new_local_properties_global_pool' := ZTree.set lender new_lender_properties_pool
                                                                  st.(hafnium_context).(mem_properties).(mem_local_properties) in
               let new_local_properties_global_pool := ZTree.set borrower new_borrower_properties_pool
                                                                 new_local_properties_global_pool' in
               let new_st := st {hafnium_context / mem_properties :
                                   mkMemProperties new_global_properties new_local_properties_global_pool} in
               trigger (SetState new_st)
          else triggerUB "wrong behavior"
        | _, _, _, _ => triggerUB "wrong behavior"
        end
      | _, _, _ => triggerUB "wrong behavior"
      end.


    Definition add_accessor (borrower : ffa_UUID_t) (borrower_num : Z) (access_state : ACCESS_STATE_TYPE) :=
      match access_state, decide (borrower_num > 1) with 
      | NoAccess, left _ => Some (SharedAccess (borrower::nil))
      | NoAccess, right _ => Some (ExclusiveAccess borrower)
      | SharedAccess borrowers, left _ => Some (SharedAccess (borrower::borrowers))
      | _, _ => None
      end.
    
    Definition ffa_mem_lend_retrieve_req_core_transition_spec (lender borrower : ffa_UUID_t) (borrower_num : Z) (address: Z) (clean: bool)
    : itree HafniumEE (unit) :=
      st <- trigger GetState ;;
      (** Find out memory properties *) 
      do global_property <- ZTree.get address st.(hafnium_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <- ZTree.get address lender_properties_pool ;;;
      (** check memory properties :
          1. lender has to have onwership
          2. lender has to have exclusive access to the address
          3. borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property, ZTree.get address borrower_properties_pool, decide (borrower_num >= 1)  with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None, left _ =>
        (** Check the valid onwership and accessibility combination for lender and borrower *)
        match mem_states_valid_combination lender borrower owned accessible,
              owned, add_accessor borrower borrower_num accessible, local_owned with
        | true, Owned owner, Some new_accessibility, LocalOwned =>
          if decide (owner = lender)
          then let new_dirty := if clean then MemClean else dirty in
               (** Only change accessibility option of the lender. The remaining operations will
                   be performed in the retrieve *)
               let new_global_properties := ZTree.set address (global_property
                                                                 {owned_by: Owned borrower}
                                                                 {accessible_by: new_accessibility}
                                                                 {mem_dirty : new_dirty})
                                                      st.(hafnium_context).(mem_properties).(mem_global_properties) in
               (** Create the new memory local properties pool for the borrower.
                Instead of making a new initial state, we copied the previous local properties that lender had. 
                Next opeartions can adjust the properties if it is necessary *)
               let new_borrower_properties_pool := ZTree.set address (gen_borrow_mem_local_properties_wrapper lender lender_property) 
                                                             borrower_properties_pool in
               let new_local_properties_global_pool := ZTree.set borrower new_borrower_properties_pool
                                                                 st.(hafnium_context).(mem_properties).(mem_local_properties) in
               let new_st := st {hafnium_context / mem_properties :
                                   mkMemProperties new_global_properties new_local_properties_global_pool} in
               trigger (SetState new_st)
          else triggerUB "wrong behavior"
        | _, _, _, _ => triggerUB "wrong behavior"
        end
      | _, _, _, _ => triggerUB "wrong behavior"
      end.

    Definition ffa_mem_share_retrieve_req_core_transition_spec (lender borrower : ffa_UUID_t) (address: Z) (clean: bool)
    : itree HafniumEE (unit) :=
      st <- trigger GetState ;;
      (** Find out memory properties *) 
      do global_property <- ZTree.get address st.(hafnium_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <- ZTree.get address lender_properties_pool ;;;
      (** check memory properties :
          1. lender has to have onwership
          2. lender has to have exclusive access to the address
          3. borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property, ZTree.get address borrower_properties_pool  with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None =>
        (** Check the valid onwership and accessibility combination for lender and borrower *)
        match mem_states_valid_combination lender borrower owned accessible,
              owned, accessible, local_owned with
        | true, Owned owner, SharedAccess (accessor::nil), LocalOwned =>
          if decide (owner = lender) && decide (accessor = lender)
          then let new_dirty := if clean then MemClean else dirty in
               (** Only change accessibility option of the lender. The remaining operations will
                   be performed in the retrieve *)
               let new_global_properties := ZTree.set address (global_property
                                                                 {owned_by: Owned borrower}
                                                                 {accessible_by: SharedAccess (borrower::lender::nil)}
                                                                 {mem_dirty : new_dirty})
                                                      st.(hafnium_context).(mem_properties).(mem_global_properties) in
               (** Create the new  memory local properties pool for the borrower.
                Instead of making a new initial state, we copied the previous local properties that lender had. 
                Next opeartions can adjust the properties if it is necessary *)
               let new_borrower_properties_pool := ZTree.set address (gen_borrow_mem_local_properties_wrapper lender lender_property) 
                                                             borrower_properties_pool in
               let new_local_properties_global_pool := ZTree.set borrower new_borrower_properties_pool
                                                                 st.(hafnium_context).(mem_properties).(mem_local_properties) in
               let new_st := st {hafnium_context / mem_properties :
                                   mkMemProperties new_global_properties new_local_properties_global_pool} in
               trigger (SetState new_st)
          else triggerUB "wrong behavior"
        | _, _, _, _ => triggerUB "wrong behavior"
        end
      | _, _, _ => triggerUB "wrong behavior"
      end.

  End FFA_MEM_RETRIEVE_REQ_CORE_STEP.
  
  Section FFA_MEM_RELINQUISH_CORE_STEPS.

    (* Related parts.
       In here, we describe simple lifcycles mentioned in "5.9.2 Relinquish memory transaction lifecycle". 
       We discuss rules defined in section 11.6 in the below (the next section in this file).

       This transaction takes place as follows (also see 5.5.2 Transaction life cycle). It is assumed that the memory region
       was originally lent or shared by the Lender to the Borrowers. This transaction must not be used on a memory
       region owned by an endpoint.

       1. If a Borrower is a PE endpoint or a SEPID associated with a dependent peripheral device,
          1. The Lender could use a Partition message to request each Borrower to relinquish access to the memory
             region. This message contains a description of the memory region relevant to the Borrower.
          2. Each Borrower uses the FFA_MEM_RELINQUISH interface (see 11.6 FFA_MEM_RELINQUISH) to
             unmap the memory region from its translation regime. This could be done in response to the message
             from the Lender or independently.
          3. Each Borrower uses a Partition message to inform the Lender that it has relinquished access to the
             memory region.
          In case of an error, the Borrower can abort the transaction before the Lender reclaims the memory region by
          calling the FFA_MEM_RETRIEVE_REQ ABI (see 11.4 FFA_MEM_RETRIEVE_REQ).
       2. If the Borrower is a SEPID associated with an independent peripheral device,
          1. The Lender could use an IMPLEMENTATION DEFINED mechanism to request each Borrower to relinquish
             access to the memory region.
          2. Each Borrower uses an IMPLEMENTATION DEFINED mechanism to request the Relayer to
             unmap the memory region from its translation regime (see 11.7.1 Component responsibilities
             for FFA_MEM_RECLAIM). This could be done in response to the message from the Lender or
             independently.
          3. Each Borrower uses an IMPLEMENTATION DEFINED mechanism to inform the Lender that it has
             relinquished access to the memory region.
       3. Once all Borrowers have relinquished access to the memory region, the Lender uses the FFA_MEM_RECLAIM
          interface to reclaim exclusive access to the memory region. This interface is described in 11.7
          FFA_MEM_RECLAIM.
     *)
    
    Definition remove_accessor (lender borrower : ffa_UUID_t) (access_state : ACCESS_STATE_TYPE) :=
      match access_state with 
      | ExclusiveAccess borrower' => if decide (borrower = borrower')
                                    then Some (ExclusiveAccess lender)
                                    else None
      | SharedAccess (shared_vms) =>
        match shared_vms with
        | nil => None
        | borrower'::nil => if decide (borrower = borrower') then Some (ExclusiveAccess lender) else None
        | fst::snd::nil =>
          (** This is the case for Share. Lend opeartion excludes lender's access, so this thing cannot happen.
              The order is specified in the previous lend operation. So there is no chance for fst to be a lender *)
          if (decide (snd = lender) && decide (fst = borrower))
          then Some (ExclusiveAccess lender)
          else
            (** This is the case for Lend. Lend opeartion excludes lender's access, so we check it
                - we can ignore them. I believe ignoring them is safe *)
            match (List.In_dec zeq borrower shared_vms), (List.In_dec zeq lender shared_vms) with
            | left _, right _ =>   Some (SharedAccess (List.remove zeq borrower shared_vms))
            | _, _ => None
            end
        (** This is the case for Lend. Lend opeartion excludes lender's access, so we check it
            - we can ignore them. I believe ignoring them is safe *)
        | _ => match (List.In_dec zeq borrower shared_vms), (List.In_dec zeq lender shared_vms) with
              | left _, right _ =>   Some (SharedAccess (List.remove zeq borrower shared_vms))
              | _, _ => None
              end
        end
      | _ => None
      end.

    Definition ffa_mem_relinquish_core_transition_spec (lender borrower : ffa_UUID_t) (address: Z) (clean: bool)
      : itree HafniumEE (unit) :=
      st <- trigger GetState ;;
      (** Find out memory properties *) 
      do global_property <- ZTree.get address st.(hafnium_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hafnium_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <- ZTree.get address lender_properties_pool ;;;
      (** check memory properties :
          1. lender has to have onwership
          2. lender has to have exclusive access to the address
          3. borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property, ZTree.get address borrower_properties_pool  with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None =>
        (** Check the valid onwership and accessibility combination for lender and borrower *)
        match mem_states_valid_combination lender borrower owned accessible,
              owned, remove_accessor lender borrower accessible, local_owned with
        | true, Owned owner, Some new_accessibility, LocalOwned =>
          if decide (owner = lender)
          then let new_dirty := if clean then MemClean else dirty in
               (** Only change accessibility option of the lender. The remaining operations will
                   be performed in the retrieve *)
               let new_global_properties := ZTree.set address (global_property
                                                                 {owned_by: Owned lender}
                                                                 {accessible_by: new_accessibility}
                                                                 {mem_dirty : new_dirty})
                                                      st.(hafnium_context).(mem_properties).(mem_global_properties) in
               (** Create the new  memory local properties pool for the borrower.
                Instead of making a new initial state, we copied the previous local properties that lender had. 
                Next opeartions can adjust the properties if it is necessary *)               
               let new_borrower_properties_pool := ZTree.remove address borrower_properties_pool in
               let new_local_properties_global_pool := ZTree.set borrower new_borrower_properties_pool
                                                                 st.(hafnium_context).(mem_properties).(mem_local_properties) in
               let new_st := st {hafnium_context / mem_properties :
                                   mkMemProperties new_global_properties new_local_properties_global_pool} in
               trigger (SetState new_st)
          else triggerUB "wrong behavior"
        | _, _, _, _ => triggerUB "wrong behavior"
        end
      | _, _, _ => triggerUB "wrong behavior"
      end.

  End FFA_MEM_RELINQUISH_CORE_STEPS.

  (* For FFA_MEM_RETRIEVE_RESP and FFA_MEM_RECLAIM, the memory state won't be changed. 
     FFA_MEM_RETRIEVE_RESP is the return value of RRA_MEM_RETRIEVE_REQ, and FFA_MEM_RECLAIM 
     is the mssage to trigger FFA_MEM_RELINQUISH. *)
  
End FFA_MEMORY_INTERFACE_CORE_STEPS.

(***********************************************************************)
(** *    Invariant and additional steps for transitions                *)
(***********************************************************************)
Section FFA_MEMORY_INTERFACE_INVARIANTS_AND_ADDITIONAL_STEPS.

  Context `{abstract_state_context: AbstractStateContext}.
  
  Notation HafniumEE := (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).
  
  Section FFA_MEM_DONATE_INVARIANTS_AND_ADDITIONAL_STEPS.
    (** 11.1 FFA_MEM_DONATE *)
    
  End FFA_MEM_DONATE_INVARIANTS_AND_ADDITIONAL_STEPS.

  Section FFA_MEM_LEND_INVARIANTS_AND_ADDITIONAL_STEPS.
    (** 11.2 FFA_MEM_LEND *)
    
  End FFA_MEM_LEND_INVARIANTS_AND_ADDITIONAL_STEPS.

  Section FFA_MEM_SHARE_INVARIANTS_AND_ADDITIONAL_STEPS.
    (** 11.3 FFA_MEM_SHARE *)

  End FFA_MEM_SHARE_INVARIANTS_AND_ADDITIONAL_STEPS.

  Section FFA_MEM_RETRIEVE_REQ_INVARIANTS_AND_ADDITIONAL_STEPS.
    (** 11.4 FFA_MEM_RETRIEVE_REQ *)
    
  End FFA_MEM_RETRIEVE_REQ_INVARIANTS_AND_ADDITIONAL_STEPS.

  Section FFA_MEM_RETRIEVE_RESP_INVARIANTS_AND_ADDITIONAL_STEPS.
    (** 11.5 FFA_MEM_RETRIEVE_RESP *)
    
  End FFA_MEM_RETRIEVE_RESP_INVARIANTS_AND_ADDITIONAL_STEPS.

  Section FFA_MEM_RELINQUISH_INVARIANTS_AND_ADDITIONAL_STEPS.
    (** 11.6 FFA_MEM_RELINQUISH *)

  End FFA_MEM_RELINQUISH_INVARIANTS_AND_ADDITIONAL_STEPS.
    
  Section FFA_MEM_RECLAIM_INVARIANTS_AND_ADDITIONAL_STEPS.
    (** 11.7 FFA_MEM_RECLAIM *)
  
  End FFA_MEM_RECLAIM_INVARIANTS_AND_ADDITIONAL_STEPS.
    
End FFA_MEMORY_INTERFACE_INVARIANTS_AND_ADDITIONAL_STEPS.

(***********************************************************************)
(** *    Invariant and additional steps for transitions                *)
(***********************************************************************)
Section FFA_MEMORY_INTERFACE_ARGUMENT_CHECKS.

  Context `{abstract_state_context: AbstractStateContext}.
  
  Notation HafniumEE := (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).

  (* TODO: Need to fix the following definition *)
  Definition ffa_mem_send_check_arguments_spec
             (func_type : FFA_FUNCTION_TYPE) 
             (length fragment_length address page_count: Z)
    : itree HafniumEE (FFA_value_type) :=
    match func_type with
    | FFA_MEM_DONATE 
    | FFA_MEM_LEND 
    | FFA_MEM_SHARE =>
      if decide (address = 0) || decide (page_count = 0) ||
                decide (length <> fragment_length) ||
                decide (length >  HF_MAILBOX_SIZE) (* ||
                decide (length >  MM_PPOOL_ENTRY_SIZE) *)
      then Ret (ffa_error FFA_INVALID_PARAMETERS)
      else Ret (init_FFA_value_type)
    (* This case cannot happen if we look at the calling sequence of this spec *)
    | _ => triggerUB "ffa_mem_send_check_arguments: wrong arguments"
    end.
  
  Section FFA_MEM_DONATE_ARGUMENT_CHECKS.
    (** 11.1 FFA_MEM_DONATE *)
    
  End FFA_MEM_DONATE_ARGUMENT_CHECKS.

  Section FFA_MEM_LEND_ARGUMENT_CHECKS.
    (** 11.2 FFA_MEM_LEND *)
    
  End FFA_MEM_LEND_ARGUMENT_CHECKS.

  Section FFA_MEM_SHARE_ARGUMENT_CHECKS.
    (** 11.3 FFA_MEM_SHARE *)

  End FFA_MEM_SHARE_ARGUMENT_CHECKS.

  Section FFA_MEM_RETRIEVE_REQ_ARGUMENT_CHECKS.
    (** 11.4 FFA_MEM_RETRIEVE_REQ *)
    
  End FFA_MEM_RETRIEVE_REQ_ARGUMENT_CHECKS.

  Section FFA_MEM_RETRIEVE_RESP_ARGUMENT_CHECKS.
    (** 11.5 FFA_MEM_RETRIEVE_RESP *)
    
  End FFA_MEM_RETRIEVE_RESP_ARGUMENT_CHECKS.

  Section FFA_MEM_RELINQUISH_ARGUMENT_CHECKS.
    (** 11.6 FFA_MEM_RELINQUISH *)

  End FFA_MEM_RELINQUISH_ARGUMENT_CHECKS.
    
  Section FFA_MEM_RECLAIM_ARGUMENT_CHECKS.
    (** 11.7 FFA_MEM_RECLAIM *)
  
  End FFA_MEM_RECLAIM_ARGUMENT_CHECKS.
    
End FFA_MEMORY_INTERFACE_ARGUMENT_CHECKS.

(***********************************************************************)
(** *                 Context switching related parts                  *)
(***********************************************************************)
Section FFAContextSwitching.
  
  Context `{abstract_state_context: AbstractStateContext}.
  
  Notation HafniumEE := (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).
  (**
     [JIEUNG:We referred context switchigns in Hafnium, but we believe it could be similar when 
     we provide abstract models for different implementations]
     
     In Hafnium, most parts are related to save registers in "/src/arch/aarch64/hypervisor/exceptions.S"
     We dramatically simplify them by saving and restoring FFA-related register values. 
     In reality, we may need to reflect the entire register save and recovery in the file:
     "save_volatile_to_vcpu", "save_register_access", "vcpu_switch", "vcpu_restore_all_and_run",
     "vcpu_restore_lazy_and_run", "vcpu_restore_nonvolatile_and_run", and 
     "vcpu_restore_volatile_and_run" in  "/src/arch/aarch64/hypervisor/exceptions.S". 
    
     In addition to that, "handle_system_register_access" in "/src/arch/aarch64/hypervisor/handler.c"
     also a function that handles register values when handling exceptions. 
    
     How it works:
     When an exception occurs, it first checks the exception value in the register ("vector_table_el2" 
     in the file). Then, if the exception number is either "sync_lower_64" or "sync_lower_32", 
     it calls "lower_sync_exception" defined in the same file. 
     
     Then, "lower_sync_exception" performs context switching and calls a C handler function to
     service the exception.
   *)
  (** Save contexts *)    
  Definition save_regs_to_vcpu_spec  :
    itree HafniumEE (unit) := 
    st <- trigger GetState;;
    (* check whether the current running entity is one of VMs *)
    if decide (st.(cur_entity_id) <> hafnium_id) && in_dec zeq st.(cur_entity_id) vm_ids
    then (* get contexts for the currently running entity ID *)
      do vm_userspace <- ZTree.get st.(cur_entity_id) st.(vms_userspaces) ;;;
      do vcpu_regs <- ZTree.get vm_userspace.(userspace_cur_vcpu_index) vm_userspace.(userspace_vcpus) ;;;
      (* get vm contexts in Hanfium to save the userspace information in it *)              
      do vm_context <- ZTree.get st.(cur_entity_id) st.(hafnium_context).(vms_contexts) ;;;
      if decide (vm_context.(vcpu_num) = vm_userspace.(userspace_vcpu_num)) &&
         decide (vcpu_regs.(vm_id) = Some st.(cur_entity_id))
      then
        let new_vcpu_id := vm_userspace.(userspace_cur_vcpu_index) in
        let new_vm_context := vm_context {vm_cur_vcpu_index: new_vcpu_id}
                                         {vm_vcpus:
                                            ZTree.set new_vcpu_id vcpu_regs vm_context.(vcpus)} in
        let new_vms_contexts :=
            ZTree.set st.(cur_entity_id) new_vm_context st.(hafnium_context).(vms_contexts) in
        let new_st := st {cur_entity_id: hafnium_id}
                         {hafnium_context/tpidr_el2: Some vcpu_regs}
                         {hafnium_context/vms_contexts: new_vms_contexts} in 
        trigger (SetState new_st)
      else triggerUB "save_resg_to_vcpu_spec: inconsistency in total vcpu number"
    else triggerUB "save_resg_to_vcpu_spec: wrong cur entity id".
  
  Definition save_regs_to_vcpu_call (args : list Lang.val) :=
    match args with
    | nil => save_regs_to_vcpu_spec
    | _ => triggerUB "save_regs_to_vcpu_call: wrong arguments"
    end.
  
  (** Restore contexts and run.
     It also contains choosing the next vm to run by using an abstract scheduler  
   *)
  Definition vcpu_restore_and_run_spec  :
    itree HafniumEE (unit) := 
    st <- trigger GetState;;
    (** find out the next vm to be scheduled *)
    let next_vm_id := scheduler st in
    (** check whether the current running entity is Hafnium *)
    if decide (st.(cur_entity_id) = hafnium_id) && in_dec zeq next_vm_id vm_ids
    then
      (** get the userspace information *)
      do vm_userspace <- ZTree.get next_vm_id st.(vms_userspaces) ;;;
      (** get vm context to restore the userspace information *)
      do vm_context <- ZTree.get next_vm_id st.(hafnium_context).(vms_contexts) ;;;
      (** get vcpu register information *)
      do vcpu_regs <- ZTree.get vm_context.(cur_vcpu_index) vm_context.(vcpus) ;;;
         if decide (vm_context.(vcpu_num) = vm_userspace.(userspace_vcpu_num)) &&
            decide (vm_context.(cur_vcpu_index) = vm_userspace.(userspace_cur_vcpu_index)) &&
            decide (vcpu_regs.(vm_id) = Some next_vm_id)
            (* TODO: add cpu connection check with vcpu_regs later *)
         then
           let new_vm_userspace := 
               vm_userspace {userspace_vcpus :
                               (ZTree.set (vm_userspace.(userspace_cur_vcpu_index))
                                          vcpu_regs (vm_userspace.(userspace_vcpus)))} in
           let new_vms_userspaces :=
               ZTree.set next_vm_id new_vm_userspace st.(vms_userspaces) in
           let new_st := st {cur_entity_id: next_vm_id}
                            {hafnium_context/tpidr_el2: None}
                            {vms_userspaces: new_vms_userspaces} in 
           trigger (SetState new_st)
         else triggerUB "vcpu_restore_and_run__spec: inconsistency in vcpu number"
    else triggerUB "vcpu_restore_and_run__spec: wrong cur entity id".
  
  Definition vcpu_restore_and_run_call (args : list Lang.val) :=
    match args with
    | nil => vcpu_restore_and_run_spec
    | _ => triggerUB "vcpu_restore_and_run_call: wrong arguments"
    end.
  
End FFAContextSwitching.

(***********************************************************************)
(** *                       FFA Dispatch                               *)
(***********************************************************************)
Section FFADispatch.
    
    
End FFADispatch.  





(******************************************************************************)
(* The following parts are archived ones.
   Some needs to be moved to some parts while working on them, so I am keeping them at this moment *)   

(*

  (************************************************************************)
  (*                 FFA ABI for memory management                        *)
  (************************************************************************)
  (* All the following things are calls via "struct vcpu *sync_lower_exception(uintreg_t esr)" 
     defined in "/src/arch/aarch64/hypervisor/handler.c". 

     Depending on "uintreg_t ec = GET_ESR_EC(esr);", the exception case, the function calls
     the proper handler. The main focus of our prototyping is when "EC_HVC", which are for 
     hypervisor calls.
     
     "struct vcpu *hvc_handler(struct vcpu *vcpu)" is also a function that is defined in the same file.

     For all cases that we consider in here, "(ffa_handler(&args, &next))" is a function 
     that handles ffa related exceptions and return true.

     "static bool ffa_handler(struct ffa_value *args, struct vcpu **next)" is also a function in the
     the same file. Among all cases, cases they we are considering are as follows.

     <<
	case FFA_MEM_DONATE_32:
	case FFA_MEM_LEND_32:
	case FFA_MEM_SHARE_32:
		*args = api_ffa_mem_send(func, args->arg1, args->arg2,
					 ipa_init(args->arg3), args->arg4,
					 current(), next);
		return true;
	case FFA_MEM_RETRIEVE_REQ_32:
		*args = api_ffa_mem_retrieve_req(args->arg1, args->arg2,
						 ipa_init(args->arg3),
						 args->arg4, current());
		return true;
	case FFA_MEM_RELINQUISH_32:
		*args = api_ffa_mem_relinquish(current());
		return true;
	case FFA_MEM_RECLAIM_32:
		*args = api_ffa_mem_reclaim(
			ffa_assemble_handle(args->arg1, args   ->arg2), args->arg3,
			current());     
    >>
  *)


  Section FFADispatch.
    
    
  End FFADispatch.  
  
  (* Send is for three FFA ABIs, SHARE, DONATE, and LEND. *)
  Section FFAMemoryHypCallSend.

    (* FFA_MEM_DONATE, FFA_MEM_LEND, and FFA_MEM_SHARE shares the common features. 
       Therefore, Hafnium provides a uniform interface for that. *)

    (* 
       Chapter 11 of "https://developer.arm.com/documentation/den0077/latest" provides interfaces for 
       those FFA ABIs

       Table 11.3: FFA_MEM_DONATE function syntax 
       Table 11.8: FFA_MEM_LEND function syntax 
       Table 11.13: FFA_MEM_SHARE function syntax 

       parameter                  register        value                  
       uint32 Function ID         w0              0x84000071 for FFA_MEM_DONATE
                                                  0x84000072 for FFA_MEM_LEND
                                                  0x84000073 for FFA_MEM_SHARE
       uint32 total length        w1              Total length of the memory transaction descriptor in
                                                  bytes
       uint32 Fragment length     w2              It's for more fine-grained control, but it will be 
                                                  ignored in here (the value in w1 has to be equal to 
                                                  be the value in w2).
       uint32/uint64 Address      w3              Base address of a buffer allocated by the Owner and
                                                  distinct from the TX buffer. More information is
                                                  in 12.2.1. MBZ if the TX buffer is used.
       uint32 Page count          w4              Number of 4K page in the buffer allocated by the 
                                                  Owner and distinct from the TX buffer. More details
                                                  are in 12.2.1. MBZ if the TX buffer is used

     *)

    
    (* FFA_SUCCESS encoding 
       Table 11.4, Table 11.9, Table 11.14

       uint64 Handle           w2/w3            Global unique Handle to identify the memory region on 
                                                successful transition of the transaction descriptor. 
                                                MBZ otherwise. Details about Handle is in 5.10.2. *)
    
    (* FFA_ERROR encoding 
       Table 11.5, Table 11.10, Table 11.15

       uint32 Error Code        w2              INVALID_PARAMETER / DENIED / NO_MEMORY /
                                                BUSY / ABORTED *)

    (* 
       1. Check arguments
       2. Read tpidr_el2 to find out the sender 
       3. Read the mailbox to find out the region information.
       4. Read receivers 
       5. validate check
       6. Check mem properties
       7. Update mem properties 
     *)

    (* 
       It is dramatically simplified version. It does the following things. 
       1. check the arguments 
       2. check the arguments with the memory_region descriptor 
          check the memory attributes 
       3.  change the memory attributes
       4. record the value in the buffer to deliver it to the receiver 
       5. return the result
     *)

    (* check arguments
       - Check basic arguments that are given by VMs (by registers
     *)
    Definition ffa_mem_send_check_arguments_spec
               (func_type : FFA_FUNCTION_TYPE) 
               (length fragment_length address page_count: Z)
    : itree HafniumEE (FFA_value_type) :=
      match func_type with
      | FFA_MEM_DONATE 
      | FFA_MEM_LEND 
      | FFA_MEM_SHARE =>
        if decide (address = 0) || decide (page_count = 0) ||
                  decide (length <> fragment_length) ||
                  decide (length >  HF_MAILBOX_SIZE) ||
                  decide (length >  MM_PPOOL_ENTRY_SIZE)
        then Ret (ffa_error FFA_INVALID_PARAMETERS)
        else Ret (init_FFA_value_type)
      (* This case cannot happen if we look at the calling sequence of this spec *)
      | _ => triggerUB "ffa_mem_send_check_arguments: wrong arguments"
      end.

    Definition get_receiver (access_descriptors: list FFA_endpoint_memory_access_descriptor_struct)
      : option FFA_endpoint_memory_access_descriptor_struct :=
      match access_descriptors with
      | hd::nil => Some hd
      | _ => None
      end.

    (* check the given descriptor and return some necessary values for the further process *)
    (* Since Hafnium only uses its RX/TX buffers for memory transitions, it requires several checks 
       by using the given descriptors recorded in RX/TX buffers. The following one also extracts 
       several information from the descriptor. 
     *)
    Definition ffa_mem_send_check_memory_region_descriptor_spec (func_type : FFA_FUNCTION_TYPE)
               (current_vm_id : Z)
      : itree HafniumEE (FFA_value_type * FFA_memory_region_struct *
                         ffa_vm_id_t (* receiver *) * bool (* clear or not-clear *) *
                         FFA_INSTRUCTION_ACCESS_TYPE * FFA_DATA_ACCESS_TYPE (* permission *)) :=
      st <- trigger GetState;; 
      (* Check mailbox and convert it into the region descriptor *)
      do sender_vm_context <- ZTree.get current_vm_id st.(hafnium_context).(vms_contexts);;;
      match mailbox_send_msg_to_region_struct (sender_vm_context.(mailbox).(send)) with 
      | None => Ret (ffa_error FFA_INVALID_PARAMETERS, init_FFA_memory_region_struct, 0, false,
                    FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)
      | Some region_descriptor =>
        (* Check whether we have a proper free memory *) 
        if decide ((st.(hafnium_context).(api_page_pool_size) < FFA_memory_region_struct_size)%Z)
        then Ret (ffa_error FFA_NO_MEMORY, init_FFA_memory_region_struct, 0, false,
                  FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)
        else
          if decide (region_descriptor.(FFA_memory_region_struct_sender) <> current_vm_id) ||
             decide ((length region_descriptor.(FFA_memory_region_struct_receivers) <> 1%nat))
          then Ret (ffa_error FFA_INVALID_PARAMETERS, init_FFA_memory_region_struct, 0, false,
                    FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)                    
          else
            do receiver <-  get_receiver (region_descriptor.(FFA_memory_region_struct_receivers)) ;;;
            let receiver_id := receiver.(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor).(FFA_memory_access_permissions_descriptor_struct_receiver) in
            if in_dec zeq receiver_id vm_ids || decide (current_vm_id <> receiver_id)
            then
              (* check clear flags *)
              let clear_flag := if decide ((Z.land region_descriptor.(FFA_memory_region_struct_flags)
                                                                       FFA_MEMORY_REGION_FLAG_CLEAR_Z) <> 0)
                                then true else false in
              let other_flags := if decide ((Z.land region_descriptor.(FFA_memory_region_struct_flags)
                                                                       (Z_not FFA_MEMORY_REGION_FLAG_CLEAR_Z)) <> 0)
                                then true else false in
              match func_type, clear_flag, other_flags with
              | FFA_MEM_SHARE, true, _ 
              | _, _, true =>
                Ret (ffa_error FFA_INVALID_PARAMETERS, init_FFA_memory_region_struct, 0, false,
                     FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)
              | _, _, _ =>
                (* check instruction permissions *)
                let permissions :=
                    receiver.(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor) in
                let instruction_permissions :=
                    permissions.(FFA_memory_access_permissions_descriptor_struct_permisions_instruction) in
                let data_permissions :=
                    permissions.(FFA_memory_access_permissions_descriptor_struct_permisions_data) in
                match func_type, instruction_permissions, data_permissions with
                (* valid case 
                   - TODO(XXX): It is not actually correct... we need to update the instruction_access 
                   in region_descriptor as FFA_INSTRUCTION_ACCESS_NX *)
                |  FFA_MEM_SHARE,  FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED
                   => Ret (init_FFA_value_type, region_descriptor, receiver_id, clear_flag,
                          FFA_INSTRUCTION_ACCESS_NX, data_permissions)

                |  FFA_MEM_LEND, _, FFA_DATA_ACCESS_NOT_SPECIFIED
                |  FFA_MEM_DONATE, _, FFA_DATA_ACCESS_NOT_SPECIFIED
                   => Ret (ffa_error FFA_INVALID_PARAMETERS, init_FFA_memory_region_struct, 0, false,
                          FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)

                (* valid case *)
                |  FFA_MEM_DONATE, FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, _
                   => Ret (init_FFA_value_type, region_descriptor, receiver_id, clear_flag,
                          instruction_permissions, data_permissions)
                (* valid case *)
                |  FFA_MEM_LEND, FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, _
                   => Ret (init_FFA_value_type, region_descriptor, receiver_id, clear_flag,
                          instruction_permissions, data_permissions)
                | _, _, _ 
                  => Ret (ffa_error FFA_INVALID_PARAMETERS, init_FFA_memory_region_struct, 0, false,
                         FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)
                end
              end
            else Ret (ffa_error FFA_INVALID_PARAMETERS, init_FFA_memory_region_struct, 0, false,
                      FFA_INSTRUCTION_ACCESS_NOT_SPECIFIED, FFA_DATA_ACCESS_NOT_SPECIFIED)
      end.

    (* update memory properties for all addresses in the region descriptor *)             
    Fixpoint update_memory_properties_in_constituent_iter (page_count : nat) (base_address: Z) (attributes: MemProperties)
             (state : AbstractState) : AbstractState :=
      match page_count with
      | O => state {hafnium_context / mem_properties:
                     ZTree.set base_address attributes state.(hafnium_context).(mem_properties)}
      | S n' =>
        let state' := update_memory_properties_in_constituent_iter n' base_address attributes state in
        state' {hafnium_context / mem_properties:
                  ZTree.set ((base_address + (Z.of_nat (S n')) * FFA_PAGE_SIZE)%Z)
                            attributes state.(hafnium_context).(mem_properties)}
      end.
                               
                     
    Definition update_memory_properties_in_constituent (constituent_info: FFA_memory_region_constituent_struct)
               (properties: MemProperties) (state : AbstractState) : AbstractState :=
      match constituent_info with
      | mkFFA_memory_region_constituent_struct base_address page_count
        => update_memory_properties_in_constituent_iter page_count base_address properties state
      end.

    Fixpoint update_memory_properties_in_composite_iter (constituents: list FFA_memory_region_constituent_struct)
               (properties: MemProperties) (state : AbstractState) : AbstractState :=
      match constituents with
      | nil => state
      | hd::tl =>
        let state' := update_memory_properties_in_composite_iter tl properties state in
        update_memory_properties_in_constituent hd properties state'
      end.
        
    Definition update_memory_properties_in_composite (composite_info: FFA_composite_memory_region_struct)
               (properties: MemProperties) (state : AbstractState) : AbstractState :=
      match composite_info with
      | mkFFA_composite_memory_region_struct page_count constituents =>
        update_memory_properties_in_composite_iter constituents properties state
      end.


    Definition find_first_constituent (constituents: list FFA_memory_region_constituent_struct) :=
      match constituents with
      | nil => None
      | hd::tl => Some hd
      end.
    
    (* TODO(XXX): need to modify them *)
    Definition ffa_mem_send_change_mem_spec
               (func_type : FFA_FUNCTION_TYPE)               
               (region_descriptor: FFA_memory_region_struct)
               (receiver_id : ffa_vm_id_t)
               (clear_flag: bool)
               (instruction_access_type: FFA_INSTRUCTION_ACCESS_TYPE)
               (data_access_type: FFA_DATA_ACCESS_TYPE)
      : itree HafniumEE (Z) :=
      (* get the mode of the base address *)
      do receiver <- get_receiver region_descriptor.(FFA_memory_region_struct_receivers) ;;;
      (* TODO(XXX): need to see the consistency of all addresses by checking all properties of all 
         areas *)
      do composite <- receiver.(FFA_memory_access_descriptor_struct_composite_memory_region_offset) ;;;
      do first_constituent <- find_first_constituent 
                               composite.(FFA_composite_memory_region_struct_constituents) ;;;
      let base_address := first_constituent.(FFA_memory_region_constituent_struct_address) in 
      st <- trigger GetState;;
      (* find out the new mode *)      
      do mem_property <- ZTree.get base_address st.(hafnium_context).(mem_properties) ;;;
      match mem_property.(accessible_by) with 
      | ExclusiveAccess owner =>
        let new_mem_property := 
            mkMemProperties (mem_property.(owned_by)) (SharedAccess (owner::receiver_id::nil))
                            (instruction_access_type) (data_access_type) (mem_property.(mem_attribute))
                            (if clear_flag then MemClean else mem_property.(mem_dirty)) in
        (* update the memory state *)
        let updated_st := update_memory_properties_in_composite composite new_mem_property st in
        (* update the share state *)
        let new_ffa_memory_share_state :=
            mkFFA_memory_share_state_struct region_descriptor func_type                                 
                                            (ZMap.set 0 (* first receiver *) false (ZMap.init true)) in
        let cur_share_state_index := (updated_st.(hafnium_context).(fresh_index_for_ffa_share_state)) in 
        let updated_st' :=
            updated_st {hafnium_context / ffa_share_state :
                          ZTree.set cur_share_state_index new_ffa_memory_share_state
                                    (updated_st.(hafnium_context).(ffa_share_state))}
                       {hafnium_context / fresh_index_for_ffa_share_state :
                          (cur_share_state_index + 1)%Z} in
        trigger (SetState updated_st');;
        Ret (Z.lor cur_share_state_index FFA_MEMORY_HANDLE_ALLOCATOR_HYPERVISOR_Z)
      | _ => triggerUB "wrong access"
      end.
      
    Definition ffa_mem_send_deliver_msg_to_receivers (reciever_id handle : Z) 
      : itree HafniumEE (unit) :=
      st <- trigger GetState;;
      (* record the message *)
      (* TODO(XXX): need to modify the following parts to 
         properly create a message and update the mailbox for retrieve *)
      trigger (SetState st);;
      triggerUB "ffa_mem_send_change_memory_attributes_spec: Not implemented yet".
    
    (* Note that we ignored next pointer in our modeling because it is not quite necessary.
       - TODO: figure out the functionality of the "update_vi" function call in "hvc_handler" 
         
    struct ffa_value api_ffa_mem_send(uint32_t share_func, uint32_t length,
            			  uint32_t fragment_length, ipaddr_t address,
            			  uint32_t page_count, struct vcpu *current,
            			  struct vcpu **next)
     *)
    Definition api_ffa_mem_send_spec (func_type:  FFA_FUNCTION_TYPE)
               (length fragment_length address page_count current_vm_id : Z)
      : itree HafniumEE (FFA_value_type) :=
      argument_check_res <- ffa_mem_send_check_arguments_spec func_type length
                                                             fragment_length address page_count ;;
      match argument_check_res.(ffa_type) with
      | FFA_RESULT_CODE_IDENTIFIER FFA_ERROR => Ret (argument_check_res)
      | _ =>
        check_result <- ffa_mem_send_check_memory_region_descriptor_spec func_type current_vm_id ;;
        let '(descriptor_check_res, region_descriptor, receiver_id, clear_flag,
              instruction_access_permissions, data_access_permissions) := check_result in
        match descriptor_check_res.(ffa_type) with 
        |  FFA_RESULT_CODE_IDENTIFIER FFA_ERROR => Ret (descriptor_check_res)
        | _ =>
          handle <- ffa_mem_send_change_mem_spec
                         func_type region_descriptor receiver_id clear_flag
                         instruction_access_permissions data_access_permissions ;;          
          ffa_mem_send_deliver_msg_to_receivers receiver_id handle;;
          Ret (ffa_mem_success handle)
        end
      end.
    
  End FFAMemoryHypCallSend.

  Section FFAMemoryHypCallRetrieve.
  (*
    struct ffa_value api_ffa_mem_retrieve_req(uint32_t length,
           				  uint32_t fragment_length,
           				  ipaddr_t address, uint32_t page_count,
           				  struct vcpu *current)    
   *)
    Definition api_ffa_mem_retrieve_req (length fragment_length address page_count current_vm_id : Z)
      : itree HafniumEE (FFA_value_type) := 
      triggerUB "api_ffa_mem_retrieve_req: Not implemented yet".

  End FFAMemoryHypCallRetrieve.


  Section FFAMemoryHypCallRelinquish.
    (*
    struct ffa_value api_ffa_mem_relinquish(struct vcpu *current)                              
    *) 
    Definition api_ffa_mem_relinquish_spec (current_vm_id : Z)
    : itree HafniumEE (FFA_value_type) :=
      triggerUB "api_ffa_mem_retrieve_req: Not implemented yet".
    
  End FFAMemoryHypCallRelinquish.

  Section FFAMemoryHypCallReclaim.
    (*
    struct ffa_value api_ffa_mem_reclaim(ffa_memory_handle_t handle,
            			     ffa_memory_region_flags_t flags,
            			     struct vcpu *current)    
    *)
    Definition api_ffa_mem_reclaim_spec (handle flags current_vm_id : Z)
    : itree HafniumEE (FFA_value_type) :=
      triggerUB "api_ffa_mem_retrieve_req: Not implemented yet".

  End FFAMemoryHypCallReclaim.

  Section FFADispatch.
  
    Definition ffa_dispatch_spec :  itree HafniumEE (unit) := 
      (* extract the curretnt vcpu *)
      st <- trigger GetState;;
      (* Get the information in tpidr_el2 register to find out the current VM to be served *)
      let vcpu_regs := st.(hafnium_context).(tpidr_el2) in
      match vcpu_regs with
      | Some vcpu_regs' =>
        match vcpu_regs' with
        | mkVCPU_struct (Some cid) (Some vid) vcpu_regs =>
          match vcpu_regs with
          | mkArchRegs (mkFFA_value_type func_type vals) =>
            match func_type with
            | FFA_FUNCTION_IDENTIFIER ffa_function_type =>
              (* Find out the result of the FFA ABI calls by using the proper handling functions *)
              ret_ffa_value <- 
              match ffa_function_type with
              | FFA_MEM_DONATE 
              | FFA_MEM_LEND 
              | FFA_MEM_SHARE
                (* For the above three FFA ABI, call the following functions, and update 
                   the VCPU value for the caller to record the result *)
                (* 
		*args = api_ffa_mem_send(func, args->arg1, args->arg2,
					 ipa_init(args->arg3), args->arg4,
					 current(), next);
                 *)
                => api_ffa_mem_send_spec ffa_function_type (ZMap.get 1 vals) (ZMap.get 2 vals)
                                        (ZMap.get 3 vals) (ZMap.get 4 vals) vid
              | FFA_MEM_RETREIVE_REQ
                (*
		*args = api_ffa_mem_retrieve_req(args->arg1, args->arg2,
						 ipa_init(args->arg3),
						 args->arg4, current());
                 *)
                => api_ffa_mem_retrieve_req (ZMap.get 1 vals) (ZMap.get 2 vals) (ZMap.get 3 vals)
                                           (ZMap.get 4 vals) vid
              | FFA_MEM_RELINQUISH
                (*
		*args = api_ffa_mem_relinquish(current());
                *)
                => api_ffa_mem_relinquish_spec vid
              | FFA_MEM_RECLAIM
                (*
		*args = api_ffa_mem_reclaim(
			ffa_assemble_handle(args->arg1, args->arg2), args->arg3,
			current());                  
                *)
                => api_ffa_mem_reclaim_spec (Z.lor (ZMap.get 1 vals) (Z.shiftl (ZMap.get 2 vals) 32))
                                           (ZMap.get 3 vals) vid
              | FFA_MEM_RETREIVE_RESP
                => triggerUB "ffa_dispatch_spec: not a proper FFA ABI function name 
                  to be called in this level"                            
              end;;
              (* get the updated state after the handling *)
              updated_st <- trigger GetState;;
              do vm_context <- ZTree.get vid updated_st.(hafnium_context).(vms_contexts);;;
              do vcpu_reg <- ZTree.get vm_context.(cur_vcpu_index) vm_context.(vcpus);;;
              let new_vcpu_reg := mkVCPU_struct (vcpu_reg.(cpu_id)) (vcpu_reg.(vm_id))
                                                (mkArchRegs ret_ffa_value) in
              let new_vm_context := 
                  vm_context {vm_vcpus: ZTree.set (vm_context.(cur_vcpu_index))
                                                  new_vcpu_reg 
                                                  vm_context.(vcpus)} in
              let new_st := updated_st {hafnium_context / vms_contexts:
                                  ZTree.set vid new_vm_context
                                            (updated_st.(hafnium_context).(vms_contexts))} in
              trigger (SetState new_st)
            | _ => triggerUB "ffa_dispatch_spec: impossible case happens"
            end
          end
        | _ => triggerUB "ffa_dispatch_spec: impossible case happens"
        end
    | None => triggerUB "ffa_dispatch_spec: impossible case happens" 
    end.
                        
    Definition ffa_dispatch_call (args : list Lang.val) :=
      match args with
      | nil => ffa_dispatch_spec
      | _ => triggerUB "ffa_dispatch_call: wrong arguments"
      end.
  
  End FFADispatch.
  
*)
