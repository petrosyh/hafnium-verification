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
Require Import FFAMemoryHypCall.
Require Import FFAMemoryHypCallIntro.
Require Export FFAMemoryHypCallDescriptorState.
Require Export FFAMemoryHypCallState.

(*************************************************************)
(** *             Core Step Rules                            *)
(*************************************************************)
(** This file defines the core step rules of FFA memory management 
    interfaces *)
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

(** Three roles in the FFA_XXX communications, and endpoints in the communications 

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
(** **            Valid Combinations                         *)
(*************************************************************)
Section VALID_COMBINATIONS.

  Context `{ffa_types_and_constants : FFA_TYPES_AND_CONSTANTS}.
  
  (** This part is one of the most important parts that describe ownership and accessibility options. 
       It is similar to "valid" check in the abstract model by Jade 
  
      Related parts: 
      - Table 5.3: Valid combinations of ownership and access states     
      - Table 5.4: Valid combinations of ownership and access states between two components

     - Component A state / Component B state / Descriptions
     - Owner-EA / !Owner-NA / Component A has exclusive access and ownership of 
       a memory region that is inaccessible from component B.
     - Owner-NA / !Owner-NA / Component A has granted exclusive access to a memory region it owns to another component. 
       It is inaccessible from component B.
     - Owner-NA / !Owner-EA / Component A has granted exclusive access to a memory region it owns to component B.
     - Owner-NA / !Owner-SA / Component A has relinquished access to a memory 
       region it owns. Access to the memory region is shared between component B and at least one other component
     - Owner-SA / !Owner-NA / Component A shares access to a region of memory it owns 
       with another component. Component B cannot access the memory region.
     - Owner-SA / !Owner-SA / Component A shares access to a region of memory it
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
         (* at least one component has ownerhsip *)
         | _, _ => false
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
       - And, it checks validity of descriptors and the current memory properties 
       - seciton 5.10, 5.11, 5.12 provide multiple constraints about descriptor information.
    3. Check validity of arguments and other related states except descriptor values
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
       - Owner-NA for the Owner.
       - !Owner-NA for the Receiver.
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
      do global_property <- ZTree.get address st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
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
                                                      st.(hypervisor_context).(mem_properties).(mem_global_properties) in
               let new_st := st {hypervisor_context / mem_properties :
                                   mkMemProperties new_global_properties
                                                   st.(hypervisor_context).(mem_properties).(mem_local_properties)} in
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
       - Owner-NA for the Owner.
       - !Owner-NA for the Receiver.
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
      do global_property <- ZTree.get address st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
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
                                                      st.(hypervisor_context).(mem_properties).(mem_global_properties) in
               let new_st := st {hypervisor_context / mem_properties :
                                   mkMemProperties new_global_properties
                                                   st.(hypervisor_context).(mem_properties).(mem_local_properties)} in
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
      do global_property <- ZTree.get address st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
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
                                                      st.(hypervisor_context).(mem_properties).(mem_global_properties) in
               let new_st := st {hypervisor_context / mem_properties :
                                   mkMemProperties new_global_properties
                                                   st.(hypervisor_context).(mem_properties).(mem_local_properties)} in
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
      do global_property <- ZTree.get address st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
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
                                                      st.(hypervisor_context).(mem_properties).(mem_global_properties) in
               (** Remove the corresponding map in the lender memory local properties pool *)
               let new_lender_properties_pool := ZTree.remove address lender_properties_pool in
               (** Create the new  memory local properties pool for the borrower.
                Instead of making a new initial state, we copied the previous local properties that lender had. 
                Next opeartions can adjust the properties if it is necessary *)
               let new_borrower_properties_pool := ZTree.set address (gen_own_mem_local_properties_wrapper lender_property) 
                                                             borrower_properties_pool in
               let new_local_properties_global_pool' := ZTree.set lender new_lender_properties_pool
                                                                  st.(hypervisor_context).(mem_properties).(mem_local_properties) in
               let new_local_properties_global_pool := ZTree.set borrower new_borrower_properties_pool
                                                                 new_local_properties_global_pool' in
               let new_st := st {hypervisor_context / mem_properties :
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
      do global_property <- ZTree.get address st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
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
                                                      st.(hypervisor_context).(mem_properties).(mem_global_properties) in
               (** Create the new memory local properties pool for the borrower.
                Instead of making a new initial state, we copied the previous local properties that lender had. 
                Next opeartions can adjust the properties if it is necessary *)
               let new_borrower_properties_pool := ZTree.set address (gen_borrow_mem_local_properties_wrapper lender lender_property) 
                                                             borrower_properties_pool in
               let new_local_properties_global_pool := ZTree.set borrower new_borrower_properties_pool
                                                                 st.(hypervisor_context).(mem_properties).(mem_local_properties) in
               let new_st := st {hypervisor_context / mem_properties :
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
      do global_property <- ZTree.get address st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
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
                                                      st.(hypervisor_context).(mem_properties).(mem_global_properties) in
               (** Create the new  memory local properties pool for the borrower.
                Instead of making a new initial state, we copied the previous local properties that lender had. 
                Next opeartions can adjust the properties if it is necessary *)
               let new_borrower_properties_pool := ZTree.set address (gen_borrow_mem_local_properties_wrapper lender lender_property) 
                                                             borrower_properties_pool in
               let new_local_properties_global_pool := ZTree.set borrower new_borrower_properties_pool
                                                                 st.(hypervisor_context).(mem_properties).(mem_local_properties) in
               let new_st := st {hypervisor_context / mem_properties :
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
      do global_property <- ZTree.get address st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <- ZTree.get lender st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <- ZTree.get borrower st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
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
                                                      st.(hypervisor_context).(mem_properties).(mem_global_properties) in
               (** Create the new  memory local properties pool for the borrower.
                Instead of making a new initial state, we copied the previous local properties that lender had. 
                Next opeartions can adjust the properties if it is necessary *)               
               let new_borrower_properties_pool := ZTree.remove address borrower_properties_pool in
               let new_local_properties_global_pool := ZTree.set borrower new_borrower_properties_pool
                                                                 st.(hypervisor_context).(mem_properties).(mem_local_properties) in
               let new_st := st {hypervisor_context / mem_properties :
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
    Definition ffa_mem_donate_additional_transition_spec
      (lender borrower : ffa_UUID_t) (address: Z) (clean: bool) : itree HafniumEE (unit) :=
      ffa_mem_donate_core_transition_spec lender borrower address clean.

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
    : itree HafniumEE (FFA_IDENTIFIER_TYPE) :=
    match func_type with
    | FFA_MEM_DONATE 
    | FFA_MEM_LEND 
    | FFA_MEM_SHARE =>
      if decide (address = 0) || decide (page_count = 0) ||
                decide (length <> fragment_length) 
      (* ||
                decide (length >  HF_MAILBOX_SIZE)  ||
                decide (length >  MM_PPOOL_ENTRY_SIZE) *)
      then Ret (FFA_RESULT_CODE_IDENTIFIER (FFA_ERROR FFA_INVALID_PARAMETERS))
      else Ret (FFA_IDENTIFIER_DEFAULT)
    (* This case cannot happen if we look at the calling sequence of this spec *)
    | _ => triggerUB "ffa_mem_send_check_arguments: wrong arguments"
    end.

  Section FFA_MEM_DONATE_ARGUMENT_CHECKS.

    (** 11.1 FFA_MEM_DONATE *)
    Definition ffa_mem_donate_spec
               (lender borrower : ffa_UUID_t) (address: Z) (clean: bool) : itree HafniumEE (unit) :=
      ffa_mem_donate_additional_transition_spec lender borrower address clean.
    
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
