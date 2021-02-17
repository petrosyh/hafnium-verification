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
  
 
Notation "'do' X <- A ;;; B" :=
  (match A with Some X => B |
           None => triggerUB "None" end)
    (at level 200, X ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation "'do' X , Y <- A ;;; B" :=
  (match A with Some (X, Y) => B |
           None => triggerUB "None" end)
    (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation "'do' X , Y , Z <- A ;;; B" :=
  (match A with Some (X, Y, Z) => B | None => triggerUB "None" end)
    (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : itree_monad_scope.
 
Notation " 'check' A ;;; B" :=
  (if A then B else Ret None)
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
             (a b : ffa_UUID_t) (ownership: OWNERSHIP_STATE_TYPE)
             (access: ACCESS_STATE_TYPE) :=
    if decide (a <> b) 
    then match ownership, access with
         | Owned id, NoAccess =>
           if decide (a = id) || decide (b = id)
           then true else false                                  
         | Owned id, ExclusiveAccess id' =>
           if decide (a = id) || decide (b = id)
           then if decide (a = id') || decide (b = id')
                then true else false
           else false
         | Owned id, SharedAccess ids =>
           if decide (a = id) || decide (b = id)
           then if (in_dec zeq a ids) || (in_dec zeq b ids)
                then true else false
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
    - Core memory changes including ownership, access state, dirty bit in memory global properties and 
      local ownership flag in memory local properties. 
      - It only handles memory ownership, access, and dirty bit changes during transitions 
      - Instead of interpreting all descriptor values, it will pass the flag value as an argument to indicate 
        whether the memory region needs to be cleaned.
    - Additional memory attributes and properties change and check validity by using descriptors and arguments
      - And, it checks validity of descriptors and the current memory properties 
      - seciton 5.10, 5.11, 5.12 provide multiple constraints about descriptor information.
      - There are multiple constraints that section 11.x mentions for each interface. 
 *)

(** For the top-level modeling, we also provide specifications for dispatching. It reads the value from the current
    registers (abstract registers specified for FFA memory management specifications), and call proper specifications
    to trigger transitions. 

    To do that, we referred Hafinum's dispatch code (but we did not strictly follow the code).
*)
    

(*************************************************************)
(** **  1. Core memory ownership and access state change     *)
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
  Notation HypervisorEE :=
    (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).

  Section FFA_MEM_DONATE_CORE_STEPS.    

    (** TODO:
        Note that the following parts are for the case when the borrower is a PE endpoint. 
        When the borrower is a SEPID associated with an independent peripheral device, there are more freedoms for
        developers to implement those memory management interfaces. We need to consider how to capture 
        them in our specs without missing generality *) 
    
    (*************************************************************)
    (** ***           FFA_MEM_DONATE                             *)
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
       - The Owner uses the FFA_MEM_DONATE interface to describe the memory region and convey the
          identity of the Receiver to the Relayer as specified in Table 5.19. This interface is described in 11.1
          FFA_MEM_DONATE.
       - If the Receiver is a PE endpoint or a SEPID associated with a dependent peripheral device,
          - The Owner uses a Partition message to request the Receiver to retrieve the donated memory region. This
             message contains a description of the memory region relevant to the Receiver.
          - The Receiver uses the FFA_MEM_RETRIEVE_REQ and FFA_MEM_RETRIEVE_RESP interfaces to
            map the memory region in its translation regime and complete the transaction. These interfaces are
            described in 11.4 FFA_MEM_RETRIEVE_REQ & 11.5 FFA_MEM_RETRIEVE_RESP respectively.
         In case of an error, the Sender can abort the transaction before the Receiver retrieves the memory region
         by calling the FFA_MEM_RECLAIM ABI (see 11.7 FFA_MEM_RECLAIM).
       - If the Receiver is a SEPID associated with an independent peripheral device, an IMPLEMENTATION DEFINED
         mechanism is used by the Sender and Relayer to map and describe the memory region to the Receiver (see
         11.1.1 Component responsibilities for FFA_MEM_DONATE).
     *)
    
    Definition ffa_mem_donate_core_transition_spec
               (lender borrower : ffa_UUID_t) (address: Z)
    : itree HypervisorEE (bool) :=
      st <- trigger GetState ;;
      (** - Find out memory properties *) 
      do global_property <-
         ZTree.get
           address
           st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <-
         ZTree.get
           lender
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <-
         ZTree.get
           borrower
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <- ZTree.get address lender_properties_pool ;;;
      (** - check memory properties :
            - lender has to have onwership
            - lender has to have exclusive access to the address
            - borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property,
            ZTree.get address borrower_properties_pool  with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None =>
        (** - Check the valid onwership and accessibility combination for lender and borrower *)
        match mem_states_valid_combination lender borrower owned accessible,
              owned, accessible, local_owned with
        | true, Owned owner, ExclusiveAccess ex_accessor, LocalOwned =>
          if decide (owner = lender) && decide (ex_accessor = lender)
          then
            (** - Only change accessibility option of the lender. The remaining operations will
                be performed in the retrieve *)
            let new_global_properties :=
                ZTree.set
                  address (global_property {accessible_by: NoAccess}
                                           {mem_dirty : dirty})
                  st.(hypervisor_context).(mem_properties).(mem_global_properties) in
            let new_st :=
                st {hypervisor_context / mem_properties :
                      mkMemProperties
                        new_global_properties
                        st.(hypervisor_context).(mem_properties).(mem_local_properties)} in
            trigger (SetState new_st);;
            Ret (true)
          else Ret (false)
        | _, _, _, _ => Ret (false)
        end
      | _, _, _ => Ret (false)
      end.
         
  End FFA_MEM_DONATE_CORE_STEPS.

  Section FFA_MEM_LEND_CORE_STEPS.

    (*************************************************************)
    (** ***           FFA_MEM_LEND                               *)
    (*************************************************************)    
    
    (** Related parts
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
       - The Lender uses the FFA_MEM_LEND interface to describe the memory region and convey the identities of
         the Borrowers to the Relayer as specified in Table 5.19. This interface is described in 11.2 FFA_MEM_LEND.
       - If a Borrower is a PE endpoint or a SEPID associated with a dependent peripheral device,
          - The Lender uses a Partition message to request each Borrower to retrieve the lent memory region. This
            message contains a description of the memory region relevant to the Borrower.
          - Each Borrower uses the FFA_MEM_RETRIEVE_REQ and FFA_MEM_RETRIEVE_RESP interfaces
            to map the memory region in its translation regime and complete the transaction. These interfaces are
            described in 11.4 FFA_MEM_RETRIEVE_REQ & 11.5 FFA_MEM_RETRIEVE_RESP respectively.
       - If the Borrower is a SEPID associated with an independent peripheral device, an IMPLEMENTATION DEFINED
         mechanism is used by the Lender and Relayer to map and describe the memory region to the Borrower (see
         11.2.1 Component responsibilities for FFA_MEM_LEND).
       - In case of an error, the Lender can abort the transaction before the Borrower retrieves the memory region by
         calling the FFA_MEM_RECLAIM ABI (see 11.7 FFA_MEM_RECLAIM).
     *)

    Definition ffa_mem_lend_core_transition_spec
               (lender borrower : ffa_UUID_t) (borrower_num : Z)
               (address: Z)
    : itree HypervisorEE (bool) :=
      st <- trigger GetState ;;
      (** - Find out memory properties *) 
      do global_property <-
         ZTree.get
           address
           st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <-
         ZTree.get
           lender
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <-
         ZTree.get
           borrower
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <- ZTree.get address lender_properties_pool ;;;
      (** - check memory properties :
            - lender has to have onwership
            - lender has to have exclusive access to the address
            - borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property,
            ZTree.get address borrower_properties_pool,
            decide (borrower_num >= 1) with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None, left _ =>
        (** - Check the valid onwership and accessibility combination for lender and borrower *)        
        match mem_states_valid_combination lender borrower owned accessible,
              owned, accessible, local_owned with
        | true, Owned owner, ExclusiveAccess ex_accessor, LocalOwned =>
          if decide (owner = lender) && decide (ex_accessor = lender)
          then (** Only change accessibility option of the lender. The remaining operations will
                   be performed in the retrieve *)                 
               let new_global_properties :=
                   ZTree.set
                     address (global_property {accessible_by: NoAccess}
                                              {mem_dirty : dirty})
                     st.(hypervisor_context).(mem_properties).(mem_global_properties) in
               let new_st :=
                   st {hypervisor_context / mem_properties :
                         mkMemProperties
                           new_global_properties
                           st.(hypervisor_context).(mem_properties).(mem_local_properties)} in
               trigger (SetState new_st);;
               Ret (true)
          else Ret (false)
        | _, _, _, _ => Ret (false)
        end
      | _, _, _, _ => Ret (false)
      end.
    
  End FFA_MEM_LEND_CORE_STEPS.
    
  Section FFA_MEM_SHARE_CORE_STEPS.

    (*************************************************************)
    (** ***           FFA_MEM_SHARE                              *)
    (*************************************************************)    

    (** Related parts
     - 11.3.1.2 Relayer responsibilities
       There are two cases, but we only consider the case mentioned in 12.1.1, 
       the case when a Borrower is a PE endpoint.
       - Owner-SA for the Owner.
       - !Owner-NA for the Receiver.
     - Note that it differs from the well-defined transition in
       Table 5.11: Share memory transaction state machine.
       This is due to the fact that the transition defined in "Table 5.11" is actually 
       divided into two parts, FFA_MEM_SHARE and FFA_MEM_RETRIEVE_REQ 

       But, the possible initial state of two endpoints are defined in Table 5.10:
       Owner-EA !Owner-NA

       In here, we describe simple lifcycles mentioned in "5.8.2 Share memory transaction lifecycle". 
       We discuss rules defined in section 11.3 in the below (the next section in this file).

       This transaction takes place as follows (also see 5.5.2 Transaction life cycle).
       - The Lender uses the FFA_MEM_SHARE interface to describe the memory region and convey the identities of
         the Borrowers to the Relayer as specified in Table 5.19. This interface is described in 11.2 FFA_MEM_LEND.
       - If a Borrower is a PE endpoint or a SEPID associated with a dependent peripheral device,
         - The Lender uses a Partition message to request each Borrower to retrieve the shared memory region.
           This message contains a description of the memory region relevant to the Borrower.
         - Each Borrower uses the FFA_MEM_RETRIEVE_REQ and FFA_MEM_RETRIEVE_RESP interfaces
           to map the memory region in its translation regime and complete the transaction. These interfaces are
           described in 11.4 FFA_MEM_RETRIEVE_REQ & 11.5 FFA_MEM_RETRIEVE_RESP respectively.
       - If the Borrower is a SEPID associated with an independent peripheral device, an IMPLEMENTATION DEFINED
         mechanism is used by the Lender and Relayer to map and describe the memory region to the Borrower (see
         11.3.1 Component responsibilities for FFA_MEM_SHARE).
       - In case of an error, the Lender can abort the transaction before the Borrower retrieves the memory region by
         calling the FFA_MEM_RECLAIM ABI (see 11.7 FFA_MEM_RECLAIM).
     *)
    Definition ffa_mem_share_core_transition_spec
               (lender borrower : ffa_UUID_t) (address: Z)
    : itree HypervisorEE (bool) :=
      st <- trigger GetState ;;
      (** - Find out memory properties *) 
      do global_property <-
         ZTree.get
           address
           st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <-
         ZTree.get
           lender
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <-
         ZTree.get
           borrower
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <-
         ZTree.get address lender_properties_pool ;;;
      (** - check memory properties :
            - lender has to have onwership
            - lender has to have exclusive access to the address
            - borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property,
            ZTree.get address borrower_properties_pool with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None =>
        (** Check the valid onwership and accessibility combination for lender and borrower *)        
        match mem_states_valid_combination lender borrower owned accessible,
              owned, accessible, local_owned with
        | true, Owned owner, ExclusiveAccess ex_accessor, LocalOwned =>
          if decide (owner = lender) && decide (ex_accessor = lender)
          then (** Only change accessibility option of the lender. The remaining operations will
                   be performed in the retrieve *)                 
            let new_global_properties :=
                ZTree.set
                  address
                  (global_property
                     {accessible_by: SharedAccess (lender::nil)}
                     {mem_dirty : dirty})
                  st.(hypervisor_context).(mem_properties).(mem_global_properties) in
            let new_st :=
                st {hypervisor_context / mem_properties :
                      mkMemProperties new_global_properties
                                      st.(hypervisor_context).(mem_properties).(mem_local_properties)} in
            trigger (SetState new_st);;
            Ret (true)
          else Ret (false)
        | _, _, _, _ => Ret (false)
        end
      | _, _, _ => Ret (false)
      end.

  End FFA_MEM_SHARE_CORE_STEPS.

  Section FFA_MEM_RETRIEVE_REQ_CORE_STEP.

    (*************************************************************)
    (** ***        FFA_MEM_RETRIEVE_REQ                          *)
    (*************************************************************)    
    
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
         - Table 5.9: Donate memory transaction state machine.
         - Table 5.10: Lend memory transaction state machine.
         - Table 5.11: Share memory transaction state machine.

       We discuss rules defined in section 11.4 in the below (the next section in this file).
     *)
    
    (*************************************************************)
    (** ****       FFA_MEM_DONATE_RETRIEVE_REQ                   *)
    (*************************************************************)    

    Definition ffa_mem_donate_retrieve_req_core_transition_spec
               (lender borrower : ffa_UUID_t) (address: Z) (clean: bool)
    : itree HypervisorEE (bool) :=
      st <- trigger GetState ;;
      (** - Find out memory properties *) 
      do global_property <-
         ZTree.get
           address
           st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <-
         ZTree.get
           lender
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <-
         ZTree.get
           borrower
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <- ZTree.get address lender_properties_pool ;;;
      (** - check memory properties :
            - lender has to have onwership
            - lender has to have exclusive access to the address
            - borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property,
            ZTree.get address borrower_properties_pool  with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None =>
        (** - Check the valid onwership and accessibility combination for lender and borrower *)
        match mem_states_valid_combination lender borrower owned accessible,
              owned, accessible, local_owned with
        | true, Owned owner, NoAccess, LocalOwned =>
          if decide (owner = lender)
          then let new_dirty := if clean then MemClean else dirty in
               (** - Only change accessibility option of the lender. The remaining operations will
                     be performed in the retrieve *)
               let new_global_properties :=
                   ZTree.set
                     address
                     (global_property
                        {owned_by: Owned borrower}
                        {accessible_by: ExclusiveAccess borrower}
                        {mem_dirty : new_dirty})
                     st.(hypervisor_context).(mem_properties).(mem_global_properties) in
               (** - Remove the corresponding map in the lender memory local properties pool *)
               let new_lender_properties_pool :=
                   ZTree.remove address lender_properties_pool in
               (** - Create the new  memory local properties pool for the borrower.
                     Instead of making a new initial state, we copied the previous local properties that lender had. 
                     Next opeartions can adjust the properties if it is necessary *)
               let new_borrower_properties_pool :=
                   ZTree.set
                     address
                     (gen_own_mem_local_properties_wrapper lender_property) 
                     borrower_properties_pool in
               let new_local_properties_global_pool' :=
                   ZTree.set
                     lender new_lender_properties_pool
                     st.(hypervisor_context).(mem_properties).(mem_local_properties) in
               let new_local_properties_global_pool :=
                   ZTree.set
                     borrower
                     new_borrower_properties_pool
                     new_local_properties_global_pool' in
               let new_st :=
                   st {hypervisor_context / mem_properties :
                         mkMemProperties
                           new_global_properties
                           new_local_properties_global_pool} in
               trigger (SetState new_st);;
               Ret (true)
          else Ret (false)
        | _, _, _, _ => Ret (false)
        end
      | _, _, _ => Ret (false)
      end.

    (*************************************************************)
    (** ****         FFA_MEM_LEND_RETRIEVE_REQ                   *)
    (*************************************************************)    

    Definition add_accessor
               (borrower : ffa_UUID_t) (borrower_num : Z)
               (access_state : ACCESS_STATE_TYPE) :=
      match access_state, decide (borrower_num > 1) with 
      | NoAccess, left _ =>
        Some (SharedAccess (borrower::nil))
      | NoAccess, right _ =>
        Some (ExclusiveAccess borrower)
      | SharedAccess borrowers, left _ =>
        Some (SharedAccess (borrower::borrowers))
      | _, _ => None
      end.
    
    Definition ffa_mem_lend_retrieve_req_core_transition_spec
               (lender borrower : ffa_UUID_t) (borrower_num : Z)
               (address: Z) (clean: bool)
    : itree HypervisorEE (bool) :=
      st <- trigger GetState ;;
      (** - Find out memory properties *) 
      do global_property <-
         ZTree.get
           address
           st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <-
         ZTree.get
           lender
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <-
         ZTree.get
           borrower
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <- ZTree.get address lender_properties_pool ;;;
      (** - check memory properties :
            - lender has to have onwership
            - lender has to have exclusive access to the address
            - borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property,
            ZTree.get address borrower_properties_pool,
            decide (borrower_num >= 1)  with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None, left _ =>
        (** - Check the valid onwership and accessibility combination for lender and borrower *)
        match mem_states_valid_combination
                lender borrower owned accessible,
              owned, add_accessor borrower borrower_num accessible,
              local_owned with
        | true, Owned owner, Some new_accessibility, LocalOwned =>
          if decide (owner = lender)
          then let new_dirty := if clean then MemClean else dirty in
               (** - Only change accessibility option of the lender. The remaining operations will
                     be performed in the retrieve *)
               let new_global_properties :=
                   ZTree.set
                     address
                     (global_property
                        {owned_by: Owned borrower}
                        {accessible_by: new_accessibility}
                        {mem_dirty : new_dirty})
                     st.(hypervisor_context).(mem_properties).(mem_global_properties) in
               (** - Create the new memory local properties pool for the borrower.
                     Instead of making a new initial state, we copied the previous local properties that lender had. 
                     Next opeartions can adjust the properties if it is necessary *)
               let new_borrower_properties_pool :=
                   ZTree.set
                     address
                     (gen_borrow_mem_local_properties_wrapper lender lender_property) 
                     borrower_properties_pool in
               let new_local_properties_global_pool :=
                   ZTree.set
                     borrower
                     new_borrower_properties_pool
                     st.(hypervisor_context).(mem_properties).(mem_local_properties) in
               let new_st :=
                   st {hypervisor_context / mem_properties :
                         mkMemProperties new_global_properties
                                         new_local_properties_global_pool} in
               trigger (SetState new_st);;
               Ret (true)
          else Ret (false)
        | _, _, _, _ => Ret (false)
        end
      | _, _, _, _ => Ret (false)
      end.

    (*************************************************************)
    (** ****        FFA_MEM_SHARE_RETRIEVE_REQ                   *)
    (*************************************************************)    
         
    Definition ffa_mem_share_retrieve_req_core_transition_spec
               (lender borrower : ffa_UUID_t) (address: Z) (clean: bool)
      : itree HypervisorEE (bool) :=
      st <- trigger GetState ;;
      (** - Find out memory properties *) 
      do global_property <-
         ZTree.get
           address
           st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <-
         ZTree.get
           lender
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <-
         ZTree.get
           borrower
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <-
         ZTree.get address lender_properties_pool ;;;
      (** - check memory properties :
            - lender has to have onwership
            - lender has to have exclusive access to the address
            - borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property,
            ZTree.get address borrower_properties_pool  with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None =>
        (** - Check the valid onwership and accessibility combination for lender and borrower *)
        match mem_states_valid_combination lender borrower owned accessible,
              owned, accessible, local_owned with
        | true, Owned owner, SharedAccess accessors, LocalOwned =>
          if decide (owner = lender) && (in_dec zeq lender accessors)
          then let new_dirty := if clean then MemClean else dirty in
               (** - Only change accessibility option of the lender. The remaining operations will
                     be performed in the retrieve *)
               let new_global_properties :=
                   ZTree.set
                     address
                     (global_property
                        {owned_by: Owned borrower}
                        {accessible_by: SharedAccess (borrower::accessors)}
                        {mem_dirty : new_dirty})
                     st.(hypervisor_context).(mem_properties).(mem_global_properties) in
               (** - Create the new  memory local properties pool for the borrower.
                     Instead of making a new initial state, we copied the previous local properties that lender had. 
                     Next opeartions can adjust the properties if it is necessary *)
               let new_borrower_properties_pool :=
                   ZTree.set
                     address
                     (gen_borrow_mem_local_properties_wrapper lender lender_property) 
                     borrower_properties_pool in
               let new_local_properties_global_pool :=
                   ZTree.set
                     borrower
                     new_borrower_properties_pool
                     st.(hypervisor_context).(mem_properties).(mem_local_properties) in
               let new_st :=
                   st {hypervisor_context / mem_properties :
                         mkMemProperties new_global_properties
                                         new_local_properties_global_pool} in
               trigger (SetState new_st);;
               Ret (true)
          else Ret (false)
        | _, _, _, _ => Ret (false)
        end
      | _, _, _ => Ret (false)
      end.

  End FFA_MEM_RETRIEVE_REQ_CORE_STEP.
  
  Section FFA_MEM_RELINQUISH_CORE_STEPS.

    (*************************************************************)
    (** ***         FFA_MEM_SHARE_RETRIEVE                       *)
    (*************************************************************)    

    (* Related parts.
       In here, we describe simple lifcycles mentioned in "5.9.2 Relinquish memory transaction lifecycle". 
       We discuss rules defined in section 11.6 in the below (the next section in this file).

       This transaction takes place as follows (also see 5.5.2 Transaction life cycle). It is assumed that the memory region
       was originally lent or shared by the Lender to the Borrowers. This transaction must not be used on a memory
       region owned by an endpoint.

       - If a Borrower is a PE endpoint or a SEPID associated with a dependent peripheral device,
         - The Lender could use a Partition message to request each Borrower to relinquish access to the memory
           region. This message contains a description of the memory region relevant to the Borrower.
         - Each Borrower uses the FFA_MEM_RELINQUISH interface (see 11.6 FFA_MEM_RELINQUISH) to
           unmap the memory region from its translation regime. This could be done in response to the message
           from the Lender or independently.
         - Each Borrower uses a Partition message to inform the Lender that it has relinquished access to the
           memory region.
         In case of an error, the Borrower can abort the transaction before the Lender reclaims the memory region by
         calling the FFA_MEM_RETRIEVE_REQ ABI (see 11.4 FFA_MEM_RETRIEVE_REQ).
       - If the Borrower is a SEPID associated with an independent peripheral device,
         - The Lender could use an IMPLEMENTATION DEFINED mechanism to request each Borrower to relinquish
           access to the memory region.
         - Each Borrower uses an IMPLEMENTATION DEFINED mechanism to request the Relayer to
           unmap the memory region from its translation regime (see 11.7.1 Component responsibilities
           for FFA_MEM_RECLAIM). This could be done in response to the message from the Lender or
           independently.
         - Each Borrower uses an IMPLEMENTATION DEFINED mechanism to inform the Lender that it has
           relinquished access to the memory region.
       - Once all Borrowers have relinquished access to the memory region, the Lender uses the FFA_MEM_RECLAIM
         interface to reclaim exclusive access to the memory region. This interface is described in 11.7
         FFA_MEM_RECLAIM.
     *)
    
    Definition remove_accessor
               (lender borrower : ffa_UUID_t)
               (access_state : ACCESS_STATE_TYPE) :=
      match access_state with 
      | ExclusiveAccess borrower' =>
        if decide (borrower = borrower')
        then Some (ExclusiveAccess lender)
        else None
      | SharedAccess (shared_vms) =>
        match shared_vms with
        | nil => None
        | borrower'::nil =>
          if decide (borrower = borrower')
          then Some (ExclusiveAccess lender) else None
        | fst::snd::nil =>
          (** - This is the case for Share. Lend opeartion excludes lender's access, so this thing cannot happen.
                The order is specified in the previous lend operation. So there is no chance for fst to be a lender *)
          if (decide (snd = lender) && decide (fst = borrower))
          then Some (ExclusiveAccess lender)
          else
            (** - This is the case for Lend. Lend opeartion excludes lender's access, so we check it
                  - we can ignore them. I believe ignoring them is safe *)
            match (List.In_dec zeq borrower shared_vms) with
            | left _ =>
              Some (SharedAccess (List.remove zeq borrower shared_vms))
            | _ => None
            end
        (** - This is the case for Lend. Lend opeartion excludes lender's access, so we check it
              - we can ignore them. I believe ignoring them is safe *)
        | _ => match (List.In_dec zeq borrower shared_vms) with
              | left _ =>
                Some (SharedAccess (List.remove zeq borrower shared_vms))
              | _ => None
              end
        end
      | _ => None
      end.

    Definition ffa_mem_relinquish_core_transition_spec
               (lender borrower : ffa_UUID_t) (address: Z) (clean: bool)
      : itree HypervisorEE (bool) :=
      st <- trigger GetState ;;
      (** - Find out memory properties *) 
      do global_property <-
         ZTree.get
           address
           st.(hypervisor_context).(mem_properties).(mem_global_properties) ;;;
      do lender_properties_pool <-
         ZTree.get
           lender
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do borrower_properties_pool <-
         ZTree.get
           borrower
           st.(hypervisor_context).(mem_properties).(mem_local_properties) ;;;
      do lender_property <- ZTree.get address lender_properties_pool ;;;
      (** - check memory properties :
            - lender has to have onwership
            - lender has to have exclusive access to the address
            - borrower does not have the memory in its memory property pool 
       *)
      match global_property, lender_property,
            ZTree.get address borrower_properties_pool  with
      | mkMemGlobalProperties owned accessible dirty,
        mkMemLocalProperties local_owned _ _ _, None =>
        (** - Check the valid onwership and accessibility combination for lender and borrower *)
        match mem_states_valid_combination lender borrower owned accessible,
              owned, remove_accessor lender borrower accessible, local_owned with
        | true, Owned owner, Some new_accessibility, LocalOwned =>
          if decide (owner = lender)
          then let new_dirty := if clean then MemClean else dirty in
               (** - Only change accessibility option of the lender. The remaining operations will
                     be performed in the retrieve *)
               let new_global_properties :=
                   ZTree.set address (global_property
                                        {owned_by: Owned lender}
                                        {accessible_by: new_accessibility}
                                        {mem_dirty : new_dirty})
                             st.(hypervisor_context).(mem_properties).(mem_global_properties) in
               (** - Create the new  memory local properties pool for the borrower.
                     Instead of making a new initial state, we copied the previous local properties that lender had. 
                     Next opeartions can adjust the properties if it is necessary *)               
               let new_borrower_properties_pool :=
                   ZTree.remove address borrower_properties_pool in
               let new_local_properties_global_pool :=
                   ZTree.set
                     borrower new_borrower_properties_pool
                     st.(hypervisor_context).(mem_properties).(mem_local_properties) in
               let new_st :=
                   st {hypervisor_context / mem_properties :
                         mkMemProperties new_global_properties
                                         new_local_properties_global_pool} in
               trigger (SetState new_st);;
               Ret (true)
          else Ret (false)
        | _, _, _, _ => Ret (false)
        end
      | _, _, _ => Ret (false)
      end.

  End FFA_MEM_RELINQUISH_CORE_STEPS.

  (* - For FFA_MEM_RETRIEVE_RESP and FFA_MEM_RECLAIM, the memory state won't be changed. 
     FFA_MEM_RETRIEVE_RESP is the return value of RRA_MEM_RETRIEVE_REQ, and FFA_MEM_RECLAIM 
     is the mssage to trigger FFA_MEM_RELINQUISH. *)
  
End FFA_MEMORY_INTERFACE_CORE_STEPS.

(***********************************************************************)
(** **                 additional steps for transitions                *)
(***********************************************************************)
Section FFA_MEMORY_INTERFACE_ADDITIONAL_STEPS.

  Context `{abstract_state_context: AbstractStateContext}.
  
  Notation HypervisorEE := (CallExternalE +' updateStateE +' GlobalE +' MemoryE +' Event).

  (** TODO: when TX/RX buffers are used to trasmit descriptors, 
      [length], [fragement_length], [address], and [page_count] 
      are not actually used. Do we need to define the following definitions even for that case? *)
  Definition ffa_mem_send_check_arguments
             (total_length fragment_length address page_count: Z)
    : bool :=
    if decide (total_length > granuale) && decide (total_length <> 0)
       || decide (fragment_length <> 0) && decide (total_length > fragment_length)
       || decide (address <> 0) || decide (page_count <> 0)
    then true
    else false. 
  
  (** Get a memory region descriptor for send (donate, lend, share) operations *)
  Definition get_send_memory_region_descriptor (caller : Z) (state: AbstractState)
    : option FFA_memory_region_struct := 
    match ZTree.get caller state.(hypervisor_context).(vms_contexts) with
    | Some vm_context =>
      mailbox_send_msg_to_region_struct vm_context.(mailbox).(send)
    | _ => None
    end.
    

  (** TODO: need to consider offset when implement LEND and SHARE *)
  Fixpoint get_constituents_from_receivers
             (receivers: list FFA_endpoint_memory_access_descriptor_struct) :=
    match receivers with
    | nil => nil
    | receiver::receivers' =>
      let constituents' := get_constituents_from_receivers receivers' in
      match receiver.(FFA_memory_access_descriptor_struct_composite_memory_region_struct) with
      | Some composite =>
        composite.(FFA_composite_memory_region_struct_constituents)
                    ++ constituents' 
      | _ => nil ++ constituents' 
      end
    end.

  (* TODO: need to fill out the following things *)
  Definition check_mem_properties_with_descriptor
             (vid : ffa_UUID_t)
             (memory_region_descriptor: FFA_memory_region_struct)
             (mem_properties : MemProperties) :=
    if decide (memory_region_descriptor.(FFA_memory_region_struct_sender) = vid)
    then true
    else false.
  
  Definition get_receivers (memory_region_descriptor: FFA_memory_region_struct)
    : list FFA_endpoint_memory_access_descriptor_struct :=
    memory_region_descriptor.(FFA_memory_region_struct_receivers).

  Fixpoint get_addresses (address: ffa_address_t) (page_count : nat) :=
    match page_count with
    | O => nil
    | S n' => let addresses' := get_addresses address n' in
             ((address + granuale * (Z.of_nat page_count))%Z)::addresses'
    end.

  Fixpoint get_addresses_from_constituents
           (constituents : list FFA_memory_region_constituent_struct) :=
    match constituents with
    | nil => nil
    | hd::tl =>
      (get_addresses (hd.(FFA_memory_region_constituent_struct_address))
                     (Z.to_nat (hd.(FFA_memory_region_constituent_struct_page_count))))
        ++ (get_addresses_from_constituents tl)
    end.
  
  Definition addresses (memory_region_descriptor: FFA_memory_region_struct) :=
    let constituents :=
        get_constituents_from_receivers 
          memory_region_descriptor.(FFA_memory_region_struct_receivers) in
    get_addresses_from_constituents constituents.
    
  (***********************************************************************)
  (** ***  11.1 FFA_MEM_DONATE                                           *)
  (***********************************************************************)
  (***********************************************************************)
  (** ***  11.2 FFA_MEM_LEND                                             *)
  (***********************************************************************)
  (***********************************************************************)
  (** ***  11.3 FFA_MEM_SHARE                                            *)
  (***********************************************************************)
  
  (** 
      - Structure
        - paramemter
          - stored register
          - description 

      - Table 11.3, 11.8, 11.13: FFA_MEM_DONATE, FFA_MEM_LEND, and FFA_MEM_SHARE function syntax
        - uint32 Function ID
          - w0 
          - 0x84000071
        - uint32 total length
          - w1
          - Total length of the memory transaction descriptor in bytes
        - uint32 Fragment length
          - w2
          - Length in bytes of the memory transaction descriptor passed in this ABI invocation.
          - Fragment length must be <= Total length.
          - If Fragment length < Total length then see 12.2.2 Transmission of transaction 
            descriptor in fragments about how the remainder of the descriptor will be transmitted.
        - uint32/uint64 Address
          - w3
          - Base address of a buffer allocated by the Owner and 
            distinct from the TX buffer. More information is
            in 12.2.1. MBZ if the TX buffer is used.
          - MBZ if the TX buffer is used.
        - uint32 Page count
          - w4
          - Number of 4K page in the buffer allocated by the 
            Owner and distinct from the TX buffer. More details
            are in 12.2.1. MBZ if the TX buffer is used
          - MBZ if the TX buffer is used
        - Other Parameter registers
          - w5-w7
          - Reserved (MBZ).

      - Table 11.4, 11.9, 11.14: FFA_SUCCESS encoding
        - uint64 Handle
          - w2/w3
          - Globally unique Handle to identify the memory 
            region on successful transmission of the transaction descriptor.
        - Other Result registers
          - w4-w7 
          - Reserved (MBZ)
      
      - Table 11.5, 11.10, 11.15: FFA_ERROR encoding
        - int32 Error code
          - w2
          - INVALID_PARAMETERS / DENIED / NO_MEMORY / BUSY / ABORTED
   *)
  
  Section FFA_MEM_DONATE_ADDITIONAL_STEPS.

    Definition get_receiver_id (region_descriptor: FFA_memory_region_struct) : option ffa_UUID_t :=
      match region_descriptor.(FFA_memory_region_struct_receivers) with
      | hd::nil =>
        Some 
          hd.(FFA_endpoint_memory_access_descriptor_struct_memory_access_permissions_descriptor).(FFA_memory_access_permissions_descriptor_struct_receiver)
      | _ => None
      end.

    Definition ffa_mem_donate_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
      : itree HypervisorEE (FFA_RESULT_CODE_TYPE) :=
      (** - Check the arguments *)
      if ffa_mem_send_check_arguments total_length fragment_length address count
      then                          
        st <- trigger (GetState);;
        match get_send_memory_region_descriptor caller st with
        | Some memory_region_descriptor =>
          (** - Check the well_formed conditions of the memory region descriptor *)
          if well_formed_FFA_memory_region_struct
               memory_region_descriptor &&
             decide ((length (get_receivers memory_region_descriptor) = 1)%nat)
          then if decide ((st.(hypervisor_context).(api_page_pool_size)
                           < (FFA_memory_region_struct_size
                                (Zlength (get_constituents_from_receivers
                                            (get_receivers memory_region_descriptor)))))%Z)
               then
                 if (check_mem_properties_with_descriptor
                       caller memory_region_descriptor st.(hypervisor_context).(mem_properties))
                 then 
                   do receiver_id <- (get_receiver_id memory_region_descriptor);;;
                   let cur_addresses := addresses memory_region_descriptor in
                   (* TODO: add cases to handle multiple address transfer *)
                   match cur_addresses with
                   | cur_address::nil =>
                     result <- ffa_mem_donate_core_transition_spec caller receiver_id cur_address;;
                     match result with  
                     (* TODO: need to creage handle! - 0 is the wrong value  *)
                     (* TODO: need to reduce mpool size *) 
                     | true => Ret (FFA_SUCCESS 0)
                     | flase => Ret (FFA_ERROR FFA_DENIED)
                     end
                   | _ => Ret (FFA_ERROR FFA_INVALID_PARAMETERS)
                   end
                 else Ret (FFA_ERROR FFA_INVALID_PARAMETERS)
               else Ret (FFA_ERROR FFA_NO_MEMORY)
          else Ret (FFA_ERROR FFA_DENIED)
        | _ => triggerUB "this case cannot happen at this moment"
        end
      else Ret (FFA_ERROR FFA_INVALID_PARAMETERS).
    
  End FFA_MEM_DONATE_ADDITIONAL_STEPS.

  Section FFA_MEM_LEND_ADDITIONAL_STEPS.
    
    Definition ffa_mem_lend_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
    : itree HypervisorEE (FFA_RESULT_CODE_TYPE) :=
      triggerUB "Not Implemented Yet".
    
  End FFA_MEM_LEND_ADDITIONAL_STEPS.

  Section FFA_MEM_SHARE_ADDITIONAL_STEPS.
   
    Definition ffa_mem_share_spec
               (caller : ffa_UUID_t)               
               (total_length fragment_length address count : Z)
    : itree HypervisorEE (FFA_RESULT_CODE_TYPE) :=
      triggerUB "Not Implemented Yet".
    
  End FFA_MEM_SHARE_ADDITIONAL_STEPS.

  Section FFA_MEM_RETRIEVE_REQ_ARGUMENT_CHECKS.
    (***********************************************************************)
    (** ***  11.4 FFA_MEM_RETRIEVE_REQ                                     *)
    (***********************************************************************)
    (** 
      - Structure
        - paramemter
          - stored register
          - description 

      - Table 11.18: FFA_MEM_RETRIEVE_REQ function syntax
        - uint32 Function ID
          - w0
          - 0x84000074
        - uint32 Total length
          - w1
          - Total length of the memory transaction descriptor in bytes.
        - uint32 Fragment length 
          - w2
          - Length in bytes of the memory transaction descriptor passed in this ABI invocation.
          - Fragment length must be <= Total length.
          - If Fragment length < Total length then see 12.2.2 Transmission of transaction 
            descriptor in fragments about how the remainder of the descriptor will be
            transmitted.
        - uint32/uint64 Address
          - w3
          - Base address of a buffer allocated by the Owner and distinct from the TX buffer. See 12.2.1
            Transmission of transaction descriptor in dynamically allocated buffers.
          - MBZ if the TX buffer is used.
        - uint32 Page count
          - w4
          - Number of 4K pages in the buffer allocated by the 
            Owner and distinct from the TX buffer. See 12.2.1
            Transmission of transaction descriptor in dynamically allocated buffers.
          - MBZ if the TX buffer is used.
        - Other Parameter registers 
          - w5-w7
          - Reserved (MBZ)

      - Table 11.19: FFA_ERROR encoding
        - int32 Error code 
          - w2
          - INVALID_PARAMETERS / DENIED / NO_MEMORY / BUSY / ABORTED
     *)

    Definition ffa_mem_retrieve_req_spec
               (caller : ffa_UUID_t)
               (total_length fragment_length address count : Z)
    : itree HypervisorEE (FFA_RESULT_CODE_TYPE) :=
      triggerUB "Not Implemented Yet".
    
  End FFA_MEM_RETRIEVE_REQ_ARGUMENT_CHECKS.

  Section FFA_MEM_RETRIEVE_RESP_ARGUMENT_CHECKS.
    (***********************************************************************)
    (** ***  11.5 FFA_MEM_RETRIEVE_RESP                                    *)
    (***********************************************************************)
    (** 
      - Structure
        - paramemter
          - stored register
          - description 

      - Table 11.22: FFA_MEM_RETRIEVE_RESP function syntax
        - uint32 Function ID
          - w0
          - 0x84000075
        - uint32 Total length
          - w1
          - Total length of the memory transaction descriptor in bytes.
        - uint32 Fragment length 
          - w2
          - Length in bytes of the memory transaction descriptor passed in this ABI invocation.
          - Fragment length must be <= Total length.
          - If Fragment length < Total length then see 12.2.2 Transmission of transaction 
            descriptor in fragments about how the remainder of the descriptor will be
            transmitted.
        - uint32/uint64 Parameter
          - w3
          - Reserved (MBZ)
        - uint32/uint64 Parameter
          - w4
          - Reserved (MBZ)
        - Other Parameter registers 
          - w5-w7
          - Reserved (MBZ)

      - Table 11.23: FFA_ERROR encoding
        - int32 Error code 
          - w2
          - INVALID_PARAMETERS / NO_MEMORY
     *)
    
    Definition ffa_mem_retrieve_resp_spec
               (caller : ffa_UUID_t)               
               (total_length fragment_length : Z)
    : itree HypervisorEE (FFA_RESULT_CODE_TYPE) :=
      triggerUB "Not Implemented Yet".    
    
  End FFA_MEM_RETRIEVE_RESP_ARGUMENT_CHECKS.

  Section FFA_MEM_RELINQUISH_ARGUMENT_CHECKS.
    (***********************************************************************)
    (** ***  11.6 FFA_MEM_RELINQUISH                                       *)
    (***********************************************************************)
    (** 
      - Structure
        - paramemter
          - stored register
          - description 

      - Table 11.27: FFA_MEM_RELINQUISH function syntax
        - uint32 Function ID
          - w0
          - 0x84000076
        - Other Parameter registers
          - w1-w7
          - Reserved (MBZ)

      - Table 11.28: FFA_ERROR encoding
        - int32 Error code 
          - w2
          - INVALID_PARAMETERS / DENIED / NO_MEMORY / ABORTED
     *)

    Definition ffa_mem_relinquish_spec
               (caller : ffa_UUID_t)               
    : itree HypervisorEE (FFA_RESULT_CODE_TYPE) :=
      triggerUB "Not Implemented Yet".

    
  End FFA_MEM_RELINQUISH_ARGUMENT_CHECKS.
    
  Section FFA_MEM_RECLAIM_ARGUMENT_CHECKS.
    (***********************************************************************)
    (** ***  11.7 FFA_MEM_RECLAIM                                          *)
    (***********************************************************************)
    (** 
      - Structure
        - paramemter
          - stored register
          - description 

      - Table 11.31: FFA_MEM_RECLAIM function syntax
        - uint32 Function ID
          - w0
          - 0x84000077
        - uint64 Handle
          - w1/w2
          - Globally unique Handle to identify the memory region (see 5.10.2 Memory region handle).
        - uint32 Flags
          - w3
          - Bit(0): Zero memory before reclaim flag.
            – This flag specifies if the Relayer must clear memory region contents before mapping it in
              the Owner translation regime.
              - b0: Relayer must not zero the memory region contents.
              - b1: Relayer must zero the memory region contents.
            – Relayer must fulfill memory zeroing requirements listed in in 5.12.4 Flags usage.
            – MBZ if the Owner has Read-only access to the memory region, else the Relayer must return DENIED.
          - Bit(1): Operation time slicing flag.
            – This flag specifies if the Relayer can time slice this operation.
              - b0: Relayer must not time slice this operation.
              - b1: Relayer can time slice this operation.
            - MBZ if the Relayer does not support time slicing of memory management operations (see 12.2.3 Time
              slicing of memory management operations) .
          - Bit(31:2): Reserved (MBZ).
        - Other Parameter registers
          - w4-w7
          - Reserved (MBZ)

      - Table 11.32: FFA_ERROR encoding
        - int32 Error code 
          - w2
          - INVALID_PARAMETERS / DENIED / NO_MEMORY / ABORTED
     *)

    Definition ffa_mem_reclaim_spec
               (caller : ffa_UUID_t)               
               (handle_high handle_low flags : Z)
    : itree HypervisorEE (FFA_RESULT_CODE_TYPE) :=
      triggerUB "Not Implemented Yet".
    
  End FFA_MEM_RECLAIM_ARGUMENT_CHECKS.
    
End FFA_MEMORY_INTERFACE_ADDITIONAL_STEPS.








(************************************************************************************************)
(* In the below: ignore them  *)


(*
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

   
*)





  
  (*    
  
  (** **** FFA Mem Default Flags *)  
  Record FFA_mem_default_flags_struct :=
    mkFFA_mem_default_flags_struct {
        (** - Bit(0): Zero memory flag.
              - In an invocation of FFA_MEM_DONATE or FFA_MEM_LEND, this flag specifies
                if the memory region contents must be zeroed by the Relayer after the memory
                region has been unmapped from the translation regime of the Owner.
                - b0: Relayer must not zero the memory region contents.
                - b1: Relayer must zero the memory region contents.
              - MBZ in an invocation of FFA_MEM_SHARE, else the Relayer must return INVALID_PARAMETERS.
              - MBZ if the Owner has Read-only access to the memory region , else the Relayer must return DENIED. *)
        FFA_mem_default_flags_struct_zero_memory_flag: bool;
        (** - Bit(1): Operation time slicing flag.
              - In an invocation of FFA_MEM_DONATE, FFA_MEM_LEND or
                FFA_MEM_SHARE, this flag specifies if the Relayer can time slice this operation.
                - b0: Relayer must not time slice this operation.
                - b1: Relayer can time slice this operation.
              -  MBZ if the Relayer does not support time slicing of memory management
                 operations (see 12.2.3 Time slicing of memory management operations), else the
                 Relayer must return INVALID_PARAMETERS. *)
        FFA_mem_default_flags_struct_operation_time_slicing_flag: bool;
        (** - Bit(31:2): Reserved (MBZ). *)
      }.
      *)
(*
(*
11.1.1.2 Relayer responsibilities
1. Must validate the Total length input parameter to ensure that the length of the transaction descriptor does not
exceed the size of the buffer it has been populated in. Must return INVALID_PARAMETERS in case of an
error.
*)

(*    
2. Must validate the Sender endpoint ID field in the transaction descriptor to ensure that the Sender is the Owner
of the memory region and a PE endpoint. Must return DENIED in case of an error.
 *)
(*
3. Must ensure that a request by an SP to donate Secure memory to a NS-Endpoint is rejected by returning the
DENIED error code.
 *)
 (*
4. Must ensure that the memory region is in the Owner-EA state for the Owner (see Table 5.9). It must return
DENIED in case of an error.
  *)

(*    
5. Must validate that the Endpoint memory access descriptor count & Endpoint memory access descriptor array
fields in the transaction descriptor as specified in 5.12.3.3 Relayer usage.
 *)

(*    
6. Must validate the Memory region attributes field in the transaction descriptor as specified in 5.11.4 Memory
region attributes usage.
 *)

(*
7. Must validate the Flags field specified in the transaction descriptor as specified in 5.12.4 Flags usage.
 *)

(*
8. Must validate the Handle field specified in the transaction descriptor as specified in 5.12.1 Handle usage.
 *)

(*    
9. Unmap the memory region from the translation regime of the Owner, if managed by the Relayer as specified
in 5.3 Address translation regimes.
 *)

    (*
10. If the Receiver is a PE endpoint or a Stream endpoint with a proxy endpoint managed by the Relayer, then
the Relayer must:
1. Save the transaction descriptor information so that it can be validated when retrieved through invocations
of the FFA_MEM_RETRIEVE_REQ & FFA_MEM_RETRIEVE_RESP interfaces.
2. Return NO_MEMORY if there is not enough memory to complete this operation.
*)

(*    
11. If the Receiver is a Stream endpoint associated with an independent device managed by the Relayer, then the
Relayer must:
1. Allocate an IPA range and map the memory region in the translation regime of the Receiver managed by
the Relayer as specified in 5.3 Address translation regimes.
The mapping must be created with the memory region attributes and permissions specified in the
transaction descriptor.
2. Describe the memory region to the device using the SEPID through an IMPLEMENTATION DEFINED
mechanism.
 *)

(*
12. If the call executes successfully, the Relayer must:
1. Ensure that the state of the memory region in the participating FF-A components is observed as follows:
1. If the Receiver is a PE endpoint or a SEPID associated with a dependent peripheral device, then:
• Owner-NA for the Owner.
• !Owner-NA for the Receiver.
2. If the Receiver is a SEPID associated with an independent peripheral device, then:
• !Owner-NA for the Owner.
• Owner-EA for the Receiver.
2. Allocate and return a Handle as described in 5.10.2 Memory region handle.
 *)
(*    
13. If the Owner is a VM and the Receiver is an SP or SEPID associated with a Secure Stream ID, the Hypervisor
must forward the memory transaction descriptor to the SPM. This must be done by invoking this interface at
the Non-secure physical FF-A instance as follows.
1. The fields of the transaction descriptor must be unchanged apart from the following exception.
1. The memory region must be described as composed of physically addressed constituent 4K pages in
one or more Constituent memory region descriptors.
This must be done by performing the VA or IPA to PA translation of the memory region described
by the Owner at the non-secure virtual FF-A instance.
The order in which the address ranges are specified by the Owner must be preserved by the
Hypervisor.
2. The Constituent memory region descriptors must be described in a Composite memory region
descriptor which must be referenced by the Endpoint memory access descriptor included in the
transaction descriptor.
2. The updated transaction descriptor must be copied into the TX buffer shared between the Hypervisor
and SPM.
If the TX buffer is busy, the Hypervisor must return BUSY.
If the TX buffer is too small and it is not possible to use the optional features to transmit the descriptor
listed in 12.2.2 Transmission of transaction descriptor in fragments and 12.2.1 Transmission of
transaction descriptor in dynamically allocated buffers, the Hypervisor must return NO_MEMORY
The SPM must fulfill the Relayer responsibilities listed in this section.
  *)               
  *)

