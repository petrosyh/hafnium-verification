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
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Import Int64.

Require Import Maps.
Set Implicit Arguments.

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
(* 

Table 5.1: Ownership states
No.     Ownership state         Acronym         Description
1       Owner                   Owner           Component owns the memory region.
2       Not Owner               !Owner          Component does not own the memory


Table 5.2 Access states
No.       Access state          Acronym         Description
1         No access             NA              A component has no access to a memory region. 
                                                It is not mapped in its translation regime.
2         Exclusive access      EA              A component has exclusive access to a memory region. 
                                                It is mapped only in its translation regime.
3         Shared access         SA              A component has shared access to a memory. 
                                                It is mapped in its translation regime and 
                                                the translation regime of at least one other component
*)

Section AbstractState.

  Definition addr := Z.
  Definition vm_id := Z.
  Definition hafnium_id := Z.  

  Class HighSpecContext :=
    {
    hid : hafnium_id; (* hafnium id *)
    address_low : addr;
    address_high : addr;
    alignment_value : Z; (* usually 4096 *)
    address_le_prop :
      (address_low < address_high)%Z;
    alignment_value_non_zero_prop :
      alignment_value > 0;
    address_low_alignment_prop :
      (Z.modulo address_low alignment_value)%Z = 0;
    address_high_alignment_prop :
      (Z.modulo address_high alignment_value)%Z = 0
    }.

  Context `{high_spec_context: HighSpecContext}.
  
  (* an entity is either a VM or Hafnium ("+" means "or") *)
  Definition entity_id : Type := vm_id + hafnium_id.

  Inductive OwnershipState :=
  | Owned (id : entity_id)
  | NotOwned.

  Inductive AccessState :=
  | NoAccess
  | ExclusiveAccess (id : entity_id)
  | SharedAccess (list : entity_id).

  (* boilerplate: convert vm_ids and hafnium_id to entity_id if needed *)
  Local Definition inl_entity : vm_id -> entity_id := @inl vm_id hafnium_id.
  Local Definition inr_entity : hafnium_id -> entity_id := @inr vm_id hafnium_id.
  Local Coercion inl_entity : vm_id >-> entity_id.
  Local Coercion inr_entity : hafnium_id >-> entity_id.
  Hint Unfold inl_entity inr_entity.
  Set Printing Coercions.

  (* boilerplate: decidability for the entity_id type *)
  Definition entity_id_eq_dec (i1 i2 : entity_id) : {i1 = i2} + {i1 <> i2}.
  Admitted.
  
  (* unchanging starting parameters of the global state *)
  Class abstract_state_parameters :=
    {
    vms : list vm_id;
    hafnium_reserved : addr -> bool;
    }.
  
  Class abstract_state :=
    {
    accessible_by : ZMap.t AccessState;
    owned_by : ZMap.t  OwnershipState
    }.
  
  (* There are multiple well-formedness conditions, but it enumerate some basic well-formedness *)
  (*
  Table 5.3: Valid combinations of ownership and access states
  No.     Ownership state       Access state         Acronym           Description
  1       Not Owner             No access            !Owner-NA         Component has neither ownership nor access 
                                                                       to the memory region.
  2       Not Owner             Exclusive access     !Owner-EA         Component has exclusive access without 
                                                                       ownership of the memory region.
  3       Not Owner             Shared access        !Owner-SA         Component has shared access with one or more
                                                                       components without ownership of the memory region.
  4       Owner                 No access            Owner-NA          Component owns the memory region and has granted:
                                                                       - Either exclusive access to the memory region to 
                                                                         another component.
                                                                       - Or shared access to the memory region among other
                                                                         components.
  5       Owner                 Exclusive access     Owner-EA          Component owns the memory region and has exclusive 
                                                                       access to it.
  6       Owner                 Shared access        Owner-SA          Component owns the memory region and shares 
                                                                       access to it with one or more components.
   
  Table 5.4: Valid combinations of ownership and access states between two components
  No.     Component A state     Component B state       Description
  1       Owner-EA              !Owner-NA               Component A has exclusive access and ownership of a memory region 
                                                        that is inaccessible from component B.
  2       Owner-NA              !Owner-NA               Component A has granted exclusive access to a memory region it 
                                                        owns to another component. It is inaccessible from component B.
  3       Owner-NA              !Owner-EA               Component A has granted exclusive access to a memory region it 
                                                        owns to component B.
  4       Owner-NA              !Owner-SA               Component A has relinquished access to a memory region it owns. 
                                                        Access to the memory region is shared between component B and
                                                        at least one other component
  5       Owner-SA              !Owner-NA               Component A shares access to a region of memory it owns with 
                                                        another component. Component B cannot access the memory region.
  6       Owner-SA              !Owner-SA               Component A shares access to a region of memory it owns with 
                                                        component B and possibly other components.
  *)
  Definition well_formed  := admit.

  

  (* TODO: need to add  more state in here - e.g. register values defined in interfaces / permissions of each page entry 
     described in the FF-A document *)
  
End AbstractState.

Section AbstractModel.
  
  Context `{high_spec_context: HighSpecContext}.

  (*
  Table 5.5: Memory region transactions
  No.   Transaction        Description
  1.    Donate             - Endpoint A transfers ownership of a memory region it owns to endpoint B.
  2.    Lend               - Endpoint A relinquishes access to a memory region and grants it to only endpoint B. 
                             Endpoint B gains exclusive access to the memory region.
                           - Endpoint A relinquishes access to a memory region and grants it to endpoint B and 
                             at least one other endpoint simultaneously. Endpoint B gains shared 
                             access to the memory region.
  3.    Share              - Endpoint A grants access to a memory region to endpoint B and optionally to 
                             other endpoints simultaneously. 
  4.    Relinquish         - Endpoint B relinquishes access to a memory region granted to it by Endpoint A. 
                             Endpoint A reclaims exclusive access to the memory region.
   
  Transaction life cycle
  1. The Sender sends a Framework message to the Relayer to start a transaction involving one or more Receivers.
  2. The Sender sends a Partition message requesting each Receiver to complete the transaction.
  3. Each Receiver sends a Framework message to the Relayer to complete the transaction.
  *)

  Section Donate.

  (*
  Table 5.9: Donate memory transaction state machine
  No.   Current        Current           Next           Next              Description
        Endpoint       Endpoint          Endpoint       Endpoint
        A state        B state           A state        B state
  1     Owner-EA       !Owner-NA         !Owner-NA      Owner-EA          Owner has exclusive access to the memory region and transfers
                                                                          ownership to endpoint B.
  2     Owner-NA       !Owner-NA         Error                            Owner does not have exclusive access to the memory region.
                                                                          It cannot transfer its ownership.
  3     Owner-NA       !Owner-SA         Error                            Owner has lent access to the memory region to endpoint B and
                                                                          possibly other endpoints. It cannot transfer its ownership.
  4     Owner-SA       !Owner-NA         Error                            Owner has shared access to the memory region with one or more
                                                                          endpoints. It cannot transfer its ownership.
  5     Owner-SA       !Owner-SA         Error                            Owner has shared access to the memory region with endpoint B
                                                                          and possibly other endpoints. It cannot transfer its ownership.
  *)

  End Donate.

  Section Lend.

  (* 
  Table 5.10: Lend memory transaction state machine
  No.   Current        Current           Next           Next              Description
        Endpoint       Endpoint          Endpoint       Endpoint
        A state        B state           A state        B state
  1     Owner-EA       !Owner-NA         Owner-NA       !Owner-EA         Owner has exclusive access to the
                                                        or !Owner-SA      memory region and relinquishes access to it to one or more
                                                                          Borrowers including endpoint B.
  2     Owner-NA       !Owner-NA         Error                            Owner has already lent the memory region to one or more endpoints. 
                                                                          It cannot lend it to endpoint B.
  3     Owner-NA       !Owner-EA         Error                            Owner has already lent the memory region to endpoint 
                                                                          B with exclusive access.
  4     Owner-NA       !Owner-SA         Error                            Owner has already lent the memory region to endpoint 
                                                                          B and other endpoints.
  5     Owner-SA       !Owner-NA         Error                            Owner has already shared the memory region with one or more 
                                                                          endpoints. It cannot lend it to endpoint B.
  6     Owner-SA       !Owner-SA         Error                            Owner has already shared the memory region with endpoint B and
                                                                          possibly other endpoints.
  *)

    
  End Lend.

  Section Share.
  
  (*   
  Table 5.11: Share memory transaction state machine
  No.   Current        Current           Next           Next              Description
        Endpoint       Endpoint          Endpoint       Endpoint
        A state        B state           A state        B state
  1     Owner-EA       !Owner-NA         Owner-SA       !Owner-SA         Owner has exclusive access to the memory region and grants access 
                                                                          to it to one or more Borrowers including endpoint B.
  2     Owner-NA       !Owner-NA         Error                            Owner has already lent the memory region to one or more endpoints. 
                                                                          It cannot share it with endpoint B.
  3     Owner-NA       !Owner-EA         Error                            Owner has already lent the memory region to endpoint B with 
                                                                          exclusive access.
  4     Owner-NA       !Owner-SA         Error                            Owner has already lent the memory region to endpoint B and 
                                                                          other endpoints.
  5     Owner-SA       !Owner-NA         Error                            Owner has already shared the memory region with one or more endpoints.
                                                                          It cannot share it with endpoint B.
  6     Owner-SA       !Owner-SA         Error                            Owner has already shared the memory region with endpoint B and 
                                                                          possibly other endpoints.
  *)

    
  End Share.

  Section Relinquish.

  (*
  Table 5.12: Relinquish and reclaim memory state machine
  No.   Current        Current           Next           Next              Description
        Endpoint       Endpoint          Endpoint       Endpoint
        A state        B state           A state        B state
  1     Owner-EA       !Owner-NA         Error                            Endpoint B tries to relinquish access to a memory region 
                                                                          that the Owner has exclusive access to.
  2     Owner-NA       !Owner-NA         Error                            Endpoint B tries to relinquish access to a memory region
                                                                          that the Owner has granted shared or exclusive access to 
                                                                          one or more other Borrowers.
  3     Owner-NA       !Owner-EA         Owner-EA       !Owner-NA         Endpoint B relinquishes exclusive access to the memory region 
                                                                          and transfers it back to the Owner.
  4     Owner-NA       !Owner-SA         Owner-EA       !Owner-NA         Endpoint B relinquishes access to the memory region that it shares 
                                                                          with other Borrowers. Owner reclaims exclusive access once all 
                                                                          Borrowers have relinquished access.
  5     Owner-SA       !Owner-NA         Error                            Endpoint B tries to give up access to a memory region that the 
                                                                          Owner shares with one or more other Borrowers.
  *)

  End Relinquish.

End AbstractModel.
