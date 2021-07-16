From refinedc.typing Require Import typing.
From refinedc.project.pkvm_refinedc.src.check_pkvm_pgtables Require Import generated_code.
From refinedc.project.pkvm_refinedc.src.check_pkvm_pgtables Require Import page_table_entry_type.
From refinedc.project.pkvm_refinedc.src.check_pkvm_pgtables Require Import Decision.
Set Default Proof Using "Type".

(* Generated from [src/check_pkvm_pgtables.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [fault_record]. *)
  Definition fault_record_rec : (Z -d> typeO) → (Z -d> typeO) := (λ self statuscode,
    (
      struct struct_FaultRecord [@{type}
        (statuscode @ (int (u32)))
      ]
    )
  )%I.
  Typeclasses Opaque fault_record_rec.

  Global Instance fault_record_rec_ne : Contractive fault_record_rec.
  Proof. solve_type_proper. Qed.

  Definition fault_record : rtype := {|
    rty_type := Z;
    rty r__ := fixp fault_record_rec r__
  |}.

  Lemma fault_record_unfold (statuscode : Z):
    (statuscode @ fault_record)%I ≡@{type} (
      (
        struct struct_FaultRecord [@{type}
          (statuscode @ (int (u32)))
        ]
      )
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance fault_record_rmovable : RMovable fault_record :=
    {| rmovable patt__ := movable_eq _ _ (fault_record_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance fault_record_simplify_hyp_place_inst_generated l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ fault_record)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (fault_record_unfold _)).
  Global Instance fault_record_simplify_goal_place_inst_generated l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ fault_record)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (fault_record_unfold _)).

  Global Program Instance fault_record_simplify_hyp_val_inst_generated v_ patt__:
    SimplifyHypVal v_ (patt__ @ fault_record)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (fault_record_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance fault_record_simplify_goal_val_inst_generated v_ patt__:
    SimplifyGoalVal v_ (patt__ @ fault_record)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (fault_record_unfold _) T _).
  Next Obligation. done. Qed.

  (* Definition of type [full_address]. *)
  Definition full_address_rec : (Z * Z -d> typeO) → (Z * Z -d> typeO) := (λ self patt__,
    let address := patt__.1 in
    let NS := patt__.2 in
    (
      struct struct_FullAddress [@{type}
        (address @ (int (u64))) ;
        (NS @ (int (u32)))
      ]
    )
  )%I.
  Typeclasses Opaque full_address_rec.

  Global Instance full_address_rec_ne : Contractive full_address_rec.
  Proof. solve_type_proper. Qed.

  Definition full_address : rtype := {|
    rty_type := Z * Z;
    rty r__ := fixp full_address_rec r__
  |}.

  Lemma full_address_unfold (patt__ : Z * Z):
    (patt__ @ full_address)%I ≡@{type} (
      let address := patt__.1 in
      let NS := patt__.2 in
      (
        struct struct_FullAddress [@{type}
          (address @ (int (u64))) ;
          (NS @ (int (u32)))
        ]
      )
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance full_address_rmovable : RMovable full_address :=
    {| rmovable patt__ := movable_eq _ _ (full_address_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance full_address_simplify_hyp_place_inst_generated l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ full_address)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (full_address_unfold _)).
  Global Instance full_address_simplify_goal_place_inst_generated l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ full_address)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (full_address_unfold _)).

  Global Program Instance full_address_simplify_hyp_val_inst_generated v_ patt__:
    SimplifyHypVal v_ (patt__ @ full_address)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (full_address_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance full_address_simplify_goal_val_inst_generated v_ patt__:
    SimplifyGoalVal v_ (patt__ @ full_address)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (full_address_unfold _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

  (* Specifications for function [entry_kind]. *)
  Definition type_of_entry_kind :=
    fn(∀ (zpte, zlevel) : Z * Z; (zpte @ (int (u64))), (zlevel @ (int (u8))); ⌜well_formed_page_table_entry zpte zlevel⌝)
      → ∃ res : Z, (res @ (int (u32))); True.

  (* Function [mkFault] has been skipped. *)

  (* Function [hyp_phys_to_virt] has been skipped. *)

  (* Function [AArch64_TranslationTableWalk] has been skipped. *)

  (* Function [main] has been skipped. *)
End spec.

Typeclasses Opaque fault_record_rec.
Typeclasses Opaque full_address_rec.
