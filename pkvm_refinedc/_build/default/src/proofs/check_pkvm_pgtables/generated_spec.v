From refinedc.typing Require Import typing.
From refinedc.project.pkvm_refinedc.src.check_pkvm_pgtables Require Import generated_code.
From refinedc.project.pkvm_refinedc.src.check_pkvm_pgtables Require Import page_table_entry_type.
Set Default Proof Using "Type".

(* Generated from [src/check_pkvm_pgtables.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [entry_kind]. *)
  Definition type_of_entry_kind :=
    fn(∀ (npte, nlevel) : nat * nat; (npte @ (int (u64))), (nlevel @ (int (u8))); True)
      → ∃ () : (), (int (u32)); True.

  (* Function [hyp_phys_to_virt] has been skipped. *)

  (* Function [AArch64_TranslationTableWalk] has been skipped. *)

  (* Function [main] has been skipped. *)
End spec.
