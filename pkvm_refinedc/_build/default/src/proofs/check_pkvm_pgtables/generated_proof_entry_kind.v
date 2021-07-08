From refinedc.typing Require Import typing.
From refinedc.project.pkvm_refinedc.src.check_pkvm_pgtables Require Import generated_code.
From refinedc.project.pkvm_refinedc.src.check_pkvm_pgtables Require Import generated_spec.
From refinedc.project.pkvm_refinedc.src.check_pkvm_pgtables Require Import page_table_entry_type.
Set Default Proof Using "Type".

(* Generated from [src/check_pkvm_pgtables.c]. *)
Section proof_entry_kind.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [entry_kind]. *)
  Lemma type_entry_kind :
    ⊢ typed_function impl_entry_kind type_of_entry_kind.
  Proof.
    Open Scope printing_sugar.
    start_function "entry_kind" ([npte nlevel]) => arg_pte arg_level.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "entry_kind" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "entry_kind".
  Qed.
End proof_entry_kind.
