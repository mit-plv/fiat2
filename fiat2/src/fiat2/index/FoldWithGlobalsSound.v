Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.index.IndexInterface.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Morphisms.
Import ListNotations.

Section WithMap.
  Notation value := (value).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Section WithIndex.
    Context {idx : IndexInterface.index} {idx_wf : value -> value -> Prop} {idx_ok : ok idx idx_wf}.
    Context (is_tbl_ty : type -> bool) (aux_ty : type -> type) (aux_wf : value -> Prop).

    Notation expr_aug_transf_sound := (expr_aug_transf_sound is_tbl_ty aux_ty aux_wf).
    Notation aug_transf_sound := (aug_transf_sound is_tbl_ty aux_ty aux_wf).

    Lemma fold_command_with_globals_sound : forall f,
        expr_aug_transf_sound f ->
        aug_transf_sound (fun x => fold_command_with_globals [x] (f x)).
    Proof.
      unfold expr_aug_transf_sound, aug_transf_sound; intros; intuition idtac.
      3: symmetry; eapply fold_command_with_globals_preserve_sem;
      resolve_locals_wf; eauto; auto.
      2: eapply fold_command_with_globals_preserve_index_wf; eauto; auto.
      1: eapply fold_command_with_globals_preserve_ty; eauto; try reflexivity.
      (* a whole program is checked under no assumption *)
      all: try exact I.
      all: try (unfold preserve_ty; intros; eapply H; eauto).
      all: unfold preserve_sem; intros;
        lazymatch goal with
          H: context[type_of _ _ _ _ -> _], H': type_of _ _ _ _ |- _ =>
            eapply H in H' as [HL HR]; eauto end; erewrite HR; eauto.
    Qed.
  End WithIndex.
End WithMap.

#[export] Hint Resolve fold_command_with_globals_sound : transf_hints.
