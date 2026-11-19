Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils.
Require Import coqutil.Map.Interface.
From Stdlib Require Import List String ZArith.
Import ListNotations.

Section WithMap.
  Notation value := (value).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Definition preserve_ty Gstore f :=
    forall e t (Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv ->
      type_of Gstore Genv e t -> type_of Gstore Genv (f e) t.

  Definition preserve_sem Gstore store f :=
    forall e t (Genv : tenv) (env : locals),
      tenv_wf Gstore -> tenv_wf Genv ->
      type_of Gstore Genv e t ->
      locals_wf Gstore store -> locals_wf Genv env ->
      interp_expr store env (f e) = interp_expr store env e.

  Definition transf_sound (f : tenv -> tenv -> command -> command) :=
    forall (Gstore Genv : tenv) c,
      tenv_wf Gstore -> tenv_wf Genv ->
      well_typed Gstore Genv c ->
      well_typed Gstore Genv (f Gstore Genv c) /\
        forall (store env : locals),
          locals_wf Gstore store -> locals_wf Genv env ->
          interp_command store env (f Gstore Genv c) = interp_command store env c.

  Lemma transf_sound_compose : forall f g,
      transf_sound f -> transf_sound g ->
      transf_sound (fun Gstore Genv => Basics.compose (f Gstore Genv) (g Gstore Genv)).
  Proof.
    unfold transf_sound; intros * H_f H_g; intros.
    apply H_g in H1; auto; destruct H1.
    apply H_f in H1; intuition idtac.
    rewrite H4, H2; auto.
  Qed.

  Lemma transf_sound__preserve_sem : forall f,
      transf_sound f ->
      forall (Gstore Genv : tenv) (c : command),
        tenv_wf Gstore -> tenv_wf Genv ->
        well_typed Gstore Genv c ->
        forall (store env : locals),
          locals_wf Gstore store -> locals_wf Genv env ->
          interp_command store env (f Gstore Genv c) = interp_command store env c.
  Proof.
    unfold transf_sound; intuition idtac.
    apply H; auto.
  Qed.

  Definition expr_transf_sound (f : expr -> expr) :=
    forall Gstore Genv e t,
      tenv_wf Gstore -> tenv_wf Genv ->
      type_of Gstore Genv e t ->
      type_of Gstore Genv (f e) t /\
        forall (store env : locals),
          locals_wf Gstore store -> locals_wf Genv env ->
          interp_expr store env (f e) = interp_expr store env e.

  Lemma expr_transf_sound_compose : forall f g,
      expr_transf_sound f -> expr_transf_sound g ->
      expr_transf_sound (Basics.compose f g).
  Proof.
    unfold expr_transf_sound; intros * H_f H_g; intros.
    apply H_g in H1; auto; destruct H1.
    apply H_f in H1; intuition idtac.
    rewrite H4, H2; auto.
  Qed.

  Fixpoint repeat_transf (f : command -> command) (n : nat) :=
    match n with
    | O => id
    | S n => Basics.compose f (repeat_transf f n)
    end.
End WithMap.

#[export] Hint Resolve transf_sound_compose : transf_hints.
