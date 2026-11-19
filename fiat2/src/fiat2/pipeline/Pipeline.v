Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils
  fiat2.TransfSound fiat2.Invariant fiat2.constraint.Surface fiat2.rules.EraseField.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String.

(* The compiler: typecheck the elaborated program, run the passes that keep the
   invariant context, then the passes that only keep well-typedness. *)

Section WithMap.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Definition run_passes (ps : list (tenv -> tenv -> command -> command)) (c : command) : command :=
    fold_left (fun c f => f map.empty map.empty c) ps c.

  Definition compile (ipasses fpasses : list (tenv -> tenv -> command -> command)) (sc : scommand)
    : result command :=
    match typecheck map.empty map.empty (elab nil sc) with
    | Success c => Success (run_passes fpasses (run_passes ipasses c))
    | Failure err => Failure err
    end.

  Lemma run_passes_cons : forall f ps c,
      run_passes (f :: ps) c = run_passes ps (f map.empty map.empty c).
  Proof. reflexivity. Qed.

  Lemma run_inv_passes : forall ps c,
      Forall (inv_transf_sound (locals := locals)) ps ->
      maintains_invs (locals := locals) map.empty map.empty nil (fun _ _ => True) c ->
      maintains_invs (locals := locals) map.empty map.empty nil (fun _ _ => True) (run_passes ps c) /\
        forall store env : locals, interp_command store env (run_passes ps c) = interp_command store env c.
  Proof.
    induction ps as [ | f ps IH ]; intros c H_ps H_c.
    1: split; [ exact H_c | reflexivity ].
    rewrite run_passes_cons. inversion H_ps as [ | ? ? H_f H_ps' ]; subst.
    destruct (H_f map.empty map.empty nil _ c tenv_wf_empty tenv_wf_empty (Forall_nil _) H_c) as [ H_c' H_sem ].
    destruct (IH _ H_ps' H_c') as [ H_r H_rsem ].
    split; [ exact H_r | ].
    intros store env. rewrite H_rsem. apply H_sem; auto using locals_wf_empty. constructor.
  Qed.

  Lemma run_wt_passes : forall ps c,
      Forall (transf_sound (locals := locals)) ps ->
      well_typed map.empty map.empty c ->
      well_typed map.empty map.empty (run_passes ps c) /\
        forall store env : locals, interp_command store env (run_passes ps c) = interp_command store env c.
  Proof.
    induction ps as [ | f ps IH ]; intros c H_ps H_c.
    1: split; [ exact H_c | reflexivity ].
    rewrite run_passes_cons. inversion H_ps as [ | ? ? H_f H_ps' ]; subst.
    destruct (H_f map.empty map.empty c tenv_wf_empty tenv_wf_empty H_c) as [ H_c' H_sem ].
    destruct (IH _ H_ps' H_c') as [ H_r H_rsem ].
    split; [ exact H_r | ].
    intros store env. rewrite H_rsem. apply H_sem; apply locals_wf_empty.
  Qed.

  Theorem compile_sound : forall ipasses fpasses sc c,
      Forall (inv_transf_sound (locals := locals)) ipasses ->
      Forall (transf_sound (locals := locals)) fpasses ->
      compile ipasses fpasses sc = Success c ->
      well_typed map.empty map.empty c /\
        forall store env : locals, interp_command store env c = interp_command store env (elab nil sc).
  Proof.
    unfold compile; intros * H_ip H_fp H_c.
    destruct (typecheck map.empty map.empty (elab nil sc)) as [ c0 | ] eqn:E; [ | discriminate ].
    injection H_c as <-.
    pose proof (elab_prog_maintains_invs (locals := locals) sc map.empty map.empty c0
                  tenv_wf_empty tenv_wf_empty E) as H_m.
    destruct (run_inv_passes ipasses c0 H_ip H_m) as [ H_m' H_isem ].
    destruct (run_wt_passes fpasses _ H_fp (maintains_invs__well_typed _ _ _ _ _ H_m')) as [ H_wt H_fsem ].
    split; [ exact H_wt | ].
    intros store env. rewrite H_fsem, H_isem.
    exact (command_typechecker_preserve_sem _ _ _ _ E store env).
  Qed.

  Corollary erase_dead_field_at_sound : forall tbl fld,
      transf_sound (locals := locals)
        (fun Gstore _ c => at_letmut tbl (fun Gstore c => erase_dead_field fld Gstore Gstore c) Gstore c).
  Proof.
    intros. apply at_letmut_wt_sound. exact (erase_dead_field_sound fld).
  Qed.
End WithMap.
