Require Import conquord.Language conquord.Interpret conquord.Value conquord.TypeSystem conquord.TypeSound conquord.Utils conquord.TransfSound.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import List String ZArith Permutation.

Open Scope string_scope.

Definition to_filter_head (e : expr) :=
  match e with
  | EFlatmap LikeList e' x
      (EIf p (EBinop OCons (EVar y) (EAtom (ANil _))) (EAtom (ANil _))) =>
      if String.eqb x y then EFilter LikeList e' x p else e
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma to_filter_head_preserve_ty : forall Gstore, preserve_ty Gstore to_filter_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    rewrite eqb_eq in *; subst. repeat invert_type_of_clear.
    invert_type_of_op. rewrite_map_get_put_hyp. do_injection.
    constructor; auto.
  Qed.

  Lemma to_filter_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store to_filter_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl. repeat (case_match; auto; []). simpl.
    case_match; auto. f_equal.
    rewrite eqb_eq in *; subst.
    lazymatch goal with
      H: _ = VList _ |- _ => clear H
    end. induction l; auto.
    simpl. repeat (case_match; auto).
    unfold get_local. rewrite map.get_put_same. simpl. f_equal. auto.
  Qed.

  Lemma to_filter_head_sound : expr_transf_sound (locals:=locals) to_filter_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply to_filter_head_preserve_ty; auto.
    eapply to_filter_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

Definition to_join_head (e : expr) :=
  match e with
  | EFlatmap LikeList tbl1 x
      (EFlatmap LikeList tbl2 y
         (EIf p (EBinop OCons r (EAtom (ANil _))) (EAtom (ANil _)))) =>
      if ((x =? y) || free_immut_in x tbl2)%bool
      then e
      else EJoin LikeList tbl1 tbl2 x y p r
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma to_join_head_preserve_ty : forall Gstore, preserve_ty Gstore to_join_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear. invert_type_of_op.
    econstructor; eauto.
    rewrite Bool.orb_false_iff in *.
    eapply not_free_immut_put_ty; eauto. intuition idtac.
  Qed.

  Lemma to_join_head_preserve_sem' : forall (store env: locals) (Gstore Genv: tenv) (tbl1 tbl2 p r : expr) (x y : string) (t1 t2 t3 : type) (t t' : option type),
      tenv_wf Gstore -> tenv_wf Genv ->
      type_of Gstore Genv tbl1 (TList t1) ->
      type_of Gstore (map.put Genv x t1) tbl2 (TList t2) ->
      free_immut_in x tbl2 = false ->
      type_of Gstore (map.put (map.put Genv x t1) y t2) p TBool ->
      locals_wf Gstore store ->
      locals_wf Genv env ->
      interp_expr store env (EFlatmap LikeList tbl1 x
                               (EFlatmap LikeList tbl2 y
                                  (EIf p (EBinop OCons r (EAtom (ANil t))) (EAtom (ANil t'))))) =
        interp_expr store env (EJoin LikeList tbl1 tbl2 x y p r).
  Proof.
    intros store env Gstore Genv tbl1 tbl2 p r x y t1 t2 t3 t t' H_Gstore H_Genv H_tbl1 H_tbl2 H_free H_p H_str H_env.
    simpl. apply type_of__type_wf in H_tbl1 as H_wf1; auto. apply type_of__type_wf in H_tbl2 as H_wf2; auto;
      [| apply tenv_wf_step; inversion H_wf1]; auto.
    eapply type_sound in H_tbl1; eauto. inversion H_tbl1; subst.
    f_equal. apply not_free_immut_put_ty in H_tbl2 as H_tbl2'; auto.
    eapply type_sound in H_tbl2'; eauto. inversion H_tbl2'; subst.
    f_equal. apply flat_map_eq. rewrite Forall_forall. intros v H_v.
    eapply type_sound with (env := (map.put env x v)) in H_tbl2; eauto.
    - inversion H_tbl2; subst.
      rewrite <- not_free_immut_put_sem in H2; auto. rewrite <- H2 in H0.
      injection H0; intros; subst.
      subst. clear H0 H2. induction l1; auto. simpl.
      eapply type_sound in H_p; eauto.
      + inversion H_p; subst. rewrite <- H2. destruct b; simpl; [f_equal |];
          inversion H3; inversion H5; apply IHl1; auto.
      + rewrite Forall_forall in *; repeat apply locals_wf_step;
          repeat apply tenv_wf_step; intuition;
          inversion H_wf1; inversion H_wf2; auto.
      + repeat apply locals_wf_step; auto.
        * eapply List.Forall_In in H1; eauto.
        * inversion H3; auto.
    - apply tenv_wf_step; auto. inversion H_wf1; auto.
    - rewrite Forall_forall in *; repeat apply locals_wf_step; intuition.
  Qed.

  Lemma to_join_head_preserve_sem : forall Gstore (store : locals), preserve_sem Gstore store to_join_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
      repeat destruct_subexpr.
      unfold to_join_head. repeat (case_match; auto).
      repeat invert_type_of_clear. invert_type_of_op.
      rewrite Bool.orb_false_iff in *.
      erewrite to_join_head_preserve_sem' with (Gstore := Gstore); eauto; intuition idtac.
  Qed.

  Lemma to_join_head_sound : expr_transf_sound (locals:=locals) to_join_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply to_join_head_preserve_ty; auto.
    eapply to_join_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

Definition filter_pushdown_head (e : expr) :=
  match e with
  | EJoin LikeList tbl1 tbl2 r1 r2 (EBinop OAnd p1 p) r =>
      if free_immut_in r2 p1
      then e
      else EJoin LikeList (EFilter LikeList tbl1 r1 p1) tbl2 r1 r2 p r
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma filter_pushdown_head_preserve_ty : forall Gstore,
      preserve_ty Gstore filter_pushdown_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear. invert_type_of_op.
    econstructor; eauto. constructor; auto.
    eapply not_free_immut_put_ty; eauto.
  Qed.

  Lemma filter_pushdown_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store filter_pushdown_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    destruct e; auto. destruct tag; auto. destruct e3; auto. destruct o; auto.
    unfold filter_pushdown_head. destruct (free_immut_in y e3_1) eqn:E; auto.
    simpl. destruct (interp_expr store env e1) eqn:E1; auto.
    destruct (interp_expr store env e2) eqn:E2; auto. f_equal.
    inversion H; subst.
    eapply type_sound in H7, H8; eauto. rewrite E1 in H7. rewrite E2 in H8.
    inversion H7; inversion H8; subst.
    rewrite flat_map_filter. apply In_flat_map_ext; intros.
    destruct (interp_expr store (map.put env x a) e3_1) eqn:E3_1;
      try (clear E2 H8; induction l0; auto; simpl;
           eapply not_free_immut_put_sem in E; rewrite <- E; rewrite E3_1; simpl;
           apply IHl0; inversion H5; intuition).
    destruct b.
    - clear E2 H8; induction l0; inversion H5; auto; simpl.
      eapply not_free_immut_put_sem in E; rewrite <- E; rewrite E3_1; simpl.
      destruct (interp_expr store (map.put (map.put env x a) y a0) e3_2) eqn:E3_2; simpl;
        try (apply IHl0; intuition).
      destruct b; simpl; [f_equal |]; apply IHl0; intuition.
    - clear E2 H8; induction l0; inversion H5; auto; simpl.
      eapply not_free_immut_put_sem in E; rewrite <- E; rewrite E3_1; simpl.
      destruct (interp_expr store (map.put (map.put env x a) y a0) e3_2) eqn:E3_2; simpl;
        apply IHl0; intuition.
  Qed.

  Lemma filter_pushdown_head_sound : expr_transf_sound (locals:=locals) filter_pushdown_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply filter_pushdown_head_preserve_ty; auto.
    eapply filter_pushdown_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

Definition to_proj_head (e : expr) :=
  match e with
  | EFlatmap LikeList e x
      (EBinop OCons e' (EAtom (ANil _))) =>
      EProj LikeList e x e'
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma to_proj_head_preserve_ty : forall Gstore, preserve_ty Gstore to_proj_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear.
    invert_type_of_op.
    econstructor; eauto.
  Qed.

  Lemma to_proj_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store to_proj_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl.
    case_match; auto.
  Qed.

  Lemma to_proj_head_sound : expr_transf_sound (locals:=locals) to_proj_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply to_proj_head_preserve_ty; auto.
    eapply to_proj_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

#[export] Hint Resolve to_filter_head_sound : transf_hints.
#[export] Hint Resolve to_proj_head_sound : transf_hints.
#[export] Hint Resolve to_join_head_sound : transf_hints.
#[export] Hint Resolve filter_pushdown_head_sound : transf_hints.
