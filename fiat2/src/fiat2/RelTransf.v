Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils fiat2.TransfSound.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
From Stdlib Require Import List String ZArith Permutation.

Open Scope string_scope.

Definition swap_if_nil_head (e : expr) :=
  (* Swap potential filter constructs to facilitate swap_flatmap_if_head *)
  match e with
  | EIf p1 (EIf p2 e1 (EAtom (ANil t))) (EAtom (ANil _)) =>

      EIf p2 (EIf p1 e1 (EAtom (ANil t))) (EAtom (ANil t))
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma swap_if_nil_head_preserve_ty : forall Gstore, preserve_ty Gstore swap_if_nil_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear.
    repeat constructor; auto.
  Qed.

  Lemma swap_if_nil_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store swap_if_nil_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl. repeat (case_match; auto; []). simpl.
    repeat invert_type_of_clear.
    apply_type_sound e1; invert_type_of_value_clear.
    apply_type_sound e2_1; invert_type_of_value_clear.
    repeat case_match; reflexivity.
  Qed.

  Lemma swap_if_nil_head_sound : expr_transf_sound (locals:=locals) swap_if_nil_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply swap_if_nil_head_preserve_ty; auto.
    eapply swap_if_nil_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

Definition merge_if_head (e : expr) :=
  match e with
  | EIf p1 (EIf p2 e1 (EAtom (ANil t))) (EAtom (ANil _)) =>
      EIf (EBinop OAnd p1 p2) e1 (EAtom (ANil t))
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma merge_if_head_preserve_ty : forall Gstore, preserve_ty Gstore merge_if_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear.
    repeat econstructor; eauto.
  Qed.

  Lemma merge_if_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store merge_if_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl. repeat (case_match; auto; []). simpl.
    repeat invert_type_of_clear.
    apply_type_sound e1; invert_type_of_value_clear.
    apply_type_sound e2_1; invert_type_of_value_clear.
    cbn; destruct b, b0; reflexivity.
  Qed.

  Lemma merge_if_head_sound : expr_transf_sound (locals:=locals) merge_if_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply merge_if_head_preserve_ty; auto.
    eapply merge_if_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

Definition swap_flatmap_if_head (e : expr) :=
  (* Push potential filter construct closer to the relevant table *)
  match e with
  | EFlatmap LikeList e1 x1 (EIf p e2 (EAtom (ANil t))) =>
      if free_immut_in x1 p then e
      else EIf p (EFlatmap LikeList e1 x1 e2) (EAtom (ANil t))
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma swap_flatmap_if_head_preserve_ty : forall Gstore, preserve_ty Gstore swap_flatmap_if_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear.
    repeat econstructor; eauto using not_free_immut_put_ty.
  Qed.

  Lemma swap_flatmap_if_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store swap_flatmap_if_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl. repeat (case_match; auto; []). simpl.
    repeat invert_type_of_clear.
    apply_type_sound e1; invert_type_of_value_clear.
    lazymatch goal with
      H: VList _ = _ |- _ => clear H
    end.
    lazymatch goal with
      H: type_of _ (map.put _ _ _) _ TBool |- _ =>
        apply not_free_immut_put_ty in H
    end; trivial.
    apply_type_sound e2_1; invert_type_of_value_clear.
    case_match; f_equal; subst.
    2:{ erewrite flat_map_eq.
        2:{ rewrite Forall_forall; intros.
            rewrite <- not_free_immut_put_sem; trivial.
            repeat rewrite_r_to_l.
            repeat rewrite_l_to_r.
            instantiate (1:=fun _ => nil).
            reflexivity. }
        clear. induction l; auto. }
    apply flat_map_eq.
    rewrite Forall_forall; intros.
    rewrite <- (not_free_immut_put_sem e2_1); trivial.
    repeat rewrite_r_to_l. reflexivity.
  Qed.

  Lemma swap_flatmap_if_head_sound : expr_transf_sound (locals:=locals) swap_flatmap_if_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply swap_flatmap_if_head_preserve_ty; auto.
    eapply swap_flatmap_if_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

Definition singleton (e : expr) :=
  EBinop OCons e (EAtom (ANil None)).

Lemma flat_map__flat_map : forall A B C (f : B -> list C) (g : A -> list B) l,
    flat_map f (flat_map g l) = flat_map (fun x => flat_map f (g x)) l.
Proof.
  induction l; auto. cbn.
  rewrite flat_map_app. congruence.
Qed.

Definition if_nil_into_flatmap_head (e : expr) :=
  (* Expose filter construct *)
  match e with
  | EFlatmap LikeList e1 x (EIf p e2 (EAtom (ANil t))) =>
      EFlatmap LikeList (EFlatmap LikeList e1 x (EIf p (singleton (EVar x)) (EAtom (ANil None)))) x e2
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma if_nil_into_flatmap_head_preserve_ty : forall Gstore, preserve_ty Gstore if_nil_into_flatmap_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear.
    repeat (econstructor ; eauto with fiat2_hints).
    rewrite_map_get_put_goal. reflexivity.
  Qed.

  Lemma if_nil_into_flatmap_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store if_nil_into_flatmap_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl. repeat (case_match; auto; []). simpl.
    repeat invert_type_of_clear.
    apply_type_sound e1; invert_type_of_value_clear.
    lazymatch goal with
      _: VList _ = ?x, H': ?x = _ |- _ =>
        rewrite H' in *; clear H'
    end. do_injection; clear_refl.
    f_equal; subst.
    rewrite flat_map__flat_map.
    apply flat_map_eq.
    rewrite Forall_forall; intros.
    apply_Forall_In.
    apply_type_sound e2_1; eauto with fiat2_hints. invert_type_of_value_clear.
    unfold get_local. rewrite_map_get_put_goal.
    case_match; cbn; auto.
    rewrite app_nil_r. reflexivity.
  Qed.

  Lemma if_nil_into_flatmap_head_sound : expr_transf_sound (locals:=locals) if_nil_into_flatmap_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply if_nil_into_flatmap_head_preserve_ty; auto.
    eapply if_nil_into_flatmap_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

Definition join_to_flatmap_filter_head (e : expr) :=
  match e with
  | EJoin LikeList e1 e2 x1 x2 p e3 =>
      if free_immut_in x1 e2 then e
      else EFlatmap LikeList e1 x1
             (EFlatmap LikeList (EFilter LikeList e2 x2 p) x2
                (EBinop OCons e3 (EAtom (ANil None))))
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma join_to_flatmap_filter_head_preserve_ty : forall Gstore, preserve_ty Gstore join_to_flatmap_filter_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear.
    repeat econstructor; eauto using not_free_immut_put_ty2.
    eapply type_of__type_wf. 3: eassumption.
    1: eauto with fiat2_hints.
    repeat apply tenv_wf_step; eauto with fiat2_hints.
  Qed.

  Lemma join_to_flatmap_filter_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store join_to_flatmap_filter_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl. repeat (case_match; auto; []). simpl.
    repeat invert_type_of_clear.
    apply_type_sound e1; invert_type_of_value_clear.
    lazymatch goal with
      H: VList _ = _ |- _ => clear H
    end.
    apply_type_sound e2; invert_type_of_value_clear.
    f_equal; subst.
    apply flat_map_eq.
    rewrite Forall_forall; intros.
    rewrite <- (not_free_immut_put_sem e2); trivial.
    repeat rewrite_r_to_l. reflexivity.
  Qed.

  Lemma join_to_flatmap_filter_head_sound : expr_transf_sound (locals:=locals) join_to_flatmap_filter_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply join_to_flatmap_filter_head_preserve_ty; auto.
    eapply join_to_flatmap_filter_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

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
          repeat apply tenv_wf_step; intuition idtac;
          inversion H_wf1; inversion H_wf2; auto.
      + repeat apply locals_wf_step; auto.
        * eapply List.Forall_In in H1; eauto.
        * inversion H3; auto.
    - apply tenv_wf_step; auto. inversion H_wf1; auto.
    - rewrite Forall_forall in *; repeat apply locals_wf_step; intuition auto.
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
           apply IHl0; inversion H5; intuition idtac).
    destruct b.
    - clear E2 H8; induction l0; inversion H5; auto; simpl.
      eapply not_free_immut_put_sem in E; rewrite <- E; rewrite E3_1; simpl.
      destruct (interp_expr store (map.put (map.put env x a) y a0) e3_2) eqn:E3_2; simpl;
        try (apply IHl0; intuition idtac).
      destruct b; simpl; [f_equal |]; apply IHl0; intuition idtac.
    - clear E2 H8; induction l0; inversion H5; auto; simpl.
      eapply not_free_immut_put_sem in E; rewrite <- E; rewrite E3_1; simpl.
      destruct (interp_expr store (map.put (map.put env x a) y a0) e3_2) eqn:E3_2; simpl;
        apply IHl0; intuition idtac.
  Qed.

  Lemma filter_pushdown_head_sound : expr_transf_sound (locals:=locals) filter_pushdown_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply filter_pushdown_head_preserve_ty; auto.
    eapply filter_pushdown_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

Definition swap_conjuncts_head (e : expr) :=
  match e with
  | EBinop OAnd p1 p2 =>
      EBinop OAnd p2 p1
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma swap_conjuncts_head_preserve_ty : forall Gstore,
      preserve_ty Gstore swap_conjuncts_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear. invert_type_of_op.
    econstructor; eauto.
  Qed.

  Lemma swap_conjuncts_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store swap_conjuncts_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl. repeat (case_match; auto; []). simpl.
    invert_type_of_clear. invert_type_of_op_clear.
    apply_type_sound e1; invert_type_of_value_clear.
    apply_type_sound e2; invert_type_of_value_clear.
    cbn. rewrite Bool.andb_comm; reflexivity.
  Qed.

  Lemma swap_conjuncts_head_sound : expr_transf_sound (locals:=locals) swap_conjuncts_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply swap_conjuncts_head_preserve_ty; auto.
    eapply swap_conjuncts_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

Definition filter_pushdown_likebag_head (e : expr) :=
  match e with
  | EJoin LikeBag tbl1 tbl2 r1 r2 (EBinop OAnd p1 p) r =>
      if free_immut_in r2 p1
      then e
      else EJoin LikeBag (EFilter LikeBag tbl1 r1 p1) tbl2 r1 r2 p r
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma filter_pushdown_likebag_head_preserve_ty : forall Gstore,
      preserve_ty Gstore filter_pushdown_likebag_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear. invert_type_of_op.
    econstructor; eauto. constructor; auto.
    eapply not_free_immut_put_ty; eauto.
  Qed.

  Lemma filter_repeat_true : forall A f (v : A) n,
      f v = true -> filter f (repeat v n) = repeat v n.
  Proof.
    induction n; cbn; auto.
    intros. repeat rewrite_l_to_r.
    intuition idtac. congruence.
  Qed.

  Lemma filter_repeat_false : forall A f (v : A) n,
      f v = false -> filter f (repeat v n) = nil.
  Proof.
    induction n; cbn; auto.
    intros. repeat rewrite_l_to_r.
    intuition idtac.
  Qed.

  Lemma bag_to_list_filter_fst : forall (f : value -> bool) l,
      bag_to_list (filter (fun v => f (fst v)) l) =
        filter f (bag_to_list l).
  Proof.
    induction l; cbn; auto. destruct a; cbn.
    case_match; cbn; rewrite IHl, filter_app.
    1: rewrite filter_repeat_true; auto.
    1: rewrite filter_repeat_false; auto.
  Qed.

  Lemma filter_pushdown_likebag_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store filter_pushdown_likebag_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl.
    repeat (case_match; auto; []). simpl.
    repeat invert_type_of_clear.
    invert_type_of_op_clear.
    apply_type_sound e1; invert_type_of_value_clear.
    apply_type_sound e2; invert_type_of_value_clear.
    do 2 f_equal.
    erewrite bag_to_list_filter_fst with
      (f := fun v : value =>
              match
                interp_expr store (map.put env x v) e3_1
              with
              | VBool b => b
              | _ => false
              end).
    rewrite flat_map_filter.
    apply flat_map_eq.
    rewrite Forall_forall; intros ? H_in.
    apply bag_to_list_incl, In_fst in H_in.
    destruct_exists; intuition idtac.
    apply_Forall_In.
    lazymatch goal with
      H: type_of _ _ e3_1 _ |- _ =>
        apply not_free_immut_put_ty in H
      end; auto.
    apply_type_sound e3_1;
      eauto with fiat2_hints.
    invert_type_of_value_clear; rewrite_expr_value.
    case_match.
    1:{ f_equal. apply filter_ext_in; intros ? H_in.
    apply bag_to_list_incl, In_fst in H_in.
    destruct_exists; intuition idtac.
    apply_Forall_In.
    rewrite <- not_free_immut_put_sem with (e:=e3_1); auto.
    rewrite_expr_value; cbn.
    case_match; auto. }
    1:{ symmetry; apply List.map_nil.
        apply List.filter_nil; intros ? H_in.
    apply bag_to_list_incl, In_fst in H_in.
    destruct_exists; intuition idtac.
    apply_Forall_In.
    rewrite <- not_free_immut_put_sem with (e:=e3_1); auto.
    rewrite_expr_value; cbn.
    apply_type_sound e3_2; eauto with fiat2_hints.
    2: repeat apply tenv_wf_step; eauto with fiat2_hints.
    invert_type_of_value_clear.
    rewrite_expr_value; reflexivity. }
  Qed.

  Lemma filter_pushdown_likebag_head_sound : expr_transf_sound (locals:=locals) filter_pushdown_likebag_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply filter_pushdown_likebag_head_preserve_ty; auto.
    eapply filter_pushdown_likebag_head_preserve_sem; resolve_locals_wf; eauto.
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

Definition swap_join_likebag_head (e : expr) :=
  match e with
  | EJoin LikeBag e1 e2 x1 x2 p e3 =>
      if String.eqb x1 x2 then e
      else EJoin LikeBag e2 e1 x2 x1 p e3
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma swap_join_likebag_head_preserve_ty : forall Gstore, preserve_ty Gstore swap_join_likebag_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear.
    rewrite String.eqb_neq in *.
    econstructor; eauto.
    all: rewrite Properties.map.put_put_diff; auto.
  Qed.

  Lemma bag_insert_comm : forall (x y : value) l,
      bag_insert x (bag_insert y l) = bag_insert y (bag_insert x l).
  Proof.
    induction l; cbn; unfold value_ltb, value_eqb.
    1:{ case_match.
        all: try lazymatch goal with
                 E: _ = Eq |- _ =>
                   apply value_compare_Eq_eq in E;
                   subst;
                   rewrite value_compare_refl
               end.
        all: repeat (rewrite value_compare_antisym; rewrite_l_to_r); cbn; auto. }
    1:{ repeat case_match; cbn.
        all: repeat lazymatch goal with
                 E: _ = Eq |- _ =>
                   apply value_compare_Eq_eq in E;
                   subst
               end; trivial.
        all: unfold value_ltb, value_eqb;
          try rewrite value_compare_refl;
          repeat rewrite_l_to_r; auto.
        all: repeat (rewrite value_compare_antisym; rewrite_l_to_r); cbn; auto.
        all: case_match;
          try lazymatch goal with
              E: _ = Eq |- _ =>
                apply value_compare_Eq_eq in E;
                subst
            end;
          try rewrite value_compare_refl; auto.
        all: repeat (rewrite value_compare_antisym; rewrite_l_to_r); cbn; auto.
        all: repeat rewrite_l_to_r; try discriminate.
        all: lazymatch goal with
            H1: value_compare ?a ?b = Lt,
              H2: value_compare ?b ?c = Lt |- _ =>
              eapply (value_compare_trans _ _ _ H1) in H2
          end; rewrite_l_to_r; discriminate. }
  Qed.

  Lemma Permutation_list_to_bag_eq : forall (l l' : list value),
      Permutation l l' ->
      list_to_bag l = list_to_bag l'.
  Proof.
    induction 1; cbn; try congruence.
    apply bag_insert_comm.
  Qed.

  Lemma Permutation_flat_map_app : forall A B (f : A -> list B) g l,
      Permutation
        (flat_map (fun x => (f x ++ g x)%list) l)
        (flat_map f l ++ flat_map g l).
  Proof.
    induction l; cbn; auto.
    rewrite IHl.
    rewrite <- !app_assoc.
    apply Permutation_app_head.
    rewrite !app_assoc.
    apply Permutation_app_tail.
    apply Permutation_app_comm.
  Qed.

  Lemma Permutation_flat_map_comm : forall A B C (f : A -> B -> list C) l l',
      Permutation
        (flat_map (fun x => flat_map (fun y => f x y) l) l')
        (flat_map (fun y => flat_map (fun x => f x y) l') l).
  Proof.
    induction l; cbn.
    1: induction l'; auto.
    intros.
    rewrite Permutation_flat_map_app, IHl.
    auto.
  Qed.

  Lemma map_filter__flat_map : forall A B (f : A -> B) g l,
      map f (filter g l) = flat_map (fun x => if g x then f x :: nil else nil) l.
  Proof.
    induction l; cbn; auto.
    case_match; cbn; congruence.
  Qed.

  Lemma swap_join_likebag_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store swap_join_likebag_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl.
    repeat (case_match; auto; []). simpl.
    rewrite String.eqb_neq in *.
    repeat invert_type_of_clear.
    apply_type_sound e1; invert_type_of_value_clear.
    apply_type_sound e2; invert_type_of_value_clear.
    repeat lazymatch goal with
      H: VBag _ = _ |- _ => clear H
           end.
    f_equal.
    apply Permutation_list_to_bag_eq.
    erewrite flat_map_eq.
    (* swap the order of map.put *)
    2:{ rewrite Forall_forall; intros ? H_in.
        apply bag_to_list_incl, In_fst in H_in.
        destruct_exists. destruct_and.
        apply_Forall_In.
        erewrite filter_ext_in.
        2:{ intros ? H_in.
            apply bag_to_list_incl, In_fst in H_in.
            destruct_exists. destruct_and.
            rewrite Properties.map.put_put_diff; auto.
            reflexivity. }
        erewrite map_ext_in.
        2:{ intros.
            rewrite Properties.map.put_put_diff; auto.
            reflexivity. }
        reflexivity. }
    erewrite flat_map_eq.
    2:{  rewrite Forall_forall; intros.
         rewrite map_filter__flat_map . reflexivity. }
    erewrite flat_map_eq with (l:=bag_to_list l).
    2:{  rewrite Forall_forall; intros.
         rewrite map_filter__flat_map . reflexivity. }
    apply Permutation_flat_map_comm.
  Qed.

  Lemma swap_join_likebag_head_sound : expr_transf_sound (locals:=locals) swap_join_likebag_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply swap_join_likebag_head_preserve_ty; auto.
    eapply swap_join_likebag_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

#[export] Hint Resolve to_filter_head_sound : transf_hints.
#[export] Hint Resolve to_proj_head_sound : transf_hints.
#[export] Hint Resolve to_join_head_sound : transf_hints.
#[export] Hint Resolve filter_pushdown_head_sound : transf_hints.
#[export] Hint Resolve swap_if_nil_head_sound : transf_hints.
#[export] Hint Resolve merge_if_head_sound : transf_hints.
#[export] Hint Resolve swap_flatmap_if_head_sound : transf_hints.
#[export] Hint Resolve if_nil_into_flatmap_head_sound : transf_hints.
#[export] Hint Resolve join_to_flatmap_filter_head_sound : transf_hints.
#[export] Hint Resolve filter_pushdown_likebag_head_sound : transf_hints.
#[export] Hint Resolve swap_join_likebag_head_sound : transf_hints.
#[export] Hint Resolve swap_conjuncts_head_sound : transf_hints.
