Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils fiat2.TransfSound fiat2.CollectionTransf.
Require Import coqutil.Map.Interface.
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

(* The two conjuncts of a TWO-SIDED RANGE on one attribute: a lower bound and
   an upper bound, on the same attribute of the same row.  This is exactly the
   first shape range_bounds (DictIndexImpl.v) matches, and it matches it
   WHOLE.

   Splitting such a conjunction is the one case where splitting can only
   lose.  There is nothing to expose -- both halves are bounds on the same
   attribute, and the rule that serves them wants them together -- while the
   split leaves the outer half a ONE-SIDED range and demotes the inner half to
   a residual filter, so the read goes from [lo, hi) to [lo, inf) and a test.
   Measured in eval/Kafka_WindowStore: fetchAll lost its upper bound to a
   split it had no use for, demanded by a DIFFERENT read of the same table.

   Selector.v's conj_evidence already declines to ASK for SplitIf on a bare
   range pair, for this reason.  That is not enough, and the gap is what this
   guard closes: SplitIf is one whole-program rewrite, so a table with two
   range readers turns it on for one of them and it then reaches the other. *)
Definition is_two_sided_range (p1 p2 : expr) : bool :=
  match p1, p2 with
  | EUnop ONot (EBinop OLess (EAccess (EVar x1) a1) _),
    EBinop OLess (EAccess (EVar x2) a2) _ =>
      (String.eqb x1 x2 && String.eqb a1 a2)%bool
  | _, _ => false
  end.

Definition split_if_head (e : expr) :=
  match e with
  | EIf (EBinop OAnd p1 p2) e1 (EAtom (ANil t)) =>
      if is_two_sided_range p1 p2 then e
      else EIf p1 (EIf p2 e1 (EAtom (ANil t))) (EAtom (ANil t))
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma split_if_head_preserve_ty : forall Gstore, preserve_ty Gstore split_if_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear. invert_type_of_op_clear.
    repeat econstructor; eauto.
  Qed.

  Lemma split_if_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store split_if_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl. repeat (case_match; auto; []). simpl.
    repeat invert_type_of_clear. invert_type_of_op_clear.
    (* the guard's own case_match means the outer condition is no longer
       destructed for us, so both conditions are reduced to booleans here *)
    apply_type_sound e1_1; invert_type_of_value_clear.
    apply_type_sound e1_2; invert_type_of_value_clear.
    cbn; destruct b, b0; reflexivity.
  Qed.

  Lemma split_if_head_sound : expr_transf_sound (locals:=locals) split_if_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply split_if_head_preserve_ty; auto.
    eapply split_if_head_preserve_sem; resolve_locals_wf; eauto.
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

(* Whether e is [x] *)
Definition is_singleton_of (x : string) (e : expr) : bool :=
  match e with
  | EBinop OCons (EVar y) (EAtom (ANil _)) => String.eqb x y
  | _ => false
  end.

Definition if_nil_into_flatmap_head (e : expr) :=
  (* Expose filter construct; a flatmap that already is a filter is left alone,
     since splitting it would only add an identity flatmap around the filter *)
  match e with
  | EFlatmap LikeList e1 x (EIf p e2 (EAtom (ANil t))) =>
      if is_singleton_of x e2 then e
      else EFlatmap LikeList (EFlatmap LikeList e1 x (EIf p (singleton (EVar x)) (EAtom (ANil None)))) x e2
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
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
    destruct (interp_expr store env e1) eqn:E_e1; auto.
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

Definition flatmap_assoc_head (e : expr) :=
  (* [y <- [x <- e1, e2], e3] --> [x <- e1, y <- e2, e3], where x is not free in e3 *)
  match e with
  | EFlatmap LikeList (EFlatmap LikeList e1 x e2) y e3 =>
      if free_immut_in x e3 then e
      else EFlatmap LikeList e1 x (EFlatmap LikeList e2 y e3)
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  (* Binding x around e does not change e's type when x is not free in e *)
  Lemma not_free_immut_put_put_ty : forall x y e (Gstore Genv : tenv) tx ty t,
      free_immut_in x e = false ->
      type_of Gstore (map.put Genv y ty) e t ->
      type_of Gstore (map.put (map.put Genv x tx) y ty) e t.
  Proof.
    intros. destruct (String.eqb x y) eqn:E.
    - rewrite String.eqb_eq in E; subst.
      rewrite Properties.map.put_put_same; assumption.
    - rewrite String.eqb_neq in E.
      rewrite Properties.map.put_put_diff_comm; auto.
      apply not_free_immut_put_ty2; assumption.
  Qed.

  (* Binding x around e does not change e's value when x is not free in e *)
  Lemma not_free_immut_put_put_sem : forall x y e (store env : locals) vx vy,
      free_immut_in x e = false ->
      interp_expr store (map.put (map.put env x vx) y vy) e = interp_expr store (map.put env y vy) e.
  Proof.
    intros. destruct (String.eqb x y) eqn:E.
    - rewrite String.eqb_eq in E; subst.
      rewrite Properties.map.put_put_same; reflexivity.
    - rewrite String.eqb_neq in E.
      rewrite Properties.map.put_put_diff_comm; auto.
      symmetry. apply not_free_immut_put_sem; assumption.
  Qed.

  Lemma flatmap_assoc_head_preserve_ty : forall Gstore, preserve_ty Gstore flatmap_assoc_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    repeat invert_type_of_clear.
    repeat econstructor; eauto using not_free_immut_put_put_ty.
  Qed.

  Lemma flatmap_assoc_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store flatmap_assoc_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl. repeat (case_match; auto; []).
    repeat invert_type_of_clear.
    cbn [interp_expr].
    apply_type_sound e1_1; invert_type_of_value_clear.
    f_equal. rewrite flat_map__flat_map.
    apply flat_map_eq. rewrite Forall_forall; intros v H_in.
    apply_Forall_In.
    apply_type_sound2 e1_2;
      try (apply tenv_wf_step; eauto with fiat2_hints);
      try (apply locals_wf_step; auto).
    invert_type_of_value_clear. try rewrite_expr_value.
    apply flat_map_eq. rewrite Forall_forall; intros.
    rewrite not_free_immut_put_put_sem; auto.
  Qed.

  Lemma flatmap_assoc_head_sound : expr_transf_sound (locals:=locals) flatmap_assoc_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply flatmap_assoc_head_preserve_ty; auto.
    eapply flatmap_assoc_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

Definition flatmap_singleton_head (e : expr) :=
  (* [x <- [e1], e2] --> let x = e1 in e2 *)
  match e with
  | EFlatmap LikeList (EBinop OCons e1 (EAtom (ANil _))) x e2 => ELet e1 x e2
  | _ => e
  end.

Definition flatmap_identity_head (e : expr) :=
  (* [x <- e1, ret x] --> e1 *)
  match e with
  | EFlatmap LikeList e1 x (EBinop OCons (EVar y) (EAtom (ANil _))) =>
      if String.eqb x y then e1 else e
  | _ => e
  end.

Lemma flat_map_singleton_id : forall A (l : list A),
    flat_map (fun v => v :: nil) l = l.
Proof.
  induction l; cbn; congruence.
Qed.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma flatmap_singleton_head_preserve_ty : forall Gstore, preserve_ty Gstore flatmap_singleton_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat invert_type_of_clear. repeat invert_type_of_op_clear.
    econstructor; eauto.
  Qed.

  Lemma flatmap_singleton_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store flatmap_singleton_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl.
    repeat invert_type_of_clear. repeat invert_type_of_op_clear.
    apply_type_sound2 e2;
      try (apply tenv_wf_step; eauto with fiat2_hints);
      try (apply locals_wf_step; auto; eapply type_sound; eauto).
    invert_type_of_value_clear.
    try rewrite_expr_value. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma flatmap_singleton_head_sound : expr_transf_sound (locals:=locals) flatmap_singleton_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply flatmap_singleton_head_preserve_ty; auto.
    eapply flatmap_singleton_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.

  Lemma flatmap_identity_head_preserve_ty : forall Gstore, preserve_ty Gstore flatmap_identity_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    rewrite String.eqb_eq in *; subst.
    repeat invert_type_of_clear. repeat invert_type_of_op_clear.
    repeat rewrite_map_get_put_hyp. repeat do_injection. assumption.
  Qed.

  Lemma flatmap_identity_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store flatmap_identity_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl. repeat (case_match; auto; []).
    rewrite String.eqb_eq in *; subst.
    repeat invert_type_of_clear.
    apply_type_sound e1; invert_type_of_value_clear.
    cbn [interp_expr interp_binop interp_atom]. try rewrite_expr_value.
    unfold get_local. f_equal.
    erewrite flat_map_ext; [ symmetry; apply flat_map_singleton_id | ].
    intros. rewrite map.get_put_same. reflexivity.
  Qed.

  Lemma flatmap_identity_head_sound : expr_transf_sound (locals:=locals) flatmap_identity_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply flatmap_identity_head_preserve_ty; auto.
    eapply flatmap_identity_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

Definition flatmap_if_head (e : expr) :=
  (* [x <- (if p then e1 else []), e2] --> if p then [x <- e1, e2] else [] *)
  match e with
  | EFlatmap LikeList (EIf p e1 (EAtom (ANil _))) x e2 =>
      EIf p (EFlatmap LikeList e1 x e2) (EAtom (ANil None))
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma flatmap_if_head_preserve_ty : forall Gstore, preserve_ty Gstore flatmap_if_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat invert_type_of_clear.
    repeat (econstructor; eauto).
    (* the type of the new empty list is well-formed because it is e2's element type *)
    lazymatch goal with
      H: type_of _ (map.put _ _ _) _ (TList ?t2) |- type_wf ?t2 =>
        apply type_of__type_wf in H
    end; auto.
    1: invert_type_wf; assumption.
    apply tenv_wf_step; auto.
    lazymatch goal with
      H: type_of _ _ _ (TList ?t1) |- type_wf ?t1 =>
        apply type_of__type_wf in H
    end; auto.
    invert_type_wf; assumption.
  Qed.

  Lemma flatmap_if_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store flatmap_if_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl.
    destruct (interp_expr store env e1_1); auto.
    destruct b; reflexivity.
  Qed.

  Lemma flatmap_if_head_sound : expr_transf_sound (locals:=locals) flatmap_if_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply flatmap_if_head_preserve_ty; auto.
    eapply flatmap_if_head_preserve_sem; resolve_locals_wf; eauto.
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

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

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

End WithMap.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

End WithMap.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

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

End WithMap.

Definition swap_flatmap_likebag_head (e : expr) :=
  (* Under bag semantics, the order of two independent nested iterations does not matter:
     [x <- e1, y <- e2, e3] --> [y <- e2, x <- e1, e3]
     when x and y differ, x is not free in e2 and y is not free in e1 *)
  match e with
  | EFlatmap LikeBag e1 x (EFlatmap LikeBag e2 y e3) =>
      if (String.eqb x y || free_immut_in x e2 || free_immut_in y e1)%bool then e
      else EFlatmap LikeBag e2 y (EFlatmap LikeBag e1 x e3)
  | _ => e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma swap_flatmap_likebag_head_preserve_ty : forall Gstore, preserve_ty Gstore swap_flatmap_likebag_head.
  Proof.
    unfold preserve_ty. intros Gstore e t Genv H_Gstore H_Genv H.
    repeat destruct_subexpr.
    simpl. repeat (case_match; auto).
    rewrite !Bool.orb_false_iff, String.eqb_neq in *; intuition idtac.
    repeat invert_type_of_clear.
    repeat econstructor.
    - eapply not_free_immut_put_ty; eauto.
    - apply not_free_immut_put_ty2; eauto.
    - rewrite Properties.map.put_put_diff_comm; auto.
  Qed.

  Lemma swap_flatmap_likebag_head_preserve_sem : forall Gstore (store : locals),
      preserve_sem Gstore store swap_flatmap_likebag_head.
  Proof.
    unfold preserve_sem. intros Gstore store e t Genv env H_Gstore H_Genv H H_str H_env.
    repeat destruct_subexpr. simpl.
    repeat (case_match; auto; []).
    rewrite !Bool.orb_false_iff, String.eqb_neq in *; intuition idtac.
    repeat invert_type_of_clear.
    cbn [interp_expr].
    lazymatch goal with
      H: type_of _ (map.put _ _ _) e2_1 _ |- _ =>
        apply not_free_immut_put_ty in H; auto
    end.
    apply_type_sound e1; invert_type_of_value_clear.
    apply_type_sound e2_1; invert_type_of_value_clear.
    repeat rewrite_expr_value.
    f_equal. apply Permutation_list_to_bag_eq.
    (* each table is the same in every iteration of the other loop *)
    erewrite In_flat_map_ext with (l := bag_to_list l0);
      [ | intros w _; rewrite <- (not_free_immut_put_sem e1 x0); [ rewrite <- H; reflexivity | assumption ] ].
    erewrite In_flat_map_ext with (l := bag_to_list l);
      [ | intros v _; rewrite <- (not_free_immut_put_sem e2_1 x); [ rewrite <- H0; reflexivity | assumption ] ].
    cbn beta iota.
    (* drop the conversions of the inner results to bags and back *)
    eapply perm_trans;
      [ eapply Utils.Permutation_flat_map;
        [ intros; apply list_to_bag_to_list_Permutation | apply Permutation_refl ] | ].
    eapply perm_trans;
      [ | apply Permutation_sym; eapply Utils.Permutation_flat_map;
          [ intros; apply list_to_bag_to_list_Permutation | apply Permutation_refl ] ].
    (* bind the two variables in the same order on both sides, then swap the loops *)
    erewrite In_flat_map_ext with (l := bag_to_list l0);
      [ | intros w _; apply In_flat_map_ext; intros v _;
          rewrite Properties.map.put_put_diff_comm; [ reflexivity | congruence ] ].
    apply Permutation_flat_map_comm.
  Qed.

  Lemma swap_flatmap_likebag_head_sound : expr_transf_sound (locals:=locals) swap_flatmap_likebag_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply swap_flatmap_likebag_head_preserve_ty; auto.
    eapply swap_flatmap_likebag_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

#[export] Hint Resolve swap_if_nil_head_sound : transf_hints.
#[export] Hint Resolve merge_if_head_sound : transf_hints.
#[export] Hint Resolve swap_flatmap_if_head_sound : transf_hints.
#[export] Hint Resolve if_nil_into_flatmap_head_sound : transf_hints.
#[export] Hint Resolve swap_conjuncts_head_sound : transf_hints.
#[export] Hint Resolve split_if_head_sound : transf_hints.
#[export] Hint Resolve flatmap_assoc_head_sound : transf_hints.
#[export] Hint Resolve flatmap_singleton_head_sound : transf_hints.
#[export] Hint Resolve flatmap_identity_head_sound : transf_hints.
#[export] Hint Resolve flatmap_if_head_sound : transf_hints.
#[export] Hint Resolve swap_flatmap_likebag_head_sound : transf_hints.
