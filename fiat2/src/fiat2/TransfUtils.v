Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils fiat2.TransfSound.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Morphisms.
Import ListNotations.

Ltac apply_type_of__type_wf :=
  lazymatch goal with
  | H: type_of _ _ _ ?t |- type_wf ?t =>
      let H' := fresh "H'" in
      apply type_of__type_wf in H as H'
  | H: type_of _ _ _ (TList ?t) |- type_wf ?t =>
      let H' := fresh "H'" in
      apply type_of__type_wf in H as H'
  | H: type_of _ _ _ (TBag ?t) |- type_wf ?t =>
      let H' := fresh "H'" in
      apply type_of__type_wf in H as H'
  | H: type_of _ _ _ (TSet ?t) |- type_wf ?t =>
      let H' := fresh "H'" in
      apply type_of__type_wf in H as H'
  | H:  type_of _ _ _ (TOption ?t) |- type_wf ?t =>
      let H' := fresh "H'" in
      apply type_of__type_wf in H as H'
  | H:  type_of _ _ _ (TDict ?t _) |- type_wf ?t =>
      let H' := fresh "H'" in
      apply type_of__type_wf in H as H'
  | H:  type_of _ _ _ (TDict _ ?t) |- type_wf ?t =>
      let H' := fresh "H'" in
      apply type_of__type_wf in H as H'
  | H:  type_of _ _ _ (TRecord ?tl) |- context[?tl] =>
      let H' := fresh "H'" in
      apply type_of__type_wf in H as H'
  end.

Ltac trans_of_eq :=
  lazymatch goal with
    H: interp_expr _ _ ?e = _, H': _ = interp_expr _ _ ?e |- _ =>
      rewrite H in H'; injection H'; intros; subst end.

Ltac type_of_list_entry :=
  lazymatch goal with
  | H1: type_of _ _ ?e _, _: interp_expr _ _ ?e = _ ?l,
        _: In ?x ?l |- type_of_value ?x _ =>
      eapply type_sound in H1; eauto; inversion H1; subst;
      trans_of_eq;
      apply_Forall_In
  end.

Ltac type_of_bag_entry :=
  lazymatch goal with
    H: type_of _ _ ?e (TBag _), _: interp_expr _ _ ?e = VBag ?l,
        _: In ?a (bag_to_list ?l) |- type_of_value ?a _ =>
      apply_type_sound e; invert_type_of_value; rewrite_l_to_r;
      Forall_fst__Forall_bag_to_list; do_injection; apply_Forall_In
  end.

Section fold_expr.
  Context (f : expr -> expr).
  Fixpoint fold_expr (e : expr) :=
    f
      match e with
      | EVar _ | ELoc _ | EAtom _ => e
      | EUnop o e => EUnop o (fold_expr e)
      | EBinop o e1 e2 => EBinop o (fold_expr e1) (fold_expr e2)
      | ETernop o e1 e2 e3 => ETernop o (fold_expr e1) (fold_expr e2) (fold_expr e3)
      | EIf e1 e2 e3 => EIf (fold_expr e1) (fold_expr e2) (fold_expr e3)
      | ELet e1 x e2 => ELet (fold_expr e1) x (fold_expr e2)
      | EFlatmap tag e1 x e2 => EFlatmap tag (fold_expr e1) x (fold_expr e2)
      | EFold e1 e2 x y e3 => EFold (fold_expr e1) (fold_expr e2) x y (fold_expr e3)
      | EACFold ag e => EACFold ag (fold_expr e)
      | EACIFold ag e => EACIFold ag (fold_expr e)
      | ERecord l => ERecord (List.map (fun '(s, e) => (s, fold_expr e)) l)
      | EAccess e x => EAccess (fold_expr e) x
      | EOptMatch e e_none x e_some => EOptMatch (fold_expr e) (fold_expr e_none) x (fold_expr e_some)
      | ESort tag l => ESort tag (fold_expr l)
      end.
End fold_expr.

Lemma fold_expr_id : forall e, fold_expr id e = e.
Proof.
  induction e using expr_IH; cbn [fold_expr]; rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; try reflexivity.
  change (id (ERecord ?l')) with (ERecord l'). f_equal.
  induction l as [ | [ s e ] l IHl ]; [ reflexivity | ].
  inversion H; subst. cbn in *. f_equal; [ congruence | auto ].
Qed.

Section WithMap.
  Notation value := (value).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Ltac apply_fold_expr_preserve_ty_IH :=
    lazymatch goal with
    | IH: context[type_of _ _ (fold_expr _ ?e) _] |- type_of _ _ (fold_expr _ ?e) _ =>
        apply IH; auto
    end.

  Lemma fold_expr_preserve_ty : forall Gstore f,
      preserve_ty Gstore f -> preserve_ty Gstore (fold_expr f).
  Proof.
    unfold preserve_ty. intros * H * ? ? ?.
    generalize dependent Genv; generalize dependent t. induction e using expr_IH;
      intros; simpl; auto;
      apply H; invert_type_of_clear; subst; try econstructor; eauto.
    all: try apply_fold_expr_preserve_ty_IH; repeat apply tenv_wf_step; auto;
      try now (apply_type_of__type_wf; eauto; try invert_type_wf; auto).
    1: apply type_of__type_wf in H10; auto.
    1: rewrite fst_map_fst; auto.
    1:{ lazymatch goal with H1: NoDup _, H2: Permutation _ _,
            H3: List.map fst _ = _ |- _ =>
                              clear H1 H2 H3 end.
        generalize dependent tl. induction l; auto. intros.
        destruct tl; invert_Forall2; try discriminate. simpl in *.
        constructor.
        2: apply IHl; invert_Forall; intuition auto.
        invert_Forall. destruct a; simpl in *. apply H5; auto. }
  Qed.

  Ltac apply_fold_expr_preserve_sem_IH :=
    multimatch goal with
    | IH: context[interp_expr _ _ (fold_expr _ ?e)],
        _: type_of _ ?G ?e _ |- context[interp_expr _ _ (fold_expr _ ?e)] =>
        erewrite IH with (Genv:=G); eauto
    end.

  Lemma fold_expr_preserve_sem : forall Gstore (store : locals) f,
      preserve_ty Gstore f ->
      preserve_sem Gstore store f -> preserve_sem Gstore store (fold_expr f).
  Proof.
    unfold preserve_sem; intros * ? H_sem. induction e using expr_IH; simpl; auto; intros.
    1-3: erewrite H_sem; eauto.
    all: invert_type_of_clear.
    all: try now (erewrite H_sem; eauto;
                  [ simpl; repeat apply_fold_expr_preserve_sem_IH
                  | econstructor; eauto; apply fold_expr_preserve_ty ];
                  eauto with fiat2_hints).
    1:{ erewrite H_sem; eauto.
        2: econstructor; eauto; apply fold_expr_preserve_ty; eauto with fiat2_hints.
        simpl; apply_fold_expr_preserve_sem_IH. case_match; auto.
        f_equal. apply In_flat_map_ext; intros.
        apply_fold_expr_preserve_sem_IH; eauto with fiat2_hints.
        apply locals_wf_step; auto; type_of_list_entry. }
    1:{ erewrite H_sem; eauto.
        2: econstructor; eauto; apply fold_expr_preserve_ty; eauto with fiat2_hints.
        simpl; apply_fold_expr_preserve_sem_IH. case_match; auto.
        do 2 f_equal. apply In_flat_map_ext; intros.
        apply_fold_expr_preserve_sem_IH; eauto with fiat2_hints.
        apply locals_wf_step; auto.
        type_of_bag_entry. }
    1:{ erewrite H_sem; eauto.
        2: econstructor; eauto; apply fold_expr_preserve_ty; eauto with fiat2_hints.
        simpl; apply_fold_expr_preserve_sem_IH. case_match; auto.
        do 2 f_equal. apply In_flat_map_ext; intros.
        apply_fold_expr_preserve_sem_IH; eauto with fiat2_hints.
        apply locals_wf_step; auto.
        type_of_list_entry. }
    1:{ erewrite H_sem; eauto.
        2: econstructor; eauto; apply fold_expr_preserve_ty; eauto;
        repeat apply tenv_wf_step; eauto with fiat2_hints.
        simpl; apply_fold_expr_preserve_sem_IH. case_match; auto.
        apply_fold_expr_preserve_sem_IH.
        eapply In_fold_right_ext with (P:=fun a => type_of_value a t); intros.
        1: eapply type_sound; eauto.
        apply_type_sound e1; rewrite_l_to_r; invert_type_of_value.
        apply_Forall_In; intuition;
          [ apply_fold_expr_preserve_sem_IH | eapply type_sound; resolve_locals_wf; eauto ];
          repeat apply tenv_wf_step; repeat apply locals_wf_step;
          eauto with fiat2_hints.
        apply fold_expr_preserve_ty; repeat apply tenv_wf_step; eauto with fiat2_hints. }
    1:{ erewrite H_sem with (t:=TRecord tl'); eauto.
        2:{ econstructor; eauto.
            1: rewrite fst_map_fst; auto.
            1: lazymatch goal with
               | H1: Permutation _ _, H2: NoDup _, H3: List.map fst _ = _ |- _ =>
                   clear H1 H2 H3
               end. generalize dependent tl. induction l; simpl; auto; intros.
            destruct tl; simpl in *; invert_Forall2.
            constructor. 2: apply IHl; invert_Forall; intuition.
            case_match; simpl in *.
            apply fold_expr_preserve_ty; auto. }
        simpl. do 2 f_equal.
        lazymatch goal with
        | H1: Permutation _ _, H2: NoDup _, H3: List.map fst _ = _ |- _ =>
            clear H1 H2 H3
        end. generalize dependent tl; induction l; simpl; auto; intros.
        destruct tl; invert_Forall2.
        invert_Forall; case_match; simpl in *.
        f_equal. 2: eapply IHl; eauto.
        f_equal; eauto. }
    1:{ erewrite H_sem; eauto.
        2: econstructor; eapply fold_expr_preserve_ty; eauto with fiat2_hints.
        simpl. apply_fold_expr_preserve_sem_IH. repeat case_match; auto.
        all: apply_fold_expr_preserve_sem_IH; eauto with fiat2_hints.
        apply locals_wf_step; eauto. eapply type_sound in H10; eauto. inversion H10; subst.
        all: trans_of_eq; congruence. }
  Qed.

  Lemma fold_expr_sound : forall f,
      expr_transf_sound (locals:=locals) f ->
      expr_transf_sound (locals:=locals) (fold_expr f).
  Proof.
    unfold expr_transf_sound; intuition idtac.
    1:{ apply fold_expr_preserve_ty; auto.
        unfold preserve_ty; intros; apply H; auto. }
    1:{ eapply fold_expr_preserve_sem; resolve_locals_wf; eauto.
        all: unfold preserve_ty, preserve_sem; intros.
        all: apply H in H7; intuition auto. }
  Qed.
End WithMap.

Section fold_command.
  Context (f : command -> command).
  Context (g : expr -> expr).

  Fixpoint fold_command (c : command) : command :=
    f
      match c with
      | CSkip => CSkip
      | CSeq c1 c2 => CSeq (fold_command c1) (fold_command c2)
      | CLet e x c => CLet (fold_expr g e) x (fold_command c)
      | CLetMut e x ot invs c => CLetMut (fold_expr g e) x ot invs (fold_command c)
      | CAssign x e => CAssign x (fold_expr g e)
      | CIf e c1 c2 => CIf (fold_expr g e) (fold_command c1) (fold_command c2)
      | CForeach e x c => CForeach (fold_expr g e) x (fold_command c)
      end.
End fold_command.

Section WithMap.
  Notation value := (value).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Lemma fold_command_id_preserve_ty : forall f,
      (forall Gstore, preserve_ty Gstore f) ->
      forall c Gstore Genv,
      tenv_wf Gstore -> tenv_wf Genv ->
      well_typed Gstore Genv c -> well_typed Gstore Genv (fold_command id f c).
  Proof.
    induction c; simpl; auto; intros.
    all: invert_well_typed.
    all: econstructor; eauto with fiat2_hints;
      try apply fold_expr_preserve_ty; auto.
  Qed.

  Ltac use_fold_command_id_preserve_sem_IH Gstore' :=
    lazymatch goal with
      IH: context[interp_command _ _ (fold_command id _ ?c) = _] |-
        context[interp_command _ _ (fold_command id _ ?c)] =>
        erewrite IH with (Gstore:=Gstore')
    end.

  Lemma fold_command_id_preserve_sem : forall f,
      (forall Gstore, preserve_ty Gstore f) ->
      (forall Gstore (store : locals), preserve_sem Gstore store f) ->
      forall c (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv ->
      well_typed Gstore Genv c ->
      locals_wf Gstore store -> locals_wf Genv env ->
      interp_command store env (fold_command id f c) = interp_command store env c.
  Proof.
    induction c; simpl; auto; intros.
    all: invert_well_typed.
    1:{ repeat use_fold_command_id_preserve_sem_IH Gstore; eauto.
        eapply command_type_sound; eauto. }
    1:{ use_fold_command_id_preserve_sem_IH Gstore.
        4: eauto. all: eauto with fiat2_hints.
        2:{ apply locals_wf_step; auto. eapply type_sound with (Gstore:=Gstore); eauto.
            apply fold_expr_preserve_ty; auto. }
        erewrite fold_expr_preserve_sem with (Gstore:=Gstore); eauto. }
    1:{ use_fold_command_id_preserve_sem_IH (map.put Gstore x t).
        all: eauto with fiat2_hints.
        2:{ apply locals_wf_step; auto. eapply type_sound with (Gstore:=Gstore); eauto.
            apply fold_expr_preserve_ty; auto. }
        f_equal. erewrite fold_expr_preserve_sem with (Gstore:=Gstore); eauto. }
    1:{ f_equal. erewrite fold_expr_preserve_sem with (Gstore:=Gstore); eauto. }
    1:{ erewrite fold_expr_preserve_sem with (Gstore:=Gstore); eauto.
        repeat case_match; auto.
        all: use_fold_command_id_preserve_sem_IH Gstore; eauto. }
    1:{ erewrite fold_expr_preserve_sem with (Gstore:=Gstore); eauto.
        repeat case_match; auto.
        apply_type_sound e; rewrite_l_to_r.
        invert_type_of_value.
        repeat lazymatch goal with H: context[VList] |- _ => clear H end.
        generalize dependent store.
        induction l; simpl in *; auto; intros. invert_Forall.
        rewrite IHl; auto.
        2: eapply command_type_sound; resolve_locals_wf; eauto with fiat2_hints.
        2: apply fold_command_id_preserve_ty; eauto with fiat2_hints.
        f_equal. use_fold_command_id_preserve_sem_IH Gstore. 4: eauto.
        all: eauto with fiat2_hints. }
  Qed.

  Lemma fold_expr_sem_eq : forall f (Gstore Genv : tenv) e t (store env : locals),
      type_of Gstore Genv e t ->
      (forall (Gstore : tenv), preserve_ty Gstore f) ->
      (forall (Gstore : tenv) (store : locals), preserve_sem Gstore store f) ->
      tenv_wf Gstore -> tenv_wf Genv ->
      locals_wf Gstore store -> locals_wf Genv env ->
      interp_expr store env (fold_expr f e) = interp_expr store env e.
  Proof.
    intros * H_t H_ty H_sem ? ? ? ?.
    eapply (fold_expr_preserve_sem Gstore store f (H_ty Gstore) (H_sem Gstore store));
      eassumption.
  Qed.

  Lemma fold_command_id_sound : forall f,
      expr_transf_sound (locals:=locals) f ->
      transf_sound (locals:=locals) (fun _ _ => fold_command id f).
  Proof.
    unfold expr_transf_sound, transf_sound; intros; split.
    1:{ apply fold_command_id_preserve_ty; auto.
        unfold preserve_ty; intros.
        lazymatch goal with
          H: context[_ -> _ /\ _], H': type_of _ _ _ _ |- _ =>
            apply H in H' end; intuition idtac. }
    1:{ intros. erewrite fold_command_id_preserve_sem;
        resolve_locals_wf; eauto;
        unfold preserve_ty, preserve_sem; intros;
        lazymatch goal with
              H: context[_ -> _ /\ _], H': type_of _ _ _ _ |- _ =>
                apply H in H' end; intuition auto. }
  Qed.
End WithMap.

Section fold_command_with_global.
  (* Useful for whole-program to-index transformation *)
  Context (f : command -> command).
  Context (g : expr -> expr).
  Context (h : invariant -> invariant).
  Fixpoint fold_command_with_global (c : command) : command :=
    f
      match c with
      | CSkip => CSkip
      | CSeq c1 c2 => CSeq (fold_command_with_global c1) (fold_command_with_global c2)
      | CLet e x c => CLet (fold_expr g e) x (fold_command_with_global c)
      | CLetMut e x ot invs c => CLetMut (fold_expr g e) x ot (List.map h invs) (fold_command_with_global c)
      | CAssign x e => CAssign x (fold_expr g e)
      | CIf e c1 c2 =>
          CIf (fold_expr g e) (fold_command_with_global c1) (fold_command_with_global c2)
      | CForeach e x c =>
          CForeach (fold_expr g e) x (fold_command_with_global c)
      end.
End fold_command_with_global.

#[export] Hint Resolve fold_command_id_sound : transf_hints.

Section WithMap.
  Notation value := (value).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Definition singleton_rel x (y y' : string) :=
    y = x /\ y' = x.

  Lemma singleton_rel_refl : forall (s : string),
      singleton_rel s s s.
  Proof.
    unfold singleton_rel; intuition auto.
  Qed.

  Definition sem_eq (Gstore Genv : tenv) (t : type) (e1 e2 : expr) :=
    type_of Gstore Genv e1 t /\ type_of Gstore Genv e2 t /\
      forall (store env : locals),
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env e1 = interp_expr store env e2.

  Lemma sem_eq_sym  (Gstore Genv : tenv) (t : type) : forall e1 e2,
      sem_eq Gstore Genv t e1 e2 -> sem_eq Gstore Genv t e2 e1.
  Proof.
    unfold sem_eq; intros. intuition auto. symmetry. auto.
  Qed.

  Lemma sem_eq_trans  (Gstore Genv : tenv) (t : type) : forall e1 e2 e3,
      sem_eq Gstore Genv t e1 e2 ->
      sem_eq Gstore Genv t e2 e3 ->
      sem_eq Gstore Genv t e1 e3.
  Proof.
    unfold sem_eq; intros. intuition auto.
    rewrite H4, H5; auto.
  Qed.

  Lemma sem_eq_eq : forall Gstore Genv t e1 e2,
      sem_eq Gstore Genv t e1 e2 ->
      forall store env : locals,
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env e1 = interp_expr store env e2.
  Proof.
    unfold sem_eq; intros; intuition auto.
  Qed.

  Lemma sem_eq_refl : forall Gstore Genv t e, type_of Gstore Genv e t -> sem_eq Gstore Genv t e e.
  Proof.
    unfold sem_eq; intuition auto.
  Qed.
End WithMap.
