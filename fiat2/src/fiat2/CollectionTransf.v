Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils fiat2.TransfUtils fiat2.TransfSound.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Definition annotate_collection (e : expr) : expr :=
  match e with
  | ESort LikeList l => ESort LikeBag (EBagOf l)
  | EFold l (EAtom (AInt 0)) v acc (EBinop OPlus (EVar v') (EVar acc')) =>
      if (negb (v =? acc) && (v =? v') && (acc =? acc'))%bool then EACFold AGSum (EBagOf l)
      else e
  | EUnop OLength l => EACFold AGCount (EBagOf l)
  | _ => e
  end.

Fixpoint bag_of (e : expr) : expr :=
  match e with
  | EFlatmap LikeList e1 x e2 => EFlatmap LikeBag (bag_of e1) x (bag_of e2)
  | EFilter LikeList e x p => EFilter LikeBag (bag_of e) x p
  | EJoin LikeList e1 e2 x y p e3 => EJoin LikeBag (bag_of e1) (bag_of e2) x y p e3
  | EProj LikeList e1 x e2 => EProj LikeBag (bag_of e1) x e2
  | EBinop OCons e1 e2 => EBinop OBagInsert (bag_of e2) e1
  | _ => EBagOf e
  end.

Definition push_down_collection (e : expr) : expr :=
  match e with
  | EBagOf e => bag_of e
  | _ => e
  end.

Definition ex : expr :=
  ESort LikeList (EFilter LikeList (ELoc "tbl") "x"
    (EBinop OEq (EAccess (EVar "x") "attr") (EAtom (AInt 0)))).
Compute fold_expr push_down_collection (fold_expr annotate_collection ex).


Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Local Notation value := (Value.value (word := word)).

  Local Coercion is_true : bool >-> Sortclass.

  Lemma bag_to_list__bag_insert : forall (v : value) (b : list (value * nat)),
    exists b1 b2,
      b1 ++ b2 = b /\
        bag_to_list (bag_insert v b) = bag_to_list b1 ++ v :: bag_to_list b2.
  Proof.
    induction b.
    1:{ do 2 exists nil; auto. }
    cbn. repeat case_match.
    1:{ exists nil. exists ((v0, n) :: b). auto. }
    1:{ lazymatch goal with
        H: value_eqb _ _ = true |- _ =>
          apply value_eqb_eq in H end. subst.
        exists nil. exists ((v0, n) :: b). auto. }
    1:{ repeat destruct_exists. exists ((v0, n) :: x). exists x0.
        cbn; intuition idtac.
        1: congruence.
        rewrite_l_to_r. rewrite app_assoc. reflexivity. }
  Qed.

  Lemma bag_to_list_app : forall (b1 b2 : list (value * nat)),
      bag_to_list b1 ++ bag_to_list b2 = bag_to_list (b1 ++ b2).
  Proof.
    induction b1; cbn; auto; intros.
    rewrite <- app_assoc. congruence.
  Qed.

  Ltac apply_value_compare_trans :=
    lazymatch goal with
      H: value_compare ?x ?y = Lt, H': value_compare ?y ?z = Lt |- _ =>
        pose proof (value_compare_trans _ _ _ H H')
    end.

  Ltac apply_value_compare_Eq_eq :=
    lazymatch goal with
      H: value_compare _ _ = Eq |- _ => apply value_compare_Eq_eq in H; subst
    end.

  Lemma bag_insert_bag_insert : forall (x y : value) b,
      StronglySorted bag_entry_leb b ->
      bag_insert x (bag_insert y b) = bag_insert y (bag_insert x b).
  Proof.
    induction b; cbn; intros.
    1:{ unfold value_ltb, value_eqb. case_match;
        repeat (rewrite value_compare_antisym; rewrite_l_to_r; cbn); auto.
        apply value_compare_Eq_eq in E; congruence. }
    1:{ unfold value_ltb, value_eqb. case_match.
        case_match; repeat (rewrite value_compare_antisym; rewrite_l_to_r; cbn);
          case_match;
          repeat apply_value_compare_Eq_eq; auto.
        all: try (cbn; unfold value_ltb, value_eqb; rewrite_l_to_r;
                  repeat (rewrite value_compare_antisym; rewrite_l_to_r; cbn);
                  rewrite value_compare_refl; auto).
        all: try (cbn; unfold value_ltb, value_eqb;
                  case_match; repeat (rewrite value_compare_antisym; rewrite_l_to_r; cbn);
                  repeat apply_value_compare_Eq_eq; auto); try congruence.
        1:{ apply_value_compare_trans; congruence. }
        1:{ rewrite value_compare_antisym, CompOpp_iff in E0; cbn in *.
            apply_value_compare_trans. clear_refl.
            repeat (rewrite value_compare_antisym; rewrite_l_to_r; cbn); auto. }
        1:{ clear_refl. rewrite_l_to_r. invert_SSorted. rewrite IHb; auto. } }
  Qed.

  Lemma list_to_bag_to_list_Permutation : forall (l : list value),
      Permutation (bag_to_list (list_to_bag l)) l.
  Proof.
    induction l; cbn; auto.
    pose proof (bag_to_list__bag_insert a (list_to_bag l)).
    repeat destruct_exists; destruct_and.
    rewrite_l_to_r.
    eapply perm_trans.
    1: eapply Permutation_sym, Permutation_middle.
    rewrite bag_to_list_app. rewrite_l_to_r.
    apply Permutation_cons; auto.
  Qed.

  Lemma Permutation_list_to_bag_eq : forall (l l' : list value),
      Permutation l l' ->
      list_to_bag l = list_to_bag l'.
  Proof.
    induction 1; cbn; auto; try congruence.
    apply bag_insert_bag_insert, list_to_bag_SSorted.
  Qed.

  Lemma lt_bag_insert : forall x (b : list (value * nat)),
      Forall (fun v => value_compare x (fst v) = Lt) b -> bag_insert x b = (x, 1) :: b.
  Proof.
    induction 1; cbn; auto.
    case_match; cbn in *. unfold value_ltb, value_leb.
    rewrite_l_to_r; auto.
  Qed.

  Lemma filter_bag_insert : forall P x (b : list (value * nat)),
      StronglySorted bag_entry_leb b ->
      filter (fun v => P (fst v)) (bag_insert x b) =
        if P x then bag_insert x (filter (fun v => P (fst v)) b)
        else filter (fun v => P (fst v)) b.
  Proof.
    induction b; cbn; intros.
    1: case_match; auto.
    case_match; cbn.
    unfold value_ltb, value_eqb. case_match.
    1:{ apply_value_compare_Eq_eq. cbn. case_match; cbn; auto.
        unfold value_ltb, value_eqb. rewrite value_compare_refl; auto. }
    1:{ do 2 case_match; cbn; unfold value_ltb, value_eqb; repeat rewrite_l_to_r; auto.
        erewrite lt_bag_insert; auto.
        eapply incl_Forall; eauto using incl_filter.
        invert_SSorted. unfold bag_entry_leb, value_leb, leb_from_compare in H3; cbn in *.
        rewrite Forall_forall; intros. apply_Forall_In.
        destruct_match_hyp; try discriminate;
          try apply_value_compare_Eq_eq; eauto using value_compare_trans. }
    1:{ invert_SSorted.
        do 2 case_match; cbn; unfold value_ltb, value_eqb; repeat rewrite_l_to_r; auto;
        rewrite IHb; auto. }
  Qed.

  Lemma filter_list_to_bag : forall P (l : list value),
      filter (fun v => P (fst v)) (list_to_bag l) = list_to_bag (filter P l).
  Proof.
    induction l; cbn; auto.
    rewrite filter_bag_insert; auto using list_to_bag_SSorted.
    rewrite IHl. case_match; auto.
  Qed.

  Section WithMap.
    Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    Theorem annotate_collection_preserve_ty : forall e Gstore Genv t,
        type_of Gstore Genv e t ->
        type_of Gstore Genv (annotate_collection e) t.
    Proof.
      destruct 1.
      all: try now (econstructor; eauto).
      1:{ cbn. case_match; try now (econstructor; eauto).
          invert_type_of_op. repeat econstructor; eauto. }
      1:{ cbn. repeat case_match; try now (econstructor; eauto).
          repeat invert_type_of_clear. invert_type_of_op.
          rewrite !Bool.andb_true_iff, Bool.negb_true_iff,
            !eqb_eq, eqb_neq in *; intuition idtac; subst.
          repeat rewrite_map_get_put_hyp.
          repeat clear_refl; do_injection.
          repeat econstructor; eauto. }
      1:{ cbn. repeat econstructor; eauto. }
    Qed.

    Lemma bag_to_list_preserve_SSorted : forall (b : list (value * nat)),
        StronglySorted bag_entry_leb b -> StronglySorted value_leb (bag_to_list b).
    Proof.
      induction b; cbn; auto using SSorted_nil.
      intros. invert_SSorted.
      induction (snd a); cbn; auto.
      constructor; auto.
      apply Forall_app; intuition idtac.
      1:{ rewrite Forall_forall; intros ? H_in.
          apply repeat_spec in H_in; subst.
          unfold value_leb, leb_from_compare. rewrite value_compare_refl; auto. }
      1:{ unfold bag_entry_leb in *. eapply incl_Forall.
          1: apply bag_to_list_incl.
          rewrite <- Forall_map_fst. assumption. }
    Qed.

    Theorem annotate_collection_preserve_sem : forall e (Gstore Genv : tenv) t (store env : locals),
        type_of Gstore Genv e t ->
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env (annotate_collection e) = interp_expr store env e.
      destruct 1; auto; intros; cbn.
      1:{ case_match; auto. cbn; case_match; auto.
          erewrite List.fold_right_change_order;
            [ | auto | apply list_to_bag_to_list_Permutation ].
          lazymatch goal with
            H: _ = VList _ |- _ => clear H
          end.
          induction l; cbn; auto.
          rewrite IHl. f_equal. rewrite Zpos_P_of_succ_nat. case_match; auto.
          destruct p; auto. }
      1:{ repeat (case_match; auto; cbn; []).
          rewrite !Bool.andb_true_iff, Bool.negb_true_iff, !eqb_eq, eqb_neq in *.
          intuition idtac; subst.
          erewrite List.fold_right_change_order;
            [
            | clear; intros; unfold apply_int_binop;
              repeat case_match; auto; rewrite Z.add_shuffle3; reflexivity
            | apply list_to_bag_to_list_Permutation ].
          lazymatch goal with
            H: _ = VList _ |- _ => clear H
          end.
          unfold get_local. induction l; cbn; auto.
          rewrite IHl. repeat rewrite_map_get_put_goal.
          congruence. }
      1:{ case_match; auto. f_equal.
          apply Permutation_SSorted_eq;
            auto using bag_to_list_preserve_SSorted, list_to_bag_SSorted, StronglySorted_value_sort.
          eapply perm_trans; [ apply list_to_bag_to_list_Permutation | apply Permuted_value_sort ]. }
    Qed.

    Theorem annotate_collection_sound : expr_transf_sound (locals:=locals) annotate_collection.
    Proof.
      unfold expr_transf_sound; intros; intuition idtac.
      1: apply annotate_collection_preserve_ty; auto.
      1: eapply annotate_collection_preserve_sem; eauto.
    Qed.

    Lemma bag_of_ty : forall e Gstore Genv t,
        type_of Gstore Genv e (TList t) ->
        type_of Gstore Genv (bag_of e) (TBag t).
    Proof.
      induction e using expr_IH; cbn; intros.
      all: try now (econstructor; eauto).
      all: case_match; invert_type_of; try invert_type_of_op;
        repeat (econstructor; eauto).
    Qed.

    Definition VBag_of (v : value) :=
      match v with
      | VList l => VBag (list_to_bag l)
      | _ => VUnit
      end.

    Lemma bag_of_sem : forall e (Gstore Genv : tenv) t,
        type_of Gstore Genv e (TList t) ->
        forall (store env : locals),
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env (bag_of e) = VBag_of (interp_expr store env e).
    Proof.
      induction 1; unfold VBag_of in *; auto; intros.
      1:{ cbn. case_match; auto; cbn. rewrite IHtype_of2; auto.
          case_match; auto. }
      1:{ cbn. rewrite IHtype_of1; auto. case_match; auto. f_equal.
          apply Permutation_list_to_bag_eq. apply Utils.Permutation_flat_map; intros;
            auto using list_to_bag_to_list_Permutation.
          apply_type_sound e1. rewrite_l_to_r. invert_type_of_value.
          eapply Permutation_in in H5; [ | apply list_to_bag_to_list_Permutation ].
          apply_Forall_In. erewrite IHtype_of2; eauto with fiat2_hints.
          apply_type_sound e2; eauto with fiat2_hints. invert_type_of_value.
          apply list_to_bag_to_list_Permutation. }
      1:{ cbn. rewrite IHtype_of1; auto. case_match; auto. f_equal.
          apply filter_list_to_bag with
            (P:=fun v : value => match interp_expr store (map.put env x v) p with
                                 | VBool b => b
                                 | _ => false
                                 end). }
      1:{ cbn. rewrite IHtype_of1, IHtype_of2; auto. repeat (case_match; auto). f_equal.
          auto using Permutation_list_to_bag_eq, Utils.Permutation_flat_map,
            list_to_bag_to_list_Permutation, Permutation_map, Permutation_filter. }
      1:{ cbn. rewrite IHtype_of1; auto. case_match; auto. f_equal.
          auto using Permutation_list_to_bag_eq, Permutation_map, list_to_bag_to_list_Permutation. }
    Qed.

    Theorem push_down_collection_preserve_ty : forall e Gstore Genv t,
        type_of Gstore Genv e t ->
        type_of Gstore Genv (push_down_collection e) t.
    Proof.
      destruct 1.
      all: try now (econstructor; eauto).
      cbn. auto using bag_of_ty.
    Qed.

    Theorem push_down_collection_preserve_sem : forall e (Gstore Genv : tenv) t (store env : locals),
        type_of Gstore Genv e t ->
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env (push_down_collection e) = interp_expr store env e.
    Proof.
      destruct 1; auto; cbn; intros.
      erewrite bag_of_sem; eauto.
    Qed.

    Theorem push_down_collection_sound : expr_transf_sound (locals:=locals) push_down_collection.
    Proof.
      unfold expr_transf_sound; intros; intuition idtac.
      1: apply push_down_collection_preserve_ty; auto.
      1: eapply push_down_collection_preserve_sem; eauto.
    Qed.
  End WithMap.
End WithWord.
