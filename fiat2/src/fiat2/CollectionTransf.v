Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils fiat2.TransfUtils fiat2.TransfSound.
Require Import coqutil.Map.Interface.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Definition annotate_collection (e : expr) : expr :=
  match e with
  | ESort LikeList l => ESort LikeBag (EBagOf l)
  | EFold l (EAtom (AInt 0)) v acc (EBinop OPlus (EVar v') (EVar acc')) =>
      if (negb (v =? acc) && (v =? v') && (acc =? acc'))%bool then EACFold AGSum (EBagOf l)
      else e
  | EUnop OLength l => EACFold AGCount (EBagOf l)
  | EFold l (EAtom (ANone _)) v0 acc0
      (EOptMatch (EVar acc1) (EUnop OSome (EVar v1))
         x0 (EIf (EBinop OLess (EVar v2) (EVar x1)) (EUnop OSome (EVar v3)) (EVar acc2))) =>
      if (all_neqb [v0; acc0; x0] && all_eqb [(v0, [v1; v2; v3]); (acc0, [acc1; acc2]); (x0, [x1])])%bool
      then EACIFold AGMin (ESetOf l)
      else e
  | EBinop OEq e (EAtom (ANil t)) =>
      EBinop OEq (EBagOf e) (EAtom (AEmptyBag t))
  | _ => e
  end.

Fixpoint bag_of (e : expr) : expr :=
  match e with
  | EFlatmap LikeList e1 x e2 => EFlatmap LikeBag (bag_of e1) x (bag_of e2)
  | EBinop OCons e1 e2 => EBinop OBagInsert (bag_of e2) e1
  | EIf e1 e2 e3 => EIf e1 (bag_of e2) (bag_of e3)
  | EAtom (ANil t) => EAtom (AEmptyBag t)
  | _ => EBagOf e
  end.

Fixpoint set_of (e : expr) : expr :=
  match e with
  | EFlatmap LikeList e1 x e2 => EFlatmap LikeSet (set_of e1) x (set_of e2)
  | EBinop OCons e1 e2 => EBinop OSetInsert (set_of e2) e1
  | EIf e1 e2 e3 => EIf e1 (set_of e2) (set_of e3)
  | EAtom (ANil t) => EAtom (AEmptySet t)
  | _ => ESetOf e
  end.

Definition push_down_collection (e : expr) : expr :=
  match e with
  | EBagOf e => bag_of e
  | ESetOf e => set_of e
  | _ => e
  end.

Definition ex : expr :=
  ESort LikeList (EFlatmap LikeList (ELoc "tbl") "x"
    (EIf (EBinop OEq (EAccess (EVar "x") "attr") (EAtom (AInt 0)))
       (EBinop OCons (EVar "x") (EAtom (ANil None))) (EAtom (ANil None)))).
(* Compute fold_expr push_down_collection (fold_expr annotate_collection ex). *)

Definition ex1 : expr :=
  EFold (EFlatmap LikeList (ELoc "tbl") "r" (EBinop OCons (EAccess (EVar "r") "attr") (EAtom (ANil None))))
    (EAtom (ANone None)) "v" "acc"
      (EOptMatch (EVar "acc") (EUnop OSome (EVar "v"))
         "x" (EIf (EBinop OLess (EVar "v") (EVar "x")) (EUnop OSome (EVar "v")) (EVar "acc"))).
(* Compute fold_expr push_down_collection (fold_expr annotate_collection ex1). *)

Section WithWord.

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

  (* ------------------------------------------------------------------
     A bag's values are the set of the same elements.

     Read at the level of expressions, map_fst_list_to_bag says that
     OSetOfBag after EBagOf is ESetOf: the new operator does not add a way
     of building a set, it just lets an existing one start from a bag.

     No sortedness is needed, because the two insert functions agree
     structurally.  bag_insert and set_insert split on the same two tests in
     the same order; where the element is already present one bumps a count
     and the other returns the list untouched, and neither changes a key.
     ------------------------------------------------------------------ *)
  Lemma map_fst_bag_insert : forall (v : value) (b : list (value * nat)),
      List.map fst (bag_insert v b) = set_insert v (List.map fst b).
  Proof.
    induction b as [| [v' n'] b IH]; [ reflexivity | ].
    cbn [bag_insert List.map fst set_insert].
    destruct (value_ltb v v'); [ reflexivity | ].
    destruct (value_eqb v v') eqn:E_eq.
    - apply value_eqb_eq in E_eq; subst. cbn [List.map fst]. reflexivity.
    - cbn [List.map fst]. rewrite IH. reflexivity.
  Qed.

  Lemma map_fst_list_to_bag : forall (l : list value),
      List.map fst (list_to_bag l) = list_to_set l.
  Proof.
    induction l as [| v l IH]; [ reflexivity | ].
    cbn [list_to_bag list_to_set fold_right].
    rewrite map_fst_bag_insert, IH. reflexivity.
  Qed.

  (* And the bridge pays for itself: a set is canonical under reordering, which
     would otherwise want a commutation lemma for set_insert of its own. *)
  Lemma Permutation_list_to_set_eq : forall (l l' : list value),
      Permutation l l' ->
      list_to_set l = list_to_set l'.
  Proof.
    intros l l' H. rewrite <- !map_fst_list_to_bag.
    f_equal. apply Permutation_list_to_bag_eq; assumption.
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

    Lemma set_insert_incl_r : forall (a : value) l,
        incl (a :: l) (set_insert a l).
      induction l; cbn.
      1:{ constructor. destruct_In; auto.
          apply in_nil in H; intuition idtac. }
      repeat case_match.
      1: apply incl_refl.
      1:{ apply value_eqb_eq in E0; subst.
          unfold incl; intros. destruct_In; auto.
          left; reflexivity. }
      1:{ apply incl_cons_inv in IHl; intuition idtac.
          unfold incl; intros. destruct_In.
          1: right; auto.
          destruct_In.
          1: left; auto.
          1: right; auto. }
    Qed.

    Lemma list_to_set_incl_r : forall (l : list value),
        incl l (list_to_set l).
    Proof.
      induction l; cbn; auto using incl_nil_l.
      eapply incl_tran; [ apply incl_cons_step | ]; eauto.
      apply set_insert_incl_r.
    Qed.

    Lemma aci_aggr_alt : forall f l,
        Forall (fun v => type_of_value v TInt) l ->
        fold_right
          (fun v acc0 : value =>
             match acc0 with
             | VOption (Some (VInt v')) =>
                 match v with
                 | VInt v1 => VOption (Some (VInt (f v1 v')))
                 | _ => VUnit
                 end
             | VOption None => VOption (Some v)
             | _ => VUnit
             end) (VOption None) l =
          fold_right
            (fun v acc0 : value =>
               match v, acc0 with
               | VInt v1, VOption (Some (VInt v')) =>
                   VOption (Some (VInt (f v1 v')))
               | VInt v1, VOption None => VOption (Some v)
               | _, _ => VUnit
               end) (VOption None) l.
    Proof.
      intros. apply In_fold_right_ext with (P:=fun _ => True); intuition idtac.
      apply_Forall_In.
      lazymatch goal with
        H: type_of_value _ _ |- _ =>
          inversion H; subst end.
      case_match; auto.
    Qed.

    Theorem annotate_collection_preserve_ty : forall e Gstore Genv t,
        type_of Gstore Genv e t ->
        type_of Gstore Genv (annotate_collection e) t.
    Proof.
      destruct 1.
      all: try now (econstructor; eauto).
      1:{ cbn. case_match; try now (econstructor; eauto).
          invert_type_of_op. repeat econstructor; eauto. }
      1:{ cbn; repeat case_match; try now (econstructor; eauto).
          repeat invert_type_of_clear; repeat invert_type_of_op_clear.
          invert_type_of_atom; repeat (econstructor; eauto). }
      1:{ cbn; repeat case_match; try now (econstructor; eauto);
          repeat invert_type_of_clear; repeat invert_type_of_op_clear;
          rewrite !Bool.andb_true_iff, !Bool.negb_true_iff,
            !eqb_eq, !eqb_neq in *; intuition idtac; subst;
          repeat rewrite_map_get_put_hyp;
          repeat (repeat clear_refl; do_injection);
          repeat econstructor; eauto. }
      1:{ cbn. repeat econstructor; eauto. }
    Qed.

    Lemma bag_insert_not_nil : forall (v : value) l, bag_insert v l <> nil.
    Proof.
      induction l; cbn; repeat case_match; discriminate.
    Qed.

    Lemma list_to_bag_nil : forall (l : list value), list_to_bag l = [] -> l = [].
    Proof.
      induction l; auto.
      cbn. intros. apply bag_insert_not_nil in H.
      intuition fail.
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
          f_equal.
          lazymatch goal with
            |- _ = ?RHS =>
              destruct RHS eqn:E_list
          end.
          1:{ apply value_eqb_eq in E_list.
              do_injection; reflexivity. }
          1:{ apply value_eqb_neq in E_list.
          lazymatch goal with
            |- ?LHS = _ =>
              destruct LHS eqn:E_bag
          end; try congruence.
          apply value_eqb_eq in E_bag.
          do_injection.
          lazymatch goal with
            H: list_to_bag _ = nil |- _ =>
              apply list_to_bag_nil in H
          end; congruence. } }
      1:{ repeat (case_match; auto; cbn; []).
          case_match; auto; cbn; repeat (case_match; auto; cbn; []);
          rewrite !Bool.andb_true_iff, !Bool.negb_true_iff, !eqb_eq, !eqb_neq in *;
            intuition idtac; subst.
          1:{ erewrite List.fold_right_change_order;
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
          1:{ repeat invert_type_of_clear.
              repeat invert_type_of_op_clear.
              repeat rewrite_map_get_put_hyp.
              repeat (repeat clear_refl; do_injection).
            rewrite aci_aggr_alt.
              2:{ apply_type_sound e1. rewrite_l_to_r. invert_type_of_value_clear.
                  eauto using incl_Forall, list_to_set_incl. }
              erewrite fold_right_change_order_idem.

            2:{ intros. repeat case_match; auto; do 3 f_equal.
                1: rewrite !Z.min_assoc;
                rewrite (Z.min_comm z); reflexivity.
                1: apply Z.min_comm. }
            2:{ intros. repeat case_match; auto; do 3 f_equal.
                1: rewrite Z.min_assoc, Z.min_id; reflexivity.
                1: apply Z.min_id. }
            2: apply list_to_set_incl.
            2: apply list_to_set_incl_r.
              eapply In_fold_right_ext with (P:=fun _ => True); auto.
              intuition idtac; intros.
              unfold get_local. rewrite_map_get_put_goal.
              apply_type_sound e1. rewrite_l_to_r.
              invert_type_of_value_clear. apply_Forall_In.
              lazymatch goal with
                H: type_of_value _ TInt |- _ =>
                  inversion H; subst; clear H
              end.
              repeat (case_match; auto; []).
              case_match; repeat rewrite_map_get_put_goal; auto.
              repeat case_match; auto; f_equal;
                unfold Z.ltb, Z.min in *; case_match;
                rewrite ?Z.compare_eq_iff in *; congruence. } }
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
      all: try now (invert_type_of; econstructor; eauto).
      all: case_match; invert_type_of; try invert_type_of_op;
                    repeat (econstructor; eauto).
      all: (* EAtom (ANil _) *)
        invert_type_of_atom; constructor; auto.
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
      1:{ (* TyEAtom *)
          cbn. destruct a; reflexivity. }
      1:{ cbn. case_match; auto; cbn. rewrite IHtype_of2; auto.
          case_match; auto. }
      1:{ cbn. apply_type_sound e1.
          invert_type_of_value_clear.
          case_match; auto. }
      1:{ cbn. rewrite IHtype_of1; auto. case_match; auto. f_equal.
          apply Permutation_list_to_bag_eq. apply Utils.Permutation_flat_map; intros;
            auto using list_to_bag_to_list_Permutation.
          apply_type_sound e1. rewrite_l_to_r. invert_type_of_value.
          eapply Permutation_in in H5; [ | apply list_to_bag_to_list_Permutation ].
          apply_Forall_In. erewrite IHtype_of2; eauto with fiat2_hints.
          apply_type_sound e2; eauto with fiat2_hints. invert_type_of_value.
          apply list_to_bag_to_list_Permutation. }
    Qed.

    Lemma set_of_ty : forall e Gstore Genv t,
        type_of Gstore Genv e (TList t) ->
        type_of Gstore Genv (set_of e) (TSet t).
    Proof.
      induction e using expr_IH; cbn; intros.
      all: try now (econstructor; eauto).
      (* the EIf case: its branches are the lists, so the source typing has to
         be taken apart before the branches' IHs apply *)
      all: try now (invert_type_of; econstructor; eauto).
      all: case_match; invert_type_of; try invert_type_of_op;
        repeat (econstructor; eauto).
      all: (* EAtom (ANil _) *)
        invert_type_of_atom; constructor; auto.
    Qed.

    Definition VSet_of (v : value) :=
      match v with
      | VList l => VSet (list_to_set l)
      | _ => VUnit
      end.

    Lemma In_flat_map_incl : forall [A B : Type] (f : A -> list B) (a : A) l,
        In a l -> incl (f a) (flat_map f l).
    Proof.
      induction l; cbn; intuition idtac; intros.
      1:{ subst. apply incl_appl; apply incl_refl. }
      1:{ apply incl_appr; assumption. }
    Qed.

    Lemma incl_flat_map : forall [A B : Type] (f : A -> list B) [l1 l2 : list A],
        incl l1 l2 -> incl (flat_map f l1) (flat_map f l2).
    Proof.
      induction l1; cbn; auto using incl_nil_l.
      intros. apply incl_cons_inv in H; intuition idtac.
      apply incl_app; auto using In_flat_map_incl.
    Qed.

    Lemma flat_map_incl_in : forall [A B : Type] (f g : A -> list B) [l : list A],
      (forall a, In a l -> incl (f a) (g a)) ->
      incl (flat_map f l) (flat_map g l).
    Proof.
      induction l; cbn; auto using incl_refl; intros.
      apply incl_app_app; auto.
    Qed.

    Lemma flat_map_incl_in2 : forall [A B : Type] (f g : A -> list B) [l1 l2 : list A],
        incl l1 l2 ->
        (forall a, In a l2 -> incl (f a) (g a)) ->
        incl (flat_map f l1) (flat_map g l2).
    Proof.
      induction l1; cbn; auto using incl_nil_l; intros.
      apply incl_cons_inv in H; intuition idtac.
      apply incl_app; auto.
      eapply incl_tran; [ apply In_flat_map_incl | ]; eauto using flat_map_incl_in.
    Qed.

    Lemma NoDup_SSorted_double_incl_eq : forall (l1 l2 : list value),
        NoDup l1 -> NoDup l2 ->
        StronglySorted value_leb l1 ->
        StronglySorted value_leb l2 ->
        incl l1 l2 -> incl l2 l1 ->
        l1 = l2.
    Proof.
      induction l1; intros.
      1: apply incl_l_nil in H4; congruence.
      destruct l2.
      1:{ unfold incl in *.
          lazymatch goal with
            H: forall _, In _ (?a :: _) -> _ |- _ =>
              specialize (H a) end.
          cbn in *. intuition fail. }
      1:{
        repeat lazymatch goal with
        | H: NoDup (_ :: _) |- _ => inversion H; clear H
          | H: StronglySorted _ (_ :: _) |- _ => inversion H; clear H
          | H: incl (_ :: _) _ |- _ => apply incl_cons_inv in H
          end; subst.
        intuition idtac.
        assert (a = v).
        { destruct (value_eqb a v) eqn:E.
          1: apply value_eqb_eq in E; congruence.
          apply value_eqb_neq in E.
          lazymatch goal with
            H: In a (v :: _), H': In v (a :: _) |- _ =>
              inversion H; inversion H' end;
          auto. repeat apply_Forall_In.
          apply value_leb_antisym; auto. }
        f_equal; auto; subst.
        1:{ apply IHl1; auto;
            unfold incl in *; intros;
            lazymatch goal with
              H: forall _, In _ ?l1 -> In _ (_ :: ?l2),
              H': In _ ?l1 |- In _ ?l2 =>
              apply H in H' as H_in end;
            destruct (value_eqb a v) eqn:E;
            try (apply value_eqb_eq in E; subst; intuition idtac);
            inversion H_in; auto;
            apply value_eqb_neq in E; congruence. } }
    Qed.
    (* filtering a set leaves a set *)
    Lemma SSorted_filter : forall (R : value -> value -> Prop) (p : value -> bool) l,
        StronglySorted R l -> StronglySorted R (filter p l).
    Proof.
      induction l; cbn; auto; intros.
      invert_SSorted. case_match; auto.
      constructor; auto using Forall_Forall_filter.
    Qed.

    (* projecting a set commutes with adding one element to it *)
    Lemma list_to_set_map_set_insert : forall (f : value -> value) v s,
        list_to_set (List.map f (set_insert v s))
        = set_insert (f v) (list_to_set (List.map f s)).
    Proof.
      intros. apply NoDup_SSorted_double_incl_eq;
        auto using list_to_set_NoDup, list_to_set_SSorted,
                   set_insert_preserve_NoDup, set_insert_preserve_SSorted.
      - unfold incl; intros w H_in.
        apply list_to_set_incl, in_map_iff in H_in.
        destruct H_in as [u [H_eq H_u]]; subst.
        apply set_insert_incl in H_u; destruct H_u as [H_u | H_u]; subst.
        1: apply set_insert_incl_r; cbn; auto.
        apply set_insert_incl_r; cbn; right.
        apply list_to_set_incl_r, in_map; auto.
      - unfold incl; intros w H_in.
        apply set_insert_incl in H_in; destruct H_in as [H_in | H_in]; subst.
        1: apply list_to_set_incl_r, in_map, set_insert_incl_r; cbn; auto.
        apply list_to_set_incl, in_map_iff in H_in.
        destruct H_in as [u [H_eq H_u]]; subst.
        apply list_to_set_incl_r, in_map, set_insert_incl_r; cbn; auto.
    Qed.

    (* a projection of a set of rows does not care that the rows were deduplicated *)
    Lemma list_to_set_map_list_to_set : forall (f : value -> value) l,
        list_to_set (List.map f (list_to_set l)) = list_to_set (List.map f l).
    Proof.
      intros. apply NoDup_SSorted_double_incl_eq;
        auto using list_to_set_NoDup, list_to_set_SSorted.
      - unfold incl; intros w H_in.
        apply list_to_set_incl, in_map_iff in H_in.
        destruct H_in as [u [H_eq H_u]]; subst.
        apply list_to_set_incl in H_u.
        apply list_to_set_incl_r, in_map; auto.
      - unfold incl; intros w H_in.
        apply list_to_set_incl, in_map_iff in H_in.
        destruct H_in as [u [H_eq H_u]]; subst.
        apply list_to_set_incl_r, in_map, list_to_set_incl_r; auto.
    Qed.

    (* and neither does a filter of one: the same statement for filter rather
       than map, which is what a scan whose source was deduplicated needs *)
    Lemma list_to_set_filter_list_to_set : forall (p : value -> bool) l,
        list_to_set (filter p (list_to_set l)) = list_to_set (filter p l).
    Proof.
      intros. apply NoDup_SSorted_double_incl_eq;
        auto using list_to_set_NoDup, list_to_set_SSorted.
      - unfold incl; intros w H_in.
        apply list_to_set_incl, filter_In in H_in as [ H_w H_p ].
        apply list_to_set_incl in H_w.
        apply list_to_set_incl_r, filter_In; split; assumption.
      - unfold incl; intros w H_in.
        apply list_to_set_incl, filter_In in H_in as [ H_w H_p ].
        apply list_to_set_incl_r, filter_In; split;
          [ apply list_to_set_incl_r | ]; assumption.
    Qed.

    (* dropping every row whose attribute is k drops exactly k from the set *)
    Lemma filter_list_to_set_map : forall (f : value -> value) k l,
        filter (fun w => negb (value_eqb w k)) (list_to_set (List.map f l))
        = list_to_set (List.map f (filter (fun v => negb (value_eqb (f v) k)) l)).
    Proof.
      intros.
      apply NoDup_SSorted_double_incl_eq;
        auto using list_to_set_NoDup, list_to_set_SSorted,
                   NoDup_filter, SSorted_filter.
      - unfold incl; intros w H_in.
        apply filter_In in H_in; destruct H_in as [H_in H_q].
        apply list_to_set_incl, in_map_iff in H_in.
        destruct H_in as [u [H_eq H_u]]; subst.
        apply list_to_set_incl_r, in_map, filter_In; intuition auto.
      - unfold incl; intros w H_in.
        apply list_to_set_incl, in_map_iff in H_in.
        destruct H_in as [u [H_eq H_u]]; subst.
        apply filter_In in H_u; destruct H_u as [H_u H_p].
        apply filter_In; intuition auto.
        apply list_to_set_incl_r, in_map; auto.
    Qed.

    Lemma incl_filter_incl : forall [A : Type] (f : A -> bool) (l1 l2 : list A),
        incl l1 l2 ->
        incl (filter f l1) (filter f l2).
    Proof.
      induction l1; cbn; auto using incl_nil_l; intros.
      apply incl_cons_inv in H.
      case_match; intuition auto.
      apply incl_cons; auto.
      rewrite filter_In; auto.
    Qed.

    Ltac use_set_of_sem_IH :=
      lazymatch goal with
        IH: context[interp_expr _ _ (set_of ?e)] |- context[interp_expr _ _ (set_of ?e)] =>
          rewrite IH; clear IH end.

    Lemma set_of_sem : forall e (Gstore Genv : tenv) t,
        type_of Gstore Genv e (TList t) ->
        forall (store env : locals),
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env (set_of e) = VSet_of (interp_expr store env e).
    Proof.
      induction 1; unfold VSet_of in *; auto; intros.
      1:{ (* TyEAtom *)
          cbn. destruct a; reflexivity. }
      1:{ cbn. case_match; auto; cbn; use_set_of_sem_IH; auto.
          case_match; auto. }
      1:{ (* TyEIf, as in bag_of_sem: the branch taken is the same one on both
             sides, so only e1's value has to be pinned down *)
          cbn. apply_type_sound e1.
          invert_type_of_value_clear.
          case_match; auto. }
      1:{ cbn. use_set_of_sem_IH; auto.
          case_match; auto. f_equal.
          apply NoDup_SSorted_double_incl_eq; auto using list_to_set_NoDup, list_to_set_SSorted.
          1:{ eapply incl_tran; [ apply list_to_set_incl | ].
              eapply incl_tran; [ apply incl_flat_map, list_to_set_incl | ].
              eapply incl_tran; [ | apply list_to_set_incl_r ].
              apply flat_map_incl_in; intros.
              apply_type_sound e1. rewrite_l_to_r.
              invert_type_of_value_clear. apply_Forall_In.
              rewrite IHtype_of2; eauto with fiat2_hints.
              case_match; auto using incl_refl, list_to_set_incl. }
          1:{ eapply incl_tran; [ | apply list_to_set_incl_r ].
              eapply incl_tran; [ | apply incl_flat_map, list_to_set_incl_r ].
              eapply incl_tran; [ apply list_to_set_incl | ].
              apply flat_map_incl_in; intros.
              apply_type_sound e1. rewrite_l_to_r.
              invert_type_of_value_clear. apply_Forall_In.
              rewrite IHtype_of2; eauto with fiat2_hints.
              case_match; auto using incl_refl, list_to_set_incl_r. } }
    Qed.

    Theorem push_down_collection_preserve_ty : forall e Gstore Genv t,
        type_of Gstore Genv e t ->
        type_of Gstore Genv (push_down_collection e) t.
    Proof.
      destruct 1.
      all: try now (econstructor; eauto).
      all: cbn; auto using bag_of_ty, set_of_ty.
    Qed.

    Theorem push_down_collection_preserve_sem : forall e (Gstore Genv : tenv) t (store env : locals),
        type_of Gstore Genv e t ->
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env (push_down_collection e) = interp_expr store env e.
    Proof.
      destruct 1; auto; cbn; intros.
      1: erewrite bag_of_sem; eauto.
      1: erewrite set_of_sem; eauto.
    Qed.

    Theorem push_down_collection_sound : expr_transf_sound (locals:=locals) push_down_collection.
    Proof.
      unfold expr_transf_sound; intros; intuition idtac.
      1: apply push_down_collection_preserve_ty; auto.
      1: eapply push_down_collection_preserve_sem; eauto.
    Qed.
  End WithMap.
End WithWord.

#[export] Hint Resolve push_down_collection_sound : transf_hints.
#[export] Hint Resolve annotate_collection_sound : transf_hints.
