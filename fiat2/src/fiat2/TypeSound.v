Require Import fiat2.Value fiat2.Language fiat2.Interpret fiat2.TypeSystem.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.
Require Import ZArith String List Sorted Permutation.

Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.

  Section WithMap.
    Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
    Local Notation value := (Value.value (word := word)).
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    Local Coercion is_true : bool >-> Sortclass.

    Definition tenv_wf (G : tenv) := forall x t, map.get G x = Some t -> type_wf t.

    Lemma tenv_wf_step : forall G t, tenv_wf G -> type_wf t -> forall x, tenv_wf (map.put G x t).
    Proof.
      unfold tenv_wf; intros. destruct (String.eqb x x0) eqn:E.
      - rewrite eqb_eq in *; subst. rewrite map.get_put_same in *.
        injection H1; intro; subst; auto.
      - rewrite eqb_neq in *. rewrite map.get_put_diff in *; eauto.
    Qed.

    Lemma type_of__type_wf : forall Gstore Genv e t,
        tenv_wf Gstore ->
        tenv_wf Genv ->
        type_of Gstore Genv e t ->
        type_wf t.
    Proof.
      intros Gstore Genv e t H_store H_env H. induction H using @type_of_IH; eauto.
      - inversion H; constructor; auto.
      - inversion H; constructor; auto.
      - inversion H; repeat constructor; auto.
      - auto using tenv_wf_step.
      - apply IHtype_of2. apply tenv_wf_step; auto.
        apply IHtype_of1 in H_env as H_wf1. inversion H_wf1; auto.
      - constructor; auto.
        + apply Permutation_map with (f := fst) in H2. eapply Permutation_NoDup; eauto.
        + apply Permutation_map with (f := snd), Permutation_sym in H2.
          rewrite Forall_forall; intros t H_in. eapply Permutation_in in H_in; eauto.
          remember (List.map snd tl) as tl2. revert H_env H1 H_in; clear; intros.
          induction H1; try apply in_nil in H_in; intuition.
          inversion H_in; subst; auto.
      - apply IHtype_of in H_env as H_wf. inversion H_wf; subst.
        eapply Forall_access_record; eauto.
      - constructor; auto.
      - apply IHtype_of1 in H_env as H_wf1. inversion H_wf1; constructor; auto.
      - constructor; apply IHtype_of4. repeat apply tenv_wf_step; auto.
        + apply IHtype_of1 in H_env as H_wf1. inversion H_wf1; auto.
        + apply IHtype_of2 in H_env as H_wf2. inversion H_wf2; auto.
      - constructor; apply IHtype_of2, tenv_wf_step; auto.
        apply IHtype_of1 in H_env as H_wf1. inversion H_wf1; auto.
    Qed.

    Inductive type_of_value : value -> type -> Prop :=
    | TyVWord w : type_of_value (VWord w) TWord
    | TyVInt n : type_of_value (VInt n) TInt
    | TyVBool b : type_of_value (VBool b) TBool
    | TyVString s : type_of_value (VString s) TString
    | TyVOptionNone t : type_of_value (VOption None) (TOption t)
    | TyVOptionSome v t : type_of_value v t ->
                          type_of_value (VOption (Some v)) (TOption t)
    | TyVList l t : Forall (fun v => type_of_value v t) l -> type_of_value (VList l) (TList t)
    | TyVRecord l tl : NoDup (List.map fst tl) -> StronglySorted record_entry_leb tl ->
                       Forall2 (fun p tp => fst p = fst tp /\ type_of_value (snd p) (snd tp)) l tl ->
                       type_of_value (VRecord l) (TRecord tl)
    | TyVDict l tk tv : type_wf tk -> type_wf tv ->
                        Forall (fun p => type_of_value (fst p) tk /\ type_of_value (snd p) tv) l ->
                        NoDup (List.map fst l) -> StronglySorted dict_entry_leb l ->
                        type_of_value (VDict l) (TDict tk tv)
    | TyVUnit : type_of_value VUnit TUnit.

    Definition locals_wf (G : tenv) (E : locals) :=
      forall x t, map.get G x = Some t ->
                  match map.get E x with
                  | Some v => type_of_value v t
                  | _ => False
                  end.

    Lemma locals_wf_step : forall G E,
        locals_wf G E ->
        forall x t v,
          type_of_value v t ->
          locals_wf (map.put G x t) (map.put E x v).
    Proof.
      unfold locals_wf; intros.
      destruct (String.eqb x0 x) eqn:E_x.
      - rewrite String.eqb_eq in E_x. rewrite E_x in *.
        rewrite map.get_put_same. rewrite map.get_put_same in H1. congruence.
      - rewrite String.eqb_neq in E_x. rewrite map.get_put_diff; auto.
        rewrite map.get_put_diff in H1; auto. apply H. auto.
    Qed.

    Ltac destruct_match :=
      lazymatch goal with
      | H : (if type_eqb ?x ?y then _ else _) = _ |- _ =>
          let E := fresh "E" in
          destruct (type_eqb x y) eqn:E; try discriminate; apply type_eqb_eq in E; subst; simpl in *
      | H: (match ?x with _ => _ end) = Success _ |- _ =>
          let E := fresh "E" in
          destruct x eqn:E; try discriminate; simpl in *
      end.

    Ltac destruct_compare_types :=
      unfold compare_types in *; destruct_match; constructor.

    Ltac invert_type_wf :=
      lazymatch goal with
      | H: type_wf (TList ?t) |- type_wf ?t => inversion H; clear H; subst
      | H: type_wf (TOption ?t) |- type_wf ?t => inversion H; clear H; subst
      | H: type_wf (TDict ?t _) |- type_wf ?t => inversion H; clear H; subst
      | H: type_wf (TDict _ ?t) |- type_wf ?t => inversion H; clear H; subst
      | H: type_wf (TRecord ?tl) |- Forall type_wf (List.map snd ?tl) => inversion H; clear H; subst
      end.

  Ltac invert_result :=
    lazymatch goal with
    | H: Success _ = Success _ |- _ => inversion H; clear H; intros; subst
    end.

  Ltac invert_pair :=
    lazymatch goal with
    | H: (_, _) = (_, _) |- _ => inversion H; clear H; intros; subst
    end.

  Lemma atom_typechecker_sound : forall a t a',
      (synthesize_atom a = Success (t, a') -> type_of_atom a t) /\
        (analyze_atom t a = Success a' -> type_wf t -> type_of_atom a t).
  Proof.
    destruct a; split; simpl; intro.
    all: try (invert_result; constructor).
    all: try destruct_compare_types.
    1, 3: repeat destruct_match; invert_result; constructor; apply type_wf_comp_sound; auto.
    1, 2: repeat destruct_match;
    [ destruct_compare_types; invert_result; invert_type_wf; auto
    | invert_result; constructor; invert_type_wf; auto ].
  Qed.

  Lemma fst_map_fst : forall (A B C : Type) (l : list (A * B)) (f : A -> B -> C),
      List.map fst (List.map (fun '(a, b) => (a, f a b)) l) = List.map fst l.
  Proof.
    induction l; auto.
    intros. destruct a. simpl. f_equal. auto.
  Qed.

  Lemma record_type_from'_sound : forall l tl el (Gstore Genv : tenv),
       Forall
         (fun p : string * expr =>
            forall (Gstore0 Genv0 : tenv) (t : type) (e' : expr),
              tenv_wf Gstore0 ->
              tenv_wf Genv0 ->
              (synthesize_expr Gstore0 Genv0 (snd p) = Success (t, e') -> type_of Gstore0 Genv0 (snd p) t) /\
                (analyze_expr Gstore0 Genv0 t (snd p) = Success e' -> type_wf t -> type_of Gstore0 Genv0 (snd p) t)) l ->
       tenv_wf Gstore ->
       tenv_wf Genv ->
       record_type_from' (map (fun '(s, e') => (s, synthesize_expr Gstore Genv e')) l) = Success (tl, el) ->
       map fst l = map fst tl /\ Forall2 (type_of Gstore Genv) (map snd l) (map snd tl) /\ NoDup (map fst l).
  Proof.
    induction l; intros.
    - simpl in *. invert_result. intuition. apply NoDup_nil.
    - simpl in *. repeat destruct_match. invert_result. destruct a. inversion E; subst; simpl.
      inversion H; subst. apply (IHl _ _ _ _ H6) in E2; auto. intuition.
      + f_equal. auto.
      + constructor; auto. apply H5 in H4; auto.
      + constructor; auto. apply inb_false_iff. erewrite <- fst_map_fst. apply E4.
  Qed.

  Lemma NoDup_In_get_attr_type : forall tl,  NoDup (List.map fst tl) -> forall s t, In (s, t) tl -> get_attr_type tl s = t.
  Proof.
    clear. induction tl; simpl; intros.
    - intuition.
    - destruct a. unfold get_attr_type; simpl. destruct (String.eqb s s0) eqn:E.
      + intuition; try congruence. rewrite String.eqb_eq in E; inversion H; subst.
        assert (In s0 (List.map fst tl)).
        { clear H H3 H4 IHtl. induction tl; auto. destruct a; inversion H1; subst; simpl.
          - left; congruence.
          - right; auto. }
        intuition.
      + inversion H; subst. apply IHtl; auto. destruct H0; auto.
        rewrite String.eqb_neq in E; inversion H0; congruence.
  Qed.

  Lemma Permutation_NoDup_In_get_attr_type : forall tl tl',
      Permutation tl tl' -> NoDup (List.map fst tl') ->
      forall s, In s (List.map fst tl') -> get_attr_type tl s = get_attr_type tl' s.
  Proof.
    intros.
    assert (exists t, In (s, t) tl').
    { clear H H0. induction tl'; simpl in *; intuition.
      - exists (snd a). left; subst. apply surjective_pairing.
      - destruct H0 as [t Ht]. firstorder. }
    assert (NoDup (List.map fst tl)).
    { apply Permutation_map with (f := fst) in H. apply Permutation_sym in H.
      eapply Permutation_NoDup; eauto. }
    destruct H2 as [t Ht]. repeat rewrite NoDup_In_get_attr_type with (t := t); auto.
    apply Permutation_sym in H. eapply Permutation_in; eauto.
  Qed.

  Lemma In_fst : forall A B x (l : list (A * B)), In x (List.map fst l) -> exists p, In p l /\ fst p = x.
  Proof.
    induction l; simpl; intros; intuition.
    - exists a. intuition.
    - destruct H as [p H]; exists p; intuition.
  Qed.

  Lemma record_from'_sound :
    forall l tl' el Gstore Genv,
      Forall
        (fun p : string * expr =>
           forall (Gstore Genv : tenv) (t : type) (e' : expr),
             tenv_wf Gstore ->
             tenv_wf Genv ->
             (synthesize_expr Gstore Genv (snd p) = Success (t, e') -> type_of Gstore Genv (snd p) t) /\
               (analyze_expr Gstore Genv t (snd p) = Success e' -> type_wf t -> type_of Gstore Genv (snd p) t)) l ->
      tenv_wf Gstore ->
      tenv_wf Genv ->
      type_wf (TRecord tl') ->
      incl (List.map fst l) (List.map fst tl') ->
      record_from' (List.map (fun '(s, e) => (s, analyze_expr Gstore Genv (get_attr_type tl' s) e)) l) = Success el ->
      let tl := List.map (fun '(s, _) => (s, get_attr_type tl' s)) l in
      List.map fst l = List.map fst tl /\ Forall2 (type_of Gstore Genv) (List.map snd l) (List.map snd tl) /\ NoDup (List.map fst l).
  Proof.
    induction l; intros tl' el Gstore Genv H H_Gstore H_Genv H_wf H_incl H_rec.
    - simpl in *. invert_result. intuition. apply NoDup_nil.
    - simpl in *. repeat destruct_match. destruct a. inversion H; inversion E; subst.
      invert_result. simpl in *. intuition.
      + f_equal. rewrite fst_map_fst. auto.
      + constructor.
        * eapply H2; eauto. inversion H_wf; subst.
          unfold incl in *. simpl in *. assert (In s (List.map fst tl')). { intuition. }
          apply In_fst in H0 as [p H0]. intuition. destruct p; simpl in *; subst.
          eapply NoDup_In_get_attr_type in H1; eauto.
          apply in_map with (f := snd) in H7.
          eapply List.Forall_In in H5; eauto. subst; auto.
        * eapply IHl; eauto. unfold incl in *; intuition.
      + rewrite fst_map_fst in E2. apply inb_false_iff in E2. apply NoDup_cons; auto.
        eapply IHl with (Gstore := Gstore); eauto.
        unfold incl in *; intuition.
  Qed.

  Lemma In_Permuted : forall A (x : A) l', In x l' -> exists l, Permutation (x :: l) l'.
  Proof.
    clear. induction l'; intros.
    - apply in_nil in H; intuition.
    - inversion H.
      + exists l'; subst; auto.
      + apply IHl' in H0 as [l Hl]. exists (a :: l). eapply perm_trans; try apply perm_swap.
        constructor; assumption.
  Qed.

  Lemma Permutation_incl : forall A (l l' : list A), Permutation l l' -> incl l l'.
  Proof.
    intros. unfold incl; intros.
    eapply Permutation_in; eauto.
  Qed.

  Lemma double_incl_NoDup_Permuted : forall (l : list (string * expr)) (tl' : list (string * type)),
      inclb String.eqb (List.map fst l) (List.map fst tl') = true ->
      inclb String.eqb (List.map fst tl') (List.map fst l) = true ->
      NoDup (List.map fst l) ->
      length (List.map fst tl') <= length (List.map fst l) ->
      Permutation (List.map (fun '(s, _) => (s, get_attr_type tl' s)) l) tl'.
  Proof.
    intros.
    assert (NoDup (List.map fst tl')).
    { apply inclb_correct in H, H0. eapply NoDup_incl_NoDup; eauto. }
    generalize dependent tl'. induction l; simpl; intros.
    - destruct tl'; simpl in *; intuition; discriminate.
    - destruct a; simpl in *. remember (s, get_attr_type tl' s) as p.
      rewrite Bool.andb_true_iff in H; destruct H. rewrite inb_true_iff in H.
      assert (forall s, In s (List.map fst tl') -> In (s, get_attr_type tl' s) tl').
      { clear; induction tl'; simpl; intros.
        - auto.
        - destruct a; simpl in *. destruct (String.eqb s0 s) eqn:E.
          + rewrite String.eqb_eq in E; subst.
            unfold get_attr_type, access_record. rewrite eqb_refl; auto.
          + rewrite String.eqb_neq in E. right. apply not_eq_sym in E as E'. rewrite <- eqb_neq in E'.
            unfold get_attr_type, access_record. rewrite E'. apply IHtl'. intuition. }
      apply H5, In_Permuted in H. destruct H as [tl Htl].
      eapply Permutation_trans; [| apply Htl].
      subst; apply perm_skip.
      assert (forall (l : list (string * expr)) tl tl' s t,
                 incl (List.map fst l) (List.map fst tl') ->
                 Permutation ((s, t) :: tl) tl' ->
                 ~ In s (List.map fst l) -> NoDup (List.map fst tl') ->
                 List.map (fun '(s, _) => (s, get_attr_type tl' s)) l = List.map (fun '(s, _) => (s, get_attr_type tl s)) l).
      { generalize dependent width; generalize dependent tenv; clear; intros. induction l; simpl; intros; auto.
        destruct a; simpl in *. f_equal.
        - rewrite <- Permutation_NoDup_In_get_attr_type with (tl := (s,t) :: tl) (tl' := tl'); auto.
          + simpl. destruct (String.eqb s s0) eqn:E.
            * exfalso; apply H1; left; symmetry; apply String.eqb_eq; auto.
            * unfold get_attr_type. simpl. rewrite eqb_sym, E. auto.
          + intuition.
        - eapply IHl; eauto. apply incl_cons_inv in H. intuition. }
      erewrite H; eauto.
      + apply IHl.
        * inversion H1. auto.
        * apply Permutation_sym in Htl. apply inclb_complete. apply inclb_correct in H4. auto.
          apply Permutation_map with (f := fst) in Htl. apply Permutation_incl in Htl. unfold incl; intros.
          apply H4 in H6 as H8. apply Htl in H8. inversion H8; auto. simpl in *; subst. inversion H1; intuition.
        * apply inclb_complete. apply inclb_correct in H0.
          apply Permutation_map with (f := fst) in Htl. apply Permutation_sym in Htl. apply (Permutation_NoDup Htl) in H3.
          apply Permutation_sym in Htl. apply Permutation_incl in Htl.
          unfold incl; intros. simpl in *. apply incl_cons_inv in Htl. apply Htl in H6 as H8. apply H0 in H8. inversion H8; auto.
          subst. inversion H3; intuition.
        * apply Permutation_map with (f := fst) in Htl; apply Permutation_length in Htl. simpl in Htl.
          rewrite <- Htl in H2. apply le_S_n in H2. auto.
        * apply Permutation_map with (f := fst) in Htl. apply Permutation_sym in Htl. apply (Permutation_NoDup Htl) in H3.
          simpl in *. inversion H3; intuition.
      + apply inclb_correct; auto.
      + inversion H1; auto.
  Qed.

  Lemma access_record_sound : forall A l s (a : A), access_record l s = Success a -> In (s, a) l.
  Proof.
    induction l; simpl in *; try discriminate. intros.
    destruct a. destruct_match; auto.
    rewrite String.eqb_eq in E. invert_result. auto.
  Qed.

  Lemma first_success_exists_l : forall Gstore Genv t l,
      first_success (List.map (fun '(k, _) => synthesize_expr Gstore Genv k) l) = Success t ->
      exists (p : expr * expr) e, In p l /\ synthesize_expr Gstore Genv (fst p) = Success (t, e).
  Proof.
    induction l; simpl; intros; try discriminate.
    destruct a as [k v]. destruct_match.
    - destruct a; invert_result; subst. eauto.
    - apply IHl in H as [p [e H]]. exists p; exists e. intuition.
  Qed.

  Lemma first_success_exists_r : forall Gstore Genv t l,
      first_success (List.map (fun '(_, v) => synthesize_expr Gstore Genv v) l) = Success t ->
      exists (p : expr * expr) e, In p l /\ synthesize_expr Gstore Genv (snd p) = Success (t, e).
  Proof.
    induction l; simpl; intros; try discriminate.
    destruct a as [k v]. destruct_match.
    - destruct a; invert_result; subst. eauto.
    - apply IHl in H as [p [e H]]. exists p; exists e. intuition.
  Qed.

  Lemma dict_from'_sound : forall l,
      Forall (fun p =>
                (forall (Gstore Genv : tenv) (t : type) (e' : expr),
                    tenv_wf Gstore ->
                    tenv_wf Genv ->
                    (synthesize_expr Gstore Genv (fst p) = Success (t, e') -> type_of Gstore Genv (fst p) t) /\
                      (analyze_expr Gstore Genv t (fst p) = Success e' -> type_wf t -> type_of Gstore Genv (fst p) t)) /\
                  (forall (Gstore Genv : tenv) (t : type) (e' : expr),
                      tenv_wf Gstore ->
                      tenv_wf Genv ->
                      (synthesize_expr Gstore Genv (snd p) = Success (t, e') -> type_of Gstore Genv (snd p) t) /\
                        (analyze_expr Gstore Genv t (snd p) = Success e' -> type_wf t  -> type_of Gstore Genv (snd p) t))) l ->
      forall Gstore Genv kt vt l',
        tenv_wf Gstore -> tenv_wf Genv ->
        type_wf kt -> type_wf vt ->
        dict_from' (List.map (fun '(k, v) => k' <- analyze_expr Gstore Genv kt k;; v' <- analyze_expr Gstore Genv vt v;; Success (k', v')) l) = Success l' -> Forall (fun p => type_of Gstore Genv (fst p) kt /\ type_of Gstore Genv (snd p) vt) l.
  Proof.
   Proof.
      induction l; simpl; intros.
      - apply Forall_nil.
      - repeat destruct_match. invert_result. inversion H; subst; simpl in *.
        constructor.
        + split; simpl.
          * apply H6 in E3; auto.
          * apply H6 in E4; auto.
        + eapply IHl; eauto.
   Qed.

  Lemma analyze_dict_body_sound : forall l,
      Forall (fun p =>
                (forall (Gstore Genv : tenv) (t : type) (e' : expr),
                    tenv_wf Gstore ->
                    tenv_wf Genv ->
                    (synthesize_expr Gstore Genv (fst p) = Success (t, e') -> type_of Gstore Genv (fst p) t) /\
                      (analyze_expr Gstore Genv t (fst p) = Success e' -> type_wf t -> type_of Gstore Genv (fst p) t)) /\
                  (forall (Gstore Genv : tenv) (t : type) (e' : expr),
                      tenv_wf Gstore ->
                      tenv_wf Genv ->
                      (synthesize_expr Gstore Genv (snd p) = Success (t, e') -> type_of Gstore Genv (snd p) t) /\
                        (analyze_expr Gstore Genv t (snd p) = Success e' -> type_wf t -> type_of Gstore Genv (snd p) t))) l ->
      forall Gstore Genv kt vt e',
        tenv_wf Gstore -> tenv_wf Genv ->
        type_wf kt -> type_wf vt ->
        analyze_dict_body analyze_expr Gstore Genv kt vt l = Success e' -> Forall (fun p => type_of Gstore Genv (fst p) kt /\ type_of Gstore Genv (snd p) vt) l.
  Proof.
      unfold analyze_dict_body, dict_from. intros.
      destruct_match. invert_result.
      eapply dict_from'_sound; eauto.
    Qed.

  Ltac unfold_typechecker :=
    lazymatch goal with
    | H: synthesize_expr _ _ _ = Success _ |- _ => unfold synthesize_expr in H
    | H: analyze_expr _ _ _ _ = Success _ |- _ => unfold analyze_expr in H
    end.

  Ltac unfold_fold_typechecker := repeat unfold_typechecker; fold synthesize_expr in *; fold analyze_expr in *.

  Ltac apply_type_of__type_wf :=
    lazymatch goal with
    | H: type_of _ _ _ ?t |- type_wf ?t =>
        let H' := fresh "H'" in
        apply type_of__type_wf in H as H'
    | H: type_of _ _ _ (TList ?t) |- type_wf ?t =>
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

  Ltac apply_typechecker_IH :=
    lazymatch goal with
    | IH: (forall _ _ _ _, _ -> _ -> (synthesize_expr _ _ ?e = _ -> _) /\ _),
        H: synthesize_expr _ _ ?e = Success _ |- context[?e] => eapply IH in H; eauto
    | IH: (forall _ _ _ _, _ -> _ -> _ /\ (analyze_expr _ _ _ ?e = _ -> _)),
        H: analyze_expr _ _ _ ?e = Success _ |- context[?e] => eapply IH in H; eauto
    | IH: (forall _ _ _ _, _ -> _ -> (synthesize_expr _ _ ?e = _ -> _) /\ _),
        H: synthesize_expr _ _ ?e = Success (?t, _) |- context[?t] => eapply IH in H; eauto
    | IH: (forall _ _ _ _, _ -> _ -> _ /\ (analyze_expr _ _ _ ?e = _ -> _)),
        H: analyze_expr _ _ ?t ?e = Success _ |- context[?t] => eapply IH in H; eauto
    end.

(*  Set Ltac Profiling. *)
    Lemma typechecker_sound : forall e Gstore Genv t e',
        tenv_wf Gstore -> tenv_wf Genv ->
        (synthesize_expr Gstore Genv e = Success (t, e') -> type_of Gstore Genv e t) /\
          (analyze_expr Gstore Genv t e = Success e' -> type_wf t -> type_of Gstore Genv e t).
    Proof.
      induction e using expr_IH; intros.
      - (* EVar *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; invert_result; constructor; easy.
      - (* ELoc *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; invert_result; constructor; easy.
      - (* EAtom *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; constructor;
          invert_result; apply atom_typechecker_sound in E; auto.
      - (* EUnop *)
        split; intros; destruct o; simpl in *;
          unfold_fold_typechecker; repeat destruct_match; try invert_result;
          apply_typechecker_IH; try invert_pair; repeat (econstructor; eauto);
          try apply_type_of__type_wf; auto; invert_type_wf; auto.
      - (* EBinop *)
        split; intros; destruct o; simpl in *;
        unfold_fold_typechecker; repeat destruct_match; try invert_result;
        repeat (apply_typechecker_IH; try invert_pair; try econstructor; eauto; try constructor;
                try apply_type_of__type_wf; auto; try invert_type_wf; auto).
      - (* EIf *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (apply_typechecker_IH; try invert_result; try econstructor; eauto;
                try apply_type_of__type_wf; auto; try invert_type_wf; auto).
      - (* ELet *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (try apply_typechecker_IH; try invert_result; try econstructor; eauto;
                  try apply_type_of__type_wf; auto; try invert_type_wf; auto;
                  try apply tenv_wf_step; auto).
      - (* EFlatmap *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (try apply_typechecker_IH; try invert_result; try econstructor; eauto;
                  try apply_type_of__type_wf; auto; try invert_type_wf; auto;
                  try apply tenv_wf_step; auto).
      - (* EFold *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (try apply_typechecker_IH; try invert_result; try econstructor; eauto;
                  try apply_type_of__type_wf; auto; try invert_type_wf; auto;
                  try apply tenv_wf_step; auto).
      - (* ERecord *)
        split; intros; unfold_fold_typechecker; repeat destruct_match.
        + unfold record_type_from in *. repeat destruct_match. invert_result.
          eapply record_type_from'_sound with (Gstore := Gstore) (Genv := Genv) in H; eauto.
          apply TyERecord with (tl := l0); intuition.
          * apply Permuted_record_sort.
          * rewrite <- H2; auto.
          * apply StronglySorted_record_sort.
        + unfold record_from in *. destruct_match. invert_result.
          rewrite Bool.andb_true_iff in E1. intuition.
          eapply record_from'_sound with (Gstore := Gstore) in H; eauto; [| apply inclb_correct; auto].
          apply TyERecord with (tl := List.map (fun '(s, e) => (s, get_attr_type l0 s)) l); intuition.
          * apply double_incl_NoDup_Permuted; intuition.
            apply leb_complete. repeat rewrite map_length. auto.
          * rewrite fst_map_fst; auto.
          * inversion H3; auto.
      - (* EAccess *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (apply_typechecker_IH; try invert_result; try econstructor; eauto;
                  try apply_type_of__type_wf; auto; try invert_type_wf; auto).
      - (* EDict *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (apply_typechecker_IH; try invert_result; try econstructor; eauto;
                  try apply_type_of__type_wf; auto; try invert_type_wf; auto).
        + invert_result. constructor.
          * apply first_success_exists_l in E as [p0 [e0 [HL HR]]]. rewrite Forall_forall in H.
            apply H in HR; auto; apply_type_of__type_wf; auto.
          * apply first_success_exists_r in E0 as [p0 [e0 [HL HR]]]. rewrite Forall_forall in H.
            apply H in HR; auto; apply_type_of__type_wf; auto.
          * eapply analyze_dict_body_sound; eauto.
            -- apply first_success_exists_l in E as [p0 [e0 [HL HR]]]. rewrite Forall_forall in H.
               apply H in HR; auto; apply_type_of__type_wf; auto.
            -- apply first_success_exists_r in E0 as [p0 [e0 [HL HR]]]. rewrite Forall_forall in H.
               apply H in HR; auto; apply_type_of__type_wf; auto.
        + constructor; try invert_type_wf; auto.
          eapply analyze_dict_body_sound; eauto; invert_type_wf; auto.
      - (* EInsert *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (apply_typechecker_IH; try invert_result; try apply_type_of__type_wf; auto;
                  try invert_type_wf; auto; try econstructor; eauto).
      - (* EDelete *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (apply_typechecker_IH; try invert_result; try apply_type_of__type_wf; auto;
                  try invert_type_wf; auto; try econstructor; eauto).
      - (* ELookup *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (apply_typechecker_IH; try invert_result; try apply_type_of__type_wf; auto;
                  try invert_type_wf; auto; try econstructor; eauto).
      - (* EOptmatch *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (try apply_typechecker_IH; try invert_result; try apply_type_of__type_wf; auto;
                  try apply tenv_wf_step; try invert_type_wf; auto;
                  try invert_type_wf; auto; try econstructor; eauto).
      - (* EDictFold *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (try apply_typechecker_IH; try invert_result; try apply_type_of__type_wf; auto;
                  try apply tenv_wf_step; try invert_type_wf; auto;
                  try invert_type_wf; auto; try econstructor; eauto).
      - (* ESort *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (try apply_typechecker_IH; try invert_result; try apply_type_of__type_wf; auto;
                  try apply tenv_wf_step; try invert_type_wf; auto;
                  try invert_type_wf; auto; try econstructor; eauto).
      - (* EFilter *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (try apply_typechecker_IH; try invert_result; try apply_type_of__type_wf; auto;
                  try apply tenv_wf_step; try invert_type_wf; auto;
                  try invert_type_wf; auto; try econstructor; eauto).
      - (* EJoin *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (try apply_typechecker_IH; try invert_result; try apply_type_of__type_wf; auto;
                  try repeat apply tenv_wf_step; try invert_type_wf; auto;
                  try invert_type_wf; auto; try econstructor; eauto).
        all: apply IHe2 in E2; auto; apply_type_of__type_wf; auto; invert_type_wf; auto.
      - (* EProj *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat (try apply_typechecker_IH; try invert_result; try apply_type_of__type_wf; auto;
                  try repeat apply tenv_wf_step; try invert_type_wf; auto;
                  try invert_type_wf; auto; try econstructor; eauto).
    Qed.
(*  Show Ltac Profile. *)

    Ltac apply_type_sound_IH :=
      lazymatch goal with
      | H : (tenv_wf ?Genv ->
             forall store env, locals_wf ?Gstore store ->
                               locals_wf ?Genv env -> _),
          H0: tenv_wf ?Genv,
          H1: locals_wf ?Gstore _,
            H2: locals_wf ?Genv _ |- _ =>
          let H' := fresh "H'" in
          pose proof (H H0 _ _ H1 H2) as H'; clear H; inversion H'; subst
      | H : (tenv_wf ?Genv0 ->
             forall _ _, _ -> _ -> type_of_value (interp_expr _ _ ?e) ?t) |- type_of_value (interp_expr _ _ ?e) ?t =>
          apply H; try apply tenv_wf_step; try apply locals_wf_step
      end.

    Ltac type_injection :=
      lazymatch goal with
      | H : TList _ = TList _ |- _ => injection H as H; subst
      end.

    Ltac apply_locals_wf :=
      match goal with
      | H : locals_wf ?G ?E, H' : map.get ?G ?x = _ |- _ =>
          apply H in H'; unfold get_local; destruct (map.get E x); intuition
      end.
    Ltac invert_Forall :=
      match goal with
      | H : Forall _ (_ :: _) |- _ => inversion H; subst
      end.

    Ltac destruct_exists :=
      match goal with
      | H: exists x, _ |- _ => destruct H as [x H]
      end.


    Lemma Forall2_In_Permuted : forall A B (R : A -> B -> Prop) l1 l2 a, Forall2 R l1 l2 -> In a l1 -> exists l1_0 b l2_0, Permutation l1 (a :: l1_0) /\ Permutation l2 (b :: l2_0) /\ R a b /\ Forall2 R l1_0 l2_0.
    Proof.
      intros A B R l1 l2 a HR. induction HR; intros.
      - apply in_nil in H; intuition.
      - inversion H0.
        + exists l, y, l'; subst. intuition.
        + apply IHHR in H1. repeat destruct_exists.
          exists (x :: l1_0), b, (y :: l2_0); intuition.
          * apply Permutation_trans with (l' := x :: a :: l1_0); auto using perm_swap.
          * apply Permutation_trans with (l' := y :: b :: l2_0); auto using perm_swap.
    Qed.

    Lemma Forall2_Permuted_StronglySorted : forall A B R (l1 : list (string * A)) (l2 : list (string * B)) l1' l2',
        Forall2 R l1 l2 -> NoDup (List.map fst l1) -> (forall x y, R x y -> fst x = fst y) -> Permutation l1 l1' -> Permutation l2 l2' -> StronglySorted record_entry_leb l1' -> StronglySorted record_entry_leb l2' -> Forall2 R l1' l2'.
    Proof.
      intros A B R l1 l2 l1'; generalize dependent l2; generalize dependent l1; induction l1'; intros l1 l2 l2' HR Hnodup Hfst Hpermu1 Hpermu2 Hsorted1 Hsorted2.
      - apply Permutation_sym, Permutation_nil in Hpermu1; subst. inversion HR; subst.
        apply Permutation_nil in Hpermu2; subst; auto.
      - assert (In a l1). { apply Permutation_in with (l := a :: l1'); auto using Permutation_sym. intuition. }
        eapply Forall2_In_Permuted in H; eauto. repeat destruct_exists. intuition.
        apply Permutation_sym in H. assert (Permutation (b :: l2_0) l2'). { eapply Permutation_trans; eauto. }
        destruct l2' as [| b' l2'].
        + apply Permutation_sym, Permutation_nil in H2. discriminate.
        + apply Hfst in H1 as H1'. assert (b' = b).
          { inversion Hsorted1; inversion Hsorted2; subst.
            apply Permutation_in with (x := b) in H2; intuition. inversion H2; auto.
            apply (List.Forall_In H11) in H4 as H4'. unfold record_entry_leb in H4'. (* fst b' <= fst b *)
            apply Permutation_sym, Permutation_in with (x := b') in Hpermu2 as H5; intuition.
            apply Permutation_map with (f := fst) in Hpermu1.
            assert (List.map fst l1 = List.map fst l2).
            { generalize dependent Hfst; generalize dependent HR. clear. intros HR Hfst.
              induction HR; auto. simpl. apply Hfst in H. congruence. }
            simpl in *. rewrite H8 in Hpermu1.
            assert (forall A B (p : A * B) l, In p l -> In (fst p) (List.map fst l)). {
              clear. intros. induction l; intuition.
              inversion H; subst; simpl; intuition. }
            apply H9 in H5. apply Permutation_in with (x := fst b') in Hpermu1; auto.
            assert (String.leb (fst b) (fst b')).
            { inversion Hpermu1.
              - rewrite H1' in H12. rewrite H12. auto. unfold String.leb. rewrite string_compare_refl; auto.
              - apply In_fst in H12 as [p [H12L H12R]]. apply (List.Forall_In H7) in H12L. unfold record_entry_leb in H12L.
                rewrite H12R, H1' in H12L. assumption. } (* fst b <= fst b' *)
            pose proof (leb_antisym _ _ H4' H12). (* fst b = fst b' *)
            assert (NoDup (List.map fst (b' :: l2'))).
            { rewrite H8 in Hnodup. apply Permutation_map with (f := fst) in Hpermu2. simpl in *.
              apply Permutation_sym, Permutation_NoDup in Hpermu2; auto. }
            inversion H14. apply H9 in H4. rewrite <- H13 in H4. intuition. }
          subst.
          assert (Permutation (a :: l1_0) (a :: l1')). { apply Permutation_sym in H0; eapply Permutation_trans; eauto. }
          apply Permutation_cons_inv in H4, H2.
          constructor; intuition; eapply IHl1'; eauto.
          * apply Permutation_map with (f := fst), Permutation_NoDup in H0; auto.
            simpl in *; inversion H0; auto.
          * inversion Hsorted1; auto.
          * inversion Hsorted2; auto.
    Qed.

    Lemma Forall2_split : forall A B (l : list A) (l' : list B) f g, Forall2 (fun p p' => f p p' /\ g p p') l l' -> Forall2 f l l' /\ Forall2 g l l'.
    Proof.
      intros. induction H; intuition.
    Qed.

    Lemma Forall2_fst_eq : forall A B (l : list (string * A)) (l' : list (string * B)),
        Forall2 (fun p p' => fst p = fst p') l l' <->
        List.map fst l = List.map fst l'.
    Proof.
      intros. split; intro H.
      - induction H; intuition. simpl; congruence.
      - generalize dependent l'. induction l; destruct l'; try discriminate; intuition.
        simpl in *. inversion H. constructor; auto.
    Qed.

    Lemma TyVList_def : forall l t, Forall (fun v => type_of_value v t) l <-> type_of_value (VList l) (TList t).
    Proof.
      split; intros.
      - constructor; auto.
      - inversion H; intuition.
    Qed.

    Lemma TyVDict_def : forall l kt vt, type_wf kt -> type_wf vt ->
                                        NoDup (map fst l) ->
                                        StronglySorted (fun p p' : value * value => dict_entry_leb p p') l ->
                                        Forall (fun p => type_of_value (fst p) kt /\ type_of_value (snd p) vt) l <-> type_of_value (VDict l) (TDict kt vt).
    Proof.
      split; intros.
      - constructor; auto.
      - inversion H3; intuition.
    Qed.

    Lemma record_proj_sound : forall l, NoDup (List.map fst l) ->
                                        forall tl, Forall2 (fun p tp => fst p = fst tp /\ type_of_value (snd p) (snd tp)) l tl ->
                                                   forall x t, In (x, t) tl ->
                                                               type_of_value (record_proj (width := width) x l) t.
    Proof.
      intros l Hnodup tl Hvt x t Hin. generalize dependent tl. induction l; intros; simpl in *.
      - inversion Hvt; subst. apply in_nil in Hin. intuition.
      - inversion Hvt; subst. destruct a. inversion Hin; subst.
        + destruct H1. simpl in *. subst. unfold record_proj. simpl. rewrite eqb_refl. auto.
        + simpl in *; inversion Hnodup; subst. assert (String.eqb x s = false).
          { apply in_map with (f := fst) in H; simpl in H. apply Forall2_split in H3 as [HL HR]. apply Forall2_fst_eq in HL.
            rewrite eqb_neq. intro contra; subst. rewrite HL in H4. intuition. }
          unfold record_proj; simpl. rewrite H0. eapply IHl; eauto.
    Qed.

    Lemma dict_insert_preserve_NoDup : forall k k' v l,
        ~ In k (map fst l) ->
        k <> k' ->
        ~ In k (map fst (dict_insert (word := word) k' v l)).
    Proof.
      induction l; intros.
      - simpl; intuition.
      - simpl in H. apply Decidable.not_or in H as [HL HR].
        pose proof IHl HR H0; auto.
        simpl. destruct a. unfold value_ltb, value_eqb.
        destruct (value_compare k' v0); simpl; intuition.
    Qed.

    Lemma dict_insert_incl : forall k v l, incl (dict_insert (word:=word) k v l) ((k, v) :: l).
    Proof.
      induction l; simpl; intuition.
      unfold value_ltb, value_eqb; destruct value_compare eqn:E; intuition.
      apply incl_cons; intuition.
      unfold incl in *; intros. apply IHl in H.
      inversion H; intuition. constructor; congruence.
    Qed.

    Ltac destruct_value_compare :=
      lazymatch goal with
      | H: context[value_compare ?x ?y] |- _ =>
          let E := fresh "E" in
          destruct (value_compare x y) eqn: E
      | |- context[value_compare ?x ?y] =>
          let E := fresh "E" in
          destruct (value_compare x y) eqn: E
      end.

    Ltac invert_SSorted :=
      lazymatch goal with
      | H: StronglySorted _ (_ :: _) |- _ => inversion H; subst
      end.

    Ltac invert_NoDup :=
      lazymatch goal with
      | H: NoDup (_ :: _) |- _ => inversion H; subst
      end.

    Ltac invert_In :=
      lazymatch goal with H: In _ (_ :: _) |- _ => inversion H end.

    Lemma dict_insert_sound : forall l kt vt k v,
        type_wf kt -> type_wf vt ->
        type_of_value (VDict l) (TDict kt vt) ->
        type_of_value k kt ->
        type_of_value v vt ->
        type_of_value (VDict (dict_insert k v l)) (TDict kt vt).
    Proof.
      intros. induction l; constructor; simpl; auto.
      1-2: constructor; intuition.
      1: apply NoDup_nil. 1: apply SSorted_nil.
      1-3: destruct a as [k' v']; inversion H1; subst;
      assert (Hl: type_of_value (VDict l) (TDict kt vt));
      [ lazymatch goal with
         | H1: Forall _ _, H2: NoDup _, H3: StronglySorted _ _ |- _ =>
             inversion H1; inversion H2; inversion H3
         end; constructor; auto | ];
      apply IHl in Hl.
      - unfold value_ltb, value_eqb; destruct_value_compare.
        + invert_Forall; constructor; auto.
        + constructor; auto.
        + invert_Forall; constructor; auto. inversion Hl; auto.
      - unfold value_ltb, value_eqb; destruct_value_compare; simpl in *.
        + apply value_compare_Eq_eq in E. subst; auto.
        + constructor; auto. intro contra. invert_SSorted.
          inversion contra.
          * symmetry in H4. apply eq_value_compare_Eq in H4. congruence.
          * rewrite Forall_forall in H12. apply In_fst in H4 as [[k'' v''] [HL HR]].
            apply H12 in HL. unfold dict_entry_leb in HL; simpl in *; subst.
            unfold value_leb in HL. unfold leb_from_compare in HL. rewrite value_compare_antisym in E.
            simpl in E. destruct_value_compare; discriminate.
        + inversion Hl; subst.
          constructor; auto. invert_NoDup.
          apply dict_insert_preserve_NoDup; auto. intro contra.
          symmetry in contra; apply eq_value_compare_Eq in contra; congruence.
      - unfold value_ltb, value_eqb; destruct_value_compare; simpl in *.
        + apply value_compare_Eq_eq in E; subst; auto.
          invert_SSorted; constructor; auto.
        + constructor; auto. rewrite Forall_forall; intros. destruct x; simpl.
          unfold dict_entry_leb, value_leb, leb_from_compare. simpl. invert_In.
          * invert_pair; subst. rewrite E; auto.
          * invert_SSorted; subst. eapply List.Forall_In in H14; eauto.
            unfold dict_entry_leb, value_leb, leb_from_compare in *. simpl in *.
            destruct_value_compare.
            1:{ apply value_compare_Eq_eq in E0; subst. rewrite E; trivial. }
            1: erewrite value_compare_trans; eauto.
            1: intuition.
        + inversion Hl; subst. constructor; auto.
          rewrite Forall_forall. intros. apply dict_insert_incl in H4.
          unfold dict_entry_leb, value_leb, leb_from_compare; simpl.
          invert_In; subst; simpl.
          * rewrite value_compare_antisym. rewrite E; auto.
          * invert_SSorted; subst. eapply List.Forall_In in H19; eauto.
    Qed.

    Lemma dict_delete_preserve_NoDup : forall k k' l,
        ~ In k (map fst l) -> ~ In k (map fst (dict_delete (word:=word) k' l)).
    Proof.
      induction l; simpl; auto; intros.
      repeat lazymatch goal with |- context[match ?x with _ => _ end] => destruct x end;
        simpl; intuition.
    Qed.

    Lemma dict_delete_incl : forall k l, incl (dict_delete (word:=word) k l) l.
    Proof.
      induction l; simpl; intuition.
      lazymatch goal with |- context[match ?x with _ => _ end] => destruct x end;
      intuition.
    Qed.

    Lemma dict_delete_sound : forall l kt vt k,
        type_wf kt -> type_wf vt ->
        type_of_value (VDict l) (TDict kt vt) ->
        type_of_value k kt ->
        type_of_value (VDict (dict_delete k l)) (TDict kt vt).
    Proof.
      intros; induction l; constructor; simpl; auto using NoDup_nil, SSorted_nil.
      all: destruct a as [k' v']; inversion H1; subst;
        assert (Hl: type_of_value (VDict l) (TDict kt vt));
        [ lazymatch goal with
          | H1: Forall _ _, H2: NoDup _, H3: StronglySorted _ _ |- _ =>
              inversion H1; inversion H2; inversion H3
          end; constructor; auto | ];
        apply IHl in Hl; simpl in *.
      - destruct (value_eqb k k').
        + invert_Forall; auto.
        + inversion Hl; subst. invert_Forall. constructor; auto.
      - destruct (value_eqb k k').
        + invert_NoDup; auto.
        + inversion Hl; subst. simpl. constructor; auto.
          apply dict_delete_preserve_NoDup; invert_NoDup; auto.
      - destruct (value_eqb k k').
        + invert_SSorted; auto.
        + inversion Hl; subst. constructor; auto.
          rewrite Forall_forall; intros.
          invert_SSorted. eapply List.Forall_In in H17; eauto.
          apply dict_delete_incl in H3; auto.
    Qed.

    Lemma dict_lookup_sound : forall l kt vt k,
        type_wf kt -> type_wf vt ->
        type_of_value (VDict l) (TDict kt vt) ->
        type_of_value k kt ->
        type_of_value (VOption (dict_lookup k l)) (TOption vt).
    Proof.
      intros; induction l.
      - constructor.
      - simpl. destruct a as [k' v']. destruct (value_eqb k k');
          match goal with
          | H: type_of_value (VDict (_ :: _)) _ |- _ => inversion H; subst
          end; invert_Forall; auto.
        + constructor. intuition.
        + apply IHl. constructor; auto;
            simpl in *; invert_NoDup; invert_SSorted; auto.
    Qed.

    Lemma Forall_Forall_filter : forall A P (l : list A), Forall P l -> forall f, Forall P (filter f l).
    Proof.
      induction l; simpl; intros.
      - constructor.
      - destruct (f a).
        + constructor; inversion H; intuition.
        + apply IHl; inversion H; intuition.
    Qed.

    Lemma flat_map_type_sound : forall l t, type_of_value (VList l) (TList t) ->
                                        forall f t', (forall v, type_of_value v t -> type_of_value (VList (f v)) (TList t')) ->
                                                     type_of_value (VList (flat_map f l)) (TList t').
    Proof.
      induction l; simpl; intros; repeat constructor.
      apply Forall_app. inversion H; inversion H3; subst. split.
      - rewrite TyVList_def. apply H0; auto.
      - try rewrite TyVList_def in *. eapply IHl; eauto.
    Qed.

    Lemma map_type_sound : forall l t, type_of_value (VList l) (TList t) ->
                                       forall f t', (forall v, type_of_value v t -> type_of_value (f v) t') ->
                                                    type_of_value (VList (List.map f l)) (TList t').
    Proof.
      induction l; simpl; intros; repeat constructor; inversion H; inversion H3.
      - intuition.
      - rewrite TyVList_def. eapply IHl; eauto. constructor. auto.
    Qed.

  Lemma NoDup_dedup_fst : forall A B P_eqb (l : list (A * B)),
      (forall x y, P_eqb x y = true <-> fst x = fst y) -> NoDup (List.map fst (List.dedup P_eqb l)).
  Proof.
    intros. induction l; simpl; auto using NoDup_nil.
    destruct (find (P_eqb a) l) eqn:E; auto.
    simpl; constructor; auto. intro contra.
    pose proof (find_none _ _ E).
    assert (exists x, In x l /\ fst a = fst x).
    { revert H contra. clear. intros; induction l; simpl in *; intuition.
      destruct (find (P_eqb a0) l) eqn:E.
      - apply IHl in contra; firstorder.
      - simpl in *. firstorder. exists a0; intuition. }
    destruct H1 as [x [HL HR]]. apply H0 in HL. apply H in HR. congruence.
  Qed.

  Lemma dedup_In : forall A (x : A) f l, In x (List.dedup f l) -> In x l.
  Proof.
    induction l; simpl; auto.
    lazymatch goal with |- context[match ?x with _ => _ end] => destruct x end; intuition.
    inversion H; auto.
  Qed.

  Lemma type_sound : forall Gstore Genv e t,
      type_of Gstore Genv e t ->
      tenv_wf Gstore -> tenv_wf Genv ->
      forall store env,
        locals_wf Gstore store -> locals_wf Genv env ->
        type_of_value (interp_expr store env e) t.
    Proof.
      intros Gstore Genv e t H H_Gstore H_Genv. induction H using @type_of_IH; simpl; intros store env H_store H_env; auto.
      1, 2: (* TyEVar | TyELoc *)
        apply_locals_wf.
      - (* TyEAtom *)
        match goal with H : type_of_atom _ _ |- _ => inversion H end; subst; constructor; apply Forall_nil.
      - (* TyEUnop *)
        inversion H; apply_type_sound_IH; try discriminate; repeat constructor; auto.
      - (* TyEBinop *)
        inversion H; repeat apply_type_sound_IH; try discriminate; try type_injection; repeat constructor; auto.
        + apply Forall_app; auto.
        + assert (forall A f (l : list A), Forall f l -> forall n, Forall f (concat (repeat l n))).
          { clear. induction n; simpl; intros.
            - apply Forall_nil.
            - apply Forall_app; auto. }
          auto.
        + assert (forall len lo, Forall (fun v => type_of_value v TInt) (eval_range lo len)).
          { clear; induction len; simpl; intros.
            - apply Forall_nil.
            - repeat constructor; auto. }
          auto.
        + assert (forall len lo, Forall (fun v => type_of_value v TWord) (eval_range_word lo len)).
          { clear; induction len; simpl; intros.
            - apply Forall_nil.
            - repeat constructor; auto. }
          auto.
      - (* TyEIf *)
        repeat apply_type_sound_IH;
          match goal with
          | |- type_of_value (if ?b then _ else _) _ => destruct b; constructor; auto
          end.
      - (* TyELet *)
        repeat apply_type_sound_IH; try constructor;
          try apply_type_of__type_wf; try invert_type_wf; auto.
      - (* TyEFlatmap *)
        repeat apply_type_sound_IH;
        clear H1. constructor. induction l; simpl.
        + apply Forall_nil.
        + apply Forall_app; split.
          * invert_Forall.
            assert (type_of_value (interp_expr store (map.put env x a) e2) (TList t2)).
            { apply_type_sound_IH; auto. apply type_of__type_wf in H; try invert_type_wf; auto. }
            inversion H1; auto.
          * apply IHl. inversion H3. assumption.
      - (* TyEFold *)
        repeat apply_type_sound_IH;
          try (match goal with
               | H: VList ?l = _ |- _ => clear H
               end; induction l; simpl; try constructor; auto; apply_type_sound_IH; auto;
               match goal with
               | H: Forall _ (_ :: _) |- _ => inversion H; subst
               end);
               repeat apply locals_wf_step; auto; repeat apply tenv_wf_step; auto;
          try apply_type_of__type_wf; try invert_type_wf; auto.
        all: match goal with
             | H: VList ?l = _ |- type_of_value (fold_right _ _ ?l) _ => clear H; induction l end;
          simpl; try constructor; auto; apply_type_sound_IH; auto;
          match goal with
          | H: Forall _ (_ :: _) |- _ => inversion H; subst
          end;
          repeat apply locals_wf_step; auto; repeat apply tenv_wf_step; auto;
          try apply_type_of__type_wf; try invert_type_wf; auto.
      - (* TyERecord *)
        constructor; auto.
        + apply Permutation_NoDup with (l := List.map fst tl); auto. apply Permutation_map; auto.
        + remember (fun p tp => fst p = fst tp /\ type_of_value (snd p) (snd tp)) as R.
          assert (Forall2 R (List.map (fun '(s, e0) => (s, interp_expr store env e0)) l) tl).
          { revert H_Genv H_store H_env H H1 HeqR. clear; intros; generalize dependent tl.
            induction l; simpl; intros; destruct tl; try discriminate.
            - intuition.
            - destruct a, p; simpl in *; subst. constructor.
              + simpl. split; try congruence. inversion H1; auto.
              + apply IHl; inversion H; inversion H1; intuition. }
          eapply Forall2_Permuted_StronglySorted; eauto.
          * rewrite fst_map_fst; rewrite H; auto.
          * subst; intuition.
          * apply Permuted_record_sort.
          * apply StronglySorted_record_sort.
      - (* TyEAccess *)
        repeat apply_type_sound_IH. eapply record_proj_sound; eauto.
        + rewrite <- H1 in *. assert (E: List.map fst l = List.map fst tl).
          { revert H5; clear; intros H5. induction H5; simpl; auto.
            intuition; congruence. }
          rewrite E; auto.
        + apply access_record_sound; auto.
      - (* TyEDict *)
        constructor; auto.
        + rewrite Forall_forall in *.
          assert (forall p, In p (List.map (fun '(k, v) => (interp_expr store env k, interp_expr store env v)) l) -> type_of_value (fst p) kt /\ type_of_value (snd p) vt).
          { induction l; intros; simpl in *; try now (exfalso; auto).
            destruct H3.
            - pose proof (H1 a); intuition; destruct a; subst; simpl in *.
              + change e with (fst (e, e0)). apply H2; auto.
              + change e0 with (snd (e, e0)). apply H2; auto.
            - apply IHl; auto. }
          intros. apply H3. eapply dedup_In. pose proof (Permuted_dict_sort (width:=width)).
          eapply Permutation_in; [ apply Permutation_sym |]; eauto.
        + assert (Permutation_NoDup_fst : forall A B (l0 l' : list (A * B)), NoDup (List.map fst l0) -> Permutation l0 l' -> NoDup (List.map fst l')).
          { intros A B l0 l' H_NoDup H_Permu. eapply Permutation_map in H_Permu. eapply Permutation_NoDup; eauto. }
          eapply Permutation_NoDup_fst.
          2: eapply Permuted_dict_sort.
          apply NoDup_dedup_fst. unfold value_eqb. split.
          * destruct (value_compare (fst x) (fst y)) eqn:E; try discriminate. intros.
            apply value_compare_Eq_eq. auto.
          * intros. rewrite H3. rewrite value_compare_refl. auto.
        + apply StronglySorted_dict_sort.
      - (* TyEInsert *)
        repeat apply_type_sound_IH; apply dict_insert_sound; constructor; try invert_type_wf; auto.
      - (* TyEDelete *)
        repeat apply_type_sound_IH; apply dict_delete_sound; try constructor;
          try apply_type_of__type_wf; try invert_type_wf; auto.
      - (* TyELookup *)
        repeat apply_type_sound_IH;
          lazymatch goal with
          | H: Forall (fun p => type_of_value (fst p) ?t /\ _) _ |- _ => apply dict_lookup_sound with (kt := t)
          end; try constructor; try invert_type_wf; auto.
      - (* TyEOptMatch *)
        repeat apply_type_sound_IH; auto; try constructor;
          try apply_type_of__type_wf; try invert_type_wf; auto.
      - (* TyEDictFold *)
        repeat apply_type_sound_IH.
        all: try (lazymatch goal with
                  | H: VDict ?l = _ |- _ => clear H
                  end; induction l; simpl; try constructor; auto; apply_type_sound_IH; auto;
                  invert_Forall; repeat apply locals_wf_step; auto; repeat apply tenv_wf_step; auto;
                  try apply_type_of__type_wf; try invert_type_wf; intuition;
                  lazymatch goal with
                  | H: _ -> _ -> ?P |- ?P => apply H
                  end;
                  simpl in *; invert_NoDup; invert_SSorted; intuition).
        all: try (lazymatch goal with
                  | H: VDict ?l = _ |- type_of_value (fold_right _ _ ?l) _ => clear H; induction l
                  end;
                  simpl; try constructor; auto; apply_type_sound_IH; auto;
                  invert_Forall; repeat apply locals_wf_step; auto; repeat apply tenv_wf_step; auto;
                  try apply_type_of__type_wf; try invert_type_wf; intuition;
                  lazymatch goal with
                  | H: _ -> _ -> ?P |- ?P => apply H
                  end; simpl in *; invert_NoDup; invert_SSorted; intuition).
      - (* TyESort *)
        repeat apply_type_sound_IH. constructor. rewrite Forall_forall; intros.
        eapply List.Forall_In in H2; eauto. eapply Permutation_in.
        1: apply Permutation_sym, Permuted_value_sort. auto.
      - (* TyEFilter *)
        repeat apply_type_sound_IH. constructor. apply Forall_Forall_filter. auto.
      - (* TyEJoin *)
        repeat apply_type_sound_IH.
        rewrite <- H4 in H'0. eapply flat_map_type_sound; eauto. intros.
        apply map_type_sound with (t := t2).
        + constructor; apply Forall_Forall_filter; auto.
        + intuition. repeat apply_type_sound_IH; repeat apply locals_wf_step; auto;
            try apply tenv_wf_step; try apply_type_of__type_wf; try invert_type_wf; auto.
      - (* TyEProj *)
        repeat apply_type_sound_IH.
        apply map_type_sound with (t := t1).
        + constructor. auto.
        + intros; repeat apply_type_sound_IH; repeat apply locals_wf_step; auto;
            try apply_type_of__type_wf; try invert_type_wf; auto.
    Qed.

    Ltac apply_cmd_tc_sound_IH :=
      lazymatch goal with
      | IH: context[well_typed _ _ ?c] |- well_typed _ _ ?c =>
          eapply IH; eauto
      end.

    Lemma command_typechecker_sound : forall Gstore Genv c c',
        tenv_wf Gstore -> tenv_wf Genv ->
        typecheck Gstore Genv c = Success c' -> well_typed Gstore Genv c.
    Proof.
      intros Gstore Genv c; revert Gstore Genv.
      induction c; simpl; intros Gstore Genv c' H_str H_env H.
      all: repeat destruct_match.
      1,2: try constructor; try apply_cmd_tc_sound_IH.
      1,2,5: lazymatch goal with
           | H: synthesize_expr _ _ _ = Success _ |- _ =>
               let H_wf := fresh "H_wf" in
               apply typechecker_sound in H; auto;
               apply type_of__type_wf in H as H_wf; auto
           end;
      econstructor; eauto; apply_cmd_tc_sound_IH; apply tenv_wf_step;
      try invert_type_wf; auto.
      - econstructor; eauto. eapply typechecker_sound; eauto.
      - constructor; try apply_cmd_tc_sound_IH.
        eapply typechecker_sound; eauto. constructor.
    Qed.

    Lemma locals_wf_restored : forall Gstore store store' x t,
        locals_wf Gstore store ->
        locals_wf (map.put Gstore x t) store' ->
        locals_wf Gstore (map.update store' x (map.get store x)).
    Proof.
      unfold locals_wf; intros Gstore store store' x t H_str H_str' x' t' H.
      destruct (String.eqb x x') eqn:E.
      + rewrite eqb_eq in E; subst. rewrite Properties.map.get_update_same.
        apply H_str; auto.
      + rewrite eqb_neq in E. rewrite Properties.map.get_update_diff; try congruence.
        apply H_str'. rewrite map.get_put_diff; congruence.
    Qed.

    Lemma command_type_sound : forall Gstore Genv c,
      well_typed Gstore Genv c ->
      tenv_wf Gstore -> tenv_wf Genv ->
      forall store env,
        locals_wf Gstore store -> locals_wf Genv env ->
        locals_wf Gstore (interp_command store env c).
    Proof.
      intros Gstore Genv c H. induction H; simpl;
        intros H_Gstr H_Genv store env H_str H_env; auto.
      - apply IHwell_typed; auto.
        + apply tenv_wf_step; auto. apply type_of__type_wf in H; auto.
        + apply locals_wf_step; auto. eapply type_sound; eauto.
      - eapply locals_wf_restored; auto. apply IHwell_typed; auto.
        + apply tenv_wf_step; auto. apply type_of__type_wf in H; auto.
        + apply locals_wf_step; auto. eapply type_sound; eauto.
      - unfold locals_wf. intros x0 t' H'.
        destruct (String.eqb x x0) eqn:E;
          [ rewrite eqb_eq in E; subst; rewrite map.get_put_same
          | rewrite eqb_neq in E; rewrite map.get_put_diff; try congruence ].
        + rewrite H' in H; injection H as H; subst.
          eapply type_sound; eauto.
        + apply H_str; auto.
      - repeat match goal with |- context[match ?x with _ => _ end] => destruct x end; auto.
      - match goal with |- context[match ?x with _ => _ end] => destruct x eqn:E end; auto.
        apply type_of__type_wf in H as H_wf; auto.
        eapply type_sound in H; eauto. rewrite E in H. inversion H; subst. clear E H.
        generalize dependent store. induction l; simpl; auto; intros.
        apply IHl; try invert_Forall; intuition. apply H; auto.
        + apply tenv_wf_step; auto. invert_type_wf; auto.
        + apply locals_wf_step; auto.
    Qed.

  End WithMap.
End WithWord.
