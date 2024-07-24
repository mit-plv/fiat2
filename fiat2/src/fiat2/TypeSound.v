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
    Local Notation value := (value (word := word)).
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    Local Coercion is_true : bool >-> Sortclass.

    Inductive type_of_value : value -> type -> Prop :=
    | TyVWord w : type_of_value (VWord w) TWord
    | TyVInt n : type_of_value (VInt n) TInt
    | TyVBool b : type_of_value (VBool b) TBool
    | TyVString s : type_of_value (VString s) TString
    | TyVOptionNone t : type_of_value (VOption None) (TOption t)
    | TyVOptionSome v t : type_of_value v t ->
                          type_of_value (VOption (Some v)) (TOption t)
    | TyVList l t : Forall (fun v => type_of_value v t) l -> type_of_value (VList l) (TList t)
    | TyVRecord l tl : NoDup (List.map fst l) -> StronglySorted record_entry_leb l ->
                       Forall2 (fun p tp => fst p = fst tp /\ type_of_value (snd p) (snd tp)) l tl ->
                       type_of_value (VRecord l) (TRecord tl)
    | TyVDict l tk tv : Forall (fun p => type_of_value (fst p) tk /\ type_of_value (snd p) tv) l ->
                        type_of_value (VDict l) (TDict tk tv)
    | TyVUnit : type_of_value VUnit TUnit.

  Definition well_formed_locals (G : tenv) (E : locals) :=
    forall x t, map.get G x = Some t ->
                match map.get E x with
                | Some v => type_of_value v t
                | _ => False
                end.

  Lemma well_formed_locals_step : forall G E,
      well_formed_locals G E ->
      forall x t v,
        type_of_value v t ->
        well_formed_locals (map.put G x t) (map.put E x v).
  Proof.
    unfold well_formed_locals; intros.
    destruct (String.eqb x0 x) eqn:E_x.
    - rewrite String.eqb_eq in E_x. rewrite E_x in *.
      rewrite map.get_put_same. rewrite map.get_put_same in H1. congruence.
    - rewrite String.eqb_neq in E_x. rewrite map.get_put_diff; auto.
      rewrite map.get_put_diff in H1; auto. apply H. auto.
  Qed.

  Local Ltac destruct_match :=
    lazymatch goal with
    | H : (if type_eqb ?x ?y then _ else _) = _ |- _ =>
        let E := fresh "E" in
        destruct (type_eqb x y) eqn:E; try discriminate; apply type_eqb_eq in E; subst; simpl in *
    | H: (match ?x with _ => _ end) = Success _ |- _ =>
        let E := fresh "E" in
        destruct x eqn:E; try discriminate; simpl in *
    end.

  Local Ltac destruct_compare_types :=
    unfold compare_types in *; destruct_match; constructor.

  Local Ltac invert_result :=
    lazymatch goal with
    | H: Success _ = Success _ |- _ => inversion H; clear H; intros; subst
    end.

  Local Ltac invert_pair :=
    lazymatch goal with
    | H: (_, _) = (_, _) |- _ => inversion H; clear H; intros; subst
    end.

  Lemma atom_typechecker_sound : forall a t a',
      (synthesize_atom a = Success (t, a') -> type_of_atom a t) /\
        (analyze_atom t a = Success a' -> type_of_atom a t).
  Proof.
    destruct a; split; simpl; intro;
      repeat (try destruct_compare_types; try destruct_match; try invert_result; try constructor).
  Qed.

  Local Ltac apply_typechecker_IH :=
    match goal with
    | IH: (forall _ _ _ _, (synthesize_expr _ _ ?e = _ -> _) /\ _),
        H: synthesize_expr _ _ ?e = _ |- _ => eapply IH in H; eauto
    | IH: (forall _ _ _ _, _ /\ (analyze_expr _ _ _ ?e = _ -> _)),
        H: analyze_expr _ _ _ ?e = _ |- _ => eapply IH in H; eauto
    end.

    Section __.
    Lemma fst_map_fst : forall (A B C : Type) (l : list (A * B)) (f : A -> B -> C),
        List.map fst (List.map (fun '(a, b) => (a, f a b)) l) = List.map fst l.
    Proof.
      induction l; auto.
      intros. destruct a. simpl. f_equal. auto.
    Qed.

    Lemma inb_false_iff : forall s l, inb eqb l s = false <-> ~ In s l.
    Proof.
      induction l; simpl; intros.
      - intuition.
      - destruct (String.eqb a s) eqn:E; intuition.
        + rewrite String.eqb_eq in E; intuition.
        + rewrite String.eqb_neq in E; intuition.
    Qed.

    Lemma inb_true_iff : forall s l, inb eqb l s = true <-> In s l.
    Proof.
      induction l; simpl; intros.
      - split; intuition.
      - destruct (String.eqb a s) eqn:E; intuition.
        + rewrite String.eqb_eq in E; intuition.
        + rewrite String.eqb_neq in E; intuition.
    Qed.

    Lemma inclb_correct : forall l l', inclb String.eqb l l' = true -> incl l l'.
    Proof.
      induction l; simpl; intros.
      - apply incl_nil_l.
      - rewrite Bool.andb_true_iff in H. destruct H as [HL HR].
        apply IHl in HR. rewrite inb_true_iff in HL.
        unfold incl. intros. inversion H; subst; intuition.
    Qed.

    Lemma inclb_complete : forall l l', incl l l' -> inclb String.eqb l l' = true.
    Proof.
      intros l l' H. unfold inclb. rewrite forallb_forall; intros.
      rewrite inb_true_iff. intuition.
    Qed.

    Lemma record_type_from'_sound : forall l tl el Gstore Genv,
        Forall
        (fun p : string * expr =>
         forall (Gstore Genv : tenv) (t : type) (e' : expr),
         (synthesize_expr Gstore Genv (snd p) = Success (t, e') -> type_of Gstore Genv (snd p) t) /\
         (analyze_expr Gstore Genv t (snd p) = Success e' -> type_of Gstore Genv (snd p) t)) l ->
        record_type_from' (List.map (fun '(s, e') => (s, synthesize_expr Gstore Genv e')) l) = Success (tl, el) ->
        List.map fst l = List.map fst tl /\ Forall2 (type_of Gstore Genv) (List.map snd l) (List.map snd tl) /\ NoDup (List.map fst l).
    Proof.
      induction l; intros.
      - simpl in *. invert_result. intuition. apply NoDup_nil.
      - simpl in *. repeat destruct_match. invert_result. destruct a. inversion E; subst; simpl.
        inversion H; subst. apply (IHl _ _ _ _ H4)in E2 as [IHl1 [IHl2 IHl3]]. split; [| split].
        + f_equal. auto.
        + constructor; auto. apply H3 in H2. auto.
        + constructor; auto. apply inb_false_iff. erewrite <- fst_map_fst. apply E4.
    Qed.

    Lemma record_from'_sound :
      forall l tl' el Gstore Genv,
        Forall
        (fun p : string * expr =>
         forall (Gstore Genv : tenv) (t : type) (e' : expr),
         (synthesize_expr Gstore Genv (snd p) = Success (t, e') -> type_of Gstore Genv (snd p) t) /\
         (analyze_expr Gstore Genv t (snd p) = Success e' -> type_of Gstore Genv (snd p) t)) l ->
        record_from' (List.map (fun '(s, e) => (s, analyze_expr Gstore Genv (get_attr_type tl' s) e)) l) = Success el ->
        let tl := List.map (fun '(s, _) => (s, get_attr_type tl' s)) l in
        List.map fst l = List.map fst tl /\ Forall2 (type_of Gstore Genv) (List.map snd l) (List.map snd tl) /\ NoDup (List.map fst l).
    Proof.
      induction l; intros.
      - simpl in *. invert_result. intuition. apply NoDup_nil.
      - simpl in *. repeat destruct_match. destruct a. inversion H; inversion E; subst.
        invert_result. simpl in *. intuition.
        + f_equal. rewrite fst_map_fst. auto.
        + constructor.
          * eapply H3; eauto.
          * eapply IHl; eauto.
        + rewrite fst_map_fst in E2. apply inb_false_iff in E2. apply NoDup_cons; auto.
          eapply IHl; eauto.
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
            + rewrite String.eqb_eq in E; subst; auto.
            + rewrite String.eqb_neq in E. right. apply IHtl'. intuition. }
        apply H5, In_Permuted in H. destruct H as [tl Htl].
        eapply Permutation_trans; [| apply Htl].
        subst; apply perm_skip.
        assert (forall (l : list (string * expr)) tl tl' s t,
                   incl (List.map fst l) (List.map fst tl') ->
                   Permutation ((s, t) :: tl) tl' ->
                   ~ In s (List.map fst l) -> NoDup (List.map fst tl') ->
                   List.map (fun '(s, _) => (s, get_attr_type tl' s)) l = List.map (fun '(s, _) => (s, get_attr_type tl s)) l).
        { clear. induction l; simpl; intros; auto.
          destruct a; simpl in *. f_equal.
          - rewrite <- Permutation_NoDup_In_get_attr_type with (tl := (s,t) :: tl) (tl' := tl'); auto.
            + simpl. destruct (String.eqb s s0) eqn:E; auto.
              exfalso; apply H1; left; symmetry; apply String.eqb_eq; auto.
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
    End __.

    Lemma proj_record_type_sound : forall l s t, proj_record_type l s = Success t -> In (s, t) l.
    Proof.
      induction l; simpl in *; try discriminate. intros.
      destruct a. destruct_match; auto.
      rewrite String.eqb_eq in E. invert_result. auto.
    Qed.

    Lemma dict_from'_sound : forall l,
        Forall (fun p =>
                  (forall (Gstore Genv : tenv) (t : type) (e' : expr),
                      (synthesize_expr Gstore Genv (fst p) = Success (t, e') -> type_of Gstore Genv (fst p) t) /\
                        (analyze_expr Gstore Genv t (fst p) = Success e' -> type_of Gstore Genv (fst p) t)) /\
                    (forall (Gstore Genv : tenv) (t : type) (e' : expr),
                        (synthesize_expr Gstore Genv (snd p) = Success (t, e') -> type_of Gstore Genv (snd p) t) /\
                          (analyze_expr Gstore Genv t (snd p) = Success e' -> type_of Gstore Genv (snd p) t))) l ->
        forall Gstore Genv kt vt l',
          dict_from' (List.map (fun '(k, v) => k' <- analyze_expr Gstore Genv kt k;; v' <- analyze_expr Gstore Genv vt v;; Success (k', v')) l) = Success l' -> Forall (fun p => type_of Gstore Genv (fst p) kt /\ type_of Gstore Genv (snd p) vt) l.
    Proof.
      induction l; simpl; intros.
      - apply Forall_nil.
      - repeat destruct_match. invert_result. inversion H; subst; simpl in *.
        constructor.
        + split; simpl.
          * apply H2 in E3. apply E3.
          * apply H2 in E4. apply E4.
        + eapply IHl; eauto.
    Qed.

    Lemma analyze_dict_body_sound : forall l,
        Forall (fun p =>
                  (forall (Gstore Genv : tenv) (t : type) (e' : expr),
                      (synthesize_expr Gstore Genv (fst p) = Success (t, e') -> type_of Gstore Genv (fst p) t) /\
                        (analyze_expr Gstore Genv t (fst p) = Success e' -> type_of Gstore Genv (fst p) t)) /\
                    (forall (Gstore Genv : tenv) (t : type) (e' : expr),
                        (synthesize_expr Gstore Genv (snd p) = Success (t, e') -> type_of Gstore Genv (snd p) t) /\
                          (analyze_expr Gstore Genv t (snd p) = Success e' -> type_of Gstore Genv (snd p) t))) l ->
        forall Gstore Genv kt vt e',
          analyze_dict_body analyze_expr Gstore Genv kt vt l = Success e' -> Forall (fun p => type_of Gstore Genv (fst p) kt /\ type_of Gstore Genv (snd p) vt) l.
    Proof.
      unfold analyze_dict_body, dict_from. intros.
      destruct_match. invert_result. eapply dict_from'_sound; eauto.
    Qed.

    Local Ltac unfold_typechecker := lazymatch goal with
                               | H: context [synthesize_expr _ _ ?e] |- _ => unfold synthesize_expr in H
                               | H: context [analyze_expr _ _ _ ?e] |- _ => unfold analyze_expr in H
                               end.

    Local Ltac unfold_fold_typechecker := repeat unfold_typechecker; fold synthesize_expr in *; fold analyze_expr in *.

    Lemma typechecker_sound : forall e Gstore Genv t e',
        (synthesize_expr Gstore Genv e = Success (t, e') -> type_of Gstore Genv e t) /\
          (analyze_expr Gstore Genv t e = Success e' -> type_of Gstore Genv e t).
    Proof.
      apply (expr_IH (fun e => forall (Gstore Genv : tenv) (t : type) (e' : expr),
  (synthesize_expr Gstore Genv e = Success (t, e') -> type_of Gstore Genv e t) /\
  (analyze_expr Gstore Genv t e = Success e' -> type_of Gstore Genv e t))); intros.
      - (* EVar *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; invert_result; constructor; easy.
      - (* ELoc *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; invert_result; constructor; easy.
      - (* EAtom *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; constructor;
          invert_result; apply atom_typechecker_sound in E; auto.
      - (* EUnop *)
        split; intros; destruct o; simpl in *;
          try (unfold_fold_typechecker; repeat destruct_match; try invert_result; apply_typechecker_IH;
               try invert_pair; repeat econstructor; eauto).
      - (* EBinop *)
        split; intros; destruct o; simpl in *;
          try (unfold_fold_typechecker; repeat destruct_match; try invert_result; repeat apply_typechecker_IH;
               try invert_pair; repeat econstructor; eauto).
      - (* EIf *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - (* ELet *)
        split; intros; unfold_fold_typechecker; repeat destruct_match;
          repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - (* EFlatmap *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - (* EFold *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - (* ERecord *)
        split; intros; unfold_fold_typechecker; repeat destruct_match.
        + unfold record_type_from in *. repeat destruct_match. invert_result.
          pose proof record_type_from'_sound. eapply H0 in H; eauto.
          apply TyERecord with (tl := l0); intuition;
          [ apply Permuted_record_sort | apply StronglySorted_record_sort ].
        + assert (type_eqb (TRecord l0) (TRecord (record_sort l0))); auto.
          apply type_eqb_eq in H1. injection H1; intro. unfold record_from in *. destruct_match. invert_result.
          pose proof record_from'_sound. eapply H0 in H; eauto.
          apply TyERecord with (tl := List.map (fun '(s, e) => (s, get_attr_type l0 s)) l); intuition.
          * rewrite Bool.andb_true_iff in E2. apply double_incl_NoDup_Permuted; intuition.
            apply leb_complete. repeat rewrite map_length. auto.
          * rewrite H2. apply StronglySorted_record_sort.
      - (* EAccess *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto;
          auto using proj_record_type_sound.
      - (* EDict *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; try invert_result; constructor;
        eapply analyze_dict_body_sound; eauto.
      - (* EInsert *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; repeat apply_typechecker_IH; invert_result; constructor; auto.
      - (* EDelete *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; repeat apply_typechecker_IH; invert_result; constructor; auto.
      - (* ELookup *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - (* EFilter *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - (* EJoin *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - (* EProj *)
        split; intros; unfold_fold_typechecker; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
    Qed.

    Local Ltac apply_type_sound_IH :=
      lazymatch goal with
      | H : (forall store env, well_formed_locals ?Gstore store ->
                               well_formed_locals ?Genv env -> _),
          H1: well_formed_locals ?Gstore _,
            H2: well_formed_locals ?Genv _ |- _ =>
          let H' := fresh "H'" in
          pose proof (H _ _ H1 H2) as H'; clear H; inversion H'; subst
      | H : (forall _ _, _ -> _ -> type_of_value (interp_expr _ _ ?e) ?t) |- type_of_value (interp_expr _ _ ?e) ?t =>
          apply H; try apply well_formed_locals_step
      end.

    Local Ltac apply_well_formed_locals :=
      match goal with
      | H : well_formed_locals ?G ?E, H' : map.get ?G ?x = _ |- _ =>
          apply H in H'; unfold get_local; destruct (map.get E x); intuition
      end.

    Local Ltac invert_Forall :=
      match goal with
      | H : Forall _ (_ :: _) |- _ => inversion H; subst
      end.

    Local Ltac destruct_exists :=
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

    Lemma In_fst : forall A B x (l : list (A * B)), In x (List.map fst l) -> exists p, In p l /\ fst p = x.
    Proof.
      induction l; simpl; intros; intuition.
      - exists a. intuition.
      - destruct H as [p H]; exists p; intuition.
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

    Lemma TyVDict_def : forall l tk tv, Forall (fun p => type_of_value (fst p) tk /\ type_of_value (snd p) tv) l <-> type_of_value (VDict l) (TDict tk tv).
    Proof.
      split; intros.
      - constructor; auto.
      - inversion H; intuition.
    Qed.

    Lemma record_proj_sound : forall l, NoDup (List.map fst l) ->
                                        forall tl, Forall2 (fun p tp => fst p = fst tp /\ type_of_value (snd p) (snd tp)) l tl ->
                                                   forall x t, In (x, t) tl ->
                                                               type_of_value (record_proj (width := width) x l) t.
    Proof.
      intros l Hnodup tl Hvt x t Hin. generalize dependent tl. induction l; intros; simpl in *.
      - inversion Hvt; subst. apply in_nil in Hin. intuition.
      - inversion Hvt; subst. destruct a. inversion Hin; subst.
        + destruct H1. simpl in *. subst. rewrite eqb_refl. auto.
        + simpl in *; inversion Hnodup; subst. assert (String.eqb x s = false).
          { apply in_map with (f := fst) in H; simpl in H. apply Forall2_split in H3 as [HL HR]. apply Forall2_fst_eq in HL.
            rewrite eqb_neq. intro contra; subst. rewrite HL in H4. intuition. }
          rewrite H0. eapply IHl; eauto.
    Qed.

    Lemma dict_insert_sound : forall l kt vt k v,
        type_of_value (VDict l) (TDict kt vt) ->
        type_of_value k kt ->
        type_of_value v vt ->
        type_of_value (VDict (dict_insert k v l)) (TDict kt vt).
    Proof.
      intros. induction l; constructor; simpl.
      - constructor; intuition.
      - destruct a as [k' v']. destruct (value_ltb k k'); [| destruct(value_eqb k k')]; inversion H.
        + auto.
        + inversion H4; auto.
        + inversion H4; subst; constructor; intuition.
          rewrite TyVDict_def. apply IHl. constructor. inversion H. intuition.
    Qed.

    Lemma dict_delete_sound : forall l kt vt k,
        type_of_value (VDict l) (TDict kt vt) ->
        type_of_value k kt ->
        type_of_value (VDict (dict_delete k l)) (TDict kt vt).
    Proof.
      intros; induction l; constructor; simpl.
      - constructor.
      - destruct a as [k' v']. destruct (value_eqb k k'); inversion H; inversion H3.
        + auto.
        + constructor; auto. try rewrite TyVDict_def in *. apply IHl; auto.
    Qed.

    Lemma dict_lookup_sound : forall l kt vt k,
        type_of_value (VDict l) (TDict kt vt) ->
        type_of_value k kt ->
        type_of_value (VOption (dict_lookup k l)) (TOption vt).
    Proof.
      intros; induction l.
      - constructor.
      - simpl. destruct a as [k' v']. destruct (value_eqb k k').
        + constructor. inversion H; inversion H3. intuition.
        + apply IHl. constructor. inversion H; inversion H3. auto.
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

    Lemma type_sound : forall Gstore Genv e t,
        type_of Gstore Genv e t ->
        forall store env,
        well_formed_locals Gstore store ->
        well_formed_locals Genv env ->
        type_of_value (interp_expr store env e) t.
    Proof.
      intros Gstore Genv e t H. apply (type_of_IH Gstore) with
        (P := fun Genv e t => forall store env,
        well_formed_locals Gstore store ->
        well_formed_locals Genv env ->
        type_of_value (interp_expr store env e) t); simpl; intros; auto.
      - apply_well_formed_locals.
      - apply_well_formed_locals.
      - match goal with H : type_of_atom _ _ |- _ => inversion H end; subst; constructor; apply Forall_nil.
      - inversion H0; subst; apply_type_sound_IH;
          simpl; repeat constructor; auto.
      - inversion H0; subst; repeat apply_type_sound_IH;
          simpl; repeat constructor; auto.
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
      - repeat apply_type_sound_IH;
        match goal with
        | |- type_of_value (if ?b then _ else _) _ => destruct b; constructor; auto
        end.
      - repeat apply_type_sound_IH; auto; constructor; auto.
      - repeat apply_type_sound_IH.
        clear H1. constructor. induction l; simpl.
        + apply Forall_nil.
        + apply Forall_app; split.
          * invert_Forall.
            assert (type_of_value (interp_expr store (map.put env x a) e2) (TList t2)).
            { apply_type_sound_IH; auto. }
            inversion H1; auto.
          * apply IHl. inversion H7. assumption.
      - repeat apply_type_sound_IH;
          try (match goal with
               | H: VList ?l = _ |- _ => clear H
               end; induction l; simpl; try constructor; auto; apply_type_sound_IH; auto;
               match goal with
               | H: Forall _ (_ :: _) |- _ => inversion H; subst
               end;
             repeat apply well_formed_locals_step; auto);
          try (clear H1; induction l0; simpl; try constructor; auto;
           apply_type_sound_IH; auto;
           match goal with
           | H: Forall _ (_ :: _) |- _ => inversion H; subst
           end;
           repeat apply well_formed_locals_step; auto).
      - constructor.
        + apply Permutation_NoDup with (l := List.map fst (List.map (fun '(s, e0) => (s, interp_expr store env e0)) l)).
          * apply Permutation_map. apply Permuted_record_sort.
          * rewrite fst_map_fst. auto.
        + apply StronglySorted_record_sort.
        + remember (fun p tp => fst p = fst tp /\ type_of_value (snd p) (snd tp)) as R.
          assert (Forall2 R (List.map (fun '(s, e0) => (s, interp_expr store env e0)) l) tl).
          { generalize dependent H0; generalize dependent H2; generalize dependent H6; generalize dependent H7; generalize dependent HeqR.
            clear. intros H0 H1 H2 H3 H4. generalize dependent tl.
            induction l; simpl; intros; destruct tl; try discriminate.
            - intuition.
            - destruct a, p; simpl in *; subst. constructor.
              + simpl. split; try congruence. inversion H3; subst. apply H6; auto.
              + apply IHl; inversion H3; inversion H4; intuition.
          }
          eapply Forall2_Permuted_StronglySorted; eauto.
          * rewrite fst_map_fst; auto.
          * subst; intuition.
          * apply Permuted_record_sort.
          * apply StronglySorted_record_sort.
      - repeat apply_type_sound_IH. eapply record_proj_sound; eauto.
      - constructor. rewrite Forall_forall in *.

        assert (forall p, In p (List.map (fun '(k, v) => (interp_expr store env k, interp_expr store env v)) l) -> type_of_value (fst p) kt /\ type_of_value (snd p) vt).
         { induction l; intros; simpl in *; try now (exfalso; auto).
           inversion H4.
           - pose proof (H1 a). intuition; destruct a; subst; simpl in *;
               try apply H4; try apply H9; auto.
           - apply IHl; auto. }
        intros. apply H4. pose proof (Permuted_dict_sort (width:=width)).
        eapply Permutation_in; [ apply Permutation_sym |]; eauto.
      - repeat apply_type_sound_IH; apply dict_insert_sound; constructor; auto.
      - repeat apply_type_sound_IH; apply dict_delete_sound; constructor; auto.
      - repeat apply_type_sound_IH; eapply dict_lookup_sound; econstructor; eauto.
      - repeat apply_type_sound_IH. constructor. apply Forall_Forall_filter. auto.
      - repeat apply_type_sound_IH.
        rewrite <- H1 in H'0. eapply flat_map_type_sound; eauto. intros.
        apply map_type_sound with (t := t2).
        + constructor; apply Forall_Forall_filter; auto.
        + intuition. repeat apply_type_sound_IH; repeat apply well_formed_locals_step; auto.
      - repeat apply_type_sound_IH.
        apply map_type_sound with (t := t1).
        + constructor. auto.
        + intros; repeat apply_type_sound_IH; repeat apply well_formed_locals_step; auto.
    Qed.
  End WithMap.
End WithWord.
