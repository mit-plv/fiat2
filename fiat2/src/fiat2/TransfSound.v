Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils fiat2.IndexInterface.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import List String ZArith Morphisms.
Import ListNotations.

Section WithMap.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).
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

  Definition holds_for_all_entries {A : Type} {m : map.map string A} (P : string -> A -> Prop) (G : m) :=
    forall k v, map.get G k = Some v -> P k v.

  Definition rm_from_pred (P : string -> value -> Prop) (x : string) :=
    fun s v => s = x \/ P s v.

  Inductive parameterized_wf (Gstore Genv : tenv) (P : string -> value -> Prop) : command -> Prop :=
  | PWCSkip : parameterized_wf Gstore Genv P CSkip
  | PWCSeq c1 c2 : parameterized_wf Gstore Genv P c1 ->
                   parameterized_wf Gstore Genv P c2 ->
                   parameterized_wf Gstore Genv P (CSeq c1 c2)
  | PWCLet e t x c : type_of Gstore Genv e t ->
                     parameterized_wf Gstore (map.put Genv x t) P c ->
                     parameterized_wf Gstore Genv P (CLet e x c)
  | PWCLetMut e t x c :
    type_of Gstore Genv e t ->
    parameterized_wf (map.put Gstore x t) Genv (rm_from_pred P x) c ->
    parameterized_wf Gstore Genv P (CLetMut e x c)
  | PWCAssign x t e :
    (forall store env, holds_for_all_entries P store ->
                       locals_wf Gstore store -> locals_wf Genv env ->
                       P x (interp_expr store env e)) ->
    map.get Gstore x = Some t ->
    type_of Gstore Genv e t ->
    parameterized_wf Gstore Genv P (CAssign x e)
  | PWCIf e c1 c2 : type_of Gstore Genv e TBool ->
                    parameterized_wf Gstore Genv P c1 ->
                    parameterized_wf Gstore Genv P c2 ->
                    parameterized_wf Gstore Genv P (CIf e c1 c2)
  | PWCForeach e t x c : type_of Gstore Genv e (TList t) ->
                         parameterized_wf Gstore (map.put Genv x t) P c ->
                         parameterized_wf Gstore Genv P (CForeach e x c).

  Lemma parameterized_wf__well_typed : forall Gstore Genv P c,
      parameterized_wf Gstore Genv P c -> well_typed Gstore Genv c.
  Proof.
    intros. induction H.
    all: econstructor; eauto.
  Qed.

  Lemma parameterized_wf__preserve_P : forall Gstore Genv store env P c,
      tenv_wf Gstore -> tenv_wf Genv ->
      parameterized_wf Gstore Genv P c ->
      locals_wf Gstore store -> locals_wf Genv env ->
      holds_for_all_entries P store ->
      holds_for_all_entries P (interp_command store env c).
  Proof.
    intros. generalize dependent store; generalize dependent env.
    induction H1; simpl; auto; intros.
    1:{ apply IHparameterized_wf2; auto. eapply command_type_sound; eauto.
        eapply parameterized_wf__well_typed; eauto. }
    1:{ apply IHparameterized_wf; eauto with fiat2_hints. }
    1:{ unfold holds_for_all_entries. intros. get_update_same_diff x k.
        1:{ rewrite Properties.map.get_update_same in *. auto. }
        1:{ rewrite Properties.map.get_update_diff in *; try congruence.
            unfold rm_from_pred in *.
            apply IHparameterized_wf in H6; eauto with fiat2_hints.
            1:{ intuition auto. congruence. }
            unfold holds_for_all_entries; intros.
            get_put_same_diff x k0; rewrite_map_get_put_hyp. } }
    1:{ unfold holds_for_all_entries; intros.
        get_put_same_diff x k; rewrite_map_get_put_hyp.
        do_injection. apply H1; auto. }
    1:{ apply_type_sound e. invert_type_of_value. case_match; auto. }
    1:{ apply_type_sound e. invert_type_of_value. clear H' H6.
        generalize dependent store. induction l; simpl; auto; intros.
        invert_Forall; apply IHl; auto.
        2:{ apply IHparameterized_wf; eauto with fiat2_hints. }
        eapply command_type_sound.
        5: apply locals_wf_step. all: eauto with fiat2_hints.
        eapply parameterized_wf__well_typed; eauto. }
  Qed.

  Definition iff2 {A B} (P Q : A -> B -> Prop) :=
    forall a b, P a b <-> Q a b.

  Lemma iff2_refl : forall A B (P : A -> B -> Prop),
      iff2 P P.
  Proof.
    unfold iff2; intros; intuition auto.
  Qed.

  Lemma iff2_sym : forall A B (P Q : A -> B -> Prop),
      iff2 P Q -> iff2 Q P.
  Proof.
    unfold iff2; intros; apply iff_sym; auto.
  Qed.

  Lemma iff2_trans : forall A B (P Q R : A -> B -> Prop),
      iff2 P Q -> iff2 Q R -> iff2 P R.
  Proof.
    unfold iff2; split; intros.
    1: apply H0, H; auto.
    1: apply H, H0; auto.
  Qed.

  Add Parametric Relation A B : (A -> B -> Prop) iff2
      reflexivity proved by (iff2_refl A B)
      symmetry proved by (iff2_sym A B)
      transitivity proved by (iff2_trans A B)
      as iff2_rel.

  Instance rm_from_pred_Proper : Proper (iff2 ==> eq ==> iff2) rm_from_pred.
  Proof.
    intros P Q H x x' Hx.
    unfold iff2, rm_from_pred; intros.
    subst; intuition auto.
    all: right; apply H; auto.
  Qed.

  Instance holds_for_all_entries_Proper {A : Type} {m : map.map string A} : Proper (iff2 ==> eq ==> iff) (holds_for_all_entries (m:=m)).
  Proof.
    intros P Q H x x' Hx.
    unfold holds_for_all_entries. split; intros.
    all: subst; apply H, H0; auto.
  Qed.

  Lemma iff2_parameterized_wf : forall x y z P Q,
      iff2 P Q ->
      parameterized_wf x y P z -> parameterized_wf x y Q z.
  Proof.
    intros * H_iff2 H_wf. generalize dependent Q.
    induction H_wf; intros.
    all: econstructor; eauto.
    1:{ apply IHH_wf. erewrite H_iff2; auto using iff2_refl. }
    1:{ intros. apply H_iff2, H; auto.
        rewrite H_iff2; auto. }
  Qed.

  Instance parameterized_wf_Proper : Proper (eq ==> eq ==> iff2 ==> eq ==> iff) parameterized_wf.
  Proof.
    intros x x' Hx y y' Hy P Q H z z' Hz.
    split; subst; apply iff2_parameterized_wf;
      auto using iff2_sym.
  Qed.

  Section WithPv.
    Context (Pv : value -> Prop).

    Definition value_wf_with_globals globals (x : string) (v : value) :=
      Forall (fun tbl => x <> tbl \/ Pv v) globals.

    Lemma not_In__value_wf_with_globals : forall x globals (store : locals) v,
        ~In x globals ->
        holds_for_all_entries (value_wf_with_globals globals) store ->
        holds_for_all_entries (value_wf_with_globals globals) (map.put store x v).
    Proof.
      unfold holds_for_all_entries; intros.
      unfold value_wf_with_globals in *.
      destruct (String.eqb k x) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst; rewrite_map_get_put_hyp.
      rewrite Forall_forall; intros. left; intro contra; subst; auto.
    Qed.

    Lemma rm_not_in_globals : forall x globals,
        ~In x globals ->
        iff2 (rm_from_pred (value_wf_with_globals globals) x) (value_wf_with_globals globals).
    Proof.
      unfold iff2, rm_from_pred, value_wf_with_globals; intros.
      induction globals; intuition auto; subst.
      rewrite Forall_forall; intros.
      left. intro contra; subst; auto.
    Qed.
  End WithPv.

  Section WithGlobals.
    Context (globals : list string).
    Context (global_types : list type) (global_types_ok : List.length globals = List.length global_types).

    Definition tenv_wf_with_globals Gstore :=
      Forall2 (fun x t => map.get Gstore x = Some t) globals global_types.

    Lemma tenv_wf_with_globals_step : forall Gstore x t,
        tenv_wf_with_globals Gstore ->
        ~ In x globals ->
        tenv_wf_with_globals (map.put Gstore x t).
    Proof.
      intros * H ?. unfold tenv_wf_with_globals in *.
      induction H; auto. constructor.
      2: apply IHForall2; intuition.
      rewrite map.get_put_diff; intuition.
      lazymatch goal with H: _ -> False |- _ => apply H end.
      constructor; auto.
    Qed.

    Lemma not_In__tenv_wf_with_globals : forall x t Gstore,
        ~ In x globals -> tenv_wf_with_globals Gstore -> tenv_wf_with_globals (map.put Gstore x t).
    Proof.
      intros * H_not_in H. unfold tenv_wf_with_globals in *.
      induction H; auto.
      constructor. 2: apply IHForall2; intuition.
      rewrite map.get_put_diff; intuition.
      apply H_not_in; subst; intuition.
    Qed.
  End WithGlobals.

  Section WithIndex.
    Context {consistency : Type} (consistent : consistency -> value -> value -> Prop).
    Context {to_from_con from_to_con : consistency}.
    Context {idx : IndexInterface.index} {idx_wf : value -> Prop} {idx_ok : ok to_from_con from_to_con idx idx_wf consistent}.

    Definition expr_aug_transf_sound (f : string -> expr -> expr) : Prop :=
      forall Gstore Genv tbl tbl_ty e t,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_wf tbl_ty -> is_tbl_ty tbl_ty = true ->
        tenv_wf_with_globals [tbl] [idx_ty tbl_ty] Gstore ->
        type_of Gstore Genv e t ->
        type_of Gstore Genv (f tbl e) t /\
          forall store env,
            locals_wf Gstore store -> locals_wf Genv env ->
            holds_for_all_entries (value_wf_with_globals idx_wf [tbl]) store ->
            interp_expr store env (f tbl e) = interp_expr store env e.

    Definition aug_transf_sound (f : string -> command -> command) : Prop :=
      forall Gstore Genv tbl t c,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_wf t -> is_tbl_ty t = true ->
        tenv_wf_with_globals [tbl] [idx_ty t] Gstore ->
        well_typed Gstore Genv c ->
        parameterized_wf Gstore Genv (value_wf_with_globals idx_wf [tbl]) c ->
        well_typed Gstore Genv (f tbl c) /\
          parameterized_wf Gstore Genv (value_wf_with_globals idx_wf [tbl]) (f tbl c) /\
          forall store env,
            locals_wf Gstore store -> locals_wf Genv env ->
            holds_for_all_entries (value_wf_with_globals idx_wf [tbl]) store ->
            interp_command store env (f tbl c) = interp_command store env c.

    Lemma aug_transf_sound_compose : forall f g,
        aug_transf_sound f -> aug_transf_sound g ->
        aug_transf_sound (fun x => Basics.compose (f x) (g x)).
    Proof.
      unfold aug_transf_sound; intros * H_f H_g; intros.
      eapply H_g in H4; eauto; repeat destruct_and.
      eapply H_f in H4; eauto; intuition idtac.
      rewrite H10; auto.
    Qed.
  End WithIndex.
End WithMap.

#[export] Hint Resolve transf_sound_compose : transf_hints.
#[export] Hint Resolve aug_transf_sound_compose : transf_hints.
