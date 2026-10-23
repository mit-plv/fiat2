Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils fiat2.IndexInterface.
Require Import coqutil.Map.Interface.
From Stdlib Require Import List String ZArith Morphisms.
Import ListNotations.

Section WithMap.
  Notation value := (value).
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

  (* An assumption about the store and the environment a command runs in: the
     path condition that reaching the command establishes.  CIf is the only
     form that strengthens it, and it can because its branches run in exactly
     the store and environment the test was evaluated in.  Every other form
     runs its subcommand in a store or environment the surrounding tests say
     nothing about, so it drops the assumption.

     This one rule is what lets a program, rather than the optimizer, establish
     an invariant that an index depends on: the obligation at an assignment
     receives the truth of the guard it sits under, so

       CIf guard (CAssign x e) policy

     is well formed as soon as the guard implies the invariant of the value
     being written -- which is far weaker than asking it of e on its own. *)
  Inductive parameterized_wf (Gstore Genv : tenv) (P : string -> value -> Prop)
    : (locals -> locals -> Prop) -> command -> Prop :=
  | PWCSkip A : parameterized_wf Gstore Genv P A CSkip
  | PWCSeq A c1 c2 : parameterized_wf Gstore Genv P A c1 ->
                     parameterized_wf Gstore Genv P (fun _ _ => True) c2 ->
                     parameterized_wf Gstore Genv P A (CSeq c1 c2)
  | PWCLet A e t x c : type_of Gstore Genv e t ->
                       parameterized_wf Gstore (map.put Genv x t) P (fun _ _ => True) c ->
                       parameterized_wf Gstore Genv P A (CLet e x c)
  | PWCLetMut A e t x c :
    type_of Gstore Genv e t ->
    parameterized_wf (map.put Gstore x t) Genv (rm_from_pred P x) (fun _ _ => True) c ->
    parameterized_wf Gstore Genv P A (CLetMut e x c)
  | PWCAssign A x t e :
    (forall store env, A store env ->
                       holds_for_all_entries P store ->
                       locals_wf Gstore store -> locals_wf Genv env ->
                       P x (interp_expr store env e)) ->
    map.get Gstore x = Some t ->
    type_of Gstore Genv e t ->
    parameterized_wf Gstore Genv P A (CAssign x e)
  | PWCIf A e c1 c2 :
    type_of Gstore Genv e TBool ->
    parameterized_wf Gstore Genv P
      (fun store env => A store env /\ interp_expr store env e = VBool true) c1 ->
    parameterized_wf Gstore Genv P
      (fun store env => A store env /\ interp_expr store env e = VBool false) c2 ->
    parameterized_wf Gstore Genv P A (CIf e c1 c2)
  | PWCForeach A e t x c : type_of Gstore Genv e (TList t) ->
                           parameterized_wf Gstore (map.put Genv x t) P (fun _ _ => True) c ->
                           parameterized_wf Gstore Genv P A (CForeach e x c).

  Lemma parameterized_wf__well_typed : forall Gstore Genv P A c,
      parameterized_wf Gstore Genv P A c -> well_typed Gstore Genv c.
  Proof.
    intros. induction H.
    all: econstructor; eauto.
  Qed.

  (* A stronger assumption only makes the obligations easier.  The implication
     may itself assume the well-formedness conditions, since those are
     available everywhere the assumption is used. *)
  Lemma parameterized_wf_weaken : forall Gstore Genv P A A' c,
      (forall store env,
          locals_wf Gstore store -> locals_wf Genv env ->
          holds_for_all_entries P store ->
          A' store env -> A store env) ->
      parameterized_wf Gstore Genv P A c ->
      parameterized_wf Gstore Genv P A' c.
  Proof.
    intros * H_imp H_wf. generalize dependent A'.
    induction H_wf; intros.
    (* CSkip, CSeq, CLet, CLetMut and CForeach mention the assumption nowhere,
       and every subcommand of theirs but CSeq's first carries none *)
    1-4,7: econstructor; eauto.
    1:{ (* CAssign: strengthen the assumption, then use the original obligation *)
        econstructor.
        2,3: eassumption.
        intros * H_A' ? ? ?. apply H; auto. }
    1:{ (* CIf: both branch assumptions are strengthened the same way *)
        econstructor.
        1: eassumption.
        1: apply IHH_wf1. 2: apply IHH_wf2.
        all: intros * ? ? ? [? ?]; split; auto. }
  Qed.

  (* Every derivation built without a path condition is usable under any. *)
  Corollary parameterized_wf_no_cond : forall Gstore Genv P A c,
      parameterized_wf Gstore Genv P (fun _ _ => True) c ->
      parameterized_wf Gstore Genv P A c.
  Proof.
    intros * H. eapply parameterized_wf_weaken with (A := fun _ _ => True).
    2: exact H.
    intros; exact I.
  Qed.

  Lemma parameterized_wf__preserve_P : forall Gstore Genv P A c,
      tenv_wf Gstore -> tenv_wf Genv ->
      parameterized_wf Gstore Genv P A c ->
      forall store env,
        A store env ->
        locals_wf Gstore store -> locals_wf Genv env ->
        holds_for_all_entries P store ->
        holds_for_all_entries P (interp_command store env c).
  Proof.
    intros * ? ? H_wf. induction H_wf; simpl; auto; intros.
    1:{ (* CSeq: c2 runs in the store c1 produced, so it carries no assumption *)
        assert (H_c1 : locals_wf Gstore (interp_command store env c1))
          by (eapply command_type_sound; eauto using parameterized_wf__well_typed).
        assert (H_P1 : holds_for_all_entries P (interp_command store env c1))
          by (apply IHH_wf1; auto).
        apply IHH_wf2; auto. }
    1:{ apply IHH_wf; eauto with fiat2_hints. }
    1:{ unfold holds_for_all_entries. intros. get_update_same_diff x k.
        1:{ rewrite Properties.map.get_update_same in *. auto. }
        1:{ rewrite Properties.map.get_update_diff in *; try congruence.
            unfold rm_from_pred in *.
            lazymatch goal with
              H: map.get (interp_command _ _ _) _ = Some _ |- _ =>
                apply IHH_wf in H; eauto with fiat2_hints
            end.
            1:{ intuition auto. congruence. }
            unfold holds_for_all_entries; intros.
            get_put_same_diff x k0; rewrite_map_get_put_hyp. } }
    1:{ unfold holds_for_all_entries; intros.
        get_put_same_diff x k; rewrite_map_get_put_hyp.
        do_injection. apply H1; auto. }
    1:{ (* CIf: each branch runs under the outcome of the test *)
        apply_type_sound e. invert_type_of_value.
        lazymatch goal with H: VBool _ = interp_expr _ _ e |- _ => symmetry in H end.
        destruct b.
        1: apply IHH_wf1; auto.
        1: apply IHH_wf2; auto. }
    1:{ (* CForeach: the body runs once per row, each in a different store *)
        apply_type_sound e. invert_type_of_value.
        lazymatch goal with H: type_of_value _ _ |- _ => clear H end.
        lazymatch goal with H: VList _ = interp_expr _ _ e |- _ => clear H end.
        (* the body carries no assumption, so the induction over the rows need
           not keep the one this command was reached under *)
        lazymatch goal with H: A _ _ |- _ => clear H end.
        generalize dependent store. induction l; simpl; auto; intros.
        invert_Forall; apply IHl; auto.
        2:{ apply IHH_wf; eauto with fiat2_hints. }
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

  Lemma iff2_parameterized_wf : forall x y A z P Q,
      iff2 P Q ->
      parameterized_wf x y P A z -> parameterized_wf x y Q A z.
  Proof.
    intros * H_iff2 H_wf. generalize dependent Q.
    induction H_wf; intros.
    all: econstructor; eauto.
    1:{ apply IHH_wf. erewrite H_iff2; auto using iff2_refl. }
    1:{ intros. apply H_iff2, H; auto.
        rewrite H_iff2; auto. }
  Qed.

  Instance parameterized_wf_Proper : Proper (eq ==> eq ==> iff2 ==> eq ==> eq ==> iff) parameterized_wf.
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
      2: apply IHForall2; intuition auto with *.
      rewrite map.get_put_diff; intuition idtac.
      lazymatch goal with H: _ -> False |- _ => apply H end.
      constructor; auto.
    Qed.

    Lemma not_In__tenv_wf_with_globals : forall x t Gstore,
        ~ In x globals -> tenv_wf_with_globals Gstore -> tenv_wf_with_globals (map.put Gstore x t).
    Proof.
      intros * H_not_in H. unfold tenv_wf_with_globals in *.
      induction H; auto.
      constructor. 2: apply IHForall2; intuition auto with *.
      rewrite map.get_put_diff; intuition idtac.
      apply H_not_in; subst; intuition auto with *.
    Qed.
  End WithGlobals.

  Section WithIndex.
    Context (is_tbl_ty : type -> bool) (aux_ty : type -> type) (aux_wf : value -> Prop).

  Definition expr_aug_transf_sound (f : string -> expr -> expr) : Prop :=
    forall Gstore Genv tbl tbl_ty e t,
      tenv_wf Gstore -> tenv_wf Genv ->
      type_wf tbl_ty -> is_tbl_ty tbl_ty = true ->
      tenv_wf_with_globals [tbl] [aux_ty tbl_ty] Gstore ->
      type_of Gstore Genv e t ->
      type_of Gstore Genv (f tbl e) t /\
        forall store env,
          locals_wf Gstore store -> locals_wf Genv env ->
          holds_for_all_entries (value_wf_with_globals aux_wf [tbl]) store ->
          interp_expr store env (f tbl e) = interp_expr store env e.

    Definition aug_transf_sound (f : string -> command -> command) : Prop :=
      forall Gstore Genv tbl t c,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_wf t -> is_tbl_ty t = true ->
        tenv_wf_with_globals [tbl] [aux_ty t] Gstore ->
        well_typed Gstore Genv c ->
        parameterized_wf Gstore Genv (value_wf_with_globals aux_wf [tbl]) (fun _ _ => True) c ->
        well_typed Gstore Genv (f tbl c) /\
          parameterized_wf Gstore Genv (value_wf_with_globals aux_wf [tbl]) (fun _ _ => True) (f tbl c) /\
          forall store env,
            locals_wf Gstore store -> locals_wf Genv env ->
            holds_for_all_entries (value_wf_with_globals aux_wf [tbl]) store ->
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

    Lemma expr_transf_sound__expr_aug_transf_sound : forall (f : expr -> expr),
        expr_transf_sound f ->
        expr_aug_transf_sound (fun _ => f).
    Proof.
      unfold expr_transf_sound, expr_aug_transf_sound; intros;
        apply H in H5; intuition auto.
    Qed.
  End WithIndex.

  (* An expression rule may be used where MORE is known about the table than
     it was proved against.

     aug_transf_sound is not monotone in aux_wf either way, since it both
     assumes and re-establishes the parameterized_wf the predicate appears in.
     An expression rule only ever assumes it, so a rule proved against a
     record of ordinary indexes keeps working in a record that also carries a
     declared index's invariant -- which is what lets indexes that need a
     declaration and indexes that do not share one record. *)
  Lemma expr_aug_transf_sound_strengthen_wf :
    forall is_tbl_ty aux_ty (P Q : value -> Prop) f,
      (forall v, Q v -> P v) ->
      expr_aug_transf_sound is_tbl_ty aux_ty P f ->
      expr_aug_transf_sound is_tbl_ty aux_ty Q f.
  Proof.
    unfold expr_aug_transf_sound; intros * H_imp H_f * H_Gs H_Ge H_twf H_tbl H_glob H_t.
    specialize (H_f _ _ _ _ _ _ H_Gs H_Ge H_twf H_tbl H_glob H_t).
    destruct H_f as [ H_ty H_sem ]; split; [ exact H_ty | ].
    intros store env H_lws H_lwe H_inv.
    apply H_sem; auto.
    unfold holds_for_all_entries, value_wf_with_globals in *.
    intros k v E_k. specialize (H_inv _ _ E_k).
    eapply Forall_impl; [ | exact H_inv ].
    intros tbl' [ H_ne | H_q ]; [ left; exact H_ne | right; apply H_imp; exact H_q ].
  Qed.

  Fixpoint repeat_transf (f : command -> command) (n : nat) :=
    match n with
    | O => id
    | S n => Basics.compose f (repeat_transf f n)
    end.

  Lemma repeat_transf_preserve_aug_transf_sound : forall is_tbl_ty aux_ty aux_wf f n,
      aug_transf_sound is_tbl_ty aux_ty aux_wf f ->
      aug_transf_sound is_tbl_ty aux_ty aux_wf (fun tbl => repeat_transf (f tbl) n).
  Proof.
    induction n; cbn.
    1:{ intros _. unfold aug_transf_sound; auto. }
    1:{ intros; cbn. apply aug_transf_sound_compose; auto. }
  Qed.
End WithMap.

#[export] Hint Resolve transf_sound_compose : transf_hints.
#[export] Hint Resolve aug_transf_sound_compose : transf_hints.
#[export] Hint Resolve expr_transf_sound__expr_aug_transf_sound : transf_hints.
