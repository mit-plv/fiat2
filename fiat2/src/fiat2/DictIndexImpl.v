Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.Examples fiat2.TypeSystem fiat2.TypeSound fiat2.CollectionTag fiat2.IndexInterface.
Require Import List String ZArith Permutation.
Import ListNotations.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Import ResultMonadNotations.
Require Import Sorted.
Require Import Morphisms.
Require Import Ltac2.Ltac2 Ltac2.Control Ltac2.Constr.

Set Default Proof Mode "Classic".

Open Scope string_scope.

Create HintDb fiat2_hints.

Ltac invert_type_wf :=
  lazymatch goal with
  | H: type_wf (TList ?t) |- _ => inversion H; clear H; subst
  | H: type_wf (TOption ?t) |- _ => inversion H; clear H; subst
  | H: type_wf (TDict ?t _) |- _ => inversion H; clear H; subst
  | H: type_wf (TDict _ ?t) |- _ => inversion H; clear H; subst
  | H: type_wf (TRecord ?tl) |- _ => inversion H; clear H; subst
  end.

Lemma invert_TList_wf: forall t, type_wf (TList t) -> type_wf t.
Proof.
  intros. invert_type_wf; auto.
Qed.

Lemma invert_TOption_wf: forall t, type_wf (TOption t) -> type_wf t.
Proof.
  intros. invert_type_wf; auto.
Qed.

Lemma invert_TDict_wf_l: forall kt vt, type_wf (TDict kt vt) -> type_wf kt.
Proof.
  intros. invert_type_wf; auto.
Qed.

Lemma invert_TDict_wf_r: forall kt vt, type_wf (TDict kt vt) -> type_wf vt.
Proof.
  intros. invert_type_wf; auto.
Qed.

Lemma invert_TRecord_wf: forall tl, type_wf (TRecord tl) -> Forall type_wf (List.map snd tl).
Proof.
  intros. invert_type_wf; auto.
Qed.

Hint Resolve invert_TList_wf : fiat2_hints.
Hint Resolve invert_TOption_wf : fiat2_hints.
Hint Resolve invert_TDict_wf_l : fiat2_hints.
Hint Resolve invert_TDict_wf_r : fiat2_hints.
Hint Resolve invert_TRecord_wf : fiat2_hints.
Hint Resolve type_of__type_wf : fiat2_hints.
Hint Resolve tenv_wf_step : fiat2_hints.
Hint Resolve locals_wf_step : fiat2_hints.
Hint Resolve tenv_wf_empty : fiat2_hints.
Hint Resolve locals_wf_empty : fiat2_hints.
Hint Resolve type_sound : fiat2_hints.

Definition epair (e1 e2 : expr) := ERecord [("0", e1); ("1", e2)].
Definition ofst (e : expr) : expr := EAccess e "0".
Definition osnd (e : expr) : expr := EAccess e "1".
Definition enil := EAtom (ANil None).
Definition econs (e1 e2 : expr) := EBinop OCons e1 e2.
Definition cons_to_fst (e1 e2 : expr) :=
  epair (econs e1 (ofst e2)) (osnd e2).

Fixpoint is_NoDup {A} (l : list A) : Prop :=
  match l with
  | nil => True
  | x :: l => ~ In x l /\ is_NoDup l
  end.

Ltac rewrite_map_get_put_hyp :=
  multimatch goal with
  | H: context[map.get (map.put _ ?x _) ?x] |- _ =>
      rewrite map.get_put_same in H
  | H: context[map.get (map.put _ _ _) _] |- _ =>
      rewrite map.get_put_diff in H; try now (simpl in *; intuition)
  end.

Ltac rewrite_map_get_put_goal :=
  multimatch goal with
  | |- context[map.get (map.put _ ?x _) ?x] =>
      rewrite map.get_put_same
  | |- context[map.get (map.put _ _ _) _] =>
      rewrite map.get_put_diff; try now (simpl in *; intuition)
  end.

Ltac rewrite_l_to_r :=
  lazymatch goal with
  | H: ?x = _ |- context[?x] => rewrite H
  | H: ?x = _, H': context[?x] |- _ => rewrite H in H'
  end.

Ltac rewrite_r_to_l :=
  lazymatch goal with
  | H: _ = ?x, H': context[?x] |- _ => rewrite <- H in H'
  | H: _ = ?x|- context[?x] => rewrite <- H
  end.

Ltac apply_Forall_In :=
  lazymatch goal with
  | H1: Forall _ ?l, H2: In _ ?l |- _ => eapply List.Forall_In in H1; eauto
  end.

Ltac destruct_match_hyp :=
  lazymatch goal with
    H: context[match ?x with _ => _ end] |- _ =>
      let E := fresh "E" in
      destruct x eqn:E end.

Ltac destruct_exists :=
  lazymatch goal with
    H: exists _, _ |- _ => destruct H end.

Ltac destruct_and :=
  lazymatch goal with
    H: _ /\ _ |- _ => destruct H end.

Ltac invert_type_of_value :=
  lazymatch goal with
  | H: type_of_value (_ _) _ |- _ =>
      inversion H; subst
  | H: type_of_value ?v (_ _) |- context[?v] =>
      inversion H; subst
  end.

Ltac invert_type_of_value_clear :=
  lazymatch goal with
  | H: type_of_value (_ _) _ |- _ =>
      inversion H; subst; clear H
  | H: type_of_value _ (_ _) |- _ =>
      inversion H; subst; clear H
  end.

Ltac invert_type_of_the_value v :=
  lazymatch goal with
    H: type_of_value v _ |- _ =>
      inversion H; subst
  end.

Ltac invert_well_typed :=
  lazymatch goal with
    H: well_typed _ _ _ |- _ => inversion H; subst; clear H end.

Ltac invert_type_of :=
  lazymatch goal with
  | H: type_of _ _ (_ _) _ |- _ => inversion H; subst; clear H
  | H: type_of_binop _ _ _ _ |- _ => inversion H; subst; clear H
  end.

Ltac invert_type_of_atom :=
  lazymatch goal with
    H: type_of_atom _ _ |- _ => inversion H; subst end.

Ltac invert_Forall2 :=
  lazymatch goal with
  | H: Forall2 _ _ (_ :: _) |- _ => inversion H; subst; clear H
  | H: Forall2 _ _ nil |- _ => inversion H; subst; clear H
  | H: Forall2 _ _ _ |- _ => inversion H; subst; clear H
  end.

Ltac case_match' c :=
  lazymatch c with
  | context [match ?c' with _ => _ end] => case_match' c'
  | _ =>
      let E := fresh "E" in
      destruct c eqn:E
  end.

Ltac case_match :=
  match goal with
  | |- context [ match ?e with
                 | _ => _
                 end ] => case_match' e
  end.

Ltac clear_refl := lazymatch goal with H: ?x = ?x |- _ => clear H end.

Ltac iter_hyps tac :=
  let iter := ltac2:(tac |- List.iter (fun (h, _ , t) =>
                                         ltac1:(h t tac|- tac h t)
                                                 (Ltac1.of_constr (Unsafe.make (Unsafe.Var h)))
                                                 (Ltac1.of_constr t)
                                                 tac)
                              (hyps ())) in
  iter tac.
Ltac do_injection' h t :=
  try lazymatch t with
    | ?x _ = ?x _ => injection h; intros; subst
    end.

Ltac do_injection := iter_hyps do_injection'.

Ltac invert_Forall :=
  lazymatch goal with
  | H: Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  end.

Ltac invert_NoDup :=
  lazymatch goal with H: NoDup (_ :: _) |- _ => inversion H; subst end.

Ltac invert_SSorted :=
  lazymatch goal with
  | H: StronglySorted _ (_ :: _) |- _ => inversion H; subst
  end.

Ltac get_update_same_diff x y :=
  let E := fresh "E" in
  destruct (String.eqb x y) eqn:E;
  [ rewrite eqb_eq in E; subst; repeat rewrite Properties.map.get_update_same
  | rewrite eqb_neq in E; repeat rewrite Properties.map.get_update_diff ]; auto.

Ltac get_put_same_diff x y :=
  let E := fresh "E" in
  destruct (String.eqb x y) eqn:E;
  [ rewrite eqb_eq in E; subst; repeat rewrite map.get_put_same
  | rewrite eqb_neq in E; repeat rewrite map.get_put_diff ]; auto.

Ltac apply_type_sound e :=
  lazymatch goal with
  | H: type_of _ _ e _ |- _ =>
      let H' := fresh "H'" in
      eapply type_sound in H as H'; eauto; try inversion H'; subst; auto
  end.

Lemma In_access_record : forall A l attr, In attr (List.map fst l) -> exists (x : A), access_record l attr = Success x.
Proof.
  induction l; simpl; intros.
  - intuition eauto.
  - destruct a; simpl in *. destruct (eqb attr s) eqn:E.
    + exists a. reflexivity.
    + rewrite eqb_neq in *. intuition. congruence.
Qed.

Lemma get_attr_type_ty_wf : forall rt attr,
    type_wf (TRecord rt) ->
    type_wf (get_attr_type rt attr).
Proof.
  intros. unfold get_attr_type. destruct (access_record rt attr) eqn:E.
  - apply access_record_sound in E. inversion H.
    apply in_map with (f:=snd) in E; simpl in E. apply_Forall_In.
  - constructor.
Qed.


Section fold_command.
  Context (f : command -> command).
  Context (g : expr -> expr).

  Fixpoint fold_command (c : command) : command :=
    f
      match c with
      | CSkip => CSkip
      | CSeq c1 c2 => CSeq (fold_command c1) (fold_command c2)
      | CLet e x c => CLet (fold_expr g e) x (fold_command c)
      | CLetMut e x c => CLetMut (fold_expr g e) x (fold_command c)
      | CAssign x e => CAssign x (fold_expr g e)
      | CIf e c1 c2 => CIf (fold_expr g e) (fold_command c1) (fold_command c2)
      | CForeach e x c => CForeach (fold_expr g e) x (fold_command c)
      end.
End fold_command.

Section WithMap.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Lemma fold_command_id_preserve_ty : forall f c Gstore Genv,
      tenv_wf Gstore -> tenv_wf Genv ->
      preserve_ty f ->
      well_typed Gstore Genv c -> well_typed Gstore Genv (fold_command id f c).
  Proof.
    induction c; simpl; auto; intros.
    all: invert_well_typed.
    all: econstructor; eauto with fiat2_hints;
      try apply fold_expr_preserve_ty; auto.
  Qed.

  Ltac use_fold_command_id_preserve_sem_IH Gstore' :=
    lazymatch goal with
      IH: context[interp_command _ _ ?c = _] |-
        context[interp_command _ _ (fold_command id _ ?c)] =>
        erewrite <- IH with (Gstore:=Gstore')
    end.

  Lemma fold_command_id_preserve_sem : forall f c (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv ->
      well_typed Gstore Genv c ->
      locals_wf Gstore store -> locals_wf Genv env ->
      preserve_ty f -> preserve_sem (locals := locals) f ->
      interp_command store env c = interp_command store env (fold_command id f c).
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
        erewrite <- fold_expr_preserve_sem with (Gstore:=Gstore) in *; eauto.
        apply_type_sound e.
        lazymatch goal with
          E: ?x = VList _, E': VList _ = ?x, H: context[?x] |- _ =>
            rewrite E in E'; do_injection; rewrite E in H end.
        invert_type_of_value.
        repeat lazymatch goal with H: context[VList] |- _ => clear H end.
        generalize dependent store.
        induction l; simpl in *; auto; intros. invert_Forall.
        rewrite IHl; auto.
        2: eapply command_type_sound; eauto with fiat2_hints.
        f_equal. use_fold_command_id_preserve_sem_IH Gstore. 4: eauto.
        all: eauto with fiat2_hints. }
  Qed.

  Definition preserve_ty Gstore f :=
    forall e t (Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv ->
      type_of Gstore Genv e t -> type_of Gstore Genv (f e) t.

  Definition preserve_sem Gstore store f :=
    forall e t (Genv : tenv) (env : locals),
      tenv_wf Gstore -> tenv_wf Genv ->
      type_of Gstore Genv e t ->
      locals_wf Gstore store -> locals_wf Genv env ->
      interp_expr store env e = interp_expr store env (f e).

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
      apply H; invert_type_of; subst; try econstructor; eauto.
    all: try apply_fold_expr_preserve_ty_IH; repeat apply tenv_wf_step; auto;
      try now (apply_type_of__type_wf; auto; try invert_type_wf; auto).
    1: apply type_of__type_wf in H10; auto.
    4: apply type_of__type_wf in H11; auto.
    1: rewrite fst_map_fst; auto.
    1:{ lazymatch goal with H1: NoDup _, H2: Permutation _ _,
            H3: List.map fst _ = _ |- _ =>
                              clear H1 H2 H3 end.
        generalize dependent tl. induction l; auto. intros.
        destruct tl; invert_Forall2; try discriminate. simpl in *.
        constructor.
        2: apply IHl; invert_Forall; intuition auto.
        invert_Forall. destruct a; simpl in *. apply H5; auto. }
    1:{ induction l; simpl; auto. repeat invert_Forall. constructor.
        2:{ apply IHl; intuition auto. }
        destruct a; simpl in *. intuition auto. }
  Qed.

  Ltac apply_fold_expr_preserve_sem_IH :=
    multimatch goal with
    | IH: context[interp_expr _ _ (fold_expr _ ?e)],
        _: type_of _ ?G ?e _ |- context[interp_expr _ _ (fold_expr _ ?e)] =>
        erewrite <- IH with (Genv:=G); eauto
    end.

  Ltac trans_eq :=
    lazymatch goal with
      H: interp_expr _ _ ?e = _, H': _ = interp_expr _ _ ?e |- _ =>
        rewrite H in H'; injection H'; intros; subst end.

  Ltac type_of_list_entry :=
    lazymatch goal with
    | H1: type_of _ _ ?e _, _: interp_expr _ _ ?e = VList ?l,
          _: In ?x ?l |- type_of_value ?x _ =>
        eapply type_sound in H1; eauto; inversion H1; subst;
        trans_eq;
        apply_Forall_In end.

  Lemma fold_expr_preserve_sem : forall Gstore store f,
      preserve_ty Gstore f ->
      preserve_sem Gstore store f -> preserve_sem Gstore store (fold_expr f).
  Proof.
    unfold preserve_sem; intros * ? H_sem. induction e using expr_IH; simpl; auto; intros.
    1-3: erewrite <- H_sem; eauto.
    all: invert_type_of.
    all: try now (erewrite <- H_sem; eauto;
                  [ simpl; repeat apply_fold_expr_preserve_sem_IH
                  | econstructor; eauto; apply fold_expr_preserve_ty ];
                  eauto with fiat2_hints).
    1:{ erewrite <- H_sem; eauto.
        2: econstructor; eauto; apply fold_expr_preserve_ty; eauto with fiat2_hints.
        simpl; apply_fold_expr_preserve_sem_IH. case_match; auto.
        f_equal. apply In_flat_map_ext; intros.
        apply_fold_expr_preserve_sem_IH; eauto with fiat2_hints.
        apply locals_wf_step; auto. type_of_list_entry. }
    1:{ erewrite <- H_sem; eauto.
        2: econstructor; eauto; apply fold_expr_preserve_ty; eauto;
        repeat apply tenv_wf_step; eauto with fiat2_hints.
        simpl; apply_fold_expr_preserve_sem_IH. case_match; auto.
        apply_fold_expr_preserve_sem_IH.
        eapply In_fold_right_ext with (P:=fun a => type_of_value a t); intros.
        1: eapply type_sound; eauto.
        split;
          [ apply_fold_expr_preserve_sem_IH | eapply type_sound; eauto ];
          repeat apply tenv_wf_step; repeat apply locals_wf_step;
          eauto with fiat2_hints; type_of_list_entry. }
    1:{ erewrite <- H_sem with (t:=TRecord tl'); eauto.
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
    1:{ erewrite <- H_sem; eauto.
        2:{ econstructor.
            3:{ induction l; simpl; auto.
                repeat invert_Forall.
                case_match; constructor; simpl in *.
                2: apply IHl; intuition.
                intuition; apply fold_expr_preserve_ty; eauto. }
            all: auto. }
        simpl. do 3 f_equal. induction l; simpl; auto.
        repeat invert_Forall; case_match; simpl in *.
        f_equal. 2: apply IHl; intuition.
        f_equal; intuition; apply_fold_expr_preserve_sem_IH. }
    1:{ erewrite <- H_sem; eauto.
        2: econstructor; eapply fold_expr_preserve_ty; eauto with fiat2_hints.
        simpl. apply_fold_expr_preserve_sem_IH. repeat case_match; auto.
        all: apply_fold_expr_preserve_sem_IH; eauto with fiat2_hints.
        apply locals_wf_step; eauto. eapply type_sound in H10; eauto. inversion H10; subst.
        all: trans_eq; congruence. }
    1:{ erewrite <- H_sem; eauto.
        2: econstructor; eauto; apply fold_expr_preserve_ty; eauto;
        repeat apply tenv_wf_step; eauto with fiat2_hints.
        simpl; apply_fold_expr_preserve_sem_IH. case_match; auto.
        apply_fold_expr_preserve_sem_IH.
        eapply In_fold_right_ext with (P:=fun a => type_of_value a t); intros.
        1: eapply type_sound; eauto.
        split;
          [ apply_fold_expr_preserve_sem_IH | eapply type_sound; eauto ];
          repeat apply tenv_wf_step; repeat apply locals_wf_step;
          eauto with fiat2_hints.
        all: eapply type_sound in H12; eauto; inversion H12; subst.
        all: trans_eq; apply_Forall_In; intuition. }
    1:{ erewrite <- H_sem; eauto.
        2: econstructor; eauto; apply fold_expr_preserve_ty; eauto with fiat2_hints.
        simpl. apply_fold_expr_preserve_sem_IH. case_match; auto.
        f_equal. apply In_filter_ext; intros.
        apply_fold_expr_preserve_sem_IH; eauto with fiat2_hints.
        apply locals_wf_step; auto. type_of_list_entry. }
    1:{ erewrite <- H_sem; eauto.
        2: econstructor; eauto; apply fold_expr_preserve_ty;
        repeat apply tenv_wf_step; eauto with fiat2_hints.
        simpl. repeat apply_fold_expr_preserve_sem_IH. repeat case_match; auto.
        f_equal. apply In_flat_map_ext; intros. erewrite In_filter_ext.
        1: apply map_ext_in; intros.
        2: simpl; intros.
        all: apply_fold_expr_preserve_sem_IH;
          [ repeat apply tenv_wf_step | repeat apply locals_wf_step ]; eauto with fiat2_hints.
        all: try type_of_list_entry.
        all: lazymatch goal with H: In _ (filter _ _) |- _ => apply filter_In in H; intuition end.
        type_of_list_entry. }
    1:{ erewrite <- H_sem; eauto.
        2: econstructor; eauto; apply fold_expr_preserve_ty; eauto with fiat2_hints.
        simpl. apply_fold_expr_preserve_sem_IH. case_match; auto.
        f_equal. apply map_ext_in; intros.
        apply_fold_expr_preserve_sem_IH; eauto with fiat2_hints.
        repeat apply locals_wf_step; auto; type_of_list_entry. }
  Qed.

  Section WithGlobals.
    Context (globals : list string).
    Context (global_types : list type) (global_types_ok : List.length globals = List.length global_types).

    Section fold_command_with_globals.
      Context (f : expr -> expr).

      Fixpoint fold_command_with_globals (c : command) : command :=
        match c with
        | CSkip => CSkip
        | CSeq c1 c2 => CSeq (fold_command_with_globals c1) (fold_command_with_globals c2)
        | CLet e x c => CLet (fold_expr f e) x (fold_command_with_globals c)
        | CLetMut e x c =>
            (* Avoid applying the transformation if the global variable is shadowed *)
            CLetMut (fold_expr f e) x
              (if inb String.eqb x globals then c else fold_command_with_globals c)
        | CAssign x e => CAssign x (fold_expr f e)
        | CIf e c1 c2 =>
            CIf (fold_expr f e) (fold_command_with_globals c1) (fold_command_with_globals c2)
        | CForeach e x c =>
            CForeach (fold_expr f e) x (fold_command_with_globals c)
        end.
    End fold_command_with_globals.

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

    Ltac apply_fold_command_with_globals_preserve_ty_IH :=
      lazymatch goal with
      | IH: context[fold_command_with_globals _ ?c] |- context[?c] =>
          apply IH
      end.

    Lemma fold_command_with_globals_preserve_ty : forall f,
        (forall Gstore, tenv_wf_with_globals Gstore -> preserve_ty Gstore f) ->
        forall c Gstore Genv,
          tenv_wf Gstore -> tenv_wf Genv -> tenv_wf_with_globals Gstore ->
          well_typed Gstore Genv c -> well_typed Gstore Genv (fold_command_with_globals f c).
    Proof.
      induction c; simpl; auto; intros.
      all: lazymatch goal with
             H: well_typed _ _ _ |- _ => inversion H; subst
           end.
      1: constructor; apply_fold_command_with_globals_preserve_ty_IH; auto.
      all: econstructor; try now (apply fold_expr_preserve_ty; eauto).
      all: try apply_fold_command_with_globals_preserve_ty_IH; auto.
      1,3: apply tenv_wf_step; auto.
      1: eapply type_of__type_wf with (Gstore:=Gstore); eauto.
      1: lazymatch goal with
           H: type_of _ _ _ (TList ?t) |- type_wf ?t =>
             apply type_of__type_wf in H; auto;
             apply invert_TList_wf in H; auto
         end.
      1:{ case_match; auto.
          apply_fold_command_with_globals_preserve_ty_IH; auto.
          1: apply tenv_wf_step; auto;
          eapply type_of__type_wf with (Gstore:=Gstore); eauto.
          apply tenv_wf_with_globals_step; auto.
          rewrite inb_false_iff in *. auto. }
    Qed.

    Ltac invert_parameterized_wf :=
      lazymatch goal with H: parameterized_wf _ _ _ _ |- _ => inversion H; subst end.

    Ltac apply_preserve_parameterized_wf_IH :=
      lazymatch goal with
        IH: context[fold_command_with_globals _ ?c] |- context[?c] =>
          apply IH
      end.

    Ltac apply_fold_command_with_globals_preserve_sem_IH :=
      lazymatch goal with
      | IH: context[interp_command _ _ (fold_command_with_globals _ ?c)],
          H: parameterized_wf ?Gstore' ?Genv' _ ?c |-
          context[interp_command _ _ (fold_command_with_globals _ ?c)] =>
          erewrite <- IH with (Gstore:=Gstore') (Genv:=Genv'); eauto
      end.

    Context  {idx : IndexInterface.index} {idx_wf : value -> Prop} {idx_ok : ok LikeBag LikeList idx idx_wf consistent}.
    Notation index_wf_with_globals := (index_wf_with_globals (idx_wf:=idx_wf)).

    Lemma not_In__index_wf_with_globals : forall x globals (store : locals) v,
        ~In x globals ->
        holds_for_all_entries (index_wf_with_globals globals) store ->
        holds_for_all_entries (index_wf_with_globals globals) (map.put store x v).
    Proof.
      unfold holds_for_all_entries; intros.
      unfold index_wf_with_globals in *.
      destruct (String.eqb k x) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst; rewrite_map_get_put_hyp.
      rewrite Forall_forall; intros. left; intro contra; subst; auto.
    Qed.

    Lemma fold_command_with_globals_preserve_sem : forall f c,
        (forall (Gstore : tenv), tenv_wf_with_globals Gstore ->
                                 preserve_ty Gstore f) ->
        (forall (Gstore : tenv) (store : locals),
            tenv_wf_with_globals Gstore ->
            holds_for_all_entries (index_wf_with_globals globals) store ->
            preserve_sem Gstore store f) ->
        forall (Gstore Genv : tenv) (store env : locals),
          tenv_wf Gstore -> tenv_wf Genv -> tenv_wf_with_globals Gstore ->
          parameterized_wf Gstore Genv (index_wf_with_globals globals) c ->
          locals_wf Gstore store -> locals_wf Genv env ->
          holds_for_all_entries (index_wf_with_globals globals) store ->
          interp_command store env c = interp_command store env (fold_command_with_globals f c).
    Proof.
      induction c; simpl; intros; auto; invert_parameterized_wf.
      3:{ erewrite <- fold_expr_preserve_sem; eauto; case_match; auto.
          rewrite inb_false_iff in *.
          erewrite <- IHc; auto.
          4:{ eapply parameterized_wf_Proper.
              5: eauto. all: eauto.
              apply iff2_sym. apply rm_not_in_globals; auto. }
          all: eauto with fiat2_hints.
          1: apply not_In__tenv_wf_with_globals; auto.
          unfold holds_for_all_entries.
          1: apply not_In__index_wf_with_globals; auto. }
      all: try erewrite <- fold_expr_preserve_sem; eauto;
        repeat case_match; auto;
        repeat apply_fold_command_with_globals_preserve_sem_IH; eauto with fiat2_hints.
      1:{ eapply command_type_sound; eauto.
          eapply parameterized_wf__well_typed; eauto. }
      1:{ eapply parameterized_wf__preserve_P with (Gstore:=Gstore); eauto. }
      1:{ apply_type_sound e. rewrite E in *.
          lazymatch goal with H: type_of_value _ _ |- _ => inversion H; subst end.
          lazymatch goal with
            H1: VList _ = VList _, H2: type_of_value _ _, H3: interp_expr _ _ _ = VList _ |- _ =>
              clear H1 H2 H3
          end.
          generalize dependent store. induction l; simpl; auto; intros.
          invert_Forall. eapply IHc in H12 as IHc'; eauto with fiat2_hints.
          rewrite <- IHc'. apply IHl; auto.
          2: eapply parameterized_wf__preserve_P with (Gstore:=Gstore) (Genv:=map.put Genv x t);
          eauto with fiat2_hints.
          apply command_type_sound with (Genv:=map.put Genv x t); auto.
          2:{ apply tenv_wf_step; auto. apply_type_of__type_wf; auto. invert_type_wf; auto. }
          2: eapply locals_wf_step; eauto.
          eapply parameterized_wf__well_typed; eauto. }
    Qed.

    Lemma fold_command_with_globals_preserve_index_wf : forall f,
        (forall (Gstore : tenv), tenv_wf_with_globals Gstore ->
                                 preserve_ty Gstore f) ->
        (forall (Gstore : tenv) (store : locals),
            tenv_wf_with_globals Gstore ->
            holds_for_all_entries (index_wf_with_globals globals) store ->
            preserve_sem Gstore store f) ->
        forall c (Gstore Genv : tenv),
          tenv_wf Gstore -> tenv_wf Genv ->
          tenv_wf_with_globals Gstore ->
          parameterized_wf Gstore Genv (index_wf_with_globals globals) c ->
          parameterized_wf Gstore Genv (index_wf_with_globals globals) (fold_command_with_globals f c).
    Proof.
      induction c; simpl; auto; intros; invert_parameterized_wf.
      all: try (econstructor;
                try (apply fold_expr_preserve_ty; eauto);
                apply_preserve_parameterized_wf_IH; eauto with fiat2_hints).
      1:{ econstructor.
          1: apply fold_expr_preserve_ty; eauto.
          case_match; auto. rewrite inb_false_iff in *.
          eapply parameterized_wf_Proper.
          3: apply rm_not_in_globals.
          all: eauto. apply_preserve_parameterized_wf_IH; eauto with fiat2_hints.
          1: apply tenv_wf_with_globals_step; auto.
          eapply parameterized_wf_Proper.
          3: apply iff2_sym, rm_not_in_globals.
          all: eauto. }
      1:{ econstructor; eauto.
          2: apply fold_expr_preserve_ty; eauto.
          intros. erewrite <- fold_expr_preserve_sem; eauto. }
    Qed.

  End WithGlobals.
End WithMap.

Definition is_NoDup_opaque {A : Type} := is_NoDup (A:=A).

Lemma is_NoDup_to_transparent : forall A, is_NoDup_opaque (A:=A) = is_NoDup (A:=A).
Proof.
  reflexivity.
Qed.

Opaque is_NoDup_opaque.

Ltac use_is_NoDup :=
  rewrite is_NoDup_to_transparent in *;
  simpl in *; intuition idtac; try congruence.

Section WithHole.
  Context (hole : string).
  Context (attr : string).

  Section WithVars.
    Context (tup acc x k v : string).
    Context (H_NoDup : is_NoDup_opaque [tup; acc; x; k; v]).

    (* Materialize tbl (expected to be a list of records) into an index over attr *)
    Definition to_idx : expr :=
      let k := EAccess (EVar tup) attr in
      EFold (EVar hole) (EDict nil) tup acc
        (EInsert (EVar acc) k
           (EOptMatch (ELookup (EVar acc) k)
              (epair enil (EVar tup))
              x (cons_to_fst (EVar tup) (EVar x)))).

    (* Inverse of to_idx, expecting idx to be a dict
   Require the index keys in idx to match the attr values in the records *)
    Definition from_idx : expr :=
      EDictFold (EVar hole) enil k v acc
        (EBinop OConcat (ofst (EVar v))
           (econs (osnd (EVar v)) (EVar acc))).

    Definition is_tbl_ty (t : type) : bool :=
      match t with
      | TList (TRecord rt) => inb (String.eqb) attr (List.map fst rt)
      | _ => false
      end.

    (* An index is a dictionary with each of its keys mapped to at least one row of the table *)
    Definition index_type (kt : type) (rt : list (string * type)) :=
      TDict kt (TRecord [("0", TList (TRecord rt)); ("1", TRecord rt)]).

    Definition idx_ty (t : type) : type :=
      match t with
      | TList (TRecord rt) => index_type (get_attr_type rt attr) rt
      | _ => TUnit
      end.

    Lemma idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t).
      destruct t; simpl; intros; try congruence.
      destruct t; try congruence. unfold index_type.
      inversion H; subst. inversion H2; subst. repeat constructor; intuition auto.
      1: apply get_attr_type_ty_wf; auto.
      1:{ simpl in *; intuition idtac. congruence. }
    Qed.

    Section WithMap.
      Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
      Notation value := (value (width:=width)).
      Context {tenv : map.map string type} {tenv_ok : map.ok tenv}
        {locals : map.map string value} {locals_ok : map.ok locals}.

      Ltac apply_In_access_record :=
        lazymatch goal with
          H: inb _ _ _ = true |- _ =>
            rewrite inb_true_iff in H;
            apply In_access_record in H
        end.

      Lemma to_idx_ty : forall (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t).
      Proof.
        intros. unfold to_idx.
        unfold is_tbl_ty in *. repeat destruct_match_hyp; try discriminate; subst.
        invert_type_wf. repeat econstructor; simpl; auto.
        all: repeat rewrite_map_get_put_goal; eauto.
        1: apply get_attr_type_ty_wf; auto.
        all: invert_type_wf; try now use_is_NoDup.
        1,2: unfold get_attr_type; apply_In_access_record; destruct_exists; rewrite_l_to_r; auto.
        1,2: repeat econstructor; auto; repeat rewrite_map_get_put_goal; use_is_NoDup.
      Qed.

      Lemma from_idx_ty : forall (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of map.empty (map.put map.empty hole (idx_ty t)) from_idx t.
      Proof.
        intros. unfold from_idx.
        unfold is_tbl_ty in *. repeat destruct_match_hyp; try discriminate; subst.
        invert_type_wf. repeat econstructor; simpl; auto.
        all: repeat rewrite_map_get_put_goal;
          invert_type_wf; use_is_NoDup.
      Qed.

      Definition index_wf (l : list (value * value)) :=
        Forall (fun p => match snd p with
                         | VRecord r =>
                             match access_record r "0" with
                             | Success (VList l) =>
                                 Forall (fun r => match r with
                                                  | VRecord r => access_record r attr = Success (fst p)
                                                  | _ => False
                                                  end) l
                             | _ => False
                             end /\
                               match access_record r "1" with
                               | Success (VRecord r) => access_record r attr = Success (fst p)
                               | _ => False
                               end
                         | _ => False
                         end) l.

      Lemma index_wf_step_inv : forall p idx,
          index_wf (p :: idx) -> index_wf idx.
      Proof.
        intros. unfold index_wf in *. invert_Forall; auto.
      Qed.

      Definition idx_wf (v : value) :=
        match v with
        | VDict l => index_wf l
        | _ => False
        end.

      Notation index_wf_with_globals := (index_wf_with_globals (idx_wf:=idx_wf)).

      Ltac swap_record_map_fst :=
        lazymatch goal with
          H: Forall2 _ _ _ |- _ => apply Forall2_split in H end; destruct_and;
        rewrite Forall2_fst_eq in *;
        lazymatch goal with
          H: map fst _ = _ |- _ => rewrite <- H in * end.

      Lemma dict_lookup__In : forall k l (v : value), dict_lookup k l = Some v -> In (k, v) l.
      Proof.
        induction l; simpl; intros.
        1: congruence.
        repeat destruct_match_hyp; intuition auto. do_injection.
        left; f_equal; symmetry; auto using value_eqb_eq.
      Qed.

      Lemma fold_right_invariant : forall (A B : Type) (a : A) (l : list B) (f : B -> A -> A) (P : A -> Prop),
          P a -> (forall (a : A) (b : B), P a -> In b l -> P (f b a)) ->
          P (fold_right f a l).
      Proof.
        intros. assert(fold_right f a l = fold_right f a l /\ P (fold_right f a l)).
        { auto using In_fold_right_ext'. }
        intuition auto.
      Qed.

      Lemma to_idx_wf : forall (v : value) (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          idx_wf (interp_expr map.empty (map.put map.empty hole v) to_idx).
      Proof.
        unfold is_tbl_ty; intros; simpl in * |-.
        repeat destruct_match_hyp; try discriminate.
        simpl. unfold get_local; rewrite_map_get_put_goal.
        invert_type_of_value.
        apply fold_right_invariant.
        1:{ unfold dict_sort, Mergesort.Sectioned.sort, idx_wf, index_wf; simpl; auto. }
        1:{ intros; apply_Forall_In.
            repeat rewrite_map_get_put_goal; try now use_is_NoDup.
            unfold idx_wf in *. destruct_match_hyp; auto.
            repeat invert_type_of_value_clear.
            unfold index_wf. eapply incl_Forall.
            1: apply dict_insert_incl.
            swap_record_map_fst.
            apply_In_access_record; destruct_exists.
            constructor; auto; simpl. case_match; simpl.
            1:{ repeat rewrite_map_get_put_goal; try now use_is_NoDup.
                unfold index_wf in *. apply dict_lookup__In in E.
                apply_Forall_In; simpl in *. unfold record_proj.
                case_match; auto.
                intuition auto; case_match; auto.
                case_match; auto. constructor; auto.
                repeat rewrite_l_to_r; auto. }
            1:{ split; auto. unfold record_proj. repeat rewrite_l_to_r; auto. } }
      Qed.

      Definition vcons_to_fst (v p : value) : value :=
        VRecord [("0", match p with
                       | VRecord p =>
                           match record_proj "0" p with
                           | VList l => VList (v :: l)
                           | _ => VUnit
                           end
                       | _ => VUnit
                       end);
                 ("1", match p with
                       | VRecord p => record_proj "1" p
                       | _ => VUnit
                       end)].

      Definition gallina_to_idx (v0 : value) : list (value * value) :=
        match v0 with
        | VList l =>
            fold_right
              (fun v acc => match v with
                            | VRecord v =>
                                dict_insert (record_proj attr v)
                                  (match dict_lookup (record_proj attr v) acc with
                                   | Some p => vcons_to_fst (VRecord v) p
                                   | None => VRecord [("0", VList nil); ("1", VRecord v)]
                                   end) acc
                            | _ => nil
                            end) nil l
        | _ => nil
        end.

      Lemma fiat2_gallina_to_idx : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          interp_expr map.empty (map.put map.empty hole v) to_idx = VDict (gallina_to_idx v).
      Proof.
        unfold is_tbl_ty; intros. repeat destruct_match_hyp; try discriminate.
        invert_type_of_value_clear; simpl.
        unfold get_local; rewrite_map_get_put_goal.
        erewrite In_fold_right_ext with
          (P := fun a => match a with VDict _ => True | _ => False end)
          (g := fun v1 v2 => match v1, v2 with
                             | VRecord l1, VDict l0 =>
                                 VDict
                                   (dict_insert (record_proj attr l1)
                                      match dict_lookup (record_proj attr l1) l0 with
                                      | Some v0 =>
                                          VRecord
                                            [("0",
                                               match
                                                 match v0 with
                                                 | VRecord l2 => record_proj "0" l2
                                                 | _ => VUnit
                                                 end
                                               with
                                               | VList l2 => VList (VRecord l1 :: l2)
                                               | _ => VUnit
                                               end);
                                             ("1",
                                               match v0 with
                                               | VRecord l2 => record_proj "1" l2
                                               | _ => VUnit
                                               end)]
                                      | None => VRecord (record_sort [("0", VList []); ("1", VRecord l1)])
                                      end l0)
                             | _, _ => VUnit
                             end); auto.
        1:{ induction l0; simpl; auto. invert_Forall. invert_type_of_value_clear.
            rewrite IHl0; auto. do 2 f_equal. case_match; auto.
            unfold vcons_to_fst. repeat f_equal. case_match; auto. }
        1:{ intros. apply_Forall_In; invert_type_of_value_clear.
            repeat rewrite_map_get_put_goal; try now use_is_NoDup.
            destruct_match_hyp; split; try now (intuition auto).
            do 2 f_equal. case_match; auto. f_equal.
            unfold record_sort, Mergesort.Sectioned.sort; simpl.
            do 2 f_equal.
            1:{ rewrite_map_get_put_goal. case_match; auto.
                case_match; auto. repeat rewrite_map_get_put_goal; use_is_NoDup. }
            1:{ f_equal. rewrite_map_get_put_goal; auto. } }
      Qed.

      Definition gallina_from_idx (v : value) : list value :=
        match v with
        | VDict d =>
            fold_right
              (fun v acc => match snd v with
                            | VRecord p => match record_proj "0" p with
                                           | VList l => (l ++ (record_proj "1" p :: acc))%list
                                           | _ => nil
                                           end
                            | _ => nil
                            end)
              nil d
        | _ => nil
        end.

      Lemma fiat2_gallina_from_idx : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v (idx_ty t) ->
          interp_expr map.empty (map.put map.empty hole v) from_idx = VList (gallina_from_idx v).
      Proof.
        unfold is_tbl_ty, idx_ty, index_type; intros. repeat destruct_match_hyp; try discriminate.
        invert_type_of_value_clear; simpl.
        unfold get_local; rewrite_map_get_put_goal.
        erewrite In_fold_right_ext with
          (P := fun v => match v with VList _ => True | _ => False end)
          (g := fun v1 v2 =>
                  match v1, v2 with
                  | (v0, v1), (VList l) => match v1 with
                                           | VRecord l1 => match record_proj "0" l1 with
                                                           | VList l1_0 => VList (l1_0 ++ record_proj "1" l1 :: l)
                                                           | _ => VUnit
                                                           end
                                           | _ => VUnit
                                           end
                  | _, _ => VUnit
                  end); auto.
        1:{ induction l0; simpl in *; auto. invert_Forall; invert_NoDup; invert_SSorted.
            rewrite IHl0; auto. destruct a; simpl in *.
            destruct_and. invert_type_of_value_clear. repeat invert_Forall2.
            destruct x0, x1; simpl in *. do 2 destruct_and; subst.
            unfold record_proj; simpl. do 2 invert_type_of_value_clear; auto. }
        1:{ intros. destruct_match_hyp; try now (intuition auto).
            repeat rewrite_map_get_put_goal; try now use_is_NoDup.
            apply_Forall_In. destruct_and.
            destruct b; simpl in *. invert_type_of_value_clear; split; auto.
            repeat invert_Forall2. do 2 destruct_and; destruct x0, x1.
            simpl in *; subst. unfold record_proj; simpl.
            do 2 invert_type_of_value_clear; auto. }
      Qed.

      Lemma map_incl_step_l : forall {kt vt} {key_eqb : kt -> kt -> bool}
                                     {mt : map.map kt vt} {mt_ok : map.ok mt} (m m' : mt)
                                     x v,
          (forall x y : kt, BoolSpec (x = y) (x <> y) (key_eqb x y)) ->
          map_incl m m' -> map.get m' x = Some v ->
          map_incl (map.put m x v) m'.
      Proof.
        intros.
        erewrite <- Properties.map.put_noop; eauto.
        apply map_incl_step; auto.
        intros. specialize (H k1 k2).
        destruct (key_eqb k1 k2) eqn:E;
          [ left; eapply autoforward.BoolSpec_true
          | right; eapply autoforward.BoolSpec_false ]; eauto.
      Qed.

      Lemma fiat2_gallina_from_idx2 : forall (store env : locals) (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v (idx_ty t) ->
          map.get env hole = Some v ->
          interp_expr store env from_idx = VList (gallina_from_idx v).
      Proof.
        intros. erewrite interp_expr_strengthen.
        1: eapply fiat2_gallina_from_idx.
        6: apply from_idx_ty.
        all: eauto using idx_ty_wf, map_incl_empty with fiat2_hints.
        eapply map_incl_step_l; auto using map_incl_empty.
        apply String.eqb_spec.
      Qed.

      Ltac use_from_idx_ty :=
        eapply type_of_strengthen;
        [ apply from_idx_ty; auto
        | apply map_incl_empty
        | apply map_incl_refl ].

      Ltac prove_sub_wf :=
        unfold sub_wf; simpl; intros;
        case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
        [ rewrite_map_get_put_hyp
        | rewrite map.get_put_diff, map.get_empty in *; auto ];
        congruence.

      Lemma fiat2_gallina_from_idx_sem : forall Gstore Genv store env e t,
          tenv_wf Gstore -> tenv_wf Genv ->
          type_wf t -> is_tbl_ty t = true ->
          type_of Gstore Genv e (idx_ty t) ->
          locals_wf Gstore store -> locals_wf Genv env ->
          interp_expr store env (substitute [(hole, e)] (get_free_vars Genv) from_idx) = VList (gallina_from_idx (interp_expr store env e)).
      Proof.
        intros. erewrite substitute_preserve_sem.
        1:{ erewrite fiat2_gallina_from_idx2; eauto with fiat2_hints.
            simpl. rewrite_map_get_put_goal. auto. }
        6-8: eauto using incl_refl.
        all: auto.
        2: use_from_idx_ty.
        all: eauto using idx_ty_wf with fiat2_hints.
        prove_sub_wf.
      Qed.

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

      Instance EFilter_Proper {t : type} (x0 : string) (Gstore Genv : tenv) :
        tenv_wf Gstore -> tenv_wf Genv ->
        Proper (sem_eq Gstore Genv (TList t) ==> singleton_rel x0 ==> sem_eq Gstore (map.put Genv x0 t) TBool ==> sem_eq Gstore Genv (TList t)) EFilter.
      Proof.
        intros * ? ? e1 e1' H1 y y' Hy e2 e2' H2.
        unfold sem_eq in *; intros.
        unfold singleton_rel in *. intuition auto; subst.
        1,2: constructor; auto.
        repeat invert_type_of.
        simpl. lazymatch goal with
          H: context[interp_expr _ _ ?e = _] |-
            context[match interp_expr _ _ ?e with _ => _ end] =>
            rewrite H end; auto.
        case_match; auto. f_equal.
        apply filter_ext_in; intros.
        lazymatch goal with
          H: context[interp_expr _ _ ?e = _] |-
            context[match interp_expr _ _ ?e with _ => _ end] =>
            rewrite H end; eauto with fiat2_hints.
        apply_type_sound e1'; auto. rewrite_l_to_r.
        apply locals_wf_step; auto. do_injection; subst.
        apply_Forall_In.
      Qed.

      Ltac apply_tenv_wf :=
        lazymatch goal with
          H: tenv_wf ?G, H': map.get ?G _ = Some ?t |- _ =>
            apply H in H' end.

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

      Lemma fold_from_idx : forall Gstore Genv t e k0 v0 acc0,
          is_NoDup [k0; v0; acc0] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          type_wf t -> is_tbl_ty t = true ->
          type_of Gstore Genv e (idx_ty t) ->
          sem_eq Gstore Genv t
            (EDictFold e (EAtom (ANil None)) k0 v0 acc0
               (EBinop OConcat (EAccess (EVar v0) "0") (EBinop OCons (EAccess (EVar v0) "1") (EVar acc0))))
            (substitute [(hole, e)] (get_free_vars Genv) from_idx).
      Proof.
        unfold sem_eq; intros. intuition idtac.
        1:{ unfold idx_ty in *. unfold is_tbl_ty in *.
            do 2 (destruct_match_hyp; try discriminate).
            invert_type_wf.
            repeat (econstructor; eauto); repeat rewrite_map_get_put_goal; eauto. }
        1:{ eapply substitute_preserve_ty; auto using incl_refl.
            2: use_from_idx_ty.
            1: eauto using idx_ty_wf with fiat2_hints.
            1: prove_sub_wf. }
        erewrite substitute_preserve_sem.
        1:{ unfold from_idx. simpl.
            unfold get_local; rewrite_map_get_put_goal.
            case_match; auto.
            eapply In_fold_right_ext with (P:=fun _ => True); intuition auto.
            repeat rewrite_map_get_put_goal; use_is_NoDup. }
        6-8: eauto using incl_refl.
        all: auto.
        2: use_from_idx_ty.
        all: eauto using idx_ty_wf with fiat2_hints.
        prove_sub_wf.
      Qed.

      Ltac use_to_idx_ty :=
        eapply type_of_strengthen;
        [ apply to_idx_ty; auto
        | apply map_incl_empty
        | apply map_incl_refl ].

      Lemma fold_to_idx : forall Gstore Genv t e x0 tup0 acc0,
          is_NoDup [x0; tup0; acc0] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          is_tbl_ty t = true ->
          type_of Gstore Genv e t ->
          sem_eq Gstore Genv (idx_ty t)
            (EFold e (EDict []) tup0 acc0
               (EInsert (EVar acc0) (EAccess (EVar tup0) attr) (EOptMatch (ELookup (EVar acc0) (EAccess (EVar tup0) attr)) (epair enil (EVar tup0)) x0 (cons_to_fst (EVar tup0) (EVar x0)))))
            (substitute [(hole, e)] (get_free_vars Genv) to_idx).
      Proof.
        unfold sem_eq, is_tbl_ty; intros.
        repeat destruct_match_hyp; try discriminate; subst.
        intuition idtac.
        1:{ unfold idx_ty, index_type in *. lazymatch goal with
            H: type_of _ _ _ _ |- _ =>
              apply type_of__type_wf in H as H' end; auto.
            repeat invert_type_wf.
            repeat (econstructor; simpl; intuition eauto).
            all: repeat rewrite_map_get_put_goal; try congruence; eauto.
            1: apply get_attr_type_ty_wf; eauto with fiat2_hints.
            1,2: unfold get_attr_type; apply_In_access_record; destruct_exists; rewrite_l_to_r; auto. }
        1:{ eapply substitute_preserve_ty; auto using incl_refl.
            2: use_to_idx_ty.
            1,2: eauto using idx_ty_wf with fiat2_hints.
            1: prove_sub_wf. }
        erewrite substitute_preserve_sem with (t0:=idx_ty (TList (TRecord l))).
        1:{ simpl.
            unfold get_local; rewrite_map_get_put_goal.
            repeat case_match; auto.
            eapply In_fold_right_ext with (P:=fun _ => True); intuition auto.
            repeat rewrite_map_get_put_goal; try now use_is_NoDup.
            case_match; auto. do 2 f_equal.
            lazymatch goal with
              |- context[match ?x with _ => _ end] =>
                destruct x; auto
            end. repeat f_equal.
            all: repeat (rewrite_map_get_put_goal; try now use_is_NoDup); reflexivity. }
        6-8: eauto using incl_refl.
        all: auto.
        2: use_to_idx_ty.
        all: eauto using idx_ty_wf with fiat2_hints.
        prove_sub_wf.
      Qed.

      Lemma fiat2_gallina_to_idx2: forall (store env : locals) v t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          map.get env hole = Some v ->
          interp_expr store env to_idx = VDict (gallina_to_idx v).
      Proof.
        intros.
        erewrite interp_expr_strengthen.
        1: eapply fiat2_gallina_to_idx.
        6: apply to_idx_ty.
        all: eauto with fiat2_hints.
        2: eapply map_incl_step_l; eauto using String.eqb_spec.
        all: apply map_incl_empty.
      Qed.

      Lemma fiat2_gallina_to_idx_sem : forall Gstore Genv store env e t,
          tenv_wf Gstore -> tenv_wf Genv ->
          is_tbl_ty t = true ->
          type_of Gstore Genv e t ->
          locals_wf Gstore store -> locals_wf Genv env ->
          interp_expr store env (substitute [(hole, e)] (get_free_vars Genv) to_idx) = VDict (gallina_to_idx (interp_expr store env e)).
      Proof.
        intros. erewrite substitute_preserve_sem.
        1:{ erewrite fiat2_gallina_to_idx2; eauto with fiat2_hints.
            simpl. rewrite_map_get_put_goal. auto. }
        6-8: eauto using incl_refl.
        all: auto.
        2: use_to_idx_ty.
        all: eauto with fiat2_hints.
        prove_sub_wf.
      Qed.

      Lemma gallina_to_idx_ty : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          type_of_value (VDict (gallina_to_idx v)) (idx_ty t).
      Proof.
        intros. erewrite <- fiat2_gallina_to_idx; eauto.
        eapply type_sound; eauto using to_idx_ty with fiat2_hints.
      Qed.

      Lemma fiat2_gallina_to_from_idx : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          interp_expr map.empty (map.put map.empty hole (interp_expr map.empty (map.put map.empty hole v) to_idx)) from_idx =
            VList (gallina_from_idx (VDict (gallina_to_idx v))).
      Proof.
        intros.
        erewrite fiat2_gallina_to_idx, fiat2_gallina_from_idx;
          eauto using gallina_to_idx_ty.
      Qed.

      Fixpoint concat_VList_V (l : list value) :=
        match l with
        | VRecord l' :: l => match record_proj "0" l' with
                             | VList vl => (vl ++ (record_proj "1" l' :: concat_VList_V l))%list
                             | _ => nil
                             end
        | _ => nil
        end.

      Definition has_index_entry_shape (p : value * value) :=
        match snd p with
        | VRecord r =>
            match record_proj "0" r with
            | VList _ => True | _ => False end
        | _ => False end.

      Local Coercion is_true : bool >-> Sortclass.

      Lemma dict_lookup_Lt : forall d k,
          StronglySorted dict_entry_leb d ->
          (forall p, In p d -> value_compare k (fst p) = Lt) ->
          dict_lookup (word:=word) k d = None.
      Proof.
        intros. induction d; auto.
        simpl. destruct a; simpl in *.
        case_match.
        - unfold value_eqb in *. pose proof (H0 (v0, v1)).
          intuition; simpl in *. rewrite H1 in E; discriminate.
        - apply IHd; inversion H; auto.
      Qed.

      Lemma Permutation_cons_app_cons : forall A (l : list A) u v xl yl,
          Permutation xl (v :: yl) -> Permutation (l ++ u :: xl) (v :: l ++ u :: yl).
      Proof.
        clear. intros.
        replace (v :: l ++ u :: yl) with ((v :: nil) ++ l ++ u :: yl)%list; auto.
        eapply perm_skip with (x:=u), Permutation_sym, perm_trans in H.
        2: apply perm_swap.
        eapply perm_trans. 2: eapply Permutation_app_swap_app. simpl.
        auto using Permutation_app, Permutation_sym.
      Qed.

      Lemma dict_insert_lookup_Permutation :
        forall k d v, Forall has_index_entry_shape d ->
                      StronglySorted dict_entry_leb d ->
                      Permutation
                        (concat_VList_V
                           (List.map snd
                              (dict_insert k
                                 match dict_lookup k d with
                                 | Some p => vcons_to_fst v p
                                 | None =>
                                     VRecord [("0", VList []); ("1", v)]
                                 end d)))
                        (v :: (concat_VList_V (List.map snd d))).
      Proof.
        unfold has_index_entry_shape; intros.
        induction d; simpl; auto.
        case_match. simpl. invert_Forall; subst; simpl in *.
        do 2 destruct_match_hyp; try now (intuition auto).
        unfold value_eqb, value_ltb. case_match; cbn; auto.
        all: rewrite_l_to_r; auto.
        all: invert_SSorted; subst.
        - rewrite dict_lookup_Lt; auto. intros p H_in. apply_Forall_In.
          unfold dict_entry_leb, value_leb, leb_from_compare in *; simpl in *.
          destruct_match_hyp; try congruence.
          + lazymatch goal with
              E: value_compare _ _ = Eq |- _ =>
                apply value_compare_Eq_eq in E end; subst; auto.
          + eapply value_compare_trans; eauto.
        - apply Permutation_cons_app_cons; auto.
      Qed.

      Lemma Forall_dict_lookup : forall P d k v,
          Forall P d -> dict_lookup (width:=width) k d = Some v -> P (k, v).
      Proof.
        intros * H_P H. induction d; simpl in H; try congruence.
        destruct a. inversion H_P; subst.
        lazymatch goal with
        | H: context[value_eqb ?a ?b] |- _ => destruct (value_eqb a b) eqn:E
        end.
        1: apply value_eqb_eq in E; subst; do_injection; auto.
        1: apply IHd; auto.
      Qed.

      Lemma gallina_list_to_idx_shape : forall l rt,
          Forall (fun v => type_of_value v (TRecord rt)) l ->
          In attr (List.map fst rt) ->
          Forall has_index_entry_shape (gallina_to_idx (VList l)).
      Proof.
        intros * H_ty H_in. induction H_ty; simpl; auto.
        invert_type_of_value.
        specialize (dict_insert_incl (width:=width)) as H_ins.
        eapply incl_Forall; eauto.
        constructor; intuition. simpl. unfold has_index_entry_shape in *.
        lazymatch goal with
        | |- context[dict_lookup ?k ?d] => destruct (dict_lookup k d) eqn:E
        end; simpl; auto.
        eapply Forall_dict_lookup in IHH_ty; simpl in IHH_ty; eauto.
        repeat destruct_match_hyp; auto.
      Qed.

      Ltac destruct_or :=
        lazymatch goal with
          H: _ \/ _ |- _ => destruct H
        end.

      Ltac invert_pair_eq :=
        lazymatch goal with
          H: (_, _) = (_, _) |- _ => inversion H; subst
        end.

      Lemma dict_insert_preserve_SSorted : forall d k v,
          StronglySorted (dict_entry_leb (word:=word)) d ->
          StronglySorted dict_entry_leb (dict_insert k v d).
      Proof.
        induction d; intros; simpl.
        - repeat constructor.
        - case_match; invert_SSorted. unfold value_ltb, value_eqb.
          case_match.
          + constructor; auto. rewrite Forall_forall in *.
            unfold dict_entry_leb in *; simpl in *. apply value_compare_Eq_eq in E; subst; auto.
          + constructor; auto. rewrite Forall_forall in *; intros. destruct x0.
            unfold dict_entry_leb, value_leb, leb_from_compare in *; simpl in *.
            destruct_or.
            * invert_pair_eq; rewrite E; auto.
            * apply H3 in H0; simpl in H0. destruct_match_hyp; try discriminate.
              1: { lazymatch goal with
                  E: value_compare _ _ = Eq |- _ => apply value_compare_Eq_eq in E; subst end.
                   rewrite_l_to_r; trivial. }
              1: erewrite value_compare_trans; eauto.
          + constructor; auto. rewrite Forall_forall; intros ? H_in.
            apply dict_insert_incl in H_in.
            unfold dict_entry_leb, value_leb, leb_from_compare in *; simpl in *.
            inversion H_in; subst.
            * simpl. rewrite value_compare_antisym. rewrite E. auto.
            * eapply List.Forall_In in H3; eauto.
      Qed.

      Lemma gallina_list_to_idx_SSorted : forall l rt,
          Forall (fun v => type_of_value v (TRecord rt)) l ->
          In attr (List.map fst rt) ->
          StronglySorted dict_entry_leb (gallina_to_idx (VList l)).
      Proof.
        intros; induction l; simpl; try constructor.
        invert_Forall. invert_type_of_value_clear.
        apply dict_insert_preserve_SSorted; auto.
      Qed.

      Lemma gallina_to_idx_LikeBag : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          consistent LikeBag v (VList (concat_VList_V (List.map snd (gallina_to_idx v)))).
      Proof.
        unfold is_tbl_ty; intros. repeat destruct_match_hyp; try discriminate.
        rewrite inb_true_iff in *; invert_type_of_value_clear. simpl.
        apply Permutation_sym.
        induction H4; simpl in *; auto. invert_type_of_value_clear.
        eapply perm_trans.
        1:{ eapply dict_insert_lookup_Permutation.
            - eapply gallina_list_to_idx_shape; eauto.
            - eapply gallina_list_to_idx_SSorted; eauto. }
        1: constructor; auto.
      Qed.

      Lemma gallina_from_idx__concat_VList_V : forall l,
          Forall has_index_entry_shape l ->
          gallina_from_idx (VDict l) = concat_VList_V (List.map snd l).
      Proof.
        intros * H.
        induction l; simpl; auto. invert_Forall.
        case_match; auto. simpl in *. rewrite IHl; auto.
      Qed.

      Lemma gallina_to_from_LikeBag : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          consistent LikeBag
            v
            (VList (gallina_from_idx (VDict (gallina_to_idx v)))).
      Proof.
        intros. eapply consistent_tran'.
        1: eapply gallina_to_idx_LikeBag; eauto.
        rewrite gallina_from_idx__concat_VList_V; auto using consistent_refl.
        unfold is_tbl_ty in *.
        repeat destruct_match_hyp; try discriminate.
        rewrite inb_true_iff in *. invert_type_of_value_clear.
        eapply gallina_list_to_idx_shape; eauto.
      Qed.

      Lemma to_from_LikeBag : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          consistent LikeBag
            v
            (interp_expr map.empty (map.put map.empty hole (interp_expr map.empty (map.put map.empty hole v) to_idx)) from_idx).
      Proof.
        intros.
        erewrite fiat2_gallina_to_idx, fiat2_gallina_from_idx;
          eauto using gallina_to_from_LikeBag, gallina_to_idx_ty.
      Qed.

      Lemma idx_wf__has_index_entry_shape : forall l,
          idx_wf (VDict l) -> Forall has_index_entry_shape l.
      Proof.
        unfold idx_wf, index_wf; intros. rewrite Forall_forall.
        intros. apply_Forall_In. unfold has_index_entry_shape.
        destruct_match_hyp; auto. unfold record_proj.
        repeat destruct_match_hyp; intuition auto.
      Qed.

      Lemma dict_insert_Lt : forall k (v : value) d,
          (forall p, In p d -> value_compare k (fst p) = Lt) ->
          dict_insert k v d = (k, v) :: d.
      Proof.
        destruct d; simpl; auto; intros.
        repeat case_match; auto.
        all: lazymatch goal with
               H: forall _, (?k, ?v) = _ \/ _ -> _ |- _ => specialize H with (k, v)
             end;
          simpl in *; intuition.
        1:{ lazymatch goal with
            H: value_eqb _ _ = true |- _ => apply value_eqb_eq in H; subst
          end.
            rewrite value_compare_refl in *; congruence. }
        1:{ unfold value_ltb in *.
            lazymatch goal with
              H: context[match ?x with _ => _ end], E: ?x = _ |- _ => rewrite E in H
            end. congruence. }
      Qed.

      Lemma NoDup_SSorted__Lt : forall (k v : value) d,
          NoDup (k :: List.map fst d) ->
          StronglySorted dict_entry_leb ((k, v) :: d) ->
          forall p, In p d -> value_compare k (fst p) = Lt.
      Proof.
        intros. invert_NoDup; invert_SSorted. destruct p; simpl.
        apply_Forall_In; unfold dict_entry_leb in *; simpl in *.
        unfold value_leb, leb_from_compare in *.
        lazymatch goal with |- ?x = _ => destruct x eqn:E end; try congruence.
        apply value_compare_Eq_eq in E; subst. apply in_map with (f:=fst) in H1; intuition.
      Qed.

      Lemma gallina_from_idx_ty : forall v t,
          type_wf t ->
          is_tbl_ty t = true ->
          type_of_value v (idx_ty t) ->
          type_of_value (VList (gallina_from_idx v)) t.
      Proof.
        intros. erewrite <- fiat2_gallina_from_idx; eauto.
        eapply type_sound;
          eauto using from_idx_ty, idx_ty_wf with fiat2_hints.
      Qed.

      Lemma gallina_from_to_LikeList : forall v t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v (idx_ty t) ->
          idx_wf v ->
          consistent LikeList v
            (VDict (gallina_to_idx (VList (gallina_from_idx v)))).
      Proof.
        unfold is_tbl_ty, idx_ty, index_type; intros.
        repeat destruct_match_hyp; try discriminate.
        invert_type_of_value_clear.
        rewrite consistent_LikeList_eq. f_equal.
        rewrite gallina_from_idx__concat_VList_V;
          auto using idx_wf__has_index_entry_shape.
        simpl. unfold record_proj.
        induction l0; simpl in *; auto. unfold record_proj.
        invert_Forall; invert_NoDup; invert_SSorted.
        destruct a; simpl in *.
        destruct_and. invert_type_of_value_clear.
        do 2 (invert_Forall2; destruct_and). invert_Forall2.
        destruct x0, x1; simpl in *; subst.
        do 2 invert_type_of_value_clear.
        rewrite List.assoc_app_cons, fold_right_app.
        rewrite <- IHl0; auto.
        2: lazymatch goal with
             H: index_wf (_ :: _) |- _ =>
               apply index_wf_step_inv in H
           end; auto.
        unfold idx_wf, index_wf in H2; invert_Forall; simpl in *.
        destruct_and.
        induction l2; simpl; repeat rewrite_l_to_r.
        1:{ rewrite dict_lookup_Lt, dict_insert_Lt;
            eauto using NoDup_SSorted__Lt. }
        1:{ rewrite <- IHl2; auto.
            all: repeat invert_Forall; try now (intuition auto).
            2: repeat (constructor; simpl in *; auto).
            invert_type_of_value_clear. rewrite_l_to_r.
            simpl. rewrite value_eqb_refl.
            unfold value_ltb. rewrite value_compare_refl. auto. }
      Qed.

      Lemma from_to_LikeList : forall v t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v (idx_ty t) ->
          idx_wf v ->
          consistent LikeList v
            (interp_expr map.empty (map.put map.empty hole (interp_expr map.empty (map.put map.empty hole v) from_idx)) to_idx).
      Proof.
        intros. erewrite fiat2_gallina_from_idx, fiat2_gallina_to_idx;
          eauto using gallina_from_to_LikeList, gallina_from_idx_ty.
      Qed.

      Instance dict_idx : IndexInterface.index := IndexInterface.mk hole to_idx from_idx idx_ty is_tbl_ty.

      Instance dict_idx_ok : IndexInterface.ok LikeBag LikeList dict_idx idx_wf consistent := IndexInterface.Build_ok dict_idx idx_wf idx_ty_wf to_idx_ty from_idx_ty to_idx_wf to_from_LikeBag from_to_LikeList.

      (* Every string in l equals s *)
      Fixpoint all_eqb' (s : string) (l : list string) : bool :=
        match l with
        | nil => true
        | x :: l => String.eqb x s && all_eqb' s l
        end.

      Fixpoint all_eqb (l : list (string * list string)) : bool :=
        match l with
        | nil => true
        | (s, sl) :: l => all_eqb' s sl && all_eqb l
        end.

      Fixpoint all_neqb' (s : string) (l : list string) : bool :=
        match l with
        | nil => true
        | x :: l => negb (String.eqb x s) && all_neqb' s l
        end.

      Fixpoint all_neqb (l : list string) : bool :=
        match l with
        | nil => true
        | x :: l => all_neqb' x l && all_neqb l
        end.

      Ltac destruct_subexpr :=
        multimatch goal with
        | e : expr |- _ => destruct e; auto; []
        | o : unop |- _ => destruct o; auto; []
        | o : binop |- _ => destruct o; auto; []
        | a : atom |- _ => destruct a; auto; []
        | t : option type |- _ => destruct t; auto; []
        | l : list (expr * expr) |- _ => destruct l; auto; []
        | l : list (string * expr) |- _ => destruct l; auto; []
        | p : string * expr |- _ => destruct p; auto; []
        | s : string |- _ => destruct s; auto; []
        | a : Ascii.ascii |- _ => destruct a; auto; []
        | b : bool |- _ => destruct b; auto; []
        end.

      Notation elist_to_idx tup0 tup1 tup2 tup3 tup4 acc0 acc1 acc2 x0 x1 x2 attr0 attr1 d :=
        (EFold d (EDict []) tup0 acc0
           (EInsert (EVar acc1) (EAccess (EVar tup1) attr0) (EOptMatch (ELookup (EVar acc2) (EAccess (EVar tup2) attr1)) (ERecord [("0", EAtom (ANil None)); ("1", EVar tup3)]) x0 (ERecord [("0", EBinop OCons (EVar tup4) (EAccess (EVar x1) "0")); ("1", EAccess (EVar x2) "1")] )))).

      Notation eidx_to_list k v0 v1 v2 acc0 acc1 d :=
        (EDictFold d (EAtom (ANil None)) k v0 acc0 (EBinop OConcat (EAccess (EVar v1) "0") (EBinop OCons (EAccess (EVar v2) "1") (EVar acc1)))).

      Notation efilter_neq x0 x1 attr0 k l :=
        (EFilter l x0 (EUnop ONot (EBinop OEq (EAccess (EVar x1) attr0) k))).

      Section eq_filter_to_lookup.
        Context (p : string).

        Definition eq_filter_to_lookup_head (tbl : string) (e : expr) :=
          (* filter (idx_to_list idx) (fun row => row.attr == e') -->
           match (lookup idx e') with none => nil | some p => fst p ++ [snd p] *)
          match e with
          | EFilter
              (eidx_to_list k0 v0 v1 v2 acc0 acc1 (ELoc tbl0))
              x
              (EBinop OEq (EAccess (EVar x0) attr0) e') =>
              if (all_eqb [(v0, [v1; v2]); (acc0, [acc1]); (tbl, [tbl0]); (attr, [attr0]); (x, [x0])] &&
                    all_neqb [k0; v0; acc0] &&
                    negb (free_immut_in x e'))%bool
              then EOptMatch (ELookup (ELoc tbl) e')
                     enil
                     p (EBinop OConcat (ofst (EVar p)) (econs (osnd (EVar p)) enil))
              else e
          | _ => e
          end.

        Definition gallina_filter_access_eq (s : string) (v0 : value) (l : list value) :=
          filter (fun v => value_eqb match v with
                             | VRecord r => record_proj s r
                             | _ => VUnit
                             end v0) l.

        Lemma fiat2_gallina_filter_access_eq :
          forall (store env : locals) e1 e2 x s l,
            interp_expr store env e1 = VList l ->
            free_immut_in x e2 = false ->
            interp_expr store env (EFilter e1 x (EBinop OEq (EAccess (EVar x) s) e2)) =
              VList (gallina_filter_access_eq s (interp_expr store env e2) l).
        Proof.
          intros * H1 H_free; simpl. rewrite H1. f_equal. apply filter_ext. intro a.
          unfold get_local. rewrite map.get_put_same. rewrite <- not_free_immut_put_sem; auto.
        Qed.

        Lemma eq_filter_to_lookup_head_preserve_ty : forall tbl t (Gstore : tenv),
            type_wf t -> is_tbl_ty t ->
            map.get Gstore tbl = Some (idx_ty t) ->
            preserve_ty Gstore (eq_filter_to_lookup_head tbl).
        Proof.
          clear H_NoDup.
          unfold preserve_ty, is_tbl_ty. intros.
          repeat destruct_match_hyp; try congruence.
          repeat destruct_subexpr. simpl.
          case_match; auto. repeat rewrite Bool.andb_true_r in *.
          repeat rewrite Bool.andb_true_iff in *; intuition. rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
          repeat invert_type_of. repeat rewrite_map_get_put_hyp.
          repeat (clear_refl; repeat do_injection).
          repeat (econstructor; eauto).
          1:{ lazymatch goal with H: ?x = _, H': ?x = _ |- _ => rewrite H in H' end.
              do_injection. do_injection. simpl in *; do_injection.
              unfold get_attr_type. lazymatch goal with H: ?x = _ |- context[?x] => rewrite H end.
              eapply not_free_immut_put_ty; eauto. }
          all: rewrite map.get_put_same; trivial.
        Qed.

        Lemma eq_filter_to_lookup_preserve_ty' :
          forall Gstore tbl t,
            type_wf t -> is_tbl_ty t ->
            map.get Gstore tbl = Some (idx_ty t) ->
            preserve_ty Gstore (fold_expr (eq_filter_to_lookup_head tbl)).
        Proof.
          clear H_NoDup.
          intros. apply fold_expr_preserve_ty.
          eapply eq_filter_to_lookup_head_preserve_ty; eauto.
        Qed.

        Lemma eq_filter_to_lookup_preserve_ty :
          forall c Gstore Genv tbl t,
            tenv_wf Gstore -> tenv_wf Genv ->
            type_wf t -> is_tbl_ty t ->
            tenv_wf_with_globals [tbl] [idx_ty t] Gstore ->
            well_typed Gstore Genv c -> well_typed Gstore Genv (fold_command_with_globals [tbl] (eq_filter_to_lookup_head tbl) c).
        Proof.
          clear H_NoDup.
          intros. eapply fold_command_with_globals_preserve_ty.
          5: eauto.
          all: simpl in *; auto.
          intros. eapply eq_filter_to_lookup_head_preserve_ty; eauto.
          unfold tenv_wf_with_globals in *; invert_Forall2; eauto.
        Qed.

        Lemma dict_lookup__filter_none : forall k idx,
            index_wf idx ->
            dict_lookup k idx = None ->
            gallina_filter_access_eq attr k (gallina_from_idx (VDict idx)) = nil.
        Proof.
          unfold gallina_filter_access_eq, gallina_from_idx, record_proj.
          intros. induction idx; simpl; auto. unfold record_proj.
          destruct a; simpl in *. case_match; auto.
          inversion H; subst; simpl in *.
          destruct (access_record l "0"); intuition; destruct a; intuition.
          destruct (access_record l "1"); intuition; destruct a; intuition.
          rewrite filter_app. destruct (value_eqb k0 v0) eqn:E.
          1: congruence. simpl.
          rewrite H3; auto.
          rewrite_l_to_r. rewrite value_eqb_sym, E, app_nil_r.
          lazymatch goal with
          | H: Forall _ l0 |- _ => induction H; simpl; auto end. rewrite IHForall.
          case_match; intuition. rewrite_l_to_r. rewrite value_eqb_sym, E. reflexivity.
        Qed.

        Lemma not_In__dict_lookup : forall (v : value) d, ~ In v (List.map fst d) -> dict_lookup v d = None.
        Proof.
          intros * H. induction d; simpl; auto.
          destruct a; simpl in *. intuition. case_match; auto.
          apply value_eqb_eq in E; subst; intuition.
        Qed.

        Lemma Forall_false__filter : forall A f (l : list A), Forall (fun x => f x = false) l -> filter f l = nil.
        Proof.
          intros * H; induction l; simpl; auto. simpl in H.
          inversion H; subst. rewrite H2. auto.
        Qed.

        Lemma gallina_from_idx_cons : forall a idx,
            index_wf (a :: idx) ->
            gallina_from_idx (VDict (a :: idx)) = List.app (gallina_from_idx (VDict [a])) (gallina_from_idx (VDict idx)).
        Proof.
          unfold index_wf. destruct a; simpl.
          intros. invert_Forall; simpl in *.
          case_match; intuition auto. unfold record_proj.
          repeat (case_match; intuition auto).
          rewrite <- app_assoc. f_equal; auto.
        Qed.

        Lemma dict_lookup__filter_some : forall k idx kt vt l v,
            index_wf idx ->
            type_of_value (VDict idx) (TDict kt vt) ->
            dict_lookup k idx = Some (VRecord [("0", VList l); ("1", v)]) ->
            gallina_filter_access_eq attr k (gallina_from_idx (VDict idx)) = (l ++ [v])%list.
        Proof.
          intros. unfold gallina_filter_access_eq.
          induction idx.
          1: unfold dict_lookup in *; discriminate.
          rewrite gallina_from_idx_cons; auto.
          rewrite filter_app.
          destruct a. invert_type_of_value.
          simpl. unfold index_wf in *.
          repeat invert_Forall; simpl in *.
          repeat (destruct_match_hyp; intuition auto);
            [ lazymatch goal with
                E: value_eqb _ _ = _ |- _ =>
                  apply value_eqb_eq in E; subst
              end
            | ].
          1:{ rewrite <- app_nil_r. f_equal.
              1:{ do_injection. cbn.
                  apply forallb_filter_id. rewrite forallb_app.
                  simpl in *. repeat do_injection.
                  rewrite Bool.andb_true_iff; split.
                  1:{ rewrite forallb_forall; intros.
                      apply_Forall_In. destruct_match_hyp; intuition auto.
                      unfold record_proj; rewrite_l_to_r; apply value_eqb_refl. }
                  1:{ simpl. unfold record_proj; rewrite_l_to_r.
                      rewrite Bool.andb_true_r; apply value_eqb_refl. } }
              1:{ apply dict_lookup__filter_none; auto.
                  apply not_In__dict_lookup.
                  invert_NoDup; auto. } }
          1:{ rewrite <- app_nil_l. f_equal.
              1:{ apply Forall_false__filter.
                  rewrite Forall_forall; intros.
                  unfold record_proj in *; repeat rewrite_l_to_r.
                  lazymatch goal with
                    H: In _ (_ ++ _) |- _ => apply in_app_or in H end.
                  intuition auto.
                  1:{ apply_Forall_In. destruct_match_hyp; intuition auto.
                      rewrite_l_to_r; eauto using value_eqb_sym. }
                  1:{ lazymatch goal with
                      H: In _ (_ :: nil) |- _ => inversion H; subst;
                                                 [ | exfalso; eapply in_nil; eauto ] end.
                      rewrite_l_to_r; eauto using value_eqb_sym. } }
              1:{ apply H7; auto.
                  invert_NoDup; invert_SSorted; constructor; auto. } }
        Qed.

        Ltac rewrite_expr_value :=
          lazymatch goal with
          | H: VList _ = _ |- _ => rewrite <- H in *
          | H: VDict _ = _ |- _ => rewrite <- H in *
          end.

        Lemma eq_filter_to_lookup_head_preserve_sem : forall tbl (Gstore : tenv) (store : locals) t,
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (idx_ty t) ->
            holds_for_all_entries (index_wf_with_globals [tbl]) store ->
            preserve_sem Gstore store (eq_filter_to_lookup_head tbl).
        Proof.
          unfold preserve_sem; intros. unfold holds_for_all_entries, index_wf_with_globals in *.
          unfold is_tbl_ty, idx_ty in *. do 2 (destruct_match_hyp; try discriminate).
          lazymatch goal with
            H: context[get_attr_type] |- _ =>
              let H_tbl_ty := fresh "H_tbl_ty" in
              eapply TyELoc in H as H_tbl_ty
          end. apply_type_sound (ELoc tbl).
          assert(H_wf: index_wf l0).
          { symmetry in H8. unfold get_local in H8. destruct_match_hyp; try discriminate.
            apply H2 in E. rewrite Forall_forall in E. specialize (E tbl). destruct E; simpl; intuition auto.
            simpl in *. unfold idx_wf in *. subst. auto. }
          repeat destruct_subexpr. unfold eq_filter_to_lookup_head.
          lazymatch goal with |- context[if ?x then _ else _] => destruct x eqn:E' end; auto.
          repeat rewrite Bool.andb_true_r in *. simpl in E'.
          repeat rewrite Bool.andb_true_iff in E'; intuition.
          rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
          repeat invert_type_of. repeat rewrite_map_get_put_hyp.
          repeat do_injection. erewrite sem_eq_eq.
          3,4: eauto.
          2:{ unfold sem_eq. eapply EFilter_Proper; auto.
              2: apply singleton_rel_refl.
              2:{ apply sem_eq_refl. repeat (econstructor; eauto).
                  rewrite_map_get_put_goal; auto. }
              apply fold_from_idx; simpl; intuition auto.
              1: constructor; auto.
              1:{ rewrite inb_true_iff.
                  lazymatch goal with
                    H: access_record ?tl ?attr = Success _ |- In ?attr (List.map fst ?tl) =>
                      apply access_record_sound, in_map with (f:=fst) in H
                  end. auto. }
              1:{ constructor.
                  lazymatch goal with
                    H1: map.get ?Gstore ?tbl = _, H2: map.get ?Gstore ?tbl = _ |- _ =>
                      rewrite H1 in H2; unfold index_type in H2
                  end.
                  repeat (clear_refl; repeat do_injection).
                  simpl in *; repeat do_injection. auto. } }
          erewrite fiat2_gallina_filter_access_eq; auto.
          2:{ erewrite fiat2_gallina_from_idx_sem with (t:=TList (TRecord l)); simpl.
              3-8: eauto. all: try constructor; auto. }
          simpl in H'. simpl. rewrite_expr_value.
          specialize (dict_lookup_sound (width:=width) l0) as H_lookup.
          eapply (H_lookup _ _ (interp_expr store env e2_2)) in H'; eauto.
          2:{ unfold get_attr_type. lazymatch goal with
              H: ?x = _, H': ?x = _ |- _ => rewrite H in H'
            end. repeat (clear_refl; repeat do_injection).
              simpl in *; repeat do_injection. simpl in *; do_injection. rewrite_l_to_r.
              lazymatch goal with
                H: context[free_immut_in] |- _ =>
                  eapply not_free_immut_put_ty in H; eauto
              end.
              eapply type_sound; eauto. }
          inversion H'; subst.
          2: unfold get_local; rewrite map.get_put_same.
          (* dict_lookup found no match *)
          1:{ f_equal; apply dict_lookup__filter_none; auto. }
          (* dict_lookup found some match *)
          1:{ lazymatch goal with
              H: type_of_value ?v _ |- context[?v] => inversion H; subst end.
              repeat invert_Forall2.
              destruct x1, x2; repeat destruct_and; simpl in * |-; subst.
              unfold record_proj, access_record. repeat rewrite String.eqb_refl.
              lazymatch goal with
                H: type_of_value v1 _ |- _ => inversion H; subst end.
              f_equal. case_match; simpl in * |-; try congruence.
              eapply dict_lookup__filter_some; eauto; try congruence.
              constructor. 3-5: eauto.
              all: auto. }
        Qed.

        Lemma eq_filter_to_lookup_preserve_sem' :
          forall Gstore store tbl t,
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (idx_ty t) ->
            holds_for_all_entries (index_wf_with_globals [tbl]) store ->
            preserve_sem Gstore store (fold_expr (eq_filter_to_lookup_head tbl)).
        Proof.
          unfold is_tbl_ty; intros. repeat destruct_match_hyp; try congruence.
          apply fold_expr_preserve_sem.
          1: eapply eq_filter_to_lookup_head_preserve_ty; eauto.
          eapply eq_filter_to_lookup_head_preserve_sem with (Gstore:=Gstore); eauto.
        Qed.

        Lemma eq_filter_to_lookup_preserve_sem :
          forall c (Gstore Genv : tenv) (store env : locals) tbl t,
            tenv_wf Gstore -> tenv_wf Genv ->
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (idx_ty t) ->
            tenv_wf_with_globals [tbl] [idx_ty t] Gstore ->
            parameterized_wf Gstore Genv (index_wf_with_globals [tbl]) c ->
            locals_wf Gstore store -> locals_wf Genv env ->
            holds_for_all_entries (index_wf_with_globals [tbl]) store ->
            interp_command store env c = interp_command store env (fold_command_with_globals [tbl] (eq_filter_to_lookup_head tbl) c).
        Proof.
          unfold is_tbl_ty; intros. repeat destruct_match_hyp; try congruence.
          eapply fold_command_with_globals_preserve_sem with (Gstore:=Gstore); simpl in *; auto.
          5-7: eauto.
          all: intros; simpl in *; auto.
          1:{ unfold tenv_wf_with_globals in *.
              invert_Forall2. eapply eq_filter_to_lookup_head_preserve_ty; eauto. }
          1:{ eapply eq_filter_to_lookup_head_preserve_sem with (Gstore:=Gstore0); eauto.
              simpl. unfold tenv_wf_with_globals in *. invert_Forall2. auto. }
        Qed.

        Lemma eq_filter_to_lookup_preserve_index_wf :
          forall c Gstore Genv tbl t,
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (idx_ty t) ->
            tenv_wf Gstore -> tenv_wf Genv ->
            tenv_wf_with_globals [tbl] [idx_ty t] Gstore ->
            parameterized_wf Gstore Genv (index_wf_with_globals [tbl]) c -> parameterized_wf Gstore Genv (index_wf_with_globals [tbl]) (fold_command_with_globals [tbl] (eq_filter_to_lookup_head tbl) c).
        Proof.
          unfold is_tbl_ty; intros. repeat destruct_match_hyp; try congruence.
          eapply fold_command_with_globals_preserve_index_wf.
          6: eauto.
          all: simpl in *; auto; intros.
          all:  unfold tenv_wf_with_globals in *; repeat invert_Forall2.
          1: eapply eq_filter_to_lookup_head_preserve_ty; eauto.
          1: eapply eq_filter_to_lookup_head_preserve_sem; eauto.
        Qed.

        Lemma eq_filter_to_lookup_preserve_index_wf2 :
          forall c Gstore Genv tbl t,
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (idx_ty t) ->
            tenv_wf Gstore -> tenv_wf Genv ->
            tenv_wf_with_globals [tbl] [idx_ty t] Gstore ->
            parameterized_wf Gstore Genv (index_wf_with_globals [tbl]) c -> parameterized_wf Gstore Genv (index_wf_with_globals [tbl]) (fold_command_with_globals [tbl] (eq_filter_to_lookup_head tbl) (fold_command_with_globals [tbl] (eq_filter_to_lookup_head tbl) c)).
        Proof.
          intros.
          apply compose_op_transf_preserve_parameterized_wf; auto.
          all: unfold preserve_param_wf; intros; eapply eq_filter_to_lookup_preserve_index_wf; eauto.
        Qed.

        Definition command_sem_eq (Gstore Genv : tenv) (c1 c2 : command) :=
          well_typed Gstore Genv c1 /\
            well_typed Gstore Genv c2 /\
            forall (store env : locals),
              locals_wf Gstore store -> locals_wf Genv env ->
              interp_command store env c1 = interp_command store env c2.

        Lemma CLetMut_Proper {t : type} (x0 : string) (Gstore Genv : tenv) :
          tenv_wf Gstore -> tenv_wf Genv ->
          Proper (sem_eq Gstore Genv t ==> singleton_rel x0 ==> command_sem_eq (map.put Gstore x0 t) Genv ==> command_sem_eq Gstore Genv) CLetMut.
        Proof.
          intros * ? ? e e' He y y' Hy c c' Hc.
          unfold singleton_rel, sem_eq, command_sem_eq in *.
          intuition auto; subst.
          1,2: econstructor; eauto.
          simpl. f_equal. rewrite H8, H9; eauto with fiat2_hints.
        Qed.

        Lemma eq_filter_to_lookup_preserve_sem2 :
          forall c Gstore Genv tbl t,
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (idx_ty t) ->
            tenv_wf Gstore -> tenv_wf Genv ->
            tenv_wf_with_globals [tbl] [idx_ty t] Gstore ->
            parameterized_wf Gstore Genv (index_wf_with_globals [tbl]) c ->
            forall store env,
              locals_wf Gstore store -> locals_wf Genv env ->
              holds_for_all_entries (index_wf_with_globals [tbl]) store ->
              interp_command store env c = interp_command store env (fold_command_with_globals [tbl] (eq_filter_to_lookup_head tbl) (fold_command_with_globals [tbl] (eq_filter_to_lookup_head tbl) c)).
        Proof.
          intros.
          erewrite compose_op_transf_preserve_sem; eauto.
          1: unfold preserve_param_wf; intros; eapply eq_filter_to_lookup_preserve_index_wf; eauto.
          1:{ unfold command_wf_preserve_sem; intros.
              eapply eq_filter_to_lookup_preserve_sem.
              3-10: eauto. all: auto. }
          1:{ unfold command_wf_preserve_sem; intros.
              eapply eq_filter_to_lookup_preserve_sem.
              3-10: eauto. all: auto. }
        Qed.
      End eq_filter_to_lookup.

      Section neq_filter_to_delete.
        Definition neq_filter_to_delete_head (tbl attr : string) (e : expr) :=
          (* list_to_idx (filter (idx_to_list idx) (fun row => row.attr != e)) = delete idx e *)
          match e with
          | elist_to_idx tup0 tup1 tup2 tup3 tup4 acc0 acc1 acc2 x0 x1 x2 attr0 attr1
              ((efilter_neq y0 y1 attr2 k' (eidx_to_list k0 v0 v1 v2 acc3 acc4 (ELoc tbl0))))
            => if (all_eqb [(tbl, [tbl0]); (v0,[v1; v2]); (acc0, [acc1; acc2; acc3; acc4]); (y0, [y1]); (tup0, [tup1; tup2; tup3; tup4]); (attr, [attr0; attr1; attr2]); (x0, [x1; x2])] &&
                     all_neqb [acc0; tup0; v0; k0; x0] &&
                     negb (free_immut_in y0 k'))%bool
               then EDelete (ELoc tbl) k'
               else e
          | _ => e
          end.

        Definition gallina_filter_access_neq (s : string) (v0 : value) (l : list value) :=
          filter (fun v => negb (value_eqb match v with
                                   | VRecord r => record_proj s r
                                   | _ => VUnit
                                   end v0)) l.

        Lemma fiat2_gallina_filter_access_neq :
          forall (store env : locals) e1 e2 x s l,
            interp_expr store env e1 = VList l ->
            free_immut_in x e2 = false ->
            interp_expr store env (EFilter e1 x (EUnop ONot (EBinop OEq (EAccess (EVar x) s) e2))) =
              VList (gallina_filter_access_neq s (interp_expr store env e2) l).
        Proof.
          intros * H1 H_free; simpl. rewrite H1. f_equal. apply filter_ext. intro a.
          unfold get_local. rewrite map.get_put_same. rewrite <- not_free_immut_put_sem; auto.
        Qed.

        Lemma neq_filter_to_delete_head_preserve_ty : forall tbl t (Gstore : tenv),
            type_wf t -> is_tbl_ty t ->
            map.get Gstore tbl = Some (idx_ty t) ->
            preserve_ty Gstore (neq_filter_to_delete_head tbl attr).
        Proof.
          clear H_NoDup.
          unfold is_tbl_ty, preserve_ty; intros.
          repeat destruct_match_hyp; try congruence.
          repeat destruct_subexpr. simpl. case_match; auto.
          repeat rewrite Bool.andb_true_r in E1. repeat rewrite Bool.andb_true_iff in E1; intuition idtac.
          rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
          repeat invert_type_of. repeat rewrite_map_get_put_hyp. repeat (clear_refl; repeat do_injection).
          repeat constructor; auto.
          1:{ lazymatch goal with
              H: map.get Gstore tbl = _, H': map.get Gstore tbl = _ |- _ =>
                rewrite H in *; do_injection; simpl in *; do_injection
            end.
              unfold get_attr_type.
              lazymatch goal with
              | H1: ?x = _, H2: ?x = _ |- _ => rewrite H1 in H2 end.
              do_injection.
              lazymatch goal with
              | H: context[?x] |- context[match ?x with _ => _ end] =>
                  rewrite H end.
              repeat clear_refl. unfold index_type. do 3 f_equal.
              repeat invert_Forall2. repeat invert_type_of.
              repeat rewrite_map_get_put_hyp.
              repeat rewrite_l_to_r; repeat (try clear_refl; do_injection).
              do 3 (destruct tl1; simpl in *; try congruence). destruct p, p0; simpl in *.
              do 3 (destruct tl; simpl in *; try congruence). destruct p, p0; simpl in *.
              repeat (lazymatch goal with
                        H: cons _ _ = cons _ _ |- _ => inversion H; subst; auto end;
                      clear_refl).
              multimatch goal with
                H: Permutation _ _ |- _ => apply Permutation_length_2_inv in H; destruct H end.
              all: lazymatch goal with
                     H: _ = cons _ _ |- _ => inversion H; subst; auto end.
              2:{ invert_SSorted. invert_Forall. unfold record_entry_leb in *; simpl in *.
                  lazymatch goal with H: is_true (_ <=? _) |- _ => inversion H end. }
              simpl in *; do_injection. auto. }
          1:{ repeat lazymatch goal with
                  H: ?x = _, H': ?x = _ |- _ => rewrite H in H'
                end. repeat (clear_refl; repeat do_injection).
              eapply not_free_immut_put_ty; eauto. }
        Qed.

        Lemma neq_filter_to_delete_preserve_ty' :
          forall Gstore tbl t,
            type_wf t -> is_tbl_ty t ->
            map.get Gstore tbl = Some (idx_ty t) ->
            preserve_ty Gstore (fold_expr (neq_filter_to_delete_head tbl attr)).
        Proof.
          clear H_NoDup.
          intros. apply fold_expr_preserve_ty.
          eapply neq_filter_to_delete_head_preserve_ty; eauto.
        Qed.

        Lemma neq_filter_to_delete_preserve_ty :
          forall c Gstore Genv tbl t,
            type_wf t -> is_tbl_ty t = true ->
            tenv_wf Gstore -> tenv_wf Genv ->
            tenv_wf_with_globals [tbl] [idx_ty t] Gstore ->
            well_typed Gstore Genv c -> well_typed Gstore Genv (fold_command_with_globals [tbl] (neq_filter_to_delete_head tbl attr) c).
        Proof.
          clear H_NoDup.
          intros. eapply fold_command_with_globals_preserve_ty.
          5: eauto.
          all: simpl in *; auto.
          intros. eapply neq_filter_to_delete_head_preserve_ty; eauto.
          unfold tenv_wf_with_globals in *; invert_Forall2; eauto.
        Qed.

        Lemma not_In__dict_delete : forall (k : value) d, ~ In k (List.map fst d) -> dict_delete k d = d.
        Proof.
          induction d; intros; simpl; auto.
          destruct a; case_match; simpl in *.
          1:apply value_eqb_eq in E; subst; intuition.
          f_equal. auto.
        Qed.

        Lemma gallina_filter_access_neq_from_idx : forall k idx kt vt,
            idx_wf (VDict idx) ->
            type_of_value (VDict idx) (TDict kt vt) ->
            gallina_filter_access_neq attr k (gallina_from_idx (VDict idx)) = gallina_from_idx (VDict (dict_delete k idx)).
        Proof.
          intros * H. simpl. unfold record_proj; induction idx; auto.
          simpl. unfold idx_wf, index_wf in *; invert_Forall. destruct_match_hyp; intuition auto; simpl in *.
          repeat destruct_match_hyp; intuition auto. repeat rewrite_l_to_r.
          destruct a; simpl in *.
          unfold gallina_filter_access_neq in *. rewrite filter_app. simpl. rewrite_l_to_r.
          invert_type_of_value; simpl in *; invert_Forall; invert_NoDup; invert_SSorted.
          destruct (value_eqb k0 v0) eqn:E_k0v0.
          1:{ apply value_eqb_eq in E_k0v0; subst.
              lazymatch goal with
                H: context[?x = _] |- context[?x] => rewrite H end.
              2: constructor; auto.
              unfold record_proj. rewrite_l_to_r. rewrite value_eqb_refl; simpl.
              rewrite not_In__dict_delete; auto.
              rewrite Forall_false__filter; auto. rewrite Forall_forall; intros. apply_Forall_In.
              destruct_match_hyp; intuition auto. rewrite_l_to_r. rewrite value_eqb_refl; auto. }
          1:{ simpl. lazymatch goal with
              H: context[?x = _] |- context[?x] => rewrite H end.
              2: constructor; auto.
              unfold record_proj; rewrite value_eqb_sym; repeat rewrite_l_to_r.
              simpl. f_equal.
              f_equal. apply forallb_filter_id. rewrite forallb_forall; intros; apply_Forall_In.
              destruct_match_hyp; intuition. rewrite_l_to_r. rewrite value_eqb_sym. rewrite_l_to_r; auto. }
        Qed.

        Lemma dict_delete_preserve_index_wf : forall idx,
            idx_wf (VDict idx) ->
            forall k, idx_wf (VDict (dict_delete k idx)).
        Proof.
          intros * H_wf *.
          induction idx; simpl; auto.
          destruct a. destruct (value_eqb k0 v0).
          all: apply index_wf_step_inv in H_wf as H_wf'; auto.
          specialize (IHidx H_wf').
          unfold idx_wf, index_wf in H_wf; invert_Forall.
          unfold idx_wf, index_wf; simpl; intuition auto.
        Qed.

        Lemma neq_filter_to_delete_head_preserve_sem : forall tbl (Gstore : tenv) (store : locals) t,
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (idx_ty t) ->
            holds_for_all_entries (index_wf_with_globals [tbl]) store ->
            preserve_sem Gstore store (neq_filter_to_delete_head tbl attr).
        Proof.
          unfold preserve_sem, is_tbl_ty; intros.
          repeat destruct_match_hyp; try congruence.
          unfold holds_for_all_entries, index_wf_with_globals in *.
          repeat destruct_subexpr. unfold neq_filter_to_delete_head in *. case_match; auto.
          simpl in * |-. repeat rewrite Bool.andb_true_r in * |-.
          repeat rewrite Bool.andb_true_iff in * |-; intuition idtac.
          rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
          assert (type_of Gstore Genv (efilter_neq x0 x0 attr e1_2_2 (eidx_to_list k0 v1 v1 v1 acc0 acc0 (ELoc tbl))) (TList (TRecord l))).
          { do 3 invert_type_of.
            assert(t1 = TRecord l).
            { repeat invert_type_of; repeat rewrite_map_get_put_hyp.
              rewrite_l_to_r. unfold index_type in *; do_injection.
              simpl in *. congruence. }
            subst; auto. }
          erewrite sem_eq_eq with (t:=idx_ty (TList (TRecord l))).
          3,4: eauto.
          2: apply fold_to_idx; eauto; simpl; intuition auto.
          erewrite fiat2_gallina_to_idx_sem.
          3-7: eauto.
          all: auto.
          erewrite fiat2_gallina_filter_access_neq; auto.
          2:{ erewrite sem_eq_eq; eauto.
              2: apply fold_from_idx; simpl; intuition eauto.
              2: constructor; auto.
              1: eapply fiat2_gallina_from_idx_sem.
              2-7: eauto.
              2: constructor.
              all: auto. }
          cbn [interp_expr]. unfold get_local.
          lazymatch goal with
            H1: locals_wf Gstore store, H2: map.get Gstore _ = _ |- _ => apply H1 in H2 end.
          destruct_match_hyp; intuition idtac.
          invert_type_of_value.
          apply H2 in E; invert_Forall; destruct_or; intuition auto.
          erewrite gallina_filter_access_neq_from_idx; eauto.
          apply consistent_LikeList_eq.
          rewrite <- gallina_from_to_LikeList with (t:=TList (TRecord l)); auto.
          1:{ apply dict_delete_sound; eauto.
              repeat invert_type_of. unfold get_attr_type.
              repeat rewrite_map_get_put_hyp. repeat do_injection.
              eapply type_sound.
              1:{ rewrite_l_to_r. eapply not_free_immut_put_ty; eauto. }
              all: auto. }
          1: apply dict_delete_preserve_index_wf; auto.
        Qed.

        Lemma neq_filter_to_delete_preserve_sem' :
          forall Gstore store tbl t,
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (idx_ty t) ->
            holds_for_all_entries (index_wf_with_globals [tbl]) store ->
            preserve_sem Gstore store (fold_expr (neq_filter_to_delete_head tbl attr)).
        Proof.
          intros. apply fold_expr_preserve_sem.
          1: eapply  neq_filter_to_delete_head_preserve_ty; eauto.
          eapply  neq_filter_to_delete_head_preserve_sem with (Gstore:=Gstore); eauto.
        Qed.

        Lemma neq_filter_to_delete_preserve_sem :
          forall c (Gstore Genv : tenv) (store env : locals) tbl t,
            type_wf t -> is_tbl_ty t = true ->
            tenv_wf Gstore -> tenv_wf Genv ->
            tenv_wf_with_globals [tbl] [idx_ty t] Gstore ->
            parameterized_wf Gstore Genv (index_wf_with_globals [tbl]) c ->
            locals_wf Gstore store -> locals_wf Genv env ->
            holds_for_all_entries (index_wf_with_globals [tbl]) store ->
            interp_command store env c = interp_command store env (fold_command_with_globals [tbl] (neq_filter_to_delete_head tbl attr) c).
        Proof.
          intros.
          eapply fold_command_with_globals_preserve_sem with (Gstore:=Gstore); simpl in *; auto.
          6: eauto.
          all: intros; simpl in *; eauto; try reflexivity.
          all: unfold tenv_wf_with_globals in H8; inversion H8; subst.
          1: eapply neq_filter_to_delete_head_preserve_ty; eauto.
          1: eapply neq_filter_to_delete_head_preserve_sem with (Gstore:=Gstore0); eauto.
        Qed.

        Lemma neq_filter_to_delete_preserve_index_wf :
          forall c Gstore Genv tbl t,
            type_wf t -> is_tbl_ty t = true ->
            tenv_wf Gstore -> tenv_wf Genv ->
            tenv_wf_with_globals [tbl] [idx_ty t] Gstore ->
            parameterized_wf Gstore Genv (index_wf_with_globals [tbl]) c -> parameterized_wf Gstore Genv (index_wf_with_globals [tbl]) (fold_command_with_globals [tbl] (neq_filter_to_delete_head tbl attr) c).
        Proof.
          intros. eapply fold_command_with_globals_preserve_index_wf.
          6: eauto.
          all: simpl in *; auto; intros.
          all:  unfold tenv_wf_with_globals in *; repeat invert_Forall2.
          1: eapply neq_filter_to_delete_head_preserve_ty; eauto.
          1: eapply neq_filter_to_delete_head_preserve_sem; eauto.
        Qed.
      End neq_filter_to_delete.

      Definition apply_after_letmut f (c : command) :=
        match c with
        | CLetMut e x c => CLetMut e x (f c)
        | _ => c
        end.

      Lemma apply_after_letmut_preserve_ty : forall t e x c f Gstore Genv,
          type_of Gstore Genv e t ->
          well_typed (map.put Gstore x t) Genv (f c) ->
          well_typed Gstore Genv (apply_after_letmut f (CLetMut e x c)).
      Proof.
        intros. simpl; econstructor; eauto.
      Qed.

      Lemma apply_after_letmut_compose : forall f g c,
          apply_after_letmut f (apply_after_letmut g c) = apply_after_letmut (fun c => f (g c)) c.
      Proof.
        intros. destruct c; auto.
      Qed.

      Lemma apply_after_letmut_transf_to_idx : forall f free_vars e x c,
          apply_after_letmut f (transf_to_idx free_vars (CLetMut e x c)) =
            CLetMut (substitute [(hole, e)] free_vars to_idx) x (f (transf_to_idx' free_vars x c)).
      Proof.
        auto.
      Qed.

      Lemma fold_command_id_CLetMut : forall f e x c,
          fold_command id f (CLetMut e x c) = CLetMut (fold_expr f e) x (fold_command id f c).
      Proof.
        auto.
      Qed.

      Lemma apply_after_letmut_preserve_sem : forall (Gstore Genv : tenv) tbl_ty f e tbl c,
          tenv_wf Gstore -> tenv_wf Genv ->
          is_tbl_ty tbl_ty = true -> type_wf tbl_ty ->
          type_of Gstore Genv e (IndexInterface.idx_ty tbl_ty) ->
          parameterized_wf (map.put Gstore tbl (IndexInterface.idx_ty tbl_ty)) Genv (index_wf_with_globals [tbl]) c ->
          (forall (store env : locals),
              locals_wf Gstore store -> locals_wf Genv env ->
              idx_wf (interp_expr store env e)) ->
          (forall (store env : locals) c,
              locals_wf (map.put Gstore tbl (IndexInterface.idx_ty tbl_ty)) store ->
              locals_wf Genv env ->
              parameterized_wf (map.put Gstore tbl (IndexInterface.idx_ty tbl_ty)) Genv (index_wf_with_globals [tbl]) c ->
              holds_for_all_entries (index_wf_with_globals [tbl]) store ->
              interp_command store env c = interp_command store env (f c)) ->
          forall (store env : locals),
            locals_wf Gstore store -> locals_wf Genv env ->
            interp_command store env (CLetMut e tbl c) = interp_command store env (apply_after_letmut f (CLetMut e tbl c)).
      Proof.
        intros. eapply CLetMut_Proper2.
        3-10: intros; eauto.
        all: auto.
      Qed.

    End WithMap.
  End WithVars.
End WithHole.

Section WithWord.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Section ConcreteExample.
    Local Open Scope string.

    Instance ctenv : map.map string type := SortedListString.map _.
    Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

    Instance clocals : map.map string value := SortedListString.map _.
    Instance clocals_ok : map.ok clocals := SortedListString.ok _.

    Instance caenv : map.map string collection_tag := SortedListString.map _.
    Instance caenv_ok : map.ok caenv := SortedListString.ok _.

    Instance cRenv : map.map string (value -> value -> Prop) := SortedListString.map _.
    Instance cRenv_ok : map.ok cRenv := SortedListString.ok _.

    Definition attr := "department".

    Lemma H_NoDup : is_NoDup ["tup"; "acc"; "x"; "k"; "v"].
    Proof.
      simpl; intuition auto; congruence.
    Qed.

    Notation idx_wf := (idx_wf attr).
    Instance cdict_idx : IndexInterface.index := (dict_idx "hole" attr "tup" "acc" "x" "k" "v").
    Instance cdict_idx_ok : IndexInterface.ok LikeBag LikeList cdict_idx idx_wf consistent.
    apply dict_idx_ok. apply H_NoDup.
    Qed.

    Definition to_filter_transf := fold_command id to_filter_head.
    Definition lookup_transf tbl := apply_after_letmut (fold_command_with_globals [tbl] (eq_filter_to_lookup_head attr "p" tbl)).
    Definition delete_transf tbl := apply_after_letmut (fold_command_with_globals [tbl] (neq_filter_to_delete_head tbl attr)).
    Definition ex_transf1 tbl free_vars (c : command) :=
      delete_transf tbl (lookup_transf tbl (transf_to_idx free_vars (to_filter_transf c))).

    Hint Extern 5 (word.ok _) => typeclasses eauto : fiat2_hints.
    Hint Extern 5 (map.ok _) => typeclasses eauto : fiat2_hints.
    Hint Extern 5 (map.get (map.put _ ?x _) ?x = _) => rewrite_map_get_put_goal.

    Lemma to_filter_head_preserve_ty2 : forall {tenv : map.map string type},
        map.ok tenv ->
        forall Gstore,
          preserve_ty Gstore to_filter_head.
    Proof.
      unfold preserve_ty; intros; apply to_filter_head_preserve_ty; auto.
    Qed.

    Lemma to_filter_preserve_ty' : forall {tenv : map.map string type}, map.ok tenv -> forall Gstore, preserve_ty Gstore (fold_expr to_filter_head).
    Proof.
      intros. apply fold_expr_preserve_ty.
      apply to_filter_head_preserve_ty2; auto.
    Qed.

    Lemma to_filter_preserve_ty : forall {tenv : map.map string type},
        map.ok tenv ->
        forall Gstore Genv c,
          tenv_wf Gstore -> tenv_wf Genv ->
          well_typed Gstore Genv c ->
          well_typed Gstore Genv (fold_command id to_filter_head c).
    Proof.
      intros. apply fold_command_id_preserve_ty; auto.
      apply to_filter_head_preserve_ty; auto.
    Qed.

    Theorem ex_transf1_preserve_ty : forall (Gstore Genv : ctenv) free_vars tbl_ty e tbl c,
        type_of Gstore Genv e tbl_ty ->
        tenv_wf Gstore -> tenv_wf Genv ->
        IndexInterface.is_tbl_ty tbl_ty = true -> type_wf tbl_ty ->
        incl (get_free_vars Genv) free_vars ->
        well_typed (map.put Gstore tbl tbl_ty) Genv c ->
        well_typed Gstore Genv (ex_transf1 tbl free_vars (CLetMut e tbl c)).
    Proof.
      intros.
      lazymatch goal with
        H: IndexInterface.is_tbl_ty _ = _ |- _ =>
          simpl in H; unfold is_tbl_ty in H;
          repeat destruct_match_hyp; try congruence
      end.
      unfold ex_transf1, delete_transf, lookup_transf.
      rewrite apply_after_letmut_compose.
      eapply apply_after_letmut_preserve_ty.
      1:{ apply to_idx_preserve_ty; eauto with fiat2_hints.
          apply to_filter_preserve_ty'; auto with fiat2_hints. }
      1:{ eapply neq_filter_to_delete_preserve_ty; eauto with fiat2_hints.
          1: apply tenv_wf_step; auto; apply idx_ty_wf; auto.
          1: constructor; auto.
          eapply eq_filter_to_lookup_preserve_ty; eauto with fiat2_hints.
          1: apply tenv_wf_step; auto; apply idx_ty_wf; auto.
          1: constructor; auto; rewrite_map_get_put_goal; reflexivity.
          erewrite <- Properties.map.put_put_same;
            apply transf_to_idx_preserve_ty'; auto.
          1: apply tenv_wf_step; auto.
          apply to_filter_preserve_ty; auto with fiat2_hints. }
    Qed.

    Lemma to_filter_head_preserve_sem2 : forall {tenv : map.map string type} {tenv_ok : map.ok tenv}
                                                {locals : map.map string value} {locals_ok : map.ok locals}
                                                (Gstore : tenv) (store : locals),
        preserve_sem Gstore store to_filter_head.
    Proof.
      unfold preserve_sem; intros.
      rewrite to_filter_head_preserve_sem; [ | | | eauto | .. ]; auto.
    Qed.

    Lemma to_filter_preserve_sem' : forall {tenv : map.map string type} {tenv_ok : map.ok tenv}
                                           {locals : map.map string value} {locals_ok : map.ok locals}
                                           (Gstore : tenv) (store : locals),
        preserve_sem Gstore store (fold_expr to_filter_head).
    Proof.
      intros; apply fold_expr_preserve_sem; auto using to_filter_head_preserve_ty2.
      apply to_filter_head_preserve_sem2.
    Qed.

    Lemma to_filter_preserve_sem : forall {tenv : map.map string type} {tenv_ok : map.ok tenv}
                                          {locals : map.map string value} {locals_ok : map.ok locals}
                                          (Gstore Genv : tenv) (store env : locals) c,
        tenv_wf Gstore -> tenv_wf Genv ->
        well_typed Gstore Genv c ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_command store env (fold_command id to_filter_head c) = interp_command store env c.
    Proof.
      intros. erewrite <- fold_command_id_preserve_sem; [ | | | eauto | .. ];
        auto using to_filter_head_preserve_ty, to_filter_head_preserve_sem.
    Qed.

    Lemma ex_transf1_preserve_sem' : forall Gstore Genv tbl_ty free_vars e tbl c,
        tenv_wf Gstore -> tenv_wf Genv ->
        IndexInterface.is_tbl_ty tbl_ty = true -> type_wf tbl_ty ->
        incl (get_free_vars Genv) free_vars ->
        type_of Gstore Genv e tbl_ty ->
        well_typed (map.put Gstore tbl tbl_ty) Genv c ->
        can_transf_to_index tbl_ty
          (map.update (make_LikeList_aenv Gstore) tbl None)
          (fold_command id to_filter_head (CLetMut e tbl c)) = true ->
        forall (store env : clocals),
          locals_wf Gstore store ->
          locals_wf Genv env ->
          interp_command store env (transf_to_idx free_vars (to_filter_transf (CLetMut e tbl c))) = interp_command store env (CLetMut e tbl c).
    Proof.
      intros. unfold to_filter_transf. cbn [fold_command id].
      erewrite transf_to_idx_preserve_sem.
      4: apply to_filter_preserve_ty'. 7: eauto.
      all: auto using to_filter_head_preserve_ty2, to_filter_preserve_ty with fiat2_hints.
      eapply CLetMut_Proper.
      4: apply singleton_rel_refl.
      5,6: eauto.
      all: auto.
      1:{ unfold sem_eq; intros; intuition eauto.
          1: apply to_filter_preserve_ty'; auto with fiat2_hints.
          1: rewrite <- to_filter_preserve_sem'; [ | | | eauto | .. ]; auto. }
      1:{ unfold command_sem_eq; intros; intuition idtac.
          1: apply to_filter_preserve_ty; auto with fiat2_hints.
          1: eapply to_filter_preserve_sem; [ | | eauto | .. ]; auto with fiat2_hints. }
    Qed.

    Theorem ex_transf1_preserve_sem : forall Gstore Genv tbl_ty free_vars e tbl c,
        type_of Gstore Genv e tbl_ty ->
        tenv_wf Gstore -> tenv_wf Genv ->
        IndexInterface.is_tbl_ty tbl_ty = true -> type_wf tbl_ty ->
        incl (get_free_vars Genv) free_vars ->
        can_transf_to_index tbl_ty
          (map.update (make_LikeList_aenv Gstore) tbl None)
          (fold_command id to_filter_head (CLetMut e tbl c)) = true ->
        well_typed (map.put Gstore tbl tbl_ty) Genv c ->
        forall (store env : clocals),
          locals_wf Gstore store ->
          locals_wf Genv env ->
          interp_command store env (CLetMut e tbl c) = interp_command store env (ex_transf1 tbl free_vars (CLetMut e tbl c)).
    Proof.
      intros. lazymatch goal with H: IndexInterface.is_tbl_ty _ = _ |- _ => simpl in H end.
      unfold is_tbl_ty in *.
      repeat destruct_match_hyp; try congruence.
      unfold ex_transf1, delete_transf, lookup_transf, to_filter_transf.
      cbn [fold_command id] in *. unfold cdict_idx.
      unfold transf_to_idx.
      rewrite apply_after_letmut_compose.
      erewrite <- apply_after_letmut_preserve_sem.
      2-4: auto with fiat2_hints.
      6:{ apply to_idx_preserve_ty.
          5: apply to_filter_preserve_ty'.
          8: eauto. all: auto with fiat2_hints. }
      6:{ erewrite <- Properties.map.put_put_same.
          apply transf_to_idx'_index_wf; auto.
          1: apply tenv_wf_step; auto.
          apply to_filter_preserve_ty; auto with fiat2_hints. }
      6:{ intros. eapply to_idx_idx_wf.
          5: apply to_filter_preserve_ty'.
          8: eauto. all: auto with fiat2_hints. }
      6:{ intros. erewrite <- neq_filter_to_delete_preserve_sem,
          <- eq_filter_to_lookup_preserve_sem; auto.
          all: try eapply eq_filter_to_lookup_preserve_index_wf.
          all: try apply word_ok; try apply ctenv_ok; try apply clocals_ok.
          17,18: eauto. all: eauto.
          all: try apply H_NoDup.
          all: try (apply tenv_wf_step; auto; apply idx_ty_wf; auto).
          all: constructor; auto; rewrite_map_get_put_goal; auto. }
      all: auto.
      erewrite <- ex_transf1_preserve_sem'. 1: reflexivity.
      6: eauto. all: auto.
    Qed.

    Require Import fiat2.Notations.
    Open Scope fiat2_scope.

    Definition row_ty := TRecord (record_sort [("name", TString); ("department", TString); ("feedback", TString)]).
    (* two arbitrary well_typed rows *)
    Definition row1 := EVar "row1".
    Definition row2 := EVar "row2".

    Definition build_responses1 := <{ set "responses" := row1 :: row2 :: mut "responses" }>.
    Definition remove_NA := <{ set "responses" :=
            "row" <- mut "responses" ;
                               check(!("row"["department"] == << EAtom (AString "NA") >>)) ;
                               ret "row" }>.
    Definition filter_responses dpt : expr := ESort <[ "row" <- mut "responses" ;
                                                       check("row"["department"] == << EAtom (AString dpt) >>);
                                                       ret "row" ]>.
    Definition query := CSeq remove_NA
                          (CForeach (filter_responses "EECS") "r"
                           <{ let "name" = "r"["name"] +++ << EAtom (AString ": ") >> in
                              let "feedback" = "r"["feedback"] +++ << EAtom (AString "\n") >> in
                              let "line" = "name" +++ "feedback" in
                              set "all_feedback" := mut "all_feedback" +++ "line" }>).
    Definition ex1' := CSeq build_responses1 query.
    Definition ex1 := CLetMut (EAtom (ANil (Some (row_ty)))) "responses" ex1'.

    Definition init_Gstore : ctenv := map.put map.empty "all_feedback" TString.
    Definition init_Genv : ctenv := map.put (map.put map.empty "row1" row_ty) "row2" row_ty.

    Compute typecheck (map.put map.empty "all_feedback" TString) init_Genv ex1.
    Compute can_transf_to_index (TList row_ty) (map.put map.empty "all_feedback" LikeList) ex1.

    Definition ex1_to_filter := fold_command id to_filter_head ex1.
    Compute typecheck (map.put map.empty "all_feedback" TString) init_Genv ex1_to_filter.
    Compute can_transf_to_index (TList row_ty) (map.put map.empty "all_feedback" LikeList) ex1_to_filter.

    Ltac resolve_NoDup := repeat constructor; simpl; intuition idtac; congruence.

    Ltac resolve_tenv_wf := repeat apply tenv_wf_step; try apply tenv_wf_empty; repeat constructor; resolve_NoDup.

    Definition ex1_to_idx := transf_to_idx (get_free_vars init_Genv) ex1_to_filter.
    Compute ex1_to_idx.

    Definition ex1_lookup := apply_after_letmut (fold_command_with_globals ["responses"] (eq_filter_to_lookup_head attr "p" "responses")) ex1_to_idx.
    Compute ex1_lookup.

    Definition ex1_delete := apply_after_letmut (fold_command_with_globals ["responses"] (neq_filter_to_delete_head "responses" attr)) ex1_lookup.
    Compute ex1_delete.

    Hint Extern 5 (type_of _ _ _ _) => resolve_NoDup.
    Hint Immediate incl_refl.
    (* Hint Resolve command_typechecker_sound. *)
    Hint Extern 5 (well_typed _ _ _) => simple eapply command_typechecker_sound.
    Hint Extern 5 (tenv_wf _) => resolve_tenv_wf.
    Hint Extern 5 (type_wf _) => resolve_tenv_wf.
    Hint Extern 5 (_ = true) => resolve_tenv_wf.
    Hint Extern 5 (_ = Success _) => resolve_tenv_wf.


    Corollary ex1_delete_ty : well_typed init_Gstore init_Genv ex1_delete.
    Proof.
      eauto using ex_transf1_preserve_ty.
    Qed.

    Corollary ex1_delete_sem : forall (store env : clocals),
        locals_wf init_Gstore store ->
        locals_wf init_Genv env ->
        interp_command store env ex1 = interp_command store env ex1_delete.
    Proof.
      eapply ex_transf1_preserve_sem; eauto.
    Qed.
  End ConcreteExample.
End WithWord.
