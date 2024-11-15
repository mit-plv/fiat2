Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.Examples fiat2.TypeSystem fiat2.TypeSound.
Require Import List String ZArith Permutation.
Import ListNotations.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Import ResultMonadNotations.
Require Import Sorted.
Require Import coqutil.Map.SortedListString.
Require Import Ltac2.Ltac2 Ltac2.Control Ltac2.Constr.

Set Default Proof Mode "Classic".

Create HintDb fiat2_hints.

Local Ltac invert_type_wf :=
  lazymatch goal with
  | H: type_wf (TList ?t) |- type_wf ?t => inversion H; clear H; subst
  | H: type_wf (TOption ?t) |- type_wf ?t => inversion H; clear H; subst
  | H: type_wf (TDict ?t _) |- type_wf ?t => inversion H; clear H; subst
  | H: type_wf (TDict _ ?t) |- type_wf ?t => inversion H; clear H; subst
  | H: type_wf (TRecord ?tl) |- Forall type_wf (List.map snd ?tl) => inversion H; clear H; subst
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

Local Ltac destruct_match :=
  match goal with
  | H: context[match ?x with _ => _ end] |- _ =>
      let E := fresh "E" in
      destruct x eqn:E
  end.

Local Ltac destruct_match_goal :=
  let E := fresh "E" in
  lazymatch goal with
  | |- context[match ?x with _ => _ end] => destruct x eqn:E
  end.

Local Ltac iter_hyps tac :=
  let iter := ltac2:(tac |- List.iter (fun (h, _ , t) =>
                             ltac1:(h t tac|- tac h t)
                                     (Ltac1.of_constr (Unsafe.make (Unsafe.Var h)))
                                     (Ltac1.of_constr t)
                                     tac)
                              (hyps ())) in
  iter tac.

Local Ltac rewrite_hyp_l h t :=
  try lazymatch t with
    | _ = _ => rewrite <- h in *
    end.

Local Ltac invert_type_of :=
  lazymatch goal with
  | H: type_of _ _ (_ _) _ |- _ => inversion H; subst; clear H
  | H: type_of_binop _ _ _ _ |- _ => inversion H; subst; clear H
  end.

Local Ltac invert_unop_binop_atom_ty :=
  lazymatch goal with
  | H: type_of_unop _ _ _ |- _ => inversion H; subst
  | H: type_of_binop _ _ _ _ |- _ => inversion H; subst
  | H: type_of_atom _ _ |- _ => inversion H; subst
  end.

Local Ltac invert_Forall :=
  lazymatch goal with
  | H: Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  end.

Local Ltac invert_SSorted :=
  lazymatch goal with
  | H: StronglySorted _ (_ :: _) |- _ => inversion H; subst
  end.

Local Ltac invert_type_of_value :=
  lazymatch goal with
  | H: type_of_value ?v _ |- context[?v] => inversion H; subst; clear H
  end.

Local Ltac rewrite_map_get_put_hyp :=
  multimatch goal with
  | H: context[map.get (map.put _ ?x _) ?x] |- _ =>
      rewrite map.get_put_same in H
  | H: context[map.get (map.put _ _ _) _] |- _ =>
      rewrite map.get_put_diff in H; try now (simpl in *; intuition)
  end.

Local Ltac rewrite_map_get_put_goal :=
  multimatch goal with
  | |- context[map.get (map.put _ ?x _) ?x] =>
      rewrite map.get_put_same
  | |- context[map.get (map.put _ _ _) _] =>
      rewrite map.get_put_diff; try now (simpl in *; intuition)
  end.


Local Ltac clear_refl := lazymatch goal with H: ?x = ?x |- _ => clear H end.

Local Ltac do_injection' h t :=
  try lazymatch t with
    | ?x _ = ?x _ => injection h; intros; subst
    end.

Local Ltac do_injection := iter_hyps do_injection'.

Local Ltac destruct_subexpr :=
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

Local Ltac apply_Forall_In :=
  lazymatch goal with
  | H1: Forall _ ?l, H2: In _ ?l |- _ => eapply List.Forall_In in H1; eauto
  end.

Local Ltac rewrite_expr_value :=
  lazymatch goal with
  | E: VList _ = ?e |- context[?e] => rewrite <- E
  | E: VList _ = ?e, H: context[?e] |- _ => rewrite <- E in H
  | E: VDict _ = ?e |- context[?e] => rewrite <- E
  | E: VDict _ = ?e, H: context[?e] |- _ => rewrite <- E in H
  end.

Local Ltac apply_type_sound e :=
  lazymatch goal with
  | H: type_of _ _ e _ |- _ =>
      let H' := fresh "H'" in
      eapply type_sound in H as H'; eauto; try inversion H'; subst; auto
  end.

Local Ltac rewrite_interp_fold_expr :=
  lazymatch goal with
  | H: interp_expr _ _ (fold_expr _ ?e) = _ |- context[fold_expr _ ?e] =>
      rewrite H; clear H
  end.

Local Ltac get_update_same_diff x y :=
  let E := fresh "E" in
  destruct (String.eqb x y) eqn:E;
  [ rewrite eqb_eq in E; subst; repeat rewrite Properties.map.get_update_same
  | rewrite eqb_neq in E; repeat rewrite Properties.map.get_update_diff ]; auto.

Local Ltac get_put_same_diff x y :=
  let E := fresh "E" in
  destruct (String.eqb x y) eqn:E;
  [ rewrite eqb_eq in E; subst; repeat rewrite map.get_put_same
  | rewrite eqb_neq in E; repeat rewrite map.get_put_diff ]; auto.

Local Ltac invert_Forall2 := lazymatch goal with H: Forall2 _ _ _ |- _ => inversion H; subst; clear H end.

Local Ltac rewrite_l_to_r := lazymatch goal with H: ?x = _ |- context[?x] => rewrite H end.

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

Open Scope string_scope.

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

Lemma In_access_record : forall A l attr, In attr (List.map fst l) -> exists (x : A), access_record l attr = Success x.
Proof.
  induction l; simpl; intros.
  - intuition.
  - destruct a; simpl in *. destruct (eqb attr s) eqn:E.
    + exists a. reflexivity.
    + rewrite eqb_neq in *. intuition. congruence.
Qed.

Lemma access_record_type_wf : forall rt attr t,
    type_wf (TRecord rt) ->
    access_record rt attr = Success t ->
    type_wf t.
Proof.
  intros * H_ty H. apply access_record_sound in H. apply in_map with (f:=snd) in H; simpl in H.
  inversion H_ty; subst. apply_Forall_In.
Qed.


Lemma In_map_ext : forall A B (f g : A -> B) l, (forall x, In x l -> f x = g x) -> List.map f l = List.map g l.
Proof.
  intros * H. induction l; simpl; auto.
  f_equal; [ apply H | apply IHl ]; intuition.
Qed.

Lemma Permutation_filter : forall A (l l' : list A), Permutation l l' -> forall f, Permutation (filter f l) (filter f l').
Proof.
  induction l; intros.
  - apply Permutation_nil in H. subst. auto.
  - apply Permutation_sym in H as H'. apply Permutation_vs_cons_inv in H'.
    repeat lazymatch goal with H: exists _, _ |- _ => destruct H end.
    subst. rewrite filter_app. simpl; destruct (f a).
    1: apply Permutation_cons_app.
    all: rewrite <- filter_app.
    all: apply Permutation_cons_app_inv in H; auto.
Qed.

Lemma Permutation_flat_map : forall A B (f g : A -> list B),
  forall l l', (forall x, In x l -> Permutation (f x) (g x)) ->
               Permutation l l' ->
               Permutation (flat_map f l) (flat_map g l').
Proof.
  intros * H_fg. generalize dependent l'. induction l; simpl; intros l' H.
  - apply Permutation_nil in H; subst; auto.
  - apply Permutation_sym in H as H'. apply Permutation_vs_cons_inv in H'.
    repeat lazymatch goal with H: exists _, _ |- _ => destruct H end. subst.
    rewrite flat_map_app. simpl. pose proof H_fg a as H_a.
    assert (H_a_in: In a (a :: l)). { intuition. } apply H_a in H_a_in as H_p.
    destruct (f a) eqn:E.
    + simpl. apply Permutation_nil in H_p.
      rewrite H_p; simpl. rewrite <- flat_map_app.
      apply Permutation_cons_app_inv in H. intuition.
    + eapply perm_trans. 2: apply Permutation_app_swap_app.
      apply Permutation_app; auto. rewrite <- flat_map_app. apply IHl.
      2: apply Permutation_cons_app_inv in H.
      all: intuition.
Qed.

Lemma imp_pre_true : forall A B, A -> (A -> B) -> A /\ B.
Proof. intuition. Qed.

Section __.
  Context (tbl attr : string).

  (* is_inv stands for whether the context is invariant to Permutations of the current expr's output *)
  Definition unop_is_inv (is_inv : bool) (o : unop) : bool :=
    match o with
    | OLength => true
    | _ => false
    end.

  Definition binop_is_inv (is_inv : bool) (o : binop) : bool * bool :=
    match o with
    | OCons => (false, is_inv)
    | _ => (false, false)
    end.

  Fixpoint can_transf_to_idx'' (is_inv : bool) (e : expr) : bool :=
    match e with
    | EVar _ | EAtom _ => true
    | ELoc x => negb (String.eqb x tbl) || is_inv
    | EUnop o e => can_transf_to_idx'' (unop_is_inv is_inv o) e
    | EBinop o e1 e2 => let '(b1, b2) := binop_is_inv is_inv o in
                        can_transf_to_idx'' b1 e1 && can_transf_to_idx'' b2 e2
    | EIf e1 e2 e3 => can_transf_to_idx'' false e1 && can_transf_to_idx'' is_inv e2 && can_transf_to_idx'' is_inv e3
    | ELet e1 x e2 => can_transf_to_idx'' false e1 && can_transf_to_idx'' is_inv e2
    | EFlatmap e1 x e2 => can_transf_to_idx'' is_inv e1 && can_transf_to_idx'' is_inv e2
    | EFold e1 e2 x y e3 => can_transf_to_idx'' false e1 && can_transf_to_idx'' false e2 && can_transf_to_idx'' false e3
    | ERecord l => forallb (fun p => can_transf_to_idx'' false (snd p)) l
    | EAccess e s => can_transf_to_idx'' false e
    | EDict l => forallb (fun p => (can_transf_to_idx'' false (fst p) && can_transf_to_idx'' false (snd p))%bool) l
    | EInsert d k v => can_transf_to_idx'' false d && can_transf_to_idx'' false k && can_transf_to_idx'' false v
    | EDelete d k => can_transf_to_idx'' false d && can_transf_to_idx'' false k
    | ELookup d k => can_transf_to_idx'' false d && can_transf_to_idx'' false k
    | EOptMatch e e_none x e_some => can_transf_to_idx'' false e && can_transf_to_idx'' is_inv e_none && can_transf_to_idx'' is_inv e_some
    | EDictFold d e0 k v acc e => can_transf_to_idx'' false d && can_transf_to_idx'' false e0 && can_transf_to_idx'' false e
    | ESort l => can_transf_to_idx'' true l
    | EFilter l x p => can_transf_to_idx'' is_inv l && can_transf_to_idx'' false p
    | EJoin l1 l2 x1 x2 p r => can_transf_to_idx'' is_inv l1 && can_transf_to_idx'' is_inv l2 && can_transf_to_idx'' false p && can_transf_to_idx'' false r
    | EProj l x r => can_transf_to_idx'' is_inv l && can_transf_to_idx'' false r
    end.

  Fixpoint can_transf_to_idx' (c : command) : bool :=
    match c with
    | CSkip => true
    | CSeq c1 c2 => can_transf_to_idx' c1 && can_transf_to_idx' c2
    | CLet e x c => can_transf_to_idx'' false e && can_transf_to_idx' c
    | CLetMut e x c => negb (String.eqb x tbl) && can_transf_to_idx'' false e && can_transf_to_idx' c
    | CAssign x e => can_transf_to_idx'' false e
    | CIf e c1 c2 => can_transf_to_idx'' false e && can_transf_to_idx' c1 && can_transf_to_idx' c2
    | CForeach e x c => can_transf_to_idx'' false e && can_transf_to_idx' c
    end.

  Definition can_transf_to_idx (c : command) : bool :=
    match c with
    | CLetMut (EAtom (ANil (Some (TRecord rt)))) x c =>
        String.eqb x tbl &&
          inb String.eqb attr (List.map fst rt) &&
          can_transf_to_idx' c
    | _ => false
    end.
End __.

Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Local Notation value := (value (word := word)).

  (* ??? TODO: move *)
  Lemma value_eqb_refl : forall (v : value), value_eqb v v = true.
  Proof.
    unfold value_eqb. intros; rewrite value_compare_refl; reflexivity.
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

  Local Coercion is_true : bool >-> Sortclass.

  Lemma dict_insert_preserve_SSorted : forall d k v,
      StronglySorted (dict_entry_leb (word:=word)) d ->
      StronglySorted dict_entry_leb (dict_insert k v d).
  Proof.
    induction d; intros; simpl.
    - repeat constructor.
    - destruct a. inversion H; subst. unfold value_ltb, value_eqb.
      lazymatch goal with
      | |- context[value_compare ?a ?b] => destruct (value_compare a b) eqn:E
      end.
      + constructor; auto. rewrite Forall_forall in *.
        unfold dict_entry_leb in *; simpl in *. apply value_compare_Eq_eq in E; subst; auto.
      + constructor; auto. rewrite Forall_forall in *; intros. destruct x.
        unfold dict_entry_leb, value_leb, leb_from_compare in *; simpl in *.
        destruct H0.
        * inversion H0; subst; rewrite E; auto.
        * apply H3 in H0; simpl in H0. destruct (value_compare v0 v2) eqn:E'; intuition.
          1: { apply value_compare_Eq_eq in E'; subst; rewrite E; trivial. }
          erewrite value_compare_trans; eauto.
      + constructor; auto. rewrite Forall_forall; intros x H_in.
        apply dict_insert_incl in H_in.
        unfold dict_entry_leb, value_leb, leb_from_compare in *; simpl in *.
        inversion H_in; subst.
        * simpl. rewrite value_compare_antisym. rewrite E. auto.
        * eapply List.Forall_In in H3; eauto.
  Qed.

  Lemma dict_lookup_Lt : forall d k,
      StronglySorted dict_entry_leb d ->
      (forall p, In p d -> value_compare k (fst p) = Lt) ->
      dict_lookup (word:=word) k d = None.
  Proof.
    intros. induction d; auto.
    simpl. destruct a; simpl in *.
    destruct (value_eqb k v) eqn:E.
    - unfold value_eqb in *. pose proof (H0 (v, v0)).
      intuition; simpl in *. rewrite H1 in E; discriminate.
    - apply IHd; inversion H; auto.
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
    unfold has_index_entry_shape; intros * H H_SSorted.
    induction d; simpl; auto.
    destruct a; simpl. inversion H; subst; simpl in *.
    destruct v1; intuition.
    unfold value_eqb, value_ltb. destruct (value_compare k v0) eqn:E; cbn; auto.
    all: destruct (record_proj "0" l); intuition.
    all: inversion H_SSorted; subst.
    - rewrite dict_lookup_Lt; auto. intros p H_in. apply_Forall_In.
      unfold dict_entry_leb, value_leb, leb_from_compare in *; simpl in *.
      destruct (value_compare v0 (fst p)) eqn:E'; try congruence.
      + apply value_compare_Eq_eq in E'; subst; auto.
      + eapply value_compare_trans; eauto.
    - assert (H_Permu: forall A (l : list A) u v xl yl, Permutation xl (v :: yl) -> Permutation (l ++ u :: xl) (v :: l ++ u :: yl)).
      { clear. intros.
        replace (v :: l ++ u :: yl) with ((v :: nil) ++ l ++ u :: yl)%list; auto.
        eapply perm_skip with (x:=u), Permutation_sym, perm_trans in H.
        2: apply perm_swap.
        eapply perm_trans. 2: eapply Permutation_app_swap_app. simpl.
        auto using Permutation_app, Permutation_sym. }
      auto.
  Qed.

  Lemma Permutation_SSorted_eq : forall l l',
      Permutation l l' ->
      StronglySorted (value_leb (word:=word)) l ->
      StronglySorted value_leb l' ->
      l = l'.
  Proof.
    induction l; intros l' H H_sort H_sort'.
    - apply Permutation_nil in H; congruence.
    - destruct l'.
      1: apply Permutation_sym, Permutation_nil in H; discriminate.
      inversion H_sort; inversion H_sort'; subst.
      apply Permutation_in with (x:=a) in H as H_in; intuition.
      apply Permutation_sym in H as H'.
      apply Permutation_in with (x:=v) in H' as H_in'; intuition.
      inversion H_in; inversion H_in'; subst.
      1-3: f_equal; apply IHl; auto; eapply Permutation_cons_inv; eauto.
      eapply List.Forall_In in H3, H7; eauto.
      apply value_leb_antisym in H3; auto; subst. f_equal.
      apply IHl; auto. eapply Permutation_cons_inv; eauto.
  Qed.

  (* An index is a dictionary with each of its keys mapped to at least one row of the table *)
  Definition index_type (kt : type) (rt : list (string * type)) :=
    TDict kt (TRecord [("0", TList (TRecord rt)); ("1", TRecord rt)]).

  Section WithMap.
    Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    (* ??? TODO: move *)
    Local Ltac use_not_free_immut_put_ty_IH :=
      lazymatch goal with
      | H: context[type_of _ (map.put _ _ _) ?e _ <-> type_of _ _ ?e _],
        _: type_of _ (map.put ?Genv _ _) ?e _|- type_of _ ?Genv ?e _ => rewrite <- H
      | H: context[type_of _ (map.put _ _ _) ?e _ <-> type_of _ _ ?e _] |- type_of _ _ ?e _ => rewrite H
      end.

    Local Ltac swap_map_puts :=
      lazymatch goal with
      | IH: context[type_of _ (map.put _ ?x _) _ _ <-> _],
          H: context[map.put (map.put _ ?x _) ?y _] |- context[map.put _ ?y _] =>
          let E := fresh "E" in
          destruct (String.eqb x y) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst;
          [ rewrite Properties.map.put_put_same in *
          | rewrite Properties.map.put_put_diff with (k1:=x) in * ]; auto
      |  IH: context[type_of _ (map.put _ ?x _) _ _ <-> _],
          H: context[map.put _ ?y _] |- context[map.put (map.put _ ?x _) ?y _] =>
           let E := fresh "E" in
           destruct (String.eqb x y) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst;
           [ rewrite Properties.map.put_put_same in *
           | rewrite Properties.map.put_put_diff with (k1:=x) in * ]; auto
      end.

    Lemma not_free_immut_put_ty_iff: forall x e Gstore Genv t t',
        free_immut_in x e = false ->
        type_of Gstore (map.put Genv x t') e t <->
        type_of Gstore Genv e t.
    Proof.
      intros. generalize dependent Genv. revert t t'. induction e using expr_IH;
        intros; simpl in *; repeat rewrite Bool.orb_false_iff in *.
      all: try now ( split; intro H'; inversion H'; subst; econstructor; eauto; intuition;
                     repeat (try use_not_free_immut_put_ty_IH; eauto; swap_map_puts;
                  simpl in *; repeat rewrite Bool.orb_false_iff in *; intuition)).
      1:{ (* EVar *)
        split; intro H'; inversion H'; subst; constructor.
        all: rewrite eqb_neq, map.get_put_diff in *; auto. }
      1:{ (* ERecord *)
        split; intro H'; inversion H'; subst; econstructor; eauto.
        all: lazymatch goal with
             | H1: context[Permutation.Permutation], H2: context[Sorted.StronglySorted],
                   H3: context[NoDup], H4: type_of _ _ _ _ |- _ => clear H1 H2 H3 H4
             end.
        all: generalize dependent tl; induction l; simpl in *; intros;
          destruct tl; simpl in *; try congruence; auto; constructor; auto.
        1,3: invert_Forall2; invert_Forall; subst; use_not_free_immut_put_ty_IH;
        eauto; rewrite Bool.orb_false_iff in *; destruct a; intuition.
        all: apply IHl; invert_Forall2; invert_Forall; injection H2; rewrite Bool.orb_false_iff in *; intuition. }
      1:{ (* EDict *)
        split; intro H'; inversion H'; subst; econstructor; eauto.
        all: lazymatch goal with
             | H: type_of _ _ _ _ |- _ => clear H
             end.
        all: induction H4; simpl in *; auto; constructor.
        1,3: invert_Forall; destruct_match; simpl in *;
        repeat rewrite Bool.orb_false_iff in *; intuition; use_not_free_immut_put_ty_IH; eauto.
        all: invert_Forall; rewrite Bool.orb_false_iff in *; apply IHForall; intuition. }
    Qed.

    Definition gallina_list_to_idx attr (l : list value) :=
      fold_right
        (fun v acc => match v with
                      | VRecord v =>
                          dict_insert (record_proj attr v)
                            (match dict_lookup (record_proj attr v) acc with
                             | Some p => vcons_to_fst (VRecord v) p
                             | None => VRecord [("0", VList nil); ("1", VRecord v)]
                             end) acc
                      | _ => nil
                      end) nil l.

    Definition gallina_idx_to_list (d : list (value * value)) :=
      fold_right
        (fun v acc => match snd v with
                      | VRecord p => match record_proj "0" p with
                                     | VList l => (l ++ (record_proj "1" p :: acc))%list
                                     | _ => nil
                                     end
                      | _ => nil
                      end)
        nil d.

    Definition tenv_equiv_at (x attr : string) (rt : list (string * type)) (Gstore : tenv) :=
      map.put Gstore x (index_type (get_attr_type rt attr) rt).

    Definition locals_eq_except (x : string) (l l' : locals) :=
      forall y, x <> y -> map.get l y = map.get l' y.

    Definition locals_equiv_idx_list_at (x attr : string) (l l' : locals) :=
      match map.get l x with
      | Some (VDict v) =>
          match map.get l' x with
          | Some (VList v') => v = gallina_list_to_idx attr v'
          | _ => False
          end
      | _ => False
      end.

    Lemma locals_eq_update : forall (l l' : locals) x v,
        (forall y, x <> y -> map.get l y = map.get l' y) ->
        map.update l x v = map.update l' x v.
    Proof.
      intros * H. apply map.map_ext. intro y. destruct (String.eqb x y) eqn:E.
      - rewrite eqb_eq in E; subst. repeat rewrite Properties.map.get_update_same; trivial.
      - rewrite eqb_neq in E. repeat rewrite Properties.map.get_update_diff; auto.
    Qed.


    Lemma locals_eq_except_update : forall l l' tbl x v,
        locals_eq_except tbl l l' -> locals_eq_except tbl (map.update l x v) (map.update l' x v).
    Proof.
      intros. intros y H_neq. get_update_same_diff x y.
    Qed.

    Lemma locals_equiv_idx_list_at_update : forall l l' tbl attr x v,
        locals_equiv_idx_list_at tbl attr l l' -> x <> tbl ->
        locals_equiv_idx_list_at tbl attr (map.update l x v) (map.update l' x v).
    Proof.
      intros. unfold locals_equiv_idx_list_at in *. get_update_same_diff x tbl. intuition.
    Qed.

    Lemma locals_eq_except_put : forall l l' x y v,
        locals_eq_except x l l' -> locals_eq_except x (map.put l y v) (map.put l' y v).
    Proof.
      intros. intros z H_neq. get_put_same_diff y z.
    Qed.

    Lemma locals_equiv_idx_list_at_put : forall l l' attr x y v,
        locals_equiv_idx_list_at x attr l l' -> x <> y ->
        locals_equiv_idx_list_at x attr (map.put l y v) (map.put l' y v).
    Proof.
      unfold locals_equiv_idx_list_at; intros. get_put_same_diff y x. intuition.
    Qed.

    Lemma locals_eq_except_put0 : forall l l' x v v',
        locals_eq_except x l l' -> locals_eq_except x (map.put l x v) (map.put l' x v').
    Proof.
      unfold locals_eq_except; intros. repeat rewrite map.get_put_diff; auto.
    Qed.

    Lemma locals_equiv_idx_list_at_put0 :forall l l' x attr interp_e interp_e' v v',
        locals_equiv_idx_list_at x attr l l' ->
        interp_e = VDict v -> interp_e' = VList v' ->
        v = gallina_list_to_idx attr v' ->
        locals_equiv_idx_list_at x attr (map.put l x (interp_e)) (map.put l' x (interp_e')).
    Proof.
      unfold locals_equiv_idx_list_at; intros. repeat rewrite map.get_put_same. subst; auto.
    Qed.

    Lemma get_attr_type_ty_wf : forall rt attr,
        type_wf (TRecord rt) ->
        type_wf (get_attr_type rt attr).
    Proof.
      intros. unfold get_attr_type. destruct (access_record rt attr) eqn:E.
      - apply access_record_sound in E. inversion H. apply in_map with (f:=snd) in E; simpl in E.
        eapply List.Forall_In in H3; eauto.
      - constructor.
    Qed.

    Hint Resolve get_attr_type_ty_wf : fiat2_hints.
    Hint Resolve tenv_wf_step : fiat2_hints.
    Hint Resolve locals_wf_step : fiat2_hints.
    Hint Resolve locals_eq_except_put : fiat2_hints.
    Hint Resolve locals_equiv_idx_list_at_put : fiat2_hints.
    Hint Resolve locals_eq_except_put0 : fiat2_hints.
    Hint Resolve locals_equiv_idx_list_at_put0 : fiat2_hints.
    Hint Resolve type_sound : fiat2_hints.

    Lemma tenv_equiv_at_wf : forall tbl attr rt Gstore,
        tenv_wf Gstore -> map.get Gstore tbl = Some (TList (TRecord rt)) ->
        tenv_wf (tenv_equiv_at tbl attr rt Gstore).
    Proof.
      intros * H_Gstr H_tbl_ty. apply tenv_wf_step; auto. constructor.
      all: apply H_Gstr in H_tbl_ty; auto with fiat2_hints.
      repeat (constructor; simpl; intuition). congruence.
    Qed.

    Hint Resolve tenv_equiv_at_wf : fiat2_hints.

    Section list_idx.
      Context (tup acc x k v : string).

      (* Materialize tbl (expected to be a list of records) into an index over attr *)
      Definition list_to_idx (attr : string) (tbl : expr) : expr :=
        let k := EAccess (EVar tup) attr in
        EFold tbl (EDict nil) tup acc
          (EInsert (EVar acc) k
             (EOptMatch (ELookup (EVar acc) k)
                (epair enil (EVar tup))
                x (cons_to_fst (EVar tup) (EVar x)))).

      (* Inverse of tbl_to_idx, expecting idx to be a dict
   Require the index keys in idx to match the attr values in the records *)
      Definition idx_to_list (idx : expr) : expr :=
        EDictFold idx enil k v acc
          (EBinop OConcat (ofst (EVar v))
             (econs (osnd (EVar v)) (EVar acc))).

      Lemma fiat2_gallina_list_to_idx : forall (Gstore Genv : tenv) (store env : locals) tbl attr l rt,
          is_NoDup [tup; acc; x] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv tbl (TList (TRecord rt)) ->
          In attr (List.map fst rt) ->
          locals_wf Gstore store -> locals_wf Genv env ->
          interp_expr store env tbl = VList l ->
          interp_expr store env (list_to_idx attr tbl) = VDict (gallina_list_to_idx attr l).
      Proof.
        intros * vars_distinct H_Gstr H_Genv H_ty H_in H_str H_env H_tbl_v.
        simpl. rewrite H_tbl_v.
        eapply type_sound in H_ty; eauto. rewrite H_tbl_v in H_ty. inversion H_ty; subst.
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
                             end).
        3:{ intros a b H_a H_in_b. destruct a; intuition.
            all: unfold get_local; repeat rewrite_map_get_put_goal; auto.
            apply_Forall_In. invert_type_of_value. do 2 f_equal.
            lazymatch goal with
            | |- context[dict_lookup ?a ?b] => destruct (dict_lookup a b)
            end; simpl; auto. f_equal. repeat rewrite_map_get_put_goal; auto. }
        2: trivial.
        1:{ clear H_tbl_v H_ty. induction l; simpl; auto. invert_Forall; subst. rewrite IHl; auto. clear IHl.
            invert_type_of_value. do 2 f_equal. simpl.
            lazymatch goal with
            | |- context[dict_lookup ?a ?b] => destruct (dict_lookup a b)
            end; simpl; auto. f_equal. destruct v0; auto. }
      Qed.

      Lemma fiat2_gallina_idx_to_list : forall (Gstore Genv : tenv) (store env : locals) idx l kt rt,
          is_NoDup [acc; v] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv idx (index_type kt rt) ->
          locals_wf Gstore store -> locals_wf Genv env ->
          interp_expr store env idx = VDict l ->
          interp_expr store env (idx_to_list idx) = VList (gallina_idx_to_list l).
      Proof.
        intros * vars_distinct H_Gstr H_Genv H_ty H_str H_env H_idx_v.
        eapply type_sound in H_ty; eauto. rewrite H_idx_v in H_ty; inversion H_ty; subst.
        simpl. rewrite H_idx_v.
        erewrite In_fold_right_ext with
          (P := fun v => match v with VList _ => True | _ => False end).
        3:{ intros a b H_a H_in_b. unfold get_local.
            repeat rewrite_map_get_put_goal.
            apply_Forall_In. intuition. invert_type_of_value. destruct a; intuition.
            inversion H9; subst. destruct x0; intuition. unfold record_proj.
            simpl in *; subst. invert_type_of_value; auto. }
        2: trivial.
        1:{ clear H_idx_v H_ty H5 H6. induction l; simpl; auto. invert_Forall.
            rewrite IHl; auto. clear IHl. intuition. invert_type_of_value.
            invert_Forall2; subst. destruct x0; intuition; simpl in *. subst.
            invert_type_of_value; auto. }
      Qed.

      Lemma fiat2_gallina_list_to_idx_to_list : forall (Gstore Genv : tenv) (store env : locals) l attr tbl rt,
          is_NoDup [tup; acc; x; v] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv tbl (TList (TRecord rt)) ->
          In attr (List.map fst rt) ->
          locals_wf Gstore store -> locals_wf Genv env ->
          interp_expr store env tbl = VList l ->
          interp_expr store env (idx_to_list (list_to_idx attr tbl)) =
            VList (gallina_idx_to_list (gallina_list_to_idx attr l)).
      Proof.
        intros * vars_distinct H_Gstr H_Genv H_ty H_in H_str H_env H_tbl_v.
        apply In_access_record in H_in as Ht. destruct Ht as [t Ht].
        eapply fiat2_gallina_idx_to_list with (Gstore:=Gstore) (kt:=t); eauto.
        1: simpl in *; intuition.
        2:{ eapply fiat2_gallina_list_to_idx with (Gstore:=Gstore); eauto. simpl in *; intuition. }
        apply type_of__type_wf in H_ty as H_wf; auto. inversion H_wf; subst.
        repeat (try econstructor; try erewrite map.get_put_same; try erewrite map.get_put_diff; eauto).
        1: eapply access_record_type_wf; eauto.
        1, 5, 8: simpl; try rewrite <- eqb_eq; intuition.
        all: simpl in *; intuition.
      Qed.

      Lemma list_to_idx_preserve_ty : forall Gstore Genv tbl rt attr,
          is_NoDup [tup; acc; x] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          In attr (List.map fst rt) ->
          type_of Gstore Genv tbl (TList (TRecord rt)) ->
          type_of Gstore Genv (list_to_idx attr tbl) (TDict (get_attr_type rt attr) (TRecord [("0", (TList (TRecord rt))); ("1", TRecord rt)])).
      Proof.
        intros * vars_distinct H_Gstr H_Genv H_in H_ty.
        eapply type_of__type_wf in H_ty as H_wf; auto. inversion H_wf; subst.
        inversion H0; subst.
        repeat (econstructor; eauto; repeat rewrite_map_get_put_goal).
        all: try rewrite <- inb_false_iff; auto.
        all: unfold get_attr_type; apply In_access_record in H_in as [t Ht]; try rewrite Ht; auto.
        apply access_record_sound in Ht; apply in_map with (f:=snd) in Ht; apply_Forall_In.
      Qed.

      Lemma idx_to_list_preserve_ty : forall Gstore Genv idx kt t,
          is_NoDup [acc; v] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv idx (TDict kt (TRecord [("0", TList t); ("1", t)])) ->
          type_of Gstore Genv (idx_to_list idx) (TList t).
      Proof.
        intros * vars_distinct H_Gstr H_Genv H_ty. eapply type_of__type_wf in H_ty as H_wf; auto.
        inversion H_wf; subst. inversion H2; subst; simpl in *.
        repeat (econstructor; eauto; repeat rewrite_map_get_put_goal).
        all: try lazymatch goal with
               | |- type_wf _ => idtac; eapply List.Forall_In; eauto; intuition
               end.
      Qed.

      Lemma gallina_list_to_idx_shape : forall l attr rt,
          Forall (fun v => type_of_value v (TRecord rt)) l ->
          In attr (List.map fst rt) ->
          Forall has_index_entry_shape (gallina_list_to_idx attr l).
      Proof.
        intros * H_ty H_in. induction H_ty; simpl; auto.
        invert_type_of_value.
        specialize (dict_insert_incl (width:=width)) as H_ins.
        eapply incl_Forall; eauto.
        constructor; intuition. simpl. unfold has_index_entry_shape in *.
        lazymatch goal with
        | |- context[dict_lookup ?k ?d] => destruct (dict_lookup k d) eqn:E
        end; simpl; intuition.
        eapply Forall_dict_lookup in IHH_ty; simpl in IHH_ty; eauto.
        destruct v0; intuition. destruct (record_proj "0" l1); intuition.
      Qed.

      Lemma gallina_list_to_idx_SSorted : forall l attr rt,
          Forall (fun v => type_of_value v (TRecord rt)) l ->
          In attr (List.map fst rt) ->
          StronglySorted dict_entry_leb (gallina_list_to_idx attr l).
      Proof.
        intros; induction l; simpl; try constructor.
        inversion H; subst. inversion H3; subst.
        apply dict_insert_preserve_SSorted; auto.
      Qed.

      Lemma gallina_list_to_idx_Permutation : forall attr l rt,
          Forall (fun v => type_of_value v (TRecord rt)) l ->
          In attr (List.map fst rt) ->
          Permutation (concat_VList_V (List.map snd (gallina_list_to_idx attr l))) l.
      Proof.
        intros * H_ty H_in. induction H_ty; simpl; auto.
        invert_type_of_value. eapply perm_trans.
        1:{ eapply dict_insert_lookup_Permutation.
            - eapply gallina_list_to_idx_shape; eauto.
            - eapply gallina_list_to_idx_SSorted; eauto. }
        1: constructor; auto.
      Qed.

      Lemma gallina_idx_to_list__concat_VList_V : forall l,
          Forall has_index_entry_shape l ->
          gallina_idx_to_list l = concat_VList_V (List.map snd l).
      Proof.
        intros * H.
        induction l; simpl; auto.
        inversion H; subst.
        destruct (snd a); intuition. rewrite H0. reflexivity.
      Qed.

      Lemma gallina_list_to_idx_to_list_sound : forall attr l rt ,
          Forall (fun v => type_of_value v (TRecord rt)) l ->
          In attr (List.map fst rt) ->
          Permutation (gallina_idx_to_list (gallina_list_to_idx attr l)) l.
      Proof.
        intros * H_ty H_in.
        eapply perm_trans. 2: eapply gallina_list_to_idx_Permutation; eauto.
        rewrite gallina_idx_to_list__concat_VList_V. 1: apply Permutation_refl.
        eapply gallina_list_to_idx_shape; eauto.
      Qed.

      Lemma list_to_idx_to_list_sound :
        forall attr tbl (Gstore Genv : tenv) (store env : locals) rt,
          is_NoDup [tup; acc; x; v] ->
          type_of Gstore Genv tbl (TList (TRecord rt)) ->
          tenv_wf Gstore -> tenv_wf Genv ->
          locals_wf Gstore store -> locals_wf Genv env ->
          In attr (List.map fst rt) ->
          exists l l',
            interp_expr store env (idx_to_list (list_to_idx attr tbl)) = VList l /\
              interp_expr store env tbl = VList l' /\
              Permutation l l'.
      Proof.
        intros * vars_distinct H * H_Gstr H_Genv H_str H_env H_in.
        eapply type_sound in H as H'; eauto. inversion H'; subst. symmetry in H0.
        eapply fiat2_gallina_list_to_idx_to_list with (Gstore:=Gstore) (attr:=attr) in H0 as H0'; eauto.
        repeat eexists; eauto.
        eapply gallina_list_to_idx_to_list_sound; eauto.
      Qed.

      Lemma locals_equiv_locals_wf :
        is_NoDup [tup; acc; x] ->
        forall x rt attr Gstore' store' store,
          locals_wf Gstore' store' ->
          tenv_wf Gstore' ->
          locals_equiv_idx_list_at x attr store store' ->
          locals_eq_except x store store' ->
          map.get Gstore' x = Some (TList (TRecord rt)) ->
          In attr (List.map fst rt) ->
          locals_wf (tenv_equiv_at x attr rt Gstore') store.
      Proof.
        intro vars_distinct; intros * H_wf H_Gstr' H_equiv H_except H_x H_in. unfold tenv_equiv_at.
        unfold locals_wf; intros y t. get_put_same_diff x0 y.
        - intro H_t; injection H_t as H_t; subst.
          unfold locals_equiv_idx_list_at in H_equiv. repeat destruct_match; intuition.
          apply H_wf in H_x as H'. rewrite E1 in H'. subst.
          assert (interp_expr store' map.empty (ELoc y) = VList l0). { simpl; unfold get_local. rewrite E1; auto. }
          assert (interp_expr store' map.empty (list_to_idx attr (ELoc y)) = VDict (gallina_list_to_idx attr l0)).
          { eapply fiat2_gallina_list_to_idx with (Genv:=map.empty); eauto.
            1,3: unfold tenv_wf, locals_wf; intros * contra; rewrite map.get_empty in contra; discriminate.
            1: constructor; auto. }
          assert (type_of Gstore' map.empty (ELoc y) (TList (TRecord rt))). { constructor; auto. }
          eapply list_to_idx_preserve_ty in H1; eauto.
          1: eapply type_sound with (env:=map.empty) in H1; eauto.
          2-4: unfold tenv_wf, locals_wf; intros; repeat rewrite map.get_empty in *; discriminate.
          rewrite H0 in H1. auto.
        - intro H_y. apply H_wf in H_y. destruct_match; intuition. rewrite H_except; auto. rewrite E0; auto.
      Qed.

      Hint Resolve locals_equiv_locals_wf : fiat2_hints.

      Definition idx_read_to_list_read (tbl : string) (e : expr) :=
        match e with
        | ELoc tbl' => if String.eqb tbl tbl'
                       then idx_to_list (ELoc tbl)
                       else e
        | _ => e
        end.

      Definition list_write_to_idx_write (tbl attr : string) (c : command) :=
        match c with
        | CAssign tbl' e =>
            if String.eqb tbl tbl'
            then CAssign tbl (list_to_idx attr e)
            else c
        | _ => c
        end.

      Definition transf_to_idx' (tbl attr : string) (c : command) : command :=
        fold_command (list_write_to_idx_write tbl attr) (idx_read_to_list_read tbl) c.

      Definition transf_to_idx (tbl attr : string) (c : command) : command :=
        match c with
        | CLetMut (EAtom (ANil _)) tbl' c =>
            CLetMut (EDict nil) tbl (* Rely on can_transf_to_idx to check tbl' = tbl *)
              (transf_to_idx' tbl attr c)
        | _ => c
        end.

      Lemma transf_read_preserve_ty : forall Gstore Genv x attr rt e t,
          is_NoDup [acc; v] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          map.get Gstore x = Some (TList (TRecord rt)) -> type_of Gstore Genv e t ->
          type_of (tenv_equiv_at x attr rt Gstore) Genv (fold_expr (idx_read_to_list_read x) e) t.
      Proof.
        intros * vars_distinct H_Gstr H_Genv H_x H_ty. unfold tenv_equiv_at.
        generalize dependent Genv. generalize dependent t.
        induction e using expr_IH; simpl; intros.
        all: inversion H_ty; subst.
        all: try now (econstructor; eauto).
        - get_put_same_diff x0 x1.
          + rewrite H0 in H_x; injection H_x as H_x; subst.
            eapply idx_to_list_preserve_ty; eauto with fiat2_hints.
            constructor. rewrite_map_get_put_goal; f_equal.
            unfold index_type; eauto.
          + constructor. rewrite map.get_put_diff; congruence.
        - econstructor; eauto. apply IHe2; eauto with fiat2_hints.
        - econstructor; eauto. apply IHe2; auto. eauto with fiat2_hints.
        - econstructor; eauto. apply IHe3; auto. repeat apply tenv_wf_step; eauto with fiat2_hints.
        - econstructor; eauto.
          + rewrite fst_map_fst; auto.
          + clear H_ty H1 H3 H4 H5. generalize dependent tl. induction l; simpl; intros.
            1: inversion H2; constructor.
            destruct tl; simpl in *; inversion H2; subst. constructor; inversion H; subst.
            1: destruct a; simpl in *; apply H3; auto.
            apply IHl; auto; injection H1; intros; auto.
        - econstructor; eauto. clear H_ty. induction H3; intuition. constructor; inversion H; subst.
          1: destruct x1; simpl in *; split; apply H7; auto.
          1: apply IHForall; auto.
        - econstructor; eauto. apply IHe3; eauto with fiat2_hints.
        - econstructor; eauto. apply IHe3; auto. repeat apply tenv_wf_step; eauto with fiat2_hints.
        - constructor; auto. apply IHe2; eauto with fiat2_hints.
        - econstructor; eauto.
          1: apply IHe3; auto. 2: apply IHe4; eauto with fiat2_hints.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
        - econstructor; eauto. apply IHe2; eauto with fiat2_hints.
      Qed.

      Local Ltac apply_transf_read_preserve_ty e attr :=
        lazymatch goal with
        | H: type_of _ _ e _ |- _ =>
            let H_transf_ty := fresh "H_transf_ty" in
            eapply transf_read_preserve_ty with (attr:=attr) in H as H_transf_ty; eauto with fiat2_hints;
            apply_type_sound e; try now (simpl in *; intuition);
            eapply type_sound in H_transf_ty; eauto with fiat2_hints;
            inversion H_transf_ty; subst
        end.

      Local Ltac apply_transf_read_write_sound''_IH Gstore' :=
        lazymatch goal with
        | H: context[type_of _ _ ?e _ -> _],
            H_can: can_transf_to_idx'' _ false ?e = true,
              H_equiv: locals_equiv_idx_list_at _ _ _ _ |- _ =>
            let IH := fresh "IH" in
            let IHL := fresh "IHL" in
            let IH' := fresh "IH'" in
            eapply H with (Gstore':=Gstore') in H_equiv as IH; eauto; clear H;
            try (destruct IH as [IHL _]; apply IHL in H_can as IH')
        | H: context[type_of _ _ ?e _ -> _],
            H_can: can_transf_to_idx'' _ true ?e = true,
              H_equiv: locals_equiv_idx_list_at _ _ _ _ |- _ =>
            let IH := fresh "IH" in
            let IHR := fresh "IHR" in
            let IH' := fresh "IH'" in
            eapply H with (Gstore':=Gstore') in H_equiv as IH; eauto; clear H;
            try (destruct IH as [_ IHR]; apply IHR in H_can as IH')
        end.

      Lemma transf_read_write_sound'' : forall tbl attr rt e Gstore' Genv t store store' env,
          is_NoDup [tup; acc; x; v] ->
          type_of Gstore' Genv e t ->
          tenv_wf Gstore' -> tenv_wf Genv ->
          map.get Gstore' tbl = Some (TList (TRecord rt)) -> In attr (List.map fst rt) ->
          locals_wf Gstore' store' -> locals_wf Genv env ->
          locals_eq_except tbl store store' ->
          locals_equiv_idx_list_at tbl attr store store' ->
          (can_transf_to_idx'' tbl false e -> interp_expr store env (fold_expr (idx_read_to_list_read tbl) e) = interp_expr store' env e) /\
            (can_transf_to_idx'' tbl true e ->
             match t with
             | TList t =>
                 match interp_expr store env (fold_expr (idx_read_to_list_read tbl) e) with
                 | VList l => match interp_expr store' env e with
                              | VList l' => Permutation l l'
                              | _ => False
                              end
                 | _ => False
                 end
             | _ => interp_expr store env (fold_expr (idx_read_to_list_read tbl) e) = interp_expr store' env e
             end).
      Proof.
        induction e using expr_IH; cbn; intros * vars_distinct H_ty H_Gstr' H_Genv H_tbl_ty H_in H_str' H_env H_except H_equiv; auto.
        - (* EVar *)
          split; intros; auto. apply_type_sound (EVar x0).
        - (* ELoc *)
          split; intros.
          all: unfold is_true in *; rewrite Bool.orb_true_iff in H.
          + destruct (String.eqb x0 tbl) eqn:E; intuition; try discriminate.
            rewrite eqb_sym; rewrite E; try discriminate. apply eqb_neq in E. simpl.
            unfold get_local. rewrite H_except; auto.
          +  clear H; destruct (String.eqb x0 tbl) eqn:E; rewrite eqb_sym; rewrite E.
             * (* x0 = tbl *) rewrite eqb_eq in E; subst.
               inversion H_ty; subst. rewrite H0 in H_tbl_ty. injection H_tbl_ty; intros; subst.
               apply_type_sound (ELoc tbl).
               erewrite fiat2_gallina_idx_to_list with (Gstore:=tenv_equiv_at tbl attr rt Gstore'); simpl; eauto with fiat2_hints.
               1: eapply gallina_list_to_idx_to_list_sound; eauto.
               1: intuition.
               1:{ constructor. unfold tenv_equiv_at. rewrite map.get_put_same. eauto. }
               1:{ unfold get_local. eapply locals_equiv_locals_wf; eauto. simpl in *; intuition. }
               1:{ unfold locals_equiv_idx_list_at in H_equiv; repeat destruct_match; intuition.
                   subst. unfold get_local in *. rewrite E1 in H. rewrite E. injection H; congruence. }
             * (* x <> tbl *) rewrite eqb_neq in E. destruct t; simpl.
               all: unfold get_local; rewrite H_except; auto.
               apply_type_sound (ELoc x0). unfold get_local in *.
               rewrite_expr_value. intuition.
        - (* EAtom *)
          split; intro H_can; destruct t; auto. inversion H_ty; subst. invert_unop_binop_atom_ty.
          all: simpl; intuition.
        - (* EUnop *)
          inversion H_ty; subst. split; intro H_can; destruct o; simpl in *.
          all: invert_unop_binop_atom_ty; unfold is_true in H_can.
          all: apply_transf_read_write_sound''_IH Gstore'; try rewrite IH'; auto.
          (* OLength *)
          all: apply_transf_read_preserve_ty e attr.
          all: [> iter_hyps rewrite_hyp_l ..].
          all: destruct_match; intuition; erewrite Permutation_length; eauto.
        - (* EBinop *)
          inversion H_ty; subst. split; intro H_can; destruct o; simpl in *.
          all: invert_unop_binop_atom_ty; unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can.
          all: try (intuition; repeat apply_transf_read_write_sound''_IH Gstore'; try congruence; intuition;
                    repeat rewrite_interp_fold_expr; try congruence; intuition).
          1,2,4,5: (* OConcat, ORepeat, ORange, OWRange *)
            apply_type_sound e1; apply_type_sound e2; auto.
          (* OCons *)
          eapply locals_equiv_locals_wf in H_equiv as H_wf; eauto. 2: simpl; intuition.
          apply_transf_read_preserve_ty e2 attr. destruct_match; intuition.
          apply perm_skip. repeat rewrite_expr_value; auto.
        - (* EIf *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: repeat apply_transf_read_write_sound''_IH Gstore'; simpl; intuition;
            repeat rewrite_interp_fold_expr; auto.
          apply_type_sound e1. destruct b; auto.
        - (* ELet *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: repeat apply_transf_read_write_sound''_IH Gstore'; simpl; intuition;
            repeat rewrite_interp_fold_expr; eauto with fiat2_hints.
        - (* EFlatmap *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: revert IHe2; apply_transf_read_write_sound''_IH Gstore'; simpl; intuition; intros.
          + rewrite_interp_fold_expr; auto. apply_type_sound e1. f_equal.
            apply In_flat_map_ext. intros a H_a_in. apply_transf_read_write_sound''_IH Gstore'; try rewrite_interp_fold_expr; eauto with fiat2_hints.
            1: intuition.
            apply locals_wf_step; auto; apply_Forall_In.
          + eapply locals_equiv_locals_wf in H_equiv as H_wf; eauto.
            2: simpl; intuition.
            apply_transf_read_preserve_ty e1 attr; repeat rewrite_expr_value.
            destruct_match; auto. apply Permutation_flat_map; auto.
            intros v0 H_v_in. eapply Permutation_in in H_v_in; eauto. apply_Forall_In.
            apply_transf_read_write_sound''_IH Gstore'; eauto with fiat2_hints; intuition.
            apply_transf_read_preserve_ty e2 attr; eauto with fiat2_hints.
            iter_hyps rewrite_hyp_l; auto. destruct_match; intuition.
        - (* EFold *)
          inversion H_ty; subst.
          apply imp_pre_true.
          1: intro H_can.
          2: intros HA H_can; specialize (HA H_can).
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: revert IHe3; repeat apply_transf_read_write_sound''_IH Gstore'; intros; simpl; intuition.
          + repeat rewrite_interp_fold_expr. apply_type_sound e1.
            eapply type_sound in H6 as H2'; eauto.
            eapply In_fold_right_ext with (P:=fun a => type_of_value a t); auto.
            intros * P H_b_in. intuition.
            1:{ apply_transf_read_write_sound''_IH Gstore'; eauto; simpl; intuition.
                1: repeat apply tenv_wf_step; eauto with fiat2_hints.
                1: repeat apply locals_wf_step; eauto with fiat2_hints; apply_Forall_In. }
            1:{ apply_transf_read_write_sound''_IH Gstore'; auto; simpl; intuition.
                1: rewrite_interp_fold_expr; eapply type_sound; eauto.
                1,3: repeat apply tenv_wf_step; eauto with fiat2_hints.
                1,2: repeat apply locals_wf_step; eauto with fiat2_hints; apply_Forall_In. }
          + rewrite HA. destruct t; auto.
            apply_type_sound (EFold e1 e2 x0 y e3).
        - (* ERecord *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: do 2 f_equal; rewrite map_map.
          all: apply In_map_ext; intros x0 H_x_in; apply_Forall_In;
            rewrite forallb_forall in H_can; apply H_can in H_x_in as H_x.
          all: apply in_map with (f:=snd) in H_x_in; pose proof (Forall2_In_Permuted _ _ _ _ _ _ H2 H_x_in).
          all: do 3 lazymatch goal with H: exists _, _ |- _ => destruct H end; intuition.
          all: eapply H with (Gstore':=Gstore') in H_equiv as IH; eauto; simpl; intuition.
          all: destruct x0; simpl in *; congruence.
        - (* EAccess *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: apply_transf_read_write_sound''_IH Gstore'; simpl; intuition; rewrite_interp_fold_expr; auto.
          destruct t; auto. apply_type_sound (EAccess e s).
        - (* EDict *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can.
          all: do 3 f_equal; rewrite map_map; apply In_map_ext.
          all: intros x0 H_x_in; destruct x0; simpl in *.
          all: repeat apply_Forall_In; rewrite forallb_forall in H_can; apply H_can in H_x_in as H_x.
          all: repeat rewrite Bool.andb_true_iff in *; intuition; simpl in *.
          all: repeat apply_transf_read_write_sound''_IH Gstore'; simpl; intuition.
          all: rewrite IH', IH'0; auto.
        - (* EInsert *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: repeat apply_transf_read_write_sound''_IH Gstore'; repeat rewrite_interp_fold_expr; auto.
          all: simpl; intuition.
        - (* EDelete *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: repeat apply_transf_read_write_sound''_IH Gstore'; repeat rewrite_interp_fold_expr; auto.
          all: simpl; intuition.
        - (* ELookup *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: repeat apply_transf_read_write_sound''_IH Gstore'; repeat rewrite_interp_fold_expr; auto.
          all: simpl; intuition.
        - (* EOptMatch *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: revert IHe2 IHe3; apply_transf_read_write_sound''_IH Gstore'; simpl; intuition; intros.
          all: rewrite_interp_fold_expr; apply_type_sound e1.
          all: try now (revert IHe3; apply_transf_read_write_sound''_IH Gstore'; eauto; intuition).
          all: revert IHe2; apply_transf_read_write_sound''_IH Gstore'; eauto with fiat2_hints; intuition.
        - (* EDictFold *)
          inversion H_ty; subst. apply imp_pre_true.
          1: intro H_can.
          2: intros HA H_can; specialize (HA H_can).
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: revert IHe3; repeat apply_transf_read_write_sound''_IH Gstore'; simpl; intuition; intros.
          + repeat rewrite_interp_fold_expr; apply_type_sound e1.
            apply In_fold_right_ext with (P := fun a => type_of_value a t).
            2:{ intros. apply_transf_read_write_sound''_IH Gstore'; intuition.
                1: rewrite_interp_fold_expr; auto.
                2: repeat apply tenv_wf_step; eauto with fiat2_hints.
                2: repeat apply locals_wf_step; auto; apply_Forall_In; intuition.
                eapply type_sound with (Gstore:=tenv_equiv_at tbl attr rt Gstore').
                1: apply transf_read_preserve_ty; simpl; intuition. 2: eauto.
                2: apply tenv_equiv_at_wf; auto. 3: eapply locals_equiv_locals_wf; eauto; simpl; intuition.
                1-2: repeat apply tenv_wf_step; eauto with fiat2_hints.
                1: repeat apply locals_wf_step; apply_Forall_In; intuition. }
            apply_type_sound e2; eauto.
          + rewrite HA. destruct t; auto.
            apply_type_sound (EDictFold e1 e2 k0 v0 acc0 e3).
        - (* ESort *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: apply_transf_read_write_sound''_IH Gstore'; simpl; intuition.
          1:{ repeat destruct_match; intuition. f_equal. apply Permutation_SSorted_eq; auto using StronglySorted_value_sort.
              pose proof Permuted_value_sort l. pose proof Permuted_value_sort l0.
              eapply perm_trans. 2: eauto. apply Permutation_sym. eapply perm_trans. 2: eauto. apply Permutation_sym; auto. }
          1:{ eapply locals_equiv_locals_wf in H_equiv as H_wf; eauto; simpl; intuition.
              apply_transf_read_preserve_ty e attr. repeat rewrite_expr_value.
              pose proof Permuted_value_sort l. destruct_match; intuition. pose proof Permuted_value_sort l0.
              eapply perm_trans. 2: eauto. apply Permutation_sym. eapply perm_trans. 2: eauto. apply Permutation_sym; auto. }
        - (* EFilter *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: revert IHe2; apply_transf_read_write_sound''_IH Gstore'; simpl; intuition; intros.
          + rewrite_interp_fold_expr. apply_type_sound e1. f_equal.
            apply filter_ext_in; intros a H_a_in. apply_transf_read_write_sound''_IH Gstore'; eauto with fiat2_hints; intuition.
            1: rewrite_interp_fold_expr; auto.
            1: apply locals_wf_step; auto; apply_Forall_In.
          + eapply locals_equiv_locals_wf in H_equiv as H_wf; eauto; simpl; intuition.
            apply_transf_read_preserve_ty e1 attr. repeat destruct_match; intuition. repeat rewrite_expr_value.
            rewrite In_filter_ext with
              (g:=fun v : value => match interp_expr store' (map.put env x0 v) e2 with
                                   | VBool b => b
                                   | _ => false
                                   end).
            2:{ intros a H_a_in. apply_transf_read_write_sound''_IH Gstore'; eauto with fiat2_hints; intuition.
                1: rewrite_interp_fold_expr; auto.
                1:{ apply locals_wf_step; auto. do_injection. eapply Permutation_in in H_a_in; eauto. apply_Forall_In. }}
            apply Permutation_filter; congruence.
        - (* EJoin *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: revert IHe3 IHe4; repeat apply_transf_read_write_sound''_IH Gstore'; simpl; intuition; intros.
          + repeat rewrite_interp_fold_expr.
            apply_type_sound e1. apply_type_sound e2. f_equal.
            apply In_flat_map_ext; intros a H_a_in.
            rewrite In_filter_ext with
              (g:=fun v2 : value => match interp_expr store' (map.put (map.put env x0 a) y v2) e3 with
                                    | VBool b => b
                                    | _ => false
                                    end).
            1: apply In_map_ext; intros b H_b_in; revert IHe3; repeat apply_transf_read_write_sound''_IH Gstore'; auto; intuition.
            1: repeat apply tenv_wf_step; eauto with fiat2_hints.
            1: repeat apply locals_wf_step; eauto with fiat2_hints.
            1,2: rewrite filter_In in H_b_in; intuition; repeat apply_Forall_In.
            intros c H_c_in. revert IHe4; apply_transf_read_write_sound''_IH Gstore'; simpl; intuition; intros.
            1: rewrite_interp_fold_expr; auto.
            1: repeat apply tenv_wf_step; eauto with fiat2_hints.
            1: repeat apply locals_wf_step; repeat apply_Forall_In.
          + eapply locals_equiv_locals_wf in H_equiv as H_wf; eauto; simpl; intuition.
            apply_transf_read_preserve_ty e1 attr.
            apply_transf_read_preserve_ty e2 attr. repeat destruct_match; intuition. repeat rewrite_expr_value.
            repeat (try clear_refl; repeat do_injection). auto. apply Permutation_flat_map; auto.
            intros a H_a_in.
            rewrite In_map_ext with (g:=fun v2 : value => interp_expr store' (map.put (map.put env x0 a) y v2) e4).
            1: apply Permutation_map.
            1: rewrite In_filter_ext with
              (g:=fun v2 : value => match interp_expr store' (map.put (map.put env x0 a) y v2) e3 with
                                    | VBool b => b
                                    | _ => false
                                    end).
            1:{ apply Permutation_filter; auto. }
            1:{ intros b H_b_in. revert IHe4; apply_transf_read_write_sound''_IH Gstore'; simpl; intuition; intros.
                1: rewrite_interp_fold_expr; auto.
                1: repeat apply tenv_wf_step; eauto with fiat2_hints.
                1: repeat apply locals_wf_step; auto;
                eapply Permutation_in in H_a_in, H_b_in; eauto; repeat apply_Forall_In. }
            1:{ intros b H_b_in. revert IHe3; apply_transf_read_write_sound''_IH Gstore'; simpl; intuition; intros.
                1: rewrite_interp_fold_expr; auto.
                1: repeat apply tenv_wf_step; eauto with fiat2_hints.
                1: repeat apply locals_wf_step; auto.
                1,2: apply filter_In in H_b_in; intuition.
                1: eapply Permutation_in in H_a_in; eauto; apply_Forall_In.
                1: eapply Permutation_in in H20; eauto; apply_Forall_In. }
        - (* EProj *)
          inversion H_ty; subst. split; intro H_can.
          all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
          all: revert IHe2; apply_transf_read_write_sound''_IH Gstore'; simpl; intuition; intros.
          + rewrite_interp_fold_expr. apply_type_sound e1. f_equal. apply In_map_ext.
            intros a H_a_in. apply_transf_read_write_sound''_IH Gstore'; eauto with fiat2_hints; simpl; intuition.
            repeat apply locals_wf_step; apply_Forall_In.
          + eapply locals_equiv_locals_wf in H_equiv as H_wf; eauto; simpl; intuition.
            apply_transf_read_preserve_ty e1 attr. repeat destruct_match; intuition. do_injection.
            rewrite In_map_ext with (g:=(fun v : value => interp_expr store' (map.put env x0 v) e2)).
            2:{ intros a H_a_in. apply_transf_read_write_sound''_IH Gstore'; eauto with fiat2_hints; simpl; intuition.
                repeat apply locals_wf_step; auto. eapply Permutation_in in H_a_in; eauto. apply_Forall_In. }
            repeat rewrite_expr_value. apply Permutation_map; auto.
      Qed.

      Lemma transf_read_write_sound' : forall c Gstore' Genv rt store store' env tbl attr,
          is_NoDup [tup; acc; x; v] ->
          well_typed Gstore' Genv c ->
          map.get Gstore' tbl = Some (TList (TRecord rt)) ->
          In attr (List.map fst rt) ->
          tenv_wf Gstore' -> tenv_wf Genv -> locals_wf Gstore' store' -> locals_wf Genv env ->
          locals_eq_except tbl store store' ->
          locals_equiv_idx_list_at tbl attr store store' ->
          can_transf_to_idx' tbl c = true ->
          (locals_eq_except tbl
             (interp_command store env (transf_to_idx' tbl attr c))
             (interp_command store' env c)) /\
            (locals_equiv_idx_list_at tbl attr
               (interp_command store env (transf_to_idx' tbl attr c))
               (interp_command store' env c)).
      Proof.
        induction c; simpl; auto; intros * vars_distinct H_ty H_tbl_ty H_in H_Gstr' H_Genv H_str' H_env H_except H_equiv H_can.
        all: repeat rewrite Bool.andb_true_iff in H_can; inversion H_ty; subst.
        - eapply IHc2; try eapply IHc1; eauto; intuition.
          eapply command_type_sound; eauto.
        - destruct H_can.
          eapply transf_read_write_sound'' with (Gstore':=Gstore') in H as H'; eauto. rewrite H'.
          eapply IHc; eauto; [ apply tenv_wf_step | apply locals_wf_step ]; eauto with fiat2_hints.
        - rewrite Bool.negb_true_iff, eqb_neq in *.
          assert (E: map.get store x0 = map.get store' x0). { apply H_except; intuition. } rewrite E.
          repeat lazymatch goal with H: _ /\ _ |- _ => destruct H end.
          eapply transf_read_write_sound'' with (Gstore':=Gstore') in H2 as H'; eauto.
          2: simpl; intuition.
          rewrite H'. split.
          1: apply locals_eq_except_update. 2: apply locals_equiv_idx_list_at_update. 3: congruence.
          1,2: eapply IHc; eauto with fiat2_hints. all: simpl; intuition; rewrite map.get_put_diff; auto.
        - cbn. eapply transf_read_write_sound'' with (Gstore':=Gstore') in H_can; eauto.
          destruct (String.eqb tbl x0) eqn:E.
          + unfold fold_command. unfold interp_command.
            rewrite eqb_eq in *; subst. rewrite H_tbl_ty in H1. injection H1; intros; subst.
            apply_type_sound e.
            split; eauto with fiat2_hints. eapply locals_equiv_idx_list_at_put0; eauto.
            remember (map.put Gstore' x0 (index_type (get_attr_type rt attr) rt)) as Gstore.
            eapply fiat2_gallina_list_to_idx with (Gstore:=Gstore); eauto; simpl; intuition.
            1:{ subst. apply tenv_wf_step; auto. apply type_of__type_wf in H2; auto. inversion H2; subst. inversion H15; subst. repeat constructor; simpl; eauto with fiat2_hints. intuition; congruence. }
            1: subst; apply transf_read_preserve_ty; auto; simpl; intuition.
            1: subst; eapply locals_equiv_locals_wf; eauto; simpl; intuition.
            1: rewrite H_can; auto.
          + simpl. rewrite H_can.
            rewrite eqb_neq in *. split; auto with fiat2_hints.
        - repeat lazymatch goal with H: _ /\ _ |- _ => destruct H end.
          eapply transf_read_write_sound'' with (Gstore':=Gstore') in H; eauto.
          2: simpl; intuition. rewrite H.
          apply_type_sound e. destruct b; [ eapply IHc1 | eapply IHc2 ]; eauto; simpl; intuition.
        - repeat lazymatch goal with H: _ /\ _ |- _ => destruct H end.
          eapply transf_read_write_sound'' with (Gstore':=Gstore') in H; eauto.
          2: simpl; intuition. rewrite H.
          apply_type_sound e.
          destruct (interp_expr store' env e) eqn:E; try now (exfalso; auto).
          clear E H H8. generalize dependent store; generalize dependent store'. induction l; simpl; auto. intros.
          lazymatch goal with H: Forall _ (_ :: _) |- _ => inversion H; subst end. apply IHl; auto.
          1: eapply command_type_sound; eauto.
          3,4: eapply IHc.
          all: eauto with fiat2_hints; simpl; intuition.
      Qed.

      Lemma transf_read_write_sound : forall (Gstore Genv : tenv) (store env : locals) tbl attr c,
          is_NoDup [tup; acc; x; v] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          well_typed Gstore Genv c ->
          locals_wf Gstore store -> locals_wf Genv env ->
          can_transf_to_idx tbl attr c = true ->
          interp_command store env (transf_to_idx tbl attr c) = interp_command store env c.
      Proof.
        intros * vars_distinct H_Gstr H_Genv H_ty H_str H_env H.
        destruct c; simpl in *; try discriminate.
      repeat (destruct_match; try discriminate).
      repeat rewrite Bool.andb_true_iff in H.
      do 2 destruct H. apply eqb_eq in H; subst; simpl. apply locals_eq_update. intros.
      inversion H_ty; subst. inversion H4; subst. inversion H3; subst.
      eapply transf_read_write_sound'; cbn; eauto with fiat2_hints; intuition.
      - rewrite map.get_put_same; eauto.
      - rewrite inb_true_iff in *; auto.
      - apply locals_wf_step; auto. repeat constructor.
      - unfold locals_eq_except; intros. repeat rewrite map.get_put_diff; congruence.
      - unfold locals_equiv_idx_list_at. repeat rewrite map.get_put_same; trivial.
    Qed.

    Lemma fold_idx_to_list : forall idx,
        EDictFold idx enil k v acc
          (EBinop OConcat (ofst (EVar v))
             (econs (osnd (EVar v)) (EVar acc))) = idx_to_list idx.
    Proof. reflexivity. Qed.
    End list_idx.

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

    Lemma Forall_false__filter : forall A f (l : list A), Forall (fun x => f x = false) l -> filter f l = nil.
    Proof.
      intros * H; induction l; simpl; auto. simpl in H.
      inversion H; subst. rewrite H2. auto.
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

    Local Ltac apply_type_of__type_wf :=
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

    Local Ltac apply_fold_expr_preserve_ty_IH :=
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
              H3: List.map fst _ = _ |- _ => clear H1 H2 H3 end.
          generalize dependent tl. induction l; auto. intros.
          destruct tl; invert_Forall2; try discriminate. simpl in *.
          constructor.
          2: apply IHl; invert_Forall; intuition.
          invert_Forall. destruct a; simpl in *. apply H5; auto. }
      1:{ induction l; simpl; auto. repeat invert_Forall. constructor.
          2: apply IHl; intuition.
          destruct a; simpl in *. intuition. }
    Qed.

    Local Ltac apply_fold_expr_preserve_sem_IH :=
      multimatch goal with
      | IH: context[interp_expr _ _ (fold_expr _ ?e)],
        _: type_of _ ?G ?e _ |- context[interp_expr _ _ (fold_expr _ ?e)] =>
          erewrite <- IH with (Genv:=G); eauto
      end.

    Local Ltac trans_eq :=
      lazymatch goal with
        H: interp_expr _ _ ?e = _, H': _ = interp_expr _ _ ?e |- _ =>
          rewrite H in H'; injection H'; intros; subst end.

    Local Ltac type_of_list_entry :=
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
          simpl; apply_fold_expr_preserve_sem_IH. destruct_match_goal; auto.
          f_equal. apply In_flat_map_ext; intros.
          apply_fold_expr_preserve_sem_IH; eauto with fiat2_hints.
          apply locals_wf_step; auto. type_of_list_entry. }
      1:{ erewrite <- H_sem; eauto.
          2: econstructor; eauto; apply fold_expr_preserve_ty; eauto;
          repeat apply tenv_wf_step; eauto with fiat2_hints.
          simpl; apply_fold_expr_preserve_sem_IH. destruct_match_goal; auto.
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
              destruct_match_goal; simpl in *.
              apply fold_expr_preserve_ty; auto. }
          simpl. do 2 f_equal.
          lazymatch goal with
                 | H1: Permutation _ _, H2: NoDup _, H3: List.map fst _ = _ |- _ =>
                     clear H1 H2 H3
          end. generalize dependent tl; induction l; simpl; auto; intros.
          destruct tl; invert_Forall2.
          invert_Forall; destruct_match_goal; simpl in *.
          f_equal. 2: eapply IHl; eauto.
          f_equal; eauto. }
      1:{ erewrite <- H_sem; eauto.
          2:{ econstructor.
              3:{ induction l; simpl; auto.
                  repeat invert_Forall.
                  destruct_match_goal; constructor; simpl in *.
                  2: apply IHl; intuition.
                  intuition; apply fold_expr_preserve_ty; eauto. }
              all: auto. }
          simpl. do 3 f_equal. induction l; simpl; auto.
          repeat invert_Forall; destruct_match_goal; simpl in *.
          f_equal. 2: apply IHl; intuition.
          f_equal; intuition; apply_fold_expr_preserve_sem_IH. }
      1:{ erewrite <- H_sem; eauto.
          2: econstructor; eapply fold_expr_preserve_ty; eauto with fiat2_hints.
          simpl. apply_fold_expr_preserve_sem_IH. repeat destruct_match_goal; auto.
          all: apply_fold_expr_preserve_sem_IH; eauto with fiat2_hints.
          apply locals_wf_step; eauto. eapply type_sound in H10; eauto. inversion H10; subst.
          all: trans_eq; congruence. }
      1:{ erewrite <- H_sem; eauto.
          2: econstructor; eauto; apply fold_expr_preserve_ty; eauto;
          repeat apply tenv_wf_step; eauto with fiat2_hints.
          simpl; apply_fold_expr_preserve_sem_IH. destruct_match_goal; auto.
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
          simpl. apply_fold_expr_preserve_sem_IH. destruct_match_goal; auto.
          f_equal. apply In_filter_ext; intros.
          apply_fold_expr_preserve_sem_IH; eauto with fiat2_hints.
          apply locals_wf_step; auto. type_of_list_entry. }
      1:{ erewrite <- H_sem; eauto.
          2: econstructor; eauto; apply fold_expr_preserve_ty;
          repeat apply tenv_wf_step; eauto with fiat2_hints.
          simpl. repeat apply_fold_expr_preserve_sem_IH. repeat destruct_match_goal; auto.
          f_equal. apply In_flat_map_ext; intros. erewrite In_filter_ext.
          1: apply In_map_ext; intros.
          2: simpl; intros.
          all: apply_fold_expr_preserve_sem_IH;
              [ repeat apply tenv_wf_step | repeat apply locals_wf_step ]; eauto with fiat2_hints.
          all: try type_of_list_entry.
          all: lazymatch goal with H: In _ (filter _ _) |- _ => apply filter_In in H; intuition end.
          type_of_list_entry. }
      1:{ erewrite <- H_sem; eauto.
          2: econstructor; eauto; apply fold_expr_preserve_ty; eauto with fiat2_hints.
          simpl. apply_fold_expr_preserve_sem_IH. destruct_match_goal; auto.
          f_equal. apply In_map_ext; intros.
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

      Local Ltac apply_fold_command_with_globals_preserve_ty_IH :=
        lazymatch goal with
        | IH: context[fold_command_with_globals _ ?c] |- context[?c] =>
            apply IH
        end.

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
        1:{ destruct_match_goal; auto.
            apply_fold_command_with_globals_preserve_ty_IH; auto.
            1: apply tenv_wf_step; auto;
            eapply type_of__type_wf with (Gstore:=Gstore); eauto.
            apply tenv_wf_with_globals_step; auto.
            rewrite inb_false_iff in *. auto. }
      Qed.

      Definition holds_for_all_entries (P : string -> value -> Prop) (store : locals) :=
        forall k v, map.get store k = Some v -> P k v.

      Inductive parameterized_wf (Gstore Genv : tenv) (P : string -> value -> Prop) : command -> Prop :=
      | PWCSkip : parameterized_wf Gstore Genv P CSkip
      | PWCSeq c1 c2 : parameterized_wf Gstore Genv P c1 ->
                       parameterized_wf Gstore Genv P c2 ->
                       parameterized_wf Gstore Genv P (CSeq c1 c2)
      | PWCLet e t x c : type_of Gstore Genv e t ->
                         parameterized_wf Gstore (map.put Genv x t) P c ->
                         parameterized_wf Gstore Genv P (CLet e x c)
      | PWCLetMut e t x c :
        (forall store env, holds_for_all_entries P store ->
                           locals_wf Gstore store -> locals_wf Genv env ->
                           P x (interp_expr store env e)) ->
        type_of Gstore Genv e t ->
        parameterized_wf (map.put Gstore x t) Genv P c ->
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
                apply IHparameterized_wf in H7; eauto with fiat2_hints.
                unfold holds_for_all_entries; intros.
                get_put_same_diff x k0; rewrite_map_get_put_hyp.
                do_injection. apply H1; auto. } }
        1:{ unfold holds_for_all_entries; intros.
            get_put_same_diff x k; rewrite_map_get_put_hyp.
            do_injection. apply H1; auto. }
        1:{ apply_type_sound e. destruct_match_goal; auto. }
        1:{ apply_type_sound e. clear H' H6.
            generalize dependent store. induction l; simpl; auto; intros.
            invert_Forall; apply IHl; auto.
            2:{ apply IHparameterized_wf; eauto with fiat2_hints. }
            eapply command_type_sound.
            5: apply locals_wf_step. all: eauto with fiat2_hints.
            eapply parameterized_wf__well_typed; eauto. }
        Qed.

      Local Ltac apply_preserve_parameterized_wf_IH :=
        lazymatch goal with
          IH: context[fold_command_with_globals _ ?c] |- context[?c] =>
            apply IH
        end.

      Local Ltac invert_parameterized_wf :=
        lazymatch goal with H: parameterized_wf _ _ _ _ |- _ => inversion H; subst end.

      Lemma fold_command_with_globals_preserve_parameterized_wf : forall P f,
          (forall (Gstore : tenv), tenv_wf_with_globals Gstore ->
                                   preserve_ty Gstore f) ->
          (forall (Gstore : tenv) (store : locals),
              tenv_wf_with_globals Gstore ->
              holds_for_all_entries P store ->
              preserve_sem Gstore store f) ->
          forall c (Gstore Genv : tenv),
            tenv_wf Gstore -> tenv_wf Genv ->
            tenv_wf_with_globals Gstore ->
            parameterized_wf Gstore Genv P c ->
            parameterized_wf Gstore Genv P (fold_command_with_globals f c).
      Proof.
        induction c; simpl; auto; intros; invert_parameterized_wf.
        all: try (econstructor;
                  try (apply fold_expr_preserve_ty; eauto);
                  apply_preserve_parameterized_wf_IH; eauto with fiat2_hints).
        1:{ econstructor.
            1: intros; erewrite <- fold_expr_preserve_sem; eauto.
            1: apply fold_expr_preserve_ty; eauto.
            destruct_match_goal; auto. apply_preserve_parameterized_wf_IH; eauto with fiat2_hints.
            unfold tenv_wf_with_globals. rewrite inb_false_iff in *.
            apply not_In__tenv_wf_with_globals; auto. }
        1:{ econstructor; eauto.
            2: apply fold_expr_preserve_ty; eauto.
            intros. erewrite <- fold_expr_preserve_sem; eauto. }
      Qed.

      Context (global_attrs : list string) (global_attrs_ok : List.length globals = List.length global_attrs).

      Definition index_wf (attr : string) (l : list (value * value)) :=
        NoDup (List.map fst l) /\
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

      Lemma index_wf_step_inv : forall attr p idx,
          index_wf attr (p :: idx) -> index_wf attr idx.
      Proof.
        intros * H. destruct H as [HL HR]; inversion HL; inversion HR; subst.
        split; auto.
      Qed.

      Definition index_wf_with_globals x v :=
        Forall2 (fun tbl attr => x <> tbl \/
                                   match v with
                                   | VDict l => index_wf attr l
                                   | _ => False
                                   end) globals global_attrs.

      Lemma not_In__index_wf_with_globals : forall (store : locals) x v,
          ~ In x globals ->
          holds_for_all_entries index_wf_with_globals store ->
          holds_for_all_entries index_wf_with_globals (map.put store x v).
      Proof.
        clear global_types global_types_ok.
        unfold holds_for_all_entries, index_wf_with_globals.
        intros * H_not_In H * H'. get_put_same_diff x k; rewrite_map_get_put_hyp.
        revert global_attrs_ok. generalize dependent global_attrs. clear global_attrs.
        induction globals; destruct global_attrs.
        all: simpl in *; try congruence; intuition.
        constructor; intuition.
        apply H2; intros; auto. apply H in H3. invert_Forall2; auto.
      Qed.

      Local Ltac apply_fold_command_with_globals_preserve_sem_IH :=
        lazymatch goal with
          | IH: context[interp_command _ _ (fold_command_with_globals _ ?c)],
              H: parameterized_wf ?Gstore' ?Genv' _ ?c |-
              context[interp_command _ _ (fold_command_with_globals _ ?c)] =>
              erewrite <- IH with (Gstore:=Gstore') (Genv:=Genv'); eauto
        end.

      Lemma fold_command_with_globals_preserve_sem : forall f,
          (forall (Gstore : tenv), tenv_wf_with_globals Gstore ->
                                   preserve_ty Gstore f) ->
          (forall (Gstore : tenv) (store : locals),
              tenv_wf_with_globals Gstore ->
              holds_for_all_entries index_wf_with_globals store ->
              preserve_sem Gstore store f) ->
          forall c (Gstore Genv : tenv) (store env : locals),
            tenv_wf Gstore -> tenv_wf Genv -> tenv_wf_with_globals Gstore ->
            parameterized_wf Gstore Genv index_wf_with_globals c ->
            locals_wf Gstore store -> locals_wf Genv env ->
            holds_for_all_entries index_wf_with_globals store ->
            interp_command store env c = interp_command store env (fold_command_with_globals f c).
      Proof.
        induction c; simpl; intros; auto; invert_parameterized_wf.
        all: try erewrite <- fold_expr_preserve_sem; eauto;
          repeat destruct_match_goal; auto;
          repeat apply_fold_command_with_globals_preserve_sem_IH; eauto with fiat2_hints.
        1:{ eapply command_type_sound; eauto.
            eapply parameterized_wf__well_typed; eauto. }
        1:{ eapply parameterized_wf__preserve_P with (Gstore:=Gstore); eauto. }
        1: rewrite inb_false_iff in *; apply not_In__tenv_wf_with_globals; auto.
        1: rewrite inb_false_iff in *; apply not_In__index_wf_with_globals; auto.
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
    End WithGlobals.

    Section eq_filter_to_lookup.
      Context (k v acc p : string).

      Definition eq_filter_to_lookup_head (tbl attr : string) (e : expr) :=
        (* filter (idx_to_list idx) (fun row => row.attr == e') -->
           match (lookup idx e') with none => nil | some p => fst p ++ [snd p] *)
        match e with
        | EFilter
            (EDictFold (ELoc tbl0) (EAtom (ANil None)) k0 v0 acc0
               (EBinop OConcat
                  (EAccess (EVar v1) "0")
                  (EBinop OCons (EAccess (EVar v2) "1") (EVar acc1))))
            x
            (EBinop OEq (EAccess (EVar x0) attr0) e') =>
            if (all_eqb [(k, [k0]); (v, [v0; v1; v2]); (acc, [acc0; acc1]); (tbl, [tbl0]); (attr, [attr0]); (x, [x0])] &&
                  negb (String.eqb v acc) && negb (free_immut_in x e'))%bool
            then EOptMatch (ELookup (ELoc tbl) e')
                   enil
                   p (EBinop OConcat (ofst (EVar p)) (econs (osnd (EVar p)) enil))
            else e
        | _ => e
        end.

      Lemma eq_filter_to_lookup_head_preserve_ty : forall tbl attr rt (Gstore : tenv),
          is_NoDup [k; v; acc; p] ->
          map.get Gstore tbl = Some (index_type (get_attr_type rt attr) rt) ->
          preserve_ty Gstore (eq_filter_to_lookup_head tbl attr).
      Proof.
        unfold preserve_ty. intros.
        repeat destruct_subexpr. simpl.
        lazymatch goal with |- context[if ?x then _ else _] => destruct x eqn:E end; auto. repeat rewrite Bool.andb_true_r in E.
        repeat rewrite Bool.andb_true_iff in E; intuition. rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
        repeat invert_type_of. repeat rewrite_map_get_put_hyp.
        repeat (clear_refl; repeat do_injection).
        repeat (econstructor; eauto).
        1:{ lazymatch goal with H: ?x = _, H': ?x = _ |- _ => rewrite H in H' end.
            do_injection. do_injection. simpl in *; do_injection.
            unfold get_attr_type. rewrite_l_to_r.
            eapply not_free_immut_put_ty; eauto. }
        all: rewrite map.get_put_same; trivial.
      Qed.

      Lemma eq_filter_to_lookup_preserve_ty' :
        forall Gstore tbl rt attr,
          is_NoDup [k; v; acc; p] ->
          map.get Gstore tbl = Some (index_type (get_attr_type rt attr) rt) ->
          preserve_ty Gstore (fold_expr (eq_filter_to_lookup_head tbl attr)).
      Proof.
        intros. apply fold_expr_preserve_ty.
        eapply eq_filter_to_lookup_head_preserve_ty; eauto.
      Qed.

      Lemma eq_filter_to_lookup_preserve_ty :
        forall c Gstore Genv tbl rt attr,
          is_NoDup [k; v; acc; p] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          tenv_wf_with_globals [tbl] [index_type (get_attr_type rt attr) rt] Gstore ->
          well_typed Gstore Genv c -> well_typed Gstore Genv (fold_command_with_globals [tbl] (eq_filter_to_lookup_head tbl attr) c).
      Proof.
        intros. eapply fold_command_with_globals_preserve_ty.
        5: eauto.
        all: simpl in *; auto.
        intros. eapply eq_filter_to_lookup_head_preserve_ty; eauto.
        unfold tenv_wf_with_globals in *; invert_Forall2; eauto.
      Qed.

      Lemma dict_lookup__filter_none : forall attr k idx,
          index_wf attr idx ->
          dict_lookup k idx = None ->
          gallina_filter_access_eq attr k (gallina_idx_to_list idx) = nil.
      Proof.
        unfold gallina_filter_access_eq, record_proj.
        intros. induction idx; simpl; auto. unfold record_proj.
        destruct a; simpl in *. destruct v1; auto.
        destruct H as [HL HR]; inversion HL; inversion HR; subst; simpl in *.
        destruct (access_record l "0"); intuition; destruct a; intuition.
        destruct (access_record l "1"); intuition; destruct a; intuition.
        rewrite filter_app. destruct (value_eqb k0 v0) eqn:E.
        1: congruence. simpl.
        rewrite IHidx; auto. 2: split; auto.
        rewrite H1, value_eqb_sym, E, app_nil_r.
        induction H; simpl; auto. rewrite IHForall.
        destruct x; intuition. rewrite H, value_eqb_sym, E. reflexivity.
      Qed.

      Lemma not_In__dict_lookup : forall (v : value) d, ~ In v (List.map fst d) -> dict_lookup v d = None.
      Proof.
        intros * H. induction d; simpl; auto.
        destruct a; simpl in *. intuition. destruct_match_goal; auto.
        apply value_eqb_eq in E; subst; intuition.
      Qed.

      Lemma dict_lookup__filter_some : forall attr k idx l v,
          index_wf attr idx ->
          dict_lookup k idx = Some (VRecord [("0", VList l); ("1", v)]) ->
          gallina_filter_access_eq attr k (gallina_idx_to_list idx) = (l ++ [v])%list.
      Proof.
        intros * H_wf H_lookup. induction idx; simpl in *; try congruence.
        destruct a; simpl in *. destruct_match.
        all: inversion H_wf; subst; invert_Forall.
        1:{ do_injection; unfold record_proj; simpl. unfold gallina_filter_access_eq.
            apply value_eqb_eq in E; subst. rewrite filter_app. f_equal.
            1:{ apply forallb_filter_id. rewrite forallb_forall. intros x H_in.
                simpl in *; intuition. apply_Forall_In. destruct x; intuition.
                unfold record_proj. rewrite_l_to_r. apply value_eqb_refl. }
            1:{ simpl in *; destruct v0; intuition. unfold record_proj. rewrite_l_to_r. rewrite value_eqb_refl.
                f_equal. apply dict_lookup__filter_none. 1: eapply index_wf_step_inv; eauto.
                apply not_In__dict_lookup. inversion H; auto. } }
        1:{ simpl in *. destruct v2; intuition.
            unfold record_proj. repeat destruct_match; intuition.
            rewrite List.assoc_app_cons. unfold gallina_filter_access_eq. rewrite filter_app.
            lazymatch goal with |- _ = ?x => replace x with (app nil x) end; auto.
            f_equal. 2: rewrite <- IHidx; auto; eapply index_wf_step_inv; eauto.
            apply Forall_false__filter. apply Forall_app. split.
            1:{ rewrite Forall_forall. intros x H_in. apply_Forall_In. unfold record_proj.
                destruct x; intuition. rewrite_l_to_r. rewrite value_eqb_sym; auto. }
            1:{ constructor; auto. unfold record_proj; rewrite_l_to_r. rewrite value_eqb_sym; auto. } }
      Qed.

      Lemma eq_filter_to_lookup_head_preserve_sem : forall tbl attr (Gstore : tenv) (store : locals) rt,
          is_NoDup [k; v; acc; p] ->
          In attr (List.map fst rt) ->
          map.get Gstore tbl = Some (index_type (get_attr_type rt attr) rt) ->
          holds_for_all_entries (index_wf_with_globals [tbl] [attr]) store ->
          preserve_sem Gstore store (eq_filter_to_lookup_head tbl attr).
      Proof.
        unfold preserve_sem; intros. unfold holds_for_all_entries, index_wf_with_globals in *.
        lazymatch goal with
          H: context[get_attr_type] |- _ =>
            let H_tbl_ty := fresh "H_tbl_ty" in
            eapply TyELoc in H as H_tbl_ty
        end. apply_type_sound (ELoc tbl).
        repeat destruct_subexpr. unfold eq_filter_to_lookup_head.
        lazymatch goal with |- context[if ?x then _ else _] => destruct x eqn:E' end; auto.
        repeat rewrite Bool.andb_true_r in *. simpl in E'.
        repeat rewrite Bool.andb_true_iff in E'; intuition. rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
        rewrite fold_idx_to_list.
        repeat invert_type_of. repeat rewrite_map_get_put_hyp.
        repeat (clear_refl; repeat do_injection).
        erewrite fiat2_gallina_filter_access_eq; auto.
        2: eapply fiat2_gallina_idx_to_list with (Gstore:=Gstore); eauto; simpl; intuition.
        2: econstructor; eauto.
        simpl in H'. rewrite_expr_value.
        specialize (dict_lookup_sound (width:=width) l) as H_lookup.
        eapply (H_lookup (get_attr_type rt attr) _ (interp_expr store env e2_2)) in H'; eauto.
        2:{ unfold get_attr_type. lazymatch goal with
              H: ?x = _, H': ?x = _ |- _ => rewrite H in H'
              end. repeat (clear_refl; repeat do_injection).
            simpl in *; repeat do_injection. simpl in *; do_injection. rewrite_l_to_r.
            lazymatch goal with
              H: context[free_immut_in] |- _ =>
                eapply not_free_immut_put_ty in H; eauto
            end.
            eapply type_sound; eauto. }
        simpl. rewrite <- H8. unfold get_local; inversion H'; subst.
        2: rewrite map.get_put_same.
        (* dict_lookup found no match *)
        1:{ f_equal; apply dict_lookup__filter_none; auto.
            lazymatch goal with
              H: VDict _ = get_local _ _ |- _ =>
                symmetry in H; unfold get_local in H; destruct_match; try discriminate end.
            lazymatch goal with
              E: map.get store _ = _,
                H: (forall _ _, map.get _ _ = _ -> _) |- _ =>
                apply H in E end. invert_Forall2; intuition. }
        (* dict_lookup found some match *)
        1:{ invert_type_of_value. repeat invert_Forall2.
            destruct x0, x1; intuition; simpl in *; subst.
            unfold record_proj; simpl. invert_type_of_value. f_equal.
            apply dict_lookup__filter_some; try congruence.
            lazymatch goal with
              H: VDict _ = get_local _ _ |- _ =>
                symmetry in H; unfold get_local in H; destruct_match; try discriminate end.
            lazymatch goal with
              E: map.get store _ = _,
                H: (forall _ _, map.get _ _ = _ -> _) |- _ =>
                apply H in E end. inversion E; subst. intuition. }
      Qed.

      Lemma eq_filter_to_lookup_preserve_sem' :
        forall Gstore store tbl rt attr,
          is_NoDup [k; v; acc; p] ->
          In attr (List.map fst rt) ->
          map.get Gstore tbl = Some (index_type (get_attr_type rt attr) rt) ->
          holds_for_all_entries (index_wf_with_globals [tbl] [attr]) store ->
          preserve_sem Gstore store (fold_expr (eq_filter_to_lookup_head tbl attr)).
      Proof.
        intros. apply fold_expr_preserve_sem.
        1: eapply eq_filter_to_lookup_head_preserve_ty; eauto.
        eapply eq_filter_to_lookup_head_preserve_sem with (Gstore:=Gstore); eauto.
      Qed.

      Lemma eq_filter_to_lookup_preserve_sem :
        forall c (Gstore Genv : tenv) (store env : locals) tbl rt attr,
          is_NoDup [k; v; acc; p] ->
          In attr (List.map fst rt) ->
          tenv_wf Gstore -> tenv_wf Genv ->
          tenv_wf_with_globals [tbl] [index_type (get_attr_type rt attr) rt] Gstore ->
          parameterized_wf Gstore Genv (index_wf_with_globals [tbl] [attr]) c ->
          locals_wf Gstore store -> locals_wf Genv env ->
          holds_for_all_entries (index_wf_with_globals [tbl] [attr]) store ->
          interp_command store env c = interp_command store env (fold_command_with_globals [tbl] (eq_filter_to_lookup_head tbl attr) c).
      Proof.
        intros.
        eapply fold_command_with_globals_preserve_sem with (Gstore:=Gstore); simpl in *; auto.
        6, 9: eauto.
        all: intros; simpl in *; eauto.
        all: unfold tenv_wf_with_globals in H8; inversion H8; subst.
        1: eapply eq_filter_to_lookup_head_preserve_ty; eauto.
        1: eapply eq_filter_to_lookup_head_preserve_sem with (Gstore:=Gstore0); eauto.
      Qed.

      Lemma eq_filter_to_lookup_preserve_index_wf :
        forall c Gstore Genv tbl rt attr,
          is_NoDup [k; v; acc; p] ->
          In attr (List.map fst rt) ->
          tenv_wf Gstore -> tenv_wf Genv ->
          tenv_wf_with_globals [tbl] [index_type (get_attr_type rt attr) rt] Gstore ->
          parameterized_wf Gstore Genv (index_wf_with_globals [tbl] [attr]) c -> parameterized_wf Gstore Genv (index_wf_with_globals [tbl] [attr]) (fold_command_with_globals [tbl] (eq_filter_to_lookup_head tbl attr) c).
      Proof.
        intros. eapply fold_command_with_globals_preserve_parameterized_wf.
        6: eauto.
        all: simpl in *; auto; intros.
        all:  unfold tenv_wf_with_globals in *; repeat invert_Forall2.
        1: eapply eq_filter_to_lookup_head_preserve_ty; eauto.
        1: eapply eq_filter_to_lookup_head_preserve_sem; eauto.
      Qed.
    End eq_filter_to_lookup.

    Notation elist_to_idx tup0 tup1 tup2 tup3 tup4 acc0 acc1 acc2 x0 x1 x2 attr0 attr1 d :=
      (EFold d (EDict []) tup0 acc0
         (EInsert (EVar acc1) (EAccess (EVar tup1) attr0) (EOptMatch (ELookup (EVar acc2) (EAccess (EVar tup2) attr1)) (ERecord [("0", EAtom (ANil None)); ("1", EVar tup3)]) x0 (ERecord [("0", EBinop OCons (EVar tup4) (EAccess (EVar x1) "0")); ("1", EAccess (EVar x2) "1")] )))).

    Notation eidx_to_list k v0 v1 v2 acc0 acc1 d :=
      (EDictFold d (EAtom (ANil None)) k v0 acc0 (EBinop OConcat (EAccess (EVar v1) "0") (EBinop OCons (EAccess (EVar v2) "1") (EVar acc1)))).

    Notation efilter x0 x1 attr0 k l :=
      (EFilter l x0 (EUnop ONot (EBinop OEq (EAccess (EVar x1) attr0) k))).

    Section neq_filter_to_delete.
      Context (k v acc tup x : string).

      Definition neq_filter_to_delete_head (tbl attr : string) (e : expr) :=
        (* list_to_idx (filter (idx_to_list idx) (fun row => row.attr != e)) = delete idx e *)
        match e with
        | elist_to_idx tup0 tup1 tup2 tup3 tup4 acc0 acc1 acc2 x0 x1 x2 attr0 attr1
            ((efilter y0 y1 attr2 k' (eidx_to_list k0 v0 v1 v2 acc3 acc4 (ELoc tbl0))))
  => if (all_eqb [(tbl, [tbl0]); (k,[k0]); (v,[v0; v1; v2]); (acc, [acc0; acc1; acc2; acc3; acc4]); (y0, [y1]); (tup, [tup0; tup1; tup2; tup3; tup4]); (attr, [attr0; attr1; attr2]); (x, [x0; x1; x2])] && negb (free_immut_in y0 k'))%bool
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

      Lemma neq_filter_to_delete_head_preserve_ty : forall tbl attr rt (Gstore : tenv),
          is_NoDup [v; acc; tup; x] ->
          map.get Gstore tbl = Some (index_type (get_attr_type rt attr) rt) ->
          preserve_ty Gstore (neq_filter_to_delete_head tbl attr).
      Proof.
        unfold preserve_ty; intros.
        repeat destruct_subexpr. simpl. destruct_match_goal; auto.
        repeat rewrite Bool.andb_true_r in E. repeat rewrite Bool.andb_true_iff in E; intuition.
        rewrite Bool.negb_true_iff, eqb_eq in *; subst.
        repeat invert_type_of. repeat rewrite_map_get_put_hyp. repeat (clear_refl; repeat do_injection).
        repeat constructor; auto.
        1:{ lazymatch goal with
            H: map.get Gstore tbl = _, H': map.get Gstore tbl = _ |- _ =>
              rewrite H in *; do_injection; simpl in *; do_injection
          end.
            unfold get_attr_type. rewrite H30.
            do 3 (destruct tl; simpl in *; try congruence). destruct p, p0; simpl in *. do_injection; intros; subst.
            assert ([("0", t); ("1", t0)] = tl').
            { multimatch goal with
                H: Permutation _ _ |- _ => apply Permutation_length_2_inv in H; destruct H end.
              all: lazymatch goal with
                     H: cons _ _ = cons _ _ |- _ => inversion H; subst; auto end.
              invert_SSorted. invert_Forall. unfold record_entry_leb in *; simpl in *.
              lazymatch goal with H: is_true(_ <=? _) |- _ => inversion H end. }
            inversion H7; subst. repeat invert_type_of. repeat rewrite_map_get_put_hyp. repeat (clear_refl; do_injection).
            unfold index_type.
            repeat invert_Forall2. repeat invert_type_of; repeat rewrite_map_get_put_hyp. repeat do_injection.
            simpl in *; repeat do_injection. repeat clear_refl.
            lazymatch goal with
              H: ?x = _, H': ?x = _ |- _ => rewrite H in H' end. do_injection.
            lazymatch goal with
              H: cons _ _ = cons _ _ |- _ => inversion H; subst; auto end.
             multimatch goal with
                H: Permutation tl1 _ |- _ => apply Permutation_sym, Permutation_length_2_inv in H; destruct H end.
              all: lazymatch goal with
                     H: _ = cons _ _ |- _ => inversion H; subst; auto end.
              all: simpl in *; repeat multimatch goal with
                                       H: cons _ _ = cons _ _ |- _ => inversion H; subst; auto end. }
        1:{ repeat lazymatch goal with
              H: ?x = _, H': ?x = _ |- _ => rewrite H in H'
              end. repeat (clear_refl; repeat do_injection).
            eapply not_free_immut_put_ty; eauto. }
      Qed.

      Lemma neq_filter_to_delete_preserve_ty' :
        forall Gstore tbl rt attr,
          is_NoDup [v; acc; tup; x] ->
          map.get Gstore tbl = Some (index_type (get_attr_type rt attr) rt) ->
          preserve_ty Gstore (fold_expr (neq_filter_to_delete_head tbl attr)).
      Proof.
        intros. apply fold_expr_preserve_ty.
        eapply neq_filter_to_delete_head_preserve_ty; eauto.
      Qed.

      Lemma neq_filter_to_delete_preserve_ty :
        forall c Gstore Genv tbl rt attr,
          is_NoDup [v; acc; tup; x] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          tenv_wf_with_globals [tbl] [index_type (get_attr_type rt attr) rt] Gstore ->
          well_typed Gstore Genv c -> well_typed Gstore Genv (fold_command_with_globals [tbl] (neq_filter_to_delete_head tbl attr) c).
      Proof.
        intros. eapply fold_command_with_globals_preserve_ty.
        5: eauto.
        all: simpl in *; auto.
        intros. eapply neq_filter_to_delete_head_preserve_ty; eauto.
        unfold tenv_wf_with_globals in *; invert_Forall2; eauto.
      Qed.

      Lemma fold_list_to_idx : forall tup acc x attr tbl,
          EFold tbl (EDict []) tup acc
            (EInsert (EVar acc) (EAccess (EVar tup) attr)
               (EOptMatch (ELookup (EVar acc) (EAccess (EVar tup) attr))
                  (epair enil (EVar tup)) x (cons_to_fst (EVar tup) (EVar x)))) =
            list_to_idx tup acc x attr tbl.
      Proof. reflexivity. Qed.

      Lemma dict_insert_Lt : forall k (v : value) d,
          (forall p, In p d -> value_compare k (fst p) = Lt) ->
          dict_insert k v d = (k, v) :: d.
      Proof.
        destruct d; simpl; auto; intros.
        repeat destruct_match_goal; auto.
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

      Local Ltac invert_NoDup :=
        lazymatch goal with H: NoDup (_ :: _) |- _ => inversion H; subst; clear H end.

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

      Lemma gallina_idx_to_list_to_idx : forall attr idx kt rt,
          type_of_value (VDict idx) (index_type kt rt) ->
          index_wf attr idx -> gallina_list_to_idx attr (gallina_idx_to_list idx) = idx.
      Proof.
        intros * H_ty H_wf. induction idx; simpl; auto.
        apply index_wf_step_inv in H_wf as H_wf'.
        destruct a as [k0 v0]; simpl.
        destruct H_wf as [HL HR]. inversion HL; inversion HR; subst.
        destruct v0; simpl in *; intuition. unfold record_proj. repeat destruct_match; intuition.

        unfold gallina_list_to_idx in *. rewrite List.assoc_app_cons, fold_right_app. rewrite IHidx; auto.
        all: inversion H_ty; subst; invert_Forall; invert_SSorted; subst. 2: constructor; intuition.
        generalize dependent l; induction l1; intros; simpl in *; auto.
        all: intuition; inversion H4; subst; repeat invert_Forall2.
        all: destruct x0, x1; simpl in *; intuition; subst.
        1:{ unfold record_proj; lazymatch goal with H: ?x = Success _ |- context[?x] => rewrite H end.
            rewrite dict_lookup_Lt; eauto using NoDup_SSorted__Lt.
            rewrite dict_insert_Lt; eauto using NoDup_SSorted__Lt; congruence. }
        1:{ destruct v0; simpl in *; try congruence. destruct l; try congruence.
            rewrite IHl1 with (l:=[("0", VList l); ("1", v1)]); simpl; auto; try congruence.
            all: repeat invert_Forall; intuition.
            all: repeat (constructor; simpl in *; auto);
              lazymatch goal with H: type_of_value (VList (_ :: ?l)) _ |- _ => inversion H; subst end;
              invert_Forall; intuition.
            2: invert_Forall; auto.
            destruct_match_goal; intuition. unfold record_proj. rewrite_l_to_r.
            unfold value_ltb, value_eqb. rewrite value_compare_refl.
            unfold vcons_to_fst, record_proj; simpl. congruence. }
      Qed.

      Lemma not_In__dict_delete : forall (k : value) d, ~ In k (List.map fst d) -> dict_delete k d = d.
      Proof.
        induction d; intros; simpl; auto.
        destruct a; destruct_match_goal; simpl in *.
        1:apply value_eqb_eq in E; subst; intuition.
        f_equal. auto.
      Qed.

      Lemma gallina_filter_access_neq_idx_to_list : forall attr k idx,
          index_wf attr idx ->
          gallina_filter_access_neq attr k (gallina_idx_to_list idx) = gallina_idx_to_list (dict_delete k idx).
      Proof.
        intros * H. induction idx; auto.
        simpl. inversion H; invert_Forall. destruct_match; intuition; simpl in *.
        repeat destruct_match; intuition. unfold record_proj; repeat rewrite_l_to_r.
        destruct a; simpl in *.
        unfold gallina_filter_access_neq in *. rewrite filter_app. simpl. rewrite IHidx.
        2: eapply index_wf_step_inv; eauto.
        destruct (value_eqb k0 v0) eqn:E_k0v0.
        1:{ apply value_eqb_eq in E_k0v0; subst. unfold record_proj; rewrite_l_to_r. rewrite value_eqb_refl; simpl.
            rewrite not_In__dict_delete. 2: invert_NoDup; auto.
            rewrite Forall_false__filter; auto. rewrite Forall_forall; intros. apply_Forall_In.
            destruct_match; intuition. rewrite_l_to_r. rewrite value_eqb_refl; auto. }
        1:{ simpl. unfold record_proj; rewrite value_eqb_sym; repeat rewrite_l_to_r. simpl.
            f_equal. apply forallb_filter_id. rewrite forallb_forall; intros; apply_Forall_In.
            destruct_match; intuition. rewrite_l_to_r. rewrite value_eqb_sym. rewrite_l_to_r; auto. }
      Qed.

      Lemma dict_delete_preserve_index_wf : forall attr idx,
          index_wf attr idx ->
          forall k, index_wf attr (dict_delete k idx).
      Proof.
        intros * H_wf *.
        induction idx; simpl; auto.
        destruct a. destruct (value_eqb k0 v0).
        all: apply index_wf_step_inv in H_wf as H_wf'; auto.
        specialize (IHidx H_wf').
        destruct H_wf as [HL HR]; inversion HL; inversion HR; subst.
        unfold index_wf; simpl; intuition.
        1:{ constructor. 1: apply dict_delete_preserve_NoDup; auto. apply IHidx; auto. }
        1:{ constructor; auto. eapply incl_Forall; eauto. apply dict_delete_incl. }
      Qed.

      Lemma neq_filter_to_delete_head_preserve_sem : forall tbl attr (Gstore : tenv) (store : locals) rt,
          is_NoDup [v; acc; tup; x] ->
          In attr (List.map fst rt) ->
          map.get Gstore tbl = Some (index_type (get_attr_type rt attr) rt) ->
          holds_for_all_entries (index_wf_with_globals [tbl] [attr]) store ->
          preserve_sem Gstore store (neq_filter_to_delete_head tbl attr).
      Proof.
        unfold preserve_sem; intros. unfold holds_for_all_entries, index_wf_with_globals in *.
        lazymatch goal with
          H: context[get_attr_type] |- _ =>
            let H_tbl_ty := fresh "H_tbl_ty" in
            eapply TyELoc in H as H_tbl_ty
        end. apply_type_sound (ELoc tbl).
        repeat destruct_subexpr. unfold neq_filter_to_delete_head. destruct_match_goal; auto.
        simpl in E. repeat rewrite Bool.andb_true_r in E.
        repeat rewrite Bool.andb_true_iff in E; intuition. rewrite Bool.negb_true_iff, eqb_eq in *; subst.
        rewrite fold_idx_to_list, fold_list_to_idx in *.
        erewrite fiat2_gallina_list_to_idx with (Gstore:=Gstore); eauto.
        2: simpl in *; intuition.
        3:{ erewrite fiat2_gallina_filter_access_neq; auto. eapply fiat2_gallina_idx_to_list with (Gstore:=Gstore); eauto.
            simpl in *; intuition. }
        2:{ repeat invert_type_of. repeat rewrite_map_get_put_hyp; repeat (clear_refl; repeat do_injection).
            repeat (constructor; auto).
            1: eapply idx_to_list_preserve_ty; eauto; constructor; eauto; simpl in *; intuition.
            lazymatch goal with
              H: ?x = _, H': ?x = _ |- _ => rewrite H in H'
            end; do_injection; auto. simpl in *; do_injection.
            repeat (econstructor; eauto). rewrite_map_get_put_goal; auto. }
        simpl. rewrite_expr_value. f_equal.
        erewrite gallina_filter_access_neq_idx_to_list, gallina_idx_to_list_to_idx; auto.
        2: apply dict_delete_preserve_index_wf.
        2,3: lazymatch goal with
               H: VDict _ = get_local _ _ |- _ =>
                 symmetry in H; unfold get_local in H; destruct_match; try discriminate end;
        lazymatch goal with
          E: map.get _ _ = Some _,
            H: (forall _ _, map.get _ _ = _ -> _) |- _ =>
            apply H in E end; invert_Forall2; intuition.
        apply dict_delete_sound.
        3: simpl in *; rewrite_expr_value; eauto.
        all: repeat invert_type_of; repeat rewrite_map_get_put_hyp; repeat (clear_refl; repeat do_injection).
        all: repeat lazymatch goal with
                 H: ?x = _, H': ?x = _ |- _ => rewrite H in H'
               end; [> do_injection ..]; simpl in *; repeat (clear_refl; repeat do_injection).
        lazymatch goal with
          H: type_of _ _ ?e _ |- context[?e] =>
            apply not_free_immut_put_ty in H; auto; eapply type_sound in H; eauto
        end.
        unfold get_attr_type. rewrite_l_to_r; auto.
      Qed.

      Lemma neq_filter_to_delete_preserve_sem' :
        forall Gstore store tbl rt attr,
          is_NoDup [v; acc; tup; x] ->
          In attr (List.map fst rt) ->
          map.get Gstore tbl = Some (index_type (get_attr_type rt attr) rt) ->
          holds_for_all_entries (index_wf_with_globals [tbl] [attr]) store ->
          preserve_sem Gstore store (fold_expr (neq_filter_to_delete_head tbl attr)).
      Proof.
        intros. apply fold_expr_preserve_sem.
        1: eapply  neq_filter_to_delete_head_preserve_ty; eauto.
        eapply  neq_filter_to_delete_head_preserve_sem with (Gstore:=Gstore); eauto.
      Qed.

      Lemma neq_filter_to_delete_preserve_sem :
        forall c (Gstore Genv : tenv) (store env : locals) tbl rt attr,
          is_NoDup [v; acc; tup; x] ->
          In attr (List.map fst rt) ->
          tenv_wf Gstore -> tenv_wf Genv ->
          tenv_wf_with_globals [tbl] [index_type (get_attr_type rt attr) rt] Gstore ->
          parameterized_wf Gstore Genv (index_wf_with_globals [tbl] [attr]) c ->
          locals_wf Gstore store -> locals_wf Genv env ->
          holds_for_all_entries (index_wf_with_globals [tbl] [attr]) store ->
          interp_command store env c = interp_command store env (fold_command_with_globals [tbl] (neq_filter_to_delete_head tbl attr) c).
      Proof.
        intros.
        eapply fold_command_with_globals_preserve_sem with (Gstore:=Gstore); simpl in *; auto.
        6, 9: eauto.
        all: intros; simpl in *; eauto.
        all: unfold tenv_wf_with_globals in H8; inversion H8; subst.
        1: eapply neq_filter_to_delete_head_preserve_ty; eauto.
        1: eapply neq_filter_to_delete_head_preserve_sem with (Gstore:=Gstore0); eauto.
      Qed.

      Lemma neq_filter_to_delete_preserve_index_wf :
        forall c Gstore Genv tbl rt attr,
          is_NoDup [v; acc; tup; x] ->
          In attr (List.map fst rt) ->
          tenv_wf Gstore -> tenv_wf Genv ->
          tenv_wf_with_globals [tbl] [index_type (get_attr_type rt attr) rt] Gstore ->
          parameterized_wf Gstore Genv (index_wf_with_globals [tbl] [attr]) c -> parameterized_wf Gstore Genv (index_wf_with_globals [tbl] [attr]) (fold_command_with_globals [tbl] (neq_filter_to_delete_head tbl attr) c).
      Proof.
        intros. eapply fold_command_with_globals_preserve_parameterized_wf.
        6: eauto.
        all: simpl in *; auto; intros.
        all:  unfold tenv_wf_with_globals in *; repeat invert_Forall2.
        1: eapply neq_filter_to_delete_head_preserve_ty; eauto.
        1: eapply neq_filter_to_delete_head_preserve_sem; eauto.
      Qed.
    End neq_filter_to_delete.

    Section cons_to_insert.
      Context (k v acc tup x y : string).

      Definition cons_to_insert_head (tbl attr : string) (e : expr) :=
        (* list_to_idx (cons e (idx_to_list idx)) = insert idx (e.attr) (e :: lookup idx e.attr) *)
        match e with
        | elist_to_idx tup0 tup1 tup2 tup3 tup4 acc0 acc1 acc2 x0 x1 x2 attr0 attr1
            (EBinop OCons row (eidx_to_list k0 v0 v1 v2 acc3 acc4 (ELoc tbl0))) =>
            if (all_eqb [(tbl, [tbl0]); (k,[k0]); (v, [v0; v1; v2]); (acc, [acc0; acc1; acc2; acc3; acc4]); (tup, [tup0; tup1; tup2; tup3; tup4]); (attr, [attr0; attr1]); (x, [x0; x1; x2])] && negb (free_immut_in y row))%bool
            then EInsert (ELoc tbl) (EAccess row attr)
                   (EOptMatch (ELookup (ELoc tbl) (EAccess row attr)) (epair enil row) y (cons_to_fst row (EVar y)))
            else e
        | _ => e
        end.

      Lemma cons_to_insert_head_preserve_ty : forall tbl attr rt (Gstore : tenv),
          is_NoDup [tup; acc; v; x] ->
          map.get Gstore tbl = Some (index_type (get_attr_type rt attr) rt) ->
          preserve_ty Gstore (cons_to_insert_head tbl attr).
      Proof.
        unfold preserve_ty; intros.
        repeat destruct_subexpr. simpl; auto.
        destruct_match_goal; auto. repeat rewrite Bool.andb_true_r in E.
        repeat rewrite Bool.andb_true_iff in E; intuition. rewrite eqb_eq, Bool.negb_true_iff in *; subst.
        repeat invert_type_of. repeat rewrite_map_get_put_hyp. repeat (try clear_refl; repeat do_injection); auto.
        repeat (econstructor; eauto).
        all: repeat invert_Forall2; simpl in *; repeat invert_type_of;
          repeat rewrite_map_get_put_hyp; repeat (try clear_refl; repeat do_injection).
        1:{ lazymatch goal with
            H: map.get Gstore tbl = _, H': map.get Gstore tbl = _ |- _=>
              rewrite H in H'; repeat do_injection; rewrite H; repeat f_equal end.
            simpl in *. repeat (try clear_refl; repeat do_injection).
            unfold get_attr_type, index_type. rewrite_l_to_r.
            do 3 (destruct tl; simpl in *; try congruence).
            do 3 (destruct tl1; simpl in *; try congruence).
            lazymatch goal with
            | H: Permutation _ _ |- _ =>
                apply Permutation_length_2_inv in H; destruct H; subst
            end.
            2:{ invert_SSorted. lazymatch goal with H: Forall _ [_] |- _ => inversion H; subst end.
                unfold record_entry_leb in *.
                repeat lazymatch goal with H: ["0"; "1"] = [_; _] |- _ => inversion H; subst; clear H end.
                lazymatch goal with
                  H1: _ = fst p1, H2: _ = fst p2 |- _ =>
                    rewrite <- H1, <- H2 in *
                end.
                lazymatch goal with
                  H: is_true _ |- _ => inversion H end. }
            repeat lazymatch goal with
                     H: _ :: _ = _ :: _ |- _ => inversion H; subst; clear H end.
            destruct p, p0, p1, p2; simpl in *.
            repeat lazymatch goal with
                   | H: "0" = _ |- _ => rewrite <- H in *; clear H
                   | H: "1" = _ |- _ => rewrite <- H in *; clear H
                   end.
            congruence. }
        1:{ lazymatch goal with
             H: map.get Gstore tbl = _, H': map.get Gstore tbl = _ |- _=>
               rewrite H in H'; repeat do_injection end.
            simpl in *; do_injection. unfold get_attr_type. rewrite_l_to_r; auto. }
        1: repeat constructor; auto.
        1:{ do 3 (destruct tl; simpl in *; try congruence).
            do 3 (destruct tl1; simpl in *; try congruence).
            lazymatch goal with
            | H: Permutation _ _ |- _ =>
                apply Permutation_length_2_inv in H; destruct H; subst
            end.
            2:{ invert_SSorted. lazymatch goal with H: Forall _ [_] |- _ => inversion H; subst end.
                unfold record_entry_leb in *.
                repeat lazymatch goal with H: ["0"; "1"] = [_; _] |- _ => inversion H; subst; clear H end.
                lazymatch goal with
                  H1: _ = fst p1, H2: _ = fst p2 |- _ =>
                    rewrite <- H1, <- H2 in *
                end.
                lazymatch goal with
                  H: is_true _ |- _ => inversion H end. }
            repeat lazymatch goal with
                     H: _ :: _ = _ :: _ |- _ => inversion H; subst; clear H end.
            destruct p, p0, p1, p2; simpl in *.
            repeat lazymatch goal with
                   | H: "0" = _ |- _ => rewrite <- H in *; clear H
                   | H: "1" = _ |- _ => rewrite <- H in *; clear H
                   end. repeat (try clear_refl; repeat do_injection).
            repeat (econstructor; eauto).
            2,3: rewrite_map_get_put_goal; auto.
            apply not_free_immut_put_ty_iff; auto. }
      Qed.

      Lemma cons_to_insert_preserve_ty' :
        forall Gstore tbl rt attr,
          is_NoDup [tup; acc; v; x] ->
          map.get Gstore tbl = Some (index_type (get_attr_type rt attr) rt) ->
          preserve_ty Gstore (fold_expr (cons_to_insert_head tbl attr)).
      Proof.
        intros. apply fold_expr_preserve_ty.
        eapply cons_to_insert_head_preserve_ty; eauto.
      Qed.

      Lemma cons_to_insert_preserve_ty :
        forall c Gstore Genv tbl rt attr,
          is_NoDup [tup; acc; v; x] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          tenv_wf_with_globals [tbl] [index_type (get_attr_type rt attr) rt] Gstore ->
          well_typed Gstore Genv c -> well_typed Gstore Genv (fold_command_with_globals [tbl] (cons_to_insert_head tbl attr) c).
      Proof.
        intros. eapply fold_command_with_globals_preserve_ty.
        5: eauto.
        all: simpl in *; auto.
        intros. eapply cons_to_insert_head_preserve_ty; eauto.
        unfold tenv_wf_with_globals in *; invert_Forall2; eauto.
      Qed.

      Lemma cons_to_insert_head_preserve_sem : forall tbl attr (Gstore : tenv) (store : locals) rt,
          is_NoDup [tup; acc; v; x] ->
          In attr (List.map fst rt) ->
          map.get Gstore tbl = Some (index_type (get_attr_type rt attr) rt) ->
          holds_for_all_entries (index_wf_with_globals [tbl] [attr]) store ->
          preserve_sem Gstore store (cons_to_insert_head tbl attr).
      Proof.
        unfold preserve_sem; intros. unfold holds_for_all_entries, index_wf_with_globals in *.
        lazymatch goal with
          H: context[get_attr_type] |- _ =>
            let H_tbl_ty := fresh "H_tbl_ty" in
            eapply TyELoc in H as H_tbl_ty
        end. apply_type_sound (ELoc tbl).
        repeat destruct_subexpr. unfold cons_to_insert_head. destruct_match_goal; auto.
        simpl in E. repeat rewrite Bool.andb_true_r in *.
        repeat rewrite Bool.andb_true_iff in *; intuition. rewrite eqb_eq, Bool.negb_true_iff in *; subst.
        repeat invert_type_of. repeat rewrite_map_get_put_hyp. repeat (clear_refl; repeat do_injection).
        rewrite fold_list_to_idx, fold_idx_to_list. erewrite fiat2_gallina_list_to_idx with (Gstore:=Gstore); eauto.
        2: simpl in *; intuition.
        2:{ repeat (econstructor; eauto).
            2-4: repeat rewrite_map_get_put_goal; reflexivity.
            lazymatch goal with
              H: ?x = _, H': ?x = _ |- _ => rewrite H in H'
            end. do_injection. simpl in *. do_injection. constructor; auto. }
        2:{ assert(E_cons: forall e1 e2, interp_expr store env (EBinop OCons e1 e2) =
                                   interp_binop OCons (interp_expr store env e1) (interp_expr store env e2)).
            { reflexivity. }
            rewrite E_cons. erewrite fiat2_gallina_idx_to_list with (Gstore:=Gstore); eauto.
            2: simpl in *; intuition.
            2: constructor; eauto.
            simpl; eauto. }
        simpl. rewrite_expr_value. f_equal.
        apply_type_sound e1_1.
        f_equal. 1: erewrite gallina_idx_to_list_to_idx; eauto.
        all: lazymatch goal with
               H: VDict _ = get_local _ _ |- _ =>
                 symmetry in H; unfold get_local in H end;
           destruct_match; try discriminate; subst.
        3: lazymatch goal with
             E: map.get store _ = Some _,
               H: (forall _ _, map.get _ _ = _ -> _) |- _ =>
               apply H in E end; inversion E; subst; intuition.
        3: eapply gallina_idx_to_list_to_idx; eauto.
        4: lazymatch goal with
             E: map.get store _ = Some _,
               H: (forall _ _, map.get _ _ = _ -> _) |- _ =>
               apply H in E end; inversion E; subst; intuition.
        2,3: lazymatch goal with
             | H: locals_wf ?Gstore ?store,
                 H_ty: map.get ?Gstore _ = Some (index_type _ _),
                   H_v: map.get ?store _ = _ |- _ =>
                 let H_tbl := fresh "H_tbl" in
                 apply H in H_ty as H_tbl; rewrite H_v in H_tbl
             end; eauto.
        destruct_match_goal; auto.
        unfold vcons_to_fst. f_equal. unfold get_local; rewrite_map_get_put_goal.
        repeat destruct_match_goal; try reflexivity.
        rewrite <- not_free_immut_put_sem; auto.
        lazymatch goal with H: VRecord _ = ?e |- context[?e] => rewrite <- H end; auto.
      Qed.

      Lemma cons_to_insert_preserve_sem' :
        forall Gstore store tbl rt attr,
          is_NoDup [tup; acc; v; x] ->
          In attr (List.map fst rt) ->
          map.get Gstore tbl = Some (index_type (get_attr_type rt attr) rt) ->
          holds_for_all_entries (index_wf_with_globals [tbl] [attr]) store ->
          preserve_sem Gstore store (fold_expr (cons_to_insert_head tbl attr)).
      Proof.
        intros. apply fold_expr_preserve_sem.
        1: eapply cons_to_insert_head_preserve_ty; eauto.
        eapply cons_to_insert_head_preserve_sem with (Gstore:=Gstore); eauto.
      Qed.

      Lemma cons_to_insert_preserve_sem :
        forall c (Gstore Genv : tenv) (store env : locals) tbl rt attr,
          is_NoDup [tup; acc; v; x] ->
          In attr (List.map fst rt) ->
          tenv_wf Gstore -> tenv_wf Genv ->
          tenv_wf_with_globals [tbl] [index_type (get_attr_type rt attr) rt] Gstore ->
          parameterized_wf Gstore Genv (index_wf_with_globals [tbl] [attr]) c ->
          locals_wf Gstore store -> locals_wf Genv env ->
          holds_for_all_entries (index_wf_with_globals [tbl] [attr]) store ->
          interp_command store env c = interp_command store env (fold_command_with_globals [tbl] (cons_to_insert_head tbl attr) c).
      Proof.
        intros.
        eapply fold_command_with_globals_preserve_sem with (Gstore:=Gstore); simpl in *; auto.
        6, 9: eauto.
        all: intros; simpl in *; eauto.
        all: unfold tenv_wf_with_globals in H8; inversion H8; subst.
        1: eapply cons_to_insert_head_preserve_ty; eauto.
        1: eapply cons_to_insert_head_preserve_sem with (Gstore:=Gstore0); eauto.
      Qed.

      Lemma cons_to_insert_preserve_index_wf :
        forall c Gstore Genv tbl rt attr,
          is_NoDup [tup; acc; v; x] ->
          In attr (List.map fst rt) ->
          tenv_wf Gstore -> tenv_wf Genv ->
          tenv_wf_with_globals [tbl] [index_type (get_attr_type rt attr) rt] Gstore ->
          parameterized_wf Gstore Genv (index_wf_with_globals [tbl] [attr]) c -> parameterized_wf Gstore Genv (index_wf_with_globals [tbl] [attr]) (fold_command_with_globals [tbl] (cons_to_insert_head tbl attr) c).
      Proof.
        intros. eapply fold_command_with_globals_preserve_parameterized_wf.
        6: eauto.
        all: simpl in *; auto; intros.
        all:  unfold tenv_wf_with_globals in *; repeat invert_Forall2.
        1: eapply cons_to_insert_head_preserve_ty; eauto.
        1: eapply cons_to_insert_head_preserve_sem; eauto.
      Qed.
    End cons_to_insert.
  End WithMap.

  (* ??? TODO: move *)
  Section ConcreteExample.
    Local Open Scope string.

    Definition ex1 := CLetMut (EAtom (ANil (Some (TRecord (("id", TInt) :: ("name", TString) :: nil))))) "persons"
                        (*  (CLetMut (EAtom (AInt 0)) "res" *)
                        (CSeq
                           (CAssign "persons" (EBinop OCons
                                                 (ERecord (("id", EAtom (AInt 1)) :: ("name", EAtom (AString "K")) :: nil))
                                                 (ELoc "persons")))
                           (CSeq
                              (CAssign "res" (EUnop OLength (ELoc "persons")))
                              CSkip)).

    Instance ctenv : map.map string type := SortedListString.map _.
    Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

    Instance clocals : map.map string value := SortedListString.map _.
    Instance clocals_ok : map.ok clocals := SortedListString.ok _.
(*
    Set Printing Implicit.
    Check typecheck map.empty map.empty ex1.
    Set Printing Coercions.
    Compute @map.empty string type ctenv.
    Compute @map.rep string type ctenv.

    Compute typecheck (map.put map.empty "res" TInt) map.empty ex1.
*)
    Definition ex1' := transf_to_idx "tup" "acc" "x" "k" "v" "persons" "id" ex1.
(*    Compute ex1'. *)

    Definition ex1'' := fold_command id (cons_to_insert_head "k" "v" "acc" "tup" "x" "y" "persons" "id") ex1'.
(*    Compute ex1''. *)

    Goal interp_command (map.put map.empty "res" (VInt 0)) (map.empty (value:=value)) ex1'' = interp_command (map.put map.empty "res" (VInt 0)) map.empty ex1.
    Proof. reflexivity. Abort.
  End ConcreteExample.
End WithWord.
