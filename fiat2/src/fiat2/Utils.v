Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Require Import List String ZArith Permutation Sorted.
Import ListNotations.
Require Import Ltac2.Ltac2 Ltac2.Control Ltac2.Constr.

Set Default Proof Mode "Classic".

Ltac invert_type_wf :=
  lazymatch goal with
  | H: type_wf (TList ?t) |- _ => inversion H; clear H; subst
  | H: type_wf (TBag ?t) |- _ => inversion H; clear H; subst
  | H: type_wf (TOption ?t) |- _ => inversion H; clear H; subst
  | H: type_wf (TDict ?t _) |- _ => inversion H; clear H; subst
  | H: type_wf (TDict _ ?t) |- _ => inversion H; clear H; subst
  | H: type_wf (TRecord ?tl) |- _ => inversion H; clear H; subst
  end.

Lemma invert_TList_wf: forall t, type_wf (TList t) -> type_wf t.
Proof.
  intros. invert_type_wf; auto.
Qed.

Lemma invert_TBag_wf: forall t, type_wf (TBag t) -> type_wf t.
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

Create HintDb fiat2_hints.
#[export] Hint Resolve type_of__type_wf : fiat2_hints.
#[export] Hint Resolve invert_TList_wf : fiat2_hints.
#[export] Hint Resolve invert_TBag_wf : fiat2_hints.
#[export] Hint Resolve invert_TOption_wf : fiat2_hints.
#[export] Hint Resolve invert_TDict_wf_l : fiat2_hints.
#[export] Hint Resolve invert_TDict_wf_r : fiat2_hints.
#[export] Hint Resolve invert_TRecord_wf : fiat2_hints.
#[export] Hint Resolve tenv_wf_step : fiat2_hints.
#[export] Hint Resolve locals_wf_step : fiat2_hints.
#[export] Hint Resolve type_sound : fiat2_hints.

Ltac invert_pair :=
  lazymatch goal with
    H: _ = (_, _) |- _ => inversion H; subst; clear H
  end.

Ltac invert_pair2 :=
  lazymatch goal with
  | H: (_,_) = (_, _) |- _ => inversion H; subst; clear H
  end.

Ltac invert_cons :=
  lazymatch goal with H: _ :: _ = _ :: _ |- _ => inversion H; subst end.

Ltac invert_type_of_op :=
  lazymatch goal with
  | H: type_of_unop _ _ _ |- _ => inversion H; subst
  | H: type_of_binop _ _ _ _ |- _ => inversion H; subst
  | H: type_of_ternop _ _ _ _ _ |- _ => inversion H; subst
  end.

Ltac invert_type_of_op_clear :=
  lazymatch goal with
  | H: type_of_unop _ _ _ |- _ => inversion H; subst; clear H
  | H: type_of_binop _ _ _ _ |- _ => inversion H; subst; clear H
  | H: type_of_ternop _ _ _ _ _ |- _ => inversion H; subst; clear H
  end.

Ltac invert_type_of_atom :=
  lazymatch goal with
    H: type_of_atom _ _ |- _ => inversion H; subst end.

Ltac invert_type_of :=
  lazymatch goal with
  | H: type_of _ _ (_ _) _ |- _ => inversion H; subst end.

Ltac invert_type_of_clear :=
  lazymatch goal with
  | H: type_of _ _ (_ _) _ |- _ => inversion H; clear H; subst end.

Ltac invert_well_typed :=
  lazymatch goal with
  | H: well_typed _ _ (_ _) |- _ => inversion H; subst
  | H: well_typed _ _ _ |- _ => inversion H; subst end.

Ltac apply_type_sound e :=
  lazymatch goal with
    H: type_of _ _ e _ |- _ =>
      let H' := fresh "H'" in
      eapply type_sound in H as H'; eauto
  end.

Ltac apply_type_sound2 e :=
  lazymatch goal with
  | H:type_of _ _ e _ |- context[interp_expr _ ?env0 e] =>
      let H' := fresh "H'" in
      eapply type_sound with (env:=env0) in H as H'; eauto
  end.

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

Ltac destruct_match_hyp :=
  lazymatch goal with
    H: context[match ?x with _ => _ end] |- _ =>
      let E := fresh "E" in
      destruct x eqn:E end.

Ltac clear_refl := lazymatch goal with H: ?x = ?x |- _ => clear H end.

Ltac rewrite_l_to_r :=
  lazymatch goal with
  | H: ?x = _, H': context[?x] |- _ => rewrite H in H'
  | H: ?x = _ |- context[?x] => rewrite H
  end.

Ltac rewrite_r_to_l :=
  lazymatch goal with
  | H: _ = ?x, H': context[?x] |- _ => rewrite <- H in H'
  | H: _ = ?x |- context[?x] => rewrite <- H
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

Ltac destruct_String_eqb x y :=
  let E := fresh "E" in
  destruct (String.eqb x y) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.

Ltac destruct_get_put_strings :=
  lazymatch goal with
  | |- context[map.get(map.put _ ?x _) ?y] =>
      destruct_String_eqb x y;
      repeat rewrite_map_get_put_hyp; repeat rewrite_map_get_put_goal
  | _: context[map.get(map.put _ ?x _) ?y] |- _ =>
      destruct_String_eqb x y;
      repeat rewrite_map_get_put_hyp
  end.

Ltac case_match_string_eqb :=
  case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
  rewrite_map_get_put_hyp; auto.

Ltac destruct_get_update_strings :=
  lazymatch goal with
  | |- context[map.get(map.update _ ?x _) ?y] =>
      destruct_String_eqb x y;
      [ rewrite Properties.map.get_update_same
      | rewrite Properties.map.get_update_diff]; auto
  end.

Ltac do_injection :=
  lazymatch goal with
    H: ?c _ = ?c _ |- _ => injection H; intros; subst
  end.

Ltac apply_Forall_In :=
  lazymatch goal with
    H: Forall _ ?l, _: In _ ?l |- _ =>
      eapply List.Forall_In in H; eauto end.

Ltac invert_Forall :=
  lazymatch goal with
  | H: Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  end.

Ltac invert_Forall2 :=
  lazymatch goal with
  | H: Forall2 _ (_ :: _) _ |- _ => inversion H; subst; clear H
  | H: Forall2 _ _ (_ :: _) |- _ => inversion H; subst; clear H
  | H: Forall2 _ _ _ |- _ => inversion H; subst; clear H
  end.

Ltac invert_NoDup :=
  lazymatch goal with H: NoDup (_ :: _) |- _ => inversion H; subst end.

Ltac invert_SSorted :=
  lazymatch goal with
  | H: StronglySorted _ (_ :: _) |- _ => inversion H; subst
  end.

Ltac resolve_locals_wf :=
  repeat apply locals_wf_step;
  try multimatch goal with H: locals_wf _ _ |- _ => apply H end.

Ltac destruct_In :=
  lazymatch goal with
    H: In _ (_ :: _) |- _ => destruct H; subst end.

Ltac destruct_exists :=
  lazymatch goal with
    H: exists _, _ |- _ => destruct H end.

Ltac destruct_and :=
  lazymatch goal with
    H: _ /\ _ |- _ => destruct H end.

Ltac destruct_or :=
  lazymatch goal with
    H: _ \/ _ |- _ => destruct H
  end.

Ltac apply_tenv_wf :=
  lazymatch goal with
    H: tenv_wf ?G, H': map.get ?G _ = Some ?t |- _ =>
      apply H in H' end.

Ltac apply_locals_wf l :=
  lazymatch goal with H: locals_wf ?G l, H': map.get ?G _ = Some _ |- _ =>
                        let H'' := fresh in
                        apply H in H' as H'' end.

Ltac apply_value_eqb_eq :=
  lazymatch goal with
    H: value_eqb _ _ = _ |- _ =>
      apply value_eqb_eq in H; subst
  end.

Ltac rewrite_expr_value :=
  multimatch goal with
  | H: VList _ = interp_expr _ _ _ |- _ => rewrite <- H in *
  | H: VBool _ = interp_expr _ _ _ |- _ => rewrite <- H in *
  | H: VRecord _ = interp_expr _ _ _ |- _ => rewrite <- H in *
  | H: VDict _ = interp_expr _ _ _ |- _ => rewrite <- H in *
  | H: VOption _ = interp_expr _ _ _ |- _ => rewrite <- H in *
  | H: interp_expr _ _ _ = VList _ |- _ => rewrite H in *
  | H: interp_expr _ _ _ = VBool _ |- _ => rewrite H in *
  | H: interp_expr _ _ _ = VRecord _ |- _ => rewrite H in *
  | H: interp_expr _ _ _ = VDict _ |- _ => rewrite H in *
  | H: interp_expr _ _ _ = VOption _ |- _ => rewrite H in * end.

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

Ltac do_injection2 := iter_hyps do_injection'.

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
  | tag : collection_tag |- _ => destruct tag; auto; []
  | ag : aggr |- _ => destruct ag; auto; []
  end.

Ltac Forall_fst__Forall_bag_to_list :=
  lazymatch goal with
  | H: context[fun p => type_of_value (fst p) ?t] |- _ =>
      erewrite (Forall_map_fst _ _ _ (fun v => type_of_value v t)) in H;
      eapply incl_Forall in H;
      [ | apply bag_to_list_incl ]
  | |- Forall (fun p => type_of_value _ ?t) _ =>
      erewrite (Forall_map_fst _ _ _
                  (fun v => type_of_value v t));
      eapply incl_Forall; eauto using list_to_bag_incl
  end.

Definition size_of_map {key value map} (m : @map.rep key value map) :=
  map.fold (fun n _ _ => S n) O m.

Definition mmap {k v1 v2} {map1 : map.map k v1} {map2 : map.map k v2}
  (f : v1 -> v2) (m : map1) : map2 :=
  map.fold (fun m k v => map.put m k (f v)) map.empty m.

Lemma get_mmap : forall vt vt' (mt : map.map string vt) (mt_ok : map.ok mt)
                        (mt' : map.map string vt') (mt'_ok : map.ok mt')
                        (m : mt) (f : vt -> vt') k,
    map.get (mmap f m) k = option_map f (map.get m k).
Proof.
  intros. unfold mmap. apply map.fold_spec.
  1: rewrite !map.get_empty; trivial.
  intros. destruct_String_eqb k0 k; repeat rewrite_map_get_put_goal.
  auto.
Qed.

Lemma mmap_put : forall vt vt' (mt : map.map string vt) (mt_ok : map.ok mt)
                        (mt' : map.map string vt') (mt'_ok : map.ok mt')
                        (m : mt) k v (f : vt -> vt'),
    mmap f (map.put m k v) = map.put (mmap f m) k (f v).
Proof.
  intros. apply map.map_ext; intro x.
  rewrite get_mmap; auto.
  destruct_String_eqb k x; repeat rewrite_map_get_put_goal; simpl; auto.
  rewrite get_mmap; auto.
Qed.

Lemma mmap_update : forall vt vt' (mt : map.map string vt) (mt_ok : map.ok mt)
                           (mt' : map.map string vt') (mt'_ok : map.ok mt')
                           (m : mt) k v (f : vt -> vt'),
    mmap f (map.update m k v) = map.update (mmap f m) k (option_map f v).
Proof.
  intros. apply map.map_ext; intro x.
  rewrite get_mmap; auto.
  destruct_String_eqb k x.
  1: rewrite !Properties.map.get_update_same; reflexivity.
  1:{ rewrite !Properties.map.get_update_diff; auto.
      rewrite get_mmap; auto. }
Qed.

Lemma put_update_same : forall vt (mt : map.map string vt) {mt_ok : map.ok mt}
                               (m : mt) k v v',
    map.put (map.update m k v) k v' = map.put m k v'.
Proof.
  intros; apply map.map_ext; intro x.
  destruct_get_put_strings; auto.
  destruct_get_update_strings; intuition idtac.
Qed.

Lemma update_put_diff : forall (vt : Type) (mt : map.map string vt),
    map.ok mt -> forall (m : mt) (k k' : string) (v : vt) (v' : option vt),
      k <> k' ->
      map.update (map.put m k v) k' v' = map.put (map.update m k' v') k v.
Proof.
  intros. apply map.map_ext; intro x.
  destruct_get_put_strings.
  1: rewrite Properties.map.get_update_diff, map.get_put_same; auto.
  destruct_String_eqb x k'.
  1: rewrite !Properties.map.get_update_same; auto.
  1: rewrite !Properties.map.get_update_diff, map.get_put_diff; auto.
Qed.

Lemma In_find_some : forall A A_eqb a (l : list A),
    (forall a, A_eqb a a = true) ->
    In a l ->
    match find (A_eqb a) l with
    | Some _ => True
    | None => False
    end.
Proof.
  intros * H_refl. induction l; simpl; auto; intros.
  intuition auto.
        1: subst; rewrite H_refl; auto.
        1: case_match; auto.
Qed.

Lemma not_In_find_none : forall A A_eqb a (l : list A),
    (forall a a', A_eqb a a' = true -> a = a') ->
    ~ In a l -> find (A_eqb a) l = None.
Proof.
  intros * H_eq. induction l; simpl; auto; intros.
  intuition auto. case_match; auto.
  apply H_eq in E; congruence.
Qed.

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

Lemma In_flat_map_ext : forall A B l (f : A -> list B) g,
    (forall a, In a l -> f a = g a) ->
    flat_map f l = flat_map g l.
Proof.
  induction l; simpl; intuition. f_equal; auto.
Qed.

Lemma In_fold_right_ext' : forall A B a l (f : B -> A -> A) g P,
    P a ->
    (forall a b, P a -> In b l -> f b a = g b a /\ P (f b a)) ->
    fold_right f a l = fold_right g a l /\ P (fold_right f a l).
Proof.
  intros. induction l as [| b l]; auto.
  simpl. split.
  - assert (H' : fold_right f a l = fold_right g a l).
    { apply IHl. intros a' b' H_a' H_b'. apply H0; intuition. }
    rewrite H'. apply H0; intuition. rewrite <- H'; apply IHl.
    intros. apply H0; intuition.
  - apply H0; intuition. apply IHl. intros. apply H0; intuition.
Qed.

Lemma In_fold_right_ext : forall A B a l (f : B -> A -> A) g P,
    P a ->
    (forall a b, P a -> In b l -> f b a = g b a /\ P (f b a)) ->
    fold_right f a l = fold_right g a l.
Proof.
  apply In_fold_right_ext'.
Qed.

Lemma flat_map_eq : forall A B (f : A -> list B) g l, Forall (fun x => f x = g x) l -> flat_map f l = flat_map g l.
Proof.
  intros. induction H; auto.
  simpl; congruence.
Qed.

Lemma flat_map_filter : forall A B (f : A -> list B) g l,
    flat_map f (filter g l) = flat_map (fun v => if g v then f v else nil) l.
Proof.
  induction l; auto; simpl.
  destruct (g a); auto. simpl. rewrite IHl; auto.
Qed.

Lemma Forall2_eq : forall A (l l' : list A), Forall2 eq l l' <-> l = l'.
Proof.
  split; intros.
  1: induction H; congruence.
  1: subst; induction l'; auto.
Qed.

Lemma In_filter_ext : forall A (l : list A) f g, (forall x, In x l -> f x = g x) -> filter f l = filter g l.
Proof.
  induction l; intuition.
  simpl. rewrite H; intuition.
  erewrite IHl; eauto. intuition.
Qed.

Lemma Forall_false__filter : forall A f (l : list A), Forall (fun x => f x = false) l -> filter f l = nil.
Proof.
  intros * H; induction l; simpl; auto. simpl in H.
  inversion H; subst. rewrite H2. auto.
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

Lemma dedup_preserve_Permutation : forall A A_eqb (l l' : list A),
    (forall a a', A_eqb a a' = true -> a = a') ->
    (forall a, A_eqb a a = true) ->
    (forall a a', A_eqb a a' = A_eqb a' a) ->
    Permutation l l' ->
    Permutation (List.dedup A_eqb l) (List.dedup A_eqb l').
Proof.
  intros * H_eq H_refl H_sym. induction 1; simpl; auto.
  1:{ case_match.
      1:{ apply find_some in E as [HL HR]; apply H_eq in HR; subst;
          eapply Permutation_in in HL; eauto.
          eapply In_find_some in HL; eauto.
          destruct_match_hyp; intuition auto. }
      1:{ specialize (find_none _ _ E x); intros. rewrite not_In_find_none; auto.
          intro contra. eapply Permutation_in in contra.
          2: apply Permutation_sym; eauto.
          intuition auto. congruence. } }
  1:{ rewrite H_sym. case_match.
      1:{ apply H_eq in E; subst. case_match; auto. }
      1:{ repeat case_match; auto. apply perm_swap. } }
  1: eapply perm_trans; eauto.
Qed.

Definition domain_incl {vt1 vt2 : Type} {m1 : map.map string vt1} {m2 : map.map string vt2}
    (G1 : m1) (G2 : m2) :=
    forall x, match map.get G1 x with
              | Some _ => match map.get G2 x with
                          | Some _ => True
                          | None => False
                          end
              | None => True
              end.

Definition domain_eq {vt1 vt2 : Type} {m1 : map.map string vt1} {m2 : map.map string vt2}
  (G1 : m1) (G2 : m2) :=
  domain_incl G1 G2 /\ domain_incl G2 G1.

Lemma domain_incl_refl : forall {vt : Type} {m : map.map string vt} (G : m),
    domain_incl G G.
Proof.
  unfold domain_incl; intros. case_match; auto.
Qed.

Lemma domain_incl_tran : forall {vt1 vt2 vt3: Type} {m1 : map.map string vt1}
                                {m2 : map.map string vt2} {m3 : map.map string vt3}
                                (G1 : m1) (G2 : m2) (G3 : m3),
    domain_incl G1 G2 -> domain_incl G2 G3 ->
    domain_incl G1 G3.
Proof.
  unfold domain_incl; intros * H1 H2 x.
  specialize (H1 x); specialize (H2 x).
  repeat destruct_match_hyp; intuition idtac.
Qed.

Lemma domain_eq_refl : forall {vt : Type} {m : map.map string vt} (G : m),
    domain_eq G G.
Proof.
  unfold domain_eq; auto using domain_incl_refl.
Qed.

Lemma domain_eq_sym : forall {vt1 vt2 : Type} {m1 : map.map string vt1} {m2 : map.map string vt2}
                             (G1 : m1) (G2 : m2),
    domain_eq G1 G2 -> domain_eq G2 G1.
Proof.
  unfold domain_eq; intuition auto.
Qed.

Lemma domain_eq_tran : forall {vt1 vt2 vt3: Type} {m1 : map.map string vt1}
                              {m2 : map.map string vt2} {m3 : map.map string vt3}
                              (G1 : m1) (G2 : m2) (G3 : m3),
    domain_eq G1 G2 -> domain_eq G2 G3 ->
    domain_eq G1 G3.
Proof.
  unfold domain_eq; intuition eauto using domain_incl_tran.
Qed.

Lemma domain_incl_empty : forall {vt1 vt2 : Type} {m1 : map.map string vt1}
                                 {m1_ok : map.ok m1}
                                 {m2 : map.map string vt2} (G : m2),
    domain_incl (map.empty (map:=m1)) G.
Proof.
  unfold domain_incl; intros.
  rewrite map.get_empty; auto.
Qed.


Section WithWord.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value_eqb := (value_eqb (word:=word)).

  Lemma value_eqb_refl : forall (v : value), value_eqb v v = true.
  Proof.
    unfold value_eqb. intro; rewrite value_compare_refl; auto.
  Qed.

  Lemma value_eqb_neq : forall (x y : value), value_eqb x y = false -> x <> y.
  Proof.
    intros; intro; subst. rewrite value_eqb_refl in *; congruence.
  Qed.

  Lemma value_eqb_dec : forall (x y : value), BoolSpec (x = y) (x <> y) (value_eqb x y).
    intros. destruct (value_eqb x y) eqn:E.
    1: constructor; auto using value_eqb_eq.
    1: constructor. 1: auto using value_eqb_neq.
  Qed.

  Lemma NoDup_dedup_value_eqb : forall (l : list value), NoDup (List.dedup value_eqb l).
  Proof.
    induction l; simpl.
    1: apply NoDup_nil.
    case_match; trivial. constructor; auto.
    intro H. apply dedup_In in H. apply (find_none _ _ E) in H.
    rewrite value_eqb_refl in *; discriminate.
  Qed.

  Local Coercion is_true : bool >-> Sortclass.

  Lemma NoDup_SSorted__Lt : forall (k v : value) d,
      NoDup (k :: List.map fst d) ->
      StronglySorted dict_entry_leb ((k, v) :: d) ->
      forall p, In p d -> value_compare (word:=word) k (fst p) = Lt.
  Proof.
    intros. invert_NoDup; invert_SSorted. destruct p; simpl.
    apply_Forall_In; unfold dict_entry_leb in *; simpl in *.
    unfold value_leb, leb_from_compare in *.
    lazymatch goal with |- ?x = _ => destruct x eqn:E end; try congruence.
    apply value_compare_Eq_eq in E; subst. apply in_map with (f:=fst) in H1; intuition.
  Qed.

  Lemma dict_lookup_Lt : forall d k,
      StronglySorted dict_entry_leb d ->
      (forall p, In p d -> value_compare k (fst p) = Lt) ->
      dict_lookup (word:=word) k d = None.
  Proof.
    intros. induction d; auto.
    simpl. destruct a; simpl in *.
    case_match.
    - unfold value_eqb in *. pose proof (H0 (v, v0)).
      intuition; simpl in *. rewrite H1 in E; discriminate.
    - apply IHd; inversion H; auto.
  Qed.

  Lemma not_In__dict_lookup : forall (v : value) d, ~ In v (List.map fst d) -> dict_lookup (word:=word) v d = None.
  Proof.
    intros * H. induction d; simpl; auto.
    destruct a; simpl in *. intuition. case_match; auto.
    apply value_eqb_eq in E; subst; intuition.
  Qed.

  Lemma not_In__dict_delete : forall (k : value) d, ~ In k (List.map fst d) -> dict_delete (word:=word) k d = d.
  Proof.
    induction d; intros; simpl; auto.
    destruct a; case_match; simpl in *.
    1:apply value_eqb_eq in E; subst; intuition.
    f_equal. auto.
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
      + constructor; auto. rewrite Forall_forall in *; intros. destruct x.
        unfold dict_entry_leb, value_leb, leb_from_compare in *; simpl in *.
        destruct_or.
        * invert_pair2; rewrite E; auto.
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
End WithWord.


Definition map_incl {key value : Type} {map : map.map key value} (m m' : map) : Prop :=
  forall k v, map.get m k = Some v -> map.get m' k = Some v.

Lemma map_incl_refl : forall {key value : Type} {map : map.map key value}
                             (m : map), map_incl m m.
Proof.
  unfold map_incl; intros. assumption.
Qed.

Lemma map_incl_empty : forall {key value : Type} {map : map.map key value} {map_ok : map.ok map}
                              (m : map), map_incl map.empty m.
Proof.
  unfold map_incl; intros. rewrite map.get_empty in H; congruence.
Qed.

Lemma map_incl_step : forall {kt vt : Type} {m : map.map kt vt} {m_ok : map.ok m}
                             (H_dec: forall k1 k2 : kt, {k1 = k2} + {k1 <> k2}) (G G' : m) k v,
    map_incl G G' -> map_incl (map.put G k v) (map.put G' k v).
Proof.
  unfold map_incl; intros.
  destruct (H_dec k k0); subst.
  1: rewrite map.get_put_same in *; auto.
  1: rewrite map.get_put_diff in *; auto.
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

Lemma map_incl_step_r : forall {A : Type} {map : map.map string A} {map_ok : map.ok map}
                               k v (m m' : map),
    map_incl m m' -> map.get m k = None -> map_incl m (map.put m' k v).
Proof.
  unfold map_incl; intros.
  destruct_get_put_strings; congruence.
Qed.

Lemma In_length_le_max : forall x l,
    In x l -> le (String.length x) (list_max (List.map String.length l)).
Proof.
  induction l; simpl; intros; intuition auto.
  1:{ subst. apply Nat.le_max_l. }
  1:{ eapply Nat.le_trans; eauto. apply Nat.le_max_r. }
Qed.

Lemma string_app_length : forall x y,
    String.length (x ++ y) = String.length x + String.length y.
Proof.
  induction x; simpl; auto.
Qed.

Lemma add_l_le : forall m n p, m + n <= p -> n <= p.
Proof.
  induction 1; intuition auto with *.
Qed.

Lemma incl_cons_step : forall A l l' (x : A), incl l l' -> incl (x :: l) (x :: l').
Proof.
  unfold incl; intros. destruct_In.
  1: constructor; auto.
  1: auto using in_cons.
Qed.

Lemma SSorted_app_cons : forall A (P : A -> A -> Prop) l a l',
    StronglySorted P (l ++ a :: l') ->
    StronglySorted P (l ++ l').
Proof.
  induction l; simpl; intros.
  1: apply StronglySorted_inv in H; intuition fail.
  invert_SSorted. constructor.
  1: eapply IHl; eauto.
  rewrite Forall_app in *; intuition idtac.
  invert_Forall; auto.
Qed.

Section WithMap.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Lemma tenv_wf_empty : tenv_wf map.empty.
  Proof.
    unfold tenv_wf; intros. rewrite map.get_empty in H; congruence.
  Qed.

  Lemma locals_wf_empty : forall (l : locals), locals_wf map.empty l.
  Proof.
    unfold locals_wf; intros. rewrite map.get_empty in *; congruence.
  Qed.

  Ltac apply_type_of_strengthen_IH :=
    lazymatch goal with
      IH: context[_ -> type_of _ _ ?e _] |- type_of _ _ ?e _ =>
        apply IH end.

  Lemma type_of_strengthen : forall e (Gstore Genv: tenv) t,
      type_of Gstore Genv e t ->
      forall (Gstore' Genv' : tenv),
        map_incl Gstore Gstore' -> map_incl Genv Genv' ->
        type_of Gstore' Genv' e t.
  Proof.
    induction 1 using type_of_IH; simpl; intros.
    all: econstructor; eauto.
    all: try (apply_type_of_strengthen_IH; auto;
              repeat apply map_incl_step; auto using string_dec).
    eapply Forall2_impl; [ | eauto ]; auto.
  Qed.

  Lemma locals_wf_step_r : forall G (l : locals) x v,
      locals_wf G l -> map.get G x = None ->
      locals_wf G (map.put l x v).
  Proof.
    unfold locals_wf; intros.
    destruct_get_put_strings; try congruence.
    apply H in H1. auto.
  Qed.

  Definition locals_equiv (G : tenv) (l l' : locals) : Prop :=
    forall x t, map.get G x = Some t ->
                map.get l x = map.get l' x.

  Lemma locals_equiv_refl : forall G l, locals_equiv G l l.
  Proof.
    unfold locals_equiv. auto.
  Qed.

  Lemma locals_equiv_step : forall G l l' x t v v',
      locals_equiv G l l' ->
      v = v' ->
      locals_equiv (map.put G x t) (map.put l x v) (map.put l' x v').
  Proof.
    unfold locals_equiv; intros.
    destruct_get_put_strings; eauto.
  Qed.

  Lemma locals_equiv__put_fresh : forall G l x v,
      map.get G x = None -> locals_equiv G l (map.put l x v).
  Proof.
    unfold locals_equiv. intros. rewrite_map_get_put_goal. congruence.
  Qed.

  Lemma locals_equiv_sym : forall G l l',
      locals_equiv G l l' -> locals_equiv G l' l.
  Proof.
    unfold locals_equiv; intros.
    symmetry; eauto.
  Qed.

  Lemma locals_equiv_tran : forall G l l' l'',
      locals_equiv G l l' -> locals_equiv G l' l'' -> locals_equiv G l l''.
  Proof.
    unfold locals_equiv; intros.
    erewrite H; eauto.
  Qed.

  #[local] Hint Resolve locals_equiv_step : fiat2_hints.

  Ltac apply_locals_equiv :=
    lazymatch goal with
    | H: locals_equiv ?G _ _, H': map.get ?G _ = Some _ |- _ =>
        apply H in H' end.

  Lemma In_flat_map2_ext : forall (A B C : Type) (l : list A) (l' : list B) (f g : A -> B -> list C),
      (forall a b, In a l -> In b l' -> f a b = g a b) -> flat_map2 f l l' = flat_map2 g l l'.
  Proof.
    induction l; auto.
    destruct l'; auto.
    cbn; intros. rewrite H; auto.
    f_equal. erewrite IHl; eauto.
  Qed.

  Ltac use_interp_expr__locals_equiv_IH :=
    lazymatch goal with
      IH: context[interp_expr _ _ ?e] |- context[interp_expr _ _ ?e] =>
        erewrite IH; clear IH end.

  Lemma interp_expr__locals_equiv : forall e Gstore Genv t,
      tenv_wf Gstore -> tenv_wf Genv ->
      type_of Gstore Genv e t ->
      forall (store env store' env' : locals),
        locals_wf Gstore store -> locals_wf Genv env ->
        locals_equiv Gstore store store' -> locals_equiv Genv env env' ->
        interp_expr store' env' e = interp_expr store env e.
  Proof.
    induction e using expr_IH; simpl; auto; intros.
    all: invert_type_of.
    1,2: unfold get_local; apply_locals_equiv; rewrite_l_to_r; auto.
    all: try now (repeat (use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto)).
    1:{ revert IHe2. use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; intros;
        eauto using locals_equiv_refl with fiat2_hints.
        use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ];
          eauto using locals_equiv_refl with fiat2_hints. }
    1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
        apply_type_sound e1; invert_type_of_value. f_equal.
        apply In_flat_map_ext; intros; apply_Forall_In.
        use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints. }
    1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
        apply_type_sound e1; invert_type_of_value. do 2 f_equal.
        apply In_flat_map_ext; intros.
        Forall_fst__Forall_bag_to_list. apply_Forall_In.
        use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints. }
    1:{ repeat (use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto).
        apply_type_sound e1; invert_type_of_value.
        apply_type_sound e2; invert_type_of_value.
        f_equal.
        apply In_flat_map2_ext; intros. repeat apply_Forall_In.
        use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ];
          try apply tenv_wf_step; try apply locals_wf_step; eauto with fiat2_hints. }
    1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
        apply_type_sound e1; invert_type_of_value.
        revert IHe3. use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto; intros.
        eapply In_fold_right_ext with (P:=fun v => type_of_value v t); intros.
        1: apply_type_sound e2.
        1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints.
            2: repeat apply tenv_wf_step; eauto with fiat2_hints.
            2: repeat apply locals_wf_step; apply_Forall_In; intuition auto.
            apply_type_sound e3;
              [ repeat apply tenv_wf_step; eauto with fiat2_hints
              | repeat apply locals_wf_step; apply_Forall_In; intuition auto ]. } }
    1:{ do 2 f_equal. lazymatch goal with
        H1: type_of _ _ _ _, H2: Permutation _ _, H3: NoDup _, H4: List.map fst _ = _ |- _ =>
          clear H1 H2 H3 H4 end.
        generalize dependent tl; induction l; simpl; auto; intros. case_match.
        destruct tl; invert_Forall; invert_Forall2; simpl in *. f_equal.
        1: f_equal; use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
        1: eapply IHl; eauto. }
    1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
        apply_type_sound e1; invert_type_of_value.
        all: use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints. }
    1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
        apply_type_sound e1; invert_type_of_value.
        revert IHe3. use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto; intros.
        eapply In_fold_right_ext with (P:=fun v => type_of_value v t); intros.
        1: apply_type_sound e2.
        1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints.
            2: repeat apply tenv_wf_step; eauto with fiat2_hints.
            2: repeat apply locals_wf_step; apply_Forall_In; intuition auto.
            apply_type_sound e3;
              [ repeat apply tenv_wf_step; eauto with fiat2_hints
              | repeat apply locals_wf_step; apply_Forall_In; intuition auto ]. } }
    1,2: use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto;
        apply_type_sound e1; invert_type_of_value;
        f_equal; apply In_filter_ext; auto; intros; apply_Forall_In;
        use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints.
    1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
        apply_type_sound e1; invert_type_of_value.
        use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
        apply_type_sound e2; invert_type_of_value.
        f_equal. apply In_flat_map_ext; intros. apply_Forall_In.
        erewrite In_filter_ext; eauto.
        2:{ intros. apply_Forall_In.
            use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints.
            1: reflexivity.
            repeat apply tenv_wf_step; eauto with fiat2_hints. }
        apply map_ext_in; intros.
        lazymatch goal with H: In _ (filter _ _) |- _ => apply filter_In in H; intuition auto end.
        apply_Forall_In.
        use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints.
        repeat apply tenv_wf_step; eauto with fiat2_hints. }
    1:{  use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
        apply_type_sound e1; invert_type_of_value.
        use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
        apply_type_sound e2; invert_type_of_value.
        do 2 f_equal. apply In_flat_map_ext; intros.
        repeat Forall_fst__Forall_bag_to_list. apply_Forall_In.
        erewrite In_filter_ext; eauto.
        2:{ intros. apply_Forall_In.
            use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints.
            1: reflexivity.
            repeat apply tenv_wf_step; eauto with fiat2_hints. }
        apply map_ext_in; intros.
        lazymatch goal with H: In _ (filter _ _) |- _ => apply filter_In in H; intuition auto end.
        apply_Forall_In.
        use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints.
        repeat apply tenv_wf_step; eauto with fiat2_hints. }
    1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
        apply_type_sound e1; invert_type_of_value.
        f_equal. apply map_ext_in; intros. apply_Forall_In.
        use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints. }
    1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
        apply_type_sound e1; invert_type_of_value.
        do 2 f_equal. apply map_ext_in; intros.
        Forall_fst__Forall_bag_to_list. apply_Forall_In.
        use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints. }
  Qed.

  Lemma map_incl__locals_equiv : forall G l l',
      locals_wf G l -> map_incl l l' -> locals_equiv G l l'.
  Proof.
    unfold locals_wf, map_incl, locals_equiv. intros * H_wf H_incl * H.
    apply H_wf in H. destruct_match_hyp; intuition auto.
    apply H_incl in E. congruence.
  Qed.

  Lemma interp_expr_strengthen : forall e Gstore Genv t,
      tenv_wf Gstore -> tenv_wf Genv ->
      type_of Gstore Genv e t ->
      forall (store env store' env' : locals),
        locals_wf Gstore store -> locals_wf Genv env ->
        map_incl store store' -> map_incl env env' ->
        interp_expr store' env' e = interp_expr store env e.
  Proof.
    intros.
    eapply interp_expr__locals_equiv; [ | | eauto | .. ]; auto using map_incl__locals_equiv.
  Qed.

  Lemma stores_eq_except__update_eq : forall (store store' : locals) tbl v,
      (forall x, x <> tbl -> map.get store x = map.get store' x) ->
      map.update store tbl v = map.update store' tbl v.
  Proof.
    intros. apply map.map_ext. intros.
    destruct_String_eqb k tbl.
    1: repeat rewrite Properties.map.get_update_same; reflexivity.
    1: repeat rewrite Properties.map.get_update_diff; auto.
  Qed.

  Lemma command_preserve_untouched_store : forall c (Gstore Genv :tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv ->
      well_typed Gstore Genv c ->
      locals_wf Gstore store -> locals_wf Genv env ->
      forall x, map.get Gstore x = None ->
                map.get (interp_command store env c) x = map.get store x.
  Proof.
    induction c; simpl; auto; intros.
    all: invert_well_typed.
    1:{ erewrite IHc2. 4: eauto. all: auto.
        2: eapply command_type_sound; eauto.
        eapply IHc1. 4: eauto. all: eauto. }
    1:{ erewrite IHc. 4: eauto. all: eauto with fiat2_hints. }
    1:{ destruct_String_eqb x0 x.
        1: rewrite Properties.map.get_update_same; reflexivity.
        1: rewrite Properties.map.get_update_diff; auto.
        erewrite IHc. 4: eauto. all: eauto with fiat2_hints.
        all: rewrite_map_get_put_goal. }
    1:{ destruct_get_put_strings; try congruence. }
    1:{ case_match; auto. case_match; subst; eauto. }
    1:{ apply_type_sound e. invert_type_of_value.
        lazymatch goal with H: VList _ = _ |- _ => clear H end.
        generalize dependent store. induction l; simpl; auto; intros.
        rewrite IHl; auto; invert_Forall.
        1: eapply IHc. 3: eauto. all: eauto with fiat2_hints.
        1: eapply command_type_sound; eauto with fiat2_hints.
        1:{ apply_type_sound e. eapply command_type_sound; eauto with fiat2_hints. }}
  Qed.

  Local Ltac unfold_typechecker :=
    lazymatch goal with
    | H: synthesize_expr _ _ _ = Success _ |- _ => unfold synthesize_expr in H
    | H: analyze_expr _ _ _ _ = Success _ |- _ => unfold analyze_expr in H
    end.

  Local Ltac unfold_fold_typechecker := repeat unfold_typechecker; fold synthesize_expr in *; fold analyze_expr in *.

  Lemma synthesizable_atom_ty_unique : forall a a' t t',
            type_of_atom a t ->
            synthesize_atom a = Success (t', a') ->
            t = t'.
  Proof.
    destruct a; simpl; intros.
    all: invert_type_of_atom; try congruence.
    all: destruct_match_hyp; try congruence.
  Qed.

  Ltac apply_typechecker_sound :=
    lazymatch goal with
      H: synthesize_expr _ _ _ = Success _ |- _ =>
        eapply typechecker_sound in H
    end.

  Ltac use_synthesize_ty_unique_IH :=
    lazymatch goal with
    | IH: ?x -> ?y -> forall _ _, Success (?t, ?e) = _ -> _,
    H1: ?x, H2: ?y |- _ => specialize (IH H1 H2 e t eq_refl)
    | IH: context[synthesize_expr _ _ ?e = _ -> _ = _],
        H: synthesize_expr _ _ ?e = _ |- _ => eapply IH end.

  Lemma synthesizable_ty_unique : forall Gstore Genv e t,
      type_of Gstore Genv e t ->
      tenv_wf Gstore -> tenv_wf Genv ->
      forall e' t',
      synthesize_expr Gstore Genv e = Success (t', e') ->
      t = t'.
  Proof.
    induction 1 using type_of_IH; simpl; intros.
    1,2: apply_typechecker_sound; auto;
    invert_type_of; congruence.
    all: unfold_fold_typechecker.
    all: repeat (destruct_match_hyp; try congruence; []).
    1:{ do_injection.
        eapply synthesizable_atom_ty_unique; eauto. }
    1:{ repeat destruct_match_hyp; try congruence;
        simpl in *; try invert_pair2;
        lazymatch goal with
          H: type_of_unop _ _ _ |- _ => inversion H; subst end;
        try do_injection; try reflexivity.
        use_synthesize_ty_unique_IH; congruence. }
    1:{ repeat destruct_match_hyp; try congruence;
        simpl in *; try invert_pair2;
        lazymatch goal with
          H: type_of_binop _ _ _ _ |- _ => inversion H; subst end;
        try do_injection; try reflexivity;
        use_synthesize_ty_unique_IH; congruence. }
    all: try now (repeat destruct_match_hyp; try congruence;
                  try do_injection;
                  repeat (use_synthesize_ty_unique_IH; eauto with fiat2_hints);
                  try congruence; repeat (try clear_refl; do_injection); subst; eauto; repeat (try clear_refl; do_injection); try (f_equal; use_synthesize_ty_unique_IH);
                  repeat apply tenv_wf_step; eauto with fiat2_hints).
    1:{ do_injection. inversion H; subst; eauto. }
    1:{ repeat destruct_match_hyp; try congruence;
        try do_injection;
        repeat (use_synthesize_ty_unique_IH; eauto with fiat2_hints);
        lazymatch goal with
          H: type_of_aggr _ _ _ |- _ => inversion H; subst
        end; auto. }
    1:{ generalize dependent tl. generalize dependent tl'.
        generalize dependent t'. revert e'.
        unfold record_type_from in *. induction l; intros.
        1:{ destruct tl; simpl in *; try congruence.
            apply Permutation_nil in H2.
            unfold record_sort, Mergesort.Sectioned.sort in *; simpl in *.
            do_injection2; reflexivity. }
        1:{ invert_Forall2. destruct tl; simpl in *; try congruence.
            invert_cons. invert_Forall2; simpl in *.
            repeat destruct_match_hyp; try congruence.
            simpl in *; do_injection2; invert_pair. repeat clear_refl.
            apply H11 in H8; auto. destruct p; simpl in *; subst.
            apply Permutation_sym, Permutation_vs_cons_inv in H2 as H_p.
            repeat destruct_exists; subst.
            apply Permutation_sym, Permutation_cons_app_inv in H2 as H_p.
            invert_NoDup. invert_cons.
            eapply IHl in H_p; eauto using SSorted_app_cons.
            do_injection2. f_equal.
            eapply Forall2_eq, Forall2_Permuted_StronglySorted.
            4: apply Permutation_refl.
            4:{ pose proof (Permuted_record_sort l2); rewrite_r_to_l.
                eapply perm_trans, Permuted_record_sort.
                eapply perm_trans, perm_skip; [ | apply Permutation_sym; eassumption ].
                apply Permutation_sym, Permutation_middle. }
            1: apply Forall2_eq; auto.
            1: apply (Permutation_map fst), Permutation_NoDup in H2; auto.
            all: intros; subst; auto using StronglySorted_record_sort. } }
  Qed.
End WithMap.

#[export] Hint Resolve tenv_wf_empty : fiat2_hints.
#[export] Hint Resolve locals_wf_empty : fiat2_hints.

Lemma dedup_nil : forall A A_eqb (l : list A),
    List.dedup A_eqb l = nil -> l = nil.
Proof.
  induction l; simpl; auto; intros.
  destruct_match_hyp; try congruence.
  apply find_some in E. intuition auto; subst.
  apply in_nil in H0. intuition auto.
Qed.

Lemma dedup_dedup : forall A A_eqb (l : list A),
    List.dedup A_eqb (List.dedup A_eqb l) = List.dedup A_eqb l.
Proof.
  induction l; simpl; auto.
  case_match; auto. simpl.
  case_match; try congruence.
  apply find_some in E0; intuition auto.
  apply dedup_In in H. eapply find_none in E; eauto. congruence.
Qed.

Lemma find_app_Some : forall A p (l l' : list A) a,
    find p (l ++ l') = Some a ->
    find p l = Some a \/ find p l' = Some a.
Proof.
  induction l; simpl; auto; intros.
  case_match; intuition auto.
Qed.

Lemma find_app_None : forall A p  (l l' : list A),
    find p (l ++ l') = None ->
    find p l = None /\ find p l' = None.
Proof.
  induction l; simpl; auto; intros.
  case_match; try congruence. auto.
Qed.

Lemma dedup_app : forall A A_eqb (l l' : list A),
    (forall x y : A, BoolSpec (x = y) (x <> y) (A_eqb x y)) ->
    List.dedup A_eqb (l ++ l') = List.dedup A_eqb (List.dedup A_eqb l ++ List.dedup A_eqb l').
Proof.
  induction l; simpl; intros.
  1: rewrite dedup_dedup; reflexivity.
  pose proof List.dedup_preserves_In as dedup_preserves_In.
  case_match.
  1:{ apply find_app_Some in E. case_match; auto.
      intuition auto; try congruence. simpl.
      case_match; auto.
      lazymatch goal with H: find _ _ = Some _ |- _ => apply find_some in H end.
      lazymatch goal with H: find _ _ = None |- _ => eapply find_none in H end.
      2:{ apply in_or_app. right. rewrite <- dedup_preserves_In.
          intuition eauto. }
      intuition auto; congruence. }
  1:{ apply find_app_None in E. intuition auto. rewrite_l_to_r.
      simpl. case_match.
      2: rewrite IHl; auto.
      lazymatch goal with H: find _ _ = Some _ |- _ => apply find_some in H end.
      intuition auto.
      lazymatch goal with H: In _ (_ ++ _) |- _ => apply in_app_or in H end.
      rewrite <- !dedup_preserves_In in *. intuition auto;
        lazymatch goal with H: find _ ?l = None, _: In _ ?l |- _ => eapply find_none in H end;
        eauto; congruence. }
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
    assert (H_a_in: In a (a :: l)). { intuition auto with *. } apply H_a in H_a_in as H_p.
    destruct (f a) eqn:E.
    + simpl. apply Permutation_nil in H_p.
      rewrite H_p; simpl. rewrite <- flat_map_app.
      apply Permutation_cons_app_inv in H. intuition auto with *.
    + eapply perm_trans. 2: apply Permutation_app_swap_app.
      apply Permutation_app; auto. rewrite <- flat_map_app. apply IHl.
      2: apply Permutation_cons_app_inv in H.
      all: intuition auto with *.
Qed.

Section WithWord.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Lemma Permutation_dedup_app : forall (l1 l2 l3 l4 : list value),
      Permutation (List.dedup value_eqb l1) (List.dedup value_eqb l2) ->
      Permutation (List.dedup value_eqb l3) (List.dedup value_eqb l4) ->
      Permutation (List.dedup value_eqb (l1 ++ l3)) (List.dedup value_eqb (l2 ++ l4)).
  Proof.
    intros.
    rewrite dedup_app; [ rewrite (dedup_app _ _ l2) | ]; auto using value_eqb_dec.
    apply dedup_preserve_Permutation;
      auto using value_eqb_refl, value_eqb_sym, value_eqb_eq, Permutation_app.
  Qed.

  Lemma fold_right__type_of_value : forall t1 t2 l (acc0 : value) f,
      Forall (fun v : value => type_of_value v t1) l ->
      type_of_value acc0 t2 ->
      (forall v acc, type_of_value v t1 -> type_of_value acc t2 ->
                     type_of_value (f v acc) t2) ->
      type_of_value (fold_right f acc0 l) t2.
  Proof.
    induction l; simpl; auto; intros.
    invert_Forall. apply H1; auto.
  Qed.

  Lemma Permutation_SSorted_eq : forall (l l' : list value),
      Permutation l l' ->
      Sorted.StronglySorted (fun v v' => is_true (value_leb v v')) l ->
      Sorted.StronglySorted (fun v v' => is_true (value_leb v v')) l' ->
      l = l'.
  Proof.
    induction l; intros l' H H_sort H_sort'.
    - apply Permutation_nil in H; congruence.
    - destruct l'.
      1: apply Permutation_sym, Permutation_nil in H; discriminate.
      inversion H_sort; inversion H_sort'; subst.
      apply Permutation_in with (x:=a) in H as H_in; intuition auto with *.
      apply Permutation_sym in H as H'.
      apply Permutation_in with (x:=v) in H' as H_in'; intuition auto with *.
      inversion H_in; inversion H_in'; subst.
      1-3: f_equal; apply IHl; auto; eapply Permutation_cons_inv; eauto.
      eapply List.Forall_In in H3, H7; eauto.
      apply value_leb_antisym in H3; auto; subst. f_equal.
      apply IHl; auto. eapply Permutation_cons_inv; eauto.
  Qed.

  Lemma In_dedup_app : forall (l l' : list value),
      Forall (fun x => In x l') l ->
      List.dedup value_eqb (l ++ l') = List.dedup value_eqb l'.
  Proof.
    induction l; simpl; auto; intros.
    invert_Forall.
    assert(H: In a (l ++ l')).
    { apply in_or_app; auto. }
    apply (In_find_some _ value_eqb) in H; auto using value_eqb_refl.
    destruct_match_hyp; intuition auto.
  Qed.

  Lemma dedup_flat_map_dedup : forall (f : value -> list value) l,
      List.dedup value_eqb (flat_map f l) = List.dedup value_eqb (flat_map f (List.dedup value_eqb l)).
  Proof.
    induction l; simpl; auto.
    case_match.
    1:{ rewrite In_dedup_app; auto. apply find_some in E; intuition auto.
        apply_value_eqb_eq.
        rewrite Forall_forall; intros. apply in_flat_map; eauto. }
    1:{ simpl. rewrite dedup_app; auto using value_eqb_dec. rewrite IHl.
        rewrite <- dedup_app; auto using value_eqb_dec. }
  Qed.

  Lemma dedup_flat_map_dedup2 : forall (f : value -> list value) l,
      List.dedup value_eqb (flat_map f l) = List.dedup value_eqb (flat_map (fun v => List.dedup value_eqb (f v)) l).
  Proof.
    induction l; simpl; auto.
    rewrite dedup_app; auto using value_eqb_dec.
    lazymatch goal with
      |- _ = _ _ (_ ++ ?l') =>
        rewrite (dedup_app _ _ _ l') end; auto using value_eqb_dec.
    do 2 f_equal; auto using dedup_dedup.
  Qed.

  Lemma dedup_map_dedup : forall (f : value -> value) l,
      List.dedup value_eqb (List.map f l) = List.dedup value_eqb (List.map f (List.dedup value_eqb l)).
  Proof.
    induction l; simpl; auto. repeat case_match; simpl; auto.
    1:{ apply find_some in E; intuition auto.
        pose proof value_eqb_dec; rewrite List.dedup_preserves_In in H.
        apply_value_eqb_eq.
        rewrite IHl in * |-. rewrite <- List.dedup_preserves_In in H.
        eapply In_find_some in H; eauto using value_eqb_refl.
        destruct_match_hyp; intuition auto. }
    1:{ apply find_some in E0; intuition auto; apply_value_eqb_eq.
        eapply in_map in H.
        eapply find_none in E; intuition eauto.
        rewrite value_eqb_refl in *; congruence. }
    1:{ case_match; try congruence.
        apply find_some in E1; intuition auto; apply_value_eqb_eq.
        pose proof value_eqb_dec; rewrite List.dedup_preserves_In in H.
        rewrite <- IHl, <- List.dedup_preserves_In in * |-.
        eapply find_none in E; eauto.
        rewrite value_eqb_refl in *; congruence. }
  Qed.

  Lemma In_Permutation_map : forall (f g : value -> value) l l',
      (forall x, In x l -> f x = g x) ->
      Permutation l l' ->
      Permutation (List.map f l) (List.map g l').
  Proof.
    induction l; simpl; intros.
    1:{ apply Permutation_nil in H0; subst; auto. }
    1:{ apply Permutation_sym, Permutation_vs_cons_inv in H0 as H1.
        repeat destruct_exists; subst. rewrite map_app; simpl.
        eapply perm_trans in H0; [ | apply Permutation_middle ].
        eapply perm_trans; [ | apply Permutation_middle ].
        apply Permutation_cons; intuition auto.
        rewrite <- map_app. apply IHl; auto.
        eapply Permutation_cons_inv; eauto using Permutation_sym. }
  Qed.

  Lemma Permutation_filter : forall f g l l',
      (forall x : value, In x l -> f x = g x) ->
      Permutation l l' ->
      Permutation (filter f l) (filter g l').
    induction l; simpl; intros.
    1:{ apply Permutation_nil in H0; subst; auto. }
    1:{ apply Permutation_sym, Permutation_vs_cons_inv in H0 as H1.
        repeat destruct_exists; subst. rewrite filter_app; simpl.
        rewrite H; intuition auto. case_match.
        all: eapply perm_trans in H0; [ | apply Permutation_middle ].
        1:{ eapply perm_trans; [ | apply Permutation_middle ].
            apply Permutation_cons; auto. rewrite <- filter_app.
            apply IHl; intros; auto.
            eapply Permutation_cons_inv; eauto using Permutation_sym. }
        1:{ rewrite <- filter_app; apply IHl; auto.
            eapply Permutation_cons_inv; eauto using Permutation_sym. } }
  Qed.

  Lemma dedup_filter_dedup : forall (f : value -> bool) l,
      List.dedup value_eqb (filter f l) = List.dedup value_eqb (filter f (List.dedup value_eqb l)).
  Proof.
    induction l; simpl; auto.
    repeat case_match; simpl; repeat rewrite_l_to_r; simpl; auto.
    1:{ apply find_some in E0; intuition auto. apply_value_eqb_eq.
        assert(E_f : In v (filter f l)). { apply filter_In; intuition auto. }
        eapply In_find_some in E_f; eauto using value_eqb_refl.
        destruct_match_hyp; intuition auto. }
    1:{ pose proof (find_none _ _ E0 a).
        case_match.
        1:{ apply find_some in E1; intuition auto. apply_value_eqb_eq.
            apply filter_In in H0; intuition auto.
            rewrite value_eqb_refl in *; congruence. }
        1:{ pose proof (find_none _ _ E1 a). rewrite value_eqb_refl in *.
            case_match; auto.
            apply find_some in E2; intuition auto; apply_value_eqb_eq.
            pose proof value_eqb_dec.
            rewrite List.dedup_preserves_In, <- IHl, <- List.dedup_preserves_In in H1.
            apply H0 in H1. congruence. } }
  Qed.

  Lemma In_Permutation_filter : forall f g l l',
      (forall x : value, In x l -> f x = g x) ->
      Permutation l l' ->
      Permutation (filter f l) (filter g l').
  Proof.
    induction l; simpl; intros.
    1:{ apply Permutation_nil in H0; subst; auto. }
    1:{ apply Permutation_sym, Permutation_vs_cons_inv in H0 as H1.
        repeat destruct_exists; subst. rewrite filter_app; simpl.
        rewrite H; [ | left; auto ].
        case_match.
        all: eapply perm_trans in H0; [ | apply Permutation_middle ];
          apply Permutation_cons_inv in H0.
        1:{ eapply perm_trans; [ | apply Permutation_middle ].
            apply Permutation_cons; auto. rewrite <- filter_app.
            apply IHl; auto using Permutation_sym. }
        1:{ rewrite <- filter_app.
            apply IHl; auto using Permutation_sym. } }
  Qed.

  Lemma Permutation_dedup_Permuted : forall (l1 l2 l1' l2' : list value),
      Permutation (List.dedup value_eqb l1) (List.dedup value_eqb l2) ->
      Permutation l1 l1' -> Permutation l2 l2' ->
      Permutation (List.dedup value_eqb l1') (List.dedup value_eqb l2').
  Proof.
    intros. eapply dedup_preserve_Permutation in H0, H1;
      eauto using value_eqb_refl, value_eqb_eq, value_eqb_sym,
      Permutation_sym, perm_trans.
  Qed.
End WithWord.

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


Fixpoint is_NoDup {A} (l : list A) : Prop :=
  match l with
  | nil => True
  | x :: l => ~ In x l /\ is_NoDup l
  end.

Definition is_NoDup_opaque {A : Type} := is_NoDup (A:=A).

Lemma is_NoDup_to_transparent : forall A l, is_NoDup_opaque (A:=A) l <-> is_NoDup (A:=A) l.
Proof.
  split; auto.
Qed.

Global Opaque is_NoDup_opaque.

Ltac use_is_NoDup :=
  rewrite is_NoDup_to_transparent in *;
  simpl in *; intuition idtac; try congruence.

Create HintDb transf_hints.
#[export] Hint Resolve <- is_NoDup_to_transparent : transf_hints.
#[export] Hint Extern 5 (is_NoDup _) => simpl; intuition discriminate : transf_hints.
#[export] Hint Extern 5 ((_ : string) <> _) => apply eqb_neq : transf_hints.
#[export] Hint Extern 5 (word.ok _) => typeclasses eauto : transf_hints.
#[export] Hint Extern 5 (map.ok _) => typeclasses eauto : transf_hints.
#[export] Hint Extern 5 string => exact (EmptyString:string).

Ltac resolve_NoDup := repeat constructor; simpl; intuition idtac; congruence.

Ltac resolve_tenv_wf := repeat apply tenv_wf_step; try apply tenv_wf_empty; repeat constructor; resolve_NoDup.

Hint Extern 5 (well_typed _ _ _) => simple eapply command_typechecker_sound : transf_hints.
Hint Extern 5 (tenv_wf _) => resolve_tenv_wf : transf_hints.
Hint Extern 5 (typecheck _ _ _ = Success _) => reflexivity : transf_hints.

Fixpoint free_immut_in (x : string) (e : expr) : bool :=
  match e with
  | EVar y => String.eqb x y
  | ELoc _ | EAtom _ => false
  | EUnop _ e => free_immut_in x e
  | EBinop _ e1 e2 => free_immut_in x e1 || free_immut_in x e2
  | ETernop _ e1 e2 e3 => free_immut_in x e1 || free_immut_in x e2 || free_immut_in x e3
  | EIf e1 e2 e3 => free_immut_in x e1 || free_immut_in x e2 || free_immut_in x e3
  | ELet e1 y e2 | EFlatmap _ e1 y e2 => free_immut_in x e1 || (negb (String.eqb x y) && free_immut_in x e2)
  | EFlatmap2 e1 e2 x1 x2 e3 =>
      free_immut_in x e1 || free_immut_in x e2 ||
        (negb (String.eqb x x1) && negb (String.eqb x x2) && free_immut_in x e3)
  | EFold e1 e2 y z e3 => free_immut_in x e1 || free_immut_in x e2 || (negb (String.eqb x y) && negb (String.eqb x z) && free_immut_in x e3)
  | EACFold _ e => free_immut_in x e
  | ERecord l => existsb (fun '(_, e) => free_immut_in x e) l
  | EAccess e _ => free_immut_in x e
  | EOptMatch e e_none y e_some => free_immut_in x e || free_immut_in x e_none || (negb (String.eqb x y) && free_immut_in x e_some)
  | EDictFold d e0 k v acc e => free_immut_in x d || free_immut_in x e0 ||
                                  (negb (String.eqb x k) && negb (String.eqb x v) && negb (String.eqb x acc) &&
                                     free_immut_in x e)
  | ESort _ l => free_immut_in x l
  | EFilter _ e y p => free_immut_in x e || (negb (String.eqb x y) && free_immut_in x p)
  | EJoin _ e1 e2 x1 x2 p r => free_immut_in x e1 || free_immut_in x e2 ||
                               (negb (String.eqb x x1) && negb (String.eqb x x2) && (free_immut_in x p || free_immut_in x r))
  | EProj _ e y r => free_immut_in x e || (negb (String.eqb x y) && free_immut_in x r)
  | EBagOf e => free_immut_in x e
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  Open Scope string_scope.

  Ltac destruct_one_match :=
    lazymatch goal with
    | |- context [match ?x with _ => _ end] =>
        let E := fresh "E" in
        destruct x eqn:E
    end.

  Lemma not_free_immut_put_ty: forall x e Gstore Genv t t',
      free_immut_in x e = false ->
      type_of Gstore (map.put Genv x t') e t ->
      type_of Gstore Genv e t.
  Proof.
    intros. generalize dependent Genv. revert t. induction e using expr_IH;
      intros; simpl in *; repeat rewrite Bool.orb_false_iff in *;
      try now (inversion H0; subst; econstructor; eauto; intuition auto).
    - inversion H0; subst; constructor. rewrite eqb_neq in *. rewrite map.get_put_diff in *; auto.
    - inversion H0; subst; econstructor.
      + apply IHe1; eauto; intuition.
      + destruct (x =? x0) eqn:Ex.
        * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
        * apply IHe2; intuition.
          rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
    - inversion H0; subst; econstructor.
      1,3: apply IHe1; eauto; intuition idtac.
      1,2: destruct (x =? x0) eqn:Ex;
      [ rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same in *; auto
      | apply IHe2; intuition idtac;
        rewrite eqb_neq in *; rewrite Properties.map.put_put_diff; auto ].
    - invert_type_of_clear; econstructor.
      1: apply IHe1; eauto; intuition idtac.
      1: apply IHe2; eauto; intuition idtac.
      destruct (x =? x1) eqn:Ex1;
      [ rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same in *; auto
      | rewrite eqb_neq in *; rewrite Properties.map.put_put_diff with (k1 := x) in *; auto ].
      destruct (x =? x2) eqn:Ex2;
        [ rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same in *; auto
        | apply IHe3; intuition idtac;
          rewrite eqb_neq in *; rewrite Properties.map.put_put_diff; auto ].
    - inversion H0; subst; econstructor.
      + apply IHe1; eauto; intuition.
      + apply IHe2; intuition.
      + destruct (x =? x0) eqn:Ex.
        * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
        * rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x) in *; auto.
          destruct (x =? y) eqn:Ey.
          -- rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
          -- apply IHe3; intuition.
             rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
    - inversion H1; subst. econstructor; eauto. revert H0 H H4; clear; intros.
      generalize dependent tl. induction l; intros; destruct tl; intuition; inversion H4.
      subst. simpl in H; rewrite Bool.orb_false_iff in *. constructor; inversion H0; subst.
      + apply H3; destruct a; intuition.
      + fold (map snd l) (map snd tl). apply IHl; intuition.
    - inversion H0; subst. econstructor.
      + apply IHe1; eauto; intuition.
      + apply IHe2; eauto; intuition.
      + destruct (x =? x0) eqn:Ex.
        * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
        * apply IHe3; intuition.
          rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
    - inversion H0; subst; econstructor.
      + apply IHe1; eauto; intuition.
      + apply IHe2; intuition.
      + destruct (x =? k) eqn:Ek.
        * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
        * rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x) in *; auto.
          destruct (x =? v) eqn:Ev.
          -- rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
          -- rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x) in *; auto.
             destruct (x =? acc) eqn:Eacc.
             ++ rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
             ++ apply IHe3; intuition.
                rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
    - inversion H0; subst; constructor.
      1,3: apply IHe1; auto; intuition.
      1,2: destruct (x =? x0) eqn:Ex;
      [ rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same in *; auto
      | apply IHe2; intuition;
        rewrite eqb_neq in *; rewrite Properties.map.put_put_diff; auto ].
    - inversion H0; subst; econstructor.
      1,5: apply IHe1; eauto; intuition.
      1,4: apply IHe2; eauto; intuition.
      1,3: destruct (x =? x0) eqn:Ex;
      [ rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same in *; auto
      | rewrite eqb_neq in *; rewrite Properties.map.put_put_diff with (k1 := x) in *; auto ];
      (destruct (x =? y) eqn:Ey;
       [ rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same in *; auto
       | apply IHe3; simpl in *; rewrite Bool.orb_false_iff in *; intuition; rewrite eqb_neq in *;
         rewrite Properties.map.put_put_diff; auto ]).
      1,2: destruct (x =? x0) eqn:Ex;
      [ rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same in *; auto
      | rewrite eqb_neq in *; rewrite Properties.map.put_put_diff with (k1 := x) in *; auto ];
      (destruct (x =? y) eqn:Ey;
       [ rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same in *; auto
       | apply IHe4; simpl in *; rewrite Bool.orb_false_iff in *; intuition; rewrite eqb_neq in *;
         rewrite Properties.map.put_put_diff; auto ]).
    - inversion H0; subst; econstructor.
      1,3: apply IHe1; eauto; intuition.
      1,2: destruct (x =? x0) eqn:Ex;
      [ rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same in *; auto
      | apply IHe2; intuition;
        rewrite eqb_neq in *; rewrite Properties.map.put_put_diff; auto ].
  Qed.

  Lemma not_free_immut_put_sem: forall e x (store env : locals) v,
      free_immut_in x e = false ->
      interp_expr store env e = interp_expr store (map.put env x v) e.
  Proof.
    induction e using expr_IH; intros; simpl in *; auto; repeat rewrite Bool.orb_false_iff in *;
      try (erewrite IHe; auto).
    - rewrite eqb_neq in *. unfold get_local. rewrite map.get_put_diff; auto.
    - erewrite IHe1, IHe2; intuition idtac.
    - erewrite IHe1, IHe2, IHe3; intuition idtac.
    - erewrite IHe1, IHe2, IHe3; intuition idtac.
    - destruct (x0 =? x) eqn:E.
      + rewrite eqb_eq in *; subst.
        rewrite Properties.map.put_put_same. erewrite IHe1; intuition.
      + rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
        erewrite IHe1, IHe2; intuition.
    - destruct tag; auto;
        rewrite <- IHe1; intuition; case_match; auto; [do 2 f_equal | f_equal ];
        apply flat_map_ext; intros; destruct (x0 =? x) eqn:E'.
      1,3: rewrite eqb_eq in *; subst;
      rewrite Properties.map.put_put_same; auto.
      1,2: rewrite eqb_neq in *; rewrite Properties.map.put_put_diff; auto;
      erewrite IHe2; intuition.
    - rewrite <- IHe1; intuition idtac.
      rewrite <- IHe2; intuition idtac.
      repeat case_match; auto. f_equal.
      apply In_flat_map2_ext; intros.
      destruct (x =? x1) eqn:Ex1;
        [ rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same; auto
        | rewrite eqb_neq in *; rewrite Properties.map.put_put_diff with (k1 := x); intuition idtac ].
      destruct (x =? x2) eqn:Ex2;
        [ rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same; auto
        | rewrite eqb_neq in *; rewrite Properties.map.put_put_diff with (k1 := x); intuition idtac ].
      rewrite <- (IHe3 x); auto.
    - rewrite <- IHe1; intuition. case_match; auto. rewrite <- IHe2; auto.
      apply In_fold_right_ext with (P := fun _ => True); auto.
      intros. destruct (x0 =? x) eqn:Ex.
      + rewrite eqb_eq in *; subst.
        rewrite Properties.map.put_put_same. auto.
      + rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x0); intuition.
        destruct (x0 =? y) eqn:Ey.
        * rewrite eqb_eq in *; subst.
          rewrite Properties.map.put_put_same. auto.
        * rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x0); intuition.
    - do 2 f_equal. induction l; auto. simpl in *. rewrite Bool.orb_false_iff in *.
      destruct a; intuition. f_equal.
      + f_equal. inversion H; subst. apply H4; intuition.
      + inversion H; apply IHl; intuition.
    - rewrite <- IHe1, <- IHe2; auto; intuition. repeat case_match; auto.
      destruct (x0 =? x) eqn:Ex.
      * rewrite eqb_eq in *; subst.
        rewrite Properties.map.put_put_same. auto.
      * rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x0); intuition.
    - rewrite <- IHe1; intuition. case_match; auto. rewrite <- IHe2; auto.
      apply In_fold_right_ext with (P := fun _ => True); auto.
      intros. destruct (x =? k) eqn:Ek;
        try (rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same; auto).
      rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x); intuition.
      destruct (x =? v) eqn:Ev;
        try (rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same; auto).
      rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x); intuition.
      destruct (x =? acc) eqn:Eacc;
        try (rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same; auto).
      rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x); intuition.
    - destruct tag; auto;
      rewrite <- IHe1; intuition idtac; case_match; auto;
      f_equal; clear E; induction l; auto; simpl;
      (destruct (x0 =? x) eqn:E';
       [ rewrite eqb_eq in *; subst;
         rewrite Properties.map.put_put_same; destruct_one_match;
         [f_equal |]; apply IHl
       | rewrite eqb_neq in *; rewrite Properties.map.put_put_diff; intuition idtac;
         rewrite <- IHe2 with (x := x0); intuition idtac;
         destruct_one_match; auto; f_equal; apply IHl ]).
    - destruct tag; auto;
        rewrite <- IHe1, <- IHe2; intuition idtac; repeat case_match; auto.
      1: do 2 f_equal; apply flat_map_ext; intros; clear E E0;
      remember (bag_to_list l0) as l0'; clear Heql0';
      induction l0'; auto; simpl.
      2: f_equal; apply flat_map_ext; intros; clear E E0;
      induction l0; auto; simpl.
      all: enough (interp_expr store (map.put (map.put (map.put env x0 v) x a) y a0) e3 = interp_expr store (map.put (map.put env x a) y a0) e3);
        [ | (destruct (x0 =? x) eqn:Ex;
             [ rewrite eqb_eq in *; subst;
               rewrite Properties.map.put_put_same; auto
             | rewrite eqb_neq in *;
               rewrite Properties.map.put_put_diff with (k1 := x0); auto;
               (destruct (x0 =? y) eqn:Ey;
               [ rewrite eqb_eq in *; subst;
                 rewrite Properties.map.put_put_same; auto
               | rewrite eqb_neq in *;
                 rewrite Properties.map.put_put_diff; auto;
                 simpl in H1; rewrite Bool.orb_false_iff in *;
                 rewrite <- IHe3; intuition idtac ]) ]) ].
      1: rewrite H0; destruct_one_match; simpl; try apply IHl0';
      f_equal; try apply IHl0'.
      2: rewrite H0; destruct_one_match; simpl; try apply IHl0;
      f_equal; try apply IHl0.
      all: destruct (x0 =? x) eqn:Ex;
        [ rewrite eqb_eq in *; subst;
          rewrite Properties.map.put_put_same; auto
        | rewrite eqb_neq in *;
          rewrite Properties.map.put_put_diff with (k1 := x0); auto;
          (destruct (x0 =? y) eqn:Ey;
           [ rewrite eqb_eq in *; subst;
             rewrite Properties.map.put_put_same; auto
           | rewrite eqb_neq in *;
             rewrite Properties.map.put_put_diff with (k1 := x0); auto;
             simpl in H1; rewrite Bool.orb_false_iff in *;
             rewrite <- (IHe4 x0); intuition idtac ]) ].
    - destruct tag; auto;
        rewrite <- IHe1; intuition idtac; case_match; auto.
      all: [> do 2 f_equal | f_equal ]; apply map_ext; intro;
        (destruct (x0 =? x) eqn:Ex;
         [ rewrite eqb_eq in *; subst;
           rewrite Properties.map.put_put_same; auto
         | rewrite eqb_neq in *;
           rewrite Properties.map.put_put_diff with (k1 := x0); auto ]).
  Qed.
End WithMap.

Open Scope string_scope.

Definition epair (e1 e2 : expr) := ERecord [("0", e1); ("1", e2)].
Definition ofst (e : expr) : expr := EAccess e "0".
Definition osnd (e : expr) : expr := EAccess e "1".
Definition enil := EAtom (ANil None).
Definition econs (e1 e2 : expr) := EBinop OCons e1 e2.
Definition cons_to_fst (e1 e2 : expr) :=
  epair (econs e1 (ofst e2)) (osnd e2).
