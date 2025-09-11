Require Import ZArith String List.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Datatypes.List coqutil.Datatypes.Result.
Require Import Std.Sorting.Mergesort Sorted Permutation.

Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.

  Inductive value :=
  | VWord (w : word)
  | VInt (z : Z)
  | VBool (b : bool)
  | VString (s : string)
  | VOption (m : option value)
  | VList (l : list value)
  | VRecord (l : list (string * value))
  | VDict (l : list (value * value))
  | VBag (l : list (value * nat))
  | VUnit.

  Section ValueIH.
    Context (P : value -> Prop).
    Hypothesis (f_word : forall w : word, P (VWord w)) (f_int : forall z : Z, P (VInt z)) (f_bool : forall b : bool, P (VBool b)) (f_string : forall s : string, P (VString s))
      (f_option : forall m : option value, match m with Some v => P v | None => True end -> P (VOption m))
      (f_list : forall l : list value, Forall P l -> P (VList l))
      (f_record : forall l : list (string * value), Forall (fun v => P (snd v)) l -> P (VRecord l))
      (f_dict : forall l : list (value * value), Forall (fun v => P (fst v) /\ P (snd v)) l -> P (VDict l))
      (f_bag : forall l : list (value * nat), Forall (fun v => P (fst v)) l -> P (VBag l))
      (f_unit : P VUnit).
    Section __.
      Context (value_IH : forall v, P v).
      Fixpoint list_value_IH (l : list value) : Forall P l :=
        match l as l0 return Forall P l0 with
        | nil => Forall_nil P
        | v :: l' => Forall_cons v (value_IH v) (list_value_IH l')
        end.
      Fixpoint record_value_IH (l : list (string * value)) : Forall (fun v => P (snd v)) l :=
        match l as l0 return Forall (fun v => P (snd v)) l0 with
        | nil => Forall_nil (fun v => P (snd v))
        | v :: l' => Forall_cons v (value_IH (snd v)) (record_value_IH l')
        end.
      Fixpoint dict_value_IH (l : list (value * value)) : Forall (fun v => P (fst v) /\ P (snd v)) l :=
        match l as l0 return Forall (fun v => P (fst v) /\ P (snd v)) l0 with
        | nil => Forall_nil (fun v => P (fst v) /\ P (snd v))
        | v :: l' => Forall_cons v (conj (value_IH (fst v)) (value_IH (snd v)))(dict_value_IH l')
        end.
      Fixpoint bag_value_IH (l : list (value * nat)) : Forall (fun v => P (fst v)) l :=
        match l as l0 return Forall (fun v => P (fst v)) l0 with
        | nil => Forall_nil (fun v => P (fst v))
        | v :: l' => Forall_cons v (value_IH (fst v)) (bag_value_IH l')
        end.
    End __.

    Fixpoint value_IH (v : value) {struct v} : P v :=
      match v with
      | VWord w => f_word w
      | VInt z => f_int z
      | VBool b => f_bool b
      | VString s => f_string s
      | VOption m => f_option m match m with Some v => value_IH v | None => I end
      | VList l => f_list l (list_value_IH value_IH l)
      | VRecord l => f_record l (record_value_IH value_IH l)
      | VDict l => f_dict l (dict_value_IH value_IH l)
      | VBag l => f_bag l (bag_value_IH value_IH l)
      | VUnit => f_unit
      end.
  End ValueIH.

  Fixpoint access_record {A : Type} (l : list (string * A)) (s : string) : result A :=
    match l with
    | nil => error:("Attribute" s "not found in record" l)
    | (s0, a) :: l => if String.eqb s s0 then Success a else access_record l s
    end.

  (* ===== Comparison ===== *)
  Scheme Equality for list.

  Section __.
    Context {A} (A_compare : A -> A -> comparison).
    Fixpoint list_compare (l l' : list A) : comparison :=
      match l, l' with
      | nil, nil => Eq
      | nil, _ => Lt
      | _, nil => Gt
      | h :: l, h' :: l' => match A_compare h h' with
                            | Eq => list_compare l l'
                            | _ as c => c
                            end
      end.
  End __.

  Definition pair_compare {A B : Type} (fst_compare : A -> A -> comparison) (snd_compare : B -> B -> comparison) (p1 p2 : A * B) : comparison :=
    let '(a1, b1) := p1 in
    let '(a2, b2) := p2 in
    match fst_compare a1 a2 with
    | Eq => snd_compare b1 b2
    | c => c
    end.

  Section WithValueCompare.
    Context (value_compare : value -> value -> comparison).

    Definition record_compare : list (string * value) -> list (string * value) -> comparison :=
      list_compare (pair_compare String.compare value_compare).

    Definition dict_compare : list (value * value) -> list (value * value) -> comparison :=
      list_compare (pair_compare value_compare value_compare).

    Definition bag_compare : list (value * nat) -> list (value * nat) -> comparison :=
      list_compare (pair_compare value_compare Nat.compare).
  End WithValueCompare.

  Fixpoint value_compare (a b : value) : comparison :=
    match a, b with
    | VWord a, VWord b =>
        if word.eqb a b then Eq else if word.ltu a b then Lt else Gt
    | VInt a, VInt b =>
        Z.compare a b (* if Z.eqb a b then Eq else if Z.ltb a b then Lt else Gt *)
    | VBool a, VBool b =>
        Bool.compare a b (* if Bool.eqb a b then Eq else if andb (negb a) b then Lt else Gt *)
    | VString a, VString b =>
        String.compare a b (* if String.eqb a b then Eq else if String.ltb a b then Lt else Gt *)
    | VOption a, VOption b =>
        match a with
        | None => match b with None => Eq | _ => Lt end
        | Some a => match b with None => Gt | Some b => value_compare a b end
        end
    | VList a, VList b => list_compare value_compare a b
    | VRecord a, VRecord b => record_compare value_compare a b
    | VDict a, VDict b => dict_compare value_compare a b
    | VBag a, VBag b => bag_compare value_compare a b
    | VUnit, VUnit => Eq
    | VUnit, _ => Lt | _, VUnit => Gt
    | VBool _, _ => Lt | _, VBool _ => Gt
    | VWord _, _ => Lt | _, VWord _ => Gt
    | VInt _, _ => Lt | _, VInt _ => Gt
    | VString _, _ => Lt | _, VString _ => Gt
    | VOption _, _ => Lt | _, VOption _ => Gt
    | VList _, _ => Lt | _, VList _ => Gt
    | VRecord _, _ => Lt | _, VRecord _ => Gt
    | VDict _, _ => Lt | _, VDict _ => Gt
    end.

  Definition value_eqb (a b : value) : bool :=
    match value_compare a b with
    | Eq => true
    | _ => false
    end.

  Definition value_ltb (a b : value) : bool :=
    match value_compare a b with
    | Lt => true
    | _ => false
    end.

  Definition leb_from_compare {A : Type} (cmp : A -> A -> comparison) (x y : A) : bool :=
    match cmp x y with
    | Lt | Eq => true
    | Gt => false
    end.

  Definition value_leb := leb_from_compare value_compare.

  Definition is_antisym {A : Type} (cmp : A -> A -> comparison) := forall x y : A, cmp x y = CompOpp (cmp y x).

  Lemma antisym__pair_antisym : forall (A B : Type) (A_cmp : A -> A -> comparison) (B_cmp : B -> B -> comparison),
      is_antisym A_cmp -> is_antisym B_cmp -> is_antisym (pair_compare A_cmp B_cmp).
  Proof.
    intros A B A_cmp B_cmp HA HB. unfold is_antisym. intros [xa xb] [ya yb].
    simpl. rewrite HA, HB. destruct (A_cmp ya xa), (B_cmp yb xb); auto.
  Qed.

  Definition is_total {A : Type} (leb : A -> A -> bool) : Prop :=
    forall x y, leb x y = true \/ leb y x = true.

  Lemma compare_antisym__leb_total : forall (A : Type) (cmp : A -> A -> comparison), is_antisym cmp -> is_total (leb_from_compare cmp).
  Proof.
    unfold is_antisym, is_total, leb_from_compare.
    intros A cmp H x y. rewrite H; destruct (cmp y x); intuition.
  Qed.

  Lemma string_compare_refl : forall s : string, String.compare s s = Eq.
  Proof.
    induction s; trivial. simpl. unfold Ascii.compare.
    rewrite N.compare_refl; trivial.
  Qed.

  Lemma value_compare_refl : forall v : value, value_compare v v = Eq.
    induction v using value_IH; auto; intros; simpl.
    - rewrite word.eqb_eq; trivial.
    - apply Z.compare_refl.
    - destruct b; trivial.
    - apply string_compare_refl.
    - destruct m; auto.
    - induction l; auto. simpl. inversion H; subst; auto.
      rewrite H2. auto.
    - induction l; auto. destruct a. simpl.
      rewrite string_compare_refl. inversion H; subst; simpl in *.
      rewrite H2. auto.
    - induction l; auto. destruct a; simpl.
      inversion H; subst; simpl in *. destruct H2.
      rewrite H0, H1. auto.
    - induction l; auto. destruct a; simpl.
      inversion H; subst; simpl in *. rewrite H2, Nat.compare_refl.
      auto.
  Qed.

  Lemma value_compare_antisym : is_antisym value_compare.
  Proof.
    intro u. apply (value_IH ((fun u => forall v, value_compare u v = CompOpp (value_compare v u))));
      destruct v; auto; intros; simpl.
    - repeat match goal with
             | |- context[word.eqb ?a ?b] => destruct (word.eqb_spec a b)
             | |- context[word.ltu ?a ?b] => destruct (word.ltu_spec a b)
             | H1: ?a <> ?b, H2: ?b = ?a |- _ => symmetry in H2; intuition
             end; auto; intuition.
      + exfalso. apply (Z.lt_asymm _ _ H1). assumption.
      + exfalso. apply H. apply (Z.le_antisymm _ _ H1) in H2.
        rewrite <-word.of_Z_unsigned. rewrite <-word.of_Z_unsigned at 1. congruence.
    - apply Z.compare_antisym.
    - destruct b, b0; auto.
    - apply String.compare_antisym.
    - destruct m, m0; auto.
    - revert l0. induction l; destruct l0; auto.
      simpl. inversion H; subst. pose proof (H2 v) as H2. destruct (value_compare v a) eqn:E.
      + rewrite H2. simpl. apply IHl. assumption.
      + rewrite H2. trivial.
      + rewrite H2. trivial.
    - revert l0. induction l as [| a l IHl]; destruct l0 as [| b l0]; auto. destruct a as [sa va], b as [sb vb].
      simpl. inversion H; subst. pose proof (H2 vb) as H2. simpl in *.
      rewrite String.compare_antisym. destruct (sb ?= sa)%string; simpl; auto. rewrite H2.
      destruct (value_compare vb va); simpl; auto.
    - revert l0. induction l as [| a l IHl]; destruct l0 as [| b l0]; auto. destruct a as [ka va], b as [kb vb].
      simpl. inversion H; subst. destruct H2 as [H2L H2R]. pose proof (H2L kb) as H2L. pose proof (H2R vb) as H2R.
      simpl in *. rewrite H2L, H2R. destruct (value_compare kb ka), (value_compare vb va); simpl; auto.
    - revert l0. induction l as [| a l IHl]; destruct l0 as [| b l0]; auto. destruct a as [sa va], b as [sb vb].
      simpl. inversion H; subst. pose proof (H2 sb) as H2. simpl in *. rewrite H2.
      destruct (value_compare sb sa); simpl; auto.
      rewrite Nat.compare_antisym. destruct (Nat.compare vb va); simpl; auto.
  Qed.

  Local Ltac destruct_match :=
    lazymatch goal with
    | H: context[match ?x with _ => _ end] |- _ =>
        let E := fresh "E" in
        destruct x eqn:E
    end.

  Lemma list_compare_Eq_eq : forall A A_compare (l l' : list A),
      Forall (fun v => forall v', A_compare v v' = Eq -> v = v') l ->
      list_compare A_compare l l' = Eq -> l = l'.
  Proof.
    intros. generalize dependent l'.
    induction H; simpl; intros; destruct l'; try discriminate; auto.
    destruct_match; try discriminate. apply H in E.
    subst. f_equal. auto.
  Qed.

  Lemma pair_compare_Eq_eq : forall A B A_compare B_compare (p p' : A * B),
      (forall a, A_compare (fst p) a = Eq -> fst p = a) ->
      (forall b, B_compare (snd p) b = Eq -> snd p = b) ->
      pair_compare A_compare B_compare p p' = Eq -> p = p'.
  Proof.
    intros A B A_compare B_compare p p' HA HB H. destruct p, p'; simpl in *.
    destruct_match; try discriminate. apply HA in E; apply HB in H.
    congruence.
  Qed.

  Lemma record_compare_Eq_eq : forall value_compare l l',
      Forall (fun v =>
                forall v', value_compare (snd v) v' = Eq -> snd v = v') l ->
      record_compare value_compare l l' = Eq ->
      l = l'.
  Proof.
    intros. generalize dependent l'.
    induction H; simpl; intros; destruct l'; try discriminate; auto.
    destruct_match; try discriminate. erewrite IHForall; eauto.
    f_equal. eapply pair_compare_Eq_eq; eauto.
    apply compare_eq_iff.
  Qed.

  Lemma bag_compare_Eq_eq : forall value_compare l l',
      Forall (fun v =>
                forall v', value_compare (fst v) v' = Eq -> fst v = v') l ->
      bag_compare value_compare l l' = Eq ->
      l = l'.
  Proof.
    intros. generalize dependent l'.
    induction H; simpl; intros; destruct l'; try discriminate; auto.
    destruct_match; try discriminate. erewrite IHForall; eauto.
    f_equal. eapply pair_compare_Eq_eq; eauto.
    apply Nat.compare_eq_iff.
  Qed.

  Lemma value_compare_Eq_eq : forall v v', value_compare v v' = Eq -> v = v'.
  Proof.
    intros. generalize dependent v'. induction v using value_IH; intros;
      destruct v'; simpl in *; try discriminate;
      repeat destruct_match; try discriminate; auto; f_equal.
      - apply word.eqb_true; auto.
      - apply Z.compare_eq; auto.
      - destruct b, b0; try discriminate; auto.
      - apply compare_eq_iff; auto.
      - f_equal; auto.
      - eapply list_compare_Eq_eq; eauto.
      - eapply record_compare_Eq_eq; eauto.
      - unfold dict_compare in *. eapply list_compare_Eq_eq; eauto.
        rewrite Forall_forall; intros. eapply List.Forall_In in H; eauto.
        eapply pair_compare_Eq_eq; eauto; intuition.
      - eapply bag_compare_Eq_eq; eauto.
  Qed.

  Lemma eq_value_compare_Eq : forall v v', v = v' -> value_compare v v' = Eq.
  Proof.
    intros; subst; apply value_compare_refl.
  Qed.

  Lemma value_eqb_sym : forall x y, value_eqb x y = value_eqb y x.
  Proof.
    intros. unfold value_eqb. rewrite value_compare_antisym. destruct (value_compare y x); auto.
  Qed.

  Lemma value_eqb_eq : forall x y, value_eqb x y = true -> x = y.
  Proof.
    intros * H. unfold value_eqb in H.
    lazymatch goal with H: context [value_compare ?x ?y] |- _ => destruct (value_compare x y) eqn:E end.
    2-3: discriminate.
    apply value_compare_Eq_eq; auto.
  Qed.

  Definition trans_at {A} (compare : A -> A -> comparison) (a a' a'' : A) :=
    compare a a' = Lt -> compare a' a'' = Lt -> compare a a'' = Lt.

  Lemma string_compare_trans : forall s1 s2 s3,
      trans_at String.compare s1 s2 s3.
  Proof.
    unfold trans_at.
    induction s1; destruct s2, s3; auto; simpl in *; try discriminate.
    - intros. destruct (Ascii.compare a a0) eqn:E1, (Ascii.compare a0 a1) eqn:E2; try discriminate; auto.
      + apply Ascii.compare_eq_iff in E2; subst. rewrite E1. eapply IHs1; eauto.
      + apply Ascii.compare_eq_iff in E1; subst. rewrite E2. auto.
      + apply Ascii.compare_eq_iff in E2; subst. rewrite E1. auto.
      + unfold Ascii.compare in *. rewrite N.compare_lt_iff in E1, E2.
        pose proof (N.lt_trans _ _ _ E1 E2). rewrite <-  N.compare_lt_iff in H1.
        rewrite H1. easy.
  Qed.

  Lemma list_compare_trans : forall A A_compare (l l' l'' : list A),
      (forall v, A_compare v v = Eq) ->
      (forall v v', A_compare v v' = Eq -> v = v') ->
      Forall (fun v => forall v' v'', trans_at A_compare v v' v'') l ->
      list_compare A_compare l l' = Lt ->
      list_compare A_compare l' l'' = Lt ->
      list_compare A_compare l l'' = Lt.
  Proof.
    induction l; destruct l', l''; try discriminate; auto.
    intros H_refl H_Eq_eq H_trans H1 H2; simpl in *.
    repeat destruct_match; try discriminate;
      try apply H_Eq_eq in E0; try apply H_Eq_eq in E; subst.
    - rewrite H_refl. inversion H_trans; eapply IHl; eauto.
    - rewrite E0; auto.
    - rewrite E; auto.
    - inversion H_trans; subst. erewrite H3; eauto.
  Qed.

  Lemma pair_compare_refl : forall A B A_compare B_compare (p : A * B),
      (forall a, A_compare a a = Eq) ->
      (forall b, B_compare b b = Eq) ->
      pair_compare A_compare B_compare p p = Eq.
  Proof.
    intros. destruct p. simpl. rewrite H, H0; auto.
  Qed.

  Lemma pair_compare_trans : forall A B A_compare B_compare (p p' p'' : A * B),
      (forall v, A_compare v v = Eq) ->
      (forall v v', A_compare v v' = Eq -> v = v') ->
      trans_at A_compare (fst p) (fst p') (fst p'') ->
      trans_at B_compare (snd p) (snd p') (snd p'') ->
      trans_at (pair_compare A_compare B_compare) p p' p''.
  Proof.
    unfold trans_at; destruct p, p', p''; simpl; intros H_refl H_Eq_eq HA HB H1 H2.
    repeat destruct_match; try discriminate.
    all: try apply H_Eq_eq in E; try apply H_Eq_eq in E0; subst.
    - rewrite H_refl. auto.
    - rewrite E0; auto.
    - rewrite E; auto.
    - rewrite HA; auto.
  Qed.

  Lemma record_compare_trans : forall value_compare l l' l'',
      (forall v, value_compare v v = Eq) ->
      (forall v v', value_compare v v' = Eq -> v = v') ->
      Forall (fun v => forall v' v'', trans_at value_compare (snd v) v' v'') l ->
      record_compare value_compare l l' = Lt ->
      record_compare value_compare l' l'' = Lt ->
      record_compare value_compare l l'' = Lt.
  Proof.
    induction l; destruct l', l''; try discriminate; simpl; auto.
    intros H_refl H_Eq_eq H_trans H1 H2. repeat destruct_match; try discriminate.
    all: try apply pair_compare_Eq_eq in E0; try apply pair_compare_Eq_eq in E;
      auto using compare_eq_iff; subst.
    - rewrite pair_compare_refl; auto using string_compare_refl.
      inversion H_trans; eauto.
    - rewrite E0; auto.
    - rewrite E; auto.
    - erewrite pair_compare_trans; eauto using string_compare_refl, compare_eq_iff, string_compare_trans.
      inversion H_trans; auto.
  Qed.

  Lemma value_compare_trans : forall v v' v'', value_compare v v' = Lt -> value_compare v' v'' = Lt ->
                                               value_compare v v'' = Lt.
    induction v using value_IH.
    all: destruct v', v''; simpl in *; intros; try discriminate; auto.
    - repeat destruct_match; try discriminate.
      rewrite word.unsigned_ltu in *. unfold Z.ltb in *.
      repeat destruct_match; try discriminate. eapply Zcompare_Lt_trans in E3; eauto.
      rewrite E3. destruct (word.eqb w w1) eqn:E'; try discriminate; auto.
      apply word.eqb_true in E'; subst. rewrite Z.compare_refl in E3. discriminate.
    - eapply Zcompare_Lt_trans; eauto.
    - destruct b, b0, b1; try discriminate; auto.
    - eapply string_compare_trans; eauto.
    - destruct m, m0, m1; try discriminate; auto. eapply H; eauto.
    - eapply list_compare_trans; eauto using value_compare_Eq_eq, value_compare_refl.
    - eapply record_compare_trans; eauto using value_compare_Eq_eq, value_compare_refl.
    - unfold dict_compare. eapply list_compare_trans; eauto.
      + intros; apply pair_compare_refl; auto using value_compare_refl.
      + intros; eapply pair_compare_Eq_eq; eauto using value_compare_Eq_eq, value_compare_refl.
      + rewrite Forall_forall; intros. eapply List.Forall_In in H; eauto; intuition idtac.
        apply pair_compare_trans; simpl; auto using value_compare_Eq_eq, value_compare_refl.
        * unfold trans_at; apply H3.
        * unfold trans_at; apply H4.
    - eapply list_compare_trans; intros; eauto.
      + auto using pair_compare_refl, Nat.compare_refl, value_compare_refl.
      + eapply pair_compare_Eq_eq; eauto using value_compare_Eq_eq, Nat.compare_eq.
      + apply Forall_forall; intros.
        eapply List.Forall_In in H; eauto; intuition idtac.
        apply pair_compare_trans; simpl;
          unfold trans_at; eauto using value_compare_Eq_eq, value_compare_refl.
        rewrite !Nat.compare_lt_iff. apply Nat.lt_trans.
  Qed.

  Local Coercion is_true : bool >-> Sortclass.

  Lemma value_leb_total : is_total value_leb.
  Proof.
    apply compare_antisym__leb_total. exact value_compare_antisym.
  Qed.

  Lemma value_leb_trans : RelationClasses.Transitive value_leb.
  Proof.
    unfold RelationClasses.Transitive. unfold value_leb, leb_from_compare.
    intros x y z.
    destruct (value_compare x y) eqn:E1, (value_compare y z) eqn:E2, (value_compare x z) eqn:E3; intuition.
    all: repeat match goal with H: value_compare _ _ = Eq |- _ => apply value_compare_Eq_eq in H end; subst.
    all: try congruence.
    - rewrite value_compare_refl in E3; discriminate.
    - erewrite value_compare_trans in E3; eauto. discriminate.
  Qed.

  Lemma value_leb_antisym : forall x y, value_leb x y -> value_leb y x -> x = y.
  Proof.
    intros. unfold value_leb, leb_from_compare in *.
    destruct (value_compare x y) eqn:E, (value_compare y x) eqn:E';
      try discriminate.
    all: repeat match goal with H: _ = Eq |- _ => apply value_compare_Eq_eq in H end; auto.
    assert (value_compare x x = Lt). { eapply value_compare_trans; eauto. }
    rewrite value_compare_refl in *. discriminate.
  Qed.

  (* ===== Order of entries in record and dict ===== *)
  Fixpoint record_wf (l : list (string * value)) : Prop :=
    match l with
    | nil => True
    | (s, v) :: l' => (forall s' v', In (s', v') l' -> String.ltb s s' = true)
                      /\ record_wf l'
    end.

  Fixpoint dict_wf (l : list (value * value)) : Prop :=
    match l with
    | nil => True
    | (k, v) :: l' => (forall k' v', In (k', v') l' -> value_ltb k k' = true)
                      /\ dict_wf l'
    end.

  Definition value_sort := Sectioned.sort value_leb.

  Lemma LocallySorted_value_sort : forall l, LocallySorted value_leb (value_sort l).
  Proof.
    exact (Sectioned.LocallySorted_sort _ value_leb value_leb_total).
  Qed.

  Lemma Permuted_value_sort : forall l, Permutation l (value_sort l).
  Proof.
    apply Sectioned.Permuted_sort.
  Qed.

  Lemma StronglySorted_value_sort : forall l, StronglySorted (value_leb) (value_sort l).
    Proof.
      intros. apply Sectioned.StronglySorted_sort.
      - apply value_leb_total.
      - apply value_leb_trans.
    Qed.

  Section SortRecord.
    Context {A : Type}.
    Definition record_entry_leb (p p' : (string * A)) : bool := String.leb (fst p) (fst p').
    Definition record_sort := Sectioned.sort record_entry_leb.

    Lemma record_entry_leb_total : is_total record_entry_leb.
    Proof.
      unfold is_total. intros p p'. destruct p as [s t], p' as [s' t'].
      unfold record_entry_leb; simpl. destruct (String.leb s s') eqn:E; auto.
      right. pose proof String.leb_total as H. destruct (H s s'); congruence.
    Qed.

    Lemma LocallySorted_record_sort : forall l, LocallySorted record_entry_leb (record_sort l).
    Proof.
      exact (Sectioned.LocallySorted_sort _ record_entry_leb record_entry_leb_total).
    Qed.

    Lemma record_entry_leb_trans : RelationClasses.Transitive record_entry_leb.
    Proof.
      unfold RelationClasses.Transitive. destruct x, y, z. unfold record_entry_leb. simpl.
      unfold String.leb. destruct (String.compare s s0) eqn:E1, (String.compare s0 s1) eqn:E2; intuition.
      - apply compare_eq_iff in E2. subst. rewrite E1; easy.
      - apply compare_eq_iff in E1. subst. rewrite E2; easy.
      - apply compare_eq_iff in E2. subst. rewrite E1; easy.
      - pose proof (string_compare_trans _ _ _ E1 E2). rewrite H1; easy.
    Qed.

    Lemma StronglySorted_record_sort : forall l, StronglySorted (record_entry_leb) (record_sort l).
    Proof.
      intros. apply Sectioned.StronglySorted_sort.
      - apply record_entry_leb_total.
      - apply record_entry_leb_trans.
    Qed.

    Lemma Permuted_record_sort : forall l, Permutation l (record_sort l).
    Proof.
      apply Sectioned.Permuted_sort.
    Qed.
  End SortRecord.

  Definition dict_entry_leb (p p' : (value * value)) : bool := value_leb (fst p) (fst p').

  Definition dict_sort := Sectioned.sort dict_entry_leb.

  Lemma dict_entry_leb_total : is_total dict_entry_leb.
  Proof.
    unfold is_total. intros p p'. destruct p as [s t], p' as [s' t'].
    unfold dict_entry_leb; simpl. apply value_leb_total.
  Qed.

  Lemma LocallySorted_dict_sort : forall l, LocallySorted dict_entry_leb (dict_sort l).
  Proof.
    exact (Sectioned.LocallySorted_sort _ dict_entry_leb dict_entry_leb_total).
  Qed.

  Lemma Permuted_dict_sort : forall l, Permutation l (dict_sort l).
  Proof.
    apply Sectioned.Permuted_sort.
  Qed.

  Lemma dict_entry_leb_trans : RelationClasses.Transitive dict_entry_leb.
  Proof.
    unfold RelationClasses.Transitive. destruct x, y, z. unfold dict_entry_leb. simpl.
    unfold value_leb, leb_from_compare.
    repeat lazymatch goal with
           | |- context[match ?x with _ => _ end] =>
               let E := fresh "E" in
               destruct x eqn:E
           end; intuition.
    all: try apply value_compare_Eq_eq in E; try apply value_compare_Eq_eq in E0; subst;
      try congruence.
    - rewrite value_compare_refl in E1. discriminate.
    - erewrite value_compare_trans in E1; eauto. discriminate.
  Qed.

  Lemma StronglySorted_dict_sort : forall l, StronglySorted (dict_entry_leb) (dict_sort l).
  Proof.
    intros. apply Sectioned.StronglySorted_sort.
    - apply dict_entry_leb_total.
    - apply dict_entry_leb_trans.
  Qed.


  Definition bag_entry_leb (p p' : (value * nat)) : bool := value_leb (fst p) (fst p').

  Definition bag_sort := Sectioned.sort bag_entry_leb.

  Lemma bag_entry_leb_total : is_total bag_entry_leb.
  Proof.
    unfold is_total. intros p p'. destruct p as [s t], p' as [s' t'].
    unfold bag_entry_leb; simpl. apply value_leb_total.
  Qed.

  Lemma LocallySorted_bag_sort : forall l, LocallySorted bag_entry_leb (bag_sort l).
  Proof.
    exact (Sectioned.LocallySorted_sort _ bag_entry_leb bag_entry_leb_total).
  Qed.

  Lemma Permuted_bag_sort : forall l, Permutation l (bag_sort l).
  Proof.
    apply Sectioned.Permuted_sort.
  Qed.

  Lemma bag_entry_leb_trans : RelationClasses.Transitive bag_entry_leb.
  Proof.
    unfold RelationClasses.Transitive. destruct x, y, z. unfold bag_entry_leb. simpl.
    unfold value_leb, leb_from_compare.
    repeat lazymatch goal with
           | |- context[match ?x with _ => _ end] =>
               let E := fresh "E" in
               destruct x eqn:E
           end; intuition.
    all: try apply value_compare_Eq_eq in E; try apply value_compare_Eq_eq in E0; subst;
      try congruence.
    - rewrite value_compare_refl in E1. discriminate.
    - erewrite value_compare_trans in E1; eauto. discriminate.
  Qed.

  Lemma StronglySorted_bag_sort : forall l, StronglySorted (bag_entry_leb) (bag_sort l).
  Proof.
    intros. apply Sectioned.StronglySorted_sort.
    - apply bag_entry_leb_total.
    - apply bag_entry_leb_trans.
  Qed.
End WithWord.

Arguments list_beq {A}.
