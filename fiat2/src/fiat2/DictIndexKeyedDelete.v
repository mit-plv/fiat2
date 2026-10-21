(* ====================================================================
   Deleting a row from a dictionary index keyed on an attribute OTHER
   than the one the delete names.

   filter_neq_to_delete_head (DictIndexImpl.v) handles the easy case: the
   filtered attribute IS the index's own, so every row in the bucket at
   that value leaves and the whole entry goes with one ODelete.  When the
   delete names a different attribute -- a primary key, say, while the
   index buckets on something else -- that rule cannot fire, and the
   member is rebuilt by a fold over the surviving rows.

   What is needed instead is to read the leaving row out of a sibling
   primary-key member, and take just that row out of the bucket its own
   attribute names.  Sound only where the key is declared unique: with two
   rows at the same key, removing one row's contributions would lose the
   other's.  This is the shape TrigramIndexUse.filter_neq_to_tri_delete_head
   already has, with the trigrams of a row's text replaced by one attribute
   of the row.

   Removing one row from a bucket needs no bag-removal operator: a bucket
   is a bag, removal is a filter over it, and the lemma below says what
   that filter computes at the value level.
   ==================================================================== *)
Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.CollectionTransf fiat2.FlatmapTransf fiat2.EraseField fiat2.DictIndexImpl.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

(* A key function that is injective on a list, as a declared unique key is,
   identifies its rows: the fact the keyed delete needs to know that the row
   it reads out of the primary-key member is the only one leaving. *)
Lemma NoDup_map_In_eq : forall A B (f : A -> B) (l : list A) (x y : A),
    NoDup (map f l) -> In x l -> In y l -> f y = f x -> y = x.
Proof.
  induction l as [ | a l IH ]; cbn [map In]; intros x y H_nd H_x H_y E;
    [ contradiction | ].
  inversion H_nd as [ | ? ? H_ni H_nd' ]; subst.
  destruct H_x as [ E_x | H_x ]; destruct H_y as [ E_y | H_y ]; subst.
  - reflexivity.
  - exfalso; apply H_ni; rewrite <- E; apply in_map; exact H_y.
  - exfalso; apply H_ni; rewrite E; apply in_map; exact H_x.
  - apply IH; assumption.
Qed.

Section WithWord.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).

  (* Filtering a bag is filtering its entry list: no multiplicity changes,
     only whole entries go, and the result is already canonical so the
     round trip through a list costs nothing. *)
  Lemma list_to_bag_filter_bag_to_list :
    forall (f : value -> bool) (b : list (value * nat)),
      NoDup (map fst b) ->
      StronglySorted (fun p p' => is_true (bag_entry_leb p p')) b ->
      Forall (fun p : value * nat => Nat.lt 0 (snd p)) b ->
      list_to_bag (filter f (bag_to_list b)) = filter (fun p => f (fst p)) b.
  Proof.
    intros f b H_nd H_ss H_pos.
    rewrite <- bag_to_list_filter_fst.
    apply bag_to_list_to_bag.
    - rewrite <- filter_map_swap. apply NoDup_filter. assumption.
    - apply StronglySorted_filter. assumption.
    - rewrite Forall_forall in *; intros x H_in.
      apply filter_In in H_in as [ H_in _ ]. auto.
  Qed.

  (* And the same fact from the other side: filtering a list before bagging
     it is filtering the bag afterwards.  This is the form the index side
     needs, where buckets are built by list_to_bag rather than read out of a
     stored bag. *)
  Lemma list_to_bag_filter :
    forall (p : value -> bool) (l : list value),
      list_to_bag (filter p l) = filter (fun e => p (fst e)) (list_to_bag l).
  Proof.
    intros p l.
    rewrite <- (list_to_bag_filter_bag_to_list p (list_to_bag l));
      auto using list_to_bag_NoDup, list_to_bag_SSorted, list_to_bag_pos.
    apply Permutation_list_to_bag_eq, Permutation_filter.
    apply Permutation_sym, list_to_bag_to_list_Permutation.
  Qed.
End WithWord.

Section WithAttrs.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).

  (* attr is the attribute this index buckets on; key is the primary key the
     delete names.  They are different -- when they coincide the O(1) rule
     filter_neq_to_delete_head already applies and is better. *)
  Context (attr key : string).

  Definition proj_at (a : string) (r : value) : value :=
    match r with
    | VRecord rc => record_proj a rc
    | _ => VUnit
    end.

  (* the rows the index files under av *)
  Definition rows_at (av : value) (l : list value) : list value :=
    filter (fun r => value_eqb (proj_at attr r) av) l.

  Definition idx_of (l : list value) : list (value * value) :=
    match gallina_to_idx attr (VList l) with
    | VDict d => d
    | _ => nil
    end.

  Lemma gallina_to_idx_VDict : forall l,
      gallina_to_idx attr (VList l) = VDict (idx_of l).
  Proof. intro l; unfold idx_of; cbn [gallina_to_idx]; reflexivity. Qed.

  (* What the index holds at a key: the bag of the rows filed there, and no
     entry at all when none are.  The index never stores an empty bucket --
     every insertion puts a row in -- which is why the delete below must
     remove an entry that empties rather than leave it behind. *)
  Lemma idx_of_lookup : forall l av,
      Forall (fun r => exists rc, r = VRecord rc) l ->
      dict_lookup av (idx_of l)
      = match rows_at av l with
        | nil => None
        | rows => Some (VBag (list_to_bag rows))
        end.
  Proof.
    intros l av H_rec.
    induction H_rec as [ | r l [ rc E_r ] H_l IH ]; [ reflexivity | ].
    subst r. unfold idx_of, rows_at in *; cbn [gallina_to_idx fold_right filter] in *.
    unfold proj_at in *; cbn [record_proj] in *.
    destruct (value_eqb (record_proj attr rc) av) eqn:E_av.
    - apply value_eqb_eq in E_av; subst av.
      rewrite dict_lookup_insert_same, IH.
      destruct (filter _ l) as [ | r0 rows ] eqn:E_rows; reflexivity.
    - rewrite dict_lookup_insert_diff;
        [ exact IH | intro E; subst; rewrite value_eqb_refl in E_av; discriminate ].
  Qed.

  Lemma idx_of_dict_wf : forall l, dict_wf (idx_of l).
  Proof.
    induction l as [ | r l IH ]; [ exact I | ].
    unfold idx_of in *; cbn [gallina_to_idx fold_right] in *.
    destruct r; try exact I.
    apply dict_insert_preserve_dict_wf; exact IH.
  Qed.

  (* the rows that survive a delete of the row at kv *)
  Definition keeps (kv r : value) : bool :=
    negb (value_eqb (proj_at key r) kv).

  (* one bucket, with that row taken out: a filter, since a bucket is a bag
     and the language has no bag removal *)
  Definition bucket_without (kv : value) (b : list (value * nat)) :=
    filter (fun e => keeps kv (fst e)) b.

  (* and the whole index, with the row r taken out of the bucket its own
     attribute names.  The entry goes when it empties, because the index of
     a table never holds an empty bucket (idx_of_lookup). *)
  Definition unindex (kv r : value) (d : list (value * value)) :=
    match dict_lookup (proj_at attr r) d with
    | Some (VBag b) =>
        match bucket_without kv b with
        | nil => dict_delete (proj_at attr r) d
        | b' => dict_insert (proj_at attr r) (VBag b') d
        end
    | _ => d
    end.


  Lemma Forall_rec_filter : forall (f : value -> bool) l,
      Forall (fun v => exists rc, v = VRecord rc) l ->
      Forall (fun v => exists rc, v = VRecord rc) (filter f l).
  Proof.
    intros f l H; rewrite Forall_forall in *; intros x H_in.
    apply filter_In in H_in as [ H_in _ ]; auto.
  Qed.

  Lemma filter_all_true : forall A (f : A -> bool) (l : list A),
      (forall x, In x l -> f x = true) -> filter f l = l.
  Proof.
    induction l as [ | x l IH ]; cbn [filter]; intros H; [ reflexivity | ].
    rewrite (H x (or_introl eq_refl)).
    f_equal; apply IH; intros y H_in; apply H; right; exact H_in.
  Qed.

  (* Filtering the table commutes with picking out one bucket's rows. *)
  Lemma rows_at_filter : forall av kv l,
      rows_at av (filter (keeps kv) l) = filter (keeps kv) (rows_at av l).
  Proof.
    intros av kv l; unfold rows_at; induction l as [ | r l IH ]; cbn [filter]; auto.
    destruct (keeps kv r) eqn:E_k;
      destruct (value_eqb (proj_at attr r) av) eqn:E_a;
      cbn [filter]; rewrite ?E_k, ?E_a, IH; reflexivity.
  Qed.

  (* With the key declared unique, the row read out of the primary-key member
     is the only one the filter removes. *)
  Lemma keeps_other : forall l r kv r',
      NoDup (map (proj_at key) l) ->
      In r l -> proj_at key r = kv ->
      In r' l -> r' <> r -> keeps kv r' = true.
  Proof.
    intros l r kv r' H_nd H_in E_kv H_in' H_ne.
    unfold keeps; destruct (value_eqb (proj_at key r') kv) eqn:E; [ exfalso | reflexivity ].
    apply value_eqb_eq in E.
    apply H_ne, (NoDup_map_In_eq _ _ (proj_at key) l r r' H_nd H_in H_in').
    rewrite E, E_kv; reflexivity.
  Qed.

  (* ==================================================================
     The delete equation.  The index of the table with the row at kv
     filtered out is the stored index with that one row taken out of the
     one bucket its own attribute names -- not rebuilt.
     ================================================================== *)
  Theorem idx_of_filter_neq_key : forall l (r kv : value),
      Forall (fun v => exists rc, v = VRecord rc) l ->
      NoDup (map (proj_at key) l) ->
      In r l -> proj_at key r = kv ->
      idx_of (filter (keeps kv) l) = unindex kv r (idx_of l).
  Proof.
    intros l r kv H_rec H_nd H_in E_kv.
    pose proof (Forall_rec_filter (keeps kv) l H_rec) as H_recf.
    (* r sits in the bucket its attribute names, so that bucket is there *)
    assert (E_lk : dict_lookup (proj_at attr r) (idx_of l)
                   = Some (VBag (list_to_bag (rows_at (proj_at attr r) l)))).
    1:{ rewrite (idx_of_lookup l _ H_rec).
        assert (H_rin : In r (rows_at (proj_at attr r) l)).
        1:{ unfold rows_at; apply filter_In; split;
            [ exact H_in | apply value_eqb_refl ]. }
        destruct (rows_at (proj_at attr r) l) as [ | r0 rows ];
          [ contradiction | reflexivity ]. }
    apply dict_wf_lookup_ext; [ apply idx_of_dict_wf | | ].
    1:{ unfold unindex; rewrite E_lk.
        destruct (bucket_without kv (list_to_bag (rows_at (proj_at attr r) l)));
          [ apply dict_delete_preserve_dict_wf | apply dict_insert_preserve_dict_wf ];
          apply idx_of_dict_wf. }
    intros av.
    rewrite (idx_of_lookup _ av H_recf), rows_at_filter.
    unfold unindex; rewrite E_lk.
    replace (bucket_without kv (list_to_bag (rows_at (proj_at attr r) l)))
      with (list_to_bag (filter (keeps kv) (rows_at (proj_at attr r) l)))
      by (unfold bucket_without; apply list_to_bag_filter).
    destruct (value_eqb av (proj_at attr r)) eqn:E_av.
    - (* the bucket the row leaves *)
      apply value_eqb_eq in E_av; subst av.
      destruct (filter (keeps kv) (rows_at (proj_at attr r) l)) as [ | r0 rows ] eqn:E_f.
      + cbn [list_to_bag fold_right].
        rewrite dict_lookup_delete_same; [ reflexivity | apply idx_of_dict_wf ].
      + destruct (list_to_bag (r0 :: rows)) as [ | e b ] eqn:E_b.
        1:{ exfalso; cbn [list_to_bag fold_right] in E_b.
            eapply bag_insert_not_nil, E_b. }
        rewrite dict_lookup_insert_same; reflexivity.
    - (* every other bucket: untouched, and nothing in it leaves *)
      assert (H_ne : av <> proj_at attr r) by (apply value_eqb_neq; exact E_av).
      assert (E_keep : filter (keeps kv) (rows_at av l) = rows_at av l).
      1:{ apply filter_all_true; intros r' H_r'.
          unfold rows_at in H_r'; apply filter_In in H_r' as [ H_r'l E_r'a ].
          apply (keeps_other l r kv r' H_nd H_in E_kv H_r'l).
          intro E; subst r'; apply H_ne.
          symmetry; apply value_eqb_eq; exact E_r'a. }
      rewrite E_keep.
      destruct (filter (keeps kv) (rows_at (proj_at attr r) l)) as [ | r0 rows ].
      + cbn [list_to_bag fold_right].
        rewrite dict_lookup_delete_diff by exact H_ne.
        rewrite (idx_of_lookup l av H_rec); reflexivity.
      + destruct (list_to_bag (r0 :: rows)) as [ | e b ] eqn:E_b.
        1:{ exfalso; cbn [list_to_bag fold_right] in E_b.
            eapply bag_insert_not_nil, E_b. }
        rewrite dict_lookup_insert_diff by exact H_ne.
        rewrite (idx_of_lookup l av H_rec); reflexivity.
  Qed.


  (* And if no row carries the key, the delete removes nothing.  The rule
     needs this for the branch where the primary-key member has no entry at
     the deleted key -- a delete of something that is not there. *)
  Lemma idx_of_filter_neq_absent : forall l kv,
      (forall r, In r l -> proj_at key r <> kv) ->
      idx_of (filter (keeps kv) l) = idx_of l.
  Proof.
    intros l kv H; f_equal.
    apply filter_all_true; intros r H_in; unfold keeps.
    destruct (value_eqb (proj_at key r) kv) eqn:E; [ exfalso | reflexivity ].
    apply (H r H_in), value_eqb_eq, E.
  Qed.

End WithAttrs.

(* ====================================================================
   The expression side: what the bucket rewrite computes.
   ==================================================================== *)
Section WithIndexUse.
  (* the dictionary index's own binders, and the attribute it buckets on *)
  Context (attr key : string).
  (* the binders the rewritten delete introduces: the row that is leaving,
     the bucket it sits in, and a row of that bucket *)
  Context (tup bkt rvar : string).
  Context (H_rvar_tup : tup <> rvar).

  Section WithMap.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (word:=word)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    (* the bucket with the leaving row taken out.  A filter, not a removal
       operator: a bucket is a bag, and filtering one is filtering its
       entry list (list_to_bag_filter_bag_to_list). *)
    Notation without_row :=
      (EFlatmap LikeBag (EVar bkt) rvar
         (EIf (EUnop ONot (EBinop OEq (EAccess (EVar rvar) key)
                             (EAccess (EVar tup) key)))
            (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar rvar))
            (EAtom (AEmptyBag None)))).

    Lemma flat_map_pointwise : forall (f g : value -> list value) (l : list value),
        (forall v, f v = g v) -> flat_map f l = flat_map g l.
    Proof.
      intros f g l H; induction l as [ | v l IH ]; cbn [flat_map];
        [ reflexivity | rewrite H, IH; reflexivity ].
    Qed.

    Lemma flat_map_if_singleton : forall (p : value -> bool) (l : list value),
        flat_map (fun v => if p v then cons v nil else nil) l = filter p l.
    Proof.
      induction l as [ | v l IH ]; cbn [flat_map filter]; [ reflexivity | ].
      destruct (p v); cbn [app]; rewrite IH; reflexivity.
    Qed.

    Lemma interp_without_row : forall (store env : locals) b t rv,
        map.get env bkt = Some (VBag b) ->
        map.get env tup = Some rv ->
        type_of_value (VBag b) (TBag t) ->
        interp_expr store env without_row
        = VBag (bucket_without key (proj_at key rv) b).
    Proof.
      intros store env b t rv E_bkt E_tup H_ty.
      cbn [interp_expr]; unfold get_local; rewrite E_bkt.
      erewrite flat_map_pointwise with
        (g := fun v => if keeps key (proj_at key rv) v then cons v nil else nil).
      2:{ intro v; cbn [interp_expr interp_unop interp_binop]; unfold get_local.
          rewrite map.get_put_same, map.get_put_diff by exact H_rvar_tup.
          rewrite E_tup; unfold keeps, proj_at.
          destruct (value_eqb match v with VRecord rc => record_proj key rc | _ => VUnit end
                      match rv with VRecord rc => record_proj key rc | _ => VUnit end);
            reflexivity. }
      rewrite flat_map_if_singleton.
      unfold bucket_without; f_equal.
      inversion H_ty; subst.
      apply list_to_bag_filter_bag_to_list; assumption.
    Qed.
  End WithMap.
End WithIndexUse.
