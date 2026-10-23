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
  fiat2.Utils fiat2.CollectionTransf fiat2.FlatmapTransf fiat2.EraseField
  fiat2.Constraint fiat2.DictIndexImpl fiat2.FlatmapForms
  fiat2.IndexInterface fiat2.UniqueDictIndexImpl fiat2.Surface fiat2.UniqueIndexGate
  fiat2.TransfSound fiat2.TransfUtils
  fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
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

  (* Two readings of a well-typed value, used to get at the table's rows and
     the index record's members.  Both are generic; they are restated here
     rather than imported because the copies in TrigramIndexUse sit inside
     that file's own section. *)
  Lemma type_of_value_field : forall (rv : list (string * value)) tl x (v : value) t,
      type_of_value (VRecord rv) (TRecord tl) ->
      access_record rv x = Success v ->
      access_record tl x = Success t ->
      type_of_value v t.
  Proof.
    intros * H_ty H_v H_t.
    invert_type_of_value_clear.
    lazymatch goal with H : Forall2 _ rv _ |- _ =>
      eapply Forall2_access_record; [ exact H | exact H_v | exact H_t ] end.
  Qed.

  Lemma type_of_value_TList_inv : forall (v : value) t,
      type_of_value v (TList t) ->
      exists l, v = VList l /\ Forall (fun r => type_of_value r t) l.
  Proof.
    intros v t H. inversion H; subst.
    eexists; split; [ reflexivity | assumption ].
  Qed.

  (* The row shape the index's equations are stated with, from the row type. *)
  Lemma typed_rows_are_records : forall (l : list value) rt,
      Forall (fun r => type_of_value r (TRecord rt)) l ->
      Forall (fun r => exists rc, r = VRecord rc) l.
  Proof.
    intros l rt H; rewrite Forall_forall in *; intros r H_in.
    specialize (H r H_in); inversion H; subst; eauto.
  Qed.
End WithWord.

Section WithAttrs.

  (* attr is the attribute this index buckets on; key is the primary key the
     delete names.  They are different -- when they coincide the O(1) rule
     filter_neq_to_delete_head already applies and is better. *)
  Context (attr key : string).

  (* the rows the index files under av *)
  Definition rows_at (av : value) (l : list value) : list value :=
    filter (fun r => value_eqb (row_key attr r) av) l.

  Definition idx_of (l : list value) : list (value * value) :=
    match gallina_to_idx attr (VList l) with
    | VDict d => d
    | _ => nil
    end.

  Lemma gallina_to_idx_VDict : forall l,
      gallina_to_idx attr (VList l) = VDict (idx_of l).
  Proof. intro l; unfold idx_of; cbn [gallina_to_idx]; reflexivity. Qed.

  (* One step of the index's own fold: a row joins the bucket its attribute
     names.  Named so that the expression side can be matched against it
     without unfolding gallina_to_idx twice over. *)
  Lemma idx_of_cons : forall rc l,
      idx_of (VRecord rc :: l)
      = dict_insert (record_proj attr rc)
          (VBag (bag_insert (VRecord rc)
                   match dict_lookup (record_proj attr rc) (idx_of l) with
                   | Some (VBag b) => b
                   | _ => nil
                   end)) (idx_of l).
  Proof. intros rc l; unfold idx_of; cbn [gallina_to_idx fold_right]; reflexivity. Qed.

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
    unfold row_key in *; cbn [record_proj] in *.
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

  (* Whatever bucket the index holds is a bag of the table's rows: it is the
     rows filed at that key, and they are rows of the table.  This is what
     makes a bucket filterable, and it is all the delete body needs to know
     about the dictionary it is rewriting. *)
  Lemma idx_of_bucket_typed : forall l t av bv,
      Forall (fun r => exists rc, r = VRecord rc) l ->
      Forall (fun r => type_of_value r t) l ->
      dict_lookup av (idx_of l) = Some bv ->
      type_of_value bv (TBag t).
  Proof.
    intros l t av bv H_rec H_ty H_lk.
    rewrite (idx_of_lookup l av H_rec) in H_lk.
    destruct (rows_at av l) as [ | r0 rows ] eqn:E_rows; [ discriminate | ].
    injection H_lk as H_lk; subst bv.
    (* the match reduced list_to_bag's fold one step; put it back *)
    change (bag_insert r0 (list_to_bag rows)) with (list_to_bag (r0 :: rows)).
    apply list_to_bag_sound.
    rewrite <- E_rows; unfold rows_at.
    rewrite Forall_forall in *; intros r H_in.
    apply filter_In in H_in as [ H_in _ ]; auto.
  Qed.

  (* the rows that survive a delete of the row at kv *)
  Definition keeps (kv r : value) : bool :=
    negb (value_eqb (row_key key r) kv).

  (* one bucket, with that row taken out: a filter, since a bucket is a bag
     and the language has no bag removal *)
  Definition bucket_without (kv : value) (b : list (value * nat)) :=
    filter (fun e => keeps kv (fst e)) b.

  (* and the whole index, with the row r taken out of the bucket its own
     attribute names.  The entry goes when it empties, because the index of
     a table never holds an empty bucket (idx_of_lookup). *)
  Definition unindex (kv r : value) (d : list (value * value)) :=
    match dict_lookup (row_key attr r) d with
    | Some (VBag b) =>
        match bucket_without kv b with
        | nil => dict_delete (row_key attr r) d
        | b' => dict_insert (row_key attr r) (VBag b') d
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
      destruct (value_eqb (row_key attr r) av) eqn:E_a;
      cbn [filter]; rewrite ?E_k, ?E_a, IH; reflexivity.
  Qed.

  (* With the key declared unique, the row read out of the primary-key member
     is the only one the filter removes. *)
  Lemma keeps_other : forall l r kv r',
      NoDup (map (row_key key) l) ->
      In r l -> row_key key r = kv ->
      In r' l -> r' <> r -> keeps kv r' = true.
  Proof.
    intros l r kv r' H_nd H_in E_kv H_in' H_ne.
    unfold keeps; destruct (value_eqb (row_key key r') kv) eqn:E; [ exfalso | reflexivity ].
    apply value_eqb_eq in E.
    apply H_ne, (NoDup_map_In_eq _ _ (row_key key) l r r' H_nd H_in H_in').
    rewrite E, E_kv; reflexivity.
  Qed.

  (* ==================================================================
     The delete equation.  The index of the table with the row at kv
     filtered out is the stored index with that one row taken out of the
     one bucket its own attribute names -- not rebuilt.
     ================================================================== *)
  Theorem idx_of_filter_neq_key : forall l (r kv : value),
      Forall (fun v => exists rc, v = VRecord rc) l ->
      NoDup (map (row_key key) l) ->
      In r l -> row_key key r = kv ->
      idx_of (filter (keeps kv) l) = unindex kv r (idx_of l).
  Proof.
    intros l r kv H_rec H_nd H_in E_kv.
    pose proof (Forall_rec_filter (keeps kv) l H_rec) as H_recf.
    (* r sits in the bucket its attribute names, so that bucket is there *)
    assert (E_lk : dict_lookup (row_key attr r) (idx_of l)
                   = Some (VBag (list_to_bag (rows_at (row_key attr r) l)))).
    1:{ rewrite (idx_of_lookup l _ H_rec).
        assert (H_rin : In r (rows_at (row_key attr r) l)).
        1:{ unfold rows_at; apply filter_In; split;
            [ exact H_in | apply value_eqb_refl ]. }
        destruct (rows_at (row_key attr r) l) as [ | r0 rows ];
          [ contradiction | reflexivity ]. }
    apply dict_wf_lookup_ext; [ apply idx_of_dict_wf | | ].
    1:{ unfold unindex; rewrite E_lk.
        destruct (bucket_without kv (list_to_bag (rows_at (row_key attr r) l)));
          [ apply dict_delete_preserve_dict_wf | apply dict_insert_preserve_dict_wf ];
          apply idx_of_dict_wf. }
    intros av.
    rewrite (idx_of_lookup _ av H_recf), rows_at_filter.
    unfold unindex; rewrite E_lk.
    replace (bucket_without kv (list_to_bag (rows_at (row_key attr r) l)))
      with (list_to_bag (filter (keeps kv) (rows_at (row_key attr r) l)))
      by (unfold bucket_without; apply list_to_bag_filter).
    destruct (value_eqb av (row_key attr r)) eqn:E_av.
    - (* the bucket the row leaves *)
      apply value_eqb_eq in E_av; subst av.
      destruct (filter (keeps kv) (rows_at (row_key attr r) l)) as [ | r0 rows ] eqn:E_f.
      + cbn [list_to_bag fold_right].
        rewrite dict_lookup_delete_same; [ reflexivity | apply idx_of_dict_wf ].
      + destruct (list_to_bag (r0 :: rows)) as [ | e b ] eqn:E_b.
        1:{ exfalso; cbn [list_to_bag fold_right] in E_b.
            eapply bag_insert_not_nil, E_b. }
        rewrite dict_lookup_insert_same; reflexivity.
    - (* every other bucket: untouched, and nothing in it leaves *)
      assert (H_ne : av <> row_key attr r) by (apply value_eqb_neq; exact E_av).
      assert (E_keep : filter (keeps kv) (rows_at av l) = rows_at av l).
      1:{ apply filter_all_true; intros r' H_r'.
          unfold rows_at in H_r'; apply filter_In in H_r' as [ H_r'l E_r'a ].
          apply (keeps_other l r kv r' H_nd H_in E_kv H_r'l).
          intro E; subst r'; apply H_ne.
          symmetry; apply value_eqb_eq; exact E_r'a. }
      rewrite E_keep.
      destruct (filter (keeps kv) (rows_at (row_key attr r) l)) as [ | r0 rows ].
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
      (forall r, In r l -> row_key key r <> kv) ->
      idx_of (filter (keeps kv) l) = idx_of l.
  Proof.
    intros l kv H; f_equal.
    apply filter_all_true; intros r H_in; unfold keeps.
    destruct (value_eqb (row_key key r) kv) eqn:E; [ exfalso | reflexivity ].
    apply (H r H_in), value_eqb_eq, E.
  Qed.

End WithAttrs.



(* ====================================================================
   The rule: a keyed delete, read off two members of one index record.

   The shape is TrigramIndexUse.filter_neq_to_tri_delete_head's, with the
   trigrams of a row's text replaced by one attribute of the row.  The
   dictionary member buckets on attr; the delete names key; so the row that
   is leaving is not in the expression at all, only its key is, and the rule
   reads the row out of the primary-key member.  That is also why it is
   sound only where the key is declared unique: with two rows at one key,
   taking one row's contributions out would lose the other's.
   ==================================================================== *)
Section WithRule.
  (* the dictionary index's own binders and the attribute it buckets on *)
  Context (hole attr : string).
  Context (dk : dict_kind).
  Context (tup acc x : string).
  Context (H_NoDup : is_NoDup_opaque [tup; acc; x]).
  (* The primary-key index's binders, and the attribute the delete names.
     Only this index can turn a key back into the row that carries it, and
     the two indexes have to agree on which attribute that is. *)
  Context (key utup uacc : string).
  Context (H_utup_uacc : utup <> uacc).
  (* the two fields the installation pairs *)
  Context (id_tag aux_tag : string).
  (* the tags the two dictionaries sit under inside one index record *)
  Context (idx_tag pk_tag : string).
  (* the binders the rewritten delete introduces: a bucket, and a row of it *)
  Context (bkt rvar : string).
  Context (H_tup_rvar : tup <> rvar) (H_tup_bkt : tup <> bkt) (H_acc_bkt : acc <> bkt).

  Notation didx := (dict_idx hole attr dk tup acc x).
  Notation uidx := (unique_dict_idx hole key utup uacc).

  (* The index states its binders' distinctness as one opaque is_NoDup,
     which is awkward in a side condition; it is taken apart once here. *)
  Lemma tup_neq_acc : tup <> acc.
  Proof. use_is_NoDup. Qed.

  (* The table shape the dictionary index demands, as an inversion. *)
  Lemma dict_is_tbl_ty_inv : forall t,
      @IndexInterface.is_tbl_ty didx t = true ->
      exists rt at_ty, t = TList (TRecord rt)
                       /\ access_record rt attr = Success at_ty.
  Proof.
    cbn [IndexInterface.is_tbl_ty dict_idx]; unfold DictIndexImpl.is_tbl_ty.
    intros t H.
    destruct t as [ | | | | | t1 | | | | ]; try discriminate.
    destruct t1 as [ | | | | | | rt | | | ]; try discriminate.
    rewrite inb_true_iff in H; apply In_access_record in H as [ at_ty E_attr ].
    exists rt, at_ty; split; [ reflexivity | exact E_attr ].
  Qed.

  (* The same for the primary-key member.  The dictionary index's own
     is_tbl_ty says nothing about key -- it buckets on attr -- so a rule
     that reads the key off a row has to be told separately that the row
     carries one, and the natural way to say it is that the primary-key
     member is installable on the same table. *)
  Lemma unique_is_tbl_ty_inv : forall t,
      @IndexInterface.is_tbl_ty uidx t = true ->
      exists rt kt, t = TList (TRecord rt)
                    /\ access_record rt key = Success kt.
  Proof.
    cbn [IndexInterface.is_tbl_ty unique_dict_idx];
      unfold UniqueDictIndexImpl.is_tbl_ty.
    intros t H.
    destruct t as [ | | | | | t1 | | | | ]; try discriminate.
    destruct t1 as [ | | | | | | rt | | | ]; try discriminate.
    rewrite inb_true_iff in H; apply In_access_record in H as [ kt E_key ].
    exists rt, kt; split; [ reflexivity | exact E_key ].
  Qed.

  (* The rules' kind test, as an equation oriented so that the PATTERN's
     kind disappears: rewriting the other way would eliminate the section
     variable dk and with it every definition mentioning it. *)
  Ltac use_dk_beq :=
    repeat lazymatch goal with
        H: dict_kind_beq dk ?d = true |- _ =>
          apply dict_kind_beq_eq in H; rewrite <- H in *; clear H
      end.

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Notation value := (value).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    (* ----------------------------------------------------------------
       The expression side: what the bucket rewrite computes.
       ---------------------------------------------------------------- *)
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
        = VBag (bucket_without key (row_key key rv) b).
    Proof.
      intros store env b t rv E_bkt E_tup H_ty.
      cbn [interp_expr]; unfold get_local; rewrite E_bkt.
      erewrite flat_map_pointwise with
        (g := fun v => if keeps key (row_key key rv) v then cons v nil else nil).
      2:{ intro v; cbn [interp_expr interp_unop interp_binop]; unfold get_local.
          rewrite map.get_put_same, map.get_put_diff by exact H_tup_rvar.
          rewrite E_tup; unfold keeps, row_key.
          destruct (value_eqb match v with VRecord rc => record_proj key rc | _ => VUnit end
                      match rv with VRecord rc => record_proj key rc | _ => VUnit end);
            reflexivity. }
      rewrite flat_map_if_singleton.
      unfold bucket_without; f_equal.
      inversion H_ty; subst.
      apply list_to_bag_filter_bag_to_list; assumption.
    Qed.

    (* Reading a binder whose value is known. *)
    Lemma interp_EVar_get : forall (store env : locals) y (v : value),
        map.get env y = Some v -> interp_expr store env (EVar y) = v.
    Proof.
      intros store env y v E; rewrite interp_EVar; unfold get_local.
      rewrite E; reflexivity.
    Qed.

    (* Reading one attribute off a row bound to a binder.  row_key is the
       same match, so this is the bridge between the expression's EAccess
       and the Gallina key the equations above are stated with. *)
    Lemma interp_row_attr : forall (store env : locals) (y a : string) rv,
        map.get env y = Some rv ->
        interp_expr store env (EAccess (EVar y) a) = row_key a rv.
    Proof.
      intros store env y a rv E_y.
      rewrite interp_EAccess, interp_EVar; unfold get_local; rewrite E_y.
      unfold row_key; destruct rv; reflexivity.
    Qed.

    (* ------------------------------------------------------------------
       The whole per-row update: find the bucket the leaving row's own
       attribute names, take the row out of it, and put the shortened
       bucket back -- or delete the entry if the row was the last one in
       it, since the index of a table never holds an empty bucket.

       without_row is spelled twice rather than bound to a name, following
       TrigramIndexImpl.tri_without_pk: a let would cost every rule that
       matches this body one more binder to be told about, and a bucket is
       small enough to filter twice.
       ------------------------------------------------------------------ *)
    (* ELet's step rule.  The trigram file has its own copy; this is the
       same one-liner, kept here so this file does not depend on it. *)
    Lemma interp_ELet_step : forall (store env : locals) e1 y e2,
        interp_expr store env (ELet e1 y e2)
        = interp_expr store (map.put env y (interp_expr store env e1)) e2.
    Proof. reflexivity. Qed.

    Notation bucket_key := (EAccess (EVar tup) attr).

    Notation dict_row_delete_body :=
      (EOptMatch (EBinop OLookup (EVar acc) bucket_key)
         (EVar acc)
         bkt
         (EIf (EBinop OEq without_row (EAtom (AEmptyBag None)))
            (EBinop ODelete (EVar acc) bucket_key)
            (ETernop OInsert (EVar acc) bucket_key without_row))).

    (* What that body computes.  The one premise is that the bucket the
       leaving row's attribute names, if there is one, is a bag of rows --
       which is what makes it filterable, and what idx_of_bucket_typed says
       of an index built from a table. *)
    Lemma interp_dict_row_delete : forall (store env : locals) d rv t,
        map.get env acc = Some (VDict d) ->
        map.get env tup = Some rv ->
        (forall bv, dict_lookup (row_key attr rv) d = Some bv ->
                    type_of_value bv (TBag t)) ->
        interp_expr store env dict_row_delete_body
        = VDict (unindex attr key (row_key key rv) rv d).
    Proof.
      intros store env d rv t E_acc E_tup H_bags.
      rewrite interp_EOptMatch, interp_EBinop, interp_EVar.
      unfold get_local; rewrite E_acc.
      rewrite (interp_row_attr store env tup attr rv E_tup).
      cbn [interp_binop].
      unfold unindex.
      destruct (dict_lookup (row_key attr rv) d) as [ bv | ] eqn:E_lk.
      (* the none branch is the accumulator itself, already read above *)
      2: reflexivity.
      (* the bucket is a bag, by the premise -- which the destruct above
         has already specialised to this lookup *)
      assert (H_bv : type_of_value bv (TBag t)) by (apply H_bags; reflexivity).
      assert (H_bag : exists b, bv = VBag b) by (inversion H_bv; eauto).
      destruct H_bag as [ b E_bv ]; subst bv.
      (* the shortened bucket, the same on both branches of the test *)
      assert (E_wo : interp_expr store (map.put env bkt (VBag b)) without_row
                     = VBag (bucket_without key (row_key key rv) b)).
      1:{ apply (interp_without_row _ _ b t);
          [ apply map.get_put_same
          | rewrite map.get_put_diff by exact H_tup_bkt; exact E_tup
          | exact H_bv ]. }
      rewrite interp_EIf, interp_EBinop, E_wo, interp_EAtom.
      cbn [interp_atom interp_binop].
      destruct (bucket_without key (row_key key rv) b) as [ | e b' ] eqn:E_bw.
      - (* the row was the last one in its bucket, so the entry goes *)
        rewrite value_eqb_refl.
        rewrite interp_EBinop, interp_EVar; unfold get_local.
        rewrite map.get_put_diff by exact H_acc_bkt; rewrite E_acc.
        rewrite (interp_row_attr _ _ tup attr rv)
          by (rewrite map.get_put_diff by exact H_tup_bkt; exact E_tup).
        reflexivity.
      - (* and otherwise the shortened bucket goes back in its place *)
        destruct (value_eqb (VBag (e :: b')) (VBag nil)) eqn:E_eq.
        1:{ exfalso; apply value_eqb_eq in E_eq; discriminate. }
        rewrite interp_ETernop, interp_EVar, E_wo; unfold get_local.
        rewrite map.get_put_diff by exact H_acc_bkt; rewrite E_acc.
        rewrite (interp_row_attr _ _ tup attr rv)
          by (rewrite map.get_put_diff by exact H_tup_bkt; exact E_tup).
        reflexivity.
    Qed.

    (* ----------------------------------------------------------------
       The emitted forms, typed.  Each body is given its own lemma rather
       than rebuilt inside every rule: the derivations are deterministic,
       and writing them down is what records which types the index fixes.
       ---------------------------------------------------------------- *)
    Lemma without_row_ty : forall rt kt (Gstore Genv : tenv),
        access_record rt key = Success kt ->
        map.get Genv bkt = Some (TBag (TRecord rt)) ->
        map.get Genv tup = Some (TRecord rt) ->
        type_wf (TRecord rt) ->
        type_of Gstore Genv without_row (TBag (TRecord rt)).
    Proof.
      intros rt kt Gstore Genv E_key E_bkt E_tup H_rtwf.
      eapply TyEFlatmap_Bag; [ apply TyEVar; exact E_bkt | ].
      apply TyEIf.
      1:{ eapply TyEUnop; [ apply TyONot | ].
          eapply TyEBinop; [ apply TyOEq | | ].
          1:{ eapply TyEAccess;
              [ apply TyEVar; apply map.get_put_same | exact E_key ]. }
          1:{ eapply TyEAccess; [ apply TyEVar | exact E_key ].
              rewrite map.get_put_diff by exact H_tup_rvar; exact E_tup. } }
      1:{ eapply TyEBinop; [ apply TyOBagInsert | | ].
          1: apply TyEAtom; apply TyAEmptyBag'; exact H_rtwf.
          1: apply TyEVar; apply map.get_put_same. }
      1: apply TyEAtom; apply TyAEmptyBag'; exact H_rtwf.
    Qed.

    Lemma dict_row_delete_body_ty : forall rt at_ty kt (Gstore Genv : tenv),
        access_record rt attr = Success at_ty ->
        access_record rt key = Success kt ->
        map.get Genv tup = Some (TRecord rt) ->
        map.get Genv acc = Some (TDict dk at_ty (TBag (TRecord rt))) ->
        type_wf (TRecord rt) ->
        type_of Gstore Genv dict_row_delete_body
          (TDict dk at_ty (TBag (TRecord rt))).
    Proof.
      intros rt at_ty kt Gstore Genv E_attr E_key E_tup E_acc H_rtwf.
      (* the two reads that pass under the bucket's binder *)
      assert (E_tup' : map.get (map.put Genv bkt (TBag (TRecord rt))) tup
                       = Some (TRecord rt))
        by (rewrite map.get_put_diff by exact H_tup_bkt; exact E_tup).
      assert (E_acc' : map.get (map.put Genv bkt (TBag (TRecord rt))) acc
                       = Some (TDict dk at_ty (TBag (TRecord rt))))
        by (rewrite map.get_put_diff by exact H_acc_bkt; exact E_acc).
      assert (H_wo : type_of Gstore (map.put Genv bkt (TBag (TRecord rt)))
                       without_row (TBag (TRecord rt)))
        by (eapply without_row_ty;
            [ exact E_key | apply map.get_put_same | exact E_tup' | exact H_rtwf ]).
      eapply TyEOptMatch.
      1:{ eapply TyEBinop; [ apply TyOLookup | | ].
          1: apply TyEVar; exact E_acc.
          1: eapply TyEAccess; [ apply TyEVar; exact E_tup | exact E_attr ]. }
      1: apply TyEVar; exact E_acc.
      apply TyEIf.
      1:{ eapply TyEBinop; [ apply TyOEq | exact H_wo | ].
          apply TyEAtom; apply TyAEmptyBag'; exact H_rtwf. }
      1:{ eapply TyEBinop; [ apply TyODelete | | ].
          1: apply TyEVar; exact E_acc'.
          1: eapply TyEAccess; [ apply TyEVar; exact E_tup' | exact E_attr ]. }
      1:{ eapply TyETernop; [ apply TyOInsert | | | ].
          1: apply TyEVar; exact E_acc'.
          1: eapply TyEAccess; [ apply TyEVar; exact E_tup' | exact E_attr ].
          1: exact H_wo. }
    Qed.

    (* The two invariants the rule reads off the store, each at its own tag.
       The dictionary member asks only for its own idx_wf, which the install
       manufactures from typing; the primary-key member asks for the STRONG
       relation, which no index establishes and which the declaration pays
       for. *)
    Notation idx_aux_wf_at :=
      (aux_wf_for_idx id_tag aux_tag idx_tag
         (DictIndexImpl.idx_wf hole attr dk tup acc x (locals := locals))).
    Notation unique_aux_wf_at :=
      (aux_wf_for_idx id_tag aux_tag pk_tag
         (UniqueDictIndexImpl.idx_wf_unique hole key utup uacc (locals := locals))).

    (* ------------------------------------------------------------------
       Everything the rule needs about the store, read off the two
       invariants and the store's type at once: the table's rows with their
       type, both members as Gallina mirrors of those rows, and the
       distinctness of the keys -- the one part no index establishes from
       typing, and what the declaration is spent on.
       ------------------------------------------------------------------ *)
    Lemma invariants__idx_data :
      forall tl rt (v : value),
        type_wf (TList (TRecord rt)) ->
        DictIndexImpl.is_tbl_ty attr (TList (TRecord rt)) = true ->
        access_record tl id_tag = Success (TList (TRecord rt)) ->
        type_of_value v (TRecord tl) ->
        idx_aux_wf_at v ->
        unique_aux_wf_at v ->
        exists rv rv_aux rows,
          v = VRecord rv
          /\ record_proj id_tag rv = VList rows
          /\ record_proj aux_tag rv = VRecord rv_aux
          /\ record_proj idx_tag rv_aux = VDict (idx_of attr rows)
          /\ record_proj pk_tag rv_aux
             = VDict (UniqueDictIndexImpl.idx_entries key rows)
          /\ Forall (fun r => type_of_value r (TRecord rt)) rows
          /\ NoDup (List.map (row_key key) rows).
    Proof.
      unfold aux_wf_for_idx, UniqueDictIndexImpl.idx_wf_unique,
        UniqueDictIndexImpl.idx_wf, UniqueDictIndexImpl.keys_distinct,
        DictIndexImpl.idx_wf.
      intros tl rt v H_twf H_is E_id.
      (* v is destructed before the invariants are introduced, so that their
         names survive; each later destruct is pushed into them by hand,
         since destruct rewrites the goal but not hypotheses *)
      destruct v as [ | | | | | rv | | | | ];
        intros H_vty H_idx H_pk;
        cbv beta iota in H_idx, H_pk; try contradiction.
      destruct (access_record rv id_tag) as [ v_id | ] eqn:E_vid;
        cbv beta iota in H_idx, H_pk; try contradiction.
      destruct (access_record rv aux_tag) as [ v_aux | ] eqn:E_vaux;
        cbv beta iota in H_idx, H_pk; try contradiction.
      destruct v_aux as [ | | | | | rv_aux | | | | ];
        cbv beta iota in H_idx, H_pk; try contradiction.
      destruct (access_record rv_aux idx_tag) as [ v_idx | ] eqn:E_vidx;
        cbv beta iota in H_idx; try contradiction.
      destruct (access_record rv_aux pk_tag) as [ v_pk | ] eqn:E_vpk;
        cbv beta iota in H_pk; try contradiction.
      destruct H_pk as [ E_pk H_kd ].
      (* the table's own rows, and their typing *)
      assert (H_idty : type_of_value v_id (TList (TRecord rt)))
        by (eapply type_of_value_field; [ exact H_vty | exact E_vid | exact E_id ]).
      apply type_of_value_TList_inv in H_idty as [ rows [ E_rows H_rows ] ].
      subst v_id.
      cbn [UniqueDictIndexImpl.keys_distinct] in H_kd.
      (* and both dictionaries are their own mirrors *)
      rewrite (DictIndexImpl.fiat2_gallina_to_idx hole attr dk tup acc x H_NoDup
                 (locals_ok := locals_ok) (VList rows) (TList (TRecord rt))
                 H_twf H_is (TyVList _ _ H_rows)) in H_idx.
      rewrite gallina_to_idx_VDict in H_idx.
      rewrite (UniqueDictIndexImpl.fiat2_gallina_to_idx hole key utup uacc
                 H_utup_uacc (locals_ok := locals_ok) rows) in E_pk.
      exists rv, rv_aux, rows.
      repeat split; try assumption;
        try (apply access_record__record_proj; assumption).
      1:{ apply access_record__record_proj. rewrite E_vidx, H_idx. reflexivity. }
      1:{ apply access_record__record_proj. rewrite E_vpk, E_pk. reflexivity. }
    Qed.

    (* ------------------------------------------------------------------
       The rebuild, as the rule has to match it, and what it computes.

       to_idx_at is the index's own to_idx with the table read in place of
       the hole, so nothing about bucketing has to be re-proved; the fold
       lemma below just says the expression's fold is gallina_to_idx's.
       ------------------------------------------------------------------ *)
    Notation dict_row_insert_body :=
      (ETernop OInsert (EVar acc) (EAccess (EVar tup) attr)
         (EBinop OBagInsert
            (EOptMatch (EBinop OLookup (EVar acc) (EAccess (EVar tup) attr))
               (EAtom (AEmptyBag None)) x (EVar x))
            (EVar tup))).

    Definition to_idx_at (d : expr) : expr :=
      EFold d (EAtom (AEmptyDict dk None)) tup acc dict_row_insert_body.

    Lemma dict_row_insert_body_ty : forall rt at_ty (Gstore Genv : tenv),
        access_record rt attr = Success at_ty ->
        map.get Genv tup = Some (TRecord rt) ->
        map.get Genv acc = Some (TDict dk at_ty (TBag (TRecord rt))) ->
        type_wf (TRecord rt) ->
        type_of Gstore Genv dict_row_insert_body
          (TDict dk at_ty (TBag (TRecord rt))).
    Proof.
      intros rt at_ty Gstore Genv E_attr E_tup E_acc H_rtwf.
      eapply TyETernop; [ apply TyOInsert | | | ].
      1: apply TyEVar; exact E_acc.
      1: eapply TyEAccess; [ apply TyEVar; exact E_tup | exact E_attr ].
      eapply TyEBinop; [ apply TyOBagInsert | | ].
      2: apply TyEVar; exact E_tup.
      eapply TyEOptMatch.
      1:{ eapply TyEBinop; [ apply TyOLookup | | ].
          1: apply TyEVar; exact E_acc.
          1: eapply TyEAccess; [ apply TyEVar; exact E_tup | exact E_attr ]. }
      1: apply TyEAtom; apply TyAEmptyBag'; exact H_rtwf.
      1: apply TyEVar; apply map.get_put_same.
    Qed.

    Lemma to_idx_at_ty : forall rt at_ty (Gstore Genv : tenv) (d : expr),
        access_record rt attr = Success at_ty ->
        type_wf (TRecord rt) ->
        type_of Gstore Genv d (TList (TRecord rt)) ->
        type_of Gstore Genv (to_idx_at d) (TDict dk at_ty (TBag (TRecord rt))).
    Proof.
      intros rt at_ty Gstore Genv d E_attr H_rtwf H_d.
      assert (H_atwf : type_wf at_ty).
      1:{ replace at_ty with (get_attr_type rt attr)
            by (unfold get_attr_type; rewrite E_attr; reflexivity).
          apply get_attr_type_ty_wf; exact H_rtwf. }
      unfold to_idx_at. eapply TyEFold.
      1: exact H_d.
      1: apply TyEAtom; apply TyAEmptyDict';
         [ exact H_atwf | constructor; exact H_rtwf ].
      eapply dict_row_insert_body_ty.
      1: exact E_attr.
      1:{ rewrite map.get_put_diff by exact tup_neq_acc; apply map.get_put_same. }
      1: apply map.get_put_same.
      1: exact H_rtwf.
    Qed.

    Lemma interp_to_idx_fold : forall (store env : locals) (l : list value),
        Forall (fun r => exists rc, r = VRecord rc) l ->
        fold_right
          (fun r a => interp_expr store (map.put (map.put env tup r) acc a)
                        dict_row_insert_body)
          (VDict nil) l
        = VDict (idx_of attr l).
    Proof.
      intros store env l H_rec.
      induction H_rec as [ | r l [ rc E_r ] H_l IH ]; [ reflexivity | ].
      subst r; cbn [fold_right]; rewrite IH, idx_of_cons.
      (* the row, read through the accumulator's binder *)
      assert (E_tup : map.get (map.put (map.put env tup (VRecord rc)) acc
                                 (VDict (idx_of attr l))) tup
                      = Some (VRecord rc)).
      1:{ rewrite map.get_put_diff by exact tup_neq_acc. apply map.get_put_same. }
      rewrite interp_ETernop, (interp_EVar_get _ _ acc (VDict (idx_of attr l)))
        by apply map.get_put_same.
      rewrite (interp_row_attr _ _ tup attr (VRecord rc) E_tup).
      unfold row_key; cbn [record_proj].
      rewrite interp_EBinop, interp_EOptMatch, interp_EBinop,
        (interp_EVar_get _ _ acc (VDict (idx_of attr l))) by apply map.get_put_same.
      rewrite (interp_row_attr _ _ tup attr (VRecord rc) E_tup).
      unfold row_key; cbn [record_proj interp_binop].
      (* the bucket the row joins: there, or absent, never anything else *)
      rewrite (idx_of_lookup attr l _ H_l).
      destruct (rows_at attr (record_proj attr rc) l) as [ | r0 rows ].
      - rewrite interp_EAtom; cbn [interp_atom interp_binop].
        rewrite (interp_EVar_get _ _ tup (VRecord rc) E_tup).
        cbn [interp_ternop]; reflexivity.
      - rewrite (interp_EVar_get _ _ x (VBag (list_to_bag (r0 :: rows))))
          by apply map.get_put_same.
        cbn [interp_binop].
        (* the inserted row is read outside the bucket's binder *)
        rewrite (interp_EVar_get _ _ tup (VRecord rc) E_tup).
        cbn [interp_ternop]; reflexivity.
    Qed.

    Lemma interp_to_idx_at :
      forall (store env : locals) (d : expr) (rows : list value),
        Forall (fun r => exists rc, r = VRecord rc) rows ->
        interp_expr store env d = VList rows ->
        interp_expr store env (to_idx_at d) = VDict (idx_of attr rows).
    Proof.
      intros store env d rows H_rec E_d.
      unfold to_idx_at.
      rewrite interp_EFold, E_d, interp_EAtom; cbn [interp_atom].
      apply interp_to_idx_fold; exact H_rec.
    Qed.

    Section WithTable.
      (* the store location the index record sits at *)
      Context (tbl : string).

      Notation pk_e := (EAccess (EAccess (ELoc tbl) aux_tag) pk_tag).

      (* Reading one of the index record's fields out of the store. *)
      Lemma interp_tbl_field : forall (store env : locals) rv rv_aux t2 (w : value),
          map.get store tbl = Some (VRecord rv) ->
          record_proj aux_tag rv = VRecord rv_aux ->
          record_proj t2 rv_aux = w ->
          interp_expr store env (EAccess (EAccess (ELoc tbl) aux_tag) t2) = w.
      Proof.
        intros * E_v E_aux E_f.
        rewrite interp_EAccess, interp_EAccess, interp_ELoc.
        unfold get_local; rewrite E_v; cbv beta iota.
        rewrite E_aux; cbv beta iota.
        rewrite E_f; reflexivity.
      Qed.

      (* ------------------------------------------------------------------
         Maintaining the index when a row goes.

         A filter-shaped delete: keep the rows whose key is not k.  The row
         that leaves is not in the expression at all -- only its key is --
         so the rule reads it out of the PRIMARY-KEY member, and then takes
         it out of the one bucket its own attribute names.

         The side condition key <> attr is not needed for soundness: when
         the two coincide this rule is still correct, but the whole bucket
         leaves and DictIndexImpl.filter_neq_to_delete_head does it with one
         ODelete and no probe.  The guard keeps the two rules from racing.
         ------------------------------------------------------------------ *)

      (* to_idx_at spelled out, so that the rule can match it.  Every
         binder, attribute and kind occurrence is a pattern variable, and
         the guard checks that they are the ones this index uses. *)
      Notation edict_idx dk0 tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1 d :=
        (EFold d (EAtom (AEmptyDict dk0 None)) tup0 acc0
           (ETernop OInsert (EVar acc1) (EAccess (EVar tup1) attr0)
              (EBinop OBagInsert
                 (EOptMatch (EBinop OLookup (EVar acc2) (EAccess (EVar tup2) attr1))
                    (EAtom (AEmptyBag None)) x0 (EVar x1))
                 (EVar tup3)))).

      Definition filter_neq_to_keyed_delete_head (e : expr) : expr :=
        match e with
        | edict_idx dk0 tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1
            (flatmap_filter_list (EAccess (ELoc tbl0) id_tag0) y0
               (EUnop ONot (EBinop OEq (EAccess (EVar y1) key0) kexp)) y2 _ _) =>
            if (dict_kind_beq dk dk0
                && all_eqb [(tup, [tup0; tup1; tup2; tup3]);
                            (acc, [acc0; acc1; acc2]); (x, [x0; x1]);
                            (attr, [attr0; attr1]); (key, [key0]);
                            (tbl, [tbl0]); (id_tag, [id_tag0]); (y0, [y1; y2])]
                && negb (String.eqb key attr)
                && negb (free_immut_in y0 kexp)
                && negb (free_immut_in acc kexp))%bool
            then ELet (to_idx_at (EAccess (ELoc tbl) id_tag)) acc
                   (EOptMatch (EBinop OLookup pk_e kexp) (EVar acc) tup
                      dict_row_delete_body)
            else e
        | _ => e
        end.

      Lemma filter_neq_to_keyed_delete_head_preserve_ty :
        forall tl ctl t (Gstore : tenv),
          type_wf t ->
          @IndexInterface.is_tbl_ty didx t = true ->
          @IndexInterface.is_tbl_ty uidx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl pk_tag = Success (@IndexInterface.idx_ty uidx t) ->
          preserve_ty Gstore filter_neq_to_keyed_delete_head.
      Proof.
        unfold preserve_ty.
        intros tl ctl t Gstore H_twf H_isd H_isu E_tbl E_id E_aux E_pk.
        (* the table type's shape, from the two members' is_tbl_ty *)
        apply dict_is_tbl_ty_inv in H_isd as [ rt [ at_ty [ E_t E_attr ] ] ].
        subst t.
        apply unique_is_tbl_ty_inv in H_isu as [ rt' [ kt [ E_t' E_key ] ] ].
        injection E_t' as E_t'; subst rt'.
        cbn [IndexInterface.idx_ty unique_dict_idx UniqueDictIndexImpl.idx_ty]
          in E_pk.
        (* the primary-key member's key type, spelled the way the source
           spells it: the source accesses the field, the index's idx_ty
           names it through get_attr_type *)
        assert (E_kt : get_attr_type rt key = kt)
          by (unfold get_attr_type; rewrite E_key; reflexivity).
        rewrite E_kt in E_pk. clear E_kt.
        assert (H_rtwf : type_wf (TRecord rt)) by (inversion H_twf; assumption).
        intros e t' Genv H_Gs H_Ge H_t.
        repeat destruct_subexpr.
        cbn [filter_neq_to_keyed_delete_head]. repeat (case_match; auto; []).
        cbn in * |-.
        rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition idtac.
        use_dk_beq.
        rewrite eqb_eq in *; subst.
        (* the source's typing, taken apart for the types it fixes: the
           dictionary's, the row's, and the deleted key's.  Nothing of the
           source's own derivation is reused -- the emitted form is built
           from the typing lemmas above -- so this may consume everything. *)
        repeat invert_type_of_clear. repeat invert_type_of_op_clear.
        (* rewrite_map_get_put_hyp discharges map.get_put_diff's side
           condition with (simpl in *; intuition auto), which reads the
           CONTEXT only.  This section's variables are kept apart by
           is_NoDup_opaque, which is opaque by construction, so the side
           condition would survive as a goal whose context still holds
           rewritable hypotheses -- and the repeat would then spawn side
           goals without end.  Putting the disequalities in the context
           first is what makes the tactic terminate.  map.get_put_diff
           wants put-key <> looked-up-key, so both orientations go in. *)
        assert (H_tup_acc : tup <> acc) by use_is_NoDup.
        assert (H_acc_tup : acc <> tup) by (apply not_eq_sym; use_is_NoDup).
        assert (H_tup_x : tup <> x) by use_is_NoDup.
        assert (H_x_tup : x <> tup) by (apply not_eq_sym; use_is_NoDup).
        assert (H_acc_x : acc <> x) by use_is_NoDup.
        assert (H_x_acc : x <> acc) by (apply not_eq_sym; use_is_NoDup).
        repeat rewrite_map_get_put_hyp.
        repeat (try clear_refl; repeat do_injection).
        (* the table read fixes the row type, which fixes the attribute's
           and the key's.  match, not lazymatch: the first hypothesis of
           each shape is the one this lemma was given, and rewriting it with
           itself fails, so the search has to go on to the inverted copy. *)
        match goal with
        | H : map.get Gstore tbl = Some (TRecord _) |- _ =>
            rewrite E_tbl in H; injection H as H; subst
        end.
        match goal with
        | H : access_record _ id_tag = Success (TList _) |- _ =>
            rewrite E_id in H; injection H as H; subst
        end.
        repeat match goal with
               | H : Some _ = Some _ |- _ => injection H as H; subst
               end.
        repeat match goal with
               | H : access_record _ attr = Success ?t0 |- _ =>
                   is_var t0; rewrite E_attr in H; injection H as H; subst t0
               | H : access_record _ key = Success ?t0 |- _ =>
                   is_var t0; rewrite E_key in H; injection H as H; subst t0
               end.
        (* the empty-dictionary literal names the kind, so inverting its
           typing is what collapses the source's kind onto the index's *)
        repeat match goal with
               | H : type_of_atom (AEmptyDict _ _) _ |- _ =>
                   inversion H; subst; clear H
               end.
        (* and now the emitted form, from the typing lemmas above *)
        eapply TyELet.
        1:{ eapply to_idx_at_ty; [ exact E_attr | exact H_rtwf | ].
            eapply TyEAccess; [ apply TyELoc; exact E_tbl | exact E_id ]. }
        eapply TyEOptMatch.
        1:{ (* the deleted row, from the primary-key member *)
            eapply TyEBinop; [ apply TyOLookup | | ].
            1:{ eapply TyEAccess;
                [ eapply TyEAccess; [ apply TyELoc; exact E_tbl | exact E_aux ]
                | exact E_pk ]. }
            1:{ apply not_free_immut_put_ty2; [ assumption | ].
                eapply not_free_immut_put_ty; [ eassumption | eassumption ]. } }
        1:{ apply TyEVar; rewrite map.get_put_same; reflexivity. }
        1:{ eapply dict_row_delete_body_ty.
            1: exact E_attr.
            1: exact E_key.
            1: apply map.get_put_same.
            1:{ rewrite map.get_put_diff by (apply not_eq_sym; exact tup_neq_acc).
                apply map.get_put_same. }
            1: exact H_rtwf. }
      Qed.

      (* =================================================================
         The rule computes what the source computes.

         The source rebuilds the whole index from the filtered table.  The
         emitted form rebuilds it from the whole table and then takes one
         row out of the single bucket that row's attribute names.  The two
         agree because at most one row carries the deleted key, which is
         exactly what the primary-key member's NoDup pays for: on the hit
         branch through idx_of_filter_neq_key, on the miss branch through
         idx_of_filter_neq_absent.
         ================================================================= *)
      Lemma filter_neq_to_keyed_delete_head_preserve_sem :
        forall tl rt (Gstore : tenv) (store : locals),
          type_wf (TList (TRecord rt)) ->
          DictIndexImpl.is_tbl_ty attr (TList (TRecord rt)) = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          match map.get store tbl with
          | Some v =>
              type_of_value v (TRecord tl) /\ idx_aux_wf_at v /\ unique_aux_wf_at v
          | _ => False
          end ->
          preserve_sem Gstore store filter_neq_to_keyed_delete_head.
      Proof.
        unfold preserve_sem; intros * H_twf H_is E_tbl E_id H_store.
        intros e t Genv env H_Gs H_Ge H_t H_sw H_ew.
        destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
        destruct H_store as [ H_vty [ H_idx H_pk ] ].
        destruct (invariants__idx_data tl rt v H_twf H_is E_id H_vty H_idx H_pk)
          as [ rv [ rv_aux [ rows [ E_vrec [ E_rows [ E_aux
             [ E_idx [ E_pkf [ H_rows H_nd ] ] ] ] ] ] ] ] ].
        subst v.
        (* the rows are records, which both to_idx and the bucket lemmas need *)
        pose proof (typed_rows_are_records rows rt H_rows) as H_rec.
        repeat destruct_subexpr.
        cbn [filter_neq_to_keyed_delete_head]. repeat (case_match; auto; []).
        cbn in * |-.
        rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition idtac.
        use_dk_beq.
        rewrite eqb_eq in *; subst.
        (* the deleted key's expression, which destruct_subexpr named for us *)
        lazymatch goal with pe : expr |- _ => rename pe into kexp end.
        (* the table read, which both sides start from *)
        assert (E_tr : interp_expr store env (EAccess (ELoc tbl) id_tag)
                       = VList rows).
        1:{ rewrite interp_EAccess, interp_ELoc.
            unfold get_local; rewrite E_v; cbv beta iota. exact E_rows. }
        (* The source, settled first and separately: destruct_subexpr has
           spelled its fold out, so only conversion relates it to to_idx_at
           and rewrite's syntactic match would not see it. *)
        lazymatch goal with
        | |- _ = interp_expr store env ?src =>
            assert (E_src : interp_expr store env src
                            = VDict (idx_of attr
                                       (filter (keeps key
                                                  (interp_expr store env kexp))
                                          rows)))
        end.
        1:{ apply (interp_to_idx_at store env _ _
                     (Forall_rec_filter _ rows H_rec)).
            rewrite interp_flatmap_filter_list, E_tr.
            rewrite FlatmapForms.filter_pred_neq by assumption.
            reflexivity. }
        rewrite E_src.
        (* and the emitted form: rebuild from the whole table, then probe
           the primary-key member for the row that is leaving *)
        rewrite interp_ELet_step.
        rewrite (interp_to_idx_at store env _ rows H_rec E_tr).
        rewrite interp_EOptMatch, interp_EBinop.
        rewrite (interp_tbl_field store _ rv rv_aux pk_tag _ E_v E_aux E_pkf).
        rewrite <- (not_free_immut_put_sem kexp acc store env) by assumption.
        cbn [interp_binop].
        destruct (dict_lookup (interp_expr store env kexp)
                    (UniqueDictIndexImpl.idx_entries key rows)) as [ r | ] eqn:E_lk.
        1:{ (* the one row the key names, which the member resolves in O(1) *)
            apply (UniqueDictIndexImpl.idx_lookup_Some_inv key)
              in E_lk as [ H_in E_k ].
            (* what the per-row body computes, its binders read by shape *)
            assert (E_acc' : map.get
                               (map.put (map.put env acc
                                           (VDict (idx_of attr rows))) tup r)
                               acc = Some (VDict (idx_of attr rows))).
            1:{ (* map.get_put_diff wants looked-up-key <> put-key *)
                rewrite map.get_put_diff by (apply not_eq_sym; exact tup_neq_acc).
                apply map.get_put_same. }
            assert (E_tup' : map.get
                               (map.put (map.put env acc
                                           (VDict (idx_of attr rows))) tup r)
                               tup = Some r) by apply map.get_put_same.
            (* the index holds nothing but bags, which is the body's one
               premise and what idx_of_bucket_typed supplies *)
            assert (H_bags : forall bv,
                       dict_lookup (row_key attr r) (idx_of attr rows) = Some bv ->
                       type_of_value bv (TBag (TRecord rt))).
            1:{ intros bv H_bv.
                exact (idx_of_bucket_typed attr rows (TRecord rt) _ bv
                         H_rec H_rows H_bv). }
            rewrite (interp_dict_row_delete store _ (idx_of attr rows) r
                       (TRecord rt) E_acc' E_tup' H_bags).
            (* taking the row out of the recomputation is taking its key
               out of the index that was already there *)
            rewrite E_k. f_equal. symmetry.
            exact (idx_of_filter_neq_key attr key rows r _ H_rec H_nd H_in E_k). }
        1:{ (* no row carries the key, so the filter removes nothing *)
            rewrite interp_EVar; unfold get_local; rewrite map.get_put_same.
            f_equal. symmetry.
            apply (idx_of_filter_neq_absent attr key rows).
            intros r H_in E_k.
            pose proof (UniqueDictIndexImpl.idx_lookup_Some key
 rows r H_nd H_in) as E_s.
            rewrite E_k, E_lk in E_s; discriminate. }
      Qed.
    End WithTable.

    (* =================================================================
       What a pipeline has to supply for the rule to fire.

       Two members, so two aux_ty_for_idx clauses -- and, unlike the
       trigram's bridges, two is_tbl_ty implications.  The dictionary
       index buckets on attr and its is_tbl_ty says nothing about key,
       while this rule reads the key off a row, so the primary-key
       member has to be installable on the same table.

       The dictionary member needs only the relation any index
       establishes from typing.  The primary-key member needs its STRONG
       one, which no index establishes and which a declaration pays for.
       ================================================================= *)
    Definition dict_keyed_delete_bridges (is_tbl_ty' : type -> bool)
      (aux_ty : type -> type) (aux_wf : value -> Prop) : Prop :=
      aux_ty_for_idx id_tag aux_tag idx_tag (@IndexInterface.idx_ty didx) aux_ty
      /\ aux_ty_for_idx id_tag aux_tag pk_tag (@IndexInterface.idx_ty uidx) aux_ty
      /\ (forall t, is_tbl_ty' t = true -> @IndexInterface.is_tbl_ty didx t = true)
      /\ (forall t, is_tbl_ty' t = true -> @IndexInterface.is_tbl_ty uidx t = true)
      /\ (forall (t : type) (v : value),
             type_wf t -> is_tbl_ty' t = true ->
             type_of_value v (aux_ty t) -> aux_wf v -> idx_aux_wf_at v)
      /\ (forall (t : type) (v : value),
             type_wf t -> is_tbl_ty' t = true ->
             type_of_value v (aux_ty t) -> aux_wf v -> unique_aux_wf_at v).

    Lemma filter_neq_to_keyed_delete_head_sound :
      forall is_tbl_ty' aux_ty (aux_wf : value -> Prop),
        dict_keyed_delete_bridges is_tbl_ty' aux_ty aux_wf ->
        expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf
          filter_neq_to_keyed_delete_head.
    Proof.
      unfold dict_keyed_delete_bridges, aux_ty_for_idx, expr_aug_transf_sound.
      intros * [ H_aty1 [ H_aty2 [ H_isd [ H_isu [ H_wf1 H_wf2 ] ] ] ] ] *.
      intros H_Gs H_Ge H_twf H_is' H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with
        H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl
      end.
      (* the table type's shape, from the dictionary member *)
      pose proof (H_isd _ H_is') as H_is_d.
      pose proof (H_isu _ H_is') as H_is_u.
      apply dict_is_tbl_ty_inv in H_is_d as [ rt [ at_ty [ E_t E_attr ] ] ].
      specialize (H_aty1 tbl_ty); specialize (H_aty2 tbl_ty).
      repeat destruct_match_hyp; intuition idtac.
      1:{ eapply filter_neq_to_keyed_delete_head_preserve_ty; try eassumption.
          all: try (apply H_isd; exact H_is').
          all: try (apply H_isu; exact H_is'). }
      1:{ subst tbl_ty.
          eapply filter_neq_to_keyed_delete_head_preserve_sem; try eassumption.
          1:{ (* the member's is_tbl_ty, in the spelling preserve_sem wants *)
              pose proof (H_isd _ H_is') as H_d.
              cbn [IndexInterface.is_tbl_ty dict_idx] in H_d; exact H_d. }
          (* and the store's side: the table's value is well typed and
             both members' relations hold of it *)
          lazymatch goal with
            H : locals_wf Gstore _ |- _ => specialize (H _ _ E_tbl)
          end.
          destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
          lazymatch goal with
            H : holds_for_all_entries _ _ |- _ => specialize (H _ _ E_v)
          end.
          unfold value_wf_with_globals in *; invert_Forall.
          lazymatch goal with
            H : _ \/ _ |- _ => destruct H as [ H_neq | H_aw ]; [ congruence | ]
          end.
          split; [ assumption | split ].
          1:{ eapply H_wf1; [ exact H_twf | exact H_is' | | exact H_aw ].
              lazymatch goal with E : aux_ty _ = _ |- _ => rewrite E end.
              assumption. }
          1:{ eapply H_wf2; [ exact H_twf | exact H_is' | | exact H_aw ].
              lazymatch goal with E : aux_ty _ = _ |- _ => rewrite E end.
              assumption. } }
    Qed.

    Definition filter_neq_to_keyed_delete_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl]
                   (filter_neq_to_keyed_delete_head tbl).

    Lemma filter_neq_to_keyed_delete_transf_sound :
      forall is_tbl_ty' aux_ty aux_wf,
        dict_keyed_delete_bridges is_tbl_ty' aux_ty aux_wf ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf
          filter_neq_to_keyed_delete_transf.
    Proof.
      intros * H_br. unfold filter_neq_to_keyed_delete_transf.
      apply fold_command_with_globals_sound.
      apply filter_neq_to_keyed_delete_head_sound; exact H_br.
    Qed.

    (* ------------------------------------------------------------------
       The rule as a pipeline uses it: the identity unless the table's
       declarations name the key.

       The gate is on the key, not on anything about the bucketing
       attribute.  The dictionary index is sound to install and to read on
       any table; what needs the declaration is knowing that the row this
       rule takes out of one bucket is the ONLY row the filter removed.
       Without it another row could share the key, and its contribution
       would be left behind in a bucket this rule never visits.
       ------------------------------------------------------------------ *)
    Definition keyed_delete_gated (ds : list decl) : string -> command -> command :=
      if declares_unique key ds
      then filter_neq_to_keyed_delete_transf
      else fun _ => id.

    Lemma keyed_delete_gated_sound : forall ds is_tbl_ty' aux_ty aux_wf,
        (declares_unique key ds = true ->
         dict_keyed_delete_bridges is_tbl_ty' aux_ty aux_wf) ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf (keyed_delete_gated ds).
    Proof.
      intros * H_br. unfold keyed_delete_gated.
      destruct (declares_unique key ds) eqn:E_uq.
      1: apply filter_neq_to_keyed_delete_transf_sound, H_br; reflexivity.
      1: unfold aug_transf_sound, id; intros; repeat split; auto.
    Qed.
  End WithMap.
End WithRule.
