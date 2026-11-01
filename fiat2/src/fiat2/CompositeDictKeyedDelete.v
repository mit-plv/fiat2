(* ====================================================================
   Deleting a row from a COMPOSITE dictionary index when the delete names
   a single declared key rather than the attributes the index buckets on.

   Two rules already delete from a composite dictionary index, and neither
   covers this write:

   - filter_neq_to_composite_delete_head (CompositeDictIndexImpl.v) fires
     when the filter names EVERY key attribute, so the whole entry leaves
     with one ODelete.  Its matcher tests that the conjunction covers
     attrs exactly, which is why it cannot fire here and why the two rules
     cannot race.
   - filter_neq_to_keyed_delete_head (DictIndexKeyedDelete.v) is this
     rule at a single bucketing attribute.

   The shape is that rule's, with record_proj attr replaced by ckey attrs:
   the row that is leaving is not in the expression at all, only its key
   is, so the rule reads the row out of a sibling primary-key member and
   takes it out of the one bucket its own composite key names.  Sound only
   where that key is declared unique -- with two rows at the same key,
   removing one row's contributions would lose the other's -- so the rule
   is GATED on the declaration, while the composite index's own rules are
   not.  A table therefore gets the unconstrained delete with no
   declaration and this one in addition with one.

   Everything below the bucket key is already proved: the lemmas of
   DictIndexKeyedDelete that mention only the DELETED key (keeps,
   keeps_other, Forall_rec_filter, filter_all_true, list_to_bag_filter)
   are reused rather than restated, which is the whole reason this file is
   a fraction of that one's length.
   ==================================================================== *)
Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.CollectionTransf fiat2.FlatmapTransf fiat2.EraseField
  fiat2.Constraint fiat2.DictIndexImpl fiat2.FlatmapForms
  fiat2.IndexInterface fiat2.UniqueDictIndexImpl fiat2.Surface fiat2.UniqueIndexGate
  fiat2.CompositeDictIndexImpl fiat2.DictIndexKeyedDelete
  fiat2.TransfSound fiat2.TransfUtils
  fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Section WithAttrs.

  (* attrs is the composite key this index buckets on; key is the single
     declared key the delete names.  The delete rule's matcher requires the
     filter to name key, and the composite index's own delete rule requires
     it to name every one of attrs, so the two are told apart by the
     pattern and never both fire. *)
  Context (attrs : list string) (key : string).

  (* the composite key a row is filed under; the n-ary row_key *)
  Definition crow_key (r : value) : value :=
    match r with
    | VRecord rc => ckey attrs rc
    | _ => VUnit
    end.

  (* the rows the index files under av *)
  Definition crows_at (av : value) (l : list value) : list value :=
    filter (fun r => value_eqb (crow_key r) av) l.

  Definition cidx_of (l : list value) : list (value * value) :=
    match gallina_to_idx attrs (VList l) with
    | VDict d => d
    | _ => nil
    end.

  Lemma cgallina_to_idx_VDict : forall l,
      gallina_to_idx attrs (VList l) = VDict (cidx_of l).
  Proof. intro l; unfold cidx_of; cbn [gallina_to_idx]; reflexivity. Qed.

  (* One step of the index's own fold: a row joins the bucket its composite
     key names. *)
  Lemma cidx_of_cons : forall rc l,
      cidx_of (VRecord rc :: l)
      = dict_insert (ckey attrs rc)
          (VBag (bag_insert (VRecord rc)
                   match dict_lookup (ckey attrs rc) (cidx_of l) with
                   | Some (VBag b) => b
                   | _ => nil
                   end)) (cidx_of l).
  Proof. intros rc l; unfold cidx_of; cbn [gallina_to_idx fold_right]; reflexivity. Qed.

  (* What the index holds at a key: the bag of the rows filed there, and no
     entry at all when none are.  The index never stores an empty bucket,
     which is why the delete below must remove an entry that empties. *)
  Lemma cidx_of_lookup : forall l av,
      Forall (fun r => exists rc, r = VRecord rc) l ->
      dict_lookup av (cidx_of l)
      = match crows_at av l with
        | nil => None
        | rows => Some (VBag (list_to_bag rows))
        end.
  Proof.
    intros l av H_rec.
    induction H_rec as [ | r l [ rc E_r ] H_l IH ]; [ reflexivity | ].
    subst r. rewrite cidx_of_cons.
    unfold crows_at, crow_key in *; cbn [filter].
    destruct (value_eqb (ckey attrs rc) av) eqn:E_av.
    - apply value_eqb_eq in E_av; subst av.
      rewrite dict_lookup_insert_same, IH.
      destruct (filter _ l) as [ | r0 rows ] eqn:E_rows; reflexivity.
    - rewrite dict_lookup_insert_diff;
        [ exact IH | intro E; subst; rewrite value_eqb_refl in E_av; discriminate ].
  Qed.

  Lemma cidx_of_dict_wf : forall l, dict_wf (cidx_of l).
  Proof.
    induction l as [ | r l IH ]; [ exact I | ].
    destruct r; try exact I.
    rewrite cidx_of_cons; apply dict_insert_preserve_dict_wf; exact IH.
  Qed.

  (* Whatever bucket the index holds is a bag of the table's rows.  This is
     what makes a bucket filterable, and it is all the delete body needs to
     know about the dictionary it is rewriting. *)
  Lemma cidx_of_bucket_typed : forall l t av bv,
      Forall (fun r => exists rc, r = VRecord rc) l ->
      Forall (fun r => type_of_value r t) l ->
      dict_lookup av (cidx_of l) = Some bv ->
      type_of_value bv (TBag t).
  Proof.
    intros l t av bv H_rec H_ty H_lk.
    rewrite (cidx_of_lookup l av H_rec) in H_lk.
    destruct (crows_at av l) as [ | r0 rows ] eqn:E_rows; [ discriminate | ].
    injection H_lk as H_lk; subst bv.
    (* the match reduced list_to_bag's fold one step; put it back *)
    change (bag_insert r0 (list_to_bag rows)) with (list_to_bag (r0 :: rows)).
    apply list_to_bag_sound.
    rewrite <- E_rows; unfold crows_at.
    rewrite Forall_forall in *; intros r H_in.
    apply filter_In in H_in as [ H_in _ ]; auto.
  Qed.

  (* the whole index, with the row r taken out of the bucket its own
     composite key names.  The entry goes when it empties, because the index
     of a table never holds an empty bucket (cidx_of_lookup).  The bucket
     and the surviving-row test are DictIndexKeyedDelete's: neither depends
     on what the index buckets on. *)
  Definition cunindex (kv r : value) (d : list (value * value)) :=
    match dict_lookup (crow_key r) d with
    | Some (VBag b) =>
        match bucket_without key kv b with
        | nil => dict_delete (crow_key r) d
        | b' => dict_insert (crow_key r) (VBag b') d
        end
    | _ => d
    end.

  (* Filtering the table commutes with picking out one bucket's rows. *)
  Lemma crows_at_filter : forall av kv l,
      crows_at av (filter (keeps key kv) l) = filter (keeps key kv) (crows_at av l).
  Proof.
    intros av kv l; unfold crows_at; induction l as [ | r l IH ]; cbn [filter]; auto.
    destruct (keeps key kv r) eqn:E_k;
      destruct (value_eqb (crow_key r) av) eqn:E_a;
      cbn [filter]; rewrite ?E_k, ?E_a, IH; reflexivity.
  Qed.

  (* ==================================================================
     The delete equation.  The index of the table with the row at kv
     filtered out is the stored index with that one row taken out of the
     one bucket its own composite key names -- not rebuilt.
     ================================================================== *)
  Theorem cidx_of_filter_neq_key : forall l (r kv : value),
      Forall (fun v => exists rc, v = VRecord rc) l ->
      NoDup (map (row_key key) l) ->
      In r l -> row_key key r = kv ->
      cidx_of (filter (keeps key kv) l) = cunindex kv r (cidx_of l).
  Proof.
    intros l r kv H_rec H_nd H_in E_kv.
    pose proof (Forall_rec_filter (keeps key kv) l H_rec) as H_recf.
    (* r sits in the bucket its composite key names, so that bucket is there *)
    assert (E_lk : dict_lookup (crow_key r) (cidx_of l)
                   = Some (VBag (list_to_bag (crows_at (crow_key r) l)))).
    1:{ rewrite (cidx_of_lookup l _ H_rec).
        assert (H_rin : In r (crows_at (crow_key r) l)).
        1:{ unfold crows_at; apply filter_In; split;
            [ exact H_in | apply value_eqb_refl ]. }
        destruct (crows_at (crow_key r) l) as [ | r0 rows ];
          [ contradiction | reflexivity ]. }
    apply dict_wf_lookup_ext; [ apply cidx_of_dict_wf | | ].
    1:{ unfold cunindex; rewrite E_lk.
        destruct (bucket_without key kv (list_to_bag (crows_at (crow_key r) l)));
          [ apply dict_delete_preserve_dict_wf | apply dict_insert_preserve_dict_wf ];
          apply cidx_of_dict_wf. }
    intros av.
    rewrite (cidx_of_lookup _ av H_recf), crows_at_filter.
    unfold cunindex; rewrite E_lk.
    replace (bucket_without key kv (list_to_bag (crows_at (crow_key r) l)))
      with (list_to_bag (filter (keeps key kv) (crows_at (crow_key r) l)))
      by (unfold bucket_without; apply list_to_bag_filter).
    destruct (value_eqb av (crow_key r)) eqn:E_av.
    - (* the bucket the row leaves *)
      apply value_eqb_eq in E_av; subst av.
      destruct (filter (keeps key kv) (crows_at (crow_key r) l)) as [ | r0 rows ] eqn:E_f.
      + cbn [list_to_bag fold_right].
        rewrite dict_lookup_delete_same; [ reflexivity | apply cidx_of_dict_wf ].
      + destruct (list_to_bag (r0 :: rows)) as [ | e b ] eqn:E_b.
        1:{ exfalso; cbn [list_to_bag fold_right] in E_b.
            eapply bag_insert_not_nil, E_b. }
        rewrite dict_lookup_insert_same; reflexivity.
    - (* every other bucket: untouched, and nothing in it leaves *)
      assert (H_ne : av <> crow_key r) by (apply value_eqb_neq; exact E_av).
      assert (E_keep : filter (keeps key kv) (crows_at av l) = crows_at av l).
      1:{ apply filter_all_true; intros r' H_r'.
          unfold crows_at in H_r'; apply filter_In in H_r' as [ H_r'l E_r'a ].
          apply (keeps_other key l r kv r' H_nd H_in E_kv H_r'l).
          intro E; subst r'; apply H_ne.
          symmetry; apply value_eqb_eq; exact E_r'a. }
      rewrite E_keep.
      destruct (filter (keeps key kv) (crows_at (crow_key r) l)) as [ | r0 rows ].
      + cbn [list_to_bag fold_right].
        rewrite dict_lookup_delete_diff by exact H_ne.
        rewrite (cidx_of_lookup l av H_rec); reflexivity.
      + destruct (list_to_bag (r0 :: rows)) as [ | e b ] eqn:E_b.
        1:{ exfalso; cbn [list_to_bag fold_right] in E_b.
            eapply bag_insert_not_nil, E_b. }
        rewrite dict_lookup_insert_diff by exact H_ne.
        rewrite (cidx_of_lookup l av H_rec); reflexivity.
  Qed.

  (* And if no row carries the key, the delete removes nothing: the branch
     where the primary-key member has no entry at the deleted key. *)
  Lemma cidx_of_filter_neq_absent : forall l kv,
      (forall r, In r l -> row_key key r <> kv) ->
      cidx_of (filter (keeps key kv) l) = cidx_of l.
  Proof.
    intros l kv H; f_equal.
    apply filter_all_true; intros r H_in; unfold keeps.
    destruct (value_eqb (row_key key r) kv) eqn:E; [ exfalso | reflexivity ].
    apply (H r H_in), value_eqb_eq, E.
  Qed.

End WithAttrs.


(* ====================================================================
   The rule: a keyed delete, read off two members of one index record.

   The composite dictionary member buckets on attrs; the delete names a
   single declared key; so the row that is leaving is not in the
   expression at all, only its key is, and the rule reads the row out of
   the primary-key member.  That is also why it is sound only where the
   key is declared unique.
   ==================================================================== *)
Section WithRule.
  (* the composite index's own binders and the attributes it buckets on *)
  Context (hole : string).
  Context (attrs : list string).
  Context (tup acc x : string).
  Context (H_NoDup : is_NoDup_opaque [tup; acc; x]).
  (* The primary-key index's binders, and the attribute the delete names.
     Only this index can turn a key back into the row that carries it. *)
  Context (key utup uacc : string).
  Context (H_utup_uacc : utup <> uacc).
  (* the two fields the installation pairs *)
  Context (id_tag aux_tag : string).
  (* the tags the two dictionaries sit under inside one index record *)
  Context (idx_tag pk_tag : string).
  (* the binders the rewritten delete introduces: a bucket, and a row of it *)
  Context (bkt rvar : string).
  Context (H_tup_rvar : tup <> rvar) (H_tup_bkt : tup <> bkt) (H_acc_bkt : acc <> bkt).

  Notation cidx := (composite_dict_idx hole attrs tup acc x).
  Notation uidx := (unique_dict_idx hole key utup uacc).

  Lemma ctup_neq_acc : tup <> acc.
  Proof. use_is_NoDup. Qed.

  (* The table shape the composite index demands, as an inversion.  Unlike
     the single-attribute index's, it fixes no one attribute's type: the key
     is a record whose field types are read off the row type by key_ty. *)
  Lemma composite_is_tbl_ty_inv : forall t,
      @IndexInterface.is_tbl_ty cidx t = true ->
      exists rt, t = TList (TRecord rt)
                 /\ CompositeDictIndexImpl.is_tbl_ty attrs (TList (TRecord rt)) = true.
  Proof.
    cbn [IndexInterface.is_tbl_ty composite_dict_idx].
    intros t H.
    destruct t as [ | | | | | t1 | | | | ]; try discriminate.
    destruct t1 as [ | | | | | | rt | | | ]; try discriminate.
    exists rt; split; [ reflexivity | exact H ].
  Qed.

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Notation value := (value).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    (* the bucket with the leaving row taken out.  Spelled exactly as the
       single-attribute rule spells it, and its two lemmas are that file's:
       what the delete names is one attribute either way, so nothing about
       this body depends on what the index buckets on. *)
    Notation without_row :=
      (EFlatmap LikeBag (EVar bkt) rvar
         (EIf (EUnop ONot (EBinop OEq (EAccess (EVar rvar) key)
                             (EAccess (EVar tup) key)))
            (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar rvar))
            (EAtom (AEmptyBag None)))).

    (* the bucket the leaving row belongs to: its COMPOSITE key, which is
       the index's own key expression over the fold's binder *)
    Notation bucket_key := (composite_key attrs (EVar tup)).

    Notation cdict_row_delete_body :=
      (EOptMatch (EBinop OLookup (EVar acc) bucket_key)
         (EVar acc)
         bkt
         (EIf (EBinop OEq without_row (EAtom (AEmptyBag None)))
            (EBinop ODelete (EVar acc) bucket_key)
            (ETernop OInsert (EVar acc) bucket_key without_row))).

    (* What that body computes.  The leaving row must be a record -- unlike
       the single-attribute rule, where a non-record row's key was VUnit on
       both sides, a record literal built over a non-record is still a
       record, so the two sides would not agree.  Every row of a well-typed
       table is a record, which is where the premise comes from. *)
    Lemma interp_cdict_row_delete : forall (store env : locals) d rc t,
        map.get env acc = Some (VDict d) ->
        map.get env tup = Some (VRecord rc) ->
        (forall bv, dict_lookup (ckey attrs rc) d = Some bv ->
                    type_of_value bv (TBag t)) ->
        interp_expr store env cdict_row_delete_body
        = VDict (cunindex attrs key (row_key key (VRecord rc)) (VRecord rc) d).
    Proof.
      intros store env d rc t E_acc E_tup H_bags.
      rewrite interp_EOptMatch, interp_EBinop, interp_EVar.
      unfold get_local; rewrite E_acc.
      rewrite (interp_composite_key_var attrs store env tup rc E_tup).
      cbn [interp_binop].
      unfold cunindex, crow_key.
      destruct (dict_lookup (ckey attrs rc) d) as [ bv | ] eqn:E_lk.
      2: reflexivity.
      assert (H_bv : type_of_value bv (TBag t)) by (apply H_bags; reflexivity).
      assert (H_bag : exists b, bv = VBag b) by (inversion H_bv; eauto).
      destruct H_bag as [ b E_bv ]; subst bv.
      assert (E_wo : interp_expr store (map.put env bkt (VBag b)) without_row
                     = VBag (bucket_without key (row_key key (VRecord rc)) b)).
      1:{ apply (interp_without_row tup key bkt rvar H_tup_rvar store _ b t);
          [ apply map.get_put_same
          | rewrite map.get_put_diff by exact H_tup_bkt; exact E_tup
          | exact H_bv ]. }
      rewrite interp_EIf, interp_EBinop, E_wo, interp_EAtom.
      cbn [interp_atom interp_binop].
      destruct (bucket_without key (row_key key (VRecord rc)) b) as [ | e b' ] eqn:E_bw.
      - (* the row was the last one in its bucket, so the entry goes *)
        rewrite value_eqb_refl.
        rewrite interp_EBinop, interp_EVar; unfold get_local.
        rewrite map.get_put_diff by exact H_acc_bkt; rewrite E_acc.
        rewrite (interp_composite_key_var attrs store _ tup rc)
          by (rewrite map.get_put_diff by exact H_tup_bkt; exact E_tup).
        reflexivity.
      - (* and otherwise the shortened bucket goes back in its place *)
        destruct (value_eqb (VBag (e :: b')) (VBag nil)) eqn:E_eq.
        1:{ exfalso; apply value_eqb_eq in E_eq; discriminate. }
        rewrite interp_ETernop, interp_EVar, E_wo; unfold get_local.
        rewrite map.get_put_diff by exact H_acc_bkt; rewrite E_acc.
        rewrite (interp_composite_key_var attrs store _ tup rc)
          by (rewrite map.get_put_diff by exact H_tup_bkt; exact E_tup).
        reflexivity.
    Qed.

    Lemma cdict_row_delete_body_ty : forall rt kt (Gstore Genv : tenv),
        CompositeDictIndexImpl.is_tbl_ty attrs (TList (TRecord rt)) = true ->
        access_record rt key = Success kt ->
        map.get Genv tup = Some (TRecord rt) ->
        map.get Genv acc = Some (TDict Unranged (key_ty attrs rt) (TBag (TRecord rt))) ->
        type_wf (TRecord rt) ->
        type_of Gstore Genv cdict_row_delete_body
          (TDict Unranged (key_ty attrs rt) (TBag (TRecord rt))).
    Proof.
      intros rt kt Gstore Genv H_is E_key E_tup E_acc H_rtwf.
      assert (E_tup' : map.get (map.put Genv bkt (TBag (TRecord rt))) tup
                       = Some (TRecord rt))
        by (rewrite map.get_put_diff by exact H_tup_bkt; exact E_tup).
      assert (E_acc' : map.get (map.put Genv bkt (TBag (TRecord rt))) acc
                       = Some (TDict Unranged (key_ty attrs rt) (TBag (TRecord rt))))
        by (rewrite map.get_put_diff by exact H_acc_bkt; exact E_acc).
      assert (H_wo : type_of Gstore (map.put Genv bkt (TBag (TRecord rt)))
                       without_row (TBag (TRecord rt)))
        by (eapply (without_row_ty tup key bkt rvar H_tup_rvar);
            [ exact E_key | apply map.get_put_same | exact E_tup' | exact H_rtwf ]).
      (* the key expression, at both of its occurrences *)
      assert (H_k : type_of Gstore Genv bucket_key (key_ty attrs rt))
        by (eapply composite_key_ty; [ exact H_is | apply TyEVar; exact E_tup ]).
      assert (H_k' : type_of Gstore (map.put Genv bkt (TBag (TRecord rt)))
                       bucket_key (key_ty attrs rt))
        by (eapply composite_key_ty; [ exact H_is | apply TyEVar; exact E_tup' ]).
      eapply TyEOptMatch.
      1:{ eapply TyEBinop; [ apply TyOLookup | | ].
          1: apply TyEVar; exact E_acc.
          1: exact H_k. }
      1: apply TyEVar; exact E_acc.
      apply TyEIf.
      1:{ eapply TyEBinop; [ apply TyOEq | exact H_wo | ].
          apply TyEAtom; apply TyAEmptyBag'; exact H_rtwf. }
      1:{ eapply TyEBinop; [ apply TyODelete | | ].
          1: apply TyEVar; exact E_acc'.
          1: exact H_k'. }
      1:{ eapply TyETernop; [ apply TyOInsert | | | ].
          1: apply TyEVar; exact E_acc'.
          1: exact H_k'.
          1: exact H_wo. }
    Qed.

    (* The two invariants the rule reads off the store, each at its own tag. *)
    Notation idx_aux_wf_at :=
      (aux_wf_for_idx id_tag aux_tag idx_tag
         (CompositeDictIndexImpl.idx_wf hole attrs tup acc x (locals := locals))).
    Notation unique_aux_wf_at :=
      (aux_wf_for_idx id_tag aux_tag pk_tag
         (UniqueDictIndexImpl.idx_wf_unique hole key utup uacc (locals := locals))).

    (* Everything the rule needs about the store, read off the two
       invariants and the store's type at once. *)
    Lemma cinvariants__idx_data :
      forall tl rt (v : value),
        type_wf (TList (TRecord rt)) ->
        CompositeDictIndexImpl.is_tbl_ty attrs (TList (TRecord rt)) = true ->
        access_record tl id_tag = Success (TList (TRecord rt)) ->
        type_of_value v (TRecord tl) ->
        idx_aux_wf_at v ->
        unique_aux_wf_at v ->
        exists rv rv_aux rows,
          v = VRecord rv
          /\ record_proj id_tag rv = VList rows
          /\ record_proj aux_tag rv = VRecord rv_aux
          /\ record_proj idx_tag rv_aux = VDict (cidx_of attrs rows)
          /\ record_proj pk_tag rv_aux
             = VDict (UniqueDictIndexImpl.idx_entries key rows)
          /\ Forall (fun r => type_of_value r (TRecord rt)) rows
          /\ NoDup (List.map (row_key key) rows).
    Proof.
      unfold aux_wf_for_idx, UniqueDictIndexImpl.idx_wf_unique,
        UniqueDictIndexImpl.idx_wf, UniqueDictIndexImpl.keys_distinct,
        CompositeDictIndexImpl.idx_wf.
      intros tl rt v H_twf H_is E_id.
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
      assert (H_idty : type_of_value v_id (TList (TRecord rt)))
        by (eapply type_of_value_field; [ exact H_vty | exact E_vid | exact E_id ]).
      apply type_of_value_TList_inv in H_idty as [ rows [ E_rows H_rows ] ].
      subst v_id.
      cbn [UniqueDictIndexImpl.keys_distinct] in H_kd.
      rewrite (CompositeDictIndexImpl.fiat2_gallina_to_idx hole attrs tup acc x
                 H_NoDup (locals_ok := locals_ok) (VList rows) (TList (TRecord rt))
                 H_twf H_is (TyVList _ _ H_rows)) in H_idx.
      rewrite cgallina_to_idx_VDict in H_idx.
      rewrite (UniqueDictIndexImpl.fiat2_gallina_to_idx hole key utup uacc
                 H_utup_uacc (locals_ok := locals_ok) rows) in E_pk.
      exists rv, rv_aux, rows.
      repeat split; try assumption;
        try (apply access_record__record_proj; assumption).
      1:{ apply access_record__record_proj. rewrite E_vidx, H_idx. reflexivity. }
      1:{ apply access_record__record_proj. rewrite E_vpk, E_pk. reflexivity. }
    Qed.

    Section WithTable.
      (* the store location the index record sits at *)
      Context (tbl : string).

      Notation pk_e := (EAccess (EAccess (ELoc tbl) aux_tag) pk_tag).

      (* to_idx_from spelled out, so that the rule can match it.  The key is
         a record literal COMPUTED from attrs, so a pattern cannot bind it
         positionally; keys_match checks it, exactly as the composite
         index's own maintenance rules do. *)
      Notation ecomposite_to_idx tup0 tup1 acc0 acc1 acc2 x0 x1 kl0 kl1 d :=
        (EFold d (EAtom (AEmptyDict Unranged None)) tup0 acc0
           (ETernop OInsert (EVar acc1) (ERecord kl0)
              (EBinop OBagInsert
                 (EOptMatch (EBinop OLookup (EVar acc2) (ERecord kl1))
                    (EAtom (AEmptyBag None)) x0 (EVar x1))
                 (EVar tup1)))).

      (* The one case this rule declines: a composite key of exactly the
         attribute the delete names.  There the index's OWN delete rule
         fires (filter_neq_to_composite_delete_head) and does it with one
         ODelete and no probe, so the two would race.  At any other arity,
         or on any other attribute, that rule's matcher requires the filter
         to name every key attribute and cannot fire on this write. *)
      Definition attrs_is_key : bool :=
        match attrs with
        | [a] => String.eqb a key
        | _ => false
        end.

      Definition filter_neq_to_composite_keyed_delete_head (e : expr) : expr :=
        match e with
        | ecomposite_to_idx tup0 tup1 acc0 acc1 acc2 x0 x1 kl0 kl1
            (flatmap_filter_list (EAccess (ELoc tbl0) id_tag0) y0
               (EUnop ONot (EBinop OEq (EAccess (EVar y1) key0) kexp)) y2 _ _) =>
            if (all_eqb [(tup, [tup0; tup1]); (acc, [acc0; acc1; acc2]);
                         (x, [x0; x1]); (key, [key0]);
                         (tbl, [tbl0]); (id_tag, [id_tag0]); (y0, [y1; y2])]
                && keys_match tup attrs kl0
                && keys_match tup attrs kl1
                && negb attrs_is_key
                && negb (free_immut_in y0 kexp)
                && negb (free_immut_in acc kexp))%bool
            then ELet (to_idx_from attrs tup acc x (EAccess (ELoc tbl) id_tag)) acc
                   (EOptMatch (EBinop OLookup pk_e kexp) (EVar acc) tup
                      cdict_row_delete_body)
            else e
        | _ => e
        end.
      Lemma filter_neq_to_composite_keyed_delete_head_preserve_ty :
        forall tl ctl t (Gstore : tenv),
          type_wf t ->
          @IndexInterface.is_tbl_ty cidx t = true ->
          @IndexInterface.is_tbl_ty uidx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl pk_tag = Success (@IndexInterface.idx_ty uidx t) ->
          preserve_ty Gstore filter_neq_to_composite_keyed_delete_head.
      Proof.
        unfold preserve_ty.
        intros tl ctl t Gstore H_twf H_isd H_isu E_tbl E_id E_aux E_pk.
        (* the table type's shape, from the two members' is_tbl_ty *)
        apply composite_is_tbl_ty_inv in H_isd as [ rt [ E_t H_is ] ]. subst t.
        apply unique_is_tbl_ty_inv in H_isu as [ rt' [ kt [ E_t' E_key ] ] ].
        injection E_t' as E_t'; subst rt'.
        cbn [IndexInterface.idx_ty unique_dict_idx UniqueDictIndexImpl.idx_ty]
          in E_pk.
        (* the primary-key member's key type, spelled the way the source
           spells it *)
        assert (E_kt : get_attr_type rt key = kt)
          by (unfold get_attr_type; rewrite E_key; reflexivity).
        rewrite E_kt in E_pk. clear E_kt.
        assert (H_rtwf : type_wf (TRecord rt)) by (inversion H_twf; assumption).
        intros e t' Genv H_Gs H_Ge H_t.
        unfold filter_neq_to_composite_keyed_delete_head.
        repeat (case_match; auto; []).
        (* the guard *)
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *.
        repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
        rewrite !Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        lazymatch goal with
          H : keys_match _ _ ?kl = true |- _ => apply keys_match_eq in H; subst kl
        end.
        lazymatch goal with
          H : keys_match _ _ ?kl = true |- _ => apply keys_match_eq in H; subst kl
        end.
        (* the source's typing, down to the row type and the key type *)
        invert_type_of_clear.
        lazymatch goal with
          H : type_of _ _ (EFlatmap _ _ _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EAccess (ELoc _) _) _ |- _ =>
            inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (ELoc _) _ |- _ => inversion H; clear H; subst
        end.
        (* the table read fixes the row type *)
        lazymatch goal with
          H : map.get Gstore tbl = Some _ |- _ =>
            rewrite E_tbl in H; injection H as H; subst
        end.
        lazymatch goal with
          H : access_record _ id_tag = Success _ |- _ =>
            rewrite E_id in H; injection H as H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EIf _ _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EBinop OCons _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_binop OCons _ _ _ |- _ => inversion H; clear H; subst
        end.
        (* the filter's INPUT row type is its OUTPUT row type *)
        lazymatch goal with
          H : type_of _ (map.put _ ?yy _) (EVar ?yy) _ |- _ =>
            apply EVar_ty_inv in H; rewrite map.get_put_same in H;
            injection H as H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EUnop ONot _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_unop ONot _ _ |- _ => inversion H; clear H; subst
        end.
        (* the deleted key's own type, which the emitted probe needs *)
        lazymatch goal with
          H : type_of _ _ (EBinop OEq _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_binop OEq _ _ _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EAccess (EVar _) key) _ |- _ =>
            inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EVar _) (TRecord _) |- _ =>
            apply EVar_ty_inv in H; rewrite map.get_put_same in H;
            injection H as H; subst
        end.
        lazymatch goal with
          H : access_record _ key = Success _ |- _ =>
            rewrite E_key in H; injection H as H; subst
        end.
        (* the accumulator's type, from the fold's initial value and body *)
        lazymatch goal with
          H : type_of _ _ (EAtom (AEmptyDict _ _)) _ |- _ =>
            inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_atom (AEmptyDict _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (ETernop OInsert _ _ _) _ |- _ =>
            inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_ternop OInsert _ _ _ _ |- _ => inversion H; clear H; subst
        end.
        (* and the key literal says what that key type is *)
        lazymatch goal with
          H : type_of ?Gs (map.put (map.put ?Ge ?tp (TRecord ?rt0)) ?ac ?D)
                (ERecord (List.map (fun a => (a, EAccess (EVar ?tp) a)) attrs))
                ?kt0 |- _ =>
            assert (E_tp : map.get (map.put (map.put Ge tp (TRecord rt0)) ac D) tp
                           = Some (TRecord rt0))
              by (rewrite map.get_put_diff by use_is_NoDup;
                  apply map.get_put_same);
            pose proof (key_lit_inv attrs Gs _ tp rt0 kt0 E_tp H) as [ _ E_kty ]
        end.
        subst.
        (* and the bag insert says what the dictionary's VALUE type is *)
        lazymatch goal with
          H : type_of _ _ (EBinop OBagInsert _ (EVar _)) _ |- _ =>
            inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_binop OBagInsert _ _ _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EVar tup) _ |- _ =>
            apply EVar_ty_inv in H;
            rewrite map.get_put_diff in H by use_is_NoDup;
            rewrite map.get_put_same in H; injection H as H; subst
        end.
        (* the emitted form, from the typing lemmas above *)
        eapply TyELet.
        1:{ eapply (to_idx_from_ty attrs tup acc x H_NoDup).
            (* the collection first, so that it is what fixes the table type *)
            3: eapply TyEAccess; [ apply TyELoc; exact E_tbl | exact E_id ].
            1: constructor; exact H_rtwf.
            1: exact H_is. }
        eapply TyEOptMatch.
        1:{ (* the deleted row, from the primary-key member *)
            eapply TyEBinop; [ apply TyOLookup | | ].
            1:{ eapply TyEAccess;
                [ eapply TyEAccess; [ apply TyELoc; exact E_tbl | exact E_aux ]
                | exact E_pk ]. }
            1:{ apply not_free_immut_put_ty2; [ assumption | ].
                (* the typing premise first: it is what says WHICH binder the
                   deleted key's expression is being lifted out of, and
                   guessing from the two freeness hypotheses would pick the
                   other one *)
                eapply not_free_immut_put_ty; [ | eassumption ]; assumption. } }
        1:{ apply TyEVar; rewrite map.get_put_same; reflexivity. }
        1:{ eapply cdict_row_delete_body_ty.
            1: exact H_is.
            1: exact E_key.
            1: apply map.get_put_same.
            1:{ rewrite map.get_put_diff by (apply not_eq_sym; exact ctup_neq_acc).
                apply map.get_put_same. }
            1: exact H_rtwf. }
      Qed.

      (* =================================================================
         The rule computes what the source computes.

         The source rebuilds the whole index from the filtered table.  The
         emitted form rebuilds it from the whole table and then takes one
         row out of the single bucket that row's COMPOSITE key names.  The
         two agree because at most one row carries the deleted key, which
         is what the primary-key member's NoDup pays for: on the hit branch
         through cidx_of_filter_neq_key, on the miss branch through
         cidx_of_filter_neq_absent.
         ================================================================= *)
      Lemma filter_neq_to_composite_keyed_delete_head_preserve_sem :
        forall tl rt (Gstore : tenv) (store : locals),
          type_wf (TList (TRecord rt)) ->
          CompositeDictIndexImpl.is_tbl_ty attrs (TList (TRecord rt)) = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          match map.get store tbl with
          | Some v =>
              type_of_value v (TRecord tl) /\ idx_aux_wf_at v /\ unique_aux_wf_at v
          | _ => False
          end ->
          preserve_sem Gstore store filter_neq_to_composite_keyed_delete_head.
      Proof.
        unfold preserve_sem; intros * H_twf H_is E_tbl E_id H_store.
        intros e t Genv env H_Gs H_Ge H_t H_sw H_ew.
        destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
        destruct H_store as [ H_vty [ H_idx H_pk ] ].
        destruct (cinvariants__idx_data tl rt v H_twf H_is E_id H_vty H_idx H_pk)
          as [ rv [ rv_aux [ rows [ E_vrec [ E_rows [ E_aux
             [ E_idx [ E_pkf [ H_rows H_nd ] ] ] ] ] ] ] ] ].
        subst v.
        assert (H_rtwf : type_wf (TRecord rt)) by (inversion H_twf; assumption).
        (* the rows are records, which both to_idx and the bucket lemmas need *)
        pose proof (typed_rows_are_records rows rt H_rows) as H_rec.
        unfold filter_neq_to_composite_keyed_delete_head.
        repeat (case_match; auto; []).
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *.
        repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
        rewrite !Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        lazymatch goal with
          H : keys_match _ _ ?kl = true |- _ => apply keys_match_eq in H; subst kl
        end.
        lazymatch goal with
          H : keys_match _ _ ?kl = true |- _ => apply keys_match_eq in H; subst kl
        end.
        (* the deleted key's expression, which case_match named for us *)
        lazymatch goal with pe : expr |- _ => rename pe into kexp end.
        (* the table read, which both sides start from *)
        assert (E_tr : interp_expr store env (EAccess (ELoc tbl) id_tag)
                       = VList rows).
        1:{ rewrite interp_EAccess, interp_ELoc.
            unfold get_local; rewrite E_v; cbv beta iota. exact E_rows. }
        (* The source, settled first and separately: the matched term is
           to_idx_from only up to unfolding, and rewrite's syntactic match
           would not see it. *)
        lazymatch goal with
        | |- _ = interp_expr store env ?src =>
            assert (E_src : interp_expr store env src
                            = VDict (cidx_of attrs
                                       (filter (keeps key
                                                  (interp_expr store env kexp))
                                          rows)))
        end.
        1:{ rewrite <- cgallina_to_idx_VDict.
            eapply (interp_to_idx_from attrs tup acc x H_NoDup
                      (locals_ok := locals_ok)).
            1: exact H_rtwf.
            1: exact H_is.
            1:{ apply Forall_forall; intros v H_v.
                apply filter_In in H_v as [ H_v _ ].
                rewrite Forall_forall in H_rows; apply H_rows; exact H_v. }
            1:{ rewrite interp_flatmap_filter_list, E_tr.
                rewrite FlatmapForms.filter_pred_neq by assumption.
                reflexivity. } }
        rewrite E_src.
        (* and the emitted form: rebuild from the whole table, then probe
           the primary-key member for the row that is leaving *)
        rewrite interp_ELet_step.
        rewrite (interp_to_idx_from attrs tup acc x H_NoDup
                   (locals_ok := locals_ok) store env _ rt rows
                   H_rtwf H_is H_rows E_tr).
        rewrite cgallina_to_idx_VDict.
        rewrite interp_EOptMatch, interp_EBinop.
        rewrite (interp_tbl_field aux_tag tbl store _ rv rv_aux pk_tag _
                   E_v E_aux E_pkf).
        rewrite <- (not_free_immut_put_sem kexp acc store env) by assumption.
        cbn [interp_binop].
        destruct (dict_lookup (interp_expr store env kexp)
                    (UniqueDictIndexImpl.idx_entries key rows)) as [ r | ] eqn:E_lk.
        1:{ (* the one row the key names, which the member resolves in O(1) *)
            apply (UniqueDictIndexImpl.idx_lookup_Some_inv key)
              in E_lk as [ H_in E_k ].
            (* and it is a record, which the composite key's two sides need *)
            assert (H_rr : exists rc, r = VRecord rc)
              by (rewrite Forall_forall in H_rec; apply H_rec; exact H_in).
            destruct H_rr as [ rc E_r ]; subst r.
            assert (E_acc' : map.get
                               (map.put (map.put env acc
                                           (VDict (cidx_of attrs rows))) tup
                                  (VRecord rc))
                               acc = Some (VDict (cidx_of attrs rows))).
            1:{ rewrite map.get_put_diff by (apply not_eq_sym; exact ctup_neq_acc).
                apply map.get_put_same. }
            assert (E_tup' : map.get
                               (map.put (map.put env acc
                                           (VDict (cidx_of attrs rows))) tup
                                  (VRecord rc))
                               tup = Some (VRecord rc)) by apply map.get_put_same.
            (* the index holds nothing but bags, which is the body's one
               premise and what cidx_of_bucket_typed supplies *)
            assert (H_bags : forall bv,
                       dict_lookup (ckey attrs rc) (cidx_of attrs rows) = Some bv ->
                       type_of_value bv (TBag (TRecord rt))).
            1:{ intros bv H_bv.
                exact (cidx_of_bucket_typed attrs rows (TRecord rt) _ bv
                         H_rec H_rows H_bv). }
            rewrite (interp_cdict_row_delete store _ (cidx_of attrs rows) rc
                       (TRecord rt) E_acc' E_tup' H_bags).
            (* taking the row out of the recomputation is taking its key
               out of the index that was already there *)
            rewrite E_k. f_equal. symmetry.
            exact (cidx_of_filter_neq_key attrs key rows (VRecord rc) _
                     H_rec H_nd H_in E_k). }
        1:{ (* no row carries the key, so the filter removes nothing *)
            rewrite interp_EVar; unfold get_local; rewrite map.get_put_same.
            f_equal. symmetry.
            apply (cidx_of_filter_neq_absent attrs key rows).
            intros r H_in E_k.
            pose proof (UniqueDictIndexImpl.idx_lookup_Some key rows r H_nd H_in)
              as E_s.
            rewrite E_k, E_lk in E_s; discriminate. }
      Qed.
    End WithTable.

    (* =================================================================
       What a pipeline has to supply for the rule to fire.

       Two members, so two aux_ty_for_idx clauses and two is_tbl_ty
       implications: the composite index buckets on attrs and its
       is_tbl_ty says nothing about key, while this rule reads the key off
       a row, so the primary-key member has to be installable on the same
       table.

       The composite member needs only the relation any index establishes
       from typing.  The primary-key member needs its STRONG one, which no
       index establishes and which a declaration pays for.
       ================================================================= *)
    Definition composite_keyed_delete_bridges (is_tbl_ty' : type -> bool)
      (aux_ty : type -> type) (aux_wf : value -> Prop) : Prop :=
      aux_ty_for_idx id_tag aux_tag idx_tag (@IndexInterface.idx_ty cidx) aux_ty
      /\ aux_ty_for_idx id_tag aux_tag pk_tag (@IndexInterface.idx_ty uidx) aux_ty
      /\ (forall t, is_tbl_ty' t = true -> @IndexInterface.is_tbl_ty cidx t = true)
      /\ (forall t, is_tbl_ty' t = true -> @IndexInterface.is_tbl_ty uidx t = true)
      /\ (forall (t : type) (v : value),
             type_wf t -> is_tbl_ty' t = true ->
             type_of_value v (aux_ty t) -> aux_wf v -> idx_aux_wf_at v)
      /\ (forall (t : type) (v : value),
             type_wf t -> is_tbl_ty' t = true ->
             type_of_value v (aux_ty t) -> aux_wf v -> unique_aux_wf_at v).

    Lemma filter_neq_to_composite_keyed_delete_head_sound :
      forall is_tbl_ty' aux_ty (aux_wf : value -> Prop),
        composite_keyed_delete_bridges is_tbl_ty' aux_ty aux_wf ->
        expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf
          filter_neq_to_composite_keyed_delete_head.
    Proof.
      unfold composite_keyed_delete_bridges, aux_ty_for_idx,
        expr_aug_transf_sound.
      intros * [ H_aty1 [ H_aty2 [ H_isd [ H_isu [ H_wf1 H_wf2 ] ] ] ] ] *.
      intros H_Gs H_Ge H_twf H_is' H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with
        H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl
      end.
      (* the table type's shape, from the composite member *)
      pose proof (H_isd _ H_is') as H_is_d.
      pose proof (H_isu _ H_is') as H_is_u.
      apply composite_is_tbl_ty_inv in H_is_d as [ rt [ E_t H_isc ] ].
      specialize (H_aty1 tbl_ty); specialize (H_aty2 tbl_ty).
      repeat destruct_match_hyp; intuition idtac.
      1:{ eapply filter_neq_to_composite_keyed_delete_head_preserve_ty;
          try eassumption.
          all: try (apply H_isd; exact H_is').
          all: try (apply H_isu; exact H_is'). }
      1:{ subst tbl_ty.
          eapply filter_neq_to_composite_keyed_delete_head_preserve_sem;
            try eassumption.
          (* the member's is_tbl_ty is already in the spelling preserve_sem
             wants -- the composite index's is_tbl_ty IS its own, with no
             kind to collapse -- so eassumption has taken it, and what is
             left is the store's side: the table's value is well typed and
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

    Definition filter_neq_to_composite_keyed_delete_transf
      : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl]
                   (filter_neq_to_composite_keyed_delete_head tbl).

    Lemma filter_neq_to_composite_keyed_delete_transf_sound :
      forall is_tbl_ty' aux_ty aux_wf,
        composite_keyed_delete_bridges is_tbl_ty' aux_ty aux_wf ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf
          filter_neq_to_composite_keyed_delete_transf.
    Proof.
      intros * H_br. unfold filter_neq_to_composite_keyed_delete_transf.
      apply fold_command_with_globals_sound.
      apply filter_neq_to_composite_keyed_delete_head_sound; exact H_br.
    Qed.

    (* ------------------------------------------------------------------
       The rule as a pipeline uses it: the identity unless the table's
       declarations name the key.

       This is what lets ONE index choice hand out an unconstrained delete
       and a keyed one at the same time.  The composite index's own rules
       -- its read, its insert, and the delete that names every key
       attribute -- are sound on any table and are installed ungated; this
       one needs to know that the row it takes out of a single bucket is
       the ONLY row the filter removed, so it is the identity until a
       declaration says so.  Without that, another row could share the key
       and its contribution would be left behind in a bucket this rule
       never visits.
       ------------------------------------------------------------------ *)
    Definition composite_keyed_delete_gated (ds : list decl)
      : string -> command -> command :=
      if declares_unique key ds
      then filter_neq_to_composite_keyed_delete_transf
      else fun _ => id.

    Lemma composite_keyed_delete_gated_sound :
      forall ds is_tbl_ty' aux_ty aux_wf,
        (declares_unique key ds = true ->
         composite_keyed_delete_bridges is_tbl_ty' aux_ty aux_wf) ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf
          (composite_keyed_delete_gated ds).
    Proof.
      intros * H_br. unfold composite_keyed_delete_gated.
      destruct (declares_unique key ds) eqn:E_uq.
      1: apply filter_neq_to_composite_keyed_delete_transf_sound, H_br;
         reflexivity.
      1: unfold aug_transf_sound, id; intros; repeat split; auto.
    Qed.
  End WithMap.
End WithRule.
