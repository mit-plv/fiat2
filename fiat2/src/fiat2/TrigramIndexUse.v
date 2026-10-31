Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.Utils fiat2.Substitute
  fiat2.IndexTransf fiat2.Constraint fiat2.DictIndexImpl fiat2.FlatmapForms fiat2.TransfUtils
  fiat2.CollectionTransf fiat2.StringFacts
  fiat2.UniqueDictIndexImpl fiat2.UniqueIndexInstall fiat2.UniqueIndexGate
  fiat2.UniqueIndexUse fiat2.TrigramIndexImpl fiat2.Surface.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List Permutation Sorted Lia.

Import ListNotations.

(* Using the trigram index: a substring query becomes a probe and a recheck.

   A trigram match is NECESSARY but not SUFFICIENT: a row sharing a trigram
   with the pattern need not contain the pattern.  So the rewrite keeps the
   source's own `contains` test, applied to the rows the probe produced.

   The probe needs TWO members of the index record at once, since the trigram
   dictionary maps a trigram to a set of primary KEYS and only the primary-key
   index turns those keys back into rows.  Hence the two sets of bridges
   below.

   The rule may fire only where the pattern HAS a trigram.  This first form
   decides that statically, the pattern being a literal of length at least
   three, so it needs no runtime guard. *)

Section WithWord.
  Notation value := (value).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.
  (* the text attribute the index is built on, and the table's primary key *)
  Context (attr key : string).
  (* the separators the index tokenizes on: the same ones to_idx was built
     with, since a pattern that straddles two words is in no bucket *)
  Context (seps : string).

  (* The bucket a trigram names, as the list the probe iterates.  A bucket
     that is absent and a bucket that is empty behave alike, which is what
     lets the rewrite answer an absent trigram with the empty set. *)
  Definition tri_bucket (g d : value) : list value :=
    match d with
    | VDict d' =>
        match dict_lookup g d' with
        | Some (VSet b) => b
        | _ => nil
        end
    | _ => nil
    end.

  Lemma key_at__In_tri_bucket : forall (g k d : value),
      TrigramIndexImpl.key_at g k d -> In k (tri_bucket g d).
  Proof.
    unfold TrigramIndexImpl.key_at, tri_bucket; intros g k d H.
    destruct d as [ | | | | | | d' | | | ]; try contradiction.
    destruct (dict_lookup g d') as [ b | ]; try contradiction.
    destruct b; try contradiction.
    exact H.
  Qed.

  (* The test a substring query runs on a row, as a function of the row.
     This is what the source expression's filter computes. *)
  Definition contains_test (p : string) (r : value) : bool :=
    match interp_binop OStrContains (row_key attr r) (VString p) with
    | VBool b => b
    | _ => false
    end.

  (* Passing the test means the pattern really occurs, which is the
     hypothesis tri_lookup_complete wants.  No typing is needed: a row whose
     attribute is not a string fails the test outright. *)
  Lemma contains_test_true__occurrence : forall p (r : value),
      contains_test p r = true ->
      String.index 0 p (TrigramIndexImpl.row_str attr r) <> None.
  Proof.
    unfold contains_test, TrigramIndexImpl.row_str; intros p r H.
    destruct (row_key attr r) as [ | | s | | | | | | | ];
      cbn in H; try discriminate.
    destruct (String.index 0 p s); discriminate.
  Qed.

  (* ------------------------------------------------------------------
     The probe and the scan agree.

     Left: the set the source query builds, by filtering the table.
     Right: the set the rewrite builds, by taking one trigram's bucket,
     turning each key back into its row, and rechecking.

     Completeness (left in right) is where the trigram reasoning lives.
     Soundness (right in left) needs nothing about trigrams at all: the
     primary-key probe only ever returns rows of the table, and the recheck
     is the source's own filter.  That asymmetry is exactly what makes a
     necessary-but-not-sufficient index sound to use.
     ------------------------------------------------------------------ *)
  (* What the probe does with one key: turn it back into its row, and keep
     that row only if it really contains the pattern. *)
  Definition probe_body (rows : list value) (p : string) (k : value) : list value :=
    match dict_lookup k (UniqueDictIndexImpl.idx_entries key rows) with
    | Some r => if contains_test p r then [r] else nil
    | None => nil
    end.

  Lemma probe_recheck_eq :
    forall (rows : list value) (p : string),
      3 <= String.length p ->
      sep_free seps p = true ->
      NoDup (List.map (row_key key) rows) ->
      list_to_set (filter (contains_test p) (list_to_set rows))
      = list_to_set
          (flat_map (probe_body rows p)
             (tri_bucket (VString (String.substring 0 3 p))
                (TrigramIndexImpl.tri_entries attr key seps rows))).
  Proof.
    intros rows p H_len H_free H_nd.
    apply NoDup_SSorted_double_incl_eq;
      auto using list_to_set_NoDup, list_to_set_SSorted.
    1:{ (* every row the scan keeps is a row the probe finds and rechecks *)
        unfold incl; intros v H_in.
        apply list_to_set_incl, filter_In in H_in as [ H_in H_p ].
        apply list_to_set_incl in H_in.
        apply list_to_set_incl_r, in_flat_map.
        exists (row_key key v); split.
        1:{ apply key_at__In_tri_bucket.
            (* word_ok is implicit but not found by instance search from
               outside the section, so it is named here and below *)
            apply (TrigramIndexImpl.tri_lookup_complete attr key seps);
              [ exact H_in | exact H_free | exact H_len
              | apply contains_test_true__occurrence; exact H_p ]. }
        1:{ unfold probe_body.
            rewrite (UniqueDictIndexImpl.idx_lookup_Some key
                       rows v H_nd H_in).
            rewrite H_p. cbn [In]; auto. } }
    1:{ (* and every row the probe keeps is a row of the table that passes *)
        unfold incl; intros v H_in.
        apply list_to_set_incl, in_flat_map in H_in as [ k [ H_k H_v ] ].
        unfold probe_body in H_v.
        destruct (dict_lookup k (UniqueDictIndexImpl.idx_entries key rows))
          as [ r | ] eqn:E_lk; [ | contradiction ].
        destruct (contains_test p r) eqn:E_p; [ | contradiction ].
        destruct H_v as [ E_v | H_bad ]; [ subst r | contradiction ].
        apply (UniqueDictIndexImpl.idx_lookup_Some_inv key)
          in E_lk as [ H_rows _ ].
        apply list_to_set_incl_r, filter_In; split; [ | exact E_p ].
        apply list_to_set_incl_r; exact H_rows. }
  Qed.

  (* ------------------------------------------------------------------
     Every trigram of the pattern, not only its first.

     One shared trigram is necessary for an occurrence, which is what makes
     the single-bucket probe above sound.  EVERY trigram of the pattern is
     equally necessary, so the candidate set may be narrowed to the
     intersection of all their buckets before a single key is resolved.
     That is what gin_trgm_consistent does for LIKE, where every one of the
     query's trigrams has to be present; the recheck stays either way, since
     sharing all of them is still not sufficient.
     ------------------------------------------------------------------ *)

  (* The candidate set as the rewritten expression computes it: start from
     one bucket and keep narrowing by the others.  OSetIntersect interprets
     to a filter by set_mem, so the mirror is a chain of filters. *)
  Fixpoint tri_inter (b : list value) (gs : list string) (d : value) : list value :=
    match gs with
    | nil => b
    | g :: gs' =>
        tri_inter (filter (fun v => set_mem v (tri_bucket (VString g) d)) b) gs' d
    end.

  Lemma set_mem_true_iff : forall (v : value) l, set_mem v l = true <-> In v l.
  Proof.
    unfold set_mem; intros v l; rewrite existsb_exists; split.
    1:{ intros [ y [ H_in H_eq ] ]. apply value_eqb_eq in H_eq; subst; assumption. }
    1:{ intros H_in. exists v; split; [ assumption | apply value_eqb_refl ]. }
  Qed.

  Lemma In_tri_inter : forall gs (d v : value) b,
      In v (tri_inter b gs d)
      <-> In v b /\ (forall g, In g gs -> In v (tri_bucket (VString g) d)).
  Proof.
    induction gs as [ | g gs IH ]; intros d v b; cbn [tri_inter].
    1:{ split; [ intros H; split; [ exact H | contradiction ] | ].
        intros [ H _ ]; exact H. }
    rewrite IH. split.
    1:{ intros [ H_f H_all ]. apply filter_In in H_f as [ H_b H_m ].
        split; [ exact H_b | ]. intros g' [ E | H_in ].
        1: subst g'; apply set_mem_true_iff; exact H_m.
        1: apply H_all; exact H_in. }
    1:{ intros [ H_b H_all ]. split.
        1:{ apply filter_In; split; [ exact H_b | ].
            apply set_mem_true_iff, H_all. left; reflexivity. }
        1: intros g' H_in; apply H_all; right; exact H_in. }
  Qed.

  (* The scan and ANY sound candidate set agree.

     This is the real content, and it is weaker than it looks: the candidate
     list is arbitrary, and the only obligation is COMPLETENESS -- every row
     the scan would keep has its key in the list.  Soundness needs nothing,
     because the recheck is the source's own filter and the key probe only
     ever returns rows of the table.

     That asymmetry is what makes a necessary-but-not-sufficient index sound
     to use, and stating it this way means every candidate-set construction
     -- one bucket, all the buckets of a literal's trigrams, or a fold over
     a pattern known only at run time -- discharges the same lemma and
     differs only in how it proves completeness. *)
  Lemma probe_recheck_cands_eq :
    forall (rows : list value) (p : string) (cl : list value),
      NoDup (List.map (row_key key) rows) ->
      (forall (r : value), In r rows -> contains_test p r = true ->
                           In (row_key key r) cl) ->
      list_to_set (filter (contains_test p) (list_to_set rows))
      = list_to_set (flat_map (probe_body rows p) cl).
  Proof.
    intros rows p cl H_nd H_compl.
    apply NoDup_SSorted_double_incl_eq;
      auto using list_to_set_NoDup, list_to_set_SSorted.
    1:{ (* completeness, which is the hypothesis *)
        unfold incl; intros v H_in.
        apply list_to_set_incl, filter_In in H_in as [ H_in H_p ].
        apply list_to_set_incl in H_in.
        apply list_to_set_incl_r, in_flat_map.
        exists (row_key key v); split; [ apply H_compl; assumption | ].
        unfold probe_body.
        rewrite (UniqueDictIndexImpl.idx_lookup_Some key rows v H_nd H_in).
        rewrite H_p. cbn [In]; auto. }
    1:{ (* soundness, which is free *)
        unfold incl; intros v H_in.
        apply list_to_set_incl, in_flat_map in H_in as [ kk [ H_k H_v ] ].
        unfold probe_body in H_v.
        destruct (dict_lookup kk (UniqueDictIndexImpl.idx_entries key rows))
          as [ r | ] eqn:E_lk; [ | contradiction ].
        destruct (contains_test p r) eqn:E_p; [ | contradiction ].
        destruct H_v as [ E_v | H_bad ]; [ subst r | contradiction ].
        apply (UniqueDictIndexImpl.idx_lookup_Some_inv key)
          in E_lk as [ H_rows _ ].
        apply list_to_set_incl_r, filter_In; split; [ | exact E_p ].
        apply list_to_set_incl_r; exact H_rows. }
  Qed.

  (* The scan and the all-trigram probe agree.  Completeness now rests on
     tri_lookup_complete_all, once per trigram probed; soundness is
     unchanged and needs nothing about trigrams, since the recheck is the
     source's own filter and the key probe only returns rows of the table.

     The first trigram is a separate argument from the rest because the
     intersection has to start somewhere: there is no expression for the set
     of all keys, so a narrowing chain needs a nonempty bucket list to begin
     with.  g0 need not be p's FIRST trigram -- any trigram of p will do. *)
  Lemma probe_recheck_all_eq :
    forall (rows : list value) (p g0 : string) (gs : list string),
      In g0 (trigrams p) ->
      sep_free seps p = true ->
      (forall g, In g gs -> In g (trigrams p)) ->
      NoDup (List.map (row_key key) rows) ->
      list_to_set (filter (contains_test p) (list_to_set rows))
      = list_to_set
          (flat_map (probe_body rows p)
             (tri_inter
                (tri_bucket (VString g0)
                   (TrigramIndexImpl.tri_entries attr key seps rows))
                gs (TrigramIndexImpl.tri_entries attr key seps rows))).
  Proof.
    intros rows p g0 gs H_g0 H_free H_gs H_nd.
    pose proof (In_trigrams_nonempty _ _ H_g0) as H_pne.
    apply probe_recheck_cands_eq; [ exact H_nd | ].
    intros r H_in H_p. apply In_tri_inter; split.
    1:{ apply key_at__In_tri_bucket.
        apply (TrigramIndexImpl.tri_lookup_complete_all attr key seps _ _ p g0);
          [ exact H_in | exact H_free | exact H_pne
          | apply contains_test_true__occurrence; exact H_p
          | exact H_g0 ]. }
    1:{ intros g H_g. apply key_at__In_tri_bucket.
        apply (TrigramIndexImpl.tri_lookup_complete_all attr key seps _ _ p g);
          [ exact H_in | exact H_free | exact H_pne
          | apply contains_test_true__occurrence; exact H_p
          | apply H_gs; exact H_g ]. }
  Qed.

End WithWord.

Section WithIndexUse.
  (* the trigram index's own binders *)
  Context (hole attr key tup acc gvar sacc bkt : string).
  Context (H_tup_acc : tup <> acc) (H_tup_gvar : tup <> gvar)
    (H_tup_sacc : tup <> sacc) (H_tup_bkt : tup <> bkt) (H_gvar_sacc : gvar <> sacc).
  (* The primary-key index's binders.  Its attribute is the trigram index's
     key: the buckets hold keys, so only this index can turn them back into
     rows, and the two have to agree on which attribute that is. *)
  Context (utup uacc : string).
  Context (H_utup_uacc : utup <> uacc).
  (* the two fields the installation pairs *)
  Context (id_tag aux_tag : string).
  Context (H_tags_diff : id_tag <> aux_tag).
  (* the tags the two dictionaries sit under inside one index record *)
  Context (tri_tag pk_tag : string).
  (* the binders the rewritten form introduces: a bucket, a key, its row *)
  Context (b k y : string).
  (* last, so that the lemmas above keep the arguments they had: only the
     delete rule needs these two, since the delete body is the only one that
     reads a position and a bucket under each other's binders *)
  Context (H_sacc_bkt : sacc <> bkt) (H_gvar_bkt : gvar <> bkt).
  (* The all-trigram probe's own two binders: the position the candidate
     fold is at, and the candidate set it has narrowed so far.  Added after
     everything above so that the existing lemmas keep the arguments they
     had -- only the lemmas that mention these two acquire them. *)
  Context (cpos cacc : string).
  Context (H_cacc_cpos : cacc <> cpos).
  (* The separators the index tokenizes on, and the two binders of the
     fold over a row's WORDS: the word itself, and the index built from the
     words before it.  Last again, for the same reason. *)
  Context (seps wrd wacc : string).
  Context (H_wrd_tup : wrd <> tup).
  Context (H_wrd_gvar : wrd <> gvar).
  Context (H_wrd_sacc : wrd <> sacc).
  Context (H_wrd_bkt : wrd <> bkt).
  Context (H_wacc_tup : wacc <> tup).
  Context (H_wacc_gvar : wacc <> gvar).
  Context (H_wacc_sacc : wacc <> sacc).
  Context (H_wacc_bkt : wacc <> bkt).
  Context (H_wacc_wrd : wacc <> wrd).

  Notation tridx :=
    (trigram_idx hole attr key tup acc gvar sacc bkt seps wrd wacc).
  Notation uidx := (unique_dict_idx hole key utup uacc).

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Notation value := (value).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Notation tridx_wf :=
      (TrigramIndexImpl.idx_wf hole attr key tup acc gvar sacc bkt seps wrd wacc
         (locals := locals)).
    Notation uidx_wf := (UniqueDictIndexImpl.idx_wf hole key utup uacc (locals := locals)).

    (* The two invariants the rule reads off the store, each at its own tag.
       The trigram member asks only for its own idx_wf, which the install
       manufactures from typing; the primary-key member asks for the STRONG
       relation, which it cannot, and which the declaration supplies. *)
    Notation tri_aux_wf_at := (aux_wf_for_idx id_tag aux_tag tri_tag tridx_wf).
    Notation unique_aux_wf_at :=
      (aux_wf_for_idx id_tag aux_tag pk_tag
         (UniqueDictIndexImpl.idx_wf_unique hole key utup uacc (locals := locals))).

    Lemma flat_map_pointwise : forall (f g : value -> list value) (l : list value),
        (forall v, f v = g v) -> flat_map f l = flat_map g l.
    Proof.
      intros f g l H; induction l as [ | v l IH ]; cbn [flat_map];
        [ reflexivity | rewrite H, IH; reflexivity ].
    Qed.

    Lemma filter_pointwise : forall (f1 f2 : value -> bool) (l : list value),
        (forall v, f1 v = f2 v) -> filter f1 l = filter f2 l.
    Proof.
      intros f1 f2 l H; induction l as [ | v l IH ]; cbn [filter];
        [ reflexivity | rewrite H, IH; reflexivity ].
    Qed.

    (* A record's field has the type the record type gives it. *)
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

    Lemma interp_EFlatmap_set : forall (store env : locals) e1 x e2,
        interp_expr store env (EFlatmap LikeSet e1 x e2)
        = match interp_expr store env e1 with
          | VSet l1 =>
              VSet (list_to_set
                      (flat_map (fun v => match interp_expr store (map.put env x v) e2 with
                                          | VSet l2 => l2
                                          | _ => nil
                                          end) l1))
          | _ => VUnit
          end.
    Proof. reflexivity. Qed.

    (* ------------------------------------------------------------------
       Maintaining the index: inserting a row updates its buckets.

       Unlike the lookup rules this one needs no invariant and no
       declaration at all: it is the equation

         to_idx (r :: l)  =  <r's own update> (to_idx l)

       which holds by the very shape of to_idx, a fold over the rows.  So it
       is a plain expression rule, and it fires on every table whether
       anything is declared or not.

       The emitted form reuses the index's OWN per-row body: bind the index
       of the rest to acc, bind the new row to tup, and run tri_row_body.
       Nothing about trigrams has to be re-proved.
       ------------------------------------------------------------------ *)

    Notation tri_row_body' :=
      (TrigramIndexImpl.tri_row_body attr key tup acc gvar sacc bkt
         seps wrd wacc).

    Definition to_idx_at (d : expr) : expr :=
      EFold d (EAtom (AEmptyDict Unranged None)) tup acc tri_row_body'.

    (* to_idx_at spelled out, so that the rule can match it.  Every binder
       and attribute occurrence is a pattern variable, and the guard checks
       that they are the ones this index uses. *)
    Notation etri_idx tup0 tup1 tup2 tup3 acc0 acc1
      wrd0 wrd1 wacc0 wacc1 gvar0 gvar1 gvar2 sacc0 sacc1 sacc2
      bkt0 bkt1 attr0 key0 key1 seps0 d :=
      (EFold d (EAtom (AEmptyDict Unranged None)) tup0 acc0
         (EFold (EBinop OWords (EAtom (AString seps0))
                   (EAccess (EVar tup1) attr0))
            (EVar acc1) wrd0 wacc0
            (EFold (EUnop OTrigrams
                      (EBinop OConcatString (EAtom (AString "  "))
                         (EBinop OConcatString (EVar wrd1)
                            (EAtom (AString " ")))))
               (EVar wacc1) gvar0 sacc0
               (ETernop OInsert (EVar sacc1) (EVar gvar1)
                  (EOptMatch
                     (EBinop OLookup (EVar sacc2) (EVar gvar2))
                     (EBinop OSetInsert (EAtom (AEmptySet None))
                        (EAccess (EVar tup2) key0))
                     bkt0 (EBinop OSetInsert (EVar bkt1)
                             (EAccess (EVar tup3) key1))))))).

    Definition cons_to_tri_insert_head (e : expr) : expr :=
      match e with
      | etri_idx tup0 tup1 tup2 tup3 acc0 acc1
          wrd0 wrd1 wacc0 wacc1 gvar0 gvar1 gvar2 sacc0 sacc1 sacc2
          bkt0 bkt1 attr0 key0 key1 seps0
          (EBinop OCons e1 e2) =>
          if (all_eqb [(tup, [tup0; tup1; tup2; tup3]);
                       (acc, [acc0; acc1]); (wrd, [wrd0; wrd1]);
                       (wacc, [wacc0; wacc1]); (gvar, [gvar0; gvar1; gvar2]);
                       (sacc, [sacc0; sacc1; sacc2]); (bkt, [bkt0; bkt1]);
                       (attr, [attr0]); (key, [key0; key1]); (seps, [seps0])]
              && negb (free_immut_in acc e1))%bool
          then ELet (to_idx_at e2) acc (ELet e1 tup tri_row_body')
          else e
      | _ => e
      end.

    Lemma interp_ELet_step : forall (store env : locals) e1 x e2,
        interp_expr store env (ELet e1 x e2)
        = interp_expr store (map.put env x (interp_expr store env e1)) e2.
    Proof. reflexivity. Qed.

    Lemma fold_right_pointwise :
      forall (f g : value -> value -> value) (a : value) (l : list value),
        (forall v acc', f v acc' = g v acc') -> fold_right f a l = fold_right g a l.
    Proof.
      intros f g a l H; induction l as [ | v l IH ]; cbn [fold_right];
        [ reflexivity | rewrite H, IH; reflexivity ].
    Qed.

    Lemma cons_to_tri_insert_head_preserve_ty : forall (Gstore : tenv),
        tup <> acc -> preserve_ty Gstore cons_to_tri_insert_head.
    Proof.
      unfold preserve_ty; intros Gstore H_ne e t Genv H_Gs H_Ge H_t.
      repeat destruct_subexpr.
      cbn [cons_to_tri_insert_head]. repeat (case_match; auto; []).
      cbn in * |-.
      rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition idtac.
      rewrite eqb_eq in *; subst.
      (* only the top of the source is inverted: the fold's body typing is
         exactly what both occurrences of the fold need, so it is reused
         rather than rebuilt *)
      lazymatch goal with
      | H : type_of _ _ (EFold _ _ _ _ _) _ |- _ => inversion H; subst; clear H
      end.
      lazymatch goal with
      | H : type_of _ _ (EBinop OCons _ _) _ |- _ =>
          inversion H; subst; clear H
      end.
      invert_type_of_op_clear.
      eapply TyELet.
      1:{ unfold to_idx_at. eapply TyEFold; eassumption. }
      1:{ eapply TyELet.
          (* the row is typed under acc's binder now, which is what the
             rule's freshness side condition is for *)
          1:{ apply not_free_immut_put_ty2; [ assumption | eassumption ]. }
          1:{ rewrite <- (Properties.map.put_comm _ _ _ _ Genv H_ne).
              eassumption. } }
    Qed.

    Lemma cons_to_tri_insert_head_preserve_sem :
      forall (Gstore : tenv) (store : locals),
        tup <> acc -> preserve_sem Gstore store cons_to_tri_insert_head.
    Proof.
      unfold preserve_sem; intros Gstore store H_ne e t Genv env H_Gs H_Ge H_t H_sw H_ew.
      repeat destruct_subexpr.
      cbn [cons_to_tri_insert_head]. repeat (case_match; auto; []).
      cbn in * |-.
      rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition idtac.
      rewrite eqb_eq in *; subst.
      (* the rest of the table really is a list: without that the equation
         is false, since the index of a non-list is VUnit while one row's
         update of VUnit is not *)
      lazymatch type of H_t with
      | type_of _ _ (EFold (EBinop OCons _ ?rest) _ _ _ _) _ =>
          assert (H_l : exists l, interp_expr store env rest = VList l)
      end.
      1:{ repeat invert_type_of_clear; repeat invert_type_of_op_clear.
          lazymatch goal with
          | H : type_of _ _ ?rest (TList ?t1) |- context[interp_expr _ _ ?rest] =>
              pose proof (type_sound Gstore Genv rest (TList t1) H H_Gs H_Ge
                            store env H_sw H_ew) as H_v
          end.
          apply type_of_value_TList_inv in H_v as [ l [ E_l _ ] ].
          exists l; exact E_l. }
      destruct H_l as [ l E_l ].
      rewrite interp_ELet_step, interp_ELet_step.
      unfold to_idx_at.
      rewrite !interp_EFold, interp_EBinop, E_l.
      cbn [interp_binop].
      rewrite <- (not_free_immut_put_sem _ acc store env) by assumption.
      cbn [fold_right].
      rewrite (Properties.map.put_comm _ _ _ _ env H_ne).
      reflexivity.
    Qed.

    Lemma cons_to_tri_insert_head_sound :
      tup <> acc -> expr_transf_sound (locals := locals) cons_to_tri_insert_head.
    Proof.
      unfold expr_transf_sound; intros H_ne *; intros.
      intuition idtac.
      1: eapply cons_to_tri_insert_head_preserve_ty; eauto.
      1: eapply cons_to_tri_insert_head_preserve_sem; [ | | | eauto .. ]; auto.
    Qed.

    Lemma cons_to_tri_insert_sound : forall is_tbl_ty' aux_ty aux_wf,
        tup <> acc ->
        aug_transf_sound (locals := locals) is_tbl_ty' aux_ty aux_wf
          (fun tbl => fold_command_with_globals [tbl] cons_to_tri_insert_head).
    Proof.
      intros * H_ne.
      apply fold_command_with_globals_sound.
      apply expr_transf_sound__expr_aug_transf_sound.
      apply cons_to_tri_insert_head_sound; exact H_ne.
    Qed.

    (* What to_idx_at computes, in Gallina.  The insert rule above needed
       nothing of the sort, because both of its sides recompute; every rule
       that turns a recomputation into a READ of the stored index has to go
       through this, since the index's invariant is stated in these terms. *)
    Lemma interp_to_idx_at :
      forall (store env : locals) (d : expr) rt (rows : list value),
        access_record rt attr = Success TString ->
        Forall (fun r => type_of_value r (TRecord rt)) rows ->
        interp_expr store env d = VList rows ->
        interp_expr store env (to_idx_at d)
        = TrigramIndexImpl.tri_entries attr key seps rows.
    Proof.
      intros * H_attr H_rows E_d.
      unfold to_idx_at, TrigramIndexImpl.tri_entries.
      rewrite interp_EFold, E_d, interp_EAtom. cbn [interp_atom].
      (* the index's own section hypotheses, which every lemma from it
         carries: the binders it folds with are distinct *)
      apply TrigramIndexImpl.interp_to_idx_fold; try assumption.
      eapply TrigramIndexImpl.typed_rows_have_text; eassumption.
    Qed.

    Lemma tri_is_tbl_ty_inv : forall t,
        @IndexInterface.is_tbl_ty tridx t = true ->
        exists rt kt, t = TList (TRecord rt)
                      /\ access_record rt attr = Success TString
                      /\ access_record rt key = Success kt.
    Proof.
      cbn [IndexInterface.is_tbl_ty trigram_idx]; unfold TrigramIndexImpl.is_tbl_ty.
      intros t H.
      destruct t as [ | | | | | t1 | | | | ]; try discriminate.
      destruct t1 as [ | | | | | | rt | | | ]; try discriminate.
      destruct (access_record rt attr) as [ at_ty | ] eqn:E_attr; try discriminate.
      destruct (access_record rt key) as [ kt | ] eqn:E_key; try discriminate.
      apply type_eqb_eq in H; subst at_ty.
      exists rt, kt; split; [ reflexivity | split; [ exact E_attr | exact E_key ] ].
    Qed.

    Section WithTable.
      Context (tbl : string).

      Notation tri_e := (EAccess (EAccess (ELoc tbl) aux_tag) tri_tag).
      Notation pk_e := (EAccess (EAccess (ELoc tbl) aux_tag) pk_tag).

      (* Probe one trigram's bucket, turn each key back into its row with
         the primary-key index, and recheck the pattern on what comes back.
         A trigram match is necessary and not sufficient, so dropping the
         recheck would be unsound. *)
      Definition trigram_probe (g p : expr) : expr :=
        EFlatmap LikeSet
          (EOptMatch (EBinop OLookup tri_e g) (EAtom (AEmptySet None)) b (EVar b))
          k
          (EOptMatch (EBinop OLookup pk_e (EVar k)) (EAtom (AEmptySet None))
             y (EIf (EBinop OStrContains (EAccess (EVar y) attr) p)
                  (EBinop OSetInsert (EAtom (AEmptySet None)) (EVar y))
                  (EAtom (AEmptySet None)))).

      (* Reading the table's record never looks at the environment, so both
         dictionaries have the same value under every binder the probe
         introduces. *)
      Lemma interp_tbl_access_env_irrel : forall (store env env' : locals) t1 t2,
          interp_expr store env (EAccess (EAccess (ELoc tbl) t1) t2)
          = interp_expr store env' (EAccess (EAccess (ELoc tbl) t1) t2).
      Proof. reflexivity. Qed.

      (* ------------------------------------------------------------------
         Everything the rule needs about the store, read off the two
         invariants and the store's type at once.

         The trigram member contributes its dictionary; the primary-key
         member contributes its dictionary AND the distinctness of the keys,
         which is the part no index establishes from typing and which the
         declaration is spent on.  The typing is what turns the trigram
         index's own well-formedness into the Gallina mirror, since to_idx
         only behaves as the mirror says on rows whose attribute is a string.
         ------------------------------------------------------------------ *)
      Lemma invariants__probe_data :
        forall tl rt (v : value),
          access_record rt attr = Success TString ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          type_of_value v (TRecord tl) ->
          tri_aux_wf_at v ->
          unique_aux_wf_at v ->
          exists rv rv_aux rows td,
            v = VRecord rv
            /\ record_proj id_tag rv = VList rows
            /\ record_proj aux_tag rv = VRecord rv_aux
            /\ record_proj tri_tag rv_aux = VDict td
            /\ record_proj pk_tag rv_aux
               = VDict (UniqueDictIndexImpl.idx_entries key rows)
            /\ TrigramIndexImpl.tri_entries attr key seps rows = VDict td
            /\ Forall (fun e : value * value =>
                         match snd e with VSet _ => True | _ => False end) td
            /\ NoDup (List.map (row_key key) rows).
      Proof.
        unfold aux_wf_for_idx, UniqueDictIndexImpl.idx_wf_unique,
          UniqueDictIndexImpl.idx_wf, UniqueDictIndexImpl.keys_distinct,
          TrigramIndexImpl.idx_wf.
        intros tl rt v H_attr E_id.
        (* v is destructed before the invariants are introduced, so that
           their names survive; and each later destruct is pushed into them
           by hand, since destruct rewrites the goal but not hypotheses *)
        destruct v as [ | | | | | rv | | | | ];
          intros H_vty H_tri H_pk;
          cbv beta iota in H_tri, H_pk; try contradiction.
        (* destruct on a match's scrutinee substitutes it in the hypotheses
           too, so each step only has to reduce the match it exposed *)
        destruct (access_record rv id_tag) as [ v_id | ] eqn:E_vid;
          cbv beta iota in H_tri, H_pk; try contradiction.
        destruct (access_record rv aux_tag) as [ v_aux | ] eqn:E_vaux;
          cbv beta iota in H_tri, H_pk; try contradiction.
        destruct v_aux as [ | | | | | rv_aux | | | | ];
          cbv beta iota in H_tri, H_pk; try contradiction.
        destruct (access_record rv_aux tri_tag) as [ v_tri | ] eqn:E_vtri;
          cbv beta iota in H_tri; try contradiction.
        destruct (access_record rv_aux pk_tag) as [ v_pk | ] eqn:E_vpk;
          cbv beta iota in H_pk; try contradiction.
        destruct H_pk as [ E_pk H_kd ].
        (* the table's own rows, and their typing *)
        assert (H_idty : type_of_value v_id (TList (TRecord rt)))
          by (eapply type_of_value_field; [ exact H_vty | exact E_vid | exact E_id ]).
        apply type_of_value_TList_inv in H_idty as [ rows [ E_rows H_rows ] ].
        subst v_id.
        cbn [UniqueDictIndexImpl.keys_distinct] in H_kd.
        (* the trigram dictionary is the Gallina mirror, hence a dictionary
           whose buckets are sets *)
        rewrite (TrigramIndexImpl.fiat2_gallina_to_idx hole attr key tup acc
                   gvar sacc bkt
                   H_tup_acc H_tup_gvar H_tup_sacc H_tup_bkt H_gvar_sacc
                   seps wrd wacc H_wrd_tup H_wacc_tup H_wacc_wrd
                   (locals_ok := locals_ok) rows
                   (TrigramIndexImpl.typed_rows_have_text attr rows rt H_attr H_rows))
          in H_tri.
        assert (H_bs : TrigramIndexImpl.buckets_are_sets
                         (TrigramIndexImpl.tri_entries attr key seps rows)).
        1:{ unfold TrigramIndexImpl.tri_entries.
            apply (TrigramIndexImpl.tri_entries_buckets attr key seps).
            constructor. }
        destruct (TrigramIndexImpl.tri_entries attr key seps rows) as
          [ | | | | | | td | | | ] eqn:E_te;
          cbn [TrigramIndexImpl.buckets_are_sets] in H_bs; try contradiction.
        (* and the primary-key dictionary is its own mirror *)
        rewrite (UniqueDictIndexImpl.fiat2_gallina_to_idx hole key utup uacc
                   H_utup_uacc (locals_ok := locals_ok) rows) in E_pk.
        exists rv, rv_aux, rows, td.
        repeat split; try assumption;
          try (apply access_record__record_proj; assumption).
        1:{ apply access_record__record_proj. rewrite E_vtri, H_tri. reflexivity. }
        1:{ apply access_record__record_proj. rewrite E_vpk, E_pk. reflexivity. }
      Qed.

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
         Every trigram of the pattern, at the expression level.

         The probe is split in two: the CANDIDATE SET it iterates, and what
         it does with each key it finds there.  Splitting it this way is what
         makes the all-trigram rule a generalisation rather than a rival --
         trigram_probe IS probe_from of a single bucket, by definition, as
         trigram_probe_is_probe_from records.
         ------------------------------------------------------------------ *)
      Definition tri_bucket_e (g : expr) : expr :=
        EOptMatch (EBinop OLookup tri_e g) (EAtom (AEmptySet None)) b (EVar b).

      Definition probe_from (cand p : expr) : expr :=
        EFlatmap LikeSet cand k
          (EOptMatch (EBinop OLookup pk_e (EVar k)) (EAtom (AEmptySet None))
             y (EIf (EBinop OStrContains (EAccess (EVar y) attr) p)
                  (EBinop OSetInsert (EAtom (AEmptySet None)) (EVar y))
                  (EAtom (AEmptySet None)))).

      Lemma trigram_probe_is_probe_from : forall g p,
          trigram_probe g p = probe_from (tri_bucket_e g) p.
      Proof. reflexivity. Qed.

      (* One more bucket narrows the candidates.  Left-nested, so that the
         chain can be built by a fold over the pattern's trigram list and
         the empty list of extra trigrams leaves the single probe alone. *)
      Definition tri_cands_step (a : expr) (g : string) : expr :=
        EBinop OSetIntersect a (tri_bucket_e (EAtom (AString g))).

      Definition tri_cands_from (cnd : expr) (gs : list string) : expr :=
        fold_left tri_cands_step gs cnd.

      (* The candidate set of a pattern whose trigrams are g0 :: gs. *)
      Definition trigram_probe_all (g0 : string) (gs : list string) (p : expr) : expr :=
        probe_from (tri_cands_from (tri_bucket_e (EAtom (AString g0))) gs) p.

      Lemma interp_tri_bucket_e :
        forall (store env : locals) (g : expr) (gv : value) (td : list (value * value)),
          interp_expr store env g = gv ->
          interp_expr store env tri_e = VDict td ->
          Forall (fun e : value * value =>
                    match snd e with VSet _ => True | _ => False end) td ->
          interp_expr store env (tri_bucket_e g) = VSet (tri_bucket gv (VDict td)).
      Proof.
        intros * E_g E_tri H_sets.
        unfold tri_bucket_e.
        rewrite interp_EOptMatch, interp_EBinop, E_tri, E_g.
        cbn [interp_binop]. unfold tri_bucket.
        destruct (dict_lookup gv td) as [ bkv | ] eqn:E_lk.
        2:{ rewrite interp_EAtom. cbn [interp_atom]. reflexivity. }
        (* the bucket a hit returns is a set, because every bucket is *)
        assert (H_bl : exists bl, bkv = VSet bl).
        1:{ apply DictIndexImpl.dict_lookup_Some_In in E_lk.
            eapply List.Forall_In in H_sets; [ | exact E_lk ].
            destruct bkv as [ | | | | | | | | bl | ];
              cbn [snd] in H_sets; try contradiction.
            exists bl; reflexivity. }
        destruct H_bl as [ bl E_bl ]; subst bkv.
        rewrite interp_EVar. unfold get_local. rewrite map.get_put_same.
        reflexivity.
      Qed.

      (* The narrowing chain computes the Gallina intersection.  OSetIntersect
         interprets to a filter by set_mem, which is exactly tri_inter's
         step, so the two agree by construction. *)
      Lemma interp_tri_cands_from :
        forall gs (store env : locals) (cnd : expr) (al : list value)
               (td : list (value * value)),
          interp_expr store env tri_e = VDict td ->
          Forall (fun e : value * value =>
                    match snd e with VSet _ => True | _ => False end) td ->
          interp_expr store env cnd = VSet al ->
          interp_expr store env (tri_cands_from cnd gs)
          = VSet (tri_inter al gs (VDict td)).
      Proof.
        induction gs as [ | g gs IH ]; intros store env cnd al td E_tri H_sets E_cnd.
        1: exact E_cnd.
        cbn [tri_cands_from fold_left tri_inter].
        eapply IH; [ exact E_tri | exact H_sets | ].
        unfold tri_cands_step.
        rewrite interp_EBinop, E_cnd.
        rewrite (interp_tri_bucket_e store env (EAtom (AString g)) (VString g) td
                   eq_refl E_tri H_sets).
        cbn [interp_binop]. reflexivity.
      Qed.

      (* What the probe does once it has its candidates.  Stated for an
         arbitrary candidate expression, so that both rules use it. *)
      Lemma interp_probe_from :
        forall (store env : locals) (cand p : expr) (cl : list value) (pv : string)
               (pd : list (value * value)),
          interp_expr store env cand = VSet cl ->
          (forall (v r : value),
              interp_expr store (map.put (map.put env k v) y r) p = VString pv) ->
          interp_expr store env pk_e = VDict pd ->
          interp_expr store env (probe_from cand p)
          = VSet (list_to_set
                    (flat_map
                       (fun kk => match dict_lookup kk pd with
                                  | Some r => if contains_test attr pv r then [r] else nil
                                  | None => nil
                                  end)
                       cl)).
      Proof.
        intros * E_cand E_p E_pk.
        unfold probe_from. rewrite interp_EFlatmap_set, E_cand; cbv beta iota.
        apply (f_equal (fun z : list value => VSet (list_to_set z))).
        (* the body, one key at a time *)
        apply flat_map_pointwise; intros v.
        rewrite interp_EOptMatch, interp_EBinop.
        rewrite (interp_tbl_access_env_irrel store (map.put env k v) env aux_tag pk_tag).
        rewrite E_pk, interp_EVar.
        unfold get_local; rewrite map.get_put_same.
        cbn [interp_binop].
        destruct (dict_lookup v pd) as [ r | ].
        2:{ rewrite interp_EAtom; cbn [interp_atom]; reflexivity. }
        rewrite interp_EIf, interp_EBinop, interp_EAccess, interp_EVar.
        unfold get_local; rewrite map.get_put_same.
        rewrite (E_p v r).
        unfold contains_test, row_key.
        destruct (interp_binop OStrContains
                    (match r with VRecord fs => record_proj attr fs | _ => VUnit end)
                    (VString pv)) as [ | bb | | | | | | | | ].
        2:{ destruct bb.
            1:{ rewrite interp_EBinop, interp_EAtom, interp_EVar.
                unfold get_local; rewrite map.get_put_same.
                cbn [interp_atom interp_binop set_insert]. reflexivity. }
            1:{ rewrite interp_EAtom; cbn [interp_atom]; reflexivity. } }
        all: reflexivity.
      Qed.

      (* What the probe computes.  The two dictionaries are given as values
         here; which values they are is the business of the invariants, and
         is settled at the rewrite site. *)
      Lemma interp_trigram_probe :
        forall (store env : locals) (g p : expr) (gv : value) (pv : string)
               (td pd : list (value * value)),
          (* g is read outside the binders the probe introduces, p inside
             them: a pattern that mentions neither k nor y is enough *)
          interp_expr store env g = gv ->
          (forall (v r : value),
              interp_expr store (map.put (map.put env k v) y r) p = VString pv) ->
          interp_expr store env tri_e = VDict td ->
          interp_expr store env pk_e = VDict pd ->
          Forall (fun e : value * value =>
                    match snd e with VSet _ => True | _ => False end) td ->
          interp_expr store env (trigram_probe g p)
          = VSet (list_to_set
                    (flat_map
                       (fun kk => match dict_lookup kk pd with
                                  | Some r => if contains_test attr pv r then [r] else nil
                                  | None => nil
                                  end)
                       (tri_bucket gv (VDict td)))).
      Proof.
        intros * E_g E_p E_tri E_pk H_sets.
        unfold trigram_probe. rewrite interp_EFlatmap_set.
        (* the source: the bucket of the trigram, present or absent *)
        rewrite interp_EOptMatch, interp_EBinop, E_tri, E_g.
        cbn [interp_binop]. unfold tri_bucket.
        destruct (dict_lookup gv td) as [ bkv | ] eqn:E_lk.
        2:{ rewrite interp_EAtom. cbn [interp_atom].
            cbn [flat_map list_to_set]. reflexivity. }
        (* the bucket a hit returns is a set, because every bucket is *)
        assert (H_bl : exists bl, bkv = VSet bl).
        1:{ apply DictIndexImpl.dict_lookup_Some_In in E_lk.
            eapply List.Forall_In in H_sets; [ | exact E_lk ].
            (* substituting a constructor for bkv does not reduce the match
               inside the hypothesis, so reduce it again after the destruct *)
            destruct bkv as [ | | | | | | | | bl | ];
              cbn [snd] in H_sets; try contradiction.
            exists bl; reflexivity. }
        destruct H_bl as [ bl E_bl ]; subst bkv.
        rewrite interp_EVar. unfold get_local. rewrite map.get_put_same.
        apply (f_equal (fun z : list value => VSet (list_to_set z))).
        (* and the body, one key at a time *)
        apply flat_map_pointwise; intros v.
        rewrite interp_EOptMatch, interp_EBinop.
        rewrite (interp_tbl_access_env_irrel store (map.put env k v) env aux_tag pk_tag).
        rewrite E_pk, interp_EVar.
        unfold get_local; rewrite map.get_put_same.
        cbn [interp_binop].
        destruct (dict_lookup v pd) as [ r | ].
        2:{ rewrite interp_EAtom; cbn [interp_atom]; reflexivity. }
        rewrite interp_EIf, interp_EBinop, interp_EAccess, interp_EVar.
        unfold get_local; rewrite map.get_put_same.
        rewrite (E_p v r).
        unfold contains_test, row_key.
        destruct (interp_binop OStrContains
                    (match r with VRecord fs => record_proj attr fs | _ => VUnit end)
                    (VString pv)) as [ | bb | | | | | | | | ].
        (* only the boolean branch has anything to do: a test that is not a
           boolean fails the recheck and contributes nothing, on both sides *)
        2:{ destruct bb.
            1:{ rewrite interp_EBinop, interp_EAtom, interp_EVar.
                unfold get_local; rewrite map.get_put_same.
                cbn [interp_atom interp_binop set_insert]. reflexivity. }
            1:{ rewrite interp_EAtom; cbn [interp_atom]; reflexivity. } }
        all: reflexivity.
      Qed.
      (* ------------------------------------------------------------------
         The rule.

         The pattern is kept as an expression here and tested separately,
         so that the rule's shape stays shallow: a literal of at least three
         characters that holds no separator hands over its first trigram at
         rewrite time, and anything else leaves the program alone.

         The separator test is the second half of the condition, and it is
         not a technicality.  The index keys on WORDS, so a pattern
         straddling a separator -- "h J" against "Smith Jones" -- is in no
         bucket at all, and probing for it would lose the row.  On a
         literal the test is decided here, by evaluating sep_free; the
         runtime form below has to emit it as an expression. *)
      Definition literal_trigram (e : expr) : option expr :=
        match e with
        | EAtom (AString s) =>
            if (Nat.leb 3 (String.length s) && sep_free seps s)%bool
            then Some (EAtom (AString (String.substring 0 3 s)))
            else None
        | _ => None
        end.

      Lemma literal_trigram_Some : forall p g,
          literal_trigram p = Some g ->
          exists s, p = EAtom (AString s)
                    /\ 3 <= String.length s
                    /\ sep_free seps s = true
                    /\ g = EAtom (AString (String.substring 0 3 s)).
      Proof.
        unfold literal_trigram; intros p g H.
        destruct p as [ | | a | | | | | | | | | | | | | ]; try discriminate.
        destruct a as [ | | str | | | | | | ]; try discriminate.
        destruct (Nat.leb 3 (String.length str) && sep_free seps str)%bool
          eqn:E_len; [ | discriminate ].
        rewrite Bool.andb_true_iff in E_len; destruct E_len as [ E_len E_free ].
        injection H as H; subst.
        exists str; split; [ reflexivity | ].
        split; [ apply Nat.leb_le; exact E_len | ].
        split; [ exact E_free | reflexivity ].
      Qed.

      (* [row <- set(tbl[id_tag]), check(contains(row.attr, p)), ret row]
         -->
         probe tbl[aux_tag][tri_tag] with p's first trigram, resolve each
         key through tbl[aux_tag][pk_tag], and recheck contains. *)
      Definition trigram_lookup_head (e : expr) : expr :=
        match e with
        | flatmap_filter_set
            (EUnop OSetOfList (EAccess (ELoc tbl0) id_tag0))
            x0 (EBinop OStrContains (EAccess (EVar x1) attr0) p) x2 _ _ =>
            if all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x0, [x1; x2]);
                        (id_tag, [id_tag0])]
            then match literal_trigram p with
                 | Some g => trigram_probe g p
                 | None => e
                 end
            else e
        | _ => e
        end.

      (* destruct_subexpr, minus the cases that take a string apart: this
         rule's pattern keeps a string LITERAL, and descending into its
         characters does not terminate. *)
      Ltac destruct_subexpr_keep_str :=
        multimatch goal with
        | e : expr |- _ => destruct e; auto; []
        | o : unop |- _ => destruct o; auto; []
        | o : binop |- _ => destruct o; auto; []
        | a : atom |- _ => destruct a; auto; []
        | tag : collection_tag |- _ => destruct tag; auto; []
        end.

      Lemma trigram_lookup_head_preserve_sem :
        forall tl rt (Gstore : tenv) (store : locals),
          access_record rt attr = Success TString ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          match map.get store tbl with
          | Some v =>
              type_of_value v (TRecord tl) /\ tri_aux_wf_at v /\ unique_aux_wf_at v
          | _ => False
          end ->
          preserve_sem Gstore store trigram_lookup_head.
      Proof.
        unfold preserve_sem; intros * H_attr E_tbl E_id H_store.
        intros e t Genv env H_Gs H_Ge H_t H_sw H_ew.
        destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
        destruct H_store as [ H_vty [ H_tri H_pk ] ].
        destruct (invariants__probe_data tl rt v H_attr E_id H_vty H_tri H_pk)
          as [ rv [ rv_aux [ rows [ td [ E_vrec [ E_rows [ E_aux
             [ E_tri [ E_pk [ E_te [ H_sets H_nd ] ] ] ] ] ] ] ] ] ] ].
        subst v.
        repeat destruct_subexpr_keep_str.
        unfold trigram_lookup_head. cbv beta iota.
        case_match; auto.
        destruct (literal_trigram _) as [ g | ] eqn:E_lit; auto.
        (* the names the guard equated.  This comes FIRST: its subst would
           otherwise also eliminate the trigram the next step names. *)
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        repeat (rewrite eqb_eq in *; subst).
        (* destruct_subexpr introduces auto-named strings, so the pattern's
           own string gets a name of its own here *)
        apply literal_trigram_Some in E_lit
          as [ pstr [ E_p [ H_len [ H_free E_g ] ] ] ].
        (* the pattern and its trigram are literals from here on: both are
           substituted away, since destruct_subexpr named the pattern itself *)
        subst.
        (* everything the probe's semantics asks for, before rewriting with
           it, so that no step depends on the order of side goals *)
        assert (H_g : interp_expr store env
                        (EAtom (AString (String.substring 0 3 pstr)))
                      = VString (String.substring 0 3 pstr)) by reflexivity.
        assert (H_pv : forall (v r : value),
                   interp_expr store (map.put (map.put env k v) y r)
                     (EAtom (AString pstr)) = VString pstr) by reflexivity.
        assert (H_tri_e : interp_expr store env
                            (EAccess (EAccess (ELoc tbl) aux_tag) tri_tag) = VDict td)
          by (eapply interp_tbl_field; [ exact E_v | exact E_aux | exact E_tri ]).
        assert (H_pk_e : interp_expr store env
                           (EAccess (EAccess (ELoc tbl) aux_tag) pk_tag)
                         = VDict (UniqueDictIndexImpl.idx_entries key rows))
          by (eapply interp_tbl_field; [ exact E_v | exact E_aux | exact E_pk ]).
        rewrite (interp_trigram_probe store env _ _ _ pstr td _
                   H_g H_pv H_tri_e H_pk_e H_sets).
        (* the scan side *)
        rewrite interp_flatmap_filter_set, interp_ESetOf,
          interp_EAccess, interp_ELoc.
        unfold get_local; rewrite E_v; cbv beta iota.
        rewrite E_rows; cbv beta iota.
        (* the filter the source runs is the test the equation is stated with *)
        erewrite filter_pointwise with (f2 := contains_test attr pstr).
        2:{ intros w.
            rewrite interp_EBinop, interp_EAccess, interp_EVar, interp_EAtom.
            unfold get_local; rewrite map.get_put_same.
            unfold contains_test, row_key. cbn [interp_atom]. reflexivity. }
        rewrite (probe_recheck_eq attr key seps rows pstr H_len H_free H_nd), E_te.
        unfold probe_body. reflexivity.
      Qed.

      Lemma trigram_lookup_head_preserve_ty : forall tl ctl t (Gstore : tenv),
          type_wf t -> @IndexInterface.is_tbl_ty tridx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (@IndexInterface.idx_ty tridx t) ->
          access_record ctl pk_tag = Success (@IndexInterface.idx_ty uidx t) ->
          preserve_ty Gstore trigram_lookup_head.
      Proof.
        unfold preserve_ty.
        intros tl ctl t Gstore H_twf H_is E_tbl E_id E_aux E_tri E_pk.
        (* the table type's shape, forced by the index's own is_tbl_ty *)
        cbn [IndexInterface.is_tbl_ty IndexInterface.idx_ty trigram_idx
               unique_dict_idx] in H_is, E_tri, E_pk.
        unfold TrigramIndexImpl.is_tbl_ty, TrigramIndexImpl.idx_ty,
          UniqueDictIndexImpl.idx_ty in H_is, E_tri, E_pk.
        destruct t as [ | | | | | t1 | | | | ]; try discriminate.
        destruct t1 as [ | | | | | | rt | | | ]; try discriminate.
        destruct (access_record rt attr) as [ at_ty | ] eqn:E_attr;
          try discriminate.
        destruct (access_record rt key) as [ kt | ] eqn:E_key; try discriminate.
        apply type_eqb_eq in H_is; subst at_ty.
        (* so both dictionaries' types are known *)
        assert (E_kt : get_attr_type rt key = kt)
          by (unfold get_attr_type; rewrite E_key; reflexivity).
        rewrite E_kt in E_tri, E_pk.
        assert (H_rtwf : type_wf (TRecord rt)) by (inversion H_twf; assumption).
        assert (H_ktwf : type_wf kt)
          by (rewrite <- E_kt; apply get_attr_type_ty_wf; exact H_rtwf).
        (* E_kt orients as "term = kt", so a later subst would eliminate kt
           along with it; it has done its work here *)
        clear E_kt.
        (* now the rewrite's two sides *)
        intros e t' Genv H_Gs H_Ge H_t.
        repeat destruct_subexpr_keep_str.
        unfold trigram_lookup_head. cbv beta iota.
        case_match; auto.
        destruct (literal_trigram _) as [ g | ] eqn:E_lit; auto.
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        repeat (rewrite eqb_eq in *; subst).
        apply literal_trigram_Some in E_lit
          as [ pstr [ E_p [ H_len [ H_free E_g ] ] ] ].
        subst.
        (* the source's type is the set of rows, which the target also has *)
        repeat invert_type_of_clear; repeat invert_type_of_op_clear.
        repeat rewrite_map_get_put_hyp.
        repeat (clear_refl; repeat do_injection2).
        repeat (rewrite_l_to_r; do_injection2).
        unfold trigram_probe.
        eapply TyEFlatmap_Set with (t1 := kt).
        1:{ (* the bucket of the pattern's trigram *)
            eapply TyEOptMatch with (t1 := TSet kt).
            1:{ eapply TyEBinop; [ apply TyOLookup | | ].
                1:{ eapply TyEAccess;
                    [ eapply TyEAccess;
                      [ apply TyELoc; exact E_tbl | exact E_aux ]
                    | exact E_tri ]. }
                1: apply TyEAtom; apply TyAString. }
            1: apply TyEAtom; apply TyAEmptySet'; exact H_ktwf.
            1: apply TyEVar; rewrite map.get_put_same; reflexivity. }
        1:{ (* each key back to its row, then the recheck *)
            (* the row type is left to unification: the inversions above
               renamed it, and the primary-key dictionary's type pins it *)
            eapply TyEOptMatch.
            1:{ eapply TyEBinop; [ apply TyOLookup | | ].
                1:{ eapply TyEAccess;
                    [ eapply TyEAccess;
                      [ apply TyELoc; exact E_tbl | exact E_aux ]
                    | exact E_pk ]. }
                1: apply TyEVar; rewrite map.get_put_same; reflexivity. }
            1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf.
            1:{ eapply TyEIf.
                1:{ eapply TyEBinop; [ apply TyOStrContains | | ].
                    1:{ eapply TyEAccess;
                        [ apply TyEVar; rewrite map.get_put_same; reflexivity
                        | exact E_attr ]. }
                    1: apply TyEAtom; apply TyAString. }
                1:{ eapply TyEBinop; [ apply TyOSetInsert | | ].
                    1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf.
                    1: apply TyEVar; rewrite map.get_put_same; reflexivity. }
                1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf. } }
      Qed.

      (* ------------------------------------------------------------------
         The candidate set of a pattern known only at run time.

         A literal hands over its trigram list at rewrite time; a pattern
         that is a variable does not, so the chain of intersections becomes
         a FOLD over the pattern's own trigram positions.  Seeded with the
         first trigram's bucket, which is what makes the empty-narrowing
         case the single-bucket probe.
         ------------------------------------------------------------------ *)
      Definition tri_at (p pe : expr) : expr :=
        ETernop OSubstring p pe (EAtom (AInt 3)).

      (* 1, 2, ... |p| - 3: the positions AFTER the first, because the fold
         is seeded with the first trigram's bucket.  Starting at 0 instead
         would look the first bucket up twice and intersect it with itself,
         which costs a second probe and a whole set walk for nothing -- and
         for a pattern of exactly three characters, where there is only one
         trigram, that waste is the entire rewrite.  Starting at 1 makes the
         one-trigram case an EMPTY fold, so the rewritten term reduces to the
         single-bucket probe. *)
      Definition tri_positions (p : expr) : expr :=
        EBinop ORange (EAtom (AInt 1))
          (EBinop OMinus (EUnop OLengthString p) (EAtom (AInt 2))).

      Definition cands_body (p : expr) : expr :=
        EBinop OSetIntersect (EVar cacc) (tri_bucket_e (tri_at p (EVar cpos))).

      Definition dyn_cands (p : expr) : expr :=
        EFold (tri_positions p) (tri_bucket_e (tri_at p (EAtom (AInt 0))))
          cpos cacc (cands_body p).

      (* The trigram a position names, at the value level.  A position that
         is not an integer names nothing, on both sides. *)
      Definition tri_str (pv : string) (iv : value) : value :=
        match iv with
        | VInt i => VString (String.substring (Z.to_nat i) 3 pv)
        | _ => VUnit
        end.

      Definition cands_g (l : list value) (pv : string) (d : value)
        (sl : list value) : list value :=
        fold_right
          (fun iv a => filter (fun v => set_mem v (tri_bucket (tri_str pv iv) d)) a)
          sl l.

      (* Completeness of the fold: a key in the seed and in every position's
         bucket survives.  That is all the rule needs; soundness is the
         recheck's business. *)
      Lemma In_cands_g : forall l pv (d v : value) sl,
          In v sl ->
          (forall iv, In iv l -> In v (tri_bucket (tri_str pv iv) d)) ->
          In v (cands_g l pv d sl).
      Proof.
        unfold cands_g; induction l as [ | iv l IH ];
          intros pv d v sl H_sl H_all; cbn [fold_right].
        1: exact H_sl.
        apply filter_In; split.
        1:{ apply IH; [ exact H_sl | ].
            intros iv' H_in; apply H_all; right; exact H_in. }
        1: apply set_mem_true_iff, H_all; left; reflexivity.
      Qed.

      (* The inverse of In_eval_range: every element of a range really is
         an integer at a position below the length. *)
      Lemma In_eval_range_inv : forall n lo (iv : value),
          In iv (eval_range lo n) ->
          exists i, (i < n)%nat /\ iv = VInt (lo + Z.of_nat i).
      Proof.
        induction n as [ | n IH ]; intros lo iv H_in; cbn [eval_range] in H_in.
        1: contradiction.
        destruct H_in as [ E | H_in ].
        1: exists 0%nat; split; [ lia | subst; f_equal; lia ].
        1:{ destruct (IH (lo + 1)%Z iv H_in) as [ i [ H_lt E ] ].
            exists (S i); split; [ lia | subst; f_equal; lia ]. }
      Qed.

      (* One narrowing step of the fold. *)
      Lemma interp_cands_step :
        forall (store env : locals) (p : expr) (pv : string) (iv : value)
               (al : list value) (td : list (value * value)),
          interp_expr store env tri_e = VDict td ->
          Forall (fun e : value * value =>
                    match snd e with VSet _ => True | _ => False end) td ->
          interp_expr store (map.put (map.put env cpos iv) cacc (VSet al)) p
          = VString pv ->
          interp_expr store (map.put (map.put env cpos iv) cacc (VSet al))
            (cands_body p)
          = VSet (filter (fun v => set_mem v (tri_bucket (tri_str pv iv) (VDict td)))
                    al).
      Proof.
        intros store env p pv iv al td E_tri H_sets H_p.
        assert (H_tri' : interp_expr store
                           (map.put (map.put env cpos iv) cacc (VSet al)) tri_e
                         = VDict td).
        1:{ rewrite (interp_tbl_access_env_irrel store _ env aux_tag tri_tag).
            exact E_tri. }
        assert (H_g : interp_expr store
                        (map.put (map.put env cpos iv) cacc (VSet al))
                        (tri_at p (EVar cpos)) = tri_str pv iv).
        1:{ unfold tri_at. rewrite interp_ETernop, H_p, interp_EVar, interp_EAtom.
            unfold get_local.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same.
            destruct iv as [ i | | | | | | | | | ];
              cbn [interp_atom interp_ternop tri_str]; reflexivity. }
        unfold cands_body.
        rewrite interp_EBinop, interp_EVar.
        unfold get_local; rewrite map.get_put_same.
        rewrite (interp_tri_bucket_e store _ _ _ td H_g H_tri' H_sets).
        cbn [interp_binop]. reflexivity.
      Qed.

      (* And the whole fold.  The pattern must read the same under the
         fold's two binders, which the rule's guard checks syntactically. *)
      Lemma interp_cands_fold :
        forall (l : list value) (store env : locals) (p e1 seed : expr)
               (pv : string) (sl : list value) (td : list (value * value)),
          interp_expr store env e1 = VList l ->
          interp_expr store env seed = VSet sl ->
          interp_expr store env tri_e = VDict td ->
          Forall (fun e : value * value =>
                    match snd e with VSet _ => True | _ => False end) td ->
          (forall (iv a : value),
              interp_expr store (map.put (map.put env cpos iv) cacc a) p
              = VString pv) ->
          interp_expr store env (EFold e1 seed cpos cacc (cands_body p))
          = VSet (cands_g l pv (VDict td) sl).
      Proof.
        intros l store env p e1 seed pv sl td E_e1 E_seed E_tri H_sets H_p.
        rewrite interp_EFold, E_e1, E_seed.
        (* E_e1 mentions l, so the induction would carry it into the IH as a
           premise and the rewrite below would leave a side goal *)
        clear E_e1.
        unfold cands_g.
        induction l as [ | iv l IH ]; cbn [fold_right].
        1: reflexivity.
        rewrite IH.
        apply interp_cands_step; [ exact E_tri | exact H_sets | apply H_p ].
      Qed.

      (* ==================================================================
         The all-trigram rule.

         Same pattern as the single-trigram rule, same recheck, same
         fallback; the only change is that the candidate set is the
         intersection of the buckets of ALL the pattern's trigrams rather
         than one of them.  A literal pattern hands over its whole trigram
         list at rewrite time, so the chain is built statically and there is
         still no runtime guard.

         Note that no length test appears: trigrams is empty for a pattern
         shorter than three characters, so literal_trigrams returns None and
         the program is left alone.  The old rule needed `3 <= length p`
         spelled out; here the nonempty trigram list carries it.
         ================================================================== *)
      Definition literal_trigrams (e : expr) : option (string * list string) :=
        match e with
        | EAtom (AString s) =>
            if sep_free seps s
            then match trigrams s with
                 | nil => None
                 | g0 :: gs => Some (g0, gs)
                 end
            else None
        | _ => None
        end.

      Lemma literal_trigrams_Some : forall p g0 gs,
          literal_trigrams p = Some (g0, gs) ->
          exists s, p = EAtom (AString s)
                    /\ sep_free seps s = true
                    /\ trigrams s = g0 :: gs.
      Proof.
        unfold literal_trigrams; intros p g0 gs H.
        destruct p as [ | | a | | | | | | | | | | | | | ]; try discriminate.
        destruct a as [ | | str | | | | | | ]; try discriminate.
        destruct (sep_free seps str) eqn:E_free; [ | discriminate ].
        destruct (trigrams str) as [ | h t ] eqn:E_tri; [ discriminate | ].
        injection H as E1 E2; subst.
        exists str; split; [ reflexivity | split; [ exact E_free | exact E_tri ] ].
      Qed.

      (* [row <- set(tbl[id_tag]), check(contains(row.attr, p)), ret row]
         -->
         intersect the buckets of every trigram of p in tbl[aux_tag][tri_tag],
         resolve each surviving key through tbl[aux_tag][pk_tag], and recheck
         contains. *)
      Definition trigram_lookup_all_head (e : expr) : expr :=
        match e with
        | flatmap_filter_set
            (EUnop OSetOfList (EAccess (ELoc tbl0) id_tag0))
            x0 (EBinop OStrContains (EAccess (EVar x1) attr0) p) x2 _ _ =>
            if all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x0, [x1; x2]);
                        (id_tag, [id_tag0])]
            then match literal_trigrams p with
                 | Some (g0, gs) => trigram_probe_all g0 gs p
                 | None => e
                 end
            else e
        | _ => e
        end.

      (* Stated for any TString-typed trigram expression, so that a literal
         and a substring taken at run time use the same lemma. *)
      Lemma tri_bucket_e_ty : forall (Gstore Genv : tenv) tl ctl kt g,
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (TDict Unranged TString (TSet kt)) ->
          type_wf kt ->
          type_of Gstore Genv g TString ->
          type_of Gstore Genv (tri_bucket_e g) (TSet kt).
      Proof.
        intros * E_tbl E_aux E_tri H_ktwf H_g.
        unfold tri_bucket_e.
        eapply TyEOptMatch with (t1 := TSet kt).
        1:{ eapply TyEBinop; [ apply TyOLookup | | ].
            1:{ eapply TyEAccess;
                [ eapply TyEAccess; [ apply TyELoc; exact E_tbl | exact E_aux ]
                | exact E_tri ]. }
            1: exact H_g. }
        1: apply TyEAtom; apply TyAEmptySet'; exact H_ktwf.
        1: apply TyEVar; rewrite map.get_put_same; reflexivity.
      Qed.

      Lemma tri_cands_from_ty : forall gs (Gstore Genv : tenv) tl ctl kt cnd,
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (TDict Unranged TString (TSet kt)) ->
          type_wf kt ->
          type_of Gstore Genv cnd (TSet kt) ->
          type_of Gstore Genv (tri_cands_from cnd gs) (TSet kt).
      Proof.
        induction gs as [ | g gs IH ]; intros * E_tbl E_aux E_tri H_ktwf H_cnd.
        1: exact H_cnd.
        cbn [tri_cands_from fold_left].
        eapply IH; try eassumption.
        unfold tri_cands_step.
        eapply TyEBinop; [ apply TyOSetIntersect | exact H_cnd | ].
        eapply tri_bucket_e_ty; try eassumption.
        apply TyEAtom; apply TyAString.
      Qed.

      Lemma trigram_lookup_all_head_preserve_ty : forall tl ctl t (Gstore : tenv),
          type_wf t -> @IndexInterface.is_tbl_ty tridx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (@IndexInterface.idx_ty tridx t) ->
          access_record ctl pk_tag = Success (@IndexInterface.idx_ty uidx t) ->
          preserve_ty Gstore trigram_lookup_all_head.
      Proof.
        unfold preserve_ty.
        intros tl ctl t Gstore H_twf H_is E_tbl E_id E_aux E_tri E_pk.
        cbn [IndexInterface.is_tbl_ty IndexInterface.idx_ty trigram_idx
               unique_dict_idx] in H_is, E_tri, E_pk.
        unfold TrigramIndexImpl.is_tbl_ty, TrigramIndexImpl.idx_ty,
          UniqueDictIndexImpl.idx_ty in H_is, E_tri, E_pk.
        destruct t as [ | | | | | t1 | | | | ]; try discriminate.
        destruct t1 as [ | | | | | | rt | | | ]; try discriminate.
        destruct (access_record rt attr) as [ at_ty | ] eqn:E_attr;
          try discriminate.
        destruct (access_record rt key) as [ kt | ] eqn:E_key; try discriminate.
        apply type_eqb_eq in H_is; subst at_ty.
        assert (E_kt : get_attr_type rt key = kt)
          by (unfold get_attr_type; rewrite E_key; reflexivity).
        rewrite E_kt in E_tri, E_pk.
        assert (H_rtwf : type_wf (TRecord rt)) by (inversion H_twf; assumption).
        assert (H_ktwf : type_wf kt)
          by (rewrite <- E_kt; apply get_attr_type_ty_wf; exact H_rtwf).
        clear E_kt.
        intros e t' Genv H_Gs H_Ge H_t.
        repeat destruct_subexpr_keep_str.
        unfold trigram_lookup_all_head. cbv beta iota.
        case_match; auto.
        destruct (literal_trigrams _) as [ [ g0 gs ] | ] eqn:E_lit; auto.
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        repeat (rewrite eqb_eq in *; subst).
        apply literal_trigrams_Some in E_lit as [ pstr [ E_p [ H_free E_tris ] ] ].
        subst.
        repeat invert_type_of_clear; repeat invert_type_of_op_clear.
        repeat rewrite_map_get_put_hyp.
        repeat (clear_refl; repeat do_injection2).
        repeat (rewrite_l_to_r; do_injection2).
        unfold trigram_probe_all, probe_from.
        eapply TyEFlatmap_Set with (t1 := kt).
        1:{ (* the candidate set: the first bucket, narrowed by the rest *)
            eapply tri_cands_from_ty;
              [ exact E_tbl | exact E_aux | exact E_tri | exact H_ktwf | ].
            eapply tri_bucket_e_ty;
              [ exact E_tbl | exact E_aux | exact E_tri | exact H_ktwf | ].
            apply TyEAtom; apply TyAString. }
        1:{ (* each surviving key back to its row, then the recheck *)
            eapply TyEOptMatch.
            1:{ eapply TyEBinop; [ apply TyOLookup | | ].
                1:{ eapply TyEAccess;
                    [ eapply TyEAccess;
                      [ apply TyELoc; exact E_tbl | exact E_aux ]
                    | exact E_pk ]. }
                1: apply TyEVar; rewrite map.get_put_same; reflexivity. }
            1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf.
            1:{ eapply TyEIf.
                1:{ eapply TyEBinop; [ apply TyOStrContains | | ].
                    1:{ eapply TyEAccess;
                        [ apply TyEVar; rewrite map.get_put_same; reflexivity
                        | exact E_attr ]. }
                    1: apply TyEAtom; apply TyAString. }
                1:{ eapply TyEBinop; [ apply TyOSetInsert | | ].
                    1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf.
                    1: apply TyEVar; rewrite map.get_put_same; reflexivity. }
                1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf. } }
      Qed.

      Lemma trigram_lookup_all_head_preserve_sem :
        forall tl rt (Gstore : tenv) (store : locals),
          access_record rt attr = Success TString ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          match map.get store tbl with
          | Some v =>
              type_of_value v (TRecord tl) /\ tri_aux_wf_at v /\ unique_aux_wf_at v
          | _ => False
          end ->
          preserve_sem Gstore store trigram_lookup_all_head.
      Proof.
        unfold preserve_sem; intros * H_attr E_tbl E_id H_store.
        intros e t Genv env H_Gs H_Ge H_t H_sw H_ew.
        destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
        destruct H_store as [ H_vty [ H_tri H_pk ] ].
        destruct (invariants__probe_data tl rt v H_attr E_id H_vty H_tri H_pk)
          as [ rv [ rv_aux [ rows [ td [ E_vrec [ E_rows [ E_aux
             [ E_tri [ E_pk [ E_te [ H_sets H_nd ] ] ] ] ] ] ] ] ] ] ].
        subst v.
        repeat destruct_subexpr_keep_str.
        unfold trigram_lookup_all_head. cbv beta iota.
        case_match; auto.
        destruct (literal_trigrams _) as [ [ g0 gs ] | ] eqn:E_lit; auto.
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        repeat (rewrite eqb_eq in *; subst).
        apply literal_trigrams_Some in E_lit as [ pstr [ E_p [ H_free E_tris ] ] ].
        subst.
        assert (H_tri_e : interp_expr store env
                            (EAccess (EAccess (ELoc tbl) aux_tag) tri_tag) = VDict td)
          by (eapply interp_tbl_field; [ exact E_v | exact E_aux | exact E_tri ]).
        assert (H_pk_e : interp_expr store env
                           (EAccess (EAccess (ELoc tbl) aux_tag) pk_tag)
                         = VDict (UniqueDictIndexImpl.idx_entries key rows))
          by (eapply interp_tbl_field; [ exact E_v | exact E_aux | exact E_pk ]).
        assert (H_pv : forall (v r : value),
                   interp_expr store (map.put (map.put env k v) y r)
                     (EAtom (AString pstr)) = VString pstr) by reflexivity.
        (* the candidate set is the intersection of every bucket *)
        assert (H_cand : interp_expr store env
                  (tri_cands_from (tri_bucket_e (EAtom (AString g0))) gs)
                = VSet (tri_inter (tri_bucket (VString g0) (VDict td)) gs (VDict td))).
        1:{ eapply interp_tri_cands_from; [ exact H_tri_e | exact H_sets | ].
            eapply interp_tri_bucket_e;
              [ reflexivity | exact H_tri_e | exact H_sets ]. }
        (* the trigrams the rule probed really are the pattern's *)
        assert (H_g0in : In g0 (trigrams pstr))
          by (rewrite E_tris; left; reflexivity).
        assert (H_gsin : forall g, In g gs -> In g (trigrams pstr))
          by (intros g H_g; rewrite E_tris; right; exact H_g).
        unfold trigram_probe_all.
        rewrite (interp_probe_from store env _ _ _ pstr _ H_cand H_pv H_pk_e).
        (* the scan side *)
        rewrite interp_flatmap_filter_set, interp_ESetOf,
          interp_EAccess, interp_ELoc.
        unfold get_local; rewrite E_v; cbv beta iota.
        rewrite E_rows; cbv beta iota.
        erewrite filter_pointwise with (f2 := contains_test attr pstr).
        2:{ intros w.
            rewrite interp_EBinop, interp_EAccess, interp_EVar, interp_EAtom.
            unfold get_local; rewrite map.get_put_same.
            unfold contains_test, row_key. cbn [interp_atom]. reflexivity. }
        rewrite (probe_recheck_all_eq attr key seps rows pstr g0 gs
                   H_g0in H_free H_gsin H_nd), E_te.
        unfold probe_body. reflexivity.
      Qed.

      (* ------------------------------------------------------------------
         The guarded form, for a pattern that is not a literal.

         Whether the pattern has a trigram at all cannot be decided at
         rewrite time, so the rule decides it at run time and keeps the
         original scan for the short case.  The length condition is a
         soundness obligation, not a heuristic: probe_recheck_eq does not
         hold without it, so the fallback cannot be dropped.
         ------------------------------------------------------------------ *)
      (* The runtime guard, in two halves, both necessary.  The pattern
         must have a trigram at all, and it must hold no separator: the
         index keys on WORDS, so a pattern straddling one is in no bucket
         and probing for it would lose rows.

         The second half cannot be evaluated here, since the pattern is not
         known until run time, so it is EMITTED as a comparison: a string
         is separator-free exactly when splitting it hands back the
         one-element list holding it (StringFacts.words_singleton__sep_free),
         and both sides of that are ordinary expressions.  The literal
         forms above decide the same condition at rewrite time. *)
      Definition pattern_is_word (p : expr) : expr :=
        EBinop OEq (EBinop OWords (EAtom (AString seps)) p)
          (EBinop OCons p (EAtom (ANil (Some TString)))).

      Definition pattern_has_trigram (p : expr) : expr :=
        EBinop OAnd
          (EBinop OLess (EAtom (AInt 2)) (EUnop OLengthString p))
          (pattern_is_word p).

      (* and what the emitted comparison tells the proof *)
      Lemma guard_word__sep_free : forall (pv : string),
          value_eqb (VList (List.map VString (words seps pv)))
            (VList [VString pv]) = true ->
          sep_free seps pv = true.
      Proof.
        intros pv H. apply value_eqb_eq in H. injection H as H.
        apply words_singleton__sep_free.
        destruct (words seps pv) as [ | w ws ]; [ discriminate | ].
        cbn [List.map] in H. injection H as E_w E_ws.
        destruct ws as [ | w2 ws ]; [ | cbn [List.map] in E_ws; discriminate ].
        subst w; reflexivity.
      Qed.

      Definition first_trigram (p : expr) : expr :=
        ETernop OSubstring p (EAtom (AInt 0)) (EAtom (AInt 3)).

      Definition trigram_lookup_guarded_head (e : expr) : expr :=
        match e with
        | flatmap_filter_set
            (EUnop OSetOfList (EAccess (ELoc tbl0) id_tag0))
            x0 (EBinop OStrContains (EAccess (EVar x1) attr0) p) x2 _ _ =>
            if (all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x0, [x1; x2]);
                         (id_tag, [id_tag0])]
                && negb (free_immut_in x0 p)
                && negb (free_immut_in k p)
                && negb (free_immut_in y p))%bool
            then EIf (pattern_has_trigram p) (trigram_probe (first_trigram p) p) e
            else e
        | _ => e
        end.

      Lemma trigram_lookup_guarded_head_preserve_ty : forall tl ctl t (Gstore : tenv),
          type_wf t -> @IndexInterface.is_tbl_ty tridx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (@IndexInterface.idx_ty tridx t) ->
          access_record ctl pk_tag = Success (@IndexInterface.idx_ty uidx t) ->
          preserve_ty Gstore trigram_lookup_guarded_head.
      Proof.
        unfold preserve_ty.
        intros tl ctl t Gstore H_twf H_is E_tbl E_id E_aux E_tri E_pk.
        cbn [IndexInterface.is_tbl_ty IndexInterface.idx_ty trigram_idx
               unique_dict_idx] in H_is, E_tri, E_pk.
        unfold TrigramIndexImpl.is_tbl_ty, TrigramIndexImpl.idx_ty,
          UniqueDictIndexImpl.idx_ty in H_is, E_tri, E_pk.
        destruct t as [ | | | | | t1 | | | | ]; try discriminate.
        destruct t1 as [ | | | | | | rt | | | ]; try discriminate.
        destruct (access_record rt attr) as [ at_ty | ] eqn:E_attr;
          try discriminate.
        destruct (access_record rt key) as [ kt | ] eqn:E_key; try discriminate.
        apply type_eqb_eq in H_is; subst at_ty.
        assert (E_kt : get_attr_type rt key = kt)
          by (unfold get_attr_type; rewrite E_key; reflexivity).
        rewrite E_kt in E_tri, E_pk.
        assert (H_rtwf : type_wf (TRecord rt)) by (inversion H_twf; assumption).
        assert (H_ktwf : type_wf kt)
          by (rewrite <- E_kt; apply get_attr_type_ty_wf; exact H_rtwf).
        clear E_kt.
        intros e t' Genv H_Gs H_Ge H_t.
        repeat destruct_subexpr_keep_str.
        unfold trigram_lookup_guarded_head. cbv beta iota.
        case_match; auto.
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        repeat rewrite Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        (* destruct_subexpr stops at the pattern, which is the only
           expression variable left: give it a name to use below *)
        lazymatch goal with pe : expr |- _ => rename pe into pat end.
        (* the pattern's type, read off the source by inversions that are
           kept local so the source's own typing survives for the else
           branch below *)
        assert (H_pty : type_of Gstore Genv pat TString).
        1:{ repeat invert_type_of_clear; repeat invert_type_of_op_clear.
            eapply not_free_immut_put_ty; [ eassumption | eassumption ]. }
        unfold pattern_has_trigram, first_trigram, trigram_probe.
        eapply TyEIf.
        3: exact H_t.
        1:{ (* the guard: a trigram's worth of characters, and one word *)
            unfold pattern_is_word.
            eapply TyEBinop; [ apply TyOAnd | | ].
            1:{ eapply TyEBinop;
                [ apply TyOLess | apply TyEAtom; apply TyAInt | ].
                eapply TyEUnop; [ apply TyOLengthString | exact H_pty ]. }
            1:{ eapply TyEBinop; [ apply TyOEq | | ].
                1:{ eapply TyEBinop;
                    [ apply TyOWords | apply TyEAtom; apply TyAString
                    | exact H_pty ]. }
                1:{ eapply TyEBinop; [ apply TyOCons | exact H_pty | ].
                    apply TyEAtom; apply TyANil; constructor. } } }
        1:{ repeat invert_type_of_clear; repeat invert_type_of_op_clear.
            repeat rewrite_map_get_put_hyp.
            repeat (clear_refl; repeat do_injection2).
            repeat (rewrite_l_to_r; do_injection2).
            eapply TyEFlatmap_Set with (t1 := kt).
            1:{ eapply TyEOptMatch with (t1 := TSet kt).
                1:{ eapply TyEBinop; [ apply TyOLookup | | ].
                    1:{ eapply TyEAccess;
                        [ eapply TyEAccess;
                          [ apply TyELoc; exact E_tbl | exact E_aux ]
                        | exact E_tri ]. }
                    1:{ eapply TyETernop;
                        [ apply TyOSubstring | exact H_pty
                        | apply TyEAtom; apply TyAInt
                        | apply TyEAtom; apply TyAInt ]. } }
                1: apply TyEAtom; apply TyAEmptySet'; exact H_ktwf.
                1: apply TyEVar; rewrite map.get_put_same; reflexivity. }
            1:{ eapply TyEOptMatch.
                1:{ eapply TyEBinop; [ apply TyOLookup | | ].
                    1:{ eapply TyEAccess;
                        [ eapply TyEAccess;
                          [ apply TyELoc; exact E_tbl | exact E_aux ]
                        | exact E_pk ]. }
                    1: apply TyEVar; rewrite map.get_put_same; reflexivity. }
                1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf.
                1:{ eapply TyEIf.
                    1:{ eapply TyEBinop; [ apply TyOStrContains | | ].
                        1:{ eapply TyEAccess;
                            [ apply TyEVar; rewrite map.get_put_same; reflexivity
                            | exact E_attr ]. }
                        1:{ apply not_free_immut_put_ty2; [ assumption | ].
                            apply not_free_immut_put_ty2;
                              [ assumption | exact H_pty ]. } }
                    1:{ eapply TyEBinop; [ apply TyOSetInsert | | ].
                        1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf.
                        1: apply TyEVar; rewrite map.get_put_same; reflexivity. }
                    1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf. } } }
      Qed.

      (* --- *)
      Lemma trigram_lookup_guarded_head_preserve_sem :
        forall tl rt (Gstore : tenv) (store : locals),
          access_record rt attr = Success TString ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          match map.get store tbl with
          | Some v =>
              type_of_value v (TRecord tl) /\ tri_aux_wf_at v /\ unique_aux_wf_at v
          | _ => False
          end ->
          preserve_sem Gstore store trigram_lookup_guarded_head.
      Proof.
        unfold preserve_sem; intros * H_attr E_tbl E_id H_store.
        intros e t Genv env H_Gs H_Ge H_t H_sw H_ew.
        destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
        destruct H_store as [ H_vty [ H_tri H_pk ] ].
        destruct (invariants__probe_data tl rt v H_attr E_id H_vty H_tri H_pk)
          as [ rv [ rv_aux [ rows [ td [ E_vrec [ E_rows [ E_aux
             [ E_tri [ E_pk [ E_te [ H_sets H_nd ] ] ] ] ] ] ] ] ] ] ].
        subst v.
        repeat destruct_subexpr_keep_str.
        unfold trigram_lookup_guarded_head. cbv beta iota.
        case_match; auto.
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        repeat rewrite Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        (* destruct_subexpr stops at the pattern, which is the only
           expression variable left: give it a name to use below *)
        lazymatch goal with pe : expr |- _ => rename pe into pat end.
        (* the pattern is a string, so the guard really is a boolean *)
        assert (H_pty : type_of Gstore Genv pat TString).
        1:{ repeat invert_type_of_clear; repeat invert_type_of_op_clear.
            eapply not_free_immut_put_ty; [ eassumption | eassumption ]. }
        pose proof (type_sound Gstore Genv pat TString H_pty H_Gs H_Ge
                      store env H_sw H_ew) as H_pval.
        assert (H_pstr : exists pv, interp_expr store env pat = VString pv).
        1:{ destruct (interp_expr store env pat)
              as [ | | pv | | | | | | | ] eqn:E_pv.
            3: exists pv; reflexivity.
            all: inversion H_pval. }
        destruct H_pstr as [ pv E_pv ].
        (* the guard *)
        unfold pattern_has_trigram, pattern_is_word, first_trigram.
        rewrite interp_EIf, !interp_EBinop, interp_EUnop, !interp_EAtom, E_pv.
        cbn [interp_unop interp_binop interp_atom apply_bool_binop].
        destruct (Z.ltb 2 (Z.of_nat (String.length pv))) eqn:E_long;
          cbn [andb].
        2: reflexivity.
        destruct (value_eqb (VList (List.map VString (words seps pv)))
                    (VList [VString pv])) eqn:E_word.
        2: reflexivity.
        pose proof (guard_word__sep_free pv E_word) as H_free.
        assert (H_len : 3 <= String.length pv)
          by (apply Z.ltb_lt in E_long; lia).
        (* the probe, as in the literal case, with the trigram taken at run
           time instead of at rewrite time *)
        assert (H_g : interp_expr store env
                        (ETernop OSubstring pat (EAtom (AInt 0)) (EAtom (AInt 3)))
                      = VString (String.substring 0 3 pv)).
        1:{ rewrite interp_ETernop, E_pv.
            cbn [interp_expr interp_atom interp_ternop]. reflexivity. }
        assert (H_pv' : forall (v r : value),
                   interp_expr store (map.put (map.put env k v) y r) pat
                   = VString pv).
        1:{ intros v r.
            rewrite <- (not_free_immut_put_sem pat y store (map.put env k v) r)
              by assumption.
            rewrite <- (not_free_immut_put_sem pat k store env v) by assumption.
            exact E_pv. }
        assert (H_tri_e : interp_expr store env
                            (EAccess (EAccess (ELoc tbl) aux_tag) tri_tag) = VDict td)
          by (eapply interp_tbl_field; [ exact E_v | exact E_aux | exact E_tri ]).
        assert (H_pk_e : interp_expr store env
                           (EAccess (EAccess (ELoc tbl) aux_tag) pk_tag)
                         = VDict (UniqueDictIndexImpl.idx_entries key rows))
          by (eapply interp_tbl_field; [ exact E_v | exact E_aux | exact E_pk ]).
        rewrite (interp_trigram_probe store env _ _ _ pv td _
                   H_g H_pv' H_tri_e H_pk_e H_sets).
        rewrite interp_flatmap_filter_set, interp_ESetOf,
          interp_EAccess, interp_ELoc.
        unfold get_local; rewrite E_v; cbv beta iota.
        rewrite E_rows; cbv beta iota.
        erewrite filter_pointwise with (f2 := contains_test attr pv).
        2:{ intros w.
            rewrite interp_EBinop, interp_EAccess, interp_EVar.
            unfold get_local; rewrite map.get_put_same.
            rewrite <- (not_free_immut_put_sem pat x store env w) by assumption.
            rewrite E_pv.
            unfold contains_test, row_key. reflexivity. }
        rewrite (probe_recheck_eq attr key seps rows pv H_len H_free H_nd), E_te.
        unfold probe_body. reflexivity.
      Qed.

      (* ==================================================================
         The all-trigram rule, guarded.

         This is the one the pipeline installs: the pattern is a variable,
         so its trigrams are not known until run time and the chain of
         intersections is a fold over its own positions.  Everything else is
         the guarded rule above -- same shape, same runtime length test,
         same fallback to the scan, same recheck.

         The extra two freshness conditions are for the fold's binders: the
         pattern is read under them, so it must not mention them.
         ================================================================== *)
      Definition trigram_lookup_all_guarded_head (e : expr) : expr :=
        match e with
        | flatmap_filter_set
            (EUnop OSetOfList (EAccess (ELoc tbl0) id_tag0))
            x0 (EBinop OStrContains (EAccess (EVar x1) attr0) p) x2 _ _ =>
            if (all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x0, [x1; x2]);
                         (id_tag, [id_tag0])]
                && negb (free_immut_in x0 p)
                && negb (free_immut_in k p)
                && negb (free_immut_in y p)
                && negb (free_immut_in cpos p)
                && negb (free_immut_in cacc p))%bool
            then EIf (pattern_has_trigram p) (probe_from (dyn_cands p) p) e
            else e
        | _ => e
        end.

      Lemma dyn_cands_ty : forall (Gstore Genv : tenv) tl ctl kt p,
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (TDict Unranged TString (TSet kt)) ->
          type_wf kt ->
          free_immut_in cpos p = false ->
          free_immut_in cacc p = false ->
          type_of Gstore Genv p TString ->
          type_of Gstore Genv (dyn_cands p) (TSet kt).
      Proof.
        intros * E_tbl E_aux E_tri H_ktwf H_cpos H_cacc H_p.
        unfold dyn_cands.
        eapply TyEFold with (t1 := TInt).
        1:{ (* the pattern's trigram positions *)
            unfold tri_positions.
            eapply TyEBinop; [ apply TyORange | apply TyEAtom; apply TyAInt | ].
            eapply TyEBinop; [ apply TyOMinus | | apply TyEAtom; apply TyAInt ].
            eapply TyEUnop; [ apply TyOLengthString | exact H_p ]. }
        1:{ (* the seed: the first trigram's bucket *)
            eapply tri_bucket_e_ty;
              [ exact E_tbl | exact E_aux | exact E_tri | exact H_ktwf | ].
            unfold tri_at.
            eapply TyETernop; [ apply TyOSubstring | exact H_p
                              | apply TyEAtom; apply TyAInt
                              | apply TyEAtom; apply TyAInt ]. }
        1:{ (* one narrowing step *)
            unfold cands_body.
            eapply TyEBinop; [ apply TyOSetIntersect | | ].
            1: apply TyEVar; rewrite map.get_put_same; reflexivity.
            1:{ eapply tri_bucket_e_ty;
                  [ exact E_tbl | exact E_aux | exact E_tri | exact H_ktwf | ].
                unfold tri_at.
                eapply TyETernop; [ apply TyOSubstring | | | ].
                1:{ apply not_free_immut_put_ty2; [ exact H_cacc | ].
                    apply not_free_immut_put_ty2; [ exact H_cpos | exact H_p ]. }
                1:{ apply TyEVar. rewrite map.get_put_diff by congruence.
                    rewrite map.get_put_same; reflexivity. }
                1: apply TyEAtom; apply TyAInt. } }
      Qed.

      Lemma trigram_lookup_all_guarded_head_preserve_ty :
        forall tl ctl t (Gstore : tenv),
          type_wf t -> @IndexInterface.is_tbl_ty tridx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (@IndexInterface.idx_ty tridx t) ->
          access_record ctl pk_tag = Success (@IndexInterface.idx_ty uidx t) ->
          preserve_ty Gstore trigram_lookup_all_guarded_head.
      Proof.
        unfold preserve_ty.
        intros tl ctl t Gstore H_twf H_is E_tbl E_id E_aux E_tri E_pk.
        cbn [IndexInterface.is_tbl_ty IndexInterface.idx_ty trigram_idx
               unique_dict_idx] in H_is, E_tri, E_pk.
        unfold TrigramIndexImpl.is_tbl_ty, TrigramIndexImpl.idx_ty,
          UniqueDictIndexImpl.idx_ty in H_is, E_tri, E_pk.
        destruct t as [ | | | | | t1 | | | | ]; try discriminate.
        destruct t1 as [ | | | | | | rt | | | ]; try discriminate.
        destruct (access_record rt attr) as [ at_ty | ] eqn:E_attr;
          try discriminate.
        destruct (access_record rt key) as [ kt | ] eqn:E_key; try discriminate.
        apply type_eqb_eq in H_is; subst at_ty.
        assert (E_kt : get_attr_type rt key = kt)
          by (unfold get_attr_type; rewrite E_key; reflexivity).
        rewrite E_kt in E_tri, E_pk.
        assert (H_rtwf : type_wf (TRecord rt)) by (inversion H_twf; assumption).
        assert (H_ktwf : type_wf kt)
          by (rewrite <- E_kt; apply get_attr_type_ty_wf; exact H_rtwf).
        clear E_kt.
        intros e t' Genv H_Gs H_Ge H_t.
        repeat destruct_subexpr_keep_str.
        unfold trigram_lookup_all_guarded_head. cbv beta iota.
        case_match; auto.
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        repeat rewrite Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        lazymatch goal with pe : expr |- _ => rename pe into pat end.
        (* the pattern is a string, read off the source's own typing *)
        assert (H_pty : type_of Gstore Genv pat TString).
        1:{ repeat invert_type_of_clear; repeat invert_type_of_op_clear.
            eapply not_free_immut_put_ty; [ eassumption | eassumption ]. }
        eapply TyEIf.
        1:{ unfold pattern_has_trigram, pattern_is_word.
            eapply TyEBinop; [ apply TyOAnd | | ].
            1:{ eapply TyEBinop;
                [ apply TyOLess | apply TyEAtom; apply TyAInt | ].
                eapply TyEUnop; [ apply TyOLengthString | exact H_pty ]. }
            1:{ eapply TyEBinop; [ apply TyOEq | | ].
                1:{ eapply TyEBinop;
                    [ apply TyOWords | apply TyEAtom; apply TyAString
                    | exact H_pty ]. }
                1:{ eapply TyEBinop; [ apply TyOCons | exact H_pty | ].
                    apply TyEAtom; apply TyANil; constructor. } } }
        2: exact H_t.
        (* the probe's own type is the set of rows, which the source has *)
        repeat invert_type_of_clear; repeat invert_type_of_op_clear.
        repeat rewrite_map_get_put_hyp.
        repeat (clear_refl; repeat do_injection2).
        repeat (rewrite_l_to_r; do_injection2).
        unfold probe_from.
        eapply TyEFlatmap_Set with (t1 := kt).
        1:{ eapply dyn_cands_ty;
              [ exact E_tbl | exact E_aux | exact E_tri | exact H_ktwf
              | assumption | assumption | exact H_pty ]. }
        1:{ eapply TyEOptMatch.
            1:{ eapply TyEBinop; [ apply TyOLookup | | ].
                1:{ eapply TyEAccess;
                    [ eapply TyEAccess;
                      [ apply TyELoc; exact E_tbl | exact E_aux ]
                    | exact E_pk ]. }
                1: apply TyEVar; rewrite map.get_put_same; reflexivity. }
            1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf.
            1:{ eapply TyEIf.
                1:{ eapply TyEBinop; [ apply TyOStrContains | | ].
                    1:{ eapply TyEAccess;
                        [ apply TyEVar; rewrite map.get_put_same; reflexivity
                        | exact E_attr ]. }
                    1:{ apply not_free_immut_put_ty2; [ assumption | ].
                        apply not_free_immut_put_ty2; [ assumption | exact H_pty ]. } }
                1:{ eapply TyEBinop; [ apply TyOSetInsert | | ].
                    1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf.
                    1: apply TyEVar; rewrite map.get_put_same; reflexivity. }
                1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf. } }
      Qed.

      Lemma trigram_lookup_all_guarded_head_preserve_sem :
        forall tl rt (Gstore : tenv) (store : locals),
          access_record rt attr = Success TString ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          match map.get store tbl with
          | Some v =>
              type_of_value v (TRecord tl) /\ tri_aux_wf_at v /\ unique_aux_wf_at v
          | _ => False
          end ->
          preserve_sem Gstore store trigram_lookup_all_guarded_head.
      Proof.
        unfold preserve_sem; intros * H_attr E_tbl E_id H_store.
        intros e t Genv env H_Gs H_Ge H_t H_sw H_ew.
        destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
        destruct H_store as [ H_vty [ H_tri H_pk ] ].
        destruct (invariants__probe_data tl rt v H_attr E_id H_vty H_tri H_pk)
          as [ rv [ rv_aux [ rows [ td [ E_vrec [ E_rows [ E_aux
             [ E_tri [ E_pk [ E_te [ H_sets H_nd ] ] ] ] ] ] ] ] ] ] ].
        subst v.
        repeat destruct_subexpr_keep_str.
        unfold trigram_lookup_all_guarded_head. cbv beta iota.
        case_match; auto.
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        repeat rewrite Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        lazymatch goal with pe : expr |- _ => rename pe into pat end.
        assert (H_pty : type_of Gstore Genv pat TString).
        1:{ repeat invert_type_of_clear; repeat invert_type_of_op_clear.
            eapply not_free_immut_put_ty; [ eassumption | eassumption ]. }
        pose proof (type_sound Gstore Genv pat TString H_pty H_Gs H_Ge
                      store env H_sw H_ew) as H_pval.
        assert (H_pstr : exists pv, interp_expr store env pat = VString pv).
        1:{ destruct (interp_expr store env pat)
              as [ | | pv | | | | | | | ] eqn:E_pv.
            3: exists pv; reflexivity.
            all: inversion H_pval. }
        destruct H_pstr as [ pv E_pv ].
        (* the runtime guard *)
        unfold pattern_has_trigram, pattern_is_word.
        rewrite interp_EIf, !interp_EBinop, interp_EUnop, !interp_EAtom, E_pv.
        cbn [interp_unop interp_binop interp_atom apply_bool_binop].
        destruct (Z.ltb 2 (Z.of_nat (String.length pv))) eqn:E_long;
          cbn [andb].
        2: reflexivity.
        destruct (value_eqb (VList (List.map VString (words seps pv)))
                    (VList [VString pv])) eqn:E_word.
        2: reflexivity.
        pose proof (guard_word__sep_free pv E_word) as H_free.
        assert (H_len : 3 <= String.length pv)
          by (apply Z.ltb_lt in E_long; lia).
        (* the pattern reads the same under every binder the probe adds *)
        assert (H_pv' : forall (v r : value),
                   interp_expr store (map.put (map.put env k v) y r) pat
                   = VString pv).
        1:{ intros v r.
            rewrite <- (not_free_immut_put_sem pat y store (map.put env k v) r)
              by assumption.
            rewrite <- (not_free_immut_put_sem pat k store env v) by assumption.
            exact E_pv. }
        assert (H_pv_c : forall (iv a : value),
                   interp_expr store (map.put (map.put env cpos iv) cacc a) pat
                   = VString pv).
        1:{ intros iv a.
            rewrite <- (not_free_immut_put_sem pat cacc store
                          (map.put env cpos iv) a) by assumption.
            rewrite <- (not_free_immut_put_sem pat cpos store env iv)
              by assumption.
            exact E_pv. }
        assert (H_tri_e : interp_expr store env
                            (EAccess (EAccess (ELoc tbl) aux_tag) tri_tag) = VDict td)
          by (eapply interp_tbl_field; [ exact E_v | exact E_aux | exact E_tri ]).
        assert (H_pk_e : interp_expr store env
                           (EAccess (EAccess (ELoc tbl) aux_tag) pk_tag)
                         = VDict (UniqueDictIndexImpl.idx_entries key rows))
          by (eapply interp_tbl_field; [ exact E_v | exact E_aux | exact E_pk ]).
        (* the seed: the bucket of the pattern's first trigram *)
        assert (H_seed : interp_expr store env
                           (tri_bucket_e (tri_at pat (EAtom (AInt 0))))
                         = VSet (tri_bucket (VString (String.substring 0 3 pv))
                                   (VDict td))).
        1:{ eapply interp_tri_bucket_e; [ | exact H_tri_e | exact H_sets ].
            unfold tri_at. rewrite interp_ETernop, E_pv.
            cbn [interp_expr interp_atom interp_ternop]. reflexivity. }
        (* the positions the fold runs over *)
        assert (H_pos : interp_expr store env (tri_positions pat)
                        = VList (eval_range 1
                                   (Z.to_nat (Z.of_nat (String.length pv) - 2 - 1)))).
        1:{ unfold tri_positions.
            rewrite interp_EBinop, interp_EBinop, interp_EUnop, E_pv, !interp_EAtom.
            cbn [interp_unop interp_binop interp_atom]. reflexivity. }
        (* so the candidate set is the intersection of every bucket *)
        unfold dyn_cands.
        rewrite (interp_probe_from store env _ _ _ pv _
                   (interp_cands_fold _ store env pat _ _ pv _ td
                      H_pos H_seed H_tri_e H_sets H_pv_c)
                   H_pv' H_pk_e).
        (* the scan side *)
        rewrite interp_flatmap_filter_set, interp_ESetOf,
          interp_EAccess, interp_ELoc.
        unfold get_local; rewrite E_v; cbv beta iota.
        rewrite E_rows; cbv beta iota.
        erewrite filter_pointwise with (f2 := contains_test attr pv).
        2:{ intros w.
            rewrite interp_EBinop, interp_EAccess, interp_EVar.
            unfold get_local; rewrite map.get_put_same.
            rewrite <- (not_free_immut_put_sem pat x store env w) by assumption.
            rewrite E_pv.
            unfold contains_test, row_key. reflexivity. }
        (* completeness: a row that contains the pattern survives the seed
           and every narrowing step *)
        assert (H_compl : forall (r : value),
                   In r rows -> contains_test attr pv r = true ->
                   In (row_key key r)
                     (cands_g
                        (eval_range 1
                           (Z.to_nat (Z.of_nat (String.length pv) - 2 - 1)))
                        pv (VDict td)
                        (tri_bucket (VString (String.substring 0 3 pv))
                           (VDict td)))).
        1:{ intros r H_in H_p. apply In_cands_g.
            1:{ apply key_at__In_tri_bucket. rewrite <- E_te.
                apply (TrigramIndexImpl.tri_lookup_complete attr key seps);
                  [ exact H_in | exact H_free | exact H_len
                  | apply contains_test_true__occurrence; exact H_p ]. }
            1:{ intros iv H_iv.
                apply In_eval_range_inv in H_iv as [ i [ H_lt E_iv ] ]; subst iv.
                cbn [tri_str].
                replace (Z.to_nat (1 + Z.of_nat i)) with (S i) by lia.
                apply key_at__In_tri_bucket. rewrite <- E_te.
                apply (TrigramIndexImpl.tri_lookup_complete_all attr key seps
                         _ _ pv (String.substring (S i) 3 pv));
                  [ exact H_in | exact H_free | | | ].
                1:{ destruct pv; [ cbn [String.length] in H_len; lia
                                 | discriminate ]. }
                1: apply contains_test_true__occurrence; exact H_p.
                unfold trigrams. apply in_map_iff.
                exists (S i); split; [ reflexivity | ]. apply in_seq. lia. } }
        rewrite (probe_recheck_cands_eq attr key rows pv _ H_nd H_compl).
        unfold probe_body. reflexivity.
      Qed.

      (* ------------------------------------------------------------------
         The index of the table's rows IS the index the table stores.

         A maintenance rule such as cons_to_tri_insert_head leaves behind
         the index of the UNCHANGED part of the table, which is still a
         recomputation; this rule turns that into a read of the stored
         dictionary.  Without it a maintained write still folds over every
         row and re-tokenizes every text.

         It is sound only because of the invariant -- it IS the invariant,
         read from left to right -- but it needs no declaration, since the
         trigram member's invariant holds of any table the index was
         installed on.
         ------------------------------------------------------------------ *)
      Definition tri_use_idx_head (e : expr) : expr :=
        match e with
        | etri_idx tup0 tup1 tup2 tup3 acc0 acc1
            wrd0 wrd1 wacc0 wacc1 gvar0 gvar1 gvar2 sacc0 sacc1 sacc2
            bkt0 bkt1 attr0 key0 key1 seps0
            (EAccess (ELoc tbl0) id_tag0) =>
            if all_eqb [(tup, [tup0; tup1; tup2; tup3]);
                        (acc, [acc0; acc1]); (wrd, [wrd0; wrd1]);
                        (wacc, [wacc0; wacc1]); (gvar, [gvar0; gvar1; gvar2]);
                        (sacc, [sacc0; sacc1; sacc2]); (bkt, [bkt0; bkt1]);
                        (attr, [attr0]); (seps, [seps0]); (key, [key0; key1]);
                        (tbl, [tbl0]); (id_tag, [id_tag0])]
            then tri_e
            else e
        | _ => e
        end.

      (* What the trigram member's invariant says on its own, without the
         declaration the lookups also need. *)
      Lemma tri_invariant__rows :
        forall tl rt (v : value),
          access_record rt attr = Success TString ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          type_of_value v (TRecord tl) ->
          tri_aux_wf_at v ->
          exists rv rv_aux rows,
            v = VRecord rv
            /\ record_proj id_tag rv = VList rows
            /\ record_proj aux_tag rv = VRecord rv_aux
            /\ Forall (fun r => type_of_value r (TRecord rt)) rows
            /\ record_proj tri_tag rv_aux
               = TrigramIndexImpl.tri_entries attr key seps rows.
      Proof.
        unfold aux_wf_for_idx, TrigramIndexImpl.idx_wf.
        intros tl rt v H_attr E_id.
        destruct v as [ | | | | | rv | | | | ];
          intros H_vty H_tri; cbv beta iota in H_tri; try contradiction.
        destruct (access_record rv id_tag) as [ v_id | ] eqn:E_vid;
          cbv beta iota in H_tri; try contradiction.
        destruct (access_record rv aux_tag) as [ v_aux | ] eqn:E_vaux;
          cbv beta iota in H_tri; try contradiction.
        destruct v_aux as [ | | | | | rv_aux | | | | ];
          cbv beta iota in H_tri; try contradiction.
        destruct (access_record rv_aux tri_tag) as [ v_tri | ] eqn:E_vtri;
          cbv beta iota in H_tri; try contradiction.
        assert (H_idty : type_of_value v_id (TList (TRecord rt)))
          by (eapply type_of_value_field; [ exact H_vty | exact E_vid | exact E_id ]).
        apply type_of_value_TList_inv in H_idty as [ rows [ E_rows H_rows ] ].
        subst v_id.
        rewrite (TrigramIndexImpl.fiat2_gallina_to_idx hole attr key tup acc
                   gvar sacc bkt
                   H_tup_acc H_tup_gvar H_tup_sacc H_tup_bkt H_gvar_sacc
                   seps wrd wacc H_wrd_tup H_wacc_tup H_wacc_wrd
                   (locals_ok := locals_ok) rows
                   (TrigramIndexImpl.typed_rows_have_text attr rows rt H_attr H_rows))
          in H_tri.
        apply access_record__record_proj in E_vid, E_vaux, E_vtri.
        exists rv, rv_aux, rows.
        (* one conjunct at a time: "repeat split" would prove the reflexive
           one by eq_refl and renumber everything after it *)
        split; [ reflexivity | ].
        split; [ exact E_vid | ].
        split; [ exact E_vaux | ].
        split; [ exact H_rows | ].
        rewrite E_vtri; exact H_tri.
      Qed.

      Lemma tri_use_idx_head_preserve_sem :
        forall tl rt (Gstore : tenv) (store : locals),
          access_record rt attr = Success TString ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          match map.get store tbl with
          | Some v => type_of_value v (TRecord tl) /\ tri_aux_wf_at v
          | _ => False
          end ->
          preserve_sem Gstore store tri_use_idx_head.
      Proof.
        unfold preserve_sem; intros * H_attr E_tbl E_id H_store.
        intros e t Genv env H_Gs H_Ge H_t H_sw H_ew.
        destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
        destruct H_store as [ H_vty H_tri ].
        destruct (tri_invariant__rows tl rt v H_attr E_id H_vty H_tri)
          as [ rv [ rv_aux [ rows [ E_vrec [ E_rows [ E_aux [ H_rows E_tri ] ] ] ] ] ] ].
        subst v.
        repeat destruct_subexpr.
        (* destruct_subexpr stops where the rule's pattern is still stuck on
           the fold's body, so the case analysis is finished by hand, as in
           the insert rule above *)
        cbn [tri_use_idx_head]. repeat (case_match; auto; []).
        cbn in * |-.
        rewrite !Bool.andb_true_iff in *; intuition idtac.
        rewrite eqb_eq in *; subst.
        (* the read *)
        erewrite interp_tbl_field; [ | exact E_v | exact E_aux | reflexivity ].
        (* and the recomputation.  apply, not rewrite: destruct_subexpr has
           left the fold's body spelled out, so it is only CONVERTIBLE with
           to_idx_at's body, which rewrite's syntactic match will not see *)
        rewrite E_tri. symmetry.
        eapply (interp_to_idx_at store env _ rt rows H_attr H_rows).
        rewrite interp_EAccess, interp_ELoc.
        unfold get_local; rewrite E_v; cbv beta iota.
        exact E_rows.
      Qed.

      Lemma tri_use_idx_head_preserve_ty : forall tl ctl t (Gstore : tenv),
          type_wf t -> @IndexInterface.is_tbl_ty tridx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (@IndexInterface.idx_ty tridx t) ->
          preserve_ty Gstore tri_use_idx_head.
      Proof.
        unfold preserve_ty.
        intros tl ctl t Gstore H_twf H_is E_tbl E_id E_aux E_tri.
        cbn [IndexInterface.is_tbl_ty IndexInterface.idx_ty trigram_idx] in H_is, E_tri.
        unfold TrigramIndexImpl.is_tbl_ty, TrigramIndexImpl.idx_ty in H_is, E_tri.
        destruct t as [ | | | | | t1 | | | | ]; try discriminate.
        destruct t1 as [ | | | | | | rt | | | ]; try discriminate.
        destruct (access_record rt attr) as [ at_ty | ] eqn:E_attr; try discriminate.
        destruct (access_record rt key) as [ kt | ] eqn:E_key; try discriminate.
        apply type_eqb_eq in H_is; subst at_ty.
        assert (E_kt : get_attr_type rt key = kt)
          by (unfold get_attr_type; rewrite E_key; reflexivity).
        rewrite E_kt in E_tri. clear E_kt.
        intros e t' Genv H_Gs H_Ge H_t.
        repeat destruct_subexpr.
        cbn [tri_use_idx_head]. repeat (case_match; auto; []).
        cbn in * |-.
        rewrite !Bool.andb_true_iff in *; intuition idtac.
        rewrite eqb_eq in *; subst.
        (* the type the source fold produces is the dictionary's own *)
        repeat invert_type_of_clear. repeat invert_type_of_op_clear.
        repeat rewrite_map_get_put_hyp.
        (* the accumulator's type, chased back to the index's own: the
           table's row type fixes the key's type, and the body's OInsert
           fixes the dictionary's *)
        (* the empty-dictionary literal carries the kind, so inverting the
           atom typings is what resolves the rebuilt dictionary's kind *)
        repeat lazymatch goal with
                 H: type_of_atom _ _ |- _ => inversion H; subst; clear H
               end.
        (* matched by SHAPE for the same reason as below: the table's own
           record variable is generated, and binding the row's text moves
           every generated name after it.  E_tbl has this shape too, so it
           is skipped explicitly. *)
        match goal with
          H : map.get Gstore tbl = Some (TRecord ?TL) |- _ =>
            tryif constr_eq H E_tbl then fail
            else (rewrite E_tbl in H; injection H as H; subst TL)
        end.
        (* matched by SHAPE, not by a generated name: padding the indexed
           text adds typing premises to this goal, and every H<n> after the
           insertion point moves when it does.  E_id has the same shape, so
           it is skipped explicitly and match backtracks past it. *)
        match goal with
          H : access_record tl id_tag = Success (TList _) |- _ =>
            tryif constr_eq H E_id then fail
            else (rewrite E_id in H; injection H as H; subst)
        end.
        (* and the same for the row record and the key's type: every row
           record the inversions produced is the table's own, and the key's
           type is then the one the table's record fixes *)
        repeat match goal with
                 H : Some (TRecord rt) = Some (TRecord ?TL) |- _ =>
                   injection H as H; subst TL
               end.
        match goal with
          H : access_record rt key = Success ?T |- _ =>
            tryif constr_eq H E_key then fail
            else (rewrite E_key in H; injection H as H; subst T)
        end.
        (* the key type of the dictionary the inner fold builds, which the
           two nested folds leave as a unification variable until the
           trigram operator's own typing pins it *)
        repeat match goal with
               | H : Some TString = Some ?T |- _ =>
                   is_var T; injection H as H; subst T
               end.
        eapply TyEAccess;
          [ eapply TyEAccess; [ apply TyELoc; exact E_tbl | exact E_aux ]
          | exact E_tri ].
      Qed.

      (* ==================================================================
         Maintaining the index when a row goes.

         A filter-shaped delete: keep the rows whose key is not k.  The row
         that leaves is not in the expression at all -- only its key is --
         so the rule reads it out of the PRIMARY-KEY member.  That is also
         why it is sound only where the key is declared unique: otherwise
         another row could carry the same key, and taking its contributions
         out of buckets this rule never visits would lose rows from the
         index.  The insert rule needs no declaration, because a row's own
         contributions are all it adds.
         ================================================================== *)
      Notation tri_row_delete_body' :=
        (TrigramIndexImpl.tri_row_delete_body attr key tup acc gvar sacc bkt
           seps wrd wacc).

      Definition filter_neq_to_tri_delete_head (e : expr) : expr :=
        match e with
        | etri_idx tup0 tup1 tup2 tup3 acc0 acc1
            wrd0 wrd1 wacc0 wacc1 gvar0 gvar1 gvar2 sacc0 sacc1 sacc2
            bkt0 bkt1 attr0 key0 key1 seps0
            (flatmap_filter_list (EAccess (ELoc tbl0) id_tag0) y0
               (EUnop ONot (EBinop OEq (EAccess (EVar y1) key2) kexp)) y2 _ _) =>
            if (all_eqb [(tup, [tup0; tup1; tup2; tup3]);
                         (acc, [acc0; acc1]); (wrd, [wrd0; wrd1]);
                         (wacc, [wacc0; wacc1]); (gvar, [gvar0; gvar1; gvar2]);
                         (sacc, [sacc0; sacc1; sacc2]); (bkt, [bkt0; bkt1]);
                         (attr, [attr0]); (seps, [seps0]);
                         (key, [key0; key1; key2]);
                         (tbl, [tbl0]); (id_tag, [id_tag0]); (y0, [y1; y2])]
                && negb (free_immut_in y0 kexp)
                && negb (free_immut_in acc kexp))%bool
            then ELet (to_idx_at (EAccess (ELoc tbl) id_tag)) acc
                   (EOptMatch (EBinop OLookup pk_e kexp) (EVar acc) tup
                      tri_row_delete_body')
            else e
        | _ => e
        end.

      Lemma filter_neq_to_tri_delete_head_preserve_ty :
        forall tl ctl t (Gstore : tenv),
          type_wf t -> @IndexInterface.is_tbl_ty tridx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl pk_tag = Success (@IndexInterface.idx_ty uidx t) ->
          preserve_ty Gstore filter_neq_to_tri_delete_head.
      Proof.
        unfold preserve_ty.
        intros tl ctl t Gstore H_twf H_is E_tbl E_id E_aux E_pk.
        (* the table type's shape, from the index's own is_tbl_ty *)
        apply tri_is_tbl_ty_inv in H_is as [ rt [ kt [ E_t [ E_attr E_key ] ] ] ].
        subst t.
        cbn [IndexInterface.idx_ty unique_dict_idx UniqueDictIndexImpl.idx_ty]
          in E_pk.
        assert (E_kt : get_attr_type rt key = kt)
          by (unfold get_attr_type; rewrite E_key; reflexivity).
        rewrite E_kt in E_pk.
        assert (H_rtwf : type_wf (TRecord rt)) by (inversion H_twf; assumption).
        assert (H_ktwf : type_wf kt)
          by (rewrite <- E_kt; apply get_attr_type_ty_wf; exact H_rtwf).
        clear E_kt.
        intros e t' Genv H_Gs H_Ge H_t.
        repeat destruct_subexpr.
        cbn [filter_neq_to_tri_delete_head]. repeat (case_match; auto; []).
        cbn in * |-.
        rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition idtac.
        rewrite eqb_eq in *; subst.
        (* the source's typing, taken apart for the types it fixes: the
           dictionary's, the row's, and the deleted key's.  Nothing of the
           source's own derivation is reused -- the emitted form is built
           from the index's typing lemmas -- so the inversion may consume
           everything. *)
        repeat invert_type_of_clear. repeat invert_type_of_op_clear.
        repeat rewrite_map_get_put_hyp.
        (* The table read fixes the element type, which fixes the key's.
           match, not lazymatch: the first hypothesis of each shape is the
           one this lemma was given, and rewriting it with itself fails, so
           the search has to be allowed to go on to the inverted copy. *)
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
        (* every copy of the key's type collapses onto kt *)
        repeat match goal with
               | H : access_record _ key = Success ?t0 |- _ =>
                   is_var t0; rewrite E_key in H; injection H as H; subst t0
               end.
        (* the empty-dictionary literal names the kind, so inverting its
           typing is what collapses the source's kind onto the index's *)
        repeat match goal with
               | H : type_of_atom (AEmptyDict _ _) _ |- _ =>
                   inversion H; subst; clear H
               end.
        (* and now the emitted form, from the index's own typing lemmas *)
        eapply TyELet.
        1:{ unfold to_idx_at. eapply TyEFold.
            1:{ eapply TyEAccess; [ apply TyELoc; exact E_tbl | exact E_id ]. }
            1:{ apply TyEAtom; apply TyAEmptyDict';
                [ apply WFTString | apply WFTSet; exact H_ktwf ]. }
            1:{ (* the index's own body, which the lemma's own hypotheses
                   (distinct binders, the row type, the key type) cover *)
                (* eassumption, not assumption: the row type is an evar
                   until the record's own field equations fix it *)
                eapply TrigramIndexImpl.tri_row_body_ty; try eassumption.
                (* the two environment reads, whichever order they come in *)
                all: repeat (rewrite map.get_put_diff by congruence).
                all: rewrite map.get_put_same; reflexivity. } }
        eapply TyEOptMatch.
        1:{ (* the deleted row, from the primary-key member *)
            eapply TyEBinop; [ apply TyOLookup | | ].
            1:{ eapply TyEAccess;
                [ eapply TyEAccess; [ apply TyELoc; exact E_tbl | exact E_aux ]
                | exact E_pk ]. }
            1:{ apply not_free_immut_put_ty2; [ assumption | ].
                eapply not_free_immut_put_ty; [ eassumption | eassumption ]. } }
        1:{ apply TyEVar; rewrite map.get_put_same; reflexivity. }
        1:{ eapply TrigramIndexImpl.tri_row_delete_body_ty; try eassumption.
            all: repeat (rewrite map.get_put_diff by congruence).
            all: rewrite map.get_put_same; reflexivity. }
      Qed.

      Lemma filter_neq_to_tri_delete_head_preserve_sem :
        forall tl rt (Gstore : tenv) (store : locals),
          access_record rt attr = Success TString ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          match map.get store tbl with
          | Some v =>
              type_of_value v (TRecord tl) /\ tri_aux_wf_at v /\ unique_aux_wf_at v
          | _ => False
          end ->
          preserve_sem Gstore store filter_neq_to_tri_delete_head.
      Proof.
        unfold preserve_sem; intros * H_attr E_tbl E_id H_store.
        intros e t Genv env H_Gs H_Ge H_t H_sw H_ew.
        destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
        destruct H_store as [ H_vty [ H_tri H_pk ] ].
        destruct (invariants__probe_data tl rt v H_attr E_id H_vty H_tri H_pk)
          as [ rv [ rv_aux [ rows [ td [ E_vrec [ E_rows [ E_aux
             [ E_tri [ E_pk [ E_te [ H_sets H_nd ] ] ] ] ] ] ] ] ] ] ].
        (* the rows' typing, which the texts the index reads come from.  The
           weaker extractor returns it, and names the same rows. *)
        destruct (tri_invariant__rows tl rt v H_attr E_id H_vty H_tri)
          as [ rv' [ rv_aux' [ rows' [ E_vrec' [ E_rows' [ E_aux' [ H_rows _ ] ] ] ] ] ] ].
        rewrite E_vrec in E_vrec'; injection E_vrec' as E_vrec'; subst rv'.
        rewrite E_rows in E_rows'; injection E_rows' as E_rows'; subst rows'.
        subst v.
        (* the dictionary the invariant names is the index of the rows *)
        rewrite TrigramIndexImpl.tri_entries_VDict in E_te.
        injection E_te as E_te; subst td.
        repeat destruct_subexpr.
        cbn [filter_neq_to_tri_delete_head]. repeat (case_match; auto; []).
        cbn in * |-.
        rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition idtac.
        rewrite eqb_eq in *; subst.
        (* the deleted key's expression, which destruct_subexpr named for us *)
        lazymatch goal with pe : expr |- _ => rename pe into kexp end.
        (* the table read, on both sides *)
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
                            = VDict (TrigramIndexImpl.tri_dict attr key seps
                                       (filter (fun r =>
                                                  negb (value_eqb (row_key key r)
                                                          (interp_expr store env kexp)))
                                          rows)))
        end.
        1:{ rewrite <- TrigramIndexImpl.tri_entries_VDict.
            apply (interp_to_idx_at store env _ rt _ H_attr).
            1:{ apply Forall_forall; intros w H_w.
                apply filter_In in H_w as [ H_w _ ].
                rewrite Forall_forall in H_rows; apply H_rows; exact H_w. }
            1:{ rewrite interp_flatmap_filter_list, E_tr.
                f_equal. apply filter_pointwise; intro w.
                rewrite interp_EUnop, interp_EBinop, interp_EAccess, interp_EVar.
                unfold get_local; rewrite map.get_put_same.
                erewrite <- not_free_immut_put_sem by eassumption.
                cbn [interp_unop interp_binop]. unfold row_key. reflexivity. } }
        rewrite E_src.
        (* and the emitted form *)
        rewrite interp_ELet_step.
        rewrite (interp_to_idx_at store env _ rt rows H_attr H_rows E_tr).
        rewrite TrigramIndexImpl.tri_entries_VDict.
        rewrite interp_EOptMatch, interp_EBinop.
        rewrite (interp_tbl_field store _ rv rv_aux pk_tag _ E_v E_aux E_pk).
        rewrite <- (not_free_immut_put_sem kexp acc store env) by assumption.
        cbn [interp_binop].
        destruct (dict_lookup (interp_expr store env kexp)
                    (UniqueDictIndexImpl.idx_entries key rows)) as [ r | ] eqn:E_lk.
        1:{ (* the row the key names, which the primary-key member resolves *)
            apply (UniqueDictIndexImpl.idx_lookup_Some_inv key)
              in E_lk as [ H_in E_k ].
            (* its text, from the row's type *)
            pose proof (TrigramIndexImpl.typed_rows_have_text attr rows rt
                          H_attr H_rows) as H_txts.
            rewrite Forall_forall in H_txts.
            destruct (H_txts r H_in) as [ txt E_txt ].
            (* what the delete body computes, the binders it reads through
               and the invariant it needs discharged by shape rather than
               by position *)
            erewrite TrigramIndexImpl.interp_tri_row_delete; try eassumption.
            all: try exact E_txt.
            all: try apply map.get_put_same.
            all: try (rewrite map.get_put_diff by congruence;
                      apply map.get_put_same).
            all: try apply TrigramIndexImpl.tri_dict_tri_wf.
            (* erewrite leaves the map instance open as well *)
            all: try exact word_ok.
            (* and the equation: taking the row out of the recomputation is
               taking its key out of the stored index *)
            f_equal.
            assert (E_str : TrigramIndexImpl.row_str attr r = txt)
              by (unfold TrigramIndexImpl.row_str; rewrite E_txt; reflexivity).
            rewrite <- E_str, E_k.
            symmetry.
            (* the lemma carries the index's own section hypotheses, so its
               premises are discharged by shape here too *)
            apply TrigramIndexImpl.tri_dict_filter_neq; try eassumption. }
        1:{ (* no row carries the key, so the filter removes nothing *)
            rewrite interp_EVar; unfold get_local; rewrite map.get_put_same.
            f_equal. symmetry.
            apply TrigramIndexImpl.tri_dict_filter_neq_absent; try assumption.
            all: intros r H_in E_k;
              pose proof (UniqueDictIndexImpl.idx_lookup_Some key
 rows r H_nd H_in) as E_s;
              rewrite E_k, E_lk in E_s; discriminate. }
      Qed.

    End WithTable.


    (* ------------------------------------------------------------------
       What whoever assembles the index record owes this rule.

       Two members' layouts instead of one, because the trigram buckets hold
       keys and only the primary-key index can resolve them -- that is the
       price of a rule that needs a second index to interpret the first
       one's answer.  And one invariant bridge delivering both members'
       relations, where the primary-key one is the STRONG relation that no
       index establishes from typing and the declaration pays for.
       ------------------------------------------------------------------ *)
    (* What a rule that only READS the trigram member needs: where that
       member sits in the index record, and that its own invariant holds.
       Not the primary key's -- so such a rule is not gated on a
       declaration. *)
    Definition trigram_idx_bridges (is_tbl_ty' : type -> bool) (aux_ty : type -> type)
      (aux_wf : value -> Prop) : Prop :=
      aux_ty_for_idx id_tag aux_tag tri_tag (@IndexInterface.idx_ty tridx) aux_ty
      /\ (forall t, is_tbl_ty' t = true -> @IndexInterface.is_tbl_ty tridx t = true)
      /\ (forall (t : type) (v : value),
             type_wf t -> is_tbl_ty' t = true ->
             type_of_value v (aux_ty t) -> aux_wf v -> tri_aux_wf_at v).

    Definition trigram_bridges (is_tbl_ty' : type -> bool) (aux_ty : type -> type)
      (aux_wf : value -> Prop) : Prop :=
      aux_ty_for_idx id_tag aux_tag tri_tag (@IndexInterface.idx_ty tridx) aux_ty
      /\ aux_ty_for_idx id_tag aux_tag pk_tag (@IndexInterface.idx_ty uidx) aux_ty
      /\ (forall t, is_tbl_ty' t = true -> @IndexInterface.is_tbl_ty tridx t = true)
      (* the trigram member's own relation, which any index establishes from
         typing, and the primary-key member's STRONG one, which none does *)
      /\ (forall (t : type) (v : value),
             type_wf t -> is_tbl_ty' t = true ->
             type_of_value v (aux_ty t) -> aux_wf v -> tri_aux_wf_at v)
      /\ (forall (t : type) (v : value),
             type_wf t -> is_tbl_ty' t = true ->
             type_of_value v (aux_ty t) -> aux_wf v -> unique_aux_wf_at v).

    Lemma trigram_lookup_head_sound :
      forall is_tbl_ty' aux_ty (aux_wf : value -> Prop),
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf trigram_lookup_head.
    Proof.
      unfold trigram_bridges, aux_ty_for_idx, expr_aug_transf_sound.
      intros * [ H_aty1 [ H_aty2 [ H_is [ H_wf1 H_wf2 ] ] ] ] *.
      intros H_Gs H_Ge H_twf H_is' H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl end.
      (* the table type's shape, and both members' places in the record *)
      apply H_is in H_is' as H_is_tri.
      apply tri_is_tbl_ty_inv in H_is_tri as [ rt [ kt [ E_t [ E_attr E_key ] ] ] ].
      specialize (H_aty1 tbl_ty); specialize (H_aty2 tbl_ty).
      repeat destruct_match_hyp; intuition idtac.
      (* destruct_match_hyp names the record's field equations itself, so
         they are picked up by eassumption rather than by name *)
      1:{ (* preserve_ty's own premises come as goals too, so everything
             that is already in context goes by eassumption and only the
             index's is_tbl_ty is left to the bridge *)
          eapply trigram_lookup_head_preserve_ty; try eassumption.
          apply H_is; exact H_is'. }
      1:{ subst tbl_ty.
          eapply trigram_lookup_head_preserve_sem; try eassumption.
          (* and the store carries both invariants at the table *)
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

    (* The same, for the guarded form.  The two proofs differ only in which
       head they appeal to. *)
    Lemma trigram_lookup_guarded_head_sound :
      forall is_tbl_ty' aux_ty (aux_wf : value -> Prop),
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf trigram_lookup_guarded_head.
    Proof.
      unfold trigram_bridges, aux_ty_for_idx, expr_aug_transf_sound.
      intros * [ H_aty1 [ H_aty2 [ H_is [ H_wf1 H_wf2 ] ] ] ] *.
      intros H_Gs H_Ge H_twf H_is' H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl end.
      apply H_is in H_is' as H_is_tri.
      apply tri_is_tbl_ty_inv in H_is_tri as [ rt [ kt [ E_t [ E_attr E_key ] ] ] ].
      specialize (H_aty1 tbl_ty); specialize (H_aty2 tbl_ty).
      repeat destruct_match_hyp; intuition idtac.
      1:{ eapply trigram_lookup_guarded_head_preserve_ty; try eassumption.
          apply H_is; exact H_is'. }
      1:{ subst tbl_ty.
          eapply trigram_lookup_guarded_head_preserve_sem; try eassumption.
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

    (* The all-trigram rules' soundness, by the same argument: the
       bridges give the typing and the two invariants, and the two
       obligations are already proved. *)
    Lemma trigram_lookup_all_head_sound :
      forall is_tbl_ty' aux_ty (aux_wf : value -> Prop),
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf trigram_lookup_all_head.
    Proof.
      unfold trigram_bridges, aux_ty_for_idx, expr_aug_transf_sound.
      intros * [ H_aty1 [ H_aty2 [ H_is [ H_wf1 H_wf2 ] ] ] ] *.
      intros H_Gs H_Ge H_twf H_is' H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl end.
      apply H_is in H_is' as H_is_tri.
      apply tri_is_tbl_ty_inv in H_is_tri as [ rt [ kt [ E_t [ E_attr E_key ] ] ] ].
      specialize (H_aty1 tbl_ty); specialize (H_aty2 tbl_ty).
      repeat destruct_match_hyp; intuition idtac.
      1:{ eapply trigram_lookup_all_head_preserve_ty; try eassumption.
          apply H_is; exact H_is'. }
      1:{ subst tbl_ty.
          eapply trigram_lookup_all_head_preserve_sem; try eassumption.
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

    Lemma trigram_lookup_all_guarded_head_sound :
      forall is_tbl_ty' aux_ty (aux_wf : value -> Prop),
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf trigram_lookup_all_guarded_head.
    Proof.
      unfold trigram_bridges, aux_ty_for_idx, expr_aug_transf_sound.
      intros * [ H_aty1 [ H_aty2 [ H_is [ H_wf1 H_wf2 ] ] ] ] *.
      intros H_Gs H_Ge H_twf H_is' H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl end.
      apply H_is in H_is' as H_is_tri.
      apply tri_is_tbl_ty_inv in H_is_tri as [ rt [ kt [ E_t [ E_attr E_key ] ] ] ].
      specialize (H_aty1 tbl_ty); specialize (H_aty2 tbl_ty).
      repeat destruct_match_hyp; intuition idtac.
      1:{ eapply trigram_lookup_all_guarded_head_preserve_ty; try eassumption.
          apply H_is; exact H_is'. }
      1:{ subst tbl_ty.
          eapply trigram_lookup_all_guarded_head_preserve_sem; try eassumption.
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

    (* The rules, applied everywhere below the installation. *)
    (* and the lookups' bridges include them *)
    Lemma trigram_bridges__idx_bridges : forall is_tbl_ty' aux_ty aux_wf,
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        trigram_idx_bridges is_tbl_ty' aux_ty aux_wf.
    Proof.
      unfold trigram_bridges, trigram_idx_bridges.
      intros * [ H_aty1 [ _ [ H_is [ H_wf1 _ ] ] ] ].
      split; [ exact H_aty1 | split; [ exact H_is | exact H_wf1 ] ].
    Qed.

    Lemma tri_use_idx_head_sound :
      forall is_tbl_ty' aux_ty (aux_wf : value -> Prop),
        trigram_idx_bridges is_tbl_ty' aux_ty aux_wf ->
        expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf tri_use_idx_head.
    Proof.
      unfold trigram_idx_bridges, aux_ty_for_idx, expr_aug_transf_sound.
      intros * [ H_aty [ H_is H_wf ] ] *.
      intros H_Gs H_Ge H_twf H_is' H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl end.
      apply H_is in H_is' as H_is_tri.
      apply tri_is_tbl_ty_inv in H_is_tri as [ rt [ kt [ E_t [ E_attr E_key ] ] ] ].
      specialize (H_aty tbl_ty).
      repeat destruct_match_hyp; intuition idtac.
      1:{ eapply tri_use_idx_head_preserve_ty; try eassumption.
          apply H_is; exact H_is'. }
      1:{ subst tbl_ty.
          eapply tri_use_idx_head_preserve_sem; try eassumption.
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
          split; [ assumption | ].
          eapply H_wf; [ exact H_twf | exact H_is' | | exact H_aw ].
          lazymatch goal with E : aux_ty _ = _ |- _ => rewrite E end.
          assumption. }
    Qed.

    Definition tri_use_idx_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl] (tri_use_idx_head tbl).

    Lemma tri_use_idx_transf_sound : forall is_tbl_ty' aux_ty aux_wf,
        trigram_idx_bridges is_tbl_ty' aux_ty aux_wf ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf tri_use_idx_transf.
    Proof.
      intros * H_br. unfold tri_use_idx_transf.
      apply fold_command_with_globals_sound.
      apply tri_use_idx_head_sound; exact H_br.
    Qed.

    Definition trigram_lookup_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl] (trigram_lookup_head tbl).

    Definition trigram_lookup_guarded_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl] (trigram_lookup_guarded_head tbl).

    Definition trigram_lookup_all_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl] (trigram_lookup_all_head tbl).

    Definition trigram_lookup_all_guarded_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl]
                   (trigram_lookup_all_guarded_head tbl).

    Lemma trigram_lookup_transf_sound : forall is_tbl_ty' aux_ty aux_wf,
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf trigram_lookup_transf.
    Proof.
      intros * H_br. unfold trigram_lookup_transf.
      apply fold_command_with_globals_sound.
      apply trigram_lookup_head_sound; exact H_br.
    Qed.

    Lemma trigram_lookup_guarded_transf_sound : forall is_tbl_ty' aux_ty aux_wf,
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf trigram_lookup_guarded_transf.
    Proof.
      intros * H_br. unfold trigram_lookup_guarded_transf.
      apply fold_command_with_globals_sound.
      apply trigram_lookup_guarded_head_sound; exact H_br.
    Qed.

    Lemma trigram_lookup_all_transf_sound : forall is_tbl_ty' aux_ty aux_wf,
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf trigram_lookup_all_transf.
    Proof.
      intros * H_br. unfold trigram_lookup_all_transf.
      apply fold_command_with_globals_sound.
      apply trigram_lookup_all_head_sound; exact H_br.
    Qed.

    Lemma trigram_lookup_all_guarded_transf_sound :
      forall is_tbl_ty' aux_ty aux_wf,
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf
          trigram_lookup_all_guarded_transf.
    Proof.
      intros * H_br. unfold trigram_lookup_all_guarded_transf.
      apply fold_command_with_globals_sound.
      apply trigram_lookup_all_guarded_head_sound; exact H_br.
    Qed.

    Lemma filter_neq_to_tri_delete_head_sound :
      forall is_tbl_ty' aux_ty (aux_wf : value -> Prop),
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf
          filter_neq_to_tri_delete_head.
    Proof.
      unfold trigram_bridges, aux_ty_for_idx, expr_aug_transf_sound.
      intros * [ H_aty1 [ H_aty2 [ H_is [ H_wf1 H_wf2 ] ] ] ] *.
      intros H_Gs H_Ge H_twf H_is' H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl end.
      apply H_is in H_is' as H_is_tri.
      apply tri_is_tbl_ty_inv in H_is_tri as [ rt [ kt [ E_t [ E_attr E_key ] ] ] ].
      specialize (H_aty1 tbl_ty); specialize (H_aty2 tbl_ty).
      repeat destruct_match_hyp; intuition idtac.
      1:{ eapply filter_neq_to_tri_delete_head_preserve_ty; try eassumption.
          apply H_is; exact H_is'. }
      1:{ subst tbl_ty.
          eapply filter_neq_to_tri_delete_head_preserve_sem; try eassumption.
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

    Definition filter_neq_to_tri_delete_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl] (filter_neq_to_tri_delete_head tbl).

    Lemma filter_neq_to_tri_delete_transf_sound : forall is_tbl_ty' aux_ty aux_wf,
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf filter_neq_to_tri_delete_transf.
    Proof.
      intros * H_br. unfold filter_neq_to_tri_delete_transf.
      apply fold_command_with_globals_sound.
      apply filter_neq_to_tri_delete_head_sound; exact H_br.
    Qed.

    (* The delete rule is gated on the same declaration as the lookups, for
       a different reason: a lookup needs the key to resolve a bucket's keys
       to single rows, while maintenance needs it to know that the row it
       takes out of the buckets is the only one the filter removed. *)
    Definition tri_delete_gated (ds : list decl) : string -> command -> command :=
      if declares_unique key ds
      then filter_neq_to_tri_delete_transf
      else fun _ => id.

    Lemma tri_delete_gated_sound : forall ds is_tbl_ty' aux_ty aux_wf,
        (declares_unique key ds = true -> trigram_bridges is_tbl_ty' aux_ty aux_wf) ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf (tri_delete_gated ds).
    Proof.
      intros * H_br. unfold tri_delete_gated.
      destruct (declares_unique key ds) eqn:E_uq.
      1: apply filter_neq_to_tri_delete_transf_sound, H_br; reflexivity.
      1: unfold aug_transf_sound, id; intros; repeat split; auto.
    Qed.

    (* ------------------------------------------------------------------
       The rule as the pipeline uses it: the identity unless the table's
       declarations name the key the buckets hold.

       The gate is on the PRIMARY KEY, not on anything about trigrams.  The
       trigram index is sound to install and to read on any table; what needs
       a declaration is resolving a bucket's keys back to single rows, and
       that is the primary-key index's business.
       ------------------------------------------------------------------ *)
    (* The literal rule runs first, so a literal pattern gets the probe
       without a guard and the guarded rule then finds nothing left to do
       there.  A pattern that is not a literal is left to the guard. *)
    (* The all-trigram rules, not the single-bucket ones: they have the same
       shape and a narrower candidate set, so the narrow one is installed and
       the single-bucket pair stays proved as the k = 1 instance it is. *)
    Definition trigram_lookup_gated (ds : list decl) : string -> command -> command :=
      if declares_unique key ds
      then fun tbl => Basics.compose (trigram_lookup_all_guarded_transf tbl)
                        (trigram_lookup_all_transf tbl)
      else fun _ => id.

    Lemma trigram_lookup_gated_sound : forall ds is_tbl_ty' aux_ty aux_wf,
        (declares_unique key ds = true -> trigram_bridges is_tbl_ty' aux_ty aux_wf) ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf (trigram_lookup_gated ds).
    Proof.
      intros * H_br. unfold trigram_lookup_gated.
      destruct (declares_unique key ds) eqn:E_uq.
      1:{ apply aug_transf_sound_compose.
          1: apply trigram_lookup_all_guarded_transf_sound, H_br; reflexivity.
          1: apply trigram_lookup_all_transf_sound, H_br; reflexivity. }
      1: unfold aug_transf_sound, id; intros; repeat split; auto.
    Qed.
  End WithMap.
End WithIndexUse.
