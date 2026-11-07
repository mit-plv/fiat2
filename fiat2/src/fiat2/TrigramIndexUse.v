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

   The rules may fire only where the pattern HAS a trigram.  The literal
   forms decide that statically, the pattern being a literal of length at
   least three, so they need no runtime guard. *)

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

  (* The row a key resolves to, rechecked by the SOURCE's own filter --
     whatever that filter is.  The filter is a parameter because the lemma
     below needs nothing about it: a second predicate therefore gets the
     lemma rather than a copy of its proof. *)
  Definition probe_body_t (test : value -> bool) (rows : list value) (k : value)
    : list value :=
    match dict_lookup k (UniqueDictIndexImpl.idx_entries key rows) with
    | Some r => if test r then [r] else nil
    | None => nil
    end.

  (* The scan and ANY sound candidate set agree, for ANY recheck.

     The candidate list is arbitrary and the only obligation is
     COMPLETENESS -- every row the scan would keep has its key in the list.
     Soundness needs nothing, because the recheck is the source's own filter
     and the key probe only ever returns rows of the table.  Nothing here
     looks at what the filter tests, which is why the substring predicate
     and the threshold predicate share this proof. *)
  Lemma probe_recheck_cands_eq_t :
    forall (rows : list value) (test : value -> bool) (cl : list value),
      NoDup (List.map (row_key key) rows) ->
      (forall (r : value), In r rows -> test r = true ->
                           In (row_key key r) cl) ->
      list_to_set (filter test (list_to_set rows))
      = list_to_set (flat_map (probe_body_t test rows) cl).
  Proof.
    intros rows test cl H_nd H_compl.
    apply NoDup_SSorted_double_incl_eq;
      auto using list_to_set_NoDup, list_to_set_SSorted.
    1:{ (* completeness, which is the hypothesis *)
        unfold incl; intros v H_in.
        apply list_to_set_incl, filter_In in H_in as [ H_in H_p ].
        apply list_to_set_incl in H_in.
        apply list_to_set_incl_r, in_flat_map.
        exists (row_key key v); split; [ apply H_compl; assumption | ].
        unfold probe_body_t.
        rewrite (UniqueDictIndexImpl.idx_lookup_Some key rows v H_nd H_in).
        rewrite H_p. cbn [In]; auto. }
    1:{ (* soundness, which is free *)
        unfold incl; intros v H_in.
        apply list_to_set_incl, in_flat_map in H_in as [ kk [ H_k H_v ] ].
        unfold probe_body_t in H_v.
        destruct (dict_lookup kk (UniqueDictIndexImpl.idx_entries key rows))
          as [ r | ] eqn:E_lk; [ | contradiction ].
        destruct (test r) eqn:E_p; [ | contradiction ].
        destruct H_v as [ E_v | H_bad ]; [ subst r | contradiction ].
        apply (UniqueDictIndexImpl.idx_lookup_Some_inv key)
          in E_lk as [ H_rows _ ].
        apply list_to_set_incl_r, filter_In; split; [ | exact E_p ].
        apply list_to_set_incl_r; exact H_rows. }
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
    exact (probe_recheck_cands_eq_t rows (contains_test p) cl H_nd H_compl).
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
  (* The separators the index tokenizes on, and the two binders of the
     fold over a row's WORDS: the word itself, and the index built from the
     words before it.  Last again. *)
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
  (* The all-trigram probe's one binder, which replaces the cpos/cacc pair:
     the aggregate carries no accumulator, so the only name the rewritten
     candidate set introduces is the trigram it is looking up.  Last again,
     so the lemmas above keep the arguments they had. *)
  Context (cgram : string).

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

    (* ------------------------------------------------------------------
       The trigram member's APPEND, normalised into its CONS.

       One rewrite, after which cons_to_tri_insert_head above does the
       maintenance unchanged -- the division of labour every other index
       gets.  What it rests on is TrigramIndexImpl.tri_entries_app_singleton,
       and that fact is not the dictionaries': a row puts its KEY into the
       bucket of every trigram of every word of its text, so the per-row step
       is a fold of a fold.  Two rows commute because set_insert is
       commutative AND IDEMPOTENT -- rows whose trigram sets OVERLAP may
       write one bucket in either order.  The bag-backed indexes needed only
       commutativity.
       ------------------------------------------------------------------ *)
    Definition snoc_to_cons_in_tri_head (e : expr) : expr :=
      match e with
      | etri_idx tup0 tup1 tup2 tup3 acc0 acc1
          wrd0 wrd1 wacc0 wacc1 gvar0 gvar1 gvar2 sacc0 sacc1 sacc2
          bkt0 bkt1 attr0 key0 key1 seps0
          (EBinop OConcat e2 (EBinop OCons e1 (EAtom (ANil _)))) =>
          if (all_eqb [(tup, [tup0; tup1; tup2; tup3]);
                       (acc, [acc0; acc1]); (wrd, [wrd0; wrd1]);
                       (wacc, [wacc0; wacc1]); (gvar, [gvar0; gvar1; gvar2]);
                       (sacc, [sacc0; sacc1; sacc2]); (bkt, [bkt0; bkt1]);
                       (attr, [attr0]); (key, [key0; key1]); (seps, [seps0])])%bool
          then etri_idx tup0 tup1 tup2 tup3 acc0 acc1
                 wrd0 wrd1 wacc0 wacc1 gvar0 gvar1 gvar2 sacc0 sacc1 sacc2
                 bkt0 bkt1 attr0 key0 key1 seps0
                 (EBinop OCons e1 e2)
          else e
      | _ => e
      end.

    Lemma snoc_to_cons_in_tri_head_preserve_ty : forall (Gstore : tenv),
        preserve_ty Gstore snoc_to_cons_in_tri_head.
    Proof.
      unfold preserve_ty; intros Gstore e t Genv H_Gs H_Ge H_t.
      repeat destruct_subexpr.
      cbn [snoc_to_cons_in_tri_head]. repeat (case_match; auto; []).
      cbn in * |-.
      rewrite !Bool.andb_true_iff in *; intuition idtac.
      rewrite eqb_eq in *; subst.
      lazymatch goal with
      | H : type_of _ _ (EFold _ _ _ _ _) _ |- _ => inversion H; subst; clear H
      end.
      lazymatch goal with
      | H : type_of _ _ (EBinop OConcat _ _) _ |- _ =>
          inversion H; subst; clear H
      end.
      invert_type_of_op_clear.
      lazymatch goal with
      | H : type_of _ _ (EBinop OCons _ _) _ |- _ =>
          inversion H; subst; clear H
      end.
      invert_type_of_op_clear.
      eapply TyEFold; [ | eassumption | eassumption ].
      eapply TyEBinop; [ apply TyOCons | eassumption | eassumption ].
    Qed.

    Lemma snoc_to_cons_in_tri_head_preserve_sem :
      forall (Gstore : tenv) (store : locals),
        tup <> acc -> preserve_sem Gstore store snoc_to_cons_in_tri_head.
    Proof.
      unfold preserve_sem;
        intros Gstore store H_ta e t Genv env H_Gs H_Ge H_t H_sw H_ew.
      repeat destruct_subexpr.
      cbn [snoc_to_cons_in_tri_head]. repeat (case_match; auto; []).
      cbn in * |-.
      rewrite !Bool.andb_true_iff in *; intuition idtac.
      rewrite eqb_eq in *; subst.
      lazymatch goal with
      | H : type_of _ _ (EFold _ _ _ _ _) _ |- _ => inversion H; subst; clear H
      end.
      lazymatch goal with
      | H : type_of _ _ (EBinop OConcat _ _) _ |- _ =>
          inversion H; subst; clear H
      end.
      invert_type_of_op_clear.
      lazymatch goal with
      | H : type_of _ _ (EBinop OCons _ _) _ |- _ =>
          inversion H; subst; clear H
      end.
      invert_type_of_op_clear.
      (* The row type is a RECORD whose attr is a STRING, forced by the body's
         OWords on that attribute: the bridge to tri_entries is stated in
         those terms, so the rule cannot proceed without them. *)
      lazymatch goal with
      | H : type_of _ _ (EFold (EBinop OWords _ (EAccess (EVar _) _)) _ _ _ _) _
        |- _ => inversion H; subst
      end.
      lazymatch goal with
      | H : type_of _ _ (EBinop OWords _ (EAccess (EVar _) _)) _ |- _ =>
          inversion H; subst
      end.
      invert_type_of_op_clear.
      lazymatch goal with
      | H : type_of _ _ (EAccess (EVar _) _) _ |- _ => inversion H; subst
      end.
      lazymatch goal with
      | H : type_of _ _ (EVar tup) _ |- _ => inversion H; subst
      end.
      lazymatch goal with
      | H : map.get (map.put (map.put Genv tup _) acc _) tup = Some _ |- _ =>
          rewrite map.get_put_diff in H by congruence;
          rewrite map.get_put_same in H; do_injection; subst
      end.
      (* the table's rows, and the row being appended *)
      apply_type_sound e1_1. invert_type_of_value_clear.
      apply_type_sound e1_2_1.
      lazymatch goal with
      | H : VList ?rs = interp_expr store env e1_1 |- _ =>
          assert (E_rows : interp_expr store env e1_1 = VList rs)
            by (symmetry; exact H)
      end.
      lazymatch goal with
      | H : Forall (fun v => type_of_value v (TRecord tl)) ?rs |- _ =>
          assert (H_Fc : Forall (fun v => type_of_value v (TRecord tl))
                           (interp_expr store env e1_2_1 :: rs))
            by (constructor; assumption);
          assert (H_Fa : Forall (fun v => type_of_value v (TRecord tl))
                           (rs ++ [interp_expr store env e1_2_1]))
            by (eapply Forall_Permutation_iff;
                [ apply Permutation_cons_append | exact H_Fc ])
      end.
      (* each side's collection, as a value *)
      lazymatch goal with
      | H : VList ?rs = interp_expr store env e1_1 |- _ =>
          assert (E_cons : interp_expr store env (EBinop OCons e1_2_1 e1_1)
                           = VList (interp_expr store env e1_2_1 :: rs))
            by (cbn [interp_expr interp_binop]; rewrite E_rows; reflexivity);
          assert (E_snoc : interp_expr store env
                             (EBinop OConcat e1_1
                                (EBinop OCons e1_2_1 (EAtom (ANil t0))))
                           = VList (rs ++ [interp_expr store env e1_2_1]))
            by (cbn [interp_expr interp_binop interp_atom];
                rewrite E_rows; reflexivity)
      end.
      lazymatch goal with
      | |- interp_expr _ _ ?lhs = interp_expr _ _ ?rhs =>
          replace (interp_expr store env lhs)
            with (TrigramIndexImpl.tri_entries attr key seps
                    (interp_expr store env e1_2_1 :: l))
            by (symmetry;
                eapply interp_to_idx_at;
                [ exact H3 | exact H_Fc | exact E_cons ]);
          replace (interp_expr store env rhs)
            with (TrigramIndexImpl.tri_entries attr key seps
                    (l ++ [interp_expr store env e1_2_1]))
            by (symmetry;
                eapply interp_to_idx_at;
                [ exact H3 | exact H_Fa | exact E_snoc ])
      end.
      symmetry. apply TrigramIndexImpl.tri_entries_app_singleton.
    Qed.

    Lemma snoc_to_cons_in_tri_head_sound :
      tup <> acc ->
      expr_transf_sound (locals := locals) snoc_to_cons_in_tri_head.
    Proof.
      unfold expr_transf_sound; intros H_ne *; intros.
      intuition idtac.
      1: eapply snoc_to_cons_in_tri_head_preserve_ty; eauto.
      1: eapply (snoc_to_cons_in_tri_head_preserve_sem Gstore store H_ne); eauto.
    Qed.

    Lemma snoc_to_cons_in_tri_sound : forall is_tbl_ty' aux_ty aux_wf,
        tup <> acc ->
        aug_transf_sound (locals := locals) is_tbl_ty' aux_ty aux_wf
          (fun tbl => fold_command_with_globals [tbl] snoc_to_cons_in_tri_head).
    Proof.
      intros * H_ne.
      apply fold_command_with_globals_sound.
      apply expr_transf_sound__expr_aug_transf_sound.
      apply snoc_to_cons_in_tri_head_sound; exact H_ne.
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
        destruct v as [ | | | | | rv | | | | ];
          intros H_vty H_tri H_pk;
          cbv beta iota in H_tri, H_pk; try contradiction.
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
         makes the k = 1 case need no rule of its own: with one trigram
         tri_cands_from's fold is empty, so the candidate set IS a single
         bucket.
         ------------------------------------------------------------------ *)
      Definition tri_bucket_e (g : expr) : expr :=
        EOptMatch (EBinop OLookup tri_e g) (EAtom (AEmptySet None)) b (EVar b).

      Definition probe_from (cand p : expr) : expr :=
        EFlatmap LikeSet cand k
          (EOptMatch (EBinop OLookup pk_e (EVar k)) (EAtom (AEmptySet None))
             y (EIf (EBinop OStrContains (EAccess (EVar y) attr) p)
                  (EBinop OSetInsert (EAtom (AEmptySet None)) (EVar y))
                  (EAtom (AEmptySet None)))).


      (* One more bucket narrows the candidates.  Left-nested, so that the
         chain can be built by a fold over the pattern's trigram list and
         the empty list of extra trigrams leaves the single probe alone. *)
      Definition tri_cands_step (a : expr) (g : string) : expr :=
        EBinop OSetIntersect a (tri_bucket_e (EAtom (AString g))).

      Definition tri_cands_from (cnd : expr) (gs : list string) : expr :=
        fold_left tri_cands_step gs cnd.

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


      (* ------------------------------------------------------------------
         The candidate set, as an AGGREGATE over the set of buckets.

         Every trigram of the pattern must be present for the pattern to
         occur, so the candidates are the intersection of all their buckets.
         The old form above folded OSetIntersect over ORange 1 (|p| - 2),
         reading each trigram out of the string with OSubstring.  That shape
         paid twice: intersection has no identity over an unknown universe,
         so the fold needed a SEED, and the seed had to be the bucket of a
         trigram named by POSITION.  AGIntersect is associative, commutative
         and idempotent, so the aggregate commits to no order, needs no seed,
         and answers at TOption -- and its None, the empty set of buckets, is
         exactly the case in which the index says nothing.
         ------------------------------------------------------------------ *)

      (* One bucket per trigram of the pattern, as a SET of buckets.  The
         coercion deduplicates, which costs nothing in answers because
         intersection is idempotent, and saves a probe whenever a pattern
         repeats a trigram -- pad "aaaa" contains "aaa" twice. *)
      Definition tri_buckets (p : expr) : expr :=
        EFlatmap LikeSet (EUnop OSetOfList (EUnop OTrigrams p)) cgram
          (EBinop OSetInsert (EAtom (AEmptySet None)) (tri_bucket_e (EVar cgram))).

      Definition dyn_cands' (p : expr) : expr :=
        EOptMatch (EACIFold AGIntersect (tri_buckets p))
          (EAtom (AEmptySet None)) b (EVar b).

      (* The Gallina side, written to match what the interpreter produces
         rather than to be canonical: the outer list_to_set is EFlatmap
         LikeSet's, the inner one OSetOfList's. *)
      Definition bucket_set (pv : string) (d : value) : list value :=
        list_to_set
          (flat_map (fun gv => [VSet (tri_bucket gv d)])
             (list_to_set (List.map VString (trigrams pv)))).

      Definition inter_all (bs : list value) : value :=
        fold_right (snd (interp_aci_aggr AGIntersect))
          (fst (interp_aci_aggr AGIntersect)) bs.

      (* The ONLY fact the rule needs about the aggregate, and it mentions
         no order: a key survives the intersection exactly when it is in
         every bucket.  That is why no permutation argument is needed even
         though OSetOfList has sorted and deduplicated the trigrams -- the
         characterization is order-free because the operation is. *)
      Lemma inter_all_chara :
        forall bs,
          bs <> nil ->
          Forall (fun s => exists l, s = VSet l) bs ->
          exists l, inter_all bs = VOption (Some (VSet l)) /\
                      (forall v, In v l <-> (forall l', In (VSet l') bs -> In v l')).
      Proof.
        unfold inter_all; cbn [interp_aci_aggr].
        induction bs as [ | s bs IH ]; intros H_ne H_sets; [ congruence | ].
        invert_Forall.
        lazymatch goal with H: exists _, s = VSet _ |- _ =>
          destruct H as [ l0 E_s ]; subst s end.
        destruct bs as [ | s' bs ].
        (* one bucket: it IS the answer, with no seed to supply *)
        1:{ exists l0; cbn [fold_right]; split; [ reflexivity | ].
            intros v; split.
            1:{ intros H_in l' [ E | [] ]. injection E as E; subst l'. exact H_in. }
            1: intros H_all; apply H_all; left; reflexivity. }
        (* at least two: narrow the tail's answer by this bucket *)
        1:{ destruct (IH ltac:(discriminate) ltac:(assumption)) as [ a [ E_a H_a ] ].
            cbn [fold_right] in *. rewrite E_a.
            exists (filter (fun x => set_mem x a) l0); split; [ reflexivity | ].
            intros v; split.
            1:{ intros H_in; apply filter_In in H_in as [ H_l0 H_mem ].
                apply set_mem_true_iff in H_mem.
                intros l' [ E | H_in' ].
                1:{ injection E as E; subst l'; exact H_l0. }
                1: apply (proj1 (H_a v) H_mem); exact H_in'. }
            1:{ intros H_all; apply filter_In; split.
                1: apply H_all; left; reflexivity.
                1:{ apply set_mem_true_iff, (proj2 (H_a v)).
                    intros l' H_in'; apply H_all; right; exact H_in'. } } }
      Qed.

      (* ----------------------------------------------------------------
         THE UNION, which is the other end of the same family.

         Stage 1 intersects the buckets, because an occurrence puts EVERY
         trigram of the pattern in the text.  A THRESHOLD cannot intersect:
         a row similar enough need not share every trigram, which is what a
         threshold means, so the candidate pool is the UNION and the count
         over it is what prunes.  AGUnion and AGIntersect differ by one
         constructor, so the pool reuses tri_buckets and its bridge whole.
         ---------------------------------------------------------------- *)

      Lemma In_fold_set_insert_iff : forall (l base : list value) v0,
          In v0 (fold_right set_insert base l) <-> In v0 l \/ In v0 base.
      Proof.
        induction l as [ | x l IH ]; cbn [fold_right In]; intros base v0.
        1: intuition.
        1: rewrite set_insert_In, IH; intuition congruence.
      Qed.

      Definition union_all (bs : list value) : value :=
        fold_right (snd (interp_aci_aggr AGUnion))
          (fst (interp_aci_aggr AGUnion)) bs.

      (* The only fact the threshold rule needs about the aggregate, and it
         mentions no order: a key is in the union exactly when some bucket
         holds it.  Order-free because the operation is, which is why the
         sorting and deduplication OSetOfList performs on the trigrams costs
         no permutation argument -- exactly as for the intersection. *)
      Lemma union_all_chara :
        forall bs,
          bs <> nil ->
          Forall (fun s => exists l, s = VSet l) bs ->
          exists l, union_all bs = VOption (Some (VSet l)) /\
                      (forall v, In v l <-> exists l', In (VSet l') bs /\ In v l').
      Proof.
        unfold union_all; cbn [interp_aci_aggr].
        induction bs as [ | s bs IH ]; intros H_ne H_sets; [ congruence | ].
        invert_Forall.
        lazymatch goal with H: exists _, s = VSet _ |- _ =>
          destruct H as [ l0 E_s ]; subst s end.
        destruct bs as [ | s' bs ].
        (* one bucket: it IS the pool, with no seed to supply *)
        1:{ exists l0; cbn [fold_right]; split; [ reflexivity | ].
            intros v; split.
            1: intros H_in; exists l0; split; [ left; reflexivity | exact H_in ].
            1:{ intros [ l' [ [ E | [] ] H_in ] ].
                injection E as E; subst l'; exact H_in. } }
        (* at least two: widen the tail's pool by this bucket *)
        1:{ destruct (IH ltac:(discriminate) ltac:(assumption)) as [ a [ E_a H_a ] ].
            cbn [fold_right] in *. rewrite E_a.
            exists (fold_right set_insert a l0); split; [ reflexivity | ].
            intros v; rewrite In_fold_set_insert_iff; split.
            1:{ intros [ H_in | H_in ].
                1: exists l0; split; [ left; reflexivity | exact H_in ].
                1:{ apply H_a in H_in as [ l' [ H_in' H_v ] ].
                    exists l'; split; [ right; exact H_in' | exact H_v ]. } }
            1:{ intros [ l' [ [ E | H_in' ] H_v ] ].
                1: injection E as E; subst l'; left; exact H_v.
                1:{ right. apply (proj2 (H_a v)).
                    exists l'; split; [ exact H_in' | exact H_v ]. } } }
      Qed.

      (* What the rule needs about the set of buckets: which buckets are in
         it (both directions, since completeness reads one way and the
         subset argument the other), that they are all sets, and that there
         is at least one. *)
      Lemma In_bucket_set_inv : forall pv d l,
          In (VSet l) (bucket_set pv d) ->
          exists g, In g (trigrams pv) /\
                      l = tri_bucket (VString g) d.
      Proof.
        unfold bucket_set; intros pv d l H_in.
        apply list_to_set_incl, in_flat_map in H_in as [ gv [ H_gv [ E | [] ] ] ].
        injection E as E; subst l.
        apply list_to_set_incl, in_map_iff in H_gv as [ g [ E_g H_g ] ].
        exists g; split; [ exact H_g | rewrite E_g; reflexivity ].
      Qed.

      Lemma In_bucket_set : forall pv d g,
          In g (trigrams pv) ->
          In (VSet (tri_bucket (VString g) d)) (bucket_set pv d).
      Proof.
        unfold bucket_set; intros pv d g H_g.
        apply list_to_set_incl_r, in_flat_map.
        exists (VString g); split; [ | left; reflexivity ].
        apply list_to_set_incl_r, in_map_iff.
        exists g; split; [ reflexivity | exact H_g ].
      Qed.

      Lemma bucket_set_VSet : forall pv d,
          Forall (fun s => exists l, s = VSet l) (bucket_set pv d).
      Proof.
        intros pv d; rewrite Forall_forall; intros s H_in.
        unfold bucket_set in H_in.
        apply list_to_set_incl, in_flat_map in H_in as [ gv [ _ [ E | [] ] ] ].
        exists (tri_bucket gv d); congruence.
      Qed.

      Lemma bucket_set_not_nil : forall pv d,
          (3 <= String.length pv)%nat -> bucket_set pv d <> nil.
      Proof.
        intros pv d H_len E_nil.
        destruct (trigrams pv) as [ | g gs ] eqn:E_tg.
        1: apply (trigrams_not_nil _ H_len); exact E_tg.
        pose proof (In_bucket_set pv d g) as H.
        rewrite E_nil in H. apply H. rewrite E_tg; left; reflexivity.
      Qed.

      (* The emitted set of buckets computes the Gallina one.  The pattern is
         read in the OUTER environment -- it sits under no binder here. *)
      Lemma interp_tri_buckets :
        forall (store env : locals) (p : expr) (pv : string)
               (td : list (value * value)),
          interp_expr store env tri_e = VDict td ->
          Forall (fun e : value * value =>
                    match snd e with VSet _ => True | _ => False end) td ->
          interp_expr store env p = VString pv ->
          interp_expr store env (tri_buckets p)
          = VSet (bucket_set pv (VDict td)).
      Proof.
        intros store env p pv td E_tri H_sets E_p.
        unfold tri_buckets, bucket_set.
        rewrite interp_EFlatmap_set, interp_EUnop, interp_EUnop, E_p.
        cbn [interp_unop]. do 2 f_equal.
        apply flat_map_ext; intros gv.
        assert (H_tri' : interp_expr store (map.put env cgram gv) tri_e = VDict td).
        1:{ rewrite (interp_tbl_access_env_irrel store _ env aux_tag tri_tag).
            exact E_tri. }
        rewrite interp_EBinop, interp_EAtom.
        rewrite (interp_tri_bucket_e store _ _ gv td
                   ltac:(rewrite interp_EVar; unfold get_local;
                         rewrite map.get_put_same; reflexivity)
                   H_tri' H_sets).
        cbn [interp_atom interp_binop set_insert]. reflexivity.
      Qed.

      Lemma interp_EACIFold : forall (store env : locals) ag e,
          interp_expr store env (EACIFold ag e) =
            let '(zr, op) := interp_aci_aggr ag in
            match interp_expr store env e with
            | VSet l => fold_right op zr l
            | _ => VUnit
            end.
      Proof. reflexivity. Qed.

      (* The whole candidate set.  Under the rule's guard the bucket set is
         nonempty, so the aggregate's None branch -- the scan fallback -- is
         unreachable and the answer is always the intersection.  No seed, no
         position, and the characterization is by membership alone. *)
      Lemma interp_dyn_cands' :
        forall (store env : locals) (p : expr) (pv : string)
               (td : list (value * value)),
          interp_expr store env tri_e = VDict td ->
          Forall (fun e : value * value =>
                    match snd e with VSet _ => True | _ => False end) td ->
          interp_expr store env p = VString pv ->
          (3 <= String.length pv)%nat ->
          exists cl,
            interp_expr store env (dyn_cands' p) = VSet cl /\
              (forall v, In v cl <->
                           (forall g, In g (trigrams pv) ->
                                      In v (tri_bucket (VString g) (VDict td)))).
      Proof.
        intros store env p pv td E_tri H_sets E_p H_len.
        destruct (inter_all_chara (bucket_set pv (VDict td))
                    (bucket_set_not_nil _ _ H_len)
                    (bucket_set_VSet _ _)) as [ cl [ E_ia H_cl ] ].
        exists cl; split.
        1:{ unfold dyn_cands'.
            rewrite interp_EOptMatch, interp_EACIFold,
              (interp_tri_buckets store env p pv td E_tri H_sets E_p).
            unfold inter_all in E_ia.
            cbn [interp_aci_aggr fst snd] in E_ia |- *.
            rewrite E_ia, interp_EVar.
            unfold get_local; rewrite map.get_put_same. reflexivity. }
        1:{ intros v; rewrite H_cl; split.
            1: intros H_all g H_g; apply H_all, In_bucket_set; exact H_g.
            1:{ intros H_all l' H_in.
                apply In_bucket_set_inv in H_in as [ g [ H_g E_l ] ]; subst l'.
                apply H_all; exact H_g. } }
      Qed.

      (* ----------------------------------------------------------------
         THE THRESHOLD RULE'S CANDIDATE POOL.

         dyn_cands' narrows by intersection; this widens by union.  Same
         bucket set, same bridge, one constructor apart -- and the
         characterisation flips an "every" into a "some", which is exactly
         the difference between a substring query and a threshold one.
         ---------------------------------------------------------------- *)
      Definition thr_cands (p : expr) : expr :=
        EOptMatch (EACIFold AGUnion (tri_buckets p))
          (EAtom (AEmptySet None)) b (EVar b).

      Lemma interp_thr_cands :
        forall (store env : locals) (p : expr) (pv : string)
               (td : list (value * value)),
          interp_expr store env tri_e = VDict td ->
          Forall (fun e : value * value =>
                    match snd e with VSet _ => True | _ => False end) td ->
          interp_expr store env p = VString pv ->
          (3 <= String.length pv)%nat ->
          exists cl,
            interp_expr store env (thr_cands p) = VSet cl /\
              (forall v, In v cl <->
                           (exists g, In g (trigrams pv) /\
                                      In v (tri_bucket (VString g) (VDict td)))).
      Proof.
        intros store env p pv td E_tri H_sets E_p H_len.
        destruct (union_all_chara (bucket_set pv (VDict td))
                    (bucket_set_not_nil _ _ H_len)
                    (bucket_set_VSet _ _)) as [ cl [ E_ua H_cl ] ].
        exists cl; split.
        1:{ unfold thr_cands.
            rewrite interp_EOptMatch, interp_EACIFold,
              (interp_tri_buckets store env p pv td E_tri H_sets E_p).
            unfold union_all in E_ua.
            cbn [interp_aci_aggr fst snd] in E_ua |- *.
            rewrite E_ua, interp_EVar.
            unfold get_local; rewrite map.get_put_same. reflexivity. }
        1:{ intros v; rewrite H_cl; split.
            1:{ intros [ l' [ H_in H_v ] ].
                apply In_bucket_set_inv in H_in as [ g [ H_g E_l ] ]; subst l'.
                exists g; split; [ exact H_g | exact H_v ]. }
            1:{ intros [ g [ H_g H_v ] ].
                exists (tri_bucket (VString g) (VDict td)); split;
                  [ apply In_bucket_set; exact H_g | exact H_v ]. } }
      Qed.

      (* ----------------------------------------------------------------
         HOW MANY OF THE PATTERN'S TRIGRAMS HOLD A GIVEN KEY: the ntrue of
         gin_trgm_consistent, asked of the index rather than of the row.

         The trigrams are DEDUPLICATED, and here that is correctness and
         not the saved probe it is for the intersection: the Jaccard
         predicate counts a trigram once however often it occurs, so a
         pattern repeating one would inflate the count and admit rows the
         predicate rejects.  OSetOfList is what deduplicates.
         ---------------------------------------------------------------- *)
      (* ----------------------------------------------------------------
         THE QUERY'S TRIGRAMS, PAIRED WITH THEIR BUCKETS.

         Hoisting the trigram set took the string work out of the candidate
         filter but left the DICT LOOKUPS in it: the count still looked up
         `bucket g` for every query trigram g, once per candidate.  Those
         lookups are loop-invariant too -- the index does not change while
         the pool is being filtered -- so the emitted term binds the
         trigram PAIRED WITH ITS BUCKET, and the candidate filter only
         tests membership.

         The pairing is what makes it correct.  Hoisting a set of BUCKETS
         alone would collapse two query trigrams that happen to name the
         same keys into one element, undercounting c -- and since c is on
         the admitting side of the test, undercounting would DROP rows and
         break completeness.  Carrying the trigram in field "0" keeps the
         elements distinct, and is also what makes the map below injective,
         which is what the count's length argument rests on.
         ---------------------------------------------------------------- *)

      (* record_entry_leb compares NAMES only, so a two-field record whose
         names are literals is sorted by conversion. *)
      Lemma record_sort_zero_one : forall (a b : value),
          record_sort [("0", a); ("1", b)] = [("0", a); ("1", b)].
      Proof. reflexivity. Qed.

      Definition tri_pair (d gv : value) : value :=
        VRecord [("0", gv); ("1", VSet (tri_bucket gv d))].

      Lemma tri_pair_inj : forall d u v, tri_pair d u = tri_pair d v -> u = v.
      Proof. unfold tri_pair; intros d u v E; congruence. Qed.

      (* ---- three generic list facts.  They belong in Utils with the
         others, under the convention DictIndexImpl.v notes. ---- *)

      Lemma filter_map_comm :
        forall (A B : Type) (f : A -> B) (P : B -> bool) (l : list A),
          List.filter P (List.map f l)
          = List.map f (List.filter (fun v => P (f v)) l).
      Proof.
        intros A B f P l; induction l as [ | x l IH ];
          cbn [List.map List.filter]; [ reflexivity | ].
        destruct (P (f x)); cbn [List.map]; [ f_equal | ]; exact IH.
      Qed.

      Lemma NoDup_map_inj :
        forall (f : value -> value) (l : list value),
          (forall u v, f u = f v -> u = v) -> NoDup l -> NoDup (List.map f l).
      Proof.
        intros f l H_inj H_nd; induction H_nd as [ | x l H_notin H_nd IH ];
          cbn [List.map]; [ constructor | ].
        constructor; [ | exact IH ].
        intros H_in; apply in_map_iff in H_in as [ u [ E_u H_u ] ].
        apply H_inj in E_u; subst u; contradiction.
      Qed.

      (* list_to_set only reorders and deduplicates, so on a duplicate-free
         list it preserves the length. *)
      Lemma length_list_to_set_NoDup :
        forall l : list value,
          NoDup l -> List.length (list_to_set l) = List.length l.
      Proof.
        intros l H_nd.
        apply Permutation_length, NoDup_Permutation;
          [ apply list_to_set_NoDup | exact H_nd | ].
        intros x; split; [ apply list_to_set_incl | apply list_to_set_incl_r ].
      Qed.

      (* flat_map with a singleton body is a map *)
      Lemma flat_map_singleton :
        forall (A B : Type) (f : A -> B) (l : list A),
          flat_map (fun x => [f x]) l = List.map f l.
      Proof.
        intros A B f l; induction l as [ | x l IH ]; [ reflexivity | ].
        cbn [flat_map List.map app]; f_equal; exact IH.
      Qed.

      (* list_to_set only reorders and deduplicates, so a projection of a
         filter's survivors is the same SET whether it is taken over the
         canonicalised list or over the list itself.  The sibling is
         CollectionTransf.v's list_to_set_filter_list_to_set; this is the
         form with a projection on the survivors, which is what the
         PROJECTED count needs. *)
      Lemma list_to_set_map_filter_list_to_set :
        forall (f : value -> value) (P : value -> bool) (l : list value),
          list_to_set (List.map f (List.filter P (list_to_set l)))
          = list_to_set (List.map f (List.filter P l)).
      Proof.
        intros f P l. apply NoDup_SSorted_double_incl_eq;
          auto using list_to_set_NoDup, list_to_set_SSorted.
        - unfold incl; intros w H_in.
          apply list_to_set_incl, in_map_iff in H_in as [ u [ E_u H_u ] ].
          apply filter_In in H_u as [ H_u H_p ].
          apply list_to_set_incl in H_u.
          apply list_to_set_incl_r, in_map_iff; exists u; split;
            [ exact E_u | apply filter_In; split; assumption ].
        - unfold incl; intros w H_in.
          apply list_to_set_incl, in_map_iff in H_in as [ u [ E_u H_u ] ].
          apply filter_In in H_u as [ H_u H_p ].
          apply list_to_set_incl_r, in_map_iff; exists u; split;
            [ exact E_u | apply filter_In; split;
              [ apply list_to_set_incl_r | ]; assumption ].
      Qed.

      (* a map that acts as the identity on its elements disappears, and the
         filter's condition may be replaced pointwise at the same time *)
      Lemma map_proj_filter_pointwise :
        forall (f : value -> value) (P Q : value -> bool) (l : list value),
          (forall x, f x = x) -> (forall x, P x = Q x) ->
          List.map f (List.filter P l) = List.filter Q l.
      Proof.
        intros f P Q l H_f H_PQ; induction l as [ | x l IH ]; [ reflexivity | ].
        cbn [List.filter]; rewrite H_PQ; destruct (Q x);
          cbn [List.map]; [ rewrite H_f, IH | rewrite IH ]; reflexivity.
      Qed.

      Definition pair_set (pv : string) (d : value) : list value :=
        list_to_set
          (flat_map (fun gv => [tri_pair d gv])
             (list_to_set (List.map VString (trigrams pv)))).

      Lemma pair_set_map : forall pv d,
          pair_set pv d
          = list_to_set
              (List.map (tri_pair d) (list_to_set (List.map VString (trigrams pv)))).
      Proof. intros pv d; unfold pair_set; rewrite flat_map_singleton; reflexivity. Qed.

      (* The pair set has one element per DISTINCT trigram, which is the `a`
         of the count test. *)
      Lemma length_pair_set : forall pv d,
          List.length (pair_set pv d)
          = List.length (list_to_set (List.map VString (trigrams pv))).
      Proof.
        intros pv d; rewrite pair_set_map.
        rewrite length_list_to_set_NoDup
          by (apply NoDup_map_inj;
              [ apply tri_pair_inj | apply list_to_set_NoDup ]).
        apply length_map.
      Qed.

      Definition tri_pairs (p : expr) : expr :=
        EFlatmap LikeSet (EUnop OSetOfList (EUnop OTrigrams p)) cgram
          (EBinop OSetInsert (EAtom (AEmptySet None))
             (ERecord [("0", EVar cgram); ("1", tri_bucket_e (EVar cgram))])).

      Lemma interp_tri_pairs :
        forall (store env : locals) (p : expr) (pv : string)
               (td : list (value * value)),
          interp_expr store env tri_e = VDict td ->
          Forall (fun e : value * value =>
                    match snd e with VSet _ => True | _ => False end) td ->
          interp_expr store env p = VString pv ->
          interp_expr store env (tri_pairs p) = VSet (pair_set pv (VDict td)).
      Proof.
        intros store env p pv td E_tri H_sets E_p.
        unfold tri_pairs, pair_set.
        rewrite interp_EFlatmap_set, interp_EUnop, interp_EUnop, E_p.
        cbn [interp_unop]. do 2 f_equal.
        apply flat_map_ext; intros gv.
        assert (H_tri' : interp_expr store (map.put env cgram gv) tri_e = VDict td).
        1:{ rewrite (interp_tbl_access_env_irrel store _ env aux_tag tri_tag).
            exact E_tri. }
        assert (E_rec : interp_expr store (map.put env cgram gv)
                          (ERecord [("0", EVar cgram);
                                    ("1", tri_bucket_e (EVar cgram))])
                        = tri_pair (VDict td) gv).
        1:{ cbn [interp_expr List.map].
            rewrite record_sort_zero_one.
            unfold tri_pair; do 2 f_equal.
            1:{ f_equal. unfold get_local; rewrite map.get_put_same; reflexivity. }
            1:{ f_equal.
                rewrite <- (interp_tri_bucket_e store (map.put env cgram gv)
                              (EVar cgram) gv td
                              ltac:(rewrite interp_EVar; unfold get_local;
                                    rewrite map.get_put_same; reflexivity)
                              H_tri' H_sets).
                reflexivity. } }
        rewrite interp_EBinop, interp_EAtom, E_rec.
        cbn [interp_atom interp_binop set_insert]. reflexivity.
      Qed.

      (* ---------------------------------------------------------------
         FILTER-THEN-PROJECT ON SETS, the missing third flatmap form.

         `flatmap_filter_set` yields `EVar y`, so it cannot express a filter
         whose survivors are projected, and `flatmap_proj_set` carries no
         condition.  This is the form between them, and it BELONGS BESIDE
         THEM in FlatmapForms.v -- it is here because `thr_count_of` is its
         only user so far and moving it up rebuilds the development, the
         same reason `filter_length_mono'` is duplicated in this file.

         It matches NEITHER sibling's pattern: the yield is not a variable,
         so `flatmap_filter_set` does not see it, and the EIf means
         `flatmap_proj_set` does not either.  So no existing recognizer
         fires on it, which is the property to want here -- see the
         rule-ordering hazard about a rule that emits another's pattern. *)
      Notation flatmap_filter_proj_set e x p r t1 t2 :=
        (EFlatmap LikeSet e x
           (EIf p (EBinop OSetInsert (EAtom (AEmptySet t1)) r)
              (EAtom (AEmptySet t2)))).

      Lemma interp_flatmap_filter_proj_set :
        forall (store env : locals) e x p r t1 t2,
          interp_expr store env (flatmap_filter_proj_set e x p r t1 t2)
          = match interp_expr store env e with
            | VSet l =>
                VSet (list_to_set
                        (List.map
                           (fun v => interp_expr store (map.put env x v) r)
                           (filter
                              (fun v =>
                                 match interp_expr store (map.put env x v) p with
                                 | VBool b => b
                                 | _ => false
                                 end) l)))
            | _ => VUnit
            end.
      Proof.
        intros. cbn [interp_expr]. case_match; auto.
        do 2 f_equal.
        lazymatch goal with H : interp_expr _ _ _ = VSet _ |- _ => clear H end.
        induction l as [| v l' IH]; auto.
        cbn [flat_map filter List.map]. rewrite IH.
        (* the bool is NOT named `b` here: `b` is a section variable of this
           file, so `destruct b` picks the wrong thing.  A second case_match
           splits the `if` without naming it. *)
        case_match; auto.
        (* the bool is NOT named `b`: `b` is a section variable of this file,
           so `destruct b` as the sibling lemma writes it picks the wrong
           thing. *)
        destruct b0; cbn [interp_binop interp_atom set_insert List.map app];
          auto.
      Qed.


      (* Generalised over the SOURCE of the count, so that the emitted term
         can bind the query's deduplicated trigrams ONCE, outside the
         candidate filter, and the count can read them from a variable.

         The old form rebuilt them inside the filter body -- and twice over,
         once here and once for the `a` of the test in thr_keep -- so a pool
         of n candidates extracted the pattern's trigrams 2n times and built
         2n sets of them.  harness/compiled/authors.ml's WagtailShapes
         priced that before this was written. *)
      Definition thr_count_of (qbk : expr) : expr :=
        EUnop OSetSize
          (flatmap_filter_proj_set qbk cgram
             (EBinop OSetMem (EAccess (EVar cgram) "1") (EVar k))
             (EAccess (EVar cgram) "0") None None).


      Definition count_set (pv : string) (d kv : value) : list value :=
        list_to_set
          (filter (fun gv => set_mem kv (tri_bucket gv d))
             (list_to_set (List.map VString (trigrams pv)))).

      (* The buckets are already IN the value, so this no longer needs the
         index or its well-formedness -- the whole dependence on the store
         moved into interp_tri_pairs, which runs once per query.

         AND THE FILTER PROJECTS ITS SURVIVORS BACK TO THEIR TRIGRAM, which
         is what makes the emitted set the specification's set rather than
         an injective image of it.  The yield of a filter under OSetSize is
         unobservable -- only the cardinality is read -- so the rule is free
         to choose it, and yielding the whole pair put a COLLECTION inside a
         set element, once per candidate.  A backend that hashes sets then
         has to canonicalise the inner set to use the element as a key:
         measured at 110-184x on the generated column under `hashes`, while
         harness/compiled/authors.ml's `bucketed` pricing control -- which
         builds a set of STRINGS, i.e. this projected form -- showed none of
         it.  The projection also makes `c` literally what
         gin_trgm_consistent counts: the number of QUERY KEYS that matched. *)
      Lemma interp_thr_count_of :
        forall (store env : locals) (qbk : expr) (pv : string) (kv : value)
               (td : list (value * value)),
          cgram <> k ->
          interp_expr store env qbk = VSet (pair_set pv (VDict td)) ->
          map.get env k = Some kv ->
          interp_expr store env (thr_count_of qbk)
          = VInt (Z.of_nat (List.length (count_set pv (VDict td) kv))).
      Proof.
        intros store env qbk pv kv td H_ne E_qbk E_k.
        unfold thr_count_of, count_set.
        rewrite interp_EUnop, interp_flatmap_filter_proj_set, E_qbk.
        cbn [interp_unop].
        do 2 f_equal.
        (* the condition reads the pair's BUCKET ... *)
        assert (E_pt : forall gv,
                   match interp_expr store (map.put env cgram (tri_pair (VDict td) gv))
                           (EBinop OSetMem (EAccess (EVar cgram) "1") (EVar k)) with
                   | VBool b => b | _ => false end
                   = set_mem kv (tri_bucket gv (VDict td))).
        1:{ intros gv.
            rewrite interp_EBinop, interp_EAccess, interp_EVar, interp_EVar.
            unfold get_local.
            rewrite map.get_put_same.
            rewrite map.get_put_diff by congruence.
            rewrite E_k. cbn [tri_pair record_proj]. reflexivity. }
        (* ... and the yield projects it back to its TRIGRAM.  So the emitted
           set IS the specification's set, element for element, and the
           injective-image LENGTH argument the un-projected form needed --
           NoDup_map_inj on tri_pair_inj, then length_map -- is gone. *)
        assert (E_proj : forall gv,
                   interp_expr store (map.put env cgram (tri_pair (VDict td) gv))
                     (EAccess (EVar cgram) "0") = gv).
        1:{ intros gv.
            rewrite interp_EAccess, interp_EVar. unfold get_local.
            rewrite map.get_put_same. cbn [tri_pair record_proj]. reflexivity. }
        f_equal.
        rewrite pair_set_map, list_to_set_map_filter_list_to_set.
        rewrite filter_map_comm, map_map.
        f_equal.
        apply map_proj_filter_pointwise; intros gv;
          [ apply E_proj | apply E_pt ].
      Qed.


      (* ----------------------------------------------------------------
         THE INDEX REPORTS AT LEAST WHAT A WORD SHARES.

         The completeness argument compares two counts, and both are lengths
         of filters over the SAME list -- the query's deduplicated trigrams
         -- so nothing has to be marshalled between strings and values, and
         the pointwise implication between the two filters is the index's
         own completeness at a word.
         ---------------------------------------------------------------- *)
      Definition qtris (pv : string) : list value :=
        list_to_set (List.map VString (trigrams pv)).

      (* Belongs in Utils with the other generic list facts, under the
         convention DictIndexImpl.v notes.  It used to be duplicated in
         TrigramThreshold.v, which is gone. *)
      Lemma filter_length_mono' :
        forall (A : Type) (f g : A -> bool) (l : list A),
          (forall x, In x l -> f x = true -> g x = true) ->
          List.length (List.filter f l) <= List.length (List.filter g l).
      Proof.
        intros A f g l; induction l as [ | x l IH ]; cbn [List.filter];
          intros H_imp.
        1: cbn; lia.
        assert (H_tail : forall z, In z l -> f z = true -> g z = true)
          by (intros z H_in; apply H_imp; right; exact H_in).
        destruct (f x) eqn:E_f.
        1:{ rewrite (H_imp x (or_introl eq_refl) E_f).
            cbn [List.length]. apply le_n_S. apply IH; exact H_tail. }
        1:{ destruct (g x); cbn [List.length];
              [ apply Nat.le_le_succ_r | ]; apply IH; exact H_tail. }
      Qed.

      (* The emitted count filters a canonical set, so the coercion the
         set-level flatmap leaves on the result is the identity. *)
      Lemma count_set_canonical : forall pv d kv,
          count_set pv d kv
          = filter (fun gv => set_mem kv (tri_bucket gv d)) (qtris pv).
      Proof.
        intros pv d kv; unfold count_set, qtris.
        apply list_to_set_canonical.
        1: apply NoDup_filter, list_to_set_NoDup.
        1: apply SSorted_filter, list_to_set_SSorted.
      Qed.

      (* How many of the query's trigrams one string really shares, in the
         shape OSetIntersect computes: it filters its LEFT operand by
         membership in its right, so this is the predicate's own c. *)
      Definition shared_count (pv ws : string) : nat :=
        List.length (filter (fun gv => set_mem gv (qtris ws)) (qtris pv)).

      Lemma shared_le_count_set :
        forall (rows : list value) (pv : string) (r : value) (w : string),
          In r rows ->
          In w (words seps (TrigramIndexImpl.row_str attr r)) ->
          shared_count pv (pad w)
          <= List.length
               (count_set pv
                  (TrigramIndexImpl.tri_entries attr key seps rows)
                  (row_key key r)).
      Proof.
        intros rows pv r w H_in H_w.
        rewrite count_set_canonical; unfold shared_count.
        apply filter_length_mono'.
        intros gv _ H_has.
        apply set_mem_true_iff in H_has; unfold qtris in H_has.
        apply list_to_set_incl, in_map_iff in H_has as [ g [ E_gv H_g ] ].
        subst gv.
        apply set_mem_true_iff, key_at__In_tri_bucket.
        eapply TrigramIndexImpl.tri_lookup_complete_at_word;
          [ exact H_in | | exact H_g ].
        unfold TrigramIndexImpl.row_wrds; exact H_w.
      Qed.

      (* The trigram SET of a string, by the same extractor the index uses.
         Ex_TrigramSimilarity shows the predicate needs NO operator at all --
         a fold over a range inserting substrings -- and keeps that form
         compiled as the witness.  The rule uses OTrigrams instead, because
         pg_trgm's similarity() and its GIN index both read generate_trgm,
         so predicate and index agreeing by construction is the faithful
         arrangement rather than a convenience. *)
      Definition tri_vset (e : expr) : expr :=
        EUnop OSetOfList (EUnop OTrigrams e).

      Lemma interp_tri_vset :
        forall (store env : locals) (e : expr) (sv : string),
          interp_expr store env e = VString sv ->
          interp_expr store env (tri_vset e) = VSet (qtris sv).
      Proof.
        intros store env e sv E_e; unfold tri_vset, qtris.
        rewrite interp_EUnop, interp_EUnop, E_e.
        cbn [interp_unop]. reflexivity.
      Qed.

      Lemma filter_length_le' :
        forall (A : Type) (f : A -> bool) (l : list A),
          List.length (List.filter f l) <= List.length l.
      Proof.
        intros A f l; induction l as [ | x l IH ];
          cbn [List.filter List.length]; [ lia | ].
        destruct (f x); cbn [List.length]; lia.
      Qed.

      (* ----------------------------------------------------------------
         THE EMITTED CANDIDATE SET IS COMPLETE FOR THE PER-WORD PREDICATE.

         Given a word of the row that meets the threshold, with the counts
         read off the same value-level sets the predicate computes on, the
         row's key is in the pool AND survives the count test -- the two
         things the emitted filter asks of it.  Neither half needs the index
         to be precise, which is what makes a necessary-but-not-sufficient
         structure sound to probe, and the arithmetic is cross-multiplied
         throughout, so no division and no float appears anywhere.
         ---------------------------------------------------------------- *)
      Lemma thr_cands_complete_for_row :
        forall (rows : list value) (pv : string) (r : value) (w : string)
               (tn td aq bw cw : nat),
          In r rows ->
          In w (words seps (TrigramIndexImpl.row_str attr r)) ->
          aq = List.length (qtris pv) ->
          bw = List.length (qtris (pad w)) ->
          cw = shared_count pv (pad w) ->
          0 < tn ->
          cw <= bw ->
          0 < aq + bw - cw ->
          cw * td >= tn * (aq + bw - cw) ->
          (exists g, In g (trigrams pv) /\
                     In (row_key key r)
                       (tri_bucket (VString g)
                          (TrigramIndexImpl.tri_entries attr key seps rows)))
          /\ tn * aq
             <= List.length
                  (count_set pv
                     (TrigramIndexImpl.tri_entries attr key seps rows)
                     (row_key key r)) * td.
      Proof.
        intros rows pv r w tn td aq bw cw
               H_in H_w E_a E_b E_c H_tn H_cb H_ab H_jac.
        assert (H_ca : cw <= aq)
          by (subst aq cw; unfold shared_count; apply filter_length_le').
        (* the row shares at least one trigram, or the threshold is 0 *)
        assert (H_pos : 0 < cw).
        1:{ destruct cw as [ | cw' ]; [ | lia ].
            rewrite Nat.mul_0_l in H_jac.
            assert (H_p : 0 < tn * (aq + bw - 0))
              by (apply Nat.mul_pos_pos; lia).
            lia. }
        split.
        (* in the pool *)
        1:{ subst cw; unfold shared_count in H_pos.
            destruct (filter (fun gv => set_mem gv (qtris (pad w))) (qtris pv))
              as [ | gv rest ] eqn:E_f; [ cbn in H_pos; lia | ].
            assert (H_mem : In gv
                      (filter (fun gv => set_mem gv (qtris (pad w))) (qtris pv)))
              by (rewrite E_f; left; reflexivity).
            apply filter_In in H_mem as [ H_q H_pred ].
            apply set_mem_true_iff in H_pred; unfold qtris in H_pred.
            apply list_to_set_incl, in_map_iff in H_pred as [ g [ E_gv H_g ] ].
            subst gv.
            unfold qtris in H_q.
            apply list_to_set_incl, in_map_iff in H_q as [ g0 [ E_g0 H_g0 ] ].
            injection E_g0 as E_g0; subst g0.
            exists g; split; [ exact H_g0 | ].
            apply key_at__In_tri_bucket.
            eapply TrigramIndexImpl.tri_lookup_complete_at_word;
              [ exact H_in | | exact H_g ].
            unfold TrigramIndexImpl.row_wrds; exact H_w. }
        (* and passes the count test *)
        1:{ assert (H1 : tn * aq <= tn * (aq + bw - cw))
              by (apply Nat.mul_le_mono_l; lia).
            assert (H2 : cw * td
                         <= List.length
                              (count_set pv
                                 (TrigramIndexImpl.tri_entries attr key seps rows)
                                 (row_key key r)) * td).
            1:{ apply Nat.mul_le_mono_r. subst cw.
                apply shared_le_count_set; [ exact H_in | exact H_w ]. }
            lia. }
      Qed.

      (* ----------------------------------------------------------------
         THE EMITTED KEEP-TERM: the pool, filtered by the count test.

         This is gin_trgm_consistent's own test, and it is a STRICT
         over-approximation of the predicate -- c/a rather than
         c/(a+b-c) -- so what it returns is a candidate list and never an
         answer.  That is why the obligation discharged against it is
         completeness alone, and why the recheck is not optional.

         The test is cross-multiplied, so the threshold is an exact
         rational and no division or float appears.  The bound variable is
         k, which is what thr_count reads its key from.
         ---------------------------------------------------------------- *)
      Definition thr_keep (tn tdz : Z) (p : expr) : expr :=
        ELet (tri_pairs p) cgram
          (flatmap_filter_set (thr_cands p) k
             (EUnop ONot
                (EBinop OLess
                   (EBinop OTimes (thr_count_of (EVar cgram)) (EAtom (AInt tdz)))
                   (EBinop OTimes (EAtom (AInt tn))
                      (EUnop OSetSize (EVar cgram)))))
             k None None).

      (* The count test at the value level, on the counts the lemmas above
         produce: c * td >= tn * a with c the index's count and a the
         query's deduplicated trigram count. *)
      Definition thr_test (tn tdz : Z) (pv : string) (d kv : value) : bool :=
        negb (Z.of_nat (List.length (count_set pv d kv)) * tdz
              <? tn * Z.of_nat (List.length (qtris pv)))%Z.

      Lemma interp_thr_keep :
        forall (store env : locals) (tn tdz : Z) (p : expr) (pv : string)
               (tdict : list (value * value)),
          cgram <> k ->
          interp_expr store env tri_e = VDict tdict ->
          Forall (fun e : value * value =>
                    match snd e with VSet _ => True | _ => False end) tdict ->
          (forall kv, interp_expr store (map.put env k kv) p = VString pv) ->
          (* and under the HOISTED binder, which the emitted term now binds
             the query's deduplicated trigrams to.  The rule's guard supplies
             this the same way it supplies the one above, from
             `negb (free_immut_in cgram p0)`. *)
          (forall gv, interp_expr store (map.put env cgram gv) p = VString pv) ->
          interp_expr store env p = VString pv ->
          (3 <= String.length pv)%nat ->
          exists cl,
            interp_expr store env (thr_keep tn tdz p)
            = VSet (list_to_set
                      (filter (fun kv => thr_test tn tdz pv (VDict tdict) kv) cl))
            /\ (forall v, In v cl <->
                            (exists g, In g (trigrams pv) /\
                                       In v (tri_bucket (VString g) (VDict tdict)))).
      Proof.
        intros store env tn tdz p pv tdict H_ne E_tri H_sets E_pk E_pc E_p H_len.
        (* the hoisted binding, evaluated ONCE in the outer environment: the
           query's distinct trigrams, each already paired with its bucket *)
        assert (E_qs : interp_expr store env (tri_pairs p)
                       = VSet (pair_set pv (VDict tdict)))
          by (apply interp_tri_pairs; assumption).
        assert (E_tri1 : interp_expr store
                           (map.put env cgram (VSet (pair_set pv (VDict tdict))))
                           tri_e = VDict tdict).
        1:{ rewrite (interp_tbl_access_env_irrel store _ env aux_tag tri_tag).
            exact E_tri. }
        destruct (interp_thr_cands store
                    (map.put env cgram (VSet (pair_set pv (VDict tdict))))
                    p pv tdict E_tri1 H_sets
                    (E_pc (VSet (pair_set pv (VDict tdict)))) H_len)
          as [ cl [ E_cands H_cl ] ].
        exists cl; split; [ | exact H_cl ].
        unfold thr_keep.
        rewrite interp_ELet_step, E_qs, interp_flatmap_filter_set, E_cands.
        do 2 f_equal.
        apply filter_ext; intros kv.
        (* the count and the test's `a` BOTH read the one binding, where the
           old shape rebuilt the trigram set twice per candidate AND looked
           up every bucket again *)
        assert (E_cg : interp_expr store
                         (map.put
                            (map.put env cgram (VSet (pair_set pv (VDict tdict))))
                            k kv)
                         (EVar cgram)
                       = VSet (pair_set pv (VDict tdict))).
        1:{ rewrite interp_EVar; unfold get_local.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same. reflexivity. }
        rewrite interp_EUnop, interp_EBinop, interp_EBinop, interp_EBinop.
        rewrite (interp_thr_count_of store
                   (map.put
                      (map.put env cgram (VSet (pair_set pv (VDict tdict))))
                      k kv)
                   (EVar cgram) pv kv tdict H_ne E_cg
                   ltac:(apply map.get_put_same)).
        rewrite interp_EUnop, E_cg.
        cbn [interp_unop interp_binop apply_int_binop].
        unfold thr_test, qtris. rewrite length_pair_set. reflexivity.
      Qed.

      (* ----------------------------------------------------------------
         THE PREDICATE THE RULE MATCHES, and what one word of it computes.

         pg_trgm's padding, LPADDING 2 and RPADDING 1 with a space.  Each
         word is padded ON ITS OWN, which is what keeps any trigram from
         straddling a separator -- and therefore what keeps the index able
         to answer the predicate at all, since the index keys on exactly
         these per-word trigrams.
         ---------------------------------------------------------------- *)
      Definition padded_e (s : expr) : expr :=
        EBinop OConcatString (EAtom (AString "  "))
          (EBinop OConcatString s (EAtom (AString " "))).

      Lemma interp_padded_e :
        forall (store env : locals) (s : expr) (sv : string),
          interp_expr store env s = VString sv ->
          interp_expr store env (padded_e s) = VString (pad sv).
      Proof.
        intros store env s sv E_s; unfold padded_e, pad.
        rewrite interp_EBinop, interp_EBinop, E_s.
        cbn [interp_binop interp_expr interp_atom]. reflexivity.
      Qed.

      (* similarity(w, p) >= tn/td at ONE word, cross-multiplied:

             c * td >= tn * (a + b - c)

         with a = |T(p)|, b = |T(w)|, c = |T(p) INTERSECT T(w)|.  The
         query's set and size arrive already bound, because recomputing them
         per word would charge the scan for work no implementation does. *)
      Definition sim_body (rsv cnum : string) (tn tdz : Z) (ae : expr) : expr :=
        EUnop ONot
          (EBinop OLess
             (EBinop OTimes (EVar cnum) (EAtom (AInt tdz)))
             (EBinop OTimes (EAtom (AInt tn))
                (EBinop OMinus
                   (EBinop OPlus ae (EUnop OSetSize (EVar rsv)))
                   (EVar cnum)))).

      Definition sim_word (rsv cnum : string) (tn tdz : Z) (qe ae we : expr)
        : expr :=
        ELet (tri_vset we) rsv
          (ELet (EUnop OSetSize (EBinop OSetIntersect qe (EVar rsv))) cnum
             (sim_body rsv cnum tn tdz ae)).

      (* What the body computes once the two lets have bound: every lookup
         arrives as a hypothesis, so no put-diff reasoning is needed here. *)
      Lemma interp_sim_body :
        forall (rsv cnum : string) (store env : locals) (tn tdz : Z) (ae : expr)
               (cv : nat) (rl : list value) (av : nat),
          map.get env cnum = Some (VInt (Z.of_nat cv)) ->
          map.get env rsv = Some (VSet rl) ->
          interp_expr store env ae = VInt (Z.of_nat av) ->
          interp_expr store env (sim_body rsv cnum tn tdz ae)
          = VBool (negb (Z.of_nat cv * tdz
                         <? tn * (Z.of_nat av + Z.of_nat (List.length rl)
                                  - Z.of_nat cv))%Z).
      Proof.
        intros rsv cnum store env tn tdz ae cv rl av E_c E_r E_ae.
        unfold sim_body.
        repeat (rewrite interp_EUnop || rewrite interp_EBinop).
        rewrite E_ae, !interp_EVar, !interp_EAtom.
        unfold get_local; rewrite E_c, E_r.
        cbn [interp_unop interp_binop apply_int_binop interp_atom].
        reflexivity.
      Qed.

      (* The same test at the value level.  OSetIntersect filters its LEFT
         operand by membership in its right, so the count it computes is
         shared_count's filter exactly, which is why shared_count was
         stated in that shape rather than as a set intersection. *)
      Definition sim_test (tn tdz : Z) (pv wv : string) : bool :=
        negb (Z.of_nat (shared_count pv wv) * tdz
              <? tn * (Z.of_nat (List.length (qtris pv))
                       + Z.of_nat (List.length (qtris wv))
                       - Z.of_nat (shared_count pv wv)))%Z.

      Lemma interp_sim_word :
        forall (rsv cnum : string) (store env : locals) (tn tdz : Z)
               (qe ae we : expr) (pv wv : string),
          rsv <> cnum ->
          interp_expr store env we = VString wv ->
          (forall rv, interp_expr store (map.put env rsv rv) qe
                      = VSet (qtris pv)) ->
          (forall rv cv,
              interp_expr store (map.put (map.put env rsv rv) cnum cv) ae
              = VInt (Z.of_nat (List.length (qtris pv)))) ->
          interp_expr store env (sim_word rsv cnum tn tdz qe ae we)
          = VBool (sim_test tn tdz pv wv).
      Proof.
        intros rsv cnum store env tn tdz qe ae we pv wv H_ne E_w E_q E_a.
        assert (E_cnt : interp_expr store (map.put env rsv (VSet (qtris wv)))
                          (EUnop OSetSize (EBinop OSetIntersect qe (EVar rsv)))
                        = VInt (Z.of_nat (shared_count pv wv))).
        1:{ rewrite interp_EUnop, interp_EBinop, (E_q (VSet (qtris wv))).
            rewrite interp_EVar; unfold get_local; rewrite map.get_put_same.
            cbn [interp_binop interp_unop]. unfold shared_count. reflexivity. }
        unfold sim_word, sim_test.
        rewrite interp_ELet_step, (interp_tri_vset store env we wv E_w).
        rewrite interp_ELet_step, E_cnt.
        apply (interp_sim_body rsv cnum store _ tn tdz ae (shared_count pv wv)
                 (qtris wv) (List.length (qtris pv))).
        1: apply map.get_put_same.
        1:{ rewrite map.get_put_diff by congruence. apply map.get_put_same. }
        1: apply E_a.
      Qed.

      (* ----------------------------------------------------------------
         THE PREDICATE IS A DISJUNCTION OVER THE ROW'S WORDS.

         "Some word is similar enough" is written as a fold of OOr, and this
         says the fold computes the disjunction.  The two side conditions are
         what the rule's guard has to check: the body must not read the
         accumulator, and it must be a boolean -- OOr answers VUnit otherwise
         and the induction would not close.  Both are stated SEMANTICALLY, so
         no syntactic free-variable analysis is needed here.
         ---------------------------------------------------------------- *)
      Lemma interp_fold_or :
        forall (store env : locals) (coll : expr) (ws : list value)
               (xw xa : string) (body : expr),
          interp_expr store env coll = VList ws ->
          (forall wv av, In wv ws ->
              interp_expr store (map.put (map.put env xw wv) xa av) body
              = interp_expr store (map.put env xw wv) body) ->
          (forall wv, In wv ws -> exists bb,
              interp_expr store (map.put env xw wv) body = VBool bb) ->
          interp_expr store env
            (EFold coll (EAtom (ABool false)) xw xa
               (EBinop OOr (EVar xa) body))
          = VBool (existsb
                     (fun wv =>
                        match interp_expr store (map.put env xw wv) body with
                        | VBool bb => bb
                        | _ => false
                        end) ws).
      Proof.
        intros store env coll ws xw xa body E_coll H_fresh H_bool.
        rewrite interp_EFold, E_coll, interp_EAtom; cbn [interp_atom].
        clear E_coll.
        induction ws as [ | wv ws IH ]; cbn [fold_right existsb].
        1: reflexivity.
        assert (H_f' : forall z av, In z ws ->
                   interp_expr store (map.put (map.put env xw z) xa av) body
                   = interp_expr store (map.put env xw z) body)
          by (intros z av H_in; apply H_fresh; right; exact H_in).
        assert (H_b' : forall z, In z ws ->
                   exists bb,
                     interp_expr store (map.put env xw z) body = VBool bb)
          by (intros z H_in; apply H_bool; right; exact H_in).
        rewrite (IH H_f' H_b').
        rewrite interp_EBinop, interp_EVar.
        unfold get_local; rewrite map.get_put_same.
        rewrite H_fresh by (left; reflexivity).
        destruct (H_bool wv (or_introl eq_refl)) as [ bb E_bb ]; rewrite E_bb.
        cbn [interp_binop apply_bool_binop].
        f_equal. apply Bool.orb_comm.
      Qed.

      (* ----------------------------------------------------------------
         SOME WORD OF THE TEXT IS SIMILAR ENOUGH.

         strict_word_similarity's shape: "greatest similarity between the
         first string and any continuous extent of WORDS of the second".  At
         a single-word query the greatest is always attained at one word,
         since extending the extent only adds trigrams to the divisor, so a
         disjunction over words is the whole predicate and not an
         approximation of it.

         The query's trigram set and its size are bound OUTSIDE the fold on
         purpose.  Recomputing them per word would charge a scan for work no
         implementation does and would flatter every ratio measured against
         it.
         ---------------------------------------------------------------- *)

      (* The eleven ways the predicate's six binders have to differ, bundled
         so the lemmas take one hypothesis instead of eleven -- and so the
         rule's guard has one thing to discharge. *)
      Definition pred_binders_ok (qsv aqv rsv cnum pwrd pacc : string)
        : Prop :=
        rsv <> cnum /\ qsv <> aqv /\
        qsv <> rsv /\ qsv <> cnum /\ qsv <> pwrd /\ qsv <> pacc /\
        aqv <> rsv /\ aqv <> cnum /\ aqv <> pwrd /\ aqv <> pacc /\
        pwrd <> pacc.

      (* The eleven inequalities as a decision procedure, so the rule's guard
         can discharge pred_binders_ok from the source term alone. *)
      Definition pred_binders_okb (q a r n w c : string) : bool :=
        (negb (String.eqb r n) && negb (String.eqb q a)
         && negb (String.eqb q r) && negb (String.eqb q n)
         && negb (String.eqb q w) && negb (String.eqb q c)
         && negb (String.eqb a r) && negb (String.eqb a n)
         && negb (String.eqb a w) && negb (String.eqb a c)
         && negb (String.eqb w c))%bool.

      Lemma pred_binders_okb_ok : forall q a r n w c,
          pred_binders_okb q a r n w c = true -> pred_binders_ok q a r n w c.
      Proof.
        unfold pred_binders_okb, pred_binders_ok; intros q a r n w c H.
        rewrite !Bool.andb_true_iff in H.
        repeat match goal with H : _ /\ _ |- _ => destruct H end.
        repeat match goal with
               | H : negb (String.eqb ?u ?v) = true |- _ =>
                   apply Bool.negb_true_iff, String.eqb_neq in H
               end.
        repeat split; assumption.
      Qed.

      Definition sim_any_e (qsv aqv rsv cnum pwrd pacc : string)
        (tn tdz : Z) (text p : expr) : expr :=
        ELet (tri_vset (padded_e p)) qsv
          (ELet (EUnop OSetSize (EVar qsv)) aqv
             (EFold (EBinop OWords (EAtom (AString seps)) text)
                (EAtom (ABool false)) pwrd pacc
                (EBinop OOr (EVar pacc)
                   (sim_word rsv cnum tn tdz (EVar qsv) (EVar aqv)
                      (padded_e (EVar pwrd)))))).

      Lemma existsb_map_VString :
        forall (f : string -> bool) (l : list string),
          existsb (fun wv => match wv with
                             | VString w => f w
                             | _ => false
                             end) (List.map VString l)
          = existsb f l.
      Proof.
        intros f l; induction l as [ | w l IH ]; cbn [List.map existsb];
          [ reflexivity | rewrite IH; reflexivity ].
      Qed.

      Lemma existsb_ext_in :
        forall (A : Type) (f g : A -> bool) (l : list A),
          (forall x, In x l -> f x = g x) ->
          existsb f l = existsb g l.
      Proof.
        intros A f g l; induction l as [ | x l IH ]; cbn [existsb]; intros H;
          [ reflexivity | ].
        rewrite (H x (or_introl eq_refl)), IH;
          [ reflexivity | intros z H_in; apply H; right; exact H_in ].
      Qed.

      Lemma interp_sim_any_e :
        forall (qsv aqv rsv cnum pwrd pacc : string)
               (store env : locals) (tn tdz : Z) (text p : expr)
               (sv pv : string),
          pred_binders_ok qsv aqv rsv cnum pwrd pacc ->
          interp_expr store env p = VString pv ->
          (forall qv av,
              interp_expr store (map.put (map.put env qsv qv) aqv av) text
              = VString sv) ->
          interp_expr store env
            (sim_any_e qsv aqv rsv cnum pwrd pacc tn tdz text p)
          = VBool (existsb (fun w => sim_test tn tdz (pad pv) (pad w))
                     (words seps sv)).
      Proof.
        intros qsv aqv rsv cnum pwrd pacc store env tn tdz text p sv pv
               H_ok E_p E_text.
        destruct H_ok as [ H_rc [ H_qa [ H_qr [ H_qc [ H_qw [ H_qp
                         [ H_ar [ H_ac [ H_aw [ H_ap H_wp ] ] ] ] ] ] ] ] ] ].
        (* what one word's test computes, in any env that binds the three *)
        assert (H_body : forall (E : locals) (w : string),
                   map.get E pwrd = Some (VString w) ->
                   (forall rv, map.get (map.put E rsv rv) qsv
                               = Some (VSet (qtris (pad pv)))) ->
                   (forall rv cv,
                       map.get (map.put (map.put E rsv rv) cnum cv) aqv
                       = Some (VInt (Z.of_nat
                                       (List.length (qtris (pad pv)))))) ->
                   interp_expr store E
                     (sim_word rsv cnum tn tdz (EVar qsv) (EVar aqv)
                        (padded_e (EVar pwrd)))
                   = VBool (sim_test tn tdz (pad pv) (pad w))).
        1:{ intros E w E_w E_q E_a.
            apply (interp_sim_word rsv cnum store E tn tdz (EVar qsv) (EVar aqv)
                     (padded_e (EVar pwrd)) (pad pv) (pad w) H_rc).
            1:{ apply (interp_padded_e store E (EVar pwrd) w).
                rewrite interp_EVar; unfold get_local, get_local.
                rewrite E_w; reflexivity. }
            1:{ intros rv; rewrite interp_EVar; unfold get_local.
                rewrite (E_q rv); reflexivity. }
            1:{ intros rv cv; rewrite interp_EVar; unfold get_local.
                rewrite (E_a rv cv); reflexivity. } }
        unfold sim_any_e.
        rewrite interp_ELet_step.
        rewrite (interp_tri_vset store env (padded_e p) (pad pv)
                   (interp_padded_e store env p pv E_p)).
        rewrite interp_ELet_step.
        rewrite interp_EUnop, interp_EVar; unfold get_local.
        rewrite map.get_put_same; cbn [interp_unop].
        rewrite (interp_fold_or store _
                   (EBinop OWords (EAtom (AString seps)) text)
                   (List.map VString (words seps sv)) pwrd pacc
                   (sim_word rsv cnum tn tdz (EVar qsv) (EVar aqv)
                      (padded_e (EVar pwrd)))).
        (* the three side conditions, then the existsb *)
        4:{ intros wv H_in.
            apply in_map_iff in H_in as [ w [ E_wv _ ] ]; subst wv.
            exists (sim_test tn tdz (pad pv) (pad w)).
            apply H_body; [ apply map.get_put_same | | ];
              intros; repeat (rewrite map.get_put_diff by congruence);
              apply map.get_put_same. }
        3:{ intros wv av H_in.
            apply in_map_iff in H_in as [ w [ E_wv _ ] ]; subst wv.
            rewrite (H_body _ w), (H_body _ w); [ reflexivity | .. ];
              try apply map.get_put_same;
              intros; repeat (rewrite map.get_put_diff by congruence);
              apply map.get_put_same. }
        2:{ rewrite interp_EBinop, interp_EAtom, (E_text _ _).
            cbn [interp_atom interp_binop]. reflexivity. }
        1:{ f_equal.
            rewrite <- (existsb_map_VString
                          (fun w => sim_test tn tdz (pad pv) (pad w))).
            apply existsb_ext_in.
            intros x H_in.
            apply in_map_iff in H_in as [ w [ E_x _ ] ]; subst x.
            rewrite (H_body _ w); [ reflexivity | apply map.get_put_same | | ];
              intros; repeat (rewrite map.get_put_diff by congruence);
              apply map.get_put_same. }
      Qed.

      (* ----------------------------------------------------------------
         THE ARITHMETIC BRIDGE: from the predicate's own boolean to the
         counts thr_cands_complete_for_row asks for.

         The predicate's test is in Z, because a threshold is a literal; the
         completeness argument is in nat, because it counts list elements.
         The two agree only because the shared count never exceeds either
         side's trigram count, which is what keeps nat's truncating
         subtraction from differing from Z's.  Both of those bounds are
         proved here rather than assumed.
         ---------------------------------------------------------------- *)

      Lemma pad_length : forall s, (3 <= String.length (pad s))%nat.
      Proof.
        intros s; unfold pad; cbn [String.length String.append].
        destruct s; cbn [String.length String.append]; lia.
      Qed.

      (* A padded string always has a trigram, so the query's count is
         positive -- which is what makes a + b - c positive, and so what
         keeps the threshold inequality from holding vacuously. *)
      Lemma qtris_pos : forall s,
          (3 <= String.length s)%nat -> 0 < List.length (qtris s).
      Proof.
        intros s H_len.
        destruct (trigrams s) as [ | g gs ] eqn:E_tg.
        1: exfalso; apply (trigrams_not_nil _ H_len); exact E_tg.
        destruct (qtris s) as [ | v vs ] eqn:E_q; cbn [List.length]; [ | lia ].
        exfalso.
        pose proof (list_to_set_incl_r (List.map VString (trigrams s))
                      (VString g)) as H.
        unfold qtris in E_q; rewrite E_q in H.
        apply H, in_map. rewrite E_tg; left; reflexivity.
      Qed.

      (* The shared count is bounded by BOTH trigram counts.  The left bound
         is a filter shrinking its list; the right one needs the query's set
         to be duplicate-free, since it maps the survivors injectively into
         the word's set. *)
      Lemma shared_le_left : forall pv ws,
          shared_count pv ws <= List.length (qtris pv).
      Proof.
        intros pv ws; unfold shared_count; apply filter_length_le'.
      Qed.

      Lemma shared_le_right : forall pv ws,
          shared_count pv ws <= List.length (qtris ws).
      Proof.
        intros pv ws; unfold shared_count.
        apply NoDup_incl_length.
        1: apply NoDup_filter; unfold qtris; apply list_to_set_NoDup.
        1:{ intros x H_in; apply filter_In in H_in as [ _ H_mem ].
            apply set_mem_true_iff in H_mem; exact H_mem. }
      Qed.

      Lemma sim_test_true__nat :
        forall (tnn tdn : nat) (pv ws : string),
          sim_test (Z.of_nat tnn) (Z.of_nat tdn) pv ws = true ->
          shared_count pv ws * tdn
          >= tnn * (List.length (qtris pv) + List.length (qtris ws)
                    - shared_count pv ws).
      Proof.
        intros tnn tdn pv ws H.
        unfold sim_test in H.
        apply Bool.negb_true_iff, Z.ltb_ge in H.
        pose proof (shared_le_left pv ws) as H_ca.
        pose proof (shared_le_right pv ws) as H_cb.
        lia.
      Qed.

      (* And the bridge itself: a word of the row passing the predicate puts
         the row's key in the emitted pool and past the emitted count test. *)
      Theorem sim_word_true__thr_complete :
        forall (rows : list value) (r : value) (pv w : string)
               (tnn tdn : nat),
          In r rows ->
          In w (words seps (TrigramIndexImpl.row_str attr r)) ->
          sim_test (Z.of_nat tnn) (Z.of_nat tdn) (pad pv) (pad w) = true ->
          0 < tnn ->
          (exists g, In g (trigrams (pad pv)) /\
                     In (row_key key r)
                       (tri_bucket (VString g)
                          (TrigramIndexImpl.tri_entries attr key seps rows)))
          /\ tnn * List.length (qtris (pad pv))
             <= List.length
                  (count_set (pad pv)
                     (TrigramIndexImpl.tri_entries attr key seps rows)
                     (row_key key r)) * tdn.
      Proof.
        intros rows r pv w tnn tdn H_in H_w H_test H_tn.
        pose proof (shared_le_right (pad pv) (pad w)) as H_cb.
        pose proof (qtris_pos (pad pv) (pad_length pv)) as H_aq.
        apply (thr_cands_complete_for_row rows (pad pv) r w tnn tdn
                 (List.length (qtris (pad pv)))
                 (List.length (qtris (pad w)))
                 (shared_count (pad pv) (pad w)));
          [ exact H_in | exact H_w | reflexivity | reflexivity | reflexivity
          | exact H_tn | exact H_cb | lia | ].
        apply sim_test_true__nat; exact H_test.
      Qed.

      (* ----------------------------------------------------------------
         THE EMITTED RECHECK.

         probe_from with the threshold predicate in place of OStrContains:
         turn each candidate key back into its row, and keep the row only if
         it really passes.  Like the substring recheck this needs NO typing
         hypothesis -- a row whose attribute is not a string makes the fold
         over words fold over nothing, so the predicate is not a boolean, the
         EIf yields VUnit, and a non-set body contributes nothing.  That is
         the same reason contains_test needed none.
         ---------------------------------------------------------------- *)
      Definition sim_row_test (tn tdz : Z) (pv : string) (r : value) : bool :=
        match row_key attr r with
        | VString s => existsb (fun w => sim_test tn tdz (pad pv) (pad w))
                         (words seps s)
        | _ => false
        end.

      Definition thr_probe (qsv aqv rsv cnum pwrd pacc : string)
        (tn tdz : Z) (cand p : expr) : expr :=
        EFlatmap LikeSet cand k
          (EOptMatch (EBinop OLookup pk_e (EVar k)) (EAtom (AEmptySet None))
             y (EIf (sim_any_e qsv aqv rsv cnum pwrd pacc tn tdz
                       (EAccess (EVar y) attr) p)
                  (EBinop OSetInsert (EAtom (AEmptySet None)) (EVar y))
                  (EAtom (AEmptySet None)))).

      (* Off a non-string the predicate is not a boolean.  Stated at the
         VALUE the text takes, so the caller destructs once and this covers
         every non-string case at a stroke. *)
      Lemma interp_sim_any_e_unit :
        forall (qsv aqv rsv cnum pwrd pacc : string)
               (store env : locals) (tn tdz : Z) (text p : expr) (tv : value),
          (forall qv av,
              interp_expr store (map.put (map.put env qsv qv) aqv av) text = tv) ->
          (forall s, tv <> VString s) ->
          interp_expr store env
            (sim_any_e qsv aqv rsv cnum pwrd pacc tn tdz text p) = VUnit.
      Proof.
        intros qsv aqv rsv cnum pwrd pacc store env tn tdz text p tv
               E_text H_ns.
        unfold sim_any_e.
        rewrite interp_ELet_step, interp_ELet_step, interp_EFold,
          interp_EBinop, interp_EAtom, (E_text _ _).
        cbn [interp_atom].
        destruct tv as [ | | s | | | | | | | ]; cbn [interp_binop];
          try reflexivity.
        exfalso; apply (H_ns s); reflexivity.
      Qed.

      Lemma interp_thr_probe :
        forall (qsv aqv rsv cnum pwrd pacc : string)
               (store env : locals) (tn tdz : Z) (cand p : expr)
               (cl : list value) (pv : string) (pd : list (value * value)),
          pred_binders_ok qsv aqv rsv cnum pwrd pacc ->
          y <> qsv -> y <> aqv ->
          interp_expr store env cand = VSet cl ->
          (forall (v r : value),
              interp_expr store (map.put (map.put env k v) y r) p = VString pv) ->
          interp_expr store env pk_e = VDict pd ->
          interp_expr store env
            (thr_probe qsv aqv rsv cnum pwrd pacc tn tdz cand p)
          = VSet (list_to_set
                    (flat_map
                       (fun kk =>
                          match dict_lookup kk pd with
                          | Some r =>
                              if sim_row_test tn tdz pv r then [r] else nil
                          | None => nil
                          end)
                       cl)).
      Proof.
        intros qsv aqv rsv cnum pwrd pacc store env tn tdz cand p cl pv pd
               H_ok H_yq H_ya E_cand E_p E_pk.
        unfold thr_probe.
        rewrite interp_EFlatmap_set, E_cand; cbv beta iota.
        apply (f_equal (fun z : list value => VSet (list_to_set z))).
        apply flat_map_pointwise; intros v.
        rewrite interp_EOptMatch, interp_EBinop.
        rewrite (interp_tbl_access_env_irrel store (map.put env k v) env
                   aux_tag pk_tag).
        rewrite E_pk, interp_EVar.
        unfold get_local; rewrite map.get_put_same.
        cbn [interp_binop].
        destruct (dict_lookup v pd) as [ r | ].
        2:{ rewrite interp_EAtom; cbn [interp_atom]; reflexivity. }
        assert (E_acc : forall qv av,
                   interp_expr store
                     (map.put (map.put (map.put (map.put env k v) y r) qsv qv)
                        aqv av)
                     (EAccess (EVar y) attr)
                   = row_key attr r).
        1:{ intros qv av.
            rewrite interp_EAccess, interp_EVar; unfold get_local.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same.
            unfold row_key. reflexivity. }
        rewrite interp_EIf. unfold sim_row_test.
        destruct (row_key attr r) as [ | | s | | | | | | | ].
        3:{ rewrite (interp_sim_any_e qsv aqv rsv cnum pwrd pacc store _ tn tdz
                       (EAccess (EVar y) attr) p s pv H_ok (E_p v r) E_acc).
            destruct (existsb (fun w => sim_test tn tdz (pad pv) (pad w))
                        (words seps s)).
            1:{ rewrite interp_EBinop, interp_EAtom, interp_EVar.
                unfold get_local; rewrite map.get_put_same.
                cbn [interp_atom interp_binop set_insert]. reflexivity. }
            1:{ rewrite interp_EAtom; cbn [interp_atom]; reflexivity. } }
        all: rewrite (interp_sim_any_e_unit qsv aqv rsv cnum pwrd pacc store _
                        tn tdz (EAccess (EVar y) attr) p _ E_acc)
               by (intros s'; discriminate).
        all: reflexivity.
      Qed.

      (* And the bridge: at the primary-key index of a table, the recheck IS
         probe_body_t at the threshold test, so probe_recheck_cands_eq_t
         applies to it unchanged.  That lemma asks only for completeness of
         the candidate list, which is why generalising it over the test was
         worth doing rather than copying it. *)
      Lemma interp_thr_probe_as_probe_body :
        forall (qsv aqv rsv cnum pwrd pacc : string)
               (store env : locals) (tn tdz : Z) (cand p : expr)
               (cl rows : list value) (pv : string),
          pred_binders_ok qsv aqv rsv cnum pwrd pacc ->
          y <> qsv -> y <> aqv ->
          interp_expr store env cand = VSet cl ->
          (forall (v r : value),
              interp_expr store (map.put (map.put env k v) y r) p = VString pv) ->
          interp_expr store env pk_e
          = VDict (UniqueDictIndexImpl.idx_entries key rows) ->
          interp_expr store env
            (thr_probe qsv aqv rsv cnum pwrd pacc tn tdz cand p)
          = VSet (list_to_set
                    (flat_map
                       (probe_body_t key (sim_row_test tn tdz pv) rows) cl)).
      Proof.
        intros qsv aqv rsv cnum pwrd pacc store env tn tdz cand p cl rows pv
               H_ok H_yq H_ya E_cand E_p E_pk.
        rewrite (interp_thr_probe qsv aqv rsv cnum pwrd pacc store env tn tdz
                   cand p cl pv _ H_ok H_yq H_ya E_cand E_p E_pk).
        reflexivity.
      Qed.

      (* ----------------------------------------------------------------
         TYPING THE PREDICATE.

         preserve_ty needs this because the rewrite RE-EMITS the source's own
         predicate, under the recheck's binder rather than the scan's.  The
         binder names come from the source term, not from this section, so
         every lookup below is justified by pred_binders_ok rather than by a
         section hypothesis -- which is what lets the rule fire whatever the
         author called their own variables.
         ---------------------------------------------------------------- *)
      Lemma padded_e_ty : forall (Gstore Genv : tenv) s,
          type_of Gstore Genv s TString ->
          type_of Gstore Genv (padded_e s) TString.
      Proof.
        intros * H_s; unfold padded_e.
        eapply TyEBinop; [ apply TyOConcatString | apply TyEAtom, TyAString | ].
        eapply TyEBinop; [ apply TyOConcatString | exact H_s | ].
        apply TyEAtom, TyAString.
      Qed.

      Lemma tri_vset_ty : forall (Gstore Genv : tenv) e,
          type_of Gstore Genv e TString ->
          type_of Gstore Genv (tri_vset e) (TSet TString).
      Proof.
        intros * H_e; unfold tri_vset.
        eapply TyEUnop; [ apply TyOSetOfList | ].
        eapply TyEUnop; [ apply TyOTrigrams | exact H_e ].
      Qed.

      Lemma sim_word_ty :
        forall (rsv0 cnum0 : string) (Gstore Genv : tenv) (tn tdz : Z)
               (qe ae we : expr),
          rsv0 <> cnum0 ->
          type_of Gstore Genv we TString ->
          type_of Gstore (map.put Genv rsv0 (TSet TString)) qe (TSet TString) ->
          type_of Gstore (map.put (map.put Genv rsv0 (TSet TString)) cnum0 TInt)
            ae TInt ->
          type_of Gstore Genv (sim_word rsv0 cnum0 tn tdz qe ae we) TBool.
      Proof.
        intros * H_ne H_we H_qe H_ae; unfold sim_word, sim_body.
        eapply TyELet; [ apply tri_vset_ty; exact H_we | ].
        eapply TyELet.
        1:{ eapply TyEUnop; [ apply TyOSetSize | ].
            eapply TyEBinop; [ apply TyOSetIntersect | exact H_qe | ].
            apply TyEVar; rewrite map.get_put_same; reflexivity. }
        eapply TyEUnop; [ apply TyONot | ].
        eapply TyEBinop; [ apply TyOLess | | ].
        1:{ eapply TyEBinop; [ apply TyOTimes | | apply TyEAtom, TyAInt ].
            apply TyEVar; rewrite map.get_put_same; reflexivity. }
        eapply TyEBinop; [ apply TyOTimes | apply TyEAtom, TyAInt | ].
        eapply TyEBinop; [ apply TyOMinus | | ].
        1:{ eapply TyEBinop; [ apply TyOPlus | exact H_ae | ].
            eapply TyEUnop; [ apply TyOSetSize | ].
            apply TyEVar.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same; reflexivity. }
        apply TyEVar; rewrite map.get_put_same; reflexivity.
      Qed.

      Lemma sim_any_e_ty :
        forall (qsv0 aqv0 rsv0 cnum0 pwrd0 pacc0 : string)
               (Gstore Genv : tenv) (tn tdz : Z) (text p : expr),
          pred_binders_ok qsv0 aqv0 rsv0 cnum0 pwrd0 pacc0 ->
          type_of Gstore Genv p TString ->
          type_of Gstore (map.put (map.put Genv qsv0 (TSet TString)) aqv0 TInt)
            text TString ->
          type_of Gstore Genv
            (sim_any_e qsv0 aqv0 rsv0 cnum0 pwrd0 pacc0 tn tdz text p) TBool.
      Proof.
        intros * H_ok H_p H_text.
        destruct H_ok as [ H_rc [ H_qa [ H_qr [ H_qc [ H_qw [ H_qp
                         [ H_ar [ H_ac [ H_aw [ H_ap H_wp ] ] ] ] ] ] ] ] ] ].
        unfold sim_any_e.
        eapply TyELet; [ apply tri_vset_ty, padded_e_ty; exact H_p | ].
        eapply TyELet.
        1:{ eapply TyEUnop; [ apply TyOSetSize | ].
            apply TyEVar; rewrite map.get_put_same; reflexivity. }
        eapply TyEFold.
        1:{ eapply TyEBinop;
              [ apply TyOWords | apply TyEAtom, TyAString | exact H_text ]. }
        1: apply TyEAtom, TyABool.
        eapply TyEBinop; [ apply TyOOr | | ].
        1: apply TyEVar; rewrite map.get_put_same; reflexivity.
        eapply sim_word_ty; [ exact H_rc | | | ].
        1:{ apply padded_e_ty, TyEVar.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same; reflexivity. }
        1:{ apply TyEVar.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same; reflexivity. }
        1:{ apply TyEVar.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same; reflexivity. }
      Qed.

      (* ----------------------------------------------------------------
         READING THE PREDICATE OFF THE TERM.

         The predicate is a twenty-five level term, and matching it inside
         the rule's own pattern makes destruct_subexpr search a space it
         cannot afford: every expr left in the context is a candidate to
         destruct, each branching fifteen ways, and the surviving-goal
         discipline backtracks across all of them.  So the shape is decided
         HERE, by a function, and the rule's pattern stays as shallow as
         every other rule's.

         Everything internal to the predicate is checked here too -- the
         padding literals, the separators, that each binder's occurrences
         agree, and that different binders differ -- so the Some case yields
         exactly the two facts the rule needs: the term IS sim_any_e, and
         its binders are distinct.
         ---------------------------------------------------------------- *)
      Definition parse_sim_any (e : expr)
        : option (string * string * string * string * string * string
                  * Z * Z * string * string * expr) :=
        match e with
        | ELet (EUnop OSetOfList (EUnop OTrigrams
                  (EBinop OConcatString (EAtom (AString lp0))
                     (EBinop OConcatString p0 (EAtom (AString rp0)))))) q0
            (ELet (EUnop OSetSize (EVar q1)) a0
               (EFold (EBinop OWords (EAtom (AString sp0))
                         (EAccess (EVar x1) attr0))
                  (EAtom (ABool false)) w0 c0
                  (EBinop OOr (EVar c1)
                     (ELet (EUnop OSetOfList (EUnop OTrigrams
                              (EBinop OConcatString (EAtom (AString lp1))
                                 (EBinop OConcatString (EVar w1)
                                    (EAtom (AString rp1)))))) r0
                        (ELet (EUnop OSetSize
                                 (EBinop OSetIntersect (EVar q2) (EVar r1)))
                           n0
                           (EUnop ONot
                              (EBinop OLess
                                 (EBinop OTimes (EVar n1) (EAtom (AInt tdz0)))
                                 (EBinop OTimes (EAtom (AInt tn0))
                                    (EBinop OMinus
                                       (EBinop OPlus (EVar a1)
                                          (EUnop OSetSize (EVar r2)))
                                       (EVar n2)))))))))) =>
            if (all_eqb [(q0, [q1; q2]); (a0, [a1]); (r0, [r1; r2]);
                         (n0, [n1; n2]); (w0, [w1]); (c0, [c1]);
                         (seps, [sp0]); (lp0, ["  "]); (lp1, ["  "]);
                         (rp0, [" "]); (rp1, [" "])]
                && pred_binders_okb q0 a0 r0 n0 w0 c0)%bool
            then Some (q0, a0, r0, n0, w0, c0, tn0, tdz0, x1, attr0, p0)
            else None
        | _ => None
        end.

      Lemma parse_sim_any_Some :
        forall e q a r n w c tn tdz x1 attr0 p,
          parse_sim_any e = Some (q, a, r, n, w, c, tn, tdz, x1, attr0, p) ->
          e = sim_any_e q a r n w c tn tdz (EAccess (EVar x1) attr0) p
          /\ pred_binders_ok q a r n w c.
      Proof.
        intros e q a r n w c tn tdz x1 attr0 p H.
        unfold parse_sim_any in H.
        (* destruct_match_hyp takes the scrutinee of whatever match is in H
           and records the equation under a fresh name, so this walks the
           term one constructor at a time with no search over the context --
           unlike destruct_subexpr, which would consider every expr in
           scope.  That is the whole reason the shape is decided by a
           function rather than inside the rule's own pattern. *)
        repeat (destruct_match_hyp; try discriminate).
        injection H; intros; subst.
        lazymatch goal with
        | Hg : (all_eqb _ && pred_binders_okb _ _ _ _ _ _)%bool = true |- _ =>
            rewrite Bool.andb_true_iff in Hg; destruct Hg as [ E_eq E_ok ]
        end.
        cbn [all_eqb all_eqb' andb] in E_eq.
        repeat rewrite Bool.andb_true_iff in E_eq.
        repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
        repeat (rewrite eqb_eq in *; subst).
        split; [ reflexivity | apply pred_binders_okb_ok; exact E_ok ].
      Qed.

      (* The one typing fact the rule needs out of the source's predicate.

         Proved by FIVE targeted inversions rather than by repeat
         invert_type_of_clear: that tactic inverts the first typing
         hypothesis it finds and substitutes across the whole context, so
         repeating it on a twenty-five level predicate inverts the entire
         derivation and costs minutes.  Each peel below names the subterm it
         is about, so nothing else is touched. *)
      Lemma sim_any_e_ty_inv :
        forall (q a r n w c : string) (Gstore Genv : tenv) (tn tdz : Z)
               (text p : expr) (t : type),
          type_of Gstore Genv (sim_any_e q a r n w c tn tdz text p) t ->
          type_of Gstore Genv p TString.
      Proof.
        intros q a r n w c Gstore Genv tn tdz text p t H.
        unfold sim_any_e, tri_vset, padded_e in H.
        lazymatch goal with
        | H0 : type_of _ _ (ELet _ _ _) _ |- _ =>
            inversion H0; clear H0; subst
        end.
        lazymatch goal with
        | H0 : type_of _ _ (EUnop OSetOfList _) _ |- _ =>
            inversion H0; clear H0; subst
        end.
        lazymatch goal with
        | H0 : type_of _ _ (EUnop OTrigrams _) _ |- _ =>
            inversion H0; clear H0; subst
        end.
        lazymatch goal with
        | H0 : type_of _ _ (EBinop OConcatString (EAtom (AString _)) _) _ |- _ =>
            inversion H0; clear H0; subst
        end.
        lazymatch goal with
        | H0 : type_of _ _ (EBinop OConcatString p _) _ |- _ =>
            inversion H0; clear H0; subst
        end.
        (* the operator premises say what the argument types were; these are
           cheap, since an op typing has no subterms to recurse into *)
        repeat invert_type_of_op_clear.
        assumption.
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
         soundness obligation, not a heuristic: probe_recheck_all_eq does not
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


      (* ==================================================================
         The all-trigram rule, guarded.

         This is the one the pipeline installs: the pattern is a variable,
         so its trigrams are not known until run time and the chain of
         intersections is a fold over its own positions.  Everything else is
         the guarded rule above -- same shape, same runtime length test,
         same fallback to the scan, same recheck.

         The pattern is read under probe_from's two binders, so it must not
         mention them.  It is read under NO binder of the candidate set --
         the aggregate has no accumulator and the pattern sits outside the
         flatmap's binder -- so the two freshness conditions the positional
         fold needed for cpos and cacc are gone.
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
                && negb (free_immut_in y p))%bool
            then EIf (pattern_has_trigram p) (probe_from (dyn_cands' p) p) e
            else e
        | _ => e
        end.

      Lemma dyn_cands'_ty : forall (Gstore Genv : tenv) tl ctl kt p,
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (TDict Unranged TString (TSet kt)) ->
          type_wf kt ->
          type_of Gstore Genv p TString ->
          type_of Gstore Genv (dyn_cands' p) (TSet kt).
      Proof.
        intros * E_tbl E_aux E_tri H_ktwf H_p.
        assert (H_skwf : type_wf (TSet kt)) by (constructor; exact H_ktwf).
        unfold dyn_cands'.
        eapply TyEOptMatch with (t1 := TSet kt).
        1:{ eapply TyEACIFold; [ apply TyAGIntersect | ].
            unfold tri_buckets.
            eapply TyEFlatmap_Set with (t1 := TString).
            1:{ eapply TyEUnop; [ apply TyOSetOfList | ].
                eapply TyEUnop; [ apply TyOTrigrams | exact H_p ]. }
            1:{ eapply TyEBinop; [ apply TyOSetInsert | | ].
                1: apply TyEAtom; apply TyAEmptySet'; exact H_skwf.
                1:{ eapply tri_bucket_e_ty;
                      [ exact E_tbl | exact E_aux | exact E_tri | exact H_ktwf | ].
                    apply TyEVar; rewrite map.get_put_same; reflexivity. } } }
        1: apply TyEAtom; apply TyAEmptySet'; exact H_ktwf.
        1: apply TyEVar; rewrite map.get_put_same; reflexivity.
      Qed.

      (* ----------------------------------------------------------------
         TYPING THE EMITTED TERMS.

         thr_cands is dyn_cands' with one constructor changed, so its typing
         is that proof with TyAGUnion in place of TyAGIntersect.  The count
         and the keep-term both read the candidate key out of k, so both ask
         the environment for it -- which is also why k is the keep-term's own
         binder rather than a fresh one.
         ---------------------------------------------------------------- *)
      Lemma thr_cands_ty : forall (Gstore Genv : tenv) tl ctl kt p,
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (TDict Unranged TString (TSet kt)) ->
          type_wf kt ->
          type_of Gstore Genv p TString ->
          type_of Gstore Genv (thr_cands p) (TSet kt).
      Proof.
        intros * E_tbl E_aux E_tri H_ktwf H_p.
        assert (H_skwf : type_wf (TSet kt)) by (constructor; exact H_ktwf).
        unfold thr_cands.
        eapply TyEOptMatch with (t1 := TSet kt).
        1:{ eapply TyEACIFold; [ apply TyAGUnion | ].
            unfold tri_buckets.
            eapply TyEFlatmap_Set with (t1 := TString).
            1:{ eapply TyEUnop; [ apply TyOSetOfList | ].
                eapply TyEUnop; [ apply TyOTrigrams | exact H_p ]. }
            1:{ eapply TyEBinop; [ apply TyOSetInsert | | ].
                1: apply TyEAtom; apply TyAEmptySet'; exact H_skwf.
                1:{ eapply tri_bucket_e_ty;
                      [ exact E_tbl | exact E_aux | exact E_tri | exact H_ktwf | ].
                    apply TyEVar; rewrite map.get_put_same; reflexivity. } } }
        1: apply TyEAtom; apply TyAEmptySet'; exact H_ktwf.
        1: apply TyEVar; rewrite map.get_put_same; reflexivity.
      Qed.

      (* The element type of the hoisted set: a query trigram beside the
         bucket it names. *)
      Notation pair_ty kt := (TRecord [("0", TString); ("1", TSet kt)]).

      Lemma pair_ty_wf : forall kt,
          type_wf kt -> type_wf (pair_ty kt).
      Proof.
        intros kt H_wf; constructor; cbn [List.map fst snd].
        1:{ repeat constructor; cbn [In]; intuition discriminate. }
        1:{ repeat constructor; reflexivity. }
        1:{ repeat constructor; exact H_wf. }
      Qed.

      Lemma tri_pairs_ty : forall (Gstore Genv : tenv) tl ctl kt p,
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (TDict Unranged TString (TSet kt)) ->
          type_wf kt ->
          type_of Gstore Genv p TString ->
          type_of Gstore Genv (tri_pairs p) (TSet (pair_ty kt)).
      Proof.
        intros * E_tbl E_aux E_tri H_ktwf H_p.
        unfold tri_pairs.
        eapply TyEFlatmap_Set with (t1 := TString).
        1:{ eapply TyEUnop; [ apply TyOSetOfList | ].
            eapply TyEUnop; [ apply TyOTrigrams | exact H_p ]. }
        eapply TyEBinop; [ apply TyOSetInsert | | ].
        1: apply TyEAtom; apply TyAEmptySet'; apply pair_ty_wf; exact H_ktwf.
        eapply TyERecord with (tl := [("0", TString); ("1", TSet kt)]).
        1: reflexivity.
        1:{ cbn [List.map snd]. constructor.
            1: apply TyEVar; apply map.get_put_same.
            constructor; [ | constructor ].
            eapply tri_bucket_e_ty;
              [ exact E_tbl | exact E_aux | exact E_tri | exact H_ktwf | ].
            apply TyEVar; apply map.get_put_same. }
        1: apply Permutation_refl.
        1:{ cbn [List.map fst]. repeat constructor; cbn [In];
            intuition discriminate. }
        1:{ repeat constructor; reflexivity. }
      Qed.

      Lemma thr_count_of_ty : forall (Gstore Genv : tenv) kt qbk,
          cgram <> k ->
          type_wf kt ->
          map.get Genv k = Some kt ->
          type_of Gstore Genv qbk (TSet (pair_ty kt)) ->
          type_of Gstore Genv (thr_count_of qbk) TInt.
      Proof.
        intros * H_ne H_ktwf E_k H_qbk.
        unfold thr_count_of.
        eapply TyEUnop; [ apply TyOSetSize | ].
        (* the SOURCE is still a set of pairs; only the RESULT is now a set
           of the trigrams themselves, so the empty sets below are at
           TString and no longer need pair_ty_wf *)
        eapply TyEFlatmap_Set with (t1 := pair_ty kt).
        1: exact H_qbk.
        eapply TyEIf.
        1:{ eapply TyEBinop; [ apply TyOSetMem | | ].
            1:{ eapply TyEAccess;
                  [ apply TyEVar; apply map.get_put_same | reflexivity ]. }
            1:{ apply TyEVar; rewrite map.get_put_diff by congruence; exact E_k. } }
        (* the ELEMENT first, for the reason the old shape needed too: it
           fixes the set's type, so the empty set's type_wf goal is
           concrete rather than an open metavariable. *)
        1:{ eapply TyEBinop; [ apply TyOSetInsert | | ].
            2:{ eapply TyEAccess;
                  [ apply TyEVar; apply map.get_put_same | reflexivity ]. }
            1: apply TyEAtom; apply TyAEmptySet'; apply WFTString. }
        1: apply TyEAtom; apply TyAEmptySet'; apply WFTString.
      Qed.

      Lemma thr_keep_ty : forall (Gstore Genv : tenv) tl ctl kt tn tdz p,
          cgram <> k ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (TDict Unranged TString (TSet kt)) ->
          type_wf kt ->
          type_of Gstore Genv p TString ->
          type_of Gstore (map.put Genv cgram (TSet (pair_ty kt))) p TString ->
          type_of Gstore Genv (thr_keep tn tdz p) (TSet kt).
      Proof.
        intros * H_ne E_tbl E_aux E_tri H_ktwf H_p H_pc.
        unfold thr_keep.
        eapply TyELet;
          [ eapply tri_pairs_ty;
            [ exact E_tbl | exact E_aux | exact E_tri | exact H_ktwf | exact H_p ]
          | ].
        eapply TyEFlatmap_Set with (t1 := kt).
        1:{ eapply thr_cands_ty;
              [ exact E_tbl | exact E_aux | exact E_tri | exact H_ktwf | exact H_pc ]. }
        eapply TyEIf.
        1:{ eapply TyEUnop; [ apply TyONot | ].
            eapply TyEBinop; [ apply TyOLess | | ].
            1:{ eapply TyEBinop; [ apply TyOTimes | | apply TyEAtom, TyAInt ].
                eapply thr_count_of_ty;
                  [ exact H_ne | exact H_ktwf | apply map.get_put_same | ].
                apply TyEVar; rewrite map.get_put_diff by congruence.
                apply map.get_put_same. }
            1:{ eapply TyEBinop; [ apply TyOTimes | apply TyEAtom, TyAInt | ].
                eapply TyEUnop; [ apply TyOSetSize | ].
                apply TyEVar; rewrite map.get_put_diff by congruence.
                apply map.get_put_same. } }
        1:{ eapply TyEBinop; [ apply TyOSetInsert | | ].
            1: apply TyEAtom; apply TyAEmptySet'; exact H_ktwf.
            1: apply TyEVar; rewrite map.get_put_same; reflexivity. }
        1: apply TyEAtom; apply TyAEmptySet'; exact H_ktwf.
      Qed.

      (* The recheck's type: a set of the table's rows.  The predicate is
         typed by sim_any_e_ty under the recheck's own binder, which is the
         whole point of having parameterised it over the source's names. *)
      Lemma thr_probe_ty :
        forall (q a r n w c : string) (Gstore Genv : tenv) tl ctl rt kt
               (tn tdz : Z) (cand p : expr),
          pred_binders_ok q a r n w c ->
          y <> q -> y <> a ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl pk_tag = Success (TDict Unranged kt (TRecord rt)) ->
          access_record rt attr = Success TString ->
          type_wf (TRecord rt) ->
          type_of Gstore Genv cand (TSet kt) ->
          type_of Gstore (map.put (map.put Genv k kt) y (TRecord rt)) p TString ->
          type_of Gstore Genv (thr_probe q a r n w c tn tdz cand p)
            (TSet (TRecord rt)).
      Proof.
        intros * H_ok H_yq H_ya E_tbl E_aux E_pk H_attr H_rtwf H_cand H_p.
        unfold thr_probe.
        eapply TyEFlatmap_Set with (t1 := kt); [ exact H_cand | ].
        eapply TyEOptMatch with (t1 := TRecord rt).
        1:{ eapply TyEBinop; [ apply TyOLookup | | ].
            1:{ eapply TyEAccess;
                [ eapply TyEAccess; [ apply TyELoc; exact E_tbl | exact E_aux ]
                | exact E_pk ]. }
            1: apply TyEVar; rewrite map.get_put_same; reflexivity. }
        1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf.
        eapply TyEIf.
        1:{ eapply sim_any_e_ty; [ exact H_ok | exact H_p | ].
            eapply TyEAccess; [ | exact H_attr ].
            apply TyEVar.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            apply map.get_put_same. }
        1:{ eapply TyEBinop; [ apply TyOSetInsert | | ].
            2: apply TyEVar; rewrite map.get_put_same; reflexivity.
            1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf. }
        1: apply TyEAtom; apply TyAEmptySet'; exact H_rtwf.
      Qed.

      (* ----------------------------------------------------------------
         THE THRESHOLD RULE.

         [row <- set(tbl[id_tag]), check(some word of row.attr is similar
         enough to p), ret row]
           -->
         union the buckets of every trigram of the PADDED pattern, keep the
         keys whose count passes gin_trgm_consistent's test, resolve each
         through tbl[aux_tag][pk_tag], and recheck the source's own
         predicate.

         parse_sim_any decides the predicate's shape, so this pattern stays
         as shallow as every other rule's.  What is left to check here is
         what relates the predicate to the TABLE: that the text it reads is
         this table's attribute under the scan's own binder, that the pattern
         is free of the three binders it will be read under, and that the
         threshold is positive.

         Freeness of x0 is what makes the rewrite legitimate: the predicate's
         only dependence on the row is the one access parse_sim_any returned,
         so the recheck may re-emit it under y instead.  0 < tn is
         load-bearing -- at a threshold of zero every row qualifies while the
         count test admits nothing -- and both bounds carry the source's Z
         literals into the nat arithmetic the completeness argument counts
         in.  y differs from the query's two outer binders because the
         recheck reads the row through EVar y from INSIDE the re-emitted
         predicate, so those two puts sit between; k needs no such check,
         since the key is read in the lookup's scrutinee before any of them
         is bound.
         ---------------------------------------------------------------- *)
      Definition thr_lookup_head (e : expr) : expr :=
        match e with
        | flatmap_filter_set
            (EUnop OSetOfList (EAccess (ELoc tbl0) id_tag0)) x0 pred x2 _ _ =>
            match parse_sim_any pred with
            | Some (q0, a0, r0, n0, w0, c0, tn0, tdz0, x1, attr0, p0) =>
                if (all_eqb [(tbl, [tbl0]); (attr, [attr0]);
                             (id_tag, [id_tag0]); (x0, [x1; x2])]
                    && negb (free_immut_in x0 p0)
                    && negb (free_immut_in k p0)
                    && negb (free_immut_in y p0)
                    (* and of the HOISTED binder: the emitted term binds the
                       query's deduplicated trigrams to cgram outside the
                       candidate filter, so the pattern is read under it. *)
                    && negb (free_immut_in cgram p0)
                    && negb (String.eqb y q0) && negb (String.eqb y a0)
                    && negb (String.eqb x0 q0) && negb (String.eqb x0 a0)
                    && (0 <? tn0)%Z && (0 <? tdz0)%Z)%bool
                then thr_probe q0 a0 r0 n0 w0 c0 tn0 tdz0
                       (thr_keep tn0 tdz0 (padded_e p0)) p0
                else e
            | None => e
            end
        | _ => e
        end.

      Lemma thr_lookup_head_preserve_ty : forall tl ctl t (Gstore : tenv),
          cgram <> k ->
          type_wf t -> @IndexInterface.is_tbl_ty tridx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl tri_tag = Success (@IndexInterface.idx_ty tridx t) ->
          access_record ctl pk_tag = Success (@IndexInterface.idx_ty uidx t) ->
          preserve_ty Gstore thr_lookup_head.
      Proof.
        unfold preserve_ty.
        intros tl ctl t Gstore H_ck H_twf H_is E_tbl E_id E_aux E_tri E_pk.
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
        unfold thr_lookup_head. cbv beta iota.
        (* the predicate's shape, decided by the parser *)
        lazymatch goal with
        | |- type_of _ _ (match parse_sim_any ?pr with _ => _ end) _ =>
            destruct (parse_sim_any pr) as [ res | ] eqn:E_parse
        end; [ | auto ].
        destruct res as
          [[[[[[[[[[qb ab] rb] nb] wb] cb] tnum] tden] xrow] attrn] pat0].
        apply parse_sim_any_Some in E_parse as [ E_pred H_ok ].
        (* the rule's own guard *)
        lazymatch goal with
        | |- type_of _ _ (if ?g then _ else _) _ => destruct g eqn:E_g
        end; [ | auto ].
        cbn [all_eqb all_eqb' andb] in E_g.
        repeat rewrite Bool.andb_true_iff in E_g.
        repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
        repeat rewrite Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        rewrite E_pred in H_t.
        repeat invert_type_of_clear; repeat invert_type_of_op_clear.
        (* Only the get_put_same branch of rewrite_map_get_put_hyp is wanted.
           Its second branch rewrites get_put_diff and discharges the side
           condition with `simpl in *` under a multimatch; with the
           predicate's own lookups in context that does not finish. *)
        repeat match goal with
               | Hg : context[map.get (map.put _ ?z _) ?z] |- _ =>
                   rewrite map.get_put_same in Hg
               end.
        repeat (clear_refl; repeat do_injection2).
        (* the row type, by congruence over the equalities the inversions
           left: two readings of the same store entry and two of the same
           id_tag access *)
        lazymatch goal with
        | |- type_of _ _ _ (TSet ?tz) =>
            replace tz with (TRecord rt) by congruence
        end.
        (* the inversions already bottomed out on the pattern's own typing *)
        assert (H_pty : type_of Gstore Genv pat0 TString).
        1:{ lazymatch goal with
            | Hp : type_of Gstore (map.put Genv _ _) pat0 TString |- _ =>
                eapply not_free_immut_put_ty; [ | exact Hp ]; assumption
            end. }
        assert (H_pty_k : type_of Gstore (map.put Genv k kt) pat0 TString)
          by (apply not_free_immut_put_ty2; [ assumption | exact H_pty ]).
        assert (H_pty_ky : type_of Gstore
                             (map.put (map.put Genv k kt) y (TRecord rt))
                             pat0 TString)
          by (apply not_free_immut_put_ty2; [ assumption | exact H_pty_k ]).
        eapply thr_probe_ty with (tl := tl) (ctl := ctl) (kt := kt).
        1: exact H_ok.
        1: apply String.eqb_neq; assumption.
        1: apply String.eqb_neq; assumption.
        1: exact E_tbl.
        1: exact E_aux.
        1: exact E_pk.
        1: exact E_attr.
        1: exact H_rtwf.
        2: exact H_pty_ky.
        eapply thr_keep_ty with (tl := tl) (ctl := ctl);
          [ exact H_ck | exact E_tbl | exact E_aux | exact E_tri | exact H_ktwf
          | apply padded_e_ty; exact H_pty
          | apply padded_e_ty;
            apply not_free_immut_put_ty2; [ assumption | exact H_pty ] ].
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
        1:{ eapply dyn_cands'_ty;
              [ exact E_tbl | exact E_aux | exact E_tri | exact H_ktwf
              | exact H_pty ]. }
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

      (* ------------------------------------------------------------------
         Three small, name-agnostic steps the semantics proof needs.

         The rule's guard and the parser between them leave the SOURCE's own
         binder names in the context under whatever name destruct_subexpr
         gave them, and `subst` picks which of two equal names survives.  So
         every step below is stated as a lemma over explicit parameters and
         applied with `assumption`, rather than written inline against a name
         the script would have to guess.
         ------------------------------------------------------------------ *)
      Lemma get_put_two_diff :
        forall (env : locals) (x q a : string) (rw qv av : value),
          String.eqb x q = false -> String.eqb x a = false ->
          map.get (map.put (map.put (map.put env x rw) q qv) a av) x
          = Some rw.
      Proof.
        intros env x q a rw qv av E_q E_a.
        apply String.eqb_neq in E_q, E_a.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_diff by congruence.
        apply map.get_put_same.
      Qed.

      (* Reading the indexed attribute off the scan's binder is exactly
         row_key -- including off a value that is not a record, where both
         sides give VUnit.  That is what lets the predicate's two cases be
         decided by row_key alone. *)
      Lemma interp_row_access :
        forall (store env : locals) (x : string) (rw : value),
          map.get env x = Some rw ->
          interp_expr store env (EAccess (EVar x) attr) = row_key attr rw.
      Proof.
        intros store env x rw E_x.
        rewrite interp_EAccess, interp_EVar.
        unfold get_local; rewrite E_x.
        destruct rw; reflexivity.
      Qed.

      (* The source's filter IS sim_row_test, at every value the table can
         hold -- a record whose attribute is a string by interp_sim_any_e, and
         anything else by interp_sim_any_e_unit, where the predicate is not a
         boolean at all and both sides are false. *)
      Lemma sim_filter_pointwise :
        forall (qsv aqv rsv cnum pwrd pacc : string)
               (store env : locals) (x : string) (tn tdz : Z)
               (p : expr) (pv : string) (rw : value),
          pred_binders_ok qsv aqv rsv cnum pwrd pacc ->
          String.eqb x qsv = false -> String.eqb x aqv = false ->
          free_immut_in x p = false ->
          interp_expr store env p = VString pv ->
          match interp_expr store (map.put env x rw)
                  (sim_any_e qsv aqv rsv cnum pwrd pacc tn tdz
                     (EAccess (EVar x) attr) p) with
          | VBool b => b
          | _ => false
          end
          = sim_row_test tn tdz pv rw.
      Proof.
        intros qsv aqv rsv cnum pwrd pacc store env x tn tdz p pv rw
          H_ok E_q E_a H_free E_p.
        assert (E_px : interp_expr store (map.put env x rw) p = VString pv).
        1:{ rewrite <- (not_free_immut_put_sem p x store env rw) by exact H_free.
            exact E_p. }
        assert (H_text : forall qv av,
                   interp_expr store
                     (map.put (map.put (map.put env x rw) qsv qv) aqv av)
                     (EAccess (EVar x) attr) = row_key attr rw).
        1:{ intros qv av. apply interp_row_access.
            apply get_put_two_diff; assumption. }
        destruct (row_key attr rw) as [ | | s | | | | | | | ] eqn:E_rk.
        (* the destruct rewrites the attribute's value in H_text too, so in
           each branch H_text already says what the text evaluates to *)
        3:{ rewrite (interp_sim_any_e qsv aqv rsv cnum pwrd pacc store
                       (map.put env x rw) tn tdz (EAccess (EVar x) attr) p
                       s pv H_ok E_px H_text).
            unfold sim_row_test; rewrite E_rk; reflexivity. }
        all: erewrite (interp_sim_any_e_unit qsv aqv rsv cnum pwrd pacc store
                         (map.put env x rw) tn tdz (EAccess (EVar x) attr) p);
          [ unfold sim_row_test; rewrite E_rk; reflexivity
          | exact H_text
          | intros s0; discriminate ].
      Qed.

      (* ------------------------------------------------------------------
         The threshold rule preserves semantics.

         The shape is the substring rule's, and every piece it composes is
         already proved:

           interp_thr_keep                 the candidate list, filtered by
                                           gin_trgm_consistent's own count test
           interp_thr_probe_as_probe_body  the emitted side, as probe_body_t
           sim_filter_pointwise            the source's filter, as sim_row_test
           probe_recheck_cands_eq_t        candidates + recheck = the scan
           sim_word_true__thr_complete     and the candidate list is COMPLETE

         Only completeness is owed, never soundness: the recheck is the
         source's own predicate, so a key the probe hands over that does not
         pass is dropped by the very test the scan would have applied.

         Unlike the substring rules this needs NO runtime guard on the
         pattern.  pad_length says the padded pattern is at least three
         characters whatever the pattern is, so it always has a trigram.
         ------------------------------------------------------------------ *)
      Lemma thr_lookup_head_preserve_sem :
        forall tl rt (Gstore : tenv) (store : locals),
          cgram <> k ->
          access_record rt attr = Success TString ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          match map.get store tbl with
          | Some v =>
              type_of_value v (TRecord tl) /\ tri_aux_wf_at v /\ unique_aux_wf_at v
          | _ => False
          end ->
          preserve_sem Gstore store thr_lookup_head.
      Proof.
        unfold preserve_sem; intros * H_ck H_attr E_tbl E_id H_store.
        intros e t Genv env H_Gs H_Ge H_t H_sw H_ew.
        destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
        destruct H_store as [ H_vty [ H_tri H_pk ] ].
        destruct (invariants__probe_data tl rt v H_attr E_id H_vty H_tri H_pk)
          as [ rv [ rv_aux [ rows [ td [ E_vrec [ E_rows [ E_aux
             [ E_tri [ E_pk [ E_te [ H_sets H_nd ] ] ] ] ] ] ] ] ] ] ].
        subst v.
        repeat destruct_subexpr_keep_str.
        unfold thr_lookup_head. cbv beta iota.
        (* the predicate's shape, decided by the parser *)
        lazymatch goal with
        | |- interp_expr _ _ (match parse_sim_any ?pr with _ => _ end) = _ =>
            destruct (parse_sim_any pr) as [ res | ] eqn:E_parse
        end; [ | reflexivity ].
        destruct res as
          [[[[[[[[[[qb ab] rb] nb] wb] cb] tnum] tden] xrow] attrn] pat0].
        apply parse_sim_any_Some in E_parse as [ E_pred H_ok ].
        (* the rule's own guard *)
        lazymatch goal with
        | |- interp_expr _ _ (if ?g then _ else _) = _ => destruct g eqn:E_g
        end; [ | reflexivity ].
        cbn [all_eqb all_eqb' andb] in E_g.
        repeat rewrite Bool.andb_true_iff in E_g.
        repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
        repeat rewrite Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        rewrite E_pred.
        (* the pattern is a string, and reads the same under every binder the
           rewrite introduces *)
        assert (H_pty : type_of Gstore Genv pat0 TString).
        1:{ rewrite E_pred in H_t.
            lazymatch goal with
            | H : type_of _ _ (EFlatmap _ _ _ _) _ |- _ =>
                inversion H; clear H; subst
            end.
            lazymatch goal with
            | H : type_of _ _ (EIf _ _ _) _ |- _ =>
                inversion H; clear H; subst
            end.
            lazymatch goal with
            | H : type_of _ _ (sim_any_e _ _ _ _ _ _ _ _ _ _) _ |- _ =>
                apply sim_any_e_ty_inv in H
            end.
            (* the typing hypothesis FIRST: three free_immut_in facts are in
               context and only this one's binder is the scan's *)
            eapply not_free_immut_put_ty; [ | eassumption ]; assumption. }
        pose proof (type_sound Gstore Genv pat0 TString H_pty H_Gs H_Ge
                      store env H_sw H_ew) as H_pval.
        assert (H_pstr : exists pv, interp_expr store env pat0 = VString pv).
        1:{ destruct (interp_expr store env pat0)
              as [ | | pv | | | | | | | ] eqn:E_pv.
            3: exists pv; reflexivity.
            all: inversion H_pval. }
        destruct H_pstr as [ pv E_pv ].
        assert (E_ppv : interp_expr store env (padded_e pat0)
                        = VString (pad pv))
          by (apply interp_padded_e; exact E_pv).
        assert (E_pad_k : forall kv,
                   interp_expr store (map.put env k kv) (padded_e pat0)
                   = VString (pad pv)).
        1:{ intros kv. apply interp_padded_e.
            erewrite <- not_free_immut_put_sem by eassumption. exact E_pv. }
        assert (E_pad_cg : forall gv,
                   interp_expr store (map.put env cgram gv) (padded_e pat0)
                   = VString (pad pv)).
        1:{ intros gv. apply interp_padded_e.
            erewrite <- not_free_immut_put_sem by eassumption. exact E_pv. }
        assert (H_pv' : forall (v0 r0 : value),
                   interp_expr store (map.put (map.put env k v0) y r0) pat0
                   = VString pv).
        1:{ intros v0 r0.
            erewrite <- not_free_immut_put_sem by eassumption.
            erewrite <- not_free_immut_put_sem by eassumption.
            exact E_pv. }
        (* the two members of the index record *)
        assert (H_tri_e : interp_expr store env
                            (EAccess (EAccess (ELoc tbl) aux_tag) tri_tag)
                          = VDict td)
          by (eapply interp_tbl_field; [ exact E_v | exact E_aux | exact E_tri ]).
        assert (H_pk_e : interp_expr store env
                           (EAccess (EAccess (ELoc tbl) aux_tag) pk_tag)
                         = VDict (UniqueDictIndexImpl.idx_entries key rows))
          by (eapply interp_tbl_field; [ exact E_v | exact E_aux | exact E_pk ]).
        (* the candidate list: every bucket of every trigram of the PADDED
           pattern, kept only where the count test passes *)
        destruct (interp_thr_keep store env tnum tden (padded_e pat0)
                    (pad pv) td H_ck H_tri_e H_sets E_pad_k E_pad_cg E_ppv
                    (pad_length pv))
          as [ cl [ E_cands H_cl ] ].
        (* completeness, which is all the recheck leaves to prove *)
        assert (H_compl : forall (r0 : value),
                   In r0 rows -> sim_row_test tnum tden pv r0 = true ->
                   In (row_key key r0)
                     (list_to_set
                        (filter (fun kv =>
                                   thr_test tnum tden (pad pv) (VDict td) kv)
                           cl))).
        1:{ intros r0 H_in H_test.
            apply list_to_set_incl_r, filter_In.
            unfold sim_row_test in H_test.
            destruct (row_key attr r0) as [ | | s | | | | | | | ] eqn:E_rk;
              try discriminate.
            apply existsb_exists in H_test as [ w0 [ H_w0 H_sim ] ].
            assert (E_str : TrigramIndexImpl.row_str attr r0 = s)
              by (unfold TrigramIndexImpl.row_str; rewrite E_rk; reflexivity).
            assert (H_tn : (0 < tnum)%Z)
              by (lazymatch goal with
                  | Hg : (0 <? tnum)%Z = true |- _ =>
                      apply Z.ltb_lt in Hg; exact Hg
                  end).
            assert (H_td : (0 < tden)%Z)
              by (lazymatch goal with
                  | Hg : (0 <? tden)%Z = true |- _ =>
                      apply Z.ltb_lt in Hg; exact Hg
                  end).
            assert (E_tn : Z.of_nat (Z.to_nat tnum) = tnum)
              by (apply Z2Nat.id; lia).
            assert (E_td : Z.of_nat (Z.to_nat tden) = tden)
              by (apply Z2Nat.id; lia).
            assert (H_w0' : In w0 (words seps (TrigramIndexImpl.row_str attr r0)))
              by (rewrite E_str; exact H_w0).
            assert (H_sim' : sim_test (Z.of_nat (Z.to_nat tnum))
                               (Z.of_nat (Z.to_nat tden)) (pad pv) (pad w0)
                             = true)
              by (rewrite E_tn, E_td; exact H_sim).
            assert (H_pos : 0 < Z.to_nat tnum) by lia.
            destruct (sim_word_true__thr_complete rows r0 pv w0
                        (Z.to_nat tnum) (Z.to_nat tden)
                        H_in H_w0' H_sim' H_pos)
              as [ H_bucket H_cnt ].
            rewrite E_te in H_bucket, H_cnt.
            split.
            1: apply (proj2 (H_cl _)); exact H_bucket.
            1:{ unfold thr_test.
                apply Bool.negb_true_iff, Z.ltb_ge.
                apply Nat2Z.inj_le in H_cnt.
                rewrite !Nat2Z.inj_mul in H_cnt.
                rewrite E_tn, E_td in H_cnt.
                lia. } }
        (* The SCAN side first.  filter_pointwise has to be applied while
           the goal holds exactly one filter: once the emitted side is
           rewritten it carries the candidate filter too, and the rewrite
           picks that one. *)
        rewrite interp_flatmap_filter_set, interp_ESetOf,
          interp_EAccess, interp_ELoc.
        unfold get_local; rewrite E_v; cbv beta iota.
        rewrite E_rows; cbv beta iota.
        erewrite filter_pointwise with (f2 := sim_row_test tnum tden pv).
        2:{ intros rw. apply sim_filter_pointwise; assumption. }
        (* the emitted side *)
        rewrite (interp_thr_probe_as_probe_body qb ab rb nb wb cb store env
                   tnum tden (thr_keep tnum tden (padded_e pat0)) pat0
                   _ rows pv H_ok
                   (ltac:(apply String.eqb_neq; assumption))
                   (ltac:(apply String.eqb_neq; assumption))
                   E_cands H_pv' H_pk_e).
        rewrite (probe_recheck_cands_eq_t key rows (sim_row_test tnum tden pv)
                   _ H_nd H_compl).
        reflexivity.
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
        assert (H_tri_e : interp_expr store env
                            (EAccess (EAccess (ELoc tbl) aux_tag) tri_tag) = VDict td)
          by (eapply interp_tbl_field; [ exact E_v | exact E_aux | exact E_tri ]).
        assert (H_pk_e : interp_expr store env
                           (EAccess (EAccess (ELoc tbl) aux_tag) pk_tag)
                         = VDict (UniqueDictIndexImpl.idx_entries key rows))
          by (eapply interp_tbl_field; [ exact E_v | exact E_aux | exact E_pk ]).
        (* the candidate set is the intersection of EVERY trigram's bucket.
           No seed to establish and no position to name: the guard's length
           test makes the bucket set nonempty, which is all interp_dyn_cands'
           needs to rule out the aggregate's None. *)
        destruct (interp_dyn_cands' store env pat pv td H_tri_e H_sets E_pv H_len)
          as [ cl [ E_cands H_cl ] ].
        rewrite (interp_probe_from store env _ _ _ pv _ E_cands H_pv' H_pk_e).
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
        (* completeness: a row that contains the pattern shares every one of
           its trigrams, so it is in every bucket, so it survives the
           intersection -- which is exactly what the characterization says,
           with no induction over positions. *)
        assert (H_compl : forall (r : value),
                   In r rows -> contains_test attr pv r = true ->
                   In (row_key key r) cl).
        1:{ intros r H_in H_p. apply (proj2 (H_cl _)). intros g H_g.
            apply key_at__In_tri_bucket. rewrite <- E_te.
            apply (TrigramIndexImpl.tri_lookup_complete_all attr key seps
                     _ _ pv g);
              [ exact H_in | exact H_free | | | exact H_g ].
            1:{ destruct pv; [ cbn [String.length] in H_len; lia
                             | discriminate ]. }
            1: apply contains_test_true__occurrence; exact H_p. }
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
        cbn [tri_use_idx_head]. repeat (case_match; auto; []).
        cbn in * |-.
        rewrite !Bool.andb_true_iff in *; intuition idtac.
        rewrite eqb_eq in *; subst.
        (* the read *)
        erewrite interp_tbl_field; [ | exact E_v | exact E_aux | reflexivity ].
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
        (* the key type of the dictionary the inner fold builds *)
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
           dictionary's, the row's, and the deleted key's. *)
        repeat invert_type_of_clear. repeat invert_type_of_op_clear.
        repeat rewrite_map_get_put_hyp.
        (* The table read fixes the element type, which fixes the key's. *)
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
            (* what the delete body computes *)
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


    (* The threshold rule, as a sound augmented expression transformation.

       Same shape as the substring rules': the typing branch is
       preserve_ty, and the semantics branch turns the store's
       holds_for_all_entries into the two index-member invariants
       preserve_sem asks for.  `cgram <> k` travels as a hypothesis rather
       than a Context because adding one at any but the END of the section
       renumbers the arguments of every later lemma. *)
    Lemma thr_lookup_head_sound :
      forall is_tbl_ty' aux_ty (aux_wf : value -> Prop),
        cgram <> k ->
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf thr_lookup_head.
    Proof.
      unfold trigram_bridges, aux_ty_for_idx, expr_aug_transf_sound.
      intros * H_ck [ H_aty1 [ H_aty2 [ H_is [ H_wf1 H_wf2 ] ] ] ] *.
      intros H_Gs H_Ge H_twf H_is' H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with
        H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl
      end.
      apply H_is in H_is' as H_is_tri.
      apply tri_is_tbl_ty_inv in H_is_tri
        as [ rt [ kt [ E_t [ E_attr E_key ] ] ] ].
      specialize (H_aty1 tbl_ty); specialize (H_aty2 tbl_ty).
      repeat destruct_match_hyp; intuition idtac.
      1:{ eapply thr_lookup_head_preserve_ty; try eassumption.
          apply H_is; exact H_is'. }
      1:{ subst tbl_ty.
          eapply thr_lookup_head_preserve_sem; try eassumption.
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


    Definition trigram_lookup_all_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl] (trigram_lookup_all_head tbl).

    Definition trigram_lookup_all_guarded_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl]
                   (trigram_lookup_all_guarded_head tbl).


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

    Definition thr_lookup_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl] (thr_lookup_head tbl).

    Lemma thr_lookup_transf_sound : forall is_tbl_ty' aux_ty aux_wf,
        cgram <> k ->
        trigram_bridges is_tbl_ty' aux_ty aux_wf ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf thr_lookup_transf.
    Proof.
      intros * H_ck H_br. unfold thr_lookup_transf.
      apply fold_command_with_globals_sound.
      apply thr_lookup_head_sound; assumption.
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
    (* The all-trigram rules.  A one-trigram pattern makes tri_cands_from's
       fold empty, so the candidate set IS a single bucket, and the k = 1
       case needs no rule of its own. *)
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
    (* The threshold rule is gated exactly as the substring lookups are, and
       for the same reason: it probes the primary-key member to turn a
       candidate key back into a row, so it needs that member's strong
       invariant, and only the declaration pays for it.

       A SEPARATE gate rather than a third disjunct of
       trigram_lookup_gated, so that nothing already proved changes: the
       threshold rule carries the side condition `cgram <> k`, and folding
       it into the existing bundle would add that hypothesis to
       trigram_lookup_gated_sound. *)
    Definition thr_lookup_gated (ds : list decl) : string -> command -> command :=
      if declares_unique key ds
      then thr_lookup_transf
      else fun _ => id.

    Lemma thr_lookup_gated_sound : forall ds is_tbl_ty' aux_ty aux_wf,
        cgram <> k ->
        (declares_unique key ds = true ->
         trigram_bridges is_tbl_ty' aux_ty aux_wf) ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf (thr_lookup_gated ds).
    Proof.
      intros * H_ck H_br. unfold thr_lookup_gated.
      destruct (declares_unique key ds) eqn:E_uq.
      1: apply thr_lookup_transf_sound;
         [ exact H_ck | apply H_br; reflexivity ].
      1: unfold aug_transf_sound, id; intros; repeat split; auto.
    Qed.

  End WithMap.
End WithIndexUse.
