Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.Utils fiat2.Substitute
  fiat2.IndexTransf fiat2.Constraint fiat2.DictIndexImpl fiat2.FlatmapForms fiat2.TransfUtils
  fiat2.CollectionTransf fiat2.StringFacts
  fiat2.UniqueDictIndexImpl fiat2.UniqueIndexInstall fiat2.UniqueIndexGate
  fiat2.UniqueIndexUse fiat2.TrigramIndexImpl fiat2.Surface.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List Permutation Sorted Lia.

Import ListNotations.

(* Using the trigram index: a substring query becomes a probe and a recheck.

   Three things make this rule unlike every other lookup rule here.

   A trigram match is NECESSARY but not SUFFICIENT: a row sharing a trigram
   with the pattern need not contain the pattern.  So the rewrite keeps the
   source's own `contains` test, applied to the rows the probe produced.
   TrigramIndexImpl.tri_lookup_complete is one inclusion of the equation
   below; the recheck is what supplies the other.

   The probe needs TWO members of the index record at once.  The trigram
   dictionary maps a trigram to a set of primary KEYS, so only the
   primary-key index can turn those keys back into rows.  That is why the
   rule below is stated against two sets of bridges, and why the primary-key
   work had to come first.

   And the rule may only fire when the pattern HAS a trigram.  Here that is
   decided statically -- the pattern is a string literal of length at least
   three -- which is why this first form needs no runtime guard. *)

Section WithWord.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.
  (* the text attribute the index is built on, and the table's primary key *)
  Context (attr key : string).

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
    destruct d as [ | | | | | | | d' | | | ]; try contradiction.
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
    destruct (row_key attr r) as [ | | | s | | | | | | | ];
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
      NoDup (List.map (row_key key) rows) ->
      list_to_set (filter (contains_test p) (list_to_set rows))
      = list_to_set
          (flat_map (probe_body rows p)
             (tri_bucket (VString (String.substring 0 3 p))
                (TrigramIndexImpl.tri_entries attr key rows))).
  Proof.
    intros rows p H_len H_nd.
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
            apply (TrigramIndexImpl.tri_lookup_complete attr key (word_ok := word_ok));
              [ exact H_in | exact H_len
              | apply contains_test_true__occurrence; exact H_p ]. }
        1:{ unfold probe_body.
            rewrite (UniqueDictIndexImpl.idx_lookup_Some key (word_ok := word_ok)
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
        apply (UniqueDictIndexImpl.idx_lookup_Some_inv key (word_ok := word_ok))
          in E_lk as [ H_rows _ ].
        apply list_to_set_incl_r, filter_In; split; [ | exact E_p ].
        apply list_to_set_incl_r; exact H_rows. }
  Qed.
End WithWord.

Section WithIndexUse.
  (* the trigram index's own binders *)
  Context (hole attr key tup acc pos sacc bkt : string).
  Context (H_tup_acc : tup <> acc) (H_tup_pos : tup <> pos)
    (H_tup_sacc : tup <> sacc) (H_tup_bkt : tup <> bkt) (H_pos_sacc : pos <> sacc).
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

  Notation tridx := (trigram_idx hole attr key tup acc pos sacc bkt).
  Notation uidx := (unique_dict_idx hole key utup uacc).

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (width:=width)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Notation tridx_wf :=
      (TrigramIndexImpl.idx_wf hole attr key tup acc pos sacc bkt (locals := locals)).
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
       Nothing new has to be written down, and nothing about trigrams has to
       be re-proved -- which is the payoff of having written to_idx as a fold
       in the first place.
       ------------------------------------------------------------------ *)

    Notation tri_row_body' :=
      (TrigramIndexImpl.tri_row_body attr key tup acc pos sacc bkt).

    Definition to_idx_at (d : expr) : expr :=
      EFold d (EAtom (AEmptyDict None)) tup acc tri_row_body'.

    (* to_idx_at spelled out, so that the rule can match it.  Every binder
       and attribute occurrence is a pattern variable, and the guard checks
       that they are the ones this index uses. *)
    Notation etri_idx tup0 tup1 tup2 tup3 tup4 tup5 acc0 acc1
      pos0 pos1 pos2 sacc0 sacc1 sacc2 bkt0 bkt1 attr0 attr1 attr2 key0 key1 d :=
      (EFold d (EAtom (AEmptyDict None)) tup0 acc0
         (EFold (EBinop ORange (EAtom (AInt 0))
                   (EBinop OMinus
                      (EUnop OLengthString (EAccess (EVar tup1) attr0))
                      (EAtom (AInt 2))))
            (EVar acc1) pos0 sacc0
            (ETernop OInsert (EVar sacc1)
               (ETernop OSubstring (EAccess (EVar tup2) attr1) (EVar pos1)
                  (EAtom (AInt 3)))
               (EOptMatch
                  (EBinop OLookup (EVar sacc2)
                     (ETernop OSubstring (EAccess (EVar tup3) attr2) (EVar pos2)
                        (EAtom (AInt 3))))
                  (EBinop OSetInsert (EAtom (AEmptySet None))
                     (EAccess (EVar tup4) key0))
                  bkt0 (EBinop OSetInsert (EVar bkt1)
                          (EAccess (EVar tup5) key1)))))).

    Definition cons_to_tri_insert_head (e : expr) : expr :=
      match e with
      | etri_idx tup0 tup1 tup2 tup3 tup4 tup5 acc0 acc1
          pos0 pos1 pos2 sacc0 sacc1 sacc2 bkt0 bkt1 attr0 attr1 attr2 key0 key1
          (EBinop OCons e1 e2) =>
          if (all_eqb [(tup, [tup0; tup1; tup2; tup3; tup4; tup5]);
                       (acc, [acc0; acc1]); (pos, [pos0; pos1; pos2]);
                       (sacc, [sacc0; sacc1; sacc2]); (bkt, [bkt0; bkt1]);
                       (attr, [attr0; attr1; attr2]); (key, [key0; key1])]
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

    Section WithTable.
      Context (tbl : string).

      Notation tri_e := (EAccess (EAccess (ELoc tbl) aux_tag) tri_tag).
      Notation pk_e := (EAccess (EAccess (ELoc tbl) aux_tag) pk_tag).

      (* Probe one trigram's bucket, turn each key back into its row with
         the primary-key index, and recheck the pattern on what comes back.
         The recheck is not an optimization that was left in: a trigram match
         is necessary and not sufficient, so dropping it would be unsound. *)
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
            /\ TrigramIndexImpl.tri_entries attr key rows = VDict td
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
        destruct v as [ | | | | | | rv | | | | ];
          intros H_vty H_tri H_pk;
          cbv beta iota in H_tri, H_pk; try contradiction.
        (* destruct on a match's scrutinee substitutes it in the hypotheses
           too, so each step only has to reduce the match it exposed *)
        destruct (access_record rv id_tag) as [ v_id | ] eqn:E_vid;
          cbv beta iota in H_tri, H_pk; try contradiction.
        destruct (access_record rv aux_tag) as [ v_aux | ] eqn:E_vaux;
          cbv beta iota in H_tri, H_pk; try contradiction.
        destruct v_aux as [ | | | | | | rv_aux | | | | ];
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
        rewrite (TrigramIndexImpl.fiat2_gallina_to_idx hole attr key tup acc pos sacc bkt
                   H_tup_acc H_tup_pos H_tup_sacc H_tup_bkt H_pos_sacc
                   (locals_ok := locals_ok) rows
                   (TrigramIndexImpl.typed_rows_have_text attr rows rt H_attr H_rows))
          in H_tri.
        assert (H_bs : TrigramIndexImpl.buckets_are_sets
                         (TrigramIndexImpl.tri_entries attr key rows)).
        1:{ unfold TrigramIndexImpl.tri_entries.
            apply (TrigramIndexImpl.tri_entries_buckets attr key (word_ok := word_ok)).
            constructor. }
        destruct (TrigramIndexImpl.tri_entries attr key rows) as
          [ | | | | | | | td | | | ] eqn:E_te;
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
            destruct bkv as [ | | | | | | | | | bl | ];
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
                    (VString pv)) as [ | | bb | | | | | | | | ].
        (* only the boolean branch has anything to do: a test that is not a
           boolean fails the recheck and contributes nothing, on both sides *)
        3:{ destruct bb.
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
         characters hands over its first trigram at rewrite time, and
         anything else leaves the program alone.
         ------------------------------------------------------------------ *)
      Definition literal_trigram (e : expr) : option expr :=
        match e with
        | EAtom (AString s) =>
            if Nat.leb 3 (String.length s)
            then Some (EAtom (AString (String.substring 0 3 s)))
            else None
        | _ => None
        end.

      Lemma literal_trigram_Some : forall p g,
          literal_trigram p = Some g ->
          exists s, p = EAtom (AString s)
                    /\ 3 <= String.length s
                    /\ g = EAtom (AString (String.substring 0 3 s)).
      Proof.
        unfold literal_trigram; intros p g H.
        destruct p as [ | | a | | | | | | | | | | | | | | | ]; try discriminate.
        destruct a as [ | | | str | | | | | | ]; try discriminate.
        destruct (Nat.leb 3 (String.length str)) eqn:E_len; [ | discriminate ].
        injection H as H; subst.
        exists str. split.
        1: reflexivity.
        1:{ split; [ apply Nat.leb_le; exact E_len | reflexivity ]. }
      Qed.

      (* [row <- set(tbl[id_tag]), check(contains(row.attr, p)), ret row]
         -->
         probe tbl[aux_tag][tri_tag] with p's first trigram, resolve each
         key through tbl[aux_tag][pk_tag], and recheck contains. *)
      Definition trigram_lookup_head (e : expr) : expr :=
        match e with
        | flatmap_filter_set
            (ESetOf (EAccess (ELoc tbl0) id_tag0))
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
        apply literal_trigram_Some in E_lit as [ pstr [ E_p [ H_len E_g ] ] ].
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
        rewrite (probe_recheck_eq attr key rows pstr H_len H_nd), E_te.
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
        destruct t as [ | | | | | | t1 | | | | ]; try discriminate.
        destruct t1 as [ | | | | | | | rt | | | ]; try discriminate.
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
        apply literal_trigram_Some in E_lit as [ pstr [ E_p [ H_len E_g ] ] ].
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
         The guarded form, for a pattern that is not a literal.

         Whether the pattern has a trigram at all cannot be decided at
         rewrite time, so the rule decides it at run time and keeps the
         original scan for the short case.  Every production engine does
         this -- PostgreSQL's index scan "degenerates to a full-index scan"
         for a pattern with no extractable trigrams, Google Code Search's
         trigram query for a short literal collapses to ANY -- while two
         mainstream n-gram indexes instead return nothing, which is simply
         wrong.  The difference here is that the length condition is a
         soundness obligation: probe_recheck_eq does not hold without it, so
         the fallback cannot be dropped.
         ------------------------------------------------------------------ *)
      Definition pattern_has_trigram (p : expr) : expr :=
        EBinop OLess (EAtom (AInt 2)) (EUnop OLengthString p).

      Definition first_trigram (p : expr) : expr :=
        ETernop OSubstring p (EAtom (AInt 0)) (EAtom (AInt 3)).

      Definition trigram_lookup_guarded_head (e : expr) : expr :=
        match e with
        | flatmap_filter_set
            (ESetOf (EAccess (ELoc tbl0) id_tag0))
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
        destruct t as [ | | | | | | t1 | | | | ]; try discriminate.
        destruct t1 as [ | | | | | | | rt | | | ]; try discriminate.
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
        1:{ (* the guard: 2 < strlen(pattern) *)
            eapply TyEBinop; [ apply TyOLess | apply TyEAtom; apply TyAInt | ].
            eapply TyEUnop; [ apply TyOLengthString | exact H_pty ]. }
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
              as [ | | | pv | | | | | | | ] eqn:E_pv.
            4: exists pv; reflexivity.
            all: inversion H_pval. }
        destruct H_pstr as [ pv E_pv ].
        (* the guard *)
        unfold pattern_has_trigram, first_trigram.
        rewrite interp_EIf, interp_EBinop, interp_EUnop, interp_EAtom, E_pv.
        cbn [interp_unop interp_binop interp_atom].
        destruct (Z.ltb 2 (Z.of_nat (String.length pv))) eqn:E_long.
        2: reflexivity.
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
        rewrite (probe_recheck_eq attr key rows pv H_len H_nd), E_te.
        unfold probe_body. reflexivity.
      Qed.

    End WithTable.

    Lemma tri_is_tbl_ty_inv : forall t,
        @IndexInterface.is_tbl_ty tridx t = true ->
        exists rt kt, t = TList (TRecord rt)
                      /\ access_record rt attr = Success TString
                      /\ access_record rt key = Success kt.
    Proof.
      cbn [IndexInterface.is_tbl_ty trigram_idx]; unfold TrigramIndexImpl.is_tbl_ty.
      intros t H.
      destruct t as [ | | | | | | t1 | | | | ]; try discriminate.
      destruct t1 as [ | | | | | | | rt | | | ]; try discriminate.
      destruct (access_record rt attr) as [ at_ty | ] eqn:E_attr; try discriminate.
      destruct (access_record rt key) as [ kt | ] eqn:E_key; try discriminate.
      apply type_eqb_eq in H; subst at_ty.
      exists rt, kt; split; [ reflexivity | split; [ exact E_attr | exact E_key ] ].
    Qed.

    (* ------------------------------------------------------------------
       What whoever assembles the index record owes this rule.

       Two members' layouts instead of one, because the trigram buckets hold
       keys and only the primary-key index can resolve them -- that is the
       price of a rule that needs a second index to interpret the first
       one's answer.  And one invariant bridge delivering both members'
       relations, where the primary-key one is the STRONG relation that no
       index establishes from typing and the declaration pays for.
       ------------------------------------------------------------------ *)
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

    (* The rules, applied everywhere below the installation. *)
    Definition trigram_lookup_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl] (trigram_lookup_head tbl).

    Definition trigram_lookup_guarded_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl] (trigram_lookup_guarded_head tbl).

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
    Definition trigram_lookup_gated (ds : list decl) : string -> command -> command :=
      if declares_unique key ds
      then fun tbl => Basics.compose (trigram_lookup_guarded_transf tbl)
                        (trigram_lookup_transf tbl)
      else fun _ => id.

    Lemma trigram_lookup_gated_sound : forall ds is_tbl_ty' aux_ty aux_wf,
        (declares_unique key ds = true -> trigram_bridges is_tbl_ty' aux_ty aux_wf) ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf (trigram_lookup_gated ds).
    Proof.
      intros * H_br. unfold trigram_lookup_gated.
      destruct (declares_unique key ds) eqn:E_uq.
      1:{ apply aug_transf_sound_compose.
          1: apply trigram_lookup_guarded_transf_sound, H_br; reflexivity.
          1: apply trigram_lookup_transf_sound, H_br; reflexivity. }
      1: unfold aug_transf_sound, id; intros; repeat split; auto.
    Qed.
  End WithMap.
End WithIndexUse.
