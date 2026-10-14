Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.Utils fiat2.Substitute
  fiat2.IndexTransf fiat2.Constraint fiat2.DictIndexImpl fiat2.FlatmapForms fiat2.TransfUtils
  fiat2.CollectionTransf fiat2.StringFacts
  fiat2.UniqueDictIndexImpl fiat2.UniqueIndexUse fiat2.TrigramIndexImpl.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List Permutation Sorted.

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
          (forall (env' : locals), interp_expr store env' g = gv) ->
          (forall (env' : locals), interp_expr store env' p = VString pv) ->
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
        rewrite interp_EOptMatch, interp_EBinop, E_tri, (E_g env).
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
        rewrite (E_p (map.put (map.put env k v) y r)).
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
        assert (H_g : forall (env' : locals),
                   interp_expr store env' (EAtom (AString (String.substring 0 3 pstr)))
                   = VString (String.substring 0 3 pstr)) by reflexivity.
        assert (H_pv : forall (env' : locals),
                   interp_expr store env' (EAtom (AString pstr)) = VString pstr)
          by reflexivity.
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

    End WithTable.
  End WithMap.
End WithIndexUse.
