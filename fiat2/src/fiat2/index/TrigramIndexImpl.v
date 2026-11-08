Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.IndexInterface fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute
  fiat2.StringFacts fiat2.constraint.Constraint fiat2.rules.CollectionTransf.
Require fiat2.index.DictIndexImpl.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Sorted Lia.
Import ListNotations.

Open Scope string_scope.

(* An inverted index for substring search: trigram -> the primary keys of the
   rows whose text contains it.

   This index puts a row under MORE THAN ONE key -- a text of length n has
   n-2 trigrams, and the row's key goes into the bucket of each -- and it is
   lossy in the other direction, a bucket holding keys rather than rows.  So
   it pays off only beside a primary-key index, which turns a key back into
   its row: the two are members of ONE index record, the trigram dictionary
   built here and the key-to-row dictionary of UniqueDictIndexImpl, and a
   substring query is one lookup in each.

   Why a SET of keys, not a bag or a list.  A text may contain the same
   trigram twice ("aaaa" contains "aaa" at two positions), so a bag would hold
   a row's key once per occurrence and a lookup emitting one row per entry
   would return that row twice -- wrong, not merely slow.  Deduplication is
   part of correctness here.  Nothing is lost by it: a query answered this way
   is a bag or set query, never a list query, so the order the keys come back
   in is not observable.  A set also makes the maintenance rewrites
   idempotent, one insertion per occurrence.

   What this index claims, like every other, is only that it is what to_idx
   computes, which is true of any table.  It does NOT by itself give the step
   from "the bucket of one trigram of the pattern" to "every row that contains
   the pattern" -- that rests on sep_free_inside_word and trigrams_factor in
   StringFacts --
   nor the step back from a key to its row, which rests on the declared
   primary key. *)

Section WithHole.
  Context (hole : string).
  (* the text attribute whose trigrams are indexed, and the primary key the
     buckets hold *)
  Context (attr key : string).

  Section WithVars.
    (* the row and the dictionary, bound by the outer fold over rows *)
    Context (tup acc : string).
    (* the trigram and the dictionary, bound by the inner fold over the
       trigrams of one padded word *)
    Context (gvar sacc : string).
    (* the bucket already stored at a trigram, if any *)
    Context (bkt : string).
    Context (H_tup_acc : tup <> acc).
    Context (H_tup_pos : tup <> gvar).
    Context (H_tup_sacc : tup <> sacc).
    Context (H_tup_bkt : tup <> bkt).
    Context (H_sacc_bkt : sacc <> bkt).
    Context (H_pos_sacc : gvar <> sacc).
    (* Last in the list, so that adding it leaves every existing lemma's
       arguments where they were.  Only the delete body below needs it, since
       it is the only body that mentions a trigram under the bucket's
       binder. *)
    Context (H_pos_bkt : gvar <> bkt).

    (* pg_trgm trigrams each WORD separately -- find_word walks the maximal
       runs of word characters and generate_trgm_only pads each one -- so
       the per-row body is TWO folds: over the words, then over that word's
       trigrams.  These are the outer fold's binders, and the alphabet of
       separator characters it splits on.

       Last in the list, like the hypothesis above. *)
    Context (seps : string).
    Context (wrd wacc : string).
    Context (H_wrd_tup : wrd <> tup).
    Context (H_wrd_gvar : wrd <> gvar).
    Context (H_wrd_sacc : wrd <> sacc).
    Context (H_wrd_bkt : wrd <> bkt).
    Context (H_wacc_tup : wacc <> tup).
    Context (H_wacc_gvar : wacc <> gvar).
    Context (H_wacc_sacc : wacc <> sacc).
    Context (H_wacc_bkt : wacc <> bkt).
    Context (H_wacc_wrd : wacc <> wrd).

    (* The text whose trigrams are indexed, PADDED: two spaces before and
       one after, which is what pg_trgm does (LPADDING 2, RPADDING 1 in
       trgm.h).  Padding is what makes the index able to answer a FUZZY
       query at all -- unpadded, "Smith" and "Smyth" share no trigram
       whatever, so no similarity threshold could ever relate them, while
       padded they share three of nine (StringFacts.trigrams_pad_smith).

       It lives here, in the one definition every body goes through, rather
       than in each body, so that the insert body, the delete body and both
       of their position ranges pad identically by construction.

       The key stays a TString: a padded trigram is still three characters.
       So idx_ty, every typing premise and every maintenance rule keep their
       shape, and only WHICH strings occur as keys changes.

       The PATTERN side is deliberately NOT padded -- see
       StringFacts.trigrams_pad: padding only ADDS keys, so a lookup that
       extracts the pattern's trigrams unpadded still finds every row it
       should.  That is also what Postgres does, since a substring may match
       in the middle of a word, where no padding applies. *)
    (* the row's text, split as find_word splits it *)
    Definition row_words (r : expr) : expr :=
      EBinop OWords (EAtom (AString seps)) (EAccess r attr).
    Definition row_pk (r : expr) : expr := EAccess r key.

    (* one WORD, padded: LPADDING 2 and RPADDING 1, the buffer
       generate_trgm_only hands to make_trigrams *)
    Definition word_text (w : expr) : expr :=
      EBinop OConcatString (EAtom (AString "  "))
        (EBinop OConcatString w (EAtom (AString " "))).

    (* and the windows make_trigrams slides over it.  Empty when the padded
       word is shorter than three characters, as there. *)
    Definition word_trigrams (w : expr) : expr :=
      EUnop OTrigrams (word_text w).

    (* the key goes into the bucket at one trigram of one padded word *)
    Definition tri_insert_body : expr :=
      ETernop OInsert (EVar sacc) (EVar gvar)
        (EOptMatch
           (EBinop OLookup (EVar sacc) (EVar gvar))
           (EBinop OSetInsert (EAtom (AEmptySet None)) (row_pk (EVar tup)))
           bkt
           (EBinop OSetInsert (EVar bkt) (row_pk (EVar tup)))).

    Definition tri_word_body : expr :=
      EFold (word_trigrams (EVar wrd)) (EVar wacc) gvar sacc tri_insert_body.

    Definition tri_row_body : expr :=
      EFold (row_words (EVar tup)) (EVar acc) wrd wacc tri_word_body.

    Definition to_idx : expr :=
      EFold (EVar hole) (EAtom (AEmptyDict Unranged None)) tup acc tri_row_body.

    (* ------------------------------------------------------------------
       And the other direction, for maintaining the index when a row goes:
       the key leaves the bucket at one trigram of the row's text, and the
       entry goes with it if that was its last key.

       The removal is spelled twice rather than bound to a name: a let would
       cost every rule matching this body one more binder to be told about,
       and a bucket is small enough to take apart twice.
       ------------------------------------------------------------------ *)
    Definition tri_without_pk : expr :=
      EBinop OSetDiff (EVar bkt)
        (EBinop OSetInsert (EAtom (AEmptySet None)) (row_pk (EVar tup))).

    Definition tri_delete_body : expr :=
      EOptMatch
        (EBinop OLookup (EVar sacc)
           (EVar gvar))
        (EVar sacc)
        bkt
        (EIf (EBinop OEq tri_without_pk (EAtom (AEmptySet None)))
           (EBinop ODelete (EVar sacc)
              (EVar gvar))
           (ETernop OInsert (EVar sacc)
              (EVar gvar)
              tri_without_pk)).

    Definition tri_word_delete_body : expr :=
      EFold (word_trigrams (EVar wrd)) (EVar wacc) gvar sacc tri_delete_body.

    Definition tri_row_delete_body : expr :=
      EFold (row_words (EVar tup)) (EVar acc) wrd wacc tri_word_delete_body.

    (* A table this index is for: a list of records carrying a string
       attribute to index and a key attribute to point at. *)
    Definition is_tbl_ty (t : type) : bool :=
      match t with
      | TList (TRecord rt) =>
          match access_record rt attr with
          | Success at_ty =>
              match access_record rt key with
              | Success _ => type_eqb at_ty TString
              | _ => false
              end
          | _ => false
          end
      | _ => false
      end.

    Definition idx_ty (t : type) : type :=
      match t with
      (* Both trigram lookup tiers are point probes, so this one is
         Unranged too. *)
      | TList (TRecord rt) => TDict Unranged TString (TSet (get_attr_type rt key))
      | _ => TUnit
      end.

    Lemma idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t).
    Proof.
      unfold is_tbl_ty, idx_ty; destruct t; cbn; intros H_wf H_tbl; try discriminate.
      destruct t; try discriminate.
      invert_type_wf.
      repeat constructor.
      apply get_attr_type_ty_wf; assumption.
    Qed.

    Section WithMap.
      Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
      Notation value := (value).
      Context {locals : map.map string value} {locals_ok : map.ok locals}.

      (* as elsewhere, so that a boolean order can be read as a relation *)
      Local Coercion is_true : bool >-> Sortclass.

      (* reading a variable out of the environment the folds have built *)
      Ltac lookup_var :=
        apply TyEVar; repeat (rewrite map.get_put_diff by congruence);
        rewrite map.get_put_same; reflexivity.

      (* like lookup_var, except that the variable may come from the
         environment itself rather than from a chain of puts *)
      Ltac lookup_var' :=
        apply TyEVar;
        repeat (rewrite map.get_put_diff by congruence);
        first [ rewrite map.get_put_same; reflexivity | eassumption ].

      Ltac int_lit := apply TyEAtom; apply TyAInt.
      Ltac str_lit := apply TyEAtom; apply TyAString.

      (* The padded text at attr.  Its type is TString for the same reason
         the raw field's is -- concatenation with a literal preserves it --
         so every occurrence of the text in the bodies below is discharged
         by these same three steps. *)
      (* the row's words: OWords over the field, a TList TString *)
      Ltac words_src :=
        eapply TyEBinop;
          [ apply TyOWords
          | str_lit
          | eapply TyEAccess; [ lookup_var | eassumption ] ].

      (* one word's trigrams: OTrigrams over the padded word, also a list.
         The padding is two concatenations with literals, which preserve
         TString, so the whole source is discharged in these steps. *)
      Ltac word_tri_src :=
        eapply TyEUnop;
          [ apply TyOTrigrams
          | eapply TyEBinop;
              [ apply TyOConcatString
              | str_lit
              | eapply TyEBinop; [ apply TyOConcatString | lookup_var | str_lit ] ] ].

      (* the same two, for the lemmas that look a binder up in Genv itself *)
      Ltac words_src' :=
        eapply TyEBinop;
          [ apply TyOWords
          | str_lit
          | eapply TyEAccess; [ lookup_var' | eassumption ] ].

      Ltac word_tri_src' :=
        eapply TyEUnop;
          [ apply TyOTrigrams
          | eapply TyEBinop;
              [ apply TyOConcatString
              | str_lit
              | eapply TyEBinop; [ apply TyOConcatString | lookup_var' | str_lit ] ] ].

      Lemma to_idx_ty : forall (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t).
      Proof.
        unfold is_tbl_ty, idx_ty, to_idx, tri_row_body, tri_insert_body,
          row_words, word_text, word_trigrams, row_pk.
        intros * H_wf H_tbl.
        repeat destruct_match_hyp; try discriminate; subst.
        rewrite type_eqb_eq in H_tbl; subst.
        assert (H_rec_wf : type_wf (TRecord l)) by (inversion H_wf; assumption).
        pose proof (get_attr_type_ty_wf l key H_rec_wf) as H_kt_wf.
        lazymatch goal with
          E : access_record l key = Success ?kt |- _ =>
            assert (H_kt : get_attr_type l key = kt)
              by (unfold get_attr_type; rewrite E; reflexivity)
        end.
        rewrite H_kt in H_kt_wf |- *.
        (* the outer fold, over the rows *)
        eapply TyEFold.
        1:{ lookup_var. }
        1:{ apply TyEAtom; apply TyAEmptyDict';
            [ apply WFTString | apply WFTSet; assumption ]. }
        (* the fold over this row's words, as find_word splits them *)
        eapply TyEFold.
        1:{ words_src. }
        1:{ lookup_var. }
        (* the fold over this word's trigrams, padded *)
        eapply TyEFold.
        1:{ word_tri_src. }
        1:{ lookup_var. }
        (* insert the key under this trigram *)
        eapply TyETernop; [ apply TyOInsert | lookup_var | lookup_var | ].
        eapply TyEOptMatch.
        1:{ (* what is stored at that trigram, if anything *)
            eapply TyEBinop; [ apply TyOLookup | lookup_var | lookup_var ]. }
        1:{ (* nothing yet: the singleton of this row's key *)
            eapply TyEBinop; [ apply TyOSetInsert
              | apply TyEAtom; apply TyAEmptySet'; assumption | ].
            eapply TyEAccess; [ lookup_var | eassumption ]. }
        1:{ (* something already: this row's key goes in beside it *)
            eapply TyEBinop; [ apply TyOSetInsert | lookup_var | ].
            eapply TyEAccess; [ lookup_var | eassumption ]. }
      Qed.

      (* The index's own per-row body, typed from the environment rather
         than from the hole, so that a rule can rebuild the index of a
         table it did not get from the source's own typing. *)
      Lemma tri_row_body_ty : forall rt kt (Gstore Genv : tenv),
          type_wf kt ->
          access_record rt attr = Success TString ->
          access_record rt key = Success kt ->
          map.get Genv tup = Some (TRecord rt) ->
          map.get Genv acc = Some (TDict Unranged TString (TSet kt)) ->
          type_of Gstore Genv tri_row_body (TDict Unranged TString (TSet kt)).
      Proof.
        unfold tri_row_body, tri_word_body, tri_insert_body, row_words,
          word_text, word_trigrams, row_pk.
        intros * H_ktwf E_attr E_key E_tup E_acc.
        eapply TyEFold.
        1:{ words_src'. }
        1:{ lookup_var'. }
        eapply TyEFold.
        1:{ word_tri_src'. }
        1:{ lookup_var'. }
        eapply TyETernop; [ apply TyOInsert | lookup_var' | lookup_var' | ].
        eapply TyEOptMatch.
        1:{ eapply TyEBinop; [ apply TyOLookup | lookup_var' | lookup_var' ]. }
        1:{ eapply TyEBinop; [ apply TyOSetInsert
              | apply TyEAtom; apply TyAEmptySet'; assumption | ].
            eapply TyEAccess; [ lookup_var' | eassumption ]. }
        1:{ eapply TyEBinop; [ apply TyOSetInsert | lookup_var' | ].
            eapply TyEAccess; [ lookup_var' | eassumption ]. }
      Qed.

      (* The delete body types wherever the index's own does: the row at tup
         and the dictionary at acc. *)
      Lemma tri_row_delete_body_ty : forall rt kt (Gstore Genv : tenv),
          type_wf kt ->
          access_record rt attr = Success TString ->
          access_record rt key = Success kt ->
          map.get Genv tup = Some (TRecord rt) ->
          map.get Genv acc = Some (TDict Unranged TString (TSet kt)) ->
          type_of Gstore Genv tri_row_delete_body (TDict Unranged TString (TSet kt)).
      Proof.
        unfold tri_row_delete_body, tri_word_delete_body, tri_delete_body,
          tri_without_pk, row_words, word_text, word_trigrams, row_pk.
        intros * H_ktwf E_attr E_key E_tup E_acc.
        (* the fold over this row's words, then over each word's trigrams *)
        eapply TyEFold.
        1:{ words_src'. }
        1:{ lookup_var'. }
        eapply TyEFold.
        1:{ word_tri_src'. }
        1:{ lookup_var'. }
        eapply TyEOptMatch.
        1:{ (* what the bucket at this trigram holds, if anything *)
            eapply TyEBinop; [ apply TyOLookup | lookup_var' | lookup_var' ]. }
        1:{ (* nothing there: the dictionary is unchanged *)
            lookup_var'. }
        (* something there: the key comes out, and the entry goes if that
           empties the bucket *)
        eapply TyEIf.
        1:{ eapply TyEBinop; [ apply TyOEq | | ].
            1:{ eapply TyEBinop; [ apply TyOSetDiff | lookup_var' | ].
                eapply TyEBinop;
                  [ apply TyOSetInsert
                  | apply TyEAtom; apply TyAEmptySet'; assumption | ].
                eapply TyEAccess; [ lookup_var' | eassumption ]. }
            1: apply TyEAtom; apply TyAEmptySet'; assumption. }
        1:{ eapply TyEBinop; [ apply TyODelete | lookup_var' | lookup_var' ]. }
        1:{ eapply TyETernop; [ apply TyOInsert | lookup_var' | lookup_var' | ].
            1:{ eapply TyEBinop; [ apply TyOSetDiff | lookup_var' | ].
                eapply TyEBinop;
                  [ apply TyOSetInsert
                  | apply TyEAtom; apply TyAEmptySet'; assumption | ].
                eapply TyEAccess; [ lookup_var' | eassumption ]. } }
      Qed.

      Definition idx_wf (tbl_v idx_v : value) : Prop :=
        idx_v = interp_expr map.empty (map.put map.empty hole tbl_v) to_idx.

      Lemma to_idx_wf : forall (v : value) (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          idx_wf v (interp_expr map.empty (map.put map.empty hole v) to_idx).
      Proof. intros; unfold idx_wf; reflexivity. Qed.

      (* ------------------------------------------------------------------
         What the index is, in Gallina.

         to_idx is two nested folds with a read-modify-write inside, so the
         mirror is two nested fold_rights.  The inner fold is what puts a row
         under many keys instead of one.
         ------------------------------------------------------------------ *)

      (* The bucket at a trigram once this row's key has gone in. *)
      Definition bucket_insert (k : value) (o : option value) : value :=
        match o with
        | None => VSet (set_insert k nil)
        | Some (VSet l) => VSet (set_insert k l)
        | Some _ => VUnit
        end.

      (* One trigram.  The key is the trigram itself: OTrigrams hands the
         fold the window, where the old body computed it from a text and a
         position. *)
      Definition tri_step (g k a : value) : value :=
        match a with
        | VDict d => VDict (dict_insert g (bucket_insert k (dict_lookup g d)) d)
        | _ => VUnit
        end.

      (* the trigrams of one PADDED word, which is what the index keys on *)
      Definition word_keys (w : string) : list value :=
        List.map VString (trigrams (pad w)).

      (* One word: its row's key goes into the bucket of each trigram. *)
      Definition tri_word_step (w : string) (k a : value) : value :=
        fold_right (fun g a' => tri_step g k a') a (word_keys w).

      Definition row_str (r : value) : string :=
        match row_key attr r with VString s => s | _ => EmptyString end.

      (* The WORDS the index keys on, as find_word splits them.
         Deliberately a different name from row_str, which is the text the
         PREDICATE reads -- the recheck has to see the row's real text, and
         the two must not be confused.  Every lemma below that is about the
         index's contents says row_wrds; every lemma about what a row
         contains says row_str. *)
      Definition row_wrds (r : value) : list string := words seps (row_str r).

      Definition tri_row_step (ws : list string) (k a : value) : value :=
        fold_right (fun w a' => tri_word_step w k a') a ws.

      Definition tri_entries (l : list value) : value :=
        fold_right (fun r a => tri_row_step (row_wrds r) (row_key key r) a)
          (VDict nil) l.

      (* The store is universally quantified in this group of lemmas: none of
         to_idx's parts mentions a global, so the index of a list of rows is
         the same whatever store it is computed in.  The maintenance rules
         need that, since they recompute the index where the table's own
         store is in scope. *)
      (* The row's words, which the outer fold runs over. *)
      Lemma interp_row_words : forall (store env : locals) r txt,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          interp_expr store env (row_words (EVar tup))
          = VList (List.map VString (words seps txt)).
      Proof.
        unfold row_words, row_key in *.
        intros * H_txt E_tup.
        rewrite interp_EBinop, interp_EAccess, interp_EVar, interp_EAtom.
        unfold get_local; rewrite E_tup.
        destruct r; try discriminate.
        rewrite H_txt. cbn [interp_binop interp_atom]. reflexivity.
      Qed.

      (* One word's trigrams, which the inner fold runs over.  The padding
         appears in this one proof, as it did at the row's text before. *)
      Lemma interp_word_trigrams : forall (store env : locals) w,
          map.get env wrd = Some (VString w) ->
          interp_expr store env (word_trigrams (EVar wrd)) = VList (word_keys w).
      Proof.
        unfold word_trigrams, word_text, word_keys, pad.
        intros * E_wrd.
        rewrite interp_EUnop, !interp_EBinop, interp_EVar, !interp_EAtom.
        unfold get_local; rewrite E_wrd.
        cbn [interp_unop interp_binop interp_atom]. reflexivity.
      Qed.

      Lemma interp_ELet : forall (store env : locals) e1 y e2,
          interp_expr store env (ELet e1 y e2)
          = interp_expr store (map.put env y (interp_expr store env e1)) e2.
      Proof. reflexivity. Qed.

      (* One trigram.  The fold hands the body the window itself, so this
         says nothing about a text or a position. *)
      Lemma interp_tri_insert : forall (store env : locals) r g a,
          map.get env tup = Some r ->
          map.get env gvar = Some g ->
          map.get env sacc = Some a ->
          interp_expr store env tri_insert_body = tri_step g (row_key key r) a.
      Proof.
        unfold tri_insert_body, row_pk, tri_step.
        intros * E_tup E_g E_sacc.
        cbn [interp_expr].
        unfold get_local, row_key; rewrite E_tup, E_g, E_sacc.
        destruct a as [ | | | | | | d | | | ]; try reflexivity.
        cbn [interp_binop interp_ternop].
        destruct (dict_lookup g d) as [ bk | ]; cbn [bucket_insert interp_atom].
        (* something already there: the key goes in beside it *)
        1:{ repeat rewrite_map_get_put_goal.
            rewrite ?E_tup, ?E_g. destruct bk; reflexivity. }
        (* nothing yet: the singleton *)
        1: reflexivity.
      Qed.

      (* The inner fold, over one word's trigrams. *)
      Lemma interp_tri_fold : forall (store env : locals) r a l,
          map.get env tup = Some r ->
          fold_right
            (fun g a' => interp_expr store
                           (map.put (map.put env gvar g) sacc a') tri_insert_body)
            a l
          = fold_right (fun g a' => tri_step g (row_key key r) a') a l.
      Proof.
        intros * E_tup.
        induction l as [ | g l IH ]; cbn [fold_right]; [ reflexivity | ].
        rewrite IH.
        apply interp_tri_insert.
        1:{ rewrite !map.get_put_diff by congruence. exact E_tup. }
        1:{ rewrite map.get_put_diff by congruence. apply map.get_put_same. }
        1: apply map.get_put_same.
      Qed.

      (* One word's contribution. *)
      Lemma interp_tri_word : forall (store env : locals) r w a,
          map.get env wrd = Some (VString w) ->
          map.get env tup = Some r ->
          map.get env wacc = Some a ->
          interp_expr store env tri_word_body = tri_word_step w (row_key key r) a.
      Proof.
        intros * E_wrd E_tup E_wacc.
        unfold tri_word_body, tri_word_step.
        rewrite interp_EFold.
        rewrite (interp_word_trigrams store env w E_wrd).
        rewrite interp_EVar; unfold get_local; rewrite E_wacc.
        apply interp_tri_fold; exact E_tup.
      Qed.

      (* The fold over one row's words. *)
      Lemma interp_tri_word_fold :
        forall (store env : locals) r a (ws : list string),
          map.get env tup = Some r ->
          fold_right
            (fun w a' => interp_expr store
                           (map.put (map.put env wrd w) wacc a') tri_word_body)
            a (List.map VString ws)
          = fold_right (fun w a' => tri_word_step w (row_key key r) a') a ws.
      Proof.
        intros * E_tup.
        induction ws as [ | w ws IH ]; cbn [List.map fold_right]; [ reflexivity | ].
        rewrite IH.
        apply interp_tri_word.
        1:{ rewrite map.get_put_diff by congruence. apply map.get_put_same. }
        1:{ rewrite !map.get_put_diff by congruence. exact E_tup. }
        1: apply map.get_put_same.
      Qed.

      (* One row's contribution: its words, each padded. *)
      Lemma interp_tri_row : forall (store env : locals) r txt a,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          map.get env acc = Some a ->
          interp_expr store env tri_row_body
          = tri_row_step (words seps txt) (row_key key r) a.
      Proof.
        intros * H_txt E_tup E_acc.
        unfold tri_row_body, tri_row_step.
        rewrite interp_EFold.
        rewrite (interp_row_words store env r txt H_txt E_tup).
        rewrite interp_EVar; unfold get_local; rewrite E_acc.
        apply interp_tri_word_fold; exact E_tup.
      Qed.

      (* The outer fold, over the rows.  Every row has to carry a string at
         attr, which is what is_tbl_ty asks of the table's type. *)
      Lemma interp_to_idx_fold : forall (store env : locals) (l : list value) a,
          Forall (fun r => exists txt, row_key attr r = VString txt) l ->
          fold_right
            (fun r a' => interp_expr store
                           (map.put (map.put env tup r) acc a') tri_row_body)
            a l
          = fold_right (fun r a' => tri_row_step (row_wrds r) (row_key key r) a') a l.
      Proof.
        intros store env l a H_all.
        induction l as [ | r l IH ]; cbn [fold_right]; [ reflexivity | ].
        invert_Forall.
        rewrite IH by assumption.
        lazymatch goal with H : exists _, _ |- _ => destruct H as [ txt H_txt ] end.
        assert (E_str : row_wrds r = words seps txt)
          by (unfold row_wrds, row_str; rewrite H_txt; reflexivity).
        rewrite E_str.
        apply interp_tri_row; [ exact H_txt | | apply map.get_put_same ].
        rewrite map.get_put_diff by congruence. apply map.get_put_same.
      Qed.

      Theorem fiat2_gallina_to_idx : forall (l : list value),
          Forall (fun r => exists txt, row_key attr r = VString txt) l ->
          interp_expr map.empty (map.put map.empty hole (VList l)) to_idx
          = tri_entries l.
      Proof.
        intros l H_all. unfold to_idx, tri_entries.
        rewrite interp_EFold, interp_EVar, interp_EAtom.
        unfold get_local; rewrite map.get_put_same.
        cbn [interp_atom].
        apply interp_to_idx_fold; exact H_all.
      Qed.

      Lemma typed_rows_have_text : forall (l : list value) rt,
          access_record rt attr = Success TString ->
          Forall (fun r => type_of_value r (TRecord rt)) l ->
          Forall (fun r => exists txt, row_key attr r = VString txt) l.
      Proof.
        intros l rt H_attr H_all.
        eapply Forall_impl; [ | exact H_all ].
        intros r H_r. unfold row_key.
        inversion H_r; subst.
        lazymatch goal with H : Forall2 _ ?rv rt |- _ => rename H into H_f2 end.
        pose proof H_f2 as H_keys.
        apply Forall2_split in H_keys as [ H_keys _ ].
        apply Forall2_fst_eq in H_keys.
        assert (H_in : In attr (List.map fst rt)).
        1:{ apply access_record_sound in H_attr.
            replace attr with (fst (attr, TString)) by reflexivity.
            apply in_map; exact H_attr. }
        rewrite <- H_keys in H_in.
        destruct (In_access_record _ _ _ H_in) as [ v E_v ].
        assert (H_proj : type_of_value v TString)
          by (eapply Forall2_access_record; [ exact H_f2 | exact E_v | exact H_attr ]).
        unfold record_proj; rewrite E_v.
        inversion H_proj; subst; eauto.
      Qed.

      (* ------------------------------------------------------------------
         What a lookup in this dictionary is good for.

         The claim worth proving is COMPLETENESS of the bucket: if a row's
         text contains the pattern, the row's key is in the bucket of the
         pattern's first trigram.  That is what lets a lookup rule replace a
         scan -- the bucket cannot miss a row.  Soundness in the other
         direction is deliberately not claimed, and is false: a trigram match
         does not imply a substring match, which is why a rule that reads this
         index must keep the containment test on the rows it finds.
         ------------------------------------------------------------------ *)

      (* k is among the keys stored at g. *)

      Definition key_at (g k a : value) : Prop :=
        match a with
        | VDict d =>
            match dict_lookup g d with
            | Some (VSet b) => In k b
            | _ => False
            end
        | _ => False
        end.

      (* Every bucket is a set.  Needed because bucket_insert mirrors
         EOptMatch, which cannot do anything sensible with a bucket that is
         not a set; the invariant says no such bucket ever arises. *)
      Definition buckets_are_sets (a : value) : Prop :=
        match a with
        | VDict d =>
            Forall (fun e => match snd e with VSet _ => True | _ => False end) d
        | _ => False
        end.

      Lemma Forall_dict_insert : forall (P : value * value -> Prop) k v d,
          Forall P d -> P (k, v) -> Forall P (dict_insert k v d).
      Proof.
        induction d as [ | [ k' v' ] d IH ]; cbn [dict_insert];
          intros H_all H_kv.
        1: constructor; [ exact H_kv | constructor ].
        invert_Forall.
        destruct (value_ltb k k'); [ | destruct (value_eqb k k') ].
        1: constructor; [ exact H_kv | constructor; assumption ].
        1: constructor; [ exact H_kv | assumption ].
        1: constructor; [ assumption | apply IH; assumption ].
      Qed.

      Lemma tri_step_buckets : forall g k a,
          buckets_are_sets a -> buckets_are_sets (tri_step g k a).
      Proof.
        unfold buckets_are_sets, tri_step; intros * H.
        destruct a as [ | | | | | | d | | | ]; try contradiction.
        apply Forall_dict_insert; [ exact H | ].
        cbn [snd]; unfold bucket_insert.
        destruct (dict_lookup g d) as [ b | ] eqn:E_lk; [ | exact I ].
        (* a bucket already there is a set, by the invariant *)
        apply DictIndexImpl.dict_lookup_Some_In in E_lk.
        eapply List.Forall_In in H; [ | exact E_lk ].
        cbn [snd] in H. destruct b; try contradiction. exact I.
      Qed.

      Lemma tri_fold_buckets : forall k l a,
          buckets_are_sets a ->
          buckets_are_sets (fold_right (fun g a' => tri_step g k a') a l).
      Proof.
        intros * H; induction l as [ | g l IH ]; cbn [fold_right];
          [ exact H | apply tri_step_buckets, IH ].
      Qed.

      Lemma tri_word_buckets : forall w k a,
          buckets_are_sets a -> buckets_are_sets (tri_word_step w k a).
      Proof. unfold tri_word_step; intros; apply tri_fold_buckets; assumption. Qed.

      Lemma tri_row_buckets : forall ws k a,
          buckets_are_sets a -> buckets_are_sets (tri_row_step ws k a).
      Proof.
        unfold tri_row_step; intros * H.
        induction ws as [ | w ws IH ]; cbn [fold_right];
          [ exact H | apply tri_word_buckets, IH ].
      Qed.


      (* ----------------------------------------------------------------
         AN INSERT AT THE END OF THE LIST, for the trigram member.

         The other indexes earn this from a step that commutes.  So does this
         one, but its step is not a single insert: a row contributes its KEY
         to the bucket of every trigram of every word of its text, so the
         per-row step is a fold of a fold.  Two rows still commute, and the
         reason is the SET: set_insert is both commutative and IDEMPOTENT, so
         two rows whose trigram sets OVERLAP may write the same bucket in
         either order, and a row's own repeated trigram costs nothing.

         buckets_are_sets is too weak to say it, though -- set_insert is a
         SORTED, deduplicating insert, so it commutes only on a CANONICAL
         set.  This is that invariant, and the four lemmas below are the
         four buckets_are_sets already has. *)
      Definition canonical_buckets (d : list (value * value)) : Prop :=
        Forall (fun e => match snd e with
                         | VSet l => NoDup l /\ StronglySorted value_leb l
                         | _ => False
                         end) d.

      (* dict_wf is in here because dict_insert_insert_same needs it: the
         same-trigram case of the commutation collapses two inserts at one
         key, and that is a fact about CANONICAL dictionaries. *)
      Definition buckets_are_canonical (a : value) : Prop :=
        match a with
        | VDict d => dict_wf d /\ canonical_buckets d
        | _ => False
        end.

      (* the set a trigram's bucket holds, and what tri_step does to it *)
      Definition bucket_set (d : list (value * value)) (g : value) : list value :=
        match dict_lookup g d with
        | Some (VSet l) => l
        | _ => nil
        end.

      Lemma bucket_set_canonical : forall d g,
          canonical_buckets d ->
          NoDup (bucket_set d g) /\ StronglySorted value_leb (bucket_set d g).
      Proof.
        unfold canonical_buckets, bucket_set; intros d g H.
        destruct (dict_lookup g d) as [ w | ] eqn:E_lk.
        2: split; [ constructor | constructor ].
        apply DictIndexImpl.dict_lookup_Some_In in E_lk.
        eapply List.Forall_In in H; [ | exact E_lk ].
        cbn [snd] in H. destruct w; try contradiction. exact H.
      Qed.

      Lemma bucket_insert_as_set : forall d g k,
          canonical_buckets d ->
          bucket_insert k (dict_lookup g d) = VSet (set_insert k (bucket_set d g)).
      Proof.
        unfold canonical_buckets, bucket_insert, bucket_set; intros d g k H.
        destruct (dict_lookup g d) as [ w | ] eqn:E_lk; [ | reflexivity ].
        apply DictIndexImpl.dict_lookup_Some_In in E_lk.
        eapply List.Forall_In in H; [ | exact E_lk ].
        cbn [snd] in H. destruct w; try contradiction. reflexivity.
      Qed.

      Lemma tri_step_canonical : forall g k a,
          buckets_are_canonical a -> buckets_are_canonical (tri_step g k a).
      Proof.
        unfold buckets_are_canonical, tri_step; intros * H.
        destruct a as [ | | | | | | d | | | ]; try contradiction.
        destruct H as [ H_wf H_b ]. split.
        1: apply dict_insert_preserve_dict_wf; exact H_wf.
        unfold canonical_buckets in *.
        apply Forall_dict_insert; [ exact H_b | ].
        cbn [snd]. rewrite bucket_insert_as_set by exact H_b.
        destruct (bucket_set_canonical d g H_b) as [ H_nd H_s ]. split.
        1: apply set_insert_preserve_NoDup; assumption.
        1: apply set_insert_preserve_SSorted; assumption.
      Qed.

      (* THE COMMUTATION.  Two trigram-and-key insertions commute: at the same
         trigram because set_insert does (and is idempotent, so two rows
         sharing a trigram is not a special case), and at different trigrams
         because dict_insert does. *)
      Lemma tri_step_comm : forall g1 k1 g2 k2 a,
          buckets_are_canonical a ->
          tri_step g1 k1 (tri_step g2 k2 a)
          = tri_step g2 k2 (tri_step g1 k1 a).
      Proof.
        unfold tri_step; intros * H.
        destruct a as [ | | | | | | d | | | ]; try contradiction.
        destruct H as [ H_wf H_b ].
        destruct (value_eqb g1 g2) eqn:E_g.
        1:{ (* one bucket, taken in both orders *)
            apply value_eqb_eq in E_g; subst g2.
            rewrite !DictIndexImpl.dict_lookup_insert_same.
            rewrite !(bucket_insert_as_set d g1 _ H_b).
            cbn [bucket_insert].
            rewrite !DictIndexImpl.dict_insert_insert_same by exact H_wf.
            destruct (bucket_set_canonical d g1 H_b) as [ H_nd H_s ].
            rewrite (set_insert_set_insert k1 k2 _ H_nd H_s). reflexivity. }
        1:{ (* different trigrams: neither insertion sees the other's bucket *)
            assert (H_ne : g1 <> g2)
              by (intro H_eq; rewrite H_eq, value_eqb_refl in E_g; discriminate).
            rewrite (DictIndexImpl.dict_lookup_insert_diff g1 g2) by exact H_ne.
            rewrite (DictIndexImpl.dict_lookup_insert_diff g2 g1)
              by (apply not_eq_sym; exact H_ne).
            f_equal.
            apply DictIndexImpl.dict_insert_comm; [ exact H_ne | exact H_wf ]. }
      Qed.

      Lemma tri_fold_canonical : forall k l a,
          buckets_are_canonical a ->
          buckets_are_canonical (fold_right (fun g a' => tri_step g k a') a l).
      Proof.
        intros * H; induction l as [ | g l IH ]; cbn [fold_right];
          [ exact H | apply tri_step_canonical, IH ].
      Qed.

      Lemma tri_word_canonical : forall w k a,
          buckets_are_canonical a -> buckets_are_canonical (tri_word_step w k a).
      Proof.
        unfold tri_word_step; intros; apply tri_fold_canonical; assumption.
      Qed.

      Lemma tri_row_canonical : forall ws k a,
          buckets_are_canonical a -> buckets_are_canonical (tri_row_step ws k a).
      Proof.
        unfold tri_row_step; intros * H.
        induction ws as [ | w ws IH ]; cbn [fold_right];
          [ exact H | apply tri_word_canonical, IH ].
      Qed.

      (* ----------------------------------------------------------------
         Lifting the commutation through a fold.  TWO levels of fold sit
         between tri_step and the per-row step -- trigrams within a word,
         words within a row -- so these are applied twice, and then once more
         to push a whole row past the fold over rows. *)
      (* Generic, and polymorphic in the element type on purpose: the three
         levels fold over trigrams (values), words (strings) and rows
         (values). *)
      Lemma fold_pres :
        forall (A B : Type) (g : A -> B -> B) (P : B -> Prop) l b,
          (forall y a, P a -> P (g y a)) -> P b -> P (fold_right g b l).
      Proof.
        intros * H_pres H_b; induction l as [ | y l IH ]; cbn [fold_right];
          [ exact H_b | apply H_pres, IH ].
      Qed.

      Lemma fold_push :
        forall (A B : Type) (f g : A -> B -> B) (P : B -> Prop) x l b,
          (forall y a, P a -> P (g y a)) ->
          (forall y a, P a -> f x (g y a) = g y (f x a)) ->
          P b ->
          f x (fold_right g b l) = fold_right g (f x b) l.
      Proof.
        intros * H_pres H_comm H_b.
        induction l as [ | y l IH ]; cbn [fold_right]; [ reflexivity | ].
        rewrite H_comm by (eapply fold_pres; eassumption).
        rewrite IH; reflexivity.
      Qed.

      Lemma fold_two_comm :
        forall (A B : Type) (f g : A -> B -> B) (P : B -> Prop) l1 l2 b,
          (forall y a, P a -> P (f y a)) ->
          (forall y a, P a -> P (g y a)) ->
          (forall x y a, P a -> f x (g y a) = g y (f x a)) ->
          P b ->
          fold_right f (fold_right g b l2) l1
          = fold_right g (fold_right f b l1) l2.
      Proof.
        intros * H_f H_g H_comm H_b.
        induction l1 as [ | x l1 IH ]; cbn [fold_right]; [ reflexivity | ].
        rewrite IH.
        eapply fold_push with (P := P);
          [ exact H_g | intros; apply H_comm; assumption
          | eapply fold_pres; eassumption ].
      Qed.

      Lemma tri_word_step_comm : forall w1 k1 w2 k2 a,
          buckets_are_canonical a ->
          tri_word_step w1 k1 (tri_word_step w2 k2 a)
          = tri_word_step w2 k2 (tri_word_step w1 k1 a).
      Proof.
        unfold tri_word_step; intros * H.
        eapply fold_two_comm with (P := buckets_are_canonical);
          [ intros; apply tri_step_canonical; assumption
          | intros; apply tri_step_canonical; assumption
          | intros; apply tri_step_comm; assumption
          | exact H ].
      Qed.

      Lemma tri_row_step_comm : forall ws1 k1 ws2 k2 a,
          buckets_are_canonical a ->
          tri_row_step ws1 k1 (tri_row_step ws2 k2 a)
          = tri_row_step ws2 k2 (tri_row_step ws1 k1 a).
      Proof.
        unfold tri_row_step; intros * H.
        eapply fold_two_comm with (P := buckets_are_canonical);
          [ intros; apply tri_word_canonical; assumption
          | intros; apply tri_word_canonical; assumption
          | intros; apply tri_word_step_comm; assumption
          | exact H ].
      Qed.

      Lemma buckets_are_canonical_nil : buckets_are_canonical (VDict nil).
      Proof. split; [ exact I | constructor ]. Qed.

      (* THE FACT THE RULE NEEDS: appending a row at the end builds the same
         trigram index as consing it at the front. *)
      Lemma tri_entries_app_singleton : forall l r,
          tri_entries (l ++ [r]) = tri_entries (r :: l).
      Proof.
        unfold tri_entries; intros l r.
        rewrite fold_right_app. cbn [fold_right]. symmetry.
        eapply fold_push with (P := buckets_are_canonical);
          [ intros; apply tri_row_canonical; assumption
          | intros; apply tri_row_step_comm; assumption
          | exact buckets_are_canonical_nil ].
      Qed.
      Lemma tri_entries_buckets : forall l a,
          buckets_are_sets a ->
          buckets_are_sets
            (fold_right (fun r a' => tri_row_step (row_wrds r) (row_key key r) a') a l).
      Proof.
        intros * H; induction l as [ | r l IH ]; cbn [fold_right]; [ exact H | ].
        apply tri_row_buckets, IH.
      Qed.

      (* Nothing ever removes a key from a bucket. *)
      Lemma tri_step_monotone : forall g' k' g k a,
          key_at g k a -> key_at g k (tri_step g' k' a).
      Proof.
        unfold key_at, tri_step; intros * H.
        destruct a as [ | | | | | | d | | | ]; try contradiction.
        destruct (value_eqb_dec g' g) as [ E | E ].
        1:{ subst g'. rewrite DictIndexImpl.dict_lookup_insert_same.
            unfold bucket_insert.
            destruct (dict_lookup g d) as [ b | ]; [ | contradiction ].
            destruct b; try contradiction.
            apply set_insert_incl_r; right; exact H. }
        1:{ rewrite DictIndexImpl.dict_lookup_insert_diff by congruence. exact H. }
      Qed.

      Lemma tri_fold_monotone : forall k' g k l a,
          key_at g k a ->
          key_at g k (fold_right (fun g'' a' => tri_step g'' k' a') a l).
      Proof.
        intros * H; induction l as [ | g' l IH ]; cbn [fold_right];
          [ exact H | apply tri_step_monotone, IH ].
      Qed.

      Lemma tri_word_monotone : forall w k' g k a,
          key_at g k a -> key_at g k (tri_word_step w k' a).
      Proof. unfold tri_word_step; intros; apply tri_fold_monotone; assumption. Qed.

      Lemma tri_row_monotone : forall ws k' g k a,
          key_at g k a -> key_at g k (tri_row_step ws k' a).
      Proof.
        unfold tri_row_step; intros * H.
        induction ws as [ | w ws IH ]; cbn [fold_right];
          [ exact H | apply tri_word_monotone, IH ].
      Qed.

      Lemma tri_entries_monotone : forall g k l a,
          key_at g k a ->
          key_at g k
            (fold_right (fun r a' => tri_row_step (row_wrds r) (row_key key r) a') a l).
      Proof.
        intros * H; induction l as [ | r l IH ]; cbn [fold_right]; [ exact H | ].
        apply tri_row_monotone, IH.
      Qed.

      (* And a trigram among those folded over puts the key there.  Simpler
         than it was: the fold runs over the trigrams themselves, so there is
         no position to map through. *)
      Lemma tri_fold_establishes : forall k g l a,
          buckets_are_sets a ->
          In g l ->
          key_at g k (fold_right (fun g' a' => tri_step g' k a') a l).
      Proof.
        intros * H_bs H_in.
        induction l as [ | g' l IH ]; cbn [fold_right] in H_in |- *.
        1: contradiction.
        destruct H_in as [ E_g | H_in ].
        (* here: the key goes into this bucket *)
        1:{ subst g'.
            pose proof (tri_fold_buckets k l a H_bs) as H_bs'.
            (* name the accumulator before destructing it, so the invariant
               about it is destructed too *)
            remember (fold_right (fun g' a' => tri_step g' k a') a l) as A eqn:E_A.
            unfold buckets_are_sets in H_bs'.
            destruct A as [ | | | | | | d | | | ]; try contradiction.
            unfold key_at, tri_step.
            rewrite DictIndexImpl.dict_lookup_insert_same.
            unfold bucket_insert.
            destruct (dict_lookup g d) as [ b | ] eqn:E_lk.
            1:{ apply DictIndexImpl.dict_lookup_Some_In in E_lk.
                eapply List.Forall_In in H_bs'; [ | exact E_lk ].
                cbn [snd] in H_bs'. destruct b; try contradiction.
                apply set_insert_incl_r; left; reflexivity. }
            1: apply set_insert_incl_r; left; reflexivity. }
        (* further on: whatever goes in later cannot take it out *)
        1: apply tri_step_monotone, IH; exact H_in.
      Qed.

      Lemma tri_word_establishes : forall w k g a,
          buckets_are_sets a ->
          In g (word_keys w) ->
          key_at g k (tri_word_step w k a).
      Proof.
        unfold tri_word_step; intros; apply tri_fold_establishes; assumption.
      Qed.

      Lemma tri_row_establishes : forall ws w k g a,
          buckets_are_sets a ->
          In w ws ->
          In g (word_keys w) ->
          key_at g k (tri_row_step ws k a).
      Proof.
        unfold tri_row_step; intros * H_bs H_w H_g.
        induction ws as [ | w' ws IH ]; cbn [fold_right] in H_w |- *;
          [ contradiction | ].
        destruct H_w as [ E | H_w ].
        1:{ subst w'. apply tri_word_establishes; [ | exact H_g ].
            clear IH. induction ws as [ | w'' ws IH ]; cbn [fold_right];
              [ exact H_bs | apply tri_word_buckets, IH ]. }
        1: apply tri_word_monotone, IH; exact H_w.
      Qed.

      (* The other half: a key in a bucket came from a row of the table.
         Not the same as soundness of the SEARCH -- the row's text need not
         contain the pattern, only one trigram of it -- but it is what keeps a
         lookup from inventing rows, and so what a rewrite needs beside
         completeness. *)
      Lemma tri_step_inv : forall g' k' g k a,
          key_at g k (tri_step g' k' a) -> k = k' \/ key_at g k a.
      Proof.
        unfold key_at, tri_step; intros * H.
        destruct a as [ | | | | | | d | | | ]; try contradiction.
        destruct (value_eqb_dec g' g) as [ E | E ].
        1:{ subst g'. rewrite DictIndexImpl.dict_lookup_insert_same in H.
            unfold bucket_insert in H.
            destruct (dict_lookup g d) as [ b | ].
            1:{ destruct b; try contradiction.
                apply set_insert_incl in H; intuition auto. }
            1:{ apply set_insert_incl in H; cbn in H; intuition auto. } }
        1:{ rewrite DictIndexImpl.dict_lookup_insert_diff in H by congruence.
            right; exact H. }
      Qed.

      Lemma tri_fold_inv : forall k' g k l a,
          key_at g k (fold_right (fun g'' a' => tri_step g'' k' a') a l) ->
          k = k' \/ key_at g k a.
      Proof.
        intros * H; induction l as [ | g' l IH ]; cbn [fold_right] in H;
          [ right; exact H | ].
        apply tri_step_inv in H; intuition auto.
      Qed.

      Lemma tri_word_inv : forall w k' g k a,
          key_at g k (tri_word_step w k' a) -> k = k' \/ key_at g k a.
      Proof. unfold tri_word_step; intros * H; eapply tri_fold_inv; exact H. Qed.

      Lemma tri_row_inv : forall ws k' g k a,
          key_at g k (tri_row_step ws k' a) -> k = k' \/ key_at g k a.
      Proof.
        unfold tri_row_step; intros * H.
        induction ws as [ | w ws IH ]; cbn [fold_right] in H; [ right; exact H | ].
        apply tri_word_inv in H; intuition auto.
      Qed.

      Lemma tri_entries_inv : forall l g k,
          key_at g k (tri_entries l) -> exists r, In r l /\ row_key key r = k.
      Proof.
        unfold tri_entries; intros l g k.
        induction l as [ | r l IH ]; cbn [fold_right]; intros H.
        1:{ unfold key_at in H; cbn [dict_lookup] in H; contradiction. }
        apply tri_row_inv in H as [ E | H ].
        1: exists r; split; [ left; reflexivity | symmetry; exact E ].
        1:{ destruct (IH H) as [ r' [ H_in E ] ].
            exists r'; split; [ right; exact H_in | exact E ]. }
      Qed.

      Lemma In_word_keys : forall w g,
          In g (trigrams (pad w)) -> In (VString g) (word_keys w).
      Proof.
        unfold word_keys; intros w g H_in.
        apply in_map_iff. exists g; split; [ reflexivity | exact H_in ].
      Qed.

      (* The claim, for ANY trigram of ANY of the row's padded words -- the
         strings the index KEYS ON.  Stated this way rather than for the
         pattern's first trigram, because the all-trigram lookup needs one
         bucket per trigram of the pattern and they are all instances of
         this. *)
      Theorem tri_lookup_complete_at_word : forall (l : list value) r w g,
          In r l ->
          In w (row_wrds r) ->
          In g (trigrams (pad w)) ->
          key_at (VString g) (row_key key r) (tri_entries l).
      Proof.
        intros l r w g H_in H_w H_tri.
        apply In_word_keys in H_tri.
        (* split the table at the row *)
        apply in_split in H_in as [ l1 [ l2 E_l ] ]; subst l.
        unfold tri_entries; rewrite fold_right_app.
        apply tri_entries_monotone.
        cbn [fold_right].
        eapply tri_row_establishes; [ | exact H_w | exact H_tri ].
        apply tri_entries_buckets. cbn [buckets_are_sets]. constructor.
      Qed.

      (* And the same for a trigram of a PATTERN that occurs in the row --
         which is what every lookup rule has in hand.

         This is where tokenizing the index is paid for.  The premise can no
         longer be "g is a trigram of the row's text": a trigram straddling a
         separator, like "h J" in "Smith Jones", is a trigram of the text and
         is in no bucket, because the index keys on the words.  What is true
         is that a SEPARATOR-FREE pattern occurring in the text lies inside
         one word (StringFacts.sep_free_inside_word), so its trigrams are
         trigrams of that word's padded form, and those are keys.

         The hypothesis is exactly what the rule's runtime guard tests, so
         nothing is lost in translation: a pattern with no separator in it. *)
      Theorem tri_lookup_complete_at : forall (l : list value) r p g m,
          In r l ->
          sep_free seps p = true ->
          p <> EmptyString ->
          String.index 0 p (row_str r) = Some m ->
          In g (trigrams p) ->
          key_at (VString g) (row_key key r) (tri_entries l).
      Proof.
        intros l r p g m H_in H_free H_ne E_idx H_tri.
        apply index_decomp in E_idx as [ a [ b E_s ] ].
        destruct (trigrams_inside_word seps p a b g H_free H_ne H_tri)
          as [ w [ H_w H_g ] ].
        eapply tri_lookup_complete_at_word; [ exact H_in | | exact H_g ].
        unfold row_wrds. rewrite E_s. exact H_w.
      Qed.

      (* And in the bucket of EVERY trigram of the pattern -- the fact the
         all-trigram rule uses, so that intersecting the buckets keeps the
         row.  No length hypothesis: a pattern shorter than three characters
         has no trigrams, so the premise is unsatisfiable rather than false. *)
      Theorem tri_lookup_complete_all : forall (l : list value) r p g,
          In r l ->
          sep_free seps p = true ->
          p <> EmptyString ->
          String.index 0 p (row_str r) <> None ->
          In g (trigrams p) ->
          key_at (VString g) (row_key key r) (tri_entries l).
      Proof.
        intros l r p g H_in H_free H_ne H_occ H_tri.
        destruct (String.index 0 p (row_str r)) as [ m | ] eqn:E_idx;
          [ | contradiction ].
        eapply tri_lookup_complete_at;
          [ exact H_in | exact H_free | exact H_ne | exact E_idx | exact H_tri ].
      Qed.

      (* A row whose text contains the pattern has its key in the bucket of
         the pattern's FIRST trigram -- the fact the single-probe rule uses. *)
      Theorem tri_lookup_complete : forall (l : list value) r p,
          In r l ->
          sep_free seps p = true ->
          3 <= String.length p ->
          String.index 0 p (row_str r) <> None ->
          key_at (VString (String.substring 0 3 p)) (row_key key r) (tri_entries l).
      Proof.
        intros l r p H_in H_free H_len H_occ.
        eapply tri_lookup_complete_all;
          [ exact H_in | exact H_free | | exact H_occ | ].
        1:{ destruct p; [ cbn [String.length] in H_len; lia | discriminate ]. }
        1: apply In_trigrams_first; exact H_len.
      Qed.


      Instance trigram_idx : IndexInterface.index :=
        IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

      Instance trigram_idx_ok : IndexInterface.ok trigram_idx idx_wf :=
        IndexInterface.Build_ok trigram_idx idx_wf idx_ty_wf to_idx_ty to_idx_wf.

      (* ==================================================================
         Removing a row from the index.

         to_idx is a fold, so ADDING a row needs no theory at all: the
         index of r :: l is the index of l with one more step run on it.
         REMOVING one is not like that.  The index has to come out the same
         as a recomputation over the smaller table, and that forces two
         things this section is about: the row's key leaves the bucket of
         each of the row's trigrams, and an entry whose bucket loses its
         last key has to GO, since a recomputation over a table no row of
         which contains that trigram holds no entry for it.

         Everything here is at the level of the dictionary rather than the
         value, since an equality of dictionaries is what has to be proved.
         ================================================================== *)

      (* the index's steps, on dictionaries.  The trigram is the key, so
         the step takes the window the fold hands it and nothing else. *)
      Definition tri_step_d (k g : value)
        (d : list (value * value)) : list (value * value) :=
        dict_insert g (bucket_insert k (dict_lookup g d)) d.

      Lemma tri_step_d_eq : forall k g (d : list (value * value)),
          tri_step_d k g d
          = dict_insert g (bucket_insert k (dict_lookup g d)) d.
      Proof. reflexivity. Qed.

      Definition tri_word_step_d (w : string) (k : value)
        (d : list (value * value)) : list (value * value) :=
        fold_right (tri_step_d k) d (word_keys w).

      Definition tri_row_step_d (ws : list string) (k : value)
        (d : list (value * value)) : list (value * value) :=
        fold_right (fun w d' => tri_word_step_d w k d') d ws.

      Definition tri_dict (l : list value) : list (value * value) :=
        fold_right (fun r d => tri_row_step_d (row_wrds r) (row_key key r) d) nil l.

      (* folded equations for the two nested folds *)
      Lemma tri_word_step_d_eq : forall w k d,
          tri_word_step_d w k d = fold_right (tri_step_d k) d (word_keys w).
      Proof. reflexivity. Qed.

      Lemma tri_row_step_d_cons : forall w ws k d,
          tri_row_step_d (w :: ws) k d
          = tri_word_step_d w k (tri_row_step_d ws k d).
      Proof. reflexivity. Qed.

      Lemma tri_word_step_VDict : forall w k d,
          tri_word_step w k (VDict d) = VDict (tri_word_step_d w k d).
      Proof.
        unfold tri_word_step, tri_word_step_d; intros w k d.
        induction (word_keys w) as [ | g gs IH ]; cbn [fold_right];
          [ reflexivity | ].
        rewrite IH. reflexivity.
      Qed.

      Lemma tri_row_step_VDict : forall ws k d,
          tri_row_step ws k (VDict d) = VDict (tri_row_step_d ws k d).
      Proof.
        unfold tri_row_step, tri_row_step_d; intros ws k d.
        induction ws as [ | w ws IH ]; cbn [fold_right]; [ reflexivity | ].
        rewrite IH. apply tri_word_step_VDict.
      Qed.

      Lemma tri_entries_VDict : forall l, tri_entries l = VDict (tri_dict l).
      Proof.
        unfold tri_entries, tri_dict.
        induction l as [ | r l IH ]; cbn [fold_right]; [ reflexivity | ].
        rewrite IH. apply tri_row_step_VDict.
      Qed.

      (* the bucket at g, empty if there is no entry *)
      Definition bucket_of (g : value) (d : list (value * value)) : list value :=
        match dict_lookup g d with
        | Some (VSet b) => b
        | _ => nil
        end.

      Definition tri_keys (ws : list string) : list value :=
        flat_map word_keys ws.

      (* and the keys the index ought to hold at g: those of the rows one
         of whose words has g among its trigrams *)
      Definition keys_at (g : value) (l : list value) : list value :=
        fold_right (fun r b => if set_mem g (tri_keys (row_wrds r))
                               then set_insert (row_key key r) b
                               else b) nil l.

      Lemma set_mem_app : forall (g : value) l1 l2,
          set_mem g (l1 ++ l2)%list = (set_mem g l1 || set_mem g l2)%bool.
      Proof. intros; apply existsb_app. Qed.

      Lemma tri_keys_cons : forall w ws,
          tri_keys (w :: ws) = (word_keys w ++ tri_keys ws)%list.
      Proof. reflexivity. Qed.

      (* What the index's dictionaries look like: canonical, and every
         entry a NONEMPTY set of keys.  The second half is what makes the
         collapse above forced, and it is preserved by both steps. *)
      Definition tri_wf (d : list (value * value)) : Prop :=
        dict_wf d /\ Forall (fun e => exists b, snd e = VSet b /\ b <> nil) d.

      Lemma set_insert_not_nil : forall (v : value) l, set_insert v l <> nil.
      Proof.
        destruct l as [ | v' l ]; cbn [set_insert]; [ discriminate | ].
        destruct (value_ltb v v'); [ discriminate | ].
        destruct (value_eqb v v'); discriminate.
      Qed.

      Lemma value_ltb_refl : forall (v : value), value_ltb v v = false.
      Proof.
        intros v; unfold value_ltb; rewrite value_compare_refl; reflexivity.
      Qed.

      Lemma set_insert_idem : forall (v : value) l,
          set_insert v (set_insert v l) = set_insert v l.
      Proof.
        induction l as [ | v' l IH ]; cbn [set_insert].
        1: rewrite value_ltb_refl, value_eqb_refl; reflexivity.
        destruct (value_ltb v v') eqn:E_lt.
        1: cbn [set_insert]; rewrite value_ltb_refl, value_eqb_refl; reflexivity.
        destruct (value_eqb v v') eqn:E_eq.
        1: cbn [set_insert]; rewrite E_lt, E_eq; reflexivity.
        1: cbn [set_insert]; rewrite E_lt, E_eq, IH; reflexivity.
      Qed.

      Lemma Forall_dict_insert_entry :
        forall (P : value * value -> Prop) k (v : value) d,
          P (k, v) -> Forall P d -> Forall P (dict_insert k v d).
      Proof.
        intros * H_P H_d. apply Forall_forall; intros e H_in.
        apply dict_insert_incl in H_in; cbn [In] in H_in.
        destruct H_in as [ E | H_in ]; [ subst e; exact H_P | ].
        rewrite Forall_forall in H_d; apply H_d; exact H_in.
      Qed.

      Lemma tri_step_d_preserve_tri_wf : forall k g d,
          tri_wf d -> tri_wf (tri_step_d k g d).
      Proof.
        unfold tri_wf, tri_step_d; intros * [ H_wf H_ne ].
        split; [ apply dict_insert_preserve_dict_wf; exact H_wf | ].
        apply Forall_dict_insert_entry; [ | exact H_ne ].
        cbn [snd]. unfold bucket_insert.
        destruct (dict_lookup g d) as [ bk | ] eqn:E.
        1:{ (* the entry that was there is a set, by the invariant *)
            apply (Forall_dict_lookup _ _ _ _ H_ne) in E as [ b [ E_b _ ] ].
            cbn [snd] in E_b; subst bk.
            exists (set_insert k b); split; [ reflexivity | apply set_insert_not_nil ]. }
        1: exists (set_insert k nil); split; [ reflexivity | apply set_insert_not_nil ].
      Qed.

      Lemma tri_fold_d_preserve_tri_wf : forall k gs d,
          tri_wf d -> tri_wf (fold_right (tri_step_d k) d gs).
      Proof.
        intros k gs d H.
        induction gs as [ | g gs IH ]; cbn [fold_right]; [ exact H | ].
        apply tri_step_d_preserve_tri_wf; exact IH.
      Qed.

      Lemma tri_word_step_d_preserve_tri_wf : forall w k d,
          tri_wf d -> tri_wf (tri_word_step_d w k d).
      Proof. intros; apply tri_fold_d_preserve_tri_wf; assumption. Qed.

      Lemma tri_row_step_d_preserve_tri_wf : forall ws k d,
          tri_wf d -> tri_wf (tri_row_step_d ws k d).
      Proof.
        intros ws k d H.
        induction ws as [ | w ws IH ]; [ exact H | ].
        rewrite tri_row_step_d_cons.
        apply tri_word_step_d_preserve_tri_wf; exact IH.
      Qed.

      Lemma tri_dict_tri_wf : forall l, tri_wf (tri_dict l).
      Proof.
        unfold tri_dict; induction l as [ | r l IH ]; cbn [fold_right].
        1: split; [ exact I | constructor ].
        1: apply tri_row_step_d_preserve_tri_wf; exact IH.
      Qed.

      (* One word's step, bucket by bucket: it touches the buckets of its
         own trigrams and nothing else.  Both lemmas are about a fold over
         an ARBITRARY list of trigrams. *)
      Lemma tri_fold_d_lookup_other : forall k gs d g,
          set_mem g gs = false ->
          dict_lookup g (fold_right (tri_step_d k) d gs) = dict_lookup g d.
      Proof.
        intros k gs d g.
        induction gs as [ | g' gs IH ]; cbn [fold_right]; [ reflexivity | ].
        intros H_mem.
        unfold set_mem in H_mem; cbn [existsb] in H_mem.
        rewrite Bool.orb_false_iff in H_mem; destruct H_mem as [ H_g H_gs ].
        rewrite tri_step_d_eq.
        rewrite DictIndexImpl.dict_lookup_insert_diff
          by (apply value_eqb_neq; exact H_g).
        apply IH; exact H_gs.
      Qed.

      Lemma tri_fold_d_lookup_same : forall k gs d g,
          tri_wf d ->
          set_mem g gs = true ->
          dict_lookup g (fold_right (tri_step_d k) d gs)
          = Some (VSet (set_insert k (bucket_of g d))).
      Proof.
        intros k gs d g H_wf.
        induction gs as [ | g' gs IH ]; cbn [fold_right]; [ discriminate | ].
        intros H_mem.
        unfold set_mem in H_mem; cbn [existsb] in H_mem.
        rewrite Bool.orb_true_iff in H_mem.
        destruct (value_eqb g g') eqn:E_g.
        1:{ (* this trigram is g: the key goes in here, on top of whatever
               the later trigrams left *)
            apply value_eqb_eq in E_g; subst g'.
            rewrite tri_step_d_eq, DictIndexImpl.dict_lookup_insert_same.
            destruct (set_mem g gs) eqn:E_gs.
            1:{ rewrite (IH eq_refl). unfold bucket_insert.
                rewrite set_insert_idem; reflexivity. }
            1:{ rewrite (tri_fold_d_lookup_other k gs d g E_gs).
                (* the bucket that was there is a set, by the invariant *)
                unfold bucket_insert, bucket_of.
                destruct (dict_lookup g d) as [ bk | ] eqn:E; [ | reflexivity ].
                destruct H_wf as [ _ H_ne ].
                apply (Forall_dict_lookup _ _ _ _ H_ne) in E as [ b [ E_b _ ] ].
                cbn [snd] in E_b; subst bk; reflexivity. } }
        1:{ (* it is not: this trigram leaves g alone *)
            destruct H_mem as [ E | H_gs ]; [ congruence | ].
            rewrite tri_step_d_eq.
            rewrite DictIndexImpl.dict_lookup_insert_diff
              by (apply value_eqb_neq; exact E_g).
            apply IH; exact H_gs. }
      Qed.

      Corollary tri_word_step_d_lookup_other : forall w k d g,
          set_mem g (word_keys w) = false ->
          dict_lookup g (tri_word_step_d w k d) = dict_lookup g d.
      Proof. intros; apply tri_fold_d_lookup_other; assumption. Qed.

      Corollary tri_word_step_d_lookup_same : forall w k d g,
          tri_wf d ->
          set_mem g (word_keys w) = true ->
          dict_lookup g (tri_word_step_d w k d)
          = Some (VSet (set_insert k (bucket_of g d))).
      Proof. intros; apply tri_fold_d_lookup_same; assumption. Qed.

      (* and one ROW's step, which is the same statement one fold out: the
         keys it touches are the union over its words *)
      Lemma tri_row_step_d_lookup_other : forall ws k d g,
          set_mem g (tri_keys ws) = false ->
          dict_lookup g (tri_row_step_d ws k d) = dict_lookup g d.
      Proof.
        intros ws k d g; induction ws as [ | w ws IH ]; [ reflexivity | ].
        rewrite tri_keys_cons, set_mem_app, Bool.orb_false_iff.
        intros [ H_w H_ws ].
        rewrite tri_row_step_d_cons.
        rewrite (tri_word_step_d_lookup_other w k _ g H_w).
        apply IH; exact H_ws.
      Qed.

      Lemma tri_row_step_d_lookup_same : forall ws k d g,
          tri_wf d ->
          set_mem g (tri_keys ws) = true ->
          dict_lookup g (tri_row_step_d ws k d)
          = Some (VSet (set_insert k (bucket_of g d))).
      Proof.
        intros ws k d g H_wf; induction ws as [ | w ws IH ]; [ discriminate | ].
        rewrite tri_keys_cons, set_mem_app, Bool.orb_true_iff.
        intros H_mem.
        rewrite tri_row_step_d_cons.
        destruct (set_mem g (word_keys w)) eqn:E_w.
        2:{ destruct H_mem as [ E | H_ws ]; [ congruence | ].
            rewrite (tri_word_step_d_lookup_other w k _ g E_w).
            apply IH; exact H_ws. }
        rewrite (tri_word_step_d_lookup_same w k _ g
                   (tri_row_step_d_preserve_tri_wf ws k d H_wf) E_w).
        (* and the bucket the inner word found is the one the earlier words
           left, which is d's own whether or not they touched it *)
        do 2 f_equal.
        destruct (set_mem g (tri_keys ws)) eqn:E_ws.
        1:{ unfold bucket_of at 1; rewrite (IH eq_refl); apply set_insert_idem. }
        1:{ unfold bucket_of at 1;
            rewrite (tri_row_step_d_lookup_other ws k d g E_ws); reflexivity. }
      Qed.

      (* folded equations for the fold over rows *)
      Lemma tri_dict_cons : forall r l,
          tri_dict (r :: l)
          = tri_row_step_d (row_wrds r) (row_key key r) (tri_dict l).
      Proof. reflexivity. Qed.

      Lemma keys_at_cons : forall g r l,
          keys_at g (r :: l)
          = if set_mem g (tri_keys (row_wrds r))
            then set_insert (row_key key r) (keys_at g l)
            else keys_at g l.
      Proof. reflexivity. Qed.

      (* and so the index's bucket at g holds exactly the keys it ought to:
         those of the rows one of whose words has g among its trigrams, and
         no entry at all when there are none *)
      Lemma tri_dict_lookup : forall l g,
          dict_lookup g (tri_dict l)
          = match keys_at g l with
            | nil => None
            | b => Some (VSet b)
            end.
      Proof.
        intros l g.
        induction l as [ | r l IH ]; [ reflexivity | ].
        rewrite tri_dict_cons, keys_at_cons.
        destruct (set_mem g (tri_keys (row_wrds r))) eqn:E_mem.
        1:{ rewrite (tri_row_step_d_lookup_same _ _ _ _ (tri_dict_tri_wf l) E_mem).
            unfold bucket_of; rewrite IH.
            destruct (keys_at g l) as [ | v b ] eqn:E_b.
            1:{ destruct (set_insert (row_key key r) nil) eqn:E_i;
                [ exfalso; eapply set_insert_not_nil; exact E_i | reflexivity ]. }
            1:{ destruct (set_insert (row_key key r) (v :: b)) eqn:E_i;
                [ exfalso; eapply set_insert_not_nil; exact E_i | reflexivity ]. } }
        1: rewrite <- IH; apply tri_row_step_d_lookup_other; exact E_mem.
      Qed.

      (* ------------------------------------------------------------------
         The other direction: one row's keys coming out.

         bucket_remove is what OSetDiff against the singleton computes, and
         the emptiness test is on the RESULT of the removal rather than on
         the bucket being exactly the singleton.  Those agree when buckets
         are duplicate-free, but testing the result needs no such invariant:
         the insert branch then knows its bucket is nonempty from the test
         itself.
         ------------------------------------------------------------------ *)
      Definition bucket_remove (k : value) (b : list value) : list value :=
        filter (fun v => negb (set_mem v (set_insert k nil))) b.

      Definition tri_unstep_d (k g : value)
        (d : list (value * value)) : list (value * value) :=
        match dict_lookup g d with
        | Some (VSet b) =>
            if value_eqb (VSet (bucket_remove k b)) (VSet nil)
            then dict_delete g d
            else dict_insert g (VSet (bucket_remove k b)) d
        | _ => d
        end.

      Definition tri_word_unstep_d (w : string) (k : value)
        (d : list (value * value)) : list (value * value) :=
        fold_right (tri_unstep_d k) d (word_keys w).

      Definition tri_row_unstep_d (ws : list string) (k : value)
        (d : list (value * value)) : list (value * value) :=
        fold_right (fun w d' => tri_word_unstep_d w k d') d ws.

      Lemma tri_unstep_d_eq : forall k g (d : list (value * value)),
          tri_unstep_d k g d
          = match dict_lookup g d with
            | Some (VSet b) =>
                if value_eqb (VSet (bucket_remove k b)) (VSet nil)
                then dict_delete g d
                else dict_insert g (VSet (bucket_remove k b)) d
            | _ => d
            end.
      Proof. reflexivity. Qed.

      Lemma tri_word_unstep_d_eq : forall w k d,
          tri_word_unstep_d w k d = fold_right (tri_unstep_d k) d (word_keys w).
      Proof. reflexivity. Qed.

      Lemma tri_row_unstep_d_cons : forall w ws k d,
          tri_row_unstep_d (w :: ws) k d
          = tri_word_unstep_d w k (tri_row_unstep_d ws k d).
      Proof. reflexivity. Qed.

      Lemma bucket_remove_idem : forall (k : value) (b : list value),
          bucket_remove k (bucket_remove k b) = bucket_remove k b.
      Proof.
        unfold bucket_remove; induction b as [ | v b IH ]; cbn [filter];
          [ reflexivity | ].
        destruct (negb (set_mem v (set_insert k nil))) eqn:E;
          [ cbn [filter]; rewrite E, IH; reflexivity | exact IH ].
      Qed.

      Lemma VSet_nil_eqb : forall (b : list value),
          value_eqb (VSet b) (VSet nil) = true <-> b = nil.
      Proof.
        intros b; split; intro H.
        1: apply value_eqb_eq in H; injection H as H; exact H.
        1: subst b; apply value_eqb_refl.
      Qed.

      Lemma Forall_dict_delete : forall (P : value * value -> Prop) k d,
          Forall P d -> Forall P (dict_delete k d).
      Proof.
        intros * H. apply Forall_forall; intros e H_in.
        apply dict_delete_incl in H_in.
        rewrite Forall_forall in H; apply H; exact H_in.
      Qed.

      Lemma tri_unstep_d_preserve_tri_wf : forall k g d,
          tri_wf d -> tri_wf (tri_unstep_d k g d).
      Proof.
        unfold tri_wf; intros * [ H_wf H_ne ].
        rewrite tri_unstep_d_eq.
        destruct (dict_lookup g d) as [ bk | ]; [ | split; assumption ].
        destruct bk as [ | | | | | | | | b | ]; try (split; assumption).
        destruct (value_eqb (VSet (bucket_remove k b)) (VSet nil)) eqn:E.
        1: split; [ apply dict_delete_preserve_dict_wf; exact H_wf
                  | apply Forall_dict_delete; exact H_ne ].
        1:{ split; [ apply dict_insert_preserve_dict_wf; exact H_wf | ].
            apply Forall_dict_insert_entry; [ | exact H_ne ].
            cbn [snd]; exists (bucket_remove k b); split; [ reflexivity | ].
            intro E_nil; rewrite E_nil, value_eqb_refl in E; discriminate. }
      Qed.

      Lemma tri_unstep_d_lookup_diff : forall k g' d g,
          tri_wf d ->
          value_eqb g g' = false ->
          dict_lookup g (tri_unstep_d k g' d) = dict_lookup g d.
      Proof.
        intros * [ H_wf _ ] H_ne.
        apply value_eqb_neq in H_ne.
        rewrite tri_unstep_d_eq.
        destruct (dict_lookup g' d) as [ bk | ]; [ | reflexivity ].
        destruct bk as [ | | | | | | | | b | ]; try reflexivity.
        destruct (value_eqb (VSet (bucket_remove k b)) (VSet nil)).
        1: apply dict_lookup_delete_diff; exact H_ne.
        1: apply DictIndexImpl.dict_lookup_insert_diff; exact H_ne.
      Qed.

      Lemma tri_unfold_d_preserve_tri_wf : forall k gs d,
          tri_wf d -> tri_wf (fold_right (tri_unstep_d k) d gs).
      Proof.
        intros k gs d H.
        induction gs as [ | g gs IH ]; cbn [fold_right]; [ exact H | ].
        apply tri_unstep_d_preserve_tri_wf; exact IH.
      Qed.

      Lemma tri_word_unstep_d_preserve_tri_wf : forall w k d,
          tri_wf d -> tri_wf (tri_word_unstep_d w k d).
      Proof. intros; apply tri_unfold_d_preserve_tri_wf; assumption. Qed.

      Lemma tri_row_unstep_d_preserve_tri_wf : forall ws k d,
          tri_wf d -> tri_wf (tri_row_unstep_d ws k d).
      Proof.
        intros ws k d H.
        induction ws as [ | w ws IH ]; [ exact H | ].
        rewrite tri_row_unstep_d_cons.
        apply tri_word_unstep_d_preserve_tri_wf; exact IH.
      Qed.

      Lemma tri_unfold_d_lookup_other : forall k gs d g,
          tri_wf d ->
          set_mem g gs = false ->
          dict_lookup g (fold_right (tri_unstep_d k) d gs) = dict_lookup g d.
      Proof.
        intros k gs d g H_wf.
        induction gs as [ | g' gs IH ]; cbn [fold_right]; [ reflexivity | ].
        intros H_mem.
        unfold set_mem in H_mem; cbn [existsb] in H_mem.
        rewrite Bool.orb_false_iff in H_mem; destruct H_mem as [ H_g H_gs ].
        rewrite (tri_unstep_d_lookup_diff k g' _ g
                   (tri_unfold_d_preserve_tri_wf k gs d H_wf) H_g).
        apply IH; exact H_gs.
      Qed.

      (* and at a trigram the word does have: the bucket loses the key, and
         the entry goes with it if that empties it *)
      Lemma tri_unfold_d_lookup_same : forall k gs d g,
          tri_wf d ->
          set_mem g gs = true ->
          dict_lookup g (fold_right (tri_unstep_d k) d gs)
          = match bucket_remove k (bucket_of g d) with
            | nil => None
            | b => Some (VSet b)
            end.
      Proof.
        intros k gs d g H_wf.
        induction gs as [ | g' gs IH ]; cbn [fold_right]; [ discriminate | ].
        intros H_mem.
        unfold set_mem in H_mem; cbn [existsb] in H_mem.
        rewrite Bool.orb_true_iff in H_mem.
        destruct (value_eqb g g') eqn:E_g.
        2:{ (* this trigram leaves g alone *)
            destruct H_mem as [ E | H_gs ]; [ congruence | ].
            rewrite (tri_unstep_d_lookup_diff k g' _ g
                       (tri_unfold_d_preserve_tri_wf k gs d H_wf) E_g).
            apply IH; exact H_gs. }
        (* this one IS g *)
        apply value_eqb_eq in E_g; subst g'.
        rewrite tri_unstep_d_eq.
        destruct (set_mem g gs) eqn:E_gs.
        1:{ (* a later trigram already removed the key here, and removing
               it again changes nothing *)
            rewrite (IH eq_refl).
            destruct (bucket_remove k (bucket_of g d)) as [ | v b ] eqn:E_b.
            (* nothing is left at g, so there is no entry to remove from *)
            1: cbv beta iota; exact (IH eq_refl).
            (* the bucket here is already the removed one, and removing
               the key from it again changes nothing *)
            1:{ cbv beta iota. rewrite <- E_b, bucket_remove_idem, E_b.
                destruct (value_eqb (VSet (v :: b)) (VSet nil)) eqn:E_nil.
                1: apply VSet_nil_eqb in E_nil; discriminate.
                1: apply DictIndexImpl.dict_lookup_insert_same. } }
        1:{ (* none did, so the bucket here is the original *)
            rewrite (tri_unfold_d_lookup_other k gs d g H_wf E_gs).
            unfold bucket_of.
            destruct (dict_lookup g d) as [ bk | ] eqn:E_lk.
            (* no entry at g at all: nothing to remove, and nothing is
               owed there either *)
            2:{ cbv beta iota; cbn [bucket_remove filter].
                rewrite (tri_unfold_d_lookup_other k gs d g H_wf E_gs).
                exact E_lk. }
            (* the entry is a set, by the invariant *)
            pose proof H_wf as H_wf'; destruct H_wf' as [ H_dwf H_ne ].
            apply (Forall_dict_lookup _ _ _ _ H_ne) in E_lk as E_set.
            destruct E_set as [ b [ E_b _ ] ]; cbn [snd] in E_b; subst bk.
            destruct (value_eqb (VSet (bucket_remove k b)) (VSet nil)) eqn:E_nil.
            (* the last key goes, so the entry goes: and the delete is on
               the dictionary the later trigrams left, not on d *)
            1:{ apply VSet_nil_eqb in E_nil; rewrite E_nil.
                apply dict_lookup_delete_same.
                apply (proj1 (tri_unfold_d_preserve_tri_wf k gs d H_wf)). }
            1:{ destruct (bucket_remove k b) as [ | v b' ] eqn:E_br.
                (* the test already said the removal leaves something *)
                1:{ try rewrite E_br in E_nil;
                    rewrite value_eqb_refl in E_nil; discriminate. }
                1:{ rewrite DictIndexImpl.dict_lookup_insert_same; reflexivity. } } }
      Qed.

      Corollary tri_word_unstep_d_lookup_other : forall w k d g,
          tri_wf d ->
          set_mem g (word_keys w) = false ->
          dict_lookup g (tri_word_unstep_d w k d) = dict_lookup g d.
      Proof. intros; apply tri_unfold_d_lookup_other; assumption. Qed.

      Corollary tri_word_unstep_d_lookup_same : forall w k d g,
          tri_wf d ->
          set_mem g (word_keys w) = true ->
          dict_lookup g (tri_word_unstep_d w k d)
          = match bucket_remove k (bucket_of g d) with
            | nil => None
            | b => Some (VSet b)
            end.
      Proof. intros; apply tri_unfold_d_lookup_same; assumption. Qed.

      (* one ROW's removal, one fold out *)
      Lemma tri_row_unstep_d_lookup_other : forall ws k d g,
          tri_wf d ->
          set_mem g (tri_keys ws) = false ->
          dict_lookup g (tri_row_unstep_d ws k d) = dict_lookup g d.
      Proof.
        intros ws k d g H_wf; induction ws as [ | w ws IH ]; [ reflexivity | ].
        rewrite tri_keys_cons, set_mem_app, Bool.orb_false_iff.
        intros [ H_w H_ws ].
        rewrite tri_row_unstep_d_cons.
        rewrite (tri_word_unstep_d_lookup_other w k _ g
                   (tri_row_unstep_d_preserve_tri_wf ws k d H_wf) H_w).
        apply IH; exact H_ws.
      Qed.

      Lemma tri_row_unstep_d_lookup_same : forall ws k d g,
          tri_wf d ->
          set_mem g (tri_keys ws) = true ->
          dict_lookup g (tri_row_unstep_d ws k d)
          = match bucket_remove k (bucket_of g d) with
            | nil => None
            | b => Some (VSet b)
            end.
      Proof.
        intros ws k d g H_wf; induction ws as [ | w ws IH ]; [ discriminate | ].
        rewrite tri_keys_cons, set_mem_app, Bool.orb_true_iff.
        intros H_mem.
        rewrite tri_row_unstep_d_cons.
        pose proof (tri_row_unstep_d_preserve_tri_wf ws k d H_wf) as H_wf'.
        destruct (set_mem g (word_keys w)) eqn:E_w.
        2:{ destruct H_mem as [ E | H_ws ]; [ congruence | ].
            rewrite (tri_word_unstep_d_lookup_other w k _ g H_wf' E_w).
            apply IH; exact H_ws. }
        rewrite (tri_word_unstep_d_lookup_same w k _ g H_wf' E_w).
        (* the bucket the inner word removes from is what the earlier words
           left, and removing the same key twice is removing it once *)
        destruct (set_mem g (tri_keys ws)) eqn:E_ws.
        1:{ assert (E_b : bucket_of g (tri_row_unstep_d ws k d)
                          = bucket_remove k (bucket_of g d)).
            1:{ unfold bucket_of at 1; rewrite (IH eq_refl).
                destruct (bucket_remove k (bucket_of g d)); reflexivity. }
            rewrite E_b, bucket_remove_idem; reflexivity. }
        1:{ unfold bucket_of at 1;
            rewrite (tri_row_unstep_d_lookup_other ws k d g H_wf E_ws);
            reflexivity. }
      Qed.

      (* ------------------------------------------------------------------
         What the delete body computes.  Unlike the insert body, this one
         needs the invariant: on a bucket that is not a set the expression
         would insert garbage, where the mirror leaves the dictionary
         alone, so the two agree only where every bucket is a set.
         ------------------------------------------------------------------ *)
      Lemma interp_tri_delete : forall (store env : locals) r g d,
          map.get env tup = Some r ->
          map.get env gvar = Some g ->
          map.get env sacc = Some (VDict d) ->
          tri_wf d ->
          interp_expr store env tri_delete_body
          = VDict (tri_unstep_d (row_key key r) g d).
      Proof.
        unfold tri_delete_body, tri_without_pk, row_pk.
        intros * E_tup E_g E_sacc [ _ H_ne ].
        (* the interpreter reaches the key through the record, so the mirror's
           row_key is unfolded to the same shape rather than folded back *)
        unfold row_key.
        cbn [interp_expr].
        unfold get_local; rewrite ?E_tup, ?E_g, ?E_sacc.
        (* the mirror is unfolded here so that its removal and the one the
           interpreter computes are the same term, and the test can be
           destructed once for both sides *)
        rewrite tri_unstep_d_eq; unfold bucket_remove.
        cbn [interp_binop].
        destruct (dict_lookup g d) as [ bk | ] eqn:E_lk;
          cbn [interp_atom]; [ | reflexivity ].
        (* the bucket is a set, by the invariant *)
        apply (Forall_dict_lookup _ _ _ _ H_ne) in E_lk as E_set.
        destruct E_set as [ b [ E_b _ ] ]; cbn [snd] in E_b; subst bk.
        repeat rewrite_map_get_put_goal.
        rewrite ?E_tup, ?E_g, ?E_sacc.
        cbn [interp_binop interp_atom].
        lazymatch goal with
        | |- context[if ?tst then _ else _] => destruct tst eqn:E_nil
        end.
        all: cbn [interp_expr interp_binop interp_ternop interp_atom].
        all: unfold get_local.
        all: repeat rewrite_map_get_put_goal.
        all: rewrite ?E_tup, ?E_g, ?E_sacc.
        all: reflexivity.
      Qed.

      Lemma interp_tri_delete_fold : forall (store env : locals) r d gs,
          map.get env tup = Some r ->
          tri_wf d ->
          fold_right
            (fun g a' => interp_expr store
                           (map.put (map.put env gvar g) sacc a') tri_delete_body)
            (VDict d) gs
          = VDict (fold_right (tri_unstep_d (row_key key r)) d gs).
      Proof.
        intros * E_tup H_wf.
        induction gs as [ | g gs IH ]; cbn [fold_right]; [ reflexivity | ].
        rewrite IH.
        apply interp_tri_delete.
        1:{ rewrite !map.get_put_diff by congruence. exact E_tup. }
        1:{ rewrite map.get_put_diff by congruence. apply map.get_put_same. }
        1: apply map.get_put_same.
        1: apply tri_unfold_d_preserve_tri_wf; exact H_wf.
      Qed.

      Lemma interp_tri_word_delete : forall (store env : locals) r w d,
          map.get env wrd = Some (VString w) ->
          map.get env tup = Some r ->
          map.get env wacc = Some (VDict d) ->
          tri_wf d ->
          interp_expr store env tri_word_delete_body
          = VDict (tri_word_unstep_d w (row_key key r) d).
      Proof.
        intros * E_wrd E_tup E_wacc H_wf.
        unfold tri_word_delete_body; rewrite tri_word_unstep_d_eq.
        rewrite interp_EFold.
        rewrite (interp_word_trigrams store env w E_wrd).
        rewrite interp_EVar; unfold get_local; rewrite E_wacc.
        apply interp_tri_delete_fold; [ exact E_tup | exact H_wf ].
      Qed.

      Lemma interp_tri_word_delete_fold :
        forall (store env : locals) r d (ws : list string),
          map.get env tup = Some r ->
          tri_wf d ->
          fold_right
            (fun w a' => interp_expr store
                           (map.put (map.put env wrd w) wacc a') tri_word_delete_body)
            (VDict d) (List.map VString ws)
          = VDict (tri_row_unstep_d ws (row_key key r) d).
      Proof.
        intros * E_tup H_wf.
        induction ws as [ | w ws IH ]; cbn [List.map fold_right];
          [ reflexivity | ].
        rewrite IH, tri_row_unstep_d_cons.
        apply interp_tri_word_delete.
        1:{ rewrite map.get_put_diff by congruence. apply map.get_put_same. }
        1:{ rewrite !map.get_put_diff by congruence. exact E_tup. }
        1: apply map.get_put_same.
        1: apply tri_row_unstep_d_preserve_tri_wf; exact H_wf.
      Qed.

      Lemma interp_tri_row_delete : forall (store env : locals) r txt d,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          map.get env acc = Some (VDict d) ->
          tri_wf d ->
          interp_expr store env tri_row_delete_body
          = VDict (tri_row_unstep_d (words seps txt) (row_key key r) d).
      Proof.
        intros * H_txt E_tup E_acc H_wf.
        unfold tri_row_delete_body.
        rewrite interp_EFold.
        rewrite (interp_row_words store env r txt H_txt E_tup).
        rewrite interp_EVar; unfold get_local; rewrite E_acc.
        apply interp_tri_word_delete_fold; [ exact E_tup | exact H_wf ].
      Qed.

      (* ------------------------------------------------------------------
         The two sides meet: what a recomputation over the filtered table
         holds at a trigram, against what the removal leaves there.
         ------------------------------------------------------------------ *)
      Lemma set_mem_true_iff : forall (v : value) l, set_mem v l = true <-> In v l.
      Proof.
        unfold set_mem; intros v l; rewrite existsb_exists; split.
        1:{ intros [ x [ H_in E ] ]; apply value_eqb_eq in E; subst; exact H_in. }
        1:{ intros H_in; exists v; split; [ exact H_in | apply value_eqb_refl ]. }
      Qed.

      Lemma bucket_remove_eq : forall (k : value) (b : list value),
          bucket_remove k b = filter (fun v => negb (value_eqb v k)) b.
      Proof.
        unfold bucket_remove, set_mem; intros k b.
        apply filter_ext; intro v; cbn [set_insert existsb].
        rewrite Bool.orb_false_r; reflexivity.
      Qed.

      Lemma keys_at_nil : forall g, keys_at g nil = nil.
      Proof. reflexivity. Qed.

      Lemma In_keys_at : forall g l (v : value),
          In v (keys_at g l)
          <-> exists r, In r l /\ set_mem g (tri_keys (row_wrds r)) = true
                        /\ row_key key r = v.
      Proof.
        intros g l v; induction l as [ | r l IH ].
        1:{ rewrite keys_at_nil; split;
            [ intros [] | intros [ r [ [] _ ] ] ]. }
        rewrite keys_at_cons.
        destruct (set_mem g (tri_keys (row_wrds r))) eqn:E_mem; split.
        1:{ intro H_in; apply set_insert_incl in H_in.
            destruct H_in as [ E | H_in ].
            1: exists r; split;
               [ left; reflexivity | split; [ exact E_mem | symmetry; exact E ] ].
            1:{ apply IH in H_in as [ r' [ H_in' H' ] ].
                exists r'; split; [ right; exact H_in' | exact H' ]. } }
        1:{ intros [ r' [ [ E_r | H_in' ] [ H_m' E' ] ] ].
            1: subst r'; apply set_insert_incl_r; left; exact E'.
            1:{ apply set_insert_incl_r; right.
                apply IH; exists r'; split; [ exact H_in' | split; assumption ]. } }
        1:{ intro H_in; apply IH in H_in as [ r' [ H_in' H' ] ].
            exists r'; split; [ right; exact H_in' | exact H' ]. }
        1:{ intros [ r' [ [ E_r | H_in' ] [ H_m' E' ] ] ].
            1: subst r'; congruence.
            1: apply IH; exists r'; split; [ exact H_in' | split; assumption ]. }
      Qed.

      Lemma keys_at_SSorted : forall g l, StronglySorted value_leb (keys_at g l).
      Proof.
        intros g l; induction l as [ | r l IH ].
        1: rewrite keys_at_nil; constructor.
        rewrite keys_at_cons; destruct (set_mem g (tri_keys (row_wrds r)));
          [ apply set_insert_preserve_SSorted; exact IH | exact IH ].
      Qed.

      Lemma keys_at_NoDup : forall g l, NoDup (keys_at g l).
      Proof.
        intros g l; induction l as [ | r l IH ].
        1: rewrite keys_at_nil; constructor.
        rewrite keys_at_cons; destruct (set_mem g (tri_keys (row_wrds r)));
          [ apply set_insert_preserve_NoDup; [ exact IH | apply keys_at_SSorted ]
          | exact IH ].
      Qed.

      (* a declared key is what makes the deleted row unique *)
      Lemma NoDup_map_key_In_eq : forall l (r r' : value),
          NoDup (List.map (row_key key) l) ->
          In r l -> In r' l -> row_key key r' = row_key key r -> r' = r.
      Proof.
        induction l as [ | r0 l IH ]; cbn [List.map In]; intros r r' H_nd H_r H_r' E.
        1: contradiction.
        inversion H_nd as [ | ? ? H_ni H_nd' ]; subst.
        destruct H_r as [ E_r | H_r ]; destruct H_r' as [ E_r' | H_r' ]; subst.
        1: reflexivity.
        1:{ exfalso; apply H_ni; rewrite <- E; apply in_map; exact H_r'. }
        1:{ exfalso; apply H_ni; rewrite E; apply in_map; exact H_r. }
        1: apply IH; assumption.
      Qed.

      (* At a trigram the deleted row has, filtering the table out of the
         recomputation is removing its key from the bucket.  No hypothesis
         about the key being unique is needed here: the row whose key is
         gone is the only one whose key the filter removes. *)
      Lemma keys_at_filter_neq_tri : forall l (k : value) g,
          keys_at g (filter (fun r' => negb (value_eqb (row_key key r') k)) l)
          = bucket_remove k (keys_at g l).
      Proof.
        intros l k g.
        rewrite bucket_remove_eq.
        apply NoDup_SSorted_double_incl_eq;
          auto using keys_at_NoDup, keys_at_SSorted, NoDup_filter,
                     SSorted_filter.
        1:{ intros v H_in; apply In_keys_at in H_in as [ r' [ H_in' [ H_m' E' ] ] ].
            apply filter_In in H_in' as [ H_in' H_ne ].
            apply filter_In; split.
            1: apply In_keys_at; exists r'; split; [ exact H_in' | split; assumption ].
            1: rewrite <- E'; exact H_ne. }
        1:{ intros v H_in; apply filter_In in H_in as [ H_in H_ne ].
            apply In_keys_at in H_in as [ r' [ H_in' [ H_m' E' ] ] ].
            apply In_keys_at; exists r'; split; [ | split; assumption ].
            apply filter_In; split; [ exact H_in' | rewrite E'; exact H_ne ]. }
      Qed.

      (* and at any other trigram the recomputation is unchanged -- which is
         where the declared key is needed: without it some OTHER row could
         share the deleted key, and filtering would take that row's
         contributions out of buckets the removal never touches. *)
      Lemma keys_at_filter_neq_other : forall l (r : value) (k : value) g,
          NoDup (List.map (row_key key) l) ->
          In r l -> row_key key r = k ->
          set_mem g (tri_keys (row_wrds r)) = false ->
          keys_at g (filter (fun r' => negb (value_eqb (row_key key r') k)) l)
          = keys_at g l.
      Proof.
        intros l r k g H_nd H_in E_k E_mem.
        apply NoDup_SSorted_double_incl_eq;
          auto using keys_at_NoDup, keys_at_SSorted.
        1:{ intros v H_v; apply In_keys_at in H_v as [ r' [ H_in' [ H_m' E' ] ] ].
            apply filter_In in H_in' as [ H_in' _ ].
            apply In_keys_at; exists r'; split; [ exact H_in' | split; assumption ]. }
        1:{ intros v H_v; apply In_keys_at in H_v as [ r' [ H_in' [ H_m' E' ] ] ].
            apply In_keys_at; exists r'; split; [ | split; assumption ].
            apply filter_In; split; [ exact H_in' | ].
            (* the row that contributed v is not the deleted one, since the
               deleted one does not have g among its trigrams *)
            rewrite Bool.negb_true_iff.
            destruct (value_eqb (row_key key r') k) eqn:E_eq; [ | reflexivity ].
            exfalso. apply value_eqb_eq in E_eq.
            rewrite <- E_k in E_eq.
            pose proof (NoDup_map_key_In_eq l r r' H_nd H_in H_in' E_eq) as E_rr.
            subst r'; congruence. }
      Qed.

      (* ==================================================================
         The delete equation: the index of the table with one row's key
         filtered out is the stored index with that row's keys removed.
         ================================================================== *)
      Theorem tri_dict_filter_neq : forall l (r : value) (k : value),
          NoDup (List.map (row_key key) l) ->
          In r l -> row_key key r = k ->
          tri_dict (filter (fun r' => negb (value_eqb (row_key key r') k)) l)
          = tri_row_unstep_d (row_wrds r) k (tri_dict l).
      Proof.
        intros l r k H_nd H_in E_k.
        apply dict_wf_lookup_ext.
        1: apply (proj1 (tri_dict_tri_wf _)).
        1: apply (proj1 (tri_row_unstep_d_preserve_tri_wf _ _ _ (tri_dict_tri_wf l))).
        intros g.
        rewrite !tri_dict_lookup.
        destruct (set_mem g (tri_keys (row_wrds r))) eqn:E_mem.
        1:{ rewrite (tri_row_unstep_d_lookup_same _ _ _ _ (tri_dict_tri_wf l) E_mem).
            (* the stored bucket at g is the keys the table owes it *)
            assert (E_b : bucket_of g (tri_dict l) = keys_at g l).
            1:{ unfold bucket_of; rewrite tri_dict_lookup.
                destruct (keys_at g l); reflexivity. }
            rewrite E_b, keys_at_filter_neq_tri; reflexivity. }
        1:{ rewrite (tri_row_unstep_d_lookup_other _ _ _ _ (tri_dict_tri_wf l) E_mem).
            rewrite tri_dict_lookup.
            rewrite (keys_at_filter_neq_other l r k g H_nd H_in E_k E_mem).
            reflexivity. }
      Qed.

      Lemma filter_all_true : forall (A : Type) (f : A -> bool) (l : list A),
          (forall x, In x l -> f x = true) -> filter f l = l.
      Proof.
        induction l as [ | x l IH ]; cbn [filter]; intros H; [ reflexivity | ].
        rewrite (H x (or_introl eq_refl)).
        f_equal; apply IH; intros y H_in; apply H; right; exact H_in.
      Qed.

      Lemma tri_dict_filter_neq_absent : forall l (k : value),
          (forall r, In r l -> row_key key r <> k) ->
          tri_dict (filter (fun r' => negb (value_eqb (row_key key r') k)) l)
          = tri_dict l.
      Proof.
        intros l k H_ne; f_equal.
        apply filter_all_true; intros r H_in.
        rewrite Bool.negb_true_iff.
        destruct (value_eqb (row_key key r) k) eqn:E; [ | reflexivity ].
        apply value_eqb_eq in E; exfalso; apply (H_ne r H_in); exact E.
      Qed.

    End WithMap.
  End WithVars.
End WithHole.
