Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.IndexInterface fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute
  fiat2.StringFacts fiat2.Constraint fiat2.CollectionTransf.
Require fiat2.DictIndexImpl.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
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
   the pattern" -- that rests on occurrence_first_trigram in StringFacts --
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
    (* the position and the dictionary, bound by the inner fold over the
       positions at which the row's text has a trigram *)
    Context (pos sacc : string).
    (* the bucket already stored at a trigram, if any *)
    Context (bkt : string).
    Context (H_tup_acc : tup <> acc).
    Context (H_tup_pos : tup <> pos).
    Context (H_tup_sacc : tup <> sacc).
    Context (H_tup_bkt : tup <> bkt).
    Context (H_sacc_bkt : sacc <> bkt).
    Context (H_pos_sacc : pos <> sacc).
    (* last in the list on purpose: a section hypothesis is abstracted into
       the lemmas that use it in declaration order, so adding one at the end
       leaves every existing lemma's arguments where they were.  Only the
       delete body below needs this one, since it is the only body that
       mentions a position under the bucket's binder. *)
    Context (H_pos_bkt : pos <> bkt).

    Definition row_text (r : expr) : expr := EAccess r attr.
    Definition row_pk (r : expr) : expr := EAccess r key.

    (* 0, 1, ... |s| - 3: the positions at which s has a trigram.  Empty when
       s is shorter than three characters, since ORange counts up by one and
       stops, and a negative length is no positions at all. *)
    Definition trigram_positions (s : expr) : expr :=
      EBinop ORange (EAtom (AInt 0))
        (EBinop OMinus (EUnop OLengthString s) (EAtom (AInt 2))).

    Definition trigram_at (s p : expr) : expr :=
      ETernop OSubstring s p (EAtom (AInt 3)).

    (* the key goes into the bucket at one trigram of one row's text *)
    Definition tri_insert_body : expr :=
      ETernop OInsert (EVar sacc)
        (trigram_at (row_text (EVar tup)) (EVar pos))
        (EOptMatch
           (EBinop OLookup (EVar sacc)
              (trigram_at (row_text (EVar tup)) (EVar pos)))
           (EBinop OSetInsert (EAtom (AEmptySet None)) (row_pk (EVar tup)))
           bkt
           (EBinop OSetInsert (EVar bkt) (row_pk (EVar tup)))).

    (* one row: every position at which its text has a trigram *)
    Definition tri_row_body : expr :=
      EFold (trigram_positions (row_text (EVar tup))) (EVar acc) pos sacc
        tri_insert_body.

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
           (trigram_at (row_text (EVar tup)) (EVar pos)))
        (EVar sacc)
        bkt
        (EIf (EBinop OEq tri_without_pk (EAtom (AEmptySet None)))
           (EBinop ODelete (EVar sacc)
              (trigram_at (row_text (EVar tup)) (EVar pos)))
           (ETernop OInsert (EVar sacc)
              (trigram_at (row_text (EVar tup)) (EVar pos))
              tri_without_pk)).

    Definition tri_row_delete_body : expr :=
      EFold (trigram_positions (row_text (EVar tup))) (EVar acc) pos sacc
        tri_delete_body.

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
      Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
      Notation value := (value (width:=width)).
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

      Lemma to_idx_ty : forall (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t).
      Proof.
        unfold is_tbl_ty, idx_ty, to_idx, tri_row_body, tri_insert_body,
          row_text, row_pk, trigram_positions, trigram_at.
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
        (* the inner fold, over the positions at which this row has a trigram *)
        eapply TyEFold.
        1:{ (* range 0 (strlen (tup.attr) - 2) *)
            eapply TyEBinop; [ apply TyORange | int_lit | ].
            eapply TyEBinop; [ apply TyOMinus | | int_lit ].
            eapply TyEUnop; [ apply TyOLengthString | ].
            eapply TyEAccess; [ lookup_var | eassumption ]. }
        1:{ lookup_var. }
        (* insert the key under the trigram at this position *)
        eapply TyETernop; [ apply TyOInsert | lookup_var | | ].
        1:{ eapply TyETernop;
              [ apply TyOSubstring
              | eapply TyEAccess; [ lookup_var | eassumption ]
              | lookup_var
              | int_lit ]. }
        eapply TyEOptMatch.
        1:{ (* what is stored at that trigram, if anything *)
            eapply TyEBinop; [ apply TyOLookup | lookup_var | ].
            eapply TyETernop;
              [ apply TyOSubstring
              | eapply TyEAccess; [ lookup_var | eassumption ]
              | lookup_var
              | int_lit ]. }
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
        unfold tri_row_body, tri_insert_body, row_text, row_pk,
          trigram_positions, trigram_at.
        intros * H_ktwf E_attr E_key E_tup E_acc.
        eapply TyEFold.
        1:{ eapply TyEBinop; [ apply TyORange | int_lit | ].
            eapply TyEBinop; [ apply TyOMinus | | int_lit ].
            eapply TyEUnop; [ apply TyOLengthString | ].
            eapply TyEAccess; [ lookup_var' | eassumption ]. }
        1:{ lookup_var'. }
        eapply TyETernop; [ apply TyOInsert | lookup_var' | | ].
        1:{ eapply TyETernop;
              [ apply TyOSubstring
              | eapply TyEAccess; [ lookup_var' | eassumption ]
              | lookup_var'
              | int_lit ]. }
        eapply TyEOptMatch.
        1:{ eapply TyEBinop; [ apply TyOLookup | lookup_var' | ].
            eapply TyETernop;
              [ apply TyOSubstring
              | eapply TyEAccess; [ lookup_var' | eassumption ]
              | lookup_var'
              | int_lit ]. }
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
        unfold tri_row_delete_body, tri_delete_body, tri_without_pk,
          row_text, row_pk, trigram_positions, trigram_at.
        intros * H_ktwf E_attr E_key E_tup E_acc.
        (* the fold over the positions at which this row has a trigram *)
        eapply TyEFold.
        1:{ eapply TyEBinop; [ apply TyORange | int_lit | ].
            eapply TyEBinop; [ apply TyOMinus | | int_lit ].
            eapply TyEUnop; [ apply TyOLengthString | ].
            eapply TyEAccess; [ lookup_var' | eassumption ]. }
        1:{ lookup_var'. }
        eapply TyEOptMatch.
        1:{ (* what the bucket at this trigram holds, if anything *)
            eapply TyEBinop; [ apply TyOLookup | lookup_var' | ].
            eapply TyETernop;
              [ apply TyOSubstring
              | eapply TyEAccess; [ lookup_var' | eassumption ]
              | lookup_var'
              | int_lit ]. }
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
        1:{ eapply TyEBinop; [ apply TyODelete | lookup_var' | ].
            eapply TyETernop;
              [ apply TyOSubstring
              | eapply TyEAccess; [ lookup_var' | eassumption ]
              | lookup_var'
              | int_lit ]. }
        1:{ eapply TyETernop; [ apply TyOInsert | lookup_var' | | ].
            1:{ eapply TyETernop;
                  [ apply TyOSubstring
                  | eapply TyEAccess; [ lookup_var' | eassumption ]
                  | lookup_var'
                  | int_lit ]. }
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

      (* The trigram of txt at a position, as a value. *)
      Definition tri_key (txt : string) (p : value) : value :=
        match p with
        | VInt i => VString (String.substring (Z.to_nat i) 3 txt)
        | _ => VUnit
        end.

      (* One position of one row. *)
      Definition tri_step (txt : string) (k p a : value) : value :=
        match a with
        | VDict d =>
            VDict (dict_insert (tri_key txt p)
                     (bucket_insert k (dict_lookup (tri_key txt p) d)) d)
        | _ => VUnit
        end.

      (* The positions at which a text has a trigram, as the range the index
         expression computes.  Shorter than three characters means none. *)
      Definition tri_positions (txt : string) : list value :=
        eval_range 0 (Z.to_nat (Z.of_nat (String.length txt) - 2)).

      (* One row: its key goes into the bucket of each of its trigrams. *)
      Definition tri_row_step (txt : string) (k a : value) : value :=
        fold_right (tri_step txt k) a (tri_positions txt).

      Definition row_str (r : value) : string :=
        match row_key attr r with VString s => s | _ => EmptyString end.

      Definition tri_entries (l : list value) : value :=
        fold_right (fun r a => tri_row_step (row_str r) (row_key key r) a)
          (VDict nil) l.

      (* The store is universally quantified in this group of lemmas: none of
         to_idx's parts mentions a global, so the index of a list of rows is
         the same whatever store it is computed in.  The maintenance rules
         need that, since they recompute the index where the table's own
         store is in scope. *)
      Lemma interp_trigram_positions : forall (store env : locals) r txt,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          interp_expr store env (trigram_positions (row_text (EVar tup)))
          = VList (tri_positions txt).
      Proof.
        unfold trigram_positions, row_text, tri_positions, row_key in *.
        intros * H_txt E_tup.
        rewrite !interp_EBinop, interp_EUnop, interp_EAccess, !interp_EVar,
          !interp_EAtom.
        unfold get_local; rewrite E_tup.
        destruct r; try discriminate.
        rewrite H_txt.
        cbn [interp_unop interp_binop interp_atom apply_int_binop].
        rewrite Z.sub_0_r. reflexivity.
      Qed.

      Lemma interp_trigram_at_val : forall txt p,
          interp_ternop OSubstring (VString txt) p (VInt 3) = tri_key txt p.
      Proof. unfold tri_key; intros; destruct p; reflexivity. Qed.

      Lemma interp_tri_insert : forall (store env : locals) r txt p a,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          map.get env pos = Some p ->
          map.get env sacc = Some a ->
          interp_expr store env tri_insert_body
          = tri_step txt (row_key key r) p a.
      Proof.
        unfold tri_insert_body, trigram_at, row_text, row_pk, tri_step.
        intros * H_txt E_tup E_pos E_sacc.
        cbn [interp_expr].
        unfold get_local; rewrite E_tup, E_pos, E_sacc.
        unfold row_key in H_txt |- *.
        destruct r as [ | | | | | | rv | | | | ]; try discriminate.
        rewrite H_txt, !interp_trigram_at_val.
        destruct a as [ | | | | | | | d | | | ]; try reflexivity.
        cbn [interp_binop interp_ternop].
        destruct (dict_lookup (tri_key txt p) d) as [ bk | ];
          cbn [bucket_insert interp_atom].
        (* something already there: the key goes in beside it *)
        1:{ rewrite map.get_put_same, map.get_put_diff by congruence.
            rewrite E_tup. destruct bk; reflexivity. }
        (* nothing yet: the singleton *)
        1: reflexivity.
      Qed.

      (* The inner fold, over the positions. *)
      Lemma interp_tri_fold : forall (store env : locals) r txt a l,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          fold_right
            (fun p a' => interp_expr store
                           (map.put (map.put env pos p) sacc a') tri_insert_body)
            a l
          = fold_right (tri_step txt (row_key key r)) a l.
      Proof.
        intros * H_txt E_tup.
        induction l as [ | p l IH ]; cbn [fold_right]; [ reflexivity | ].
        rewrite IH.
        apply interp_tri_insert; [ exact H_txt | | | apply map.get_put_same ].
        1:{ rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact E_tup. }
        1:{ rewrite map.get_put_diff by congruence. apply map.get_put_same. }
      Qed.

      (* One row's contribution. *)
      Lemma interp_tri_row : forall (store env : locals) r txt a,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          map.get env acc = Some a ->
          interp_expr store env tri_row_body
          = tri_row_step txt (row_key key r) a.
      Proof.
        intros * H_txt E_tup E_acc. unfold tri_row_body, tri_row_step.
        rewrite interp_EFold.
        rewrite (interp_trigram_positions store env r txt H_txt E_tup).
        rewrite interp_EVar; unfold get_local; rewrite E_acc.
        apply interp_tri_fold; assumption.
      Qed.

      (* The outer fold, over the rows.  Every row has to carry a string at
         attr, which is what is_tbl_ty asks of the table's type. *)
      Lemma interp_to_idx_fold : forall (store env : locals) (l : list value) a,
          Forall (fun r => exists txt, row_key attr r = VString txt) l ->
          fold_right
            (fun r a' => interp_expr store
                           (map.put (map.put env tup r) acc a') tri_row_body)
            a l
          = fold_right (fun r a' => tri_row_step (row_str r) (row_key key r) a') a l.
      Proof.
        intros store env l a H_all.
        induction l as [ | r l IH ]; cbn [fold_right]; [ reflexivity | ].
        invert_Forall.
        rewrite IH by assumption.
        lazymatch goal with H : exists _, _ |- _ => destruct H as [ txt H_txt ] end.
        assert (E_str : row_str r = txt)
          by (unfold row_str; rewrite H_txt; reflexivity).
        rewrite E_str.
        apply interp_tri_row; [ exact H_txt | | apply map.get_put_same ].
        rewrite map.get_put_diff by congruence. apply map.get_put_same.
      Qed.

      (* What to_idx computes, in Gallina. *)
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

      (* And the hypothesis is what the table's type gives. *)
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
      (* ------------------------------------------------------------------
         Canonical dictionaries.

         A dict value's entries are strictly increasing in their keys
         (Value.dict_wf), so a dictionary is determined by what it looks up.
         The delete rule has to prove an EQUALITY of dictionaries -- the
         index of a table with a row removed is the stored index with that
         row's keys taken out -- and extensionality is the only handle on
         that.  (The insert rule needed none of this: there both sides are
         built by the same insertion.)
         ------------------------------------------------------------------ *)
      Lemma dict_wf_lookup_None : forall (d : list (value * value)) (k : value),
          (forall k' v', In (k', v') d -> value_ltb k k' = true) ->
          dict_lookup k d = None.
      Proof.
        induction d as [ | [ k0 v0 ] d IH ]; cbn [dict_lookup]; [ reflexivity | ].
        intros k H_lt.
        destruct (value_eqb k k0) eqn:E.
        1:{ apply value_eqb_eq in E; subst k0.
            specialize (H_lt k v0 (or_introl eq_refl)).
            unfold value_ltb in H_lt; rewrite value_compare_refl in H_lt.
            discriminate. }
        apply IH; intros k' v' H_in; apply (H_lt k' v'); right; exact H_in.
      Qed.

      Lemma dict_insert_preserve_dict_wf : forall (d : list (value * value)) (k v : value),
          dict_wf d -> dict_wf (dict_insert k v d).
      Proof.
        induction d as [ | [ k0 v0 ] d IH ]; cbn [dict_insert dict_wf]; intros k v H_wf.
        1: split; [ intros ? ? [] | exact I ].
        destruct H_wf as [ H_hd H_wf ].
        destruct (value_ltb k k0) eqn:E_lt.
        1:{ (* k goes in front *)
            cbn [dict_wf]; split; [ | split; [ exact H_hd | exact H_wf ] ].
            intros k' v' [ E | H_in ].
            1: injection E as E _; subst k'; exact E_lt.
            1:{ apply H_hd in H_in.
                unfold value_ltb in *.
                destruct (value_compare k k') eqn:E_kk'; try reflexivity.
                (* k' <= k < k0 <= k' is impossible *)
                all: destruct (value_compare k k0) eqn:E_kk0; try discriminate.
                all: destruct (value_compare k0 k') eqn:E_k0k'; try discriminate.
                1:{ apply value_compare_Eq_eq in E_kk'; subst k'.
                    pose proof (value_compare_trans _ _ _ E_kk0 E_k0k') as E_t.
                    rewrite value_compare_refl in E_t; discriminate. }
                1:{ pose proof (value_compare_trans _ _ _ E_kk0 E_k0k') as E_t.
                    rewrite E_kk' in E_t; discriminate. } } }
        destruct (value_eqb k k0) eqn:E_eq.
        1:{ (* k replaces the head *)
            apply value_eqb_eq in E_eq; subst k0.
            cbn [dict_wf]; split; [ exact H_hd | exact H_wf ]. }
        1:{ (* k goes further in *)
            cbn [dict_wf]; split; [ | apply IH; exact H_wf ].
            intros k' v' H_in.
            (* the new entry's key is one that was already in, or k itself,
               and k0 < k because it is neither less nor equal *)
            apply dict_insert_incl in H_in; cbn [In] in H_in;
              destruct H_in as [ E | H_in ].
            1:{ injection E as E _; subst k'.
                unfold value_ltb, value_eqb in *.
                destruct (value_compare k0 k) eqn:E_k0k; try reflexivity.
                1:{ apply value_compare_Eq_eq in E_k0k; subst.
                    rewrite value_compare_refl in E_eq; discriminate. }
                1:{ rewrite (value_compare_antisym k k0), E_k0k in E_lt.
                    cbn in E_lt; discriminate. } }
            1: apply H_hd in H_in; exact H_in. }
      Qed.

      Lemma dict_delete_preserve_dict_wf : forall (d : list (value * value)) (k : value),
          dict_wf d -> dict_wf (dict_delete k d).
      Proof.
        induction d as [ | [ k0 v0 ] d IH ]; cbn [dict_delete dict_wf]; intros k H_wf;
          [ exact I | ].
        destruct H_wf as [ H_hd H_wf ].
        destruct (value_eqb k k0); [ exact H_wf | ].
        cbn [dict_wf]; split; [ | apply IH; exact H_wf ].
        intros k' v' H_in; apply (H_hd k' v').
        apply dict_delete_incl in H_in; exact H_in.
      Qed.

      Lemma dict_wf_lookup_ext : forall (d1 d2 : list (value * value)),
          dict_wf d1 -> dict_wf d2 ->
          (forall k : value, dict_lookup k d1 = dict_lookup k d2) -> d1 = d2.
      Proof.
        induction d1 as [ | [ k1 v1 ] d1 IH ];
          intros d2 H_wf1 H_wf2 H_lk.
        1:{ destruct d2 as [ | [ k2 v2 ] d2 ]; [ reflexivity | ].
            specialize (H_lk k2); cbn [dict_lookup] in H_lk.
            rewrite value_eqb_refl in H_lk; discriminate. }
        destruct d2 as [ | [ k2 v2 ] d2 ].
        1:{ specialize (H_lk k1); cbn [dict_lookup] in H_lk.
            rewrite value_eqb_refl in H_lk; discriminate. }
        destruct H_wf1 as [ H_hd1 H_wf1 ]; destruct H_wf2 as [ H_hd2 H_wf2 ].
        (* the two heads hold the smallest key of each, so they agree *)
        assert (E_k : k1 = k2).
        1:{ destruct (value_eqb k1 k2) eqn:E; [ apply value_eqb_eq; exact E | ].
            (* otherwise one head's key is absent from the other dictionary *)
            exfalso.
            destruct (value_compare k1 k2) eqn:E_c.
            1: apply value_compare_Eq_eq in E_c; unfold value_eqb in E;
               rewrite E_c, value_compare_refl in E; discriminate.
            (* k1 < k2: then k1 is below every key of d2, so d2 does not
               hold it, while d1's head does *)
            1:{ specialize (H_lk k1); cbn [dict_lookup] in H_lk.
                rewrite value_eqb_refl, E in H_lk.
                rewrite dict_wf_lookup_None in H_lk; [ discriminate | ].
                intros k' v' H_in; apply H_hd2 in H_in.
                unfold value_ltb in H_in |- *.
                destruct (value_compare k2 k') eqn:E_2k'; try discriminate.
                rewrite (value_compare_trans k1 k2 k' E_c E_2k'); reflexivity. }
            (* and k2 < k1 symmetrically *)
            1:{ assert (E_21 : value_compare k2 k1 = Lt).
                1:{ rewrite (value_compare_antisym k1 k2) in E_c.
                    destruct (value_compare k2 k1); cbn in E_c; congruence. }
                specialize (H_lk k2); cbn [dict_lookup] in H_lk.
                rewrite value_eqb_refl in H_lk.
                rewrite (value_eqb_sym k2 k1), E in H_lk.
                rewrite dict_wf_lookup_None in H_lk; [ discriminate | ].
                intros k' v' H_in; apply H_hd1 in H_in.
                unfold value_ltb in H_in |- *.
                destruct (value_compare k1 k') eqn:E_1k'; try discriminate.
                rewrite (value_compare_trans k2 k1 k' E_21 E_1k'); reflexivity. } }
        subst k2.
        (* then the values at that key, and then the tails *)
        assert (E_v : v1 = v2).
        1:{ specialize (H_lk k1); cbn [dict_lookup] in H_lk.
            rewrite value_eqb_refl in H_lk; injection H_lk as H_lk; exact H_lk. }
        subst v2. f_equal.
        apply IH; [ exact H_wf1 | exact H_wf2 | ].
        intros k.
        destruct (value_eqb k k1) eqn:E.
        1:{ (* the head's key is in neither tail *)
            apply value_eqb_eq in E; subst k.
            rewrite (dict_wf_lookup_None d1), (dict_wf_lookup_None d2);
              [ reflexivity | | ]; assumption. }
        1:{ specialize (H_lk k); cbn [dict_lookup] in H_lk.
            rewrite E in H_lk; exact H_lk. }
      Qed.

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

      Lemma tri_step_buckets : forall txt k p a,
          buckets_are_sets a -> buckets_are_sets (tri_step txt k p a).
      Proof.
        unfold buckets_are_sets, tri_step; intros * H.
        destruct a as [ | | | | | | | d | | | ]; try contradiction.
        apply Forall_dict_insert; [ exact H | ].
        cbn [snd]; unfold bucket_insert.
        destruct (dict_lookup (tri_key txt p) d) as [ b | ] eqn:E_lk; [ | exact I ].
        (* a bucket already there is a set, by the invariant *)
        apply DictIndexImpl.dict_lookup_Some_In in E_lk.
        eapply List.Forall_In in H; [ | exact E_lk ].
        cbn [snd] in H. destruct b; try contradiction. exact I.
      Qed.

      Lemma tri_fold_buckets : forall txt k l a,
          buckets_are_sets a -> buckets_are_sets (fold_right (tri_step txt k) a l).
      Proof.
        intros * H; induction l as [ | p l IH ]; cbn [fold_right];
          [ exact H | apply tri_step_buckets, IH ].
      Qed.

      Lemma tri_entries_buckets : forall l a,
          buckets_are_sets a ->
          buckets_are_sets
            (fold_right (fun r a' => tri_row_step (row_str r) (row_key key r) a') a l).
      Proof.
        intros * H; induction l as [ | r l IH ]; cbn [fold_right]; [ exact H | ].
        unfold tri_row_step; apply tri_fold_buckets, IH.
      Qed.

      (* Nothing ever removes a key from a bucket. *)
      Lemma tri_step_monotone : forall txt k' g k p a,
          key_at g k a -> key_at g k (tri_step txt k' p a).
      Proof.
        unfold key_at, tri_step; intros * H.
        destruct a as [ | | | | | | | d | | | ]; try contradiction.
        destruct (value_eqb_dec (tri_key txt p) g) as [ E | E ].
        1:{ subst g. rewrite DictIndexImpl.dict_lookup_insert_same.
            unfold bucket_insert.
            destruct (dict_lookup (tri_key txt p) d) as [ b | ];
              [ | contradiction ].
            destruct b; try contradiction.
            apply set_insert_incl_r; right; exact H. }
        1:{ rewrite DictIndexImpl.dict_lookup_insert_diff by congruence. exact H. }
      Qed.

      Lemma tri_fold_monotone : forall txt k' g k l a,
          key_at g k a -> key_at g k (fold_right (tri_step txt k') a l).
      Proof.
        intros * H; induction l as [ | p l IH ]; cbn [fold_right];
          [ exact H | apply tri_step_monotone, IH ].
      Qed.

      Lemma tri_entries_monotone : forall g k l a,
          key_at g k a ->
          key_at g k
            (fold_right (fun r a' => tri_row_step (row_str r) (row_key key r) a') a l).
      Proof.
        intros * H; induction l as [ | r l IH ]; cbn [fold_right]; [ exact H | ].
        unfold tri_row_step; apply tri_fold_monotone, IH.
      Qed.

      (* And a position whose trigram is g puts the key there. *)
      Lemma tri_fold_establishes : forall txt k g l a,
          buckets_are_sets a ->
          In g (List.map (tri_key txt) l) ->
          key_at g k (fold_right (tri_step txt k) a l).
      Proof.
        intros * H_bs H_in.
        induction l as [ | p l IH ]; cbn [List.map fold_right] in H_in |- *.
        1: contradiction.
        destruct H_in as [ E_g | H_in ].
        (* here: the key goes into this bucket *)
        1:{ subst g.
            pose proof (tri_fold_buckets txt k l a H_bs) as H_bs'.
            (* name the accumulator before destructing it, so the invariant
               about it is destructed too *)
            remember (fold_right (tri_step txt k) a l) as A eqn:E_A.
            unfold buckets_are_sets in H_bs'.
            destruct A as [ | | | | | | | d | | | ]; try contradiction.
            unfold key_at, tri_step.
            rewrite DictIndexImpl.dict_lookup_insert_same.
            unfold bucket_insert.
            destruct (dict_lookup (tri_key txt p) d) as [ b | ] eqn:E_lk.
            1:{ apply DictIndexImpl.dict_lookup_Some_In in E_lk.
                eapply List.Forall_In in H_bs'; [ | exact E_lk ].
                cbn [snd] in H_bs'. destruct b; try contradiction.
                apply set_insert_incl_r; left; reflexivity. }
            1: apply set_insert_incl_r; left; reflexivity. }
        (* further on: whatever goes in later cannot take it out *)
        1: apply tri_step_monotone, IH; exact H_in.
      Qed.

      Lemma In_eval_range : forall n lo i,
          (i < n)%nat -> In (VInt (lo + Z.of_nat i) : value) (eval_range lo n).
      Proof.
        induction n as [ | n IH ]; intros lo i H_lt; cbn [eval_range]; [ lia | ].
        destruct i as [ | i ].
        1: left; f_equal; lia.
        1:{ right.
            replace (lo + Z.of_nat (S i))%Z with ((lo + 1) + Z.of_nat i)%Z by lia.
            apply IH. lia. }
      Qed.

      (* The other half: a key in a bucket came from a row of the table.
         Not the same as soundness of the SEARCH -- the row's text need not
         contain the pattern, only one trigram of it -- but it is what keeps a
         lookup from inventing rows, and so what a rewrite needs beside
         completeness. *)
      Lemma tri_step_inv : forall txt k' g k p a,
          key_at g k (tri_step txt k' p a) -> k = k' \/ key_at g k a.
      Proof.
        unfold key_at, tri_step; intros * H.
        destruct a as [ | | | | | | | d | | | ]; try contradiction.
        destruct (value_eqb_dec (tri_key txt p) g) as [ E | E ].
        1:{ subst g. rewrite DictIndexImpl.dict_lookup_insert_same in H.
            unfold bucket_insert in H.
            destruct (dict_lookup (tri_key txt p) d) as [ b | ].
            1:{ destruct b; try contradiction.
                apply set_insert_incl in H; intuition auto. }
            1:{ apply set_insert_incl in H; cbn in H; intuition auto. } }
        1:{ rewrite DictIndexImpl.dict_lookup_insert_diff in H by congruence.
            right; exact H. }
      Qed.

      Lemma tri_fold_inv : forall txt k' g k l a,
          key_at g k (fold_right (tri_step txt k') a l) -> k = k' \/ key_at g k a.
      Proof.
        intros * H; induction l as [ | p l IH ]; cbn [fold_right] in H;
          [ right; exact H | ].
        apply tri_step_inv in H; intuition auto.
      Qed.

      Lemma tri_entries_inv : forall l g k,
          key_at g k (tri_entries l) -> exists r, In r l /\ row_key key r = k.
      Proof.
        unfold tri_entries; intros l g k.
        induction l as [ | r l IH ]; cbn [fold_right]; intros H.
        1:{ unfold key_at in H; cbn [dict_lookup] in H; contradiction. }
        unfold tri_row_step in H.
        apply tri_fold_inv in H as [ E | H ].
        1: exists r; split; [ left; reflexivity | symmetry; exact E ].
        1:{ destruct (IH H) as [ r' [ H_in E ] ].
            exists r'; split; [ right; exact H_in | exact E ]. }
      Qed.

      (* Every trigram of a text is the trigram at one of its positions. *)
      Lemma In_trigrams_tri_key : forall txt g,
          In g (trigrams txt) ->
          In (VString g) (List.map (tri_key txt) (tri_positions txt)).
      Proof.
        unfold trigrams, tri_positions; intros txt g H_in.
        apply in_map_iff in H_in as [ i [ E_g H_i ] ].
        apply in_seq in H_i.
        apply in_map_iff. exists (VInt (Z.of_nat i)); split.
        1:{ unfold tri_key. rewrite Nat2Z.id. rewrite E_g. reflexivity. }
        1:{ replace (Z.of_nat i) with (0 + Z.of_nat i)%Z by lia.
            apply In_eval_range. lia. }
      Qed.

      (* The claim: a row whose text contains the pattern has its key in the
         bucket of the pattern's first trigram. *)
      Theorem tri_lookup_complete : forall (l : list value) r p,
          In r l ->
          3 <= String.length p ->
          String.index 0 p (row_str r) <> None ->
          key_at (VString (String.substring 0 3 p)) (row_key key r) (tri_entries l).
      Proof.
        intros l r p H_in H_len H_occ.
        (* the pattern's first trigram is one of the row's text's trigrams *)
        destruct (String.index 0 p (row_str r)) as [ m | ] eqn:E_idx;
          [ | contradiction ].
        pose proof (occurrence_first_trigram p (row_str r) m H_len E_idx) as H_tri.
        apply In_trigrams_tri_key in H_tri.
        (* split the table at the row *)
        apply in_split in H_in as [ l1 [ l2 E_l ] ]; subst l.
        unfold tri_entries; rewrite fold_right_app.
        apply tri_entries_monotone.
        cbn [fold_right]; unfold tri_row_step.
        apply tri_fold_establishes; [ | exact H_tri ].
        apply tri_entries_buckets. cbn [buckets_are_sets]. constructor.
      Qed.

      (* And the hypothesis above is exactly what a substring query's filter
         computes, so nothing is lost in translation: OStrContains IS
         String.index. *)
      Corollary tri_lookup_complete_contains : forall (l : list value) r p,
          In r l ->
          3 <= String.length p ->
          interp_binop OStrContains (VString (row_str r) : value) (VString p)
          = VBool true ->
          key_at (VString (String.substring 0 3 p)) (row_key key r) (tri_entries l).
      Proof.
        intros * H_in H_len H_c.
        apply tri_lookup_complete; [ exact H_in | exact H_len | ].
        intro E_none. cbn [interp_binop] in H_c.
        rewrite E_none in H_c. discriminate.
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

      (* the index's steps, on dictionaries *)
      Definition tri_step_d (txt : string) (k p : value)
        (d : list (value * value)) : list (value * value) :=
        dict_insert (tri_key txt p)
          (bucket_insert k (dict_lookup (tri_key txt p) d)) d.

      (* unfolding only the outer, fully applied step: "unfold tri_step_d"
         would also unfold the one inside the fold, and the induction
         hypothesis is stated in terms of that one *)
      Lemma tri_step_d_eq : forall txt k p (d : list (value * value)),
          tri_step_d txt k p d
          = dict_insert (tri_key txt p)
              (bucket_insert k (dict_lookup (tri_key txt p) d)) d.
      Proof. reflexivity. Qed.

      Definition tri_row_step_d (txt : string) (k : value)
        (d : list (value * value)) : list (value * value) :=
        fold_right (tri_step_d txt k) d (tri_positions txt).

      Definition tri_dict (l : list value) : list (value * value) :=
        fold_right (fun r d => tri_row_step_d (row_str r) (row_key key r) d) nil l.

      Lemma tri_row_step_VDict : forall txt k d,
          tri_row_step txt k (VDict d) = VDict (tri_row_step_d txt k d).
      Proof.
        unfold tri_row_step, tri_row_step_d; intros txt k d.
        induction (tri_positions txt) as [ | p ps IH ]; cbn [fold_right];
          [ reflexivity | ].
        rewrite IH. reflexivity.
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

      (* the trigrams of a text, as the keys the index files a row under *)
      Definition tri_keys (txt : string) : list value :=
        List.map (tri_key txt) (tri_positions txt).

      (* and the keys the index ought to hold at g: those of the rows whose
         text has g among its trigrams *)
      Definition keys_at (g : value) (l : list value) : list value :=
        fold_right (fun r b => if set_mem g (tri_keys (row_str r))
                               then set_insert (row_key key r) b
                               else b) nil l.

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

      Lemma tri_step_d_preserve_tri_wf : forall txt k p d,
          tri_wf d -> tri_wf (tri_step_d txt k p d).
      Proof.
        unfold tri_wf, tri_step_d; intros * [ H_wf H_ne ].
        split; [ apply dict_insert_preserve_dict_wf; exact H_wf | ].
        apply Forall_dict_insert_entry; [ | exact H_ne ].
        cbn [snd]. unfold bucket_insert.
        destruct (dict_lookup (tri_key txt p) d) as [ bk | ] eqn:E.
        1:{ (* the entry that was there is a set, by the invariant *)
            apply (Forall_dict_lookup _ _ _ _ H_ne) in E as [ b [ E_b _ ] ].
            cbn [snd] in E_b; subst bk.
            exists (set_insert k b); split; [ reflexivity | apply set_insert_not_nil ]. }
        1: exists (set_insert k nil); split; [ reflexivity | apply set_insert_not_nil ].
      Qed.

      Lemma tri_row_step_d_preserve_tri_wf : forall txt k d,
          tri_wf d -> tri_wf (tri_row_step_d txt k d).
      Proof.
        unfold tri_row_step_d; intros txt k d H.
        induction (tri_positions txt) as [ | p ps IH ]; cbn [fold_right];
          [ exact H | ].
        apply tri_step_d_preserve_tri_wf; exact IH.
      Qed.

      Lemma tri_dict_tri_wf : forall l, tri_wf (tri_dict l).
      Proof.
        unfold tri_dict; induction l as [ | r l IH ]; cbn [fold_right].
        1: split; [ exact I | constructor ].
        1: apply tri_row_step_d_preserve_tri_wf; exact IH.
      Qed.

      (* One row's step, bucket by bucket: it touches the buckets of its
         own trigrams and nothing else.  Both lemmas are about a fold over
         an ARBITRARY list of positions, since the induction peels one
         position off and the rest is no longer a text's position list. *)
      Lemma tri_fold_d_lookup_other : forall txt k ps d g,
          set_mem g (List.map (tri_key txt) ps) = false ->
          dict_lookup g (fold_right (tri_step_d txt k) d ps) = dict_lookup g d.
      Proof.
        intros txt k ps d g.
        induction ps as [ | p ps IH ]; cbn [fold_right List.map];
          [ reflexivity | ].
        intros H_mem.
        unfold set_mem in H_mem; cbn [existsb] in H_mem.
        rewrite Bool.orb_false_iff in H_mem; destruct H_mem as [ H_p H_ps ].
        rewrite tri_step_d_eq.
        rewrite DictIndexImpl.dict_lookup_insert_diff
          by (apply value_eqb_neq; exact H_p).
        apply IH; exact H_ps.
      Qed.

      Lemma tri_fold_d_lookup_same : forall txt k ps d g,
          tri_wf d ->
          set_mem g (List.map (tri_key txt) ps) = true ->
          dict_lookup g (fold_right (tri_step_d txt k) d ps)
          = Some (VSet (set_insert k (bucket_of g d))).
      Proof.
        intros txt k ps d g H_wf.
        induction ps as [ | p ps IH ]; cbn [fold_right List.map];
          [ discriminate | ].
        intros H_mem.
        unfold set_mem in H_mem; cbn [existsb] in H_mem.
        rewrite Bool.orb_true_iff in H_mem.
        destruct (value_eqb g (tri_key txt p)) eqn:E_p.
        1:{ (* this position's trigram is g: the key goes in here, on top of
               whatever the later positions left *)
            apply value_eqb_eq in E_p; subst g.
            rewrite tri_step_d_eq, DictIndexImpl.dict_lookup_insert_same.
            destruct (set_mem (tri_key txt p) (List.map (tri_key txt) ps)) eqn:E_ps.
            1:{ rewrite (IH eq_refl). unfold bucket_insert.
                rewrite set_insert_idem; reflexivity. }
            1:{ rewrite (tri_fold_d_lookup_other txt k ps d (tri_key txt p) E_ps).
                (* the bucket that was there is a set, by the invariant *)
                unfold bucket_insert, bucket_of.
                destruct (dict_lookup (tri_key txt p) d) as [ bk | ] eqn:E;
                  [ | reflexivity ].
                destruct H_wf as [ _ H_ne ].
                apply (Forall_dict_lookup _ _ _ _ H_ne) in E as [ b [ E_b _ ] ].
                cbn [snd] in E_b; subst bk; reflexivity. } }
        1:{ (* it is not: this position leaves g alone *)
            destruct H_mem as [ E | H_ps ]; [ congruence | ].
            rewrite tri_step_d_eq.
            rewrite DictIndexImpl.dict_lookup_insert_diff
              by (apply value_eqb_neq; exact E_p).
            apply IH; exact H_ps. }
      Qed.

      Corollary tri_row_step_d_lookup_other : forall txt k d g,
          set_mem g (tri_keys txt) = false ->
          dict_lookup g (tri_row_step_d txt k d) = dict_lookup g d.
      Proof. intros; apply tri_fold_d_lookup_other; assumption. Qed.

      Corollary tri_row_step_d_lookup_same : forall txt k d g,
          tri_wf d ->
          set_mem g (tri_keys txt) = true ->
          dict_lookup g (tri_row_step_d txt k d)
          = Some (VSet (set_insert k (bucket_of g d))).
      Proof. intros; apply tri_fold_d_lookup_same; assumption. Qed.

      (* folded equations for the two fold_rights over rows, so that the
         induction below never has to unfold them *)
      Lemma tri_dict_cons : forall r l,
          tri_dict (r :: l)
          = tri_row_step_d (row_str r) (row_key key r) (tri_dict l).
      Proof. reflexivity. Qed.

      Lemma keys_at_cons : forall g r l,
          keys_at g (r :: l)
          = if set_mem g (tri_keys (row_str r))
            then set_insert (row_key key r) (keys_at g l)
            else keys_at g l.
      Proof. reflexivity. Qed.

      (* and so the index's bucket at g holds exactly the keys it ought to:
         those of the rows whose text has g among its trigrams, and no
         entry at all when there are none *)
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
        destruct (set_mem g (tri_keys (row_str r))) eqn:E_mem.
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

      Definition tri_unstep_d (txt : string) (k p : value)
        (d : list (value * value)) : list (value * value) :=
        match dict_lookup (tri_key txt p) d with
        | Some (VSet b) =>
            if value_eqb (VSet (bucket_remove k b)) (VSet nil)
            then dict_delete (tri_key txt p) d
            else dict_insert (tri_key txt p) (VSet (bucket_remove k b)) d
        | _ => d
        end.

      Definition tri_row_unstep_d (txt : string) (k : value)
        (d : list (value * value)) : list (value * value) :=
        fold_right (tri_unstep_d txt k) d (tri_positions txt).

      Lemma tri_unstep_d_eq : forall txt k p (d : list (value * value)),
          tri_unstep_d txt k p d
          = match dict_lookup (tri_key txt p) d with
            | Some (VSet b) =>
                if value_eqb (VSet (bucket_remove k b)) (VSet nil)
                then dict_delete (tri_key txt p) d
                else dict_insert (tri_key txt p) (VSet (bucket_remove k b)) d
            | _ => d
            end.
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

      Lemma dict_lookup_delete_same : forall (d : list (value * value)) (k : value),
          dict_wf d -> dict_lookup k (dict_delete k d) = None.
      Proof.
        induction d as [ | [ k0 v0 ] d IH ]; cbn [dict_delete dict_wf];
          intros k H_wf; [ reflexivity | ].
        destruct H_wf as [ H_hd H_wf ].
        destruct (value_eqb k k0) eqn:E.
        1:{ (* the entry goes, and the rest holds strictly larger keys *)
            apply value_eqb_eq in E; subst k0.
            apply dict_wf_lookup_None; exact H_hd. }
        1:{ cbn [dict_lookup]; rewrite E. apply IH; exact H_wf. }
      Qed.

      Lemma Forall_dict_delete : forall (P : value * value -> Prop) k d,
          Forall P d -> Forall P (dict_delete k d).
      Proof.
        intros * H. apply Forall_forall; intros e H_in.
        apply dict_delete_incl in H_in.
        rewrite Forall_forall in H; apply H; exact H_in.
      Qed.

      Lemma tri_unstep_d_preserve_tri_wf : forall txt k p d,
          tri_wf d -> tri_wf (tri_unstep_d txt k p d).
      Proof.
        unfold tri_wf; intros * [ H_wf H_ne ].
        rewrite tri_unstep_d_eq.
        destruct (dict_lookup (tri_key txt p) d) as [ bk | ];
          [ | split; assumption ].
        destruct bk as [ | | | | | | | | | b | ]; try (split; assumption).
        destruct (value_eqb (VSet (bucket_remove k b)) (VSet nil)) eqn:E.
        1: split; [ apply dict_delete_preserve_dict_wf; exact H_wf
                  | apply Forall_dict_delete; exact H_ne ].
        1:{ split; [ apply dict_insert_preserve_dict_wf; exact H_wf | ].
            apply Forall_dict_insert_entry; [ | exact H_ne ].
            cbn [snd]; exists (bucket_remove k b); split; [ reflexivity | ].
            intro E_nil; rewrite E_nil, value_eqb_refl in E; discriminate. }
      Qed.

      Lemma tri_unstep_d_lookup_diff : forall txt k p d g,
          tri_wf d ->
          value_eqb g (tri_key txt p) = false ->
          dict_lookup g (tri_unstep_d txt k p d) = dict_lookup g d.
      Proof.
        intros * [ H_wf _ ] H_ne.
        apply value_eqb_neq in H_ne.
        rewrite tri_unstep_d_eq.
        destruct (dict_lookup (tri_key txt p) d) as [ bk | ]; [ | reflexivity ].
        destruct bk as [ | | | | | | | | | b | ]; try reflexivity.
        destruct (value_eqb (VSet (bucket_remove k b)) (VSet nil)).
        1: apply dict_lookup_delete_diff; exact H_ne.
        1: apply DictIndexImpl.dict_lookup_insert_diff; exact H_ne.
      Qed.

      Lemma tri_unfold_d_preserve_tri_wf : forall txt k ps d,
          tri_wf d -> tri_wf (fold_right (tri_unstep_d txt k) d ps).
      Proof.
        intros txt k ps d H.
        induction ps as [ | p ps IH ]; cbn [fold_right]; [ exact H | ].
        apply tri_unstep_d_preserve_tri_wf; exact IH.
      Qed.

      Lemma tri_unfold_d_lookup_other : forall txt k ps d g,
          tri_wf d ->
          set_mem g (List.map (tri_key txt) ps) = false ->
          dict_lookup g (fold_right (tri_unstep_d txt k) d ps) = dict_lookup g d.
      Proof.
        intros txt k ps d g H_wf.
        induction ps as [ | p ps IH ]; cbn [fold_right List.map];
          [ reflexivity | ].
        intros H_mem.
        unfold set_mem in H_mem; cbn [existsb] in H_mem.
        rewrite Bool.orb_false_iff in H_mem; destruct H_mem as [ H_p H_ps ].
        rewrite (tri_unstep_d_lookup_diff txt k p _ g
                   (tri_unfold_d_preserve_tri_wf txt k ps d H_wf) H_p).
        apply IH; exact H_ps.
      Qed.

      (* and at a trigram the row does have: the bucket loses the key, and
         the entry goes with it if that empties it *)
      Lemma tri_unfold_d_lookup_same : forall txt k ps d g,
          tri_wf d ->
          set_mem g (List.map (tri_key txt) ps) = true ->
          dict_lookup g (fold_right (tri_unstep_d txt k) d ps)
          = match bucket_remove k (bucket_of g d) with
            | nil => None
            | b => Some (VSet b)
            end.
      Proof.
        intros txt k ps d g H_wf.
        induction ps as [ | p ps IH ]; cbn [fold_right List.map];
          [ discriminate | ].
        intros H_mem.
        unfold set_mem in H_mem; cbn [existsb] in H_mem.
        rewrite Bool.orb_true_iff in H_mem.
        destruct (value_eqb g (tri_key txt p)) eqn:E_p.
        2:{ (* this position leaves g alone *)
            destruct H_mem as [ E | H_ps ]; [ congruence | ].
            rewrite (tri_unstep_d_lookup_diff txt k p _ g
                       (tri_unfold_d_preserve_tri_wf txt k ps d H_wf) E_p).
            apply IH; exact H_ps. }
        (* this position's trigram IS g *)
        apply value_eqb_eq in E_p; subst g.
        rewrite tri_unstep_d_eq.
        destruct (set_mem (tri_key txt p) (List.map (tri_key txt) ps)) eqn:E_ps.
        1:{ (* a later position already removed the key here, and removing
               it again changes nothing *)
            rewrite (IH eq_refl).
            destruct (bucket_remove k (bucket_of (tri_key txt p) d)) as [ | v b ]
                                                                        eqn:E_b.
            (* nothing is left at g, so there is no entry to remove from *)
            1: cbv beta iota; exact (IH eq_refl).
            (* the bucket here is already the removed one, and removing
               the key from it again changes nothing *)
            1:{ cbv beta iota. rewrite <- E_b, bucket_remove_idem, E_b.
                destruct (value_eqb (VSet (v :: b)) (VSet nil)) eqn:E_nil.
                1: apply VSet_nil_eqb in E_nil; discriminate.
                1: apply DictIndexImpl.dict_lookup_insert_same. } }
        1:{ (* no later position did, so the bucket here is the original *)
            rewrite (tri_unfold_d_lookup_other txt k ps d (tri_key txt p) H_wf E_ps).
            unfold bucket_of.
            destruct (dict_lookup (tri_key txt p) d) as [ bk | ] eqn:E_lk.
            (* no entry at g at all: nothing to remove, and nothing is
               owed there either *)
            2:{ cbv beta iota; cbn [bucket_remove filter].
                rewrite (tri_unfold_d_lookup_other txt k ps d (tri_key txt p)
                           H_wf E_ps).
                exact E_lk. }
            (* the entry is a set, by the invariant *)
            pose proof H_wf as H_wf'; destruct H_wf' as [ H_dwf H_ne ].
            apply (Forall_dict_lookup _ _ _ _ H_ne) in E_lk as E_set.
            destruct E_set as [ b [ E_b _ ] ]; cbn [snd] in E_b; subst bk.
            destruct (value_eqb (VSet (bucket_remove k b)) (VSet nil)) eqn:E_nil.
            (* the last key goes, so the entry goes: and the delete is on
               the dictionary the later positions left, not on d *)
            1:{ apply VSet_nil_eqb in E_nil; rewrite E_nil.
                apply dict_lookup_delete_same.
                apply (proj1 (tri_unfold_d_preserve_tri_wf txt k ps d H_wf)). }
            1:{ destruct (bucket_remove k b) as [ | v b' ] eqn:E_br.
                (* the test already said the removal leaves something *)
                1:{ try rewrite E_br in E_nil;
                    rewrite value_eqb_refl in E_nil; discriminate. }
                1:{ rewrite DictIndexImpl.dict_lookup_insert_same; reflexivity. } } }
      Qed.

      (* ------------------------------------------------------------------
         What the delete body computes.  Unlike the insert body, this one
         needs the invariant: on a bucket that is not a set the expression
         would insert garbage, where the mirror leaves the dictionary
         alone, so the two agree only where every bucket is a set.
         ------------------------------------------------------------------ *)
      Lemma interp_tri_delete : forall (store env : locals) r txt p d,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          map.get env pos = Some p ->
          map.get env sacc = Some (VDict d) ->
          tri_wf d ->
          interp_expr store env tri_delete_body
          = VDict (tri_unstep_d txt (row_key key r) p d).
      Proof.
        unfold tri_delete_body, tri_without_pk, trigram_at, row_text, row_pk.
        intros * H_txt E_tup E_pos E_sacc [ _ H_ne ].
        cbn [interp_expr].
        unfold get_local; rewrite E_tup, E_pos, E_sacc.
        unfold row_key in H_txt |- *.
        destruct r as [ | | | | | | rv | | | | ]; try discriminate.
        rewrite H_txt, interp_trigram_at_val.
        (* the mirror is unfolded here so that its removal and the one the
           interpreter computes are the same term, and the test can be
           destructed once for both sides *)
        rewrite tri_unstep_d_eq; unfold bucket_remove.
        cbn [interp_binop].
        destruct (dict_lookup (tri_key txt p) d) as [ bk | ] eqn:E_lk;
          cbn [interp_atom]; [ | reflexivity ].
        (* the bucket is a set, by the invariant *)
        apply (Forall_dict_lookup _ _ _ _ H_ne) in E_lk as E_set.
        destruct E_set as [ b [ E_b _ ] ]; cbn [snd] in E_b; subst bk.
        (* the bucket binder is in the way of every read the branches make *)
        rewrite !map.get_put_same.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_diff by congruence.
        rewrite !map.get_put_diff by congruence.
        rewrite E_tup, E_pos, E_sacc.
        rewrite H_txt, interp_trigram_at_val.
        cbn [interp_binop interp_atom].
        lazymatch goal with
        | |- context[if ?tst then _ else _] => destruct tst eqn:E_nil
        end.
        all: cbn [interp_expr interp_binop interp_ternop interp_atom].
        all: unfold get_local.
        all: rewrite ?map.get_put_diff by congruence.
        all: rewrite ?E_tup, ?E_pos, ?E_sacc.
        all: rewrite ?H_txt, ?interp_trigram_at_val.
        all: reflexivity.
      Qed.

      Lemma interp_tri_delete_fold : forall (store env : locals) r txt d ps,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          tri_wf d ->
          fold_right
            (fun p a' => interp_expr store
                           (map.put (map.put env pos p) sacc a') tri_delete_body)
            (VDict d) ps
          = VDict (fold_right (tri_unstep_d txt (row_key key r)) d ps).
      Proof.
        intros * H_txt E_tup H_wf.
        induction ps as [ | p ps IH ]; cbn [fold_right]; [ reflexivity | ].
        rewrite IH.
        apply interp_tri_delete;
          [ exact H_txt | | | apply map.get_put_same | ].
        1:{ rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact E_tup. }
        1:{ rewrite map.get_put_diff by congruence. apply map.get_put_same. }
        1: apply tri_unfold_d_preserve_tri_wf; exact H_wf.
      Qed.

      Lemma interp_tri_row_delete : forall (store env : locals) r txt d,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          map.get env acc = Some (VDict d) ->
          tri_wf d ->
          interp_expr store env tri_row_delete_body
          = VDict (tri_row_unstep_d txt (row_key key r) d).
      Proof.
        intros * H_txt E_tup E_acc H_wf.
        unfold tri_row_delete_body, tri_row_unstep_d.
        rewrite interp_EFold.
        rewrite (interp_trigram_positions store env r txt H_txt E_tup).
        rewrite interp_EVar; unfold get_local; rewrite E_acc.
        apply interp_tri_delete_fold; assumption.
      Qed.

      Corollary tri_row_unstep_d_lookup_other : forall txt k d g,
          tri_wf d ->
          set_mem g (tri_keys txt) = false ->
          dict_lookup g (tri_row_unstep_d txt k d) = dict_lookup g d.
      Proof. intros; apply tri_unfold_d_lookup_other; assumption. Qed.

      Corollary tri_row_unstep_d_lookup_same : forall txt k d g,
          tri_wf d ->
          set_mem g (tri_keys txt) = true ->
          dict_lookup g (tri_row_unstep_d txt k d)
          = match bucket_remove k (bucket_of g d) with
            | nil => None
            | b => Some (VSet b)
            end.
      Proof. intros; apply tri_unfold_d_lookup_same; assumption. Qed.

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
          <-> exists r, In r l /\ set_mem g (tri_keys (row_str r)) = true
                        /\ row_key key r = v.
      Proof.
        intros g l v; induction l as [ | r l IH ].
        1:{ rewrite keys_at_nil; split;
            [ intros [] | intros [ r [ [] _ ] ] ]. }
        rewrite keys_at_cons.
        destruct (set_mem g (tri_keys (row_str r))) eqn:E_mem; split.
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
        rewrite keys_at_cons; destruct (set_mem g (tri_keys (row_str r)));
          [ apply set_insert_preserve_SSorted; exact IH | exact IH ].
      Qed.

      Lemma keys_at_NoDup : forall g l, NoDup (keys_at g l).
      Proof.
        intros g l; induction l as [ | r l IH ].
        1: rewrite keys_at_nil; constructor.
        rewrite keys_at_cons; destruct (set_mem g (tri_keys (row_str r)));
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
          set_mem g (tri_keys (row_str r)) = false ->
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
          = tri_row_unstep_d (row_str r) k (tri_dict l).
      Proof.
        intros l r k H_nd H_in E_k.
        apply dict_wf_lookup_ext.
        1: apply (proj1 (tri_dict_tri_wf _)).
        1:{ unfold tri_row_unstep_d.
            apply (proj1 (tri_unfold_d_preserve_tri_wf _ _ _ _ (tri_dict_tri_wf l))). }
        intros g.
        rewrite !tri_dict_lookup.
        destruct (set_mem g (tri_keys (row_str r))) eqn:E_mem.
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

      (* And if no row has the key, the filter removes nothing. *)
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
