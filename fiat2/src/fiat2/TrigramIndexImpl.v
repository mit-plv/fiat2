Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.IndexInterface fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute
  fiat2.StringFacts fiat2.Constraint fiat2.CollectionTransf.
Require fiat2.DictIndexImpl.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Lia.
Import ListNotations.

Open Scope string_scope.

(* An inverted index for substring search: trigram -> the primary keys of the
   rows whose text contains it.

   This is the first index here that puts a row under MORE THAN ONE key: a
   text of length n has n-2 trigrams, and the row's key goes into the bucket
   of each.  It is also the first that is deliberately LOSSY in the other
   direction -- the bucket holds keys, not rows -- so it only pays off beside
   a primary-key index, which turns a key back into its row.  That pairing is
   the point: the two indexes are members of ONE index record, the trigram
   dictionary built here and the key-to-row dictionary of UniqueDictIndexImpl,
   and a substring query is answered by one lookup in each.

   Why a SET of keys and not a bag or a list.  A text may contain the same
   trigram twice ("aaaa" contains "aaa" at two positions), so a bag would hold
   a row's key once per occurrence and a lookup that emitted one row per entry
   would return that row twice -- wrong, not merely slow.  Deduplication is
   therefore part of correctness, not an optimization.  Nothing is lost by it:
   real trigram indexes (PostgreSQL's GIN over pg_trgm, say) hold posting
   lists of distinct row identifiers and the scan that follows returns each
   row once, in no particular order -- so a query answered this way is a bag
   or set query, never a list query, and the order the keys come back in is
   not observable.  A set is also what the maintenance rewrites want: one
   insertion per occurrence is idempotent.

   What this index claims, like every other, is only that it is what to_idx
   computes.  That is true of any table.  What it does NOT give by itself is
   the step from "the bucket of one trigram of the pattern" to "every row that
   contains the pattern", which rests on occurrence_first_trigram in
   StringFacts, nor the step back from a key to its row, which rests on the
   declared primary key. *)

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
      EFold (EVar hole) (EAtom (AEmptyDict None)) tup acc tri_row_body.

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
      | TList (TRecord rt) => TDict TString (TSet (get_attr_type rt key))
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

      (* reading a variable out of the environment the folds have built *)
      Ltac lookup_var :=
        apply TyEVar; repeat (rewrite map.get_put_diff by congruence);
        rewrite map.get_put_same; reflexivity.

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
         mirror is two nested fold_rights.  Every existing index puts a row
         under exactly one key and so has nothing like this; the inner fold is
         what makes a trigram index a trigram index.
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

      Lemma interp_trigram_positions : forall (env : locals) r txt,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          interp_expr map.empty env (trigram_positions (row_text (EVar tup)))
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

      Lemma interp_tri_insert : forall (env : locals) r txt p a,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          map.get env pos = Some p ->
          map.get env sacc = Some a ->
          interp_expr map.empty env tri_insert_body
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
      Lemma interp_tri_fold : forall (env : locals) r txt a l,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          fold_right
            (fun p a' => interp_expr map.empty
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
      Lemma interp_tri_row : forall (env : locals) r txt a,
          row_key attr r = VString txt ->
          map.get env tup = Some r ->
          map.get env acc = Some a ->
          interp_expr map.empty env tri_row_body
          = tri_row_step txt (row_key key r) a.
      Proof.
        intros * H_txt E_tup E_acc. unfold tri_row_body, tri_row_step.
        rewrite interp_EFold.
        rewrite (interp_trigram_positions env r txt H_txt E_tup).
        rewrite interp_EVar; unfold get_local; rewrite E_acc.
        apply interp_tri_fold; assumption.
      Qed.

      (* The outer fold, over the rows.  Every row has to carry a string at
         attr, which is what is_tbl_ty asks of the table's type. *)
      Lemma interp_to_idx_fold : forall (env : locals) (l : list value) a,
          Forall (fun r => exists txt, row_key attr r = VString txt) l ->
          fold_right
            (fun r a' => interp_expr map.empty
                           (map.put (map.put env tup r) acc a') tri_row_body)
            a l
          = fold_right (fun r a' => tri_row_step (row_str r) (row_key key r) a') a l.
      Proof.
        intros env l a H_all.
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

      Instance trigram_idx : IndexInterface.index :=
        IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

      Instance trigram_idx_ok : IndexInterface.ok trigram_idx idx_wf :=
        IndexInterface.Build_ok trigram_idx idx_wf idx_ty_wf to_idx_ty to_idx_wf.

    End WithMap.
  End WithVars.
End WithHole.
