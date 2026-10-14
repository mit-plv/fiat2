Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.IndexInterface fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute
  fiat2.StringFacts.
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

    Definition to_idx : expr :=
      EFold (EVar hole) (EAtom (AEmptyDict None)) tup acc
        (EFold (trigram_positions (row_text (EVar tup))) (EVar acc) pos sacc
           (ETernop OInsert (EVar sacc)
              (trigram_at (row_text (EVar tup)) (EVar pos))
              (EOptMatch
                 (EBinop OLookup (EVar sacc)
                    (trigram_at (row_text (EVar tup)) (EVar pos)))
                 (EBinop OSetInsert (EAtom (AEmptySet None)) (row_pk (EVar tup)))
                 bkt
                 (EBinop OSetInsert (EVar bkt) (row_pk (EVar tup)))))).

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
        unfold is_tbl_ty, idx_ty, to_idx, row_text, row_pk,
          trigram_positions, trigram_at.
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

      Instance trigram_idx : IndexInterface.index :=
        IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

      Instance trigram_idx_ok : IndexInterface.ok trigram_idx idx_wf :=
        IndexInterface.Build_ok trigram_idx idx_wf idx_ty_wf to_idx_ty to_idx_wf.

    End WithMap.
  End WithVars.
End WithHole.
