Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.FlatmapForms fiat2.TrigramIndexUse
  fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   Source
     wagtail/modelsearch 1.3.2 (wagtail delegates search to the
     modelsearch package, pinned >=1.3.2,<1.4 in pyproject.toml; every
     file under wagtail/search/backends/ is a one-line re-export).
     Read from the PyPI sdist.

     modelsearch/backends/database/postgres/postgres.py

       :63    DEFAULT_FUZZY_SIMILARITY_THRESHOLD = 0.3
       :272   title_text = " ".join(texts)
       :744   title_similarity = TrigramWordSimilarity(search_string, title_field)
       :748   raw_similarity = Greatest(title_similarity, body_similarity, ...)
       :775   .filter(_fuzzy_raw_similarity__gte=threshold)

     and beside it, over the same two columns,

       modelsearch/management/commands/enable_trigram.py
         CREATE INDEX ... USING gin (title_text gin_trgm_ops)
         CREATE INDEX ... USING gin (body_text  gin_trgm_ops)
         ... and the same two over f_unaccent(...)

     wagtail/search/migrations/0010_add_text_fields.py adds title_text and
     body_text to the index-entry table; the entries are written and
     removed as objects are saved and deleted.

   Pattern
     B8 threshold filter over a scan, beside A1a a hand-built index that
     cannot serve it.  The gap is not an oversight: TrigramWordSimilarity
     emits the WORD_SIMILARITY(...) FUNCTION, which is not in
     gin_trgm_ops, so the four GIN indexes this project creates cannot
     serve the predicate it then writes.  The indexable form is the %>
     OPERATOR, which the ORM does not offer.

   Claim
     C3 for the threshold read.  This is the second substring-family
     subject and it is a different claim from the first: Jenkins_UserSearch
     has an author who built no structure for the read, where here the
     author DID build one, for this very column, and still writes the
     query in a form that scans.

   Faithfulness -- what this translation drops, and why
     * Greatest(title, body) >= t is a_title >= t \/ a_body >= t, and
       enable_trigram.py creates one index per column, so the source
       itself treats the two disjuncts as separable.  The TITLE disjunct is
       modelled.  That is scope, not omission -- but it is scope: the
       program here answers half of the source's predicate.
     * The source filters on the RAW score and ranks on a boosted one
       (postgres.py:748 vs :775).  Only the filter is modelled; the ranking
       is a sort over the rows the filter returns, and nothing here
       observes the order.
     * wagtail computes the NON-STRICT word similarity (<%, whose extents
       may start mid-word); this models the whole-word one (<<%).  The two
       differ on a query that matches the inside of a word.
     * The threshold is the exact rational 3/10, cross-multiplied so that
       no division or float appears.  pg_trgm computes CALCSML in float4,
       so a row sitting exactly on the boundary is the one place the two
       can disagree.
     * Padding is pg_trgm's: LPADDING 2, RPADDING 1, applied per WORD, as
       generate_trgm does it -- which is what makes similarity usable on
       short strings at all.
     * f_unaccent is dropped.  It is a per-row function of the text, and
       the source builds a separate index for it rather than folding it
       into this one.
     * Nothing is added.  Both writes are writes the source performs.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort [("id", TString); ("title_text", TString)]).

Definition query_ty :=
  TRecord (record_sort [("kind", TInt); ("qtext", TString); ("new_entry", row_ty)]).

Section WithConcreteMaps.
  Notation value := (value).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* ---- the predicate, written the way the source computes it ---- *)

  (* pg_trgm pads before extracting: two spaces in front, one behind. *)
  Definition padded (s : expr) : expr :=
    EBinop OConcatString (EAtom (AString "  "))
      (EBinop OConcatString s (EAtom (AString " "))).

  Definition tri_set_of (s : expr) : expr :=
    EUnop OSetOfList (EUnop OTrigrams s).

  (* similarity(query, word) >= 3/10, cross-multiplied:

         c * 10 >= 3 * (a + b - c)

     with a the query's trigram count, b the word's, c the shared count.
     Jaccard, which is what CALCSML computes. *)
  Definition word_at_threshold : expr :=
    ELet (tri_set_of (padded (EVar "wd"))) "wset"
      (ELet (EUnop OSetSize
               (EBinop OSetIntersect (EVar "qset") (EVar "wset"))) "shared"
         (EUnop ONot
            (EBinop OLess
               (EBinop OTimes (EVar "shared") (EAtom (AInt 10)))
               (EBinop OTimes (EAtom (AInt 3))
                  (EBinop OMinus
                     (EBinop OPlus (EVar "qnum") (EUnop OSetSize (EVar "wset")))
                     (EVar "shared")))))).

  Definition qtext : expr := EAccess (EVar "qr") "qtext".

  (* WORD_SIMILARITY(q, title_text) >= 0.3: the greatest similarity between
     the query and any WORD of the text, which at a threshold test is just
     "some word is similar enough". *)
  Definition fuzzy_pred_on (row : string) : expr :=
    ELet (tri_set_of (padded qtext)) "qset"
      (ELet (EUnop OSetSize (EVar "qset")) "qnum"
         (EFold (EBinop OWords (EAtom (AString " "))
                   (EAccess (EVar row) "title_text"))
            (EAtom (ABool false)) "wd" "found"
            (EBinop OOr (EVar "found") word_at_threshold))).

  (* ---- the program ---- *)

  (* _build_fuzzy_queryset's filter, over the entry table. *)
  Definition by_similarity : expr :=
    EUnop OSetOfList
      (flatmap_filter_list (ELoc "entries") "e" (fuzzy_pred_on "e") "e"
         (Some row_ty) (Some row_ty)).

  (* an index entry removed when its object goes *)
  Definition without_key : expr :=
    flatmap_filter_list (ELoc "entries") "e"
      (EUnop ONot (EBinop OEq (EAccess (EVar "e") "id") qtext))
      "e" (Some row_ty) (Some row_ty).

  Definition dispatch (k : Z) (thn els : scommand) : scommand :=
    SIf (EBinop OEq (EAccess (EVar "qr") "kind") (EAtom (AInt k))) thn els.

  Definition prog_s (ds : list decl) : scommand :=
    SLetConstrained "entries" row_ty ds
      (SForeach (EVar "queries") "qr"
         (dispatch 0
            (SAssign "entries"
               (EBinop OCons (EAccess (EVar "qr") "new_entry") (ELoc "entries"))
               SSkip)
            (dispatch 1
               (SAssign "entries" without_key SSkip)
               (SAssign "results" by_similarity SSkip)))).

  Definition init_Gstore : ctenv :=
    map.put map.empty "results" (TSet row_ty).

  Definition init_Genv : ctenv :=
    map.put map.empty "queries" (TList query_ty).

  Definition elaborated (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_s ds).

  Definition decls := [DUnique "id"].

  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition anno : canno_command :=
    CAC (("entries", (row_ty, decls)) :: cenv_rm "entries" []) O
      basics [TrigramIdx "title_text" "id"] [] (elaborated decls).

  Definition optimized : command :=
    apply_optimize_anno_constrained anno init_Gstore init_Genv.

  (* ---- projections, so every claim below is an equality of closed terms ---- *)

  Definition install_of (c : command) : option expr :=
    match c with CLetMut e _ _ => Some e | _ => None end.

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  Definition write_guard (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ (CIf g _ _) _)) => Some g
    | _ => None
    end.

  Definition insert_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ (CIf _ (CAssign _ e) _) _)) => Some e
    | _ => None
    end.

  Definition delete_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ (CIf _ (CAssign _ e) _) _))) =>
        Some e
    | _ => None
    end.

  Definition search_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CAssign _ e)))) => Some e
    | _ => None
    end.

  (* ---- the shapes the claims are stated against ---- *)

  Definition member (i : string) : expr :=
    EAccess (EAccess (ELoc "entries") "aux_tag") i.
  Definition new_entry : expr := EAccess (EVar "qr") "new_entry".
  Definition no_rows : expr := EAtom (ANil (Some row_ty)).

  (* What the index keys on, as generate_trgm does it: the text is split
     into WORDS and each word is padded on its own.  The cross-word windows
     a whole-string extraction would produce are not keys. *)
  Definition tup_words : expr :=
    EBinop OWords (EAtom (AString " ")) (EAccess (EVar "tup") "title_text").
  Definition word_text : expr :=
    EBinop OConcatString (EAtom (AString "  "))
      (EBinop OConcatString (EVar "wrd") (EAtom (AString " "))).
  Definition word_tris : expr := EUnop OTrigrams word_text.
  Definition tup_key : expr := EAccess (EVar "tup") "id".

  (* one row's id into the bucket of every trigram of every word of its
     text: generate_trgm_only's own two loops *)
  Definition post_row (acc : expr) : expr :=
    EFold tup_words acc "wrd" "wacc"
      (EFold word_tris (EVar "wacc") "gvar" "sacc"
         (ETernop OInsert (EVar "sacc") (EVar "gvar")
            (EOptMatch (EBinop OLookup (EVar "sacc") (EVar "gvar"))
               (EBinop OSetInsert (EAtom (AEmptySet None)) tup_key)
               "bkt" (EBinop OSetInsert (EVar "bkt") tup_key)))).

  Definition build_postings (src : expr) : expr :=
    EFold src (EAtom (AEmptyDict Unranged None)) "tup" "acc" (post_row (EVar "acc")).

  Definition build_keys (src : expr) : expr :=
    EFold src (EAtom (AEmptyDict Unranged None)) "tup" "acc"
      (ETernop OInsert (EVar "acc") tup_key (EVar "tup")).

  Definition key_probe (idx k : expr) : expr :=
    EOptMatch (EBinop OLookup idx k)
      (EAtom (AEmptyBag None)) "y"
      (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "y")).

  (* the bucket a trigram names, absent and empty alike *)
  Definition bucket (g : expr) : expr :=
    EOptMatch (EBinop OLookup (member "0") g)
      (EAtom (AEmptySet None)) "b" (EVar "b").

  (* The pool: the UNION of the buckets of every trigram of the padded
     query.  This is where the threshold read parts company with the
     substring read, which intersects -- a row similar enough to the query
     need not share all of its trigrams, only enough of them.  Nominatim
     writes both endpoints by hand and by name: name_vector @> ARRAY[...]
     is the intersection, name_vector && ARRAY[...] is this union. *)
  Definition pool : expr :=
    EOptMatch
      (EACIFold AGUnion
         (EFlatmap LikeSet (tri_set_of (padded qtext)) "cgram"
            (EBinop OSetInsert (EAtom (AEmptySet None)) (bucket (EVar "cgram")))))
      (EAtom (AEmptySet None)) "b" (EVar "b").

  (* THE HOISTED BINDING: each of the query's distinct trigrams paired with
     the bucket it names, built once per query.

     Everything the count needs is loop-invariant across candidates -- the
     trigrams, and the index lookups that find their buckets -- so none of
     it belongs inside the filter.  The earlier shape had all of it there:
     it rebuilt the trigram set TWICE per candidate (once for the count,
     once for the `a` of the test) and looked up every bucket again for
     each one.  Both costs were measured against a hand-built GIN index
     before this was written; see harness/compiled/authors.ml's
     WagtailShapes and `compiled.exe shapes`.

     The PAIRING is what makes it correct, not just faster.  Hoisting the
     buckets alone would collapse two query trigrams that happen to name
     the same keys into one set element, undercounting c -- and c is on the
     admitting side of the test, so undercounting would drop rows and break
     completeness.  Field "0" carries the trigram, which keeps the elements
     distinct. *)
  Definition tri_pairs : expr :=
    EFlatmap LikeSet (tri_set_of (padded qtext)) "cgram"
      (EBinop OSetInsert (EAtom (AEmptySet None))
         (ERecord [("0", EVar "cgram"); ("1", bucket (EVar "cgram"))])).

  (* How many of the query's trigrams name this key: a membership test per
     pair, and no lookup at all.

     A consequence worth recording: the count is now a set-level filter
     directly.  It used to appear as OSetSize (OSetOfList
     (flatmap_filter_list ...)), because the rule emitted a filter over a
     COERCION and a later collection pass pulled the coercion out past it.
     With the source a variable there is no coercion to pull, so the
     per-candidate list-then-set construction is gone as well. *)
  Definition shared_with (k : expr) : expr :=
    EUnop OSetSize
      (flatmap_filter_set (EVar "cgram") "cgram"
         (EBinop OSetMem (EAccess (EVar "cgram") "1") k) "cgram" None None).

  (* c * 10 >= 3 * a, where a is the query's trigram count: the k-of-n count
     test, which is gin_trgm_consistent's own test and a STRICT
     over-approximation of the Jaccard one, since it ignores the row's
     trigram count entirely.  That is why the recheck below is not a
     leftover.

     The ELet is the hoist.  It reuses `cgram`, the trigram binder the rule
     already owns, rather than introducing a name: the inner filter rebinds
     it to each element while the source and the `a` are evaluated outside,
     so the two uses never collide.  What it costs is one more guard
     conjunct -- the pattern may not mention cgram -- which is the same
     price the rule already pays for k and y.

     `a` is the SIZE of the pair set, which is the number of distinct
     trigrams because the pairing is injective. *)
  Definition candidates : expr :=
    ELet tri_pairs "cgram"
      (flatmap_filter_set pool "k"
         (EUnop ONot
            (EBinop OLess
               (EBinop OTimes (shared_with (EVar "k")) (EAtom (AInt 10)))
               (EBinop OTimes (EAtom (AInt 3))
                  (EUnop OSetSize (EVar "cgram")))))
         "k" None None).

  (* ==================== what the choice produces ==================== *)

  (* Two members from one choice: the postings on title_text at "0", the
     primary-key dictionary on id at "1".  A trigram dictionary holds KEYS
     and cannot resolve them on its own, which is why one choice installs
     two members. *)
  Definition install_expected : expr :=
    ERecord
      [("aux_tag", ERecord [("0", build_postings no_rows);
                            ("1", build_keys no_rows)])].

  Lemma installs_the_pair : install_of optimized = Some install_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* And the list is GONE.  The threshold rule leaves NO fallback scan --
     unlike the substring rules, which emit a runtime length test and keep
     the source query as the other branch -- so once both writes are
     maintained the list has no reader at all and erase_dead_field drops
     the field.  The table's whole representation is the two members. *)
  Lemma the_list_does_not_survive :
    installed_fields optimized = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* THE READ, and the reason this file exists.

     WORD_SIMILARITY(q, title_text) >= 0.3 over a scan became: the union of
     the buckets of the query's trigrams, filtered by the count test, each
     surviving key resolved through the key member, and the source's own
     predicate rechecked on the way out.

     Read the recheck: it is fuzzy_pred_on "y" -- literally the predicate
     the source wrote, on the probed row.  Nothing about the threshold is
     re-derived at the exit; the index narrows the rows and the author's
     test decides them.  That is the whole soundness story, and it is why
     only COMPLETENESS of the candidate set had to be proved.

     And there is no guard.  The substring rules must test at run time that
     the pattern is long enough to have a trigram; here the query is PADDED
     before extraction, so it has one whatever it is. *)
  Definition search_expected : expr :=
    EFlatmap LikeSet candidates "k"
      (EOptMatch (EBinop OLookup (member "1") (EVar "k"))
         (EAtom (AEmptySet None)) "y"
         (EIf (fuzzy_pred_on "y")
            (EBinop OSetInsert (EAtom (AEmptySet None)) (EVar "y"))
            (EAtom (AEmptySet None)))).

  Lemma search_is_a_threshold_probe :
    search_of optimized = Some search_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* the entry's id is declared unique, so the write's key check costs one
     probe of the key member rather than a scan *)
  Lemma guard_is_a_probe :
    write_guard optimized
    = Some (EBinop OAnd
              (ELet new_entry "_pk_row"
                 (EBinop OEq (key_probe (member "1") (EAccess (EVar "_pk_row") "id"))
                    (EAtom (AEmptyBag None))))
              (EAtom (ABool true))).
  Proof. vm_compute; reflexivity. Qed.

  (* ==================== and it is MAINTAINED ==================== *)

  (* the new entry's id joins the bucket of each trigram of its own text,
     and the key member at its key.  Neither member is rebuilt. *)
  Definition insert_expected : expr :=
    ERecord
      [("aux_tag",
         ERecord
           [("0", ELet (member "0") "acc"
                    (ELet new_entry "tup" (post_row (EVar "acc"))));
            ("1", ELet (member "1") "acc"
                    (ELet new_entry "tup"
                       (ETernop OInsert (EVar "acc") tup_key (EVar "tup"))))])].

  Lemma insert_maintains_both : insert_of optimized = Some insert_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* The delete is the one worth reading.  The row that leaves is not named
     by the write -- the write names a key -- so the postings are corrected
     by PROBING the key member for that row and removing its id from each
     bucket its own text names, dropping a bucket that empties.  Nothing is
     rebuilt and nothing scans the table. *)
  Definition unpost_row (acc : expr) : expr :=
    EFold tup_words acc "wrd" "wacc"
      (EFold word_tris (EVar "wacc") "gvar" "sacc"
         (EOptMatch (EBinop OLookup (EVar "sacc") (EVar "gvar"))
            (EVar "sacc") "bkt"
            (EIf (EBinop OEq
                    (EBinop OSetDiff (EVar "bkt")
                       (EBinop OSetInsert (EAtom (AEmptySet None)) tup_key))
                    (EAtom (AEmptySet None)))
               (EBinop ODelete (EVar "sacc") (EVar "gvar"))
               (ETernop OInsert (EVar "sacc") (EVar "gvar")
                  (EBinop OSetDiff (EVar "bkt")
                     (EBinop OSetInsert (EAtom (AEmptySet None)) tup_key)))))).

  Definition delete_expected : expr :=
    ERecord
      [("aux_tag",
         ERecord
           [("0", ELet (member "0") "acc"
                    (EOptMatch (EBinop OLookup (member "1") qtext)
                       (EVar "acc") "tup" (unpost_row (EVar "acc"))));
            ("1", EBinop ODelete (member "1") qtext)])].

  Lemma delete_maintains_both : delete_of optimized = Some delete_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* ==================== soundness ==================== *)

  Lemma row_ty_wf : type_wf row_ty.
  Proof. unfold row_ty. repeat constructor; cbn; intuition congruence. Qed.

  Lemma query_ty_wf : type_wf query_ty.
  Proof. unfold query_ty, row_ty. repeat constructor; cbn; intuition congruence. Qed.

  Lemma init_Gstore_wf : tenv_wf init_Gstore.
  Proof.
    unfold init_Gstore; apply tenv_wf_step;
      [ apply tenv_wf_empty | constructor; apply row_ty_wf ].
  Qed.

  Lemma init_Genv_wf : tenv_wf init_Genv.
  Proof.
    unfold init_Genv; apply tenv_wf_step;
      [ apply tenv_wf_empty | constructor; apply query_ty_wf ].
  Qed.

  Lemma decls_wf : Forall (decl_wf (tenv:=ctenv) row_ty) decls.
  Proof.
    unfold decls, row_ty; cbn [decl_wf].
    repeat constructor;
      exists [("id", TString); ("title_text", TString)], TString;
      split; reflexivity.
  Qed.

  Lemma elaborated_well_typed :
    well_typed init_Gstore init_Genv (elaborated decls).
  Proof.
    eapply command_typechecker_sound with (c := elaborated decls).
    1: apply init_Gstore_wf.
    1: apply init_Genv_wf.
    reflexivity.
  Qed.

  (* and all of it is sound: the optimized program computes what the scan
     form computes, on every store and environment *)
  Theorem optimized_sound :
    well_typed init_Gstore init_Genv optimized /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized
        = interp_command store env (elaborated decls).
  Proof.
    unfold optimized, anno, elaborated, prog_s.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply row_ty_wf
      | apply incl_refl | apply decls_wf | apply elaborated_well_typed ].
  Qed.
End WithConcreteMaps.
