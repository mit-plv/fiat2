Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem
  fiat2.TypeSound fiat2.Utils fiat2.StringFacts fiat2.TrigramSimilarity.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString
  coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Lia.

Import ListNotations.
Local Open Scope string_scope.

(* Threshold trigram similarity, as an ordinary program in this language.

   PostgreSQL answers `name % pattern` -- "similar enough" -- with the
   Jaccard coefficient of the two strings' trigram sets, which trgm_op.c
   computes as CALCSML(count, len1, len2) = count / (len1 + len2 - count).
   The point of this file is that writing that predicate needs NO new type
   and NO new operator: the trigram set is a fold over a range inserting
   substrings, the cardinalities are OLength of ESort (card_via_sort below,
   kept compiled as the witness for exactly this claim), the intersection is
   OSetIntersect, and the threshold is a cross-multiplied comparison of two
   products.  Everything here already existed for other reasons.

   OSetSize was added LATER and `card` now uses it.  That does not weaken the
   claim: it buys the cost of |A|, one traversal instead of a sort, and
   card_agrees_with_the_sort_form pins that the answers are identical.

   So "support similarity search" is not a question about the LANGUAGE.  It
   is a question about which rule can serve the predicate from an index,
   which is what TrigramSimilarity.gin_test_sound is about.

   Three deliberate differences from pg_trgm, none of them hidden:

   - Thresholds are exact rationals, cross-multiplied.  CALCSML and nlimit
     are float4, so the two can disagree on a boundary a float comparison
     decides by its own rounding error.
   - pg_trgm pads each WORD (LPADDING 2, RPADDING 1, space, word characters
     decided by ISWORDCHR); `padded` below pads the whole string.  On a
     single-word name the two agree; on a name with a space they extract
     different trigrams.  Splitting on non-alphanumerics would need one new
     operator and buys nothing structural, so it is not done.
   - pg_trgm lower-cases in a default build; nothing here does.  The
     examples below keep case consistent so that the difference does not
     silently carry the result. *)

(* ------------------------------------------------------------------
   The predicate, built out of what the language already has.
   ------------------------------------------------------------------ *)

(* The trigram SET of a string: fold over the positions at which it has a
   trigram, inserting each one.  A set, not a bag, because pg_trgm sorts and
   uniques what it extracts -- "aaaa" has one trigram, not two. *)
Definition tri_set (s : expr) : expr :=
  EFold
    (EBinop ORange (EAtom (AInt 0))
       (EBinop OMinus (EUnop OLengthString s) (EAtom (AInt 2))))
    (EAtom (AEmptySet (Some TString)))
    "i" "acc"
    (EBinop OSetInsert (EVar "acc")
       (ETernop OSubstring s (EVar "i") (EAtom (AInt 3)))).

(* Cardinality, two ways, and the pair is the point.

   card_via_sort is how this file was first written, when a set had no size
   operator of its own: OLength of ESort LikeSet.  It is kept because it is
   the WITNESS for the claim above -- the predicate needed no new operator to
   be written -- and `card_agrees_with_the_sort_form` below pins that the two
   give the same answer.

   But it is not the cost one wants: ESort reads a set's canonical
   representation, so asking |A| this way pays n log n to build an ordering
   the answer never looks at.  OSetSize is one traversal on any representation
   a set could have.  So the operator buys COST, not expressiveness, and the
   two definitions standing side by side are what says so. *)
Definition card_via_sort (a : expr) : expr := EUnop OLength (ESort LikeSet a).
Definition card (a : expr) : expr := EUnop OSetSize a.

(* pg_trgm's padding, LPADDING 2 and RPADDING 1, with a space. *)
Definition padded (s : expr) : expr :=
  EBinop OConcatString (EAtom (AString "  "))
    (EBinop OConcatString s (EAtom (AString " "))).

(* similarity(s, p) >= tn/td, cross-multiplied so that it is exact:

       c * td >= tn * (a + b - c)

   with a = |T(p)|, b = |T(s)|, c = |T(p) INTERSECT T(s)|.  The lets are
   what keep each trigram set from being extracted twice. *)
Definition sim_ge (tn td : Z) (s p : expr) : expr :=
  ELet (tri_set p) "qs"
    (ELet (tri_set s) "rs"
       (ELet (card (EBinop OSetIntersect (EVar "qs") (EVar "rs"))) "c"
          (EUnop ONot
             (EBinop OLess
                (EBinop OTimes (EVar "c") (EAtom (AInt td)))
                (EBinop OTimes (EAtom (AInt tn))
                   (EBinop OMinus
                      (EBinop OPlus (card (EVar "qs")) (card (EVar "rs")))
                      (EVar "c"))))))).

(* And the query a source program would write: every row similar enough to
   the pattern.  This is the shape a rule would have to match -- the same
   shape as the substring query, with a different predicate. *)
Definition sim_query (tn td : Z) : expr :=
  EFlatmap LikeSet (EUnop OSetOfList (ELoc "users")) "r"
    (EIf (sim_ge tn td (padded (EAccess (EVar "r") "name")) (padded (EVar "p")))
       (EBinop OSetInsert (EAtom (AEmptySet None)) (EVar "r"))
       (EAtom (AEmptySet None))).

(* ------------------------------------------------------------------
   THE SAME PREDICATE PER WORD, which is what multi-word text needs.

   Whole-set Jaccard cannot see a word inside a sentence, and the reason is
   arithmetic rather than incidental: a four-word row has about forty
   trigrams against a ten-trigram query, so even an EXACT word match scores
   10/(10+40-10) = 0.25 and fails a threshold of 0.3.  Measured on 196,898
   dictionary words, the whole-set predicate accepts 0.00 rows per query at
   four words a row, where the per-word predicate accepts 1.2 to 4.8.

   That is why pg_trgm has a word variant at all, and why wagtail's
   modelsearch calls one.  This is `strict_word_similarity`: "greatest
   similarity between first string and any continuous extent of WORDS of the
   second string".  At a single-word query the greatest is always attained at
   one word, since extending the extent only adds trigrams to the divisor.
   ------------------------------------------------------------------ *)

(* One word, with the query's trigram set and its size already bound.  They
   are bound OUTSIDE the fold below on purpose: recomputing them per word
   would charge the scan for work no implementation does, and would flatter
   every ratio measured against it. *)
Definition sim_ge_from (tn td : Z) (qs a w : expr) : expr :=
  ELet (tri_set w) "rs"
    (ELet (card (EBinop OSetIntersect qs (EVar "rs"))) "c"
       (EUnop ONot
          (EBinop OLess
             (EBinop OTimes (EVar "c") (EAtom (AInt td)))
             (EBinop OTimes (EAtom (AInt tn))
                (EBinop OMinus
                   (EBinop OPlus a (card (EVar "rs")))
                   (EVar "c")))))).

(* SOME word of the text is similar enough to the pattern.  Each word is
   padded on its own, as pg_trgm's generate_trgm does, so no trigram
   straddles a separator -- which is also what keeps the index able to
   answer this, since the index keys on exactly these per-word trigrams. *)
Definition sim_any (tn td : Z) (seps : string) (text p : expr) : expr :=
  ELet (tri_set (padded p)) "qs"
    (ELet (card (EVar "qs")) "a"
       (EFold (EBinop OWords (EAtom (AString seps)) text)
          (EAtom (ABool false)) "wrd" "sacc"
          (EBinop OOr (EVar "sacc")
             (sim_ge_from tn td (EVar "qs") (EVar "a")
                (padded (EVar "wrd")))))).

(* And the query a source writes over multi-word text. *)
Definition sim_any_query (tn td : Z) (seps : string) : expr :=
  EFlatmap LikeSet (EUnop OSetOfList (ELoc "users")) "r"
    (EIf (sim_any tn td seps (EAccess (EVar "r") "name") (EVar "p"))
       (EBinop OSetInsert (EAtom (AEmptySet None)) (EVar "r"))
       (EAtom (AEmptySet None))).

Definition row_ty := TRecord (record_sort [("id", TInt); ("name", TString)]).

Section WithConcreteMaps.
  Notation value := (value).

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.
  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Definition pred_Genv : ctenv :=
    map.put (map.put map.empty "s" TString) "p" TString.

  Definition query_Gstore : ctenv :=
    map.put map.empty "users" (TList row_ty).

  Definition query_Genv : ctenv := map.put map.empty "p" TString.

  (* ----------------------------------------------------------------
     It is a well-typed boolean, and the query is a well-typed set of
     rows.  No new type, no new operator, no extension of any kind: this
     is the claim, and the type checker is the evidence for it.
     ---------------------------------------------------------------- *)
  Lemma sim_ge_is_a_boolean :
    match synthesize_expr map.empty pred_Genv
            (sim_ge 3 10 (EVar "s") (EVar "p")) with
    | Success (t, _) => t = TBool
    | _ => False
    end.
  Proof. vm_compute; reflexivity. Qed.

  Lemma sim_query_is_a_set_of_rows :
    match synthesize_expr query_Gstore query_Genv (sim_query 3 10) with
    | Success (t, _) => t = TSet row_ty
    | _ => False
    end.
  Proof. vm_compute; reflexivity. Qed.

  (* ----------------------------------------------------------------
     What it computes, on strings chosen because the answer is the whole
     argument for padding.
     ---------------------------------------------------------------- *)
  Definition two (sv pv : string) : clocals :=
    map.put (map.put map.empty "s" (VString sv)) "p" (VString pv).

  Notation ps := (padded (EVar "s")).
  Notation pq := (padded (EVar "p")).

  (* UNPADDED, Smith against Smyth: the trigram sets are DISJOINT.  "Smith"
     gives {Smi, mit, ith} and "Smyth" gives {Smy, myt, yth}, so the
     similarity is 0 and no positive threshold can match them.  Unpadded
     whole-string extraction cannot do fuzzy name matching at all -- which
     is the measured reason pg_trgm pads, and the reason our existing index
     serves SUBSTRING search and not this. *)
  Lemma unpadded_smith_smyth_share_nothing :
    interp_expr map.empty (two "Smith" "Smyth")
      (card (EBinop OSetIntersect (tri_set (EVar "s")) (tri_set (EVar "p"))))
    = VInt 0.
  Proof. vm_compute; reflexivity. Qed.

  Lemma unpadded_smith_is_not_smyth :
    interp_expr map.empty (two "Smith" "Smyth")
      (sim_ge 3 10 (EVar "s") (EVar "p")) = VBool false.
  Proof. vm_compute; reflexivity. Qed.

  (* PADDED, the same pair: six trigrams each, three shared -- the two
     boundary trigrams and the right one -- so the similarity is
     3 / (6 + 6 - 3) = 1/3, which clears pg_trgm's default threshold of
     0.3.  Padding is exactly what makes Smith match Smyth. *)
  Lemma padded_smith_has_six : forall sv,
      interp_expr map.empty (two sv "Smith") (card (tri_set pq)) = VInt 6.
  Proof. intros; vm_compute; reflexivity. Qed.

  Lemma padded_smith_smyth_share_three :
    interp_expr map.empty (two "Smith" "Smyth")
      (card (EBinop OSetIntersect (tri_set ps) (tri_set pq))) = VInt 3.
  Proof. vm_compute; reflexivity. Qed.

  Lemma padded_smith_is_smyth :
    interp_expr map.empty (two "Smith" "Smyth") (sim_ge 3 10 ps pq)
    = VBool true.
  Proof. vm_compute; reflexivity. Qed.

  (* and the predicate still says no to a name that shares nothing, and yes
     to the name itself, so the threshold is not simply always met *)
  Lemma padded_smith_is_smith :
    interp_expr map.empty (two "Smith" "Smith") (sim_ge 3 10 ps pq)
    = VBool true.
  Proof. vm_compute; reflexivity. Qed.

  Lemma padded_jones_is_not_smith :
    interp_expr map.empty (two "Jones" "Smith") (sim_ge 3 10 ps pq)
    = VBool false.
  Proof. vm_compute; reflexivity. Qed.

  (* ----------------------------------------------------------------
     Why the recheck cannot be dropped, with strings instead of numbers.

     TrigramSimilarity.recheck_is_necessary says the index's test is a
     STRICT over-approximation.  Here is a row that witnesses it.  Querying
     for "Smith", the row "Smithsonian Institute" shares five of the
     query's six trigrams, so the index's test -- ntrue/nkeys >= nlimit,
     which is 5/6 here -- passes easily.  But the row has twenty-two
     trigrams of its own, so the real similarity is 5/(6+22-5) = 5/23,
     about 0.217, and the threshold rejects it.

     The index cannot see this, because its posting lists are indexed by
     trigram and know nothing about how many trigrams the ROW has.  That is
     why gin_trgm_consistent sets *recheck = true unconditionally.
     ---------------------------------------------------------------- *)
  Definition smithsonian := two "Smithsonian Institute" "Smith".

  Lemma smithsonian_counts :
    interp_expr map.empty smithsonian (card (tri_set pq)) = VInt 6
    /\ interp_expr map.empty smithsonian (card (tri_set ps)) = VInt 22
    /\ interp_expr map.empty smithsonian
         (card (EBinop OSetIntersect (tri_set ps) (tri_set pq))) = VInt 5.
  Proof. repeat split; vm_compute; reflexivity. Qed.

  (* OSetSize answers what the sort answered.  Pinned on all three of the
     counts above, including the intersection, so the operator is checked
     against the form it replaces rather than only against a literal. *)
  Lemma card_agrees_with_the_sort_form :
    interp_expr map.empty smithsonian (card (tri_set pq))
    = interp_expr map.empty smithsonian (card_via_sort (tri_set pq))
    /\ interp_expr map.empty smithsonian (card (tri_set ps))
       = interp_expr map.empty smithsonian (card_via_sort (tri_set ps))
    /\ interp_expr map.empty smithsonian
         (card (EBinop OSetIntersect (tri_set ps) (tri_set pq)))
       = interp_expr map.empty smithsonian
           (card_via_sort (EBinop OSetIntersect (tri_set ps) (tri_set pq))).
  Proof. repeat apply conj; vm_compute; reflexivity. Qed.

  Lemma smithsonian_passes_the_index_test : 5 * 10 >= 3 * 6.
  Proof. lia. Qed.

  Lemma smithsonian_fails_the_threshold :
    interp_expr map.empty smithsonian (sim_ge 3 10 ps pq) = VBool false.
  Proof. vm_compute; reflexivity. Qed.

  (* ----------------------------------------------------------------
     WHY THE WHOLE-STRING FORM IS NOT ENOUGH, pinned rather than argued.

     On ONE word the two predicates agree, which is why every pin above is
     still valid -- and is also why they hid this: the file's only example
     had one word.
     ---------------------------------------------------------------- *)
  Lemma one_word_the_two_predicates_agree :
    interp_expr map.empty (two "Smith" "Smyth") (sim_ge 3 10 ps pq)
    = interp_expr map.empty (two "Smith" "Smyth")
        (sim_any 3 10 " " (EVar "s") (EVar "p")).
  Proof. vm_compute; reflexivity. Qed.

  (* On four words they disagree, and the whole-string one is the one that
     is wrong: "Smyth" against a row holding "Smith" is exactly the match a
     fuzzy search exists to find. *)
  Lemma four_words_whole_string_finds_nothing :
    interp_expr map.empty (two "Smith Jones Associates Limited" "Smyth")
      (sim_ge 3 10 ps pq) = VBool false.
  Proof. vm_compute; reflexivity. Qed.

  Lemma four_words_per_word_finds_it :
    interp_expr map.empty (two "Smith Jones Associates Limited" "Smyth")
      (sim_any 3 10 " " (EVar "s") (EVar "p")) = VBool true.
  Proof. vm_compute; reflexivity. Qed.

  (* And the mechanism, which is the part an index depends on: padding the
     whole string manufactures a trigram that straddles a separator, and no
     bucket of the index holds it.  Padding each word, as generate_trgm
     does, never produces it. *)
  Lemma whole_string_padding_invents_a_cross_word_trigram :
    interp_expr map.empty (two "Smith Jones" "Smyth")
      (EBinop OSetMem (tri_set (padded (EVar "s"))) (EAtom (AString "h J")))
    = VBool true.
  Proof. vm_compute; reflexivity. Qed.

  Lemma no_padded_word_holds_it :
    interp_expr map.empty (two "Smith Jones" "Smyth")
      (EBinop OOr
         (EBinop OSetMem (tri_set (padded (EAtom (AString "Smith"))))
            (EAtom (AString "h J")))
         (EBinop OSetMem (tri_set (padded (EAtom (AString "Jones"))))
            (EAtom (AString "h J"))))
    = VBool false.
  Proof. vm_compute; reflexivity. Qed.

End WithConcreteMaps.
