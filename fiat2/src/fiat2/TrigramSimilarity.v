From Stdlib Require Import List String Arith Lia.
Import ListNotations.

(* The arithmetic a threshold similarity search rests on, and the reason an
   inverted index can serve one at all.

   PostgreSQL's pg_trgm answers `name % pattern` -- "similar enough" -- with
   a trigram GIN index, and it does so even though the index CANNOT compute
   the similarity it is asked about.  Two different numbers are involved, and
   the gap between them is the whole mechanism:

     trgm_op.c    CALCSML(count, len1, len2) = count / (len1 + len2 - count)

                  the real answer: the JACCARD coefficient of the two
                  trigram sets, computed by cnt_sml as a merge join over two
                  sorted unique arrays -- i.e. by a sequential scan.

     trgm_gin.c   gin_trgm_consistent, for the % operator:
                      ((float4) ntrue / (float4) nkeys) >= nlimit

                  what the INDEX can decide: of the query's nkeys trigrams,
                  how many are present in this row.  It has no idea how many
                  trigrams the ROW has, because the posting lists it walked
                  are indexed by trigram, not by row.

   Write a = |T(query)|, b = |T(row)|, c = |T(query) INTERSECT T(row)|.  The
   real predicate is c / (a + b - c) >= t and the index's is c / a >= t.
   They are not equal -- the index's is WEAKER -- and that is exactly why
   gin_trgm_consistent sets *recheck = true unconditionally: the index
   produces candidates and cnt_sml decides them.

   gin_test_sound below is the obligation Postgres satisfies by construction
   and states as a flag.  Here it is a theorem.

   Two deliberate differences from the C, neither hidden:

   - CALCSML and nlimit are float4.  The predicates here are stated over
     naturals with the threshold as a rational tn/td and the comparison
     CROSS-MULTIPLIED, so they are exact.  That is the intended meaning of
     the test rather than a transcription of its rounding, and the two can
     disagree on a boundary case a float comparison decides by its own
     error.
   - The counts are cardinalities of SETS of trigrams, as in pg_trgm, which
     sorts and uniques what it extracts.  Nothing here assumes how the sets
     were built, so it holds of padded and unpadded extraction alike. *)

(* The index's test is implied by the real one.  The two side conditions are
   the only facts about the sets that are needed, and both say the same
   thing: an intersection is contained in each of its arguments. *)
Theorem gin_test_sound : forall a b c tn td : nat,
    c <= a -> c <= b ->
    c * td >= tn * (a + b - c) ->
    c * td >= tn * a.
Proof.
  intros a b c tn td H_ca H_cb H_jac.
  (* the union is at least as big as either side, which is where c <= b is
     spent -- and the only place it is *)
  assert (H_ge : a <= a + b - c) by lia.
  (* scaling by the numerator is the one nonlinear step, so it is done by
     hand rather than left to lia *)
  assert (H_mul : tn * a <= tn * (a + b - c))
    by (apply Nat.mul_le_mono_l; exact H_ge).
  lia.
Qed.

(* The same fact as the index uses it: a row the index rejects could not
   have passed. *)
Corollary gin_filter_complete : forall a b c tn td : nat,
    c <= a -> c <= b ->
    c * td < tn * a ->
    c * td < tn * (a + b - c).
Proof.
  intros a b c tn td H_ca H_cb H_rej.
  assert (H_ge : a <= a + b - c) by lia.
  assert (H_mul : tn * a <= tn * (a + b - c))
    by (apply Nat.mul_le_mono_l; exact H_ge).
  lia.
Qed.

(* And the connection to the substring rule, which is not a coincidence:
   requiring EVERY one of the query's trigrams -- what gin_trgm_consistent
   does for LIKE, and what the all-trigram intersection computes -- is the
   threshold-one instance of the same test.

   So the two lookups are one family.  The substring rule filters at t = 1,
   where the index's test is exact and the recheck is only needed because a
   trigram match is not an occurrence; the similarity rule filters at t < 1,
   where the index's test is additionally an over-approximation of the
   answer. *)
Corollary like_is_threshold_one : forall a c : nat,
    c <= a -> (c * 1 >= 1 * a <-> c = a).
Proof. intros a c H_ca; split; intros; lia. Qed.

(* The over-approximation is STRICT, so the recheck cannot be dropped.  One
   query trigram, all of it matched, against a row with ten: the index's test
   passes at a threshold of one half and the real predicate fails, because
   the row is mostly other trigrams.  This is the counterexample to the
   converse of gin_test_sound, and the reason *recheck = true is
   unconditional rather than a heuristic. *)
Example recheck_is_necessary :
  let a := 1 in let b := 10 in let c := 1 in let tn := 1 in let td := 2 in
  c * td >= tn * a /\ ~ (c * td >= tn * (a + b - c)).
Proof. cbn; lia. Qed.

(* The degenerate case, which is why every rule in this development carries
   a guard rather than relying on the test alone: with a = 0 the index's
   ratio is ntrue/nkeys = 0/0 and decides nothing, so there is no lemma to
   state here.  pg_trgm answers that query with GIN_SEARCH_MODE_ALL -- scan
   everything and recheck -- and our rules decline to rewrite, which is the
   same decision reached syntactically. *)
