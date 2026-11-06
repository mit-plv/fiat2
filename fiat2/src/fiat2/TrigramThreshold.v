Require Import fiat2.Value fiat2.Interpret fiat2.Constraint fiat2.StringFacts
  fiat2.TrigramSimilarity fiat2.TrigramIndexImpl fiat2.CollectionTransf.
From Stdlib Require Import List String Arith Lia.
Import ListNotations.

(* The candidate set a THRESHOLD similarity query gets from a trigram index,
   and the proof that it keeps every row the query wants.

   Stage 1 answered a SUBSTRING query by intersecting the buckets of all of
   the pattern's trigrams: a row that contains the pattern is in every one
   of them, so the intersection loses nothing.  A threshold query cannot be
   answered that way.  A row similar enough to the pattern need not share
   EVERY trigram with it -- that is the whole point of a threshold -- so an
   intersection would throw away exactly the rows the query is looking for.

   What the index can decide is how MANY of the pattern's trigrams a row
   shares.  gin_trgm_consistent's test for the % operator is

       ntrue / nkeys >= nlimit,

   the fraction of the QUERY's trigrams present in the row, and
   TrigramSimilarity.gin_test_sound is the fact that makes it usable: it is
   implied by the real Jaccard predicate, so it admits every qualifying row
   (and some others, which the recheck removes).  So the candidate
   construction here is a COUNT over the buckets, not an intersection --
   k-of-n rather than n-of-n -- and Stage 1 is its n-of-n instance, by
   TrigramSimilarity.like_is_threshold_one.

   Two things are worth being clear about before any of it.

   First, nothing here needs the index to be PRECISE.  The only fact used
   about the index is tri_lookup_complete_at_word: a trigram of one of the
   row's padded words puts the row's key in that trigram's bucket.  A
   bucket may hold keys for other reasons -- it does, since a key is filed
   under every trigram of every word of its text -- and that only makes the
   count bigger, which only makes the candidate set bigger.  Soundness comes from the recheck, as it
   does for every other lookup rule here.

   Second, this is a count over a LIST of the query's trigrams, and which
   list matters.  The Jaccard predicate counts a trigram once however many
   times it occurs, so the list has to be duplicate-free for the count to
   agree with the predicate's.  That obligation is deliberately NOT
   discharged here: these theorems take the list as given and say what
   follows, and the expression level supplies a deduplicated one.  Mixing
   the two would hide the one place the agreement can fail. *)

Section WithAttrs.
  Context (attr key : string).
  (* the separators the index tokenizes on *)
  Context (seps : string).

  (* pg_trgm's generate_trgm: a text's trigram set is the union over its
     WORDS, each padded.  Both sides of the similarity predicate are over
     this set in Postgres -- similarity() tokenizes its arguments by the
     same find_word loop the index does -- so it is the right notion here
     too, and it is exactly what the index keys on. *)
  Definition tri_set (s : string) : list string :=
    flat_map (fun w => trigrams (pad w)) (words seps s).

  (* The keys filed under one trigram, read out of an index VALUE. *)
  Definition bucket (idx : value) (g : string) : list value :=
    match idx with
    | VDict d => bucket_of (VString g) d
    | _ => nil
    end.

  (* How many of the query's trigrams have this key in their bucket: the
     ntrue of gin_trgm_consistent, counted by asking the index. *)
  Definition tri_count (idx : value) (gs : list string) (k : value) : nat :=
    List.length (List.filter (fun g => set_mem k (bucket idx g)) gs).

  (* And how many of them the row's text really has: the c of the Jaccard
     predicate, when gs is duplicate-free. *)
  Definition inter_count (gs ts : list string) : nat :=
    List.length (List.filter (fun g => List.existsb (String.eqb g) ts) gs).

  (* A pointwise implication between two tests is a <= between the lengths
     they filter to.  The standard library relates filter to In and to
     incl, but not two filters to each other. *)
  Lemma filter_length_mono :
    forall (A : Type) (f g : A -> bool) (l : list A),
      (forall x, In x l -> f x = true -> g x = true) ->
      List.length (List.filter f l) <= List.length (List.filter g l).
  Proof.
    intros A f g l; induction l as [ | x l IH ]; cbn [List.filter]; intros H_imp.
    1: cbn; lia.
    assert (H_tail : forall y, In y l -> f y = true -> g y = true)
      by (intros y H_in; apply H_imp; right; exact H_in).
    destruct (f x) eqn:E_f.
    1:{ rewrite (H_imp x (or_introl eq_refl) E_f).
        cbn [List.length]. apply le_n_S. apply IH; exact H_tail. }
    1:{ destruct (g x); cbn [List.length];
          [ apply Nat.le_le_succ_r | ]; apply IH; exact H_tail. }
  Qed.

  (* key_at says the bucket exists and holds the key; bucket reads whatever
     is there.  So the one implies membership in the other. *)
  Lemma key_at_In_bucket : forall idx g k,
      key_at (VString g) k idx -> In k (bucket idx g).
  Proof.
    unfold key_at, bucket, bucket_of; intros idx g k H.
    destruct idx as [ | | | | | | d | | | ]; try contradiction.
    destruct (dict_lookup (VString g) d) as [ bk | ]; try contradiction.
    destruct bk; try contradiction. exact H.
  Qed.

  (* THE BRIDGE: whatever the row really shares with the query, the index
     reports at least that much.  No hypothesis about the threshold, and
     none about the index being precise. *)
  (* A trigram of the row's own set is a trigram of one of its padded
     words, which is a key the index files the row under. *)
  Lemma In_tri_set__key_at : forall (l : list value) r g,
      In r l ->
      In g (tri_set (row_str attr r)) ->
      key_at (VString g) (row_key key r) (tri_entries attr key seps l).
  Proof.
    unfold tri_set; intros l r g H_in H_g.
    apply in_flat_map in H_g as [ w [ H_w H_g ] ].
    eapply tri_lookup_complete_at_word; [ exact H_in | | exact H_g ].
    unfold row_wrds; exact H_w.
  Qed.

  Theorem index_sees_the_intersection : forall (l : list value) r gs,
      In r l ->
      inter_count gs (tri_set (row_str attr r))
      <= tri_count (tri_entries attr key seps l) gs (row_key key r).
  Proof.
    unfold inter_count, tri_count; intros l r gs H_in.
    apply filter_length_mono.
    intros g _ H_has.
    (* g really is one of the row's trigrams *)
    apply existsb_exists in H_has as [ g' [ H_in' E_eq ] ].
    apply String.eqb_eq in E_eq; subst g'.
    apply set_mem_true_iff, key_at_In_bucket.
    apply In_tri_set__key_at; [ exact H_in | exact H_in' ].
  Qed.

  (* THE ARITHMETIC: a row the real predicate accepts passes the index's
     count test.  gin_test_sound carries the Jaccard predicate to the
     index's own, and the bridge above only raises the count. *)
  Theorem candidate_test_passes : forall idx (gs : list string) k a b c tn td,
      a = List.length gs ->
      c <= a -> c <= b ->
      c * td >= tn * (a + b - c) ->
      c <= tri_count idx gs k ->
      tri_count idx gs k * td >= tn * a.
  Proof.
    intros idx gs k a b c tn td _ H_ca H_cb H_jac H_cnt.
    pose proof (gin_test_sound a b c tn td H_ca H_cb H_jac) as H_idx.
    assert (H_mul : c * td <= tri_count idx gs k * td)
      by (apply Nat.mul_le_mono_r; exact H_cnt).
    lia.
  Qed.

  (* ------------------------------------------------------------------
     The candidate POOL, and the set the rule actually emits.

     The pool is every key filed under any of the query's trigrams -- a
     UNION, where Stage 1 took an intersection.  Written as the expression
     writes it: a fold over the query's trigrams whose step is OSetUnion,
     whose own semantics is fold_right set_insert over the left operand.
     ------------------------------------------------------------------ *)
  Definition tri_cands (idx : value) (gs : list string) : list value :=
    fold_right (fun g acc => fold_right set_insert acc (bucket idx g)) nil gs.

  Lemma In_fold_set_insert : forall (l acc : list value) k,
      In k l -> In k (fold_right set_insert acc l).
  Proof.
    induction l as [ | x l IH ]; cbn [fold_right]; intros acc k H_in.
    1: contradiction.
    destruct H_in as [ E | H_in ].
    1:{ subst x. apply set_insert_incl_r. left; reflexivity. }
    1:{ apply set_insert_incl_r. right. apply IH; exact H_in. }
  Qed.

  Lemma In_fold_set_insert_acc : forall (l acc : list value) k,
      In k acc -> In k (fold_right set_insert acc l).
  Proof.
    induction l as [ | x l IH ]; cbn [fold_right]; intros acc k H_in.
    1: exact H_in.
    apply set_insert_incl_r. right. apply IH; exact H_in.
  Qed.

  Lemma In_tri_cands : forall idx gs g k,
      In g gs -> In k (bucket idx g) -> In k (tri_cands idx gs).
  Proof.
    unfold tri_cands; intros idx gs g k H_g H_k.
    induction gs as [ | g0 gs IH ]; cbn [fold_right]; [ contradiction | ].
    destruct H_g as [ E | H_g ].
    1:{ subst g0. apply In_fold_set_insert; exact H_k. }
    1:{ apply In_fold_set_insert_acc. apply IH; exact H_g. }
  Qed.

  (* The test the index can make, cross-multiplied so that it is exact:
     of the query's |gs| trigrams, the fraction present is at least tn/td. *)
  Definition passes (idx : value) (gs : list string) (tn td : nat) (k : value) : bool :=
    Nat.leb (tn * List.length gs) (tri_count idx gs k * td).

  Definition tri_keep (idx : value) (gs : list string) (tn td : nat) : list value :=
    List.filter (passes idx gs tn td) (tri_cands idx gs).

  Lemma tri_count_le : forall idx gs k, tri_count idx gs k <= List.length gs.
  Proof.
    unfold tri_count; intros idx gs k.
    induction gs as [ | g gs IH ]; cbn [List.filter List.length]; [ lia | ].
    destruct (set_mem k (bucket idx g)); cbn [List.length]; lia.
  Qed.

  (* Stage 1 is the n-of-n instance of this rule, not a different one: at
     threshold one the count test says every one of the query's trigrams is
     present, which is what intersecting their buckets decides.
     TrigramSimilarity.like_is_threshold_one is the same fact as
     arithmetic; this is it as the emitted test. *)
  Corollary passes_at_threshold_one : forall idx gs k,
      passes idx gs 1 1 k = true <-> tri_count idx gs k = List.length gs.
  Proof.
    unfold passes; intros idx gs k.
    pose proof (tri_count_le idx gs k) as H_le.
    rewrite Nat.leb_le. lia.
  Qed.

  (* A row the real predicate accepts shares at least one trigram with the
     query, so it is in the pool at all.  This is where the rule's side
     conditions come from: with a threshold of zero every row qualifies,
     but the pool holds only rows that share something, so the rewrite
     would LOSE rows.  0 < tn is not a technicality. *)
  Lemma qualifying_shares_a_trigram : forall gs ts a b c tn td,
      a = List.length gs ->
      0 < tn -> 0 < td -> 0 < a + b - c ->
      c * td >= tn * (a + b - c) ->
      c <= inter_count gs ts ->
      exists g, In g gs /\ In g ts.
  Proof.
    intros gs ts a b c tn td _ H_tn H_td H_ab H_jac H_c.
    (* the threshold forces at least one shared trigram *)
    assert (H_ge1 : 1 <= tn * (a + b - c)).
    1:{ apply Nat.le_trans with (m := 1 * (a + b - c));
          [ lia | apply Nat.mul_le_mono_r; lia ]. }
    assert (H_cd : 1 <= c * td) by lia.
    assert (H_c1 : 1 <= c) by (destruct c; [ cbn in H_cd; lia | lia ]).
    assert (H_ic : 1 <= inter_count gs ts) by lia.
    (* so the filter is not empty, and its head is such a trigram *)
    unfold inter_count in H_ic.
    destruct (List.filter (fun g => List.existsb (String.eqb g) ts) gs)
      as [ | g rest ] eqn:E_f.
    1:{ cbn [List.length] in H_ic; lia. }
    assert (H_in : In g (List.filter
                           (fun g => List.existsb (String.eqb g) ts) gs))
      by (rewrite E_f; left; reflexivity).
    apply filter_In in H_in as [ H_g H_has ].
    apply existsb_exists in H_has as [ g' [ H_in' E_eq ] ].
    apply String.eqb_eq in E_eq; subst g'.
    exists g; split; assumption.
  Qed.

  (* THE THEOREM.  Every row the threshold predicate accepts is kept by the
     count test over the index -- so the rewrite from a scan to this
     candidate set loses nothing, and the recheck that follows restores
     precision.  Nothing here assumes the index is precise, and nothing
     assumes a primary key: the only index fact used is
     tri_lookup_complete_at_word. *)
  Theorem threshold_candidates_complete :
    forall (l : list value) r gs a b c tn td,
      In r l ->
      a = List.length gs ->
      c <= a -> c <= b ->
      0 < tn -> 0 < td -> 0 < a + b - c ->
      c * td >= tn * (a + b - c) ->
      c <= inter_count gs (tri_set (row_str attr r)) ->
      In (row_key key r) (tri_keep (tri_entries attr key seps l) gs tn td).
  Proof.
    intros l r gs a b c tn td H_in E_a H_ca H_cb H_tn H_td H_ab H_jac H_c.
    unfold tri_keep. apply filter_In; split.
    (* in the pool, because it shares a trigram *)
    1:{ destruct (qualifying_shares_a_trigram gs (tri_set (row_str attr r))
                    a b c tn td E_a H_tn H_td H_ab H_jac H_c)
          as [ g [ H_g H_tri ] ].
        eapply In_tri_cands; [ exact H_g | ].
        apply key_at_In_bucket.
        apply In_tri_set__key_at; [ exact H_in | exact H_tri ]. }
    (* and passes the count test *)
    1:{ unfold passes. rewrite Nat.leb_le, <- E_a.
        apply (candidate_test_passes (tri_entries attr key seps l) gs
                 (row_key key r) a b c tn td E_a H_ca H_cb H_jac).
        eapply Nat.le_trans; [ exact H_c | ].
        apply index_sees_the_intersection; exact H_in. }
  Qed.

  (* ------------------------------------------------------------------
     THE SAME THEOREM AT ONE WORD, which is what multi-word text needs.

     Whole-set Jaccard cannot accept a row because of one of its words: a
     four-word row carries about forty trigrams against a ten-trigram
     query, so even an exact word match scores 10/(10+40-10) = 0.25 and
     fails a threshold of 0.3.  The predicate a source actually writes --
     pg_trgm's word variant, and wagtail's modelsearch calls one -- asks
     whether SOME word is similar enough.

     Nothing about the candidate set changes, and that is the point: the
     theorem above already takes the counts as given, and a word's trigrams
     are a SUBSET of its row's, so the count the index reports is at least
     the word's.  So the k-of-n test is complete for the per-word predicate
     for the same reason and with the same proof.
     ------------------------------------------------------------------ *)

  (* A longer trigram list can only match more of the query. *)
  Lemma inter_count_mono : forall gs ts1 ts2,
      (forall g, In g ts1 -> In g ts2) ->
      inter_count gs ts1 <= inter_count gs ts2.
  Proof.
    unfold inter_count; intros gs ts1 ts2 H_sub.
    apply filter_length_mono.
    intros g _ H_has.
    apply existsb_exists in H_has as [ g' [ H_in' E_eq ] ].
    apply String.eqb_eq in E_eq; subst g'.
    apply existsb_exists. exists g; split;
      [ apply H_sub; exact H_in' | apply String.eqb_refl ].
  Qed.

  (* A word's padded trigrams are among its row's. *)
  Lemma In_word_tri_set : forall (s w : string) g,
      In w (words seps s) -> In g (trigrams (pad w)) -> In g (tri_set s).
  Proof.
    unfold tri_set; intros s w g H_w H_g.
    apply in_flat_map. exists w; split; [ exact H_w | exact H_g ].
  Qed.

  Theorem word_threshold_candidates_complete :
    forall (l : list value) r w gs a b c tn td,
      In r l ->
      In w (words seps (row_str attr r)) ->
      a = List.length gs ->
      c <= a -> c <= b ->
      0 < tn -> 0 < td -> 0 < a + b - c ->
      c * td >= tn * (a + b - c) ->
      c <= inter_count gs (trigrams (pad w)) ->
      In (row_key key r) (tri_keep (tri_entries attr key seps l) gs tn td).
  Proof.
    intros l r w gs a b c tn td H_in H_w E_a H_ca H_cb H_tn H_td H_ab H_jac H_c.
    eapply threshold_candidates_complete;
      [ exact H_in | exact E_a | exact H_ca | exact H_cb
      | exact H_tn | exact H_td | exact H_ab | exact H_jac | ].
    eapply Nat.le_trans; [ exact H_c | ].
    apply inter_count_mono.
    intros g H_g. eapply In_word_tri_set; [ exact H_w | exact H_g ].
  Qed.
End WithAttrs.
