From Stdlib Require Import String Ascii List Arith Lia.
Import ListNotations.

(* for the string literals in pad and the examples below; Local, so that
   requiring this file does not change any other file's scopes *)
Local Open Scope string_scope.

(* The string theory a trigram index needs, and which neither fiat2 nor the
   standard library has.

   A trigram index is an inverted index: it maps each three-character
   substring of a text to the rows whose text contains it.  A lookup for a
   pattern p intersects the buckets of the trigrams of p and rechecks the
   full containment on the rows it finds.  That is correct only because of
   occurrence_all_trigrams below: if p occurs in s at all, then EVERY trigram
   of p is among s's trigrams, so no bucket of any of them can miss a row,
   and neither can their intersection.  (The converse is false -- a trigram
   match is necessary, not sufficient -- which is why the recheck stays.)

   Taking one trigram instead of all of them is the special case
   occurrence_first_trigram, which is derived from the general fact below
   rather than proved again: a rule that probes a single bucket is the k = 1
   instance of the rule that intersects k of them, not a competitor to it.

   The standard library relates String.index to String.substring
   (index_correct1), and that is the only bridge it offers; the substring
   facts below are what carry a trigram of p back to a trigram of s.  Each
   one is proved by induction with the LENGTH argument destructed before the
   offset, because substring's match scrutinises the string first and so
   reduces only once the string is in constructor form. *)

Definition trigrams (s : string) : list string :=
  List.map (fun i => substring i 3 s) (List.seq 0 (String.length s - 2)).

Lemma substring_0_substring_0 : forall s k l,
    k <= l -> substring 0 k (substring 0 l s) = substring 0 k s.
Proof.
  induction s as [ | c s IH ]; intros k l H_le.
  1: destruct k, l; reflexivity.
  destruct l as [ | l ].
  1:{ assert (E : k = 0) by lia; subst k; reflexivity. }
  destruct k as [ | k ]; [ reflexivity | ].
  cbn [substring]. f_equal. apply IH. lia.
Qed.

Lemma substring_0_substring : forall s n k l,
    k <= l -> substring 0 k (substring n l s) = substring n k s.
Proof.
  induction s as [ | c s IH ]; intros n k l H_le.
  1: destruct n, k, l; reflexivity.
  destruct n as [ | n ].
  1: apply substring_0_substring_0; exact H_le.
  cbn [substring]. apply IH; exact H_le.
Qed.

(* A nonzero offset into a window that starts at the beginning. *)
Lemma substring_substring_0 : forall s i k l,
    i + k <= l -> substring i k (substring 0 l s) = substring i k s.
Proof.
  induction s as [ | c s IH ]; intros i k l H_le.
  1:{ destruct l; destruct i, k; reflexivity. }
  destruct l as [ | l ].
  1:{ assert (E : i = 0) by lia. assert (E2 : k = 0) by lia. subst. reflexivity. }
  cbn [substring].
  destruct i as [ | i ].
  1:{ destruct k as [ | k ]; [ reflexivity | ].
      cbn [substring]. f_equal. apply substring_0_substring_0. lia. }
  cbn [substring]. apply IH. lia.
Qed.

(* The general composition, and the one fact the all-trigram lookup needs
   that the single-trigram lookup did not: reading k characters from offset i
   of the window that starts at m is reading them from offset m + i of the
   string, as long as the window is long enough to hold them.  The induction
   is on m, because that is the argument substring recurses on while the
   string is being consumed. *)
Lemma substring_substring : forall m s l i k,
    i + k <= l -> substring i k (substring m l s) = substring (m + i) k s.
Proof.
  induction m as [ | m IH ]; intros s l i k H_le.
  1: apply substring_substring_0; exact H_le.
  destruct s as [ | c s ].
  1:{ destruct i, k; reflexivity. }
  cbn [substring Nat.add]. apply IH. exact H_le.
Qed.

Lemma length_substring_le : forall s n k,
    String.length (substring n k s) <= String.length s - n.
Proof.
  induction s as [ | c s IH ]; intros n k.
  1: destruct n, k; cbn; lia.
  destruct n as [ | n ].
  1:{ destruct k as [ | k ]; cbn [substring String.length]; [ lia | ].
      specialize (IH 0 k); cbn [Nat.sub] in IH |- *; lia. }
  cbn [substring String.length]. specialize (IH n k); lia.
Qed.

(* The fact the lookup rules rest on: an occurrence of p in s puts EVERY
   trigram of p among s's trigrams.  So each bucket the rule intersects
   contains the row's key, and therefore so does the intersection. *)
Theorem occurrence_all_trigrams : forall p s m g,
    String.index 0 p s = Some m ->
    In g (trigrams p) ->
    In g (trigrams s).
Proof.
  intros p s m g E_idx H_in.
  (* p sits at offset m in s *)
  assert (E_sub : substring m (String.length p) s = p)
    by (eapply String.index_correct1; exact E_idx).
  (* g is p's trigram at some position i, which the window at m can hold *)
  unfold trigrams in H_in. apply in_map_iff in H_in as [ i [ E_g H_i ] ].
  apply in_seq in H_i.
  assert (H_fit := length_substring_le s m (String.length p)).
  rewrite E_sub in H_fit.
  (* so g is s's trigram at m + i *)
  assert (E_tri : g = substring (m + i) 3 s).
  1:{ subst g. rewrite <- E_sub at 1. apply substring_substring. lia. }
  unfold trigrams. rewrite E_tri.
  apply in_map_iff. exists (m + i); split; [ reflexivity | ].
  apply in_seq. lia.
Qed.

(* A pattern of three characters or more has a first trigram. *)
Lemma In_trigrams_first : forall p,
    3 <= String.length p -> In (substring 0 3 p) (trigrams p).
Proof.
  unfold trigrams; intros p H_len.
  apply in_map_iff. exists 0; split; [ reflexivity | ]. apply in_seq. lia.
Qed.

(* The single-trigram lookup's fact, as the k = 1 instance of the general
   one.  Kept under its own name because the rule that probes one bucket is
   still registered and still proved against it. *)
Theorem occurrence_first_trigram : forall p s m,
    3 <= String.length p ->
    String.index 0 p s = Some m ->
    In (substring 0 3 p) (trigrams s).
Proof.
  intros p s m H_len E_idx.
  eapply occurrence_all_trigrams; [ exact E_idx | ].
  apply In_trigrams_first; exact H_len.
Qed.

(* ==================================================================
   Padding.

   pg_trgm does not extract a string's trigrams directly: it pads first,
   LPADDING 2 and RPADDING 1 with a space (trgm.h), so that "Smith" yields
   six trigrams rather than three and the two ends of the string are
   themselves indexed.  That is not cosmetic.  Unpadded, "Smith" gives
   {Smi, mit, ith} and "Smyth" gives {Smy, myt, yth} -- DISJOINT, so no
   threshold can match them.  Padded they share three trigrams out of nine,
   which clears pg_trgm's default threshold of 0.3.  Padding is what makes
   a trigram index able to do fuzzy matching at all.

   Two things are worth being precise about.

   First, the key stays a STRING.  A padded trigram is still three
   characters; only the characters differ.  So nothing about the index's
   type, its typing rules, or its maintenance changes shape -- which is a
   simpler arrangement than carrying the pad widths beside a shorter string,
   and it is what trgm.h itself does.

   Second, padding only ADDS keys.  trigrams_pad is the whole soundness
   argument for keeping the existing rules: s is a substring of pad s, so
   every trigram of s is a trigram of pad s.  A rule proved against the
   unpadded index therefore stays sound against the padded one, and the
   substring lookup keeps extracting the PATTERN's trigrams unpadded, as
   Postgres does -- a substring may match in the middle of a word, where no
   padding applies.
   ================================================================== *)
Definition pad (s : string) : string := "  " ++ s ++ " ".

Lemma length_append : forall s t,
    String.length (s ++ t) = String.length s + String.length t.
Proof.
  induction s as [ | c s IH ]; intros t;
    cbn [append String.length]; [ reflexivity | ].
  rewrite IH; reflexivity.
Qed.

Lemma length_pad : forall s, String.length (pad s) = String.length s + 3.
Proof.
  intros s; unfold pad. rewrite !length_append. cbn [String.length]. lia.
Qed.

(* A window that ends before the join does not see the second string. *)
Lemma substring_app_l : forall s t n k,
    n + k <= String.length s -> substring n k (s ++ t) = substring n k s.
Proof.
  induction s as [ | c s IH ]; intros t n k H_le.
  1:{ cbn [String.length] in H_le.
      assert (E : n = 0) by lia. assert (E2 : k = 0) by lia. subst.
      destruct t; reflexivity. }
  destruct n as [ | n ].
  1:{ destruct k as [ | k ]; [ reflexivity | ].
      cbn [append substring]. f_equal. apply IH.
      cbn [String.length] in H_le. lia. }
  cbn [append substring]. apply IH. cbn [String.length] in H_le. lia.
Qed.

(* Reading past the two-space prefix. *)
Lemma substring_pad_shift : forall s i k,
    substring (2 + i) k (pad s) = substring i k (s ++ " ").
Proof. intros; unfold pad; reflexivity. Qed.

(* Padding only adds keys. *)
Theorem trigrams_pad : forall s g, In g (trigrams s) -> In g (trigrams (pad s)).
Proof.
  unfold trigrams; intros s g H_in.
  apply in_map_iff in H_in as [ i [ E_g H_i ] ]. apply in_seq in H_i.
  apply in_map_iff. exists (2 + i); split.
  1:{ rewrite substring_pad_shift, substring_app_l by lia. exact E_g. }
  1:{ apply in_seq. rewrite length_pad. lia. }
Qed.

(* and what it adds, concretely: the three trigrams at the two boundaries.
   Pinned rather than proved in general, because the general statement is
   fiddlier than it is useful -- these two lines say what the padding does
   more clearly than a quantified version of them would. *)
Example trigrams_smith : trigrams "Smith" = [ "Smi"; "mit"; "ith" ].
Proof. reflexivity. Qed.

Example trigrams_pad_smith :
  trigrams (pad "Smith") = [ "  S"; " Sm"; "Smi"; "mit"; "ith"; "th " ].
Proof. reflexivity. Qed.

(* The pair that makes the point: unpadded, these two names share nothing. *)
Example trigrams_smyth : trigrams "Smyth" = [ "Smy"; "myt"; "yth" ].
Proof. reflexivity. Qed.

(* Every trigram of s really has three characters, which is what lets the
   index's key type be a string and the lookup compare with substring 0 3. *)
Lemma length_substring_ge : forall s n k,
    n + k <= String.length s -> String.length (substring n k s) = k.
Proof.
  induction s as [ | c s IH ]; intros n k H_le.
  1:{ cbn [String.length] in H_le. assert (E : k = 0) by lia; subst k.
      destruct n; reflexivity. }
  destruct n as [ | n ].
  1:{ destruct k as [ | k ]; [ reflexivity | ].
      cbn [substring String.length] in *. rewrite IH by lia. reflexivity. }
  cbn [substring String.length] in *. apply IH. lia.
Qed.

(* and the pattern a trigram came from is not empty, which is what the
   tokenized index's completeness theorems ask for *)
Lemma In_trigrams_nonempty : forall s g, In g (trigrams s) -> s <> EmptyString.
Proof.
  intros s g H; destruct s as [ | c s ]; [ | discriminate ].
  cbn [trigrams String.length Nat.sub List.seq List.map] in H; contradiction.
Qed.

Lemma In_trigrams_length : forall s g, In g (trigrams s) -> String.length g = 3.
Proof.
  unfold trigrams; intros s g H_in.
  apply in_map_iff in H_in as [ i [ E_g H_i ] ].
  apply in_seq in H_i. subst g.
  apply length_substring_ge. lia.
Qed.

(* ==================================================================
   AN OCCURRENCE, AS A DECOMPOSITION

   String.index is the only occurrence witness the standard library offers
   and it is stated with substring.  A fact about an occurrence inside a
   LARGER text needs the factors instead, which is what these four give.
   ================================================================== *)

(* An occurrence as a DECOMPOSITION.  String.index is the only occurrence
   witness the standard library offers and it is stated with substring;
   every fact about a TRANSFORMED text needs the factors instead, because
   the transformation is a homomorphism for append and says nothing about
   substring. *)
Lemma prefix_decomp : forall p s,
    prefix p s = true -> exists b, s = p ++ b.
Proof.
  induction p as [ | c p IH ]; intros s H.
  1:{ exists s; reflexivity. }
  destruct s as [ | d s ]; [ discriminate | ].
  cbn [prefix] in H. destruct (ascii_dec c d) as [ E | _ ]; [ | discriminate ].
  subst d. apply IH in H as [ b E_b ]. exists b. cbn [append]. congruence.
Qed.

Lemma index_decomp : forall s p n m,
    String.index n p s = Some m -> exists a b, s = a ++ p ++ b.
Proof.
  induction s as [ | c s IH ]; intros p n m H.
  1:{ destruct n as [ | n ]; [ | discriminate ].
      destruct p as [ | d p ]; [ | discriminate ].
      exists "", ""; reflexivity. }
  destruct n as [ | n ]; cbn [String.index] in H.
  - destruct (prefix p (String c s)) eqn:E_pre.
    1:{ apply prefix_decomp in E_pre as [ b E_b ]. exists "", b. exact E_b. }
    destruct (String.index 0 p s) as [ i | ] eqn:E_i; [ | discriminate ].
    apply IH in E_i as [ a [ b E_ab ] ]. exists (String c a), b.
    cbn [append]. congruence.
  - destruct (String.index n p s) as [ i | ] eqn:E_i; [ | discriminate ].
    apply IH in E_i as [ a [ b E_ab ] ]. exists (String c a), b.
    cbn [append]. congruence.
Qed.

(* Skipping a prefix, the counterpart of substring_app_l. *)
Lemma substring_app_r : forall a t n k,
    substring (String.length a + n) k (a ++ t) = substring n k t.
Proof.
  induction a as [ | c a IH ]; intros t n k; [ reflexivity | ].
  cbn [String.length append substring]. apply IH.
Qed.

(* occurrence_all_trigrams restated over the factors.  Same content: a
   trigram of the middle factor is a trigram of the whole. *)
Theorem trigrams_factor : forall a p b g,
    In g (trigrams p) -> In g (trigrams (a ++ p ++ b)).
Proof.
  unfold trigrams; intros a p b g H_in.
  apply in_map_iff in H_in as [ i [ E_g H_i ] ]. apply in_seq in H_i.
  apply in_map_iff. exists (String.length a + i); split.
  - rewrite substring_app_r, substring_app_l by lia. exact E_g.
  - apply in_seq. rewrite !length_append. lia.
Qed.

(* ==================================================================
   WORDS

   pg_trgm splits a text into the maximal runs of word characters and
   trigrams each one separately, padded (trgm_op.c, find_word and
   generate_trgm_only).  The separator class is a PARAMETER here, given as
   the string of separator characters, because that is what the language
   can compute: there is no ordering on characters, so ISWORDCHR's
   "alphanumeric" -- the complement of an unbounded set -- is not
   expressible, while membership in a literal alphabet is one
   OStrContains.  pg_trgm's own class is a build-time choice
   (KEEPONLYALNUM), so this narrows a parameter rather than changing the
   design.  For the text the corpus actually holds -- human names -- the
   separator set is the single space.
   ================================================================== *)

Definition is_sep (seps : string) (c : ascii) : bool :=
  match String.index 0 (String c EmptyString) seps with
  | Some _ => true
  | None => false
  end.

(* The accumulator carries the word being built.  Written this way rather
   than as "longest non-separator prefix, then recurse on the rest" because
   the rest is not a structural subterm, which would cost a fuel argument
   or a well-founded recursion for no gain in clarity. *)
Fixpoint words_acc (seps cur s : string) : list string :=
  match s with
  | EmptyString => if String.eqb cur EmptyString then [] else [cur]
  | String c s' =>
      if is_sep seps c
      then (if String.eqb cur EmptyString then [] else [cur])
             ++ words_acc seps EmptyString s'
      else words_acc seps (cur ++ String c EmptyString) s'
  end.

Definition words (seps s : string) : list string := words_acc seps EmptyString s.

Example words_two : words " " "Fred Smith" = [ "Fred"; "Smith" ].
Proof. reflexivity. Qed.

Example words_runs_collapse : words " -" "Smith--Jones" = [ "Smith"; "Jones" ].
Proof. reflexivity. Qed.

Example words_edges : words " " "  lead trail  " = [ "lead"; "trail" ].
Proof. reflexivity. Qed.

Example words_none : words " " "user0042" = [ "user0042" ].
Proof. reflexivity. Qed.

Example words_empty : words " " "" = [].
Proof. reflexivity. Qed.

(* ==================================================================
   WORDS AND OCCURRENCES

   The fact the whole tokenized lookup rests on: an occurrence that
   contains no separator lies inside a single WORD of the text.  A
   word-split index can therefore answer a substring query -- the pattern
   never straddles a word boundary, so one word contains it, and that
   word's padded trigrams are in the index.
   ================================================================== *)
Lemma append_nil_r : forall s, (s ++ "")%string = s.
Proof. induction s as [ | c s IH ]; cbn [append]; congruence. Qed.

Lemma append_assoc : forall s t u, ((s ++ t) ++ u)%string = (s ++ (t ++ u))%string.
Proof. induction s as [ | c s IH ]; intros; cbn [append]; congruence. Qed.

(* a string with no separator in it: one whole word, or empty *)
Fixpoint sep_free (seps s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => negb (is_sep seps c) && sep_free seps s'
  end.

(* W1: a separator-free accumulator may be pushed back into the input *)
Lemma words_acc_absorb : forall seps cur pre s,
    sep_free seps cur = true ->
    words_acc seps (pre ++ cur) s = words_acc seps pre (cur ++ s).
Proof.
  induction cur as [ | c cur IH ]; intros pre s H_free.
  1:{ rewrite append_nil_r. reflexivity. }
  cbn [sep_free] in H_free. rewrite Bool.andb_true_iff in H_free.
  destruct H_free as [ H_c H_cur ]. rewrite Bool.negb_true_iff in H_c.
  cbn [append words_acc]. rewrite H_c.
  rewrite <- (IH (pre ++ String c EmptyString) s H_cur).
  rewrite append_assoc. reflexivity.
Qed.

(* W2: with a non-empty accumulator the first word emitted extends it *)
Lemma words_acc_head : forall seps s cur,
    cur <> EmptyString ->
    exists t rest, words_acc seps cur s = (cur ++ t) :: rest.
Proof.
  intros seps s; induction s as [ | c s IH ]; intros cur H_ne.
  1:{ cbn [words_acc]. destruct (String.eqb cur EmptyString) eqn:E.
      1: apply String.eqb_eq in E; contradiction.
      exists EmptyString, nil. rewrite append_nil_r. reflexivity. }
  cbn [words_acc]. destruct (is_sep seps c) eqn:E_sep.
  1:{ destruct (String.eqb cur EmptyString) eqn:E.
      1: apply String.eqb_eq in E; contradiction.
      exists EmptyString, (words_acc seps EmptyString s).
      rewrite append_nil_r. reflexivity. }
  destruct (IH (cur ++ String c EmptyString)) as [ t [ rest E ] ].
  1:{ destruct cur; [ contradiction | discriminate ]. }
  exists (String c EmptyString ++ t), rest. rewrite E, append_assoc. reflexivity.
Qed.

Lemma sep_free_app : forall seps s t,
    sep_free seps s = true -> sep_free seps t = true ->
    sep_free seps (s ++ t) = true.
Proof.
  induction s as [ | c s IH ]; intros t H_s H_t; cbn [sep_free append] in *;
    [ exact H_t | ].
  rewrite Bool.andb_true_iff in *. intuition auto.
Qed.

(* Every word the splitter produces is separator-free -- which is what
   makes a RUNTIME test for "this pattern is one word" possible: the rule
   cannot evaluate sep_free, but it can compare the pattern's word list
   with the one-element list holding the pattern, and that comparison is
   an ordinary expression. *)
Lemma Forall_sep_free_words_acc : forall seps s cur,
    sep_free seps cur = true ->
    Forall (fun w => sep_free seps w = true) (words_acc seps cur s).
Proof.
  induction s as [ | c s IH ]; intros cur H_cur; cbn [words_acc].
  1:{ destruct (String.eqb cur EmptyString); [ constructor | ].
      constructor; [ exact H_cur | constructor ]. }
  destruct (is_sep seps c) eqn:E_sep.
  1:{ apply Forall_app; split; [ | apply IH; reflexivity ].
      destruct (String.eqb cur EmptyString); [ constructor | ].
      constructor; [ exact H_cur | constructor ]. }
  1:{ apply IH. apply sep_free_app; [ exact H_cur | ].
      cbn [sep_free]; rewrite E_sep; reflexivity. }
Qed.

Lemma Forall_sep_free_words : forall seps s,
    Forall (fun w => sep_free seps w = true) (words seps s).
Proof. intros; apply Forall_sep_free_words_acc; reflexivity. Qed.

(* and so the runtime test is sound: a string that is its own only word
   has no separator in it *)
Lemma words_singleton__sep_free : forall seps s,
    words seps s = [s] -> sep_free seps s = true.
Proof.
  intros seps s E.
  pose proof (Forall_sep_free_words seps s) as H.
  rewrite E in H. inversion H; assumption.
Qed.


(* THE lemma the tokenized lookup rests on: an occurrence that contains no
   separator lies inside a single WORD of the text.  That is what makes a
   word-split index answer a substring query -- the pattern never straddles
   a word boundary, so some one word contains it, and that word's padded
   trigrams are in the index.

   Generalized over the accumulator, which is what makes the induction on
   the prefix go through: a word character before the occurrence does not
   restart the word, it extends it. *)
Lemma sep_free_inside_word_acc : forall seps a w pre b,
    sep_free seps w = true ->
    w <> EmptyString ->
    sep_free seps pre = true ->
    exists w' x y, In w' (words_acc seps pre (a ++ w ++ b)) /\ w' = x ++ w ++ y.
Proof.
  intros seps a; induction a as [ | c a IH ]; intros w pre b H_w H_ne H_pre.
  - cbn [append].
    rewrite <- (words_acc_absorb seps w pre b H_w).
    destruct (words_acc_head seps b (pre ++ w)) as [ t [ rest E ] ].
    1:{ destruct pre as [ | c pre ]; cbn [append]; [ exact H_ne | discriminate ]. }
    rewrite E. exists ((pre ++ w) ++ t), pre, t; split; [ left; reflexivity | ].
    rewrite append_assoc. reflexivity.
  - cbn [append words_acc]. destruct (is_sep seps c) eqn:E_sep.
    + destruct (IH w EmptyString b H_w H_ne eq_refl)
        as [ w' [ x [ y [ H_in E ] ] ] ].
      exists w', x, y; split; [ | exact E ].
      destruct (String.eqb pre EmptyString); cbn [app];
        [ exact H_in | right; exact H_in ].
    + apply (IH w (pre ++ String c EmptyString) b H_w H_ne).
      apply sep_free_app; [ exact H_pre | ].
      cbn [sep_free]. rewrite E_sep. reflexivity.
Qed.

Theorem sep_free_inside_word : forall seps w a b,
    sep_free seps w = true ->
    w <> EmptyString ->
    exists w' x y, In w' (words seps (a ++ w ++ b)) /\ w' = x ++ w ++ y.
Proof.
  intros seps w a b H_free H_ne. unfold words.
  apply sep_free_inside_word_acc; [ exact H_free | exact H_ne | reflexivity ].
Qed.

(* and therefore, in the form the index wants it: every trigram a
   separator-free pattern demands is a trigram of some word's PADDED text,
   which is exactly what the word-split index keys on.  trigrams_factor
   carries the trigram from the pattern to the containing word, and
   trigrams_pad carries it from the word to the word's padded form. *)
Corollary trigrams_inside_word : forall seps w a b g,
    sep_free seps w = true ->
    w <> EmptyString ->
    In g (trigrams w) ->
    exists w', In w' (words seps (a ++ w ++ b)) /\ In g (trigrams (pad w')).
Proof.
  intros seps w a b g H_free H_ne H_tri.
  destruct (sep_free_inside_word seps w a b H_free H_ne)
    as [ w' [ x [ y [ H_in E ] ] ] ].
  exists w'; split; [ exact H_in | ]. subst w'.
  apply trigrams_pad, trigrams_factor. exact H_tri.
Qed.

(* the two shapes agree on a word: a word of a string is separator-free and
   non-empty, which is what the corollary above asks for *)
Example sep_free_word : sep_free " " "Smith" = true.
Proof. reflexivity. Qed.

Example sep_free_not : sep_free " " "Smith Jones" = false.
Proof. reflexivity. Qed.
