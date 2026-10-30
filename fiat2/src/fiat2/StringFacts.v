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

Lemma In_trigrams_length : forall s g, In g (trigrams s) -> String.length g = 3.
Proof.
  unfold trigrams; intros s g H_in.
  apply in_map_iff in H_in as [ i [ E_g H_i ] ].
  apply in_seq in H_i. subst g.
  apply length_substring_ge. lia.
Qed.
