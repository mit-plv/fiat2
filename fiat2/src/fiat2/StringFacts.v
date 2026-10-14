From Stdlib Require Import String Ascii List Lia.
Import ListNotations.

(* The string theory a trigram index needs, and which neither fiat2 nor the
   standard library has.

   A trigram index is an inverted index: it maps each three-character
   substring of a text to the rows whose text contains it.  A lookup for a
   pattern p takes the bucket of ONE trigram of p and rechecks the full
   containment on the rows it finds.  That is correct only because of
   occurrence_first_trigram below: if p occurs in s at all, then p's first
   trigram is among s's trigrams, so the bucket cannot miss a row.  (The
   converse is false -- a trigram match is necessary, not sufficient -- which
   is why the recheck stays.)

   The standard library relates String.index to String.substring
   (index_correct1), and that is the only bridge it offers; the three
   substring facts below are what carry p's first trigram back to a trigram
   of s.  Each one is proved by induction on the string with the LENGTH
   argument destructed before the offset, because substring's match scrutinises
   the string first and so reduces only once the string is in constructor
   form. *)

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

(* The fact the lookup rule rests on: an occurrence of p in s puts p's first
   trigram among s's trigrams. *)
Theorem occurrence_first_trigram : forall p s m,
    3 <= String.length p ->
    String.index 0 p s = Some m ->
    In (substring 0 3 p) (trigrams s).
Proof.
  intros p s m H_len E_idx.
  (* p sits at offset m in s *)
  assert (E_sub : substring m (String.length p) s = p)
    by (eapply String.index_correct1; exact E_idx).
  (* so p's first three characters are s's three characters at m *)
  assert (E_tri : substring 0 3 p = substring m 3 s).
  1:{ rewrite <- E_sub at 1. apply substring_0_substring. exact H_len. }
  (* and m is far enough from the end of s for that to be a trigram of s *)
  assert (H_fit := length_substring_le s m (String.length p)).
  rewrite E_sub in H_fit.
  unfold trigrams. rewrite E_tri.
  apply in_map_iff. exists m; split; [ reflexivity | ].
  apply in_seq. lia.
Qed.

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
