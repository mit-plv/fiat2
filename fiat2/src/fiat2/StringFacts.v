From Stdlib Require Import String Ascii List Arith Lia.
Import ListNotations.

Local Open Scope string_scope.

(* The string theory a trigram index needs. *)

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

Lemma In_trigrams_first : forall p,
    3 <= String.length p -> In (substring 0 3 p) (trigrams p).
Proof.
  unfold trigrams; intros p H_len.
  apply in_map_iff. exists 0; split; [ reflexivity | ]. apply in_seq. lia.
Qed.


(* We use PostgreSQL's padding as reference.

   pg_trgm does not extract a string's trigrams directly: it pads first,
   LPADDING 2 and RPADDING 1 with a space. *)
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

Lemma substring_pad_shift : forall s i k,
    substring (2 + i) k (pad s) = substring i k (s ++ " ").
Proof. intros; unfold pad; reflexivity. Qed.

Theorem trigrams_pad : forall s g, In g (trigrams s) -> In g (trigrams (pad s)).
Proof.
  unfold trigrams; intros s g H_in.
  apply in_map_iff in H_in as [ i [ E_g H_i ] ]. apply in_seq in H_i.
  apply in_map_iff. exists (2 + i); split.
  1:{ rewrite substring_pad_shift, substring_app_l by lia. exact E_g. }
  1:{ apply in_seq. rewrite length_pad. lia. }
Qed.

Example trigrams_smith : trigrams "Smith" = [ "Smi"; "mit"; "ith" ].
Proof. reflexivity. Qed.

Example trigrams_pad_smith :
  trigrams (pad "Smith") = [ "  S"; " Sm"; "Smi"; "mit"; "ith"; "th " ].
Proof. reflexivity. Qed.

(* The pair that makes the point: unpadded, these two names share nothing. *)
Example trigrams_smyth : trigrams "Smyth" = [ "Smy"; "myt"; "yth" ].
Proof. reflexivity. Qed.

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

Lemma In_trigrams_nonempty : forall s g, In g (trigrams s) -> s <> EmptyString.
Proof.
  intros s g H; destruct s as [ | c s ]; [ | discriminate ].
  cbn [trigrams String.length Nat.sub List.seq List.map] in H; contradiction.
Qed.

Lemma trigrams_not_nil : forall s,
    (3 <= String.length s)%nat -> trigrams s <> nil.
Proof.
  intros s H_len; unfold trigrams.
  destruct (String.length s - 2)%nat eqn:E; [ lia | ].
  cbn [List.seq List.map]. discriminate.
Qed.

Lemma In_trigrams_length : forall s g, In g (trigrams s) -> String.length g = 3.
Proof.
  unfold trigrams; intros s g H_in.
  apply in_map_iff in H_in as [ i [ E_g H_i ] ].
  apply in_seq in H_i. subst g.
  apply length_substring_ge. lia.
Qed.

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

Lemma substring_app_r : forall a t n k,
    substring (String.length a + n) k (a ++ t) = substring n k t.
Proof.
  induction a as [ | c a IH ]; intros t n k; [ reflexivity | ].
  cbn [String.length append substring]. apply IH.
Qed.

Theorem trigrams_factor : forall a p b g,
    In g (trigrams p) -> In g (trigrams (a ++ p ++ b)).
Proof.
  unfold trigrams; intros a p b g H_in.
  apply in_map_iff in H_in as [ i [ E_g H_i ] ]. apply in_seq in H_i.
  apply in_map_iff. exists (String.length a + i); split.
  - rewrite substring_app_r, substring_app_l by lia. exact E_g.
  - apply in_seq. rewrite !length_append. lia.
Qed.

(* Words.
   pg_trgm splits a text into the maximal runs of word characters and
   trigrams each one separately, padded (trgm_op.c, find_word and
   generate_trgm_only).  The separator class is a parameter here, given as
   the string of separator characters.

   pg_trgm's own class is a build-time choice (KEEPONLYALNUM), so this
   narrows a parameter rather than changing the design. *)

Definition is_sep (seps : string) (c : ascii) : bool :=
  match String.index 0 (String c EmptyString) seps with
  | Some _ => true
  | None => false
  end.

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

Lemma words_singleton__sep_free : forall seps s,
    words seps s = [s] -> sep_free seps s = true.
Proof.
  intros seps s E.
  pose proof (Forall_sep_free_words seps s) as H.
  rewrite E in H. inversion H; assumption.
Qed.

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

Example sep_free_word : sep_free " " "Smith" = true.
Proof. reflexivity. Qed.

Example sep_free_not : sep_free " " "Smith Jones" = false.
Proof. reflexivity. Qed.
