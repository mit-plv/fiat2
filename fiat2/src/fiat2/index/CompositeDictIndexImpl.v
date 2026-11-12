Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.index.IndexInterface fiat2.rules.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils
  fiat2.Substitute fiat2.rules.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
(* NOT Import: this file defines to_idx, idx_ty, is_tbl_ty and gallina_to_idx
   of its own, and importing would shadow them.  What is wanted from here is
   the handful of lemmas about dict_insert, dict_lookup and bag_insert that say
   nothing about any index -- they happen to live there, and the comment at
   DictIndexImpl.v:348 states the convention under which they belong in Utils
   instead.  Moving them is the right cleanup and would drop this dependency;
   it touches the whole build, so it is noted rather than done in passing. *)
Require fiat2.index.DictIndexImpl.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.

(* ============================================================
   A DICTIONARY KEYED ON A SEQUENCE OF ATTRIBUTES.

   WHY IT NEEDS NO NEW TYPE AND NO NEW OPERATOR.  The key is a RECORD of the
   key attributes, so TRecord carries it, value_compare already orders it
   (record_compare, Value.v:102), and OLookup is key-generic.  The only thing
   that had to be checked is that the key a lookup BUILDS equals the key the
   index STORED even when the two are written with their fields in different
   orders -- and it does, because interp_expr of an ERecord canonicalises with
   record_sort (Interpret.v:448), while TyERecord accepts the literal in any
   order and types it at the sorted permutation (TypeSystem.v:279-285).  So
   field order is a non-issue on both sides, which is what makes a composite
   key an ordinary dictionary rather than a new structure.

   ANY ARITY.  The key is a list of attributes, `attrs`, and every statement
   about the key is a statement about a map over that list.  Three facts carry
   the generalisation, and they are the three lemmas to read first:

     - record_proj_record_sort: a field read out of the SORTED key record is
       the field that was put in, whatever the arity, provided the names are
       duplicate-free.  This is what makes a record key a faithful TUPLE.
     - ckey_eq_iff: a conjunction of field equalities holds exactly when the
       two composite keys are equal.  This is the mathematical content of a
       composite key, and the arity only appears as the length of a Forall.
     - conj_eq_pairs: the rule's pattern is no longer a fixed tree.  A
       recursive matcher collects the conjuncts of an arbitrarily long, and
       arbitrarily ASSOCIATED, conjunction and hands back the (attribute,
       right-hand side) pairs it found.  Association is therefore free; see
       the rule for what is not.

   Arity one is not excluded and is not useless: it is a dictionary keyed on a
   record of ONE field, which is DictIndexImpl's index wearing a record
   wrapper.  The wrapper costs a constant per probe, so there is no reason to
   prefer it there -- stated because the degenerate case being WELL DEFINED is
   what lets the rule be one rule.

   WHAT IT IS FOR.  Three subjects measure its absence.  eval/Kafka_Cluster's
   partition(topic, partition) is a conjunctive equality on two attributes --
   `new TopicPartition(p.topic(), p.partition())` in Kafka.
   eval/HA_EntityRegistry's async_get_entity_id(domain, platform, unique_id)
   is the same shape on THREE -- `self._index[(entry.domain, entry.platform,
   entry.unique_id)]` in Home Assistant, a dict the author keys on a 3-tuple
   by hand.  eval/Kafka_WindowStore's fetch(key, from, to) wants a point on
   key and a range on time, which this index does not serve.

   UNRANGED, AND THAT IS NOT A LIMITATION OF THIS FILE.  record_compare orders
   records lexicographically in SORTED FIELD-NAME order, which is not the order
   a programmer declared the key in, so a range over a composite key would
   range on whichever attribute happens to sort first by name.  That is a
   trap, not a feature, and no witnessed query wants it: both composite reads
   above are points.  The kind therefore says Unranged, which already makes
   ODictRange untypeable here -- see Ex_DictMinKey for the same refusal used
   deliberately.
   ============================================================ *)

(* ---- list-level helpers, stated over an arbitrary attribute list ----

   `attrs` below is a section variable, so everything that needs an induction
   is stated here over a universally quantified list and instantiated at
   attrs. *)

Lemma map_fst_pairs : forall A (f : string -> A) al,
    List.map fst (List.map (fun a => (a, f a)) al) = al.
Proof.
  induction al; cbn; congruence.
Qed.

Lemma map_snd_pairs : forall A (f : string -> A) al,
    List.map snd (List.map (fun a => (a, f a)) al) = List.map f al.
Proof.
  induction al; cbn; congruence.
Qed.

Lemma all_neqb'_not_In : forall s al, all_neqb' s al = true -> ~ In s al.
Proof.
  induction al; cbn; intros H; [ intuition idtac | ].
  rewrite Bool.andb_true_iff, Bool.negb_true_iff, String.eqb_neq in H.
  intuition idtac; congruence.
Qed.

Lemma all_neqb_NoDup : forall al, all_neqb al = true -> NoDup al.
Proof.
  induction al; cbn; intros H; [ constructor | ].
  rewrite Bool.andb_true_iff in H. destruct H as [ H1 H2 ].
  constructor; [ apply all_neqb'_not_In; assumption | apply IHal; assumption ].
Qed.

Lemma all_neqb'_of_not_In : forall s al, ~ In s al -> all_neqb' s al = true.
Proof.
  induction al; cbn; intros H; auto.
  rewrite Bool.andb_true_iff, Bool.negb_true_iff, String.eqb_neq.
  intuition auto.
Qed.

Lemma NoDup_all_neqb : forall al, NoDup al -> all_neqb al = true.
Proof.
  induction al; cbn; intros H; auto.
  invert_NoDup. rewrite Bool.andb_true_iff.
  split; [ apply all_neqb'_of_not_In | apply IHal ]; assumption.
Qed.

(* ---- recognising the index's own key literal ----

   The maintenance rule matches the index-building FOLD, whose key is a record
   literal computed from attrs rather than written out, so a pattern cannot
   bind it positionally.  This checks it instead. *)
Fixpoint keys_match (t : string) (al : list string) (kl : list (string * expr))
  : bool :=
  match al, kl with
  | [], [] => true
  | a :: al, (b, EAccess (EVar t') c) :: kl =>
      (String.eqb a b && String.eqb a c && String.eqb t t'
       && keys_match t al kl)%bool
  | _, _ => false
  end.

Lemma keys_match_eq : forall t al kl,
    keys_match t al kl = true ->
    kl = List.map (fun a => (a, EAccess (EVar t) a)) al.
Proof.
  induction al as [ | a al IH ]; destruct kl as [ | p kl ];
    cbn [keys_match List.map]; intros H; try discriminate; auto.
  destruct p as [ b e ].
  repeat (destruct_match_hyp; try discriminate).
  repeat rewrite Bool.andb_true_iff in H.
  rewrite !String.eqb_eq in H.
  destruct H as [ [ [ Hab Hac ] Htt ] Hrest ]; subst.
  f_equal. apply IH; assumption.
Qed.

Lemma attrs_nonempty : forall A (al : list A),
    Nat.eqb (List.length al) 0 = false -> al <> [].
Proof.
  destruct al; cbn; intros H; [ discriminate | congruence ].
Qed.

Lemma access_record_get_attr_type : forall rt a,
    In a (List.map fst rt) ->
    access_record rt a = Success (get_attr_type rt a).
Proof.
  intros rt a H.
  apply In_access_record in H. destruct H as [t Ht].
  unfold get_attr_type. rewrite Ht. reflexivity.
Qed.


(* ---- matching an arbitrarily long conjunction of attribute equalities ----

   The binary rule's pattern was a fixed tree: one EBinop OAnd with an
   equality under each side.  At arity n there is no fixed tree -- n-1
   conjunctions, in any association -- so the pattern becomes a RECURSIVE
   MATCHER that collects the (attribute, right-hand side) pairs it finds, and
   ASSOCIATION BECOMES FREE.  The freshness condition that lets a right-hand
   side out from under the row binder is checked per conjunct, here, rather
   than once per side in the rule's guard. *)

Definition eq_attr_pair (x0 : string) (e : expr) : option (string * expr) :=
  match e with
  | EBinop OEq (EAccess (EVar y) a) rhs =>
      if (String.eqb y x0 && negb (free_immut_in x0 rhs))%bool
      then Some (a, rhs) else None
  | _ => None
  end.

Fixpoint conj_eq_pairs (x0 : string) (e : expr) : option (list (string * expr)) :=
  match e with
  | EBinop OAnd e1 e2 =>
      match conj_eq_pairs x0 e1, conj_eq_pairs x0 e2 with
      | Some p1, Some p2 => Some (p1 ++ p2)%list
      | _, _ => None
      end
  | _ => match eq_attr_pair x0 e with
         | Some p => Some [p]
         | None => None
         end
  end.

(* The recursive case, as an equation. *)
Lemma conj_eq_pairs_and : forall x0 e1 e2,
    conj_eq_pairs x0 (EBinop OAnd e1 e2)
    = match conj_eq_pairs x0 e1, conj_eq_pairs x0 e2 with
      | Some p1, Some p2 => Some (p1 ++ p2)%list
      | _, _ => None
      end.
Proof. reflexivity. Qed.

(* ---- the sort is determined by the multiset of NAMES ----

   record_entry_leb compares field NAMES only (Value.v:498), so it is total
   and transitive but NOT antisymmetric: two entries with the same name and
   different values are below each other both ways.  It IS antisymmetric where
   the names are distinct, which is exactly what a NoDup premise buys, and
   that is enough for the sort to be determined by the multiset.  Stdlib has
   no uniqueness lemma for a sort under a merely total order, so here it is.

   WHY THIS MATTERS HERE.  It is what makes the declared ORDER of a composite
   key's attributes inert: the stored key record is record_sort'ed, so an
   index on (a, b) and an index on (b, a) are the same index, and a read may
   list its conjuncts in any order at all.  Without this lemma the read rule
   has to insist on one order, which is what it used to do. *)

Lemma string_leb_antisym : forall s s',
    String.leb s s' = true -> String.leb s' s = true -> s = s'.
Proof.
  unfold String.leb; intros s s' H H'.
  destruct (String.compare s' s) eqn:E.
  - symmetry; apply String.compare_eq_iff; assumption.
  - rewrite String.compare_antisym, E in H; cbn in H; discriminate.
  - discriminate.
Qed.

Lemma StronglySorted_NoDup_Permutation_eq :
  forall A (l l' : list (string * A)),
    StronglySorted (fun p p' => is_true (record_entry_leb p p')) l ->
    StronglySorted (fun p p' => is_true (record_entry_leb p p')) l' ->
    NoDup (List.map fst l) ->
    Permutation l l' ->
    l = l'.
Proof.
  induction l as [ | p l IH ]; intros l' Hs Hs' Hnd Hp.
  - apply Permutation_nil in Hp; congruence.
  - destruct l' as [ | p' l' ].
    1: apply Permutation_sym, Permutation_nil in Hp; discriminate.
    inversion Hs as [ | ? ? Hs2 Hall ]; subst.
    inversion Hs' as [ | ? ? Hs2' Hall' ]; subst.
    (* the two heads are the same entry: each is in the other list, and if
       neither is the other's head then the names are below each other both
       ways, so they are equal -- and then one name occurs twice *)
    assert (Hhd : p = p').
    { pose proof (Permutation_in _ Hp (or_introl eq_refl)) as Hin.
      pose proof (Permutation_in _ (Permutation_sym Hp) (or_introl eq_refl)) as Hin'.
      cbn in Hin, Hin'.
      destruct Hin as [ Heq | Hin ]; [ congruence | ].
      destruct Hin' as [ Heq' | Hin' ]; [ congruence | ].
      exfalso.
      rewrite Forall_forall in Hall, Hall'.
      pose proof (Hall _ Hin') as Hle.
      pose proof (Hall' _ Hin) as Hle'.
      unfold record_entry_leb, is_true in Hle, Hle'.
      pose proof (string_leb_antisym _ _ Hle Hle') as Hname.
      inversion Hnd as [ | ? ? Hni ]; subst.
      apply Hni. rewrite Hname. apply in_map; assumption. }
    subst p'. f_equal.
    cbn in Hnd; inversion Hnd; subst.
    apply IH; try assumption.
    eapply Permutation_cons_inv; eassumption.
Qed.

Lemma record_sort_Permutation_eq :
  forall A (l l' : list (string * A)),
    NoDup (List.map fst l) ->
    Permutation l l' ->
    record_sort l = record_sort l'.
Proof.
  intros A l l' Hnd Hp.
  apply StronglySorted_NoDup_Permutation_eq;
    auto using StronglySorted_record_sort.
  - eapply Permutation_NoDup;
      [ apply Permutation_map, Permuted_record_sort | assumption ].
  - eapply perm_trans; [ apply Permutation_sym, Permuted_record_sort | ].
    eapply perm_trans; [ exact Hp | apply Permuted_record_sort ].
Qed.

Section ConjMatcher.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Notation value := (value).
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Definition conj_sat (store env : locals) (rc : list (string * value))
    (prs : list (string * expr)) : bool :=
    forallb (fun p => value_eqb (record_proj (fst p) rc)
                        (interp_expr store env (snd p))) prs.

  Lemma conj_sat_single : forall (store env : locals) rc p,
      conj_sat store env rc [p]
      = value_eqb (record_proj (fst p) rc) (interp_expr store env (snd p)).
  Proof.
    intros. unfold conj_sat; cbn [forallb]. apply Bool.andb_true_r.
  Qed.

  Lemma interp_eq_attr_pair : forall (store env : locals) x0 e rc,
      match eq_attr_pair x0 e with
      | Some p =>
          interp_expr store (map.put env x0 (VRecord rc)) e
          = VBool (value_eqb (record_proj (fst p) rc)
                     (interp_expr store env (snd p)))
      | None => True
      end.
  Proof.
    intros store env x0 e rc.
    unfold eq_attr_pair. repeat (case_match; auto; []).
    lazymatch goal with
      H : (_ && _)%bool = true |- _ =>
        rewrite Bool.andb_true_iff, Bool.negb_true_iff, String.eqb_eq in H;
        destruct H as [ -> Hf ]
    end.
    cbn [interp_expr fst snd]. unfold get_local. rewrite map.get_put_same.
    cbn [interp_binop].
    erewrite <- not_free_immut_put_sem by eassumption. reflexivity.
  Qed.

  Lemma interp_conj_leaf : forall (store env : locals) x0 e rc,
      match match eq_attr_pair x0 e with
            | Some p => Some [p]
            | None => None
            end with
      | Some prs =>
          interp_expr store (map.put env x0 (VRecord rc)) e
          = VBool (conj_sat store env rc prs)
      | None => True
      end.
  Proof.
    intros store env x0 e rc.
    pose proof (interp_eq_attr_pair store env x0 e rc) as Hp.
    destruct (eq_attr_pair x0 e) as [ p | ]; [ | exact I ].
    rewrite conj_sat_single. assumption.
  Qed.

  Lemma interp_conj_eq_pairs : forall (store env : locals) x0 e rc,
      match conj_eq_pairs x0 e with
      | Some prs =>
          interp_expr store (map.put env x0 (VRecord rc)) e
          = VBool (conj_sat store env rc prs)
      | None => True
      end.
  Proof.
    intros store env x0 e rc.
    induction e; try (apply interp_conj_leaf).
    destruct o; try (apply interp_conj_leaf).
    rewrite conj_eq_pairs_and.
    (* OAnd: the conjunction of the two sides' forallb is the forallb of the
       concatenation, which is the whole content of the recursive case *)
    destruct (conj_eq_pairs x0 e1) as [ p1 | ];
      destruct (conj_eq_pairs x0 e2) as [ p2 | ];
      cbv beta iota; auto.
    cbv beta iota in IHe1, IHe2.
    cbn [interp_expr]. rewrite IHe1, IHe2.
    cbn [interp_binop apply_bool_binop].
    unfold conj_sat. rewrite forallb_app. reflexivity.
  Qed.

  Lemma eq_attr_pair_ty : forall (Gstore Genv : tenv) x0 e rt t,
      type_of Gstore (map.put Genv x0 (TRecord rt)) e t ->
      match eq_attr_pair x0 e with
      | Some p =>
          In (fst p) (List.map fst rt)
          /\ type_of Gstore Genv (snd p) (get_attr_type rt (fst p))
      | None => True
      end.
  Proof.
    intros Gstore Genv x0 e rt t He.
    unfold eq_attr_pair. repeat (case_match; auto; []).
    lazymatch goal with
      H : (_ && _)%bool = true |- _ =>
        rewrite Bool.andb_true_iff, Bool.negb_true_iff, String.eqb_eq in H;
        destruct H as [ -> Hf ]
    end.
    cbn [fst snd].
    repeat invert_type_of_clear. repeat invert_type_of_op_clear.
    rewrite_map_get_put_hyp.
    repeat (clear_refl; repeat do_injection2).
    (* the row type arrives as Some (TRecord rt) = Some (TRecord tl), which
       do_injection2 leaves alone *)
    lazymatch goal with
      H : Some _ = Some _ |- _ => inversion H; subst
    end.
    lazymatch goal with
      H : access_record ?r ?a = Success _ |- In ?a (List.map fst ?r) /\ _ =>
        pose proof H as Hacc; apply access_record_sound in H;
        apply (in_map fst) in H
    end.
    split; [ assumption | ].
    unfold get_attr_type. rewrite Hacc.
    eapply not_free_immut_put_ty; eassumption.
  Qed.

  Lemma conj_leaf_ty : forall (Gstore Genv : tenv) x0 e rt t,
      type_of Gstore (map.put Genv x0 (TRecord rt)) e t ->
      match match eq_attr_pair x0 e with
            | Some p => Some [p]
            | None => None
            end with
      | Some prs =>
          Forall (fun p => In (fst p) (List.map fst rt)
                           /\ type_of Gstore Genv (snd p)
                                (get_attr_type rt (fst p))) prs
      | None => True
      end.
  Proof.
    intros Gstore Genv x0 e rt t He.
    pose proof (eq_attr_pair_ty Gstore Genv x0 e rt t He) as Hp.
    destruct (eq_attr_pair x0 e) as [ p | ]; [ | exact I ].
    constructor; auto.
  Qed.

  (* A key literal's typing says the ROW TYPE IS A RECORD, provided the key
     has at least one attribute: its first field is an access on the row, and
     TyEAccess types an access only at a record.  Stated here, over an
     arbitrary attribute list, because inside the index's section `attrs` is a
     section variable and cannot be case-split -- the other definitions there
     mention it. *)
  Lemma key_lit_row_record : forall (Gstore Genv : tenv) (r : string) al kt,
      al <> [] ->
      type_of Gstore Genv
        (ERecord (List.map (fun a => (a, EAccess (EVar r) a)) al)) kt ->
      exists rt, map.get Genv r = Some (TRecord rt).
  Proof.
    intros Gstore Genv r al kt Hne H.
    destruct al as [ | a0 al ]; [ congruence | ].
    inversion H; subst.
    (* the literal's first field is an access on the row; one step of the
       Forall2 is all this needs *)
    lazymatch goal with
      Hty : Forall2 _ (List.map snd (_ :: _)) (List.map snd ?tl) |- _ =>
        destruct tl as [ | p0 tl0 ]; cbn [List.map snd] in Hty;
        inversion Hty as [ | u w l1 l2 Hhd Htl ]; subst
    end.
    inversion Hhd; subst.
    lazymatch goal with
      H' : type_of _ _ (EVar r) _ |- _ => inversion H'; subst
    end.
    eexists; eassumption.
  Qed.

  Lemma conj_eq_pairs_ty : forall (Gstore Genv : tenv) x0 e rt t,
      type_of Gstore (map.put Genv x0 (TRecord rt)) e t ->
      match conj_eq_pairs x0 e with
      | Some prs =>
          Forall (fun p => In (fst p) (List.map fst rt)
                           /\ type_of Gstore Genv (snd p)
                                (get_attr_type rt (fst p))) prs
      | None => True
      end.
  Proof.
    intros Gstore Genv x0 e rt t He. generalize dependent t.
    induction e; intros t He;
      try (eapply conj_leaf_ty; eassumption).
    destruct o; try (eapply conj_leaf_ty; eassumption).
    rewrite conj_eq_pairs_and.
    invert_type_of_clear. invert_type_of_op_clear.
    lazymatch goal with
      H1 : type_of _ _ e1 _, H2 : type_of _ _ e2 _ |- _ =>
        specialize (IHe1 _ H1); specialize (IHe2 _ H2)
    end.
    destruct (conj_eq_pairs x0 e1) as [ p1 | ];
      destruct (conj_eq_pairs x0 e2) as [ p2 | ];
      cbv beta iota; auto.
    cbv beta iota in IHe1, IHe2.
    rewrite Forall_app; split; assumption.
  Qed.
End ConjMatcher.

Section WithHole.
  Context (hole : string).
  (* The key attributes, in the order the index is DECLARED with.  Their order
     does not reach the stored key -- record_sort decides that -- but it is
     the order the read rule expects the conjuncts in, so it is not inert. *)
  Context (attrs : list string).

  Section WithVars.
    Context (tup acc x : string).
    Context (H_NoDup : is_NoDup_opaque [tup; acc; x]).

    Definition composite_key (r : expr) : expr :=
      ERecord (List.map (fun a => (a, EAccess r a)) attrs).

    (* The index-building fold, over an ARBITRARY collection expression.  The
       index interface wants it over the hole; the maintenance rule below
       needs the same fold over the TAIL of a cons, and both are this one. *)
    Definition to_idx_from (d : expr) : expr :=
      let k := composite_key (EVar tup) in
      EFold d (EAtom (AEmptyDict Unranged None)) tup acc
        (ETernop OInsert (EVar acc) k
           (EBinop OBagInsert
              (EOptMatch (EBinop OLookup (EVar acc) k)
                 (EAtom (AEmptyBag None))
                 x (EVar x))
              (EVar tup))).

    Definition to_idx : expr := to_idx_from (EVar hole).

    (* The key attributes must all be present AND PAIRWISE DISTINCT.
       Distinctness is not fussiness: a record literal with a repeated field
       name fails TyERecord's NoDup premise, so an index on (a, a) could not be
       built at all. *)
    Definition is_tbl_ty (t : type) : bool :=
      match t with
      | TList (TRecord rt) =>
          (forallb (fun a => inb String.eqb a (List.map fst rt)) attrs
           && all_neqb attrs)%bool
      | _ => false
      end.

    Definition key_ty (rt : list (string * type)) : type :=
      TRecord (record_sort (List.map (fun a => (a, get_attr_type rt a)) attrs)).

    Definition idx_ty (t : type) : type :=
      match t with
      | TList (TRecord rt) => TDict Unranged (key_ty rt) (TBag (TRecord rt))
      | _ => TUnit
      end.

    Lemma is_tbl_ty_attrs : forall rt,
        is_tbl_ty (TList (TRecord rt)) = true ->
        Forall (fun a => In a (List.map fst rt)) attrs /\ NoDup attrs.
    Proof.
      cbn; intros rt H.
      rewrite Bool.andb_true_iff in H; destruct H as [ Hin Hnd ].
      split; [ | auto using all_neqb_NoDup ].
      rewrite Forall_forall; intros a Ha.
      rewrite forallb_forall in Hin. apply Hin in Ha.
      rewrite inb_true_iff in Ha; assumption.
    Qed.

    (* The read rule's two decidable tests, cashed in as the permutation every
       key lemma above wants: every attribute the index declares occurs among
       the collected conjuncts, and there are exactly as many conjuncts as
       attributes.  With the attributes distinct -- which is_tbl_ty already
       forces -- that is a permutation, and so the conjunction may list its
       equalities IN ANY ORDER. *)
    Lemma guard_Permutation : forall (prs : list (string * expr)),
        NoDup attrs ->
        forallb (fun a => inb String.eqb a (List.map fst prs)) attrs = true ->
        Nat.eqb (List.length attrs) (List.length prs) = true ->
        Permutation (List.map fst prs) attrs.
    Proof.
      intros prs Hnd Hin Hlen.
      apply Nat.eqb_eq in Hlen.
      apply Permutation_sym, NoDup_Permutation_bis.
      - assumption.
      - rewrite length_map. rewrite <- Hlen. apply Nat.le_refl.
      - rewrite forallb_forall in Hin. intros a Ha.
        apply Hin in Ha. rewrite inb_true_iff in Ha. assumption.
    Qed.

    Lemma key_ty_wf : forall rt,
        type_wf (TRecord rt) ->
        is_tbl_ty (TList (TRecord rt)) = true ->
        type_wf (key_ty rt).
    Proof.
      intros rt Hwf Htbl.
      pose proof (is_tbl_ty_attrs _ Htbl) as [ _ Hnd ].
      unfold key_ty. constructor.
      - eapply Permutation_NoDup;
          [ apply Permutation_map, Permuted_record_sort | ].
        rewrite map_fst_pairs; assumption.
      - apply StronglySorted_record_sort.
      - eapply Permutation_Forall;
          [ apply Permutation_map, Permuted_record_sort | ].
        rewrite map_snd_pairs, Forall_map, Forall_forall; intros.
        apply get_attr_type_ty_wf; assumption.
    Qed.

    Lemma idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t).
    Proof.
      destruct t; cbn; intros Hwf Htbl; try congruence.
      destruct t; try congruence.
      assert (Hrt : type_wf (TRecord l)) by (invert_type_wf; assumption).
      constructor.
      - apply key_ty_wf; assumption.
      - constructor; assumption.
    Qed.

    Section WithMap.
      Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
      Notation value := (value).
      Context {locals : map.map string value} {locals_ok : map.ok locals}.

      (* A record literal whose field names are the key attributes, IN ORDER,
         has the key type, whatever the field expressions are.  Stated in this
         generality because BOTH sides need it: the index builds the key out of
         the row's attributes, and the read rule builds it out of the
         conjunction's right-hand sides. *)
      Lemma composite_key_expr_ty : forall (Gstore Genv : tenv) rt kvs,
          is_tbl_ty (TList (TRecord rt)) = true ->
          Permutation (List.map fst kvs) attrs ->
          Forall2 (type_of Gstore Genv) (List.map snd kvs)
            (List.map (get_attr_type rt) (List.map fst kvs)) ->
          type_of Gstore Genv (ERecord kvs) (key_ty rt).
      Proof.
        intros Gstore Genv rt kvs Htbl Hperm Hty.
        pose proof (is_tbl_ty_attrs _ Htbl) as [ _ Hnd ].
        assert (Hnd' : NoDup (List.map fst kvs))
          by (eapply Permutation_NoDup;
              [ apply Permutation_sym; eassumption | assumption ]).
        unfold key_ty.
        (* the literal is typed at ITS OWN field order and the key type is the
           sorted permutation of it, which is what makes the declared order of
           the index's attributes inert on the typing side *)
        eapply TyERecord with
          (tl := List.map (fun a => (a, get_attr_type rt a)) (List.map fst kvs)).
        - rewrite map_fst_pairs; reflexivity.
        - rewrite map_snd_pairs; assumption.
        - eapply perm_trans; [ | apply Permuted_record_sort ].
          apply Permutation_map; assumption.
        - rewrite map_fst_pairs; assumption.
        - apply StronglySorted_record_sort.
      Qed.

      (* Reading each key attribute out of a row is well typed at the type
         get_attr_type names. *)
      Lemma Forall2_access_ty : forall (Gstore Genv : tenv) rt r al,
          type_of Gstore Genv r (TRecord rt) ->
          Forall (fun a => In a (List.map fst rt)) al ->
          Forall2 (type_of Gstore Genv) (List.map (fun a => EAccess r a) al)
            (List.map (get_attr_type rt) al).
      Proof.
        induction al; cbn; intros Hr Hin; [ constructor | ].
        invert_Forall. constructor; [ | apply IHal; assumption ].
        econstructor; eauto using access_record_get_attr_type.
      Qed.

      (* The collected conjuncts, typed one by one, as the Forall2 that
         composite_key_expr_ty asks for. *)
      Lemma Forall2_of_pairs_ty : forall (Gstore Genv : tenv) rt prs,
          Forall (fun p => In (fst p) (List.map fst rt)
                           /\ type_of Gstore Genv (snd p)
                                (get_attr_type rt (fst p))) prs ->
          Forall2 (type_of Gstore Genv) (List.map snd prs)
            (List.map (get_attr_type rt) (List.map fst prs)).
      Proof.
        induction prs as [ | q prs IH ]; cbn [List.map]; intros HF;
          [ constructor | ].
        invert_Forall.
        lazymatch goal with H : _ /\ _ |- _ => destruct H as [ _ Hty ] end.
        constructor; [ exact Hty | apply IH; assumption ].
      Qed.

      (* ---- reading the index's side conditions OUT of a matched term ----

         The maintenance rules below match the index-building FOLD, and the
         `use the index you already have` one has to know that the type the
         fold was given IS idx_ty -- otherwise it cannot replace the fold by
         the stored member.  There is no is_tbl_ty premise to lean on, so the
         facts are recovered from the matched term's own typing, and they are
         all there: the key literal's field names ARE attrs, so TyERecord's
         NoDup premise makes them distinct; each field is an access on the
         row, so each access's typing makes the attribute present; and the key
         type is then forced, because a sorted permutation of a list with
         distinct names is unique (record_sort_Permutation_eq's lemma). *)
      Lemma accesses_Forall2_inv : forall (Gstore Genv : tenv) (r : string) rt tl,
          map.get Genv r = Some (TRecord rt) ->
          Forall2 (type_of Gstore Genv)
            (List.map (fun a => EAccess (EVar r) a) (List.map fst tl))
            (List.map snd tl) ->
          Forall (fun a => inb String.eqb a (List.map fst rt) = true)
            (List.map fst tl)
          /\ tl = List.map (fun a => (a, get_attr_type rt a)) (List.map fst tl).
      Proof.
        induction tl as [ | [ b T ] tl IH ]; cbn [List.map fst snd];
          intros Hget HF.
        - split; [ constructor | reflexivity ].
        - inversion HF as [ | u w l1 l2 Hhd Htl ]; subst.
          specialize (IH Hget Htl) as [ IH1 IH2 ].
          inversion Hhd; subst.
          lazymatch goal with
            H : type_of _ _ (EVar r) _ |- _ => inversion H; subst
          end.
          assert (Hacc : access_record rt b = Success T).
          { lazymatch goal with
              H2 : access_record ?r2 b = Success T |- _ =>
                enough (r2 = rt) by (subst; exact H2)
            end.
            congruence. }
          split.
          + constructor; [ | assumption ].
            rewrite inb_true_iff.
            apply access_record_sound in Hacc as Hin0.
            apply (in_map fst) in Hin0; cbn in Hin0; exact Hin0.
          + cbn [List.map]. rewrite <- IH2. do 2 f_equal.
            unfold get_attr_type. rewrite Hacc. reflexivity.
      Qed.

      Lemma EVar_ty_inv : forall (Gstore Genv : tenv) y t,
          type_of Gstore Genv (EVar y) t -> map.get Genv y = Some t.
      Proof.
        intros Gstore Genv y t H. inversion H; subst; assumption.
      Qed.

      Lemma key_lit_inv : forall (Gstore Genv : tenv) (r : string) rt kt,
          map.get Genv r = Some (TRecord rt) ->
          type_of Gstore Genv
            (ERecord (List.map (fun a => (a, EAccess (EVar r) a)) attrs)) kt ->
          is_tbl_ty (TList (TRecord rt)) = true /\ kt = key_ty rt.
      Proof.
        intros Gstore Genv r rt kt Hget H.
        (* only TyERecord can conclude at an ERecord, so this is one case *)
        inversion H; subst.
        lazymatch goal with
          Hfst : List.map fst (List.map _ attrs) = _ |- _ =>
            rewrite map_fst_pairs in Hfst
        end.
        lazymatch goal with
          Hty : Forall2 _ (List.map snd (List.map _ attrs)) _ |- _ =>
            rewrite map_snd_pairs in Hty
        end.
        lazymatch goal with
          Hfst : attrs = List.map fst ?tl0,
          Hty : Forall2 _ _ (List.map snd ?tl0) |- _ =>
            rewrite Hfst in Hty;
            pose proof (accesses_Forall2_inv _ _ r rt tl0 Hget Hty) as [ Hin Htl ];
            rewrite <- Hfst in Hin, Htl
        end.
        lazymatch goal with
          Hfst : attrs = List.map fst ?tl0, Hnd : NoDup (List.map fst ?tl0) |- _ =>
            assert (Hndattrs : NoDup attrs) by (rewrite Hfst; assumption)
        end.
        split.
        - cbn. rewrite Bool.andb_true_iff. split.
          + rewrite forallb_forall; intros a Ha.
            rewrite Forall_forall in Hin; apply Hin; assumption.
          + apply NoDup_all_neqb; assumption.
        - unfold key_ty. f_equal.
          symmetry. apply StronglySorted_NoDup_Permutation_eq.
          + apply StronglySorted_record_sort.
          + assumption.
          + eapply Permutation_NoDup;
              [ apply Permutation_map, Permuted_record_sort | ].
            rewrite map_fst_pairs; assumption.
          + eapply perm_trans;
              [ apply Permutation_sym, Permuted_record_sort | ].
            rewrite <- Htl; assumption.
      Qed.

      (* The key literal's typing also tells you the ROW TYPE IS A RECORD,
         provided the key has at least one attribute: the first field is an
         access on the row, and TyEAccess types an access only at a record.
         The rules with an is_tbl_ty hypothesis to lean on use key_lit_inv
         below; the delete rule has none and uses this. *)
      Lemma key_lit_inv_ex : forall (Gstore Genv : tenv) (r : string) kt,
          attrs <> [] ->
          type_of Gstore Genv
            (ERecord (List.map (fun a => (a, EAccess (EVar r) a)) attrs)) kt ->
          exists rt, map.get Genv r = Some (TRecord rt)
                     /\ is_tbl_ty (TList (TRecord rt)) = true
                     /\ kt = key_ty rt.
      Proof.
        intros Gstore Genv r kt Hne H.
        pose proof (key_lit_row_record Gstore Genv r attrs kt Hne H)
          as [ rt Hget ].
        exists rt. split; [ assumption | ].
        eapply key_lit_inv; eassumption.
      Qed.

      Corollary composite_key_ty : forall (Gstore Genv : tenv) rt r,
          is_tbl_ty (TList (TRecord rt)) = true ->
          type_of Gstore Genv r (TRecord rt) ->
          type_of Gstore Genv (composite_key r) (key_ty rt).
      Proof.
        intros Gstore Genv rt r Htbl Hr.
        pose proof (is_tbl_ty_attrs _ Htbl) as [ Hin _ ].
        unfold composite_key.
        apply composite_key_expr_ty.
        - assumption.
        - rewrite map_fst_pairs; apply Permutation_refl.
        - rewrite map_fst_pairs, map_snd_pairs.
          apply Forall2_access_ty; assumption.
      Qed.

      Definition ckey (rc : list (string * value)) : value :=
        VRecord (record_sort (List.map (fun a => (a, record_proj a rc)) attrs)).

      Lemma interp_key_fields : forall (store env : locals) r rc al,
          interp_expr store env r = VRecord rc ->
          List.map (fun '(s, e) => (s, interp_expr store env e))
            (List.map (fun a => (a, EAccess r a)) al)
          = List.map (fun a => (a, record_proj a rc)) al.
      Proof.
        induction al; cbn [List.map]; intros Hr; auto.
        cbn [interp_expr]. rewrite Hr.
        f_equal. apply IHal; assumption.
      Qed.

      Lemma interp_composite_key : forall (store env : locals) r rc,
          interp_expr store env r = VRecord rc ->
          interp_expr store env (composite_key r) = ckey rc.
      Proof.
        intros store env r rc Hr.
        unfold composite_key, ckey. cbn [interp_expr].
        do 2 f_equal. apply interp_key_fields; assumption.
      Qed.

      Corollary interp_composite_key_var : forall (store env : locals) y rc,
          map.get env y = Some (VRecord rc) ->
          interp_expr store env (composite_key (EVar y)) = ckey rc.
      Proof.
        intros store env y rc Hget. apply interp_composite_key.
        cbn [interp_expr]. unfold get_local; rewrite Hget; reflexivity.
      Qed.

      (* The fold's step. *)
      Lemma to_idx_body_ty : forall rt (Gstore Genv : tenv),
          type_wf (TRecord rt) ->
          is_tbl_ty (TList (TRecord rt)) = true ->
          map.get Genv tup = Some (TRecord rt) ->
          map.get Genv acc = Some (TDict Unranged (key_ty rt) (TBag (TRecord rt))) ->
          type_of Gstore Genv
            (ETernop OInsert (EVar acc) (composite_key (EVar tup))
               (EBinop OBagInsert
                  (EOptMatch (EBinop OLookup (EVar acc) (composite_key (EVar tup)))
                     (EAtom (AEmptyBag None)) x (EVar x))
                  (EVar tup)))
            (TDict Unranged (key_ty rt) (TBag (TRecord rt))).
      Proof.
        intros rt Gstore Genv Hrt Htbl Htup Hacc.
        eapply TyETernop.
        1: apply TyOInsert.
        - apply TyEVar; assumption.
        - apply composite_key_ty; [ assumption | apply TyEVar; assumption ].
        - eapply TyEBinop.
          1: apply TyOBagInsert.
          + eapply TyEOptMatch.
            * eapply TyEBinop.
              1: apply TyOLookup.
              -- apply TyEVar; eassumption.
              -- apply composite_key_ty; [ assumption | apply TyEVar; eassumption ].
            * apply TyEAtom, TyAEmptyBag'; assumption.
            * apply TyEVar. rewrite map.get_put_same; reflexivity.
          + apply TyEVar; eassumption.
      Qed.

      (* The fold is well typed over any well-typed collection, which is what
         the maintenance rule's OUTPUT needs: it rebuilds the fold over the
         tail of the cons it matched. *)
      Lemma to_idx_from_ty : forall (Gstore Genv : tenv) d t,
          type_wf t -> is_tbl_ty t = true ->
          type_of Gstore Genv d t ->
          type_of Gstore Genv (to_idx_from d) (idx_ty t).
      Proof.
        intros Gstore Genv d t Hwf Htbl Hd. unfold to_idx_from.
        destruct t; try discriminate. destruct t; try discriminate.
        cbn [idx_ty].
        assert (Hrt : type_wf (TRecord l)) by (invert_type_wf; assumption).
        eapply TyEFold.
        - exact Hd.
        - apply TyEAtom, TyAEmptyDict'.
          + apply key_ty_wf; assumption.
          + constructor; assumption.
        - apply to_idx_body_ty; auto.
          + rewrite map.get_put_diff, map.get_put_same; [ reflexivity | use_is_NoDup ].
          + rewrite map.get_put_same; reflexivity.
      Qed.

      Lemma to_idx_ty : forall (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t).
      Proof.
        intros t Hwf Htbl. unfold to_idx.
        apply to_idx_from_ty; auto.
        apply TyEVar. rewrite map.get_put_same; reflexivity.
      Qed.

      Definition idx_wf (tbl_v idx_v : value) : Prop :=
        idx_v = interp_expr map.empty (map.put map.empty hole tbl_v) to_idx.

      Lemma to_idx_wf : forall (v : value) (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          idx_wf v (interp_expr map.empty (map.put map.empty hole v) to_idx).
      Proof.
        intros; unfold idx_wf; auto.
      Qed.

      (* The key VALUE a row is filed under has the key type: the key is an
         ordinary expression of the language, so the type of its value follows
         from the type of the expression.  This is the one fact the
         characterisation below needs about the key. *)
      Lemma composite_key_value_sound : forall rt rc,
          type_wf (TRecord rt) ->
          is_tbl_ty (TList (TRecord rt)) = true ->
          type_of_value (VRecord rc) (TRecord rt) ->
          type_of_value (ckey rc) (key_ty rt).
      Proof.
        intros rt rc Hrt Htbl Hrc.
        erewrite <- interp_composite_key_var
          with (env := map.put map.empty tup (VRecord rc)) (store := map.empty).
        2: apply map.get_put_same.
        eapply type_sound with (Genv := map.put map.empty tup (TRecord rt)).
        - apply composite_key_ty; [ assumption | ].
          apply TyEVar, map.get_put_same.
        - apply tenv_wf_empty.
        - apply tenv_wf_step; [ apply tenv_wf_empty | assumption ].
        - apply locals_wf_empty.
        - apply locals_wf_step; [ apply locals_wf_empty | assumption ].
      Qed.

      (* The index the fold builds, as a Gallina function.  Same shape as the
         single-attribute model; only the key differs. *)
      Definition gallina_to_idx (tbl_v : value) : value :=
        match tbl_v with
        | VList l =>
            VDict (fold_right
                     (fun v acc =>
                        match v with
                        | VRecord rc =>
                            dict_insert (ckey rc)
                              (VBag (bag_insert (VRecord rc)
                                       (match dict_lookup (ckey rc) acc with
                                        | Some (VBag b) => b
                                        | _ => nil
                                        end))) acc
                        | _ => nil
                        end) nil l)
        | _ => VDict nil
        end.


      (* ----------------------------------------------------------------
         THIS index's instance of the bucket fold.

         The step is the single-attribute dictionary's step at a RECORD key:
         same insertion into the same kind of bucket, only the key function
         differs.  So the fact that an append builds the same index as a cons
         is DictIndexImpl's lemma instantiated here, not a second copy of its
         proof -- which is why that lemma is stated over an arbitrary key
         function in the first place. *)
      Definition cidx_step := DictIndexImpl.bidx_step ckey.

      Lemma gallina_to_idx_fold : forall l,
          gallina_to_idx (VList l) = VDict (fold_right cidx_step nil l).
      Proof. reflexivity. Qed.

      Lemma gallina_to_idx_app_singleton : forall l r,
          Forall (fun v => exists rc, v = VRecord rc) l ->
          gallina_to_idx (VList (l ++ [VRecord r]))
          = gallina_to_idx (VList (VRecord r :: l)).
      Proof.
        intros l r H_rec. rewrite !gallina_to_idx_fold. f_equal.
        unfold cidx_step.
        apply DictIndexImpl.bidx_fold_app_singleton; assumption.
      Qed.

      Lemma interp_ETernop_peel : forall (store env : locals) o e1 e2 e3,
          interp_expr store env (ETernop o e1 e2 e3)
          = interp_ternop o (interp_expr store env e1) (interp_expr store env e2)
              (interp_expr store env e3).
      Proof. reflexivity. Qed.

      Lemma interp_EOptMatch_peel : forall (store env : locals) e e_none x e_some,
          interp_expr store env (EOptMatch e e_none x e_some)
          = match interp_expr store env e with
            | VOption None => interp_expr store env e_none
            | VOption (Some v) => interp_expr store (map.put env x v) e_some
            | _ => VUnit
            end.
      Proof. reflexivity. Qed.

      Lemma interp_EVar_peel : forall (store env : locals) x,
          interp_expr store env (EVar x) = get_local env x.
      Proof. reflexivity. Qed.

      Lemma interp_EAtom_peel : forall (store env : locals) a,
          interp_expr store env (EAtom a) = interp_atom a.
      Proof. reflexivity. Qed.

      Lemma interp_EFold_peel : forall (store env : locals) c i tup0 acc0 body,
          interp_expr store env (EFold c i tup0 acc0 body)
          = match interp_expr store env c with
            | VList l => fold_right
                           (fun v a => interp_expr store
                                         (map.put (map.put env tup0 v) acc0 a) body)
                           (interp_expr store env i) l
            | _ => VUnit
            end.
      Proof. reflexivity. Qed.

      (* ----------------------------------------------------------------
         The fold's step at the MATCHED binder names, which is cidx_step as
         soon as keys_match says the key literal is this index's own. *)
      Lemma interp_cidx_body :
        forall (store env : locals) tup0 acc0 x0 kl_i kl_l rc d,
          acc0 <> tup0 -> x0 <> tup0 -> x0 <> acc0 ->
          keys_match tup0 attrs kl_i = true ->
          keys_match tup0 attrs kl_l = true ->
          DictIndexImpl.bidx_acc_wf d ->
          interp_expr store
            (map.put (map.put env tup0 (VRecord rc)) acc0 (VDict d))
            (ETernop OInsert (EVar acc0) (ERecord kl_i)
               (EBinop OBagInsert
                  (EOptMatch (EBinop OLookup (EVar acc0) (ERecord kl_l))
                     (EAtom (AEmptyBag None)) x0 (EVar x0))
                  (EVar tup0)))
          = VDict (cidx_step (VRecord rc) d).
      Proof.
        intros store env tup0 acc0 x0 kl_i kl_l rc d H_at H_xt H_xa
          H_km_i H_km_l H_wf.
        (* the insert's key and the lookup's key are each this index's, so
           they are the same literal; the rule matches them separately *)
        apply keys_match_eq in H_km_i; apply keys_match_eq in H_km_l;
          subst kl_i kl_l.
        assert (E_acc : map.get
                          (map.put (map.put env tup0 (VRecord rc)) acc0 (VDict d))
                          acc0 = Some (VDict d)) by apply map.get_put_same.
        assert (E_tup : map.get
                          (map.put (map.put env tup0 (VRecord rc)) acc0 (VDict d))
                          tup0 = Some (VRecord rc))
          by (rewrite map.get_put_diff by congruence; apply map.get_put_same).
        (* the key literal evaluates to this index's composite key *)
        assert (E_key : forall e_env,
                   map.get e_env tup0 = Some (VRecord rc) ->
                   interp_expr store e_env
                     (ERecord (List.map (fun a => (a, EAccess (EVar tup0) a)) attrs))
                   = ckey rc).
        1:{ intros e_env H_g. cbn [interp_expr]. unfold ckey.
            do 2 f_equal. apply interp_key_fields.
            cbn [interp_expr]. unfold get_local. rewrite H_g. reflexivity. }
        rewrite interp_ETernop_peel, !interp_EBinop, interp_EOptMatch_peel,
          !interp_EBinop, !interp_EVar_peel.
        rewrite !(E_key _ E_tup).
        unfold get_local. rewrite E_acc, E_tup.
        cbn [interp_ternop interp_binop].
        unfold cidx_step, DictIndexImpl.bidx_step.
        destruct (dict_lookup (ckey rc) d) as [ w | ] eqn:E.
        (* absent: the new bucket holds just this row *)
        2:{ cbn [interp_expr interp_atom]. reflexivity. }
        (* found: the entry is a bucket, which is what the invariant says *)
        rewrite interp_EVar_peel. unfold get_local, DictIndexImpl.bidx_acc_wf in *.
        rewrite map.get_put_same.
        destruct H_wf as [ _ H_b ].
        apply DictIndexImpl.dict_lookup_Some_In in E.
        rewrite Forall_forall in H_b. apply H_b in E. cbn in E.
        destruct E as [ b [ -> _ ] ]. reflexivity.
      Qed.
      (* What the fold COMPUTES, over any collection expression and in any
         environment.  The index interface's own equation is the instance at
         the hole; the maintenance rule needs the instance at the tail of a
         cons, and the proof is the same proof. *)
      Lemma interp_to_idx_from :
        forall (store env : locals) d l (l0 : list value),
          type_wf (TRecord l) ->
          is_tbl_ty (TList (TRecord l)) = true ->
          Forall (fun v => type_of_value v (TRecord l)) l0 ->
          interp_expr store env d = VList l0 ->
          interp_expr store env (to_idx_from d) = gallina_to_idx (VList l0).
      Proof.
        intros store env d l l0 Hrt Htbl' Hrows Hd.
        unfold to_idx_from; cbn [interp_expr interp_atom].
        unfold get_local. rewrite Hd.
        erewrite In_fold_right_ext with
          (P := fun a => type_of_value a (TDict Unranged (key_ty l) (TBag (TRecord l))))
          (g := fun b a =>
                  match a with
                  | VDict d =>
                      match b with
                      | VRecord rc =>
                          VDict
                            (dict_insert (ckey rc)
                               (VBag
                                  match dict_lookup (ckey rc) d with
                                  | Some (VBag bb) => bag_insert b bb
                                  | _ => [(b, 1)]
                                  end) d)
                      | _ => VUnit
                      end
                  | _ => VUnit
                  end).
        2:{ constructor; cbn; auto using NoDup_nil, SSorted_nil. }
        2:{ intros a b Ha Hb.
            invert_type_of_value_clear.
            apply_Forall_In. invert_type_of_value_clear.
            cbn [interp_expr].
            erewrite !interp_composite_key_var with (rc := l2) by
              (rewrite map.get_put_diff, map.get_put_same;
               [ reflexivity | use_is_NoDup ]).
            repeat rewrite_map_get_put_goal; try now use_is_NoDup.
            cbn [interp_ternop interp_binop interp_atom].
            assert (Hkty : type_wf (key_ty l)) by (apply key_ty_wf; auto).
            enough (type_of_value (VOption (dict_lookup (ckey l2) l1))
                      (TOption (TBag (TRecord l)))).
            2:{ eapply dict_lookup_sound with (dk := Unranged).
                1: exact Hkty.
                1: constructor; assumption.
                1: constructor; assumption.
                1: apply composite_key_value_sound; auto; constructor; auto. }
            intuition idtac.
            1:{ do 2 f_equal.
                invert_type_of_value_clear; auto.
                rewrite_map_get_put_goal.
                invert_type_of_value_clear; auto. }
            1:{ eapply dict_insert_sound with (dk := Unranged).
                1: exact Hkty.
                1: constructor; assumption.
                1: constructor; assumption.
                1: apply composite_key_value_sound; auto; constructor; auto.
                invert_type_of_value_clear; cbn.
                1: repeat (constructor; cbn; auto using NoDup_nil, SSorted_nil).
                rewrite_map_get_put_goal.
                invert_type_of_value_clear.
                constructor; auto using bag_insert_preserve_NoDup,
                  bag_insert_preserve_SSorted, bag_insert_preserve_pos.
                rewrite Forall_forall; intros ? H_in.
                apply bag_insert_incl in H_in; intuition idtac.
                (* clear first: rewrite_l_to_r would otherwise pick up the
                   FOLDED is_tbl_ty equation kept for key_ty_wf and fail on
                   it. *)
                1: clear Htbl'; rewrite_l_to_r; constructor; auto.
                1: apply_Forall_In. } }
        1:{ clear Hd. revert Hrows.
            induction l0 as [ | a l0 IH ]; intros Hrows; cbn; auto.
            invert_Forall. erewrite IH; auto.
            invert_type_of_value_clear. cbn [gallina_to_idx]. do 3 f_equal.
            repeat (case_match; auto). }
      Qed.

      Corollary fiat2_gallina_to_idx : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          interp_expr map.empty (map.put map.empty hole v) to_idx = gallina_to_idx v.
      Proof.
        intros v t Hwf Htbl Hv. unfold to_idx.
        assert (Htbl' := Htbl). unfold is_tbl_ty in Htbl.
        repeat destruct_match_hyp; try discriminate.
        assert (Hrt : type_wf (TRecord l)) by (invert_type_wf; assumption).
        invert_type_of_value_clear.
        eapply interp_to_idx_from; eauto.
        cbn [interp_expr]. unfold get_local.
        rewrite map.get_put_same; reflexivity.
      Qed.

      Lemma gallina_to_idx_sound : forall v t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          type_of_value (gallina_to_idx v) (idx_ty t).
      Proof.
        intros v t Hwf Htbl Hv.
        erewrite <- fiat2_gallina_to_idx by eassumption.
        eapply type_sound with (Gstore := map.empty)
                               (Genv := map.put map.empty hole t).
        - apply to_idx_ty; assumption.
        - apply tenv_wf_empty.
        - apply tenv_wf_step; [ apply tenv_wf_empty | assumption ].
        - apply locals_wf_empty.
        - apply locals_wf_step; [ apply locals_wf_empty | assumption ].
      Qed.


      (* The index the fold builds is key-sorted, which is what makes the
         delete below an EQUALITY of canonical dictionaries and not a
         permutation of them. *)
      Lemma gallina_to_idx_SSorted : forall l d,
          gallina_to_idx (VList l) = VDict d ->
          StronglySorted (fun p p' => is_true (dict_entry_leb p p')) d.
      Proof.
        cbn [gallina_to_idx]; intros l d H. injection H as H; subst.
        induction l as [ | r l IH ]; cbn [fold_right].
        - constructor.
        - destruct r; try constructor.
          apply dict_insert_preserve_SSorted; assumption.
      Qed.

      (* THE CONTENT OF THE DELETE RULE.  Building the index of a table with
         the rows at ONE COMPOSITE KEY filtered out is deleting that key from
         the index of the whole table. *)
      Lemma gallina_to_idx_filter_neq : forall l rt kv,
          type_of_value (VList l) (TList (TRecord rt)) ->
          gallina_to_idx
            (VList (filter (fun r => negb (value_eqb (match r with
                                                      | VRecord rc => ckey rc
                                                      | _ => VUnit
                                                      end) kv)) l))
          = match gallina_to_idx (VList l) with
            | VDict d => VDict (dict_delete kv d)
            | v => v
            end.
      Proof.
        intros l rt kv H_ty. invert_type_of_value_clear.
        lazymatch goal with
          H: Forall _ l |- _ => induction H as [ | r l H_r H_l IH ]
        end; auto.
        invert_type_of_value_clear.
        pose proof (gallina_to_idx_SSorted l _ eq_refl) as H_sort.
        cbn [gallina_to_idx filter fold_right] in *.
        injection IH as IH.
        destruct (value_eqb (ckey l0) kv) eqn:E; cbn [negb fold_right].
        - apply value_eqb_eq in E. rewrite E, dict_delete_insert_same; auto.
          f_equal; assumption.
        - assert (H_neq : ckey l0 <> kv).
          { intro H_eq. rewrite H_eq, value_eqb_refl in E. discriminate. }
          rewrite IH, dict_lookup_delete_diff, dict_delete_insert_diff; auto.
      Qed.

      (* ---- what the index means ----

         The bucket at a key holds exactly the rows whose COMPOSITE key is
         that key, up to order.  Same statement as the single-attribute one
         with record_proj attr replaced by ckey, which is the whole of the
         difference. *)
      Definition idx_chara (tbl_v idx_v : value) : Prop :=
        match tbl_v, idx_v with
        | VList l, VDict d =>
            forall key_v,
              Permutation
                (filter (fun r => match r with
                                  | VRecord rc => value_eqb (ckey rc) key_v
                                  | _ => false
                                  end) l)
                (bag_to_list match dict_lookup key_v d with
                             | Some (VBag b) => b
                             | _ => nil
                             end)
        | _, _ => False
        end.

      (* ---- the key is a faithful TUPLE ----

         record_sort only permutes, so a field read out of the sorted key
         record is the field that was put in, provided the key's names are
         duplicate-free.  THIS is what makes a record key a tuple rather than
         merely some value derived from the attributes. *)
      Lemma record_proj_record_sort : forall (kvs : list (string * value)) a,
          NoDup (List.map fst kvs) ->
          In a (List.map fst kvs) ->
          record_proj a (record_sort kvs) = record_proj a kvs.
      Proof.
        intros kvs a Hnd Hin.
        assert (H : access_record kvs a = access_record (record_sort kvs) a).
        { apply NoDup_Permutation_access_record; auto using Permuted_record_sort. }
        unfold record_proj. rewrite H. reflexivity.
      Qed.

      Lemma record_proj_pairs : forall (kvs : list (string * value)) a v,
          NoDup (List.map fst kvs) ->
          In (a, v) kvs ->
          record_proj a kvs = v.
      Proof.
        intros kvs a v Hnd Hin. unfold record_proj.
        erewrite NoDup_In_access_record; eauto.
      Qed.

      Lemma record_proj_key : forall (f : string -> value) a,
          NoDup attrs -> In a attrs ->
          record_proj a (record_sort (List.map (fun a => (a, f a)) attrs)) = f a.
      Proof.
        intros f a Hnd Hin.
        rewrite record_proj_record_sort by (rewrite map_fst_pairs; assumption).
        apply record_proj_pairs.
        - rewrite map_fst_pairs; assumption.
        - apply (in_map (fun a => (a, f a))); assumption.
      Qed.

      Corollary record_proj_ckey : forall rc a,
          NoDup attrs -> In a attrs ->
          record_proj a
            (record_sort (List.map (fun a0 => (a0, record_proj a0 rc)) attrs))
          = record_proj a rc.
      Proof.
        intros rc a. apply (record_proj_key (fun a0 => record_proj a0 rc)).
      Qed.

      Lemma pairs_eq_of_Forall : forall (f : string -> value) kvs al,
          List.map fst kvs = al ->
          Forall (fun p => f (fst p) = snd p) kvs ->
          kvs = List.map (fun a => (a, f a)) al.
      Proof.
        induction kvs as [ | [ s v ] kvs IH ]; cbn; intros al Hfst HF; subst; auto.
        invert_Forall. cbn in *. f_equal.
        - f_equal; auto.
        - apply IH; auto.
      Qed.

      (* THE MATHEMATICAL CONTENT OF A COMPOSITE KEY.  A conjunction of field
         equalities holds exactly when the two composite keys are equal.  The
         left-to-right direction is where the faithfulness above is spent;
         right-to-left is congruence.  The arity appears only as the length of
         the Forall. *)
      Lemma ckey_eq_iff : forall rc kvs,
          NoDup attrs ->
          Permutation (List.map fst kvs) attrs ->
          ckey rc = VRecord (record_sort kvs)
          <-> Forall (fun p => record_proj (fst p) rc = snd p) kvs.
      Proof.
        intros rc kvs Hnd Hperm. unfold ckey.
        assert (Hnd' : NoDup (List.map fst kvs))
          by (eapply Permutation_NoDup;
              [ apply Permutation_sym; eassumption | assumption ]).
        split.
        - intros H. injection H as H.
          rewrite Forall_forall; intros [ s v ] Hp. cbn [fst snd].
          assert (Hinkvs : In s (List.map fst kvs))
            by (apply (in_map fst) in Hp; cbn in Hp; assumption).
          assert (Hin : In s attrs) by (eapply Permutation_in; eassumption).
          rewrite <- (record_proj_ckey rc s Hnd Hin), H.
          rewrite record_proj_record_sort by assumption.
          apply record_proj_pairs; assumption.
        - intros HF.
          pose proof (pairs_eq_of_Forall (fun a => record_proj a rc) kvs
                        (List.map fst kvs) eq_refl HF) as Heq.
          f_equal.
          transitivity (record_sort
                          (List.map (fun a => (a, record_proj a rc))
                             (List.map fst kvs))).
          + apply record_sort_Permutation_eq.
            * rewrite map_fst_pairs; assumption.
            * apply Permutation_map, Permutation_sym; assumption.
          + f_equal. symmetry. exact Heq.
      Qed.

      Lemma idx_wf__idx_chara : forall (t : type) (tbl_v idx_v : value),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value tbl_v t ->
          idx_wf tbl_v idx_v -> idx_chara tbl_v idx_v.
      Proof.
        unfold idx_wf, idx_chara.
        intros; subst; erewrite fiat2_gallina_to_idx; eauto.
        unfold is_tbl_ty, gallina_to_idx in *.
        repeat destruct_match_hyp; try discriminate.
        invert_type_of_value_clear. intros.
        lazymatch goal with
          H: Forall _ _ |- _ =>
            induction H
        end; cbn; auto.
        invert_type_of_value_clear.
        case_match.
        1:{ apply value_eqb_eq in E; subst.
            rewrite DictIndexImpl.dict_lookup_insert_same.
            rewrite DictIndexImpl.bag_to_list_insert_Permutation.
            apply perm_skip; auto. }
        1:{ rewrite DictIndexImpl.dict_lookup_insert_diff; auto.
            rewrite <- DictIndexImpl.value_eqb_iff_eq, Bool.not_true_iff_false in *;
              eauto using value_eqb_sym. }
      Qed.

      Instance composite_dict_idx : IndexInterface.index :=
        IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

      Instance composite_dict_idx_ok : IndexInterface.ok composite_dict_idx idx_wf :=
        IndexInterface.Build_ok composite_dict_idx idx_wf idx_ty_wf to_idx_ty to_idx_wf.


      (* ============================================================
         MAINTENANCE: one inserted row, one insert.

         The install leaves `to_idx (row :: rest)` on the write path.  This
         rule turns it into "build the index of the tail, then insert the one
         row", which is the fold's own step -- and its OUTPUT REUSES THE
         MATCHED BODY VERBATIM, in the environment the matched term typed it
         in.

         The index's key is a record literal COMPUTED from attrs, so a pattern
         cannot bind it positionally; keys_match checks it instead. *)

      (* and the whole fold, which is the index the interpreter builds *)
      Lemma interp_cidx_fold :
        forall (store env : locals) tup0 acc0 x0 kl_i kl_l l,
          acc0 <> tup0 -> x0 <> tup0 -> x0 <> acc0 ->
          keys_match tup0 attrs kl_i = true ->
          keys_match tup0 attrs kl_l = true ->
          Forall (fun v => exists rc, v = VRecord rc) l ->
          fold_right
            (fun v a => interp_expr store (map.put (map.put env tup0 v) acc0 a)
               (ETernop OInsert (EVar acc0) (ERecord kl_i)
                  (EBinop OBagInsert
                     (EOptMatch (EBinop OLookup (EVar acc0) (ERecord kl_l))
                        (EAtom (AEmptyBag None)) x0 (EVar x0))
                     (EVar tup0))))
            (VDict nil) l
          = VDict (fold_right cidx_step nil l).
      Proof.
        intros store env tup0 acc0 x0 kl_i kl_l l H_at H_xt H_xa H_km_i H_km_l.
        induction l as [| v l IH]; cbn [fold_right]; intros H_rec;
          [ reflexivity | ].
        invert_Forall.
        lazymatch goal with H : exists _, v = VRecord _ |- _ =>
          destruct H as [ rc -> ] end.
        rewrite IH by assumption.
        apply interp_cidx_body; try assumption.
        unfold cidx_step. apply DictIndexImpl.bidx_fold_acc_wf; assumption.
      Qed.
      Notation ecomposite_to_idx tup0 tup1 acc0 acc1 acc2 x0 x1 kl0 kl1 d :=
        (EFold d (EAtom (AEmptyDict Unranged None)) tup0 acc0
           (ETernop OInsert (EVar acc1) (ERecord kl0)
              (EBinop OBagInsert
                 (EOptMatch (EBinop OLookup (EVar acc2) (ERecord kl1))
                    (EAtom (AEmptyBag None)) x0 (EVar x1))
                 (EVar tup1)))).

      Definition cons_to_composite_insert_head (e : expr) :=
        match e with
        | ecomposite_to_idx tup0 tup1 acc0 acc1 acc2 x0 x1 kl0 kl1
            (EBinop OCons e1 e2) =>
            let body :=
              ETernop OInsert (EVar acc0) (ERecord kl0)
                (EBinop OBagInsert
                   (EOptMatch (EBinop OLookup (EVar acc0) (ERecord kl1))
                      (EAtom (AEmptyBag None)) x0 (EVar x0))
                   (EVar tup0)) in
            if (all_eqb [(acc0, [acc1; acc2]); (tup0, [tup1]); (x0, [x1])]
                && all_neqb [acc0; tup0; x0]
                && keys_match tup0 attrs kl0
                && keys_match tup0 attrs kl1
                && negb (free_immut_in tup0 e2))%bool
            then
              ELet e1 tup0
                (ELet (EFold e2 (EAtom (AEmptyDict Unranged None)) tup0 acc0 body)
                   acc0 body)
            else e
        | _ => e
        end.



      (* With at least one key attribute, the key literal's own typing forces
         the row type to be a record: EAccess has a record subject or it has
         nothing.  This is what the rule's non-empty check buys, and the only
         reason it is needed. *)
      Lemma keys_match_forces_record :
        forall (Gstore Genv : tenv) tup0 al kl t_key,
          al <> [] ->
          keys_match tup0 al kl = true ->
          type_of Gstore Genv (ERecord kl) t_key ->
          exists rt, map.get Genv tup0 = Some (TRecord rt).
      Proof.
        intros * H_ne H_km H_t.
        destruct al as [ | a0 al' ]; [ congruence | ].
        apply keys_match_eq in H_km; subst kl.
        inversion H_t; subst. cbn [List.map] in *.
        lazymatch goal with
          H : Forall2 _ (_ :: _) _ |- _ => inversion H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EAccess (EVar _) _) _ |- _ => inversion H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EVar _) _ |- _ => inversion H; subst
        end.
        eexists; eassumption.
      Qed.
      (* ----------------------------------------------------------------
         The composite dictionary's APPEND, normalised into its CONS.

         One rewrite, after which cons_to_composite_insert_head above does
         the maintenance unchanged -- the division of labour the attribute
         dictionary gets from snoc_to_cons_in_idx_head and the four
         aggregates get from snoc_to_cons_under_coercion.

         What licenses it is that this index's fold is the attribute
         dictionary's fold at a RECORD key, so the commutation is that one's
         lemma instantiated (gallina_to_idx_app_singleton above) rather than
         a second proof. *)
      Definition snoc_to_cons_in_cidx_head (e : expr) :=
        match e with
        | ecomposite_to_idx tup0 tup1 acc0 acc1 acc2 x0 x1 kl0 kl1
            (EBinop OConcat e2 (EBinop OCons e1 (EAtom (ANil _)))) =>
            (* The attribute list is tested FIRST so that an empty one
               reduces the whole guard to false by iota alone, which is what
               lets the proofs dispatch that case in one step. *)
            if (negb (Nat.eqb (List.length attrs) O)
                && all_eqb [(acc0, [acc1; acc2]); (tup0, [tup1]); (x0, [x1])]
                && all_neqb [acc0; tup0; x0]
                && keys_match tup0 attrs kl0
                && keys_match tup0 attrs kl1
                (* AT LEAST ONE key attribute, and the reason is not
                   fussiness.  The commutation this rule rests on is a fact
                   about gallina_to_idx, whose step returns nil on a row that
                   is not a record, while the interpreter's body inserts such
                   a row at a degenerate key -- so the bridge between them
                   needs the rows to BE records.  The only thing that says so
                   here is the key literal's own typing, since EAccess forces
                   its subject to be a record, and with no attributes there is
                   no EAccess to force it.  is_tbl_ty admits attrs = [], so
                   this is checked rather than assumed; an index on no
                   attributes buckets every row under one key and serves
                   nothing, so declining it costs nothing. *))%bool
            then ecomposite_to_idx tup0 tup1 acc0 acc1 acc2 x0 x1 kl0 kl1
                   (EBinop OCons e1 e2)
            else e
        | _ => e
        end.

      Lemma snoc_to_cons_in_cidx_head_preserve_ty : forall (Gstore : tenv),
          preserve_ty Gstore snoc_to_cons_in_cidx_head.
      Proof.
        unfold preserve_ty; intros Gstore e t Genv Hgs Hge He.
        unfold snoc_to_cons_in_cidx_head.
        repeat (case_match; auto; []).
        invert_type_of_clear.
        lazymatch goal with
          H : type_of _ _ (EBinop OConcat _ _) _ |- _ => inversion H; clear H; subst
        end.
        invert_type_of_op_clear.
        lazymatch goal with
          H : type_of _ _ (EBinop OCons _ _) _ |- _ => inversion H; clear H; subst
        end.
        invert_type_of_op_clear.
        eapply TyEFold; [ | eassumption | eassumption ].
        eapply TyEBinop; [ apply TyOCons | eassumption | eassumption ].
      Qed.

      Lemma snoc_to_cons_in_cidx_head_preserve_sem :
        forall (Gstore : tenv) (store : locals),
          preserve_sem Gstore store snoc_to_cons_in_cidx_head.
      Proof.
        unfold preserve_sem; intros Gstore store e t Genv env Hgs Hge He Hsw Hew.
        unfold snoc_to_cons_in_cidx_head.
        repeat (case_match; auto; []).
        cbn [all_eqb all_eqb' all_neqb all_neqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        repeat (rewrite eqb_eq in *; subst).
        rewrite !Bool.negb_true_iff in *.
        (* the guard's distinctness, as disequalities rather than booleans *)
        rewrite !eqb_neq in *.
        invert_type_of_clear.
        lazymatch goal with
          H : type_of _ _ (EBinop OConcat _ _) _ |- _ => inversion H; clear H; subst
        end.
        invert_type_of_op_clear.
        lazymatch goal with
          H : type_of _ _ (EBinop OCons _ _) _ |- _ => inversion H; clear H; subst
        end.
        invert_type_of_op_clear.
        (* The row type is a RECORD, forced by the key literal.  The single-
           attribute dictionary gets this for free, because its key is an
           EAccess directly; here the key is a record literal, which forces
           nothing when it is empty -- hence the rule's non-empty check. *)
        lazymatch goal with
          H : type_of _ _ (ETernop OInsert _ (ERecord _) _) _ |- _ =>
            pose proof H as H_body; inversion H; subst
        end.
        assert (H_attrs : attrs <> []).
        1:{ intro H_nil.
            lazymatch goal with
            | H : Nat.eqb (List.length attrs) O = false |- _ =>
                rewrite H_nil in H; cbn in H; discriminate
            | H : negb (Nat.eqb (List.length attrs) O) = true |- _ =>
                rewrite H_nil in H; cbn in H; discriminate
            end. }
        lazymatch goal with
        | H : type_of _ _ (ERecord _) _, H_km : keys_match _ attrs _ = true |- _ =>
            destruct (keys_match_forces_record _ _ _ _ _ _ H_attrs H_km H)
              as [ rt H_g ]
        end.
        rewrite map.get_put_diff in H_g by congruence.
        rewrite map.get_put_same in H_g. do_injection; subst.
        (* the table's rows, and the row being appended *)
        apply_type_sound e0_4. invert_type_of_value_clear.
        apply_type_sound e0_6. invert_type_of_value_clear.
        (* record-ness of each of the two lists the folds run over *)
        assert (H_rec : Forall (fun w => exists rc, w = VRecord rc) l1).
        1:{ eapply Forall_impl; [ | exact H5 ].
            intros w H_w. inversion H_w; subst; eauto. }
        assert (H_cons : Forall (fun w => exists rc, w = VRecord rc)
                           (VRecord l2 :: l1))
          by (constructor; [ eauto | exact H_rec ]).
        assert (H_app : Forall (fun w => exists rc, w = VRecord rc)
                          (l1 ++ [VRecord l2])).
        1:{ rewrite Forall_forall in H_rec |- *. intros w H_in.
            apply in_app_or in H_in.
            destruct H_in as [ H_in | H_in ]; [ apply H_rec; exact H_in | ].
            destruct H_in as [ H_eq | [] ]; subst; eauto. }
        rewrite !interp_EFold_peel, !interp_EBinop, !interp_EAtom_peel.
        rewrite <- H, <- H3. cbn [interp_atom interp_binop].
        rewrite !interp_cidx_fold by (first [ assumption | congruence ]).
        f_equal. symmetry. unfold cidx_step.
        apply DictIndexImpl.bidx_fold_app_singleton; assumption.
      Qed.
      Lemma cons_to_composite_insert_head_preserve_ty : forall (Gstore : tenv),
          preserve_ty Gstore cons_to_composite_insert_head.
      Proof.
        unfold preserve_ty; intros Gstore e t Genv Hgs Hge He.
        unfold cons_to_composite_insert_head.
        repeat (case_match; auto; []).
        cbn [all_eqb all_eqb' all_neqb all_neqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        rewrite !Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        (* the matched fold's three sub-derivations, and the cons's two.  The
           inversions are aimed: invert_type_of_clear picks whichever shape it
           finds first, and the fold leaves three to choose from. *)
        invert_type_of_clear.
        lazymatch goal with
          H : type_of _ _ (EBinop OCons _ _) _ |- _ => inversion H; clear H; subst
        end.
        invert_type_of_op_clear.
        eapply TyELet; [ eassumption | ].
        eapply TyELet.
        - eapply TyEFold.
          + eapply not_free_immut_put_ty2; eassumption.
          + eapply not_free_immut_put_ty2; [ reflexivity | eassumption ].
          + rewrite Properties.map.put_put_same. eassumption.
        - eassumption.
      Qed.

      Lemma cons_to_composite_insert_head_preserve_sem :
        forall (Gstore : tenv) (store : locals),
          preserve_sem Gstore store cons_to_composite_insert_head.
      Proof.
        unfold preserve_sem; intros Gstore store e t Genv env Hgs Hge He Hsw Hew.
        unfold cons_to_composite_insert_head.
        repeat (case_match; auto; []).
        cbn [all_eqb all_eqb' all_neqb all_neqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        rewrite !Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        invert_type_of_clear.
        lazymatch goal with
          H : type_of _ _ (EBinop OCons _ _) _ |- _ => inversion H; clear H; subst
        end.
        invert_type_of_op_clear.
        lazymatch goal with
          H : type_of Gstore Genv ?b (TList _) |- _ => apply_type_sound b
        end.
        invert_type_of_value_clear.
        assert (E_Let : forall (env' : locals) a b x0,
                   interp_expr store env' (ELet a x0 b)
                   = interp_expr store (map.put env' x0 (interp_expr store env' a)) b)
          by reflexivity.
        rewrite !E_Let.
        (* THE STEP THAT MAKES THIS CHEAP.  The inner fold BINDS the row name
           itself, so the outer let's binding of that name cannot reach it and
           the fold has the same value in either environment. *)
        erewrite <- (not_free_immut_put_sem (EFold _ _ _ _ _))
          by (cbn [free_immut_in]; rewrite String.eqb_refl; cbn [negb andb];
              rewrite !Bool.orb_false_r; assumption).
        cbn [interp_expr interp_binop].
        lazymatch goal with
          H : VList ?l2 = interp_expr store env ?b |- _ => rewrite <- H
        end.
        cbn [fold_right]. reflexivity.
      Qed.

      Lemma snoc_to_cons_in_cidx_head_sound :
        expr_transf_sound (locals:=locals) snoc_to_cons_in_cidx_head.
      Proof.
        unfold expr_transf_sound; split; intros.
        1: eapply snoc_to_cons_in_cidx_head_preserve_ty; eauto.
        eapply snoc_to_cons_in_cidx_head_preserve_sem;
          resolve_locals_wf; eauto.
      Qed.

      Lemma cons_to_composite_insert_head_sound :
        expr_transf_sound (locals:=locals) cons_to_composite_insert_head.
      Proof.
        unfold expr_transf_sound; split; intros.
        1: eapply cons_to_composite_insert_head_preserve_ty; eauto.
        eapply cons_to_composite_insert_head_preserve_sem;
          resolve_locals_wf; eauto.
      Qed.

      Lemma Forall_VRecord_of_list : forall (l : list value) rt,
          type_of_value (VList l) (TList (TRecord rt)) ->
          Forall (fun v => exists rc, v = VRecord rc) l.
      Proof.
        intros l rt H. invert_type_of_value_clear.
        lazymatch goal with
          HF: Forall _ ?ll |- Forall _ ?ll => eapply Forall_impl; [ | exact HF ]
        end.
        intros v Hv; cbn beta in Hv.
        invert_type_of_value_clear. eexists; reflexivity.
      Qed.

      (* THE BRIDGE the read rule runs over.  What the conjunction computes on
         a row is exactly the test idx_chara filters by: whether the row's
         composite key equals the key the probe builds.  The right-hand sides
         are evaluated OUTSIDE the row binder, which is what the matcher's
         per-conjunct freshness condition buys. *)
      (* interp of an ERecord canonicalises with record_sort over exactly this
         map, so the key the probe computes is stated in the same form the
         interpreter produces. *)
      Lemma map_fst_interp_pairs :
        forall (store env : locals) (prs : list (string * expr)),
          List.map fst (List.map (fun '(s, e) => (s, interp_expr store env e)) prs)
          = List.map fst prs.
      Proof.
        induction prs as [ | [ s e ] prs IH ]; cbn; congruence.
      Qed.

      (* THE BRIDGE the read rule runs over.  What the conjunction computes on
         a row is exactly the test idx_chara filters by: whether the row's
         composite key equals the key the probe builds.  The right-hand sides
         are evaluated OUTSIDE the row binder, which is what the matcher's
         per-conjunct freshness condition buys. *)
      Lemma conj_sat_eq_ckey : forall (store env : locals) rc prs,
          NoDup attrs ->
          Permutation (List.map fst prs) attrs ->
          conj_sat store env rc prs
          = value_eqb (ckey rc)
              (VRecord (record_sort
                 (List.map (fun '(s, e) => (s, interp_expr store env e)) prs))).
      Proof.
        intros store env rc prs Hnd Hperm.
        apply Bool.eq_iff_eq_true.
        rewrite DictIndexImpl.value_eqb_iff_eq.
        rewrite ckey_eq_iff;
          [ | assumption | rewrite map_fst_interp_pairs; assumption ].
        unfold conj_sat. rewrite forallb_forall, Forall_map, Forall_forall.
        split; intros H q Hq; specialize (H q Hq);
          destruct q as [ s e ]; cbn [fst snd] in *.
        - rewrite <- DictIndexImpl.value_eqb_iff_eq; assumption.
        - rewrite DictIndexImpl.value_eqb_iff_eq; assumption.
      Qed.

      (* The filter the SOURCE performs and the filter idx_chara describes are
         the same filter. *)
      Lemma filter_conj_eq_filter_ckey :
        forall (store env : locals) x0 pr prs (l : list value),
          NoDup attrs ->
          conj_eq_pairs x0 pr = Some prs ->
          Permutation (List.map fst prs) attrs ->
          Forall (fun v => exists rc, v = VRecord rc) l ->
          filter (fun v => match interp_expr store (map.put env x0 v) pr with
                           | VBool bb => bb
                           | _ => false
                           end) l
          = filter (fun v => match v with
                             | VRecord rc =>
                                 value_eqb (ckey rc)
                                   (VRecord (record_sort
                                      (List.map
                                         (fun '(s, e) => (s, interp_expr store env e))
                                         prs)))
                             | _ => false
                             end) l.
      Proof.
        intros store env x0 pr prs l Hnd Hm Hperm Hrec.
        apply In_filter_ext; intros v Hin.
        rewrite Forall_forall in Hrec. apply Hrec in Hin as [ rc -> ].
        pose proof (interp_conj_eq_pairs store env x0 pr rc) as Hi.
        rewrite Hm in Hi; cbv beta iota in Hi. rewrite Hi.
        apply conj_sat_eq_ckey; assumption.
      Qed.

      (* The NEGATED bridge, for the delete: what `not (conjunction)` computes
         on a row is that the row's composite key DIFFERS from the probe's. *)
      Lemma filter_not_conj_eq_filter_neq_ckey :
        forall (store env : locals) x0 pr prs (l : list value),
          NoDup attrs ->
          conj_eq_pairs x0 pr = Some prs ->
          Permutation (List.map fst prs) attrs ->
          Forall (fun v => exists rc, v = VRecord rc) l ->
          filter (fun v => match interp_expr store (map.put env x0 v)
                                   (EUnop ONot pr) with
                           | VBool bb => bb
                           | _ => false
                           end) l
          = filter (fun r => negb (value_eqb
                                     (match r with
                                      | VRecord rc => ckey rc
                                      | _ => VUnit
                                      end)
                                     (VRecord (record_sort
                                        (List.map
                                           (fun '(s, e) => (s, interp_expr store env e))
                                           prs))))) l.
      Proof.
        intros store env x0 pr prs l Hnd Hm Hperm Hrec.
        apply In_filter_ext; intros v Hin.
        rewrite Forall_forall in Hrec. apply Hrec in Hin as [ rc -> ].
        pose proof (interp_conj_eq_pairs store env x0 pr rc) as Hi.
        rewrite Hm in Hi; cbv beta iota in Hi.
        cbn [interp_expr]. rewrite Hi. cbn [interp_unop].
        f_equal. apply conj_sat_eq_ckey; assumption.
      Qed.

      (* ============================================================
         MAINTENANCE: a key's rows removed, one delete.

         [row <- e', check(!(row.a1 == e1 && ... && row.an == en)), ret row]
         rebuilt into an index  -->  delete {a1 = e1; ...} from the index of e'

         The same shape as DictIndexImpl's filter_neq_to_delete_head, and the
         same conjunction matcher as the read rule, so the predicate may be
         written in any order and any association.  Its content is
         gallina_to_idx_filter_neq; the rest is plumbing.

         Paired with composite_use_idx_head as the insert rule is: this leaves
         `index of e'` behind, and that rule replaces it with the member
         already stored, which is what makes the delete O(log n) instead of a
         rebuild. *)
      Definition filter_neq_to_composite_delete_head (e : expr) :=
        match e with
        | ecomposite_to_idx tup0 tup1 acc0 acc1 acc2 x0 x1 kl0 kl1
            (flatmap_filter_list e' y (EUnop ONot pr) y1 _ _) =>
            match conj_eq_pairs y pr with
            | Some prs =>
                if (all_eqb [(tup, [tup0; tup1]); (acc, [acc0; acc1; acc2]);
                             (x, [x0; x1]); (y, [y1])]
                    && keys_match tup0 attrs kl0
                    && keys_match tup0 attrs kl1
                    && forallb (fun a => inb String.eqb a (List.map fst prs))
                         attrs
                    && Nat.eqb (List.length attrs) (List.length prs)
                    (* a key of NO attributes would leave the row type
                       unconstrained, and the row type is what the key's own
                       typing is read out of *)
                    && negb (Nat.eqb (List.length attrs) 0))%bool
                then EBinop ODelete (to_idx_from e') (ERecord prs)
                else e
            | None => e
            end
        | _ => e
        end.

      Lemma filter_neq_to_composite_delete_head_preserve_ty : forall (Gstore : tenv),
          preserve_ty Gstore filter_neq_to_composite_delete_head.
      Proof.
        unfold preserve_ty; intros Gstore e t' Genv Hgs Hge He.
        unfold filter_neq_to_composite_delete_head.
        repeat (case_match; auto; []).
        (* The guard, and the typing inversions down to the key literal.
           Inlined in both halves rather than factored into an Ltac: the
           names an intro-pattern introduces inside an Ltac body are not
           available to the caller, and preserve_ty needs two of them. *)
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *.
        repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
        rewrite !Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        lazymatch goal with
          H : keys_match _ _ ?kl = true |- _ => apply keys_match_eq in H; subst kl
        end.
        lazymatch goal with
          H : keys_match _ _ ?kl = true |- _ => apply keys_match_eq in H; subst kl
        end.
        invert_type_of_clear.
        lazymatch goal with
          H : type_of _ _ (EFlatmap _ _ _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EIf _ _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EBinop OCons _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_binop OCons _ _ _ |- _ => inversion H; clear H; subst
        end.
        (* the filter's INPUT row type is its OUTPUT row type *)
        lazymatch goal with
          H : type_of _ (map.put _ ?yy _) (EVar ?yy) _ |- _ =>
            apply EVar_ty_inv in H; rewrite map.get_put_same in H;
            injection H as H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EUnop ONot _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_unop ONot _ _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ (map.put (map.put _ _ _) _ _) (ETernop OInsert _ _ _) _
          |- _ => pose proof H as Hbody; inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_ternop OInsert _ _ _ _ |- _ => inversion H; clear H; subst
        end.
        assert (Hne : attrs <> []).
        { apply attrs_nonempty with (A := string).
          lazymatch goal with
            H : Nat.eqb (List.length attrs) 0 = false |- _ => exact H
          end. }
        (* the key literal gives the row type, the side condition and the key
           type in one step *)
        lazymatch goal with
          H : type_of ?Gs (map.put (map.put ?Ge ?tp ?rowt) ?ac ?D)
                (ERecord (List.map (fun a => (a, EAccess (EVar ?tp) a)) attrs))
                ?kt |- _ =>
            pose proof (key_lit_inv_ex Gs _ tp kt Hne H)
              as [ rt [ Hgt [ Htbl Hkt ] ] ]
        end.
        rewrite map.get_put_diff in Hgt by use_is_NoDup.
        rewrite map.get_put_same in Hgt.
        injection Hgt as Hgt; subst.
        pose proof (is_tbl_ty_attrs _ Htbl) as [ _ Hndattrs ].
        lazymatch goal with
          H1 : forallb _ _ = true,
          H2 : Nat.eqb (List.length attrs) (List.length _) = true |- _ =>
            pose proof (guard_Permutation _ Hndattrs H1 H2) as Hperm
        end.
        subst. eapply TyEBinop; [ apply TyODelete | | ].
        - (* the same fold, over the filter's SOURCE: its three
             sub-derivations are the matched term's own *)
          unfold to_idx_from, composite_key.
          eapply TyEFold; [ eassumption | eassumption | exact Hbody ].
        - lazymatch goal with
            H : type_of ?Gs (map.put ?Ge ?yy (TRecord ?rt0)) ?pr TBool |- _ =>
              pose proof (conj_eq_pairs_ty Gs Ge yy pr rt0 TBool H) as Hprs
          end.
          lazymatch goal with
            H : conj_eq_pairs _ _ = Some _ |- _ =>
              rewrite H in Hprs; cbv beta iota in Hprs
          end.
          apply composite_key_expr_ty;
            [ assumption | exact Hperm | apply Forall2_of_pairs_ty; assumption ].
      Qed.

      Lemma filter_neq_to_composite_delete_head_preserve_sem :
        forall (Gstore : tenv) (store : locals),
          preserve_sem Gstore store filter_neq_to_composite_delete_head.
      Proof.
        unfold preserve_sem; intros Gstore store e t' Genv env Hgs Hge He Hsw Hew.
        unfold filter_neq_to_composite_delete_head.
        repeat (case_match; auto; []).
        (* The guard, and the typing inversions down to the key literal.
           Inlined in both halves rather than factored into an Ltac: the
           names an intro-pattern introduces inside an Ltac body are not
           available to the caller, and preserve_ty needs two of them. *)
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *.
        repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
        rewrite !Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        lazymatch goal with
          H : keys_match _ _ ?kl = true |- _ => apply keys_match_eq in H; subst kl
        end.
        lazymatch goal with
          H : keys_match _ _ ?kl = true |- _ => apply keys_match_eq in H; subst kl
        end.
        invert_type_of_clear.
        lazymatch goal with
          H : type_of _ _ (EFlatmap _ _ _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EIf _ _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EBinop OCons _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_binop OCons _ _ _ |- _ => inversion H; clear H; subst
        end.
        (* the filter's INPUT row type is its OUTPUT row type *)
        lazymatch goal with
          H : type_of _ (map.put _ ?yy _) (EVar ?yy) _ |- _ =>
            apply EVar_ty_inv in H; rewrite map.get_put_same in H;
            injection H as H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EUnop ONot _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_unop ONot _ _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ (map.put (map.put _ _ _) _ _) (ETernop OInsert _ _ _) _
          |- _ => pose proof H as Hbody; inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_ternop OInsert _ _ _ _ |- _ => inversion H; clear H; subst
        end.
        assert (Hne : attrs <> []).
        { apply attrs_nonempty with (A := string).
          lazymatch goal with
            H : Nat.eqb (List.length attrs) 0 = false |- _ => exact H
          end. }
        (* the key literal gives the row type, the side condition and the key
           type in one step *)
        lazymatch goal with
          H : type_of ?Gs (map.put (map.put ?Ge ?tp ?rowt) ?ac ?D)
                (ERecord (List.map (fun a => (a, EAccess (EVar ?tp) a)) attrs))
                ?kt |- _ =>
            pose proof (key_lit_inv_ex Gs _ tp kt Hne H)
              as [ rt [ Hgt [ Htbl Hkt ] ] ]
        end.
        rewrite map.get_put_diff in Hgt by use_is_NoDup.
        rewrite map.get_put_same in Hgt.
        injection Hgt as Hgt; subst.
        pose proof (is_tbl_ty_attrs _ Htbl) as [ _ Hndattrs ].
        lazymatch goal with
          H1 : forallb _ _ = true,
          H2 : Nat.eqb (List.length attrs) (List.length _) = true |- _ =>
            pose proof (guard_Permutation _ Hndattrs H1 H2) as Hperm
        end.
        (* the filter's source, as a list of rows *)
        lazymatch goal with
          H : type_of Gstore Genv ?src (TList _) |- _ => apply_type_sound src
        end.
        lazymatch goal with
          H : type_of_value _ (TList _) |- _ => inversion H; subst
        end.
        (* the row type is well formed, which the index's own lemmas want *)
        assert (Hrt : type_wf (TRecord rt)).
        { lazymatch goal with
            H : type_of Gstore Genv _ (TList (TRecord rt)) |- _ =>
              apply type_of__type_wf in H as Hwf0; auto;
              inversion Hwf0; subst; assumption
          end. }
        assert (E_Binop : forall o a b,
                   interp_expr store env (EBinop o a b)
                   = interp_binop o (interp_expr store env a)
                       (interp_expr store env b)) by reflexivity.
        (* The matched term is the fold, not the constant to_idx_from applied
           to it, so the right-hand side is matched as a fold and the lemma
           about to_idx_from is unfolded into that shape before it is used. *)
        lazymatch goal with
          Hrows : Forall _ ?rows,
          Hsrc : VList ?rows = interp_expr store env ?src |- _ =>
            lazymatch goal with
              |- interp_expr store env
                   (EBinop ODelete (to_idx_from _) (ERecord ?prs))
                 = interp_expr store env (EFold ?flt _ _ _ _) =>
                (* the index of the whole table *)
                assert (Hidx : interp_expr store env (to_idx_from src)
                               = gallina_to_idx (VList rows))
                  by (eapply interp_to_idx_from with (l := rt);
                      [ assumption | assumption | assumption
                      | symmetry; exact Hsrc ]);
                (* the rows the filter keeps, as the delete's own test *)
                assert (Hfl : interp_expr store env flt
                              = VList (filter (fun r => negb (value_eqb
                                   (match r with
                                    | VRecord rc => ckey rc
                                    | _ => VUnit
                                    end)
                                   (VRecord (record_sort (List.map
                                      (fun '(s, e) => (s, interp_expr store env e))
                                      prs))))) rows))
                  by (rewrite interp_flatmap_filter_list, <- Hsrc;
                      cbv beta iota; f_equal;
                      apply filter_not_conj_eq_filter_neq_ckey;
                      [ assumption | eassumption | assumption
                      | apply (Forall_VRecord_of_list rows rt);
                        constructor; assumption ]);
                (* and the index of those rows *)
                assert (Hfidx : interp_expr store env (to_idx_from flt)
                                = gallina_to_idx
                                    (VList (filter (fun r => negb (value_eqb
                                       (match r with
                                        | VRecord rc => ckey rc
                                        | _ => VUnit
                                        end)
                                       (VRecord (record_sort (List.map
                                          (fun '(s, e) => (s, interp_expr store env e))
                                          prs))))) rows)))
                  by (eapply interp_to_idx_from with (l := rt);
                      [ assumption | assumption
                      | rewrite Forall_forall; intros v Hv;
                        apply filter_In in Hv as [ Hv _ ];
                        rewrite Forall_forall in Hrows; apply Hrows; assumption
                      | exact Hfl ]);
                unfold to_idx_from, composite_key in Hfidx;
                rewrite E_Binop, Hidx, Hfidx;
                erewrite (gallina_to_idx_filter_neq rows rt);
                  [ | constructor; assumption ]
            end
        end.
        cbn [interp_expr gallina_to_idx interp_binop]. reflexivity.
      Qed.

      Lemma filter_neq_to_composite_delete_head_sound :
        expr_transf_sound (locals:=locals) filter_neq_to_composite_delete_head.
      Proof.
        unfold expr_transf_sound; split; intros.
        1: eapply filter_neq_to_composite_delete_head_preserve_ty; eauto.
        eapply filter_neq_to_composite_delete_head_preserve_sem;
          resolve_locals_wf; eauto.
      Qed.

      Section WithTags.
        Context (id_tag aux_tag idx_tag : string).

        Notation aux_ty_for_idx := (aux_ty_for_idx id_tag aux_tag idx_tag idx_ty).
        Notation aux_wf_for_idx := (aux_wf_for_idx id_tag aux_tag idx_tag idx_wf).

        (* ============================================================
           USE THE INDEX YOU ALREADY HAVE.

           cons_to_composite_insert_head leaves `to_idx (tbl[id_tag])` on the
           write path -- the index of the table BEFORE the insert -- and
           rebuilding that is exactly the cost the maintenance rule was meant
           to remove.  This replaces it with the stored member, which is sound
           because aux_wf_for_idx says the member IS that index.  Without this
           rule the insert rule buys nothing, which is why they are registered
           together.

           The binder names are required to be the index's own, unlike
           DictIndexImpl's version which accepts any and pays for the
           generality with an alpha-invariance argument (fold_to_idx).  The
           install only ever emits the index's own names, so the generality
           has no customer here. *)
        Section composite_use_idx.
          Context (tbl : string).

          Definition composite_use_idx_head (e : expr) :=
            match e with
            | ecomposite_to_idx tup0 tup1 acc0 acc1 acc2 x0 x1 kl0 kl1
                (EAccess (ELoc tbl0) id_tag0) =>
                if (all_eqb [(tbl, [tbl0]); (id_tag, [id_tag0]);
                             (tup, [tup0; tup1]); (acc, [acc0; acc1; acc2]);
                             (x, [x0; x1])]
                    && keys_match tup0 attrs kl0
                    && keys_match tup0 attrs kl1)%bool
                then EAccess (EAccess (ELoc tbl) aux_tag) idx_tag
                else e
            | _ => e
            end.

          Lemma composite_use_idx_head_preserve_ty :
            forall tl t aux_tl (Gstore : tenv),
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              preserve_ty Gstore composite_use_idx_head.
          Proof.
            unfold preserve_ty; intros tl t aux_tl Gstore Hwf Htbl Hget Hid Haux Hidx.
            assert (Htbl' := Htbl). unfold is_tbl_ty in Htbl.
            repeat destruct_match_hyp; try congruence.
            intros e t' Genv Hgs Hge He.
            unfold composite_use_idx_head.
            repeat (case_match; auto; []).
            cbn [all_eqb all_eqb' andb] in *.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            repeat (rewrite eqb_eq in *; subst).
            lazymatch goal with
              H : keys_match _ _ ?kl = true |- _ =>
                apply keys_match_eq in H; subst kl
            end.
            lazymatch goal with
              H : keys_match _ _ ?kl = true |- _ =>
                apply keys_match_eq in H; subst kl
            end.
            (* the fold's three sub-derivations, then the insert's, which is
               what pins the dictionary's key and value types *)
            invert_type_of_clear.
            lazymatch goal with
              H : type_of _ _ (ETernop OInsert _ _ _) _ |- _ =>
                inversion H; clear H; subst
            end.
            invert_type_of_op_clear.
            (* the collection is the table's own row list, so the fold's row
               type is the table's row type *)
            lazymatch goal with
              H : type_of _ _ (EAccess (ELoc tbl) id_tag) _ |- _ =>
                inversion H; clear H; subst
            end.
            lazymatch goal with
              H : type_of _ _ (ELoc tbl) _ |- _ => inversion H; subst
            end.
            lazymatch goal with
              H : type_of ?Gs (map.put (map.put ?Ge ?tp ?rowt) ?ac ?D)
                    (ERecord (List.map (fun a => (a, EAccess (EVar ?tp) a)) attrs))
                    ?kt |- _ =>
                assert (Hrow : rowt = TRecord l) by congruence;
                rewrite Hrow in *;
                assert (Hgt : map.get (map.put (map.put Ge tp (TRecord l)) ac D) tp
                              = Some (TRecord l))
                  by (rewrite map.get_put_diff, map.get_put_same;
                      [ reflexivity | use_is_NoDup ]);
                pose proof (key_lit_inv Gs _ tp l kt Hgt H) as [ _ Hkt ]
            end.
            (* the dictionary's KIND, from the fold's initial value *)
            lazymatch goal with
              H : type_of _ _ (EAtom (AEmptyDict _ _)) _ |- _ =>
                inversion H; clear H; subst
            end.
            lazymatch goal with
              H : type_of_atom (AEmptyDict _ _) _ |- _ =>
                inversion H; clear H; subst
            end.
            (* and its VALUE type, from the bag insert on the row *)
            lazymatch goal with
              H : type_of _ _ (EBinop OBagInsert _ (EVar _)) _ |- _ =>
                inversion H; clear H; subst
            end.
            lazymatch goal with
              H : type_of_binop OBagInsert _ _ _ |- _ =>
                inversion H; clear H; subst
            end.
            (* the bag's element type is the ROW type: the row is what the
               insert inserts. *)
            lazymatch goal with
              H : type_of _ (map.put (map.put _ ?tp _) _ _) (EVar ?tp) _ |- _ =>
                apply EVar_ty_inv in H;
                rewrite map.get_put_diff in H by use_is_NoDup;
                rewrite map.get_put_same in H;
                try (injection H as H); subst
            end.
            subst. cbn [idx_ty] in Hidx |- *.
            eapply TyEAccess; [ | exact Hidx ].
            eapply TyEAccess; [ | exact Haux ].
            apply TyELoc. exact Hget.
          Qed.

          Lemma composite_use_idx_head_preserve_sem :
            forall (Gstore : tenv) (store : locals) tl t aux_tl,
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              match map.get store tbl with
              | Some v => aux_wf_for_idx v
              | _ => False
              end ->
              preserve_sem Gstore store composite_use_idx_head.
          Proof.
            unfold preserve_sem, aux_wf_for_idx, idx_wf; intros.
            assert (Htbl' : is_tbl_ty t = true) by assumption.
            unfold is_tbl_ty, idx_ty in *.
            apply_locals_wf store.
            repeat (destruct_match_hyp; try discriminate; intuition idtac; []).
            (* the table's row list, and the member that IS its index *)
            assert (Htblv : type_of_value a (TList (TRecord l))).
            { lazymatch goal with
                H : type_of_value (VRecord _) (TRecord tl) |- _ =>
                  inversion H; subst
              end.
              lazymatch goal with
                HF : Forall2 _ _ tl |- _ =>
                  pose proof (Forall2_access_record _ _ _ _ _ _ _ _ HF E3 H2)
              end; auto. }
            inversion Htblv; subst.
            unfold composite_use_idx_head.
            repeat (case_match; auto; []).
            cbn [all_eqb all_eqb' andb] in *.
            repeat rewrite Bool.andb_true_iff in *.
            repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
            repeat (rewrite eqb_eq in *; subst).
            lazymatch goal with
              H : keys_match _ _ ?kl = true |- _ =>
                apply keys_match_eq in H; subst kl
            end.
            lazymatch goal with
              H : keys_match _ _ ?kl = true |- _ =>
                apply keys_match_eq in H; subst kl
            end.
            (* the LEFT side is the index-building fold over the table's own
               row list, which is gallina_to_idx of that list *)
            lazymatch goal with
              Hrows : Forall _ ?rows |- _ =>
                assert (Hlhs : interp_expr store env
                                 (to_idx_from (EAccess (ELoc tbl) id_tag))
                               = gallina_to_idx (VList rows))
            end.
            { eapply interp_to_idx_from with (l := l).
              - lazymatch goal with
                  H : type_wf (TList (TRecord l)) |- _ =>
                    inversion H; subst; assumption
                end.
              (* the guard's conjuncts were destructed above, so the folded
                 side condition is rebuilt from them *)
              - cbn [is_tbl_ty]. rewrite Bool.andb_true_iff.
                split; assumption.
              - eassumption.
              - cbn [interp_expr]. unfold get_local, record_proj.
                rewrite E. cbn. rewrite E3. reflexivity. }
            unfold to_idx_from, composite_key in Hlhs. rewrite Hlhs.
            (* the RIGHT side is the stored member, and aux_wf_for_idx says it
               IS that index *)
            cbn [interp_expr]. unfold get_local, record_proj.
            rewrite E. cbv beta iota. rewrite E4. cbv beta iota. rewrite E6.
            cbv beta iota.
            (* the member's value IS the index *)
            eapply fiat2_gallina_to_idx with (t := TList (TRecord l)).
            - lazymatch goal with
                H : type_wf (TList (TRecord l)) |- _ => exact H
              end.
            - cbn [is_tbl_ty]. rewrite Bool.andb_true_iff. split; assumption.
            - constructor; assumption.
          Qed.

        End composite_use_idx.

        Section composite_eq_filter_to_lookup.
          Context (b : string).
          Context (tbl : string).

          (* [row <- tbl[id_tag], check(row.a1 == e1 && ... && row.an == en),
              ret row]
             --> match lookup idx {a1 = e1; ...; an = en} with
                 | none => emptybag | some b => b

             The pattern is the CONJUNCTION, unsplit, of ANY length, ANY
             association and ANY ORDER -- conj_eq_pairs collects the conjuncts
             and the guard checks that the names it collected are a
             PERMUTATION of the index's attribute list (guard_Permutation).
             Nothing about how the programmer wrote the conjunction has to
             match how the index was declared, and that is not a convenience:
             the stored key record is record_sort'ed, so an index on (a, b) is
             the same index as one on (b, a), and a rule that insisted on one
             order would be insisting on a distinction its own index does not
             make.  record_sort_Permutation_eq is what pays for it.

             WHAT THE GUARD STILL DOES NOT DO, and it is deliberate: it does
             not match a conjunction with an EXTRA conjunct beside the key's
             n.  That read is a probe followed by a residual filter, which is
             a different rule.

             Rule ORDER is an obligation and not an accident: SplitIf peels a
             conjunct off and hands it to an index on its own, after which this
             pattern no longer matches and only part of the key is ever used.
             So this rule must be given its chance before SplitIf, and a
             configuration that lists both without ordering them gets the
             partly-indexed read -- the measured gap this index exists to
             close. *)
          Definition composite_eq_filter_to_lookup_head (e : expr) :=
            match e with
            | flatmap_filter_bag
                (EUnop OBagOfList (EAccess (ELoc tbl0) id_tag0)) x0 pr x3 _ _ =>
                match conj_eq_pairs x0 pr with
                | Some prs =>
                    if (all_eqb [(tbl, [tbl0]); (x0, [x3]); (id_tag, [id_tag0])]
                        && forallb (fun a => inb String.eqb a (List.map fst prs))
                             attrs
                        && Nat.eqb (List.length attrs) (List.length prs))%bool
                    then EOptMatch (EBinop OLookup
                                      (EAccess (EAccess (ELoc tbl) aux_tag) idx_tag)
                                      (ERecord prs))
                           (EAtom (AEmptyBag None))
                           b (EVar b)
                    else e
                | None => e
                end
            | _ => e
            end.

          (* Reading the table and the index out through the tags. *)
          Lemma interp_tbl_bag : forall (store env : locals) rv v,
              map.get store tbl = Some (VRecord rv) ->
              access_record rv id_tag = Success (VList v) ->
              interp_expr store env (EUnop OBagOfList (EAccess (ELoc tbl) id_tag))
              = VBag (list_to_bag v).
          Proof.
            intros store env rv v Hget Hacc.
            cbn [interp_expr]. unfold get_local, record_proj.
            rewrite Hget. cbn. rewrite Hacc. reflexivity.
          Qed.

          (* What the emitted probe computes. *)
          Lemma interp_probe : forall (store env : locals) rv rav d k,
              map.get store tbl = Some (VRecord rv) ->
              access_record rv aux_tag = Success (VRecord rav) ->
              access_record rav idx_tag = Success (VDict d) ->
              interp_expr store env
                (EOptMatch (EBinop OLookup
                              (EAccess (EAccess (ELoc tbl) aux_tag) idx_tag) k)
                   (EAtom (AEmptyBag None)) b (EVar b))
              = match dict_lookup (interp_expr store env k) d with
                | Some w => w
                | None => VBag nil
                end.
          Proof.
            intros store env rv rav d k Hget Haux Hidx.
            cbn [interp_expr]. unfold get_local, record_proj.
            rewrite Hget. cbn. rewrite Haux. cbn. rewrite Hidx. cbn.
            destruct (dict_lookup (interp_expr store env k) d) eqn:E; cbn.
            - unfold get_local. rewrite map.get_put_same. reflexivity.
            - reflexivity.
          Qed.

          Lemma composite_eq_filter_to_lookup_head_preserve_ty :
            forall tl t aux_tl (Gstore : tenv),
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              preserve_ty Gstore composite_eq_filter_to_lookup_head.
          Proof.
            unfold preserve_ty; intros tl t aux_tl Gstore Hwf Htbl Hget Hid Haux Hidx.
            assert (Htbl' := Htbl). unfold is_tbl_ty in Htbl.
            repeat destruct_match_hyp; try congruence.
            intros e t' Genv Hgs Hge He.
            unfold composite_eq_filter_to_lookup_head.
            repeat (case_match; auto; []).
            cbn [all_eqb all_eqb' andb] in *.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            repeat (rewrite eqb_eq in *; subst).
            pose proof (is_tbl_ty_attrs _ Htbl') as [ _ Hndattrs ].
            lazymatch goal with
              H1 : forallb _ _ = true, H2 : Nat.eqb _ _ = true |- _ =>
                pose proof (guard_Permutation _ Hndattrs H1 H2) as Hperm
            end.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear.
            repeat rewrite_map_get_put_hyp.
            repeat (clear_refl; repeat do_injection2).
            repeat (rewrite_l_to_r; do_injection2).
            cbn [idx_ty] in Hidx.
            eapply TyEOptMatch.
            3:{ apply TyEVar. rewrite map.get_put_same. reflexivity. }
            2:{ apply TyEAtom, TyAEmptyBag'. invert_type_wf; assumption. }
            eapply TyEBinop.
            1: apply TyOLookup.
            1:{ eapply TyEAccess.
                2: exact Hidx.
                eapply TyEAccess.
                2: exact Haux.
                apply TyELoc. exact Hget. }
            (* the key: the conjuncts' right-hand sides, typed OUTSIDE the row
               binder -- which is what the matcher's freshness condition buys,
               and the only thing conj_eq_pairs_ty has to say *)
            lazymatch goal with
              H : type_of _ (map.put _ ?x0 (TRecord ?rt0)) ?pr _ |- _ =>
                pose proof (conj_eq_pairs_ty _ _ x0 pr rt0 _ H) as Hprs
            end.
            lazymatch goal with
              H : conj_eq_pairs _ _ = Some _ |- _ =>
                rewrite H in Hprs; cbv beta iota in Hprs
            end.
            apply composite_key_expr_ty;
              [ assumption | exact Hperm | apply Forall2_of_pairs_ty; assumption ].
          Qed.

          Lemma composite_eq_filter_to_lookup_head_preserve_sem :
            forall (Gstore : tenv) (store : locals) tl t aux_tl,
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              match map.get store tbl with
              | Some v => aux_wf_for_idx v
              | _ => False
              end ->
              preserve_sem Gstore store composite_eq_filter_to_lookup_head.
          Proof.
            unfold preserve_sem, aux_wf_for_idx; intros.
            unfold is_tbl_ty, idx_ty in *.
            apply_locals_wf store.
            repeat (destruct_match_hyp; try discriminate; intuition idtac; []).
            (* the distinctness conjunct of is_tbl_ty, which is what the key's
               faithfulness rests on; read out of the unfolded guard so that
               the folded form stays available for idx_wf__idx_chara *)
            assert (Hnd : NoDup attrs).
            { lazymatch goal with
                H : (_ && all_neqb attrs)%bool = true |- _ =>
                  apply all_neqb_NoDup;
                  rewrite Bool.andb_true_iff in H; apply (proj2 H)
              end. }
            (* the table's list and the index's dictionary, with their types *)
            assert (Htblv : type_of_value a (TList (TRecord l1))).
            { invert_type_of_value_clear.
              lazymatch goal with
                HF: Forall2 _ _ tl |- _ =>
                  pose proof (Forall2_access_record _ _ _ _ _ _ _ _ HF E1 H2)
              end; auto. }
            assert (Hidxv : type_of_value a1
                              (TDict Unranged (key_ty l1) (TBag (TRecord l1)))).
            { invert_type_of_value_clear.
              lazymatch goal with
                HF: Forall2 _ _ tl |- _ =>
                  pose proof (Forall2_access_record _ _ _ _ _ _ _ _ HF E2 H3)
              end.
              invert_type_of_value_clear.
              lazymatch goal with
                HF: Forall2 _ _ aux_tl |- _ =>
                  pose proof (Forall2_access_record _ _ _ _ _ _ _ _ HF E4 H4)
              end; auto. }
            assert (Hchara : idx_chara a a1)
              by (eapply idx_wf__idx_chara with (t := TList (TRecord l1)); eauto).
            unfold idx_chara in Hchara.
            repeat (destruct_match_hyp; try discriminate; intuition idtac; []).
            pose proof (Forall_VRecord_of_list _ _ Htblv) as Hrows.
            unfold composite_eq_filter_to_lookup_head.
            repeat (case_match; auto; []).
            cbn [all_eqb all_eqb' andb] in *.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            repeat (rewrite eqb_eq in *; subst).
            lazymatch goal with
              H1 : forallb _ _ = true, H2 : Nat.eqb _ _ = true |- _ =>
                pose proof (guard_Permutation _ Hnd H1 H2) as Hperm
            end.
            (* the SOURCE side: a filter over the table's rows *)
            rewrite interp_flatmap_filter_bag.
            erewrite interp_tbl_bag by eassumption.
            cbv beta iota.
            rewrite list_to_bag_filter_list_to_bag.
            erewrite filter_conj_eq_filter_ckey; try eassumption.
            (* the OPTIMIZED side: one probe *)
            erewrite interp_probe by eassumption.
            cbn [interp_expr].
            lazymatch goal with
              |- context[dict_lookup ?k l3] => specialize (Hchara k)
            end.
            destruct (dict_lookup _ l3) as [ w | ] eqn:Elk.
            - (* the bucket exists; it is a bag, and it is the filtered rows *)
              assert (Hw : type_of_value w (TBag (TRecord l1))).
              { apply DictIndexImpl.dict_lookup_Some_In in Elk.
                clear Htblv. invert_type_of_value_clear.
                lazymatch goal with
                  HF: Forall _ l3 |- _ =>
                    rewrite Forall_forall in HF; apply HF in Elk
                end.
                cbn in Elk; intuition idtac. }
              inversion Hw; subst. cbv beta iota in Hchara.
              apply Permutation_list_to_bag_eq in Hchara.
              rewrite Hchara, DictIndexImpl.bag_to_list_to_bag by assumption.
              reflexivity.
            - (* no bucket: the filter is empty *)
              cbv beta iota in Hchara. cbn [bag_to_list] in Hchara.
              apply Permutation_sym, Permutation_nil in Hchara.
              rewrite Hchara. reflexivity.
          Qed.
        End composite_eq_filter_to_lookup.

        (* The two halves packaged as a registrable transformation. *)
        Ltac invert_tenv_wf_with_globals :=
          lazymatch goal with
            H: tenv_wf_with_globals _ _ _ |- _ => inversion H; subst
          end.

        Lemma composite_eq_filter_to_lookup_head_sound :
            forall (b : string) is_tbl_ty' aux_ty aux_wf,
              aux_ty_for_idx aux_ty ->
              (forall t, is_tbl_ty' t = true -> is_tbl_ty t = true) ->
              (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
              expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf
                (composite_eq_filter_to_lookup_head b).
          Proof.
            unfold aux_ty_for_idx, expr_aug_transf_sound; intros.
            invert_tenv_wf_with_globals.
            specialize (H tbl_ty). repeat destruct_match_hyp; intuition idtac.
            1: eapply composite_eq_filter_to_lookup_head_preserve_ty; eauto.
            1: eapply composite_eq_filter_to_lookup_head_preserve_sem; eauto.
            lazymatch goal with
              H: locals_wf ?G ?str, H': map.get ?G _ = _ |- _ =>
                apply H in H'
            end.
            destruct_match_hyp; intuition idtac.
            lazymatch goal with
              H: holds_for_all_entries _ ?str, H': map.get ?str _ = _ |- _ =>
                apply H in H'
            end.
            unfold value_wf_with_globals in *. invert_Forall; intuition auto.
          Qed.
        Lemma composite_use_idx_head_sound :
            forall is_tbl_ty' aux_ty aux_wf,
              aux_ty_for_idx aux_ty ->
              (forall t, is_tbl_ty' t = true -> is_tbl_ty t = true) ->
              (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
              expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf
                composite_use_idx_head.
          Proof.
            unfold aux_ty_for_idx, expr_aug_transf_sound; intros.
            invert_tenv_wf_with_globals.
            specialize (H tbl_ty). repeat destruct_match_hyp; intuition idtac.
            1: eapply composite_use_idx_head_preserve_ty; eauto.
            1: eapply composite_use_idx_head_preserve_sem; eauto.
            lazymatch goal with
              H: locals_wf ?G ?str, H': map.get ?G _ = _ |- _ =>
                apply H in H'
            end.
            destruct_match_hyp; intuition idtac.
            lazymatch goal with
              H: holds_for_all_entries _ ?str, H': map.get ?str _ = _ |- _ =>
                apply H in H'
            end.
            unfold value_wf_with_globals in *. invert_Forall; intuition auto.
          Qed.
      End WithTags.
    End WithMap.
  End WithVars.
End WithHole.

(* The registrable form, with every section variable spelled out so that the
   pipeline's hint database can apply it.  Same shape as
   DictIndexImpl.eq_filter_to_lookup_head_sound2. *)
Lemma composite_eq_filter_to_lookup_head_sound2 :
  forall (hole : string) (attrs : list string),
  forall tup acc x : string,
  forall tenv : map.map string type,
  map.ok tenv ->
  forall locals : map.map string value,
  map.ok locals ->
  forall (id_tag aux_tag idx_tag b : string)
         (is_tbl_ty' : type -> bool) (aux_ty : type -> type)
         (aux_wf : value -> Prop),
  aux_ty_for_idx id_tag aux_tag idx_tag (idx_ty attrs) aux_ty ->
  (forall t : type, is_tbl_ty' t = true -> is_tbl_ty attrs t = true) ->
  (forall v : value,
      aux_wf v ->
      aux_wf_for_idx id_tag aux_tag idx_tag (idx_wf hole attrs tup acc x) v) ->
  is_NoDup_opaque [tup; acc; x] ->
  expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf
    (composite_eq_filter_to_lookup_head attrs id_tag aux_tag idx_tag b).
Proof.
  intros; eapply composite_eq_filter_to_lookup_head_sound; eauto.
Qed.

#[export] Hint Resolve composite_eq_filter_to_lookup_head_sound2 : transf_hints.

(* The two maintenance rules need no restatement: closing the sections
   generalised them into exactly the registrable form, because neither one's
   soundness depends on the tags beyond what aux_ty_for_idx already carries. *)
#[export] Hint Resolve composite_use_idx_head_sound : transf_hints.
#[export] Hint Resolve cons_to_composite_insert_head_sound : transf_hints.
#[export] Hint Resolve filter_neq_to_composite_delete_head_sound : transf_hints.
