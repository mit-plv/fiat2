Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.IndexInterface fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils
  fiat2.Substitute fiat2.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
(* NOT Import: this file defines to_idx, idx_ty, is_tbl_ty and gallina_to_idx
   of its own, and importing would shadow them.  What is wanted from here is
   the handful of lemmas about dict_insert, dict_lookup and bag_insert that say
   nothing about any index -- they happen to live there, and the comment at
   DictIndexImpl.v:348 states the convention under which they belong in Utils
   instead.  Moving them is the right cleanup and would drop this dependency;
   it touches the whole build, so it is noted rather than done in passing. *)
Require fiat2.DictIndexImpl.
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

   `attrs` below is a section variable, so no lemma about it can be proved by
   induction on it.  Everything that needs an induction is therefore stated
   here, over a universally quantified list, and instantiated at attrs. *)

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
   than once per side in the rule's guard.

   Each lemma below is stated with the matcher's result in the GOAL rather
   than in a hypothesis, as a match with a trivial None branch.  That is not
   decoration: it lets the proof reduce the matcher with case_match instead of
   inverting it, so no lemma has to name the pieces of a pattern. *)

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

(* The recursive case, as an equation: cbn will not unfold the fixpoint on a
   term it cannot reduce all the way, so the proofs rewrite with this. *)
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

  (* What a collected conjunction COMPUTES on a row: every collected
     attribute equals its right-hand side. *)
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

    (* the composite key of a row, as a record literal *)
    Definition composite_key (r : expr) : expr :=
      ERecord (List.map (fun a => (a, EAccess r a)) attrs).

    Definition to_idx : expr :=
      let k := composite_key (EVar tup) in
      EFold (EVar hole) (EAtom (AEmptyDict Unranged None)) tup acc
        (ETernop OInsert (EVar acc) k
           (EBinop OBagInsert
              (EOptMatch (EBinop OLookup (EVar acc) k)
                 (EAtom (AEmptyBag None))
                 x (EVar x))
              (EVar tup))).

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

    (* The two things is_tbl_ty is checked for, cashed in once. *)
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
         get_attr_type names.  The induction the section variable forbids. *)
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

      (* The key of a row, on the value side. *)
      Definition ckey (rc : list (string * value)) : value :=
        VRecord (record_sort (List.map (fun a => (a, record_proj a rc)) attrs)).

      Lemma interp_key_fields : forall (store env : locals) y rc al,
          map.get env y = Some (VRecord rc) ->
          List.map (fun '(s, e) => (s, interp_expr store env e))
            (List.map (fun a => (a, EAccess (EVar y) a)) al)
          = List.map (fun a => (a, record_proj a rc)) al.
      Proof.
        induction al; cbn [List.map]; intros Hget; auto.
        cbn [interp_expr]. unfold get_local; rewrite Hget.
        f_equal. apply IHal; assumption.
      Qed.

      (* What the key expression COMPUTES, in any environment that binds the
         row.  Stated on its own because the characterisation below rewrites
         with it under a fold, where the environment is not the literal one. *)
      Lemma interp_composite_key : forall (store env : locals) y rc,
          map.get env y = Some (VRecord rc) ->
          interp_expr store env (composite_key (EVar y)) = ckey rc.
      Proof.
        intros store env y rc Hget.
        unfold composite_key, ckey. cbn [interp_expr].
        do 2 f_equal. apply interp_key_fields; assumption.
      Qed.

      (* The fold's step, stated separately so the assembly below does not have
         to interleave the record-literal premises with the dictionary ones. *)
      Lemma to_idx_body_ty : forall rt (Genv : tenv),
          type_wf (TRecord rt) ->
          is_tbl_ty (TList (TRecord rt)) = true ->
          map.get Genv tup = Some (TRecord rt) ->
          map.get Genv acc = Some (TDict Unranged (key_ty rt) (TBag (TRecord rt))) ->
          type_of map.empty Genv
            (ETernop OInsert (EVar acc) (composite_key (EVar tup))
               (EBinop OBagInsert
                  (EOptMatch (EBinop OLookup (EVar acc) (composite_key (EVar tup)))
                     (EAtom (AEmptyBag None)) x (EVar x))
                  (EVar tup)))
            (TDict Unranged (key_ty rt) (TBag (TRecord rt))).
      Proof.
        intros rt Genv Hrt Htbl Htup Hacc.
        eapply TyETernop.
        1: apply TyOInsert.
        - apply TyEVar; assumption.
        - apply composite_key_ty; [ assumption | apply TyEVar; assumption ].
        - eapply TyEBinop.
          1: apply TyOBagInsert.
          (* eassumption, not assumption: at this point the lookup's key and
             kind are still evars, which assumption will not instantiate. *)
          + eapply TyEOptMatch.
            * eapply TyEBinop.
              1: apply TyOLookup.
              -- apply TyEVar; eassumption.
              -- apply composite_key_ty; [ assumption | apply TyEVar; eassumption ].
            * apply TyEAtom, TyAEmptyBag'; assumption.
            * apply TyEVar. rewrite map.get_put_same; reflexivity.
          + apply TyEVar; eassumption.
      Qed.

      Lemma to_idx_ty : forall (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t).
      Proof.
        intros t Hwf Htbl. unfold to_idx.
        destruct t; try discriminate. destruct t; try discriminate.
        cbn [idx_ty].
        assert (Hrt : type_wf (TRecord l)) by (invert_type_wf; assumption).
        eapply TyEFold.
        - apply TyEVar. rewrite map.get_put_same; reflexivity.
        - apply TyEAtom, TyAEmptyDict'.
          + apply key_ty_wf; assumption.
          + constructor; assumption.
        - apply to_idx_body_ty; auto.
          + rewrite map.get_put_diff, map.get_put_same; [ reflexivity | use_is_NoDup ].
          + rewrite map.get_put_same; reflexivity.
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

      (* The key VALUE a row is filed under has the key type.  Derived from
         composite_key_ty through type_sound rather than proved again by hand:
         the key is an ordinary expression of the language, so the type of its
         value is already a consequence of the type of the expression.  This is
         the one fact the whole characterisation below needs about the key, and
         it is where the single-attribute development would instead appeal to
         record_proj_sound. *)
      Lemma composite_key_value_sound : forall rt rc,
          type_wf (TRecord rt) ->
          is_tbl_ty (TList (TRecord rt)) = true ->
          type_of_value (VRecord rc) (TRecord rt) ->
          type_of_value (ckey rc) (key_ty rt).
      Proof.
        intros rt rc Hrt Htbl Hrc.
        erewrite <- interp_composite_key
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

      Lemma fiat2_gallina_to_idx : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          interp_expr map.empty (map.put map.empty hole v) to_idx = gallina_to_idx v.
      Proof.
        intros v t Hwf Htbl Hv.
        assert (Htbl' := Htbl). unfold is_tbl_ty in Htbl.
        repeat destruct_match_hyp; try discriminate.
        assert (Hrt : type_wf (TRecord l)) by (invert_type_wf; assumption).
        invert_type_of_value_clear.
        unfold to_idx; cbn [interp_expr interp_atom].
        unfold get_local; rewrite_map_get_put_goal.
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
            erewrite !interp_composite_key with (rc := l2) by
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
        1:{ induction l0; cbn; auto. invert_Forall. erewrite IHl0; auto.
            invert_type_of_value_clear. cbn [gallina_to_idx]. do 3 f_equal.
            repeat (case_match; auto). }
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
         merely some value derived from the attributes, and the two lemmas
         below are the whole of what the arity costs: in the binary file they
         were two hand-written cases, here they are one induction. *)
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

      (* A pair list whose names are the key attributes IN ORDER and whose
         values are the row's is the key's own field list. *)
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


      (* Every row of a well-typed table is a record.  In its own lemma so that
         the inversion has exactly one hypothesis to choose from; inside the
         rule's proof there are three type_of_value hypotheses and the
         inversion tactic picks the wrong one. *)
      Lemma Forall_VRecord_of_list : forall (l : list value) rt,
          type_of_value (VList l) (TList (TRecord rt)) ->
          Forall (fun v => exists rc, v = VRecord rc) l.
      Proof.
        intros l rt H. invert_type_of_value_clear.
        (* tie the hypothesis's list to the goal's: inversion may have
           substituted l away, in which case naming it is ill-typed *)
        lazymatch goal with
          HF: Forall _ ?ll |- Forall _ ?ll => eapply Forall_impl; [ | exact HF ]
        end.
        (* cbn first: Forall_impl hands the premise back as a beta-redex, which
           the inversion tactic's pattern does not match *)
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
         interpreter produces -- otherwise the two sides of the rule agree only
         up to a conversion the rewrite cannot see. *)
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
         the same filter.  Separated out so the rule's own proof is about the
         index and not about evaluating a conjunction. *)
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

      Section WithTags.
        Context (id_tag aux_tag idx_tag : string).

        Notation aux_ty_for_idx := (aux_ty_for_idx id_tag aux_tag idx_tag idx_ty).
        Notation aux_wf_for_idx := (aux_wf_for_idx id_tag aux_tag idx_tag idx_wf).

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

          (* Reading the table and the index out through the tags.  Two lines
             each, but stated rather than inlined: the matches have to be
             reduced in order, and doing it inside the rule's proof buries
             that in a replace-by tactic. *)
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

          (* What the emitted probe computes.  Stated whole rather than built up
             inside the rule's proof: the tag accesses have to be reduced in
             order, and the SOME branch's binder has to be discharged after the
             lookup is case-split, not before. *)
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
            intros Genv e t' Hgenv He.
            unfold composite_eq_filter_to_lookup_head.
            (* the predicate is not a fixed tree, so the pattern cannot be
               enumerated with destruct_subexpr: case_match reduces exactly the
               matches the rule itself performs, and the matcher is one of them *)
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
            (* unfold idx_ty in the index's own typing hypothesis, or the
               dictionary's three arguments stay behind a constant that
               unification will not look through *)
            cbn [idx_ty] in Hidx.
            eapply TyEOptMatch.
            (* the SOME binder first: it is what pins the option's element
               type, after which every other goal is determinate *)
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
            (* destruct substitutes into Hchara as well, so no rewrite is
               needed -- its bucket becomes a match on w. *)
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
              (* beta and iota ONLY: a bare cbn unfolds record_sort into its
                 mergesort implementation and the filter stops matching *)
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
