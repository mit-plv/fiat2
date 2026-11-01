Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.IndexInterface fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils
  fiat2.Substitute fiat2.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.

(* ============================================================
   A DICTIONARY KEYED ON TWO ATTRIBUTES AT ONCE.

   WHY IT NEEDS NO NEW TYPE AND NO NEW OPERATOR.  The key is a RECORD of the
   two attributes, so TRecord carries it, value_compare already orders it
   (record_compare, Value.v:102), and OLookup is key-generic.  The only thing
   that had to be checked is that the key a lookup BUILDS equals the key the
   index STORED even when the two are written with their fields in different
   orders -- and it does, because interp_expr of an ERecord canonicalises with
   record_sort (Interpret.v:448), while TyERecord accepts the literal in any
   order and types it at the sorted permutation (TypeSystem.v:279-285).  So
   field order is a non-issue on both sides, which is what makes a composite
   key an ordinary dictionary rather than a new structure.

   WHAT IT IS FOR.  Two subjects measure its absence.  eval/Kafka_Cluster's
   partition(topic, partition) is a conjunctive equality on two attributes --
   `new TopicPartition(p.topic(), p.partition())` in Kafka -- and today it
   probes the topic's bucket and filters the partition out of it
   (one_partition_probes_then_filters), which is O(partitions in the topic)
   where a composite key is O(1).  eval/Kafka_WindowStore's fetch(key, from,
   to) wants a point on key and a range on time (fetch_key_probes_split).
   This file serves the FIRST of those.

   ARITY TWO, DELIBERATELY, AND SAID OUT LOUD.  Both witnesses are binary, and
   a record of two fields is stateable without any machinery a record of n
   would need (an idx_ty folded over a list, and every proof carrying that
   fold).  The n-ary generalisation is the same refactor the trigram delete
   block wants -- parameterise the index on a key FUNCTION of the row rather
   than on an attribute -- and it should be done once, for both, not twice.

   UNRANGED, AND THAT IS NOT A LIMITATION OF THIS FILE.  record_compare orders
   records lexicographically in SORTED FIELD-NAME order, which is not the order
   a programmer declared the key in, so a range over a composite key would
   range on whichever attribute happens to sort first by name.  That is a
   trap, not a feature, and no witnessed query wants it: Kafka_Cluster's
   composite read is a point.  The kind therefore says Unranged, which already
   makes ODictRange untypeable here -- see Ex_DictMinKey for the same refusal
   used deliberately.
   ============================================================ *)

Section WithHole.
  Context (hole : string).
  (* The two key attributes, in the order the index is DECLARED with.  Their
     order does not reach the stored key -- record_sort decides that -- so it
     matters only for reading the declaration. *)
  Context (attr1 attr2 : string).

  Section WithVars.
    Context (tup acc x : string).
    Context (H_NoDup : is_NoDup_opaque [tup; acc; x]).

    (* the composite key of a row, as a record literal *)
    Definition composite_key (r : expr) : expr :=
      ERecord [(attr1, EAccess r attr1); (attr2, EAccess r attr2)].

    Definition to_idx : expr :=
      let k := composite_key (EVar tup) in
      EFold (EVar hole) (EAtom (AEmptyDict Unranged None)) tup acc
        (ETernop OInsert (EVar acc) k
           (EBinop OBagInsert
              (EOptMatch (EBinop OLookup (EVar acc) k)
                 (EAtom (AEmptyBag None))
                 x (EVar x))
              (EVar tup))).

    (* The two attributes must be present AND DISTINCT.  Distinctness is not
       fussiness: a record literal with a repeated field name fails TyERecord's
       NoDup premise, so an index on (a, a) could not be built at all. *)
    Definition is_tbl_ty (t : type) : bool :=
      match t with
      | TList (TRecord rt) =>
          (inb String.eqb attr1 (List.map fst rt)
           && inb String.eqb attr2 (List.map fst rt)
           && negb (String.eqb attr1 attr2))%bool
      | _ => false
      end.

    Definition key_ty (rt : list (string * type)) : type :=
      TRecord (record_sort [(attr1, get_attr_type rt attr1);
                            (attr2, get_attr_type rt attr2)]).

    Definition idx_ty (t : type) : type :=
      match t with
      | TList (TRecord rt) => TDict Unranged (key_ty rt) (TBag (TRecord rt))
      | _ => TUnit
      end.
    (* The key record's field names are duplicate-free.  This is the premise
       both TyERecord and WFTRecord need, and it is exactly what is_tbl_ty's
       distinctness conjunct is there to supply. *)
    Lemma key_names_NoDup : forall rt,
        is_tbl_ty (TList (TRecord rt)) = true ->
        NoDup (List.map fst [(attr1, get_attr_type rt attr1);
                             (attr2, get_attr_type rt attr2)]).
    Proof.
      cbn; intros rt H.
      repeat rewrite Bool.andb_true_iff in H; intuition idtac.
      rewrite Bool.negb_true_iff, String.eqb_neq in *.
      repeat constructor; cbn; intuition auto.
    Qed.

    Lemma key_ty_wf : forall rt,
        type_wf (TRecord rt) ->
        is_tbl_ty (TList (TRecord rt)) = true ->
        type_wf (key_ty rt).
    Proof.
      intros rt Hwf Htbl. unfold key_ty. constructor.
      - eapply Permutation_NoDup;
          [ apply Permutation_map, Permuted_record_sort
          | apply key_names_NoDup; assumption ].
      - apply StronglySorted_record_sort.
      - eapply Permutation_Forall;
          [ apply Permutation_map, Permuted_record_sort | ].
        cbn; repeat constructor; apply get_attr_type_ty_wf; assumption.
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
    (* An attribute is_tbl_ty found really is in the record, with the type
       get_attr_type names.  Stated separately because both key lemmas below
       need it and burying it in an assert would hide the one place the
       membership test is cashed in. *)
    Lemma access_record_get_attr_type : forall rt a,
        inb String.eqb a (List.map fst rt) = true ->
        access_record rt a = Success (get_attr_type rt a).
    Proof.
      intros rt a H. rewrite inb_true_iff in H.
      apply In_access_record in H. destruct H as [t Ht].
      unfold get_attr_type. rewrite Ht. reflexivity.
    Qed.

    Lemma is_tbl_ty_attrs : forall rt,
        is_tbl_ty (TList (TRecord rt)) = true ->
        inb String.eqb attr1 (List.map fst rt) = true
        /\ inb String.eqb attr2 (List.map fst rt) = true.
    Proof.
      cbn; intros rt H.
      repeat rewrite Bool.andb_true_iff in H; intuition idtac.
    Qed.

    Section WithMap.
      Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
      Notation value := (value).
      Context {locals : map.map string value} {locals_ok : map.ok locals}.

      (* The key a row is filed under has the key type, whatever environment
         binds the row.  This is the whole typing content of a composite key:
         it is an ordinary record literal, and record_sort on the TYPE side
         mirrors the record_sort interp performs on the VALUE side. *)
      Lemma composite_key_ty : forall (Genv : tenv) rt r,
          is_tbl_ty (TList (TRecord rt)) = true ->
          type_of map.empty Genv r (TRecord rt) ->
          type_of map.empty Genv (composite_key r) (key_ty rt).
      Proof.
        intros Genv rt r Htbl Hr.
        (* pose rather than apply-in: is_tbl_ty's THIRD conjunct, that the two
           attributes differ, is what key_names_NoDup needs below, and
           consuming Htbl would throw it away. *)
        pose proof (is_tbl_ty_attrs _ Htbl) as [ H1 H2 ].
        unfold composite_key, key_ty.
        eapply TyERecord with
          (tl := [(attr1, get_attr_type rt attr1); (attr2, get_attr_type rt attr2)]).
        - reflexivity.
        - cbn. constructor.
          1: econstructor; eauto using access_record_get_attr_type.
          constructor.
          1: econstructor; eauto using access_record_get_attr_type.
          constructor.
        - apply Permuted_record_sort.
        - apply key_names_NoDup; assumption.
        - apply StronglySorted_record_sort.
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

      Instance composite_dict_idx : IndexInterface.index :=
        IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

      Instance composite_dict_idx_ok : IndexInterface.ok composite_dict_idx idx_wf :=
        IndexInterface.Build_ok composite_dict_idx idx_wf idx_ty_wf to_idx_ty to_idx_wf.
    End WithMap.
  End WithVars.
End WithHole.
