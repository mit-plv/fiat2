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

      (* What the key expression COMPUTES, in any environment that binds the
         row.  Stated on its own because the characterisation below rewrites
         with it under a fold, where the environment is not the literal one. *)
      Lemma interp_composite_key : forall (env : locals) rc,
          map.get env tup = Some (VRecord rc) ->
          interp_expr map.empty env (composite_key (EVar tup))
          = VRecord (record_sort [(attr1, record_proj attr1 rc);
                                  (attr2, record_proj attr2 rc)]).
      Proof.
        intros env rc Hget. cbn [interp_expr composite_key List.map].
        unfold get_local; rewrite Hget. reflexivity.
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
          type_of_value
            (VRecord (record_sort [(attr1, record_proj attr1 rc);
                                   (attr2, record_proj attr2 rc)]))
            (key_ty rt).
      Proof.
        intros rt rc Hrt Htbl Hrc.
        erewrite <- interp_composite_key with (env := map.put map.empty tup (VRecord rc)).
        2: apply map.get_put_same.
        eapply type_sound with (Genv := map.put map.empty tup (TRecord rt)).
        - apply composite_key_ty; [ assumption | ].
          apply TyEVar, map.get_put_same.
        - apply tenv_wf_empty.
        - apply tenv_wf_step; [ apply tenv_wf_empty | assumption ].
        - apply locals_wf_empty.
        - apply locals_wf_step; [ apply locals_wf_empty | assumption ].
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

      (* The key of a row, on the value side. *)
      Definition ckey (rc : list (string * value)) : value :=
        VRecord (record_sort [(attr1, record_proj attr1 rc);
                              (attr2, record_proj attr2 rc)]).

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
        invert_type_of_value_clear; simpl.
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
            repeat rewrite_map_get_put_goal; try now use_is_NoDup.
            assert (Hkty : type_wf (key_ty l)) by (apply key_ty_wf; auto).
            (* The one place the composite key is used, and the only place this
               proof differs from the single-attribute one: there the key's type
               comes from record_proj_sound, here from the key expression's own
               typing through composite_key_value_sound. *)
            enough (type_of_value (VOption (dict_lookup (ckey l2) l1))
                      (TOption (TBag (TRecord l)))).
            2:{ eapply dict_lookup_sound with (dk := Unranged).
                1: exact Hkty.
                1: constructor; assumption.
                1: constructor; assumption.
                1: apply composite_key_value_sound; auto; constructor; auto. }
            unfold ckey in *.
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
                   it.  The single-attribute proof unfolds is_tbl_ty at the
                   start and so never has one in scope. *)
                1: clear Htbl'; rewrite_l_to_r; constructor; auto.
                1: apply_Forall_In. } }
        1:{ induction l0; cbn; auto. invert_Forall. erewrite IHl0; auto.
            invert_type_of_value_clear. unfold ckey. do 3 f_equal.
            repeat (case_match; auto). }
      Qed.

      (* ---- facts about dict_insert, dict_lookup and bag_insert ----

         These five say nothing about any index: they are properties of the
         canonical dictionary and bag operations.  DictIndexImpl proves the
         same five for itself, and the comment at DictIndexImpl.v:348 states
         the convention they violate -- lemmas about dict_insert and
         dict_delete rather than about an index belong in Utils.  Moving them
         there is the right cleanup and would remove this duplication; it
         touches DictIndexImpl and the whole build, so it is flagged here
         rather than done in passing. *)

      Lemma value_eqb_iff_eq : forall (v v' : value),
          value_eqb v v' = true <-> v = v'.
      Proof.
        split; intros; subst; auto using value_eqb_eq, value_eqb_refl.
      Qed.

      Lemma value_compare_Eq_iff_eq : forall (v v' : value),
          value_compare v v' = Eq <-> v = v'.
      Proof.
        split; intros; subst; auto using value_compare_Eq_eq, value_compare_refl.
      Qed.

      Lemma dict_lookup_insert_diff : forall k k' (v : value) d,
          k <> k' -> dict_lookup k (dict_insert k' v d) = dict_lookup k d.
      Proof.
        intros; induction d; cbn.
        1:{ rewrite <- value_eqb_iff_eq, Bool.not_true_iff_false in *.
            rewrite_l_to_r; auto. }
        1:{ case_match; cbn; unfold value_ltb, value_eqb.
            case_match; cbn; unfold value_ltb, value_eqb;
              rewrite <- value_compare_Eq_iff_eq in *.
            1:{ rewrite value_compare_Eq_iff_eq in *; subst.
                rewrite <- value_compare_Eq_iff_eq in *.
                case_match; intuition auto. }
            all: case_match; intuition auto. }
      Qed.

      Lemma dict_lookup_insert_same : forall k (v : value) d,
          dict_lookup k (dict_insert k v d) = Some v.
      Proof.
        induction d; cbn; intros.
        1: rewrite value_eqb_refl; trivial.
        1:{ case_match. unfold value_ltb, value_eqb.
            case_match; cbn.
            1,2: rewrite value_eqb_refl; trivial.
            unfold value_eqb. rewrite_l_to_r. assumption. }
      Qed.

      Lemma bag_to_list_insert_Permutation : forall (v : value) b,
          Permutation (bag_to_list (bag_insert v b)) (v :: bag_to_list b).
      Proof.
        intros. pose proof (bag_to_list__bag_insert v b).
        repeat destruct_exists; destruct_and; subst.
        rewrite_l_to_r.
        eapply perm_trans.
        1: apply Permutation_sym, Permutation_middle.
        rewrite bag_to_list_app. auto.
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
            rewrite dict_lookup_insert_same.
            rewrite bag_to_list_insert_Permutation.
            apply perm_skip; auto. }
        1:{ rewrite dict_lookup_insert_diff; auto.
            rewrite <- value_eqb_iff_eq, Bool.not_true_iff_false in *;
              eauto using value_eqb_sym. }
      Qed.

      Instance composite_dict_idx : IndexInterface.index :=
        IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

      Instance composite_dict_idx_ok : IndexInterface.ok composite_dict_idx idx_wf :=
        IndexInterface.Build_ok composite_dict_idx idx_wf idx_ty_wf to_idx_ty to_idx_wf.
    End WithMap.
  End WithVars.
End WithHole.
