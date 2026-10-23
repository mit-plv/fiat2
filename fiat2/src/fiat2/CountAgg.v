Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute fiat2.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.

(* A maintained ROW COUNT.

   The same shape as SumAgg and shorter everywhere, because a count reads no
   attribute.  There is no attr parameter; is_tbl_ty asks only for a table of
   records, since type_of_aggr AGCount is generic in the element type; and the
   step function of interp_aggr AGCount ignores the element it is handed, which
   is why the fold lemma below needs no typing hypothesis where SumAgg's
   fold_add_int needs one.

   Witnesses: Kafka's InFlightRequests.inFlightRequestCount and NamedCache's
   size().  eval/Keycloak_CachedRealm.v already contains an unoptimized
   whole-table count, so enabling this choice there turns it into a field
   read with no other change to that example. *)

Section WithHole.
  Context (hole : string).

  Definition to_idx : expr := EACFold AGCount (EBagOf (EVar hole)).

  Definition is_tbl_ty (t : type) : bool :=
    match t with
    | TList (TRecord _) => true
    | _ => false
    end.

  Definition idx_ty (t : type) : type := TInt.

  Lemma idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t).
    intros; constructor.
  Qed.

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Notation value := (value).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Definition idx_wf (tbl_v agg_v : value) : Prop :=
      agg_v = interp_expr map.empty (map.put map.empty hole tbl_v) to_idx.

    Lemma to_idx_ty : forall (t : type),
        type_wf t -> is_tbl_ty t = true ->
        type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t).
    Proof.
      unfold is_tbl_ty, to_idx, idx_ty; intros.
      repeat destruct_match_hyp; try discriminate.
      repeat econstructor; repeat rewrite_map_get_put_goal; eauto.
    Qed.

    Lemma to_idx_wf : forall (v : value) (t : type),
        type_wf t -> is_tbl_ty t = true ->
        type_of_value v t ->
        idx_wf v (interp_expr map.empty (map.put map.empty hole v) to_idx).
    Proof.
      unfold idx_wf; intros; auto.
    Qed.

    Instance count_agg : IndexInterface.index := IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

    Instance count_agg_ok : IndexInterface.ok count_agg idx_wf :=
      IndexInterface.Build_ok count_agg idx_wf idx_ty_wf to_idx_ty to_idx_wf.

    (* The number of rows, as an integer.  Written as a fold of addition over
       ones so that it mirrors SumAgg's sum of an attribute, and so that no
       nat and no Z.of_nat appears anywhere in this file. *)
    Definition Zcount (l : list value) : Z :=
      fold_right Z.add 0%Z (List.map (fun _ => 1%Z) l).

    (* AGCount's fold, over any rows at all.  No typing hypothesis: the step
       discards the row, so nothing is ever read out of it. *)
    Lemma fold_count : forall (l : list value),
        fold_right (fun _ : value => apply_int_binop Z.add (VInt 1 : value)) (VInt 0) l
        = VInt (Zcount l).
    Proof.
      unfold Zcount; induction l as [| v l IH]; cbn; auto.
      rewrite IH; reflexivity.
    Qed.

    (* a count does not depend on the order of the rows *)
    Lemma Zcount_Permutation : forall l1 l2,
        Permutation l1 l2 -> Zcount l1 = Zcount l2.
    Proof.
      unfold Zcount; intros. apply List.fold_right_change_order.
      1: intros; rewrite !Z.add_assoc, (Z.add_comm a1); reflexivity.
      1: apply Permutation_map; auto.
    Qed.

    (* a count splits over a filter and its complement *)
    Lemma Zcount_filter_partition : forall (p : value -> bool) l,
        Zcount l = (Zcount (filter p l) + Zcount (filter (fun v => negb (p v)) l))%Z.
    Proof.
      (* the reduction is restricted: a bare cbn would compute "1 + _" into Z's
         binary representation, since here the summand is the literal 1 and not
         an opaque projection as it is in SumAgg *)
      unfold Zcount; intros p l; induction l as [| v l IH]; auto.
      cbn [List.map fold_right filter].
      destruct (p v); cbn [List.map fold_right negb filter]; rewrite IH.
      1: apply Z.add_assoc.
      1: apply Z.add_shuffle3.
    Qed.

    (* the count of a bag of rows *)
    Lemma interp_count_bag : forall (store env : locals) eb lb,
        interp_expr store env eb = VBag lb ->
        interp_expr store env (EACFold AGCount eb) = VInt (Zcount (bag_to_list lb)).
    Proof.
      intros * H_e. rewrite interp_EACFold, H_e. cbn [interp_aggr].
      apply fold_count.
    Qed.

    (* the count of a list of rows *)
    Lemma interp_count_list : forall (store env : locals) e l,
        interp_expr store env e = VList l ->
        interp_expr store env (EACFold AGCount (EBagOf e)) = VInt (Zcount l).
    Proof.
      intros * H_e.
      erewrite interp_count_bag; [ | rewrite interp_EBagOf, H_e; reflexivity ].
      f_equal. apply Zcount_Permutation, list_to_bag_to_list_Permutation.
    Qed.

    (* the count of the rows a predicate keeps *)
    Lemma interp_count_filter_bag : forall (store env : locals) e l y p t1 t2,
        interp_expr store env e = VList l ->
        interp_expr store env (EACFold AGCount (flatmap_filter_bag (EBagOf e) y p y t1 t2))
        = VInt (Zcount (filter (fun v => match interp_expr store (map.put env y v) p with
                                         | VBool b => b
                                         | _ => false
                                         end) l)).
    Proof.
      intros * H_e.
      erewrite interp_count_bag;
        [ | rewrite interp_flatmap_filter_bag, interp_EBagOf, H_e; reflexivity ].
      f_equal. apply Zcount_Permutation.
      eapply perm_trans; [ apply list_to_bag_to_list_Permutation | ].
      apply Permutation_filter; auto using list_to_bag_to_list_Permutation.
    Qed.

    Ltac invert_type_of_aggr_clear :=
      lazymatch goal with
      | H: type_of_aggr _ _ _ |- _ =>
          inversion H; subst
      end.

    Section WithTags.
      Context (id_tag aux_tag idx_tag: string).

      Notation aux_ty_for_idx := (aux_ty_for_idx id_tag aux_tag idx_tag idx_ty).
      Notation aux_wf_for_idx := (aux_wf_for_idx id_tag aux_tag idx_tag idx_wf).

      Section count_to_agg_lookup.
        Context (tbl : string).

        (* the whole-table count is the member itself *)
        Definition count_to_agg_lookup_head (e : expr) :=
          match e with
          | EACFold AGCount (EBagOf (EAccess (ELoc tbl0) id_tag0)) =>
              if all_eqb [(tbl, [tbl0]); (id_tag, [id_tag0])]
              then EAccess (EAccess (ELoc tbl) aux_tag) idx_tag
              else e
          | _ => e
          end.

        Lemma count_to_agg_lookup_head_preserve_ty : forall tl t aux_tl (Gstore : tenv),
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (TRecord tl) ->
            access_record tl id_tag = Success t ->
            access_record tl aux_tag = Success (TRecord aux_tl) ->
            access_record aux_tl idx_tag = Success (idx_ty t) ->
            preserve_ty Gstore (count_to_agg_lookup_head).
        Proof.
          unfold preserve_ty, is_tbl_ty. intros.
          repeat destruct_match_hyp; try congruence.
          repeat destruct_subexpr. simpl.
          case_match; auto. repeat rewrite Bool.andb_true_r in *.
          repeat rewrite Bool.andb_true_iff in *; intuition idtac. rewrite eqb_eq in *; subst.
          repeat invert_type_of_clear. repeat invert_type_of_op_clear.
          repeat rewrite_map_get_put_hyp.
          invert_type_of_aggr_clear.
          repeat (clear_refl; repeat do_injection2).
          repeat (rewrite_l_to_r; do_injection2).
          repeat (econstructor; eauto).
        Qed.

        Lemma count_to_agg_lookup_head_preserve_sem : forall (Gstore : tenv) (store : locals) tl t aux_tl,
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (TRecord tl) ->
            access_record tl id_tag = Success t ->
            access_record tl aux_tag = Success (TRecord aux_tl) ->
            access_record aux_tl idx_tag = Success (idx_ty t) ->
            match map.get store tbl with
            | Some v => aux_wf_for_idx v
            | _ => False
            end ->
            preserve_sem Gstore store count_to_agg_lookup_head.
        Proof.
          unfold preserve_sem, aux_wf_for_idx; intros.
          unfold is_tbl_ty, idx_ty in *.
          apply_locals_wf store.
          repeat (destruct_match_hyp; try discriminate; intuition idtac; []).
          invert_type_of_value_clear.
          pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H16 E1 H2); auto.
          pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H16 E2 H3); auto.
          repeat invert_type_of_value_clear.
          pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H20 E4 H4); auto.
          repeat destruct_subexpr. unfold count_to_agg_lookup_head.
          simpl; case_match; auto.
          repeat rewrite Bool.andb_true_iff in *; intuition idtac.
          rewrite eqb_eq in *; subst. repeat clear_refl.
          unfold idx_wf in *.
          repeat rewrite_l_to_r.
          cbn. unfold get_local. rewrite_l_to_r. unfold record_proj.
          repeat rewrite_l_to_r. unfold to_idx.
          cbn. unfold get_local. unfold record_proj.
          rewrite_map_get_put_goal. reflexivity.
        Qed.
      End count_to_agg_lookup.

      Section cons_to_incr.
        (* an insert adds one, and never looks at the row it adds *)
        Definition cons_to_incr_head (e : expr) :=
          match e with
          | EACFold AGCount (EBagOf (EBinop OCons e1 e2)) =>
              EBinop OPlus (EAtom (AInt 1)) (EACFold AGCount (EBagOf e2))
          | _ => e
          end.

        Lemma cons_to_incr_head_preserve_ty : forall (Gstore : tenv),
            preserve_ty Gstore cons_to_incr_head.
        Proof.
          unfold preserve_ty; intros. repeat destruct_subexpr.
          cbn. repeat (case_match; auto).
          repeat invert_type_of_clear.
          repeat invert_type_of_op_clear.
          invert_type_of_aggr_clear.
          repeat (econstructor; eauto).
        Qed.

        Lemma cons_to_incr_head_preserve_sem : forall (Gstore : tenv) (store : locals),
            preserve_sem Gstore store cons_to_incr_head.
        Proof.
          unfold preserve_sem; intros. repeat destruct_subexpr.
          cbn [cons_to_incr_head]. repeat (case_match; auto; []).
          repeat invert_type_of_clear.
          repeat invert_type_of_op_clear.
          apply_type_sound e2.
          invert_type_of_value_clear.
          lazymatch goal with
          | H: VList ?ll = interp_expr store env e2 |- _ =>
              assert (H_tl : interp_expr store env e2 = VList ll) by (symmetry; exact H)
          end.
          (* the collection inserted into, and the result of the insert *)
          erewrite interp_count_list with (e := EBinop OCons e1 e2);
            [ | cbn [interp_expr interp_binop]; rewrite H_tl; reflexivity ].
          rewrite interp_EBinop.
          erewrite interp_count_list; [ | exact H_tl ].
          (* the reduction stays away from Z.add, which would otherwise compute
             "1 + _" into Z's binary representation *)
          cbn [interp_expr interp_atom interp_binop apply_int_binop].
          unfold Zcount; cbn [List.map fold_right]; reflexivity.
        Qed.
      End cons_to_incr.

      Section filter_neq_to_count_sub.
        (* A delete BY KEY subtracts the rows that carry the key.  The
           attribute is a pattern variable: a count reads no attribute of its
           own, so any attribute may be the one deleted on. *)
        Definition filter_neq_to_count_sub_head (e : expr) :=
          match e with
          | EACFold AGCount
              (EBagOf (flatmap_filter_list e' y
                         (EUnop ONot (EBinop OEq (EAccess (EVar y0) attr0) k)) y1 t1 t2)) =>
              if all_eqb [(y, [y0; y1])]
              then EBinop OMinus
                     (EACFold AGCount (EBagOf e'))
                     (EACFold AGCount
                        (flatmap_filter_bag (EBagOf e') y
                           (EBinop OEq (EAccess (EVar y) attr0) k) y None None))
              else e
          | _ => e
          end.

        Lemma filter_neq_to_count_sub_head_preserve_ty : forall (Gstore : tenv),
            preserve_ty Gstore filter_neq_to_count_sub_head.
        Proof.
          unfold preserve_ty; intros. repeat destruct_subexpr.
          cbn. repeat (case_match; auto).
          cbn [all_eqb all_eqb' andb] in *.
          rewrite !Bool.andb_true_r, !Bool.andb_true_iff in *; intuition idtac.
          rewrite eqb_eq in *; subst.
          repeat invert_type_of_clear. repeat invert_type_of_op_clear.
          invert_type_of_aggr_clear.
          repeat rewrite_map_get_put_hyp.
          econstructor.
          1: constructor.
          (* the count over the whole table *)
          1:{ repeat (econstructor; eauto);
              repeat rewrite_map_get_put_goal; auto; congruence. }
          (* the count over the rows that carry the key; the bag's element type
             comes from the table, so the empty-bag annotations are determined *)
          1:{ econstructor; [ constructor | ].
              lazymatch goal with
              | H: type_of _ _ e1 (TList ?rt) |- _ =>
                  assert (type_wf rt) by (apply type_of__type_wf in H; auto;
                                          invert_type_wf; auto);
                  eapply TyEFlatmap_Bag with (t1 := rt)
              end.
              all: repeat (econstructor; eauto);
                repeat rewrite_map_get_put_goal; auto; try congruence.
          }
        Qed.

        Lemma filter_neq_to_count_sub_head_preserve_sem : forall (Gstore : tenv) (store : locals),
            preserve_sem Gstore store filter_neq_to_count_sub_head.
        Proof.
          unfold preserve_sem; intros. repeat destruct_subexpr.
          cbn [filter_neq_to_count_sub_head]. repeat (case_match; auto; []).
          cbn [all_eqb all_eqb' andb] in *.
          rewrite !Bool.andb_true_r, !Bool.andb_true_iff in *; intuition idtac.
          rewrite eqb_eq in *; subst.
          repeat invert_type_of_clear. repeat invert_type_of_op_clear.
          invert_type_of_aggr_clear.
          repeat rewrite_map_get_put_hyp.
          apply_type_sound e1. invert_type_of_value_clear.
          lazymatch goal with
          | H: VList ?ll = interp_expr store env e1 |- _ =>
              assert (H_tbl : interp_expr store env e1 = VList ll) by (symmetry; exact H)
          end.
          (* the count over the survivors, over the whole table, and over the rows
             that carry the key.  Each rewrite names its own subject: both sides
             of the goal contain a count of a bag of a list. *)
          erewrite interp_count_list with
            (e := flatmap_filter_list e1 x
                    (EUnop ONot (EBinop OEq (EAccess (EVar x) s) e2_1_2)) x t0 t1);
            [ | rewrite interp_flatmap_filter_list, H_tbl; reflexivity ].
          rewrite interp_EBinop.
          erewrite interp_count_list with (e := e1); [ | exact H_tbl ].
          erewrite interp_count_filter_bag with (e := e1); [ | exact H_tbl ].
          (* a count splits over the delete's predicate and its complement *)
          rewrite filter_pred_not_eq.
          erewrite Zcount_filter_partition with
            (p := fun v => match interp_expr store (map.put env x v)
                                   (EBinop OEq (EAccess (EVar x) s) e2_1_2) with
                           | VBool b => b
                           | _ => false
                           end).
          cbn [interp_binop apply_int_binop]. f_equal. apply Z.add_simpl_l.
        Qed.
      End filter_neq_to_count_sub.

      Ltac invert_tenv_wf_with_globals :=
        lazymatch goal with H: tenv_wf_with_globals _ _ _ |- _ => inversion H; subst end.

      Lemma count_to_agg_lookup_head_sound : forall is_tbl_ty' aux_ty aux_wf,
          aux_ty_for_idx aux_ty ->
          (forall t, is_tbl_ty' t = true -> is_tbl_ty t = true) ->
          (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
          expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf count_to_agg_lookup_head.
      Proof.
        unfold aux_ty_for_idx, expr_aug_transf_sound; intros.
        invert_tenv_wf_with_globals.
        specialize (H tbl_ty). repeat destruct_match_hyp; intuition idtac.
        1: eapply count_to_agg_lookup_head_preserve_ty; eauto.
        1: eapply count_to_agg_lookup_head_preserve_sem; eauto.
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

      Lemma cons_to_incr_head_sound :
        expr_transf_sound (locals:=locals) cons_to_incr_head.
      Proof.
        unfold expr_transf_sound; intros.
        intuition idtac.
        1: eapply cons_to_incr_head_preserve_ty; eauto.
        1: eapply cons_to_incr_head_preserve_sem; [ | | eauto .. ]; auto.
      Qed.

      Lemma filter_neq_to_count_sub_head_sound :
        expr_transf_sound (locals:=locals) filter_neq_to_count_sub_head.
      Proof.
        unfold expr_transf_sound; intros.
        intuition idtac.
        1: eapply filter_neq_to_count_sub_head_preserve_ty; eauto.
        1: eapply filter_neq_to_count_sub_head_preserve_sem; [ | | eauto .. ]; auto.
      Qed.
    End WithTags.
  End WithMap.
End WithHole.

#[export] Hint Resolve cons_to_incr_head_sound : transf_hints.
#[export] Hint Resolve filter_neq_to_count_sub_head_sound : transf_hints.
#[export] Hint Resolve count_to_agg_lookup_head_sound : transf_hints.

#[export] Hint Extern 5 (type_of _ _ IndexInterface.to_idx _) => apply CountAgg.to_idx_ty : transf_hints.
