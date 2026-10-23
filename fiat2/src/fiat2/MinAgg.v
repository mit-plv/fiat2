Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute fiat2.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.


Section WithHole.
  Context (hole : string).
  Context (attr : string).

  Section WithVars.
    Context (x : string).

    Definition to_idx : expr :=
      EACIFold AGMin (flatmap_proj_set (ESetOf (EVar hole)) x (EAccess (EVar x) attr) None).

    Definition is_tbl_ty (t : type) : bool :=
      match t with
      | TList (TRecord rt) => match access_record rt attr with
                              | Success t => type_eqb t TInt
                              | _ => false
                              end
      | _ => false
      end.

    Definition idx_ty (t : type) : type := TOption TInt.

    Lemma idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t).
      intros; repeat constructor.
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
        rewrite type_eqb_eq in *; subst.
        repeat econstructor; repeat rewrite_map_get_put_goal; eauto.
      Qed.

      Lemma to_idx_wf : forall (v : value) (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          idx_wf v (interp_expr map.empty (map.put map.empty hole v) to_idx).
      Proof.
        unfold idx_wf; intros; auto.
      Qed.


      Instance min_agg : IndexInterface.index := IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

      Instance min_agg_ok : IndexInterface.ok min_agg idx_wf :=
        IndexInterface.Build_ok min_agg idx_wf idx_ty_wf to_idx_ty to_idx_wf.

      Local Coercion is_true : bool >-> Sortclass.

      (* The canonical form of a set is sorted, so the minimum fold returns the
         first element.  This is a fact about the canonical form the semantics
         gives a set, not a claim about how an implementation represents one. *)
      Lemma interp_EACIFold_AGMin_sorted : forall (store env : locals) e l,
          interp_expr store env e = VSet l ->
          Forall (fun v => type_of_value v TInt) l ->
          StronglySorted value_leb l ->
          interp_expr store env (EACIFold AGMin e)
          = match l with
            | nil => VOption None
            | v :: _ => VOption (Some v)
            end.
      Proof.
        intros * H_e H_ty H_sorted. cbn [interp_expr interp_aci_aggr].
        rewrite H_e. clear H_e.
        induction l as [| v l IH]; auto.
        invert_Forall. invert_SSorted.
        cbn [fold_right]. rewrite IH; auto.
        destruct l as [| w l']; cbn [fst snd].
        1: reflexivity.
        invert_Forall.
        lazymatch goal with H: Forall _ (_ :: _) |- _ => inversion H; subst end.
        (* v and its successor are both integers, and v is the smaller *)
        lazymatch goal with H: type_of_value v TInt |- _ => inversion H; subst end.
        lazymatch goal with H: type_of_value w TInt |- _ => inversion H; subst end.
        cbn [snd]. do 3 f_equal.
        unfold value_leb, leb_from_compare in *; cbn [value_compare] in *.
        lazymatch goal with |- Z.min ?a ?b = ?a => destruct (Z.compare_spec a b) end;
          try discriminate.
        1: subst; apply Z.min_id.
        1: apply Z.min_l, Z.lt_le_incl; auto.
      Qed.

      (* Deleting every row whose attribute is k only disturbs the minimum when
         the minimum is k itself. *)
      Lemma min_set_map_filter_neq : forall (f : value -> value) k l,
          match list_to_set (List.map f (filter (fun v => negb (value_eqb (f v) k)) l)) with
          | nil => VOption None
          | v :: _ => VOption (Some v)
          end
          = match list_to_set (List.map f l) with
            | nil => VOption None
            | v :: _ =>
                if value_eqb v k
                then match list_to_set
                            (List.map f (filter (fun v => negb (value_eqb (f v) k)) l)) with
                     | nil => VOption None
                     | w :: _ => VOption (Some w)
                     end
                else VOption (Some v)
            end.
      Proof.
        intros. rewrite <- filter_list_to_set_map.
        destruct (list_to_set (List.map f l)) as [| v s] eqn:E; auto.
        cbn [filter]. destruct (value_eqb v k) eqn:E2; cbn [negb]; auto.
      Qed.

      Notation proj_attr :=
        (fun v => match v with
                  | VRecord r => record_proj attr r
                  | _ => VUnit
                  end).

      (* the minimum of an attribute over a table, in terms of the table's rows *)
      Lemma interp_min_proj : forall (store env : locals) e l tl x t,
          interp_expr store env e = VList l ->
          Forall (fun v => type_of_value v (TRecord tl)) l ->
          access_record tl attr = Success TInt ->
          interp_expr store env
            (EACIFold AGMin (flatmap_proj_set (ESetOf e) x (EAccess (EVar x) attr) t))
          = match list_to_set (List.map proj_attr l) with
            | nil => VOption None
            | v :: _ => VOption (Some v)
            end.
      Proof.
        intros * H_e H_l H_attr.
        erewrite interp_EACIFold_AGMin_sorted;
          eauto using list_to_set_SSorted.
        1:{ rewrite interp_flatmap_proj_set, interp_ESetOf, H_e.
            cbn [interp_expr]. rewrite map_proj_put, list_to_set_map_list_to_set.
            reflexivity. }
        1:{ eapply incl_Forall; [ apply list_to_set_incl | ].
            eapply Forall_map_record_proj; eauto. }
      Qed.

      Ltac invert_type_of_aci_aggr_clear :=
        lazymatch goal with
        | H: type_of_aci_aggr _ _ _ |- _ =>
            inversion H; subst
        end.

      Section WithTags.
        Context (id_tag aux_tag idx_tag: string).

        Notation aux_ty_for_idx := (aux_ty_for_idx id_tag aux_tag idx_tag idx_ty).
        Notation aux_wf_for_idx := (aux_wf_for_idx id_tag aux_tag idx_tag idx_wf).

        Section min_to_agg_lookup.
          Context (tbl : string).

          Definition min_to_agg_lookup_head (e : expr) :=
            match e with
            | EACIFold AGMin (flatmap_proj_set (ESetOf (EAccess (ELoc tbl0) id_tag0)) x0 (EAccess (EVar x1) attr0) _) =>
                if all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x0, [x1]); (id_tag, [id_tag0]); (x0, [x1])]
                then EAccess (EAccess (ELoc tbl) aux_tag) idx_tag
                else e
            | _ => e
            end.

          Lemma min_to_agg_lookup_head_preserve_ty : forall tl t aux_tl (Gstore : tenv),
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              preserve_ty Gstore (min_to_agg_lookup_head).
          Proof.
            unfold preserve_ty, is_tbl_ty. intros.
            repeat destruct_match_hyp; try congruence.
            repeat destruct_subexpr. simpl.
            repeat case_match; auto.
            rewrite !Bool.andb_true_r, !Bool.andb_true_iff in *; intuition idtac. rewrite eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear. repeat rewrite_map_get_put_hyp.
            invert_type_of_aci_aggr_clear.
            repeat (clear_refl; repeat do_injection2).
            repeat (rewrite_l_to_r; do_injection2).
            repeat (econstructor; eauto).
          Qed.

          Lemma min_to_agg_lookup_head_preserve_sem : forall (Gstore : tenv) (store : locals) tl t aux_tl,
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              match map.get store tbl with
              | Some v => aux_wf_for_idx v
              | _ => False
              end ->
              preserve_sem Gstore store min_to_agg_lookup_head.
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
            repeat destruct_subexpr. unfold min_to_agg_lookup_head.
            simpl; repeat (case_match; auto; []).
            rewrite !Bool.andb_true_iff in *; intuition idtac.
            rewrite eqb_eq in *; subst. repeat clear_refl.
            cbn in * |-; invert_pair. unfold idx_wf in *.
            repeat rewrite_l_to_r.
            cbn. unfold get_local. rewrite_l_to_r. unfold record_proj.
            repeat rewrite_l_to_r. unfold to_idx.
            cbn. unfold get_local. unfold record_proj.
            rewrite_map_get_put_goal.
            erewrite In_flat_map_ext; eauto.
            intros. repeat rewrite_map_get_put_goal. reflexivity.
          Qed.
        End min_to_agg_lookup.

        Section cons_to_min.
          Context (y : string).

          Definition cons_to_min_head (e : expr) :=
            match e with
            | EACIFold AGMin (flatmap_proj_set (ESetOf (EBinop OCons e1 e2)) x0 e3 t) =>
                if (negb (y =? x0) && negb (free_immut_in y e2)
                   && negb (free_immut_in y e3))%bool
                then
                ELet (ELet e1 x0 e3) y
                  (EOptMatch (EACIFold AGMin (flatmap_proj_set (ESetOf e2) x0 e3 t)) (EUnop OSome (EVar y))
                     x0 (EIf (EBinop OLess (EVar y) (EVar x0)) (EUnop OSome (EVar y)) (EUnop OSome (EVar x0))))
                else e
            | _ => e
            end.

          Lemma cons_to_min_head_preserve_ty : forall (Gstore : tenv),
              preserve_ty Gstore cons_to_min_head.
          Proof.
            unfold preserve_ty; intros. repeat destruct_subexpr.
            cbn. repeat (case_match; auto).
            repeat invert_type_of_clear.
            repeat invert_type_of_op_clear.
            invert_type_of_aci_aggr_clear.
            rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition idtac.
            rewrite eqb_neq in *.
            repeat (econstructor; eauto);
              repeat rewrite_map_get_put_goal; auto.
            1:{ eapply not_free_immut_put_ty2; eauto. }
            1:{ rewrite Properties.map.put_put_diff_comm; auto.
                eapply not_free_immut_put_ty2; eauto. }
          Qed.

          Lemma cons_to_min_head_preserve_sem : forall (Gstore : tenv) (store : locals),
              preserve_sem Gstore store cons_to_min_head.
          Proof.
            unfold preserve_sem; intros. repeat destruct_subexpr.
            cbn [cons_to_min_head]. repeat (case_match; auto; []).
            repeat invert_type_of_clear.
            repeat invert_type_of_op_clear.
            invert_type_of_aci_aggr_clear.
            rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition idtac.
            rewrite eqb_neq in *.
            cbn. rewrite_flat_map_singleton.
            rewrite <- not_free_immut_put_sem; auto.
            apply_type_sound e1_2.
            invert_type_of_value_clear.
            unfold get_local. rewrite_map_get_put_goal.
            rewrite aci_aggr_alt.
            2:{ eapply incl_Forall; [ apply list_to_set_incl | ].
                eapply incl_Forall; [ apply incl_map, list_to_set_incl | ].
                rewrite Forall_map.
                rewrite Forall_forall; intros; apply_Forall_In.
                rewrite Properties.map.put_put_diff_comm; auto.
                rewrite <- not_free_immut_put_sem; auto.
                apply_type_sound e1_4; eauto with fiat2_hints. }
            rewrite aci_aggr_alt.
            2:{ eapply incl_Forall; [ apply list_to_set_incl | ].
                eapply incl_Forall; [ apply incl_map, list_to_set_incl | ].
                rewrite Forall_map.
                constructor.
                1: apply_type_sound e1_1;
                apply_type_sound e1_4; eauto with fiat2_hints.
                rewrite Forall_forall; intros; apply_Forall_In.
                apply_type_sound e1_4; eauto with fiat2_hints. }
            erewrite fold_right_change_order_idem.
            2:{ intros. repeat case_match; auto; do 3 f_equal.
                1: rewrite !Z.min_assoc;
                rewrite (Z.min_comm z); reflexivity.
                1: apply Z.min_comm. }
            2:{ intros. repeat case_match; auto; do 3 f_equal.
                1: rewrite Z.min_assoc, Z.min_id; reflexivity.
                1: apply Z.min_id. }
            2:{ eapply incl_tran; [ apply list_to_set_incl | ]. apply incl_map, list_to_set_incl. }
            2:{ eapply incl_tran; [ apply incl_map, list_to_set_incl_r | ].
                apply list_to_set_incl_r. }
            let pat := open_constr:(list_to_set _) in
            erewrite fold_right_change_order_idem with (l1:=pat).
            2:{ intros. repeat case_match; auto; do 3 f_equal.
                1: rewrite !Z.min_assoc;
                rewrite (Z.min_comm z); reflexivity.
                1: apply Z.min_comm. }
            2:{ intros. repeat case_match; auto; do 3 f_equal.
                1: rewrite Z.min_assoc, Z.min_id; reflexivity.
                1: apply Z.min_id. }
            2:{ eapply incl_tran; [ apply list_to_set_incl | ]. apply incl_map, list_to_set_incl. }
            2:{ eapply incl_tran; [ apply incl_map, list_to_set_incl_r | ].
                apply list_to_set_incl_r. }
            cbn. apply_type_sound e1_1.
            apply_type_sound e1_4; eauto with fiat2_hints.
            lazymatch goal with
              H: type_of_value _ TInt |- _ =>
                inversion H; subst
            end.
            lazymatch goal with
              |- match ?x with _ => _ end = match ?y with _ => _ end =>
                assert (x = y) end.
            1:{ f_equal. apply map_ext_in. intros.
                rewrite Properties.map.put_put_diff_comm; auto.
                rewrite <- not_free_immut_put_sem; auto. }
            repeat rewrite_l_to_r. repeat (case_match; auto; []).
            repeat rewrite_map_get_put_goal.
            lazymatch goal with
              H: VInt _ = _ |- _ => rewrite <- H end.
            repeat case_match; auto;
              do 3 f_equal; unfold Z.ltb, Z.min in *; case_match;
              rewrite ?Z.compare_eq_iff in *; congruence.
          Qed.
        End cons_to_min.

        Section filter_neq_to_min_guard.
          Context (m : string).

          Definition filter_neq_to_min_guard_head (e : expr) :=
            match e with
            | EACIFold AGMin
                (flatmap_proj_set
                   (ESetOf (flatmap_filter_list e' y
                              (EUnop ONot (EBinop OEq (EAccess (EVar y0) attr1) k)) y1 t1 t2))
                   x0 (EAccess (EVar x1) attr0) t) =>
                if (all_eqb [(attr, [attr0; attr1]); (x0, [x1]); (y, [y0; y1])] &&
                      negb (free_immut_in y k) &&
                      negb (free_immut_in m k) && negb (free_immut_in m e'))%bool
                then
                  EOptMatch
                    (EACIFold AGMin
                       (flatmap_proj_set (ESetOf e') x0 (EAccess (EVar x0) attr) t))
                    (EAtom (ANone (Some TInt))) m
                    (EIf (EBinop OEq (EVar m) k)
                       (EACIFold AGMin
                          (flatmap_proj_set
                             (ESetOf (flatmap_filter_list e' y
                                        (EUnop ONot (EBinop OEq (EAccess (EVar y) attr) k)) y t1 t2))
                             x0 (EAccess (EVar x0) attr) t))
                       (EUnop OSome (EVar m)))
                else e
            | _ => e
            end.

          Lemma filter_neq_to_min_guard_head_preserve_ty : forall (Gstore : tenv),
              preserve_ty Gstore filter_neq_to_min_guard_head.
          Proof.
            unfold preserve_ty; intros. repeat destruct_subexpr.
            cbn. repeat (case_match; auto).
            cbn [all_eqb all_eqb' andb] in *.
            rewrite !Bool.andb_true_r, !Bool.andb_true_iff, !Bool.negb_true_iff in *;
              intuition idtac.
            rewrite eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear.
            repeat rewrite_map_get_put_hyp.
            (* the filter's row and the projected row are the same record *)
            repeat lazymatch goal with
                   | H: Some _ = Some _ |- _ => injection H as H
                   | H: TRecord _ = TRecord _ |- _ => injection H as H
                   end; subst.
            lazymatch goal with H: type_of_aci_aggr _ _ _ |- _ => inversion H; subst end.
            repeat (rewrite_l_to_r; do_injection).
            repeat (econstructor; eauto); repeat rewrite_map_get_put_goal; eauto.
            (* the key is compared against the attribute, so it is an integer,
               and it mentions neither the filtered row nor the bound minimum *)
            1:{ apply not_free_immut_put_ty2; auto.
                eapply not_free_immut_put_ty; [ eassumption | ].
                lazymatch goal with
                | H: type_of _ (map.put _ _ _) e2_2 ?t2 |- type_of _ _ _ ?t1 =>
                    replace t1 with t2 by congruence; exact H
                end. }
            (* the table does not mention the bound minimum *)
            1: apply not_free_immut_put_ty2; auto.
            (* the key again, now under the filter's row as well *)
            1:{ lazymatch goal with
                | |- type_of _ (map.put (map.put _ ?mm _) ?yy _) _ _ =>
                    destruct (String.eqb mm yy) eqn:E_m;
                    [ rewrite eqb_eq in E_m; subst;
                      rewrite Properties.map.put_put_same; assumption
                    | rewrite eqb_neq in E_m;
                      rewrite Properties.map.put_put_diff_comm by auto;
                      apply not_free_immut_put_ty2; auto ]
                end. }
          Qed.

          Lemma filter_neq_to_min_guard_head_preserve_sem : forall (Gstore : tenv) (store : locals),
              preserve_sem Gstore store filter_neq_to_min_guard_head.
          Proof.
            unfold preserve_sem; intros. repeat destruct_subexpr.
            cbn [filter_neq_to_min_guard_head]. repeat (case_match; auto; []).
            cbn [all_eqb all_eqb' andb] in *.
            rewrite !Bool.andb_true_r, !Bool.andb_true_iff, !Bool.negb_true_iff in *;
              intuition idtac.
            rewrite eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear.
            repeat lazymatch goal with
                   | H: Some _ = Some _ |- _ => injection H as H
                   | H: TRecord _ = TRecord _ |- _ => injection H as H
                   end; subst.
            lazymatch goal with H: type_of_aci_aggr _ _ _ |- _ => inversion H; subst end.
            repeat (rewrite_l_to_r; do_injection).
            repeat rewrite_map_get_put_hyp.
            repeat (clear_refl; repeat do_injection).
            apply_type_sound e1_1. invert_type_of_value_clear.
            (* the rows that survive the delete *)
            assert (H_filt : interp_expr store env
                      (flatmap_filter_list e1_1 x1
                         (EUnop ONot (EBinop OEq (EAccess (EVar x1) attr) e2_2)) x1 t0 t1)
                    = VList (filter (fun v => negb (value_eqb (proj_attr v)
                                                     (interp_expr store env e2_2))) l)).
            1:{ rewrite interp_flatmap_filter_list, <- H1.
                f_equal. apply filter_pred_neq; auto. }
            rewrite interp_EOptMatch.
            erewrite interp_min_proj with (e := e1_1) (l := l); eauto.
            erewrite interp_min_proj; eauto using Forall_Forall_filter.
            rewrite min_set_map_filter_neq.
            destruct (list_to_set (List.map proj_attr l)) as [| v s] eqn:E.
            1: reflexivity.
            (* the bound minimum is compared against the deleted key *)
            rewrite interp_EIf, interp_EBinop, interp_EVar.
            unfold get_local. rewrite map.get_put_same.
            rewrite <- (not_free_immut_put_sem e2_2 m) by assumption.
            cbn [interp_binop].
            destruct (value_eqb v (interp_expr store env e2_2)).
            2:{ cbn [interp_expr interp_unop]. unfold get_local.
                rewrite map.get_put_same. reflexivity. }
            (* the minimum was deleted, so it is recomputed, and the recomputation
               does not mention the bound minimum *)
            rewrite <- not_free_immut_put_sem.
            2:{ cbn [free_immut_in].
                lazymatch goal with H: free_immut_in m e1_1 = false |- _ => rewrite H end.
                lazymatch goal with H: free_immut_in m e2_2 = false |- _ => rewrite H end.
                destruct (String.eqb m x1), (String.eqb m x0); cbn; auto. }
            erewrite interp_min_proj; eauto using Forall_Forall_filter.
          Qed.
        End filter_neq_to_min_guard.

        Ltac invert_tenv_wf_with_globals :=
          lazymatch goal with H: tenv_wf_with_globals _ _ _ |- _ => inversion H; subst end.

        Lemma min_to_agg_lookup_head_sound : forall is_tbl_ty' aux_ty aux_wf,
            aux_ty_for_idx aux_ty ->
            (forall t, is_tbl_ty' t = true -> is_tbl_ty t = true) ->
            (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
            expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf min_to_agg_lookup_head.
        Proof.
          unfold aux_ty_for_idx, expr_aug_transf_sound; intros.
          invert_tenv_wf_with_globals.
          specialize (H tbl_ty). repeat destruct_match_hyp; intuition idtac.
          1: eapply min_to_agg_lookup_head_preserve_ty; eauto.
          1: eapply min_to_agg_lookup_head_preserve_sem; eauto.
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

        Lemma cons_to_min_head_sound : forall y,
          expr_transf_sound (locals:=locals) (cons_to_min_head y).
        Proof.
          unfold expr_transf_sound; intros.
          intuition idtac.
          1: eapply cons_to_min_head_preserve_ty; eauto.
          1: eapply cons_to_min_head_preserve_sem; [ | | eauto .. ]; auto.
        Qed.

        Lemma filter_neq_to_min_guard_head_sound : forall m,
          expr_transf_sound (locals:=locals) (filter_neq_to_min_guard_head m).
        Proof.
          unfold expr_transf_sound; intros.
          intuition idtac.
          1: eapply filter_neq_to_min_guard_head_preserve_ty; eauto.
          1: eapply filter_neq_to_min_guard_head_preserve_sem; [ | | eauto .. ]; auto.
        Qed.
      End WithTags.
    End WithMap.
  End WithVars.
End WithHole.

#[export] Hint Resolve cons_to_min_head_sound : transf_hints.
#[export] Hint Resolve filter_neq_to_min_guard_head_sound : transf_hints.
#[export] Hint Resolve min_to_agg_lookup_head_sound : transf_hints.

#[export] Hint Extern 5 (type_of _ _ IndexInterface.to_idx _) => apply MinAgg.to_idx_ty : transf_hints.
