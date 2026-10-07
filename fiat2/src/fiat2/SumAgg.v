Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute fiat2.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.


Section WithHole.
  Context (hole : string).
  Context (attr : string).

  Section WithVars.
    Context (tup acc x : string).
    Context (H_NoDup : is_NoDup_opaque [tup; acc; x]).

    Definition to_idx : expr :=
      EACFold AGSum (flatmap_proj_bag (EBagOf (EVar hole)) x (EAccess (EVar x) attr) None).

    Definition is_tbl_ty (t : type) : bool :=
      match t with
      | TList (TRecord rt) => match access_record rt attr with
                              | Success t => type_eqb t TInt
                              | _ => false
                              end
      | _ => false
      end.

    Definition idx_ty (t : type) : type := TInt.

    Lemma idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t).
      intros; constructor.
    Qed.

    Section WithMap.
      Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
      Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
      Notation value := (value (width:=width)).
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


      Instance sum_agg : IndexInterface.index := IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

      Instance sum_agg_ok : IndexInterface.ok sum_agg idx_wf :=
        IndexInterface.Build_ok sum_agg idx_wf idx_ty_wf to_idx_ty to_idx_wf.

      Ltac apply_int_binop_Z_add_AC :=
        intros; unfold apply_int_binop;
        repeat case_match; auto;
        rewrite !Z.add_assoc;
        lazymatch goal with
          |- context[(?z + _ + _)%Z] =>
            rewrite (Z.add_comm z)
        end; reflexivity.

      Notation proj_attr :=
        (fun v => match v with VRecord r => record_proj attr r | _ => VUnit end).
      Notation int_of := (fun v : value => match v with VInt z => z | _ => 0%Z end).

      (* a fold of integer addition over integers *)
      Lemma fold_add_int : forall (l : list value),
          Forall (fun v => type_of_value v TInt) l ->
          fold_right (apply_int_binop Z.add) (VInt 0) l
          = VInt (fold_right Z.add 0%Z (List.map int_of l)).
      Proof.
        induction l as [| v l IH]; cbn; auto; intros.
        invert_Forall.
        lazymatch goal with H: type_of_value v TInt |- _ => inversion H; subst end.
        rewrite IH; auto.
      Qed.

      (* a sum splits over a filter and its complement *)
      Lemma Zsum_filter_partition : forall (h : value -> Z) (p : value -> bool) l,
          fold_right Z.add 0%Z (List.map h l)
          = (fold_right Z.add 0%Z (List.map h (filter p l))
             + fold_right Z.add 0%Z (List.map h (filter (fun v => negb (p v)) l)))%Z.
      Proof.
        induction l as [| v l IH]; cbn; auto; intros.
        rewrite IH. destruct (p v); cbn.
        1: apply Z.add_assoc.
        1: apply Z.add_shuffle3.
      Qed.

      (* a sum does not depend on the order of the rows *)
      Lemma Zsum_Permutation : forall (h : value -> Z) l1 l2,
          Permutation l1 l2 ->
          fold_right Z.add 0%Z (List.map h l1) = fold_right Z.add 0%Z (List.map h l2).
      Proof.
        intros. apply List.fold_right_change_order.
        1: intros; rewrite !Z.add_assoc, (Z.add_comm a1); reflexivity.
        1: apply Permutation_map; auto.
      Qed.

      (* the sum of an attribute over a bag of rows *)
      Lemma interp_sum_proj_bag : forall (store env : locals) eb lb tl x t,
          interp_expr store env eb = VBag lb ->
          Forall (fun v => type_of_value v (TRecord tl)) (bag_to_list lb) ->
          access_record tl attr = Success TInt ->
          interp_expr store env (EACFold AGSum (flatmap_proj_bag eb x (EAccess (EVar x) attr) t))
          = VInt (fold_right Z.add 0%Z
                    (List.map (fun v => int_of (proj_attr v)) (bag_to_list lb))).
      Proof.
        intros * H_e H_l H_attr.
        rewrite interp_EACFold, interp_flatmap_proj_bag, H_e. cbn [interp_aggr].
        erewrite List.fold_right_change_order;
          [ | apply_int_binop_Z_add_AC | apply list_to_bag_to_list_Permutation ].
        cbn [interp_expr]. rewrite map_proj_put, fold_add_int.
        2: eapply Forall_map_record_proj; eauto.
        f_equal. rewrite map_map. reflexivity.
      Qed.

      (* the sum of an attribute over a list of rows *)
      Lemma interp_sum_proj_list : forall (store env : locals) e l tl x t,
          interp_expr store env e = VList l ->
          Forall (fun v => type_of_value v (TRecord tl)) l ->
          access_record tl attr = Success TInt ->
          interp_expr store env
            (EACFold AGSum (flatmap_proj_bag (EBagOf e) x (EAccess (EVar x) attr) t))
          = VInt (fold_right Z.add 0%Z (List.map (fun v => int_of (proj_attr v)) l)).
      Proof.
        intros * H_e H_l H_attr.
        erewrite interp_sum_proj_bag;
          [ | rewrite interp_EBagOf, H_e; reflexivity
            | eapply Permutation_Forall;
              [ apply Permutation_sym, list_to_bag_to_list_Permutation | eauto ]
            | eauto ].
        f_equal. apply Zsum_Permutation, list_to_bag_to_list_Permutation.
      Qed.

      (* the sum of an attribute over the rows a predicate keeps *)
      Lemma interp_sum_proj_filter_bag : forall (store env : locals) e l tl x y p t1 t2 t,
          interp_expr store env e = VList l ->
          Forall (fun v => type_of_value v (TRecord tl)) l ->
          access_record tl attr = Success TInt ->
          interp_expr store env
            (EACFold AGSum
               (flatmap_proj_bag (flatmap_filter_bag (EBagOf e) y p y t1 t2)
                  x (EAccess (EVar x) attr) t))
          = VInt (fold_right Z.add 0%Z
                    (List.map (fun v => int_of (proj_attr v))
                       (filter (fun v => match interp_expr store (map.put env y v) p with
                                         | VBool b => b
                                         | _ => false
                                         end) l))).
      Proof.
        intros * H_e H_l H_attr.
        assert (H_perm : Permutation
                           (bag_to_list
                              (list_to_bag
                                 (filter (fun v => match interp_expr store (map.put env y v) p with
                                                   | VBool b => b
                                                   | _ => false
                                                   end)
                                    (bag_to_list (list_to_bag l)))))
                           (filter (fun v => match interp_expr store (map.put env y v) p with
                                             | VBool b => b
                                             | _ => false
                                             end) l)).
        1:{ eapply perm_trans; [ apply list_to_bag_to_list_Permutation | ].
            apply Permutation_filter; auto using list_to_bag_to_list_Permutation. }
        erewrite interp_sum_proj_bag;
          [ | rewrite interp_flatmap_filter_bag, interp_EBagOf, H_e; reflexivity
            | eapply Permutation_Forall; [ apply Permutation_sym, H_perm | ]
            | eauto ].
        1: f_equal; apply Zsum_Permutation, H_perm.
        eapply incl_Forall; [ apply incl_filter | eauto ].
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

        Section sum_to_agg_lookup.
          Context (tbl : string).

          Definition sum_to_agg_lookup_head (e : expr) :=
            match e with
            | EACFold AGSum (flatmap_proj_bag (EBagOf (EAccess (ELoc tbl0) id_tag0)) x0 (EAccess (EVar x1) attr0) _) =>
                if all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x0, [x1]); (id_tag, [id_tag0]); (x0, [x1])]
                then EAccess (EAccess (ELoc tbl) aux_tag) idx_tag
                else e
            | _ => e
            end.

          Lemma sum_to_agg_lookup_head_preserve_ty : forall tl t aux_tl (Gstore : tenv),
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              preserve_ty Gstore (sum_to_agg_lookup_head).
          Proof.
            clear H_NoDup.
            unfold preserve_ty, is_tbl_ty. intros.
            repeat destruct_match_hyp; try congruence.
            repeat destruct_subexpr. simpl.
            case_match; auto. repeat rewrite Bool.andb_true_r in *.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac. rewrite eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear. repeat rewrite_map_get_put_hyp.
            invert_type_of_aggr_clear.
            repeat (clear_refl; repeat do_injection2).
            repeat (rewrite_l_to_r; do_injection2).
            repeat (econstructor; eauto).
          Qed.

          Lemma sum_to_agg_lookup_head_preserve_sem : forall (Gstore : tenv) (store : locals) tl t aux_tl,
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              match map.get store tbl with
              | Some v => aux_wf_for_idx v
              | _ => False
              end ->
              preserve_sem Gstore store sum_to_agg_lookup_head.
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
            repeat destruct_subexpr. unfold sum_to_agg_lookup_head.
            simpl; case_match; auto.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            rewrite eqb_eq in *; subst. repeat clear_refl.
            unfold idx_wf in *.
            repeat rewrite_l_to_r.
            cbn. unfold get_local. rewrite_l_to_r. unfold record_proj.
            repeat rewrite_l_to_r. unfold to_idx.
            cbn. unfold get_local. unfold record_proj.
            rewrite_map_get_put_goal.
            do 3 f_equal. apply In_flat_map_ext.
            intros. repeat rewrite_map_get_put_goal. reflexivity.
          Qed.
        End sum_to_agg_lookup.

        Section cons_to_add.
          Definition cons_to_add_head (e : expr) :=
            match e with
            | EACFold AGSum (flatmap_proj_bag (EBagOf (EBinop OCons e1 e2)) x0 e3 t) =>
                EBinop OPlus (ELet e1 x0 e3) (EACFold AGSum (flatmap_proj_bag (EBagOf e2) x0 e3 t))
            | _ => e
            end.

          Lemma cons_to_add_head_preserve_ty : forall (Gstore : tenv),
              preserve_ty Gstore cons_to_add_head.
          Proof.
            unfold preserve_ty; intros. repeat destruct_subexpr.
            cbn. repeat (case_match; auto).
            repeat invert_type_of_clear.
            repeat invert_type_of_op_clear.
            invert_type_of_aggr_clear.
            repeat (econstructor; eauto);
              repeat rewrite_map_get_put_goal; auto;
              try use_is_NoDup.
            all: repeat eapply not_free_immut_put_ty2; eauto.
          Qed.

          Lemma cons_to_add_head_preserve_sem : forall (Gstore : tenv) (store : locals),
              preserve_sem Gstore store cons_to_add_head.
          Proof.
            unfold preserve_sem; intros. repeat destruct_subexpr.
            cbn [cons_to_add_head]. repeat (case_match; auto; []).
            cbn in * |-.
            repeat invert_type_of_clear.
            repeat invert_type_of_op_clear.
            cbn.
            apply_type_sound e1_2.
            invert_type_of_value_clear.
            erewrite List.fold_right_change_order;
            [
            | apply_int_binop_Z_add_AC
            | apply list_to_bag_to_list_Permutation ].
            let pat := open_constr:(bag_to_list (list_to_bag _)) in
            erewrite List.fold_right_change_order with (l1:=pat);
            [
            | apply_int_binop_Z_add_AC | ].
            2:{ eapply perm_trans.
                1: apply list_to_bag_to_list_Permutation.
                eapply Permutation_map, list_to_bag_to_list_Permutation. }
            cbn.
            f_equal.
            erewrite List.fold_right_change_order;
            [
            | apply_int_binop_Z_add_AC
            | eapply Permutation_map, list_to_bag_to_list_Permutation ].
            reflexivity.
          Qed.
        End cons_to_add.

        Section filter_neq_to_sub.
          Definition filter_neq_to_sub_head (e : expr) :=
            match e with
            | EACFold AGSum
                (flatmap_proj_bag
                   (EBagOf (flatmap_filter_list e' y
                              (EUnop ONot (EBinop OEq (EAccess (EVar y0) attr1) k)) y1 t1 t2))
                   x0 (EAccess (EVar x1) attr0) t) =>
                (* the delete's attribute need not be the one being summed *)
                if all_eqb [(attr, [attr0]); (x0, [x1]); (y, [y0; y1])]
                then EBinop OMinus
                       (EACFold AGSum (flatmap_proj_bag (EBagOf e') x0 (EAccess (EVar x0) attr) t))
                       (EACFold AGSum
                          (flatmap_proj_bag
                             (flatmap_filter_bag (EBagOf e') y
                                (EBinop OEq (EAccess (EVar y) attr1) k) y None None)
                             x0 (EAccess (EVar x0) attr) t))
                else e
            | _ => e
            end.

          Lemma filter_neq_to_sub_head_preserve_ty : forall (Gstore : tenv),
              preserve_ty Gstore filter_neq_to_sub_head.
          Proof.
            unfold preserve_ty; intros. repeat destruct_subexpr.
            cbn. repeat (case_match; auto).
            cbn [all_eqb all_eqb' andb] in *.
            rewrite !Bool.andb_true_r, !Bool.andb_true_iff in *; intuition idtac.
            rewrite eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear.
            lazymatch goal with H: type_of_aggr _ _ _ |- _ => inversion H; subst end.
            repeat rewrite_map_get_put_hyp.
            econstructor.
            1: constructor.
            (* the sum over the whole table *)
            1:{ repeat (econstructor; eauto);
                repeat rewrite_map_get_put_goal; auto; congruence. }
            (* the sum over the rows that carry the key; the bag's element type comes
               from the table, so that the empty-bag annotations are determined *)
            1:{ econstructor; [ constructor | ].
                lazymatch goal with
                | H: type_of _ _ e1_1 (TList ?rt) |- _ =>
                    assert (type_wf rt) by (apply type_of__type_wf in H; auto;
                                            invert_type_wf; auto);
                    eapply TyEFlatmap_Bag with (t1 := rt);
                    [ eapply TyEFlatmap_Bag with (t1 := rt) (t2 := rt) | ]
                end.
                all: repeat (econstructor; eauto);
                  repeat rewrite_map_get_put_goal; auto; try congruence.
                }
          Qed.

          Lemma filter_neq_to_sub_head_preserve_sem : forall (Gstore : tenv) (store : locals),
              preserve_sem Gstore store filter_neq_to_sub_head.
          Proof.
            unfold preserve_sem; intros. repeat destruct_subexpr.
            cbn [filter_neq_to_sub_head]. repeat (case_match; auto; []).
            cbn [all_eqb all_eqb' andb] in *.
            rewrite !Bool.andb_true_r, !Bool.andb_true_iff in *; intuition idtac.
            rewrite eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear.
            lazymatch goal with H: type_of_aggr _ _ _ |- _ => inversion H; subst end.
            repeat rewrite_map_get_put_hyp.
            (* the filtered row and the projected row are the same record *)
            repeat lazymatch goal with
                   | H: Some _ = Some _ |- _ => injection H as H
                   | H: TRecord _ = TRecord _ |- _ => injection H as H
                   end; subst.
            repeat (rewrite_l_to_r; do_injection).
            apply_type_sound e1_1. invert_type_of_value_clear.
            lazymatch goal with
            | H: VList ?ll = interp_expr store env e1_1 |- _ =>
                assert (H_tbl : interp_expr store env e1_1 = VList ll) by (symmetry; exact H)
            end.
            assert (H_rest : interp_expr store env
                      (flatmap_filter_list e1_1 x1
                         (EUnop ONot (EBinop OEq (EAccess (EVar x1) s) e1_2_1_2)) x1 t0 t1)
                    = VList (filter (fun v => match interp_expr store (map.put env x1 v)
                                                      (EUnop ONot
                                                         (EBinop OEq (EAccess (EVar x1) s)
                                                            e1_2_1_2)) with
                                              | VBool b => b
                                              | _ => false
                                              end) l))
              by (rewrite interp_flatmap_filter_list, H_tbl; reflexivity).
            (* the sum over the whole table, over the rows carrying the key, and over
               the rows that survive *)
            rewrite interp_EBinop.
            erewrite interp_sum_proj_list with (e := e1_1); eauto.
            erewrite interp_sum_proj_filter_bag with (e := e1_1); eauto.
            erewrite interp_sum_proj_list;
              [ | exact H_rest | eapply Forall_Forall_filter; eauto | eauto ].
            (* a sum splits over the delete's predicate and its complement *)
            rewrite filter_pred_not_eq.
            erewrite Zsum_filter_partition with
              (p := fun v => match interp_expr store (map.put env x1 v)
                                     (EBinop OEq (EAccess (EVar x1) s) e1_2_1_2) with
                             | VBool b => b
                             | _ => false
                             end).
            cbn [interp_binop apply_int_binop]. f_equal. apply Z.add_simpl_l.
          Qed.
        End filter_neq_to_sub.

        Ltac invert_tenv_wf_with_globals :=
          lazymatch goal with H: tenv_wf_with_globals _ _ _ |- _ => inversion H; subst end.

        Lemma sum_to_agg_lookup_head_sound : forall is_tbl_ty' aux_ty aux_wf,
            aux_ty_for_idx aux_ty ->
            (forall t, is_tbl_ty' t = true -> is_tbl_ty t = true) ->
            (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
            expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf sum_to_agg_lookup_head.
        Proof.
          unfold aux_ty_for_idx, expr_aug_transf_sound; intros.
          invert_tenv_wf_with_globals.
          specialize (H tbl_ty). repeat destruct_match_hyp; intuition idtac.
          1: eapply sum_to_agg_lookup_head_preserve_ty; eauto.
          1: eapply sum_to_agg_lookup_head_preserve_sem; eauto.
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

          Lemma cons_to_add_head_sound :
            expr_transf_sound (locals:=locals) cons_to_add_head.
          Proof.
            unfold expr_transf_sound; intros.
            intuition idtac.
            1: eapply cons_to_add_head_preserve_ty; eauto.
            1: eapply cons_to_add_head_preserve_sem; [ | | eauto .. ]; auto.
          Qed.

          Lemma filter_neq_to_sub_head_sound :
            expr_transf_sound (locals:=locals) filter_neq_to_sub_head.
          Proof.
            unfold expr_transf_sound; intros.
            intuition idtac.
            1: eapply filter_neq_to_sub_head_preserve_ty; eauto.
            1: eapply filter_neq_to_sub_head_preserve_sem; [ | | eauto .. ]; auto.
          Qed.
      End WithTags.
    End WithMap.
  End WithVars.
End WithHole.

#[export] Hint Resolve cons_to_add_head_sound : transf_hints.
#[export] Hint Resolve filter_neq_to_sub_head_sound : transf_hints.
#[export] Hint Resolve sum_to_agg_lookup_head_sound : transf_hints.

#[export] Hint Extern 5 (type_of _ _ IndexInterface.to_idx _) => apply SumAgg.to_idx_ty : transf_hints.
