Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface2 fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.


Section WithHole.
  Context (hole : string).
  Context (attr : string).

  Section WithVars.
    Context (tup acc x : string).
    Context (H_NoDup : is_NoDup_opaque [tup; acc; x]).

    Definition to_idx : expr :=
      EACFold AGSum (EProj LikeBag (EBagOf (EVar hole)) x (EAccess (EVar x) attr)).

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


      Instance sum_agg : IndexInterface2.index := IndexInterface2.mk hole to_idx idx_ty is_tbl_ty.

      Instance sum_agg_ok : IndexInterface2.ok sum_agg idx_wf :=
        IndexInterface2.Build_ok sum_agg idx_wf idx_ty_wf to_idx_ty to_idx_wf.

      (* ??? move to utils *)
      Lemma Forall2_access_record : forall A A' P l l' x (a : A) (a' : A'),
          Forall2 (fun p p' => fst p = fst p' /\ P (snd p) (snd p')) l l' ->
          access_record l x = Success a ->
          access_record l' x = Success a' ->
          P a a'.
      Proof.
        induction 1; cbn; try discriminate; auto.
        repeat case_match; cbn in *; intuition idtac;
          repeat (try clear_refl; do_injection); subst; auto;
          congruence.
      Qed.

      Ltac invert_type_of_aggr_clear :=
        lazymatch goal with
        | H: type_of_aggr _ _ _ |- _ =>
            inversion H; subst
        end.

      Section WithTags.
        Context (id_tag aux_tag idx_tag: string).

        Definition aux_ty_for_idx (aux_ty : type -> type) : Prop :=
          forall t,
            match aux_ty t with
            | TRecord tl =>
                access_record tl id_tag = Success t /\
                  match access_record tl aux_tag with
                  | Success (TRecord aux_tl) => access_record aux_tl idx_tag = Success (idx_ty t)
                  | _ => False
                  end
            | _ => False
            end.

        Definition aux_wf_for_idx (v : value) : Prop :=
          match v with
          | VRecord rv =>
              match access_record rv id_tag with
              | Success v_id =>
                  match access_record rv aux_tag with
                  | Success (VRecord rv_aux) =>
                      match access_record rv_aux idx_tag with
                      | Success v_idx =>
                          idx_wf v_id v_idx
                      | _ => False
                      end
                  | _ => False
                  end
              | _ => False
              end
          | _ => False
          end.

        Section sum_to_agg_lookup.
          Context (tbl : string).

          Definition sum_to_agg_lookup_head (e : expr) :=
            match e with
            | EACFold AGSum (EProj LikeBag (EBagOf (EAccess (ELoc tbl0) id_tag0)) x0 (EAccess (EVar x1) attr0)) =>
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
            do 3 f_equal. erewrite map_ext_in; eauto.
            intros. repeat rewrite_map_get_put_goal. reflexivity.
          Qed.
        End sum_to_agg_lookup.

        Section cons_to_add.
          Definition cons_to_add_head (e : expr) :=
            match e with
            | EACFold AGSum (EProj LikeBag (EBagOf (EBinop OCons e1 e2)) x0 e3) =>
                EBinop OPlus (ELet e1 x0 e3) (EACFold AGSum (EProj LikeBag (EBagOf e2) x0 e3))
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

          Ltac apply_int_binop_Z_add_AC :=
             intros; unfold apply_int_binop;
             repeat case_match; auto;
             rewrite !Z.add_assoc;
             lazymatch goal with
               |- context[(?z + _ + _)%Z] =>
                 rewrite (Z.add_comm z)
             end; reflexivity.

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
      End WithTags.
    End WithMap.
  End WithVars.
End WithHole.
