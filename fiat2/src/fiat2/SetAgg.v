Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute fiat2.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.

(* The set of values that an attribute takes over a table.

   min_agg keeps only the smallest value, so deleting that value leaves it
   with nothing to fall back on.  This index keeps all of them, and it is a
   set rather than a bag because of the shape of the deletes the dictionary
   index rewrites: "remove every row with attr = k" takes k out of the set
   outright, since no remaining row carries it.  Multiplicity would be
   needed only for a delete that removed some, but not all, of the rows
   sharing a value. *)
Section WithHole.
  Context (hole : string).
  Context (attr : string).

  Section WithVars.
    Context (x : string).

    Definition to_idx : expr :=
      flatmap_proj_set (ESetOf (EVar hole)) x (EAccess (EVar x) attr) None.

    (* Any attribute, not just an integer one.  A set needs equality and
       nothing else -- OSetInsert and OSetMem are both generic in the element
       type (TypeSystem.v:197,203) -- so the TInt this index was born with was
       incidental: it came from being written beside min_agg and sum_agg,
       which really do need numbers.  Keeping it would have held the
       membership rewrite off every string-keyed table, which is where
       membership tests mostly live.

       The match is left three deep, on access_record rather than on inb, so
       that the shape the proofs below destruct is unchanged. *)
    Definition is_tbl_ty (t : type) : bool :=
      match t with
      | TList (TRecord rt) => match access_record rt attr with
                              | Success _ => true
                              | _ => false
                              end
      | _ => false
      end.

    Definition idx_ty (t : type) : type :=
      match t with
      | TList (TRecord rt) => TSet (get_attr_type rt attr)
      | _ => TUnit
      end.

    Lemma idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t).
      destruct t; cbn; intros; try congruence.
      destruct t; try congruence.
      inversion H; subst.
      constructor; apply get_attr_type_ty_wf; assumption.
    Qed.

    Section WithMap.
      Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
      Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
      Notation value := (value (width:=width)).
      Context {locals : map.map string value} {locals_ok : map.ok locals}.

      Definition idx_wf (tbl_v idx_v : value) : Prop :=
        idx_v = interp_expr map.empty (map.put map.empty hole tbl_v) to_idx.

      Lemma to_idx_ty : forall (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t).
      Proof.
        unfold is_tbl_ty, to_idx, idx_ty; intros.
        repeat destruct_match_hyp; try discriminate.
        assert (H_rwf : type_wf (TRecord l)) by (inversion H; assumption).
        (* the element type, named through get_attr_type so that the index's
           type is a function of the table's as the interface requires *)
        assert (E_gat : access_record l attr = Success (get_attr_type l attr)).
        1:{ unfold get_attr_type.
            lazymatch goal with
              H : access_record _ attr = Success _ |- _ => rewrite H
            end. reflexivity. }
        repeat econstructor; repeat rewrite_map_get_put_goal; eauto.
        all: try exact E_gat.
        all: try (apply get_attr_type_ty_wf; exact H_rwf).
      Qed.

      Lemma to_idx_wf : forall (v : value) (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          idx_wf v (interp_expr map.empty (map.put map.empty hole v) to_idx).
      Proof.
        unfold idx_wf; intros; auto.
      Qed.

      Lemma set_mem_singleton : forall (v k : value), set_mem v [k] = value_eqb v k.
      Proof.
        intros. unfold set_mem; cbn. apply Bool.orb_false_r.
      Qed.

      Instance set_agg : IndexInterface.index := IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

      Instance set_agg_ok : IndexInterface.ok set_agg idx_wf :=
        IndexInterface.Build_ok set_agg idx_wf idx_ty_wf to_idx_ty to_idx_wf.

      (* Unfold interp_expr one layer at a time, so that the rewrites below can
         work from the outside in without touching the subexpressions. *)










      Section WithTags.
        Context (id_tag aux_tag idx_tag: string).

        Notation aux_ty_for_idx := (aux_ty_for_idx id_tag aux_tag idx_tag idx_ty).
        Notation aux_wf_for_idx := (aux_wf_for_idx id_tag aux_tag idx_tag idx_wf).

        Section set_to_lookup.
          Context (tbl : string).

          Definition set_to_lookup_head (e : expr) :=
            match e with
            | flatmap_proj_set (ESetOf (EAccess (ELoc tbl0) id_tag0)) x0 (EAccess (EVar x1) attr0) _ =>
                if all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x0, [x1]); (id_tag, [id_tag0])]
                then EAccess (EAccess (ELoc tbl) aux_tag) idx_tag
                else e
            | _ => e
            end.

          Lemma set_to_lookup_head_preserve_ty : forall tl t aux_tl (Gstore : tenv),
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              preserve_ty Gstore (set_to_lookup_head).
          Proof.
            unfold preserve_ty, is_tbl_ty. intros.
            repeat destruct_match_hyp; try congruence.
            (* the attribute's type is the set's element type; keep the
               equation for the collapse after idx_ty is unfolded below *)
            lazymatch goal with
              H : access_record _ attr = Success _ |- _ => rename H into E_attr
            end.
            repeat destruct_subexpr. simpl.
            repeat case_match; auto.
            rewrite !Bool.andb_true_r, !Bool.andb_true_iff in *; intuition idtac.
            rewrite eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear. repeat rewrite_map_get_put_hyp.
            repeat (clear_refl; repeat do_injection2).
            repeat (rewrite_l_to_r; do_injection2).
            unfold idx_ty, get_attr_type in *; rewrite E_attr in *.
            repeat (econstructor; eauto).
          Qed.

          Lemma set_to_lookup_head_preserve_sem : forall (Gstore : tenv) (store : locals) tl t aux_tl,
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              match map.get store tbl with
              | Some v => aux_wf_for_idx v
              | _ => False
              end ->
              preserve_sem Gstore store set_to_lookup_head.
          Proof.
            unfold preserve_sem, aux_wf_for_idx; intros.
            unfold is_tbl_ty, idx_ty, get_attr_type in *.
            apply_locals_wf store.
            repeat (destruct_match_hyp; try discriminate; intuition idtac; []).
            invert_type_of_value_clear.
            pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H16 E1 H2); auto.
            pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H16 E2 H3); auto.
            repeat invert_type_of_value_clear.
            pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H20 E4 H4); auto.
            repeat destruct_subexpr. unfold set_to_lookup_head.
            simpl; repeat (case_match; auto; []).
            rewrite !Bool.andb_true_iff in *; intuition idtac.
            rewrite eqb_eq in *; subst. repeat clear_refl.
            unfold idx_wf in *.
            repeat rewrite_l_to_r.
            cbn. unfold get_local. rewrite_l_to_r. unfold record_proj.
            repeat rewrite_l_to_r. unfold to_idx.
            cbn. unfold get_local. unfold record_proj.
            rewrite_map_get_put_goal.
            erewrite In_flat_map_ext; eauto.
            intros. repeat rewrite_map_get_put_goal. reflexivity.
          Qed.
        End set_to_lookup.

        (* inserting a row adds its attribute to the set *)
        Section cons_to_set_insert.

          Definition cons_to_set_insert_head (e : expr) :=
            match e with
            | flatmap_proj_set (ESetOf (EBinop OCons e1 e2)) x0 (EAccess (EVar x1) attr0) t =>
                if all_eqb [(attr, [attr0]); (x0, [x1])]
                then EBinop OSetInsert
                       (flatmap_proj_set (ESetOf e2) x0 (EAccess (EVar x0) attr0) t)
                       (EAccess e1 attr)
                else e
            | _ => e
            end.

          Lemma cons_to_set_insert_head_preserve_ty : forall (Gstore : tenv),
              preserve_ty Gstore cons_to_set_insert_head.
          Proof.
            unfold preserve_ty; intros. repeat destruct_subexpr.
            cbn. repeat (case_match; auto).
            rewrite !Bool.andb_true_r, !Bool.andb_true_iff in *; intuition idtac.
            rewrite eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear.
            repeat rewrite_map_get_put_hyp.
            (* the consed row has the record type the attribute is read from *)
            lazymatch goal with
              H: Some _ = Some (TRecord _) |- _ => injection H; intros; subst end.
            repeat (econstructor; eauto); repeat rewrite_map_get_put_goal; auto.
          Qed.

          Lemma cons_to_set_insert_head_preserve_sem : forall (Gstore : tenv) (store : locals),
              preserve_sem Gstore store cons_to_set_insert_head.
          Proof.
            unfold preserve_sem; intros. repeat destruct_subexpr.
            cbn [cons_to_set_insert_head]. repeat (case_match; auto; []).
            cbn [all_eqb all_eqb' andb] in *.
            rewrite !Bool.andb_true_r, !Bool.andb_true_iff in *; intuition idtac.
            rewrite eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear.
            apply_type_sound e1_2.
            invert_type_of_value_clear.
            cbn.
            lazymatch goal with
              H: VList _ = interp_expr _ _ e1_2 |- _ => rewrite <- H end.
            cbn. rewrite_flat_map_singleton. rewrite !map_proj_put.
            f_equal. symmetry. apply list_to_set_map_set_insert.
          Qed.
        End cons_to_set_insert.

        (* deleting every row with a given attribute value drops it from the set *)
        Section filter_neq_to_set_diff.

          Definition filter_neq_to_set_diff_head (e : expr) :=
            match e with
            | flatmap_proj_set
                (ESetOf (flatmap_filter_list e' y
                           (EUnop ONot (EBinop OEq (EAccess (EVar y0) attr1) k)) y1 _ _))
                x0 (EAccess (EVar x1) attr0) t =>
                if (all_eqb [(attr, [attr0; attr1]); (x0, [x1]); (y, [y0; y1])] &&
                      negb (free_immut_in y k))%bool
                then EBinop OSetDiff
                       (flatmap_proj_set (ESetOf e') x0 (EAccess (EVar x0) attr0) t)
                       (EBinop OSetInsert (EAtom (AEmptySet None)) k)
                else e
            | _ => e
            end.

          Lemma filter_neq_to_set_diff_head_preserve_ty : forall (Gstore : tenv),
              preserve_ty Gstore filter_neq_to_set_diff_head.
          Proof.
            unfold preserve_ty; intros. repeat destruct_subexpr.
            cbn. repeat (case_match; auto).
            cbn [all_eqb all_eqb' andb] in *.
            rewrite !Bool.andb_true_r, !Bool.andb_true_iff, !Bool.negb_true_iff in *;
              intuition idtac.
            rewrite eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear.
            repeat rewrite_map_get_put_hyp.
            (* the filtered row and the projected row are the same record *)
            repeat lazymatch goal with
                   | H: Some _ = Some _ |- _ => injection H as H
                   | H: TRecord _ = TRecord _ |- _ => injection H as H
                   end; subst.
            repeat (rewrite_l_to_r; do_injection).
            repeat (econstructor; eauto);
              repeat rewrite_map_get_put_goal; auto.
            (* the empty set's element type is well formed *)
            1: lazymatch goal with
                 H: type_of_atom (AEmptySet _) _ |- _ => inversion H; subst; auto end.
            (* the deleted key does not mention the filtered row, and is compared
               against the attribute, so it has the attribute's type *)
            1:{ eapply not_free_immut_put_ty; [ eassumption | ].
                lazymatch goal with
                | H: type_of _ (map.put _ _ _) e1_2_1_2 ?t2 |- type_of _ _ _ ?t1 =>
                    replace t1 with t2 by congruence; exact H
                end. }
          Qed.

          Lemma filter_neq_to_set_diff_head_preserve_sem : forall (Gstore : tenv) (store : locals),
              preserve_sem Gstore store filter_neq_to_set_diff_head.
          Proof.
            unfold preserve_sem; intros. repeat destruct_subexpr.
            cbn [filter_neq_to_set_diff_head]. repeat (case_match; auto; []).
            cbn [all_eqb all_eqb' andb] in *.
            rewrite !Bool.andb_true_r, !Bool.andb_true_iff, !Bool.negb_true_iff in *;
              intuition idtac.
            rewrite eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear.
            rewrite !interp_EBinop, !interp_flatmap_proj_set, !interp_ESetOf,
              interp_flatmap_filter_list.
            (* the table being filtered is a list of records *)
            apply_type_sound e1_1. invert_type_of_value_clear.
            rewrite filter_pred_neq by assumption.
            cbn [interp_expr interp_binop interp_atom set_insert].
            rewrite !map_proj_put, !list_to_set_map_list_to_set.
            f_equal.
            (* the difference against a singleton tests the key *)
            erewrite In_filter_ext by (intros; rewrite set_mem_singleton; reflexivity).
            apply filter_list_to_set_map.
          Qed.
        End filter_neq_to_set_diff.

        Ltac invert_tenv_wf_with_globals :=
          lazymatch goal with H: tenv_wf_with_globals _ _ _ |- _ => inversion H; subst end.

        Lemma set_to_lookup_head_sound : forall is_tbl_ty' aux_ty aux_wf,
            aux_ty_for_idx aux_ty ->
            (forall t, is_tbl_ty' t = true -> is_tbl_ty t = true) ->
            (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
            expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf set_to_lookup_head.
        Proof.
          unfold aux_ty_for_idx, expr_aug_transf_sound; intros.
          invert_tenv_wf_with_globals.
          specialize (H tbl_ty). repeat destruct_match_hyp; intuition idtac.
          1: eapply set_to_lookup_head_preserve_ty; eauto.
          1: eapply set_to_lookup_head_preserve_sem; eauto.
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

        Lemma cons_to_set_insert_head_sound :
          expr_transf_sound (locals:=locals) cons_to_set_insert_head.
        Proof.
          unfold expr_transf_sound; intros.
          intuition idtac.
          1: eapply cons_to_set_insert_head_preserve_ty; eauto.
          1: eapply cons_to_set_insert_head_preserve_sem; [ | | eauto .. ]; auto.
        Qed.

        Lemma filter_neq_to_set_diff_head_sound :
          expr_transf_sound (locals:=locals) filter_neq_to_set_diff_head.
        Proof.
          unfold expr_transf_sound; intros.
          intuition idtac.
          1: eapply filter_neq_to_set_diff_head_preserve_ty; eauto.
          1: eapply filter_neq_to_set_diff_head_preserve_sem; [ | | eauto .. ]; auto.
        Qed.
      End WithTags.
    End WithMap.
  End WithVars.
End WithHole.

#[export] Hint Resolve set_to_lookup_head_sound : transf_hints.
#[export] Hint Resolve cons_to_set_insert_head_sound : transf_hints.
#[export] Hint Resolve filter_neq_to_set_diff_head_sound : transf_hints.

#[export] Hint Extern 5 (type_of _ _ IndexInterface.to_idx _) => apply SetAgg.to_idx_ty : transf_hints.
