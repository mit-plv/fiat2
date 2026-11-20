Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.index.IndexInterface
  fiat2.Utils fiat2.TransfSound fiat2.Substitute fiat2.TransfUtils fiat2.Invariant.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Sorted Permutation.
Import ListNotations.

Ltac NoDup_map_record_sort :=
  eapply Permutation_NoDup;
  [ eapply Permutation_map, Permuted_record_sort
  | cbn; repeat constructor; intuition idtac;
    destruct_In; auto ].

Ltac subst_type_annot :=
  lazymatch goal with
  | H : type_annot_ok (Some _) ?t |- _ =>
      let H_eq := fresh in pose proof H as H_eq; cbn in H_eq; subst t
  end.

Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Notation value := (value).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Section WithIndex.
      Context {idx : IndexInterface.index} {idx_ok : ok idx}.
      Context (id_tag aux_tag: string).
      Context (H_tags_diff : id_tag <> aux_tag).

      Section WithGlobal.
        Context (tbl : string).

      Definition create_aux_write_head (c : command) :=
        match c with
        | CAssign tbl' e =>
            if String.eqb tbl tbl'
            then CAssign tbl (ERecord [(id_tag, e); (aux_tag, no_cap_substitute ((hole, e) :: nil) to_idx)])
            else c
        | _ => c
        end.

      Definition create_aux_read_head (e : expr) :=
        match e with
        | ELoc x => if String.eqb tbl x
                    then (EAccess (ELoc tbl) id_tag)
                    else e
        | _ => e
        end.

      Definition transf_inv (i : invariant) : invariant :=
        match i with
        | ConstraintInv tbl' path row cond =>
            ConstraintInv tbl' (if String.eqb tbl' tbl then id_tag :: path else path) row
              (fold_expr create_aux_read_head cond)
        | IndexInv tbl' id_path aux_path h to_idx' =>
            if String.eqb tbl' tbl
            then IndexInv tbl' (id_tag :: id_path) (id_tag :: aux_path) h to_idx'
            else i
        end.

      Definition transf_to_idx' (c : command) : command :=
        fold_command_with_global create_aux_write_head create_aux_read_head transf_inv c.

      Definition aux_ty (tbl_ty : type) :=
        TRecord
          (record_sort
             [(id_tag, tbl_ty); (aux_tag, idx_ty tbl_ty)]).

      Ltac apply_transf_to_idx_preserve_ty''_IH :=
        lazymatch goal with IH: context[type_of _ _ ?e _ ] |- type_of _ _ ?e _ => apply IH end.

      Lemma transf_to_idx_preserve_ty'' : forall tbl_ty e Gstore Genv t,
          tenv_wf Gstore -> tenv_wf Genv ->
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          type_of Gstore Genv e t ->
          type_of (map.put Gstore tbl (aux_ty tbl_ty)) Genv (fold_expr create_aux_read_head e) t.
      Proof.
        unfold aux_ty.
        induction 5 using type_of_IH; simpl; intros.
        all: try (econstructor; eauto; apply_transf_to_idx_preserve_ty''_IH; apply tenv_wf_step; eauto with fiat2_hints).
        1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
            1:{ repeat rewrite_l_to_r; do_injection.
                repeat econstructor; try rewrite_map_get_put_goal; eauto.
                apply NoDup_In_access_record.
                1: NoDup_map_record_sort.
                eapply Permutation_in; [ apply Permuted_record_sort | ].
                cbn; auto. }
            constructor. rewrite_map_get_put_goal. }
        1:{ econstructor; eauto.
            1: rewrite fst_map_fst; assumption.
            lazymatch goal with
              H1: map fst _ = _, H2: Forall2 (type_of _ _) _ _,
                  H3: Permutation _ _, H4: NoDup _ |- _ => clear H1 H2 H3 H4 end.
            generalize dependent tl.
            induction l; intros; simpl in *; invert_Forall2; auto.
            case_match; simpl in *. constructor; auto.
            destruct tl; simpl in *; try congruence. invert_cons.
            apply IHl; auto. }
      Qed.

      Lemma aux_ty_wf : forall t,
          type_wf t -> is_tbl_ty t = true ->
          type_wf (aux_ty t).
      Proof.
        intros.
        unfold aux_ty. constructor; auto using StronglySorted_record_sort.
        1: NoDup_map_record_sort.
        1: rewrite Forall_map.
        eapply Permutation_Forall; [ apply Permuted_record_sort | ].
        repeat constructor; intuition idtac; cbn.
        eauto using idx_ty_wf.
      Qed.

      (* The record that a write rewrite assigns is at the augmented table type. *)
      Lemma aux_record_ty : forall tbl_ty e (Gstore Genv : tenv),
          tenv_wf Gstore -> tenv_wf Genv ->
          type_wf tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          type_of Gstore Genv e tbl_ty ->
          type_of Gstore Genv
            (ERecord [(id_tag, e); (aux_tag, no_cap_substitute ((hole, e) :: nil) to_idx)])
            (aux_ty tbl_ty).
      Proof.
        unfold aux_ty; intros.
        econstructor.
        3: apply Permuted_record_sort.
        1: reflexivity.
        1:{ repeat constructor; cbn [snd]; auto.
            eapply no_cap_substitute_preserve_ty with (Genv0:=map.put map.empty hole tbl_ty);
              eauto using idx_ty_wf with fiat2_hints.
            1:{ eapply type_of_strengthen; eauto using to_idx_ty, map_incl_refl.
                apply map_incl_empty. }
            1:{ unfold sub_wf. simpl; intros.
                case_match_string_eqb.
                1: do_injection; auto.
                rewrite map.get_empty in *; discriminate. } }
        1: cbn; repeat constructor; intuition idtac; destruct_In; auto.
        1: apply StronglySorted_record_sort.
      Qed.

      Lemma aux_ty_access_id : forall tbl_ty,
          access_record (record_sort [(id_tag, tbl_ty); (aux_tag, idx_ty tbl_ty)]) id_tag
          = Success tbl_ty.
      Proof.
        intros. apply NoDup_In_access_record.
        1: NoDup_map_record_sort.
        eapply Permutation_in; [ apply Permuted_record_sort | ]; cbn; auto.
      Qed.

      Lemma aux_ty_access_aux : forall tbl_ty,
          access_record (record_sort [(id_tag, tbl_ty); (aux_tag, idx_ty tbl_ty)]) aux_tag
          = Success (idx_ty tbl_ty).
      Proof.
        intros. apply NoDup_In_access_record.
        1: NoDup_map_record_sort.
        eapply Permutation_in; [ apply Permuted_record_sort | ]; cbn; auto.
      Qed.

      Lemma type_at_aux_ty_id : forall t p,
          type_at (aux_ty t) (id_tag :: p) = type_at t p.
      Proof.
        intros. unfold aux_ty; cbn [type_at]. rewrite aux_ty_access_id. reflexivity.
      Qed.

      Lemma transf_inv_wf : forall tbl_ty Gstore i,
          tenv_wf Gstore ->
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          inv_wf Gstore i ->
          inv_wf (map.put Gstore tbl (aux_ty tbl_ty)) (transf_inv i).
      Proof.
        intros * H_Gs H_tbl H_is H_i.
        inversion H_i as [ tbl' path row cond t row_ty H_get H_at H_cond
                         | tbl' id_path aux_path h ti t t_id t_aux H_get H_id H_aux H_ti ];
          subst; cbn [transf_inv].
        - assert (H_row : type_wf row_ty).
          1:{ eapply type_at_wf in H_at; [ inversion H_at; assumption | ].
              eapply H_Gs; eassumption. }
          destruct (String.eqb tbl' tbl) eqn:E.
          + apply String.eqb_eq in E; subst tbl'.
            rewrite H_tbl in H_get; injection H_get as <-.
            econstructor; [ apply map.get_put_same | rewrite type_at_aux_ty_id; eassumption | ].
            eapply transf_to_idx_preserve_ty''; eauto.
            apply tenv_wf_step; [ apply tenv_wf_empty | assumption ].
          + apply String.eqb_neq in E.
            econstructor; [ rewrite map.get_put_diff by congruence; eassumption | eassumption | ].
            eapply transf_to_idx_preserve_ty''; eauto.
            apply tenv_wf_step; [ apply tenv_wf_empty | assumption ].
        - destruct (String.eqb tbl' tbl) eqn:E.
          + apply String.eqb_eq in E; subst tbl'.
            rewrite H_tbl in H_get; injection H_get as <-.
            econstructor; [ apply map.get_put_same | rewrite type_at_aux_ty_id; eassumption
                          | rewrite type_at_aux_ty_id; eassumption | eassumption ].
          + apply String.eqb_neq in E.
            econstructor; [ rewrite map.get_put_diff by congruence; eassumption | eassumption .. ].
      Qed.

      Lemma get_put_other_None : forall (G : tenv) x y t t',
          map.get G x = None -> map.get G y = Some t' ->
          map.get (map.put G y t) x = None.
      Proof.
        intros. rewrite map.get_put_diff; congruence.
      Qed.

      Lemma transf_invs_wf_below : forall tbl_ty Gstore x t invs,
          tenv_wf (map.put Gstore x t) ->
          map.get Gstore tbl = Some tbl_ty -> map.get Gstore x = None ->
          is_tbl_ty tbl_ty = true ->
          Forall (inv_wf (map.put Gstore x t)) invs ->
          Forall (inv_wf (map.put (map.put Gstore tbl (aux_ty tbl_ty)) x t)) (List.map transf_inv invs).
      Proof.
        intros * H_Gs H_tbl H_x H_is H_invs.
        rewrite Properties.map.put_put_diff by congruence.
        rewrite Forall_map. eapply Forall_impl; [ | eassumption ].
        intros; eapply transf_inv_wf; eauto.
        rewrite map.get_put_diff by congruence; assumption.
      Qed.

      Ltac use_transf_to_idx_preserve_ty'_IH :=
        lazymatch goal with
          IH: context[well_typed _ _ (transf_to_idx' ?c)] |- well_typed _ _ (transf_to_idx' ?c) =>
            eapply IH; try reflexivity
        end.

      Lemma transf_to_idx_preserve_ty' : forall tbl_ty c (Gstore Gstore' Genv :tenv),
          tenv_wf Gstore -> tenv_wf Genv ->
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          well_typed Gstore Genv c ->
          Gstore' = map.put Gstore tbl (aux_ty tbl_ty) ->
          well_typed Gstore' Genv (transf_to_idx' c).
      Proof.
        induction c; simpl; intros; try invert_well_typed; try now (constructor; auto).
        1: econstructor; eauto using transf_to_idx_preserve_ty''.
        1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
            use_transf_to_idx_preserve_ty'_IH; eauto with fiat2_hints. }
        1:{ assert (x <> tbl) by congruence.
            econstructor; eauto using transf_to_idx_preserve_ty''.
            1:{ rewrite Properties.map.put_put_diff in *; auto.
                use_transf_to_idx_preserve_ty'_IH; eauto with fiat2_hints.
                rewrite_map_get_put_goal. }
            1: eapply transf_invs_wf_below; eauto with fiat2_hints.
            1: eapply get_put_other_None; eassumption. }
        1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
            1:{ econstructor; [ rewrite_map_get_put_goal; eauto | ].
                repeat rewrite_l_to_r; repeat (do_injection; clear_refl).
                apply aux_record_ty; eauto using aux_ty_wf, transf_to_idx_preserve_ty'' with fiat2_hints. }
            1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
                rewrite_map_get_put_goal; eauto. } }
        1: constructor; eauto using transf_to_idx_preserve_ty''.
        1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
            use_transf_to_idx_preserve_ty'_IH; eauto with fiat2_hints. }
      Qed.

      Definition consistent_with_global (store store' : locals) :=
        match map.get store tbl with
        | Some v =>
            match map.get store' tbl with
            | Some (VRecord rv) =>
                match access_record rv id_tag with
                | Success v_id =>
                    v_id = v
                | _ => False
                end
            | _ => False
            end
        | _ => False
        end /\
          forall x, x <> tbl -> map.get store x = map.get store' x.

      Lemma consistent_with_global__store_eq_except : forall (store store' : locals),
          consistent_with_global store store' ->
          forall x, x <> tbl -> map.get store x = map.get store' x.
      Proof.
        unfold consistent_with_global.
        intuition idtac.
      Qed.

      Lemma In_map_ext2 :   forall [A B : Type] (f g : A -> B) (l l' : list A),
          l = l' ->
          (forall a : A, In a l -> f a = g a) ->
          map f l = map g l'.
      Proof.
        intros; subst; eapply map_ext_in; eauto.
      Qed.

      Ltac use_transf_to_idx_preserve_sem''_IH :=
        lazymatch goal with
          IH: context[interp_expr _ _ (fold_expr _ ?e) = _] |-
            context[interp_expr _ _ (fold_expr _ ?e)] =>
            erewrite IH end.

      Lemma transf_to_idx_preserve_sem'' : forall tbl tbl_ty Gstore Genv e t,
          type_of Gstore Genv e t ->
          map.get Gstore tbl = Some tbl_ty ->
          tenv_wf Gstore -> tenv_wf Genv ->
          is_tbl_ty tbl_ty = true ->
          forall store store' env,
            locals_wf Gstore store -> locals_wf Genv env ->
            consistent_with_global store store' ->
            interp_expr store' env (fold_expr create_aux_read_head e) = interp_expr store env e.
      Proof.
        intros * H. induction H using type_of_IH; intros; cbn; auto.
        1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
            cbn; unfold consistent_with_global, get_local, record_proj in *.
            1: repeat case_match; intuition idtac.
            destruct_and.
            lazymatch goal with
              H: context[map.get _ _ = _] |- _ => rewrite H end; auto. }
        all: try now (repeat (use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints)).
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            case_match; auto; f_equal.
            apply_type_sound e1; eauto. rewrite_l_to_r.
            invert_type_of_value_clear.
            apply In_flat_map_ext; intros. apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints. }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            case_match; auto. do 2 f_equal.
            apply_type_sound e1. rewrite_l_to_r; invert_type_of_value_clear.
            apply In_flat_map_ext; intros.
            rewrite Forall_map_fst with (P:= fun v => type_of_value v t1) in *.
            lazymatch goal with
              H: In _ _ |- _ => apply bag_to_list_incl in H end.
            apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints. }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            case_match; auto. do 2 f_equal.
            apply_type_sound e1. rewrite_l_to_r; invert_type_of_value_clear.
            apply In_flat_map_ext; intros.
            apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints. }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            case_match; auto.
            revert IHtype_of3;
              use_transf_to_idx_preserve_sem''_IH; eauto; intros.
            apply_type_sound e1; rewrite_l_to_r; invert_type_of_value_clear.
            eapply In_fold_right_ext with (P:=fun v => type_of_value v t2);
              intros; intuition idtac; try apply_Forall_In.
            1: eapply type_sound; eauto.
            1: use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints;
            eapply tenv_wf_step; eauto with fiat2_hints.
            1:{ use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints.
                2: eapply tenv_wf_step; eauto with fiat2_hints.
                eapply type_sound; eauto with fiat2_hints.
                eapply tenv_wf_step; eauto with fiat2_hints. } }
        1:{ do 2 f_equal. rewrite map_map.
            lazymatch goal with
              H1: Permutation _ _, H2: NoDup _, H3: StronglySorted _ _ |- _ =>
                clear H1 H2 H3
            end. generalize dependent tl.
            induction l; cbn; auto; intros.
            destruct tl; try discriminate.
            case_match; cbn in *. invert_cons.
            repeat lazymatch goal with
                     H: Forall2 _ (_ :: _) _ |- _ =>
                       inversion H; subst; clear H end.
            erewrite IHl; eauto.
            use_transf_to_idx_preserve_sem''_IH; eauto. }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            apply_type_sound e. invert_type_of_value_clear;
              use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints. }
      Qed.

      Lemma consistent_with_global_update : forall (l0 l0' l l' : locals),
          consistent_with_global l0 l0' ->
          consistent_with_global l l' ->
          forall x,
            consistent_with_global (map.update l x (map.get l0 x)) (map.update l' x (map.get l0' x)).
      Proof.
        intros.
        unfold consistent_with_global.
        destruct (String.eqb x tbl) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
        1:{ rewrite Properties.map.get_update_same.
            unfold consistent_with_global in *.
            case_match; intuition idtac.
            1: rewrite Properties.map.get_update_same; repeat (case_match; intuition idtac).
            1: rewrite !Properties.map.get_update_diff; auto. }
        1:{ rewrite Properties.map.get_update_diff; auto.
            unfold consistent_with_global in *.
            case_match; intuition idtac.
            1: rewrite Properties.map.get_update_diff; auto.
            1:{ destruct (String.eqb x x0) eqn:E'; rewrite ?eqb_eq, ?eqb_neq in *; subst.
                1: rewrite !Properties.map.get_update_same; auto.
                1: rewrite !Properties.map.get_update_diff; auto. } }
      Qed.

      Lemma consistent_with_global_put_local : forall (l l' : locals) x v v',
          consistent_with_global l l' ->
          x <> tbl ->
          v = v' ->
          consistent_with_global (map.put l x v) (map.put l' x v').
      Proof.
        unfold consistent_with_global; intros; subst.
        repeat rewrite_map_get_put_goal; intuition auto.
        destruct_get_put_strings; reflexivity.
      Qed.

      Ltac use_transf_to_idx_preserve_sem'_IH :=
        lazymatch goal with
          IH: context[consistent_with_global (interp_command _ _ ?c) _] |-
            consistent_with_global (interp_command _ _ ?c) _ =>
            eapply IH
        end.

      Lemma transf_to_idx_preserve_sem' : forall tbl_ty c (Gstore Genv : tenv),
          well_typed Gstore Genv c ->
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          tenv_wf Gstore -> tenv_wf Genv ->
          forall (store store' env : locals),
            locals_wf Gstore store -> locals_wf Genv env ->
            consistent_with_global store store' ->
            consistent_with_global (interp_command store env c) (interp_command store' env (transf_to_idx' c)).
      Proof.
        intros * H. induction H; cbn; auto; intros.
        1:{ use_transf_to_idx_preserve_sem'_IH; auto.
            eapply command_type_sound; eauto. }
        1:{ erewrite transf_to_idx_preserve_sem''; eauto.
            use_transf_to_idx_preserve_sem'_IH; eauto with fiat2_hints. }
        1:{ assert (x <> tbl) by congruence.
            apply consistent_with_global_update; auto.
            use_transf_to_idx_preserve_sem'_IH; eauto with fiat2_hints.
            1: rewrite_map_get_put_goal.
            apply consistent_with_global_put_local; auto.
            erewrite transf_to_idx_preserve_sem''; eauto. }
        1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst; cbn [interp_command].
            1:{ unfold consistent_with_global in *; intuition idtac;
                repeat rewrite_map_get_put_goal.
                cbn [interp_expr List.map].
                erewrite NoDup_In_access_record.
                2: NoDup_map_record_sort.
                2: eapply Permutation_in; [ apply Permuted_record_sort | ];
                cbn; auto.
                erewrite transf_to_idx_preserve_sem''; eauto.
                unfold consistent_with_global; auto. }
            1:{ erewrite transf_to_idx_preserve_sem''; eauto.
                apply consistent_with_global_put_local; auto. } }
        1:{ erewrite transf_to_idx_preserve_sem''; eauto.
            repeat case_match; auto. }
        1:{ erewrite transf_to_idx_preserve_sem''; eauto.
            case_match; auto.
            apply_type_sound e. rewrite_l_to_r. invert_type_of_value_clear.
            lazymatch goal with
              H: _ = VList _ |- _ => clear H end.
            generalize dependent store; generalize dependent store'.
            induction l; cbn; auto. invert_Forall; intros.
            apply IHl; auto.
            1: eapply command_type_sound; eauto with fiat2_hints.
            use_transf_to_idx_preserve_sem'_IH; eauto with fiat2_hints. }
      Qed.

      Definition aux_wf (v : value) :=
        match v with
          VRecord rv =>
            match access_record rv id_tag with
            | Success v_id =>
                match access_record rv aux_tag with
                | Success v_aux =>
                    v_aux = interp_expr map.empty (map.put map.empty hole v_id) to_idx
                | _ => False
                end
            | _ => False
            end
        | _ => False
        end.

      (* ------------------------------------------------------------------
         Reading the table back out of the augmented store.

         transf_to_idx' replaces the table by a record pairing the table with
         its index, so an invariant about the table becomes an invariant about
         the id_tag field: that is transf_inv.  strip_aux goes the other
         way, rebuilding the store the untransformed command would have run
         in.  It is needed because an assignment's obligation in the
         transformed program has to be discharged from the obligation the
         original derivation proved, and that obligation speaks about the
         original store.
         ------------------------------------------------------------------ *)

      Definition strip_aux (store : locals) : locals :=
        match map.get store tbl with
        | Some (VRecord rv) =>
            match access_record rv id_tag with
            | Success v_id => map.put store tbl v_id
            | _ => store
            end
        | _ => store
        end.

      Lemma type_of_value_at_id_tag : forall tbl_ty (rv : list (string * value)) (v_id : value),
          type_of_value (VRecord rv) (aux_ty tbl_ty) ->
          access_record rv id_tag = Success v_id ->
          type_of_value v_id tbl_ty.
      Proof.
        unfold aux_ty; intros * H_v H_id.
        invert_type_of_value_clear.
        lazymatch goal with H : Forall2 _ rv _ |- _ =>
          eapply Forall2_access_record; [ exact H | exact H_id | ] end.
        apply aux_ty_access_id.
      Qed.

      Lemma to_idx_satisfy_idx_wf : forall e Gstore Genv t store env,
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv e t ->
          is_tbl_ty t = true ->
          locals_wf Gstore store -> locals_wf Genv env ->
          interp_expr store env (no_cap_substitute ((hole, e) :: nil) to_idx)
          = interp_expr map.empty (map.put map.empty hole (interp_expr store env e)) to_idx.
      Proof.
      intros * H_Gs H_Ge H_e H_is H_store H_env.
      assert (H_t : type_wf t) by (eapply type_of__type_wf; [ | | exact H_e ]; assumption).
      assert (H_G0 : tenv_wf (map.put map.empty hole t)).
      1:{ apply tenv_wf_step; [ | exact H_t ].
          intros ? ? H. rewrite map.get_empty in H. discriminate. }
      assert (H_ti : type_of Gstore (map.put map.empty hole t) to_idx (idx_ty t))
        by (eapply type_of_strengthen; [ apply to_idx_ty; eauto | apply map_incl_empty | apply map_incl_refl ]).
      assert (H_sub : sub_wf (map.put map.empty hole t) Gstore Genv ((hole, e) :: nil)).
      1:{ unfold sub_wf; intros x t' H. cbn.
          destruct (String.eqb x hole) eqn:E; rewrite ?eqb_eq, ?eqb_neq in E; subst.
          1: rewrite map.get_put_same in H; injection H as <-; exact H_e.
          1: rewrite map.get_put_diff, map.get_empty in H by exact E; discriminate. }
      rewrite (no_cap_substitute_preserve_sem to_idx Gstore (map.put map.empty hole t) Genv (idx_ty t) _ store env
                 H_G0 H_Gs H_Ge H_ti H_sub H_store H_env).
      unfold make_sub_env.
      erewrite interp_expr_strengthen with (e:=to_idx); [ reflexivity | .. ].
      3: apply to_idx_ty.
      all: eauto with fiat2_hints.
      1: apply map_incl_empty.
      1: simpl; apply map_incl_step; auto using string_dec, map_incl_refl.
    Qed.


      Lemma record_sort_access_id : forall (v1 v2 : value),
          access_record (record_sort [(id_tag, v1); (aux_tag, v2)]) id_tag = Success v1.
      Proof.
        intros. apply NoDup_In_access_record.
        1: NoDup_map_record_sort.
        eapply Permutation_in; [ apply Permuted_record_sort | ]; cbn; auto.
      Qed.

      Lemma record_sort_access_aux : forall (v1 v2 : value),
          access_record (record_sort [(id_tag, v1); (aux_tag, v2)]) aux_tag = Success v2.
      Proof.
        intros. apply NoDup_In_access_record.
        1: NoDup_map_record_sort.
        eapply Permutation_in; [ apply Permuted_record_sort | ]; cbn; auto.
      Qed.

      Definition idx_inv : invariant := IndexInv tbl (id_tag :: nil) (aux_tag :: nil) hole to_idx.

      Lemma idx_inv_holds : forall (store : locals),
          inv_holds store idx_inv <->
            match map.get store tbl with Some v => aux_wf v | None => False end.
      Proof.
        intros. unfold idx_inv, aux_wf; cbn [inv_holds].
        destruct (map.get store tbl) as [ v | ]; [ | tauto ].
        destruct v; cbn [value_at]; try tauto.
        destruct (access_record l id_tag); destruct (access_record l aux_tag); cbn [value_at]; tauto.
      Qed.

      Lemma strip_aux_idx_inv : forall tbl_ty Gstore (store : locals),
          map.get Gstore tbl = Some tbl_ty ->
          locals_wf (map.put Gstore tbl (aux_ty tbl_ty)) store ->
          inv_holds store idx_inv ->
          locals_wf Gstore (strip_aux store) /\ consistent_with_global (strip_aux store) store.
      Proof.
        intros * H_tbl H_store H_inv. apply idx_inv_holds in H_inv.
        pose proof (H_store tbl (aux_ty tbl_ty)) as H_v.
        rewrite map.get_put_same in H_v; specialize (H_v eq_refl).
        destruct (map.get store tbl) as [ v | ] eqn:E_tbl; try contradiction.
        unfold aux_wf in H_inv. destruct v; try contradiction.
        destruct (access_record l id_tag) as [ v_id | ] eqn:E_id; try contradiction.
        assert (E_strip : strip_aux store = map.put store tbl v_id)
          by (unfold strip_aux; rewrite E_tbl, E_id; reflexivity).
        rewrite E_strip. split.
        1:{ unfold locals_wf; intros x t H_x.
            destruct (String.eqb x tbl) eqn:E_x; rewrite ?eqb_eq, ?eqb_neq in *; subst.
            1:{ rewrite map.get_put_same. rewrite H_tbl in H_x; injection H_x as <-.
                eapply type_of_value_at_id_tag; eassumption. }
            1:{ rewrite map.get_put_diff by congruence.
                specialize (H_store x t). rewrite map.get_put_diff in H_store by congruence.
                apply H_store; exact H_x. } }
        1:{ unfold consistent_with_global. rewrite map.get_put_same, E_tbl, E_id.
            split; [ reflexivity | ]. intros; rewrite map.get_put_diff; auto. }
      Qed.

      (* The rewritten invariant says about the augmented store what the
         original says about the original one. *)
      Lemma transf_inv_holds : forall tbl_ty Gstore i (store store' : locals),
          tenv_wf Gstore -> map.get Gstore tbl = Some tbl_ty -> is_tbl_ty tbl_ty = true ->
          inv_wf Gstore i -> locals_wf Gstore store -> consistent_with_global store store' ->
          inv_holds store' (transf_inv i) <-> inv_holds store i.
      Proof.
        intros * H_Gs H_tbl H_is H_i H_store H_cons.
        assert (E_get : forall x, x <> tbl -> map.get store' x = map.get store x)
          by (intros; symmetry; eapply consistent_with_global__store_eq_except; eauto).
        assert (E_tbl : exists rv v, map.get store tbl = Some v
                                     /\ map.get store' tbl = Some (VRecord rv)
                                     /\ access_record rv id_tag = Success v).
        1:{ destruct H_cons as [ H_c _ ].
            destruct (map.get store tbl) eqn:E1; try contradiction.
            destruct (map.get store' tbl) as [ [] | ] eqn:E2; try contradiction.
            destruct (access_record l id_tag) eqn:E3; try contradiction. subst. eauto. }
        destruct E_tbl as [ rv [ v [ E_s [ E_s' E_id ] ] ] ].
        destruct H_i as [ tbl' path row cond t row_ty H_get H_at H_cond
                        | tbl' id_path aux_path h ti t t_id t_aux H_get H_id H_aux H_ti ];
          cbn [transf_inv].
        1:{ assert (H_row_ty : type_wf row_ty).
            1:{ assert (H_t : type_wf t) by (eapply H_Gs; eassumption).
                pose proof (type_at_wf _ _ _ H_t H_at) as H_wf.
                inversion H_wf; assumption. }
            assert (H_cond_eq : forall r, type_of_value r row_ty ->
                       interp_expr store' (map.put map.empty row r) (fold_expr create_aux_read_head cond)
                       = interp_expr store (map.put map.empty row r) cond).
            1:{ intros r H_r.
                eapply transf_to_idx_preserve_sem'' with (tbl := tbl) (tbl_ty := tbl_ty); eauto.
                1: apply tenv_wf_step; [ apply tenv_wf_empty | assumption ].
                1: apply locals_wf_step; [ apply locals_wf_empty | assumption ]. }
            pose proof (H_store _ _ H_get) as H_v.
            cbn [inv_holds].
            destruct (String.eqb tbl' tbl) eqn:E.
            1:{ apply String.eqb_eq in E; subst tbl'.
                rewrite E_s, E_s' in *. cbn [value_at]. rewrite E_id.
                destruct (value_at v path) as [ [] | ] eqn:E_p; try tauto.
                eapply value_at_type_of_value in E_p; [ | eassumption | eassumption ].
                inversion E_p; subst.
                apply Forall_iff_typed with (t := row_ty); [ assumption | ].
                intros. rewrite H_cond_eq; tauto. }
            1:{ apply String.eqb_neq in E. rewrite E_get by assumption.
                destruct (map.get store tbl') as [ v' | ]; try tauto.
                destruct (value_at v' path) as [ [] | ] eqn:E_p; try tauto.
                eapply value_at_type_of_value in E_p; [ | eassumption | eassumption ].
                inversion E_p; subst.
                apply Forall_iff_typed with (t := row_ty); [ assumption | ].
                intros. rewrite H_cond_eq; tauto. } }
        1:{ destruct (String.eqb tbl' tbl) eqn:E; cbn [inv_holds].
            1:{ apply String.eqb_eq in E; subst tbl'.
                rewrite E_s, E_s'. cbn [value_at]. rewrite E_id. tauto. }
            1:{ apply String.eqb_neq in E. rewrite E_get by assumption. tauto. } }
      Qed.

      Lemma fold_read_head_unbound : forall Gstore Genv e t,
          type_of Gstore Genv e t -> map.get Gstore tbl = None ->
          fold_expr create_aux_read_head e = e.
      Proof.
        intros * H H_tbl. induction H using type_of_IH; cbn;
          repeat lazymatch goal with
            | IH : fold_expr create_aux_read_head ?e = ?e |- _ => rewrite IH; clear IH
            end; try reflexivity.
        1:{ destruct (String.eqb tbl x) eqn:E; [ | reflexivity ].
            apply String.eqb_eq in E; subst. congruence. }
        1:{ f_equal.
            lazymatch goal with H : Forall2 (fun _ _ => _ = _) _ _ |- _ => revert H end.
            clear. generalize (List.map snd tl). induction l as [ | [ s e ] l IHl ]; cbn; auto.
            intros tl' H. inversion H; subst. f_equal; [ congruence | eauto ]. }
      Qed.

      Lemma transf_inv_unbound : forall Gstore i,
          inv_wf Gstore i -> map.get Gstore tbl = None -> transf_inv i = i.
      Proof.
        intros * H_i H_tbl. destruct H_i; cbn [transf_inv].
        all: destruct (String.eqb tbl0 tbl) eqn:E;
          [ apply String.eqb_eq in E; subst; congruence | ].
        1: erewrite fold_read_head_unbound; eauto.
        1: reflexivity.
      Qed.

      Lemma strip_aux_ictx : forall tbl_ty Gstore ictx (store : locals),
          tenv_wf Gstore -> map.get Gstore tbl = Some tbl_ty -> is_tbl_ty tbl_ty = true ->
          Forall (inv_wf Gstore) ictx ->
          locals_wf (map.put Gstore tbl (aux_ty tbl_ty)) store ->
          holds_all store (List.map transf_inv ictx ++ idx_inv :: nil) ->
          locals_wf Gstore (strip_aux store) /\ consistent_with_global (strip_aux store) store
          /\ holds_all (strip_aux store) ictx /\ inv_holds store idx_inv.
      Proof.
        intros * H_Gs H_tbl H_is H_ictx H_store H_h.
        unfold holds_all in H_h. apply Forall_app in H_h as [ H_h H_idx ].
        inversion H_idx; subst.
        destruct (strip_aux_idx_inv tbl_ty Gstore store) as [ H_wf H_cons ]; auto.
        split; [ assumption | split; [ assumption | split; [ | assumption ] ] ].
        rewrite Forall_map in H_h. unfold holds_all.
        eapply Forall_impl; [ | apply Forall_and; [ exact H_ictx | exact H_h ] ].
        intros i [ H_i H_hi ].
        apply (transf_inv_holds tbl_ty Gstore i (strip_aux store) store); auto.
      Qed.

      Ltac use_strip_aux_ictx :=
        lazymatch goal with
        | H_h : holds_all ?store (List.map transf_inv ?ictx ++ idx_inv :: nil),
          H_store : locals_wf (map.put ?G tbl (aux_ty ?ty)) ?store |- _ =>
            destruct (strip_aux_ictx ty G ictx store ltac:(eassumption) ltac:(eassumption)
                        ltac:(eassumption) ltac:(eassumption) H_store H_h)
              as [ H_wf0 [ H_cons0 [ H_h0 H_idx0 ] ] ]
        end.

      Lemma transf_to_idx'_maintains_invs :
        forall tbl_ty c Gstore Genv ictx path_cond path_cond',
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          tenv_wf Gstore -> tenv_wf Genv ->
          Forall (inv_wf Gstore) ictx ->
          (forall (store env : locals),
              locals_wf (map.put Gstore tbl (aux_ty tbl_ty)) store ->
              locals_wf Genv env ->
              holds_all store (List.map transf_inv ictx ++ idx_inv :: nil) ->
              path_cond' store env -> path_cond (strip_aux store) env) ->
          maintains_invs Gstore Genv ictx path_cond c ->
          maintains_invs (map.put Gstore tbl (aux_ty tbl_ty)) Genv
            (List.map transf_inv ictx ++ idx_inv :: nil) path_cond'
            (transf_to_idx' c).
      Proof.
        induction c; simpl; intros * H_tbl H_is H_Gs H_Ge H_ictx H_sim H_m;
          inversion H_m; subst.
        (* CSkip *)
        1: constructor.
        (* CSeq *)
        1:{ constructor.
            1: eapply IHc1; eauto.
            1: apply IHc2 with (path_cond := fun _ _ => True); auto. }
        (* CLet *)
        1:{ econstructor.
            1: eapply transf_to_idx_preserve_ty''; eauto.
            1:{ apply IHc with (path_cond := fun _ _ => True);
                  [ exact H_tbl | exact H_is
                  | exact H_Gs | eauto with fiat2_hints | exact H_ictx
                  | intros; exact I | assumption ]. } }
        (* CLetMut: no shadowing, so the binder is not the table *)
        1:{ assert (H_ne : x <> tbl) by congruence.
            assert (H_Gs' : tenv_wf (map.put Gstore x t)) by eauto with fiat2_hints.
            econstructor.
            1: eapply transf_to_idx_preserve_ty''; eauto.
            1: eassumption.
            1:{ rewrite Properties.map.put_put_diff by congruence.
                replace (List.map transf_inv invs ++ (List.map transf_inv ictx ++ idx_inv :: nil))
                  with (List.map transf_inv (invs ++ ictx) ++ idx_inv :: nil)
                  by (rewrite map_app, app_assoc; reflexivity).
                apply IHc with (path_cond := fun _ _ => True);
                  [ rewrite map.get_put_diff by congruence; exact H_tbl
                  | exact H_is | exact H_Gs' | exact H_Ge
                  | | intros; exact I | assumption ].
                apply Forall_app; split; [ assumption | ].
                eapply Forall_impl; [ | exact H_ictx ]; intros.
                eapply inv_wf_weaken; [ | eassumption ].
                apply map_incl_step_r; [ apply map_incl_refl | assumption ]. }
            1:{ rewrite Properties.map.put_put_diff by congruence.
                rewrite Forall_map. eapply Forall_impl; [ | eassumption ]; intros.
                eapply transf_inv_wf; eauto.
                rewrite map.get_put_diff by congruence; exact H_tbl. }
            1: eapply get_put_other_None; eassumption.
            1:{ intros store env H_pc H_h H_store H_env. use_strip_aux_ictx.
                assert (E_sem : interp_expr store env (fold_expr create_aux_read_head e)
                                = interp_expr (strip_aux store) env e)
                  by (eapply transf_to_idx_preserve_sem'' with (tbl := tbl) (tbl_ty := tbl_ty); eauto).
                rewrite E_sem.
                lazymatch goal with
                | H_init : forall _ _, _ -> _ -> _ -> _ -> holds_all _ invs |- _ =>
                    specialize (H_init (strip_aux store) env (H_sim _ _ H_store H_env H_h H_pc)
                                  H_h0 H_wf0 H_env)
                end.
                set (v := interp_expr (strip_aux store) env e).
                assert (H_lw : locals_wf (map.put Gstore x t) (map.put (strip_aux store) x v))
                  by (apply locals_wf_step; [ assumption | subst v; eapply type_sound; eauto ]).
                assert (H_c : consistent_with_global (map.put (strip_aux store) x v) (map.put store x v))
                  by (apply consistent_with_global_put_local; auto).
                assert (H_tbl' : map.get (map.put Gstore x t) tbl = Some tbl_ty)
                  by (rewrite map.get_put_diff by congruence; exact H_tbl).
                unfold holds_all in *. rewrite Forall_map.
                lazymatch goal with
                | H_invs : Forall (inv_wf _) invs, H_init : Forall (inv_holds _) invs |- _ =>
                    eapply Forall_impl; [ | apply Forall_and; [ exact H_invs | exact H_init ] ]
                end.
                intros i [ H_i H_hi ].
                exact (proj2 (transf_inv_holds tbl_ty _ i _ _ H_Gs' H_tbl' H_is H_i H_lw H_c) H_hi). } }
        (* CAssign *)
        1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
            (* the table: both fields are written from the same value *)
            1:{ lazymatch goal with
                | H : map.get Gstore tbl = Some ?t |- _ =>
                    rewrite H_tbl in H; injection H as <-
                end.
                assert (H_wf_t : type_wf tbl_ty) by (eapply H_Gs; eassumption).
                econstructor.
                1: apply map.get_put_same.
                1:{ apply aux_record_ty; eauto using aux_ty_wf with fiat2_hints.
                    eapply transf_to_idx_preserve_ty''; eauto. }
                intros store env H_pc H_h H_store H_env. use_strip_aux_ictx.
                assert (E_sem : interp_expr store env (fold_expr create_aux_read_head e)
                                = interp_expr (strip_aux store) env e)
                  by (eapply transf_to_idx_preserve_sem'' with (tbl := tbl) (tbl_ty := tbl_ty); eauto).
                cbn [interp_expr List.map].
                lazymatch goal with
                | H_obl : forall _ _, _ -> _ -> _ -> _ -> holds_all _ ictx |- _ =>
                    specialize (H_obl (strip_aux store) env (H_sim _ _ H_store H_env H_h H_pc)
                                  H_h0 H_wf0 H_env)
                end.
                set (v := interp_expr (strip_aux store) env e) in *.
                assert (H_lw : locals_wf Gstore (map.put (strip_aux store) tbl v)).
                1:{ eapply locals_wf_put_typed; [ eassumption | eassumption | ].
                    subst v; eapply type_sound; eauto. }
                assert (H_c : consistent_with_global (map.put (strip_aux store) tbl v)
                                (map.put store tbl (VRecord (record_sort
                                   [(id_tag, interp_expr store env (fold_expr create_aux_read_head e));
                                    (aux_tag, interp_expr store env
                                                (no_cap_substitute [(hole, fold_expr create_aux_read_head e)]
                                                   to_idx))])))).
                1:{ unfold consistent_with_global. rewrite !map.get_put_same.
                    rewrite record_sort_access_id, E_sem. split; [ reflexivity | ].
                    intros y H_y. rewrite !map.get_put_diff by assumption.
                    eapply consistent_with_global__store_eq_except; eauto. }
                unfold holds_all in *. apply Forall_app; split.
                1:{ rewrite Forall_map.
                    lazymatch goal with
                    | H_obl : Forall (inv_holds (map.put (strip_aux store) tbl v)) ictx |- _ =>
                        eapply Forall_impl; [ | apply Forall_and; [ exact H_ictx | exact H_obl ] ]
                    end.
                    intros i [ H_i H_hi ].
                    exact (proj2 (transf_inv_holds tbl_ty Gstore i _ _ H_Gs H_tbl H_is H_i H_lw H_c) H_hi). }
                1:{ constructor; [ | constructor ].
                    apply idx_inv_holds. rewrite map.get_put_same.
                    unfold aux_wf. rewrite record_sort_access_id, record_sort_access_aux.
                    eapply to_idx_satisfy_idx_wf.
                    3: apply transf_to_idx_preserve_ty''; [ | | eauto .. ]; auto.
                    all: eauto using aux_ty_wf with fiat2_hints. } }
            (* another variable *)
            1:{ econstructor.
                1: rewrite map.get_put_diff by congruence; eassumption.
                1: eapply transf_to_idx_preserve_ty''; eauto.
                intros store env H_pc H_h H_store H_env. use_strip_aux_ictx.
                assert (E_sem : interp_expr store env (fold_expr create_aux_read_head e)
                                = interp_expr (strip_aux store) env e)
                  by (eapply transf_to_idx_preserve_sem'' with (tbl := tbl) (tbl_ty := tbl_ty); eauto).
                rewrite E_sem.
                lazymatch goal with
                | H_obl : forall _ _, _ -> _ -> _ -> _ -> holds_all _ ictx |- _ =>
                    specialize (H_obl (strip_aux store) env (H_sim _ _ H_store H_env H_h H_pc)
                                  H_h0 H_wf0 H_env)
                end.
                set (v := interp_expr (strip_aux store) env e) in *.
                assert (H_lw : locals_wf Gstore (map.put (strip_aux store) x v)).
                1:{ eapply locals_wf_put_typed; [ eassumption | eassumption | ].
                    subst v; eapply type_sound; eauto. }
                assert (H_c : consistent_with_global (map.put (strip_aux store) x v) (map.put store x v))
                  by (apply consistent_with_global_put_local; auto).
                unfold holds_all in *. apply Forall_app; split.
                1:{ rewrite Forall_map.
                    lazymatch goal with
                    | H_obl : Forall (inv_holds (map.put (strip_aux store) x v)) ictx |- _ =>
                        eapply Forall_impl; [ | apply Forall_and; [ exact H_ictx | exact H_obl ] ]
                    end.
                    intros i [ H_i H_hi ].
                    exact (proj2 (transf_inv_holds tbl_ty Gstore i _ _ H_Gs H_tbl H_is H_i H_lw H_c) H_hi). }
                1:{ constructor; [ | constructor ].
                    apply idx_inv_holds. rewrite map.get_put_diff by congruence.
                    apply idx_inv_holds; assumption. } } }
        (* CIf *)
        1:{ econstructor.
            1: eapply transf_to_idx_preserve_ty''; eauto.
            1:{ eapply IHc1; [ exact H_tbl | exact H_is | exact H_Gs | exact H_Ge
                             | exact H_ictx | | eassumption ].
                intros store env H_store H_env H_h [ H_pc H_g ]. use_strip_aux_ictx.
                split; [ eapply H_sim; eauto | ].
                erewrite <- transf_to_idx_preserve_sem'' with (tbl := tbl) (tbl_ty := tbl_ty); [ exact H_g | .. ]; eauto. }
            1:{ eapply IHc2; [ exact H_tbl | exact H_is | exact H_Gs | exact H_Ge
                             | exact H_ictx | | eassumption ].
                intros store env H_store H_env H_h [ H_pc H_g ]. use_strip_aux_ictx.
                split; [ eapply H_sim; eauto | ].
                erewrite <- transf_to_idx_preserve_sem'' with (tbl := tbl) (tbl_ty := tbl_ty); [ exact H_g | .. ]; eauto. } }
        (* CForeach *)
        1:{ econstructor.
            1: eapply transf_to_idx_preserve_ty''; eauto.
            1:{ apply IHc with (path_cond := fun _ _ => True);
                  [ exact H_tbl | exact H_is
                  | exact H_Gs | eauto with fiat2_hints | exact H_ictx
                  | intros; exact I | assumption ]. } }
      Qed.
      End WithGlobal.

      Definition transf_to_idx (c : command) : command :=
        match c with
        | CLetMut e tbl ot invs c =>
            CLetMut (ERecord [(id_tag, e); (aux_tag, no_cap_substitute ((hole, e) :: nil) to_idx)]) tbl
              (option_map aux_ty ot)
              (IndexInv tbl (id_tag :: nil) (aux_tag :: nil) hole to_idx :: List.map (transf_inv tbl) invs)
              (transf_to_idx' tbl c)
        | _ => c
        end.

      Lemma transf_to_idx_invs_wf : forall tbl tbl_ty Gstore invs,
          tenv_wf Gstore -> type_wf tbl_ty -> is_tbl_ty tbl_ty = true ->
          Forall (inv_wf (map.put Gstore tbl tbl_ty)) invs ->
          Forall (inv_wf (map.put Gstore tbl (aux_ty tbl_ty)))
            (IndexInv tbl (id_tag :: nil) (aux_tag :: nil) hole to_idx
               :: List.map (transf_inv tbl) invs).
      Proof.
        intros * H_Gs H_wf H_is H_invs. constructor.
        1:{ econstructor; [ apply map.get_put_same | | | apply to_idx_ty; eauto ].
            1: rewrite type_at_aux_ty_id; reflexivity.
            1: unfold aux_ty; cbn [type_at]; rewrite aux_ty_access_aux; reflexivity. }
        rewrite Forall_map. eapply Forall_impl; [ | eassumption ]. intros.
        replace (map.put Gstore tbl (aux_ty tbl_ty))
          with (map.put (map.put Gstore tbl tbl_ty) tbl (aux_ty tbl_ty))
          by apply Properties.map.put_put_same.
        eapply transf_inv_wf; eauto using tenv_wf_step.
        apply map.get_put_same.
      Qed.

      Lemma transf_to_idx_preserve_ty : forall tbl tbl_ty e ot invs c Gstore Genv,
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv e tbl_ty ->
          type_annot_ok ot tbl_ty ->
          well_typed (map.put Gstore tbl tbl_ty) Genv c ->
          Forall (inv_wf (map.put Gstore tbl tbl_ty)) invs ->
          map.get Gstore tbl = None ->
          is_tbl_ty tbl_ty = true ->
          well_typed Gstore Genv (transf_to_idx (CLetMut e tbl ot invs c)).
      Proof.
        simpl; intros. subst. econstructor.
        1:{ econstructor.
            1: instantiate (1:=[(id_tag, tbl_ty); (aux_tag, idx_ty tbl_ty)]); reflexivity.
            1:{ cbn; repeat constructor; auto.
                eapply no_cap_substitute_preserve_ty with (Genv0:=map.put map.empty hole tbl_ty); eauto with fiat2_hints.
            1: eapply type_of_strengthen; [ apply to_idx_ty; eauto | apply map_incl_empty | apply map_incl_refl ].
            1: eapply type_of__type_wf; [ | | eauto ]; auto.
            1:{ unfold sub_wf. simpl; intros.
                destruct_get_put_strings;
                  [ do_injection; rewrite eqb_refl; auto
                  | rewrite map.get_empty in *; discriminate ]. } }
            1: eapply Permuted_record_sort.
            1:{ cbn; repeat constructor; intuition auto.
                match goal with Hi : In _ _ |- _ => inversion Hi; auto using in_nil end. }
            1: apply StronglySorted_record_sort. }
        1: apply (type_annot_ok_map aux_ty); assumption.
        1:{ erewrite <- Properties.map.put_put_same.
            eapply transf_to_idx_preserve_ty'; try reflexivity; eauto with fiat2_hints.
            rewrite_map_get_put_goal; auto. }
        1: apply transf_to_idx_invs_wf; eauto with fiat2_hints.
        1: assumption.
      Qed.

      Lemma transf_to_idx_preserve_sem : forall tbl tbl_ty e ot invs c (Gstore Genv : tenv),
          is_tbl_ty tbl_ty = true ->
          type_of Gstore Genv e tbl_ty ->
          well_typed (map.put Gstore tbl tbl_ty) Genv c ->
          tenv_wf Gstore -> tenv_wf Genv ->
          forall (store env : locals),
            locals_wf Gstore store -> locals_wf Genv env ->
            interp_command store env (transf_to_idx (CLetMut e tbl ot invs c)) = interp_command store env (CLetMut e tbl ot invs c).
      Proof.
        simpl; intros.
        apply stores_eq_except__update_eq. symmetry.
        eapply consistent_with_global__store_eq_except; eauto.
        eapply transf_to_idx_preserve_sem'; eauto with fiat2_hints.
        1: rewrite_map_get_put_goal; auto.
        unfold consistent_with_global; intuition idtac; repeat rewrite_map_get_put_goal.
        erewrite NoDup_In_access_record; eauto.
        1: eapply Permutation_NoDup;
        [ eapply Permutation_map, Permuted_record_sort
        | cbn; repeat constructor; intuition idtac;
          destruct_In; auto ].
        eapply Permutation_in; [ eapply Permuted_record_sort | ]; constructor; auto.
      Qed.

      Definition create_idx (c : command) : command :=
        match c with
        | CLetMut e x (Some t) _ _ =>
            if is_tbl_ty t then transf_to_idx c else c
        | _ => c
        end.

      Theorem create_idx_sound : inv_transf_sound (locals := locals) (fun _ _ c => create_idx c).
      Proof.
        unfold inv_transf_sound, create_idx; intros * H_Gs H_Ge H_ictx H_m.
        destruct c as [ | | | e x [ t | ] invs c0 | | | ];
          try (split; [ exact H_m | reflexivity ]).
        destruct (is_tbl_ty t) eqn:E_is; [ | split; [ exact H_m | reflexivity ] ].
        inversion H_m; subst. subst_type_annot.
        lazymatch goal with
        | H_e : type_of Gstore Genv e t, H_c : maintains_invs _ _ _ _ c0,
          H_i : Forall _ invs, H_f : map.get Gstore x = None,
          H_o : forall _ _, _ -> _ -> _ -> _ -> holds_all _ invs |- _ =>
            rename H_e into H_ty, H_c into H_body, H_i into H_invs_wf,
              H_f into H_fresh, H_o into H_init
        end.
        assert (H_wf_t : type_wf t) by (eapply type_of__type_wf; [ | | exact H_ty ]; assumption).
        assert (H_Gs' : tenv_wf (map.put Gstore x t)) by (apply tenv_wf_step; assumption).
        split.
        1:{ cbn [transf_to_idx]. apply MICLetMut with (t := aux_ty t).
            1: apply aux_record_ty; auto.
            1: exact eq_refl.
            1:{ apply maintains_invs_ictx_equiv
                  with (ictx := List.map (transf_inv x) (invs ++ ictx) ++ idx_inv x :: nil).
                1:{ replace (map.put Gstore x (aux_ty t))
                      with (map.put (map.put Gstore x t) x (aux_ty t))
                      by apply Properties.map.put_put_same.
                    eapply transf_to_idx'_maintains_invs with (path_cond := fun _ _ => True);
                      [ apply map.get_put_same | exact E_is | exact H_Gs'
                      | exact H_Ge | | intros; exact I | exact H_body ].
                    apply Forall_app; split; [ exact H_invs_wf | ].
                    eapply Forall_impl; [ | exact H_ictx ]; intros.
                    eapply inv_wf_weaken; [ | eassumption ].
                    apply map_incl_step_r; [ apply map_incl_refl | assumption ]. }
                1: apply tenv_wf_step; [ assumption | apply aux_ty_wf; assumption ].
                1: exact H_Ge.
                1:{ unfold ictx_equiv, holds_all; intros store H_store.
                    rewrite map_app.
                    rewrite (map_ext_in (transf_inv x) (fun i => i) ictx).
                    2:{ intros i H_in. rewrite Forall_forall in H_ictx.
                        eapply transf_inv_unbound; eauto. }
                    rewrite map_id. cbn [app].
                    split; apply Permutation_Forall.
                    1: apply Permutation_sym, Permutation_cons_append.
                    1: apply Permutation_cons_append. } }
            1: apply transf_to_idx_invs_wf; assumption.
            1: exact H_fresh.
            1:{ intros store env H_pc H_h H_store H_env.
                specialize (H_init store env H_pc H_h H_store H_env).
                cbn [interp_expr List.map].
                set (v := interp_expr store env e) in *.
                unfold holds_all in *. constructor.
                1:{ apply (proj2 (idx_inv_holds x _)). rewrite map.get_put_same.
                    unfold aux_wf. rewrite record_sort_access_id, record_sort_access_aux.
                    subst v; eapply to_idx_satisfy_idx_wf with (Gstore := Gstore) (Genv := Genv) (t := t);
                      eauto. }
                rewrite Forall_map.
                eapply Forall_impl; [ | apply Forall_and; [ exact H_invs_wf | exact H_init ] ].
                intros i [ H_i H_hi ].
                apply (transf_inv_holds x t (map.put Gstore x t) i (map.put store x v)); auto.
                1: apply map.get_put_same.
                1: apply locals_wf_step; [ assumption | subst v; eapply type_sound; eauto ].
                unfold consistent_with_global. rewrite !map.get_put_same.
                rewrite record_sort_access_id. split; [ reflexivity | ].
                intros y H_y. rewrite !map.get_put_diff by assumption. reflexivity. } }
        1:{ intros store env H_pc H_store H_env H_h.
            eapply transf_to_idx_preserve_sem; eauto.
            eapply maintains_invs__well_typed; eassumption. }
      Qed.

      Corollary create_idx_at_sound : forall tbl,
          inv_transf_sound (locals := locals) (fun Gstore _ c => at_letmut tbl (fun _ c => create_idx c) Gstore c).
      Proof.
        intros. apply at_letmut_sound. exact create_idx_sound.
      Qed.
    End WithIndex.
End WithMap.
