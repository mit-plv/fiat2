Require Import conquord.Language conquord.Interpret conquord.Value conquord.TypeSystem conquord.TypeSound conquord.IndexInterface
  conquord.Utils conquord.TransfSound conquord.Substitute conquord.TransfUtils.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Require Import List String ZArith Sorted Permutation.
Import ListNotations.

Lemma map_fst_map_triple : forall A B C D (l : list (A * B * C)) (f : B -> D),
    List.map fst (List.map (fun '(a, b, _) => (a, f b)) l) = List.map fst (List.map fst l).
Proof.
  intros; induction l; cbn; auto.
  repeat case_match; cbn; congruence.
Qed.

Ltac NoDup_map_record_sort :=
  eapply Permutation_NoDup;
  [ eapply Permutation_map, Permuted_record_sort
  | cbn; repeat constructor; intuition idtac;
    destruct_In; auto ].

Section compo_idx.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Context (idxs : list (string * IndexInterface.index * (value -> value -> Prop))).
  Context {idxs_ok : Forall (fun '(_, idx, idx_wf) => ok idx idx_wf) idxs}.
  Context (H_tag_NoDup : NoDup (List.map fst (List.map fst idxs))).
  Context (hole0 : string).
  Context (H_holes_eq : Forall (fun '(_, idx, _) => @hole idx = hole0) idxs).

  Definition compo_idx_ty (t : type) : type :=
    TRecord (record_sort (List.map (fun '(tag, idx, _) => (tag, @idx_ty idx t)) idxs)).

  Definition to_compo_idx : expr :=
    ERecord (List.map (fun '(tag, idx, _) => (tag, @to_idx idx)) idxs).

  Definition compo_idx_wf (v v' : value) : Prop :=
    match v' with
    | VRecord v' =>
        Forall (fun '(tag, _, idx_wf) =>
                  match access_record v' tag with
                  | Success v' => idx_wf v v'
                  | _ => False
                  end) idxs
    | _ => False
    end.

  Definition compo_is_tbl_ty (t : type) : bool :=
    forallb (fun '(tag, idx, _) => @is_tbl_ty idx t) idxs.

  Lemma to_compo_idx_ty : forall (t : type),
      type_wf t -> compo_is_tbl_ty t = true ->
      type_of map.empty (map.put map.empty hole0 t) to_compo_idx (compo_idx_ty t).
  Proof.
    unfold compo_is_tbl_ty, to_compo_idx, compo_idx_ty.
    intros. econstructor; eauto using Permuted_record_sort, StronglySorted_record_sort.
    1:{ clear. induction idxs; cbn; auto.
        do 2 case_match; cbn; congruence. }
    1:{ induction idxs; auto. cbn in *.
        repeat invert_Forall; invert_NoDup; rewrite Bool.andb_true_iff in *; intuition idtac.
        constructor; auto.
        do 2 case_match; cbn; subst. eapply (to_idx_ty (idx:=i)); eauto. }
    1:{ revert H_tag_NoDup; clear; intros.
        induction idxs; intros; cbn; auto using NoDup_nil.
        cbn in *; invert_NoDup.
        constructor; auto. do 2 case_match; cbn in *.
        rewrite map_fst_map_triple; auto. }
  Qed.

  Lemma compo_idx_ty_wf : forall t : type,
      type_wf t -> compo_is_tbl_ty t = true ->
      type_wf (compo_idx_ty t).
  Proof.
    unfold compo_is_tbl_ty, compo_idx_ty; intros ? ? H.
    eapply List.forallb_to_Forall with (P:=fun '(_, idx, _) => @is_tbl_ty idx t = true) in H.
    2: intros; repeat case_match; auto.
    constructor; auto using StronglySorted_record_sort.
    1:{ eapply Permutation_NoDup.
        1: apply Permutation_map, Permuted_record_sort.
        induction idxs; cbn in *; auto.
        repeat invert_Forall; invert_NoDup.
        constructor; auto.
        repeat case_match; cbn in *.
        rewrite map_fst_map_triple; auto. }
    1:{ rewrite Forall_map.
        eapply Permutation_Forall.
        1: apply Permuted_record_sort.
        induction H; cbn in *; auto.
        repeat invert_Forall; invert_NoDup.
        constructor; repeat case_match; auto.
        cbn; auto using idx_ty_wf. }
  Qed.

  Lemma NoDup_In_access_record : forall A (l : list (string * A)),
      NoDup (List.map fst l) ->
      forall s v, In (s, v) l ->
                  access_record l s = Success v.
  Proof.
    intros * ? ? ? H_in; induction l; cbn in *.
    1: intuition fail.
    do 2 case_match; rewrite ?eqb_eq, ?eqb_neq in *; invert_NoDup.
    1:{ subst. intuition idtac; try congruence.
        apply in_map with (f:=fst) in H0;
          cbn in *; intuition idtac. }
    1:{ intuition idtac. congruence. }
  Qed.

  Lemma NoDup_Permutation_access_record : forall s A (l l' : list (string * A)),
      NoDup (List.map fst l) ->
      In s (List.map fst l) ->
      Permutation l l' ->
      access_record l s = access_record l' s.
  Proof.
    intros * H_NoDup H_in H_permu.
    apply In_access_record in H_in. destruct_exists.
    rewrite_l_to_r.
    apply access_record_sound in H.
    symmetry. apply NoDup_In_access_record.
    1:{ eapply Permutation_NoDup.
        1: apply Permutation_map; eauto.
        assumption. }
    1:{ eapply Permutation_in; eauto. }
  Qed.

  Lemma to_compo_idx_wf : forall (v : value) (t : type),
      type_wf t -> compo_is_tbl_ty t = true ->
      type_of_value v t ->
      compo_idx_wf v (interp_expr map.empty (map.put map.empty hole0 v) to_compo_idx).
  Proof.
    intros.
    unfold compo_idx_wf, compo_idx_ty, to_compo_idx, compo_is_tbl_ty, record_proj in *.
    cbn [interp_expr].
    rewrite Forall_forall; intros. do 2 case_match.
    erewrite NoDup_Permutation_access_record.
    4: apply Permutation_sym, Permuted_record_sort.
    2:{ eapply Permutation_NoDup.
        1: eapply Permutation_map, Permuted_record_sort.
        rewrite fst_map_fst, map_fst_map_triple; auto. }
    2:{ rewrite in_map_iff. eexists; intuition idtac.
        2:{ eapply Permutation_in.
            1: apply Permuted_record_sort.
            rewrite in_map_iff. exists (s, to_idx).
            intuition idtac.
            rewrite in_map_iff; exists x.
            subst; auto. }
        reflexivity. }
    eapply List.forallb_to_Forall with (P:=fun '(_, idx, _) => @is_tbl_ty idx t = true) in H0.
    2: intros; repeat case_match; auto.
    repeat apply_Forall_In. cbn in *.
    apply to_idx_wf in H1; auto.
    erewrite NoDup_In_access_record; eauto.
    2:{ erewrite in_map_iff. exists (s, to_idx).
        subst; intuition auto.
        erewrite in_map_iff. exists (s, i, P); auto. }
    rewrite fst_map_fst, map_fst_map_triple; auto.
  Qed.

  Instance compo_idx : IndexInterface.index := IndexInterface.mk hole0 to_compo_idx compo_idx_ty compo_is_tbl_ty.

  Instance compo_idx_ok : IndexInterface.ok compo_idx compo_idx_wf :=
    IndexInterface.Build_ok compo_idx compo_idx_wf compo_idx_ty_wf to_compo_idx_ty to_compo_idx_wf.
End compo_idx.

Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (width:=width)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Section WithIndex.
      Context {idx : IndexInterface.index} {idx_wf : value -> value -> Prop} {idx_ok : ok idx idx_wf}.
      Context (id_tag aux_tag: string).
      Context (H_tags_diff : id_tag <> aux_tag).

      Section WithGlobal.
        Context (tbl : string).

      Definition create_aux_write_head (free_vars : list string) (c : command) :=
        match c with
        | CAssign tbl' e =>
            if String.eqb tbl tbl'
            then CAssign tbl (ERecord [(id_tag, e); (aux_tag, substitute ((hole, e) :: nil) free_vars to_idx)])
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

      Definition transf_to_idx' (free_vars : list string) (c : command) : command :=
        fold_command_with_global tbl create_aux_write_head create_aux_read_head free_vars c.

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
        all: try (econstructor; eauto; apply_transf_to_idx_preserve_ty''_IH; apply tenv_wf_step; eauto with conquord_hints).
        3: repeat apply tenv_wf_step; eauto with conquord_hints.
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

      Ltac use_transf_to_idx_preserve_ty'_IH :=
        lazymatch goal with
          IH: context[well_typed _ _ (transf_to_idx' _ ?c)] |- well_typed _ _ (transf_to_idx' _ ?c) =>
            eapply IH; try reflexivity
        end.

      Lemma transf_to_idx_preserve_ty' : forall tbl_ty c (Gstore Gstore' Genv :tenv) free_vars,
          tenv_wf Gstore -> tenv_wf Genv ->
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          well_typed Gstore Genv c ->
          incl (get_free_vars Genv) free_vars ->
          Gstore' = map.put Gstore tbl (aux_ty tbl_ty) ->
          well_typed Gstore' Genv (transf_to_idx' free_vars c).
      Proof.
        induction c; simpl; intros; try invert_well_typed; try now (constructor; auto).
        1: econstructor; eauto using transf_to_idx_preserve_ty''.
        1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
            use_transf_to_idx_preserve_ty'_IH; eauto with conquord_hints.
            eauto using incl_tran, incl_cons_step, get_free_vars_put. }
        1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
            case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
              [ rewrite Properties.map.put_put_same in *; auto
              | rewrite Properties.map.put_put_diff in *; auto;
                use_transf_to_idx_preserve_ty'_IH; eauto with conquord_hints ].
            rewrite_map_get_put_goal. }
        1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
            1:{ econstructor; [ rewrite_map_get_put_goal; eauto | ].
                econstructor.
                3: apply Permuted_record_sort.
                1: reflexivity.
                1:{ repeat constructor; cbn [snd].
                    1:{ invert_well_typed.
                        repeat rewrite_l_to_r; repeat (do_injection; clear_refl).
                        eauto using transf_to_idx_preserve_ty''. }
                    1:{ eapply substitute_preserve_ty with (Genv0:=map.put map.empty hole tbl_ty);
                        eauto using idx_ty_wf with conquord_hints.
                        1:{ apply tenv_wf_step; auto. constructor; auto using StronglySorted_record_sort.
                            1: NoDup_map_record_sort.
                            1:{ eapply Permutation_Forall;
                                [ eapply Permutation_map, Permuted_record_sort | ].
                                cbn. repeat constructor; eauto using idx_ty_wf. } }
                1:{ eapply type_of_strengthen; eauto using to_idx_ty, map_incl_refl.
                    apply map_incl_empty. }
                1:{ unfold sub_wf. simpl; intros.
                    case_match_string_eqb; rewrite_l_to_r; repeat do_injection;
                      [ auto using transf_to_idx_preserve_ty''
                      | rewrite map.get_empty in *; discriminate ]. } } }
                1: cbn; repeat constructor; intuition idtac; destruct_In; auto.
                1: apply StronglySorted_record_sort. }
                1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
                    rewrite_map_get_put_goal; eauto. } }
            1: constructor; eauto using transf_to_idx_preserve_ty''.
        1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
            use_transf_to_idx_preserve_ty'_IH; eauto with conquord_hints.
            eauto using incl_tran, incl_cons_step, get_free_vars_put. }
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
        all: try now (repeat (use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints)).
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            case_match; auto; f_equal.
            apply_type_sound e1; eauto. rewrite_l_to_r.
            invert_type_of_value_clear.
            apply In_flat_map_ext; intros. apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints. }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            case_match; auto. do 2 f_equal.
            apply_type_sound e1. rewrite_l_to_r; invert_type_of_value_clear.
            apply In_flat_map_ext; intros.
            rewrite Forall_map_fst with (P:= fun v => type_of_value v t1) in *.
            lazymatch goal with
              H: In _ _ |- _ => apply bag_to_list_incl in H end.
            apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints. }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            case_match; auto. do 2 f_equal.
            apply_type_sound e1. rewrite_l_to_r; invert_type_of_value_clear.
            apply In_flat_map_ext; intros.
            apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints. }
        1:{ repeat
              (use_transf_to_idx_preserve_sem''_IH; eauto;
               case_match; auto; f_equal;
               lazymatch goal with
                 _: interp_expr _ _ ?e = _ |- _ =>
                   apply_type_sound e
               end; eauto; rewrite_l_to_r;
               invert_type_of_value_clear).
            apply In_flat_map2_ext; intros. repeat apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH; try apply tenv_wf_step; eauto with conquord_hints. }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            case_match; auto.
            revert IHtype_of3;
              use_transf_to_idx_preserve_sem''_IH; eauto; intros.
            apply_type_sound e1; rewrite_l_to_r; invert_type_of_value_clear.
            eapply In_fold_right_ext with (P:=fun v => type_of_value v t2);
              intros; intuition idtac; try apply_Forall_In.
            1: eapply type_sound; eauto.
            1: use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints;
            eapply tenv_wf_step; eauto with conquord_hints.
            1:{ use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints.
                2: eapply tenv_wf_step; eauto with conquord_hints.
                eapply type_sound; eauto with conquord_hints.
                eapply tenv_wf_step; eauto with conquord_hints. } }
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
              use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints. }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            apply_type_sound d. invert_type_of_value_clear.
            revert IHtype_of3.
            use_transf_to_idx_preserve_sem''_IH; eauto; intros.
            apply In_fold_right_ext with (P:=fun v => type_of_value v t); eauto with conquord_hints.
            intros. apply_Forall_In. intuition idtac;
              use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints.
            2: eapply type_sound; eauto with conquord_hints.
            all: repeat apply tenv_wf_step; eauto with conquord_hints. }
        1,2,3: use_transf_to_idx_preserve_sem''_IH; eauto;
        apply_type_sound e; invert_type_of_value_clear;
        f_equal; apply In_filter_ext; intros; apply_Forall_In;
        use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints.
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            apply_type_sound e1. invert_type_of_value_clear.
            use_transf_to_idx_preserve_sem''_IH; eauto.
            apply_type_sound e2. invert_type_of_value_clear.
            f_equal. apply In_flat_map_ext; intros; apply_Forall_In.
            repeat lazymatch goal with
                     H: VList _ = _ |- _ => clear H
                   end.
            induction l0; cbn; auto. invert_Forall.
            erewrite IHtype_of3; eauto with conquord_hints.
            2: repeat apply tenv_wf_step; eauto with conquord_hints.
            do 2 (case_match; auto). cbn.
            rewrite IHl0; auto.
            use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints.
            repeat apply tenv_wf_step; eauto with conquord_hints. }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            apply_type_sound e1. invert_type_of_value_clear.
            use_transf_to_idx_preserve_sem''_IH; eauto.
            apply_type_sound e2. invert_type_of_value_clear.
            do 2 f_equal. apply In_flat_map_ext; intros.
            lazymatch goal with
              H: In _ (bag_to_list _) |- _ => apply bag_to_list_incl in H end.
            rewrite Forall_map_fst with (P:=fun v => type_of_value v t1) in *.
            apply_Forall_In. apply In_map_ext2.
            1:{ apply In_filter_ext; intros.
                lazymatch goal with
                  H: In _ (bag_to_list _) |- _ => apply bag_to_list_incl in H end.
                rewrite Forall_map_fst with (P:=fun v => type_of_value v t2) in *.
                apply_Forall_In.
                use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints.
                repeat apply tenv_wf_step; eauto with conquord_hints. }
            1:{ intros.
                lazymatch goal with
                  H: In _ (filter _ (bag_to_list _)) |- _ =>
                    apply filter_In in H as [H _];
                    apply bag_to_list_incl in H end.
                rewrite Forall_map_fst with (P:=fun v => type_of_value v t2) in *.
                apply_Forall_In.
                use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints.
                repeat apply tenv_wf_step; eauto with conquord_hints. } }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            apply_type_sound e1. invert_type_of_value_clear.
            use_transf_to_idx_preserve_sem''_IH; eauto.
            apply_type_sound e2. invert_type_of_value_clear.
            do 2 f_equal. apply In_flat_map_ext; intros.
            apply_Forall_In. apply In_map_ext2.
            1:{ apply In_filter_ext; intros.
                apply_Forall_In.
                use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints.
                repeat apply tenv_wf_step; eauto with conquord_hints. }
            1:{ intros.
                lazymatch goal with
                  H: In _ (filter _ _) |- _ =>
                    apply filter_In in H as [H _] end.
                apply_Forall_In.
                use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints.
                repeat apply tenv_wf_step; eauto with conquord_hints. } }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            apply_type_sound e. invert_type_of_value_clear.
            f_equal. apply map_ext_in.
            intros; apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints. }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            apply_type_sound e. invert_type_of_value_clear.
            do 2 f_equal.
            apply map_ext_in; intros.
            lazymatch goal with
              H: In _ (bag_to_list _) |- _ => apply bag_to_list_incl in H end.
            rewrite Forall_map_fst with (P:=fun v => type_of_value v t1) in *.
            apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints. }
        1:{ use_transf_to_idx_preserve_sem''_IH; eauto.
            apply_type_sound e. invert_type_of_value_clear.
            do 2 f_equal.
            apply map_ext_in; intros.
            apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH; eauto with conquord_hints. }
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

      Lemma transf_to_idx_preserve_sem' : forall tbl_ty c (Gstore Genv : tenv) free_vars,
          well_typed Gstore Genv c ->
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          incl (get_free_vars Genv) free_vars ->
          tenv_wf Gstore -> tenv_wf Genv ->
          forall (store store' env : locals),
            locals_wf Gstore store -> locals_wf Genv env ->
            consistent_with_global store store' ->
            consistent_with_global (interp_command store env c) (interp_command store' env (transf_to_idx' free_vars c)).
      Proof.
        intros * H. revert free_vars. induction H; cbn; auto; intros.
        1:{ use_transf_to_idx_preserve_sem'_IH; auto.
            eapply command_type_sound; eauto. }
        1:{ erewrite transf_to_idx_preserve_sem''; eauto.
            use_transf_to_idx_preserve_sem'_IH; eauto with conquord_hints.
            eauto using incl_tran, incl_cons_step, get_free_vars_put. }
        1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
            1:{ unfold consistent_with_global.
                rewrite !Properties.map.get_update_same.
                unfold consistent_with_global in *; intuition auto.
                rewrite !Properties.map.get_update_diff; auto.
                do 2 f_equal. apply map.map_ext. intros.
                destruct_get_put_strings. f_equal.
                erewrite transf_to_idx_preserve_sem''; eauto.
                unfold consistent_with_global; auto. }
            1:{ apply consistent_with_global_update; auto.
                use_transf_to_idx_preserve_sem'_IH; eauto with conquord_hints.
                1: rewrite_map_get_put_goal.
                apply consistent_with_global_put_local; auto.
                erewrite transf_to_idx_preserve_sem''; eauto. } }
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
            1: eapply command_type_sound; eauto with conquord_hints.
            use_transf_to_idx_preserve_sem'_IH; eauto with conquord_hints.
            eauto using incl_tran, incl_cons_step, get_free_vars_put. }
      Qed.

      Definition aux_wf (v : value) :=
        match v with
          VRecord rv =>
            match access_record rv id_tag with
            | Success v_id =>
                match access_record rv aux_tag with
                | Success v_aux =>
                    idx_wf v_id v_aux
                | _ => False
                end
            | _ => False
            end
        | _ => False
        end.

      Lemma well_typed__aux_wf_nil : forall c Gstore Genv,
          tenv_wf Gstore -> tenv_wf Genv ->
          well_typed Gstore Genv c ->
          forall P,
            (forall x v, P x v <-> value_wf_with_globals aux_wf nil x v) ->
            parameterized_wf Gstore Genv P c.
      Proof.
        induction 3; intros.
        all: try now (constructor; auto).
        1:{ econstructor; eauto. apply IHwell_typed; eauto with conquord_hints. }
        1:{ econstructor; eauto. apply IHwell_typed; eauto with conquord_hints.
            intros. split.
            1: constructor.
            1:{ unfold rm_from_pred. intros; right. rewrite H3. constructor. } }
        1:{ econstructor; eauto. intros. rewrite H3; constructor. }
        1:{ econstructor; eauto. apply IHwell_typed; eauto with conquord_hints. }
      Qed.

      Lemma rm_from_aux_wf__aux_wf_nil : forall (x : string) (v : value),
          rm_from_pred (value_wf_with_globals aux_wf (tbl :: nil)) tbl x v <-> value_wf_with_globals aux_wf nil x v.
      Proof.
        intros. split.
        1: constructor.
        1:{ intros. unfold rm_from_pred.
            destruct (String.eqb x tbl) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *;
              subst; intuition auto.
            right. constructor; auto. }
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
        auto using idx_ty_wf.
      Qed.

      Lemma to_idx_satisfy_idx_wf : forall free_vars e Gstore Genv t store env,
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv e t ->
          is_tbl_ty t = true ->
          incl (get_free_vars Genv) free_vars ->
          locals_wf Gstore store -> locals_wf Genv env ->
          idx_wf (interp_expr store env e)
            (interp_expr store env (substitute ((hole, e) :: nil) free_vars to_idx)).
      Proof.
      intros. erewrite substitute_preserve_sem with (Genv0:=map.put map.empty hole t).
      5: eauto. 8,9: eauto. all: auto.
      3: eapply type_of_strengthen; try apply to_idx_ty.
      all: eauto with conquord_hints.
      3: apply map_incl_step; try apply string_dec.
      2,3: apply map_incl_empty.
      2:{ unfold sub_wf; intros. simpl.
          case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
            rewrite_map_get_put_hyp;
            [ do_injection; auto
            | rewrite map.get_empty in *; discriminate ]. }
      unfold make_sub_env.
      erewrite interp_expr_strengthen with (e:=to_idx); [ eapply to_idx_wf | .. ].
      6: apply to_idx_ty.
      all: eauto with conquord_hints.
      1: apply map_incl_empty.
      1: simpl; apply map_incl_step; auto using string_dec, map_incl_refl.
    Qed.


      Ltac apply_transf_to_idx'_index_wf_IH :=
        lazymatch goal with
          IH: context[parameterized_wf _ _ _ (transf_to_idx' _ ?c)] |- context[?c] =>
            apply IH
        end.

      Lemma transf_to_idx'_index_wf : forall tbl_ty c free_vars Gstore Genv,
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          well_typed Gstore Genv c ->
        incl (get_free_vars Genv) free_vars ->
        tenv_wf Gstore -> tenv_wf Genv ->
        parameterized_wf (map.put Gstore tbl (aux_ty tbl_ty)) Genv (value_wf_with_globals aux_wf [tbl]) (transf_to_idx' free_vars c).
      Proof.
        unfold value_wf_with_globals.
        induction c; simpl; intros; try invert_well_typed; try now (constructor; auto).
        1:{ econstructor.
            1: apply transf_to_idx_preserve_ty''; eauto.
            apply_transf_to_idx'_index_wf_IH; eauto with conquord_hints.
            eauto using incl_tran, incl_cons_step, get_free_vars_put. }
        1:{ econstructor.
            1: apply transf_to_idx_preserve_ty''; eauto.
            case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
            1:{ rewrite Properties.map.put_put_same.
                apply well_typed__aux_wf_nil; eauto with conquord_hints.
                apply rm_from_aux_wf__aux_wf_nil. }
            1:{ rewrite Properties.map.put_put_diff; auto.
              eapply parameterized_wf_Proper; try reflexivity; auto.
              1:{ apply rm_not_in_globals.
                  intro contra. inversion contra; auto. }
              apply IHc; eauto with conquord_hints.
              rewrite_map_get_put_goal. } }
      1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          1:{ econstructor.
              2: rewrite_map_get_put_goal; eauto.
              2:{ rewrite_l_to_r. do_injection.
                  econstructor; [ | | apply Permuted_record_sort | .. ]; auto using StronglySorted_record_sort.
                  1:{ repeat constructor; eauto using transf_to_idx_preserve_ty''.
                      eapply substitute_preserve_ty with (Genv0:=map.put map.empty hole t);
                        eauto using aux_ty_wf with conquord_hints.
                      1:{ eapply type_of_strengthen.
                          1: apply to_idx_ty; eauto with conquord_hints.
                          1: apply map_incl_empty.
                          1: apply map_incl_refl. }
                      1:{ unfold sub_wf; intros; simpl.
                          destruct (String.eqb x hole) eqn:E_x;
                            rewrite ?eqb_eq, ?eqb_neq in *; subst; rewrite_map_get_put_hyp; try do_injection; auto using transf_to_idx_preserve_ty''.
                          rewrite map.get_empty in *; congruence. } }
                  1:{ repeat constructor; intuition auto. destruct_In; auto. } }
              1:{ intros. rewrite Forall_forall; intros. destruct_In; intuition idtac.
                  right. unfold aux_wf. cbn [interp_expr List.map].
                  repeat (erewrite NoDup_In_access_record;
                          [
                          | NoDup_map_record_sort
                          | eapply Permutation_in; [ apply Permuted_record_sort | ];
                            cbn; auto ]).
                  rewrite_l_to_r; do_injection; clear_refl.
                  eapply to_idx_satisfy_idx_wf.
                  3: apply transf_to_idx_preserve_ty'';
                  [ | | eauto .. ]; auto.
                  all: eauto using aux_ty_wf with conquord_hints. } }
          1:{ econstructor.
              2: rewrite_map_get_put_goal; eauto.
              2: apply transf_to_idx_preserve_ty''; auto.
              intros. unfold aux_wf. constructor; auto. } }
      1:{ constructor; try apply_transf_to_idx'_index_wf_IH; intuition.
          apply transf_to_idx_preserve_ty''; auto. }
      1:{ econstructor; eauto.
          1: apply transf_to_idx_preserve_ty''; eauto.
          apply_transf_to_idx'_index_wf_IH; eauto with conquord_hints.
          eauto using incl_tran, incl_cons_step, get_free_vars_put. }
      Qed.
      End WithGlobal.

      Definition transf_to_idx (free_vars : list string) (c : command) : command :=
        match c with
        | CLetMut e tbl c =>
            CLetMut (ERecord [(id_tag, e); (aux_tag, substitute ((hole, e) :: nil) free_vars to_idx)]) tbl
              (transf_to_idx' tbl free_vars c)
        | _ => c
        end.

      Lemma transf_to_idx_preserve_ty : forall tbl tbl_ty e c free_vars Gstore Genv,
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv e tbl_ty ->
          well_typed (map.put Gstore tbl tbl_ty) Genv c ->
          is_tbl_ty tbl_ty = true ->
          incl (get_free_vars Genv) free_vars ->
          well_typed Gstore Genv (transf_to_idx free_vars (CLetMut e tbl c)).
      Proof.
        simpl; intros. subst. econstructor.
        1:{ econstructor.
            1: instantiate (1:=[(id_tag, tbl_ty); (aux_tag, idx_ty tbl_ty)]); reflexivity.
            1:{ cbn; repeat constructor; auto.
                eapply substitute_preserve_ty with (Genv0:=map.put map.empty hole tbl_ty); eauto using incl_refl with conquord_hints.
            1: eapply type_of_strengthen; [ apply to_idx_ty; eauto | apply map_incl_empty | apply map_incl_refl ].
            1: eapply type_of__type_wf; [ | | eauto ]; auto.
            1:{ unfold sub_wf. simpl; intros.
                destruct_get_put_strings;
                  [ do_injection; rewrite eqb_refl; auto
                  | rewrite map.get_empty in *; discriminate ]. } }
            1: eapply Permuted_record_sort.
            1:{ cbn; repeat constructor; intuition auto. inversion H5; auto using in_nil. }
            1: apply StronglySorted_record_sort. }
        1:{ erewrite <- Properties.map.put_put_same.
            eapply transf_to_idx_preserve_ty'; try reflexivity; eauto using incl_refl with conquord_hints.
            rewrite_map_get_put_goal; auto. }
      Qed.

      Lemma transf_to_idx_preserve_sem : forall tbl tbl_ty e c (Gstore Genv : tenv) free_vars,
          is_tbl_ty tbl_ty = true ->
          type_of Gstore Genv e tbl_ty ->
          well_typed (map.put Gstore tbl tbl_ty) Genv c ->
          incl (get_free_vars Genv) free_vars ->
          tenv_wf Gstore -> tenv_wf Genv ->
          forall (store env : locals),
            locals_wf Gstore store -> locals_wf Genv env ->
            interp_command store env (transf_to_idx free_vars (CLetMut e tbl c)) = interp_command store env (CLetMut e tbl c).
      Proof.
        simpl; intros.
        apply stores_eq_except__update_eq. symmetry.
        eapply consistent_with_global__store_eq_except; eauto.
        eapply transf_to_idx_preserve_sem'; eauto with conquord_hints.
        1: rewrite_map_get_put_goal; auto.
        unfold consistent_with_global; intuition idtac; repeat rewrite_map_get_put_goal.
        erewrite NoDup_In_access_record; eauto.
        1: eapply Permutation_NoDup;
        [ eapply Permutation_map, Permuted_record_sort
        | cbn; repeat constructor; intuition idtac;
          destruct_In; auto ].
        eapply Permutation_in; [ eapply Permuted_record_sort | ]; constructor; auto.
      Qed.

      Definition apply_after_letmut f (c : command) :=
        match c with
        | CLetMut e x c => CLetMut e x (f x c)
        | _ => c
        end.

      Definition apply_idx_related_transfs (f : string -> command -> command) (Gstore Genv : tenv) (c : command) :=
        match c with
        | CLetMut e x _ => match synthesize_expr Gstore Genv e with
                           | Success (t, _) => if is_tbl_ty t
                                               then apply_after_letmut f (transf_to_idx (get_free_vars Genv) c)
                                                 else c
                             | _ => c
                             end
        | _ => c
        end.

      Lemma to_idx_preserve_ty : forall Gstore Genv free_vars e t,
          type_wf t -> is_tbl_ty t = true ->
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv e t ->
          incl (get_free_vars Genv) free_vars ->
          type_of Gstore Genv (substitute ((hole, e) :: nil) free_vars to_idx) (idx_ty t).
      Proof.
        intros. eapply substitute_preserve_ty;
          [ | | eapply type_of_strengthen; eauto using to_idx_ty | .. ]; auto.
        2: apply map_incl_empty.
        2: apply map_incl_refl.
        1: eauto with conquord_hints.
        1:{ unfold sub_wf; simpl; intros.
            case_match_string_eqb; try congruence.
            rewrite map.get_empty in *; discriminate. }
      Qed.

      Ltac apply_to_aux_preserve_ty :=
        econstructor; [ | |  apply Permuted_record_sort | .. ];
        auto using StronglySorted_record_sort;
        cbn; auto; repeat constructor; intuition idtac;
        try destruct_In; eauto;
        apply to_idx_preserve_ty; eauto using incl_refl with conquord_hints.

      Lemma apply_idx_related_transfs_sound : forall f,
          aug_transf_sound is_tbl_ty aux_ty aux_wf f ->
          transf_sound (locals:=locals) (apply_idx_related_transfs f).
      Proof.
        unfold apply_idx_related_transfs, transf_sound; intros.
        repeat (case_match; auto). invert_well_typed.
        eapply synthesizable_ty_unique in E0 as H_syn_ty; eauto; subst.
        assert (H_ty : well_typed (map.put Gstore x (aux_ty t)) Genv (transf_to_idx' x (get_free_vars Genv) c0)).
        { erewrite <- Properties.map.put_put_same.
          eapply transf_to_idx_preserve_ty'; try reflexivity; [ | eauto using incl_refl .. ].
          2: rewrite_map_get_put_goal; eauto.
          1: eauto with conquord_hints. }
        assert (H_wf : parameterized_wf (map.put Gstore x (aux_ty t)) Genv (value_wf_with_globals aux_wf [x]) (transf_to_idx' x (get_free_vars Genv) c0)).
        { erewrite <- Properties.map.put_put_same.
          apply transf_to_idx'_index_wf; eauto using incl_refl with conquord_hints.
          rewrite_map_get_put_goal; auto. }
        eapply H in H_wf. 5: eauto.
        all: eauto using aux_ty_wf with conquord_hints.
        2: constructor;  try eapply map.get_put_same; auto.
        split.
        1:{ econstructor.
            2: apply H_wf; auto.
            1: apply_to_aux_preserve_ty. }
        1:{ intros. unfold transf_to_idx, apply_after_letmut.
            cbn [interp_command]. eapply stores_eq_except__update_eq; intros.
            destruct (map.get Gstore x0) eqn:E.
            1:{ symmetry.
                intuition idtac. erewrite H11; auto.
                2:{ resolve_locals_wf. eapply type_sound.
                    1: apply_to_aux_preserve_ty.
                all: resolve_locals_wf; eauto using incl_refl with conquord_hints. }
                2:{ constructor; auto. destruct (String.eqb k x) eqn:E_kx;
                    rewrite ?eqb_eq, ?eqb_neq in *; subst; auto; right.
                    rewrite_map_get_put_hyp; do_injection.
                    unfold aux_wf.
                    repeat (erewrite NoDup_In_access_record;
                          [
                          | NoDup_map_record_sort
                          | eapply Permutation_in; [ apply Permuted_record_sort | ];
                            cbn; auto ]).
                    eapply to_idx_satisfy_idx_wf; [ | | eauto .. ]; auto using incl_refl. }
                eapply transf_to_idx_preserve_sem' with (Gstore:=map.put Gstore x t); eauto.
                all: try rewrite_map_get_put_goal; eauto using incl_refl with conquord_hints.
                unfold consistent_with_global; intuition idtac; repeat rewrite_map_get_put_goal.
                cbn [interp_expr].
                erewrite NoDup_In_access_record;
                  [
                  | NoDup_map_record_sort
                  | eapply Permutation_in; [ apply Permuted_record_sort | ];
                    cbn; auto ]. reflexivity. }
            1:{ repeat erewrite command_preserve_untouched_store. 4: eauto.
                9: apply H_wf.
                all: repeat rewrite_map_get_put_goal; eauto with conquord_hints.
                1:{ apply tenv_wf_step; eauto with conquord_hints. apply aux_ty_wf; eauto with conquord_hints. }
                apply locals_wf_step; auto. eapply type_sound. 1: apply_to_aux_preserve_ty.
                all: auto. } }
      Qed.
    End WithIndex.
End WithMap.

Ltac apply_transf_sound_lemmas :=
  lazymatch goal with
  | |- transf_sound (apply_idx_related_transfs _ _ _) => apply apply_idx_related_transfs_sound
  | |- aug_transf_sound _ _ _ (fun _ => Basics.compose _ _) => apply aug_transf_sound_compose
  | |- transf_sound (fun _ _ => Basics.compose _ _) => apply transf_sound_compose
  | |- aug_transf_sound _ _ _ (fun _ => repeat_transf _ _) => apply repeat_transf_preserve_aug_transf_sound
  | |- aug_transf_sound _ _ _ _ => apply fold_command_with_globals_sound
  | |- transf_sound ?x => unfold x
  end.

#[export] Hint Extern 5 (aux_wf_for_idx _ _ _ _ _) =>
  intros; unfold aux_wf, aux_wf_for_idx, compo_idx_wf in *;
  repeat destruct_match_hyp; intuition idtac;
  repeat invert_Forall;
  destruct_match_hyp; intuition idtac : transf_hints.
#[export] Hint Extern 5 (aux_ty_for_idx _ _ _ _ _) =>
  unfold aux_ty_for_idx, aux_ty; cbn : transf_hints.
#[export] Hint Extern 5 (forall t, IndexInterface.is_tbl_ty t = true -> _ = true) =>
  unfold IndexInterface.is_tbl_ty; cbn; intros;
  rewrite !Bool.andb_true_iff in *; intuition idtac : transf_hints.
