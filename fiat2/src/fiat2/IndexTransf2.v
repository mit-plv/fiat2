Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface2
  fiat2.Utils fiat2.TransfSound fiat2.Substitute fiat2.TransfUtils.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Require Import List String ZArith Sorted Permutation.
Import ListNotations.

Fixpoint mk_compo_idx' (e : expr) (free_vars : list string) (idxs : list (string * IndexInterface2.index)) :=
  match idxs with
  | nil => nil
  | (tag, idx) :: idxs => (tag, substitute [(@hole idx, e)] free_vars (@to_idx idx)) :: mk_compo_idx' e free_vars idxs
  end.

Definition mk_compo_idx (e : expr) (free_vars : list string) (idxs : list (string * IndexInterface2.index)) :=
  ERecord (mk_compo_idx' e free_vars idxs).

Lemma map_fst_map_triple : forall A B C D (l : list (A * B * C)) (f : B -> D),
    List.map fst (List.map (fun '(a, b, _) => (a, f b)) l) = List.map fst (List.map fst l).
Proof.
  intros; induction l; cbn; auto.
  repeat case_match; cbn; congruence.
Qed.

Section compo_idx.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Context {idxs : list (string * IndexInterface2.index * (value -> value -> Prop))}.
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
        Forall (fun '(tag, _, idx_wf) => idx_wf v (record_proj tag v')) idxs
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

  Instance compo_idx : IndexInterface2.index := IndexInterface2.mk hole0 to_compo_idx compo_idx_ty compo_is_tbl_ty.

  Instance compo_idx_ok : IndexInterface2.ok compo_idx compo_idx_wf :=
    IndexInterface2.Build_ok compo_idx compo_idx_wf compo_idx_ty_wf to_compo_idx_ty to_compo_idx_wf.
End compo_idx.

Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (width:=width)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Section WithIndex.
      Context {idx : IndexInterface2.index} {idx_wf : value -> value -> Prop} {idx_ok : ok idx idx_wf}.
      Context (id_tag aux_tag: string).
      Context (H_tags_diff : id_tag <> aux_tag).
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

      Definition transf_to_idx (free_vars : list string) (c : command) : command :=
        match c with
        | CLetMut e tbl c =>
            CLetMut (ERecord [(id_tag, e); (aux_tag, substitute ((hole, e) :: nil) free_vars to_idx)]) tbl
              (transf_to_idx' free_vars c)
        | _ => c
        end.

      Ltac apply_transf_to_idx_preserve_ty''_IH :=
        lazymatch goal with IH: context[type_of _ _ ?e _ ] |- type_of _ _ ?e _ => apply IH end.

      Lemma transf_to_idx_preserve_ty'' : forall tbl_ty e Gstore Genv t,
          tenv_wf Gstore -> tenv_wf Genv ->
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          type_of Gstore Genv e t ->
          type_of (map.put Gstore tbl
                     (TRecord
                        (record_sort
                           [(id_tag, tbl_ty); (aux_tag, idx_ty tbl_ty)]))) Genv (fold_expr create_aux_read_head e) t.
      Proof.
        induction 5 using type_of_IH; simpl; intros.
        all: try (econstructor; eauto; apply_transf_to_idx_preserve_ty''_IH; apply tenv_wf_step; eauto with fiat2_hints).
        3: repeat apply tenv_wf_step; eauto with fiat2_hints.
        1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
            1:{ repeat rewrite_l_to_r; do_injection.
                repeat econstructor; try rewrite_map_get_put_goal; eauto.
                apply NoDup_In_access_record.
                1:{ eapply Permutation_NoDup.
                    1: eapply Permutation_map; apply Permuted_record_sort.
                    cbn; repeat constructor; intuition idtac.
                    destruct_In; auto. }
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
          Gstore' = map.put Gstore tbl
                      (TRecord
                         (record_sort
                            [(id_tag, tbl_ty); (aux_tag, idx_ty tbl_ty)])) ->
          well_typed Gstore' Genv (transf_to_idx' free_vars c).
      Proof.
        induction c; simpl; intros; try invert_well_typed; try now (constructor; auto).
        1: econstructor; eauto using transf_to_idx_preserve_ty''.
        1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
            use_transf_to_idx_preserve_ty'_IH; eauto with fiat2_hints.
            eauto using incl_tran, incl_cons_step, get_free_vars_put. }
        1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
            case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
              [ rewrite Properties.map.put_put_same in *; auto
              | rewrite Properties.map.put_put_diff in *; auto;
                use_transf_to_idx_preserve_ty'_IH; eauto with fiat2_hints ].
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
                        eauto using idx_ty_wf with fiat2_hints.
                        1:{ apply tenv_wf_step; auto. constructor; auto using StronglySorted_record_sort.
                            1: eapply Permutation_NoDup;
                            [ eapply Permutation_map, Permuted_record_sort
                            | cbn; repeat constructor; intuition idtac;
                              destruct_In; auto ].
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
            use_transf_to_idx_preserve_ty'_IH; eauto with fiat2_hints.
            eauto using incl_tran, incl_cons_step, get_free_vars_put. }
      Qed.

      Lemma transf_to_idx_preserve_ty : forall tbl_ty e c free_vars Gstore Genv,
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
                eapply substitute_preserve_ty with (Genv0:=map.put map.empty hole tbl_ty); eauto using incl_refl with fiat2_hints.
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
            eapply transf_to_idx_preserve_ty'; try reflexivity; eauto using incl_refl with fiat2_hints.
            rewrite_map_get_put_goal; auto. }
      Qed.
    End WithIndex.
End WithTags.
