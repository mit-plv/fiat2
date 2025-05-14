Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface
  fiat2.Utils fiat2.TransfSound fiat2.CollectionTag fiat2.TransfUtils fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Require Import List String ZArith Permutation.
Import ListNotations.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (word:=word)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.
  Context {aenv: map.map string collection_tag} {aenv_ok: map.ok aenv}.

  Section WithIndex.
    Context {to_from_con from_to_con : collection_tag}.
    Context {idx : IndexInterface.index} {idx_wf : value -> Prop} {idx_ok : ok to_from_con from_to_con idx idx_wf consistent}.
    (* ??? TODO: generalize to a consistency lattice structure *)

    Lemma to_idx_idx_wf : forall Gstore Genv e t free_vars,
        type_wf t -> is_tbl_ty t = true ->
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e t ->
        incl (get_free_vars Genv) free_vars ->
        forall store env,
          locals_wf Gstore store -> locals_wf Genv env ->
          idx_wf (interp_expr store env (substitute ((hole, e) :: nil) free_vars to_idx)).
    Proof.
      intros.
      erewrite substitute_preserve_sem with (Genv0:=map.put map.empty hole t).
      7-9: eauto.
      6:{ unfold sub_wf; intros; simpl.
          case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
            rewrite_map_get_put_hyp; rewrite ?map.get_empty in *; congruence. }
      all: eauto with fiat2_hints.
      2: apply tenv_wf_step; eauto using tenv_wf_empty with fiat2_hints.
      2:{ eapply type_of_strengthen. 1: apply to_idx_ty.
          all: eauto with fiat2_hints.
          1: apply map_incl_empty.
          1: apply map_incl_refl. }
      erewrite interp_expr_strengthen.
      1: eapply to_idx_wf; eauto.
      4: apply to_idx_ty.
      9: simpl; apply map_incl_refl.
      all: eauto using tenv_wf_empty, locals_wf_empty,
          type_sound with fiat2_hints.
      apply map_incl_empty.
    Qed.

    Lemma to_idx_satisfy_idx_wf : forall free_vars e Gstore Genv t store env,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e t ->
        is_tbl_ty t = true ->
        incl (get_free_vars Genv) free_vars ->
        locals_wf Gstore store -> locals_wf Genv env ->
        idx_wf (interp_expr store env (substitute ((hole, e) :: nil) free_vars to_idx)).
    Proof.
      intros. erewrite substitute_preserve_sem with (Genv0:=map.put map.empty hole t).
      5: eauto. 8,9: eauto. all: auto.
      3: eapply type_of_strengthen; try apply to_idx_ty.
      all: eauto using tenv_wf_empty with fiat2_hints.
      3: apply map_incl_step; try apply string_dec.
      2,3: apply map_incl_empty.
      2:{ unfold sub_wf; intros. simpl.
          case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
            rewrite_map_get_put_hyp;
            [ do_injection; auto
            | rewrite map.get_empty in *; discriminate ]. }
      erewrite interp_expr_strengthen; [ eapply to_idx_wf | .. ].
      6: apply to_idx_ty.
      all: eauto using tenv_wf_empty, locals_wf_empty with fiat2_hints.
      1: apply map_incl_empty.
      1: simpl; apply map_incl_step; auto using string_dec, map_incl_refl.
    Qed.

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
      1: eauto using tenv_wf_empty with fiat2_hints.
      1:{ unfold sub_wf; simpl; intros.
          case_match_string_eqb; try congruence.
          rewrite map.get_empty in *; discriminate. }
    Qed.

    Lemma from_idx_preserve_ty : forall Gstore Genv e t free_vars,
        type_wf t -> is_tbl_ty t = true ->
        incl (get_free_vars Genv) free_vars ->
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e (idx_ty t) ->
        type_of Gstore Genv (substitute ((hole, e) :: nil) free_vars from_idx) t.
    Proof.
      intros. eapply substitute_preserve_ty;
        [ | | eapply type_of_strengthen; eauto using from_idx_ty | .. ]; auto.
      2: apply map_incl_empty.
      2: apply map_incl_refl.
      1: eauto using tenv_wf_empty with fiat2_hints.
      1:{ unfold sub_wf; simpl; intros.
          case_match_string_eqb; try congruence.
          rewrite map.get_empty in *; discriminate. }
    Qed.


    Definition can_transf_to_index' (max_i : collection_tag) (istr0 : aenv) (tbl : string) (c : command) :=
      let (_, _, inv) := command_tag_req istr0 c in
      match map.get inv tbl with
      | Some i => collection_tag_leb i max_i
      | _ => true
      end.

    Definition can_transf_to_index (max_i : collection_tag) (t : type) (istr : aenv) (c : command) :=
      (* expect t to be the type of e, istr to map all free mut vars in c except tbl to LikeList *)
      match c with
      | CLetMut e tbl c' =>
          (is_tbl_ty t && can_transf_to_index' max_i (map.put istr tbl LikeSet) tbl c')%bool
      | _ => false
      end.

    Definition idx_read_to_list_read (tbl : string) (e : expr) :=
      match e with
      | ELoc tbl' => if String.eqb tbl tbl'
                     then substitute ((hole, (ELoc tbl)) :: nil) nil from_idx
                     else e
      | _ => e
      end.

    Definition list_write_to_idx_write (tbl : string) (free_vars : list string) (c : command) :=
      match c with
      | CAssign tbl' e =>
          if String.eqb tbl tbl'
          then CAssign tbl (substitute ((hole, e) :: nil) free_vars to_idx)
          else c
      | _ => c
      end.

    Definition transf_to_idx' (free_vars : list string) (tbl : string) (c : command) : command :=
      fold_command_with_global tbl (list_write_to_idx_write tbl) (idx_read_to_list_read tbl) free_vars c.

    Definition transf_to_idx (free_vars : list string) (c : command) : command :=
      match c with
      | CLetMut e tbl c =>
          CLetMut (substitute ((hole, e)::nil) free_vars to_idx) tbl
            (transf_to_idx' free_vars tbl c)
      | _ => c
      end.

    Ltac apply_transf_to_idx_preserve_ty''_IH :=
      lazymatch goal with IH: context[type_of _ _ ?e _ ] |- type_of _ _ ?e _ => apply IH end.

    Lemma transf_to_idx_preserve_ty'' : forall tbl tbl_ty e Gstore Genv t,
        tenv_wf Gstore -> tenv_wf Genv ->
        map.get Gstore tbl = Some tbl_ty ->
        is_tbl_ty tbl_ty = true ->
        type_of Gstore Genv e t ->
        type_of (map.put Gstore tbl (idx_ty tbl_ty)) Genv (fold_expr (idx_read_to_list_read tbl) e) t.
    Proof.
      induction 5 using @type_of_IH; simpl; intros.
      all: try (econstructor; eauto; apply_transf_to_idx_preserve_ty''_IH; apply tenv_wf_step; eauto with fiat2_hints).
      4: repeat apply tenv_wf_step; eauto with fiat2_hints.
      1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          1:{ repeat rewrite_l_to_r; do_injection. eapply type_of_strengthen.
              1: apply from_idx_preserve_ty with (Gstore:=map.put map.empty x (idx_ty t)) (Genv:=map.empty);
              simpl; auto.
              1: apply_tenv_wf; auto.
              1: rewrite get_free_vars_empty.
              all: eauto using idx_ty_wf, incl_nil_l, tenv_wf_empty with fiat2_hints.
              1: constructor; rewrite_map_get_put_goal; auto.
              1: apply map_incl_step; auto using string_dec.
              1,2: apply map_incl_empty. }
          1: constructor; rewrite_map_get_put_goal. }
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
      1:{ constructor; auto. lazymatch goal with H: Forall _ _ |- _ => induction H end.
          all: simpl; auto.
          case_match; simpl in *; constructor; intuition auto.
          invert_Forall; apply IHForall; auto. }
    Qed.

    Ltac use_transf_to_idx_preserve_ty'_IH :=
      lazymatch goal with
        IH: context[well_typed _ _ (transf_to_idx' _ _ ?c)] |- well_typed _ _ (transf_to_idx' _ _ ?c) =>
          eapply IH; try reflexivity
      end.

    Lemma transf_to_idx_preserve_ty' : forall tbl_ty tbl c (Gstore Gstore' Genv :tenv) free_vars,
        tenv_wf Gstore -> tenv_wf Genv ->
        map.get Gstore tbl = Some tbl_ty ->
        is_tbl_ty tbl_ty = true ->
        well_typed Gstore Genv c ->
        incl (get_free_vars Genv) free_vars ->
        Gstore' = map.put Gstore tbl (idx_ty tbl_ty) ->
        well_typed Gstore' Genv (transf_to_idx' free_vars tbl c).
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
              eapply substitute_preserve_ty with (Genv0:=map.put map.empty hole tbl_ty); auto.
              1,2: apply tenv_wf_step; auto using tenv_wf_empty.
              1: apply idx_ty_wf; auto.
              1,2: repeat apply_tenv_wf; auto.
              1:{ eapply type_of_strengthen; eauto using to_idx_ty, map_incl_refl.
                  apply map_incl_empty. }
              1:{ unfold sub_wf. simpl; intros.
                  case_match_string_eqb; rewrite_l_to_r; repeat do_injection;
                    [ auto using transf_to_idx_preserve_ty''
                    | rewrite map.get_empty in *; discriminate ]. } }
          1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
              rewrite_map_get_put_goal; eauto. } }
      1: constructor; eauto using transf_to_idx_preserve_ty''.
      1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
          use_transf_to_idx_preserve_ty'_IH; eauto with fiat2_hints.
          eauto using incl_tran, incl_cons_step, get_free_vars_put. }
    Qed.

    Lemma transf_to_idx_preserve_ty : forall tbl_ty tbl e c free_vars Gstore Genv,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e tbl_ty ->
        well_typed (map.put Gstore tbl tbl_ty) Genv c ->
        is_tbl_ty tbl_ty = true ->
        incl (get_free_vars Genv) free_vars ->
        well_typed Gstore Genv (transf_to_idx free_vars (CLetMut e tbl c)).
    Proof.
      simpl; intros. subst. econstructor.
      1:{ eapply substitute_preserve_ty with (Genv0:=map.put map.empty hole tbl_ty); eauto using tenv_wf_empty, incl_refl with fiat2_hints.
          1: eapply type_of_strengthen; [ apply to_idx_ty; eauto | apply map_incl_empty | apply map_incl_refl ].
          1: eapply type_of__type_wf; [ | | eauto ]; auto.
          1:{ unfold sub_wf. simpl; intros.
              destruct_get_put_strings;
                [ do_injection; rewrite eqb_refl; auto
                | rewrite map.get_empty in *; discriminate ]. } }
      1:{ erewrite <- Properties.map.put_put_same.
          eapply transf_to_idx_preserve_ty'; try reflexivity; eauto using incl_refl with fiat2_hints.
          rewrite_map_get_put_goal; auto. }
    Qed.


    Definition index_wf_with_globals := value_wf_with_globals idx_wf.

    Lemma well_typed__index_wf_nil : forall c Gstore Genv,
        tenv_wf Gstore -> tenv_wf Genv ->
        well_typed Gstore Genv c ->
        forall P,
          (forall x v, P x v <-> index_wf_with_globals nil x v) ->
          parameterized_wf Gstore Genv P c.
    Proof.
      induction 3; intros.
      all: try now (constructor; auto).
      1:{ econstructor; eauto. apply IHwell_typed; eauto with fiat2_hints. }
      1:{ econstructor; eauto. apply IHwell_typed; eauto with fiat2_hints.
          intros. split.
          1: constructor.
          1:{ unfold rm_from_pred. intros; right. rewrite H3. constructor. } }
      1:{ econstructor; eauto. intros. rewrite H3; constructor. }
      1:{ econstructor; eauto. apply IHwell_typed; eauto with fiat2_hints. }
    Qed.

    Lemma rm_from_index_wf__index_wf_nil : forall (tbl x : string) (v : value),
        rm_from_pred (index_wf_with_globals (tbl :: nil)) tbl x v <-> index_wf_with_globals nil x v.
    Proof.
      intros. split.
      1: constructor.
      1:{ intros. unfold rm_from_pred.
          destruct (String.eqb x tbl) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *;
            subst; intuition auto.
          right. constructor; auto. }
    Qed.

    Ltac apply_transf_to_idx'_index_wf_IH :=
      lazymatch goal with
        IH: context[parameterized_wf _ _ _ (transf_to_idx' _ _ ?c)] |- context[?c] =>
          apply IH
      end.

    Lemma transf_to_idx'_index_wf : forall tbl tbl_ty c free_vars Gstore Genv,
        tenv_wf Gstore -> tenv_wf Genv ->
        map.get Gstore tbl = Some tbl_ty ->
        is_tbl_ty tbl_ty = true ->
        well_typed Gstore Genv c ->
        incl (get_free_vars Genv) free_vars ->
        parameterized_wf (map.put Gstore tbl (idx_ty tbl_ty)) Genv (index_wf_with_globals (tbl :: nil)) (transf_to_idx' free_vars tbl c).
    Proof.
      unfold index_wf_with_globals; induction c; simpl in *; intros.
      all: invert_well_typed.
      all: unfold is_true in *; repeat rewrite Bool.andb_true_iff in *; intuition.
      1: constructor.
      1: constructor; apply_transf_to_idx'_index_wf_IH; auto.
      1:{ econstructor.
          2: apply_transf_to_idx'_index_wf_IH; eauto; intuition eauto with fiat2_hints.
          2: eauto using incl_tran, incl_cons_step, get_free_vars_put.
          apply transf_to_idx_preserve_ty''; auto; simpl; intuition. }
      1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          all: econstructor; [ apply transf_to_idx_preserve_ty''; eauto | ].
          1:{ rewrite Properties.map.put_put_same.
              apply well_typed__index_wf_nil; eauto with fiat2_hints.
              apply rm_from_index_wf__index_wf_nil. }
          1:{ rewrite Properties.map.put_put_diff; auto.
              eapply parameterized_wf_Proper; try reflexivity; auto.
              1:{ apply rm_not_in_globals.
                  intro contra. inversion contra; auto. }
              apply IHc; eauto with fiat2_hints.
              rewrite_map_get_put_goal. } }
      1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          1:{ econstructor.
              2: rewrite_map_get_put_goal; eauto.
              2:{ apply to_idx_preserve_ty; eauto using idx_ty_wf with fiat2_hints.
                  rewrite_l_to_r. do_injection.
                  apply transf_to_idx_preserve_ty''; auto. }
              intros. unfold index_wf_with_globals. constructor; auto. right.
              lazymatch goal with H: ?x = _, H': ?x = _ |- _ => rewrite H in H' end.
              do_injection; auto.
              eapply to_idx_satisfy_idx_wf; [ | | apply transf_to_idx_preserve_ty'' | .. ].
              7: eauto. all: eauto using idx_ty_wf with fiat2_hints. }
          1:{ econstructor.
              2: rewrite_map_get_put_goal; eauto.
              2: apply transf_to_idx_preserve_ty''; auto.
              intros. unfold index_wf_with_globals. constructor; auto. } }
      1:{ constructor; try apply_transf_to_idx'_index_wf_IH; intuition.
          apply transf_to_idx_preserve_ty''; auto. }
      1:{ econstructor; eauto.
          1: apply transf_to_idx_preserve_ty''; eauto.
          apply_transf_to_idx'_index_wf_IH; eauto with fiat2_hints.
          eauto using incl_tran, incl_cons_step, get_free_vars_put. }
    Qed.

    Definition gallina_to_idx (v : value) : value :=
      interp_expr map.empty (map.put map.empty hole v) to_idx.

    Lemma fiat2_gallina_to_idx : forall e Gstore Genv store env t free_vars,
        is_tbl_ty t = true ->
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e t ->
        locals_wf Gstore store -> locals_wf Genv env ->
        incl (get_free_vars Genv) free_vars ->
        interp_expr store env (substitute ((hole, e) :: nil) free_vars to_idx) =
          gallina_to_idx (interp_expr store env e).
    Proof.
      unfold gallina_to_idx. simpl; intros.
      erewrite substitute_preserve_sem with (Gstore:=Gstore) (Genv0:=map.put map.empty hole t); eauto.
      3: eapply type_of_strengthen.
      1: eapply interp_expr_strengthen.
      all: try apply to_idx_ty; eauto.
      all: try apply tenv_wf_step; eauto with fiat2_hints; try apply tenv_wf_empty.
      all: try apply locals_wf_step; auto; try apply locals_wf_empty.
      1: eapply type_sound; eauto.
      all: try apply map_incl_step; auto using string_dec;
        try apply map_incl_empty; try apply incl_refl.
      unfold sub_wf; intros; simpl.
      destruct (String.eqb x hole) eqn:E_x; rewrite ?eqb_eq, ?eqb_neq in *; subst.
      all: rewrite_map_get_put_hyp; try rewrite map.get_empty in *; congruence.
    Qed.

    Definition gallina_from_idx (v : value) : value :=
      interp_expr map.empty (map.put map.empty hole v) from_idx.

    Lemma fiat2_gallina_from_idx : forall e Gstore Genv store env t free_vars,
        type_wf t -> is_tbl_ty t = true ->
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e (idx_ty t) ->
        locals_wf Gstore store -> locals_wf Genv env ->
        incl (get_free_vars Genv) free_vars ->
        interp_expr store env (substitute ((hole, e) :: nil) free_vars from_idx) =
          gallina_from_idx (interp_expr store env e).
    Proof.
      unfold gallina_from_idx. simpl; intros.
      erewrite substitute_preserve_sem
        with (Gstore:=Gstore) (Genv0:=map.put map.empty hole (idx_ty t)); eauto.
      3: eapply type_of_strengthen.
      1: eapply interp_expr_strengthen.
      all: try apply from_idx_ty; eauto.
      all: try apply tenv_wf_step; eauto with fiat2_hints; try apply tenv_wf_empty.
      all: try apply locals_wf_step; auto; try apply locals_wf_empty.
      1: eapply type_sound; eauto.
      all: try apply map_incl_step; auto using string_dec;
        try apply map_incl_empty; try apply incl_refl.
      unfold sub_wf; intros; simpl.
      destruct (String.eqb x hole) eqn:E_x; rewrite ?eqb_eq, ?eqb_neq in *; subst.
      all: rewrite_map_get_put_hyp; try rewrite map.get_empty in *; congruence.
    Qed.

    Section WithRelMap.
      Context {rel_map : map.map string (value -> value -> Prop)} {rel_map_ok : map.ok rel_map }.

      Definition consistent_with_global_Renv (tbl : string) (istr : aenv) : rel_map :=
        map.put
          (consistent_Renv istr)
          tbl
          (fun v v' => exists u,
               consistent (get_collection_tag istr tbl) v u
               /\ v' = gallina_to_idx u).

      Lemma aenv_le__consistent_with_global_Renv_le : forall tbl istr istr',
          aenv_le istr istr' ->
          Renv_le (consistent_with_global_Renv tbl istr) (consistent_with_global_Renv tbl istr').
      Proof.
        unfold Renv_le, consistent_with_global_Renv; intros.
        destruct_get_put_strings.
        1:{ unfold R_le; intros.
            destruct v, v'; simpl in *; auto. destruct_exists.
            exists x0; intuition eauto using aenv_le__collection_tag_leb, consistent_step. }
        1:{ unfold aenv_le, R_le in *; intros. rewrite consistent_Renv_sound in *.
            specialize (H x). unfold aenv_le_at in *. repeat destruct_match_hyp; intuition auto.
            all: destruct v, v'; simpl in *; eauto using consistent_step. }
      Qed.

      Lemma consistent_Renv_put_global : forall istr tbl R,
          map.put (consistent_Renv istr) tbl R = map.put (consistent_with_global_Renv tbl istr) tbl R.
      Proof.
        unfold consistent_Renv, consistent_with_global_Renv; intros.
        rewrite Properties.map.put_put_same; reflexivity.
      Qed.

      Lemma consistent_with_global_Renv_remove_local : forall x tbl istr,
          x <> tbl ->
          Renv_le (map.update (consistent_with_global_Renv tbl istr) x None)
            (consistent_with_global_Renv tbl (map.update istr x None)).
      Proof.
        unfold Renv_le; intros. destruct_String_eqb x0 tbl.
        1:{ unfold consistent_with_global_Renv.
            rewrite Properties.map.get_update_diff; auto.
            rewrite !map.get_put_same. unfold R_le; intros.
            destruct v, v'; simpl in *; auto.
            destruct_exists. eexists; intuition eauto.
            unfold get_collection_tag in *.
            rewrite map.get_remove_diff in *; auto. }
        1:{ unfold consistent_with_global_Renv. rewrite update_put_diff; auto.
            rewrite !map.get_put_diff; auto.
            unfold consistent_Renv. rewrite mmap_update; simpl; auto.
            apply R_le_refl. }
      Qed.

      Lemma consistent_with_global_Renv_put_local : forall tbl x istr i,
          x <> tbl ->
          Renv_le (consistent_with_global_Renv tbl (map.put istr x i))
            (map.put (consistent_with_global_Renv tbl istr) x (consistent i)).
      Proof.
        unfold Renv_le; intros. destruct_String_eqb x0 tbl.
        1:{ unfold consistent_with_global_Renv.
            repeat rewrite_map_get_put_goal. unfold R_le; intros.
            destruct v, v'; simpl in *; auto.
            destruct_exists. eexists; intuition eauto.
            unfold get_collection_tag in *. rewrite_map_get_put_goal. }
        1:{ unfold consistent_with_global_Renv. rewrite_map_get_put_goal.
            rewrite Properties.map.put_put_diff; auto. rewrite_map_get_put_goal.
            rewrite consistent_Renv_put. apply R_le_refl. }
      Qed.

      Lemma consistent_with_global_Renv_put_local2 : forall tbl x istr i,
          x <> tbl ->
          Renv_le
            (map.put (consistent_with_global_Renv tbl istr) x (consistent i))
            (consistent_with_global_Renv tbl (map.put istr x i)).
      Proof.
        unfold Renv_le; intros. destruct_String_eqb x0 tbl.
        1:{ unfold consistent_with_global_Renv.
            repeat rewrite_map_get_put_goal. unfold R_le; intros.
            destruct v, v'; simpl in *; auto.
            destruct_exists. eexists; intuition eauto.
            unfold get_collection_tag in *. rewrite_map_get_put_hyp. }
        1:{ unfold consistent_with_global_Renv.
            rewrite Properties.map.put_put_diff; auto.
            rewrite_map_get_put_goal.
            rewrite map.get_put_diff with (k':=tbl); auto.
            rewrite consistent_Renv_put. apply R_le_refl. }
      Qed.

      Ltac invert_tag_of :=
        lazymatch goal with H: tag_of _ _ _ _ |- _ => inversion H; subst end.

      Ltac invert_well_tagged :=
        lazymatch goal with
          H: well_tagged _ _ _ _ _ |- _ => inversion H; subst end.

      Ltac apply_locals_related :=
        lazymatch goal with
          H: locals_related _ ?l _ |- context[map.get ?l ?x] => specialize (H x) end.

      Ltac apply_type_sound_consistent_value e :=
        apply_type_sound2 e;
        invert_type_of_value;
        lazymatch goal with
          H: consistent _ (interp_expr _ _ e) _ |- _ =>
            let H' := fresh in
            eapply consistent__type_of_value in H as H'; eauto end;
        repeat rewrite_expr_value;
        invert_type_of_value; repeat rewrite_expr_value.

      Ltac use_transf_to_idx_preserve_sem''_IH :=
        lazymatch goal with
          IH: context[consistent _ (interp_expr _ _ ?e)],
            H: tag_of _ _ ?e _ |- context[interp_expr _ _ ?e] =>
            eapply IH in H end;
        [ | | | | | | | | | eauto | eauto ]; auto.

      Ltac use_transf_to_idx_preserve_sem''_IH_on e :=
        lazymatch goal with
          IH: context[consistent _ (interp_expr _ _ e)],
            H: tag_of _ _ e _ |- _ =>
            eapply IH in H end;
        [ | | | | | | | | | eauto | eauto ]; auto.

      Lemma transf_to_idx_preserve_sem'' : forall tbl tbl_ty Gstore Genv e t,
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv e t ->
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          forall store store' env env' istr ienv i,
            collection_tag_leb (get_collection_tag istr tbl) to_from_con = true ->
            tag_of istr ienv e i ->
            locals_wf Gstore store -> locals_wf Genv env ->
            locals_wf (map.put Gstore tbl (idx_ty tbl_ty)) store' -> locals_wf Genv env' ->
            locals_related (consistent_with_global_Renv tbl istr) store store' ->
            locals_related (consistent_Renv ienv) env env' ->
            consistent i (interp_expr store env e) (interp_expr store' env' (fold_expr (idx_read_to_list_read tbl) e)).
      Proof.
        intros * ? ? H. induction H using @type_of_IH; intros; simpl.
        all: invert_tag_of.
        all: try now (repeat use_transf_to_idx_preserve_sem''_IH;
                      rewrite consistent_LikeList_eq in *; repeat rewrite_r_to_l;
                      eapply consistent_step;
                      [ apply consistent_LikeList_eq; auto
                      |  destruct i; auto ]).
        1:{ eapply consistent_step; eauto. unfold get_local.
            apply_locals_related.
            rewrite consistent_Renv_sound in *. rewrite_l_to_r.
            apply_locals_wf env. apply_locals_wf env'. repeat destruct_match_hyp; intuition auto. }
        1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
            1:{ erewrite fiat2_gallina_from_idx with (Genv:=map.empty); simpl.
                7: eauto. all: eauto using idx_ty_wf, tenv_wf_empty, locals_wf_empty with fiat2_hints.
                2: constructor; rewrite_map_get_put_goal; auto.
                2: rewrite get_free_vars_empty; auto; apply incl_refl.
                unfold get_local. apply_locals_related.
                apply_locals_wf store.
                assert(map.get (map.put Gstore x (idx_ty tbl_ty)) x = Some (idx_ty tbl_ty)).
                { rewrite_map_get_put_goal; auto. }
                apply_locals_wf store'.
                unfold consistent_with_global_Renv in *. repeat rewrite_map_get_put_hyp.
                repeat destruct_match_hyp; simpl in *; intuition auto.
                destruct_exists. unfold get_collection_tag in *; rewrite_l_to_r.
                intuition auto; subst. unfold gallina_from_idx, gallina_to_idx.
                eapply consistent_step; eauto using consistent__type_of_value.
                eapply consistent_tran.
                2: eapply to_from_consistent; eauto using consistent__type_of_value.
                1,2: eauto using collection_tag_leb_refl.
                1: rewrite_l_to_r; auto. }
            1:{ simpl. unfold get_local. apply_locals_related.
                unfold consistent_with_global_Renv in *. rewrite_map_get_put_hyp.
                rewrite consistent_Renv_sound in *. rewrite_l_to_r.
                lazymatch goal with H: map.get _ tbl = _ |- _ => clear H end.
                apply_locals_wf store.
                assert(map.get (map.put Gstore tbl (idx_ty tbl_ty)) x = Some t).
                { rewrite_map_get_put_goal; auto. }
                apply_locals_wf store'. repeat case_match; intuition auto.
                simpl in *. eapply consistent_step; eauto. } }
        1: apply consistent_refl.
        1:{ destruct o; simpl in * |-; use_transf_to_idx_preserve_sem''_IH.
            all: try (rewrite consistent_LikeList_eq in *; repeat rewrite_l_to_r;
                      eapply consistent_step;
                      [ rewrite consistent_LikeList_eq; eauto
                      | destruct i; auto ]).
            eapply consistent_step;
              [ rewrite consistent_LikeList_eq | destruct i; auto ].
            lazymatch goal with H: type_of_unop _ _ _ |- _ => inversion H; subst end.
            simpl in *. repeat case_match; try congruence; intuition auto.
            erewrite Permutation_length; eauto. }
        1:{ destruct o; simpl in * |-; repeat use_transf_to_idx_preserve_sem''_IH.
            all: lazymatch goal with
                   H: (_, _) = (_, _) |- _ => inversion H; subst end;
              repeat rewrite consistent_LikeList_eq in *; repeat rewrite_r_to_l;
              try (eapply consistent_step;
                   [ rewrite consistent_LikeList_eq; eauto
                   | destruct i; auto ]).
            all: lazymatch goal with H: type_of_binop _ _ _ _ |- _ => inversion H; subst end.
            all: simpl in *.
            1:{ apply_type_sound_consistent_value e1.
                apply_type_sound_consistent_value e2.
                apply app_preserve_consistent; auto. }
            1:{ apply_type_sound_consistent_value e1.
                apply_type_sound2 e2. invert_type_of_value.
                apply concat_repeat_preserve_consistent; auto. }
            1:{ apply_type_sound_consistent_value e2.
                apply cons_preserve_consistent; auto. } }
        1:{ repeat use_transf_to_idx_preserve_sem''_IH.
            rewrite consistent_LikeList_eq in *; repeat rewrite_r_to_l.
            apply_type_sound2 e1. invert_type_of_value. case_match; auto. }
        1:{ use_transf_to_idx_preserve_sem''_IH_on e1.
            apply_type_sound2 e1.
            lazymatch goal with
              H: consistent _ ?v ?v', H': type_of_value ?v _ |- _ =>
                let H'' := fresh in
                eapply consistent__type_of_value in H' as H''; eauto end.
            use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints.
            rewrite consistent_Renv_put; apply locals_related_step; auto. }
        1:{ use_transf_to_idx_preserve_sem''_IH_on e1.
            apply_type_sound_consistent_value e1.
            apply flat_map_preserve_consistent; auto; intros. apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH; [ | eauto with fiat2_hints | .. ].
            4: rewrite consistent_Renv_put; apply locals_related_step; [ eauto | ].
            1: apply_type_sound_consistent_value e2; eauto with fiat2_hints.
            1,2: eapply type_sound; eauto with fiat2_hints.
            1,2: apply locals_wf_step; auto.
            1: apply consistent_refl. }
        1:{ use_transf_to_idx_preserve_sem''_IH_on e1.
            lazymatch goal with
              H: consistent LikeList _ _ |- _ =>
                rewrite consistent_LikeList_eq in H; rewrite <- H
            end.
            apply_type_sound2 e1. invert_type_of_value. rewrite_expr_value.
            use_transf_to_idx_preserve_sem''_IH_on e2. apply_type_sound2 e2.
            eapply consistent_step; eauto.
            repeat lazymatch goal with
                     H: VList _ = _ |- _ => clear H end.
            induction l; simpl.
            1: eapply consistent_step; eauto.
            1:{ invert_Forall.
                use_transf_to_idx_preserve_sem''_IH_on e3; eauto.
                1: repeat apply tenv_wf_step; eauto with fiat2_hints.
                1,2: repeat apply locals_wf_step; auto;
                eapply fold_right__type_of_value; eauto using consistent__type_of_value; intros.
                1:{ eapply type_sound; eauto with fiat2_hints.
                    repeat apply tenv_wf_step; eauto with fiat2_hints. }
                1:{ use_transf_to_idx_preserve_sem''_IH_on e3; eauto.
                    1: eapply consistent__type_of_value; eauto.
                    5: repeat rewrite consistent_Renv_put; repeat apply locals_related_step;
                    eauto using consistent_refl.
                    1: apply_type_sound2 e3.
                    all: repeat apply tenv_wf_step; eauto with fiat2_hints. }
                1:{ repeat rewrite consistent_Renv_put.
                    repeat apply locals_related_step; auto using consistent_refl.
                    apply IHl; auto. constructor; auto. } } }
        1:{ lazymatch goal with
            H1: map fst _ = _, H2: Forall2 (type_of _ _) _ _, H3: Permutation _ _,
                  H4: NoDup _, H5: Sorted.StronglySorted _ _ |- _ =>
              clear H1 H2 H3 H4 H5 end.
            apply consistent_step with (i2:=LikeList).
            2: destruct i; auto.
            rewrite consistent_LikeList_eq. do 2 f_equal.
            generalize dependent tl. induction l; simpl; auto using consistent_refl; intros.
            invert_Forall; invert_Forall2; repeat case_match; f_equal; simpl in *.
            1:{ f_equal. use_transf_to_idx_preserve_sem''_IH. }
            1:{ destruct tl; simpl in *; try congruence; invert_cons.
                lazymatch goal with
                  H: Forall _ l |- _ => eapply IHl in H; eauto end.
                constructor; auto. } }
        1:{ eapply consistent_step.
            1: apply consistent_LikeList_eq; auto.
            2: destruct i; auto.
            do 3 f_equal. induction l; simpl; auto.
            case_match; repeat invert_Forall; simpl in *.
            f_equal.
            2: apply IHl; auto; constructor; auto.
            intuition auto.
            repeat (lazymatch goal with
                    | IH:context [ consistent _ (interp_expr _ _ ?e) ], H:tag_of _ _ ?e _ |- _ => eapply IH in H
                    end; [ | | | | | | eauto | eauto ]; auto).
            rewrite consistent_LikeList_eq in *. congruence. }
        1:{ use_transf_to_idx_preserve_sem''_IH;
            rewrite consistent_LikeList_eq in *; repeat rewrite_r_to_l.
            apply_type_sound2 e. invert_type_of_value.
            all: use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints.
            rewrite consistent_Renv_put. apply locals_related_step; auto using consistent_refl. }
        1:{ use_transf_to_idx_preserve_sem''_IH;
            rewrite consistent_LikeList_eq in *; repeat rewrite_r_to_l.
            apply_type_sound2 d. invert_type_of_value.
            eapply consistent_step;
              [ apply consistent_LikeList_eq; auto
              |  destruct i; auto ].
            use_transf_to_idx_preserve_sem''_IH_on e0.
            apply_type_sound2 e0.
            rewrite consistent_LikeList_eq in *. repeat rewrite_r_to_l.
            eapply In_fold_right_ext with (P:=fun v => type_of_value v t); intros.
            2:{ apply_Forall_In. split.
                1:{ use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints.
                    1,2: repeat apply locals_wf_step; intuition auto.
                    1:{ repeat rewrite consistent_Renv_put.
                        repeat apply locals_related_step; auto using consistent_refl. } }
                eapply type_sound; eauto with fiat2_hints.
                repeat apply locals_wf_step; intuition auto. }
            eapply type_sound; eauto. }
        1:{ destruct i; unfold glb in *; simpl in *.
            all: use_transf_to_idx_preserve_sem''_IH;
              apply_type_sound_consistent_value l; simpl in *.
            1: eapply Permutation_dedup_Permuted; eauto using Permuted_value_sort.
            1: eauto using perm_trans, Permuted_value_sort, Permutation_sym.
            1:{ f_equal. apply Permutation_SSorted_eq; auto using StronglySorted_value_sort.
                eauto using perm_trans, Permuted_value_sort, Permutation_sym. } }
        1:{ use_transf_to_idx_preserve_sem''_IH.
            apply_type_sound_consistent_value e.
            apply filter_preserve_consistent; auto.
            intros. apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH.
            1:{ rewrite consistent_LikeList_eq in *;
                lazymatch goal with
                  H: interp_expr _ _ p = _ |- _ => rewrite <- H
                end. eauto. }
            all: eauto with fiat2_hints.
            rewrite consistent_Renv_put. apply locals_related_step; auto using consistent_refl. }
        1:{ use_transf_to_idx_preserve_sem''_IH. apply_type_sound_consistent_value e1.
            use_transf_to_idx_preserve_sem''_IH. apply_type_sound_consistent_value e2.
            apply flat_map_preserve_consistent; auto; intros.
            apply map_preserve_consistent; auto; intros.
            2:{ use_transf_to_idx_preserve_sem''_IH.
                1: rewrite consistent_LikeList_eq in *; eauto.
                1: repeat apply tenv_wf_step; eauto with fiat2_hints.
                1,2: rewrite filter_In in *; intuition auto;
                repeat apply_Forall_In; repeat apply locals_wf_step; auto.
                1:{ repeat rewrite consistent_Renv_put.
                    repeat apply locals_related_step; auto using consistent_refl. } }
            apply filter_preserve_consistent; auto; intros.
            use_transf_to_idx_preserve_sem''_IH.
            1: rewrite consistent_LikeList_eq in *;
            lazymatch goal with
              H: interp_expr _ _ p = _ |- _ => rewrite <- H
            end; eauto.
            all: [> repeat apply tenv_wf_step; eauto with fiat2_hints
                 | repeat apply_Forall_In; repeat apply locals_wf_step; auto
                 | repeat apply_Forall_In; repeat apply locals_wf_step; auto
                 | repeat rewrite consistent_Renv_put;
                   repeat apply locals_related_step; auto using consistent_refl ]. }
        1:{ use_transf_to_idx_preserve_sem''_IH. apply_type_sound_consistent_value e.
            apply map_preserve_consistent; auto; intros.
            use_transf_to_idx_preserve_sem''_IH;
              [ rewrite consistent_LikeList_eq in *; eauto | .. ].
            all: [> repeat apply tenv_wf_step; eauto with fiat2_hints
                 | repeat apply_Forall_In; repeat apply locals_wf_step; auto
                 | repeat apply_Forall_In; repeat apply locals_wf_step; auto
                 | repeat rewrite consistent_Renv_put;
                   repeat apply locals_related_step; auto using consistent_refl ]. }
      Qed.

      Ltac use_transf_to_idx_preserve_sem'' :=
        eapply transf_to_idx_preserve_sem''; [ | | eauto | | | | eauto | .. ]; eauto;
        eapply collection_tag_leb_tran;
        eauto using aenv_le__collection_tag_leb, aenv_le__istr_inv.

      Ltac use_transf_to_idx_preserve_sem'_IH :=
        lazymatch goal with
          IH: context[locals_related _ (interp_command _ _ ?c) _] |-
            locals_related _ (interp_command _ _ ?c) _ =>
            eapply IH
        end.

      Lemma transf_to_idx_preserve_sem' : forall tbl tbl_ty c (Gstore Genv : tenv) free_vars,
          tenv_wf Gstore -> tenv_wf Genv ->
          well_typed Gstore Genv c ->
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          incl (get_free_vars Genv) free_vars ->
          forall (istr ienv inv istr_expect : aenv) (store store' env env': locals),
            collection_tag_leb (get_collection_tag inv tbl) to_from_con = true ->
            well_tagged istr ienv inv c istr_expect ->
            locals_wf Gstore store -> locals_wf Genv env ->
            locals_wf (map.put Gstore tbl (idx_ty tbl_ty)) store' -> locals_wf Genv env' ->
            locals_related (consistent_with_global_Renv tbl istr) store store' ->
            locals_related (consistent_Renv ienv) env env' ->
            locals_related (consistent_with_global_Renv tbl istr_expect) (interp_command store env c) (interp_command store' env' (transf_to_idx' free_vars tbl c)).
      Proof.
        intros * ? ? H. revert free_vars. induction H; simpl; intros.
        all: invert_well_tagged.
        1:{ eapply locals_related__Renv_le; eauto.
            apply aenv_le__consistent_with_global_Renv_le; auto. }
        1:{ use_transf_to_idx_preserve_sem'_IH; eauto.
            all: eapply command_type_sound; eauto.
            1: eapply transf_to_idx_preserve_ty'; try reflexivity; eauto with fiat2_hints.
            apply tenv_wf_step; auto. apply idx_ty_wf; auto. apply_tenv_wf; auto. }
        1:{ use_transf_to_idx_preserve_sem'_IH; eauto with fiat2_hints.
            1: eauto using incl_tran, incl_cons_step, get_free_vars_put.
            1:{ apply locals_wf_step; auto.
                eapply type_sound; [ | | eauto | eauto | ];
                  eauto using idx_ty_wf with fiat2_hints.
                apply transf_to_idx_preserve_ty''; auto. }
            rewrite consistent_Renv_put. apply locals_related_step; auto.
            use_transf_to_idx_preserve_sem''. }
        1:{ case_match_string_eqb.
            1:{ unfold consistent_with_global_Renv.
                erewrite put_consistent_Renv_put_same.
                apply locals_related_lifted_step.
                1:{ eapply locals_related__Renv_le.
                    1: apply Renv_le_refl.
                    eapply well_tagged_sound with (istr:=map.put istr tbl i); [ | | eauto | .. ]; eauto with fiat2_hints.
                    1:{ erewrite <- Properties.map.put_put_same. apply locals_wf_step; eauto.
                        eapply consistent__type_of_value;
                          [ eapply transf_to_idx_preserve_sem'' with (env:=env) | ];
                          [ | | eauto | | | | eauto | .. ]; eauto; [ | eapply type_sound; eauto ].
                        lazymatch goal with
                        | H: well_tagged istr _ inv _ _ |- _ =>
                            let H' := fresh in
                            apply aenv_le__istr_inv in H as H';
                            eapply aenv_le__collection_tag_leb in H';
                            eapply collection_tag_leb_tran; eauto
                        end. }
                    rewrite consistent_Renv_put. rewrite consistent_Renv_put_global.
                    apply locals_related_step; auto.
                    use_transf_to_idx_preserve_sem''. }
                1:{ apply_locals_related. unfold consistent_with_global_Renv in H12.
                    rewrite_map_get_put_hyp. apply_locals_wf store.
                    assert(map.get (map.put Gstore tbl (idx_ty tbl_ty)) tbl = Some (idx_ty tbl_ty)).
                    { rewrite_map_get_put_goal; auto. }
                    apply_locals_wf store'.
                    repeat destruct_match_hyp; intuition auto. simpl in *. destruct_exists.
                    eexists; intuition eauto.
                    lazymatch goal with H: aenv_le_at _ _ _ |- _ => apply aenv_le_at__collection_tag_leb in H end.
                    eapply consistent_step; eauto. } }
            1:{ apply locals_related_lifted_step2.
                1:{ eapply locals_related__Renv_le; eauto using consistent_with_global_Renv_put_local2.
                    use_transf_to_idx_preserve_sem'_IH; [ | | | | | | eauto | .. ]; eauto with fiat2_hints.
                    1: unfold get_collection_tag; rewrite_map_get_put_goal.
                    1:{ rewrite Properties.map.put_put_diff; auto. apply locals_wf_step; auto.
                        eapply type_sound. 1: apply transf_to_idx_preserve_ty''.
                        8: eauto. all: eauto using idx_ty_wf with fiat2_hints. }
                    eapply locals_related__Renv_le; [ apply consistent_with_global_Renv_put_local | ]; auto.
                    apply locals_related_step; auto.
                    use_transf_to_idx_preserve_sem''. }
                apply_locals_related. eapply lifted_related__Renv_le; eauto.
                unfold consistent_with_global_Renv; repeat rewrite_map_get_put_goal.
                apply aenv_le_at__R_le; auto. } }
        1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst; simpl.
            1:{ rewrite_l_to_r; do_injection. erewrite fiat2_gallina_to_idx.
                5: eapply transf_to_idx_preserve_ty''.
                9: eauto. all: eauto using idx_ty_wf with fiat2_hints.
                eapply Renv_le_except__locals_related; eauto.
                1:{ intros. unfold consistent_with_global_Renv; repeat rewrite_map_get_put_goal.
                    lazymatch goal with
                      H: aenv_le ?istr _ |- context[map.get (consistent_Renv ?istr) ?y] => specialize (H y) end.
                    unfold aenv_le_at in *. rewrite_map_get_put_hyp.
                    repeat rewrite consistent_Renv_sound.
                    repeat case_match; intuition auto using R_le_refl, collection_tag_leb__R_le.
                    unfold R_le, lifted_related; intros. repeat case_match; auto. }
                unfold consistent_with_global_Renv; repeat rewrite_map_get_put_goal; simpl.
                eexists; intuition eauto. use_transf_to_idx_preserve_sem''. }
            1:{ eapply locals_related__Renv_le.
                2:{ apply locals_related_step; eauto. use_transf_to_idx_preserve_sem''. }
                eapply Renv_le_tran.
                2: apply consistent_with_global_Renv_put_local; auto.
                apply aenv_le__consistent_with_global_Renv_le.
                unfold aenv_le, aenv_le_at; intro y. destruct_get_put_strings.
                1:{ unfold get_collection_tag; case_match; auto.
                    destruct c; auto. }
                1:{ lazymatch goal with
                    H: aenv_le ?istr _ |- context[map.get ?istr ?y] => specialize (H y) end.
                    unfold aenv_le_at in *. rewrite_map_get_put_hyp. } } }
        1:{ lazymatch goal with H: tag_of _ _ _ _ |- _ => eapply transf_to_idx_preserve_sem'' in H end.
            10-13: eauto. all: eauto.
            1: rewrite consistent_LikeList_eq in *; repeat rewrite_r_to_l;
            apply_type_sound2 e; invert_type_of_value;
            case_match; use_transf_to_idx_preserve_sem'_IH; eauto.
            eapply collection_tag_leb_tran;
              eauto using aenv_le__collection_tag_leb, aenv_le__istr_inv. }
        1:{ lazymatch goal with
              H: tag_of _ _ _ _ |- _ =>
                let H' := fresh in
                eapply transf_to_idx_preserve_sem'' in H as H' end.
            1: rewrite consistent_LikeList_eq in H14.
            10-13: eauto. all: eauto.
            2: eapply collection_tag_leb_tran;
            eauto using aenv_le__collection_tag_leb, aenv_le__istr_inv.
            rewrite <- H14. apply_type_sound2 e. invert_type_of_value.
            eapply locals_related__Renv_le; eauto using aenv_le__consistent_with_global_Renv_le.
            lazymatch goal with H: VList _ = _, H1: interp_expr _ _ _ = interp_expr _ _ _ |- _ => clear H H1 end.
            destruct l; simpl.
            1: eapply locals_related__Renv_le; eauto using aenv_le__consistent_with_global_Renv_le.
            eapply locals_related__Renv_le in H12; [ | apply aenv_le__consistent_with_global_Renv_le; eauto ].
            generalize dependent v; generalize dependent store'; generalize dependent store.
            induction l; simpl; intros;  invert_Forall.
            1:{ use_transf_to_idx_preserve_sem'_IH; [ | | | | | | eauto | .. ]; eauto with fiat2_hints.
                1: eauto using incl_tran, incl_cons_step, get_free_vars_put.
                rewrite consistent_Renv_put.
                1: apply locals_related_step; auto using consistent_refl. }
            1:{ apply IHl; intuition auto.
                1: eapply command_type_sound; eauto with fiat2_hints.
                1:{ eapply type_sound; eauto. eapply command_type_sound; eauto with fiat2_hints. }
                1:{ eapply command_type_sound.
                    1: eapply transf_to_idx_preserve_ty'; [ | | | | eauto | .. ].
                    all: eauto using idx_ty_wf with fiat2_hints.
                    eauto using incl_tran, incl_cons_step, get_free_vars_put. }
                1:{ use_transf_to_idx_preserve_sem'_IH; [ | | | | | eauto | .. ]; eauto with fiat2_hints.
                    1: eauto using incl_tran, incl_cons_step, get_free_vars_put.
                    rewrite consistent_Renv_put. apply locals_related_step; auto using consistent_refl. } } }
      Qed.

      Definition make_LikeList_aenv (G : tenv) : aenv :=
        map.fold (fun m x _ => map.put m x LikeList) map.empty G.

      Lemma make_LikeList_aenv_sound : forall Gstore x t,
          map.get Gstore x = Some t -> map.get (make_LikeList_aenv Gstore) x = Some LikeList.
      Proof.
        unfold make_LikeList_aenv. intros. revert H. apply map.fold_spec; intros.
        1: rewrite map.get_empty in * |-; discriminate.
        destruct_get_put_strings; auto.
      Qed.

      Lemma make_LikeList_aenv__domain_incl : forall Gstore,
          domain_incl Gstore (make_LikeList_aenv Gstore).
      Proof.
        unfold domain_incl; intros. case_match; auto.
        erewrite make_LikeList_aenv_sound; eauto.
      Qed.

      Lemma consistent_tenv_LikeList : forall tbl Gstore store store' x t,
          locals_related (consistent_with_global_Renv tbl (map.put (make_LikeList_aenv Gstore) tbl LikeSet)) store store' ->
          x <> tbl -> map.get Gstore x = Some t -> map.get store x = map.get store' x.
      Proof.
        unfold locals_related, consistent_with_global_Renv; intros.
        specialize (H x). unfold lifted_related in *.
        repeat destruct_match_hyp; intuition auto; try congruence.
        all: rewrite_map_get_put_hyp; rewrite consistent_Renv_sound in *;
          rewrite_map_get_put_hyp.
        all: erewrite make_LikeList_aenv_sound in *; eauto.
        1: do_injection.
        all: congruence.
      Qed.

      Lemma put_to_idx__consistent_with_global : forall tbl istr e Gstore Genv store env t free_vars,
          is_tbl_ty t = true ->
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv e t ->
          incl (get_free_vars Genv) free_vars ->
          locals_wf Gstore store -> locals_wf Genv env ->
          locals_related (consistent_with_global_Renv tbl istr) (map.put store tbl (interp_expr store env e)) (map.put store tbl (interp_expr store env (substitute ((hole, e) :: nil) free_vars to_idx))).
      Proof.
        intros. unfold locals_related, consistent_with_global_Renv; intros.
        destruct_get_put_strings.
        1:{ eexists; intuition eauto using consistent_refl.
            eapply fiat2_gallina_to_idx; [ | | | eauto | .. ]; eauto using incl_refl. }
        1:{ unfold lifted_related. rewrite consistent_Renv_sound.
            repeat case_match; auto using consistent_refl. }
      Qed.

      Lemma transf_to_idx_preserve_sem : forall tbl_ty tbl e c (Gstore Genv : tenv) free_vars,
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv e tbl_ty ->
          well_typed (map.put Gstore tbl tbl_ty) Genv c ->
          can_transf_to_index to_from_con tbl_ty (make_LikeList_aenv Gstore) (CLetMut e tbl c) = true ->
          incl (get_free_vars Genv) free_vars ->
          forall (store env : locals),
            locals_wf Gstore store -> locals_wf Genv env ->
            interp_command store env (transf_to_idx free_vars (CLetMut e tbl c)) = interp_command store env (CLetMut e tbl c).
      Proof.
        simpl; intros. subst.
        rewrite Bool.andb_true_iff in *; intuition auto.
        unfold can_transf_to_index' in *. destruct_match_hyp.
        apply stores_eq_except__update_eq.
        intros. eapply command_tag_req_sound in E; eauto using domain_incl_step, make_LikeList_aenv__domain_incl.
        destruct (map.get Gstore x) eqn:E_x.
        1:{ symmetry. eapply consistent_tenv_LikeList; eauto.
            eapply transf_to_idx_preserve_sem' with (Gstore:=map.put Gstore tbl tbl_ty); eauto.
            all: try rewrite_map_get_put_goal; eauto with fiat2_hints.
            1: unfold get_collection_tag; repeat destruct_match_hyp; simpl; congruence.
            1:{ rewrite Properties.map.put_put_same. apply locals_wf_step; auto.
                eapply type_sound. 1: apply to_idx_preserve_ty; auto.
                1: eapply type_of__type_wf; [ | | eauto ]; auto.
                3: eauto. all: auto. }
            1:{ eapply put_to_idx__consistent_with_global. 4: eauto. all: auto. }
            1: apply locals_related_consistent_Renv_refl. }
        1:{ repeat erewrite command_preserve_untouched_store. 4: eauto.
            9: eapply transf_to_idx_preserve_ty' with (Gstore:=map.put Gstore tbl tbl_ty); eauto.
            all: repeat rewrite_map_get_put_goal; eauto with fiat2_hints.
            1:{ apply tenv_wf_step; eauto with fiat2_hints. apply idx_ty_wf; eauto with fiat2_hints. }
            1:{ rewrite Properties.map.put_put_same.
                apply locals_wf_step; auto. eapply type_sound. 1: apply to_idx_preserve_ty.
                1: eapply type_of__type_wf; [ | | eauto ]; auto.
                4: eauto. all: auto. } }
      Qed.


      Definition apply_after_letmut f (c : command) :=
        match c with
        | CLetMut e x c => CLetMut e x (f x c)
        | _ => c
        end.

      Definition apply_idx_related_transfs (f : string -> command -> command) (Gstore Genv : tenv) (c : command) :=
        match c with
        | CLetMut e tbl _ => match synthesize_expr Gstore Genv e with
                             | Success (t, _) => if can_transf_to_index to_from_con t (make_LikeList_aenv Gstore) c
                                                 then apply_after_letmut f (transf_to_idx (get_free_vars Genv) c)
                                                 else c
                             | _ => c
                             end
        | _ => c
        end.

      Notation expr_aug_transf_sound := (expr_aug_transf_sound (idx_wf:=idx_wf)).
      Notation aug_transf_sound := (aug_transf_sound (idx_wf:=idx_wf)).

      Lemma apply_idx_related_transfs_sound : forall f,
          aug_transf_sound f ->
          transf_sound (locals:=locals) (apply_idx_related_transfs f).
      Proof.
        unfold apply_idx_related_transfs, transf_sound; intros.
        repeat (case_match; auto). invert_well_typed.
        eapply synthesizable_ty_unique in E0 as H_syn_ty; eauto; subst.
        unfold can_transf_to_index in *; rewrite Bool.andb_true_iff in *; destruct_and.
        assert (H_ty : well_typed (map.put Gstore x (idx_ty t)) Genv (transf_to_idx' (get_free_vars Genv) x c0)).
        { erewrite <- Properties.map.put_put_same.
          eapply transf_to_idx_preserve_ty'; try reflexivity; eauto using incl_refl.
          2: rewrite_map_get_put_goal; eauto.
          1: eauto with fiat2_hints. }
        assert (H_wf : parameterized_wf (map.put Gstore x (idx_ty t)) Genv (index_wf_with_globals [x]) (transf_to_idx' (get_free_vars Genv) x c0)).
        { erewrite <- Properties.map.put_put_same.
          apply transf_to_idx'_index_wf; eauto using incl_refl with fiat2_hints.
          rewrite_map_get_put_goal; auto. }
        eapply H in H_wf. 5: eauto.
        all: eauto using idx_ty_wf with fiat2_hints.
        2: constructor;  try eapply map.get_put_same; auto.
        split.
        1:{ econstructor.
            1: apply to_idx_preserve_ty; eauto using incl_refl with fiat2_hints.
            apply H_wf; auto. }
        1:{ intros. unfold transf_to_idx, apply_after_letmut.
            cbn [interp_command]. eapply stores_eq_except__update_eq; intros.
            destruct (map.get Gstore x0) eqn:E.
            1:{ symmetry. eapply consistent_tenv_LikeList; eauto.
                intuition idtac. erewrite H13; auto.
                2:{ resolve_locals_wf. eapply type_sound.
                    1: apply to_idx_preserve_ty.
                all: resolve_locals_wf; eauto using incl_refl with fiat2_hints. }
                2:{ constructor; auto. destruct (String.eqb k x) eqn:E_kx;
                    rewrite ?eqb_eq, ?eqb_neq in *; subst; auto; right.
                    rewrite_map_get_put_hyp; do_injection.
                    eapply to_idx_satisfy_idx_wf; resolve_locals_wf; eauto using incl_refl. }
                unfold can_transf_to_index' in *; destruct_match_hyp.
                eapply command_tag_req_sound in E1;
                  eauto using domain_incl_step, make_LikeList_aenv__domain_incl.
                eapply transf_to_idx_preserve_sem' with (Gstore:=map.put Gstore x t); eauto.
                all: try rewrite_map_get_put_goal; eauto using incl_refl with fiat2_hints.
                1: unfold get_collection_tag; repeat destruct_match_hyp; simpl; congruence.
                1:{ rewrite Properties.map.put_put_same. apply locals_wf_step; auto.
                    eapply type_sound. 1: apply to_idx_preserve_ty; auto.
                    1: eapply type_of__type_wf; [ | | eauto ]; auto.
                    3: eauto. all: auto using incl_refl. }
                1:{ eapply put_to_idx__consistent_with_global. 4: eauto. all: auto using incl_refl. }
                1: eapply locals_related_consistent_Renv_refl. }
            1:{ repeat erewrite command_preserve_untouched_store. 4: eauto.
                9: apply H_wf.
                all: repeat rewrite_map_get_put_goal; eauto with fiat2_hints.
                1:{ apply tenv_wf_step; eauto with fiat2_hints. apply idx_ty_wf; eauto with fiat2_hints. }
                apply locals_wf_step; auto. eapply type_sound. 1: apply to_idx_preserve_ty.
                1: eapply type_of__type_wf; [ | | eauto ]; auto.
                4: eauto. all: auto using incl_refl. } }
      Qed.
    End WithRelMap.
  End WithIndex.
End WithMap.

#[export] Hint Extern 5 (transf_sound (apply_idx_related_transfs _)) => apply apply_idx_related_transfs_sound : transf_hints.
