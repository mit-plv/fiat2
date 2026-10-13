Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.Utils fiat2.Substitute
  fiat2.IndexTransf fiat2.Constraint fiat2.DictIndexImpl fiat2.FlatmapForms fiat2.TransfUtils
  fiat2.UniqueDictIndexImpl fiat2.UniqueIndexInstall fiat2.UniqueIndexGate
  fiat2.Surface.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List Permutation Sorted.

Import ListNotations.

(* Using the key-to-row index: a point query becomes one lookup.

   The rewrite replaces a scan that filters the table on the key attribute by
   a single lookup in the dictionary.  What makes it correct is uniqueness:
   without it the scan can return several rows and the dictionary only one, so
   the two differ.  With it the scan returns at most one row, and the
   dictionary holds exactly that one.

   Uniqueness is not something the index establishes -- to_idx builds the
   dictionary for any table, keeping one row per key and forgetting the rest.
   It is what the program maintains and what the installation carries, which
   is why this rule is proved against unique_aux_declared rather than against
   the index's own idx_wf. *)

Section WithWord.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).
  Context (attr : string).

  (* ------------------------------------------------------------------
     The scan and the lookup agree, as lists.
     ------------------------------------------------------------------ *)

  (* No row carries a key the table does not have. *)
  Lemma filter_key_eq_nil : forall (l : list value) (k : value),
      ~ In k (List.map (row_key attr) l) ->
      List.filter (fun r => value_eqb (row_key attr r) k) l = nil.
  Proof.
    intros l k; induction l as [| r l IH]; cbn [List.filter List.map In];
      auto; intros H_ni.
    destruct (value_eqb_dec (row_key attr r) k) as [ E | E ].
    1:{ exfalso. apply H_ni. left. exact E. }
    1:{ apply IH. intro H_in. apply H_ni. right. exact H_in. }
  Qed.

  (* And with the keys distinct, a row's key names that row and no other --
     so the scan the rewrite replaces returns exactly one row. *)
  Lemma filter_key_eq_singleton : forall (l : list value) (r : value),
      NoDup (List.map (row_key attr) l) ->
      In r l ->
      List.filter (fun r' => value_eqb (row_key attr r') (row_key attr r)) l = [r].
  Proof.
    intros l r; induction l as [| r0 l IH]; cbn [List.filter List.map In];
      intros H_nd H_in.
    1: contradiction.
    rewrite NoDup_cons_iff in H_nd; destruct H_nd as [ H_fresh H_nd ].
    destruct H_in as [ E_r | H_in ].
    1:{ subst r0. rewrite value_eqb_refl. f_equal.
        apply filter_key_eq_nil. exact H_fresh. }
    1:{ destruct (value_eqb_dec (row_key attr r0) (row_key attr r)) as [ E | E ].
        1:{ exfalso. apply H_fresh. rewrite E. apply in_map. exact H_in. }
        1: apply IH; assumption. }
  Qed.

  (* The two sides of the rewrite, as bags. *)
  Lemma filter_key_eq_lookup : forall (l : list value) (k : value),
      NoDup (List.map (row_key attr) l) ->
      list_to_bag (List.filter (fun r => value_eqb (row_key attr r) k) l)
      = match dict_lookup k (idx_entries attr l) with
        | Some r => bag_insert r nil
        | None => nil
        end.
  Proof.
    intros l k H_nd.
    destruct (dict_lookup k (idx_entries attr l)) as [ r | ] eqn:E_lk.
    1:{ destruct (idx_lookup_Some_inv attr l k r E_lk) as [ H_in E_key ].
        subst k. rewrite filter_key_eq_singleton by assumption. reflexivity. }
    1:{ rewrite filter_key_eq_nil; [ reflexivity | ].
        apply (proj1 (idx_lookup_None_iff attr l k)); exact E_lk. }
  Qed.
End WithWord.

Section WithIndexUse.
  (* the names the index's own fold binds *)
  Context (hole attr tup acc : string).
  Context (H_ne : tup <> acc).
  (* the two fields the installation pairs *)
  Context (id_tag aux_tag : string).
  Context (H_tags_diff : id_tag <> aux_tag).
  (* the binder the rewritten form introduces for the row it found *)
  Context (y : string).

  Notation uidx := (unique_dict_idx hole attr tup acc).

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (width:=width)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Section WithTable.
      Context (tbl : string).

      (* [row <- tbl[id_tag], check(row.attr == e'), ret row]  (as a bag)
         -->
         match lookup tbl[aux_tag] e' with none => emptybag | some y => {y} *)
      Definition unique_lookup_head (e : expr) : expr :=
        match e with
        | flatmap_filter_bag
            (EBagOf (EAccess (ELoc tbl0) id_tag0))
            x0 (EBinop OEq (EAccess (EVar x1) attr0) e') x2 _ _ =>
            if (all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x0, [x1; x2]); (id_tag, [id_tag0])] &&
                  negb (free_immut_in x0 e'))%bool
            then EOptMatch (EBinop OLookup (EAccess (ELoc tbl) aux_tag) e')
                   (EAtom (AEmptyBag None))
                   y (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar y))
            else e
        | _ => e
        end.

      Lemma unique_lookup_head_preserve_ty : forall tl t (Gstore : tenv),
          type_wf t -> @IndexInterface.is_tbl_ty uidx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (@IndexInterface.idx_ty uidx t) ->
          preserve_ty Gstore unique_lookup_head.
      Proof.
        unfold preserve_ty, IndexInterface.is_tbl_ty, IndexInterface.idx_ty,
          unique_dict_idx, UniqueDictIndexImpl.is_tbl_ty,
          UniqueDictIndexImpl.idx_ty in *.
        intros.
        repeat destruct_match_hyp; try congruence.
        repeat destruct_subexpr. simpl.
        case_match; auto. repeat rewrite Bool.andb_true_r in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        rewrite Bool.negb_true_iff, eqb_eq in *; subst.
        repeat invert_type_of_clear. repeat invert_type_of_op_clear.
        repeat rewrite_map_get_put_hyp.
        repeat (clear_refl; repeat do_injection2).
        repeat (rewrite_l_to_r; do_injection2).
        repeat (econstructor; eauto).
        1:{ unfold get_attr_type.
            lazymatch goal with H: ?x = _ |- context[?x] => rewrite H end.
            eapply not_free_immut_put_ty; eauto. }
        1-6: repeat invert_type_wf; auto.
        1: rewrite map.get_put_same; trivial.
      Qed.

      (* The scan and the lookup agree.  The store hypothesis is the strong
         invariant: the record's index field is the dictionary to_idx builds
         from its table field, and the table's keys are distinct.  Without the
         second the equation is false -- the scan would return every row
         carrying the key and the dictionary only one. *)
      Lemma unique_lookup_head_preserve_sem :
        forall tl t (Gstore : tenv) (store : locals),
          type_wf t -> @IndexInterface.is_tbl_ty uidx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (@IndexInterface.idx_ty uidx t) ->
          match map.get store tbl with
          | Some v => unique_aux_wf hole attr tup acc id_tag aux_tag v
          | _ => False
          end ->
          preserve_sem Gstore store unique_lookup_head.
      Proof.
        unfold preserve_sem, unique_aux_wf, UniqueDictIndexImpl.idx_wf_unique,
          UniqueDictIndexImpl.idx_wf, UniqueDictIndexImpl.keys_distinct,
          IndexInterface.is_tbl_ty, IndexInterface.idx_ty, unique_dict_idx,
          UniqueDictIndexImpl.is_tbl_ty, UniqueDictIndexImpl.idx_ty in *.
        intros.
        repeat (destruct_match_hyp; try discriminate; intuition idtac; []).
        rewrite fiat2_gallina_to_idx in * by assumption.
        repeat destruct_subexpr. unfold unique_lookup_head.
        cbv beta iota; case_match; auto.
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        rewrite Bool.negb_true_iff, eqb_eq in *; subst. repeat clear_refl.
        rewrite interp_flatmap_filter_bag.
        cbn [interp_expr interp_binop interp_atom].
        unfold get_local, record_proj.
        repeat rewrite_l_to_r.
        rewrite list_to_bag_filter_list_to_bag.
        erewrite In_filter_ext with
          (g := fun v => value_eqb (row_key attr v) (interp_expr store env e2_1_2)).
        2:{ intros v H_in. rewrite map.get_put_same. f_equal.
            symmetry; apply not_free_immut_put_sem; assumption. }
        rewrite filter_key_eq_lookup by assumption.
        destruct (dict_lookup (interp_expr store env e2_1_2) (idx_entries attr l0));
          [ rewrite map.get_put_same | ]; reflexivity.
      Qed.

      (* The row type a declared key carries is a typing annotation, not part
         of what the key means: it occurs in unique_constr only inside the
         empty-list atoms the counting expression builds, and interp_atom
         ignores an annotation.  This is what lets the rule read the key off
         the invariant without first having to know that the row type the
         declarations were written against is the one the store's table
         actually has. *)
      Lemma unique_constr_holds_row_ty_irrel : forall rty1 rty2 (v : value),
          constr_holds (locals:=locals) (unique_constr attr rty1) v ->
          constr_holds (locals:=locals) (unique_constr attr rty2) v.
      Proof.
        unfold constr_holds, constr_expr, unique_constr; cbn [c_row c_body].
        intros rty1 rty2 v H. rewrite <- H.
        cbn [interp_expr interp_atom]. reflexivity.
      Qed.
    End WithTable.
    (* aux_ty_access_id's companion.  IndexTransf proves only the id side,
       since the installation itself never reads the index field by name. *)
    Lemma aux_ty_access_aux : forall tbl_ty,
        access_record
          (record_sort [(id_tag, tbl_ty); (aux_tag, @IndexInterface.idx_ty uidx tbl_ty)])
          aux_tag
        = Success (@IndexInterface.idx_ty uidx tbl_ty).
    Proof.
      intros. apply NoDup_In_access_record.
      1: NoDup_map_record_sort.
      eapply Permutation_in; [ apply Permuted_record_sort | ]; cbn; auto.
    Qed.


    (* A declared key is one of the declared constraints, so the conjunction
       the installation carries yields it.  Stated at an arbitrary row type,
       unlike UniqueIndexGate's version, because here the row type the
       declarations mention and the one the store's table has are not yet
       known to agree -- and by unique_constr_holds_row_ty_irrel they need not. *)
    Lemma declares_unique__constr_holds : forall row_ty ds (v : value),
        declares_unique attr ds = true ->
        declared_holds (locals := locals) row_ty ds v ->
        constr_holds (locals := locals) (unique_constr attr row_ty) v.
    Proof.
      unfold declares_unique, declared_holds, constrs_hold, constrs_of_decls.
      intros * H_ex H_all.
      apply existsb_exists in H_ex as [ d [ H_in H_d ] ].
      destruct d; cbn [decl_is_unique] in H_d; try discriminate.
      rewrite String.eqb_eq in H_d; subst.
      rewrite Forall_forall in H_all. apply H_all.
      apply in_map_iff. exists (DUnique attr); split; [ reflexivity | assumption ].
    Qed.

    (* What the rule needs, from what the installation delivers. *)
    Lemma unique_aux_declared__unique_aux_wf : forall row_ty ds rt kt (v : value),
        declares_unique attr ds = true ->
        type_wf (TRecord rt) ->
        access_record rt attr = Success kt ->
        type_of_value v (aux_ty (idx := uidx) id_tag aux_tag (TList (TRecord rt))) ->
        unique_aux_declared hole attr tup acc id_tag aux_tag (locals := locals) row_ty ds v ->
        unique_aux_wf hole attr tup acc id_tag aux_tag (locals := locals) v.
    Proof.
      intros * H_uq H_rt H_attr H_ty [ H_aux H_id ].
      eapply (unique_aux_pre__unique_aux_wf hole attr tup acc id_tag aux_tag
                H_tags_diff rt kt v);
        [ exact H_rt | exact H_attr | exact H_ty | ].
      unfold unique_aux_pre. split; [ exact H_aux | ].
      unfold at_id_tag, key_holds, constrs_hold in *.
      repeat destruct_match_hyp; try contradiction.
      constructor; [ | constructor ].
      eapply unique_constr_holds_row_ty_irrel.
      eapply declares_unique__constr_holds; [ exact H_uq | exact H_id ].
    Qed.

    (* The rule, against the invariant the gated installation delivers.

       Nothing here is conditional on the program.  The table type comes from
       aug_transf_sound's own quantification; the row type the declarations
       were written against is irrelevant to what the key means; and the only
       hypothesis is that the declarations do name this attribute as a key,
       which is exactly the gate's decidable pattern match. *)
    Lemma unique_lookup_head_sound : forall row_ty ds,
        declares_unique attr ds = true ->
        expr_aug_transf_sound
          (@IndexInterface.is_tbl_ty uidx)
          (aux_ty (idx := uidx) id_tag aux_tag)
          (unique_aux_declared hole attr tup acc id_tag aux_tag (locals := locals) row_ty ds)
          unique_lookup_head.
    Proof.
      unfold expr_aug_transf_sound;
        intros row_ty ds H_uq * H_Gs H_Ge H_twf H_is H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl end.
      unfold aux_ty in E_tbl.
      (* the table is a list of records carrying the key; H_is is kept folded
         for the two lemmas below, which take it as it stands *)
      assert (H_is' := H_is).
      unfold IndexInterface.is_tbl_ty, unique_dict_idx,
        UniqueDictIndexImpl.is_tbl_ty in H_is'.
      repeat destruct_match_hyp; try discriminate.
      rewrite inb_true_iff in H_is'.
      destruct (In_access_record _ _ _ H_is') as [ kt E_attr ].
      split.
      1:{ eapply unique_lookup_head_preserve_ty;
            [ exact H_twf | exact H_is | exact E_tbl
            | apply aux_ty_access_id; exact H_tags_diff
            | apply aux_ty_access_aux
            | exact H_Gs | exact H_Ge | exact H_t ]. }
      intros store env H_lws H_lwe H_inv.
      eapply unique_lookup_head_preserve_sem;
        [ exact H_twf | exact H_is | exact E_tbl
        | apply aux_ty_access_id; exact H_tags_diff
        | apply aux_ty_access_aux
        | | exact H_Gs | exact H_Ge | exact H_t | exact H_lws | exact H_lwe ].
      (* the store carries the strong invariant at the table *)
      specialize (H_lws _ _ E_tbl).
      destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
      specialize (H_inv _ _ E_v).
      unfold value_wf_with_globals in H_inv; invert_Forall.
      lazymatch goal with
        H : _ \/ _ |- _ => destruct H as [ H_neq | H_decl ]; [ congruence | ]
      end.
      eapply unique_aux_declared__unique_aux_wf;
        [ exact H_uq | | exact E_attr | | exact H_decl ].
      1: invert_type_wf; assumption.
      1: unfold aux_ty; exact H_lws.
    Qed.

    (* ------------------------------------------------------------------
       Joining the pipeline.
       ------------------------------------------------------------------ *)

    (* The rule, applied everywhere below the installation. *)
    Definition unique_lookup_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl] (unique_lookup_head tbl).

    Lemma unique_lookup_transf_sound : forall row_ty ds,
        declares_unique attr ds = true ->
        aug_transf_sound
          (@IndexInterface.is_tbl_ty uidx)
          (aux_ty (idx := uidx) id_tag aux_tag)
          (unique_aux_declared hole attr tup acc id_tag aux_tag (locals := locals) row_ty ds)
          unique_lookup_transf.
    Proof.
      intros row_ty ds H_uq. unfold unique_lookup_transf.
      apply fold_command_with_globals_sound.
      apply unique_lookup_head_sound; exact H_uq.
    Qed.

    (* Install the key-to-row index and use it, gated on the declarations.
       The only premise beyond the ordinary typing ones is that the cenv
       describes the program it is paired with; nothing is assumed about the
       hints. *)
    Theorem unique_idx_pipeline_sound :
      forall ce (Gstore Genv : tenv) c,
        tenv_wf Gstore -> tenv_wf Genv ->
        well_typed Gstore Genv c ->
        cenv_respected (locals := locals) ce Gstore Genv c ->
        well_typed Gstore Genv
          (apply_unique_idx_transfs hole attr tup acc id_tag aux_tag
             ce unique_lookup_transf Gstore Genv c)
        /\ forall (store env : locals),
            locals_wf Gstore store -> locals_wf Genv env ->
            interp_command store env
              (apply_unique_idx_transfs hole attr tup acc id_tag aux_tag
                 ce unique_lookup_transf Gstore Genv c)
            = interp_command store env c.
    Proof.
      intros * H_Gs H_Ge H_wt H_ce.
      apply (apply_unique_idx_transfs_sound hole attr tup acc H_ne id_tag aux_tag H_tags_diff);
        auto.
      intros row_ty ds H_uq. apply unique_lookup_transf_sound; exact H_uq.
    Qed.

    (* And on an elaborated surface program the remaining premise is free. *)
    Corollary elab_unique_idx_pipeline_sound :
      forall sc ce free_vars (Gstore Genv : tenv) tbl row_ty ds,
        tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
        incl (get_free_vars Genv) free_vars ->
        Forall (decl_wf row_ty) ds ->
        well_typed Gstore Genv (elab ce free_vars (SLetConstrained tbl row_ty ds sc)) ->
        well_typed Gstore Genv
          (apply_unique_idx_transfs hole attr tup acc id_tag aux_tag
             ((tbl, (row_ty, ds)) :: cenv_rm tbl ce) unique_lookup_transf Gstore Genv
             (elab ce free_vars (SLetConstrained tbl row_ty ds sc)))
        /\ forall (store env : locals),
            locals_wf Gstore store -> locals_wf Genv env ->
            interp_command store env
              (apply_unique_idx_transfs hole attr tup acc id_tag aux_tag
                 ((tbl, (row_ty, ds)) :: cenv_rm tbl ce) unique_lookup_transf Gstore Genv
                 (elab ce free_vars (SLetConstrained tbl row_ty ds sc)))
            = interp_command store env (elab ce free_vars (SLetConstrained tbl row_ty ds sc)).
    Proof.
      intros * H_Gs H_Ge H_rt H_fv H_ds H_wt.
      apply (elab_unique_idx_transfs_sound hole attr tup acc H_ne id_tag aux_tag H_tags_diff);
        auto.
      intros row_ty' ds' H_uq. apply unique_lookup_transf_sound; exact H_uq.
    Qed.
  End WithMap.
End WithIndexUse.
