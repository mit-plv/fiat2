Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute fiat2.FlatmapForms fiat2.DictIndexImpl.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.

(* ------------------------------------------------------------------------
   A dictionary from a key to the rows at that key, kept AS A LIST in the
   table's own order.

   Every other index in this development is permutation-invariant: its
   to_idx coerces the rows to a bag or a set before anything looks at them
   (the four aggregates), or folds them into buckets whose step commutes
   (DictIndexImpl, CompositeDictIndexImpl, TrigramIndexImpl).  This one is
   deliberately NOT, and that is its whole point: the bucket is the
   SUBLIST of the table with that key, so a read that observes the order
   of a group can be served by a lookup instead of a scan.

   Two consequences worth stating up front.

   - None of DictIndexImpl's bucket algebra applies here.  bidx_step_comm
     is FALSE for this step: inserting two rows with the same key in the
     other order gives the other bucket order.  Nothing below cites it.

   - The characterisation (idx_chara) is an EQUALITY, not a Permutation as
     it is for the bag-valued index.  That is a strengthening, and it makes
     the read rule's proof shorter rather than longer: there is no bag
     canonicity to re-establish, because TyVList constrains nothing but the
     element types.

   The dict is Unranged.  No rule here range-queries it -- the key is a
   grouping key, not an ordering key -- so a hash table suffices, and
   saying Unranged is how that is communicated to a backend.  A read that
   wants the groups in key order is RangedDictIdx's business, not this
   index's. *)

Section WithHole.
  Context (hole : string).
  Context (attr : string).

  Section WithVars.
    Context (tup acc x : string).
    Context (H_NoDup : is_NoDup_opaque [tup; acc; x]).

    (* fold_right, so the LAST row is inserted FIRST and the first row of
       the table is consed on OUTERMOST: the bucket comes out in table
       order.  Prepending is what makes that so -- the step is the only
       place the order is decided. *)
    Definition to_idx : expr :=
      let k := EAccess (EVar tup) attr in
      EFold (EVar hole) (EAtom (AEmptyDict Unranged None)) tup acc
        (ETernop OInsert (EVar acc) k
           (EBinop OCons (EVar tup)
              (EOptMatch (EBinop OLookup (EVar acc) k)
                 (EAtom (ANil None))
                 x (EVar x)))).

    Definition is_tbl_ty (t : type) : bool :=
      match t with
      | TList (TRecord rt) => inb (String.eqb) attr (List.map fst rt)
      | _ => false
      end.

    Definition idx_ty (t : type) : type :=
      match t with
      | TList (TRecord rt) => TDict Unranged (get_attr_type rt attr) (TList (TRecord rt))
      | _ => TUnit
      end.

    Lemma idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t).
      destruct t; simpl; intros; try congruence.
      destruct t; try congruence.
      inversion H; subst. inversion H2; subst. repeat constructor; intuition auto.
      1: apply get_attr_type_ty_wf; auto.
    Qed.

    Section WithMap.
      Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
      Notation value := (value).
      Context {locals : map.map string value} {locals_ok : map.ok locals}.

      Ltac apply_In_access_record :=
        lazymatch goal with
          H: inb _ _ _ = true |- _ =>
            rewrite inb_true_iff in H;
            apply In_access_record in H
        end.

      Lemma to_idx_ty : forall (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t).
      Proof.
        intros. unfold to_idx.
        unfold is_tbl_ty in *. repeat destruct_match_hyp; try discriminate; subst.
        invert_type_wf. repeat econstructor; simpl; auto.
        all: repeat rewrite_map_get_put_goal; eauto.
        1: apply get_attr_type_ty_wf; auto.
        all: invert_type_wf; try now use_is_NoDup.
        1,2: unfold get_attr_type; apply_In_access_record; destruct_exists; rewrite_l_to_r; auto.
      Qed.

      Definition idx_wf (tbl_v idx_v : value) : Prop :=
        idx_v = interp_expr map.empty (map.put map.empty hole tbl_v) to_idx.

      Definition bucket_of (attr_v : value) (l : list value) : list value :=
        filter (fun r => match r with
                         | VRecord rc => value_eqb (record_proj attr rc) attr_v
                         | _ => false
                         end) l.

      (* An EQUALITY: the bucket at a key IS the table's sublist at that
         key, in the table's order.  Compare DictIndexImpl.idx_chara, which
         can only claim a Permutation. *)
      Definition idx_chara (tbl_v idx_v : value) : Prop :=
        match tbl_v, idx_v with
        | VList l, VDict d =>
            forall attr_v,
              match dict_lookup attr_v d with
              | Some (VList b) => b
              | _ => nil
              end
              = bucket_of attr_v l
        | _, _ => False
        end.

      Definition gallina_to_idx (tbl_v : value) : value :=
        match tbl_v with
        | VList l =>
            VDict (fold_right
                     (fun v acc => match v with
                                   | VRecord rc =>
                                       dict_insert (record_proj attr rc)
                                         (VList (VRecord rc ::
                                                   match dict_lookup (record_proj attr rc) acc with
                                                   | Some (VList b) => b
                                                   | _ => nil
                                                   end)) acc
                                   | _ => nil
                                   end) nil l)
        | _ => VDict nil
        end.

      Lemma fiat2_gallina_to_idx : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          interp_expr map.empty (map.put map.empty hole v) to_idx = gallina_to_idx v.
      Proof.
        unfold is_tbl_ty; intros. repeat destruct_match_hyp; try discriminate.
        invert_type_of_value_clear; simpl.
        unfold get_local; rewrite_map_get_put_goal.
        erewrite In_fold_right_ext with
          (P := fun a => type_of_value a (TDict Unranged (get_attr_type l attr) (TList (TRecord l))))
          (g := fun b a =>
                  match a with
                  | VDict d =>
                      match b with
                      | VRecord rc =>
                          VDict
                            (dict_insert
                               (record_proj attr rc)
                               (VList (b :: match dict_lookup (record_proj attr rc) d with
                                            | Some (VList bk) => bk
                                            | _ => nil
                                            end)) d)
                      | _ => VUnit
                      end
                  | _ => VUnit
                  end).
        2:{ constructor; cbn; auto using NoDup_nil, SSorted_nil. }
        2:{ intros. invert_type_of_value_clear.
            apply_Forall_In. invert_type_of_value_clear.
            repeat rewrite_map_get_put_goal; try now use_is_NoDup.
            (* the old bucket at this key is a well-typed list of rows *)
            enough (type_of_value (VOption (dict_lookup (record_proj attr l2) l1))
                      (TOption (TList (TRecord l)))).
            2:{ rewrite inb_true_iff in *.
                lazymatch goal with
                  H: In _ (List.map fst _) |- _ =>
                    apply In_fst in H; destruct H end.
                intuition idtac; destruct x0.
                cbn in *; subst.
                eapply dict_lookup_sound with (dk := Unranged).
                4:{ eapply record_proj_sound; eauto.
                    1: lazymatch goal with
                         H: context[Forall2] |- _ =>
                           apply Forall2_split in H;
                           rewrite Forall2_fst_eq in H
                       end;
                    intuition idtac; rewrite_l_to_r; auto. }
                1:{ repeat invert_type_wf. rewrite Forall_map in *.
                    apply_Forall_In; auto. }
                1:{ invert_type_wf. constructor; auto. }
                1:{ constructor; auto.
                    lazymatch goal with
                      H: context[get_attr_type] |- _ =>
                        erewrite NoDup_In_get_attr_type in H
                    end; eauto. } }
            intuition idtac.
            (* Both halves below case on the OLD bucket at this key.  The
               lookup is not syntactically None or Some, so it has to be
               destructed by hand -- which also rewrites the option-typing
               hypothesis, and that is where the bucket's element typing
               comes from. *)
            1:{ do 2 f_equal.
                lazymatch goal with
                  H: type_of_value (VOption (dict_lookup ?k ?d)) _ |- _ =>
                    destruct (dict_lookup k d) eqn:E_lk
                end.
                1:{ lazymatch goal with
                      H: type_of_value (VOption _) _ |- _ => inversion H; subst; clear H
                    end.
                    lazymatch goal with
                      H: type_of_value _ (TList _) |- _ => inversion H; subst; clear H
                    end.
                    cbn. rewrite_map_get_put_goal. reflexivity. }
                1: reflexivity. }
            1:{ invert_type_wf; apply dict_insert_sound.
                1: apply get_attr_type_ty_wf; auto.
                1: constructor; auto.
                1: constructor; auto.
                1:{ rewrite inb_true_iff in *.
                    lazymatch goal with
                      H: In _ (List.map fst _) |- _ =>
                        apply In_fst in H; destruct H end.
                    intuition idtac; destruct x0.
                    cbn in *; subst.
                    eapply record_proj_sound; eauto.
                    1: lazymatch goal with
                         H: context[Forall2] |- _ =>
                           apply Forall2_split in H;
                           rewrite Forall2_fst_eq in H
                       end;
                    intuition idtac; rewrite_l_to_r; auto.
                    erewrite NoDup_In_get_attr_type; eauto. }
                1:{ lazymatch goal with
                      H: type_of_value (VOption (dict_lookup ?k ?d)) _ |- _ =>
                        destruct (dict_lookup k d) eqn:E_lk
                    end.
                    1:{ lazymatch goal with
                          H: type_of_value (VOption _) _ |- _ => inversion H; subst; clear H
                        end.
                        lazymatch goal with
                          H: type_of_value _ (TList _) |- _ => inversion H; subst; clear H
                        end.
                        cbn. rewrite_map_get_put_goal.
                        repeat constructor; auto. }
                    1: repeat constructor; auto. } } }
        (* fold_right g has a value accumulator; gallina_to_idx's has a
           list-of-pairs one.  The bridge is an induction, and unlike the
           bag-valued index's it needs no case analysis afterwards: the
           bucket is a plain VList, so the two steps are convertible. *)
        1:{ induction l0; cbn; auto. invert_Forall. erewrite IHl0; auto.
            invert_type_of_value_clear. reflexivity. }
      Qed.


      (* ----------------------------------------------------------------
         The index's Gallina algebra.

         One step, one canonicity fact, and ONE characterisation strong
         enough to settle both write shapes: it gives the lookup as an
         OPTION, so dict_wf_lookup_ext applies and each write fact is
         decided by saying where each key lands.

         What is deliberately absent is a commutation lemma.  Every other
         bucketed index in this development has one (DictIndexImpl's
         bidx_step_comm, TrigramIndexImpl's tri_step_comm), and that is
         what lets an append be NORMALISED INTO a cons there.  Here it is
         false -- two rows at the same key in the other order give the
         other bucket -- so the two shapes get different rules and
         different emitted code. *)
      Definition is_record (v : value) : Prop :=
        match v with VRecord _ => True | _ => False end.

      Definition idx_step (v : value) (d : list (value * value)) : list (value * value) :=
        match v with
        | VRecord rc =>
            dict_insert (record_proj attr rc)
              (VList (VRecord rc :: match dict_lookup (record_proj attr rc) d with
                                    | Some (VList b) => b
                                    | _ => nil
                                    end)) d
        | _ => nil
        end.

      Lemma gallina_to_idx_fold : forall l,
          gallina_to_idx (VList l) = VDict (fold_right idx_step nil l).
      Proof. reflexivity. Qed.

      Lemma is_record_inv : forall v, is_record v -> exists rc, v = VRecord rc.
      Proof. destruct v; cbn; intros; try contradiction; eauto. Qed.

      Lemma type_of_value_TList_inv : forall (v : value) t,
          type_of_value v (TList t) ->
          exists l, v = VList l /\ Forall (fun u => type_of_value u t) l.
      Proof. intros v t H; inversion H; subst; eauto. Qed.

      Lemma type_of_value_TRecord_inv : forall (v : value) tl,
          type_of_value v (TRecord tl) -> exists rc, v = VRecord rc.
      Proof. intros v tl H; inversion H; subst; eauto. Qed.

      (* Per-node reduction.  cbn reduces under the EOptMatch branches and
         destroys the shapes these proofs match on, so each node is peeled
         by its own definitional equation instead. *)
      Lemma interp_ETernop' : forall (store env : locals) o e1 e2 e3,
          interp_expr store env (ETernop o e1 e2 e3)
          = interp_ternop o (interp_expr store env e1) (interp_expr store env e2)
              (interp_expr store env e3).
      Proof. reflexivity. Qed.

      Lemma interp_EAccess' : forall (store env : locals) r s,
          interp_expr store env (EAccess r s)
          = match interp_expr store env r with
            | VRecord rc => record_proj s rc
            | _ => VUnit
            end.
      Proof. reflexivity. Qed.

      Lemma interp_ANil : forall (store env : locals) t,
          interp_expr store env (EAtom (ANil t)) = VList nil.
      Proof. reflexivity. Qed.

      Lemma get_local_put_same : forall (env : locals) x v,
          get_local (map.put env x v) x = v.
      Proof. intros; unfold get_local; rewrite map.get_put_same; reflexivity. Qed.

      Lemma dict_wf_fold_idx_step : forall l,
          Forall is_record l -> dict_wf (fold_right idx_step nil l).
      Proof.
        induction 1; cbn; auto.
        lazymatch goal with H: is_record _ |- _ =>
          apply is_record_inv in H; destruct H as [? ->] end.
        apply dict_insert_preserve_dict_wf; assumption.
      Qed.

      (* The bucket at a key IS the table's sublist at that key, and a key
         with no rows has no entry at all.  Stated as an option so that it
         determines the dictionary. *)
      Lemma fold_idx_step_lookup : forall l,
          Forall is_record l ->
          forall k, dict_lookup k (fold_right idx_step nil l)
                    = match bucket_of k l with
                      | nil => None
                      | bk => Some (VList bk)
                      end.
      Proof.
        intros l H_rec; induction H_rec as [ | r l0 H_r H_rest IH ];
          intros k; cbn [fold_right bucket_of filter]; auto.
        apply is_record_inv in H_r; destruct H_r as [rc ->].
        cbn [idx_step filter].
        (* the old bucket at THIS row's key, by the induction hypothesis *)
        assert (H_old : match dict_lookup (record_proj attr rc) (fold_right idx_step nil l0) with
                        | Some (VList bk) => bk
                        | _ => nil
                        end = bucket_of (record_proj attr rc) l0).
        1:{ rewrite IH. unfold bucket_of.
            destruct (filter _ l0); reflexivity. }
        unfold bucket_of in *.
        rewrite H_old.
        destruct (value_eqb (record_proj attr rc) k) eqn:E_key.
        1:{ apply value_eqb_eq in E_key; subst k.
            rewrite DictIndexImpl.dict_lookup_insert_same; reflexivity. }
        1:{ rewrite DictIndexImpl.dict_lookup_insert_diff
              by (intro; subst; rewrite value_eqb_refl in E_key; discriminate).
            apply IH. }
      Qed.

      Lemma Forall_is_record_of_ty : forall l tl,
          Forall (fun v => type_of_value v (TRecord tl)) l -> Forall is_record l.
      Proof.
        induction 1; auto. constructor; auto.
        lazymatch goal with H: type_of_value _ (TRecord _) |- _ => inversion H end.
        cbn; auto.
      Qed.

      (* A row CONSED onto the front is PREPENDED to its bucket. *)
      Lemma fold_idx_step_cons : forall (r : value) l,
          fold_right idx_step nil (r :: l) = idx_step r (fold_right idx_step nil l).
      Proof. reflexivity. Qed.

      (* A row APPENDED at the end is APPENDED to its bucket -- which is
         not a cons, and is why this index needs a second rule where the
         permutation-invariant ones needed none. *)
      Lemma fold_idx_step_app_singleton : forall l rc,
          Forall is_record l ->
          fold_right idx_step nil (l ++ [VRecord rc])
          = dict_insert (record_proj attr rc)
              (VList (match dict_lookup (record_proj attr rc) (fold_right idx_step nil l) with
                      | Some (VList bk) => bk
                      | _ => nil
                      end ++ [VRecord rc]))
              (fold_right idx_step nil l).
      Proof.
        intros l rc H_rec.
        assert (H_rec' : Forall is_record (l ++ [VRecord rc]))
          by (rewrite Forall_app; split;
              [ assumption | constructor; [ exact I | constructor ] ]).
        apply dict_wf_lookup_ext.
        1: apply dict_wf_fold_idx_step; assumption.
        1: apply dict_insert_preserve_dict_wf, dict_wf_fold_idx_step; assumption.
        intros k.
        rewrite fold_idx_step_lookup by assumption.
        rewrite (fold_idx_step_lookup l) by assumption.
        unfold bucket_of; rewrite filter_app; cbn [filter].
        destruct (value_eqb (record_proj attr rc) k) eqn:E_key.
        1:{ apply value_eqb_eq in E_key; subst k.
            rewrite DictIndexImpl.dict_lookup_insert_same.
            destruct (filter _ l); cbn; reflexivity. }
        1:{ rewrite DictIndexImpl.dict_lookup_insert_diff
              by (intro; subst; rewrite value_eqb_refl in E_key; discriminate).
            rewrite app_nil_r.
            rewrite fold_idx_step_lookup by assumption. reflexivity. }
      Qed.
      (* The bucket at a key is the table's sublist at that key.  Where the
         bag-valued index can only move rows around inside a bucket and so
         states a Permutation, this is an equality -- and now it is a
         corollary of fold_idx_step_lookup rather than its own induction. *)
      Lemma idx_wf__idx_chara : forall (t : type) (tbl_v idx_v : value),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value tbl_v t ->
          idx_wf tbl_v idx_v -> idx_chara tbl_v idx_v.
      Proof.
        unfold idx_wf, idx_chara.
        intros; subst; erewrite fiat2_gallina_to_idx; eauto.
        unfold is_tbl_ty in *.
        repeat destruct_match_hyp; try discriminate.
        invert_type_of_value_clear.
        rewrite gallina_to_idx_fold. intros attr_v.
        rewrite fold_idx_step_lookup
          by (eapply Forall_is_record_of_ty; eassumption).
        unfold bucket_of; destruct (filter _ _); reflexivity.
      Qed.

      Lemma to_idx_wf : forall (v : value) (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          idx_wf v (interp_expr map.empty (map.put map.empty hole v) to_idx).
      Proof.
        intros; unfold idx_wf; auto.
      Qed.

      (* The rebuild, as a pattern.  Unranged is written literally: this
         index has one kind, so unlike DictIndexImpl's eto_idx there is no
         kind to check against the section's own. *)
      Notation eto_idx tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1 d :=
        (EFold d (EAtom (AEmptyDict Unranged None)) tup0 acc0
           (ETernop OInsert (EVar acc1) (EAccess (EVar tup1) attr0)
              (EBinop OCons (EVar tup3)
                 (EOptMatch (EBinop OLookup (EVar acc2) (EAccess (EVar tup2) attr1))
                    (EAtom (ANil None)) x0 (EVar x1))))).

      Ltac use_to_idx_ty :=
        eapply type_of_strengthen;
        [ apply to_idx_ty; auto
        | apply map_incl_empty
        | apply map_incl_refl ].

      Ltac prove_sub_wf :=
        unfold sub_wf; simpl; intros;
        case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
        [ rewrite_map_get_put_hyp
        | rewrite map.get_put_diff, map.get_empty in *; auto ];
        try congruence.

      Lemma fold_to_idx : forall Gstore Genv t e x0 tup0 acc0 free_vars,
          is_NoDup [x0; tup0; acc0] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          is_tbl_ty t = true ->
          type_of Gstore Genv e t ->
          incl (get_free_vars Genv) free_vars ->
          sem_eq Gstore Genv (idx_ty t)
            (EFold e (EAtom (AEmptyDict Unranged None)) tup0 acc0
               (ETernop OInsert (EVar acc0) (EAccess (EVar tup0) attr)
                  (EBinop OCons (EVar tup0)
                     (EOptMatch (EBinop OLookup (EVar acc0) (EAccess (EVar tup0) attr))
                        (EAtom (ANil None)) x0 (EVar x0)))))
            (substitute [(hole, e)] free_vars to_idx).
      Proof.
        unfold sem_eq, is_tbl_ty; intros.
        repeat destruct_match_hyp; try discriminate; subst.
        intuition idtac.
        1:{ unfold idx_ty in *. lazymatch goal with
            H: type_of _ _ _ _ |- _ =>
              apply type_of__type_wf in H as H' end; auto.
            repeat invert_type_wf.
            repeat (econstructor; simpl; intuition eauto).
            all: repeat rewrite_map_get_put_goal; try congruence; eauto.
            1: apply get_attr_type_ty_wf; eauto with fiat2_hints.
            1,2: unfold get_attr_type; apply_In_access_record; destruct_exists; rewrite_l_to_r; auto. }
        1:{ eapply substitute_preserve_ty; auto.
            2: use_to_idx_ty.
            1,2: eauto using idx_ty_wf with fiat2_hints.
            1: prove_sub_wf. }
        erewrite substitute_preserve_sem with (t0:=idx_ty (TList (TRecord l))).
        1:{ simpl.
            unfold get_local; rewrite_map_get_put_goal.
            repeat case_match; auto.
            eapply In_fold_right_ext with (P:=fun _ => True); intuition auto.
            repeat rewrite_map_get_put_goal; try now use_is_NoDup.
            case_match; auto. do 2 f_equal.
            apply_type_sound e.
            rewrite_l_to_r. invert_type_of_value_clear.
            apply_Forall_In. invert_type_of_value_clear.
            case_match; auto. repeat rewrite_map_get_put_goal; auto. }
        6-8: eauto.
        all: auto.
        2: use_to_idx_ty.
        all: eauto using idx_ty_wf with fiat2_hints.
        prove_sub_wf.
      Qed.

      Instance list_dict_idx : IndexInterface.index := IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

      Instance list_dict_idx_ok : IndexInterface.ok list_dict_idx idx_wf :=
        IndexInterface.Build_ok list_dict_idx idx_wf idx_ty_wf to_idx_ty to_idx_wf.

      Section WithTags.
        Context (id_tag aux_tag idx_tag: string).

        Notation aux_ty_for_idx := (aux_ty_for_idx id_tag aux_tag idx_tag idx_ty).
        Notation aux_wf_for_idx := (aux_wf_for_idx id_tag aux_tag idx_tag idx_wf).

        Section eq_filter_to_lookup.
          Context (b : string).
          Context (tbl : string).

          (* The rule this index exists for.  DictIndexImpl's counterpart
             matches a filter at BAG level (flatmap_filter_bag under an
             OBagOfList), because its buckets are bags; a read that keeps
             the group's order never reaches it and stays a scan.  This one
             matches the filter at LIST level and answers it with a lookup,
             and the bucket it returns is the filtered sublist itself --
             idx_chara is an equality, so the order is preserved on the
             nose rather than up to permutation. *)
          Definition eq_filter_to_lookup_list_head (e : expr) :=
            (* [row <- tbl[id_tag], check(row.attr == e'), ret row] (as a list) -->
               match (lookup idx e') with none => nil | some b => b *)
            match e with
            | flatmap_filter_list
                (EAccess (ELoc tbl0) id_tag0)
                x0 (EBinop OEq (EAccess (EVar x1) attr0) e') x2 _ _ =>
                if (all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x0, [x1; x2]); (id_tag, [id_tag0])] &&
                      negb (free_immut_in x0 e'))%bool
                then EOptMatch (EBinop OLookup (EAccess (EAccess (ELoc tbl) aux_tag) idx_tag) e')
                       (EAtom (ANil None))
                       b (EVar b)
                else e
            | _ => e
            end.

          Lemma eq_filter_to_lookup_list_head_preserve_ty : forall tl t aux_tl (Gstore : tenv),
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              preserve_ty Gstore eq_filter_to_lookup_list_head.
          Proof.
            unfold preserve_ty, is_tbl_ty. intros.
            repeat destruct_match_hyp; try congruence.
            repeat destruct_subexpr. simpl.
            case_match; auto. repeat rewrite Bool.andb_true_r in *.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            rewrite Bool.negb_true_iff, eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear. repeat rewrite_map_get_put_hyp.
            repeat (clear_refl; repeat do_injection2).
            repeat (rewrite_l_to_r; do_injection2).
            repeat (econstructor; eauto).
            1:{ unfold get_attr_type.
                lazymatch goal with H: ?x = _ |- context[?x] => rewrite H end.
                eapply not_free_immut_put_ty; eauto. }
            1-3: repeat invert_type_wf; auto.
            1: rewrite map.get_put_same; trivial.
          Qed.
          Lemma eq_filter_to_lookup_list_head_preserve_sem : forall (Gstore : tenv) (store : locals) tl t aux_tl,
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              match map.get store tbl with
              | Some v => aux_wf_for_idx v
              | _ => False
              end ->
              preserve_sem Gstore store eq_filter_to_lookup_list_head.
          Proof.
            unfold preserve_sem, aux_wf_for_idx; intros.
            unfold is_tbl_ty, idx_ty in *.
            apply_locals_wf store.
            repeat (destruct_match_hyp; try discriminate; intuition idtac; []).
            assert (idx_chara a a1).
            { subst. eapply idx_wf__idx_chara; eauto.
              invert_type_of_value_clear.
              pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H16 E1 H2); auto. }
            lazymatch goal with
              H: idx_wf _ _, H': idx_chara _ _ |- _ =>
                clear H; unfold idx_chara in H'
            end.
            invert_type_of_value_clear.
            pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H16 E1 H2).
            pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H16 E2 H3).
            invert_type_of_value_clear.
            pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H20 E4 H4).
            invert_type_of_value_clear.
            repeat destruct_subexpr. unfold eq_filter_to_lookup_list_head.
            cbv beta iota; case_match; auto.
            cbn [all_eqb all_eqb' andb] in *.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            rewrite Bool.negb_true_iff, eqb_eq in *; subst. repeat clear_refl.
            rewrite interp_flatmap_filter_list.
            cbn. unfold get_local. rewrite_l_to_r. unfold record_proj.
            repeat rewrite_l_to_r.
            repeat (destruct_match_hyp; intuition idtac).
            repeat invert_type_of_clear. rewrite_map_get_put_hyp.
            lazymatch goal with
              H: type_of _ _ e2_1_2 _ |- _ =>
                apply not_free_immut_put_ty in H; auto
            end.
            (* From here the list index's proof diverges from the bag
               index's, and gets shorter.  There is no bag canonicity to
               re-establish and no Permutation to transport: the filter in
               the source IS the bucket, so the whole argument is (i) the
               filter's predicate agrees with the bucket's on well-typed
               rows, and (ii) the lookup's result is a VList. *)
            assert (H_rows : Forall (fun v => type_of_value v (TRecord l1)) l3)
              by (lazymatch goal with
                    H: type_of_value (VList l3) _ |- _ =>
                      inversion H; subst; assumption
                  end).
            lazymatch goal with
            | |- _ = VList (filter ?f l3) =>
                assert (H_pred : filter f l3 = bucket_of (interp_expr store env e2_1_2) l3)
            end.
            1:{ unfold bucket_of. apply In_filter_ext; intros v H_in.
                rewrite Forall_forall in H_rows. specialize (H_rows v H_in).
                inversion H_rows; subst.
                rewrite_map_get_put_goal. cbn. unfold record_proj.
                erewrite <- not_free_immut_put_sem; eauto. }
            rewrite H_pred, <- H12.
            (* (ii): the bucket is a list.  Forall_dict_lookup reads it
               straight off the dictionary's element typing, which avoids
               needing the KEY's type and so avoids dict_lookup_sound. *)
            destruct (dict_lookup (interp_expr store env e2_1_2) l2) eqn:E_lk.
            1:{ lazymatch goal with
                  H: Forall (fun _ : value * value => _ /\ _) l2 |- _ =>
                    pose proof (Forall_dict_lookup _ _ _ _ H E_lk) as H_v
                end.
                cbn in H_v. destruct H_v as [_ H_v].
                inversion H_v; subst. rewrite_map_get_put_goal. reflexivity. }
            1: reflexivity.
          Qed.
        End eq_filter_to_lookup.


        (* ----------------------------------------------------------------
           Maintenance.  The two row-adding shapes get DIFFERENT rules here,
           and that is the substantive difference between this index and
           every other one in the development.

           Elsewhere an append is NORMALISED INTO a cons -- under a bag or
           set coercion (CollectionTransf.snoc_to_cons_under_coercion) or
           inside a bucket fold whose step commutes (DictIndexImpl's
           snoc_to_cons_in_idx_head) -- and the existing cons rule then
           fires unchanged.  Neither move is available here: the bucket is
           a list, so where the row goes in it is exactly what the index
           records.  A cons PREPENDS to the bucket; an append APPENDS to
           it. *)
        Section row_to_insert.
          Context (y : string).

          Definition cons_to_insert_list_head (e : expr) :=
            match e with
            | eto_idx tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1 (EBinop OCons e1 e2) =>
                if (all_eqb [(acc0, [acc1; acc2]); (tup0, [tup1; tup2; tup3]); (attr, [attr0; attr1]); (x0, [x1])] &&
                      all_neqb [acc0; tup0; x0] &&
                      negb (free_immut_in y e1))%bool
                then
                  ELet (eto_idx tup tup tup tup acc acc acc x x attr attr e2) y
                       (ETernop OInsert (EVar y)
                          (EAccess e1 attr)
                          (EBinop OCons e1
                             (EOptMatch
                                (EBinop OLookup (EVar y) (EAccess e1 attr))
                                (EAtom (ANil None)) x (EVar x))))
                else e
            | _ => e
            end.

          Definition snoc_to_append_list_head (e : expr) :=
            match e with
            | eto_idx tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1
                (EBinop OConcat e2 (EBinop OCons e1 (EAtom (ANil _)))) =>
                if (all_eqb [(acc0, [acc1; acc2]); (tup0, [tup1; tup2; tup3]); (attr, [attr0; attr1]); (x0, [x1])] &&
                      all_neqb [acc0; tup0; x0] &&
                      negb (free_immut_in y e1))%bool
                then
                  ELet (eto_idx tup tup tup tup acc acc acc x x attr attr e2) y
                       (ETernop OInsert (EVar y)
                          (EAccess e1 attr)
                          (EBinop OConcat
                             (EOptMatch
                                (EBinop OLookup (EVar y) (EAccess e1 attr))
                                (EAtom (ANil None)) x (EVar x))
                             (EBinop OCons e1 (EAtom (ANil None)))))
                else e
            | _ => e
            end.

          Lemma fiat2_gallina_to_idx2: forall (store env : locals) v t,
              type_wf t -> is_tbl_ty t = true ->
              type_of_value v t ->
              map.get env hole = Some v ->
              interp_expr store env to_idx = gallina_to_idx v.
          Proof.
            intros.
            erewrite interp_expr_strengthen.
            1: eapply fiat2_gallina_to_idx.
            6: apply to_idx_ty.
            all: eauto with fiat2_hints.
            2: eapply map_incl_step_l; eauto using Decidable.String.eqb_spec.
            all: apply map_incl_empty.
          Qed.

          (* The substituted rebuild, as one equation.  Stating it
             separately keeps the maintenance proofs from having to steer
             fiat2_gallina_to_idx2's four obligations by position. *)
          Lemma interp_to_idx_sub : forall (store env : locals) e t,
              type_wf t -> is_tbl_ty t = true ->
              type_of_value (interp_expr store env e) t ->
              interp_expr store (make_sub_env store env [(hole, e)]) to_idx
              = gallina_to_idx (interp_expr store env e).
          Proof.
            intros. eapply fiat2_gallina_to_idx2; eauto.
            cbn [make_sub_env]. apply map.get_put_same.
          Qed.

          Lemma cons_to_insert_list_head_preserve_sem : forall (Gstore : tenv) (store : locals),
              preserve_sem Gstore store cons_to_insert_list_head.
          Proof.
            unfold preserve_sem; intros. repeat destruct_subexpr.
            cbn [cons_to_insert_list_head]. repeat (case_match; auto; []).
            cbn in * |-.
            rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition idtac.
            rewrite eqb_eq, eqb_neq in *; subst. repeat invert_type_of_clear.
            repeat rewrite_map_get_put_hyp.
            repeat (try clear_refl; repeat do_injection).
            repeat invert_type_of_op_clear.
            enough (E_Let: forall e1 e2 x, interp_expr store env (ELet e1 x e2) = interp_expr store (map.put env x (interp_expr store env e1)) e2); auto.
            rewrite E_Let.
            erewrite sem_eq_eq with (env:=env) (t:=idx_ty (TList (TRecord tl))); [ | eauto .. ].
            2:{ apply fold_to_idx; eauto using incl_refl.
                1: use_is_NoDup.
                1: access_record_Success__is_tbl_ty. }
            let pat := open_constr:(EFold _ _ v acc0 _) in
            erewrite sem_eq_eq with (t:=idx_ty (TList (TRecord tl))) (e1:=pat); [ | eauto .. ].
            2:{ apply fold_to_idx; eauto using incl_refl.
                1: use_is_NoDup.
                1: access_record_Success__is_tbl_ty.
                1: repeat econstructor; eauto. }
            erewrite substitute_preserve_sem with (Genv0:=map.put map.empty hole (TList (TRecord tl))); [ | | | | eauto .. ]; eauto using incl_refl with fiat2_hints.
            3: prove_sub_wf.
            2:{ eapply type_of_strengthen;
                [ | apply map_incl_empty | apply map_incl_refl ].
                apply to_idx_ty; cbn; eauto with fiat2_hints;
                  access_record_Success__is_tbl_ty. }
            erewrite substitute_preserve_sem with (Genv0:=map.put map.empty hole (TList (TRecord tl))); [ | | | | eauto .. ]; eauto using incl_refl with fiat2_hints.
            3:{ prove_sub_wf.
                do_injection. repeat econstructor; eauto. }
            2:{ eapply type_of_strengthen;
                [ | apply map_incl_empty | apply map_incl_refl ].
                apply to_idx_ty; cbn; eauto with fiat2_hints;
                  access_record_Success__is_tbl_ty. }
            erewrite fiat2_gallina_to_idx2;
              [ | | | | cbn; rewrite_map_get_put_goal; reflexivity ];
              [ | | | eapply type_sound; eauto ]; eauto with fiat2_hints;
              [ | access_record_Success__is_tbl_ty ].
            erewrite fiat2_gallina_to_idx2;
              [ | | | | cbn; rewrite_map_get_put_goal; reflexivity ];
              [ | | | apply_type_sound e1_2; invert_type_of_value_clear;
                      repeat constructor; eauto with fiat2_hints ];
              eauto with fiat2_hints;
              [ | access_record_Success__is_tbl_ty ].
            apply_type_sound e1_2; invert_type_of_value_clear. cbn.
            unfold get_local; rewrite_map_get_put_goal.
            f_equal. apply_type_sound e1_1; invert_type_of_value_clear.
            erewrite <- not_free_immut_put_sem; auto.
            rewrite_expr_value.
            (* The bucket must be destructed BEFORE the env lookup is
               simplified: until then the Some branch binds its own
               variable, and rewrite cannot reach under that binder. *)
            fold idx_step.
            rewrite !fold_idx_step_lookup
              by (eapply Forall_is_record_of_ty; eassumption).
            destruct (bucket_of (record_proj attr l0) l) eqn:E_bk; cbn.
            1: reflexivity.
            rewrite_map_get_put_goal. reflexivity.
          Qed.
          Lemma cons_to_insert_list_head_preserve_ty : forall (Gstore : tenv),
              preserve_ty Gstore cons_to_insert_list_head.
          Proof.
            unfold preserve_ty; intros. repeat destruct_subexpr.
            cbn. repeat (case_match; auto).
            rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition auto.
            rewrite eqb_eq, eqb_neq in *; subst. repeat invert_type_of_clear.
            repeat rewrite_map_get_put_hyp.
            repeat (try clear_refl; repeat do_injection).
            repeat invert_type_of_op_clear.
            repeat (econstructor; eauto);
              repeat rewrite_map_get_put_goal; auto;
              try use_is_NoDup.
            all: repeat eapply not_free_immut_put_ty2; eauto.
          Qed.

          Lemma snoc_to_append_list_head_preserve_ty : forall (Gstore : tenv),
              preserve_ty Gstore snoc_to_append_list_head.
          Proof.
            unfold preserve_ty; intros. repeat destruct_subexpr.
            cbn. repeat (case_match; auto).
            rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition auto.
            rewrite eqb_eq, eqb_neq in *; subst. repeat invert_type_of_clear.
            repeat rewrite_map_get_put_hyp.
            repeat (try clear_refl; repeat do_injection).
            repeat invert_type_of_op_clear.
            repeat (econstructor; eauto);
              repeat rewrite_map_get_put_goal; auto;
              try use_is_NoDup.
            all: repeat eapply not_free_immut_put_ty2; eauto.
          Qed.

          Lemma snoc_to_append_list_head_preserve_sem : forall (Gstore : tenv) (store : locals),
              preserve_sem Gstore store snoc_to_append_list_head.
          Proof.
            unfold preserve_sem; intros. repeat destruct_subexpr.
            cbn [snoc_to_append_list_head]. repeat (case_match; auto; []).
            cbn in * |-.
            rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition idtac.
            rewrite eqb_eq, eqb_neq in *; subst. repeat invert_type_of_clear.
            repeat rewrite_map_get_put_hyp.
            repeat (try clear_refl; repeat do_injection).
            repeat invert_type_of_op_clear.
            enough (E_Let: forall e1 e2 x, interp_expr store env (ELet e1 x e2) = interp_expr store (map.put env x (interp_expr store env e1)) e2); auto.
            rewrite E_Let.
            erewrite sem_eq_eq with (env:=env) (t:=idx_ty (TList (TRecord tl))); [ | eauto .. ].
            2:{ apply fold_to_idx; eauto using incl_refl.
                1: use_is_NoDup.
                1: access_record_Success__is_tbl_ty. }
            let pat := open_constr:(EFold _ _ v acc0 _) in
            erewrite sem_eq_eq with (t:=idx_ty (TList (TRecord tl))) (e1:=pat); [ | eauto .. ].
            2:{ apply fold_to_idx; eauto using incl_refl.
                1: use_is_NoDup.
                1: access_record_Success__is_tbl_ty.
                1: repeat econstructor; eauto. }
            erewrite substitute_preserve_sem with (Genv0:=map.put map.empty hole (TList (TRecord tl))); [ | | | | eauto .. ]; eauto using incl_refl with fiat2_hints.
            3: prove_sub_wf.
            2:{ eapply type_of_strengthen;
                [ | apply map_incl_empty | apply map_incl_refl ].
                apply to_idx_ty; cbn; eauto with fiat2_hints;
                  access_record_Success__is_tbl_ty. }
            erewrite substitute_preserve_sem with (Genv0:=map.put map.empty hole (TList (TRecord tl))); [ | | | | eauto .. ]; eauto using incl_refl with fiat2_hints.
            3:{ prove_sub_wf.
                do_injection. repeat econstructor; eauto. }
            2:{ eapply type_of_strengthen;
                [ | apply map_incl_empty | apply map_incl_refl ].
                apply to_idx_ty; cbn; eauto with fiat2_hints;
                  access_record_Success__is_tbl_ty. }
            assert (H_tbl_ty : is_tbl_ty (TList (TRecord tl)) = true)
              by access_record_Success__is_tbl_ty.
            assert (H_twf : type_wf (TList (TRecord tl))) by eauto with fiat2_hints.
            assert (H_v1 : type_of_value (interp_expr store env e1_1) (TList (TRecord tl)))
              by (eapply type_sound; eauto).
            assert (H_v2 : type_of_value
                             (interp_expr store env
                                (EBinop OConcat e1_1 (EBinop OCons e1_2_1 (EAtom (ANil t0)))))
                             (TList (TRecord tl)))
              by (eapply type_sound; [ repeat econstructor; eauto | .. ]; eauto).
            rewrite (interp_to_idx_sub store env e1_1 _ H_twf H_tbl_ty H_v1).
            rewrite (interp_to_idx_sub store env _ _ H_twf H_tbl_ty H_v2).
            apply type_of_value_TList_inv in H_v1 as [ rows [ E_rows H_rows ] ].
            assert (H_row : type_of_value (interp_expr store env e1_2_1) (TRecord tl))
              by (eapply type_sound; eauto).
            apply type_of_value_TRecord_inv in H_row as [ rc E_rc ].
            assert (H_rec : Forall is_record rows)
              by (eapply Forall_is_record_of_ty; eassumption).
            (* the OLD bucket at the appended row's key *)
            assert (E_scrut : interp_expr store (map.put env y (gallina_to_idx (VList rows)))
                                (EBinop OLookup (EVar y) (EAccess e1_2_1 attr))
                              = VOption (dict_lookup (record_proj attr rc)
                                           (fold_right idx_step nil rows))).
            1:{ rewrite interp_EBinop, interp_EVar, interp_EAccess'.
                erewrite <- not_free_immut_put_sem by eassumption.
                rewrite E_rc, get_local_put_same, gallina_to_idx_fold. reflexivity. }
            rewrite E_rows.
            rewrite interp_ETernop'.
            rewrite !(interp_EBinop store _ OConcat).
            rewrite interp_EOptMatch, E_scrut.
            rewrite !(interp_EBinop store _ OCons).
            rewrite interp_EVar, !interp_EAccess', !interp_ANil.
            erewrite <- !(not_free_immut_put_sem e1_2_1) by eassumption.
            rewrite E_rc, get_local_put_same.
            rewrite E_rows.
            cbn [interp_binop interp_ternop].
            rewrite !gallina_to_idx_fold.
            rewrite fold_idx_step_app_singleton by assumption.
            rewrite (fold_idx_step_lookup rows) by assumption.
            (* the bucket must be destructed before the Some branch's
               binder can be eliminated *)
            destruct (bucket_of (record_proj attr rc) rows) eqn:E_bk; cbn.
            1: reflexivity.
            rewrite get_local_put_same.
            reflexivity.
          Qed.
        End row_to_insert.
        Section use_idx.
          Context (tbl : string).

          (* Don't rebuild what is already stored.  Identical in shape to
             DictIndexImpl's rule minus the kind test, which this index does
             not need: it has one kind. *)
          Definition use_list_idx_head (e : expr) :=
            match e with
            | eto_idx tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1 (EAccess (ELoc tbl0) id_tag0) =>
                if (all_eqb [(acc0, [acc1; acc2]); (tup0, [tup1; tup2; tup3]); (attr, [attr0; attr1]); (x0, [x1]); (tbl, [tbl0]); (id_tag, [id_tag0])] &&
                      all_neqb [acc0; tup0; x0])%bool
                then EAccess (EAccess (ELoc tbl) aux_tag) idx_tag
                else e
            | _ => e
            end.

          Lemma use_list_idx_head_preserve_ty : forall tl t aux_tl (Gstore : tenv),
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              preserve_ty Gstore use_list_idx_head.
          Proof.
            clear H_NoDup.
            unfold preserve_ty, is_tbl_ty. intros.
            repeat destruct_match_hyp; try congruence.
            repeat destruct_subexpr. simpl.
            repeat (case_match; auto; []). repeat rewrite Bool.andb_true_r in *.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear. repeat rewrite_map_get_put_hyp.
            repeat (clear_refl; repeat do_injection2).
            repeat (rewrite_l_to_r; do_injection2).
            repeat lazymatch goal with
                     H: type_of_atom _ _ |- _ =>
                       inversion H; subst; clear H
                   end.
            repeat (econstructor; eauto).
            lazymatch goal with H: ?x = _ |- context[?x] => rewrite H end.
            f_equal; unfold idx_ty; f_equal; try reflexivity.
            unfold get_attr_type.
            lazymatch goal with H: ?x = _ |- context[?x] => rewrite H end.
            reflexivity.
          Qed.

          Lemma use_list_idx_head_preserve_sem : forall (Gstore : tenv) (store : locals) tl t aux_tl,
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              match map.get store tbl with
              | Some v => aux_wf_for_idx v
              | _ => False
              end ->
              preserve_sem Gstore store use_list_idx_head.
          Proof.
            unfold preserve_sem, aux_wf_for_idx, idx_wf; intros.
            unfold is_tbl_ty, idx_ty in *.
            apply_locals_wf store.
            repeat (destruct_match_hyp; try discriminate; intuition idtac; []).
            invert_type_of_value_clear.
            pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H16 E1 H2).
            repeat destruct_subexpr.
            cbn [use_list_idx_head]; repeat (case_match; auto; []).
            cbn [all_eqb all_eqb' all_neqb all_neqb'] in * |-.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
            repeat clear_refl.
            let pat := open_constr:(EFold _ _ _ _ _) in
            erewrite sem_eq_eq with (t:=idx_ty (TList (TRecord l1))) (e1:=pat); [ | eauto .. ].
            2:{ apply fold_to_idx; eauto using incl_refl.
                1: use_is_NoDup.
                1: repeat econstructor; eauto. }
            erewrite substitute_preserve_sem with (Genv0:=map.put map.empty hole (TList (TRecord l1))); [ | | | | eauto .. ]; eauto using incl_refl with fiat2_hints.
            2: eapply type_of_strengthen; eauto using to_idx_ty;
            [ apply map_incl_empty | apply map_incl_refl ].
            2:{ prove_sub_wf. do_injection.
                repeat econstructor; eauto. }
            remember to_idx as to_idx_opaque. unfold make_sub_env.
            cbn [interp_expr].
            unfold get_local, record_proj; repeat rewrite_l_to_r.
            symmetry; eapply interp_expr_strengthen;
              [ | | | eauto using map_incl_empty, map_incl_refl .. ];
              [ | | apply to_idx_ty | | apply locals_wf_step; eauto with fiat2_hints ];
              eauto with fiat2_hints.
          Qed.
        End use_idx.

        Ltac invert_tenv_wf_with_globals :=
          lazymatch goal with H: tenv_wf_with_globals _ _ _ |- _ => inversion H; subst end.

        Lemma eq_filter_to_lookup_list_head_sound : forall b is_tbl_ty' aux_ty aux_wf,
            aux_ty_for_idx aux_ty ->
            (forall t, is_tbl_ty' t = true -> is_tbl_ty t = true) ->
            (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
            expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf
              (eq_filter_to_lookup_list_head b).
        Proof.
          unfold aux_ty_for_idx, expr_aug_transf_sound; intros.
          invert_tenv_wf_with_globals.
          specialize (H tbl_ty). repeat destruct_match_hyp; intuition idtac.
          1: eapply eq_filter_to_lookup_list_head_preserve_ty; eauto.
          1: eapply eq_filter_to_lookup_list_head_preserve_sem; eauto.
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

        Lemma use_list_idx_head_sound : forall is_tbl_ty' aux_ty aux_wf,
            aux_ty_for_idx aux_ty ->
            (forall t, is_tbl_ty' t = true -> is_tbl_ty t = true) ->
            (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
            expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf use_list_idx_head.
        Proof.
          unfold aux_ty_for_idx, expr_aug_transf_sound; intros.
          invert_tenv_wf_with_globals.
          specialize (H tbl_ty). repeat destruct_match_hyp; intuition idtac.
          1: eapply use_list_idx_head_preserve_ty; eauto.
          1: eapply use_list_idx_head_preserve_sem; eauto.
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
      End WithTags.

      Lemma cons_to_insert_list_head_sound : forall y,
          expr_transf_sound (locals:=locals) (cons_to_insert_list_head y).
      Proof.
        unfold expr_transf_sound; intros.
        intuition idtac.
        1: eapply cons_to_insert_list_head_preserve_ty; eauto.
        1: eapply cons_to_insert_list_head_preserve_sem; [ | | eauto .. ]; auto.
      Qed.

      Lemma snoc_to_append_list_head_sound : forall y,
          expr_transf_sound (locals:=locals) (snoc_to_append_list_head y).
      Proof.
        unfold expr_transf_sound; intros.
        intuition idtac.
        1: eapply snoc_to_append_list_head_preserve_ty; eauto.
        1: eapply snoc_to_append_list_head_preserve_sem; [ | | eauto .. ]; auto.
      Qed.
    End WithMap.
  End WithVars.
End WithHole.

(* Fully-applied forms, so that eauto with transf_hints can find them --
   the section-closed lemmas take their parameters in an order eauto will
   not guess.  Mirrors DictIndexImpl's *_sound2 wrappers. *)
Lemma use_list_idx_head_sound2 : forall (hole attr : string),
    forall tup acc x : string,
    forall tenv : map.map string type,
      map.ok tenv ->
      forall locals : map.map string value,
        map.ok locals ->
        forall (id_tag aux_tag idx_tag : string) (is_tbl_ty' : type -> bool)
          (aux_ty : type -> type) (aux_wf : value -> Prop),
          (forall v : value,
              aux_wf v -> aux_wf_for_idx id_tag aux_tag idx_tag (idx_wf hole attr tup acc x) v) ->
          aux_ty_for_idx id_tag aux_tag idx_tag (idx_ty attr) aux_ty ->
          (forall t : type, is_tbl_ty' t = true -> ListDictIndexImpl.is_tbl_ty attr t = true) ->
          is_NoDup_opaque [tup; acc; x] ->
          expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf
            (use_list_idx_head attr id_tag aux_tag idx_tag).
Proof.
  intros; eapply use_list_idx_head_sound; eauto.
Qed.

Lemma eq_filter_to_lookup_list_head_sound2 : forall (hole attr : string),
    forall tup acc x : string,
    forall tenv : map.map string type,
      map.ok tenv ->
      forall locals : map.map string value,
        map.ok locals ->
        forall (id_tag aux_tag idx_tag b : string) (is_tbl_ty' : type -> bool)
          (aux_ty : type -> type) (aux_wf : value -> Prop),
          aux_ty_for_idx id_tag aux_tag idx_tag (idx_ty attr) aux_ty ->
          (forall t : type, is_tbl_ty' t = true -> ListDictIndexImpl.is_tbl_ty attr t = true) ->
          (forall v : value,
              aux_wf v -> aux_wf_for_idx id_tag aux_tag idx_tag (idx_wf hole attr tup acc x) v) ->
          is_NoDup_opaque [tup; acc; x] ->
          expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf
            (eq_filter_to_lookup_list_head attr id_tag aux_tag idx_tag b).
Proof.
  intros; eapply eq_filter_to_lookup_list_head_sound; eauto.
Qed.

#[export] Hint Resolve use_list_idx_head_sound2 : transf_hints.
#[export] Hint Resolve eq_filter_to_lookup_list_head_sound2 : transf_hints.
#[export] Hint Resolve cons_to_insert_list_head_sound : transf_hints.
#[export] Hint Resolve snoc_to_append_list_head_sound : transf_hints.

#[export] Hint Extern 5 (type_of _ _ IndexInterface.to_idx _) => apply to_idx_ty : transf_hints.
#[export] Hint Extern 5 (type_wf (IndexInterface.idx_ty _)) => apply idx_ty_wf : transf_hints.
