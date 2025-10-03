Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface2 fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.

Section WithMap.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Lemma not_free_immut_put_ty2 : forall (x : string) (e : expr) (Gstore Genv : tenv) (t t' : type),
      free_immut_in x e = false ->
      type_of Gstore Genv e t ->
      type_of Gstore (map.put Genv x t') e t.
  Proof.
    intros. destruct (map.get Genv x) eqn:E.
    1:{ rewrite <- Properties.map.put_remove_same.
        eapply type_of_strengthen;
          [
          | apply map_incl_refl
          | apply map_incl_step_r; try apply map_incl_refl;
            apply map.get_remove_same ].
        eapply not_free_immut_put_ty; eauto.
        rewrite Properties.map.put_remove_same, Properties.map.put_noop; eauto. }
    1:{ eapply type_of_strengthen; eauto using map_incl_refl.
        apply map_incl_step_r; auto using map_incl_refl. }
  Qed.
End WithMap.

Ltac access_record_Success__is_tbl_ty :=
  cbn; apply inb_true_iff;
  lazymatch goal with
    H: access_record _ _ = Success _ |- _ =>
      apply access_record_sound in H;
      apply in_map with (f:=fst) in H;
      cbn in H
  end; assumption.

Section WithHole.
  Context (hole : string).
  Context (attr : string).

  Section WithVars.
    Context (tup acc x k v y : string).
    Context (H_NoDup : is_NoDup_opaque [tup; acc; x; k; v; y]).

    Definition to_idx : expr :=
      let k := EAccess (EVar tup) attr in
      EFold (EVar hole) (EAtom (AEmptyDict None)) tup acc
        (ETernop OInsert (EVar acc) k
           (EBinop OBagInsert
              (EOptMatch (EBinop OLookup (EVar acc) k)
                 (EAtom (AEmptyBag None))
                 x (EVar x))
              (EVar tup))).

    Definition is_tbl_ty (t : type) : bool :=
      match t with
      | TList (TRecord rt) => inb (String.eqb) attr (List.map fst rt)
      | _ => false
      end.

    Definition idx_ty (t : type) : type :=
      match t with
      | TList (TRecord rt) => TDict (get_attr_type rt attr) (TBag (TRecord rt))
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
      Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
      Notation value := (value (width:=width)).
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

      Definition idx_chara (tbl_v idx_v : value) : Prop :=
        match tbl_v, idx_v with
        | VList l, VDict d =>
            forall attr_v,
              Permutation
                (filter (fun r => match r with
                                  | VRecord rc => value_eqb (record_proj attr rc) attr_v
                                  | _ => false
                                  end) l)
                (bag_to_list match dict_lookup attr_v d with
                   | Some (VBag b) => b
                   | _ => nil
                   end)
        | _, _ => False
        end.

      Definition gallina_to_idx (tbl_v : value) : value :=
        match tbl_v with
        | VList l =>
            VDict (fold_right
                     (fun v acc => match v with
                                   | VRecord v =>
                                       dict_insert (record_proj attr v)
                                         (VBag (bag_insert (VRecord v)
                                                  (match dict_lookup (record_proj attr v) acc with
                                                   | Some (VBag b) => b
                                                   | _ => nil
                                                   end))) acc
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
          (P := fun a => type_of_value a (TDict (get_attr_type l attr) (TBag (TRecord l))))
          (g := fun b a =>
                  match a with
                  | VDict d =>
                      match b with
                      | VRecord l1 =>
                          VDict
                            (dict_insert
                               (record_proj attr l1)
                               (VBag
                                  match dict_lookup (record_proj attr l1) d with
                                  | Some (VBag l) => bag_insert b l
                                  | _ => [(b, 1)]
                                  end) d)
                      | _ => VUnit
                      end
                  | _ => VUnit
                  end).
        2:{ constructor; cbn; auto using NoDup_nil, SSorted_nil. }
        2:{ intros. invert_type_of_value_clear.
            apply_Forall_In. invert_type_of_value_clear.
            repeat rewrite_map_get_put_goal; try now use_is_NoDup.
            enough (type_of_value (VOption (dict_lookup (record_proj attr l2) l1)) (TOption (TBag (TRecord l)))).
            2:{ rewrite inb_true_iff in *.
                    lazymatch goal with
                      H: In _ (List.map fst _) |- _ =>
                        apply In_fst in H; destruct H end.
                    intuition idtac; destruct x0. eauto.
                    cbn in *; subst.
                    eapply dict_lookup_sound.
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
            1:{ do 2 f_equal.
                invert_type_of_value_clear; auto.
                rewrite_map_get_put_goal.
                invert_type_of_value_clear; auto. }
            1:{ invert_type_wf; apply dict_insert_sound.
                1: apply get_attr_type_ty_wf; auto.
                1: constructor; auto.
                1: constructor; auto.
                1:{ rewrite inb_true_iff in *.
                    lazymatch goal with
                      H: In _ (List.map fst _) |- _ =>
                        apply In_fst in H; destruct H end.
                    intuition idtac; destruct x0. eauto.
                    cbn in *; subst.
                    eapply record_proj_sound; eauto.
                    1: lazymatch goal with
                             H: context[Forall2] |- _ =>
                               apply Forall2_split in H;
                               rewrite Forall2_fst_eq in H
                           end;
                    intuition idtac; rewrite_l_to_r; auto.
                    erewrite NoDup_In_get_attr_type; eauto. }
                1:{ invert_type_of_value_clear; cbn.
                    1: repeat (constructor; cbn; auto using NoDup_nil, SSorted_nil).
                    rewrite_map_get_put_goal.
                    invert_type_of_value_clear.
                    constructor; auto using bag_insert_preserve_NoDup,
                      bag_insert_preserve_SSorted, bag_insert_preserve_pos.
                    rewrite Forall_forall; intros ? H_in.
                    apply bag_insert_incl in H_in; intuition idtac.
                    1: rewrite_l_to_r; constructor; auto.
                    1: apply_Forall_In. } } }
        1:{ induction l0; cbn; auto. invert_Forall. erewrite IHl0; auto.
            invert_type_of_value_clear. do 3 f_equal.
            repeat (case_match; auto). }
      Qed.

      Lemma value_eqb_iff_eq : forall (v v' : value),
          value_eqb v v' = true <-> v = v'.
      Proof.
        split; intros; subst; auto using value_eqb_eq, value_eqb_refl.
      Qed.

      Lemma value_compare_Eq_iff_eq : forall (v v' : value),
          value_compare v v' = Eq <-> v = v'.
      Proof.
        split; intros; subst; auto using value_compare_Eq_eq, value_compare_refl.
      Qed.

      Lemma dict_lookup_insert_diff : forall k k' (v : value) d,
          k <> k' -> dict_lookup k (dict_insert k' v d) = dict_lookup k d.
      Proof.
        intros; induction d; cbn.
        1:{ rewrite <- value_eqb_iff_eq, Bool.not_true_iff_false in *.
            rewrite_l_to_r; auto. }
        1:{ case_match; cbn; unfold value_ltb, value_eqb.
            case_match; cbn; unfold value_ltb, value_eqb;
              rewrite <- value_compare_Eq_iff_eq in *.
            1:{ rewrite value_compare_Eq_iff_eq in *; subst.
                rewrite <- value_compare_Eq_iff_eq in *.
                case_match; intuition auto. }
            all: case_match; intuition auto. }
      Qed.

      Lemma dict_lookup_insert_same : forall k (v : value) d,
          dict_lookup k (dict_insert k v d) = Some v.
      Proof.
        induction d; cbn; intros.
        1: rewrite value_eqb_refl; trivial.
        1:{ case_match. unfold value_ltb, value_eqb.
            case_match; cbn.
            1,2: rewrite value_eqb_refl; trivial.
            unfold value_eqb. rewrite_l_to_r. assumption. }
      Qed.

      Lemma bag_to_list_insert_Permutation : forall (v : value) b,
          Permutation (bag_to_list (bag_insert v b)) (v :: bag_to_list b).
      Proof.
        intros. pose proof (bag_to_list__bag_insert v0 b).
        repeat destruct_exists; destruct_and; subst.
        rewrite_l_to_r.
        eapply perm_trans.
        1: apply Permutation_sym, Permutation_middle.
        rewrite bag_to_list_app. auto.
      Qed.

      Lemma idx_wf__idx_chara : forall (t : type) (tbl_v idx_v : value),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value tbl_v t ->
          idx_wf tbl_v idx_v -> idx_chara tbl_v idx_v.
      Proof.
        unfold idx_wf, idx_chara.
        intros; subst; erewrite fiat2_gallina_to_idx; eauto.
        unfold is_tbl_ty, idx_wf, gallina_to_idx in *.
        repeat destruct_match_hyp; try discriminate.
        invert_type_of_value_clear. intros.
        lazymatch goal with
          H: Forall _ _ |- _ =>
            induction H
        end; cbn; auto.
        invert_type_of_value_clear.
        case_match.
        1:{ apply value_eqb_eq in E; subst.
            rewrite dict_lookup_insert_same.
            rewrite bag_to_list_insert_Permutation.
            apply perm_skip; auto. }
        1:{ rewrite dict_lookup_insert_diff; auto.
            rewrite <- value_eqb_iff_eq, Bool.not_true_iff_false in *;
              eauto using value_eqb_sym. }
      Qed.

      Lemma to_idx_wf : forall (v : value) (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          idx_wf v (interp_expr map.empty (map.put map.empty hole v) to_idx).
      Proof.
        intros; unfold idx_wf; auto.
      Qed.

      Notation eto_idx tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1 d :=
        (EFold d (EAtom (AEmptyDict None)) tup0 acc0
           (ETernop OInsert (EVar acc1) (EAccess (EVar tup1) attr0)
              (EBinop OBagInsert
                 (EOptMatch (EBinop OLookup (EVar acc2) (EAccess (EVar tup2) attr1))
                    (EAtom (AEmptyBag None)) x0 (EVar x1))
                 (EVar tup3)))).

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
          sem_eq (word:=word) Gstore Genv (idx_ty t)
            (EFold e (EAtom (AEmptyDict None)) tup0 acc0
           (ETernop OInsert (EVar acc0) (EAccess (EVar tup0) attr)
              (EBinop OBagInsert
                 (EOptMatch (EBinop OLookup (EVar acc0) (EAccess (EVar tup0) attr))
                    (EAtom (AEmptyBag None)) x0 (EVar x0))
                 (EVar tup0))))
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

      Instance dict_idx : IndexInterface2.index := IndexInterface2.mk hole to_idx idx_ty is_tbl_ty.

      Instance dict_idx_ok : IndexInterface2.ok dict_idx idx_wf :=
        IndexInterface2.Build_ok dict_idx idx_wf idx_ty_wf to_idx_ty to_idx_wf.

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

        Section eq_filter_to_lookup.
          Context (b : string).
          Context (tbl : string).

          Definition eq_filter_to_lookup_head (e : expr) :=
            (* filter (tbl[id_tag]) (fun row => row.attr == e') -->
           match (lookup idx e') with none => nil | some p => fst p ++ [snd p] *)
            match e with
            | EFilter LikeBag
                (EBagOf (EAccess (ELoc tbl0) (id_tag0)))
                x
                (EBinop OEq (EAccess (EVar x0) attr0) e') =>
                if (all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x, [x0]); (id_tag, [id_tag0])] &&
                      negb (free_immut_in x e'))%bool
                then EOptMatch (EBinop OLookup (EAccess (EAccess (ELoc tbl) aux_tag) idx_tag) e')
                       (EAtom (AEmptyBag None))
                       b (EVar b)
                else e
            | _ => e
            end.

          Lemma eq_filter_to_lookup_head_preserve_ty : forall tl t aux_tl (Gstore : tenv),
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              preserve_ty Gstore (eq_filter_to_lookup_head).
          Proof.
            clear H_NoDup.
            unfold preserve_ty, is_tbl_ty. intros.
            repeat destruct_match_hyp; try congruence.
            repeat destruct_subexpr. simpl.
            case_match; auto. repeat rewrite Bool.andb_true_r in *.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac. rewrite Bool.negb_true_iff, eqb_eq in *; subst.
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

          Lemma bag_insert_min : forall (v : value) l,
              ~ In v (List.map fst l) ->
              Forall (fun p =>
                        is_true (bag_entry_leb (v, 1) p)) l ->
              bag_insert v l = (v, 1) :: l.
          Proof.
            induction l; cbn; intros; auto.
            case_match; cbn in *; intuition idtac.
            rewrite <- value_eqb_iff_eq, value_eqb_sym in * |-.
            invert_Forall; unfold bag_entry_leb in *; cbn in *.
            do 2 (case_match; intuition auto).
            unfold value_eqb, value_leb, value_ltb, leb_from_compare in *.
            destruct_match_hyp; discriminate.
          Qed.

          Lemma filter_eq_nil__Forall_false : forall A l (P : A -> bool),
              filter P l = nil -> Forall (fun v => P v = false) l.
          Proof.
            induction l; cbn; auto.
            intros. destruct_match_hyp; try discriminate.
            constructor; auto.
          Qed.

          Lemma bag_to_list_to_bag : forall (b : list (value * nat)),
              NoDup (map fst b) ->
              StronglySorted (fun p p' => is_true (bag_entry_leb p p')) b ->
              Forall (fun p : value * nat => Nat.lt 0 (snd p)) b ->
              list_to_bag (bag_to_list b) = b.
          Proof.
            induction 3; cbn in *; auto.
            destruct x0. destruct n.
            1: lazymatch goal with
                 H: Nat.lt _ _ |- _ => inversion H end.
            cbn in *. invert_NoDup; invert_SSorted.
            induction n; cbn.
            1:{ rewrite IHForall; auto.
                apply bag_insert_min; auto. }
            1:{ rewrite IHn; cbn; auto using Nat.lt_0_succ.
                2: constructor; auto.
                unfold value_ltb, value_eqb.
                rewrite value_compare_refl; reflexivity. }
          Qed.

          Lemma eq_filter_to_lookup_head_preserve_sem : forall (Gstore : tenv) (store : locals) tl t aux_tl,
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              match map.get store tbl with
              | Some v => aux_wf_for_idx v
              | _ => False
              end ->
              preserve_sem Gstore store eq_filter_to_lookup_head.
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
            repeat destruct_subexpr. unfold eq_filter_to_lookup_head.
            simpl; case_match; auto.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            rewrite Bool.negb_true_iff, eqb_eq in *; subst. repeat clear_refl.
            cbn. unfold get_local. rewrite_l_to_r. unfold record_proj.
            repeat rewrite_l_to_r.
            unfold idx_wf in *.
            repeat (destruct_match_hyp; intuition idtac).
            lazymatch goal with
              H: forall _, _ |- context[dict_lookup ?v _] =>
                specialize (H v)
            end.
            repeat invert_type_of_clear. rewrite_map_get_put_hyp.
            lazymatch goal with
              H: type_of _ _ e2_2 _ |- _ =>
                apply not_free_immut_put_ty in H; auto
            end. invert_type_of_op. rewrite_l_to_r.
            repeat (do_injection; try clear_refl).
            assert (type_of_value (VOption (dict_lookup (interp_expr store env e2_2) l2)) (TOption (TBag (TRecord l1)))).
            1:{ apply_type_sound e2_2.
                eapply dict_lookup_sound; [ | | | eauto ];
                  eauto with fiat2_hints.
                1: constructor; eauto with fiat2_hints.
                1:{ constructor; auto. rewrite_l_to_r; do_injection.
                    unfold get_attr_type in *. rewrite_l_to_r. auto. } }
            rewrite filter_list_to_bag with
                  (P := (fun v0 =>
                           value_eqb
                             match
                               match map.get (map.put env x0 v0) x0 with
                               | Some v1 => v1
                               | None => VUnit
                               end
                             with
                             | VRecord l4 =>
                                 match access_record l4 attr with
                                 | Success v1 => v1
                                 | Failure _ => VUnit
                                 end
                             | _ => VUnit
                             end (interp_expr store (map.put env x0 v0) e2_2))).
            invert_type_of_value_clear.
            1:{ lazymatch goal with
                H: _ = dict_lookup _ _ |- _ =>
                  rewrite <- H in *
              end. cbn in *.
                lazymatch goal with
                  H: Permutation _ nil |- _ =>
                    apply Permutation_sym, Permutation_nil in H
                end.
                f_equal.
                rewrite Forall_false__filter; auto.
                rewrite Forall_forall.
                intros. invert_type_of_value_clear.
                lazymatch goal with
                  H: filter _ ?l = [], H': In _ ?l |- _ =>
                    apply filter_eq_nil__Forall_false in H;
                    rewrite Forall_forall in H; apply H in H' as H_x1
                end.
                apply_Forall_In.
                rewrite_map_get_put_goal. invert_type_of_value_clear.
                unfold record_proj in *.
                erewrite <- not_free_immut_put_sem; auto. }
            1:{ rewrite_map_get_put_goal.
                repeat invert_type_of_value_clear.
                lazymatch goal with
                  H: _ = dict_lookup _ _ |- _ =>
                    rewrite <- H in * end.
                f_equal.
                lazymatch goal with
                  H: Permutation _ _ |- _ =>
                    apply Permutation_list_to_bag_eq in H end.
                rewrite bag_to_list_to_bag in *; auto. subst.
                f_equal. apply In_filter_ext; intros.
                apply_Forall_In. invert_type_of_value_clear.
                rewrite_map_get_put_goal.
                erewrite <- not_free_immut_put_sem; auto. }
          Qed.
        End eq_filter_to_lookup.

        Section cons_to_insert.
          Definition cons_to_insert_head (e : expr) :=
            match e with
            | eto_idx tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1 (EBinop OCons e1 e2) =>
                if (all_eqb [(acc0, [acc1; acc2]); (tup0, [tup1; tup2; tup3]); (attr, [attr0; attr1]); (x0, [x1])] &&
                      all_neqb [acc0; tup0; x0] &&
                      negb (free_immut_in y e1))%bool
                then
                  ELet (eto_idx tup tup tup tup acc acc acc x x attr attr e2) y
                       (ETernop OInsert (EVar y)
                          (EAccess e1 attr)
                          (EBinop OBagInsert
                             (EOptMatch
                                (EBinop OLookup (EVar y) (EAccess e1 attr))
                                (EAtom (AEmptyBag None)) x (EVar x))
                             e1))
                else e
            | _ => e
            end.

          Lemma cons_to_insert_head_preserve_ty : forall (Gstore : tenv),
              preserve_ty Gstore cons_to_insert_head.
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

          Lemma fold_right_invariant : forall (A B : Type) (a : A) (l : list B) (f : B -> A -> A) (P : A -> Prop),
              P a -> (forall (a : A) (b : B), P a -> In b l -> P (f b a)) ->
              P (fold_right f a l).
          Proof.
            intros. assert(fold_right f a l = fold_right f a l /\ P (fold_right f a l)).
            { auto using In_fold_right_ext'. }
            intuition auto.
          Qed.

          Lemma cons_to_insert_head_preserve_sem : forall (Gstore : tenv) (store : locals),
              preserve_sem Gstore store cons_to_insert_head.
          Proof.
            unfold preserve_sem; intros. repeat destruct_subexpr.
            cbn [cons_to_insert_head]. repeat (case_match; auto; []).
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
            let pat := open_constr:(EFold _ _ v0 acc0 _) in
            erewrite sem_eq_eq with (t:=idx_ty (TList (TRecord tl))) (e1:=pat); [ | eauto .. ].
            2:{ apply fold_to_idx; eauto using incl_refl.
                1: use_is_NoDup.
                1: access_record_Success__is_tbl_ty.
                1: repeat econstructor; eauto. }
            erewrite substitute_preserve_sem with (Genv0:=map.put map.empty hole (TList (TRecord tl))); [ | | | | eauto .. ]; eauto using incl_refl with fiat2_hints.
            3: prove_sub_wf.
            2:{ eapply type_of_strengthen;
                [
                | apply map_incl_empty
                | apply map_incl_refl ].
                apply to_idx_ty; cbn; eauto with fiat2_hints;
                  access_record_Success__is_tbl_ty. }
            erewrite substitute_preserve_sem with (Genv0:=map.put map.empty hole (TList (TRecord tl))); [ | | | | eauto .. ]; eauto using incl_refl with fiat2_hints.
            3:{ prove_sub_wf.
                do_injection. repeat econstructor; eauto. }
            2:{ eapply type_of_strengthen;
                [
                | apply map_incl_empty
                | apply map_incl_refl ].
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
            rewrite_expr_value. f_equal.
            lazymatch goal with
              |- context[dict_lookup ?k ?d] =>
                enough (type_of_value (VDict d) (TDict (get_attr_type tl attr) (TBag (TRecord tl))))
            end.
            2:{ apply fold_right_invariant.
                1: constructor; auto using NoDup_nil, SSorted_nil.
                intros. apply_Forall_In. repeat invert_type_of_value_clear.
                apply dict_insert_sound.
                1: apply get_attr_type_ty_wf; eauto with fiat2_hints.
                1: constructor; eauto with fiat2_hints.
                1: constructor; auto.
                1:{ eapply record_proj_sound; eauto.
                    1: lazymatch goal with
                         H: context[Forall2] |- _ =>
                           apply Forall2_split in H;
                           rewrite Forall2_fst_eq in H
                       end;
                    intuition idtac; rewrite_r_to_l; auto.
                    1: lazymatch goal with
                         H: access_record _ _ = Success _ |- _ =>
                           apply access_record_sound in H;
                           let H' := fresh "H'" in
                           apply NoDup_In_get_attr_type in H as H'
                       end; subst; auto. }
                1:{ lazymatch goal with
                    |- context[dict_lookup ?k0 ?d] =>
                      enough (H_dict2: type_of_value (VDict d) (TDict (get_attr_type tl attr) (TBag (TRecord tl)))); [ | constructor; auto ];
                      eapply dict_lookup_sound with (k:=k0) in H_dict2
                  end.
                    2: apply get_attr_type_ty_wf; eauto with fiat2_hints.
                    2: constructor; eauto with fiat2_hints.
                    2:{ eapply record_proj_sound; eauto.
                        1: lazymatch goal with
                             H: context[Forall2] |- _ =>
                               apply Forall2_split in H;
                               rewrite Forall2_fst_eq in H
                           end;
                        intuition idtac; rewrite_r_to_l; auto.
                        1: lazymatch goal with
                             H: access_record _ _ = Success _ |- _ =>
                               apply access_record_sound in H;
                               let H' := fresh "H'" in
                               apply NoDup_In_get_attr_type in H as H'
                           end; subst; auto. }
                    repeat invert_type_of_value_clear; constructor.
                    all: try apply bag_insert_preserve_NoDup; auto using NoDup_nil.
                    all: try apply bag_insert_preserve_SSorted; auto using SSorted_nil.
                    all: try apply bag_insert_preserve_pos; auto.
                    all: rewrite Forall_forall; intros ? H_in;
                      apply bag_insert_incl in H_in; intuition idtac;
                      try lazymatch goal with
                          H: In _ nil |- _ =>
                            apply in_nil in H; intuition fail
                        end;
                      try (lazymatch goal with
                             H: ?x = _ |- context[?x] => rewrite H end;
                           constructor; auto);
                      apply_Forall_In. } }
            eapply dict_lookup_sound with (k:=record_proj attr l0) in H7.
            2: apply get_attr_type_ty_wf; eauto with fiat2_hints.
            2: constructor; eauto with fiat2_hints.
            2:{ eapply record_proj_sound; eauto.
                1: lazymatch goal with
                     H: context[Forall2] |- _ =>
                       apply Forall2_split in H;
                       rewrite Forall2_fst_eq in H
                   end;
                intuition idtac; rewrite_r_to_l; auto.
                1: lazymatch goal with
                     H: access_record _ _ = Success _ |- _ =>
                       apply access_record_sound in H;
                       let H' := fresh "H'" in
                       apply NoDup_In_get_attr_type in H as H'
                   end; subst; auto. }
            invert_type_of_value_clear; auto.
            rewrite_map_get_put_goal.
            invert_type_of_value_clear; auto.
          Qed.
        End cons_to_insert.

        Section use_idx.
          Context (tbl : string).
          Definition use_idx_head (e : expr) :=
            match e with
            | eto_idx tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1 (EAccess (ELoc tbl0) id_tag0) =>
                if (all_eqb [(acc0, [acc1; acc2]); (tup0, [tup1; tup2; tup3]); (attr, [attr0; attr1]); (x0, [x1]); (tbl, [tbl0]); (id_tag, [id_tag0])] &&
                      all_neqb [acc0; tup0; x0])%bool
                then EAccess (EAccess (ELoc tbl) aux_tag) idx_tag
                else e
            | _ => e
            end.

          Lemma use_idx_head_preserve_ty : forall tl t aux_tl (Gstore : tenv),
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              preserve_ty Gstore use_idx_head.
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
            f_equal; unfold idx_ty; f_equal.
            unfold get_attr_type.
            lazymatch goal with H: ?x = _ |- context[?x] => rewrite H end.
            reflexivity.
          Qed.

          Lemma use_idx_head_preserve_sem : forall (Gstore : tenv) (store : locals) tl t aux_tl,
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              match map.get store tbl with
              | Some v => aux_wf_for_idx v
              | _ => False
              end ->
              preserve_sem Gstore store use_idx_head.
          Proof.
            unfold preserve_sem, aux_wf_for_idx, idx_wf; intros.
            unfold is_tbl_ty, idx_ty in *.
            apply_locals_wf store.
            repeat (destruct_match_hyp; try discriminate; intuition idtac; []).
            invert_type_of_value_clear.
            pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H16 E1 H2).
            repeat destruct_subexpr. unfold eq_filter_to_lookup_head.
            cbn [use_idx_head]; repeat (case_match; auto; []). cbn [all_eqb all_eqb' all_neqb all_neqb'] in * |-.
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

        Lemma eq_filter_to_lookup_head_sound : forall b aux_ty aux_wf,
            aux_ty_for_idx aux_ty ->
            (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
            expr_aug_transf_sound aux_ty aux_wf (eq_filter_to_lookup_head b).
        Proof.
          unfold aux_ty_for_idx, expr_aug_transf_sound; intros.
          invert_tenv_wf_with_globals.
          specialize (H tbl_ty). repeat destruct_match_hyp; intuition idtac.
          1: eapply eq_filter_to_lookup_head_preserve_ty; eauto.
          1: eapply eq_filter_to_lookup_head_preserve_sem; eauto.
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

        Lemma cons_to_insert_head_sound : expr_transf_sound (locals:=locals) cons_to_insert_head.
        Proof.
          unfold expr_transf_sound; intros.
          intuition idtac.
          1: eapply cons_to_insert_head_preserve_ty; eauto.
          1: eapply cons_to_insert_head_preserve_sem; [ | | eauto .. ]; auto.
        Qed.

        Lemma use_idx_head_sound : forall aux_ty aux_wf,
            aux_ty_for_idx aux_ty ->
            (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
            expr_aug_transf_sound aux_ty aux_wf use_idx_head.
        Proof.
          unfold aux_ty_for_idx, expr_aug_transf_sound; intros.
          invert_tenv_wf_with_globals.
          specialize (H tbl_ty). repeat destruct_match_hyp; intuition idtac.
          1: eapply use_idx_head_preserve_ty; eauto.
          1: eapply use_idx_head_preserve_sem; eauto.
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
    End WithMap.
  End WithVars.
End WithHole.
