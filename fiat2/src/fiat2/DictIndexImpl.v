Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute fiat2.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.

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
  (* Which structure the index demands of a backend.  Only the range rule
     below cares: it is sound at Ranged and nowhere else, and says so with a
     dk = Ranged premise.  Everything else here -- the point lookup, the
     insert, the keyed delete -- is written once and serves both kinds. *)
  Context (dk : dict_kind).

  Section WithVars.
    Context (tup acc x : string).
    Context (H_NoDup : is_NoDup_opaque [tup; acc; x]).

    Definition to_idx : expr :=
      let k := EAccess (EVar tup) attr in
      EFold (EVar hole) (EAtom (AEmptyDict dk None)) tup acc
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
      | TList (TRecord rt) => TDict dk (get_attr_type rt attr) (TBag (TRecord rt))
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
          (P := fun a => type_of_value a (TDict dk (get_attr_type l attr) (TBag (TRecord l))))
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
                    (* the kind shows up only in the premise, so name it:
                       the dictionary here is this index's own *)
                    eapply dict_lookup_sound with (dk := dk).
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

      Section DictDelete.
        Local Coercion is_true : bool >-> Sortclass.

        (* value_ltb_leb_trans, value_ltb__value_eqb_false,
           neq__value_eqb_false, dict_lookup_delete_diff,
           dict_delete_lt_head, dict_delete_insert_same and
           dict_delete_insert_diff are in Utils: they are about
           dict_insert and dict_delete, not about this index. *)

        Lemma gallina_to_idx_SSorted : forall l d,
            gallina_to_idx (VList l) = VDict d ->
            StronglySorted dict_entry_leb d.
        Proof.
          cbn [gallina_to_idx]; intros l d H. injection H as H; subst.
          induction l as [| r l IH]; cbn [fold_right].
          - constructor.
          - destruct r; try constructor.
            apply dict_insert_preserve_SSorted; assumption.
        Qed.

        (* Building the index of a table with the rows whose attr equals kv filtered out
           is the same as deleting kv from the index of the whole table *)
        Lemma gallina_to_idx_filter_neq : forall l rt kv,
            type_of_value (VList l) (TList (TRecord rt)) ->
            gallina_to_idx
              (VList (filter (fun r => negb (value_eqb (match r with
                                                        | VRecord rc => record_proj attr rc
                                                        | _ => VUnit
                                                        end) kv)) l)) =
              match gallina_to_idx (VList l) with
              | VDict d => VDict (dict_delete kv d)
              | v => v
              end.
        Proof.
          intros * H_ty. invert_type_of_value_clear.
          lazymatch goal with
            H: Forall _ l |- _ => induction H as [| r l H_r H_l IH]
          end; auto.
          invert_type_of_value_clear.
          pose proof (gallina_to_idx_SSorted l _ eq_refl) as H_sort.
          cbn [gallina_to_idx filter fold_right] in *.
          injection IH as IH.
          destruct (value_eqb (record_proj attr l0) kv) eqn:E; cbn [negb fold_right].
          - apply value_eqb_eq in E. rewrite E, dict_delete_insert_same; auto.
            f_equal; assumption.
          - assert (H_neq : record_proj attr l0 <> kv).
            { intro H_eq. rewrite H_eq, value_eqb_refl in E. discriminate. }
            rewrite IH, dict_lookup_delete_diff, dict_delete_insert_diff; auto.
        Qed.
      End DictDelete.

      Lemma bag_to_list_insert_Permutation : forall (v : value) b,
          Permutation (bag_to_list (bag_insert v b)) (v :: bag_to_list b).
      Proof.
        intros. pose proof (bag_to_list__bag_insert v b).
        repeat destruct_exists; destruct_and; subst.
        rewrite_l_to_r.
        eapply perm_trans.
        1: apply Permutation_sym, Permutation_middle.
        rewrite bag_to_list_app. auto.
      Qed.

      Section DictRange.
        Local Coercion is_true : bool >-> Sortclass.

        Lemma Permutation_filter_any : forall A (f : A -> bool) l l',
            Permutation l l' -> Permutation (filter f l) (filter f l').
        Proof.
          induction 1 as [ | a l l' H IH | a b l | l l' l'' H1 IH1 H2 IH2 ]; cbn; auto.
          - destruct (f a); auto.
          - destruct (f a), (f b); auto using perm_swap.
          - eapply perm_trans; eauto.
        Qed.

        Lemma dict_lookup_Some_In : forall (k v : value) d,
            dict_lookup k d = Some v -> In (k, v) d.
        Proof.
          induction d as [| [k' v'] d IH]; cbn; intros H; [ discriminate | ].
          destruct (value_eqb k k') eqn:E.
          - apply value_eqb_eq in E; subst. injection H as ->. left; reflexivity.
          - right; auto.
        Qed.

        (* a dictionary is its entry for a, if any, followed by the remaining entries *)
        Lemma dict_lookup_delete_Permutation : forall (a : value) d,
            Permutation d (match dict_lookup a d with
                           | Some v => (a, v) :: dict_delete a d
                           | None => dict_delete a d
                           end).
        Proof.
          induction d as [| [k v] d IH]; cbn; auto.
          destruct (value_eqb a k) eqn:E.
          - apply value_eqb_eq in E; subst. reflexivity.
          - destruct (dict_lookup a d); cbn.
            + eapply perm_trans; [ apply perm_skip, IH | apply perm_swap ].
            + apply perm_skip, IH.
        Qed.

        (* inserting into a sorted dictionary replaces or adds the entry for a *)
        Lemma dict_insert_Permutation : forall (a v : value) d,
            StronglySorted dict_entry_leb d ->
            Permutation (dict_insert a v d) ((a, v) :: dict_delete a d).
        Proof.
          induction d as [| [k w] d IH]; intros H_sort; cbn [dict_insert]; auto.
          destruct (value_ltb a k) eqn:E_lt.
          - rewrite dict_delete_lt_head; auto.
          - destruct (value_eqb a k) eqn:E_eq.
            + apply value_eqb_eq in E_eq; subst.
              cbn [dict_delete]. rewrite value_eqb_refl. reflexivity.
            + cbn [dict_delete]. rewrite E_eq. inversion H_sort; subst.
              eapply perm_trans; [ apply perm_skip, IH; auto | apply perm_swap ].
        Qed.

        (* the rows stored in the buckets of a dictionary index, in key order *)
        Definition range_rows (d : list (value * value)) : list value :=
          flat_map (fun p => match snd p with VBag b => bag_to_list b | _ => nil end) d.

        Lemma range_rows_Permutation : forall d d',
            Permutation d d' -> Permutation (range_rows d) (range_rows d').
        Proof.
          intros. unfold range_rows. apply Permutation_flat_map; auto.
        Qed.

        (* the buckets of a dictionary are the values of its entries *)
        Lemma range_rows_map_snd : forall d,
            range_rows d
            = flat_map (fun v => match v with VBag b => bag_to_list b | _ => nil end)
                (List.map snd d).
        Proof.
          unfold range_rows; induction d; cbn; congruence.
        Qed.

        Lemma gallina_to_idx_buckets : forall l d,
            gallina_to_idx (VList l) = VDict d ->
            Forall (fun p => exists b, snd p = VBag b) d.
        Proof.
          cbn [gallina_to_idx]; intros l d H. injection H as H; subst.
          induction l as [| r l IH]; cbn [fold_right]; auto.
          destruct r; try constructor.
          rewrite Forall_forall in *; intros p H_in.
          apply dict_insert_incl in H_in.
          destruct H_in as [ <- | H_in ]; [ eexists; reflexivity | eauto ].
        Qed.

        (* Selecting the rows whose attr passes a test on the KEY gives the rows in
           the buckets that same test selects from the index, up to order.

           Stated for an arbitrary key test rather than for a range, because the
           three range shapes -- both bounds, lower bound only, upper bound only --
           differ only in the test they produce, and dict_range is a key filter. *)
        Lemma gallina_to_idx_filter_key : forall (f : value -> bool) l,
            Forall (fun r => exists rc, r = VRecord rc) l ->
            forall d, gallina_to_idx (VList l) = VDict d ->
            Permutation
              (filter (fun r => match r with
                                | VRecord rc => f (record_proj attr rc)
                                | _ => false
                                end) l)
              (range_rows (filter (fun p => f (fst p)) d)).
        Proof.
          intros f l H_l. induction H_l as [| r l [rc ->] H_l IH]; intros d H_d.
          - cbn in H_d. injection H_d as <-. cbn. constructor.
          - cbn [gallina_to_idx fold_right] in H_d. injection H_d as <-.
            specialize (IH _ eq_refl).
            pose proof (gallina_to_idx_SSorted l _ eq_refl) as H_sort.
            pose proof (gallina_to_idx_buckets l _ eq_refl) as H_bags.
            set (D := fold_right _ nil l) in *.
            (* the new index is its entry for the row's key followed by the other entries *)
            eapply perm_trans;
              [ | apply range_rows_Permutation, Permutation_filter_any, Permutation_sym,
                  dict_insert_Permutation; exact H_sort ].
            (* and so is the old index *)
            pose proof (perm_trans IH (range_rows_Permutation _ _
                          (Permutation_filter_any _ _ _ _ (dict_lookup_delete_Permutation (record_proj attr rc) D)))) as H1.
            clear IH. revert H1.
            unfold range_rows. cbn [filter flat_map fst snd].
            destruct (dict_lookup (record_proj attr rc) D) as [ w | ] eqn:E_lk; intro H1.
            + apply dict_lookup_Some_In in E_lk.
              rewrite Forall_forall in H_bags. apply H_bags in E_lk as [ b H_b ]. cbn in H_b. subst w.
              cbn [filter flat_map fst snd] in *. revert H1.
              destruct (f (record_proj attr rc)) eqn:E_in; intro H1; [ | exact H1 ].
              eapply perm_trans; [ apply perm_skip, H1 | ].
              apply Permutation_sym. cbn [flat_map snd]. rewrite app_comm_cons.
              apply Permutation_app_tail, bag_to_list_insert_Permutation.
            + revert H1.
              destruct (f (record_proj attr rc)) eqn:E_in; intro H1; [ | exact H1 ].
              cbn. apply perm_skip, H1.
        Qed.

        (* The range instance: a key is kept when it satisfies every bound present *)
        Corollary gallina_to_idx_range : forall lo hi l,
            Forall (fun r => exists rc, r = VRecord rc) l ->
            forall d, gallina_to_idx (VList l) = VDict d ->
            Permutation
              (filter (fun r => match r with
                                | VRecord rc => in_key_range lo hi (record_proj attr rc)
                                | _ => false
                                end) l)
              (range_rows (dict_range lo hi d)).
        Proof.
          unfold dict_range; intros; apply gallina_to_idx_filter_key; auto.
        Qed.
      End DictRange.

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

      (* The kind is a pattern variable, not this section's dk: a pattern may
         only mention constructors.  Every rule that matches a rebuild of the
         index therefore has to CHECK the kind it finds against its own, or it
         would rewrite a dictionary of one kind into a read of a member of the
         other. *)
      Notation eto_idx dk0 tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1 d :=
        (EFold d (EAtom (AEmptyDict dk0 None)) tup0 acc0
           (ETernop OInsert (EVar acc1) (EAccess (EVar tup1) attr0)
              (EBinop OBagInsert
                 (EOptMatch (EBinop OLookup (EVar acc2) (EAccess (EVar tup2) attr1))
                    (EAtom (AEmptyBag None)) x0 (EVar x1))
                 (EVar tup3)))).

      (* Turn the rules' kind test into an equation, and orient it so the
         PATTERN's kind disappears.  Rewriting the other way would eliminate
         the section variable dk and with it every definition mentioning it. *)
      Ltac use_dict_kind_beq :=
        repeat lazymatch goal with
            H: dict_kind_beq dk ?d = true |- _ =>
              apply dict_kind_beq_eq in H; rewrite <- H in *; clear H
          end.

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
            (EFold e (EAtom (AEmptyDict dk None)) tup0 acc0
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

      Instance dict_idx : IndexInterface.index := IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

      Instance dict_idx_ok : IndexInterface.ok dict_idx idx_wf :=
        IndexInterface.Build_ok dict_idx idx_wf idx_ty_wf to_idx_ty to_idx_wf.

      Section WithTags.
        Context (id_tag aux_tag idx_tag: string).

        Notation aux_ty_for_idx := (aux_ty_for_idx id_tag aux_tag idx_tag idx_ty).
        Notation aux_wf_for_idx := (aux_wf_for_idx id_tag aux_tag idx_tag idx_wf).

        Section eq_filter_to_lookup.
          Context (b : string).
          Context (tbl : string).

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

          Definition eq_filter_to_lookup_head (e : expr) :=
            (* [row <- tbl[id_tag], check(row.attr == e'), ret row] (as a bag) -->
               match (lookup idx e') with none => emptybag | some b => b *)
            match e with
            | flatmap_filter_bag
                (EBagOf (EAccess (ELoc tbl0) id_tag0))
                x0 (EBinop OEq (EAccess (EVar x1) attr0) e') x2 _ _ =>
                if (all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x0, [x1; x2]); (id_tag, [id_tag0])] &&
                      negb (free_immut_in x0 e'))%bool
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
              preserve_ty Gstore eq_filter_to_lookup_head.
          Proof.
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
            cbv beta iota; case_match; auto.
            cbn [all_eqb all_eqb' andb] in *.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            rewrite Bool.negb_true_iff, eqb_eq in *; subst. repeat clear_refl.
            rewrite interp_flatmap_filter_bag.
            cbn. unfold get_local. rewrite_l_to_r. unfold record_proj.
            repeat rewrite_l_to_r.
            unfold idx_wf in *.
            repeat (destruct_match_hyp; intuition idtac).
            cbn [list_to_bag]. rewrite list_to_bag_filter_list_to_bag.
            lazymatch goal with
              H: forall _, _ |- context[dict_lookup ?v _] =>
                specialize (H v)
            end.
            repeat invert_type_of_clear. rewrite_map_get_put_hyp.
            lazymatch goal with
              H: type_of _ _ e2_1_2 _ |- _ =>
                apply not_free_immut_put_ty in H; auto
            end. invert_type_of_op. rewrite_l_to_r.
            repeat (do_injection; try clear_refl).
            assert (type_of_value (VOption (dict_lookup (interp_expr store env e2_1_2) l2)) (TOption (TBag (TRecord l1)))).
            1:{ apply_type_sound e2_1_2.
                eapply dict_lookup_sound with (dk := dk); [ | | | eauto ];
                  eauto with fiat2_hints.
                1: constructor; eauto with fiat2_hints.
                1:{ constructor; auto. rewrite_l_to_r; do_injection.
                    unfold get_attr_type in *. rewrite_l_to_r. auto. } }
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

        Section range_filter_to_dict_range.
          Context (rv : string).
          Context (tbl : string).

          (* The bound EXPRESSIONS a range filter on the row variable x asks for,
             as option-typed expressions, or None when the filter is not a range
             on attr.

             The three shapes are the three ways ordered-map code writes a range:
             subMap/subSet name both bounds, tailMap/tailSet only the lower one,
             headMap/headSet only the upper one.  An absent bound is ANone and not
             a sentinel, because a TInt key has no infinity to name -- which is
             why the bounds of ODictRange are options in the first place. *)
          Definition range_bounds (rx : string) (p : expr) : option (expr * expr) :=
            match p with
            (* !(row.attr < lo) && row.attr < hi *)
            | EBinop OAnd (EUnop ONot (EBinop OLess (EAccess (EVar x1) attr0) lo))
                          (EBinop OLess (EAccess (EVar x2) attr1) hi) =>
                if all_eqb [(attr, [attr0; attr1]); (rx, [x1; x2])]
                then Some (EUnop OSome lo, EUnop OSome hi)
                else None
            (* !(row.attr < lo) *)
            | EUnop ONot (EBinop OLess (EAccess (EVar x1) attr0) lo) =>
                if all_eqb [(attr, [attr0]); (rx, [x1])]
                then Some (EUnop OSome lo, EAtom (ANone (Some TInt)))
                else None
            (* row.attr < hi *)
            | EBinop OLess (EAccess (EVar x1) attr0) hi =>
                if all_eqb [(attr, [attr0]); (rx, [x1])]
                then Some (EAtom (ANone (Some TInt)), EUnop OSome hi)
                else None
            | _ => None
            end.

          Definition range_filter_to_dict_range_head (e : expr) :=
            (* [row <- tbl[id_tag], check(a range on row.attr), ret row] (as a bag)
               --> the concatenated buckets of range(idx, lo, hi) *)
            match e with
            | flatmap_filter_bag
                (EBagOf (EAccess (ELoc tbl0) id_tag0)) x0 p x3 _ _ =>
                match range_bounds x0 p with
                | Some (lo, hi) =>
                    (* The kind is one of the rule's own guards.  ODictRange is the
                       only operator whose typing pins the kind, so this is where
                       the capability the kind records bites: on an Unranged index
                       the rule is the identity and the range query is left as the
                       scan it was. *)
                    if (is_ranged dk &&
                          all_eqb [(tbl, [tbl0]); (x0, [x3]); (id_tag, [id_tag0])] &&
                          negb (free_immut_in x0 lo) && negb (free_immut_in x0 hi))%bool
                    then EFlatmap LikeBag
                           (EUnop ODictValues
                              (ETernop ODictRange (EAccess (EAccess (ELoc tbl) aux_tag) idx_tag) lo hi))
                           rv (EVar rv)
                    else e
                | None => e
                end
            | _ => e
            end.

          (* Flattening the values of a dictionary collects the rows of its buckets *)
          Lemma interp_flatmap_dict_values : forall (store env : locals) d l,
              interp_expr store env d = VDict l ->
              interp_expr store env (EFlatmap LikeBag (EUnop ODictValues d) rv (EVar rv))
              = VBag (list_to_bag (range_rows l)).
          Proof.
            intros * H_d. cbn [interp_expr interp_unop]. rewrite H_d.
            erewrite In_flat_map_ext.
            2:{ intros v _. cbn [interp_expr]. unfold get_local.
                rewrite map.get_put_same. reflexivity. }
            f_equal. apply Permutation_list_to_bag_eq.
            rewrite range_rows_map_snd.
            apply Permutation_flat_map; auto using list_to_bag_to_list_Permutation.
          Qed.

          (* A range filter's bounds are integer OPTIONS, and the attribute it tests
             is an integer.  The second half is not a design choice: OLess is the
             language's only order test and it is int-typed, so a range query is
             int-keyed while a point lookup is key-generic. *)
          Lemma range_bounds_ty : forall rx p lo hi (Gstore Genv : tenv) rt,
              range_bounds rx p = Some (lo, hi) ->
              type_of Gstore (map.put Genv rx (TRecord rt)) p TBool ->
              access_record rt attr = Success TInt /\
                type_of Gstore (map.put Genv rx (TRecord rt)) lo (TOption TInt) /\
                type_of Gstore (map.put Genv rx (TRecord rt)) hi (TOption TInt).
          Proof.
            unfold range_bounds; intros * H_b H_ty.
            repeat (destruct_match_hyp; try discriminate).
            all: injection H_b as <- <-.
            all: cbn [all_eqb all_eqb' andb] in *;
              repeat rewrite Bool.andb_true_r in *;
              repeat rewrite Bool.andb_true_iff in *;
              repeat lazymatch goal with H: _ /\ _ |- _ => destruct H end;
              rewrite ?eqb_eq in *; subst.
            all: repeat invert_type_of_clear; repeat invert_type_of_op_clear;
              repeat rewrite_map_get_put_hyp; repeat (clear_refl; repeat do_injection2).
            (* the row's type under the binder is the table's row type *)
            all: repeat lazymatch goal with
                 | H: Some _ = Some _ |- _ => injection H as H
                 | H: TRecord _ = TRecord _ |- _ => injection H as H
                 end; subst.
            all: repeat split; try eassumption; repeat econstructor; eauto.
          Qed.

          (* The row's indexed attribute is the integer the bounds bound *)
          Lemma attr_is_int : forall rt rc,
              type_of_value (VRecord rc) (TRecord rt) ->
              access_record rt attr = Success TInt ->
              exists k, record_proj (width := width) attr rc = VInt k.
          Proof.
            intros * H_rc H_attr.
            assert (H_v : type_of_value (record_proj (width := width) attr rc) TInt).
            1:{ invert_type_of_value_clear.
                eapply record_proj_sound.
                2: eassumption.
                2: eauto using access_record_sound.
                (* NoDup is known of the TYPE list; the Forall2 moves it to the
                   value list, which is what record_proj_sound asks for *)
                lazymatch goal with
                  H: context[Forall2] |- _ =>
                    apply Forall2_split in H; rewrite Forall2_fst_eq in H
                end.
                intuition idtac; rewrite_l_to_r; auto. }
            inversion H_v; eauto.
          Qed.

          (* A well-typed integer expression evaluates to an integer.  Stated
             separately so that range_bounds_sem can APPLY it, rather than let a
             proof search loose on its own goal: type_sound's side conditions
             are hypotheses here, so this costs one application and no search. *)
          Lemma bound_is_int : forall (Gstore Genv : tenv) (store env : locals) b,
              type_of Gstore Genv b TInt ->
              tenv_wf Gstore -> tenv_wf Genv ->
              locals_wf Gstore store -> locals_wf Genv env ->
              exists n, interp_expr store env b = VInt n.
          Proof.
            intros * H_ty ? ? ? ?.
            eapply type_sound in H_ty; eauto.
            inversion H_ty; eauto.
          Qed.

          (* And a range filter MEANS the key test ODictRange applies: the row
             passes exactly when its attribute satisfies every bound present. *)
          Lemma range_bounds_sem : forall rx p lo hi (Gstore Genv : tenv) rt
                                          (store env : locals) rc,
              tenv_wf Gstore -> tenv_wf (map.put Genv rx (TRecord rt)) ->
              range_bounds rx p = Some (lo, hi) ->
              free_immut_in rx lo = false -> free_immut_in rx hi = false ->
              type_of Gstore (map.put Genv rx (TRecord rt)) p TBool ->
              locals_wf Gstore store ->
              locals_wf (map.put Genv rx (TRecord rt)) (map.put env rx (VRecord rc)) ->
              type_of_value (VRecord rc) (TRecord rt) ->
              interp_expr store (map.put env rx (VRecord rc)) p
              = VBool (in_key_range
                         (interp_expr store env lo)
                         (interp_expr store env hi)
                         (record_proj (width := width) attr rc)).
          Proof.
            intros * H_Gs H_Ge H_b H_flo H_fhi H_ty H_st H_en H_rc.
            (* The bounds do not read the row, so they may be read in the
               environment the caller has.  Aligning the two environments here
               rather than at the use site keeps the rewrite's side conditions
               next to the hypotheses that discharge them. *)
            rewrite (not_free_immut_put_sem lo rx store env (VRecord rc) H_flo).
            rewrite (not_free_immut_put_sem hi rx store env (VRecord rc) H_fhi).
            pose proof (range_bounds_ty _ _ _ _ _ _ _ H_b H_ty) as [ H_attr _ ].
            destruct (attr_is_int _ _ H_rc H_attr) as [ k H_k ].
            unfold range_bounds in H_b.
            repeat (destruct_match_hyp; try discriminate).
            all: injection H_b as <- <-.
            all: cbn [all_eqb all_eqb' andb] in *;
              repeat rewrite Bool.andb_true_r in *;
              repeat rewrite Bool.andb_true_iff in *;
              repeat lazymatch goal with H: _ /\ _ |- _ => destruct H end;
              rewrite ?eqb_eq in *; subst.
            all: repeat invert_type_of_clear; repeat invert_type_of_op_clear;
              repeat rewrite_map_get_put_hyp; repeat (clear_refl; repeat do_injection2).
            (* Expose the row's attribute and each bound as the integers they are.
               The inversions above rename the typing context, so this step names
               no hypothesis: it reads the bound off the goal and discharges
               bound_is_int's premises by eassumption alone -- never by a search
               that could wander onto the goal itself. *)
            all: cbn -[record_proj value_ltb];
              unfold get_local; rewrite map.get_put_same;
              cbn -[record_proj value_ltb]; rewrite H_k.
            all: repeat match goal with
                 | H: type_of _ _ ?b TInt |- context[interp_expr ?st ?en ?b] =>
                     let n := fresh "n" in
                     let Hn := fresh "H_n" in
                     assert (Hn : exists m, interp_expr st en b = VInt m)
                       by (eapply bound_is_int; eassumption);
                     destruct Hn as [ n Hn ]; rewrite Hn; clear H
                 end.
            (* and then both sides are the same test on the same integers.
               in_key_range must be unfolded by hand: cbn refolds it, because an
               absent bound leaves an "andb _ true" with no constructor to match
               on.  That identity, and its mirror, are exactly what a one-sided
               range costs here. *)
            all: unfold in_key_range, above_lo, below_hi; cbv beta iota;
              rewrite ?Bool.andb_true_r, ?Bool.andb_true_l;
              reflexivity.
          Qed.

          Lemma range_filter_to_dict_range_head_preserve_ty : forall tl t aux_tl (Gstore : tenv),
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              preserve_ty Gstore range_filter_to_dict_range_head.
          Proof.
            unfold preserve_ty, is_tbl_ty. intros.
            repeat destruct_match_hyp; try congruence.
            repeat destruct_subexpr. simpl.
            destruct (range_bounds _ _) as [ [ lo hi ] | ] eqn:E_b; auto.
            case_match; auto. repeat rewrite Bool.andb_true_r in *.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            rewrite !Bool.negb_true_iff, eqb_eq in *; subst.
            repeat invert_type_of_clear. repeat invert_type_of_op_clear.
            repeat rewrite_map_get_put_hyp.
            repeat (clear_refl; repeat do_injection2).
            repeat (rewrite_l_to_r; do_injection2).
            (* Only now does the predicate's typing name the table's ROW type,
               which is what range_bounds_ty needs to read the bounds and the
               attribute off it.  The predicate itself is never inverted: it is a
               variable here, so repeat invert_type_of_clear leaves it alone. *)
            lazymatch goal with
              H: type_of _ (map.put _ _ (TRecord _)) _ TBool |- _ =>
                pose proof (range_bounds_ty _ _ _ _ _ _ _ E_b H) as [ H_attr [ H_lo H_hi ] ]
            end.
            unfold idx_ty, get_attr_type in *.
            lazymatch goal with
              H: is_ranged dk = true |- _ =>
                apply is_ranged_true in H; rewrite H in *
            end.
            rewrite H_attr in *.
            econstructor.
            (* the index's range, as a bag of buckets *)
            1:{ econstructor; [ constructor | ].
                econstructor;
                  [ constructor
                  | repeat econstructor; eauto
                  | eapply not_free_immut_put_ty; eauto .. ]. }
            (* the flatmap returns each bucket unchanged *)
            econstructor; rewrite_map_get_put_goal; auto.
          Qed.

          Lemma range_filter_to_dict_range_head_preserve_sem : forall (Gstore : tenv) (store : locals) tl t aux_tl,
              type_wf t -> is_tbl_ty t = true ->
              map.get Gstore tbl = Some (TRecord tl) ->
              access_record tl id_tag = Success t ->
              access_record tl aux_tag = Success (TRecord aux_tl) ->
              access_record aux_tl idx_tag = Success (idx_ty t) ->
              match map.get store tbl with
              | Some v => aux_wf_for_idx v
              | _ => False
              end ->
              preserve_sem Gstore store range_filter_to_dict_range_head.
          Proof.
            unfold preserve_sem, aux_wf_for_idx; intros.
            unfold is_tbl_ty, idx_ty in *.
            apply_locals_wf store.
            repeat (destruct_match_hyp; try discriminate; intuition idtac; []).
            invert_type_of_value_clear.
            pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H16 E1 H2).
            pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H16 E2 H3).
            invert_type_of_value_clear.
            pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H20 E4 H4).
            repeat destruct_subexpr. unfold range_filter_to_dict_range_head.
            destruct (range_bounds _ _) as [ [ lo hi ] | ] eqn:E_b; auto.
            cbv beta iota; case_match; auto.
            cbn [all_eqb all_eqb' andb] in *.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            rewrite !Bool.negb_true_iff, eqb_eq in *; subst. repeat clear_refl.
            rewrite interp_flatmap_filter_bag.
            (* the table is a list of records, and the index is built from it *)
            repeat invert_type_of_clear. repeat invert_type_of_op_clear.
            repeat rewrite_map_get_put_hyp.
            repeat (clear_refl; repeat do_injection2).
            invert_type_of_value_clear.
            unfold idx_wf in *.
            repeat (rewrite_l_to_r; do_injection2).
            lazymatch goal with H: type_of_value a (TList _) |- _ => inversion H; subst end.
            (* The left side collects the rows of the index's buckets for keys in
               range.  ODictRange's scrutinee has to be a literal VDict before the
               match will reduce, so the index's own equation is used here and the
               gallina_to_idx reading is taken afterwards. *)
            erewrite interp_flatmap_dict_values;
              [ | cbn [interp_expr interp_ternop]; unfold get_local; rewrite E;
                  unfold record_proj; rewrite E2, E4;
                  lazymatch goal with
                    H: VDict _ = interp_expr _ _ to_idx |- _ => rewrite <- H
                  end; reflexivity ].
            lazymatch goal with H: VDict _ = interp_expr _ _ to_idx |- _ =>
              erewrite fiat2_gallina_to_idx in H; eauto end.
            (* the right side filters the table's rows *)
            cbn [interp_expr]. unfold get_local. rewrite E. unfold record_proj. rewrite E1.
            rewrite list_to_bag_filter_list_to_bag.
            f_equal. apply Permutation_list_to_bag_eq, Permutation_sym.
            erewrite In_filter_ext; [ apply gallina_to_idx_range | ].
            (* These three select hypotheses by SHAPE rather than by the names the
               inversions happened to give them: this proof generates them in a
               different order than the one-shape rule did. *)
            - rewrite Forall_forall in *; intros r H_in.
              match goal with
              | H: forall _, In _ _ -> _ |- _ => apply H in H_in
              end.
              inversion H_in; eauto.
            - lazymatch goal with H: VDict _ = _ |- _ => rewrite H; reflexivity end.
            - (* both filters test the same bounds on the row's integer attribute *)
              intros r H_in.
              match goal with
              | H: Forall _ _ |- _ => rewrite Forall_forall in H; apply H in H_in
              end.
              inversion H_in; subst.
              (* The bracket keeps eauto on range_bounds_sem's side conditions.
                 Letting it see the main goal is what made this proof diverge. *)
              (* Gstore is pinned: left to eauto, "tenv_wf ?Gstore" is discharged
                 with the ENV's well-formedness, which instantiates the store
                 context wrongly and leaves the rest unprovable. *)
              erewrite range_bounds_sem with (Gstore := Gstore) (Genv := Genv);
                [ reflexivity | eauto using locals_wf_step with fiat2_hints .. ].
          Qed.
        End range_filter_to_dict_range.

        Section cons_to_insert.
          Context (y : string).
          Definition cons_to_insert_head (e : expr) :=
            match e with
            | eto_idx dk0 tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1 (EBinop OCons e1 e2) =>
                if (dict_kind_beq dk dk0 &&
                      all_eqb [(acc0, [acc1; acc2]); (tup0, [tup1; tup2; tup3]); (attr, [attr0; attr1]); (x0, [x1])] &&
                      all_neqb [acc0; tup0; x0] &&
                      negb (free_immut_in y e1))%bool
                then
                  ELet (eto_idx dk tup tup tup tup acc acc acc x x attr attr e2) y
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
            use_dict_kind_beq.
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
            use_dict_kind_beq.
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
                enough (type_of_value (VDict d) (TDict dk (get_attr_type tl attr) (TBag (TRecord tl))))
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
                      enough (H_dict2: type_of_value (VDict d) (TDict dk (get_attr_type tl attr) (TBag (TRecord tl)))); [ | constructor; auto ];
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

        Section filter_to_delete.
          Definition filter_neq_to_delete_head (e : expr) :=
            (* the index rebuilt from [y <- e', check(!(y.attr == k)), ret y] -->
               delete k from the index rebuilt from e' *)
            match e with
            | eto_idx dk0 tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1
                (flatmap_filter_list e' y (EUnop ONot (EBinop OEq (EAccess (EVar y0) attr2) k)) y1 _ _) =>
                if (dict_kind_beq dk dk0 &&
                      all_eqb [(acc0, [acc1; acc2]); (tup0, [tup1; tup2; tup3]); (attr, [attr0; attr1; attr2]); (x0, [x1]); (y, [y0; y1])] &&
                      all_neqb [acc0; tup0; x0] &&
                      negb (free_immut_in y k))%bool
                then EBinop ODelete (eto_idx dk tup tup tup tup acc acc acc x x attr attr e') k
                else e
            | _ => e
            end.
          Lemma filter_neq_to_delete_head_preserve_ty : forall (Gstore : tenv),
              preserve_ty Gstore filter_neq_to_delete_head.
          Proof.
            unfold preserve_ty; intros. repeat destruct_subexpr.
            cbn. repeat (case_match; auto).
            rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition auto.
            use_dict_kind_beq.
            rewrite eqb_eq, eqb_neq in *; subst. repeat invert_type_of_clear.
            repeat rewrite_map_get_put_hyp.
            repeat (try clear_refl; repeat do_injection).
            repeat invert_type_of_op_clear.
            repeat (rewrite_l_to_r; do_injection).
            econstructor; [ constructor | | eapply not_free_immut_put_ty; eauto ].
            repeat (econstructor; eauto);
              repeat rewrite_map_get_put_goal; auto;
              try use_is_NoDup.
          Qed.

          Lemma filter_neq_to_delete_head_preserve_sem : forall (Gstore : tenv) (store : locals),
              preserve_sem Gstore store filter_neq_to_delete_head.
          Proof.
            unfold preserve_sem; intros. repeat destruct_subexpr.
            cbn [filter_neq_to_delete_head]. repeat (case_match; auto; []).
            cbn in * |-.
            rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in *; intuition idtac.
            use_dict_kind_beq.
            rewrite eqb_eq, eqb_neq in *; subst. repeat invert_type_of_clear.
            repeat rewrite_map_get_put_hyp.
            repeat (try clear_refl; repeat do_injection).
            repeat invert_type_of_op_clear.
            repeat (rewrite_l_to_r; do_injection).
            enough (E_Binop: forall o e1 e2, interp_expr store env (EBinop o e1 e2) = interp_binop o (interp_expr store env e1) (interp_expr store env e2)); auto.
            rewrite E_Binop.
            let pat := open_constr:(EFold e1_1 _ _ _ _) in
            erewrite sem_eq_eq with (t:=idx_ty (TList (TRecord tl))) (e1:=pat); [ | eauto .. ].
            2:{ apply fold_to_idx; eauto using incl_refl.
                1: use_is_NoDup.
                1: access_record_Success__is_tbl_ty. }
            let pat := open_constr:(EFold (EFlatmap _ _ _ _) _ _ _ _) in
            erewrite sem_eq_eq with (t:=idx_ty (TList (TRecord tl))) (e1:=pat); [ | eauto .. ].
            2:{ apply fold_to_idx; eauto using incl_refl.
                1: use_is_NoDup.
                1: access_record_Success__is_tbl_ty.
                1: repeat econstructor; eauto.
                all: rewrite_map_get_put_goal; reflexivity. }
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
                do_injection. repeat econstructor; eauto.
                all: rewrite_map_get_put_goal; reflexivity. }
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
              [ | | | | cbn [make_sub_env]; rewrite map.get_put_same; reflexivity ];
              [ | | | eapply type_sound with (Gstore:=Gstore) (Genv:=Genv);
                      [ repeat econstructor; eauto; try (rewrite_map_get_put_goal; reflexivity) | .. ];
                      eauto with fiat2_hints ];
              eauto with fiat2_hints;
              [ | access_record_Success__is_tbl_ty ].
            apply_type_sound e1_1.
            lazymatch goal with
              H: type_of_value (interp_expr _ _ e1_1) _ |- _ =>
                pose proof H as H_l; invert_type_of_value_clear
            end.
            rewrite interp_flatmap_filter_list. rewrite_expr_value. cbv beta iota.
            erewrite In_filter_ext with
              (g := fun r => negb (value_eqb (match r with
                                              | VRecord rc => record_proj attr rc
                                              | _ => VUnit
                                              end) (interp_expr store env e1_2_1_2))).
            2:{ intros. cbn [interp_expr interp_unop interp_binop].
                unfold get_local; rewrite map.get_put_same.
                erewrite <- not_free_immut_put_sem; auto. }
            rewrite gallina_to_idx_filter_neq with (rt:=tl); auto.
          Qed.
        End filter_to_delete.

        Section use_idx.
          Context (tbl : string).
          Definition use_idx_head (e : expr) :=
            match e with
            | eto_idx dk0 tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1 (EAccess (ELoc tbl0) id_tag0) =>
                if (dict_kind_beq dk dk0 &&
                      all_eqb [(acc0, [acc1; acc2]); (tup0, [tup1; tup2; tup3]); (attr, [attr0; attr1]); (x0, [x1]); (tbl, [tbl0]); (id_tag, [id_tag0])] &&
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
            use_dict_kind_beq.
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
            (* the kind matches on both sides; only the key type needs work *)
            f_equal; unfold idx_ty; f_equal; try reflexivity.
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
            repeat destruct_subexpr.
            cbn [use_idx_head]; repeat (case_match; auto; []). cbn [all_eqb all_eqb' all_neqb all_neqb'] in * |-.
            repeat rewrite Bool.andb_true_iff in *; intuition idtac.
            use_dict_kind_beq.
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

        Lemma eq_filter_to_lookup_head_sound : forall b is_tbl_ty' aux_ty aux_wf,
            aux_ty_for_idx aux_ty ->
            (forall t, is_tbl_ty' t = true -> is_tbl_ty t = true) ->
            (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
            expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf (eq_filter_to_lookup_head b).
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

        Lemma range_filter_to_dict_range_head_sound : forall rv is_tbl_ty' aux_ty aux_wf,
            aux_ty_for_idx aux_ty ->
            (forall t, is_tbl_ty' t = true -> is_tbl_ty t = true) ->
            (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
            expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf (range_filter_to_dict_range_head rv).
        Proof.
          unfold aux_ty_for_idx, expr_aug_transf_sound; intros.
          invert_tenv_wf_with_globals.
          specialize (H tbl_ty). repeat destruct_match_hyp; intuition idtac.
          1: eapply range_filter_to_dict_range_head_preserve_ty; eauto.
          1: eapply range_filter_to_dict_range_head_preserve_sem; eauto.
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

        Lemma use_idx_head_sound : forall is_tbl_ty' aux_ty aux_wf,
            aux_ty_for_idx aux_ty ->
            (forall t, is_tbl_ty' t = true -> is_tbl_ty t = true) ->
            (forall (v : value), aux_wf v -> aux_wf_for_idx v) ->
            expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf use_idx_head.
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

      Lemma cons_to_insert_head_sound : forall y,
          expr_transf_sound (locals:=locals) (cons_to_insert_head y).
      Proof.
        unfold expr_transf_sound; intros.
        intuition idtac.
        1: eapply cons_to_insert_head_preserve_ty; eauto.
        1: eapply cons_to_insert_head_preserve_sem; [ | | eauto .. ]; auto.
      Qed.

      Lemma filter_neq_to_delete_head_sound :
          expr_transf_sound (locals:=locals) filter_neq_to_delete_head.
      Proof.
        unfold expr_transf_sound; intros.
        intuition idtac.
        1: eapply filter_neq_to_delete_head_preserve_ty; eauto.
        1: eapply filter_neq_to_delete_head_preserve_sem; [ | | eauto .. ]; auto.
      Qed.
    End WithMap.
  End WithVars.
End WithHole.

Lemma use_idx_head_sound2 : forall (hole attr : string) (dk : dict_kind),
       forall tup acc x : string,
       forall tenv : map.map string type,
       map.ok tenv ->
       forall (width : Z) (word : Interface.word width),
       word.ok word ->
       forall locals : map.map string (value (word:=word)),
       map.ok locals ->
       forall (id_tag aux_tag idx_tag : string) (is_tbl_ty' : type -> bool) (aux_ty : type -> type) (aux_wf : value -> Prop),
         (forall v : (value (word:=word)),
             aux_wf v -> aux_wf_for_idx id_tag aux_tag idx_tag (idx_wf hole attr dk tup acc x) v) -> aux_ty_for_idx id_tag aux_tag idx_tag (idx_ty attr dk) aux_ty ->
       (forall t : type, is_tbl_ty' t = true -> DictIndexImpl.is_tbl_ty attr t = true) ->
       is_NoDup_opaque [tup; acc; x] ->
       expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf (use_idx_head attr dk id_tag aux_tag idx_tag).
Proof.
  intros; eapply use_idx_head_sound; eauto.
Qed.

Lemma eq_filter_to_lookup_head_sound2 : forall (hole attr : string) (dk : dict_kind),
       forall tup acc x : string,
       forall tenv : map.map string type,
       map.ok tenv ->
       forall (width : Z) (word : Interface.word width),
       word.ok word ->
       forall locals : map.map string (value (word:=word)),
       map.ok locals ->
       forall (id_tag aux_tag idx_tag b : string) (is_tbl_ty' : type -> bool) (aux_ty : type -> type) (aux_wf : value -> Prop),
       aux_ty_for_idx id_tag aux_tag idx_tag (idx_ty attr dk) aux_ty ->
       (forall t : type, is_tbl_ty' t = true -> DictIndexImpl.is_tbl_ty attr t = true) ->
       (forall v : (value (word:=word)), aux_wf v -> aux_wf_for_idx id_tag aux_tag idx_tag (idx_wf hole attr dk tup acc x) v) ->
       is_NoDup_opaque [tup; acc; x] ->
       expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf (eq_filter_to_lookup_head attr id_tag aux_tag idx_tag b).
Proof.
  intros; eapply eq_filter_to_lookup_head_sound; eauto.
Qed.

Lemma range_filter_to_dict_range_head_sound2 : forall (hole attr : string) (dk : dict_kind),
       forall tup acc x : string,
       forall tenv : map.map string type,
       map.ok tenv ->
       forall (width : Z) (word : Interface.word width),
       word.ok word ->
       forall locals : map.map string (value (word:=word)),
       map.ok locals ->
       forall (id_tag aux_tag idx_tag rv : string) (is_tbl_ty' : type -> bool) (aux_ty : type -> type) (aux_wf : value -> Prop),
       aux_ty_for_idx id_tag aux_tag idx_tag (idx_ty attr dk) aux_ty ->
       (forall t : type, is_tbl_ty' t = true -> DictIndexImpl.is_tbl_ty attr t = true) ->
       (forall v : (value (word:=word)), aux_wf v -> aux_wf_for_idx id_tag aux_tag idx_tag (idx_wf hole attr dk tup acc x) v) ->
       is_NoDup_opaque [tup; acc; x] ->
       expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf (range_filter_to_dict_range_head attr dk id_tag aux_tag idx_tag rv).
Proof.
  intros; eapply range_filter_to_dict_range_head_sound; eauto.
Qed.

#[export] Hint Resolve use_idx_head_sound2 : transf_hints.
#[export] Hint Resolve cons_to_insert_head_sound : transf_hints.
#[export] Hint Resolve filter_neq_to_delete_head_sound : transf_hints.
#[export] Hint Resolve eq_filter_to_lookup_head_sound2 : transf_hints.
#[export] Hint Resolve range_filter_to_dict_range_head_sound2 : transf_hints.

#[export] Hint Extern 5 (type_of _ _ IndexInterface.to_idx _) => apply to_idx_ty : transf_hints.
#[export] Hint Extern 5 (type_wf (IndexInterface.idx_ty _)) => apply idx_ty_wf : transf_hints.
