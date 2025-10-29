Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface2 fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.

Section WithHole.
  Context (hole : string).
  Context (tup acc : string).
  Context (H_NoDup : is_NoDup_opaque [tup; acc]).

  Definition to_pk_idx :=
    let n := EAccess (EVar acc) "0" in
    let d := EAccess (EVar acc) "1" in
    EFold (EVar hole) (ERecord [("0", EAtom (AInt 0)); ("1", EAtom (AEmptyDict None))])
      tup acc
      (ERecord [("0", EBinop OPlus n (EAtom (AInt 1))); ("1", ETernop OInsert d n (EVar tup))]).

  (* ??? remove
  Definition to_pk_idx :=
    let n := EAccess (EVar acc) "0" in
    let l := EAccess (EVar acc) "1" in
    let d := EAccess (EVar acc) "2" in
    EFold (EVar hole) (ERecord [("0", EAtom (AInt 0)); ("1", EAtom (ANil (Some TInt))); ("2", EAtom (AEmptyDict None))])
      tup acc
      (ERecord [("0", EBinop OPlus n (EAtom (AInt 1))); ("1", EBinop OCons n l); ("2", ETernop OInsert d n (EVar tup))]).
*)
  Definition is_pk_tbl_ty (t : type) : bool :=
    match t with
    | TList _ => true
    | _ => false
    end.

  Definition pk_idx_ty (t : type) : type :=
    match t with
    | TList t => TRecord [("0", TInt); ("1", TDict TInt t)]
    | _ => TUnit
    end.

  Lemma pk_idx_ty_wf : forall t, type_wf t -> is_pk_tbl_ty t = true -> type_wf (pk_idx_ty t).
  Proof.
    destruct t; simpl; intros; try congruence.
    repeat constructor; cbn; intuition idtac; try congruence.
    auto with fiat2_hints.
  Qed.

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (width:=width)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Lemma to_pk_idx_ty : forall (t : type),
        type_wf t -> is_pk_tbl_ty t = true ->
        type_of map.empty (map.put map.empty hole t) to_pk_idx (pk_idx_ty t).
    Proof.
      intros. unfold to_idx.
      unfold is_pk_tbl_ty in *. repeat destruct_match_hyp; try discriminate; subst.
      invert_type_wf. repeat econstructor; simpl; auto.
      all: repeat rewrite_map_get_put_goal; eauto.
      all: repeat constructor; intuition idtac; try discriminate.
      all: repeat econstructor; repeat rewrite_map_get_put_goal; auto.
      use_is_NoDup.
    Qed.

    Definition pk_idx_wf (tbl_v idx_v : value) : Prop :=
      idx_v = interp_expr map.empty (map.put map.empty hole tbl_v) to_pk_idx.

    Lemma to_pk_idx_wf : forall (v : value) (t : type),
        type_wf t -> is_pk_tbl_ty t = true ->
        type_of_value v t ->
        pk_idx_wf v (interp_expr map.empty (map.put map.empty hole v) to_pk_idx).
    Proof.
      intros; unfold pk_idx_wf; auto.
    Qed.

    Fixpoint mk_ids (n : nat) : list value :=
      match n with
      | O => []
      | S n => VInt (Z.of_nat n) :: mk_ids n
      end.

    Definition gallina_to_pk_idx (tbl_v : value) : value :=
      match tbl_v with
      | VList l1 =>
          fold_right
            (fun v acc0 : value =>
               VRecord
                 [("0",
                    apply_int_binop Z.add
                      match
                        acc0
                      with
                      | VRecord l => record_proj "0" l
                      | _ => VUnit
                      end (VInt 1));
                  ("1",
             match
               match acc0
               with
               | VRecord l => record_proj "1" l
               | _ => VUnit
               end
             with
             | VDict d =>
                 VDict
                   (dict_insert
                      match acc0
                      with
                      | VRecord l => record_proj "0" l
                      | _ => VUnit
                      end v d)
             | _ => VUnit
             end)]) (VRecord [("0", VInt 0); ("1", VDict [])])
        l1
  | _ => VUnit
      end.

    Lemma fiat2_gallina_to_pk_idx : forall tbl_v, interp_expr (word:=word) map.empty (map.put map.empty hole tbl_v) to_pk_idx = gallina_to_pk_idx tbl_v.
    Proof.
      intros. cbn.
      unfold gallina_to_pk_idx, get_local; rewrite_map_get_put_goal.
      case_match; auto.
      apply In_fold_right_ext with (P:=fun _ => True); intuition idtac.
      repeat rewrite_map_get_put_goal; auto; use_is_NoDup.
    Qed.

    Definition is_pk_idx (ids l : list value) (d : list (value * value)) : Prop :=
      d = dict_sort (flat_map2 (fun k v => [(k, v)]) ids l).

    Definition pk_idx_chara (tbl_v idx_v : value) : Prop :=
      match tbl_v, idx_v with
      | VList l, VRecord r =>
          access_record r "0" = Success (VInt (Z.of_nat (Datatypes.length l))) /\
            match access_record r "1" with
            | Success (VDict d) => is_pk_idx (mk_ids (Datatypes.length l)) l d
            | _ => False
            end
      | _, _ => False
      end.

    Lemma map_fst_flat_map2 : forall A B l l',
      incl (List.map fst
              (flat_map2 (fun (k:A) (v:B) => [(k, v)]) l l'))
        l.
    Proof.
      induction l; intros.
      1: apply incl_nil_l.
      1:{ destruct l'.
          1: apply incl_nil_l.
          cbn. auto using incl_cons_step. }
    Qed.

    Lemma mk_ids_lt : forall n,
        Forall (fun v => value_compare v (VInt (Z.of_nat n)) = Lt) (mk_ids n).
    Proof.
      induction n; cbn; intuition auto.
      rewrite Forall_forall; intros.
      destruct_In; cbn.
      2: apply_Forall_In; eapply value_compare_trans; eauto.
      all: rewrite Zpos_P_of_succ_nat;
        apply Zcompare_Gt_Lt_antisym, Zcompare_succ_Gt.
    Qed.

    Lemma dict_insert_fresh : forall (k v : value) d,
        ~ In k (List.map fst d) ->
        Permutation (dict_insert k v d) ((k, v) :: d).
      induction d; cbn; auto.
      unfold value_ltb, value_eqb. intros.
      repeat case_match.
      1:{ apply value_compare_Eq_eq in E0; subst.
          intuition idtac. }
      1: apply Permutation_refl.
      1: intuition idtac.
      eauto using perm_trans, perm_skip, perm_swap.
    Qed.

    Local Coercion is_true : bool >-> Sortclass.

    Ltac invert_SSorted_clear :=
      lazymatch goal with
        H: StronglySorted _ (_ :: _) |- _ =>
          inversion H; subst; clear H
      end.

    Lemma Permutation_NoDup_SSorted_dict : forall (l l' : list (value * value)),
        Permutation l l' ->
        NoDup (List.map fst l) ->
        StronglySorted dict_entry_leb l ->
        StronglySorted dict_entry_leb l' ->
        l = l'.
    Proof.
      induction l; destruct l'; cbn; auto; intros.
      2: apply Permutation_sym in H.
      1,2: apply Permutation_nil_cons in H; intuition idtac.
      assert (a = p).
      { repeat invert_SSorted_clear.
        eapply Permutation_in in H as H'.
        2: apply in_eq.
        destruct_In; auto. apply_Forall_In.
        apply Permutation_sym in H.
        eapply Permutation_in in H as H''.
        2: apply in_eq.
        destruct_In; auto. apply_Forall_In.
        repeat lazymatch goal with
                 H: is_true (dict_entry_leb _ _) |- _ =>
                   unfold dict_entry_leb, value_leb, leb_from_compare in H
               end.
        lazymatch goal with
          H: context[value_compare] |- _ =>
            rewrite value_compare_antisym in H
        end.
        repeat destruct_match_hyp; cbn in *; try discriminate.
        apply value_compare_Eq_eq in E0.
        lazymatch goal with
          H: In _ _ |- _ =>
            apply in_map with (f:=fst) in H
        end. repeat rewrite_l_to_r.
        invert_NoDup. intuition idtac. }
      subst. f_equal. invert_NoDup. repeat invert_SSorted_clear.
      apply IHl; eauto using Permutation_cons_inv.
    Qed.

    Lemma dict_insert_preserve_NoDup2 : forall (k v : value) d,
        StronglySorted dict_entry_leb d ->
        NoDup (List.map fst d) ->
        NoDup (List.map fst (dict_insert k v d)).
      induction d; cbn; intros.
      1: constructor; auto using NoDup_nil.
      case_match. unfold value_ltb, value_eqb.
      case_match.
      1:{ apply value_compare_Eq_eq in E0; subst.
          cbn in *; assumption. }
      1:{ invert_SSorted_clear; cbn in *.
          constructor.
          2: assumption.
          intro contra.
          cbn in *. intuition idtac; subst.
          1: rewrite value_compare_refl in *; discriminate.
          apply In_fst in H; destruct_exists; intuition idtac.
          apply_Forall_In.
          rewrite value_compare_antisym in *.
          unfold dict_entry_leb, value_leb, leb_from_compare in *; cbn in *. repeat rewrite_l_to_r.
          destruct_match_hyp; discriminate. }
      invert_NoDup; invert_SSorted_clear; cbn; constructor; auto.
      intro contra.
      apply In_fst in contra; destruct_exists; intuition idtac.
      lazymatch goal with
        H: In _ (dict_insert _ _ _) |- _ =>
          apply dict_insert_incl in H
      end.
      destruct_In.
      1: rewrite value_compare_refl in *; discriminate.
      1: apply in_map with (f:=fst) in H; intuition fail.
    Qed.

    Lemma map_fst_flat_map2_mk_ids : forall l,
        map fst
          (flat_map2 (fun k v : value => [(k, v)])
             (mk_ids (Datatypes.length l)) l) = mk_ids (Datatypes.length l).
    Proof.
      induction l; cbn; congruence.
    Qed.

    Lemma mk_ids_NoDup : forall n, NoDup (mk_ids n).
    Proof.
      induction n; cbn; auto using NoDup_nil.
      constructor; auto.
      intro contra.
      pose proof (mk_ids_lt n).
      apply_Forall_In.
      rewrite value_compare_refl in *; discriminate.
    Qed.

    Lemma pk_idx_wf__pk_idx_chara : forall t tbl_v idx_v,
        is_pk_tbl_ty t = true ->
        type_of_value tbl_v t ->
        pk_idx_wf tbl_v idx_v -> pk_idx_chara tbl_v idx_v.
    Proof.
      intros *. unfold pk_idx_wf.
      rewrite fiat2_gallina_to_pk_idx.
      unfold gallina_to_pk_idx, pk_idx_chara, is_pk_tbl_ty.
      intro. destruct_match_hyp; try discriminate.
      intros; invert_type_of_value_clear.
      lazymatch goal with
        H: Forall _ _ |- _ => induction H end.
      1:{ cbn; intuition idtac.
          unfold is_pk_idx. cbn; auto. }
      cbn. destruct_match_hyp; intuition idtac.
      1:{ f_equal. unfold record_proj.
          lazymatch goal with
            H: access_record _ _ = _ |- _ =>
              rewrite H
          end. cbn. f_equal.
          rewrite Zpos_P_of_succ_nat, <- Nat2Z.inj_succ.
          rewrite <- Nat.add_1_r, Nat2Z.inj_add. reflexivity. }
      1:{ unfold record_proj.
          repeat (destruct_match_hyp; intuition idtac).
          unfold is_pk_idx in *.
          lazymatch goal with
            H: access_record _ "0" = _ |- _ =>
              rewrite H
          end.
          cbn [flat_map2 app].
          apply Permutation_NoDup_SSorted_dict.
          1:{ subst. eapply perm_trans.
              1: apply dict_insert_fresh.
              1:{ intro contra.
                  eapply Permutation_in in contra.
                  2: apply Permutation_map, Permutation_sym, Permuted_dict_sort.
                  rewrite map_fst_flat_map2_mk_ids in *.
                  pose proof (mk_ids_lt (Datatypes.length l)).
                  apply_Forall_In.
                  rewrite value_compare_refl in *; discriminate. }
              eauto using perm_trans, Permuted_dict_sort, perm_skip, Permutation_sym. }
          1:{ apply dict_insert_preserve_NoDup2; subst.
              1: apply StronglySorted_dict_sort.
              eapply Permutation_NoDup.
              1: eapply Permutation_map, Permuted_dict_sort.
              rewrite map_fst_flat_map2_mk_ids.
              apply mk_ids_NoDup. }
          1: apply dict_insert_preserve_SSorted; subst;
          apply StronglySorted_dict_sort.
          1: apply StronglySorted_dict_sort. }
    Qed.

  End WithMap.
End WithHole.

Section WithHole.
  Context (attr str : string).
  Context (hole : string).
  Context (tup : string).

  Definition to_bitmap :=
    EFlatmap LikeList (EVar hole) tup
      (EBinop OCons
         (EBinop OEq (EAccess (EVar tup) attr) (EAtom (AString str)))
         (EAtom (ANil (Some TBool)))).

  Definition is_bitmap_tbl_ty (t : type) : bool :=
    match t with
    | TList (TRecord rt) => match access_record rt attr with
                            | Success t => type_eqb t TString
                            | _ => false
                            end
    | _ => false
    end.

  Definition bitmap_ty (t : type) : type := TList TBool.

  Lemma bitmap_ty_wf : forall t, type_wf t -> is_bitmap_tbl_ty t = true -> type_wf (bitmap_ty t).
  Proof.
    destruct t; simpl; intros; try congruence.
    repeat constructor; cbn; intuition idtac; try congruence.
  Qed.

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (width:=width)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Lemma to_bitmap_ty : forall (t : type),
        type_wf t -> is_bitmap_tbl_ty t = true ->
        type_of map.empty (map.put map.empty hole t) to_bitmap (bitmap_ty t).
    Proof.
      intros. unfold to_idx.
      unfold is_bitmap_tbl_ty in *.
      repeat destruct_match_hyp; try discriminate; rewrite type_eqb_eq in *; subst.
      invert_type_wf. repeat econstructor; simpl; auto.
      all: repeat rewrite_map_get_put_goal; eauto.
    Qed.

    Definition bitmap_wf (tbl_v idx_v : value) : Prop :=
      idx_v = interp_expr map.empty (map.put map.empty hole tbl_v) to_bitmap.

    Lemma to_bitmap_wf : forall (v : value) (t : type),
        type_wf t -> is_bitmap_tbl_ty t = true ->
        type_of_value v t ->
        bitmap_wf v (interp_expr map.empty (map.put map.empty hole v) to_bitmap).
    Proof.
      intros; unfold bitmap_wf; auto.
    Qed.


    Definition bitmap_chara (tbl_v idx_v : value) : Prop :=
      idx_v = match tbl_v with
              | VList l1 =>
                  VList
                    (flat_map
                       (fun v : value =>
                          [VBool
                             (value_eqb
                                match v with
                                | VRecord l => record_proj attr l
                                | _ => VUnit
                                end (VString str))]) l1)
              | _ => VUnit
              end.

    Lemma bitmap_wf__bitmap_chara : forall tbl_v idx_v,
        bitmap_wf tbl_v idx_v ->
        bitmap_chara tbl_v idx_v.
    Proof.
      unfold bitmap_wf, bitmap_chara; intros; subst.
      cbn; unfold get_local; rewrite_map_get_put_goal.
      case_match; auto. f_equal.
      apply In_flat_map_ext; intros.
      repeat f_equal. rewrite_map_get_put_goal.
      reflexivity.
    Qed.
  End WithMap.
End WithHole.

Section WithTags.
  Context (id_tag aux_tag pk_idx_tag bm_tag : string).

  Section filter_to_bitmap_lookup.
    Context (tbl attr str : string).
    Context (x1 b acc : string).
    Context (H_NoDup : is_NoDup_opaque [x1; b; acc]).

    Definition use_bitmap bm d :=
      let n := EAccess (EVar acc) "0" in
      let l := EAccess (EVar acc) "1" in
      EFold bm (ERecord [("0", EAtom (AInt 0)); ("1", EAtom (ANil None))])
        b acc (ERecord [("0", EBinop OPlus n (EAtom (AInt 1)));
                        ("1", EIf (EVar b)
                                (EOptMatch (EBinop OLookup d n)
                                   l x1 (EBinop OCons (EVar x1) l))
                                l)]).

    Definition filter_to_bitmap_lookup_head (e : expr) :=
      match e with
      | EFilter LikeList (EAccess (ELoc tbl0) (id_tag0)) x
          (EBinop OEq (EAccess (EVar x0) attr0) (EAtom (AString str0))) =>
          if (all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x, [x0; x1]); (id_tag, [id_tag0]); (str, [str0])])
          then
            let n := EAccess (EVar acc) "0" in
            let l := EAccess (EVar acc) "1" in
            EAccess
              (use_bitmap
                 (EAccess (EAccess (ELoc tbl) aux_tag) bm_tag)
                 (EAccess (EAccess (EAccess (ELoc tbl) aux_tag) pk_idx_tag) "1"))
              "1"
          else e
      | _ => e
      end.

    Section WithMap.
      Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
      Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
      Notation value := (value (width:=width)).
      Context {locals : map.map string value} {locals_ok : map.ok locals}.

      Lemma filter_to_bitmap_lookup_head_preserve_ty : forall tl t aux_tl (Gstore : tenv),
          type_wf t -> is_pk_tbl_ty t = true ->
          is_bitmap_tbl_ty attr t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord aux_tl) ->
          access_record aux_tl pk_idx_tag = Success (pk_idx_ty t) ->
          access_record aux_tl bm_tag = Success (bitmap_ty t) ->
          preserve_ty Gstore (filter_to_bitmap_lookup_head).
      Proof.
        unfold preserve_ty, is_pk_tbl_ty, is_bitmap_tbl_ty. intros.
        repeat destruct_match_hyp; try congruence.
        repeat destruct_subexpr. simpl.
        case_match; auto. repeat rewrite Bool.andb_true_r in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        rewrite eqb_eq in *; subst.
        repeat invert_type_of_clear. repeat invert_type_of_op_clear.
        repeat rewrite_map_get_put_hyp.
        repeat (clear_refl; repeat do_injection2).
        repeat (rewrite_l_to_r; do_injection2).
        econstructor.
        1: econstructor.
        1: repeat (econstructor; eauto).
        1:{ lazymatch goal with
            H: tenv_wf ?G, H': map.get ?G _ = _ |- _ =>
              apply H in H'
          end.
            repeat invert_type_wf.
            instantiate(1:=[("0", TInt); ("1", TList (TRecord tl0))]).
            repeat (econstructor; eauto). cbn; intuition discriminate. }
        1:{ repeat (econstructor; eauto);
            repeat rewrite_map_get_put_goal; eauto;
            use_is_NoDup. }
        cbn; reflexivity.
      Qed.

      Context (pk_hole pk_tup pk_acc : string).
      Context (H_NoDup_pk : is_NoDup_opaque [pk_tup; pk_acc]).

      Notation pk_idx_wf := (pk_idx_wf pk_hole pk_tup pk_acc).

      Definition aux_wf_for_idx idx_tag idx_wf (v : value) : Prop :=
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

      Context (bm_hole : string).
      Context (bm_tup : string).
      Notation bitmap_wf := (bitmap_wf attr str bm_hole bm_tup).

      (* ??? TODO: move *)
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

      Ltac use_Forall2_access_record tag :=
        lazymatch goal with
          H: Forall2 _ ?l ?tl, H1: access_record ?l tag = _,
              H2: access_record ?tl tag = _ |- _ =>
            pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H H1 H2)
        end.

      Lemma fiat2_gallina_use_bitmap : forall (store env : locals) bm d,
          free_immut_in b d = false ->
          free_immut_in acc d = false ->
          interp_expr store env (use_bitmap bm d) =
            match interp_expr store env bm with
            | VList l1 =>
                fold_right
                  (fun v acc0 : value =>
                     VRecord
                       [("0",
                          apply_int_binop Z.add
                            match
                              acc0
                            with
                            | VRecord l => record_proj "0" l
                            | _ => VUnit
                            end (VInt 1));
                        ("1",
                          match
                            v
                          with
                          | VBool true =>
                              match
                                match
                                  interp_expr store env d
                                with
                                | VDict d0 =>
                                    VOption
                                      (dict_lookup
                                         match
                                           acc0
                                         with
                                         | VRecord l => record_proj "0" l
                                         | _ => VUnit
                                         end d0)
                                | _ => VUnit
                                end
                              with
                              | VOption (Some v0) =>
                                  match
                                    match acc0
                                    with
                                    | VRecord l => record_proj "1" l
                                    | _ => VUnit
                                    end
                                  with
                                  | VList l =>
                                      VList
                                        (v0 :: l)
                                  | _ => VUnit
                                  end
                              | VOption None =>
                                  match acc0
                                  with
                                  | VRecord l => record_proj "1" l
                                  | _ => VUnit
                                  end
                              | _ => VUnit
                              end
                          | VBool false =>
                              match acc0
                              with
                              | VRecord l => record_proj "1" l
                              | _ => VUnit
                              end
                          | _ => VUnit
                          end)]) (VRecord [("0", VInt 0); ("1", VList [])])
                  l1
            | _ => VUnit
            end.
      Proof.
        intros; unfold use_bitmap; cbn.
        case_match; auto.
        apply In_fold_right_ext with (P:=fun _ => True); intuition idtac.
        repeat f_equal; unfold get_local; repeat rewrite_map_get_put_goal; auto.
        2: use_is_NoDup.
        case_match; auto.
        repeat rewrite_map_get_put_goal.
        repeat rewrite <- not_free_immut_put_sem; auto.
        repeat (case_match; auto; []).
        do 2 case_match; auto; repeat rewrite_map_get_put_goal; auto.
        all: use_is_NoDup.
      Qed.

      Lemma In_dict_lookup : forall (k v : value) d,
          StronglySorted (fun v1 v2=> is_true (dict_entry_leb v1 v2)) d ->
          NoDup (List.map fst d) ->
          In (k, v) d ->
          dict_lookup k d = Some v.
      Proof.
        induction d; cbn; intros.
        1: intuition idtac.
        case_match. case_match.
        1:{ intuition idtac; try invert_pair; auto.
            lazymatch goal with
              H: value_eqb _ _ = true |- _ =>
                apply value_eqb_eq in H
            end; subst.
            invert_NoDup.
            lazymatch goal with
              H: In _ _ |- _ =>
                apply in_map with (f:=fst) in H
            end. intuition idtac. }
        1:{ lazymatch goal with
            H: value_eqb _ _ = false |- _ =>
              apply value_eqb_neq in H
          end.
            invert_NoDup; invert_SSorted; apply IHd; intuition auto.
            congruence. }
      Qed.

      Lemma dict_lookup_Some__In : forall (k v : value) d,
          dict_lookup k d = Some v -> In (k, v) d.
      Proof.
        induction d; cbn; try discriminate.
        repeat case_match; intros; auto.
        do_injection. apply value_eqb_eq in E0; subst; auto.
      Qed.

      Lemma is_pk_idx__dict_lookup : forall (l : list value) d,
          is_pk_idx (mk_ids (Datatypes.length l)) l d ->
          Forall2 (fun k v => dict_lookup k d = Some v) (mk_ids (Datatypes.length l)) l.
      Proof.
        unfold is_pk_idx; intros; subst.
        induction l.
        1: cbn; auto.
        cbn [flat_map2 Datatypes.length mk_ids app].
        constructor;
          (assert (Heq: forall (k v : value) l l',
                (k, v) :: flat_map2 (fun k v => [(k, v)]) l l' = flat_map2 (fun k v => [(k, v)]) (k :: l) (v :: l')); [ reflexivity | ];
          assert (Heq': VInt (Z.of_nat (Datatypes.length l)) :: mk_ids (width:=width) (Datatypes.length l) = mk_ids (Datatypes.length (a :: l)));  [ reflexivity | ]).
        1:{ apply In_dict_lookup; auto using StronglySorted_dict_sort.
            1:{ eapply Permutation_NoDup.
                1: eapply Permutation_map, Permuted_dict_sort.
                rewrite Heq, Heq'.
                rewrite map_fst_flat_map2_mk_ids.
                apply mk_ids_NoDup. }
            1:{ eapply Permutation_in.
                1: apply Permuted_dict_sort.
                constructor; reflexivity. } }
        1:{ eapply Forall2_impl; eauto; simpl; intros.
            apply In_dict_lookup; auto using StronglySorted_dict_sort.
            1:{ eapply Permutation_NoDup.
                1: eapply Permutation_map, Permuted_dict_sort.
                rewrite Heq, Heq'.
                rewrite map_fst_flat_map2_mk_ids.
                apply mk_ids_NoDup. }
            1:{ eapply Permutation_in.
                1: apply Permuted_dict_sort.
                right.
                lazymatch goal with
                  H: dict_lookup _ _ = Some _ |- _ =>
                    apply dict_lookup_Some__In in H
                end.
                eapply Permutation_in; [ | eauto ].
                apply Permutation_sym, Permuted_dict_sort. } }
      Qed.

      Lemma use_bitmap_sem : forall l d bm tl (store env : locals),
          free_immut_in b d = false ->
          free_immut_in acc d = false ->
          match interp_expr store env d with
          | VDict d =>
              is_pk_idx (mk_ids (Datatypes.length l)) l d
          | _ => False
          end ->
          bitmap_chara attr str (VList l) (interp_expr store env bm) ->
          Forall (fun v : value => type_of_value v (TRecord tl)) l ->
          access_record tl attr = Success TString ->
          interp_expr store env (use_bitmap bm d) =
            VRecord [("0", VInt (Z.of_nat (Datatypes.length l)));
                     ("1", VList
                             (filter (fun v =>
                                        match v with
                                        | VRecord r =>
                                            match access_record r attr with
                                            | Success v => value_eqb v (VString str)
                                            | Failure _ => false
                                            end
                                        | _ => false
                                        end) l))].
      Proof.
        unfold bitmap_chara. intros; cbn in * |-.
        rewrite fiat2_gallina_use_bitmap; auto.
        destruct_match_hyp; intuition idtac.
        lazymatch goal with
          H: is_pk_idx _ _ _ |- _ =>
            apply is_pk_idx__dict_lookup in H
        end.
        rewrite_l_to_r. clear H2.
        induction l.
        1: cbn; auto.
        cbn [flat_map app].
        invert_Forall. invert_type_of_value_clear.
        cbn [fold_right].
        erewrite IHl; cbn; auto.
        2:{ cbn in *. invert_Forall2; auto. }
        repeat f_equal.
        1:{ rewrite Zpos_P_of_succ_nat.
            rewrite Z.add_1_r. reflexivity. }
        1:{ apply access_record_sound in H4.
            apply in_map with (f:=fst) in H4; cbn in H4.
            lazymatch goal with
                H: Forall2 (fun _ _ => _ /\ _) _ _ |- _ =>
                  apply Forall2_split in H
              end; intuition idtac.
            apply Forall2_fst_eq in H2.
            rewrite <- H2 in H4.
            apply In_access_record in H4; destruct_exists.
            unfold record_proj.
            rewrite_l_to_r.
            case_match; auto.
            invert_Forall2. rewrite_l_to_r. reflexivity. }
      Qed.

      Lemma filter_to_bitmap_lookup_head_preserve_sem : forall (Gstore : tenv) (store : locals) tl t aux_tl,
          type_wf t -> is_pk_tbl_ty t = true ->
          is_bitmap_tbl_ty attr t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord aux_tl) ->
          access_record aux_tl pk_idx_tag = Success (pk_idx_ty t) ->
          access_record aux_tl bm_tag = Success (bitmap_ty t) ->
          match map.get store tbl with
          | Some v => aux_wf_for_idx pk_idx_tag pk_idx_wf v /\
                        aux_wf_for_idx bm_tag bitmap_wf v
          | _ => False
          end ->
          preserve_sem Gstore store filter_to_bitmap_lookup_head.
      Proof.
        unfold preserve_sem, aux_wf_for_idx; intros.
        repeat (destruct_match_hyp; try discriminate; intuition idtac; []).
        eapply pk_idx_wf__pk_idx_chara in H13; eauto.
        all: unfold is_pk_tbl_ty, is_bitmap_tbl_ty, pk_idx_ty, bitmap_ty in *.
        all: apply_locals_wf store;
          repeat (destruct_match_hyp; try discriminate; intuition idtac; []);  do_injection.
        all: invert_type_of_value_clear;
          use_Forall2_access_record id_tag; auto.
        use_Forall2_access_record aux_tag.
        invert_type_of_value_clear.
        use_Forall2_access_record pk_idx_tag.
        use_Forall2_access_record bm_tag.
        repeat destruct_subexpr. unfold filter_to_bitmap_lookup_head.
        case_match; auto. cbn in * |-.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        rewrite eqb_eq in *; subst. repeat clear_refl.
        cbn [interp_expr interp_binop apply_bool_binop interp_atom].
        unfold get_local. rewrite_l_to_r.
        unfold record_proj. repeat rewrite_l_to_r.
        repeat invert_type_of_value_clear.
        rewrite type_eqb_eq in *; subst.
        unfold pk_idx_chara in *.
        destruct_and. repeat (destruct_match_hyp; intuition idtac).
        erewrite use_bitmap_sem; try reflexivity.
        4,5: eauto.
        2:{ cbn. unfold get_local, record_proj; repeat rewrite_l_to_r.
            eauto. }
        2:{ eapply bitmap_wf__bitmap_chara; auto; cbn.
            unfold get_local, record_proj; repeat rewrite_l_to_r. eauto. }
        cbn. f_equal.
        apply In_filter_ext; intros. apply_Forall_In.
        invert_type_of_value_clear. rewrite_map_get_put_goal.
        lazymatch goal with
          H: Forall2 _ l6 _ |- _ => apply Forall2_split in H as [HL HR] end.
        rewrite Forall2_fst_eq in HL.
        lazymatch goal with
          H: access_record l1 _ = _ |- _ =>
            apply access_record_sound in H;
            apply in_map with (f:=fst) in H; cbn in H;
            rewrite <- HL in H; apply In_access_record in H
        end.
        destruct_exists; rewrite_l_to_r. reflexivity.
      Qed.
    End WithMap.

  End filter_to_bitmap_lookup.

End WithTags.

(*
    Context (tbl attr1 str1 attr2 str2 : string).
    Context (x1 x2 b acc : string).
    Context (H_NoDup : is_NoDup_opaque [x1; x2; b; acc]).

    Definition and_bitmaps bm1 bm2 :=
      EFlatmap2 bm1 bm2
        x1 x2 (EBinop OCons (EBinop OAnd (EVar x1) (EVar x2)) (EAtom (ANil None))).

    Definition use_bitmap bm d :=
      let n := EAccess (EVar acc) "0" in
      let l := EAccess (EVar acc) "1" in
      EFold bm (ERecord [("0", EAtom (AInt 0)); ("1", EAtom (ANil None))])
        b acc (ERecord [("0", EBinop OPlus n (EAtom (AInt 1)));
                        ("1", EIf (EVar b)
                                (EOptMatch (EBinop OLookup d n)
                                   l x1 (EBinop OCons (EVar x1) l))
                                l)]).

    Definition and_filter_to_lookup_head (e : expr) :=
      match e with
      | EFilter LikeList (EAccess (ELoc tbl0) (id_tag0)) x
          (EBinop OAnd (EBinop OEq (EAccess (EVar x0) attr1') str1')
             (EBinop OEq (EAccess (EVar x1) attr2') str2')) =>
          if (all_eqb [(tbl, [tbl0]); (attr1, [attr1']); (attr2, [attr2']); (x, [x0; x1]); (id_tag, [id_tag0])])
          then
            let n := EAccess (EVar acc) "0" in
            let l := EAccess (EVar acc) "1" in
            EAccess
              (use_bitmap
                 (and_bitmaps
                    (EAccess (EAccess (ELoc tbl) aux_tag) bm1_tag)
                    (EAccess (EAccess (ELoc tbl) aux_tag) bm2_tag))
                 (EAccess (EAccess (EAccess (ELoc tbl) aux_tag) pk_idx_tag) "1"))
              "1"
          else e
      | _ => e
      end.

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (width:=width)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Lemma and_bitmaps_ty : forall Gstore Genv e1 e2,
        type_of Gstore Genv e1 (TList TBool) ->
        type_of Gstore Genv e2 (TList TBool) ->
        type_of Gstore Genv (and_bitmaps e1 e2) (TList TBool).
    Proof.
      clear H_NoDup.
      intros. econstructor; eauto.
      repeat econstructor; try now (rewrite_map_get_put_goal; auto).
      destruct_get_put_strings; auto.
    Qed.

    Lemma and_filter_to_lookup_head_preserve_ty : forall tl t aux_tl (Gstore : tenv),
        type_wf t -> is_pk_tbl_ty t = true ->
        is_bitmap_tbl_ty attr1 t = true ->
        is_bitmap_tbl_ty attr2 t = true ->
        map.get Gstore tbl = Some (TRecord tl) ->
        access_record tl id_tag = Success t ->
        access_record tl aux_tag = Success (TRecord aux_tl) ->
        access_record aux_tl pk_idx_tag = Success (pk_idx_ty t) ->
        access_record aux_tl bm1_tag = Success (bitmap_ty t) ->
        access_record aux_tl bm2_tag = Success (bitmap_ty t) ->
        preserve_ty Gstore (and_filter_to_lookup_head).
    Proof.
      unfold preserve_ty, is_pk_tbl_ty, is_bitmap_tbl_ty. intros.
      repeat destruct_match_hyp; try congruence.
      repeat destruct_subexpr. simpl.
      case_match; auto. repeat rewrite Bool.andb_true_r in *.
      repeat rewrite Bool.andb_true_iff in *; intuition idtac.
      rewrite eqb_eq in *; subst.
      repeat invert_type_of_clear. repeat invert_type_of_op_clear.
      repeat rewrite_map_get_put_hyp.
      repeat (clear_refl; repeat do_injection2).
      repeat (rewrite_l_to_r; do_injection2).
      econstructor.
      1: econstructor.
      1: apply and_bitmaps_ty; repeat (econstructor; eauto).
      1:{ lazymatch goal with
          H: tenv_wf ?G, H': map.get ?G _ = _ |- _ =>
            apply H in H'
        end.
          repeat invert_type_wf.
          instantiate(1:=[("0", TInt); ("1", TList (TRecord tl1))]).
          repeat (econstructor; eauto). cbn; intuition discriminate. }
      1:{ repeat (econstructor; eauto);
          repeat rewrite_map_get_put_goal; eauto;
          use_is_NoDup. }
      cbn; reflexivity.
    Qed.

    Context (pk_hole pk_tup pk_acc : string).
    Context (H_NoDup_pk : is_NoDup_opaque [pk_tup; pk_acc]).

    Notation pk_idx_wf := (pk_idx_wf pk_hole pk_tup pk_acc).

    Definition aux_wf_for_idx idx_tag idx_wf (v : value) : Prop :=
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

    Context (bm1_hole bm2_hole : string).
    Context (bm1_tup bm2_tup : string).
    Notation bitmap1_wf := (bitmap_wf attr1 str1 bm1_hole bm1_tup).
    Notation bitmap2_wf := (bitmap_wf attr2 str2 bm2_hole bm2_tup).

    (* ??? TODO: move *)
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

    Ltac use_Forall2_access_record tag :=
      lazymatch goal with
        H: Forall2 _ ?l ?tl, H1: access_record ?l tag = _,
            H2: access_record ?tl tag = _ |- _ =>
          pose proof (Forall2_access_record _ _ _ _ _ _ _ _ H H1 H2)
      end.

    Lemma and_filter_to_lookup_head_preserve_sem : forall (Gstore : tenv) (store : locals) tl t aux_tl,
        type_wf t -> is_pk_tbl_ty t = true ->
        is_bitmap_tbl_ty attr1 t = true ->
        is_bitmap_tbl_ty attr2 t = true ->
        map.get Gstore tbl = Some (TRecord tl) ->
        access_record tl id_tag = Success t ->
        access_record tl aux_tag = Success (TRecord aux_tl) ->
        access_record aux_tl pk_idx_tag = Success (pk_idx_ty t) ->
        access_record aux_tl bm1_tag = Success (bitmap_ty t) ->
        access_record aux_tl bm2_tag = Success (bitmap_ty t) ->
        match map.get store tbl with
        | Some v => aux_wf_for_idx pk_idx_tag pk_idx_wf v /\
                      aux_wf_for_idx bm1_tag bitmap1_wf v /\
                      aux_wf_for_idx bm2_tag bitmap2_wf v
        | _ => False
        end ->
        preserve_sem Gstore store and_filter_to_lookup_head.
    Proof.
      unfold preserve_sem, aux_wf_for_idx; intros.
      unfold is_pk_tbl_ty, is_bitmap_tbl_ty, pk_idx_ty, bitmap_ty in *.
      apply_locals_wf store.
      repeat (destruct_match_hyp; try discriminate; intuition idtac; []).

      invert_type_of_value_clear.
      use_Forall2_access_record id_tag.
      use_Forall2_access_record aux_tag.
      invert_type_of_value_clear.
      use_Forall2_access_record pk_idx_tag.
      use_Forall2_access_record bm1_tag.
      use_Forall2_access_record bm2_tag.
      repeat destruct_subexpr. unfold and_filter_to_lookup_head.
      case_match; auto. cbn in * |-.
      repeat rewrite Bool.andb_true_iff in *; intuition idtac.
      rewrite eqb_eq in *; subst. repeat clear_refl.
      unfold use_bitmap, and_bitmaps.
      cbn [interp_expr interp_binop apply_bool_binop].
      unfold get_local. rewrite_l_to_r.
      unfold record_proj. repeat rewrite_l_to_r.
      repeat invert_type_of_value_clear.


  End WithMap.
*)
