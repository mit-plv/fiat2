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
  Context (tup acc : string).
  Context (H_NoDup : is_NoDup_opaque [tup; acc]).

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



  Context (x1 x2 b : string).
  Context (EFlatmap2 : expr -> expr -> string -> string -> expr -> expr).

  Definition and_bitmaps bm1 bm2 :=
      EFlatmap2 (EVar bm1) (EVar bm2)
        x1 x2 (EBinop OCons (EBinop OAnd (EVar x1) (EVar x2)) (EAtom (ANil None))).

  Definition use_bitmap bm d :=
    let n := EAccess (EVar acc) "0" in
    let l := EAccess (EVar acc) "1" in
    EFold bm (ERecord [("0", EAtom (AInt 0)); ("1", EAtom (ANil None))])
      b acc (ERecord [("0", EBinop OPlus n (EAtom (AInt 1)));
                      ("1", EIf (EVar b) (EBinop OCons (EBinop OLookup d n) l) l)]).

  Definition and_filter_to_bitmap_lookup_head (e : expr) bm1 bm2 :=
    match e with
    | EFilter LikeList (ELoc tbl0) x0 (EBinop OAnd (EBinop OEq (EAccess (EVar x1) attr0) str0)
                                         (EBinop OEq (EAccess (EVar x2) attr1) str1)) =>
        let n := EAccess (EVar acc) "0" in
        let l := EAccess (EVar acc) "1" in
        EAccess
          (EFold (and_bitmaps bm1 bm2) (ERecord [("0", EAtom (AInt 0)); ("1", EAtom (ANil None))])
           tup acc
           (ERecord [("0", EBinop OPlus n (EAtom (AInt 1))); ("1", EBinop OCons (EBinop OLookup (ELoc tbl0) n) l)]))
          "1"
    | _ => e
    end.
  End WithMap.
End WithHole.
