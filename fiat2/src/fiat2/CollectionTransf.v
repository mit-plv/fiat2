Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils fiat2.TransfUtils.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Definition annotate_collection (e : expr) : expr :=
  match e with
  | ESort LikeList l => ESort LikeBag (EBagOf l)
  | EFold l (EAtom (AInt 0)) v acc (EBinop OPlus (EVar v') (EVar acc')) =>
      if (negb (v =? acc) && (v =? v') && (acc =? acc'))%bool then EACFold AGSum (EBagOf l)
      else e
  | EUnop OLength l => EACFold AGCount (EBagOf l)
  | _ => e
  end.

Fixpoint bag_of (e : expr) : expr :=
  match e with
  | EFlatmap LikeList e1 x e2 => EFlatmap LikeBag (bag_of e1) x (bag_of e2)
  | EFilter LikeList e x p => EFilter LikeBag (bag_of e) x p
  | EJoin LikeList e1 e2 x y p e3 => EJoin LikeBag (bag_of e1) (bag_of e2) x y p e3
  | EProj LikeList e1 x e2 => EProj LikeBag (bag_of e1) x e2
  | _ => EBagOf e
  end.

Definition push_down_collection (e : expr) : expr :=
  match e with
  | EBagOf e => bag_of e
  | _ => e
  end.

Definition ex : expr :=
  ESort LikeList (EFilter LikeList (ELoc "tbl") "x"
    (EBinop OEq (EAccess (EVar "x") "attr") (EAtom (AInt 0)))).
Compute fold_expr push_down_collection (fold_expr annotate_collection ex).

(* ??? remove
Fixpoint to_collection (tag : collection_tag) (e : expr) : expr :=
  match e with
  | EFlatmap LikeList e1 x e2 => EFlatmap tag (to_collection tag e1) x (to_collection tag e2)
  | ESort LikeList l => ESort LikeBag (to_collection LikeBag l)
  | EFold l (EAtom (AInt 0)) v acc (EBinop OPlus (EVar v') (EVar acc')) =>
      if ((v =? v') && (acc =? acc'))%bool then EACFold AGSum (to_collection LikeBag l)
      else e
  | EFold l (EAtom (AInt 0)) v acc (EBinop OPlus (EVar acc') (EAtom (AInt 1))) =>
      if acc =? acc' then EACFold AGCount (to_collection LikeBag l)
      else e
  | EUnop OLength l => EACFold AGCount (to_collection LikeBag l)
  | EFilter LikeList e x p => EFilter tag (to_collection tag e) x (to_collection LikeList p)
  | EJoin LikeList l1 l2 x y p e => EJoin tag (to_collection tag l1) (to_collection tag l2)
                                      x y (to_collection LikeList p) (to_collection LikeList e)
  | EProj LikeList l x e => EProj tag (to_collection tag l) x (to_collection LikeList e)
  | ELet e1 x e2 => ELet e1 x (to_collection tag e2)
  | EVar _ | ELoc _ | EAtom _ =>
                        match tag with
                        | LikeBag => EBagOf e
                        | LikeList => e
                        end
  end. *)


(* ??? DictIndexImpl modified *)

Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Local Notation value := (Value.value (word := word)).

  Local Coercion is_true : bool >-> Sortclass.

  Lemma bag_to_list__bag_insert : forall (v : value) (b : list (value * nat)),
    exists b1 b2,
      b1 ++ b2 = b /\
        bag_to_list (bag_insert v b) = bag_to_list b1 ++ v :: bag_to_list b2.
  Proof.
    induction b.
    1:{ do 2 exists nil; auto. }
    cbn. repeat case_match.
    1:{ exists nil. exists ((v0, n) :: b). auto. }
    1:{ lazymatch goal with
        H: value_eqb _ _ = true |- _ =>
          apply value_eqb_eq in H end. subst.
        exists nil. exists ((v0, n) :: b). auto. }
    1:{ repeat destruct_exists. exists ((v0, n) :: x). exists x0.
        cbn; intuition idtac.
        1: congruence.
        rewrite_l_to_r. rewrite app_assoc. reflexivity. }
  Qed.

  Lemma bag_to_list_app : forall (b1 b2 : list (value * nat)),
      bag_to_list b1 ++ bag_to_list b2 = bag_to_list (b1 ++ b2).
  Proof.
    induction b1; cbn; auto; intros.
    rewrite <- app_assoc. congruence.
  Qed.

  Ltac apply_value_compare_trans :=
    lazymatch goal with
      H: value_compare ?x ?y = Lt, H': value_compare ?y ?z = Lt |- _ =>
        pose proof (value_compare_trans _ _ _ H H')
    end.

  Ltac apply_value_compare_Eq_eq :=
    lazymatch goal with
      H: value_compare _ _ = Eq |- _ => apply value_compare_Eq_eq in H; subst
    end.

  Lemma bag_insert_bag_insert : forall (x y : value) b,
      StronglySorted bag_entry_leb b ->
      bag_insert x (bag_insert y b) = bag_insert y (bag_insert x b).
  Proof.
    induction b; cbn; intros.
    1:{ unfold value_ltb, value_eqb. case_match;
        repeat (rewrite value_compare_antisym; rewrite_l_to_r; cbn); auto.
        apply value_compare_Eq_eq in E; congruence. }
    1:{ unfold value_ltb, value_eqb. case_match.
        case_match; repeat (rewrite value_compare_antisym; rewrite_l_to_r; cbn);
          case_match;
          repeat apply_value_compare_Eq_eq; auto.
        all: try (cbn; unfold value_ltb, value_eqb; rewrite_l_to_r;
                  repeat (rewrite value_compare_antisym; rewrite_l_to_r; cbn);
                  rewrite value_compare_refl; auto).
        all: try (cbn; unfold value_ltb, value_eqb;
                  case_match; repeat (rewrite value_compare_antisym; rewrite_l_to_r; cbn);
                  repeat apply_value_compare_Eq_eq; auto); try congruence.
        1:{ apply_value_compare_trans; congruence. }
        1:{ rewrite value_compare_antisym, CompOpp_iff in E0; cbn in *.
            apply_value_compare_trans. clear_refl.
            repeat (rewrite value_compare_antisym; rewrite_l_to_r; cbn); auto. }
        1:{ clear_refl. rewrite_l_to_r. invert_SSorted. rewrite IHb; auto. } }
  Qed.

  Lemma list_to_bag_to_list_Permutation : forall (l : list value),
      Permutation (bag_to_list (list_to_bag l)) l.
  Proof.
    induction l; cbn; auto.
    pose proof (bag_to_list__bag_insert a (list_to_bag l)).
    repeat destruct_exists; destruct_and.
    rewrite_l_to_r.
    eapply perm_trans.
    1: eapply Permutation_sym, Permutation_middle.
    rewrite bag_to_list_app. rewrite_l_to_r.
    apply Permutation_cons; auto.
  Qed.

  Lemma Permutation_list_to_bag_eq : forall (l l' : list value),
      Permutation l l' ->
      list_to_bag l = list_to_bag l'.
  Proof.
    induction 1; cbn; auto; try congruence.
    apply bag_insert_bag_insert, list_to_bag_SSorted.
  Qed.

  Lemma lt_bag_insert : forall x (b : list (value * nat)),
      Forall (fun v => value_compare x (fst v) = Lt) b -> bag_insert x b = (x, 1) :: b.
  Proof.
    induction 1; cbn; auto.
    case_match; cbn in *. unfold value_ltb, value_leb.
    rewrite_l_to_r; auto.
  Qed.

  Lemma filter_bag_insert : forall P x (b : list (value * nat)),
      StronglySorted bag_entry_leb b ->
      filter (fun v => P (fst v)) (bag_insert x b) =
        if P x then bag_insert x (filter (fun v => P (fst v)) b)
        else filter (fun v => P (fst v)) b.
  Proof.
    induction b; cbn; intros.
    1: case_match; auto.
    case_match; cbn.
    unfold value_ltb, value_eqb. case_match.
    1:{ apply_value_compare_Eq_eq. cbn. case_match; cbn; auto.
        unfold value_ltb, value_eqb. rewrite value_compare_refl; auto. }
    1:{ do 2 case_match; cbn; unfold value_ltb, value_eqb; repeat rewrite_l_to_r; auto.
        erewrite lt_bag_insert; auto.
        eapply incl_Forall; eauto using incl_filter.
        invert_SSorted. unfold bag_entry_leb, value_leb, leb_from_compare in H3; cbn in *.
        rewrite Forall_forall; intros. apply_Forall_In.
        destruct_match_hyp; try discriminate;
          try apply_value_compare_Eq_eq; eauto using value_compare_trans. }
    1:{ invert_SSorted.
        do 2 case_match; cbn; unfold value_ltb, value_eqb; repeat rewrite_l_to_r; auto;
        rewrite IHb; auto. }
  Qed.

  Lemma filter_list_to_bag : forall P (l : list value),
      filter (fun v => P (fst v)) (list_to_bag l) = list_to_bag (filter P l).
  Proof.
    induction l; cbn; auto.
    rewrite filter_bag_insert; auto using list_to_bag_SSorted.
    rewrite IHl. case_match; auto.
  Qed.

  Section WithMap.
    Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    Lemma annotate_collection_preserve_ty : forall e Gstore Genv t,
        type_of Gstore Genv e t ->
        type_of Gstore Genv (annotate_collection e) t.
    Proof.
      destruct 1.
      all: try now (econstructor; eauto).
      1:{ cbn. case_match; try now (econstructor; eauto).
          invert_type_of_op. repeat econstructor; eauto. }
      1:{ cbn. repeat case_match; try now (econstructor; eauto).
          repeat invert_type_of_clear. invert_type_of_op.
          rewrite !Bool.andb_true_iff, Bool.negb_true_iff,
            !eqb_eq, eqb_neq in *; intuition idtac; subst.
          repeat rewrite_map_get_put_hyp.
          repeat clear_refl; do_injection.
          repeat econstructor; eauto. }
      1:{ cbn. repeat econstructor; eauto. }
    Qed.

    Lemma bag_to_list_preserve_SSorted : forall (b : list (value * nat)),
        StronglySorted bag_entry_leb b -> StronglySorted value_leb (bag_to_list b).
    Proof.
      induction b; cbn; auto using SSorted_nil.
      intros. invert_SSorted.
      induction (snd a); cbn; auto.
      constructor; auto.
      apply Forall_app; intuition idtac.
      1:{ rewrite Forall_forall; intros ? H_in.
          apply repeat_spec in H_in; subst.
          unfold value_leb, leb_from_compare. rewrite value_compare_refl; auto. }
      1:{ unfold bag_entry_leb in *. eapply incl_Forall.
          1: apply bag_to_list_incl.
          rewrite <- Forall_map_fst. assumption. }
    Qed.

    Lemma annotate_collection_preserve_sem : forall e (Gstore Genv : tenv) t (store env : locals),
        type_of Gstore Genv e t ->
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env (annotate_collection e) = interp_expr store env e.
      destruct 1; auto; intros; cbn.
      1:{ case_match; auto. cbn; case_match; auto.
          erewrite List.fold_right_change_order;
            [ | auto | apply list_to_bag_to_list_Permutation ].
          lazymatch goal with
            H: _ = VList _ |- _ => clear H
          end.
          induction l; cbn; auto.
          rewrite IHl. f_equal. rewrite Zpos_P_of_succ_nat. case_match; auto.
          destruct p; auto. }
      1:{ repeat (case_match; auto; cbn; []).
          rewrite !Bool.andb_true_iff, Bool.negb_true_iff, !eqb_eq, eqb_neq in *.
          intuition idtac; subst.
          erewrite List.fold_right_change_order;
            [
            | clear; intros; unfold apply_int_binop;
              repeat case_match; auto; rewrite Z.add_shuffle3; reflexivity
            | apply list_to_bag_to_list_Permutation ].
          lazymatch goal with
            H: _ = VList _ |- _ => clear H
          end.
          unfold get_local. induction l; cbn; auto.
          rewrite IHl. repeat rewrite_map_get_put_goal.
          congruence. }
      1:{ case_match; auto. f_equal.
          apply Permutation_SSorted_eq;
            auto using bag_to_list_preserve_SSorted, list_to_bag_SSorted, StronglySorted_value_sort.
          eapply perm_trans; [ apply list_to_bag_to_list_Permutation | apply Permuted_value_sort ]. }
    Qed.

    Lemma bag_of_ty : forall e Gstore Genv t,
        type_of Gstore Genv e (TList t) ->
        type_of Gstore Genv (bag_of e) (TBag t).
    Proof.
      induction e using expr_IH; cbn; intros.
      all: try now (econstructor; eauto).
      all: case_match; invert_type_of; econstructor; eauto.
    Qed.

    Definition VBag_of (v : value) :=
      match v with
      | VList l => VBag (list_to_bag l)
      | _ => VUnit
      end.

    Lemma bag_of_sem : forall e (Gstore Genv : tenv) t,
        type_of Gstore Genv e (TList t) ->
        forall (store env : locals),
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env (bag_of e) = VBag_of (interp_expr store env e).
    Proof.
      induction 1; unfold VBag_of in *; auto; intros.
      1:{ cbn. rewrite IHtype_of1; auto. case_match; auto. f_equal.
          apply Permutation_list_to_bag_eq. apply Utils.Permutation_flat_map; intros;
            auto using list_to_bag_to_list_Permutation.
          apply_type_sound e1. rewrite_l_to_r. invert_type_of_value.
          eapply Permutation_in in H5; [ | apply list_to_bag_to_list_Permutation ].
          apply_Forall_In. erewrite IHtype_of2; eauto with fiat2_hints.
          apply_type_sound e2; eauto with fiat2_hints. invert_type_of_value.
          apply list_to_bag_to_list_Permutation. }
      1:{ cbn. rewrite IHtype_of1; auto. case_match; auto. f_equal.
          apply filter_list_to_bag with
            (P:=fun v : value => match interp_expr store (map.put env x v) p with
                                 | VBool b => b
                                 | _ => false
                                 end). }
      1:{ cbn. rewrite IHtype_of1, IHtype_of2; auto. repeat (case_match; auto). f_equal.
          auto using Permutation_list_to_bag_eq, Utils.Permutation_flat_map,
            list_to_bag_to_list_Permutation, Permutation_map, Permutation_filter. }
      1:{ cbn. rewrite IHtype_of1; auto. case_match; auto. f_equal.
          auto using Permutation_list_to_bag_eq, Permutation_map, list_to_bag_to_list_Permutation. }
    Qed.

    Lemma push_down_collection_preserve_ty : forall e Gstore Genv t,
        type_of Gstore Genv e t ->
        type_of Gstore Genv (push_down_collection e) t.
    Proof.
      destruct 1.
      all: try now (econstructor; eauto).
      cbn. auto using bag_of_ty.
    Qed.

    Lemma push_down_collection_preserve_sem : forall e (Gstore Genv : tenv) t (store env : locals),
        type_of Gstore Genv e t ->
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env (push_down_collection e) = interp_expr store env e.
    Proof.
      destruct 1; auto; cbn; intros.
      erewrite bag_of_sem; eauto.
    Qed.
  End WithMap.
End WithWord.










(* ??? Modified DictIndexImpl.v *)
Require Import fiat2.Substitute fiat2.IndexInterface2.
Require Import coqutil.Datatypes.Result.
Open Scope string_scope.

Section WithHole.
  Context (tbl : string).
  Context (hole : string).
  Context (attr : string).

  Section WithVars.
    Context (tup acc x k v : string).
    Context (H_NoDup : is_NoDup_opaque [tup; acc; x; k; v]).

    (* Materialize tbl (expected to be a list of records) into an index over attr *)
    Definition to_idx : expr :=
      let k := EAccess (EVar tup) attr in
      EFold (EVar hole) (EAtom (AEmptyDict None)) tup acc
        (ETernop OInsert (EVar acc) k
           (EOptMatch (EBinop OLookup (EVar acc) k)
              (epair enil (EVar tup))
              x (cons_to_fst (EVar tup) (EVar x)))).

    Definition is_tbl_ty (t : type) : bool :=
      match t with
      | TList (TRecord rt) => inb (String.eqb) attr (List.map fst rt)
      | _ => false
      end.

    (* An index is a dictionary with each of its keys mapped to at least one row of the table *)
    Definition index_type (kt : type) (rt : list (string * type)) :=
      TDict kt (TRecord [("0", TList (TRecord rt)); ("1", TRecord rt)]).

    Definition idx_ty (t : type) : type :=
      match t with
      | TList (TRecord rt) => index_type (get_attr_type rt attr) rt
      | _ => TUnit
      end.

    Lemma idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t).
      destruct t; simpl; intros; try congruence.
      destruct t; try congruence. unfold index_type.
      inversion H; subst. inversion H2; subst. repeat constructor; intuition auto.
      1: apply get_attr_type_ty_wf; auto.
      1:{ simpl in *; intuition idtac. congruence. }
    Qed.

    Section WithMap.
      Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
      Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
      Notation value := (value (width:=width)).
      Context {locals : map.map string value} {locals_ok : map.ok locals}.
      Notation sem_eq := (sem_eq (locals:=locals)).

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
        1,2: repeat econstructor; auto; repeat rewrite_map_get_put_goal; use_is_NoDup.
      Qed.

      Definition index_wf (l : list (value * value)) :=
        Forall (fun p => match snd p with
                         | VRecord r =>
                             match access_record r "0" with
                             | Success (VList l) =>
                                 Forall (fun r => match r with
                                                  | VRecord r => access_record r attr = Success (fst p)
                                                  | _ => False
                                                  end) l
                             | _ => False
                             end /\
                               match access_record r "1" with
                               | Success (VRecord r) => access_record r attr = Success (fst p)
                               | _ => False
                               end
                         | _ => False
                         end) l.

      Lemma index_wf_step_inv : forall p idx,
          index_wf (p :: idx) -> index_wf idx.
      Proof.
        intros. unfold index_wf in *. invert_Forall; auto.
      Qed.

      Definition idx_wf (v : value) :=
        match v with
        | VDict l => index_wf l
        | _ => False
        end.

      Ltac swap_record_map_fst :=
        lazymatch goal with
          H: Forall2 _ _ _ |- _ => apply Forall2_split in H end; destruct_and;
        rewrite Forall2_fst_eq in *;
        lazymatch goal with
          H: map fst _ = _ |- _ => rewrite <- H in * end.

      Lemma dict_lookup__In : forall k l (v : value), dict_lookup k l = Some v -> In (k, v) l.
      Proof.
        induction l; simpl; intros.
        1: congruence.
        repeat destruct_match_hyp; intuition auto. do_injection.
        left; f_equal; symmetry; auto using value_eqb_eq.
      Qed.

      Lemma fold_right_invariant : forall (A B : Type) (a : A) (l : list B) (f : B -> A -> A) (P : A -> Prop),
          P a -> (forall (a : A) (b : B), P a -> In b l -> P (f b a)) ->
          P (fold_right f a l).
      Proof.
        intros. assert(fold_right f a l = fold_right f a l /\ P (fold_right f a l)).
        { auto using In_fold_right_ext'. }
        intuition auto.
      Qed.

      Lemma to_idx_wf : forall (v : value) (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          idx_wf (interp_expr map.empty (map.put map.empty hole v) to_idx).
      Proof.
        unfold is_tbl_ty; intros; simpl in * |-.
        repeat destruct_match_hyp; try discriminate.
        simpl. unfold get_local; rewrite_map_get_put_goal.
        invert_type_of_value.
        apply fold_right_invariant.
        1:{ unfold dict_sort, Mergesort.Sectioned.sort, idx_wf, index_wf; simpl; auto. }
        1:{ intros; apply_Forall_In.
            repeat rewrite_map_get_put_goal; try now use_is_NoDup.
            unfold idx_wf in *. destruct_match_hyp; auto.
            repeat invert_type_of_value_clear.
            unfold index_wf. eapply incl_Forall.
            1: apply dict_insert_incl.
            swap_record_map_fst.
            apply_In_access_record; destruct_exists.
            constructor; auto; simpl. case_match; simpl.
            1:{ repeat rewrite_map_get_put_goal; try now use_is_NoDup.
                unfold index_wf in *. apply dict_lookup__In in E.
                apply_Forall_In; simpl in *. unfold record_proj.
                case_match; auto.
                intuition auto; case_match; auto.
                case_match; auto. constructor; auto.
                repeat rewrite_l_to_r; auto. }
            1:{ split; auto. unfold record_proj. repeat rewrite_l_to_r; auto. } }
      Qed.

      Definition vcons_to_fst (v p : value) : value :=
        VRecord [("0", match p with
                       | VRecord p =>
                           match record_proj "0" p with
                           | VList l => VList (v :: l)
                           | _ => VUnit
                           end
                       | _ => VUnit
                       end);
                 ("1", match p with
                       | VRecord p => record_proj "1" p
                       | _ => VUnit
                       end)].

      Definition gallina_to_idx (v0 : value) : list (value * value) :=
        match v0 with
        | VList l =>
            fold_right
              (fun v acc => match v with
                            | VRecord v =>
                                dict_insert (record_proj attr v)
                                  (match dict_lookup (record_proj attr v) acc with
                                   | Some p => vcons_to_fst (VRecord v) p
                                   | None => VRecord [("0", VList nil); ("1", VRecord v)]
                                   end) acc
                            | _ => nil
                            end) nil l
        | _ => nil
        end.

      Lemma fiat2_gallina_to_idx : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          interp_expr map.empty (map.put map.empty hole v) to_idx = VDict (gallina_to_idx v).
      Proof.
        unfold is_tbl_ty; intros. repeat destruct_match_hyp; try discriminate.
        invert_type_of_value_clear; simpl.
        unfold get_local; rewrite_map_get_put_goal.
        erewrite In_fold_right_ext with
          (P := fun a => match a with VDict _ => True | _ => False end)
          (g := fun v1 v2 => match v1, v2 with
                             | VRecord l1, VDict l0 =>
                                 VDict
                                   (dict_insert (record_proj attr l1)
                                      match dict_lookup (record_proj attr l1) l0 with
                                      | Some v0 =>
                                          VRecord
                                            [("0",
                                               match
                                                 match v0 with
                                                 | VRecord l2 => record_proj "0" l2
                                                 | _ => VUnit
                                                 end
                                               with
                                               | VList l2 => VList (VRecord l1 :: l2)
                                               | _ => VUnit
                                               end);
                                             ("1",
                                               match v0 with
                                               | VRecord l2 => record_proj "1" l2
                                               | _ => VUnit
                                               end)]
                                      | None => VRecord (record_sort [("0", VList []); ("1", VRecord l1)])
                                      end l0)
                             | _, _ => VUnit
                             end); auto.
        1:{ induction l0; simpl; auto. invert_Forall. invert_type_of_value_clear.
            rewrite IHl0; auto. do 2 f_equal. case_match; auto.
            unfold vcons_to_fst. repeat f_equal. case_match; auto. }
        1:{ intros. apply_Forall_In; invert_type_of_value_clear.
            repeat rewrite_map_get_put_goal; try now use_is_NoDup.
            destruct_match_hyp; split; try now (intuition auto).
            do 2 f_equal. case_match; auto. f_equal.
            unfold record_sort, Mergesort.Sectioned.sort; simpl.
            do 2 f_equal.
            1:{ rewrite_map_get_put_goal. case_match; auto.
                case_match; auto. repeat rewrite_map_get_put_goal; use_is_NoDup. }
            1:{ f_equal. rewrite_map_get_put_goal; auto. } }
      Qed.

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
        congruence.

      Lemma fold_to_idx : forall Gstore Genv t e x0 tup0 acc0 free_vars,
          is_NoDup [x0; tup0; acc0] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          is_tbl_ty t = true ->
          type_of Gstore Genv e t ->
          incl (get_free_vars Genv) free_vars ->
          sem_eq Gstore Genv (idx_ty t)
            (EFold e (EAtom (AEmptyDict None)) tup0 acc0
               (ETernop OInsert (EVar acc0) (EAccess (EVar tup0) attr) (EOptMatch (EBinop OLookup (EVar acc0) (EAccess (EVar tup0) attr)) (epair enil (EVar tup0)) x0 (cons_to_fst (EVar tup0) (EVar x0)))))
            (substitute [(hole, e)] free_vars to_idx).
      Proof.
        unfold sem_eq, is_tbl_ty; intros.
        repeat destruct_match_hyp; try discriminate; subst.
        intuition idtac.
        1:{ unfold idx_ty, index_type in *. lazymatch goal with
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
            lazymatch goal with
              |- context[match ?x with _ => _ end] =>
                destruct x; auto
            end. repeat f_equal.
            all: repeat (rewrite_map_get_put_goal; try now use_is_NoDup); reflexivity. }
        6-8: eauto.
        all: auto.
        2: use_to_idx_ty.
        all: eauto using idx_ty_wf with fiat2_hints.
        prove_sub_wf.
      Qed.

      Lemma fiat2_gallina_to_idx2: forall (store env : locals) v t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          map.get env hole = Some v ->
          interp_expr store env to_idx = VDict (gallina_to_idx v).
      Proof.
        intros.
        erewrite interp_expr_strengthen.
        1: eapply fiat2_gallina_to_idx.
        6: apply to_idx_ty.
        all: eauto with fiat2_hints.
        2: eapply map_incl_step_l; eauto using Decidable.String.eqb_spec.
        all: apply map_incl_empty.
      Qed.

      Lemma fiat2_gallina_to_idx_sem : forall Gstore Genv store env e t free_vars,
          tenv_wf Gstore -> tenv_wf Genv ->
          is_tbl_ty t = true ->
          type_of Gstore Genv e t ->
          locals_wf Gstore store -> locals_wf Genv env ->
          incl (get_free_vars Genv) free_vars ->
          interp_expr store env (substitute [(hole, e)] free_vars to_idx) = VDict (gallina_to_idx (interp_expr store env e)).
      Proof.
        intros. erewrite substitute_preserve_sem.
        1:{ erewrite fiat2_gallina_to_idx2; eauto with fiat2_hints.
            simpl. rewrite_map_get_put_goal. auto. }
        6-8: eauto.
        all: auto.
        2: use_to_idx_ty.
        all: eauto with fiat2_hints.
        prove_sub_wf.
      Qed.

      Lemma gallina_to_idx_ty : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          type_of_value (VDict (gallina_to_idx v)) (idx_ty t).
      Proof.
        intros. erewrite <- fiat2_gallina_to_idx; eauto.
        eapply type_sound; eauto using to_idx_ty with fiat2_hints.
      Qed.

      Fixpoint concat_VList_V (l : list value) :=
        match l with
        | VRecord l' :: l => match record_proj "0" l' with
                             | VList vl => (vl ++ (record_proj "1" l' :: concat_VList_V l))%list
                             | _ => nil
                             end
        | _ => nil
        end.

      Definition has_index_entry_shape (p : value * value) :=
        match snd p with
        | VRecord r =>
            match record_proj "0" r with
            | VList _ => True | _ => False end
        | _ => False end.

      Local Coercion is_true : bool >-> Sortclass.

      Lemma dict_insert_lookup_Permutation :
        forall k d v, Forall has_index_entry_shape d ->
                      StronglySorted dict_entry_leb d ->
                      Permutation
                        (concat_VList_V
                           (List.map snd
                              (dict_insert k
                                 match dict_lookup k d with
                                 | Some p => vcons_to_fst v p
                                 | None =>
                                     VRecord [("0", VList []); ("1", v)]
                                 end d)))
                        (v :: (concat_VList_V (List.map snd d))).
      Proof.
        unfold has_index_entry_shape; intros.
        induction d; simpl; auto.
        case_match. simpl. invert_Forall; subst; simpl in *.
        do 2 destruct_match_hyp; try now (intuition auto).
        unfold value_eqb, value_ltb. case_match; cbn; auto.
        all: rewrite_l_to_r; auto.
        all: invert_SSorted; subst.
        - rewrite dict_lookup_Lt; auto. intros p H_in. apply_Forall_In.
          unfold dict_entry_leb, value_leb, leb_from_compare in *; simpl in *.
          destruct_match_hyp; try congruence.
          + lazymatch goal with
              E: value_compare _ _ = Eq |- _ =>
                apply value_compare_Eq_eq in E end; subst; auto.
          + eapply value_compare_trans; eauto.
        - apply Permutation_cons_app_cons; auto.
      Qed.

      Lemma gallina_list_to_idx_shape : forall l rt,
          Forall (fun v => type_of_value v (TRecord rt)) l ->
          In attr (List.map fst rt) ->
          Forall has_index_entry_shape (gallina_to_idx (VList l)).
      Proof.
        intros * H_ty H_in. induction H_ty; simpl; auto.
        invert_type_of_value.
        specialize (dict_insert_incl (width:=width)) as H_ins.
        eapply incl_Forall; eauto.
        constructor; intuition. simpl. unfold has_index_entry_shape in *.
        lazymatch goal with
        | |- context[dict_lookup ?k ?d] => destruct (dict_lookup k d) eqn:E
        end; simpl; auto.
        eapply Forall_dict_lookup in IHH_ty; simpl in IHH_ty; eauto.
        repeat destruct_match_hyp; auto.
      Qed.

      Lemma gallina_list_to_idx_SSorted : forall l rt,
          Forall (fun v => type_of_value v (TRecord rt)) l ->
          In attr (List.map fst rt) ->
          StronglySorted dict_entry_leb (gallina_to_idx (VList l)).
      Proof.
        intros; induction l; simpl; try constructor.
        invert_Forall. invert_type_of_value_clear.
        apply dict_insert_preserve_SSorted; auto.
      Qed.

      Lemma idx_wf__has_index_entry_shape : forall l,
          idx_wf (VDict l) -> Forall has_index_entry_shape l.
      Proof.
        unfold idx_wf, index_wf; intros. rewrite Forall_forall.
        intros. apply_Forall_In. unfold has_index_entry_shape.
        destruct_match_hyp; auto. unfold record_proj.
        repeat destruct_match_hyp; intuition auto.
      Qed.

      Lemma dict_insert_Lt : forall k (v : value) d,
          (forall p, In p d -> value_compare k (fst p) = Lt) ->
          dict_insert k v d = (k, v) :: d.
      Proof.
        destruct d; simpl; auto; intros.
        repeat case_match; auto.
        all: lazymatch goal with
               H: forall _, (?k, ?v) = _ \/ _ -> _ |- _ => specialize H with (k, v)
             end;
          simpl in *; intuition.
        1:{ lazymatch goal with
            H: value_eqb _ _ = true |- _ => apply value_eqb_eq in H; subst
          end.
            rewrite value_compare_refl in *; congruence. }
        1:{ unfold value_ltb in *.
            lazymatch goal with
              H: context[match ?x with _ => _ end], E: ?x = _ |- _ => rewrite E in H
            end. congruence. }
      Qed.

      Instance dict_idx : IndexInterface2.index := IndexInterface2.mk hole to_idx idx_ty is_tbl_ty.

      Instance dict_idx_ok : IndexInterface2.ok dict_idx idx_wf := IndexInterface2.Build_ok dict_idx idx_wf idx_ty_wf to_idx_ty to_idx_wf.

      Notation eto_idx tup0 tup1 tup2 tup3 tup4 acc0 acc1 acc2 x0 x1 x2 attr0 attr1 d :=
        (EFold d (EAtom (AEmptyDict None)) tup0 acc0
           (ETernop OInsert (EVar acc1) (EAccess (EVar tup1) attr0) (EOptMatch (EBinop OLookup (EVar acc2) (EAccess (EVar tup2) attr1)) (ERecord [("0", EAtom (ANil None)); ("1", EVar tup3)]) x0 (ERecord [("0", EBinop OCons (EVar tup4) (EAccess (EVar x1) "0")); ("1", EAccess (EVar x2) "1")] )))).

      Ltac rewrite_l_to_r_goal :=
        multimatch goal with H: ?x = _ |- context[?x] => rewrite H end.

      Section eq_filter_to_lookup.
        Context (p : string).

        Definition eq_filter_to_lookup_head (tbl : string) (e : expr) :=
          (* filter (idx_to_list idx) (fun row => row.attr == e') -->
           match (lookup idx e') with none => nil | some p => fst p ++ [snd p] *)
          match e with
          | EFilter LikeBag
              (ELoc tbl0)
              x
              (EBinop OEq (EAccess (EVar x0) attr0) e') =>
              if (all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x, [x0])] &&
                    negb (free_immut_in x e'))%bool
              then EBagOf (EOptMatch (EBinop OLookup (substitute [(hole, ELoc tbl)] [] to_idx) e')
                             enil
                             p (EBinop OConcat (ofst (EVar p)) (econs (osnd (EVar p)) enil)))
              else e
          | _ => e
          end.

        Lemma eq_filter_to_lookup_head_preserve_ty : forall tbl t (Gstore : tenv),
            type_wf t -> is_tbl_ty t ->
            map.get Gstore tbl = Some (idx_ty t) ->
            preserve_ty Gstore (eq_filter_to_lookup_head tbl).
        Proof.
          clear H_NoDup.
          unfold preserve_ty, is_tbl_ty. intros.
          repeat destruct_match_hyp; try congruence.
          repeat destruct_subexpr. simpl.
          case_match; auto. repeat rewrite Bool.andb_true_r in *.
          repeat rewrite Bool.andb_true_iff in *; intuition. rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
          repeat invert_type_of_clear. repeat invert_type_of_op_clear. repeat rewrite_map_get_put_hyp.
          repeat (clear_refl; repeat do_injection2).
          repeat (econstructor; eauto).
          1:{ lazymatch goal with H: ?x = _, H': ?x = _ |- _ => rewrite H in H' end.
              do_injection2. simpl in *; do_injection2.
              unfold get_attr_type. lazymatch goal with H: ?x = _ |- context[?x] => rewrite H end.
              eapply not_free_immut_put_ty; eauto. }
          all: rewrite map.get_put_same; trivial.
        Qed.

        Definition gallina_filter_access_eq (s : string) (v0 : value) (l : list value) :=
          filter (fun v => value_eqb match v with
                             | VRecord r => record_proj s r
                             | _ => VUnit
                             end v0) l.

        Lemma fiat2_gallina_filter_access_eq :
          forall (store env : locals) e1 e2 x s l,
            interp_expr store env e1 = VList l ->
            free_immut_in x e2 = false ->
            interp_expr store env (EFilter e1 x (EBinop OEq (EAccess (EVar x) s) e2)) =
              VList (gallina_filter_access_eq s (interp_expr store env e2) l).
        Proof.
          intros * H1 H_free; simpl. rewrite H1. f_equal. apply filter_ext. intro a.
          unfold get_local. rewrite map.get_put_same. rewrite <- not_free_immut_put_sem; auto.
        Qed.

        Lemma gallina_from_idx_cons : forall a idx,
            index_wf (a :: idx) ->
            gallina_from_idx (VDict (a :: idx)) = List.app (gallina_from_idx (VDict [a])) (gallina_from_idx (VDict idx)).
        Proof.
          unfold index_wf. destruct a; simpl.
          intros. invert_Forall; simpl in *.
          case_match; intuition auto. unfold record_proj.
          repeat (case_match; intuition auto).
          rewrite <- app_assoc. f_equal; auto.
        Qed.

        Lemma dict_lookup__filter_none : forall k idx,
            index_wf idx ->
            dict_lookup k idx = None ->
            gallina_filter_access_eq attr k (gallina_from_idx (VDict idx)) = nil.
        Proof.
          unfold gallina_filter_access_eq, gallina_from_idx, record_proj.
          intros. induction idx; simpl; auto. unfold record_proj.
          destruct a; simpl in *. case_match; auto.
          inversion H; subst; simpl in *.
          destruct (access_record l "0"); intuition; destruct a; intuition.
          destruct (access_record l "1"); intuition; destruct a; intuition.
          rewrite filter_app. destruct (value_eqb k0 v0) eqn:E.
          1: congruence. simpl.
          rewrite H3; auto.
          repeat rewrite_l_to_r. rewrite value_eqb_sym, E, app_nil_r.
          lazymatch goal with
          | H: Forall _ l0 |- _ => induction H; simpl; auto end. rewrite IHForall.
          case_match; intuition. rewrite_l_to_r. rewrite value_eqb_sym, E. reflexivity.
        Qed.

        Lemma dict_lookup__filter_some : forall k idx kt vt l v,
            index_wf idx ->
            type_of_value (VDict idx) (TDict kt vt) ->
            dict_lookup k idx = Some (VRecord [("0", VList l); ("1", v)]) ->
            gallina_filter_access_eq attr k (gallina_from_idx (VDict idx)) = (l ++ [v])%list.
        Proof.
          intros. unfold gallina_filter_access_eq.
          induction idx.
          1: unfold dict_lookup in *; discriminate.
          rewrite gallina_from_idx_cons; auto.
          rewrite filter_app.
          destruct a. invert_type_of_value.
          simpl. unfold index_wf in *.
          repeat invert_Forall; simpl in *.
          repeat (destruct_match_hyp; intuition auto);
            [ lazymatch goal with
                E: value_eqb _ _ = _ |- _ =>
                  apply value_eqb_eq in E; subst
              end
            | ].
          1:{ rewrite <- app_nil_r. f_equal.
              1:{ do_injection. cbn.
                  apply forallb_filter_id. rewrite forallb_app.
                  simpl in *. repeat do_injection.
                  rewrite Bool.andb_true_iff; split.
                  1:{ rewrite forallb_forall; intros.
                      apply_Forall_In. destruct_match_hyp; intuition auto.
                      unfold record_proj; rewrite_l_to_r_goal; apply value_eqb_refl. }
                  1:{ simpl. unfold record_proj; rewrite_l_to_r_goal.
                      rewrite Bool.andb_true_r; apply value_eqb_refl. } }
              1:{ apply dict_lookup__filter_none; auto.
                  apply not_In__dict_lookup.
                  invert_NoDup; auto. } }
          1:{ rewrite <- app_nil_l. f_equal.
              1:{ apply Forall_false__filter.
                  rewrite Forall_forall; intros.
                  unfold record_proj in *; repeat rewrite_l_to_r.
                  lazymatch goal with
                    H: In _ (_ ++ _) |- _ => apply in_app_or in H end.
                  intuition auto.
                  1:{ apply_Forall_In. destruct_match_hyp; intuition auto.
                      rewrite_l_to_r; eauto using value_eqb_sym. }
                  1:{ lazymatch goal with
                      H: In _ (_ :: nil) |- _ => inversion H; subst;
                                                 [ | exfalso; eapply in_nil; eauto ] end.
                      rewrite_l_to_r; eauto using value_eqb_sym. } }
              1:{ apply H7; auto.
                  invert_NoDup; invert_SSorted; constructor; auto. } }
        Qed.

        Lemma eq_filter_to_lookup_head_preserve_sem : forall tbl (Gstore : tenv) (store : locals) t,
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (idx_ty t) ->
            holds_for_all_entries (index_wf_with_globals [tbl]) store ->
            preserve_sem Gstore store (eq_filter_to_lookup_head tbl).
        Proof.
          unfold preserve_sem; intros. unfold holds_for_all_entries, index_wf_with_globals in *.
          unfold is_tbl_ty, idx_ty in *. do 2 (destruct_match_hyp; try discriminate).
          lazymatch goal with
            H: context[get_attr_type] |- _ =>
              let H_tbl_ty := fresh "H_tbl_ty" in
              eapply TyELoc in H as H_tbl_ty
          end. apply_type_sound (ELoc tbl). invert_type_of_value.
          assert(H_wf: index_wf l0).
          { symmetry in H8. unfold get_local in H8. destruct_match_hyp; try discriminate.
            apply H2 in E. unfold value_wf_with_globals in *.
            rewrite Forall_forall in E. specialize (E tbl). destruct E; simpl; intuition auto.
            simpl in *. unfold idx_wf in *. subst. auto. }
          repeat destruct_subexpr. unfold eq_filter_to_lookup_head.
          lazymatch goal with |- context[if ?x then _ else _] => destruct x eqn:E' end; auto.
          repeat rewrite Bool.andb_true_r in *. simpl in E'.
          repeat rewrite Bool.andb_true_iff in E'; intuition.
          rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
          repeat invert_type_of_clear. repeat invert_type_of_op_clear.
          repeat rewrite_map_get_put_hyp.
          repeat do_injection2. symmetry. erewrite sem_eq_eq.
          3,4: eauto.
          2:{ unfold sem_eq. eapply EFilter_Proper; auto.
              2: apply singleton_rel_refl.
              2:{ apply sem_eq_refl. repeat (econstructor; eauto).
                  rewrite_map_get_put_goal; auto. }
              apply fold_from_idx; simpl; intuition auto.
              1: constructor; auto.
              1:{ rewrite inb_true_iff.
                  lazymatch goal with
                    H: access_record ?tl ?attr = Success _ |- In ?attr (List.map fst ?tl) =>
                      apply access_record_sound, in_map with (f:=fst) in H
                  end. auto. }
              1:{ constructor.
                  lazymatch goal with
                    H1: map.get ?Gstore ?tbl = _, H2: map.get ?Gstore ?tbl = _ |- _ =>
                      rewrite H1 in H2; unfold index_type in H2
                  end.
                  repeat (clear_refl; repeat do_injection).
                  simpl in *; repeat do_injection. auto. } }
          erewrite fiat2_gallina_filter_access_eq; auto.
          2:{ erewrite fiat2_gallina_from_idx_sem with (t:=TList (TRecord l)); simpl.
              3-9: eauto. all: try constructor; auto. }
          simpl in H'; simpl.
          lazymatch goal with H: _ = ?x |- context[?x] => rewrite <- H in * end.
          specialize (dict_lookup_sound (width:=width) l0) as H_lookup.
          eapply (H_lookup _ _ (interp_expr store env e2_2)) in H'; eauto.
          2:{ unfold get_attr_type. lazymatch goal with
              H: ?x = _, H': ?x = _ |- _ => rewrite H in H'
            end. repeat (clear_refl; repeat do_injection).
              simpl in *; repeat do_injection2. simpl in *; do_injection2. rewrite_l_to_r.
              lazymatch goal with
                H: context[free_immut_in] |- _ =>
                  eapply not_free_immut_put_ty in H; eauto
              end.
              eapply type_sound; resolve_locals_wf;
                try lazymatch goal with H: ?x = _ |- context[?x] => rewrite H end; auto. }
          inversion H'; subst.
          2: unfold get_local; rewrite map.get_put_same.
          (* dict_lookup found no match *)
          1:{ f_equal; apply dict_lookup__filter_none; auto. }
          (* dict_lookup found some match *)
          1:{ lazymatch goal with
              H: type_of_value ?v _ |- context[?v] => inversion H; subst end.
              repeat invert_Forall2.
              destruct x1, x2; repeat destruct_and; simpl in * |-; subst.
              unfold record_proj, access_record. repeat rewrite String.eqb_refl.
              lazymatch goal with
                H: type_of_value v1 _ |- _ => inversion H; subst end.
              f_equal. case_match; simpl in * |-; try congruence.
              eapply dict_lookup__filter_some; eauto; try congruence.
              constructor. 3-5: eauto.
              all: auto. }
        Qed.

        Lemma eq_filter_to_lookup_head_sound : expr_aug_transf_sound (idx_wf:=idx_wf) eq_filter_to_lookup_head.
        Proof.
          unfold expr_aug_transf_sound; intros.
          invert_tenv_wf_with_globals. intuition idtac.
          1: eapply eq_filter_to_lookup_head_preserve_ty; eauto.
          1: eapply eq_filter_to_lookup_head_preserve_sem; eauto.
        Qed.
      End eq_filter_to_lookup.

      Section neq_filter_to_delete.
        Definition neq_filter_to_delete_head (tbl : string) (e : expr) :=
          (* list_to_idx (filter (idx_to_list idx) (fun row => row.attr != e)) = delete idx e *)
          match e with
          | elist_to_idx tup0 tup1 tup2 tup3 tup4 acc0 acc1 acc2 x0 x1 x2 attr0 attr1
              ((efilter_neq y0 y1 attr2 k' (eidx_to_list k0 v0 v1 v2 acc3 acc4 (ELoc tbl0))))
            => if (all_eqb [(tbl, [tbl0]); (v0,[v1; v2]); (acc0, [acc1; acc2; acc3; acc4]); (y0, [y1]); (tup0, [tup1; tup2; tup3; tup4]); (attr, [attr0; attr1; attr2]); (x0, [x1; x2])] &&
                     all_neqb [acc0; tup0; v0; k0; x0] &&
                     negb (free_immut_in y0 k'))%bool
               then EBinop ODelete (ELoc tbl) k'
               else e
          | _ => e
          end.

        Lemma neq_filter_to_delete_head_preserve_ty : forall tbl t (Gstore : tenv),
            type_wf t -> is_tbl_ty t ->
            map.get Gstore tbl = Some (idx_ty t) ->
            preserve_ty Gstore (neq_filter_to_delete_head tbl).
        Proof.
          clear H_NoDup.
          unfold is_tbl_ty, preserve_ty; intros.
          repeat destruct_match_hyp; try congruence.
          repeat destruct_subexpr. simpl.
          repeat (case_match; auto).
          repeat rewrite Bool.andb_true_r in *. repeat rewrite Bool.andb_true_iff in *; intuition idtac.
          rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
          repeat invert_type_of_clear. repeat invert_type_of_op_clear.
          repeat rewrite_map_get_put_hyp. repeat (clear_refl; repeat do_injection2).
          repeat econstructor; auto.
          1:{ lazymatch goal with
              H: map.get Gstore tbl = _, H': map.get Gstore tbl = _ |- _ =>
                rewrite H in *; do_injection2; simpl in *; do_injection2
            end.
              unfold get_attr_type.
              lazymatch goal with
              | H1: ?x = _, H2: ?x = _ |- _ => rewrite H1 in H2 end.
              do_injection2; rewrite_l_to_r_goal.
              repeat invert_type_of_op_clear.
              repeat clear_refl. unfold index_type. do 3 f_equal.
              repeat invert_Forall2. repeat invert_type_of_clear.
              repeat invert_type_of_op_clear; repeat rewrite_map_get_put_hyp.
              repeat rewrite_l_to_r; repeat (try clear_refl; do_injection).
              do 3 (destruct tl0; simpl in *; try congruence). destruct p, p0; simpl in *.
              do 3 (destruct tl; simpl in *; try congruence). destruct p, p0; simpl in *.
              repeat (lazymatch goal with
                        H: cons _ _ = cons _ _ |- _ => inversion H; subst; auto end;
                      clear_refl).
              multimatch goal with
                H: Permutation _ _ |- _ => apply Permutation_length_2_inv in H; destruct H end.
              all: lazymatch goal with
                     H: _ = cons _ _ |- _ => inversion H; subst; auto end.
              2:{ invert_SSorted. invert_Forall. unfold record_entry_leb in *; simpl in *.
                  lazymatch goal with H: is_true (_ <=? _) |- _ => inversion H end. }
              simpl in *; do_injection2. auto. }
          1:{ repeat lazymatch goal with
                  H: ?x = _, H': ?x = _ |- _ => rewrite H in H'
                end. repeat (clear_refl; repeat do_injection2).
              eapply not_free_immut_put_ty; eauto. }
        Qed.

        Definition gallina_filter_access_neq (s : string) (v0 : value) (l : list value) :=
          filter (fun v => negb (value_eqb match v with
                                   | VRecord r => record_proj s r
                                   | _ => VUnit
                                   end v0)) l.

        Lemma fiat2_gallina_filter_access_neq :
          forall (store env : locals) e1 e2 x s l,
            interp_expr store env e1 = VList l ->
            free_immut_in x e2 = false ->
            interp_expr store env (EFilter e1 x (EUnop ONot (EBinop OEq (EAccess (EVar x) s) e2))) =
              VList (gallina_filter_access_neq s (interp_expr store env e2) l).
        Proof.
          intros * H1 H_free; simpl. rewrite H1. f_equal. apply filter_ext. intro a.
          unfold get_local. rewrite map.get_put_same. rewrite <- not_free_immut_put_sem; auto.
        Qed.

        Lemma gallina_filter_access_neq_from_idx : forall k idx kt vt,
            idx_wf (VDict idx) ->
            type_of_value (VDict idx) (TDict kt vt) ->
            gallina_filter_access_neq attr k (gallina_from_idx (VDict idx)) = gallina_from_idx (VDict (dict_delete k idx)).
        Proof.
          intros * H. simpl. unfold record_proj; induction idx; auto.
          simpl. unfold idx_wf, index_wf in *; invert_Forall. destruct_match_hyp; intuition auto; simpl in *.
          repeat destruct_match_hyp; intuition auto. repeat rewrite_l_to_r.
          destruct a; simpl in *.
          unfold gallina_filter_access_neq in *. rewrite filter_app. simpl. rewrite_l_to_r.
          invert_type_of_value; simpl in *; invert_Forall; invert_NoDup; invert_SSorted.
          destruct (value_eqb k0 v0) eqn:E_k0v0.
          1:{ apply value_eqb_eq in E_k0v0; subst.
              lazymatch goal with
                H: context[?x = _] |- context[?x] => rewrite H end.
              2: constructor; auto.
              unfold record_proj. rewrite_l_to_r. rewrite value_eqb_refl; simpl.
              rewrite not_In__dict_delete; auto.
              rewrite Forall_false__filter; auto. rewrite Forall_forall; intros. apply_Forall_In.
              destruct_match_hyp; intuition auto. rewrite_l_to_r. rewrite value_eqb_refl; auto. }
          1:{ simpl. lazymatch goal with
              H: context[?x = _] |- context[?x] => rewrite H end.
              2: constructor; auto.
              unfold record_proj; rewrite value_eqb_sym; repeat rewrite_l_to_r.
              simpl. f_equal.
              f_equal. apply forallb_filter_id. rewrite forallb_forall; intros; apply_Forall_In.
              destruct_match_hyp; intuition. rewrite_l_to_r. rewrite value_eqb_sym. rewrite_l_to_r; auto. }
        Qed.

        Lemma dict_delete_preserve_index_wf : forall idx,
            idx_wf (VDict idx) ->
            forall k, idx_wf (VDict (dict_delete k idx)).
        Proof.
          intros * H_wf *.
          induction idx; simpl; auto.
          destruct a. destruct (value_eqb k0 v0).
          all: apply index_wf_step_inv in H_wf as H_wf'; auto.
          specialize (IHidx H_wf').
          unfold idx_wf, index_wf in H_wf; invert_Forall.
          unfold idx_wf, index_wf; simpl; intuition auto.
        Qed.

        Lemma neq_filter_to_delete_head_preserve_sem : forall tbl (Gstore : tenv) (store : locals) t,
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (idx_ty t) ->
            holds_for_all_entries (index_wf_with_globals [tbl]) store ->
            preserve_sem Gstore store (neq_filter_to_delete_head tbl).
        Proof.
          unfold preserve_sem, is_tbl_ty; intros.
          repeat destruct_match_hyp; try congruence.
          unfold holds_for_all_entries, index_wf_with_globals in *.
          repeat destruct_subexpr. unfold neq_filter_to_delete_head in *.
          repeat (case_match; auto).
          simpl in * |-. repeat rewrite Bool.andb_true_r in * |-.
          repeat rewrite Bool.andb_true_iff in * |-; intuition idtac.
          rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
          assert (type_of Gstore Genv (efilter_neq x0 x0 attr e1_2_2 (eidx_to_list k0 v1 v1 v1 acc0 acc0 (ELoc tbl))) (TList (TRecord l))).
          { do 3 invert_type_of.
            assert(t1 = TRecord l).
            { repeat invert_type_of_clear; repeat invert_type_of_op_clear.
              repeat rewrite_map_get_put_hyp.
              repeat rewrite_l_to_r.
              lazymatch goal with
                H1: map.get _ _ = _, H2: map.get _ _ = _ |- _ =>
                  rewrite H1 in H2 end.
              unfold index_type in *; do_injection2.
              simpl in *. congruence. }
            subst; auto. }
          symmetry. erewrite sem_eq_eq with (t:=idx_ty (TList (TRecord l))).
          3,4: eauto.
          2: apply fold_to_idx; eauto; simpl; intuition auto.
          erewrite fiat2_gallina_to_idx_sem.
          3-7: eauto.
          all: auto.
          erewrite fiat2_gallina_filter_access_neq; auto.
          2:{ erewrite sem_eq_eq; eauto.
              2: apply fold_from_idx; simpl; intuition eauto.
              2: constructor; auto.
              1: eapply fiat2_gallina_from_idx_sem.
              2-7: eauto.
              2: constructor.
              all: auto. }
          cbn [interp_expr]. unfold get_local.
          lazymatch goal with
            H1: locals_wf Gstore store, H2: map.get Gstore _ = _ |- _ => apply H1 in H2 end.
          destruct_match_hyp; intuition idtac.
          invert_type_of_value.
          apply H2 in E; unfold value_wf_with_globals in *.
          invert_Forall; destruct_or; intuition auto.
          erewrite gallina_filter_access_neq_from_idx; eauto.
          apply consistent_LikeList_eq.
          rewrite <- gallina_from_to_LikeList with (t:=TList (TRecord l)); auto.
          1:{ apply dict_delete_sound; eauto.
              repeat invert_type_of_clear. repeat invert_type_of_op_clear.
              unfold get_attr_type.
              repeat rewrite_map_get_put_hyp. repeat do_injection2.
              eapply type_sound.
              1:{ rewrite_l_to_r_goal. eapply not_free_immut_put_ty; eauto. }
              all: auto. }
          1: apply dict_delete_preserve_index_wf; auto.
        Qed.

        Lemma neq_filter_to_delete_head_sound : expr_aug_transf_sound (idx_wf:=idx_wf) neq_filter_to_delete_head.
        Proof.
          unfold expr_aug_transf_sound; intros.
          invert_tenv_wf_with_globals; split; intros.
          1: eapply neq_filter_to_delete_head_preserve_ty; eauto.
          1: eapply neq_filter_to_delete_head_preserve_sem; eauto.
        Qed.
      End neq_filter_to_delete.
    End WithMap.
  End WithVars.
End WithHole.

#[export] Hint Resolve eq_filter_to_lookup_head_sound : transf_hints.
#[export] Hint Resolve neq_filter_to_delete_head_sound : transf_hints.


   Prove:
    EBagOf (ELoc tbl) == EBagOf (from_idx (to_idx (ELoc tbl))).
    EFilter LikeBag (EBagOf (from_idx d)) x (x["attr"] = e) == EBinop OLookup d e.
    (given that x is not free immut in e)

   Pattern matching
   EFilter LikeBag (EBagOf (ELoc tbl))) x (x["attr"] = e)
    => EBinop OLookup (to_idx (ELoc tbl)) e.

    letmut tbl := init_e in c0.

    letmut tbl := init_e in c1 (using to_idx1, to_idx2, ...).

    letmut tbl := (init_e, to_idx1 init_e) , to_idx2 init_e, ...) in
             c2 (using tbl[0], tbl[1], tbl[2], ...).

    In particular, tbl := hd :: tbl
    becomes tbl := (hd :: tbl[0], to_idx1 (hd :: tbl[0]), to_idx2 (hd :: tbl[0]))

    to_idx1 (hd :: tbl[0]) == insert hd (to_idx1 tbl[0]) == insert hd tbl[1]
