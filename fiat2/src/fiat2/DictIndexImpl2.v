Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface2 fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.

Section WithHole.
  Context (hole : string).
  Context (attr : string).

  Section WithVars.
    Context (tup acc x k v : string).
    Context (H_NoDup : is_NoDup_opaque [tup; acc; x; k; v]).

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

      Lemma to_idx_wf : forall (v : value) (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          idx_wf v (interp_expr map.empty (map.put map.empty hole v) to_idx).
      Proof.
        intros; erewrite fiat2_gallina_to_idx; eauto.
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

      Notation eto_idx tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1 d :=
        (EFold d (EAtom (AEmptyDict None)) tup0 acc0
           (ETernop OInsert (EVar acc1) (EAccess (EVar tup1) attr0)
              (EBinop OBagInsert
                 (EOptMatch (EBinop OLookup (EVar acc2) (EAccess (EVar tup2) attr1))
                    (EAtom (AEmptyBag None)) x0 (EVar x1))
                 (EVar tup3)))).

      Section WithTags.
        Context (tbl id_tag aux_tag idx_tag: string).

        Section eq_filter_to_lookup.
          Context (b : string).

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

          Lemma eq_filter_to_lookup_head_preserve_ty : forall tbl t (Gstore : tenv),
              type_wf t -> is_tbl_ty t ->
              map.get Gstore tbl = Some (idx_ty t) ->
              preserve_ty Gstore (eq_filter_to_lookup_head tbl).
          Proof.


        End eq_filter_to_lookup.

        Section cons_to_insert.
          Context (d : string).

          Definition cons_to_insert_head (e : expr) :=
            match e with
            | eto_idx tup tup1 tup2 tup3 acc acc1 acc2 x x1 attr0 attr1 (EBinop OCons e1 e2) =>
                ELet (eto_idx tup tup tup tup acc acc acc x x attr attr e2) d
                  (ELet (EAccess e1 attr) k
                     (ETernop OInsert (EVar d)
                        (EVar k)
                        (EBinop OBagInsert
                           (EOptMatch
                              (EBinop OLookup (EVar d) (EVar k))
                              (EAtom (AEmptyBag None)) x (EVar x))
                           (EVar k))))
            | _ => e
            end.
        End cons_to_insert.

        Section use_idx.
          Definition use_idx_head (e : expr) :=
            match e with
            | eto_idx tup0 tup1 tup2 tup3 acc0 acc1 acc2 x0 x1 attr0 attr1 (EAccess (ELoc tbl0) id_tag0) =>
                EAccess (EAccess (ELoc tbl) aux_tag) idx_tag
            | _ => e
            end.
        End use_idx.
      End WithTags.
    End WithMap.
  End WithVars.
End WithHole.


(* ??? An example *)
  Require Import fiat2.Notations coqutil.Map.SortedListString.
  Open Scope fiat2_scope.
Section ConcreteExample.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Instance caenv : map.map string collection_tag := SortedListString.map _.
  Instance caenv_ok : map.ok caenv := SortedListString.ok _.

  Instance cRenv : map.map string (value -> value -> Prop) := SortedListString.map _.
  Instance cRenv_ok : map.ok cRenv := SortedListString.ok _.


  Definition row_ty := TRecord (record_sort [("name", TString); ("department", TString); ("feedback", TString)]).
  (* two arbitrary well_typed rows *)
  Definition row1 := EVar "row1".
  Definition row2 := EVar "row2".

  Definition build_responses1 := <{ set "responses" := row1 :: row2 :: mut "responses" }>.
  Definition filter_responses dpt : expr := ESort LikeList <[ "row" <- mut "responses" ;
                                                       check("row"["department"] == << EAtom (AString dpt) >>);
                                                       ret "row" ]>.
  Definition query := CForeach (filter_responses "EECS") "r"
                         <{ let "name" = "r"["name"] +++ << EAtom (AString ": ") >> in
                            let "feedback" = "r"["feedback"] +++ << EAtom (AString "\n") >> in
                            let "line" = "name" +++ "feedback" in
                            set "all_feedback" := mut "all_feedback" +++ "line" }>.
  Definition ex1' := CSeq build_responses1 query.
  Definition ex1 := CLetMut (EAtom (ANil (Some (row_ty)))) "responses" ex1'.
  Compute ex1.

  Require Import fiat2.RelTransf.
  Definition init_Gstore : ctenv := map.put map.empty "all_feedback" TString.
  Definition init_Genv : ctenv := map.put (map.put map.empty "row1" row_ty) "row2" row_ty.
  Definition ex1_to_filter := fold_command id to_filter_head ex1.
  Compute ex1_to_filter.
  Definition ex1_to_bag := fold_command id push_down_collection (fold_command id annotate_collection ex1_to_filter).
  Compute ex1_to_bag.
  Definition ex1_create_aux := fold_command (create_aux_write_head "hole" "department" "tup" "acc" "x" "id_tag" "aux_tag" "idx_tag" "responses" nil) (create_aux_read_head "id_tag" "responses") ex1_to_bag.
  Compute ex1_create_aux.
  Definition ex1_idx_write := fold_command id (cons_to_insert_head "department" "k" "d") ex1_create_aux.
  Compute ex1_idx_write.
  Definition ex1_idx_write2 := fold_command id (cons_to_insert_head "department" "k" "d") ex1_idx_write.
  Compute ex1_idx_write2.
  Definition ex1_use_idx := fold_command id (use_idx_head "responses" "aux_tag" "idx_tag") ex1_idx_write2.
  Compute ex1_use_idx.
  Definition ex1_idx_lookup := fold_command id (eq_filter_to_lookup_head "department" "responses" "id_tag" "aux_tag" "idx_tag" "b") ex1_use_idx.
  Compute ex1_idx_lookup.

        Lemma eq_filter_to_lookup_head_preserve_ty : forall t tl aux_tl (Gstore : tenv),
            type_wf t -> is_tbl_ty t = true ->
            map.get Gstore tbl = Some (TRecord tl) ->
            access_record tl id_tag = Success t ->
            access_record tl aux_tag = Success (TRecord aux_tl) ->
            access_record aux_tl idx_tag = Success (idx_ty t) ->
            preserve_ty Gstore eq_filter_to_lookup_head.
        Proof.
          clear H_NoDup.
          unfold preserve_ty, is_tbl_ty. intros.
          repeat destruct_match_hyp; try congruence.
          repeat destruct_subexpr. simpl.
          case_match; auto. repeat rewrite Bool.andb_true_r in *.
          repeat rewrite Bool.andb_true_iff in *; intuition idtac.
          rewrite eqb_eq in *; subst.
          repeat invert_type_of_clear. repeat invert_type_of_op_clear. repeat rewrite_map_get_put_hyp.
          repeat (clear_refl; repeat do_injection2).
          repeat (econstructor; eauto).
          1:{ lazymatch goal with H: ?x = _, H': ?x = _ |- _ => rewrite H in H' end.
              do_injection2. simpl in *; do_injection2.
              unfold get_attr_type. lazymatch goal with H: ?x = _ |- context[?x] => rewrite H end.
              eapply not_free_immut_put_ty; eauto. }
          all: rewrite map.get_put_same; trivial.
        Qed.

        Theorem eq_filter_to_lookup_head_preserve_sem :
idx_wf
  (interp_expr store env (EAccess (ELoc tbl) id_tag))
    (interp_expr store env idx_e) ->
End WithMap.
