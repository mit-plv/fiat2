Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface
  fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute fiat2.IndexTransf fiat2.CollectionTag.
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

    (* Materialize tbl (expected to be a list of records) into an index over attr *)
    Definition to_idx : expr :=
      let k := EAccess (EVar tup) attr in
      EFold (EVar hole) (EDict nil) tup acc
        (EInsert (EVar acc) k
           (EOptMatch (ELookup (EVar acc) k)
              (epair enil (EVar tup))
              x (cons_to_fst (EVar tup) (EVar x)))).

    (* Inverse of to_idx, expecting idx to be a dict
   Require the index keys in idx to match the attr values in the records *)
    Definition from_idx : expr :=
      EDictFold (EVar hole) enil k v acc
        (EBinop OConcat (ofst (EVar v))
           (econs (osnd (EVar v)) (EVar acc))).

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

      (* ??? experiment with uniqueness of (substitute ... to_idx)'s type *)
      Lemma to_idx_ty_unique :  forall Gstore Genv e t,
          type_wf t -> is_tbl_ty t = true ->
          (forall t', type_of Gstore Genv e t' -> t = t') ->
          forall t', type_of Gstore Genv (substitute [(hole, e)] (get_free_vars Genv) to_idx) t' ->
                     t' = (idx_ty t).
      Proof.
        unfold to_idx; cbn [substitute sub_lookup]; intros.
        repeat (try rewrite eqb_refl in *; invert_type_of_clear).
        assert(tup =? x = false). { apply eqb_neq; use_is_NoDup. }
        assert(tup =? acc = false). { apply eqb_neq; use_is_NoDup. }
        rewrite H2 in *. rewrite H5 in *. cbn in *.
        apply H1 in H9; subst. simpl.
        unfold is_tbl_ty in *. destruct_match_hyp; try discriminate.
        remember (fresh_var tup (get_free_vars Genv)) as tup'.
        remember (fresh_var acc (tup' :: get_free_vars Genv)) as acc'.
        remember (fresh_var x (acc' :: tup' :: get_free_vars Genv)) as x'.
        assert(tup' <> acc' /\ tup' <> x').
        { rewrite Heqacc', Heqx'. auto using fresh_var_neq, fresh_var_neq2. }
        clear Heqtup' Heqacc' Heqx'.
        repeat invert_Forall2.
        repeat invert_type_of_clear.
        repeat rewrite_map_get_put_hyp; repeat (try clear_refl; do_injection).
        invert_type_of_op_clear.
        do 3 (destruct tl1; try discriminate). destruct p, p0; cbn in *.
        inversion H16; inversion H26; subst.
        apply Permutation_length_2_inv in H19; intuition idtac; subst.
        2:{ invert_SSorted. invert_Forall. inversion H19. }
        unfold index_type, get_attr_type. rewrite H18. cbn in *. congruence.
      Qed.

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

      Lemma from_idx_ty : forall (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of map.empty (map.put map.empty hole (idx_ty t)) from_idx t.
      Proof.
        intros. unfold from_idx.
        unfold is_tbl_ty in *. repeat destruct_match_hyp; try discriminate; subst.
        invert_type_wf. repeat econstructor; simpl; auto.
        all: repeat rewrite_map_get_put_goal;
          invert_type_wf; use_is_NoDup.
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

      Notation index_wf_with_globals := (index_wf_with_globals (idx_wf:=idx_wf)).

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

      Definition gallina_from_idx (v : value) : list value :=
        match v with
        | VDict d =>
            fold_right
              (fun v acc => match snd v with
                            | VRecord p => match record_proj "0" p with
                                           | VList l => (l ++ (record_proj "1" p :: acc))%list
                                           | _ => nil
                                           end
                            | _ => nil
                            end)
              nil d
        | _ => nil
        end.

      Lemma fiat2_gallina_from_idx : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v (idx_ty t) ->
          interp_expr map.empty (map.put map.empty hole v) from_idx = VList (gallina_from_idx v).
      Proof.
        unfold is_tbl_ty, idx_ty, index_type; intros. repeat destruct_match_hyp; try discriminate.
        invert_type_of_value_clear; simpl.
        unfold get_local; rewrite_map_get_put_goal.
        erewrite In_fold_right_ext with
          (P := fun v => match v with VList _ => True | _ => False end)
          (g := fun v1 v2 =>
                  match v1, v2 with
                  | (v0, v1), (VList l) => match v1 with
                                           | VRecord l1 => match record_proj "0" l1 with
                                                           | VList l1_0 => VList (l1_0 ++ record_proj "1" l1 :: l)
                                                           | _ => VUnit
                                                           end
                                           | _ => VUnit
                                           end
                  | _, _ => VUnit
                  end); auto.
        1:{ induction l0; simpl in *; auto. invert_Forall; invert_NoDup; invert_SSorted.
            rewrite IHl0; auto. destruct a; simpl in *.
            destruct_and. invert_type_of_value_clear. repeat invert_Forall2.
            destruct x0, x1; simpl in *. do 2 destruct_and; subst.
            unfold record_proj; simpl. do 2 invert_type_of_value_clear; auto. }
        1:{ intros. destruct_match_hyp; try now (intuition auto).
            repeat rewrite_map_get_put_goal; try now use_is_NoDup.
            apply_Forall_In. destruct_and.
            destruct b; simpl in *. invert_type_of_value_clear; split; auto.
            repeat invert_Forall2. do 2 destruct_and; destruct x0, x1.
            simpl in *; subst. unfold record_proj; simpl.
            do 2 invert_type_of_value_clear; auto. }
      Qed.
(* ??? remove
      Lemma map_incl_step_l : forall {kt vt} {key_eqb : kt -> kt -> bool}
                                     {mt : map.map kt vt} {mt_ok : map.ok mt} (m m' : mt)
                                     x v,
          (forall x y : kt, BoolSpec (x = y) (x <> y) (key_eqb x y)) ->
          map_incl m m' -> map.get m' x = Some v ->
          map_incl (map.put m x v) m'.
      Proof.
        intros.
        erewrite <- Properties.map.put_noop; eauto.
        apply map_incl_step; auto.
        intros. specialize (H k1 k2).
        destruct (key_eqb k1 k2) eqn:E;
          [ left; eapply autoforward.BoolSpec_true
          | right; eapply autoforward.BoolSpec_false ]; eauto.
      Qed.
*)
      Lemma fiat2_gallina_from_idx2 : forall (store env : locals) (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v (idx_ty t) ->
          map.get env hole = Some v ->
          interp_expr store env from_idx = VList (gallina_from_idx v).
      Proof.
        intros. erewrite interp_expr_strengthen.
        1: eapply fiat2_gallina_from_idx.
        6: apply from_idx_ty.
        all: resolve_locals_wf; eauto using idx_ty_wf, map_incl_empty with fiat2_hints.
        eapply map_incl_step_l; auto using map_incl_empty.
        apply Decidable.String.eqb_spec.
      Qed.

      Ltac use_from_idx_ty :=
        eapply type_of_strengthen;
        [ apply from_idx_ty; auto
        | apply map_incl_empty
        | apply map_incl_refl ].

      Ltac prove_sub_wf :=
        unfold sub_wf; simpl; intros;
        case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
        [ rewrite_map_get_put_hyp
        | rewrite map.get_put_diff, map.get_empty in *; auto ];
        congruence.

      Hint Resolve incl_refl : core.

      Lemma fiat2_gallina_from_idx_sem : forall Gstore Genv store env e t free_vars,
          tenv_wf Gstore -> tenv_wf Genv ->
          type_wf t -> is_tbl_ty t = true ->
          type_of Gstore Genv e (idx_ty t) ->
          locals_wf Gstore store -> locals_wf Genv env ->
          incl (get_free_vars Genv) free_vars ->
          interp_expr store env (substitute [(hole, e)] free_vars from_idx) = VList (gallina_from_idx (interp_expr store env e)).
      Proof.
        intros. erewrite substitute_preserve_sem.
        1:{ erewrite fiat2_gallina_from_idx2; eauto with fiat2_hints.
            simpl. rewrite_map_get_put_goal. auto. }
        6-8: eauto.
        all: auto.
        2: use_from_idx_ty.
        all: eauto using idx_ty_wf with fiat2_hints.
        prove_sub_wf.
      Qed.

      Lemma fold_from_idx : forall Gstore Genv t e k0 v0 acc0 free_vars,
          is_NoDup [k0; v0; acc0] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          type_wf t -> is_tbl_ty t = true ->
          type_of Gstore Genv e (idx_ty t) ->
          incl (get_free_vars Genv) free_vars ->
          sem_eq Gstore Genv t
            (EDictFold e (EAtom (ANil None)) k0 v0 acc0
               (EBinop OConcat (EAccess (EVar v0) "0") (EBinop OCons (EAccess (EVar v0) "1") (EVar acc0))))
            (substitute [(hole, e)] free_vars from_idx).
      Proof.
        unfold sem_eq; intros. intuition idtac.
        1:{ unfold idx_ty in *. unfold is_tbl_ty in *.
            do 2 (destruct_match_hyp; try discriminate).
            invert_type_wf.
            repeat (econstructor; eauto); repeat rewrite_map_get_put_goal; eauto. }
        1:{ eapply substitute_preserve_ty; auto.
            2: use_from_idx_ty.
            1: eauto using idx_ty_wf with fiat2_hints.
            1: prove_sub_wf. }
        erewrite substitute_preserve_sem.
        1:{ unfold from_idx. simpl.
            unfold get_local; rewrite_map_get_put_goal.
            case_match; auto.
            eapply In_fold_right_ext with (P:=fun _ => True); intuition auto.
            repeat rewrite_map_get_put_goal; use_is_NoDup. }
        6-8: eauto.
        all: auto.
        2: use_from_idx_ty.
        all: eauto using idx_ty_wf with fiat2_hints.
        prove_sub_wf.
      Qed.

      Ltac use_to_idx_ty :=
        eapply type_of_strengthen;
        [ apply to_idx_ty; auto
        | apply map_incl_empty
        | apply map_incl_refl ].

      Lemma fold_to_idx : forall Gstore Genv t e x0 tup0 acc0 free_vars,
          is_NoDup [x0; tup0; acc0] ->
          tenv_wf Gstore -> tenv_wf Genv ->
          is_tbl_ty t = true ->
          type_of Gstore Genv e t ->
          incl (get_free_vars Genv) free_vars ->
          sem_eq Gstore Genv (idx_ty t)
            (EFold e (EDict []) tup0 acc0
               (EInsert (EVar acc0) (EAccess (EVar tup0) attr) (EOptMatch (ELookup (EVar acc0) (EAccess (EVar tup0) attr)) (epair enil (EVar tup0)) x0 (cons_to_fst (EVar tup0) (EVar x0)))))
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

      Lemma fiat2_gallina_to_from_idx : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          interp_expr map.empty (map.put map.empty hole (interp_expr map.empty (map.put map.empty hole v) to_idx)) from_idx =
            VList (gallina_from_idx (VDict (gallina_to_idx v))).
      Proof.
        intros.
        erewrite fiat2_gallina_to_idx, fiat2_gallina_from_idx;
          eauto using gallina_to_idx_ty.
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

      Lemma gallina_to_idx_LikeBag : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          consistent LikeBag v (VList (concat_VList_V (List.map snd (gallina_to_idx v)))).
      Proof.
        unfold is_tbl_ty; intros. repeat destruct_match_hyp; try discriminate.
        rewrite inb_true_iff in *; invert_type_of_value_clear. simpl.
        apply Permutation_sym.
        induction H4; simpl in *; auto. invert_type_of_value_clear.
        eapply perm_trans.
        1:{ eapply dict_insert_lookup_Permutation.
            - eapply gallina_list_to_idx_shape; eauto.
            - eapply gallina_list_to_idx_SSorted; eauto. }
        1: constructor; auto.
      Qed.

      Lemma gallina_from_idx__concat_VList_V : forall l,
          Forall has_index_entry_shape l ->
          gallina_from_idx (VDict l) = concat_VList_V (List.map snd l).
      Proof.
        intros * H.
        induction l; simpl; auto. invert_Forall.
        case_match; auto. simpl in *. rewrite IHl; auto.
      Qed.

      Lemma gallina_to_from_LikeBag : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          consistent LikeBag
            v
            (VList (gallina_from_idx (VDict (gallina_to_idx v)))).
      Proof.
        intros. eapply consistent_tran'.
        1: eapply gallina_to_idx_LikeBag; eauto.
        rewrite gallina_from_idx__concat_VList_V; auto using consistent_refl.
        unfold is_tbl_ty in *.
        repeat destruct_match_hyp; try discriminate.
        rewrite inb_true_iff in *. invert_type_of_value_clear.
        eapply gallina_list_to_idx_shape; eauto.
      Qed.

      Lemma to_from_LikeBag : forall (v : value) t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          consistent LikeBag
            v
            (interp_expr map.empty (map.put map.empty hole (interp_expr map.empty (map.put map.empty hole v) to_idx)) from_idx).
      Proof.
        intros.
        erewrite fiat2_gallina_to_idx, fiat2_gallina_from_idx;
          eauto using gallina_to_from_LikeBag, gallina_to_idx_ty.
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

      Lemma gallina_from_idx_ty : forall v t,
          type_wf t ->
          is_tbl_ty t = true ->
          type_of_value v (idx_ty t) ->
          type_of_value (VList (gallina_from_idx v)) t.
      Proof.
        intros. erewrite <- fiat2_gallina_from_idx; eauto.
        eapply type_sound;
          eauto using from_idx_ty, idx_ty_wf with fiat2_hints.
      Qed.

      Lemma gallina_from_to_LikeList : forall v t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v (idx_ty t) ->
          idx_wf v ->
          consistent LikeList v
            (VDict (gallina_to_idx (VList (gallina_from_idx v)))).
      Proof.
        unfold is_tbl_ty, idx_ty, index_type; intros.
        repeat destruct_match_hyp; try discriminate.
        invert_type_of_value_clear.
        rewrite consistent_LikeList_eq. f_equal.
        rewrite gallina_from_idx__concat_VList_V;
          auto using idx_wf__has_index_entry_shape.
        simpl. unfold record_proj.
        induction l0; simpl in *; auto. unfold record_proj.
        invert_Forall; invert_NoDup; invert_SSorted.
        destruct a; simpl in *.
        destruct_and. invert_type_of_value_clear.
        do 2 (invert_Forall2; destruct_and). invert_Forall2.
        destruct x0, x1; simpl in *; subst.
        do 2 invert_type_of_value_clear.
        rewrite List.assoc_app_cons, fold_right_app.
        rewrite <- IHl0; auto.
        2: lazymatch goal with
             H: index_wf (_ :: _) |- _ =>
               apply index_wf_step_inv in H
           end; auto.
        unfold idx_wf, index_wf in H2; invert_Forall; simpl in *.
        destruct_and.
        induction l2; simpl; repeat rewrite_l_to_r.
        1:{ rewrite dict_lookup_Lt, dict_insert_Lt;
            eauto using NoDup_SSorted__Lt. }
        1:{ rewrite <- IHl2; auto.
            all: repeat invert_Forall; try now (intuition auto).
            2: repeat (constructor; simpl in *; auto).
            invert_type_of_value_clear. rewrite_l_to_r.
            simpl. rewrite value_eqb_refl.
            unfold value_ltb. rewrite value_compare_refl. auto. }
      Qed.

      Lemma from_to_LikeList : forall v t,
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v (idx_ty t) ->
          idx_wf v ->
          consistent LikeList v
            (interp_expr map.empty (map.put map.empty hole (interp_expr map.empty (map.put map.empty hole v) from_idx)) to_idx).
      Proof.
        intros. erewrite fiat2_gallina_from_idx, fiat2_gallina_to_idx;
          eauto using gallina_from_to_LikeList, gallina_from_idx_ty.
      Qed.

      Instance dict_idx : IndexInterface.index := IndexInterface.mk hole to_idx from_idx idx_ty is_tbl_ty.

      Instance dict_idx_ok : IndexInterface.ok LikeBag LikeList dict_idx idx_wf consistent := IndexInterface.Build_ok dict_idx idx_wf idx_ty_wf to_idx_ty from_idx_ty to_idx_wf to_from_LikeBag from_to_LikeList.

      Notation elist_to_idx tup0 tup1 tup2 tup3 tup4 acc0 acc1 acc2 x0 x1 x2 attr0 attr1 d :=
        (EFold d (EDict []) tup0 acc0
           (EInsert (EVar acc1) (EAccess (EVar tup1) attr0) (EOptMatch (ELookup (EVar acc2) (EAccess (EVar tup2) attr1)) (ERecord [("0", EAtom (ANil None)); ("1", EVar tup3)]) x0 (ERecord [("0", EBinop OCons (EVar tup4) (EAccess (EVar x1) "0")); ("1", EAccess (EVar x2) "1")] )))).

      Notation eidx_to_list k v0 v1 v2 acc0 acc1 d :=
        (EDictFold d (EAtom (ANil None)) k v0 acc0 (EBinop OConcat (EAccess (EVar v1) "0") (EBinop OCons (EAccess (EVar v2) "1") (EVar acc1)))).

      Notation efilter_neq x0 x1 attr0 k l :=
        (EFilter l x0 (EUnop ONot (EBinop OEq (EAccess (EVar x1) attr0) k))).

      Ltac invert_tenv_wf_with_globals :=
        lazymatch goal with H: tenv_wf_with_globals _ _ _ |- _ => inversion H; subst end.

      Ltac rewrite_l_to_r_goal :=
        multimatch goal with H: ?x = _ |- context[?x] => rewrite H end.

      Section eq_filter_to_lookup.
        Context (p : string).

        Definition eq_filter_to_lookup_head (tbl : string) (e : expr) :=
          (* filter (idx_to_list idx) (fun row => row.attr == e') -->
           match (lookup idx e') with none => nil | some p => fst p ++ [snd p] *)
          match e with
          | EFilter
              (eidx_to_list k0 v0 v1 v2 acc0 acc1 (ELoc tbl0))
              x
              (EBinop OEq (EAccess (EVar x0) attr0) e') =>
              if (all_eqb [(v0, [v1; v2]); (acc0, [acc1]); (tbl, [tbl0]); (attr, [attr0]); (x, [x0])] &&
                    all_neqb [k0; v0; acc0] &&
                    negb (free_immut_in x e'))%bool
              then EOptMatch (ELookup (ELoc tbl) e')
                     enil
                     p (EBinop OConcat (ofst (EVar p)) (econs (osnd (EVar p)) enil))
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
               then EDelete (ELoc tbl) k'
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
          repeat destruct_subexpr. simpl. case_match; auto.
          repeat rewrite Bool.andb_true_r in E1. repeat rewrite Bool.andb_true_iff in E1; intuition idtac.
          rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
          repeat invert_type_of_clear. repeat invert_type_of_op_clear.
          repeat rewrite_map_get_put_hyp. repeat (clear_refl; repeat do_injection2).
          repeat constructor; auto.
          1:{ lazymatch goal with
              H: map.get Gstore tbl = _, H': map.get Gstore tbl = _ |- _ =>
                rewrite H in *; do_injection2; simpl in *; do_injection2
            end.
              unfold get_attr_type.
              lazymatch goal with
              | H1: ?x = _, H2: ?x = _ |- _ => rewrite H1 in H2 end.
              do_injection2; rewrite_l_to_r_goal.
              repeat clear_refl. unfold index_type. do 3 f_equal.
              repeat invert_Forall2. repeat invert_type_of_clear.
              repeat invert_type_of_op_clear; repeat rewrite_map_get_put_hyp.
              repeat rewrite_l_to_r; repeat (try clear_refl; do_injection).
              do 3 (destruct tl1; simpl in *; try congruence). destruct p, p0; simpl in *.
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
          repeat destruct_subexpr. unfold neq_filter_to_delete_head in *. case_match; auto.
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
