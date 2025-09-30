Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface2
  fiat2.Utils fiat2.TransfSound fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Require Import List String ZArith Sorted Permutation.
Import ListNotations.

Fixpoint mk_compo_idx' (e : expr) (free_vars : list string) (idxs : list (string * IndexInterface2.index)) :=
  match idxs with
  | nil => nil
  | (tag, idx) :: idxs => (tag, substitute [(@hole idx, e)] free_vars (@to_idx idx)) :: mk_compo_idx' e free_vars idxs
  end.

Definition mk_compo_idx (e : expr) (free_vars : list string) (idxs : list (string * IndexInterface2.index)) :=
  ERecord (mk_compo_idx' e free_vars idxs).

Lemma map_fst_map_triple : forall A B C D (l : list (A * B * C)) (f : B -> D),
    List.map fst (List.map (fun '(a, b, _) => (a, f b)) l) = List.map fst (List.map fst l).
Proof.
  intros; induction l; cbn; auto.
  repeat case_match; cbn; congruence.
Qed.

Section compo_idx.
  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (width:=width)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Context (idxs : list (string * IndexInterface2.index * (value -> value -> Prop))).
    Context (idxs_ok : Forall (fun '(_, idx, idx_wf) => ok idx idx_wf) idxs).
    Context (H_tag_NoDup : NoDup (List.map fst (List.map fst idxs))).
    Context (hole0 : string).
    Context (H_holes_eq : Forall (fun '(_, idx, _) => @hole idx = hole0) idxs).

    Definition compo_idx_ty (t : type) : type :=
      TRecord (record_sort (List.map (fun '(tag, idx, _) => (tag, @idx_ty idx t)) idxs)).

    Definition to_compo_idx : expr :=
      ERecord (List.map (fun '(tag, idx, _) => (tag, @to_idx idx)) idxs).

    Definition compo_idx_wf (v v' : value) : Prop :=
      match v' with
      | VRecord v' =>
          Forall (fun '(tag, _, idx_wf) => idx_wf v (record_proj tag v')) idxs
      | _ => False
      end.

    Definition compo_is_tbl_ty (t : type) : bool :=
      forallb (fun '(tag, idx, _) => @is_tbl_ty idx t) idxs.

    Lemma to_compo_idx_ty : forall (t : type),
        type_wf t -> compo_is_tbl_ty t = true ->
        type_of map.empty (map.put map.empty hole0 t) to_compo_idx (compo_idx_ty t).
    Proof.
      unfold compo_is_tbl_ty, to_compo_idx, compo_idx_ty.
      intros. econstructor; eauto using Permuted_record_sort, StronglySorted_record_sort.
      1:{ clear. induction idxs; cbn; auto.
          do 2 case_match; cbn; congruence. }
      1:{ induction idxs; auto. cbn in *.
          repeat invert_Forall; invert_NoDup; rewrite Bool.andb_true_iff in *; intuition idtac.
          constructor; auto.
          do 2 case_match; cbn; subst. eapply (to_idx_ty (idx:=i)); eauto. }
      1:{ revert H_tag_NoDup; clear; intros.
          induction idxs; intros; cbn; auto using NoDup_nil.
          cbn in *; invert_NoDup.
          constructor; auto. do 2 case_match; cbn in *.
          rewrite map_fst_map_triple; auto. }
    Qed.

    Lemma compo_idx_ty_wf : forall t : type,
        type_wf t -> compo_is_tbl_ty t = true ->
        type_wf (compo_idx_ty t).
    Proof.
      unfold compo_is_tbl_ty, compo_idx_ty; intros ? ? H.
      eapply List.forallb_to_Forall with (P:=fun '(_, idx, _) => @is_tbl_ty idx t = true) in H.
      2: intros; repeat case_match; auto.
      constructor; auto using StronglySorted_record_sort.
      1:{ eapply Permutation_NoDup.
          1: apply Permutation_map, Permuted_record_sort.
          induction idxs; cbn in *; auto.
          repeat invert_Forall; invert_NoDup.
          constructor; auto.
          repeat case_match; cbn in *.
          rewrite map_fst_map_triple; auto. }
      1:{ rewrite Forall_map.
          eapply Permutation_Forall.
          1: apply Permuted_record_sort.
          induction H; cbn in *; auto.
          repeat invert_Forall; invert_NoDup.
          constructor; repeat case_match; auto.
          cbn; auto using idx_ty_wf. }
    Qed.

    Lemma NoDup_In_access_record : forall A (l : list (string * A)),
        NoDup (List.map fst l) ->
        forall s v, In (s, v) l ->
        access_record l s = Success v.
    Proof.
      intros * ? ? ? H_in; induction l; cbn in *.
      1: intuition fail.
      do 2 case_match; rewrite ?eqb_eq, ?eqb_neq in *; invert_NoDup.
      1:{ subst. intuition idtac; try congruence.
          apply in_map with (f:=fst) in H0;
            cbn in *; intuition idtac. }
      1:{ intuition idtac. congruence. }
    Qed.

    Lemma NoDup_Permutation_access_record : forall s A (l l' : list (string * A)),
        NoDup (List.map fst l) ->
        In s (List.map fst l) ->
        Permutation l l' ->
        access_record l s = access_record l' s.
    Proof.
      intros * H_NoDup H_in H_permu.
      apply In_access_record in H_in. destruct_exists.
      rewrite_l_to_r.
      apply access_record_sound in H.
      symmetry. apply NoDup_In_access_record.
      1:{ eapply Permutation_NoDup.
          1: apply Permutation_map; eauto.
          assumption. }
      1:{ eapply Permutation_in; eauto. }
    Qed.

    Lemma to_compo_idx_wf : forall (v : value) (t : type),
      type_wf t -> compo_is_tbl_ty t = true ->
      type_of_value v t ->
      compo_idx_wf v (interp_expr map.empty (map.put map.empty hole0 v) to_compo_idx).
    Proof.
      intros.
      unfold compo_idx_wf, compo_idx_ty, to_compo_idx, compo_is_tbl_ty, record_proj in *.
      cbn [interp_expr].
      rewrite Forall_forall; intros. do 2 case_match.
      erewrite NoDup_Permutation_access_record.
      4: apply Permutation_sym, Permuted_record_sort.
      2:{ eapply Permutation_NoDup.
          1: eapply Permutation_map, Permuted_record_sort.
          rewrite fst_map_fst, map_fst_map_triple; auto. }
      2:{ rewrite in_map_iff. eexists; intuition idtac.
          2:{ eapply Permutation_in.
              1: apply Permuted_record_sort.
              rewrite in_map_iff. exists (s, to_idx).
              intuition idtac.
              rewrite in_map_iff; exists x.
              subst; auto. }
          reflexivity. }
      eapply List.forallb_to_Forall with (P:=fun '(_, idx, _) => @is_tbl_ty idx t = true) in H0.
      2: intros; repeat case_match; auto.
      repeat apply_Forall_In. cbn in *.
      apply to_idx_wf in H1; auto.
      erewrite NoDup_In_access_record; eauto.
      2:{ erewrite in_map_iff. exists (s, to_idx).
          subst; intuition auto.
          erewrite in_map_iff. exists (s, i, P); auto. }
      rewrite fst_map_fst, map_fst_map_triple; auto.
    Qed.

    Instance compo_idx : IndexInterface2.index := IndexInterface2.mk hole0 to_compo_idx compo_idx_ty compo_is_tbl_ty.

    Instance compo_idx_ok : IndexInterface2.ok compo_idx compo_idx_wf :=
      IndexInterface2.Build_ok compo_idx compo_idx_wf compo_idx_ty_wf to_compo_idx_ty to_compo_idx_wf.
  End WithMap.
End compo_idx.

Section WithTags.
  Context (id_tag aux_tag: string).
  Context (tbl : string).
  Context (idx : IndexInterface2.index).

  Definition create_aux_write_head (free_vars : list string) (c : command) :=
    match c with
    | CAssign tbl' e =>
        if String.eqb tbl tbl'
        then CAssign tbl (ERecord [(id_tag, e); (aux_tag, substitute ((@hole idx, e) :: nil) free_vars (@to_idx idx))])
        else c
    | _ => c
    end.

  Definition create_aux_read_head (e : expr) :=
    match e with
    | ELoc x => if String.eqb tbl x
                then (EAccess (ELoc tbl) id_tag)
                else e
    | _ => e
    end.
End WithTags.
