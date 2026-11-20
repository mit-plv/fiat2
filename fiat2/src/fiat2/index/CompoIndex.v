Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils
  fiat2.TransfSound fiat2.TransfUtils fiat2.Invariant fiat2.index.IndexInterface fiat2.index.IndexTransf.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String Sorted Permutation.
Import ListNotations.

Lemma map_fst_map_pair : forall A B D (l : list (A * B)) (f : B -> D),
    List.map fst (List.map (fun '(a, b) => (a, f b)) l) = List.map fst l.
Proof.
  intros; induction l; cbn; auto.
  repeat case_match; cbn; congruence.
Qed.

Section compo_idx.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Notation value := (value).
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Context (idxs : list (string * IndexInterface.index)).
  Context {idxs_ok : Forall (fun '(_, idx) => ok idx) idxs}.
  Context (H_tag_NoDup : NoDup (List.map fst idxs)).
  Context (hole0 : string).
  Context (H_holes_eq : Forall (fun '(_, idx) => @hole idx = hole0) idxs).

  Definition compo_idx_ty (t : type) : type :=
    TRecord (record_sort (List.map (fun '(tag, idx) => (tag, @idx_ty idx t)) idxs)).

  Definition to_compo_idx : expr :=
    ERecord (List.map (fun '(tag, idx) => (tag, @to_idx idx)) idxs).

  Definition compo_idx_wf (v v' : value) : Prop :=
    match v' with
    | VRecord v' =>
        Forall (fun '(tag, idx) =>
                  match access_record v' tag with
                  | Success v' => v' = interp_expr map.empty (map.put map.empty (@hole idx) v) (@to_idx idx)
                  | _ => False
                  end) idxs
    | _ => False
    end.

  Definition compo_is_tbl_ty (t : type) : bool :=
    forallb (fun '(tag, idx) => @is_tbl_ty idx t) idxs.

  Lemma to_compo_idx_ty : forall (t : type),
      type_wf t -> compo_is_tbl_ty t = true ->
      type_of map.empty (map.put map.empty hole0 t) to_compo_idx (compo_idx_ty t).
  Proof.
    unfold compo_is_tbl_ty, to_compo_idx, compo_idx_ty.
    intros. econstructor; eauto using Permuted_record_sort, StronglySorted_record_sort.
    1:{ clear. induction idxs; cbn; auto.
        case_match; cbn; congruence. }
    1:{ induction idxs; auto. cbn in *.
        repeat invert_Forall; invert_NoDup; rewrite Bool.andb_true_iff in *; intuition idtac.
        constructor; auto.
        case_match; cbn; subst. eapply (to_idx_ty (idx:=i)); eauto. }
    1:{ revert H_tag_NoDup; clear; intros.
        rewrite map_fst_map_pair; auto. }
  Qed.

  Lemma to_compo_idx_wf : forall (v : value),
      compo_idx_wf v (interp_expr map.empty (map.put map.empty hole0 v) to_compo_idx).
  Proof.
    intros.
    unfold compo_idx_wf, to_compo_idx, record_proj in *.
    cbn [interp_expr].
    rewrite Forall_forall; intros. case_match.
    erewrite NoDup_Permutation_access_record.
    4: apply Permutation_sym, Permuted_record_sort.
    2:{ eapply Permutation_NoDup.
        1: eapply Permutation_map, Permuted_record_sort.
        rewrite !map_map. erewrite map_ext; [ eassumption | intros [ ? ? ]; reflexivity ]. }
    2:{ rewrite in_map_iff. eexists; intuition idtac.
        2:{ eapply Permutation_in.
            1: apply Permuted_record_sort.
            rewrite in_map_iff. exists (s, to_idx).
            intuition idtac.
            rewrite in_map_iff; exists x.
            subst; auto. }
        reflexivity. }
    eapply List.Forall_In in H_holes_eq as H_h; [ | eassumption ]. cbn in *.
    erewrite NoDup_In_access_record; eauto.
    2:{ erewrite in_map_iff. exists (s, to_idx).
        subst; intuition auto.
        erewrite in_map_iff. exists (s, i); auto. }
    rewrite !map_map. erewrite map_ext; [ eassumption | intros [ ? ? ]; reflexivity ].
  Qed.

  Instance compo_idx : IndexInterface.index := IndexInterface.mk hole0 to_compo_idx compo_idx_ty compo_is_tbl_ty.

  Instance compo_idx_ok : IndexInterface.ok compo_idx :=
    IndexInterface.Build_ok compo_idx to_compo_idx_ty.
End compo_idx.


Lemma record_ext : forall A (l l' : list (string * A)),
    List.map fst l = List.map fst l' -> NoDup (List.map fst l) ->
    (forall k, In k (List.map fst l) -> access_record l k = access_record l' k) -> l = l'.
Proof.
  induction l as [ | [ k v ] l IH ]; destruct l' as [ | [ k' v' ] l' ]; cbn; intros H_k H_nd H_a;
    try discriminate; auto.
  injection H_k as <- H_k. inversion H_nd; subst.
  pose proof (H_a k (or_introl eq_refl)) as H_hd. cbn in H_hd. rewrite String.eqb_refl in H_hd.
  injection H_hd as <-. f_equal. apply IH; auto. intros k0 H_in.
  assert (H_ne : k0 <> k) by (intro; subst; contradiction).
  specialize (H_a k0 (or_intror H_in)). cbn in H_a.
  rewrite (proj2 (String.eqb_neq _ _) H_ne) in H_a. exact H_a.
Qed.

Lemma value_at_cons : forall v f p,
    value_at v (f :: p) = match value_at v [f] with
                          | Some w => value_at w p
                          | None => None
                          end.
Proof.
  intros. destruct v; try reflexivity. cbn. destruct (access_record l f); reflexivity.
Qed.

(* Several indexes on one table are created as their composite, whose
   invariant is then replaced by one invariant per member *)
Section WithIdxs.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Context (idxs : list (string * IndexInterface.index)).
  Context {idxs_ok : Forall (fun '(_, idx) => ok idx) idxs}.
  Context (H_tag_NoDup : NoDup (List.map fst idxs)).
  Context (hole0 : string).
  Context (H_holes_eq : Forall (fun '(_, idx) => @hole idx = hole0) idxs).
  Context (id_tag aux_tag : string) (H_tags_diff : id_tag <> aux_tag).

  Definition member_invs (tbl : string) : list invariant :=
    List.map (fun '(tag, idx) => IndexInv tbl [id_tag] [aux_tag; tag] hole0 (@to_idx idx)) idxs.

  Definition create_idxs (c : command) : command :=
    match c with
    | CLetMut _ _ (Some t) _ _ =>
        if compo_is_tbl_ty idxs t then
          match transf_to_idx (idx := compo_idx idxs hole0) id_tag aux_tag c with
          | CLetMut e' x' ot' (_ :: invs') c' => CLetMut e' x' ot' (member_invs x' ++ invs') c'
          | c' => c'
          end
        else c
    | _ => c
    end.

  Lemma compo_holds_iff : forall (store : locals) tbl v t,
      map.get store tbl = Some v -> type_of_value v (aux_ty (idx := compo_idx idxs hole0) id_tag aux_tag t) ->
      inv_holds store (IndexInv tbl [id_tag] [aux_tag] hole0 (to_compo_idx idxs)) <->
        Forall (inv_holds store) (member_invs tbl).
  Proof.
    intros * E_v H_v. cbn [inv_holds]. rewrite E_v. unfold member_invs. rewrite Forall_map.
    destruct (value_at_typed [id_tag] _ _ t H_v) as (v_id & E_id & _).
    1: cbn [type_at]; unfold aux_ty; rewrite (aux_ty_access_id (idx := compo_idx idxs hole0) _ _ H_tags_diff); reflexivity.
    destruct (value_at_typed [aux_tag] _ _ (compo_idx_ty idxs t) H_v) as (v_aux & E_aux & H_aux).
    1: cbn [type_at]; unfold aux_ty; rewrite (aux_ty_access_aux (idx := compo_idx idxs hole0) _ _ H_tags_diff); reflexivity.
    rewrite E_id, E_aux.
    assert (E_mem : forall tag, value_at v [aux_tag; tag] = value_at v_aux [tag])
      by (intros; rewrite value_at_cons, E_aux; reflexivity).
    unfold compo_idx_ty in H_aux. inversion H_aux; subst.
    lazymatch goal with
    | H_nd : NoDup _, H_f2 : Forall2 _ ?r (record_sort _) |- _ => rename r into rv; rename H_f2 into H_f2'
    end.
    lazymatch goal with H : NoDup (List.map fst (record_sort _)) |- _ => rename H into H_nd end.
    rename H_f2' into H_f2.
    pose proof (to_compo_idx_wf idxs H_tag_NoDup hole0 H_holes_eq v_id) as H_wf.
    split.
    1:{ intros H_eq. rewrite <- H_eq in H_wf. unfold compo_idx_wf in H_wf.
        eapply Forall_impl; [ | apply Forall_and; [ exact H_holes_eq | exact H_wf ] ].
        intros [ tag idx ] [ H_h H_t ]. cbn [inv_holds]. rewrite E_v, E_id, E_mem. cbn [value_at].
        rewrite <- H_h. destruct (access_record rv tag); [ exact H_t | contradiction ]. }
    intros H_m. cbn [to_compo_idx interp_expr]. f_equal.
    set (L := List.map (fun '(tag, idx) => (tag, @idx_ty idx t)) idxs).
    set (M := List.map (fun '(s, e) => (s, interp_expr map.empty (map.put map.empty hole0 v_id) e))
                (List.map (fun '(tag, idx) => (tag, @to_idx idx)) idxs)).
    assert (H_LM : Forall2 (fun p q => fst p = fst q) L M)
      by (subst L M; clear; induction idxs as [ | [ ? ? ] ? IH ]; cbn; constructor; auto).
    assert (H_fL : List.map fst L = List.map fst idxs) by (subst L; apply map_fst_map_pair).
    assert (H_sorted : Forall2 (fun p q => fst p = fst q) (record_sort L) (record_sort M)).
    1:{ eapply Forall2_Permuted_StronglySorted;
          [ exact H_LM | rewrite H_fL; exact H_tag_NoDup | auto
          | apply Permuted_record_sort | apply Permuted_record_sort
          | apply StronglySorted_record_sort | apply StronglySorted_record_sort ]. }
    assert (H_rv : List.map fst rv = List.map fst (record_sort L))
      by (apply Forall2_fst_eq, (proj1 (Forall2_split _ _ _ _ _ _ H_f2))).
    assert (H_keys : List.map fst rv = List.map fst (record_sort M))
      by (rewrite H_rv; apply Forall2_fst_eq; exact H_sorted).
    change (rv = record_sort M).
    apply record_ext; [ exact H_keys | rewrite H_rv; exact H_nd | ].
    intros k H_k. rewrite H_rv in H_k.
    apply (Permutation_in _ (Permutation_map fst (Permutation_sym (Permuted_record_sort L)))) in H_k.
    rewrite H_fL in H_k. apply in_map_iff in H_k as ([ k' idx ] & <- & H_in). cbn [fst].
    rewrite Forall_forall in H_m. specialize (H_m _ H_in). cbn [inv_holds] in H_m.
    rewrite E_v, E_id, E_mem in H_m. cbn [value_at] in H_m.
    destruct (access_record rv k') as [ w | ] eqn:E_k; [ | contradiction ]. rewrite H_m.
    rewrite <- (NoDup_Permutation_access_record k' _ M (record_sort M)); [ | | | apply Permuted_record_sort ].
    1:{ symmetry. apply NoDup_In_access_record.
        1: subst M; rewrite !map_fst_map_pair; exact H_tag_NoDup.
        subst M. rewrite in_map_iff. eexists (k', @to_idx idx); split; [ reflexivity | ].
        rewrite in_map_iff. exists (k', idx); auto. }
    1: subst M; rewrite !map_fst_map_pair; exact H_tag_NoDup.
    subst M; rewrite !map_fst_map_pair. apply in_map_iff. exists (k', idx); auto.
  Qed.
  Lemma compo_members_equiv : forall (Gstore : tenv) tbl t R,
      map.get Gstore tbl = Some (aux_ty (idx := compo_idx idxs hole0) id_tag aux_tag t) ->
      ictx_equiv Gstore (IndexInv tbl [id_tag] [aux_tag] hole0 (to_compo_idx idxs) :: R) (member_invs tbl ++ R).
  Proof.
    unfold ictx_equiv, holds_all; intros * H_tbl store H_store.
    pose proof (H_store _ _ H_tbl) as H_v.
    destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
    rewrite Forall_cons_iff, Forall_app, (compo_holds_iff store tbl v t E_v H_v). reflexivity.
  Qed.

  Lemma member_invs_wf : forall (Gstore : tenv) tbl t,
      type_wf t -> compo_is_tbl_ty idxs t = true ->
      map.get Gstore tbl = Some (aux_ty (idx := compo_idx idxs hole0) id_tag aux_tag t) ->
      Forall (inv_wf Gstore) (member_invs tbl).
  Proof.
    intros * H_wf H_is H_tbl. unfold member_invs. rewrite Forall_map, Forall_forall.
    intros [ tag idx ] H_in.
    assert (H_ok : ok idx) by (rewrite Forall_forall in idxs_ok; exact (idxs_ok _ H_in)).
    assert (H_h : @hole idx = hole0) by (rewrite Forall_forall in H_holes_eq; exact (H_holes_eq _ H_in)).
    assert (H_i : @is_tbl_ty idx t = true)
      by (unfold compo_is_tbl_ty in H_is; rewrite forallb_forall in H_is; exact (H_is _ H_in)).
    econstructor; [ exact H_tbl | | | ].
    1: cbn [type_at]; unfold aux_ty; rewrite (aux_ty_access_id (idx := compo_idx idxs hole0) _ _ H_tags_diff); reflexivity.
    1:{ cbn [type_at]; unfold aux_ty; rewrite (aux_ty_access_aux (idx := compo_idx idxs hole0) _ _ H_tags_diff).
        cbn [IndexInterface.idx_ty compo_idx compo_idx_ty].
        assert (H_L : NoDup (List.map fst (List.map (fun '(tag, idx) => (tag, @idx_ty idx t)) idxs)))
          by (rewrite map_fst_map_pair; exact H_tag_NoDup).
        assert (H_inL : In (tag, @idx_ty idx t) (List.map (fun '(tag, idx) => (tag, @idx_ty idx t)) idxs))
          by (rewrite in_map_iff; exists (tag, idx); auto).
        rewrite <- (NoDup_Permutation_access_record tag _ _ _ H_L (in_map fst _ _ H_inL) (Permuted_record_sort _)).
        rewrite (NoDup_In_access_record _ _ H_L _ _ H_inL). reflexivity. }
    rewrite <- H_h. apply to_idx_ty; assumption.
  Qed.

  Theorem create_idxs_sound : inv_transf_sound (locals := locals) (fun _ _ c => create_idxs c).
  Proof.
    unfold inv_transf_sound; intros * H_Gs H_Ge H_ictx H_m.
    destruct (create_idx_sound (idx := compo_idx idxs hole0)
                (idx_ok := compo_idx_ok idxs (idxs_ok := idxs_ok) H_tag_NoDup hole0 H_holes_eq)
                id_tag aux_tag H_tags_diff Gstore Genv ictx path_cond c H_Gs H_Ge H_ictx H_m) as [ H_m' H_s ].
    unfold create_idxs. destruct c as [ | | | e x [ t | ] invs c0 | | | ];
      try (split; [ exact H_m | intros; reflexivity ]).
    destruct (compo_is_tbl_ty idxs t) eqn:E_is; [ | split; [ exact H_m | intros; reflexivity ] ].
    unfold create_idx in H_m', H_s. cbn [IndexInterface.is_tbl_ty compo_idx] in H_m', H_s.
    rewrite E_is in H_m', H_s. cbn [transf_to_idx] in *.
    assert (H_twf : type_wf t)
      by (inversion H_m; subst; subst_type_annot;
          lazymatch goal with H : type_of _ _ e _ |- _ => exact (type_of__type_wf _ _ _ _ H_Gs H_Ge H) end).
    split.
    1:{ inversion H_m' as [ | | | ? ? t' ? ? ? ? H_init H_annot H_body H_wf H_x H_hold | | | ]; subst.
        cbn in H_annot; subst t'.
        assert (H_Gs' : tenv_wf (map.put Gstore x (aux_ty (idx := compo_idx idxs hole0) id_tag aux_tag t)))
          by (apply tenv_wf_step; [ assumption | eapply type_of__type_wf; [ | | eassumption ]; assumption ]).
        assert (H_eq : forall R, ictx_equiv (map.put Gstore x (aux_ty (idx := compo_idx idxs hole0) id_tag aux_tag t))
                                   (IndexInv x [id_tag] [aux_tag] hole0 (to_compo_idx idxs) :: R) (member_invs x ++ R))
          by (intros; apply (compo_members_equiv _ _ t), map.get_put_same).
        inversion H_wf; subst.
        econstructor; [ eassumption | reflexivity | | | eassumption | ].
        1:{ rewrite <- app_assoc. eapply maintains_invs_ictx_equiv; [ exact H_body | exact H_Gs' | exact H_Ge | ].
            apply H_eq. }
        1:{ apply Forall_app; split; [ | assumption ].
            eapply member_invs_wf; [ exact H_twf | exact E_is | apply map.get_put_same ]. }
        intros store env H_pc H_h H_store H_env.
        apply (H_eq _ (map.put store x (interp_expr store env _))).
        1: apply locals_wf_step; [ assumption | eapply type_sound; eauto ].
        apply H_hold; assumption. }
    intros store env H_pc H_store H_env H_h. rewrite <- H_s by assumption. reflexivity.
  Qed.
End WithIdxs.
