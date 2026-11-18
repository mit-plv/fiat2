Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String.
Import ListNotations.

Fixpoint value_at (v : value) (p : list string) : option value :=
  match p with
  | nil => Some v
  | f :: p' => match v with
               | VRecord rv => match access_record rv f with
                               | Success v' => value_at v' p'
                               | Failure _ => None
                               end
               | _ => None
               end
  end.

Section WithMap.
  Notation value := (value).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Definition inv_holds (store : locals) (i : invariant) : Prop :=
    match i with
    | ConstraintInv tbl path row cond =>
        match map.get store tbl with
        | Some v => match value_at v path with
                    | Some (VList rows) =>
                        Forall (fun r => interp_expr store (map.put map.empty row r) cond = VBool true) rows
                    | _ => False
                    end
        | None => False
        end
    | IndexInv tbl id_path aux_path hole to_idx =>
        match map.get store tbl with
        | Some v => match value_at v id_path, value_at v aux_path with
                    | Some v_id, Some v_aux =>
                        v_aux = interp_expr map.empty (map.put map.empty hole v_id) to_idx
                    | _, _ => False
                    end
        | None => False
        end
    end.

  Definition holds_all (store : locals) (ictx : list invariant) : Prop :=
    Forall (inv_holds store) ictx.

  Inductive maintains_invs (Gstore Genv : tenv) (ictx : list invariant)
    : (locals -> locals -> Prop) -> command -> Prop :=
  | MICSkip path_cond : maintains_invs Gstore Genv ictx path_cond CSkip
  | MICSeq path_cond c1 c2 :
    maintains_invs Gstore Genv ictx path_cond c1 ->
    maintains_invs Gstore Genv ictx (fun _ _ => True) c2 ->
    maintains_invs Gstore Genv ictx path_cond (CSeq c1 c2)
  | MICLet path_cond e t x c :
    type_of Gstore Genv e t ->
    maintains_invs Gstore (map.put Genv x t) ictx (fun _ _ => True) c ->
    maintains_invs Gstore Genv ictx path_cond (CLet e x c)
  | MICLetMut path_cond e t x ot invs c :
    type_of Gstore Genv e t ->
    type_annot_ok ot t ->
    maintains_invs (map.put Gstore x t) Genv (invs ++ ictx) (fun _ _ => True) c ->
    Forall (inv_wf (map.put Gstore x t)) invs ->
    map.get Gstore x = None ->
    (forall store env,
        path_cond store env -> holds_all store ictx ->
        locals_wf Gstore store -> locals_wf Genv env ->
        holds_all (map.put store x (interp_expr store env e)) invs) ->
    maintains_invs Gstore Genv ictx path_cond (CLetMut e x ot invs c)
  | MICAssign path_cond x t e :
    map.get Gstore x = Some t ->
    type_of Gstore Genv e t ->
    (forall store env,
        path_cond store env -> holds_all store ictx ->
        locals_wf Gstore store -> locals_wf Genv env ->
        holds_all (map.put store x (interp_expr store env e)) ictx) ->
    maintains_invs Gstore Genv ictx path_cond (CAssign x e)
  | MICIf path_cond e c1 c2 :
    type_of Gstore Genv e TBool ->
    maintains_invs Gstore Genv ictx
      (fun store env => path_cond store env /\ interp_expr store env e = VBool true) c1 ->
    maintains_invs Gstore Genv ictx
      (fun store env => path_cond store env /\ interp_expr store env e = VBool false) c2 ->
    maintains_invs Gstore Genv ictx path_cond (CIf e c1 c2)
  | MICForeach path_cond e t x c :
    type_of Gstore Genv e (TList t) ->
    maintains_invs Gstore (map.put Genv x t) ictx (fun _ _ => True) c ->
    maintains_invs Gstore Genv ictx path_cond (CForeach e x c).

  Lemma maintains_invs__well_typed : forall Gstore Genv ictx path_cond c,
      maintains_invs Gstore Genv ictx path_cond c -> well_typed Gstore Genv c.
  Proof.
    induction 1; econstructor; eauto.
  Qed.

  Lemma Forall2_access_record_type_of_value : forall l tl s v t,
      Forall2 (fun p tp => fst p = fst tp /\ type_of_value (snd p) (snd tp)) l tl ->
      access_record l s = Success v -> access_record tl s = Success t ->
      type_of_value v t.
  Proof.
    induction 1 as [ | [ s0 v0 ] [ s1 t1 ] l tl [ E_s H_v ] _ IH ]; cbn in *;
      intros H_l H_tl; try discriminate.
    subst s1. destruct (String.eqb s s0).
    1: injection H_l as <-; injection H_tl as <-; assumption.
    1: eauto.
  Qed.

  Lemma value_at_type_of_value : forall p v t v' t',
      type_of_value v t -> type_at t p = Some t' -> value_at v p = Some v' ->
      type_of_value v' t'.
  Proof.
    induction p as [ | f p IH ]; cbn; intros v t v' t' H_v H_t H_p.
    1: injection H_t as <-; injection H_p as <-; assumption.
    destruct t; try discriminate.
    lazymatch type of H_t with
    | match access_record ?tl f with _ => _ end = _ =>
        destruct (access_record tl f) eqn:E_t; try discriminate
    end.
    destruct v; try discriminate.
    lazymatch type of H_p with
    | match access_record ?rv f with _ => _ end = _ =>
        destruct (access_record rv f) eqn:E_v; try discriminate
    end.
    inversion H_v; subst.
    eapply IH; [ | eassumption | eassumption ].
    eapply Forall2_access_record_type_of_value; eassumption.
  Qed.

  Lemma locals_wf_empty : forall (l : locals), locals_wf map.empty l.
  Proof.
    unfold locals_wf; intros. rewrite map.get_empty in *; discriminate.
  Qed.

  (* What an invariant says depends only on the mutable variables it is
     typed against. *)
  Lemma inv_holds__locals_equiv : forall Gstore i (store store' : locals),
      tenv_wf Gstore -> inv_wf Gstore i -> locals_wf Gstore store ->
      locals_equiv Gstore store store' ->
      inv_holds store i -> inv_holds store' i.
  Proof.
    intros * H_Gs H_i H_store H_eq H.
    destruct H_i as [ tbl path row cond t row_ty H_get H_at H_cond
                    | tbl id_path aux_path hole to_idx t t_id t_aux H_get H_id H_aux H_ti ];
      cbn [inv_holds] in *.
    all: rewrite <- (H_eq _ _ H_get).
    2: assumption.
    assert (H_row_ty : type_wf row_ty).
    1:{ assert (H_t : type_wf t) by (eapply H_Gs; eassumption).
        pose proof (type_at_wf _ _ _ H_t H_at) as H_wf.
        inversion H_wf; assumption. }
    pose proof (H_store _ _ H_get) as H_v.
    destruct (map.get store tbl) as [ v | ]; try contradiction.
    destruct (value_at v path) as [ [] | ] eqn:E_p; try contradiction.
    eapply value_at_type_of_value in E_p as H_rows; [ | eassumption | eassumption ].
    inversion H_rows as [ | | | | | ? ? H_all | | | | | ]; subst.
    rewrite Forall_forall in *. intros r H_r.
    assert (H_Genv : tenv_wf (map.put map.empty row row_ty))
      by (apply tenv_wf_step; [ apply tenv_wf_empty | assumption ]).
    assert (H_env : locals_wf (map.put map.empty row row_ty) (map.put map.empty row r))
      by (apply locals_wf_step; [ apply locals_wf_empty | auto ]).
    rewrite (interp_expr__locals_equiv _ _ _ _ H_Gs H_Genv H_cond _ _ _ _
               H_store H_env H_eq (locals_equiv_refl _ _)).
    apply H; assumption.
  Qed.

  Lemma inv_wf_weaken : forall Gstore Gstore' i,
      map_incl Gstore Gstore' -> inv_wf Gstore i -> inv_wf Gstore' i.
  Proof.
    intros * H_incl H_i. inversion H_i; subst; econstructor; eauto.
    eapply type_of_strengthen; eauto using map_incl_refl.
  Qed.

  Lemma locals_wf_put_fresh : forall Gstore (store : locals) x t,
      map.get Gstore x = None ->
      locals_wf (map.put Gstore x t) store -> locals_wf Gstore store.
  Proof.
    unfold locals_wf; intros * H_x H_wf y ty H_y.
    apply H_wf. rewrite map.get_put_diff; congruence.
  Qed.

  Theorem maintains_invs__holds_all : forall Gstore Genv ictx path_cond c,
      tenv_wf Gstore -> tenv_wf Genv -> Forall (inv_wf Gstore) ictx ->
      maintains_invs Gstore Genv ictx path_cond c ->
      forall store env,
        path_cond store env ->
        locals_wf Gstore store -> locals_wf Genv env ->
        holds_all store ictx -> holds_all (interp_command store env c) ictx.
  Proof.
    intros * H_Gs H_Ge H_ictx H.
    induction H; cbn [interp_command]; intros store env H_pc H_store H_env H_holds.
    (* CSkip *)
    1: assumption.
    (* CSeq *)
    1:{ apply IHmaintains_invs2; auto.
        eapply command_type_sound; eauto using maintains_invs__well_typed. }
    (* CLet *)
    1:{ apply IHmaintains_invs; auto.
        1: apply tenv_wf_step; [ assumption | eapply type_of__type_wf; [ | | eassumption ]; assumption ].
        1: apply locals_wf_step; [ assumption | eapply type_sound; eauto ]. }
    (* CLetMut: the outer invariants cannot mention x, so they are unaffected
       both by its introduction and by its removal *)
    1:{ assert (H_Gs' : tenv_wf (map.put Gstore x t))
          by (apply tenv_wf_step; [ assumption | eapply type_of__type_wf; [ | | eassumption ]; assumption ]).
        assert (H_ictx' : Forall (inv_wf (map.put Gstore x t)) ictx).
        1:{ eapply Forall_impl; [ | exact H_ictx ]. intros.
            eapply inv_wf_weaken; [ | eassumption ].
            apply map_incl_step_r; [ apply map_incl_refl | assumption ]. }
        set (store' := map.put store x (interp_expr store env e)).
        assert (H_store' : locals_wf (map.put Gstore x t) store')
          by (apply locals_wf_step; [ assumption | eapply type_sound; eauto ]).
        assert (H_c : holds_all (interp_command store' env c) (invs ++ ictx)).
        1:{ apply IHmaintains_invs; auto.
            1: apply Forall_app; auto.
            apply Forall_app; split.
            1: lazymatch goal with
               | H_init : forall _ _, _ -> _ -> _ -> _ -> holds_all _ invs |- _ =>
                   apply H_init; assumption
               end.
            eapply Forall_impl; [ | apply Forall_and; [ exact H_ictx | exact H_holds ] ].
            intros i [ H_i H_h ].
            eapply inv_holds__locals_equiv; [ | eassumption | eassumption | | eassumption ];
              auto.
            unfold locals_equiv; intros y ty H_y. subst store'.
            rewrite map.get_put_diff; congruence. }
        apply Forall_app in H_c as [ _ H_c ].
        assert (H_wf_c : locals_wf Gstore (interp_command store' env c)).
        1:{ eapply locals_wf_put_fresh; [ eassumption | ].
            eapply command_type_sound; eauto using maintains_invs__well_typed. }
        eapply Forall_impl; [ | apply Forall_and; [ exact H_ictx | exact H_c ] ].
        intros i [ H_i H_h ].
        eapply inv_holds__locals_equiv; [ | eassumption | eassumption | | eassumption ]; auto.
        unfold locals_equiv; intros y ty H_y.
        rewrite Properties.map.get_update_diff; congruence. }
    (* CAssign *)
    1: lazymatch goal with
       | H_obl : forall _ _, _ -> _ -> _ -> _ -> holds_all _ ictx |- _ =>
           apply H_obl; assumption
       end.
    (* CIf: each branch runs under the outcome of the test *)
    1:{ apply_type_sound e. invert_type_of_value.
        lazymatch goal with H: VBool _ = interp_expr _ _ e |- _ => symmetry in H end.
        destruct b.
        1: apply IHmaintains_invs1; auto.
        1: apply IHmaintains_invs2; auto. }
    (* CForeach: the body runs once per row, each in a different store *)
    1:{ apply_type_sound e. invert_type_of_value.
        lazymatch goal with H: type_of_value _ _ |- _ => clear H end.
        lazymatch goal with H: VList _ = interp_expr _ _ e |- _ => clear H end.
        clear H_pc.
        generalize dependent store. induction l; cbn; auto; intros.
        invert_Forall. apply IHl; auto.
        2:{ apply IHmaintains_invs; eauto with fiat2_hints. }
        eapply command_type_sound.
        5: apply locals_wf_step. all: eauto with fiat2_hints.
        eapply maintains_invs__well_typed; eauto. }
  Qed.

  Definition ictx_equiv (Gstore : tenv) (ictx ictx' : list invariant) : Prop :=
    forall store, locals_wf Gstore store -> holds_all store ictx <-> holds_all store ictx'.

  Lemma ictx_equiv_app : forall Gstore x t invs ictx ictx',
      map.get Gstore x = None ->
      ictx_equiv Gstore ictx ictx' ->
      ictx_equiv (map.put Gstore x t) (invs ++ ictx) (invs ++ ictx').
  Proof.
    unfold ictx_equiv, holds_all; intros * H_x H_eq store H_store.
    apply locals_wf_put_fresh in H_store; [ | assumption ].
    rewrite !Forall_app, H_eq by assumption. reflexivity.
  Qed.

  Lemma maintains_invs_ictx_equiv : forall Gstore Genv ictx path_cond c,
      maintains_invs Gstore Genv ictx path_cond c ->
      tenv_wf Gstore -> tenv_wf Genv ->
      forall ictx', ictx_equiv Gstore ictx ictx' ->
      maintains_invs Gstore Genv ictx' path_cond c.
  Proof.
    induction 1; intros H_Gs H_Ge ictx' H_eq.
    all: econstructor; eauto.
    (* CLet *)
    1: apply IHmaintains_invs; auto;
    apply tenv_wf_step; [ assumption | eapply type_of__type_wf; [ | | eassumption ]; assumption ].
    (* CLetMut *)
    1:{ apply IHmaintains_invs; [ | assumption | apply ictx_equiv_app; assumption ].
        apply tenv_wf_step; [ assumption | eapply type_of__type_wf; [ | | eassumption ]; assumption ]. }
    1:{ intros * H_pc H_h H_store H_env.
        lazymatch goal with
        | H_init : forall _ _, _ -> _ -> _ -> _ -> holds_all _ invs |- _ => apply H_init
        end; auto.
        apply H_eq; assumption. }
    (* CAssign *)
    1:{ intros * H_pc H_h H_store H_env. apply H_eq.
        1:{ unfold locals_wf; intros y ty H_y. destruct (String.eqb y x) eqn:E.
            1:{ apply String.eqb_eq in E; subst. rewrite map.get_put_same.
                rewrite H in H_y; injection H_y as <-. eapply type_sound; eauto. }
            1:{ apply String.eqb_neq in E. rewrite map.get_put_diff by assumption.
                apply H_store; assumption. } }
        lazymatch goal with
        | H_obl : forall _ _, _ -> _ -> _ -> _ -> holds_all _ ictx |- _ => apply H_obl
        end; auto.
        apply H_eq; assumption. }
    (* CForeach *)
    1:{ apply IHmaintains_invs; auto.
        apply tenv_wf_step; [ assumption | ].
        apply type_of__type_wf in H; [ | assumption | assumption ].
        inversion H; assumption. }
  Qed.

  (* A transformation is sound if it keeps the invariant context of the
     command it is handed maintained, and computes the same stores wherever
     that context holds. *)
  Definition inv_transf_sound (f : tenv -> tenv -> command -> command) : Prop :=
    forall (Gstore Genv : tenv) ictx c,
      tenv_wf Gstore -> tenv_wf Genv -> Forall (inv_wf Gstore) ictx ->
      maintains_invs Gstore Genv ictx (fun _ _ => True) c ->
      maintains_invs Gstore Genv ictx (fun _ _ => True) (f Gstore Genv c) /\
        forall (store env : locals),
          locals_wf Gstore store -> locals_wf Genv env -> holds_all store ictx ->
          interp_command store env (f Gstore Genv c) = interp_command store env c.

  Lemma inv_transf_sound_compose : forall f g,
      inv_transf_sound f -> inv_transf_sound g ->
      inv_transf_sound (fun Gstore Genv => Basics.compose (f Gstore Genv) (g Gstore Genv)).
  Proof.
    unfold inv_transf_sound; intros * H_f H_g * H_Gs H_Ge H_ictx H_c.
    apply H_g in H_c as [ H_c H_sem_g ]; auto.
    apply H_f in H_c as [ H_c H_sem_f ]; auto.
    split; [ exact H_c | ].
    intros. unfold Basics.compose. rewrite H_sem_f, H_sem_g; auto.
  Qed.
End WithMap.
