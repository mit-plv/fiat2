Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils fiat2.Substitute
  fiat2.TransfSound fiat2.TransfUtils.
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

Fixpoint replace_loc (x h : string) (e : expr) : expr :=
  match e with
  | EVar y => EVar y
  | ELoc y => if String.eqb y x then EVar h else ELoc y
  | EAtom a => EAtom a
  | EUnop o e => EUnop o (replace_loc x h e)
  | EBinop o e1 e2 => EBinop o (replace_loc x h e1) (replace_loc x h e2)
  | ETernop o e1 e2 e3 => ETernop o (replace_loc x h e1) (replace_loc x h e2) (replace_loc x h e3)
  | EIf e1 e2 e3 => EIf (replace_loc x h e1) (replace_loc x h e2) (replace_loc x h e3)
  | ELet e1 y e2 => ELet (replace_loc x h e1) y (replace_loc x h e2)
  | EFlatmap tag e1 y e2 => EFlatmap tag (replace_loc x h e1) y (replace_loc x h e2)
  | EFold e1 e2 y z e3 => EFold (replace_loc x h e1) (replace_loc x h e2) y z (replace_loc x h e3)
  | EACFold ag e => EACFold ag (replace_loc x h e)
  | EACIFold ag e => EACIFold ag (replace_loc x h e)
  | ERecord l => ERecord (List.map (fun p => (fst p, replace_loc x h (snd p))) l)
  | EAccess e s => EAccess (replace_loc x h e) s
  | EOptMatch e e_none y e_some => EOptMatch (replace_loc x h e) (replace_loc x h e_none) y (replace_loc x h e_some)
  | ESort tag e => ESort tag (replace_loc x h e)
  end.

Fixpoint binders (e : expr) : list string :=
  match e with
  | EVar _ | ELoc _ | EAtom _ => nil
  | EUnop _ e | EACFold _ e | EACIFold _ e | EAccess e _ | ESort _ e => binders e
  | EBinop _ e1 e2 => binders e1 ++ binders e2
  | ETernop _ e1 e2 e3 | EIf e1 e2 e3 => binders e1 ++ binders e2 ++ binders e3
  | ELet e1 y e2 | EFlatmap _ e1 y e2 => y :: binders e1 ++ binders e2
  | EFold e1 e2 y z e3 => y :: z :: binders e1 ++ binders e2 ++ binders e3
  | ERecord l => fold_right (fun p acc => binders (snd p) ++ acc) nil l
  | EOptMatch e e_none y e_some => y :: binders e ++ binders e_none ++ binders e_some
  end.

Fixpoint loc_in (x : string) (e : expr) : bool :=
  match e with
  | EVar _ | EAtom _ => false
  | ELoc y => String.eqb x y
  | EUnop _ e | EACFold _ e | EACIFold _ e | EAccess e _ | ESort _ e => loc_in x e
  | EBinop _ e1 e2 => loc_in x e1 || loc_in x e2
  | ETernop _ e1 e2 e3 | EIf e1 e2 e3 => loc_in x e1 || loc_in x e2 || loc_in x e3
  | ELet e1 _ e2 | EFlatmap _ e1 _ e2 => loc_in x e1 || loc_in x e2
  | EFold e1 e2 _ _ e3 => loc_in x e1 || loc_in x e2 || loc_in x e3
  | ERecord l => existsb (fun p => loc_in x (snd p)) l
  | EOptMatch e e_none _ e_some => loc_in x e || loc_in x e_none || loc_in x e_some
  end.

Fixpoint access_path (e : expr) (p : list string) : expr :=
  match p with
  | nil => e
  | f :: p => access_path (EAccess e f) p
  end.

Definition inv_mentions (x : string) (i : invariant) : bool :=
  match i with
  | ConstraintInv tbl _ _ cond => String.eqb tbl x || loc_in x cond
  | IndexInv tbl _ _ _ _ => String.eqb tbl x
  end.

(* Whether i holds once x is assigned e, decided before the assignment *)
Definition inv_guard (x : string) (e : expr) (i : invariant) : expr :=
  match i with
  | ConstraintInv tbl path row cond =>
      let h := fresh_var "_new" (row :: binders cond) in
      let acc := fresh_var "_acc" (h :: row :: nil) in
      let src := if String.eqb tbl x then EVar h else ELoc tbl in
      ELet e h (EFold (access_path src path) (EAtom (ABool true)) row acc
                  (EIf (replace_loc x h cond) (EVar acc) (EAtom (ABool false))))
  | IndexInv tbl id_path aux_path hole to_idx =>
      let h := "_new" in
      let src := if String.eqb tbl x then EVar h else ELoc tbl in
      ELet e h (EBinop OEq (access_path src aux_path) (ELet (access_path src id_path) hole to_idx))
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

  Lemma replace_loc_sem : forall x h v e (store env : locals),
      ~ In h (binders e) -> map.get env h = Some v ->
      interp_expr store env (replace_loc x h e) = interp_expr (map.put store x v) env e.
  Proof.
    intros x h v e. induction e using expr_IH; intros store env H_h H_env; cbn [replace_loc binders] in *.
    all: cbn [In] in H_h; repeat rewrite in_app_iff in H_h.
    all: cbn [interp_expr].
    1: reflexivity.
    1:{ destruct (String.eqb x0 x) eqn:E; rewrite ?eqb_eq, ?eqb_neq in E; subst; cbn [interp_expr];
        unfold get_local.
        1: rewrite map.get_put_same, H_env; reflexivity.
        1: rewrite map.get_put_diff by congruence; reflexivity. }
    1: reflexivity.
    all: try (rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3 by (auto; intuition idtac); reflexivity).
    (* ELet *)
    1:{ rewrite IHe1 by (try assumption; intuition idtac). apply IHe2; [ intuition idtac | ].
        rewrite map.get_put_diff by intuition congruence. assumption. }
    (* EFlatmap *)
    1:{ rewrite IHe1 by (try assumption; intuition idtac).
        destruct tag; destruct (interp_expr (map.put store x v) env e1); try reflexivity.
        all: erewrite flat_map_ext; [ reflexivity | intros; cbn beta ].
        all: rewrite IHe2; [ reflexivity | intuition idtac | ].
        all: try (rewrite map.get_put_diff by intuition congruence; exact H_env).
        all: exact H_env. }
    (* EFold *)
    1:{ rewrite IHe1, IHe2 by (try assumption; intuition idtac).
        destruct (interp_expr (map.put store x v) env e1); try reflexivity.
        apply fold_right_ext; intros.
        apply IHe3; [ intuition idtac | ].
        rewrite !map.get_put_diff by intuition congruence. assumption. }
    (* ERecord *)
    1:{ do 2 f_equal. rewrite map_map. apply map_ext_in.
        intros [ s e ] H_in. cbn. f_equal.
        rewrite Forall_forall in H. apply (H (s, e)); [ exact H_in | | exact H_env ].
        intro contra. apply H_h. clear H H_h. induction l as [ | p l IH ]; cbn in *; [ contradiction | ].
        rewrite in_app_iff. destruct H_in as [ -> | H_in ]; [ left; exact contra | right; apply IH; exact H_in ]. }
    (* EOptMatch *)
    1:{ rewrite IHe1 by (try assumption; intuition idtac).
        destruct (interp_expr (map.put store x v) env e1) as [ | | | [ v' | ] | | | | | | ]; try reflexivity.
        1:{ apply IHe3; [ intuition idtac | ].
            rewrite map.get_put_diff by intuition congruence. assumption. }
        1: apply IHe2; intuition idtac. }
  Qed.

  Lemma loc_in_false_sem : forall x v e (store env : locals),
      loc_in x e = false ->
      interp_expr (map.put store x v) env e = interp_expr store env e.
  Proof.
    intros x v e. induction e using expr_IH; intros store env H_x; cbn [loc_in] in H_x; cbv beta in *.
    all: repeat rewrite Bool.orb_false_iff in H_x.
    all: cbn [interp_expr].
    all: try (rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3 by tauto; reflexivity).
    (* ELoc *)
    1:{ unfold get_local. rewrite map.get_put_diff; [ reflexivity | ].
        intro; subst; rewrite eqb_refl in H_x; discriminate. }
    (* EFlatmap *)
    1:{ rewrite IHe1 by tauto.
        destruct tag; destruct (interp_expr store env e1); try reflexivity.
        all: erewrite flat_map_ext; [ reflexivity | intros; cbn beta ].
        all: rewrite IHe2 by tauto; reflexivity. }
    (* EFold *)
    1:{ rewrite IHe1, IHe2 by tauto.
        destruct (interp_expr store env e1); try reflexivity.
        apply fold_right_ext; intros. apply IHe3; tauto. }
    (* ERecord *)
    1:{ do 2 f_equal. apply map_ext_in. intros [ s e ] H_in. f_equal.
        rewrite Forall_forall in H. apply (H (s, e) H_in).
        cbn [snd]. destruct (loc_in x e) eqn:E; [ | reflexivity ].
        rewrite <- H_x. symmetry. apply existsb_exists. exists (s, e); auto. }
    (* EOptMatch *)
    1:{ rewrite IHe1 by tauto.
        destruct (interp_expr store env e1) as [ | | | [ v' | ] | | | | | | ]; try reflexivity.
        1: apply IHe3; tauto.
        1: apply IHe2; tauto. }
  Qed.

  Lemma inv_holds_put_unmentioned : forall x v i (store : locals),
      inv_mentions x i = false ->
      inv_holds (map.put store x v) i <-> inv_holds store i.
  Proof.
    intros * H_x. destruct i as [ tbl path row cond | tbl id_path aux_path hole to_idx ];
      cbn [inv_mentions inv_holds] in *.
    all: rewrite ?Bool.orb_false_iff in H_x.
    all: rewrite map.get_put_diff by (intro; subst; rewrite eqb_refl in H_x; intuition discriminate).
    2: reflexivity.
    destruct (map.get store tbl) as [ v' | ]; [ | reflexivity ].
    destruct (value_at v' path) as [ [] | ]; try reflexivity.
    split; apply Forall_impl; intros r H_r.
    all: rewrite loc_in_false_sem in * by tauto; assumption.
  Qed.

  Lemma interp_access_path : forall p e (store env : locals) v,
      value_at (interp_expr store env e) p = Some v ->
      interp_expr store env (access_path e p) = v.
  Proof.
    induction p as [ | f p IH ]; cbn; intros e store env v H.
    1: injection H as ->; reflexivity.
    apply IH. cbn [interp_expr].
    destruct (interp_expr store env e); try discriminate.
    destruct (access_record l f) eqn:E; try discriminate.
    rewrite (access_record__record_proj _ _ _ E). assumption.
  Qed.

  Lemma Forall2_access_record_Success : forall A B (P : A -> B -> Prop) l tl s t,
      Forall2 (fun p tp => fst p = fst tp /\ P (snd p) (snd tp)) l tl ->
      access_record tl s = Success t ->
      exists v, access_record l s = Success v.
  Proof.
    induction 1 as [ | [ s0 v0 ] [ s1 t1 ] l tl [ E_s _ ] _ IH ]; cbn in *; intros H_tl; try discriminate.
    subst s1. destruct (String.eqb s s0); eauto.
  Qed.

  Lemma value_at_typed : forall p v t t',
      type_of_value v t -> type_at t p = Some t' ->
      exists v', value_at v p = Some v' /\ type_of_value v' t'.
  Proof.
    induction p as [ | f p IH ]; cbn; intros v t t' H_v H_t.
    1: injection H_t as <-; eauto.
    destruct t; try discriminate.
    lazymatch type of H_t with
    | match access_record ?tl f with _ => _ end = _ =>
        destruct (access_record tl f) eqn:E_t; try discriminate
    end.
    inversion H_v; subst.
    lazymatch goal with H : Forall2 _ _ _ |- _ =>
      destruct (Forall2_access_record_Success _ _ _ _ _ _ _ H E_t) as [ v1 E_v ];
      pose proof (Forall2_access_record_type_of_value _ _ _ _ _ H E_v E_t) end.
    rewrite E_v. eapply IH; eassumption.
  Qed.

  Lemma locals_wf_put_typed : forall Gstore (store : locals) x t v,
      locals_wf Gstore store -> map.get Gstore x = Some t -> type_of_value v t ->
      locals_wf Gstore (map.put store x v).
  Proof.
    unfold locals_wf; intros * H_wf H_x H_v y ty H_y.
    destruct (String.eqb y x) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
    1: rewrite map.get_put_same; rewrite H_x in H_y; injection H_y as <-; assumption.
    1: rewrite map.get_put_diff by assumption; apply H_wf; assumption.
  Qed.

  Lemma fold_right_all_iff : forall (f : value -> value -> value) (b : value -> bool) l,
      (forall r a, In r l -> f r a = if b r then a else VBool false) ->
      fold_right f (VBool true) l = VBool true <-> Forall (fun r => b r = true) l.
  Proof.
    induction l as [ | r l IH ]; cbn; intros H.
    1: split; auto.
    rewrite H by auto. rewrite Forall_cons_iff.
    destruct (b r).
    1: rewrite IH by auto; intuition idtac.
    1: split; [ discriminate | intuition discriminate ].
  Qed.

  Lemma Forall_iff_typed : forall (rows : list value) (P Q : value -> Prop) t,
      Forall (fun r => type_of_value r t) rows ->
      (forall r, type_of_value r t -> P r <-> Q r) ->
      Forall P rows <-> Forall Q rows.
  Proof.
    intros * H_rows H_iff. rewrite !Forall_forall in *.
    split; intros H r H_r; apply H_iff; auto.
  Qed.

  Lemma guard_src_value : forall Gstore tbl ttbl x h v (store env : locals),
      locals_wf Gstore store -> map.get Gstore tbl = Some ttbl ->
      exists vt, map.get (map.put store x v) tbl = Some vt /\
                   interp_expr store (map.put env h v) (if String.eqb tbl x then EVar h else ELoc tbl) = vt.
  Proof.
    intros * H_store H_get.
    destruct (String.eqb tbl x) eqn:E; rewrite ?eqb_eq, ?eqb_neq in E; subst.
    1:{ exists v. rewrite map.get_put_same. cbn [interp_expr]. unfold get_local.
        rewrite map.get_put_same. auto. }
    1:{ pose proof (H_store _ _ H_get) as H_v.
        destruct (map.get store tbl) as [ vt | ] eqn:E_t; try contradiction.
        exists vt. rewrite map.get_put_diff by assumption.
        cbn [interp_expr]. unfold get_local. rewrite E_t. auto. }
  Qed.

  Theorem inv_guard_iff : forall Gstore Genv x t e i (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> inv_wf Gstore i ->
      map.get Gstore x = Some t -> type_of Gstore Genv e t ->
      locals_wf Gstore store -> locals_wf Genv env ->
      interp_expr store env (inv_guard x e i) = VBool true <->
        inv_holds (map.put store x (interp_expr store env e)) i.
  Proof.
    intros * H_Gs H_Ge H_i H_x H_e H_store H_env.
    assert (H_v : type_of_value (interp_expr store env e) t) by (eapply type_sound; eauto).
    destruct H_i as [ tbl path row cond ttbl row_ty H_get H_at H_cond
                    | tbl id_path aux_path hole to_idx ttbl t_id t_aux H_get H_id H_aux H_ti ];
      cbn [inv_guard].
    1:{ set (h := fresh_var "_new" (row :: binders cond)).
        set (acc := fresh_var "_acc" (h :: row :: nil)).
        pose proof (fresh_var_is_fresh "_new" (row :: binders cond)) as H_h; fold h in H_h.
        pose proof (fresh_var_is_fresh "_acc" (h :: row :: nil)) as H_acc; fold acc in H_acc.
        cbn [In] in H_h, H_acc.
        cbn [interp_expr inv_holds].
        set (v := interp_expr store env e) in *.
        assert (H_store' : locals_wf Gstore (map.put store x v)) by (eapply locals_wf_put_typed; eauto).
        destruct (guard_src_value Gstore tbl ttbl x h v store env H_store H_get) as [ vt [ E_vt E_src ] ].
        rewrite E_vt.
        pose proof (H_store' _ _ H_get) as H_vt; rewrite E_vt in H_vt.
        destruct (value_at_typed _ _ _ _ H_vt H_at) as [ vr [ E_vr H_vr ] ].
        inversion H_vr as [ | | | | | rows ? H_rows | | | | | ]; subst.
        rewrite E_vr.
        rewrite (interp_access_path _ _ _ _ (VList rows)) by exact E_vr.
        assert (H_row_ty : type_wf row_ty).
        1:{ assert (H_t : type_wf ttbl) by (eapply H_Gs; eassumption).
            pose proof (type_at_wf _ _ _ H_t H_at) as H_wf.
            inversion H_wf; assumption. }
        assert (H_Grow : tenv_wf (map.put map.empty row row_ty))
          by (apply tenv_wf_step; [ apply tenv_wf_empty | assumption ]).
        set (b := fun r => match interp_expr (map.put store x v) (map.put map.empty row r) cond with
                           | VBool bb => bb
                           | _ => false
                           end).
        cbn [interp_atom].
        rewrite fold_right_all_iff with (b := b).
        1:{ apply Forall_iff_typed with (t := row_ty); [ assumption | ].
            intros r H_r. subst b; cbn beta.
            assert (H_c : type_of_value (interp_expr (map.put store x v) (map.put map.empty row r) cond) TBool).
            1:{ eapply type_sound; eauto. apply locals_wf_step; [ apply locals_wf_empty | assumption ]. }
            inversion H_c as [ | bb E_c | | | | | | | | | ].
            split; [ intros ->; reflexivity | intro H; injection H; auto ]. }
        1:{ intros r a H_r. cbn [interp_expr].
            assert (H_hrow : h <> row) by (intro E; apply H_h; left; symmetry; exact E).
            assert (H_hacc : h <> acc) by (intro E; apply H_acc; left; exact E).
            assert (H_rowacc : row <> acc) by (intro E; apply H_acc; right; left; exact E).
            rewrite (replace_loc_sem x h v); [ | tauto | ].
            2: rewrite map.get_put_diff, map.get_put_diff, map.get_put_same by assumption; reflexivity.
            rewrite (interp_expr__locals_equiv _ _ _ _ H_Gs H_Grow H_cond
                       (map.put store x v) (map.put map.empty row r) (map.put store x v)
                       (map.put (map.put (map.put env h v) row r) acc a) H_store').
            2: apply locals_wf_step; [ apply locals_wf_empty | rewrite Forall_forall in H_rows; auto ].
            2: apply locals_equiv_refl.
            2:{ unfold locals_equiv; intros y ty H_y.
                destruct (String.eqb y row) eqn:E_y; rewrite ?eqb_eq, ?eqb_neq in E_y; subst.
                1: rewrite (map.get_put_diff _ row a acc H_rowacc), !map.get_put_same; reflexivity.
                1: rewrite map.get_put_diff, map.get_empty in H_y by assumption; discriminate. }
            subst b; cbn beta.
            assert (H_c : type_of_value (interp_expr (map.put store x v) (map.put map.empty row r) cond) TBool)
              by (eapply type_sound; eauto; apply locals_wf_step;
                  [ apply locals_wf_empty | rewrite Forall_forall in H_rows; auto ]).
            destruct (interp_expr (map.put store x v) (map.put map.empty row r) cond) as [ | bb | | | | | | | | ];
              try (inversion H_c; fail).
            destruct bb; cbn [interp_expr interp_atom]; [ | reflexivity ].
            unfold get_local. rewrite map.get_put_same. reflexivity. } }
    1:{ cbn [interp_expr inv_holds interp_binop].
        set (v := interp_expr store env e) in *.
        assert (H_store' : locals_wf Gstore (map.put store x v)) by (eapply locals_wf_put_typed; eauto).
        destruct (guard_src_value Gstore tbl ttbl x "_new" v store env H_store H_get) as [ vt [ E_vt E_src ] ].
        rewrite E_vt.
        pose proof (H_store' _ _ H_get) as H_vt; rewrite E_vt in H_vt.
        destruct (value_at_typed _ _ _ _ H_vt H_id) as [ v_id [ E_id H_vid ] ].
        destruct (value_at_typed _ _ _ _ H_vt H_aux) as [ v_aux [ E_aux _ ] ].
        rewrite E_id, E_aux.
        rewrite (interp_access_path _ _ _ _ v_aux), (interp_access_path _ _ _ _ v_id)
          by (rewrite E_src; eassumption).
        assert (H_tid : type_wf t_id)
          by (apply (type_at_wf id_path ttbl t_id); [ eapply H_Gs; exact H_get | exact H_id ]).
        rewrite (interp_expr__locals_equiv _ _ _ _ tenv_wf_empty
                   (tenv_wf_step _ _ tenv_wf_empty H_tid hole) H_ti
                   map.empty (map.put map.empty hole v_id) store
                   (map.put (map.put env "_new" v) hole v_id)).
        2: apply locals_wf_empty.
        2: apply locals_wf_step; [ apply locals_wf_empty | assumption ].
        2: unfold locals_equiv; intros y ty H_y; rewrite map.get_empty in H_y; discriminate.
        2:{ unfold locals_equiv; intros y ty H_y.
            destruct (String.eqb y hole) eqn:E_y; rewrite ?eqb_eq, ?eqb_neq in E_y; subst.
            1: rewrite !map.get_put_same; reflexivity.
            1: rewrite map.get_put_diff, map.get_empty in H_y by assumption; discriminate. }
        split.
        1: intro H; injection H as H; apply value_eqb_eq; assumption.
        1: intros ->; rewrite value_eqb_refl; reflexivity. }
  Qed.

  Lemma maintains_invs_path_cond_impl : forall Gstore Genv ictx path_cond c,
      maintains_invs Gstore Genv ictx path_cond c ->
      forall path_cond' : locals -> locals -> Prop,
        (forall store env, path_cond' store env -> holds_all store ictx ->
                           locals_wf Gstore store -> locals_wf Genv env -> path_cond store env) ->
        maintains_invs Gstore Genv ictx path_cond' c.
  Proof.
    induction 1; intros path_cond' H_imp.
    all: econstructor; eauto.
    1: apply IHmaintains_invs1. 2: apply IHmaintains_invs2.
    all: intros * [ H_pc H_e ] H_h H_store H_env; split; eauto.
  Qed.

  Lemma holds_all_incl : forall (store : locals) ictx ictx',
      incl ictx' ictx -> holds_all store ictx -> holds_all store ictx'.
  Proof.
    unfold holds_all; intros. eapply incl_Forall; eassumption.
  Qed.

  Lemma holds_all_put_fresh : forall Gstore x v ictx (store : locals),
      tenv_wf Gstore -> Forall (inv_wf Gstore) ictx -> locals_wf Gstore store ->
      map.get Gstore x = None ->
      holds_all store ictx -> holds_all (map.put store x v) ictx.
  Proof.
    intros * H_Gs H_ictx H_store H_x H_h.
    eapply Forall_impl; [ | apply Forall_and; [ exact H_ictx | exact H_h ] ].
    intros i [ H_i H_hi ].
    eapply inv_holds__locals_equiv; [ | eassumption | eassumption | | eassumption ]; auto.
    unfold locals_equiv; intros y ty H_y.
    rewrite map.get_put_diff; congruence.
  Qed.

  Fixpoint fold_command_with_ictx (f : list invariant -> tenv -> expr -> expr)
    (ictx : list invariant) (Gstore : tenv) (c : command) : command :=
    match c with
    | CSkip => CSkip
    | CSeq c1 c2 => CSeq (fold_command_with_ictx f ictx Gstore c1) (fold_command_with_ictx f ictx Gstore c2)
    | CLet e x c => CLet (fold_expr (f ictx Gstore) e) x (fold_command_with_ictx f ictx Gstore c)
    | CLetMut e x ot invs c =>
        CLetMut (fold_expr (f ictx Gstore) e) x ot invs
          match ot with
          | Some t => fold_command_with_ictx f (invs ++ ictx) (map.put Gstore x t) c
          | None => c
          end
    | CAssign x e => CAssign x (fold_expr (f ictx Gstore) e)
    | CIf e c1 c2 =>
        CIf (fold_expr (f ictx Gstore) e)
          (fold_command_with_ictx f ictx Gstore c1) (fold_command_with_ictx f ictx Gstore c2)
    | CForeach e x c => CForeach (fold_expr (f ictx Gstore) e) x (fold_command_with_ictx f ictx Gstore c)
    end.

  (* A rule may assume the invariant context it is handed holds of the store. *)
  Definition ictx_rule_sound (f : list invariant -> tenv -> expr -> expr) : Prop :=
    forall ictx (Gstore : tenv), tenv_wf Gstore -> Forall (inv_wf Gstore) ictx ->
      preserve_ty Gstore (f ictx Gstore) /\
        forall store : locals, holds_all store ictx -> preserve_sem Gstore store (f ictx Gstore).

  Section WithRule.
    Context (f : list invariant -> tenv -> expr -> expr) (H_f : ictx_rule_sound f).

    Lemma fold_expr_ictx_ty : forall ictx (Gstore Genv : tenv) e t,
        tenv_wf Gstore -> tenv_wf Genv -> Forall (inv_wf Gstore) ictx ->
        type_of Gstore Genv e t -> type_of Gstore Genv (fold_expr (f ictx Gstore) e) t.
    Proof.
      intros * H_Gs H_Ge H_ictx H_e.
      apply fold_expr_preserve_ty; auto. apply H_f; auto.
    Qed.

    Lemma fold_expr_ictx_sem : forall ictx (Gstore Genv : tenv) e t (store env : locals),
        tenv_wf Gstore -> tenv_wf Genv -> Forall (inv_wf Gstore) ictx ->
        type_of Gstore Genv e t ->
        locals_wf Gstore store -> locals_wf Genv env -> holds_all store ictx ->
        interp_expr store env (fold_expr (f ictx Gstore) e) = interp_expr store env e.
    Proof.
      intros * H_Gs H_Ge H_ictx H_e H_store H_env H_h.
      destruct (H_f ictx Gstore H_Gs H_ictx) as [ H_ty H_sem ].
      eapply fold_expr_preserve_sem; eauto.
    Qed.

    Lemma fold_command_with_ictx_maintains : forall Gstore Genv ictx path_cond c,
        maintains_invs Gstore Genv ictx path_cond c ->
        tenv_wf Gstore -> tenv_wf Genv -> Forall (inv_wf Gstore) ictx ->
        forall ictx0, incl ictx0 ictx ->
        maintains_invs Gstore Genv ictx path_cond (fold_command_with_ictx f ictx0 Gstore c).
    Proof.
      induction 1; intros H_Gs H_Ge H_ictx ictx0 H_incl; cbn [fold_command_with_ictx].
      all: assert (H_ictx0 : Forall (inv_wf Gstore) ictx0) by (eapply incl_Forall; eassumption).
      (* CSkip *)
      1: constructor.
      (* CSeq *)
      1: constructor; auto.
      (* CLet *)
      1:{ econstructor; [ eapply fold_expr_ictx_ty; eauto | ].
          apply IHmaintains_invs; auto.
          apply tenv_wf_step; [ assumption | eapply type_of__type_wf; [ | | eassumption ]; assumption ]. }
      (* CLetMut *)
      1:{ assert (H_Gs' : tenv_wf (map.put Gstore x t))
            by (apply tenv_wf_step; [ assumption | eapply type_of__type_wf; [ | | eassumption ]; assumption ]).
          econstructor; [ eapply fold_expr_ictx_ty; eauto | eassumption | | eassumption | eassumption | ].
          1:{ destruct ot as [ t' | ]; [ | assumption ].
              cbn in *; subst t'.
              apply IHmaintains_invs; auto.
              1:{ apply Forall_app; split; [ assumption | ].
                  eapply Forall_impl; [ | exact H_ictx ]. intros.
                  eapply inv_wf_weaken; [ | eassumption ].
                  apply map_incl_step_r; [ apply map_incl_refl | assumption ]. }
              apply incl_app; [ apply incl_appl, incl_refl | apply incl_appr; assumption ]. }
          intros * H_pc H_h H_store H_env.
          erewrite (fold_expr_ictx_sem _ Gstore Genv); eauto using holds_all_incl. }
      (* CAssign *)
      1:{ econstructor; [ eassumption | eapply fold_expr_ictx_ty; eauto | ].
          intros * H_pc H_h H_store H_env.
          erewrite (fold_expr_ictx_sem _ Gstore Genv); eauto using holds_all_incl. }
      (* CIf: the rewritten test has the value of the original one *)
      1:{ econstructor; [ eapply fold_expr_ictx_ty; eauto | | ].
          1: eapply maintains_invs_path_cond_impl; [ apply IHmaintains_invs1; auto | ].
          2: eapply maintains_invs_path_cond_impl; [ apply IHmaintains_invs2; auto | ].
          all: intros * [ H_pc H_e ] H_h H_store H_env; split; [ assumption | ].
          all: erewrite <- (fold_expr_ictx_sem _ Gstore Genv); eauto using holds_all_incl. }
      (* CForeach *)
      1:{ econstructor; [ eapply fold_expr_ictx_ty; eauto | ].
          apply IHmaintains_invs; auto.
          apply tenv_wf_step; [ assumption | ].
          lazymatch goal with H : type_of _ _ _ (TList _) |- _ =>
            apply type_of__type_wf in H as H_wf; [ inversion H_wf; assumption | assumption | assumption ] end. }
    Qed.

    Lemma fold_command_with_ictx_sem : forall Gstore Genv ictx path_cond c,
        maintains_invs Gstore Genv ictx path_cond c ->
        tenv_wf Gstore -> tenv_wf Genv -> Forall (inv_wf Gstore) ictx ->
        forall ictx0, incl ictx0 ictx ->
        forall store env,
          path_cond store env -> locals_wf Gstore store -> locals_wf Genv env -> holds_all store ictx ->
          interp_command store env (fold_command_with_ictx f ictx0 Gstore c) = interp_command store env c.
    Proof.
      induction 1; intros H_Gs H_Ge H_ictx ictx0 H_incl store env H_pc H_store H_env H_h;
        cbn [fold_command_with_ictx interp_command].
      all: assert (H_ictx0 : Forall (inv_wf Gstore) ictx0) by (eapply incl_Forall; eassumption).
      all: assert (H_h0 : holds_all store ictx0) by (eapply holds_all_incl; eassumption).
      (* CSkip *)
      1: reflexivity.
      (* CSeq *)
      1:{ rewrite IHmaintains_invs1 by auto.
          apply IHmaintains_invs2; auto.
          1: eapply (command_type_sound Gstore Genv); eauto using maintains_invs__well_typed.
          eapply (maintains_invs__holds_all Gstore Genv); eauto. }
      (* CLet *)
      1:{ erewrite (fold_expr_ictx_sem _ Gstore Genv) by eauto.
          apply IHmaintains_invs; auto.
          1: apply tenv_wf_step; [ assumption | eapply type_of__type_wf; [ | | eassumption ]; assumption ].
          apply locals_wf_step; [ assumption | eapply type_sound; eauto ]. }
      (* CLetMut *)
      1:{ erewrite (fold_expr_ictx_sem _ Gstore Genv) by eauto.
          destruct ot as [ t' | ]; [ | reflexivity ].
          cbn in *; subst t'.
          assert (H_Gs' : tenv_wf (map.put Gstore x t))
            by (apply tenv_wf_step; [ assumption | eapply type_of__type_wf; [ | | eassumption ]; assumption ]).
          rewrite IHmaintains_invs; auto.
          1:{ apply Forall_app; split; [ assumption | ].
              eapply Forall_impl; [ | exact H_ictx ]. intros.
              eapply inv_wf_weaken; [ | eassumption ].
              apply map_incl_step_r; [ apply map_incl_refl | assumption ]. }
          1: apply incl_app; [ apply incl_appl, incl_refl | apply incl_appr; assumption ].
          1: apply locals_wf_step; [ assumption | eapply type_sound; eauto ].
          apply Forall_app; split.
          1: lazymatch goal with
             | H_init : forall _ _, _ -> _ -> _ -> _ -> holds_all _ invs |- _ => apply H_init; assumption
             end.
          apply (holds_all_put_fresh Gstore); assumption. }
      (* CAssign *)
      1: erewrite (fold_expr_ictx_sem _ Gstore Genv) by eauto; reflexivity.
      (* CIf *)
      1:{ erewrite (fold_expr_ictx_sem _ Gstore Genv) by eauto.
          apply_type_sound e. invert_type_of_value.
          lazymatch goal with H: VBool _ = interp_expr _ _ e |- _ => symmetry in H end.
          destruct b.
          1: apply IHmaintains_invs1; auto.
          1: apply IHmaintains_invs2; auto. }
      (* CForeach *)
      1:{ erewrite (fold_expr_ictx_sem _ Gstore Genv) by eauto.
          apply_type_sound e. invert_type_of_value.
          lazymatch goal with H: VList _ = interp_expr _ _ e |- _ => symmetry in H end.
          assert (H_Ge' : tenv_wf (map.put Genv x t)).
          1:{ apply tenv_wf_step; [ assumption | ].
              lazymatch goal with H : type_of _ _ _ (TList _) |- _ =>
                apply type_of__type_wf in H as H_wf; [ inversion H_wf; assumption | assumption | assumption ] end. }
          lazymatch goal with H: type_of_value (interp_expr _ _ e) _ |- _ => clear H end.
          lazymatch goal with H: interp_expr _ _ e = VList _ |- _ => clear H end.
          clear H_pc H_h0.
          lazymatch goal with H : Forall _ ?l |- context[fold_left _ ?l _] =>
            generalize dependent store; induction H; cbn [fold_left]; intros; auto end.
          rewrite IHmaintains_invs; auto.
          2: apply locals_wf_step; auto.
          apply IHForall; auto.
          1: eapply (command_type_sound Gstore (map.put Genv x t)); eauto using maintains_invs__well_typed;
             apply locals_wf_step; auto.
          eapply (maintains_invs__holds_all Gstore (map.put Genv x t)); eauto; try apply locals_wf_step; auto.
          all: exact I. }
    Qed.
  End WithRule.

  Theorem fold_command_with_ictx_sound : forall f,
      ictx_rule_sound f ->
      inv_transf_sound (fun Gstore _ c => fold_command_with_ictx f nil Gstore c).
  Proof.
    unfold inv_transf_sound; intros * H_f * H_Gs H_Ge H_ictx H_c.
    split.
    1: exact (fold_command_with_ictx_maintains f H_f Gstore Genv ictx _ c H_c H_Gs H_Ge H_ictx nil (incl_nil_l _)).
    intros. apply (fold_command_with_ictx_sem f H_f Gstore Genv ictx _ c H_c H_Gs H_Ge H_ictx nil (incl_nil_l _)); auto.
  Qed.
End WithMap.
