Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.Invariant.
Require Import coqutil.Map.Interface.
From Stdlib Require Import String List.
Import ListNotations.

(* A surface language with declared constraints, and its elaboration into the
   core.

   A declaration introduces a mutable variable born empty together with the
   constraints that must hold of it.  Each constraint is a condition on a row,
   which may read the table, or any other table in scope, through ELoc.
   Elaboration turns the constraints into the binder's invariants, and inserts
   a check at every assignment that can affect an invariant in scope, turning

     x := e  else  policy

   into

     if <every invariant mentioning x, read of e> then x := e else policy.

   So the policy a programmer writes at a write site is simply the else branch:
   it is an ordinary command, and if it assigns to a constrained variable it is
   elaborated too and gets its own check. *)

Inductive scommand : Type :=
| SSkip
| SSeq (c1 c2 : scommand)
| SLet (e : expr) (x : string) (c : scommand)
| SLetMut (e : expr) (x : string) (c : scommand)
(* x is born empty, holds rows of row_ty, and every (row, cond) in ds must hold
   of each of its rows for as long as it is in scope *)
| SLetConstrained (x : string) (row_ty : type) (ds : list (string * expr)) (c : scommand)
(* policy is what runs instead of the write when an invariant would break; it
   is dead syntax when no invariant in scope mentions x *)
| SAssign (x : string) (e : expr) (policy : scommand)
| SIf (e : expr) (c1 c2 : scommand)
| SForeach (e : expr) (x : string) (c : scommand).

Definition decl_invs (x : string) (ds : list (string * expr)) : list invariant :=
  List.map (fun d => ConstraintInv x nil (fst d) (snd d)) ds.

Definition guards (x : string) (e : expr) (ictx : list invariant) : expr :=
  fold_right (fun i g => EBinop OAnd (inv_guard x e i) g) (EAtom (ABool true)) ictx.

Fixpoint elab (ictx : list invariant) (sc : scommand) : command :=
  match sc with
  | SSkip => CSkip
  | SSeq c1 c2 => CSeq (elab ictx c1) (elab ictx c2)
  | SLet e x c => CLet e x (elab ictx c)
  | SLetMut e x c => CLetMut e x None nil (elab ictx c)
  | SLetConstrained x row_ty ds c =>
      CLetMut (EAtom (ANil (Some row_ty))) x (Some (TList row_ty)) (decl_invs x ds)
        (elab (decl_invs x ds ++ ictx) c)
  | SAssign x e policy =>
      match filter (inv_mentions x) ictx with
      | nil => CAssign x e
      | invs => CIf (guards x e invs) (CAssign x e) (elab ictx policy)
      end
  | SIf e c1 c2 => CIf e (elab ictx c1) (elab ictx c2)
  | SForeach e x c => CForeach e x (elab ictx c)
  end.

Section WithMap.
  Notation value := (value).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Lemma guards_true : forall x e ictx (store env : locals),
      interp_expr store env (guards x e ictx) = VBool true ->
      forall i, In i ictx -> interp_expr store env (inv_guard x e i) = VBool true.
  Proof.
    unfold guards. induction ictx as [ | i0 ictx IH ]; intros store env H i H_i; [ contradiction | ].
    cbn [fold_right interp_expr interp_binop] in H. unfold apply_bool_binop in H.
    destruct (interp_expr store env (inv_guard x e i0)) eqn:E0; try discriminate.
    destruct (interp_expr store env (fold_right _ _ ictx)) eqn:E1; try discriminate.
    injection H as H. apply Bool.andb_true_iff in H as [ -> -> ].
    destruct H_i as [ <- | H_i ]; auto.
  Qed.

  Lemma decl_invs_hold_empty : forall x ds (store : locals),
      holds_all (map.put store x (VList nil)) (decl_invs x ds).
  Proof.
    intros. unfold holds_all, decl_invs. rewrite Forall_map.
    apply Forall_forall; intros. cbn [inv_holds value_at].
    rewrite map.get_put_same. constructor.
  Qed.

  Lemma Forall_inv_wf_put_fresh : forall Gstore x t ictx,
      map.get Gstore x = None ->
      Forall (inv_wf Gstore) ictx -> Forall (inv_wf (map.put Gstore x t)) ictx.
  Proof.
    intros * H_x H. eapply Forall_impl; [ | exact H ]. intros.
    eapply inv_wf_weaken; [ | eassumption ].
    apply map_incl_step_r; [ apply map_incl_refl | assumption ].
  Qed.

  Theorem elab_maintains_invs : forall sc ictx (Gstore Genv : tenv) path_cond,
      tenv_wf Gstore -> tenv_wf Genv -> Forall (inv_wf Gstore) ictx ->
      well_typed Gstore Genv (elab ictx sc) ->
      maintains_invs Gstore Genv ictx path_cond (elab ictx sc).
  Proof.
    induction sc; cbn [elab]; intros * H_Gs H_Ge H_ictx H_wt.
    (* SSkip *)
    1: constructor.
    (* SSeq *)
    1: invert_well_typed; constructor; auto.
    (* SLet *)
    1:{ invert_well_typed. econstructor; [ eassumption | ].
        apply IHsc; auto.
        apply tenv_wf_step; [ assumption | eapply type_of__type_wf; [ | | eassumption ]; assumption ]. }
    (* SLetMut *)
    1:{ invert_well_typed. econstructor; eauto.
        1:{ apply IHsc; auto using Forall_inv_wf_put_fresh.
            apply tenv_wf_step; [ assumption | eapply type_of__type_wf; [ | | eassumption ]; assumption ]. }
        intros. constructor. }
    (* SLetConstrained *)
    1:{ invert_well_typed. econstructor; eauto.
        1:{ apply IHsc; auto.
            1: apply tenv_wf_step; [ assumption | eapply type_of__type_wf; [ | | eassumption ]; assumption ].
            apply Forall_app; auto using Forall_inv_wf_put_fresh. }
        intros. apply decl_invs_hold_empty. }
    (* SAssign: an invariant the write can affect is decided by its guard,
       and any other is unaffected by the write *)
    1:{ destruct (filter (inv_mentions x) ictx) as [ | i0 invs ] eqn:E_f.
        1:{ invert_well_typed. econstructor; eauto.
            intros store env _ H_h _ _. unfold holds_all in *.
            rewrite Forall_forall in *. intros i H_i.
            apply inv_holds_put_unmentioned; auto.
            destruct (inv_mentions x i) eqn:E; [ | reflexivity ].
            assert (H_in : In i (filter (inv_mentions x) ictx)) by (apply filter_In; auto).
            rewrite E_f in H_in. contradiction. }
        invert_well_typed.
        lazymatch goal with H : well_typed _ _ (CAssign _ _) |- _ => inversion H; subst end.
        lazymatch goal with
        | H_x : map.get Gstore x = Some ?t, H_e : type_of Gstore Genv e ?t |- _ =>
            rename H_x into H_get; rename H_e into H_te
        end.
        apply MICIf; [ assumption | | apply IHsc; assumption ].
        econstructor; [ exact H_get | exact H_te | ].
        intros store env [ _ H_g ] H_h H_store H_env. unfold holds_all in *.
        rewrite Forall_forall in *. intros i H_i.
        destruct (inv_mentions x i) eqn:E.
        1:{ assert (H_in : In i (filter (inv_mentions x) ictx)) by (apply filter_In; auto).
            rewrite E_f in H_in.
            apply (proj1 (inv_guard_iff Gstore Genv x _ e i store env H_Gs H_Ge (H_ictx i H_i)
                            H_get H_te H_store H_env)).
            eapply guards_true; eassumption. }
        1: apply inv_holds_put_unmentioned; auto. }
    (* SIf *)
    1: invert_well_typed; constructor; auto.
    (* SForeach *)
    1:{ invert_well_typed. econstructor; [ eassumption | ].
        apply IHsc; auto.
        apply tenv_wf_step; [ assumption | ].
        lazymatch goal with H : type_of _ _ _ (TList _) |- _ =>
          apply type_of__type_wf in H; [ inversion H; assumption | assumption | assumption ] end. }
  Qed.

  Corollary elab_prog_maintains_invs : forall sc (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv ->
      well_typed Gstore Genv (elab nil sc) ->
      maintains_invs Gstore Genv nil (fun _ _ => True) (elab nil sc).
  Proof.
    intros. apply elab_maintains_invs; auto.
  Qed.
End WithMap.
