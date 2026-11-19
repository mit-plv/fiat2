Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.Invariant.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
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

  Ltac destruct_tc :=
    repeat match goal with
      | H : match ?x with _ => _ end = Success _ |- _ =>
          let E := fresh "E" in destruct x eqn:E; try discriminate H
      | H : (_, _) = (_, _) |- _ => injection H as <- <-
      | H : Success _ = Success _ |- _ => injection H; intros; subst
      end.

  Theorem elab_typecheck_maintains_invs : forall sc ictx (Gstore Genv : tenv) path_cond c',
      tenv_wf Gstore -> tenv_wf Genv -> Forall (inv_wf Gstore) ictx ->
      typecheck Gstore Genv (elab ictx sc) = Success c' ->
      maintains_invs Gstore Genv ictx path_cond c'.
  Proof.
    induction sc; intros * H_Gs H_Ge H_ictx H_tc.
    (* SSkip *)
    1:{ cbn in H_tc. injection H_tc as <-. constructor. }
    (* SSeq *)
    1:{ cbn [elab typecheck] in H_tc. destruct_tc.
        constructor; eauto. }
    (* SLet *)
    1:{ cbn [elab typecheck] in H_tc. destruct_tc.
        lazymatch goal with
        | E : synthesize_expr _ _ e = Success (?t, ?e') |- _ =>
            pose proof (proj1 (typechecker_out_sound e Gstore Genv t e' H_Gs H_Ge) E) as H_e
        end.
        econstructor; [ exact H_e | ].
        eapply IHsc; [ exact H_Gs | | exact H_ictx | eassumption ].
        apply tenv_wf_step; [ exact H_Ge | exact (type_of__type_wf _ _ _ _ H_Gs H_Ge H_e) ]. }
    (* SLetMut *)
    1:{ cbn [elab typecheck typecheck_invs] in H_tc. destruct_tc.
        lazymatch goal with
        | E : synthesize_expr _ _ e = Success (?t, ?e') |- _ =>
            pose proof (proj1 (typechecker_out_sound e Gstore Genv t e' H_Gs H_Ge) E) as H_e
        end.
        pose proof (type_of__type_wf _ _ _ _ H_Gs H_Ge H_e) as H_t.
        eapply MICLetMut; [ exact H_e | reflexivity | | apply Forall_nil | assumption | ].
        1:{ eapply IHsc; [ | exact H_Ge | | eassumption ].
            1: apply tenv_wf_step; assumption.
            1: apply Forall_inv_wf_put_fresh; assumption. }
        intros. constructor. }
    (* SLetConstrained *)
    1:{ cbn [elab typecheck] in H_tc. destruct_tc.
        lazymatch goal with
        | E : type_wf_comp _ = true |- _ => apply type_wf_comp_sound in E as H_t
        end.
        lazymatch goal with
        | E : analyze_expr _ _ _ (EAtom ?a) = Success ?e' |- _ =>
            pose proof (proj2 (typechecker_out_sound (EAtom a) Gstore Genv _ e' H_Gs H_Ge) E H_t) as H_e;
            pose proof (fun store env => proj2 (typechecker_preserve_sem (EAtom a) Gstore Genv store env _ e') E)
              as E_e
        end.
        assert (H_Gs' : tenv_wf (map.put Gstore x (TList row_ty))) by (apply tenv_wf_step; assumption).
        eapply MICLetMut; [ exact H_e | reflexivity | | | assumption | ].
        1:{ eapply IHsc; [ exact H_Gs' | exact H_Ge | | eassumption ].
            apply Forall_app; split.
            1: eapply typecheck_invs_sound; [ exact H_Gs' | eassumption ].
            1: apply Forall_inv_wf_put_fresh; assumption. }
        1: eapply typecheck_invs_sound; [ exact H_Gs' | eassumption ].
        intros store env _ _ _ _. rewrite E_e. apply decl_invs_hold_empty. }
    (* SAssign: an invariant the write can affect is decided by its guard,
       and any other is unaffected by the write *)
    1:{ cbn [elab] in H_tc.
        destruct (filter (inv_mentions x) ictx) as [ | i0 invs ] eqn:E_f.
        1:{ cbn [typecheck] in H_tc. destruct_tc.
            lazymatch goal with
            | E_x : map.get Gstore x = Some ?t, E : analyze_expr _ _ _ e = Success ?e' |- _ =>
                pose proof (H_Gs _ _ E_x) as H_t;
                eapply MICAssign; [ exact E_x | exact (proj2 (typechecker_out_sound e Gstore Genv _ e' H_Gs H_Ge) E H_t) | ];
                intros store env _ H_h _ _;
                rewrite (proj2 (typechecker_preserve_sem e Gstore Genv store env _ e') E)
            end.
            unfold holds_all in *. rewrite Forall_forall in *. intros i H_i.
            apply inv_holds_put_unmentioned; auto.
            destruct (inv_mentions x i) eqn:E_m; [ | reflexivity ].
            assert (H_in : In i (filter (inv_mentions x) ictx)) by (apply filter_In; auto).
            rewrite E_f in H_in. contradiction. }
        cbn [typecheck] in H_tc. destruct_tc.
        lazymatch goal with
        | E_g : analyze_expr _ _ TBool (guards _ _ _) = Success ?g',
          E_x : map.get Gstore x = Some ?t, E : analyze_expr _ _ _ e = Success ?e' |- _ =>
            pose proof (H_Gs _ _ E_x) as H_t;
            pose proof (proj2 (typechecker_sound e Gstore Genv _ e' H_Gs H_Ge) E H_t) as H_te;
            apply MICIf;
            [ exact (proj2 (typechecker_out_sound _ Gstore Genv TBool g' H_Gs H_Ge) E_g ltac:(constructor))
            | eapply MICAssign; [ exact E_x | exact (proj2 (typechecker_out_sound e Gstore Genv _ e' H_Gs H_Ge) E H_t) | ]
            | eapply IHsc; eassumption ];
            intros store env [ _ H_g ] H_h H_store H_env;
            rewrite (proj2 (typechecker_preserve_sem e Gstore Genv store env _ e') E);
            rewrite (proj2 (typechecker_preserve_sem _ Gstore Genv store env TBool g') E_g) in H_g;
            unfold holds_all in *; rewrite Forall_forall in *; intros i H_i;
            destruct (inv_mentions x i) eqn:E_m;
            [ assert (H_in : In i (filter (inv_mentions x) ictx)) by (apply filter_In; auto);
              rewrite E_f in H_in;
              apply (proj1 (inv_guard_iff Gstore Genv x _ e i store env H_Gs H_Ge (H_ictx i H_i)
                              E_x H_te H_store H_env));
              eapply guards_true; eassumption
            | apply inv_holds_put_unmentioned; auto ]
        end. }
    (* SIf *)
    1:{ cbn [elab typecheck] in H_tc. destruct_tc.
        lazymatch goal with
        | E : analyze_expr _ _ TBool e = Success ?e' |- _ =>
            apply MICIf; [ exact (proj2 (typechecker_out_sound e Gstore Genv TBool e' H_Gs H_Ge) E ltac:(constructor))
                         | eapply IHsc1; eassumption | eapply IHsc2; eassumption ]
        end. }
    (* SForeach *)
    1:{ cbn [elab typecheck] in H_tc. destruct_tc.
        lazymatch goal with
        | E : synthesize_expr _ _ e = Success (TList ?t, ?e') |- _ =>
            pose proof (proj1 (typechecker_out_sound e Gstore Genv _ e' H_Gs H_Ge) E) as H_e
        end.
        pose proof (type_of__type_wf _ _ _ _ H_Gs H_Ge H_e) as H_t. inversion H_t; subst.
        econstructor; [ exact H_e | ].
        eapply IHsc; [ exact H_Gs | | exact H_ictx | eassumption ].
        apply tenv_wf_step; assumption. }
  Qed.

  Corollary elab_prog_maintains_invs : forall sc (Gstore Genv : tenv) c',
      tenv_wf Gstore -> tenv_wf Genv ->
      typecheck Gstore Genv (elab nil sc) = Success c' ->
      maintains_invs Gstore Genv nil (fun _ _ => True) c'.
  Proof.
    intros. eapply elab_typecheck_maintains_invs; eauto.
  Qed.
End WithMap.
