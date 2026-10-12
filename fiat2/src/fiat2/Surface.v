Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.Substitute fiat2.TransfSound fiat2.Constraint.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List.
Import ListNotations.

(* A surface language with declared constraints, and its elaboration into the
   core.

   The core language is untouched: a constraint is not a command, and a checked
   assignment is not a command.  A declaration introduces a mutable variable
   born empty together with the constraints that must hold of it, and
   elaboration inserts the check at every assignment to a constrained variable,
   turning

     x := e  else  policy

   into

     if <every declared constraint of x, read of e> then x := e else policy.

   So the policy a programmer writes at a write site is simply the else branch:
   it is an ordinary command, checked by the ordinary rules, and if it assigns
   to a constrained variable it is elaborated too and gets its own check.  The
   recursion terminates because elaboration is structural.

   There is no per-declaration default policy.  A command written at the
   declaration and inserted at every write site would capture whatever
   immutable variables those sites bind, and could break constraints declared
   between the declaration and the write; neither is checkable where it is
   written.  Recovering a default as surface sugar -- expanded before
   elaboration, where the variables are in scope -- costs nothing and avoids
   both. *)

Inductive scommand : Type :=
| SSkip
| SSeq (c1 c2 : scommand)
| SLet (e : expr) (x : string) (c : scommand)
| SLetMut (e : expr) (x : string) (c : scommand)
(* x is born empty, holds rows of row_ty, and every constraint in ks must hold
   of it for as long as it is in scope *)
| SLetConstrained (x : string) (row_ty : type) (ks : list constr) (c : scommand)
(* policy is what runs instead of the write when a constraint would break; it
   is dead syntax when x carries no constraint *)
| SAssign (x : string) (e : expr) (policy : scommand)
| SIf (e : expr) (c1 c2 : scommand)
| SForeach (e : expr) (x : string) (c : scommand).

(* Which constraints are in force on which variable.  Entries are added by a
   declaration and removed when the variable is shadowed, so a write is checked
   against exactly the constraints that are standing where it occurs. *)
Definition cenv : Type := list (string * list constr).

Fixpoint cenv_lookup (x : string) (ce : cenv) : option (list constr) :=
  match ce with
  | nil => None
  | (y, ks) :: ce => if String.eqb y x then Some ks else cenv_lookup x ce
  end.

Definition cenv_rm (x : string) (ce : cenv) : cenv :=
  filter (fun e => negb (String.eqb (fst e) x)) ce.

Lemma cenv_lookup_rm_diff : forall x y ce,
    x <> y -> cenv_lookup x (cenv_rm y ce) = cenv_lookup x ce.
Proof.
  induction ce as [| [z ks] ce IH]; auto; intros H_ne.
  unfold cenv_rm in *; simpl.
  destruct (String.eqb z y) eqn:E_y; simpl.
  - destruct (String.eqb z x) eqn:E_x.
    + rewrite String.eqb_eq in E_y, E_x. congruence.
    + apply IH; auto.
  - destruct (String.eqb z x) eqn:E_x.
    + reflexivity.
    + apply IH; auto.
Qed.

Fixpoint elab (ce : cenv) (free_vars : list string) (sc : scommand) : command :=
  match sc with
  | SSkip => CSkip
  | SSeq c1 c2 => CSeq (elab ce free_vars c1) (elab ce free_vars c2)
  | SLet e x c => CLet e x (elab ce (x :: free_vars) c)
  | SLetMut e x c => CLetMut e x (elab (cenv_rm x ce) free_vars c)
  | SLetConstrained x row_ty ks c =>
      CLetMut (EAtom (ANil (Some row_ty))) x
        (elab ((x, ks) :: cenv_rm x ce) free_vars c)
  | SAssign x e policy =>
      match cenv_lookup x ce with
      | None => CAssign x e
      | Some ks =>
          CIf (conj_guards ks free_vars e) (CAssign x e) (elab ce free_vars policy)
      end
  | SIf e c1 c2 => CIf e (elab ce free_vars c1) (elab ce free_vars c2)
  | SForeach e x c => CForeach e x (elab ce (x :: free_vars) c)
  end.

Section WithWord.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  (* A predicate that holds of everything constrains no write, so any
     well-typed command is well formed for it.  This is what a variable that
     has been shadowed falls back on. *)
  Lemma trivial_pred__parameterized_wf :
    forall c (Gstore Genv : tenv) P (A : locals -> locals -> Prop),
      (forall x v, P x v) ->
      well_typed Gstore Genv c ->
      parameterized_wf Gstore Genv P A c.
  Proof.
    induction c; intros * H_P H_wt; invert_well_typed; econstructor; eauto.
    (* CLetMut: the body's predicate is only weaker *)
    1: apply IHc; auto; unfold rm_from_pred; auto.
  Qed.

  Lemma rm_from_pred_trivial : forall tbl Pv x (v : value),
      rm_from_pred (value_wf_with_globals Pv (tbl :: nil)) tbl x v.
  Proof.
    unfold rm_from_pred, value_wf_with_globals; intros.
    destruct (String.eqb x tbl) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
    1: left; reflexivity.
    1: right; constructor; [ left; auto | constructor ].
  Qed.

  (* Elaboration keeps every constraint declared on tbl standing, at every
     point of the program.  The theorem is about a tbl already in the store's
     type environment, which is where the body of a declaration starts; the
     declaration itself supplies the base case, since the variable is born
     empty (constrs_declared). *)
  Theorem elab_constr_wf :
    forall sc ce free_vars (Gstore Genv : tenv) tbl row_ty ks
           (A : locals -> locals -> Prop),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      incl (get_free_vars Genv) free_vars ->
      map.get Gstore tbl = Some (TList row_ty) ->
      Forall (constr_wf row_ty) ks ->
      cenv_lookup tbl ce = Some ks ->
      well_typed Gstore Genv (elab ce free_vars sc) ->
      parameterized_wf Gstore Genv
        (value_wf_with_globals (constrs_hold ks) (tbl :: nil)) A
        (elab ce free_vars sc).
  Proof.
    (* the inversion of the elaborated command is done case by case, since at
       an assignment the elaboration is a match on whether the variable carries
       a constraint *)
    induction sc; cbn [elab]; intros * ? ? ? H_fv H_tbl H_ks H_ce H_wt.
    (* SSkip *)
    1: constructor.
    (* SSeq *)
    1:{ invert_well_typed. econstructor; eauto. }
    (* SLet *)
    1:{ invert_well_typed. econstructor; eauto.
        eapply IHsc; eauto with fiat2_hints.
        eauto using incl_tran, incl_cons_step, get_free_vars_put. }
    (* SLetMut: a shadowed tbl falls back on a predicate that holds of
       everything, and otherwise the invariant is untouched *)
    1:{ invert_well_typed. econstructor; eauto.
        destruct (String.eqb x tbl) eqn:E.
        1:{ rewrite eqb_eq in E; subst.
            apply trivial_pred__parameterized_wf; auto using rm_from_pred_trivial. }
        1:{ pose proof E as E'; rewrite eqb_neq in E'.
            eapply iff2_parameterized_wf.
            1: apply iff2_sym, rm_not_in_globals; cbn; intuition congruence.
            eapply IHsc; eauto with fiat2_hints.
            1: rewrite_map_get_put_goal; eauto.
            1: rewrite cenv_lookup_rm_diff; auto. } }
    (* SLetConstrained: the same, plus the new variable's own entry *)
    1:{ invert_well_typed. econstructor; eauto.
        destruct (String.eqb x tbl) eqn:E.
        1:{ rewrite eqb_eq in E; subst.
            apply trivial_pred__parameterized_wf; auto using rm_from_pred_trivial. }
        1:{ pose proof E as E'; rewrite eqb_neq in E'.
            eapply iff2_parameterized_wf.
            1: apply iff2_sym, rm_not_in_globals; cbn; intuition congruence.
            eapply IHsc; eauto with fiat2_hints.
            1: rewrite_map_get_put_goal; eauto.
            1: cbn [cenv_lookup]; rewrite E, cenv_lookup_rm_diff; auto. } }
    (* SAssign *)
    1:{ destruct (cenv_lookup x ce) eqn:E_look; invert_well_typed.
        2:{ (* x carries no constraint, so it is not tbl, and the write cannot
               break tbl's constraints *)
            econstructor; eauto.
            intros. unfold value_wf_with_globals.
            constructor; [ left | constructor ].
            intro contra; subst; congruence. }
        (* the typing of the inner assignment, before the two cases split *)
        lazymatch goal with
          H: well_typed _ _ (CAssign _ _) |- _ => inversion H; subst
        end.
        destruct (String.eqb x tbl) eqn:E.
        1:{ (* the write is checked against exactly tbl's constraints *)
            rewrite eqb_eq in E; subst.
            rewrite H_ce in E_look; do_injection.
            eapply checked_assign_wf with (row_ty := row_ty); eauto.
            lazymatch goal with
              H: type_of Gstore Genv e ?t |- _ =>
                replace (TList row_ty) with t by congruence
            end.
            auto. }
        1:{ (* a checked write to another variable leaves tbl alone *)
            pose proof E as E'; rewrite eqb_neq in E'.
            econstructor.
            1: eauto.
            1:{ econstructor; eauto.
                intros. unfold value_wf_with_globals.
                constructor; [ left; auto | constructor ]. }
            1: eapply IHsc; eauto. } }
    (* SIf *)
    1:{ invert_well_typed. econstructor; eauto. }
    (* SForeach *)
    1:{ invert_well_typed. econstructor; eauto.
        eapply IHsc; eauto with fiat2_hints.
        eauto using incl_tran, incl_cons_step, get_free_vars_put. }
  Qed.

  (* The whole story for a declared variable: the declaration establishes the
     invariant because the variable is born empty, and elaboration carries it
     over every write. *)
  Corollary elab_prog_constr_wf :
    forall sc free_vars (Gstore Genv : tenv) (store env : locals) tbl row_ty ks,
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      incl (get_free_vars Genv) free_vars ->
      map.get Gstore tbl = Some (TList row_ty) ->
      Forall (constr_wf row_ty) ks ->
      well_typed Gstore Genv (elab ((tbl, ks) :: nil) free_vars sc) ->
      locals_wf Gstore (map.put store tbl (VList nil)) -> locals_wf Genv env ->
      holds_for_all_entries (value_wf_with_globals (constrs_hold ks) (tbl :: nil))
        (interp_command (map.put store tbl (VList nil)) env
           (elab ((tbl, ks) :: nil) free_vars sc)).
  Proof.
    intros.
    eapply parameterized_wf__preserve_P
      with (Gstore := Gstore) (Genv := Genv) (A := fun _ _ => True).
    1,2: auto.
    1:{ eapply elab_constr_wf with (row_ty := row_ty); eauto.
        cbn [cenv_lookup]; rewrite String.eqb_refl; reflexivity. }
    1: exact I.
    1,2: auto.
    1: apply constrs_declared.
  Qed.
End WithWord.
