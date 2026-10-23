Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.TransfSound.
Require Import coqutil.Map.Interface.
From Stdlib Require Import List String ZArith.
Import ListNotations.

(* A flag is a two-valued key.

   The index rules look for a filter whose predicate is an equality against an
   attribute: eq_filter_to_lookup_head matches
   [EBinop OEq (EAccess (EVar x) attr) e'].  A predicate that is simply a
   boolean field -- "keep the active rows" -- asks the same question without
   writing the equality, so none of those rules fire and the filter is left as
   a scan, even though a dictionary keyed on the flag answers it.

   This rewrite puts such a predicate into the shape the index rules read.  It
   is a normalisation, not an optimisation: it changes no behaviour and asks
   for no index.  What it buys is that the dictionary index already in the
   development becomes reachable from a shape the source commonly takes.

   Why it needs no type information: the predicate sits in the condition of an
   EIf, so a well-typed program already has it at TBool, and OEq is typed at
   every type (TyOEq).  Rewriting the condition of the EIf, rather than one
   particular filter form, is also what makes the rule independent of the
   collection phase -- the list, bag and set filter forms differ only in their
   branches, which this does not touch. *)

(* A predicate in a boolean position.  Only a field of a variable is rewritten:
   a bare boolean variable is not a key of anything, so normalising it would
   bring no rule within reach. *)
Definition flag_to_eq (p : expr) : expr :=
  match p with
  | EAccess (EVar x) attr =>
      EBinop OEq (EAccess (EVar x) attr) (EAtom (ABool true))
  | EUnop ONot (EAccess (EVar x) attr) =>
      EBinop OEq (EAccess (EVar x) attr) (EAtom (ABool false))
  | _ => p
  end.

Definition flag_filter_to_eq_head (e : expr) : expr :=
  match e with
  | EIf p e2 e3 => EIf (flag_to_eq p) e2 e3
  | _ => e
  end.

Section WithWord.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Notation value := (value).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  (* comparing a boolean against each literal: the two facts the rewrite
     turns on *)
  Lemma value_eqb_bool_true : forall b,
      value_eqb (VBool b) (VBool true) = b.
  Proof. destruct b; reflexivity. Qed.

  Lemma value_eqb_bool_false : forall b,
      value_eqb (VBool b) (VBool false) = negb b.
  Proof. destruct b; reflexivity. Qed.

  Lemma flag_to_eq_preserve_ty : forall (Gstore Genv : tenv) p,
      type_of Gstore Genv p TBool ->
      type_of Gstore Genv (flag_to_eq p) TBool.
  Proof.
    intros * H. destruct p; cbn [flag_to_eq]; try assumption.
    - (* a negated field access; any other unop is left alone *)
      destruct o; cbn [flag_to_eq]; try assumption.
      destruct p; cbn [flag_to_eq]; try assumption.
      destruct p; cbn [flag_to_eq]; try assumption.
      repeat invert_type_of_clear; repeat invert_type_of_op_clear.
      repeat econstructor; eauto.
    - (* a field access of a variable *)
      destruct p; cbn [flag_to_eq]; try assumption.
      repeat invert_type_of_clear.
      repeat econstructor; eauto.
  Qed.

  Lemma flag_to_eq_preserve_sem : forall (Gstore Genv : tenv) (store env : locals) p,
      tenv_wf Gstore -> tenv_wf Genv ->
      type_of Gstore Genv p TBool ->
      locals_wf Gstore store -> locals_wf Genv env ->
      interp_expr store env (flag_to_eq p) = interp_expr store env p.
  Proof.
    intros * H_Gs H_Ge H_ty H_st H_en.
    destruct p; cbn [flag_to_eq]; try reflexivity.
    - (* not(x.attr) = (x.attr == false) *)
      destruct o; cbn [flag_to_eq]; try reflexivity.
      destruct p; cbn [flag_to_eq]; try reflexivity.
      destruct p; cbn [flag_to_eq]; try reflexivity.
      (* the field's value is a boolean, which is what makes the comparison
         against the literal the negation *)
      invert_type_of_clear; invert_type_of_op_clear.
      apply_type_sound (EAccess (EVar x) s).
      invert_type_of_value_clear.
      cbn [interp_expr interp_binop interp_unop interp_atom].
      (* type_sound gives the field's value as VBool b; put it back so that
         both sides are expressed in b *)
      lazymatch goal with H: VBool _ = _ |- _ => rewrite <- H end.
      cbn [interp_unop]. rewrite value_eqb_bool_false; reflexivity.
    - (* x.attr = (x.attr == true) *)
      destruct p; cbn [flag_to_eq]; try reflexivity.
      apply_type_sound (EAccess (EVar x) s).
      invert_type_of_value_clear.
      cbn [interp_expr interp_binop interp_atom].
      lazymatch goal with H: VBool _ = _ |- _ => rewrite <- H end.
      rewrite value_eqb_bool_true; reflexivity.
  Qed.

  Lemma flag_filter_to_eq_head_preserve_ty : forall (Gstore : tenv),
      preserve_ty Gstore flag_filter_to_eq_head.
  Proof.
    unfold preserve_ty; intros * H_Gs H_Ge H_ty.
    destruct e; cbn [flag_filter_to_eq_head]; try assumption.
    invert_type_of_clear.
    econstructor; eauto using flag_to_eq_preserve_ty.
  Qed.

  Lemma flag_filter_to_eq_head_preserve_sem :
    forall (Gstore : tenv) (store : locals),
      preserve_sem Gstore store flag_filter_to_eq_head.
  Proof.
    unfold preserve_sem; intros * H_Gs H_Ge H_ty H_st H_en.
    destruct e; cbn [flag_filter_to_eq_head]; try reflexivity.
    invert_type_of_clear.
    cbn [interp_expr].
    (* name the environments: erewrite otherwise unifies the store's with the
       environment's and leaves two unprovable side conditions *)
    erewrite flag_to_eq_preserve_sem with (Gstore := Gstore) (Genv := Genv); eauto.
  Qed.

  Lemma flag_filter_to_eq_head_sound :
    expr_transf_sound (locals:=locals) flag_filter_to_eq_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply flag_filter_to_eq_head_preserve_ty; auto.
    eapply flag_filter_to_eq_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithWord.

#[export] Hint Resolve flag_filter_to_eq_head_sound : transf_hints.
