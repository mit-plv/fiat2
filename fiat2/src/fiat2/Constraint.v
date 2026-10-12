Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.Substitute fiat2.TransfSound.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith Lia List.
Import ListNotations.

(* Declared constraints.

   A constraint on a list-typed mutable variable is an arbitrary boolean
   expression over a variable bound to each row, and it holds of the variable
   when every row satisfies it.  The body may read the table itself, through a
   hole that stands for it, which is what lets a row predicate say something
   about the rest of the table -- a primary key, for instance.

   Nothing about this form is special-cased in the language.  Two facts make a
   constraint usable:

     - it holds of the empty list, whatever the body is, because the quantifier
       ranges over no rows.  That is what lets a constraint be declared along
       with the table it constrains and never fail at the declaration, so the
       declaration needs no failure answer of its own.

     - substituting the value a write would store for the hole turns the
       constraint into a guard, and a write that happens under that guard
       leaves the constraint standing.  checked_assign_wf turns this into the
       per-write obligation of parameterized_wf, once per constraint rather
       than once per program.

   The restriction here is that the body reads no mutable variable (it is typed
   under the empty store).  A constraint reading another table -- a foreign key
   -- is expressible as a guard just as easily, but the invariant it would let
   an index assume is relational, and parameterized_wf's predicate speaks about
   one variable at a time. *)

Section WithWord.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  (* The hole standing for the constrained table, and the accumulator of the
     quantifier.  Both are bound by the constraint's own translation, so a body
     that mentions either simply does not satisfy constr_wf below. *)
  Definition c_tbl : string := "_tbl".
  Definition c_all : string := "_all".

  Record constr := mk_constr { c_row : string; c_body : expr }.

  (* Every row of the table satisfies the body. *)
  Definition constr_expr (k : constr) : expr :=
    EFold (EVar c_tbl) (EAtom (ABool true)) (c_row k) c_all
      (EIf (c_body k) (EVar c_all) (EAtom (ABool false))).

  Definition c_env (row_ty : type) (k : constr) : tenv :=
    map.put (map.put (map.put map.empty c_tbl (TList row_ty)) (c_row k) row_ty) c_all TBool.

  Definition constr_wf (row_ty : type) (k : constr) : Prop :=
    type_of (map.empty : tenv) (c_env row_ty k) (c_body k) TBool.

  (* What the constraint says about the value the variable holds.  It mentions
     no store, which is what lets it be the predicate parameterized_wf carries
     and an index assumes. *)
  Definition constr_holds (k : constr) (v : value) : Prop :=
    interp_expr (map.empty : locals) (map.put map.empty c_tbl v) (constr_expr k) = VBool true.

  (* The base case of the invariant, for free: the quantifier ranges over no
     rows, so the body is never consulted. *)
  Lemma constr_holds_nil : forall k, constr_holds k (VList nil).
  Proof.
    unfold constr_holds, constr_expr; intros.
    cbn [interp_expr]. unfold get_local.
    rewrite map.get_put_same. reflexivity.
  Qed.

  Lemma c_env_incl : forall row_ty k (Genv : tenv),
      map.get Genv c_tbl = Some (TList row_ty) ->
      map_incl (c_env row_ty k)
        (map.put (map.put Genv (c_row k) row_ty) c_all TBool).
  Proof.
    unfold c_env, map_incl; intros * H_tbl * H_get.
    destruct (String.eqb c_all k0) eqn:E_all;
      rewrite ?eqb_eq, ?eqb_neq in *; subst.
    1: rewrite map.get_put_same in *; auto.
    rewrite map.get_put_diff in * by congruence.
    destruct (String.eqb (c_row k) k0) eqn:E_row;
      rewrite ?eqb_eq, ?eqb_neq in *; subst.
    1: rewrite map.get_put_same in *; auto.
    rewrite map.get_put_diff in * by congruence.
    destruct (String.eqb c_tbl k0) eqn:E_tbl;
      rewrite ?eqb_eq, ?eqb_neq in *; subst.
    1: rewrite map.get_put_same in *; congruence.
    rewrite map.get_put_diff, map.get_empty in * by congruence. congruence.
  Qed.

  Lemma constr_expr_ty : forall row_ty k (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      constr_wf row_ty k ->
      map.get Genv c_tbl = Some (TList row_ty) ->
      type_of Gstore Genv (constr_expr k) TBool.
  Proof.
    unfold constr_wf, constr_expr; intros.
    econstructor.
    1: constructor; eauto.
    1: repeat constructor.
    econstructor.
    2: constructor; rewrite_map_get_put_goal; reflexivity.
    2: repeat constructor.
    eapply type_of_strengthen; eauto using map_incl_empty, c_env_incl.
  Qed.

  (* The guard for a write: the constraint, read of the value the write would
     store rather than of the variable. *)
  Definition constr_guard (k : constr) (free_vars : list string) (u : expr) : expr :=
    substitute ((c_tbl, u) :: nil) free_vars (constr_expr k).

  Lemma constr_guard_sub_wf : forall row_ty u (Gstore Genv : tenv),
      type_of Gstore Genv u (TList row_ty) ->
      sub_wf (map.put map.empty c_tbl (TList row_ty)) Gstore Genv ((c_tbl, u) :: nil).
  Proof.
    unfold sub_wf; cbn [sub_lookup fst snd]; intros.
    destruct (String.eqb c_tbl x) eqn:E;
      rewrite ?eqb_eq, ?eqb_neq in *; subst.
    1:{ rewrite map.get_put_same in *. do_injection.
        rewrite String.eqb_refl. auto. }
    1:{ rewrite map.get_put_diff, map.get_empty in * by congruence. congruence. }
  Qed.

  Lemma constr_guard_ty : forall row_ty k free_vars u (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      constr_wf row_ty k ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      type_of Gstore Genv (constr_guard k free_vars u) TBool.
  Proof.
    unfold constr_guard; intros.
    eapply substitute_preserve_ty with (Genv0 := map.put map.empty c_tbl (TList row_ty));
      eauto using constr_guard_sub_wf with fiat2_hints.
    eapply constr_expr_ty; eauto with fiat2_hints.
    rewrite_map_get_put_goal; reflexivity.
  Qed.

  (* The one fact that makes a constraint usable by an index: a write that
     happens under the guard stores a value the constraint holds of. *)
  Lemma constr_guard_sound : forall row_ty k free_vars u (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      constr_wf row_ty k ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      interp_expr store env (constr_guard k free_vars u) = VBool true ->
      constr_holds k (interp_expr store env u).
  Proof.
    unfold constr_guard, constr_holds; intros * ? ? ? H_k H_u ? ? ? H_guard.
    assert (H_hole : map.get (map.put (map.empty : tenv) c_tbl (TList row_ty)) c_tbl
                     = Some (TList row_ty)) by (rewrite_map_get_put_goal; reflexivity).
    assert (H_env0 : tenv_wf (map.put (map.empty : tenv) c_tbl (TList row_ty)))
      by (eauto with fiat2_hints).
    (* the substitution puts the candidate value in the hole *)
    erewrite substitute_preserve_sem with
      (Gstore := Gstore) (Genv := Genv) (Genv0 := map.put map.empty c_tbl (TList row_ty))
      in H_guard;
      eauto using constr_guard_sub_wf, constr_expr_ty.
    cbn [make_sub_env fst snd] in H_guard.
    (* and the constraint reads no mutable variable, so the store it is read
       in does not matter *)
    assert (H_eq : interp_expr store (map.put map.empty c_tbl (interp_expr store env u))
                     (constr_expr k)
                   = interp_expr (map.empty : locals)
                       (map.put map.empty c_tbl (interp_expr store env u)) (constr_expr k)).
    { eapply interp_expr_strengthen with
        (Gstore := map.empty : tenv)
        (Genv := map.put map.empty c_tbl (TList row_ty))
        (t := TBool).
      1: apply tenv_wf_empty.
      1: exact H_env0.
      1: eapply constr_expr_ty; eauto using tenv_wf_empty.
      1: apply locals_wf_empty.
      1:{ eapply locals_wf_step; eauto using locals_wf_empty.
          eapply type_sound; eauto. }
      1: apply map_incl_empty.
      1: apply map_incl_refl. }
    rewrite <- H_eq. exact H_guard.
  Qed.

  (* A declaration carries a list of constraints, and the guard for a write is
     their conjunction.  Nothing here is specific to one constraint: a write
     must leave every constraint declared on the variable standing. *)
  Definition constrs_hold (ks : list constr) (v : value) : Prop :=
    Forall (fun k => constr_holds k v) ks.

  Definition conj_guards (ks : list constr) (free_vars : list string) (u : expr) : expr :=
    fold_right (fun k acc => EBinop OAnd (constr_guard k free_vars u) acc)
      (EAtom (ABool true)) ks.

  Lemma constrs_hold_nil : forall ks, constrs_hold ks (VList nil).
  Proof.
    unfold constrs_hold; intros. rewrite Forall_forall; intros.
    apply constr_holds_nil.
  Qed.

  Lemma conj_guards_ty : forall row_ty ks free_vars u (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      Forall (constr_wf row_ty) ks ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      type_of Gstore Genv (conj_guards ks free_vars u) TBool.
  Proof.
    unfold conj_guards; induction ks; cbn [fold_right]; intros.
    1: repeat constructor.
    invert_Forall. econstructor; eauto using constr_guard_ty.
    constructor.
  Qed.

  Lemma interp_and_true : forall (store env : locals) e1 e2,
      interp_expr store env (EBinop OAnd e1 e2) = VBool true ->
      interp_expr store env e1 = VBool true /\ interp_expr store env e2 = VBool true.
  Proof.
    cbn [interp_expr interp_binop]; unfold apply_bool_binop; intros.
    repeat destruct_match_hyp; try discriminate.
    lazymatch goal with H: VBool _ = VBool _ |- _ => inversion H end.
    lazymatch goal with
      H: andb _ _ = true |- _ => apply Bool.andb_true_iff in H as [? ?]
    end.
    subst; auto.
  Qed.

  Lemma conj_guards_sound :
    forall row_ty ks free_vars u (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      Forall (constr_wf row_ty) ks ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      interp_expr store env (conj_guards ks free_vars u) = VBool true ->
      constrs_hold ks (interp_expr store env u).
  Proof.
    unfold conj_guards, constrs_hold; induction ks; cbn [fold_right]; intros.
    1: constructor.
    invert_Forall.
    lazymatch goal with
      H: interp_expr _ _ (EBinop OAnd _ _) = _ |- _ =>
        apply interp_and_true in H as [? ?]
    end.
    constructor.
    1: eapply constr_guard_sound with (row_ty := row_ty) (Gstore := Gstore) (Genv := Genv); eauto.
    1: eapply IHks with (Gstore := Gstore) (Genv := Genv); eauto.
  Qed.

  (* A write guarded by the declared constraints keeps them standing, whatever
     expression it assigns.  This is the whole point of the path-sensitive
     obligation: the invariant follows from the guard rather than from the
     assigned expression on its own, so a program -- not the optimizer --
     establishes it.  It is proved once for the constraint form, not once per
     program. *)
  Lemma checked_assign_wf :
    forall row_ty ks free_vars tbl u policy A (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      Forall (constr_wf row_ty) ks ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      parameterized_wf Gstore Genv
        (value_wf_with_globals (constrs_hold ks) (tbl :: nil)) A policy ->
      parameterized_wf Gstore Genv
        (value_wf_with_globals (constrs_hold ks) (tbl :: nil)) A
        (CIf (conj_guards ks free_vars u) (CAssign tbl u) policy).
  Proof.
    intros * ? ? ? ? H_tbl ? ? H_pol.
    econstructor.
    1: eauto using conj_guards_ty.
    1:{ econstructor; eauto.
        intros * [? H_guard] ? ? ?.
        unfold value_wf_with_globals. constructor; [ | constructor ].
        right.
        eapply conj_guards_sound with (Gstore := Gstore) (Genv := Genv)
                                      (row_ty := row_ty) (free_vars := free_vars);
          eauto. }
    1:{ eapply parameterized_wf_weaken; [ | exact H_pol ].
        intros * ? ? ? [? ?]; auto. }
  Qed.

  (* Declaring the variable empty establishes the invariant. *)
  Lemma constrs_declared : forall (store : locals) tbl ks,
      holds_for_all_entries (value_wf_with_globals (constrs_hold ks) (tbl :: nil))
        (map.put store tbl (VList nil)).
  Proof.
    unfold holds_for_all_entries, value_wf_with_globals; intros.
    destruct (String.eqb k tbl) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
    1:{ rewrite map.get_put_same in *. do_injection.
        constructor; [ right; apply constrs_hold_nil | constructor ]. }
    1: constructor; [ left; auto | constructor ].
  Qed.

  (* A primary key, as an ordinary row predicate: the row's key occurs exactly
     once in the table.  A row predicate can say this because its body may read
     the table through the hole -- which is exactly why the general form
     subsumes a dedicated uniqueness form, and why no uniqueness constructor is
     needed in the syntax of constraints. *)
  Definition unique_constr (attr : string) (row_ty : type) : constr :=
    mk_constr "_r"
      (EBinop OEq
         (EUnop OLength
            (EFlatmap LikeList (EVar c_tbl) "_r2"
               (EIf (EBinop OEq (EAccess (EVar "_r2") attr) (EAccess (EVar "_r") attr))
                  (EBinop OCons (EVar "_r2") (EAtom (ANil (Some row_ty))))
                  (EAtom (ANil (Some row_ty))))))
         (EAtom (AInt 1))).

  Lemma unique_constr_wf : forall attr rt kt,
      type_wf (TRecord rt) ->
      access_record rt attr = Success kt ->
      constr_wf (TRecord rt) (unique_constr attr (TRecord rt)).
  Proof.
    intros * H_wf H_attr.
    assert (H_in : In (attr, kt) rt) by auto using access_record_sound.
    unfold constr_wf, unique_constr, c_env, c_tbl, c_all;
      cbn [c_row c_body].
    repeat lazymatch goal with
      | |- type_of _ _ _ _ => econstructor
      | |- type_of_unop _ _ _ => constructor
      | |- type_of_binop _ _ _ _ => constructor
      | |- type_of_atom _ _ => constructor
      | |- map.get _ _ = Some _ => repeat rewrite_map_get_put_goal; reflexivity
      | |- access_record _ _ = Success _ => exact H_attr
      | |- In _ _ => exact H_in
      | |- type_wf _ => exact H_wf
      end.
  Qed.
End WithWord.
