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
  (* The guard's value, not just the true case: the guard is the constraint
     read of the candidate value.  Both the write obligation and the per-row
     split rule below are corollaries of this one equality. *)
  Lemma constr_guard_interp : forall row_ty k free_vars u (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      constr_wf row_ty k ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      interp_expr store env (constr_guard k free_vars u)
      = interp_expr (map.empty : locals)
          (map.put map.empty c_tbl (interp_expr store env u)) (constr_expr k).
  Proof.
    unfold constr_guard; intros * ? ? ? H_k H_u ? ? ?.
    assert (H_hole : map.get (map.put (map.empty : tenv) c_tbl (TList row_ty)) c_tbl
                     = Some (TList row_ty)) by (rewrite_map_get_put_goal; reflexivity).
    assert (H_env0 : tenv_wf (map.put (map.empty : tenv) c_tbl (TList row_ty)))
      by (eauto with fiat2_hints).
    (* the substitution puts the candidate value in the hole *)
    erewrite substitute_preserve_sem with
      (Gstore := Gstore) (Genv := Genv) (Genv0 := map.put map.empty c_tbl (TList row_ty));
      eauto using constr_guard_sub_wf, constr_expr_ty.
    cbn [make_sub_env fst snd].
    (* and the constraint reads no mutable variable, so the store it is read
       in does not matter *)
    eapply interp_expr_strengthen with
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
    1: apply map_incl_refl.
  Qed.

  Lemma constr_guard_sound : forall row_ty k free_vars u (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      constr_wf row_ty k ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      interp_expr store env (constr_guard k free_vars u) = VBool true ->
      constr_holds k (interp_expr store env u).
  Proof.
    unfold constr_holds; intros * ? ? ? H_k H_u ? ? ? H_guard.
    erewrite <- constr_guard_interp with (Gstore := Gstore) (Genv := Genv); eauto.
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

  (* ---------------------------------------------------------------------
     Row constraints: the case where the guard need not read the table.

     A constraint whose body does not read the hole says something about each
     row on its own -- a check constraint, or the referencing half of a foreign
     key.  For such a body, "every row of (u :: tbl) satisfies it" splits into
     "u satisfies it" and "every row of tbl satisfies it", and the second
     conjunct is exactly the invariant that already holds.  So the guard for a
     write that conses one row collapses from a scan of the table to a single
     test, with no index at all.

     "Does not read the hole" is expressed by typing the body in an
     environment that binds only the row, which is the same device constr_wf
     uses: a body that mentions the hole simply does not satisfy it.  The side
     condition c_row k <> c_all is hygiene -- the row binder must not be the
     name the quantifier uses for its accumulator, or the two environments
     disagree on it.
     --------------------------------------------------------------------- *)

  Definition row_env (row_ty : type) (k : constr) : tenv :=
    map.put map.empty (c_row k) row_ty.

  Definition row_constr_wf (row_ty : type) (k : constr) : Prop :=
    type_of (map.empty : tenv) (row_env row_ty k) (c_body k) TBool.

  (* What a row constraint says about one row. *)
  Definition row_sat (k : constr) (v : value) : Prop :=
    interp_expr (map.empty : locals) (map.put map.empty (c_row k) v) (c_body k) = VBool true.

  Lemma row_env_incl_c_env : forall row_ty k,
      c_row k <> c_all ->
      map_incl (row_env row_ty k) (c_env row_ty k).
  Proof.
    unfold row_env, c_env; intros * H_ne.
    apply map_incl_step_r.
    1:{ apply map_incl_step; auto using string_dec, map_incl_empty. }
    1: rewrite_map_get_put_goal; apply map.get_empty.
  Qed.

  (* A row constraint is a constraint: its body only reads less. *)
  Lemma row_constr_wf__constr_wf : forall row_ty k,
      c_row k <> c_all ->
      row_constr_wf row_ty k ->
      constr_wf row_ty k.
  Proof.
    unfold row_constr_wf, constr_wf; intros * H_ne H_k.
    eapply type_of_strengthen; eauto using map_incl_refl, row_env_incl_c_env.
  Qed.

  (* The body of a row constraint reads only its row, so the bindings the
     quantifier makes for the hole and the accumulator -- and the store -- do
     not reach it. *)
  Lemma row_body_interp : forall row_ty k (store env : locals) tv v acc,
      type_wf row_ty ->
      c_row k <> c_all ->
      row_constr_wf row_ty k ->
      type_of_value v row_ty ->
      interp_expr store
        (map.put (map.put (map.put env c_tbl tv) (c_row k) v) c_all acc) (c_body k)
      = interp_expr (map.empty : locals) (map.put map.empty (c_row k) v) (c_body k).
  Proof.
    unfold row_constr_wf, row_env; intros * ? H_ne H_k H_v.
    eapply interp_expr_strengthen with
      (Gstore := map.empty : tenv) (Genv := map.put map.empty (c_row k) row_ty)
      (t := TBool).
    1: apply tenv_wf_empty.
    1: eauto using tenv_wf_empty with fiat2_hints.
    1: exact H_k.
    1: apply locals_wf_empty.
    1: eapply locals_wf_step; eauto using locals_wf_empty.
    1: apply map_incl_empty.
    apply map_incl_step_r.
    1:{ apply map_incl_step; auto using string_dec, map_incl_empty. }
    1: rewrite_map_get_put_goal; apply map.get_empty.
  Qed.

  (* The step the quantifier folds with.  Naming it lets the induction below
     keep the body's view of the table fixed while the list it ranges over
     shrinks, which is the whole difficulty: a row constraint does not look at
     the table, but constr_holds binds the hole to the very list being folded. *)
  Definition constr_step (k : constr) (tv : value) (r acc : value) : value :=
    interp_expr (map.empty : locals)
      (map.put (map.put (map.put map.empty c_tbl tv) (c_row k) r) c_all acc)
      (EIf (c_body k) (EVar c_all) (EAtom (ABool false))).

  (* One step consults the row and then either keeps the accumulator or fails
     outright, whatever the table happens to be. *)
  Lemma row_constr_step : forall row_ty k tv r acc,
      type_wf row_ty -> c_row k <> c_all ->
      row_constr_wf row_ty k ->
      type_of_value r row_ty ->
      (row_sat k r /\ constr_step k tv r acc = acc)
      \/ (~ row_sat k r /\ constr_step k tv r acc = VBool false).
  Proof.
    unfold constr_step, row_sat; intros * ? H_ne H_k H_r.
    assert (H_bool : type_of_value
                       (interp_expr (map.empty : locals)
                          (map.put map.empty (c_row k) r) (c_body k)) TBool).
    { eapply type_sound with
        (Gstore := map.empty : tenv) (Genv := map.put map.empty (c_row k) row_ty).
      1: exact H_k.
      1: apply tenv_wf_empty.
      1: eauto using tenv_wf_empty with fiat2_hints.
      1: apply locals_wf_empty.
      1: eapply locals_wf_step; eauto using locals_wf_empty. }
    invert_type_of_value.
    lazymatch goal with
      H: VBool _ = interp_expr _ _ (c_body k) |- _ => symmetry in H
    end.
    lazymatch goal with H: interp_expr _ _ (c_body k) = VBool ?b |- _ => destruct b end.
    1: left. 2: right.
    all: split.
    1,3: congruence.
    all: cbn [interp_expr].
    all: erewrite row_body_interp by eauto.
    all: lazymatch goal with
           H: interp_expr _ _ _ = VBool _ |- _ => rewrite H
         end.
    1: unfold get_local; rewrite map.get_put_same; reflexivity.
    1: reflexivity.
  Qed.

  (* So the quantifier is exactly a Forall over the rows.  The induction is on
     the typing of the rows, which is what licenses the step lemma, and the
     table the body would see stays fixed throughout. *)
  Lemma row_fold_right_iff : forall row_ty k tv l,
      type_wf row_ty -> c_row k <> c_all ->
      row_constr_wf row_ty k ->
      Forall (fun r => type_of_value r row_ty) l ->
      (fold_right (constr_step k tv) (VBool true) l = VBool true
       <-> Forall (row_sat k) l).
  Proof.
    intros * ? H_ne H_k H_l.
    induction H_l as [| a l H_a H_l IHl]; cbn [fold_right].
    1: split; auto.
    destruct (row_constr_step row_ty k tv a
                (fold_right (constr_step k tv) (VBool true) l) H H_ne H_k H_a)
      as [[H_sat H_eq] | [H_nsat H_eq]]; rewrite H_eq.
    1:{ split.
        1: intros H_c; constructor; auto; apply IHl; auto.
        1: intros H_F; invert_Forall; apply IHl; auto. }
    1:{ split.
        1: intros H_c; discriminate.
        1: intros H_F; invert_Forall; contradiction. }
  Qed.

  (* The characterisation a rule can rewrite with: for a row constraint,
     the invariant is a Forall over the rows, so it splits on a cons. *)
  Lemma row_constr_holds_iff : forall row_ty k l,
      type_wf row_ty -> c_row k <> c_all ->
      row_constr_wf row_ty k ->
      Forall (fun r => type_of_value r row_ty) l ->
      (constr_holds k (VList l) <-> Forall (row_sat k) l).
  Proof.
    unfold constr_holds, constr_expr; intros * ? H_ne H_k H_l.
    cbn [interp_expr]. unfold get_local.
    rewrite map.get_put_same. cbn [interp_atom].
    eapply row_fold_right_iff; eauto.
  Qed.

  (* The split: a write that conses one row need only test that row, because
     the rest of the table already satisfies the constraint.  This is what
     makes a check constraint cost nothing to maintain. *)
  Corollary row_constr_holds_cons : forall row_ty k v vs,
      type_wf row_ty -> c_row k <> c_all ->
      row_constr_wf row_ty k ->
      type_of_value v row_ty ->
      Forall (fun r => type_of_value r row_ty) vs ->
      (constr_holds k (VList (v :: vs))
       <-> row_sat k v /\ constr_holds k (VList vs)).
  Proof.
    intros * H_wf H_ne H_k H_v H_vs.
    assert (H_cons : Forall (fun r => type_of_value r row_ty) (v :: vs))
      by (constructor; auto).
    rewrite (row_constr_holds_iff row_ty k (v :: vs) H_wf H_ne H_k H_cons).
    rewrite (row_constr_holds_iff row_ty k vs H_wf H_ne H_k H_vs).
    split.
    1: intros H_F; invert_Forall; auto.
    1: intros [? ?]; constructor; auto.
  Qed.

  (* A write that only removes rows needs no check at all: a predicate on one
     row is still a predicate on one row when the others are gone.  This is
     the delete-side counterpart of row_constr_holds_cons. *)
  Corollary row_constr_holds_filter : forall row_ty k g l,
      type_wf row_ty -> c_row k <> c_all ->
      row_constr_wf row_ty k ->
      Forall (fun r => type_of_value r row_ty) l ->
      constr_holds k (VList l) ->
      constr_holds k (VList (filter g l)).
  Proof.
    intros * H_wf H_ne H_k H_l H_holds.
    apply (proj2 (row_constr_holds_iff row_ty k (filter g l) H_wf H_ne H_k
                    (Forall_filter _ _ g l H_l))).
    apply Forall_filter.
    exact (proj1 (row_constr_holds_iff row_ty k l H_wf H_ne H_k H_l) H_holds).
  Qed.

  (* A boolean value is one of the two booleans. *)
  Lemma type_of_value_TBool : forall (v : value),
      type_of_value v TBool -> v = VBool true \/ v = VBool false.
  Proof.
    intros * H. inversion H; subst. destruct b.
    1: left; reflexivity.
    1: right; reflexivity.
  Qed.

  (* The body of a row constraint evaluates to a boolean, whatever the row. *)
  Lemma row_body_bool : forall row_ty k v,
      type_wf row_ty -> row_constr_wf row_ty k ->
      type_of_value v row_ty ->
      interp_expr (map.empty : locals) (map.put map.empty (c_row k) v) (c_body k)
      = VBool true
      \/ interp_expr (map.empty : locals) (map.put map.empty (c_row k) v) (c_body k)
         = VBool false.
  Proof.
    unfold row_constr_wf, row_env; intros * ? H_k H_v.
    assert (H_bool : type_of_value
                       (interp_expr (map.empty : locals)
                          (map.put map.empty (c_row k) v) (c_body k)) TBool).
    { eapply type_sound with
        (Gstore := map.empty : tenv) (Genv := map.put map.empty (c_row k) row_ty).
      1: exact H_k.
      1: apply tenv_wf_empty.
      1: eauto using tenv_wf_empty with fiat2_hints.
      1: apply locals_wf_empty.
      1: eapply locals_wf_step; eauto using locals_wf_empty. }
    apply type_of_value_TBool; exact H_bool.
  Qed.

  (* A row constraint's body types in any store, since it reads none. *)
  Lemma row_body_ty : forall row_ty k (Gstore : tenv),
      row_constr_wf row_ty k ->
      type_of Gstore (map.put map.empty (c_row k) row_ty) (c_body k) TBool.
  Proof.
    unfold row_constr_wf, row_env; intros.
    eapply type_of_strengthen; eauto using map_incl_empty, map_incl_refl.
  Qed.

  (* The cheap guard: test the one row being written, and never look at the
     table.  This is what the split rule rewrites a constr_guard into. *)
  Definition row_guard (k : constr) (free_vars : list string) (e : expr) : expr :=
    substitute ((c_row k, e) :: nil) free_vars (c_body k).

  Lemma row_guard_sub_wf : forall row_ty k e (Gstore Genv : tenv),
      type_of Gstore Genv e row_ty ->
      sub_wf (map.put map.empty (c_row k) row_ty) Gstore Genv ((c_row k, e) :: nil).
  Proof.
    unfold sub_wf; cbn [sub_lookup fst snd]; intros.
    destruct (String.eqb (c_row k) x) eqn:E;
      rewrite ?eqb_eq, ?eqb_neq in *; subst.
    1:{ rewrite map.get_put_same in *. do_injection.
        rewrite String.eqb_refl. auto. }
    1:{ rewrite map.get_put_diff, map.get_empty in * by congruence. congruence. }
  Qed.

  Lemma row_guard_ty : forall row_ty k free_vars e (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      row_constr_wf row_ty k ->
      type_of Gstore Genv e row_ty ->
      incl (get_free_vars Genv) free_vars ->
      type_of Gstore Genv (row_guard k free_vars e) TBool.
  Proof.
    unfold row_guard; intros.
    eapply substitute_preserve_ty with (Genv0 := map.put map.empty (c_row k) row_ty);
      eauto using row_guard_sub_wf, row_body_ty with fiat2_hints.
  Qed.

  Lemma row_guard_interp : forall row_ty k free_vars e (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      row_constr_wf row_ty k ->
      type_of Gstore Genv e row_ty ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      interp_expr store env (row_guard k free_vars e)
      = interp_expr (map.empty : locals)
          (map.put map.empty (c_row k) (interp_expr store env e)) (c_body k).
  Proof.
    unfold row_guard; intros * ? ? ? H_k H_e ? ? ?.
    assert (H_env0 : tenv_wf (map.put (map.empty : tenv) (c_row k) row_ty))
      by (eauto with fiat2_hints).
    erewrite substitute_preserve_sem with
      (Gstore := Gstore) (Genv := Genv) (Genv0 := map.put map.empty (c_row k) row_ty);
      eauto using row_guard_sub_wf, row_body_ty.
    cbn [make_sub_env fst snd].
    eapply interp_expr_strengthen with
      (Gstore := map.empty : tenv)
      (Genv := map.put map.empty (c_row k) row_ty)
      (t := TBool).
    1: apply tenv_wf_empty.
    1: exact H_env0.
    1: eauto using row_body_ty, tenv_wf_empty.
    1: apply locals_wf_empty.
    1:{ eapply locals_wf_step; eauto using locals_wf_empty.
        eapply type_sound; eauto. }
    1: apply map_incl_empty.
    1: apply map_incl_refl.
  Qed.

  (* The quantifier evaluates to a boolean, so knowing it is not true pins it
     to false -- which is what turns the iff above into an equality of guards. *)
  Lemma constr_expr_bool : forall row_ty k l,
      type_wf row_ty -> constr_wf row_ty k ->
      Forall (fun r => type_of_value r row_ty) l ->
      interp_expr (map.empty : locals) (map.put map.empty c_tbl (VList l))
        (constr_expr k) = VBool true
      \/ interp_expr (map.empty : locals) (map.put map.empty c_tbl (VList l))
           (constr_expr k) = VBool false.
  Proof.
    intros * ? H_k H_l.
    assert (H_env0 : tenv_wf (map.put (map.empty : tenv) c_tbl (TList row_ty)))
      by (apply tenv_wf_step; [ apply tenv_wf_empty | apply WFTList; assumption ]).
    assert (H_lv : type_of_value (VList l) (TList row_ty)) by (constructor; auto).
    assert (H_bool : type_of_value
                       (interp_expr (map.empty : locals)
                          (map.put map.empty c_tbl (VList l)) (constr_expr k)) TBool).
    { eapply type_sound with
        (Gstore := map.empty : tenv) (Genv := map.put map.empty c_tbl (TList row_ty)).
      (* goal-directed, so the premises may come in any order *)
      all: repeat lazymatch goal with
             | |- type_of _ _ (constr_expr _) _ =>
                 eapply constr_expr_ty with (row_ty := row_ty)
             | |- tenv_wf _ => first [ apply tenv_wf_empty | exact H_env0 ]
             | |- locals_wf _ _ =>
                 first [ apply locals_wf_empty
                       | eapply locals_wf_step; eauto using locals_wf_empty ]
             | |- type_wf _ => assumption
             | |- constr_wf _ _ => exact H_k
             | |- map.get _ _ = Some _ => rewrite_map_get_put_goal; reflexivity
             | |- type_of_value _ _ => exact H_lv
             end. }
    apply type_of_value_TBool; exact H_bool.
  Qed.

  (* Reading a list-typed variable out of a well-typed store. *)
  Lemma locals_wf_list : forall (G : tenv) (E : locals) x row_ty,
      locals_wf G E -> map.get G x = Some (TList row_ty) ->
      exists l, map.get E x = Some (VList l)
                /\ Forall (fun r => type_of_value r row_ty) l.
  Proof.
    unfold locals_wf; intros * H_wf H_get.
    specialize (H_wf _ _ H_get).
    destruct (map.get E x) as [ v | ]; [ | contradiction ].
    inversion H_wf; subst. eauto.
  Qed.

  (* ---------------------------------------------------------------------
     The per-row split rule.

     A write that conses one row onto a table carrying a row constraint need
     not scan the table: the guard the elaboration inserts is equal, in every
     store where the constraint already holds, to a single test of the row
     being written.  That store condition is exactly holds_for_all_entries,
     which is what fold_command_with_globals supplies to a rewrite, so this is
     the soundness obligation of a rule that replaces the one guard by the
     other.
     --------------------------------------------------------------------- *)
  Theorem row_split_guard_sound :
    forall row_ty k free_vars e tbl (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      c_row k <> c_all ->
      row_constr_wf row_ty k ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv e row_ty ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      constr_holds k (get_local store tbl) ->
      interp_expr store env (constr_guard k free_vars (EBinop OCons e (ELoc tbl)))
      = interp_expr store env (row_guard k free_vars e).
  Proof.
    intros * H_Gs H_Ge H_rt H_ne H_k H_tbl H_e H_fv H_store H_env H_inv.
    assert (H_kwf : constr_wf row_ty k) by (apply row_constr_wf__constr_wf; auto).
    (* the table holds a list of well-typed rows *)
    destruct (locals_wf_list Gstore store tbl row_ty H_store H_tbl)
      as [ l [ E_tbl H_l ] ].
    unfold get_local in H_inv; rewrite E_tbl in H_inv.
    (* and so does the value the write would store *)
    assert (H_rv : type_of_value (interp_expr store env e) row_ty)
      by (eapply type_sound; eauto).
    assert (H_cons_ty : type_of Gstore Genv (EBinop OCons e (ELoc tbl)) (TList row_ty))
      by (econstructor; eauto; constructor; auto).
    (* both guards, as the constraint read of a value *)
    erewrite constr_guard_interp with (Gstore := Gstore) (Genv := Genv); eauto.
    erewrite row_guard_interp with (Gstore := Gstore) (Genv := Genv); eauto.
    cbn [interp_expr interp_binop]. unfold get_local. rewrite E_tbl.
    (* the row either passes or fails, and the table already passes *)
    destruct (row_body_bool row_ty k (interp_expr store env e) H_rt H_k H_rv)
      as [H_row | H_row]; rewrite H_row.
    (* the split, at this row and this table *)
    all: destruct (row_constr_holds_cons row_ty k (interp_expr store env e) l
                     H_rt H_ne H_k H_rv H_l) as [ H_fwd H_bwd ].
    1:{ (* passes: so does the table, so the quantifier is true *)
        apply H_bwd. split.
        1: exact H_row.
        1: exact H_inv. }
    1:{ (* fails: the quantifier is not true, and it is a boolean *)
        assert (H_cl : Forall (fun r => type_of_value r row_ty)
                         (interp_expr store env e :: l)) by (constructor; auto).
        destruct (constr_expr_bool row_ty k (interp_expr store env e :: l)
                    H_rt H_kwf H_cl) as [ H_c | H_c ].
        2: exact H_c.
        exfalso. specialize (H_fwd H_c).
        destruct H_fwd as [ H_sat _ ]. unfold row_sat in H_sat. congruence. }
  Qed.

  (* The same at the level of a declaration, which carries a list of
     constraints: when every one of them is a row constraint, the conjunction
     the elaboration inserts collapses to a conjunction of single-row tests. *)
  Definition conj_row_guards (ks : list constr) (free_vars : list string) (e : expr) : expr :=
    fold_right (fun k acc => EBinop OAnd (row_guard k free_vars e) acc)
      (EAtom (ABool true)) ks.

  Lemma conj_row_guards_ty : forall row_ty ks free_vars e (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      Forall (row_constr_wf row_ty) ks ->
      type_of Gstore Genv e row_ty ->
      incl (get_free_vars Genv) free_vars ->
      type_of Gstore Genv (conj_row_guards ks free_vars e) TBool.
  Proof.
    unfold conj_row_guards; induction ks; cbn [fold_right]; intros.
    1: repeat constructor.
    invert_Forall. econstructor; eauto using row_guard_ty.
    constructor.
  Qed.

  Theorem conj_row_split_sound :
    forall row_ty ks free_vars e tbl (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      Forall (fun k => c_row k <> c_all) ks ->
      Forall (row_constr_wf row_ty) ks ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv e row_ty ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      constrs_hold ks (get_local store tbl) ->
      interp_expr store env (conj_guards ks free_vars (EBinop OCons e (ELoc tbl)))
      = interp_expr store env (conj_row_guards ks free_vars e).
  Proof.
    unfold conj_guards, conj_row_guards, constrs_hold.
    intros * H_Gs H_Ge H_rt H_ne H_ks H_tbl H_e H_fv H_store H_env H_inv.
    revert H_ne H_ks H_inv.
    induction ks as [| k ks IHks]; cbn [fold_right]; intros H_ne H_ks H_inv.
    1: reflexivity.
    assert (H_head : interp_expr store env
                       (constr_guard k free_vars (EBinop OCons e (ELoc tbl)))
                     = interp_expr store env (row_guard k free_vars e)).
    { eapply row_split_guard_sound with
        (row_ty := row_ty) (Gstore := Gstore) (Genv := Genv).
      all: repeat lazymatch goal with
             | |- tenv_wf _ => eassumption
             | |- type_wf _ => eassumption
             | |- c_row _ <> c_all => exact (Forall_inv H_ne)
             | |- row_constr_wf _ _ => exact (Forall_inv H_ks)
             | |- map.get _ _ = Some _ => eassumption
             | |- type_of _ _ _ _ => eassumption
             | |- incl _ _ => eassumption
             | |- locals_wf _ _ => eassumption
             | |- constr_holds _ _ => exact (Forall_inv H_inv)
             end. }
    cbn [interp_expr]. rewrite H_head.
    rewrite (IHks (Forall_inv_tail H_ne) (Forall_inv_tail H_ks)
               (Forall_inv_tail H_inv)).
    reflexivity.
  Qed.

  (* ---------------------------------------------------------------------
     Table constraints: the body may read the table, but not the accumulator.

     This is the class the quantifier is a plain Forall over, and it is where
     uniqueness lives: a primary key's body reads the table through the hole,
     so it is not a row constraint, but it never touches the accumulator.  The
     row constraints above are the further special case where the hole is not
     read either.
     --------------------------------------------------------------------- *)

  Lemma c_tbl_neq_c_all : c_tbl <> c_all.
  Proof. unfold c_tbl, c_all. intro H; discriminate H. Qed.

  Definition c_env_no_acc (row_ty : type) (k : constr) : tenv :=
    map.put (map.put map.empty c_tbl (TList row_ty)) (c_row k) row_ty.

  Definition tbl_constr_wf (row_ty : type) (k : constr) : Prop :=
    type_of (map.empty : tenv) (c_env_no_acc row_ty k) (c_body k) TBool.

  (* What the body says about one row, given the table it reads. *)
  Definition tbl_sat (k : constr) (tv r : value) : Prop :=
    interp_expr (map.empty : locals)
      (map.put (map.put map.empty c_tbl tv) (c_row k) r) (c_body k) = VBool true.

  Lemma c_env_no_acc_incl : forall row_ty k,
      c_row k <> c_all ->
      map_incl (c_env_no_acc row_ty k) (c_env row_ty k).
  Proof.
    unfold c_env_no_acc, c_env; intros * H_ne.
    apply map_incl_step_r.
    1:{ apply map_incl_step; auto using string_dec.
        apply map_incl_step; auto using string_dec, map_incl_empty. }
    1:{ pose proof c_tbl_neq_c_all as H_ta.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_diff by congruence.
        apply map.get_empty. }
  Qed.

  Lemma tbl_constr_wf__constr_wf : forall row_ty k,
      c_row k <> c_all ->
      tbl_constr_wf row_ty k ->
      constr_wf row_ty k.
  Proof.
    unfold tbl_constr_wf, constr_wf; intros * H_ne H_k.
    eapply type_of_strengthen; eauto using map_incl_refl, c_env_no_acc_incl.
  Qed.

  (* A row constraint is a table constraint that happens not to read the
     table. *)
  Lemma row_constr_wf__tbl_constr_wf : forall row_ty k,
      row_constr_wf row_ty k ->
      tbl_constr_wf row_ty k.
  Proof.
    unfold row_constr_wf, row_env, tbl_constr_wf, c_env_no_acc; intros.
    eapply type_of_strengthen; eauto using map_incl_refl.
    apply map_incl_step; auto using string_dec, map_incl_empty.
  Qed.

  (* The accumulator, and the store, do not reach the body. *)
  Lemma tbl_body_interp : forall row_ty k (store env : locals) tv r acc,
      type_wf row_ty -> c_row k <> c_all ->
      tbl_constr_wf row_ty k ->
      type_of_value tv (TList row_ty) ->
      type_of_value r row_ty ->
      interp_expr store
        (map.put (map.put (map.put env c_tbl tv) (c_row k) r) c_all acc) (c_body k)
      = interp_expr (map.empty : locals)
          (map.put (map.put map.empty c_tbl tv) (c_row k) r) (c_body k).
  Proof.
    unfold tbl_constr_wf, c_env_no_acc; intros * ? H_ne H_k H_tv H_r.
    eapply interp_expr_strengthen with
      (Gstore := map.empty : tenv)
      (Genv := map.put (map.put map.empty c_tbl (TList row_ty)) (c_row k) row_ty)
      (t := TBool).
    1: apply tenv_wf_empty.
    1:{ apply tenv_wf_step; [ | assumption ].
        apply tenv_wf_step; [ apply tenv_wf_empty | apply WFTList; assumption ]. }
    1: exact H_k.
    1: apply locals_wf_empty.
    1:{ eapply locals_wf_step; [ | exact H_r ].
        eapply locals_wf_step; eauto using locals_wf_empty. }
    1: apply map_incl_empty.
    apply map_incl_step_r.
    1:{ apply map_incl_step; auto using string_dec.
        apply map_incl_step; auto using string_dec, map_incl_empty. }
    1:{ pose proof c_tbl_neq_c_all as H_ta.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_diff by congruence.
        apply map.get_empty. }
  Qed.

  (* One step, for a table constraint. *)
  Lemma tbl_constr_step : forall row_ty k tv r acc,
      type_wf row_ty -> c_row k <> c_all ->
      tbl_constr_wf row_ty k ->
      type_of_value tv (TList row_ty) ->
      type_of_value r row_ty ->
      (tbl_sat k tv r /\ constr_step k tv r acc = acc)
      \/ (~ tbl_sat k tv r /\ constr_step k tv r acc = VBool false).
  Proof.
    unfold constr_step, tbl_sat; intros * ? H_ne H_k H_tv H_r.
    assert (H_bool : type_of_value
                       (interp_expr (map.empty : locals)
                          (map.put (map.put map.empty c_tbl tv) (c_row k) r)
                          (c_body k)) TBool).
    { eapply type_sound with
        (Gstore := map.empty : tenv)
        (Genv := map.put (map.put map.empty c_tbl (TList row_ty)) (c_row k) row_ty).
      1: exact H_k.
      1: apply tenv_wf_empty.
      1:{ apply tenv_wf_step; [ | assumption ].
          apply tenv_wf_step; [ apply tenv_wf_empty | apply WFTList; assumption ]. }
      1: apply locals_wf_empty.
      1:{ eapply locals_wf_step; [ | exact H_r ].
          eapply locals_wf_step; eauto using locals_wf_empty. } }
    destruct (type_of_value_TBool _ H_bool) as [ H_b | H_b ].
    1: left. 2: right.
    all: split.
    1,3: congruence.
    all: cbn [interp_expr].
    all: erewrite tbl_body_interp by eauto.
    all: rewrite H_b.
    1: unfold get_local; rewrite map.get_put_same; reflexivity.
    1: reflexivity.
  Qed.

  (* So for a table constraint too the quantifier is a Forall over the rows --
     each row consulted against the whole table. *)
  Lemma tbl_fold_right_iff : forall row_ty k tv l,
      type_wf row_ty -> c_row k <> c_all ->
      tbl_constr_wf row_ty k ->
      type_of_value tv (TList row_ty) ->
      Forall (fun r => type_of_value r row_ty) l ->
      (fold_right (constr_step k tv) (VBool true) l = VBool true
       <-> Forall (tbl_sat k tv) l).
  Proof.
    intros * H_rt H_ne H_k H_tv H_l.
    induction H_l as [| a l H_a H_l IHl]; cbn [fold_right].
    1: split; auto.
    destruct (tbl_constr_step row_ty k tv a
                (fold_right (constr_step k tv) (VBool true) l)
                H_rt H_ne H_k H_tv H_a)
      as [[H_sat H_eq] | [H_nsat H_eq]]; rewrite H_eq.
    1:{ split.
        1: intros H_c; constructor; auto; apply IHl; auto.
        1: intros H_F; invert_Forall; apply IHl; auto. }
    1:{ split.
        1: intros H_c; discriminate.
        1: intros H_F; invert_Forall; contradiction. }
  Qed.

  Lemma tbl_constr_holds_iff : forall row_ty k l,
      type_wf row_ty -> c_row k <> c_all ->
      tbl_constr_wf row_ty k ->
      Forall (fun r => type_of_value r row_ty) l ->
      (constr_holds k (VList l) <-> Forall (tbl_sat k (VList l)) l).
  Proof.
    unfold constr_holds, constr_expr; intros * H_rt H_ne H_k H_l.
    cbn [interp_expr]. unfold get_local.
    rewrite map.get_put_same. cbn [interp_atom].
    eapply tbl_fold_right_iff; eauto.
    constructor; auto.
  Qed.

  (* ---------------------------------------------------------------------
     Counting, for uniqueness.

     A primary key's body counts the rows sharing a key and asks for one.  The
     facts below turn that count into NoDup on the list of keys, which is the
     shape an index can be built against.
     --------------------------------------------------------------------- *)

  Lemma value_eqb_true_iff : forall (v v' : value), value_eqb v v' = true <-> v = v'.
  Proof.
    split; intros; subst; auto using value_eqb_eq, value_eqb_refl.
  Qed.

  Lemma value_eq_dec : forall (v v' : value), {v = v'} + {v <> v'}.
  Proof.
    intros. destruct (value_eqb v v') eqn:E.
    1: left; apply value_eqb_true_iff; exact E.
    1:{ right; intro H_eq.
        apply value_eqb_true_iff in H_eq. congruence. }
  Qed.

  (* A flat_map that emits each element at most once is a filter. *)
  Lemma length_flat_map_sing : forall (A : Type) (b : A -> bool) (l : list A),
      List.length (flat_map (fun v => if b v then v :: nil else nil) l)
      = List.length (List.filter b l).
  Proof.
    induction l as [| a l IH]; cbn [flat_map List.filter]; auto.
    destruct (b a); cbn [List.app List.length]; auto.
  Qed.

  Lemma length_filter_key__count_occ :
    forall (A B : Type) (dec : forall x y : B, {x = y} + {x <> y})
           (eqb : B -> B -> bool) (key : A -> B) (k : B) (l : list A),
      (forall x y, eqb x y = true <-> x = y) ->
      List.length (List.filter (fun a => eqb (key a) k) l)
      = count_occ dec (List.map key l) k.
  Proof.
    intros * H_eqb.
    induction l as [| a l IH]; cbn [List.filter List.map List.length count_occ]; auto.
    destruct (eqb (key a) k) eqn:E_b; destruct (dec (key a) k) as [E_d | E_d];
      cbn [List.length].
    1: f_equal; exact IH.
    1:{ exfalso. apply H_eqb in E_b. contradiction. }
    1:{ exfalso. apply (proj2 (H_eqb (key a) k)) in E_d. congruence. }
    1: exact IH.
  Qed.

  (* "every element's key occurs exactly once" is exactly NoDup on the keys. *)
  Lemma Forall_count_one_iff_NoDup :
    forall (A B : Type) (eqb : B -> B -> bool) (key : A -> B) (l : list A),
      (forall x y, eqb x y = true <-> x = y) ->
      (Forall (fun r => List.length
                          (List.filter (fun r2 => eqb (key r2) (key r)) l) = 1) l
       <-> NoDup (List.map key l)).
  Proof.
    intros * H_eqb.
    (* the spec of eqb makes B's equality decidable, which count_occ needs *)
    assert (dec : forall x y : B, {x = y} + {x <> y}).
    { intros x y. destruct (eqb x y) eqn:E.
      1: left; apply H_eqb; exact E.
      1:{ right; intro H_xy.
          apply (proj2 (H_eqb x y)) in H_xy. congruence. } }
    split.
    1:{ intros H_F.
        apply (proj2 (NoDup_count_occ' dec (List.map key l))).
        intros x H_in. rewrite in_map_iff in H_in.
        destruct H_in as [ r [ H_kr H_rin ] ]; subst.
        rewrite <- length_filter_key__count_occ with (eqb := eqb); auto.
        exact (proj1 (Forall_forall _ l) H_F r H_rin). }
    1:{ intros H_nd.
        pose proof (proj1 (NoDup_count_occ' dec (List.map key l)) H_nd) as H_cnt.
        apply (proj2 (Forall_forall _ l)). intros r H_rin.
        rewrite length_filter_key__count_occ with (dec := dec); auto.
        apply H_cnt, in_map; auto. }
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

  (* The key a row carries. *)
  Definition row_key (attr : string) (v : value) : value :=
    match v with
    | VRecord fs => record_proj attr fs
    | _ => VUnit
    end.

  (* A primary key reads the table but not the accumulator, so it is a table
     constraint, and the quantifier over it is a Forall. *)
  Lemma unique_constr_tbl_wf : forall attr rt kt,
      type_wf (TRecord rt) ->
      access_record rt attr = Success kt ->
      tbl_constr_wf (TRecord rt) (unique_constr attr (TRecord rt)).
  Proof.
    intros * H_wf H_attr.
    assert (H_in : In (attr, kt) rt) by auto using access_record_sound.
    unfold tbl_constr_wf, unique_constr, c_env_no_acc, c_tbl;
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

  (* One-layer reduction equations.  cbn on interp_expr descends under the
     binder a flatmap introduces, which destroys the shape the lemmas below
     match on; rewriting with these peels one constructor at a time instead. *)
  Lemma interp_EVar : forall (store env : locals) x,
      interp_expr store env (EVar x) = get_local env x.
  Proof. reflexivity. Qed.

  Lemma interp_ELoc : forall (store env : locals) x,
      interp_expr store env (ELoc x) = get_local store x.
  Proof. reflexivity. Qed.

  Lemma interp_EAtom : forall (store env : locals) a,
      interp_expr store env (EAtom a) = interp_atom a.
  Proof. reflexivity. Qed.

  Lemma interp_EUnop : forall (store env : locals) o e,
      interp_expr store env (EUnop o e) = interp_unop o (interp_expr store env e).
  Proof. reflexivity. Qed.

  Lemma interp_EBinop : forall (store env : locals) o e1 e2,
      interp_expr store env (EBinop o e1 e2)
      = interp_binop o (interp_expr store env e1) (interp_expr store env e2).
  Proof. reflexivity. Qed.

  Lemma interp_EFlatmap_list : forall (store env : locals) e1 x e2,
      interp_expr store env (EFlatmap LikeList e1 x e2)
      = match interp_expr store env e1 with
        | VList l1 =>
            VList (flat_map
                     (fun v => match interp_expr store (map.put env x v) e2 with
                               | VList l2 => l2
                               | _ => nil
                               end) l1)
        | _ => VUnit
        end.
  Proof. reflexivity. Qed.

  Lemma interp_EAccess : forall (store env : locals) e x,
      interp_expr store env (EAccess e x)
      = match interp_expr store env e with
        | VRecord fs => record_proj x fs
        | _ => VUnit
        end.
  Proof. reflexivity. Qed.

  Lemma interp_ETernop : forall (store env : locals) o e1 e2 e3,
      interp_expr store env (ETernop o e1 e2 e3)
      = interp_ternop o (interp_expr store env e1)
          (interp_expr store env e2) (interp_expr store env e3).
  Proof. reflexivity. Qed.

  Lemma interp_EFold : forall (store env : locals) e1 e2 x y e3,
      interp_expr store env (EFold e1 e2 x y e3)
      = match interp_expr store env e1 with
        | VList l =>
            fold_right
              (fun v a => interp_expr store (map.put (map.put env x v) y a) e3)
              (interp_expr store env e2) l
        | _ => VUnit
        end.
  Proof. reflexivity. Qed.

  Lemma interp_EOptMatch : forall (store env : locals) e e_none x e_some,
      interp_expr store env (EOptMatch e e_none x e_some)
      = match interp_expr store env e with
        | VOption (Some v) => interp_expr store (map.put env x v) e_some
        | VOption None => interp_expr store env e_none
        | _ => VUnit
        end.
  Proof. reflexivity. Qed.

  (* One element of the inner scan: the row is kept exactly when its key
     matches. *)
  Lemma unique_inner_interp : forall attr rt (r v : value) (l0 : list value),
      match interp_expr (map.empty : locals)
              (map.put (map.put (map.put map.empty c_tbl (VList l0)) "_r" r) "_r2" v)
              (EIf (EBinop OEq (EAccess (EVar "_r2") attr)
                      (EAccess (EVar "_r") attr))
                 (EBinop OCons (EVar "_r2") (EAtom (ANil (Some (TRecord rt)))))
                 (EAtom (ANil (Some (TRecord rt))))) with
      | VList l2 => l2
      | _ => nil
      end
      = (if value_eqb (row_key attr v) (row_key attr r) then v :: nil else nil).
  Proof.
    unfold c_tbl, row_key; intros.
    cbn [interp_expr interp_binop interp_atom].
    unfold get_local. repeat rewrite_map_get_put_goal.
    lazymatch goal with
    | |- context[value_eqb ?a ?b] => destruct (value_eqb a b)
    end.
    1: reflexivity.
    1: reflexivity.
  Qed.

  (* So the inner scan of a primary key's body is a filter on the key. *)
  Lemma unique_flat_map : forall attr rt (r : value) (l0 l : list value),
      flat_map
        (fun v =>
           match interp_expr (map.empty : locals)
                   (map.put (map.put (map.put map.empty c_tbl (VList l0)) "_r" r) "_r2" v)
                   (EIf (EBinop OEq (EAccess (EVar "_r2") attr)
                           (EAccess (EVar "_r") attr))
                      (EBinop OCons (EVar "_r2") (EAtom (ANil (Some (TRecord rt)))))
                      (EAtom (ANil (Some (TRecord rt))))) with
           | VList l2 => l2
           | _ => nil
           end) l
      = List.filter (fun r2 => value_eqb (row_key attr r2) (row_key attr r)) l.
  Proof.
    intros. induction l as [| v l IH]; cbn [flat_map List.filter]; auto.
    rewrite unique_inner_interp, IH.
    destruct (value_eqb (row_key attr v) (row_key attr r)); reflexivity.
  Qed.

  (* What a primary key says about one row: its key occurs once. *)
  Lemma unique_tbl_sat_iff : forall attr rt l r,
      tbl_sat (unique_constr attr (TRecord rt)) (VList l) r
      <-> List.length
            (List.filter (fun r2 => value_eqb (row_key attr r2) (row_key attr r)) l)
          = 1.
  Proof.
    unfold tbl_sat, unique_constr; cbn [c_row c_body]; intros.
    rewrite interp_EBinop, interp_EUnop, interp_EFlatmap_list, interp_EVar.
    unfold get_local.
    rewrite map.get_put_diff by (unfold c_tbl; discriminate).
    rewrite map.get_put_same.
    cbn beta iota.
    rewrite unique_flat_map.
    cbn [interp_unop interp_binop interp_atom].
    split.
    1:{ intro H. injection H as H.
        apply value_eqb_true_iff in H. injection H as H. lia. }
    1:{ intro H. rewrite H. reflexivity. }
  Qed.

  Lemma unique_constr_hygienic : forall attr row_ty,
      c_row (unique_constr attr row_ty) <> c_all.
  Proof.
    unfold unique_constr, c_all; cbn [c_row]; intros.
    intro H; discriminate H.
  Qed.

  (* ---------------------------------------------------------------------
     What a primary key declares, as a statement about keys.

     This is the bridge an index needs: the invariant the program maintains is
     a quadratic expression about counting, and what a dictionary index can
     stand for is NoDup on the list of keys.  Everything the guard does is on
     the left; everything the index assumes is on the right.
     --------------------------------------------------------------------- *)
  Theorem unique_constr_holds_iff : forall attr rt kt l,
      type_wf (TRecord rt) ->
      access_record rt attr = Success kt ->
      Forall (fun r => type_of_value r (TRecord rt)) l ->
      (constr_holds (unique_constr attr (TRecord rt)) (VList l)
       <-> NoDup (List.map (row_key attr) l)).
  Proof.
    intros * H_wf H_attr H_l.
    (* the quantifier is a Forall over the rows *)
    rewrite (tbl_constr_holds_iff (TRecord rt) (unique_constr attr (TRecord rt)) l
               H_wf (unique_constr_hygienic attr (TRecord rt))
               (unique_constr_tbl_wf attr rt kt H_wf H_attr) H_l).
    (* and NoDup on the keys is "every key occurs once" *)
    rewrite <- (Forall_count_one_iff_NoDup value value value_eqb (row_key attr) l
                  value_eqb_true_iff).
    (* so the two Foralls agree row by row *)
    split.
    1:{ intros H_F. apply (proj2 (Forall_forall _ l)); intros r H_rin.
        apply (proj1 (unique_tbl_sat_iff attr rt l r)).
        exact (proj1 (Forall_forall _ l) H_F r H_rin). }
    1:{ intros H_F. apply (proj2 (Forall_forall _ l)); intros r H_rin.
        apply (proj2 (unique_tbl_sat_iff attr rt l r)).
        exact (proj1 (Forall_forall _ l) H_F r H_rin). }
  Qed.

  (* Removing rows cannot break a key: dropping entries from a list whose keys
     are distinct leaves them distinct.  So the guard for a row-removing write
     is free here too, as it is for a row predicate. *)
  Corollary unique_constr_holds_filter : forall attr rt kt g l,
      type_wf (TRecord rt) ->
      access_record rt attr = Success kt ->
      Forall (fun r => type_of_value r (TRecord rt)) l ->
      constr_holds (unique_constr attr (TRecord rt)) (VList l) ->
      constr_holds (unique_constr attr (TRecord rt)) (VList (filter g l)).
  Proof.
    intros * H_wf H_attr H_l H_holds.
    apply (proj2 (unique_constr_holds_iff attr rt kt (filter g l) H_wf H_attr
                    (Forall_filter _ _ g l H_l))).
    apply NoDup_map_filter.
    exact (proj1 (unique_constr_holds_iff attr rt kt l H_wf H_attr H_l) H_holds).
  Qed.

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
  (* ---------------------------------------------------------------------
     Uniqueness to a lookup.

     The guard the elaboration inserts at a write that conses one row is, in
     any store where the key already holds, exactly the test "this row's key
     is not already present".  That is a membership test on a list of keys,
     which is what a dictionary index answers in one step -- so an index whose
     keys are the table's keys discharges this guard without scanning.

     The rewrite itself belongs to the index implementation, which is what
     knows that its dictionary's keys are the table's keys; what is proved here
     is the obligation that rewrite reduces to.
     --------------------------------------------------------------------- *)
  Theorem unique_guard_iff_fresh :
    forall attr rt kt free_vars e tbl l (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
      access_record rt attr = Success kt ->
      map.get Gstore tbl = Some (TList (TRecord rt)) ->
      type_of Gstore Genv e (TRecord rt) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      map.get store tbl = Some (VList l) ->
      NoDup (List.map (row_key attr) l) ->
      (interp_expr store env
         (constr_guard (unique_constr attr (TRecord rt)) free_vars
            (EBinop OCons e (ELoc tbl))) = VBool true
       <-> ~ In (row_key attr (interp_expr store env e))
               (List.map (row_key attr) l)).
  Proof.
    intros * H_Gs H_Ge H_rt H_attr H_tbl H_e H_fv H_store H_env E_tbl H_nd.
    (* the rows are well typed, and so is the row being written *)
    destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
      as [ l' [ E_tbl' H_l ] ].
    rewrite E_tbl in E_tbl'. injection E_tbl' as E_tbl'; subst l'.
    assert (H_rv : type_of_value (interp_expr store env e) (TRecord rt))
      by (eapply type_sound; eauto).
    assert (H_cons_ty : type_of Gstore Genv (EBinop OCons e (ELoc tbl))
                          (TList (TRecord rt)))
      by (econstructor; eauto; constructor; auto).
    (* the value the write would store *)
    assert (H_u : interp_expr store env (EBinop OCons e (ELoc tbl))
                  = VList (interp_expr store env e :: l)).
    { rewrite interp_EBinop, interp_ELoc. unfold get_local.
      rewrite E_tbl. reflexivity. }
    (* the guard is the constraint read of that value *)
    erewrite constr_guard_interp with (Gstore := Gstore) (Genv := Genv);
      eauto using unique_constr_wf.
    rewrite H_u.
    (* which, for a primary key, is NoDup on the keys *)
    pose proof (unique_constr_holds_iff attr rt kt
                  (interp_expr store env e :: l) H_rt H_attr
                  (Forall_cons _ H_rv H_l)) as H_iff.
    cbn [List.map] in H_iff. rewrite NoDup_cons_iff in H_iff.
    (* and the table's own keys are already distinct *)
    split.
    1:{ intro H_g. exact (proj1 (proj1 H_iff H_g)). }
    1:{ intro H_fresh. apply (proj2 H_iff). split; assumption. }
  Qed.
End WithWord.
