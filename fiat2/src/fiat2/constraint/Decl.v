Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.constraint.PrimaryKeyCheck fiat2.constraint.CompositeKeyCheck
  fiat2.Utils fiat2.Substitute fiat2.TransfSound fiat2.constraint.Constraint fiat2.rules.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List Permutation.
Import ListNotations.
Local Open Scope bool_scope.

(* Constraints and guards

   This file knows nothing about the surface language or about elaboration.
   See constraint/Surface.v for scommand and elab, the only consumer that
   assembles these guards into a program.

   Two theorems:

     decl_guard_sound   the guard is sufficient -- a write that passes it
                        leaves every declared constraint standing.

     decl_guard_agrees  the guard is necessary -- it evaluates to the
                        same boolean as the general whole-table constr_guard.

   Maintenance alone would be satisfied by a guard that rejects every write
   (the table never changes, so nothing is ever violated); the second
   theorem rules that out.  Since the surface language has no semantics of its
   own, the second is also where preservation lives, with constr_guard as the
   reference. *)

(* A declaration is a constr.  The patterns below recognize the ones a
   cheaper guard exists for: each extracts candidate parameters and accepts
   only if rebuilding the pattern from them gives back the declaration. *)
Definition constr_eqb (k k' : constr) : bool :=
  String.eqb (c_row k) (c_row k') && expr_eqb (c_body k) (c_body k').

Lemma constr_eqb_true : forall k k', constr_eqb k k' = true -> k = k'.
Proof.
  unfold constr_eqb; intros [ r b ] [ r' b' ] H; cbn in H.
  apply andb_prop in H as [ H1 H2 ].
  apply String.eqb_eq in H1; apply expr_eqb_true in H2; subst; reflexivity.
Qed.

Definition unique_attr_ok (row_ty : type) (attr : string) : bool :=
  match row_ty with
  | TRecord rt => match access_record rt attr with Success _ => true | _ => false end
  | _ => false
  end.

Definition unique_candidate (b : expr) : option string :=
  match b with
  | EBinop OEq (EUnop OLength (EFlatmap _ _ _ (EIf (EBinop OEq (EAccess _ attr) _) _ _))) _ =>
      Some attr
  | _ => None
  end.

Definition as_unique (row_ty : type) (k : constr) : option string :=
  match unique_candidate (c_body k) with
  | Some attr =>
      if constr_eqb k (unique_constr attr row_ty) && unique_attr_ok row_ty attr
      then Some attr else None
  | None => None
  end.

(* The same pattern where the row type is not known, read off the
   pattern's own annotation instead. *)
Definition unique_key_of (k : constr) : option string :=
  match c_body k with
  | EBinop OEq (EUnop OLength (EFlatmap _ _ _
      (EIf (EBinop OEq (EAccess _ attr) _) (EBinop OCons _ (EAtom (ANil (Some rt)))) _))) _ =>
      if constr_eqb k (unique_constr attr rt) then Some attr else None
  | _ => None
  end.

Lemma unique_key_of_sound : forall k attr,
    unique_key_of k = Some attr -> exists rt, k = unique_constr attr rt.
Proof.
  unfold unique_key_of; intros * H.
  repeat lazymatch type of H with
    | (match ?y with _ => _ end) = _ => destruct y eqn:?; try discriminate
    end.
  injection H as H; subst.
  eexists; apply constr_eqb_true; eassumption.
Qed.

Fixpoint attrs_of_conj (e : expr) : list string :=
  match e with
  | EBinop OEq (EAccess _ a) _ => [a]
  | EBinop OAnd (EBinop OEq (EAccess _ a) _) rest => a :: attrs_of_conj rest
  | _ => []
  end.

Fixpoint nodupb (l : list string) : bool :=
  match l with
  | [] => true
  | a :: l => negb (existsb (String.eqb a) l) && nodupb l
  end.

Lemma nodupb_NoDup : forall l, nodupb l = true -> NoDup l.
Proof.
  induction l as [ | a l IH ]; cbn; intro H; [ constructor | ].
  apply andb_prop in H as [ H1 H2 ]. constructor; [ | auto ].
  intro H_in. apply Bool.negb_true_iff in H1.
  assert (existsb (String.eqb a) l = true)
    by (apply existsb_exists; exists a; split; [ exact H_in | apply String.eqb_refl ]).
  congruence.
Qed.

Definition unique_many_attrs_ok (row_ty : type) (al : list string) : bool :=
  match row_ty with
  | TRecord rt =>
      nodupb al
      && forallb (fun a => existsb (String.eqb a) (List.map fst rt)) al
  | _ => false
  end.

Definition unique_many_candidate (b : expr) : option (list string) :=
  match b with
  | EBinop OEq (EUnop OLength (EFlatmap _ _ _ (EIf cond _ _))) _ =>
      Some (attrs_of_conj cond)
  | _ => None
  end.

Definition as_unique_many (row_ty : type) (k : constr) : option (list string) :=
  match unique_many_candidate (c_body k) with
  | Some al =>
      if constr_eqb k (unique_many_constr al row_ty) && unique_many_attrs_ok row_ty al
      then Some al else None
  | None => None
  end.

Lemma as_unique_sound : forall row_ty k attr,
    as_unique row_ty k = Some attr ->
    k = unique_constr attr row_ty
    /\ exists rt kt, row_ty = TRecord rt /\ access_record rt attr = Success kt.
Proof.
  unfold as_unique; intros * H.
  destruct (unique_candidate (c_body k)) as [ a | ]; try discriminate.
  destruct (constr_eqb k (unique_constr a row_ty) && unique_attr_ok row_ty a) eqn:E;
    try discriminate.
  injection H as H; subst.
  apply andb_prop in E as [ E1 E2 ].
  split; [ apply constr_eqb_true; exact E1 | ].
  unfold unique_attr_ok in E2.
  destruct row_ty; try discriminate.
  destruct (access_record l attr) eqn:E3; try discriminate; eauto.
Qed.

Lemma as_unique_many_sound : forall row_ty k al,
    as_unique_many row_ty k = Some al ->
    k = unique_many_constr al row_ty
    /\ exists rt, row_ty = TRecord rt /\ NoDup al
                  /\ Forall (fun a => In a (List.map fst rt)) al.
Proof.
  unfold as_unique_many; intros * H.
  destruct (unique_many_candidate (c_body k)) as [ al' | ]; try discriminate.
  destruct (constr_eqb k (unique_many_constr al' row_ty)
            && unique_many_attrs_ok row_ty al') eqn:E; try discriminate.
  injection H as H; subst.
  apply andb_prop in E as [ E1 E2 ].
  split; [ apply constr_eqb_true; exact E1 | ].
  unfold unique_many_attrs_ok in E2.
  destruct row_ty; try discriminate.
  apply andb_prop in E2 as [ E2 E3 ].
  exists l; split; [ reflexivity | split; [ apply nodupb_NoDup; exact E2 | ] ].
  apply Forall_forall; intros a H_in.
  rewrite forallb_forall in E3. apply E3 in H_in.
  apply existsb_exists in H_in as [ a' [ H_in E4 ] ].
  apply String.eqb_eq in E4; subst; exact H_in.
Qed.

Definition reads_only_row (k : constr) : bool :=
  negb (free_immut_in c_tbl (c_body k)) && negb (free_immut_in c_all (c_body k))
  && negb (String.eqb (c_row k) c_tbl) && negb (String.eqb (c_row k) c_all).

(* What the elaboration recognized a declaration as. *)
Inductive cclass : Type :=
| CUnique (attr : string)
| CRow
| CGeneral
| CUniqueMany (attrs : list string).

Definition classify (row_ty : type) (k : constr) : cclass :=
  match as_unique row_ty k with
  | Some attr => CUnique attr
  | None =>
      match as_unique_many row_ty k with
      | Some al => CUniqueMany al
      | None => if reads_only_row k then CRow else CGeneral
      end
  end.

(* The write shapes a class-specific guard can recognize.  A primary key's
   cheap test is equivalent to the quantifier for a write that conses one
   row onto the table, so that shape is matched and anything else falls back on
   the general guard. *)
Definition cons_onto (tbl : string) (e : expr) : option expr :=
  match e with
  | EBinop OCons row (ELoc tbl') => if String.eqb tbl tbl' then Some row else None
  | _ => None
  end.

(* The same single row, added at the end of the table. *)
Definition snoc_onto (tbl : string) (e : expr) : option expr :=
  match e with
  | EBinop OConcat (ELoc tbl') (EBinop OCons row (EAtom (ANil _))) =>
      if String.eqb tbl tbl' then Some row else None
  | _ => None
  end.

(* The other write shape worth a class-specific guard: a filter over the table,
   which only removes rows.  The binder of the flatmap and the variable
   returned must be the same, or the write is not a filter. *)
Definition filter_of (tbl : string) (e : expr) : option (string * expr) :=
  match e with
  | EFlatmap LikeList (ELoc tbl') x
      (EIf p (EBinop OCons (EVar y) (EAtom (ANil _))) (EAtom (ANil _))) =>
      if (String.eqb tbl tbl' && String.eqb x y)%bool then Some (x, p) else None
  | _ => None
  end.

(* A write, as the guard elaboration sees it.  The shape is a property of the
   write alone; what a shape buys depends on the declaration, which is what
   decl_guard decides. *)
Inductive write_shape : Type :=
(* adds exactly one row at the front, leaving the rest of the table *)
| WCons (row : expr)
(* adds exactly one row at the end, leaving the rest of the table *)
| WSnoc (row : expr)
(* removes rows and adds none *)
| WFilter (x : string) (p : expr)
(* anything else *)
| WOther.

Definition classify_write (tbl : string) (e : expr) : write_shape :=
  match cons_onto tbl e with
  | Some row => WCons row
  | None =>
      match snoc_onto tbl e with
      | Some row => WSnoc row
      | None =>
          match filter_of tbl e with
          | Some (x, p) => WFilter x p
          | None => WOther
          end
      end
  end.

(* The guard elaboration inserts for one declared constraint.  The general
   guard decides the constraint outright, at the cost of reading the table once
   per row; a recognized class on a recognized write gets the test that class
   is checked cheaply by.

   A row-removing write needs no test at all for a key or a row predicate:
   both are preserved when rows are dropped.  A general constraint does not
   get this, and must not: its body may read the table, so what it says of a
   row can depend on which other rows are present. *)
Definition decl_guard (row_ty : type) (tbl : string) (free_vars : list string)
  (k : constr) (e : expr) : expr :=
  match classify row_ty k, classify_write tbl e with
  (* the two row-adding shapes get the same test: see snoc_onto *)
  | CUnique attr, WCons row | CUnique attr, WSnoc row =>
      unique_guard_let tbl attr row
  | CUniqueMany attrs, WCons row | CUniqueMany attrs, WSnoc row =>
      unique_many_guard_let tbl attrs row
  | CRow, WCons row | CRow, WSnoc row =>
      row_guard k free_vars row
  | CUnique _, WFilter _ _ | CUniqueMany _, WFilter _ _
  | CRow, WFilter _ _ => EAtom (ABool true)
  | _, _ => constr_guard k free_vars e
  end.

Fixpoint decls_guard (row_ty : type) (tbl : string) (free_vars : list string)
  (ks : list constr) (e : expr) : expr :=
  match ks with
  | nil => EAtom (ABool true)
  | k :: ks => EBinop OAnd (decl_guard row_ty tbl free_vars k e)
                 (decls_guard row_ty tbl free_vars ks e)
  end.

Lemma cons_onto_eq : forall tbl e row,
    cons_onto tbl e = Some row -> e = EBinop OCons row (ELoc tbl).
Proof.
  unfold cons_onto; intros * H.
  destruct e; try discriminate.
  destruct o; try discriminate.
  destruct e2; try discriminate.
  destruct (String.eqb tbl x) eqn:E; try discriminate.
  rewrite eqb_eq in E; subst. injection H as H; subst. reflexivity.
Qed.

Lemma filter_of_eq : forall tbl e x p,
    filter_of tbl e = Some (x, p) ->
    exists t1 t2, e = flatmap_filter_list (ELoc tbl) x p x t1 t2.
Proof.
  unfold filter_of; intros * H.
  (* drill into the pattern: every branch but the matched one is None *)
  repeat lazymatch type of H with
    | (match ?y with _ => _ end) = _ => destruct y eqn:?; try discriminate
    end.
  (* the table's name and the two binders *)
  lazymatch goal with
    E : (_ && _)%bool = true |- _ =>
      rewrite Bool.andb_true_iff in E; destruct E as [ E1 E2 ];
      rewrite eqb_eq in E1, E2; subst
  end.
  injection H as H1 H2; subst. eauto.
Qed.

Lemma snoc_onto_eq : forall tbl e row,
    snoc_onto tbl e = Some row ->
    exists t, e = EBinop OConcat (ELoc tbl) (EBinop OCons row (EAtom (ANil t))).
Proof.
  unfold snoc_onto; intros * H.
  destruct e; try discriminate.
  destruct o; try discriminate.
  destruct e1; try discriminate.
  destruct e2; try discriminate.
  destruct o; try discriminate.
  destruct e2_2; try discriminate.
  destruct a; try discriminate.
  destruct (String.eqb tbl x) eqn:E; try discriminate.
  rewrite eqb_eq in E; subst. injection H as H; subst. eexists; reflexivity.
Qed.

Lemma classify_write_cons : forall tbl e row,
    classify_write tbl e = WCons row -> e = EBinop OCons row (ELoc tbl).
Proof.
  unfold classify_write; intros * H.
  destruct (cons_onto tbl e) as [ r | ] eqn:E.
  1:{ injection H as H; subst. apply cons_onto_eq; exact E. }
  1: destruct (snoc_onto tbl e) as [ | ]; try discriminate.
  1: destruct (filter_of tbl e) as [ [ ] | ]; discriminate.
Qed.

Lemma classify_write_snoc : forall tbl e row,
    classify_write tbl e = WSnoc row ->
    exists t, e = EBinop OConcat (ELoc tbl) (EBinop OCons row (EAtom (ANil t))).
Proof.
  unfold classify_write; intros * H.
  destruct (cons_onto tbl e) as [ r | ]; try discriminate.
  destruct (snoc_onto tbl e) as [ r | ] eqn:E.
  1:{ injection H as H; subst. apply snoc_onto_eq; exact E. }
  1: destruct (filter_of tbl e) as [ [ ] | ]; discriminate.
Qed.

Lemma classify_write_filter : forall tbl e x p,
    classify_write tbl e = WFilter x p ->
    exists t1 t2, e = flatmap_filter_list (ELoc tbl) x p x t1 t2.
Proof.
  unfold classify_write; intros * H.
  destruct (cons_onto tbl e); try discriminate.
  destruct (snoc_onto tbl e); try discriminate.
  destruct (filter_of tbl e) as [ [ y q ] | ] eqn:E; try discriminate.
  injection H as H1 H2; subst. apply filter_of_eq; exact E.
Qed.

Section WithWord.
  Notation value := (value).
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

  (* What a recognized class gives a guard to work with. *)
  Definition class_wf (row_ty : type) (k : constr) (c : cclass) : Prop :=
    match c with
    | CUnique attr =>
        k = unique_constr attr row_ty
        /\ exists rt kt, row_ty = TRecord rt /\ access_record rt attr = Success kt
    | CRow => c_row k <> c_all /\ row_constr_wf (tenv:=tenv) row_ty k
    | CGeneral => constr_wf (tenv:=tenv) row_ty k
    | CUniqueMany al =>
        k = unique_many_constr al row_ty
        /\ exists rt, row_ty = TRecord rt /\ NoDup al
                      /\ Forall (fun a => In a (List.map fst rt)) al
    end.

  Lemma reads_only_row_wf : forall row_ty k,
      reads_only_row k = true -> constr_wf (tenv:=tenv) row_ty k ->
      c_row k <> c_all /\ row_constr_wf (tenv:=tenv) row_ty k.
  Proof.
    unfold reads_only_row, constr_wf, row_constr_wf, c_env, row_env; intros * H H_k.
    repeat (apply andb_prop in H as [ H ? ]).
    repeat lazymatch goal with
      | E : negb _ = true |- _ => apply Bool.negb_true_iff in E
      | E : String.eqb _ _ = false |- _ => apply String.eqb_neq in E
      end.
    split; [ assumption | ].
    eapply not_free_immut_put_ty in H_k; [ | eassumption ].
    rewrite Properties.map.put_put_diff in H_k by congruence.
    eapply (not_free_immut_put_ty c_tbl); eassumption.
  Qed.

  Lemma classify_wf : forall row_ty k,
      constr_wf (tenv:=tenv) row_ty k -> class_wf row_ty k (classify row_ty k).
  Proof.
    unfold classify; intros * H.
    destruct (as_unique row_ty k) as [ attr | ] eqn:E1.
    1: apply as_unique_sound; exact E1.
    destruct (as_unique_many row_ty k) as [ al | ] eqn:E2.
    1: apply as_unique_many_sound; exact E2.
    destruct (reads_only_row k) eqn:E3.
    1: apply reads_only_row_wf; assumption.
    exact H.
  Qed.

  Lemma type_of_snoc_inv : forall (Gstore Genv : tenv) row tbl ta t,
      type_of Gstore Genv
        (EBinop OConcat (ELoc tbl) (EBinop OCons row (EAtom (ANil ta))))
        (TList t) ->
      type_of Gstore Genv row t.
  Proof.
    intros * H. inversion H; subst.
    lazymatch goal with
      H: type_of_binop OConcat _ _ _ |- _ => inversion H; subst
    end.
    lazymatch goal with
      H: type_of _ _ (EBinop OCons _ _) _ |- _ => inversion H; subst
    end.
    lazymatch goal with
      H: type_of_binop OCons _ _ _ |- _ => inversion H; subst
    end.
    assumption.
  Qed.

  Lemma type_of_cons_inv : forall (Gstore Genv : tenv) row tbl t,
      type_of Gstore Genv (EBinop OCons row (ELoc tbl)) (TList t) ->
      type_of Gstore Genv row t.
  Proof.
    intros * H. inversion H; subst.
    lazymatch goal with
      H: type_of_binop OCons _ _ _ |- _ => inversion H; subst
    end.
    assumption.
  Qed.

  Lemma decl_guard_ty : forall row_ty k free_vars tbl u (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      constr_wf row_ty k ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      type_of Gstore Genv (decl_guard row_ty tbl free_vars k u) TBool.
  Proof.
    intros * H_Gs H_Ge H_wf H_d H_tbl H_u H_fv.
    unfold decl_guard.
    pose proof (classify_wf row_ty k H_d) as H_c;
    destruct (classify row_ty k) as [ attr | | | al ];
      destruct (classify_write tbl u) as [ row | row | y q | ] eqn:E_sh;
      cbn beta iota.
    (* the free guard, and every fallback on the general one *)
    all: lazymatch goal with
         | |- type_of _ _ (EAtom (ABool true)) _ => repeat constructor
         | |- type_of _ _ (constr_guard _ _ _) _ =>
             eapply constr_guard_ty; eauto
         | _ => idtac
         end.
    (* a primary key, written by a cons onto the table *)
    1:{ destruct H_c as [ E_k [ rt [ kt [ E_rt H_attr ] ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        eapply unique_guard_let_ty with (kt := kt).
        1: exact H_Gs. 1: exact H_Ge. 1: exact H_wf. 1: exact H_attr.
        1: exact H_tbl.
        1: eapply type_of_cons_inv; exact H_u. }
    (* ... and by an append onto it *)
    1:{ destruct H_c as [ E_k [ rt [ kt [ E_rt H_attr ] ] ] ]; subst.
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        eapply unique_guard_let_ty with (kt := kt).
        1: exact H_Gs. 1: exact H_Ge. 1: exact H_wf. 1: exact H_attr.
        1: exact H_tbl.
        1: eapply type_of_snoc_inv; exact H_u. }
    (* a row constraint tests the row being written *)
    1:{ destruct H_c as [ H_ne H_row ].
        apply classify_write_cons in E_sh; subst.
        eapply row_guard_ty with (row_ty := row_ty).
        1: exact H_Gs. 1: exact H_Ge. 1: exact H_wf. 1: exact H_row.
        1: eapply type_of_cons_inv; exact H_u.
        1: exact H_fv. }
    1:{ destruct H_c as [ H_ne H_row ].
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        eapply row_guard_ty with (row_ty := row_ty).
        1: exact H_Gs. 1: exact H_Ge. 1: exact H_wf. 1: exact H_row.
        1: eapply type_of_snoc_inv; exact H_u.
        1: exact H_fv. }
    (* and the cheap guard for a composite key, same shape and same place *)
    1:{ destruct H_c as [ E_k [ rt [ E_rt [ Hnd HF ] ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        eapply unique_many_guard_let_ty.
        1: exact H_Gs. 1: exact H_Ge. 1: exact H_wf. 1: exact HF.
        1: exact H_tbl.
        1: eapply type_of_cons_inv; exact H_u. }
    1:{ destruct H_c as [ E_k [ rt [ E_rt [ Hnd HF ] ] ] ]; subst.
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        eapply unique_many_guard_let_ty.
        1: exact H_Gs. 1: exact H_Ge. 1: exact H_wf. 1: exact HF.
        1: exact H_tbl.
        1: eapply type_of_snoc_inv; exact H_u. }
  Qed.

  Lemma decls_guard_ty : forall ds row_ty free_vars tbl u (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      Forall (constr_wf row_ty) ds ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      type_of Gstore Genv (decls_guard row_ty tbl free_vars ds u) TBool.
  Proof.
    induction ds; cbn [decls_guard]; intros.
    1: repeat constructor.
    invert_Forall.
    econstructor; eauto using decl_guard_ty.
    constructor.
  Qed.

  (* A row-removing write really does remove rows: the value it stores is a
     filter of the table's. *)
  Lemma classify_write_filter_interp :
    forall tbl u x p (store env : locals) l,
      classify_write tbl u = WFilter x p ->
      map.get store tbl = Some (VList l) ->
      exists g, interp_expr store env u = VList (filter g l).
  Proof.
    intros * H_sh H_tbl.
    apply classify_write_filter in H_sh as [ t1 [ t2 E_u ] ]; subst.
    rewrite interp_flatmap_filter_list.
    cbn [interp_expr]; unfold get_local; rewrite H_tbl.
    eexists; reflexivity.
  Qed.

  (* The obligation at a checked write, for one declared constraint.

     The general guard decides the constraint from nothing; the cheap guard
     decides it only in a store where the constraint already holds of the
     table, which is the extra hypothesis here. *)
  Lemma interp_cons_write : forall (store env : locals) tbl row l,
      map.get store tbl = Some (VList l) ->
      interp_expr store env (EBinop OCons row (ELoc tbl))
      = VList (interp_expr store env row :: l).
  Proof.
    intros * E_tbl. cbn [interp_expr interp_binop]. unfold get_local.
    rewrite E_tbl. reflexivity.
  Qed.

  Lemma interp_snoc_write : forall (store env : locals) tbl row ta l,
      map.get store tbl = Some (VList l) ->
      interp_expr store env
        (EBinop OConcat (ELoc tbl) (EBinop OCons row (EAtom (ANil ta))))
      = VList (l ++ [interp_expr store env row]).
  Proof.
    intros * E_tbl. cbn [interp_expr interp_binop interp_atom].
    unfold get_local. rewrite E_tbl. reflexivity.
  Qed.

  Lemma Forall_Permutation_iff : forall (A : Type) (P : A -> Prop) l l',
      Permutation l l' -> Forall P l -> Forall P l'.
  Proof.
    intros * H_perm H_F. rewrite Forall_forall in H_F |- *.
    intros v H_in. apply H_F.
    eapply Permutation_in; [ apply Permutation_sym; exact H_perm | exact H_in ].
  Qed.

  Lemma row_constr_holds_Permutation : forall row_ty k l l',
      type_wf row_ty -> c_row k <> c_all -> row_constr_wf row_ty k ->
      Forall (fun r => type_of_value r row_ty) l ->
      Permutation l l' ->
      constr_holds k (VList l) -> constr_holds k (VList l').
  Proof.
    intros * H_wf H_ne H_k H_l H_perm H_c.
    assert (H_l' : Forall (fun r => type_of_value r row_ty) l')
      by (eapply Forall_Permutation_iff; eauto).
    apply (proj2 (row_constr_holds_iff row_ty k l' H_wf H_ne H_k H_l')).
    eapply Forall_Permutation_iff; [ exact H_perm | ].
    apply (proj1 (row_constr_holds_iff row_ty k l H_wf H_ne H_k H_l)); exact H_c.
  Qed.

  Lemma unique_constr_holds_Permutation : forall attr rt kt l l',
      type_wf (TRecord rt) -> access_record rt attr = Success kt ->
      Forall (fun v => type_of_value v (TRecord rt)) l ->
      Permutation l l' ->
      constr_holds (unique_constr attr (TRecord rt)) (VList l) ->
      constr_holds (unique_constr attr (TRecord rt)) (VList l').
  Proof.
    intros * H_wf H_attr H_l H_perm H_c.
    assert (H_l' : Forall (fun v => type_of_value v (TRecord rt)) l')
      by (eapply Forall_Permutation_iff; eauto).
    apply (proj2 (unique_constr_holds_iff attr rt kt l' H_wf H_attr H_l')).
    eapply Permutation_NoDup; [ apply Permutation_map; exact H_perm | ].
    apply (proj1 (unique_constr_holds_iff attr rt kt l H_wf H_attr H_l)); exact H_c.
  Qed.

  Lemma unique_many_constr_holds_Permutation : forall al rt l l',
      type_wf (TRecord rt) -> NoDup al ->
      Forall (fun a => In a (List.map fst rt)) al ->
      Forall (fun v => type_of_value v (TRecord rt)) l ->
      Permutation l l' ->
      constr_holds (unique_many_constr al (TRecord rt)) (VList l) ->
      constr_holds (unique_many_constr al (TRecord rt)) (VList l').
  Proof.
    intros * H_wf Hnd HF H_l H_perm H_c.
    assert (H_l' : Forall (fun v => type_of_value v (TRecord rt)) l')
      by (eapply Forall_Permutation_iff; eauto).
    apply (proj2 (unique_many_constr_holds_iff al rt l' H_wf Hnd HF H_l')).
    eapply Permutation_NoDup; [ apply Permutation_map; exact H_perm | ].
    apply (proj1 (unique_many_constr_holds_iff al rt l H_wf Hnd HF H_l)); exact H_c.
  Qed.

  Lemma decl_guard_sound :
    forall row_ty k free_vars tbl u (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      constr_wf row_ty k ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      (forall v, map.get store tbl = Some v ->
                 constr_holds k v) ->
      interp_expr store env (decl_guard row_ty tbl free_vars k u) = VBool true ->
      constr_holds k (interp_expr store env u).
  Proof.
    intros * H_Gs H_Ge H_wf H_d H_tbl H_u H_fv H_store H_env H_inv H_guard.
    unfold decl_guard in H_guard.
    pose proof (classify_wf row_ty k H_d) as H_c;
    destruct (classify row_ty k) as [ attr | | | al ];
      destruct (classify_write tbl u) as [ row | row | y q | ] eqn:E_sh;
      cbn beta iota in H_guard.
    (* every case that falls back on the general guard *)
    all: lazymatch type of H_guard with
         | interp_expr _ _ (constr_guard _ _ _) = _ =>
             eapply constr_guard_sound with (row_ty := row_ty) (free_vars := free_vars);
             [ exact H_Gs | exact H_Ge | exact H_wf
             | exact H_d
             | exact H_u | exact H_fv | exact H_store | exact H_env
             | exact H_guard ]
         | _ => idtac
         end.
    (* the cheap guard, for a key written by a cons onto the table *)
    1:{ destruct H_c as [ E_k [ rt [ kt [ E_rt H_attr ] ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        (* the table's rows, and the uniqueness the invariant gives of them *)
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_key attr) l)).
        { eapply (proj1 (unique_constr_holds_iff attr rt kt l H_wf H_attr H_l)).
          apply H_inv; exact E_tbl. }
        eapply unique_guard_let_establishes with (kt := kt) (l := l).
        1: exact H_Gs.
        1: exact H_Ge.
        1: exact H_wf.
        1: exact H_attr.
        1: exact H_tbl.
        1: eapply type_of_cons_inv; exact H_u.
        1: exact H_store.
        1: exact H_env.
        1: exact E_tbl.
        1: exact H_nd.
        1: exact H_guard. }
    (* THE same key, written by an append. *)
    1:{ destruct H_c as [ E_k [ rt [ kt [ E_rt H_attr ] ] ] ]; subst.
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_key attr) l)).
        { eapply (proj1 (unique_constr_holds_iff attr rt kt l H_wf H_attr H_l)).
          apply H_inv; exact E_tbl. }
        assert (H_row_ty : type_of Gstore Genv row (TRecord rt))
          by (eapply type_of_snoc_inv; exact H_u).
        assert (H_rv : type_of_value (interp_expr store env row) (TRecord rt))
          by (eapply type_sound; eauto).
        rewrite (interp_snoc_write store env tbl row ta l E_tbl).
        eapply unique_constr_holds_Permutation
          with (kt := kt) (l := interp_expr store env row :: l).
        1: exact H_wf.
        1: exact H_attr.
        1: constructor; [ exact H_rv | exact H_l ].
        1: apply Permutation_cons_append.
        rewrite <- (interp_cons_write store env tbl row l E_tbl).
        eapply unique_guard_let_establishes with (kt := kt) (l := l).
        1: exact H_Gs.
        1: exact H_Ge.
        1: exact H_wf.
        1: exact H_attr.
        1: exact H_tbl.
        1: exact H_row_ty.
        1: exact H_store.
        1: exact H_env.
        1: exact E_tbl.
        1: exact H_nd.
        1: exact H_guard. }
    (* no guard at all: a key survives a write that only removes rows *)
    1:{ destruct H_c as [ E_k [ rt [ kt [ E_rt H_attr ] ] ] ]; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        destruct (classify_write_filter_interp tbl u y q store env l E_sh E_tbl)
          as [ g E_u ].
        rewrite E_u.
        eapply unique_constr_holds_filter;
          [ exact H_wf | exact H_attr | exact H_l | apply H_inv; exact E_tbl ]. }
    (* a row constraint: its guard is the declared guard, by
       row_split_guard_sound, so the declared guard passed too *)
    1:{ destruct H_c as [ H_ne H_row ].
        apply classify_write_cons in E_sh; subst.
        destruct (locals_wf_list Gstore store tbl row_ty H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_at : constr_holds (k) (get_local store tbl))
          by (unfold get_local; rewrite E_tbl; apply H_inv; exact E_tbl).
        eapply constr_guard_sound with (row_ty := row_ty) (free_vars := free_vars);
          [ exact H_Gs | exact H_Ge | exact H_wf
          | apply row_constr_wf__constr_wf; [ exact H_ne | exact H_row ]
          | econstructor; [ constructor
                          | eapply type_of_cons_inv; exact H_u
                          | constructor; exact H_tbl ]
          | exact H_fv | exact H_store | exact H_env | ].
        erewrite row_split_guard_sound with (row_ty := row_ty);
          [ exact H_guard
          | exact H_Gs | exact H_Ge | exact H_wf | exact H_ne | exact H_row
          | exact H_tbl | eapply type_of_cons_inv; exact H_u | exact H_fv
          | exact H_store | exact H_env | exact H_at ]. }
    (* the row predicate, at the append.  Same guard, same bridge. *)
    1:{ destruct H_c as [ H_ne H_row ].
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        destruct (locals_wf_list Gstore store tbl row_ty H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_at : constr_holds (k) (get_local store tbl))
          by (unfold get_local; rewrite E_tbl; apply H_inv; exact E_tbl).
        assert (H_row_ty : type_of Gstore Genv row row_ty)
          by (eapply type_of_snoc_inv; exact H_u).
        assert (H_rv : type_of_value (interp_expr store env row) row_ty)
          by (eapply type_sound; eauto).
        rewrite (interp_snoc_write store env tbl row ta l E_tbl).
        eapply row_constr_holds_Permutation
          with (row_ty := row_ty) (l := interp_expr store env row :: l).
        1: exact H_wf.
        1: exact H_ne.
        1: exact H_row.
        1: constructor; [ exact H_rv | exact H_l ].
        1: apply Permutation_cons_append.
        rewrite <- (interp_cons_write store env tbl row l E_tbl).
        eapply constr_guard_sound with (row_ty := row_ty) (free_vars := free_vars);
          [ exact H_Gs | exact H_Ge | exact H_wf
          | apply row_constr_wf__constr_wf; [ exact H_ne | exact H_row ]
          | econstructor; [ constructor
                          | exact H_row_ty
                          | constructor; exact H_tbl ]
          | exact H_fv | exact H_store | exact H_env | ].
        erewrite row_split_guard_sound with (row_ty := row_ty);
          [ exact H_guard
          | exact H_Gs | exact H_Ge | exact H_wf | exact H_ne | exact H_row
          | exact H_tbl | exact H_row_ty | exact H_fv
          | exact H_store | exact H_env | exact H_at ]. }
    (* no guard at all: a row predicate survives it too *)
    1:{ destruct H_c as [ H_ne H_row ].
        destruct (locals_wf_list Gstore store tbl row_ty H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        destruct (classify_write_filter_interp tbl u y q store env l E_sh E_tbl)
          as [ g E_u ].
        rewrite E_u.
        eapply row_constr_holds_filter;
          [ exact H_wf | exact H_ne | exact H_row | exact H_l
          | apply H_inv; exact E_tbl ]. }
    (* the cheap guard for a composite key written by a cons *)
    1:{ destruct H_c as [ E_k [ rt [ E_rt [ Hnd HF ] ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_keys al) l)).
        { eapply (proj1 (unique_many_constr_holds_iff al rt l H_wf Hnd HF H_l)).
          apply H_inv; exact E_tbl. }
        eapply unique_many_guard_let_establishes with (l := l).
        1: exact H_Gs.
        1: exact H_Ge.
        1: exact H_wf.
        1: exact Hnd.
        1: exact HF.
        1: exact H_tbl.
        1: eapply type_of_cons_inv; exact H_u.
        1: exact H_store.
        1: exact H_env.
        1: exact E_tbl.
        1: exact H_nd.
        1: exact H_guard. }
    (* the composite key, at the append *)
    1:{ destruct H_c as [ E_k [ rt [ E_rt [ Hnd HF ] ] ] ]; subst.
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_keys al) l)).
        { eapply (proj1 (unique_many_constr_holds_iff al rt l H_wf Hnd HF H_l)).
          apply H_inv; exact E_tbl. }
        assert (H_row_ty : type_of Gstore Genv row (TRecord rt))
          by (eapply type_of_snoc_inv; exact H_u).
        assert (H_rv : type_of_value (interp_expr store env row) (TRecord rt))
          by (eapply type_sound; eauto).
        rewrite (interp_snoc_write store env tbl row ta l E_tbl).
        eapply unique_many_constr_holds_Permutation
          with (l := interp_expr store env row :: l).
        1: exact H_wf.
        1: exact Hnd.
        1: exact HF.
        1: constructor; [ exact H_rv | exact H_l ].
        1: apply Permutation_cons_append.
        rewrite <- (interp_cons_write store env tbl row l E_tbl).
        eapply unique_many_guard_let_establishes with (l := l).
        1: exact H_Gs.
        1: exact H_Ge.
        1: exact H_wf.
        1: exact Hnd.
        1: exact HF.
        1: exact H_tbl.
        1: exact H_row_ty.
        1: exact H_store.
        1: exact H_env.
        1: exact E_tbl.
        1: exact H_nd.
        1: exact H_guard. }
    (* and no guard at all: a composite key survives a row-removing write *)
    1:{ destruct H_c as [ E_k [ rt [ E_rt [ Hnd HF ] ] ] ]; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        destruct (classify_write_filter_interp tbl u y q store env l E_sh E_tbl)
          as [ g E_u ].
        rewrite E_u.
        eapply unique_many_constr_holds_filter;
          [ exact H_wf | exact Hnd | exact HF | exact H_l
          | apply H_inv; exact E_tbl ]. }
  Qed.

  (* The same, for the conjunction a declaration's whole list elaborates to. *)
  Lemma decls_guard_sound :
    forall ds row_ty free_vars tbl u (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      Forall (constr_wf row_ty) ds ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      (forall v, map.get store tbl = Some v ->
                 Forall (fun d => constr_holds d v) ds) ->
      interp_expr store env (decls_guard row_ty tbl free_vars ds u) = VBool true ->
      Forall (fun d => constr_holds d
                         (interp_expr store env u)) ds.
  Proof.
    induction ds as [ | d ds IH ]; cbn [decls_guard]; intros * H_Gs H_Ge H_wf H_ds
      H_tbl H_u H_fv H_store H_env H_inv H_guard.
    1: constructor.
    invert_Forall.
    apply interp_and_true in H_guard as [ H_d H_rest ].
    constructor.
    1:{ eapply decl_guard_sound with (row_ty := row_ty) (tbl := tbl)
                                     (free_vars := free_vars).
        1: exact H_Gs.
        1: exact H_Ge.
        1: exact H_wf.
        1: assumption.
        1: exact H_tbl.
        1: exact H_u.
        1: exact H_fv.
        1: exact H_store.
        1: exact H_env.
        1:{ intros v H_v. specialize (H_inv v H_v). invert_Forall. assumption. }
        1: exact H_d. }
    1:{ eapply IH with (row_ty := row_ty) (tbl := tbl) (free_vars := free_vars).
        1: exact H_Gs.
        1: exact H_Ge.
        1: exact H_wf.
        1: assumption.
        1: exact H_tbl.
        1: exact H_u.
        1: exact H_fv.
        1: exact H_store.
        1: exact H_env.
        1:{ intros v H_v. specialize (H_inv v H_v). invert_Forall. assumption. }
        1: exact H_rest. }
  Qed.

  Corollary decls_guard_sound_constrs :
    forall ds row_ty free_vars tbl u (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      Forall (constr_wf row_ty) ds ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      holds_for_all_entries
        (value_wf_with_globals (constrs_hold ds)
           (tbl :: nil)) store ->
      interp_expr store env (decls_guard row_ty tbl free_vars ds u) = VBool true ->
      constrs_hold ds (interp_expr store env u).
  Proof.
    unfold constrs_hold; intros * H_Gs H_Ge H_wf H_ds H_tbl H_u
      H_fv H_store H_env H_inv H_guard.
    eapply decls_guard_sound with (row_ty := row_ty) (tbl := tbl)
                                  (free_vars := free_vars);
      [ exact H_Gs | exact H_Ge | exact H_wf | exact H_ds | exact H_tbl
      | exact H_u | exact H_fv | exact H_store | exact H_env
      | | exact H_guard ].
    (* the invariant, read off the store at tbl *)
    1:{ intros v H_v. pose proof (H_inv tbl v H_v) as H_at.
        unfold value_wf_with_globals in H_at; invert_Forall.
        lazymatch goal with
          H: tbl <> tbl \/ _ |- _ => destruct H as [ H_ne | H_h ]; [ congruence | ]
        end.
        unfold constrs_hold in H_h.
        exact H_h. }
  Qed.

  (* ---------------------------------------------------------------------
     The guard elaboration emits decides what the declared guard decides.

     decls_guard_sound above is the half the invariant needs.  This is the
     whole equality, and it says that choosing a class-specific guard changes
     no behaviour whatever -- including which writes run their policy -- so
     elab is an optimization of the reference elaboration that always emits
     conj_guards, not a different language.  It holds in any store where the
     declaration already holds of the table, which is everywhere the program
     can reach.
     --------------------------------------------------------------------- *)
  (* The general guard's value is a function of the written value alone
     (constr_guard_interp), and it is a boolean, so two writes whose values
     satisfy the constraint under the same conditions get the same guard.
     That is what lets the append reuse the cons's agreement. *)
  Lemma constr_guard_agrees_on_iff :
    forall row_ty k free_vars u1 u2 (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      constr_wf row_ty k ->
      type_of Gstore Genv u1 (TList row_ty) ->
      type_of Gstore Genv u2 (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      (constr_holds k (interp_expr store env u1)
       <-> constr_holds k (interp_expr store env u2)) ->
      interp_expr store env (constr_guard k free_vars u1)
      = interp_expr store env (constr_guard k free_vars u2).
  Proof.
    intros * H_Gs H_Ge H_wf H_k H_u1 H_u2 H_fv H_store H_env H_iff.
    (* each guard is a boolean, by its own typing *)
    assert (H_b1 : exists b, interp_expr store env (constr_guard k free_vars u1)
                             = VBool b).
    1:{ pose proof (type_sound Gstore Genv _ TBool
                      (constr_guard_ty row_ty k free_vars u1 Gstore Genv
                         H_Gs H_Ge H_wf H_k H_u1 H_fv)
                      H_Gs H_Ge store env H_store H_env) as H_t.
        inversion H_t; subst; eauto. }
    assert (H_b2 : exists b, interp_expr store env (constr_guard k free_vars u2)
                             = VBool b).
    1:{ pose proof (type_sound Gstore Genv _ TBool
                      (constr_guard_ty row_ty k free_vars u2 Gstore Genv
                         H_Gs H_Ge H_wf H_k H_u2 H_fv)
                      H_Gs H_Ge store env H_store H_env) as H_t.
        inversion H_t; subst; eauto. }
    destruct H_b1 as [ b1 E1 ]; destruct H_b2 as [ b2 E2 ].
    rewrite E1, E2. destruct b1; destruct b2; try reflexivity.
    (* the two mixed cases each contradict the iff *)
    1:{ exfalso.
        assert (H_c1 : constr_holds k (interp_expr store env u1))
          by (eapply constr_guard_sound with (row_ty := row_ty) (free_vars := free_vars);
              [ exact H_Gs | exact H_Ge | exact H_wf | exact H_k | exact H_u1
              | exact H_fv | exact H_store | exact H_env | exact E1 ]).
        apply H_iff in H_c1.
        assert (E2' : interp_expr store env (constr_guard k free_vars u2)
                      = VBool true)
          by (eapply constr_guard_complete with (row_ty := row_ty);
              [ exact H_Gs | exact H_Ge | exact H_wf | exact H_k | exact H_u2
              | exact H_fv | exact H_store | exact H_env | exact H_c1 ]).
        rewrite E2 in E2'; discriminate. }
    1:{ exfalso.
        assert (H_c2 : constr_holds k (interp_expr store env u2))
          by (eapply constr_guard_sound with (row_ty := row_ty) (free_vars := free_vars);
              [ exact H_Gs | exact H_Ge | exact H_wf | exact H_k | exact H_u2
              | exact H_fv | exact H_store | exact H_env | exact E2 ]).
        apply H_iff in H_c2.
        assert (E1' : interp_expr store env (constr_guard k free_vars u1)
                      = VBool true)
          by (eapply constr_guard_complete with (row_ty := row_ty);
              [ exact H_Gs | exact H_Ge | exact H_wf | exact H_k | exact H_u1
              | exact H_fv | exact H_store | exact H_env | exact H_c2 ]).
        rewrite E1 in E1'; discriminate. }
  Qed.

  Lemma decl_guard_agrees :
    forall row_ty k free_vars tbl u (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      constr_wf row_ty k ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      (forall v, map.get store tbl = Some v ->
                 constr_holds k v) ->
      interp_expr store env (decl_guard row_ty tbl free_vars k u)
      = interp_expr store env
          (constr_guard k free_vars u).
  Proof.
    intros * H_Gs H_Ge H_wf H_d H_tbl H_u H_fv H_store H_env H_inv.
    unfold decl_guard.
    pose proof (classify_wf row_ty k H_d) as H_c;
    destruct (classify row_ty k) as [ attr | | | al ];
      destruct (classify_write tbl u) as [ row | row | y q | ] eqn:E_sh;
      cbn beta iota.
    (* every case that emits the general guard already *)
    all: try reflexivity.
    (* a key written by a cons onto the table *)
    1:{ destruct H_c as [ E_k [ rt [ kt [ E_rt H_attr ] ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_key attr) l)).
        { eapply (proj1 (unique_constr_holds_iff attr rt kt l H_wf H_attr H_l)).
          apply H_inv; exact E_tbl. }
        eapply unique_guard_let_sound with (kt := kt) (l := l);
          [ exact H_Gs | exact H_Ge | exact H_wf | exact H_attr | exact H_tbl
          | eapply type_of_cons_inv; exact H_u | exact H_fv | exact H_store
          | exact H_env | exact E_tbl | exact H_nd ]. }
    (* THE same key at an append. *)
    1:{ destruct H_c as [ E_k [ rt [ kt [ E_rt H_attr ] ] ] ]; subst.
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_key attr) l)).
        { eapply (proj1 (unique_constr_holds_iff attr rt kt l H_wf H_attr H_l)).
          apply H_inv; exact E_tbl. }
        assert (H_row_ty : type_of Gstore Genv row (TRecord rt))
          by (eapply type_of_snoc_inv; exact H_u).
        assert (H_rv : type_of_value (interp_expr store env row) (TRecord rt))
          by (eapply type_sound; eauto).
        assert (H_cons_ty : type_of Gstore Genv (EBinop OCons row (ELoc tbl))
                              (TList (TRecord rt)))
          by (econstructor; [ constructor | exact H_row_ty
                            | constructor; exact H_tbl ]).
        assert (H_Fc : Forall (fun v => type_of_value v (TRecord rt))
                         (interp_expr store env row :: l))
          by (constructor; [ exact H_rv | exact H_l ]).
        assert (H_Fa : Forall (fun v => type_of_value v (TRecord rt))
                         (l ++ [interp_expr store env row]))
          by (eapply Forall_Permutation_iff;
              [ apply Permutation_cons_append | exact H_Fc ]).
        transitivity (interp_expr store env
                        (constr_guard (unique_constr attr (TRecord rt))
                           free_vars (EBinop OCons row (ELoc tbl)))).
        1:{ eapply unique_guard_let_sound with (kt := kt) (l := l);
              [ exact H_Gs | exact H_Ge | exact H_wf | exact H_attr
              | exact H_tbl | exact H_row_ty | exact H_fv | exact H_store
              | exact H_env | exact E_tbl | exact H_nd ]. }
        1:{ eapply constr_guard_agrees_on_iff with (row_ty := TRecord rt);
              [ exact H_Gs | exact H_Ge | exact H_wf
              | eapply unique_constr_wf; [ exact H_wf | exact H_attr ]
              | exact H_cons_ty | exact H_u | exact H_fv | exact H_store
              | exact H_env | ].
            rewrite (interp_cons_write store env tbl row l E_tbl).
            rewrite (interp_snoc_write store env tbl row ta l E_tbl).
            split; intros H_c.
            1: eapply unique_constr_holds_Permutation with (kt := kt);
                 [ exact H_wf | exact H_attr | exact H_Fc
                 | apply Permutation_cons_append | exact H_c ].
            1: eapply unique_constr_holds_Permutation with (kt := kt);
                 [ exact H_wf | exact H_attr | exact H_Fa
                 | apply Permutation_sym, Permutation_cons_append
                 | exact H_c ]. } }
    (* a key under a row-removing write: the general guard passes too, so
       dropping it changes nothing, not even which writes run their policy *)
    1:{ destruct H_c as [ E_k [ rt [ kt [ E_rt H_attr ] ] ] ]; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        destruct (classify_write_filter_interp tbl u y q store env l E_sh E_tbl)
          as [ g E_u ].
        cbn [interp_expr interp_atom]; symmetry.
        eapply constr_guard_complete with (row_ty := TRecord rt);
          [ exact H_Gs | exact H_Ge | exact H_wf
          | eapply unique_constr_wf; [ exact H_wf | exact H_attr ]
          | exact H_u | exact H_fv | exact H_store | exact H_env | ].
        rewrite E_u.
        eapply unique_constr_holds_filter;
          [ exact H_wf | exact H_attr | exact H_l | apply H_inv; exact E_tbl ]. }
    (* a row constraint: this is exactly row_split_guard_sound *)
    1:{ destruct H_c as [ H_ne H_row ].
        apply classify_write_cons in E_sh; subst.
        destruct (locals_wf_list Gstore store tbl row_ty H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        symmetry.
        eapply row_split_guard_sound with (row_ty := row_ty);
          [ exact H_Gs | exact H_Ge | exact H_wf | exact H_ne | exact H_row
          | exact H_tbl | eapply type_of_cons_inv; exact H_u | exact H_fv
          | exact H_store | exact H_env
          | unfold get_local; rewrite E_tbl; apply H_inv; exact E_tbl ]. }
    (* the row predicate at an append *)
    1:{ destruct H_c as [ H_ne H_row ].
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        destruct (locals_wf_list Gstore store tbl row_ty H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_row_ty : type_of Gstore Genv row row_ty)
          by (eapply type_of_snoc_inv; exact H_u).
        assert (H_rv : type_of_value (interp_expr store env row) row_ty)
          by (eapply type_sound; eauto).
        assert (H_cons_ty : type_of Gstore Genv (EBinop OCons row (ELoc tbl))
                              (TList row_ty))
          by (econstructor; [ constructor | exact H_row_ty
                            | constructor; exact H_tbl ]).
        assert (H_Fc : Forall (fun v => type_of_value v row_ty)
                         (interp_expr store env row :: l))
          by (constructor; [ exact H_rv | exact H_l ]).
        assert (H_Fa : Forall (fun v => type_of_value v row_ty)
                         (l ++ [interp_expr store env row]))
          by (eapply Forall_Permutation_iff;
              [ apply Permutation_cons_append | exact H_Fc ]).
        transitivity (interp_expr store env
                        (constr_guard (k)
                           free_vars (EBinop OCons row (ELoc tbl)))).
        1:{ symmetry.
            eapply row_split_guard_sound with (row_ty := row_ty);
              [ exact H_Gs | exact H_Ge | exact H_wf | exact H_ne | exact H_row
              | exact H_tbl | exact H_row_ty | exact H_fv
              | exact H_store | exact H_env
              | unfold get_local; rewrite E_tbl; apply H_inv; exact E_tbl ]. }
        1:{ eapply constr_guard_agrees_on_iff with (row_ty := row_ty);
              [ exact H_Gs | exact H_Ge | exact H_wf
              | apply row_constr_wf__constr_wf; [ exact H_ne | exact H_row ]
              | exact H_cons_ty | exact H_u | exact H_fv | exact H_store
              | exact H_env | ].
            rewrite (interp_cons_write store env tbl row l E_tbl).
            rewrite (interp_snoc_write store env tbl row ta l E_tbl).
            split; intros H_c.
            1: eapply row_constr_holds_Permutation with (row_ty := row_ty);
                 [ exact H_wf | exact H_ne | exact H_row | exact H_Fc
                 | apply Permutation_cons_append | exact H_c ].
            1: eapply row_constr_holds_Permutation with (row_ty := row_ty);
                 [ exact H_wf | exact H_ne | exact H_row | exact H_Fa
                 | apply Permutation_sym, Permutation_cons_append
                 | exact H_c ]. } }
    (* a row constraint under a row-removing write *)
    1:{ destruct H_c as [ H_ne H_row ].
        destruct (locals_wf_list Gstore store tbl row_ty H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        destruct (classify_write_filter_interp tbl u y q store env l E_sh E_tbl)
          as [ g E_u ].
        cbn [interp_expr interp_atom]; symmetry.
        eapply constr_guard_complete with (row_ty := row_ty);
          [ exact H_Gs | exact H_Ge | exact H_wf
          | apply row_constr_wf__constr_wf; [ exact H_ne | exact H_row ]
          | exact H_u | exact H_fv | exact H_store | exact H_env | ].
        rewrite E_u.
        eapply row_constr_holds_filter;
          [ exact H_wf | exact H_ne | exact H_row | exact H_l
          | apply H_inv; exact E_tbl ]. }
    (* a composite key written by a cons onto the table *)
    1:{ destruct H_c as [ E_k [ rt [ E_rt [ Hnd HF ] ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_keys al) l)).
        { eapply (proj1 (unique_many_constr_holds_iff al rt l H_wf Hnd HF H_l)).
          apply H_inv; exact E_tbl. }
        eapply unique_many_guard_let_sound with (l := l);
          [ exact H_Gs | exact H_Ge | exact H_wf | exact Hnd | exact HF
          | exact H_tbl | eapply type_of_cons_inv; exact H_u | exact H_fv
          | exact H_store | exact H_env | exact E_tbl | exact H_nd ]. }
    (* the composite key at an append *)
    1:{ destruct H_c as [ E_k [ rt [ E_rt [ Hnd HF ] ] ] ]; subst.
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_keys al) l)).
        { eapply (proj1 (unique_many_constr_holds_iff al rt l H_wf Hnd HF H_l)).
          apply H_inv; exact E_tbl. }
        assert (H_row_ty : type_of Gstore Genv row (TRecord rt))
          by (eapply type_of_snoc_inv; exact H_u).
        assert (H_rv : type_of_value (interp_expr store env row) (TRecord rt))
          by (eapply type_sound; eauto).
        assert (H_cons_ty : type_of Gstore Genv (EBinop OCons row (ELoc tbl))
                              (TList (TRecord rt)))
          by (econstructor; [ constructor | exact H_row_ty
                            | constructor; exact H_tbl ]).
        assert (H_Fc : Forall (fun v => type_of_value v (TRecord rt))
                         (interp_expr store env row :: l))
          by (constructor; [ exact H_rv | exact H_l ]).
        assert (H_Fa : Forall (fun v => type_of_value v (TRecord rt))
                         (l ++ [interp_expr store env row]))
          by (eapply Forall_Permutation_iff;
              [ apply Permutation_cons_append | exact H_Fc ]).
        transitivity (interp_expr store env
                        (constr_guard (unique_many_constr al (TRecord rt))
                           free_vars (EBinop OCons row (ELoc tbl)))).
        1:{ eapply unique_many_guard_let_sound with (l := l);
              [ exact H_Gs | exact H_Ge | exact H_wf | exact Hnd | exact HF
              | exact H_tbl | exact H_row_ty | exact H_fv
              | exact H_store | exact H_env | exact E_tbl | exact H_nd ]. }
        1:{ eapply constr_guard_agrees_on_iff with (row_ty := TRecord rt);
              [ exact H_Gs | exact H_Ge | exact H_wf
              | eapply unique_many_constr_wf; [ exact H_wf | exact HF ]
              | exact H_cons_ty | exact H_u | exact H_fv | exact H_store
              | exact H_env | ].
            rewrite (interp_cons_write store env tbl row l E_tbl).
            rewrite (interp_snoc_write store env tbl row ta l E_tbl).
            split; intros H_c.
            1: eapply unique_many_constr_holds_Permutation;
                 [ exact H_wf | exact Hnd | exact HF | exact H_Fc
                 | apply Permutation_cons_append | exact H_c ].
            1: eapply unique_many_constr_holds_Permutation;
                 [ exact H_wf | exact Hnd | exact HF | exact H_Fa
                 | apply Permutation_sym, Permutation_cons_append
                 | exact H_c ]. } }
    (* and under a row-removing write, where the general guard passes too *)
    1:{ destruct H_c as [ E_k [ rt [ E_rt [ Hnd HF ] ] ] ]; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        destruct (classify_write_filter_interp tbl u y q store env l E_sh E_tbl)
          as [ g E_u ].
        cbn [interp_expr interp_atom]; symmetry.
        eapply constr_guard_complete with (row_ty := TRecord rt);
          [ exact H_Gs | exact H_Ge | exact H_wf
          | eapply unique_many_constr_wf; [ exact H_wf | exact HF ]
          | exact H_u | exact H_fv | exact H_store | exact H_env | ].
        rewrite E_u.
        eapply unique_many_constr_holds_filter;
          [ exact H_wf | exact Hnd | exact HF | exact H_l
          | apply H_inv; exact E_tbl ]. }
  Qed.

  Lemma decls_guard_agrees :
    forall ds row_ty free_vars tbl u (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      Forall (constr_wf row_ty) ds ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      (forall v, map.get store tbl = Some v ->
                 Forall (fun d => constr_holds d v) ds) ->
      interp_expr store env (decls_guard row_ty tbl free_vars ds u)
      = interp_expr store env
          (conj_guards ds free_vars u).
  Proof.
    induction ds as [ | d ds IH ]; intros * H_Gs H_Ge H_wf H_ds H_tbl H_u H_fv
      H_store H_env H_inv.
    1: reflexivity.
    invert_Forall.
    cbn [decls_guard conj_guards fold_right].
    rewrite !interp_EBinop.
    f_equal.
    1:{ eapply decl_guard_agrees with (row_ty := row_ty) (tbl := tbl)
                                      (free_vars := free_vars);
          [ exact H_Gs | exact H_Ge | exact H_wf | eassumption | exact H_tbl
          | exact H_u | exact H_fv | exact H_store | exact H_env
          | intros v H_v; specialize (H_inv v H_v); invert_Forall; assumption ]. }
    1:{ eapply IH with (row_ty := row_ty) (tbl := tbl) (free_vars := free_vars);
          [ exact H_Gs | exact H_Ge | exact H_wf | eassumption | exact H_tbl
          | exact H_u | exact H_fv | exact H_store | exact H_env
          | intros v H_v; specialize (H_inv v H_v); invert_Forall; assumption ]. }
  Qed.

  Corollary decls_guard_agrees_constrs :
    forall ds row_ty free_vars tbl u (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      Forall (constr_wf row_ty) ds ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      holds_for_all_entries
        (value_wf_with_globals (constrs_hold ds)
           (tbl :: nil)) store ->
      interp_expr store env (decls_guard row_ty tbl free_vars ds u)
      = interp_expr store env
          (conj_guards ds free_vars u).
  Proof.
    intros * H_Gs H_Ge H_wf H_ds H_tbl H_u H_fv H_store H_env H_inv.
    eapply decls_guard_agrees with (row_ty := row_ty) (tbl := tbl)
                                   (free_vars := free_vars);
      [ exact H_Gs | exact H_Ge | exact H_wf | exact H_ds | exact H_tbl
      | exact H_u | exact H_fv | exact H_store | exact H_env | ].
    intros v H_v. pose proof (H_inv tbl v H_v) as H_at.
    unfold value_wf_with_globals in H_at; invert_Forall.
    lazymatch goal with
      H: tbl <> tbl \/ _ |- _ => destruct H as [ H_ne | H_h ]; [ congruence | ]
    end.
    unfold constrs_hold in H_h.
    exact H_h.
  Qed.
End WithWord.
