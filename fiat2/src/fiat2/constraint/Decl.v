Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.constraint.PrimaryKeyCheck fiat2.constraint.CompositeKeyCheck
  fiat2.Utils fiat2.Substitute fiat2.TransfSound fiat2.constraint.Constraint fiat2.rules.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List Permutation.
Import ListNotations.

(* THE DECLARATION LANGUAGE: what a declared constraint is, what guard a write
   to a constrained table must pass, and the two theorems that make a
   class-specific guard safe.

   This file knows nothing about the surface language or about elaboration.
   See constraint/Surface.v for scommand and elab, the only consumer that
   assembles these guards into a program.  The split is what lets the index
   rules that need `decl` -- index/DictIndexKeyedDelete,
   index/CompositeDictKeyedDelete, index/CompositeKeyBucketDelete,
   index/DictBucketPkDelete, index/TrigramIndexUse -- depend on the
   declaration language without depending on the elaborator.

   TWO THEOREMS, doing two DIFFERENT jobs, and neither replaces the other:

     decl_guard_sound   the guard is strong ENOUGH -- a write that passes it
                        leaves every declared constraint standing.  One-sided.

     decl_guard_agrees  the guard is not TOO strong -- it evaluates to the
                        same boolean as the general whole-table constr_guard,
                        so the same writes are admitted and the same policy
                        branches are taken.

   Maintenance alone would be satisfied by a guard that rejects every write
   (the table never changes, so nothing is ever violated); only the second
   theorem rules that out.  Since the surface language has no semantics of its
   own, the second is also where preservation lives: not surface-to-target,
   which is unstatable, but target-to-target, with constr_guard as the
   reference. *)

(* A declared constraint, classified.

   constr is a boolean expression over a row and the table, which is the right
   notion to *mean* and the wrong notion to *match*: a transformation that
   wants to know whether a declaration is a primary key would have to compare
   expressions, and the language has no equality decider for them.  A
   declaration names its class instead, and constr_of_decl says what the class
   means.  DCheck is the general case, so nothing becomes inexpressible --
   every constr is constr_of_decl rt (DCheck (c_row k) (c_body k)) -- and a
   declaration written that way is simply one no rewrite recognizes, which
   costs an optimization and never soundness.

   The classes are chosen by what some rewrite can exploit, not by what can be
   written. *)
Inductive decl : Type :=
(* attr is a key: no two rows of the table agree on it *)
| DUnique (attr : string)
(* body holds of every row, and reads only the row it is given *)
| DRow (row : string) (body : expr)
(* row is the binder, body the predicate every row must satisfy *)
| DCheck (row : string) (body : expr)
(* attrs are a key TOGETHER: no two rows of the table agree on all of them.
   DUnique is its arity-one case up to the key being a one-field record, and
   is kept separate rather than replaced because the two are served by
   different indexes -- a key-to-row dictionary for one attribute, a
   composite dictionary for several.  Listed LAST so that no existing
   declaration's position in a destruct moves. *)
| DUniqueMany (attrs : list string).

Definition constr_of_decl (row_ty : type) (d : decl) : constr :=
  match d with
  | DUnique attr => unique_constr attr row_ty
  | DRow row body => mk_constr row body
  | DCheck row body => mk_constr row body
  | DUniqueMany attrs => unique_many_constr attrs row_ty
  end.

Definition constrs_of_decls (row_ty : type) (ds : list decl) : list constr :=
  List.map (constr_of_decl row_ty) ds.

(* The write shapes a class-specific guard can recognize.  A primary key's
   cheap test is equivalent to the quantifier only for a write that conses one
   row onto the table, so that shape is matched and anything else falls back on
   the general guard.  Matching it needs no expression equality -- only the
   constructors and the table's name. *)
Definition cons_onto (tbl : string) (e : expr) : option expr :=
  match e with
  | EBinop OCons row (ELoc tbl') => if String.eqb tbl tbl' then Some row else None
  | _ => None
  end.

(* The SAME single row, added at the END of the table.  This is the shape real
   code writes -- a Java ArrayList.add, a Python list.append -- and it gets the
   SAME guard as a cons, for a reason worth stating: a declared constraint is a
   property of WHICH ROWS the table holds, not of where a row sits in it, so
   the test that suffices for a cons suffices here. *)
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

   A row-removing write needs no test at all, for either recognized class: a
   row predicate and a key are both preserved when rows are dropped.  DCheck
   does not get this, and must not: its body may read the table, so what it
   says of a row can depend on which other rows are present. *)
Definition decl_guard (row_ty : type) (tbl : string) (free_vars : list string)
  (d : decl) (e : expr) : expr :=
  match d, classify_write tbl e with
  (* the two row-adding shapes get the SAME test: see snoc_onto *)
  | DUnique attr, WCons row | DUnique attr, WSnoc row =>
      unique_guard_let tbl attr row
  | DUniqueMany attrs, WCons row | DUniqueMany attrs, WSnoc row =>
      unique_many_guard_let tbl attrs row
  | DRow r b, WCons row | DRow r b, WSnoc row =>
      row_guard (mk_constr r b) free_vars row
  | DUnique _, WFilter _ _ | DUniqueMany _, WFilter _ _
  | DRow _ _, WFilter _ _ => EAtom (ABool true)
  | _, _ => constr_guard (constr_of_decl row_ty d) free_vars e
  end.

Fixpoint decls_guard (row_ty : type) (tbl : string) (free_vars : list string)
  (ds : list decl) (e : expr) : expr :=
  match ds with
  | nil => EAtom (ABool true)
  | d :: ds => EBinop OAnd (decl_guard row_ty tbl free_vars d e)
                 (decls_guard row_ty tbl free_vars ds e)
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

  (* What a declaration has to satisfy to be declarable, stated per class.
     The point of stating it per class rather than as constr_wf of its meaning
     is that the facts a class-specific guard needs are then available
     directly, instead of being recovered by inverting a typing derivation: a
     primary key needs its attribute to be a field of the row type, which is
     decidable and is checked once, where the declaration is written. *)
  Definition decl_wf (row_ty : type) (d : decl) : Prop :=
    match d with
    | DUnique attr =>
        exists rt kt, row_ty = TRecord rt /\ access_record rt attr = Success kt
    | DRow row body => row <> c_all /\ row_constr_wf row_ty (mk_constr row body)
    | DCheck row body => constr_wf row_ty (mk_constr row body)
    (* NoDup is what makes the key identify its attributes, and membership is
       what makes the conjunction typeable; both are decidable and checked
       once, where the declaration is written *)
    | DUniqueMany attrs =>
        exists rt, row_ty = TRecord rt
                   /\ NoDup attrs
                   /\ Forall (fun a => In a (List.map fst rt)) attrs
    end.

  Lemma decl_wf__constr_wf : forall row_ty d,
      type_wf row_ty -> decl_wf row_ty d ->
      constr_wf (tenv:=tenv) row_ty (constr_of_decl row_ty d).
  Proof.
    destruct d; cbn [constr_of_decl decl_wf]; intros H_wf H_d.
    1:{ destruct H_d as [ rt [ kt [ E_rt H_attr ] ] ]; subst.
        eapply unique_constr_wf; eauto. }
    1:{ destruct H_d as [ H_ne H_row ].
        apply row_constr_wf__constr_wf; assumption. }
    1: assumption.
    1:{ destruct H_d as [ rt [ E_rt [ Hnd HF ] ] ]; subst.
        eapply unique_many_constr_wf; [ exact H_wf | exact HF ]. }
  Qed.

  Lemma decls_wf__constrs_wf : forall row_ty ds,
      type_wf row_ty -> Forall (decl_wf row_ty) ds ->
      Forall (constr_wf (tenv:=tenv) row_ty) (constrs_of_decls row_ty ds).
  Proof.
    unfold constrs_of_decls; induction ds; cbn [List.map]; intros H_wf H_ds; auto.
    invert_Forall. constructor; auto using decl_wf__constr_wf.
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

  Lemma decl_guard_ty : forall row_ty d free_vars tbl u (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      decl_wf row_ty d ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      type_of Gstore Genv (decl_guard row_ty tbl free_vars d u) TBool.
  Proof.
    intros * H_Gs H_Ge H_wf H_d H_tbl H_u H_fv.
    unfold decl_guard.
    destruct d as [ attr | r b | r b | al ];
      destruct (classify_write tbl u) as [ row | row | y q | ] eqn:E_sh;
      cbn beta iota.
    (* the free guard, and every fallback on the general one *)
    all: lazymatch goal with
         | |- type_of _ _ (EAtom (ABool true)) _ => repeat constructor
         | |- type_of _ _ (constr_guard _ _ _) _ =>
             eapply constr_guard_ty; eauto using decl_wf__constr_wf
         | _ => idtac
         end.
    (* The cheap guards.  Each row-adding declaration has TWO goals, the cons
       and the append, interleaved by declaration.  Each append proof is its
       cons proof at the other shape: the guard is the same expression. *)
    (* a primary key, written by a cons onto the table *)
    1:{ destruct H_d as [ rt [ kt [ E_rt H_attr ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        eapply unique_guard_let_ty with (kt := kt).
        1: exact H_Gs. 1: exact H_Ge. 1: exact H_wf. 1: exact H_attr.
        1: exact H_tbl.
        1: eapply type_of_cons_inv; exact H_u. }
    (* ... and by an append onto it *)
    1:{ destruct H_d as [ rt [ kt [ E_rt H_attr ] ] ]; subst.
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        eapply unique_guard_let_ty with (kt := kt).
        1: exact H_Gs. 1: exact H_Ge. 1: exact H_wf. 1: exact H_attr.
        1: exact H_tbl.
        1: eapply type_of_snoc_inv; exact H_u. }
    (* a row constraint tests the row being written *)
    1:{ destruct H_d as [ H_ne H_row ].
        apply classify_write_cons in E_sh; subst.
        eapply row_guard_ty with (row_ty := row_ty).
        1: exact H_Gs. 1: exact H_Ge. 1: exact H_wf. 1: exact H_row.
        1: eapply type_of_cons_inv; exact H_u.
        1: exact H_fv. }
    1:{ destruct H_d as [ H_ne H_row ].
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        eapply row_guard_ty with (row_ty := row_ty).
        1: exact H_Gs. 1: exact H_Ge. 1: exact H_wf. 1: exact H_row.
        1: eapply type_of_snoc_inv; exact H_u.
        1: exact H_fv. }
    (* and the cheap guard for a COMPOSITE key, same shape and same place *)
    1:{ destruct H_d as [ rt [ E_rt [ Hnd HF ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        eapply unique_many_guard_let_ty.
        1: exact H_Gs. 1: exact H_Ge. 1: exact H_wf. 1: exact HF.
        1: exact H_tbl.
        1: eapply type_of_cons_inv; exact H_u. }
    1:{ destruct H_d as [ rt [ E_rt [ Hnd HF ] ] ]; subst.
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        eapply unique_many_guard_let_ty.
        1: exact H_Gs. 1: exact H_Ge. 1: exact H_wf. 1: exact HF.
        1: exact H_tbl.
        1: eapply type_of_snoc_inv; exact H_u. }
  Qed.

  Lemma decls_guard_ty : forall ds row_ty free_vars tbl u (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      Forall (decl_wf row_ty) ds ->
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
     filter of the table's.  Which rows it keeps does not matter -- only that
     it adds none. *)
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
     table, which is the extra hypothesis here and is exactly what PWCAssign's
     obligation receives. *)
  (* ------------------------------------------------------------------
     WHY AN APPEND GETS THE CONS'S GUARD.

     A declared constraint is a property of WHICH ROWS the table holds, so
     reordering them cannot change it.  That is not free -- constr_holds is a
     fold whose body may READ the table, which is exactly why DCheck gets no
     cheap guard -- so it is proved per declared form, through that form's own
     characterisation, each of which lands on a list-level predicate that a
     permutation preserves.
     ------------------------------------------------------------------ *)
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
    forall row_ty d free_vars tbl u (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      decl_wf row_ty d ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      (forall v, map.get store tbl = Some v ->
                 constr_holds (constr_of_decl row_ty d) v) ->
      interp_expr store env (decl_guard row_ty tbl free_vars d u) = VBool true ->
      constr_holds (constr_of_decl row_ty d) (interp_expr store env u).
  Proof.
    intros * H_Gs H_Ge H_wf H_d H_tbl H_u H_fv H_store H_env H_inv H_guard.
    unfold decl_guard in H_guard.
    destruct d as [ attr | r b | r b | al ];
      destruct (classify_write tbl u) as [ row | row | y q | ] eqn:E_sh;
      cbn beta iota in H_guard.
    (* every case that falls back on the general guard *)
    all: lazymatch type of H_guard with
         | interp_expr _ _ (constr_guard _ _ _) = _ =>
             eapply constr_guard_sound with (row_ty := row_ty) (free_vars := free_vars);
             [ exact H_Gs | exact H_Ge | exact H_wf
             | apply decl_wf__constr_wf; assumption
             | exact H_u | exact H_fv | exact H_store | exact H_env
             | exact H_guard ]
         | _ => idtac
         end.
    (* the cheap guard, for a key written by a cons onto the table *)
    1:{ destruct H_d as [ rt [ kt [ E_rt H_attr ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        cbn [constr_of_decl].
        (* the table's rows, and the uniqueness the invariant gives of them *)
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_key attr) l)).
        { eapply (proj1 (unique_constr_holds_iff attr rt kt l H_wf H_attr H_l)).
          cbn [constr_of_decl] in H_inv. apply H_inv; exact E_tbl. }
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
    (* THE SAME KEY, written by an APPEND.  The guard is the cons's guard, so
       the cons's reasoning establishes the constraint of the CONSED list and
       the permutation carries it to the appended one.  This is where "a
       constraint is a property of which rows the table holds" is paid for. *)
    1:{ destruct H_d as [ rt [ kt [ E_rt H_attr ] ] ]; subst.
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        cbn [constr_of_decl].
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_key attr) l)).
        { eapply (proj1 (unique_constr_holds_iff attr rt kt l H_wf H_attr H_l)).
          cbn [constr_of_decl] in H_inv. apply H_inv; exact E_tbl. }
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
    1:{ destruct H_d as [ rt [ kt [ E_rt H_attr ] ] ]; subst.
        cbn [constr_of_decl] in H_inv |- *.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        destruct (classify_write_filter_interp tbl u y q store env l E_sh E_tbl)
          as [ g E_u ].
        rewrite E_u.
        eapply unique_constr_holds_filter;
          [ exact H_wf | exact H_attr | exact H_l | apply H_inv; exact E_tbl ]. }
    (* a row constraint: its guard is the declared guard, by
       row_split_guard_sound, so the declared guard passed too *)
    1:{ destruct H_d as [ H_ne H_row ].
        apply classify_write_cons in E_sh; subst.
        cbn [constr_of_decl] in H_inv |- *.
        destruct (locals_wf_list Gstore store tbl row_ty H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_at : constr_holds (mk_constr r b) (get_local store tbl))
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
    1:{ destruct H_d as [ H_ne H_row ].
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        cbn [constr_of_decl] in H_inv |- *.
        destruct (locals_wf_list Gstore store tbl row_ty H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_at : constr_holds (mk_constr r b) (get_local store tbl))
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
    1:{ destruct H_d as [ H_ne H_row ].
        cbn [constr_of_decl] in H_inv |- *.
        destruct (locals_wf_list Gstore store tbl row_ty H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        destruct (classify_write_filter_interp tbl u y q store env l E_sh E_tbl)
          as [ g E_u ].
        rewrite E_u.
        eapply row_constr_holds_filter;
          [ exact H_wf | exact H_ne | exact H_row | exact H_l
          | apply H_inv; exact E_tbl ]. }
    (* the cheap guard for a COMPOSITE key written by a cons *)
    1:{ destruct H_d as [ rt [ E_rt [ Hnd HF ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        cbn [constr_of_decl].
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_keys al) l)).
        { eapply (proj1 (unique_many_constr_holds_iff al rt l H_wf Hnd HF H_l)).
          cbn [constr_of_decl] in H_inv. apply H_inv; exact E_tbl. }
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
    1:{ destruct H_d as [ rt [ E_rt [ Hnd HF ] ] ]; subst.
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        cbn [constr_of_decl].
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_keys al) l)).
        { eapply (proj1 (unique_many_constr_holds_iff al rt l H_wf Hnd HF H_l)).
          cbn [constr_of_decl] in H_inv. apply H_inv; exact E_tbl. }
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
    1:{ destruct H_d as [ rt [ E_rt [ Hnd HF ] ] ]; subst.
        cbn [constr_of_decl] in H_inv |- *.
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
      Forall (decl_wf row_ty) ds ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      (forall v, map.get store tbl = Some v ->
                 Forall (fun d => constr_holds (constr_of_decl row_ty d) v) ds) ->
      interp_expr store env (decls_guard row_ty tbl free_vars ds u) = VBool true ->
      Forall (fun d => constr_holds (constr_of_decl row_ty d)
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
      Forall (decl_wf row_ty) ds ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      holds_for_all_entries
        (value_wf_with_globals (constrs_hold (constrs_of_decls row_ty ds))
           (tbl :: nil)) store ->
      interp_expr store env (decls_guard row_ty tbl free_vars ds u) = VBool true ->
      constrs_hold (constrs_of_decls row_ty ds) (interp_expr store env u).
  Proof.
    unfold constrs_hold, constrs_of_decls; intros * H_Gs H_Ge H_wf H_ds H_tbl H_u
      H_fv H_store H_env H_inv H_guard.
    apply (proj2 (Forall_map _ _ _)).
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
        unfold constrs_hold, constrs_of_decls in H_h.
        exact (proj1 (Forall_map _ _ _) H_h). }
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
  (* The general guard's value is a function of the WRITTEN VALUE alone
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
    forall row_ty d free_vars tbl u (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      decl_wf row_ty d ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      (forall v, map.get store tbl = Some v ->
                 constr_holds (constr_of_decl row_ty d) v) ->
      interp_expr store env (decl_guard row_ty tbl free_vars d u)
      = interp_expr store env
          (constr_guard (constr_of_decl row_ty d) free_vars u).
  Proof.
    intros * H_Gs H_Ge H_wf H_d H_tbl H_u H_fv H_store H_env H_inv.
    unfold decl_guard.
    destruct d as [ attr | r b | r b | al ];
      destruct (classify_write tbl u) as [ row | row | y q | ] eqn:E_sh;
      cbn beta iota.
    (* every case that emits the general guard already *)
    all: try reflexivity.
    (* a key written by a cons onto the table *)
    1:{ destruct H_d as [ rt [ kt [ E_rt H_attr ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_key attr) l)).
        { eapply (proj1 (unique_constr_holds_iff attr rt kt l H_wf H_attr H_l)).
          cbn [constr_of_decl] in H_inv. apply H_inv; exact E_tbl. }
        eapply unique_guard_let_sound with (kt := kt) (l := l);
          [ exact H_Gs | exact H_Ge | exact H_wf | exact H_attr | exact H_tbl
          | eapply type_of_cons_inv; exact H_u | exact H_fv | exact H_store
          | exact H_env | exact E_tbl | exact H_nd ]. }
    (* THE SAME KEY at an APPEND.  The cheap guard agrees with the general
       guard at the CONS by the case above, and the general guard depends only
       on the written VALUE, so the permutation carries the agreement across. *)
    1:{ destruct H_d as [ rt [ kt [ E_rt H_attr ] ] ]; subst.
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        cbn [constr_of_decl].
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_key attr) l)).
        { eapply (proj1 (unique_constr_holds_iff attr rt kt l H_wf H_attr H_l)).
          cbn [constr_of_decl] in H_inv. apply H_inv; exact E_tbl. }
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
    1:{ destruct H_d as [ rt [ kt [ E_rt H_attr ] ] ]; subst.
        cbn [constr_of_decl] in H_inv |- *.
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
    1:{ destruct H_d as [ H_ne H_row ].
        apply classify_write_cons in E_sh; subst.
        cbn [constr_of_decl] in H_inv |- *.
        destruct (locals_wf_list Gstore store tbl row_ty H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        symmetry.
        eapply row_split_guard_sound with (row_ty := row_ty);
          [ exact H_Gs | exact H_Ge | exact H_wf | exact H_ne | exact H_row
          | exact H_tbl | eapply type_of_cons_inv; exact H_u | exact H_fv
          | exact H_store | exact H_env
          | unfold get_local; rewrite E_tbl; apply H_inv; exact E_tbl ]. }
    (* the row predicate at an APPEND *)
    1:{ destruct H_d as [ H_ne H_row ].
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        cbn [constr_of_decl] in H_inv |- *.
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
                        (constr_guard (mk_constr r b)
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
    1:{ destruct H_d as [ H_ne H_row ].
        cbn [constr_of_decl] in H_inv |- *.
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
    (* a COMPOSITE key written by a cons onto the table *)
    1:{ destruct H_d as [ rt [ E_rt [ Hnd HF ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_keys al) l)).
        { eapply (proj1 (unique_many_constr_holds_iff al rt l H_wf Hnd HF H_l)).
          cbn [constr_of_decl] in H_inv. apply H_inv; exact E_tbl. }
        eapply unique_many_guard_let_sound with (l := l);
          [ exact H_Gs | exact H_Ge | exact H_wf | exact Hnd | exact HF
          | exact H_tbl | eapply type_of_cons_inv; exact H_u | exact H_fv
          | exact H_store | exact H_env | exact E_tbl | exact H_nd ]. }
    (* the composite key at an APPEND *)
    1:{ destruct H_d as [ rt [ E_rt [ Hnd HF ] ] ]; subst.
        apply classify_write_snoc in E_sh; destruct E_sh as [ ta E_sh ]; subst.
        cbn [constr_of_decl].
        destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
          as [ l [ E_tbl H_l ] ].
        assert (H_nd : NoDup (List.map (row_keys al) l)).
        { eapply (proj1 (unique_many_constr_holds_iff al rt l H_wf Hnd HF H_l)).
          cbn [constr_of_decl] in H_inv. apply H_inv; exact E_tbl. }
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
    1:{ destruct H_d as [ rt [ E_rt [ Hnd HF ] ] ]; subst.
        cbn [constr_of_decl] in H_inv |- *.
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
      Forall (decl_wf row_ty) ds ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      (forall v, map.get store tbl = Some v ->
                 Forall (fun d => constr_holds (constr_of_decl row_ty d) v) ds) ->
      interp_expr store env (decls_guard row_ty tbl free_vars ds u)
      = interp_expr store env
          (conj_guards (constrs_of_decls row_ty ds) free_vars u).
  Proof.
    induction ds as [ | d ds IH ]; intros * H_Gs H_Ge H_wf H_ds H_tbl H_u H_fv
      H_store H_env H_inv.
    1: reflexivity.
    invert_Forall.
    cbn [decls_guard constrs_of_decls List.map conj_guards fold_right].
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
      Forall (decl_wf row_ty) ds ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      holds_for_all_entries
        (value_wf_with_globals (constrs_hold (constrs_of_decls row_ty ds))
           (tbl :: nil)) store ->
      interp_expr store env (decls_guard row_ty tbl free_vars ds u)
      = interp_expr store env
          (conj_guards (constrs_of_decls row_ty ds) free_vars u).
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
    unfold constrs_hold, constrs_of_decls in H_h.
    exact (proj1 (Forall_map _ _ _) H_h).
  Qed.
End WithWord.
