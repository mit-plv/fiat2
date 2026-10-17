Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.PrimaryKeyCheck
  fiat2.Utils fiat2.Substitute fiat2.TransfSound fiat2.Constraint fiat2.FlatmapForms.
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
| DCheck (row : string) (body : expr).

Definition constr_of_decl (row_ty : type) (d : decl) : constr :=
  match d with
  | DUnique attr => unique_constr attr row_ty
  | DRow row body => mk_constr row body
  | DCheck row body => mk_constr row body
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
(* adds exactly one row, leaving the rest of the table *)
| WCons (row : expr)
(* removes rows and adds none *)
| WFilter (x : string) (p : expr)
(* anything else *)
| WOther.

Definition classify_write (tbl : string) (e : expr) : write_shape :=
  match cons_onto tbl e with
  | Some row => WCons row
  | None =>
      match filter_of tbl e with
      | Some (x, p) => WFilter x p
      | None => WOther
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
  | DUnique attr, WCons row => unique_guard_let tbl attr row
  | DRow r b, WCons row => row_guard (mk_constr r b) free_vars row
  | DUnique _, WFilter _ _ | DRow _ _, WFilter _ _ => EAtom (ABool true)
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

Lemma classify_write_cons : forall tbl e row,
    classify_write tbl e = WCons row -> e = EBinop OCons row (ELoc tbl).
Proof.
  unfold classify_write; intros * H.
  destruct (cons_onto tbl e) as [ r | ] eqn:E.
  1:{ injection H as H; subst. apply cons_onto_eq; exact E. }
  1: destruct (filter_of tbl e) as [ [ ] | ]; discriminate.
Qed.

Lemma classify_write_filter : forall tbl e x p,
    classify_write tbl e = WFilter x p ->
    exists t1 t2, e = flatmap_filter_list (ELoc tbl) x p x t1 t2.
Proof.
  unfold classify_write; intros * H.
  destruct (cons_onto tbl e); try discriminate.
  destruct (filter_of tbl e) as [ [ y q ] | ] eqn:E; try discriminate.
  injection H as H1 H2; subst. apply filter_of_eq; exact E.
Qed.

Inductive scommand : Type :=
| SSkip
| SSeq (c1 c2 : scommand)
| SLet (e : expr) (x : string) (c : scommand)
| SLetMut (e : expr) (x : string) (c : scommand)
(* x is born empty, holds rows of row_ty, and every constraint in ks must hold
   of it for as long as it is in scope *)
| SLetConstrained (x : string) (row_ty : type) (ds : list decl) (c : scommand)
(* policy is what runs instead of the write when a constraint would break; it
   is dead syntax when x carries no constraint *)
| SAssign (x : string) (e : expr) (policy : scommand)
| SIf (e : expr) (c1 c2 : scommand)
| SForeach (e : expr) (x : string) (c : scommand).

(* Which constraints are in force on which variable.  Entries are added by a
   declaration and removed when the variable is shadowed, so a write is checked
   against exactly the constraints that are standing where it occurs. *)
Definition cenv : Type := list (string * (type * list decl)).

Fixpoint cenv_lookup (x : string) (ce : cenv) : option (type * list decl) :=
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
  | SLetConstrained x row_ty ds c =>
      CLetMut (EAtom (ANil (Some row_ty))) x
        (elab ((x, (row_ty, ds)) :: cenv_rm x ce) free_vars c)
  | SAssign x e policy =>
      match cenv_lookup x ce with
      | None => CAssign x e
      | Some (row_ty, ds) =>
          CIf (decls_guard row_ty x free_vars ds e)
            (CAssign x e) (elab ce free_vars policy)
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
  Qed.

  Lemma decls_wf__constrs_wf : forall row_ty ds,
      type_wf row_ty -> Forall (decl_wf row_ty) ds ->
      Forall (constr_wf (tenv:=tenv) row_ty) (constrs_of_decls row_ty ds).
  Proof.
    unfold constrs_of_decls; induction ds; cbn [List.map]; intros H_wf H_ds; auto.
    invert_Forall. constructor; auto using decl_wf__constr_wf.
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
    destruct d as [ attr | r b | r b ];
      destruct (classify_write tbl u) as [ row | y q | ] eqn:E_sh;
      cbn beta iota.
    (* the free guard, and every fallback on the general one *)
    all: lazymatch goal with
         | |- type_of _ _ (EAtom (ABool true)) _ => repeat constructor
         | |- type_of _ _ (constr_guard _ _ _) _ =>
             eapply constr_guard_ty; eauto using decl_wf__constr_wf
         | _ => idtac
         end.
    (* the cheap guard, for a primary key written by a cons onto the table *)
    1:{ destruct H_d as [ rt [ kt [ E_rt H_attr ] ] ]; subst.
        apply classify_write_cons in E_sh; subst.
        eapply unique_guard_let_ty with (kt := kt).
        1: exact H_Gs.
        1: exact H_Ge.
        1: exact H_wf.
        1: exact H_attr.
        1: exact H_tbl.
        1: eapply type_of_cons_inv; exact H_u. }
    (* a row constraint tests the row being written *)
    1:{ destruct H_d as [ H_ne H_row ].
        apply classify_write_cons in E_sh; subst.
        eapply row_guard_ty with (row_ty := row_ty).
        1: exact H_Gs.
        1: exact H_Ge.
        1: exact H_wf.
        1: exact H_row.
        1: eapply type_of_cons_inv; exact H_u.
        1: exact H_fv. }
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
    destruct d as [ attr | r b | r b ];
      destruct (classify_write tbl u) as [ row | y q | ] eqn:E_sh;
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
  Qed.

  (* The same, for the conjunction a declaration's whole list elaborates to.
     ds leads the quantifiers so that the induction's hypothesis is general. *)
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
    destruct d as [ attr | r b | r b ];
      destruct (classify_write tbl u) as [ row | y q | ] eqn:E_sh;
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

  Lemma checked_assign_wf_decls :
    forall row_ty ds free_vars tbl u policy (A : locals -> locals -> Prop)
           (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      Forall (decl_wf row_ty) ds ->
      map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore Genv u (TList row_ty) ->
      incl (get_free_vars Genv) free_vars ->
      parameterized_wf Gstore Genv
        (value_wf_with_globals (constrs_hold (constrs_of_decls row_ty ds))
           (tbl :: nil)) A policy ->
      parameterized_wf Gstore Genv
        (value_wf_with_globals (constrs_hold (constrs_of_decls row_ty ds))
           (tbl :: nil)) A
        (CIf (decls_guard row_ty tbl free_vars ds u) (CAssign tbl u) policy).
  Proof.
    intros * H_Gs H_Ge H_wf H_ds H_tbl H_u H_fv H_pol.
    econstructor.
    1: eapply decls_guard_ty with (row_ty := row_ty); eauto.
    1:{ econstructor.
        2: exact H_tbl.
        2: exact H_u.
        intros * [ H_A H_guard ] H_inv H_store H_env.
        unfold value_wf_with_globals; constructor; [ | constructor ]. right.
        eapply decls_guard_sound_constrs with (row_ty := row_ty) (tbl := tbl)
                                              (free_vars := free_vars);
          [ exact H_Gs | exact H_Ge | exact H_wf | exact H_ds | exact H_tbl
          | exact H_u | exact H_fv | exact H_store | exact H_env
          | exact H_inv | exact H_guard ]. }
    1:{ eapply parameterized_wf_weaken; [ | exact H_pol ].
        intros * ? ? ? [? ?]; auto. }
  Qed.

  (* Elaboration keeps every constraint declared on tbl standing, at every
     point of the program.  The theorem is about a tbl already in the store's
     type environment, which is where the body of a declaration starts; the
     declaration itself supplies the base case, since the variable is born
     empty (constrs_declared). *)
  Theorem elab_constr_wf :
    forall sc ce free_vars (Gstore Genv : tenv) tbl row_ty ds
           (A : locals -> locals -> Prop),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      incl (get_free_vars Genv) free_vars ->
      map.get Gstore tbl = Some (TList row_ty) ->
      Forall (decl_wf row_ty) ds ->
      cenv_lookup tbl ce = Some (row_ty, ds) ->
      well_typed Gstore Genv (elab ce free_vars sc) ->
      parameterized_wf Gstore Genv
        (value_wf_with_globals (constrs_hold (constrs_of_decls row_ty ds))
           (tbl :: nil)) A
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
    1:{ destruct (cenv_lookup x ce) as [ [ row_ty' ds' ] | ] eqn:E_look;
          invert_well_typed.
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
            rewrite H_ce in E_look; symmetry in E_look.
            injection E_look as H_rt' H_ds'; subst.
            eapply checked_assign_wf_decls with (row_ty := row_ty); eauto.
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
    forall sc free_vars (Gstore Genv : tenv) (store env : locals) tbl row_ty ds,
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      incl (get_free_vars Genv) free_vars ->
      map.get Gstore tbl = Some (TList row_ty) ->
      Forall (decl_wf row_ty) ds ->
      well_typed Gstore Genv (elab ((tbl, (row_ty, ds)) :: nil) free_vars sc) ->
      locals_wf Gstore (map.put store tbl (VList nil)) -> locals_wf Genv env ->
      holds_for_all_entries
        (value_wf_with_globals (constrs_hold (constrs_of_decls row_ty ds))
           (tbl :: nil))
        (interp_command (map.put store tbl (VList nil)) env
           (elab ((tbl, (row_ty, ds)) :: nil) free_vars sc)).
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
