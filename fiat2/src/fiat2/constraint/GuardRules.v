Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.TransfSound fiat2.Invariant fiat2.rules.FlatmapForms fiat2.constraint.KeyCheck.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String List Permutation.
Import ListNotations.
Local Open Scope bool_scope.

(* Rewrites of the general guard elaboration emits for a ConstraintInv on the
   written table, at a write that adds one row or only removes rows.  Each is
   equal to the general guard in a store where the invariant context holds.

   - a condition that does not read the table is tested on the added row only,
     and needs no test for a removing write;
   - a key is tested by a lookup of the added row's key, and needs no test for
     a removing write. *)

Definition cons_onto (tbl : string) (e : expr) : option expr :=
  match e with
  | EBinop OCons row (ELoc tbl') => if String.eqb tbl tbl' then Some row else None
  | _ => None
  end.

Definition snoc_onto (tbl : string) (e : expr) : option expr :=
  match e with
  | EBinop OConcat (ELoc tbl') (EBinop OCons row (EAtom (ANil _))) =>
      if String.eqb tbl tbl' then Some row else None
  | _ => None
  end.

Definition filter_of (tbl : string) (e : expr) : option (string * expr) :=
  match e with
  | EFlatmap LikeList (ELoc tbl') x
      (EIf p (EBinop OCons (EVar y) (EAtom (ANil _))) (EAtom (ANil _))) =>
      if String.eqb tbl tbl' && String.eqb x y then Some (x, p) else None
  | _ => None
  end.

Inductive write_shape : Type :=
| WCons (row : expr)
| WSnoc (row : expr)
| WFilter (x : string) (p : expr)
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

Definition unique_candidate (cond : expr) : option (list string) :=
  match cond with
  | EBinop OEq (EUnop OLength (EFlatmap _ _ _ (EIf c _ _))) _ => Some (attrs_of_conj c)
  | _ => None
  end.

(* The key a constraint declares, if it is one *)
Definition key_of (row_ty : type) (tbl row : string) (cond : expr) : option (list string) :=
  match row_ty with
  | TRecord rt =>
      match unique_candidate cond with
      | Some attrs =>
          if String.eqb row "_r" && expr_eqb (erase_annot cond) (erase_annot (unique_cond tbl attrs row_ty))
             && nodupb attrs && forallb (fun a => existsb (String.eqb a) (List.map fst rt)) attrs
          then Some attrs else None
      | None => None
      end
  | _ => None
  end.

Definition cheap_guard (row_ty : type) (tbl row : string) (cond e : expr) : option expr :=
  match classify_write tbl e with
  | WCons r | WSnoc r =>
      if loc_in tbl cond
      then option_map (fun attrs => unique_guard_let tbl attrs r) (key_of row_ty tbl row cond)
      else Some (ELet r row cond)
  | WFilter _ _ =>
      if loc_in tbl cond
      then option_map (fun _ => EAtom (ABool true)) (key_of row_ty tbl row cond)
      else Some (EAtom (ABool true))
  | WOther => None
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

Lemma filter_of_eq : forall tbl e x p,
    filter_of tbl e = Some (x, p) ->
    exists t1 t2, e = flatmap_filter_list (ELoc tbl) x p x t1 t2.
Proof.
  unfold filter_of; intros * H.
  repeat lazymatch type of H with
    | (match ?y with _ => _ end) = _ => destruct y eqn:?; try discriminate
    end.
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

Lemma nodupb_NoDup : forall l, nodupb l = true -> NoDup l.
Proof.
  induction l as [ | a l IH ]; cbn; intro H; [ constructor | ].
  apply andb_prop in H as [ H1 H2 ]. constructor; [ | auto ].
  intro H_in. apply Bool.negb_true_iff in H1.
  assert (existsb (String.eqb a) l = true)
    by (apply existsb_exists; exists a; split; [ exact H_in | apply String.eqb_refl ]).
  congruence.
Qed.

Lemma key_of_sound : forall row_ty tbl row cond attrs,
    key_of row_ty tbl row cond = Some attrs ->
    exists rt, row_ty = TRecord rt /\ row = "_r" /\ erase_annot cond = erase_annot (unique_cond tbl attrs row_ty)
               /\ NoDup attrs /\ Forall (fun a => In a (List.map fst rt)) attrs.
Proof.
  unfold key_of; intros * H.
  destruct row_ty; try discriminate.
  destruct (unique_candidate cond) as [ al | ]; try discriminate.
  lazymatch type of H with
  | (if ?b then _ else _) = _ => destruct b eqn:E; try discriminate
  end.
  injection H as <-. rewrite !Bool.andb_true_iff in E.
  destruct E as [ [ [ E1 E2 ] E3 ] E4 ].
  apply String.eqb_eq in E1. apply expr_eqb_true in E2.
  exists l; repeat split; auto using nodupb_NoDup.
  apply Forall_forall; intros a H_in.
  rewrite forallb_forall in E4. apply E4 in H_in.
  apply existsb_exists in H_in as [ a' [ H_in E5 ] ].
  apply String.eqb_eq in E5; subst; exact H_in.
Qed.

Section WithMap.
  Notation value := (value).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Definition cheap_for (Gstore : tenv) (e g : expr) (i : invariant) : option expr :=
    match i with
    | ConstraintInv tbl nil row cond =>
        if expr_eqb (erase_annot g) (erase_annot (inv_guard tbl e i)) then
          match map.get Gstore tbl with
          | Some (TList row_ty) => cheap_guard row_ty tbl row cond e
          | _ => None
          end
        else None
    | _ => None
    end.

  Fixpoint find_cheap (Gstore : tenv) (e g : expr) (ictx : list invariant) : option expr :=
    match ictx with
    | nil => None
    | i :: ictx =>
        match cheap_for Gstore e g i with
        | Some g' => Some g'
        | None => find_cheap Gstore e g ictx
        end
    end.

  Definition guard_rule (ictx : list invariant) (Gstore : tenv) (g : expr) : expr :=
    match g with
    | ELet e _ _ =>
        match find_cheap Gstore e g ictx with
        | Some g' => g'
        | None => g
        end
    | _ => g
    end.

  Lemma find_cheap_spec : forall Gstore e g ictx g',
      find_cheap Gstore e g ictx = Some g' ->
      exists i, In i ictx /\ cheap_for Gstore e g i = Some g'.
  Proof.
    induction ictx as [ | i ictx IH ]; cbn; intros g' H; [ discriminate | ].
    destruct (cheap_for Gstore e g i) eqn:E.
    1: injection H as <-; eauto.
    1: apply IH in H as [ i' [ ? ? ] ]; eauto.
  Qed.

  Lemma cheap_for_spec : forall Gstore e g i g',
      cheap_for Gstore e g i = Some g' ->
      exists tbl row cond row_ty,
        i = ConstraintInv tbl nil row cond /\ erase_annot g = erase_annot (inv_guard tbl e i) /\
          map.get Gstore tbl = Some (TList row_ty) /\ cheap_guard row_ty tbl row cond e = Some g'.
  Proof.
    unfold cheap_for; intros * H.
    destruct i as [ tbl [ | ] row cond | ]; try discriminate.
    destruct (expr_eqb (erase_annot g) _) eqn:E; try discriminate. apply expr_eqb_true in E.
    destruct (map.get Gstore tbl) as [ [] | ] eqn:E_t; try discriminate.
    do 4 eexists; split; [ reflexivity | split; [ exact E | split; eassumption ] ].
  Qed.

  Lemma inv_holds_erase : forall tbl path row cond cond' (store : locals),
      erase_annot cond = erase_annot cond' ->
      inv_holds store (ConstraintInv tbl path row cond) <-> inv_holds store (ConstraintInv tbl path row cond').
  Proof.
    intros * E. cbn [inv_holds].
    destruct (map.get store tbl) as [ v | ]; [ | reflexivity ].
    destruct (value_at v path) as [ [] | ]; try reflexivity.
    split; apply Forall_impl; intros r H_r.
    all: rewrite <- interp_erase_annot in *; rewrite E in *; rewrite interp_erase_annot in *; exact H_r.
  Qed.

  Lemma guard_ty_bool : forall (Gstore Genv : tenv) tbl e x g2 row cond t,
      type_of Gstore Genv (ELet e x g2) t ->
      erase_annot (ELet e x g2) = erase_annot (inv_guard tbl e (ConstraintInv tbl nil row cond)) ->
      t = TBool /\ exists te, type_of Gstore Genv e te.
  Proof.
    intros * H H_er. cbn [inv_guard] in H_er. rewrite eqb_refl in H_er.
    destruct g2; cbn [access_path erase_annot] in H_er; try discriminate H_er.
    lazymatch type of H with
    | type_of _ _ (ELet _ _ (EFold _ ?i _ _ _)) _ => destruct i; cbn [erase_annot] in H_er; try discriminate H_er
    end.
    lazymatch type of H with
    | type_of _ _ (ELet _ _ (EFold _ (EAtom ?a) _ _ _)) _ => destruct a; cbn [erase_atom] in H_er; try discriminate H_er
    end.
    inversion H; subst.
    lazymatch goal with H : type_of _ _ (EFold _ _ _ _ _) _ |- _ => inversion H; subst end.
    lazymatch goal with H : type_of _ _ (EAtom _) _ |- _ => inversion H; subst end.
    lazymatch goal with H : type_of_atom _ _ |- _ => inversion H; subst end.
    eauto.
  Qed.

  Lemma classify_write_ty : forall (Gstore Genv : tenv) tbl e te row_ty,
      map.get Gstore tbl = Some (TList row_ty) ->
      classify_write tbl e <> WOther ->
      type_of Gstore Genv e te -> te = TList row_ty.
  Proof.
    intros * H_tbl H_w H_e.
    destruct (classify_write tbl e) eqn:E; [ | | | congruence ].
    1:{ apply classify_write_cons in E; subst.
        inversion H_e; subst.
        lazymatch goal with H : type_of_binop OCons _ _ _ |- _ => inversion H; subst end.
        lazymatch goal with H : type_of _ _ (ELoc _) _ |- _ => inversion H; subst end.
        congruence. }
    1:{ apply classify_write_snoc in E as [ t E ]; subst.
        inversion H_e; subst.
        lazymatch goal with H : type_of_binop OConcat _ _ _ |- _ => inversion H; subst end.
        lazymatch goal with H : type_of _ _ (ELoc _) _ |- _ => inversion H; subst end.
        congruence. }
    1:{ apply classify_write_filter in E as [ t1 [ t2 E ] ]; subst.
        inversion H_e; subst.
        lazymatch goal with H : type_of _ _ (ELoc _) _ |- _ => inversion H; subst end.
        lazymatch goal with H : type_of _ _ (EIf _ _ _) _ |- _ => inversion H; subst end.
        lazymatch goal with H : type_of _ _ (EBinop OCons _ _) _ |- _ => inversion H; subst end.
        lazymatch goal with H : type_of_binop OCons _ _ _ |- _ => inversion H; subst end.
        lazymatch goal with H : type_of _ _ (EVar _) _ |- _ => inversion H; subst end.
        rewrite map.get_put_same in *. congruence. }
  Qed.

  Lemma classify_write_row_ty : forall (Gstore Genv : tenv) tbl e r t,
      classify_write tbl e = WCons r \/ classify_write tbl e = WSnoc r ->
      type_of Gstore Genv e (TList t) -> type_of Gstore Genv r t.
  Proof.
    intros * [ E | E ] H_e.
    1:{ apply classify_write_cons in E; subst.
        inversion H_e; subst.
        lazymatch goal with H : type_of_binop OCons _ _ _ |- _ => inversion H; subst end.
        assumption. }
    1:{ apply classify_write_snoc in E as [ ta E ]; subst.
        inversion H_e; subst.
        lazymatch goal with H : type_of_binop OConcat _ _ _ |- _ => inversion H; subst end.
        lazymatch goal with H : type_of _ _ (EBinop OCons _ _) _ |- _ => inversion H; subst end.
        lazymatch goal with H : type_of_binop OCons _ _ _ |- _ => inversion H; subst end.
        assumption. }
  Qed.

  Lemma cheap_guard_not_other : forall row_ty tbl row cond e g',
      cheap_guard row_ty tbl row cond e = Some g' -> classify_write tbl e <> WOther.
  Proof.
    unfold cheap_guard; intros * H E. rewrite E in H. discriminate.
  Qed.

  Lemma tenv_wf_singleton : forall x t, type_wf t -> tenv_wf (map.put (map.empty : tenv) x t).
  Proof.
    intros x t H_t. apply tenv_wf_step; [ | exact H_t ].
    intros y ty H. rewrite map.get_empty in H. discriminate.
  Qed.

  Lemma interp_ELet_row : forall (Gstore : tenv) row row_ty cond r (store env : locals),
      tenv_wf Gstore -> type_wf row_ty ->
      type_of Gstore (map.put map.empty row row_ty) cond TBool ->
      locals_wf Gstore store -> type_of_value (interp_expr store env r) row_ty ->
      interp_expr store env (ELet r row cond)
      = interp_expr store (map.put map.empty row (interp_expr store env r)) cond.
  Proof.
    intros * H_Gs H_rt H_cond H_store H_v. rewrite interp_ELet.
    eapply interp_expr__locals_equiv.
    1: exact H_Gs.
    1: apply tenv_wf_singleton; exact H_rt.
    1: exact H_cond.
    1: exact H_store.
    1:{ apply locals_wf_step; [ | exact H_v ].
        intros y ty H. rewrite map.get_empty in H. discriminate. }
    1: apply locals_equiv_refl.
    1:{ intros y ty H. destruct (String.eqb y row) eqn:E; rewrite ?eqb_eq, ?eqb_neq in E; subst.
        1: rewrite !map.get_put_same; reflexivity.
        1: rewrite map.get_put_diff, map.get_empty in H by exact E; discriminate. }
  Qed.

  Lemma cheap_guard_ty : forall (Gstore Genv : tenv) tbl row cond e g' row_ty,
      tenv_wf Gstore -> tenv_wf Genv -> map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore (map.put map.empty row row_ty) cond TBool ->
      type_of Gstore Genv e (TList row_ty) ->
      cheap_guard row_ty tbl row cond e = Some g' ->
      type_of Gstore Genv g' TBool.
  Proof.
    intros * H_Gs H_Ge H_tbl H_cond H_e H_c.
    assert (H_rt : type_wf row_ty)
      by (apply H_Gs in H_tbl; inversion H_tbl; assumption).
    unfold cheap_guard in H_c.
    destruct (classify_write tbl e) as [ r | r | x p | ] eqn:E_w; try discriminate.
    3:{ destruct (loc_in tbl cond).
        1: destruct (key_of row_ty tbl row cond); cbn [option_map] in H_c; try discriminate.
        all: injection H_c as <-; repeat constructor. }
    all: assert (H_r : type_of Gstore Genv r row_ty)
      by (eapply classify_write_row_ty; [ first [ left; exact E_w | right; exact E_w ] | exact H_e ]).
    all: destruct (loc_in tbl cond).
    2,4: injection H_c as <-; econstructor; [ exact H_r | ];
         eapply type_of_strengthen; [ exact H_cond | apply map_incl_refl | ];
         apply (map_incl_step string_dec); apply map_incl_empty.
    all: destruct (key_of row_ty tbl row cond) as [ attrs | ] eqn:E_k; cbn [option_map] in H_c;
         try discriminate; injection H_c as <-;
         apply key_of_sound in E_k as [ rt [ -> [ _ [ _ [ _ HF ] ] ] ] ];
         eapply unique_guard_let_ty; eauto.
  Qed.

  Lemma inv_holds_nil_iff : forall tbl row cond (store : locals) l,
      map.get store tbl = Some (VList l) ->
      inv_holds store (ConstraintInv tbl nil row cond)
      <-> Forall (fun r => interp_expr store (map.put map.empty row r) cond = VBool true) l.
  Proof.
    intros * E. cbn [inv_holds value_at]. rewrite E. reflexivity.
  Qed.

  Lemma row_only_holds_iff : forall tbl row cond (store : locals) rows,
      loc_in tbl cond = false ->
      inv_holds (map.put store tbl (VList rows)) (ConstraintInv tbl nil row cond)
      <-> Forall (fun r => interp_expr store (map.put map.empty row r) cond = VBool true) rows.
  Proof.
    intros * H_loc. rewrite inv_holds_nil_iff by apply map.get_put_same.
    split; apply Forall_impl; intros r H_r.
    1: rewrite loc_in_false_sem in H_r by exact H_loc; exact H_r.
    1: rewrite loc_in_false_sem by exact H_loc; exact H_r.
  Qed.

  Lemma interp_write : forall tbl e (store env : locals) l,
      map.get store tbl = Some (VList l) ->
      (forall r, classify_write tbl e = WCons r ->
                 interp_expr store env e = VList (interp_expr store env r :: l)) /\
      (forall r, classify_write tbl e = WSnoc r ->
                 interp_expr store env e = VList (l ++ [interp_expr store env r])) /\
      (forall x p, classify_write tbl e = WFilter x p ->
                   exists g, interp_expr store env e = VList (filter g l)).
  Proof.
    intros * E_tbl. repeat split.
    1:{ intros r E. apply classify_write_cons in E; subst.
        cbn [interp_expr interp_binop]. unfold get_local. rewrite E_tbl. reflexivity. }
    1:{ intros r E. apply classify_write_snoc in E as [ t E ]; subst.
        cbn [interp_expr interp_binop interp_atom]. unfold get_local. rewrite E_tbl. reflexivity. }
    1:{ intros x p E. apply classify_write_filter in E as [ t1 [ t2 E ] ]; subst.
        rewrite interp_flatmap_filter_list.
        cbn [interp_expr]; unfold get_local; rewrite E_tbl.
        eexists; reflexivity. }
  Qed.

  Lemma type_of_value_record : forall v rt,
      type_of_value v (TRecord rt) -> exists rv, v = VRecord rv.
  Proof.
    intros * H; inversion H; eauto.
  Qed.

  Lemma cheap_guard_iff : forall (Gstore Genv : tenv) tbl row cond e g' row_ty (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> map.get Gstore tbl = Some (TList row_ty) ->
      type_of Gstore (map.put map.empty row row_ty) cond TBool ->
      type_of Gstore Genv e (TList row_ty) ->
      cheap_guard row_ty tbl row cond e = Some g' ->
      locals_wf Gstore store -> locals_wf Genv env ->
      inv_holds store (ConstraintInv tbl nil row cond) ->
      interp_expr store env g' = VBool true <->
        inv_holds (map.put store tbl (interp_expr store env e)) (ConstraintInv tbl nil row cond).
  Proof.
    intros * H_Gs H_Ge H_tbl H_cond H_e H_c H_store H_env H_inv.
    assert (H_rt : type_wf row_ty)
      by (apply H_Gs in H_tbl; inversion H_tbl; assumption).
    destruct (locals_wf_list Gstore store tbl row_ty H_store H_tbl) as [ l [ E_tbl H_l ] ].
    destruct (interp_write tbl e store env l E_tbl) as [ E_cons [ E_snoc E_filter ] ].
    assert (H_rv : forall r, classify_write tbl e = WCons r \/ classify_write tbl e = WSnoc r ->
                             type_of_value (interp_expr store env r) row_ty)
      by (intros r H_r; eapply type_sound; [ eapply classify_write_row_ty; [ exact H_r | exact H_e ] | .. ];
          eauto).
    unfold cheap_guard in H_c.
    destruct (loc_in tbl cond) eqn:E_loc.
    (* a key *)
    1:{ destruct (key_of row_ty tbl row cond) as [ attrs | ] eqn:E_k;
          [ | destruct (classify_write tbl e); cbn [option_map] in H_c; discriminate ].
        apply key_of_sound in E_k as [ rt [ -> [ -> [ E_cond [ Hnd HF ] ] ] ] ].
        rewrite (inv_holds_erase tbl nil "_r" _ _ _ E_cond) in H_inv.
        rewrite (inv_holds_erase tbl nil "_r" _ _ _ E_cond).
        pose proof (typed_rows_are_records _ _ H_l) as H_rec.
        rewrite (unique_cond_holds_iff tbl attrs (TRecord rt) store l Hnd E_tbl H_rec) in H_inv.
        destruct (classify_write tbl e) as [ r | r | x p | ] eqn:E_w; cbn [option_map] in H_c;
          try discriminate; injection H_c as <-.
        1:{ rewrite (E_cons r eq_refl).
            destruct (type_of_value_record _ _ (H_rv r (or_introl eq_refl))) as [ rv E_rv ].
            rewrite (unique_cond_holds_iff tbl attrs (TRecord rt) _ _ Hnd (map.get_put_same _ _ _)
                       (Forall_cons _ (ex_intro _ rv E_rv) H_rec)).
            rewrite (unique_guard_let_iff tbl attrs r store env l rv Hnd E_tbl E_rv H_rec).
            rewrite E_rv. cbn [List.map]. rewrite NoDup_cons_iff. tauto. }
        1:{ rewrite (E_snoc r eq_refl).
            destruct (type_of_value_record _ _ (H_rv r (or_intror eq_refl))) as [ rv E_rv ].
            assert (H_rec' : Forall (fun v => exists rc, v = VRecord rc) (l ++ [interp_expr store env r]))
              by (apply Forall_app; split; [ exact H_rec | constructor; eauto ]).
            rewrite (unique_cond_holds_iff tbl attrs (TRecord rt) _ _ Hnd (map.get_put_same _ _ _) H_rec').
            rewrite (unique_guard_let_iff tbl attrs r store env l rv Hnd E_tbl E_rv H_rec).
            rewrite E_rv, map_app. cbn [List.map].
            split.
            1:{ intro H_out. eapply Permutation_NoDup; [ apply Permutation_cons_append | ].
                constructor; assumption. }
            1:{ intro H_nd.
                assert (H_nd' : NoDup (row_keys attrs (VRecord rv) :: List.map (row_keys attrs) l))
                  by (eapply Permutation_NoDup; [ apply Permutation_sym, Permutation_cons_append | exact H_nd ]).
                inversion H_nd'; assumption. } }
        1:{ destruct (E_filter x p eq_refl) as [ gf E_f ]. rewrite E_f.
            rewrite (unique_cond_holds_iff tbl attrs (TRecord rt) _ _ Hnd (map.get_put_same _ _ _)
                       (Forall_filter _ _ gf l H_rec)).
            cbn [interp_expr interp_atom]. split; [ intros _ | reflexivity ].
            apply NoDup_map_filter; exact H_inv. } }
    (* a condition that does not read the table *)
    destruct (classify_write tbl e) as [ r | r | x p | ] eqn:E_w; try discriminate; injection H_c as <-.
    all: rewrite (inv_holds_nil_iff tbl row cond store l E_tbl) in H_inv.
    1:{ rewrite (E_cons r eq_refl), row_only_holds_iff by exact E_loc.
        rewrite (interp_ELet_row Gstore row row_ty cond r store env H_Gs H_rt H_cond H_store
                   (H_rv r (or_introl eq_refl))).
        rewrite Forall_cons_iff. cbv beta. tauto. }
    1:{ rewrite (E_snoc r eq_refl), row_only_holds_iff by exact E_loc.
        rewrite (interp_ELet_row Gstore row row_ty cond r store env H_Gs H_rt H_cond H_store
                   (H_rv r (or_intror eq_refl))).
        rewrite Forall_app, Forall_cons_iff. cbv beta.
        split; [ intro; split; [ exact H_inv | split; [ assumption | constructor ] ] | tauto ]. }
    1:{ destruct (E_filter x p eq_refl) as [ gf E_f ]. rewrite E_f, row_only_holds_iff by exact E_loc.
        cbn [interp_expr interp_atom]. split; [ intros _ | reflexivity ].
        apply Forall_filter; exact H_inv. }
  Qed.


  Lemma bool_value_eq : forall v1 v2,
      type_of_value v1 TBool -> type_of_value v2 TBool ->
      (v1 = VBool true <-> v2 = VBool true) -> v1 = v2.
  Proof.
    intros * H1 H2 H. inversion H1; inversion H2; subst.
    destruct b, b0; try reflexivity.
    1: discriminate (proj1 H eq_refl).
    1: discriminate (proj2 H eq_refl).
  Qed.

  Lemma find_cheap_correct : forall ictx (Gstore Genv : tenv) e x g2 g' t,
      tenv_wf Gstore -> tenv_wf Genv -> Forall (inv_wf Gstore) ictx ->
      type_of Gstore Genv (ELet e x g2) t -> find_cheap Gstore e (ELet e x g2) ictx = Some g' ->
      type_of Gstore Genv g' t /\
        forall store env : locals,
          locals_wf Gstore store -> locals_wf Genv env -> holds_all store ictx ->
          interp_expr store env g' = interp_expr store env (ELet e x g2).
  Proof.
    intros * H_Gs H_Ge H_ictx H_g H_f.
    apply find_cheap_spec in H_f as [ i [ H_in H_i ] ].
    apply cheap_for_spec in H_i as (tbl & row & cond & row_ty & -> & E_g & H_tbl & H_c).
    pose proof (proj1 (Forall_forall _ _) H_ictx _ H_in) as H_wf.
    assert (H_cond : type_of Gstore (map.put map.empty row row_ty) cond TBool).
    1:{ inversion H_wf; subst. cbn [type_at] in *.
        lazymatch goal with
        | H : map.get Gstore tbl = Some ?t, H' : Some ?t = Some (TList ?rt) |- _ =>
            rewrite H_tbl in H; injection H as <-; injection H' as <-
        end.
        assumption. }
    destruct (guard_ty_bool _ _ _ _ _ _ _ _ _ H_g E_g) as [ -> [ te H_e ] ].
    assert (te = TList row_ty)
      by (eapply classify_write_ty; [ exact H_tbl | eapply cheap_guard_not_other; eassumption | exact H_e ]).
    subst te.
    pose proof (cheap_guard_ty Gstore Genv tbl row cond e g' row_ty H_Gs H_Ge H_tbl H_cond H_e H_c) as H_g'.
    split; [ exact H_g' | ].
    intros store env H_store H_env H_h.
    assert (H_holds : inv_holds store (ConstraintInv tbl nil row cond))
      by (exact (proj1 (Forall_forall _ _) H_h _ H_in)).
    apply bool_value_eq.
    1: exact (type_sound Gstore Genv g' TBool H_g' H_Gs H_Ge store env H_store H_env).
    1: exact (type_sound Gstore Genv _ TBool H_g H_Gs H_Ge store env H_store H_env).
    rewrite (cheap_guard_iff Gstore Genv tbl row cond e g' row_ty store env); eauto.
    rewrite <- (interp_erase_annot (ELet e x g2) store env), E_g, interp_erase_annot.
    rewrite (inv_guard_iff Gstore Genv tbl (TList row_ty) e _ store env); eauto.
    reflexivity.
  Qed.

  Theorem guard_rule_sound : ictx_rule_sound guard_rule.
  Proof.
    unfold ictx_rule_sound; intros ictx Gstore H_Gs H_ictx. split.
    1:{ unfold preserve_ty; intros g t Genv _ H_Ge H_g. unfold guard_rule.
        destruct g; try exact H_g.
        lazymatch goal with
        | |- context[find_cheap ?G ?e ?g ?ictx] => destruct (find_cheap G e g ictx) eqn:E
        end; [ | exact H_g ].
        exact (proj1 (find_cheap_correct ictx Gstore Genv _ _ _ _ t H_Gs H_Ge H_ictx H_g E)). }
    1:{ intros store H_h. unfold preserve_sem; intros g t Genv env _ H_Ge H_g H_store H_env.
        unfold guard_rule.
        destruct g; try reflexivity.
        lazymatch goal with
        | |- context[find_cheap ?G ?e ?g ?ictx] => destruct (find_cheap G e g ictx) eqn:E
        end; [ | reflexivity ].
        exact (proj2 (find_cheap_correct ictx Gstore Genv _ _ _ _ t H_Gs H_Ge H_ictx H_g E)
                 store env H_store H_env H_h). }
  Qed.

  Corollary guard_rules_sound :
    inv_transf_sound (locals := locals) (fun Gstore _ c => fold_command_with_ictx guard_rule nil Gstore c).
  Proof.
    apply fold_command_with_ictx_sound, guard_rule_sound.
  Qed.
End WithMap.
