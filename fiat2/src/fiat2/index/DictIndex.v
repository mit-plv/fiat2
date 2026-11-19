Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils
  fiat2.TransfSound fiat2.TransfUtils fiat2.Invariant fiat2.index.IndexInterface fiat2.rules.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String List Sorted.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope bool_scope.

(* A dictionary index on one attribute, from each key to the bag of rows with
   that key.  Only the read rule replaces an index by the stored one; the
   other rules rewrite the program into an index of the table for it. *)

Definition dict_body (attr tup acc b : string) (tb : option type) : expr :=
  ETernop OInsert (EVar acc) (EAccess (EVar tup) attr)
    (EBinop OBagInsert
       (EOptMatch (EBinop OLookup (EVar acc) (EAccess (EVar tup) attr))
          (EAtom (AEmptyBag tb)) b (EVar b))
       (EVar tup)).

Definition dict_fold (attr : string) (l : expr) : expr :=
  EFold l (EAtom (AEmptyDict Unranged None)) "_tup" "_acc" (dict_body attr "_tup" "_acc" "_b" None).

Definition dict_ty (kt : type) (rt : list (string * type)) : type :=
  TDict Unranged kt (TBag (TRecord rt)).

Definition dict_is_tbl_ty (attr : string) (t : type) : bool :=
  match t with
  | TList (TRecord rt) => inb String.eqb attr (List.map fst rt)
  | _ => false
  end.

Definition dict_idx_ty (attr : string) (t : type) : type :=
  match t with
  | TList (TRecord rt) => dict_ty (get_attr_type rt attr) rt
  | _ => TUnit
  end.

Definition dict_idx (attr : string) : IndexInterface.index :=
  IndexInterface.mk "_h" (dict_fold attr (EVar "_h")) (dict_idx_ty attr) (dict_is_tbl_ty attr).

(* The attribute and the rows of an index built from scratch, with any binder names *)
Definition dict_fold_of (e : expr) : option (string * expr) :=
  match e with
  | EFold l (EAtom (AEmptyDict Unranged _)) tup acc
      (ETernop OInsert (EVar acc1) (EAccess (EVar tup1) attr)
         (EBinop OBagInsert
            (EOptMatch (EBinop OLookup (EVar acc2) (EAccess (EVar tup2) attr'))
               (EAtom (AEmptyBag _)) b (EVar b'))
            (EVar tup3))) =>
      if negb (String.eqb tup acc) && forallb (String.eqb tup) [tup1; tup2; tup3]
         && forallb (String.eqb acc) [acc1; acc2] && String.eqb b b' && String.eqb attr attr'
      then Some (attr, l) else None
  | _ => None
  end.

Definition fold_cons_head (e : expr) : expr :=
  match e with
  | EFold (EBinop OCons r l) d x acc body =>
      if negb (String.eqb x acc) && negb (free_immut_in acc r)
      then ELet (EFold l d x acc body) acc (ELet r x body)
      else e
  | _ => e
  end.

Definition dict_delete_of (e : expr) : option (string * expr * expr) :=
  match dict_fold_of e with
  | Some (attr, flatmap_filter_list l x (EUnop ONot (EBinop OEq (EAccess (EVar x1) attr') k)) x2 _ _) =>
      if String.eqb attr attr' && String.eqb x x1 && String.eqb x x2 && negb (free_immut_in x k)
      then Some (attr, l, k) else None
  | _ => None
  end.

Definition dict_delete_head (e : expr) : expr :=
  match dict_delete_of e with
  | Some (attr, l, k) => EBinop ODelete (dict_fold attr l) k
  | None => e
  end.

Definition dict_lookup_of (e : expr) : option (string * expr * expr) :=
  match e with
  | EUnop OBagOfList (flatmap_filter_list l x (EBinop OEq (EAccess (EVar x1) attr) k) x2 _ _)
  | flatmap_filter_bag (EUnop OBagOfList l) x (EBinop OEq (EAccess (EVar x1) attr) k) x2 _ _ =>
      if String.eqb x x1 && String.eqb x x2 && negb (free_immut_in x k) then Some (attr, l, k) else None
  | _ => None
  end.

Definition eq_filter_to_lookup (e : expr) : expr :=
  match dict_lookup_of e with
  | Some (attr, l, k) => EOptMatch (EBinop OLookup (dict_fold attr l) k) (EAtom (AEmptyBag None)) "_b" (EVar "_b")
  | None => e
  end.

Definition dict_aux_of (attr : string) (l : expr) (i : invariant) : option expr :=
  match i with
  | IndexInv tbl [id] [aux] h ti =>
      match dict_fold_of ti with
      | Some (attr', EVar h') =>
          if String.eqb attr attr' && String.eqb h h' && expr_eqb l (EAccess (ELoc tbl) id)
          then Some (EAccess (ELoc tbl) aux) else None
      | _ => None
      end
  | _ => None
  end.

(* The stored index of the rows l on attr, if the context has one *)
Fixpoint dict_aux (ictx : list invariant) (attr : string) (l : expr) : option expr :=
  match ictx with
  | nil => None
  | i :: ictx => match dict_aux_of attr l i with
                 | Some aux => Some aux
                 | None => dict_aux ictx attr l
                 end
  end.

Definition dict_read_head (ictx : list invariant) (e : expr) : expr :=
  match dict_fold_of e with
  | Some (attr, l) => match dict_aux ictx attr l with
                      | Some aux => aux
                      | None => e
                      end
  | None => e
  end.

Definition has_dict_for (ictx : list invariant) (e : expr) : bool :=
  match dict_lookup_of e with
  | Some (attr, l, _) => match dict_aux ictx attr l with
                         | Some _ => true
                         | None => false
                         end
  | None => false
  end.

Definition row_key (attr : string) (v : value) : value :=
  match v with
  | VRecord r => record_proj attr r
  | _ => VUnit
  end.

Definition bucket (k : value) (d : list (value * value)) : value :=
  match dict_lookup k d with
  | Some b => b
  | None => VBag nil
  end.

Definition dict_step (attr : string) (v acc : value) : value :=
  match acc with
  | VDict d => VDict (dict_insert (row_key attr v) (interp_binop OBagInsert (bucket (row_key attr v) d) v) d)
  | _ => VUnit
  end.

Definition dict_of (attr : string) (v : value) : value :=
  match v with
  | VList l => fold_right (dict_step attr) (VDict nil) l
  | _ => VUnit
  end.

Ltac inv_tys :=
  repeat match goal with
    | H : type_of _ _ (EVar _) _ |- _ => inversion H; subst; clear H
    | H : type_of _ _ (EAtom _) _ |- _ => inversion H; subst; clear H
    | H : type_of _ _ (EUnop _ _) _ |- _ => inversion H; subst; clear H
    | H : type_of _ _ (EBinop _ _ _) _ |- _ => inversion H; subst; clear H
    | H : type_of _ _ (ETernop _ _ _ _) _ |- _ => inversion H; subst; clear H
    | H : type_of _ _ (EIf _ _ _) _ |- _ => inversion H; subst; clear H
    | H : type_of _ _ (EAccess (EVar _) _) _ |- _ => inversion H; subst; clear H
    | H : type_of _ _ (EOptMatch _ _ _ _) _ |- _ => inversion H; subst; clear H
    | H : type_of_atom _ _ |- _ => inversion H; subst; clear H
    | H : type_of_unop _ _ _ |- _ => inversion H; subst; clear H
    | H : type_of_binop _ _ _ _ |- _ => inversion H; subst; clear H
    | H : type_of_ternop _ _ _ _ _ |- _ => inversion H; subst; clear H
    | H : map.get (map.put _ ?x _) ?x = _ |- _ => rewrite map.get_put_same in H
    | H : map.get (map.put _ _ _) _ = _ |- _ => rewrite map.get_put_diff in H by (discriminate || congruence)
    | H : Some _ = Some _ |- _ => inversion H; subst; clear H
    end.

Ltac split_conds :=
  repeat match goal with
    | H : _ && _ = true |- _ => apply Bool.andb_true_iff in H as [ ? ? ]
    | H : negb _ = true |- _ => apply Bool.negb_true_iff in H
    | H : (_ =? _) = true |- _ => apply String.eqb_eq in H; subst
    | H : (_ =? _) = false |- _ => apply String.eqb_neq in H
    | H : expr_eqb _ _ = true |- _ => apply expr_eqb_true in H; subst
    end.

Lemma dict_fold_of_spec : forall e attr l,
    dict_fold_of e = Some (attr, l) ->
    exists a tup acc b tb,
      e = EFold l (EAtom (AEmptyDict Unranged a)) tup acc (dict_body attr tup acc b tb) /\ tup <> acc.
Proof.
  unfold dict_fold_of; intros * H.
  repeat (destruct_match_hyp; try discriminate).
  injection H as <- <-. cbn [forallb] in *. rewrite !Bool.andb_true_r in *. split_conds.
  do 5 eexists; split; [ reflexivity | assumption ].
Qed.

Lemma dict_fold_of_dict_fold : forall attr l, dict_fold_of (dict_fold attr l) = Some (attr, l).
Proof.
  intros. unfold dict_fold_of, dict_fold, dict_body. cbn [forallb negb].
  rewrite !String.eqb_refl. reflexivity.
Qed.

Lemma dict_delete_of_spec : forall e attr l k,
    dict_delete_of e = Some (attr, l, k) ->
    exists x t1 t2,
      dict_fold_of e = Some (attr, flatmap_filter_list l x (EUnop ONot (EBinop OEq (EAccess (EVar x) attr) k)) x t1 t2)
      /\ free_immut_in x k = false.
Proof.
  unfold dict_delete_of; intros * H.
  repeat (destruct_match_hyp; try discriminate).
  injection H as <- <- <-. split_conds. eauto.
Qed.

Lemma dict_lookup_of_spec : forall e attr l k,
    dict_lookup_of e = Some (attr, l, k) ->
    exists x t1 t2,
      (e = EUnop OBagOfList (flatmap_filter_list l x (EBinop OEq (EAccess (EVar x) attr) k) x t1 t2) \/
       e = flatmap_filter_bag (EUnop OBagOfList l) x (EBinop OEq (EAccess (EVar x) attr) k) x t1 t2) /\
        free_immut_in x k = false.
Proof.
  unfold dict_lookup_of; intros * H.
  repeat (destruct_match_hyp; try discriminate).
  all: injection H as <- <- <-; split_conds.
  all: do 3 eexists; split; [ first [ left; reflexivity | right; reflexivity ] | assumption ].
Qed.

Lemma dict_aux_spec : forall ictx attr l aux,
    dict_aux ictx attr l = Some aux ->
    exists tbl id auxf h ti,
      In (IndexInv tbl [id] [auxf] h ti) ictx /\ dict_fold_of ti = Some (attr, EVar h) /\
        l = EAccess (ELoc tbl) id /\ aux = EAccess (ELoc tbl) auxf.
Proof.
  induction ictx as [ | i ictx IH ]; cbn [dict_aux]; intros * H; [ discriminate | ].
  destruct (dict_aux_of attr l i) eqn:E.
  1:{ injection H as <-. unfold dict_aux_of in E.
      repeat (destruct_match_hyp; try discriminate).
      injection E as <-. split_conds.
      do 5 eexists; split; [ left; reflexivity | ]. eauto. }
  1:{ apply IH in H as (tbl & id & auxf & h & ti & H_in & H_rest).
      do 5 eexists; split; [ right; exact H_in | exact H_rest ]. }
Qed.

Section WithMap.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Lemma access_record_ty_wf : forall rt attr kt,
      type_wf (TRecord rt) -> access_record rt attr = Success kt -> type_wf kt.
  Proof.
    intros * H_wf H_a.
    replace kt with (get_attr_type rt attr) by (unfold get_attr_type; rewrite H_a; reflexivity).
    apply get_attr_type_ty_wf; exact H_wf.
  Qed.

  Lemma dict_fold_ty : forall (Gstore Genv : tenv) attr l rt kt,
      type_wf (TRecord rt) -> access_record rt attr = Success kt ->
      type_of Gstore Genv l (TList (TRecord rt)) ->
      type_of Gstore Genv (dict_fold attr l) (dict_ty kt rt).
  Proof.
    unfold dict_fold, dict_body, dict_ty; intros * H_wf H_a H_l.
    pose proof (access_record_ty_wf _ _ _ H_wf H_a) as H_kt.
    econstructor; [ exact H_l | constructor; constructor; [ exact H_kt | constructor; exact H_wf ] | ].
    assert (H_tup : map.get (map.put (map.put Genv "_tup" (TRecord rt)) "_acc" (TDict Unranged kt (TBag (TRecord rt)))) "_tup"
                    = Some (TRecord rt))
      by (rewrite map.get_put_diff by discriminate; apply map.get_put_same).
    assert (H_acc : map.get (map.put (map.put Genv "_tup" (TRecord rt)) "_acc" (TDict Unranged kt (TBag (TRecord rt)))) "_acc"
                    = Some (TDict Unranged kt (TBag (TRecord rt))))
      by apply map.get_put_same.
    econstructor; [ constructor | constructor; exact H_acc | econstructor; [ constructor; exact H_tup | exact H_a ] | ].
    econstructor; [ constructor | | constructor; exact H_tup ].
    econstructor.
    1: econstructor; [ constructor | constructor; exact H_acc | econstructor; [ constructor; exact H_tup | exact H_a ] ].
    1: constructor; constructor; exact H_wf.
    1: constructor; apply map.get_put_same.
  Qed.

  #[global] Instance dict_idx_ok (attr : string) : ok (dict_idx attr).
  Proof.
    constructor. cbn [IndexInterface.hole IndexInterface.to_idx IndexInterface.idx_ty IndexInterface.is_tbl_ty dict_idx].
    intros t H_wf H_is. unfold dict_is_tbl_ty in H_is.
    destruct t as [ | | | | | t | | | | ]; try discriminate.
    destruct t as [ | | | | | | rt | | | ]; try discriminate.
    rewrite inb_true_iff in H_is. apply In_access_record in H_is as [ kt H_a ].
    inversion H_wf; subst. cbn [dict_idx_ty].
    replace (get_attr_type rt attr) with kt by (unfold get_attr_type; rewrite H_a; reflexivity).
    apply dict_fold_ty; auto. constructor. apply map.get_put_same.
  Qed.

  Lemma dict_fold_of_ty : forall (Gstore Genv : tenv) e attr l t,
      dict_fold_of e = Some (attr, l) -> type_of Gstore Genv e t ->
      exists rt kt, type_of Gstore Genv l (TList (TRecord rt)) /\ access_record rt attr = Success kt /\
                      t = dict_ty kt rt.
  Proof.
    intros * H_e H_t. apply dict_fold_of_spec in H_e as (a & tup & acc & b & tb & -> & H_ne).
    inversion H_t; subst. unfold dict_body in *. inv_tys.
    all: do 2 eexists; split; [ eassumption | split; [ eassumption | reflexivity ] ].
  Qed.

  Lemma interp_EFold : forall (store env : locals) l d x y body,
      interp_expr store env (EFold l d x y body) =
        match interp_expr store env l with
        | VList vs => fold_right (fun v a => interp_expr store (map.put (map.put env x v) y a) body)
                        (interp_expr store env d) vs
        | _ => VUnit
        end.
  Proof. reflexivity. Qed.

  Lemma interp_dict_body : forall attr tup acc b tb (store env : locals) v a,
      map.get env tup = Some v -> map.get env acc = Some a ->
      interp_expr store env (dict_body attr tup acc b tb) = dict_step attr v a.
  Proof.
    intros * H_tup H_acc. unfold dict_body; cbn [interp_expr]. unfold get_local; rewrite H_tup, H_acc.
    destruct a; try reflexivity. cbn [interp_binop interp_ternop interp_atom].
    change (match v with VRecord l => record_proj attr l | _ => VUnit end) with (row_key attr v).
    unfold dict_step, bucket. destruct (dict_lookup (row_key attr v) l); [ | reflexivity ].
    rewrite map.get_put_same. reflexivity.
  Qed.

  Lemma interp_dict_fold_of : forall e attr l (store env : locals),
      dict_fold_of e = Some (attr, l) ->
      interp_expr store env e = dict_of attr (interp_expr store env l).
  Proof.
    intros * H. apply dict_fold_of_spec in H as (a & tup & acc & b & tb & -> & H_ne).
    rewrite interp_EFold. destruct (interp_expr store env l); try reflexivity. cbn [dict_of].
    change (interp_expr store env (EAtom (AEmptyDict Unranged a))) with (VDict nil).
    apply fold_right_ext; intros v a'. apply interp_dict_body.
    1: rewrite map.get_put_diff by congruence; apply map.get_put_same.
    1: apply map.get_put_same.
  Qed.

  Lemma dict_lookup_insert_same : forall k (v : value) d,
      dict_lookup k (dict_insert k v d) = Some v.
  Proof.
    induction d as [ | [ k0 v0 ] d IH ]; cbn [dict_insert].
    1: cbn; rewrite value_eqb_refl; reflexivity.
    destruct (value_ltb k k0).
    1: cbn; rewrite value_eqb_refl; reflexivity.
    destruct (value_eqb k k0) eqn:E; cbn.
    1: rewrite value_eqb_refl; reflexivity.
    rewrite E. exact IH.
  Qed.

  Lemma dict_lookup_insert_diff : forall k k' (v : value) d,
      k <> k' -> dict_lookup k (dict_insert k' v d) = dict_lookup k d.
  Proof.
    induction d as [ | [ k0 v0 ] d IH ]; cbn [dict_insert]; intros H_ne.
    1: cbn; rewrite neq__value_eqb_false by assumption; reflexivity.
    destruct (value_ltb k' k0).
    1: cbn; rewrite neq__value_eqb_false by assumption; reflexivity.
    destruct (value_eqb k' k0) eqn:E; cbn.
    1:{ apply value_eqb_eq in E; subst. rewrite neq__value_eqb_false by assumption; reflexivity. }
    destruct (value_eqb k k0); [ reflexivity | apply IH; exact H_ne ].
  Qed.

  Lemma fold_dict_step_sorted : forall attr l,
      exists d, fold_right (dict_step attr) (VDict nil) l = VDict d /\
                  StronglySorted (fun p p' => is_true (dict_entry_leb p p')) d.
  Proof.
    induction l as [ | v l (d & E & H_s) ]; cbn [fold_right].
    1: exists nil; split; [ reflexivity | constructor ].
    rewrite E. cbn [dict_step]. eexists; split; [ reflexivity | apply dict_insert_preserve_SSorted; exact H_s ].
  Qed.

  Lemma fold_dict_step_bucket : forall attr l k d,
      fold_right (dict_step attr) (VDict nil) l = VDict d ->
      bucket k d = VBag (list_to_bag (filter (fun v => value_eqb (row_key attr v) k) l)).
  Proof.
    induction l as [ | v l IH ]; cbn [fold_right]; intros k d H.
    1: injection H as <-; reflexivity.
    destruct (fold_dict_step_sorted attr l) as (d0 & E0 & _). rewrite E0 in H.
    cbn [dict_step] in H. injection H as <-. specialize (IH k d0 E0).
    cbn [filter]. destruct (value_eqb (row_key attr v) k) eqn:E.
    1:{ apply value_eqb_eq in E; subst k. unfold bucket at 1. rewrite dict_lookup_insert_same, IH.
        reflexivity. }
    1:{ unfold bucket at 1. rewrite dict_lookup_insert_diff; [ exact IH | ].
        intros ->. rewrite value_eqb_refl in E; discriminate. }
  Qed.

  Lemma fold_dict_step_delete : forall attr l k,
      fold_right (dict_step attr) (VDict nil) (filter (fun v => negb (value_eqb (row_key attr v) k)) l)
      = match fold_right (dict_step attr) (VDict nil) l with
        | VDict d => VDict (dict_delete k d)
        | _ => VUnit
        end.
  Proof.
    induction l as [ | v l IH ]; intros k; cbn [filter fold_right].
    1: reflexivity.
    destruct (fold_dict_step_sorted attr l) as (d0 & E0 & H_s). rewrite E0 in IH |- *.
    cbn [dict_step]. destruct (value_eqb (row_key attr v) k) eqn:E; cbn [negb].
    1:{ apply value_eqb_eq in E; subst k. rewrite IH, dict_delete_insert_same by exact H_s. reflexivity. }
    1:{ assert (H_ne : k <> row_key attr v) by (intros ->; rewrite value_eqb_refl in E; discriminate).
        cbn [fold_right]. rewrite IH. cbn [dict_step].
        rewrite dict_delete_insert_diff by assumption.
        unfold bucket. rewrite dict_lookup_delete_diff by congruence. reflexivity. }
  Qed.

  Lemma interp_filter_list : forall (store env : locals) l x p t1 t2 g,
      (forall v, interp_expr store (map.put env x v) p = VBool (g v)) ->
      interp_expr store env (flatmap_filter_list l x p x t1 t2) =
        match interp_expr store env l with
        | VList vs => VList (filter g vs)
        | _ => VUnit
        end.
  Proof.
    intros * H. cbn [interp_expr]. destruct (interp_expr store env l); try reflexivity.
    f_equal. induction l0 as [ | v vs IH ]; cbn [flat_map filter]; [ reflexivity | ].
    rewrite H, IH. destruct (g v); cbn [interp_binop interp_atom]; unfold get_local;
      rewrite ?map.get_put_same; reflexivity.
  Qed.

  Lemma interp_filter_bag : forall (store env : locals) l x p t1 t2 g,
      (forall v, interp_expr store (map.put env x v) p = VBool (g v)) ->
      interp_expr store env (flatmap_filter_bag (EUnop OBagOfList l) x p x t1 t2) =
        match interp_expr store env l with
        | VList vs => VBag (list_to_bag (filter g vs))
        | _ => VUnit
        end.
  Proof.
    intros * H. cbn [interp_expr]. destruct (interp_expr store env l); try reflexivity.
    cbn [interp_unop]. rewrite <- list_to_bag_filter_list_to_bag. do 2 f_equal.
    generalize (bag_to_list (list_to_bag l0)).
    induction l1 as [ | v vs IH ]; cbn [flat_map filter]; [ reflexivity | ].
    rewrite H, IH. destruct (g v); cbn [interp_binop interp_atom]; unfold get_local;
      rewrite ?map.get_put_same; reflexivity.
  Qed.

  Lemma interp_eq_key : forall (store env : locals) x attr k v,
      free_immut_in x k = false ->
      interp_expr store (map.put env x v) (EBinop OEq (EAccess (EVar x) attr) k)
      = VBool (value_eqb (row_key attr v) (interp_expr store env k)).
  Proof.
    intros * H. cbn [interp_expr interp_binop]. unfold get_local; rewrite map.get_put_same.
    rewrite <- (not_free_immut_put_sem k x store env v H). reflexivity.
  Qed.

  Lemma interp_eq_filter : forall e attr l k (store env : locals),
      dict_lookup_of e = Some (attr, l, k) ->
      interp_expr store env e =
        match interp_expr store env l with
        | VList vs => VBag (list_to_bag (filter (fun v => value_eqb (row_key attr v) (interp_expr store env k)) vs))
        | _ => VUnit
        end.
  Proof.
    intros * H. apply dict_lookup_of_spec in H as (x & t1 & t2 & [ -> | -> ] & H_free).
    1:{ change (interp_expr store env (EUnop OBagOfList ?a))
          with (interp_unop OBagOfList (interp_expr store env a)).
        rewrite interp_filter_list with (g := fun v => value_eqb (row_key attr v) (interp_expr store env k))
          by (intros; apply interp_eq_key; exact H_free).
        destruct (interp_expr store env l); reflexivity. }
    1:{ apply interp_filter_bag. intros; apply interp_eq_key; exact H_free. }
  Qed.

  Lemma filter_ty_inv : forall (Gstore Genv : tenv) l x p t1 t2 t,
      type_of Gstore Genv (flatmap_filter_list l x p x t1 t2) t ->
      exists tr, t = TList tr /\ type_of Gstore Genv l (TList tr) /\ type_of Gstore (map.put Genv x tr) p TBool.
  Proof.
    intros * H. inversion H; subst.
    lazymatch goal with H : type_of _ _ (EIf _ _ _) _ |- _ => inversion H; subst; clear H end.
    lazymatch goal with H : type_of _ _ (EBinop OCons _ _) _ |- _ => inversion H; subst; clear H end.
    lazymatch goal with H : type_of_binop OCons _ _ _ |- _ => inversion H; subst; clear H end.
    lazymatch goal with H : type_of _ _ (EVar _) _ |- _ => inversion H; subst; clear H end.
    rewrite map.get_put_same in *.
    lazymatch goal with H : Some _ = Some _ |- _ => inversion H; subst; clear H end.
    eauto.
  Qed.

  Lemma filter_bag_ty_inv : forall (Gstore Genv : tenv) l x p t1 t2 t,
      type_of Gstore Genv (flatmap_filter_bag (EUnop OBagOfList l) x p x t1 t2) t ->
      exists tr, t = TBag tr /\ type_of Gstore Genv l (TList tr) /\ type_of Gstore (map.put Genv x tr) p TBool.
  Proof.
    intros * H. inversion H; subst.
    lazymatch goal with H : type_of _ _ (EIf _ _ _) _ |- _ => inversion H; subst; clear H end.
    lazymatch goal with H : type_of _ _ (EBinop OBagInsert _ _) _ |- _ => inversion H; subst; clear H end.
    lazymatch goal with H : type_of_binop OBagInsert _ _ _ |- _ => inversion H; subst; clear H end.
    lazymatch goal with H : type_of _ _ (EVar _) _ |- _ => inversion H; subst; clear H end.
    rewrite map.get_put_same in *.
    lazymatch goal with H : Some _ = Some _ |- _ => inversion H; subst; clear H end.
    lazymatch goal with H : type_of _ _ (EUnop OBagOfList _) _ |- _ => inversion H; subst; clear H end.
    lazymatch goal with H : type_of_unop OBagOfList _ _ |- _ => inversion H; subst; clear H end.
    eauto.
  Qed.

  Lemma key_cond_ty_inv : forall (Gstore Genv : tenv) x attr k tr,
      type_of Gstore (map.put Genv x tr) (EBinop OEq (EAccess (EVar x) attr) k) TBool ->
      free_immut_in x k = false ->
      exists rt kt, tr = TRecord rt /\ access_record rt attr = Success kt /\ type_of Gstore Genv k kt.
  Proof.
    intros * H H_free. inv_tys.
    do 2 eexists; split; [ reflexivity | split; [ eassumption | ] ].
    eapply not_free_immut_put_ty; eassumption.
  Qed.

  (* Both shapes of a bag of the rows with a given key *)
  Lemma eq_filter_ty_inv : forall (Gstore Genv : tenv) e attr l k t,
      dict_lookup_of e = Some (attr, l, k) -> type_of Gstore Genv e t ->
      exists rt kt, t = TBag (TRecord rt) /\ type_of Gstore Genv l (TList (TRecord rt)) /\
                      access_record rt attr = Success kt /\ type_of Gstore Genv k kt.
  Proof.
    intros * H H_e. apply dict_lookup_of_spec in H as (x & t1 & t2 & [ -> | -> ] & H_free).
    1:{ inversion H_e; subst.
        lazymatch goal with H : type_of_unop OBagOfList _ _ |- _ => inversion H; subst; clear H end.
        lazymatch goal with
        | H : type_of _ _ (flatmap_filter_list _ _ _ _ _ _) _ |- _ =>
            apply filter_ty_inv in H as (tr & E_tr & H_l & H_p)
        end.
        inversion E_tr; subst.
        destruct (key_cond_ty_inv _ _ _ _ _ _ H_p H_free) as (rt & kt & -> & H_a & H_k).
        eauto 7. }
    1:{ apply filter_bag_ty_inv in H_e as (tr & -> & H_l & H_p).
        destruct (key_cond_ty_inv _ _ _ _ _ _ H_p H_free) as (rt & kt & -> & H_a & H_k).
        eauto 7. }
  Qed.

  Lemma dict_aux_correct : forall (Gstore Genv : tenv) ictx attr l aux rt kt,
      Forall (inv_wf Gstore) ictx -> dict_aux ictx attr l = Some aux ->
      type_of Gstore Genv l (TList (TRecord rt)) -> access_record rt attr = Success kt ->
      type_of Gstore Genv aux (dict_ty kt rt) /\
        forall (store env : locals), holds_all store ictx ->
                                     interp_expr store env aux = dict_of attr (interp_expr store env l).
  Proof.
    intros * H_ictx H_aux H_l H_a.
    apply dict_aux_spec in H_aux as (tbl & id & auxf & h & ti & H_in & H_ti & -> & ->).
    split.
    1:{ rewrite Forall_forall in H_ictx. specialize (H_ictx _ H_in). inversion H_ictx; subst.
        lazymatch goal with
        | Ht : type_of _ _ ti _ |- _ =>
            destruct (dict_fold_of_ty _ _ _ _ _ _ H_ti Ht) as (rt' & kt' & H_h & H_a' & ->)
        end.
        inversion H_h; subst. rewrite map.get_put_same in *.
        lazymatch goal with H : Some _ = Some _ |- _ => inversion H; subst; clear H end.
        inversion H_l; subst.
        lazymatch goal with H : type_of _ _ (ELoc _) _ |- _ => inversion H; subst; clear H end.
        lazymatch goal with
        | H : map.get Gstore tbl = Some _, H' : map.get Gstore tbl = Some _ |- _ =>
            rewrite H in H'; inversion H'; subst; clear H'
        end.
        cbn [type_at] in *.
        lazymatch goal with
        | H : access_record ?tl id = Success _, H' : context[access_record ?tl id] |- _ =>
            rewrite H in H'; inversion H'; subst; clear H'
        end.
        lazymatch goal with
        | H : access_record ?r attr = Success _, H' : access_record ?r attr = Success _ |- _ =>
            rewrite H in H'; inversion H'; subst; clear H'
        end.
        lazymatch goal with
        | H : match access_record _ auxf with _ => _ end = Some _ |- _ =>
            destruct (access_record _ auxf) eqn:E_aux; inversion H; subst; clear H
        end.
        econstructor; [ constructor; eassumption | exact E_aux ]. }
    1:{ intros store env H_h. unfold holds_all in H_h. rewrite Forall_forall in H_h.
        specialize (H_h _ H_in). cbn [inv_holds] in H_h.
        destruct (map.get store tbl) as [ v | ] eqn:E_s; [ | contradiction ].
        cbn [interp_expr]. unfold get_local at 1 2; rewrite E_s.
        destruct v; cbn [value_at] in H_h; try contradiction.
        destruct (access_record l id) eqn:E_id; destruct (access_record l auxf) eqn:E_aux;
          cbn [value_at] in H_h; try contradiction.
        rewrite (access_record__record_proj _ _ _ E_id), (access_record__record_proj _ _ _ E_aux).
        rewrite H_h, (interp_dict_fold_of _ _ _ _ _ H_ti). cbn [interp_expr]. unfold get_local.
        rewrite map.get_put_same. reflexivity. }
  Qed.

  Theorem fold_cons_head_sound : expr_transf_sound (locals := locals) fold_cons_head.
  Proof.
    unfold expr_transf_sound; intros Gstore Genv e t H_Gs H_Ge H_e.
    destruct e as [ | | | | | | | | | e1 d x acc body | | | | | | ];
      try (split; [ exact H_e | intros; reflexivity ]).
    destruct e1 as [ | | | | o r l | | | | | | | | | | | ];
      try (split; [ exact H_e | intros; reflexivity ]).
    destruct o; try (split; [ exact H_e | intros; reflexivity ]).
    cbn [fold_cons_head].
    destruct (negb (x =? acc) && negb (free_immut_in acc r)) eqn:E;
      [ | split; [ exact H_e | intros; reflexivity ] ].
    rewrite Bool.andb_true_iff, !Bool.negb_true_iff, String.eqb_neq in E. destruct E as [ H_ne H_free ].
    inversion H_e; subst.
    lazymatch goal with H : type_of _ _ (EBinop _ _ _) _ |- _ => inversion H; subst; clear H end.
    lazymatch goal with H : type_of_binop _ _ _ _ |- _ => inversion H; subst; clear H end.
    lazymatch goal with H : type_of _ _ l _ |- _ => rename H into H_l end.
    split.
    1:{ econstructor; [ econstructor; eassumption | ].
        econstructor; [ apply not_free_immut_put_ty2; eassumption | ].
        rewrite Properties.map.put_put_diff by congruence. eassumption. }
    1:{ intros store env H_str H_env. cbn [interp_expr].
        pose proof (type_sound _ _ _ _ H_l H_Gs H_Ge _ _ H_str H_env) as H_v.
        destruct (interp_expr store env l); inversion H_v; subst.
        cbn [interp_binop fold_right].
        rewrite <- (not_free_immut_put_sem r acc store env _ H_free).
        rewrite Properties.map.put_put_diff by congruence. reflexivity. }
  Qed.

  Theorem dict_delete_head_sound : expr_transf_sound (locals := locals) dict_delete_head.
  Proof.
    unfold expr_transf_sound, dict_delete_head; intros Gstore Genv e t H_Gs H_Ge H_e.
    destruct (dict_delete_of e) as [ [ [ attr l ] k ] | ] eqn:E;
      [ | split; [ exact H_e | intros; reflexivity ] ].
    apply dict_delete_of_spec in E as (x & t1 & t2 & E_f & H_free).
    destruct (dict_fold_of_ty _ _ _ _ _ _ E_f H_e) as (rt & kt & H_F & H_a & ->).
    apply filter_ty_inv in H_F as (tr & E_tr & H_l & H_p).
    inversion E_tr; subst. inv_tys.
    lazymatch goal with
    | H : access_record ?r attr = Success _, H' : access_record ?r attr = Success _ |- _ =>
        rewrite H in H'; inversion H'; subst
    end.
    split.
    1:{ pose proof (type_of__type_wf _ _ _ _ H_Gs H_Ge H_l) as H_wf. inversion H_wf; subst.
        econstructor; [ constructor | apply dict_fold_ty; eassumption | ].
        eapply not_free_immut_put_ty; eassumption. }
    1:{ intros store env _ _.
        change (interp_expr store env (EBinop ODelete ?a ?b))
          with (interp_binop ODelete (interp_expr store env a) (interp_expr store env b)).
        rewrite (interp_dict_fold_of _ _ _ _ _ (dict_fold_of_dict_fold attr l)), (interp_dict_fold_of _ _ _ _ _ E_f).
        rewrite interp_filter_list with (g := fun v => negb (value_eqb (row_key attr v) (interp_expr store env k))).
        2:{ intros v.
            transitivity (interp_unop ONot (interp_expr store (map.put env x v) (EBinop OEq (EAccess (EVar x) attr) k)));
              [ reflexivity | rewrite interp_eq_key by exact H_free; reflexivity ]. }
        destruct (interp_expr store env l); try reflexivity. cbn [dict_of interp_binop].
        rewrite fold_dict_step_delete.
        destruct (fold_dict_step_sorted attr l0) as (d0 & -> & _). reflexivity. }
  Qed.

  Theorem eq_filter_to_lookup_sound : expr_transf_sound (locals := locals) eq_filter_to_lookup.
  Proof.
    unfold expr_transf_sound, eq_filter_to_lookup; intros Gstore Genv e t H_Gs H_Ge H_e.
    destruct (dict_lookup_of e) as [ [ [ attr l ] k ] | ] eqn:E_lk;
      [ | split; [ exact H_e | intros; reflexivity ] ].
    destruct (eq_filter_ty_inv _ _ _ _ _ _ _ E_lk H_e) as (rt & kt & -> & H_l & H_a & H_k).
    pose proof (type_of__type_wf _ _ _ _ H_Gs H_Ge H_l) as H_wf. inversion H_wf; subst.
    split.
    1:{ pose proof (dict_fold_ty Gstore Genv attr l rt kt ltac:(assumption) H_a H_l) as H_d.
        unfold dict_ty in H_d.
        econstructor; [ econstructor; [ constructor | exact H_d | exact H_k ] | | ].
        1: constructor; constructor; assumption.
        1: constructor; apply map.get_put_same. }
    1:{ intros store env _ _. rewrite (interp_eq_filter _ _ _ _ store env E_lk).
        cbn [interp_expr]. rewrite (interp_dict_fold_of _ _ _ _ _ (dict_fold_of_dict_fold attr l)).
        destruct (interp_expr store env l); try reflexivity. cbn [dict_of].
        destruct (fold_dict_step_sorted attr l0) as (d0 & E0 & _). rewrite E0. cbn [interp_binop].
        rewrite <- (fold_dict_step_bucket _ _ _ _ E0). unfold bucket.
        destruct (dict_lookup _ d0); [ | reflexivity ].
        cbn [interp_expr]. unfold get_local. rewrite map.get_put_same. reflexivity. }
  Qed.

  Definition dict_lookup_rule (ictx : list invariant) (_ : tenv) (e : expr) : expr :=
    if has_dict_for ictx e then eq_filter_to_lookup e else e.

  Theorem dict_lookup_rule_sound : ictx_rule_sound (locals := locals) dict_lookup_rule.
  Proof.
    apply (gated_rule_sound (fun ictx _ e => has_dict_for ictx e)). exact eq_filter_to_lookup_sound.
  Qed.

  Definition dict_read_rule (ictx : list invariant) (_ : tenv) : expr -> expr := dict_read_head ictx.

  Theorem dict_read_rule_sound : ictx_rule_sound (locals := locals) dict_read_rule.
  Proof.
    unfold ictx_rule_sound, preserve_ty, preserve_sem, dict_read_rule, dict_read_head.
    intros ictx Gstore H_Gs H_ictx. split.
    1:{ intros e t Genv _ H_Ge H_e.
        destruct (dict_fold_of e) as [ [ attr l ] | ] eqn:E_f; [ | exact H_e ].
        destruct (dict_aux ictx attr l) as [ aux | ] eqn:E_aux; [ | exact H_e ].
        destruct (dict_fold_of_ty _ _ _ _ _ _ E_f H_e) as (rt & kt & H_l & H_a & ->).
        eapply dict_aux_correct in E_aux as [ H_aux _ ]; eassumption. }
    1:{ intros store H_h e t Genv env _ H_Ge H_e H_str H_env.
        destruct (dict_fold_of e) as [ [ attr l ] | ] eqn:E_f; [ | reflexivity ].
        destruct (dict_aux ictx attr l) as [ aux | ] eqn:E_aux; [ | reflexivity ].
        destruct (dict_fold_of_ty _ _ _ _ _ _ E_f H_e) as (rt & kt & H_l & H_a & ->).
        eapply dict_aux_correct in E_aux as [ _ H_aux ]; [ | eassumption .. ].
        rewrite H_aux by exact H_h. symmetry. apply interp_dict_fold_of; exact E_f. }
  Qed.
End WithMap.
