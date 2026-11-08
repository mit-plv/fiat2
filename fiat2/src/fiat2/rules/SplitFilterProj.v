Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.TransfUtils fiat2.TransfSound fiat2.rules.FlatmapForms fiat2.rules.CollectionTransf.
Require Import coqutil.Map.Interface.
From Stdlib Require Import List String ZArith Permutation.
Import ListNotations.

(* The bag-level counterpart of `if_nil_into_flatmap_head` (FlatmapTransf.v)
   at LikeList.

     flatmap e x (if p then [r] else [])
       ==>  flatmap (flatmap e x (if p then [x] else [])) x [r]

   filter first, then project.  It is a normalisation and not an
   optimisation: it introduces no index, asks for none, and changes no
   behaviour.  What it buys is that the filter it leaves behind is in the
   shape the index rules read, so the rules become reachable from a shape
   sources commonly take. *)

(* The projection is the bound row itself, i.e. this is a filter already and
   there is nothing to split out. *)
Definition is_the_bound_row (x : string) (r : expr) : bool :=
  match r with
  | EVar y => String.eqb x y
  | _ => false
  end.

(* filter, then project.  The filter's branches are left unannotated. *)
Definition filter_then_proj (l : expr) (x : string) (p r : expr)
  (t : option type) : expr :=
  EFlatmap LikeBag
    (EFlatmap LikeBag l x
       (EIf p (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar x))
          (EAtom (AEmptyBag None))))
    x (EBinop OBagInsert (EAtom (AEmptyBag t)) r).

Definition split_filter_proj_head (e : expr) : expr :=
  match e with
  | EFlatmap LikeBag l x
      (EIf p (EBinop OBagInsert (EAtom (AEmptyBag t)) r) (EAtom (AEmptyBag _))) =>
      if is_the_bound_row x r then e else filter_then_proj l x p r t
  | _ => e
  end.

Section WithWord.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Notation value := (value).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  (* Projecting after a flat_map is projecting inside it. *)
  Lemma map_flat_map : forall A B C (f : B -> C) (g : A -> list B) l,
      map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
  Proof.
    induction l; cbn; auto.
    rewrite map_app, IHl; reflexivity.
  Qed.

  Lemma flat_map_ext : forall A B (f g : A -> list B) l,
      (forall v, f v = g v) -> flat_map f l = flat_map g l.
  Proof. intros; apply flat_map_eq, Forall_forall; auto. Qed.

  Lemma bag_to_list_singleton : forall (v : value),
      bag_to_list (bag_insert v nil) = [v].
  Proof. reflexivity. Qed.

  Lemma split_filter_proj_head_preserve_ty : forall (Gstore : tenv),
      preserve_ty Gstore split_filter_proj_head.
  Proof.
    unfold preserve_ty; intros * H_Gs H_Ge H_ty.
    unfold split_filter_proj_head.
    repeat destruct_subexpr.
    case_match; [ assumption | ].
    repeat invert_type_of_clear.
    repeat invert_type_of_op_clear.
    lazymatch goal with
    | H: type_of _ _ e1 (TBag ?rt) |- _ =>
        assert (type_wf rt) by
          (apply type_of__type_wf in H; auto; invert_type_wf; assumption)
    end.
    unfold filter_then_proj.
    apply TyEFlatmap_Bag with (t1 := t2).
    - apply TyEFlatmap_Bag with (t1 := t2); [ assumption | ].
      apply TyEIf; [ assumption | | ].
      + eapply TyEBinop; [ apply TyOBagInsert | | ].
        * apply TyEAtom, TyAEmptyBag'; assumption.
        * apply TyEVar, map.get_put_same.
      + apply TyEAtom, TyAEmptyBag'; assumption.
    - eapply TyEBinop; [ apply TyOBagInsert | | ].
      + apply TyEAtom; assumption.
      + assumption.
  Qed.

  Lemma split_filter_proj_head_preserve_sem :
    forall (Gstore : tenv) (store : locals),
      preserve_sem Gstore store split_filter_proj_head.
  Proof.
    unfold preserve_sem; intros * H_Gs H_Ge H_ty H_st H_en.
    unfold split_filter_proj_head.
    repeat destruct_subexpr.
    case_match; [ reflexivity | ].
    invert_type_of_clear.
    apply_type_sound e1. invert_type_of_value_clear.
    unfold filter_then_proj.
    cbn [interp_expr interp_binop interp_atom].
    rewrite <- H.
    cbn [interp_expr interp_binop interp_atom].
    f_equal.
    assert (Hin : forall v,
               match match interp_expr store (map.put env x v) e2_1 with
                     | VBool true =>
                         VBag (bag_insert (get_local (map.put env x v) x) nil)
                     | VBool false => VBag nil
                     | _ => VUnit
                     end with
               | VBag l2 => bag_to_list l2
               | _ => nil
               end
               = match interp_expr store (map.put env x v) e2_1 with
                 | VBool true => [v]
                 | _ => nil
                 end).
    { intros. destruct (interp_expr store (map.put env x v) e2_1); cbn; auto.
      destruct b; auto.
      unfold get_local. rewrite map.get_put_same; reflexivity. }
    assert (Hone : forall v,
               match match interp_expr store (map.put env x v) e2_1 with
                     | VBool true =>
                         VBag (bag_insert
                                 (interp_expr store (map.put env x v) e2_2_2) nil)
                     | VBool false => VBag nil
                     | _ => VUnit
                     end with
               | VBag l2 => bag_to_list l2
               | _ => nil
               end
               = match interp_expr store (map.put env x v) e2_1 with
                 | VBool true => [interp_expr store (map.put env x v) e2_2_2]
                 | _ => nil
                 end).
    { intros. destruct (interp_expr store (map.put env x v) e2_1); cbn; auto.
      destruct b; reflexivity. }
    rewrite (flat_map_ext _ _ _ _ _ Hin), (flat_map_ext _ _ _ _ _ Hone).
    assert (Hout : forall X : list value,
               flat_map
                 (fun v => bag_to_list
                             (bag_insert
                                (interp_expr store (map.put env x v) e2_2_2) nil)) X
               = map (fun v => interp_expr store (map.put env x v) e2_2_2) X).
    { induction X; cbn; auto. }
    rewrite Hout.
    rewrite (Permutation_list_to_bag_eq
               _ (map (fun v => interp_expr store (map.put env x v) e2_2_2)
                    (flat_map
                       (fun v => match interp_expr store (map.put env x v) e2_1 with
                                 | VBool true => [v]
                                 | _ => nil
                                 end) (bag_to_list l)))).
    2:{ apply Permutation_map, list_to_bag_to_list_Permutation. }
    f_equal.
    rewrite map_flat_map.
    apply flat_map_ext; intros.
    destruct (interp_expr store (map.put env x v) e2_1); cbn; auto.
    destruct b; reflexivity.
  Qed.

  Lemma split_filter_proj_head_sound :
    expr_transf_sound (locals:=locals) split_filter_proj_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply split_filter_proj_head_preserve_ty; auto.
    eapply split_filter_proj_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithWord.

#[export] Hint Resolve split_filter_proj_head_sound : transf_hints.
