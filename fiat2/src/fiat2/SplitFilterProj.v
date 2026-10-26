Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.TransfUtils fiat2.TransfSound fiat2.FlatmapForms fiat2.CollectionTransf.
Require Import coqutil.Map.Interface.
From Stdlib Require Import List String ZArith Permutation.
Import ListNotations.

(* A flatmap that FILTERS AND PROJECTS AT ONCE is matched by nothing.

   The index rules are stated against two separate forms (FlatmapForms.v):

     flatmap_filter_bag e x p y   =  flatmap e x (if p then [y] else [])
     flatmap_proj_bag   e x r     =  flatmap e x [r]

   and the notation for the first fixes its then-branch as a VARIABLE -- the
   bound row itself.  So `unique_lookup_head` (UniqueIndexUse.v) and its
   siblings see a filter only when the filter hands back the whole row.

   A source query that asks for one FIELD of the matching row,

     [ r.level | r <- records, r.var == k ]

   is a single flatmap whose body is `if p then [r.level] else []`.  That is
   neither form, so no rule claims it and the read stays a scan -- even
   though the dictionary that would answer it may already be installed.  Five
   of the eight reads in eval/Sat4j_LiteralStorage.v are written this way; it
   is a third-party specification, which is how the gap was found.

   WHAT THIS IS, EXACTLY: the BAG-LEVEL COUNTERPART OF AN EXISTING RULE.
   `if_nil_into_flatmap_head` (FlatmapTransf.v) performs this same split
   at LikeList, with the same guard and for the same stated reason, and it is
   in the standard basics list -- which is why a join written as a LIST
   comprehension is already indexed today (Ex_Join.v pins that).  What was
   missing is the LikeBag case, and it is reachable: a read that the
   collection phase relaxes to bag level before any splitting -- an aggregate
   over `EBagOf` of a filtering projection -- arrives in this shape and
   `if_nil_into_flatmap_head`, matching LikeList and ANil, never sees it.

   This rule is narrower than its list-level sibling in one way, on purpose:
   the sibling splits `if p then BODY else nil` for any BODY, while this one
   requires BODY to be a singleton bag insert, which is the shape every
   witness has.  Generalising it would need `Permutation_flat_map` in place
   of `Permutation_map` in the proof below and has no witness asking for it.

   The rewrite:

     flatmap e x (if p then [r] else [])
       ==>  flatmap (flatmap e x (if p then [x] else [])) x [r]

   filter first, then project.  It is a normalisation and not an
   optimisation: it introduces no index, asks for none, and changes no
   behaviour.  What it buys is that the filter it leaves behind is in the
   shape the index rules read, so the rules already in the development become
   reachable from a shape sources commonly take.

   Two things to note about the statement.

   The guard is NOT cosmetic.  Without it the rule also matches a plain
   filter -- whose projection is the bound row -- and rewrites it to an
   identity map over itself, which is a wasted pass and, under repeated
   application, does not terminate.  `is_the_bound_row` declines exactly
   that case, so a filter is left alone and only a genuine projection is
   split.

   It is stated at BAG level only, because that is the level the index rules
   are stated at: the push-down leaves a bag-level filter, and
   flatmap_filter_bag is what the rules match.  A list- or set-level
   counterpart would need the corresponding rules to exist first.

   Why the semantics needs an argument at all: the filtered bag is
   re-canonicalised between the two passes, so the projection runs over a
   PERMUTATION of the rows the single flatmap would have projected.  Both
   sides are bags, and a bag is canonical (Value.v), so the two agree --
   but only because `list_to_bag` depends on the multiset and not the order,
   which is `Permutation_list_to_bag_eq`. *)

(* The projection is the bound row itself, i.e. this is a filter already and
   there is nothing to split out. *)
Definition is_the_bound_row (x : string) (r : expr) : bool :=
  match r with
  | EVar y => String.eqb x y
  | _ => false
  end.

(* filter, then project.  The filter's branches are left unannotated: they
   hold rows, whose type is not the type the original annotation names. *)
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

  (* Projecting after a flat_map is projecting inside it.  Stdlib has the
     concat form of flat_map but not this. *)
  Lemma map_flat_map : forall A B C (f : B -> C) (g : A -> list B) l,
      map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
  Proof.
    induction l; cbn; auto.
    rewrite map_app, IHl; reflexivity.
  Qed.

  Lemma flat_map_ext : forall A B (f g : A -> list B) l,
      (forall v, f v = g v) -> flat_map f l = flat_map g l.
  Proof. intros; apply flat_map_eq, Forall_forall; auto. Qed.

  (* a one-element bag, listed *)
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
    (* t2 is the row type, t3 the projected type.  The filter's branches are
       unannotated, which TyAEmptyBag' allows at any WELL FORMED type -- and
       the row type is well formed because the source has it. *)
    lazymatch goal with
    | H: type_of _ _ e1 (TBag ?rt) |- _ =>
        assert (type_wf rt) by
          (apply type_of__type_wf in H; auto; invert_type_wf; assumption)
    end.
    unfold filter_then_proj.
    apply TyEFlatmap_Bag with (t1 := t2).
    - (* the filter: same source, handing back the bound row *)
      apply TyEFlatmap_Bag with (t1 := t2); [ assumption | ].
      apply TyEIf; [ assumption | | ].
      + eapply TyEBinop; [ apply TyOBagInsert | | ].
        * apply TyEAtom, TyAEmptyBag'; assumption.
        * apply TyEVar, map.get_put_same.
      + apply TyEAtom, TyAEmptyBag'; assumption.
    - (* the projection, over the rows the filter kept, in the same binding *)
      eapply TyEBinop; [ apply TyOBagInsert | | ].
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
    (* The filter the split leaves behind keeps the BOUND ROW: the rebinding
       resolves, so its body is the plain predicate test. *)
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
    (* and the one-pass version keeps the PROJECTION *)
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
    (* the outer pass is a map *)
    assert (Hout : forall X : list value,
               flat_map
                 (fun v => bag_to_list
                             (bag_insert
                                (interp_expr store (map.put env x v) e2_2_2) nil)) X
               = map (fun v => interp_expr store (map.put env x v) e2_2_2) X).
    { induction X; cbn; auto. }
    rewrite Hout.
    (* A bag is canonical, so the re-canonicalisation between the two passes
       only permutes what the projection then runs over -- and list_to_bag
       depends on the multiset, not the order. *)
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
