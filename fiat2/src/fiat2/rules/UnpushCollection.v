Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.rules.CollectionTransf fiat2.rules.FlatmapForms fiat2.TransfSound fiat2.TransfUtils.
Require Import coqutil.Map.Interface.
From Stdlib Require Import List String ZArith.
Import ListNotations.

(* Taking a collection coercion back out of a filter.

   push_down_collection drives OBagOfList and OSetOfList inward, and that is what
   makes the index rules applicable.

   But a demand no index answers is a cost. Where an index absorbs
   the inner coercion, it pays.  Where nothing absorbs it, the program
   builds a bag/set of the whole table and discards most of it.

   So this rule runs AFTER the index phase and undoes the push-down exactly
   where the index phase declined it.  Its guard is the absorption itself.
   The pattern requires the coercion still to be sitting on the filter's
   input, and it is still sitting there only if no rule took it; where one
   did, the pattern does not match and this rule is the identity. *)

(* set_of descends into exactly four shapes; everywhere else it stops and
   wraps its argument. *)
Definition set_of_stops (e : expr) : bool :=
  match e with
  | EFlatmap LikeList _ _ _ => false
  | EBinop OCons _ _ => false
  | EIf _ _ _ => false
  | EAtom (ANil _) => false
  | _ => true
  end.

Lemma set_of_stops_eq : forall e, set_of_stops e = true -> set_of e = EUnop OSetOfList e.
Proof.
  intros e H; destruct e; cbn in H |- *; try reflexivity.
  1: destruct a; cbn in H |- *; try reflexivity; discriminate.
  1: destruct o; cbn in H |- *; try reflexivity; discriminate.
  1: discriminate.
  1: destruct tag; cbn in H |- *; try reflexivity; discriminate.
Qed.

(* The rule.  The coercion is still on the filter's input, which is the
   whole of the side condition. *)
Definition unpush_set_filter_head (e : expr) : expr :=
  match e with
  | flatmap_filter_set (EUnop OSetOfList src) x p y t1 t2 =>
      if (String.eqb x y && set_of_stops src)%bool
      then EUnop OSetOfList (flatmap_filter_list src x p y t1 t2)
      else e
  | _ => e
  end.

Lemma unpush_is_set_of : forall src x p t1 t2,
    set_of_stops src = true ->
    set_of (flatmap_filter_list src x p x t1 t2)
    = flatmap_filter_set (EUnop OSetOfList src) x p x t1 t2.
Proof.
  intros * H. cbn [set_of]. rewrite set_of_stops_eq by assumption. reflexivity.
Qed.

Section WithMap.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Notation value := (value).
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  (* The emitted term is well typed at the list level. *)
  Lemma unpush_inner_ty : forall (Gstore Genv : tenv) src x p t1 t2 t,
      type_of Gstore Genv (flatmap_filter_set (EUnop OSetOfList src) x p x t1 t2) (TSet t) ->
      type_of Gstore Genv (flatmap_filter_list src x p x t1 t2) (TList t).
  Proof.
    intros * H.
    repeat invert_type_of_clear; repeat invert_type_of_op_clear.
    rewrite map.get_put_same in *.
    injection H1 as H1; subst.
    econstructor.
    1: eassumption.
    econstructor.
    1: eassumption.
    2:{ constructor. inversion H0; subst; constructor; assumption. }
    econstructor.
    1: constructor.
    1: constructor; rewrite map.get_put_same; reflexivity.
    constructor. inversion H4; subst; constructor; assumption.
  Qed.

  Lemma unpush_set_filter_head_preserve_ty : forall (Gstore : tenv),
      preserve_ty Gstore unpush_set_filter_head.
  Proof.
    unfold preserve_ty; intros * H_Gs H_Ge H_ty.
    repeat destruct_subexpr; cbn [unpush_set_filter_head].
    case_match; auto.
    rewrite Bool.andb_true_iff in *; intuition idtac.
    rewrite eqb_eq in *; subst.
    assert (H_shape : exists t', t = TSet t') by (inversion H_ty; eauto).
    destruct H_shape as [t' ->].
    econstructor; [ constructor | ]. apply unpush_inner_ty. assumption.
  Qed.

  Lemma unpush_set_filter_head_preserve_sem :
    forall (Gstore : tenv) (store : locals),
      preserve_sem Gstore store unpush_set_filter_head.
  Proof.
    unfold preserve_sem; intros * H_Gs H_Ge H_ty H_st H_en.
    repeat destruct_subexpr; cbn [unpush_set_filter_head].
    case_match; auto.
    rewrite Bool.andb_true_iff in *; intuition idtac.
    rewrite eqb_eq in *; subst.
    assert (H_shape : exists t', t = TSet t') by (inversion H_ty; eauto).
    destruct H_shape as [t' ->].
    lazymatch goal with
      H : set_of_stops _ = true |- _ =>
        rewrite <- (unpush_is_set_of _ _ _ _ _ H)
    end.
    erewrite set_of_sem with (Gstore := Gstore) (Genv := Genv) (t := t');
      eauto using unpush_inner_ty.
  Qed.

  Lemma unpush_set_filter_head_sound :
    expr_transf_sound (locals:=locals) unpush_set_filter_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply unpush_set_filter_head_preserve_ty; auto.
    eapply unpush_set_filter_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithMap.

#[export] Hint Resolve unpush_set_filter_head_sound : transf_hints.
