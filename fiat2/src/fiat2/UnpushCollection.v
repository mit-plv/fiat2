Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.CollectionTransf fiat2.FlatmapForms fiat2.TransfSound fiat2.TransfUtils.
Require Import coqutil.Map.Interface.
From Stdlib Require Import List String ZArith.
Import ListNotations.

(* ====================================================================
   Taking a collection coercion back out of a filter.

   push_down_collection drives EBagOf and ESetOf inward, and that is what
   makes the index rules applicable at all: they are stated at bag and at
   set level, so a read the collection phase left at LIST level demands no
   index, and the coercion the push-down leaves on a table's read IS the
   demand an index answers.  Pushing less would cost every subject its
   indexes, so that is not what this file does.

   But a demand no index answers is a cost, and through a FILTER it is a
   cost that grows with the table.  The source writes ESetOf (filter p
   tbl), which coerces the rows the filter KEPT; the push-down rewrites it
   to filter_set p (ESetOf tbl), which coerces the rows the filter READS.
   Where an index absorbs the inner coercion -- RepIdx turns it into a
   field read -- the move pays.  Where nothing absorbs it, the program
   builds a set of the whole table on every evaluation and discards most of
   it: n log n comparisons where the source pays k log k.

   So this rule runs AFTER the index phase and undoes the push-down exactly
   where the index phase declined it.  Its guard is the absorption itself.
   The pattern requires the coercion still to be sitting on the filter's
   input, and it is still sitting there only if no rule took it; where one
   did, the pattern does not match and this rule is the identity.  Nothing
   has to be threaded in from the choice list, so the decision is local and
   the rule cannot disagree with the index phase about what happened.

   Soundness is not new reasoning.  set_of_sem already proves that set_of
   agrees with ESetOf on every list-typed expression, and the term matched
   below IS set_of of the term emitted, so the proof reads that theorem
   from right to left.
   ==================================================================== *)

(* set_of descends into exactly four shapes; everywhere else it stops and
   wraps its argument.  That is what lets the rule reconstruct the argument
   from the result, and this is the side condition saying so. *)
Definition set_of_stops (e : expr) : bool :=
  match e with
  | EFlatmap LikeList _ _ _ => false
  | EBinop OCons _ _ => false
  | EIf _ _ _ => false
  | EAtom (ANil _) => false
  | _ => true
  end.

Lemma set_of_stops_eq : forall e, set_of_stops e = true -> set_of e = ESetOf e.
Proof.
  intros e H; destruct e; cbn in H |- *; try reflexivity.
  1: destruct a; cbn in H |- *; try reflexivity; discriminate.
  1: destruct o; cbn in H |- *; try reflexivity; discriminate.
  1: discriminate.
  1: destruct tag; cbn in H |- *; try reflexivity; discriminate.
Qed.

(* The rule.  The coercion is still on the filter's INPUT, which is the
   whole of the side condition: if any index rule had taken it, this
   pattern would not match the term.  Both annotations travel unchanged,
   because set_of carries an ANil's annotation straight onto the
   AEmptySet it replaces it with. *)
Definition unpush_set_filter_head (e : expr) : expr :=
  match e with
  | flatmap_filter_set (ESetOf src) x p y t1 t2 =>
      if (String.eqb x y && set_of_stops src)%bool
      then ESetOf (flatmap_filter_list src x p y t1 t2)
      else e
  | _ => e
  end.

(* The term the rule matches IS set_of of the term it emits.  Everything
   below is this equation plus set_of_sem. *)
Lemma unpush_is_set_of : forall src x p t1 t2,
    set_of_stops src = true ->
    set_of (flatmap_filter_list src x p x t1 t2)
    = flatmap_filter_set (ESetOf src) x p x t1 t2.
Proof.
  intros * H. cbn [set_of]. rewrite set_of_stops_eq by assumption. reflexivity.
Qed.

Section WithMap.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Notation value := (value).
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  (* The emitted term is well typed at the list level.  Both preservation
     lemmas need this: one to put the coercion back around it, the other to
     apply set_of_sem to it.

     The only content is that the two annotations survive the move.  An
     AEmptySet's annotation is an ANil's, because that is what set_of put
     there, and in each of its two forms -- absent, or a type -- the atom
     rule for the list level asks for exactly what the atom rule for the set
     level supplied. *)
  Lemma unpush_inner_ty : forall (Gstore Genv : tenv) src x p t1 t2 t,
      type_of Gstore Genv (flatmap_filter_set (ESetOf src) x p x t1 t2) (TSet t) ->
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
    constructor. apply unpush_inner_ty. assumption.
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
    (* the matched term IS set_of of the emitted one, so what is left is
       set_of_sem at that term *)
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
