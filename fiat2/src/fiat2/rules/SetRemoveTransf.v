Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.TransfSound fiat2.rules.CollectionTransf fiat2.rules.FlatmapForms.
Require Import coqutil.Map.Interface.
From Stdlib Require Import List String ZArith.
Import ListNotations.

Open Scope string_scope.

(* Removing one element from a set as a result of filtering, without a rebuild.

   It fires on any set-level filter of this shape, and it is sound for every set,
   which is why it lives in its own file. *)

Definition filter_neq_to_set_remove_head (e : expr) : expr :=
  match e with
  | flatmap_filter_set s x (EUnop ONot (EBinop OEq (EVar x0) k)) x1 _ _ =>
      if (all_eqb [(x, [x0; x1])] && negb (free_immut_in x k))%bool
      then EBinop OSetDiff s (EBinop OSetInsert (EAtom (AEmptySet None)) k)
      else e
  | _ => e
  end.

Section WithWord.
  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Lemma filter_neq_to_set_remove_head_preserve_ty : forall (Gstore : tenv),
        preserve_ty Gstore filter_neq_to_set_remove_head.
    Proof.
      unfold preserve_ty; intros.
      repeat destruct_subexpr. unfold filter_neq_to_set_remove_head.
      cbv beta iota; case_match; auto.
      cbn [all_eqb all_eqb' andb] in *.
      repeat rewrite Bool.andb_true_iff in *; intuition idtac.
      rewrite Bool.negb_true_iff, eqb_eq in *; subst.
      repeat invert_type_of_clear; repeat invert_type_of_op_clear.
      repeat rewrite_map_get_put_hyp; repeat do_injection.
      lazymatch goal with
        H_k : type_of _ (map.put _ ?y _) ?k _, H_fr : free_immut_in ?y ?k = false |- _ =>
          eapply not_free_immut_put_ty in H_k; [ | exact H_fr ]
      end.
      (* OSetDiff takes two sets of the same element type: the table's own,
         and the singleton built from the removed element *)
      econstructor; [ constructor | eassumption | ].
      econstructor; [ constructor | | eassumption ].
      econstructor. econstructor.
      lazymatch goal with
        H_k : type_of _ _ _ ?kt |- type_wf ?kt =>
          eapply type_of__type_wf; [ | | exact H_k ]
      end; assumption.
    Qed.

    Lemma filter_neq_to_set_remove_head_preserve_sem :
      forall (Gstore : tenv) (store : locals),
        preserve_sem Gstore store filter_neq_to_set_remove_head.
    Proof.
      unfold preserve_sem; intros.
      repeat destruct_subexpr. unfold filter_neq_to_set_remove_head.
      cbv beta iota; case_match; auto.
      cbn [all_eqb all_eqb' andb] in *.
      repeat rewrite Bool.andb_true_iff in *; intuition idtac.
      rewrite Bool.negb_true_iff, eqb_eq in *; subst.
      repeat invert_type_of_clear; repeat invert_type_of_op_clear.
      repeat rewrite_map_get_put_hyp; repeat do_injection.
      apply_type_sound e1. invert_type_of_value_clear.
      rewrite interp_flatmap_filter_set.
      cbn [interp_expr].
      lazymatch goal with H : _ = interp_expr _ _ e1 |- _ => rewrite <- H end.
      cbn [interp_binop interp_unop interp_atom set_insert set_mem existsb orb].
      f_equal.
      assert (H_ext :
               filter (fun v : value =>
                         negb (value_eqb (get_local (map.put env x v) x)
                                 (interp_expr store (map.put env x v) e2_1_2))) l
               = filter (fun v : value =>
                           negb (value_eqb v (interp_expr store env e2_1_2) || false)) l).
      { apply In_filter_ext; intros v H_in.
        unfold get_local. rewrite map.get_put_same, Bool.orb_false_r.
        do 2 f_equal. symmetry. apply not_free_immut_put_sem; assumption. }
      rewrite H_ext.
      symmetry. apply list_to_set_canonical;
        auto using NoDup_filter, SSorted_filter.
    Qed.

    Lemma filter_neq_to_set_remove_head_sound :
      expr_transf_sound (locals:=locals) filter_neq_to_set_remove_head.
    Proof.
      unfold expr_transf_sound; split; intros.
      1: apply filter_neq_to_set_remove_head_preserve_ty; auto.
      eapply filter_neq_to_set_remove_head_preserve_sem; resolve_locals_wf; eauto.
    Qed.
  End WithMap.
End WithWord.

#[export] Hint Resolve filter_neq_to_set_remove_head_sound : transf_hints.
