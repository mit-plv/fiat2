Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.TransfSound fiat2.CollectionTransf fiat2.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
From Stdlib Require Import List String ZArith Permutation.
Import ListNotations.

Open Scope string_scope.

(* An existence test does not need a bag.

   "Is there a row whose key is k" is asked, in the source, by filtering the
   table and testing the result for emptiness.  The answer does not depend on
   how many such rows there are, so it does not depend on the multiplicities a
   bag carries: the test can be answered by the SET of the table's keys, which
   is a much smaller thing to maintain than a key-to-row dictionary.

   That is what the rewrite below does.  It is an ordinary rewrite -- it fires
   on a syntactic pattern, it is sound for every table, and it has nothing to
   do with any declaration.  A primary-key check is its most useful instance,
   but a check is not a declaration: the rewrite would fire the same way on a
   table with duplicate keys, and would still be right.  What a declaration
   buys is the other rewrite, the one that returns the row itself. *)

(* [x <- e1, check(x.attr = k)] = (bag) empty  -->  not (k in {x.attr | x <- e1})

   The rewrite is stated on the bag form, which is what the collection phase
   leaves an emptiness test in, and it produces the set form, which is what a
   set index of the attribute is. *)
Definition filter_eq_empty_to_set_mem_head (e : expr) : expr :=
  match e with
  | EBinop OEq
      (flatmap_filter_bag (EBagOf e1) x0 (EBinop OEq (EAccess (EVar x1) attr) k) x2 _ _)
      (EAtom (AEmptyBag _)) =>
      if (all_eqb [(x0, [x1; x2])] && negb (free_immut_in x0 k))%bool
      then EUnop ONot
             (EBinop OSetMem
                (flatmap_proj_set (ESetOf e1) x0 (EAccess (EVar x0) attr) None) k)
      else e
  | _ => e
  end.

Section WithWord.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  (* one step of interp_expr, so that the derived-form lemmas below have a
     subterm to match on *)
  Lemma interp_EUnop_step : forall (store env : locals) o e,
      interp_expr store env (EUnop o e) = interp_unop o (interp_expr store env e).
  Proof. reflexivity. Qed.

  Lemma interp_EBinop_step : forall (store env : locals) o e1 e2,
      interp_expr store env (EBinop o e1 e2)
      = interp_binop o (interp_expr store env e1) (interp_expr store env e2).
  Proof. reflexivity. Qed.

  Lemma bag_insert_not_nil : forall (v : value) b, bag_insert v b <> nil.
  Proof.
    intros v b; destruct b as [| [ v' n' ] b ]; cbn; [ discriminate | ].
    repeat case_match; discriminate.
  Qed.

  Lemma list_to_bag_nil_iff : forall (l : list value), list_to_bag l = nil <-> l = nil.
  Proof.
    intros l; split; [ | intros E; subst; reflexivity ].
    destruct l as [| v l ]; auto; cbn.
    intros H; exfalso; eapply bag_insert_not_nil, H.
  Qed.

  Lemma set_mem_true_iff : forall (v : value) l, set_mem v l = true <-> In v l.
  Proof.
    unfold set_mem; intros v l; rewrite existsb_exists; split.
    1:{ intros [ y [ H_in H_eq ] ]. apply value_eqb_eq in H_eq; subst; assumption. }
    1:{ intros H_in. exists v; split; [ assumption | apply value_eqb_refl ]. }
  Qed.

  (* the filter is empty exactly when no row has the key *)
  Lemma filter_key_eq_nil_iff :
    forall (key : value -> value) (k : value) (l : list value),
      filter (fun v => value_eqb (key v) k) l = nil <-> ~ In k (List.map key l).
  Proof.
    intros key k l; induction l as [| v l IH ]; cbn [filter List.map In].
    1: intuition auto.
    destruct (value_eqb_dec (key v) k) as [ E | E ].
    1:{ split; [ discriminate | intros H_ni; exfalso; auto ]. }
    1:{ rewrite IH; intuition auto. }
  Qed.

  (* and that is the same question as membership in the set of the keys, which
     is where the multiplicities drop out *)
  Lemma filter_empty_eq_not_set_mem :
    forall (key : value -> value) (k : value) (l : list value),
      value_eqb (VBag (list_to_bag (filter (fun v => value_eqb (key v) k) l))) (VBag nil)
      = negb (set_mem k (list_to_set (List.map key l))).
  Proof.
    intros key k l.
    destruct (set_mem k (list_to_set (List.map key l))) eqn:E_mem; cbn [negb].
    1:{ apply set_mem_true_iff, list_to_set_incl in E_mem.
        destruct (filter (fun v => value_eqb (key v) k) l) as [| v fl ] eqn:E_f.
        1:{ exfalso. revert E_mem.
            apply (proj1 (filter_key_eq_nil_iff key k l)); exact E_f. }
        destruct (value_eqb (VBag (list_to_bag (v :: fl))) (VBag nil)) eqn:E_eq; auto.
        apply value_eqb_eq in E_eq. injection E_eq as E_b.
        exfalso. cbn in E_b. eapply bag_insert_not_nil, E_b. }
    1:{ rewrite (proj2 (filter_key_eq_nil_iff key k l)).
        1: apply value_eqb_refl.
        intros H_in.
        apply list_to_set_incl_r, (proj2 (set_mem_true_iff _ _)) in H_in.
        congruence. }
  Qed.

  Lemma filter_eq_empty_to_set_mem_head_preserve_ty : forall (Gstore : tenv),
      preserve_ty Gstore filter_eq_empty_to_set_mem_head.
  Proof.
    unfold preserve_ty; intros.
    repeat destruct_subexpr. unfold filter_eq_empty_to_set_mem_head.
    cbv beta iota; case_match; auto.
    cbn [all_eqb all_eqb' andb] in *.
    repeat rewrite Bool.andb_true_iff in *; intuition idtac.
    rewrite Bool.negb_true_iff, eqb_eq in *; subst.
    repeat invert_type_of_clear; repeat invert_type_of_op_clear.
    repeat rewrite_map_get_put_hyp; repeat do_injection.
    (* the key expression is typed inside the filter's scope, and the rewrite
       moves it out; it may, because it does not mention the bound variable *)
    lazymatch goal with
      H_k : type_of _ (map.put _ ?y _) ?k _, H_fr : free_immut_in ?y ?k = false |- _ =>
        eapply not_free_immut_put_ty in H_k; [ | exact H_fr ]
    end.
    (* the key's type is pinned by the key expression, so the membership test
       is built from the outside in *)
    econstructor; [ constructor | ].
    econstructor; [ constructor | | eassumption ].
    econstructor; [ econstructor; eassumption | ].
    econstructor; [ constructor | | ].
    1:{ econstructor. econstructor.
        (* the key expression's typing comes first: it is what pins the two
           environments, which eassumption would otherwise guess wrong *)
        lazymatch goal with
          H_k : type_of _ _ _ ?kt |- type_wf ?kt =>
            eapply type_of__type_wf; [ | | exact H_k ]
        end; assumption. }
    1:{ econstructor; [ econstructor; apply map.get_put_same | eassumption ]. }
  Qed.

  Lemma filter_eq_empty_to_set_mem_head_preserve_sem :
    forall (Gstore : tenv) (store : locals),
      preserve_sem Gstore store filter_eq_empty_to_set_mem_head.
  Proof.
    unfold preserve_sem; intros.
    repeat destruct_subexpr. unfold filter_eq_empty_to_set_mem_head.
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
    apply_type_sound e1_1. invert_type_of_value_clear.
    rewrite interp_EUnop_step, !interp_EBinop_step.
    rewrite interp_flatmap_filter_bag, interp_flatmap_proj_set, interp_ESetOf.
    cbn [interp_expr interp_unop interp_binop interp_atom].
    rewrite <- H1.
    (* the key function the two sides share *)
    erewrite map_ext with
      (g := fun v : value =>
              match v with VRecord l0 => record_proj s l0 | _ => VUnit end).
    2:{ intros. unfold get_local. rewrite map.get_put_same. reflexivity. }
    erewrite In_filter_ext with
      (g := fun v : value =>
              value_eqb
                match v with VRecord l0 => record_proj s l0 | _ => VUnit end
                (interp_expr store env e1_2_1_2)).
    2:{ intros v H_in. unfold get_local. rewrite map.get_put_same.
        f_equal. symmetry. apply not_free_immut_put_sem; assumption. }
    (* neither side cares that the rows were deduplicated or re-counted *)
    rewrite list_to_set_map_list_to_set, list_to_bag_filter_list_to_bag.
    f_equal. symmetry. apply filter_empty_eq_not_set_mem.
  Qed.

  Lemma filter_eq_empty_to_set_mem_head_sound :
    expr_transf_sound (locals:=locals) filter_eq_empty_to_set_mem_head.
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply filter_eq_empty_to_set_mem_head_preserve_ty; auto.
    eapply filter_eq_empty_to_set_mem_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithWord.

#[export] Hint Resolve filter_eq_empty_to_set_mem_head_sound : transf_hints.
