Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils fiat2.CollectionTransf.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation.
Import ListNotations.

(* Derived forms: relational operations written as flatmaps.
   The variable bound by the flatmap and the variable in the singleton
   are separate parameters so that the notations can be used as patterns;
   a rewrite using a pattern checks that they are equal. *)

(* filter e x p, as written in the source: [x <- e, check(p), ret x] *)
Notation flatmap_filter_list e x p y t1 t2 :=
  (EFlatmap LikeList e x
     (EIf p (EBinop OCons (EVar y) (EAtom (ANil t1))) (EAtom (ANil t2)))).

(* The bag version of flatmap_filter_list, as produced by bag_of *)
Notation flatmap_filter_bag e x p y t1 t2 :=
  (EFlatmap LikeBag e x
     (EIf p (EBinop OBagInsert (EAtom (AEmptyBag t1)) (EVar y)) (EAtom (AEmptyBag t2)))).

(* map e x r on bags, as produced by bag_of from [x <- e, ret r] *)
Notation flatmap_proj_bag e x r t :=
  (EFlatmap LikeBag e x (EBinop OBagInsert (EAtom (AEmptyBag t)) r)).

(* map e x r on sets, as produced by set_of from [x <- e, ret r] *)
Notation flatmap_proj_set e x r t :=
  (EFlatmap LikeSet e x (EBinop OSetInsert (EAtom (AEmptySet t)) r)).

Lemma flat_map_singleton : forall A B (f : A -> B) l,
    flat_map (fun v => [f v]) l = map f l.
Proof.
  induction l; cbn; congruence.
Qed.

(* rewrite does not infer the function in flat_map_singleton, so match it explicitly *)
Ltac rewrite_flat_map_singleton :=
  repeat lazymatch goal with
    |- context[flat_map (fun v => [@?g v]) ?l] =>
      rewrite (flat_map_singleton _ _ g l)
    end.

Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Local Notation value := (Value.value (word := word)).

  Section WithMap.
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    (* the flatmap's bound variable is the row the attribute is read from *)
    (* projecting an attribute out of well-typed records gives values of its type *)
    Lemma Forall_map_record_proj : forall (attr : string) (l : list value) tl t,
        Forall (fun v => type_of_value v (TRecord tl)) l ->
        access_record tl attr = Success t ->
        Forall (fun v => type_of_value v t)
          (List.map (fun v => match v with
                              | VRecord r => record_proj attr r
                              | _ => VUnit
                              end) l).
    Proof.
      intros * H_l H_attr. rewrite Forall_map, Forall_forall; intros v H_in.
      rewrite Forall_forall in H_l; apply H_l in H_in.
      invert_type_of_value_clear.
      eapply record_proj_sound; eauto using access_record_sound.
      (* the record's field names are the type's field names *)
      lazymatch goal with
        H: Forall2 _ _ _ |- _ =>
          apply Forall2_split in H as [H _]; apply Forall2_fst_eq in H; rewrite H
      end; auto.
    Qed.

    Lemma map_proj_put : forall (attr : string) (env : locals) y l,
        List.map (fun v => match get_local (map.put env y v) y with
                           | VRecord r => record_proj attr r
                           | _ => VUnit
                           end) l
        = List.map (fun v => match v with
                             | VRecord r => record_proj attr r
                             | _ => VUnit
                             end) l.
    Proof.
      intros. apply map_ext; intros.
      unfold get_local. rewrite map.get_put_same. reflexivity.
    Qed.

    (* the predicate of a delete tests the row's attribute against a key that
       does not depend on the row *)
    Lemma filter_pred_neq : forall (attr : string) (store env : locals) y k l,
        free_immut_in y k = false ->
        filter (fun v => match interp_expr store (map.put env y v)
                                 (EUnop ONot (EBinop OEq (EAccess (EVar y) attr) k)) with
                         | VBool b => b
                         | _ => false
                         end) l
        = filter (fun v => negb (value_eqb
                                   (match v with
                                    | VRecord r => record_proj attr r
                                    | _ => VUnit
                                    end)
                                   (interp_expr store env k))) l.
    Proof.
      intros. apply In_filter_ext; intros.
      cbn [interp_expr interp_unop interp_binop].
      unfold get_local. rewrite map.get_put_same.
      rewrite <- not_free_immut_put_sem; auto.
    Qed.

    Lemma interp_EVar : forall (store env : locals) y,
        interp_expr store env (EVar y) = get_local env y.
    Proof. reflexivity. Qed.

    Lemma interp_EOptMatch : forall (store env : locals) e e_none y e_some,
        interp_expr store env (EOptMatch e e_none y e_some) =
          match interp_expr store env e with
          | VOption (Some v) => interp_expr store (map.put env y v) e_some
          | VOption None => interp_expr store env e_none
          | _ => VUnit
          end.
    Proof. reflexivity. Qed.

    Lemma interp_EIf : forall (store env : locals) e1 e2 e3,
        interp_expr store env (EIf e1 e2 e3) =
          match interp_expr store env e1 with
          | VBool b => if b then interp_expr store env e2 else interp_expr store env e3
          | _ => VUnit
          end.
    Proof. reflexivity. Qed.

    Lemma interp_EBinop : forall (store env : locals) o e1 e2,
        interp_expr store env (EBinop o e1 e2) =
          interp_binop o (interp_expr store env e1) (interp_expr store env e2).
    Proof.
      reflexivity.
    Qed.
    Lemma interp_EBagOf : forall (store env : locals) e,
        interp_expr store env (EBagOf e) =
          match interp_expr store env e with
          | VList l => VBag (list_to_bag l)
          | _ => VUnit
          end.
    Proof. reflexivity. Qed.

    (* a delete tests the attribute against the key, so the rows it keeps are
       exactly the complement of the rows it removes *)
    Lemma filter_pred_not_eq : forall (attr : string) (store env : locals) y k l,
        filter (fun v => match interp_expr store (map.put env y v)
                                 (EUnop ONot (EBinop OEq (EAccess (EVar y) attr) k)) with
                         | VBool b => b
                         | _ => false
                         end) l
        = filter (fun v => negb (match interp_expr store (map.put env y v)
                                         (EBinop OEq (EAccess (EVar y) attr) k) with
                                 | VBool b => b
                                 | _ => false
                                 end)) l.
    Proof.
      intros. apply In_filter_ext; intros.
      cbn [interp_expr interp_unop interp_binop]. reflexivity.
    Qed.

    Lemma interp_ESetOf : forall (store env : locals) e,
        interp_expr store env (ESetOf e) =
          match interp_expr store env e with
          | VList l => VSet (list_to_set l)
          | _ => VUnit
          end.
    Proof.
      reflexivity.
    Qed.
    Lemma interp_flatmap_proj_set : forall (store env : locals) e y r t,
        interp_expr store env (flatmap_proj_set e y r t) =
          match interp_expr store env e with
          | VSet l =>
              VSet (list_to_set
                      (List.map (fun v => interp_expr store (map.put env y v) r) l))
          | _ => VUnit
          end.
    Proof.
      intros. cbn [interp_expr]. case_match; auto.
    Qed.

    Lemma interp_flatmap_filter_list : forall (store env : locals) e x p t1 t2,
        interp_expr store env (flatmap_filter_list e x p x t1 t2) =
          match interp_expr store env e with
          | VList l =>
              VList (filter (fun v => match interp_expr store (map.put env x v) p with
                                      | VBool b => b
                                      | _ => false
                                      end) l)
          | _ => VUnit
          end.
    Proof.
      intros. cbn [interp_expr]. destruct (interp_expr store env e); auto.
      f_equal. induction l as [| v l' IH]; auto.
      cbn [flat_map filter]. rewrite IH.
      unfold get_local. rewrite map.get_put_same.
      case_match; auto.
      destruct b; auto.
    Qed.

    Lemma interp_flatmap_filter_bag : forall (store env : locals) e x p t1 t2,
        interp_expr store env (flatmap_filter_bag e x p x t1 t2) =
          match interp_expr store env e with
          | VBag l =>
              VBag (list_to_bag
                      (filter (fun v => match interp_expr store (map.put env x v) p with
                                        | VBool b => b
                                        | _ => false
                                        end) (bag_to_list l)))
          | _ => VUnit
          end.
    Proof.
      intros. cbn [interp_expr]. case_match; auto.
      do 2 f_equal. induction (bag_to_list l) as [| v l' IH]; auto.
      cbn [flat_map filter]. rewrite IH.
      unfold get_local. rewrite map.get_put_same.
      case_match; auto.
      destruct b; auto.
    Qed.

    Lemma interp_flatmap_proj_bag : forall (store env : locals) e x r t,
        interp_expr store env (flatmap_proj_bag e x r t) =
          match interp_expr store env e with
          | VBag l =>
              VBag (list_to_bag
                      (map (fun v => interp_expr store (map.put env x v) r) (bag_to_list l)))
          | _ => VUnit
          end.
    Proof.
      (* the flat_map of singletons is convertible to the map *)
      intros. cbn [interp_expr]. destruct (interp_expr store env e); reflexivity.
    Qed.

    (* Unfolds interp_expr on EACFold by one step, leaving its argument unevaluated *)
    Lemma interp_EACFold : forall (store env : locals) ag e,
        interp_expr store env (EACFold ag e) =
          let '(zr, op) := interp_aggr ag in
          match interp_expr store env e with
          | VBag l => fold_right op zr (bag_to_list l)
          | _ => VUnit
          end.
    Proof.
      reflexivity.
    Qed.
  End WithMap.

  Lemma list_to_bag_filter_list_to_bag : forall P (l : list value),
      list_to_bag (filter P (bag_to_list (list_to_bag l))) = list_to_bag (filter P l).
  Proof.
    intros. apply Permutation_list_to_bag_eq, Permutation_filter; auto.
    apply list_to_bag_to_list_Permutation.
  Qed.
End WithWord.
