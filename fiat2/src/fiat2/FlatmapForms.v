Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.Utils fiat2.CollectionTransf.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
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
     (EIf p (EBinop OBagInsert (EBagOf (EAtom (ANil t1))) (EVar y)) (EBagOf (EAtom (ANil t2))))).

Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Local Notation value := (Value.value (word := word)).

  Section WithMap.
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

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
  End WithMap.

  Lemma list_to_bag_filter_list_to_bag : forall P (l : list value),
      list_to_bag (filter P (bag_to_list (list_to_bag l))) = list_to_bag (filter P l).
  Proof.
    intros. apply Permutation_list_to_bag_eq, Permutation_filter; auto.
    apply list_to_bag_to_list_Permutation.
  Qed.
End WithWord.
