Require Import conquord.Language conquord.Interpret conquord.Value conquord.TypeSystem conquord.TypeSound conquord.Notations
  conquord.TransfUtils conquord.RelTransf conquord.TransfSound.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface.
Require Import List String ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Section WithConcreteMap.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.

  Instance tenv : map.map string type := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.

  Instance locals : map.map string (value (word:=word)) := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

Definition ex1 : expr := <[ let "scores" = [ {"s": 1} ] in
                              "x" <- "scores";
                              check(80 < "x"["s"]);
                              ret "x" ]>.

  Definition e_nil := EAtom (ANil None).
  Definition e_singleton e := EBinop OCons e e_nil.
  Definition e_check p e := EIf p e e_nil.

  Goal ex1 = ELet
               (EBinop OCons (ERecord (("s", EAtom (AInt 1)) :: nil)) e_nil)
               "scores"
               (EFlatmap LikeList
                  (EVar "scores") "x"
                  (e_check (EBinop OLess (EAtom (AInt 80))
                              (EAccess (EVar "x") "s")) (e_singleton (EVar "x")))).
    reflexivity. Abort.

  (* Definition typed_ex1 := synthesize_expr map.empty map.empty ex1.
  Compute typed_ex1.
  Compute (fold_expr to_filter_head ex1). *)

  Definition ex2 : expr :=
    <["x" <- mut "scores";
      "n" <- mut "names";
      check("x"["s_id"] == "n"["n_id"]);
        ret {"name": "n"["n_name"], "score": "x"["s_score"]} ]>.
  Goal ex2 = EFlatmap LikeList (ELoc "scores") "x"
               (EFlatmap LikeList (ELoc "names") "n"
                  (EIf (EBinop OEq (EAccess (EVar "x") "s_id") (EAccess (EVar "n") "n_id"))
                     (EBinop OCons
                        (ERecord (("name", EAccess (EVar "n") "n_name") :: ("score", EAccess (EVar "x") "s_score") :: nil))
                        (EAtom (ANil None)))
                     (EAtom (ANil None)))).
    reflexivity. Abort.

  (* Compute to_join_head ex2. *)

  Definition ex3 : expr :=
    <[ "p" <- mut "persons";
       "e" <- mut "employees";
       check("p"["age"] < 40 && "p"["id"] == "e"["id"]);
       ret {"name": "p"["name"], "salary": "e"["salary"]}
      ]>.
  Goal ex3 = EFlatmap LikeList
      (ELoc "persons") "p"
      (EFlatmap LikeList
         (ELoc "employees") "e"
         (EIf
            (EBinop OAnd
               (EBinop OLess
                  (EAccess (EVar "p") "age")
                  (EAtom (AInt 40)))
               (EBinop OEq
                  (EAccess (EVar "p") "id")
                  (EAccess (EVar "e") "id")))
            (EBinop OCons
               (ERecord (("name", EAccess (EVar "p") "name") :: ("salary", EAccess (EVar "e") "salary") :: nil))
               (EAtom (ANil None)))
            (EAtom (ANil None)))).
    reflexivity. Abort.
  (* Compute (fold_expr to_join_head ex3).
  Compute (fold_expr filter_pushdown_head (fold_expr to_join_head ex3)). *)
  (* Compute ex3. *)

  Definition ex3_op := fold_expr filter_pushdown_head (fold_expr to_join_head ex3).
  (* Compute ex3_op. *)

  Lemma ex3_op_equiv_ex3 : forall Gstore Genv t (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv ->
      type_of Gstore Genv ex3 t ->
      locals_wf Gstore store ->
      locals_wf Genv env ->
      type_of Gstore Genv ex3_op t /\ interp_expr store env ex3 = interp_expr store env ex3_op.
  Proof.
    intros; unfold ex3_op. split.
    - repeat (apply fold_expr_preserve_ty; auto using filter_pushdown_head_preserve_ty, to_join_head_preserve_ty).
    - erewrite fold_expr_preserve_sem with (Gstore := Gstore); eauto using filter_pushdown_head_preserve_ty, filter_pushdown_head_preserve_sem.
      + erewrite fold_expr_preserve_sem with (Gstore := Gstore); eauto using to_join_head_preserve_ty, to_join_head_preserve_sem.
      + apply fold_expr_preserve_ty; eauto using filter_pushdown_head_preserve_ty, to_join_head_preserve_ty.
  Qed.
End WithConcreteMap.
