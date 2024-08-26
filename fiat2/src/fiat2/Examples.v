Require Import fiat2.Language fiat2.Interpret fiat2.TypeSystem fiat2.TypeSound fiat2.Notations.
Require Import fiat2.TypeSound.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface.
Require Import coqutil.Datatypes.Result.
Require Import ZArith String List.
Import ResultMonadNotations.

(* ??? TODO: move fold_expr to Optimize. *)
Section fold_expr.
  Context (f : expr -> expr).
  Fixpoint fold_expr (e : expr) :=
    f
      match e with
      | EVar _ | ELoc _ | EAtom _ => e
      | EUnop o e => EUnop o (fold_expr e)
      | EBinop o e1 e2 => EBinop o (fold_expr e1) (fold_expr e2)
      | EIf e1 e2 e3 => EIf (fold_expr e1) (fold_expr e2) (fold_expr e3)
      | ELet e1 x e2 => ELet (fold_expr e1) x (fold_expr e2)
      | EFlatmap e1 x e2 => EFlatmap (fold_expr e1) x (fold_expr e2)
      | EFold e1 e2 x y e3 => EFold (fold_expr e1) (fold_expr e2) x y (fold_expr e3)
      | ERecord l => ERecord (List.map (fun '(s, e) => (s, fold_expr e)) l)
      | EAccess e x => EAccess (fold_expr e) x
      | EDict l => EDict (List.map (fun '(e1, e2) => (fold_expr e1, fold_expr e2)) l)
      | EInsert d k v => EInsert (fold_expr d) (fold_expr k) (fold_expr v)
      | EDelete d k => EDelete (fold_expr d) (fold_expr k)
      | ELookup d k => ELookup (fold_expr d) (fold_expr k)
      | EOptMatch e e_none x e_some => EOptMatch (fold_expr e) (fold_expr e_none) x (fold_expr e_some)
      | EDictFold d e0 k v acc e => EDictFold (fold_expr d) (fold_expr e0) k v acc (fold_expr e)
      | ESort l => ESort (fold_expr l)
      | EFilter e x p => EFilter (fold_expr e) x (fold_expr p)
      | EJoin e1 e2 x y p r => EJoin (fold_expr e1) (fold_expr e2) x y (fold_expr p) (fold_expr r)
      | EProj e x r => EProj (fold_expr e) x (fold_expr r)
      end.
End fold_expr.

Section Examples.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.

  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.

  Instance locals : map.map string type := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

  Local Open Scope Z_scope.
  Local Open Scope string_scope.

  Definition to_filter_head (e : expr) :=
    match e with
    | EFlatmap e' x
        (EIf p (EBinop OCons (EVar y) (EAtom (ANil _))) (EAtom (ANil _))) =>
        if String.eqb x y then EFilter e' x p else e
    | _ => e
    end.

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
               (EFlatmap
                  (EVar "scores") "x"
                  (e_check (EBinop OLess (EAtom (AInt 80))
                              (EAccess (EVar "x") "s")) (e_singleton (EVar "x")))).
    reflexivity. Abort.

  Definition typed_ex1 := synthesize_expr map.empty map.empty ex1.
  (* Compute typed_ex1.
  Compute (fold_expr to_filter_head ex1). *)

  Fixpoint free_immut_in (x : string) (e : expr) : bool :=
    match e with
    | EVar y => String.eqb x y
    | ELoc _ | EAtom _ => false
    | EUnop _ e => free_immut_in x e
    | EBinop _ e1 e2 => free_immut_in x e1 || free_immut_in x e2
    | EIf e1 e2 e3 => free_immut_in x e1 || free_immut_in x e2 || free_immut_in x e3
    | ELet e1 y e2 | EFlatmap e1 y e2 => free_immut_in x e1 || (negb (String.eqb x y) && free_immut_in x e2)
    | EFold e1 e2 y z e3 => free_immut_in x e1 || free_immut_in x e2 || (negb (String.eqb x y) && negb (String.eqb x z) && free_immut_in x e3)
    | ERecord l => existsb (fun '(_, e) => free_immut_in x e) l
    | EAccess e _ => free_immut_in x e
    | EDict l => existsb (fun '(e1, e2) => orb (free_immut_in x e1) (free_immut_in x e2)) l
    | EInsert d k v => free_immut_in x d || free_immut_in x k || free_immut_in x v
    | EDelete d k | ELookup d k => free_immut_in x d || free_immut_in x k
    | EOptMatch e e_none y e_some => free_immut_in x e || free_immut_in x e_none || (negb (String.eqb x y) && free_immut_in x e_some)
    | EDictFold d e0 k v acc e => free_immut_in x d || free_immut_in x e0 ||
                                    (negb (String.eqb x k) && negb (String.eqb x v) && negb (String.eqb x acc) &&
                                       free_immut_in x e)
    | ESort l => free_immut_in x l
    | EFilter e y p => free_immut_in x e || (negb (String.eqb x y) && free_immut_in x p)
    | EJoin e1 e2 x1 x2 p r => free_immut_in x e1 || free_immut_in x e2 ||
                                 (negb (String.eqb x x1) && negb (String.eqb x x2) && (free_immut_in x p || free_immut_in x r))
    | EProj e y r => free_immut_in x e || (negb (String.eqb x y) && free_immut_in x r)
    end.

  Definition to_join_head (e : expr) :=
    match e with
    | EFlatmap tbl1 x
        (EFlatmap tbl2 y
           (EIf p (EBinop OCons r (EAtom (ANil _))) (EAtom (ANil _)))) =>
        if ((x =? y) || free_immut_in x tbl2)%bool
        then e
        else EJoin tbl1 tbl2 x y p r
    | _ => e
    end.

  Definition ex2 : expr :=
    <["x" <- mut "scores";
      "n" <- mut "names";
      check("x"["s_id"] == "n"["n_id"]);
        ret {"name": "n"["n_name"], "score": "x"["s_score"]} ]>.
  Goal ex2 = EFlatmap (ELoc "scores") "x"
               (EFlatmap (ELoc "names") "n"
                  (EIf (EBinop OEq (EAccess (EVar "x") "s_id") (EAccess (EVar "n") "n_id"))
                     (EBinop OCons
                        (ERecord (("name", EAccess (EVar "n") "n_name") :: ("score", EAccess (EVar "x") "s_score") :: nil))
                        (EAtom (ANil None)))
                     (EAtom (ANil None)))).
    reflexivity. Abort.
  (* Compute to_join_head ex2. *)

  Definition filter_pushdown_head (e : expr) :=
    match e with
    | EJoin tbl1 tbl2 r1 r2 (EBinop OAnd p1 p) r =>
        if free_immut_in r2 p1
        then e
        else EJoin (EFilter tbl1 r1 p1) tbl2 r1 r2 p r
    | _ => e
    end.

  Definition ex3 : expr :=
    <[ "p" <- mut "persons";
       "e" <- mut "employees";
       check("p"["age"] < 40 && "p"["id"] == "e"["id"]);
       ret {"name": "p"["name"], "salary": "e"["salary"]}
      ]>.
  Goal ex3 = EFlatmap
      (ELoc "persons") "p"
      (EFlatmap
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

  Section WithMap.
    Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
    Context {locals: map.map string (fiat2.Value.value (width := width))} {locals_ok: map.ok locals}.

    Notation interp_expr := (interp_expr (word := word) (locals := locals)).

    Local Ltac destruct_one_match :=
      lazymatch goal with
      | |- context [match ?x with _ => _ end] =>
          let E := fresh "E" in
          destruct x eqn:E
      end.

    Lemma In_flat_map_ext : forall A B l (f : A -> list B) g,
        (forall a, In a l -> f a = g a) ->
        flat_map f l = flat_map g l.
    Proof.
      induction l; simpl; intuition. f_equal; auto.
    Qed.

    Lemma In_fold_right_ext' : forall A B a l (f : B -> A -> A) g P,
        P a ->
        (forall a b, P a -> In b l -> f b a = g b a /\ P (f b a)) ->
        fold_right f a l = fold_right g a l /\ P (fold_right f a l).
    Proof.
      intros. induction l as [| b l]; auto.
      simpl. split.
      - assert (H' : fold_right f a l = fold_right g a l).
        { apply IHl. intros a' b' H_a' H_b'. apply H0; intuition. }
        rewrite H'. apply H0; intuition. rewrite <- H'; apply IHl.
        intros. apply H0; intuition.
      - apply H0; intuition. apply IHl. intros. apply H0; intuition.
    Qed.

    Lemma In_fold_right_ext : forall A B a l (f : B -> A -> A) g P,
        P a ->
        (forall a b, P a -> In b l -> f b a = g b a /\ P (f b a)) ->
        fold_right f a l = fold_right g a l.
    Proof.
      apply In_fold_right_ext'.
    Qed.

    Lemma flat_map_eq : forall A B (f : A -> list B) g l, Forall (fun x => f x = g x) l -> flat_map f l = flat_map g l.
    Proof.
      intros. induction H; auto.
      simpl; congruence.
    Qed.

    Definition preserve_ty (f : expr -> expr) :=
      forall Gstore Genv e t,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e t -> type_of Gstore Genv (f e) t.

    Definition preserve_sem f :=
      forall Gstore Genv e t store env,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e t ->
        locals_wf Gstore store ->
        locals_wf Genv env ->
        interp_expr store env e = interp_expr store env (f e).

    Lemma to_filter_head_preserve_ty : preserve_ty to_filter_head.
    Proof.
      unfold preserve_ty. intros Gstore Genv e t H_Gstore H_Genv H.
      destruct e; auto. destruct e2; auto. destruct e2_2; auto.
      destruct o; auto. destruct e2_2_1; auto. destruct e2_2_2; auto.
      destruct a, e2_3; auto. destruct a; auto.
      simpl. destruct (x =? x0) eqn:E; auto.
      rewrite eqb_eq in E; subst.
      inversion H; subst. inversion H5; subst. inversion H8; subst.
      inversion H7; subst. inversion H9; inversion H11; subst. rewrite map.get_put_same in *.
      injection H14 as H14; subst.
      constructor; auto.
    Qed.

    Lemma to_filter_head_preserve_sem : preserve_sem to_filter_head.
    Proof.
      unfold preserve_sem. intros Gstore Genv e t store env H_Gstore H_Genv H H_str H_env.
      destruct e; auto. destruct e2; auto. destruct e2_2; auto.
      destruct o; auto. destruct e2_2_1; auto. destruct e2_2_2; auto. destruct a, e2_3; auto.
      destruct a; auto. simpl. destruct (x =? x0) eqn:E; auto. simpl.
      destruct_one_match; auto. f_equal.
      rewrite eqb_eq in E; subst.
      clear E0; induction l; auto.
      simpl. destruct (interp_expr store (map.put env x0 a) e2_1); auto.
      destruct b; auto. unfold get_local. rewrite map.get_put_same. simpl. f_equal. auto.
    Qed.

    Lemma not_free_immut_put_ty: forall x e Gstore Genv t t',
        free_immut_in x e = false ->
        type_of Gstore (map.put Genv x t') e t ->
        type_of Gstore Genv e t.
    Proof.
      intros. generalize dependent Genv. revert t. induction e using expr_IH;
        intros; simpl in *; repeat rewrite Bool.orb_false_iff in *;
        try now (inversion H0; subst; econstructor; eauto; intuition).
      - inversion H0; subst; constructor. rewrite eqb_neq in *. rewrite map.get_put_diff in *; auto.
      - inversion H0; subst; econstructor.
        + apply IHe1; eauto; intuition.
        + destruct (x =? x0) eqn:Ex.
          * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
          * apply IHe2; intuition.
            rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
      - inversion H0; subst; econstructor.
        + apply IHe1; eauto; intuition.
        + destruct (x =? x0) eqn:Ex.
          * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
          * apply IHe2; intuition.
            rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
      - inversion H0; subst; econstructor.
        + apply IHe1; eauto; intuition.
        + apply IHe2; intuition.
        + destruct (x =? x0) eqn:Ex.
          * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
          * rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x) in *; auto.
            destruct (x =? y) eqn:Ey.
            -- rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
            -- apply IHe3; intuition.
               rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
      - inversion H1; subst. econstructor; eauto. revert H0 H H4; clear; intros.
        generalize dependent tl. induction l; intros; destruct tl; intuition; inversion H4.
        subst. simpl in H; rewrite Bool.orb_false_iff in *. constructor; inversion H0; subst.
        + apply H3; destruct a; intuition.
        + fold (map snd l) (map snd tl). apply IHl; intuition.
      - inversion H1; subst. constructor; auto. clear H1. induction l; auto.
        simpl in H; rewrite Bool.orb_false_iff in *. constructor.
        + inversion H5. inversion H0; subst. split; apply H10;
            destruct a; rewrite Bool.orb_false_iff in *; intuition.
        + inversion H5; inversion H0. apply IHl; intuition.
      - inversion H0; subst. econstructor.
        + apply IHe1; eauto; intuition.
        + apply IHe2; eauto; intuition.
      - inversion H0; subst. econstructor.
        + apply IHe1; eauto; intuition.
        + apply IHe2; eauto; intuition.
        + destruct (x =? x0) eqn:Ex.
          * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
          * apply IHe3; intuition.
            rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
      - inversion H0; subst; econstructor.
        + apply IHe1; eauto; intuition.
        + apply IHe2; intuition.
        + destruct (x =? k) eqn:Ek.
          * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
          * rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x) in *; auto.
            destruct (x =? v) eqn:Ev.
            -- rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
            -- rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x) in *; auto.
               destruct (x =? acc) eqn:Eacc.
               ++ rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
               ++ apply IHe3; intuition.
                  rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
      - inversion H0; subst. constructor.
        + apply IHe1; auto; intuition.
        + destruct (x =? x0) eqn:Ex.
          * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
          * apply IHe2; intuition.
            rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
      - inversion H0; subst. econstructor.
        + apply IHe1; eauto; intuition.
        + apply IHe2; eauto; intuition.
        + destruct (x =? x0) eqn:Ex.
          * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
          * rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x) in *; auto.
            destruct (x =? y) eqn:Ey.
            -- rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
            -- apply IHe3; simpl in *; rewrite Bool.orb_false_iff in *; intuition; rewrite eqb_neq in *.
               rewrite Properties.map.put_put_diff; auto.
        + destruct (x =? x0) eqn:Ex.
          * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
          * rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x) in *; auto.
            destruct (x =? y) eqn:Ey.
            -- rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
            -- apply IHe4; simpl in *; rewrite Bool.orb_false_iff in *; intuition; rewrite eqb_neq in *.
               rewrite Properties.map.put_put_diff; auto.
      - inversion H0; subst. econstructor.
        + apply IHe1; eauto; intuition.
        + destruct (x =? x0) eqn:Ex.
          * rewrite eqb_eq in *; subst. rewrite Properties.map.put_put_same in *; auto.
          * apply IHe2; intuition.
            rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
    Qed.

    Lemma not_free_immut_put_sem: forall e x store env v,
        free_immut_in x e = false ->
        interp_expr store env e = interp_expr store (map.put env x v) e.
    Proof.
      induction e using expr_IH; intros; simpl in *; auto; repeat rewrite Bool.orb_false_iff in *;
        try (erewrite IHe; auto).
      - rewrite eqb_neq in *. unfold get_local. rewrite map.get_put_diff; auto.
      - erewrite IHe1, IHe2; intuition.
      - erewrite IHe1, IHe2, IHe3; repeat rewrite Bool.orb_false_iff in *; intuition.
      - destruct (x0 =? x) eqn:E.
        + rewrite eqb_eq in *; subst.
          rewrite Properties.map.put_put_same. erewrite IHe1; intuition.
        + rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
          erewrite IHe1, IHe2; intuition.
      - rewrite <- IHe1; intuition. destruct_one_match; auto. f_equal.
        apply flat_map_ext; intros. destruct (x0 =? x) eqn:E'.
        + rewrite eqb_eq in *; subst.
          rewrite Properties.map.put_put_same. auto.
        + rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; auto.
          erewrite IHe2; intuition.
      - rewrite <- IHe1; intuition. destruct_one_match; auto. rewrite <- IHe2; auto.
        apply In_fold_right_ext with (P := fun _ => True); auto.
        intros. destruct (x0 =? x) eqn:Ex.
        + rewrite eqb_eq in *; subst.
          rewrite Properties.map.put_put_same. auto.
        + rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x0); intuition.
          destruct (x0 =? y) eqn:Ey.
          * rewrite eqb_eq in *; subst.
            rewrite Properties.map.put_put_same. auto.
          * rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x0); intuition.
      - do 2 f_equal. induction l; auto. simpl in *. rewrite Bool.orb_false_iff in *.
        destruct a; intuition. f_equal.
        + f_equal. inversion H; subst. apply H4; intuition.
        + inversion H; apply IHl; intuition.
      - do 3 f_equal. induction l; auto. simpl in *. rewrite Bool.orb_false_iff in *.
        destruct a; intuition. f_equal.
        + f_equal; inversion H; subst; rewrite Bool.orb_false_iff in *;
            apply H4; intuition.
        + inversion H; apply IHl; intuition.
      - rewrite <- IHe1, <- IHe2, <- IHe3; auto; intuition.
      - rewrite <- IHe1, <- IHe2; auto; intuition.
      - rewrite <- IHe1, <- IHe2; auto; intuition.
      - rewrite <- IHe1, <- IHe2; auto; intuition. repeat destruct_one_match; auto.
        destruct (x0 =? x) eqn:Ex.
          * rewrite eqb_eq in *; subst.
            rewrite Properties.map.put_put_same. auto.
          * rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x0); intuition.
      - rewrite <- IHe1; intuition. destruct_one_match; auto. rewrite <- IHe2; auto.
        apply In_fold_right_ext with (P := fun _ => True); auto.
        intros. destruct (x =? k) eqn:Ek;
          try (rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same; auto).
        rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x); intuition.
        destruct (x =? v) eqn:Ev;
          try (rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same; auto).
        rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x); intuition.
        destruct (x =? acc) eqn:Eacc;
          try (rewrite eqb_eq in *; subst; rewrite Properties.map.put_put_same; auto).
        rewrite eqb_neq in *. rewrite Properties.map.put_put_diff with (k1 := x); intuition.
      - rewrite <- IHe1; intuition. destruct_one_match; auto.
        f_equal. clear E. induction l; auto. simpl.
         destruct (x0 =? x) eqn:E'.
          + rewrite eqb_eq in *; subst.
            rewrite Properties.map.put_put_same. destruct_one_match;
              [f_equal |]; apply IHl.
          + rewrite eqb_neq in *. rewrite Properties.map.put_put_diff; intuition.
            rewrite <- IHe2 with (x := x0); intuition.
            destruct_one_match; auto. f_equal. apply IHl.
      - rewrite <- IHe1, <- IHe2; intuition. repeat destruct_one_match; auto.
        f_equal. apply flat_map_ext. intros. clear E E0. induction l0; auto.
        simpl.
        assert (interp_expr store (map.put (map.put (map.put env x0 v) x a) y a0) e3 = interp_expr store (map.put (map.put env x a) y a0) e3).
        {  destruct (x0 =? x) eqn:Ex.
           - rewrite eqb_eq in *; subst.
             rewrite Properties.map.put_put_same. auto.
           - rewrite eqb_neq in *.
             rewrite Properties.map.put_put_diff with (k1 := x0); auto.
             destruct (x0 =? y) eqn:Ey.
             + rewrite eqb_eq in *; subst.
               rewrite Properties.map.put_put_same. auto.
             + rewrite eqb_neq in *.
               rewrite Properties.map.put_put_diff; auto.
               simpl in H1. rewrite Bool.orb_false_iff in *. rewrite <- IHe3; intuition. }
        rewrite H0. destruct_one_match; simpl; try apply IHl0.
        f_equal; try apply IHl0.
        destruct (x0 =? x) eqn:Ex.
        -- rewrite eqb_eq in *; subst.
           rewrite Properties.map.put_put_same. auto.
        -- rewrite eqb_neq in *.
           rewrite Properties.map.put_put_diff with (k1 := x0); auto.
           destruct (x0 =? y) eqn:Ey.
           ++ rewrite eqb_eq in *; subst.
              rewrite Properties.map.put_put_same. auto.
           ++ rewrite eqb_neq in *.
              rewrite Properties.map.put_put_diff with (k1 := x0); auto.
              simpl in H1. rewrite Bool.orb_false_iff in *. rewrite <- (IHe4 x0); intuition.
      - rewrite <- IHe1; intuition. destruct_one_match; auto.
        f_equal. apply map_ext. intro. destruct (x0 =? x) eqn:Ex.
        + rewrite eqb_eq in *; subst.
          rewrite Properties.map.put_put_same. auto.
        + rewrite eqb_neq in *.
          rewrite Properties.map.put_put_diff with (k1 := x0); auto.
    Qed.

    Lemma to_join_head_preserve_ty : preserve_ty to_join_head.
    Proof.
      unfold preserve_ty. intros Gstore Genv e t H_Gstore H_Genv H.
      destruct e; auto. destruct e2; auto. destruct e2_2; auto.
      destruct e2_2_2; auto. destruct o; auto. destruct e2_2_2_2; auto.
      destruct a; auto. destruct e2_2_3; auto. destruct a; auto.
      simpl. destruct_one_match; auto.
      inversion H; subst. inversion H5; subst. inversion H7; subst.
      inversion H9; subst. inversion H8; subst.
      econstructor; eauto.
      rewrite Bool.orb_false_iff in *.
      eapply not_free_immut_put_ty; eauto. intuition.
    Qed.

    Lemma to_join_head_preserve_sem' : forall (store env: locals) (Gstore Genv: tenv) (tbl1 tbl2 p r : expr) (x y : string) (t1 t2 t3 : type) (t t' : option type),
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv tbl1 (TList t1) ->
        type_of Gstore (map.put Genv x t1) tbl2 (TList t2) ->
        free_immut_in x tbl2 = false ->
        type_of Gstore (map.put (map.put Genv x t1) y t2) p TBool ->
        locals_wf Gstore store ->
        locals_wf Genv env ->
        interp_expr store env (EFlatmap tbl1 x
                       (EFlatmap tbl2 y
                          (EIf p (EBinop OCons r (EAtom (ANil t))) (EAtom (ANil t'))))) =
          interp_expr store env (EJoin tbl1 tbl2 x y p r).
    Proof.
      intros store env Gstore Genv tbl1 tbl2 p r x y t1 t2 t3 t t' H_Gstore H_Genv H_tbl1 H_tbl2 H_free H_p H_str H_env.
      simpl. apply type_of__type_wf in H_tbl1 as H_wf1; auto. apply type_of__type_wf in H_tbl2 as H_wf2; auto;
        [| apply tenv_wf_step; inversion H_wf1]; auto.
      eapply type_sound in H_tbl1; eauto. inversion H_tbl1; subst.
      f_equal. apply not_free_immut_put_ty in H_tbl2 as H_tbl2'; auto.
      eapply type_sound in H_tbl2'; eauto. inversion H_tbl2'; subst.
      f_equal. apply flat_map_eq. rewrite Forall_forall. intros v H_v.
      eapply type_sound with (env := (map.put env x v)) in H_tbl2; eauto.
      - inversion H_tbl2; subst.
        rewrite <- not_free_immut_put_sem in H2; auto. rewrite <- H2 in H0.
        injection H0; intros; subst.
        subst. clear H0 H2. induction l1; auto. simpl.
        eapply type_sound in H_p; eauto.
        + inversion H_p; subst. rewrite <- H2. destruct b; simpl; [f_equal |];
            inversion H3; inversion H5; apply IHl1; auto.
        + rewrite Forall_forall in *; repeat apply locals_wf_step;
            repeat apply tenv_wf_step; intuition;
            inversion H_wf1; inversion H_wf2; auto.
        + repeat apply locals_wf_step; auto.
          * eapply List.Forall_In in H1; eauto.
          * inversion H3; auto.
      - apply tenv_wf_step; auto. inversion H_wf1; auto.
      - rewrite Forall_forall in *; repeat apply locals_wf_step; intuition.
    Qed.

    Lemma to_join_head_preserve_sem : preserve_sem to_join_head.
    Proof.
      unfold preserve_sem. intros Gstore Genv e t store env H_Gstore H_Genv H H_str H_env.
      destruct e; auto. destruct e2; auto. destruct e2_2; auto.
      destruct e2_2_2; auto. destruct o; auto. destruct e2_2_2_2; auto.
      destruct a; auto. destruct e2_2_3; auto. destruct a; auto.
      unfold to_join_head. destruct ((x =? x0) || free_immut_in x e2_1)%bool eqn:E; auto.
      inversion H; subst. inversion H5; subst. inversion H7; subst. inversion H9; subst.
      rewrite Bool.orb_false_iff in *.
      eapply to_join_head_preserve_sem' with (Gstore := Gstore); eauto; intuition.
    Qed.

    Lemma filter_pushdown_head_preserve_ty : preserve_ty filter_pushdown_head.
    Proof.
      unfold preserve_ty. intros Gstore Genv e t H_Gstore H_Genv H.
      destruct e; auto. destruct e3; auto. destruct o; auto.
      simpl. destruct_one_match; auto.
      inversion H; subst. inversion H9; subst. inversion H3; subst.
      econstructor; eauto. constructor; auto.
      eapply not_free_immut_put_ty; eauto.
    Qed.

    Lemma flat_map_filter : forall A B (f : A -> list B) g l,
        flat_map f (filter g l) = flat_map (fun v => if g v then f v else nil) l.
    Proof.
      induction l; auto; simpl.
      destruct (g a); auto. simpl. rewrite IHl; auto.
    Qed.

    Lemma filter_pushdown_head_preserve_sem : preserve_sem filter_pushdown_head.
    Proof.
      unfold preserve_sem. intros Gstore Genv e t store env H_Gstore H_Genv H H_str H_env.
      destruct e; auto. destruct e3; auto. destruct o; auto.
      unfold filter_pushdown_head. destruct (free_immut_in y e3_1) eqn:E; auto.

      simpl. destruct (interp_expr store env e1) eqn:E1; auto.
      destruct (interp_expr store env e2) eqn:E2; auto. f_equal.
      inversion H; subst.
      eapply type_sound in H7, H8; eauto. rewrite E1 in H7. rewrite E2 in H8.
      inversion H7; inversion H8; subst.
      rewrite flat_map_filter. apply In_flat_map_ext; intros.
      destruct (interp_expr store (map.put env x a) e3_1) eqn:E3_1;
        try (clear E2 H8; induction l0; auto; simpl;
             eapply not_free_immut_put_sem in E; rewrite <- E; rewrite E3_1; simpl;
             apply IHl0; inversion H5; intuition).
      destruct b.
      - clear E2 H8; induction l0; inversion H5; auto; simpl.
        eapply not_free_immut_put_sem in E; rewrite <- E; rewrite E3_1; simpl.
        destruct (interp_expr store (map.put (map.put env x a) y a0) e3_2) eqn:E3_2; simpl;
          try (apply IHl0; intuition).
        destruct b; simpl; [f_equal |]; apply IHl0; intuition.
      - clear E2 H8; induction l0; inversion H5; auto; simpl.
        eapply not_free_immut_put_sem in E; rewrite <- E; rewrite E3_1; simpl.
        destruct (interp_expr store (map.put (map.put env x a) y a0) e3_2) eqn:E3_2; simpl;
          apply IHl0; intuition.
    Qed.

    Local Ltac apply_fold_expr_IH' e :=
      lazymatch goal with
      | H : type_of ?Gstore' _ _ _,
          IH : context [interp_expr _ _ e = interp_expr _ _ (fold_expr _ e)] |- _ =>
          erewrite <- IH with (Gstore := Gstore'); clear IH; eauto
      end.

    Local Ltac apply_fold_expr_IH :=
      lazymatch goal with
      | |- context [interp_expr _ _ (fold_expr _ ?e)] => apply_fold_expr_IH' e
      end.

    Local Ltac invert_type_of :=
      lazymatch goal with
      | H : type_of _ _ _ _ |- _ => inversion H; subst
      end.

  Local Ltac invert_type_wf :=
    lazymatch goal with
    | H: type_wf (TList ?t) |- type_wf ?t => inversion H; clear H; subst
    | H: type_wf (TOption ?t) |- type_wf ?t => inversion H; clear H; subst
    | H: type_wf (TDict ?t _) |- type_wf ?t => inversion H; clear H; subst
    | H: type_wf (TDict _ ?t) |- type_wf ?t => inversion H; clear H; subst
    | H: type_wf (TRecord ?tl) |- Forall type_wf (List.map snd ?tl) => inversion H; clear H; subst
    end.

    Local Ltac apply_type_of__type_wf :=
      lazymatch goal with
      | H: type_of _ _ _ ?t |- type_wf ?t =>
          let H' := fresh "H'" in
          apply type_of__type_wf in H as H'
      | H: type_of _ _ _ (TList ?t) |- type_wf ?t =>
          let H' := fresh "H'" in
          apply type_of__type_wf in H as H'
      | H:  type_of _ _ _ (TOption ?t) |- type_wf ?t =>
          let H' := fresh "H'" in
          apply type_of__type_wf in H as H'
      | H:  type_of _ _ _ (TDict ?t _) |- type_wf ?t =>
          let H' := fresh "H'" in
          apply type_of__type_wf in H as H'
      | H:  type_of _ _ _ (TDict _ ?t) |- type_wf ?t =>
          let H' := fresh "H'" in
          apply type_of__type_wf in H as H'
      | H:  type_of _ _ _ (TRecord ?tl) |- context[?tl] =>
          let H' := fresh "H'" in
          apply type_of__type_wf in H as H'
      end.

    Theorem fold_expr_preserve_ty : forall f, preserve_ty f -> preserve_ty (fold_expr f).
    Proof.
      unfold preserve_ty. intros f H Gstore Genv e.
      revert Gstore Genv. induction e using expr_IH;
        intros; simpl; auto;
        apply H; invert_type_of; subst; try econstructor; eauto.
      all: try apply IHe2; auto; repeat apply tenv_wf_step; auto; try apply_type_of__type_wf; auto;
        try invert_type_wf; auto.
      - apply IHe3; auto; repeat apply tenv_wf_step; auto;
        apply type_of__type_wf in H9, H10; try invert_type_wf; auto.
      - rewrite fst_map_fst; auto.
      - clear H3 H7 H8 H9. generalize dependent tl.
        induction l; intros; destruct tl; try discriminate.
        + constructor.
        + simpl. constructor.
          * inversion H0; subst. inversion H6; subst. apply H7 in H10; auto.
            destruct a; simpl in *. auto.
          * simpl in *; inversion H0; inversion H5; inversion H6; apply IHl; auto.
      - induction l; auto. constructor.
        + destruct a. inversion H0; inversion H7; intuition.
        + inversion H0; inversion H7; apply IHl; auto.
          inversion H3; subst. constructor; auto.
      - apply IHe3; auto. apply tenv_wf_step; auto. apply_type_of__type_wf; try invert_type_wf; auto.
      - apply IHe3; auto. repeat apply tenv_wf_step; auto.
        all: apply type_of__type_wf in H10, H11; try invert_type_wf; auto.
      - apply IHe3; auto. repeat apply tenv_wf_step; auto;
          apply_type_of__type_wf; try invert_type_wf; auto.
      - apply IHe4; auto. repeat apply tenv_wf_step; auto;
          apply_type_of__type_wf; try invert_type_wf; auto.
    Qed.

    Lemma In_map_snd : forall A B (a : A) (b : B) l, In (a, b) l -> In b (List.map snd l).
    Proof.
      induction l; intuition.
      simpl. inversion H; auto.
      left; subst; reflexivity.
    Qed.

    Lemma In_filter_ext : forall A (l : list A) f g, (forall x, In x l -> f x = g x) -> filter f l = filter g l.
    Proof.
      induction l; intuition.
      simpl. rewrite H; intuition.
      erewrite IHl; eauto. intuition.
    Qed.

    Local Ltac apply_type_sound :=
    lazymatch goal with
    | H : type_of _ _ ?e (TList ?t), E : interp_expr _ _ ?e = _ |- type_of_value _ ?t =>
        eapply type_sound in H; eauto; rewrite E in H; inversion H; subst
    | H : type_of _ _ ?e (TOption ?t), E : interp_expr _ _ ?e = _ |- type_of_value _ ?t =>
        eapply type_sound in H; eauto; rewrite E in H; inversion H; subst
    | H : type_of _ _ ?e ?t |- type_of_value (interp_expr _ _ ?e) ?t =>
        eapply type_sound in H; eauto
    | H : type_of _ _ ?e ?t,
        H1 : In ?v ?l,
          E : interp_expr _ _ ?e = Value.VList ?l
      |- type_of_value ?v ?t =>
        eapply type_sound in H; eauto; rewrite E in H; inversion H; subst
    | H:type_of _ _ ?e (TDict ?kt ?vt), H1:In ?v ?l, E:interp_expr _ _ ?e = Value.VDict ?l
      |- type_of_value (_ ?v) _ => eapply type_sound in H; eauto; rewrite E in H; inversion H; subst
    end.

    Theorem fold_expr_preserve_sem : forall f, preserve_ty f -> preserve_sem f -> preserve_sem (fold_expr f).
    Proof.
      unfold preserve_sem. intros f H_ty H_sem Gstore Genv e; revert Gstore Genv.
      induction e using expr_IH;
        intros; simpl;
        try now (erewrite <- H_sem with (Gstore := Gstore); eauto).
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; repeat apply_fold_expr_IH; eauto.
        econstructor; eauto; apply fold_expr_preserve_ty; auto.
      - invert_type_of. subst. erewrite <- H_sem with (Gstore := Gstore); simpl; repeat apply_fold_expr_IH; eauto.
        econstructor; eauto; apply fold_expr_preserve_ty; eauto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; repeat apply_fold_expr_IH; eauto.
        econstructor; apply fold_expr_preserve_ty; eauto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; eauto.
        + erewrite <- IHe2. 4: eassumption.
          all: auto; repeat apply_fold_expr_IH;
            try apply locals_wf_step; try apply tenv_wf_step; try eapply type_sound; eauto.
          apply_type_of__type_wf; auto.
        + econstructor; apply fold_expr_preserve_ty; eauto. apply tenv_wf_step; try apply_type_of__type_wf; auto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; repeat apply_fold_expr_IH; eauto.
        + destruct_one_match; auto. f_equal. apply In_flat_map_ext; intros.
          erewrite <- IHe2. 4: eassumption.
          all: auto; try apply locals_wf_step; try apply tenv_wf_step; try apply_type_of__type_wf; try invert_type_wf; auto.
          apply_type_sound. rewrite Forall_forall in *; auto.
        + econstructor; apply fold_expr_preserve_ty; eauto.
          apply tenv_wf_step; try apply_type_of__type_wf; try invert_type_wf; auto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; repeat apply_fold_expr_IH; eauto.
        + destruct_one_match; auto. apply_fold_expr_IH' e2; eauto.
          apply In_fold_right_ext with (P := fun v => type_of_value v t); intros; try apply_type_sound.
          erewrite <- IHe3. 4: eassumption. all: intuition.
          * apply_type_sound; repeat apply locals_wf_step; repeat apply tenv_wf_step; auto.
            -- apply_type_of__type_wf; auto. invert_type_wf; auto.
            -- apply type_of__type_wf in H11; auto.
            -- apply_type_sound. rewrite Forall_forall in *; auto.
          * repeat apply tenv_wf_step; auto.
            -- apply_type_of__type_wf; auto. invert_type_wf; auto.
            -- apply type_of__type_wf in H11; auto.
          * repeat apply locals_wf_step; auto.
            apply_type_sound. rewrite Forall_forall in *; auto.
        + try (econstructor; apply fold_expr_preserve_ty; eauto).
          repeat apply tenv_wf_step; auto.
            -- apply_type_of__type_wf; auto. invert_type_wf; auto.
            -- apply type_of__type_wf in H11; auto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; eauto.
        + do 2 f_equal. rewrite map_map; apply map_ext_Forall; rewrite Forall_forall.
          intros x H_in; destruct x. pose proof In_map_snd.
          match goal with
          | H : Forall2 _ _ _ |- _ => eapply Forall2_In_Permuted in H; eauto; do 3 destruct H
          end.
          intuition; f_equal.
          rewrite Forall_forall in *. eapply H with (Gstore := Gstore) in H_in; simpl in *; eauto.
        + econstructor; eauto; try (rewrite fst_map_fst; auto).
          apply fold_expr_preserve_ty in H_ty.
          clear H2 H8 H9. generalize dependent tl. induction l; destruct tl; try discriminate; intuition.
          simpl. inversion H7; subst. constructor.
          * destruct a. simpl. apply H_ty; auto.
          * inversion H6; inversion H; apply IHl; auto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; eauto; try apply_fold_expr_IH r.
        econstructor; eauto. apply fold_expr_preserve_ty; auto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; eauto.
        + do 3 f_equal. rewrite map_map; apply map_ext_Forall; rewrite Forall_forall.
          intros x H_in; destruct x eqn:E.
          apply Forall_and_inv in H. intuition. rewrite Forall_forall in *.
          f_equal; [ pose proof (H5 x) | pose proof (H9 x) ]; subst; simpl in *; eapply H with (Gstore := Gstore); eauto;
            apply H8 in H_in; simpl in *; apply H_in.
        + constructor.
          3: rewrite Forall_forall; intros p H_in;
          apply in_map_iff in H_in as [[k v] [H_p_p0 H_in]]; subst;
          rewrite Forall_forall in *; apply H8 in H_in as [HL HR];
          eapply fold_expr_preserve_ty in HL, HR; eauto.
          all: auto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; eauto; try apply_fold_expr_IH.
        + destruct_one_match; auto. do 2 f_equal; apply_fold_expr_IH.
        + constructor; apply fold_expr_preserve_ty; eauto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; eauto; try apply_fold_expr_IH.
        + destruct_one_match; auto. do 2 f_equal; apply_fold_expr_IH.
        + constructor; apply fold_expr_preserve_ty; eauto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; eauto; try apply_fold_expr_IH.
        + destruct_one_match; auto. do 2 f_equal; apply_fold_expr_IH.
        + econstructor; apply fold_expr_preserve_ty; eauto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; eauto; try apply_fold_expr_IH.
        + repeat destruct_one_match; auto.
          2: apply_fold_expr_IH; auto.
          erewrite <- IHe3. 4: eassumption.
          all: auto; try apply locals_wf_step; try apply tenv_wf_step; auto.
          * apply_type_of__type_wf; auto; invert_type_wf; auto.
          * apply_type_sound; auto.
        + econstructor; apply fold_expr_preserve_ty; eauto. apply tenv_wf_step; auto.
          apply_type_of__type_wf; auto; invert_type_wf; auto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; repeat apply_fold_expr_IH; eauto.
        + destruct_one_match; auto. apply_fold_expr_IH' e2; eauto.
          apply In_fold_right_ext with (P := fun v => type_of_value v t); intros; try apply_type_sound.
          erewrite <- IHe3. 4: eassumption. all: intuition.
          * apply_type_sound; repeat apply locals_wf_step; repeat apply tenv_wf_step; auto.
            4,5: apply_type_sound; eapply List.Forall_In in H14; intuition; eauto.
            -- apply_type_of__type_wf; auto. invert_type_wf; auto.
            -- apply type_of__type_wf in H11; try invert_type_wf; auto.
            -- apply type_of__type_wf in H12; auto. (* ??? How to prioritize H12 over H13 in Ltac? *)
          * repeat apply tenv_wf_step; auto.
            -- apply_type_of__type_wf; auto. invert_type_wf; auto.
            -- apply type_of__type_wf in H11; try invert_type_wf; auto.
            -- apply type_of__type_wf in H12; auto.
          * repeat apply locals_wf_step; auto;
              apply_type_sound; eapply List.Forall_In in H14; intuition; eauto.
        + try (econstructor; apply fold_expr_preserve_ty; eauto).
          repeat apply tenv_wf_step; auto.
            -- apply_type_of__type_wf; auto. invert_type_wf; auto.
            -- apply type_of__type_wf in H11; try invert_type_wf; auto.
            -- apply type_of__type_wf in H12; auto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; eauto; try apply_fold_expr_IH.
        constructor. apply fold_expr_preserve_ty; eauto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; eauto; try apply_fold_expr_IH.
        + destruct_one_match; auto. f_equal.
          apply In_filter_ext. intros x0 H_in.
          erewrite <- IHe2. 4: eassumption.
          all: try apply locals_wf_step; try apply tenv_wf_step; auto.
          * apply_type_of__type_wf; auto; invert_type_wf; auto.
          * apply_type_sound. rewrite Forall_forall in *; auto.
        + constructor; apply fold_expr_preserve_ty; eauto. apply tenv_wf_step; auto.
          apply_type_of__type_wf; auto; invert_type_wf; auto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; eauto; try apply_fold_expr_IH.
        + destruct_one_match; auto. apply_fold_expr_IH.
          destruct_one_match; auto. f_equal.
          apply In_flat_map_ext. intros a H_in_a. erewrite In_filter_ext; try apply map_ext_Forall.
          * rewrite Forall_forall. intros x0 H_in_x0. rewrite filter_In in H_in_x0; intuition.
            erewrite <- IHe4. 4: eassumption.
            all: repeat apply locals_wf_step; repeat apply tenv_wf_step; auto.
            1,2: apply_type_of__type_wf; auto; invert_type_wf; auto.
            1,2: apply_type_sound; rewrite Forall_forall in *; auto.
          * intros x0 H_in_x0. simpl. erewrite <- IHe3. 4: eassumption.
            all: repeat apply locals_wf_step; repeat apply tenv_wf_step; auto.
            1,2: apply_type_of__type_wf; auto; invert_type_wf; auto.
            1,2: apply_type_sound; rewrite Forall_forall in *; auto.
        + econstructor; apply fold_expr_preserve_ty; eauto; repeat apply tenv_wf_step; auto;
          apply_type_of__type_wf; auto; invert_type_wf; auto.
      - invert_type_of. erewrite <- H_sem with (Gstore := Gstore); simpl; eauto; try apply_fold_expr_IH.
        + destruct_one_match; auto. f_equal. apply map_ext_Forall; rewrite Forall_forall.
          intros x0 H_in. erewrite <- IHe2. 4: eassumption.
          all: try apply locals_wf_step; try apply tenv_wf_step; auto.
          * apply_type_of__type_wf; auto; invert_type_wf; auto.
          * apply_type_sound; rewrite Forall_forall in *; auto.
        + econstructor; apply fold_expr_preserve_ty; eauto. repeat apply tenv_wf_step; auto.
          apply_type_of__type_wf; auto; invert_type_wf; auto.
    Qed.

    (* Compute ex3. *)
    Definition ex3_op := fold_expr filter_pushdown_head (fold_expr to_join_head ex3).
    (* Compute ex3_op. *)
    Lemma ex3_op_equiv_ex3 : forall Gstore Genv t store env,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv ex3 t ->
        locals_wf Gstore store ->
        locals_wf Genv env ->
        type_of Gstore Genv ex3_op t /\ interp_expr store env ex3 = interp_expr store env ex3_op.
    Proof.
      intros; unfold ex3_op. split.
      - apply fold_expr_preserve_ty; auto; [apply filter_pushdown_head_preserve_ty |].
        apply fold_expr_preserve_ty; auto; apply to_join_head_preserve_ty.
      - erewrite fold_expr_preserve_sem with (Gstore := Gstore); eauto.
        + erewrite fold_expr_preserve_sem with (Gstore := Gstore); eauto.
          * exact filter_pushdown_head_preserve_ty.
          * exact filter_pushdown_head_preserve_sem.
          * apply fold_expr_preserve_ty; eauto. exact to_join_head_preserve_ty.
        + exact to_join_head_preserve_ty.
        + exact to_join_head_preserve_sem.
    Qed.
  End WithMap.
End Examples.
