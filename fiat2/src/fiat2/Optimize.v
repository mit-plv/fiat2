Require Import Lia.
Require Import Coq.Program.Equality.
Require Import fiat2.Language.
Require Import fiat2.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Tactics.Tactics.
Require Import Coq.Lists.List.
Require Import fiat2.SamplePrograms. (* This is imported for the string_app_assoc lemma, which should be moved elsewhere anyway *)
From Coq Require Import FunctionalExtensionality.

Require Import fiat2.PrintingNotations.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma length_eval_range : forall l s, length (eval_range s l) = l.
Proof.
  induction l; simpl; auto.
Qed.

Section WithMap.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {locals: map.map string {t & interp_type (width := width) t}} {locals_ok: map.ok locals}.

  Fixpoint listify {t : type} (l : list (expr t)) : expr (TList t) :=
    match l with
    | nil => EAtom (ANil t)
    | x :: xs => EBinop (OCons t) x (listify xs)
    end.

  Lemma listify_correct (t : type) (store env : locals) (xs : list (expr t)) :
    interp_expr store env (listify xs) = map (interp_expr store env) xs.
  Proof.
    induction xs; try easy.
    simpl.
    rewrite IHxs.
    reflexivity.
  Qed.

  Fixpoint reify (t : type) : interp_type t -> expr t :=
    match t in type return interp_type t -> expr t with
    | TWord => fun w => EAtom (AWord (word.unsigned w))
    | TInt => fun n => EAtom (AInt n)
    | TBool => fun b => EAtom (ABool b)
    | TString => fun s => EAtom (AString s)
    | TPair s t1 t2 => fun p => EBinop (OPair s t1 t2) (reify t1 (fst p)) (reify t2 (snd p))
    | TEmpty => fun _ => EAtom AEmpty
    | TList t => fun l => listify (map (reify t) l)
    end.

  Lemma reify_correct (t : type) (store env : locals) (c : interp_type t) : interp_expr store env (reify t c) = c.
  Proof.
    induction t; intros; try easy.
    - apply word.of_Z_unsigned.
    - destruct c. simpl. rewrite IHt1. rewrite IHt2. reflexivity.
    - destruct c. reflexivity.
    - induction c.
      + reflexivity.
      + simpl. rewrite IHt. simpl in IHc. rewrite IHc. reflexivity.
  Qed.

  Definition invert_atom {t : type} (e : expr t) : option (interp_type t) :=
    match e with
    | EAtom a => Some (interp_atom a)
    | _ => None
    end.

  Lemma invert_atom_correct {t : type} (store env : locals) (e : expr t) :
    forall c, invert_atom e = Some c -> interp_expr store env e = c.
  Proof.
    intros.
    destruct e; inversion H.
    simpl.
    reflexivity.
  Qed.

  Definition as_const {t : type} (e : expr t) : option (interp_type t) :=
    match e with
    | EAtom a => Some (interp_atom a)
    | EUnop o e1 => match invert_atom e1 with
                    | Some c1 => Some (interp_unop o c1)
                    | _ => None
                    end
    | EBinop o e1 e2 => match invert_atom e1, invert_atom e2 with
                        | Some c1, Some c2 => Some (interp_binop o c1 c2)
                        | _, _ => None
                        end
    | EIf a e1 e2 => match invert_atom a with
                     | Some c1 => if c1 then invert_atom e1 else invert_atom e2
                     | _ => None
                     end
    | _ => None
    end.

  Lemma as_const_correct {t : type} (store env : locals) (e : expr t) :
    forall c, as_const e = Some c -> interp_expr store env e = c.
  Proof.
    destruct e; simpl; intros; try solve [inversion H]; auto.
    - inversion H. reflexivity.
    - destruct e; try inversion H. reflexivity.
    - destruct e1; destruct e2; try inversion H. reflexivity.
    - dependent induction e1; simpl; simpl in *; try solve [inversion H];
      dependent induction a; simpl; simpl in *; try solve [inversion H];
      destruct b; simpl; apply invert_atom_correct; apply H.
  Qed.

  Definition constfold_head {t} (e : expr t) : expr t :=
    match t with
    | TInt | TBool | TString | TEmpty => match as_const e with
                                         | Some v => reify _ v
                                         | _ => e
                                         end
    | _ => e
    end.

  Lemma constfold_head_correct store env {t} e :
    interp_expr store env (@constfold_head t e) = interp_expr store env e.
  Proof.
    cbv [constfold_head].
    repeat destruct_one_match; auto; try erewrite reify_correct, as_const_correct; auto.
  Qed.

  Fixpoint eLength {t : type} (e : expr (TList t)) : expr TInt :=
    match e with
    | EBinop (OCons t') eh et => EBinop OPlus (EAtom (AInt 1)) (eLength et)
    | EBinop ORange s e => constfold_head (EIf (constfold_head (EBinop OLess e s)) (EAtom (AInt 0)) (constfold_head (EBinop OMinus e s)))
    | _ => match invert_atom e with
           | Some nil => EAtom (AInt 0)
           | _ => EUnop (OLength _) e
           end
    end.
End WithMap.

(* Workaround for COQBUG <https://github.com/coq/coq/issues/17555> *)
Section WithMap2.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {locals: map.map string {t & interp_type (width := width) t}} {locals_ok: map.ok locals}.

  Lemma eLength_correct {t : type} (store env : locals) (e : expr (TList t)) :
    interp_expr store env (eLength e) = interp_expr store env (EUnop (OLength t) e).
  Proof.
    dependent induction e; subst; cbn [eLength]; try reflexivity.
    - case invert_atom eqn:?; trivial. destruct i; trivial.
      apply invert_atom_correct with (store := store) (env := env) in Heqo.
      cbn in *. rewrite Heqo. reflexivity.
    - dependent induction o; subst; cbn [invert_atom]; trivial.
      + cbn [interp_expr interp_binop interp_unop interp_atom Datatypes.length].
        erewrite IHe2; trivial.
        cbn [interp_expr interp_binop interp_unop interp_atom Datatypes.length].
        lia.
      + repeat (rewrite constfold_head_correct; cbn [interp_expr interp_binop interp_unop interp_atom Datatypes.length]).
        destruct_one_match; rewrite length_eval_range; lia.
  Qed.

  Definition invert_EPair {X A B} (e : expr (TPair X A B)) : option (expr A * expr B) :=
    match e in expr t
    return option match t with TPair _ A' B' => expr A' * expr B' | _ => Empty_set end
    with @EBinop _a _b _ab op e1 e2 =>
       match op in binop a b t
       return expr a -> expr b -> option match t with TPair _ A' B' => expr A' * expr B' | _ => Empty_set end
       with OPair s a b => fun e1' e2' => Some (e1', e2') | _ => fun _ _ => None
       end e1 e2
    | _ => None end.

  (* Partial evaluation happens before constant folding *)
  Definition eUnop {t1 t2 : type} (o : unop t1 t2) (e : expr t1) : expr t2 :=
    constfold_head (
    match o in unop t1 t2 return expr t1 -> expr t2 with
    | OLength t => eLength
    | OFst s t1 t2 as o => fun e => match invert_EPair e with Some (x, _) => x | _ => EUnop o e end
    | OSnd s t1 t2 as o => fun e => match invert_EPair e with Some (_, x) => x | _ => EUnop o e end
    | o => EUnop o
    end e).

  Lemma invert_EPair_correct {X A B} e e1 e2 :
    @invert_EPair X A B e = Some (e1, e2)
    <-> e = EBinop (OPair X A B) e1 e2.
  Proof.
    clear dependent locals.
    clear dependent width.
    dependent induction e; cbn; intuition; try congruence;
    dependent induction o; inversion H;
    try apply Eqdep.EqdepTheory.inj_pair2 in H1, H2; try exact type_eq_dec;
    congruence.
  Qed.

  Lemma EUnop_correct {t1 t2 : type} (store env : locals) (o : unop t1 t2) (e : expr t1)
    : interp_expr store env (eUnop o e) = interp_expr store env (EUnop o e).
  Proof.
    cbv [eUnop]; rewrite constfold_head_correct; case o in *; trivial.
    { apply eLength_correct. }
    { destruct invert_EPair as [[]|] eqn:H; try apply invert_EPair_correct in H; rewrite ?H; trivial. }
    { destruct invert_EPair as [[]|] eqn:H; try apply invert_EPair_correct in H; rewrite ?H; trivial. }
  Qed.

  Definition partial_head {t} (e : expr t) : expr t :=
    match e with
    | EUnop o e1 => eUnop o e1
    | e => e
    end.

    (* TODO Move to coq util *)
    Lemma fold_left_extensionality A B acc (f f' : A -> B -> A) l :
      (forall a b, f a b = f' a b) ->
      fold_left f l acc = fold_left f' l acc.
    Proof.
      intro. revert acc.
      induction l; cbn; try eauto.
      intros. rewrite H. congruence.
    Qed.

  Section fold_expr.
    Context (f : forall {t}, expr t -> expr t). Local Arguments f {_}.
    Fixpoint fold_expr {t : type} (e : expr t) : expr t :=
      f
      match e in expr t return expr t with
      | EUnop o e1 => EUnop o (fold_expr e1)
      | EBinop o e1 e2 => EBinop o (fold_expr e1) (fold_expr e2)
      | EFlatmap e1 x e2 => EFlatmap (fold_expr e1) x (fold_expr e2)
      | EFold e1 e2 x y e3 => EFold (fold_expr e1) (fold_expr e2) x y (fold_expr e3)
      | EIf e1 e2 e3 => EIf (fold_expr e1) (fold_expr e2) (fold_expr e3)
      | ELet x e1 e2 => ELet x (fold_expr e1) (fold_expr e2)
      | (EVar _ _ | ELoc _ _ | EAtom _) as e => e
      end.

    Fixpoint fold_command (c : command) : command :=
      match c with
      | CSkip => CSkip
      | CSeq c1 c2 => CSeq (fold_command c1) (fold_command c2)
      | CLet x e c => CLet x (fold_expr e) (fold_command c)
      | CLetMut x e c => CLetMut x (fold_expr e) (fold_command c)
      | CGets x e => CGets x (fold_expr e)
      | CIf e c1 c2 => CIf (fold_expr e) (fold_command c1) (fold_command c2)
      | CForeach x e c => CForeach x (fold_expr e) (fold_command c)
      end.

    Context (H : (forall store env t e, interp_expr store env (@f t e) = interp_expr store env e)).
    Theorem fold_expr_correct {t : type} (store env : locals) (e : expr t) :
      interp_expr store env (fold_expr e) = interp_expr store env e.
    Proof.
      generalize dependent (store).
      generalize dependent (env).
      induction e; cbn; intros; rewrite H; cbn; try congruence.
      - rewrite IHe1. induction (interp_expr store env e1); try reflexivity.
        cbn. rewrite IHi.
        f_equal. rewrite IHe2. reflexivity.
      - rewrite IHe1, IHe2.
        induction (interp_expr store env e1); try reflexivity.
        cbn. rewrite IHe3, IHi.
        reflexivity.
      - rewrite IHe1, IHe2, IHe3.
        reflexivity.
    Qed.

    Theorem fold_command_correct {t : type} (store env : locals) (c : command) :
      interp_command store env (fold_command c) = interp_command store env c.
    Proof.
      generalize dependent (store).
      generalize dependent (env).
      induction c; cbn; intros;
        try (rewrite IHc);
        try (rewrite IHc1, IHc2);
        try (rewrite fold_expr_correct);
        try reflexivity.
      - apply fold_left_extensionality.
        intros. apply IHc.
    Qed.
  End fold_expr.

  Definition partial {t : type} := @fold_expr (@partial_head) t.

  Fixpoint constant_folding' {t : type} (e : expr t) : expr t * option (interp_type t) :=
    match e with
    | EVar _ x => (EVar _ x, None)
    | ELoc _ x => (ELoc _ x, None)
    | EAtom a => (EAtom a, Some (interp_atom a))
    | EUnop o e1 =>
        let (e1', v) := constant_folding' e1 in
        match v with
        | Some v' => let r := interp_unop o v' in (reify _ r, Some r)
        | _ => (EUnop o e1', None)
        end
    | EBinop o e1 e2 =>
        let (e1', v1) := constant_folding' e1 in
        let (e2', v2) := constant_folding' e2 in
        match v1, v2 with
        | Some v1', Some v2' => let r := interp_binop o v1' v2' in (reify _ r, Some r)
        | _, _ => (EBinop o e1' e2', None)
        end
    | EFlatmap e1 x e2 =>
        match constant_folding' e1 with
        | (_, Some nil) => (EAtom (ANil _), Some nil)
        | (e1', _) => match constant_folding' e2 with
                      | (_, Some nil) => (EAtom (ANil _), Some nil)
                      | (e2', _) => (EFlatmap e1' x e2', None)
                      end
        end
    | EFold e1 e2 x y e3 => (EFold (fst(constant_folding' e1)) (fst(constant_folding' e2)) x y (fst(constant_folding' e3)), None)
    | EIf e1 e2 e3 => (EIf (fst (constant_folding' e1)) (fst (constant_folding' e2)) (fst (constant_folding' e3)), None)
    | ELet x e1 e2 => (ELet x (fst (constant_folding' e1)) (fst (constant_folding' e2)), None)
    end.

  Lemma flat_map_all_nil A B (f: A -> list B) l :
    (forall x, f x = nil) -> flat_map f l = nil.
  Proof. induction l; try easy. intros. cbn. rewrite H. cbn. apply (IHl H). Qed.

  Lemma constant_folding'_snd_correct {t : type} (store env : locals) (e : expr t) :
    forall c, snd (constant_folding' e) = Some c -> interp_expr store env e = c.
  Proof.
    generalize dependent env. generalize dependent store.
    induction e; intros; simpl; try easy.

    - inversion H. reflexivity.

    - simpl in H.
      destruct (constant_folding' e). destruct o0; inversion H.
      rewrite (IHe store env i); easy.

    - simpl in H.
      destruct (constant_folding' e1). destruct (constant_folding' e2). destruct o0; destruct o1; inversion H.
      rewrite (IHe1 store env i), (IHe2 store env i0); easy.

    - simpl in H.
      destruct constant_folding'.

      destruct o; try discriminate;
        try (destruct i; try discriminate).
      1: inversion H; rewrite (IHe1 _ _ nil); reflexivity.

      all: destruct constant_folding';
         destruct o; try discriminate;
         try (destruct i); try (destruct i1); try discriminate;
         inversion H;
         apply flat_map_all_nil; intros; rewrite (IHe2 _ _ nil); reflexivity.
  Qed.

  Definition constant_folding {t : type} (e : expr t) : expr t := fst (constant_folding' e).

  Lemma constant_folding_correct {t : type} (store env : locals) (e : expr t) :
    interp_expr store env (constant_folding e) = interp_expr store env e.
  Proof.
    generalize dependent env. generalize dependent store.
    unfold constant_folding.
    induction e; intros; simpl; try easy.

    - destruct (constant_folding' e) eqn:E. destruct o0; simpl.
      + rewrite reify_correct.
        f_equal.
        simpl in IHe.
        rewrite (constant_folding'_snd_correct store env e i); try easy.
        rewrite E. reflexivity.
      + simpl in IHe. rewrite IHe. reflexivity.

    - destruct (constant_folding' e1) eqn:E1. destruct (constant_folding' e2) eqn:E2. destruct o0; destruct o1; simpl.
      all: try (rewrite IHe1, IHe2; reflexivity).
      rewrite reify_correct.
      f_equal.
      * simpl in IHe1.
        rewrite (constant_folding'_snd_correct store env e1 i); try easy. rewrite E1. reflexivity.
      * simpl in IHe2.
        rewrite (constant_folding'_snd_correct store env e2 i0); try easy. rewrite E2. reflexivity.
    - destruct (constant_folding' e1) eqn:E1, (constant_folding' e2) eqn:E2.
      destruct o.
      * destruct i.
        ** assert (interp_expr store env e1 = nil).
           { apply (constant_folding'_snd_correct). rewrite E1. reflexivity. }
           rewrite H; reflexivity.
        ** destruct o0;
            try (destruct i1); cbn;
            try (rewrite IHe1; apply flat_map_ext; easy).
           rewrite flat_map_all_nil; try easy. intros.
           assert (H: snd (constant_folding' e2) = Some nil). { rewrite E2. easy. }
           apply (constant_folding'_snd_correct store (set_local env x x0) e2 _ H).
      * destruct o0;
            try (destruct i); cbn;
            try (rewrite IHe1; apply flat_map_ext; easy).
           rewrite flat_map_all_nil; try easy. intros.
           assert (H: snd (constant_folding' e2) = Some nil). { rewrite E2. easy. }
           apply (constant_folding'_snd_correct store (set_local env x x0) e2 _ H).
    - rewrite IHe1.
      f_equal; eauto.
      apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      easy.
    - rewrite IHe1, IHe2, IHe3. reflexivity.
    - rewrite IHe1, IHe2. reflexivity.
  Qed.

  Fixpoint branch_elim {t : type} (e : expr t) : expr t :=
    match e in expr t' return expr t' with
    | EVar _ x => EVar _ x
    | ELoc _ x => ELoc _ x
    | EAtom a => EAtom a
    | EUnop o e1 => EUnop o (branch_elim e1)
    | EBinop o e1 e2 => EBinop o (branch_elim e1) (branch_elim e2)
    | EIf e1 e2 e3 =>
        let e1' := branch_elim e1 in
        let e2' := branch_elim e2 in
        let e3' := branch_elim e3 in
        match as_const e1' with
        | Some true => e2'
        | Some false => e3'
        | _ => EIf e1' e2' e3'
        end
    | EFlatmap e1 x e2 => EFlatmap (branch_elim e1) x (branch_elim e2)
    | EFold e1 e2 x y e3 => EFold (branch_elim e1) (branch_elim e2) x y (branch_elim e3)
    | ELet x e1 e2 => ELet x (branch_elim e1) (branch_elim e2)
    end.

  Lemma branch_elim_correct {t : type} (store env : locals) (e : expr t)
    : interp_expr store env (branch_elim e) = interp_expr store env e.
  Proof.
    generalize dependent env. generalize dependent store.
    induction e; simpl; intros;
    try rewrite <- IHe; try rewrite <- IHe1; try rewrite <- IHe2; try rewrite <- IHe3;
    try reflexivity.

    - assert (H:(fun y : interp_type t1 => interp_expr store (set_local env x y) (branch_elim e2))
              = (fun y => interp_expr store (set_local env x y) e2)).
      { apply functional_extensionality. intros. rewrite IHe2. reflexivity. }
      rewrite H. reflexivity.

    - f_equal.
      do 2 (apply functional_extensionality; intros).
      easy.

    - destruct (as_const (branch_elim e1)) eqn:H; try easy.
      destruct i; rewrite (as_const_correct store env (branch_elim e1) _ H); reflexivity.
  Qed.

  Fixpoint is_name_used {t : type} (x : string) (e : expr t) : bool :=
    match e with
    | EVar _ x' => eqb x' x
    | ELoc _ x' => eqb x' x
    | EAtom _ => false
    | EUnop _ e1 => is_name_used x e1
    | EBinop _ e1 e2 => is_name_used x e1 || is_name_used x e2
    | EFlatmap e1 x' e2 => is_name_used x e1 || (negb (eqb x' x) && is_name_used x e2)
    | EFold e1 e2 x' y' e3 => is_name_used x e1 || is_name_used x e2 ||
                                (negb (eqb x' x) && negb (eqb y' x) && is_name_used x e3)
    | EIf e1 e2 e3 => is_name_used x e1 || is_name_used x e2 || is_name_used x e3
    | ELet x' e1 e2 => is_name_used x e1 || (negb (eqb x' x) && is_name_used x e2)
    end.

  Lemma set_local_same {tx ty : type} (x : string) (vx : interp_type tx) (vy : interp_type ty) (l : locals)
    : set_local (set_local l x vx) x vy = set_local l x vy.
  Proof.
    unfold set_local.
    apply map.map_ext.
    intros.
    rewrite map.get_put_dec.
    destruct (eqb x k) eqn:E.
    - rewrite eqb_eq in E. rewrite E. rewrite map.get_put_same. reflexivity.
    - rewrite eqb_neq in E. rewrite map.get_put_diff; auto.
      rewrite map.get_put_diff; auto.
  Qed.

  Lemma set_local_comm_diff {tx ty : type} (x y : string) (vx : interp_type tx) (vy : interp_type ty) (l : locals)
    : x <> y -> set_local (set_local l y vy) x vx = set_local (set_local l x vx) y vy.
  Proof.
    unfold set_local.
    intros.
    apply map.map_ext.
    intros.
    rewrite 4 map.get_put_dec.
    repeat destruct_one_match; try rewrite map.get_put_diff; tauto.
  Qed.

  Lemma is_name_used_correct {t : type} {t' : type} (store env : locals) (e : expr t) (x : string):
    forall y : interp_type t', is_name_used x e = false -> interp_expr store (set_local env x y) e = interp_expr store env e.
  Proof.
    generalize dependent env. generalize dependent store.
    induction e; intros; simpl in H; simpl.

    - unfold get_local, set_local.
      rewrite map.get_put_diff; try easy.
      apply eqb_neq, H.

    - reflexivity.

    - reflexivity.

    - now rewrite IHe.

    - rewrite IHe1, IHe2; destruct (is_name_used x e2); destruct (is_name_used x e1); try easy.

    - destruct (is_name_used x e1) eqn:E; simpl in *; try discriminate.
      destruct (String.eqb x0 x) eqn:Hx; simpl in *.
      + rewrite eqb_eq in Hx. subst.
        rewrite IHe1; eauto.
        f_equal.
        apply functional_extensionality. intros.
        now rewrite set_local_same.
      + rewrite eqb_neq in Hx.
        rewrite IHe1; eauto.
        f_equal.
        apply functional_extensionality. intros.
        rewrite set_local_comm_diff; eauto.

    - destruct (is_name_used x e1) eqn:He1; simpl in *; try discriminate.
      destruct (is_name_used x e2) eqn:He2; simpl in *; try discriminate.
      destruct (eqb x0 x) eqn:H0x; simpl in *;
      destruct (eqb y x) eqn:Hyx; simpl in *;
      rewrite IHe1, IHe2; eauto; f_equal; repeat (apply functional_extensionality; intros);
      try rewrite eqb_eq in *; try rewrite eqb_neq in *; try subst.
      + now rewrite !set_local_same.
      + now rewrite !set_local_same.
      + rewrite set_local_comm_diff; eauto.
        rewrite !set_local_same.
        now rewrite set_local_comm_diff.
      + rewrite !set_local_comm_diff with (y := x); eauto.

    - rewrite IHe1, IHe2, IHe3;
      destruct (is_name_used x e1);
      destruct (is_name_used x e2);
      destruct (is_name_used x e3);
      easy.

    - destruct (is_name_used x e1); simpl in *; try discriminate.
      destruct (eqb x0 x) eqn:Hx; simpl in *;
      try rewrite eqb_eq in *; try rewrite eqb_neq in *; try subst;
      rewrite IHe1; eauto.
      + now rewrite set_local_same.
      + rewrite set_local_comm_diff; eauto.
  Qed.

  Fixpoint unused_name_elim {t : type} (e : expr t) : expr t :=
    match e with
    | EVar _ x => EVar _ x
    | ELoc _ x => ELoc _ x
    | EAtom a => EAtom a
    | EUnop o e1 => EUnop o (unused_name_elim e1)
    | EBinop o e1 e2 => EBinop o (unused_name_elim e1) (unused_name_elim e2)
    | EFlatmap e1 x e2 => EFlatmap (unused_name_elim e1) x (unused_name_elim e2)
    | EFold e1 e2 x y e3 => EFold (unused_name_elim e1) (unused_name_elim e2) x y (unused_name_elim e3)
    | EIf e1 e2 e3 => EIf (unused_name_elim e1) (unused_name_elim e2) (unused_name_elim e3)
    | ELet x e1 e2 => if is_name_used x e2 then ELet x (unused_name_elim e1) (unused_name_elim e2) else unused_name_elim e2
    end.

  Lemma unused_name_elim_correct {t : type} (store env : locals) (e : expr t)
    : interp_expr store env (unused_name_elim e) = interp_expr store env e.
  Proof.
    generalize dependent env. generalize dependent store.
    induction e; try easy; intros; simpl.

    - rewrite IHe. reflexivity.

    - rewrite IHe1, IHe2. reflexivity.

    - assert (H:(fun y : interp_type t1 => interp_expr store (set_local env x y) (unused_name_elim e2))
              = (fun y => interp_expr store (set_local env x y) e2)).
      { apply functional_extensionality. intros. rewrite IHe2. reflexivity. }
      rewrite IHe1, H. reflexivity.

    - f_equal; eauto.
      do 2 (apply functional_extensionality; intros).
      eauto.

    - rewrite IHe1, IHe2, IHe3. reflexivity.

    - destruct (is_name_used x e2) eqn:E.
      + simpl. rewrite IHe1, IHe2. reflexivity.
      + rewrite is_name_used_correct; easy.
  Qed.

  Definition flatmap_flatmap_head {t : type} (e : expr t) : expr t :=
    match e with
    | EFlatmap l x f => match l with
                        | EFlatmap l' y g => if orb (is_name_used y f) (eqb x y)
                                              then EFlatmap l x f
                                              else EFlatmap l' y (EFlatmap g x f)
                        | l' => EFlatmap l' x f
                        end
    | e' => e'
    end.

  Lemma flat_map_flat_map :
    forall {A B C} (l : list A) (f : B -> list C)  (g : A -> list B),
    flat_map f (flat_map g l) = flat_map (fun x => flat_map f (g x)) l.
  Proof.
    induction l; auto.
    intros. simpl. rewrite flat_map_app. rewrite IHl. reflexivity.
  Qed.
End WithMap2.

(* Workaround for COQBUG <https://github.com/coq/coq/issues/17555> *)
Section WithMap3.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {locals: map.map string {t & interp_type (width := width) t}} {locals_ok: map.ok locals}.

  Lemma flatmap_flatmap_head_correct {t : type} (store env : locals) (e : expr t)
    : interp_expr store env (flatmap_flatmap_head e) = interp_expr store env e.
  Proof.
    destruct e; auto.
    dependent induction e1; auto; simpl.
    destruct_one_match; auto;
    simpl. rewrite flat_map_flat_map. f_equal. apply functional_extensionality.
    intros. f_equal. apply functional_extensionality.
    intros. rewrite set_local_comm_diff.
    + apply is_name_used_correct, E.
    + apply E.
  Qed.

  Definition flatmap_flatmap {t} : expr t -> expr t := fold_expr (@flatmap_flatmap_head).

  Goal forall s x, eUnop (OLength _) (eUnop (OFst s _ _)
    (EBinop (OPair s _ _)
      (EBinop ORange (EAtom (AInt 1)) (EAtom (AInt 5)))
      (EVar TInt x)))
  = EAtom (AInt 4).
  Proof. cbv. solve [trivial]. Abort.

  Lemma fold_flatmap : forall {A B C} (l : list A) (f : A -> list B) (g : B -> C -> C) (a : C),
    fold_right g a (flat_map f l) = fold_right (fun x y => fold_right g y (f x)) a l.
  Proof.
    induction l; eauto.
    intros. cbn. rewrite fold_right_app. f_equal. eauto.
  Qed.

  Definition fold_flatmap_head {t : type} (e : expr t) : expr t :=
    match e with
    | EFold l a x y f => match l with
                         | EFlatmap l' z g =>
                             if is_name_used z f || is_name_used y g || String.eqb x y || String.eqb x z || String.eqb y z
                             then EFold (EFlatmap l' z g) a x y f
                             else EFold l' a z y (EFold g (EVar _ y) x y f)
                         | l' => EFold l' a x y f
                         end
    | e' => e'
    end.

  (* Should be in Coqutil *)
  Lemma bool_dec_refl : forall b, Bool.bool_dec b b = left eq_refl.
  Proof.
    intros.
    destruct b; simpl; eauto.
  Qed.

  Lemma ascii_dec_refl : forall c, Ascii.ascii_dec c c = left eq_refl.
  Proof.
    intros.
    destruct c; eauto.
    repeat (simpl; rewrite bool_dec_refl). simpl. f_equal.
  Qed.

  Lemma string_dec_refl : forall s, string_dec s s =  left eq_refl.
  Proof.
    intros.
    induction s; simpl; eauto.
    repeat (simpl; rewrite ascii_dec_refl). simpl. rewrite IHs. simpl. f_equal.
  Qed.

  Lemma type_eq_dec_refl : forall t, type_eq_dec t t = left eq_refl.
  Proof.
    induction t; eauto; simpl.
    - rewrite string_dec_refl. simpl.
      rewrite IHt1. simpl.
      rewrite IHt2. simpl.
      f_equal.
    - rewrite IHt. simpl.
      f_equal.
  Qed.

  Lemma fold_flatmap_head_correct {t : type} (store env : locals) (e : expr t)
    : interp_expr store env (fold_flatmap_head e) = interp_expr store env e.
  Proof.
    destruct e; eauto.
    dependent induction e1; eauto; simpl.
    destruct_one_match; eauto.
    simpl. rewrite fold_flatmap. f_equal. apply functional_extensionality.
    intros. f_equal. apply functional_extensionality.
    intros. f_equal.
    - apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      repeat rewrite set_local_comm_diff with (y := x); try apply E.
      rewrite set_local_comm_diff with (x := x0); try apply E.
      rewrite set_local_same.
      apply is_name_used_correct, E.
    - unfold get_local, set_local.
      rewrite map.get_put_same.
      unfold proj_expected. simpl.
      rewrite type_eq_dec_refl. reflexivity.
    - apply is_name_used_correct, E.
  Qed.

  Definition invert_singleton {t : type} (e : expr (TList t)) : option (expr t) :=
    match e in expr t' return option (expr t) with
    | EBinop (OCons t') h (EAtom (ANil _)) => match type_eq_dec t' t with
                               | left H => Some (cast H _ h)
                               | right _ => None
                               end
    | _ => None
    end.

  Definition fold_flatmap_singleton_head {t : type} (e : expr t) : expr t :=
    match e with
    | EFold l a x y f => match l with
                         | EFlatmap l' z g =>
                             if is_name_used z f || is_name_used y g || String.eqb x y || String.eqb x z || String.eqb y z
                             then EFold (EFlatmap l' z g) a x y f
                             else match invert_singleton g with
                                  | Some e => EFold l' a z y (ELet x e f)
                                  | None => EFold (EFlatmap l' z g) a x y f
                                  end
                         | l' => EFold l' a x y f
                         end
    | e' => e'
    end.

  Compute fold_flatmap_singleton_head
    (EFold
      (EFlatmap
        (EBinop
          (OCons TInt)
          (EAtom (AInt 3))
          (EAtom (ANil TInt))
        )
        "z"
        (EBinop
          (OCons TInt)
          (EBinop
            OTimes
            (EVar TInt "z")
            (EVar TInt "z")
          )
          (EAtom (ANil TInt))
        )
      )
      (EAtom (AInt 0))
      "x" "y"
      (EBinop
        OPlus
        (EVar TInt "x")
        (EVar TInt "y")
      )
    ).

  Lemma fold_flatmap_singleton {A B C} (l : list A) (f : A -> B) (g : B -> C -> C) (a : C):

    fold_right g a (flat_map (fun x => f x :: nil) l) = fold_right (fun x y => g (f x) y) a l.
  Proof.
    induction l; eauto.
    intros. cbn. f_equal. eauto.
  Qed.

  Lemma fold_flatmap_singleton_head_correct {t : type} (store env : locals) (e : expr t)
    : interp_expr store env (fold_flatmap_singleton_head e) = interp_expr store env e.
  Proof.
    destruct e; eauto.
    dependent induction e1; eauto; simpl.
    repeat (destruct_one_match; eauto).
    unfold invert_singleton in *.
    dependent induction e1_2; simpl in E0; try discriminate.
    dependent induction o; simpl in E0; try discriminate.
    dependent induction e1_2_2;  simpl in E0; try discriminate.
    dependent induction a.
    rewrite type_eq_dec_refl in E0. injection E0 as E0. subst.
    simpl.
    rewrite fold_flatmap_singleton.
    f_equal. repeat (apply functional_extensionality; intros).
    cbn [is_name_used] in E.
    rewrite! Bool.orb_false_r in E.
    repeat rewrite set_local_comm_diff with (y := x); try apply E.
    rewrite is_name_used_correct; try apply E.
    f_equal.
    rewrite set_local_comm_diff with (x := x0); try apply E.
    do 2 f_equal.
    rewrite set_local_comm_diff with (x := x).
    - rewrite is_name_used_correct; try apply E. reflexivity.
    - apply not_eq_sym. apply E.
  Qed.

  Definition flatmap_singleton_head {t} (e : expr t) : expr t :=
    match e in expr t' return expr t' with
    | EFlatmap l x f => match l with
                        | EBinop (OCons _) e' (EAtom (ANil _)) => ELet x e' f
                        | l'  => EFlatmap l' x f
                        end
    | e' => e'
    end.

  Lemma flatmap_singleton_head_correct {t} (store env : locals) (e : expr t) :
    interp_expr store env (flatmap_singleton_head e) = interp_expr store env e.
  Proof.
    destruct e; simpl; eauto.
    dependent induction e1; eauto.
    dependent induction o; eauto.
    dependent induction e1_2; eauto.
    dependent induction a; eauto.
    simpl.
    now rewrite app_nil_r.
  Qed.

  Definition flatmap_singleton {t : type} : expr t -> expr t := fold_expr (@flatmap_singleton_head).

  (* Everything below is WIP *)

  Definition substitute_let {t} (e : expr t) : expr t.
  (* This optimization should replace
      let x = ex in e
    with an expression with ex substituted for x in e:
      substitute x ex e
    An early attempt at implementing this is below, but has some bugs.
   *)
  Proof. Abort.

  (* First attempt at implementing substitute.
     HAS A BUG - see comment for ELet *)
  Fixpoint substitute {t tx : type} (x : string) (ex : expr tx) (e : expr t): expr t
    := match e in expr t' return expr t' with
       | EVar t' x' => match type_eq_dec tx t', String.eqb x x' return expr t' with
                       | left H, true => cast H _ ex
                       | _, _ => EVar t' x'
                       end
       | ELoc t' x' => ELoc t' x'
       | EAtom a => EAtom a
       | EUnop o e' => EUnop o (substitute x ex e')
       | EBinop o e1 e2 => EBinop o (substitute x ex e1) (substitute x ex e2)
       | EFlatmap e1 x' e2 => if String.eqb x x' || is_name_used x' ex
                                then EFlatmap e1 x' e2
                                else EFlatmap (substitute x ex e1) x' (substitute x ex e2)
       | EFold e1 e2 x' y e3 => if String.eqb x x' || String.eqb x y || is_name_used x' ex || is_name_used y ex
                                  then EFold e1 e2 x' y e3
                                  else EFold (substitute x ex e1) (substitute x ex e2) x' y (substitute x ex e3)
       | EIf e1 e2 e3 => EIf (substitute x ex e1) (substitute x ex e2) (substitute x ex e3)

       (* We should rename `x'` to something that does not occur in `ex` *)
       (* We should also substitute occurrences of `x` in `ex'` *)
       | ELet x' ex' e' => if String.eqb x x' || is_name_used x' ex
                             then ELet x' ex' e'
                             else ELet x' ex' (substitute x ex e')
       end.

  (* Correct, but old and not-strong-enough version of substitute_correct.
     PHOAS was suggested as a possible approach to prove the right version.
     For the meantime, I've left the old version here... *)
  Lemma substitute_correct' {t tx : type} (store env : locals) (x : string) (ex : expr tx) (e : expr t) :
    get_local env x = interp_expr store env ex -> interp_expr store env (substitute x ex e) = interp_expr store env e.
  Proof.
    generalize dependent env. generalize dependent store.
    induction e; intros; simpl.
    - repeat (destruct_one_match; eauto). now subst.
    - reflexivity.
    - eauto.
    - now rewrite IHe.
    - now rewrite IHe1, IHe2.
    - repeat (destruct_one_match; eauto).
      simpl. rewrite IHe1; eauto.
      f_equal. apply functional_extensionality. intros.
      rewrite IHe2; eauto.
      unfold get_local, set_local in *.
      destruct E.
      rewrite !map.get_put_diff; eauto.
      rewrite H.
      epose proof is_name_used_correct as inuc.
      unfold set_local in inuc.
      now rewrite inuc.
    - repeat (destruct_one_match; eauto).
      repeat match goal with [H : _ /\ _ |- _] => destruct H end.
      simpl. rewrite IHe1, IHe2; eauto.
      f_equal. repeat (apply functional_extensionality; intros).
      rewrite IHe3; eauto.
      unfold get_local, set_local in *.
      rewrite !map.get_put_diff; eauto.
      rewrite H.
      pose proof @is_name_used_correct.
      unfold set_local in H4.
      now rewrite !H4.
    - now rewrite IHe1, IHe2, IHe3.
    - destruct_one_match; eauto.
      simpl. rewrite IHe2; eauto.
      unfold get_local at 1, set_local at 1.
      unfold get_local in H.
      repeat match goal with [H : _ /\ _ |- _] => destruct H end.
      rewrite map.get_put_diff; eauto.
      rewrite H.
      now rewrite is_name_used_correct.
  Abort.
End WithMap3.

(* Workaround for COQBUG <https://github.com/coq/coq/issues/17555> *)
Section WithMap4.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {locals: map.map string {t & interp_type (width := width) t}} {locals_ok: map.ok locals}.


  (* Checks if an expression contains a variable, irrespective of shadowing. It should be called with a dephoasified expression that has globally unique names *)
  Fixpoint contains_variable {t : type} (e : expr t) (x : string) : bool :=
    match e with
    | EVar _ s => (s =? x)%string
    | ELoc _ s => false
    | EAtom a => false
    | EUnop o e1 => contains_variable e1 x
    | EBinop o e1 e2 => contains_variable e1 x || contains_variable e2 x
    | EFlatmap l1 v fn => (x =? v)%string || contains_variable l1 x || contains_variable fn x
    | EIf e1 e2 e3 => contains_variable e1 x || contains_variable e2 x || contains_variable e3 x
    | EFold l1 a v1 v2 fn => (x =? v1)%string || (x =? v2)%string || contains_variable l1 x || contains_variable a x || contains_variable fn x
    | ELet v e1 e2 => (x =? v)%string || contains_variable e1 x || contains_variable e2 x
    end.

  Definition move_filter' {t : type} (e : expr t) : option (expr t) :=
    match e with
    | @EFlatmap _ t1 l x f => 
        match f in expr t' return option (expr t') with
        | @EIf t2 pred e1 e2 =>
            match t2 return (expr t2 -> expr t2 -> option (expr t2)) with
            | TList t => fun e1' e2' => Some
                (if contains_variable pred x
                 then EFlatmap l x (EIf pred e1' e2')
                 else EIf pred (EFlatmap l x e1') (EFlatmap l x e2'))
            | _ => fun _ _ => None
            end e1 e2
        | _ => None
        end
    | _ => None
    end.
  Definition move_filter {t : type} (e : expr t) : expr t :=
    match move_filter' e with
    | Some e' => e'
    | None => e
    end.

  Lemma doesnt_contain_same {t1 t2 : type} (store env : locals) (e : expr t1) (x : string) (y : interp_type t2):
    contains_variable e x = false ->
    interp_expr store (set_local env x y) e = interp_expr store env e.
  Proof.
    symmetry. intros. revert env. induction e; 
      try reflexivity; cbn; cbn in H;
      try (intros; rewrite IHe; try easy);
      try (rewrite IHe; try easy); intros.
    - destruct (x0 =? x)%string eqn:E.
      + apply eqb_eq in E; subst.
        exfalso. apply Bool.diff_true_false in H. apply H.
      + apply eqb_neq in E.
        unfold get_local, set_local.
        rewrite map.get_put_diff by congruence.
        reflexivity.
    - apply Bool.orb_false_elim in H.
      rewrite IHe1, IHe2; try easy.
    - repeat (apply Bool.orb_false_elim in H; destruct H).
      rewrite IHe1 by easy. apply flat_map_ext.
      unfold set_local. rewrite eqb_neq in H.
      intros. rewrite map.put_put_diff by congruence.
      rewrite IHe2 by congruence.
      reflexivity.
    - repeat (apply Bool.orb_false_elim in H; destruct H).
      rewrite IHe1, IHe2 by easy.
      induction (interp_expr store (set_local env x y) e1); try reflexivity.
      cbn. rewrite IHi.
      rewrite IHe3 by congruence.
      unfold set_local. rewrite eqb_neq in H, H3.
      rewrite (map.put_put_diff _ x x0) by congruence.
      rewrite (map.put_put_diff _ x y0) by congruence.
      reflexivity.
    - repeat (apply Bool.orb_false_elim in H; destruct H).
      rewrite IHe1, IHe2, IHe3 by congruence.
      reflexivity.
    - repeat (apply Bool.orb_false_elim in H; destruct H).
      rewrite IHe1, IHe2 by congruence.
      unfold set_local. apply eqb_neq in H.
      rewrite map.put_put_diff by congruence.
      reflexivity.
  Qed.

  Theorem move_filter_correct {t : type} (store env : locals) (e : expr t) :
    interp_expr store env (move_filter e) = interp_expr store env e.
  Proof.
    destruct e as [| | | | | t1 t2 l x f| | |]; try reflexivity.
    refine (
      match f with
      | EIf pred e1 e2 => _
      | _ => _
      end
    ); try (destruct t; try easy);
       try (destruct t0; easy);
       try (destruct t3; easy).

   cbn.
   destruct (contains_variable pred x) eqn:contains; try reflexivity.

   cbn.
   destruct (interp_expr store env pred) eqn:E;
     apply flat_map_ext; intros;
     rewrite (doesnt_contain_same _ _ pred) by congruence;
     rewrite E; reflexivity.
  Qed.

  Theorem move_filter_fold_correct {t : type} (store env : locals) (e : expr t) :
    interp_expr store env (fold_expr (@move_filter) e) = interp_expr store env e.
  Proof. apply fold_expr_correct. intros. apply move_filter_correct. Qed.


  Fixpoint flatten_concat_str (e : expr TString) : list (expr TString) :=
    match e with
    | EBinop OConcatString s1 s2 => flatten_concat_str s1 ++ flatten_concat_str s2
    | _ => e :: nil
    end.

  Fixpoint merge_assoc_list (l : list (expr TString)) : list (expr TString) :=
    match l with
    | EAtom (AString s1) :: l' =>
        match merge_assoc_list l' with
        | e2 :: l'' => match e2 with
                       | EAtom (AString s2) => EAtom (AString (s1 ++ s2)) :: l''
                       | _ => EAtom (AString s1) :: e2 :: l''
                       end
        | l'' => EAtom (AString s1) :: l''
        end
    | e1 :: l' => e1 :: merge_assoc_list l'
    | nil => nil
    end.

  Fixpoint concat_flat_list (l : list (expr TString)) : expr TString :=
    match l with
    | nil => EAtom (AString "")
    | x :: nil => x
    | x :: xs => EBinop OConcatString x (concat_flat_list xs)
    end.

  Definition constant_fold_assoc {t : type} (e : expr t) : expr t :=
    match t return expr t -> expr t with
    | TString => fun e => concat_flat_list (merge_assoc_list (flatten_concat_str e))
    | _ => fun e => e
    end e.

  Lemma concat_move_head (store env : locals) a l :
    interp_expr store env (concat_flat_list (a :: l)) =
    (interp_expr store env a ++ interp_expr store env (concat_flat_list l))%string.
  Proof.
    revert a. induction l; intros.
    - cbn. induction interp_expr; cbn; congruence.
    - cbn. cbn in IHl. congruence.
  Qed.

  Lemma concat_flat_append (store env : locals) (l1 l2 : list (expr TString)) :
    interp_expr store env (concat_flat_list (l1 ++ l2)) =
    interp_expr store env (EBinop OConcatString (concat_flat_list l1) (concat_flat_list l2)).
  Proof.
    revert l2. induction l1; try reflexivity.
    intros.
    replace ((a :: l1) ++ l2) with (a :: (l1 ++ l2)) by reflexivity.
    rewrite concat_move_head. rewrite IHl1.
    cbn.
    destruct l1; try reflexivity.
    rewrite <- string_app_assoc.
    f_equal.
  Qed.

  Definition expr_is_atom_str {t : type} (e : expr t) :=
    match e with
    | EAtom (AString s) => Some s
    | _ => None
    end.

  Lemma is_const_str_eq {t : type} (e : expr t) s :
    match t return expr t -> Prop with
    | TString => fun e => expr_is_atom_str e = Some s -> e = EAtom (AString s)
    | _ => fun _ => True
    end e.
  Proof.
    intros. destruct e; try easy;
        try (destruct t; easy);
        try (destruct t2; easy);
        try (destruct t3; easy).
        destruct a; try easy.
        cbn. intros. inversion H. easy.
  Qed.

  Lemma merge_flat_list_move_head e l :
    expr_is_atom_str e = None ->
    concat_flat_list (merge_assoc_list (e :: l)) =
    concat_flat_list (e :: merge_assoc_list l).
  Proof.
    cbn.
    refine (match e with
            | EAtom _ => _
            | _ => _
            end);
      try (destruct t; easy);
      try (destruct t0; easy);
      try (destruct t1; easy).
      destruct a; easy.
  Qed.

  Lemma merge_flat_list_move_snd_head {t : type} e a l :
    expr_is_atom_str a = None ->
    match t return expr t -> expr t -> Prop with
    | TString => fun e a =>
                        concat_flat_list (merge_assoc_list (e :: a :: l)) =
                        concat_flat_list (e :: a :: merge_assoc_list l)
    | _ => fun _ _ => True
    end e a.
  Proof.
    destruct a; try easy;
     try (destruct a; easy);
     destruct e; try easy;
     try (destruct a; try easy);
     try (destruct a0; try easy);
     try (destruct t; try easy);
     try (destruct t2; try easy);
     try (destruct t3; try easy);
     try (destruct t4; try easy).
  Qed.

  Lemma merge_flat_list_move_both_head (* store env *) s1 s2 l :
    merge_assoc_list (EAtom (AString s1) :: EAtom (AString s2) :: l) =
    merge_assoc_list (EAtom (AString (s1 ++ s2)) :: l).
  Proof.
    cbn. induction merge_assoc_list; try reflexivity.
    refine (match a with
            | EAtom _ => _
            | _ => _
            end);
           try (destruct t0; easy);
           try (destruct t1; easy);
           try (destruct t; try easy).
    refine (match a0 with
            | AString _ => _
            | _ => _
            end); try easy.
    cbn.
    induction l0; cbn; rewrite string_app_assoc; reflexivity.
  Qed.

  Lemma concat_merge_flat_correct {t : type} (store env : locals) (l : list (expr t)) :
    match t return list (expr t) -> Prop with
    | TString => fun l => interp_expr store env (concat_flat_list (merge_assoc_list l)) = interp_expr store env (concat_flat_list l)
    | _ => fun _ => True
    end l.
  Proof.
    assert (str_prepend_eq:forall s s1 s2,
      (s ++ s1)%string = (s ++ s2)%string -> s1 = s2).
    { induction s; try easy. intros. inversion H. apply (IHs _ _ H1). }

    destruct l; try (destruct t; easy).
    revert e. induction l.
    { destruct e; try easy;
        try (destruct t; easy);
        try (destruct t2; easy);
        try (destruct t3; easy).
      destruct a; easy. }

    intros.
    destruct (expr_is_atom_str e) eqn:e_const.
    - destruct e; try discriminate.
      destruct (expr_is_atom_str a) eqn:a_const;
      destruct a; try easy;
        try (destruct a; easy); (* False EAtom case *)
        try (destruct a0; try easy);
        try (destruct t; try easy);
        try (destruct t2; try easy);
        try (destruct t3; try easy).
      1: { (* EAtom (AString _) :: EAtom (AString _) case *)
        refine (match a with
                | AString _ => _
                | _ => _
                end); try easy.
        rewrite merge_flat_list_move_both_head.
        rewrite IHl.
        repeat rewrite concat_move_head.
        cbn.
        apply string_app_assoc.
      }
      all:
        specialize (IHl (EVar _ "foo")); (* A trick in order to get indcutive hypothesis on just l and not e :: l *)
        rewrite merge_flat_list_move_head in IHl by reflexivity;
        repeat rewrite concat_move_head in IHl;
        apply str_prepend_eq in IHl;
        rewrite (@merge_flat_list_move_snd_head TString) by reflexivity;
        repeat rewrite concat_move_head;
        rewrite IHl; reflexivity.
    - destruct e;
        try (destruct a0; try easy); (* EAtom case *)
        try (destruct t; try reflexivity);
        try (destruct t2; try reflexivity);
        try (destruct t3; try reflexivity);
        try (destruct a0; try reflexivity);
        try (rewrite merge_flat_list_move_head by reflexivity;
             repeat rewrite concat_move_head;
             rewrite IHl;
             rewrite concat_move_head;
             reflexivity).
  Qed.

  Theorem concat_flatten_inv {t : type} (store env : locals) (e : expr t) :
    match t return expr t -> Prop with
    | TString => fun e => interp_expr store env (concat_flat_list (flatten_concat_str e)) = interp_expr store env e
    | _ => fun _ => True
    end e.
  Proof.
    induction e;
      try (destruct t; reflexivity);
      try (destruct t2; reflexivity).
    destruct o; try reflexivity.
    cbn. rewrite concat_flat_append.
    cbn. rewrite IHe1, IHe2.
    reflexivity.
  Qed.

  Theorem constant_fold_assoc_correct {t : type} (store env : locals) (e : expr t) :
    interp_expr store env (constant_fold_assoc e) = interp_expr store env e.
  Proof.
    destruct e;
      try (destruct t; reflexivity);
      try (destruct o; try destruct t1, t2; try reflexivity);
      try (destruct t1; reflexivity);
      try (destruct t2; reflexivity);
      try (destruct a; reflexivity).
    cbn.
    rewrite (@concat_merge_flat_correct TString).
    rewrite concat_flat_append.
    cbn.
    repeat rewrite (@concat_flatten_inv TString).
    reflexivity.
  Qed.
End WithMap4.
