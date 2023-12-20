Require Import PyLevelLang.Language.
Require Import PyLevelLang.Phoas_Language.
Require Import PyLevelLang.Phoas_Interpret.
Require Import PyLevelLang.Interpret.
Require Import PyLevelLang.Elaborate.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.


Section WithMap.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {locals: map.map string {t & interp_type (width := width) t}} {locals_ok: map.ok locals}.

  Section constant_folding.
    Context {V : type -> Type}.

  Fixpoint listify {t : type} (l : list (phoas_expr V t)) : phoas_expr V (TList t) :=
    match l with
    | nil => PhEAtom (ANil t)
    | x :: xs => PhEBinop (OCons t) x (listify xs)
    end.

    Fixpoint reify {t : type} : interp_type t -> phoas_expr V t :=
      match t in type return interp_type t -> phoas_expr V t with
      | TWord => fun w => PhEAtom (AWord (word.unsigned w))
      | TInt => fun n => PhEAtom (AInt n)
      | TBool => fun b => PhEAtom (ABool b)
      | TString => fun s => PhEAtom (AString s)
      | TPair s t1 t2 => fun p => PhEBinop (OPair s t1 t2) (reify (fst p)) (reify (snd p))
      | TEmpty => fun _ => PhEAtom AEmpty
      | TList t => fun l => listify (List.map reify l)
      end.


    Fixpoint interp_phoas_value {t : type} (e : phoas_expr V t) : result (interp_type t) :=
      match e with
      | PhEAtom a => Success (interp_atom a)
      | PhEUnop o e1 =>
          v <- interp_phoas_value e1;;
          Success (interp_unop o v)
      | PhEBinop o e1 e2 =>
          v1 <- interp_phoas_value e1;;
          v2 <- interp_phoas_value e2;;
          Success (interp_binop o v1 v2)
      | _ => error:("Expression " e " not a value")
      end.

    (* The left case is a partially simplified expression, the right case is a expression that is syntactically a value *)
    Fixpoint phoas_constant_folding' {t : type}
      (e : phoas_expr V t) : phoas_expr V t + phoas_expr V t :=
      match e with
      | PhEVar t x => inl (PhEVar t x)
      | PhELoc t x => inl (PhELoc t x)
      | PhEAtom a => inr (reify (interp_atom a))
      | PhEUnop o e =>
          match phoas_constant_folding' e with
          | inl e' => inl (PhEUnop o e')
          | inr e' => match interp_phoas_value e' with
                       | Success val => inr (reify (interp_unop o val))
                       | Failure _ => inl (PhEUnop o e') (* This code will never run *)
                       end
          end
      | PhEBinop o e1 e2 =>
          match phoas_constant_folding' e1, phoas_constant_folding' e2 with
          | inr e1', inr e2' =>
              match interp_phoas_value e1', interp_phoas_value e2' with
              | Success v1, Success v2 => inr (reify (interp_binop o v1 v2))
              | _, _ => inl (PhEBinop o e1 e2) (* This code will never run *)
              end
          | inl e1', inr e2' =>
              match interp_phoas_value e2' with
              | Success v2 => inl (PhEBinop o e1' (reify v2))
              | _ => inl (PhEBinop o e1 e2) (* This code will never run *)
              end
          | inr e1', inl e2' =>
              match interp_phoas_value e1' with
              | Success v1 =>  inl (PhEBinop o (reify v1) e2')
              | _ => inl (PhEBinop o e1 e2) (* This code will never run *)
              end
          | inl e1', inl e2' => inl (PhEBinop o e1' e2')
          end
      | PhEFlatmap l1 x fn =>
          let l1' :=
            match phoas_constant_folding' l1 with
            | inl l1' => l1' | inr l1' => l1'
            end
          in let fn' y :=
            match phoas_constant_folding' (fn y) with
            | inl v2 => v2 | inr v2 => v2
            end in
          inl (PhEFlatmap l1' x fn')
              (*
                 flat_map (fun y =>
              match phoas_constant_folding' (fn_l2 y) with
              | inl l2' => l2'
              | inr v2 => v2
              end) v1
              *)
      | PhEFold l1 e2 x y fn =>
          let l1' :=
            match phoas_constant_folding' l1 with
            | inl l1' => l1'
            | inr l1' => l1'
            end in
          let fn' x y :=
            match phoas_constant_folding' (fn x y) with
            | inl l => l
            | inr l => l
            end in
          let e2' :=
            match phoas_constant_folding' e2 with
            | inl e2' => e2'
            | inr e2' => e2'
            end in
          inl (PhEFold l1' e2' x y fn')
      | PhEIf e0 e2 e3 =>
          match phoas_constant_folding' e0 with
          | inl e0' => inl (PhEIf e0' e2 e3)
          | inr e0' => match interp_phoas_value e0' with
                     | Success true => phoas_constant_folding' e2
                     | Success false => phoas_constant_folding' e3
                     | Failure _ => inl (PhEIf e0' e2 e3) (* This should never happen *)
                     end
          end
      | PhELet x e1 fn =>
          let e1' :=
            match phoas_constant_folding' e1 with
            | inl e1' => e1'
            | inr e1' => e1'
            end in
          let fn' y :=
            match phoas_constant_folding' (fn y) with
            | inl l' => l'
            | inr l' => l'
            end in
          inl (PhELet x e1' fn')
      end.
  End constant_folding.

  (*
  Theorem phoas_constant_folding_right_success {t : type} (e e' : phoas_expr interp_type t) v:
    phoas_constant_folding' e = inr e' -> interp_phoas_value e' <> Failure v.
  Proof.
    induction e; try discriminate.
    * cbn. intros. inversion H.
      destruct a; discriminate.
    * cbn.
      destruct (phoas_constant_folding' e); try discriminate.
      destruct (interp_phoas_value p); try discriminate.

      intros. inversion H.
      induction o; try discriminate.
      - destruct a. cbn. 

      - 
   *)

  Lemma interp_expr_reify_id {t : type} (l : locals)
    (e : interp_type t) :
  interp_phoas_expr l (reify e) = e.
  Proof.
    induction t; cbn;
      try rewrite word.of_Z_unsigned;
      try (induction e; cbn; try f_equal; try easy);
      try reflexivity.
  Qed.

  Lemma interp_phoas_value_success {t : type} l a (p : phoas_expr interp_type t):
   interp_phoas_value p = Success a -> interp_phoas_expr l p = a.
  Proof.
    induction p; cbn; try congruence.
    - intros.
      destruct (interp_phoas_value p); try discriminate.
      inversion H.
      rewrite (IHp a0); reflexivity.
    - intros.
      destruct (interp_phoas_value p1); try discriminate.
      destruct (interp_phoas_value p2); try discriminate.
      rewrite (IHp1 a0); try reflexivity.
      rewrite (IHp2 a1); try reflexivity.
      congruence.
  Qed.

  Theorem phoas_constant_folding_correct {t : type} (l : locals) (e : phoas_expr interp_type t) :
    interp_phoas_expr l e = interp_phoas_expr l (match phoas_constant_folding' e with
                                                 | inl l => l
                                                 | inr v => v
                                                 end).
  Proof.
    revert l. induction e; intros; try reflexivity.
    - cbn. destruct a; try reflexivity.
      * cbn. (* Word case *)
        rewrite word.of_Z_unsigned.
        reflexivity.
    - simpl. destruct (phoas_constant_folding' e).
      * rewrite IHe. reflexivity.
      * destruct (interp_phoas_value p) eqn:V.
        ** rewrite IHe.
           rewrite (interp_phoas_value_success _ _ _ V).
           rewrite interp_expr_reify_id.
           reflexivity.
        ** cbn. f_equal. apply IHe.
    - destruct (phoas_constant_folding' e1) eqn:E1, (phoas_constant_folding' e2) eqn:E2;
        cbn; rewrite E1, E2; cbn; try destruct interp_phoas_value eqn:E; cbn; try reflexivity.
      2,3: rewrite interp_expr_reify_id;
        eapply interp_phoas_value_success in E;
        rewrite <- E, IHe1, IHe2; reflexivity.
      * rewrite IHe1, IHe2. reflexivity.
      * destruct (interp_phoas_value p0) eqn:P0; try reflexivity.
        eapply interp_phoas_value_success in P0.
        eapply interp_phoas_value_success in E.
        rewrite <- P0, <- E.
        rewrite interp_expr_reify_id.
        f_equal; easy.
    - cbn. rewrite <- IHe. 
      induction (interp_phoas_expr); try reflexivity.
      cbn. rewrite H. f_equal. apply IHi.
    - cbn. rewrite <- IHe1. rewrite <- IHe2.
      induction (interp_phoas_expr); try reflexivity.
      cbn. rewrite H. f_equal. rewrite IHi. reflexivity.
    - cbn. destruct (phoas_constant_folding' e1).
      * cbn. rewrite IHe1. reflexivity.
      * cbn. rewrite IHe1. destruct (interp_phoas_value) eqn:E.
        ** rewrite (interp_phoas_value_success _ a);
           try destruct a; easy.
        ** reflexivity.
    - cbn. rewrite <- IHe. rewrite <- H. reflexivity.
  Qed.


  Definition Phoas_constant_folding {t : type} (e : Phoas_expr t) : Phoas_expr t :=
    fun (V : type -> Type) =>
    match phoas_constant_folding' (e V) with
    | inl e => e
    | inr e => e
    end.

  Theorem Phoas_constant_folding_correct {t : type} (l : locals) (e : Phoas_expr t) :
    interp_phoas_expr l (e _) = interp_phoas_expr l (Phoas_constant_folding e _).
  Proof.
    unfold Phoas_constant_folding.
    apply phoas_constant_folding_correct.
  Qed.

End WithMap.





