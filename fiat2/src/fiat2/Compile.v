Require Import fiat2.Language.
Require Import fiat2.Interpret.
Require Import fiat2.Elaborate.
Require bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.MapEauto.
Require Import coqutil.Byte coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Word.Properties.

Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.

Definition compile_atom {t : type} (a : atom t) : result Syntax.expr :=
  match a with
  | AWord z => Success (Syntax.expr.literal z)
  | ABool b => Success (Syntax.expr.literal (Z.b2z b))
  | AInt _ | AString _ | ANil _ | AEmpty => error:("unimplemented")
  end.

Definition compile_unop {t1 t2 : type} (o : unop t1 t2) :
  result (Syntax.expr -> Syntax.expr) :=
  match o with
  | OWNeg =>
      Success (Syntax.expr.op Syntax.bopname.sub (Syntax.expr.literal 0))
  | ONot =>
      Success (Syntax.expr.op Syntax.bopname.sub (Syntax.expr.literal 1))
  | ONeg
  | OLength _
  | OLengthString
  | OFst _ _ _
  | OSnd _ _ _
  | OIntToString =>
      error:("unimplemented")
  end.

Definition compile_binop {t1 t2 t3 : type} (o : binop t1 t2 t3) :
  result (Syntax.expr -> Syntax.expr -> Syntax.expr) :=
  match o with
  | OWPlus =>
      Success (Syntax.expr.op Syntax.bopname.add)
  | OWMinus =>
      Success (Syntax.expr.op Syntax.bopname.sub)
  | OWTimes =>
      Success (Syntax.expr.op Syntax.bopname.mul)
  | OWDivU =>
      Success (Syntax.expr.op Syntax.bopname.divu)
  | OWDivS =>
      error:("unimplemented")
  | OWModU =>
      Success (Syntax.expr.op Syntax.bopname.remu)
  | OWModS =>
      error:("unimplemented")
  | OAnd =>
      Success (Syntax.expr.op Syntax.bopname.and)
  | OOr =>
      Success (Syntax.expr.op Syntax.bopname.or)
  | OConcat _
  | OConcatString =>
      error:("unimplemented")
  | OWLessU =>
      Success (Syntax.expr.op Syntax.bopname.ltu)
  | OWLessS =>
      Success (Syntax.expr.op Syntax.bopname.lts)
  | OEq _ H =>
      Success (Syntax.expr.op Syntax.bopname.eq)
  | OPlus
  | OMinus
  | OTimes
  | ODiv
  | OMod
  | OLess
  | ORepeat _
  | OPair _ _ _
  | OCons _
  | ORange
  | OWRange =>
      error:("unimplemented")
  end.

Fixpoint compile_expr {t : type} (e : expr t) : result Syntax.expr :=
  match e with
  | EVar _ x | ELoc _ x =>
      Success (Syntax.expr.var x)
  | EAtom a =>
      compile_atom a
  | EUnop o e1 =>
      f <- compile_unop o;;
      e1' <- compile_expr e1;;
      Success (f e1')
  | EBinop o e1 e2 =>
      f <- compile_binop o;;
      e1' <- compile_expr e1;;
      e2' <- compile_expr e2;;
      Success (f e1' e2')
  | _ => error:("unimplemented")
  end.

Section WithMap.
  Context {width : Z} {BW : Bitwidth width} {word : word.word width} {mem : map.map word byte}
          {word_ok : word.ok word} {mem_ok : map.ok mem}
          {tenv : map.map string (type * bool)} {tenv_ok : map.ok tenv}
          {locals : map.map string {t & interp_type (word := word) t}} {locals_ok : map.ok locals}
          {locals' : map.map string word} {locals'_ok : map.ok locals'}
          {ext_spec : ExtSpec}.

  (* Relation between source language and target language values,
   * denoting that two values are equivalent for a given type *)
  Inductive value_relation : forall {t : type}, interp_type t -> word -> Prop :=
    | RWord (w : word) : value_relation (t := TWord) w w
    | RBool (b : bool) : value_relation (t := TBool) b (word.of_Z (Z.b2z b)).

  Lemma RBool' (b : bool) (w : word) : w = word.of_Z (Z.b2z b) ->
    value_relation (t := TBool) b w.
  Proof.
    intros [= ->].
    apply RBool.
  Qed.

  (* Relation between source language and target language locals maps,
   * denoting that the source language locals are a "subset" of the target
   * language locals *)
  Definition locals_relation (lo : locals) (l : locals') : Prop :=
    map.forall_keys (fun x =>
    match map.get lo x with
    | Some (existT _ _ val) =>
        match map.get l x with
        | Some val' => value_relation val val'
        | None => False
        end
    | _ => True
    end) lo.

  Lemma locals_relation_extends (lo : locals) (l l' : locals') :
    map.extends l' l -> locals_relation lo l -> locals_relation lo l'.
  Proof.
    intros Hex.
    apply weaken_forall_keys.
    intros x Hl.
    destruct map.get as [s|]; try easy.
    destruct s as [t val].
    destruct (map.get l x) as [v|] eqn:E.
    - apply (Properties.map.extends_get (m1 := l) (m2 := l')) in E;
      [| assumption].
      now rewrite E.
    - destruct Hl.
  Qed.

  Lemma locals_relation_get (lo : locals) (l : locals') :
    locals_relation lo l ->
    forall (x : string) (t : type) (s : {t & interp_type t}),
    map.get lo x = Some s -> exists (w : word),
    map.get l x = Some w.
  Proof.
    intros Hl x t s Hs.
    unfold locals_relation, map.forall_keys in Hl.
    specialize Hl with (1 := Hs).
    rewrite Hs in Hl.
    destruct map.get.
    - fwd. now exists r.
    - destruct s, Hl.
  Qed.

  Lemma locals_relation_put (lo : locals) (l : locals') :
    locals_relation lo l ->
    forall (x : string) (t : type) (v : interp_type t) (w : word),
    value_relation v w ->
    locals_relation (set_local lo x v) (map.put l x w).
  Proof.
    intros Hl x t v w Hvw.
    unfold locals_relation, map.forall_keys, set_local.
    intros x' [t' v'].
    repeat rewrite Properties.map.get_put_dec.
    destruct (x =? x')%string.
    - easy.
    - intros Hx'. fwd.
      unfold locals_relation, map.forall_keys in Hl.
      specialize Hl with (1 := Hx').
      rewrite Hx' in Hl.
      assumption.
  Qed.

  Definition tenv_relation (G : tenv) (store env : locals) : Prop :=
    map.forall_keys (fun key =>
    match map.get G key with
    | Some (t, false) => match map.get env key with
                         | Some (existT _ t' _) => t = t'
                         | None => False
                         end
    | Some (t, true) => match map.get store key with
                        | Some (existT _ t' _) => t = t'
                        | None => False
                        end
    | None => True
    end) G.

  Lemma tenv_relation_get (G : tenv) (store env : locals) :
    tenv_relation G store env -> forall (x : string) (t : type) (b : bool),
    map.get G x = Some (t, b) -> exists (v : interp_type t),
    map.get (if b then store else env) x = Some (existT _ t v).
  Proof.
    intros Hlo x t b Htb.
    unfold tenv_relation, map.forall_keys in Hlo.
    specialize Hlo with (1 := Htb).
    rewrite Htb in Hlo.
    destruct b.
    all: destruct map.get;
    [ destruct s; subst; now exists i
    | destruct Hlo ].
  Qed.

  Lemma tenv_relation_put (G : tenv) (store env : locals) :
    tenv_relation G store env ->
    forall (x : string) (t : type) (b : bool) (v : interp_type t),
    if b then
    tenv_relation (map.put G x (t, b)) (set_local store x v) env
    else
    tenv_relation (map.put G x (t, b)) store (set_local env x v).
  Proof.
    intros Hlo x t b v.
    unfold tenv_relation, map.forall_keys, set_local.
    destruct b.
    all:
    intros x' [t' b'];
    repeat rewrite Properties.map.get_put_dec;
    destruct (x =? x')%string;
    [ easy
    | intros Hx'; fwd;
      unfold tenv_relation, map.forall_keys in Hlo;
      specialize Hlo with (1 := Hx');
      rewrite Hx' in Hlo;
      assumption ].
  Qed.

  Lemma proj_expected_existT (t : type) (v : interp_type t) :
    v = proj_expected t (existT interp_type t v).
  Proof.
    unfold proj_expected.
    simpl.
    case type_eq_dec eqn:E; [| easy].
    unfold cast.
    rewrite (Eqdep_dec.UIP_dec type_eq_dec e eq_refl).
    trivial.
  Qed.

  Lemma interp_type_eq : forall {t : type} (e : expr t) (w : interp_type t) (store env : locals),
    (existT interp_type t w =
    existT interp_type t (interp_expr store env e)) ->
    (interp_expr store env e) = w.
  Proof.
    intros.
    inversion_sigma.
    rewrite <- Eqdep_dec.eq_rect_eq_dec in H0.
    * easy.
    * exact type_eq_dec.
  Qed.

  Lemma eval_map_extends_locals : forall e (m : mem) (l l' : locals') w,
    map.extends l' l ->
    eval_expr m l e = Some w ->
    eval_expr m l' e = Some w.
  Proof.
    induction e; intros m l l' w H Hl.
    - (* Syntax.expr.literal *)
      exact Hl.
    - (* Syntax.expr.var *)
      simpl in Hl. simpl. unfold map.extends in H.
      now apply H.
    - (* Syntax.expr.inlinetable *)
      simpl in Hl. simpl.
      specialize IHe with (m := m) (1 := H).
      destruct (eval_expr m l e); try easy.
      specialize IHe with (w := r) (1 := eq_refl).
      now rewrite IHe.
    - (* Syntax.expr.load *)
      simpl in Hl. simpl.
      specialize IHe with (m := m) (1 := H).
      destruct (eval_expr m l e); try easy.
      specialize IHe with (w := r) (1 := eq_refl).
      now rewrite IHe.
    - (* Syntax.expr.op *)
      simpl in Hl. simpl.
      destruct (eval_expr m l e1) as [r1 |] eqn:H1; try easy.
      destruct (eval_expr m l e2) as [r2 |] eqn:H2; try easy.
      specialize IHe1 with (m := m) (w := r1) (1 := H) (2 := H1).
      specialize IHe2 with (m := m) (w := r2) (1 := H) (2 := H2).
      now rewrite IHe1, IHe2.
    - (* Syntax.expr.ite *)
      simpl in Hl. simpl.
      destruct (eval_expr m l e1) as [r1 |] eqn:H1; try easy.
      specialize IHe1 with (m := m) (w := r1) (1 := H) (2 := H1).
      rewrite IHe1.
      destruct word.eqb.
      + destruct (eval_expr m l e3) as [r3 |] eqn:H3; try easy.
        apply IHe3 with (l' := l') in H3; try assumption.
        now rewrite H3.
      + destruct (eval_expr m l e2) as [r2 |] eqn:H2; try easy.
        apply IHe2 with (l' := l') in H2; try assumption.
        now rewrite H2.
  Qed.

  Lemma compile_correct :
    forall {t} (e : expr t) (e' : Syntax.expr) (G : tenv),
    wf G e ->
    compile_expr e = Success e' -> forall store env l,
    tenv_relation G store env ->
    locals_relation store l -> locals_relation env l ->
    exists w : word, forall m,
    eval_expr m l e' = Some w /\
    value_relation (interp_expr store env e) w.
  Proof.
    intros t. induction e; intros e' G He He' store env l HG Hstore Henv; try easy.
    - (* EVar x *)
      unfold compile_expr in He'.
      fwd.
      simpl.
      inversion_clear He.
      edestruct tenv_relation_get as [v Hv].
      { exact HG. }
      { exact H. }
      simpl in Hv.
      edestruct locals_relation_get as [w Hw].
      { exact Henv. }
      { exact t. }
      { exact Hv. }
      exists w.
      intros _; split.
      { assumption. }
      unfold get_local.
      rewrite Hv.
      unfold locals_relation, map.forall_keys in Henv.
      specialize Henv with (1 := Hv).
      rewrite Hv, Hw in Henv.
      now rewrite <- proj_expected_existT.
    - (* ELoc x *)
      unfold compile_expr in He'.
      fwd.
      simpl.
      inversion_clear He.
      edestruct tenv_relation_get as [v Hv].
      { exact HG. }
      { exact H. }
      simpl in Hv.
      edestruct locals_relation_get as [w Hw].
      { exact Hstore. }
      { exact t. }
      { exact Hv. }
      exists w.
      intros _; split.
      { assumption. }
      unfold get_local.
      rewrite Hv.
      unfold locals_relation, map.forall_keys in Hstore.
      specialize Hstore with (1 := Hv).
      rewrite Hv, Hw in Hstore.
      now rewrite <- proj_expected_existT.
    - (* EAtom a *)
      unfold compile_expr in He'.
      fwd.
      simpl.
      destruct a; try easy.
      + (* AWord n *)
        simpl.
        simpl in He'.
        fwd.
        exists (word.of_Z (word.wrap n)).
        intros m; split;
        rewrite <- word.unsigned_of_Z, word.of_Z_unsigned; try easy.
        apply RWord.
      + (* ABool b *)
        simpl.
        simpl in He'.
        fwd.
        exists (word.of_Z (Z.b2z b)).
        intros m; split; try easy.
        apply RBool.
    - (* EUnop o e *)
      destruct o; try easy.
      all:
        simpl;
        simpl in He';
        fwd; rename a into e', E into He';
        inversion He;
        apply Eqdep_dec.inj_pair2_eq_dec in H3, H4 as [= ->]; try exact type_eq_dec;
        apply Eqdep_dec.inj_pair2_eq_dec in H3 as [= ->]; try exact type_eq_dec;
        subst;
        specialize IHe with (1 := H2) (2 := eq_refl) (3 := HG) (4 := Hstore) (5 := Henv);
        fwd;
        eexists;
        intros m; specialize IHe with m; fwd;
        simpl;
        rewrite IHep0;
        split;
        [ reflexivity |];
        inversion IHep1;
        subst;
        repeat (repeat lazymatch goal with
        | h: existT _ _ _ = existT _ _ _ |- _ =>
            apply interp_type_eq in h
        end;
        subst).
      + (* OWNeg *)
        rewrite Properties.word.sub_0_l.
        apply RWord.
      + (* ONot *)
        rewrite <- Properties.word.ring_morph_sub.
        destruct (interp_expr _ _ e); apply RBool.
    - (* EBinop o e1 e2 *)
      destruct o; try easy.
      all:
        simpl;
        simpl in He';
        fwd; rename a into e1', E into He1', a0 into e2', E0 into He2';
        inversion He;
        repeat (repeat lazymatch goal with
        | h: existT _ _ _ = existT _ _ _ |- _ =>
            apply interp_type_eq in h
        end;
        subst);
        apply Eqdep_dec.inj_pair2_eq_dec in H5, H6 as [= ->]; try exact type_eq_dec;
        subst;
        specialize IHe1 with (1 := H3) (2 := eq_refl) (3 := HG) (4 := Hstore) (5 := Henv);
        specialize IHe2 with (1 := H7) (2 := eq_refl) (3 := HG) (4 := Hstore) (5 := Henv);
        fwd;
        eexists;
        intros m; specialize IHe1 with m; specialize IHe2 with m; fwd;
        simpl;
        rewrite IHe1p0, IHe2p0;
        split;
        [ reflexivity |].
      1-9:
        (* all except OEq *)
        inversion IHe1p1; inversion IHe2p1;
        subst;
        repeat (repeat lazymatch goal with
        | h: existT _ _ _ = existT _ _ _ |- _ =>
            apply interp_type_eq in h
        end;
        subst);
        set (v1 := interp_expr _ _ e1);
        set (v2 := interp_expr _ _ e2).
      1-5:
        (* OWPlus, OWMinus, OWTimes, OWDivU, OWModU *)
        apply RWord.
      1-2:
        (* OAnd, OOr *)
        destruct v1, v2;
          simpl;
          apply RBool';
          apply word.unsigned_inj;
          simpl Z.b2z;
          try rewrite word.unsigned_and_nowrap;
          try rewrite word.unsigned_or_nowrap;
          now try rewrite word.unsigned_of_Z_0;
          try rewrite word.unsigned_of_Z_1.
      + (* OWLessU *)
        destruct (word.ltu v1 v2);
        apply RBool.
      + (* OWLessS *)
        destruct (word.lts v1 v2);
        apply RBool.
      + (* OEq *)
        destruct t; try easy; unfold eqb_values.
        * (* TWord *)
          inversion IHe1p1; inversion IHe2p1.
          subst;
          repeat (repeat lazymatch goal with
          | h: existT _ _ _ = existT _ _ _ |- _ =>
              apply interp_type_eq in h
          end;
          subst).
          destruct word.eqb;
          apply RBool.
        * (* TBool *)
          inversion IHe1p1; inversion IHe2p1.
          subst;
          repeat (repeat lazymatch goal with
          | h: existT _ _ _ = existT _ _ _ |- _ =>
              apply interp_type_eq in h
          end;
          subst).
          destruct (interp_expr _ _ e1) eqn:E1, (interp_expr _ _ e2) eqn:E2.
          all:
            apply RBool';
            simpl;
            rewrite word.unsigned_eqb;
            try rewrite word.unsigned_of_Z_0;
            now try rewrite word.unsigned_of_Z_1.
  Qed.

End WithMap.

Compute (compile_expr (EAtom (AWord 4))).
Compute (compile_expr (EAtom (ABool true))).
Compute (compile_expr (EAtom (ABool false))).
Compute (compile_expr (EBinop OOr (EAtom (ABool true)) (EAtom (ABool false)))).
Compute (compile_expr (EBinop OWPlus (EAtom (AWord 1)) (EAtom (AWord 1)))).
