Require Import PyLevelLang.Language.
Require Import PyLevelLang.Phoas_Language.
Require Import PyLevelLang.Interpret.
Require Import PyLevelLang.Elaborate.
Require Import coqutil.Tactics.forward.
Require Import coqutil.Tactics.Tactics.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Section PhoasExprEquiv.
  Context {V V' : type -> Type}.

  Definition ctxt := list { t : type & (V t * V' t)%type }.
  Definition vars := existT (fun t => (V t * V' t)%type).

  Inductive phoas_expr_equiv : ctxt -> forall {t : type},
        phoas_expr V t -> phoas_expr V' t -> Prop :=
  | eq_PhEVar C t (v : V t) (v' : V' t) :
    In (vars _ (v, v')) C -> phoas_expr_equiv C (PhEVar _ v) (PhEVar _ v')
  | eq_PhELoc C t (x x' : string) :
    x = x' -> phoas_expr_equiv C (PhELoc t x) (PhELoc t x')
  | eq_PhEAtom C {t} (a a' : atom t) :
    a = a' -> phoas_expr_equiv C (PhEAtom a) (PhEAtom a')
  | eq_PhEUnop C {t1 t2} (o : unop t1 t2) e e' :
    phoas_expr_equiv C e e' ->
    phoas_expr_equiv C (PhEUnop o e) (PhEUnop o e')
  | eq_PhEBinop C {t1 t2 t3} (o : binop t1 t2 t3) e1 e1' e2 e2' :
    phoas_expr_equiv C e1 e1' ->
    phoas_expr_equiv C e2 e2' ->
    phoas_expr_equiv C (PhEBinop o e1 e2) (PhEBinop o e1' e2')
  | eq_PhEFlatmap C {t1 t2} l1 l1' (x x' : string) (fn_l2 : V t1 -> phoas_expr V (TList t2)) fn_l2':
    phoas_expr_equiv C l1 l1' ->
    (forall v v', phoas_expr_equiv (vars _ (v, v') :: C) (fn_l2 v) (fn_l2' v')) ->
    phoas_expr_equiv C (PhEFlatmap l1 x fn_l2) (PhEFlatmap l1' x' fn_l2')
  | eq_PhEFold C {t1 t2} l1 l1' e2 e2' (x x' y y' : string) (fn_e3 : V t1 -> V t2 -> phoas_expr V t2) fn_e3' :
    phoas_expr_equiv C l1 l1' ->
    phoas_expr_equiv C e2 e2' ->
    (forall v1 v2 v1' v2', phoas_expr_equiv (vars _ (v2, v2') :: vars _ (v1, v1') :: C) (fn_e3 v1 v2) (fn_e3' v1' v2')) ->
    phoas_expr_equiv C (PhEFold l1 e2 x y fn_e3) (PhEFold l1' e2' x' y' fn_e3')
  | eq_PhEIf C {t} e1 e1' (e2 : phoas_expr V t) e2' e3 e3' :
    phoas_expr_equiv C e1 e1' ->
    phoas_expr_equiv C e2 e2' ->
    phoas_expr_equiv C e3 e3' ->
    phoas_expr_equiv C (PhEIf e1 e2 e3) (PhEIf e1' e2' e3')
  | eq_PhELet C {t1 t2} (x x' : string) e1 e1' (fn_e2 : V t1 -> phoas_expr V t2) fn_e2' :
    phoas_expr_equiv C e1 e1' ->
    (forall v v', phoas_expr_equiv (vars _ (v, v') :: C) (fn_e2 v) (fn_e2' v')) ->
    phoas_expr_equiv C (PhELet x e1 fn_e2) (PhELet x' e1' fn_e2').
End PhoasExprEquiv.

Definition projT1_fst_T2 {A : Type} {P1 P2 : A -> Type} (v : {t : A & (P1 t * P2 t)%type}) :
  {t : A & P1 t} :=
  existT _ (projT1 v) (fst (projT2 v)).

Definition projT1_snd_T2 {A : Type} {P1 P2 : A -> Type} (v : {t : A & (P1 t * P2 t)%type}) :
  {t : A & P2 t} :=
  existT _ (projT1 v) (snd (projT2 v)).

Section WithMap.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {phoas_env : forall V, map.map string {t : type & V t}} {phoas_env_ok : forall V, map.ok (phoas_env V)}.

  Fixpoint interp_phoas_expr {t : type} (store : phoas_env interp_type) (e : phoas_expr interp_type t) : interp_type t :=
    match e with
    | PhEVar _ v => v
    | PhELoc _ x => get_local store x
    | PhEAtom a => interp_atom a
    | PhEUnop o e1 => interp_unop o (interp_phoas_expr store e1)
    | PhEBinop o e1 e2 => interp_binop o (interp_phoas_expr store e1) (interp_phoas_expr store e2)
    | PhEFlatmap l1 _ fn_l2 => flat_map (fun y => interp_phoas_expr store (fn_l2 y)) (interp_phoas_expr store l1)
    | PhEFold l1 e2 _ _ fn_e3 => let l1' := interp_phoas_expr store l1 in
                                 let a' := interp_phoas_expr store e2 in
                                 let fn' := fun v acc => interp_phoas_expr store (fn_e3 v acc) in
                                 fold_right fn' a' l1'
    | PhEIf e1 e2 e3 => if interp_phoas_expr store e1 then interp_phoas_expr store e2 else interp_phoas_expr store e3
    | PhELet _ e1 fn_e2 => interp_phoas_expr store (fn_e2 (interp_phoas_expr store e1))
    end.

  Definition interp_Phoas_expr (store : phoas_env interp_type) {t : type} (e : Phoas_expr t) :=
    interp_phoas_expr store (e _).

  Section WithPhoasV.
    Context {V : type -> Type}.

    (* Default value of type (phoas_expr V t) *)
    Fixpoint default_phoas_expr (t : type) : phoas_expr V t :=
      match t return phoas_expr V t with
      | TWord => PhEAtom (AWord 0)(* default_val TWord returns a word, but we need a Z here *)
      | TInt => PhEAtom (AInt (default_val TInt))
      | TBool => PhEAtom (ABool (default_val TBool))
      | TString => PhEAtom (AString (default_val TString))
      | TPair s t1 t2 => PhEBinop (OPair _ _ _) (default_phoas_expr t1) (default_phoas_expr t2)
      | TEmpty => PhEAtom AEmpty
      | TList t1 => PhEAtom (ANil t1)
      end.

    (* Phoas map lookup, returning a default if nothing is found, for type correctness *)
    Definition phoas_proj_expected (t_expected : type) (v : {t_actual & V t_actual}) :
      phoas_expr V t_expected :=
      (* Return (phoas_expr t_expected) rather than (V t_expected)
     to avoid declaring "forall t, V t is inhabited" *)
      match type_eq_dec (projT1 v) t_expected with
      | left H => PhEVar _ (cast H _ (projT2 v))
      | _ => default_phoas_expr t_expected
      end.

    Definition set_phoas_local (env : phoas_env V) (x : string) {t : type} (v : V t) :=
      map.put env x (existT _ _ v).

    Fixpoint phoasify (env : phoas_env V) {t : type} (e : expr t) : phoas_expr V t :=
      match e with
      | EVar _ x => match map.get env x with
                    | Some v => phoas_proj_expected _ v
                    | None => default_phoas_expr _
                    end
      (* PHOAS does not handle mutable variables, so we leave them in the source langugage representation *)
      | ELoc _ x =>  PhELoc _ x
      | EAtom a => PhEAtom a
      | EUnop o e1 => PhEUnop o (phoasify env e1)
      | EBinop o e1 e2 => PhEBinop o (phoasify env e1) (phoasify env e2)
      | EFlatmap l1 x fn => PhEFlatmap (phoasify env l1) x (fun v => phoasify (set_phoas_local env x v) fn)
      | EIf e1 e2 e3 => PhEIf (phoasify env e1) (phoasify env e2) (phoasify env e3)
      | EFold l1 a x y fn => PhEFold (phoasify env l1) (phoasify env a) x y
                               (fun v acc => phoasify (set_phoas_local (set_phoas_local env x v) y acc) fn)
      | ELet x e1 e2 => PhELet x (phoasify env e1) (fun v => phoasify (set_phoas_local env x v) e2)
      end.
  End WithPhoasV.

  Definition Phoasify {t : type} (e : expr t) : Phoas_expr t:=
    fun (V : type -> Type) => phoasify (V := V) map.empty e.
End WithMap.

Definition Phoas_wf {t : type} (e : Phoas_expr t) :=
  forall V1 V2, phoas_expr_equiv nil (e V1) (e V2).

(* Remove one occurrence of x from store if there is one.
 * Auxiliary function for the definition of fresh' below *)
Fixpoint remove_one (x : string) (l : list string) : list string :=
  match l with
  | nil => nil
  | h :: t => if eqb h x then t else h :: remove_one x t
  end.

Lemma in_remove_one_len : forall (x : string) (l : list string),
    In x l -> List.length l = S (List.length (remove_one x l)).
Proof.
  intros. induction l.
  - apply in_nil in H. exfalso. apply H.
  - simpl in H. destruct (eqb a x) eqn:E.
    + simpl. rewrite E. reflexivity.
    + destruct H as [HL | HR].
      * rewrite <- eqb_eq in HL. rewrite HL in E. discriminate.
      * simpl. rewrite E. simpl. rewrite (IHl HR). reflexivity.
Qed.

Lemma in_remove_one : forall (x : string) (l : list string),
    In x l -> forall (y : string), x = y \/ In x (remove_one y l).
Proof.
  intros x l H. induction l.
  - intros. apply in_nil in H. exfalso. exact H.
  - intros y. simpl in H. destruct H as [HL | HR].
    + destruct (eqb a y) eqn:E.
      * rewrite eqb_eq in E. rewrite HL in E. left. exact E.
      * right. simpl. rewrite E. simpl. left. exact HL.
    + destruct (IHl HR) with (y := y) as [HL' | HR'].
      * left. exact HL'.
      * right. simpl. destruct (eqb a y) eqn:E.
        { exact HR. }
        { simpl. right. exact HR'. }
Qed.

(* Append "'"s to x until the resulting name is not in used.
 * The initial call should have (budget = length used) *)
Fixpoint fresh' (budget : nat) (used : list string) (x : string) : string :=
  (* We need budget as a decreasing argument for the function *)
  match budget with
  | O => x
  | S n => match in_dec string_dec x used with
           | left _ => fresh' n (remove_one x used) (x ++ "'")
           | right _ => x
           end
  end.

(* Given a list of used names and a hint, return a fresh name *)
Definition fresh (used : list string) (x : string) : string :=
  fresh' (List.length used) used x.

Lemma len_app : forall y, length y < length (y ++ "'").
Proof.
  induction y; auto. simpl. apply Arith_prebase.lt_n_S_stt. apply IHy.
Qed.

Lemma fresh'_len : forall (budget : nat) (used : list string) (x : string),
    length x <= length (fresh' budget used x).
Proof.
  induction budget; intros.
  - destruct used; unfold fresh'; constructor.
  - destruct (in_dec string_dec x used) eqn:E.
    + unfold fresh'. rewrite E.
      apply Nat.le_trans with (m := length (x ++ "'")).
      * pose proof (len_app x) as len_app_x.
        apply Nat.lt_le_incl. exact len_app_x.
      * apply (IHbudget (remove_one x used) (x ++ "'")%string).
    + unfold fresh'; rewrite E; constructor.
Qed.

Lemma fresh'_is_fresh : forall (budget : nat) (used : list string) (x : string),
    budget = List.length used -> ~ In (fresh' budget used x) used.
Proof.
  induction budget; intros.
  - destruct used.
    + auto.
    + discriminate.
  - rewrite H. destruct (in_dec string_dec x used) as [ HL | HR ] eqn:E.
    + assert (Hrm_len: S budget = S (List.length (remove_one x used))).
      { rewrite H. apply in_remove_one_len. apply HL. }
      injection Hrm_len as Hrm_len.
      apply (IHbudget (remove_one x used)) with (x := (x ++ "'")%string) in Hrm_len as Hrm.
      unfold not. intros. apply in_remove_one with (y := x) in H0 as [HL'|HR'].
      * assert (HA : length (x ++ "'") <= length (fresh' (Datatypes.length used) used x)).
        { unfold fresh'. rewrite <- H. rewrite E. apply fresh'_len. }
        rewrite HL' in HA. apply Arith_prebase.le_not_lt_stt in HA.
        apply HA. apply len_app.
      * unfold fresh' in HR'. rewrite <- H in HR'. rewrite E in HR'.
        apply Hrm. unfold fresh'. apply HR'.
    + unfold fresh'. rewrite <- H. rewrite E. exact HR.
Qed.

Corollary fresh_is_fresh : forall (used : list string) (x : string), ~ In (fresh used x) used.
Proof.
  intros. unfold fresh. apply fresh'_is_fresh. reflexivity.
Qed.

Definition const_string : type -> Type := fun _ => string.

Fixpoint dephoasify (used : list string) {t : type} (e : phoas_expr const_string t) : expr t :=
  match e with
  | PhEVar _ v => EVar _ v
  | PhELoc _ x => ELoc _ x
  | PhEAtom a => EAtom a
  | PhEUnop o e1 => EUnop o (dephoasify used e1)
  | PhEBinop o e1 e2 => EBinop o (dephoasify used e1) (dephoasify used e2)
  | PhEFlatmap l1 x fn =>
      let x' := fresh used x in
      let used' := x' :: used in
      EFlatmap (dephoasify used l1) x' (dephoasify used' (fn x'))
  | PhEIf e1 e2 e3 => EIf (dephoasify used e1) (dephoasify used e2) (dephoasify used e3)
  | PhEFold l1 a x y fn =>
      let x' := fresh used x in
      let y' := fresh (x' :: used) y in
      let used' := y' :: x' :: used in
      EFold (dephoasify used l1) (dephoasify used a) x' y' (dephoasify used' (fn x' y'))
  | PhELet x e1 fn =>
      let x' := fresh used x in
      let used' := x' :: used in
      ELet x' (dephoasify used e1) (dephoasify used' (fn x'))
  end.

Definition Dephoasify (used : list string) {t : type} (e : Phoas_expr t) : expr t :=
  dephoasify used (e const_string).

Lemma eq_dec_refl : forall  {t : Type} (eq_dec : forall (v1 v2 : t), {v1 = v2} + {v1 <> v2}),
  forall (x : t), eq_dec x x = left eq_refl.
Proof.
  intros t eq_dec x. destruct (eq_dec x x).
  - f_equal. apply Eqdep_dec.UIP_dec. apply eq_dec.
  - exfalso. apply n. reflexivity.
Qed.

Ltac eq_projT2_eq := match goal with
                     | H : existT ?f ?t _ = existT ?f ?t _ |- _ =>
                         apply Eqdep_dec.inj_pair2_eq_dec in H;[ subst; eauto | apply type_eq_dec]
                     end.

(*??? move to util?*)
Lemma fold_right_eq_ext : forall (A B : Type) (f g : B -> A -> A) (a a' : A) (l l' : list B),
    a = a' -> l = l' ->
    (forall x y, f x y = g x y) ->
    fold_right f a l = fold_right g a' l'.
Proof.
  induction l as [|h t IHt]; intros l' Ha Hl H; subst.
  - reflexivity.
  - simpl. rewrite (IHt t); congruence.
Qed.

Lemma flat_map_eq_ext : forall (A B : Type) (f g : A -> list B) (l l' : list A),
    l = l' ->
    (forall x, f x = g x) ->
    flat_map f l = flat_map g l'.
Proof.
  induction l as [|h t IHt]; intros l' Hl H; subst.
  - reflexivity.
  - simpl. rewrite (IHt t); congruence.
Qed.

Section WithMap.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {phoas_env : forall V, map.map string {t : type & V t}} {phoas_env_ok : forall V, map.ok (phoas_env V)}.

  Lemma default_val_eq : forall store t,
      interp_phoas_expr store (default_phoas_expr t) = default_val t.
  Proof.
    induction t; try reflexivity.
    (* TPair *)
    cbn. congruence.
  Qed.

  Lemma proj_expected_eq : forall store t v,
      interp_phoas_expr store (phoas_proj_expected t v) = proj_expected t v.
  Proof.
    intros store t v.
    unfold phoas_proj_expected. unfold proj_expected.
    destruct (type_eq_dec (projT1 v) t).
    - reflexivity.
    - apply default_val_eq.
  Qed.

  Ltac phoas_expr_induct e :=
    induction e; intros; simpl;
    try reflexivity;
    try (apply flat_map_eq_ext);
    try (apply fold_right_eq_ext);
    try (repeat destruct_one_match);
    try congruence.

  Lemma phoasify_sound' :
    forall {t : type} (e : expr t) (store env : phoas_env interp_type),
      interp_expr store env e = interp_phoas_expr store (phoasify env e).
  Proof.
    phoas_expr_induct e.
    1, 2: unfold get_local; rewrite E; symmetry.
    - apply proj_expected_eq.
    - apply default_val_eq.
    - intro; rewrite IHe2; reflexivity.
    - intros; rewrite IHe3; reflexivity.
    - rewrite IHe1, IHe2; reflexivity.
  Qed.

  Theorem phoasify_sound : forall (store : phoas_env interp_type) {t : type} (e : expr t),
      interp_expr store map.empty e = interp_Phoas_expr store (Phoasify e).
  Proof.
    intros store t e. unfold Phoasify. unfold interp_Phoas_expr.
    apply phoasify_sound'.
  Qed.

  Definition phoasify_form_consistent {V V'} (C : @ctxt V V')
    (env : phoas_env V) (env' : phoas_env V') :=
    forall x, match map.get env x with
              | Some v => match map.get env' x with
                          | Some v' => exists p,
                              In p C /\
                                projT1_fst_T2 p = v /\
                                projT1_snd_T2 p = v'
                          | None => False
                          end
              | None => map.get env' x = None
              end.

  Lemma phoasify_form_consistent_step : forall V V' (C : @ctxt V V') env env',
      phoasify_form_consistent C env env' ->
      forall y t (u : V t) (u' : V' t),
        phoasify_form_consistent (vars _ (u, u') :: C) (set_phoas_local env y u) (set_phoas_local env' y u').
  Proof.
    unfold phoasify_form_consistent.
    intros V V' C env env' H y t u u' x.
    unfold set_phoas_local. destruct (eqb x y) eqn:E.
    - rewrite eqb_eq in E. rewrite E.
      repeat rewrite map.get_put_same.
      exists (vars t (u, u')). split.
      + left; reflexivity.
      + split; reflexivity.
    - rewrite eqb_neq in E. repeat rewrite map.get_put_diff; try assumption.
      pose proof (H x) as H. destruct (map.get env x).
      + destruct (map.get env' x); [| exfalso; assumption].
        destruct H as [p [H1 H2]].
        exists p. split; [right |]; assumption.
      + assumption.
  Qed.

  Lemma phoas_equiv_default : forall V V' (C : @ctxt V V') (t : type),
      phoas_expr_equiv C (default_phoas_expr t) (default_phoas_expr t).
  Proof.
    induction t; constructor; try reflexivity.
    (* TPair *)
    - apply IHt1.
    - apply IHt2.
  Qed.

  Lemma phoasify_wf' : forall V V' (C : @ctxt V V') (env : phoas_env V) (env' : phoas_env V'),
      phoasify_form_consistent C env env' ->
      forall t (e : expr t) ,
        phoas_expr_equiv C (phoasify env e) (phoasify env' e).
  Proof.
    intros V V' C env env' H_consistent t e.
    generalize dependent env'; generalize dependent env; generalize dependent C.
    induction e; intros C env env' H_consistent.
    - simpl. pose proof (H_consistent x) as H.
      destruct (map.get env x).
      + destruct (map.get env' x); try (exfalso; assumption).
        * unfold phoas_proj_expected. destruct s; destruct s0; simpl.
          destruct H as [[t' [l r]] [H1 [H2 H3]]].
          unfold projT1_fst_T2 in H2; unfold projT1_snd_T2 in H3; simpl in *.
          apply projT1_eq in H2 as H2'. apply projT1_eq in H3 as H3'.
          simpl in H2', H3'. subst. repeat eq_projT2_eq.
          destruct (type_eq_dec x1 t).
          -- constructor. subst. assumption.
          -- apply phoas_equiv_default.
      + rewrite H. apply phoas_equiv_default.
    - constructor; reflexivity.
    - constructor; reflexivity.
    - constructor; apply IHe, H_consistent.
    - constructor; [apply IHe1 | apply IHe2]; apply H_consistent.
    - constructor.
      + apply IHe1, H_consistent.
      + intros v v'. apply IHe2.
        apply phoasify_form_consistent_step, H_consistent.
    - constructor.
      + apply IHe1, H_consistent.
      + apply IHe2, H_consistent.
      + intros v1 v2 v1' v2'. apply IHe3.
        repeat apply phoasify_form_consistent_step. apply H_consistent.
    - constructor; [apply IHe1 | apply IHe2 | apply IHe3]; apply H_consistent.
    - constructor.
      + apply IHe1, H_consistent.
      + intros v v'. apply IHe2.
        apply phoasify_form_consistent_step, H_consistent.
  Qed.

  Theorem phoasify_wf : forall t (e : expr t),
      Phoas_wf (Phoasify e).
  Proof.
    unfold Phoas_wf. unfold Phoasify. intros t e V V'.
    apply phoasify_wf'. unfold phoasify_form_consistent.
    intro x. repeat rewrite map.get_empty. reflexivity.
  Qed.


  Definition dephoasify_envs_consistent (C : ctxt) (used : list string) (env : phoas_env interp_type) :=
    forall (p : {t : type & (string * interp_type t)%type}),
      In p C ->
      let s := fst (projT2 p) in
      In s used /\ map.get env s = Some (projT1_snd_T2 p).

  Lemma dephoasify_envs_consistent_step : forall C used env,
      dephoasify_envs_consistent C used env ->
      forall x t (v : interp_type t),
        dephoasify_envs_consistent (vars _ (fresh used x, v) :: C) (fresh used x :: used) (set_local env (fresh used x) v).
  Proof.
    unfold dephoasify_envs_consistent. intros C used env H x t v p [HL | HR].
    - rewrite <- HL. split.
      + left; reflexivity.
      + simpl. unfold set_local. rewrite map.get_put_same. reflexivity.
    - apply H in HR as [HRL HRR]. split.
      + right; apply HRL.
      + unfold set_local. destruct (eqb (fst (projT2 p)) (fresh used x)) eqn:E.
        * rewrite eqb_eq in E. rewrite E in HRL. apply fresh_is_fresh in HRL.
          exfalso; assumption.
        * rewrite eqb_neq in E. rewrite map.get_put_diff; assumption.
  Qed.

  Lemma dephoasify_sound' :
    forall (t : type) (e : phoas_expr const_string t) (e0 : phoas_expr interp_type t) (C : ctxt),
      phoas_expr_equiv C e e0 ->
      forall (used : list string) (env : phoas_env interp_type),
        dephoasify_envs_consistent C used env ->
        forall (store : phoas_env interp_type),
          interp_phoas_expr store e0 = interp_expr store env (dephoasify used e).
  Proof.
    intros t e e0 C H_equiv. induction H_equiv; intros used env H_consistent store; simpl.
    - unfold dephoasify_envs_consistent in H_consistent.
      apply H_consistent in H. destruct H as [_ HR].
      simpl in HR. unfold get_local. destruct (map.get env v).
      + unfold projT1_snd_T2 in HR. simpl in HR.
        unfold proj_expected. injection HR as HR. rewrite HR.
        simpl. rewrite eq_dec_refl. reflexivity.
      + discriminate.
    - rewrite H; reflexivity.
    - rewrite H; reflexivity.
    - f_equal. apply IHH_equiv, H_consistent.
    - f_equal.
      + apply IHH_equiv1, H_consistent.
      + apply IHH_equiv2, H_consistent.
    - rewrite (IHH_equiv _ _ H_consistent). apply flat_map_eq_ext; try congruence.
      remember (fresh used x) as y.
      intros v'. rewrite H0 with (v := y) (used := y :: used) (env := set_local env y v').
      + reflexivity.
      + rewrite Heqy. apply dephoasify_envs_consistent_step, H_consistent.
    - rewrite (IHH_equiv1 _ _ H_consistent), (IHH_equiv2 _ _ H_consistent).
      apply fold_right_eq_ext; try congruence. intros v1 v2. apply H0.
      repeat apply dephoasify_envs_consistent_step. apply H_consistent.
    - rewrite (IHH_equiv1 _ _ H_consistent), (IHH_equiv2 _ _ H_consistent), (IHH_equiv3 _ _ H_consistent). reflexivity.
    - rewrite (IHH_equiv _ _ H_consistent). remember (fresh used x) as y.
      remember (interp_expr store env (dephoasify used e1)) as v.
      rewrite H0 with (v := y) (used := y :: used) (env := set_local env y v);
        [reflexivity |].
      rewrite Heqy. apply dephoasify_envs_consistent_step, H_consistent.
  Qed.

  Theorem dephoasify_sound : forall {t : type} (e : Phoas_expr t),
      Phoas_wf e ->
      forall (store : phoas_env interp_type) (used : list string),
        interp_Phoas_expr store e = interp_expr store map.empty (Dephoasify used e).
  Proof.
    intros t e H_wf store used.
    apply dephoasify_sound' with (C := nil) (env := map.empty).
    - apply H_wf.
    - unfold dephoasify_envs_consistent. intros p contra.
      apply in_nil in contra. exfalso; assumption.
  Qed.

  (* An example pipeline converting a source expression to its PHOAS form, performs a transformation, and converts it back to a source expression.
We proves that the pipeline in the example is sound using the soundness theorems above. *)

  (* Auxiliary function to destruct e1 and e2 under the match of o
 so that we expose the dependency of the types of e1 and e2 on the type of o.
 "Convoy pattern". *)
  Definition fold_add1 {V t1 t2 t3} (o : binop t1 t2 t3) :
    phoas_expr V t1 -> phoas_expr V t2 -> phoas_expr V t3 :=
    match o with
    | OPlus => fun e1 e2 => match e1, e2 with
                            | PhEAtom (AInt a1), PhEAtom (AInt a2) => PhEAtom (AInt (Z.add a1 a2))
                            | e1, e2 => PhEBinop OPlus e1 e2
                            end
    (* Use "o" rather than a wildcard in the pattern to make Coq break it down
     into specific cases with the respective types *)
    | o => fun e1 e2 => PhEBinop o e1 e2
    end.

  Fixpoint fold_add' {V t} (e : phoas_expr V t) : phoas_expr V t :=
    match e with
    | PhEVar t v => PhEVar t v
    | PhELoc t x => PhELoc t x
    | PhEAtom a => PhEAtom a
    | PhEUnop o e' => PhEUnop o (fold_add' e')
    | PhEBinop o e1 e2 => fold_add1 o (fold_add' e1) (fold_add' e2)
    | PhEFlatmap l1 x fn_e2 => PhEFlatmap (fold_add' l1) x (fun v => fold_add' (fn_e2 v))
    | PhEFold l1 e2 x y fn_e3 => PhEFold (fold_add' l1) (fold_add' e2) x y (fun v1 v2 => fold_add' (fn_e3 v1 v2))
    | PhEIf e1 e2 e3 => PhEIf (fold_add' e1) (fold_add' e2) (fold_add' e3)
    | PhELet x e1 fn_e2 => PhELet x (fold_add' e1) (fun v => fold_add' (fn_e2 v))
    end.

  Definition fold_add {t} (e : Phoas_expr t) : Phoas_expr t :=
    fun V => fold_add' (e V).

  Lemma phoas_expr_cases : forall V (t : type) (e : phoas_expr V t),
      (exists a, e = PhEAtom a) \/
        (exists v, e = PhEVar t v) \/
        (exists x, e = PhELoc t x) \/
        (exists t1 o (e' : phoas_expr V t1), e = PhEUnop o e') \/
        (exists t1 t2 (o : binop t1 t2 t) e1 e2, e = PhEBinop o e1 e2) \/
        (exists t1 t2 l1 x fn_e2, existT (phoas_expr V) t e = existT (phoas_expr V) (TList t2) (PhEFlatmap (l1 : phoas_expr V (TList t1)) x fn_e2)) \/
        (exists t1 (l1 : phoas_expr V (TList t1)) e2 x y fn_e3, e = PhEFold l1 e2 x y fn_e3) \/
        (exists e1 e2 e3, e = PhEIf e1 e2 e3) \/
        (exists t1 x (e1 : phoas_expr V t1) fn_e2, e = PhELet x e1 fn_e2).
  Proof.
    destruct e; eauto 14.
  Qed.

  Lemma atom_cases : forall (t : type) (a : atom t),
      match t return atom t -> Prop with
      | TWord => fun a => exists v, a = AWord v
      | TInt => fun a => exists v, a = AInt v
      | TBool => fun a => exists v, a = ABool v
      | TString => fun a => exists v, a = AString v
      | TList t' => fun a => a = ANil t'
      | TEmpty => fun a => a = AEmpty
      | _ => fun _ => True
      end a.
  Proof.
    destruct a; eauto.
  Qed.

  Ltac by_phoas_expr_cases :=
    match goal with
    | e : phoas_expr _ _ |- _ => unique pose proof (phoas_expr_cases _ _ e)
    end.
  Ltac destruct_exists :=
    match goal with
    | H : exists v, _ |- _ =>
        let v' := fresh v in
        destruct H as [v' H]; subst
    end.
  Ltac by_atom_cases :=
    match goal with
    | a : atom _ |- _ => unique pose proof (atom_cases _ a)
    end.

  Ltac existT_projT1_contra :=
    match goal with
    | H : existT _ _ _ = existT _ _ _ |- _ =>
        apply projT1_eq in H; discriminate
    end.

  Lemma fold_add1_sound : forall t1 t2 t3 (o : binop t1 t2 t3) e1 e2 store,
      interp_phoas_expr store (fold_add1 o e1 e2) = interp_phoas_expr store (PhEBinop o e1 e2).
  Proof.
    intros until o.
    destruct o; try reflexivity; intros.
    repeat by_phoas_expr_cases; intuition; repeat destruct_exists;
      try (repeat by_atom_cases; intuition; repeat destruct_exists; reflexivity);
      try existT_projT1_contra.
  Qed.

  Lemma fold_add_sound' : forall t (e : phoas_expr _ t) store,
      interp_phoas_expr store e = interp_phoas_expr store (fold_add' e).
  Proof.
    phoas_expr_induct e.
    rewrite fold_add1_sound. cbn. congruence.
  Qed.

  Theorem fold_add_sound : forall t (e : Phoas_expr t) store,
      interp_Phoas_expr store e = interp_Phoas_expr store (fold_add e).
  Proof.
    intros t e store. apply fold_add_sound'.
  Qed.

  Lemma fold_add1_wf : forall V V' t1 t2 t3 (C : @ctxt V V') e1 e1' e2 e2' (o : binop t1 t2 t3),
      phoas_expr_equiv C e1 e1' -> phoas_expr_equiv C e2 e2' ->
      phoas_expr_equiv C (fold_add1 o e1 e2) (fold_add1 o e1' e2').
  Proof.
    intros V V' t1 t2 t3 C e1 e1' e2 e2' o H1 H2.
    destruct o; try (constructor; assumption).
    inversion H1; inversion H2; subst; repeat eq_projT2_eq;
      try (repeat by_atom_cases; intuition; repeat destruct_exists; constructor);
      try assumption;
      try reflexivity.
  Qed.

  Lemma fold_add_wf' : forall V V' t (C : @ctxt V V') (e : phoas_expr _ t) (e' : phoas_expr _ t),
      phoas_expr_equiv C e e' -> phoas_expr_equiv C (fold_add' e) (fold_add' e').
  Proof.
    intros V V' t C e e' H. induction H; simpl; try (repeat constructor; assumption).
    apply fold_add1_wf; assumption.
  Qed.

  Theorem fold_add_wf : forall t (e : Phoas_expr t),
      Phoas_wf e -> Phoas_wf (fold_add e).
  Proof.
    unfold Phoas_wf. intros t e H V V'. apply fold_add_wf', H.
  Qed.

  Definition ex1 := ELet "x" (EBinop OPlus (EAtom (AInt (Z.of_nat 2)))
                                (EAtom (AInt (Z.of_nat 2))))
                      (EBinop OPlus (EVar _ "x") (EAtom (AInt (Z.of_nat 1)))).
  Definition ex1_ph := Phoasify ex1.

  Definition ex1_ph' := fold_add ex1_ph.
  Definition ex1' := Dephoasify nil ex1_ph'.

  Example pipeline_sound : forall store, interp_expr store map.empty ex1 = interp_expr store map.empty ex1'.
  Proof.
    intro store.
    rewrite phoasify_sound.
    rewrite fold_add_sound.
    apply dephoasify_sound.
    (* wellformedness *)
    apply fold_add_wf, phoasify_wf.
  Qed.
  (* End of example. *)
End WithMap.
