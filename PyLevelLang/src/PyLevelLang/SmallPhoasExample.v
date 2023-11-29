Require Import String List PeanoNat.

Inductive type : Type :=
| TNat
| TBool.

Inductive binop : type -> type -> type -> Type :=
| OPlus : binop TNat TNat TNat
| OAnd : binop TBool TBool TBool.

Inductive atom : type -> Type :=
| ANat : nat -> atom TNat
| ABool : bool -> atom TBool.

Inductive expr : type -> Type :=
| EVar (t : type) (x : string) : expr t
| EAtom {t : type} (a : atom t) : expr t
| EBinop {t1 t2 t3 : type} (o : binop t1 t2 t3) (e1 : expr t1) (e2: expr t2) : expr t3
| ELet {t1 t2 : type} (x : string) (e1 : expr t1) (e2 : expr t2) : expr t2.

Definition interp_type (t : type) : Type :=
  match t with
  | TNat => nat
  | TBool => bool
  end.

Section Phoas.
  Context {V : type -> Type}.
  Inductive phoas_expr : type -> Type :=
  | PhEVar (t : type) : V t -> phoas_expr t
  | PhEAtom {t : type} (a : atom t) : phoas_expr t
  | PhEBinop {t1 t2 t3 : type} (o : binop t1 t2 t3)
      (e1 : phoas_expr t1) (e2: phoas_expr t2) : phoas_expr t3
  | PhELet {t1 t2 : type} (x : string) (e1 : phoas_expr t1) (fn_e2 : V t1 -> phoas_expr t2) : phoas_expr t2.
End Phoas.
Arguments phoas_expr : clear implicits.

Definition Phoas_expr (t : type) := forall V, phoas_expr V t.

Section ExprEquiv.
  Context {V V' : type -> Type}.

  Definition ctxt := list { t : type & (V t * V' t)%type }.
  Definition vars := existT (fun t => (V t * V' t)%type).

  Inductive phoas_expr_equiv : ctxt -> forall {t : type},
        phoas_expr V t -> phoas_expr V' t -> Prop :=
  | eq_PhEVar C t (v : V t) (v' : V' t) :
    In (vars _ (v, v')) C -> phoas_expr_equiv C (PhEVar _ v) (PhEVar _ v')
  | eq_PhEAtom C t (a a' : atom t) :
    a = a' -> phoas_expr_equiv C (PhEAtom a) (PhEAtom a')
  | eq_PhEBinop C {t1 t2 t3} (o : binop t1 t2 t3) e1 e1' e2 e2' :
    phoas_expr_equiv C e1 e1' ->
    phoas_expr_equiv C e2 e2' ->
    phoas_expr_equiv C (PhEBinop o e1 e2) (PhEBinop o e1' e2')
  | eq_PhELet C {t1 t2} (x x' : string) e1 e1' (fn_e2 : V t1 -> phoas_expr V t2) fn_e2' :
    phoas_expr_equiv C e1 e1' ->
    (forall v v', phoas_expr_equiv (vars _ (v, v') :: C) (fn_e2 v) (fn_e2' v')) ->
    phoas_expr_equiv C (PhELet x e1 fn_e2) (PhELet x' e1' fn_e2').
End ExprEquiv.

Definition interp_binop {t1 t2 t3: type} (o : binop t1 t2 t3) :
  interp_type t1 -> interp_type t2 -> interp_type t3 :=
  match o with
  | OPlus => Nat.add
  | OAnd => andb
  end.

Definition default_val (t : type) : interp_type t :=
  match t as t' return interp_type t' with
  | TNat => 0
  | TBool => false
  end.

Definition cast {T : Type} {T1 T2 : T} (H : T1 = T2) (f: T -> Type) (x : f T1) :
  f T2 :=
  eq_rect T1 f x T2 H.

Definition type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
decide equality.
Defined.

Definition proj_expected (t_expected : type) (v : {t_actual & interp_type t_actual}) :
  interp_type t_expected :=
  match type_eq_dec (projT1 v) t_expected with
  | left H => cast H _ (projT2 v)
  | _ => default_val t_expected
  end.

Definition env (a : Type) := list (string * a).

Definition phoas_env (V : type -> Type) := env {t & V t}.
Definition venv := phoas_env interp_type.
Definition tenv := env type.

Fixpoint get_env {a} (l : env a) (x : string) : option a :=
  match l with
  | nil => None
  | (y, v) :: l' => if String.eqb x y then Some v else get_env l' x
  end.

Definition get_venv (l : venv) {t : type} (x : string) : interp_type t :=
  match get_env l x with
  | None => default_val t
  | Some v => proj_expected t v
  end.

Definition get_tenv (l : tenv) (x : string) : option type :=
  get_env l x.

Definition interp_atom {t : type} (a : atom t) : interp_type t :=
  match a with
  | ANat n => n
  | ABool b => b
  end.

Fixpoint interp_expr (l : venv) {t : type} (e : expr t) : interp_type t :=
  match e in (expr t0) return (interp_type t0) with
  | EVar _ x => get_venv l x
  | EAtom a => interp_atom a
  | EBinop o e1 e2 => interp_binop o (interp_expr l e1) (interp_expr l e2)
  | ELet x e1 e2 => interp_expr ((x, existT _ _ (interp_expr l e1)) :: l) e2
  end.

Fixpoint interp_phoas_expr {t : type} (e : phoas_expr interp_type t) : interp_type t :=
  match e with
  | PhEVar _ v => v
  | PhEAtom a => interp_atom a
  | PhEBinop o e1 e2 => interp_binop o (interp_phoas_expr e1) (interp_phoas_expr e2)
  | PhELet _ e1 fn_e2 => interp_phoas_expr (fn_e2 (interp_phoas_expr e1))
  end.

Inductive wf : tenv -> forall {t : type}, expr t -> Prop :=
| wf_EVar G t (x : string) :
  get_tenv G x = Some t -> wf G (EVar t x)
| wf_EAtom G {t} (a : atom t) :
  wf G (EAtom a)
| wf_EBinop  G {t1 t2 t3} (o : binop t1 t2 t3)
    (e1 : expr t1) (e2 : expr t2) :
  wf G e1 -> wf G e2 -> wf G (EBinop o e1 e2)
| wf_ELet G {t1 t2} (x : string) (e1 : expr t1) (e2 : expr t2) :
  wf G e1 -> wf ((x, t1) :: G) e2 -> wf G (ELet x e1 e2).

Definition Flat_wf {t : type} (e : expr t) := wf nil e.

Definition const_string : type -> Type := fun _ => string.

(* ???
Inductive str_phoas_wf : tenv -> forall {t : type}, phoas_expr const_string t -> Prop :=
| wf_PhEVar G t x :
  get_tenv G x = Some t -> str_phoas_wf G (PhEVar t x)
| wf_PhEAtom G {t} (a : atom t) :
  str_phoas_wf G (PhEAtom a)
| wf_PhEBinop  G {t1 t2 t3} (o : binop t1 t2 t3) e1 e2 :
  str_phoas_wf G e1 ->
  str_phoas_wf G e2 ->
  str_phoas_wf G (PhEBinop o e1 e2)
| wf_PhELet G {t1 t2} x e1 (fn_e2 : const_string t1 -> phoas_expr const_string t2) :
  str_phoas_wf G e1 ->
  (forall v, str_phoas_wf G (fn_e2 v)) ->
  str_phoas_wf G (PhELet x e1 fn_e2).

May not be necessary - consider using phoas_equiv instead
 Also may not need G and store to be consistent in Interpret2; try using the fact that the engineering design is the same for flat and phoas when var is not found in locals / store *)

Definition Phoas_wf {t} (e : Phoas_expr t) :=
  forall V V', phoas_expr_equiv nil (e V) (e V').

(*
flat phoasify V equiv const_string
            V equiv const_string dephoasify flat
*)

(* Default value of type (phoas_expr V t) *)
Definition default_phoas_expr {V}(t : type) : phoas_expr V t :=
  match t return phoas_expr V t with
  | TNat => PhEAtom (ANat (default_val TNat))
  | TBool => PhEAtom (ABool (default_val TBool))
  end.

(* Phoas map lookup, returning a default if nothing is found, for type correctness *)
Definition phoas_proj_expected {V}(t_expected : type) (v : {t_actual & V t_actual}) :
  phoas_expr V t_expected :=
  (* Return (phoas_expr t_expected) rather than (V t_expected)
     to avoid declaring "forall t, V t is inhabited" *)
  match type_eq_dec (projT1 v) t_expected with
  | left H => PhEVar _ (cast H _ (projT2 v))
  | _ => default_phoas_expr t_expected
  end.

Definition get_phoas_env {V} (l : phoas_env V) {t : type} (x : string) : phoas_expr V t :=
  match get_env l x with
  | None => default_phoas_expr t
  | Some v => phoas_proj_expected t v
  end.

Fixpoint phoasify {V} {t : type} (env : phoas_env V) (e : expr t) : phoas_expr V t :=
  match e with
  | EVar _ x => get_phoas_env env x
  | EAtom a => PhEAtom a
  | EBinop o e1 e2 => PhEBinop o (phoasify env e1) (phoasify env e2)
  | ELet x e1 e2 => PhELet x (phoasify env e1) (fun v => phoasify ((x, existT _ _ v) :: env) e2)
  end.

Definition Phoasify {t : type} (e : expr t) :=
  fun V => phoasify (V := V) nil e.

Open Scope string_scope.
(* Remove one occurrence of x from l if there is one.
 * Auxiliary function for the definition of fresh' below *)
Fixpoint remove_one (x : string) (l : list string) : list string :=
  match l with
  | nil => nil
  | h :: t => if String.eqb h x then t else h :: remove_one x t
  end.

Lemma in_remove_one_len : forall (x : string) (l : list string),
    In x l -> List.length l = S (List.length (remove_one x l)).
Proof.
  intros. induction l.
  - apply in_nil in H. exfalso. apply H.
  - simpl in H. destruct (String.eqb a x) eqn:E.
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
    + destruct (String.eqb a y) eqn:E.
      * rewrite eqb_eq in E. rewrite HL in E. left. exact E.
      * right. simpl. rewrite E. simpl. left. exact HL.
    + destruct (IHl HR) with (y := y) as [HL' | HR'].
      * left. exact HL'.
      * right. simpl. destruct (String.eqb a y) eqn:E.
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
           | left _ => fresh' n (remove_one x used) ((x ++ "'"))
           | right _ => x
           end
  end.

(* Given a list of used names and a hint, return a fresh name *)
Definition fresh (used : list string) (x : string) : string :=
  fresh' (List.length used) used x.

Lemma len_app : forall y : string, String.length y < String.length (y ++ "'").
Proof.
  induction y; auto. simpl. apply Arith_prebase.lt_n_S_stt. apply IHy.
Qed.

Lemma fresh'_len : forall (budget : nat) (used : list string) (x : string),
    String.length x <= String.length (fresh' budget used x).
Proof.
  induction budget; intros.
  - destruct used; unfold fresh'; constructor.
  - destruct (in_dec string_dec x used) eqn:E.
    + unfold fresh'. rewrite E.
      apply Nat.le_trans with (m := String.length (x ++ "'")).
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
      * assert (HA : String.length (x ++ "'") <= String.length (fresh' (Datatypes.length used) used x)).
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

Fixpoint dephoasify (used : list string) {t : type} (e : phoas_expr const_string t) : expr t :=
  match e with
  | PhEVar t x => EVar t x
  | PhEAtom a => EAtom a
  | PhEBinop o e1 e2 => EBinop o (dephoasify used e1) (dephoasify used e2)
  | PhELet x e1 fn_e2 =>
      let x' := fresh used x in
      let used' := x' :: used in
      ELet x' (dephoasify used e1) (dephoasify used' (fn_e2 x'))
  end.

Definition Dephoasify {t} (e : Phoas_expr t) : expr t :=
  dephoasify nil (e const_string).

Definition ex1 := ELet "x" (EBinop OPlus (EAtom (ANat 2)) (EAtom (ANat 2))) (EBinop OPlus (EVar _ "x") (EAtom (ANat 1))).
Compute (phoasify nil ex1).
Compute (Phoasify ex1).
Compute (Phoasify ex1 const_string).

Definition ex1_ph := Eval compute in (Phoasify ex1 const_string).

Lemma ex1_ph_wf : phoas_expr_equiv nil ex1_ph ex1_ph.
Proof.
  unfold ex1_ph. repeat constructor.
Qed.

Definition ex1_opt_ph := id ex1_ph.
Compute (dephoasify nil ex1_opt_ph).
Definition ex1_opt := Eval compute in (dephoasify nil ex1_opt_ph).
Lemma ex1_opt_wf : wf nil ex1_opt.
Proof.
  unfold ex1. repeat constructor.
Qed.

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

Definition phoasify_envs_consistent (G : tenv) (l : venv) (l' : phoas_env interp_type) :=
  forall x, match get_tenv G x with
            | Some t => match get_env l x with
                        | Some v => projT1 v = t /\ get_env l' x = Some v
                        | None => False
                        end
            | None => True
            end.

Lemma phoasify_envs_consistent_step : forall (G : tenv) (l : venv) (l' : phoas_env interp_type),
    phoasify_envs_consistent G l l' ->
    forall x t (v : interp_type t),
    phoasify_envs_consistent ((x, t) :: G) ((x, existT _ _ v) :: l) ((x, existT _ _ v) :: l').
Proof.
  intros G l l' H x t v. unfold phoasify_envs_consistent. intro y.
  unfold get_tenv. unfold get_env.
  destruct (String.eqb y x).
  + split; reflexivity.
  + apply H.
Qed.

Lemma phoasify_sound' : forall t (e : expr t) (G : tenv),
    wf G e ->
    forall (l : venv) (l' : phoas_env interp_type),
      phoasify_envs_consistent G l l' ->
      interp_expr l e = interp_phoas_expr (phoasify l' e).
Proof.
  induction e; intros G H_wf l l' H_consistent; inversion H_wf; subst.
  - simpl. pose proof (H_consistent x) as H_consistent. rewrite H2 in H_consistent.
    unfold get_venv. destruct (get_env l x) eqn:E; try (exfalso; assumption).
    + unfold get_phoas_env. destruct H_consistent as [_ HR]. rewrite HR.
      unfold proj_expected. unfold phoas_proj_expected.
      destruct (type_eq_dec (projT1 s) t); destruct t; reflexivity.
  - reflexivity.
  - simpl. repeat eq_projT2_eq. rewrite (IHe1 _ H3 l l'); auto.
    rewrite (IHe2 _ H7 l l'); auto.
  - simpl. repeat eq_projT2_eq. rewrite (IHe1 _ H3 l l'); auto.
    remember (interp_phoas_expr (phoasify l' e1)) as v.
    rewrite (IHe2 _ H6 ((x, existT _ _ v) :: l) ((x, existT _ _ v) :: l')).
    + reflexivity.
    + apply phoasify_envs_consistent_step. auto.
Qed.

Theorem phoasify_sound : forall t (e : expr t),
    Flat_wf e ->
    interp_expr nil e = interp_phoas_expr (Phoasify e interp_type).
Proof.
  unfold Phoasify. intros t e H_wf. apply phoasify_sound' with (G := nil); auto.
  unfold phoasify_envs_consistent. unfold get_tenv. unfold get_env. auto.
Qed.

Definition dephoasify_envs_consistent (C : @ctxt const_string interp_type) (used : list string) (l : venv) :=
  forall v, In v C -> In (fst (projT2 v)) used /\
                        match get_env l (fst (projT2 v)) with
                        | Some u => existT _ _  (snd (projT2 v)) = u
                        | None => False
                        end.

Lemma dephoasify_envs_consistent_step : forall C used l,
    dephoasify_envs_consistent C used l ->
    forall t x v',
      dephoasify_envs_consistent (vars t (fresh used x, v') :: C) (fresh used x :: used) ((fresh used x, existT _ _ v') :: l).
Proof.
  unfold dephoasify_envs_consistent. intros C used l H t x v' p [HL | HR].
  - split; subst; simpl.
    + auto.
    + rewrite eqb_refl. reflexivity.
  - pose proof (H p HR) as [HL' HR']. split.
    + right. assumption.
    + simpl. destruct (fst (projT2 p) =? fresh used x) eqn:E.
      * rewrite eqb_eq in E. rewrite E in HL'. apply fresh_is_fresh in HL'.
        exfalso; assumption.
      * assumption.
Qed.

Lemma dephoasify_sound' : forall t (e : phoas_expr const_string t) (C : ctxt) (e0 : phoas_expr interp_type t),
    phoas_expr_equiv C e e0 ->
    forall (used : list string) (l : venv),
      dephoasify_envs_consistent C used l ->
      interp_phoas_expr e0 = interp_expr l (dephoasify used e).
Proof.
  intro t. induction e; intros C e0 H_equiv used l H_consistent;
    inversion H_equiv; repeat eq_projT2_eq.
  - unfold dephoasify_envs_consistent in H_consistent.
    apply H_consistent in H3 as [_ HR]; simpl in *.
    unfold get_venv. destruct (get_env l v).
    + unfold proj_expected. destruct s. apply projT1_eq in HR as HR1.
      simpl in HR1; subst. simpl. rewrite eq_dec_refl.
      apply Eqdep_dec.inj_pair2_eq_dec in HR; auto.
      apply type_eq_dec.
    + exfalso; assumption.
  - simpl. rewrite (IHe1 _ _ H3 _ _ H_consistent).
    rewrite (IHe2 _ _ H8 _ _ H_consistent). reflexivity.
  - simpl. remember (fresh used x) as v. remember (interp_expr l (dephoasify used e)) as v'.
    rewrite H with (v := v) (C := (vars t1 (v, v') :: C)) (used := (v :: used)) (l := (v, existT _ _ v') :: l).
    + reflexivity.
    + rewrite (IHe C _ H4 used l H_consistent). rewrite <- Heqv'. apply H8.
    + rewrite Heqv. apply dephoasify_envs_consistent_step. assumption.
Qed.

Theorem dephoasify_sound : forall t (e : Phoas_expr t),
    Phoas_wf e ->
    interp_phoas_expr (e interp_type) = interp_expr nil (Dephoasify e).
Proof.
  intros t e H.
  apply dephoasify_sound' with (C := nil); auto.
  unfold dephoasify_envs_consistent; auto.
Qed.

Definition projT1_fst_projT2 {A : Type} {P P' : A -> Type} (p : {t : A & (P t * P' t)%type}) :=
  existT P (projT1 p) (fst (projT2 p)).

Definition projT1_snd_projT2 {A : Type} {P P' : A -> Type} (p : {t : A & (P t * P' t)%type}) :=
  existT P' (projT1 p) (snd (projT2 p)).

Definition phoasify_tenvs_consistent G {V} (env : phoas_env V) {V'} (env' : phoas_env V') (C : ctxt (V := V) (V' := V')) :=
  forall x, match get_tenv G x with
            | Some t => exists p, In p C /\ projT1 p = t /\
                                    get_env env x = Some (projT1_fst_projT2 p) /\
                                    get_env env' x = Some (projT1_snd_projT2 p)
            | None => True
            end.

Lemma phoasify_tenvs_consistent_step : forall G V (env : phoas_env V) V' (env' : phoas_env V') (C : @ctxt V V'),
    phoasify_tenvs_consistent G env env' C ->
    forall x t (v : V t) (v' : V' t),
      phoasify_tenvs_consistent ((x, t) :: G) ((x, existT _ _ v) :: env) ((x, existT _ _ v') :: env') (vars _ (v, v') :: C).
Proof.
  unfold phoasify_tenvs_consistent. intros G V env V' env' C H x t v v' y.
  unfold get_tenv. unfold get_env. destruct (y =? x) eqn:E.
  - exists (existT _ t (v, v')). simpl. split.
    + left. reflexivity.
    + split; try reflexivity. unfold projT1_fst_projT2. unfold projT1_snd_projT2. split; reflexivity.
  - pose proof (H y) as H'. destruct (get_tenv G y) eqn:E';
      unfold get_tenv in E'; unfold get_env in E'; rewrite E'.
    + destruct H' as [p [Hp1 [Hp2 [Hp3 Hp4]]]].
      exists p. repeat split; auto.
      * right; auto.
    + trivial.
Qed.

Lemma phoasify_wf' : forall (t : type) (e : expr t) (G : tenv),
    wf G e -> forall V (env : phoas_env V) V' (env' : phoas_env V')
                     (C : ctxt (V := V) (V' := V')),
      phoasify_tenvs_consistent G env env' C ->
      phoas_expr_equiv C (phoasify env e) (phoasify env' e).
Proof.
  intro t. induction e; intros G H_wf V env V' env' C H_consistent;
    inversion H_wf; subst.
  - simpl. unfold phoasify_tenvs_consistent in H_consistent.
    pose proof (H_consistent x) as Hx. rewrite H2 in Hx.
    destruct Hx as [p [Hp1 [Hp2 [Hp3 Hp4]]]]. unfold get_phoas_env. rewrite Hp3. rewrite Hp4.
    destruct p as [t' [l r]].
    simpl in Hp2; subst. unfold projT1_fst_projT2. unfold projT1_snd_projT2. simpl.
    unfold phoas_proj_expected. simpl. rewrite eq_dec_refl. constructor. apply Hp1.
  - constructor. reflexivity.
  - simpl. constructor; repeat eq_projT2_eq.
  - simpl. constructor; repeat eq_projT2_eq. intros v v'. apply IHe2 with (G := ((x, t1) :: G)).
    auto. apply phoasify_tenvs_consistent_step. auto.
Qed.

Theorem phoasify_wf : forall (t : type) (e : expr t),
    Flat_wf e -> Phoas_wf (Phoasify e).
Proof.
  unfold Phoas_wf. intros t e H V V'.
  apply phoasify_wf' with (G := nil). assumption.
  unfold phoasify_tenvs_consistent. intro x.
  unfold get_tenv. unfold get_env. trivial.
Qed.

Definition dephoasify_tenvs_consistent (C : @ctxt const_string const_string) (used : list string) (G : tenv) :=
  forall p, In p C -> In (fst (projT2 p)) used /\ get_tenv G (fst (projT2 p)) = Some (projT1 p).

Lemma dephoasify_tenvs_consistent_step : forall C used G,
    dephoasify_tenvs_consistent C used G ->
    forall x t,
      let x' := fresh used x in
      dephoasify_tenvs_consistent (vars t (x', x') :: C) (x' :: used) ((x', t) :: G).
Proof.
  unfold dephoasify_tenvs_consistent. intros C used G H x t p [HL | HR].
  - rewrite <- HL. simpl. split.
    + auto.
    + unfold get_tenv. unfold get_env. rewrite eqb_refl. reflexivity.
  - apply H in HR as [HL HR]. split.
    + right. assumption.
    + destruct p as [t' [l r]]. simpl in *. unfold get_tenv. unfold get_env.
      destruct (l =? fresh used x) eqn:E.
      * rewrite eqb_eq in E. rewrite E in HL. apply fresh_is_fresh in HL.
        exfalso; assumption.
      * assumption.
Qed.

Theorem dephoasify_wf' : forall (t : type) (e : phoas_expr const_string t) C,
    phoas_expr_equiv C e e ->
    forall used G,
      dephoasify_tenvs_consistent C used G ->
      wf G (dephoasify used e).
Proof.
  intro t. induction e; intros C H_equiv used G H_consistent;
    inversion H_equiv; subst; repeat eq_projT2_eq.
  - unfold dephoasify_tenvs_consistent in H_consistent.
    apply H_consistent in H3 as [H_in HG]. simpl in *.
    constructor. auto.
  - constructor.
  - simpl. constructor.
    + apply IHe1 with (C := C); auto.
    + apply IHe2 with (C := C); auto.
  - simpl. constructor.
    + apply IHe with (C := C); auto.
    + remember (fresh used x) as x'. apply H with (C := (vars t1 (x', x') :: C)).
      apply H10. rewrite Heqx'. apply dephoasify_tenvs_consistent_step.
      assumption.
Qed.

Theorem dephoasify_wf : forall (t : type) (e : Phoas_expr t),
    Phoas_wf e -> Flat_wf (Dephoasify e).
Proof.
  intros t e H. apply dephoasify_wf' with (C := nil); auto.
  unfold dephoasify_tenvs_consistent. intros p contra.
  apply in_nil in contra. exfalso. assumption.
Qed.

(* ??? Question: For mutable variables, do we rely on the same engineering design in the case of malformed environment for both expr and phoas_expr (hence requiring their value envs to be exactly the same in the theorems), or do we talk about the type env for the mutable vars too? *)
