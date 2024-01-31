Require Import fiat2.Language.
Require Import fiat2.Phoas_Language.
Require Import fiat2.Interpret.
Require Import fiat2.Elaborate.
Require Import coqutil.Tactics.forward.
Require Import coqutil.Tactics.Tactics.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Logic.Eqdep_dec.
Module DecidableFiat2Type <: DecidableType.
  Definition eq_dec := type_eq_dec.
  Definition U := type.
End DecidableFiat2Type.
Module Fiat2TypeEqDep := DecidableEqDep(DecidableFiat2Type).

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

  Inductive phoas_command_equiv : ctxt -> phoas_command V -> phoas_command V' -> Prop :=
  | eq_PhCSkip C : phoas_command_equiv C PhCSkip PhCSkip
  | eq_PhCSeq C c1 c1' c2 c2' :
    phoas_command_equiv C c1 c1' ->
    phoas_command_equiv C c2 c2' ->
    phoas_command_equiv C (PhCSeq c1 c2) (PhCSeq c1' c2')
  | eq_PhCLet C {t} (x x' : string) (e : phoas_expr _ t) e' fn_c fn_c' :
    phoas_expr_equiv C e e' ->
    (forall v v', phoas_command_equiv (vars _ (v, v') :: C) (fn_c v) (fn_c' v')) ->
    phoas_command_equiv C (PhCLet x e fn_c) (PhCLet x' e' fn_c')
  | eq_PhCLetMut C {t} (x x' : string) (e : phoas_expr _ t) e' c c' :
    x = x' ->
    phoas_expr_equiv C e e' ->
    phoas_command_equiv C c c' ->
    phoas_command_equiv C (PhCLetMut x e c) (PhCLetMut x' e' c')
  | eq_PhCGets C {t} x x' (e : phoas_expr _ t) e' :
    x = x' ->
    phoas_expr_equiv C e e' ->
    phoas_command_equiv C (PhCGets x e) (PhCGets x' e')
  | eq_PhCIf C e e' c1 c1' c2 c2' :
    phoas_expr_equiv C e e' ->
    phoas_command_equiv C c1 c1' ->
    phoas_command_equiv C c2 c2' ->
    phoas_command_equiv C (PhCIf e c1 c2) (PhCIf e' c1' c2')
  | eq_PhCForeach C {t} x x' (e : phoas_expr _ (TList t)) e' fn_c fn_c' :
    x = x' ->
    phoas_expr_equiv C e e' ->
    (forall v v', phoas_command_equiv (vars _ (v, v') :: C) (fn_c v) (fn_c' v')) ->
    phoas_command_equiv C (PhCForeach x e fn_c) (PhCForeach x' e' fn_c').
End PhoasExprEquiv.

Definition Phoas_wf {t : type} (e : Phoas_expr t) :=
  forall V1 V2, phoas_expr_equiv nil (e V1) (e V2).

Definition Phoas_command_wf (c : Phoas_command) :=
  forall V1 V2, phoas_command_equiv nil (c V1) (c V2).

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

  Fixpoint interp_phoas_command (store : phoas_env interp_type) (c : phoas_command interp_type) : phoas_env interp_type :=
    match c with
    | PhCSkip => store
    | PhCSeq c1 c2 => interp_phoas_command (interp_phoas_command store c1) c2
    | PhCLet x e fn_c => interp_phoas_command store (fn_c (interp_phoas_expr store e))
    | PhCLetMut x e c =>
        let store' := set_local store x (interp_phoas_expr store e) in
        let store'' := interp_phoas_command store' c in
        map.update store'' x (map.get store x)
    | PhCGets x e => set_local store x (interp_phoas_expr store e)
    | PhCIf e c1 c2 => interp_phoas_command store (if interp_phoas_expr store e then c1 else c2)
    | PhCForeach x l fn_c => fold_left (fun store' v => interp_phoas_command store' (fn_c v)) (interp_phoas_expr store l) store
    end.

  Definition interp_Phoas_command (store : phoas_env interp_type) (c : Phoas_command) :=
    interp_phoas_command store (c _).

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

    Fixpoint phoasify_command (env : phoas_env V) (c : command) : phoas_command V :=
      match c with
      | CSkip => PhCSkip
      | CSeq c1 c2 => PhCSeq (phoasify_command env c1) (phoasify_command env c2)
      | CLet x e c => PhCLet x (phoasify env e) (fun v => phoasify_command (set_phoas_local env x v) c)
      | CLetMut x e c => PhCLetMut x (phoasify env e) (phoasify_command env c)
      | CGets x e => PhCGets x (phoasify env e)
      | CIf e c1 c2 => PhCIf (phoasify env e) (phoasify_command env c1) (phoasify_command env c2)
      | CForeach x l c => PhCForeach x (phoasify env l) (fun v => phoasify_command (set_phoas_local env x v) c)
      end.
  End WithPhoasV.

  Definition Phoasify {t : type} (e : expr t) : Phoas_expr t :=
    fun (V : type -> Type) => phoasify (V := V) map.empty e.

  Definition Phoasify_command (c : command) : Phoas_command :=
    fun (V : type -> Type) => phoasify_command (V := V) map.empty c.
End WithMap.

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

(* Precondition: used contains all occurrences of mutable variable names in the command *)
Fixpoint dephoasify_command (used : list string) (c : phoas_command const_string) : command :=
  match c with
  | PhCSkip => CSkip
  | PhCSeq c1 c2 => CSeq (dephoasify_command used c1) (dephoasify_command used c2)
  | PhCLet x e fn_c =>
      let x' := fresh used x in
      let used' := x' :: used in
      CLet x' (dephoasify used e) (dephoasify_command used' (fn_c x'))
  | PhCLetMut x e c => CLetMut x (dephoasify used e) (dephoasify_command used c)
  | PhCGets x e => CGets x (dephoasify used e)
  | PhCIf e c1 c2 => CIf (dephoasify used e) (dephoasify_command used c1) (dephoasify_command used c2)
  | PhCForeach x l fn_c =>
      let x' := fresh used x in
      let used' := x' :: used in
      CForeach x' (dephoasify used l) (dephoasify_command used' (fn_c x'))
  end.

Definition Dephoasify (used : list string) {t : type} (e : Phoas_expr t) : expr t :=
  dephoasify used (e const_string).

Definition Dephoasify_command (used : list string) (c : Phoas_command) : command :=
  dephoasify_command used (c const_string).

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

Lemma fold_left_eq_ext : forall (A B : Type) (f g : A -> B -> A) (a a' : A) (l l' : list B),
    a = a' -> l = l' ->
    (forall x y, f x y = g x y) ->
    fold_left f l a = fold_left g l' a'.
Proof.
  intros A B f g a a' l; revert a a'.
  induction l as [|h t IHt]; intros a a' l' Ha Hl H; subst.
  - reflexivity.
  - simpl. apply IHt; congruence.
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

  Lemma phoasify_command_sound' :
    forall (c : command) (store env : phoas_env interp_type),
      interp_command store env c = interp_phoas_command store (phoasify_command env c).
  Proof.
    induction c; intros; simpl;
    try (rewrite IHc, phoasify_sound'; reflexivity).
    - reflexivity.
    - rewrite IHc1, IHc2; reflexivity.
    - rewrite phoasify_sound'; reflexivity.
    - rewrite phoasify_sound', IHc1, IHc2.
      destruct (interp_phoas_expr store (phoasify env e)); reflexivity.
    - rewrite phoasify_sound'. apply fold_left_eq_ext; try congruence.
      intros; apply IHc.
  Qed.

  Theorem phoasify_command_sound :
    forall (c : command) (store : phoas_env interp_type),
      interp_command store map.empty c = interp_Phoas_command store (Phoasify_command c).
  Proof.
    intros; apply phoasify_command_sound'.
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

  Lemma dephoasify_command_sound' :
    forall (c : phoas_command const_string) (c0 : phoas_command interp_type) (C : ctxt),
      phoas_command_equiv C c c0 ->
      forall (used : list string) (env : phoas_env interp_type),
        dephoasify_envs_consistent C used env ->
        forall (store : phoas_env interp_type),
          interp_phoas_command store c0 = interp_command store env (dephoasify_command used c).
  Proof.
    intros c c0 C H_equiv.
    induction H_equiv; intros used env H_consistent store; simpl.
    - reflexivity.
    - rewrite (IHH_equiv1 _ _ H_consistent). apply IHH_equiv2, H_consistent.
    - apply H1. rewrite (dephoasify_sound' _ _ _ _ H _ _ H_consistent).
      apply dephoasify_envs_consistent_step, H_consistent.
    - rewrite (IHH_equiv _ _ H_consistent).
      rewrite (dephoasify_sound' _ _ _ _ H0 _ _ H_consistent). congruence.
    - rewrite (dephoasify_sound' _ _ _ _ H0 _ _ H_consistent). congruence.
    - rewrite (dephoasify_sound' _ _ _ _ H _ _ H_consistent).
      destruct (interp_expr store env (dephoasify used e));
        [apply IHH_equiv1 | apply IHH_equiv2]; apply H_consistent.
    - apply fold_left_eq_ext; try trivial.
      + rewrite (dephoasify_sound' _ _ _ _ H0 _ _ H_consistent); reflexivity.
      + intros store' v'. apply H2, dephoasify_envs_consistent_step, H_consistent.
  Qed.

  Theorem dephoasify_command_sound :
    forall (c : Phoas_command),
      Phoas_command_wf c ->
        forall (store : phoas_env interp_type) (used : list string),
          interp_Phoas_command store c = interp_command store map.empty (Dephoasify_command used c).
  Proof.
    intros c H_wf store used; apply dephoasify_command_sound' with (C := nil).
    + apply H_wf.
    + unfold dephoasify_envs_consistent. intros p contra.
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

  Theorem fold_add_pipeline_sound : forall t (e : expr t) store used, interp_expr store map.empty e = interp_expr store map.empty (Dephoasify used (fold_add (Phoasify e))).
  Proof.
    intros t e store used.
    rewrite phoasify_sound.
    rewrite fold_add_sound.
    apply dephoasify_sound.
    (* wellformedness *)
    apply fold_add_wf, phoasify_wf.
  Qed.

  Definition ex1 := ELet "x" (EBinop OPlus (EAtom (AInt (Z.of_nat 2)))
                                (EAtom (AInt (Z.of_nat 2))))
                      (EBinop OPlus (EVar _ "x") (EAtom (AInt (Z.of_nat 1)))).
  Definition ex1_ph := Phoasify ex1.

  Definition ex1_ph' := fold_add ex1_ph.
  Definition ex1' := Dephoasify nil ex1_ph'.

  Example ex1_pipeline_sound : forall store, interp_expr store map.empty ex1 = interp_expr store map.empty ex1'.
  Proof. intros; apply fold_add_pipeline_sound. Qed.
  (* End of example. *)

  Ltac projT1_eq_for_projT2_eq := match goal with
                                  | H : existT ?f _ _ = existT ?f _ _ |- _ =>
                                      let H' := fresh H in
                                      pose proof projT1_eq H as H'; simpl in H'; try injection H'; intros; subst; eq_projT2_eq
                                  end.

  Definition flatmap_flatmap_head' {V : type -> Type} {t : type} (e : phoas_expr V t) : phoas_expr V t :=
    match e with
    | @PhEFlatmap _ t2 t3 l2 y fn_l3 =>
        (match l2 in (phoas_expr _ t0) return (V match t0 with
                                                 | TList t0' => t0'
                                                 | _ => TEmpty (* impossible case *)
                                                 end -> phoas_expr V (TList t3)) -> phoas_expr V (TList t3) -> phoas_expr V (TList t3)
         with
         | PhEFlatmap l1 x fn_l2 => fun fn_l3 _ => PhEFlatmap l1 x (fun v => PhEFlatmap (fn_l2 v) y fn_l3)
         | _ => fun _ e0 => e0
         end) fn_l3 (PhEFlatmap l2 y fn_l3)
    (* It is necessary to pass the reassembled PhEFlatmap l2 y fn_l3 from outside the convoy pattern for the definition to work *)
    | e' => e'
    end.

  Definition flatmap_flatmap_head {t : type} (e : Phoas_expr t) : Phoas_expr t :=
    fun V => flatmap_flatmap_head' (e V).

  Lemma flat_map_flat_map :
    forall {A B C} (l : list A) (f : B -> list C)  (g : A -> list B),
      flat_map f (flat_map g l) = flat_map (fun x => flat_map f (g x)) l.
  Proof.
    induction l; auto.
    intros. simpl. rewrite flat_map_app. rewrite IHl. reflexivity.
  Qed.

  Lemma flatmap_flatmap_head_correct' {t} (store : phoas_env interp_type) (e : phoas_expr _ t):
    interp_phoas_expr store e = interp_phoas_expr store (flatmap_flatmap_head' e).
  Proof.
    destruct e; auto.
    by_phoas_expr_cases; intuition; repeat destruct_exists;
      try (repeat by_atom_cases; intuition; repeat destruct_exists; reflexivity).
    projT1_eq_for_projT2_eq.
    apply flat_map_flat_map.
  Qed.

  Lemma flatmap_flatmap_head_correct {t} (store : phoas_env interp_type) (e : Phoas_expr t):
    interp_Phoas_expr store e = interp_Phoas_expr store (flatmap_flatmap_head e).
  Proof.
    apply flatmap_flatmap_head_correct'.
  Qed.

  (* let-lifting (with A Normal Form transformation technique  *)
  Fixpoint lift_let_from {V t} (e : phoas_expr V t) :
    (phoas_expr V t -> phoas_command V) -> phoas_command V :=
    match e with
    | PhEVar _ v => fun g => g (PhEVar _ v)
    | PhELoc _ x => fun g => g (PhELoc _ x)
    | PhEAtom a => fun g => g (PhEAtom a)
    | PhEUnop o e => fun g => lift_let_from e (fun e' => g (PhEUnop o e'))
    | PhEBinop o e1 e2 => fun g => lift_let_from e1
                                      (fun e1' => lift_let_from e2
                                                    (fun e2' => g (PhEBinop o e1' e2')))
    | PhEFlatmap l1 x fn_l2 => fun g => lift_let_from l1
                                          (fun l1' => g (PhEFlatmap l1' x fn_l2))
    | PhEFold l1 e2 x y fn_e3 => fun g => lift_let_from l1
                                             (fun l1' => lift_let_from e2
                                                           (fun e2' => g (PhEFold l1' e2' x y fn_e3)))
    | PhEIf e1 e2 e3 => fun g => lift_let_from e1
                                    (fun e1' => lift_let_from e2
                                                   (fun e2' => lift_let_from e3
                                                                 (fun e3' => g (PhEIf e1' e2' e3'))))
    | PhELet x e1 fn_e2 => fun g => lift_let_from e1 (fun e1' => PhCLet x e1' (fun v => g (fn_e2 v)))
    end.

  Fixpoint lift_let' {V} (e : phoas_command V) : phoas_command V :=
    match e with
    | PhCSkip => PhCSkip
    | PhCSeq c1 c2 => PhCSeq (lift_let' c1) (lift_let' c2)
    | PhCLet x e fn_c => lift_let_from e (fun e' => PhCLet x e' (fun v => lift_let' (fn_c v)))
    | PhCLetMut x e c => lift_let_from e (fun e' => PhCLetMut x e' (lift_let' c))
    | PhCGets x e => lift_let_from e (fun e' => PhCGets x e')
    | PhCIf e c1 c2 => lift_let_from e (fun e' => PhCIf e' (lift_let' c1) (lift_let' c2))
    | PhCForeach x l fn_c => lift_let_from l (fun l' => PhCForeach x l' (fun v => lift_let' (fn_c v)))
    end.

  Ltac reflexivity_with_lhs_evar_fun :=
    lazymatch goal with
    | |- ?f ?a = ?RHS =>
        let rhs := fresh "RHS" in
        set RHS as rhs;
        pattern a in rhs;
        subst rhs;
        apply eq_refl
    end.

  Lemma lift_let_from_correct : forall store t fn_e_c fn_v_c,
      (forall (e : phoas_expr _ t), interp_phoas_command store (fn_e_c e) = fn_v_c (interp_phoas_expr store e)) ->
      forall (e : phoas_expr _ t), interp_phoas_command store (lift_let_from e (fn_e_c)) = fn_v_c (interp_phoas_expr store e).
  Proof.
    induction e; try apply H; simpl in *;
    try (erewrite IHe; [reflexivity_with_lhs_evar_fun | trivial]);
    try (erewrite IHe1; [reflexivity_with_lhs_evar_fun | trivial];
         intro; erewrite IHe2; [reflexivity_with_lhs_evar_fun | trivial]);
    try (intro; erewrite IHe3; [reflexivity_with_lhs_evar_fun | trivial]).
    intro; apply H.
  Qed.

  Lemma lift_let_correct' : forall store c,
      interp_phoas_command store (lift_let' c) = interp_phoas_command store c.
  Proof.
    intros store c; revert store; induction c;
      intro store; simpl; try reflexivity;
      try (rewrite IHc1, IHc2; reflexivity);
      try (erewrite lift_let_from_correct; [reflexivity_with_lhs_evar_fun | trivial]).
    - intro; apply H.
    - intro; simpl. rewrite IHc; reflexivity.
    - simpl. intro e0. destruct (interp_phoas_expr store e0); rewrite ?IHc1, ?IHc2; reflexivity.
    - simpl. intro; apply fold_left_eq_ext; trivial.
  Qed.
  (* End of let-lifting *)

  (* Transformations that involve rearrangement of bindings are implemented in PHOAS
   Others, especially those which require pattern matching on the function argument or the function body,
   should not be implemented here *)
  Definition fold_flatmap_head' {V : type -> Type} {t : type} (e : phoas_expr V t) : phoas_expr V t :=
    match e with
    | @PhEFold _ t3 t4 l3 e4 x y fn_e5 =>
        match l3 in phoas_expr _ t0 return
              (V match t0 with
                 | TList t3' => t3'
                 | _ => TEmpty end -> V t4 -> phoas_expr V t4) -> phoas_expr V t4 -> phoas_expr V t4
        with
        | PhEFlatmap l1 z fn_l2 => fun fn_e5' _ => PhEFold l1 e4 z y (fun v acc => PhEFold (fn_l2 v) (PhEVar _ acc) x y fn_e5')
        | _ => fun _ e0 => e0
        end fn_e5 (PhEFold l3 e4 x y fn_e5)
    | e' => e'
    end.

  Definition fold_flatmap_head {t : type} (e : Phoas_expr t) : Phoas_expr t :=
    fun V => fold_flatmap_head' (e V).

  Lemma fold_flat_map : forall {A B C} (l : list A) (f : A -> list B) (g : B -> C -> C) (a : C),
      fold_right g a (flat_map f l) = fold_right (fun x y => fold_right g y (f x)) a l.
  Proof.
    induction l; eauto.
    intros. cbn. rewrite fold_right_app. f_equal. eauto.
  Qed.

  Ltac by_phoas_expr_cases_on e :=  unique pose proof (phoas_expr_cases _ _ e).

  Lemma fold_flatmap_head_correct' {t} (store : phoas_env interp_type) (e : phoas_expr _ t) :
    interp_phoas_expr store e = interp_phoas_expr store (fold_flatmap_head' e).
  Proof.
    destruct e; auto.
    by_phoas_expr_cases_on e1; intuition; repeat destruct_exists;
      try (repeat by_atom_cases; intuition; repeat destruct_exists; reflexivity).
    projT1_eq_for_projT2_eq.
    apply fold_flat_map.
  Qed.

  Lemma fold_flatmap_head_correct {t} (store : phoas_env interp_type) (e : Phoas_expr t)
    : interp_Phoas_expr store e = interp_Phoas_expr store (fold_flatmap_head e).
  Proof.
    apply fold_flatmap_head_correct'.
  Qed.

  Definition elt_ty t :=
  match t with
  | TList t' => t'
  | _ => TEmpty
  end.

  Definition match_singleton_list {V} {t} (e : phoas_expr V t) : option (phoas_expr V (elt_ty t)) :=
    match e with
    | PhEBinop o e' (PhEAtom (ANil _)) =>
        match o in binop t1 t2 t3 return (phoas_expr V t1) -> option (phoas_expr V (elt_ty t3)) with
        | OCons _ => fun e' => Some e'
        | _ => fun _ => None
        end e'
    | _ => None
    end.

  Lemma match_singleton_list_inner :
    forall V t1 t2 t3 (o : binop t1 t2 t3) e' e'',
      match o in binop t1 t2 t3 return (phoas_expr V t1) -> option (phoas_expr V (elt_ty t3)) with
        | OCons _ => fun e' => Some e'
        | _ => fun _ => None
      end e' = Some e'' -> existT (fun p => binop t1 (fst p) (snd p)) (t2, t3) o = existT _ (TList t1, TList t1) (OCons _).
  Proof.
    destruct o; intuition; try congruence.
  Qed.

  Lemma invert_match_singleton_list_ty :
    forall V t (e : phoas_expr V t) (p : phoas_expr V (elt_ty t)),
      match_singleton_list e = Some p ->
      TList (elt_ty t) = t.
  Proof.
    destruct e; simpl; try congruence.
    destruct e2; simpl; try congruence.
    destruct a; simpl; try congruence.
    intros. apply match_singleton_list_inner in H.
    apply projT1_eq in H as H1; simpl in H1.
    inversion H1; subst. reflexivity.
  Qed.

  Section __.
  Context (A B : Type)
    {HA : forall a b : A, {a=b} + {a<>b}}
    {HB : forall a b : B, {a=b} + {a<>b}}.
  Definition pair_eq_dec (p1 p2 : A * B) : {p1 = p2} + {p1 <> p2}.
    refine (let '(a1,b1) := p1 in let '(a2, b2) := p2 in
                                 if HA a1 a2 then if HB b1 b2 then left _ else right _ else right _);
      congruence.
    Defined.
  End __.

  Lemma invert_match_singleton_list :
    forall V t (e : phoas_expr V t) (p : phoas_expr V (elt_ty t)),
      match_singleton_list e = Some p ->
      existT _ t e = existT _ (TList (elt_ty t)) (PhEBinop (OCons _) p (PhEAtom (ANil _))).
  Proof.
    intros. apply invert_match_singleton_list_ty in H as H1.
    unshelve eapply eq_existT_curried.
    - congruence.
    - destruct e; simpl in *; try congruence.
      destruct e2; simpl; try congruence.
      destruct a; simpl; try congruence.
      apply match_singleton_list_inner in H as H2.
      apply projT1_eq in H2 as H3; simpl in H3.
      inversion H3; subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H2.
      + subst. inversion H. subst. simpl in *.
        rewrite Fiat2TypeEqDep.UIP_refl with (p := H1).
      (* instead of rewrite Eqdep.EqdepTheory.UIP_refl *)
        reflexivity.
      + apply pair_eq_dec; apply type_eq_dec.
  Qed.
  Print Assumptions invert_match_singleton_list.

  Definition fold_singleton_head' {V} {t : type} (e : phoas_expr V t) : phoas_expr V t :=
    match e with
    | @PhEFold _ t1 t2 l1 e2 x y fn_e3 =>
        match match_singleton_list l1 with
        | Some e1 => PhELet x e1 (fun v => PhELet y e2 (fn_e3 v))
        | None => PhEFold l1 e2 x y fn_e3
        end
    | e' => e'
    end.

  Definition fold_singleton_head {t : type} (e : Phoas_expr t) : Phoas_expr t :=
    fun V => fold_singleton_head' (e V).

  Lemma fold_singleton_head_correct' {t} (store : phoas_env interp_type) (e : phoas_expr _ t) :
    interp_phoas_expr store e = interp_phoas_expr store (fold_singleton_head' e).
  Proof.
    destruct e; auto.
    unfold fold_singleton_head'. destruct (match_singleton_list e1) eqn:E; auto.
    apply invert_match_singleton_list in E.
    simpl in *. eq_projT2_eq.
  Qed.
End WithMap.
