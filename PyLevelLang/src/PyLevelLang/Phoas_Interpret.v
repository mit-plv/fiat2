Require Import PyLevelLang.Language.
Require Import PyLevelLang.Phoas_Language.
Require Import PyLevelLang.Interpret.
Require Import PyLevelLang.Elaborate.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Section WithMap.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {locals: map.map string {t & interp_type (width := width) t}} {locals_ok: map.ok locals}.


  Fixpoint interp_phoas_expr {t : type} (l : locals) (e : phoas_expr interp_type t) : interp_type t :=
    match e with
    | PhEVar _ v => v
    | PhELoc _ x => get_local l x
    | PhEAtom a => interp_atom a
    | PhEUnop o e1 => interp_unop o (interp_phoas_expr l e1)
    | PhEBinop o e1 e2 => interp_binop o (interp_phoas_expr l e1) (interp_phoas_expr l e2)
    | PhEFlatmap l1 _ fn_l2 => flat_map (fun y => interp_phoas_expr l (fn_l2 y)) (interp_phoas_expr l l1)
    | PhEFold l1 e2 _ _ fn_e3 => let l1' := interp_phoas_expr l l1 in
                                 let a' := interp_phoas_expr l e2 in
                                 let fn' := fun v acc => interp_phoas_expr l (fn_e3 v acc) in
                                 fold_right fn' a' l1'
    | PhEIf e1 e2 e3 => if interp_phoas_expr l e1 then interp_phoas_expr l e2 else interp_phoas_expr l e3
    | PhELet _ e1 fn_e2 => interp_phoas_expr l (fn_e2 (interp_phoas_expr l e1))
    end.

  Section WithPhoasMap.
    Context {V : type -> Type}.
    Context {phoas_env: map.map string {t & V t}} {phoas_env_ok: map.ok phoas_env}.

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

    Definition set_phoas_local (env : phoas_env) (x : string) {t : type} (v : V t) :=
      map.put env x (existT _ _ v).

    Fixpoint phoasify {t : type} (env : phoas_env) (e : expr t) : phoas_expr V t :=
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
  End WithPhoasMap.

  (* Remove one occurrence of x from l if there is one.
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
        EFlatmap (dephoasify used' l1) x' (dephoasify used' (fn x'))
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

  Context {tenv : map.map string (type * bool)} {tenv_ok : map.ok tenv}.

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

  Section WithPhoasEnv.
    Context {phoas_env : forall V, map.map string {t : type & V t}} {phoas_env_ok : forall V, map.ok (phoas_env V)}.

    Definition phoasify_envs_consistent (G : tenv) (l : locals) (env : phoas_env interp_type) (store : locals) : Prop :=
      forall x,
        match map.get G x, map.get l x with
        | Some (t, is_mut), Some v =>
            if is_mut then map.get store x = Some v  /\ projT1 v = t
            else  map.get env x = Some v  /\ projT1 v = t
        | Some _, None => False
        | None, _ => True
        end.

    Lemma phoasify_envs_consistent_immut_step : forall G l env store x t (v : interp_type t), phoasify_envs_consistent G l env store -> phoasify_envs_consistent (map.put G x (t, false)) (set_local l x v) (set_phoas_local env x v) store.
    Proof.
      unfold phoasify_envs_consistent. intros. unfold set_local. unfold set_phoas_local. destruct (string_dec x0 x).
      - subst. repeat rewrite map.get_put_same; eauto.
      - repeat rewrite map.get_put_diff by assumption. pose proof (H x0) as H0.
        destruct (map.get G x0) eqn:E; auto.
    Qed.

    Lemma phoasify_sound' :
      forall {t : type} (e : expr t) (G : tenv),
        wf G e ->
        forall (l : locals) (env : phoas_env interp_type) (store : locals),
          phoasify_envs_consistent G l env store ->
          interp_expr l e = interp_phoas_expr store (phoasify env e).
    Proof.
      induction e; intros; simpl.
      - unfold get_local. inversion H. unfold phoasify_envs_consistent in H0.
        pose proof (H0 x) as Hx. rewrite H4 in Hx. unfold phoas_proj_expected.
        destruct (map.get l x).
        + destruct Hx. unfold proj_expected. subst. rewrite H5.
          rewrite (eq_dec_refl type_eq_dec). reflexivity.
        + exfalso. exact Hx.
      - unfold get_local. inversion H. unfold phoasify_envs_consistent in H0.
        pose proof (H0 x) as Hx. rewrite H4 in Hx. unfold phoas_proj_expected.
        destruct (map.get l x).
        + destruct  Hx. unfold proj_expected. subst. rewrite H5.
          rewrite (eq_dec_refl type_eq_dec). reflexivity.
        + exfalso. exact Hx.
      - reflexivity.
      - f_equal. inversion H. eq_projT2_eq.
      - inversion H; subst; repeat eq_projT2_eq. f_equal; eauto.
      - inversion H; repeat eq_projT2_eq. f_equal.
        + extensionality y. apply (IHe2 _ H8). apply phoasify_envs_consistent_immut_step. assumption.
        + eapply (IHe1 G); assumption.
      - inversion H; repeat eq_projT2_eq. f_equal.
        + extensionality v. extensionality acc. apply (IHe3 _ H11).
          repeat apply phoasify_envs_consistent_immut_step. assumption.
        + apply (IHe2 G); assumption.
        + apply (IHe1 G); assumption.
      - inversion H; repeat eq_projT2_eq. destruct (interp_expr l e1) eqn:E;
          rewrite (IHe1 _ H6 _ _ _ H0) in E; rewrite E.
        + apply (IHe2 _ H7 _ _ _ H0).
        + apply (IHe3 _ H8 _ _ _ H0).
      - inversion H; repeat eq_projT2_eq.
        rewrite (IHe1 _ H5 _ _ _ H0).
        apply (IHe2 _ H8). apply phoasify_envs_consistent_immut_step. exact H0.
    Qed.

    Definition Phoasify {t : type} (e : expr t) : Phoas_expr t:=
      fun (V : type -> Type) => phoasify (V := V) map.empty e.

    Definition phoasify_envs_consistent_closed (G : tenv) (l store : locals) : Prop :=
      forall x, match map.get G x with
                | Some (t, true) =>
                    match map.get l x with
                    | Some v => map.get store x = Some v /\ projT1 v = t
                    | None => False
                    end
                | _ => True
                end.

    Definition Flat_wf (G : tenv) {t : type} (e : expr t) :=
      (forall x, match map.get G x with
                 | Some (t, is_mut) =>
                     (* All variables are mutable *)
                     is_mut = true
                 | None => True
                 end) /\
        wf G e.

    Theorem phoasify_sound : forall {t : type} (e : expr t) (G : tenv),
        Flat_wf G e ->
        forall l store : locals,
          phoasify_envs_consistent_closed G l store ->
          interp_expr l e = interp_phoas_expr store (Phoasify e interp_type).
    Proof.
      intros t e G [H_closed H_wf] l store H_consistent_closed.
      assert (H_consistent : phoasify_envs_consistent G l map.empty store).
      { unfold phoasify_envs_consistent. intro x.
        pose proof (H_closed x) as H_closed'.
        pose proof (H_consistent_closed x) as H_consistent_closed'.
        destruct (map.get G x) eqn:E; trivial. destruct p. subst.
        assumption.
      }
      unfold Phoasify. eapply phoasify_sound'.
      - apply H_wf.
      - assumption.
    Qed.
  End WithPhoasEnv.

  Section expr_equiv.
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
  End expr_equiv.

  Section WithPhoasTypeEnv.
    Context {V : type -> Type}.
    (* Typing environment for mutable variables *)
    Context {tenv_mut : map.map string type} {tenv_mut_ok : map.ok tenv_mut}.

    Inductive phoas_wf {V : type -> Type} : tenv_mut -> forall {t : type}, phoas_expr V t -> Prop :=
    | wf_PhEVar G t v : phoas_wf G (PhEVar t v)
    | wf_PhELoc G t x :
      map.get G x = Some t ->
      phoas_wf G (PhELoc t x)
    | wf_PhEAtom G {t} (a : atom t) : phoas_wf G (PhEAtom a)
    | wf_PhEUnop G {t1 t2} (o : unop t1 t2) e :
      phoas_wf G e ->
      phoas_wf G (PhEUnop o e)
    | wf_PhEBinop G {t1 t2 t3} (o : binop t1 t2 t3) e1 e2 :
      phoas_wf G e1 ->
      phoas_wf G e2 ->
      phoas_wf G (PhEBinop o e1 e2)
    | wf_PhEFlatmap G {t1 t2} l1 x (fn_l2 : V t1 -> phoas_expr V (TList t2)) :
      phoas_wf G l1 ->
      (forall v, phoas_wf G (fn_l2 v)) ->
      phoas_wf G (PhEFlatmap l1 x fn_l2)
    | wf_PhEFold G {t1 t2} l1 e2 x y (fn_e3 : V t1 -> V t2 -> phoas_expr V t2) :
      phoas_wf G l1 ->
      phoas_wf G e2 ->
      (forall v1 v2, phoas_wf G (fn_e3 v1 v2)) ->
      phoas_wf G (PhEFold l1 e2 x y fn_e3)
    | wf_PhEIf G {t} e1 (e2 e3 : phoas_expr V t) :
      phoas_wf G e1 ->
      phoas_wf G e2 ->
      phoas_wf G e3 ->
      phoas_wf G (PhEIf e1 e2 e3)
    | wf_PhELet G {t1 t2} x e1 (fn_e2 : V t1 -> phoas_expr V t2) :
      phoas_wf G e1 ->
      (forall v, phoas_wf G (fn_e2 v)) ->
      phoas_wf G (PhELet x e1 fn_e2).

    Definition projT1_snd_T2 {A : Type} {P1 P2 : A -> Type} (v : {t : A & (P1 t * P2 t)%type}) :
      {t : A & P2 t} :=
      existT _ (projT1 v) (snd (projT2 v)).

    Definition dephoasify_envs_consistent (C : ctxt) (G : tenv_mut) (store l : locals) (used : list string) :=
      (forall (p : {t : type & (string * interp_type t)%type}),
          In p C ->
          let s := fst (projT2 p) in
          In s used /\
            (* Immutable variable name not used as mutable variable *)
            match map.get G s with
            | Some _ => False
            | None => True
            end /\
            match map.get l s with
            | Some p' => projT1_snd_T2 p = p'
            | None => False
            end)
      /\ (forall s, match map.get G s with
                    | Some t => In s used /\
                                  match map.get store s with
                                  | Some p => projT1 p = t /\ map.get l s = Some p
                                  | None => False
                                  end
                    | None => True
                    end).

    Lemma dephoasify_envs_consistent_immut_step: forall C G store l used t x y,
        dephoasify_envs_consistent C G store l used ->
        ~ In x used ->
        dephoasify_envs_consistent (vars t (x, y) :: C) G store (set_local l x y) (x :: used).
    Proof.
      intros C G store l used t x y [HL HR] H_not_in. split.
      - intros p [H_inL | H_inR].
        + subst; simpl. unfold set_local. rewrite map.get_put_same.
          unfold projT1_snd_T2. simpl. split;
            [left | split]; try reflexivity.
          pose proof (HR x) as HRx. destruct (map.get G x); trivial.
          destruct HRx as [HRL _]. apply H_not_in. assumption.
        + apply HL in H_inR. remember (fst (projT2 p)) as s; simpl.
          unfold set_local. destruct H_inR. split; [right; assumption |].
          rewrite map.get_put_diff; [assumption | congruence].
      - intro s. pose proof (HR s) as HRs. destruct (map.get store s) eqn:E.
        + unfold set_local. destruct (map.get G s); trivial. destruct HRs; split.
          * right; assumption.
          * rewrite map.get_put_diff; [assumption | congruence].
        + destruct (map.get G s); [destruct HRs; exfalso; assumption | trivial].
    Qed.

    Lemma dephoasify_envs_consistent_used_step: forall C G store l used x,
        dephoasify_envs_consistent C G store l used ->
        dephoasify_envs_consistent C G store l (x::used).
    Proof.
      intros C G store l used x [HL HR]. simpl in *.
      unfold dephoasify_envs_consistent. split.
      - intros p H. pose proof (HL p H) as [HL1 [HL2 HL3]].
        split; [right | split]; assumption.
      - intro s. pose proof (HR s) as HR'.
        destruct (map.get G s); destruct HR'; trivial.
        split; [right | ]; assumption.
    Qed.

    Lemma dephoasify_sound' :
      forall {t : type} (e : phoas_expr const_string t) (e0 : phoas_expr interp_type t) (C : ctxt),
        phoas_expr_equiv C e e0 ->
        forall (G : tenv_mut),
          phoas_wf G e ->
          forall (store l : locals) (used : list string),
            dephoasify_envs_consistent C G store l used ->
            interp_phoas_expr store e0 = interp_expr l (dephoasify used e).
    Proof.
      induction e; intros e0 C H_equiv G H_wf store l used H_consistent; simpl;
        inversion H_equiv; inversion H_wf; subst; repeat eq_projT2_eq; simpl.
      - unfold get_local. apply H_consistent in H3 as [_ [_ H3]]. simpl in H3.
        destruct (map.get l v).
        + unfold proj_expected. subst. simpl. rewrite (eq_dec_refl type_eq_dec). reflexivity.
        + exfalso; assumption.
      - inversion H_wf. subst. destruct H_consistent as [_ HR]. unfold get_local.
        pose proof (HR x') as HR'. rewrite H2 in HR'; destruct HR' as [_ HR'].
        destruct (map.get store x') eqn:E.
        + destruct (map.get l x'); destruct HR' as [HR'L HR'R];
            [injection HR'R as HR'R; congruence | discriminate].
        + exfalso; assumption.
      - f_equal; eauto.
      - f_equal; eauto.
      - f_equal.
        + extensionality y. eapply H.
          * apply H8.
          * apply H16.
          * apply dephoasify_envs_consistent_immut_step;
              [assumption | apply fresh_is_fresh].
        + eapply IHe.
          * apply H4.
          * apply H13.
          * apply dephoasify_envs_consistent_used_step. assumption.
      - f_equal; eauto.
        extensionality v. extensionality acc.
        eapply H; try eauto.
        repeat apply dephoasify_envs_consistent_immut_step;
          try apply fresh_is_fresh. assumption.
      - erewrite IHe1 by eauto. erewrite IHe2 by eauto. erewrite IHe3 by eauto.
        reflexivity.
      - eapply H; eauto. erewrite IHe by eauto.
        apply dephoasify_envs_consistent_immut_step;
          [assumption | apply fresh_is_fresh].
    Qed.

    Definition Dephoasify (used : list string) {t : type} (e : Phoas_expr t) : expr t :=
      dephoasify used (e const_string).

    Definition dephoasify_envs_consistent_closed (G : tenv_mut) (store l : locals) (used : list string) : Prop :=
      forall s : string, match map.get G s with
                         | Some t => In s used /\
                                       match map.get store s with
                                       | Some p => projT1 p = t /\ map.get l s = Some p
                                       | None => False
                                       end
                         | None => True
                         end.

    Definition Phoas_wf (G : tenv_mut) {t : type} (e : Phoas_expr t) :=
      (forall V1 V2, phoas_expr_equiv nil (e V1) (e V2)) /\
        forall V, phoas_wf G (e V).

    Theorem dephoasify_sound : forall {t : type} (e : Phoas_expr t) (G : tenv_mut) ,
        Phoas_wf G e ->
        forall (store l : locals) (used : list string),
          dephoasify_envs_consistent_closed G store l used ->
          interp_phoas_expr store (e interp_type) = interp_expr l (Dephoasify used e).
    Proof.
      intros t e G [H_equiv H_wf] store l used H_consistent_closed.
      eapply dephoasify_sound'.
      - apply H_equiv.
      - apply H_wf.
      - unfold dephoasify_envs_consistent. split.
        + intros p contra. apply in_nil in contra. exfalso; assumption.
        + assumption.
    Qed.

  End WithPhoasTypeEnv.
End WithMap.


(* TODO: move eq_dec_refl elsewhere
Flat_wf to Phoas_wf and vice versa
Try out separated tenv into mut and immut? By an auxiliary file instead of refactoring?
mem for bare metal; store for mutable; env for immutable *)
