Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import List String ZArith Permutation.

Fixpoint repeat_string (s : string) (n : nat) : string :=
  match n with
  | O => ""
  | S n => s ++ repeat_string s n
  end.

Lemma repeat_string_length : forall s n,
    String.length (repeat_string s n) = String.length s * n.
Proof.
  induction n; simpl; auto.
  rewrite string_app_length. intuition auto with *.
Qed.

Definition fresh_var (x : string) (free_vars : list string) :=
  if inb String.eqb x free_vars
  then append x (repeat_string "'" (S (list_max (List.map length free_vars))))
  else x.

Lemma fresh_var_is_fresh : forall x l, ~ In (fresh_var x l) l.
Proof.
  unfold fresh_var; intros. case_match.
  2: rewrite inb_false_iff in *; auto.
  intro contra. apply In_length_le_max in contra.
  rewrite string_app_length, repeat_string_length in contra.
  simpl in *. rewrite Nat.add_0_r in contra.
  apply add_l_le in contra. intuition auto with *.
Qed.

Fixpoint sub_lookup {A} (x : string) (l : list (string * A)) : option A :=
  match l with
  | nil => None
  | (y, a) :: l => if String.eqb x y then Some a else sub_lookup x l
  end.

Fixpoint substitute (sub : list (string * expr)) (free_vars : list string) (e0 : expr) : expr :=
  (* Expect sub to map every free immutable variable in e0 to some expression *)
  (* free_vars should contain all free variables in the range of the sub argument that must not be captured *)
  match e0 with
  | EVar x => match sub_lookup x sub with
              | Some e => e
              | None => EVar x
              end
  | ELoc x => ELoc x
  | EAtom a => EAtom a
  | EUnop o e0 => EUnop o (substitute sub free_vars e0)
  | EBinop o e1 e2 => EBinop o (substitute sub free_vars e1) (substitute sub free_vars e2)
  | EIf e1 e2 e3 => EIf (substitute sub free_vars e1) (substitute sub free_vars e2) (substitute sub free_vars e3)
  | ELet e1 x e2 =>
      let x' := fresh_var x free_vars in
      ELet (substitute sub free_vars e1) x'
        (substitute ((x, EVar x') :: sub) (x' :: free_vars) e2)
  | EFlatmap e1 x e2  =>
      let x' := fresh_var x free_vars in
      EFlatmap (substitute sub free_vars e1) x'
        (substitute ((x, EVar x') :: sub) (x' :: free_vars) e2)
  | EFold e1 e2 v acc e3 =>
      let v' := fresh_var v free_vars in
      let acc' := fresh_var acc (v' :: free_vars) in
      EFold (substitute sub free_vars e1) (substitute sub free_vars e2) v' acc'
        (substitute ((acc, EVar acc') :: (v, EVar v') :: sub) (acc' :: v' :: free_vars) e3)
  | ERecord l => ERecord (List.map (fun '(s, e) => (s, substitute sub free_vars e)) l)
  | EAccess e s => EAccess (substitute sub free_vars e) s
  | EDict l => EDict (List.map (fun '(ke, ve) => (substitute sub free_vars ke, substitute sub free_vars ve)) l)
  | EInsert d k v => EInsert (substitute sub free_vars d) (substitute sub free_vars k) (substitute sub free_vars v)
  | EDelete d k => EDelete (substitute sub free_vars d) (substitute sub free_vars k)
  | ELookup d k => ELookup (substitute sub free_vars d) (substitute sub free_vars k)
  | EOptMatch e1 e2 x e3 =>
      let x' := fresh_var x free_vars in
      EOptMatch (substitute sub free_vars e1) (substitute sub free_vars e2) x'
        (substitute ((x, EVar x') :: sub) (x' :: free_vars) e3)
  | EDictFold d e0 k v acc e =>
      let k' := fresh_var k free_vars in
      let v' := fresh_var v (k' :: free_vars) in
      let acc' := fresh_var acc (v' :: k' :: free_vars) in
      EDictFold (substitute sub free_vars d) (substitute sub free_vars e0) k' v' acc'
        (substitute ((acc, EVar acc') :: (v, EVar v') :: (k, EVar k') :: sub) (acc' :: v' :: k' :: free_vars) e)
  | ESort e => ESort (substitute sub free_vars e)
  | EFilter l x p =>
      let x' := fresh_var x free_vars in
      EFilter (substitute sub free_vars l) x'
        (substitute ((x, EVar x') :: sub) (x' :: free_vars) p)
  | EJoin l1 l2 x y p r =>
      let x' := fresh_var x free_vars in
      let y' := fresh_var y (x' :: free_vars) in
      EJoin (substitute sub free_vars l1) (substitute sub free_vars l2) x' y'
        (substitute ((y, EVar y') :: (x, EVar x') :: sub) (y' :: x' :: free_vars) p)
        (substitute ((y, EVar y') :: (x, EVar x') :: sub) (y' :: x' :: free_vars) r)
  | EProj l x r =>
      let x' := fresh_var x free_vars in
      EProj (substitute sub free_vars l) x'
        (substitute ((x, EVar x') :: sub) (x' :: free_vars) r)
  end.

Definition get_free_vars {A} {tenv : map.map string A} : tenv -> list string :=
  map.fold (fun l x _ => x :: l) nil.

Lemma get_free_vars_empty : forall A {m : map.map string A} {m_ok : map.ok m},
    get_free_vars (map.empty (map:=m)) = nil.
Proof.
  unfold get_free_vars; intros. apply Properties.map.fold_empty.
Qed.

Section WithMap.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.

  Lemma get_free_vars__map_get_None : forall x (G : tenv),
      ~ In x (get_free_vars G) <-> map.get G x = None.
  Proof.
    intros. unfold get_free_vars. apply map.fold_spec; intuition auto.
    1: apply map.get_empty.
    1:{ destruct (String.eqb x k) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
        1: simpl in *; intuition auto.
        1: rewrite_map_get_put_goal. }
    1:{ destruct (String.eqb x k) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
        all: rewrite_map_get_put_hyp; congruence. }
  Qed.

  Definition sub_wf (Genv0 Gstore Genv : tenv) (sub : list (string * expr)) : Prop :=
    forall x t, map.get Genv0 x = Some t ->
                match sub_lookup x sub with
                | Some e => type_of Gstore Genv e t
                | None => False
                end.

    Lemma get_free_vars__map_get_Some : forall x (G : tenv),
        In x (get_free_vars G) <-> exists t, map.get G x = Some t.
    Proof.
      intros. unfold get_free_vars. apply map.fold_spec; intuition auto.
      1: apply in_nil in H; intuition auto.
      1: destruct_exists; rewrite map.get_empty in *; congruence.
      1:{ destruct (String.eqb x k) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          all: rewrite_map_get_put_goal.
          1: exists v; auto.
                    1: destruct_In; intuition auto. }
      1:{ destruct (String.eqb x k) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          1: constructor; auto.
          1: rewrite_map_get_put_hyp. }
    Qed.

    Lemma get_free_vars_put : forall (G : tenv) x t,
        incl (get_free_vars (map.put G x t)) (x :: get_free_vars G).
    Proof.
      unfold incl; intros.
      destruct (String.eqb a x) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
      1: constructor; auto.
      rewrite get_free_vars__map_get_Some in *. rewrite_map_get_put_hyp.
      rewrite <- get_free_vars__map_get_Some in *. auto using in_cons.
    Qed.


    Ltac use_substitute_preserve_ty_IH :=
      lazymatch goal with
        IH: context[type_of _ _ (substitute _ _ ?e) _] |- type_of _ _ (substitute _ _ ?e) _ =>
          eapply IH end.

    Ltac apply_sub_wf :=
      lazymatch goal with
        H: forall _ _, map.get _ _ = Some _ -> _, H': map.get _ _ = Some _ |- _ =>
      apply H in H' end.

    Lemma map_get_fresh_var_None : forall (G : tenv) x free_vars,
        incl (get_free_vars G) free_vars ->
        map.get G (fresh_var x free_vars) = None.
    Proof.
      intros * H; apply get_free_vars__map_get_None. intro contra.
      apply H, fresh_var_is_fresh in contra; auto.
    Qed.

    Lemma fresh_var_neq : forall x y l, y <> fresh_var x (y :: l).
    Proof.
      intros; intro contra.
      lazymatch goal with
        _: _ = fresh_var ?y ?l |- _ =>
          assert(contra' : In (fresh_var y l) l) end.
      { rewrite <- contra; constructor; auto. }
      apply fresh_var_is_fresh in contra'; auto.
    Qed.

    Lemma fresh_var_neq2 : forall x y z l, y <> fresh_var x (z :: y :: l).
    Proof.
      intros; intro contra.
      lazymatch goal with
        _: _ = fresh_var ?y ?l |- _ =>
          assert(contra' : In (fresh_var y l) l) end.
      { rewrite <- contra. right. left. auto. }
      apply fresh_var_is_fresh in contra'; auto.
    Qed.

    Ltac apply_sub_wf_with_map_incl :=
      apply_sub_wf; case_match; intuition auto;
      eapply type_of_strengthen; eauto;
      repeat apply map_incl_step_r; auto using map_incl_refl;
      apply map_get_fresh_var_None; auto; repeat apply incl_tl; auto.

    Ltac apply_incl_lemmas := eapply incl_tran; eauto using get_free_vars_put; apply incl_cons_step; auto.

    Ltac inj_constr_get_put := try do_injection; constructor; repeat rewrite_map_get_put_goal; auto.

    Lemma substitute_preserve_ty : forall e0 Gstore Genv0 Genv t0 sub free_vars,
        tenv_wf Gstore -> tenv_wf Genv0 ->
        type_of Gstore Genv0 e0 t0 ->
        sub_wf Genv0 Gstore Genv sub ->
        incl (get_free_vars Genv) free_vars ->
        type_of Gstore Genv (substitute sub free_vars e0) t0.
    Proof.
      unfold sub_wf; induction e0 using expr_IH; simpl; intros.
      all: invert_type_of.
      all: try now (econstructor; eauto).
      1: apply_sub_wf; case_match; intuition auto.
      all: try (econstructor; eauto;
                use_substitute_preserve_ty_IH; simpl; intros;
                [ | | eauto | .. ]; auto;
                [ repeat apply tenv_wf_step | ..]; eauto with fiat2_hints;
                [ | repeat apply_incl_lemmas ];
                repeat (case_match_string_eqb;
                        [ inj_constr_get_put; try apply fresh_var_neq; try apply fresh_var_neq2 | ]);
                apply_sub_wf_with_map_incl).
      1:{ econstructor; eauto.
          1: rewrite fst_map_fst; auto.
          lazymatch goal with
            H0: type_of _ _ _ _, H1: Permutation _ _, H2: NoDup _,
                  H3: Sorted.StronglySorted _ _, H4: map fst _ = _ |- _ =>
              clear H0 H1 H2 H3 H4 end.
          generalize dependent tl. induction H; simpl; intros.
          all: destruct tl; simpl in *; invert_Forall2; intuition auto.
          constructor.
          1:{ case_match; simpl in *. eapply H; eauto. }
          1: apply IHForall; auto. }
      1:{ constructor; auto.
          lazymatch goal with H: type_of _ _ _ _ |- _ => clear H end.
          induction H8; simpl; auto. constructor; invert_Forall.
          1:{ case_match; simpl in *; intuition auto.
              all: lazymatch goal with
                     H: context[type_of _ _ (substitute _ _ ?e) _] |-
                       type_of _ _ (substitute _ _ ?e) _ =>
                       eapply H end; eauto. }
          1: apply IHForall; auto. }
      1:{ econstructor; eauto;
          use_substitute_preserve_ty_IH; simpl; intros.
          3,8: eauto.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
          all: repeat apply_incl_lemmas.
          all: repeat (case_match_string_eqb;
                       [ inj_constr_get_put; try apply fresh_var_neq; try apply fresh_var_neq2 | ]);
            apply_sub_wf_with_map_incl. }
    Qed.


    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (word:=word)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Fixpoint make_sub_env (store env : locals) (sub : list (string * expr)) : locals :=
      match sub with
      | nil => map.empty
      | (x, e) :: sub => map.put (make_sub_env store env sub) x (interp_expr store env e)
      end.

    Lemma sub_lookup_Some__make_sub_env : forall x sub e (store env : locals),
        sub_lookup x sub = Some e ->
        map.get (make_sub_env store env sub) x = Some (interp_expr store env e).
    Proof.
      induction sub; simpl; intros.
      1: congruence.
      case_match; simpl in *.
      destruct_match_hyp; rewrite ?eqb_eq, ?eqb_neq in *; try do_injection; subst.
      all: rewrite_map_get_put_goal; auto.
    Qed.

    Lemma make_sub_env_wf : forall Genv0 Gstore Genv store env sub,
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        sub_wf Genv0 Gstore Genv sub ->
        locals_wf Genv0 (make_sub_env store env sub).
    Proof.
      unfold sub_wf, locals_wf; intros. apply_sub_wf.
      destruct_match_hyp; intuition auto.
      erewrite sub_lookup_Some__make_sub_env; eauto.
      eapply type_sound; eauto.
    Qed.

    Lemma make_sub_env__locals_equiv : forall Genv0 Gstore Genv store env store' env' sub,
        tenv_wf Gstore -> tenv_wf Genv ->
        sub_wf Genv0 Gstore Genv sub ->
        locals_wf Gstore store -> locals_wf Genv env ->
        locals_equiv Gstore store store' -> locals_equiv Genv env env' ->
        locals_equiv Genv0 (make_sub_env store env sub) (make_sub_env store' env' sub).
    Proof.
      unfold sub_wf; intros. unfold locals_equiv; intros. apply_sub_wf.
      destruct_match_hyp; intuition auto.
      erewrite !sub_lookup_Some__make_sub_env; eauto. f_equal.
      symmetry. eapply interp_expr__locals_equiv; [ | | eauto | .. ]; auto.
    Qed.

    Ltac use_substitute_preserve_sem_IH :=
      lazymatch goal with
        IH: context[_ = interp_expr _ _ ?e] |- context[interp_expr _ _ (substitute _ _ ?e)] =>
          erewrite IH end.

    Lemma substitute_preserve_sem : forall e0 Gstore Genv0 Genv t0 sub free_vars store env,
        tenv_wf Genv0 -> tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv0 e0 t0 ->
        sub_wf Genv0 Gstore Genv sub ->
        incl (get_free_vars Genv) free_vars ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env (substitute sub free_vars e0) = interp_expr store (make_sub_env store env sub) e0.
    Proof.
      unfold sub_wf. induction e0 using expr_IH; simpl; auto; intros.
      all: invert_type_of.
      all: try now (repeat (use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto)).
      1:{ apply_sub_wf. unfold get_local. destruct_match_hyp; simpl; intuition auto.
          erewrite sub_lookup_Some__make_sub_env; eauto. }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; auto.
          6:{ eapply locals_wf_step; eauto. eapply type_sound;
              [ eapply substitute_preserve_ty | .. ]; [ | | eauto | .. ]; eauto. }
          all: eauto with fiat2_hints.
          all: [> | simpl; intros; case_match_string_eqb;
                    [ inj_constr_get_put | apply_sub_wf_with_map_incl ]
               | repeat apply_incl_lemmas ].
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          eapply interp_expr__locals_equiv; [ | | eauto | .. ]; eauto using locals_equiv_refl with fiat2_hints.
          1:{ apply locals_wf_step; [ | eapply type_sound; eauto ].
              all: eapply make_sub_env_wf; [ | | | | eauto ]; auto. }
          1:{ apply locals_equiv_step;
              [ eapply make_sub_env__locals_equiv; [ | | eauto | .. ];
                auto using locals_equiv_refl, locals_equiv__put_fresh, map_get_fresh_var_None
              | simpl; unfold get_local; rewrite_map_get_put_goal; auto ]. } }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ].
          invert_type_of_value. f_equal.
          apply In_flat_map_ext; intros; apply_Forall_In.
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
          8: eapply locals_wf_step; eauto.
          all: eauto with fiat2_hints.
          all: [> | simpl; intros; case_match_string_eqb;
                    [ inj_constr_get_put | apply_sub_wf_with_map_incl ]
               | repeat apply_incl_lemmas ].
          erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; eauto using locals_equiv_refl with fiat2_hints;
            [ apply locals_wf_step; auto; eapply make_sub_env_wf; [ | | | | eauto ]; auto
            | apply locals_equiv_step;
              [ eapply make_sub_env__locals_equiv; [ | | eauto | .. ];
                auto using locals_equiv_refl, locals_equiv__put_fresh, map_get_fresh_var_None
              | simpl; unfold get_local; rewrite_map_get_put_goal; auto ] ]. }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ].
          invert_type_of_value.
          revert IHe0_3. use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto; intros.
          eapply In_fold_right_ext with (P:=fun v => type_of_value v t0).
          1: eapply type_sound; eauto; eapply make_sub_env_wf; [ | | | | eauto ]; auto.
          intros. apply_Forall_In.
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
          8: repeat eapply locals_wf_step; eauto.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
          all: [> | repeat (simpl; intros; case_match_string_eqb;
                            [ inj_constr_get_put; try apply fresh_var_neq | try apply_sub_wf_with_map_incl ])
               | repeat apply_incl_lemmas ].
          erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; intuition auto.
          1: eapply type_sound; eauto.
          all: repeat apply tenv_wf_step; repeat apply locals_wf_step;
            eauto using locals_equiv_refl with fiat2_hints.
          all: try (eapply make_sub_env_wf; [ | | | | eauto ]; auto).
          repeat apply locals_equiv_step.
          2,3: simpl; unfold get_local; repeat rewrite_map_get_put_goal; auto using fresh_var_neq.
          eapply make_sub_env__locals_equiv; [ | | eauto | .. ]; auto using locals_equiv_refl.
          repeat eapply locals_equiv_tran, locals_equiv__put_fresh, map_get_fresh_var_None.
          all: auto using locals_equiv_refl, incl_tl. }
      1:{ do 2 f_equal. lazymatch goal with
          H1: type_of _ _ _ _, H2: List.map fst _ = _, H3: Permutation _ _, H4: NoDup _, H5: Sorted.StronglySorted _ _ |- _ =>
            clear H1 H2 H3 H4 H5 end.
          generalize dependent tl; induction l; simpl; auto; intros. invert_Forall; invert_Forall2.
          case_match. destruct tl; try discriminate; simpl in *.
          lazymatch goal with H: _ :: _ = _ :: _ |- _ => inversion H; subst end. erewrite IHl; eauto.
          do 2 f_equal. eauto. }
      1:{ do 3 f_equal. rewrite map_map. apply map_ext_in; intros.
          case_match. repeat apply_Forall_In; simpl in *. intuition auto.
          f_equal; eauto. }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ].
          invert_type_of_value.
          1: use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto with fiat2_hints.
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
          8: repeat eapply locals_wf_step; eauto.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
          all: [> | repeat (simpl; intros; case_match_string_eqb;
                            [ inj_constr_get_put; try apply fresh_var_neq | try apply_sub_wf_with_map_incl ])
               | repeat apply_incl_lemmas ].
          erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; eauto using locals_equiv_refl with fiat2_hints;
            [ apply locals_wf_step; auto; eapply make_sub_env_wf; [ | | | | eauto ]; auto
            | apply locals_equiv_step;
              [ eapply make_sub_env__locals_equiv; [ | | eauto | .. ];
                auto using locals_equiv_refl, locals_equiv__put_fresh, map_get_fresh_var_None
              | simpl; unfold get_local; rewrite_map_get_put_goal; auto ] ]. }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ].
          invert_type_of_value.
          revert IHe0_3. use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto; intros.
          apply In_fold_right_ext with (P:=fun v => type_of_value v t0); intros.
          1: eapply type_sound; eauto; eapply make_sub_env_wf; [ .. | eauto ]; auto.
          apply_Forall_In. use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
          8: repeat eapply locals_wf_step; eauto.
          8,9: intuition eauto.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
          all: [> | repeat (simpl; intros; case_match_string_eqb;
                            [ inj_constr_get_put; try apply fresh_var_neq; try apply fresh_var_neq2
                            | try apply_sub_wf_with_map_incl ])
               | repeat apply_incl_lemmas ].
          erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; intuition auto.
          1: eapply type_sound; eauto.
          all: repeat apply tenv_wf_step; repeat apply locals_wf_step;
            eauto using locals_equiv_refl with fiat2_hints.
          all: try (eapply make_sub_env_wf; [ | | | | eauto ]; auto).
          repeat apply locals_equiv_step.
          2-4: simpl; unfold get_local; repeat rewrite_map_get_put_goal; auto using fresh_var_neq, fresh_var_neq2.
          eapply make_sub_env__locals_equiv; [ | | eauto | .. ]; auto using locals_equiv_refl.
          repeat eapply locals_equiv_tran, locals_equiv__put_fresh, map_get_fresh_var_None.
          all: auto using locals_equiv_refl, incl_tl. }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ].
          invert_type_of_value. f_equal.
          apply In_filter_ext; intros. apply_Forall_In.
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
          8: repeat eapply locals_wf_step; eauto.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
          all: [> | repeat (simpl; intros; case_match_string_eqb;
                            [ inj_constr_get_put; try apply fresh_var_neq | try apply_sub_wf_with_map_incl ])
               | repeat apply_incl_lemmas ].
          erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; eauto using locals_equiv_refl with fiat2_hints;
            [ apply locals_wf_step; auto; eapply make_sub_env_wf; [ | | | | eauto ]; auto
            | apply locals_equiv_step;
              [ eapply make_sub_env__locals_equiv; [ | | eauto | .. ];
                auto using locals_equiv_refl, locals_equiv__put_fresh, map_get_fresh_var_None
              | simpl; unfold get_local; rewrite_map_get_put_goal; auto ] ]. }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ];
            invert_type_of_value.
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_2; eauto; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ];
            invert_type_of_value.
          f_equal. apply In_flat_map_ext; intros. apply_Forall_In.
          erewrite In_filter_ext; [ apply map_ext_in | ]; simpl; intros.
          1:{ lazymatch goal with H: In _ (filter _ _) |- _ => apply filter_In in H; intuition auto end.
              apply_Forall_In.
              use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
              8: repeat eapply locals_wf_step; eauto.
              all: repeat apply tenv_wf_step; eauto with fiat2_hints.
              all: [> | repeat (simpl; intros; case_match_string_eqb;
                                [ inj_constr_get_put; try apply fresh_var_neq | try apply_sub_wf_with_map_incl ])
                   | repeat apply_incl_lemmas ].
              erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; eauto using locals_equiv_refl;
                [ repeat apply tenv_wf_step; eauto with fiat2_hints
                | repeat apply locals_wf_step; auto; eapply make_sub_env_wf; [ | | | | eauto ]; auto | ].
              repeat apply locals_equiv_step.
              2,3: simpl; unfold get_local; repeat rewrite_map_get_put_goal; auto using fresh_var_neq.
              eapply make_sub_env__locals_equiv; [ | | eauto | .. ]; auto using locals_equiv_refl.
              repeat eapply locals_equiv_tran, locals_equiv__put_fresh, map_get_fresh_var_None.
              all: auto using locals_equiv_refl, incl_tl. }
          1:{ apply_Forall_In. use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
              8: repeat eapply locals_wf_step; eauto.
              all: repeat apply tenv_wf_step; eauto with fiat2_hints.
              all: [> | repeat (simpl; intros; case_match_string_eqb;
                                [ inj_constr_get_put; try apply fresh_var_neq | try apply_sub_wf_with_map_incl ])
                   | repeat apply_incl_lemmas ].
              erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; eauto using locals_equiv_refl;
                [ repeat apply tenv_wf_step; eauto with fiat2_hints
                | repeat apply locals_wf_step; auto; eapply make_sub_env_wf; [ | | | | eauto ]; auto | ].
              repeat apply locals_equiv_step.
              2,3: simpl; unfold get_local; repeat rewrite_map_get_put_goal; auto using fresh_var_neq.
              eapply make_sub_env__locals_equiv; [ | | eauto | .. ]; auto using locals_equiv_refl.
              repeat eapply locals_equiv_tran, locals_equiv__put_fresh, map_get_fresh_var_None.
              all: auto using locals_equiv_refl, incl_tl. } }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ];
            invert_type_of_value.
          f_equal. apply map_ext_in; intros; apply_Forall_In.
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
          8: repeat eapply locals_wf_step; eauto.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
          all: [> | repeat (simpl; intros; case_match_string_eqb;
                            [ inj_constr_get_put; try apply fresh_var_neq | try apply_sub_wf_with_map_incl ])
               | repeat apply_incl_lemmas ].
          erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; eauto using locals_equiv_refl with fiat2_hints;
            [ apply locals_wf_step; auto; eapply make_sub_env_wf; [ | | | | eauto ]; auto
            | apply locals_equiv_step;
              [ eapply make_sub_env__locals_equiv; [ | | eauto | .. ];
                auto using locals_equiv_refl, locals_equiv__put_fresh, map_get_fresh_var_None
              | simpl; unfold get_local; rewrite_map_get_put_goal; auto ] ]. }
    Qed.
End WithMap.
