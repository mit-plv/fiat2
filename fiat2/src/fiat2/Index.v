Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.Examples fiat2.TypeSystem fiat2.TypeSound.
Require Import List String ZArith Permutation.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Import ResultMonadNotations.
Require Import Sorted.
Require Import coqutil.Map.SortedListString.
Require Import Ltac2.Ltac2 Ltac2.Control Ltac2.Constr.

Set Default Proof Mode "Classic".

Local Ltac iter_hyps tac :=
  let iter := ltac2:(tac |- List.iter (fun (h, _ , t) =>
                             ltac1:(h t tac|- tac h t)
                                     (Ltac1.of_constr (Unsafe.make (Unsafe.Var h)))
                                     (Ltac1.of_constr t)
                                     tac)
                              (hyps ())) in
  iter tac.

Local Ltac rewrite_hyp_l h t :=
  try lazymatch t with
    | _ = _ => rewrite <- h in *
    end.

Section fold_command.
  Context (f : command -> command).
  Context (g : expr -> expr).

  Fixpoint fold_command (c : command) : command :=
    f
      match c with
      | CSkip => CSkip
      | CSeq c1 c2 => CSeq (fold_command c1) (fold_command c2)
      | CLet e x c => CLet (fold_expr g e) x (fold_command c)
      | CLetMut e x c => CLetMut (fold_expr g e) x (fold_command c)
      | CAssign x e => CAssign x (fold_expr g e)
      | CIf e c1 c2 => CIf (fold_expr g e) (fold_command c1) (fold_command c2)
      | CForeach e x c => CForeach (fold_expr g e) x (fold_command c)
      end.
End fold_command.

(* Materialize tbl (expected to be a list of records) into an index over attr *)
Definition list_to_idx (attr : string) (tbl : expr) : expr :=
  EFold tbl (EDict nil) "tup" "acc"
    (EInsert (EVar "acc") (EAccess (EVar "tup") attr)
       (EBinop OCons (EVar "tup")
          (EOptMatch (ELookup (EVar "acc") (EAccess (EVar "tup") attr))
             (EAtom (ANil None))
             "x"%string (EVar "x")))).

(* Inverse of tbl_to_idx, expecting idx to be a dict
   Require the index keys in idx to match the attr values in the records *)
Definition idx_to_list (idx : expr) : expr :=
  EDictFold idx (EAtom (ANil None)) "k" "v" "acc" (EBinop OConcat (EVar "v") (EVar "acc")).

Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Local Notation value := (value (word := word)).

  Section WithMap.
    Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    Definition gallina_list_to_idx attr (l : list value) :=
      fold_right
        (fun v acc => match v with
                      | VRecord v => dict_insert (record_proj attr v)
                                       (match dict_lookup (record_proj attr v) acc with
                                        | Some l' => match l' with
                                                     | VList l' => VList (VRecord v :: l')
                                                     | _ => VUnit
                                                     end
                                        | _ => VList (VRecord v :: nil)
                                        end) acc
           | _ => nil
           end) nil l.

    Definition gallina_idx_to_list (d : list (value * value)) :=
      fold_right
        (fun v acc => match snd v with
                      | VList v => app v acc
                      | _ => nil
                      end)
        nil d.

    Lemma fiat2_gallina_list_to_idx : forall (Gstore Genv : tenv) (store env : locals) tbl attr l rt,
        type_of Gstore Genv tbl (TList (TRecord rt)) ->
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        In attr (List.map fst rt) ->
        interp_expr store env tbl = VList l ->
        interp_expr store env (list_to_idx attr tbl) = VDict (gallina_list_to_idx attr l).
    Proof.
      intros. simpl. rewrite H5. eapply type_sound in H; eauto; subst.
      rewrite H5 in H; clear tbl H5.
      erewrite In_fold_right_ext with (P := fun v => match v with VDict _ => True | _ => False end)
                                      (g := (fun x y =>
                                               match x, y with
                                               | VRecord l1, VDict l0 =>
                                                   VDict
                                                     (dict_insert (record_proj attr l1)
                                                        match
                                                          match dict_lookup (record_proj attr l1) l0 with
                                                          | Some v =>
                                                              v
                                                          | None => VList nil
                                                          end
                                                        with
                                                        | VList l2 => VList (VRecord l1 :: l2)
                                                        | _ => VUnit
                                                        end l0)
                                               | _ , _=> VUnit
                                               end)).
      3:{
        intros.
        unfold get_local; rewrite !map.get_put_same.
        rewrite !map.get_put_diff by congruence. rewrite !map.get_put_same.
        destruct a; intuition.
        inversion H; subst. eapply List.Forall_In in H9; eauto.
        inversion H9; subst.
        destruct (dict_lookup (record_proj attr l1) l0); try reflexivity.
        rewrite !map.get_put_same. reflexivity.
      }
      2: trivial.
      induction l; simpl; auto.
      inversion H; subst. inversion H7; subst. inversion H8; subst.
      rewrite IHl.
      2:{ constructor; auto. }
      f_equal. f_equal.
      destruct (dict_lookup (record_proj attr l0) (gallina_list_to_idx attr l)); auto.
    Qed.

    Lemma fiat2_gallina_idx_to_list : forall (Gstore Genv : tenv) (store env : locals) idx l kt t,
        type_of Gstore Genv idx (TDict kt (TList t)) ->
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env idx = VDict l ->
        interp_expr store env (idx_to_list idx) = VList (gallina_idx_to_list l).
    Proof.
      intros. simpl. eapply type_sound in H; eauto.
      rewrite H4 in *. inversion H; subst. clear H4 idx.
      erewrite In_fold_right_ext with (P := fun v => match v with VList _ => True | _ => False end)
                                      (g := fun b a => match snd b with
                                                       | VList a0 => match a with
                                                                     | VList b0 => VList (a0 ++ b0)
                                                                     | _ => VUnit
                                                                     end
                                                       | _ => VUnit
                                                       end).
      3:{ intros. unfold get_local; rewrite !map.get_put_same.
          rewrite !map.get_put_diff by congruence. rewrite !map.get_put_same.
          eapply List.Forall_In in H10; eauto; intuition.
          inversion H7; subst. destruct a; intuition.
      }
      2: trivial.
      induction l; simpl; auto. simpl in *; inversion H10; inversion H11; inversion H12; subst.
      rewrite IHl; auto.
      2: constructor; auto.
      intuition. inversion H5; subst. reflexivity.
    Qed.

    Fixpoint concat_VList (l : list value) :=
      match l with
      | VList l' :: l => app l' (concat_VList l)
      | _ => nil
      end.

    Local Coercion is_true : bool >-> Sortclass.

    Lemma dict_lookup_Lt : forall d k,
        StronglySorted dict_entry_leb d ->
        (forall p, In p d -> value_compare k (fst p) = Lt) ->
        dict_lookup (word:=word) k d = None.
    Proof.
      intros. induction d; auto.
      simpl. destruct a; simpl in *.
      destruct (value_eqb k v) eqn:E.
      - unfold value_eqb in *. pose proof (H0 (v, v0)).
        intuition; simpl in *. rewrite H1 in E; discriminate.
      - apply IHd; inversion H; auto.
    Qed.

    Lemma dict_insert_lookup_Permutation :
      forall k d v, Forall (fun v => match snd v with VList _ => True | _ => False end) d ->
                    StronglySorted dict_entry_leb d ->
                    Permutation
                      (concat_VList
                         (List.map snd
                            (dict_insert k
                               match dict_lookup k d with
                               | Some (VList l) => VList (v :: l)
                               | None => VList (v :: nil)
                               | _ => VUnit
                               end d)))
                      (v :: (concat_VList (List.map snd d))).
    Proof.
      intros. induction d; simpl; auto.
      destruct a; simpl. inversion H; subst; simpl in *. destruct v1; intuition.
      unfold value_eqb, value_ltb. destruct (value_compare k v0) eqn:E; simpl; auto.
      - inversion H0; subst. rewrite dict_lookup_Lt; auto. intros p H_in.
        eapply List.Forall_In in H7; eauto. unfold dict_entry_leb, value_leb, leb_from_compare in H7; simpl in H7.
        destruct (value_compare v0 (fst p)) eqn:E'; try congruence.
        + apply value_compare_Eq_eq in E'; subst; auto.
        + eapply value_compare_trans; eauto.
      - assert (forall xl v yl, Permutation xl (v :: yl) -> Permutation (l ++ xl) (v :: l ++ yl)).
        { clear. intros. replace (v :: l ++ yl) with ((v :: nil) ++ l ++ yl); auto.
          eapply perm_trans.
          2: eapply Permutation_app_swap_app. simpl.
          apply Permutation_app; auto. }
        apply H2; apply H1; inversion H0; auto.
    Qed.

    Lemma dict_lookup_VList : forall k l,
        Forall (fun p => match snd p with VList _ => True | _ => False end) l ->
        match dict_lookup (word:=word) k l with Some (VList _) | None => True | _ => False end.
    Proof.
      intros; induction l; simpl; auto.
      destruct a. destruct (value_eqb k v); auto.
      - inversion H; subst; auto.
      - apply IHl. inversion H; intuition.
    Qed.

    Lemma gallina_list_to_idx_VList : forall l attr rt,
        Forall (fun v => type_of_value v (TRecord rt)) l ->
        In attr (List.map fst rt) ->
        Forall (fun p => match snd p with VList _ => True | _ => False end) (gallina_list_to_idx attr l).
    Proof.
      intros; induction l; simpl; auto.
      inversion H; subst. inversion H3; subst.
      rewrite Forall_forall; intros x H_in. apply dict_insert_incl in H_in.
      inversion H_in; subst; simpl.
      - apply IHl in H4. eapply dict_lookup_VList with (k:=(record_proj attr l0)) in H4.
        lazymatch goal with |- context[dict_lookup ?k ?d] => destruct (dict_lookup k d) end; intuition. destruct v; intuition.
      - apply IHl in H4. rewrite Forall_forall in H4. apply H4; auto.
    Qed.

    Lemma dict_insert_preserve_SSorted : forall d k v,
        StronglySorted (dict_entry_leb (word:=word)) d ->
        StronglySorted dict_entry_leb (dict_insert k v d).
    Proof.
      induction d; intros; simpl.
      - repeat constructor.
      - destruct a. inversion H; subst. unfold value_ltb, value_eqb. destruct (value_compare k v0) eqn:E.
        + constructor; auto. rewrite Forall_forall in *.
          unfold dict_entry_leb in *; simpl in *. apply value_compare_Eq_eq in E; subst; auto.
        + constructor; auto. rewrite Forall_forall in *; intros. destruct x.
          unfold dict_entry_leb, value_leb, leb_from_compare in *; simpl in *.
          destruct H0.
          * inversion H0; subst; rewrite E; auto.
          * apply H3 in H0; simpl in H0. destruct (value_compare v0 v2) eqn:E'; intuition.
            1: { apply value_compare_Eq_eq in E'; subst; rewrite E; trivial. }
            erewrite value_compare_trans; eauto.
        + constructor; auto. rewrite Forall_forall; intros x H_in.
          apply dict_insert_incl in H_in.
          unfold dict_entry_leb, value_leb, leb_from_compare in *; simpl in *.
          inversion H_in; subst.
          * simpl. rewrite value_compare_antisym. rewrite E. auto.
          * eapply List.Forall_In in H3; eauto.
    Qed.

    Lemma gallina_list_to_idx_SSorted : forall l attr rt,
        Forall (fun v => type_of_value v (TRecord rt)) l ->
        In attr (List.map fst rt) ->
        StronglySorted dict_entry_leb (gallina_list_to_idx attr l).
    Proof.
      intros; induction l; simpl; try constructor.
      inversion H; subst. inversion H3; subst.
      apply dict_insert_preserve_SSorted; auto.
    Qed.

    Lemma gallina_list_to_idx_Permutation : forall attr l rt,
        Forall (fun v => type_of_value v (TRecord rt)) l ->
        In attr (List.map fst rt) ->
        Permutation (concat_VList (List.map snd (gallina_list_to_idx attr l))) l.
    Proof.
      intros. induction H; intuition.
      simpl in *. inversion H; subst. eapply perm_trans.
      - eapply dict_insert_lookup_Permutation.
        + eapply gallina_list_to_idx_VList; eauto.
        + eapply gallina_list_to_idx_SSorted; eauto.
      - constructor; auto.
    Qed.

    Lemma gallina_list_to_idx_to_list : forall attr l rt ,
        Forall (fun v => type_of_value v (TRecord rt)) l ->
        In attr (List.map fst rt) ->
        Permutation (gallina_idx_to_list (gallina_list_to_idx attr l)) l.
    Proof.
      intros.
      assert (forall l, Forall (fun v => match snd v with VList _ => True | _ => False end) l -> gallina_idx_to_list l = concat_VList (List.map snd l)).
      { induction l0; simpl; intros; auto. inversion H1; subst. destruct (snd a); intuition. congruence. }
      pose proof (gallina_list_to_idx_Permutation _ _ _ H H0). rewrite <- H1 in H2; auto.
      revert H H0; clear. intro; rewrite Forall_forall. induction l; simpl; intros.
      - intuition.
      - inversion H; subst. inversion H4; subst.
        apply dict_insert_incl in H1 as H1'; inversion H1'; subst.
        2: apply IHl; auto.
        simpl. destruct (dict_lookup (record_proj attr l0) (gallina_list_to_idx attr l)) eqn:E; intuition.
        destruct v; intuition. all: eapply gallina_list_to_idx_VList with (l:=l) in H0; eauto; intuition; eapply dict_lookup_VList in H0; erewrite E in H0; intuition.
    Qed.

    Lemma In_access_record : forall A l attr, In attr (List.map fst l) -> exists (x : A), access_record l attr = Success x.
    Proof.
      induction l; simpl; intros.
      - intuition.
      - destruct a; simpl in *. destruct (eqb attr s) eqn:E.
        + exists a. reflexivity.
        + rewrite eqb_neq in *. intuition. congruence.
    Qed.

    Lemma fiat2_gallina_list_to_idx_to_list : forall (Gstore Genv : tenv) (store env : locals) l attr tbl rt,
        type_of Gstore Genv tbl (TList (TRecord rt)) ->
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        In attr (List.map fst rt) ->
        interp_expr store env tbl = VList l ->
        interp_expr store env (idx_to_list (list_to_idx attr tbl)) =
          VList (gallina_idx_to_list (gallina_list_to_idx attr l)).
    Proof.
      intros.
      apply In_access_record in H4 as Ht.
      destruct Ht as [t Ht].
      intros. eapply fiat2_gallina_idx_to_list with (Gstore:=Gstore) (kt:=t); eauto.
      2:{ eapply fiat2_gallina_list_to_idx with (Gstore:=Gstore); eauto. }
      apply type_of__type_wf in H as H_wf; auto. inversion H_wf; subst. inversion H7; subst.
      repeat (try econstructor; try erewrite map.get_put_same; try erewrite map.get_put_diff; try congruence; eauto).
      eapply Forall_access_record; eauto.
    Qed.

    Lemma list_to_idx_to_list :
      forall attr tbl (Gstore Genv : tenv) (store env : locals) rt,
        type_of Gstore Genv tbl (TList (TRecord rt)) ->
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        In attr (List.map fst rt) ->
        exists l l', interp_expr store env (idx_to_list (list_to_idx attr tbl)) = VList l /\
                       interp_expr store env tbl = VList l' /\
                       Permutation l l'.
    Proof.
      intros. eapply type_sound in H as H'; eauto. inversion H'; subst. symmetry in H5.
      eapply fiat2_gallina_list_to_idx_to_list with (attr:=attr) in H5 as H5'; eauto. repeat eexists; eauto.
      eapply gallina_list_to_idx_to_list; eauto.
    Qed.

    Lemma Permutation_SSorted_eq : forall l l',
        Permutation l l' ->
        StronglySorted (value_leb (word:=word)) l ->
        StronglySorted value_leb l' ->
        l = l'.
    Proof.
      induction l; intros l' H H_sort H_sort'.
      - apply Permutation_nil in H; congruence.
      - destruct l'.
        1: apply Permutation_sym, Permutation_nil in H; discriminate.
        inversion H_sort; inversion H_sort'; subst.
        apply Permutation_in with (x:=a) in H as H_in; intuition.
        apply Permutation_sym in H as H'.
        apply Permutation_in with (x:=v) in H' as H_in'; intuition.
        inversion H_in; inversion H_in'; subst.
        1-3: f_equal; apply IHl; auto; eapply Permutation_cons_inv; eauto.
        eapply List.Forall_In in H3, H7; eauto.
        apply value_leb_antisym in H3; auto; subst. f_equal.
        apply IHl; auto. eapply Permutation_cons_inv; eauto.
    Qed.

    Lemma ESort_Permutation_inv : forall (store env : locals) l l' vl vl',
        interp_expr store env l = VList vl ->
        interp_expr store env l' = VList vl' ->
        Permutation vl vl' ->
        interp_expr store env (ESort l) = interp_expr store env (ESort l').
    Proof.
      intros store env l l' vl vl' E E' H. simpl.
      rewrite E, E'. f_equal.
      apply Permutation_SSorted_eq.
      2,3: apply StronglySorted_value_sort.
      eapply perm_trans. 2:apply Permuted_value_sort.
      eapply perm_trans. 2:apply H.
      apply Permutation_sym, Permuted_value_sort.
    Qed.

    Lemma list_to_idx_preserve_ty : forall Gstore Genv tbl rt attr,
        tenv_wf Gstore -> tenv_wf Genv ->
        In attr (List.map fst rt) ->
        type_of Gstore Genv tbl (TList (TRecord rt)) ->
        type_of Gstore Genv (list_to_idx attr tbl) (TDict (get_attr_type rt attr) (TList (TRecord rt))).
    Proof.
      intros. eapply type_of__type_wf in H2 as H_wf; auto. inversion H_wf; subst.
      inversion H4; subst. repeat econstructor; eauto.
      all: repeat (try rewrite map.get_put_same; try rewrite map.get_put_diff; try congruence); eauto.
      all: unfold get_attr_type; apply In_access_record in H1 as [t Ht]; rewrite Ht; auto.
      apply access_record_sound in Ht. apply in_map with (f:=snd) in Ht. eapply List.Forall_In in H7; eauto.
    Qed.

    Lemma idx_to_list_preserve_ty : forall Gstore Genv idx kt t,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv idx (TDict kt (TList t)) ->
        type_of Gstore Genv (idx_to_list idx) (TList t).
    Proof.
      intros. eapply type_of__type_wf in H1 as H_wf; auto. inversion H_wf; subst. inversion H5; subst.
      repeat econstructor; eauto.
      all: repeat (try rewrite map.get_put_same; try rewrite map.get_put_diff; try congruence).
      Qed.

    Definition idx_read_to_list_read (tbl : string) (e : expr) :=
      match e with
      | ELoc tbl' => if String.eqb tbl tbl'
                     then idx_to_list (ELoc tbl)
                     else e
      | _ => e
      end.

    Definition list_write_to_idx_write (tbl attr : string) (c : command) :=
      match c with
      | CAssign tbl' e =>
          if String.eqb tbl tbl'
          then CAssign tbl (list_to_idx attr e)
          else c
      | _ => c
      end.

    Section __.
      Context (tbl attr : string).

      (* is_inv stands for whether the context is invariant to Permutations of the current expr's output *)
      Definition unop_is_inv (is_inv : bool) (o : unop) : bool :=
        match o with
        | OLength => true
        | _ => false
        end.

      Definition binop_is_inv (is_inv : bool) (o : binop) : bool * bool :=
        match o with
        | OCons => (false, is_inv)
        | _ => (false, false)
        end.

      Fixpoint can_transf_to_idx'' (is_inv : bool) (e : expr) : bool :=
        match e with
        | EVar _ | EAtom _ => true
        | ELoc x => negb (String.eqb x tbl) || is_inv
        | EUnop o e => can_transf_to_idx'' (unop_is_inv is_inv o) e
        | EBinop o e1 e2 => let '(b1, b2) := binop_is_inv is_inv o in
                            can_transf_to_idx'' b1 e1 && can_transf_to_idx'' b2 e2
        | EIf e1 e2 e3 => can_transf_to_idx'' false e1 && can_transf_to_idx'' is_inv e2 && can_transf_to_idx'' is_inv e3
        | ELet e1 x e2 => can_transf_to_idx'' false e1 && can_transf_to_idx'' is_inv e2
        | EFlatmap e1 x e2 => can_transf_to_idx'' is_inv e1 && can_transf_to_idx'' is_inv e2
        | EFold e1 e2 x y e3 => can_transf_to_idx'' false e1 && can_transf_to_idx'' false e2 && can_transf_to_idx'' false e3
        | ERecord l => forallb (fun p => can_transf_to_idx'' false (snd p)) l
        | EAccess e s => can_transf_to_idx'' false e
        | EDict l => forallb (fun p => (can_transf_to_idx'' false (fst p) && can_transf_to_idx'' false (snd p))%bool) l
        | EInsert d k v => can_transf_to_idx'' false d && can_transf_to_idx'' false k && can_transf_to_idx'' false v
        | EDelete d k => can_transf_to_idx'' false d && can_transf_to_idx'' false k
        | ELookup d k => can_transf_to_idx'' false d && can_transf_to_idx'' false k
        | EOptMatch e e_none x e_some => can_transf_to_idx'' false e && can_transf_to_idx'' is_inv e_none && can_transf_to_idx'' is_inv e_some
        | EDictFold d e0 k v acc e => can_transf_to_idx'' false d && can_transf_to_idx'' false e0 && can_transf_to_idx'' false e
        | ESort l => can_transf_to_idx'' true l
        | EFilter l x p => can_transf_to_idx'' is_inv l && can_transf_to_idx'' false p
        | EJoin l1 l2 x1 x2 p r => can_transf_to_idx'' is_inv l1 && can_transf_to_idx'' is_inv l2 && can_transf_to_idx'' false p && can_transf_to_idx'' false r
        | EProj l x r => can_transf_to_idx'' is_inv l && can_transf_to_idx'' false r
        end.

      Fixpoint can_transf_to_idx' (c : command) : bool :=
        match c with
        | CSkip => true
        | CSeq c1 c2 => can_transf_to_idx' c1 && can_transf_to_idx' c2
        | CLet e x c => can_transf_to_idx'' false e && can_transf_to_idx' c
        | CLetMut e x c => negb (String.eqb x tbl) && can_transf_to_idx'' false e && can_transf_to_idx' c
        | CAssign x e => can_transf_to_idx'' false e
        | CIf e c1 c2 => can_transf_to_idx'' false e && can_transf_to_idx' c1 && can_transf_to_idx' c2
        | CForeach e x c => can_transf_to_idx'' false e && can_transf_to_idx' c
        end.

      Definition can_transf_to_idx (c : command) : bool :=
        match c with
        | CLetMut (EAtom (ANil (Some (TRecord rt)))) x c =>
            String.eqb x tbl &&
              inb String.eqb attr (List.map fst rt) &&
              can_transf_to_idx' c
        | _ => false
        end.
    End __.

    Definition transf_to_idx' (tbl attr : string) (c : command) : command :=
      fold_command (list_write_to_idx_write tbl attr) (idx_read_to_list_read tbl) c.

    Definition transf_to_idx (tbl attr : string) (c : command) : command :=
      match c with
      | CLetMut (EAtom (ANil _)) tbl' c =>
          CLetMut (EDict nil) tbl (* Rely on can_transf_to_idx to check tbl' = tbl *)
            (transf_to_idx' tbl attr c)
      | _ => c
      end.

    Create HintDb fiat2_hints.

    Local Ltac invert_type_wf :=
      lazymatch goal with
      | H: type_wf (TList ?t) |- type_wf ?t => inversion H; clear H; subst
      | H: type_wf (TOption ?t) |- type_wf ?t => inversion H; clear H; subst
      | H: type_wf (TDict ?t _) |- type_wf ?t => inversion H; clear H; subst
      | H: type_wf (TDict _ ?t) |- type_wf ?t => inversion H; clear H; subst
      | H: type_wf (TRecord ?tl) |- Forall type_wf (List.map snd ?tl) => inversion H; clear H; subst
      end.

    Lemma invert_TList_wf: forall t, type_wf (TList t) -> type_wf t.
    Proof.
      intros. invert_type_wf; auto.
    Qed.

    Lemma invert_TOption_wf: forall t, type_wf (TOption t) -> type_wf t.
    Proof.
      intros. invert_type_wf; auto.
    Qed.

    Lemma invert_TDict_wf_l: forall kt vt, type_wf (TDict kt vt) -> type_wf kt.
    Proof.
      intros. invert_type_wf; auto.
    Qed.

    Lemma invert_TDict_wf_r: forall kt vt, type_wf (TDict kt vt) -> type_wf vt.
    Proof.
      intros. invert_type_wf; auto.
    Qed.

    Lemma invert_TRecord_wf: forall tl, type_wf (TRecord tl) -> Forall type_wf (List.map snd tl).
    Proof.
      intros. invert_type_wf; auto.
    Qed.

    Hint Resolve invert_TList_wf : fiat2_hints.
    Hint Resolve invert_TOption_wf : fiat2_hints.
    Hint Resolve invert_TDict_wf_l : fiat2_hints.
    Hint Resolve invert_TDict_wf_r : fiat2_hints.
    Hint Resolve invert_TRecord_wf : fiat2_hints.
(*
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

    Lemma type_of_TList__type_wf : forall Gstore Genv e t,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e (TList t) -> type_wf t.
    Proof.
      intros; apply_type_of__type_wf; auto with fiat2_hints.
    Qed.

    Lemma type_of_TOption__type_wf : forall Gstore Genv e t,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e (TOption t) -> type_wf t.
    Proof.
      intros; apply_type_of__type_wf; auto with fiat2_hints.
    Qed.

    Lemma type_of_TDict__type_wf_l : forall Gstore Genv e kt vt,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e (TDict kt vt) -> type_wf kt.
    Proof.
      intros; apply_type_of__type_wf; eauto with fiat2_hints.
    Qed.

    Lemma type_of_TDict__type_wf_r : forall Gstore Genv e kt vt,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e (TDict kt vt) -> type_wf vt.
    Proof.
      intros; apply_type_of__type_wf; eauto with fiat2_hints.
    Qed.

    Lemma type_of_TRecord__type_wf : forall Gstore Genv e tl,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e (TRecord tl) -> Forall type_wf (List.map snd tl).
    Proof.
      intros. apply_type_of__type_wf. auto with fiat2_hints.
    Qed.
*)
    Hint Resolve type_of__type_wf : fiat2_hints.


    Local Ltac destruct_match :=
      match goal with
      | H: context[match ?x with _ => _ end] |- _ =>
          let E := fresh "E" in
          destruct x eqn:E
      end.

    Lemma locals_eq_update : forall (l l' : locals) x v,
        (forall y, x <> y -> map.get l y = map.get l' y) ->
        map.update l x v = map.update l' x v.
    Proof.
      intros * H. apply map.map_ext. intro y. destruct (String.eqb x y) eqn:E.
      - rewrite eqb_eq in E; subst. repeat rewrite Properties.map.get_update_same; trivial.
      - rewrite eqb_neq in E. repeat rewrite Properties.map.get_update_diff; auto.
    Qed.

    Definition locals_eq_except (x : string) (l l' : locals) :=
      forall y, x <> y -> map.get l y = map.get l' y.

    Definition locals_equiv_idx_list_at (x attr : string) (l l' : locals) :=
      match map.get l x with
      | Some (VDict v) =>
          match map.get l' x with
          | Some (VList v') => v = gallina_list_to_idx attr v'
          | _ => False
          end
      | _ => False
      end.

    Definition tenv_eq_except (x : string) (G G' : tenv) :=
      forall y, x <> y -> map.get G y = map.get G' y.

    Definition tenv_equiv_idx_list_at (x attr : string) (G G' : tenv) :=
      match map.get G x with
      | Some (TDict kt vt) =>
          match map.get G' x with
          | Some (TList (TRecord rt)) => In attr (List.map fst rt) /\ kt = get_attr_type rt attr /\ vt = TList (TRecord rt)
          | _ => False
          end
      | _ => False
      end.

    Local Ltac get_update_same_diff x y :=
      let E := fresh "E" in
      destruct (String.eqb x y) eqn:E;
      [ rewrite eqb_eq in E; subst; repeat rewrite Properties.map.get_update_same
      | rewrite eqb_neq in E; repeat rewrite Properties.map.get_update_diff ]; auto.

    Local Ltac get_put_same_diff x y :=
      let E := fresh "E" in
      destruct (String.eqb x y) eqn:E;
      [ rewrite eqb_eq in E; subst; repeat rewrite map.get_put_same
      | rewrite eqb_neq in E; repeat rewrite map.get_put_diff ]; auto.

    Lemma locals_eq_except_update : forall l l' tbl x v,
        locals_eq_except tbl l l' -> locals_eq_except tbl (map.update l x v) (map.update l' x v).
    Proof.
      intros. intros y H_neq. get_update_same_diff x y.
    Qed.

    Lemma locals_equiv_idx_list_at_update : forall l l' tbl attr x v,
        locals_equiv_idx_list_at tbl attr l l' -> x <> tbl ->
        locals_equiv_idx_list_at tbl attr (map.update l x v) (map.update l' x v).
    Proof.
      intros. unfold locals_equiv_idx_list_at in *. get_update_same_diff x tbl. intuition.
    Qed.

    Lemma locals_eq_except_put : forall l l' x y v,
        locals_eq_except x l l' -> locals_eq_except x (map.put l y v) (map.put l' y v).
    Proof.
      intros. intros z H_neq. get_put_same_diff y z.
    Qed.

    Lemma locals_equiv_idx_list_at_put : forall l l' attr x y v,
        locals_equiv_idx_list_at x attr l l' -> x <> y ->
        locals_equiv_idx_list_at x attr (map.put l y v) (map.put l' y v).
    Proof.
      unfold locals_equiv_idx_list_at; intros. get_put_same_diff y x. intuition.
    Qed.

    Lemma locals_eq_except_put0 : forall l l' x v v',
        locals_eq_except x l l' -> locals_eq_except x (map.put l x v) (map.put l' x v').
    Proof.
      unfold locals_eq_except; intros. repeat rewrite map.get_put_diff; auto.
    Qed.

    Lemma locals_equiv_idx_list_at_put0 :forall l l' x attr interp_e interp_e' v v',
        locals_equiv_idx_list_at x attr l l' ->
        interp_e = VDict v -> interp_e' = VList v' ->
        v = gallina_list_to_idx attr v' ->
        locals_equiv_idx_list_at x attr (map.put l x (interp_e)) (map.put l' x (interp_e')).
    Proof.
      unfold locals_equiv_idx_list_at; intros. repeat rewrite map.get_put_same. subst; auto.
    Qed.

    Lemma get_attr_type_ty_wf : forall rt attr,
        type_wf (TRecord rt) ->
        type_wf (get_attr_type rt attr).
    Proof.
      intros. unfold get_attr_type. destruct (access_record rt attr) eqn:E.
      - apply access_record_sound in E. inversion H. apply in_map with (f:=snd) in E; simpl in E.
        eapply List.Forall_In in H3; eauto.
      - constructor.
    Qed.

    Hint Resolve get_attr_type_ty_wf : fiat2_hints.
    Hint Resolve tenv_wf_step : fiat2_hints.
    Hint Resolve locals_wf_step : fiat2_hints.

    Definition tenv_equiv_at (x attr : string) (rt : list (string * type)) (Gstore : tenv) :=
      map.put Gstore x (TDict (get_attr_type rt attr) (TList (TRecord rt))).

    Lemma locals_equiv_locals_wf : forall x rt attr Gstore' store' store,
        locals_wf Gstore' store' ->
        tenv_wf Gstore' ->
        locals_equiv_idx_list_at x attr store store' ->
        locals_eq_except x store store' ->
        map.get Gstore' x = Some (TList (TRecord rt)) ->
        In attr (List.map fst rt) ->
        locals_wf (tenv_equiv_at x attr rt Gstore') store.
    Proof.
      intros * H_wf H_Gstr' H_equiv H_except H_x H_in. unfold tenv_equiv_at.
      unfold locals_wf; intros y t. get_put_same_diff x y.
      - intro H_t; injection H_t as H_t; subst.
        unfold locals_equiv_idx_list_at in H_equiv. repeat destruct_match; intuition.
        apply H_wf in H_x as H'. rewrite E1 in H'. subst.
        assert (interp_expr store' map.empty (ELoc y) = VList l0). { simpl; unfold get_local. rewrite E1; auto. }
        assert (interp_expr store' map.empty (list_to_idx attr (ELoc y)) = VDict (gallina_list_to_idx attr l0)).
        { eapply fiat2_gallina_list_to_idx with (Genv:=map.empty); eauto.
          1: constructor; auto.
          1,2: unfold tenv_wf, locals_wf; intros; repeat rewrite map.get_empty in *; discriminate. }
        assert (type_of Gstore' map.empty (ELoc y) (TList (TRecord rt))). { constructor; auto. }
        eapply list_to_idx_preserve_ty in H1; eauto.
        1: eapply type_sound with (env:=map.empty) in H1; eauto.
        2-4: unfold tenv_wf, locals_wf; intros; repeat rewrite map.get_empty in *; discriminate.
        rewrite H0 in H1. auto.
      - intro H_y. apply H_wf in H_y. destruct_match; intuition. rewrite H_except; auto. rewrite E0; auto.
    Qed.

    Lemma tenv_equiv_at_wf : forall tbl attr rt Gstore,
        tenv_wf Gstore -> map.get Gstore tbl = Some (TList (TRecord rt)) ->
        tenv_wf (tenv_equiv_at tbl attr rt Gstore).
    Proof.
      intros * H_Gstr H_tbl_ty. apply tenv_wf_step; auto. constructor.
      all: apply H_Gstr in H_tbl_ty; auto with fiat2_hints.
    Qed.

    Hint Resolve tenv_equiv_at_wf : fiat2_hints.
    Hint Resolve locals_equiv_locals_wf : fiat2_hints.
    Hint Resolve locals_eq_except_put : fiat2_hints.
    Hint Resolve locals_equiv_idx_list_at_put : fiat2_hints.
    Hint Resolve locals_eq_except_put0 : fiat2_hints.
    Hint Resolve locals_equiv_idx_list_at_put0 : fiat2_hints.
    Hint Resolve type_sound : fiat2_hints.

    Lemma transf_read_preserve_ty : forall Gstore Genv x attr rt e t,
        tenv_wf Gstore -> tenv_wf Genv ->
        map.get Gstore x = Some (TList (TRecord rt)) -> type_of Gstore Genv e t ->
        type_of (tenv_equiv_at x attr rt Gstore) Genv (fold_expr (idx_read_to_list_read x) e) t.
    Proof.
      intros * H_Gstr H_Genv H_x H_ty. unfold tenv_equiv_at.
      generalize dependent Genv. generalize dependent t.
      induction e using expr_IH; simpl; intros.
      all: inversion H_ty; subst.
      all: try now (econstructor; eauto).
      - get_put_same_diff x x0.
        + rewrite H0 in H_x; injection H_x as H_x; subst.
          eapply idx_to_list_preserve_ty; eauto with fiat2_hints.
          constructor. rewrite map.get_put_same. eauto.
        + constructor. rewrite map.get_put_diff; congruence.
      - econstructor; eauto. apply IHe2; eauto with fiat2_hints.
      - econstructor; eauto. apply IHe2; auto. eauto with fiat2_hints.
      - econstructor; eauto. apply IHe3; auto. repeat apply tenv_wf_step; eauto with fiat2_hints.
      - econstructor; eauto.
        + rewrite fst_map_fst; auto.
        + clear H_ty H1 H3 H4 H5. generalize dependent tl. induction l; simpl; intros.
          1: inversion H2; constructor.
          destruct tl; simpl in *; inversion H2; subst. constructor; inversion H; subst.
          1: destruct a; simpl in *; apply H3; auto.
          apply IHl; auto; injection H1; intros; auto.
      - econstructor; eauto. clear H_ty. induction H3; intuition. constructor; inversion H; subst.
        1: destruct x0; simpl in *; split; apply H7; auto.
        1: apply IHForall; auto.
      - econstructor; eauto. apply IHe3; eauto with fiat2_hints.
      - econstructor; eauto. apply IHe3; auto. repeat apply tenv_wf_step; eauto with fiat2_hints.
      - constructor; auto. apply IHe2; eauto with fiat2_hints.
      - econstructor; eauto.
        1: apply IHe3; auto. 2: apply IHe4; eauto with fiat2_hints.
        all: repeat apply tenv_wf_step; eauto with fiat2_hints.
      - econstructor; eauto. apply IHe2; eauto with fiat2_hints.
    Qed.

    Local Ltac invert_unop_binop_atom_ty :=
      lazymatch goal with
      | H: type_of_unop _ _ _ |- _ => inversion H; subst
      | H: type_of_binop _ _ _ _ |- _ => inversion H; subst
      | H: type_of_atom _ _ |- _ => inversion H; subst
      end.

    Local Ltac apply_transf_read_write_sound''_IH Gstore' :=
      lazymatch goal with
      | H: context[type_of _ _ ?e _ -> _],
          H_can: can_transf_to_idx'' _ false ?e = true,
            H_equiv: locals_equiv_idx_list_at _ _ _ _ |- _ =>
          let IH := fresh "IH" in
          let IHL := fresh "IHL" in
          let IH' := fresh "IH'" in
          eapply H with (Gstore':=Gstore') in H_equiv as IH; eauto; clear H;
          try (destruct IH as [IHL _]; apply IHL in H_can as IH')
      | H: context[type_of _ _ ?e _ -> _],
          H_can: can_transf_to_idx'' _ true ?e = true,
            H_equiv: locals_equiv_idx_list_at _ _ _ _ |- _ =>
          let IH := fresh "IH" in
          let IHR := fresh "IHR" in
          let IH' := fresh "IH'" in
          eapply H with (Gstore':=Gstore') in H_equiv as IH; eauto; clear H;
          try (destruct IH as [_ IHR]; apply IHR in H_can as IH')
      end.

    Local Ltac apply_Forall_In :=
      lazymatch goal with
      | H1: Forall _ ?l, H2: In _ ?l |- _ => eapply List.Forall_In in H1; eauto
      end.

    Local Ltac rewrite_expr_value :=
      lazymatch goal with
      | E: VList _ = ?e |- context[?e] => rewrite <- E
      | E: VList _ = ?e, H: context[?e] |- _ => rewrite <- E in H
      end.

    Local Ltac apply_type_sound e :=
            lazymatch goal with
            | H: type_of _ _ e _ |- _ =>
                let H' := fresh "H'" in
                eapply type_sound in H as H'; eauto; try inversion H'; subst; auto
            end.

    Local Ltac rewrite_interp_fold_expr :=
      lazymatch goal with
      | H: interp_expr _ _ (fold_expr _ ?e) = _ |- context[?e] =>
          rewrite H; clear H
      end.

    Lemma In_map_ext : forall A B (f g : A -> B) l, (forall x, In x l -> f x = g x) -> List.map f l = List.map g l.
    Proof.
      intros * H. induction l; simpl; auto.
      f_equal; [ apply H | apply IHl ]; intuition.
    Qed.

    Lemma Permutation_filter : forall A (l l' : list A), Permutation l l' -> forall f, Permutation (filter f l) (filter f l').
    Proof.
      induction l; intros.
      - apply Permutation_nil in H. subst. auto.
      - apply Permutation_sym in H as H'. apply Permutation_vs_cons_inv in H'.
        repeat lazymatch goal with H: exists _, _ |- _ => destruct H end.
        subst. rewrite filter_app. simpl; destruct (f a).
        1: apply Permutation_cons_app.
        all: rewrite <- filter_app.
        all: apply Permutation_cons_app_inv in H; auto.
    Qed.

    Lemma Permutation_flat_map : forall A B (f g : A -> list B),
                   forall l l', (forall x, In x l -> Permutation (f x) (g x)) ->
                                Permutation l l' ->
                                Permutation (flat_map f l) (flat_map g l').
    Proof.
      intros * H_fg. generalize dependent l'. induction l; simpl; intros l' H.
      - apply Permutation_nil in H; subst; auto.
      - apply Permutation_sym in H as H'. apply Permutation_vs_cons_inv in H'.
        repeat lazymatch goal with H: exists _, _ |- _ => destruct H end. subst.
        rewrite flat_map_app. simpl. pose proof H_fg a as H_a.
        assert (H_a_in: In a (a :: l)). { intuition. } apply H_a in H_a_in as H_p.
        destruct (f a) eqn:E.
        + simpl. apply Permutation_nil in H_p.
          rewrite H_p; simpl. rewrite <- flat_map_app.
          apply Permutation_cons_app_inv in H. intuition.
        + eapply perm_trans. 2: apply Permutation_app_swap_app.
          apply Permutation_app; auto. rewrite <- flat_map_app. apply IHl.
          2: apply Permutation_cons_app_inv in H.
          all: intuition.
    Qed.

    Local Ltac apply_transf_read_preserve_ty e attr :=
      lazymatch goal with
      | H: type_of _ _ e _ |- _ =>
          let H_transf_ty := fresh "H_transf_ty" in
          eapply transf_read_preserve_ty with (attr:=attr) in H as H_transf_ty; eauto with fiat2_hints;
          apply_type_sound e;
          eapply type_sound in H_transf_ty; eauto with fiat2_hints;
          inversion H_transf_ty; subst
      end.

    Lemma imp_pre_true : forall A B, A -> (A -> B) -> A /\ B.
    Proof. intuition. Qed.

    Lemma transf_read_write_sound'' : forall tbl attr rt e Gstore' Genv t store store' env,
        type_of Gstore' Genv e t ->
        tenv_wf Gstore' -> tenv_wf Genv ->
        map.get Gstore' tbl = Some (TList (TRecord rt)) -> In attr (List.map fst rt) ->
        locals_wf Gstore' store' -> locals_wf Genv env ->
        locals_eq_except tbl store store' ->
        locals_equiv_idx_list_at tbl attr store store' ->
        (can_transf_to_idx'' tbl false e -> interp_expr store env (fold_expr (idx_read_to_list_read tbl) e) = interp_expr store' env e) /\
          (can_transf_to_idx'' tbl true e ->
           match t with
           | TList t =>
               match interp_expr store env (fold_expr (idx_read_to_list_read tbl) e) with
               | VList l => match interp_expr store' env e with
                            | VList l' => Permutation l l'
                            | _ => False
                            end
               | _ => False
               end
           | _ => interp_expr store env (fold_expr (idx_read_to_list_read tbl) e) = interp_expr store' env e
           end).
    Proof.
      induction e using expr_IH; cbn; intros * H_ty H_Gstr' H_Genv H_tbl_ty H_in H_str' H_env H_except H_equiv; auto.
      - (* EVar *)
        split; intros; auto. apply_type_sound (EVar x).
      - (* ELoc *)
        split; intros.
        all: unfold is_true in *; rewrite Bool.orb_true_iff in H.
        + destruct (String.eqb x tbl) eqn:E; intuition; try discriminate.
          rewrite eqb_sym; rewrite E; try discriminate. apply eqb_neq in E. simpl.
          unfold get_local. rewrite H_except; auto.
        +  clear H; destruct (String.eqb x tbl) eqn:E; rewrite eqb_sym; rewrite E.
          * (* x = tbl *) rewrite eqb_eq in E; subst.
            inversion H_ty; subst. rewrite H0 in H_tbl_ty. injection H_tbl_ty; intros; subst.
            apply_type_sound (ELoc tbl).
            erewrite fiat2_gallina_idx_to_list with (Gstore:=tenv_equiv_at tbl attr rt Gstore'); simpl; eauto with fiat2_hints.
            1: eapply gallina_list_to_idx_to_list; eauto.
            1:{ constructor. unfold tenv_equiv_at. rewrite map.get_put_same. eauto. }
            1:{ unfold get_local. unfold locals_equiv_idx_list_at in H_equiv; repeat destruct_match; intuition.
                subst. unfold get_local in *. rewrite E1 in H. injection H; congruence. }
          * (* x <> tbl *) rewrite eqb_neq in E. destruct t; simpl.
            all: unfold get_local; rewrite H_except; auto.
            apply_type_sound (ELoc x). unfold get_local in *.
            rewrite_expr_value. intuition.
      - (* EAtom *)
        split; intro H_can; destruct t; auto. inversion H_ty; subst. invert_unop_binop_atom_ty.
        all: simpl; intuition.
      - (* EUnop *)
        inversion H_ty; subst. split; intro H_can; destruct o; simpl in *.
        all: invert_unop_binop_atom_ty; unfold is_true in H_can.
        all: apply_transf_read_write_sound''_IH Gstore'; try rewrite IH'; auto.
        (* OLength *)
        all: apply_transf_read_preserve_ty e attr.
        all: repeat rewrite_expr_value.
        all: erewrite Permutation_length; eauto.
      - (* EBinop *)
        inversion H_ty; subst. split; intro H_can; destruct o; simpl in *.
        all: invert_unop_binop_atom_ty; unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: repeat apply_transf_read_write_sound''_IH Gstore'; try congruence.
        all: try now (repeat rewrite_interp_fold_expr; auto).
        1,2,4,5: (* OConcat, ORepeat, ORange, OWRange *)
          repeat rewrite_interp_fold_expr; auto;
        apply_type_sound e1; apply_type_sound e2; auto.
        (* OCons *)
        rewrite_interp_fold_expr.
        eapply locals_equiv_locals_wf in H_equiv as H_wf; eauto.
        apply_transf_read_preserve_ty e2 attr.
        apply perm_skip. repeat rewrite_expr_value; auto.
      - (* EIf *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: repeat apply_transf_read_write_sound''_IH Gstore';
          repeat rewrite_interp_fold_expr; auto.
        apply_type_sound e1. destruct b; auto.
      - (* ELet *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: repeat apply_transf_read_write_sound''_IH Gstore';
          repeat rewrite_interp_fold_expr; eauto with fiat2_hints.
      - (* EFlatmap *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: revert IHe2; apply_transf_read_write_sound''_IH Gstore'; intros.
        + rewrite_interp_fold_expr; auto. apply_type_sound e1. f_equal.
          apply In_flat_map_ext. intros a H_a_in. apply_transf_read_write_sound''_IH Gstore'; try rewrite_interp_fold_expr; eauto with fiat2_hints.
          1: apply locals_wf_step; auto; apply_Forall_In.
        + eapply locals_equiv_locals_wf in H_equiv as H_wf; eauto.
          apply_transf_read_preserve_ty e1 attr. repeat rewrite_expr_value.
          apply Permutation_flat_map; auto.
          intros v H_v_in. apply_Forall_In.
          apply_transf_read_write_sound''_IH Gstore'; eauto with fiat2_hints.
          1: apply_transf_read_preserve_ty e2 attr.
          1: iter_hyps rewrite_hyp_l; auto.
      - (* EFold *)
        inversion H_ty; subst.
        apply imp_pre_true.
        1: intro H_can.
        2: intros HA H_can; specialize (HA H_can).
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: revert IHe3; repeat apply_transf_read_write_sound''_IH Gstore'; intros.
        + repeat rewrite_interp_fold_expr. apply_type_sound e1.
          eapply type_sound in H6 as H2'; eauto.
          eapply In_fold_right_ext with (P:=fun a => type_of_value a t); auto.
          intros * P H_b_in. intuition.
          1:{ apply_transf_read_write_sound''_IH Gstore'; eauto.
              1: repeat apply tenv_wf_step; eauto with fiat2_hints.
              1: repeat apply locals_wf_step; eauto with fiat2_hints; apply_Forall_In. }
          1:{ apply_transf_read_write_sound''_IH Gstore'; auto.
              1: rewrite_interp_fold_expr; eapply type_sound; eauto.
              1,3: repeat apply tenv_wf_step; eauto with fiat2_hints.
              1,2: repeat apply locals_wf_step; eauto with fiat2_hints; apply_Forall_In. }
        + rewrite HA. destruct t; auto.
          apply_type_sound (EFold e1 e2 x y e3).
      - (* ERecord *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: do 2 f_equal; rewrite map_map.
        all: apply In_map_ext; intros x H_x_in; apply_Forall_In;
          rewrite forallb_forall in H_can; apply H_can in H_x_in as H_x.
        all: apply in_map with (f:=snd) in H_x_in; pose proof (Forall2_In_Permuted _ _ _ _ _ _ H2 H_x_in).
        all: do 3 destruct H0; intuition.
        all: eapply H with (Gstore':=Gstore') in H_equiv as IH; eauto.
        all: apply IH in H_x as IH'; destruct x; simpl in *; congruence.
      - (* EAccess *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: apply_transf_read_write_sound''_IH Gstore'; rewrite_interp_fold_expr; auto.
        destruct t; auto. apply_type_sound (EAccess e s).
      - (* EDict *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can.
        all: do 3 f_equal; rewrite map_map; apply In_map_ext.
        all: intros x H_x_in; destruct x; simpl in *.
        all: repeat apply_Forall_In; rewrite forallb_forall in H_can; apply H_can in H_x_in as H_x.
        all: repeat rewrite Bool.andb_true_iff in *; intuition; simpl in *.
        all: repeat apply_transf_read_write_sound''_IH Gstore'.
        all: rewrite IH', IH'0; auto.
      - (* EInsert *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: repeat apply_transf_read_write_sound''_IH Gstore'; repeat rewrite_interp_fold_expr; auto.
      - (* EDelete *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: repeat apply_transf_read_write_sound''_IH Gstore'; repeat rewrite_interp_fold_expr; auto.
      - (* ELookup *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: repeat apply_transf_read_write_sound''_IH Gstore'; repeat rewrite_interp_fold_expr; auto.
      - (* EOptMatch *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: revert IHe2 IHe3; apply_transf_read_write_sound''_IH Gstore'; intros.
        all: rewrite_interp_fold_expr; apply_type_sound e1.
        all: try now (revert IHe3; apply_transf_read_write_sound''_IH Gstore'; eauto).
        all: revert IHe2; apply_transf_read_write_sound''_IH Gstore'; eauto with fiat2_hints.
      - (* EDictFold *)
        inversion H_ty; subst. apply imp_pre_true.
        1: intro H_can.
        2: intros HA H_can; specialize (HA H_can).
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: revert IHe3; repeat apply_transf_read_write_sound''_IH Gstore'; intros.
        + repeat rewrite_interp_fold_expr; apply_type_sound e1.
          apply In_fold_right_ext with (P := fun a => type_of_value a t).
          2:{ intros. apply_transf_read_write_sound''_IH Gstore'.
              1: rewrite_interp_fold_expr.
              2: repeat apply tenv_wf_step; eauto with fiat2_hints.
              2: repeat apply locals_wf_step; auto; apply_Forall_In; intuition.
              1: intuition. apply_type_sound e3; eauto with fiat2_hints.
              1: repeat apply locals_wf_step; auto; apply_Forall_In; intuition. }
          apply_type_sound e2; eauto.
        + rewrite HA. destruct t; auto.
          apply_type_sound (EDictFold e1 e2 k v acc e3).
      - (* ESort *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: apply_transf_read_write_sound''_IH Gstore'.
        1:{ repeat destruct_match; intuition. f_equal. apply Permutation_SSorted_eq; auto using StronglySorted_value_sort.
            pose proof Permuted_value_sort l. pose proof Permuted_value_sort l0.
            eapply perm_trans. 2: eauto. apply Permutation_sym. eapply perm_trans. 2: eauto. apply Permutation_sym; auto. }
        1:{ eapply locals_equiv_locals_wf in H_equiv as H_wf; eauto.
            apply_transf_read_preserve_ty e attr. repeat rewrite_expr_value.
            pose proof Permuted_value_sort l. pose proof Permuted_value_sort l0.
            eapply perm_trans. 2: eauto. apply Permutation_sym. eapply perm_trans. 2: eauto. apply Permutation_sym; auto. }
      - (* EFilter *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: revert IHe2; apply_transf_read_write_sound''_IH Gstore'; intros.
        + rewrite_interp_fold_expr. apply_type_sound e1. f_equal.
          apply filter_ext_in; intros a H_a_in. apply_transf_read_write_sound''_IH Gstore'; eauto with fiat2_hints.
          1: rewrite_interp_fold_expr; auto.
          1: apply locals_wf_step; auto; apply_Forall_In.
        + eapply locals_equiv_locals_wf in H_equiv as H_wf; eauto.
          apply_transf_read_preserve_ty e1 attr. repeat rewrite_expr_value.
          rewrite In_filter_ext with
            (g:=fun v : value => match interp_expr store' (map.put env x v) e2 with
                                 | VBool b => b
                                 | _ => false
                                 end).
          2:{ intros a H_a_in. apply_transf_read_write_sound''_IH Gstore'; eauto with fiat2_hints.
              1: rewrite_interp_fold_expr; auto.
              1: apply locals_wf_step; auto; apply_Forall_In. }
          apply Permutation_filter; auto.
      - (* EJoin *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: revert IHe3 IHe4; repeat apply_transf_read_write_sound''_IH Gstore'; intros.
        + repeat rewrite_interp_fold_expr.
          apply_type_sound e1. apply_type_sound e2. f_equal.
          apply In_flat_map_ext; intros a H_a_in.
          rewrite In_filter_ext with
            (g:=fun v2 : value => match interp_expr store' (map.put (map.put env x a) y v2) e3 with
                                  | VBool b => b
                                  | _ => false
                                  end).
          1: apply In_map_ext; intros b H_b_in; revert IHe3; repeat apply_transf_read_write_sound''_IH Gstore'; auto.
          1: repeat apply tenv_wf_step; eauto with fiat2_hints.
          1: repeat apply locals_wf_step; eauto with fiat2_hints.
          1,2: rewrite filter_In in H_b_in; intuition; repeat apply_Forall_In.
          intros c H_c_in. revert IHe4; apply_transf_read_write_sound''_IH Gstore'; intros.
          1: rewrite_interp_fold_expr; auto.
          1: repeat apply tenv_wf_step; eauto with fiat2_hints.
          1: repeat apply locals_wf_step; repeat apply_Forall_In.
        + eapply locals_equiv_locals_wf in H_equiv as H_wf; eauto.
          apply_transf_read_preserve_ty e1 attr.
          apply_transf_read_preserve_ty e2 attr. repeat rewrite_expr_value.
          apply Permutation_flat_map; auto. intros a H_a_in.
          rewrite In_map_ext with (g:=fun v2 : value => interp_expr store' (map.put (map.put env x a) y v2) e4).
          1: apply Permutation_map.
          1: rewrite In_filter_ext with
            (g:=fun v2 : value => match interp_expr store' (map.put (map.put env x a) y v2) e3 with
                                  | VBool b => b
                                  | _ => false
                                  end).
          1:{ apply Permutation_filter; auto. }
          1:{ intros b H_b_in. revert IHe4; apply_transf_read_write_sound''_IH Gstore'; intros.
              1: rewrite_interp_fold_expr; auto.
              1: repeat apply tenv_wf_step; eauto with fiat2_hints.
              1: repeat apply locals_wf_step; repeat apply_Forall_In. }
          1:{ intros b H_b_in. revert IHe3; apply_transf_read_write_sound''_IH Gstore'; intros.
              1: rewrite_interp_fold_expr; auto.
              1: repeat apply tenv_wf_step; eauto with fiat2_hints.
              1: repeat apply locals_wf_step; auto.
              1,2: apply filter_In in H_b_in; intuition; repeat apply_Forall_In. }
      - (* EProj *)
        inversion H_ty; subst. split; intro H_can.
        all: unfold is_true in H_can; repeat rewrite Bool.andb_true_iff in H_can; intuition.
        all: revert IHe2; apply_transf_read_write_sound''_IH Gstore'; intros.
        + rewrite_interp_fold_expr. apply_type_sound e1. f_equal. apply In_map_ext.
          intros a H_a_in. apply_transf_read_write_sound''_IH Gstore'; eauto with fiat2_hints.
          repeat apply locals_wf_step; apply_Forall_In.
        + eapply locals_equiv_locals_wf in H_equiv as H_wf; eauto.
          apply_transf_read_preserve_ty e1 attr.
          rewrite In_map_ext with (g:=(fun v : value => interp_expr store' (map.put env x v) e2)).
          2:{ intros a H_a_in. apply_transf_read_write_sound''_IH Gstore'; eauto with fiat2_hints.
              repeat apply locals_wf_step; apply_Forall_In. }
          repeat rewrite_expr_value. apply Permutation_map; auto.
    Qed.

    Lemma transf_read_write_sound' : forall c Gstore' Genv rt store store' env tbl attr,
        well_typed Gstore' Genv c ->
        map.get Gstore' tbl = Some (TList (TRecord rt)) ->
        In attr (List.map fst rt) ->
        tenv_wf Gstore' -> tenv_wf Genv -> locals_wf Gstore' store' -> locals_wf Genv env ->
        locals_eq_except tbl store store' ->
        locals_equiv_idx_list_at tbl attr store store' ->
        can_transf_to_idx' tbl c = true ->
        (locals_eq_except tbl
           (interp_command store env (transf_to_idx' tbl attr c))
           (interp_command store' env c)) /\
          (locals_equiv_idx_list_at tbl attr
             (interp_command store env (transf_to_idx' tbl attr c))
             (interp_command store' env c)).
    Proof.
      induction c; simpl; auto; intros * H_ty H_tbl_ty H_in H_Gstr' H_Genv H_str' H_env H_except H_equiv H_can.
      all: repeat rewrite Bool.andb_true_iff in H_can; inversion H_ty; subst.
      - eapply IHc2; try eapply IHc1; eauto; intuition.
        eapply command_type_sound; eauto.
      - destruct H_can.
        eapply transf_read_write_sound'' with (Gstore':=Gstore') in H as H'; eauto. rewrite H'.
        eapply IHc; eauto; [ apply tenv_wf_step | apply locals_wf_step ]; eauto with fiat2_hints.
      - rewrite Bool.negb_true_iff, eqb_neq in *.
        assert (E: map.get store x = map.get store' x). { apply H_except; intuition. } rewrite E.
        repeat lazymatch goal with H: _ /\ _ |- _ => destruct H end.
        eapply transf_read_write_sound'' with (Gstore':=Gstore') in H2 as H'; eauto. rewrite H'.
        split. 1: apply locals_eq_except_update. 2: apply locals_equiv_idx_list_at_update. 3: congruence.
        1,2: eapply IHc; eauto with fiat2_hints. all: rewrite map.get_put_diff; auto.
      - cbn. eapply transf_read_write_sound'' with (Gstore':=Gstore') in H_can; eauto.
        destruct (String.eqb tbl x) eqn:E.
        + unfold fold_command. unfold interp_command.
          rewrite eqb_eq in *; subst. rewrite H_tbl_ty in H1. injection H1; intros; subst.
          apply_type_sound e.
          split; eauto with fiat2_hints. eapply locals_equiv_idx_list_at_put0; eauto.
          remember (map.put Gstore' x (TDict (get_attr_type rt attr) (TList (TRecord rt)))) as Gstore.
          eapply fiat2_gallina_list_to_idx with (Gstore:=Gstore); eauto.
          1: subst; apply transf_read_preserve_ty; auto.
          1:{ subst. apply tenv_wf_step; auto. apply type_of__type_wf in H2; auto. constructor; eauto with fiat2_hints. }
          1: subst; eapply locals_equiv_locals_wf; eauto.
          1: rewrite H_can; auto.
        + simpl. rewrite H_can.
          rewrite eqb_neq in *. split; auto with fiat2_hints.
      - repeat lazymatch goal with H: _ /\ _ |- _ => destruct H end.
        eapply transf_read_write_sound'' with (Gstore':=Gstore') in H; eauto. rewrite H.
        apply_type_sound e. destruct b; eauto.
      - repeat lazymatch goal with H: _ /\ _ |- _ => destruct H end.
        eapply transf_read_write_sound'' with (Gstore':=Gstore') in H; eauto. rewrite H.
        apply_type_sound e.
        destruct (interp_expr store' env e) eqn:E; try now (exfalso; auto).
        clear E H H2. generalize dependent store; generalize dependent store'. induction l; simpl; auto. intros.
        lazymatch goal with H: Forall _ (_ :: _) |- _ => inversion H; subst end. apply IHl; auto.
        1: eapply command_type_sound; eauto.
        3,4: eapply IHc.
        all: eauto with fiat2_hints.
    Qed.

    Lemma transf_read_write_sound : forall (Gstore Genv : tenv) (store env : locals) tbl attr c,
        tenv_wf Gstore -> tenv_wf Genv ->
        well_typed Gstore Genv c ->
        locals_wf Gstore store -> locals_wf Genv env ->
        can_transf_to_idx tbl attr c = true ->
        interp_command store env (transf_to_idx tbl attr c) = interp_command store env c.
    Proof.
      intros * H_Gstr H_Genv H_ty H_str H_env H.
      destruct c; simpl in *; try discriminate.
      repeat (destruct_match; try discriminate).
      repeat rewrite Bool.andb_true_iff in H; intuition.
      apply eqb_eq in H; subst; simpl. apply locals_eq_update. intros.
      inversion H_ty; subst. inversion H4; subst. inversion H3; subst.
      eapply transf_read_write_sound'; cbn; eauto with fiat2_hints.
      - rewrite map.get_put_same; eauto.
      - rewrite inb_true_iff in *; auto.
      - apply locals_wf_step; auto. repeat constructor.
      - unfold locals_eq_except; intros. repeat rewrite map.get_put_diff; congruence.
      - unfold locals_equiv_idx_list_at. repeat rewrite map.get_put_same; trivial.
    Qed.

    Definition eq_filter_to_lookup_head (tbl attr : string) (e : expr) :=
      match e with
      | EFilter
          (EDictFold (ELoc tbl') (EAtom (ANil None)) k v acc (EBinop OConcat (EVar v') (EVar acc')))
          x
          (EBinop OEq (EAccess (EVar y) attr') e') =>
          if (String.eqb k "k" && String.eqb v "v" && String.eqb v v' && String.eqb acc "acc" && String.eqb acc acc' && String.eqb tbl' tbl && String.eqb attr' attr && String.eqb x y &&
                negb (String.eqb v' acc') && negb (free_immut_in x e'))%bool
          then EOptMatch (ELookup (ELoc tbl) e')
                 (EAtom (ANil None))
                 "x" (EVar "x")
          else e
      | _ => e
      end.

    Local Ltac invert_type_of :=
      lazymatch goal with
      | H: type_of _ _ (_ _) _ |- _ => inversion H; subst; clear H
      | H: type_of_binop _ _ _ _ |- _ => inversion H; subst; clear H
      end.

    Local Ltac rewrite_map_get_put :=
      lazymatch goal with
      | H: context[map.get (map.put _ ?x _) ?x] |- _ =>
          rewrite map.get_put_same in H
      | H: context[map.get (map.put _ _ _) _] |- _ =>
          rewrite map.get_put_diff in H; try congruence
      | |- context[map.get (map.put _ ?x _) ?x] =>
          rewrite map.get_put_same
      | |- context[map.get (map.put _ _ _) _] =>
          rewrite map.get_put_diff; try congruence
      end.

    Local Ltac clear_refl := lazymatch goal with H: ?x = ?x |- _ => clear H end.

    Local Ltac do_injection :=
      lazymatch goal with
      | H: ?c _ = ?c _ |- _ => injection H; intros; subst
      end.

    Lemma eq_filter_to_lookup_head_preserve_ty : forall tbl attr e rt t (Gstore Genv : tenv),
        tenv_wf Gstore -> tenv_wf Genv ->
        map.get Gstore tbl = Some (TDict (get_attr_type rt attr) (TList (TRecord rt))) ->
        type_of Gstore Genv e t ->
        type_of Gstore Genv (eq_filter_to_lookup_head tbl attr e) t.
    Proof.
      intros * H_Gstr H_Genv H_tbl_ty H.
      destruct e; auto. destruct e1; auto. destruct e1_1; auto. destruct e1_2; auto.
      destruct a; auto. destruct t0; auto. destruct e1_3; auto. destruct o; auto.
      destruct e1_3_1; auto. destruct e1_3_2; auto. destruct e2; auto. destruct o; auto.
      destruct e2_1; auto. destruct e2_1; auto. simpl.
      lazymatch goal with |- context[if ?x then _ else _] => destruct x eqn:E end; auto.
      repeat rewrite Bool.andb_true_iff in E; intuition. rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
      repeat invert_type_of. repeat rewrite_map_get_put.
      injection H5; intro; subst.
      repeat econstructor; eauto.
      1:{ rewrite H10 in H_tbl_ty. repeat (clear_refl; repeat do_injection).
          unfold get_attr_type. repeat (clear_refl; repeat do_injection). rewrite H7.
          eapply not_free_immut_put_ty; eauto. }
      1:{ rewrite map.get_put_same; trivial. }
    Qed.

    Definition index_wf (attr : string) (l : list (value * value)) :=
      NoDup (List.map fst l) /\
        Forall (fun p => match snd p with
                         | VList l =>
                             Forall (fun r => match r with
                                              | VRecord r => access_record r attr = Success (fst p)
                                              | _ => False
                                              end) l
                         | _ => False
                         end) l.

    Definition gallina_filter_access_eq (s : string) (v0 : value) (l : list value) :=
      filter (fun v => value_eqb match v with
                         | VRecord r => record_proj s r
                         | _ => VUnit
                         end v0) l.

    Lemma fiat2_gallina_filter_access_eq :
      forall (store env : locals) e1 e2 x s l,
        interp_expr store env e1 = VList l ->
        free_immut_in x e2 = false ->
        interp_expr store env (EFilter e1 x (EBinop OEq (EAccess (EVar x) s) e2)) =
          VList (gallina_filter_access_eq s (interp_expr store env e2) l).
      Proof.
        intros * H1 H_free; simpl. rewrite H1. f_equal. apply filter_ext. intro a.
        unfold get_local. rewrite map.get_put_same. rewrite <- not_free_immut_put_sem; auto.
      Qed.

      Lemma dict_lookup__filter_none : forall attr k idx,
          index_wf attr idx ->
          dict_lookup k idx = None ->
          gallina_filter_access_eq attr k (gallina_idx_to_list idx) = nil.
      Proof.
        unfold gallina_filter_access_eq.
        intros. induction idx; simpl; auto. destruct a; simpl in *. destruct v0; auto.
        rewrite filter_app. destruct H as [HL HR]; inversion HL; inversion HR; subst.
        destruct (value_eqb k v) eqn:E.
        1: congruence.
        rewrite IHidx; auto. 2: split; auto.
        rewrite app_nil_r. simpl in *. induction H6; simpl; auto. rewrite IHForall.
        1:{ destruct x; intuition.
            erewrite access_record__record_proj; eauto. rewrite value_eqb_sym. rewrite E; trivial. }
        constructor; auto.
      Qed.

      Lemma Forall_false__filter : forall A f (l : list A), Forall (fun x => f x = false) l -> filter f l = nil.
      Proof.
        intros * H; induction l; simpl; auto. simpl in H.
        inversion H; subst. rewrite H2. auto.
      Qed.

      Lemma In_gallina_idx_to_list : forall r idx,
          In r (gallina_idx_to_list idx) -> exists k v, In (k, VList v) idx /\ In r v.
      Proof.
        intros. induction idx; simpl in *; intuition.
        destruct a; simpl in *. destruct v0 eqn:E; try apply in_nil in H; intuition.
        apply in_app_or in H; intuition.
        - exists v; exists l; intuition.
        - destruct H as [k' [v' H]]. exists k'; exists v'. intuition.
      Qed.

      Lemma dict_lookup__filter_some : forall attr k idx l,
          index_wf attr idx ->
          dict_lookup k idx = Some (VList l) ->
          gallina_filter_access_eq attr k (gallina_idx_to_list idx) = l.
      Proof.
        unfold gallina_filter_access_eq.
        intros; generalize dependent l; induction idx; simpl; intros.
        1: congruence.
        destruct H as [HL HR]; inversion HL; inversion HR; subst.
        destruct a; simpl in *. destruct v0; intuition. rewrite filter_app.
        destruct (value_eqb k v) eqn:E; auto.
        2:{ erewrite IHidx; eauto. 2: split; auto.
            lazymatch goal with |- ?l0 ++ _ = _ => replace l0 with (@nil value) end; auto.
            induction l0; simpl; auto. inversion H6; subst. rewrite <- IHl0; auto.
            destruct a; intuition.
            erewrite access_record__record_proj; eauto. rewrite value_eqb_sym. rewrite E; trivial. }
        1:{ injection H0; intros; subst.
            rewrite forallb_filter_id.
            1: lazymatch goal with |- _ ++ ?l = _ => replace l with (@nil value) end.
            1: apply app_nil_r.
            1:{ symmetry. apply Forall_false__filter. rewrite Forall_forall; intros r H_r_in.
                apply In_gallina_idx_to_list in H_r_in as [k' [v' [H_in_L H_in_R]]].
                apply_Forall_In. simpl in *. apply_Forall_In.
                destruct r; intuition. erewrite access_record__record_proj; eauto.
                destruct (value_eqb k' k) eqn:E'; auto. apply value_eqb_eq in E', E; subst.
                apply in_map with (f:=fst) in H_in_L; simpl in *. intuition. }
            rewrite forallb_forall; intros r H_in. apply_Forall_In. destruct r; intuition.
            erewrite access_record__record_proj; eauto using value_eqb_sym. }
      Qed.

    Lemma eq_filter_to_lookup_head_preserve_sem : forall tbl attr e (Gstore Genv : tenv) (store env : locals) rt t idx,
        tenv_wf Gstore -> tenv_wf Genv ->
        map.get Gstore tbl = Some (TDict (get_attr_type rt attr) (TList (TRecord rt))) ->
        In attr (List.map fst rt) ->
        type_of Gstore Genv e t ->
        locals_wf Gstore store -> locals_wf Genv env ->
        map.get store tbl = Some (VDict idx) ->
        index_wf attr idx ->
        interp_expr store env e = interp_expr store env (eq_filter_to_lookup_head tbl attr e).
    Proof.
      intros * H_Gstr H_Genv H_tbl_ty H_in H_ty H_str H_env H_tbl_v H_index_wf.
      (* ??? How to automate this? *)
      destruct e; auto. destruct e1; auto. destruct e1_1; auto. destruct e1_2; auto.
      destruct a; auto. destruct t0; auto. destruct e1_3; auto. destruct o; auto.
      destruct e1_3_1; auto. destruct e1_3_2; auto. destruct e2; auto. destruct o; auto.
      destruct e2_1; auto. destruct e2_1; auto.
      unfold eq_filter_to_lookup_head.
      lazymatch goal with |- context[if ?x then _ else _] => destruct x eqn:E end; auto.
      repeat rewrite Bool.andb_true_iff in E; intuition. rewrite Bool.negb_true_iff, eqb_eq, eqb_neq in *; subst.
      fold (idx_to_list (ELoc tbl)).
      repeat invert_type_of. repeat rewrite_map_get_put.
      repeat (clear_refl; repeat do_injection).
      erewrite fiat2_gallina_filter_access_eq; auto.
      2: eapply fiat2_gallina_idx_to_list with (Gstore:=Gstore); eauto.
      2: econstructor; eauto.
      2: simpl; unfold get_local; rewrite H_tbl_v; auto.
      eapply TyELoc in H_tbl_ty as H_tbl_ty'. apply_type_sound (ELoc tbl). simpl in H'. rewrite <- H1 in H'.
      unfold get_local in H1. rewrite H_tbl_v in H1. injection H1; intros; subst.
      specialize (dict_lookup_sound (width:=width) idx) as H_lookup.
      eapply (H_lookup (get_attr_type rt attr) (TList (TRecord rt)) (interp_expr store env e2_2)) in H'; eauto.
      2:{ unfold get_attr_type. rewrite H_tbl_ty in H10. repeat (clear_refl; repeat do_injection). rewrite H7; auto.
          apply not_free_immut_put_ty in H9; auto. eapply type_sound in H9; eauto. }
      simpl. unfold get_local. rewrite H_tbl_v. inversion H'; subst.
      2: rewrite map.get_put_same.
      (* dict_lookup found no match *)
      1: f_equal; auto using dict_lookup__filter_none.
      (* dict_lookup found some match *)
      1:{ lazymatch goal with H: type_of_value ?v _ |- _ = ?v => inversion H; subst end. f_equal.
          apply dict_lookup__filter_some; auto. }
    Qed.
  End WithMap.

  (* ??? TODO: to be moved *)
  Section ConcreteExample.
    Local Open Scope string.

    Definition ex1 := CLetMut (EAtom (ANil (Some (TRecord (("id", TInt) :: ("name", TString) :: nil))))) "persons"
                        (*  (CLetMut (EAtom (AInt 0)) "res" *)
                        (CSeq
                           (CAssign "persons" (EBinop OCons
                                                 (ERecord (("id", EAtom (AInt 1)) :: ("name", EAtom (AString "K")) :: nil))
                                                 (EAtom (ANil None))))
                           (CSeq
                              (CAssign "res" (EUnop OLength (ELoc "persons")))
                              CSkip)).

    Instance ctenv : map.map string type := SortedListString.map _.
    Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

    Instance clocals : map.map string value := SortedListString.map _.
    Instance clocals_ok : map.ok clocals := SortedListString.ok _.
(*
    Set Printing Implicit.
    Check typecheck map.empty map.empty ex1.
    Set Printing Coercions.
    Compute @map.empty string type ctenv.
    Compute @map.rep string type ctenv.

    Compute typecheck (map.put map.empty "res" TInt) map.empty ex1. *)

    Definition ex1' := transf_to_idx "persons" "id" ex1.
(*  Compute ex1'. *)

    Goal interp_command (map.put map.empty "res" (VInt 0)) (map.empty (value:=value)) ex1' = interp_command (map.put map.empty "res" (VInt 0)) map.empty ex1.
    Proof. reflexivity. Abort.
  End ConcreteExample.
End WithWord.
