Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.Examples fiat2.TypeSystem fiat2.TypeSound.
Require Import List String ZArith Permutation.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
Import ResultMonadNotations.

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

Definition idx_read_to_list_read (tbl attr : string) (e : expr) :=
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


Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Local Notation value := (value (word := word)).

  Section WithMap.
    Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    Definition gallina_list_to_idx attr l := fold_right (fun (v : value) acc => match v with
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

    Definition gallina_idx_to_list (d : list (value * value)) := fold_right
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

    Lemma fiat2_gallina_idx_to_list : forall (Gstore Genv : tenv) (store env : locals) idx l kt rt,
        type_of Gstore Genv idx (TDict kt (TList (TRecord rt))) ->
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

    Require Import Sorted.

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

    Lemma In_access_record
      : forall A l attr, In attr (List.map fst l) -> exists (x : A), access_record l attr = Success x.
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

    Definition list_eq_filter_to_idx_lookup (tbl attr : string) (e : expr) :=
      match e with
      | EFilter
          (EDictFold (ELoc tbl') (EAtom (ANil None)) _ v acc (EBinop OConcat (EVar v') (EVar acc')))
          x
          (EBinop OEq (EAccess (EVar y) attr') e') =>
          if (String.eqb v v' && String.eqb acc acc' && String.eqb tbl' tbl && String.eqb attr' attr && String.eqb x y && negb (free_immut_in x e'))%bool
          then EOptMatch (ELookup (ELoc tbl) e')
                 (EAtom (ANil None))
                 "x" (EVar "x")
          else e
      | _ => e
      end.

    Definition empty_list_to_idx (tbl attr : string) (c : command) : command :=
      match c with
      | CLetMut (EAtom (ANil _)) tbl c => CLetMut (EDict nil) tbl c
      | _ => c
      end.

    (* ??? to be moved *)
    Require Import coqutil.Map.SortedListString.
    Local Open Scope string.

    Definition ex1 := CLetMut (EAtom (ANil (Some (TRecord (("id", TInt) :: ("name", TString) :: nil))))) "persons"
                        (CLetMut (EAtom (ANil (Some (TRecord (("id", TInt) :: ("name", TString) :: nil))))) "res"
                           (CSeq
                              (CAssign "persons" (EBinop OCons
                                                    (ERecord (("id", EAtom (AInt 1)) :: ("name", EAtom (AString "K")) :: nil))
                                                    (EAtom (ANil None))))
                              (CSeq
                                 (CAssign "res" (ELoc "persons"))
                                 CSkip))).


    Instance ctenv : map.map string type := SortedListString.map _.
    Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

(*    Set Printing Implicit.
    Check typecheck map.empty map.empty ex1.
    Set Printing Coercions.
    Compute @map.empty string type ctenv.
    Compute @map.rep string type ctenv.

    Compute typecheck map.empty map.empty ex1. *)

    Definition ex1_1 := fold_command (empty_list_to_idx "persons" "id") id ex1.
    Definition ex1_2 := fold_command id (idx_read_to_list_read "persons" "id") ex1_1.
    Definition ex1_3 := fold_command (list_write_to_idx_write "persons" "id") id ex1_2.
(*    Compute ex1_1.
    Compute ex1_2.
    Compute ex1_3. *)

    Lemma list_to_idx_to_list_ex :
      forall attr tbl (Gstore Genv : tenv) (store env : locals) rt,
        type_of Gstore Genv tbl (TList (TRecord rt)) ->
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        attr = "id" ->
        (* repeated list_insert without any assignment command *)
        tbl = EBinop OCons (ERecord (("id", EAtom (AInt 3)) :: nil))
                (EBinop OCons (ERecord (("id", EAtom (AInt 1)) :: nil)) (EAtom (ANil None)))->
        exists l l', interp_expr store env (idx_to_list (list_to_idx attr tbl)) = VList l /\
                       interp_expr store env tbl = VList l' /\
                       Permutation l l'.
    Proof.
      intros. subst. simpl.
      unfold get_local.
      repeat (repeat rewrite map.get_put_same; simpl; rewrite map.get_put_diff; try apply eqb_neq; auto).
      repeat rewrite map.get_put_same. rewrite app_nil_r. repeat eexists. eauto.
      assert (forall T (a b : T), a :: b :: nil = app (a :: nil) (b :: nil)).
      { auto. }
      repeat rewrite H4. apply Permutation_app_comm.
    Qed.
  End WithMap.
End WithWord.
