Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.Invariant fiat2.rules.FlatmapForms fiat2.rules.CollectionTransf.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith Lia List Permutation Sorted.
Import ListNotations.

(* A key on a table: no two of its rows agree on every one of attrs.  A key on
   one attribute is the case attrs = [attr].

   The condition is written as a conjunction of per-attribute equalities, which
   is the pattern the composite dictionary index's read rule matches, and its
   cheap check, fresh_guard, has the same shape. *)

Fixpoint eq_on_attrs (attrs : list string) (e1 e2 : expr) : expr :=
  match attrs with
  | [] => EAtom (ABool true)
  | [a] => EBinop OEq (EAccess e1 a) (EAccess e2 a)
  | a :: attrs' =>
      EBinop OAnd (EBinop OEq (EAccess e1 a) (EAccess e2 a))
        (eq_on_attrs attrs' e1 e2)
  end.

(* The row's key occurs exactly once in tbl *)
Definition unique_cond (tbl : string) (attrs : list string) (row_ty : type) : expr :=
  EBinop OEq
    (EUnop OLength
       (EFlatmap LikeList (ELoc tbl) "_r2"
          (EIf (eq_on_attrs attrs (EVar "_r2") (EVar "_r"))
             (EBinop OCons (EVar "_r2") (EAtom (ANil (Some row_ty))))
             (EAtom (ANil (Some row_ty))))))
    (EAtom (AInt 1)).

Definition row_keys (attrs : list string) (v : value) : value :=
  match v with
  | VRecord rc =>
      VRecord (record_sort (List.map (fun a => (a, record_proj a rc)) attrs))
  | _ => VUnit
  end.

Definition key_filter (tbl x : string) (attrs : list string) (u : expr) : expr :=
  flatmap_filter_bag (EUnop OBagOfList (ELoc tbl)) x
    (eq_on_attrs attrs (EVar x) u) x None None.

Definition fresh_guard (tbl x : string) (attrs : list string) (u : expr) : expr :=
  EBinop OEq (key_filter tbl x attrs u) (EAtom (AEmptyBag None)).

Definition pk_row : string := "_pk_row".
Definition pk_scan : string := "_pk_scan".

(* Binding the row first leaves pk_row the only free immutable variable under
   the scan, so no capture is possible whatever the row expression is *)
Definition unique_guard_let (tbl : string) (attrs : list string) (row : expr) : expr :=
  ELet row pk_row (fresh_guard tbl pk_scan attrs (EVar pk_row)).

Section WithMap.
  Notation value := (value).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Lemma value_eqb_true_iff : forall (v v' : value), value_eqb v v' = true <-> v = v'.
  Proof.
    split; intros; subst; auto using value_eqb_eq, value_eqb_refl.
  Qed.

  Lemma length_filter_key__count_occ :
    forall (A B : Type) (dec : forall x y : B, {x = y} + {x <> y})
           (eqb : B -> B -> bool) (key : A -> B) (k : B) (l : list A),
      (forall x y, eqb x y = true <-> x = y) ->
      List.length (List.filter (fun a => eqb (key a) k) l)
      = count_occ dec (List.map key l) k.
  Proof.
    intros * H_eqb.
    induction l as [| a l IH]; cbn [List.filter List.map List.length count_occ]; auto.
    destruct (eqb (key a) k) eqn:E_b; destruct (dec (key a) k) as [E_d | E_d];
      cbn [List.length].
    1: f_equal; exact IH.
    1:{ exfalso. apply H_eqb in E_b. contradiction. }
    1:{ exfalso. apply (proj2 (H_eqb (key a) k)) in E_d. congruence. }
    1: exact IH.
  Qed.

  Lemma Forall_count_one_iff_NoDup :
    forall (A B : Type) (eqb : B -> B -> bool) (key : A -> B) (l : list A),
      (forall x y, eqb x y = true <-> x = y) ->
      (Forall (fun r => List.length
                          (List.filter (fun r2 => eqb (key r2) (key r)) l) = 1) l
       <-> NoDup (List.map key l)).
  Proof.
    intros * H_eqb.
    assert (dec : forall x y : B, {x = y} + {x <> y}).
    { intros x y. destruct (eqb x y) eqn:E.
      1: left; apply H_eqb; exact E.
      1:{ right; intro H_xy.
          apply (proj2 (H_eqb x y)) in H_xy. congruence. } }
    split.
    1:{ intros H_F.
        apply (proj2 (NoDup_count_occ' dec (List.map key l))).
        intros x H_in. rewrite in_map_iff in H_in.
        destruct H_in as [ r [ H_kr H_rin ] ]; subst.
        rewrite <- length_filter_key__count_occ with (eqb := eqb); auto.
        exact (proj1 (Forall_forall _ l) H_F r H_rin). }
    1:{ intros H_nd.
        pose proof (proj1 (NoDup_count_occ' dec (List.map key l)) H_nd) as H_cnt.
        apply (proj2 (Forall_forall _ l)). intros r H_rin.
        rewrite length_filter_key__count_occ with (dec := dec); auto.
        apply H_cnt, in_map; auto. }
  Qed.

  Lemma interp_EVar : forall (store env : locals) x,
      interp_expr store env (EVar x) = get_local env x.
  Proof. reflexivity. Qed.

  Lemma interp_ELoc : forall (store env : locals) x,
      interp_expr store env (ELoc x) = get_local store x.
  Proof. reflexivity. Qed.

  Lemma interp_EAtom : forall (store env : locals) a,
      interp_expr store env (EAtom a) = interp_atom a.
  Proof. reflexivity. Qed.

  Lemma interp_EUnop : forall (store env : locals) o e,
      interp_expr store env (EUnop o e) = interp_unop o (interp_expr store env e).
  Proof. reflexivity. Qed.

  Lemma interp_EBinop : forall (store env : locals) o e1 e2,
      interp_expr store env (EBinop o e1 e2)
      = interp_binop o (interp_expr store env e1) (interp_expr store env e2).
  Proof. reflexivity. Qed.

  Lemma interp_EFlatmap_list : forall (store env : locals) e1 x e2,
      interp_expr store env (EFlatmap LikeList e1 x e2)
      = match interp_expr store env e1 with
        | VList l1 =>
            VList (flat_map
                     (fun v => match interp_expr store (map.put env x v) e2 with
                               | VList l2 => l2
                               | _ => nil
                               end) l1)
        | _ => VUnit
        end.
  Proof. reflexivity. Qed.

  Lemma interp_EAccess : forall (store env : locals) e x,
      interp_expr store env (EAccess e x)
      = match interp_expr store env e with
        | VRecord fs => record_proj x fs
        | _ => VUnit
        end.
  Proof. reflexivity. Qed.

  Lemma interp_EIf_step : forall (store env : locals) e1 e2 e3,
      interp_expr store env (EIf e1 e2 e3)
      = match interp_expr store env e1 with
        | VBool b => if b then interp_expr store env e2 else interp_expr store env e3
        | _ => VUnit
        end.
  Proof. reflexivity. Qed.

  Lemma interp_ELet : forall (store env : locals) e1 y e2,
      interp_expr store env (ELet e1 y e2)
      = interp_expr store (map.put env y (interp_expr store env e1)) e2.
  Proof. reflexivity. Qed.

  Lemma locals_wf_list : forall (G : tenv) (E : locals) x row_ty,
      locals_wf G E -> map.get G x = Some (TList row_ty) ->
      exists l, map.get E x = Some (VList l)
                /\ Forall (fun r => type_of_value r row_ty) l.
  Proof.
    unfold locals_wf; intros * H_wf H_get.
    specialize (H_wf _ _ H_get).
    destruct (map.get E x) as [ v | ]; [ | contradiction ].
    inversion H_wf; subst. eauto.
  Qed.

  Lemma typed_rows_are_records : forall rt (l : list value),
      Forall (fun r => type_of_value r (TRecord rt)) l ->
      Forall (fun v => exists rc, v = VRecord rc) l.
  Proof.
    intros rt l H; rewrite Forall_forall in H |- *; intros v H_v.
    specialize (H v H_v); inversion H; eauto.
  Qed.

  Lemma map_fst_pairs : forall A (f : string -> A) al,
      List.map fst (List.map (fun a => (a, f a)) al) = al.
  Proof.
    induction al; cbn [List.map fst]; [ reflexivity | ].
    f_equal; assumption.
  Qed.

  Lemma record_proj_record_sort : forall (kvs : list (string * value)) a,
      NoDup (List.map fst kvs) ->
      In a (List.map fst kvs) ->
      record_proj a (record_sort kvs) = record_proj a kvs.
  Proof.
    intros kvs a Hnd Hin.
    assert (H : access_record kvs a = access_record (record_sort kvs) a).
    { apply NoDup_Permutation_access_record; auto using Permuted_record_sort. }
    unfold record_proj. rewrite H. reflexivity.
  Qed.

  Lemma record_proj_pairs : forall (f : string -> value) al a,
      In a al -> record_proj a (List.map (fun a => (a, f a)) al) = f a.
  Proof.
    induction al as [ | b al IH ]; cbn [List.map]; intros a Hin;
      [ contradiction | ].
    unfold record_proj; cbn [access_record].
    destruct (String.eqb a b) eqn:E.
    - rewrite String.eqb_eq in E; subst; reflexivity.
    - fold (record_proj a (List.map (fun a => (a, f a)) al)).
      apply IH. destruct Hin as [ E' | Hin ]; [ | exact Hin ].
      subst; rewrite String.eqb_refl in E; discriminate.
  Qed.

  Lemma row_keys_eq_iff : forall attrs rc1 rc2,
      NoDup attrs ->
      (row_keys attrs (VRecord rc1) = row_keys attrs (VRecord rc2)
       <-> Forall (fun a => record_proj a rc1 = record_proj a rc2) attrs).
  Proof.
    intros attrs rc1 rc2 Hnd; cbn [row_keys]; split.
    - intros E. injection E as E.
      apply Forall_forall; intros a Hin.
      assert (Hnd1 : NoDup (List.map fst
                              (List.map (fun a => (a, record_proj a rc1)) attrs)))
        by (rewrite map_fst_pairs; exact Hnd).
      assert (Hnd2 : NoDup (List.map fst
                              (List.map (fun a => (a, record_proj a rc2)) attrs)))
        by (rewrite map_fst_pairs; exact Hnd).
      assert (Hin1 : In a (List.map fst
                             (List.map (fun a => (a, record_proj a rc1)) attrs)))
        by (rewrite map_fst_pairs; exact Hin).
      assert (Hin2 : In a (List.map fst
                             (List.map (fun a => (a, record_proj a rc2)) attrs)))
        by (rewrite map_fst_pairs; exact Hin).
      rewrite <- (record_proj_pairs (fun a => record_proj a rc1) attrs a Hin).
      rewrite <- (record_proj_pairs (fun a => record_proj a rc2) attrs a Hin).
      rewrite <- (record_proj_record_sort _ a Hnd1 Hin1).
      rewrite <- (record_proj_record_sort _ a Hnd2 Hin2).
      rewrite E; reflexivity.
    - intros HF. do 2 f_equal.
      induction HF as [ | a attrs' Ha HF' IH ]; cbn [List.map]; [ reflexivity | ].
      rewrite Ha, IH; [ reflexivity | ].
      inversion Hnd; assumption.
  Qed.

  Lemma interp_eq_on_attrs : forall attrs (store env : locals) e1 e2 rc1 rc2,
      interp_expr store env e1 = VRecord rc1 ->
      interp_expr store env e2 = VRecord rc2 ->
      interp_expr store env (eq_on_attrs attrs e1 e2)
      = VBool (forallb
                 (fun a => value_eqb (record_proj a rc1) (record_proj a rc2)) attrs).
  Proof.
    intros attrs store env e1 e2 rc1 rc2 E1 E2.
    assert (Eacc : forall a, interp_expr store env (EAccess e1 a)
                             = record_proj a rc1).
    1:{ intro a; rewrite interp_EAccess, E1; reflexivity. }
    assert (Eacc2 : forall a, interp_expr store env (EAccess e2 a)
                              = record_proj a rc2).
    1:{ intro a; rewrite interp_EAccess, E2; reflexivity. }
    induction attrs as [ | a attrs' IH ]; cbn [eq_on_attrs forallb].
    - reflexivity.
    - destruct attrs' as [ | a' attrs'' ].
      + cbn [forallb]. rewrite interp_EBinop, Eacc, Eacc2.
        cbn [interp_binop]. rewrite Bool.andb_true_r; reflexivity.
      + rewrite interp_EBinop, IH, interp_EBinop, Eacc, Eacc2.
        cbn [interp_binop]. reflexivity.
  Qed.

  Lemma interp_eq_on_attrs_keys :
    forall attrs (store env : locals) e1 e2 rc1 rc2,
      NoDup attrs ->
      interp_expr store env e1 = VRecord rc1 ->
      interp_expr store env e2 = VRecord rc2 ->
      interp_expr store env (eq_on_attrs attrs e1 e2)
      = VBool (value_eqb (row_keys attrs (VRecord rc1))
                 (row_keys attrs (VRecord rc2))).
  Proof.
    intros attrs store env e1 e2 rc1 rc2 Hnd E1 E2.
    rewrite (interp_eq_on_attrs attrs store env e1 e2 rc1 rc2 E1 E2).
    f_equal.
    destruct (value_eqb (row_keys attrs (VRecord rc1))
                (row_keys attrs (VRecord rc2))) eqn:E.
    - apply value_eqb_eq in E.
      apply forallb_forall; intros a Hin.
      pose proof (proj1 (row_keys_eq_iff attrs rc1 rc2 Hnd) E) as HF.
      rewrite Forall_forall in HF.
      rewrite (HF a Hin); apply value_eqb_refl.
    - destruct (forallb _ attrs) eqn:Ef; [ exfalso | reflexivity ].
      rewrite forallb_forall in Ef.
      assert (HF : Forall (fun a => record_proj a rc1 = record_proj a rc2) attrs).
      1:{ apply Forall_forall; intros a Hin.
          apply value_eqb_eq, Ef, Hin. }
      rewrite (proj2 (row_keys_eq_iff attrs rc1 rc2 Hnd) HF),
        value_eqb_refl in E; discriminate.
  Qed.

  Lemma eq_on_attrs_ty : forall attrs rt e1 e2 (Gstore Genv : tenv),
      Forall (fun a => In a (List.map fst rt)) attrs ->
      type_of Gstore Genv e1 (TRecord rt) ->
      type_of Gstore Genv e2 (TRecord rt) ->
      type_of Gstore Genv (eq_on_attrs attrs e1 e2) TBool.
  Proof.
    intros attrs rt e1 e2 Gstore Genv HF E1 E2.
    induction HF as [ | a attrs' Ha HF' IH ]; cbn [eq_on_attrs].
    - apply TyEAtom; constructor.
    - apply In_access_record in Ha as [ t Et ].
      destruct attrs' as [ | a' attrs'' ].
      + eapply TyEBinop; [ apply TyOEq | | ];
          (eapply TyEAccess; [ eassumption | exact Et ]).
      + eapply TyEBinop; [ apply TyOAnd | | ].
        * eapply TyEBinop; [ apply TyOEq | | ];
            (eapply TyEAccess; [ eassumption | exact Et ]).
        * exact IH.
  Qed.

  Lemma unique_inner_interp : forall attrs row_ty (store env : locals) r v rc rv,
      NoDup attrs -> r = VRecord rc -> v = VRecord rv -> map.get env "_r" = Some r ->
      match interp_expr store (map.put env "_r2" v)
              (EIf (eq_on_attrs attrs (EVar "_r2") (EVar "_r"))
                 (EBinop OCons (EVar "_r2") (EAtom (ANil (Some row_ty))))
                 (EAtom (ANil (Some row_ty)))) with
      | VList l2 => l2
      | _ => nil
      end
      = (if value_eqb (row_keys attrs v) (row_keys attrs r) then v :: nil else nil).
  Proof.
    intros * Hnd Er Ev E_r; subst r v.
    rewrite interp_EIf_step.
    rewrite (interp_eq_on_attrs_keys attrs _ _ (EVar "_r2") (EVar "_r") rv rc Hnd).
    2:{ rewrite interp_EVar; unfold get_local; rewrite map.get_put_same;
        reflexivity. }
    2:{ rewrite interp_EVar; unfold get_local;
        rewrite map.get_put_diff by discriminate;
        rewrite E_r; reflexivity. }
    destruct (value_eqb (row_keys attrs (VRecord rv)) (row_keys attrs (VRecord rc)));
      cbn [interp_expr interp_binop interp_atom]; unfold get_local.
    - rewrite map.get_put_same; reflexivity.
    - reflexivity.
  Qed.

  Lemma unique_flat_map : forall attrs row_ty (store env : locals) r rc l,
      NoDup attrs -> r = VRecord rc -> map.get env "_r" = Some r ->
      Forall (fun v => exists rv, v = VRecord rv) l ->
      flat_map
        (fun v =>
           match interp_expr store (map.put env "_r2" v)
                   (EIf (eq_on_attrs attrs (EVar "_r2") (EVar "_r"))
                      (EBinop OCons (EVar "_r2") (EAtom (ANil (Some row_ty))))
                      (EAtom (ANil (Some row_ty)))) with
           | VList l2 => l2
           | _ => nil
           end) l
      = List.filter (fun r2 => value_eqb (row_keys attrs r2) (row_keys attrs r)) l.
  Proof.
    intros * Hnd Er E_r HF.
    induction HF as [ | v l [ rv Ev ] HF' IH ];
      cbn [flat_map List.filter]; [ reflexivity | ].
    rewrite (unique_inner_interp attrs row_ty store env r v rc rv Hnd Er Ev E_r), IH.
    destruct (value_eqb (row_keys attrs v) (row_keys attrs r)); reflexivity.
  Qed.

  Lemma unique_cond_row_iff : forall tbl attrs row_ty (store : locals) l r rc,
      NoDup attrs -> map.get store tbl = Some (VList l) -> r = VRecord rc ->
      Forall (fun v => exists rv, v = VRecord rv) l ->
      interp_expr store (map.put map.empty "_r" r) (unique_cond tbl attrs row_ty) = VBool true
      <-> List.length
            (List.filter (fun r2 => value_eqb (row_keys attrs r2) (row_keys attrs r)) l)
          = 1.
  Proof.
    intros * Hnd E_tbl Er H_rec. unfold unique_cond.
    rewrite interp_EBinop, interp_EUnop, interp_EFlatmap_list, interp_ELoc.
    unfold get_local at 1. rewrite E_tbl. cbn beta iota.
    rewrite (unique_flat_map attrs row_ty store (map.put map.empty "_r" r) r rc l Hnd Er
               (map.get_put_same _ _ _) H_rec).
    cbn [interp_unop interp_binop interp_atom].
    split.
    1:{ intro H. injection H as H.
        apply value_eqb_true_iff in H. injection H as H. lia. }
    1:{ intro H. rewrite H. reflexivity. }
  Qed.

  Theorem unique_cond_holds_iff : forall tbl attrs row_ty (store : locals) l,
      NoDup attrs ->
      map.get store tbl = Some (VList l) ->
      Forall (fun v => exists rv, v = VRecord rv) l ->
      inv_holds store (ConstraintInv tbl nil "_r" (unique_cond tbl attrs row_ty))
      <-> NoDup (List.map (row_keys attrs) l).
  Proof.
    intros * Hnd E_tbl H_rec.
    cbn [inv_holds value_at]. rewrite E_tbl.
    rewrite <- (Forall_count_one_iff_NoDup value value value_eqb (row_keys attrs) l
                  value_eqb_true_iff).
    rewrite !Forall_forall.
    split; intros H_F r H_r; specialize (H_F r H_r);
      destruct (proj1 (Forall_forall _ l) H_rec r H_r) as [ rc Er ].
    1: apply (unique_cond_row_iff tbl attrs row_ty store l r rc Hnd E_tbl Er H_rec); exact H_F.
    1: apply (unique_cond_row_iff tbl attrs row_ty store l r rc Hnd E_tbl Er H_rec); exact H_F.
  Qed.

  Section WithTable.
    Context (tbl x : string).

    Lemma fresh_guard_ty : forall attrs rt u (Gstore Genv : tenv),
        tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
        Forall (fun a => In a (List.map fst rt)) attrs ->
        map.get Gstore tbl = Some (TList (TRecord rt)) ->
        type_of Gstore Genv u (TRecord rt) ->
        free_immut_in x u = false ->
        type_of Gstore Genv (fresh_guard tbl x attrs u) TBool.
    Proof.
      intros * H_Gs H_Ge H_rt HF H_tbl H_u H_fr.
      unfold fresh_guard, key_filter.
      econstructor.
      1: apply TyOEq.
      2:{ constructor. apply TyAEmptyBag'. exact H_rt. }
      econstructor.
      1:{ econstructor; [ constructor | ]. constructor. exact H_tbl. }
      econstructor.
      1:{ eapply eq_on_attrs_ty.
          1: exact HF.
          1: constructor; apply map.get_put_same.
          1: apply not_free_immut_put_ty2; [ exact H_fr | exact H_u ]. }
      1:{ econstructor.
          1: apply TyOBagInsert.
          1: constructor; apply TyAEmptyBag'; exact H_rt.
          1: constructor; apply map.get_put_same. }
      1:{ constructor. apply TyAEmptyBag'. exact H_rt. }
    Qed.

    Lemma interp_key_filter : forall attrs (store env : locals) l u rv,
        NoDup attrs ->
        free_immut_in x u = false ->
        map.get store tbl = Some (VList l) ->
        interp_expr store env u = VRecord rv ->
        Forall (fun v => exists rc, v = VRecord rc) l ->
        interp_expr store env (key_filter tbl x attrs u)
        = VBag (list_to_bag
                  (filter (fun v => value_eqb (row_keys attrs v)
                                      (row_keys attrs (VRecord rv)))
                     (bag_to_list (list_to_bag l)))).
    Proof.
      intros * Hnd H_fr E_tbl E_u H_rec.
      assert (E_bag : interp_expr store env (EUnop OBagOfList (ELoc tbl))
                      = VBag (list_to_bag l)).
      { cbn [interp_expr]; unfold get_local; rewrite E_tbl; reflexivity. }
      unfold key_filter.
      rewrite interp_flatmap_filter_bag, E_bag.
      do 2 f_equal.
      apply filter_ext_in; intros v H_v.
      assert (H_vl : In v l).
      1:{ eapply Permutation_in;
          [ apply list_to_bag_to_list_Permutation | exact H_v ]. }
      destruct (proj1 (Forall_forall _ l) H_rec v H_vl) as [ rc Ev ].
      rewrite (interp_eq_on_attrs_keys attrs store (map.put env x v)
                 (EVar x) u rc rv Hnd).
      2:{ rewrite interp_EVar; unfold get_local; rewrite map.get_put_same;
          rewrite Ev; reflexivity. }
      2:{ rewrite <- (not_free_immut_put_sem u x store env v H_fr); exact E_u. }
      rewrite Ev; reflexivity.
    Qed.

    Lemma fresh_guard_iff : forall attrs (store env : locals) l u rv,
        NoDup attrs ->
        free_immut_in x u = false ->
        map.get store tbl = Some (VList l) ->
        interp_expr store env u = VRecord rv ->
        Forall (fun v => exists rc, v = VRecord rc) l ->
        (interp_expr store env (fresh_guard tbl x attrs u) = VBool true
         <-> ~ In (row_keys attrs (VRecord rv)) (List.map (row_keys attrs) l)).
    Proof.
      intros * Hnd H_fr E_tbl E_u H_rec.
      unfold fresh_guard.
      rewrite interp_EBinop, interp_EAtom,
        (interp_key_filter attrs store env l u rv Hnd H_fr E_tbl E_u H_rec).
      cbn [interp_binop interp_atom].
      split.
      1:{ intros H_eq H_in.
          lazymatch goal with
            H: VBool _ = VBool _ |- _ => injection H as H_eq'
          end.
          apply value_eqb_eq in H_eq'.
          lazymatch goal with H: VBag _ = VBag _ |- _ => injection H as H_nil end.
          apply list_to_bag_nil in H_nil.
          apply in_map_iff in H_in as [ r [ E_key H_r ] ].
          eapply (Permutation_in _
                    (Permutation_sym (list_to_bag_to_list_Permutation l))) in H_r.
          lazymatch goal with
            H: filter ?p ?L = nil |- _ =>
              assert (H_f : In r (filter p L))
          end.
          1:{ apply filter_In; split; [ assumption | ].
              rewrite E_key; apply value_eqb_refl. }
          rewrite H_nil in H_f; destruct H_f. }
      1:{ intro H_out. f_equal.
          lazymatch goal with
            |- value_eqb (VBag ?b) _ = true => assert (E_nil : b = nil)
          end.
          1:{ lazymatch goal with
                |- list_to_bag ?L = nil => destruct L as [ | r L' ] eqn:E_filter
              end.
              1: reflexivity.
              exfalso.
              assert (H_r : In r (filter
                 (fun v => value_eqb (row_keys attrs v)
                             (row_keys attrs (VRecord rv)))
                 (bag_to_list (list_to_bag l))))
                by (rewrite E_filter; cbn; auto).
              apply filter_In in H_r as [ H_r H_key ].
              apply value_eqb_eq in H_key.
              apply H_out. rewrite <- H_key. apply in_map.
              eapply Permutation_in;
                [ apply list_to_bag_to_list_Permutation | exact H_r ]. }
          rewrite E_nil; apply value_eqb_refl. }
    Qed.
  End WithTable.

  Lemma unique_guard_let_ty : forall tbl attrs rt row (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
      Forall (fun a => In a (List.map fst rt)) attrs ->
      map.get Gstore tbl = Some (TList (TRecord rt)) ->
      type_of Gstore Genv row (TRecord rt) ->
      type_of Gstore Genv (unique_guard_let tbl attrs row) TBool.
  Proof.
    intros * H_Gs H_Ge H_rt HF H_tbl H_row.
    unfold unique_guard_let. econstructor.
    1: exact H_row.
    eapply fresh_guard_ty with (rt := rt).
    1: exact H_Gs.
    1: apply tenv_wf_step; [ exact H_Ge | exact H_rt ].
    1: exact H_rt.
    1: exact HF.
    1: exact H_tbl.
    1: constructor; apply map.get_put_same.
    1: reflexivity.
  Qed.

  Lemma unique_guard_let_iff : forall tbl attrs row (store env : locals) l rv,
      NoDup attrs ->
      map.get store tbl = Some (VList l) ->
      interp_expr store env row = VRecord rv ->
      Forall (fun v => exists rc, v = VRecord rc) l ->
      interp_expr store env (unique_guard_let tbl attrs row) = VBool true
      <-> ~ In (row_keys attrs (VRecord rv)) (List.map (row_keys attrs) l).
  Proof.
    intros * Hnd E_tbl E_row H_rec.
    unfold unique_guard_let. rewrite interp_ELet.
    apply (fresh_guard_iff tbl pk_scan attrs store _ l (EVar pk_row) rv Hnd).
    1: reflexivity.
    1: exact E_tbl.
    1: rewrite interp_EVar; unfold get_local; rewrite map.get_put_same; exact E_row.
    1: exact H_rec.
  Qed.
End WithMap.
