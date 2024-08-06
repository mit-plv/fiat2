Require Import fiat2.Language fiat2.Value fiat2.Interpret fiat2.TypeSystem fiat2.TypeSound.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import List ZArith String.

(* below 6 lemmas should be moved to coq utils
       used in relational algebra filter/join conversions *)

(* filter of a flat_map = flat_map where filter is applied in the flat_map function*)
Lemma filter_flat_map {A B : Type} (p : B -> bool) (f : A -> list B) (l : list A) :
  filter p (flat_map f l) = flat_map (fun x => filter p (f x)) l.
  induction l as [| h t IHn].
  - simpl. reflexivity.
  - simpl. rewrite filter_app. f_equal. apply IHn.
Qed.

(* for maps from A->A: filtering a map = doing a map on the filtered list*)
Lemma filter_map_commute {A : Type} (f : A -> A) (p : A -> bool) (l : list A) :
  filter p (List.map f l) = List.map f (filter (fun x => p (f x)) l).
  induction l as [| h t IHn].
  - simpl. reflexivity.
  - simpl. destruct (p (f h)).
    + simpl. f_equal. apply IHn.
    + apply IHn.
Qed.

(* filter on another filtered list = filter on original list where function "and"s the two predicates*)
Lemma filter_filter {A : Type} (p1 p2 : A -> bool) (l : list A) :
  filter p1 (filter p2 l) = filter (fun x => andb (p1 x) (p2 x)) l.
  induction l as [| h t IHn].
  - simpl. reflexivity.
  - simpl. destruct (p2 h).
    + simpl. destruct (p1 h).
      * simpl. f_equal. apply IHn.
      * simpl. apply IHn.
    + destruct (p1 h); apply IHn.
Qed.

(* flat_map of a filtered list = flat_map where filter is applied in the flat_map function*)
Lemma flat_map_filter {A B : Type} (f : A -> list B) (p : A -> bool) (l : list A) :
  flat_map f (filter p l) = flat_map (fun x => if p x then f x else @nil B) l.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (p h) eqn:H.
    + simpl. rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma filter_nil : forall (A : Type) (f : A -> bool) (l : list A),
    (forall x : A, In x l -> f x = false) -> filter f l = nil.
  intros A f l H.
  induction l as [|h t IH].
  - simpl. reflexivity.
  - simpl. rewrite H.
    + apply IH. intros h' H'. apply H. right. apply H'.
    + left. reflexivity.
Qed.

Lemma map_nil : forall (A B : Type) (f : A -> B) (l : list A),
    l = nil -> List.map f l = nil.
  intros A B f l H.
  rewrite H. simpl. reflexivity.
Qed.


Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.

  Section WithMap.
    Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
    Local Notation value := (value (word := word)).
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    Lemma typeof_to_typeofvalue : forall (store env: locals) (Gstore Genv: tenv) (e: expr) (t: type),
      type_of Gstore Genv e t -> type_of_value (interp_expr store env e) t.
    Admitted.

    Theorem filter_into_join : forall (store env: locals) (Gstore Genv: tenv) (db1 db2 pj rj pf: expr) (xj yj xf: string) (t tx ty: type),
      type_of Gstore (map.put (map.put Genv xj tx) yj ty) pj (TList t) ->
      let pnew := EBinop OAnd pj (ELet rj xf pf) in
      interp_expr store env (EFilter (EJoin db1 db2 xj yj pj rj) xf pf)
      = interp_expr store env (EJoin db1 db2 xj yj pnew rj).
    Proof.
      intros store env Gstore Genv db1 db2 pj rj pf xj yj xf t tx ty H. simpl.
      destruct (interp_expr store env db1); try reflexivity.
      destruct (interp_expr store env db2); try reflexivity. f_equal.
      rewrite filter_flat_map. apply flat_map_ext. intros a.
      rewrite filter_map_commute. f_equal.
      rewrite filter_filter. apply filter_ext. intros b.
      apply typeof_to_typeofvalue with store (map.put (map.put env xj a) yj b) Gstore (map.put (map.put Genv xj tx) yj ty) pj (TList t) in H.
      inversion H. rewrite Bool.andb_false_r. simpl. reflexivity.
    Qed.

    Lemma interp_invariant : forall (store env: locals) (Gstore Genv: tenv) (db: expr) (k: string) (v: value) (t: type),
      type_of Gstore Genv db t -> map.get Genv k = None ->
      interp_expr store env db = interp_expr store (map.put env k v) db.
    Proof.
      intros store env0 Gstore Genv db k v t T K.
      generalize env0 as env.
      induction T; intros env; simpl; try reflexivity.
      - unfold get_local. destruct (eqb k x) eqn:KX.
        + exfalso. rewrite String.eqb_eq in KX. rewrite KX in K. rewrite K in H. discriminate H.
        + rewrite String.eqb_neq in KX. rewrite map.get_put_diff.
          * reflexivity.
          * symmetry. apply KX.
      - rewrite IHT.
        + reflexivity.
        + apply K.
      - rewrite IHT1.
        + rewrite IHT2.
          * reflexivity.
          * apply K.
        + apply K.
      - rewrite IHT1.
        + rewrite IHT2.
          * rewrite IHT3.
            -- reflexivity.
            -- apply K.
          * apply K.
        + apply K.
      - rewrite <- IHT1.
        + destruct (eqb k x) eqn:KX.
          * rewrite String.eqb_eq in KX. rewrite KX.
            rewrite Properties.map.put_put_same. reflexivity.
          * rewrite String.eqb_neq in KX. rewrite IHT2.
            -- rewrite Properties.map.put_comm.
               ++ reflexivity.
               ++ symmetry. apply KX.
            -- rewrite map.get_put_diff.
               ++ apply K.
               ++ apply KX.
        + apply K.
      - rewrite <- IHT1.
        + destruct (interp_expr store env e1) eqn:H; try reflexivity.
          f_equal. apply flat_map_ext. intros a. destruct (eqb k x) eqn:KX.
          * rewrite String.eqb_eq in KX. rewrite KX.
            rewrite Properties.map.put_put_same. reflexivity.
          * rewrite String.eqb_neq in KX. rewrite IHT2.
            -- rewrite Properties.map.put_comm.
               ++ reflexivity.
               ++ symmetry. apply KX.
            -- rewrite map.get_put_diff.
               ++ apply K.
               ++ apply KX.
        + apply K.
      - rewrite <- IHT1. (*EFold*)
        + destruct (interp_expr store env e1) eqn:H; try reflexivity. f_equal.
          * apply FunctionalExtensionality.functional_extensionality. intros a.
            apply FunctionalExtensionality.functional_extensionality. intros b.
            destruct (eqb y k) eqn:KY.
            -- admit. (*admitted due to 'rewrite IHT3' making 'set k=v' outermost*)
            -- rewrite String.eqb_neq in KY. destruct (eqb x k) eqn:KX.
               ++ admit.
               ++ rewrite String.eqb_neq in KX. rewrite IHT3.
                  ** rewrite Properties.map.put_comm.
                     --- rewrite Properties.map.put_comm with (k1:=x) (k2:=k).
                         +++ reflexivity.
                         +++ apply KX.
                     --- apply KY.
                  ** rewrite map.get_put_diff.
                     --- rewrite map.get_put_diff.
                         +++ apply K.
                         +++ symmetry. apply KX.
                     --- symmetry. apply KY.
          * apply IHT2.
            -- apply K.
        + apply K.
      - f_equal. f_equal. f_equal. apply FunctionalExtensionality.functional_extensionality.
        intros x. admit. (*ERecord, nested induction*)
      - rewrite IHT.
        + reflexivity.
        + apply K.
      - f_equal. f_equal. f_equal. apply FunctionalExtensionality.functional_extensionality.
        intros x. admit. (*EDict, nested induction*)
      - rewrite <- IHT1.
        + destruct (interp_expr store env d) eqn:H; try reflexivity. rewrite <- IHT2.
          * rewrite <- IHT3.
            -- reflexivity.
            -- apply K.
          * apply K.
        + apply K.
      - rewrite <- IHT1.
        + destruct (interp_expr store env d) eqn:H; try reflexivity. intuition congruence.
        + apply K.
      - rewrite <- IHT1.
        + destruct (interp_expr store env d) eqn:H; try reflexivity.  intuition congruence.
        + apply K.
      - admit.
      - rewrite <- IHT1.
        + destruct (interp_expr store env e) eqn:H; try reflexivity.
          f_equal. apply filter_ext. intros a. destruct (eqb k x) eqn:KX.
          * rewrite String.eqb_eq in KX. rewrite KX.
            rewrite Properties.map.put_put_same. reflexivity.
          * rewrite String.eqb_neq in KX. rewrite IHT2.
            -- rewrite Properties.map.put_comm.
               ++ reflexivity.
               ++ symmetry. apply KX.
            -- rewrite map.get_put_diff.
               ++ apply K.
               ++ apply KX.
        + apply K.
      - rewrite <- IHT1. (*EJoin*)
        + destruct (interp_expr store env e1) eqn:H1; try reflexivity. rewrite <- IHT2.
          * destruct (interp_expr store env e2) eqn:H2; try reflexivity.
            f_equal. apply flat_map_ext. intros a. destruct (eqb k y) eqn:KY.
            -- admit. (*admitted due to 'rewrite IHT4' making 'set k=v' outermost*)
            -- rewrite String.eqb_neq in KY. destruct (eqb k x) eqn:KX.
               ++ admit.
               ++ rewrite String.eqb_neq in KX. f_equal.
                  ** apply FunctionalExtensionality.functional_extensionality. intros b. rewrite IHT4.
                     --- rewrite Properties.map.put_comm.
                         +++ rewrite Properties.map.put_comm with (k1:=k) (k2:=x); congruence.
                         +++ congruence.
                     --- rewrite !map.get_put_diff; assumption.
                  ** apply filter_ext. intros b. rewrite IHT3.
                     --- rewrite Properties.map.put_comm.
                         +++ rewrite Properties.map.put_comm with (k1:=k) (k2:=x); congruence.
                         +++ congruence.
                     --- rewrite !map.get_put_diff; assumption.
          * apply K.
        + apply K.
      - rewrite <- IHT1.
        + destruct (interp_expr store env e) eqn:H; try reflexivity. f_equal. f_equal.
          apply FunctionalExtensionality.functional_extensionality. intros a.
          destruct (eqb k x) eqn:KX.
          * rewrite String.eqb_eq in KX. rewrite KX. rewrite Properties.map.put_put_same. reflexivity.
          * rewrite String.eqb_neq in KX. rewrite IHT2.
            -- rewrite Properties.map.put_comm.
               ++ reflexivity.
               ++ symmetry. apply KX.
            -- rewrite map.get_put_diff; assumption.
        + apply K.
    Admitted.

    Theorem filters_into_join : forall (store env: locals) (Gstore Genv: tenv) (db1 db2 p1 p2 pj rj: expr) (x y: string) (tx ty: type),
      x <> y ->
      map.get Genv x = None ->
      map.get Genv y = None ->
      type_of Gstore (map.put Genv x tx) p1 TBool ->
      type_of Gstore (map.put Genv y ty) p2 TBool ->
      type_of Gstore (map.put (map.put Genv x tx) y ty) pj TBool ->
      let pnew := EBinop OAnd pj (EBinop OAnd p1 p2) in
      interp_expr store env (EJoin (EFilter db1 x p1) (EFilter db2 y p2) x y pj rj)
      = interp_expr store env (EJoin db1 db2 x y pnew rj).
    Proof.
      intros store env Gstore Genv db1 db2 p1 p2 pj rj x y tx ty EXY EX EY T1 T2 TJ. simpl.
      destruct (interp_expr store env db1) eqn: DB1; try reflexivity.
      destruct (interp_expr store env db2) eqn: DB2; try reflexivity. f_equal.
      rewrite flat_map_filter. apply flat_map_ext. intros a.
      apply typeof_to_typeofvalue with store (map.put env x a) Gstore (map.put Genv x tx) p1 TBool in T1 as T1'.
      inversion T1'. symmetry in H0. destruct b.
      - f_equal. rewrite filter_filter. apply filter_ext_in. intros b HB.
        (*apply typeof_to_typeofvalue with (store:=store) (env:=set_local env x a) in TJ as TJ'.*)
        apply typeof_to_typeofvalue with store (map.put (map.put env x a) y b) Gstore (map.put (map.put Genv x tx) y ty) pj TBool in TJ as TJ'.
        inversion TJ'. symmetry in H1. simpl.
        rewrite interp_invariant with store (map.put env x a) Gstore (map.put Genv x tx) p1 y b TBool in H0.
        + rewrite H0. simpl.
          apply typeof_to_typeofvalue with store (map.put env y b) Gstore (map.put Genv y ty) p2 TBool in T2 as T2'.
          inversion T2'. symmetry in H2. rewrite Properties.map.put_comm.
          * rewrite interp_invariant with store (map.put env y b) Gstore (map.put Genv y ty) p2 x a TBool in H2.
            -- rewrite H2. reflexivity.
            -- apply T2.
            -- rewrite map.get_put_diff.
               ++ apply EX.
               ++ apply EXY.
          * apply EXY.
        + apply T1.
        + rewrite map.get_put_diff.
          * apply EY.
          * symmetry. apply EXY.
      - symmetry. apply map_nil. apply filter_nil. intros b HB. unfold apply_bool_binop.
        destruct (interp_expr store (map.put (map.put env x a) y b) pj) eqn:H4; try reflexivity.
        rewrite interp_invariant with store (map.put env x a) Gstore (map.put Genv x tx) p1 y b TBool in H0.
        + rewrite H0.
          destruct (interp_expr store (map.put (map.put env x a) y b) p2) eqn:H5; try reflexivity.
          apply Bool.andb_false_r.
        + apply T1.
        + rewrite map.get_put_diff.
          * apply EY.
          * symmetry. apply EXY.
    Qed.

    Section EnvGenvRelation. (*env-genv relation definitions and related proofs
                              for possible use in filter/join conversions (not currently used)*)
    Definition sub_domain1 (env: locals) (Genv: tenv) : Prop := (* in env -> in Genv *)
      forall (k: string),
        (exists v: value, map.get env k = Some v) -> (exists t: type, map.get Genv k = Some t).

    Definition sub_domain2 (env: locals) (Genv: tenv) : Prop := (* in Genv -> in env *)
      forall (k: string),
        (exists t: type, map.get Genv k = Some t) -> (exists v: value, map.get env k = Some v).

    Definition same_domain2 (env: locals) (Genv: tenv) : Prop :=
      sub_domain1 env Genv /\ sub_domain2 env Genv.

    Definition env_genv_relation (env: locals) (Genv: tenv) : Prop :=
      same_domain2 env Genv /\
      forall (k: string) (v: value) (t: type),
        (map.get env k = Some v) -> (map.get Genv k = Some t) -> type_of_value v t.

    Lemma same_domain_inductive : forall (env: locals) (Genv: tenv) (x: string) (a: value) (tx: type),
        same_domain2 env Genv ->
        same_domain2 (map.put env x a) (map.put Genv x tx).
      intros env Genv x a tx [EG1 EG2]. split.
      - unfold sub_domain1. intros k [v EV]. destruct (eqb k x) eqn:KX.
        + rewrite String.eqb_eq in KX. rewrite KX. exists tx. apply map.get_put_same.
        + rewrite String.eqb_neq in KX. rewrite map.get_put_diff.
          * apply EG1. rewrite map.get_put_diff in EV.
            -- exists v. apply EV.
            -- apply KX.
          * apply KX.
      - unfold sub_domain2. intros k [t EV]. destruct (eqb k x) eqn:KX.
        + rewrite String.eqb_eq in KX. rewrite KX. exists a. apply map.get_put_same.
        + rewrite String.eqb_neq in KX. rewrite map.get_put_diff.
          * apply EG2. rewrite map.get_put_diff in EV.
            -- exists t. apply EV.
            -- apply KX.
          * apply KX. Qed.

    Lemma env_genv_inductive: forall (env: locals) (Genv: tenv) (x: string) (a: value) (tx: type),
      type_of_value a tx ->
      (forall (k : string) (v : value) (t : type),
        map.get env k = Some v -> map.get Genv k = Some t -> type_of_value v t) ->
      forall (k : string) (v : value) (t : type),
        map.get (map.put env x a) k = Some v ->
        map.get (map.put Genv x tx) k = Some t -> type_of_value v t.
    intros env Genv x a tx T EG k v t KV KT. destruct (eqb k x) eqn:KX.
    - rewrite String.eqb_eq in KX. rewrite KX in KV, KT.
      rewrite map.get_put_same in KV. rewrite map.get_put_same in KT. inversion KV. inversion KT.
      rewrite <- H0. rewrite <- H1. apply T.
    - rewrite String.eqb_neq in KX. apply EG with k.
      + rewrite map.get_put_diff in KV.
        * apply KV.
        * apply KX.
      + rewrite map.get_put_diff in KT.
        * apply KT.
        * apply KX. Qed.
    End EnvGenvRelation.
  End WithMap.
End WithWord.
