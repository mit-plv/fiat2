Require Import fiat2.Language fiat2.Value fiat2.Interpret fiat2.TypeSystem fiat2.TypeSound fiat2.Examples.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import coqutil.Datatypes.List.
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

(* map of a flat map = a flat map where map function is composed with flat map function *)
Lemma map_flat_map :
  forall (A B C : Type) (f : B -> C) (g : A -> list B) (l : list A),
    map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof.
  intros A B C f g l.
  induction l as [| x xs IH].
  - simpl. reflexivity.
  - simpl. rewrite map_app. f_equal. apply IH.
Qed.

(* map ext_in when lists aren't the same*)
Theorem map_ext_in_eq :
  forall (A B : Type) (f g : A -> B) (l1 l2 : list A),
    l1 = l2 -> (forall a : A, In a l1 -> f a = g a) -> map f l1 = map g l2.
Proof.
  intros A B f g l1 l2 H_eq H_in.
  rewrite H_eq. apply map_ext_in. rewrite <- H_eq. apply H_in.
Qed.

(* flat map of a map = flat map where flat map function is composed with map function *)
Lemma flat_map_map: forall {A B C: Type} (f: A -> B) (g: B -> list C) (l: list A),
  flat_map g (map f l) = flat_map (fun x => g (f x)) l.
Proof.
  intros A B C f g l.
  induction l as [| x xs IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma filter_cons {A : Type} (f : A -> bool) (x : A) (xs : list A) :
  filter f (x :: xs) =
  if f x then x :: filter f xs else filter f xs.
Proof.
  simpl.
  destruct (f x).
  - reflexivity.
  - reflexivity.
Qed.

Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.

  Section WithMap.
    Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
    Local Notation value := (value (word := word)).
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    Definition option_append (o1 o2: option (list string)) : option (list string) :=
      match o1, o2 with
      | Some l1, Some l2 => Some (dedup String.eqb (l1 ++ l2))
      | _, _ => None
      end.

    (* added shadowing check ex: ELet e1 x1 e2. if x = x1, then e2 uses x1's value instead of x's value so don't need cols e2
       return list of columns used in expr "ex" of the record stored in string "x" *)
    Fixpoint cols (x: string) (ex: expr) : option (list string) :=
      match ex with
      | EVar y => if string_dec y x then None else Some nil (* EVar x could use all columns, return None*)
      | ELoc _ => Some nil
      | EAtom _ => Some nil
      | EUnop _ e => cols x e
      | EBinop _ e1 e2 => option_append (cols x e1) (cols x e2)
      | EIf e1 e2 e3 => option_append (cols x e3) (option_append (cols x e1) (cols x e2))
      | ELet e1 x1 e2 => if string_dec x x1 then (cols x e1) else option_append (cols x e1) (cols x e2)
      | EFlatmap e1 x1 e2 => if string_dec x x1 then (cols x e1) else option_append (cols x e1) (cols x e2)
      | EFold e1 e2 x1 x2 e3 => if Sumbool.sumbool_or _ _ _ _ (string_dec x x1) (string_dec x x2) then option_append (cols x e1) (cols x e2) else option_append (cols x e3) (option_append (cols x e1) (cols x e2))
      | ERecord l => fold_right (fun val acc => option_append (cols x (snd val)) acc) (Some nil) l
      | EAccess (EVar x1) y => if string_dec x1 x then Some (y :: nil) else Some nil
      | EAccess e y => cols x e
      | EDict l => fold_right (fun val acc => option_append (option_append (cols x (snd val)) (cols x (fst val))) acc) (Some nil) l
      | EInsert d k v => option_append (cols x v) (option_append (cols x d) (cols x k))
      | EDelete d k => option_append (cols x d) (cols x k)
      | ELookup d k => option_append (cols x d) (cols x k)
      | EOptMatch e en x1 es => if string_dec x x1 then option_append (cols x e) (cols x en) else option_append (cols x e) (option_append (cols x en) (cols x es))
      | EDictFold d e0 x1 x2 x3 e => if Sumbool.sumbool_or _ _ _ _ (Sumbool.sumbool_or _ _ _ _ (string_dec x x2) (string_dec x x3)) (string_dec x x1) then option_append (cols x d) (cols x e0) else option_append (cols x e) (option_append (cols x d) (cols x e0))
      | ESort l => cols x l
      | EFilter e x1 p => if string_dec x x1 then (cols x e) else option_append (cols x e) (cols x p)
      | EJoin e1 e2 x1 x2 p r => if Sumbool.sumbool_or _ _ _ _ (string_dec x x1) (string_dec x x2) then option_append (cols x e1) (cols x e2) else option_append (cols x r) (option_append (cols x p) (option_append (cols x e1) (cols x e2)))
      | EProj e x1 r => if string_dec x x1 then (cols x e) else option_append (cols x e) (cols x r)
      end.
    
    Theorem proj_into_join: forall (store env: locals) (Gstore Genv: tenv) (t1 t2 p r rp: expr) (x y xp: string),
       x <> y ->
       xp <> x ->
       xp <> y ->
       free_immut_in x rp = false ->
       free_immut_in y rp = false ->
       let rnew := ELet r xp rp in
       interp_expr store env (EProj (EJoin t1 t2 x y p r) xp rp) =
       interp_expr store env (EJoin t1 t2 x y p rnew).
    Proof.
      intros store env Gstore Genv t1 t2 p r rp x y xp XY XPX XPY HX HY. simpl.
      destruct (interp_expr store env t1) eqn:T1; try reflexivity.
      destruct (interp_expr store env t2) eqn:T2; try reflexivity. f_equal.
      rewrite map_flat_map. apply flat_map_ext. intros a. rewrite map_map. f_equal.
      apply FunctionalExtensionality.functional_extensionality. intros b.
      rewrite not_free_immut_put_sem with (x:=x) (v:=a) (e:=rp).
      - rewrite not_free_immut_put_sem with (x:=y) (v:=b) (e:=rp).
        + rewrite Properties.map.put_put_diff with (k1:=xp).
          * rewrite Properties.map.put_put_diff with (k1:=xp).
            -- reflexivity.
            -- apply XPY.
          * apply XPX.
        + apply HY.
      - apply HX.
    Qed.

    Definition make_record (x: string) (cols: list string) : expr :=
      ERecord (map (fun k => (k, EAccess (EVar x) k)) cols).
    
    (* says that for all columns, lists a and b have the same values
       = everything in a is also in b (incl l1 l2) and
         everything in columns is also in a (incl columns l1)*)
    Definition relation (a: value) (b: value) (columns: list string): Prop :=
      match a, b with
      | VRecord l1, VRecord l2 => incl l1 l2 /\ incl columns (map fst l1)
      | _, _  => False
      end.

    Lemma dedup_incl: forall (l l0: list string) (columns: list string),
        dedup eqb (l ++ l0) = columns ->
        incl l columns /\ incl l0 columns.
      intros l l0 columns H. rewrite <- H. unfold incl. split.
      - intros. rewrite <- dedup_preserves_In. apply in_or_app. left. assumption.
      - intros. rewrite <- dedup_preserves_In. apply in_or_app. right. assumption.
    Qed.

    Lemma incl_dedup: forall (l l0: list string) (columns: list string),
        incl (dedup eqb (l ++ l0)) columns ->
        incl l columns /\ incl l0 columns.
      intros l l0 columns H. unfold incl in *. split.
      - intros a HA. apply H. rewrite <- dedup_preserves_In. apply in_or_app. left. apply HA.
      - intros a HA. apply H. rewrite <- dedup_preserves_In. apply in_or_app. right. apply HA.
    Qed.
        
    Lemma rel_step: forall (a a': value) (l columns: list string),
        incl l columns -> relation a a' columns -> relation a a' l.
      intros a a' l columns HC HR. unfold relation.
      destruct a eqn:H1; try inversion HR. destruct a' eqn:H2; try inversion HR. split; try apply H.
      unfold relation in HR. apply incl_tran with (m:=columns); assumption.
    Qed.

    Lemma subcols_record: forall (x s: string) (columns: list string) (e: expr) (l: list (string * expr)),
        fold_right (fun (val: string * expr) (acc: option (list string)) =>
          option_append (cols x (snd val)) acc) (Some nil) l = Some columns ->
        In (s, e) l -> exists cols2, cols x e = Some cols2 /\ incl cols2 columns.
      intros x s columns e l. generalize dependent columns. induction l; intros.
      - contradiction.
      - simpl in *. destruct H0.
        + rewrite H0 in H. simpl in H. destruct (cols x e) eqn:C.
          * exists l0. split; try reflexivity. remember (fold_right
           (fun (val : string * expr) (acc : option (list string)) =>
              option_append (cols x (snd val)) acc) (Some nil) l) as l1. unfold option_append in H. destruct l1.
            -- injection H as H. apply dedup_incl with (l0:=l1). apply H.
            -- inversion H.
          * simpl in H. inversion H.
        + remember (fold_right (fun (val : string * expr) (acc : option (list string)) =>
                    option_append (cols x (snd val)) acc) (Some nil) l) as l1. destruct l1 eqn:A.
          * subst. assert (H2 := IHl l0 eq_refl H0). destruct H2 as [cols2 H2]. destruct H2. exists cols2. split; try assumption.
            unfold option_append in H. destruct (cols x (snd a)).
            -- injection H as H. apply dedup_incl in H. destruct H. apply incl_tran with (m:=l0); assumption.
            -- congruence.
          * unfold option_append in H. destruct (cols x (snd a)); congruence.
    Qed.

   Lemma subcols_dict: forall (x: string) (columns: list string) (e1 e2: expr) (l: list (expr * expr)),
         fold_right (fun (val: expr * expr) (acc: option (list string)) =>
          (option_append (option_append (cols x (snd val)) (cols x (fst val))) acc))      
          (Some nil) l = Some columns ->
          In (e1, e2) l -> (exists cols1, cols x e1 = Some cols1 /\ incl cols1 columns)
                     /\ (exists cols2, cols x e2 = Some cols2 /\ incl cols2 columns).
     intros x columns e1 e2 l. generalize dependent columns. induction l; intros.
     - contradiction.
     - simpl in *. destruct H0.
       + rewrite H0 in H. simpl in *. destruct (cols x e2) eqn:C2; simpl in *; try congruence.
         destruct (cols x e1) eqn:C1; simpl in *; try congruence. destruct (fold_right
          (fun (val : expr * expr) (acc : option (list string)) =>
           option_append (option_append (cols x (snd val)) (cols x (fst val))) acc)
          (Some nil) l); try congruence. injection H as H. rewrite <- H. unfold incl. split.
         * exists l1. split; try reflexivity. intros. rewrite <- dedup_preserves_In. apply in_or_app. left. rewrite <- dedup_preserves_In.
           apply in_or_app. right. assumption.
         * exists l0. split; try reflexivity. intros. rewrite <- dedup_preserves_In. apply in_or_app. left. rewrite <- dedup_preserves_In.            apply in_or_app. left. assumption.
        + remember (fold_right
          (fun (val : expr * expr) (acc : option (list string)) =>
           option_append (option_append (cols x (snd val)) (cols x (fst val))) acc)
          (Some nil) l) as l2. destruct a. simpl in *. unfold option_append in H.
          destruct (cols x e0) eqn:C1; try congruence. destruct (cols x e) eqn:C2; try congruence. destruct l2; try congruence.
          injection H as H. apply dedup_incl in H. destruct H. apply IHl with (columns:=l2) in H0; try reflexivity. destruct H0. split.
          * destruct H0. destruct H0. exists x0. split; try assumption. apply incl_tran with (m:=l2); assumption.
          * destruct H2. destruct H2. exists x0. split; try assumption. apply incl_tran with (m:=l2); assumption. 
   Qed.

   Lemma In_map_fst: forall A B (a:A) (b:B) l, In (a,b) l -> In a (map fst l).
     induction l; intuition. simpl. inversion H; auto. left; subst; reflexivity.   
   Qed.

   Lemma Forall2_Forall :
    forall {A B : Type} (P : A -> B -> Prop) (Q : A -> Prop) (l1 : list A) (l2 : list B),
      Forall2 P l1 l2 -> (forall a b, P a b -> Q a) -> Forall Q l1.
     intros. induction H; try apply Forall_nil. apply Forall_cons; eauto.
   Qed.

   Ltac dcols e x :=
     destruct (cols x e) eqn:?; try congruence.
 
   (* TODO: use ltacs to condense this proof and other proofs below *)
   Lemma cols_in_record: forall (Gstore Genv: tenv)(e: expr)(t: type)(x: string)(f1: list (string*type))(ecols: list string),
       type_of Gstore Genv e t ->
       map.get Genv x = Some (TRecord f1) ->
       cols x e = Some ecols ->
       incl ecols (map fst f1).
   Proof.
     (* if x is a record where the list of items has types f1, and expression e uses columns ecols out of that record,
        then those columns are included in all of the columns of the record (assuming e is well-typed *)
     intros Gstore Genv e t x f1 ecols H T. generalize dependent ecols.
     induction H using @type_of_IH; intuition; simpl in *; unfold option_append in *.
     - destruct (string_dec x0 x) eqn:S; try inversion H0. apply incl_nil_l.
     - injection H0 as H0. rewrite <- H0. apply incl_nil_l.
     - injection H0 as H0. rewrite <- H0. apply incl_nil_l.
     - dcols e1 x. dcols e2 x. injection H4 as H4. rewrite <- H4.
       unfold incl in *. intros. apply dedup_In in H5. apply in_app_or in H5. destruct H5; eauto.
     - dcols e3 x. dcols e1 x. dcols e2 x.
       injection H5 as H5. rewrite <- H5. unfold incl in *. intros. apply dedup_In in H6. apply in_app_or in H6. destruct H6.
        + eapply H4; eauto.
        + apply dedup_In in H6. apply in_app_or in H6. destruct H6; eauto.
      - destruct (string_dec x x0); try eauto. destruct (cols x e1); try congruence. destruct (cols x e2); try congruence.
        injection H2 as H2. rewrite <- H2. unfold incl in *. intros. apply dedup_In in H3. apply in_app_or in H3. destruct H3.
          * eapply H1; eauto.
          * eapply IHtype_of2; eauto. rewrite map.get_put_diff; assumption.
      - destruct (string_dec x x0); try eauto. destruct (cols x e1); try congruence. destruct (cols x e2); try congruence.
        injection H2 as H2. rewrite <- H2. unfold incl in *. intros. apply dedup_In in H3. apply in_app_or in H3. destruct H3.
          * eapply H1; eauto.
          * eapply IHtype_of2; eauto. rewrite map.get_put_diff; assumption.
      - destruct (Sumbool.sumbool_or (x = x0) (x <> x0) (x = y) (x <> y) (string_dec x x0) (string_dec x y)) as [b1 | b2].
        + destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. injection H4 as H4. rewrite <- H4.
          unfold incl in *. intros. apply dedup_In in H5. apply in_app_or in H5. destruct H5; eauto.
        + destruct (cols x e3); try congruence. destruct (cols x e1); try congruence. destruct (cols x e2); try congruence.
          injection H4 as H4. rewrite <- H4. unfold incl in *. intros. apply dedup_In in H5. apply in_app_or in H5. destruct H5.
          * eapply IHtype_of3; eauto. destruct b2. rewrite !map.get_put_diff; try assumption.
          * apply dedup_In in H5. apply in_app_or in H5. destruct H5; eauto.
      - clear H H0 H2 H3 H4. apply Forall2_Forall with (Q := fun e => map.get Genv x = Some (TRecord f1) -> forall ecols : list string,
        cols x e = Some ecols -> incl ecols (map fst f1)) in H1; try eauto. generalize dependent ecols. induction l; intros; simpl in *.
        + injection H5 as H5. rewrite <- H5. apply incl_nil_l.
        + destruct a. simpl in *. destruct (cols x e) eqn:C; try congruence. apply Forall_inv_tail in H1 as H. apply Forall_inv in H1.
          apply H1 with (ecols:=l0) in T as H2; try assumption. clear H1. destruct (fold_right
           (fun (val : string * expr) (acc : option (list string)) =>
            match cols x (snd val) with
            | Some l1 =>
                match acc with
                | Some l2 => Some (dedup eqb (l1 ++ l2))
                | None => None
                end
            | None => None
            end) (Some nil) l);try congruence. injection H5 as H5. rewrite <- H5. apply IHl with (ecols:=l1) in H; try reflexivity.
          unfold incl in *. intros. apply dedup_In in H0. apply in_app_or in H0. destruct H0; auto.
      - destruct e eqn:E; eauto. destruct (string_dec x1 x); subst; injection H2 as H2; rewrite <- H2.
        + apply access_record_sound in H0. inversion H. subst. rewrite H4 in T. injection T as T. unfold incl. intros. destruct H2.
          * subst. apply In_map_fst in H0. assumption.
          * simpl in H2. inversion H2.
        + apply incl_nil_l.
      - clear H H0 H1. generalize dependent ecols. induction l; intros; simpl in *.
        + injection H3 as H3. rewrite <- H3. apply incl_nil_l.
        + destruct a. simpl in *. destruct (cols x e0) eqn:C0; try congruence. destruct (cols x e) eqn:C; try congruence.
          apply Forall_inv_tail in H2 as H1. apply Forall_inv in H2. simpl in *. destruct H2. remember T as T1. clear HeqT1.
          apply H0 with (ecols:=l0) in T; try assumption. apply H with (ecols:=l1) in T1; try assumption.
            destruct (fold_right
           (fun (val : expr * expr) (acc : option (list string)) =>
            match
              match cols x (snd val) with
              | Some l1 =>
                  match cols x (fst val) with
                  | Some l2 => Some (dedup eqb (l1 ++ l2))
                  | None => None
                  end
              | None => None
              end
            with
            | Some l1 =>
                match acc with
                | Some l2 => Some (dedup eqb (l1 ++ l2))
                | None => None
                end
            | None => None
            end) (Some nil) l); try congruence. injection H3 as H3. rewrite <- H3. apply IHl with (ecols:=l2) in H1; try reflexivity.
            unfold incl in *. intros. apply dedup_In in H2. apply in_app_or in H2. destruct H2; auto. apply dedup_In in H2.
            apply in_app_or in H2. destruct H2; auto.
      - destruct (cols x v); try congruence. destruct (cols x d); try congruence. destruct (cols x k); try congruence.
        injection H5 as H5. rewrite <- H5. unfold incl in *. intros. apply dedup_In in H6. apply in_app_or in H6. destruct H6.
        + eapply H4; eauto.
        + apply dedup_In in H6. apply in_app_or in H6. destruct H6; eauto.
      - destruct (cols x d); try congruence. destruct (cols x k); try congruence. injection H3 as H3. rewrite <- H3.
        unfold incl in *. intros. apply dedup_In in H4. apply in_app_or in H4. destruct H4; eauto.
      - destruct (cols x d); try congruence. destruct (cols x k); try congruence. injection H3 as H3. rewrite <- H3.
        unfold incl in *. intros. apply dedup_In in H4. apply in_app_or in H4. destruct H4; eauto.
      - destruct (string_dec x x0).
        + destruct (cols x e); try congruence. destruct (cols x e_none); try congruence. injection H4 as H4. rewrite <- H4.
          unfold incl in *. intros. apply dedup_In in H5. apply in_app_or in H5. destruct H5; eauto.
        + destruct (cols x e); try congruence. destruct (cols x e_none); try congruence. destruct (cols x e_some); try congruence.
          injection H4 as H4. rewrite <- H4. unfold incl in *. intros. apply dedup_In in H5. apply in_app_or in H5. destruct H5.
          * eapply H2; eauto.
          * apply dedup_In in H5. apply in_app_or in H5. destruct H5.
            -- eapply H3; eauto.
            -- eapply IHtype_of3; eauto. rewrite map.get_put_diff; assumption.
      - destruct (Sumbool.sumbool_or (x = v \/ x = acc) (x <> v /\ x <> acc) (x = k) (x <> k)
          (Sumbool.sumbool_or (x = v) (x <> v) (x = acc) (x <> acc) (string_dec x v) (string_dec x acc)) (string_dec x k)) as [b1|b2].
        + destruct (cols x d); try congruence. destruct (cols x e0); try congruence. injection H4 as H4. rewrite <- H4.
          unfold incl in *. intros. apply dedup_In in H5. apply in_app_or in H5. destruct H5; eauto.
        + destruct b2 as [b2 b4]. destruct b2 as [b2 b3]. destruct (cols x e); try congruence. destruct (cols x d); try congruence.
          destruct (cols x e0); try congruence. injection H4 as H4. rewrite <- H4. unfold incl in *. intros. apply dedup_In in H5.
          apply in_app_or in H5. destruct H5.
          * eapply IHtype_of3; eauto. rewrite !map.get_put_diff; try assumption.
          * apply dedup_In in H5. apply in_app_or in H5. destruct H5; eauto.
      - destruct (string_dec x x0); try eauto. destruct (cols x e); try congruence. destruct (cols x p); try congruence.
        injection H2 as H2. rewrite <- H2. unfold incl in *. intros. apply dedup_In in H3. apply in_app_or in H3. destruct H3.
        + eapply H1; eauto.
        + eapply IHtype_of2; eauto. rewrite map.get_put_diff; assumption.
      - destruct (Sumbool.sumbool_or (x = x0) (x <> x0) (x = y) (x <> y) (string_dec x x0) (string_dec x y)) as [b1|b2].
        + destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. injection H5 as H5. rewrite <- H5.
          unfold incl in *. intros. apply dedup_In in H6. apply in_app_or in H6. destruct H6; eauto.
        + destruct (cols x r); try congruence. destruct (cols x p); try congruence. destruct (cols x e1); try congruence.
          destruct (cols x e2); try congruence. destruct b2 as [b2 b3]. injection H5 as H5. rewrite <- H5. unfold incl in *.
          intros. apply dedup_In in H6. apply in_app_or in H6. destruct H6.
          * eapply IHtype_of4; eauto. rewrite !map.get_put_diff; try assumption.
          * apply dedup_In in H6. apply in_app_or in H6. destruct H6.
            -- eapply IHtype_of3; eauto. rewrite !map.get_put_diff; try assumption.
            -- apply dedup_In in H6. apply in_app_or in H6. destruct H6; eauto.
      - destruct (string_dec x x0); try eauto. destruct (cols x e); try congruence. destruct (cols x r); try congruence.
        injection H2 as H2. rewrite <- H2. unfold incl in *. intros. apply dedup_In in H3. apply in_app_or in H3. destruct H3.
        + eapply H1; eauto.
        + eapply IHtype_of2; eauto. rewrite map.get_put_diff; assumption.
    Qed.

    Ltac destruct_match_goal := lazymatch goal with |-context [match ?x with _ => _ end] => destruct x end.
                         
    Lemma rel_lemma: forall (store: locals) (x: string) (a a': value) (e: expr) (columns: list string) tl tl',
      forall (env: locals),
      type_of_value a (TRecord tl) ->
      type_of_value a' (TRecord tl') ->  
      cols x e = Some columns ->
      relation a a' columns -> 
      interp_expr store (map.put env x a) e
      = interp_expr store (map.put env x a') e.
    Proof.
      (* a' is the smaller record with only the relevant columns, if a and a' are wellformed,
         and the relation holds between a a' and the expression's columns
         (columns of expression incl in a', a' included in a), then can replace a with a' when interpreting e *)
      induction e using expr_IH.
      11: {
          intros columns ? ? env ? ? HC HR. simpl in *. destruct e eqn:E; try now (erewrite IHe; eauto). simpl. destruct (string_dec x0 x).
          + subst. unfold get_local. rewrite !map.get_put_same. unfold relation in HR. destruct a,a'; intuition. inversion H. subst.
            inversion H0. subst. clear H6 H9. injection HC as HC. rewrite <- HC in H2. simpl in *. unfold incl in H2. simpl in *.
            specialize (H2 s). intuition. clear H4. apply Forall2_split in H7. destruct H7. apply Forall2_fst_eq in H3. (*lemma *)
            rewrite <- H3 in H5. apply In_fst in H2. destruct H2. destruct x0. intuition. subst. simpl in *. unfold incl in H1.
            specialize (H1 (s0,v)). remember H6 as H6'. clear HeqH6'. apply H1 in H6'. apply Forall2_split in H10. destruct H10.
            apply Forall2_fst_eq in H2. rewrite <- H2 in H8. assert (S1: record_proj s0 l = v).
            * clear IHe H H0 H1 H3 H4 H8 H2 H7 H6'. induction l.
              -- simpl in H6. contradiction.
              -- simpl. destruct a eqn:A. simpl in H6. destruct H6 eqn: S.
                 ++ subst. destruct (s0 =? s)%string eqn:HS.
                    ** inversion e. reflexivity.
                    ** inversion e. subst. rewrite eqb_refl in HS. congruence.
                 ++ subst. destruct (s0 =? s)%string eqn:HS.
                    ** apply eqb_eq in HS. subst. rewrite map_cons in H5. simpl in H5. apply invert_NoDup_cons in H5. destruct H5.
                       apply In_map_fst in i. contradiction.
                    ** rewrite map_cons in H5. simpl in H5. apply invert_NoDup_cons in H5. destruct H5. apply IHl; assumption.
            * assert (S2: record_proj s0 l0 = v).
              -- clear IHe H H0 H1 H3 H4 H5 H3 H2 H7 H6. induction l0.
                 ++ simpl in H6'. contradiction.
                 ++ simpl. destruct a eqn:A. simpl in H6'. destruct H6' eqn:S.
                    ** subst. destruct (s0 =? s)%string eqn:HS.
                       --- inversion e. reflexivity.
                       --- inversion e. subst. rewrite eqb_refl in HS. congruence.
                    ** subst. destruct (s0 =? s)%string eqn:HS.
                       --- apply eqb_eq in HS. subst. rewrite map_cons in H8. simpl in H8. apply invert_NoDup_cons in H8. destruct H8.
                           apply In_map_fst in i. contradiction.
                       --- rewrite map_cons in H8. simpl in H8. apply invert_NoDup_cons in H8. destruct H8. apply IHl0; assumption.
              -- rewrite S1. rewrite S2. reflexivity.
          + unfold get_local. rewrite !map.get_put_diff; try assumption. reflexivity.
        }        
      - intros columns env HC HR. simpl. simpl in HC. destruct (string_dec x0 x).
        + congruence.
        + unfold get_local. repeat (rewrite map.get_put_diff; try assumption). reflexivity.
      - simpl. reflexivity.
      - simpl. reflexivity.
      - intros columns ? ? env ? ? HC HR. simpl. f_equal. eapply IHe; eauto.
      - intros columns ? ? env ? ? HC HR. simpl in *. unfold option_append in HC. destruct (cols x e1); try congruence.
        destruct (cols x e2); try congruence. injection HC as HC. apply dedup_incl in HC. destruct HC. f_equal.
         + eapply IHe1; eauto. eapply rel_step; eauto.
         + eapply IHe2; eauto. eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. unfold option_append in HC. destruct (cols x e3); try congruence.
        destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. injection HC as HC.
        apply dedup_incl in HC. destruct HC. apply incl_dedup in H0. destruct H0. erewrite IHe1; eauto.
        + destruct_match_goal; try reflexivity. destruct b.
          * eapply IHe2; eauto. eapply rel_step; eauto.
          * eapply IHe3; eauto. eapply rel_step; eauto.
        + eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. unfold option_append in HC. destruct (string_dec x x0).
        + subst. rewrite !Properties.map.put_put_same. erewrite IHe1; eauto.
        + destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. injection HC as HC. apply dedup_incl in HC.
          destruct HC. erewrite IHe1; eauto.
          * rewrite !Properties.map.put_put_diff with (k2:=x0); try assumption. eapply IHe2; eauto. eapply rel_step; eauto.
          * eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. unfold option_append in HC. destruct (string_dec x x0).
        + subst. erewrite IHe1; eauto. destruct_match_goal; try reflexivity. f_equal. apply In_flat_map_ext. intros.
          rewrite !Properties.map.put_put_same. reflexivity.
        + destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. injection HC as HC. apply dedup_incl in HC.
          destruct HC. erewrite IHe1; eauto.
          * destruct_match_goal; try reflexivity. f_equal. apply In_flat_map_ext. intros.
            rewrite !Properties.map.put_put_diff with (k2:=x0); try assumption. erewrite IHe2; eauto. eapply rel_step; eauto.
          * eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. unfold option_append in HC.
        destruct (Sumbool.sumbool_or (x=x0)(x<>x0)(x=y)(x<>y)
        (string_dec x x0)(string_dec x y)) as [b1|b2].
        + destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. injection HC as HC. apply dedup_incl in HC.
          destruct HC. erewrite IHe1; eauto. 
          * destruct_match_goal; try reflexivity. f_equal.
            -- repeat (apply FunctionalExtensionality.functional_extensionality; intros). destruct b1.
               ++ subst. rewrite !Properties.map.put_put_same. reflexivity.
               ++ subst. destruct (string_dec y x0).
                  ** subst. rewrite !Properties.map.put_put_same. reflexivity.
                  ** rewrite !Properties.map.put_put_diff with (k2:=x0); try assumption. rewrite !Properties.map.put_put_same.
                     reflexivity.
            -- eapply IHe2; eauto. eapply rel_step; eauto.
          * eapply rel_step; eauto.
        + destruct (cols x e3); try congruence. destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. destruct b2.
          injection HC as HC. apply dedup_incl in HC. destruct HC. apply incl_dedup in H2. destruct H2. erewrite IHe1; eauto.
          * destruct_match_goal; try reflexivity. f_equal.
            -- repeat (apply FunctionalExtensionality.functional_extensionality; intros).
               rewrite !Properties.map.put_put_diff with (k2:=x0); try assumption.
               rewrite !Properties.map.put_put_diff with (k1:=x); try assumption. eapply IHe3; eauto. eapply rel_step; eauto.
            -- eapply IHe2; eauto. eapply rel_step; eauto.
          * eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. f_equal. f_equal. apply map_ext_in. intros [s e] LA. f_equal.
        apply Forall_In with (x:=(s,e)) in H; try assumption. simpl in *. eapply subcols_record in HC; eauto. destruct HC.
        destruct H0. eapply H; eauto. eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. f_equal. f_equal. f_equal. apply map_ext_in. intros [s e] LA.
        apply Forall_In with (x:=(s,e)) in H; try assumption. simpl in *. eapply subcols_dict in HC; eauto. destruct HC.
        destruct H0. destruct H0. destruct H1. destruct H1. destruct H. f_equal.
        + eapply H; eauto. eapply rel_step; eauto.
        + eapply H4; eauto. eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. unfold option_append in HC. destruct (cols x e3); try congruence.
        destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. injection HC as HC.
        apply dedup_incl in HC. destruct HC. apply incl_dedup in H0. destruct H0. erewrite IHe1; eauto.
        + destruct_match_goal; try reflexivity. f_equal. f_equal.
          * eapply IHe2; eauto. eapply rel_step; eauto.
          * eapply IHe3; eauto. eapply rel_step; eauto.
        + eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. unfold option_append in HC. destruct (cols x e1); try congruence.
        destruct (cols x e2); try congruence. injection HC as HC. apply dedup_incl in HC. destruct HC. erewrite IHe1; eauto.
        + destruct_match_goal; try reflexivity. f_equal. f_equal. eapply IHe2; eauto. eapply rel_step; eauto.
        + eapply rel_step; eauto.
      - intros columns env ? ? HT1 HT2 HC HR. simpl in *. unfold option_append in HC. destruct (cols x e1); try congruence.
        destruct (cols x e2); try congruence. injection HC as HC. apply dedup_incl in HC. destruct HC. erewrite IHe1; eauto.
        + destruct_match_goal; try reflexivity. f_equal. f_equal. eapply IHe2; eauto. eapply rel_step; eauto.
        + eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. unfold option_append in HC. destruct (string_dec x x0).
        + destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. injection HC as HC. apply dedup_incl in HC.
          destruct HC. erewrite IHe1; eauto.
          * destruct_match_goal; try reflexivity. subst. destruct m.
            -- rewrite !Properties.map.put_put_same. reflexivity. 
            -- erewrite IHe2; eauto. eapply rel_step; eauto.
          * eapply rel_step; eauto.
        + destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. destruct (cols x e3); try congruence.
          injection HC as HC. apply dedup_incl in HC. destruct HC. apply incl_dedup in H0. destruct H0. erewrite IHe1; eauto.
          * destruct_match_goal; try reflexivity. destruct m.
            -- rewrite !Properties.map.put_put_diff with (k2:=x0); try assumption. erewrite IHe3; eauto. eapply rel_step; eauto.
            -- erewrite IHe2; eauto. eapply rel_step; eauto.
          * eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. unfold option_append in HC. destruct (Sumbool.sumbool_or (x = v \/ x = acc)
        (x <> v /\ x <> acc) (x = k) (x <> k) (Sumbool.sumbool_or (x = v) (x <> v) (x = acc) (x <> acc)
        (string_dec x v) (string_dec x acc)) (string_dec x k)) as [b1|b2].
        + destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. injection HC as HC. apply dedup_incl in HC.
          destruct HC. erewrite IHe1; eauto.
          * destruct_match_goal; try reflexivity. f_equal.
            -- repeat (apply FunctionalExtensionality.functional_extensionality; intros). destruct x0. simpl. destruct b1.
               ++ destruct H1; subst.
                  ** destruct (string_dec v k).
                     --- subst. rewrite !Properties.map.put_put_same. reflexivity.
                     --- rewrite !Properties.map.put_put_diff with (k2:=k); try assumption. rewrite !Properties.map.put_put_same.
                         reflexivity.
                  ** destruct (string_dec acc k).
                     --- subst. rewrite !Properties.map.put_put_same. reflexivity.
                     --- rewrite !Properties.map.put_put_diff with (k2:=k); try assumption. destruct (string_dec acc v).
                         +++ subst. rewrite !Properties.map.put_put_same. reflexivity.
                         +++ rewrite !Properties.map.put_put_diff with (k1:=acc)(k2:=v); try assumption.
                             rewrite !Properties.map.put_put_same. reflexivity.
               ++ subst. rewrite !Properties.map.put_put_same. reflexivity.
            -- eapply IHe2; eauto. eapply rel_step; eauto.
          * eapply rel_step; eauto.
        + destruct (cols x e3); try congruence. destruct (cols x e1); try congruence. destruct (cols x e2); try congruence.
          destruct b2 as [b2 b4]. destruct b2 as [b2 b3]. injection HC as HC. apply dedup_incl in HC. destruct HC.
          apply incl_dedup in H0. destruct H0. erewrite IHe1; eauto.
          * destruct_match_goal; try reflexivity. f_equal.
            -- repeat (apply FunctionalExtensionality.functional_extensionality; intros). destruct x0. simpl.
               rewrite !Properties.map.put_put_diff with (k1:=x); try assumption. erewrite IHe3; eauto. eapply rel_step; eauto.
            -- eapply IHe2; eauto. eapply rel_step; eauto.
          * eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. erewrite IHe; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. unfold option_append in HC. destruct (string_dec x x0).
        + subst. erewrite IHe1; eauto. destruct_match_goal; try reflexivity. f_equal. apply In_filter_ext. intros b L.
          rewrite !Properties.map.put_put_same. reflexivity.
        + destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. injection HC as HC. apply dedup_incl in HC.
          destruct HC. erewrite IHe1; eauto.
          * destruct_match_goal; try reflexivity. f_equal. apply In_filter_ext. intros b L.
            rewrite !Properties.map.put_put_diff with (k2:=x0); try assumption. erewrite IHe2; eauto. eapply rel_step; eauto.
          * eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. unfold option_append in HC.
        destruct (Sumbool.sumbool_or (x = x0) (x <> x0) (x = y) (x <> y) (string_dec x x0) (string_dec x y)) as [b1|b2].
        + destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. injection HC as HC. apply dedup_incl in HC.
          destruct HC. erewrite IHe1; eauto.
          * destruct_match_goal; try reflexivity. erewrite IHe2; eauto.
            -- destruct_match_goal; try reflexivity. f_equal. apply In_flat_map_ext. intros. f_equal.
               ++ apply FunctionalExtensionality.functional_extensionality. intros. destruct b1; subst.
                  ** rewrite !Properties.map.put_put_same. reflexivity.
                  ** destruct (string_dec x0 y); subst.
                     --- rewrite !Properties.map.put_put_same. reflexivity.
                     --- rewrite !Properties.map.put_put_diff with (k1:=x0); try assumption. rewrite !Properties.map.put_put_same.
                         reflexivity.
               ++ apply In_filter_ext. intros. destruct b1; subst.
                  ** rewrite !Properties.map.put_put_same. reflexivity.
                  ** destruct (string_dec x0 y); subst.
                     --- rewrite !Properties.map.put_put_same. reflexivity.
                     --- rewrite !Properties.map.put_put_diff with (k1:=x0); try assumption. rewrite !Properties.map.put_put_same.
                         reflexivity.
            -- eapply rel_step; eauto.
          * eapply rel_step; eauto.
        + destruct (cols x e4); try congruence. destruct (cols x e3); try congruence. destruct (cols x e1); try congruence.
          destruct (cols x e2); try congruence. destruct b2 as [b1 b2]. injection HC as HC. apply dedup_incl in HC. destruct HC.
          apply incl_dedup in H0. destruct H0. apply incl_dedup in H1. destruct H1. erewrite IHe1; eauto.
          * destruct_match_goal; try reflexivity. erewrite IHe2; eauto.
            -- destruct_match_goal; try reflexivity. f_equal. apply In_flat_map_ext. intros. f_equal.
               ++ apply FunctionalExtensionality.functional_extensionality. intros.
                  rewrite !Properties.map.put_put_diff with (k1:=x); try assumption. eapply IHe4; eauto. eapply rel_step; eauto.
               ++ apply In_filter_ext. intros. rewrite !Properties.map.put_put_diff with (k1:=x); try assumption. erewrite IHe3; eauto.
                  eapply rel_step; eauto.
            -- eapply rel_step; eauto.
          * eapply rel_step; eauto.
      - intros columns ? ? env HT1 HT2 HC HR. simpl in *. unfold option_append in HC. destruct (string_dec x x0); subst.
        + erewrite IHe1; eauto. destruct_match_goal; try reflexivity. f_equal. apply map_ext_in. intros.
          rewrite !Properties.map.put_put_same. reflexivity.
        + destruct (cols x e1); try congruence. destruct (cols x e2); try congruence. injection HC as HC. apply dedup_incl in HC.
          destruct HC. erewrite IHe1; eauto; try eapply rel_step; eauto. destruct_match_goal; try reflexivity. f_equal. apply map_ext_in.
          intros. rewrite !Properties.map.put_put_diff with (k1:=x); try assumption. erewrite IHe2; eauto; eapply rel_step; eauto.
    Qed.

    Lemma record_proj_lemma: forall (l: list (string*value)) (x: string),
        In x (map fst l) -> In (x, record_proj x l) l.
      induction l.
      - intros. simpl in H. contradiction.
      - intros. destruct H.
        + left. subst. destruct a eqn:A. f_equal. simpl. rewrite eqb_refl. reflexivity.
        + simpl. destruct a eqn:A. destruct (x =? s)%string eqn:S.
          * subst. auto. apply eqb_eq in S. subst. left. reflexivity. 
          * right. eauto.
    Qed.

    Lemma record_proj_skip: forall (x s : string) (v : value) (l1 : list (string * value)),
       x <> s -> record_proj x ((s,v)::l1) = record_proj x l1.
      intros. simpl. destruct (x =? s)%string eqn:XS.
      - rewrite String.eqb_eq in XS. contradiction.
      - reflexivity.
    Qed.
 
    Lemma map_record_proj_skip: forall (s : string) (v : value) (l1 : list (string * value)) (l2 : list string),
       (forall x0, In x0 l2 -> x0 <> s) ->
       map (fun x0 => (x0, record_proj x0 ((s, v) :: l1))) l2 = map (fun x0 => (x0, record_proj x0 l1)) l2.
      intros. apply map_ext_in. intros. rewrite record_proj_skip; try reflexivity. apply H. auto.
    Qed.

    Lemma map_fst_a0: forall (a0: string) (l: list (string * type)),
        a0 = fst match find (fun '(s, _) => (a0 =? s)%string) l with
               | Some (s, t0) => (s, t0)
               | None => (a0, TUnit)
               end.
      intros. destruct (find (fun '(s, _) => (a0 =? s)%string) l) eqn:D.
      - destruct p. apply find_some in D. destruct D. rewrite String.eqb_eq in H0. auto.
      - auto.
    Qed.

    Lemma map_snd_a0: forall (a0: string) (l: list (string * type)),
        In a0 (map fst l) ->
        In (a0, snd match find (fun '(s, _) => (a0 =? s)%string) l with
                  | Some (s, t0) => (s, t0)
                  | None => (a0, TUnit)
                  end) l.
      intros. destruct (find (fun '(s, _) => (a0 =? s)%string) l) eqn:D; simpl.
      - destruct p. apply find_some in D. destruct D. rewrite String.eqb_eq in H1. subst. auto.
      - apply in_map_iff in H. destruct H. destruct H. eapply find_none in D; eauto. destruct x. rewrite String.eqb_neq in D.
        simpl in H. subst. contradiction.
    Qed.

    Lemma Permutation_cons_in {A: Type}: forall (la lb: list A) (a b: A),
        Permutation.Permutation (a :: la) (b :: lb) ->
        (a = b /\ Permutation.Permutation la lb) \/ (In a lb /\ In b la).
      intros. apply Permutation.Permutation_sym in H as S.
      apply Permutation.Permutation_in with (x:=a) in H as H1. 2: {simpl. left. auto.}
      apply Permutation.Permutation_in with (x:=b) in S as H2. 2: {simpl. left. auto.} destruct H1.
      - left. split.
        + symmetry. auto.
        + subst. eapply Permutation.Permutation_cons_inv. eauto.
      - destruct H2.
        + left. split; auto. subst. eapply Permutation.Permutation_cons_inv. eauto.
        + right. split; auto.
    Qed.

    Lemma unify_Perm_NoDup_fst: forall (l2'' l2': list (string * type)),
      Permutation.Permutation l2'' l2' ->
      map fst l2' = map fst l2'' ->
      NoDup (map fst l2'') -> 
      l2' = l2''.
      induction l2''.
      - intros. apply Permutation.Permutation_nil. auto.
      - destruct l2'.
        + intros. symmetry. apply Permutation.Permutation_nil. apply Permutation.Permutation_sym in H. auto.
        + intros. rewrite !map_cons in H0. inversion H0. simpl in H1. apply invert_NoDup_cons in H1. destruct H1.
          apply Permutation_cons_in in H as H5. destruct H5; destruct H5.
          * subst. f_equal. apply IHl2''; auto.
          * rewrite <- H3 in H1. apply in_map with (f:=fst) in H6. contradiction.
    Qed.

    Lemma record_type_a': forall (store env:locals) (a a': value) (f1' f1: list (string * type)) (pcols rcols: list string) (xp: string),
      a' =
          VRecord
            (record_sort
               (map
                  (fun x0 : string =>
                   (x0,
                    interp_expr store (map.put env xp a) (EAccess (EVar xp) x0)))
                  (dedup eqb (pcols ++ rcols)))) ->
      f1' =
           record_sort
             (map
                (fun x0 : string =>
                 match find (fun '(s, _) => (x0 =? s)%string) f1 with
                 | Some (s, t) => (s, t)
                 | None => (x0, TUnit)
                 end) (dedup eqb (pcols ++ rcols))) ->
      incl pcols (map fst f1) ->
      incl rcols (map fst f1) ->
      type_of_value a (TRecord f1) ->
      type_of_value a' (TRecord f1').
    Proof.
      intros store env a a' f1' f1 pcols rcols xp HA HF HI1 HI2 HT.
      assert (HI3: incl (dedup eqb (pcols ++ rcols)) (map fst f1)).
      {1: unfold incl in *. intros. apply dedup_preserves_In in H. apply in_app_or in H. destruct H; auto.}
      assert (HD: NoDup (dedup eqb (pcols ++ rcols))) by apply NoDup_dedup.
      rewrite HA. apply TyVRecord; inversion HT; subst.
      - rewrite <- Permuted_record_sort. rewrite map_map. rewrite map_ext_id; auto. intros. rewrite <- map_fst_a0. auto.
      - apply StronglySorted_record_sort.
      - induction (dedup eqb (pcols ++ rcols)).
        {1: simpl. unfold record_sort. unfold Mergesort.Sectioned.sort. simpl. apply Forall2_nil.}
        apply incl_cons_inv in HI3. destruct HI3. apply invert_NoDup_cons in HD. destruct HD. apply IHl0 in H2 as H6; auto. clear IHl0.
        apply Forall2_Permuted_StronglySorted with (l1:=(map (fun x0 : string =>
         (x0, interp_expr store (map.put env xp (VRecord l)) (EAccess (EVar xp) x0))) (a :: l0))) (l2:=(map (fun x0 : string =>
         match find (fun '(s, _) => (x0 =? s)%string) f1 with | Some (s, t0) => (s, t0) | None => (x0, TUnit) end) (a :: l0))).
        + simpl. unfold get_local in *. rewrite map.get_put_same in *. apply Forall2_cons; simpl in *.
          * split; try apply map_fst_a0. clear H1 HI1 HI2 HT. induction H3; simpl; try apply TyVUnit. destruct y. simpl in *. destruct H.
            -- destruct x. simpl in H1. destruct H1. subst. rewrite eqb_refl. simpl. auto.
            -- apply invert_NoDup_cons in H0. destruct H0. destruct ((a =? s)%string) eqn:AS.
               ++ rewrite String.eqb_eq in AS. subst. simpl. destruct x. simpl in H1. destruct H1.
                  destruct ((s =? s0)%string) eqn:SS; auto. rewrite String.eqb_neq in SS. subst. contradiction.
               ++ destruct x. simpl in H1. destruct H1. subst. rewrite AS. rewrite String.eqb_neq in AS. destruct (in_dec string_dec s l0).
                  ** clear IHForall2 H6. apply record_proj_sound with (l:=l)(tl:=l'); auto.
                     --- apply Forall2_split in H3. destruct H3. apply Forall2_fst_eq in H1. rewrite H1. auto.
                     --- apply map_snd_a0. auto. 
                  ** assert (HL: incl l0 (map fst l')).
                     {1: unfold incl in *. intros. apply H2 in H1 as H9. destruct H9; try auto. subst. contradiction.}
                      apply IHForall2 in H; clear IHForall2; auto. unfold get_local in H6. rewrite map.get_put_same in H6.
                      rewrite map_record_proj_skip in H6. 2: { intros. unfold incl in HL. apply HL in H1. intro. subst. contradiction. }
                      assert (HM: (record_sort (map (fun x0 : string => match (if (x0 =? s)%string then Some (s, t) else
                             find (fun '(s, _) => (x0 =? s)%string) l') with | Some (s, t) => (s, t) | None => (x0, TUnit) end) l0))
                              = (record_sort (map (fun x0 : string => match find (fun '(s0, _) => (x0 =? s0)%string) l' with
                              | Some (s, t) => (s, t) | None => (x0, TUnit) end) l0))).
                      --- f_equal. apply map_ext_in. intros. destruct (a0 =? s)%string eqn:AS0; auto. rewrite String.eqb_eq in AS0.
                          subst. contradiction.
                      --- rewrite HM in H6. unfold get_local. rewrite map.get_put_same. auto.
          * unfold get_local in *. rewrite map.get_put_same in *. clear H H4. induction l0; simpl; try apply Forall2_nil.
            apply Forall2_cons; simpl.
            -- split; try apply map_fst_a0. apply incl_cons_inv in H2. destruct H2. apply record_proj_sound with (l:=l)(tl:=f1); auto.
               ++ apply Forall2_split in H3. destruct H3. apply Forall2_fst_eq in H3. rewrite H3. auto.
               ++ apply map_snd_a0. auto.
            -- apply invert_NoDup_cons in H5. destruct H5. apply incl_cons_inv in H2. destruct H2. apply IHl0; auto. simpl in H6.
               remember ((a0, record_proj a0 l) :: map (fun x0 : string => (x0, record_proj x0 l)) l0) as l'.
               remember ((match find (fun '(s, _) => (a0 =? s)%string) f1 with | Some (s, t) => (s, t) | None => (a0, TUnit) end
                          :: map (fun x0 : string => match find (fun '(s, _) => (x0 =? s)%string) f1 with
                          | Some (s, t) => (s, t) | None => (x0, TUnit) end) l0)) as l2''. clear IHl0.
               apply Permutation.Permutation_Forall2 with (l1':=l') in H6.
               2: {apply Permutation.Permutation_sym. apply Permuted_record_sort.}
               destruct H6 as [l2' [H6 H7]]. assert (HL2: l2' = l2'').
               {1: apply Permutation.perm_trans with (l':=record_sort l2'')(l'':=l2')(l:=l2'') in H6; try apply Permuted_record_sort.
                apply Forall2_split in H7. destruct H7. clear H8.
                apply unify_Perm_NoDup_fst with (l2':=l2')(l2'':=l2''); auto.
                - apply Forall2_fst_eq in H7. rewrite <- H7. subst l' l2''. simpl. f_equal; try apply map_fst_a0. rewrite !map_map. simpl.
                  rewrite map_id. clear H5 H H4 H6 H7. induction l0; auto. simpl. f_equal; auto. apply map_fst_a0.
                - rewrite Heql2''. simpl. rewrite map_map. rewrite <- map_fst_a0. clear H6 H7. subst. apply NoDup_cons.
                  + clear H5. induction l0; auto. apply not_in_cons in H. destruct H. apply invert_NoDup_cons in H4. destruct H4.
                    apply not_in_cons. split.
                    * rewrite <- map_fst_a0. auto.
                    * apply IHl0; auto.
                  + clear H. induction l0; auto. simpl. rewrite <- map_fst_a0. apply invert_NoDup_cons in H4. destruct H4.
                    apply incl_cons_inv in H5. destruct H5. apply IHl0 in H4; auto. apply NoDup_cons; auto. clear IHl0 H6.
                    induction l0; auto. apply not_in_cons in H. destruct H. simpl in H4. apply invert_NoDup_cons in H4. destruct H4.
                    apply not_in_cons. split.
                    * rewrite <- map_fst_a0. auto.
                    * apply IHl0; auto. }
               subst l2''. rewrite Heql' in H7. rewrite HL2 in H7. apply Forall2_cons_iff in H7. destruct H7. simpl in *.
               apply Forall2_Permuted_StronglySorted with
                  (l1:=(map (fun x0:string => (x0, record_proj x0 l)) l0)) (l2:=(map (fun x0:string => match find (fun '(s, _) =>
                  (x0 =? s)%string) f1 with | Some (s,t) => (s,t) | None => (x0, TUnit) end) l0)); auto.
                  ++ simpl. rewrite map_map. simpl. rewrite map_id. auto.
                  ++ intros. destruct H9. auto.
                  ++ apply Permuted_record_sort.
                  ++ apply Permuted_record_sort.
                  ++ apply StronglySorted_record_sort.
                  ++ apply StronglySorted_record_sort.
           + simpl. rewrite map_map. simpl. rewrite map_id. apply NoDup_cons; assumption.
           + intros. destruct H7. auto.
           + apply Permuted_record_sort.
           + apply Permuted_record_sort.
           + apply StronglySorted_record_sort.
           + apply StronglySorted_record_sort.
    Qed.
  
    Theorem proj_pushdown_left: forall (store env: locals) (Gstore Genv: tenv) (tb1 tb2 p r: expr) (x y xp: string) (pcols rcols: list string) (f1 f2: list (string * type)) (t: type),
      tenv_wf Gstore -> tenv_wf Genv ->
      locals_wf Gstore store -> locals_wf Genv env ->  
      type_of Gstore (map.put (map.put Genv x (TRecord f1)) y (TRecord f2)) p TBool ->
      type_of Gstore (map.put (map.put Genv x (TRecord f1)) y (TRecord f2)) r t ->
      type_of Gstore Genv tb1 (TList (TRecord f1)) ->
      type_of Gstore Genv tb2 (TList (TRecord f2)) ->
      x <> y ->
      cols x p = Some pcols ->
      cols x r = Some rcols ->
      let columns := dedup String.eqb (pcols ++ rcols) in
      let rp := make_record xp columns in
      interp_expr store env (EJoin tb1 tb2 x y p r) =
      interp_expr store env (EJoin (EProj tb1 xp rp) tb2 x y p r).
    Proof.
      intros store env Gstore Genv tb1 tb2 p r x y xp pcols rcols f1 f2 t WF1 WF2 L1 L2 TP TR T1 T2 XY HP HR. simpl.
      destruct (interp_expr store env tb1) eqn:H1; try reflexivity.
      destruct (interp_expr store env tb2) eqn:H2; try reflexivity. f_equal.
      rewrite flat_map_map. apply In_flat_map_ext. intros a LA. rewrite map_map.
      assert (HI1: incl pcols (map fst f1)).
      {1: eapply cols_in_record with (e:=p); eauto. rewrite Properties.map.put_put_diff; auto. rewrite map.get_put_same. auto.}
      assert (HI2: incl rcols (map fst f1)).
      {1: eapply cols_in_record with (e:=r); eauto. rewrite Properties.map.put_put_diff; auto. rewrite map.get_put_same. auto.}
      assert (HT: type_of_value a (TRecord f1)).
      {1: eapply type_sound in T1; eauto. rewrite H1 in T1. rewrite <- TyVList_def in T1. eapply Forall_In in T1; eauto.}
      remember (record_sort (map (fun x0 : string => match find (fun '(s,_) => (x0 =? s)%string) f1 with
                                                     | Some (s,t) => (s,t)
                                                     | None => (x0, TUnit) end) (dedup eqb (pcols ++ rcols)))) as f1'.
      remember (VRecord (record_sort (map (fun x0 : string => (x0, interp_expr store (map.put env xp a) (EAccess (EVar xp) x0)))
                                        (dedup eqb (pcols ++ rcols))))) as a'.
      assert (HT': type_of_value a' (TRecord f1')) by (eapply record_type_a'; eauto). apply map_ext_in_eq.
      - apply In_filter_ext. intros b LB.
        repeat (rewrite Properties.map.put_put_diff with (k2:=y); try apply XY).
        rewrite rel_lemma with (tl:=f1')(tl':=f1)(a:=a')(a':=a)(columns:=pcols); try reflexivity; try assumption; unfold relation.
        rewrite Heqa'. simpl. apply type_sound with (store:=store) (env:=env) in T1; try assumption.
        inversion T1. symmetry in H. rewrite H in H1. injection H1 as H1. rewrite <- H1 in LA.
        apply Forall_In with (x:=a) in H3; try assumption. destruct a; try inversion H3. subst. unfold incl. split.
        + intros. rewrite <- Permuted_record_sort in H0. apply in_map_iff in H0. destruct H0 as [? [? ?]]. rewrite <- H0.
          unfold get_local. rewrite map.get_put_same. apply record_proj_lemma. apply dedup_preserves_In in H1.
          apply in_app_or in H1. apply Forall2_split in H8. destruct H8. apply Forall2_fst_eq in H4. rewrite H4. destruct H1.
          * unfold incl in HI1. apply HI1. assumption.
          * unfold incl in HI2. apply HI2. assumption.
        + intros. rewrite in_map_iff. exists ((a,record_proj a l2)). simpl. split; try reflexivity.
          rewrite <- Permuted_record_sort. apply in_map_iff. exists a. split.
          * f_equal. unfold get_local. rewrite map.get_put_same. reflexivity.
          * rewrite <- dedup_preserves_In. apply in_or_app. left. assumption.
      - intros b LB.
        repeat (rewrite Properties.map.put_put_diff with (k2:=y); try apply XY).
        rewrite rel_lemma with (tl:=f1')(tl':=f1)(a:=a')(a':=a)(columns:=rcols); try reflexivity; try assumption. unfold relation.
        rewrite Heqa'. simpl. apply type_sound with (store:=store) (env:=env) in T1; try assumption.
        inversion T1. symmetry in H. rewrite H in H1. injection H1 as H1. rewrite <- H1 in LA.
        apply Forall_In with (x:=a) in H3; try assumption. destruct a; try inversion H3. subst. unfold incl. split.
        + intros. rewrite <- Permuted_record_sort in H0. apply in_map_iff in H0. destruct H0 as [? [? ?]]. rewrite <- H0.
          unfold get_local. rewrite map.get_put_same. apply record_proj_lemma. apply dedup_preserves_In in H1.
          apply in_app_or in H1. apply Forall2_split in H8. destruct H8. apply Forall2_fst_eq in H4. rewrite H4. destruct H1.
          * unfold incl in HI1. apply HI1. assumption.
          * unfold incl in HI2. apply HI2. assumption.
        + intros. rewrite in_map_iff. exists ((a, record_proj a l2)). simpl. split; try reflexivity.
          rewrite <- Permuted_record_sort. apply in_map_iff. exists a. split.
          * f_equal. unfold get_local. rewrite map.get_put_same. reflexivity.
          * rewrite <- dedup_preserves_In. apply in_or_app. right. assumption.
    Qed. Print Assumptions proj_pushdown_left.


    (* TODO: finish proofs below *)
    Theorem filter_into_join: forall (store env: locals) (Gstore Genv: tenv) (tb1 tb2 pj rj pf: expr) (xj yj xf: string) (t tx ty tj: type),
      type_of Gstore (map.put (map.put Genv xj tx) yj ty) pj TBool ->  
      tenv_wf Gstore -> tenv_wf (map.put (map.put Genv xj tx) yj ty) ->
      locals_wf Gstore store -> locals_wf Genv env ->
      let pnew := EBinop OAnd pj (ELet rj xf pf) in
      interp_expr store env (EFilter (EJoin tb1 tb2 xj yj pj rj) xf pf)
      = interp_expr store env (EJoin tb1 tb2 xj yj pnew rj).
    Proof.
      intros store env Gstore Genv tb1 tb2 pj rj pf xj yj xf t tx ty tj TJ WF1 WF2 WF3 WF4. simpl.
      destruct (interp_expr store env tb1) eqn: D1; try reflexivity.
      destruct (interp_expr store env tb2) eqn: D2; try reflexivity. f_equal.
      rewrite filter_flat_map. apply In_flat_map_ext. intros a LA.
      rewrite filter_map_commute. f_equal.
      rewrite filter_filter. apply In_filter_ext. intros b LB.
      apply type_sound with Gstore (map.put (map.put Genv xj tx) yj ty) pj TBool store (map.put (map.put env xj a) yj b) in TJ; try auto.
      - inversion TJ. simpl. remember (interp_expr store (map.put (map.put env xj a) yj b) rj) as RJ.
        assert (TF: type_of Gstore (map.put Genv xf tj) pf TBool). 1: admit. apply type_sound with Gstore (map.put Genv xf tj) pf TBool store (map.put env xf RJ) in TF; try auto.
        + inversion TF. admit.
        + admit.
        + admit.
      - apply locals_wf_step.
        + apply locals_wf_step.
          * apply WF4.
          * Search VList type_of_value.  admit.
       + admit.
    Admitted.
 
    Lemma typeof_to_typeofvalue : forall (store env: locals) (Gstore Genv: tenv) (e: expr) (t: type),
      type_of Gstore Genv e t -> type_of_value (interp_expr store env e) t.
    Admitted.

    Theorem filter_into_join_updated : forall (store env: locals) (Gstore Genv: tenv) (db1 db2 pj rj pf: expr) (xj yj xf: string) (t tx ty: type),
      type_of Gstore (map.put (map.put Genv xj tx) yj ty) pj (TList t) ->  
      tenv_wf Gstore -> tenv_wf (map.put (map.put Genv xj tx) yj ty) ->
      locals_wf Gstore store -> locals_wf Genv env ->
      let pnew := EBinop OAnd pj (ELet rj xf pf) in
      interp_expr store env (EFilter (EJoin db1 db2 xj yj pj rj) xf pf)
      = interp_expr store env (EJoin db1 db2 xj yj pnew rj).
    Proof.
      intros store env Gstore Genv db1 db2 pj rj pf xj yj xf t tx ty H WF1 WF2 WF3 WF4. simpl.
      destruct (interp_expr store env db1) eqn: D1; try reflexivity.
      destruct (interp_expr store env db2) eqn: D2; try reflexivity. f_equal.
      rewrite filter_flat_map. apply In_flat_map_ext. intros a LA.
      rewrite filter_map_commute. f_equal.
      rewrite filter_filter. apply In_filter_ext. intros b LB.
      apply type_sound with Gstore (map.put (map.put Genv xj tx) yj ty) pj (TList t) store (map.put (map.put env xj a) yj b) in H.
      - inversion H. rewrite Bool.andb_false_r. simpl. reflexivity.
      - apply WF1.
      - apply WF2.
      - apply WF3.
      - apply locals_wf_step.
        + apply locals_wf_step.
          * apply WF4.
          * admit.
       + admit.
    Admitted.

    Theorem filter_into_join_old: forall (store env: locals) (Gstore Genv: tenv) (db1 db2 pj rj pf: expr) (xj yj xf: string) (tx ty: type),
      type_of Gstore (map.put (map.put Genv xj tx) yj ty) pj TBool ->
      let pnew := EBinop OAnd pj (ELet rj xf pf) in
      interp_expr store env (EFilter (EJoin db1 db2 xj yj pj rj) xf pf)
      = interp_expr store env (EJoin db1 db2 xj yj pnew rj).
    Proof.
      intros store env Gstore Genv db1 db2 pj rj pf xj yj xf tx ty H. simpl.
      destruct (interp_expr store env db1); try reflexivity.
      destruct (interp_expr store env db2); try reflexivity. f_equal.
      rewrite filter_flat_map. apply flat_map_ext. intros a.
      rewrite filter_map_commute. f_equal.
      rewrite filter_filter. apply filter_ext. intros b.
      apply typeof_to_typeofvalue with store (map.put (map.put env xj a) yj b) Gstore (map.put (map.put Genv xj tx) yj ty) pj TBool in H. inversion H.
      destruct (interp_expr store (map.put (map.put env xj a) yj b) pj) eqn:H2; try inversion H1. simpl.
      destruct b1.
      - simpl. rewrite Bool.andb_true_r. admit.
      - simpl. rewrite Bool.andb_false_r. admit.
      (*destruct (interp_expr store (map.put (map.put env xj a) yj b) rj) eqn:H4.*)  Admitted. (*inversion H1. simpl.
      destruct (interp_expr store (map.put . rewrite Bool.andb_false_r. simpl. reflexivity.
    Qed.*)  

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
      - f_equal. f_equal. f_equal. admit. (*EDict, nested induction*)
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
      - admit.
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
