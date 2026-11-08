(* ====================================================================
   A PRIMARY KEY ON SEVERAL ATTRIBUTES AT ONCE.

   Constraint.unique_constr declares one attribute to be a key.  This is the
   same declaration on a SEQUENCE of attributes: no two rows of the table
   agree on all of them.  Real code declares keys this way constantly --
   Django's `unique_together` and `UniqueConstraint(fields=...)`, and by hand
   in home-assistant's entity registry, whose `_index` maps a triple to one
   entity_id -- and arity one is the special case, not the norm.

   THE SHAPE OF THE DECLARED BODY IS THE POINT.  It is a CONJUNCTION of
   per-attribute equalities, not one comparison of key records, and that is
   what makes the whole file cheap: the conjunction is exactly the pattern
   CompositeDictIndexImpl's read rule matches, so the write check a
   composite key needs is compiled to ONE PROBE into the composite index by
   a rewrite that already exists.  No rule was written for it.  A
   formulation comparing two key records would be shorter to reason about
   and would compile to nothing.

   What is here, in order:

     - eq_on_attrs, the conjunction, and row_keys, the composite key a row
       carries.  row_keys is literally CompositeDictIndexImpl.ckey of the
       row's fields; the two are kept textually apart so that nothing in the
       language layer depends on an index implementation.
     - row_keys_eq_iff: the key identifies the attributes.  NoDup attrs is
       needed in one direction, and it is the direction the meaning rests
       on -- without it record_sort could hold two entries under one name
       and a projection would not see both.
     - unique_many_constr and the bridge unique_many_constr_holds_iff:
       what the program maintains is a quadratic statement about counting,
       and what an index can stand for is NoDup on the list of composite
       keys.  This is Constraint.unique_constr_holds_iff at any arity.
     - cfresh_guard, the cheap check, and cfresh_guard_sound: in any store
       whose composite keys are already distinct, the cheap check and the
       declared guard have the SAME VALUE, so emitting one for the other
       changes no behaviour, including which writes run their policy.
     - unique_many_guard_let, the guard an elaboration writes, with the row
       bound first so that no capture is possible whatever the row
       expression is.  Its binders are PrimaryKeyCheck's own, so a program
       cannot tell which arity it got.

   An EMPTY attribute list is accepted and is not a key: eq_on_attrs [] is
   `true`, so the declaration says the table holds exactly one row.  That is
   a legal constraint and a strange one; nothing here rejects it, and the
   index that would serve it has no key to probe with.
   ==================================================================== *)
Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.Substitute fiat2.TransfSound fiat2.constraint.Constraint
  fiat2.constraint.PrimaryKeyCheck fiat2.rules.FlatmapForms fiat2.rules.CollectionTransf.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith Lia List Permutation Sorted.
Import ListNotations.

Section WithWord.
  Notation value := (value).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  (* The conjunction "these two rows agree on every one of attrs", written as
     the chain a reader would write: one equality per attribute, right-nested,
     with no trailing `&& true`.  The shape matters, and it is the whole
     reason this is a conjunction rather than one comparison of key records:
     it is exactly what the composite index's read rule matches, so the check
     an elaboration emits for a composite key is compiled to one probe by a
     rule that already exists. *)
  Fixpoint eq_on_attrs (attrs : list string) (e1 e2 : expr) : expr :=
    match attrs with
    | [] => EAtom (ABool true)
    | [a] => EBinop OEq (EAccess e1 a) (EAccess e2 a)
    | a :: attrs' =>
        EBinop OAnd (EBinop OEq (EAccess e1 a) (EAccess e2 a))
          (eq_on_attrs attrs' e1 e2)
    end.

  (* The key a row carries under a COMPOSITE declaration: the n-ary row_key.
     A record, canonically ordered, so that the declared order of the
     attributes does not reach the key -- which is what makes a declaration
     on (a, b) the same declaration as one on (b, a).  It is literally
     CompositeDictIndexImpl.ckey of the row's fields, and that file's index
     is keyed on exactly this; the two are kept textually apart only so that
     nothing in the language layer depends on an index implementation. *)
  Definition row_keys (attrs : list string) (v : value) : value :=
    match v with
    | VRecord rc =>
        VRecord (record_sort (List.map (fun a => (a, record_proj a rc)) attrs))
    | _ => VUnit
    end.

  (* Two generic record facts.  CompositeDictIndexImpl proves the same two for
     its own use; both belong in Utils, under the convention stated at
     DictIndexImpl.v:348, and moving them there is the cleanup that would
     remove this duplication. *)
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

  (* The key identifies the attributes: two rows have the same composite key
     exactly when they agree on every attribute of it.  NoDup is needed in
     one direction only, and it is the direction the constraint's meaning
     rests on: without it record_sort could hold two entries under one name
     and a projection would not see both. *)
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
  (* What the conjunction COMPUTES: the attributes agree, one by one. *)
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

  (* and therefore: the conjunction is the composite key's equality *)
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
    - (* the keys agree, so every attribute does *)
      apply value_eqb_eq in E.
      apply forallb_forall; intros a Hin.
      pose proof (proj1 (row_keys_eq_iff attrs rc1 rc2 Hnd) E) as HF.
      rewrite Forall_forall in HF.
      rewrite (HF a Hin); apply value_eqb_refl.
    - (* and if some attribute differs the keys cannot agree *)
      destruct (forallb _ attrs) eqn:Ef; [ exfalso | reflexivity ].
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

  (* ---------------------------------------------------------------------
     A COMPOSITE primary key, as an ordinary row predicate: the row's
     composite key occurs exactly once in the table.  The arity-one instance
     is Constraint.unique_constr, up to the key being a one-field record
     rather than the field itself.
     --------------------------------------------------------------------- *)
  Definition unique_many_constr (attrs : list string) (row_ty : type) : constr :=
    mk_constr "_r"
      (EBinop OEq
         (EUnop OLength
            (EFlatmap LikeList (EVar c_tbl) "_r2"
               (EIf (eq_on_attrs attrs (EVar "_r2") (EVar "_r"))
                  (EBinop OCons (EVar "_r2") (EAtom (ANil (Some row_ty))))
                  (EAtom (ANil (Some row_ty))))))
         (EAtom (AInt 1))).

  Lemma unique_many_constr_tbl_wf : forall attrs rt,
      type_wf (TRecord rt) ->
      Forall (fun a => In a (List.map fst rt)) attrs ->
      tbl_constr_wf (TRecord rt) (unique_many_constr attrs (TRecord rt)).
  Proof.
    intros attrs rt H_wf HF.
    unfold tbl_constr_wf, unique_many_constr, c_env_no_acc, c_tbl;
      cbn [c_row c_body].
    eapply TyEBinop; [ apply TyOEq | | ].
    2: apply TyEAtom; constructor.
    eapply TyEUnop; [ apply TyOLength | ].
    eapply TyEFlatmap_List.
    1:{ apply TyEVar; repeat rewrite_map_get_put_goal; reflexivity. }
    apply TyEIf.
    1:{ eapply eq_on_attrs_ty; [ exact HF | | ];
        apply TyEVar; repeat rewrite_map_get_put_goal; reflexivity. }
    1:{ eapply TyEBinop; [ apply TyOCons | | ].
        1: apply TyEVar; repeat rewrite_map_get_put_goal; reflexivity.
        1: apply TyEAtom; apply TyANil; exact H_wf. }
    1: apply TyEAtom; apply TyANil; exact H_wf.
  Qed.

  (* Constraint.v has interp_EUnop, interp_EBinop and interp_EFlatmap_list
     already; the conditional's one-liner is not among them. *)
  Lemma interp_EIf_step : forall (store env : locals) e1 e2 e3,
      interp_expr store env (EIf e1 e2 e3)
      = match interp_expr store env e1 with
        | VBool b => if b then interp_expr store env e2 else interp_expr store env e3
        | _ => VUnit
        end.
  Proof. reflexivity. Qed.

  (* The body's inner scan, one row at a time.  Unlike the single-attribute
     version, both rows must be RECORDS: a single attribute of a non-record
     row is VUnit on both sides, but a key RECORD built over a non-record is
     still a record, so the two sides would not agree.  Every row of a
     well-typed table is a record, which is where the premises come from. *)
  Lemma unique_many_inner_interp :
    forall attrs rt (r v : value) (l0 : list value) rc rv,
      NoDup attrs -> r = VRecord rc -> v = VRecord rv ->
      match interp_expr (map.empty : locals)
              (map.put (map.put (map.put map.empty c_tbl (VList l0)) "_r" r) "_r2" v)
              (EIf (eq_on_attrs attrs (EVar "_r2") (EVar "_r"))
                 (EBinop OCons (EVar "_r2") (EAtom (ANil (Some (TRecord rt)))))
                 (EAtom (ANil (Some (TRecord rt))))) with
      | VList l2 => l2
      | _ => nil
      end
      = (if value_eqb (row_keys attrs v) (row_keys attrs r) then v :: nil else nil).
  Proof.
    intros attrs rt r v l0 rc rv Hnd Er Ev; subst r v.
    rewrite interp_EIf_step.
    rewrite (interp_eq_on_attrs_keys attrs _ _ (EVar "_r2") (EVar "_r") rv rc Hnd).
    2:{ rewrite interp_EVar; unfold get_local; rewrite map.get_put_same;
        reflexivity. }
    2:{ rewrite interp_EVar; unfold get_local;
        rewrite map.get_put_diff by discriminate;
        rewrite map.get_put_same; reflexivity. }
    destruct (value_eqb (row_keys attrs (VRecord rv)) (row_keys attrs (VRecord rc)));
      cbn [interp_expr interp_binop interp_atom]; unfold get_local.
    - rewrite map.get_put_same; reflexivity.
    - reflexivity.
  Qed.

  (* So the inner scan of a composite key's body is a filter on the key. *)
  Lemma unique_many_flat_map : forall attrs rt (r : value) (l0 l : list value) rc,
      NoDup attrs -> r = VRecord rc ->
      Forall (fun v => exists rv, v = VRecord rv) l ->
      flat_map
        (fun v =>
           match interp_expr (map.empty : locals)
                   (map.put (map.put (map.put map.empty c_tbl (VList l0)) "_r" r)
                      "_r2" v)
                   (EIf (eq_on_attrs attrs (EVar "_r2") (EVar "_r"))
                      (EBinop OCons (EVar "_r2") (EAtom (ANil (Some (TRecord rt)))))
                      (EAtom (ANil (Some (TRecord rt))))) with
           | VList l2 => l2
           | _ => nil
           end) l
      = List.filter (fun r2 => value_eqb (row_keys attrs r2) (row_keys attrs r)) l.
  Proof.
    intros attrs rt r l0 l rc Hnd Er HF.
    induction HF as [ | v l [ rv Ev ] HF' IH ];
      cbn [flat_map List.filter]; [ reflexivity | ].
    rewrite (unique_many_inner_interp attrs rt r v l0 rc rv Hnd Er Ev), IH.
    destruct (value_eqb (row_keys attrs v) (row_keys attrs r)); reflexivity.
  Qed.

  (* What a composite key says about one row: its key occurs once. *)
  Lemma unique_many_tbl_sat_iff : forall attrs rt l r rc,
      NoDup attrs -> r = VRecord rc ->
      Forall (fun v => exists rv, v = VRecord rv) l ->
      (tbl_sat (unique_many_constr attrs (TRecord rt)) (VList l) r
       <-> List.length
             (List.filter (fun r2 => value_eqb (row_keys attrs r2)
                                       (row_keys attrs r)) l)
           = 1).
  Proof.
    unfold tbl_sat, unique_many_constr; cbn [c_row c_body]; intros * Hnd Er HF.
    rewrite interp_EBinop, interp_EUnop, interp_EFlatmap_list, interp_EVar.
    unfold get_local.
    rewrite map.get_put_diff by (unfold c_tbl; discriminate).
    rewrite map.get_put_same.
    cbn beta iota.
    rewrite (unique_many_flat_map attrs rt r l l rc Hnd Er HF).
    cbn [interp_unop interp_binop interp_atom].
    split.
    1:{ intro H. injection H as H.
        apply value_eqb_true_iff in H. injection H as H. lia. }
    1:{ intro H. rewrite H. reflexivity. }
  Qed.

  Lemma unique_many_constr_hygienic : forall attrs row_ty,
      c_row (unique_many_constr attrs row_ty) <> c_all.
  Proof.
    unfold unique_many_constr, c_all; cbn [c_row]; intros.
    intro H; discriminate H.
  Qed.

  (* ---------------------------------------------------------------------
     The bridge, at any arity: what the program maintains is a quadratic
     statement about counting, and what an index can stand for is NoDup on
     the list of COMPOSITE keys.
     --------------------------------------------------------------------- *)
  Theorem unique_many_constr_holds_iff : forall attrs rt l,
      type_wf (TRecord rt) ->
      NoDup attrs ->
      Forall (fun a => In a (List.map fst rt)) attrs ->
      Forall (fun r => type_of_value r (TRecord rt)) l ->
      (constr_holds (unique_many_constr attrs (TRecord rt)) (VList l)
       <-> NoDup (List.map (row_keys attrs) l)).
  Proof.
    intros * H_wf Hnd HF H_l.
    assert (H_rec : Forall (fun v => exists rv, v = VRecord rv) l).
    1:{ rewrite Forall_forall in H_l |- *; intros v H_v.
        specialize (H_l v H_v); inversion H_l; eauto. }
    rewrite (tbl_constr_holds_iff (TRecord rt)
               (unique_many_constr attrs (TRecord rt)) l H_wf
               (unique_many_constr_hygienic attrs (TRecord rt))
               (unique_many_constr_tbl_wf attrs rt H_wf HF) H_l).
    rewrite <- (Forall_count_one_iff_NoDup value value value_eqb
                  (row_keys attrs) l value_eqb_true_iff).
    split.
    1:{ intros H_F. apply (proj2 (Forall_forall _ l)); intros r H_rin.
        destruct (proj1 (Forall_forall _ l) H_rec r H_rin) as [ rc Er ].
        apply (proj1 (unique_many_tbl_sat_iff attrs rt l r rc Hnd Er H_rec)).
        exact (proj1 (Forall_forall _ l) H_F r H_rin). }
    1:{ intros H_F. apply (proj2 (Forall_forall _ l)); intros r H_rin.
        destruct (proj1 (Forall_forall _ l) H_rec r H_rin) as [ rc Er ].
        apply (proj2 (unique_many_tbl_sat_iff attrs rt l r rc Hnd Er H_rec)).
        exact (proj1 (Forall_forall _ l) H_F r H_rin). }
  Qed.

  (* Removing rows cannot break a composite key either. *)
  Corollary unique_many_constr_holds_filter : forall attrs rt g l,
      type_wf (TRecord rt) ->
      NoDup attrs ->
      Forall (fun a => In a (List.map fst rt)) attrs ->
      Forall (fun r => type_of_value r (TRecord rt)) l ->
      constr_holds (unique_many_constr attrs (TRecord rt)) (VList l) ->
      constr_holds (unique_many_constr attrs (TRecord rt)) (VList (filter g l)).
  Proof.
    intros * H_wf Hnd HF H_l H_holds.
    apply (proj2 (unique_many_constr_holds_iff attrs rt (filter g l) H_wf Hnd HF
                    (Forall_filter _ _ g l H_l))).
    apply NoDup_map_filter.
    exact (proj1 (unique_many_constr_holds_iff attrs rt l H_wf Hnd HF H_l) H_holds).
  Qed.

  Lemma unique_many_constr_wf : forall attrs rt,
      type_wf (TRecord rt) ->
      Forall (fun a => In a (List.map fst rt)) attrs ->
      constr_wf (TRecord rt) (unique_many_constr attrs (TRecord rt)).
  Proof.
    intros attrs rt H_wf HF.
    unfold constr_wf, unique_many_constr, c_env, c_tbl, c_all;
      cbn [c_row c_body].
    eapply TyEBinop; [ apply TyOEq | | ].
    2: apply TyEAtom; constructor.
    eapply TyEUnop; [ apply TyOLength | ].
    eapply TyEFlatmap_List.
    1:{ apply TyEVar; repeat rewrite_map_get_put_goal; reflexivity. }
    apply TyEIf.
    1:{ eapply eq_on_attrs_ty; [ exact HF | | ];
        apply TyEVar; repeat rewrite_map_get_put_goal; reflexivity. }
    1:{ eapply TyEBinop; [ apply TyOCons | | ].
        1: apply TyEVar; repeat rewrite_map_get_put_goal; reflexivity.
        1: apply TyEAtom; apply TyANil; exact H_wf. }
    1: apply TyEAtom; apply TyANil; exact H_wf.
  Qed.

  (* ---------------------------------------------------------------------
     Uniqueness to a lookup, at any arity.

     The guard an elaboration inserts at a write that conses one row is, in
     any store whose composite keys are already distinct, exactly the test
     "this row's composite key is not already present" -- a membership test
     on a list of key records, which is what the composite dictionary index
     answers in one step.
     --------------------------------------------------------------------- *)
  Theorem unique_many_guard_iff_fresh :
    forall attrs rt free_vars e tbl l (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
      NoDup attrs ->
      Forall (fun a => In a (List.map fst rt)) attrs ->
      map.get Gstore tbl = Some (TList (TRecord rt)) ->
      type_of Gstore Genv e (TRecord rt) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      map.get store tbl = Some (VList l) ->
      NoDup (List.map (row_keys attrs) l) ->
      (interp_expr store env
         (constr_guard (unique_many_constr attrs (TRecord rt)) free_vars
            (EBinop OCons e (ELoc tbl))) = VBool true
       <-> ~ In (row_keys attrs (interp_expr store env e))
               (List.map (row_keys attrs) l)).
  Proof.
    intros * H_Gs H_Ge H_rt Hnd HF H_tbl H_e H_fv H_store H_env E_tbl H_nd.
    destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
      as [ l' [ E_tbl' H_l ] ].
    rewrite E_tbl in E_tbl'. injection E_tbl' as E_tbl'; subst l'.
    assert (H_rv : type_of_value (interp_expr store env e) (TRecord rt))
      by (eapply type_sound; eauto).
    assert (H_cons_ty : type_of Gstore Genv (EBinop OCons e (ELoc tbl))
                          (TList (TRecord rt)))
      by (econstructor; eauto; constructor; auto).
    assert (H_u : interp_expr store env (EBinop OCons e (ELoc tbl))
                  = VList (interp_expr store env e :: l)).
    { rewrite interp_EBinop, interp_ELoc. unfold get_local.
      rewrite E_tbl. reflexivity. }
    erewrite constr_guard_interp with (Gstore := Gstore) (Genv := Genv);
      eauto using unique_many_constr_wf.
    rewrite H_u.
    pose proof (unique_many_constr_holds_iff attrs rt
                  (interp_expr store env e :: l) H_rt Hnd HF
                  (Forall_cons _ H_rv H_l)) as H_iff.
    cbn [List.map] in H_iff. rewrite NoDup_cons_iff in H_iff.
    split.
    1:{ intro H_g. exact (proj1 (proj1 H_iff H_g)). }
    1:{ intro H_fresh. apply (proj2 H_iff). split; assumption. }
  Qed.

  (* ---------------------------------------------------------------------
     THE CHEAP CHECK, at any arity.

     The declared constraint above counts; this is the test an elaboration
     emits in its place, and it is the SAME SHAPE the composite dictionary
     index's read rule matches.  So a composite primary key's write check
     compiles to one probe into that index, and no rewrite had to be written
     for it -- which is the whole reason the constraint's body is a
     conjunction of equalities rather than one comparison of key records.
     --------------------------------------------------------------------- *)
  Section WithTable.
    (* the table and the binder the filter scans with *)
    Context (tbl x : string).

    Definition ckey_filter (attrs : list string) (u : expr) : expr :=
      flatmap_filter_bag (EUnop OBagOfList (ELoc tbl)) x
        (eq_on_attrs attrs (EVar x) u) x None None.

    Definition cfresh_guard (attrs : list string) (u : expr) : expr :=
      EBinop OEq (ckey_filter attrs u) (EAtom (AEmptyBag None)).

    Lemma cfresh_guard_ty : forall attrs rt u (Gstore Genv : tenv),
        tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
        Forall (fun a => In a (List.map fst rt)) attrs ->
        map.get Gstore tbl = Some (TList (TRecord rt)) ->
        type_of Gstore Genv u (TRecord rt) ->
        free_immut_in x u = false ->
        type_of Gstore Genv (cfresh_guard attrs u) TBool.
    Proof.
      intros * H_Gs H_Ge H_rt HF H_tbl H_u H_fr.
      unfold cfresh_guard, ckey_filter.
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

    Lemma interp_ckey_filter : forall attrs (store env : locals) l u rv,
        NoDup attrs ->
        free_immut_in x u = false ->
        map.get store tbl = Some (VList l) ->
        interp_expr store env u = VRecord rv ->
        Forall (fun v => exists rc, v = VRecord rc) l ->
        interp_expr store env (ckey_filter attrs u)
        = VBag (list_to_bag
                  (filter (fun v => value_eqb (row_keys attrs v)
                                      (row_keys attrs (VRecord rv)))
                     (bag_to_list (list_to_bag l)))).
    Proof.
      intros * Hnd H_fr E_tbl E_u H_rec.
      assert (E_bag : interp_expr store env (EUnop OBagOfList (ELoc tbl))
                      = VBag (list_to_bag l)).
      { cbn [interp_expr]; unfold get_local; rewrite E_tbl; reflexivity. }
      unfold ckey_filter.
      rewrite interp_flatmap_filter_bag, E_bag.
      do 2 f_equal.
      apply filter_ext_in; intros v H_v.
      (* every row the filter sees is a row of the table, hence a record *)
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

    (* And so the cheap guard is the membership test
       unique_many_guard_iff_fresh reduces the declared guard to. *)
    Lemma cfresh_guard_iff : forall attrs (store env : locals) l u rv,
        NoDup attrs ->
        free_immut_in x u = false ->
        map.get store tbl = Some (VList l) ->
        interp_expr store env u = VRecord rv ->
        Forall (fun v => exists rc, v = VRecord rc) l ->
        (interp_expr store env (cfresh_guard attrs u) = VBool true
         <-> ~ In (row_keys attrs (VRecord rv)) (List.map (row_keys attrs) l)).
    Proof.
      intros * Hnd H_fr E_tbl E_u H_rec.
      unfold cfresh_guard.
      rewrite interp_EBinop, interp_EAtom,
        (interp_ckey_filter attrs store env l u rv Hnd H_fr E_tbl E_u H_rec).
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
    Lemma typed_rows_are_records' : forall rt (l : list value),
        Forall (fun r => type_of_value r (TRecord rt)) l ->
        Forall (fun v => exists rc, v = VRecord rc) l.
    Proof.
      intros rt l H; rewrite Forall_forall in H |- *; intros v H_v.
      specialize (H v H_v); inversion H; eauto.
    Qed.

    (* ------------------------------------------------------------------
       What the check establishes: given distinct composite keys before the
       write, a passing guard says the whole new table satisfies the
       declared constraint.
       ------------------------------------------------------------------ *)
    Lemma cfresh_guard_establishes :
      forall attrs rt u l (Gstore Genv : tenv) (store env : locals),
        tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
        NoDup attrs ->
        Forall (fun a => In a (List.map fst rt)) attrs ->
        map.get Gstore tbl = Some (TList (TRecord rt)) ->
        type_of Gstore Genv u (TRecord rt) ->
        free_immut_in x u = false ->
        locals_wf Gstore store -> locals_wf Genv env ->
        map.get store tbl = Some (VList l) ->
        NoDup (List.map (row_keys attrs) l) ->
        interp_expr store env (cfresh_guard attrs u) = VBool true ->
        constr_holds (unique_many_constr attrs (TRecord rt))
          (interp_expr store env (EBinop OCons u (ELoc tbl))).
    Proof.
      intros * H_Gs H_Ge H_rt Hnd HF H_tbl H_u H_fr H_store H_env E_tbl H_ndk
        H_guard.
      destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
        as [ l' [ E_tbl' H_l ] ].
      rewrite E_tbl in E_tbl'; injection E_tbl' as E_tbl'; subst l'.
      assert (H_rv : type_of_value (interp_expr store env u) (TRecord rt))
        by (eapply type_sound; eauto).
      assert (H_rvr : exists rv, interp_expr store env u = VRecord rv)
        by (inversion H_rv; eauto).
      destruct H_rvr as [ rv E_rv ].
      assert (H_rec : Forall (fun v => exists rc, v = VRecord rc) l)
        by (eapply typed_rows_are_records'; exact H_l).
      assert (H_fresh : ~ In (row_keys attrs (VRecord rv))
                          (List.map (row_keys attrs) l))
        by (apply (proj1 (cfresh_guard_iff attrs store env l u rv Hnd H_fr E_tbl
                            E_rv H_rec)); exact H_guard).
      assert (E_cons : interp_expr store env (EBinop OCons u (ELoc tbl))
                       = VList (interp_expr store env u :: l)).
      { rewrite interp_EBinop, interp_ELoc. unfold get_local.
        rewrite E_tbl. reflexivity. }
      rewrite E_cons.
      eapply (proj2 (unique_many_constr_holds_iff attrs rt
                       (interp_expr store env u :: l) H_rt Hnd HF
                       (Forall_cons _ H_rv H_l))).
      cbn [List.map]. rewrite E_rv. apply NoDup_cons; assumption.
    Qed.

    (* ------------------------------------------------------------------
       The cheap guard decides what the declared guard decides: in any store
       whose composite keys are already distinct, the two expressions have
       the same value, so replacing one by the other changes no behaviour --
       including which writes run their policy.
       ------------------------------------------------------------------ *)
    Theorem cfresh_guard_sound :
      forall attrs rt free_vars u l (Gstore Genv : tenv) (store env : locals),
        tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
        NoDup attrs ->
        Forall (fun a => In a (List.map fst rt)) attrs ->
        map.get Gstore tbl = Some (TList (TRecord rt)) ->
        type_of Gstore Genv u (TRecord rt) ->
        incl (get_free_vars Genv) free_vars ->
        locals_wf Gstore store -> locals_wf Genv env ->
        map.get store tbl = Some (VList l) ->
        NoDup (List.map (row_keys attrs) l) ->
        free_immut_in x u = false ->
        interp_expr store env (cfresh_guard attrs u)
        = interp_expr store env
            (constr_guard (unique_many_constr attrs (TRecord rt)) free_vars
               (EBinop OCons u (ELoc tbl))).
    Proof.
      intros * H_Gs H_Ge H_rt Hnd HF H_tbl H_u H_fv H_store H_env E_tbl H_ndk
        H_fr.
      destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
        as [ l' [ E_tbl' H_l ] ].
      rewrite E_tbl in E_tbl'; injection E_tbl' as E_tbl'; subst l'.
      assert (H_rv : type_of_value (interp_expr store env u) (TRecord rt))
        by (eapply type_sound; eauto).
      assert (H_rvr : exists rv, interp_expr store env u = VRecord rv)
        by (inversion H_rv; eauto).
      destruct H_rvr as [ rv E_rv ].
      assert (H_rec : Forall (fun v => exists rc, v = VRecord rc) l)
        by (eapply typed_rows_are_records'; exact H_l).
      (* the membership test both guards reduce to *)
      pose proof (cfresh_guard_iff attrs store env l u rv Hnd H_fr E_tbl E_rv
                    H_rec) as H_cheap.
      pose proof (unique_many_guard_iff_fresh attrs rt free_vars u tbl l
                    Gstore Genv store env H_Gs H_Ge H_rt Hnd HF H_tbl H_u
                    H_fv H_store H_env E_tbl H_ndk) as H_decl.
      rewrite E_rv in H_decl.
      (* both sides are booleans *)
      assert (H_cons_ty : type_of Gstore Genv (EBinop OCons u (ELoc tbl))
                            (TList (TRecord rt)))
        by (econstructor; [ constructor | exact H_u | constructor; exact H_tbl ]).
      assert (H_lhs : type_of_value
                        (interp_expr store env (cfresh_guard attrs u)) TBool).
      { eapply type_sound with (Gstore := Gstore) (Genv := Genv).
        1:{ eapply cfresh_guard_ty with (rt := rt); assumption. }
        1: exact H_Gs.
        1: exact H_Ge.
        1: exact H_store.
        1: exact H_env. }
      assert (H_rhs : type_of_value
                        (interp_expr store env
                           (constr_guard (unique_many_constr attrs (TRecord rt))
                              free_vars (EBinop OCons u (ELoc tbl)))) TBool).
      { eapply type_sound with (Gstore := Gstore) (Genv := Genv).
        1:{ eapply constr_guard_ty with (row_ty := TRecord rt).
            1: exact H_Gs.
            1: exact H_Ge.
            1: exact H_rt.
            1: eapply unique_many_constr_wf; [ exact H_rt | exact HF ].
            1: exact H_cons_ty.
            1: exact H_fv. }
        1: exact H_Gs.
        1: exact H_Ge.
        1: exact H_store.
        1: exact H_env. }
      destruct (type_of_value_TBool _ H_lhs) as [ H_lt | H_lf ];
        destruct (type_of_value_TBool _ H_rhs) as [ H_rt' | H_rf ];
        rewrite ?H_lt, ?H_lf, ?H_rt', ?H_rf.
      1,4: reflexivity.
      1:{ exfalso. rewrite (proj2 H_decl (proj1 H_cheap H_lt)) in H_rf.
          discriminate H_rf. }
      1:{ exfalso. rewrite (proj2 H_cheap (proj1 H_decl H_rt')) in H_lf.
          discriminate H_lf. }
    Qed.
  End WithTable.

  (* ---------------------------------------------------------------------
     The guard an elaboration writes, at any arity.

     Binding the row first settles the capture question once and for all,
     exactly as in the arity-one case: inside the template the only free
     immutable variable is pk_row and the scan binder is pk_scan, so no
     capture is possible whatever the row expression is -- and the row is
     evaluated once rather than once per attribute.  Both binders are
     PrimaryKeyCheck's, so a program cannot tell which arity it got.
     --------------------------------------------------------------------- *)
  Definition unique_many_guard_let (tbl : string) (attrs : list string)
    (row : expr) : expr :=
    ELet row pk_row (cfresh_guard tbl pk_scan attrs (EVar pk_row)).

  Lemma unique_many_guard_let_ty : forall tbl attrs rt row (Gstore Genv : tenv),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
      Forall (fun a => In a (List.map fst rt)) attrs ->
      map.get Gstore tbl = Some (TList (TRecord rt)) ->
      type_of Gstore Genv row (TRecord rt) ->
      type_of Gstore Genv (unique_many_guard_let tbl attrs row) TBool.
  Proof.
    intros * H_Gs H_Ge H_rt HF H_tbl H_row.
    unfold unique_many_guard_let. econstructor.
    1: exact H_row.
    eapply cfresh_guard_ty with (rt := rt).
    1: exact H_Gs.
    1: apply tenv_wf_step; [ exact H_Ge | exact H_rt ].
    1: exact H_rt.
    1: exact HF.
    1: exact H_tbl.
    1: constructor; apply map.get_put_same.
    1: reflexivity.
  Qed.

  Lemma unique_many_guard_let_establishes :
    forall tbl attrs rt row l (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
      NoDup attrs ->
      Forall (fun a => In a (List.map fst rt)) attrs ->
      map.get Gstore tbl = Some (TList (TRecord rt)) ->
      type_of Gstore Genv row (TRecord rt) ->
      locals_wf Gstore store -> locals_wf Genv env ->
      map.get store tbl = Some (VList l) ->
      NoDup (List.map (row_keys attrs) l) ->
      interp_expr store env (unique_many_guard_let tbl attrs row) = VBool true ->
      constr_holds (unique_many_constr attrs (TRecord rt))
        (interp_expr store env (EBinop OCons row (ELoc tbl))).
  Proof.
    intros * H_Gs H_Ge H_rt Hnd HF H_tbl H_row H_store H_env E_tbl H_ndk H_guard.
    unfold unique_many_guard_let in H_guard; rewrite interp_ELet in H_guard.
    assert (H_rv : type_of_value (interp_expr store env row) (TRecord rt))
      by (eapply type_sound; eauto).
    assert (H_Ge' : tenv_wf (map.put Genv pk_row (TRecord rt)))
      by (apply tenv_wf_step; assumption).
    assert (H_env' : locals_wf (map.put Genv pk_row (TRecord rt))
                       (map.put env pk_row (interp_expr store env row)))
      by (apply locals_wf_step; assumption).
    assert (E1 : interp_expr store env (EBinop OCons row (ELoc tbl))
                 = VList (interp_expr store env row :: l)).
    { rewrite interp_EBinop, interp_ELoc; unfold get_local.
      rewrite E_tbl; reflexivity. }
    assert (E2 : interp_expr store (map.put env pk_row (interp_expr store env row))
                   (EBinop OCons (EVar pk_row) (ELoc tbl))
                 = VList (interp_expr store env row :: l)).
    { rewrite interp_EBinop, interp_ELoc, interp_EVar; unfold get_local.
      rewrite map.get_put_same, E_tbl; reflexivity. }
    rewrite E1, <- E2.
    eapply (cfresh_guard_establishes tbl pk_scan attrs rt (EVar pk_row) l
              Gstore (map.put Genv pk_row (TRecord rt)) store
              (map.put env pk_row (interp_expr store env row))).
    1: exact H_Gs.
    1: exact H_Ge'.
    1: exact H_rt.
    1: exact Hnd.
    1: exact HF.
    1: exact H_tbl.
    1: constructor; apply map.get_put_same.
    1: reflexivity.
    1: exact H_store.
    1: exact H_env'.
    1: exact E_tbl.
    1: exact H_ndk.
    1: exact H_guard.
  Qed.

  Theorem unique_many_guard_let_sound :
    forall tbl attrs rt free_vars row l (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
      NoDup attrs ->
      Forall (fun a => In a (List.map fst rt)) attrs ->
      map.get Gstore tbl = Some (TList (TRecord rt)) ->
      type_of Gstore Genv row (TRecord rt) ->
      incl (get_free_vars Genv) free_vars ->
      locals_wf Gstore store -> locals_wf Genv env ->
      map.get store tbl = Some (VList l) ->
      NoDup (List.map (row_keys attrs) l) ->
      interp_expr store env (unique_many_guard_let tbl attrs row)
      = interp_expr store env
          (constr_guard (unique_many_constr attrs (TRecord rt)) free_vars
             (EBinop OCons row (ELoc tbl))).
  Proof.
    intros * H_Gs H_Ge H_rt Hnd HF H_tbl H_row H_fv H_store H_env E_tbl H_ndk.
    assert (H_rv : type_of_value (interp_expr store env row) (TRecord rt))
      by (eapply type_sound; eauto).
    assert (H_Ge' : tenv_wf (map.put Genv pk_row (TRecord rt)))
      by (apply tenv_wf_step; assumption).
    assert (H_env' : locals_wf (map.put Genv pk_row (TRecord rt))
                       (map.put env pk_row (interp_expr store env row)))
      by (apply locals_wf_step; assumption).
    assert (H_fv' : incl (get_free_vars (map.put Genv pk_row (TRecord rt)))
                      (pk_row :: free_vars))
      by eauto using incl_tran, incl_cons_step, get_free_vars_put.
    assert (H_pk : type_of Gstore (map.put Genv pk_row (TRecord rt))
                     (EVar pk_row) (TRecord rt))
      by (constructor; apply map.get_put_same).
    assert (H_k : constr_wf (TRecord rt) (unique_many_constr attrs (TRecord rt)))
      by (eapply unique_many_constr_wf; eassumption).
    assert (E_val : interp_expr store (map.put env pk_row (interp_expr store env row))
                      (EBinop OCons (EVar pk_row) (ELoc tbl))
                    = interp_expr store env (EBinop OCons row (ELoc tbl))).
    { rewrite !interp_EBinop, !interp_ELoc, interp_EVar; unfold get_local.
      rewrite map.get_put_same, E_tbl; reflexivity. }
    unfold unique_many_guard_let; rewrite interp_ELet.
    rewrite (cfresh_guard_sound tbl pk_scan attrs rt (pk_row :: free_vars)
               (EVar pk_row) l Gstore (map.put Genv pk_row (TRecord rt)) store
               (map.put env pk_row (interp_expr store env row))
               H_Gs H_Ge' H_rt Hnd HF H_tbl H_pk H_fv' H_store H_env' E_tbl H_ndk
               (eq_refl : free_immut_in pk_scan (EVar pk_row) = false)).
    erewrite constr_guard_interp with (row_ty := TRecord rt) (Gstore := Gstore)
      (Genv := map.put Genv pk_row (TRecord rt)).
    2: exact H_Gs.
    2: exact H_Ge'.
    2: exact H_rt.
    2: exact H_k.
    2:{ econstructor; [ constructor | exact H_pk | constructor; exact H_tbl ]. }
    2: exact H_fv'.
    2: exact H_store.
    2: exact H_env'.
    erewrite constr_guard_interp with (row_ty := TRecord rt) (Gstore := Gstore)
      (Genv := Genv).
    2: exact H_Gs.
    2: exact H_Ge.
    2: exact H_rt.
    2: exact H_k.
    2:{ econstructor; [ constructor | exact H_row | constructor; exact H_tbl ]. }
    2: exact H_fv.
    2: exact H_store.
    2: exact H_env.
    rewrite E_val; reflexivity.
  Qed.

End WithWord.
