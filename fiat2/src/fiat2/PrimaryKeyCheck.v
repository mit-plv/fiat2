Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.Substitute fiat2.TransfSound fiat2.Constraint fiat2.FlatmapForms fiat2.CollectionTransf.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List Permutation.
Import ListNotations.

(* The write check for a primary key, in the shape an ordinary dictionary
   index already answers.

   A declared primary key elaborates to a guard that reads the whole table
   twice: the quantifier "every key occurs once" is a fold over the rows, and
   each row's inner scan is another fold.  Constraint.unique_guard_iff_fresh
   says what that guard decides in a store where the key already holds: the
   written row's key is not already present.  That is a membership test, and
   this file writes it as the one expression a dictionary index is good at --
   "the rows whose key equals this one, as a bag, is empty".

   The point of that shape is that nothing downstream has to know a constraint
   was involved.  After the index transformation the filter reads
   EAccess (ELoc tbl) id_tag, which is exactly what
   DictIndexImpl.eq_filter_to_lookup_head matches, and that rule rewrites it to
   one lookup.  Its soundness needs no uniqueness at all, because a dictionary
   from keys to bags of rows represents the filter faithfully for every table.

   So a primary key needs no index of its own.  What it needs is the
   constraint, used once, to turn a quadratic guard into a filter; the index
   that answers the filter is the one the optimizer already has.  The
   uniqueness assumption appears exactly once, in checked_cons_wf below, where
   it is discharged from the invariant being maintained -- the table's keys are
   distinct before the write, which is what makes the cheap test sufficient to
   keep them distinct after it. *)

Section WithWord.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Section WithTable.
    (* the table, its key attribute, and the binder the filter scans with *)
    Context (tbl attr x : string).

    (* the rows of tbl carrying u's key, as a bag *)
    Definition key_filter (u : expr) : expr :=
      flatmap_filter_bag (EBagOf (ELoc tbl)) x
        (EBinop OEq (EAccess (EVar x) attr) (EAccess u attr)) x None None.

    (* ... and the test that there are none *)
    Definition fresh_guard (u : expr) : expr :=
      EBinop OEq (key_filter u) (EAtom (AEmptyBag None)).

    Lemma fresh_guard_ty : forall rt kt u (Gstore Genv : tenv),
        tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
        access_record rt attr = Success kt ->
        map.get Gstore tbl = Some (TList (TRecord rt)) ->
        type_of Gstore Genv u (TRecord rt) ->
        free_immut_in x u = false ->
        type_of Gstore Genv (fresh_guard u) TBool.
    Proof.
      intros * H_Gs H_Ge H_rt H_attr H_tbl H_u H_fr.
      unfold fresh_guard, key_filter.
      econstructor.
      1: apply TyOEq.
      2:{ (* the empty bag the filter is compared against *)
          constructor. apply TyAEmptyBag'. exact H_rt. }
      econstructor.
      1:{ (* the table, read as a bag *)
          constructor. constructor. exact H_tbl. }
      econstructor.
      1:{ (* the key test *)
          econstructor.
          1: apply TyOEq.
          1:{ econstructor.
              1: constructor; apply map.get_put_same.
              1: exact H_attr. }
          1:{ econstructor.
              1: apply not_free_immut_put_ty2; [ exact H_fr | exact H_u ].
              1: exact H_attr. } }
      1:{ (* the row, inserted into an empty bag *)
          econstructor.
          1: apply TyOBagInsert.
          1: constructor; apply TyAEmptyBag'; exact H_rt.
          1: constructor; apply map.get_put_same. }
      1:{ (* no row, when the key differs *)
          constructor. apply TyAEmptyBag'. exact H_rt. }
    Qed.

    (* ------------------------------------------------------------------
       What the filter computes.
       ------------------------------------------------------------------ *)

    (* The filter keeps exactly the rows whose key matches.  It scans
       bag_to_list of the table's bag rather than the table, which is a
       permutation of it; only membership is used below, so the reordering
       does not matter. *)
    Lemma interp_key_filter : forall (store env : locals) l u,
        free_immut_in x u = false ->
        map.get store tbl = Some (VList l) ->
        interp_expr store env (key_filter u)
        = VBag (list_to_bag
                  (filter (fun v => value_eqb (row_key attr v)
                                      (row_key attr (interp_expr store env u)))
                     (bag_to_list (list_to_bag l)))).
    Proof.
      intros * H_fr E_tbl.
      assert (E_bag : interp_expr store env (EBagOf (ELoc tbl)) = VBag (list_to_bag l)).
      { cbn [interp_expr]; unfold get_local; rewrite E_tbl; reflexivity. }
      unfold key_filter.
      rewrite interp_flatmap_filter_bag, E_bag.
      do 2 f_equal.
      apply filter_ext_in; intros v _.
      rewrite interp_EBinop, !interp_EAccess, interp_EVar.
      unfold get_local; rewrite map.get_put_same.
      rewrite <- (not_free_immut_put_sem u x store env v H_fr).
      unfold row_key; cbn [interp_binop]; reflexivity.
    Qed.

    (* And so the guard is the membership test Constraint.unique_guard_iff_fresh
       reduces the declared guard to. *)
    Lemma fresh_guard_iff : forall (store env : locals) l u,
        free_immut_in x u = false ->
        map.get store tbl = Some (VList l) ->
        (interp_expr store env (fresh_guard u) = VBool true
         <-> ~ In (row_key attr (interp_expr store env u))
                 (List.map (row_key attr) l)).
    Proof.
      intros * H_fr E_tbl.
      unfold fresh_guard.
      rewrite interp_EBinop, interp_EAtom, (interp_key_filter store env l u H_fr E_tbl).
      cbn [interp_binop interp_atom].
      (* the guard is true exactly when the filtered bag is empty *)
      split.
      1:{ intros H_eq H_in.
          lazymatch goal with
            H: VBool _ = VBool _ |- _ => injection H as H_eq'
          end.
          apply value_eqb_eq in H_eq'.
          lazymatch goal with H: VBag _ = VBag _ |- _ => injection H as H_nil end.
          apply list_to_bag_nil in H_nil.
          (* but the row carrying the key survives the filter *)
          apply in_map_iff in H_in as [ r [ E_key H_r ] ].
          eapply (Permutation_in _ (Permutation_sym (list_to_bag_to_list_Permutation l))) in H_r.
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
              (* a surviving row would carry the key, which is absent *)
              exfalso.
              assert (H_r : In r (filter
                 (fun v => value_eqb (row_key attr v)
                             (row_key attr (interp_expr store env u)))
                 (bag_to_list (list_to_bag l))))
                by (rewrite E_filter; cbn; auto).
              apply filter_In in H_r as [ H_r H_key ].
              apply value_eqb_eq in H_key.
              apply H_out. rewrite <- H_key. apply in_map.
              eapply Permutation_in; [ apply list_to_bag_to_list_Permutation | exact H_r ]. }
          rewrite E_nil; apply value_eqb_refl. }
    Qed.


    (* ------------------------------------------------------------------
       The check maintains the primary key.

       This is the one place uniqueness is assumed, and it is assumed of the
       table before the write -- which is exactly what PWCAssign's obligation
       receives.  So the cheap test is enough: the keys were distinct, the
       written row's key is not among them, and therefore the keys are still
       distinct afterwards.  An induction over the program turns that into an
       invariant, which is what Surface.elab_constr_wf does.
       ------------------------------------------------------------------ *)
    Lemma checked_cons_wf : forall rt kt u policy (A : locals -> locals -> Prop)
                                   (Gstore Genv : tenv),
        tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
        access_record rt attr = Success kt ->
        map.get Gstore tbl = Some (TList (TRecord rt)) ->
        type_of Gstore Genv u (TRecord rt) ->
        free_immut_in x u = false ->
        parameterized_wf Gstore Genv
          (value_wf_with_globals
             (constrs_hold [unique_constr attr (TRecord rt)]) [tbl]) A policy ->
        parameterized_wf Gstore Genv
          (value_wf_with_globals
             (constrs_hold [unique_constr attr (TRecord rt)]) [tbl]) A
          (CIf (fresh_guard u) (CAssign tbl (EBinop OCons u (ELoc tbl))) policy).
    Proof.
      intros * H_Gs H_Ge H_rt H_attr H_tbl H_u H_fr H_pol.
      assert (H_cons_ty : type_of Gstore Genv (EBinop OCons u (ELoc tbl))
                            (TList (TRecord rt)))
        by (econstructor; [ constructor | exact H_u | constructor; exact H_tbl ]).
      econstructor.
      1: eapply fresh_guard_ty; eauto.
      2:{ (* the policy keeps whatever assumption it was reached under *)
          eapply parameterized_wf_weaken; [ | exact H_pol ].
          intros * ? ? ? [? ?]; auto. }
      econstructor.
      2: exact H_tbl.
      2: exact H_cons_ty.
      intros store env [ H_A H_guard ] H_inv H_store H_env.
      unfold value_wf_with_globals; constructor; [ | constructor ]. right.
      (* the table's rows, and their types *)
      destruct (locals_wf_list Gstore store tbl (TRecord rt) H_store H_tbl)
        as [ l [ E_tbl H_l ] ].
      (* the invariant, read off the store at tbl *)
      assert (H_nd : NoDup (List.map (row_key attr) l)).
      { pose proof (H_inv tbl (VList l) E_tbl) as H_at_tbl.
        unfold value_wf_with_globals in H_at_tbl; invert_Forall.
        lazymatch goal with
          H: tbl <> tbl \/ _ |- _ => destruct H as [ H_ne | H_holds ]; [ congruence | ]
        end.
        unfold constrs_hold in H_holds; invert_Forall.
        eapply (proj1 (unique_constr_holds_iff attr rt kt l H_rt H_attr H_l));
          eassumption. }
      (* the guard, which says the written row's key is free *)
      assert (H_fresh : ~ In (row_key attr (interp_expr store env u))
                          (List.map (row_key attr) l))
        by (apply (proj1 (fresh_guard_iff store env l u H_fr E_tbl)); exact H_guard).
      (* the value the write stores *)
      assert (E_cons : interp_expr store env (EBinop OCons u (ELoc tbl))
                       = VList (interp_expr store env u :: l)).
      { rewrite interp_EBinop, interp_ELoc. unfold get_local.
        rewrite E_tbl. reflexivity. }
      assert (H_rv : type_of_value (interp_expr store env u) (TRecord rt))
        by (eapply type_sound; eauto).
      rewrite E_cons.
      unfold constrs_hold; constructor; [ | constructor ].
      eapply (proj2 (unique_constr_holds_iff attr rt kt
                       (interp_expr store env u :: l) H_rt H_attr
                       (Forall_cons _ H_rv H_l))).
      cbn [List.map]. apply NoDup_cons; assumption.
    Qed.


    (* ------------------------------------------------------------------
       The cheap guard decides what the declared guard decides.

       checked_cons_wf above does not need this -- it establishes the
       invariant from the cheap guard directly.  What this adds is that the
       cheap guard is an *optimization* of the declared one rather than a
       different check: in any store where the keys are already distinct, the
       two expressions have the same value.  So replacing one by the other
       changes no behaviour, including which writes run their policy.
       ------------------------------------------------------------------ *)
    Theorem fresh_guard_sound :
      forall rt kt free_vars u l (Gstore Genv : tenv) (store env : locals),
        tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
        access_record rt attr = Success kt ->
        map.get Gstore tbl = Some (TList (TRecord rt)) ->
        type_of Gstore Genv u (TRecord rt) ->
        incl (get_free_vars Genv) free_vars ->
        locals_wf Gstore store -> locals_wf Genv env ->
        map.get store tbl = Some (VList l) ->
        NoDup (List.map (row_key attr) l) ->
        free_immut_in x u = false ->
        interp_expr store env (fresh_guard u)
        = interp_expr store env
            (constr_guard (unique_constr attr (TRecord rt)) free_vars
               (EBinop OCons u (ELoc tbl))).
    Proof.
      intros * H_Gs H_Ge H_rt H_attr H_tbl H_u H_fv H_store H_env E_tbl H_nd H_fr.
      (* the membership test both guards reduce to *)
      pose proof (fresh_guard_iff store env l u H_fr E_tbl) as H_cheap.
      pose proof (unique_guard_iff_fresh attr rt kt free_vars u tbl l
                    Gstore Genv store env H_Gs H_Ge H_rt H_attr H_tbl H_u
                    H_fv H_store H_env E_tbl H_nd) as H_decl.
      (* both sides are booleans *)
      assert (H_cons_ty : type_of Gstore Genv (EBinop OCons u (ELoc tbl))
                            (TList (TRecord rt)))
        by (econstructor; [ constructor | exact H_u | constructor; exact H_tbl ]).
      assert (H_lhs : type_of_value (interp_expr store env (fresh_guard u)) TBool).
      { eapply type_sound with (Gstore := Gstore) (Genv := Genv).
        1:{ eapply fresh_guard_ty with (rt := rt) (kt := kt)
                                       (Gstore := Gstore) (Genv := Genv);
            assumption. }
        1: exact H_Gs.
        1: exact H_Ge.
        1: exact H_store.
        1: exact H_env. }
      assert (H_rhs : type_of_value
                        (interp_expr store env
                           (constr_guard (unique_constr attr (TRecord rt)) free_vars
                              (EBinop OCons u (ELoc tbl)))) TBool).
      { eapply type_sound with (Gstore := Gstore) (Genv := Genv).
        1:{ eapply constr_guard_ty with (row_ty := TRecord rt).
            1: exact H_Gs.
            1: exact H_Ge.
            1: exact H_rt.
            1: eapply unique_constr_wf; [ exact H_rt | exact H_attr ].
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
      1:{ (* cheap true, declared false: the key is free, so the declared
             guard would have passed *)
          exfalso. rewrite (proj2 H_decl (proj1 H_cheap H_lt)) in H_rf.
          discriminate H_rf. }
      1:{ (* declared true, cheap false: likewise *)
          exfalso. rewrite (proj2 H_cheap (proj1 H_decl H_rt')) in H_lf.
          discriminate H_lf. }
    Qed.

  End WithTable.
End WithWord.
