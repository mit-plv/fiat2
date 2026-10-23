Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.Utils fiat2.Substitute
  fiat2.IndexTransf fiat2.Constraint fiat2.UniqueDictIndexImpl.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* Installing an index whose correctness depends on a declared primary key.

   UniqueDictIndexImpl builds the dictionary that sends each key to a single
   row.  Its weak well-formedness, idx_wf, says only that the dictionary is
   what to_idx computes, which is true of any table: for a table with
   duplicate keys the dictionary keeps one row per key and forgets the others.
   That is enough to answer the write guard, which only asks whether a key is
   present, and it is why the index satisfies IndexInterface.ok at all.  It is
   not enough to answer a point query, and the lemmas that do that carry a
   NoDup hypothesis.

   idx_wf_unique is the strong form, idx_wf together with that NoDup.  It is
   not an instance of IndexInterface.ok, and cannot be: to_idx does not
   establish it for an arbitrary table.  What establishes it is the program,
   by maintaining the constraint, and what carries it to every store the
   program reaches is transf_to_idx'_wf_pre, the fused form of the index
   installation's well-formedness proof.

   This file closes that loop.  The invariant the installation delivers is
   unique_aux_wf: at the table's entry, the record's index field is a correct
   index of its table field *and* the table's keys are distinct. *)

Section WithIndexVars.
  (* the names the index's own fold binds *)
  Context (hole attr tup acc : string).
  Context (H_ne : tup <> acc).
  (* the two fields the installation pairs *)
  Context (id_tag aux_tag : string).
  Context (H_tags_diff : id_tag <> aux_tag).

  Notation uidx := (unique_dict_idx hole attr tup acc).

  Lemma unique_is_tbl_ty : forall rt kt,
      access_record rt attr = Success kt ->
      @IndexInterface.is_tbl_ty uidx (TList (TRecord rt)) = true.
  Proof.
    intros * H_attr. cbn.
    apply inb_true_iff.
    apply access_record_sound in H_attr.
    replace attr with (fst (attr, kt)) by reflexivity.
    apply in_map; assumption.
  Qed.

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Notation value := (value).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Notation uidx_wf := (UniqueDictIndexImpl.idx_wf hole attr tup acc (locals:=locals)).

    (* The table invariant a primary key on attr declares. *)
    Definition key_holds (rt : list (string * type)) : value -> Prop :=
      constrs_hold (locals:=locals) [unique_constr attr (TRecord rt)].

    (* What transf_to_idx' delivers, with the weak index well-formedness and
       the declared constraint side by side. *)
    Definition unique_aux_pre (rt : list (string * type)) (v : value) : Prop :=
      aux_wf (idx_wf := uidx_wf) id_tag aux_tag v
      /\ at_id_tag id_tag (key_holds rt) v.

    (* And what a rewrite over this index gets to assume: the strong form. *)
    Definition unique_aux_wf (v : value) : Prop :=
      match v with
      | VRecord rv =>
          match access_record rv id_tag with
          | Success v_id =>
              match access_record rv aux_tag with
              | Success v_aux => idx_wf_unique hole attr tup acc v_id v_aux
              | _ => False
              end
          | _ => False
          end
      | _ => False
      end.

    (* ------------------------------------------------------------------
       The value-level core of the bridge.  It says nothing about how the
       installation lays its record out, only about a table and its index side
       by side, so every layout can go through it: the flat record the
       single-index installation builds, and the nested one an index record
       builds, where the dictionary sits under a tag of its own.
       ------------------------------------------------------------------ *)
    Lemma idx_wf__idx_wf_unique : forall rt kt (v_id v_aux : value),
        type_wf (TRecord rt) ->
        access_record rt attr = Success kt ->
        type_of_value v_id (TList (TRecord rt)) ->
        uidx_wf v_id v_aux ->
        constr_holds (locals := locals) (unique_constr attr (TRecord rt)) v_id ->
        idx_wf_unique hole attr tup acc v_id v_aux.
    Proof.
      intros * H_rt H_attr H_ty H_wf H_constr.
      inversion H_ty; subst.
      unfold idx_wf_unique; split; [ exact H_wf | ].
      cbn [keys_distinct].
      lazymatch goal with
        H_fa : Forall _ ?l |- NoDup (List.map (row_key attr) ?l) =>
          apply (proj1 (unique_constr_holds_iff attr rt kt l H_rt H_attr H_fa))
      end.
      exact H_constr.
    Qed.

    (* ------------------------------------------------------------------
       The bridge.  The constraint is a statement about counting and the
       index assumes NoDup on the keys, so the step from one to the other
       goes through unique_constr_holds_iff, which needs the table value to
       be well typed.  That typing is not part of a value predicate, so it
       is a hypothesis here rather than a conjunct of unique_aux_pre: every
       rewrite site has locals_wf and can supply it.
       ------------------------------------------------------------------ *)
    Lemma unique_aux_pre__unique_aux_wf : forall rt kt (v : value),
        type_wf (TRecord rt) ->
        access_record rt attr = Success kt ->
        type_of_value v (aux_ty (idx := uidx) id_tag aux_tag (TList (TRecord rt))) ->
        unique_aux_pre rt v ->
        unique_aux_wf v.
    Proof.
      unfold unique_aux_pre, unique_aux_wf, aux_wf, at_id_tag, key_holds, constrs_hold.
      intros * H_rt H_attr H_ty [ H_aux H_pre ].
      repeat destruct_match_hyp; try contradiction.
      invert_Forall.
      lazymatch goal with
        E : access_record _ id_tag = Success ?vid |- _ =>
          assert (H_vid : type_of_value vid (TList (TRecord rt)))
            by (eapply type_of_value_at_id_tag; [ exact H_tags_diff | exact H_ty | exact E ])
      end.
      eapply idx_wf__idx_wf_unique;
        [ exact H_rt | exact H_attr | exact H_vid | assumption | assumption ].
    Qed.

    Section WithGlobal.
      Context (tbl : string).

      (* ------------------------------------------------------------------
         The installation.  This is transf_to_idx'_wf_pre with Pv set to the
         declared primary key: a program that maintains the key is turned
         into one that maintains the key *and* the index of it.
         ------------------------------------------------------------------ *)
      Theorem transf_to_idx'_unique_install :
        forall rt kt c free_vars Gstore Genv A A',
          type_wf (TRecord rt) ->
          access_record rt attr = Success kt ->
          map.get Gstore tbl = Some (TList (TRecord rt)) ->
          incl (get_free_vars Genv) free_vars ->
          tenv_wf Gstore -> tenv_wf Genv ->
          (forall (store env : locals),
              locals_wf (map.put Gstore tbl
                           (aux_ty (idx := uidx) id_tag aux_tag (TList (TRecord rt)))) store ->
              locals_wf Genv env ->
              holds_for_all_entries
                (value_wf_with_globals (unique_aux_pre rt) (tbl :: nil)) store ->
              A' store env -> A (strip_aux id_tag tbl store) env) ->
          parameterized_wf Gstore Genv
            (value_wf_with_globals (key_holds rt) (tbl :: nil)) A c ->
          parameterized_wf
            (map.put Gstore tbl (aux_ty (idx := uidx) id_tag aux_tag (TList (TRecord rt)))) Genv
            (value_wf_with_globals (unique_aux_pre rt) (tbl :: nil)) A'
            (transf_to_idx' (idx := uidx) id_tag aux_tag tbl free_vars c).
      Proof.
        intros * H_rt H_attr H_tbl H_incl H_Gs H_Ge H_sim H_wf.
        eapply (transf_to_idx'_wf_pre
                  (idx_ok := unique_dict_idx_ok hole attr tup acc H_ne)
                  id_tag aux_tag H_tags_diff tbl (key_holds rt));
          [ exact H_tbl
          | apply unique_is_tbl_ty with (kt := kt); exact H_attr
          | exact H_incl | exact H_Gs | exact H_Ge
          | exact H_sim
          | exact H_wf ].
      Qed.

      (* ------------------------------------------------------------------
         Reading the strong invariant off a reachable store.  This is the
         statement a rewrite that uses the unique index needs: wherever the
         transformed program runs, the table's index field is a faithful
         key-to-row map of its table field.
         ------------------------------------------------------------------ *)
      Theorem installed_unique_aux_wf :
        forall rt kt (Gstore : tenv) (store : locals) (v : value),
          type_wf (TRecord rt) ->
          access_record rt attr = Success kt ->
          map.get Gstore tbl
          = Some (aux_ty (idx := uidx) id_tag aux_tag (TList (TRecord rt))) ->
          locals_wf Gstore store ->
          holds_for_all_entries
            (value_wf_with_globals (unique_aux_pre rt) (tbl :: nil)) store ->
          map.get store tbl = Some v ->
          unique_aux_wf v.
      Proof.
        unfold holds_for_all_entries, value_wf_with_globals.
        intros * H_rt H_attr H_tbl H_store H_inv E_tbl.
        specialize (H_inv _ _ E_tbl). invert_Forall.
        lazymatch goal with H : _ \/ _ |- _ => destruct H as [ H_ne' | H_pre ] end.
        1: congruence.
        specialize (H_store tbl _ H_tbl). rewrite E_tbl in H_store.
        eapply unique_aux_pre__unique_aux_wf; eauto.
      Qed.
    End WithGlobal.
  End WithMap.
End WithIndexVars.
