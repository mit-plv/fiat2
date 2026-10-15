Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.IndexInterface fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute
  fiat2.Constraint.
Require fiat2.DictIndexImpl.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Sorted.
Import ListNotations.

Open Scope string_scope.

(* A dictionary index for a table carrying a declared primary key.

   The index in DictIndexImpl maps an attribute value to the *bag* of rows
   that carry it, because nothing stops two rows from sharing an attribute
   value.  When the table declares the attribute to be a primary key, the bag
   has at most one element, and this index maps the key straight to the row:

     attr -> row    instead of    attr -> bag of rows

   The difference is not only in the size of the value.  A table with a
   primary key is the one case where a dictionary lookup answers a question
   the table itself can only answer by scanning, and where that question is
   asked on *every write*: the guard the constraint elaboration inserts at an
   insertion asks whether the new row's key is already taken.  Constraint.v
   proves that this guard is a membership test on the list of keys; what is
   proved here is that this index's keys are exactly the table's keys, so the
   membership test is one lookup.

   Note what this index does *not* claim.  idx_wf below says only that the
   index is what to_idx computes, which is true of any table whatsoever -- for
   a table with duplicate keys the dictionary simply keeps one row per key and
   forgets the others.  That is enough for the write guard, which only ever
   asks whether a key is present.  It is *not* enough to answer a point query
   from the index, and the lemmas that do that (idx_lookup_Some and
   idx_lookup_Some_inv) carry the NoDup hypothesis the constraint supplies.
   So the uniqueness assumption is recorded exactly where it is used: the
   index installs on any table, and only the rules that read a row back out of
   it owe the declaration. *)

(* A hit is not a miss.  Stated separately because the case analysis has to
   happen away from the hypotheses that mention the lookup, which a destruct
   in place would rewrite. *)
Lemma option_is_some_bool : forall (A : Type) (o : option A),
    o <> None -> (match o with None => true | Some _ => false end) = false.
Proof.
  intros * H; destruct o; [ reflexivity | congruence ].
Qed.

Section WithHole.
  Context (hole : string).
  Context (attr : string).

  Section WithVars.
    Context (tup acc : string).
    (* the row and the accumulator are bound by the same fold, so they must
       differ for the row to be readable in the body *)
    Context (H_ne : tup <> acc).

    Definition to_idx : expr :=
      EFold (EVar hole) (EAtom (AEmptyDict None)) tup acc
        (ETernop OInsert (EVar acc) (EAccess (EVar tup) attr) (EVar tup)).

    Definition is_tbl_ty (t : type) : bool :=
      match t with
      | TList (TRecord rt) => inb (String.eqb) attr (List.map fst rt)
      | _ => false
      end.

    Definition idx_ty (t : type) : type :=
      match t with
      | TList (TRecord rt) => TDict (get_attr_type rt attr) (TRecord rt)
      | _ => TUnit
      end.

    Lemma idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t).
    Proof.
      destruct t; cbn; intros; try congruence.
      destruct t; try congruence.
      invert_type_wf. constructor.
      1: apply get_attr_type_ty_wf; auto.
      1: assumption.
    Qed.

    Section WithMap.
      Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
      Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
      Notation value := (value (width:=width)).
      Context {locals : map.map string value} {locals_ok : map.ok locals}.

      Lemma to_idx_ty : forall (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t).
      Proof.
        unfold is_tbl_ty, idx_ty, to_idx; intros * H_wf H_tbl.
        repeat destruct_match_hyp; try discriminate; subst.
        invert_type_wf.
        rewrite inb_true_iff in H_tbl.
        apply In_access_record in H_tbl as [ kt H_attr ].
        assert (H_kt : get_attr_type l attr = kt)
          by (unfold get_attr_type; rewrite H_attr; reflexivity).
        econstructor.
        (* the table, read out of the hole *)
        1:{ constructor. rewrite map.get_put_same. reflexivity. }
        (* the empty dictionary *)
        1:{ constructor. constructor.
            1: apply get_attr_type_ty_wf; assumption.
            1: assumption. }
        (* one insertion of the row under its key *)
        1:{ econstructor.
            1: constructor.
            1:{ constructor. rewrite map.get_put_same. reflexivity. }
            1:{ rewrite H_kt. econstructor.
                1:{ constructor. rewrite map.get_put_diff by congruence.
                    rewrite map.get_put_same. reflexivity. }
                1: exact H_attr. }
            1:{ constructor. rewrite map.get_put_diff by congruence.
                rewrite map.get_put_same. reflexivity. } }
      Qed.

      Definition idx_wf (tbl_v idx_v : value) : Prop :=
        idx_v = interp_expr map.empty (map.put map.empty hole tbl_v) to_idx.

      Lemma to_idx_wf : forall (v : value) (t : type),
          type_wf t -> is_tbl_ty t = true ->
          type_of_value v t ->
          idx_wf v (interp_expr map.empty (map.put map.empty hole v) to_idx).
      Proof.
        intros; unfold idx_wf; reflexivity.
      Qed.

      (* ------------------------------------------------------------------
         What the index is, as a list of entries.
         ------------------------------------------------------------------ *)

      (* One step of the fold to_idx runs: the row goes in under its key. *)
      Definition idx_step (r d : value) : value :=
        match d with
        | VDict d => VDict (dict_insert (row_key attr r) r d)
        | _ => VUnit
        end.

      (* The entries to_idx accumulates.  Stated as a fold over the rows, so
         the induction the lookup lemmas need is the one the list of rows
         already offers. *)
      Definition idx_entries (l : list value) : list (value * value) :=
        fold_right (fun r d => dict_insert (row_key attr r) r d) nil l.

      (* stated for an arbitrary store, since the maintenance rules below
         rewrite the index inside a program, where the store is whatever the
         program's is -- to_idx itself is only ever interpreted with the
         empty one *)
      Lemma interp_idx_body : forall (store env : locals) r d,
          interp_expr store (map.put (map.put env tup r) acc d)
            (ETernop OInsert (EVar acc) (EAccess (EVar tup) attr) (EVar tup))
          = idx_step r d.
      Proof.
        unfold idx_step; intros.
        assert (E_acc : map.get (map.put (map.put env tup r) acc d) acc = Some d)
          by apply map.get_put_same.
        assert (E_tup : map.get (map.put (map.put env tup r) acc d) tup = Some r)
          by (rewrite map.get_put_diff by congruence; apply map.get_put_same).
        rewrite interp_ETernop, interp_EAccess, !interp_EVar.
        unfold get_local; rewrite E_acc, !E_tup.
        destruct d; reflexivity.
      Qed.

      Lemma fold_idx_step : forall (l : list value),
          fold_right idx_step (VDict nil) l = VDict (idx_entries l).
      Proof.
        induction l as [| r l IH]; cbn [fold_right]; auto.
        rewrite IH; reflexivity.
      Qed.

      Lemma interp_to_idx_fold : forall (store env : locals) (l : list value) (d0 : value),
          fold_right
            (fun v a => interp_expr store (map.put (map.put env tup v) acc a)
                          (ETernop OInsert (EVar acc) (EAccess (EVar tup) attr) (EVar tup)))
            d0 l
          = fold_right idx_step d0 l.
      Proof.
        intros; induction l as [| r l IH]; cbn [fold_right]; auto.
        rewrite IH, interp_idx_body; reflexivity.
      Qed.

      Lemma fiat2_gallina_to_idx : forall (l : list value),
          interp_expr map.empty (map.put map.empty hole (VList l)) to_idx
          = VDict (idx_entries l).
      Proof.
        intros. unfold to_idx.
        rewrite interp_EFold, interp_EVar, interp_EAtom.
        unfold get_local; rewrite map.get_put_same.
        cbn beta iota; cbn [interp_atom].
        rewrite interp_to_idx_fold. apply fold_idx_step.
      Qed.

      (* ------------------------------------------------------------------
         What maintaining the index takes, in Gallina.

         Both facts are about idx_entries alone, so they are proved here and
         the rewrite rules in UniqueIndexUse only have to connect a program
         to them.
         ------------------------------------------------------------------ *)

      Local Coercion is_true : bool >-> Sortclass.

      (* The entries are a canonical dictionary: every row goes in through
         dict_insert, which keeps the keys strictly increasing. *)
      Lemma idx_entries_SSorted : forall (l : list value),
          StronglySorted dict_entry_leb (idx_entries l).
      Proof.
        induction l as [| r l IH]; cbn [idx_entries fold_right].
        - constructor.
        - apply dict_insert_preserve_SSorted; exact IH.
      Qed.

      (* Dropping from the table every row whose key is k deletes exactly k's
         entry.  Nothing is assumed about the keys being distinct: a row
         contributes only to its own key's entry, so the rows that leave can
         affect only the entry they all share.  That is why a keyed delete is
         maintainable here with no declaration at all. *)
      Lemma idx_entries_filter_neq : forall (l : list value) (k : value),
          idx_entries (filter (fun r => negb (value_eqb (row_key attr r) k)) l)
          = dict_delete k (idx_entries l).
      Proof.
        induction l as [| r l IH]; intros k; cbn [idx_entries filter fold_right];
          [ reflexivity | ].
        destruct (value_eqb (row_key attr r) k) eqn:E; cbn [negb].
        - (* the row leaves, and its key's entry is the one being deleted *)
          apply value_eqb_eq in E; rewrite E.
          rewrite dict_delete_insert_same by apply idx_entries_SSorted.
          apply IH.
        - (* the row stays, and the deletion passes under its insertion *)
          cbn [idx_entries fold_right]. rewrite IH.
          symmetry; apply dict_delete_insert_diff;
            [ apply not_eq_sym, value_eqb_neq; exact E
            | apply idx_entries_SSorted ].
      Qed.

      Instance unique_dict_idx : IndexInterface.index :=
        IndexInterface.mk hole to_idx idx_ty is_tbl_ty.

      Instance unique_dict_idx_ok : IndexInterface.ok unique_dict_idx idx_wf :=
        IndexInterface.Build_ok unique_dict_idx idx_wf idx_ty_wf to_idx_ty to_idx_wf.

      (* ------------------------------------------------------------------
         The same index, as an index for a primary key.

         Above, idx_wf says only that the dictionary is the one to_idx builds,
         which is all that holds of every well-typed table.  A primary key's
         index claims more -- that a key names one row -- and that claim is
         about tables with distinct keys and no others.  So it is stated
         separately, as a conjunction with the precondition that makes it
         true.  The two are not alternatives: the weak idx_wf above is what an
         index-maintaining transformation establishes on its own, and the
         strong one below is what a rewrite rule needs.  Nothing is owed at
         installation -- idx_wf_unique is assembled from the two where a rule
         needs it, by UniqueIndexInstall.idx_wf__idx_wf_unique.
         ------------------------------------------------------------------ *)

      Definition keys_distinct (tbl_v : value) : Prop :=
        match tbl_v with
        | VList l => NoDup (List.map (row_key attr) l)
        | _ => False
        end.

      Definition idx_wf_unique (tbl_v idx_v : value) : Prop :=
        idx_wf tbl_v idx_v /\ keys_distinct tbl_v.

      (* ------------------------------------------------------------------
         The index's keys are exactly the table's keys.
         ------------------------------------------------------------------ *)

      (* No uniqueness is needed for this one: every row inserts its own key,
         so a key is absent from the dictionary exactly when no row carries
         it.  This is the whole of what the write guard asks, which is why the
         guard rewrite below assumes nothing about the index beyond idx_wf. *)
      Lemma idx_lookup_None_iff : forall (l : list value) (k : value),
          dict_lookup k (idx_entries l) = None
          <-> ~ In k (List.map (row_key attr) l).
      Proof.
        intros l; induction l as [| r l IH]; intros k;
          cbn [idx_entries fold_right List.map In].
        1: split; auto.
        destruct (value_eqb_dec k (row_key attr r)) as [ E | E ].
        1:{ subst. rewrite DictIndexImpl.dict_lookup_insert_same.
            split.
            1: discriminate.
            1: intro H; exfalso; apply H; left; reflexivity. }
        1:{ rewrite DictIndexImpl.dict_lookup_insert_diff by assumption.
            rewrite IH. split.
            1: intros H_ni [ H_eq | H_in ]; auto.
            1: intros H_ni H_in; apply H_ni; right; assumption. }
      Qed.

      (* With the keys distinct -- which is exactly what a declared primary
         key gives -- the index answers a point query. *)
      Lemma idx_lookup_Some : forall (l : list value) (r : value),
          NoDup (List.map (row_key attr) l) ->
          In r l ->
          dict_lookup (row_key attr r) (idx_entries l) = Some r.
      Proof.
        induction l as [| r0 l IH]; cbn [idx_entries fold_right List.map In];
          intros r H_nd H_in.
        1: contradiction.
        rewrite NoDup_cons_iff in H_nd; destruct H_nd as [ H_fresh H_nd ].
        destruct H_in as [ H_eq | H_in ].
        1:{ subst. apply DictIndexImpl.dict_lookup_insert_same. }
        1:{ assert (H_kne : row_key attr r <> row_key attr r0).
            { intro contra; apply H_fresh; rewrite <- contra.
              apply in_map; assumption. }
            rewrite DictIndexImpl.dict_lookup_insert_diff by assumption.
            apply IH; assumption. }
      Qed.

      (* And nothing else is in it: a hit names a row of the table carrying
         that key.  No uniqueness needed here either, since every entry was
         put there by some row. *)
      Lemma idx_lookup_Some_inv : forall (l : list value) (k r : value),
          dict_lookup k (idx_entries l) = Some r ->
          In r l /\ row_key attr r = k.
      Proof.
        intros l; induction l as [| r0 l IH]; intros k r;
          cbn [idx_entries fold_right In]; intros H_lk.
        1: discriminate.
        destruct (value_eqb_dec k (row_key attr r0)) as [ E | E ].
        1:{ subst. rewrite DictIndexImpl.dict_lookup_insert_same in H_lk.
            injection H_lk as H_lk; subst. split; auto. }
        1:{ rewrite DictIndexImpl.dict_lookup_insert_diff in H_lk by assumption.
            apply IH in H_lk. intuition auto. }
      Qed.

      (* ------------------------------------------------------------------
         The bridge: the write guard is one lookup.
         ------------------------------------------------------------------ *)

      (* Constraint.unique_guard_iff_fresh proves that the guard the
         elaboration inserts at an insertion is the test "this key is not
         among the table's keys"; idx_lookup_None_iff proves that the index's
         keys are the table's keys.  Composing them: the guard, which scans
         the table, has the same value as one lookup in the index.  Nothing
         about the index beyond idx_wf is used, and the uniqueness assumption
         appears only where Constraint.v needs it. *)
      Theorem guard_iff_lookup_None :
        forall rt kt free_vars e tbl l (Gstore Genv : tenv) (store env : locals),
          tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
          access_record rt attr = Success kt ->
          map.get Gstore tbl = Some (TList (TRecord rt)) ->
          type_of Gstore Genv e (TRecord rt) ->
          incl (get_free_vars Genv) free_vars ->
          locals_wf Gstore store -> locals_wf Genv env ->
          map.get store tbl = Some (VList l) ->
          NoDup (List.map (row_key attr) l) ->
          (interp_expr store env
             (constr_guard (unique_constr attr (TRecord rt)) free_vars
                (EBinop OCons e (ELoc tbl))) = VBool true
           <-> dict_lookup (row_key attr (interp_expr store env e))
                 (idx_entries l) = None).
      Proof.
        intros * H_Gs H_Ge H_rt H_attr H_tbl H_e H_fv H_store H_env E_tbl H_nd.
        pose proof (unique_guard_iff_fresh attr rt kt free_vars e tbl l
                      Gstore Genv store env H_Gs H_Ge H_rt H_attr H_tbl H_e
                      H_fv H_store H_env E_tbl H_nd) as H_guard.
        pose proof (idx_lookup_None_iff l (row_key attr (interp_expr store env e)))
          as H_lookup.
        tauto.
      Qed.


      (* ------------------------------------------------------------------
         The cheap guard.
         ------------------------------------------------------------------ *)

      (* The write is allowed exactly when the index holds no entry under the
         new row's key.  There is no OIsNone, so the test is an option match
         whose branches are the two booleans; y names the row that would be
         displaced and is never read. *)
      Definition unique_guard (idx_e : expr) (y : string) (e : expr) : expr :=
        EOptMatch (EBinop OLookup idx_e (EAccess e attr))
          (EAtom (ABool true)) y (EAtom (ABool false)).

      Lemma unique_guard_ty : forall rt kt idx_e y e (Gstore Genv : tenv),
          access_record rt attr = Success kt ->
          type_of Gstore Genv idx_e (TDict kt (TRecord rt)) ->
          type_of Gstore Genv e (TRecord rt) ->
          type_of Gstore Genv (unique_guard idx_e y e) TBool.
      Proof.
        unfold unique_guard; intros * H_attr H_idx H_e.
        econstructor.
        1:{ econstructor.
            1: constructor.
            1: exact H_idx.
            1: econstructor; [ exact H_e | exact H_attr ]. }
        1: repeat constructor.
        1: repeat constructor.
      Qed.

      Lemma unique_guard_interp : forall (store env : locals) idx_e y e d,
          interp_expr store env idx_e = VDict d ->
          interp_expr store env (unique_guard idx_e y e)
          = VBool (match dict_lookup (row_key attr (interp_expr store env e)) d with
                   | None => true
                   | Some _ => false
                   end).
      Proof.
        unfold unique_guard, row_key; intros * H_idx.
        rewrite interp_EOptMatch, interp_EBinop, interp_EAccess, H_idx.
        cbn [interp_binop].
        lazymatch goal with
        | |- context[dict_lookup ?k d] => destruct (dict_lookup k d)
        end; rewrite interp_EAtom; reflexivity.
      Qed.

      (* The declared guard and the index guard agree.  This is the equality
         of guards a rewrite asks for: on the left one lookup, on the right
         the test the constraint elaboration inserts, which scans the table.

         Both hypotheses on the store are needed, and they come from different
         places: idx_wf says the index is the table's own dictionary, which an
         index-maintaining transformation establishes, and NoDup says the keys
         are distinct, which the declared primary key establishes.  Neither
         implies the other. *)
      Theorem unique_guard_sound :
        forall rt kt free_vars y e idx_e tbl l (Gstore Genv : tenv) (store env : locals),
          tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
          access_record rt attr = Success kt ->
          map.get Gstore tbl = Some (TList (TRecord rt)) ->
          type_of Gstore Genv e (TRecord rt) ->
          incl (get_free_vars Genv) free_vars ->
          locals_wf Gstore store -> locals_wf Genv env ->
          map.get store tbl = Some (VList l) ->
          NoDup (List.map (row_key attr) l) ->
          idx_wf (VList l) (interp_expr store env idx_e) ->
          interp_expr store env (unique_guard idx_e y e)
          = interp_expr store env
              (constr_guard (unique_constr attr (TRecord rt)) free_vars
                 (EBinop OCons e (ELoc tbl))).
      Proof.
        intros * H_Gs H_Ge H_rt H_attr H_tbl H_e H_fv H_store H_env E_tbl H_nd H_idx.
        (* the index is the table's own dictionary *)
        unfold idx_wf in H_idx; rewrite fiat2_gallina_to_idx in H_idx.
        (* the declared guard is a boolean *)
        assert (H_cons_ty : type_of Gstore Genv (EBinop OCons e (ELoc tbl))
                              (TList (TRecord rt)))
          by (econstructor; [ constructor | exact H_e | constructor; exact H_tbl ]).
        assert (H_guard_ty : type_of Gstore Genv
                               (constr_guard (unique_constr attr (TRecord rt)) free_vars
                                  (EBinop OCons e (ELoc tbl))) TBool).
        { eapply constr_guard_ty with (row_ty := TRecord rt).
          1: exact H_Gs.
          1: exact H_Ge.
          1: exact H_rt.
          1: eapply unique_constr_wf; [ exact H_rt | exact H_attr ].
          1: exact H_cons_ty.
          1: exact H_fv. }
        assert (H_rhs : type_of_value
                          (interp_expr store env
                             (constr_guard (unique_constr attr (TRecord rt)) free_vars
                                (EBinop OCons e (ELoc tbl)))) TBool)
          by (eapply type_sound; eauto).
        (* and it is true exactly when the lookup misses *)
        pose proof (guard_iff_lookup_None rt kt free_vars e tbl l Gstore Genv store env
                      H_Gs H_Ge H_rt H_attr H_tbl H_e H_fv H_store H_env E_tbl H_nd)
          as H_iff.
        rewrite (unique_guard_interp store env idx_e y e (idx_entries l) H_idx).
        destruct (type_of_value_TBool _ H_rhs) as [ H_t | H_f ].
        1:{ (* the declared guard passes, so the key is free and so does the
               lookup test *)
            rewrite H_t, (proj1 H_iff H_t). reflexivity. }
        1:{ (* the declared guard fails, so the key is taken: were the lookup a
               miss, the declared guard would have passed *)
            rewrite H_f. f_equal. apply option_is_some_bool.
            intro H_none. rewrite (proj2 H_iff H_none) in H_f. discriminate H_f. }
      Qed.


      (* The same soundness with one store hypothesis instead of two.

         This is the shape a rewrite rule can be stated in.  What
         expr_aug_transf_sound hands a rule is a single predicate about the
         store entry it rewrites at, so a rule that wants two facts about that
         entry has nowhere to put the second one.  Folding the constraint into
         the index's own well-formedness puts it exactly where the framework
         already carries it.  Installation is unaffected: the index goes in
         under the weak idx_wf, and whoever uses THIS corollary owes the
         strong one. *)
      Corollary unique_guard_sound_pre :
        forall rt kt free_vars y e idx_e tbl l (Gstore Genv : tenv) (store env : locals),
          tenv_wf Gstore -> tenv_wf Genv -> type_wf (TRecord rt) ->
          access_record rt attr = Success kt ->
          map.get Gstore tbl = Some (TList (TRecord rt)) ->
          type_of Gstore Genv e (TRecord rt) ->
          incl (get_free_vars Genv) free_vars ->
          locals_wf Gstore store -> locals_wf Genv env ->
          map.get store tbl = Some (VList l) ->
          idx_wf_unique (VList l) (interp_expr store env idx_e) ->
          interp_expr store env (unique_guard idx_e y e)
          = interp_expr store env
              (constr_guard (unique_constr attr (TRecord rt)) free_vars
                 (EBinop OCons e (ELoc tbl))).
      Proof.
        intros * H_Gs H_Ge H_rt H_attr H_tbl H_e H_fv H_store H_env E_tbl H_wf.
        unfold idx_wf_unique in H_wf; destruct H_wf as [ H_idx H_nd ].
        cbn [keys_distinct] in H_nd.
        exact (unique_guard_sound rt kt free_vars y e idx_e tbl l Gstore Genv store env
                 H_Gs H_Ge H_rt H_attr H_tbl H_e H_fv H_store H_env E_tbl H_nd H_idx).
      Qed.

    End WithMap.
  End WithVars.
End WithHole.
