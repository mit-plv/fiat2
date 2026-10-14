Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.Utils fiat2.Substitute
  fiat2.IndexTransf fiat2.Constraint fiat2.DictIndexImpl fiat2.FlatmapForms fiat2.TransfUtils
  fiat2.UniqueDictIndexImpl fiat2.UniqueIndexInstall fiat2.UniqueIndexGate
  fiat2.Surface.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List Permutation Sorted.

Import ListNotations.

(* Using the key-to-row index: a point query becomes one lookup.

   The rewrite replaces a scan that filters the table on the key attribute by
   a single lookup in the dictionary.  What makes it correct is uniqueness:
   without it the scan can return several rows and the dictionary only one, so
   the two differ.  With it the scan returns at most one row, and the
   dictionary holds exactly that one.

   Uniqueness is not something the index establishes -- to_idx builds the
   dictionary for any table, keeping one row per key and forgetting the rest.
   It is what the program maintains and what the installation carries, which
   is why this rule is proved against the strong relation rather than against
   the index's own idx_wf -- see unique_bridges, whose third component is the
   only thing here that a declaration-free index does not also owe. *)

Section WithWord.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).
  Context (attr : string).

  (* ------------------------------------------------------------------
     The scan and the lookup agree, as lists.
     ------------------------------------------------------------------ *)

  (* No row carries a key the table does not have. *)
  Lemma filter_key_eq_nil : forall (l : list value) (k : value),
      ~ In k (List.map (row_key attr) l) ->
      List.filter (fun r => value_eqb (row_key attr r) k) l = nil.
  Proof.
    intros l k; induction l as [| r l IH]; cbn [List.filter List.map In];
      auto; intros H_ni.
    destruct (value_eqb_dec (row_key attr r) k) as [ E | E ].
    1:{ exfalso. apply H_ni. left. exact E. }
    1:{ apply IH. intro H_in. apply H_ni. right. exact H_in. }
  Qed.

  (* And with the keys distinct, a row's key names that row and no other --
     so the scan the rewrite replaces returns exactly one row. *)
  Lemma filter_key_eq_singleton : forall (l : list value) (r : value),
      NoDup (List.map (row_key attr) l) ->
      In r l ->
      List.filter (fun r' => value_eqb (row_key attr r') (row_key attr r)) l = [r].
  Proof.
    intros l r; induction l as [| r0 l IH]; cbn [List.filter List.map In];
      intros H_nd H_in.
    1: contradiction.
    rewrite NoDup_cons_iff in H_nd; destruct H_nd as [ H_fresh H_nd ].
    destruct H_in as [ E_r | H_in ].
    1:{ subst r0. rewrite value_eqb_refl. f_equal.
        apply filter_key_eq_nil. exact H_fresh. }
    1:{ destruct (value_eqb_dec (row_key attr r0) (row_key attr r)) as [ E | E ].
        1:{ exfalso. apply H_fresh. rewrite E. apply in_map. exact H_in. }
        1: apply IH; assumption. }
  Qed.

  (* The two sides of the rewrite, as bags. *)
  Lemma filter_key_eq_lookup : forall (l : list value) (k : value),
      NoDup (List.map (row_key attr) l) ->
      list_to_bag (List.filter (fun r => value_eqb (row_key attr r) k) l)
      = match dict_lookup k (idx_entries attr l) with
        | Some r => bag_insert r nil
        | None => nil
        end.
  Proof.
    intros l k H_nd.
    destruct (dict_lookup k (idx_entries attr l)) as [ r | ] eqn:E_lk.
    1:{ destruct (idx_lookup_Some_inv attr l k r E_lk) as [ H_in E_key ].
        subst k. rewrite filter_key_eq_singleton by assumption. reflexivity. }
    1:{ rewrite filter_key_eq_nil; [ reflexivity | ].
        apply (proj1 (idx_lookup_None_iff attr l k)); exact E_lk. }
  Qed.
End WithWord.

Section WithIndexUse.
  (* the names the index's own fold binds *)
  Context (hole attr tup acc : string).
  Context (H_ne : tup <> acc).
  (* the two fields the installation pairs *)
  Context (id_tag aux_tag : string).
  Context (H_tags_diff : id_tag <> aux_tag).
  (* and the tag this dictionary sits under inside the index record, so that
     one record may hold it beside the ordinary indexes *)
  Context (idx_tag : string).
  (* the binder the rewritten form introduces for the row it found *)
  Context (y : string).

  Notation uidx := (unique_dict_idx hole attr tup acc).

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (width:=width)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Notation uidx_wf := (UniqueDictIndexImpl.idx_wf hole attr tup acc (locals := locals)).

    (* The strong invariant as it appears once the dictionary sits inside an
       index record: the member at idx_tag is a faithful key-to-row map of the
       table at id_tag.  This is TransfUtils' aux_wf_for_idx -- the shape every
       member rule is stated against -- with the STRONG relation plugged in
       where an ordinary member would put its own idx_wf.  That is the whole
       difference a declared constraint makes to a use rule. *)
    Notation unique_aux_wf_at :=
      (aux_wf_for_idx id_tag aux_tag idx_tag
         (idx_wf_unique hole attr tup acc (locals := locals))).

    Section WithTable.
      Context (tbl : string).

      (* [row <- tbl[id_tag], check(row.attr == e'), ret row]  (as a bag)
         -->
         match lookup tbl[aux_tag][idx_tag] e' with
         | none => emptybag | some y => {y} *)
      Definition unique_lookup_head (e : expr) : expr :=
        match e with
        | flatmap_filter_bag
            (EBagOf (EAccess (ELoc tbl0) id_tag0))
            x0 (EBinop OEq (EAccess (EVar x1) attr0) e') x2 _ _ =>
            if (all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x0, [x1; x2]); (id_tag, [id_tag0])] &&
                  negb (free_immut_in x0 e'))%bool
            then EOptMatch (EBinop OLookup (EAccess (EAccess (ELoc tbl) aux_tag) idx_tag) e')
                   (EAtom (AEmptyBag None))
                   y (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar y))
            else e
        | _ => e
        end.

      Lemma unique_lookup_head_preserve_ty : forall tl ctl t (Gstore : tenv),
          type_wf t -> @IndexInterface.is_tbl_ty uidx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl idx_tag = Success (@IndexInterface.idx_ty uidx t) ->
          preserve_ty Gstore unique_lookup_head.
      Proof.
        unfold preserve_ty, IndexInterface.is_tbl_ty, IndexInterface.idx_ty,
          unique_dict_idx, UniqueDictIndexImpl.is_tbl_ty,
          UniqueDictIndexImpl.idx_ty in *.
        intros.
        repeat destruct_match_hyp; try congruence.
        repeat destruct_subexpr. simpl.
        case_match; auto. repeat rewrite Bool.andb_true_r in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        rewrite Bool.negb_true_iff, eqb_eq in *; subst.
        repeat invert_type_of_clear. repeat invert_type_of_op_clear.
        repeat rewrite_map_get_put_hyp.
        repeat (clear_refl; repeat do_injection2).
        repeat (rewrite_l_to_r; do_injection2).
        repeat (econstructor; eauto).
        1:{ unfold get_attr_type.
            lazymatch goal with H: ?x = _ |- context[?x] => rewrite H end.
            eapply not_free_immut_put_ty; eauto. }
        (* selected with all:, not by position: the extra record access the
           rewrite now goes through reorders what econstructor leaves *)
        all: repeat invert_type_wf; auto.
        all: rewrite map.get_put_same; trivial.
      Qed.

      (* The scan and the lookup agree.  The store hypothesis is the strong
         invariant: the record's index field is the dictionary to_idx builds
         from its table field, and the table's keys are distinct.  Without the
         second the equation is false -- the scan would return every row
         carrying the key and the dictionary only one. *)
      Lemma unique_lookup_head_preserve_sem :
        forall tl ctl t (Gstore : tenv) (store : locals),
          type_wf t -> @IndexInterface.is_tbl_ty uidx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl idx_tag = Success (@IndexInterface.idx_ty uidx t) ->
          match map.get store tbl with
          | Some v => unique_aux_wf_at v
          | _ => False
          end ->
          preserve_sem Gstore store unique_lookup_head.
      Proof.
        unfold preserve_sem, aux_wf_for_idx, UniqueDictIndexImpl.idx_wf_unique,
          UniqueDictIndexImpl.idx_wf, UniqueDictIndexImpl.keys_distinct,
          IndexInterface.is_tbl_ty, IndexInterface.idx_ty, unique_dict_idx,
          UniqueDictIndexImpl.is_tbl_ty, UniqueDictIndexImpl.idx_ty in *.
        intros.
        repeat (destruct_match_hyp; try discriminate; intuition idtac; []).
        rewrite fiat2_gallina_to_idx in * by assumption.
        repeat destruct_subexpr. unfold unique_lookup_head.
        cbv beta iota; case_match; auto.
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *; intuition idtac.
        rewrite Bool.negb_true_iff, eqb_eq in *; subst. repeat clear_refl.
        rewrite interp_flatmap_filter_bag.
        cbn [interp_expr interp_binop interp_atom].
        unfold get_local, record_proj.
        repeat rewrite_l_to_r.
        rewrite list_to_bag_filter_list_to_bag.
        erewrite In_filter_ext with
          (g := fun v => value_eqb (row_key attr v) (interp_expr store env e2_1_2)).
        2:{ intros v H_in. rewrite map.get_put_same. f_equal.
            symmetry; apply not_free_immut_put_sem; assumption. }
        rewrite filter_key_eq_lookup by assumption.
        (* matched rather than named: the extra record access adds a value
           list to the context and shifts the generated names *)
        lazymatch goal with
        | |- context[dict_lookup ?k (idx_entries _ ?rows)] =>
            destruct (dict_lookup k (idx_entries attr rows))
        end;
          [ rewrite map.get_put_same | ]; reflexivity.
      Qed.

      (* The row type a declared key carries is a typing annotation, not part
         of what the key means: it occurs in unique_constr only inside the
         empty-list atoms the counting expression builds, and interp_atom
         ignores an annotation.  This is what lets the rule read the key off
         the invariant without first having to know that the row type the
         declarations were written against is the one the store's table
         actually has. *)
      Lemma unique_constr_holds_row_ty_irrel : forall rty1 rty2 (v : value),
          constr_holds (locals:=locals) (unique_constr attr rty1) v ->
          constr_holds (locals:=locals) (unique_constr attr rty2) v.
      Proof.
        unfold constr_holds, constr_expr, unique_constr; cbn [c_row c_body].
        intros rty1 rty2 v H. rewrite <- H.
        cbn [interp_expr interp_atom]. reflexivity.
      Qed.
    End WithTable.
    (* aux_ty_access_id's companion.  IndexTransf proves only the id side,
       since the installation itself never reads the index field by name. *)
    Lemma record_sort_access_aux : forall (t1 t2 : type),
        access_record (record_sort [(id_tag, t1); (aux_tag, t2)]) aux_tag = Success t2.
    Proof.
      intros. apply NoDup_In_access_record.
      1: NoDup_map_record_sort.
      eapply Permutation_in; [ apply Permuted_record_sort | ]; cbn; auto.
    Qed.

    Corollary aux_ty_access_aux : forall tbl_ty,
        access_record
          (record_sort [(id_tag, tbl_ty); (aux_tag, @IndexInterface.idx_ty uidx tbl_ty)])
          aux_tag
        = Success (@IndexInterface.idx_ty uidx tbl_ty).
    Proof. intros. apply record_sort_access_aux. Qed.


    (* A declared key is one of the declared constraints, so the conjunction
       the installation carries yields it.  Stated at an arbitrary row type,
       unlike UniqueIndexGate's version, because here the row type the
       declarations mention and the one the store's table has are not yet
       known to agree -- and by unique_constr_holds_row_ty_irrel they need not. *)
    Lemma declares_unique__constr_holds : forall row_ty ds (v : value),
        declares_unique attr ds = true ->
        declared_holds (locals := locals) row_ty ds v ->
        constr_holds (locals := locals) (unique_constr attr row_ty) v.
    Proof.
      unfold declares_unique, declared_holds, constrs_hold, constrs_of_decls.
      intros * H_ex H_all.
      apply existsb_exists in H_ex as [ d [ H_in H_d ] ].
      destruct d; cbn [decl_is_unique] in H_d; try discriminate.
      rewrite String.eqb_eq in H_d; subst.
      rewrite Forall_forall in H_all. apply H_all.
      apply in_map_iff. exists (DUnique attr); split; [ reflexivity | assumption ].
    Qed.

    (* ------------------------------------------------------------------
       Projecting this member out of an index record, and strengthening it
       with the declaration.

       The record's own well-formedness gives the WEAK relation at idx_tag --
       the dictionary is whatever to_idx computed -- which is all any index
       establishes from typing alone.  The declaration gives the keys'
       distinctness.  The value's type is what lets the two be combined, and
       it is available at every rewrite site from locals_wf.
       ------------------------------------------------------------------ *)
    Lemma compo_declared__unique_aux_wf_at :
      forall idxs rt kt row_ty ds (v : value),
        In (idx_tag, uidx, uidx_wf) idxs ->
        declares_unique attr ds = true ->
        type_wf (TRecord rt) ->
        access_record rt attr = Success kt ->
        type_of_value v
          (aux_ty (idx := compo_idx idxs hole) id_tag aux_tag (TList (TRecord rt))) ->
        aux_wf (idx_wf := compo_idx_wf idxs) id_tag aux_tag v ->
        at_id_tag id_tag (declared_holds (locals := locals) row_ty ds) v ->
        unique_aux_wf_at v.
    Proof.
      unfold aux_wf, at_id_tag, aux_wf_for_idx, compo_idx_wf.
      intros * H_in H_uq H_rt H_attr H_ty H_aux H_id.
      repeat destruct_match_hyp; try contradiction.
      eapply List.Forall_In in H_aux as H_mem; [ | exact H_in ]; cbn in H_mem.
      repeat destruct_match_hyp; try contradiction.
      (* the map and word instances are named: none of them occurs in the
         lemma's conclusion, so from outside its section eapply turns each one
         it cannot determine into a goal of its own *)
      eapply (idx_wf__idx_wf_unique hole attr tup acc
                (tenv := tenv) (tenv_ok := tenv_ok)
                (word_ok := word_ok) (locals_ok := locals_ok));
        [ exact H_rt | exact H_attr | | exact H_mem | ].
      1:{ eapply type_of_value_at_id_tag; [ exact H_tags_diff | exact H_ty | eassumption ]. }
      1:{ eapply unique_constr_holds_row_ty_irrel.
          eapply declares_unique__constr_holds; [ exact H_uq | exact H_id ]. }
    Qed.

    (* ------------------------------------------------------------------
       The rule, in the shape every member rule has: abstract in the record
       the installation builds, with the bridges to this member supplied by
       whoever assembles the record (compare DictIndexImpl's
       eq_filter_to_lookup_head_sound).

       A declared index changes exactly one thing here -- which relation the
       third bridge carries.  An ordinary member asks for its own idx_wf,
       which the install manufactures from typing; this one asks for the
       strong relation, which it cannot, and which the lemma above extracts
       from the declarations instead.  Nothing else about the rule is
       conditional on the program.
       ------------------------------------------------------------------ *)
    Lemma unique_lookup_head_sound :
      forall is_tbl_ty' aux_ty (aux_wf : value -> Prop),
        aux_ty_for_idx id_tag aux_tag idx_tag (@IndexInterface.idx_ty uidx) aux_ty ->
        (forall t, is_tbl_ty' t = true -> @IndexInterface.is_tbl_ty uidx t = true) ->
        (* the strengthening needs the value's TYPE, which is not part of a
           value predicate -- an ordinary member's bridge does not.  Every
           rewrite site has it, from locals_wf. *)
        (forall (t : type) (v : value),
            type_wf t -> is_tbl_ty' t = true ->
            type_of_value v (aux_ty t) -> aux_wf v -> unique_aux_wf_at v) ->
        expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf unique_lookup_head.
    Proof.
      unfold aux_ty_for_idx, expr_aug_transf_sound; intros * H_aty H_is H_wf *.
      intros H_Gs H_Ge H_twf H_is' H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl end.
      specialize (H_aty tbl_ty).
      repeat destruct_match_hyp; intuition idtac.
      1:{ repeat rewrite_l_to_r.
          eapply unique_lookup_head_preserve_ty; eauto using H_is. }
      1:{ repeat rewrite_l_to_r.
          eapply unique_lookup_head_preserve_sem; eauto using H_is.
          (* all that is left is that the store carries the strong invariant
             at the table, which is the third bridge *)
          lazymatch goal with
            H : locals_wf Gstore _ |- _ => specialize (H _ _ E_tbl)
          end.
          destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
          lazymatch goal with
            H : holds_for_all_entries _ _ |- _ => specialize (H _ _ E_v)
          end.
          unfold value_wf_with_globals in *; invert_Forall.
          lazymatch goal with
            H : _ \/ _ |- _ => destruct H as [ H_neq | H_aw ]; [ congruence | ]
          end.
          eapply H_wf; [ exact H_twf | exact H_is' | | exact H_aw ].
          lazymatch goal with E : aux_ty tbl_ty = _ |- _ => rewrite E end.
          assumption. }
    Qed.

    (* The three bridges, named once: what whoever assembles the record owes
       this member. *)
    Definition unique_bridges (is_tbl_ty' : type -> bool) (aux_ty : type -> type)
      (aux_wf : value -> Prop) : Prop :=
      aux_ty_for_idx id_tag aux_tag idx_tag (@IndexInterface.idx_ty uidx) aux_ty
      /\ (forall t, is_tbl_ty' t = true -> @IndexInterface.is_tbl_ty uidx t = true)
      /\ (forall (t : type) (v : value),
             type_wf t -> is_tbl_ty' t = true ->
             type_of_value v (aux_ty t) -> aux_wf v -> unique_aux_wf_at v).

    (* The rule, applied everywhere below the installation. *)
    Definition unique_lookup_transf : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl] (unique_lookup_head tbl).

    Lemma unique_lookup_transf_sound : forall is_tbl_ty' aux_ty aux_wf,
        unique_bridges is_tbl_ty' aux_ty aux_wf ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf unique_lookup_transf.
    Proof.
      intros * [ H_aty [ H_is H_wf ] ]. unfold unique_lookup_transf.
      apply fold_command_with_globals_sound.
      apply unique_lookup_head_sound; assumption.
    Qed.

    (* ------------------------------------------------------------------
       The rule as the pipeline uses it: the identity unless the table's
       declarations name this key.

       The gate takes the declarations rather than looking them up, because
       aug_transf_sound quantifies over the table internally while the
       invariant it carries is fixed by the one installation -- so the rule
       and the invariant have to be gated on the same declarations, and those
       are the installed table's.  The install site does the lookup.

       What this buys is the whole point: the bridges are owed only where the
       gate fires, so an undeclared table owes nothing at all.
       ------------------------------------------------------------------ *)
    Definition unique_lookup_gated (ds : list decl) : string -> command -> command :=
      if declares_unique attr ds then unique_lookup_transf else fun _ => id.

    Lemma unique_lookup_gated_sound : forall ds is_tbl_ty' aux_ty aux_wf,
        (declares_unique attr ds = true -> unique_bridges is_tbl_ty' aux_ty aux_wf) ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf (unique_lookup_gated ds).
    Proof.
      intros * H_br. unfold unique_lookup_gated.
      destruct (declares_unique attr ds) eqn:E_uq.
      1: apply unique_lookup_transf_sound, H_br; reflexivity.
      1: unfold aug_transf_sound, id; intros; repeat split; auto.
    Qed.

    (* ------------------------------------------------------------------
       Joining the pipeline: install unconditionally, and let the rule gate
       itself.

       The installation is the same function whether or not anything is
       declared: it is sound for any table, because the index's OWN
       well-formedness is the weak one, which to_idx establishes from typing
       alone.  What the declarations decide is only which invariant the
       installation PROPAGATES, and so whether the use rule may fire.  That
       decision is taken in the proof below, not in the function -- which is
       why a declaration-dependent index needs no gate of its own, and why a
       hint asking for it on an undeclared table costs only a dictionary
       nobody reads.
       ------------------------------------------------------------------ *)

    (* The record this index sits in.  A singleton here; the same statements
       hold of any record that has this member, which is what
       compo_declared__unique_aux_wf_at is quantified over. *)
    Notation uidx_entry := (idx_tag, uidx, uidx_wf).
    Notation uidx_rec := (compo_idx [uidx_entry] hole).

    Lemma uidx_entry_ok :
      Forall (fun '(_, idx, idx_wf) => IndexInterface.ok idx idx_wf) [uidx_entry].
    Proof.
      constructor; [ | constructor ].
      cbn. apply (unique_dict_idx_ok hole attr tup acc H_ne).
    Qed.

    Lemma uidx_rec_ok :
      IndexInterface.ok uidx_rec (compo_idx_wf [uidx_entry]).
    Proof.
      apply (compo_idx_ok [uidx_entry] (idxs_ok := uidx_entry_ok));
        [ cbn; repeat constructor; cbn; intuition idtac
        | cbn; repeat constructor; reflexivity ].
    Qed.

    (* What the record owes this member, discharged for the record above.
       The third bridge is where the declaration is spent: it is the only one
       that needs it, and the only one an ordinary member does not have. *)
    Lemma unique_bridges_compo : forall row_ty ds,
        declares_unique attr ds = true ->
        unique_bridges
          (@IndexInterface.is_tbl_ty uidx_rec)
          (aux_ty (idx := uidx_rec) id_tag aux_tag)
          (fun v => aux_wf (idx_wf := compo_idx_wf [uidx_entry]) id_tag aux_tag v
                    /\ at_id_tag id_tag (declared_holds (locals := locals) row_ty ds) v).
    Proof.
      intros row_ty ds H_uq. unfold unique_bridges; split; [ | split ].
      (* the record's layout exposes this member at idx_tag *)
      1:{ unfold aux_ty_for_idx, aux_ty; intros t; cbn [IndexInterface.idx_ty compo_idx].
          split.
          1: apply (aux_ty_access_id (idx := uidx_rec) id_tag aux_tag H_tags_diff).
          1:{ rewrite record_sort_access_aux.
              unfold compo_idx_ty; cbn [List.map].
              apply NoDup_In_access_record;
                [ NoDup_map_record_sort
                | eapply Permutation_in; [ apply Permuted_record_sort | ]; cbn; auto ]. } }
      (* a record of one index is a table type exactly when its member is *)
      1:{ intros t; cbn [IndexInterface.is_tbl_ty compo_idx compo_is_tbl_ty forallb].
          rewrite Bool.andb_true_r; trivial. }
      (* and the declaration strengthens the record's own well-formedness *)
      1:{ intros t v H_twf H_is H_ty [ H_aux H_id ].
          cbn [IndexInterface.is_tbl_ty compo_idx compo_is_tbl_ty forallb] in H_is.
          rewrite Bool.andb_true_r in H_is.
          unfold IndexInterface.is_tbl_ty, unique_dict_idx,
            UniqueDictIndexImpl.is_tbl_ty in H_is.
          repeat destruct_match_hyp; try discriminate.
          rewrite inb_true_iff in H_is.
          destruct (In_access_record _ _ _ H_is) as [ kt E_attr ].
          eapply compo_declared__unique_aux_wf_at;
            [ apply in_eq | exact H_uq | | exact E_attr | exact H_ty | exact H_aux | exact H_id ].
          invert_type_wf; assumption. }
    Qed.

    Definition decls_of (ce : cenv) (tbl : string) : list decl :=
      match cenv_lookup tbl ce with
      | Some (_, ds) => ds
      | None => []
      end.

    Definition unique_idx_transf (ce : cenv) (Gstore Genv : tenv) (c : command) : command :=
      match c with
      | CLetMut _ tbl _ =>
          apply_idx_related_transfs (idx := uidx_rec) id_tag aux_tag
            (unique_lookup_gated (decls_of ce tbl)) Gstore Genv c
      | _ => c
      end.

    (* A declaration of this key is the only thing that makes decls_of's
       lookup succeed with it, so the two branches below are exhaustive. *)
    Lemma declares_decls_of : forall ce tbl,
        declares_unique attr (decls_of ce tbl) = true ->
        exists row_ty ds, cenv_lookup tbl ce = Some (row_ty, ds) /\ ds = decls_of ce tbl.
    Proof.
      unfold decls_of; intros ce tbl H.
      destruct (cenv_lookup tbl ce) as [ [ row_ty ds ] | ] eqn:E;
        [ eauto | cbn in H; discriminate ].
    Qed.

    Theorem unique_idx_transf_sound : forall ce (Gstore Genv : tenv) c,
        tenv_wf Gstore -> tenv_wf Genv ->
        well_typed Gstore Genv c ->
        cenv_respected (locals := locals) ce Gstore Genv c ->
        well_typed Gstore Genv (unique_idx_transf ce Gstore Genv c)
        /\ forall (store env : locals),
            locals_wf Gstore store -> locals_wf Genv env ->
            interp_command store env (unique_idx_transf ce Gstore Genv c)
            = interp_command store env c.
    Proof.
      intros * H_Gs H_Ge H_wt H_ce. unfold unique_idx_transf.
      destruct c; try (split; [ assumption | intros; reflexivity ]).
      cbn [cenv_respected] in H_ce.
      destruct (declares_unique attr (decls_of ce x)) eqn:E_uq.
      (* declared: the installation propagates the declarations too, and the
         rule may fire *)
      1:{ destruct (declares_decls_of ce x E_uq) as [ row_ty [ ds [ E_look E_ds ] ] ].
          eapply (apply_idx_related_transfs_pre_sound
                    (idx_ok := uidx_rec_ok) id_tag aux_tag H_tags_diff
                    (declared_holds (locals := locals) row_ty ds));
            [ | assumption .. | apply H_ce; exact E_look ].
          rewrite <- E_ds.
          apply unique_lookup_gated_sound.
          intros H_uq'. apply unique_bridges_compo; exact H_uq'. }
      (* not declared: the rule is the identity, so the ordinary installation
         is enough -- and nothing is assumed about the program *)
      1:{ apply (apply_idx_related_transfs_sound
                   (idx_ok := uidx_rec_ok) id_tag aux_tag H_tags_diff);
            auto.
          apply unique_lookup_gated_sound.
          intros H_uq'; rewrite E_uq in H_uq'; discriminate. }
    Qed.
    (* And on an elaborated surface program the remaining premise is free. *)
    Corollary elab_unique_idx_transf_sound :
      forall sc ce free_vars (Gstore Genv : tenv) tbl row_ty ds,
        tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
        incl (get_free_vars Genv) free_vars ->
        Forall (decl_wf row_ty) ds ->
        well_typed Gstore Genv (elab ce free_vars (SLetConstrained tbl row_ty ds sc)) ->
        well_typed Gstore Genv
          (unique_idx_transf ((tbl, (row_ty, ds)) :: cenv_rm tbl ce) Gstore Genv
             (elab ce free_vars (SLetConstrained tbl row_ty ds sc)))
        /\ forall (store env : locals),
            locals_wf Gstore store -> locals_wf Genv env ->
            interp_command store env
              (unique_idx_transf ((tbl, (row_ty, ds)) :: cenv_rm tbl ce) Gstore Genv
                 (elab ce free_vars (SLetConstrained tbl row_ty ds sc)))
            = interp_command store env (elab ce free_vars (SLetConstrained tbl row_ty ds sc)).
    Proof.
      intros * H_Gs H_Ge H_rt H_fv H_ds H_wt.
      apply unique_idx_transf_sound; [ assumption .. | ].
      apply elab_cenv_respected; assumption.
    Qed.
  End WithMap.
End WithIndexUse.
