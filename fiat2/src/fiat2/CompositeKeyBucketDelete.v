(* ====================================================================
   Maintaining a PRIMARY-KEY member across a delete at a COMPOSITE key.

   This is the rule in the direction CompositeDictKeyedDelete does not go,
   and the two together are what make a table with both deletes pay for
   neither.  That file's rule reads the primary-key member to maintain the
   composite one; this one reads the COMPOSITE member to maintain the
   primary-key one.

   The write is a delete at the whole composite key:

     [row <- tbl, check(!(row.a1 == e1 && ... && row.an == en)), ret row]

   The composite member drops one entry with one ODelete
   (filter_neq_to_composite_delete_head).  The primary-key member is keyed
   on an attribute the filter never names, so no rule could tell which of
   its entries leave, and the member was REBUILT from the surviving rows --
   a linear pass that also kept the row list alive, which cost the keyed
   delete beside it its whole advantage.

   WHAT MAKES IT SERVABLE AFTER ALL: the rows that are leaving are exactly
   the composite member's bucket at the deleted key, and that bucket is one
   probe away.  So the rule emits a fold over the bucket that deletes one
   key per leaving row.  A fold wants a list and a bucket is a bag, so the
   bucket is coerced with ESort LikeBag -- and the coercion is sound here
   for a reason worth naming: deleting keys from a dictionary COMMUTES
   (dict_delete_comm below), so the order the sort happens to pick cannot
   be observed.  That is the whole content of fold_pk_del_Permutation, and
   it is why no new operator is needed.

   GATED on the key being declared unique, exactly as the rule in the other
   direction is.  With two rows at one key the primary-key member holds
   only one of them, and deleting that key would take out the row that
   stays; idx_entries_filter_cneq needs the NoDup for precisely that step.
   ==================================================================== *)
Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.CollectionTransf fiat2.FlatmapTransf fiat2.EraseField
  fiat2.Constraint fiat2.DictIndexImpl fiat2.FlatmapForms
  fiat2.IndexInterface fiat2.UniqueDictIndexImpl fiat2.UniqueIndexUse
  fiat2.Surface fiat2.UniqueIndexGate
  fiat2.CompositeDictIndexImpl fiat2.DictIndexKeyedDelete
  fiat2.CompositeDictKeyedDelete
  fiat2.TransfSound fiat2.TransfUtils
  fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Module CDI := fiat2.CompositeDictIndexImpl.
Module CKD := fiat2.CompositeDictKeyedDelete.

Section WithAttrs.

  (* attrs is the composite key the delete names in full; key is the single
     declared key the primary-key member is built on. *)
  Context (attrs : list string) (key : string).

  (* the spelling every dictionary lemma in Utils is stated at *)
  Local Coercion is_true : bool >-> Sortclass.

  Definition pk_del (d : list (value * value)) (r : value) : list (value * value) :=
    dict_delete (row_key key r) d.

  (* ==================================================================
     THE DICT ALGEBRA.  Four facts about deleting keys from a sorted
     association list; none of them mentions an index.
     ================================================================== *)

  Lemma dict_delete_SSorted : forall (k : value) d,
      StronglySorted dict_entry_leb d ->
      StronglySorted dict_entry_leb (dict_delete k d).
  Proof.
    induction d as [ | [ k0 v0 ] d IH ]; cbn [dict_delete]; intros H_sort;
      [ assumption | ].
    inversion H_sort; subst.
    destruct (value_eqb k k0); [ assumption | ].
    constructor; [ apply IH; assumption | ].
    eapply incl_Forall; [ apply dict_delete_incl | assumption ].
  Qed.

  (* Deleting two keys in either order gives the same dictionary.  Needs no
     well-formedness: dict_delete removes the FIRST entry at its key, and the
     two walks commute entry by entry. *)
  Lemma dict_delete_comm : forall (k k' : value) d,
      dict_delete k (dict_delete k' d) = dict_delete k' (dict_delete k d).
  Proof.
    induction d as [ | [ k0 v0 ] d IH ]; [ reflexivity | ].
    cbn [dict_delete].
    destruct (value_eqb k k0) eqn:E_k; destruct (value_eqb k' k0) eqn:E_k'.
    - apply value_eqb_eq in E_k, E_k'; subst; reflexivity.
    - cbn [dict_delete]; rewrite E_k; reflexivity.
    - cbn [dict_delete]; rewrite E_k'; reflexivity.
    - cbn [dict_delete]; rewrite E_k, E_k'; f_equal; apply IH.
  Qed.

  Lemma fold_pk_del_cons : forall (r : value) (rs : list value) d,
      fold_left pk_del (r :: rs) d
      = fold_left pk_del rs (dict_delete (row_key key r) d).
  Proof. reflexivity. Qed.

  (* THE REASON THE BUCKET MAY BE SORTED INTO A LIST.  The fold's result
     does not depend on the order it visits the leaving rows in. *)
  Lemma fold_pk_del_Permutation : forall (rs rs' : list value) d,
      Permutation rs rs' ->
      fold_left pk_del rs d = fold_left pk_del rs' d.
  Proof.
    intros rs rs' d H_perm. revert d.
    induction H_perm as [ | r rs rs' H_perm IH | r r' rs | rs rs1 rs' H1 IH1 H2 IH2 ];
      intros d.
    - reflexivity.
    - rewrite !fold_pk_del_cons; apply IH.
    - rewrite !fold_pk_del_cons, dict_delete_comm; reflexivity.
    - rewrite IH1; apply IH2.
  Qed.

  (* Deleting a key commutes with the whole fold.  This is what lets the
     fold_right that EFold actually computes stand for the fold_left the
     content lemma below is stated with. *)
  Lemma fold_pk_del_delete : forall (rs : list value) (k : value) d,
      dict_delete k (fold_left pk_del rs d)
      = fold_left pk_del rs (dict_delete k d).
  Proof.
    induction rs as [ | r rs IH ]; intros k d; [ reflexivity | ].
    rewrite !fold_pk_del_cons, IH, dict_delete_comm; reflexivity.
  Qed.

  Lemma fold_right_pk_del : forall (rs : list value) d,
      fold_right (fun r a => dict_delete (row_key key r) a) d rs
      = fold_left pk_del rs d.
  Proof.
    induction rs as [ | r rs IH ]; intros d; [ reflexivity | ].
    cbn [fold_right]; rewrite IH, fold_pk_del_cons, fold_pk_del_delete.
    reflexivity.
  Qed.

  (* An insertion at a key none of the leaving rows carries passes through
     the fold untouched. *)
  Lemma fold_pk_del_insert : forall (rs : list value) (k v : value) d,
      StronglySorted dict_entry_leb d ->
      ~ In k (List.map (row_key key) rs) ->
      fold_left pk_del rs (dict_insert k v d)
      = dict_insert k v (fold_left pk_del rs d).
  Proof.
    induction rs as [ | r rs IH ]; intros k v d H_sort H_ni; [ reflexivity | ].
    cbn [List.map] in H_ni.
    rewrite !fold_pk_del_cons.
    rewrite dict_delete_insert_diff
      by (assumption || (intro E; apply H_ni; left; exact E)).
    apply IH; [ apply dict_delete_SSorted; assumption | ].
    intro H_in; apply H_ni; right; exact H_in.
  Qed.

  (* ==================================================================
     THE CONTENT.  The primary-key map of the rows a composite key does
     not name is the stored map with one key deleted per row the composite
     key DOES name.

     NoDup is load-bearing and only in the second branch: without it the
     row that stays could share its key with a row that leaves, and the
     delete would take out the survivor's entry.

     STATED OVER AN ARBITRARY BUCKET KEY, because nothing in it depends on
     what files a row under which key -- only that the index files each row
     under exactly one.  So DictBucketPkDelete's arity-one rule instantiates
     this proof at row_key rather than repeating it, and the composite
     statement below is the instance at crow_key.
     ================================================================== *)
  Lemma idx_entries_filter_bneq :
    forall (bk : value -> value) (l : list value) (av : value),
      NoDup (List.map (row_key key) l) ->
      UniqueDictIndexImpl.idx_entries key
        (filter (fun r => negb (value_eqb (bk r) av)) l)
      = fold_left pk_del (filter (fun r => value_eqb (bk r) av) l)
          (UniqueDictIndexImpl.idx_entries key l).
  Proof.
    intros bk l; induction l as [ | r l IH ]; intros av H_nd; [ reflexivity | ].
    cbn [List.map] in H_nd; inversion H_nd as [ | ? ? H_ni H_nd' ]; subst.
    cbn [filter].
    destruct (value_eqb (bk r) av) eqn:E_av; cbn [negb].
    - (* r is leaving: its own entry goes, and it was the only one at its key *)
      rewrite IH by assumption.
      rewrite fold_pk_del_cons.
      rewrite UniqueDictIndexImpl.idx_entries_cons.
      rewrite dict_delete_insert_same
        by apply UniqueDictIndexImpl.idx_entries_SSorted.
      rewrite UniqueDictIndexImpl.dict_delete_idx_entries_absent by assumption.
      reflexivity.
    - (* r stays: its entry has to survive every delete the fold makes *)
      rewrite UniqueDictIndexImpl.idx_entries_cons, IH by assumption.
      rewrite UniqueDictIndexImpl.idx_entries_cons.
      rewrite fold_pk_del_insert;
        [ reflexivity
        | apply UniqueDictIndexImpl.idx_entries_SSorted
        | ].
      intro H_in; apply H_ni.
      apply in_map_iff in H_in as [ r' [ E_k H_in' ] ].
      apply filter_In in H_in' as [ H_in' _ ].
      rewrite <- E_k. apply in_map; exact H_in'.
  Qed.

  (* the instance this file's own rule uses *)
  Lemma idx_entries_filter_cneq : forall (l : list value) (av : value),
      NoDup (List.map (row_key key) l) ->
      UniqueDictIndexImpl.idx_entries key
        (filter (fun r => negb (value_eqb (crow_key attrs r) av)) l)
      = fold_left pk_del (crows_at attrs av l)
          (UniqueDictIndexImpl.idx_entries key l).
  Proof. intros l av H_nd; apply idx_entries_filter_bneq; exact H_nd. Qed.

End WithAttrs.

(* A record literal mentions no variable that none of its fields mentions.
   Stated here because the guard checks the fields one by one and the
   weakening lemma wants the whole literal. *)
Lemma free_immut_in_ERecord_false :
  forall (z : string) (prs : list (string * expr)),
    forallb (fun p => negb (free_immut_in z (snd p))) prs = true ->
    free_immut_in z (ERecord prs) = false.
Proof.
  induction prs as [ | [ a e ] prs IH ]; intros H_fa; [ reflexivity | ].
  cbn [forallb] in H_fa; rewrite Bool.andb_true_iff in H_fa.
  destruct H_fa as [ H_e H_fa ].
  cbn [snd] in H_e; rewrite Bool.negb_true_iff in H_e.
  specialize (IH H_fa).
  cbn [free_immut_in existsb] in *.
  rewrite H_e, IH; reflexivity.
Qed.

(* ====================================================================
   THE RULE.
   ==================================================================== *)
Section WithRule.
  Context (hole : string).
  Context (attrs : list string).
  (* the composite member's own binders.  The rule never rebuilds that
     member -- it only probes it -- so these appear in the bridges below
     and nowhere in the emitted term. *)
  Context (tup acc x : string).
  Context (H_NoDup : is_NoDup_opaque [tup; acc; x]).
  (* the primary-key member: the attribute it is keyed on and the two
     binders its own fold uses, which the rule both matches and emits *)
  Context (key utup uacc : string).
  Context (H_utup_uacc : utup <> uacc).
  Context (id_tag aux_tag : string).
  Context (idx_tag pk_tag : string).
  (* the binder the probed bucket is bound to *)
  Context (bkt : string).
  Context (H_uacc_bkt : uacc <> bkt).

  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.

  Section WithMap.
    Notation value := (value).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Notation cidx := (CDI.composite_dict_idx hole attrs tup acc x).
    Notation uidx := (unique_dict_idx hole key utup uacc).

    Notation idx_aux_wf_at :=
      (aux_wf_for_idx id_tag aux_tag idx_tag
         (CDI.idx_wf hole attrs tup acc x (locals := locals))).
    Notation unique_aux_wf_at :=
      (aux_wf_for_idx id_tag aux_tag pk_tag
         (idx_wf_unique hole key utup uacc (locals := locals))).

    Section WithTable.
      Context (tbl : string).

      (* the composite member, read in place -- the rule probes it and does
         not rebuild it *)
      Notation cmem_e := (EAccess (EAccess (ELoc tbl) aux_tag) idx_tag).

      (* uto_idx_at spelled out, so the rule can match the primary-key
         member's own recomputation. *)
      Notation euidx utup0 utup1 utup2 uacc0 uacc1 key0 d :=
        (EFold d (EAtom (AEmptyDict Unranged None)) utup0 uacc0
           (ETernop OInsert (EVar uacc1) (EAccess (EVar utup1) key0) (EVar utup2))).

      (* THE EMITTED FOLD.  The bucket is a bag and a fold wants a list, so
         ESort LikeBag coerces it -- sound because the deletes commute
         (fold_pk_del_Permutation). *)
      Definition pk_bucket_delete_body : expr :=
        EFold (ESort LikeBag (EVar bkt)) (EVar uacc) utup uacc
          (EBinop ODelete (EVar uacc) (EAccess (EVar utup) key)).

      Definition cfilter_neq_to_bucket_delete_head (e : expr) : expr :=
        match e with
        | euidx utup0 utup1 utup2 uacc0 uacc1 key0
            (flatmap_filter_list (EAccess (ELoc tbl0) id_tag0) y
               (EUnop ONot pr) y1 _ _) =>
            match CDI.conj_eq_pairs y pr with
            | Some prs =>
                if (all_eqb [(utup, [utup0; utup1; utup2]);
                             (uacc, [uacc0; uacc1]); (key, [key0]);
                             (tbl, [tbl0]); (id_tag, [id_tag0]); (y, [y1])]
                    && forallb (fun a => inb String.eqb a (List.map fst prs))
                         attrs
                    && Nat.eqb (List.length attrs) (List.length prs)
                    && negb (Nat.eqb (List.length attrs) 0)
                    (* at arity one on the declared key itself the
                       primary-key member's OWN delete rule fires, with one
                       ODelete and no probe, so the two would race *)
                    && negb (CKD.attrs_is_key attrs key)
                    (* the probed key moves under the ELet's binder *)
                    && forallb (fun p => negb (free_immut_in uacc (snd p))) prs)%bool
                then ELet (uto_idx_at key utup uacc (EAccess (ELoc tbl) id_tag))
                       uacc
                       (EOptMatch (EBinop OLookup cmem_e (ERecord prs))
                          (EVar uacc) bkt pk_bucket_delete_body)
                else e
            | None => e
            end
        | _ => e
        end.
      (* The emitted fold, typed on its own: the bucket is a bag of rows,
         the accumulator is the primary-key dictionary, and each step takes
         one key out of it. *)
      Lemma pk_bucket_delete_body_ty :
        forall (Gstore Genv : tenv) rt kt,
          access_record rt key = Success kt ->
          map.get Genv bkt = Some (TBag (TRecord rt)) ->
          map.get Genv uacc = Some (TDict Unranged kt (TRecord rt)) ->
          type_of Gstore Genv pk_bucket_delete_body
            (TDict Unranged kt (TRecord rt)).
      Proof.
        intros Gstore Genv rt kt E_key E_bkt E_uacc.
        unfold pk_bucket_delete_body.
        eapply TyEFold.
        1:{ apply TyESort_Bag. apply TyEVar; exact E_bkt. }
        1:{ apply TyEVar; exact E_uacc. }
        eapply TyEBinop; [ apply TyODelete | | ].
        1:{ apply TyEVar; apply map.get_put_same. }
        1:{ eapply TyEAccess; [ apply TyEVar | exact E_key ].
            rewrite map.get_put_diff by congruence.
            apply map.get_put_same. }
      Qed.

      Lemma cfilter_neq_to_bucket_delete_head_preserve_ty :
        forall tl ctl t (Gstore : tenv),
          type_wf t ->
          @IndexInterface.is_tbl_ty cidx t = true ->
          @IndexInterface.is_tbl_ty uidx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl idx_tag = Success (@IndexInterface.idx_ty cidx t) ->
          preserve_ty Gstore cfilter_neq_to_bucket_delete_head.
      Proof.
        unfold preserve_ty.
        intros tl ctl t Gstore H_twf H_isd H_isu E_tbl E_id E_aux E_idx.
        apply CKD.composite_is_tbl_ty_inv in H_isd as [ rt [ E_t H_is ] ]. subst t.
        apply unique_is_tbl_ty_inv in H_isu as [ rt' [ kt [ E_t' E_key ] ] ].
        injection E_t' as E_t'; subst rt'.
        cbn [IndexInterface.idx_ty CDI.composite_dict_idx CDI.idx_ty] in E_idx.
        assert (H_rtwf : type_wf (TRecord rt)) by (inversion H_twf; assumption).
        pose proof (CDI.is_tbl_ty_attrs attrs _ H_is) as [ _ H_ndattrs ].
        intros e t' Genv H_Gs H_Ge H_t.
        unfold cfilter_neq_to_bucket_delete_head.
        repeat (case_match; auto; []).
        (* the guard *)
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *.
        repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
        rewrite !Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        (* the source's typing, down to the row type *)
        invert_type_of_clear.
        lazymatch goal with
          H : type_of _ _ (EFlatmap _ _ _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EAccess (ELoc _) _) _ |- _ =>
            inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (ELoc _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : map.get Gstore tbl = Some _ |- _ =>
            rewrite E_tbl in H; injection H as H; subst
        end.
        lazymatch goal with
          H : access_record _ id_tag = Success _ |- _ =>
            rewrite E_id in H; injection H as H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EIf _ _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EBinop OCons _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_binop OCons _ _ _ |- _ => inversion H; clear H; subst
        end.
        (* the filter's INPUT row type is its OUTPUT row type *)
        lazymatch goal with
          H : type_of _ (map.put _ ?yy _) (EVar ?yy) _ |- _ =>
            apply EVar_ty_inv in H; rewrite map.get_put_same in H;
            injection H as H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EUnop ONot _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_unop ONot _ _ |- _ => inversion H; clear H; subst
        end.
        (* the accumulator's type, from the fold's initial value and body *)
        lazymatch goal with
          H : type_of _ _ (EAtom (AEmptyDict _ _)) _ |- _ =>
            pose proof H as H_init; inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_atom (AEmptyDict _ _) _ |- _ => inversion H; clear H; subst
        end.
        (* a COPY of the fold's body, which the emitted rebuild reuses whole *)
        lazymatch goal with
          H : type_of _ (map.put (map.put _ _ _) _ _) (ETernop OInsert _ _ _) _
          |- _ => pose proof H as H_body; inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_ternop OInsert _ _ _ _ |- _ => inversion H; clear H; subst
        end.
        (* the inserted key is the row's own declared key, so the dictionary's
           key type is the one is_tbl_ty named *)
        lazymatch goal with
          H : type_of _ _ (EAccess (EVar _) key) _ |- _ =>
            inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EVar _) (TRecord _) |- _ =>
            apply EVar_ty_inv in H;
            rewrite map.get_put_diff in H by congruence;
            rewrite map.get_put_same in H; injection H as H; subst
        end.
        lazymatch goal with
          H : access_record _ key = Success _ |- _ =>
            rewrite E_key in H; injection H as H; subst
        end.
        (* the dictionary's VALUE type, from the row the fold inserts *)
        lazymatch goal with
          H : type_of _ _ (EVar utup) _ |- _ =>
            apply EVar_ty_inv in H;
            rewrite map.get_put_diff in H by congruence;
            rewrite map.get_put_same in H; injection H as H; subst
        end.
        (* the collected conjuncts are a permutation of the key's attributes,
           which is what makes the probe's record literal a key *)
        lazymatch goal with
          H1 : forallb (fun a => inb String.eqb a (List.map fst _)) _ = true,
          H2 : Nat.eqb (List.length attrs) (List.length _) = true |- _ =>
            pose proof (CDI.guard_Permutation attrs _ H_ndattrs H1 H2) as H_perm
        end.
        (* the emitted form *)
        eapply TyELet.
        1:{ eapply TyEFold;
            [ eapply TyEAccess; [ apply TyELoc; exact E_tbl | exact E_id ]
            | exact H_init | exact H_body ]. }
        eapply TyEOptMatch.
        1:{ eapply TyEBinop; [ apply TyOLookup | | ].
            1:{ eapply TyEAccess;
                [ eapply TyEAccess; [ apply TyELoc; exact E_tbl | exact E_aux ]
                | exact E_idx ]. }
            1:{ (* the probed key, lifted out of the ELet's binder *)
                apply not_free_immut_put_ty2.
                1:{ lazymatch goal with
                      H : forallb (fun p => negb (free_immut_in _ (snd p))) _
                          = true |- _ =>
                        apply (free_immut_in_ERecord_false _ _ H)
                    end. }
                lazymatch goal with
                  H : type_of ?Gs (map.put ?Ge ?yy (TRecord ?rt0)) ?pr TBool |- _ =>
                    pose proof (CDI.conj_eq_pairs_ty Gs Ge yy pr rt0 TBool H)
                      as H_prs
                end.
                lazymatch goal with
                  H : CDI.conj_eq_pairs _ _ = Some _ |- _ =>
                    rewrite H in H_prs; cbv beta iota in H_prs
                end.
                apply CDI.composite_key_expr_ty;
                  [ assumption | exact H_perm
                  | apply CDI.Forall2_of_pairs_ty; assumption ]. } }
        1:{ apply TyEVar; apply map.get_put_same. }
        1:{ eapply pk_bucket_delete_body_ty.
            1: exact E_key.
            1: apply map.get_put_same.
            1:{ rewrite map.get_put_diff by congruence.
                apply map.get_put_same. } }
      Qed.

      (* ================================================================
         THE RULE COMPUTES WHAT THE SOURCE COMPUTES.

         The source rebuilds the primary-key map from the surviving rows.
         The emitted form rebuilds it from the WHOLE table and then takes
         out one key per row in the composite member's bucket at the
         deleted key.  The two agree by idx_entries_filter_cneq, and the
         bag-to-list coercion in between is invisible because the deletes
         commute.
         ================================================================ *)

      (* The emitted fold, run.  Each step is one ODelete on the
         accumulator at the row's own key, so the whole fold is the
         Gallina fold the content lemma speaks about. *)
      Lemma interp_delete_fold :
        forall (store env : locals) (rs : list value)
               (d : list (value * value)),
          Forall (fun r => exists rc, r = VRecord rc) rs ->
          fold_right
            (fun v a => interp_expr store (map.put (map.put env utup v) uacc a)
                          (EBinop ODelete (EVar uacc) (EAccess (EVar utup) key)))
            (VDict d) rs
          = VDict (fold_right (fun r a => dict_delete (row_key key r) a) d rs).
      Proof.
        intros store env rs d H_rec.
        induction H_rec as [ | r rs [ rc E_r ] H_rs IH ]; [ reflexivity | ].
        cbn [fold_right]; rewrite IH.
        rewrite interp_EBinop, !interp_EVar.
        unfold get_local; rewrite map.get_put_same.
        rewrite interp_EAccess, interp_EVar.
        unfold get_local; rewrite map.get_put_diff by congruence.
        rewrite map.get_put_same, E_r; cbv beta iota.
        reflexivity.
      Qed.

      Lemma interp_ESort_bag : forall (store env : locals) (e : expr) b,
          interp_expr store env e = VBag b ->
          interp_expr store env (ESort LikeBag e) = VList (bag_to_list b).
      Proof. intros * E; cbn [interp_expr]; rewrite E; reflexivity. Qed.

      (* The whole emitted body, run on a bucket: the stored map with one
         key deleted per row in it.  The sort is where the bag becomes a
         list, and fold_pk_del_Permutation is what makes that free. *)
      Lemma interp_pk_bucket_delete_body :
        forall (store env : locals) b (d : list (value * value)),
          Forall (fun r => exists rc, r = VRecord rc) (bag_to_list b) ->
          map.get env bkt = Some (VBag b) ->
          map.get env uacc = Some (VDict d) ->
          interp_expr store env pk_bucket_delete_body
          = VDict (fold_left (pk_del key) (bag_to_list b) d).
      Proof.
        intros store env b d H_rec E_bkt E_uacc.
        unfold pk_bucket_delete_body.
        rewrite interp_EFold.
        rewrite (interp_ESort_bag store env (EVar bkt) b)
          by (rewrite interp_EVar; unfold get_local; rewrite E_bkt; reflexivity).
        rewrite interp_EVar; unfold get_local; rewrite E_uacc.
        rewrite interp_delete_fold by exact H_rec.
        rewrite (fold_right_pk_del key); reflexivity.
      Qed.

      Lemma cfilter_neq_to_bucket_delete_head_preserve_sem :
        forall tl rt (Gstore : tenv) (store : locals),
          type_wf (TList (TRecord rt)) ->
          CDI.is_tbl_ty attrs (TList (TRecord rt)) = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          match map.get store tbl with
          | Some v =>
              type_of_value v (TRecord tl) /\ idx_aux_wf_at v /\ unique_aux_wf_at v
          | _ => False
          end ->
          preserve_sem Gstore store cfilter_neq_to_bucket_delete_head.
      Proof.
        unfold preserve_sem; intros * H_twf H_is E_tbl E_id H_store.
        intros e t Genv env H_Gs H_Ge H_t H_sw H_ew.
        destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
        destruct H_store as [ H_vty [ H_idx H_pk ] ].
        destruct (CKD.cinvariants__idx_data hole attrs tup acc x H_NoDup key
                    utup uacc H_utup_uacc id_tag aux_tag idx_tag pk_tag
                    tl rt v H_twf H_is E_id H_vty H_idx H_pk)
          as [ rv [ rv_aux [ rows [ E_vrec [ E_rows [ E_aux
             [ E_cidx [ E_pkf [ H_rows H_nd ] ] ] ] ] ] ] ] ].
        subst v.
        pose proof (typed_rows_are_records rows rt H_rows) as H_rec.
        pose proof (CDI.is_tbl_ty_attrs attrs rt H_is) as [ _ H_ndattrs ].
        unfold cfilter_neq_to_bucket_delete_head.
        repeat (case_match; auto; []).
        (* the guard *)
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *.
        repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
        rewrite !Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        lazymatch goal with
          H1 : forallb (fun a => inb String.eqb a (List.map fst _)) _ = true,
          H2 : Nat.eqb (List.length attrs) (List.length _) = true |- _ =>
            pose proof (CDI.guard_Permutation attrs _ H_ndattrs H1 H2) as H_perm
        end.
        (* the table read, which both sides start from *)
        assert (E_tr : interp_expr store env (EAccess (ELoc tbl) id_tag)
                       = VList rows).
        1:{ rewrite interp_EAccess, interp_ELoc.
            unfold get_local; rewrite E_v; cbv beta iota. exact E_rows. }
        (* THE FILTERED TABLE: what `not (conjunction)` keeps is the rows
           whose composite key differs from the probe's *)
        lazymatch goal with
          H : CDI.conj_eq_pairs ?y0 ?pr0 = Some ?prs0 |- _ =>
            assert (E_flt :
              interp_expr store env
                (flatmap_filter_list (EAccess (ELoc tbl) id_tag) y0
                   (EUnop ONot pr0) y0 None None)
              = VList (filter (fun r => negb (value_eqb (CKD.crow_key attrs r)
                                                (interp_expr store env
                                                   (ERecord prs0)))) rows))
        end.
        1:{ rewrite interp_flatmap_filter_list, E_tr. f_equal.
            lazymatch goal with
              H : CDI.conj_eq_pairs ?y0 ?pr0 = Some ?prs0 |- _ =>
                rewrite (CDI.filter_not_conj_eq_filter_neq_ckey attrs store env
                           y0 pr0 prs0 rows H_ndattrs H H_perm H_rec)
            end.
            reflexivity. }
        (* THE SOURCE *)
        lazymatch goal with
        | |- _ = interp_expr store env ?src =>
            assert (E_src : interp_expr store env src
                            = VDict (UniqueDictIndexImpl.idx_entries key
                                       (filter (fun r =>
                                          negb (value_eqb (CKD.crow_key attrs r)
                                            (interp_expr store env
                                               (ERecord _)))) rows)))
              by exact (interp_uto_idx_at key utup uacc H_utup_uacc
                          (locals_ok := locals_ok) store env _ _ E_flt)
        end.
        rewrite E_src, (idx_entries_filter_cneq attrs key rows _ H_nd).
        (* THE EMITTED FORM *)
        rewrite interp_ELet_step.
        rewrite (interp_uto_idx_at key utup uacc H_utup_uacc
                   (locals_ok := locals_ok) store env _ _ E_tr).
        rewrite interp_EOptMatch, interp_EBinop.
        rewrite (interp_tbl_field aux_tag tbl store _ rv rv_aux idx_tag _
                   E_v E_aux E_cidx).
        rewrite <- (not_free_immut_put_sem (ERecord _) uacc store env)
          by (lazymatch goal with
                H : forallb (fun p => negb (free_immut_in _ (snd p))) _ = true
                |- _ => apply (free_immut_in_ERecord_false _ _ H)
              end).
        cbn [interp_binop].
        rewrite (CKD.cidx_of_lookup attrs rows _ H_rec).
        destruct (CKD.crows_at attrs (interp_expr store env (ERecord _)) rows)
          as [ | r0 rs0 ] eqn:E_bk.
        1:{ (* no row at that key: the map is the stored one, unchanged *)
            rewrite interp_EVar; unfold get_local; rewrite map.get_put_same.
            reflexivity. }
        1:{ (* the bucket holds exactly the leaving rows *)
            assert (H_rec_bk : Forall (fun r => exists rc, r = VRecord rc)
                                 (r0 :: rs0)).
            1:{ rewrite <- E_bk.
                apply Forall_forall; intros r' H_in.
                unfold CKD.crows_at in H_in; apply filter_In in H_in as [ H_in _ ].
                rewrite Forall_forall in H_rec; apply H_rec; exact H_in. }
            lazymatch goal with
            | |- interp_expr store ?E _ = _ =>
                rewrite (interp_pk_bucket_delete_body store E
                           (list_to_bag (r0 :: rs0))
                           (UniqueDictIndexImpl.idx_entries key rows))
            end.
            1:{ f_equal.
                apply (fold_pk_del_Permutation key),
                  list_to_bag_to_list_Permutation. }
            1:{ apply Forall_forall; intros r' H_in.
                apply (Permutation_in _
                         (list_to_bag_to_list_Permutation (r0 :: rs0))) in H_in.
                rewrite Forall_forall in H_rec_bk; apply H_rec_bk; exact H_in. }
            1: apply map.get_put_same.
            1:{ rewrite map.get_put_diff by congruence.
                apply map.get_put_same. } }
      Qed.

    End WithTable.

    (* =================================================================
       What a pipeline has to supply.

       THE BRIDGES ARE CompositeDictKeyedDelete'S, UNCHANGED.  The two
       cross-member rules need exactly the same two relations, which is
       the honest statement of their symmetry: each probes one member to
       maintain the other, so each needs the probed member to be up to
       date and the declared key to be unique.  Here the composite member
       is the one probed -- its weak relation is enough -- and the
       primary-key member's STRONG one is what NoDup is read out of.
       ================================================================= *)
    Lemma cfilter_neq_to_bucket_delete_head_sound :
      forall is_tbl_ty' aux_ty (aux_wf : value -> Prop),
        CKD.composite_keyed_delete_bridges hole attrs tup acc x key utup uacc
          id_tag aux_tag idx_tag pk_tag is_tbl_ty' aux_ty aux_wf ->
        expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf
          cfilter_neq_to_bucket_delete_head.
    Proof.
      unfold CKD.composite_keyed_delete_bridges, aux_ty_for_idx,
        expr_aug_transf_sound.
      intros * [ H_aty1 [ H_aty2 [ H_isd [ H_isu [ H_wf1 H_wf2 ] ] ] ] ] *.
      intros H_Gs H_Ge H_twf H_is' H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with
        H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl
      end.
      pose proof (H_isd _ H_is') as H_is_d.
      pose proof (H_isu _ H_is') as H_is_u.
      apply CKD.composite_is_tbl_ty_inv in H_is_d as [ rt [ E_t H_isc ] ].
      specialize (H_aty1 tbl_ty); specialize (H_aty2 tbl_ty).
      repeat destruct_match_hyp; intuition idtac.
      1:{ eapply cfilter_neq_to_bucket_delete_head_preserve_ty;
          try eassumption.
          all: try (apply H_isd; exact H_is').
          all: try (apply H_isu; exact H_is'). }
      1:{ subst tbl_ty.
          eapply cfilter_neq_to_bucket_delete_head_preserve_sem;
            try eassumption.
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
          split; [ assumption | split ].
          1:{ eapply H_wf1; [ exact H_twf | exact H_is' | | exact H_aw ].
              lazymatch goal with E : aux_ty _ = _ |- _ => rewrite E end.
              assumption. }
          1:{ eapply H_wf2; [ exact H_twf | exact H_is' | | exact H_aw ].
              lazymatch goal with E : aux_ty _ = _ |- _ => rewrite E end.
              assumption. } }
    Qed.

    Definition cfilter_neq_to_bucket_delete_transf
      : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl]
                   (cfilter_neq_to_bucket_delete_head tbl).

    Lemma cfilter_neq_to_bucket_delete_transf_sound :
      forall is_tbl_ty' aux_ty aux_wf,
        CKD.composite_keyed_delete_bridges hole attrs tup acc x key utup uacc
          id_tag aux_tag idx_tag pk_tag is_tbl_ty' aux_ty aux_wf ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf
          cfilter_neq_to_bucket_delete_transf.
    Proof.
      intros * H_br. unfold cfilter_neq_to_bucket_delete_transf.
      apply fold_command_with_globals_sound.
      apply cfilter_neq_to_bucket_delete_head_sound; exact H_br.
    Qed.

    (* ------------------------------------------------------------------
       The rule as a pipeline uses it: the identity unless the table's
       declarations name the key.

       Gated for the same reason the rule in the other direction is, and
       the reason is visible in idx_entries_filter_cneq's second branch:
       the primary-key member holds ONE row per key, so if a row that
       stays shared its key with a row that leaves, deleting that key
       would take out the survivor's entry.
       ------------------------------------------------------------------ *)
    Definition cbucket_delete_gated (ds : list decl)
      : string -> command -> command :=
      if declares_unique key ds
      then cfilter_neq_to_bucket_delete_transf
      else fun _ => id.

    Lemma cbucket_delete_gated_sound :
      forall ds is_tbl_ty' aux_ty aux_wf,
        (declares_unique key ds = true ->
         CKD.composite_keyed_delete_bridges hole attrs tup acc x key utup uacc
           id_tag aux_tag idx_tag pk_tag is_tbl_ty' aux_ty aux_wf) ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf (cbucket_delete_gated ds).
    Proof.
      intros * H_br. unfold cbucket_delete_gated.
      destruct (declares_unique key ds) eqn:E_uq.
      1: apply cfilter_neq_to_bucket_delete_transf_sound, H_br; reflexivity.
      1: unfold aug_transf_sound, id; intros; repeat split; auto.
    Qed.
  End WithMap.
End WithRule.
