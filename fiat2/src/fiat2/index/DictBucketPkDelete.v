(* ====================================================================
   Maintaining a PRIMARY-KEY member across a delete at a DICTIONARY'S OWN
   bucketing attribute.

   CompositeKeyBucketDelete at arity one, and built for the same reason: a
   delete naming the attribute the dictionary buckets on left the
   primary-key member keyed on an attribute the filter never mentions, so
   that member was REBUILT.  Measured on Ex_KeyedDictTwoDeletes before this
   rule existed, that made the operation 2051550 at a=1.22 -- 3.0x WORSE
   than the source's own filter -- and the rebuild kept the row list
   installed, which cost the keyed delete beside it its whole 66x.

   WHAT IS DIFFERENT FROM THE COMPOSITE CASE, and it is the thing to keep in
   view when reading the measurement: a composite key was unique per row, so
   a bucket held ONE row.  A dictionary bucketed on one attribute is a
   secondary index, so a bucket holds MANY rows and the delete removes all
   of them.  Any correct implementation of this operation is therefore
   Omega(bucket), and whether serving it changes an exponent or a constant
   depends on whether buckets stay bounded as the table grows.  The rule is
   the same either way; the claim it supports is not.  Ex_KeyedDictTwoDeletes
   states the generator's bucket policy for exactly this reason.

   WHAT IS SHARED, rather than repeated: the emitted body is literally
   CompositeKeyBucketDelete's (pk_bucket_delete_body), with its typing and
   its semantics, and the content lemma is that file's
   idx_entries_filter_bneq instantiated at row_key instead of crow_key.  The
   dictionary algebra behind it -- that deleting keys COMMUTES, which is what
   makes the ESort LikeBag coercion free -- lives there too.  If a third
   arity ever wants it, that algebra belongs in Utils.

   GATED on the key being declared unique, for the reason
   idx_entries_filter_bneq's second branch shows: the member holds one row
   per key, so deleting a leaving row's key would take out a survivor that
   shared it.
   ==================================================================== *)
Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.rules.CollectionTransf fiat2.rules.FlatmapTransf fiat2.rules.EraseField
  fiat2.constraint.Constraint fiat2.index.DictIndexImpl fiat2.rules.FlatmapForms
  fiat2.IndexInterface fiat2.index.UniqueDictIndexImpl fiat2.index.UniqueIndexUse
  fiat2.constraint.Decl fiat2.index.UniqueIndexGate
  fiat2.index.DictIndexKeyedDelete fiat2.index.CompositeKeyBucketDelete
  fiat2.TransfSound fiat2.TransfUtils
  fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.


Section WithRule.
  Context (hole : string).
  (* attr is the attribute this dictionary buckets on, and the one the
     delete names in full; key is the declared key the primary-key member
     is built on.  They must differ -- where they coincide the primary-key
     member's OWN delete rule fires, with one ODelete and no probe. *)
  Context (attr : string).
  Context (dk : dict_kind).
  Context (tup acc x : string).
  Context (H_NoDup : is_NoDup_opaque [tup; acc; x]).
  Context (key utup uacc : string).
  Context (H_utup_uacc : utup <> uacc).
  Context (id_tag aux_tag : string).
  Context (idx_tag pk_tag : string).
  Context (bkt : string).
  Context (H_uacc_bkt : uacc <> bkt).

  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.

  (* One line, and it duplicates CompositeDictIndexImpl's: taking that one
     would mean requiring the composite index from a rule about a
     single-attribute dictionary, and importing it would shadow
     DictIndexImpl's own idx_ty and is_tbl_ty.  It belongs in Utils, with
     the other key-agnostic inversions DictIndexImpl.v:348 notes. *)
  Lemma EVar_ty_inv : forall (Gstore Genv : tenv) y t,
      type_of Gstore Genv (EVar y) t -> map.get Genv y = Some t.
  Proof. intros * H; inversion H; assumption. Qed.

  Section WithMap.
    Notation value := (value).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Notation didx := (dict_idx hole attr dk tup acc x).
    Notation uidx := (unique_dict_idx hole key utup uacc).

    Notation idx_aux_wf_at :=
      (aux_wf_for_idx id_tag aux_tag idx_tag
         (DictIndexImpl.idx_wf hole attr dk tup acc x (locals := locals))).
    Notation unique_aux_wf_at :=
      (aux_wf_for_idx id_tag aux_tag pk_tag
         (idx_wf_unique hole key utup uacc (locals := locals))).

    Section WithTable.
      Context (tbl : string).

      (* the dictionary member, read in place -- the rule probes it and does
         not rebuild it *)
      Notation dmem_e := (EAccess (EAccess (ELoc tbl) aux_tag) idx_tag).

      (* uto_idx_at spelled out, so the rule can match the primary-key
         member's own recomputation *)
      Notation euidx utup0 utup1 utup2 uacc0 uacc1 key0 d :=
        (EFold d (EAtom (AEmptyDict Unranged None)) utup0 uacc0
           (ETernop OInsert (EVar uacc1) (EAccess (EVar utup1) key0) (EVar utup2))).

      Definition filter_neq_to_bucket_pk_delete_head (e : expr) : expr :=
        match e with
        | euidx utup0 utup1 utup2 uacc0 uacc1 key0
            (flatmap_filter_list (EAccess (ELoc tbl0) id_tag0) y
               (EUnop ONot (EBinop OEq (EAccess (EVar y1) attr0) kexp)) y2 _ _) =>
            if (all_eqb [(utup, [utup0; utup1; utup2]);
                         (uacc, [uacc0; uacc1]); (key, [key0]); (attr, [attr0]);
                         (tbl, [tbl0]); (id_tag, [id_tag0]); (y, [y1; y2])]
                && negb (String.eqb attr key)
                && negb (free_immut_in y kexp)
                (* the probed key moves under the ELet's binder *)
                && negb (free_immut_in uacc kexp))%bool
            then ELet (uto_idx_at key utup uacc (EAccess (ELoc tbl) id_tag))
                   uacc
                   (EOptMatch (EBinop OLookup dmem_e kexp)
                      (EVar uacc) bkt
                      (CompositeKeyBucketDelete.pk_bucket_delete_body key utup uacc bkt))
            else e
        | _ => e
        end.

      Lemma filter_neq_to_bucket_pk_delete_head_preserve_ty :
        forall tl ctl t (Gstore : tenv),
          type_wf t ->
          @IndexInterface.is_tbl_ty didx t = true ->
          @IndexInterface.is_tbl_ty uidx t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord ctl) ->
          access_record ctl idx_tag = Success (@IndexInterface.idx_ty didx t) ->
          preserve_ty Gstore filter_neq_to_bucket_pk_delete_head.
      Proof.
        unfold preserve_ty.
        intros tl ctl t Gstore H_twf H_isd H_isu E_tbl E_id E_aux E_idx.
        apply DictIndexKeyedDelete.dict_is_tbl_ty_inv in H_isd as [ rt [ kt' [ E_t H_isa ] ] ].
        subst t.
        apply DictIndexKeyedDelete.unique_is_tbl_ty_inv in H_isu as [ rt' [ kt [ E_t' E_key ] ] ].
        injection E_t' as E_t'; subst rt'.
        cbn [IndexInterface.idx_ty dict_idx DictIndexImpl.idx_ty] in E_idx.
        assert (H_rtwf : type_wf (TRecord rt)) by (inversion H_twf; assumption).
        intros e t' Genv H_Gs H_Ge H_t.
        unfold filter_neq_to_bucket_pk_delete_head.
        repeat (case_match; auto; []).
        (* the guard *)
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *.
        repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
        rewrite !Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        lazymatch goal with pe : expr |- _ => rename pe into kexp end.
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
        (* the probed key's own type, from the filter's equality *)
        lazymatch goal with
          H : type_of _ _ (EBinop OEq _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_binop OEq _ _ _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ _ (EAccess (EVar _) attr) _ |- _ =>
            inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ (map.put _ ?yy _) (EVar ?yy) (TRecord _) |- _ =>
            apply EVar_ty_inv in H; rewrite map.get_put_same in H;
            injection H as H; subst
        end.
        (* the accumulator's type, from the fold's initial value and body *)
        lazymatch goal with
          H : type_of _ _ (EAtom (AEmptyDict _ _)) _ |- _ =>
            pose proof H as H_init; inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_atom (AEmptyDict _ _) _ |- _ => inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of _ (map.put (map.put _ _ _) _ _) (ETernop OInsert _ _ _) _
          |- _ => pose proof H as H_body; inversion H; clear H; subst
        end.
        lazymatch goal with
          H : type_of_ternop OInsert _ _ _ _ |- _ => inversion H; clear H; subst
        end.
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
        (* the member's key type, spelled the way the source spells it *)
        lazymatch goal with
          H : access_record ?rt0 attr = Success ?kta |- _ =>
            assert (E_kta : get_attr_type rt0 attr = kta)
              by (unfold get_attr_type; rewrite H; reflexivity)
        end.
        rewrite E_kta in E_idx.
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
            1:{ apply not_free_immut_put_ty2; [ assumption | ].
                eapply not_free_immut_put_ty; [ | eassumption ]; assumption. } }
        1:{ apply TyEVar; apply map.get_put_same. }
        1:{ eapply CompositeKeyBucketDelete.pk_bucket_delete_body_ty.
            1: exact H_utup_uacc.
            1: exact tenv_ok.
            1: exact E_key.
            1: apply map.get_put_same.
            1:{ rewrite map.get_put_diff by congruence.
                apply map.get_put_same. } }
      Qed.

      (* ================================================================
         THE RULE COMPUTES WHAT THE SOURCE COMPUTES.

         Word for word the composite case: the source rebuilds the
         primary-key map from the surviving rows, the emitted form rebuilds
         it from the whole table and then takes out one key per row in the
         dictionary's bucket at the deleted attribute value.
         ================================================================ *)
      Lemma filter_neq_to_bucket_pk_delete_head_preserve_sem :
        forall tl rt (Gstore : tenv) (store : locals),
          type_wf (TList (TRecord rt)) ->
          DictIndexImpl.is_tbl_ty attr (TList (TRecord rt)) = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success (TList (TRecord rt)) ->
          match map.get store tbl with
          | Some v =>
              type_of_value v (TRecord tl) /\ idx_aux_wf_at v /\ unique_aux_wf_at v
          | _ => False
          end ->
          preserve_sem Gstore store filter_neq_to_bucket_pk_delete_head.
      Proof.
        unfold preserve_sem; intros * H_twf H_is E_tbl E_id H_store.
        intros e t Genv env H_Gs H_Ge H_t H_sw H_ew.
        destruct (map.get store tbl) as [ v | ] eqn:E_v; [ | contradiction ].
        destruct H_store as [ H_vty [ H_idx H_pk ] ].
        destruct (DictIndexKeyedDelete.invariants__idx_data hole attr dk tup acc x H_NoDup key
                    utup uacc H_utup_uacc id_tag aux_tag idx_tag pk_tag
                    tl rt v H_twf H_is E_id H_vty H_idx H_pk)
          as [ rv [ rv_aux [ rows [ E_vrec [ E_rows [ E_aux
             [ E_didx [ E_pkf [ H_rows H_nd ] ] ] ] ] ] ] ] ].
        subst v.
        pose proof (DictIndexKeyedDelete.typed_rows_are_records rows rt H_rows) as H_rec.
        unfold filter_neq_to_bucket_pk_delete_head.
        repeat (case_match; auto; []).
        (* the guard *)
        cbn [all_eqb all_eqb' andb] in *.
        repeat rewrite Bool.andb_true_iff in *.
        repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
        rewrite !Bool.negb_true_iff in *.
        repeat (rewrite eqb_eq in *; subst).
        lazymatch goal with pe : expr |- _ => rename pe into kexp end.
        (* the table read, which both sides start from *)
        assert (E_tr : interp_expr store env (EAccess (ELoc tbl) id_tag)
                       = VList rows).
        1:{ rewrite interp_EAccess, interp_ELoc.
            unfold get_local; rewrite E_v; cbv beta iota. exact E_rows. }
        (* the filtered table: what `not (row.attr == k)` keeps. *)
        lazymatch goal with
        | |- _ = interp_expr store env (EFold ?d _ _ _ _) =>
            assert (E_flt :
                     interp_expr store env d
                     = VList (filter
                                (fun r => negb (value_eqb (row_key attr r)
                                             (interp_expr store env kexp)))
                                rows))
        end.
        1:{ rewrite interp_flatmap_filter_list, E_tr. f_equal.
            rewrite FlatmapForms.filter_pred_neq by assumption.
            reflexivity. }
        (* THE SOURCE *)
        lazymatch goal with
        | |- _ = interp_expr store env ?src =>
            assert (E_src : interp_expr store env src
                            = VDict (UniqueDictIndexImpl.idx_entries key
                                       (filter (fun r =>
                                          negb (value_eqb (row_key attr r)
                                            (interp_expr store env kexp)))
                                          rows)))
              by exact (interp_uto_idx_at key utup uacc H_utup_uacc
                          (locals_ok := locals_ok) store env _ _ E_flt)
        end.
        rewrite E_src.
        rewrite (CompositeKeyBucketDelete.idx_entries_filter_bneq key (row_key attr) rows _ H_nd).
        (* THE EMITTED FORM *)
        rewrite DictIndexKeyedDelete.interp_ELet_step.
        rewrite (interp_uto_idx_at key utup uacc H_utup_uacc
                   (locals_ok := locals_ok) store env _ _ E_tr).
        rewrite interp_EOptMatch, interp_EBinop.
        rewrite (DictIndexKeyedDelete.interp_tbl_field aux_tag tbl store _ rv rv_aux idx_tag _
                   E_v E_aux E_didx).
        rewrite <- (not_free_immut_put_sem kexp uacc store env) by assumption.
        cbn [interp_binop].
        rewrite (DictIndexKeyedDelete.idx_of_lookup attr rows _ H_rec).
        destruct (DictIndexKeyedDelete.rows_at attr (interp_expr store env kexp) rows)
          as [ | r0 rs0 ] eqn:E_bk.
        (* the content lemma is stated over an arbitrary bucket key, so its
           bucket is a filter where rows_at is that filter by definition *)
        all: unfold DictIndexKeyedDelete.rows_at in E_bk; rewrite E_bk.
        1:{ (* no row at that key: the map is the stored one, unchanged *)
            rewrite interp_EVar; unfold get_local; rewrite map.get_put_same.
            reflexivity. }
        1:{ (* the bucket holds exactly the leaving rows *)
            assert (H_rec_bk : Forall (fun r => exists rc, r = VRecord rc)
                                 (r0 :: rs0)).
            1:{ rewrite <- E_bk.
                apply Forall_forall; intros r' H_in.
                apply filter_In in H_in as [ H_in _ ].
                rewrite Forall_forall in H_rec; apply H_rec; exact H_in. }
            lazymatch goal with
            | |- interp_expr store ?E _ = _ =>
                rewrite (CompositeKeyBucketDelete.interp_pk_bucket_delete_body key utup uacc
                           H_utup_uacc bkt (locals_ok := locals_ok) store E
                           (list_to_bag (r0 :: rs0))
                           (UniqueDictIndexImpl.idx_entries key rows))
            end.
            1:{ f_equal.
                apply (CompositeKeyBucketDelete.fold_pk_del_Permutation key),
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
       What a pipeline has to supply: DictIndexKeyedDelete's bridges,
       unchanged, for the same reason CompositeKeyBucketDelete reuses
       CompositeDictKeyedDelete's.  The two rules of a pair each probe one
       member to maintain the other, so each needs the probed member's weak
       relation and the declared key's strong one.
       ================================================================= *)
    Lemma filter_neq_to_bucket_pk_delete_head_sound :
      forall is_tbl_ty' aux_ty (aux_wf : value -> Prop),
        DictIndexKeyedDelete.dict_keyed_delete_bridges hole attr dk tup acc x key utup uacc
          id_tag aux_tag idx_tag pk_tag is_tbl_ty' aux_ty aux_wf ->
        expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf
          filter_neq_to_bucket_pk_delete_head.
    Proof.
      unfold DictIndexKeyedDelete.dict_keyed_delete_bridges, aux_ty_for_idx,
        expr_aug_transf_sound.
      intros * [ H_aty1 [ H_aty2 [ H_isd [ H_isu [ H_wf1 H_wf2 ] ] ] ] ] *.
      intros H_Gs H_Ge H_twf H_is' H_glob H_t.
      unfold tenv_wf_with_globals in H_glob; invert_Forall2.
      lazymatch goal with
        H : map.get Gstore tbl = Some _ |- _ => rename H into E_tbl
      end.
      pose proof (H_isd _ H_is') as H_is_d.
      pose proof (H_isd _ H_is') as H_is_dict.
      pose proof (H_isu _ H_is') as H_is_u.
      apply DictIndexKeyedDelete.dict_is_tbl_ty_inv in H_is_d as [ rt [ kt' [ E_t H_isa ] ] ].
      specialize (H_aty1 tbl_ty); specialize (H_aty2 tbl_ty).
      repeat destruct_match_hyp; intuition idtac.
      1:{ eapply filter_neq_to_bucket_pk_delete_head_preserve_ty;
          try eassumption.
          all: try (apply H_isd; exact H_is').
          all: try (apply H_isu; exact H_is'). }
      1:{ subst tbl_ty.
          eapply filter_neq_to_bucket_pk_delete_head_preserve_sem;
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

    Definition filter_neq_to_bucket_pk_delete_transf
      : string -> command -> command :=
      fun tbl => fold_command_with_globals [tbl]
                   (filter_neq_to_bucket_pk_delete_head tbl).

    Lemma filter_neq_to_bucket_pk_delete_transf_sound :
      forall is_tbl_ty' aux_ty aux_wf,
        DictIndexKeyedDelete.dict_keyed_delete_bridges hole attr dk tup acc x key utup uacc
          id_tag aux_tag idx_tag pk_tag is_tbl_ty' aux_ty aux_wf ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf
          filter_neq_to_bucket_pk_delete_transf.
    Proof.
      intros * H_br. unfold filter_neq_to_bucket_pk_delete_transf.
      apply fold_command_with_globals_sound.
      apply filter_neq_to_bucket_pk_delete_head_sound; exact H_br.
    Qed.

    Definition bucket_pk_delete_gated (ds : list decl)
      : string -> command -> command :=
      if declares_unique key ds
      then filter_neq_to_bucket_pk_delete_transf
      else fun _ => id.

    Lemma bucket_pk_delete_gated_sound :
      forall ds is_tbl_ty' aux_ty aux_wf,
        (declares_unique key ds = true ->
         DictIndexKeyedDelete.dict_keyed_delete_bridges hole attr dk tup acc x key utup uacc
           id_tag aux_tag idx_tag pk_tag is_tbl_ty' aux_ty aux_wf) ->
        aug_transf_sound is_tbl_ty' aux_ty aux_wf (bucket_pk_delete_gated ds).
    Proof.
      intros * H_br. unfold bucket_pk_delete_gated.
      destruct (declares_unique key ds) eqn:E_uq.
      1: apply filter_neq_to_bucket_pk_delete_transf_sound, H_br; reflexivity.
      1: unfold aug_transf_sound, id; intros; repeat split; auto.
    Qed.
  End WithMap.
End WithRule.
