Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.Utils fiat2.TransfSound fiat2.TransfUtils fiat2.Substitute fiat2.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.

(* The table itself, at a weaker collection level.

   Every other index here answers a question about the table -- a sum, a
   minimum, a key lookup.  This one answers none: it stores the same rows, as a
   bag or a set.  What makes it worth installing is where the collection
   push-down stops.

   push_down_collection drives EBagOf and ESetOf inward through a query, and
   where it reaches a read of the table it can go no further, so it leaves the
   coercion sitting on that read (CollectionTransf.bag_of, set_of).  That
   residue is a demand: the query wants the table as a bag or a set, and
   materializes every row to get one, each time it runs.  An index whose to_idx
   IS that coercion turns the residue into a field read.

   Maintenance needs no rule of its own, for the same reason.  A write stores
   to_idx of the new table, so the installation leaves EBagOf (row :: tbl) or
   ESetOf (filter p tbl) behind -- exactly the shapes push_down_collection
   rewrites, into an insert or a filter at the weaker level, over the coercion
   of the OLD table, which the rule below then reads off the record.  So this
   index is one use rule plus a basic transformation the pipeline already runs.

   tag is an explicit argument rather than a section variable: the proofs case
   split on it, and a section variable cannot be eliminated, since unfolding a
   definition of the section reintroduces it.

   LikeList is the identity index -- no coercion, so the rule never fires and
   the member is a second copy of the table.  It is here to keep the
   definitions total over collection_tag, not because there is a reason to ask
   for it. *)
Section WithHole.
  Context (hole : string).

  Definition to_idx (tag : collection_tag) : expr :=
    match tag with
    | LikeSet => ESetOf (EVar hole)
    | LikeBag => EBagOf (EVar hole)
    | LikeList => EVar hole
    end.

  Definition is_tbl_ty (t : type) : bool :=
    match t with
    | TList _ => true
    | _ => false
    end.

  Definition idx_ty (tag : collection_tag) (t : type) : type :=
    match t with
    | TList t' => match tag with
                  | LikeSet => TSet t'
                  | LikeBag => TBag t'
                  | LikeList => TList t'
                  end
    | _ => t
    end.

  Lemma idx_ty_wf : forall tag t,
      type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty tag t).
  Proof.
    unfold is_tbl_ty, idx_ty; intros * H_wf H_tbl.
    destruct t; try discriminate.
    inversion H_wf; subst.
    destruct tag; constructor; assumption.
  Qed.

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (width:=width)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Definition idx_wf (tag : collection_tag) (tbl_v idx_v : value) : Prop :=
      idx_v = interp_expr map.empty (map.put map.empty hole tbl_v) (to_idx tag).

    Lemma to_idx_ty : forall tag (t : type),
        type_wf t -> is_tbl_ty t = true ->
        type_of map.empty (map.put map.empty hole t) (to_idx tag) (idx_ty tag t).
    Proof.
      unfold is_tbl_ty, to_idx, idx_ty; intros * H_wf H_tbl.
      destruct t; try discriminate.
      destruct tag; repeat econstructor; rewrite_map_get_put_goal; reflexivity.
    Qed.

    Lemma to_idx_wf : forall tag (v : value) (t : type),
        type_wf t -> is_tbl_ty t = true ->
        type_of_value v t ->
        idx_wf tag v (interp_expr map.empty (map.put map.empty hole v) (to_idx tag)).
    Proof.
      unfold idx_wf; intros; auto.
    Qed.

    Instance rep_idx (tag : collection_tag) : IndexInterface.index :=
      IndexInterface.mk hole (to_idx tag) (idx_ty tag) is_tbl_ty.

    Instance rep_idx_ok (tag : collection_tag) :
      IndexInterface.ok (rep_idx tag) (idx_wf tag) :=
      IndexInterface.Build_ok (rep_idx tag) (idx_wf tag)
        (idx_ty_wf tag) (to_idx_ty tag) (to_idx_wf tag).

    Section WithTags.
      Context (id_tag aux_tag idx_tag : string).

      Section rep_to_lookup.
        Context (tbl : string).

      (* The whole rule: the coercion the push-down left on the table's read is
         the member the installation stored. *)
      Definition rep_to_lookup_head (tag : collection_tag) (e : expr) : expr :=
        match tag, e with
        | LikeSet, ESetOf (EAccess (ELoc tbl0) id_tag0) =>
            if (String.eqb tbl tbl0 && String.eqb id_tag id_tag0)%bool
            then EAccess (EAccess (ELoc tbl) aux_tag) idx_tag
            else e
        | LikeBag, EBagOf (EAccess (ELoc tbl0) id_tag0) =>
            if (String.eqb tbl tbl0 && String.eqb id_tag id_tag0)%bool
            then EAccess (EAccess (ELoc tbl) aux_tag) idx_tag
            else e
        | _, _ => e
        end.

      Lemma rep_to_lookup_head_preserve_ty : forall tag tl t aux_tl (Gstore : tenv),
          type_wf t -> is_tbl_ty t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord aux_tl) ->
          access_record aux_tl idx_tag = Success (idx_ty tag t) ->
          preserve_ty Gstore (rep_to_lookup_head tag).
      Proof.
        unfold preserve_ty, is_tbl_ty, idx_ty, rep_to_lookup_head; intros.
        destruct t; try discriminate.
        destruct tag; repeat destruct_subexpr; auto.
        all: repeat case_match; auto.
        all: rewrite Bool.andb_true_iff in *; intuition idtac;
             rewrite eqb_eq in *; subst;
             repeat invert_type_of_clear;
             repeat rewrite_map_get_put_hyp;
             repeat (clear_refl; repeat do_injection2);
             repeat (rewrite_l_to_r; do_injection2);
             repeat (econstructor; eauto).
      Qed.

      Lemma rep_to_lookup_head_preserve_sem :
        forall tag (Gstore : tenv) (store : locals) tl t aux_tl,
          type_wf t -> is_tbl_ty t = true ->
          map.get Gstore tbl = Some (TRecord tl) ->
          access_record tl id_tag = Success t ->
          access_record tl aux_tag = Success (TRecord aux_tl) ->
          access_record aux_tl idx_tag = Success (idx_ty tag t) ->
          match map.get store tbl with
          | Some v => aux_wf_for_idx id_tag aux_tag idx_tag (idx_wf tag) v
          | _ => False
          end ->
          preserve_sem Gstore store (rep_to_lookup_head tag).
      Proof.
        unfold preserve_sem, aux_wf_for_idx, idx_wf, to_idx, rep_to_lookup_head;
          intros * H_wf H_tbl H_G H_id H_aux H_idx H_at *; intros.
        destruct tag; repeat destruct_subexpr; auto.
        all: repeat (case_match; auto; []).
        all: rewrite Bool.andb_true_iff in *; intuition idtac;
             rewrite eqb_eq in *; subst.
        (* read the member off the stored record.  No typing is needed: the
           relation already says what the member holds. *)
        all: repeat lazymatch type of H_at with
               | match ?y with _ => _ end => destruct y eqn:?; try contradiction
               end;
             cbn [interp_expr] in H_at |- *;
             unfold get_local, record_proj in *;
             rewrite map.get_put_same in H_at;
             repeat rewrite_l_to_r;
             congruence.
      Qed.

      End rep_to_lookup.

      Ltac invert_tenv_wf_with_globals :=
        lazymatch goal with H: tenv_wf_with_globals _ _ _ |- _ => inversion H; subst end.

      Lemma rep_to_lookup_head_sound : forall tag is_tbl_ty' aux_ty aux_wf,
          aux_ty_for_idx id_tag aux_tag idx_tag (idx_ty tag) aux_ty ->
          (forall t, is_tbl_ty' t = true -> is_tbl_ty t = true) ->
          (forall (v : value),
              aux_wf v -> aux_wf_for_idx id_tag aux_tag idx_tag (idx_wf tag) v) ->
          expr_aug_transf_sound is_tbl_ty' aux_ty aux_wf
            (fun tbl => rep_to_lookup_head tbl tag).
      Proof.
        unfold aux_ty_for_idx, expr_aug_transf_sound; intros.
        invert_tenv_wf_with_globals.
        specialize (H tbl_ty). repeat destruct_match_hyp; intuition idtac.
        1: eapply rep_to_lookup_head_preserve_ty; eauto.
        1: eapply rep_to_lookup_head_preserve_sem; eauto.
        lazymatch goal with
          H: locals_wf ?G ?str, H': map.get ?G _ = _ |- _ =>
            apply H in H'
        end.
        destruct_match_hyp; intuition idtac.
        lazymatch goal with
          H: holds_for_all_entries _ ?str, H': map.get ?str _ = _ |- _ =>
            apply H in H'
        end.
        unfold value_wf_with_globals in *. invert_Forall; intuition auto.
      Qed.
    End WithTags.
  End WithMap.
End WithHole.

#[export] Hint Resolve rep_to_lookup_head_sound : transf_hints.

#[export] Hint Extern 5 (type_of _ _ IndexInterface.to_idx _) => apply RepIdx.to_idx_ty : transf_hints.
