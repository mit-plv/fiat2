Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface
  fiat2.CollectionTransf fiat2.DictIndexImpl fiat2.SumAgg fiat2.MinAgg fiat2.BitmapIndex fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf fiat2.TransfSound fiat2.Utils fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.
Import ListNotations.

Variant basic_transf :=
  | ToJoin
  | ToFilter
  | FilterPushdown
  | AnnotateCollection
  | PushdownCollection.

Variant index_choice :=
  | SumAgg (attr : string)
  | MinAgg (attr : string)
  | DictIdx (attr : string)
  | BitmapIdx (attr : string) (attr_v : string).

Variant anno_command :=
  | AC (basic_transfs : list basic_transf) (all_index_choices : list (list index_choice)) (c : command).


Section WithConcreteMaps.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Section CommonPipelineParts.
    Context (sum_agg_attr : string).
    Context (tag tag' : string).

    Definition sum_agg_wf := (SumAgg.idx_wf (locals:=clocals) "hole" sum_agg_attr "x").
    Instance csum_agg : IndexInterface.index := (sum_agg "hole" sum_agg_attr "x").
    Instance csum_agg_ok : IndexInterface.ok csum_agg sum_agg_wf.
    apply sum_agg_ok.
    Qed.

    Definition sum_agg_lookup_transf := fun tbl => fold_command_with_globals [tbl] (sum_to_agg_lookup_head sum_agg_attr "id_tag" "aux_tag" tag tbl).
    Definition cons_to_add_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_add_head).

    Context (min_agg_attr : string).

    Definition min_agg_wf := (MinAgg.idx_wf (locals:=clocals) "hole" min_agg_attr "x").
    Instance cmin_agg : IndexInterface.index := (min_agg "hole" min_agg_attr "x").
    Instance cmin_agg_ok : IndexInterface.ok cmin_agg min_agg_wf.
    apply min_agg_ok.
    Qed.

    Definition min_agg_lookup_transf := fun tbl => fold_command_with_globals [tbl] (min_to_agg_lookup_head min_agg_attr "id_tag" "aux_tag" tag tbl).
    Definition cons_to_min_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_min_head "y").

    Context (dict_idx_attr : string).

    Definition dict_idx_wf := (DictIndexImpl.idx_wf (width:=width) "hole" dict_idx_attr "tup" "acc" "x").
    Instance cdict_idx : IndexInterface.index := (dict_idx "hole" dict_idx_attr "tup" "acc" "x").
    Instance cdict_idx_ok : IndexInterface.ok cdict_idx dict_idx_wf.
    apply dict_idx_ok. auto with transf_hints.
    Qed.

    Definition dict_lookup_transf := fun tbl => fold_command_with_globals [tbl] (eq_filter_to_lookup_head dict_idx_attr "id_tag" "aux_tag" tag "b" tbl).
    Definition cons_to_insert_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_insert_head dict_idx_attr "tup" "acc" "x" "y").
    Definition use_dict_idx_transf := fun tbl => fold_command_with_globals [tbl] (use_idx_head dict_idx_attr "id_tag" "aux_tag" tag tbl).

    Definition pk_idx_wf := (BitmapIndex.pk_idx_wf (width:=width) "hole" "tup" "acc").
    Instance cpk_idx : IndexInterface.index := (pk_idx "hole" "tup" "acc").
    Instance cpk_idx_ok : IndexInterface.ok cpk_idx pk_idx_wf.
    apply pk_idx_ok. auto with transf_hints.
    Qed.

    Context (bitmap_attr : string).
    Context (bitmap_str : string).
    Definition bitmap_wf := (bitmap_wf (width:=width) bitmap_attr bitmap_str "hole" "tup").
    Instance bitmap : IndexInterface.index := (bitmap bitmap_attr bitmap_str "hole" "tup").
    Instance bitmap_ok : IndexInterface.ok bitmap bitmap_wf.
    apply bitmap_ok.
    Qed.

    Definition cons_to_pk_idx_update_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_pk_idx_update_head "y").
    Definition use_pk_idx_transf := fun tbl => fold_command_with_globals [tbl] (use_pk_idx_head "id_tag" "aux_tag" tag tbl).
    Definition cons_to_bitmap_update_transf := fun tbl => fold_command_with_globals [tbl] cons_to_bitmap_update_head.
    Definition use_bitmap_transf := fun tbl => fold_command_with_globals [tbl] (use_bitmap_head bitmap_attr bitmap_str "id_tag" "aux_tag" tag tbl).
    Definition filter_to_bitmap_lookup_transf :=
      fun tbl => fold_command_with_globals [tbl]
                   (filter_to_bitmap_lookup_head bitmap_attr bitmap_str "id_tag" "aux_tag" tag tag' "x" "b" "acc" tbl).
  End CommonPipelineParts.

  Definition mk_idx (cur_tag : nat) (reps : nat) (ic : index_choice) :
    list (string * IndexInterface.index * (value -> value -> Prop)) * list (string -> command -> command) * nat :=
    match ic with
    | SumAgg attr =>
        let sum_tag := String.of_nat cur_tag in
        ([(sum_tag, csum_agg attr, sum_agg_wf attr)],
          [sum_agg_lookup_transf sum_tag attr;
           fun tbl => repeat_transf (cons_to_add_transf tbl) reps],
          S cur_tag)
    | MinAgg attr =>
        let min_tag := String.of_nat cur_tag in
        ([(min_tag, cmin_agg attr, min_agg_wf attr)],
                       [min_agg_lookup_transf min_tag attr;
                        fun tbl => repeat_transf (cons_to_min_transf tbl) reps],
          S cur_tag)
    | DictIdx attr =>
        let dict_idx_tag := String.of_nat cur_tag in
        ([(dict_idx_tag, cdict_idx attr, dict_idx_wf attr)],
          [dict_lookup_transf dict_idx_tag attr;
           use_dict_idx_transf dict_idx_tag attr;
           fun tbl => repeat_transf (cons_to_insert_transf attr tbl) reps],
          S cur_tag)
    | BitmapIdx attr v =>
        let pk_idx_tag := String.of_nat cur_tag in
        let bm_tag := String.of_nat (S cur_tag) in
        ([(pk_idx_tag, cpk_idx, pk_idx_wf);
          (bm_tag, bitmap attr v, bitmap_wf attr v)],
          [filter_to_bitmap_lookup_transf pk_idx_tag bm_tag attr v;
           use_bitmap_transf bm_tag attr v;
           fun tbl => repeat_transf (cons_to_bitmap_update_transf tbl) reps;
           use_pk_idx_transf pk_idx_tag;
           fun tbl => repeat_transf (cons_to_pk_idx_update_transf tbl) reps],
          S (S cur_tag))
end.

  Fixpoint mk_idxs (cur_tag : nat) (reps : nat) (ics : list index_choice) :
    list (string * IndexInterface.index * (value -> value -> Prop)) * list (string -> command -> command) * nat :=
    match ics with
    | [] => ([], [], cur_tag)
    | ic :: ics =>
        let '(idxs1, transfs1, cur_tag1) := mk_idx cur_tag reps ic in
        let '(idxs2, transfs2, cur_tag2) := mk_idxs cur_tag1 reps ics in
        (app idxs1 idxs2, app transfs1 transfs2, cur_tag2)
    end.

  Definition mk_compo_idx (idxs : list (string * IndexInterface.index * (value -> value -> Prop))) : IndexInterface.index :=
    compo_idx idxs "hole" (word:=word).

  Lemma Forall_tag_bound_trans : forall a b c l,
      Forall (fun s => exists n, s = String.of_nat n /\ a <= n < b) l ->
      c <= a ->
      Forall (fun s => exists n, s = String.of_nat n /\ c <= n < b) l.
  Proof.
    induction l; constructor; invert_Forall; auto.
    destruct_exists.
    eexists; intuition eauto using Nat.le_trans.
  Qed.

  Lemma Forall_tag_bound_trans2 : forall a b c l,
      Forall (fun s => exists n, s = String.of_nat n /\ a <= n < b) l ->
      b <= c ->
      Forall (fun s => exists n, s = String.of_nat n /\ a <= n < c) l.
  Proof.
    induction l; constructor; invert_Forall; auto.
    destruct_exists.
    eexists; intuition eauto using Nat.le_trans.
  Qed.

  Lemma mk_idx_ok : forall ic init_tag reps idxs transfs next_tag,
      (idxs, transfs, next_tag) = mk_idx init_tag reps ic ->
      init_tag < next_tag /\
      Forall (fun '(_, idx, idx_wf) => IndexInterface.ok idx idx_wf) idxs /\
        Forall (fun tag => exists n, tag = String.of_nat n /\ init_tag <= n /\ n < next_tag) (map fst (map fst idxs)) /\
        NoDup (map fst (map fst idxs)) /\
        Forall (fun '(_, idx, _) => hole = "hole") idxs.
  Proof.
    destruct ic; unfold mk_idx; intros;
      invert_pair; intuition idtac; constructor; auto using NoDup_nil, csum_agg_ok, cmin_agg_ok, cdict_idx_ok, cpk_idx_ok, bitmap_ok; auto.
    1-4: eexists; intuition eauto.
    1:{ repeat constructor. unfold String.of_nat.
        exists (S init_tag); intuition auto. }
    1:{ intuition idtac.
        cbn [fst] in *. destruct_In; auto.
        apply String.of_nat_inj, Nat.neq_succ_diag_l in H.
        intuition fail. }
    1:{ cbn [fst].
        constructor; auto using NoDup_nil. }
  Qed.

  Lemma mk_idxs_ok : forall ics init_tag reps idxs transfs next_tag,
      (idxs, transfs, next_tag) = mk_idxs init_tag reps ics ->
      init_tag <= next_tag /\
      Forall (fun '(_, idx, idx_wf) => IndexInterface.ok idx idx_wf) idxs /\
        Forall (fun tag => exists n, tag = String.of_nat n /\ init_tag <= n /\ n < next_tag) (map fst (map fst idxs)) /\
        NoDup (map fst (map fst idxs)) /\
        Forall (fun '(_, idx, _) => hole = "hole") idxs.
  Proof.
    induction ics; cbn; intros.
    1:{ invert_pair; intuition auto using NoDup_nil. }
    1:{ repeat destruct_match_hyp. invert_pair.
        intuition idtac.
        all: lazymatch goal with
               E: mk_idx _ _ _ = _ |- _ =>
                 symmetry in E; apply mk_idx_ok in E
             end; intuition idtac.
        all: lazymatch goal with
               E: mk_idxs _ _ _ = _ |- _ =>
                 symmetry in E; apply IHics in E
             end; intuition idtac.
        1:{ eauto using Nat.lt_le_trans, Nat.lt_le_incl. }
        1:{ apply Forall_app; intuition idtac. }
        1:{ rewrite !map_app. apply Forall_app; intuition idtac.
            2: eapply Forall_tag_bound_trans; eauto using Nat.lt_le_trans, Nat.lt_le_incl.
            eapply Forall_tag_bound_trans2; eauto. }
        1:{ rewrite !map_app. apply NoDup_app; auto.
            intros. intro contra. repeat apply_Forall_In.
            repeat destruct_exists; intuition subst.
            lazymatch goal with
              E: String.of_nat _ = String.of_nat _ |- _ =>
                apply String.of_nat_inj in E
            end. subst.
            lazymatch goal with
              H: ?x <= ?y, _: ?y < ?x |- _ =>
                apply Nat.le_ngt in H
            end; intuition idtac. }
        1:{ apply Forall_app; intuition idtac. } }
  Qed.

  Lemma mk_compo_idx_ok : forall init_tag reps index_choices idxs transfs next_tag,
      (idxs, transfs, next_tag) = mk_idxs init_tag reps index_choices ->
      IndexInterface.ok (mk_compo_idx idxs) (compo_idx_wf idxs).
  Proof.
    intros. apply mk_idxs_ok in H; intuition idtac.
    apply compo_idx_ok; auto.
  Qed.
End WithConcreteMaps.
