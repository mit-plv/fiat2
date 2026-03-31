Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface
  fiat2.CollectionTransf fiat2.DictIndexImpl fiat2.SumAgg fiat2.MinAgg fiat2.BitmapIndex fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf fiat2.TransfSound fiat2.Utils fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation.
Import ListNotations.

Require Import fiat2.Notations.
Open Scope fiat2_scope.

Variant basic_transf :=
  | SwapIfNil
  | MergeIf
  | SwapFlatmapIf
  | IfNilIntoFlatmap
  | ToFilter
  | ToProj
  | ToJoin
  | SwapConjuncts
  | JoinToFlatmapFilter
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

Definition to_proj_transf := fold_command id to_proj_head.
Definition to_filter_transf := fold_command id to_filter_head.
Definition to_join_transf := fold_command id to_join_head.
Definition annotate_collection_transf := fold_command id annotate_collection.
Definition push_down_collection_transf := fold_command id push_down_collection.
Definition filter_pushdown_transf := fold_command id filter_pushdown_head.
Definition swap_if_nil_transf := fold_command id swap_if_nil_head.
Definition merge_if_transf := fold_command id merge_if_head.
Definition swap_flatmap_if_transf := fold_command id swap_flatmap_if_head.
Definition if_nil_into_flatmap_transf := fold_command id if_nil_into_flatmap_head.
Definition join_to_flatmap_filter_transf := fold_command id join_to_flatmap_filter_head.
Definition swap_conjuncts_transf := fold_command id swap_conjuncts_head.

Definition mk_basic_transf (f : basic_transf) : command -> command :=
  match f with
  | SwapIfNil => swap_if_nil_transf
  | MergeIf => merge_if_transf
  | SwapFlatmapIf => swap_flatmap_if_transf
  | IfNilIntoFlatmap => if_nil_into_flatmap_transf
  | ToFilter => to_filter_transf
  | ToProj => to_proj_transf
  | ToJoin => to_join_transf
  | SwapConjuncts => swap_conjuncts_transf
  | JoinToFlatmapFilter => join_to_flatmap_filter_transf
  | FilterPushdown => filter_pushdown_transf
  | AnnotateCollection => annotate_collection_transf
  | PushdownCollection => push_down_collection_transf
  end.

Definition compose_basic_transfs : list (command -> command) -> command -> command :=
  fold_right Basics.compose id.

Section WithConcreteMaps.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Section CommonPipelineParts.
    Context (tag tag' : string).
    Context (sum_agg_attr : string).

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

  Definition mk_idx_use_transfs (l : list (string -> command -> command)) : string -> command -> command :=
    fun tbl => fold_right (fun f g => Basics.compose (f tbl) g) id l.

  Definition mk_idx_related_transfs (idx : IndexInterface.index) (f : string -> command -> command) :
    ctenv -> ctenv -> command -> command :=
    apply_idx_related_transfs (idx:=idx) "id_tag" "aux_tag" f.

  Fixpoint apply_below_n_letmuts (n : nat) (f : ctenv -> ctenv -> command -> command) :
    ctenv -> ctenv -> command -> command :=
    match n with
    | O => f
    | S n => apply_below_n_letmuts n (apply_below_letmut f)
    end.

  Fixpoint compose_all_idx_transfs (n : nat) (l : list (ctenv -> ctenv -> command -> command)) :
    ctenv -> ctenv -> command -> command :=
    match l with
    | [] => fun _ _ => id
    | f :: l =>
        fun Gstore Genv =>
          Basics.compose (apply_below_n_letmuts n f Gstore Genv) (compose_all_idx_transfs (S n) l Gstore Genv)
    end.

  Definition apply_all_transfs (reps : nat) (fs : list basic_transf) (icss : list (list index_choice)) (Gstore Genv : ctenv) :=
    let idx_transfs :=
      map (fun ics =>
             let '(idxs, transfs, _) := mk_idxs O reps ics in
             let cidx := mk_compo_idx idxs in
             let idx_use_transfs := mk_idx_use_transfs transfs in
             mk_idx_related_transfs cidx idx_use_transfs) icss in
    (Basics.compose (compose_all_idx_transfs O idx_transfs Gstore Genv) (compose_basic_transfs (map mk_basic_transf fs))).

  Definition apply_optimize_anno (ac : anno_command) (Gstore Genv : ctenv) :=
    match ac with
    | AC fs icss c =>
        apply_all_transfs 10000 fs icss Gstore Genv c
    end.

  Lemma id_transf_sound : transf_sound (locals:=clocals) (fun _ _ => id).
  Proof.
    unfold transf_sound; intuition auto.
  Qed.

  Hint Resolve id_transf_sound : transf_hints.

  Lemma compose_basic_transfs_sound : forall fs,
      transf_sound (locals := clocals)
        (fun _ _ : ctenv =>
           compose_basic_transfs (map mk_basic_transf fs)).
  Proof.
    induction fs; cbn; auto with transf_hints.
    apply_transf_sound_lemmas; auto.
    destruct a; eauto with transf_hints.
  Qed.

  Lemma apply_below_n_letmuts_sound : forall n f,
      transf_sound (locals:=clocals) f ->
      transf_sound (locals:=clocals) (apply_below_n_letmuts n f).
  Proof.
    induction n; cbn; auto; intros.
    apply IHn. apply_transf_sound_lemmas.
    assumption.
  Qed.

  Lemma compose_all_idx_transfs_sound : forall l n,
      Forall (transf_sound (locals:=clocals)) l ->
      transf_sound (locals:=clocals) (compose_all_idx_transfs n l).
  Proof.
    induction l; cbn; intros; auto with transf_hints.
    apply_transf_sound_lemmas; invert_Forall; auto.
    apply apply_below_n_letmuts_sound.
    assumption.
  Qed.

  Lemma id_aug_transf_sound : forall is_tbl_ty aux_ty (aux_wf : value -> Prop),
      aug_transf_sound is_tbl_ty aux_ty aux_wf (fun _ => id).
  Proof.
    unfold aug_transf_sound; cbn; auto.
  Qed.

  Lemma aug_transf_sound_fold_compose : forall is_tbl_ty aux_ty aux_wf transfs,
      Forall (aug_transf_sound (locals:=clocals) is_tbl_ty aux_ty aux_wf) transfs ->
    aug_transf_sound is_tbl_ty aux_ty aux_wf
    (fun tbl : string =>
       fold_right
         (fun f g => Basics.compose (f tbl) g)
         id transfs).
  Proof.
    induction transfs; cbn; intros.
    1: apply id_aug_transf_sound.
    invert_Forall.
    apply_transf_sound_lemmas; auto.
  Qed.

  Ltac apply_in_nil :=
    lazymatch goal with
      H: In _ [] |- _ =>
        apply in_nil in H; intuition fail
    end.

  Ltac apply_incl_cons_inv :=
    lazymatch goal with
      H: incl (_ :: _) _ |- _ =>
        apply incl_cons_inv in H; intuition idtac
    end.

  Lemma map_fst_map_fst : forall A B C D (l : list (A * B * C)) (f : B -> D),
      map fst (map (fun '(a, b, _) => (a, f b)) l) = map fst (map fst l).
  Proof.
    induction l; cbn; auto; intros.
    repeat case_match; cbn; f_equal.
    auto.
  Qed.

  Ltac apply_in_map :=
    lazymatch goal with
      H: In _ ?l |- In _ (map ?g ?l) =>
        apply in_map with (f:=g) in H
    end.

  Ltac apply_in_map_with_tag :=
    lazymatch goal with
      H: In (?tag, _, _) ?l |- In (?tag, _) (map ?g ?l) =>
        apply in_map with (f:=g) in H
    end.

  Ltac prove_aux_ty_for_idx :=
    lazymatch goal with
      |- aux_ty_for_idx _ _ _ _ _ =>
        unfold aux_ty_for_idx;
        intros; cbn; intuition idtac;
        erewrite NoDup_Permutation_access_record;
        try apply Permutation.Permutation_sym, Permuted_record_sort
    end.

  Ltac prove_access_record_idx_ty :=
    apply NoDup_In_access_record;
    [ rewrite map_fst_map_fst; assumption
    | apply_in_map_with_tag; auto ].

  Ltac prove_NoDup_map_fst_sort_map :=
    eapply Permutation_NoDup; try eassumption;
    eapply perm_trans;
    [ | eapply Permutation_map, Permuted_record_sort ];
    rewrite map_fst_map_fst; auto.

  Ltac prove_In_map_fst_sort_map :=
    eapply Permutation_in;
    [ apply Permutation_map, Permuted_record_sort | ];
    rewrite map_map;
    apply_in_map; cbn in *;
    try lazymatch goal with
      | H:In (?tag, _, _) ?l |- In ?tag (map ?g ?l) => apply in_map with (f := g) in H
      end;
    assumption.

  Ltac prove_is_tbl_ty :=
    unfold compo_is_tbl_ty; intros;
    rewrite forallb_forall in *;
    repeat lazymatch goal with
      H: forall _, In _ _ -> _, H': In _ _ |- _ =>
    apply H in H'
  end; assumption.

  Ltac prove_idx_wf :=
    unfold aux_wf, aux_wf_for_idx; intros;
    do 4 (case_match; intuition idtac);
    unfold compo_idx_wf in *;
    repeat lazymatch goal with
    | H:Forall _ ?l, H':In _ ?l |- _ =>
        let H_new := fresh "H_new" in
        eapply List.Forall_In in H as H_new; eauto; clear H'
    end;
    repeat destruct_match_hyp; intuition idtac;
    repeat invert_pair; rewrite_l_to_r; try eassumption.

  Lemma mk_idx_sound : forall ic init_tag reps idxs transfs next_tag f,
      (idxs, transfs, next_tag) = mk_idx init_tag reps ic ->
      In f transfs ->
      forall l,
        incl idxs l ->
        NoDup (map fst (map fst l)) ->
        @aug_transf_sound width word ctenv clocals (@IndexInterface.is_tbl_ty (mk_compo_idx l))
          (@aux_ty (mk_compo_idx l) "id_tag" "aux_tag") (@aux_wf width word (@compo_idx_wf width word l) "id_tag" "aux_tag") f.
  Proof.
    destruct ic; cbn; intros; invert_pair; repeat apply_incl_cons_inv.
    1:{ repeat destruct_In; try apply_in_nil; repeat apply_transf_sound_lemmas.
        1:{ eapply sum_to_agg_lookup_head_sound; auto using ctenv_ok, clocals_ok.
            1: prove_aux_ty_for_idx;
            [ prove_access_record_idx_ty
            | prove_NoDup_map_fst_sort_map
            | prove_In_map_fst_sort_map ].
            1: prove_is_tbl_ty.
            1: prove_idx_wf. }
        1:{ apply expr_transf_sound__expr_aug_transf_sound.
            eapply cons_to_add_head_sound. } }
    1:{ repeat destruct_In; try apply_in_nil; repeat apply_transf_sound_lemmas.
        1:{ eapply min_to_agg_lookup_head_sound; auto using ctenv_ok, clocals_ok.
            1: prove_aux_ty_for_idx;
            [ prove_access_record_idx_ty
            | prove_NoDup_map_fst_sort_map
            | prove_In_map_fst_sort_map ].
            1: prove_is_tbl_ty.
            1: prove_idx_wf. }
        1:{ apply expr_transf_sound__expr_aug_transf_sound.
            eapply cons_to_min_head_sound. } }
    1:{ repeat destruct_In; try apply_in_nil; repeat apply_transf_sound_lemmas.
        1:{ eapply eq_filter_to_lookup_head_sound; auto using ctenv_ok, clocals_ok.
            1:{ rewrite is_NoDup_to_transparent.
                instantiate(3:="tup"). instantiate (2:="acc"). instantiate (1:="x").
                cbn; intuition discriminate. }
            1: prove_aux_ty_for_idx;
            [ prove_access_record_idx_ty
            | prove_NoDup_map_fst_sort_map
            | prove_In_map_fst_sort_map ].
            1: prove_is_tbl_ty.
            1: prove_idx_wf. }
        1:{ eapply use_idx_head_sound; eauto with transf_hints.
            1:{ rewrite is_NoDup_to_transparent.
                instantiate(3:="tup"). instantiate (2:="acc"). instantiate (1:="x").
                eauto with transf_hints. }
            1: prove_aux_ty_for_idx;
            [ prove_access_record_idx_ty
            | prove_NoDup_map_fst_sort_map
            | prove_In_map_fst_sort_map ].
            1: prove_is_tbl_ty.
            1: prove_idx_wf. }
        1:{ apply expr_transf_sound__expr_aug_transf_sound.
            eapply cons_to_insert_head_sound;
              eauto with transf_hints. } }
    1:{ repeat destruct_In; try apply_in_nil; repeat apply_transf_sound_lemmas.
        1:{ eapply filter_to_bitmap_lookup_head_sound;
              eauto with transf_hints.
            1:{ rewrite is_NoDup_to_transparent.
                instantiate(2:="pk_tup"). instantiate (1:="pk_acc").
                eauto with transf_hints. }
            1,2: prove_aux_ty_for_idx;
            [ prove_access_record_idx_ty
            | prove_NoDup_map_fst_sort_map
            | prove_In_map_fst_sort_map ].
            1,2: prove_is_tbl_ty.
            1,2: prove_idx_wf; instantiate(1:="hole"); auto. }
        1:{ eapply use_bitmap_head_sound;
              eauto with transf_hints.
            1: prove_aux_ty_for_idx;
            [ prove_access_record_idx_ty
            | prove_NoDup_map_fst_sort_map
            | prove_In_map_fst_sort_map ].
            1: prove_is_tbl_ty.
            1: prove_idx_wf. }
        1:{ apply expr_transf_sound__expr_aug_transf_sound.
            eapply cons_to_bitmap_update_head_sound. }
        1:{ eapply use_pk_idx_head_sound;
            eauto with transf_hints.
            1:{ instantiate(2:="pk_tup"); instantiate(1:="pk_acc");
                eauto with transf_hints. }
            1: prove_aux_ty_for_idx;
            [ prove_access_record_idx_ty
            | prove_NoDup_map_fst_sort_map
            | prove_In_map_fst_sort_map ].
            1: prove_is_tbl_ty.
            1: prove_idx_wf; instantiate (1:="hole"); assumption. }
        1:{ apply expr_transf_sound__expr_aug_transf_sound.
            apply cons_to_pk_idx_update_head_sound. } }
  Qed.

  Lemma mk_idxs_mk_idx : forall ics init_tag reps idxs transfs next_tag f,
      (idxs, transfs, next_tag) = mk_idxs init_tag reps ics ->
      In f transfs ->
      exists ic init_tag' reps idxs' transfs' next_tag',
        In ic ics /\
          (idxs', transfs', next_tag') = mk_idx init_tag' reps ic /\
          incl idxs' idxs /\
          In f transfs'.
  Proof.
    induction ics; cbn; intros.
    1:{ invert_pair. apply_in_nil. }
    1:{ repeat destruct_match_hyp. invert_pair.
        rewrite in_app_iff in *; intuition idtac.
        1:{ repeat eexists; eauto using incl_appl, incl_refl. }
        1:{ eapply IHics in H; eauto.
            repeat destruct_exists; intuition idtac.
            repeat eexists; try eassumption;
              intuition auto using incl_appr. } }
  Qed.

  Lemma mk_idx_related_transfs_sound : forall ics idxs transfs n init_tag reps,
      (idxs, transfs, n) = mk_idxs init_tag reps ics ->
      transf_sound (locals:=clocals) (mk_idx_related_transfs (mk_compo_idx idxs) (mk_idx_use_transfs transfs)).
  Proof.
    unfold mk_idx_related_transfs, mk_idx_use_transfs.
    intros.
    eapply apply_idx_related_transfs_sound.
    1: discriminate.
    apply aug_transf_sound_fold_compose.
    instantiate (1:=compo_idx_wf idxs).
    rewrite Forall_forall; intros.
    eapply mk_idxs_mk_idx in H0; eauto.
    repeat destruct_exists; intuition idtac.
    eapply mk_idx_sound; eauto.
    eapply mk_idxs_ok; eauto.
    Unshelve.
    all: eauto with transf_hints.
    eapply mk_compo_idx_ok; eauto.
  Qed.

  Theorem apply_all_transfs_sound : forall reps fs icss,
      transf_sound (locals:=clocals) (apply_all_transfs reps fs icss).
  Proof.
    unfold apply_all_transfs; intros.
    apply transf_sound_compose.
    2: apply compose_basic_transfs_sound.
    apply compose_all_idx_transfs_sound.
    rewrite Forall_forall; intros.
    rewrite in_map_iff in *.
    destruct_exists; intuition idtac.
    repeat destruct_match_hyp. subst.
    eapply mk_idx_related_transfs_sound; eauto.
  Qed.
End WithConcreteMaps.
