Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface
  fiat2.CollectionTransf fiat2.ExistsTransf fiat2.DictIndexImpl fiat2.SumAgg fiat2.MinAgg fiat2.SetAgg fiat2.TransfUtils fiat2.FlatmapTransf fiat2.IndexTransf fiat2.TransfSound fiat2.Utils fiat2.Substitute
  fiat2.Surface fiat2.UniqueDictIndexImpl fiat2.UniqueIndexGate fiat2.UniqueIndexUse.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation.
Import ListNotations.

Require Import fiat2.Notations.
Open Scope fiat2_scope.

Variant basic_transf :=
  | SwapIfNil
  | MergeIf
  | SplitIf
  | SwapFlatmapIf
  | IfNilIntoFlatmap
  | SwapConjuncts
  | AnnotateCollection
  | PushdownCollection
  | FlatmapAssoc
  | FlatmapSingleton
  | FlatmapIdentity
  | FlatmapIf
  | SwapBagFlatmaps
  (* an emptiness test of a key-equality filter is a membership test in the
     set of the keys; see ExistsTransf *)
  | FilterEmptyToSetMem.

Variant index_choice :=
  | SumAgg (attr : string)
  | MinAgg (attr : string)
  | SetAgg (attr : string)
  | DictIdx (attr : string).

Variant anno_command :=
  | AC (basic_transfs : list basic_transf) (all_index_choices : list (list index_choice)) (c : command).

Definition annotate_collection_transf := fold_command id annotate_collection.
Definition push_down_collection_transf := fold_command id push_down_collection.
Definition swap_if_nil_transf := fold_command id swap_if_nil_head.
Definition merge_if_transf := fold_command id merge_if_head.
Definition split_if_transf := fold_command id split_if_head.
Definition swap_flatmap_if_transf := fold_command id swap_flatmap_if_head.
Definition if_nil_into_flatmap_transf := fold_command id if_nil_into_flatmap_head.
Definition swap_conjuncts_transf := fold_command id swap_conjuncts_head.
Definition flatmap_assoc_transf := fold_command id flatmap_assoc_head.
Definition flatmap_singleton_transf := fold_command id flatmap_singleton_head.
Definition flatmap_identity_transf := fold_command id flatmap_identity_head.
Definition flatmap_if_transf := fold_command id flatmap_if_head.
Definition swap_flatmap_likebag_transf := fold_command id swap_flatmap_likebag_head.
Definition filter_eq_empty_to_set_mem_transf :=
  fold_command id filter_eq_empty_to_set_mem_head.

Definition mk_basic_transf (f : basic_transf) : command -> command :=
  match f with
  | SwapIfNil => swap_if_nil_transf
  | MergeIf => merge_if_transf
  | SplitIf => split_if_transf
  | SwapFlatmapIf => swap_flatmap_if_transf
  | IfNilIntoFlatmap => if_nil_into_flatmap_transf
  | SwapConjuncts => swap_conjuncts_transf
  | AnnotateCollection => annotate_collection_transf
  | PushdownCollection => push_down_collection_transf
  | FlatmapAssoc => flatmap_assoc_transf
  | FlatmapSingleton => flatmap_singleton_transf
  | FlatmapIdentity => flatmap_identity_transf
  | FlatmapIf => flatmap_if_transf
  | SwapBagFlatmaps => swap_flatmap_likebag_transf
  | FilterEmptyToSetMem => filter_eq_empty_to_set_mem_transf
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
    Context (tag : string).
    Context (sum_agg_attr : string).

    Definition sum_agg_wf := (SumAgg.idx_wf (locals:=clocals) "hole" sum_agg_attr "x").
    Instance csum_agg : IndexInterface.index := (sum_agg "hole" sum_agg_attr "x").
    Instance csum_agg_ok : IndexInterface.ok csum_agg sum_agg_wf.
    apply sum_agg_ok.
    Qed.

    Definition sum_agg_lookup_transf := fun tbl => fold_command_with_globals [tbl] (sum_to_agg_lookup_head sum_agg_attr "id_tag" "aux_tag" tag tbl).
    Definition cons_to_add_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_add_head).
    Definition filter_to_sub_transf := fun tbl => fold_command_with_globals [tbl] (filter_neq_to_sub_head sum_agg_attr).

    Context (min_agg_attr : string).

    Definition min_agg_wf := (MinAgg.idx_wf (locals:=clocals) "hole" min_agg_attr "x").
    Instance cmin_agg : IndexInterface.index := (min_agg "hole" min_agg_attr "x").
    Instance cmin_agg_ok : IndexInterface.ok cmin_agg min_agg_wf.
    apply min_agg_ok.
    Qed.

    Definition min_agg_lookup_transf := fun tbl => fold_command_with_globals [tbl] (min_to_agg_lookup_head min_agg_attr "id_tag" "aux_tag" tag tbl).
    Definition cons_to_min_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_min_head "y").
    (* applied once, not repeatedly: the rewritten form contains the expression
       it rewrote, in the branch that recomputes the minimum *)
    Definition filter_to_min_guard_transf := fun tbl => fold_command_with_globals [tbl] (filter_neq_to_min_guard_head min_agg_attr "m").

    Context (dict_idx_attr : string).

    Definition dict_idx_wf := (DictIndexImpl.idx_wf (width:=width) "hole" dict_idx_attr "tup" "acc" "x").
    Instance cdict_idx : IndexInterface.index := (dict_idx "hole" dict_idx_attr "tup" "acc" "x").
    Instance cdict_idx_ok : IndexInterface.ok cdict_idx dict_idx_wf.
    apply dict_idx_ok. auto with transf_hints.
    Qed.

    Definition dict_lookup_transf := fun tbl => fold_command_with_globals [tbl] (eq_filter_to_lookup_head dict_idx_attr "id_tag" "aux_tag" tag "b" tbl).
    Definition dict_range_transf := fun tbl => fold_command_with_globals [tbl] (range_filter_to_dict_range_head dict_idx_attr "id_tag" "aux_tag" tag "b" tbl).
    Definition cons_to_insert_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_insert_head dict_idx_attr "tup" "acc" "x" "y").
    Definition filter_to_delete_transf := fun tbl => fold_command_with_globals [tbl] (filter_neq_to_delete_head dict_idx_attr "tup" "acc" "x").
    Definition use_dict_idx_transf := fun tbl => fold_command_with_globals [tbl] (use_idx_head dict_idx_attr "id_tag" "aux_tag" tag tbl).

    Context (set_agg_attr : string).

    Definition set_agg_wf := (SetAgg.idx_wf (locals:=clocals) "hole" set_agg_attr "x").
    Instance cset_agg : IndexInterface.index := (set_agg "hole" set_agg_attr "x").
    Instance cset_agg_ok : IndexInterface.ok cset_agg set_agg_wf.
    apply set_agg_ok.
    Qed.

    Definition set_agg_lookup_transf := fun tbl => fold_command_with_globals [tbl] (set_to_lookup_head set_agg_attr "id_tag" "aux_tag" tag tbl).
    Definition cons_to_set_insert_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_set_insert_head set_agg_attr).
    Definition filter_to_set_diff_transf := fun tbl => fold_command_with_globals [tbl] (filter_neq_to_set_diff_head set_agg_attr).

  End CommonPipelineParts.

  Definition mk_idx (cur_tag : nat) (reps : nat) (ic : index_choice) :
    list (string * IndexInterface.index * (value -> value -> Prop)) * list (string -> command -> command) * nat :=
    match ic with
    | SumAgg attr =>
        let sum_tag := String.of_nat cur_tag in
        ([(sum_tag, csum_agg attr, sum_agg_wf attr)],
          [sum_agg_lookup_transf sum_tag attr;
           (* an insert and a keyed delete are both maintained in one pass; the
              delete's rewrite is not self-similar, so repeating it is safe *)
           fun tbl => repeat_transf (Basics.compose (filter_to_sub_transf attr tbl)
                                       (cons_to_add_transf tbl)) reps],
          S cur_tag)
    | MinAgg attr =>
        let min_tag := String.of_nat cur_tag in
        ([(min_tag, cmin_agg attr, min_agg_wf attr)],
                       [min_agg_lookup_transf min_tag attr;
                        fun tbl => repeat_transf (cons_to_min_transf tbl) reps;
                        (* last in the list, so first to run: the guard leaves a
                           read of the old minimum for the lookup rule above *)
                        filter_to_min_guard_transf attr],
          S cur_tag)
    | SetAgg attr =>
        let set_tag := String.of_nat cur_tag in
        ([(set_tag, cset_agg attr, set_agg_wf attr)],
          [set_agg_lookup_transf set_tag attr;
           (* an insert and a keyed delete are both maintained in one pass *)
           fun tbl => repeat_transf (Basics.compose (filter_to_set_diff_transf attr tbl)
                                       (cons_to_set_insert_transf attr tbl)) reps],
          S cur_tag)
    | DictIdx attr =>
        let dict_idx_tag := String.of_nat cur_tag in
        ([(dict_idx_tag, cdict_idx attr, dict_idx_wf attr)],
          [dict_lookup_transf dict_idx_tag attr;
           dict_range_transf dict_idx_tag attr;
           use_dict_idx_transf dict_idx_tag attr;
           (* inserts and deletes are maintained in the same loop, so that
              an insert into a filtered table and a filter of an extended table
              are both handled *)
           fun tbl => repeat_transf (Basics.compose (filter_to_delete_transf attr tbl)
                                       (cons_to_insert_transf attr tbl)) reps],
          S cur_tag)
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
      invert_pair; intuition idtac; constructor;
      auto using NoDup_nil, csum_agg_ok, cmin_agg_ok, cset_agg_ok, cdict_idx_ok; auto.
    1-4: eexists; intuition eauto.
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

  (* The basic phase keeps whatever the program established.

     Each basic rewrite is fold_command id applied to an expression rule, so
     none of them touches the command skeleton, and a semantics-preserving
     expression rewrite preserves any parameterized_wf.  That matters because
     this phase runs before any index is installed: an invariant a declared
     constraint puts on a table has to survive it to be usable at the
     installation. *)
  Lemma mk_basic_transf_preserve_parameterized_wf :
    forall a c P A (Gstore Genv : ctenv),
      tenv_wf Gstore -> tenv_wf Genv ->
      parameterized_wf (locals:=clocals) Gstore Genv P A c ->
      parameterized_wf Gstore Genv P A (mk_basic_transf a c).
  Proof.
    intros * H_Gs H_Ge H_wf. destruct a; cbn [mk_basic_transf];
      unfold swap_if_nil_transf, merge_if_transf, split_if_transf,
        swap_flatmap_if_transf, if_nil_into_flatmap_transf, swap_conjuncts_transf,
        annotate_collection_transf, push_down_collection_transf,
        flatmap_assoc_transf, flatmap_singleton_transf, flatmap_identity_transf,
        flatmap_if_transf, swap_flatmap_likebag_transf,
        filter_eq_empty_to_set_mem_transf;
      eapply expr_transf_sound__preserve_parameterized_wf;
      eauto with transf_hints.
  Qed.

  Lemma compose_basic_transfs_preserve_parameterized_wf :
    forall fs c P A (Gstore Genv : ctenv),
      tenv_wf Gstore -> tenv_wf Genv ->
      parameterized_wf (locals:=clocals) Gstore Genv P A c ->
      parameterized_wf Gstore Genv P A
        (compose_basic_transfs (map mk_basic_transf fs) c).
  Proof.
    induction fs; cbn [map compose_basic_transfs fold_right]; auto; intros.
    unfold Basics.compose.
    apply mk_basic_transf_preserve_parameterized_wf; auto.
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

  (* The soundness of one index's own rewrites, against any invariant at least
     as strong as the index's own.

     This cannot be a corollary of the instance below: aug_transf_sound is
     monotone in the invariant in NEITHER direction, since it both assumes and
     re-establishes the same parameterized_wf.  So the generalization has to be
     what is proved.  It costs one tactic per rewrite, because every rewrite
     here is really an expression rule, and an expression rule only ever
     assumes the invariant -- see expr_aug_transf_sound_strengthen_wf.

     What this buys: an index record that also carries an index whose
     correctness rests on a declared constraint is installed under the stronger
     invariant "the record is well formed AND the declarations hold", and the
     ordinary indexes' rewrites have to be usable there too. *)
  Lemma mk_idx_sound_strengthen : forall ic init_tag reps idxs transfs next_tag f,
      (idxs, transfs, next_tag) = mk_idx init_tag reps ic ->
      In f transfs ->
      forall l (Q : value -> Prop),
        incl idxs l ->
        NoDup (map fst (map fst l)) ->
        (forall v, Q v -> @aux_wf width word (@compo_idx_wf width word l) "id_tag" "aux_tag" v) ->
        @aug_transf_sound width word ctenv clocals (@IndexInterface.is_tbl_ty (mk_compo_idx l))
          (@aux_ty (mk_compo_idx l) "id_tag" "aux_tag") Q f.
  Proof.
    intros ic init_tag reps idxs transfs next_tag f H_mk H_in l Q H_incl H_nd H_Q.
    revert H_mk H_in H_incl H_nd.
    destruct ic; cbn; intros; invert_pair; repeat apply_incl_cons_inv.
    1:{ repeat destruct_In; try apply_in_nil; repeat apply_transf_sound_lemmas.
        all: try (eapply expr_aug_transf_sound_strengthen_wf; [ exact H_Q | ]).
        1:{ eapply sum_to_agg_lookup_head_sound; auto using ctenv_ok, clocals_ok.
            1: prove_aux_ty_for_idx;
            [ prove_access_record_idx_ty
            | prove_NoDup_map_fst_sort_map
            | prove_In_map_fst_sort_map ].
            1: prove_is_tbl_ty.
            1: prove_idx_wf. }
        all: apply expr_transf_sound__expr_aug_transf_sound.
        1: eapply filter_neq_to_sub_head_sound; auto using ctenv_ok, clocals_ok.
        1: eapply cons_to_add_head_sound. }
    1:{ repeat destruct_In; try apply_in_nil; repeat apply_transf_sound_lemmas.
        all: try (eapply expr_aug_transf_sound_strengthen_wf; [ exact H_Q | ]).
        1:{ eapply min_to_agg_lookup_head_sound; auto using ctenv_ok, clocals_ok.
            1: prove_aux_ty_for_idx;
            [ prove_access_record_idx_ty
            | prove_NoDup_map_fst_sort_map
            | prove_In_map_fst_sort_map ].
            1: prove_is_tbl_ty.
            1: prove_idx_wf. }
        all: apply expr_transf_sound__expr_aug_transf_sound.
        1: eapply cons_to_min_head_sound.
        1: eapply filter_neq_to_min_guard_head_sound; auto using ctenv_ok, clocals_ok. }
    1:{ repeat destruct_In; try apply_in_nil; repeat apply_transf_sound_lemmas.
        all: try (eapply expr_aug_transf_sound_strengthen_wf; [ exact H_Q | ]).
        1:{ eapply set_to_lookup_head_sound; auto using ctenv_ok, clocals_ok.
            1: prove_aux_ty_for_idx;
            [ prove_access_record_idx_ty
            | prove_NoDup_map_fst_sort_map
            | prove_In_map_fst_sort_map ].
            1: prove_is_tbl_ty.
            1: prove_idx_wf. }
        1:{ apply expr_transf_sound__expr_aug_transf_sound.
            eapply filter_neq_to_set_diff_head_sound; auto using ctenv_ok, clocals_ok. }
        1:{ apply expr_transf_sound__expr_aug_transf_sound.
            eapply cons_to_set_insert_head_sound; auto using ctenv_ok, clocals_ok. } }
    1:{ repeat destruct_In; try apply_in_nil; repeat apply_transf_sound_lemmas.
        all: try (eapply expr_aug_transf_sound_strengthen_wf; [ exact H_Q | ]).
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
        1:{ eapply range_filter_to_dict_range_head_sound; auto using ctenv_ok, clocals_ok.
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
            eapply filter_neq_to_delete_head_sound;
              eauto with transf_hints. }
        1:{ apply expr_transf_sound__expr_aug_transf_sound.
            eapply cons_to_insert_head_sound;
              eauto with transf_hints. } }
  Qed.
  Lemma mk_idx_sound : forall ic init_tag reps idxs transfs next_tag f,
      (idxs, transfs, next_tag) = mk_idx init_tag reps ic ->
      In f transfs ->
      forall l,
        incl idxs l ->
        NoDup (map fst (map fst l)) ->
        @aug_transf_sound width word ctenv clocals (@IndexInterface.is_tbl_ty (mk_compo_idx l))
          (@aux_ty (mk_compo_idx l) "id_tag" "aux_tag") (@aux_wf width word (@compo_idx_wf width word l) "id_tag" "aux_tag") f.
  Proof.
    intros. eapply mk_idx_sound_strengthen; eauto.
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

  (* ====================================================================
     The constraint-dependent installation, joined to this pipeline.

     A declared index cannot be chosen the way the others are.  mk_idx hands
     compo_idx a list of plain IndexInterface.ok indexes, and "this dictionary
     represents that table" is not an ok fact for a primary-key index: it holds
     of tables with distinct keys and of no others.  So the gated installation
     of UniqueIndexGate runs as its own layer, and what it reads is the
     declaration environment the program was elaborated with.

     It is placed between the two existing phases.  The basic phase runs first,
     as it already does, because the index rules match annotated forms; the
     unconstrained index layer runs last and needs nothing from the cenv, being
     sound for every well-typed program.  Only the middle layer has a premise,
     and only the first phase has to be shown to keep it.
     ==================================================================== *)

  (* The basic phase leaves a declared variable's initial value alone: it is an
     annotated empty list, and every basic rule matches a compound expression.
     This is what lets the gate's premise cross the phase -- see
     fold_command_id_preserve_cenv_respected for why a semantic argument would
     not be enough. *)
  Lemma mk_basic_transf_letmut_atom : forall bt (ai : atom) tbl body,
      mk_basic_transf bt (CLetMut (EAtom ai) tbl body)
      = CLetMut (EAtom ai) tbl (mk_basic_transf bt body).
  Proof. destruct bt; reflexivity. Qed.

  Lemma compose_basic_transfs_letmut_atom : forall fs (ai : atom) tbl body,
      exists body',
        compose_basic_transfs (map mk_basic_transf fs) (CLetMut (EAtom ai) tbl body)
        = CLetMut (EAtom ai) tbl body'.
  Proof.
    induction fs; cbn [map compose_basic_transfs fold_right]; intros.
    1: eexists; reflexivity.
    unfold Basics.compose.
    destruct (IHfs ai tbl body) as [ body' E ]; rewrite E.
    rewrite mk_basic_transf_letmut_atom. eexists; reflexivity.
  Qed.

  Lemma mk_basic_transf_preserve_cenv_respected :
    forall bt ce (Gstore Genv : ctenv) (ai : atom) tbl body,
      tenv_wf Gstore -> tenv_wf Genv ->
      cenv_respected (locals:=clocals) ce Gstore Genv (CLetMut (EAtom ai) tbl body) ->
      cenv_respected (locals:=clocals) ce Gstore Genv
        (mk_basic_transf bt (CLetMut (EAtom ai) tbl body)).
  Proof.
    intros * H_Gs H_Ge H_ce; destruct bt; cbn [mk_basic_transf];
      unfold swap_if_nil_transf, merge_if_transf, split_if_transf,
        swap_flatmap_if_transf, if_nil_into_flatmap_transf, swap_conjuncts_transf,
        annotate_collection_transf, push_down_collection_transf,
        flatmap_assoc_transf, flatmap_singleton_transf, flatmap_identity_transf,
        flatmap_if_transf, swap_flatmap_likebag_transf,
        filter_eq_empty_to_set_mem_transf;
      eapply (expr_transf_sound__preserve_cenv_respected (tenv := ctenv) (locals := clocals));
      eauto with transf_hints.
  Qed.

  Lemma compose_basic_transfs_preserve_cenv_respected :
    forall fs ce (Gstore Genv : ctenv) (ai : atom) tbl body,
      tenv_wf Gstore -> tenv_wf Genv ->
      cenv_respected (locals:=clocals) ce Gstore Genv (CLetMut (EAtom ai) tbl body) ->
      cenv_respected (locals:=clocals) ce Gstore Genv
        (compose_basic_transfs (map mk_basic_transf fs) (CLetMut (EAtom ai) tbl body)).
  Proof.
    induction fs; cbn [map compose_basic_transfs fold_right]; auto; intros.
    unfold Basics.compose.
    destruct (compose_basic_transfs_letmut_atom fs ai tbl body) as [ body' E ].
    rewrite E.
    apply mk_basic_transf_preserve_cenv_respected; auto.
    rewrite <- E. apply IHfs; auto.
  Qed.

  (* The unconstrained index layer on its own, as apply_all_transfs_sound
     already proves it inside its own composition. *)
  Definition idx_transfs_of (reps : nat) (icss : list (list index_choice)) :
    list (ctenv -> ctenv -> command -> command) :=
    map (fun ics =>
           let '(idxs, transfs, _) := mk_idxs O reps ics in
           mk_idx_related_transfs (mk_compo_idx idxs) (mk_idx_use_transfs transfs)) icss.

  Lemma compose_all_idx_transfs_of_sound : forall reps icss,
      transf_sound (locals:=clocals) (compose_all_idx_transfs O (idx_transfs_of reps icss)).
  Proof.
    intros. apply compose_all_idx_transfs_sound.
    rewrite Forall_forall; intros.
    unfold idx_transfs_of in *.
    rewrite in_map_iff in *.
    destruct_exists; intuition idtac.
    repeat destruct_match_hyp. subst.
    eapply mk_idx_related_transfs_sound; eauto.
  Qed.

  (* A declared index is chosen by naming the attribute the declaration is
     about; which rules it brings is fixed, as it is for the others. *)
  Variant constrained_index_choice :=
    | UniqueDictIdx (attr : string).

  Definition mk_constrained_idx_transf (ce : cenv) (cic : constrained_index_choice) :
    ctenv -> ctenv -> command -> command :=
    match cic with
    | UniqueDictIdx attr =>
        (* installed unconditionally, like any other index; it is the use rule
           that is the identity where the declarations are silent *)
        unique_idx_transf (locals := clocals) (word := word)
          "hole" attr "tup" "acc" "id_tag" "aux_tag" "u" "y" ce
    end.

  Definition apply_all_transfs_constrained (ce : cenv) (reps : nat)
    (fs : list basic_transf) (cic : option constrained_index_choice)
    (icss : list (list index_choice)) (Gstore Genv : ctenv) : command -> command :=
    Basics.compose
      (compose_all_idx_transfs O (idx_transfs_of reps icss) Gstore Genv)
      (Basics.compose
         (match cic with
          | None => id
          | Some cic => mk_constrained_idx_transf ce cic Gstore Genv
          end)
         (compose_basic_transfs (map mk_basic_transf fs))).

  Theorem apply_all_transfs_constrained_sound :
    forall ce reps fs cic icss (Gstore Genv : ctenv) (ai : atom) tbl body,
      tenv_wf Gstore -> tenv_wf Genv ->
      well_typed Gstore Genv (CLetMut (EAtom ai) tbl body) ->
      cenv_respected (locals:=clocals) ce Gstore Genv (CLetMut (EAtom ai) tbl body) ->
      well_typed Gstore Genv
        (apply_all_transfs_constrained ce reps fs cic icss Gstore Genv
           (CLetMut (EAtom ai) tbl body))
      /\ forall (store env : clocals),
          locals_wf Gstore store -> locals_wf Genv env ->
          interp_command store env
            (apply_all_transfs_constrained ce reps fs cic icss Gstore Genv
               (CLetMut (EAtom ai) tbl body))
          = interp_command store env (CLetMut (EAtom ai) tbl body).
  Proof.
    intros * H_Gs H_Ge H_wt H_ce.
    unfold apply_all_transfs_constrained, Basics.compose.
    (* the basic phase: sound, and it keeps the gate's premise *)
    pose proof (compose_basic_transfs_sound fs Gstore Genv _ H_Gs H_Ge H_wt)
      as [ H_wt1 H_sem1 ].
    pose proof (compose_basic_transfs_preserve_cenv_respected
                  fs ce Gstore Genv ai tbl body H_Gs H_Ge H_ce) as H_ce1.
    cbn in H_wt1, H_sem1.
    (* the gated layer: sound where the declarations say it may fire *)
    assert (H_mid :
             well_typed Gstore Genv
               (match cic with
                | None => id
                | Some cic => mk_constrained_idx_transf ce cic Gstore Genv
                end (compose_basic_transfs (map mk_basic_transf fs)
                       (CLetMut (EAtom ai) tbl body)))
             /\ forall (store env : clocals),
                 locals_wf Gstore store -> locals_wf Genv env ->
                 interp_command store env
                   (match cic with
                    | None => id
                    | Some cic => mk_constrained_idx_transf ce cic Gstore Genv
                    end (compose_basic_transfs (map mk_basic_transf fs)
                           (CLetMut (EAtom ai) tbl body)))
                 = interp_command store env
                     (compose_basic_transfs (map mk_basic_transf fs)
                        (CLetMut (EAtom ai) tbl body))).
    1:{ destruct cic as [ [ attr ] | ]; [ | split; auto ].
        cbn [mk_constrained_idx_transf].
        apply (unique_idx_transf_sound "hole" attr "tup" "acc"
                 ltac:(discriminate) "id_tag" "aux_tag" ltac:(discriminate) "u" "y");
          assumption. }
    destruct H_mid as [ H_wt2 H_sem2 ].
    (* the unconstrained index layer: sound for every well-typed program *)
    pose proof (compose_all_idx_transfs_of_sound reps icss Gstore Genv _ H_Gs H_Ge H_wt2)
      as [ H_wt3 H_sem3 ].
    split; [ assumption | ].
    intros store env H_lws H_lwe.
    rewrite H_sem3 by assumption.
    rewrite H_sem2 by assumption.
    apply H_sem1; assumption.
  Qed.


  (* With no constrained choice the pipeline is sound for every well-typed
     program, exactly as apply_all_transfs is.  Nothing is assumed about the
     declarations because none is consulted -- which is what makes a rewrite
     like the one in ExistsTransf, that needs no declaration, usable without
     one. *)
  Lemma apply_all_transfs_constrained_None_sound : forall ce reps fs icss,
      transf_sound (locals:=clocals) (apply_all_transfs_constrained ce reps fs None icss).
  Proof.
    unfold apply_all_transfs_constrained, Basics.compose, transf_sound, id; intros.
    pose proof (compose_basic_transfs_sound fs Gstore Genv _ H H0 H1)
      as [ H_wt1 H_sem1 ]; cbn in H_wt1, H_sem1.
    pose proof (compose_all_idx_transfs_of_sound reps icss Gstore Genv _ H H0 H_wt1)
      as [ H_wt2 H_sem2 ].
    split; [ exact H_wt2 | ].
    intros store env H_lws H_lwe.
    rewrite H_sem2 by assumption. apply H_sem1; assumption.
  Qed.

  (* The annotation a program is optimized with, now also carrying the
     declaration environment it was elaborated with and which declared index to
     install.  A separate variant, since the existing one is what every
     unconstrained example is written against. *)
  Variant canno_command :=
    | CAC (ce : cenv) (basic_transfs : list basic_transf)
        (constrained_choice : option constrained_index_choice)
        (all_index_choices : list (list index_choice)) (c : command).

  Definition apply_optimize_anno_constrained (ac : canno_command) (Gstore Genv : ctenv) :=
    match ac with
    | CAC ce fs cic icss c =>
        apply_all_transfs_constrained ce 10000 fs cic icss Gstore Genv c
    end.

  (* The end of the chain: on a program the surface language elaborated, the
     whole pipeline -- basic rewrites, the declared index, and whatever
     unconstrained indexes were chosen -- is sound with no side condition
     beyond the ordinary typing ones, and for any hints.  Nothing is assumed
     about the index choices, and the declarations the program carries are what
     make the constrained installation available. *)
  Theorem elab_apply_optimize_anno_constrained_sound :
    forall sc ce free_vars fs cic icss (Gstore Genv : ctenv) tbl row_ty ds,
      tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
      incl (get_free_vars Genv) free_vars ->
      Forall (decl_wf row_ty) ds ->
      well_typed Gstore Genv (elab ce free_vars (SLetConstrained tbl row_ty ds sc)) ->
      well_typed Gstore Genv
        (apply_optimize_anno_constrained
           (CAC ((tbl, (row_ty, ds)) :: cenv_rm tbl ce) fs cic icss
              (elab ce free_vars (SLetConstrained tbl row_ty ds sc))) Gstore Genv)
      /\ forall (store env : clocals),
          locals_wf Gstore store -> locals_wf Genv env ->
          interp_command store env
            (apply_optimize_anno_constrained
               (CAC ((tbl, (row_ty, ds)) :: cenv_rm tbl ce) fs cic icss
                  (elab ce free_vars (SLetConstrained tbl row_ty ds sc))) Gstore Genv)
          = interp_command store env (elab ce free_vars (SLetConstrained tbl row_ty ds sc)).
  Proof.
    intros * H_Gs H_Ge H_rt H_fv H_ds H_wt.
    pose proof (elab_cenv_respected (locals := clocals)
                  sc ce free_vars Gstore Genv tbl row_ty ds
                  H_Gs H_Ge H_rt H_fv H_ds H_wt) as H_ce.
    cbn [apply_optimize_anno_constrained].
    cbn [elab] in H_wt, H_ce |- *.
    apply apply_all_transfs_constrained_sound; assumption.
  Qed.

End WithConcreteMaps.
