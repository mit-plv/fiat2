Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface2
fiat2.CollectionTransf fiat2.DictIndexImpl2 fiat2.SumAgg fiat2.BitmapIndex fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf2 fiat2.TransfSound fiat2.Utils fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
Require Import List String ZArith.
Import ListNotations.

Section ConcreteExample.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Definition sum_agg_attr := "salary".

  Notation sum_agg_wf := (SumAgg.idx_wf "hole" sum_agg_attr "x").
  Instance csum_agg : IndexInterface2.index := (sum_agg "hole" sum_agg_attr "x").
  Instance csum_agg_ok : IndexInterface2.ok csum_agg sum_agg_wf.
  apply sum_agg_ok.
  Qed.

  Definition dict_idx_attr := "department".

  Notation dict_idx_wf := (DictIndexImpl2.idx_wf "hole" dict_idx_attr "tup" "acc" "x").
  Instance cdict_idx : IndexInterface2.index := (dict_idx "hole" dict_idx_attr "tup" "acc" "x").
  Instance cdict_idx_ok : IndexInterface2.ok cdict_idx dict_idx_wf.
  apply dict_idx_ok. auto with transf_hints.
  Qed.

  Notation pk_idx_wf := (BitmapIndex.pk_idx_wf "hole" "tup" "acc").
  Instance cpk_idx : IndexInterface2.index := (pk_idx "hole" "tup" "acc").
  Instance cpk_idx_ok : IndexInterface2.ok cpk_idx pk_idx_wf.
  apply pk_idx_ok. auto with transf_hints.
  Qed.

  Definition bitmap_attr := "state".
  Definition bitmap_str := "MA".
  Notation bitmap_wf := (bitmap_wf bitmap_attr bitmap_str "hole" "tup").
  Instance bitmap : IndexInterface2.index := (bitmap bitmap_attr bitmap_str "hole" "tup").
  Instance bitmap_ok : IndexInterface2.ok bitmap bitmap_wf.
  apply bitmap_ok.
  Qed.

  Definition to_proj_transf := fold_command id to_proj_head.
  Definition to_filter_transf := fold_command id to_filter_head.
  Definition annotate_collection_transf := fold_command id annotate_collection.
  Definition push_down_collection_transf := fold_command id push_down_collection.
  Definition sum_agg_lookup_transf := fun tbl => fold_command_with_globals [tbl] (sum_to_agg_lookup_head sum_agg_attr "id_tag" "aux_tag" "sum_agg_tag" tbl).
  Definition cons_to_add_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_add_head).
  Definition dict_lookup_transf := fun tbl => fold_command_with_globals [tbl] (eq_filter_to_lookup_head dict_idx_attr "id_tag" "aux_tag" "dict_idx_tag" "b" tbl).
  Definition cons_to_insert_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_insert_head dict_idx_attr "tup" "acc" "x" "y").
  Definition use_dict_idx_transf := fun tbl => fold_command_with_globals [tbl] (use_idx_head dict_idx_attr "id_tag" "aux_tag" "dict_idx_tag" tbl).
  Definition cons_to_pk_idx_update_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_pk_idx_update_head "y").
  Definition use_pk_idx_transf := fun tbl => fold_command_with_globals [tbl] (use_pk_idx_head "id_tag" "aux_tag" "pk_idx_tag" tbl).
  Definition cons_to_bitmap_update_transf := fun tbl => fold_command_with_globals [tbl] cons_to_bitmap_update_head.
  Definition use_bitmap_transf := fun tbl => fold_command_with_globals [tbl] (use_bitmap_head bitmap_attr bitmap_str "id_tag" "aux_tag" "bm_tag" tbl).
  Definition filter_to_bitmap_lookup_transf :=
    fun tbl => fold_command_with_globals [tbl]
                 (filter_to_bitmap_lookup_head bitmap_attr bitmap_str "id_tag" "aux_tag" "pk_idx_tag" "bm_tag" "x" "b" "acc" tbl).

  Hint Extern 5 (type_of _ _ IndexInterface2.to_idx _) => apply SumAgg.to_idx_ty : transf_hints.
  Hint Extern 5 (type_of _ _ IndexInterface2.to_idx _) => apply DictIndexImpl2.to_idx_ty : transf_hints.
  Hint Extern 5 (type_of _ _ IndexInterface2.to_idx _) => apply BitmapIndex.to_pk_idx_ty : transf_hints.
  Hint Extern 5 (type_of _ _ IndexInterface2.to_idx _) => apply BitmapIndex.to_bitmap_ty : transf_hints.
  Hint Extern 5 (type_wf (IndexInterface2.idx_ty _)) => apply DictIndexImpl2.idx_ty_wf : transf_hints.
  Hint Extern 5 (type_wf (IndexInterface2.idx_ty _)) => apply BitmapIndex.pk_idx_ty_wf : transf_hints.

  Notation idxs := [("sum_agg_tag", csum_agg, sum_agg_wf);
                    ("dict_idx_tag", cdict_idx, dict_idx_wf);
                    ("pk_idx_tag", cpk_idx, pk_idx_wf);
                    ("bm_tag", bitmap, bitmap_wf)].
  Instance ccompo_idx : IndexInterface2.index := compo_idx idxs "hole" (word:=word).
  Instance ccompo_idx_ok : IndexInterface2.ok ccompo_idx (compo_idx_wf idxs).
  apply compo_idx_ok; repeat constructor; intros; auto with transf_hints.
  all: cbn; rewrite <- eqb_eq; intuition idtac; discriminate.
  Qed.

  (* ??? move to TransfUtils *)
  Fixpoint repeat_transf (f : command -> command) (n : nat) :=
    match n with
    | O => id
    | S n => Basics.compose f (repeat_transf f n)
    end.

  Section repeat_transf_sound.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Lemma repeat_transf_preserve_aug_transf_sound : forall is_tbl_ty aux_ty aux_wf f n,
        aug_transf_sound is_tbl_ty aux_ty aux_wf f ->
        aug_transf_sound (locals:=locals) is_tbl_ty aux_ty aux_wf (fun tbl => repeat_transf (f tbl) n).
    Proof.
      induction n; cbn.
      1:{ intros _. unfold aug_transf_sound; auto. }
      1:{ intros; cbn. apply aug_transf_sound_compose; auto. }
    Qed.
  End repeat_transf_sound.

  Ltac apply_transf_sound_lemmas :=
    lazymatch goal with
    | |- transf_sound (apply_idx_related_transfs _ _ _) => apply apply_idx_related_transfs_sound
    | |- aug_transf_sound _ _ _ (fun _ => Basics.compose _ _) => apply aug_transf_sound_compose
    | |- transf_sound (fun _ _ => Basics.compose _ _) => apply transf_sound_compose
    | |- aug_transf_sound _ _ _ (fun _ => repeat_transf _ _) => apply repeat_transf_preserve_aug_transf_sound
    | |- aug_transf_sound _ _ _ _ => apply fold_command_with_globals_sound
    | |- transf_sound ?x => unfold x
    end.

  Hint Extern 5 ((_ : string) <> _) => apply eqb_neq; auto : transf_hints.
  Hint Resolve push_down_collection_sound : transf_hints.
  Hint Resolve annotate_collection_sound : transf_hints.
  Hint Extern 5 (forall v, aux_wf _ _ v -> SumAgg.aux_wf_for_idx _ _ _ _ _ _ v) =>
              intros; unfold aux_wf, aux_wf_for_idx, compo_idx_wf in *;
              repeat destruct_match_hyp; intuition idtac;
              repeat invert_Forall; unfold SumAgg.idx_wf, record_proj in *;
                             destruct_match_hyp; intuition eauto : transf_hints.
  Hint Extern 5 (SumAgg.aux_ty_for_idx _ _ _ _) => unfold SumAgg.aux_ty_for_idx, aux_ty; cbn; auto : transf_hints.
  Hint Extern 5 (forall t, IndexInterface2.is_tbl_ty t = true -> _ = true) =>
         unfold IndexInterface2.is_tbl_ty; cbn; intros;
  rewrite !Bool.andb_true_iff in *; intuition auto : transf_hints.
  Hint Resolve cons_to_add_head_sound : transf_hints.
  Hint Resolve sum_to_agg_lookup_head_sound : transf_hints.
  Hint Resolve cons_to_insert_head_sound : transf_hints.
  Hint Resolve cons_to_pk_idx_update_head_sound : transf_hints.
  Hint Resolve cons_to_bitmap_update_head_sound : transf_hints.
  Hint Resolve use_bitmap_head_sound : transf_hints.
  Hint Resolve use_idx_head_sound2 : transf_hints.
  Hint Resolve eq_filter_to_lookup_head_sound2 : transf_hints.
  Hint Resolve filter_to_bitmap_lookup_head_sound2 : transf_hints.
  Hint Resolve use_pk_idx_head_sound2 : transf_hints.
  (*
  Hint Extern 5 (expr_aug_transf_sound _ _ _ (DictIndexImpl2.use_idx_head _ _ _ _)) =>
         eapply use_idx_head_sound; [ | | | | | | eauto with transf_hints ]; auto with transf_hints : transf_hints.
  Hint Extern 5 (expr_aug_transf_sound _ _ _ (DictIndexImpl2.eq_filter_to_lookup_head _ _ _ _ _)) =>
         eapply eq_filter_to_lookup_head_sound; [ | | | | | | eauto with transf_hints ]; auto with transf_hints : transf_hints.
  Hint Extern 5 (expr_aug_transf_sound IndexInterface2.is_tbl_ty _ _
                   (filter_to_bitmap_lookup_head _ _ _ _ _ _ _ _ _)) =>
         eapply filter_to_bitmap_lookup_head_sound; eauto with transf_hints; auto with transf_hints : transf_hints.
  Hint Extern 5 (expr_aug_transf_sound IndexInterface2.is_tbl_ty _ _
                         (use_pk_idx_head _ _ _)) =>
          eapply use_pk_idx_head_sound; eauto with transf_hints; auto with transf_hints : transf_hints. *)
  Hint Extern 5 (forall v, aux_wf _ _ v -> DictIndexImpl2.aux_wf_for_idx _ _ _ _ _ _ _ _ v) =>
         intros; unfold aux_wf, DictIndexImpl2.aux_wf_for_idx, compo_idx_wf in *;
                 repeat destruct_match_hyp; intuition idtac;
  repeat invert_Forall; unfold DictIndexImpl2.idx_wf, record_proj in *;
                        destruct_match_hyp; intuition eauto : transf_hints.
  Hint Extern 5 (forall v, aux_wf _ _ v -> SumAgg.aux_wf_for_idx _ _ _ _ _ _ v) =>
         intros; unfold aux_wf, SumAgg.aux_wf_for_idx, compo_idx_wf in *;
                 repeat destruct_match_hyp; intuition idtac;
  repeat invert_Forall; unfold SumAgg.idx_wf, record_proj in *;
                        destruct_match_hyp; intuition eauto : transf_hints.
  Hint Extern 5 (forall v, aux_wf _ _ v -> BitmapIndex.aux_wf_for_idx _ _ _ _ v) =>
         intros; unfold aux_wf, BitmapIndex.aux_wf_for_idx, compo_idx_wf in *;
                 repeat destruct_match_hyp; intuition idtac;
  repeat invert_Forall; unfold BitmapIndex.bitmap_wf, record_proj in *;
            destruct_match_hyp; intuition eauto : transf_hints.
  (* ??? Simplify this? ^^^ *)
  Hint Extern 5 (DictIndexImpl2.aux_ty_for_idx _ _ _ _ _) => unfold DictIndexImpl2.aux_ty_for_idx, aux_ty; cbn; auto : transf_hints.
  Hint Extern 5 (BitmapIndex.aux_ty_for_idx _ _ _ _ _) => unfold BitmapIndex.aux_ty_for_idx, aux_ty; cbn; auto : transf_hints.
 (* Hint Unfold ??? *)
  Hint Extern 5 string => exact ("":string).

  Definition ex_transf (Gstore Genv : ctenv) :=
    Basics.compose
      (apply_idx_related_transfs (idx:=ccompo_idx) "id_tag" "aux_tag"
         (fun tbl =>
            (Basics.compose (filter_to_bitmap_lookup_transf tbl)
               (Basics.compose (use_bitmap_transf tbl)
                  (Basics.compose (repeat_transf (cons_to_bitmap_update_transf tbl) 10000)
                        (Basics.compose (use_pk_idx_transf tbl)
                           (Basics.compose (repeat_transf (cons_to_pk_idx_update_transf tbl) 10000)
                                 (Basics.compose (dict_lookup_transf tbl)
                                    (Basics.compose (use_dict_idx_transf tbl)
                                       (Basics.compose (repeat_transf (cons_to_insert_transf tbl) 10000)
                                             (Basics.compose (sum_agg_lookup_transf tbl)
                                                (Basics.compose (repeat_transf (cons_to_add_transf tbl) 10000)
                                                   (cons_to_add_transf tbl)))))))))))) Gstore Genv)
      (Basics.compose push_down_collection_transf
         (Basics.compose push_down_collection_transf
            (Basics.compose annotate_collection_transf
               (Basics.compose to_filter_transf to_proj_transf)))).

  Lemma ex_transf_sound : transf_sound (locals:=clocals) ex_transf.
  Proof.
    repeat (repeat apply_transf_sound_lemmas; eauto with transf_hints).
  Qed.

  Require Import fiat2.Notations.
  Open Scope fiat2_scope.

  Definition row_ty := TRecord (record_sort [("name", TString); ("department", TString); ("feedback", TString); ("salary", TInt); ("state", TString)]).
  (* Two Arbitrary Well_typed rows *)
  Definition row1 := EVar "row1".
  Definition row2 := EVar "row2".

  Definition build_responses1 := <{ set "responses" := row1 :: row2 :: mut "responses" }>.
  Definition filter_responses dpt : expr := ESort LikeList <[ "row" <- mut "responses" ;
                                                       check("row"["department"] == << EAtom (AString dpt) >>);
                                                              ret "row" ]>.
  Definition filter_responses2 : expr := <[ "row" <- mut "responses" ;
                                            check("row"["state"] == << EAtom (AString "MA") >>);
                                            ret "row" ]>.
  Definition query1 := CForeach (filter_responses "EECS") "r"
                      <{ let "name" = "r"["name"] +++ << EAtom (AString ": ") >> in
                         let "feedback" = "r"["feedback"] +++ << EAtom (AString "\n") >> in
                         let "line" = "name" +++ "feedback" in
                         set "all_feedback" := mut "all_feedback" +++ "line" }>.
  Definition query2 := CAssign "sum" (EFold (<["row" <- mut "responses" ; ret "row"["salary"]]>) (EAtom (AInt 0)) "v" "acc" (EBinop OPlus (EVar "v") (EVar "acc"))).
  Definition query3 := CForeach (filter_responses2) "r"
                      <{ let "name" = "r"["name"] +++ << EAtom (AString ": ") >> in
                         let "feedback" = "r"["feedback"] +++ << EAtom (AString "\n") >> in
                         let "line" = "name" +++ "feedback" in
                         set "all_feedback" := mut "all_feedback" +++ "line" }>.
  Definition ex1' := CSeq build_responses1 (CSeq query1 (CSeq query2 query3)).
  Definition ex1 := CLetMut (EAtom (ANil (Some (row_ty)))) "responses" ex1'.

  Definition init_Gstore : ctenv := map.put (map.put map.empty "all_feedback" TString) "sum" TInt.
  Definition init_Genv : ctenv := map.put (map.put map.empty "row1" row_ty) "row2" row_ty.

  Compute typecheck init_Gstore init_Genv ex1.

  Unset Printing Notations.
  Definition ex1_transformed := ex_transf init_Gstore init_Genv ex1.
  Compute ex1_transformed.

  Ltac resolve_NoDup := repeat constructor; simpl; intuition idtac; congruence.

  Ltac resolve_tenv_wf := repeat apply tenv_wf_step; try apply tenv_wf_empty; repeat constructor; resolve_NoDup.

  Hint Extern 5 (well_typed _ _ _) => simple eapply command_typechecker_sound.
  Hint Extern 5 (tenv_wf _) => resolve_tenv_wf.
  Hint Extern 5 (typecheck _ _ _ = Success _) => reflexivity.

  Theorem ex1_transformed_sem : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      interp_command store env ex1_transformed = interp_command store env ex1.
  Proof.
    intros. apply transf_sound__preserve_sem; auto using ex_transf_sound.
    (* ??? debug eauto 2 using transf_sound__preserve_sem, ex_transf_sound. *)
  Qed.
End ConcreteExample.

Print Assumptions ex1_transformed.
