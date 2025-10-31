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

  Notation idxs := [("sum_agg_tag", csum_agg, sum_agg_wf);
                    ("dict_idx_tag", cdict_idx, dict_idx_wf);
                    ("pk_idx_tag", cpk_idx, pk_idx_wf);
                    ("bm_tag", bitmap, bitmap_wf)].
  Instance ccompo_idx : IndexInterface2.index := compo_idx idxs "hole" (word:=word).
  Instance ccompo_idx_ok : IndexInterface2.ok ccompo_idx (compo_idx_wf idxs).
  apply compo_idx_ok; repeat constructor; intros; auto with transf_hints.
  all: cbn; rewrite <- eqb_eq; intuition idtac; discriminate.
  Qed.

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
    repeat (repeat apply_transf_sound_lemmas; eauto 10 with transf_hints).
  Qed.

  Require Import fiat2.Notations.
  Open Scope fiat2_scope.

  Definition row_ty := TRecord (record_sort [("name", TString); ("department", TString); ("feedback", TString); ("salary", TInt); ("state", TString)]).
  (* Two Arbitrary well_typed rows *)
  Definition row1 := EVar "row1".
  Definition row2 := EVar "row2".
  (* ??? change the names *)

  Definition build_responses1 := <{ set "responses" := row1 :: row2 :: mut "responses" }>.
  Definition filter_responses dpt : expr := ESort LikeList <[ "row" <- mut "responses" ;
                                                       check("row"["department"] == << EAtom (AString dpt) >>);
                                                              ret "row" ]>.
  (* ??? foreach from another table to update this table e.g. purchase of items*)
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

  Theorem ex1_transformed_sem : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      interp_command store env ex1_transformed = interp_command store env ex1.
  Proof.
    intros. apply transf_sound__preserve_sem; auto using ex_transf_sound with transf_hints.
  Qed.
End ConcreteExample.

Print Assumptions ex1_transformed.
