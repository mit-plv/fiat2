Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface
  fiat2.CollectionTransf fiat2.DictIndexImpl fiat2.SumAgg fiat2.MinAgg fiat2.BitmapIndex fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf fiat2.TransfSound fiat2.Utils fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
Require Import List String ZArith.
Import ListNotations.

Require Import fiat2.Notations.
Open Scope fiat2_scope.

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

    Notation sum_agg_wf := (SumAgg.idx_wf (locals:=clocals) "hole" sum_agg_attr "x").
    Instance csum_agg : IndexInterface.index := (sum_agg "hole" sum_agg_attr "x").
    Instance csum_agg_ok : IndexInterface.ok csum_agg sum_agg_wf.
    apply sum_agg_ok.
    Qed.

    Definition sum_agg_lookup_transf := fun tbl => fold_command_with_globals [tbl] (sum_to_agg_lookup_head sum_agg_attr "id_tag" "aux_tag" "sum_agg_tag" tbl).
    Definition cons_to_add_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_add_head).

    Context (min_agg_attr : string).

    Notation min_agg_wf := (MinAgg.idx_wf (locals:=clocals) "hole" min_agg_attr "x").
    Instance cmin_agg : IndexInterface.index := (min_agg "hole" min_agg_attr "x").
    Instance cmin_agg_ok : IndexInterface.ok cmin_agg min_agg_wf.
    apply min_agg_ok.
    Qed.

    Definition min_agg_lookup_transf := fun tbl => fold_command_with_globals [tbl] (min_to_agg_lookup_head min_agg_attr "id_tag" "aux_tag" "min_agg_tag" tbl).
    Definition cons_to_min_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_min_head "y").

    Context (dict_idx_attr : string).

    Notation dict_idx_wf := (DictIndexImpl.idx_wf "hole" dict_idx_attr "tup" "acc" "x").
    Instance cdict_idx : IndexInterface.index := (dict_idx "hole" dict_idx_attr "tup" "acc" "x").
    Instance cdict_idx_ok : IndexInterface.ok cdict_idx dict_idx_wf.
    apply dict_idx_ok. auto with transf_hints.
    Qed.

    Definition dict_lookup_transf := fun tbl => fold_command_with_globals [tbl] (eq_filter_to_lookup_head dict_idx_attr "id_tag" "aux_tag" "dict_idx_tag" "b" tbl).
    Definition cons_to_insert_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_insert_head dict_idx_attr "tup" "acc" "x" "y").
    Definition use_dict_idx_transf := fun tbl => fold_command_with_globals [tbl] (use_idx_head dict_idx_attr "id_tag" "aux_tag" "dict_idx_tag" tbl).

    Notation pk_idx_wf := (BitmapIndex.pk_idx_wf "hole" "tup" "acc").
    Instance cpk_idx : IndexInterface.index := (pk_idx "hole" "tup" "acc").
    Instance cpk_idx_ok : IndexInterface.ok cpk_idx pk_idx_wf.
    apply pk_idx_ok. auto with transf_hints.
    Qed.

    Context (bitmap_attr : string).
    Context (bitmap_str : string).
    Notation bitmap_wf := (bitmap_wf bitmap_attr bitmap_str "hole" "tup").
    Instance bitmap : IndexInterface.index := (bitmap bitmap_attr bitmap_str "hole" "tup").
    Instance bitmap_ok : IndexInterface.ok bitmap bitmap_wf.
    apply bitmap_ok.
    Qed.

    Definition cons_to_pk_idx_update_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_pk_idx_update_head "y").
    Definition use_pk_idx_transf := fun tbl => fold_command_with_globals [tbl] (use_pk_idx_head "id_tag" "aux_tag" "pk_idx_tag" tbl).
    Definition cons_to_bitmap_update_transf := fun tbl => fold_command_with_globals [tbl] cons_to_bitmap_update_head.
    Definition use_bitmap_transf := fun tbl => fold_command_with_globals [tbl] (use_bitmap_head bitmap_attr bitmap_str "id_tag" "aux_tag" "bm_tag" tbl).
    Definition filter_to_bitmap_lookup_transf :=
      fun tbl => fold_command_with_globals [tbl]
                   (filter_to_bitmap_lookup_head bitmap_attr bitmap_str "id_tag" "aux_tag" "pk_idx_tag" "bm_tag" "x" "b" "acc" tbl).

    Definition to_proj_transf := fold_command id to_proj_head.
    Definition to_filter_transf := fold_command id to_filter_head.
    Definition annotate_collection_transf := fold_command id annotate_collection.
    Definition push_down_collection_transf := fold_command id push_down_collection.



    Notation idxs := [("sum_agg_tag", csum_agg, sum_agg_wf);
                      ("min_agg_tag", cmin_agg, min_agg_wf);
                      ("dict_idx_tag", cdict_idx, dict_idx_wf);
                      ("pk_idx_tag", cpk_idx, pk_idx_wf);
                      ("bm_tag", bitmap, bitmap_wf)].
    Instance ccompo_idx : IndexInterface.index := compo_idx idxs "hole" (word:=word).
    Instance ccompo_idx_ok : IndexInterface.ok ccompo_idx (compo_idx_wf idxs).
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
                                      (Basics.compose (min_agg_lookup_transf tbl)
                                         (Basics.compose (repeat_transf (cons_to_min_transf tbl) 10000)
                                            (Basics.compose (sum_agg_lookup_transf tbl)
                                               (repeat_transf (cons_to_add_transf tbl) 10000)
              )))))))))))) Gstore Genv)
           (Basics.compose push_down_collection_transf
                 (Basics.compose annotate_collection_transf
                    (Basics.compose to_filter_transf to_proj_transf))).

         Lemma ex_transf_sound : transf_sound (locals:=clocals) ex_transf.
    Proof.
      repeat (repeat apply_transf_sound_lemmas; eauto 10 with transf_hints).
    Qed.
  End CommonPipelineParts.

  Section Example1.
    Definition sum_agg_attr1 := "salary".
    Definition min_agg_attr1 := "salary".
    Definition dict_idx_attr1 := "department".
    Definition bitmap_attr1 := "location".
    Definition bitmap_str1 := "A".

    Definition ex_transf1 := ex_transf sum_agg_attr1 min_agg_attr1 dict_idx_attr1 bitmap_attr1 bitmap_str1.

    Definition row_ty := TRecord (record_sort [("name", TString); ("department", TString); ("feedback", TString); ("salary", TInt); ("location", TString)]).
    (* Two Arbitrary well_typed rows *)
    Definition row1 := EVar "row1".
    Definition row2 := EVar "row2".

    Definition build_responses1 := <{ set "responses" := row1 :: row2 :: mut "responses" }>.
    Definition filter_responses dpt : expr := ESort LikeList <[ "row" <- mut "responses" ;
                                                                check("row"["department"] == << EAtom (AString dpt) >>);
                                                                ret "row" ]>.
    Definition filter_responses2 : expr := <[ "row" <- mut "responses" ;
                                              check("row"["location"] == << EAtom (AString "A") >>);
                                              ret "row" ]>.
    Definition query1_1 := CForeach (filter_responses "CS") "r"
                           <{ let "name" = "r"["name"] +++ << EAtom (AString ": ") >> in
                              let "feedback" = "r"["feedback"] +++ << EAtom (AString "\n") >> in
                              let "line" = "name" +++ "feedback" in
                              set "all_feedback" := mut "all_feedback" +++ "line" }>.
    Definition query1_2 := CAssign "sum" (EFold (<["row" <- mut "responses" ; ret "row"["salary"]]>) (EAtom (AInt 0)) "v" "acc" (EBinop OPlus (EVar "v") (EVar "acc"))).
    Definition query1_3 := CForeach (filter_responses2) "r"
                           <{ let "name" = "r"["name"] +++ << EAtom (AString ": ") >> in
                              let "feedback" = "r"["feedback"] +++ << EAtom (AString "\n") >> in
                              let "line" = "name" +++ "feedback" in
                              set "all_feedback" := mut "all_feedback" +++ "line" }>.
    Definition ex1' := CSeq build_responses1 (CSeq query1_1 (CSeq query1_2 query1_3)).
    Definition ex1 := CLetMut (EAtom (ANil (Some (row_ty)))) "responses" ex1'.

    Definition init_Gstore1 : ctenv := map.put (map.put map.empty "all_feedback" TString) "sum" TInt.
    Definition init_Genv1 : ctenv := map.put (map.put map.empty "row1" row_ty) "row2" row_ty.

    (* Compute typecheck init_Gstore1 init_Genv1 ex1. *)

    Definition ex1_transformed := ex_transf1 init_Gstore1 init_Genv1 ex1.
    (* Compute ex1_transformed. *)

    Theorem ex1_transformed_sem : forall (store env : clocals),
        locals_wf init_Gstore1 store ->
        locals_wf init_Genv1 env ->
        interp_command store env ex1_transformed = interp_command store env ex1.
    Proof.
      apply transf_sound__preserve_sem; eauto using ex_transf_sound with transf_hints.
    Qed.
  End Example1.

  Section Example2.
    Definition sum_agg_attr2 := "price".
    Definition min_agg_attr2 := "price".
    Definition dict_idx_attr2 := "color".
    Definition bitmap_attr2 := "name".
    Definition bitmap_str2 := "shirt_1".

    Definition ex_transf2 := ex_transf sum_agg_attr2 min_agg_attr2 dict_idx_attr2 bitmap_attr2 bitmap_str2.

    Definition outfits_row_ty := TRecord (record_sort [("outfit_name", TString); ("shirt_name", TString); ("shirt_color", TString); ("shirt_price", TInt); ("pants_name", TString); ("pants_color", TString); ("pants_price", TInt)]).

    Definition shirts_row_ty := TRecord (record_sort [("name", TString); ("color", TString); ("price", TInt)]).

    Definition populate_shirts_from_outfits : command :=
      <{ for "row" in <[ "row" <- mut "outfits";
                         ret ({"name" : "row" ["shirt_name"],
                                 "color" : "row" ["shirt_color"],
                                   "price" : "row" ["shirt_price"]}) ]>:
                         set "shirts" := "row" :: mut "shirts" end }>.

    Definition filter_shirts color : expr :=
      ESort LikeList <[ "row" <- mut "shirts" ;
                        check("row"["color"] == << EAtom (AString color) >>);
                        ret "row" ]>.

    Definition query2_1 :=
      CLetMut (EAtom (AString ""))  "all_shirt_info"
        (CForeach (filter_shirts "white") "r"
          <{ let "n" = "r"["name"] +++ << EAtom (AString ": ") >> in
            let "p" = << EUnop OIntToString (EAccess (EVar "r") "price") >> +++ << EAtom (AString "\n") >> in
            let "line" = "n" +++ "p" in
            set "all_shirt_info" := mut "all_shirt_info" +++ "line" }>).

    Definition query2_2 :=
      CAssign "total_shirt_price" (EFold (<["row" <- mut "shirts" ; ret "row"["price"]]>) (EAtom (AInt 0)) "v" "acc" (EBinop OPlus (EVar "v") (EVar "acc"))).

    Definition query2_3 :=
      CAssign "min_shirt_price"
        (EFold (<["row" <- mut "shirts" ; ret "row"["price"]]>) (EAtom (ANone (Some TInt))) "v" "acc"
           (EOptMatch (EVar "acc") (EUnop OSome (EVar "v"))
              "x" (EIf (EBinop OLess (EVar "v") (EVar "x")) (EUnop OSome (EVar "v")) (EVar "acc")))).

    Definition ex2 := CLetMut (EAtom (ANil (Some (shirts_row_ty)))) "shirts"
                        (CSeq populate_shirts_from_outfits
                           (CSeq query2_1
                              (CSeq query2_2 query2_3))).

    Definition init_Gstore2 : ctenv := map.put (map.put (map.put map.empty "outfits" (TList outfits_row_ty)) "total_shirt_price" TInt) "min_shirt_price" (TOption TInt).
    Definition init_Genv2 : ctenv := map.empty.

    (* Compute typecheck init_Gstore2 init_Genv2 ex2. *)

    Definition ex2_transformed := ex_transf2 init_Gstore2 init_Genv2 ex2.
    (* Compute ex2_transformed. *)

    Theorem ex2_transformed_sem : forall (store env : clocals),
        locals_wf init_Gstore2 store ->
        locals_wf init_Genv2 env ->
        interp_command store env ex2_transformed = interp_command store env ex2.
    Proof.
      apply transf_sound__preserve_sem; eauto using ex_transf_sound with transf_hints.
    Qed.
  End Example2.
End WithConcreteMaps.

Print Assumptions ex1_transformed.
Print Assumptions ex2_transformed.
