Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface2
  fiat2.CollectionTransf fiat2.DictIndexImpl2 fiat2.SumAgg fiat2.BitmapIndex fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf2 fiat2.TransfSound fiat2.Utils fiat2.Substitute.
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

  Section Example1.
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

    Definition bitmap_attr := "location".
    Definition bitmap_str := "A".
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

    Definition ex_transf1 (Gstore Genv : ctenv) :=
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

    Lemma ex_transf1_sound : transf_sound (locals:=clocals) ex_transf1.
    Proof.
      repeat (repeat apply_transf_sound_lemmas; eauto 10 with transf_hints).
    Qed.

    Definition row_ty := TRecord (record_sort [("name", TString); ("department", TString); ("feedback", TString); ("salary", TInt); ("location", TString)]).
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
      apply transf_sound__preserve_sem; auto using ex_transf1_sound with transf_hints.
    Qed.
  End Example1.

  Section Example2.
    Definition sum_agg_attr2 := "price".

    Notation sum_agg_wf2 := (SumAgg.idx_wf "hole" sum_agg_attr2 "x").
    Instance csum_agg2 : IndexInterface2.index := (sum_agg "hole" sum_agg_attr2 "x").
    Instance csum_agg_ok2 : IndexInterface2.ok csum_agg2 sum_agg_wf2.
    apply sum_agg_ok.
    Qed.

    Definition dict_idx_attr2 := "color".

    Notation dict_idx_wf2 := (DictIndexImpl2.idx_wf "hole" dict_idx_attr2 "tup" "acc" "x").
    Instance cdict_idx2 : IndexInterface2.index := (dict_idx "hole" dict_idx_attr2 "tup" "acc" "x").
    Instance cdict_idx_ok2 : IndexInterface2.ok cdict_idx2 dict_idx_wf2.
    apply dict_idx_ok. auto with transf_hints.
    Qed.

    Definition sum_agg_lookup_transf2 := fun tbl => fold_command_with_globals [tbl] (sum_to_agg_lookup_head sum_agg_attr2 "id_tag" "aux_tag" "sum_agg_tag" tbl).
    Definition cons_to_add_transf2 := fun tbl => fold_command_with_globals [tbl] (cons_to_add_head).
    Definition dict_lookup_transf2 := fun tbl => fold_command_with_globals [tbl] (eq_filter_to_lookup_head dict_idx_attr2 "id_tag" "aux_tag" "dict_idx_tag" "b" tbl).
    Definition cons_to_insert_transf2 := fun tbl => fold_command_with_globals [tbl] (cons_to_insert_head dict_idx_attr2 "tup" "acc" "x" "y").
    Definition use_dict_idx_transf2 := fun tbl => fold_command_with_globals [tbl] (use_idx_head dict_idx_attr2 "id_tag" "aux_tag" "dict_idx_tag" tbl).

    Notation idxs2 := [("sum_agg_tag", csum_agg2, sum_agg_wf2);
                       ("dict_idx_tag", cdict_idx2, dict_idx_wf2)].
    Instance ccompo_idx2 : IndexInterface2.index := compo_idx idxs2 "hole" (word:=word).
    Instance ccompo_idx_ok2 : IndexInterface2.ok ccompo_idx2 (compo_idx_wf idxs2).
    apply compo_idx_ok; repeat constructor; intros; auto with transf_hints.
    all: cbn; rewrite <- eqb_eq; intuition idtac; discriminate.
    Qed.

    Definition ex_transf2 (Gstore Genv : ctenv) :=
      Basics.compose
        (apply_idx_related_transfs (idx:=ccompo_idx2) "id_tag" "aux_tag"
           (fun tbl =>
              (Basics.compose (dict_lookup_transf2 tbl)
                 (Basics.compose (use_dict_idx_transf2 tbl)
                    (Basics.compose (repeat_transf (cons_to_insert_transf2 tbl) 10000)
                       (Basics.compose (sum_agg_lookup_transf2 tbl)
                          (Basics.compose (repeat_transf (cons_to_add_transf2 tbl) 10000)
                             (cons_to_add_transf2 tbl))))))) Gstore Genv)
        (Basics.compose push_down_collection_transf
           (Basics.compose push_down_collection_transf
              (Basics.compose annotate_collection_transf
                 (Basics.compose to_filter_transf to_proj_transf)))).

    Lemma ex_transf2_sound : transf_sound (locals:=clocals) ex_transf2.
    Proof.
      repeat (repeat apply_transf_sound_lemmas; eauto 10 with transf_hints).
    Qed.

    Definition outfits_row_ty := TRecord (record_sort [("outfit_name", TString); ("shirt_name", TString); ("shirt_color", TString); ("shirt_price", TInt); ("pants_name", TString); ("pants_color", TString); ("pants_price", TInt)]).

    Definition shirts_row_ty := TRecord (record_sort [("name", TString); ("color", TString); ("price", TInt)]).

    Definition populate_shirts_from_outfits : command :=
      CForeach (EFlatmap LikeList (ELoc "outfits") "row"
                  (EBinop OCons
                     (ERecord [("name", EAccess (EVar "row") "shirt_name"); ("color", EAccess (EVar "row") "shirt_color"); ("price", EAccess (EVar "row") "shirt_price")])
                     (EAtom (ANil (Some shirts_row_ty)))))
        "row" (CAssign "shirts" (EBinop OCons (EVar "row") (ELoc "shirts"))).

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
      CLetMut (EFold (<["row" <- mut "shirts" ; ret "row"["price"]]>) (EAtom (AInt 0)) "v" "acc" (EBinop OPlus (EVar "v") (EVar "acc"))) "total_shirt_price" CSkip.

    Definition ex2 := CLetMut (EAtom (ANil (Some (shirts_row_ty)))) "shirts"
                        (CSeq populate_shirts_from_outfits
                           (CSeq query2_1 query2_2)).

    Definition init_Gstore2 : ctenv := map.put map.empty "outfits" (TList outfits_row_ty).
    Definition init_Genv2 : ctenv := map.empty.

    (* Compute typecheck init_Gstore2 init_Genv2 ex2. *)

    Definition ex2_transformed := ex_transf2 init_Gstore2 init_Genv2 ex2.
    (* Compute ex2_transformed. *)

    Theorem ex2_transformed_sem : forall (store env : clocals),
        locals_wf init_Gstore2 store ->
        locals_wf init_Genv2 env ->
        interp_command store env ex2_transformed = interp_command store env ex2.
    Proof.
      apply transf_sound__preserve_sem; auto using ex_transf2_sound with transf_hints.
    Qed.
  End Example2.
End WithConcreteMaps.

Print Assumptions ex1_transformed.
Print Assumptions ex2_transformed.
