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

    Definition sum_agg_wf := (SumAgg.idx_wf (locals:=clocals) "hole" sum_agg_attr "x").
    Instance csum_agg : IndexInterface.index := (sum_agg "hole" sum_agg_attr "x").
    Instance csum_agg_ok : IndexInterface.ok csum_agg sum_agg_wf.
    apply sum_agg_ok.
    Qed.

    Definition sum_agg_lookup_transf := fun tbl => fold_command_with_globals [tbl] (sum_to_agg_lookup_head sum_agg_attr "id_tag" "aux_tag" "sum_agg_tag" tbl).
    Definition cons_to_add_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_add_head).

    Context (min_agg_attr : string).

    Definition min_agg_wf := (MinAgg.idx_wf (locals:=clocals) "hole" min_agg_attr "x").
    Instance cmin_agg : IndexInterface.index := (min_agg "hole" min_agg_attr "x").
    Instance cmin_agg_ok : IndexInterface.ok cmin_agg min_agg_wf.
    apply min_agg_ok.
    Qed.

    Definition min_agg_lookup_transf := fun tbl => fold_command_with_globals [tbl] (min_to_agg_lookup_head min_agg_attr "id_tag" "aux_tag" "min_agg_tag" tbl).
    Definition cons_to_min_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_min_head "y").

    Context (dict_idx_attr : string).

    Definition dict_idx_wf := (DictIndexImpl.idx_wf (width:=width) "hole" dict_idx_attr "tup" "acc" "x").
    Instance cdict_idx : IndexInterface.index := (dict_idx "hole" dict_idx_attr "tup" "acc" "x").
    Instance cdict_idx_ok : IndexInterface.ok cdict_idx dict_idx_wf.
    apply dict_idx_ok. auto with transf_hints.
    Qed.

    Definition dict_lookup_transf := fun tbl => fold_command_with_globals [tbl] (eq_filter_to_lookup_head dict_idx_attr "id_tag" "aux_tag" "dict_idx_tag" "b" tbl).
    Definition cons_to_insert_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_insert_head dict_idx_attr "tup" "acc" "x" "y").
    Definition use_dict_idx_transf := fun tbl => fold_command_with_globals [tbl] (use_idx_head dict_idx_attr "id_tag" "aux_tag" "dict_idx_tag" tbl).

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
    Definition use_pk_idx_transf := fun tbl => fold_command_with_globals [tbl] (use_pk_idx_head "id_tag" "aux_tag" "pk_idx_tag" tbl).
    Definition cons_to_bitmap_update_transf := fun tbl => fold_command_with_globals [tbl] cons_to_bitmap_update_head.
    Definition use_bitmap_transf := fun tbl => fold_command_with_globals [tbl] (use_bitmap_head bitmap_attr bitmap_str "id_tag" "aux_tag" "bm_tag" tbl).
    Definition filter_to_bitmap_lookup_transf :=
      fun tbl => fold_command_with_globals [tbl]
                   (filter_to_bitmap_lookup_head bitmap_attr bitmap_str "id_tag" "aux_tag" "pk_idx_tag" "bm_tag" "x" "b" "acc" tbl).
  End CommonPipelineParts.

  Section ParameterizedPipeline.
    Context (sum_agg_attr : option string).
    Context (min_agg_attr : option string).
    Context (dict_idx_attr : option string).
    Context (bitmap_params : option (string * string)).

    Definition to_proj_transf := fold_command id to_proj_head.
    Definition to_filter_transf := fold_command id to_filter_head.
    Definition to_join_transf := fold_command id to_join_head.
    Definition annotate_collection_transf := fold_command id annotate_collection.
    Definition push_down_collection_transf := fold_command id push_down_collection.
    Definition filter_pushdown_transf := fold_command id filter_pushdown_head.

    Notation idxs :=
      (match sum_agg_attr with
       | None => []
       | Some sum_agg_attr =>
           [("sum_agg_tag", csum_agg sum_agg_attr, sum_agg_wf sum_agg_attr)]
       end ++
         match min_agg_attr with
         | None => []
         | Some min_agg_attr =>
             [("min_agg_tag", cmin_agg min_agg_attr, min_agg_wf min_agg_attr)]
         end ++
         match dict_idx_attr with
         | None => []
         | Some dict_idx_attr =>
             [("dict_idx_tag", cdict_idx dict_idx_attr, dict_idx_wf dict_idx_attr)]
         end ++
         match bitmap_params with
         | None => []
         | Some (bitmap_attr, bitmap_str) =>
             [("pk_idx_tag", cpk_idx, pk_idx_wf);
              ("bm_tag", bitmap bitmap_attr bitmap_str, bitmap_wf bitmap_attr bitmap_str)]
         end)%list.

    Instance ccompo_idx : IndexInterface.index := compo_idx idxs "hole" (word:=word).
    Instance ccompo_idx_ok : IndexInterface.ok ccompo_idx (compo_idx_wf idxs).
    apply compo_idx_ok;
      repeat case_match;
      repeat constructor; intros; auto with transf_hints;
      cbn; rewrite <- eqb_eq; intuition idtac; discriminate.
    Qed.

    Definition ex_transf (Gstore Genv : ctenv) :=
      Basics.compose
        (apply_idx_related_transfs (idx:=ccompo_idx) "id_tag" "aux_tag"
           (fun tbl =>
              (Basics.compose
                 (match bitmap_params with
                  | Some (bitmap_attr, bitmap_str) =>
                      Basics.compose (filter_to_bitmap_lookup_transf bitmap_attr bitmap_str tbl)
                        (Basics.compose (use_bitmap_transf bitmap_attr bitmap_str tbl)
                           (Basics.compose (repeat_transf (cons_to_bitmap_update_transf tbl) 10000)
                              (Basics.compose (use_pk_idx_transf tbl) (repeat_transf (cons_to_pk_idx_update_transf tbl) 10000))))
                  | None => id
                  end)
                 (Basics.compose
                    match dict_idx_attr with
                    | Some dict_idx_attr =>
                        Basics.compose (dict_lookup_transf dict_idx_attr tbl)
                          (Basics.compose (use_dict_idx_transf dict_idx_attr tbl)
                             (repeat_transf (cons_to_insert_transf dict_idx_attr tbl) 10000))
                    | None => id
                    end
                    (Basics.compose
                       match min_agg_attr with
                       | Some min_agg_attr =>
                           Basics.compose (min_agg_lookup_transf min_agg_attr tbl)
                             (repeat_transf (cons_to_min_transf tbl) 10000)
                       | None => id
                       end
                       match sum_agg_attr with
                       | Some sum_agg_attr =>
                           Basics.compose (sum_agg_lookup_transf sum_agg_attr tbl)
                             (repeat_transf (cons_to_add_transf tbl) 10000)
                       | None => id
                       end)))) Gstore Genv)
           (Basics.compose push_down_collection_transf
              (Basics.compose annotate_collection_transf
                 (Basics.compose filter_pushdown_transf
                    (Basics.compose to_filter_transf
                       (Basics.compose to_proj_transf to_join_transf))))).

    Lemma id_aug_transf_sound : forall is_tbl_ty aux_ty (aux_wf : value -> Prop),
        aug_transf_sound is_tbl_ty aux_ty aux_wf (fun _ => id).
    Proof.
      unfold aug_transf_sound; cbn; auto.
    Qed.

    Lemma ex_transf_sound : transf_sound (locals:=clocals) ex_transf.
    Proof.
      unfold ex_transf.
      repeat case_match;
        repeat (repeat apply_transf_sound_lemmas; eauto 10 with transf_hints).
      all:
        try simple eapply id_aug_transf_sound;
        try simple eapply filter_to_bitmap_lookup_head_sound2;
        try simple eapply use_bitmap_head_sound;
        try simple eapply use_pk_idx_head_sound2;
        try simple eapply use_idx_head_sound2;
        try simple eapply min_to_agg_lookup_head_sound;
        try simple eapply sum_to_agg_lookup_head_sound;
        try simple eapply eq_filter_to_lookup_head_sound2;
        eauto with transf_hints;
        try (unfold aux_ty_for_idx, aux_ty; cbn;
             repeat rewrite_l_to_r;
             eauto with transf_hints);
        try (unfold compo_is_tbl_ty;
             unfold IndexInterface.is_tbl_ty; cbn; intros;
             rewrite !Bool.andb_true_iff in *; intuition idtac);
        try (intros; unfold aux_wf, aux_wf_for_idx, compo_idx_wf in *;
             repeat destruct_match_hyp; intuition idtac; cbn in *;
             repeat invert_Forall;
             case_match; intuition idtac;
             eauto with transf_hints);
        try use_is_NoDup.
    Qed.
  End ParameterizedPipeline.

  Section ExampleFilterPushdown.
    Definition row_ty1 := TRecord (record_sort [("A", TInt); ("B", TString)]).
    Definition row_ty2 := TRecord (record_sort [("B", TString); ("C", TInt)]).

    Definition ex_pushdown :=
      <[ "r1" <- "tbl1";
         "r2" <- "tbl2";
         check("r1"["A"] == 0 && "r1"["B"] == "r2"["B"]);
         ret {"B": "r1"["B"], "C": "r2"["C"]} ]>.

    Definition ex0 := CAssign "res" ex_pushdown.

    Definition init_Gstore0 : ctenv := map.put map.empty "res" (TList (TRecord ([("B", TString); ("C", TInt)]))).
    Definition init_Genv0 : ctenv := map.put (map.put map.empty "tbl1" (TList row_ty1)) "tbl2" (TList row_ty2).

    Definition ex_transf_pushdown := ex_transf None None None None.
    Definition ex0_transformed := ex_transf_pushdown init_Gstore0 init_Genv0 ex0.
    (* Compute (typecheck init_Gstore0 init_Genv0 ex0). *)
    (* Compute ex0_transformed. *)

    Theorem ex0_transformed_sem : forall (store env : clocals),
        locals_wf init_Gstore0 store ->
        locals_wf init_Genv0 env ->
        interp_command store env ex0_transformed = interp_command store env ex0.
    Proof.
      apply transf_sound__preserve_sem; eauto using ex_transf_sound with transf_hints.
    Qed.
  End ExampleFilterPushdown.


  Section Example1.
    Definition sum_agg_attr1 := "salary".
    Definition dict_idx_attr1 := "department".
    Definition bitmap_attr1 := "location".
    Definition bitmap_str1 := "A".

    Definition ex_transf1 := ex_transf (Some sum_agg_attr1) None (Some dict_idx_attr1) (Some (bitmap_attr1, bitmap_str1)).

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

    Definition ex1_transformed := ex_transf1 init_Gstore1 init_Genv1 ex1.
    (* Compute typecheck init_Gstore1 init_Genv1 ex1. *)
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
    Definition attr2 := "department-id".

    Definition row_ty2_1 := TRecord (record_sort [("department-id", TInt); ("department-name", TString)]).
    Definition row_ty2_2 := TRecord (record_sort [("name", TString); ("department-id", TInt); ("feedback", TString)]).

    Definition join_tables : expr := ESort LikeList <[
          "r1" <- mut "departments" ;
          "r3" <- ("r2" <- mut "responses" ;
                   check("r2"["department-id"] == "r1"["department-id"]);
                   ret "r2") ;
          ret {"name" : "r3" ["name"],
                "department" : "r1" ["department-name"],
                  "feedback" : "r3" ["feedback"]} ]>.

    Definition ex2 := CLetMut (EVar "res_tbl") "responses"
                        (CLetMut (EVar "dpt_tbl") "departments"
                           (CForeach join_tables "r"
                            <{ let "name" = "r"["name"] +++ << EAtom (AString " from ") >> in
                               let "dep" = "r"["department"] +++ << EAtom (AString " wrote: ") >> in
                               let "feedback" = "r"["feedback"] +++ << EAtom (AString "\n") >> in
                               let "line" = "name" +++ "dep" +++ "feedback" in
                               set "all_feedback" := mut "all_feedback" +++ "line" }>)).

    Definition init_Gstore2 : ctenv := map.put map.empty "all_feedback" TString.
    Definition init_Genv2 : ctenv := map.put (map.put map.empty "res_tbl" (TList row_ty2_2)) "dpt_tbl" (TList row_ty2_1).


    Definition ex_transf2 := ex_transf None None (Some attr2) None.
    Definition ex2_transformed := ex_transf2 init_Gstore2 init_Genv2 ex2.
    (* Compute (typecheck init_Gstore1 init_Genv1 ex1). *)
    (* Compute ex2_transformed. *)

    Theorem ex2_transformed_sem : forall (store env : clocals),
        locals_wf init_Gstore2 store ->
        locals_wf init_Genv2 env ->
        interp_command store env ex2_transformed = interp_command store env ex2.
    Proof.
      apply transf_sound__preserve_sem; eauto using ex_transf_sound with transf_hints.
    Qed.
  End Example2.

  Section Example3.
    Definition sum_agg_attr3 := "price".
    Definition min_agg_attr3 := "price".
    Definition dict_idx_attr3 := "color".
    Definition bitmap_attr3 := "name".
    Definition bitmap_str3 := "shirt_1".

    Definition ex_transf3 := ex_transf (Some sum_agg_attr3) (Some min_agg_attr3) (Some dict_idx_attr3) (Some (bitmap_attr3, bitmap_str3)).

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

    Definition query3_1 :=
      CLetMut (EAtom (AString ""))  "white_shirt_info"
        (CForeach (filter_shirts "white") "r"
          <{ let "n" = "r"["name"] +++ << EAtom (AString ": ") >> in
            let "p" = << EUnop OIntToString (EAccess (EVar "r") "price") >> +++ << EAtom (AString "\n") >> in
            let "line" = "n" +++ "p" in
            set "white_shirt_info" := mut "white_shirt_info" +++ "line" }>).

    Definition query3_2 :=
      CAssign "total_shirt_price" (EFold (<["row" <- mut "shirts" ; ret "row"["price"]]>) (EAtom (AInt 0)) "v" "acc" (EBinop OPlus (EVar "v") (EVar "acc"))).

    Definition query3_3 :=
      CAssign "min_shirt_price"
        (EFold (<["row" <- mut "shirts" ; ret "row"["price"]]>) (EAtom (ANone (Some TInt))) "v" "acc"
           (EOptMatch (EVar "acc") (EUnop OSome (EVar "v"))
              "x" (EIf (EBinop OLess (EVar "v") (EVar "x")) (EUnop OSome (EVar "v")) (EVar "acc")))).

    Definition ex3 := CLetMut (EAtom (ANil (Some (shirts_row_ty)))) "shirts"
                        (CSeq populate_shirts_from_outfits
                           (CSeq query3_1
                              (CSeq query3_2 query3_3))).

    Definition init_Gstore3 : ctenv := map.put (map.put (map.put map.empty "outfits" (TList outfits_row_ty)) "total_shirt_price" TInt) "min_shirt_price" (TOption TInt).
    Definition init_Genv3 : ctenv := map.empty.

    Definition ex3_transformed := ex_transf3 init_Gstore3 init_Genv3 ex3.
    (* Compute typecheck init_Gstore3 init_Genv3 ex3. *)
    (* Compute ex3_transformed. *)

    Theorem ex3_transformed_sem : forall (store env : clocals),
        locals_wf init_Gstore3 store ->
        locals_wf init_Genv3 env ->
        interp_command store env ex3_transformed = interp_command store env ex3.
    Proof.
      apply transf_sound__preserve_sem; eauto using ex_transf_sound with transf_hints.
    Qed.
  End Example3.
End WithConcreteMaps.

Print Assumptions ex0_transformed.
Print Assumptions ex1_transformed.
Print Assumptions ex2_transformed.
Print Assumptions ex3_transformed.
