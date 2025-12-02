Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface
fiat2.CollectionTransf fiat2.DictIndexImpl fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf fiat2.TransfSound fiat2.Utils fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.
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
    Context (attr : string).

    Notation idx_wf := (idx_wf "hole" attr "tup" "acc" "x").
    Instance cdict_idx : IndexInterface.index := (dict_idx "hole" attr "tup" "acc" "x").
    Instance cdict_idx_ok : IndexInterface.ok cdict_idx idx_wf.
    apply dict_idx_ok. auto with transf_hints.
    Qed.

    Definition to_filter_transf := fold_command id to_filter_head.
    Definition to_proj_transf := fold_command id to_proj_head.
    Definition annotate_collection_transf := fold_command id annotate_collection.
    Definition push_down_collection_transf := fold_command id push_down_collection.
    Definition lookup_transf := fun tbl => fold_command_with_globals [tbl] (eq_filter_to_lookup_head attr "id_tag" "aux_tag" "dict_idx_tag" "b" tbl).
    Definition cons_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_insert_head attr "tup" "acc" "x" "y").
    Definition use_dict_idx_transf := fun tbl => fold_command_with_globals [tbl] (use_idx_head attr "id_tag" "aux_tag" "dict_idx_tag" tbl).

    Notation idxs := [("dict_idx_tag", cdict_idx, idx_wf)].
    Instance ccompo_idx : IndexInterface.index := compo_idx idxs "hole" (word:=word).
    Instance ccompo_idx_ok : IndexInterface.ok ccompo_idx (compo_idx_wf idxs).
    apply compo_idx_ok; repeat constructor; auto; intros.
    1: apply idx_ty_wf; auto.
    1: apply to_idx_ty; auto with transf_hints.
    Qed.

    Definition ex_transf (Gstore Genv : ctenv) :=
      Basics.compose (apply_idx_related_transfs (idx:=ccompo_idx) "id_tag" "aux_tag" (fun tbl => Basics.compose (use_dict_idx_transf tbl) (Basics.compose (repeat_transf (cons_transf tbl) 1000) (lookup_transf tbl))) Gstore Genv) (Basics.compose push_down_collection_transf (Basics.compose annotate_collection_transf (Basics.compose to_filter_transf to_proj_transf))).

    Lemma ex_transf_sound : transf_sound (locals:=clocals) ex_transf.
    Proof.
      repeat (repeat apply_transf_sound_lemmas; eauto 8 with transf_hints).
    Qed.
  End CommonPipelineParts.

  Section ConcreteExample1.
    Definition attr1 := "department".

    Definition ex_transf1 := ex_transf attr1.

    Definition row_ty := TRecord (record_sort [("name", TString); ("department", TString); ("feedback", TString)]).
    (* two arbitrary well_typed rows *)
    Definition row1 := EVar "row1".
    Definition row2 := EVar "row2".

    Definition build_responses1 := <{ set "responses" := row1 :: row2 :: mut "responses" }>.
    Definition filter_responses dpt : expr := ESort LikeList <[ "row" <- mut "responses" ;
                                                                check("row"["department"] == << EAtom (AString dpt) >>);
                                                                ret "row" ]>.
    Definition query := CForeach (filter_responses "CS") "r"
                        <{ let "name" = "r"["name"] +++ << EAtom (AString ": ") >> in
                           let "feedback" = "r"["feedback"] +++ << EAtom (AString "\n") >> in
                           let "line" = "name" +++ "feedback" in
                           set "all_feedback" := mut "all_feedback" +++ "line" }>.
    Definition ex1' := CSeq build_responses1 query.
    Definition ex1 := CLetMut (EAtom (ANil (Some (row_ty)))) "responses" ex1'.

    Definition init_Gstore1 : ctenv := map.put map.empty "all_feedback" TString.
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
  End ConcreteExample1.

  Section ConcreteExample2.
    Definition attr2 := "department-id".

    Definition row_ty1 := TRecord (record_sort [("department-id", TInt); ("department-name", TString)]).
    Definition row_ty2 := TRecord (record_sort [("name", TString); ("department-id", TInt); ("feedback", TString)]).

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
    Definition init_Genv2 : ctenv := map.put (map.put map.empty "res_tbl" (TList row_ty2)) "dpt_tbl" (TList row_ty1).


    Definition ex_transf2 := ex_transf attr2.
    Definition ex2_transformed := ex_transf2 init_Gstore2 init_Genv2 ex2.
    (* Compute (typecheck init_Gstore2 init_Genv2 ex2). *)
    (* Compute ex2_transformed. *)

    Theorem ex2_transformed_sem : forall (store env : clocals),
        locals_wf init_Gstore2 store ->
        locals_wf init_Genv2 env ->
        interp_command store env ex2_transformed = interp_command store env ex2.
    Proof.
      apply transf_sound__preserve_sem; eauto using ex_transf_sound with transf_hints.
    Qed.
  End ConcreteExample2.
End WithConcreteMaps.

Print Assumptions ex1_transformed_sem.
Print Assumptions ex2_transformed_sem.
