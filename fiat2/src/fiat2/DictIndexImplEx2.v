Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface2
fiat2.CollectionTransf fiat2.DictIndexImpl2 fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf2 fiat2.TransfSound fiat2.Utils fiat2.Substitute.
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

  Definition attr := "department".

  Notation idx_wf := (idx_wf "hole" attr "tup" "acc" "x").
  Instance cdict_idx : IndexInterface2.index := (dict_idx "hole" attr "tup" "acc" "x").
  Instance cdict_idx_ok : IndexInterface2.ok cdict_idx idx_wf.
  apply dict_idx_ok. auto with transf_hints.
  Qed.

  Definition to_filter_transf := fold_command id to_filter_head.
  Definition annotate_collection_transf := fold_command id annotate_collection.
  Definition push_down_collection_transf := fold_command id push_down_collection.
  Definition lookup_transf := fun tbl => fold_command_with_globals [tbl] (eq_filter_to_lookup_head attr "id_tag" "aux_tag" "dict_idx_tag" "b" tbl).
  Definition cons_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_insert_head attr "tup" "acc" "x" "y").
  Definition use_dict_idx_transf := fun tbl => fold_command_with_globals [tbl] (use_idx_head attr "id_tag" "aux_tag" "dict_idx_tag" tbl).

  Notation idxs := [("dict_idx_tag", cdict_idx, idx_wf)].
  Instance ccompo_idx : IndexInterface2.index := compo_idx idxs "hole" (word:=word).
  Instance ccompo_idx_ok : IndexInterface2.ok ccompo_idx (compo_idx_wf idxs).
  apply compo_idx_ok; repeat constructor; auto; intros.
  1: apply idx_ty_wf; auto.
  1: apply to_idx_ty; auto with transf_hints.
  Qed.

  Definition ex_transf (Gstore Genv : ctenv) :=
    Basics.compose (apply_idx_related_transfs (idx:=ccompo_idx) "id_tag" "aux_tag" (fun tbl => Basics.compose (use_dict_idx_transf tbl) (Basics.compose (cons_transf tbl) (Basics.compose (cons_transf tbl) (lookup_transf tbl)))) Gstore Genv) (Basics.compose push_down_collection_transf (Basics.compose annotate_collection_transf to_filter_transf)).

  Lemma ex_transf_sound : transf_sound (locals:=clocals) ex_transf.
  Proof.
    repeat (repeat apply_transf_sound_lemmas; eauto 8 with transf_hints).
  Qed.

  Require Import fiat2.Notations.
  Open Scope fiat2_scope.

  Definition row_ty := TRecord (record_sort [("name", TString); ("department", TString); ("feedback", TString)]).
  (* two arbitrary well_typed rows *)
  Definition row1 := EVar "row1".
  Definition row2 := EVar "row2".

  Definition build_responses1 := <{ set "responses" := row1 :: row2 :: mut "responses" }>.
  Definition filter_responses dpt : expr := ESort LikeList <[ "row" <- mut "responses" ;
                                                       check("row"["department"] == << EAtom (AString dpt) >>);
                                                       ret "row" ]>.
  Definition query := CForeach (filter_responses "EECS") "r"
                      <{ let "name" = "r"["name"] +++ << EAtom (AString ": ") >> in
                         let "feedback" = "r"["feedback"] +++ << EAtom (AString "\n") >> in
                         let "line" = "name" +++ "feedback" in
                         set "all_feedback" := mut "all_feedback" +++ "line" }>.
  Definition ex1' := CSeq build_responses1 query.
  Definition ex1 := CLetMut (EAtom (ANil (Some (row_ty)))) "responses" ex1'.

  Definition init_Gstore : ctenv := map.put map.empty "all_feedback" TString.
  Definition init_Genv : ctenv := map.put (map.put map.empty "row1" row_ty) "row2" row_ty.

  Unset Printing Notations.
  Definition ex1_transformed := ex_transf init_Gstore init_Genv ex1.
  Compute ex1_transformed.

  Theorem ex1_transformed_sem : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      interp_command store env ex1_transformed = interp_command store env ex1.
  Proof.
    eauto using transf_sound__preserve_sem, ex_transf_sound.
  Qed.
End ConcreteExample.

Print Assumptions ex1_transformed_sem.
