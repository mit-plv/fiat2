Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface
fiat2.CollectionTransf fiat2.SumAgg fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf fiat2.TransfSound fiat2.Utils fiat2.Substitute.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
Require Import List String ZArith.
Import ListNotations.

Require Import fiat2.Notations.
Open Scope fiat2_scope.

Section ConcreteExample.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Instance caenv : map.map string collection_tag := SortedListString.map _.
  Instance caenv_ok : map.ok caenv := SortedListString.ok _.

  Instance cRenv : map.map string (value -> value -> Prop) := SortedListString.map _.
  Instance cRenv_ok : map.ok cRenv := SortedListString.ok _.

  Definition attr := "salary".

  Notation idx_wf := (idx_wf "hole" attr "x").
  Instance csum_agg : IndexInterface.index := (sum_agg "hole" attr "x").
  Instance csum_agg_ok : IndexInterface.ok csum_agg idx_wf.
  apply sum_agg_ok.
  Qed.

  Definition to_proj_transf := fold_command id to_proj_head.
  Definition annotate_collection_transf := fold_command id annotate_collection.
  Definition push_down_collection_transf := fold_command id push_down_collection.
  Definition lookup_transf := fun tbl => fold_command_with_globals [tbl] (sum_to_agg_lookup_head attr "id_tag" "aux_tag" "sum_agg_tag" tbl).
  Definition cons_transf := fun tbl => fold_command_with_globals [tbl] (cons_to_add_head).

  Notation idxs := [("sum_agg_tag", csum_agg, idx_wf)].
  Instance ccompo_idx : IndexInterface.index := compo_idx idxs "hole" (word:=word).
  Instance ccompo_idx_ok : IndexInterface.ok ccompo_idx (compo_idx_wf idxs).
  apply compo_idx_ok; repeat constructor; auto; intros.
  apply to_idx_ty; auto with transf_hints.
  Qed.

  Definition ex_transf (Gstore Genv : ctenv) :=
    Basics.compose (apply_idx_related_transfs (idx:=ccompo_idx) "id_tag" "aux_tag"
                      (fun tbl => Basics.compose (lookup_transf tbl)
                                    (Basics.compose (cons_transf tbl)
                                       (cons_transf tbl))) Gstore Genv)
                      (Basics.compose push_down_collection_transf
                         (Basics.compose push_down_collection_transf
                            (Basics.compose annotate_collection_transf to_proj_transf))).

  Lemma ex_transf_sound : transf_sound (locals:=clocals) ex_transf.
  Proof.
    repeat (apply_transf_sound_lemmas; eauto with transf_hints).
  Qed.

  Definition row_ty := TRecord (record_sort [("name", TString); ("department", TString); ("feedback", TString); ("salary", TInt)]).
  (* two arbitrary well_typed rows *)
  Definition row1 := EVar "row1".
  Definition row2 := EVar "row2".

  Definition build_responses1 := <{ set "responses" := row1 :: row2 :: mut "responses" }>.
  Definition query := CAssign "sum" (EFold (<["row" <- mut "responses" ; ret "row"["salary"]]>) (EAtom (AInt 0)) "v" "acc" (EBinop OPlus (EVar "v") (EVar "acc"))).
  Definition ex1' := CSeq build_responses1 query.
  Definition ex1 := CLetMut (EAtom (ANil (Some (row_ty)))) "responses" ex1'.

  Definition init_Gstore : ctenv := map.put map.empty "sum" TInt.
  Definition init_Genv : ctenv := map.put (map.put map.empty "row1" row_ty) "row2" row_ty.

  Definition ex1_transformed := ex_transf init_Gstore init_Genv ex1.
  (* Compute ex1_transformed. *)

  Theorem ex1_transformed_sem : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      interp_command store env ex1_transformed = interp_command store env ex1.
  Proof.
    eauto using transf_sound__preserve_sem, ex_transf_sound with transf_hints.
  Qed.
End ConcreteExample.

Print Assumptions ex1_transformed_sem.
