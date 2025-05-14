Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface
fiat2.CollectionTag fiat2.DictIndexImpl fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf fiat2.TransfSound fiat2.Utils fiat2.Substitute.
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

  Instance caenv : map.map string collection_tag := SortedListString.map _.
  Instance caenv_ok : map.ok caenv := SortedListString.ok _.

  Instance cRenv : map.map string (value -> value -> Prop) := SortedListString.map _.
  Instance cRenv_ok : map.ok cRenv := SortedListString.ok _.

  Definition attr := "department".

  Notation idx_wf := (idx_wf attr).
  Instance cdict_idx : IndexInterface.index := (dict_idx "hole" attr "tup" "acc" "x" "k" "v").
  Instance cdict_idx_ok : IndexInterface.ok LikeBag LikeList cdict_idx idx_wf consistent.
    apply dict_idx_ok. auto with transf_hints.
  Qed.

  Definition to_filter_transf := fold_command id to_filter_head.
  Definition lookup_transf := fun tbl => fold_command_with_globals [tbl] (eq_filter_to_lookup_head attr "p" tbl).
  Definition delete_transf := fun tbl => fold_command_with_globals [tbl] (neq_filter_to_delete_head attr tbl).
  Definition ex_transf (Gstore Genv : ctenv) :=
    Basics.compose (apply_idx_related_transfs (to_from_con:=LikeBag) (fun tbl => Basics.compose (lookup_transf tbl) (Basics.compose (delete_transf tbl) (lookup_transf tbl))) Gstore Genv) to_filter_transf.

  Lemma ex_transf_sound : transf_sound (locals:=clocals) ex_transf.
  Proof.
    eauto 20 with transf_hints.
  Qed.

  Require Import fiat2.Notations.
  Open Scope fiat2_scope.

  Definition row_ty := TRecord (record_sort [("name", TString); ("department", TString); ("feedback", TString)]).
  (* two arbitrary well_typed rows *)
  Definition row1 := EVar "row1".
  Definition row2 := EVar "row2".

  Definition build_responses1 := <{ set "responses" := row1 :: row2 :: mut "responses" }>.
  Definition remove_NA := <{ set "responses" :=
                             "row" <- mut "responses" ;
                             check(!("row"["department"] == << EAtom (AString "NA") >>)) ;
                             ret "row" }>.
  Definition filter_responses dpt : expr := ESort <[ "row" <- mut "responses" ;
                                                       check("row"["department"] == << EAtom (AString dpt) >>);
                                                       ret "row" ]>.
  Definition query := CSeq remove_NA
                        (CForeach (filter_responses "EECS") "r"
                         <{ let "name" = "r"["name"] +++ << EAtom (AString ": ") >> in
                            let "feedback" = "r"["feedback"] +++ << EAtom (AString "\n") >> in
                            let "line" = "name" +++ "feedback" in
                            set "all_feedback" := mut "all_feedback" +++ "line" }>).
  Definition ex1' := CSeq build_responses1 query.
  Definition ex1 := CLetMut (EAtom (ANil (Some (row_ty)))) "responses" ex1'.

  Definition init_Gstore : ctenv := map.put map.empty "all_feedback" TString.
  Definition init_Genv : ctenv := map.put (map.put map.empty "row1" row_ty) "row2" row_ty.

  (*
  Compute typecheck (map.put map.empty "all_feedback" TString) init_Genv ex1.
  Compute can_transf_to_index LikeBag (TList row_ty) (map.put map.empty "all_feedback" LikeList) ex1.
  Compute command_tag_req_times (fun istr => command_tag_req istr query) (map.put map.empty "all_feedback" LikeList) 1.

  Compute ex1.
  Definition ex1_to_filter := fold_command id to_filter_head ex1.
  Compute typecheck (map.put map.empty "all_feedback" TString) init_Genv ex1_to_filter.
  Compute can_transf_to_index LikeBag (TList row_ty) (map.put map.empty "all_feedback" LikeList) ex1_to_filter.
  Compute ex1_to_filter.

  Definition ex1_to_idx := transf_to_idx (get_free_vars init_Genv) ex1_to_filter.
  Compute ex1_to_idx.

  Definition ex1_lookup := apply_after_letmut (fun tbl => fold_command_with_globals [tbl] (eq_filter_to_lookup_head attr "p" tbl)) ex1_to_idx.
  Compute ex1_lookup.

Definition ex1_delete := apply_after_letmut (fun tbl => fold_command_with_globals [tbl] (neq_filter_to_delete_head attr tbl)) ex1_lookup.
  Compute ex1_delete.
   *)

  Definition ex1_transformed := ex_transf init_Gstore init_Genv ex1.


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
    eauto using transf_sound__preserve_sem, ex_transf_sound.
  Qed.
End ConcreteExample.
