Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.IndexInterface
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

  Instance caenv : map.map string collection_tag := SortedListString.map _.
  Instance caenv_ok : map.ok caenv := SortedListString.ok _.

  Instance cRenv : map.map string (value -> value -> Prop) := SortedListString.map _.
  Instance cRenv_ok : map.ok cRenv := SortedListString.ok _.

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

  Hint Extern 5 ((_ : string) <> _) => apply eqb_neq; auto : transf_hints.
  Hint Resolve push_down_collection_sound : transf_hints.
  Hint Resolve annotate_collection_sound : transf_hints.
  Hint Resolve use_idx_head_sound : transf_hints.
  Hint Extern 5 (forall v, aux_wf _ _ v -> DictIndexImpl2.aux_wf_for_idx _ _ _ _ _ _ _ _ v) =>
              intros; unfold aux_wf, aux_wf_for_idx, compo_idx_wf in *;
              repeat destruct_match_hyp; intuition idtac;
              invert_Forall; unfold idx_wf, record_proj in *;
                             destruct_match_hyp; intuition eauto : transf_hints.
  Hint Extern 5 (aux_ty_for_idx _ _ _ _ _) => unfold aux_ty_for_idx, aux_ty; cbn; auto : transf_hints.
  Hint Extern 5 (forall t, IndexInterface2.is_tbl_ty t = true -> _ = true) =>
         unfold IndexInterface2.is_tbl_ty; cbn; intros;
  rewrite Bool.andb_true_iff in *; intuition auto : transf_hints.
  Hint Extern 5 string => pose proof ("":string). (* ??? : transf_hints doesn't work; how to find the cause of this extra arg? *)
  Hint Resolve cons_to_insert_head_sound : transf_hints.
  Hint Extern 5 (expr_aug_transf_sound _ _ _ (DictIndexImpl2.use_idx_head _ _ _ _)) =>
         eapply use_idx_head_sound; [ | | | | | | eauto with transf_hints ]; auto with transf_hints : transf_hints.
  Hint Extern 5 (expr_aug_transf_sound _ _ _ (DictIndexImpl2.eq_filter_to_lookup_head _ _ _ _ _)) =>
         eapply eq_filter_to_lookup_head_sound; [ | | | | | | eauto with transf_hints ]; auto with transf_hints : transf_hints.
  Hint Extern 5 (transf_sound (apply_idx_related_transfs _ _ _)) => apply apply_idx_related_transfs_sound : transf_hints.
  Hint Extern 5 (@transf_sound width word ctenv clocals ex_transf) => apply transf_sound_compose : transf_hints. (* ??? Doesn't work *)

  Lemma ex_transf_sound : transf_sound (locals:=clocals) ex_transf.
  Proof.
    apply transf_sound_compose; eauto 20 with transf_hints.
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

  Definition ex1_1 := (Basics.compose push_down_collection_transf (Basics.compose annotate_collection_transf to_filter_transf)) ex1.
  Compute ex1_1.
  Compute apply_idx_related_transfs (idx:=ccompo_idx) "id_tag" "aux_tag" (fun tbl => Basics.compose (cons_transf tbl) (lookup_transf tbl)) init_Gstore init_Genv ex1_1.

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
    eauto using transf_sound__preserve_sem, ex_transf_sound.
  Qed.
End ConcreteExample.
