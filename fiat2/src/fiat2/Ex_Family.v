Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.SumAgg fiat2.MinAgg fiat2.BitmapIndex fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.OptimizeAnno fiat2.ToPython.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.

Import ListNotations.

(*
(* Conjunction separation, filter pushdown across join *)

let mut parents := parents_tbl in

foreach person in queries do
    let mut result := "Grandchildren of " ++ person ++ ":\n" in
    let children =
        sort
            [ p <- !parents,
            q <- !parents,
            check(p.parent = person && q.parent = p.child),
            ret q.child ] in
    foreach child in children do
        result := !result ++ child ++ "\n"
    end;
    outputs := !result :: !outputs
end
*)

Definition prog := (CLetMut (EVar "parents_tbl") "parents" (CForeach (EVar "queries") "person" (CLetMut (EBinop OConcatString (EAtom (AString "Grandchildren of ")) (EBinop OConcatString (EVar "person") (EAtom (AString ":\n")))) "result" (CLet (ESort LikeList (EFlatmap LikeList (ELoc "parents") "p" (EFlatmap LikeList (ELoc "parents") "q" (EIf (EBinop OAnd (EBinop OEq (EAccess (EVar "p") "parent") (EVar "person")) (EBinop OEq (EAccess (EVar "q") "parent") (EAccess (EVar "p") "child"))) (EBinop OCons (EAccess (EVar "q") "child") (EAtom (ANil None))) (EAtom (ANil None)))))) "children" (CSeq (CForeach (EVar "children") "child" (CAssign "result" (EBinop OConcatString (ELoc "result") (EBinop OConcatString (EVar "child") (EAtom (AString "\n")))))) (CAssign "outputs" (EBinop OCons (ELoc "result") (ELoc "outputs")))))))).

Definition heuristics :=
  [
    AC
      [PushdownCollection; AnnotateCollection; JoinToFlatmapFilter; FilterPushdown; ToJoin]
      [[DictIdx "parent"]];
    AC
      [PushdownCollection; AnnotateCollection; FilterPushdown; ToJoin]
      [[DictIdx "parent"]];
    AC
      [PushdownCollection; AnnotateCollection; ToJoin]
      [[]]
  ].

Definition row_ty_parents :=
  TRecord (record_sort [("parent", TString); ("child", TString)]).

Section WithConcreteMaps.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put (map.put map.empty
               "parents_tbl" (TList row_ty_parents))
      "queries" (TList TString).

  Compute (typecheck init_Gstore init_Genv prog).

  Definition prog_transformed := map (fun heu => apply_optimize_anno (width:=width) (heu prog) init_Gstore init_Genv) heuristics.

  Compute prog_transformed.

  Theorem prog_transformed_sem : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      forall prog', In prog' prog_transformed ->
                    interp_command store env prog' = interp_command store env prog.
  Proof.
    unfold prog_transformed, heuristics, apply_optimize_anno; cbn [map]; intros.
    repeat destruct_In;
      try eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
    lazymatch goal with H: In _ [] |- _ => apply in_nil in H; intuition idtac end.
  Qed.
End WithConcreteMaps.

Compute program_py prog.
Compute map program_py prog_transformed.
