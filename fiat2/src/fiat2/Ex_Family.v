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
            [ p <- mut parents,
            q <- mut parents,
            check(p.parent = person && q.parent = p.child),
            ret q.child ] in
    foreach child in children do
        result := mut result ++ "child" ++ "\n"
    end;
    outputs := mut result :: mut outputs
end
*)

Definition prog := (CLetMut (EVar "parents_tbl") "parents" (CForeach (EVar "queries") "person" (CLetMut (EBinop OConcatString (EAtom (AString "Grandchildren of ")) (EBinop OConcatString (EVar "person") (EAtom (AString ":\n")))) "result" (CLet (ESort LikeList (EFlatmap LikeList (ELoc "parents") "p" (EFlatmap LikeList (ELoc "parents") "q" (EIf (EBinop OEq (EAccess (EVar "p") "parent") (EBinop OAnd (EVar "person") (EBinop OEq (EAccess (EVar "q") "parent") (EAccess (EVar "p") "child")))) (EBinop OCons (EAccess (EVar "q") "child") (EAtom (ANil None))) (EAtom (ANil None)))))) "children" (CSeq (CForeach (EVar "children") "child" (CAssign "result" (EBinop OConcatString (ELoc "result") (EBinop OConcatString (EAtom (AString "child")) (EAtom (AString "\n")))))) (CAssign "outputs" (EBinop OCons (ELoc "result") (ELoc "outputs")))))))).

Definition heuristics :=
  [
    AC [PushdownCollection; AnnotateCollection; FilterPushdown; ToFilter; ToJoin; ToProj] [[DictIdx "parent"]];
    AC [AnnotateCollection; FilterPushdown; ToFilter; ToJoin; ToProj] [[DictIdx "parent"]];
    AC [PushdownCollection; AnnotateCollection; ToFilter; ToJoin; ToProj] [[DictIdx "parent"]]
  ].
