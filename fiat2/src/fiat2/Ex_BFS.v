Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.SumAgg fiat2.MinAgg fiat2.BitmapIndex fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.OptimizeAnno fiat2.ToPython.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.

Import ListNotations.

(*
let mut edges := edges_tbl in
let mut visited := [ {node: start_node, depth: 0} ] in
let mut frontier := [ start_node ] in
let mut next_frontier := [] in
let mut cur_depth := 1 in

foreach i in range(0, len(edges)) do
  foreach cur_node in mut frontier do
    let cur_children =
      sort [ e <- mut edges,
        check(e.src = cur_node),
        check([n <- visited, check(n.node = e.dst), ret ()] = []),
        ret e.dst ] in

    foreach n in cur_children do
      visited := {node: n, depth: cur_depth} :: mut visited;
      next_frontier := n :: mut next_frontier
    end
  end;

  frontier := mut next_frontier;
  next_frontier := [];
  cur_depth := mut cur_depth + 1
end;

foreach n in visited do
  output := "Node " ++ n.node ++ " at depth " ++ str(n.depth) ++ "\n" ++ mut output
end
*)

Definition prog := (CLetMut (EVar "edges_tbl") "edges" (CLetMut (EBinop OCons (ERecord [("node", (EVar "start_node")); ("depth", (EAtom (AInt 0)))]) (EAtom (ANil None))) "visited" (CLetMut (EBinop OCons (EVar "start_node") (EAtom (ANil None))) "frontier" (CLetMut (EAtom (ANil (Some TInt))) "next_frontier" (CLetMut (EAtom (AInt 1)) "cur_depth" (CSeq (CForeach (EBinop ORange (EAtom (AInt 0)) (EUnop OLength (EVar "edges_tbl"))) "i" (CSeq (CForeach (ELoc "frontier") "cur_node" (CLet (ESort LikeList (EFlatmap LikeList (ELoc "edges") "e" (EIf (EBinop OEq (EAccess (EVar "e") "src") (EVar "cur_node")) (EIf (EBinop OEq (EFlatmap LikeList (ELoc "visited") "n" (EIf (EBinop OEq (EAccess (EVar "n") "node") (EAccess (EVar "e") "dst")) (EBinop OCons (EAtom AUnit) (EAtom (ANil None))) (EAtom (ANil None)))) (EAtom (ANil None))) (EBinop OCons (EAccess (EVar "e") "dst") (EAtom (ANil None))) (EAtom (ANil None))) (EAtom (ANil None))))) "cur_children" (CForeach (EVar "cur_children") "n" (CSeq (CAssign "visited" (EBinop OCons (ERecord [("node", (EVar "n")); ("depth", (ELoc "cur_depth"))]) (ELoc "visited"))) (CAssign "next_frontier" (EBinop OCons (EVar "n") (ELoc "next_frontier"))))))) (CSeq (CAssign "frontier" (ELoc "next_frontier")) (CSeq (CAssign "next_frontier" (EAtom (ANil (Some TInt)))) (CAssign "cur_depth" (EBinop OPlus (ELoc "cur_depth") (EAtom (AInt 1)))))))) (CForeach (ESort LikeList (ELoc "visited")) "n" (CAssign "outputs" (EBinop OCons (EBinop OConcatString (EAtom (AString "Node ")) (EBinop OConcatString (EUnop OIntToString (EAccess (EVar "n") "node")) (EBinop OConcatString (EAtom (AString " at depth ")) (EBinop OConcatString (EUnop OIntToString (EAccess (EVar "n") "depth")) (EAtom (AString "\n")))))) (ELoc "outputs")))))))))).

Definition heuristics :=
  [
    AC [PushdownCollection; AnnotateCollection; ToJoin; ToFilter; IfNilIntoFlatmap; SwapConjuncts] [[DictIdx "src"]; [DictIdx "node"]];
    AC [AnnotateCollection; ToJoin; ToFilter; IfNilIntoFlatmap] [[DictIdx "src"]; [DictIdx "node"]];
    AC [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap] [[DictIdx "src"]; [DictIdx "node"]]
  ].

Definition row_ty_edges :=
  TRecord (record_sort [("src", TInt); ("dst", TInt)]).

Definition row_ty_visited :=
  TRecord (record_sort [("node", TInt); ("depth", TInt)]).

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
               "edges_tbl" (TList row_ty_edges))
      "start_node" TInt.

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

Definition res_attrs := ["node"; "depth"].
Compute sort_key_py "res" (Mergesort.Sectioned.sort String.leb res_attrs).
