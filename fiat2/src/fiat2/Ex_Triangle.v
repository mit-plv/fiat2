Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.SumAgg fiat2.MinAgg fiat2.BitmapIndex fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.OptimizeAnno fiat2.ToPython.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.

Import ListNotations.

(*
(* Example application for adding edges to a graph and printing all triangles in the graph.
Triple self-join, filter pushdown, index creation and incremental updates *)

let mut edges := edges_tbl in

foreach q in queries do
    if q.type = 0
    then
        let triangles =
            sort [ e1 <- !edges,
                e2 <- !edges,
                e3 <- !edges,
                check(e2.src = e1.dst),
                check(e3.src = e2.dst),
                check(e1.dst = e3.dst),
                check(e1.src < e1.dst && e2.src < e2.dst),
                ret { p1: e1.src, p2: e2.src, p3: e3.src } ] in
        let mut result := "" in
        foreach tri in triangles do
            result := !result ++ str(tri.p1) ++ ", " ++
                str(tri.p2) ++ ", " ++ str(tri.p3) ++ "\n"
        end;
        outputs := !result :: !outputs
    else
        edges := q.new_edge :: !edges;
        outputs := "New edge added successfully\n" :: !outputs
    end
end
 *)

Definition prog := (CLetMut (EVar "edges_tbl") "edges" (CForeach (EVar "queries") "q" (CIf (EBinop OEq (EAccess (EVar "q") "type") (EAtom (AInt 0))) (CLet (ESort LikeList (EFlatmap LikeList (ELoc "edges") "e1" (EFlatmap LikeList (ELoc "edges") "e2" (EFlatmap LikeList (ELoc "edges") "e3" (EIf (EBinop OEq (EAccess (EVar "e2") "src") (EAccess (EVar "e1") "dst")) (EIf (EBinop OEq (EAccess (EVar "e3") "src") (EAccess (EVar "e2") "dst")) (EIf (EBinop OEq (EAccess (EVar "e1") "dst") (EAccess (EVar "e3") "dst")) (EIf (EBinop OAnd (EBinop OLess (EAccess (EVar "e1") "src") (EAccess (EVar "e1") "dst")) (EBinop OLess (EAccess (EVar "e2") "src") (EAccess (EVar "e2") "dst"))) (EBinop OCons (ERecord [("p1", (EAccess (EVar "e1") "src")); ("p2", (EAccess (EVar "e2") "src")); ("p3", (EAccess (EVar "e3") "src"))]) (EAtom (ANil None))) (EAtom (ANil None))) (EAtom (ANil None))) (EAtom (ANil None))) (EAtom (ANil None))))))) "triangles" (CLetMut (EAtom (AString "")) "result" (CSeq (CForeach (EVar "triangles") "tri" (CAssign "result" (EBinop OConcatString (ELoc "result") (EBinop OConcatString (EUnop OIntToString (EAccess (EVar "tri") "p1")) (EBinop OConcatString (EAtom (AString ", ")) (EBinop OConcatString (EUnop OIntToString (EAccess (EVar "tri") "p2")) (EBinop OConcatString (EAtom (AString ", ")) (EBinop OConcatString (EUnop OIntToString (EAccess (EVar "tri") "p3")) (EAtom (AString "\n")))))))))) (CAssign "outputs" (EBinop OCons (ELoc "result") (ELoc "outputs")))))) (CSeq (CAssign "edges" (EBinop OCons (EAccess (EVar "q") "new_edge") (ELoc "edges"))) (CAssign "outputs" (EBinop OCons (EAtom (AString "New edge added successfully\n")) (ELoc "outputs"))))))).

Definition heuristics := [
    AC
      [PushdownCollection; AnnotateCollection; ToProj; ToFilter;
       IfNilIntoFlatmap; SwapFlatmapIf; SwapFlatmapIf;
       SplitIf; SwapIfNil;
       IfNilIntoFlatmap; SwapFlatmapIf; SwapFlatmapIf]
      [[DictIdx "src"]];
    AC
      [PushdownCollection; AnnotateCollection; ToProj; ToFilter;
       IfNilIntoFlatmap; SwapFlatmapIf; SwapFlatmapIf; SwapFlatmapIf;
       SplitIf; SwapIfNil;
       IfNilIntoFlatmap; SwapFlatmapIf; SwapFlatmapIf; SwapFlatmapIf]
      [[DictIdx "src"]];
    AC
      [PushdownCollection; AnnotateCollection; ToFilter;
       IfNilIntoFlatmap; SwapFlatmapIf; SwapFlatmapIf;
       SplitIf; SwapIfNil;
       IfNilIntoFlatmap; SwapFlatmapIf; SwapFlatmapIf]
      [[DictIdx "src"]]
  ].

Definition row_ty_edges :=
  TRecord (record_sort [("src", TInt); ("dst", TInt)]).

Definition row_ty_query :=
  TRecord (record_sort [("type", TInt); ("new_edge", row_ty_edges)]).

Definition row_ty_triangle :=
  TRecord (record_sort [("p1", TInt); ("p2", TInt); ("p3", TInt)]).

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
      "queries" (TList row_ty_query).

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

Definition res_attrs := ["p1"; "p2"; "p3"].
Compute sort_key_py "res" (Mergesort.Sectioned.sort String.leb res_attrs).
