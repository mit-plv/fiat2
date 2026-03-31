(* Materialized view and incremental computation of an aggregation *)
Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.SumAgg fiat2.MinAgg fiat2.BitmapIndex fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.OptimizeAnno fiat2.ToPython.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.

Import ListNotations.

(*
let mut orders := orders_tbl in

foreach q in queries do
    let mut output := "" in
    if q.type = 0
    then
        let total = sum [ o <- mut orders, ret o.value ] in
        output := "Current total value: " ++
            str(total) ++ "\n"
    else
        orders := q.new_order :: mut orders;
        output := "Added a new order\n"
    end;
    outputs := mut output :: mut outputs
end
*)

Definition prog := (CLetMut (EVar "orders_tbl") "orders" (CForeach (EVar "queries") "q" (CLetMut (EAtom (AString "")) "output" (CSeq (CIf (EBinop OEq (EAccess (EVar "q") "type") (EAtom (AInt 0))) (CLet (EFold (EFlatmap LikeList (ELoc "orders") "o" (EBinop OCons (EAccess (EVar "o") "value") (EAtom (ANil None)))) (EAtom (AInt 0)) "_v" "_acc" (EBinop OPlus (EVar "_v") (EVar "_acc"))) "total" (CAssign "output" (EBinop OConcatString (EAtom (AString "Current total value: ")) (EBinop OConcatString (EUnop OIntToString (EVar "total")) (EAtom (AString "\n")))))) (CSeq (CAssign "orders" (EBinop OCons (EAccess (EVar "q") "new_order") (ELoc "orders"))) (CAssign "output" (EAtom (AString "Added a new order\n"))))) (CAssign "outputs" (EBinop OCons (ELoc "output") (ELoc "outputs"))))))).

Definition heuristics := [
    AC [PushdownCollection; AnnotateCollection; ToProj] [[SumAgg "value"]];
    AC [AnnotateCollection; ToProj] [[SumAgg "value"]];
    AC [PushdownCollection; AnnotateCollection] [[SumAgg "value"]]
  ].

Definition row_ty_orders :=
  TRecord (record_sort [("id", TInt); ("value", TInt)]).

Definition row_ty_query :=
  TRecord (record_sort [("type", TInt); ("new_order", row_ty_orders)]).

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
    map.put (map.put map.empty "orders_tbl" (TList row_ty_orders))
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
