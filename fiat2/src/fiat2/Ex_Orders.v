Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.SumAgg fiat2.MinAgg fiat2.BitmapIndex fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.OptimizeAnno fiat2.ToPython.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.

Import ListNotations.

(*
(* Consider a sales event where the customer can get the lowest-value item in their orders for free if they spend at least 300 dollars.
This is the code for an application executing commands to add orders and log information about whether the current orders qualify for the discount.
Collection annotation creation and pushdown, filter pushdown, dictionary-based index for filter by equality, sum and min aggregations, incremental updates *)

let mut inventory := inventory_tbl in
let mut orders := orders_tbl in

foreach q in queries do
    let mut new_log := "" in
    if q.type = "add order" then
        let item_price =
            sort [ item <- !inventory,
            check(item.id = q.new_order_id),
            ret item.price ] in
        foreach price in item_price do
            orders := { id: q.new_order_id, price: price } :: !orders
        end;
        new_log := "Added order: " ++ str(q.new_order_id) ++ "\n"
    else if q.type = "discount status" then
            let total = sum([ item <- !orders, ret item.price ]) in
            if total < 300 then
                let diff = 300 - total in
                new_log := "Spend another " ++ str(diff) ++
                    " dollars to get discount\n"
            else
                let min_price_opt =
                    min([ item <- !orders, ret item.price ]) in
                new_log :=
                    optmatch min_price_opt as min_price with
                        "Minimum price undefined: No orders\n"
                        :
                        "Qualified for a discount of " ++
                        str(min_price) ++ " dollars\n"
                    end
            end
        else
            new_log := "Invalid q\n"
        end
    end;
    log := !new_log :: !log
end
*)

Definition prog := (CLetMut (EVar "inventory_tbl") "inventory" (CLetMut (EVar "orders_tbl") "orders" (CForeach (EVar "queries") "q" (CLetMut (EAtom (AString "")) "new_log" (CSeq (CIf (EBinop OEq (EAccess (EVar "q") "type") (EAtom (AString "add order"))) (CLet (ESort LikeList (EFlatmap LikeList (ELoc "inventory") "item" (EIf (EBinop OEq (EAccess (EVar "item") "id") (EAccess (EVar "q") "new_order_id")) (EBinop OCons (EAccess (EVar "item") "price") (EAtom (ANil None))) (EAtom (ANil None))))) "item_price" (CSeq (CForeach (EVar "item_price") "price" (CAssign "orders" (EBinop OCons (ERecord [("id", (EAccess (EVar "q") "new_order_id")); ("price", (EVar "price"))]) (ELoc "orders")))) (CAssign "new_log" (EBinop OConcatString (EAtom (AString "Added order: ")) (EBinop OConcatString (EUnop OIntToString (EAccess (EVar "q") "new_order_id")) (EAtom (AString "\n"))))))) (CIf (EBinop OEq (EAccess (EVar "q") "type") (EAtom (AString "discount status"))) (CLet (EFold (EFlatmap LikeList (ELoc "orders") "item" (EBinop OCons (EAccess (EVar "item") "price") (EAtom (ANil None)))) (EAtom (AInt 0)) "_v" "_acc" (EBinop OPlus (EVar "_v") (EVar "_acc"))) "total" (CIf (EBinop OLess (EVar "total") (EAtom (AInt 300))) (CLet (EBinop OMinus (EAtom (AInt 300)) (EVar "total")) "diff" (CAssign "new_log" (EBinop OConcatString (EAtom (AString "Spend another ")) (EBinop OConcatString (EUnop OIntToString (EVar "diff")) (EAtom (AString " dollars to get discount\n")))))) (CLet (EFold (EFlatmap LikeList (ELoc "orders") "item" (EBinop OCons (EAccess (EVar "item") "price") (EAtom (ANil None)))) (EAtom (ANone (Some TInt))) "_v" "_acc" (EOptMatch (EVar "_acc") (EUnop OSome (EVar "_v")) "_x" (EIf (EBinop OLess (EVar "_v") (EVar "_x")) (EUnop OSome (EVar "_v")) (EVar "_acc")))) "min_price_opt" (CAssign "new_log" (EOptMatch (EVar "min_price_opt") (EAtom (AString "Minimum price undefined: No orders\n")) "min_price" (EBinop OConcatString (EAtom (AString "Qualified for a discount of ")) (EBinop OConcatString (EUnop OIntToString (EVar "min_price")) (EAtom (AString " dollars\n"))))))))) (CAssign "new_log" (EAtom (AString "Invalid q\n"))))) (CAssign "log" (EBinop OCons (ELoc "new_log") (ELoc "log")))))))).

Definition heuristics :=
  [
    AC
      [PushdownCollection; AnnotateCollection; ToProj; ToFilter; IfNilIntoFlatmap; ToProj]
      [[DictIdx "id"]; [SumAgg "price"; MinAgg "price"]];
    AC
      [PushdownCollection; AnnotateCollection; ToProj]
      [[DictIdx "id"]; [SumAgg "price"; MinAgg "price"]];
    AC
      [PushdownCollection; AnnotateCollection; ToProj]
      [[]; [SumAgg "price"; MinAgg "price"]]
  ].

Definition row_ty_inventory :=
  TRecord (record_sort [("id", TInt); ("price", TInt)]).

Definition row_ty_orders :=
  TRecord (record_sort [("id", TInt); ("price", TInt)]).

Definition row_ty_query :=
  TRecord (record_sort [("type", TString); ("new_order_id", TInt)]).

Section WithConcreteMaps.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Definition init_Gstore : ctenv :=
    map.put map.empty "log" (TList TString).

  Definition init_Genv : ctenv :=
    map.put (map.put (map.put map.empty
                        "inventory_tbl" (TList row_ty_inventory))
               "orders_tbl" (TList row_ty_orders))
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
