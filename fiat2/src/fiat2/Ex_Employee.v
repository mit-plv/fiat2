Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.SumAgg fiat2.MinAgg fiat2.BitmapIndex fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.OptimizeAnno fiat2.ToPython.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.

Import ListNotations.

(*
(* Join on foreign key *)

(* id is the primary key of dept_tbl
   dept_id is a foreign key of emp_tbl
*)

let mut employees := emp_tbl in
let mut departments := dept_tbl in

foreach i in range(0, iters) do
    let mut output := "" in
    let result =
    sort [ d <- !departments,
        e <- !employees,
        check(e.dept_id = d.id),
        ret {name: e.name, dept: d.name} ] in

    foreach r in result do
        output := !output ++ r.name ++ " is in " ++ r.dept ++ "\n"
    end;
    outputs := !output :: !outputs
end
*)

Definition prog := (CLetMut (EVar "emp_tbl") "employees" (CLetMut (EVar "dept_tbl") "departments" (CForeach (EBinop ORange (EAtom (AInt 0)) (EVar "iters")) "i" (CLetMut (EAtom (AString "")) "output" (CLet (ESort LikeList (EFlatmap LikeList (ELoc "departments") "d" (EFlatmap LikeList (ELoc "employees") "e" (EIf (EBinop OEq (EAccess (EVar "e") "dept_id") (EAccess (EVar "d") "id")) (EBinop OCons (ERecord [("name", (EAccess (EVar "e") "name")); ("dept", (EAccess (EVar "d") "name"))]) (EAtom (ANil None))) (EAtom (ANil None)))))) "result" (CSeq (CForeach (EVar "result") "r" (CAssign "output" (EBinop OConcatString (ELoc "output") (EBinop OConcatString (EAccess (EVar "r") "name") (EBinop OConcatString (EAtom (AString " is in ")) (EBinop OConcatString (EAccess (EVar "r") "dept") (EAtom (AString "\n")))))))) (CAssign "outputs" (EBinop OCons (ELoc "output") (ELoc "outputs"))))))))).

Definition heuristics := [
    AC
      [PushdownCollection; AnnotateCollection; ToProj; JoinToFlatmapFilter; ToJoin]
      [[DictIdx "dept_id"]; []];
    AC
      [PushdownCollection; AnnotateCollection; ToJoin]
      [[]; []]
  ].

(* Row types *)
Definition row_ty_employees :=
  TRecord (record_sort [("name", TString); ("dept_id", TInt); ("salary", TInt)]).

Definition row_ty_departments :=
  TRecord (record_sort [("id", TInt); ("name", TString)]).

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
    map.put (map.put (map.put map.empty "emp_tbl" (TList row_ty_employees))
               "dept_tbl" (TList row_ty_departments))
      "iters" TInt.

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

Definition res_attrs := ["name"; "dept"].
Compute sort_key_py "res" (Mergesort.Sectioned.sort String.leb res_attrs).
