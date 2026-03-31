Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.SumAgg fiat2.MinAgg fiat2.BitmapIndex fiat2.TransfUtils fiat2.RelTransf fiat2.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.

Import ListNotations.

Require Import fiat2.Notations.
Open Scope fiat2_scope.

Section WithConcreteMaps.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Definition attr2 := "department-id".
Unset Printing Notations.
    Definition row_ty2_1 := TRecord (record_sort [("department-id", TInt); ("department-name", TString)]).
    Definition row_ty2_2 := TRecord (record_sort [("name", TString); ("department-id", TInt); ("feedback", TString)]).

    Definition join_tables : expr := ESort LikeList <[
          "r1" <- mut "departments" ;
          "r3" <- ("r2" <- mut "responses" ;
                   check("r2"["department-id"] == "r1"["department-id"]);
                   ret "r2") ;
          ret {"name" : "r3" ["name"],
                "department" : "r1" ["department-name"],
                  "feedback" : "r3" ["feedback"]} ]>.

    Definition ex2 := CLetMut (EVar "dpt_tbl") "departments"
                        (CLetMut (EVar "res_tbl") "responses"
                           (CForeach (EBinop ORange (EAtom (AInt 0)) (EAtom (AInt 10000))) "i"
                              (CSeq (CAssign "all_feedback" (EAtom (AString "")))
                                    (CForeach join_tables "r"
                                     <{ let "name" = "r"["name"] +++ << EAtom (AString " from ") >> in
                                        let "dep" = "r"["department"] +++ << EAtom (AString " wrote: ") >> in
                                        let "feedback" = "r"["feedback"] +++ << EAtom (AString "\n") >> in
                                        let "line" = "name" +++ "dep" +++ "feedback" in
                                        set "all_feedback" := mut "all_feedback" +++ "line" }>)))).

    Definition init_Gstore2 : ctenv := map.put map.empty "all_feedback" TString.
    Definition init_Genv2 : ctenv := map.put (map.put map.empty "res_tbl" (TList row_ty2_2)) "dpt_tbl" (TList row_ty2_1).

    Definition ex2_heu1 :=
      AC [PushdownCollection; AnnotateCollection; FilterPushdown; ToFilter; ToProj; ToJoin]
        [[DictIdx "department-id"]; [DictIdx "department-id"]]
        ex2.
    Definition ex2_heu2 :=
      AC [PushdownCollection; AnnotateCollection; ToFilter; ToProj; ToJoin]
        [[DictIdx "department-id"]; []]
        ex2.

    Definition ex2_heu3 :=
      AC [PushdownCollection; AnnotateCollection; FilterPushdown; ToJoin]
        [[DictIdx "department-id"]; [BitmapIdx "department-id" ""]]
        ex2.

    Require Import fiat2.ToPython.
    Compute (program_py ex2).

    Definition ex2_heu := AC
                            [PushdownCollection; AnnotateCollection; FilterPushdown; ToFilter; ToProj; ToJoin]
                            [[DictIdx attr2]; [DictIdx attr2]] ex2.

    Definition ex2_transformed := apply_optimize_anno (width:=width) ex2_heu2 init_Gstore2 init_Genv2.
    (* Compute (typecheck init_Gstore2 init_Genv2 ex2). *)
    Compute ex2_transformed.

    Compute (program_py ex2_transformed).

    Theorem ex2_transformed_sem : forall (store env : clocals),
        locals_wf init_Gstore2 store ->
        locals_wf init_Genv2 env ->
        interp_command store env ex2_transformed = interp_command store env ex2.
    Proof.
      unfold ex2_transformed, apply_optimize_anno.
      eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
    Qed.
End WithConcreteMaps.
