Require Import fiat2.Language fiat2.Invariant fiat2.constraint.Surface fiat2.constraint.KeyCheck fiat2.index.DictIndex
  fiat2.FlatmapForms fiat2.pipeline.Pipeline.
Require Import coqutil.Map.SortedListString coqutil.Datatypes.Result.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition tenv := SortedListString.map type.

Definition rules (ics : list index_choice) : list rule :=
  [ Guard; AndTrue; IfConst; CreateIdxs "users" ics;
    DictSnoc; FoldCons; DictDelete; AnnotateCollection; PushDownCollection; DictLookup; DictRead ].

Definition row_ty := TRecord [("age", TInt); ("id", TInt)].

Definition age_pos := EBinop OLess (EAtom (AInt 0)) (EAccess (EVar "u") "age").

Definition new_row := ERecord [("age", EAtom (AInt 30)); ("id", EAtom (AInt 7))].

Definition id_is_7 := EBinop OEq (EAccess (EVar "x") "id") (EAtom (AInt 7)).

Definition insert := EBinop OCons new_row (ELoc "users").

Definition delete := flatmap_filter_list (ELoc "users") "x" (EUnop ONot id_is_7) "x" None None.

Definition count := EUnop OLength (flatmap_filter_list (ELoc "users") "x" id_is_7 "x" None None).

Definition key := erase_annot (unique_cond "users" ["id"] row_ty).

Definition prog : scommand :=
  SLetConstrained "users" row_ty [("_r", key); ("u", age_pos)]
    (SSeq (SAssign "users" insert SSkip)
       (SSeq (SLet count "n" SSkip) (SAssign "users" delete SSkip))).

Definition idx := EAccess (EAccess (ELoc "users") "idx") "idx0".

Definition key_guard :=
  ELet new_row "_pk_row"
    (EBinop OEq
       (EOptMatch (EBinop OLookup idx (EAccess (EVar "_pk_row") "id")) (EAtom (AEmptyBag None)) "_b" (EVar "_b"))
       (EAtom (AEmptyBag None))).

Example compiled :
  compile_anno (tenv := tenv) {| program := prog; passes := rules [DictIdx "id"]; erasures := [("users", "tbl")] |} =
    Success (CLetMut (ERecord [("idx", ERecord [("idx0", dict_fold "id" (EAtom (ANil (Some row_ty))))])]) "users"
               (Some (TRecord [("idx", TRecord [("idx0", dict_ty TInt [("age", TInt); ("id", TInt)])])])) nil
               (CSeq
                  (CIf (EBinop OAnd key_guard (ELet new_row "u" age_pos))
                     (CAssign "users"
                        (ERecord [("idx", ERecord [("idx0", ELet idx "_acc" (ELet new_row "_tup" (dict_body "id" "_tup" "_acc" "_b" None)))])]))
                     CSkip)
                  (CSeq
                     (CLet (EACFold AGCount
                              (EOptMatch (EBinop OLookup idx (EAtom (AInt 7))) (EAtom (AEmptyBag None)) "_b" (EVar "_b")))
                        "n" CSkip)
                     (CAssign "users" (ERecord [("idx", ERecord [("idx0", EBinop ODelete idx (EAtom (AInt 7)))])]))))).
Proof. reflexivity. Qed.

Definition count_age := EUnop OLength
  (flatmap_filter_list (ELoc "users") "x" (EBinop OEq (EAccess (EVar "x") "age") (EAtom (AInt 30))) "x" None None).

Definition prog2 : scommand :=
  SLetConstrained "users" row_ty [("_r", key); ("u", age_pos)]
    (SSeq (SAssign "users" insert SSkip)
       (SSeq (SLet count "n" SSkip) (SLet count_age "m" SSkip))).

Definition idx_at (tag : string) := EAccess (EAccess (ELoc "users") "idx") tag.

Definition row_tl := [("age", TInt); ("id", TInt)].

Definition insert_into (tag attr : string) :=
  ELet (idx_at tag) "_acc" (ELet new_row "_tup" (dict_body attr "_tup" "_acc" "_b" None)).

Definition lookup (tag : string) (k : Z) :=
  EACFold AGCount (EOptMatch (EBinop OLookup (idx_at tag) (EAtom (AInt k))) (EAtom (AEmptyBag None)) "_b" (EVar "_b")).

Example compiled2 :
  compile_anno (tenv := tenv)
    {| program := prog2; passes := rules [DictIdx "age"; DictIdx "id"]; erasures := [("users", "tbl")] |} =
    Success (CLetMut
               (ERecord [("idx", ERecord [("idx0", dict_fold "age" (EAtom (ANil (Some row_ty))));
                                          ("idx1", dict_fold "id" (EAtom (ANil (Some row_ty))))])])
               "users"
               (Some (TRecord [("idx", TRecord [("idx0", dict_ty TInt row_tl); ("idx1", dict_ty TInt row_tl)])]))
               nil
               (CSeq
                  (CIf (EBinop OAnd
                          (ELet new_row "_pk_row"
                             (EBinop OEq
                                (EOptMatch (EBinop OLookup (idx_at "idx1") (EAccess (EVar "_pk_row") "id"))
                                   (EAtom (AEmptyBag None)) "_b" (EVar "_b"))
                                (EAtom (AEmptyBag None))))
                          (ELet new_row "u" age_pos))
                     (CAssign "users"
                        (ERecord [("idx", ERecord [("idx0", insert_into "idx0" "age");
                                                   ("idx1", insert_into "idx1" "id")])]))
                     CSkip)
                  (CSeq (CLet (lookup "idx1" 7) "n" CSkip) (CLet (lookup "idx0" 30) "m" CSkip)))).
Proof. reflexivity. Qed.
