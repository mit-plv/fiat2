Require Import fiat2.Language fiat2.TypeSystem fiat2.Invariant fiat2.constraint.Surface
  fiat2.constraint.KeyCheck fiat2.constraint.GuardRules fiat2.index.IndexTransf fiat2.index.DictIndex
  fiat2.rules.CollectionTransf fiat2.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Datatypes.Result.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition tenv := SortedListString.map type.

Definition row_ty := TRecord [("age", TInt); ("id", TInt)].

Definition key := erase_annot (unique_cond "users" ["id"] row_ty).

Definition new_row := ERecord [("age", EAtom (AInt 30)); ("id", EAtom (AInt 7))].

Definition insert := EBinop OCons new_row (ELoc "users").

Definition id_is_7 := EBinop OEq (EAccess (EVar "x") "id") (EAtom (AInt 7)).

Definition delete := flatmap_filter_list (ELoc "users") "x" (EUnop ONot id_is_7) "x" None None.

Definition count := EUnop OLength (flatmap_filter_list (ELoc "users") "x" id_is_7 "x" None None).

Definition prog : scommand :=
  SLetConstrained "users" row_ty [("_r", key)]
    (SSeq (SAssign "users" insert SSkip)
       (SSeq (SLet count "n" SSkip) (SAssign "users" delete SSkip))).

Definition compile (sc : scommand) : option command :=
  match typecheck (tenv := tenv) map.empty map.empty (elab nil sc) with
  | Success c =>
      let c := fold_command_with_ictx (tenv := tenv) guard_rule (fun _ _ c => c) nil map.empty c in
      let c := at_letmut "users" (fun _ c => create_idx (idx := dict_idx "id") "tbl" "idx" c) (map.empty : tenv) c in
      let c := fold_command_with_ictx (tenv := tenv)
                 (fun _ _ e => annotate_collection (dict_delete_head (fold_cons_head (dict_snoc_head e)))) (fun _ _ c => c) nil map.empty c in
      let c := fold_command_with_ictx (tenv := tenv) (fun _ _ => push_down_collection) (fun _ _ c => c) nil map.empty c in
      let c := fold_command_with_ictx (tenv := tenv) dict_lookup_rule (fun _ _ c => c) nil map.empty c in
      Some (fold_command_with_ictx (tenv := tenv) dict_read_rule (fun _ _ c => c) nil map.empty c)
  | Failure _ => None
  end.

Definition tbl := EAccess (ELoc "users") "tbl".

Definition idx := EAccess (ELoc "users") "idx".

Definition key_guard (row : expr) :=
  ELet row "_pk_row"
    (EBinop OEq
       (EOptMatch (EBinop OLookup idx (EAccess (EVar "_pk_row") "id")) (EAtom (AEmptyBag None)) "_b" (EVar "_b"))
       (EAtom (AEmptyBag None))).

Definition users_init :=
  ERecord [("tbl", EAtom (ANil (Some row_ty))); ("idx", dict_fold "id" (EAtom (ANil (Some row_ty))))].

Definition users_ty := TRecord [("idx", dict_ty TInt [("age", TInt); ("id", TInt)]); ("tbl", TList row_ty)].

Definition users_invs :=
  [ IndexInv "users" ["tbl"] ["idx"] "_h" (dict_fold "id" (EVar "_h"));
    ConstraintInv "users" ["tbl"] "_r"
      (EBinop OEq
         (EUnop OLength
            (flatmap_filter_list tbl "_r2"
               (EBinop OEq (EAccess (EVar "_r2") "id") (EAccess (EVar "_r") "id")) "_r2" None None))
         (EAtom (AInt 1))) ].

Example compiled :
  compile prog =
    Some (CLetMut users_init "users" (Some users_ty) users_invs
            (CSeq
               (CIf (EBinop OAnd (key_guard new_row) (EAtom (ABool true)))
                  (CAssign "users"
                     (ERecord [("tbl", EBinop OCons new_row tbl);
                               ("idx", ELet idx "_acc" (ELet new_row "_tup" (dict_body "id" "_tup" "_acc" "_b" None)))]))
                  CSkip)
               (CSeq
                  (CLet (EACFold AGCount
                           (EOptMatch (EBinop OLookup idx (EAtom (AInt 7))) (EAtom (AEmptyBag None)) "_b" (EVar "_b")))
                     "n" CSkip)
                  (CIf (EBinop OAnd (EAtom (ABool true)) (EAtom (ABool true)))
                     (CAssign "users"
                        (ERecord [("tbl", flatmap_filter_list tbl "x" (EUnop ONot id_is_7) "x" (Some row_ty) (Some row_ty));
                                  ("idx", EBinop ODelete idx (EAtom (AInt 7)))]))
                     CSkip)))).
Proof. reflexivity. Qed.

(* The new row reads a variable named like the index's accumulator, so
   substituting it into the index renames the accumulator *)
Definition age_row := ERecord [("age", EVar "_acc"); ("id", EAtom (AInt 7))].

Definition prog_renamed : scommand :=
  SLetConstrained "users" row_ty [("_r", key)]
    (SLet (EAtom (AInt 30)) "_acc" (SAssign "users" (EBinop OCons age_row (ELoc "users")) SSkip)).

Example compiled_renamed :
  compile prog_renamed =
    Some (CLetMut users_init "users" (Some users_ty) users_invs
            (CLet (EAtom (AInt 30)) "_acc"
               (CIf (EBinop OAnd (key_guard age_row) (EAtom (ABool true)))
                  (CAssign "users"
                     (ERecord [("tbl", EBinop OCons age_row tbl);
                               ("idx", ELet idx "_acc'''''"
                                         (ELet age_row "_tup" (dict_body "id" "_tup" "_acc'''''" "_b" None)))]))
                  CSkip))).
Proof. reflexivity. Qed.

Definition prog_append : scommand :=
  SLetConstrained "users" row_ty nil
    (SAssign "users" (EBinop OConcat (ELoc "users") (EBinop OCons new_row (EAtom (ANil None)))) SSkip).

Example compiled_append :
  compile prog_append =
    Some (CLetMut users_init "users" (Some users_ty) [ IndexInv "users" ["tbl"] ["idx"] "_h" (dict_fold "id" (EVar "_h")) ]
            (CAssign "users"
               (ERecord [("tbl", EBinop OConcat tbl (EBinop OCons new_row (EAtom (ANil (Some row_ty)))));
                         ("idx", ELet idx "_acc" (ELet new_row "_tup" (dict_body "id" "_tup" "_acc" "_b" None)))]))).
Proof. reflexivity. Qed.
