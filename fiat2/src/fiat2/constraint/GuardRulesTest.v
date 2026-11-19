Require Import fiat2.Language fiat2.TypeSystem fiat2.Invariant fiat2.constraint.Surface
  fiat2.constraint.KeyCheck fiat2.constraint.GuardRules.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Datatypes.Result.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition tenv := SortedListString.map type.

Definition row_ty := TRecord [("age", TInt); ("id", TInt)].

Definition age_pos := EBinop OLess (EAtom (AInt 0)) (EAccess (EVar "u") "age").

Definition users_decls : list (string * expr) :=
  [ ("_r", unique_cond "users" ["id"] row_ty); ("u", age_pos) ].

Definition new_row := ERecord [("age", EAtom (AInt 30)); ("id", EAtom (AInt 7))].

Definition insert := EBinop OCons new_row (ELoc "users").

Definition delete :=
  EFlatmap LikeList (ELoc "users") "x"
    (EIf (EBinop OLess (EAccess (EVar "x") "id") (EAtom (AInt 7)))
       (EBinop OCons (EVar "x") (EAtom (ANil None)))
       (EAtom (ANil None))).

Definition prog : scommand :=
  SLetConstrained "users" row_ty users_decls
    (SSeq (SAssign "users" insert SSkip) (SAssign "users" delete SSkip)).

Definition rewritten : command :=
  fold_command_with_ictx (tenv := tenv) guard_rule nil map.empty (elab nil prog).

Example elab_prog :
  elab nil prog =
    CLetMut (EAtom (ANil (Some row_ty))) "users" (Some (TList row_ty)) (decl_invs "users" users_decls)
      (CSeq (CIf (guards "users" insert (decl_invs "users" users_decls)) (CAssign "users" insert) CSkip)
         (CIf (guards "users" delete (decl_invs "users" users_decls)) (CAssign "users" delete) CSkip)).
Proof. reflexivity. Qed.

Example rewritten_prog :
  rewritten =
    CLetMut (EAtom (ANil (Some row_ty))) "users" (Some (TList row_ty)) (decl_invs "users" users_decls)
      (CSeq
         (CIf (EBinop OAnd (unique_guard_let "users" ["id"] new_row)
                 (EBinop OAnd (ELet new_row "u" age_pos) (EAtom (ABool true))))
            (CAssign "users" insert) CSkip)
         (CIf (EBinop OAnd (EAtom (ABool true))
                 (EBinop OAnd (EAtom (ABool true)) (EAtom (ABool true))))
            (CAssign "users" delete) CSkip)).
Proof. reflexivity. Qed.

Definition users_decls_unannotated : list (string * expr) :=
  [ ("_r", erase_annot (unique_cond "users" ["id"] row_ty)); ("u", age_pos) ].

Definition prog_unannotated : scommand :=
  SLetConstrained "users" row_ty users_decls_unannotated
    (SSeq (SAssign "users" insert SSkip) (SAssign "users" delete SSkip)).

Definition delete_annotated :=
  EFlatmap LikeList (ELoc "users") "x"
    (EIf (EBinop OLess (EAccess (EVar "x") "id") (EAtom (AInt 7)))
       (EBinop OCons (EVar "x") (EAtom (ANil (Some row_ty))))
       (EAtom (ANil (Some row_ty)))).

Example rewritten_after_typecheck :
  match typecheck (tenv := tenv) map.empty map.empty (elab nil prog_unannotated) with
  | Success c => Some (fold_command_with_ictx (tenv := tenv) guard_rule nil map.empty c)
  | Failure _ => None
  end =
    Some (CLetMut (EAtom (ANil (Some row_ty))) "users" (Some (TList row_ty))
            (decl_invs "users" users_decls_unannotated)
            (CSeq
               (CIf (EBinop OAnd (unique_guard_let "users" ["id"] new_row)
                       (EBinop OAnd (ELet new_row "u" age_pos) (EAtom (ABool true))))
                  (CAssign "users" insert) CSkip)
               (CIf (EBinop OAnd (EAtom (ABool true))
                       (EBinop OAnd (EAtom (ABool true)) (EAtom (ABool true))))
                  (CAssign "users" delete_annotated) CSkip))).
Proof. reflexivity. Qed.
