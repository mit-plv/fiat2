Require Import fiat2.Language fiat2.TypeSystem fiat2.Invariant fiat2.constraint.Surface
  fiat2.index.IndexTransf fiat2.index.CompoIndex fiat2.index.DictIndex
  fiat2.rules.CollectionTransf fiat2.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Datatypes.Result.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition tenv := SortedListString.map type.

Definition row_ty := TRecord [("age", TInt); ("id", TInt)].

Definition idxs := [("by_age", dict_idx "age"); ("by_id", dict_idx "id")].

Definition new_row := ERecord [("age", EAtom (AInt 30)); ("id", EAtom (AInt 7))].

Definition insert := EBinop OCons new_row (ELoc "users").

Definition count (attr : string) (k : Z) :=
  EUnop OLength
    (flatmap_filter_list (ELoc "users") "x" (EBinop OEq (EAccess (EVar "x") attr) (EAtom (AInt k))) "x" None None).

Definition prog : scommand :=
  SLetConstrained "users" row_ty nil
    (SSeq (SAssign "users" insert SSkip)
       (SSeq (SLet (count "id" 7) "n" SSkip) (SLet (count "age" 30) "m" SSkip))).

Definition compile (sc : scommand) : option command :=
  match typecheck (tenv := tenv) map.empty map.empty (elab nil sc) with
  | Success c =>
      let c := at_letmut "users" (fun _ c => create_idxs idxs "_h" "tbl" "idx" c) (map.empty : tenv) c in
      let c := fold_command_with_ictx (tenv := tenv)
                 (fun _ _ e => annotate_collection (dict_delete_head (fold_cons_head (dict_snoc_head e))))
                 (fun _ _ c => c) nil map.empty c in
      let c := fold_command_with_ictx (tenv := tenv) (fun _ _ => push_down_collection) (fun _ _ c => c) nil map.empty c in
      let c := fold_command_with_ictx (tenv := tenv) dict_lookup_rule (fun _ _ c => c) nil map.empty c in
      Some (fold_command_with_ictx (tenv := tenv) dict_read_rule (fun _ _ c => c) nil map.empty c)
  | Failure _ => None
  end.

Definition tbl := EAccess (ELoc "users") "tbl".

Definition idx (tag : string) := EAccess (EAccess (ELoc "users") "idx") tag.

Definition row_tl := [("age", TInt); ("id", TInt)].

Definition lookup (tag : string) (k : Z) :=
  EACFold AGCount (EOptMatch (EBinop OLookup (idx tag) (EAtom (AInt k))) (EAtom (AEmptyBag None)) "_b" (EVar "_b")).

Definition insert_into (tag attr : string) :=
  ELet (idx tag) "_acc" (ELet new_row "_tup" (dict_body attr "_tup" "_acc" "_b" None)).

Example compiled :
  compile prog =
    Some (CLetMut
            (ERecord [("tbl", EAtom (ANil (Some row_ty)));
                      ("idx", ERecord [("by_age", dict_fold "age" (EAtom (ANil (Some row_ty))));
                                       ("by_id", dict_fold "id" (EAtom (ANil (Some row_ty))))])])
            "users"
            (Some (TRecord [("idx", TRecord [("by_age", dict_ty TInt row_tl); ("by_id", dict_ty TInt row_tl)]);
                            ("tbl", TList row_ty)]))
            [ IndexInv "users" ["tbl"] ["idx"; "by_age"] "_h" (dict_fold "age" (EVar "_h"));
              IndexInv "users" ["tbl"] ["idx"; "by_id"] "_h" (dict_fold "id" (EVar "_h")) ]
            (CSeq
               (CAssign "users"
                  (ERecord [("tbl", EBinop OCons new_row tbl);
                            ("idx", ERecord [("by_age", insert_into "by_age" "age");
                                             ("by_id", insert_into "by_id" "id")])]))
               (CSeq (CLet (lookup "by_id" 7) "n" CSkip) (CLet (lookup "by_age" 30) "m" CSkip)))).
Proof. reflexivity. Qed.
