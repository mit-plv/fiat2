Require Import fiat2.Language fiat2.Value fiat2.Interpret fiat2.TypeSystem fiat2.Invariant fiat2.constraint.Surface
  fiat2.constraint.KeyCheck fiat2.constraint.GuardRules fiat2.index.IndexTransf fiat2.index.DictIndex
  fiat2.rules.CollectionTransf fiat2.rules.FlatmapForms fiat2.rules.EraseField fiat2.TransfSound fiat2.Pipeline.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Datatypes.Result.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition tenv := SortedListString.map type.

Definition locals := SortedListString.map Value.value.

#[local] Instance tenv_ok : map.ok tenv := SortedListString.ok type.

#[local] Instance locals_ok : map.ok locals := SortedListString.ok Value.value.

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

Definition ipasses : list (tenv -> tenv -> command -> command) :=
  [ fun G _ c => fold_command_with_ictx guard_rule nil G c;
    fun G _ c => at_letmut "users" (fun _ c => create_idx (idx := dict_idx "id") "tbl" "idx" c) G c;
    fun G _ c => fold_command_with_ictx (fun _ _ e => annotate_collection (dict_delete_head (fold_cons_head e))) nil G c;
    fun G _ c => fold_command_with_ictx dict_lookup_rule nil G c;
    fun G _ c => fold_command_with_ictx dict_read_rule nil G c ].

Definition fpasses : list (tenv -> tenv -> command -> command) :=
  [ fun G _ c => at_letmut "users" (fun G c => erase_dead_field "tbl" G G c) G c ].

Definition compile_users : scommand -> result command := compile ipasses fpasses.

Theorem compile_users_sound : forall sc c,
    compile_users sc = Success c ->
    well_typed (tenv := tenv) map.empty map.empty c /\
      forall store env : locals, interp_command store env c = interp_command store env (elab nil sc).
Proof.
  intros sc c H. eapply compile_sound; [ | | exact H ].
  1:{ repeat apply Forall_cons; try apply Forall_nil.
      1: apply guard_rules_sound.
      1: apply create_idx_at_sound; discriminate.
      1: apply fold_command_with_ictx_sound, expr_transf__ictx_rule_sound.
      1: exact (expr_transf_sound_compose _ _ annotate_collection_sound
                  (expr_transf_sound_compose _ _ dict_delete_head_sound fold_cons_head_sound)).
      1: apply fold_command_with_ictx_sound, dict_lookup_rule_sound.
      1: apply fold_command_with_ictx_sound, dict_read_rule_sound. }
  1: apply Forall_cons; [ apply erase_dead_field_at_sound | apply Forall_nil ].
Qed.

Definition tbl := EAccess (ELoc "users") "tbl".

Definition idx := EAccess (ELoc "users") "idx".

Definition key_guard (row : expr) :=
  ELet row "_pk_row"
    (EBinop OEq
       (flatmap_filter_bag (EUnop OBagOfList tbl) "_pk_scan"
          (EBinop OEq (EAccess (EVar "_pk_scan") "id") (EAccess (EVar "_pk_row") "id"))
          "_pk_scan" None None)
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
  compile_users prog =
    Success (CLetMut users_init "users" (Some users_ty) users_invs
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
  compile_users prog_renamed =
    Success (CLetMut users_init "users" (Some users_ty) users_invs
            (CLet (EAtom (AInt 30)) "_acc"
               (CIf (EBinop OAnd (key_guard age_row) (EAtom (ABool true)))
                  (CAssign "users"
                     (ERecord [("tbl", EBinop OCons age_row tbl);
                               ("idx", ELet idx "_acc'''''"
                                         (ELet age_row "_tup" (dict_body "id" "_tup" "_acc'''''" "_b" None)))]))
                  CSkip))).
Proof. reflexivity. Qed.

(* Once every read goes through the index, the rows themselves are dead *)
Definition prog_dead : scommand :=
  SLetConstrained "users" row_ty nil
    (SSeq (SAssign "users" insert SSkip) (SLet count "n" SSkip)).

Example compiled_dead :
  compile_users prog_dead =
    Success (CLetMut (ERecord [("idx", dict_fold "id" (EAtom (ANil (Some row_ty))))]) "users"
               (Some (TRecord [("idx", dict_ty TInt [("age", TInt); ("id", TInt)])])) nil
               (CSeq
                  (CAssign "users"
                     (ERecord [("idx", ELet idx "_acc" (ELet new_row "_tup" (dict_body "id" "_tup" "_acc" "_b" None)))]))
                  (CLet (EACFold AGCount
                           (EOptMatch (EBinop OLookup idx (EAtom (AInt 7))) (EAtom (AEmptyBag None)) "_b" (EVar "_b")))
                     "n" CSkip))).
Proof. reflexivity. Qed.
