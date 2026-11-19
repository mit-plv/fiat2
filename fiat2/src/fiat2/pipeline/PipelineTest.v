Require Import fiat2.Language fiat2.Value fiat2.Interpret fiat2.TypeSystem fiat2.TransfSound fiat2.Invariant
  fiat2.constraint.Surface fiat2.constraint.KeyCheck fiat2.constraint.GuardRules fiat2.index.IndexTransf fiat2.index.DictIndex
  fiat2.rules.CollectionTransf fiat2.rules.FlatmapForms fiat2.rules.EraseField fiat2.rules.BoolTransf fiat2.pipeline.Pipeline.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Datatypes.Result.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition tenv := SortedListString.map type.

Definition locals := SortedListString.map Value.value.

#[local] Instance tenv_ok : map.ok tenv := SortedListString.ok type.

#[local] Instance locals_ok : map.ok locals := SortedListString.ok Value.value.

Definition ipasses : list (tenv -> tenv -> command -> command) :=
  [ fun G _ c => fold_command_with_ictx guard_rule (fun _ _ c => c) nil G c;
    fun G _ c => fold_command_with_ictx (fun _ _ => and_true_head) (fun _ _ => if_const_head) nil G c;
    fun G _ c => at_letmut "users" (fun _ c => create_idx (idx := dict_idx "id") "tbl" "idx" c) G c;
    fun G _ c => fold_command_with_ictx (fun _ _ e => annotate_collection (dict_delete_head (fold_cons_head e))) (fun _ _ c => c) nil G c;
    fun G _ c => fold_command_with_ictx dict_lookup_rule (fun _ _ c => c) nil G c;
    fun G _ c => fold_command_with_ictx dict_read_rule (fun _ _ c => c) nil G c ].

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
      1: apply fold_command_with_ictx_sound;
           [ apply expr_transf__ictx_rule_sound, and_true_head_sound
           | apply inv_transf__ictx_cmd_rule_sound, if_const_head_sound ].
      1: apply create_idx_at_sound; discriminate.
      1:{ apply fold_command_with_ictx_sound; [ apply expr_transf__ictx_rule_sound | apply id_cmd_rule_sound ].
          exact (expr_transf_sound_compose _ _ annotate_collection_sound
                   (expr_transf_sound_compose _ _ dict_delete_head_sound fold_cons_head_sound)). }
      1: apply fold_command_with_ictx_sound; [ apply dict_lookup_rule_sound | apply id_cmd_rule_sound ].
      1: apply fold_command_with_ictx_sound; [ apply dict_read_rule_sound | apply id_cmd_rule_sound ]. }
  1: apply Forall_cons; [ apply erase_dead_field_at_sound | apply Forall_nil ].
Qed.

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

Definition idx := EAccess (ELoc "users") "idx".

Definition key_guard :=
  ELet new_row "_pk_row"
    (EBinop OEq
       (EOptMatch (EBinop OLookup idx (EAccess (EVar "_pk_row") "id")) (EAtom (AEmptyBag None)) "_b" (EVar "_b"))
       (EAtom (AEmptyBag None))).

Example compiled :
  compile_users prog =
    Success (CLetMut (ERecord [("idx", dict_fold "id" (EAtom (ANil (Some row_ty))))]) "users"
               (Some (TRecord [("idx", dict_ty TInt [("age", TInt); ("id", TInt)])])) nil
               (CSeq
                  (CIf (EBinop OAnd key_guard (ELet new_row "u" age_pos))
                     (CAssign "users"
                        (ERecord [("idx", ELet idx "_acc" (ELet new_row "_tup" (dict_body "id" "_tup" "_acc" "_b" None)))]))
                     CSkip)
                  (CSeq
                     (CLet (EACFold AGCount
                              (EOptMatch (EBinop OLookup idx (EAtom (AInt 7))) (EAtom (AEmptyBag None)) "_b" (EVar "_b")))
                        "n" CSkip)
                     (CAssign "users" (ERecord [("idx", EBinop ODelete idx (EAtom (AInt 7)))]))))).
Proof. reflexivity. Qed.
