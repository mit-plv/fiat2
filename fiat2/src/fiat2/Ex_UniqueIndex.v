Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.Utils fiat2.Substitute
  fiat2.Constraint fiat2.UniqueDictIndexImpl.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface
  coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* The unique dictionary index on a concrete table.

   A table of users keyed by id, holding two rows, together with the index
   that maps each id to its row.  What is checked here:

   - the index really is id -> row, computed (demo_idx_value);
   - the cheap guard typechecks (demo_unique_guard_ty);
   - on a key the table already holds, both the cheap guard and the guard the
     constraint elaboration inserts reject the write, and on a fresh key both
     accept it -- by computation, so the compiler checks the two agree on
     these inputs (demo_taken_key, demo_fresh_key);
   - and they agree on *every* row, for this table and this index, by
     unique_guard_sound (demo_guards_agree).  Every hypothesis that theorem
     asks for is discharged below, which is the point of the file: the
     statement is not vacuous. *)

(* already sorted by field name, as a record type must be *)
Definition row_ty := TRecord [("id", TInt); ("name", TString)].

(* the variable names the index's own fold binds *)
Definition uhole := "hole".
Definition utup := "tup".
Definition uacc := "acc".

Lemma utup_neq_uacc : utup <> uacc.
Proof. unfold utup, uacc; intro H; discriminate H. Qed.

Section WithConcreteMaps.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Definition row (i : Z) (n : string) : value :=
    VRecord [("id", VInt i); ("name", VString n)].

  Definition demo_rows : list value := [ row 1 "a"; row 2 "b" ].

  (* The index the table carries, as to_idx computes it. *)
  Definition demo_idx : value :=
    interp_expr (map.empty : clocals)
      (map.put map.empty uhole (VList demo_rows))
      (to_idx uhole "id" utup uacc).

  (* It is the dictionary sending each id to its row. *)
  Lemma demo_idx_value :
    demo_idx = VDict [ (VInt 1, row 1 "a"); (VInt 2, row 2 "b") ].
  Proof. reflexivity. Qed.

  Definition demo_Gstore : ctenv :=
    map.put (map.put map.empty "users" (TList row_ty)) "idx" (TDict TInt row_ty).

  Definition demo_Genv : ctenv := map.put map.empty "u" row_ty.

  Definition demo_store : clocals :=
    map.put (map.put map.empty "users" (VList demo_rows)) "idx" demo_idx.

  (* The guard the constraint elaboration inserts at "users := u :: !users". *)
  Definition declared_guard : expr :=
    constr_guard (unique_constr "id" row_ty) (get_free_vars demo_Genv)
      (EBinop OCons (EVar "u") (ELoc "users")).

  (* And the cheap one, which reads the index instead of the table. *)
  Definition index_guard : expr :=
    unique_guard "id" (ELoc "idx") "y" (EVar "u").

  (* ---------------------------------------------------------------------
     The two guards, computed.
     --------------------------------------------------------------------- *)

  Lemma demo_taken_key :
    interp_expr demo_store (map.put map.empty "u" (row 1 "c")) index_guard
    = VBool false
    /\ interp_expr demo_store (map.put map.empty "u" (row 1 "c")) declared_guard
       = VBool false.
  Proof. split; reflexivity. Qed.

  Lemma demo_fresh_key :
    interp_expr demo_store (map.put map.empty "u" (row 3 "c")) index_guard
    = VBool true
    /\ interp_expr demo_store (map.put map.empty "u" (row 3 "c")) declared_guard
       = VBool true.
  Proof. split; reflexivity. Qed.

  (* ---------------------------------------------------------------------
     Everything unique_guard_sound asks for, on this table.
     --------------------------------------------------------------------- *)

  Lemma row_ty_wf : type_wf row_ty.
  Proof. unfold row_ty; repeat constructor; cbn; intuition congruence. Qed.

  Lemma demo_Gstore_wf : tenv_wf demo_Gstore.
  Proof.
    unfold demo_Gstore.
    apply tenv_wf_step.
    1: apply tenv_wf_step; [ apply tenv_wf_empty | constructor; apply row_ty_wf ].
    1: constructor; [ constructor | apply row_ty_wf ].
  Qed.

  Lemma demo_Genv_wf : tenv_wf demo_Genv.
  Proof.
    unfold demo_Genv.
    apply tenv_wf_step; [ apply tenv_wf_empty | apply row_ty_wf ].
  Qed.

  Lemma demo_rows_ty : Forall (fun r => type_of_value r row_ty) demo_rows.
  Proof.
    unfold demo_rows, row, row_ty.
    repeat constructor; cbn; intuition congruence.
  Qed.

  (* The index is well typed because to_idx is, which is the index
     interface's own obligation rather than anything about this table. *)
  Lemma demo_idx_ty : type_of_value demo_idx (TDict TInt row_ty).
  Proof.
    unfold demo_idx.
    replace (TDict TInt row_ty) with (idx_ty "id" (TList row_ty)) by reflexivity.
    eapply type_sound.
    1: apply (to_idx_ty uhole "id" utup uacc utup_neq_uacc);
       [ constructor; apply row_ty_wf | reflexivity ].
    1: apply tenv_wf_empty.
    1: apply tenv_wf_step; [ apply tenv_wf_empty | constructor; apply row_ty_wf ].
    1: apply locals_wf_empty.
    1: apply locals_wf_step; [ apply locals_wf_empty | constructor; apply demo_rows_ty ].
  Qed.

  Lemma demo_store_wf : locals_wf demo_Gstore demo_store.
  Proof.
    unfold demo_Gstore, demo_store.
    apply locals_wf_step.
    1: apply locals_wf_step;
       [ apply locals_wf_empty | constructor; apply demo_rows_ty ].
    1: apply demo_idx_ty.
  Qed.

  (* The ids are distinct: this is what the declared primary key supplies, and
     what the index needs to stand for the table. *)
  Lemma demo_keys_NoDup : NoDup (List.map (row_key "id") demo_rows).
  Proof.
    unfold demo_rows, row, row_key; cbn [List.map record_proj access_record].
    repeat constructor; cbn; intuition congruence.
  Qed.

  Lemma demo_idx_wf : forall (env : clocals),
      idx_wf uhole "id" utup uacc (VList demo_rows)
        (interp_expr demo_store env (ELoc "idx")).
  Proof.
    intros. unfold idx_wf, demo_store.
    rewrite interp_ELoc. unfold get_local.
    rewrite map.get_put_same. reflexivity.
  Qed.

  (* So the cheap guard may replace the declared one at every write to this
     table, whatever row is written. *)
  Theorem demo_guards_agree : forall (env : clocals),
      locals_wf demo_Genv env ->
      interp_expr demo_store env index_guard
      = interp_expr demo_store env declared_guard.
  Proof.
    intros env H_env; unfold index_guard, declared_guard.
    eapply (unique_guard_sound uhole "id" utup uacc utup_neq_uacc)
      with (kt := TInt) (tbl := "users") (l := demo_rows)
           (Gstore := demo_Gstore) (Genv := demo_Genv).
    1: apply demo_Gstore_wf.
    1: apply demo_Genv_wf.
    1: apply row_ty_wf.
    1: reflexivity.
    1: unfold demo_Gstore; rewrite_map_get_put_goal; reflexivity.
    1: constructor; unfold demo_Genv; rewrite_map_get_put_goal; reflexivity.
    1: apply incl_refl.
    1: apply demo_store_wf.
    1: assumption.
    1: unfold demo_store; repeat rewrite_map_get_put_goal; reflexivity.
    1: apply demo_keys_NoDup.
    1: apply demo_idx_wf.
  Qed.

  (* The cheap guard is an ordinary boolean expression of the store. *)
  Lemma demo_unique_guard_ty :
    type_of demo_Gstore demo_Genv index_guard TBool.
  Proof.
    unfold index_guard.
    eapply unique_guard_ty with (rt := [("id", TInt); ("name", TString)]) (kt := TInt).
    1: reflexivity.
    1: constructor; unfold demo_Gstore; repeat rewrite_map_get_put_goal; reflexivity.
    1: constructor; unfold demo_Genv; rewrite_map_get_put_goal; reflexivity.
  Qed.
End WithConcreteMaps.
