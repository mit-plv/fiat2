(* ============================================================
   A PRIMARY KEY ON TWO ATTRIBUTES, AND ITS CHECK COMPILED TO ONE PROBE.

   A MEASURED SUBJECT -- eval/Extract.v lists it as composite_key_decl --
   written because the corpus had no witness for a declared composite key.
   The table declares (k1, k2) a key -- not either attribute alone -- and the
   program does the two things a declaration touches: a read at the composite
   key, and an insert, which is where the declaration is checked.

   WHAT IS WORTH READING IN THE TERMS BELOW: no rewrite was written for the
   check.  The declared constraint's body is a CONJUNCTION of per-attribute
   equalities (CompositeKeyCheck.eq_on_attrs), which is exactly the pattern
   CompositeDictIndexImpl's read rule already matches, so the O(n) scan the
   elaboration emits is turned into one probe into the composite index by a
   rule that existed before composite keys were declarable.  Had the
   constraint been stated as one comparison of key records -- shorter to
   reason about -- it would have compiled to nothing.

   And the row list is ERASED: the read is a probe, the check is a probe, and
   the insert maintains the index, so nothing reads the list and the table IS
   its index across a write.

   WHAT IT MEASURES (harness `csv typed 200 400 800 1600`; work at 1600 rows
   and the fitted exponent):

     kind          source     a     optimized     a      ratio
     readAtKey    1096780  1.00          1392  0.01      788x
     insert       1231335  0.98          2950  0.01      417x

   THE INSERT IS THE NUMBER THIS FILE EXISTS FOR, and it is an exponent, not
   a constant: 0.98 to 0.01.  A declared composite key costs a linear scan
   per write in the source and one probe in the optimized form.  The read's
   788x is the composite index doing what it already did.
   ============================================================ *)
Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.constraint.Decl fiat2.constraint.Surface fiat2.constraint.Constraint fiat2.constraint.CompositeKeyCheck fiat2.Substitute
  fiat2.constraint.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.rules.FlatmapForms fiat2.pipeline.Pipeline.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String ZArith List.

Import ListNotations.

Definition row_ty :=
  TRecord (record_sort [("k1", TString); ("k2", TString); ("v", TString)]).

Definition query_ty :=
  TRecord (record_sort
             [("kind", TInt); ("a", TString); ("b", TString);
              ("new_item", row_ty)]).

Section WithConcreteMaps.
  Notation value := (value).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Definition filt (pred : expr) : expr :=
    EUnop OLength
      (EFlatmap LikeList (ELoc "items") "r"
         (EIf pred (EBinop OCons (EVar "r") (EAtom (ANil None)))
            (EAtom (ANil None)))).

  Definition c1 : expr := EBinop OEq (EAccess (EVar "r") "k1") (EAccess (EVar "q") "a").
  Definition c2 : expr := EBinop OEq (EAccess (EVar "r") "k2") (EAccess (EVar "q") "b").

  Definition report (e : expr) : scommand :=
    SLet e "n"
      (SAssign "outputs"
         (EBinop OCons (EUnop OStringOfInt (EVar "n")) (ELoc "outputs")) SSkip).

  Definition dispatch (k : Z) (thn els : scommand) : scommand :=
    SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt k))) thn els.

  (*   0  a read at the composite key
       1  an insert, which is where the DECLARATION is checked *)
  Definition prog_s (ds : list decl) : scommand :=
    SLetConstrained "items" row_ty ds
      (SForeach (EVar "queries") "q"
         (dispatch 0 (report (filt (EBinop OAnd c1 c2)))
            (SAssign "items"
               (EBinop OCons (EAccess (EVar "q") "new_item") (ELoc "items"))
               SSkip))).

  Definition init_Gstore : ctenv := map.put map.empty "outputs" (TList TString).
  Definition init_Genv : ctenv := map.put map.empty "queries" (TList query_ty).

  Definition elaborated (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_s ds).

  (* THE DECLARATION: the pair is a key, not either attribute alone. *)
  Definition decls := [DUniqueMany ["k1"; "k2"]].

  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition anno : canno_command :=
    CAC (("items", (row_ty, decls)) :: cenv_rm "items" []) O
      basics [CompositeDictIdx ["k1"; "k2"]] [] (elaborated decls).

  Definition optimized : command :=
    apply_optimize_anno_constrained anno init_Gstore init_Genv.

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  Fixpoint peel (c : command) : command :=
    match c with
    | CLetMut _ _ c' => peel c'
    | CForeach _ _ c' => c'
    | _ => c
    end.

  Fixpoint read_branch (n : nat) (c : command) : option expr :=
    match n, c with
    | O, CIf _ (CLet e _ _) _ => Some e
    | O, CLet e _ _ => Some e
    | S n', CIf _ _ c' => read_branch n' c'
    | _, _ => None
    end.

  Definition query_at (n : nat) (c : command) : option expr :=
    read_branch n (peel c).

  Fixpoint write_branch (n : nat) (c : command) : option expr :=
    match n, c with
    | O, CIf _ (CAssign _ e) _ => Some e
    | O, CAssign _ e => Some e
    | S n', CIf _ _ c' => write_branch n' c'
    | _, _ => None
    end.

  Definition write_at (n : nat) (c : command) : option expr :=
    write_branch n (peel c).

  (* the test a checked write is guarded by *)
  Fixpoint guard_branch (n : nat) (c : command) : option expr :=
    match n, c with
    | O, CIf g (CAssign _ _) _ => Some g
    | S n', CIf _ _ c' => guard_branch n' c'
    | _, _ => None
    end.

  Definition guard_at (n : nat) (c : command) : option expr :=
    guard_branch n (peel c).

  (* ---- what the terms are written in ---- *)

  Definition mem (t : string) : expr :=
    EAccess (EAccess (ELoc "items") "aux_tag") t.
  Definition ckey_of_row (r : string) : expr :=
    ERecord [("k1", EAccess (EVar r) "k1"); ("k2", EAccess (EVar r) "k2")].
  Definition ckey_of_q : expr :=
    ERecord [("k1", EAccess (EVar "q") "a"); ("k2", EAccess (EVar "q") "b")].
  Definition probe_at (k : expr) : expr :=
    EOptMatch (EBinop OLookup (mem "0") k) (EAtom (AEmptyBag None)) "b" (EVar "b").

  (* ---- THE POINT: the declared key's check is one probe ----

     "the bucket at the new row's composite key is empty".  The row is bound
     to pk_row first, which is what makes the check capture-free whatever the
     row expression is; the trailing `true` is the rest of the declaration
     list, which is empty. *)
  Lemma declared_key_check_is_one_probe :
    guard_at 1 optimized
    = Some (EBinop OAnd
              (ELet (EAccess (EVar "q") "new_item") pk_row
                 (EBinop OEq (probe_at (ckey_of_row pk_row))
                    (EAtom (AEmptyBag None))))
              (EAtom (ABool true))).
  Proof. vm_compute; reflexivity. Qed.

  Lemma read_is_one_probe :
    query_at 0 optimized = Some (EACFold AGCount (probe_at ckey_of_q)).
  Proof. vm_compute; reflexivity. Qed.

  (* the insert maintains the index rather than rebuilding it *)
  Lemma insert_maintains_the_index :
    write_at 1 optimized
    = Some (ERecord
              [("aux_tag",
                 ERecord
                   [("0",
                      ELet (EAccess (EVar "q") "new_item") "tup"
                        (ELet (mem "0") "acc"
                           (ETernop OInsert (EVar "acc") (ckey_of_row "tup")
                              (EBinop OBagInsert
                                 (EOptMatch
                                    (EBinop OLookup (EVar "acc")
                                       (ckey_of_row "tup"))
                                    (EAtom (AEmptyBag None)) "x" (EVar "x"))
                                 (EVar "tup")))))])]).
  Proof. vm_compute; reflexivity. Qed.

  (* and so nothing reads the row list: the table IS its index, across a
     write and across a checked one *)
  Lemma the_table_is_its_index :
    installed_fields optimized = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ---- and it is all sound ---- *)

  Lemma row_ty_wf : type_wf row_ty.
  Proof. unfold row_ty; repeat constructor; cbn; intuition congruence. Qed.

  Lemma query_ty_wf : type_wf query_ty.
  Proof. unfold query_ty, row_ty; repeat constructor; cbn; intuition congruence. Qed.

  Lemma init_Gstore_wf : tenv_wf init_Gstore.
  Proof.
    unfold init_Gstore.
    apply tenv_wf_step; [ apply tenv_wf_empty | repeat constructor ].
  Qed.

  Lemma init_Genv_wf : tenv_wf init_Genv.
  Proof.
    unfold init_Genv.
    apply tenv_wf_step; [ apply tenv_wf_empty | constructor; apply query_ty_wf ].
  Qed.

  (* The declaration's own well-formedness: the attributes are distinct and
     are fields of the row type.  Both are decidable and checked here, where
     the declaration is written. *)
  Lemma decls_wf : Forall (decl_wf (tenv:=ctenv) row_ty) decls.
  Proof.
    unfold decls, row_ty; cbn [decl_wf].
    repeat constructor;
      exists [("k1", TString); ("k2", TString); ("v", TString)];
      split; [ reflexivity | split ].
    1:{ repeat constructor; cbn; intuition congruence. }
    1:{ repeat constructor; cbn; intuition congruence. }
  Qed.

  Lemma elaborated_well_typed :
    well_typed init_Gstore init_Genv (elaborated decls).
  Proof.
    eapply command_typechecker_sound with (c := elaborated decls).
    1: apply init_Gstore_wf.
    1: apply init_Genv_wf.
    reflexivity.
  Qed.

  Theorem optimized_sound :
    well_typed init_Gstore init_Genv optimized /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized
        = interp_command store env (elaborated decls).
  Proof.
    unfold optimized, anno, elaborated, prog_s.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply row_ty_wf
      | apply incl_refl | apply decls_wf | apply elaborated_well_typed ].
  Qed.
End WithConcreteMaps.
