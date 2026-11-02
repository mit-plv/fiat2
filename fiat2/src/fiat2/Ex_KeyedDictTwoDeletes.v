Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.FlatmapForms fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   THE SAME TWO DELETES AT A SINGLE-ATTRIBUTE DICTIONARY.

   A regression test, not an evaluation subject.  Ex_CompositeKeyedDelete is
   this file at a composite key; this one is the arity-one case, and it
   exists to MEASURE whether the gap that file closed is worth closing here
   too.  The table carries a dictionary bucketed on fl and declares id
   unique -- OptimizeAnno's KeyedDictIdx -- and the program deletes in both
   shapes the pair can be asked for:

     * AT THE BUCKETING ATTRIBUTE -- a filter naming fl.  Served by the
       dictionary's own rule with no declaration: every row in the bucket
       leaves, so the entry goes with one ODelete.
     * AT THE DECLARED KEY -- a filter naming id, which the dictionary is
       not keyed on.  Only the pair's gated rule can serve it, by probing
       the primary-key member for the leaving row and taking that row out
       of the one bucket its fl names.

   WHY THE ARITY MATTERS HERE and did not there: a composite key was unique
   per row, so a bucket held ONE row.  A dictionary bucketed on one
   attribute is a secondary index, so a bucket holds MANY rows, and a delete
   at fl removes all of them.  Any correct implementation of that operation
   is therefore Omega(bucket), which is the thing to keep in view when
   reading the numbers below.

   THE GENERATOR'S BUCKET POLICY, because the first number depends on it.
   harness/gen.ml keeps one bucket per bucket_size rows, so the number of
   distinct fl values grows with the table and a bucket stays bounded -- the
   same policy eval/HA_AreaRegistry's generator uses, which is the eval
   subject for this index.  Under that policy a delete at fl touches a
   bounded number of rows, so serving it is a change of exponent.  Under the
   opposite policy -- a CONSTANT number of floors, which is the more faithful
   reading of a house and the deviation eval/HA_EntityRegistry documents for
   domains -- a floor's bucket grows with the table, the operation is
   inherently linear, and the same rule would buy a constant there instead.
   The second number below, the delete at the declared key, does not depend
   on the policy either way.
   WHAT IT MEASURED, and the measurement is why DictBucketPkDelete exists
   (harness `csv typed 200 400 800 1600`; work at 1600 rows and the fitted
   exponent).  Two programs: keyed_two_deletes is the one above and
   keyed_dict_delete drops kind 2, which isolates the keyed delete.

   keyed_two_deletes, after the rule against the same column before it:

     kind            source     a     before     a      after     a
     readAtFloor     554160  0.99       1180  0.00       1180  0.00
     insert          724170  0.98       3822  0.01       3502  0.01
     deleteAtFloor   687680  1.21    2051550  1.22       8880  0.04
     deleteById      780290  1.02     791630  0.97      11980  0.01

   BEFORE THE RULE, BOTH DELETES WERE LOST.  The delete at fl was 2051550 at
   a=1.22, which is 3.0x WORSE than the source's own filter -- the
   primary-key member was rebuilt from the surviving rows, which costs more
   than the filter the source already wrote -- and the rebuild kept the row
   list installed, which took the keyed delete from 66x to 1.0x and its
   exponent from 0.01 to 0.97.  That is a worse regression than the composite
   case's 2.5x, and it is the measurement that justified the rule.

   AFTER, deleteAtFloor is 77x and deleteById is 65.1x against the control's
   66.2x -- the keyed delete is back to what it costs when nothing else
   touches the table, and the row list is erased
   (the_table_is_its_two_indexes).

   READ deleteAtFloor's 0.04 HONESTLY: it is not 0.01 because the emitted
   fold walks the bucket, and the bucket is bounded by the generator's policy
   rather than by the rule.  Under a constant number of floors a bucket would
   grow with the table and that operation would stay linear, at a smaller
   constant than the source's.  deleteById's exponent does not depend on the
   policy either way, and neither does the erasure of the list.

   AND NO EVALUATION NUMBER MOVED.  eval/HA_AreaRegistry is the eval subject
   for this index and the only other KeyedDictIdx in the tree; its program
   deletes only by the declared key -- as the source's __delitem__ does -- so
   this rule cannot fire there, and its three measurements are unchanged to
   the digit.  The gap is real in the rules and has no witness in the
   witnessed code, which is why this file is a regression test and not an
   evaluation subject.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort
             [("id", TString); ("fl", TString); ("v", TString)]).

Definition query_ty :=
  TRecord (record_sort
             [("kind", TInt); ("fl", TString); ("k", TString);
              ("new_item", row_ty)]).

Section WithConcreteMaps.
  Notation value := (value).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* [r <- items, check(pred), ret r], counted *)
  Definition filt (pred : expr) : expr :=
    EUnop OLength
      (EFlatmap LikeList (ELoc "items") "r"
         (EIf pred (EBinop OCons (EVar "r") (EAtom (ANil None)))
            (EAtom (ANil None)))).

  Definition c_fl : expr :=
    EBinop OEq (EAccess (EVar "r") "fl") (EAccess (EVar "q") "fl").
  Definition c_id : expr :=
    EBinop OEq (EAccess (EVar "r") "id") (EAccess (EVar "q") "k").

  (* keep the rows the bucketing attribute does NOT name *)
  Definition drop_at_fl : expr :=
    EFlatmap LikeList (ELoc "items") "r"
      (EIf (EUnop ONot c_fl)
         (EBinop OCons (EVar "r") (EAtom (ANil None))) (EAtom (ANil None))).

  (* keep the rows whose DECLARED key is not the one named *)
  Definition drop_at_id : expr :=
    EFlatmap LikeList (ELoc "items") "r"
      (EIf (EUnop ONot c_id)
         (EBinop OCons (EVar "r") (EAtom (ANil None))) (EAtom (ANil None))).

  Definition report (e : expr) : scommand :=
    SLet e "n"
      (SAssign "outputs"
         (EBinop OCons (EUnop OStringOfInt (EVar "n")) (ELoc "outputs")) SSkip).

  Definition dispatch (k : Z) (thn els : scommand) : scommand :=
    SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt k))) thn els.

  (*   0  read at the bucketing attribute
       1  an insert
       2  a delete AT the bucketing attribute   (needs no declaration)
       3  a delete at the DECLARED key          (gated on it) *)
  Definition prog_s (ds : list decl) : scommand :=
    SLetConstrained "items" row_ty ds
      (SForeach (EVar "queries") "q"
         (dispatch 0 (report (filt c_fl))
            (dispatch 1
               (SAssign "items"
                  (EBinop OCons (EAccess (EVar "q") "new_item") (ELoc "items")) SSkip)
               (dispatch 2
                  (SAssign "items" drop_at_fl SSkip)
                  (SAssign "items" drop_at_id SSkip))))).

  (* THE SAME TABLE WITHOUT THE DELETE AT THE BUCKETING ATTRIBUTE, which is
     what isolates the keyed delete: the difference between the two programs
     is that one write and nothing else. *)
  Definition prog_keyed_s (ds : list decl) : scommand :=
    SLetConstrained "items" row_ty ds
      (SForeach (EVar "queries") "q"
         (dispatch 0 (report (filt c_fl))
            (dispatch 1
               (SAssign "items"
                  (EBinop OCons (EAccess (EVar "q") "new_item") (ELoc "items")) SSkip)
               (SAssign "items" drop_at_id SSkip)))).

  Definition init_Gstore : ctenv := map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv := map.put map.empty "queries" (TList query_ty).

  Definition elaborated (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_s ds).

  Definition elaborated_keyed (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_keyed_s ds).

  Definition decls := [DUnique "id"].

  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition anno : canno_command :=
    CAC (("items", (row_ty, decls)) :: cenv_rm "items" []) O
      basics [KeyedDictIdx "fl" "id"] [] (elaborated decls).

  Definition optimized : command :=
    apply_optimize_anno_constrained anno init_Gstore init_Genv.

  Definition anno_keyed : canno_command :=
    CAC (("items", (row_ty, decls)) :: cenv_rm "items" []) O
      basics [KeyedDictIdx "fl" "id"] [] (elaborated_keyed decls).

  Definition optimized_keyed : command :=
    apply_optimize_anno_constrained anno_keyed init_Gstore init_Genv.

  (* ---- projections, the same ones Ex_CompositeKeyedDelete uses ---- *)

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

  Fixpoint write_branch (n : nat) (c : command) : option expr :=
    match n, c with
    | O, CIf _ (CAssign _ e) _ => Some e
    | O, CIf _ (CIf _ (CAssign _ e) _) _ => Some e
    | O, CAssign _ e => Some e
    | S n', CIf _ _ c' => write_branch n' c'
    | _, _ => None
    end.

  Definition write_at (n : nat) (c : command) : option expr :=
    write_branch n (peel c).

  Fixpoint read_branch (n : nat) (c : command) : option expr :=
    match n, c with
    | O, CIf _ (CLet e _ _) _ => Some e
    | O, CLet e _ _ => Some e
    | S n', CIf _ _ c' => read_branch n' c'
    | _, _ => None
    end.

  Definition query_at (n : nat) (c : command) : option expr :=
    read_branch n (peel c).

  Fixpoint assoc_expr (k : string) (l : list (string * expr)) : option expr :=
    match l with
    | [] => None
    | (k', e) :: l' => if String.eqb k k' then Some e else assoc_expr k l'
    end.

  Definition member_at (n : nat) (tg : string) (c : command) : option expr :=
    match write_at n c with
    | Some (ERecord l) =>
        match assoc_expr "aux_tag" l with
        | Some (ERecord al) => assoc_expr tg al
        | _ => None
        end
    | _ => None
    end.

  Definition list_at (n : nat) (c : command) : option expr :=
    match write_at n c with
    | Some (ERecord l) => assoc_expr "id_tag" l
    | _ => None
    end.

  Definition rebuild_src (e : option expr) : option expr :=
    match e with
    | Some (EFold d _ _ _ _) => Some d
    | _ => None
    end.

  (* ---- what the terms are written in ---- *)

  Definition mem (t : string) : expr :=
    EAccess (EAccess (ELoc "items") "aux_tag") t.
  Definition list_e : expr := EAccess (ELoc "items") "id_tag".
  Definition q_fld (f : string) : expr := EAccess (EVar "q") f.

  (* ---- what the pipeline does with it ---- *)

  (* the read at the bucketing attribute: one probe, the bucket counted *)
  Lemma read_is_one_probe :
    query_at 0 optimized
    = Some (EACFold AGCount
              (EOptMatch (EBinop OLookup (mem "0") (q_fld "fl"))
                 (EAtom (AEmptyBag None)) "b" (EVar "b"))).
  Proof. vm_compute; reflexivity. Qed.

  (* the delete at the bucketing attribute: the dictionary's own rule, which
     needs no declaration -- the whole entry leaves *)
  Lemma delete_at_floor_is_one_odelete :
    member_at 2 "0" optimized
    = Some (EBinop ODelete (mem "0") (q_fld "fl")).
  Proof. vm_compute; reflexivity. Qed.

  (* AND ITS OTHER MEMBER, which is what this file was built to price.  The
     primary-key member is keyed on id, which this filter does not name, so
     no rule can read off which entries leave -- but the dictionary's bucket
     at the deleted fl holds exactly the rows that are leaving, so their ids
     are deleted one at a time.  Before DictBucketPkDelete this member was
     REBUILT from the surviving rows. *)
  Lemma delete_at_floor_maintains_the_key_member :
    member_at 2 "1" optimized
    = Some (ELet (mem "1") "acc"
              (EOptMatch (EBinop OLookup (mem "0") (q_fld "fl"))
                 (EVar "acc") "bkt"
                 (EFold (ESort LikeBag (EVar "bkt")) (EVar "acc") "tup" "acc"
                    (EBinop ODelete (EVar "acc")
                       (EAccess (EVar "tup") "id"))))).
  Proof. vm_compute; reflexivity. Qed.

  (* and the delete at the declared key still drops one entry with one
     ODelete, as it did before *)
  Lemma keyed_delete_is_one_odelete_on_the_key_member :
    member_at 3 "1" optimized
    = Some (EBinop ODelete (mem "1") (q_fld "k")).
  Proof. vm_compute; reflexivity. Qed.

  (* ---- what is installed ----

     THE TABLE IS ITS TWO INDEXES, across both deletes.  The row list is
     erased: the rebuild above was its only remaining reader.  Before the
     rule it was ["id_tag"; "aux_tag"], and with the list installed every
     write paid a linear pass over it. *)
  Lemma the_table_is_its_two_indexes :
    installed_fields optimized = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* the control program erases it too, and did before *)
  Lemma keyed_only_erases_the_list :
    installed_fields optimized_keyed = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* and no write anywhere carries a row list *)
  Lemma no_write_keeps_a_row_list :
    list_at 3 optimized = None.
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

  Lemma decls_wf : Forall (decl_wf (tenv:=ctenv) row_ty) decls.
  Proof.
    unfold decls, row_ty; cbn [decl_wf].
    repeat constructor;
      exists [("fl", TString); ("id", TString); ("v", TString)], TString;
      split; reflexivity.
  Qed.

  Lemma elaborated_well_typed :
    well_typed init_Gstore init_Genv (elaborated decls).
  Proof.
    eapply command_typechecker_sound with (c := elaborated decls).
    1: apply init_Gstore_wf.
    1: apply init_Genv_wf.
    reflexivity.
  Qed.

  Lemma elaborated_keyed_well_typed :
    well_typed init_Gstore init_Genv (elaborated_keyed decls).
  Proof.
    eapply command_typechecker_sound with (c := elaborated_keyed decls).
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

  Theorem optimized_keyed_sound :
    well_typed init_Gstore init_Genv optimized_keyed /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized_keyed
        = interp_command store env (elaborated_keyed decls).
  Proof.
    unfold optimized_keyed, anno_keyed, elaborated_keyed, prog_keyed_s.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply row_ty_wf
      | apply incl_refl | apply decls_wf | apply elaborated_keyed_well_typed ].
  Qed.
End WithConcreteMaps.
