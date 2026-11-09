(* ====================================================================
   AN INSERT AT THE END OF THE LIST, maintained incrementally.

   Every other example in this development conses its new row onto the
   FRONT of the table.  That was never a modelling choice: the cons was the
   only shape an index-maintenance rule recognised, so writing the append
   that real code performs -- a Java ArrayList.add, a Python list.append --
   would have cost the whole index and left the read a scan.  OConcat was
   typed, had notation, and no rule in the tree used it.

   This file is the evidence that it now costs nothing.  The program is
   Ex_Sum's, with its ONE write turned from

     orders := q.new_order :: !orders        (a cons at the front)

   into

     orders := !orders ++ [q.new_order]      (an append at the end)

   and nothing else changed.  What the pins below say is that the optimized
   program is incremental anyway: the read is one cached field, the write is
   one addition, and the row list is gone.
   ==================================================================== *)
Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem
  fiat2.TypeSound fiat2.TransfSound fiat2.IndexInterface fiat2.rules.CollectionTransf
  fiat2.index.DictIndexImpl fiat2.index.SumAgg fiat2.index.MinAgg fiat2.TransfUtils
  fiat2.rules.FlatmapTransf fiat2.index.IndexTransf fiat2.Utils fiat2.Substitute
  fiat2.pipeline.Pipeline fiat2.constraint.Decl fiat2.constraint.Surface fiat2.constraint.PrimaryKeyCheck.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString
  coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.
Import ListNotations.

Definition row_ty_orders :=
  TRecord (record_sort [("id", TInt); ("value", TInt)]).

Definition row_ty_query :=
  TRecord (record_sort [("type", TInt); ("new_order", row_ty_orders)]).

(* the read: the total over the table, written as the fold the surface
   language elaborates to *)
Definition read_total : expr :=
  EFold (EFlatmap LikeList (ELoc "orders") "o"
           (EBinop OCons (EAccess (EVar "o") "value") (EAtom (ANil None))))
    (EAtom (AInt 0)) "_v" "_acc" (EBinop OPlus (EVar "_v") (EVar "_acc")).

Definition report : command :=
  CLet read_total "total"
    (CAssign "output"
       (EBinop OConcatString (EAtom (AString "Current total value: "))
          (EBinop OConcatString (EUnop OStringOfInt (EVar "total"))
             (EAtom (AString "\n"))))).

(* the two writes, which are the only difference between the two programs *)
Definition write_cons : expr :=
  EBinop OCons (EAccess (EVar "q") "new_order") (ELoc "orders").

Definition write_snoc : expr :=
  EBinop OConcat (ELoc "orders")
    (EBinop OCons (EAccess (EVar "q") "new_order") (EAtom (ANil None))).

Definition prog_with (w : expr) : command :=
  CLetMut (EVar "orders_tbl") "orders"
    (CForeach (EVar "queries") "q"
       (CLetMut (EAtom (AString "")) "output"
          (CSeq
             (CIf (EBinop OEq (EAccess (EVar "q") "type") (EAtom (AInt 0)))
                report
                (CSeq (CAssign "orders" w)
                   (CAssign "output" (EAtom (AString "Added a new order\n")))))
             (CAssign "outputs" (EBinop OCons (ELoc "output") (ELoc "outputs")))))).

Definition prog_cons := prog_with write_cons.
Definition prog_snoc := prog_with write_snoc.

Definition heuristics :=
  [ AC [PushdownCollection; AnnotateCollection] [[SumAgg "value"]] ].

Section WithConcreteMaps.
  Notation value := (value).
  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.
  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put (map.put map.empty "orders_tbl" (TList row_ty_orders))
      "queries" (TList row_ty_query).

  (* both programs are well typed, so the append is not merely tolerated by
     the optimizer -- it is a program the language already accepted *)
  Definition checks (c : command) : bool :=
    match typecheck init_Gstore init_Genv c with
    | Success _ => true
    | Failure _ => false
    end.

  Lemma prog_cons_typechecks : checks prog_cons = true.
  Proof. vm_compute; reflexivity. Qed.

  Lemma prog_snoc_typechecks : checks prog_snoc = true.
  Proof. vm_compute; reflexivity. Qed.

  Definition optimized (c : command) : command :=
    apply_optimize_anno
      (AC [PushdownCollection; AnnotateCollection] [[SumAgg "value"]] c)
      init_Gstore init_Genv.

  (* ------------------------------------------------------------------
     The projections the pins read off.
     ------------------------------------------------------------------ *)
  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  (* the value assigned to the table in the write branch *)
  Fixpoint write_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ c' | CForeach _ _ c' => write_of c'
    | CSeq c1 c2 => match write_of c1 with
                    | Some e => Some e
                    | None => write_of c2
                    end
    | CIf _ _ c' => write_of c'
    | CAssign "orders" e => Some e
    | _ => None
    end.

  (* the expression the read is bound to *)
  Fixpoint read_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ c' | CForeach _ _ c' => read_of c'
    | CSeq c1 c2 => match read_of c1 with
                    | Some e => Some e
                    | None => read_of c2
                    end
    | CIf _ c' _ => read_of c'
    | CLet e _ _ => Some e
    | _ => None
    end.

  (* ------------------------------------------------------------------
     THE PINS.

     First: the row LIST IS GONE.  Only the aggregate's record remains, so
     the table IS its index -- the same outcome a cons gets, from a write
     that until now would have defeated the index entirely.
     ------------------------------------------------------------------ *)
  Lemma snoc_erases_the_list :
    installed_fields (optimized prog_snoc) = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* and the cons does the same, so the append is not a special case *)
  Lemma cons_erases_the_list :
    installed_fields (optimized prog_cons) = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* Second: the WRITE is one addition.  No fold over the table appears in
     it, which is the whole claim -- the appended row's value is added to the
     stored total. *)
  Lemma snoc_write_is_incremental :
    write_of (optimized prog_snoc)
    = Some (ERecord
              [("aux_tag",
                 ERecord
                   [("0",
                      EBinop OPlus
                        (ELet (EAccess (EVar "q") "new_order") "x"
                           (EAccess (EVar "x") "value"))
                        (EAccess (EAccess (ELoc "orders") "aux_tag") "0"))])]).
  Proof. vm_compute; reflexivity. Qed.

  (* Third: the READ is one cached field, not a scan *)
  Lemma snoc_read_is_a_field :
    read_of (optimized prog_snoc)
    = Some (EAccess (EAccess (ELoc "orders") "aux_tag") "0").
  Proof. vm_compute; reflexivity. Qed.

  (* And the two programs' optimized writes differ ONLY in the order the
     addition is written, which is what "the append costs nothing" means. *)
  Lemma cons_write_is_incremental :
    write_of (optimized prog_cons)
    = Some (ERecord
              [("aux_tag",
                 ERecord
                   [("0",
                      EBinop OPlus
                        (ELet (EAccess (EVar "q") "new_order") "x"
                           (EAccess (EVar "x") "value"))
                        (EAccess (EAccess (ELoc "orders") "aux_tag") "0"))])]).
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     AND THE GUARD SIDE.  Maintenance being incremental is only half of
     affordable: under a DECLARED key the write also has to be CHECKED, and
     until classify_write recognised an append that check read the whole
     table once per row.  These three pins say it now takes the same cheap
     path a cons takes, and that the recogniser is not vacuous.
     ------------------------------------------------------------------ *)
  Definition the_append : expr :=
    EBinop OConcat (ELoc "orders")
      (EBinop OCons (EAccess (EVar "q") "new_order") (EAtom (ANil None))).

  Lemma append_is_recognised :
    classify_write "orders" the_append
    = WSnoc (EAccess (EVar "q") "new_order").
  Proof. vm_compute; reflexivity. Qed.

  (* the cheap guard, which probes the key, rather than constr_guard, which
     quantifies over the rows *)
  Lemma append_gets_the_cheap_key_guard :
    decl_guard row_ty_orders "orders" [] (DUnique "id") the_append
    = unique_guard_let "orders" "id" (EAccess (EVar "q") "new_order").
  Proof. vm_compute; reflexivity. Qed.

  (* NEGATIVE CONTROL: an append of the table to ITSELF adds more than one
     row, so it is not recognised and still falls back on the general guard *)
  Lemma self_append_is_not_recognised :
    classify_write "orders" (EBinop OConcat (ELoc "orders") (ELoc "orders"))
    = WOther.
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     And both are sound: each optimized program computes what its own source
     computes, on every store and environment.
     ------------------------------------------------------------------ *)
  Theorem optimized_snoc_sound : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      interp_command store env (optimized prog_snoc)
      = interp_command store env prog_snoc.
  Proof.
    unfold optimized, apply_optimize_anno; intros.
    eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
  Qed.

  Theorem optimized_cons_sound : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      interp_command store env (optimized prog_cons)
      = interp_command store env prog_cons.
  Proof.
    unfold optimized, apply_optimize_anno; intros.
    eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
  Qed.
End WithConcreteMaps.
