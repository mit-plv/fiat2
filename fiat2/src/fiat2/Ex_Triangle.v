Require Import fiat2.Selector fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.SumAgg fiat2.MinAgg fiat2.TransfUtils fiat2.FlatmapTransf fiat2.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.OptimizeAnno fiat2.ToPython.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.

Import ListNotations.

(*
(* Example application for adding edges to a graph and printing all triangles in the graph.
Triple self-join, filter pushdown, index creation and incremental updates *)

let mut edges := edges_tbl in

foreach q in queries do
    if q.type = 0
    then
        let triangles =
            sort [ e1 <- !edges,
                e2 <- !edges,
                e3 <- !edges,
                check(e2.src = e1.dst),
                check(e3.src = e2.dst),
                check(e1.dst = e3.dst),
                check(e1.src < e1.dst && e2.src < e2.dst),
                ret { p1: e1.src, p2: e2.src, p3: e3.src } ] in
        let mut result := "" in
        foreach tri in triangles do
            result := !result ++ str(tri.p1) ++ ", " ++
                str(tri.p2) ++ ", " ++ str(tri.p3) ++ "\n"
        end;
        outputs := !result :: !outputs
    else
        edges := q.new_edge :: !edges;
        outputs := "New edge added successfully\n" :: !outputs
    end
end
 *)

Definition prog := (CLetMut (EVar "edges_tbl") "edges" (CForeach (EVar "queries") "q" (CIf (EBinop OEq (EAccess (EVar "q") "type") (EAtom (AInt 0))) (CLet (ESort LikeList (EFlatmap LikeList (ELoc "edges") "e1" (EFlatmap LikeList (ELoc "edges") "e2" (EFlatmap LikeList (ELoc "edges") "e3" (EIf (EBinop OEq (EAccess (EVar "e2") "src") (EAccess (EVar "e1") "dst")) (EIf (EBinop OEq (EAccess (EVar "e3") "src") (EAccess (EVar "e2") "dst")) (EIf (EBinop OEq (EAccess (EVar "e1") "dst") (EAccess (EVar "e3") "dst")) (EIf (EBinop OAnd (EBinop OLess (EAccess (EVar "e1") "src") (EAccess (EVar "e1") "dst")) (EBinop OLess (EAccess (EVar "e2") "src") (EAccess (EVar "e2") "dst"))) (EBinop OCons (ERecord [("p1", (EAccess (EVar "e1") "src")); ("p2", (EAccess (EVar "e2") "src")); ("p3", (EAccess (EVar "e3") "src"))]) (EAtom (ANil None))) (EAtom (ANil None))) (EAtom (ANil None))) (EAtom (ANil None))) (EAtom (ANil None))))))) "triangles" (CLetMut (EAtom (AString "")) "result" (CSeq (CForeach (EVar "triangles") "tri" (CAssign "result" (EBinop OConcatString (ELoc "result") (EBinop OConcatString (EUnop OIntToString (EAccess (EVar "tri") "p1")) (EBinop OConcatString (EAtom (AString ", ")) (EBinop OConcatString (EUnop OIntToString (EAccess (EVar "tri") "p2")) (EBinop OConcatString (EAtom (AString ", ")) (EBinop OConcatString (EUnop OIntToString (EAccess (EVar "tri") "p3")) (EAtom (AString "\n")))))))))) (CAssign "outputs" (EBinop OCons (ELoc "result") (ELoc "outputs")))))) (CSeq (CAssign "edges" (EBinop OCons (EAccess (EVar "q") "new_edge") (ELoc "edges"))) (CAssign "outputs" (EBinop OCons (EAtom (AString "New edge added successfully\n")) (ELoc "outputs"))))))).

(* Adapted by hand from the Claude Sonnet 4.6 heuristics after EFilter/EProj/EJoin
   were removed from the rewrite menu: ToFilter is dropped, since filters now stay
   flatmaps. *)
Definition heuristics :=
[ AC [PushdownCollection; AnnotateCollection;
      IfNilIntoFlatmap; IfNilIntoFlatmap;
      SwapFlatmapIf]
     [[DictIdx "src"]]
; AC [PushdownCollection; AnnotateCollection;
      IfNilIntoFlatmap; IfNilIntoFlatmap;
      SwapIfNil; SwapFlatmapIf]
     [[DictIdx "src"; DictIdx "dst"]]
; AC [PushdownCollection; AnnotateCollection;
      IfNilIntoFlatmap; IfNilIntoFlatmap;
      SwapFlatmapIf;
      SwapIfNil; SwapIfNil;
      SwapFlatmapIf;
      SwapIfNil; SwapIfNil;
      SwapFlatmapIf;
      SwapIfNil; SwapIfNil; SwapIfNil;
      SwapFlatmapIf;
      SplitIf]
    [[DictIdx "src"]]
  ; AC [PushdownCollection; AnnotateCollection;
    SwapFlatmapIf; SwapIfNil; SwapFlatmapIf; SwapFlatmapIf; SwapIfNil;
    IfNilIntoFlatmap; IfNilIntoFlatmap;
    SwapFlatmapIf; SplitIf]
   [[DictIdx "src"]]
].

Definition row_ty_edges :=
  TRecord (record_sort [("src", TInt); ("dst", TInt)]).

Definition row_ty_query :=
  TRecord (record_sort [("type", TInt); ("new_edge", row_ty_edges)]).

Definition row_ty_triangle :=
  TRecord (record_sort [("p1", TInt); ("p2", TInt); ("p3", TInt)]).

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
    map.put (map.put map.empty
               "edges_tbl" (TList row_ty_edges))
      "queries" (TList row_ty_query).

  Compute (typecheck init_Gstore init_Genv prog).

  Definition prog_transformed := map (fun heu => apply_optimize_anno (heu prog) init_Gstore init_Genv) heuristics.

  Compute prog_transformed.

  (* ------------------------------------------------------------------
     WHAT THE SELECTOR DOES WITH A JOIN, which is the point of the four
     hand-written configurations above and of their replacement.

     A join's conditions are a chain of nil-guards at the innermost body,
     and each belongs to the innermost loop that binds all its variables.
     The ones written above the useful one do not mention the inner loop's
     variable at all, so what the index rules read is a condition that is
     constant in that loop: `if_nil_into_flatmap_head` splits on it and
     produces a filter that filters nothing.  The four configurations above
     fix that by hand, with chains of SwapIfNil and SwapFlatmapIf found per
     configuration.

     None of that was ever necessary.  `swap_flatmap_if_head` is ALREADY
     directed -- it fires only when the guard does not mention the loop
     variable, and firing removes that guard from the body, so it cannot
     undo itself and needs no ordering decision.  What was missing is that
     `basics_of` never emitted it.  It does now, on a demand (`DHoist`)
     whose detection is the rule's own guard, and the selector reaches this
     join with no hand-written chain at all:

       select_basics  = [PushdownCollection; AnnotateCollection;
                         IfNilIntoFlatmap; SwapFlatmapIf]
       select_choices = [DictIdx "src"]

     pinned in eval/SelectorTests.v.  Counting probes -- each one a scan the
     rules turned into a lookup -- that configuration reaches FOUR, which is
     what the best of the four hand-written chains reaches (they reach 4, 5,
     3 and 4, and the 5 uses two indexes).  Before the demand existed the
     selector reached TWO.

     THE HEADROOM, stated because the count makes it visible.  The same
     uniform basics list with `[DictIdx "src"; DictIdx "dst"]` reaches SIX,
     more than any configuration here.  The selector asks for `src` and not
     `dst` because the `dst` equality sits BEHIND the `src` one in the guard
     chain, and the demand analysis reads the guard the rules will see.
     Promoting a second indexable guard over the first needs to know which
     attributes are indexed, which is decided in a later phase than the one
     that would have to do the promoting -- so this is the join limit that
     remains, and it is a different one from the limit this change closed.
     A probe count is a count and not a measurement; this subject is not in
     the harness. *)

  Fixpoint probes_e (e : expr) : nat :=
    match e with
    | EBinop OLookup a b => S (Nat.add (probes_e a) (probes_e b))
    | EBinop _ a b => Nat.add (probes_e a) (probes_e b)
    | EUnop _ a => probes_e a
    | ETernop _ a b c =>
        Nat.add (probes_e a) (Nat.add (probes_e b) (probes_e c))
    | EIf a b c => Nat.add (probes_e a) (Nat.add (probes_e b) (probes_e c))
    | ELet a _ b => Nat.add (probes_e a) (probes_e b)
    | EFlatmap _ a _ b => Nat.add (probes_e a) (probes_e b)
    | EFold a b _ _ c =>
        Nat.add (probes_e a) (Nat.add (probes_e b) (probes_e c))
    | EACFold _ a | EACIFold _ a => probes_e a
    | EAccess a _ => probes_e a
    | EOptMatch a b _ c =>
        Nat.add (probes_e a) (Nat.add (probes_e b) (probes_e c))
    | ESort _ a | EBagOf a | ESetOf a => probes_e a
    | ERecord l => fold_right (fun p acc => Nat.add (probes_e (snd p)) acc) O l
    | _ => O
    end.

  Fixpoint probes (c : command) : nat :=
    match c with
    | CSkip => O
    | CSeq a b => Nat.add (probes a) (probes b)
    | CLet e _ c | CLetMut e _ c => Nat.add (probes_e e) (probes c)
    | CAssign _ e => probes_e e
    | CIf e a b => Nat.add (probes_e e) (Nat.add (probes a) (probes b))
    | CForeach e _ c => Nat.add (probes_e e) (probes c)
    end.

  (* the configuration the selector computes, with no chain written by hand *)
  Definition selected : command :=
    apply_optimize_anno
      (AC (select_basics [] "edges" prog) [select_choices [] "edges" prog] prog)
      init_Gstore init_Genv.

  Lemma hand_written_probe_counts :
    map probes prog_transformed = [4; 5; 3; 4]%nat.
  Proof. vm_compute; reflexivity. Qed.

  Lemma selector_matches_the_best_single_index_chain :
    probes selected = 4%nat.
  Proof. vm_compute; reflexivity. Qed.

  (* and without the demand it reached two: the inner loops were filtering on
     a condition that does not mention their own variable *)
  Lemma without_the_hoist_it_reaches_two :
    probes (apply_optimize_anno
              (AC [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap]
                 [[DictIdx "src"]] prog) init_Gstore init_Genv) = 2%nat.
  Proof. vm_compute; reflexivity. Qed.

  (* the headroom a second index would buy under the SAME uniform list *)
  Lemma two_indexes_would_reach_six :
    probes (apply_optimize_anno
              (AC [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap;
                   SwapFlatmapIf]
                 [[DictIdx "src"; DictIdx "dst"]] prog) init_Gstore init_Genv)
    = 6%nat.
  Proof. vm_compute; reflexivity. Qed.

  Theorem selected_sem : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      interp_command store env selected = interp_command store env prog.
  Proof.
    unfold selected, apply_optimize_anno; intros.
    eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
  Qed.

  Theorem prog_transformed_sem : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      forall prog', In prog' prog_transformed ->
                    interp_command store env prog' = interp_command store env prog.
  Proof.
    unfold prog_transformed, heuristics, apply_optimize_anno; cbn [map]; intros.
    repeat destruct_In;
      try eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
    lazymatch goal with H: In _ [] |- _ => apply in_nil in H; intuition idtac end.
  Qed.
End WithConcreteMaps.

Compute program_py prog.
Compute map program_py prog_transformed.

Definition res_attrs := ["p1"; "p2"; "p3"].
Compute sort_key_py "res" (Mergesort.Sectioned.sort String.leb res_attrs).
