Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.TransfUtils fiat2.FlatmapTransf fiat2.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   THE COMPOSITE KEY'S READ RULE DOES NOT CARE HOW THE CONJUNCTION WAS
   WRITTEN.

   A regression test, not an evaluation subject: the four reads below exist to
   make the rule fire (and, once, to make it decline), which is why this file
   is here and not in eval/.

   Three of them are the SAME query written three ways -- different
   association and different order of the three equalities -- and all three
   come out as one probe into one index.  Two facts make that true and both
   are proved in CompositeDictIndexImpl:

     * conj_eq_pairs COLLECTS the conjuncts of an arbitrary tree, so
       association never reaches the guard at all.
     * record_sort_Permutation_eq says a record's canonical form is determined
       by the multiset of its field names when those names are distinct.  So
       the index on (k1, k2, k3) and an index on any permutation of them are
       the SAME index, and the guard can accept the conjuncts in any order --
       guard_Permutation is the decidable test it uses.

   The emitted keys below therefore differ as EXPRESSIONS and agree as VALUES,
   which is what the_three_keys_are_one_key pins directly rather than leaving
   to the reader.

   The fourth read is the negative half, and it is the limit that survives:
   a conjunction on a PREFIX of the key (k1 and k2, not k3) is not matched at
   all.  The guard's length test is what declines it, and declining is right
   -- the index is keyed on the whole triple, so a two-attribute probe is not
   a probe into it.  Serving that read would need either a second index or an
   ordered composite key, and the latter is refused on purpose (record_compare
   orders a record by sorted field NAME, so a range over a composite key would
   range on whichever attribute sorts first).  The read stays a scan, so the
   row list survives -- which prefix_read_keeps_the_list pins.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort
             [("k1", TString); ("k2", TString); ("k3", TInt); ("v", TString)]).

Definition query_ty :=
  TRecord (record_sort
             [("kind", TInt); ("a", TString); ("b", TString); ("c", TInt)]).

Section WithConcreteMaps.

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string (value) := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* [r <- items, check(pred), ret r], counted *)
  Definition filt (pred : expr) : expr :=
    EUnop OLength
      (EFlatmap LikeList (ELoc "items") "r"
         (EIf pred (EBinop OCons (EVar "r") (EAtom (ANil None)))
            (EAtom (ANil None)))).

  Definition c1 : expr := EBinop OEq (EAccess (EVar "r") "k1") (EAccess (EVar "q") "a").
  Definition c2 : expr := EBinop OEq (EAccess (EVar "r") "k2") (EAccess (EVar "q") "b").
  Definition c3 : expr := EBinop OEq (EAccess (EVar "r") "k3") (EAccess (EVar "q") "c").

  Definition report (e : expr) : command :=
    CLet e "n"
      (CAssign "outputs"
         (EBinop OCons (EUnop OStringOfInt (EVar "n")) (ELoc "outputs"))).

  Definition dispatch (k : Z) (thn els : command) : command :=
    CIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt k))) thn els.

  (* the same three equalities, four ways:
       0  declared order, right-nested
       1  PERMUTED and LEFT-nested
       2  permuted again
       3  a PREFIX of the key -- two of the three *)
  Definition prog : command :=
    CLetMut (EVar "items_tbl") "items"
      (CForeach (EVar "queries") "q"
         (dispatch 0 (report (filt (EBinop OAnd c1 (EBinop OAnd c2 c3))))
            (dispatch 1 (report (filt (EBinop OAnd (EBinop OAnd c3 c1) c2)))
               (dispatch 2 (report (filt (EBinop OAnd c2 (EBinop OAnd c3 c1))))
                  (report (filt (EBinop OAnd c1 c2))))))).

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put (map.put map.empty "items_tbl" (TList row_ty))
      "queries" (TList query_ty).

  (* No SplitIf: the composite rule wants the conjunction whole, and the
     ordering hazard that costs is pinned twice in eval/ already. *)
  Definition heuristics :=
    [ AC [PushdownCollection; AnnotateCollection]
        [[CompositeDictIdx ["k1"; "k2"; "k3"]]] ].

  Definition prog_transformed :=
    map (fun heu => apply_optimize_anno (heu prog) init_Gstore init_Genv)
      heuristics.

  Definition optimized : command := nth 0 prog_transformed CSkip.

  (* ---- projections ---- *)

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  Fixpoint branch (n : nat) (c : command) : option expr :=
    match n, c with
    | O, CIf _ (CLet e _ _) _ => Some e
    | O, CLet e _ _ => Some e
    | S n', CIf _ _ c' => branch n' c'
    | _, _ => None
    end.

  Definition query_at (n : nat) (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ b) => branch n b
    | _ => None
    end.

  Definition probe (k : expr) : expr :=
    EOptMatch
      (EBinop OLookup (EAccess (EAccess (ELoc "items") "aux_tag") "0") k)
      (EAtom (AEmptyBag None)) "b" (EVar "b").

  Definition key_of (l : list (string * string)) : expr :=
    ERecord (List.map (fun p => (fst p, EAccess (EVar "q") (snd p))) l).

  (* ---- the three spellings, one index ---- *)

  (* declared order *)
  Lemma in_order_probes :
    query_at 0 optimized
    = Some (EACFold AGCount (probe (key_of [("k1","a"); ("k2","b"); ("k3","c")]))).
  Proof. vm_compute; reflexivity. Qed.

  (* permuted AND re-associated: (k3 && k1) && k2 *)
  Lemma permuted_left_nested_probes :
    query_at 1 optimized
    = Some (EACFold AGCount (probe (key_of [("k3","c"); ("k1","a"); ("k2","b")]))).
  Proof. vm_compute; reflexivity. Qed.

  (* permuted the other way: k2 && (k3 && k1) *)
  Lemma permuted_right_nested_probes :
    query_at 2 optimized
    = Some (EACFold AGCount (probe (key_of [("k2","b"); ("k3","c"); ("k1","a")]))).
  Proof. vm_compute; reflexivity. Qed.

  (* ---- and the three keys are one key ----

     Different expressions, equal values, because interp_expr of an ERecord
     canonicalises with record_sort.  Pinned on a concrete query row so that
     it is an equality of closed values and not an appeal to the lemma. *)
  Definition sample_q : clocals :=
    map.put map.empty "q"
      (VRecord (record_sort [("kind", VInt 2); ("a", VString "x");
                             ("b", VString "y"); ("c", VInt 7)])).

  Lemma the_three_keys_are_one_key :
    let v := interp_expr map.empty sample_q
               (key_of [("k1","a"); ("k2","b"); ("k3","c")]) in
    interp_expr map.empty sample_q (key_of [("k3","c"); ("k1","a"); ("k2","b")]) = v
    /\ interp_expr map.empty sample_q (key_of [("k2","b"); ("k3","c"); ("k1","a")]) = v.
  Proof. vm_compute; split; reflexivity. Qed.

  (* ---- the limit that survives ----

     A conjunction on a PREFIX of the key is declined, and the scan it stays
     keeps the row list alive. *)
  Lemma prefix_read_scans :
    query_at 3 optimized
    = Some (EACFold AGCount
              (EFlatmap LikeBag
                 (EUnop OBagOfList (EAccess (ELoc "items") "id_tag")) "r"
                 (EIf (EBinop OAnd c1 c2)
                    (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "r"))
                    (EAtom (AEmptyBag None))))).
  Proof. vm_compute; reflexivity. Qed.

  Lemma prefix_read_keeps_the_list :
    installed_fields optimized = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ---- soundness ---- *)

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
