Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.rules.CollectionTransf fiat2.index.DictIndexImpl
  fiat2.TransfUtils fiat2.rules.FlatmapTransf fiat2.index.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.pipeline.Pipeline.
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
   WHAT IT MEASURES (harness `bench typed 200 400 800 1600`; work at 1600
   rows and the fitted exponent).  This file is extracted, unlike the other
   Ex_* regression files but like Ex_RangeDelete and Ex_MinDelete, because the
   two maintenance rules have no third-party witness yet and this is where
   they are priced:

     kind           source    a        optimized   a
     readInOrder   1738172  1.00            1712  0.00
     readPermuted  1738412  1.00            1972  0.00
     readPermuted2 1738652  1.00            2212  0.00
     insert           1320  0.00            3042 -0.00
     deleteAtKey   1883785  1.02            2080 -0.01
     build               9  --            126899  1.00
     whole op phase 7112674               11018          646x

   THE DELETE IS THE NUMBER TO READ: 1883785 to 2080, 906x, and the exponent
   1.02 to -0.01.  The source rebuilds the index from the filtered list on
   every delete; the optimized form is one ODelete on a tree.

   THE INSERT COSTS MORE, and that is the honest direction: a prepend is O(1)
   already, so maintaining the index adds a constant (1320 to 3042) and buys
   nothing on this operation.  What it buys is that the READS stay probes
   afterwards, which is the whole point of maintaining rather than rebuilding.

   A WARNING ABOUT THIS FILE AS EVIDENCE.  It is a regression file: the
   queries were written to make the rules fire, so the ratios above say what
   the rules are worth WHEN THEY APPLY and say nothing about how often that
   is.  eval/ is where that question lives, and the delete rule has no witness
   there yet -- eval/HA_EntityRegistry's own removal is keyed on entity_id,
   not on the composite key, so it needs a KEYED delete (probe the primary
   member for the row, then drop it from the one bucket its key names, as
   DictIndexKeyedDelete does for a single attribute).  That rule does not
   exist for a composite key.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort
             [("k1", TString); ("k2", TString); ("k3", TInt); ("v", TString)]).

Definition query_ty :=
  TRecord (record_sort
             [("kind", TInt); ("a", TString); ("b", TString); ("c", TInt);
              ("new_item", row_ty)]).

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

  (* keep the rows the composite key does NOT name, written PERMUTED so that
     the delete inherits the read rule's order-insensitivity *)
  Definition drop_at_key : expr :=
    EFlatmap LikeList (ELoc "items") "r"
      (EIf (EUnop ONot (EBinop OAnd c3 (EBinop OAnd c1 c2)))
         (EBinop OCons (EVar "r") (EAtom (ANil None))) (EAtom (ANil None))).

  (* the same three equalities three ways, and then the two writes:
       0  declared order, right-nested
       1  PERMUTED and LEFT-nested
       2  permuted again
       3  an insert
       4  a delete AT the composite key, permuted

     The PREFIX read is in prog_prefix below and not here, deliberately: a
     scan of the row list keeps the list alive, and with the list alive the
     delete's own linear pass over it hides what the delete rule does.  Two
     programs, so that each fact is measured where nothing masks it. *)
  Definition prog : command :=
    CLetMut (EVar "items_tbl") "items"
      (CForeach (EVar "queries") "q"
         (dispatch 0 (report (filt (EBinop OAnd c1 (EBinop OAnd c2 c3))))
            (dispatch 1 (report (filt (EBinop OAnd (EBinop OAnd c3 c1) c2)))
               (dispatch 2 (report (filt (EBinop OAnd c2 (EBinop OAnd c3 c1))))
                  (dispatch 3
                     (CAssign "items"
                        (EBinop OCons (EAccess (EVar "q") "new_item")
                           (ELoc "items")))
                     (CAssign "items" drop_at_key)))))).

  (* the negative half, on its own: a conjunction on a PREFIX of the key *)
  Definition prog_prefix : command :=
    CLetMut (EVar "items_tbl") "items"
      (CForeach (EVar "queries") "q" (report (filt (EBinop OAnd c1 c2)))).

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put (map.put map.empty "items_tbl" (TList row_ty))
      "queries" (TList query_ty).

  (* No SplitIf: the composite rule wants the conjunction whole, and the
     ordering hazard that costs is pinned twice in eval/ already. *)
  (* the basics the deterministic selector emits for this program, so that
     eval/SelectorTests can compare its output to this annotation directly *)
  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition heuristics :=
    [ AC basics [[CompositeDictIdx ["k1"; "k2"; "k3"]]] ].

  Definition prog_transformed :=
    map (fun heu => apply_optimize_anno (heu prog) init_Gstore init_Genv)
      heuristics.

  Definition optimized : command := nth 0 prog_transformed CSkip.

  Definition optimized_prefix : command :=
    apply_optimize_anno
      (AC basics [[CompositeDictIdx ["k1"; "k2"; "k3"]]] prog_prefix)
      init_Gstore init_Genv.

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

  Fixpoint write_branch (n : nat) (c : command) : option expr :=
    match n, c with
    | O, CIf _ (CAssign _ e) _ => Some e
    | O, CAssign _ e => Some e
    | S n', CIf _ _ c' => write_branch n' c'
    | _, _ => None
    end.

  Definition write_at (n : nat) (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ b) => write_branch n b
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
    query_at 0 optimized_prefix
    = Some (EACFold AGCount
              (EFlatmap LikeBag
                 (EUnop OBagOfList (EAccess (ELoc "items") "id_tag")) "r"
                 (EIf (EBinop OAnd c1 c2)
                    (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "r"))
                    (EAtom (AEmptyBag None))))).
  Proof. vm_compute; reflexivity. Qed.

  Lemma prefix_read_keeps_the_list :
    installed_fields optimized_prefix = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* And in the program with the writes and no prefix read, the list is GONE:
     every read is a probe and both writes are maintained, so the table IS its
     index -- across an insert AND across a delete. *)
  Lemma the_table_is_its_index :
    installed_fields optimized = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ---- the two writes, maintained ----

     The insert is one OInsert into the member, which takes the insert rule
     and the use rule as a pair: the first turns rebuilding the index of
     `row :: rest` into building the index of `rest` and inserting one row,
     and the second replaces that `index of rest` with the member already
     stored.

     THE DELETE IS ONE ODelete, and the key it deletes at is written in the
     conjunction's order, not the index's -- so the delete inherits the read
     rule's order-insensitivity from the same permutation guard.  Its content
     is gallina_to_idx_filter_neq: the index of a table with one key's rows
     removed IS the index with that key deleted.

     AND THE ROW LIST IS GONE.  Every read is a probe and both writes are
     maintained, so no reader of the list is left and erase_dead_field drops
     it -- including from the writes' own right-hand sides.  The delete is one
     ODelete and NOTHING ELSE: the table IS its index, across a delete.  That
     is why the prefix read lives in prog_prefix: a scan of the list keeps the
     list, and a surviving list makes the delete pay a linear pass that has
     nothing to do with the index. *)

  Definition member : expr :=
    EAccess (EAccess (ELoc "items") "aux_tag") "0".
  Definition new_item : expr := EAccess (EVar "q") "new_item".

  Definition row_key : expr :=
    ERecord [("k1", EAccess (EVar "tup") "k1");
             ("k2", EAccess (EVar "tup") "k2");
             ("k3", EAccess (EVar "tup") "k3")].

  Lemma insert_is_one_insert :
    write_at 3 optimized
    = Some (ERecord
              [("aux_tag",
                 ERecord
                   [("0",
                      ELet new_item "tup"
                        (ELet member "acc"
                           (ETernop OInsert (EVar "acc") row_key
                              (EBinop OBagInsert
                                 (EOptMatch (EBinop OLookup (EVar "acc") row_key)
                                    (EAtom (AEmptyBag None)) "x" (EVar "x"))
                                 (EVar "tup")))))])]).
  Proof. vm_compute; reflexivity. Qed.

  Lemma delete_is_one_delete :
    write_at 4 optimized
    = Some (ERecord
              [("aux_tag",
                 ERecord
                   [("0", EBinop ODelete member
                            (key_of [("k3","c"); ("k1","a"); ("k2","b")]))])]).
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
