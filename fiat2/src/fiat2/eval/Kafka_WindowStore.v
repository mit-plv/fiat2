Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.TransfUtils fiat2.FlatmapTransf fiat2.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   Source
     apache/kafka, commit 995cfcf9 (streams/src/main/java/org/apache/
       kafka/streams/state/internals/InMemoryWindowStore.java)

       private final ConcurrentNavigableMap<Long,
           ConcurrentNavigableMap<Bytes, byte[]>> segmentMap
               = new ConcurrentSkipListMap<>();                          :78

     and the four places that use its ordering:

       fetchAll(timeFrom, timeTo)          :398  -> :434
           segmentMap.subMap(minTime, true, timeTo, true)
       fetch(key, timeFrom, timeTo)        :287  -> :312
           segmentMap.subMap(minTime, true, timeTo, true)   then, per
           segment, the key's sub-range                            :1021-1029
       put(key, value, windowStartTimestamp)                        :221-226
           segmentMap.computeIfAbsent(t, ...).put(keyBytes, value)
       removeExpiredSegments()                                      :637-642
           segmentMap.headMap(minLiveTime, false).clear()

     A record store keyed by (window start time, key), held as a SORTED map
     from time to a sorted map from key to value.  The outer map is sorted
     because every read of it is a time RANGE, and the retention policy
     deletes a time range as well.

   Pattern
     B7 range scan, with a hand-built witness: the structure is a skip list
     precisely so the range is not a scan.  A1a hand-built index, A2 index
     maintained on removal, D4 composite key (the fetch at :287 wants
     time AND key).

   Claim
     C3 and C4 for the read side: asked a time range, the optimizer installs
     an ORDERED dictionary on time and answers the range out of it, which is
     the structure Kafka chose by hand.  This is the only eval file whose
     index is Ranged -- the other four are point-lookup structures a backend
     may hash.

     And two limitations, pinned rather than described, because both are
     cheap to state and neither is visible from a passing example:
     fetch_key_scans_unsplit and the_list_filter_keeps_the_list.

   Faithfulness -- what this translation drops, and why
     * segmentMap is TWO levels, time -> key -> value.  Here the store is one
       flat table of (time, k, val) rows.  Flat is the honest reading for
       this optimizer: it is handed a collection and it chooses the nesting,
       and what it chooses -- a dict from time to a bag of rows -- is the
       same two levels with the inner level unindexed.  Kafka's inner level
       is indexed too, and that difference is exactly the D4 gap measured
       below: no composite-key index exists, so the key narrowing stays a
       filter over the time bucket.
     * Kafka's ranges are closed, [minTime, timeTo].  The range rule's shape
       is half-open, [lo, hi).  Same query with hi = timeTo + 1; the shape is
       the rule's, and nothing here turns on which end is open.
     * minTime is max(timeFrom, observedStreamTime - retentionPeriod + 1),
       i.e. the requested bound clipped to the retention window, and
       observedStreamTime is mutable state.  The clipping is arithmetic on
       the bound before the query; `lo` here is the clipped bound.
     * `value` is byte[] and `key` is Bytes; they are TString here.  Neither
       is read by anything modelled -- the rows are counted, as in the other
       eval files, because the output channel is a list of strings.
     * put's expiry check, the duplicate-retaining seqnum wrapper, the
       transaction buffer, the iterator registry and the metrics sensor are
       all out of scope: none of them reads or maintains segmentMap's
       ordering.  put's delete path (value == null, :229-235) removes one
       key from one segment; it is HA_AreaRegistry's keyed delete, already
       covered there, and is left out so that the one delete in this file is
       the one this file is about.
     * Nothing is added.

     * put prepends the row.  The source puts into a NavigableMap keyed by
       time, so it names no position in a sequence of rows, and nothing here
       observes row order -- the ordering this file is about is the ORDER ON
       THE KEY, which the ranged dictionary holds.  See the note on row order
       in this directory's README.
   Expected
     ONE Ranged dict on time, installed and maintained incrementally across
     the put.  fetchAll becomes a range probe: ODictRange on the member,
     then its buckets.  No row outside the range is touched -- which is the
     whole reason Kafka's map is a skip list.

     Then the two limits.

     (1) fetch(key, timeFrom, timeTo) is a conjunction, range AND key, and
     no configuration serves both readers WELL.  Without SplitIf the range
     rule sees fetchAll's predicate whole and fires, while the conjunction
     stays a full scan.  With SplitIf the conjunction is split and the range
     rule fires on its outer half -- a range probe refined by the key test,
     which is Kafka's plan -- but the SAME splitter also cuts fetchAll's
     range pair in two.  Since a bound may now be absent, the outer half is
     still a range: fetchAll becomes a ONE-SIDED probe [lo, inf) whose upper
     bound survives only as a residual filter.  It reads fewer rows than the
     table but more than the range it asked for.  Both directions are
     pinned.  What is missing is small and nameable: SplitIf must not split
     a conjunction that is a range pair on one attribute.  This is the third
     rule-ordering hazard of the same kind (TableRep listed first,
     FilterEmptyToSetMem on a unique-dict table) and the first that no
     ordering can fix.

     (2) removeExpiredSegments is a RANGE-shaped delete, and the MEMBER is
     now maintained by one range operation: the retention predicate
     !(r.time < lo) is a one-sided bound, so keeping the rows it keeps is
     restricting the member to [lo, inf), and the write emits exactly that.
     What the restriction costs is the backend's affair -- a split of a
     persistent tree, or a walk of the survivors -- and this development
     fixes the SHAPE, not the constant.  Kafka's headMap(lo, false).clear()
     touches only the segments that expire, which is the other end of the
     same split, and the two-sided case is the complement operator
     ODictRangeDelete.

     What survives is the LIST.  The table's own field is still assigned a
     row-by-row filter over itself, and because that filter reads the list,
     the list cannot be erased: nothing recovers the rows from the member.
     This file is still HA_AreaRegistry before its keyed delete existed, but
     for a different reason than before -- the member is incremental and the
     list is not.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort [("time", TInt); ("k", TString); ("val", TString)]).

Definition query_ty :=
  TRecord (record_sort
             [("kind", TInt); ("lo", TInt); ("hi", TInt); ("key", TString);
              ("new_rec", row_ty)]).

Section WithConcreteMaps.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* ---- the source program: no index is named anywhere in it ---- *)

  Definition keep (pred : expr) : expr :=
    EFlatmap LikeList (ELoc "segments") "r"
      (EIf pred (EBinop OCons (EVar "r") (EAtom (ANil None))) (EAtom (ANil None))).

  (* lo <= r.time < hi, written as a programmer writes it with no index *)
  Definition in_range : expr :=
    EBinop OAnd
      (EUnop ONot (EBinop OLess (EAccess (EVar "r") "time") (EAccess (EVar "q") "lo")))
      (EBinop OLess (EAccess (EVar "r") "time") (EAccess (EVar "q") "hi")).

  Definition key_eq : expr :=
    EBinop OEq (EAccess (EVar "r") "k") (EAccess (EVar "q") "key").

  (* the retention policy: keep the rows at or after the live bound *)
  Definition not_expired : expr :=
    EUnop ONot (EBinop OLess (EAccess (EVar "r") "time") (EAccess (EVar "q") "lo")).

  Definition report (e : expr) : command :=
    CLet e "n"
      (CAssign "outputs"
         (EBinop OCons (EUnop OIntToString (EVar "n")) (ELoc "outputs"))).

  Definition dispatch (k : Z) (thn els : command) : command :=
    CIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt k))) thn els.

  (* Hand-written, not generated by an LLM. *)
  Definition prog : command :=
    CLetMut (EVar "segments_tbl") "segments"
      (CForeach (EVar "queries") "q"
         (* fetchAll(timeFrom, timeTo) -- :398 *)
         (dispatch 0 (report (EUnop OLength (keep in_range)))
            (* fetch(key, timeFrom, timeTo) -- :287 *)
            (dispatch 1 (report (EUnop OLength (keep (EBinop OAnd in_range key_eq))))
               (* put(key, value, windowStartTimestamp) -- :221 *)
               (dispatch 2
                  (CAssign "segments"
                     (EBinop OCons (EAccess (EVar "q") "new_rec") (ELoc "segments")))
                  (* removeExpiredSegments() -- :637 *)
                  (CAssign "segments" (keep not_expired)))))).

  Definition init_Gstore : ctenv := map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put (map.put map.empty "segments_tbl" (TList row_ty))
      "queries" (TList query_ty).

  (* ---- two configurations, differing only in whether a conjunctive filter
         is split before the collection phase.  See Expected (1): neither
         serves both readers. ---- *)

  Definition heuristics :=
    [ AC [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap]
        [[RangedDictIdx "time"]]
    ; AC [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap; SplitIf]
        [[RangedDictIdx "time"]]
    ].

  Definition prog_transformed :=
    map (fun heu => apply_optimize_anno (width:=width) (heu prog) init_Gstore init_Genv)
      heuristics.

  (* ---- projections, so every claim below is an equality of closed terms
         and reduces with vm_compute instead of unifying a whole program
         against a pattern full of holes ---- *)

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  Definition install_of (c : command) : option expr :=
    match c with
    | CLetMut e _ _ => Some e
    | _ => None
    end.

  (* the expression the n-th query branch binds *)
  Definition query_at (n : nat) (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ body) =>
        let rec := fix rec n b :=
          match n, b with
          | O, CIf _ (CLet e _ _) _ => Some e
          | S n', CIf _ _ els => rec n' els
          | _, _ => None
          end in rec n body
    | _ => None
    end.

  Definition put_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CIf _ (CAssign _ e) _)))) => Some e
    | _ => None
    end.

  Definition expire_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CIf _ _ (CAssign _ e))))) => Some e
    | _ => None
    end.

  (* ---- the shapes the claims are stated against ---- *)

  Definition member : expr := EAccess (EAccess (ELoc "segments") "aux_tag") "0".
  Definition the_list : expr := EAccess (ELoc "segments") "id_tag".
  Definition new_rec : expr := EAccess (EVar "q") "new_rec".

  (* the table is initialised from an input collection, as the store is
     restored from its changelog *)
  Definition initial_rows : expr := EVar "segments_tbl".

  (* add one row to the bucket its time names, reading the bucket out of the
     accumulator -- segmentMap.computeIfAbsent(t, ...).put(...) *)
  Definition bucket_add (acc_e key_e row_e : expr) : expr :=
    ETernop OInsert acc_e key_e
      (EBinop OBagInsert
         (EOptMatch (EBinop OLookup acc_e key_e)
            (EAtom (AEmptyBag None)) "x" (EVar "x"))
         row_e).

  Definition build_by_time (src : expr) : expr :=
    EFold src (EAtom (AEmptyDict Ranged None)) "tup" "acc"
      (bucket_add (EVar "acc") (EAccess (EVar "tup") "time") (EVar "tup")).

  (* the buckets of the index restricted to the key range, flattened *)
  Definition range_probe : expr :=
    EFlatmap LikeBag
      (EUnop ODictValues
         (ETernop ODictRange member
            (EUnop OSome (EAccess (EVar "q") "lo"))
            (EUnop OSome (EAccess (EVar "q") "hi"))))
      "b" (EVar "b").

  (* the same probe with only the lower bound named: the shape SplitIf leaves
     behind, since an absent bound is ANone and not a sentinel *)
  Definition range_probe_from : expr :=
    EFlatmap LikeBag
      (EUnop ODictValues
         (ETernop ODictRange member
            (EUnop OSome (EAccess (EVar "q") "lo"))
            (EAtom (ANone (Some TInt)))))
      "b" (EVar "b").

  (* the member restricted to the live range: headMap(lo, false).clear()
     read from the other end -- keep [lo, inf) *)
  Definition live_range : expr :=
    ETernop ODictRange member
      (EUnop OSome (EAccess (EVar "q") "lo"))
      (EAtom (ANone (Some TInt))).

  (* a residual filter over whatever collection it is given *)
  Definition refine (src pred : expr) : expr :=
    EFlatmap LikeBag src "r"
      (EIf pred (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "r"))
         (EAtom (AEmptyBag None))).

  Definition scan (pred : expr) : expr := refine (EBagOf the_list) pred.

  (* the surviving rows, as a list -- the retention filter, unrewritten *)
  Definition survivors : expr :=
    EFlatmap LikeList the_list "r"
      (EIf not_expired (EBinop OCons (EVar "r") (EAtom (ANil None)))
         (EAtom (ANil None))).

  (* ==================== configuration 0: no SplitIf ==================== *)

  (* One member, a Ranged dict on time: the sorted map Kafka declared by
     hand at :78, derived from a program that names no structure.  It is the
     only Ranged index in these files, and the obligation is real -- a
     backend owes this member a structure that can answer a key range,
     where every other member here may be a hash table. *)
  Definition install_expected : expr :=
    ERecord
      [("id_tag", initial_rows);
       ("aux_tag", ERecord [("0", build_by_time initial_rows)])].

  Lemma installs_the_ranged_dict :
    install_of (nth 0 prog_transformed CSkip) = Some install_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* fetchAll(timeFrom, timeTo), :398 -> :434: one ODictRange and the
     buckets it selects.  No row outside [lo, hi) is looked at, which is
     what segmentMap.subMap buys Kafka. *)
  Lemma fetch_all_is_a_range_probe :
    query_at 0 (nth 0 prog_transformed CSkip)
    = Some (EACFold AGCount range_probe).
  Proof. vm_compute; reflexivity. Qed.

  (* fetch(key, timeFrom, timeTo), :287: a full scan.  The range rule's
     pattern is a filter whose body is a singleton, and a conjunction's
     outer test does not have one.  Compare the same query in
     configuration 1, where it becomes the probe Kafka performs. *)
  Lemma fetch_key_scans_unsplit :
    query_at 1 (nth 0 prog_transformed CSkip)
    = Some (EACFold AGCount (scan (EBinop OAnd in_range key_eq))).
  Proof. vm_compute; reflexivity. Qed.

  (* put(key, value, t), :221-226: the bucket t names takes one row.  No
     fold over the table appears -- this is computeIfAbsent(t,..).put(..). *)
  Definition put_expected : expr :=
    ERecord
      [("id_tag", EBinop OCons new_rec the_list);
       ("aux_tag",
         ERecord [("0", ELet member "y"
                           (bucket_add (EVar "y") (EAccess new_rec "time") new_rec))])].

  Lemma put_is_incremental :
    put_of (nth 0 prog_transformed CSkip) = Some put_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* removeExpiredSegments(), :637-642: a RANGE-shaped delete, and the
     member is maintained by ONE range operation rather than a fold over
     every surviving row.  The retention predicate !(r.time < lo) is a
     one-sided bound, so the rows it keeps are the keys in [lo, inf) and
     the member's new value is the old member restricted to that range.

     This is where the two operators pay off.  ODictRange's bounds are
     TOption, so the absent upper bound is ANone and needs no infinity for
     a TInt key; and the two-sided case -- where the survivors are two
     disjoint ranges and there is no dict union -- is the complement
     operator ODictRangeDelete rather than a pair of ranges.  Five
     witnesses in this corpus, three one-sided and two two-sided:
     InMemoryWindowStore:642, InMemorySessionStore:640,
     TreeMapLogHistory:61, SharePartition:2730,
     RocksDBTransactionBuffer:147.

     What the restriction COSTS is the backend's affair: splitting a
     persistent tree is logarithmic, walking the survivors is not, and this
     development fixes the shape and not the constant.  Kafka's
     headMap(minLiveTime, false).clear() is the same split taken from the
     expiring end. *)
  Definition expire_expected : expr :=
    ERecord
      [("id_tag", survivors);
       ("aux_tag", ERecord [("0", live_range)])].

  Lemma expiry_restricts_the_member :
    expire_of (nth 0 prog_transformed CSkip) = Some expire_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* And the list stays anyway.  Not because a query reads it -- after the
     rewrite no query does -- and no longer because the member's rebuild
     does, but because the TABLE's own field is still assigned a row-by-row
     filter over itself, and nothing recovers the rows from the member.
     This is HA_AreaRegistry's situation before its keyed delete existed
     with one difference: there the member kept the list alive, here only
     the list does. *)
  Lemma the_list_filter_keeps_the_list :
    installed_fields (nth 0 prog_transformed CSkip) = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ==================== configuration 1: with SplitIf ==================== *)

  (* Now the conjunctive reader gets Kafka's plan: the time range out of the
     ordered member, then the key test over that bucket -- which is
     :312 followed by the per-segment narrowing at :1021-1029, except that
     Kafka's inner level is a sorted map and ours is a bag.  That residual
     is the D4 composite-key gap, and it is the same gap Kafka_Cluster
     measures for (topic, partition). *)
  Lemma fetch_key_probes_split :
    query_at 1 (nth 1 prog_transformed CSkip)
    = Some (EACFold AGCount (refine range_probe key_eq)).
  Proof. vm_compute; reflexivity. Qed.

  (* And here is the price, which is why both configurations are in the
     file.  The same splitter cuts fetchAll's range pair in two, and two
     one-sided comparisons are not a range: the probe becomes a scan
     filtered by one bound, chained into a scan filtered by the other.  No
     ordering of the rules recovers it -- SplitIf runs in the basic phase,
     before any index rule can see the predicate.  The fix is a guard on
     SplitIf: leave a conjunction alone when it is a range pair on one
     attribute. *)
  Lemma fetch_all_loses_a_bound_split :
    query_at 0 (nth 1 prog_transformed CSkip)
    = Some (EACFold AGCount
              (refine range_probe_from
                 (EBinop OLess (EAccess (EVar "r") "time")
                    (EAccess (EVar "q") "hi")))).
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     And all of it is sound: every program above computes what the source
     program computes, on every store and environment.  The two
     configurations are equal to the same source, so the limitations are
     limitations of what was derived, never of whether it is correct. *)

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
