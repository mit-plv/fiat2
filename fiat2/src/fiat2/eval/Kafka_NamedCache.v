Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.constraint.Decl fiat2.constraint.Surface fiat2.constraint.Constraint fiat2.Substitute fiat2.constraint.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.rules.FlatmapForms fiat2.pipeline.Pipeline.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   Source
     apache/kafka, commit 995cfcf9 (streams/src/main/java/org/apache/
       kafka/streams/state/internals/NamedCache.java)

       private final NavigableMap<Bytes, LRUNode> cache = new TreeMap<>();  :44
       private long currentSizeBytes;                                       :49

     and the five places that keep the second field equal to the sum of the
     first's node sizes:

       put(key, value)        :174  LRUNode node = cache.get(key);
                              :178      currentSizeBytes -= node.size();
                              :185      cache.put(key, node);
                              :192  currentSizeBytes += node.size();
       evict()                :249  currentSizeBytes -= eldest.size();
                              :251  cache.remove(eldest.key);
       delete(key)            :273  LRUNode node = cache.remove(key);
                              :281  currentSizeBytes -= node.size();
       sizeInBytes()          :196  return currentSizeBytes;

     A keyed store and a RUNNING TOTAL over it, maintained by hand in both
     directions.  sizeInBytes() is called on every cache operation by
     ThreadCache to decide whether to evict, so the total is read far more
     often than the table changes -- which is why it is a field and not a
     fold.

   Pattern
     A3 maintained aggregate, with a hand-written witness in both
     directions.  A1b keyed store (the cache is a map keyed by Bytes, so the
     key is unique by construction).  A2 index maintained on removal.

   Claim
     C3 and C4.  Asked for a total and for key lookups, the optimizer
     installs exactly the two fields NamedCache declares -- a key-to-row
     dictionary and an integer -- and maintains both across both writes.
     The total is never recomputed: a delete subtracts the leaving row's
     size, fetched by a PROBE into the dictionary, and that is :281 reading
     :273's node.

     C1 secondarily: the declared uniqueness is what makes the lookup a
     single-row probe rather than a bucket, and it is a fact about the data
     structure Kafka chose, not an assumption added here.

   Faithfulness -- what this translation drops, and why
     * LRUNode.size() (:398) is COMPUTED from the key length and the entry,
       not stored.  It is a stored attribute here.  It is a pure function of
       a row and changes only when update(:411) replaces the entry, which is
       the overwrite path modelled below as a delete followed by an insert --
       so storing it costs this example nothing and saves introducing a
       derived field no rule reads.
     * The LRU order -- the `previous`/`next` chain, `head`, `tail`,
       putHead(:232), updateLRU(:213) -- is a SECOND derived structure, and
       it answers a different question: which row is eldest.  prog_s below
       does not model it, and prog_lru_s DOES: see the LRU section near the
       end of this file.  The modelling choice there is worth stating here,
       because an earlier draft of this note guessed wrong.  It said evict()
       would need "a recency attribute and a maintained extremum over it,
       which is what MinAgg is for".  That is one way; it is not the
       source's way and not the one taken.  NamedCache stores no timestamp:
       recency IS position in the chain, so the row list's ORDER is the
       structure, and evict() reads its last element.  Modelled that way the
       program needs no new attribute, no extremum, and no new operator --
       and it becomes the one program in this development whose row list
       cannot be erased, because order is the only thing it asks for.
       What evict() contributes to prog_s is its size accounting (:249),
       which is delete's (:281).
     * dirtyKeys (:45) is a third derived structure, a set of the keys whose
       entry is dirty.  It is a declared-predicate index -- the rows where
       entry.isDirty() -- and the flag it keys on is not modelled here.
     * size() (:286) returns cache.size(), a maintained ROW COUNT.  This
       development has no count aggregate: SumAgg sums an attribute, and a
       count is not a sum of any field.  So that reader is left out of the
       program rather than written as a fold that nothing would rewrite.
       Its witness is elsewhere in the same corpus --
       clients/.../InFlightRequests.java maintains inFlightRequestCount at
       :49/:67/:86/:150 and returns it at :123 -- and it is the clearest
       case for the one aggregate index that is missing.
     * Bytes keys and LRUCacheEntry values are TString and an integer size;
       nothing modelled reads a value.  Rows are counted on the way out, as
       in the other eval files, because the output channel is a list of
       strings.
     * keyRange/computeSubSet (:295-314) range over the KEY, not over an
       integer attribute, and the range rule's comparison is on TInt.  That
       reader belongs to Kafka_WindowStore, which is about ranges.
     * The metrics sensors, the flush listener and the hit-ratio counters are
       bookkeeping over no collection.
     * Nothing is added.  In particular the put below is written exactly as
       NamedCache writes it: remove the key, then insert the new row.

     * The insert prepends the row.  The source puts into a NavigableMap, so
       it names no position in a sequence of rows, and nothing here observes
       row order -- see the note on row order in this directory's README.
   Expected
     Two members and no list: a dictionary from key to row, and one integer.
     That is NamedCache's two fields, derived from a program that declares a
     uniqueness and asks four questions.

     sizeInBytes() becomes a field read.  get(key) becomes a probe.

     And both writes maintain both members in place:
       * delete(key): ODelete on the dictionary, and the total MINUS the
         size of the row the probe found -- :273 and :281, in that order,
         with the probe standing in for cache.remove's return value.
       * put(key, value): the delete half subtracts the old row's size
         (:178) and the insert half adds the new one's (:192), each against
         a member read, with the uniqueness check itself a probe.

     Nothing anywhere folds over the table.  The one thing the source does
     that this does not is read its own total to decide to evict, and that
     decision needs the LRU order, not the total.

     And one measured negative, because this example is the first where two
     index choices interact: listing the aggregate BEFORE the dictionary
     leaves the delete's correction term a scan over the table, which also
     keeps the list alive.  Both orderings are sound and one is
     asymptotically worse -- a silent pessimization, pinned at
     swapped_correction_scans so a selector can be held to it.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort [("k", TString); ("size", TInt)]).

Definition query_ty :=
  TRecord (record_sort [("kind", TInt); ("k", TString); ("node", row_ty)]).

Section WithConcreteMaps.
  Notation value := (value).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* ---- the source program: no index and no counter in it ---- *)

  Definition node_key : expr := EAccess (EAccess (EVar "q") "node") "k".

  (* cache.remove(key), as a programmer writes it over a collection *)
  Definition without (key_e : expr) : expr :=
    EFlatmap LikeList (ELoc "cache") "r"
      (EIf (EUnop ONot (EBinop OEq (EAccess (EVar "r") "k") key_e))
         (EBinop OCons (EVar "r") (EAtom (ANil None))) (EAtom (ANil None))).

  (* sizeInBytes(), with no field to read it out of: a fold over the table *)
  Definition total_size : expr :=
    EFold (EFlatmap LikeList (ELoc "cache") "r"
             (EBinop OCons (EAccess (EVar "r") "size") (EAtom (ANil None))))
      (EAtom (AInt 0)) "_v" "_acc" (EBinop OPlus (EVar "_v") (EVar "_acc")).

  (* cache.get(key), with no map to probe: a scan *)
  Definition get_key : expr :=
    EUnop OLength
      (EFlatmap LikeList (ELoc "cache") "r"
         (EIf (EBinop OEq (EAccess (EVar "r") "k") (EAccess (EVar "q") "k"))
            (EBinop OCons (EVar "r") (EAtom (ANil None))) (EAtom (ANil None)))).

  Definition report (e : expr) : scommand :=
    SLet e "n"
      (SAssign "outputs"
         (EBinop OCons (EUnop OStringOfInt (EVar "n")) (ELoc "outputs")) SSkip).

  Definition dispatch (k : Z) (thn els : scommand) : scommand :=
    SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt k))) thn els.

  (* Hand-written, not generated by an LLM. *)
  Definition prog_s (ds : list decl) : scommand :=
    SLetConstrained "cache" row_ty ds
      (SForeach (EVar "ops") "q"
         (* delete(key) -- :273 *)
         (dispatch 0
            (SAssign "cache" (without (EAccess (EVar "q") "k")) SSkip)
            (* put(key, value) -- :174-192, written as the source writes it:
               take the key out, then put the new row in *)
            (dispatch 1
               (SSeq (SAssign "cache" (without node_key) SSkip)
                  (SAssign "cache"
                     (EBinop OCons (EAccess (EVar "q") "node") (ELoc "cache"))
                     SSkip))
               (* sizeInBytes() -- :196 *)
               (dispatch 2 (report total_size)
                  (* get(key) -- :200-201 *)
                  (report get_key))))).

  Definition init_Gstore : ctenv := map.put map.empty "outputs" (TList TString).
  Definition init_Genv : ctenv := map.put map.empty "ops" (TList query_ty).

  Definition elaborated (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_s ds).

  (* The cache is a Map keyed by Bytes, so one row per key is a fact about
     the structure NamedCache chose. *)
  Definition decls := [DUnique "k"].

  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  (* The dictionary FIRST and the aggregate SECOND, which means the
     aggregate's rules run first (the transfs of the choices are
     concatenated in list order, and the last to be listed is the first to
     run).  The order matters, and the cost of getting it wrong is measured
     below rather than asserted: see swapped_correction_scans. *)
  Definition anno : canno_command :=
    CAC (("cache", (row_ty, decls)) :: cenv_rm "cache" []) O
      basics [UniqueDictIdx "k"; SumAgg "size"] [] (elaborated decls).

  Definition optimized : command :=
    apply_optimize_anno_constrained anno init_Gstore init_Genv.

  (* the same two indexes, listed the other way round *)
  Definition anno_swapped : canno_command :=
    CAC (("cache", (row_ty, decls)) :: cenv_rm "cache" []) O
      basics [SumAgg "size"; UniqueDictIdx "k"] [] (elaborated decls).

  Definition optimized_swapped : command :=
    apply_optimize_anno_constrained anno_swapped init_Gstore init_Genv.

  (* ---- projections, so every claim below is an equality of closed terms
         and reduces with vm_compute ---- *)

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

  Definition delete_of (c : command) : option (expr * expr) :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ (CIf g (CAssign _ e) _) _)) => Some (g, e)
    | _ => None
    end.

  Definition put_del_of (c : command) : option (expr * expr) :=
    match c with
    | CLetMut _ _ (CForeach _ _
         (CIf _ _ (CIf _ (CSeq (CIf g (CAssign _ e) _) _) _))) => Some (g, e)
    | _ => None
    end.

  Definition put_ins_of (c : command) : option (expr * expr) :=
    match c with
    | CLetMut _ _ (CForeach _ _
         (CIf _ _ (CIf _ (CSeq _ (CIf g (CAssign _ e) _)) _))) => Some (g, e)
    | _ => None
    end.

  Definition read_total_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CIf _ (CLet e _ _) _)))) => Some e
    | _ => None
    end.

  Definition read_get_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CIf _ _ (CLet e _ _))))) => Some e
    | _ => None
    end.

  (* ---- the shapes the claims are stated against ---- *)

  (* member 0 is the dictionary, member 1 the total *)
  Definition member (i : string) : expr := EAccess (EAccess (ELoc "cache") "aux_tag") i.
  Definition new_node : expr := EAccess (EVar "q") "node".

  Definition row_list_ty : type := TRecord [("k", TString); ("size", TInt)].
  Definition empty_rows : expr := EAtom (ANil (Some row_list_ty)).

  (* a unique index holds the row, so a probe wraps it into a bag *)
  Definition probe (k : expr) : expr :=
    EOptMatch (EBinop OLookup (member "0") k) (EAtom (AEmptyBag None)) "y"
      (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "y")).

  (* the sum of `size` over whatever collection it is given *)
  Definition sum_size (src : expr) : expr :=
    EACFold AGSum (flatmap_proj_bag src "x" (EAccess (EVar "x") "size") None).

  Definition the_list : expr := EAccess (ELoc "cache") "id_tag".

  (* the rows with a given key, found by looking at all of them *)
  Definition key_scan (key_e : expr) : expr :=
    flatmap_filter_bag (EUnop OBagOfList the_list) "r"
      (EBinop OEq (EAccess (EVar "r") "k") key_e) "r" None None.

  Definition build_by_key (src : expr) : expr :=
    EFold src (EAtom (AEmptyDict Unranged None)) "tup" "acc"
      (ETernop OInsert (EVar "acc") (EAccess (EVar "tup") "k") (EVar "tup")).

  (* ------------------------------------------------------------------
     What the pipeline produced. *)

  (* NamedCache's two fields, :44 and :49, derived: a key-to-row dictionary
     and one integer holding the sum of the sizes. *)
  Definition install_expected : expr :=
    ERecord
      [("aux_tag",
         ERecord [("0", build_by_key empty_rows);
                  ("1", sum_size (EUnop OBagOfList empty_rows))])].

  Lemma installs_the_map_and_the_total :
    install_of optimized = Some install_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* And no list.  NamedCache has no list of nodes either: every reader goes
     through the map or through the counter. *)
  Lemma erases_the_list : installed_fields optimized = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* sizeInBytes() (:196-197): the field read it is in the source.  The fold
     over the table is gone. *)
  Lemma size_in_bytes_reads_the_counter :
    read_total_of optimized = Some (member "1").
  Proof. vm_compute; reflexivity. Qed.

  (* cache.get(key) (:200-201): one probe. *)
  Lemma get_is_a_probe :
    read_get_of optimized
    = Some (EACFold AGCount (probe (EAccess (EVar "q") "k"))).
  Proof. vm_compute; reflexivity. Qed.

  (* delete(key) (:273-281).  THIS IS THE POINT: the dictionary loses one
     key, and the total loses the size of the row the probe found.  Neither
     member is rebuilt and no fold over the table survives.

     Read against the source: :273 binds the node by cache.remove(key) and
     :281 subtracts that node's size.  Here the probe plays :273's part --
     it reads the row before the delete, which is the same row Java's remove
     hands back -- and the OMinus is :281.

     What it cost: the sum's delete rule (SumAgg's filter_neq_to_sub) states
     the correction as a sum over the rows the filter removes, which is a sum
     over a BUCKET.  The declared uniqueness is what shrinks that bucket to
     one row, so the correction is O(1) and not O(rows with that key). *)
  Definition delete_guard_expected : expr :=
    EBinop OAnd (EAtom (ABool true)) (EAtom (ABool true)).

  Definition delete_expected (key_e : expr) : expr :=
    ERecord
      [("aux_tag",
         ERecord [("0", EBinop ODelete (member "0") key_e);
                  ("1", EBinop OMinus (member "1") (sum_size (probe key_e)))])].

  Lemma delete_corrects_by_a_probe :
    delete_of optimized
    = Some (delete_guard_expected,
            delete_expected (EAccess (EVar "q") "k")).
  Proof. vm_compute; reflexivity. Qed.

  (* put(key, value), first half (:174-178): the same rewrite at the put's
     key.  currentSizeBytes -= node.size(), where node came from
     cache.get(key). *)
  Lemma put_subtracts_the_old :
    put_del_of optimized
    = Some (delete_guard_expected, delete_expected node_key).
  Proof. vm_compute; reflexivity. Qed.

  (* put(key, value), second half (:185-192): the dictionary takes the row
     and the total takes its size.  currentSizeBytes += node.size().

     The guard is the uniqueness check, and it is a probe -- not a scan --
     because the index serves it.  That check is what the source gets for
     free from being a Map; here it is checked, and checked in O(1). *)
  Definition put_guard_expected : expr :=
    EBinop OAnd
      (ELet new_node "_pk_row"
         (EBinop OEq (probe (EAccess (EVar "_pk_row") "k"))
            (EAtom (AEmptyBag None))))
      (EAtom (ABool true)).

  Definition put_expected : expr :=
    ERecord
      [("aux_tag",
         ERecord
           [("0", ELet (member "0") "acc"
                    (ELet new_node "tup"
                       (ETernop OInsert (EVar "acc")
                          (EAccess (EVar "tup") "k") (EVar "tup"))));
            ("1", EBinop OPlus
                    (ELet new_node "x" (EAccess (EVar "x") "size"))
                    (member "1"))])].

  Lemma put_adds_the_new :
    put_ins_of optimized = Some (put_guard_expected, put_expected).
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     The order of the two choices, measured.

     Listing the aggregate first makes the dictionary's rules run first, and
     then the sum's delete rule carves its correction term out of a filter
     the index rules have already gone past.  The correction is still a
     correction -- the total is not rebuilt -- but the rows it sums are found
     by SCANNING, so a delete costs a pass over the table instead of a
     probe.  And because that scan reads the list, the list survives: the
     erasure rule is reporting a real reader.

     This is the fourth rule-ordering hazard in the development (TableRep
     must be listed first; SetAgg before MinAgg; FilterEmptyToSetMem must
     not be enabled on a table with a unique-dict member) and, like the
     other three, it is a SILENT pessimization: the output is sound, passes
     the type checker, and is asymptotically worse.  A deterministic
     selector has to get this ordering right, which is why it is pinned
     here and not left as advice. *)
  Definition swapped_member (i : string) : expr :=
    EAccess (EAccess (ELoc "cache") "aux_tag") i.

  Lemma swapped_correction_scans :
    option_map snd (delete_of optimized_swapped)
    = Some (ERecord
              [("id_tag",
                 flatmap_filter_list the_list "r"
                   (EUnop ONot (EBinop OEq (EAccess (EVar "r") "k")
                                  (EAccess (EVar "q") "k")))
                   "r" None None);
               ("aux_tag",
                 ERecord
                   [("0", EBinop OMinus (swapped_member "0")
                            (sum_size (key_scan (EAccess (EVar "q") "k"))));
                    ("1", EBinop ODelete (swapped_member "1")
                            (EAccess (EVar "q") "k"))])]).
  Proof. vm_compute; reflexivity. Qed.

  Lemma swapped_keeps_the_list :
    installed_fields optimized_swapped = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ==================================================================
     THE LRU CHAIN -- the second derived structure the faithfulness note
     above declined, and the reason this file has a second program.

     WHAT IT IS IN THE SOURCE.  `head`, `tail` (:45-46) and LRUNode's
     `previous`/`next` are a doubly-linked list over the same nodes the map
     holds, and POSITION IN IT IS RECENCY.  Nothing stores a timestamp:
     get(:99) calls updateLRU(:213), which is remove(:217) then
     putHead(:232), and evict(:241) takes `tail`.

     WHY IT IS WORTH A SECOND PROGRAM.  Every other read in this
     development is order-insensitive, and the collection analysis only
     ever RELAXES -- annotate_collection's five patterns all weaken a list
     toward a bag or a set (CollectionTransf.v:6-23), and nothing anywhere
     demands a list.  So no subject before this one observed row order, and
     the row list was always dead the moment the indexes captured every
     read: erases_the_list, above, is this very table.  Here order is the
     MEANING.  The eviction reads the LAST row, so the list is not an
     artefact to be erased -- it is the data structure, and the index sits
     beside it rather than replacing it.

     HOW THE WRITES ARE SHAPED, which is faithfulness and not convenience.
     updateLRU is remove-then-putHead in the source, and it is two writes
     here for the same reason: each is a shape the guard elaboration
     recognises -- a filter, then a cons -- so the declared key costs one
     probe per write.  Written as a single expression instead (`the hit ++
     the rest`) the write would be WOther (Surface.v:125) and the
     declaration would re-check uniqueness over the whole table on every
     touch.  That is a fact about the guard elaboration, not about LRU, and
     it is why the shape below is the shape the source already has.

     WHAT IT MEASURES (harness `csv typed 200 400 800 1600`; work at 1600
     rows and the fitted exponent), and this is the most informative table
     in the file because most of it is NEGATIVE:

       kind        source     a     optimized     a      ratio
       contains    617100  0.99          1628  0.01    379.05x
       getTouch   2753196  1.00        812572  0.98      3.39x
       put        1576060  0.98        951424  0.98      1.66x
       evict      1503225  1.02       1503765  1.02      1.00x
       delete      811660  1.02        812280  1.01      1.00x

     ONE EXPONENT AND FOUR CONSTANTS, and the split is exactly the one the
     order demand predicts.  `contains` is a pure keyed lookup, so the index
     answers it outright: 0.99 to 0.01.  Every other operation has to
     REWRITE the row list -- the touch moves a row, the eviction and the
     delete drop one, the put does both -- and the list is the structure, so
     each of them stays linear and can only win a constant.  getTouch's
     3.39x is three list passes becoming one (the hit's scan and the cons's
     uniqueness scan both became probes, and the filter is what is left);
     put's 1.66x is its uniqueness scan becoming a probe; evict and delete
     were already one pass, so the index buys them nothing and -- the thing
     worth checking -- costs them nothing either, 1.00x, because both
     members are maintained incrementally rather than rebuilt.

     THE SENTENCE THIS SUBJECT EXISTS FOR: order as semantics costs the
     erasure, and the erasure is where the exponents came from.  Every other
     subject in this directory ends with its row list gone, and the
     asymptotic wins all come from that -- once nothing reads the list, a
     write stops touching n rows.  Here one read asks for the order, the
     list stays, and the optimizer is left serving the lookups beside it.

     AND THE PRICE OF AN UNNECESSARY ORDER DEMAND, measured on the same
     workload with the same index (named_cache_lru_ordered):

       getTouch   2753176  1.00       1428084  0.99      1.93x

     1.93x against 3.39x, so the demand costs 1.76x on that operation --
     812572 to 1428084 -- for a sublist that the declaration says holds at
     most one row.  Nothing else in the development exercises the demand
     analysis in this direction: every other subject is relaxed as far as it
     can go.

     AND THE ISOLATION, which is the number to quote.  prog_lru_noevict_s is
     this program with the eviction replaced by one more report: every write
     is the same, the move-to-front included, and nothing asks what the
     order is.  The list is then erased (lru_noevict_erases_the_list), and
     the same operations measure:

       kind        order read (this program)   order never read
       contains      1628  a=0.01   379.05x      1628  a=0.01   379.05x
       getTouch    812572  a=0.98     3.39x      4332  a=0.01   635.55x
       put         951424  a=0.98     1.66x      2584  a=0.01   609.93x
       delete      812280  a=1.01     1.00x       840  a=0.02   966.26x

     READING THE ORDER ONCE COSTS EVERY WRITE ITS EXPONENT.  Two to three
     orders of magnitude, and `contains` is identical in both columns
     because it never needed the list.  The difference between the two
     programs is one read.

     WHAT WOULD CLOSE IT, and it is not an insert-by-position operator.
     Every write here is linear because every write REBUILDS THE WHOLE LIST:
     the move-to-front filters it, the eviction filters it, the put filters
     it.  Kafka does each of those in O(1) by splicing a node whose address
     it already holds -- `node.previous.next = node.next` (:219) -- which is
     a handle, not an index.  Adding ONth and OInsertAt would let a program
     speak about positions, but it would still have to SCAN to find the
     position, so none of the three writes above would get faster.  Serving
     them needs a sequence whose removal and insertion are O(1) at a handle,
     and an index kind that hands out handles.

     So this is a LIMIT rather than a missing rewrite, and the honest form of
     it is: the only way to get these writes sublinear in the language as it
     stands is to hand-build the chain as `prev`/`next` attributes with a
     dictionary on the key -- which is exactly the derived structure this
     work exists to stop people writing by hand.  The row list is where
     order lives, and a list has no cheap middle.
     ================================================================== *)

  (* cache.get(key) returning the node rather than counting it: the rows
     carrying the key, in canonical order.  At most one, k being declared
     unique.

     THE ESort IS LOAD-BEARING.  unique_lookup_head matches a BAG-level
     filter (UniqueIndexUse.v:434), so a keyed read whose ORDER is demanded
     cannot be served from the index at all.  ESort LikeList is the
     programmer saying the order of this at-most-one-row sublist does not
     matter, and annotate_collection turns it into the bag form the rule
     needs.  prog_lru_ordered_s below is the same program without it, and
     lru_ordered_front_scans is what that costs. *)
  Definition hit_sorted (key_e : expr) : expr :=
    ESort LikeList
      (EFlatmap LikeList (ELoc "cache") "r"
         (EIf (EBinop OEq (EAccess (EVar "r") "k") key_e)
            (EBinop OCons (EVar "r") (EAtom (ANil None))) (EAtom (ANil None)))).

  Definition hit_ordered (key_e : expr) : expr :=
    EFlatmap LikeList (ELoc "cache") "r"
      (EIf (EBinop OEq (EAccess (EVar "r") "k") key_e)
         (EBinop OCons (EVar "r") (EAtom (ANil None))) (EAtom (ANil None))).

  (* tail (:46), as a fold: fold_right keeping the accumulator once it is
     set, so the LAST element wins.  THIS IS THE ORDER-OBSERVING READ, and
     no collection relaxation can touch it -- annotate_collection
     recognises exactly two fold shapes, the sum at CollectionTransf.v:9
     and the min at :13, and this is neither.  Swap two rows and the answer
     changes, which is the whole point. *)
  Definition eldest_key_of (src : expr) : expr :=
    EFold (EFlatmap LikeList src "r"
             (EBinop OCons (EAccess (EVar "r") "k") (EAtom (ANil None))))
      (EAtom (ANone (Some TString))) "_v" "_acc"
      (EOptMatch (EVar "_acc") (EUnop OSome (EVar "_v")) "_x" (EVar "_acc")).

  Definition eldest_key : expr := eldest_key_of (ELoc "cache").

  Definition eldest_rows_of (src : expr) : expr :=
    EOptMatch (eldest_key_of src) (EAtom (ANil (Some TString))) "x"
      (EBinop OCons (EVar "x") (EAtom (ANil None))).

  (* `if (tail == null) return;` (:242), as a collection: the eldest key if
     there is one, and nothing if the cache is empty.

     WHY NOT MATCH ON THE OPTION IN THE ASSIGNMENT.  Writing the eviction as
     `cache := match eldest with none => cache | some ek => without ek` makes
     the write WOther (Surface.v:125) and, worse, buries the filter inside an
     EOptMatch where filter_of cannot see it -- so the dictionary member is
     REBUILT on every eviction.  Measured, that cost 2.0x against the
     source's own filter.  Stepping over the at-most-one eldest key instead
     leaves the write a plain keyed filter, which is the shape both the guard
     elaboration and the index's delete rule recognise.  Same shape the touch
     uses, and the same reason. *)
  Definition eldest_rows : expr := eldest_rows_of (ELoc "cache").

  (*   0  delete(key)                          :273
       1  put(key, node), remove then putHead   :174
       2  get(key): report the hit, then updateLRU  :99, :213
       3  evict(): drop the tail                :241
       _  the plain map lookup put() does before it branches  :174 *)
  Definition prog_lru_gen (ds : list decl) (hit : expr -> expr) : scommand :=
    SLetConstrained "cache" row_ty ds
      (SForeach (EVar "ops") "q"
         (dispatch 0
            (SAssign "cache" (without (EAccess (EVar "q") "k")) SSkip)
            (dispatch 1
               (SSeq (SAssign "cache" (without node_key) SSkip)
                  (SAssign "cache"
                     (EBinop OCons (EAccess (EVar "q") "node") (ELoc "cache"))
                     SSkip))
               (dispatch 2
                  (SSeq (report get_key)
                     (SLet (hit (EAccess (EVar "q") "k")) "hit_rows"
                        (SSeq
                           (SAssign "cache"
                              (without (EAccess (EVar "q") "k")) SSkip)
                           (SForeach (EVar "hit_rows") "hr"
                              (SAssign "cache"
                                 (EBinop OCons (EVar "hr") (ELoc "cache"))
                                 SSkip)))))
                  (dispatch 3
                     (SForeach eldest_rows "ek"
                        (SAssign "cache" (without (EVar "ek")) SSkip))
                     (report get_key)))))).

  Definition prog_lru_s (ds : list decl) : scommand :=
    prog_lru_gen ds hit_sorted.

  Definition prog_lru_ordered_s (ds : list decl) : scommand :=
    prog_lru_gen ds hit_ordered.

  (* THE CONTROL THAT ISOLATES THE ORDER READ.  The same five arms with the
     eviction replaced by one more report, so the program does every write
     the LRU does -- including the move-to-front -- and never asks what the
     order is.  Nothing then reads the row list, the list is erased, and the
     same `delete` goes from a constant to an exponent.  The difference
     between this program and prog_lru_s is one read. *)
  Definition prog_lru_noevict_s (ds : list decl) : scommand :=
    SLetConstrained "cache" row_ty ds
      (SForeach (EVar "ops") "q"
         (dispatch 0
            (SAssign "cache" (without (EAccess (EVar "q") "k")) SSkip)
            (dispatch 1
               (SSeq (SAssign "cache" (without node_key) SSkip)
                  (SAssign "cache"
                     (EBinop OCons (EAccess (EVar "q") "node") (ELoc "cache"))
                     SSkip))
               (dispatch 2
                  (SSeq (report get_key)
                     (SLet (hit_sorted (EAccess (EVar "q") "k")) "hit_rows"
                        (SSeq
                           (SAssign "cache"
                              (without (EAccess (EVar "q") "k")) SSkip)
                           (SForeach (EVar "hit_rows") "hr"
                              (SAssign "cache"
                                 (EBinop OCons (EVar "hr") (ELoc "cache"))
                                 SSkip)))))
                  (dispatch 3 (report get_key) (report get_key)))))).

  Definition elaborated_lru (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_lru_s ds).

  Definition elaborated_lru_ordered (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_lru_ordered_s ds).

  Definition elaborated_lru_noevict (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_lru_noevict_s ds).

  (* no aggregate: this program asks for no total.  One index, and the row
     list beside it. *)
  Definition anno_lru : canno_command :=
    CAC (("cache", (row_ty, decls)) :: cenv_rm "cache" []) O
      basics [UniqueDictIdx "k"] [] (elaborated_lru decls).

  Definition optimized_lru : command :=
    apply_optimize_anno_constrained anno_lru init_Gstore init_Genv.

  Definition anno_lru_ordered : canno_command :=
    CAC (("cache", (row_ty, decls)) :: cenv_rm "cache" []) O
      basics [UniqueDictIdx "k"] [] (elaborated_lru_ordered decls).

  Definition optimized_lru_ordered : command :=
    apply_optimize_anno_constrained anno_lru_ordered init_Gstore init_Genv.

  Definition anno_lru_noevict : canno_command :=
    CAC (("cache", (row_ty, decls)) :: cenv_rm "cache" []) O
      basics [UniqueDictIdx "k"] [] (elaborated_lru_noevict decls).

  Definition optimized_lru_noevict : command :=
    apply_optimize_anno_constrained anno_lru_noevict init_Gstore init_Genv.

  (* ---- projections for the LRU program's five arms ---- *)

  Fixpoint lru_loop (c : command) : command :=
    match c with
    | CLetMut _ _ c' => lru_loop c'
    | CForeach _ _ c' => c'
    | _ => c
    end.

  Fixpoint lru_arm (n : nat) (c : command) : option command :=
    match n, c with
    | O, CIf _ c1 _ => Some c1
    | S n', CIf _ _ c2 => lru_arm n' c2
    | _, _ => None
    end.

  (* the collection an arm scrutinises: the touch's hit (behind its
     report), and the eviction's at-most-one eldest key. *)
  Definition arm_let (c : option command) : option expr :=
    match c with
    | Some (CLet e _ _) => Some e
    | Some (CForeach e _ _) => Some e
    | Some (CSeq _ (CLet e _ _)) => Some e
    | _ => None
    end.

  Definition lru_at (n : nat) (c : command) : option expr :=
    arm_let (lru_arm n (lru_loop c)).

  (* the list-level counterpart of key_scan: the scan that is left when the
     read's ORDER is demanded and the bag-level rule cannot fire *)
  Definition key_scan_list (key_e : expr) : expr :=
    flatmap_filter_list the_list "r"
      (EBinop OEq (EAccess (EVar "r") "k") key_e) "r" None None.

  (* ------------------------------------------------------------------
     WHAT THE LRU PROGRAM PRODUCED.

     THE HEADLINE, and the first of its kind in this development: the row
     list is NOT erased.  Compare erases_the_list above -- the same table,
     the same declaration, the same index -- where the list went away
     because every read of it had been captured.  Here one read cannot be
     captured by any index, because what it asks for is the ORDER. *)
  Lemma lru_keeps_the_list :
    installed_fields optimized_lru = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* and the index is installed beside it and does serve the keyed reads:
     get(key)'s node is one probe, wrapped back into a list by the sort
     that made the read order-insensitive in the first place *)
  Lemma lru_touch_is_a_probe :
    lru_at 2 optimized_lru
    = Some (ESort LikeBag (probe (EAccess (EVar "q") "k"))).
  Proof. vm_compute; reflexivity. Qed.

  (* THE ORDER-OBSERVING READ, UNTOUCHED.  evict() reads the eldest key off
     the row list with a fold the collection analysis cannot relax: it is
     neither the sum at CollectionTransf.v:9 nor the min at :13, and no
     index rule matches a fold.  The term below is the SOURCE term with the
     table read replaced by the list member -- that is, the installation
     moved it and nothing else touched it. *)
  Lemma lru_evict_reads_the_list_in_order :
    lru_at 3 optimized_lru = Some (eldest_rows_of the_list).
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     AND WHAT AN UNNECESSARY ORDER DEMAND COSTS.

     prog_lru_ordered_s is the same program with the front sublist written
     as a plain filter instead of a sorted one.  The two agree whenever the
     key is unique, which the declaration says it is -- so this is a
     difference in what the program ASKS FOR, not in what it computes.  And
     the index, installed and maintained either way, cannot serve the read
     at all: unique_lookup_head matches a bag-level filter, so a read whose
     order is demanded stays a scan.

     This is the demand analysis showing its teeth in the direction nothing
     else in the development exercises: every other subject is relaxed as
     far as it can go, and here one subterm that could have been relaxed is
     not, with a measured price. *)
  Lemma lru_ordered_front_scans :
    lru_at 2 optimized_lru_ordered
    = Some (key_scan_list (EAccess (EVar "q") "k")).
  Proof. vm_compute; reflexivity. Qed.

  (* the eviction is unaffected -- it was never relaxable *)
  Lemma lru_ordered_evict_is_the_same :
    lru_at 3 optimized_lru_ordered = Some (eldest_rows_of the_list).
  Proof. vm_compute; reflexivity. Qed.

  Lemma lru_ordered_keeps_the_list :
    installed_fields optimized_lru_ordered = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     AND THE CONTROL, which is what makes the whole claim an isolation
     rather than a comparison between two different programs.  Take the
     eviction away and nothing asks for the order any more -- every write
     is the same, the move-to-front included -- and the list is erased. *)
  Lemma lru_noevict_erases_the_list :
    installed_fields optimized_lru_noevict = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     And all of it is sound: the program above computes what the fold-and-
     scan program computes, on every store and environment.  Both orderings
     are sound -- the hazard costs time, never correctness, which is exactly
     why it is silent. *)

  Lemma row_ty_wf : type_wf row_ty.
  Proof.
    unfold row_ty. repeat constructor; cbn; intuition congruence.
  Qed.

  Lemma query_ty_wf : type_wf query_ty.
  Proof.
    unfold query_ty, row_ty. repeat constructor; cbn; intuition congruence.
  Qed.

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
      exists [("k", TString); ("size", TInt)], TString;
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

  Theorem optimized_swapped_sound :
    well_typed init_Gstore init_Genv optimized_swapped /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized_swapped
        = interp_command store env (elaborated decls).
  Proof.
    unfold optimized_swapped, anno_swapped, elaborated, prog_s.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply row_ty_wf
      | apply incl_refl | apply decls_wf | apply elaborated_well_typed ].
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

  Lemma elaborated_lru_well_typed :
    well_typed init_Gstore init_Genv (elaborated_lru decls).
  Proof.
    eapply command_typechecker_sound with (c := elaborated_lru decls).
    1: apply init_Gstore_wf.
    1: apply init_Genv_wf.
    reflexivity.
  Qed.

  Lemma elaborated_lru_noevict_well_typed :
    well_typed init_Gstore init_Genv (elaborated_lru_noevict decls).
  Proof.
    eapply command_typechecker_sound with (c := elaborated_lru_noevict decls).
    1: apply init_Gstore_wf.
    1: apply init_Genv_wf.
    reflexivity.
  Qed.

  Theorem optimized_lru_noevict_sound :
    well_typed init_Gstore init_Genv optimized_lru_noevict /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized_lru_noevict
        = interp_command store env (elaborated_lru_noevict decls).
  Proof.
    unfold optimized_lru_noevict, anno_lru_noevict, elaborated_lru_noevict,
      prog_lru_noevict_s.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply row_ty_wf
      | apply incl_refl | apply decls_wf
      | apply elaborated_lru_noevict_well_typed ].
  Qed.

  Lemma elaborated_lru_ordered_well_typed :
    well_typed init_Gstore init_Genv (elaborated_lru_ordered decls).
  Proof.
    eapply command_typechecker_sound with (c := elaborated_lru_ordered decls).
    1: apply init_Gstore_wf.
    1: apply init_Genv_wf.
    reflexivity.
  Qed.

  (* The order-observing program is sound for the same reason every other
     one is, and that is the point worth stating: nothing in the soundness
     argument knows that this table's order is load-bearing.  The rules
     preserve the denotation, and the denotation of a list includes its
     order, so a rule that would have reordered this table simply does not
     match. *)
  Theorem optimized_lru_sound :
    well_typed init_Gstore init_Genv optimized_lru /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized_lru
        = interp_command store env (elaborated_lru decls).
  Proof.
    unfold optimized_lru, anno_lru, elaborated_lru, prog_lru_s, prog_lru_gen.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply row_ty_wf
      | apply incl_refl | apply decls_wf | apply elaborated_lru_well_typed ].
  Qed.

  Theorem optimized_lru_ordered_sound :
    well_typed init_Gstore init_Genv optimized_lru_ordered /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized_lru_ordered
        = interp_command store env (elaborated_lru_ordered decls).
  Proof.
    unfold optimized_lru_ordered, anno_lru_ordered, elaborated_lru_ordered,
      prog_lru_ordered_s, prog_lru_gen.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply row_ty_wf
      | apply incl_refl | apply decls_wf
      | apply elaborated_lru_ordered_well_typed ].
  Qed.
End WithConcreteMaps.
