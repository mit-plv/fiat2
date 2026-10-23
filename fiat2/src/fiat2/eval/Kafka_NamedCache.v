Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.FlatmapForms fiat2.OptimizeAnno.
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
       it answers a different question: which row is eldest.  evict() is a
       top-1-by-recency query (D7), and it is not modelled: it would need a
       recency attribute and a maintained extremum over it, which is what
       MinAgg is for, and pairing the two is beyond what this file claims.
       What evict() contributes here is its size accounting (:249), which is
       delete's (:281).
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
         (EBinop OCons (EUnop OIntToString (EVar "n")) (ELoc "outputs")) SSkip).

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
    flatmap_filter_bag (EBagOf the_list) "r"
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
                  ("1", sum_size (EBagOf empty_rows))])].

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
End WithConcreteMaps.
