Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.TransfUtils fiat2.FlatmapTransf fiat2.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   Source
     apache/kafka, commit 995cfcf9 (clients/src/main/java/org/apache/
       kafka/common/Cluster.java)
     the constructor at :114, the accessors at :289, :298, :307, :317, :326

       for (PartitionInfo p : partitions) {
           tmpPartitionsByTopicPartition.put(new TopicPartition(p.topic(), p.partition()), p);
           tmpPartitionsByTopic.computeIfAbsent(p.topic(), topic -> new ArrayList<>()).add(p);
           if (p.leader() == null || p.leader().isEmpty())
               continue;
           List<PartitionInfo> partitionsForNode = ...tmpPartitionsByNode.get(p.leader().id());
           partitionsForNode.add(p);
       }

     One collection of PartitionInfo, five maps derived from it in the
     constructor, and -- the detail that makes this example worth having --
     the collection itself is NEVER STORED.  Cluster has fields for every
     map and no field for `partitions`.

   What the composite key measured (harness alternatives, typed,
   200/400/800/1600 rows; work at 1600 and the fitted exponent).  Every row
   below is against configuration 0, the selector's pick -- SplitIf with the
   two single-attribute dictionaries:

                       build   forTopic  forNode  onePartition  available
     chosen (cfg 0)   151289       1260     1322          5000       4488
                      a=1.02     a=0.00   a=0.00        a=0.00     a=0.00
     cfg 1 unsplit    151293       1260     1322       1388320    1162568
                      a=1.02     a=0.00   a=0.00        a=1.00     a=1.00
     cfg 2 composite  250927       1280     1342          1800    1162568
                      a=1.01     a=0.00   a=0.00        a=0.01     a=1.00
     cfg 3 cmp+split  250923       1280     1342          5020       4508
                      a=1.01     a=0.00   a=0.00        a=0.00     a=0.00

   Read it against configuration 1, not against 0: 1 and 2 differ ONLY in the
   composite index, so that pair isolates it.  On onePartition the scan
   becomes a probe -- 1388320 to 1800, 771x, and the exponent from 1.00 to
   0.01.  It costs 1.66x to build, which is the third member.

   Against configuration 0 the same read is only 2.8x better (5000 to 1800),
   and that is a CONSTANT, not an exponent.  THE CAVEAT TO REPEAT WHENEVER
   THAT NUMBER IS USED: the generator keeps one topic per 8 rows
   (gen.ml bucket_size), so the residual filter configuration 0 leaves scans
   8 rows however large the table is.  What the composite key saves against a
   SPLIT conjunction is that filter, so its advantage there grows with bucket
   size and is small here by construction.  What it saves against an UNSPLIT
   conjunction is the whole scan, which is the exponent above.

   And configuration 3 is the hazard with a price on it: identical to
   configuration 0 on every read, to within the one extra record field, while
   paying configuration 2's 1.7x build.  An index installed, maintained in
   the install, and never read.

   Pattern
     A1a, built once, multi-index.  Unlike Keycloak_CachedRealm the keys are
     not unique: each map is key-to-many, so each bucket is a bag of rows.
     D4 composite key, for the accessor at :289, and it is SERVED here rather
     than only noted -- a dictionary keyed on a record of the two attributes,
     which is the key Kafka itself constructs.

   Claim
     C3 and C4.  The optimizer reaches Kafka's own storage decision from a
     program that names no index: keep the maps, drop the list.  Contrast
     Keycloak_CachedRealm, where the same erasure rule keeps the list --
     because there a query reads it.  One rule, two code bases, each time the
     representation the programmer chose by hand.

   Faithfulness -- what this translation drops, and why
     * PartitionInfo also carries replicas, inSyncReplicas and
       offlineReplicas.  None is a key and none is read by the accessors
       modelled here.
     * `leader` is a nullable Node in Java; it is TOption TInt here, holding
       the node id.  Kafka's loop SKIPS the rows whose leader is null, so
       partitionsByNode is a partial index.  Keyed by the option instead, the
       index is total and those rows sit in the None bucket, which no query
       probes -- the same answers from a structure with no side condition.
     * `new TopicPartition(p.topic(), p.partition())` is a composite key.
       The query is written as the conjunctive filter it is, and both answers
       to it are measured below rather than one being hidden:
       one_partition_probes_then_filters is what a single-attribute index
       leaves (a probe on topic and a residual filter, O(partitions in the
       topic)), and one_partition_probes_composite is the same read served by
       a dictionary keyed on BOTH attributes, which is one probe.  The second
       needs the conjunction left whole, so it is a configuration without
       SplitIf; composite_unused_when_split is what happens when it is not.
     * The three Set fields, the controller, the cluster id and the
       topicIds/topicNames pair belong to other collections and are out of
       scope here.
     * Nothing is added.  Cluster is immutable -- withPartitions(:227) builds
       a new one -- so this program only reads, and the table is initialised
       from an input collection exactly as the constructor is.

   Expected
     Both maps installed off the input collection; the two single-attribute
     accessors become probes; the two conjunctive accessors probe on topic
     and filter the bucket; and no query reads the list, so the list is
     erased -- matching Cluster, which has no partitions field.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort
             [("topic", TString); ("partition", TInt); ("leader", TOption TInt)]).

Definition query_ty :=
  TRecord (record_sort
             [("kind", TInt); ("topic", TString); ("part", TInt); ("node", TInt)]).

Section WithConcreteMaps.

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string (value) := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* ---- the source program: five accessors, no index named ---- *)

  Definition by_topic : expr :=
    EBinop OEq (EAccess (EVar "p") "topic") (EAccess (EVar "q") "topic").

  Definition has_leader : expr :=
    EUnop ONot (EBinop OEq (EAccess (EVar "p") "leader")
                  (EAtom (ANone (Some TInt)))).

  (* [p <- partitions, check(pred), ret p], counted *)
  Definition filt (pred : expr) : expr :=
    EUnop OLength
      (EFlatmap LikeList (ELoc "partitions") "p"
         (EIf pred (EBinop OCons (EVar "p") (EAtom (ANil None))) (EAtom (ANil None)))).

  (* partitionsForTopic / partitionCountForTopic (:298, :307) *)
  Definition q_for_topic : expr := filt by_topic.

  (* partitionsForNode (:326) *)
  Definition q_for_node : expr :=
    filt (EBinop OEq (EAccess (EVar "p") "leader")
            (EUnop OSome (EAccess (EVar "q") "node"))).

  (* partition(new TopicPartition(topic, part)) (:289) *)
  Definition q_one : expr :=
    filt (EBinop OAnd by_topic
            (EBinop OEq (EAccess (EVar "p") "partition") (EAccess (EVar "q") "part"))).

  (* availablePartitionsForTopic (:317) *)
  Definition q_available : expr :=
    filt (EBinop OAnd by_topic has_leader).

  Definition report (e : expr) : command :=
    CLet e "n"
      (CAssign "outputs"
         (EBinop OCons (EUnop OStringOfInt (EVar "n")) (ELoc "outputs"))).

  Definition dispatch (k : Z) (thn els : command) : command :=
    CIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt k))) thn els.

  Definition prog : command :=
    CLetMut (EVar "partitions_tbl") "partitions"
      (CForeach (EVar "queries") "q"
         (dispatch 0 (report q_for_topic)
            (dispatch 1 (report q_for_node)
               (dispatch 2 (report q_one)
                  (report q_available))))).

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put (map.put map.empty "partitions_tbl" (TList row_ty))
      "queries" (TList query_ty).

  (* ---- four configurations ----

     0 and 1 differ only in whether a conjunctive filter is split before the
     collection phase.  2 and 3 add a COMPOSITE dictionary on (topic,
     partition), the key Kafka actually builds -- `new TopicPartition(topic,
     partition)` -- and differ in the same way, which is what makes the
     ordering between SplitIf and a composite index measurable rather than
     merely stated. *)

  Definition heuristics :=
    [ AC [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap; SplitIf]
        [[DictIdx "topic"; DictIdx "leader"]]
    ; AC [PushdownCollection; AnnotateCollection]
        [[DictIdx "topic"; DictIdx "leader"]]
    (* the composite key, and NO SplitIf: the composite rule matches the
       conjunction whole, so it must be given its chance before anything
       takes the conjunction apart *)
    ; AC [PushdownCollection; AnnotateCollection]
        [[CompositeDictIdx "topic" "partition"; DictIdx "topic"; DictIdx "leader"]]
    (* the same choices WITH SplitIf, which is the hazard *)
    ; AC [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap; SplitIf]
        [[CompositeDictIdx "topic" "partition"; DictIdx "topic"; DictIdx "leader"]]
    ].

  Definition prog_transformed :=
    map (fun heu => apply_optimize_anno (heu prog) init_Gstore init_Genv)
      heuristics.

  (* ---- projections, so every claim is an equality of closed terms ---- *)

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

  (* the expression bound in the n-th arm of the dispatch chain *)
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

  (* ---- the expected output ---- *)

  (* one pass over the input collection, appending each row to its bucket *)
  Definition bucket_by (attr : string) : expr :=
    EFold (EVar "partitions_tbl") (EAtom (AEmptyDict Unranged None)) "tup" "acc"
      (ETernop OInsert (EVar "acc") (EAccess (EVar "tup") attr)
         (EBinop OBagInsert
            (EOptMatch (EBinop OLookup (EVar "acc") (EAccess (EVar "tup") attr))
               (EAtom (AEmptyBag None)) "x" (EVar "x"))
            (EVar "tup"))).

  Definition install_expected : expr :=
    ERecord [("aux_tag",
               ERecord [("0", bucket_by "topic"); ("1", bucket_by "leader")])].

  Definition probe (i : string) (k : expr) : expr :=
    EOptMatch
      (EBinop OLookup (EAccess (EAccess (ELoc "partitions") "aux_tag") i) k)
      (EAtom (AEmptyBag None)) "b" (EVar "b").

  (* a residual filter over whatever collection it is given *)
  Definition refine (src pred : expr) : expr :=
    EFlatmap LikeBag src "p"
      (EIf pred (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "p"))
         (EAtom (AEmptyBag None))).

  Definition scan (pred : expr) : expr :=
    refine (EUnop OBagOfList (EAccess (ELoc "partitions") "id_tag")) pred.

  Definition topic_key : expr := EAccess (EVar "q") "topic".

  Definition part_eq : expr :=
    EBinop OEq (EAccess (EVar "p") "partition") (EAccess (EVar "q") "part").

  (* ================= configuration 0: with SplitIf ================= *)

  (* Two choices, two members, each a key-to-bag dictionary folded in one
     pass over the input collection -- Cluster's constructor loop, derived.
     Both are Unranged: a point lookup owes a backend no ordering, which is
     the honest reading of Kafka's two HashMaps. *)
  Lemma installs_both_maps :
    install_of (nth 0 prog_transformed CSkip) = Some install_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* And nothing reads the list any more, so the erasure pass drops it: the
     table IS its indexes.  Cluster has no partitions field for exactly this
     reason. *)
  Lemma drops_the_list :
    installed_fields (nth 0 prog_transformed CSkip) = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* partitionsForTopic: one probe. *)
  Lemma for_topic_probes :
    query_at 0 (nth 0 prog_transformed CSkip)
    = Some (EACFold AGCount (probe "0" topic_key)).
  Proof. vm_compute; reflexivity. Qed.

  (* partitionsForNode: one probe, at key `some nodeId`.  Kafka's map holds
     only the rows with a known leader; this one holds all of them, and the
     rows Kafka skipped sit in the None bucket, which nothing probes.  The
     partial index needed no partiality. *)
  Lemma for_node_probes :
    query_at 1 (nth 0 prog_transformed CSkip)
    = Some (EACFold AGCount
              (probe "1" (EUnop OSome (EAccess (EVar "q") "node")))).
  Proof. vm_compute; reflexivity. Qed.

  (* partition(topic, partition): the composite key.  There is no composite
     index, and this is what its absence costs -- not the index, only the
     last narrowing: the probe picks the topic's bucket and the residual
     filter picks the partition out of it.  O(partitions in the topic) where
     a composite key would be O(1), against O(all partitions) unoptimized. *)
  Lemma one_partition_probes_then_filters :
    query_at 2 (nth 0 prog_transformed CSkip)
    = Some (EACFold AGCount (refine (probe "0" topic_key) part_eq)).
  Proof. vm_compute; reflexivity. Qed.

  (* availablePartitionsForTopic: probe on topic, then keep the rows with a
     leader.  Kafka precomputes this map, but the loop it precomputes it with
     (:176-179) is this expression: iterate the topic's partitions, keep the
     ones whose leader is non-null.  The optimizer did not materialise it;
     it did derive the same traversal. *)
  Lemma available_probes_then_filters :
    query_at 3 (nth 0 prog_transformed CSkip)
    = Some (EACFold AGCount (refine (probe "0" topic_key) has_leader)).
  Proof. vm_compute; reflexivity. Qed.

  (* ================= configuration 1: without SplitIf ================= *)

  (* The single-attribute accessors are unaffected: their filters were never
     conjunctions. *)
  Lemma for_topic_probes_either_way :
    query_at 0 (nth 1 prog_transformed CSkip)
    = Some (EACFold AGCount (probe "0" topic_key)).
  Proof. vm_compute; reflexivity. Qed.

  Lemma for_node_probes_either_way :
    query_at 1 (nth 1 prog_transformed CSkip)
    = Some (EACFold AGCount
              (probe "1" (EUnop OSome (EAccess (EVar "q") "node")))).
  Proof. vm_compute; reflexivity. Qed.

  (* The conjunctive ones are not.  The index rule's pattern is a filter
     whose body is a singleton, and a conjunction's outer test does not have
     one until the conjunction is split, so both stay full scans. *)
  Lemma one_partition_scans_unsplit :
    query_at 2 (nth 1 prog_transformed CSkip)
    = Some (EACFold AGCount (scan (EBinop OAnd by_topic part_eq))).
  Proof. vm_compute; reflexivity. Qed.

  Lemma available_scans_unsplit :
    query_at 3 (nth 1 prog_transformed CSkip)
    = Some (EACFold AGCount (scan (EBinop OAnd by_topic has_leader))).
  Proof. vm_compute; reflexivity. Qed.

  (* And because those scans still read the list, the list stays -- which is
     the storage Cluster does not have.  Splitting the conjunctions is what
     buys the representation, not just the speed. *)
  Lemma unsplit_keeps_the_list :
    installed_fields (nth 1 prog_transformed CSkip) = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ========== configurations 2 and 3: the composite key ========== *)

  (* The key Kafka builds by hand.  Written in the order the index was
     declared; the stored key is record_sort's order, and the two agree
     because interp canonicalises an ERecord literal either way -- which is
     what makes a composite key an ordinary dictionary key. *)
  Definition tp_key : expr :=
    ERecord [("topic", EAccess (EVar "q") "topic");
             ("partition", EAccess (EVar "q") "part")].

  (* THE D4 GAP, CLOSED.  partition(new TopicPartition(topic, part)) is one
     probe: no residual filter, and so no O(partitions in the topic) scan of
     the topic's bucket.  Compare one_partition_probes_then_filters, which is
     the same read under configuration 0. *)
  Lemma one_partition_probes_composite :
    query_at 2 (nth 2 prog_transformed CSkip)
    = Some (EACFold AGCount (probe "0" tp_key)).
  Proof. vm_compute; reflexivity. Qed.

  (* and the single-attribute accessors are untouched, at the tags the
     composite member displaced them to *)
  Lemma for_topic_probes_with_composite :
    query_at 0 (nth 2 prog_transformed CSkip)
    = Some (EACFold AGCount (probe "1" topic_key)).
  Proof. vm_compute; reflexivity. Qed.

  Lemma for_node_probes_with_composite :
    query_at 1 (nth 2 prog_transformed CSkip)
    = Some (EACFold AGCount (probe "2" (EUnop OSome (EAccess (EVar "q") "node")))).
  Proof. vm_compute; reflexivity. Qed.

  (* What configuration 2 does NOT get, pinned rather than described: without
     SplitIf, availablePartitionsForTopic stays a scan, so the list survives.
     The composite key buys the conjunctive POINT read and nothing else. *)
  Lemma available_scans_with_composite :
    query_at 3 (nth 2 prog_transformed CSkip)
    = Some (EACFold AGCount (scan (EBinop OAnd by_topic has_leader))).
  Proof. vm_compute; reflexivity. Qed.

  Lemma composite_keeps_the_list :
    installed_fields (nth 2 prog_transformed CSkip) = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* THE HAZARD, EXECUTABLE.  Configuration 3 asks for the same four things
     and adds SplitIf.  SplitIf peels the first conjunct off and hands it to
     the dictionary on topic, after which the composite rule's pattern no
     longer matches -- so the composite index is INSTALLED AND NEVER READ,
     and the read is the probe-then-filter of configuration 0 again.

     This is a rule-ordering hazard of a kind the list did not yet have: not
     two rules racing for one read, but a BASIC rewrite destroying the shape
     an index rule needs.  Its cost is not a slower read but an index paid
     for in full and never used. *)
  Lemma composite_unused_when_split :
    query_at 2 (nth 3 prog_transformed CSkip)
    = Some (EACFold AGCount (refine (probe "1" topic_key) part_eq)).
  Proof. vm_compute; reflexivity. Qed.

  (* ================= soundness ================= *)

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
