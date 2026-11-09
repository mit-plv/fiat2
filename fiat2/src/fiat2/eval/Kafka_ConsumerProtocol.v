Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem
  fiat2.TypeSound fiat2.TransfSound fiat2.IndexInterface fiat2.rules.CollectionTransf
  fiat2.TransfUtils fiat2.rules.FlatmapForms fiat2.rules.FlatmapTransf fiat2.index.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.pipeline.Pipeline fiat2.constraint.Decl fiat2.constraint.Surface fiat2.rules.SortBy.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString
  coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

(* ============================================================
   Source
     apache/kafka
     clients/src/main/java/org/apache/kafka/clients/consumer/internals/
       ConsumerProtocol.java:83-92  (serializeSubscription)

       List<TopicPartition> ownedPartitions = new ArrayList<>(subscription.ownedPartitions());
       ownedPartitions.sort(Comparator.comparing(TopicPartition::topic)
                                      .thenComparing(TopicPartition::partition));
       ConsumerProtocolSubscription.TopicPartition partition = null;
       for (TopicPartition tp : ownedPartitions) {
           if (partition == null || !partition.topic().equals(tp.topic())) {
               partition = new ConsumerProtocolSubscription.TopicPartition().setTopic(tp.topic());
               data.ownedPartitions().add(partition);
           }
           partition.partitions().add(tp.partition());
       }

   Why this subject exists
     A two-key ascending comparator -- `comparing(topic).thenComparing(partition)`
     -- over a HETEROGENEOUS key: topic is a String and partition an int.
     That is the case the desugaring in `SortBy.v` exists for, and the case
     a simpler encoding cannot reach: a key held as a `TList` would need all
     its components at one type, so the key has to be a RECORD, and then
     `record_compare` fixes the comparison order by FIELD NAME.  `order by
     topic, partition` therefore elaborates to a projection onto

       { a0_topic ; a1_partition ; z_row }

     whose canonical order IS the comparator the source wrote.  Nothing is
     added to the language.

     The sorted order is then OBSERVED twice, and both reads are the
     source's: the list goes on the wire in that order (`data.setTopics`
     at :79 does the same for the topic list), and the loop at :86-92
     compares each element with its neighbour to decide where one
     `ConsumerProtocolSubscription.TopicPartition` ends and the next
     begins.  A different order is a different message.

   Pattern
     A1a built-once.  No code claimed from the catalogue for the sort
     itself; the pattern is stated here in prose, as
     `Jenkins_DependentPlugins` and `Netbox_TemplateExtensions` do.

   Claim
     C1.  The sort the programmer wrote by hand with a comparator chain is
     reached by the collection hierarchy alone -- it is an `ESort` of a
     projection, with no comparator in the language and no operator added.

   Faithfulness -- what this translation drops, and why
     * `TopicPartition` carries only topic and partition, which is all the
       comparator and the loop read.
     * The loop builds a grouped message.  What is modelled is the two
       things that grouping is a function of: the wire ORDER, folded into
       one string so that the order is observable in a VALUE rather than in
       a side effect, and the NUMBER of groups, which is the number of
       adjacent pairs whose topics differ.  The group count is chosen over
       the grouped structure itself because a boundary between adjacent
       elements is direction-SYMMETRIC: `EFold` is a fold_right, so a
       run would otherwise be detected at its last element rather than its
       first and the topic label would come out after its partitions
       instead of before.  The grouping is the same either way; the count
       says so without the wart.
     * `userData`, `rackId` and `generationId` are not collections of this
       table.
     * `subscription.ownedPartitions()` is given to the serializer, so the
       table is bound from an input and there is no write -- A1a
       built-once, as in `HA_LookinFunctions` and `Kafka_Cluster`.  No
       write is added.
     * No index is requested.  There is no keyed read here: both reads scan
       the whole table by construction, which is what the source does.
       What this file measures is the DESUGARING, not an index.

   Expected
     The two-key order is the record order; the sorted list is the source's
     order; and -- the finding worth stating -- the table UPSTREAM of the
     sort relaxes to a bag even though the fold downstream observes order.
     A sort is a demand FIREWALL: it re-establishes the order from the
     values, so nothing above it can need a list.  That is the precise
     boundary of where list semantics is load-bearing, and it is the
     opposite of `Netbox_TemplateExtensions`, where the order is INSERTION
     order and no sort can recover it.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort [("topic", TString); ("partition", TInt)]).

Definition query_ty :=
  TRecord (record_sort [("kind", TInt)]).

(* `comparing(topic).thenComparing(partition)` *)
Definition owned_sorted : expr :=
  sort_by ["topic"; "partition"] "r" "p" (ELoc "owned").

(* the wire order, folded into one string: EFold is a fold_right, so this
   is left-to-right concatenation -- the source's order, not its reverse *)
Definition wire_string_of (src : expr) : expr :=
  EFold src (EAtom (AString "")) "w" "acc"
    (EBinop OConcatString
       (EBinop OConcatString (EAccess (EVar "w") "topic")
          (EBinop OConcatString (EAtom (AString "/"))
             (EUnop OStringOfInt (EAccess (EVar "w") "partition"))))
       (EVar "acc")).

Definition wire_string : expr := wire_string_of owned_sorted.

(* how many ConsumerProtocolSubscription.TopicPartition entries the loop
   creates: one per run of equal topics in the SORTED list, i.e. one per
   adjacent pair whose topics differ, plus one *)
Definition group_state (n prev has : expr) : expr :=
  ERecord [("n", n); ("prev", prev); ("has", has)].

Definition group_count_of (src : expr) : expr :=
  EAccess
    (EFold src
       (group_state (EAtom (AInt 0)) (EAtom (AString "")) (EAtom (ABool false)))
       "w" "acc"
       (EIf (EBinop OAnd (EAccess (EVar "acc") "has")
               (EBinop OEq (EAccess (EVar "acc") "prev") (EAccess (EVar "w") "topic")))
          (group_state (EAccess (EVar "acc") "n")
             (EAccess (EVar "w") "topic") (EAtom (ABool true)))
          (group_state (EBinop OPlus (EAccess (EVar "acc") "n") (EAtom (AInt 1)))
             (EAccess (EVar "w") "topic") (EAtom (ABool true)))))
    "n".

Definition group_count : expr := group_count_of owned_sorted.

Definition prog : command :=
  CLetMut (EVar "owned_tbl") "owned"
    (CForeach (EVar "queries") "q"
       (CIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt 0)))
          (CAssign "outputs" (EBinop OCons wire_string (ELoc "outputs")))
          (CAssign "outputs"
             (EBinop OCons (EUnop OStringOfInt group_count) (ELoc "outputs"))))).

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
    map.put (map.put map.empty "owned_tbl" (TList row_ty))
      "queries" (TList query_ty).

  Definition checks (c : command) : bool :=
    match typecheck init_Gstore init_Genv c with
    | Success _ => true
    | Failure _ => false
    end.

  (* ------------------------------------------------------------------
     PIN 1.  The side condition holds for this comparator, and the
     desugared program typechecks -- so `order by topic, partition` is a
     program the language already accepted.
     ------------------------------------------------------------------ *)
  Lemma comparator_is_expressible : names_ok ["topic"; "partition"] = true.
  Proof. vm_compute; reflexivity. Qed.

  Lemma prog_typechecks : checks prog = true.
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     PIN 2.  What the comparator means, on a table small enough to read.

     The point of the three pins together: a row's OWN canonical order is
     partition-major, because field names sort "partition" < "topic" -- so
     sorting the rows directly is the WRONG comparator, and it is wrong
     silently.  The desugaring is what makes the requested order the one
     that happens, and asking for the other order gives the other answer.
     ------------------------------------------------------------------ *)
  Definition row (t : string) (n : Z) : value :=
    VRecord (record_sort [("topic", VString t); ("partition", VInt n)]).

  (* out of order, and with a topic TIE so the second key has to matter *)
  Definition sample : list value :=
    [ row "beta" 7; row "alpha" 3; row "beta" 2; row "alpha" 1 ].

  Definition sample_store : clocals := map.put map.empty "owned" (VList sample).

  Definition run (e : expr) : value :=
    interp_expr sample_store (map.empty : clocals) e.

  Lemma sorting_the_rows_is_the_WRONG_comparator :
    run (ESort LikeList (ELoc "owned"))
    = VList [ row "alpha" 1; row "beta" 2; row "alpha" 3; row "beta" 7 ].
  Proof. vm_compute; reflexivity. Qed.

  Lemma order_by_topic_partition :
    run owned_sorted
    = VList [ row "alpha" 1; row "alpha" 3; row "beta" 2; row "beta" 7 ].
  Proof. vm_compute; reflexivity. Qed.

  Lemma order_by_partition_topic :
    run (sort_by ["partition"; "topic"] "r" "p" (ELoc "owned"))
    = VList [ row "alpha" 1; row "beta" 2; row "alpha" 3; row "beta" 7 ].
  Proof. vm_compute; reflexivity. Qed.

  (* and the order reaches the output, in both reads *)
  Lemma wire_order_is_observable :
    run wire_string = VString "alpha/1alpha/3beta/2beta/7".
  Proof. vm_compute; reflexivity. Qed.

  Lemma group_count_counts_runs : run group_count = VInt 2.
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     PIN 3.  And not only on that table: the general theorems apply at
     this comparator, because its side condition holds.  This is what
     stops the pins above from being three lucky computations.
     ------------------------------------------------------------------ *)
  Corollary owned_sorted_is_sorted_by_the_comparator :
    forall (store env : clocals) rows out,
      interp_expr store env (ELoc "owned") = VList rows ->
      Forall (fun v => exists rc, v = VRecord rc) rows ->
      interp_expr store env owned_sorted = VList out ->
      Permutation rows out /\
      StronglySorted (fun u v => is_true (lex_leb ["topic"; "partition"] u v)) out.
  Proof.
    intros store env rows out H_rows H_rec H_out.
    unfold owned_sorted in H_out. split.
    1: eapply sort_by_permutes with (attrs := ["topic"; "partition"]) (e := ELoc "owned");
       [ apply comparator_is_expressible | exact H_rows | exact H_rec | exact H_out ].
    1: eapply sort_by_sorted with (attrs := ["topic"; "partition"]) (e := ELoc "owned");
       [ apply comparator_is_expressible | exact H_rows | exact H_rec | exact H_out ].
  Qed.

  (* ------------------------------------------------------------------
     PIN 4.  THE FINDING.  A sort is a demand FIREWALL.

     The fold downstream of the sort observes the order -- it compares each
     element with its neighbour -- and yet the table UPSTREAM of the sort
     is read as a BAG: `ESort LikeList` of a list projection becomes
     `ESort LikeBag` of a BAG projection over `OBagOfList` of the table.
     That is sound for the obvious reason, and it is the precise boundary
     of where the list level of the hierarchy is load-bearing: a sort
     re-establishes the order from the VALUES, so nothing above it can
     need a list.

     Read against `Netbox_TemplateExtensions`, where the order observed is
     INSERTION order: no sort can recover that from the values, which is
     why that read needs list-valued buckets and this one needs nothing.
     ------------------------------------------------------------------ *)
  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection].

  Definition optimized : command :=
    apply_optimize_anno (AC basics [] prog) init_Gstore init_Genv.

  Fixpoint read_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ c' | CForeach _ _ c' => read_of c'
    | CIf _ c' _ => read_of c'
    | CAssign "outputs" (EBinop OCons r _) => Some r
    | _ => None
    end.

  (* the key-record projection, at BAG level *)
  Definition bag_level_keys : expr :=
    EFlatmap LikeBag (EUnop OBagOfList (ELoc "owned")) "r"
      (EBinop OBagInsert (EAtom (AEmptyBag None))
         (ERecord [("a0_topic", EAccess (EVar "r") "topic");
                   ("a1_partition", EAccess (EVar "r") "partition");
                   ("z_row", EVar "r")])).

  Definition project_back (src : expr) : expr :=
    EFlatmap LikeList src "p"
      (EBinop OCons (EAccess (EVar "p") "z_row") (EAtom (ANil None))).

  Lemma sort_is_a_demand_firewall :
    read_of optimized
    = Some (wire_string_of (project_back (ESort LikeBag bag_level_keys))).
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     And the optimized program computes what the source computes.
     ------------------------------------------------------------------ *)
  Theorem optimized_sound : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      interp_command store env optimized = interp_command store env prog.
  Proof.
    unfold optimized, apply_optimize_anno; intros.
    eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
  Qed.
End WithConcreteMaps.
