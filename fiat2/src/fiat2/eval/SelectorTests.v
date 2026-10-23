Require Import fiat2.Selector fiat2.OptimizeAnno fiat2.Surface fiat2.Language.
Require fiat2.eval.Keycloak_CachedRealm fiat2.eval.Kafka_NamedCache
  fiat2.eval.Kafka_Cluster fiat2.eval.Kafka_WindowStore
  fiat2.eval.HA_AreaRegistry fiat2.eval.HA_LookinFunctions
  fiat2.eval.Jenkins_UserSearch
  fiat2.Ex_RangeDelete fiat2.Ex_Inventory fiat2.Ex_Sum fiat2.Ex_SumDelete
  fiat2.Ex_MinDelete fiat2.Ex_Range fiat2.Ex_FlagFilter fiat2.Ex_Orders
  fiat2.Ex_Employee.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Local Open Scope string.

(* ============================================================
   What the selector picks, against what each example asks for.

   Selector.v mentions no table, no attribute and no example; this file is
   where the two meet, and the dependency runs one way only -- the selector
   does not Require anything here, and nothing here is Required by it.
   Every lemma below is an equality of closed terms, so the compiler checks
   the whole truth table.

   The first group is the strongest form of the claim available: the
   selector's output is compared to the example's OWN annotation, the term
   the file already optimizes with, so a passing lemma means the example
   could be rewritten to call the selector and nothing would change.

   Where an example pins two configurations, the lemma names which one the
   selector reaches, and whether that is the better one is stated beside it
   -- that is the interesting content, since a configuration the selector
   could not reach would be a hole in the story.
   ============================================================ *)

Module KC := Keycloak_CachedRealm.
Module NC := Kafka_NamedCache.
Module AR := HA_AreaRegistry.
Module LF := HA_LookinFunctions.
Module JU := Jenkins_UserSearch.

(* ---------- the constrained subjects: the annotation itself ---------- *)

(* Both declared keys, and the maintained row count.  This is the file's
   SECOND configuration, which is the better of the two: with the count,
   the list's one remaining reader becomes a field read and the list is
   erased. *)
Lemma keycloak_cached_realm :
  select_anno (("actions", (KC.row_ty, KC.decls)) :: cenv_rm "actions" []) "actions" O
    (KC.elaborated KC.decls)
  = KC.anno_counted.
Proof. vm_compute; reflexivity. Qed.

(* The declared key and the maintained sum, the dictionary listed BEFORE
   the aggregate.  The file's second configuration is the same pair listed
   the other way round, which it measures as a pessimization; the selector
   reaches the good order by construction, since the order of its output is
   the ordering spec. *)
Lemma kafka_named_cache :
  select_anno (("cache", (NC.row_ty, NC.decls)) :: cenv_rm "cache" []) "cache" O
    (NC.elaborated NC.decls)
  = NC.anno.
Proof. vm_compute; reflexivity. Qed.

(* The keyed pair: a dictionary bucketed on floor, paired with the declared
   key so the delete is a probe and not a rebuild. *)
Lemma ha_area_registry :
  select_anno (("areas", (AR.row_ty, AR.decls)) :: cenv_rm "areas" []) "areas" O
    (AR.elaborated AR.decls)
  = AR.anno.
Proof. vm_compute; reflexivity. Qed.

(* Nothing is declared here, which is why FilterEmptyToSetMem is safe to
   run: there is no uniqueness guard for it to break. *)
Lemma ha_lookin_functions :
  select_anno (("functions", (LF.row_ty, LF.decls)) :: cenv_rm "functions" []) "functions" O
    (LF.elaborated LF.decls)
  = LF.anno.
Proof. vm_compute; reflexivity. Qed.

(* One choice, two members.  UniqueDictIdx "id" is demanded by both the
   exact-match read and the elaborated uniqueness guard, and dropped again
   because the trigram pair's second member already carries its rules.

   This is the file's FIRST configuration.  Its second asks for the table's
   set representation as well, which erases the list by giving the trigram
   rule's short-token fallback something other than the list to scan; the
   selector does not reach it, and cannot, because the read that
   configuration serves does not exist until the trigram rule has run.  See
   the note at the end of Selector.v. *)
Lemma jenkins_user_search :
  select_anno (("users", (JU.row_ty, JU.decls)) :: cenv_rm "users" []) "users" O
    (JU.elaborated JU.decls)
  = JU.anno.
Proof. vm_compute; reflexivity. Qed.

(* ---------- the unconstrained subjects ---------- *)

Definition unconstrained (tbl : string) (c : command) : anno_command :=
  AC (select_basics [] tbl c) [select_choices [] tbl c] c.

Definition nth_heu (l : list (command -> anno_command)) (n : nat) (c : command) :=
  nth n l (fun c => AC [] [] c) c.

(* The file's configuration 0, the one with SplitIf: both conjunctive reads
   become a probe followed by a filter, where configuration 1 leaves them
   scanning.  The selector asks for the split because a conjunction's first
   conjunct is an equality here and no conjunction is a range pair. *)
Lemma kafka_cluster :
  unconstrained "partitions" Kafka_Cluster.prog
  = nth_heu Kafka_Cluster.heuristics 0 Kafka_Cluster.prog.
Proof. vm_compute; reflexivity. Qed.

(* The file's configuration 0, the one WITHOUT SplitIf -- and the one place
   in the suite where the selector has to choose between two readers it
   cannot both serve.  Splitting would make fetch(key, lo, hi) a probe and
   cost fetchAll(lo, hi) one of its two bounds; declining keeps the range
   pair whole and leaves fetch scanning.  The selector declines, because a
   conjunction here IS a range pair.  Both configurations are pinned in the
   file; which is preferable is a property of the workload, and the fix is
   a splitter that leaves a range pair alone. *)
Lemma kafka_window_store :
  unconstrained "segments" Kafka_WindowStore.prog
  = nth_heu Kafka_WindowStore.heuristics 0 Kafka_WindowStore.prog.
Proof. vm_compute; reflexivity. Qed.

(* The ranged dictionary, demanded by the read and by both range-shaped
   writes. *)
Lemma ex_range_delete :
  unconstrained "orders" Ex_RangeDelete.prog
  = nth_heu Ex_RangeDelete.heuristics 0 Ex_RangeDelete.prog.
Proof. vm_compute; reflexivity. Qed.

(* ---------- the rule-demonstration examples ---------- *)

(* These are not evaluation subjects; each exists to exercise one rule.
   They are tested at the CHOICE level, because several of them write a
   basic list that omits IfNilIntoFlatmap, which the selector always emits.
   Emitting it is not pinned to be harmless on those programs -- it is the
   identity wherever no if-nil sits under a flatmap, and nothing here
   checks that it is. *)

Lemma ex_inventory : select_choices [] "inventory" Ex_Inventory.prog = [DictIdx "id"].
Proof. vm_compute; reflexivity. Qed.

Lemma ex_sum : select_choices [] "orders" Ex_Sum.prog = [SumAgg "value"].
Proof. vm_compute; reflexivity. Qed.

(* configuration 0: the dictionary on the delete's attribute is what turns
   the sum's correction term into a read of one bucket *)
Lemma ex_sum_delete :
  select_choices [] "orders" Ex_SumDelete.prog = [DictIdx "cust"; SumAgg "price"].
Proof. vm_compute; reflexivity. Qed.

(* configuration 0: the delete is on the attribute the minimum is cached
   on, and there the correction reads the SET of that attribute's values
   rather than a bucket, so the selector asks for a set index and not a
   dictionary *)
Lemma ex_min_delete :
  select_choices [] "orders" Ex_MinDelete.prog = [SetAgg "price"; MinAgg "price"].
Proof. vm_compute; reflexivity. Qed.

(* configuration 0: Ranged, which is the kind the range rule's typing pins.
   Configuration 1 asks for the same dictionary Unranged and measures that
   the range query is left alone; the selector never asks for that, since
   it asks for a ranged dictionary exactly where a range is read. *)
Lemma ex_range : select_choices [] "orders" Ex_Range.prog = [RangedDictIdx "price"].
Proof. vm_compute; reflexivity. Qed.

(* configuration 0: without FlagFilterToEq no index rule matches a filter
   on a boolean attribute, which is what configuration 1 measures *)
Lemma ex_flag_filter :
  select_basics [] "users" Ex_FlagFilter.prog
  = [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap; FlagFilterToEq].
Proof. vm_compute; reflexivity. Qed.
Lemma ex_flag_filter_choices :
  select_choices [] "users" Ex_FlagFilter.prog = [DictIdx "is_active"].
Proof. vm_compute; reflexivity. Qed.

(* two tables, one choice list each, which is how a multi-table program is
   selected: one call per table *)
Lemma ex_orders_inventory :
  select_choices [] "inventory" Ex_Orders.prog = [DictIdx "id"].
Proof. vm_compute; reflexivity. Qed.
Lemma ex_orders_orders :
  select_choices [] "orders" Ex_Orders.prog = [SumAgg "price"; MinAgg "price"].
Proof. vm_compute; reflexivity. Qed.

Lemma ex_employee :
  select_choices [] "employees" Ex_Employee.prog = [DictIdx "dept_id"].
Proof. vm_compute; reflexivity. Qed.

(* ---------- out of scope, and why ----------

   Ex_Triangle, Ex_BFS and Ex_Family are joins: a flatmap over one read
   nested inside a flatmap over another.  Their basic lists are not the
   selector's three plus a decision but a sequence of flatmap shuffles --
   SwapFlatmapIf, SwapIfNil, repeated IfNilIntoFlatmap -- chosen to bring
   the inner read into the shape an index rule matches, and the sequence
   differs per example.  Choosing those is a different problem from
   choosing an index, and the selector does not attempt it.  Every
   evaluation subject is join-free, so nothing in the performance claim
   depends on it.
   ---------------------------------------------------------- *)
