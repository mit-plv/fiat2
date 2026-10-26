Require Import fiat2.Selector fiat2.OptimizeAnno fiat2.Surface fiat2.Language.
Require fiat2.Ex_Triangle.
Require fiat2.eval.Jenkins_ItemDeletion
  fiat2.eval.Keycloak_CachedRealm fiat2.eval.Kafka_NamedCache
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
Module JID := Jenkins_ItemDeletion.

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

(* One choice, two members.  UniqueDictIdx "id" is demanded by both the
   exact-match read and the elaborated uniqueness guard, and dropped again
   because the trigram pair's second member already carries its rules.

   This is the file's FIRST configuration, and it is the one to want.  Its
   second asks for the table's set representation as well, which erases the
   list by giving the trigram rule's short-token fallback something other
   than the list to scan.  The selector does not reach it, for two reasons
   that are worth keeping apart:

     - It could not be asked for by a shape.  The read that configuration
       serves is the else branch of a guarded probe, which the rewriting
       creates by keeping its own input, so it is not in the program.
     - It should not be asked for at all.  Measured in that file at
       rep_delete_filters_the_rep and rep_insert_is_a_set_insert: the
       erasure moves the delete's O(n) filter from the list to the rep
       member rather than removing it, and degrades the insert from a cons
       to a set insert.

   A feedback step -- run the pipeline, find the surviving read, add
   TableRep and run again -- closes the first gap and does reach that
   configuration.  It was built and removed, because the second reason
   makes reaching it the wrong goal.  See the note at the end of
   Selector.v. *)
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

(* ---------- the join ----------

   The first JOIN the selector handles.  Every other subject in this file has
   one loop over the table; a join has several, and its conditions are a chain
   of nil-guards at the innermost body, each belonging to the innermost loop
   that binds its variables.  A condition written above the useful one does
   not mention the inner loop's variable, so what the index rules read is
   constant in that loop.

   `swap_flatmap_if_head` is the rewrite for it and was always directed -- it
   fires only on a guard that does not mention the loop variable, and firing
   removes the guard, so it cannot undo itself.  What was missing is that
   `basics_of` never emitted it.  The DHoist demand, whose detection is the
   rule's own guard, is what emits it, and with it the selector reaches this
   three-way self-join with no hand-written chain: Ex_Triangle's four
   configurations each list a sequence of SwapIfNil and SwapFlatmapIf found by
   hand, and this list is uniform.

   What that is worth is counted in Ex_Triangle itself
   (`selector_matches_the_best_single_index_chain`, and
   `without_the_hoist_it_reaches_two` for what this demand changed). *)
Lemma ex_triangle_basics :
  select_basics [] "edges" Ex_Triangle.prog
  = [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap; SwapFlatmapIf].
Proof. vm_compute; reflexivity. Qed.

Lemma ex_triangle :
  select_choices [] "edges" Ex_Triangle.prog = [DictIdx "src"].
Proof. vm_compute; reflexivity. Qed.

(* The file's configuration 0, the one with SplitIf: both conjunctive reads
   become a probe followed by a filter, where configuration 1 leaves them
   scanning.  The selector asks for the split because a conjunction's first
   conjunct is an equality here and no conjunction is a range pair. *)
Lemma kafka_cluster :
  unconstrained "partitions" Kafka_Cluster.prog
  = nth_heu Kafka_Cluster.heuristics 0 Kafka_Cluster.prog.
Proof. vm_compute; reflexivity. Qed.

(* The file's configuration 1, the one WITH SplitIf -- and the selector
   reaches it for a reason that has nothing to do with this program.  Its
   fetch predicate is (range && key), which no rule matches as it stands,
   while the conjunct the splitter peels -- the range -- is matched by the
   ranged dictionary.  So splitting turns a full scan into a probe, which
   is the whole of the condition.

   fetchAll's predicate is a bare two-sided range, which range_bounds
   already matches whole, so it contributes no reason to split; it is
   split anyway, because SplitIf is a whole-program rewrite, and it loses
   one of its two bounds.  That is the cost, and the file measures it
   (fetch_all_loses_a_bound_split) alongside the three gains that come
   with it: fetch becomes a probe, the list is erased, and retention
   reduces to the member's own incremental restriction
   (split_erases_the_list, split_expiry_is_only_the_restriction).

   An earlier version of the selector declined here, on a veto that read a
   range conjunct as purely a cost.  That was a category error -- a range
   conjunct is exactly as indexable as an equality -- and the veto fired
   on no subject anyway. *)
Lemma kafka_window_store :
  unconstrained "segments" Kafka_WindowStore.prog
  = nth_heu Kafka_WindowStore.heuristics 1 Kafka_WindowStore.prog.
Proof. vm_compute; reflexivity. Qed.

(* Nothing is declared here, which is why FilterEmptyToSetMem is safe to
   run: there is no uniqueness guard for it to break.  The selector is given
   the empty cenv, which is the whole of what this subject tells it. *)
Lemma ha_lookin_functions :
  unconstrained "functions" LF.elaborated = LF.anno.
Proof. vm_compute; reflexivity. Qed.

(* TableRep, demanded.  This is the one subject whose read names no
   attribute -- registrations.contains(item) asks about a whole row -- so
   whole_collection_binop fires and nothing else can.  The two pins together
   are the claim that the condition is not an overfit: this subject gets
   TableRep and the one ABOVE does not, although Lookin's source also hands
   a bare coercion of its table to a membership test.  What separates them
   is that Lookin's membership test is reached through an EAccess, so
   FilterEmptyToSetMem and SetAgg claim it first and the coercion the
   selector sees is of an ATTRIBUTE's values, not of the table. *)
Lemma jenkins_item_deletion :
  select_choices [] "registrations" JID.elaborated = [TableRep LikeSet].
Proof. vm_compute; reflexivity. Qed.

Lemma jenkins_item_deletion_anno :
  unconstrained "registrations" JID.elaborated = JID.anno_rep.
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
