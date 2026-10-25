# Evaluation examples

Programs drawn from real code bases, written in Conquord, used as the subjects of the
paper's evaluation.

These are **not** the development's test files. The `Ex_*.v` files one directory up
exercise individual rewrite rules and are regression tests; citing them as evidence of
pattern coverage would be circular, since they were written to make the rules fire.
Files here are translations of code someone else wrote for their own reasons.

The build needs no configuration for this directory: `fiat2/Makefile` collects sources
with a recursive `find`, and `-Q src/fiat2 fiat2` is recursive, so a file here is
`fiat2.eval.<Name>` and compiles with the rest.

## File convention

Every file opens with a header comment giving, in this order:

1. **Source** — repository, path, and the commit the reading is from, so the
   translation can be checked against the original.
2. **Pattern** — the pattern IDs from the separate pattern study that the original
   instantiates. These say why the example was chosen; the study's counts are a
   discovery aid and never appear in the paper.
3. **Claim** — which evaluation claim the example evidences (see the evaluation log).
4. **Faithfulness** — what was dropped in translation and why, stated plainly. The
   original is Java or Python; an honest note here is what makes the example usable.
5. **Expected** — what the optimizer should produce, in words.

The expectation in (5) is then pinned by a lemma, in the style of `Ex_Range.v`: a small
projection out of the optimized program closed by `vm_compute; reflexivity`, rather than
an `exists` against the whole term, which does not terminate in reasonable time.

## Row order, and the one way to add a row

Five of these files write a row into the table, and all five do it by **prepending**:
`EBinop OCons row (ELoc tbl)`. Their sources do not prepend. Four of them put into a map
(Keycloak's two `HashMap`s, `NamedCache`'s and `WindowStore`'s `NavigableMap`, Home
Assistant's registry dict), so the source names no position in a sequence of rows at all;
Jenkins appends, and its header quotes the `result.add` that does it. The remaining two
files have no table write -- `Cluster` is immutable, and the Lookin functions program only
reads -- so the question does not arise there.

The substitution is sound here, and for a reason that is checkable rather than assumed:
**no read in any of these files observes row order.** There is no `ESort` anywhere in this
directory, and every read is a count, a probe, a filter or an aggregate -- all invariant
under permutation of the rows. A prepend and an append differ as lists and agree as bags,
so where nothing observes more than the bag they are the same write. Each affected file
now says this in its Faithfulness section.

Worth separating from that: appending **is** expressible. `OConcat : TList t -> TList t ->
TList t` exists, with typing, semantics and a backend case, so an append at the end is
`OConcat (ELoc tbl) (OCons row nil)`, and a fold expresses an insert at a position. What is
missing is not the operator but the rule -- see the limits table below.

## The files

| file | source | what it is for |
|---|---|---|
| `Keycloak_CachedRealm.v` | `CachedRealm.java:301` | two unique-key maps over one list; the list is read, so the list survives -- and, in a second configuration, a maintained row count makes that last read a field read and the list is erased |
| `Kafka_Cluster.v` | `Cluster.java:114` | two bucketed maps over one collection; nothing reads the list, so the list is erased |
| `HA_AreaRegistry.v` | `area_registry.py:169` | a primary key dict and a secondary index, maintained across an insert and a delete; nothing reads the list, so the list is erased |
| `HA_LookinFunctions.v` | `lookin/entity.py:94` | a set derived from a list because no query observes order or multiplicity; both reads are membership probes, and the list is erased |
| `Kafka_NamedCache.v` | `NamedCache.java:44,49` | a keyed store and a running total over it, both maintained across a delete and a put; the total is corrected by a probe, never recomputed |
| `Kafka_WindowStore.v` | `InMemoryWindowStore.java:78` | the only ORDERED index: a time range answered out of a sorted dictionary, maintained incrementally across both a put and a range-shaped retention delete -- and two limits, a conjunctive range reader and a list that survives its own filter |
| `Jenkins_ItemDeletion.v` | `ItemDeletion.java:74,129,149,165` | the only WHOLE-ROW read: a `Set<Item>` asked `contains(item)`, so the question is about a row and not an attribute, no dictionary can be keyed for it, and `TableRep` is the only index that applies |
| `Jenkins_UserSearch.v` | `CollectionSearchIndex.java:54`, `Jenkins.java:2437` | the only SUBSTRING index, and the only file whose claim is that the author did NOT build the structure: `find` is their own `ConcurrentHashMap` lookup, `suggest` their own linear `contains` scan, one class and one collection; both writes maintain both members, and the declared key erases the list |

The eight fall into five groups, and the groups are the argument.

**What the reads ask for** -- `Keycloak_CachedRealm`, `Kafka_Cluster`,
`HA_LookinFunctions`. The first two are a pair and should be read as one: they put
the same erasure rule in front of two code bases and get opposite answers -- keep the
list, drop the list -- and each answer is the storage the original's author chose by
hand. Keycloak keeps `requiredActionProviderList` beside both maps; `Cluster` has a
field for every map it derives and no field for `partitions`.

`HA_LookinFunctions` is the only one whose rewrite is licensed by the **collection
interpretation** rather than by a declared constraint -- its `decls` is empty. The
programmer wrote a `set`, not a list and not a map, because neither order nor
multiplicity of the names is ever observed; the optimizer reaches the same structure
from the queries alone, and erases the list because after the rewrite nothing reads it.
Read it against `Keycloak_CachedRealm`: same erasure rule, same built-once shape,
opposite answer about the list, and the reason is what the queries ask.

So those three cover both directions in which one category's conclusion licenses
another's rewrite: a declared uniqueness making a single-row lookup sound
(`Keycloak_CachedRealm`), and an inferred interpretation making a membership probe
available (`HA_LookinFunctions`).

**What the writes cost** -- `HA_AreaRegistry`, `Kafka_NamedCache`. These are the two
whose writes are their own; the other four build once.

`HA_AreaRegistry` maintains a secondary index. `delete_is_incremental` pins a delete
that probes the primary member for the leaving row and rewrites only the one bucket
that row's attribute names, which is `_unindex_entry` line for line. It needs
`KeyedDictIdx`, and it is gated on the key being declared.

`Kafka_NamedCache` maintains an **aggregate**, in both directions: a delete subtracts
the leaving row's size, found by a probe, and a put subtracts the old row's and adds
the new one's. That is `currentSizeBytes` at `NamedCache.java:178`, `:192`, `:249` and
`:281`, and `sizeInBytes()` comes out as the field read it is in the source. It is
also the first file where two index choices interact, and the interaction is measured:
listing the aggregate before the dictionary leaves the correction term a scan, which
keeps the list alive. Sound either way, asymptotically worse one way -- see
`swapped_correction_scans`.

Read with `HA_AreaRegistry`: before the keyed delete existed, that file kept its list
-- not because a query read it, but because the rebuild did. The representation gap
and the maintenance gap were one gap, and closing the second closed the first with no
change to the erasure rule. `Kafka_WindowStore` is in that earlier position with one
difference: its member is now maintained incrementally, and what keeps its list alive
is the list's own row-by-row filter rather than the member's rebuild.

**What the order asks for** -- `Kafka_WindowStore`. The only file whose index is
`Ranged`, and so the only one that obliges a backend to provide a structure that can
answer a key range; every other member in these files may be a hash table. Kafka made
the same choice by hand -- `segmentMap` is a `ConcurrentSkipListMap` -- and for the same
reason: every read of it is a time range and the retention policy deletes a time range.

It is also the file that measures the most. Two configurations, and the second now serves
both of the source's range readers: without `SplitIf` the flat range is a probe and the
conjunctive one is a scan; with `SplitIf` the conjunctive one becomes a probe refined by a
key test and the flat one is **unchanged**, because `is_two_sided_range` stops the
splitter cutting a range pair in half. It did not use to be, and what that cost is a
real cost and a much smaller one than it was before the bounds became optional, when
the same split produced two chained table scans.

And `removeExpiredSegments` is a range-shaped delete, which the member now absorbs in
one operation: its retention predicate is a one-sided bound, so keeping the rows it
keeps is restricting the member to `[lo, inf)`, and that is what the write emits
(`expiry_restricts_the_member`). What the restriction costs is the backend's affair --
splitting a persistent tree is logarithmic, walking the survivors is not -- and this
development fixes the shape, not the constant.

Whether the list survives turns out to depend on the configuration, which is why this
file now pins both. Without `SplitIf` it does, because the table's own field is assigned
a row-by-row filter over itself and nothing recovers the rows from the member
(`the_list_filter_keeps_the_list`). **With `SplitIf` it does not**: the keyed read stops
scanning the list, and with the list's last reader gone the field is erased and retention
is nothing but the member's own restriction (`split_erases_the_list`,
`split_expiry_is_only_the_restriction`). The deterministic selector takes the split.

**What the author did NOT build** -- `Jenkins_UserSearch`. Every file above compares a
derived structure with a hand-built one. This file is the exception, and it is the
exception on purpose: `hudson.search.CollectionSearchIndex` gives one collection two
lookups in one class, and the author built a `ConcurrentHashMap` for the exact one and
left the substring one a linear `contains` scan. So the two halves of the same file make
the two different claims -- `find_is_a_probe` reproduces the map they wrote (C4), and
`suggest_is_a_guarded_trigram_probe` replaces the scan they wrote (C3) -- out of one
source program and one index choice.

It is also the only file where a read is GUARDED rather than rewritten outright. The
search token comes from the request, so its length is not a rewrite-time fact, and a
pattern shorter than three characters has no trigram at all; the rule emits the test and
keeps the source query as the other branch.

That branch used to be why the list survived. It no longer is. The key is declared, so
the primary-key dictionary holds every row exactly once, and a scan of its values answers
the same query as a scan of the list -- which is what `unique_scan_head` does
(`UniqueIndexUse.v`), gated on the declaration exactly as the point lookup is and resting
on the same fact about the same member (`idx_entries_values_Permutation`). With the
fallback served from the member the list has no reader left at all, so the field is erased
and both writes collapse to two member updates each
(`the_declared_key_erases_the_list`, `delete_writes_no_list`, `insert_writes_no_list`).
What the table stores is then the author's own `byName` map plus the postings this file
exists to add.

The fallback is still a scan, and should be: a substring match has to look at every row.
What it costs over the source's scan is one extra linear pass, `ODictValues` producing the
member's values before the filter runs -- measured at 32,180 steps for 20 queries over
1600 rows, which is exactly one pass per query, and 14% on top of the source. Its
comparison count stays flat.

The delete is the part to read twice. The write names a key, not a row, so the postings
cannot be corrected without knowing which text the departing row carried -- and the pair
supplies it: the key member is probed for the row, and that row's id comes out of the
bucket of each trigram of its own text, with a bucket dropped when it empties. One
choice, two members, and the second exists so the first can be maintained.

**What no key can answer** -- `Jenkins_ItemDeletion`. Every read above names an
attribute, which is what lets a dictionary be keyed for it. This one does not: the
source stores whole rows in a `Set<Item>` and asks `contains(item)`, so there is no key
to probe with and the only index in the development that applies is the one that
represents the table itself. It is the file that makes `TableRep` a measurement rather
than a listing, and it is argued where the numbers are, under *What it costs* below.

## Who chooses the heuristics

Every file here names its own heuristics beside its program: a list of basic rewrites
and a list of index choices. That is enough for a soundness claim, since the optimizer
is sound for any choice list, and not enough for a performance one, where "with
appropriate heuristics" has to mean something a program computes rather than something
a person chose after seeing the answer.

`src/fiat2/Selector.v` computes them, and `SelectorTests.v` in this directory is where
the two meet. The selector mentions no table name, no attribute name and no example;
the dependency runs one way, and the test file is the only place the two are compared.

For the five files here that use the constrained pipeline the test is the strongest
form available -- `select_anno … = <that file's own anno>` -- so a passing lemma means
the file could call the selector instead of naming its heuristics and nothing would
change, and that file's existing output pins carry over unaltered. For the three that
use the unconstrained one the test compares against the file's own `heuristics` list by
index. Where a file pins two configurations, the test names which one the selector
reaches and whether it is the better one; it is, in every case where the two differ in
quality.

One row is worth reading for what it says about the rules rather than about the selector.
`SplitIf` is emitted from a single condition: some conjunctive filter over the table is
matched by **no** rule as it stands, while the conjunct the splitter peels **is** matched.
Splitting then turns a full scan into a probe with a residual filter, and that is the only
thing it is asked to do.

There is no veto, and the case a veto would cover falls out of the same condition. A
two-sided range is itself a conjunction and `range_bounds` matches it whole, so it is
already served; splitting it would cost it a bound and expose nothing new, so the
condition does not fire on it. That is why `Ex_RangeDelete`, whose only conjunction is a
bare range pair, is left alone, while `Kafka_Cluster` (two equalities) and
`Kafka_WindowStore` (a range conjoined with a key test) are both split.

WindowStore is where the cost used to show. Its `fetchAll` reads a bare range pair,
contributes no reason to split, and was split anyway, because `SplitIf` is a
whole-program rewrite -- so it lost one of its two bounds. The selector's condition
already declined to *ask* for the split on such a read, which was not enough: one reader
of the table asked for it and the rewrite then reached the other.

**That is now fixed in the rule rather than worked around.**
`FlatmapTransf.is_two_sided_range` makes `SplitIf` leave a conjunction alone when the
conjunction *is* a two-sided range on one attribute -- the shape `range_bounds` matches
whole -- because splitting it can expose nothing and can only cost a bound.
`fetch_all_keeps_both_bounds_split` pins the result: the same term as the unsplit
configuration, both bounds named, no residual filter. So configuration 1 is better on all
four measured operations and configuration 0 is dominated; it stays only because
`fetch_key_scans_unsplit` is the evidence that the split is needed at all.

The other is `TableRep`, which the selector emits for exactly one kind of read. Two kinds
have to be told apart. A read the **rewriting leaves behind** -- the else branch of a
guarded probe, which `trigram_lookup_guarded_head` creates by keeping its own input -- is
nowhere in the source, so no matcher can ask for it; a feedback step that runs the
pipeline, finds the surviving read, adds `TableRep` and runs again does reach that
configuration, and it was built and then removed, because the goal turned out to be the
wrong one. A read the **programmer wrote** is an ordinary shape, and that is the one the
selector now demands (`whole_collection_binop`): an operator that takes the collection
whole and names no attribute, so no dictionary or aggregate can be keyed for it.

In `Jenkins_UserSearch` that case is now closed from the other end. The declared key
serves the fallback, so the read `TableRep` was added for is gone before it can be found,
and the list is erased without it. Both configurations are still pinned, and the pair is
now one-sided rather than a wash: the first writes nothing to a list because there is no
list, while the second still pays the source's own O(n) filter on the delete and degrades
the insert from a cons to a set insert (`rep_delete_filters_the_rep`,
`rep_insert_is_a_set_insert`) -- and its rep member, measurably, is read by nothing while
both writes keep maintaining it.

**But that is the dominated case, not the whole story**, and `Jenkins_ItemDeletion` is the
other half. Its read is a **whole-row** membership test -- `registrations.contains(item)`
in the source, where `registrations` is a `Set<Item>` and there is no key, because the
question is about a row and not about an attribute. No dictionary can serve it, so
`TableRep` is the only index in the development that applies, and the unindexed form
coerces the whole table on every evaluation. Comparisons for twenty reads:

| kind | 50 rows | 1600 rows | across 32x |
|---|---|---|---|
| `containsHit` without | 10,872 | 764,164 | 70.3x |
| `containsHit` with | 232 | **444** | 1.9x |
| `register` without (a cons) | 40 | 40 | 1.0x |
| `register` with (a set insert) | 340 | 578 | 1.7x |
| `deregister` without (filter a list) | 1,680 | 63,680 | 37.9x |
| `deregister` with (a tree deletion) | 268 | **532** | 2.0x |

Every read and every write is flat: the exponents are 0.18, 0.21, 0.15 and 0.20 against
the source's 1.22, 1.22, 0.00 and 1.04, and the op phase as a whole falls from 289,220
steps and 1,592,358 comparisons to 1,200 and 2,126. The one column `TableRep` loses is the
insert, by 538 comparisons on an operation whose cost does not grow. The read's step counts
are equal in both columns and that is the correct reading, not a blind spot: `count.ml`
puts a tree operation's cost in comparisons.

**The delete did not start out flat, and the history is the result.** Measured first, it
cost 744,280 comparisons -- 11.7x *worse* than the source's list filter, and
asymptotically worse, because the semantics of a set-level filter rebuilds the member and
every surviving row pays a logarithmic insert. So `TableRep` was a trade: a large win on
the read, a log factor given back on the write. `SetRemoveTransf.v` rules that out by
recognising the filter for what it is -- one row leaving a set, `OSetDiff` against the
singleton -- and the column drops by a factor of 1399. The rule is stated for any set and
mentions no index; this subject is only where its absence showed.

What decides between the two subjects is therefore whether a **dictionary is available**
for the read that keeps the list alive. Where one is, `TableRep` is a copy and is
dominated. Where the read is whole-row, nothing else can serve it.

So the erasures that are wins are the ones where every read is answered by an index and
**nothing replaces the list** -- `Kafka_Cluster`, `HA_AreaRegistry`, `Kafka_NamedCache`,
`Keycloak_CachedRealm` with its count, and now `Jenkins_UserSearch` with its declared
key. That is every subject: all eight install `aux_tag` alone.

`TableRep` erases by substitution, so what it establishes is a **representation** fact
rather than a cost one, and that is the right way to read it. The collection phase has
already decided, per read, the weakest level a read's consumers observe -- a table read
that comes out under a bag or set coercion is exactly the statement that nothing
downstream observes more. `TableRep` lets that conclusion be realised in storage instead
of only in the plan: the member it installs has type `TBag t` or `TSet t`, the program is
well typed holding it, and it computes what the scan form computes. Both conjuncts are in
the configuration's soundness theorem, so *a set suffices here* is checked rather than
asserted; and once the list field is erased, no stored copy of the rows is finer than the
level the program needs. It is the same move the dictionary kinds make -- a representation
obligation pushed into the type, where a backend can read it.

The claim is about information and not about structures, which is worth protecting in both
directions: a set in the semantics is a canonical duplicate-free sorted list, which a
backend need not build, and a list-typed table may still be hash-backed, since nothing in
the language observes arbitrary order.

And it is a claim about what remains stored, not that one relaxed collection replaces
everything. `TableRep` at set level **alone** would not have erased
`Jenkins_UserSearch`'s list: `find` is a counted bag-level filter, so multiplicity is
observed and the rep rule, which matches only a set coercion, leaves that read scanning
the list. At bag level alone the list would have survived too, because the suggestion read
is at set level. Either way the erasure needed the trigram pair to take `find` first --
which is the reading to keep, because it is about what a relaxed collection can and
cannot stand in for. What actually erases the list in that file is a different mechanism
entirely: not a weaker collection standing in for the rows, but a declared key making an
index a faithful copy of them.

## What it costs, measured

The claims above are about what the optimizer *produces*. What it *buys* is measured by
running the produced programs, which happens outside this directory: `Extract.v` hands
the terms to OCaml and the harness beside them evaluates them over generated workloads.
How the evaluator is built, and what it assumes, is documented where it lives; the two
things worth repeating here are that the evaluator is checked against the Gallina
interpreter on all sixteen programs over 240 configurations, and that every run compares
the source program's final store against the optimized one's, so each measurement is
also a concrete witness of that subject's soundness theorem on that input.

The workload grows the table to n rows and then issues a fixed number of queries of each
kind the subject dispatches on. What is counted is interpreter work -- entries into
`interp_expr` plus one per element any primitive linear in its argument walks -- and
value comparisons, which is where the cost of a dictionary, bag or set operation sits.
Both are machine-independent; neither is a count of AST nodes, and the program sizes
reported elsewhere play no part here. Wall-clock seconds are printed alongside, but only
as a check that the counters have the right shape: they time a tree-walking interpreter
over an extracted AST, so their constants say nothing about a backend.

Each op kind is measured at six sizes -- 50, 100, 200, 400, 800, 1600 -- and what is
reported is the exponent `a` in `cost ~ rows^a`, fitted by least squares on the logs. A
ratio between two sizes would not settle the question it looks like it settles: over an
8x range, `n` grows 8.0x and `n log n` grows 9.4x.

Thirty-one reads and writes across the eight subjects, by the exponent of their STEP
count:

| | source | optimized |
|---|---|---|
| linear in the table, `a` = 0.92 to 1.05 | 26 of 31 | 2 of 31 |
| independent of it, `a` = -0.01 to 0.02 | 5 of 31 | 28 of 31 |
| sublinear, `a` = 0.19 | 0 of 31 | 1 of 31 |

Five in the source column do not grow in steps, and they are two different things.
Three are genuinely O(1) writes -- `window_store/put`, `range_delete/insert` and
`item_deletion/register` -- because a prepend is a prepend whether or not anything is
indexed. The other two are `Jenkins_ItemDeletion`'s two membership reads, which are one
`OSetMem` step over a collection the step counter does not walk and whose cost is
therefore entirely in COMPARISONS, at `a` = 1.22. That is not a blind spot in the
instrument but where `count.ml` puts a tree operation's cost, and it is why the table
below that subject reports comparisons.

The twenty-eight in the optimized column are not merely flatter, they are flat: the
Lookin membership test, to take one, costs **exactly 300 steps at every one of the six
sizes**. Their comparison counts are where the index shows through, at `a` = 0.08 to
0.31, which is `log n` appearing as the weak power law it is -- the same subject's
comparison count goes 114, 134, 157, 177, 191, 211, gaining about twenty per doubling
across twenty queries. Two of the twenty-eight do no comparisons at all (`a` = 0.00):
`getRequiredActionProviderList`'s count and `sizeInBytes`, which are maintained
aggregates and so are field reads, cheaper than a probe.

**The three that still grow are the interesting column, and every one of them is a correct
answer rather than a cost.** Their exponents are 0.98, 0.98 and 0.19.
* `Jenkins_UserSearch`'s `suggestMiss` and `suggestShort`, `a` = 0.98 each. These are the
  guarded fallback, reached by a token with no trigram and by one shorter than three
  characters, and they are linear because a substring match **has** to look at every row.
  What the optimizer changes is not the exponent but what gets scanned: the rows now come
  from the primary-key member rather than from a list field, which is what lets the field
  be erased. The price is one extra linear pass per query -- `ODictValues` producing the
  member's values -- measured at 32,180 steps for 20 queries over 1600 rows, exactly one
  pass each, or 14% on top of the source's own scan. The comparison counts stay flat.
* `Jenkins_UserSearch`'s `suggest`, `a` = 0.19 -- sublinear, and it is the answer growing
  rather than the search: a three-character token matches more of a larger table.

Two entries have left this list, and both left the same way -- a rule named in the note
that described them.

`Jenkins_UserSearch`'s `remove` used to be here at `a` = 0.94, with the note that "a rule
recovering rows from `ODictValues` would erase it and this number with it". That rule is
`UniqueIndexUse.unique_scan_head`, and it did: `remove` is now `a` = 0.01, 318,320 steps
against 4,500 at 1600 rows, and the list it filtered is gone. The build phase went with
it, from 8,983,202 steps to 270,409.

`Kafka_WindowStore`'s `fetchAll` used to be here at `a` = 0.94 -- the one entry that was a
**cost** rather than a correct answer, with the note that a better rule would remove it.
That rule is `FlatmapTransf.is_two_sided_range`, a guard declining to split a conjunction
that is already a two-sided range, and it did: `fetchAll` is now `a` = 0.01, 448,700 steps
against 900 at 1600 rows. **So every measured read and write in the optimized column is
now flat except the two substring fallbacks, which have to be linear.**

The seconds agree where they can be read at all, and over the full 32x span they are
read more easily: the source op phases that resolve grow about 30x, against a counted
exponent of 1. In the optimized column only the exceptions resolve at all -- everything
else is under 50 microseconds per op phase, which is to say a few hundred interpreter
steps, and the harness prints that rather than a ratio.

The build phase is where the optimized program pays, and for the four subjects with a
declared key it is where it collects instead. The uniqueness guard the elaborator emits
is a scan, so building an n-row table costs O(n^2) in the source; the declared index
turns the guard into one probe. At 800 rows that is 4.50M steps against 51.2K for
`Keycloak_CachedRealm`, 5.77M against 58.4K for `Kafka_NamedCache`, 2.25M against 41.6K
for `HA_AreaRegistry` and 2.25M against 135K for `Jenkins_UserSearch`. For the four
subjects whose table arrives already populated the direction reverses, as it should:
the source does no setup at all and the optimized program spends 3.2K to 19.2K steps
building its indexes once, before the loop.

`HA_LookinFunctions` is where the set coercion is visible at runtime rather than only in
the term. Both of its membership tests go from 7.8x and 7.9x to 1.0x, and alongside that
the source canonicalises a bag 40 times in a query phase, to compare it against the
empty bag, while the optimized program does it zero times, because `FilterEmptyToSetMem`
has replaced the comparison with a membership test. Its table is the one that arrives
populated for a reason worth naming: the component is handed its device at construction
(`entity.py:91`) and only reads the list, so the list is an input, not something the
program builds. An earlier version of that file introduced the table with
`SLetConstrained`, which starts a table empty by definition; with no write anywhere in
the component the table then stayed empty at every n, and the subject could not be
measured at all. The fix was to model the input as an input, which is what
`Kafka_Cluster` -- immutable for the same reason -- already did.

## Against the originals' own structures

Everything above compares the source form with the optimized form, and the source form
is **not** the original author's code: the hand-built structure was removed so the query
could be written against one plain collection. So that comparison measures
declarative-with-no-index against compiler-indexed, and a reviewer can fairly say nobody
would write the left-hand column. `harness/baseline.ml` is the other comparison --
the authors' own structures and operations transcribed into OCaml, each citing the file
and line it came from, run over the same workloads. **Parity is the positive result**: the
compiler is supposed to arrive back at what the author built.

All thirty-one kinds agree with the optimized program on every workload -- the check that
a transcription computes the same answers, which caught a wrong one on its first run --
and every optimized exponent matches the author's except `Jenkins_UserSearch`'s `suggest`,
at 0.52 against the author's 1.00, because that index is the one the author did not build.

Two places run the other way, and both are a composite key the author indexed and this
development has no index for: `Cluster.partition(new TopicPartition(topic, partition))`
and `InMemoryWindowStore`'s inner map from key to value. The statement is structural, so
that it does not depend on how a counter is read: **the author descends a map on the whole
composite key, where the derived form probes one attribute and filters the bucket.** The
bucket is bounded, so the exponents still match. A third is noted rather than measured:
`partitionCountForTopic` answers a per-bucket count in O(1) from `ArrayList.size()`, which
would need a maintained aggregate per bucket -- the dict-of-aggregates combinator this
development does not build.

Three biases, all of them running in the author's favour and stated rather than corrected:
the originals' maps are hash maps where ours are `Map.Make(Value)`, so they win a log
factor on every point lookup (a backend freedom the type system records, not a defect in
the rewriting -- and `Kafka_NamedCache` is the exception, since its author chose a
`TreeMap`); wall-clock seconds are about 25% inflated on our side by the tree-walking
interpreter, measured; and the row counter charges each pipeline stage, so its constant is
not comparable factor for factor against code that has no stages. The build phase is never
compared at all -- the source's is O(n^2) because the declared-key subjects elaborate a
uniqueness guard into a scan while the originals check nothing, which is a claim about
constraint checking and not about a missing index. `harness/README.md` has the table.

One subject in that comparison has no author: `Ex_RangeDelete` is our own example, so what
stands in for one is the implementation its structure asks for. It is listed in
`Baseline.hand_written` and the report marks it, rather than letting it pass as a
transcription.

## Limits stated here rather than hidden

Each of these has a witness in the corpus and no rule, and each is pinned in the file
that found it rather than described in prose:

| gap | witness | pinned at |
|---|---|---|
| collection-keyed index | HA `_labels_index`, `_aliases_index` | stated in `HA_AreaRegistry.v`'s header |
| composite key | `Cluster.partition(topic, partition)`; `WindowStore.fetch(key, lo, hi)` | `one_partition_probes_then_filters`, `fetch_key_probes_split` |
| erasing a list whose only reader is its own write | `removeExpiredSegments()` rewrites the table from the table | `the_list_filter_keeps_the_list` -- but only in the unsplit configuration. Splitting removes the list's other reader, after which the field is erased and the write is incremental (`split_erases_the_list`). So the gap is narrower than it looked: it bites a program whose write is the list's **only** reader, which no subject here is |
| moving an indexable conjunct into the position the splitter peels | not exhibited here; the selector reads the first conjunct only, so an indexable conjunct elsewhere is invisible | not pinned: `swap_conjuncts_head` exists but is unconditional -- it reverses every conjunction it meets -- so it cannot bring one forward without reordering the rest. A guarded swap does not exist |
| a declared-key read at SET level is served, but by a SCAN rather than a probe | this file's own first draft | narrowed, not closed. `unique_lookup_head` still matches bag level only, so a set-level read of a declared key gets no probe. What it now gets is `unique_scan_head`, which serves it from the primary-key member instead of from the list -- enough to erase the field, not enough to make the read logarithmic. A set-level counterpart of the lookup rule does not exist; the rule that fires instead is correct and linear |
| a write that appends instead of prepending | every source here adds at the end or puts into a map | not pinned: `OConcat` exists, and **no rewrite rule in the development mentions it**, so such a write rebuilds every index instead of updating it. All seven maintenance rules (`cons_to_insert`, `cons_to_incr`, `cons_to_add`, `cons_to_set_insert`, `cons_to_min`, `cons_to_unique_insert`, `cons_to_tri_insert`) match `OCons` and nothing else |
| a read that observes row order | none here, by construction | not pinned, and the limit is wider than the write above: **every** index in the development is order-insensitive, so an order-observing read is served by none of them, and such a table keeps its list and gains nothing |

The count aggregate was on this list and is now built: `CountAgg`, pinned in
`Keycloak_CachedRealm.v` at `counted_list_read_is_a_field` and
`counted_erases_the_list`.

The range-shaped delete was on this list, first as a missing operator and then as
a missing rule, and both are now built. A one-sided delete is a restriction to
`[lo, inf)`, which `ODictRange` expresses since its bounds became optional, and a
two-sided one is `ODictRangeDelete`, the exact complement; the rules that fire on
a range-shaped write are `filter_range_to_dict_range_head` and
`filter_range_to_dict_range_delete_head`, both resting on the same equality --
`gallina_to_idx_filter_key_eq`, that building the index of a restricted table is
restricting the index of the whole one. The one-sided case is witnessed here, in
`Kafka_WindowStore`. The two-sided case has no witness in these files, because
the corpus's two-sided retention policies are in files not translated, so it is
witnessed by `Ex_RangeDelete.v` one directory up -- which is a rule test and is
cited as nothing more.

What is left is narrower and is what the row above now names: the list. The
retention write rewrites the table from the table, so the field cannot be
erased, and no rule turns a filter over the list into one over the member.

The substring row changed on 2026-10-23 and the change is worth stating, because the
earlier reading of it was wrong. There is still **no hand-built substring index** in any
of the seven corpora -- no trigram, n-gram, trie or suffix array -- and that is
structural: substring search is outsourced to a database or a search engine, so looking
for the structure finds nothing. But the *query* over a table the program maintains is
there and is first-class. Jenkins's own search facility gives every searchable
collection two lookups in one class, `find` by exact name through a hand-built map and
`suggest` by `contains` through a linear scan, which is the trigram pair's two members
with one of them missing. NetBox hand-builds the other half -- `CachedValue` is an
inverted index held as a table, postings carrying object identity, maintained on save
and delete, queried with `icontains`. So the claim for this index is **C3**, we beat the
hand-written code, rather than the **C4** claim the other files make; that is the
stronger of the two and the paper should say which it is.
`Jenkins_UserSearch.v` is that subject, written on 2026-10-23.

The first row is the one gap with no file of its own: `_labels_index` and
`_aliases_index` key on each element of a per-row collection rather than on one
attribute, and `HA_AreaRegistry.v`'s header says which two fields it drops and why.
