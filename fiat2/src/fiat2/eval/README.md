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
| `Jenkins_UserSearch.v` | `CollectionSearchIndex.java:54`, `Jenkins.java:2437` | the only SUBSTRING index, and the only file whose claim is that the author did NOT build the structure: `find` is their own `ConcurrentHashMap` lookup, `suggest` their own linear `contains` scan, one class and one collection; both writes maintain both members, and a second configuration erases the list |

The seven fall into four groups, and the groups are the argument.

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

It is also the file that measures the most. Two configurations, because no single one
serves both of the source's range readers well: without `SplitIf` the flat range is a
probe and the conjunctive one is a scan; with `SplitIf` the conjunctive one becomes a
probe refined by a key test, while the flat one keeps only its lower bound -- a
one-sided probe `[lo, inf)` with the upper bound left as a residual filter, because the
same splitter cuts the range pair in half and only one half can be a bound. That is a
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
keeps the source query as the other branch. That branch is why the list survives here,
and `rep_erases_the_list` shows what it takes to remove it: ask for the table's set
representation too, and the fallback scans that instead.

The delete is the part to read twice. The write names a key, not a row, so the postings
cannot be corrected without knowing which text the departing row carried -- and the pair
supplies it: the key member is probed for the row, and that row's id comes out of the
bucket of each trigram of its own text, with a bucket dropped when it empties. One
choice, two members, and the second exists so the first can be maintained.

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

WindowStore is where the cost shows. Its `fetchAll` reads a bare range pair, contributes
no reason to split, and is split anyway, because `SplitIf` is a whole-program rewrite --
so it loses one of its two bounds. The file measures that
(`fetch_all_loses_a_bound_split`) beside the three gains that come with it: `fetch`
becomes a probe, the list is erased, and retention reduces to the member's own incremental
restriction (`split_erases_the_list`, `split_expiry_is_only_the_restriction`). Three gains
against one loss; which is the better trade in general is a comparison, and the selector
is built to avoid comparisons, so both configurations stay pinned side by side.

The other is `TableRep`, which the selector never emits. It is the only choice whose
justification is a shape the pipeline *leaves behind* rather than one the program
contains -- the read it serves in `Jenkins_UserSearch` is the else branch of a guarded
probe, which the rewriting creates by keeping its own input -- so no matcher can ask for
it. A feedback step that runs the pipeline, finds the surviving read, adds `TableRep` and
runs again does reach that configuration; it was built and then removed, because the
goal turned out to be the wrong one. `TableRep` is a copy of the table, so erasing the
list while adding a rep member removes no structure: measured at
`rep_delete_filters_the_rep` and `rep_insert_is_a_set_insert`, the delete applies the
same O(n) filter to the member that it applied to the list, and the insert degrades from
a cons to a set insert. `Kafka_WindowStore` behaves the same way with a bag.

So the erasures that are wins are the ones where every read is answered by an index and
**nothing replaces the list** -- `Kafka_Cluster`, `HA_AreaRegistry`, `Kafka_NamedCache`,
and `Keycloak_CachedRealm` with its count.

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
everything. `TableRep` at set level **alone** does not erase `Jenkins_UserSearch`'s list:
`find` is a counted bag-level filter, so multiplicity is observed and the rep rule, which
matches only a set coercion, leaves that read scanning the list. At bag level alone the
list survives too, because the suggestion read is at set level. The erasure in that file's
second configuration happens only because the trigram pair has already taken `find`.

## Limits stated here rather than hidden

Each of these has a witness in the corpus and no rule, and each is pinned in the file
that found it rather than described in prose:

| gap | witness | pinned at |
|---|---|---|
| collection-keyed index | HA `_labels_index`, `_aliases_index` | stated in `HA_AreaRegistry.v`'s header |
| composite key | `Cluster.partition(topic, partition)`; `WindowStore.fetch(key, lo, hi)` | `one_partition_probes_then_filters`, `fetch_key_probes_split` |
| erasing a list whose only reader is its own write | `removeExpiredSegments()` rewrites the table from the table | `the_list_filter_keeps_the_list` -- but only in the unsplit configuration. Splitting removes the list's other reader, after which the field is erased and the write is incremental (`split_erases_the_list`). So the gap is narrower than it looked: it bites a program whose write is the list's **only** reader, which no subject here is |
| `SplitIf` is a whole-program rewrite, so a read that gains nothing from it pays anyway | the same file's two readers: one conjunction is worth splitting, the other is a bare range pair that loses a bound | `fetch_all_loses_a_bound_split`. Separating them needs a per-filter decision, which the basic rewrites do not have |
| moving an indexable conjunct into the position the splitter peels | not exhibited here; the selector reads the first conjunct only, so an indexable conjunct elsewhere is invisible | not pinned: `swap_conjuncts_head` exists but is unconditional -- it reverses every conjunction it meets -- so it cannot bring one forward without reordering the rest. A guarded swap does not exist |
| a declared-key read at SET level | this file's own first draft; `unique_lookup_head` (`UniqueIndexUse.v:438`) matches bag level only | stated in `Jenkins_UserSearch.v`'s Faithfulness |
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
