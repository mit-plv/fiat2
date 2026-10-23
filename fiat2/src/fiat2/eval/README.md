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
2. **Pattern** — the pattern IDs from `fiat2-paper/pattern-study` that the original
   instantiates. These say why the example was chosen; the study's counts are a
   discovery aid and never appear in the paper.
3. **Claim** — which evaluation claim the example evidences (see the evaluation log).
4. **Faithfulness** — what was dropped in translation and why, stated plainly. The
   original is Java or Python; an honest note here is what makes the example usable.
5. **Expected** — what the optimizer should produce, in words.

The expectation in (5) is then pinned by a lemma, in the style of `Ex_Range.v`: a small
projection out of the optimized program closed by `vm_compute; reflexivity`, rather than
an `exists` against the whole term, which does not terminate in reasonable time.

## The files

| file | source | what it is for |
|---|---|---|
| `Keycloak_CachedRealm.v` | `CachedRealm.java:301` | two unique-key maps over one list; the list is read, so the list survives -- and, in a second configuration, a maintained row count makes that last read a field read and the list is erased |
| `Kafka_Cluster.v` | `Cluster.java:114` | two bucketed maps over one collection; nothing reads the list, so the list is erased |
| `HA_AreaRegistry.v` | `area_registry.py:169` | a primary key dict and a secondary index, maintained across an insert and a delete; nothing reads the list, so the list is erased |
| `HA_LookinFunctions.v` | `lookin/entity.py:94` | a set derived from a list because no query observes order or multiplicity; both reads are membership probes, and the list is erased |
| `Kafka_NamedCache.v` | `NamedCache.java:44,49` | a keyed store and a running total over it, both maintained across a delete and a put; the total is corrected by a probe, never recomputed |
| `Kafka_WindowStore.v` | `InMemoryWindowStore.java:78` | the only ORDERED index: a time range answered out of a sorted dictionary, maintained incrementally across both a put and a range-shaped retention delete -- and two limits, a conjunctive range reader and a list that survives its own filter |

The six fall into three groups, and the groups are the argument.

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
development fixes the shape, not the constant. The list still survives, now because
the table's own field is assigned a row-by-row filter over itself and nothing recovers
the rows from the member (`the_list_filter_keeps_the_list`).

## Limits stated here rather than hidden

Each of these has a witness in the corpus and no rule, and each is pinned in the file
that found it rather than described in prose:

| gap | witness | pinned at |
|---|---|---|
| collection-keyed index | HA `_labels_index`, `_aliases_index` | stated in `HA_AreaRegistry.v`'s header |
| composite key | `Cluster.partition(topic, partition)`; `WindowStore.fetch(key, lo, hi)` | `one_partition_probes_then_filters`, `fetch_key_probes_split` |
| erasing a list whose only reader is its own write | `removeExpiredSegments()` rewrites the table from the table | `the_list_filter_keeps_the_list` |
| `SplitIf` costs a range pair one bound | the same file's two readers | `fetch_all_loses_a_bound_split` |
| an `eval/` subject for the substring index | Jenkins `hudson.search.CollectionSearchIndex:54-75` -- `find` is a hand-built map lookup and `suggest` a `contains` scan, same class, same collection | not yet written |

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
hand-written code, rather than the **C4** claim the files above make; that is the
stronger of the two and the paper should say which it is.

The first row is the one gap with no file of its own: `_labels_index` and
`_aliases_index` key on each element of a per-row collection rather than on one
attribute, and `HA_AreaRegistry.v`'s header says which two fields it drops and why.
