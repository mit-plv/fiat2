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
| `Kafka_WindowStore.v` | `InMemoryWindowStore.java:78` | the only ORDERED index: a time range answered out of a sorted dictionary, maintained across a put -- and two limits, a conjunctive range reader and a range-shaped delete |

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
change to the erasure rule. `Kafka_WindowStore` is now in that earlier position, for
the same reason and with the same diagnosis.

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
the same split produced two chained table scans. And `removeExpiredSegments` is a
range-shaped delete, which rebuilds -- so the list survives.

## Limits stated here rather than hidden

Each of these has a witness in the corpus and no rule, and each is pinned in the file
that found it rather than described in prose:

| gap | witness | pinned at |
|---|---|---|
| collection-keyed index | HA `_labels_index`, `_aliases_index` | stated in `HA_AreaRegistry.v`'s header |
| composite key | `Cluster.partition(topic, partition)`; `WindowStore.fetch(key, lo, hi)` | `one_partition_probes_then_filters`, `fetch_key_probes_split` |
| range-shaped delete | `subMap(lo, hi).clear()` (two-sided only) | `expiry_rebuilds` |
| `SplitIf` costs a range pair one bound | the same file's two readers | `fetch_all_loses_a_bound_split` |
| substring index | none found in seven corpora | -- |

The count aggregate was on this list and is now built: `CountAgg`, pinned in
`Keycloak_CachedRealm.v` at `counted_list_read_is_a_field` and
`counted_erases_the_list`.

The first row is the one gap with no file of its own: `_labels_index` and
`_aliases_index` key on each element of a per-row collection rather than on one
attribute, and `HA_AreaRegistry.v`'s header says which two fields it drops and why.
