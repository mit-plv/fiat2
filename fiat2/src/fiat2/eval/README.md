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
| `Keycloak_CachedRealm.v` | `CachedRealm.java:301` | two unique-key maps over one list; the list is read, so the list survives |
| `Kafka_Cluster.v` | `Cluster.java:114` | two bucketed maps over one collection; nothing reads the list, so the list is erased |
| `HA_AreaRegistry.v` | `area_registry.py:169` | a primary key dict and a secondary index, maintained across an insert and a delete; nothing reads the list, so the list is erased |
| `HA_LookinFunctions.v` | `lookin/entity.py:94` | a set derived from a list because no query observes order or multiplicity; both reads are membership probes, and the list is erased |

The first two are a pair, and should be read as one. They put the same erasure rule in
front of two code bases and get opposite answers -- keep the list, drop the list -- and
each answer is the storage the original's author chose by hand. Keycloak keeps
`requiredActionProviderList` beside both maps; `Cluster` has a field for every map it
derives and no field for `partitions`.

The third is the only one whose writes are its own, and it now reaches the original on
both of them: `delete_is_incremental` pins a delete that probes the primary member for
the leaving row and rewrites only the one bucket that row's attribute names, which is
`_unindex_entry` line for line. It needs `KeyedDictIdx`, and it is gated on the key
being declared.

Reading the three together: the first two show the erasure rule giving opposite answers
on read-only code, and the third shows that for code that writes, the erasure answer
depends on how well the writes are maintained. Before the keyed delete existed this
file kept its list -- not because a query read it, but because the rebuild did. The
delete becoming incremental is what erased it, with no change to the erasure rule.
That is the same decision procedure answering a third time, and it is the most useful
thing in the three files.

The fourth is the only one whose rewrite is licensed by the **collection
interpretation** rather than by a declared constraint -- its `decls` is empty. The
programmer wrote a `set`, not a list and not a map, because neither order nor
multiplicity of the names is ever observed; the optimizer reaches the same structure
from the queries alone, and erases the list because after the rewrite nothing reads it.
Read it against `Keycloak_CachedRealm`: same erasure rule, same built-once shape,
opposite answer about the list, and the reason is what the queries ask.

So the four cover both directions in which one category's conclusion licenses another's
rewrite: a declared uniqueness making a single-row lookup sound
(`Keycloak_CachedRealm`, `HA_AreaRegistry`), and an inferred interpretation making a
membership probe available (`HA_LookinFunctions`).

Still not reached: `_labels_index` and `_aliases_index`, which key on each element of a
per-row collection rather than on one attribute. That gap is stated here rather than
hidden, and `HA_AreaRegistry.v`'s header says which two fields it drops and why.
