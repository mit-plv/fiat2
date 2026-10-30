# Harness

The OCaml side of the evaluation. Nothing in here is verified, and nothing in here is
meant to be: it consumes terms the Rocq development produced, runs them, and counts.

## Layout

    generated/        extracted by src/fiat2/eval/Extract.v -- derived, not checked in
    count.ml          the counters the measurement is made of
    value.ml          values, and the representation choice the cost model rests on
    eval.ml           the evaluator: Interpret.v transcribed onto those values
    bridge.ml         the bijection between the two representations, written out
    gen.ml            one workload spec per subject
    free.ml           the names a program reads without binding
    report.ml         what is in the extracted terms; evaluates nothing
    differential.ml   the evaluator against the Gallina interpreter
    bench.ml          the subjects, run and counted
    main.ml           entry point: report | check | bench

## Building and running

    opam install containers-data      # the one library the harness needs: CCHashTrie,
                                      # a persistent hash map, for the hashed stores
    make                              # from the repository root: compiles the Rocq
                                      # development and writes generated/
    dune build                        # from this directory
    ./_build/default/main.exe report  # what is in the terms
    ./_build/default/main.exe check   # the store check, then the differential test
    ./_build/default/main.exe stores  # the store check alone
    ./_build/default/main.exe bench   # the measurement; takes table sizes
    ./_build/default/main.exe baseline      # against the originals' own code
    ./_build/default/main.exe threeway      # all three programs in one table:
                                            # as written, derived, and the author's
    ./_build/default/main.exe matched       # both sides, under each of the three
                                            # structure settings
    ./_build/default/main.exe alternatives  # a side note: what the selector's
                                            # own choice is worth

Any command takes a **structure setting** -- `typed`, `trees` or `hashes` -- which says
what every point-access collection is charged as, **on both sides at once**:

    ./_build/default/main.exe check hashes
    ./_build/default/main.exe csv trees 1600

| setting | our side | the originals |
|---|---|---|
| `typed` (default) | `Unranged` dicts hash (`dict_kind` licenses it); sets are trees (no `set_kind`) | as the author wrote them |
| `trees` | everything a tree | everything a tree |
| `hashes` | everything a tree may not be | every map whose order the modelled operations never read |

No setting hashes a structure whose operations **read** the key order -- our `Ranged`
dictionaries, and the ordered maps `window_store` and `range_delete` range-query. A row
whose three columns agree is a row with no structure choice in it.

The extraction is part of the ordinary Rocq build, so `generated/` is derived and
gitignored. `dune build` before a `make` fails with a missing module, which is the
intended failure.

## What crosses the boundary

The abstract syntax; each subject program twice, before and after the optimizer, plus
the five alternative configurations the subject files pin and argue about; and the
Gallina interpreter. Each program term is the normal form of the very definition its
own file's soundness theorem is about, reduced by `vm_compute` and handed over as data,
so there is no transcription step between the verified optimizer's output and the thing
that gets measured.

The interpreter is there as an **oracle and nothing else**. Nothing that measures
anything calls it. `interp_expr`'s dictionaries are canonical sorted association lists,
so an evaluator extracted from it would have a linear insert and a linear lookup --
destroying the incrementality the measurement exists to demonstrate, in exactly the
direction that matters. The evaluator is written by hand against the denotations; the
oracle is what checks that the hand did not slip.

Two mappings are unverified and belong in the paper's assumptions beside the choice of
representations:

| Rocq | OCaml | why it matters |
|---|---|---|
| `Z` | `int` | sound while every integer in a run stays in range; the generators keep them small |
| `string` | `string` | not cosmetic. The default extraction of a Rocq string is a list of characters, which would make `OStrContains` and `OSubstring` linear in the wrong parameter and distort the substring subject specifically |

## The cost model

`value.ml` is where the asymptotics is decided, so the reasoning is worth stating
plainly. A representation has to denote the same map, multiset or set as the
specification's, and it has to pay for anything the semantics can **observe** about the
canonical form. What the semantics observes is narrow: `OEq` on two collections, and
`ESort`, which hands the canonical order back as a list. Nothing else can see it. So:

| | representation | why |
|---|---|---|
| dict | balanced tree | canonical in the same sense as the sorted list, so the bijection is the identity on bindings; lookup, insert, delete and range restriction cost a path |
| set | balanced tree | a set rejects duplicates on insert, so it needs the order anyway, and `OSetMem` is a probe |
| bag | unordered list | a bag rejects nothing and probes nothing; every operation on one in these programs is an insert, a concatenation or a fold |

**Representation and charge are separate questions, deliberately.** The table above is
the *storage*. **For a dictionary the two are now the same question.** The setting picks
the store when the dictionary is created (`Value.dempty`) and the store is what the
operations run on: a `Map.Make` balanced tree where the kind is Ordered, `CCHashTrie`'s
persistent hash-array-mapped trie where it is Hashed. So a dictionary's cost is
**counted, not charged** -- `Value.compare` counts the tree's descent, `Value.hash` the
trie's hash and `Value.equal` its leaf comparison -- and it is counted the same way on
both sides, because both sides run the same structure rather than calling the same
pricing helper. That is a stronger claim than the one this file used to make, and one
that cannot drift.

It also moves a theorem from honour to enforcement. `TyODictRange` is stated at
`TDict Ranged`, so an `Unranged` dictionary can never be asked for a range -- and
`CCHashTrie` has no `split` to offer, because a hash table has no key order to split at.
A range restriction is now impossible to *write* against a hashed store, where it used to
be a `failwith` the harness had to remember.

**A set is the same story, with no annotation to consult.** `TSet` carries no kind, so
`Count.unlicensed` picks its store (`Value.sempty`) -- a tree under `typed` and `trees`,
a trie under `hashes` -- which is what makes the `hashes` column a *measurement* of what
a `set_kind` would be worth rather than a charge standing in for one. Union,
intersection and difference have no trie counterpart to call, so where either side is
hashed they iterate one side and probe the other, which is the cost model the old
`set_pair` already described, with the probes now real. Two trees still merge, because
that is what a backend holding two trees would do.

**A bag is a list under every setting, and that is a finding rather than an omission.**
It has three implementations here -- a list, a multiset over a tree, a multiset over a
trie -- and the dial was tried both other ways. The figures below are the key-work
ratios as that experiment measured them, before `strings` and `fields` were counted;
the orders of magnitude are what the comparison rests on and they do not move:

| Ordered as a tree | Hashed as a trie |
|---|---|
| `OBagOfList` becomes n·log n whole-row comparisons, and coercing the table to a bag is the *whole* of what a source-form membership test does. `user_search/suggestMiss` 60 → **612,820**, `suggestShort` 10,074 → **637,464**, `window_store/fetchAll` 508 → 2,599 | every bag construction hashes every element for a benefit no fold collects. **Every** ratio in the `hashes` column got worse: `suggestShort` 1.02 → **38.02**, `area_registry/remove` 3.88 → 22.57, `cluster/available` 7.03 → 44.22 |

A dictionary's choice can be uniform because every dictionary here is probed, and a set's
because every set here is tested for membership. A bag's cannot: the right structure
depends on whether *that* bag is ever removed from, and these programs build bags
constantly while only one subject's rules remove from one. Both uniform answers are wrong
by one to four orders of magnitude. **A per-bag question needs a per-bag annotation**,
which is what `dict_kind` is for dictionaries — and the measurement above is a better
argument for one than "the harness cannot tell one bag from another".

The three stores stay, because `BTree` and `BHash` are what a bag that is removed from
should hold and what `OBagDiff` is fast on, and the store check exercises all three. So
when something can say which bags those are, the structures are already here and already
checked.

The consequence, now narrowed to what is still true: **wall-clock seconds follow the
charge for a dictionary and a set, and not for a bag.**

The deferred cost is counted rather than assumed away: `canonicalisations` says how often
a bag's canonical order actually had to be produced, and across every subject, phase and
size it is now **zero**. Every site that used to fire was an `OEq` against the *empty*
bag, which asks nothing about order; `value.ml` answers those arms directly, charging what
a backend would pay rather than what a list costs. Two of the three sites were comparing
two empty bags and so had always been free. The third was real: `HA_AreaRegistry`'s keyed
delete asking whether a bucket had emptied, which sorted the bucket to find out -- 48
comparisons per delete, 62% of that kind's cost, and Θ(b·log b) in the bucket size where
a backend pays Θ(1). A line reappearing in that report would mean a subject had begun to
observe a bag's order for real.

`report` also checks that no subject contains an `ESort` at all, before or after, so the
other observer never fires.

## What is counted

**One figure, and its decomposition.** `work` is every elementary operation a run
performs. It is a *sum*, not a selection, and the named counters below are what it is
the sum of -- so a cost cannot be left out of the measurement without being left out of
one of these, and the invariant that stops that is in `eval.ml`'s dispatch: the match
over the operator is exhaustive, so a new operator cannot arrive costing nothing by
falling into a catch-all.

    work       = steps + overhead | cmps + hashing + strings + fields
    data work  =                    cmps + hashing + strings + fields

The bar is the boundary. Everything to its right is work the *program* does and both
sides of the author comparison really perform; everything to its left is this
interpreter's own, and a compiled backend would not pay it. That is why there are two
figures rather than one: see below.

    steps     a unit of interpreter work: one entry into interp_expr, plus one for each
              element a primitive that is linear in its argument has to walk (OLength,
              ODictValues, OConcat, ORange, and the two aggregate folds).  A scan over n
              rows evaluates its body n times and shows up here; so does a fold over an
              n-element bag, which evaluates nothing but is no cheaper for it.  An index
              probe shows up in neither this nor rows.
    overhead  what the interpreter does for itself: the string comparisons a lookup or
              an insert into its map of local names performs, and the ones that put a
              record's fields in canonical order when one is built.  A backend reads a
              local from a slot and lays a record out at compile time, so neither is a
              cost the program implies.  It runs about the same size as steps, which is
              the argument for naming it rather than folding it in.
    cmps      entries into the value comparison, recursive ones included.  A tree descent
              is logarithmically many, a scan linearly many.
    hashing   value nodes walked in order to HASH a key, one per node, by exactly the
              rule cmps uses for the nodes walked in order to compare one.
    strings   characters a string primitive examines or produces: the positions a naive
              substring scan really compares before it stops, the bytes a substring
              copies or a concatenation writes, the digits an int-to-string emits.
    fields    record fields a projection walks past before reaching the one it wants.
    rows      the stored elements an operation ITERATES -- a scan of n is n, a probe that
              yields a row is 1, a membership test is 0 because it yields nothing, a
              write is 0 because it writes -- counted once per NESTING LEVEL that
              iterates them.  A different VIEW of work already counted, not a component
              of it, so it is not in the sum.
    canonicalisations
              every time a bag's canonical order had to be produced, which is the only
              cost the unordered bag defers.  Identically zero across the development; a
              nonzero value is a signal, not a measurement.

All of them are machine-independent, which is why they and not wall-clock time are the
evidence.

**Why `strings` and `fields` were worth adding, with the numbers that say so.** Both
were previously free: the dispatch of `OStrContains` was one step however long the two
strings were, and a record projection cost nothing at all. Neither changed an exponent,
because the generators fix the strings and the terms fix the records -- but nothing in
the instrument said so, and two rows were being reported wrongly because of it:

| | with key work alone | with the complete figure |
|---|---|---|
| `user_search/suggest`, ours against the author's | **2.53x against us** | **0.0064x in our favour** |
| `window_store/fetchAll`, source against optimized | **0.04x**, flagged in this file as an instrument artifact | **396x**, and the caveat deleted rather than explained |

The first is the subject that is *about* string matching. The author's own algorithm is
a `contains()` scan over every row, which really does about 200,000 character
comparisons at 1600 rows; key work charged it 184, because a character comparison is not
a key comparison. The complete figure now agrees with the wall clock, which had been
saying 57x in our favour all along -- so this was not a presentational problem. The
second is the mirror image: a scan whose per-row cost is a field projection and an
integer comparison was called *flat*, which made the optimizer's win on that row look
like a loss.

**Why the total cannot be the one number for the author comparison.** `steps` counts
entries into `interp_expr` and `overhead` counts this interpreter's own bookkeeping, and
hand-written OCaml has neither. Charging them to our side and to nothing on theirs would
make the comparison a measurement of the harness. So the tables that cross the boundary
use **data work**, which is complete for everything the two sides both do, and the gap
between the two figures is named rather than hidden. A string key costs one comparison
or one hash **plus its bytes**, charged to `strings`: the prefix a comparison shares
before it stops, or the whole length when a hash walks it. So the work a key costs is
`cmps + hashing + strings`, and a long key costs what it costs.

**"Once per nesting level" is not "once",** and it has nothing to do with the phases of
the optimizer -- this harness never runs the optimizer, it runs the extracted terms. It
means once per iterating construct in the term. `window_store`'s optimized `fetchAll`
answers a window of 8 rows and reports 24, because it is

    EACFold (AGCount,            <- walk n      = 8
      EFlatmap (LikeBag,         <- visit n     = 8
        EUnop (ODictValues,      <- walk 1 each = 8
          ETernop (ODictRange,   <- 0: a split, charged to cmps
            ...))))

where `cluster`'s `forTopic` is an `EACFold` over one `OLookup` -- one iterating
construct, a probe that charges no rows, so 8. Both are **flat** in the table size (480
and 160 per 20 queries at 400, 800 and 1600), because the depth is a constant of the
term. So the exponent is unaffected; the constant is comparable between two forms of the
same subject at the same depth, and **not** against hand-written code, which has no
nesting levels to count.

Neither is a count of AST nodes. `report` prints those -- they say how big a program
the optimizer wrote -- and nothing below uses them. `bench` runs the programs.

## Asymptotics, which is what the claim is about

An op kind is measured at **every** size, and the per-kind table reports the exponent
`a` in `cost ~ rows^a`, fitted by least squares on the logs. A ratio between two sizes
cannot do this job: over an 8x range, `n` grows 8.0x and `n log n` grows 9.4x, which is
inside the spread the generators' own bucketing produces. The default sizes double --
50, 100, 200, 400, 800, 1600 -- because an exponent is read off evenly spaced points on
a log axis, and 32x is as wide as the quadratic source build phases allow. `bench 100
400 1600` overrides them.

The exponent is printed with a `~` when the fit is loose, because reporting a fitted
exponent without saying how it fit would be worse than reporting nothing. A logarithmic
cost fits a power law loosely and should, with a visible `~` where the constant term is
large enough to bend it.

**The key-work component separates the three structures by exponent alone**, which is
worth reading as a result rather than as a scale. This is the one place below where the
component and not the total is the right quantity, because it is the only part of the
total the structure setting moves. `csv [n ...]` prints every component as one row per
`(subject, kind, program, rows)`, so the curves can be checked independently; the
table's exponents are computed from exactly those numbers and nothing else. Three
series, all optimized, all twenty queries, `cmps + hashing`:

| structure | series | exponent |
|---|---|---|
| `Unranged` dict (`keycloak/byId`, charged as a hash) | `60+20` at **every one of the six sizes** | 0.00 |
| set (`lookin/varyingKey`, no `set_kind`, charged as a tree) | 114, 134, 157, 177, 191, 211 | 0.18 |
| `Ranged` dict (`window_store/fetchAll`, which needs the order) | 272, 316, 357, 398, 453, 508 | 0.18 |

Those are the **`typed`** column, and the structure setting moves exactly the two rows
it should. Same three reads, same six sizes, under each setting:

| | `typed` | `trees` | `hashes` |
|---|---|---|---|
| `keycloak/byId` | `80` flat | 136, 157, 187, 200, 216, 242 | `80` flat |
| `lookin/varyingKey` | 114 … 211 | 114 … 211 | `59` flat |
| `window_store/fetchAll` | 272 … 508 | 272 … 508 | 272 … 508 |

The `Unranged` dictionary is flat wherever anything is allowed to hash and a descent on
the floor. The set is a descent until `hashes` licenses what a `set_kind` would, and
then it is flat. The `Ranged` dictionary is **the same series in all three**, because a
range restriction reads the key order and no setting can hash it — which is the clearest
statement available that the parameter is not a dial for making numbers smaller.

The middle and bottom rows are `log n`, stated by the data rather than by a curve fit --
about twenty more comparisons per doubling across twenty queries. The top row is not a
weak power law at all: it is the same number at 50 rows and at 1600. Which structure a
read lands on is decided by the type system, so the column reads off `dict_kind` rather
than anything this harness chose. The Lookin step count is **exactly 300 at every size**
in all three cases, which is the other half of the point -- `steps` cannot see a tree
descent, and the key-work component is where it lives.

Wall-clock seconds are printed too, **per operation**, as a check that the counters have
the right shape and not as the result. They are weak evidence on purpose: they time a
tree-walking OCaml interpreter over an extracted AST, so the constants belong to this
harness rather than to anything a backend would produce, and the only thing worth
reading off them is whether a curve the counters call flat is flat in seconds too.

**The check the seconds exist to provide, made.** Over 42 op kinds, the counters call 39
of them flat or sublinear in the table and 3 of them linear. The clock agrees on every
one: across a **32x** table the 30 timeable flat kinds grow by a median of **1.1x** and
at most 4.3x, while the three the counters call linear grow **34x, 36x and 32x**. The
three are `user_search/suggestMiss` and `suggestShort`, the two deliberately-linear
fallback kinds, and `dependent_plugins/resolveAll`, whose derived form is linear where
the author's is quadratic. Nothing the counters call flat is linear on the clock, which
is the one thing this column could falsify and does not.

An op phase is timed as (build + ops) less (build alone), each side repeated until it
has accumulated 0.1s. Two nearly-equal timings subtracted have no meaningful quotient,
so the op count **doubles until the difference clears 2ms** — which costs nothing for a
linear read and takes a few thousand operations for a flat one. A **write** is never
scaled: `Gen.workload` appends the op queries after the build, so five thousand inserts
on a fifty-row table would measure a table that grew a hundredfold while being measured.
`Gen.spec`'s `mutating` field names those kinds, and they keep the table's own op count
and print `<50us` when they fall below the floor.

That floor was asserted for a long time and is now measured. `main.exe timing <subject>
<kind> <rows>` reports the spread of the difference directly. At 1600 rows,
`item_deletion/containsHit`'s optimized op phase over seven repetitions:

| ops | mean | spread | per-op |
|---|---|---|---|
| 20 | 14us | **604%** | 6.8e-07 |
| 80 | 89us | 41% | 1.12e-06 |
| 320 | 336us | 28% | 1.05e-06 |
| 1280 | 1.29ms | 7.2% | 1.00e-06 |
| 5120 | 5.32ms | 5.0% | 1.04e-06 |

Twenty operations is indeed unreadable — the difference of two 20ms numbers is noise with
a sign. But the per-operation cost it implies is within about 10% of the one 5120
operations implies, and the spread falls monotonically as the op count rises. So the
floor was never a property of the clock; it was a property of using twenty operations.
With the scaling above, most of the optimized entries that used to print `<50us` now
report a number — on a recent run, 36 of the 42 do — and every one that still does not is
a **write**, which is the one thing the scaling cannot be applied to. Which writes fall
below the floor varies between runs, since they sit just under it; which *kinds* can fall
below it does not.

**The instrumentation itself costs about 2x of the wall clock, and it is now measured
rather than hoped.** Counting the characters a string scan compares means comparing them
one at a time instead of letting `String.sub` reach a `memcmp`, and counting the record
fields a projection walks means a hand-written loop instead of `List.assoc`. Timing the
same kinds on the same machine before and after: the optimized programs got **2.02x**
slower, the author transcriptions **2.07x**, and the source programs 1.34x. It lands on
both columns of the author comparison at nearly the same rate, so the ratios survive —
`item_deletion/containsHit` reads 2.67x ours-over-theirs where it read 2.51x before —
but the absolute seconds are now the harness's instrumented clock and not even its
uninstrumented one. One more reason the counters and not the seconds are the evidence.

What the diagnostic also settled, which matters for anything built on top of these
numbers: **the interpreter is not where the time goes.** `containsHit`'s optimized cost
is 0.66us per operation at 50 rows and 1.06us at 1600, while the tree descent inside the
set goes from about 5.6 levels to 10.6 — so fitting `cost = fixed + k * levels` puts the
fixed part at roughly 0.22us and the per-level part at 0.08us. The interpreter's own
dispatch and environment lookups are about **a fifth** of the cost at 1600 rows (it was
a quarter before the instrumentation above was added, which inflates both parts), and
the rest is `Value.compare` walking records inside a balanced tree, which is work any
implementation using an ordered structure also does. Generating OCaml from the
interpreter would therefore buy a factor of roughly **1.3** here, not an order of
magnitude: what separates these seconds from hand-written code is the **representation**
(boxed dynamic values compared structurally) and the **structure choice** (tree where the
original used a hash), not the evaluation strategy.

## The originals, beside the optimizer's output

`main.exe baseline` is the other comparison, and the more important one. Everything above
compares our source form against our optimized form — but **the source form is not the
author's code**: the author's hand-built structure was removed so the query could be
written declaratively, so `src -> opt` measures "declarative with no index" against
"compiler-indexed", and a reviewer can fairly say nobody would write that baseline.
`baseline.ml` transcribes the **authors' own structures**, each citing the file and line
it came from, and runs them over the same workloads. Nine of the eleven subjects have an
author. `range_delete` is our own example, so what stands in for one there is the
implementation its structure asks for, and it is listed in `Baseline.hand_written` so the
report marks it instead of letting it pass as a transcription; `sat4j` came from Cozy's
benchmark suite rather than from a program we chose, and has no transcription at all, so
its author column is empty everywhere.

**Parity is the expected result.** The compiler is supposed to arrive back at what the
author built, so matching asymptotics is the positive finding and a win would mean one of
the two is not what it claims to be.

Three instruments, because no one of them crosses the boundary cleanly:

| | crosses? | bias |
|---|---|---|
| `steps` + `overhead` | **no** | entries into `interp_expr`, and the interpreter's own name lookups and record ordering. Hand-written OCaml does neither. Together they are about half of `work` |
| `rows` | yes — its **exponent** is the headline | counts the elements an operation iterates — a scan is n, a probe that yields a row is 1, a membership test is 0, a write is 0 — but **once per nesting level**, so a derived read can count the same rows more than once. See below |
| **data work** | yes | `cmps + hashing + strings + fields`: everything the two sides both really do. Not one convention applied twice — the same code. Both columns hold the stores the run's setting names, both call the same `Eval.str_contains`, both project a record through the same accessor |
| s/op | yes | **~25% inflated on our side** by the interpreter, measured, not guessed. It **follows** the charge for dictionaries and sets, which hold the store their setting names, and does **not** for bags, which are a list under every setting for the reason given above |

`rows` is still the instrument the others cannot replace, though it is no longer the
only one that sees a traversal: completing the figure is what fixed that. Keycloak's
whole-list **count** came out at exponent 0.00 on the source side under key work alone,
while its step count was linear; its data-work exponent is now linear too, because the
scan projects a field per row. `rows` remains the one counter that is about *stored
elements* rather than operations, which is a different question and the one an index is
supposed to change.

**The structure choice is a parameter, the same one on both sides.** It used to be an
assumption buried in the instrument: ours was charged as a hash because its type said
`Unranged`, while the originals' was charged as whatever the author happened to write. So
Kafka's `NamedCache`, whose author chose a `NavigableMap`, compared our hash against their
tree — and the number flattered us for a reason that had nothing to do with the optimizer.
`matched` prints the three settings side by side, and within a column both sides ran the
same structure, so the ratio compares two *programs*.

What that shows, at 1600 rows, data work as ours/theirs:

| | `typed` | `trees` | `hashes` | what the spread is |
|---|---|---|---|---|
| `named_cache/get` | **1.15** | 1.76 | 3.00 | the confound. Matched, we are behind; the 0.50 this row used to read was their tree against our hash |
| `item_deletion/containsHit` | 3.02 | **1.12** | 1.33 | almost all of it is the set charging gap, not the algorithm |
| `lookin/varyingKey` | 3.14 | 1.22 | **1.61** | what a `set_kind` is worth: 3.14 → 1.61 |
| `window_store/fetchAll` | 1.29 | 1.29 | 1.29 | a `Ranged` dict: no structure choice in it at all |
| `cluster/onePartition` | 4.50 | **2.14** | 4.50 | their composite-key descent costs less than ours; a tree narrows it rather than closing it |
| `user_search/suggest` | **0.0064** | 0.0090 | 0.0066 | the trigram index against a `contains()` scan: 156x, and visible only now that a character comparison is counted |
| `dependent_plugins/resolveAll` | 0.0088 | **0.0081** | 0.0088 | hashing is *dearer* than a shallow descent here, which is why the model is not rigged toward hashes |

So the remaining asymmetry is named and now also **priced**: sets have no `set_kind`, so
under `typed` — the only column every charge of which the type system backs —
`TableRep`'s set and the set indexes are the trees they are stored in. `hashes` is the
measurement of what the annotation would buy, and `item_deletion` and `lookin` are where
it lands. Completing the figure made that gap look *smaller* rather than larger, because
the record and string work it added is the same on both sides and dilutes a ratio that
was all key work: `lookin/varyingKey` reads 3.14x where key work alone said 5.41x. The
unchanged statement underneath is the structural one: on 20 queries ours pays **211
comparisons** descending a tree where the author pays **39 units** probing a hash, and
licensing the hash would take ours to **59**.

The build phase is never compared, and that exclusion is the one asymmetry running in
**our** favour rather than the author's: our source build is O(n²) because the declared-key
subjects elaborate a uniqueness guard into a table scan. The reason for excluding it is
that it is a claim about constraint checking rather than about a missing index — but
"the originals check nothing" is not true of all of them, and Keycloak is the counterexample.
Its `id` is a JPA `@Id` with primary key `CONSTRAINT_REQ_ACT_PRV_PK`, so the database
enforces it and no application code looks; its `alias` has **no** unique constraint in any
changelog, and is enforced instead at one write path, `RealmAdapter.addRequiredActionProvider`,
by `getRequiredActionProviderByAlias` — a linear scan of the collection followed by a
throw. That is the same shape `SLetConstrained` + `DUnique` elaborates, so on that key the
build phase is a comparison we could make rather than one we have to decline.

**What the constant in the `rows` column is not.** The counter charges every stage of a
pipeline that iterates a collection, and an intermediate collection is not storage.
Measured: `window_store/fetchAll` answers a window of 8 rows and reports **24** — eight
dict entries out of the ranged member, then the eight buckets they hold, then the eight
rows inside them — while `cluster/forTopic` answers a bucket of 8 through one lookup and
reports **8**. Hand-written code has no stages at all. The number of stages is a constant
of the term, so the **exponent** is unaffected, which is why the claims are exponents; an
opt-against-base ratio on a multi-stage read is partly an artifact of how many stages the
rewriting left, and the gaps that matter are named structurally as well as numbered. This
is also why `named_cache/delete` reports 2 rows per delete against the author's 1 and is
*not* reading the row twice: `delete_corrects_by_a_probe` pins one probe, and the second
tick is the fold over the projection of the row the probe found.

**The result.** All 32 kinds `agree`. Every optimized `rows` exponent matches the
author's but two, and both are ours: `user_search/suggest` at **0.52 against 1.00** — the
trigram index Jenkins never built, **156x** less data work than their own `contains` scan
at 1600 rows and 57x faster on the clock — and `dependent_plugins/resolveAll` at **1.00
against 2.00**, where the author's own code is quadratic. Two places run the other
way, both a composite key the author indexed and this development has no index for:
`Cluster.partition(new TopicPartition(topic, partition))` and `InMemoryWindowStore`'s
inner map from key to value. Stated structurally, because that statement does not depend
on how stages are counted: **the author descends a map on the whole composite key, where
the derived form probes one attribute and filters the bucket.** Same exponent, bounded
bucket, and each is the gap its own subject file pins (`one_partition_probes_then_filters`,
`fetch_key_probes_split`). Kafka's `partitionCountForTopic` is a third, noted rather than
measured: it answers a per-bucket count in O(1) from `ArrayList.size()`, which would need
a maintained aggregate per bucket — the dict-of-aggregates combinator this development
does not build.

The column that actually matters is `agree`: each transcription's final store is printed the
same way the subject's is, so a transcription that computes something else is caught before
any of its numbers are read. It earned its place on the first run — `item_deletion`'s table
arrives in the environment rather than through build queries, the transcription started
empty, and every `containsHit` disagreed.

## All three in one table

`main.exe threeway` is the two comparisons above printed side by side, one row per op
kind: the query **as written** with no index, the program the optimizer **derives** from
it, and the **author's own** code. The two ratios are the two claims — `src/opt` is what
the optimizer buys, `opt/orig` is whether it arrived back where the author was by hand —
and the exponents are what either claim actually rests on.

Only **data work** is shown, because it is what crosses to `orig`: `steps` counts this
interpreter walking a tree and `overhead` counts its own name lookups, and hand-written
OCaml does neither. The comparison of the complete total is in the `bench` table, where
both sides are the same interpreter. The source's total exponent is printed beside its
data exponent, as `src aT` beside `src aD`, so that the two can be seen to agree.

**This column used to be key work alone, and the two rows it misread are worth keeping.**
Both were fixed by completing the figure rather than by annotating it:

| kind | under key work | now | what was missing |
|---|---|---|---|
| `window_store/fetchAll`, `src/opt` | `0.04x`, with `src aK` 0.00 against `src aS` 0.99 | **396x**, `src aD` 1.00 | a scan whose range filter is `OLess` on ints compares no *keys*, so the instrument called a full scan flat. Its per-row cost is the field each row is projected through |
| `user_search/suggest`, `opt/orig` | `2.53x` against us | **0.0064x** in our favour | the author's algorithm *is* a `contains()` scan. 198,860 character comparisons at 1600 rows, charged as 184 |

The second one is the one to take seriously: it was not a presentational problem. The
wall clock had been reporting 57x in our favour on that row while the counter reported
2.53x against, and the counter was the thing we said was the evidence.

At 1600 rows under `typed`:

- **The exponent falls on every read.** `src aD` is 0.99–1.22 on every one of them now —
  there is no longer a read whose source column looks flat — and **2.00** on
  `dependent_plugins`, the one quadratic source. Against that, `opt aD` is **−0.01 to
  0.16** for the indexed reads, `~0.28` for `suggest`, and 1.00 for `resolveAll`. The two
  deliberately-linear fallback kinds are 0.99, which is what they are there to be. Same
  exponents in all three settings.
- **`src/opt` spans 1.00x to 1405x** on the data-work constant: `item_deletion/containsHit`
  1405x, `cluster/forTopic` 1164x, `dependent_plugins/resolveAll` 1143x *with the exponent
  halved underneath it*, `sat4j/findRecord` 1001x, `cluster/forNode` 561x,
  `area_registry/byId` 401x.
- **`opt/orig` on a read is a constant, never an exponent** — the parity the comparison
  predicts. Reads run 0.0064x to 8.50x, every exponent matching. The two that beat an
  author do it on the **exponent**: `user_search/suggest` at 0.0064x and
  `dependent_plugins/resolveAll` at 0.0088x, both against an author algorithm that is
  linear or quadratic where the derived form is not. The top of the range is
  `keycloak/wholeList` and `named_cache/sizeInBytes` at 8.50x, which is the honest cost
  of answering a whole-collection read by traversing it where the author keeps a cached
  number; after those, `item_deletion/register` 5.98x and `cluster/available` 4.53x.
- **Writes are where `opt/orig` is widest, and that is index maintenance**:
  `user_search/remove` **41.86x** — three indexes to keep, including the trigram pair
  Jenkins never built — `item_deletion/register` 5.98x, `area_registry/remove` 8.21x,
  `window_store/put` 1.47x, and `named_cache/delete` **0.65x**, where the derived form is
  ahead because the author re-walks a list the index replaces. The reads above are bought
  with these writes, and the table prices both rather than reporting only the half that
  flatters the compiler.
- **`src/opt` below 1 is mostly the same fact from the source side**:
  `range_delete/insert` 0.18x, `item_deletion/register` 0.25x, `window_store/put` 0.29x.
  The source form maintains nothing because it has no index to maintain. The two reads
  that used to sit below 1 were the instrument and do not any more; the two that remain
  are not — `keycloak/wholeList` 0.76x and `sat4j/size` 0.84x, both whole-collection
  reads with nothing to index, where the derived form reads through the index
  representation and pays a few more field projections for it. `src aD` on the first is
  **0.03**, so what the ratio is comparing is two flat constants.

All 42 kinds `agree`, at every size — which here is the stronger statement it looks like,
because it is checked across all three programs rather than two.

## A side note: what the selector's choice is worth

`main.exe alternatives` is kept out of both tables above, and the reason is the point of
it. Every program it runs is **sound**, and every one is this pipeline's own output on the
same source; the only difference within a pair is which indexes were listed and in what
order. So nothing in it says whether the rewriting works — it says what a program would
have paid had the selector picked the other configuration its file also pins. The five
pairs are the rule-ordering hazards catalogued in `Selector.v`, each already pinned as an
equality of terms in the file it belongs to; this puts a cost on those pins, and `chosen`
is what `eval/SelectorTests.v` pins as the selector's own pick, so a row where the
alternative won would be a selector **bug** rather than a caveat. None does.

It reports the build phase, unlike the baseline comparison, because a hazard can land on
a write: the table-representation pair degrades an insert, and for the subjects whose
inserts *are* their build that is the only place it would show. The result worth naming is
`named_cache/swapped`, whose build exponent goes 1.00 to **1.97** — both configurations
install the same two members, and listing them the other way round leaves a scan inside a
write that the uniqueness guard then runs once per row, costing 225x the total work at
1600 rows and 796x on the `delete` that follows. `user_search/table-rep` costs **194x**
the data work on `remove`, and `dependent_plugins/unpromoted` puts the exponent back to
2.00. The table is in
`src/fiat2/eval/README.md`, under *Who chooses the heuristics*, which is where the
question belongs.

## The two checks that come free

`bench` compares the final stores of the source and the optimized program on every
input. They must be equal -- the table itself is gone by then, because `CLetMut` restores
the outer binding on the way out, so what is left is exactly the program's output. Each
`yes` in that column is therefore a concrete witness of that subject's soundness theorem
on that input.

`check` compares the evaluator against the oracle on both programs of all eleven
subjects, over tables of 0, 1, 2, 7 and 23 rows and op phases of 0, 1 and 5 queries per
kind: 330 configurations, 0 mismatches, re-run under each of the three structure
settings. A failure there would be a bug in `eval.ml`, in
`bridge.ml` or in a generator -- never in the development, which depends on none of them.

## Reading the numbers

A workload has two phases, and `bench` reports them separately by running the subject
twice and subtracting. **build** brings the table to its size: for the four subjects
whose table is introduced empty, that is the insert queries, and the optimized program
pays its index maintenance there; for the four whose table arrives in the environment
it is the one-off cost of building the indexes from it. Which of the two a subject gets
is not the harness's choice -- it is whether the source builds the structure or is
handed it. **ops** is the queries, which is
what the optimizer is about.

Selectivity is the choice that matters. A read whose answer is a constant fraction of
the table is linear in the table however it is indexed, so every bucket in `gen.ml` --
floors, topics, keys -- grows with the table, keeping a bucket's size bounded. That is
the regime the source programs' own callers are in: `getRequiredActionProviderById`
returns one row.

Two op kinds break that discipline on purpose, and `gen.ml` says so where it defines
them. `suggestMiss` and `suggestShort` ask the substring subject for a token that no
trigram can serve -- one that matches nothing, and one shorter than three characters --
so that the guarded read's **fallback branch** is the branch measured. Without them the
fallback was never evaluated at any size, in the measurement or in the differential
test: every generated token was exactly three characters long, and the guard is
`2 < length token`. They are the two kinds whose optimized exponent is deliberately
linear, because a substring match has to look at every row; what they measure is which
rows it looks at and what that costs over the source's own scan.

A third kind, `suggestLong`, was added on 2026-10-30 for a different reason, and the
sentence above is why it was needed: *every* generated token was exactly three
characters long, so every token had exactly **one trigram**. The lookup rule intersects
the buckets of all of the pattern's trigrams, and on a one-trigram token that is the
same probe as taking the first bucket alone -- so the kind meant to exercise the rule
could not tell it apart from its predecessor at all. The guard was not the only thing
the token length was hiding.

`suggestLong` takes five characters out of the middle of a name, `"user0042"` ->
`"r0042"`, giving three trigrams whose buckets differ by two orders of magnitude:
`"r00"` is every name whose digits begin `00`, `"042"` is the one or two names
containing it. The first bucket alone leaves about a hundred candidates to resolve and
recheck; the intersection of the three leaves one or two. Swapping the two rules with
everything else held fixed, at 1600 rows:

| kind | src | one bucket | all trigrams |
| --- | --- | --- | --- |
| `suggest` | 648,937 | 5,673 | 5,893 |
| `suggestLong` | 628,160 | **96,700** | **6,687** |

So on a one-trigram token the two rules agree *to the index operation* -- `opt cmp+hash`
is `12713+379` either way -- and differ by 220 units of this interpreter's own fold
scaffolding, 3.9%. On a three-trigram token intersecting is **14.5x** cheaper, the
subject's whole op phase drops 6%, and hashing drops 5x. That asymmetry is what
`gin_trgm_consistent` exploits for `LIKE`, and before this kind existed our data could
not have shown it either way.

**Stale figures, flagged rather than silently revised:** the `user_search/suggest`
numbers quoted elsewhere in this file predate the rule swap, so its optimized work is
3.9% higher than they say and ratios derived from it move in the third significant
figure; subject-level aggregates for `user_search` now cover six op kinds rather than
five. The per-kind figures for every other subject and every other `user_search` kind
are unchanged, since neither the source programs nor the cost model moved.
