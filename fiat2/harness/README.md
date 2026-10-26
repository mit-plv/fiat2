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

    make                              # from the repository root: compiles the Rocq
                                      # development and writes generated/
    dune build                        # from this directory
    ./_build/default/main.exe report  # what is in the terms
    ./_build/default/main.exe check   # the differential test
    ./_build/default/main.exe bench   # the measurement; takes table sizes
    ./_build/default/main.exe baseline      # against the originals' own code
    ./_build/default/main.exe alternatives  # a side note: what the selector's
                                            # own choice is worth

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

The deferred cost is counted rather than assumed away: `canonicalisations` says how often
a bag's canonical order actually had to be produced. Across all eight subjects it happens
in two places, both an `OEq` against the empty bag, and the interesting one is that the
optimizer removes it -- the membership subject's source canonicalises 40 times in an op
phase and its optimized form 0, which is the `FilterEmptyToSetMem` rule doing exactly
what it is for.

`report` also checks that no subject contains an `ESort` at all, before or after, so the
other observer never fires.

## What is counted

    steps   a unit of interpreter work: one entry into interp_expr, plus one for each
            element a primitive that is linear in its argument has to walk (OLength,
            ODictValues, OConcat, ORange, and the two aggregate folds).  A scan over n
            rows evaluates its body n times and shows up here; so does a fold over an
            n-element bag, which evaluates nothing but is no cheaper for it.  An index
            probe shows up in neither counter.
    cmps    entries into the value comparison, recursive ones included.  This is where
            the cost of a dictionary or set operation lives: a probe is logarithmically
            many, a scan linearly many.

Both are machine-independent, which is why they and not wall-clock time are the
evidence. A string comparison counts as one, which is honest only because the
generators keep keys short.

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
cost fits a power law loosely and should: a probe's comparison count comes out around
0.2 over this range, with a visible `~` on the subjects where the constant term is large
enough to bend it.

`csv [n ...]` prints the same op-phase series as one row per `(subject, kind, program,
rows)`, so the curves can be plotted or fitted independently. The table's exponents are
computed from exactly those numbers and nothing else. It is worth looking at the series
directly at least once -- for instance the Lookin membership test, whose optimized op
phase is **exactly 300 steps at every one of the six sizes** while its comparison count
goes 114, 134, 157, 177, 191, 211, gaining about twenty per doubling for twenty queries.
That is `log n`, stated by the data rather than by a curve fit.

Wall-clock seconds are printed too, **per operation**, as a check that the counters have
the right shape and not as the result. They are weak evidence on purpose: they time a
tree-walking OCaml interpreter over an extracted AST, so the constants belong to this
harness rather than to anything a backend would produce, and the only thing worth
reading off them is whether a curve the counters call flat is flat in seconds too.

An op phase is timed as (build + ops) less (build alone), each side repeated until it
has accumulated 0.1s. Two nearly-equal timings subtracted have no meaningful quotient,
so the op count **doubles until the difference clears 2ms** — which costs nothing for a
linear read and takes a few thousand operations for a flat one. A **write** is never
scaled: `Gen.workload` appends the op queries after the build, so five thousand inserts
on a fifty-row table would measure a table that grew a hundredfold while being measured.
`Gen.spec`'s `mutating` field names those kinds, and they keep the table's own op count
and print `<50us` when they fall below the floor.

That floor was asserted for a long time and is now measured. `main.exe timing <subject>
<kind> <rows>` reports the spread of the difference directly: at 1600 rows
`item_deletion/containsHit`'s optimized op phase is 9us over 20 operations with a **119%
spread**, which is indeed unreadable — but at 320 operations it is stable to 6%, at 1280
to 3%, and the implied per-operation cost agrees across all of them to within 2%. So the
floor was never a property of the clock; it was a property of using twenty operations.
With the scaling above, 25 of the 31 optimized entries that used to print `<50us` now
report a number, and the six that remain are all writes.

What the diagnostic also settled, which matters for anything built on top of these
numbers: **the interpreter is not where the time goes.** `containsHit`'s optimized cost
is 0.293us per operation at 50 rows and 0.460us at 1600, while the tree descent inside
`VSet.mem` goes from about 5.6 levels to 10.6 — so fitting `cost = fixed + k * levels`
puts the fixed part at roughly 0.11us and the structural part at 0.35us. The
interpreter's own dispatch and environment lookups are about **a quarter** of the cost at
1600 rows, and the rest is `Value.compare` walking records inside a balanced tree, which
is work any implementation using an ordered structure also does. Generating OCaml from
the interpreter would therefore buy a factor of roughly 1.3 here, not an order of
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
it came from, and runs them over the same workloads. Eight of the nine subjects have an
author; `range_delete` is our own example, so what stands in for one there is the
implementation its structure asks for, and it is listed in `Baseline.hand_written` so the
report marks it instead of letting it pass as a transcription.

**Parity is the expected result.** The compiler is supposed to arrive back at what the
author built, so matching asymptotics is the positive finding and a win would mean one of
the two is not what it claims to be.

Three instruments, because no one of them crosses the boundary cleanly:

| | crosses? | bias |
|---|---|---|
| `steps` | **no** | counts entries into `interp_expr`, which has no analogue in hand-written OCaml |
| `rows` | yes — its **exponent** is the headline | counts the elements an operation iterates — a scan is n, a probe that yields a row is 1, a membership test is 0, a write is 0 — but **once per pipeline stage**, so a derived read can count the same rows more than once. See below |
| `cmps` | yes | **undercounts a hash map** — one key equality per probe, no hashing. Flatters the author |
| s/op | yes | **~25% inflated on our side** by the interpreter, measured, not guessed |

`rows` is the instrument the other two cannot replace: `cmps` is blind to a traversal that
compares nothing, which is how Keycloak's whole-list **count** came out at exponent 0.00 on
the source side when its step count is linear. The build phase is never compared — our
source build is O(n²) because the declared-key subjects elaborate a uniqueness guard into a
table scan while the originals check nothing.

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

**The result.** All 31 kinds `agree`, and every optimized exponent matches the author's
except `user_search/suggest` at **0.52 against 1.00** — the trigram index Jenkins never
built, 66x faster than their own `contains` scan at 1600 rows. Two places run the other
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
write that the uniqueness guard then runs once per row. The table is in
`src/fiat2/eval/README.md`, under *Who chooses the heuristics*, which is where the
question belongs.

## The two checks that come free

`bench` compares the final stores of the source and the optimized program on every
input. They must be equal -- the table itself is gone by then, because `CLetMut` restores
the outer binding on the way out, so what is left is exactly the program's output. Each
`yes` in that column is therefore a concrete witness of that subject's soundness theorem
on that input.

`check` compares the evaluator against the oracle on both programs of all eight
subjects, over tables of 0, 1, 2, 7 and 23 rows and op phases of 0, 1 and 5 queries per
kind: 240 configurations, 0 mismatches. A failure there would be a bug in `eval.ml`, in
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
