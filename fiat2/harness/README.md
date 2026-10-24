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

Wall-clock seconds are printed too, per op kind, as a check that the counters have the
right shape and not as the result. They are weak evidence on purpose: they time a
tree-walking OCaml interpreter over an extracted AST, so the constants belong to this
harness rather than to anything a backend would produce, and the only thing worth
reading off them is whether a curve the counters call flat is flat in seconds too. An
op phase is timed as (build + ops) less (build alone), each side repeated until it has
accumulated 0.1s; where that difference falls under 50us the table prints `<50us`
rather than a ratio, because two nearly-equal timings subtracted do not have a
meaningful quotient. That happens for most of the optimized column, which is the point
being made rather than a gap in it: those op phases are a few hundred interpreter steps.

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
