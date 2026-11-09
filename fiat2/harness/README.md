# Harness

The OCaml side of the evaluation. Nothing here is verified and nothing here is meant to
be: it consumes terms the Rocq development extracted, runs them, and measures them.

## Layout

    generated/         extracted by src/fiat2/eval/Extract.v -- derived, gitignored
    compiled/          the compiled backend's generated module, its correctness
                       checks and its measurement; monotypes.ml is written by a
                       dune rule running `main.exe types`, not by hand
    results/           reproduce.sh's output; see results/README.md
    reproduce.sh       regenerates every table the paper quotes

    value.ml           values, and the representation choice the cost model rests on
    count.ml           the counters; documents what each one charges and why
    eval.ml            the evaluator: Interpret.v transcribed onto those values
    bridge.ml          the bijection between the two representations
    differential.ml    the evaluator against the Gallina interpreter
    probe.ml           the dictionary store against a reference map
    gen.ml             one workload spec per subject
    free.ml            the names a program reads without binding
    report.ml          what is in the extracted terms; evaluates nothing
    bench.ml           the subjects, run and counted (interpreted)
    baseline.ml        the originals' own structures, interpreted
    mono.ml            the compiled backend's type level: a Conquord type
                       becomes an OCaml type, and the declarations that takes
    codegen.ml         its expressions and commands, type-directed; asks
                       Extracted.synth for each node's type rather than
                       carrying a second typechecker
    rt.ml              the runtime the compiled code and the author
                       transcriptions share; its string comparison IS
                       value.ml's, not a copy
    main.ml            entry point for the interpreted side

## Build and run

    opam install containers-data   # CCHashTrie, a persistent hash map, for hashed stores
    make                           # at the repository root: builds Rocq, writes generated/
    dune build                     # here

`dune build` before a `make` fails with a missing module, which is the intended failure.

`main.exe` — the interpreted side and the checks:

    report      what is in the extracted terms (the default)
    check       the store check, then the differential test against Gallina
    stores      the store check alone
    types       the OCaml type declarations the compiled backend needs (stdout)
    bench csv timing            measurement, data, and a wall-clock precision diagnostic
    baseline threeway matched   against the originals' own code
    alternatives enumerate      what the selector's choice is worth

`compiled/compiled.exe` — the compiled backend. With no argument it runs its four
correctness checks under all three settings:

    work shapes breakdown       counted
    time shapesec kinds writes  seconds
    threeway indexed matched    against the originals
    sweep scale stationary      the write-fraction sweep and the two checks it rests on
    alloc kalloc                the allocation instrument

Both executables take table sizes as trailing numbers, `only=a,b` to restrict subjects,
and `share=K` to set the funnel vocabulary and group size.

## Reproducing the paper's numbers

`./reproduce.sh [checks|counted|compare|timed|slow|all]` writes to `results/`, recording
in each file the command that produced it. Run `checks` first: a number from a tree that
does not pass it means nothing. `results/README.md` maps each claim to its file and says
which files are byte-stable; `reproduce.sh`'s own header gives the tiers and their
runtimes. Neither is repeated here, because this file once said four counted files when
there were six.

A claim is not finished until its subject is measured under **all three settings**. The
checks always ran under all three; the tables did not, and that is how a 110-184x
pathology on `fuzzy_search` under `hashes` went unnoticed -- correctness cannot see it,
because correctness is unaffected. `results/settings-all-subjects.txt` is the table that
catches it and is now part of `counted`.

## Two instruments, and what each is for

**Counters** (`count.ml`) are exact and deterministic, so they are the evidence for
shape: a read the counters call flat had better not take eight times longer on an
eight-times-larger table. Being deterministic also makes them a regression test — the
`counted` tier reproduces byte for byte on an unchanged tree.

**Seconds** come from the compiled backend. They are evidence that a counted result also
shows up on a clock, not a quantity to diff. Earlier versions of this file and of
`count.ml`'s header dismissed seconds outright; that was written when the only timing
instrument was the tree-walking interpreter, and the compiled backend superseded it.
Both instruments are live, and `results/` keeps them in separate tiers precisely so that
neither is mistaken for the other.

## Structure settings

Any command of either executable takes `typed`, `trees` or `hashes`, which says what
every point-access collection is charged as, **on both sides at once**:

| setting | our side | the originals |
|---|---|---|
| `typed` (default) | `Unranged` dicts hash (`dict_kind` licenses it); sets are trees (no `set_kind`) | as the author wrote them |
| `trees` | everything a tree | everything a tree |
| `hashes` | everything a tree may not be | every map whose order the modelled operations never read |

No setting hashes a structure whose operations **read** key order — our `Ranged`
dictionaries, and the ordered maps `window_store` and `range_delete` range-query. A row
whose three columns agree has no structure choice in it.

## What crosses the boundary

The abstract syntax; each subject program twice, before and after the optimizer, plus
the alternative configurations the subject files pin; and the Gallina interpreter. Each
term is the normal form of the very definition its own file's soundness theorem is
about, reduced by `vm_compute` and handed over as data — so there is no transcription
step between the verified output and the thing measured.

The interpreter is an **oracle and nothing else**; nothing that measures calls it.
`interp_expr`'s dictionaries are canonical sorted association lists, so an evaluator
extracted from it would have a linear insert and lookup, destroying the incrementality
the measurement exists to demonstrate. The evaluator is hand-written against the
denotations; the oracle checks that the hand did not slip.

Two mappings are unverified and belong in the paper's assumptions:

| Rocq | OCaml | why it matters |
|---|---|---|
| `Z` | `int` | sound while every integer stays in range; the generators keep them small |
| `string` | `string` | not cosmetic. Rocq's default extraction is a list of characters, which would make `OStrContains` and `OSubstring` linear in the wrong parameter and distort the substring subject |

## Reading the numbers

Two phases, reported separately by running the subject twice and subtracting. **build**
brings the table to its size — the insert queries where the table starts empty, the
one-off index build where it arrives in the environment, and which one a subject gets is
whether its source builds the structure or is handed it. **ops** is the queries, which is
what the optimizer is about.

Selectivity is the choice that matters. A read returning a constant fraction of the
table is linear however it is indexed, so every bucket in `gen.ml` grows with the table,
keeping bucket size bounded — the regime the originals' own callers are in.

Three op kinds break that on purpose, and `gen.ml` says so where it defines them.
`suggestMiss` and `suggestShort` ask the substring subject for a token no trigram can
serve, so the guarded read's **fallback** branch is what is measured; their optimized
exponent is deliberately linear. `suggestLong` takes five characters from the middle of
a name, giving three trigrams whose buckets differ by two orders of magnitude — without
it every generated token had exactly one trigram, and the rule that intersects all of a
pattern's buckets could not be told apart from taking the first.
