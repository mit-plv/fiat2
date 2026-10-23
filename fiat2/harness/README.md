# Harness

The OCaml side of the evaluation. Nothing in here is verified, and nothing in here is
meant to be: it consumes terms the Rocq development produced and measures them.

## Layout

    generated/      extracted by src/fiat2/eval/Extract.v -- not checked in
    main.ml         a report over the extracted terms; see below
    dune, dune-project

## Building

    make            # from the repository root: compiles the Rocq development and,
                    # as part of it, writes generated/ast.ml and generated/ast.mli
    dune build      # from this directory
    ./_build/default/main.exe

The extraction is part of the ordinary Rocq build, so `generated/` is derived and
gitignored. `dune build` before a `make` fails with a missing module, which is the
intended failure.

## What crosses the boundary

The abstract syntax, and each subject program twice -- before and after the optimizer --
plus the five alternative configurations the subject files pin and argue about. Each term
is the normal form of the very definition its own file's soundness theorem is about,
reduced by `vm_compute` and handed over as data, so there is no transcription step between
the verified optimizer's output and the thing that gets measured.

**Not** the interpreter. The Gallina `interp_expr` is the specification of the semantics,
not a source to derive an implementation from: its dictionaries are canonical sorted
association lists, so extracting it would produce an evaluator in which every insert and
every lookup is linear, destroying the incrementality the measurement exists to
demonstrate. The evaluator is written by hand against the denotations.

Two mappings are unverified and belong in the paper's assumptions beside the choice of
persistent maps:

| Rocq | OCaml | why it matters |
|---|---|---|
| `Z` | `int` | sound while every integer in a run stays in range; the generators keep them small |
| `string` | `string` | not cosmetic. The default extraction of a Rocq string is a list of characters, which would make `OStrContains` and `OSubstring` linear in the wrong parameter and distort the substring subject specifically |

## What `main.ml` does today

It walks the terms and reports their shape: node counts before and after, which index
operators the optimizer introduced, the field names of the record each table is bound to,
and the number of `ESort` occurrences anywhere (zero -- the asymptotic argument leans on
no subject paying for a canonical materialisation, so it is checked rather than asserted).

The field names are the part worth keeping. Each subject's Rocq file already pins them by
`vm_compute`, so OCaml agreeing is a check on the **extraction**: it says the term that
crossed the boundary is the term the theorems are about. All eight agree.

It found one thing on its first run that the Rocq files had not recorded -- that splitting
the conjunction in the window-store subject erases its list and reduces retention to an
incremental restriction. That is now pinned in Rocq, where it belongs.

## Next

The evaluator, with persistent `Map`/`Set` so that a dictionary insert is logarithmic and
not a copy, and generators parameterised by row count.
