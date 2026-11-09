# `src/fiat2` — what is where

Every dependency arrow points one way:

```
core  <-  rules/  <-  constraint/  <-  index/  <-  pipeline/  <-  examples/, eval/
```

`-Q src/fiat2 fiat2` makes each folder a logical sub-namespace, so a file in
`index/` is `fiat2.index.DictIndexImpl`.

## There is no single "compiler" file

Three stages, and it is worth knowing which is which before reading anything:

| stage | where | what it does |
|---|---|---|
| front end | `constraint/Surface.v` — `elab` | surface -> core. Inserts a guard at every write to a declared table. Applies **no** rewrite rule. |
| optimizer | `Pipeline.v` — `apply_all_transfs`, `apply_all_transfs_constrained` | core -> core. Applies a chosen list of rules and proves the result sound. |
| choice | `Selector.v` — `demands_of`, `choices_of` | decides *which* rules and indexes the optimizer is given. |

`elab` is 38 lines and is a structural recursion; the program that gets
measured is produced by `Pipeline`. The two factors of the constraint-check
speedup are split across the first two stages: elaboration collapses the
quantifier (O(n^2) -> O(n)) by emitting a class-specific guard, and an index
rule turns the remaining filter into a probe (O(n) -> O(1)).

## The layers

**core (flat, 11 files)** — the language and its metatheory. Read in this order:
`Language.v` (syntax), `Value.v`, `Interpret.v` (semantics), `TypeSystem.v`,
`TypeSound.v`; then `Utils.v`, `Substitute.v`, `StringFacts.v` (support) and
`TransfSound.v`, `TransfUtils.v`, `IndexInterface.v` (what a sound
transformation and an index are).

`TransfSound.v` is the one to read carefully: `parameterized_wf` and
`transf_sound` are the obligations every rule in `rules/` and `index/`
discharges.

**`rules/` (11)** — rewrite rules that mention no index. Each is a
`*_head` function plus `*_sound` / `*_preserve_ty` theorems.

**`constraint/` (5)** — declared constraints. `Constraint.v` is what a
constraint is; `PrimaryKeyCheck.v` and `CompositeKeyCheck.v` compile a declared
key to a probe (note they import no index implementation — they are
compilation, not indexing); `Decl.v` is the declaration language and the guards,
with the two theorems that make a class-specific guard safe; `Surface.v` is
`scommand`, `elab`, and the theorems that carry a declaration through a whole
program.

**`index/` (19)** — index implementations (`DictIndexImpl`,
`UniqueDictIndexImpl`, `CompositeDictIndexImpl`, `ListDictIndexImpl`,
`TrigramIndexImpl`, `RepIdx`, and the four aggregates `SetAgg`/`SumAgg`/
`MinAgg`/`CountAgg`) and the rules that read and maintain them.
`IndexTransf.v` is the generic driver.

**`pipeline/` (3)** — `Pipeline.v` (registry + driver + soundness),
`PruneDeadIndexes.v` (a top-level entry point of its own rather than a stage
of the default path: drop a choice nothing reads and re-run), `Selector.v`
(the demand analysis and the selection policy — a reviewer who wants only the
method can stop at `demands_of`).

**`examples/` (25)** — `Ex_*`. Small programs, each pinning a rule's output by
`Compute` or `reflexivity`.

**`eval/` (22)** — the measured subjects, the extraction, and
`Enumerate.v`, which generates every configuration the demand analysis admits
so measurement rather than policy decides.

## Build

```
make -j$(nproc)
```

No Makefile or `_CoqProject` edit is ever needed when adding a file or a
folder: `VFILES` is a recursive `find` and both are generated.
