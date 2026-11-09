# How a number in the paper is produced

One worked example, end to end. The subject is `keycloak`, because it is a real
program with a real author and exercises the declared-key path.

## 0. The original

`keycloak`, commit `dd4ae31d`, `CachedRealm.java:301`, with its reads at
`RealmAdapter.java:1572` and `:1579`:

```java
requiredActionProviderList = model.getRequiredActionProvidersStream().collect(toList());
for (RequiredActionProviderModel action : requiredActionProviderList) {
    requiredActionProviders.put(action.getId(), action);
    requiredActionProvidersByAlias.put(action.getAlias(), action);
}
```

One list and two maps over it, keyed on two different unique attributes. The
callers resolve to two point lookups and one whole-list read.

## 1. Transcription — `src/fiat2/eval/Keycloak_CachedRealm.v`

Written by hand in the surface language, and the file states the source commit
and line, the pattern it instantiates, the claim it supports, and — in a
**Faithfulness** section — what the translation drops and why. The source form
keeps **one plain list**: the author's two maps are deliberately removed, so
what is measured is "declarative with no index" against "compiler-indexed".

The two keys are *declared*, not hand-maintained:

```coq
Definition decls := [DUnique "id"; DUnique "alias"].
```

This is the step nothing checks, and the one the paper has to be honest about.

## 2. Elaboration — `src/fiat2/constraint/Surface.v`

`elab` turns the surface program into a core `command`, inserting a guard at
every write to a declared table. For a `DUnique` the guard is a filter of the
table on the key attribute compared against the empty bag — an O(n) scan.
`elab_constr_wf` proves the elaborated program maintains every declaration.

## 3. Hints — `src/fiat2/pipeline/Selector.v`

`CAC cenv depth basics choices icss` names the basic rewrites and the index
choices. `Selector.v` *computes* them from the program (`demands_of`,
`choices_of`) rather than being told; subject files write them out so the file
can argue about alternatives. Hints are only hints: pipeline soundness is
quantified over them with no side condition.

## 4. Optimization — `src/fiat2/pipeline/Pipeline.v`

`apply_optimize_anno_constrained`, in execution order: the basic rewrites, the
declared table's index installation, the unconstrained index layer, taking back
collection coercions no index absorbed, then erasing a table's list where
nothing reads it.

## 5. Soundness — the same file

`elab_apply_optimize_anno_constrained_sound` gives well-typedness and an
`interp_command` equality between the optimized and elaborated programs, from
surface-level premises only. Each subject instantiates it as `optimized_sound`.
**This is the whole of what is verified.** It says the output computes what the
input computes; it says nothing about speed.

## 6. Shape pins — the same file, by `vm_compute`

What the optimizer actually emitted, asserted term-for-term:
`installs_both_maps`, `id_read_is_a_probe`, `alias_read_is_a_probe`,
`guard_is_two_probes` (each declared key's write check became one dictionary
probe instead of a scan), `write_is_incremental`, `counted_erases_the_list`.
These are the claims about *what* the compiler did; §9 measures what it was
worth.

## 7. Extraction — `src/fiat2/eval/Extract.v`

```coq
Definition keycloak_src : command := Eval vm_compute in KC.elaborated KC.decls.
Definition keycloak_opt : command := Eval vm_compute in KC.optimized_counted.
... [ ("keycloak", keycloak_src, keycloak_opt) ; ... ]   (* 23 subjects *)
```

Each term is the **normal form of the very definition the soundness theorem is
about**, handed over as data — so nothing is transcribed between the verified
output and the thing measured. `ExtractAll.v` writes `harness/generated/`.

## 8. Workload — `harness/gen.ml`

One spec per subject: the query mix, the sizes, and the data. Selectivity is the
design choice — every bucket grows with the table, so a read returns a bounded
number of rows, which is the regime the original's own callers are in.

## 9. Measurement — two instruments

| | files | what it gives |
|---|---|---|
| interpreted | `value.ml` `eval.ml` `count.ml` `bench.ml` | exact, deterministic counters |
| compiled | `mono.ml` `codegen.ml` `rt.ml` `compiled/` | seconds |

`count.ml` defines the counters and the one figure `work` they sum to; `data
work` is the subset that crosses to hand-written code. Counters are the evidence
for shape and, being deterministic, double as a regression test. Seconds are
evidence that a counted result also shows up on a clock.

Every command of either instrument takes a **structure setting** — `typed`,
`trees`, `hashes` — applied to both sides at once. A claim is not finished until
its subject is measured under all three.

## 10. The author comparison — `harness/compiled/authors.ml`

The original's *own* data structures, transcribed, each citing its file and
line. The expected result is **parity**: the compiler is supposed to arrive back
at the structure the author built, so matching asymptotics is the positive
result and a large win would mean one of the two is not what it claims to be.

## 11. Checking the harness itself

`differential.ml` runs the hand-written evaluator against the extracted Gallina
interpreter — the interpreter is an oracle and nothing that measures calls it,
because its dictionaries are sorted association lists and would destroy the
incrementality being demonstrated. `probe.ml` checks the dictionary store
against a reference map.

## 12. Output — `harness/reproduce.sh` → `harness/results/`

Each file records the command that produced it. `results/README.md` maps each
claim to its file. Tiers: `checks`, `counted` (byte-stable, six files),
`compare` (counted *and* seconds columns), `timed`, `slow`.

## The boundary, stated plainly

**Verified:** the optimized program computes what the elaborated one computes,
and the elaborated one maintains its declarations. Plus, by `vm_compute`, the
exact shape of what was emitted.

**Not verified, and these belong in the paper's assumptions:** the transcription
from Java to the surface language; the cost model in `count.ml`; the workload in
`gen.ml`; the author transcriptions in `authors.ml`; and two extraction
mappings — `Z` to `int` (sound while integers stay in range) and `string` to
`string` (not cosmetic: Rocq's default extraction is a character list, which
would make `OStrContains` linear in the wrong parameter).

The chain is arranged so the unverified parts are *inputs and instruments*, never
steps between the verified output and the measured term.
