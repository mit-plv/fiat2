# Raw measurement outputs

Produced by `../reproduce.sh`, which records in each file the exact command
that wrote it. Every table in the paper should be traceable to a file here and
every file to one command.

**Prerequisite:** `make` at the repository root first. The harness consumes
terms extracted by the Rocq build.

## Which files are regression tests

The tiers are drawn by **what is in the file**, not by what the table is for.

`./reproduce.sh counted` writes the six files that contain nothing but
counters. The counters are exact and deterministic, so on an unchanged tree
those six reproduce **byte for byte** — a non-empty `git diff` means the
development changed, and that is the intended use. Verified by running the
tier twice and diffing.

`./reproduce.sh compare` writes the three author comparisons. Each of their
rows carries a counted column *and* a seconds column, which is the point of
them — so the file never diffs clean even though every counted figure in it
is stable. That distinction was found by the check rather than by reading the
script: these three were filed under `counted` at first, and the twice-and-diff
run is what said otherwise.

`./reproduce.sh timed` writes the files that are about seconds. They never
reproduce themselves; they are evidence that a counted result also shows up on
a clock, not quantities to diff.

| tier | files | byte-stable |
|---|---|---|
| `counted` | `settings-all-subjects`, `src-vs-opt-fuzzy`, `rule-by-rule`, `residual-breakdown`, `alternatives`, `enumerate` | yes |
| `compare` | `author-scan-fuzzy`, `fair-baseline-fuzzy`, `fair-baseline-user-search` | counted columns only |
| `timed` | `residual-seconds`, `seconds-per-read-kind` | no |
| `checks` | `check-differential`, `check-compiled` | yes |

## What answers what

| claim | file | the number |
|---|---|---|
| the optimizer is sound on real inputs | `check-differential.txt` | 1230 configurations, 0 mismatches |
| and so is the compiled backend, at every storage | `check-compiled.txt` | 4 checks x 3 settings, 0 failures |
| every configuration the demand analysis admits is sound, witnessed per program rather than argued | `enumerate.txt` | 864 configurations x 3 settings = 2592 runs, every one producing the selector's final store |
| the configuration is not hand-picked: it wins a measurement against all of them | `enumerate.txt` | cheapest on 20 of 23 at `typed`, 21 at `trees`, 22 at `hashes` |
| what the pick is worth against the alternative each subject file pins by hand | `alternatives.txt` | 18 pairs over 9 subjects; an alternative wins some row in 7, and loses nothing in exactly one |
| no performance claim hides a pathology at an unmeasured storage | `settings-all-subjects.txt` | 23 subjects x 3 settings; only `min_delete` (12x) and `fuzzy_search` (2.05x) are sensitive |
| faster than the query AS WRITTEN, with no index | `src-vs-opt-fuzzy.txt` | reads 19.2x / 13.8x / 2.31x at share=2 / 128 / 2048; **and the build phase 8.6-9.5x**, which is the declared primary key compiling to a probe instead of a scan |
| faster than the author's OWN code | `author-scan-fuzzy.txt` | 14.7x / 7.7x less work, parity (1.06x) at share=2048 |
| the FAIR baseline: the same author, given a hand-built GIN | `fair-baseline-fuzzy.txt` | opt/gin 13.1x / 4.7x / 2.7x; **writes 1.10-1.54x** |
| substring search reaches parity with that baseline | `fair-baseline-user-search.txt` | 0.71-1.25x over five read kinds; writes 1.69x |
| what each rule change is worth, and what the language cannot say | `rule-by-rule.txt` | the two hoists 1.38-2.55x; `ordered` = `gin` to the digit under `trees` (the set->list coercion is free on a tree); `scatter` WORSE than what we emit |
| which kind of work the residual is | `residual-breakdown.txt` | at `typed` we pay comparisons and the transcription pays hashing -- a tree against a hash; at `trees` the residual is 1.44x |
| and the residual is in the clock too | `residual-seconds.txt` | opt/rechecked 2.41s at `typed`, **1.50s at `trees`** against 1.45 counted |
| per read kind, in seconds | `seconds-per-read-kind.txt` | `searchMiss` 235x at share=2048, where the index short-circuits and the scan cannot |

## Caveats that belong with the numbers

**Trust the counters at a factor and the seconds at an order of magnitude.**
At a point read both columns take about 200ns, where the clock measures how a
column happens to be written. The one exception is `residual-seconds.txt`,
which uses one op count per cell satisfying every column with the ops phase
required to dominate the build -- scaling each column to its own count is what
biased an earlier table by 29-88%.

**Do not compare the `rows` column across our column and a transcription.** A
transcription charges one row per probe that YIELDS a row and none for a
membership test (baseline.ml's kprobe convention). The 15442.6 against 4.2 in
`residual-breakdown.txt` is that convention, not rows touched.

**The `remove` row means two different things in two files.** In
`author-scan-fuzzy.txt` the author maintains only their primary-key map and is
charged nothing for the four GIN indexes Postgres maintains, so that column is
not a result. In `fair-baseline-fuzzy.txt` the author maintains the same
postings we do, so it is.

**The ranking in `enumerate.txt` is a function of the op mix, not a property of
the configurations.** The objective is total counted work at the top size with
`ops_per_kind = 20`, so it prices a build against twenty operations of each
kind. `user_search` is where that bites: declining the trigram index builds
8-11x cheaper and makes every read 2x worse, which the objective scores as a
1.1-1.2x win at `typed` and `trees` and a tie at `hashes`. Read the build and
ops columns before believing any verdict line -- the file prints them
separately for exactly this reason.

**Winning a row is not winning.** In 7 of the 18 pairs an alternative beats
the selector's pick on some row, and in 6 of those it pays for it elsewhere by
more than it gained: `cluster/composite` serves `onePartition` 2.8x cheaper and
`available` **259x** dearer; `entity_registry/split-dicts` builds 1.4x cheaper
and answers `getEntityId` **45.9x** dearer. Those are the rule-ordering hazards
with numbers on them, and they are why both instruments still score those
subjects as the selector's. Read a pair's whole block, never one row.

**`alternatives.txt` and `enumerate.txt` are independent, and they agree on one
subject.** The first measures 18 counterfactuals written by hand in the subject
files; the second enumerates every configuration the demand analysis admits.
`min_delete/dictmin-erased` is the only pair in which the alternative loses
nothing -- 1.6x cheaper build, 40x cheaper `deleteMin` (33748 against 828), 1.8x
cheaper `deleteOther`, and `readMin` a tie -- and the enumeration reaches the
same subject at all three storages (1.5-1.7x), the only loss that survives
every setting. `MinAgg` there is maintained by every write and never pays a read
back. By `alternatives.txt`'s own header -- "the alternative winning a row would
be a selector bug, not a caveat" -- that is a policy mistake rather than a
measurement artifact, and it is the one thing two different methodologies both
found.

**All figures are at 6,400 rows** unless the command says otherwise, and
`share=K` sets how many rows share a title prefix -- the parameter the sign of
the comparison depends on.

## Not generated here

`./reproduce.sh slow` writes the write-fraction sweep, the scale ladder to
25,600 rows, the stationarity check and the matched-storage table. They take
hours, mostly because `dependent_plugins`' source form is quadratic, so they
are left to an explicit run rather than committed.
