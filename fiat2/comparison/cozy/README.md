# Against Cozy

Cozy (Loncaric, Ernst, Torlak; ICSE'18, *Generalized Data Structure Synthesis*) is the
nearest system to this one: it takes a specification of a collection with queries and
update operations and synthesizes an implementation, choosing representations and writing
the incremental maintenance code. It is the obvious thing to compare against, and this
directory is that comparison, run rather than described.

Two directions, because a one-directional comparison is the kind that gets discounted:

1. **Our subjects, as Cozy specifications.** The `.ds` files here. Each cites the eval
   subject it came from and records every encoding decision the spec language forced, so
   a reader can see what was assumed by hand rather than derived.
2. **Cozy's own benchmarks, in our language.** Their suite was chosen by someone else for
   someone else's paper, which makes it the better answer to "you picked the examples".
   The audit of what we can and cannot express is below.

Neither direction is free of asymmetry and the asymmetries run both ways. They are listed
rather than netted out.

## Reproducing

Cozy is not vendored. It is cloned and run with its own dependencies:

```
git clone https://github.com/CozySynthesizer/cozy     # at commit d7b2c0e
python3.9 -m venv venv && ./venv/bin/pip install -r cozy/requirements.txt
cd cozy && ../venv/bin/python -m cozy -t 60 --no-deduplicate-subqueries \
    --java Out.java <spec>.ds
```

Three notes on that command line, all three found by running it:

* **Python 3.9.** Cozy's `dictionaries==0.0.1` dependency uses `collections.Mapping`,
  which was removed in Python 3.10, so the tool does not start on a current interpreter.
* **`--no-deduplicate-subqueries`.** With the default settings, a specification whose
  predicate is an `extern` crashes Cozy's solver — `z3types.Z3Exception: ast is null`,
  raised from `solver.py:mkfunc` while `queries_equivalent` tries to build a model for an
  uninterpreted function. The flag avoids that code path. It is used for every spec here,
  not only the ones that need it, so that no two runs differ in their settings.
* **No wall-clock bound.** Cozy's `-t N` bounds its *search*, not its runtime. When the
  budget expires, `improve_implementation` asks each worker job to stop by setting a flag
  (`jobs.py:281`, `stop_jobs`), then loops `while jobs:` with no deadline and no
  `terminate()`. A worker that is not at a point where it checks the flag is waited on
  forever. On `named_cache.ds` at `-t 60` this happened: one worker
  (`ImproveQueryJob[_query2607]`, an internal maintenance subquery Cozy invented for
  `put`) spun at 100% CPU while the parent printed `Waiting on 1 jobs...` once a second,
  5,320 times — 89 minutes on a 60-second budget — and had to be killed. Where inside the
  worker it was stuck was not determined; the stop flag *is* checked inside the solver
  loop (`solver.py:1176`), so Z3 is not the obvious culprit. Every run here is therefore
  wrapped in an external wall-clock cap, `probes/cap.sh`, and any spec that needed the cap
  is marked as capped rather than reported as a result.

## Direction 1: our subjects, as Cozy specifications

Every run below is `-t 60 --no-deduplicate-subqueries` at the default cost model, under
the external cap, on one laptop core-set. **Cozy's paper reports runs of hours on 96
cores, so these are not Cozy at full strength**; where a longer budget was tried it is
said so explicitly.

"Ours" is the configuration `Selector.v` computes, not one written by hand.

| subject | ours | Cozy's state | the reads | the writes |
|---|---|---|---|---|
| `keycloak` | `UniqueDictIdx id`, `UniqueDictIdx alias`, `CountAgg` | `Integer` + 2 × `HashMap<String,Action>`, **no list** | O(1) each | — |
| `lookin` | `SetAgg name` | 1 × `HashMap<String,Boolean>`, **no list** | `containsKey` | spec has no ops |
| `item_deletion` | `TableRep LikeSet` | 1 × `HashMap<Item,Boolean>`, **no list** | `containsKey` | both O(1) |
| `user_search_find` | (`TrigramIdx` serves it) | `ArrayList` + `HashMap<String,User>` + `HashMap<User,Boolean>` + `ArrayList<String>` | O(1) by id | not inspected |
| `cluster` | `DictIdx topic`, `DictIdx leader` | 4 maps: 2 × `<String,List>`, 2 × `<Integer,List>` | bucket lookup | spec has no ops |
| `cluster_declared` | — (we cannot declare this) | **the same four maps** | `onePartition` = bucket lookup **then scan for the topic** | spec has no ops |
| `area_registry` | `KeyedDictIdx floor id` | 6 fields, incl. 2 × `<String,List<Area>>` and a `<Area,Boolean>` | `byId` O(1), `byFloor` bucket | `remove` = **978 lines, 38 full passes** over the list |
| `named_cache` | `UniqueDictIdx k`, `SumAgg size` | `ArrayList` + `Integer` + `<String,Node>` + `<Node,Boolean>` + 2 more | `sizeInBytes()` returns the maintained `Integer` | `delete` = **866 lines, 33 full passes**, and the total is **recomputed** (`_var335 = _sum2960`), not corrected |
| `window_store` | `RangedDictIdx time` | `ArrayList` + `<String,List<Record>>` + `<String,Boolean>` + `ArrayList<String>` | `fetch` = bucket lookup then **linear scan** of the time range; `fetchAll` = **full scan** | not inspected |
| `user_search_suggest` | `TrigramIdx fullName id` | 1 × `ArrayList<User>` | **"Number of improvements done: 0"** — the author's own `for` loop with `.contains(token)` | — |

What this says, in the order it matters:

**1. On reads, Cozy reaches our choice, and twice reaches it exactly.** `lookin` and
`item_deletion` come out as a single hash set with the list erased and the read a
`containsKey` — the same representation `SetAgg` and `TableRep LikeSet` produce, derived
independently. `keycloak` comes out as our `optimized_counted` including the maintained
count. These are the strongest *parity* results in the comparison and they should be
reported as parity, not spun: an independent system agreeing is evidence the selector's
heuristics are not arbitrary, which is the thing a reviewer doubted.

**2. The one subject that cannot be expressed is the one we win by 66x.** Cozy's language
has no string operations, so `suggest`'s substring predicate enters only as an opaque
`extern`, and with one Cozy reports zero improvements and emits the author's scan.

**3. Writes are where the two systems part, and the cause is identified, not guessed.**
`named_cache` is the clean case: Cozy maintains the total and answers `sizeInBytes` in
O(1), exactly as we do — then *recomputes the whole sum* in `delete` across 33 passes,
where our `delete_corrects_by_a_probe` pins a single probe. `area_registry/remove` is 38
passes. The cause is the default cost model, which has no maintenance term (below); this
is the prediction `--cost-model 3` tests, and a comparison that stopped here would be
unfair.

**4. The composite-key gap is narrower than claimed, and the honest version is better for
us anyway.** Cozy *can* declare `invariant unique [(p.topic, p.partition) | ...]`, which
`Surface.decl` cannot express. But declaring it changed Cozy's chosen state **not at all**
— `cluster.ds` and `cluster_declared.ds` produce the same four maps — and `onePartition`
is bucket-then-scan in both, which is what ours does. The invariant bought Cozy the
*query type* (a single row via `the`, instead of a stream), not a better representation.
So the limits table should say: we cannot state a composite key, and on this subject
stating it bought the state of the art nothing.

**5. Cozy derives redundant state.** Four maps for two bucketed reads on `cluster`, six
fields on `area_registry`, two identical `<String,List<Area>>` maps. We emit one record
with one field per index. Not measured, and storage is in its default cost model, so this
is an observation rather than a result.

Two asymmetries that run against this table, stated rather than netted out:

* **`cluster`, `cluster_declared` and `lookin` have no ops.** Cozy had no maintenance to
  pay for, so their parity is read-only parity. The subjects they came from do have a
  build phase.
* **Budget.** 60 seconds on a laptop against a tool whose paper used hours on a cluster.
  `window_store` was therefore re-run at `-t 600` specifically to test whether the ordered
  structure ever appears — Cozy registers a `TreeMultiset` by default
  (`structures/__init__.py:12`), so the scan in `fetch` is a choice its search did not
  revisit, not a missing capability.

## What Cozy does with a spec whose constraint can break

This is worth stating carefully, because it is the one place where Cozy's design is
*stronger* than ours in kind, and weaker in degree.

Cozy checks it. `invariant_preservation.py:32`, `check_ops_preserve_invariants`, runs
before any synthesis: for each op and each declared invariant it symbolically executes the
body (`mutate(a, m.body)`) and asks the solver whether `op's preconditions ∧ invariants ⟹
invariant[post-state]`. It also checks that every `the [...]` is singleton-or-empty
(`check_the_wf`), that `argmin`/`argmax` are non-empty (`check_minmax_wf`), and that each
query call satisfies the callee's preconditions (`check_calls_wf`). Any failure is an
`Error:` and `sys.exit(1)` (`main.py:93-101`) — the spec is **rejected**, not compiled.

Four probes, run rather than read (`probes/`, and `cap.sh` for the wrapper):

| probe | what it is | what Cozy does |
|---|---|---|
| `violate.ds` | `named_cache.ds` with the eviction dropped from `put`, so uniqueness is genuinely violable | `Error: 'put' may not preserve invariant (unique Map {n -> (n).k} (cache))`, refuses to synthesize |
| `assumed.ds` | the same op plus `assume not (node.k in [x.k | x <- cache])` | passes the check, synthesizes |
| `violate.ds --collection-depth 0` | the *violating* spec, verification bound shrunk | **accepted** — `Done!` — and synthesized |
| `violate.ds --no-invariant-preservation-check` | the violating spec, checking off | accepted; builds `HashMap<String,Node>` and emits `get` as `_var453.getOrDefault(key, ...)` — a unique-key map on a key that is not unique |

So the guarantee is **bounded model checking, not proof**. `solver.valid(e)` is
`not satisfiable(not e)` (`solver.py:1270`) over models in which every collection holds at
most `--collection-depth` elements, default 4 (`solver.py:31`, whose own description reads
"Bound for bounded verification"). Acceptance means "no counterexample within the bound".
The third probe shows that this bound is load-bearing rather than theoretical: the same
false invariant is accepted at depth 0 and rejected at depth 1, 2 and 4 — uniqueness needs
only two rows to break, so a small bound suffices *here*, but an invariant whose smallest
counterexample is larger than the bound is accepted silently. To Cozy's credit it raises
`SolverReportedUnknown` rather than assuming validity when Z3 returns `unknown`
(`solver.py:1183`).

The fourth probe is the consequence. With the check disabled, the declared invariant is
still fed to the synthesizer as a solver assumption (`high_level_interface.py:160`), so
Cozy derives a representation that is correct *only* under an invariant nothing
established, and the resulting `get` silently answers with one of the two rows sharing a
key. Nothing in the emitted Java records that it depends on an unchecked claim.

**Where this leaves the comparison.** Both systems take the constraint as a *hypothesis*
and neither verifies it against the application that will call the data structure — the
honest statement of the shared limitation. The difference is what the hypothesis buys and
what it costs:

* Cozy checks preservation of the invariant by the ops, which we do not do at all, and
  reports a violation before wasting synthesis time on it. That check is bounded at four
  elements and can be switched off.
* Our declared constraints are discharged in Rocq, unbounded, and the rewrite that turns a
  declared key into a single index probe is a *proved* equivalence rather than a solver
  query — but the constraint itself is assumed of the input, and an op that breaks it is
  not detected. A write whose precondition is the declared check elaborates to a guard
  (`classify_write`), so uniqueness is enforced at runtime where the source enforced it;
  it is not established statically.

Neither of those is obviously the better engineering choice, and the paper should say so
rather than claim the stronger position.

## Cozy's cost model, and the setting this comparison must use

Found while writing `named_cache.ds`, and it corrects an earlier note in that file.
`--cost-model` (`cost_model.py:21`) selects among four, default **2**, which orders
candidates by asymptotic query runtime, then maximum storage size, then exact query
runtime, then expression size: **no state-maintenance term**. Mode **3** adds one
`maintenance_cost(e, op)` per op (`:209-212`), but ranked *below* asymptotic query runtime
and unprioritized among the ops, so it breaks ties rather than driving the choice.

Our subjects whose difficulty is in a write — `named_cache` above all, where the wrong
choice costs 752x on the delete and takes the build from linear to quadratic — must
therefore be run at **both** settings, and the table must say which. Reporting only the
default would be the easy win and the dishonest one.

## Direction 2: their benchmarks in our language

Cozy ships 20 example specifications, five of them derived from real applications. What
we can express:

| their spec | expressible for us? | what decides it |
|---|---|---|
| `ztopo-cache` (ZTopo) | **yes**, with encodings | an enum becomes an int, a handle update becomes a delete and an insert; the unique key, the two filtered sums and the point lookup are all directly ours |
| `sat4j-literal-storage` (Sat4j) | **yes**, with encodings | same two encodings, plus `Native` field types that nothing reads becoming opaque strings; a unique key, `the`-lookups on it, and a `len` |
| `select-flatmap`, `listcomp-flatmap` | **yes** | value-typed records and several state collections, with an equality join written as nested comprehensions -- which is a shape no subject of ours currently has |
| `graph` | **yes** | two collections, a count aggregate keyed on an attribute |
| `basic`, `agg`, `map`, `in`, `intset`, `maxbag`, `argmin` | **yes** | the small ones; `maxbag`/`argmin` want the min/max aggregate, which we have and no third-party subject of ours witnesses |
| `lobsters` (Lobsters) | **no** | collections nested inside rows (`hidden_to_users : Bag<HiddenToUser>` inside a `Story`) |
| `clausedb` (MiniSat) | **no** | `Set<Set<Bound>>`; a collection of collections |
| `openfire-roster` (Openfire) | **no** | tuple-valued state used as a relation (`Set<(Group, User)>`), plus queries that call other queries |
| `redmine` (Redmine), `tpchq5` (TPC-H Q5) | **no** | rows holding REFERENCES to other rows, chased in the query (`i.val.supplier.val.nation.val.region.val.name`); we have no reference type |
| `lsort`, `polyupdate`, `nested-map`, `disjunction`, `rot1`, ... | mixed | sorted-order queries and indexing into a sorted result are out; the rest are small shapes we have |

So **two of their five application-derived specifications are expressible**, and the three
that are not fail for one of two reasons: a row that holds a reference to another row, or
a collection nested inside a row. Both are honest limits of our language and neither is a
limit of the rewriting; they are now in the limits table in `src/fiat2/eval/README.md`.

The two that are expressible are worth more than their count, because they are subjects
**we did not choose**: a cache with two filtered sums over an enum-valued state, and a
literal store with a unique key and six lookups through it. The join-shaped pair is worth
more still, since no subject of ours has two interacting collections.

## The axis that needs no measurement

| | Cozy | here |
|---|---|---|
| input | a specification, written by hand; its own case studies required reverse-engineering and refactoring the applications | the imperative program, with no ADT boundary to extract |
| the bag relaxation | the spec writer declares `Bag` or `Set` | derived from what the queries observe, and proved (`AnnotateCollection`, `PushdownCollection`) |
| correctness | a Z3 check at **bounded** collection depth (`--collection-depth`, default 4), plus the applications' own test suites | whole-program semantic preservation, proved in Rocq for any input, 1,250 lemmas, no holes |
| composite keys | `invariant unique [(p.topic, p.partition) \| p <- partitions]`, and a map built on the pair | **not expressible**: `Surface.decl`'s `DUnique` names one attribute, and `DRow`/`DCheck` read a single row, so no cross-row declaration about a pair can be made |
| string predicates | **not expressible**: the operator table is arithmetic, comparison and boolean, and the unary operators are sum/not/distinct/unique/all/any/exists/len/empty/the/reversed. A substring test can enter only as an opaque `extern` | `OStrContains`, and a trigram index derived from the structure of the predicate |
| cost model | static and symbolic, and documented as ignoring state-maintenance cost | measured; and the three hazards where maintenance decides the answer are pinned and costed (`main.exe alternatives`) |
