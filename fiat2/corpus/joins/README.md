# Is the nested-loop equijoin real code?

`Ex_Family` is a self-join we wrote, and its measured speedup is the largest in
the development: the scan form is quadratic (`a` = 2.00) and the indexed form is
constant. A number like that earns nothing unless the shape it comes from
occurs in code nobody wrote for us, so this directory is the search for it.

Two passes, because the first one was blind to the form the shape usually takes.

* `find_joins.py` — a `for` nested inside a `for`, with an equality inside the
  inner body relating a MEMBER of the outer variable to a MEMBER of the inner
  one. The condition is the discriminating test: a nested loop whose condition
  does not relate the two variables is not a join, and `a == b` is a duplicate
  check rather than an equijoin on an attribute. Neither is counted.
* `find_joins2.py` — the same shape with the inner loop written as a **stream
  or a generator**: `coll.stream().filter(b -> b.getY().equals(a.getX()))`,
  `any(b["y"] == a["x"] for b in coll)`, `[b for b in coll if b.y == a.x]`.
  Modern code writes joins this way far more often than as a nested `for`, and
  leaving it out would have made a low count a fact about the regex rather than
  about the corpora: the first pass found **nothing** in one corpus where the
  second found six.

Run as `python3 -I find_joins.py <corpus-root>`; the corpus root is an argument
so that no path is recorded here. The `.txt` files are the output, one per
corpus per pass, each hit printed with its file, line, the two loop sources and
the matched condition, so every one can be read and judged rather than trusted.

## What the output is, and is not

These are **candidates**, not findings. The search is regex over text, not a
parser: it does not know scope, so an inner loop found by look-ahead may not
really be inside the outer body; it cannot tell a collection from a fixed-size
array; and it cannot tell production code from a test. Judging is by hand, and
the judgements are below.

The counts are design input and do not belong in the paper — the standing rule
on frequency data applies here as it does to the other corpus searches.

## What survived reading, and why the rest did not

Rejected, with the reason:

* **test code** — most of the hits. Kafka's five nested-`for` hits are all in
  `src/test`; four of Keycloak's six stream hits are in `src/test`,
  `test-framework` or `test-stability`.
* **not a join.** Kafka's four `PersisterStateManager` hits are the same idiom
  four times: the inner collection is a nested collection OF THE OUTER ROW and
  the filter compares against `partitionKey()` on `this`, not against the outer
  loop variable. A nested-collection lookup with a constant key, flagged only
  because both variables appear on the line.
* **bounded outer.** Kafka's `NodeApiVersions` iterates a fixed enum set
  outside, so the cost is linear in data, not quadratic.
* **an inequality.** Kafka's `CustomStickyTaskAssignorTest` compares
  `!client1.processId().equals(client2.processId())` — an all-distinct-pairs
  check, not an equijoin.
* **component scale.** Home Assistant's eighteen hits are integration
  components joining a handful of devices or attributes against a per-device
  list; the collections do not grow with anything.
* **composite key on small collections.** Wagtail's `images/models.py` joins
  existing renditions against newly created ones on
  `(filter_spec, focal_point_key)`. A real equijoin, but both collections are
  bounded by the number of filters requested, and the key is composite, which
  is a limit of ours (`Surface.decl` names one attribute).

Three survived, and all three are production code whose cost grows with data.
They are ranked by how well each would serve as the subject:

| | site | shape | why | against it |
|---|---|---|---|---|
| 1 | netbox `dcim/svg/cables.py:265` | `for parent in parents: [t for t in terminations if t.parent_object == parent.object]` | a group-by inside a loop: single-attribute equality, both collections scale with the device drawn, served by the `DictIdx` we already have, and from a corpus we have drawn NO subject from | read-only, so it exercises no index maintenance |
| 2 | jenkins `core/.../PluginManager.java:1041` | `for (p : plugins) for (q : plugins) for (d : q.getDependencies()) if (d.shortName.equals(p.getShortName()))` | the most genuinely quadratic of the three -- `plugins` squared, and `plugins` is a maintained FIELD (`:325`), so an index would have to be maintained across install and delete | the join key is reached through a collection nested in a row, so it needs a side-table encoding; and Jenkins already supplies two of our subjects |
| 3 | zulip `zerver/data_import/slack.py:446` | `for field in fields: for v in values: if v["field"] == field["id"] and len(v["value"]) > 50: break` | the cleanest equijoin of the three -- one attribute, a residual filter, and `break` makes it an EXISTS; fresh corpus | the outer collection is the set of custom profile fields, which is small in practice, so the growth is really in one factor |

The recommendation is 1 with 2 beside it: the first is the clean illustration
from an unused corpus, and the second is the one that also exercises index
maintenance and is a true self-join, which is what `Ex_Family` is.
