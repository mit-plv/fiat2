(* The counters the measurement is made of.

   Wall-clock time is reported alongside them by bench.ml, but it is not the
   evidence: it depends on the machine, on the allocator, on how hard OCaml's
   Map happens to work on a given shape, and above all on the fact that it is
   timing a tree-walking interpreter rather than any backend anyone would
   ship.  These counters depend on none of that.  What the seconds are good
   for is a check on the SHAPE: a read these counters call flat had better
   not take eight times longer on an eight-times-larger table.

   THERE IS ONE FIGURE AND THESE ARE ITS PARTS.  `work` is the sum of every
   counter below that represents work done, and the names exist so that the
   sum can be read rather than taken on trust -- not so that a table can
   quote one of them and leave the others out.  `data work` is the part of it
   that crosses to hand-written code.  Both are spelt out at the bottom of
   this file, with the argument for the split.

     comparisons  every entry into Value.compare, including the recursive
                  entries on sub-values.  This is where the cost of a
                  dictionary, bag or set operation lives: a probe into a
                  balanced tree is logarithmically many of them, a scan is
                  linearly many.  A string comparison counts as one, which is
                  honest only because the generators keep keys short; the one
                  subject whose keys are long strings (the trigram one) is
                  also the one where the counts are reported with that
                  caveat.

     hashing      value nodes walked in order to HASH a key, one per node,
                  by exactly the rule [comparisons] uses for the nodes walked
                  in order to compare one -- so a string is one unit on both
                  counters and a four-field record of scalars is five.  It is
                  the other half of what a key costs, and it exists because
                  the two sides of the author comparison were charged by
                  different rules: a tree descent paid a comparison per level
                  per node of the key, while a hash probe in baseline.ml paid
                  one flat unit however large the key was.  A whole-row key
                  made that gap 22x on item_deletion, almost all of it the
                  convention rather than the algorithm.

                  Charged on BOTH sides, so `comparisons + hashing` is one
                  figure for the work a structure does on keys, comparable
                  across a tree and a hash table.  Nothing that was counted
                  before is counted differently: every number this harness
                  used to print is still that number.

     strings      characters a string primitive examines or produces: the
                  positions a naive substring scan really compares, the bytes
                  a substring copies, the bytes a concatenation writes, the
                  digits an int-to-string emits.  It exists because the
                  dispatch of OStrContains is one step whatever the two
                  strings are, which made the one subject that is ABOUT string
                  matching the one subject whose characteristic cost was
                  invisible.  Charged on BOTH sides: baseline.ml's author scan
                  calls the same str_contains.

     fields       record fields a projection walks past before it reaches
                  the one it wants.  This is bounded by a constant of the
                  term rather than by the table, so it cannot bend an
                  exponent -- but a projection happens once per row of a
                  scan, so it is a real part of the constant, and leaving it
                  out was an assumption rather than a measurement.  It is
                  charged on both sides, and symmetrically: the workload
                  hands both columns the same VRecord association lists, and
                  baseline.ml's own accessor walks one the same way ours
                  does.  A backend would project by offset, which is as true
                  of the author's column as of ours -- the representation is
                  an assumption this comparison already rests on, and this
                  counter prices it instead of hiding it.

     overhead     work THIS INTERPRETER does that a compiled backend would
                  not: the comparisons a lookup or an insert into its map of
                  local names performs, and the comparisons that put a
                  record's fields into canonical order when one is built.  A
                  backend reads a local from a slot and lays a record out at
                  compile time, so neither is a cost the program implies.
                  It belongs with [steps]: counted, so the total is complete,
                  and kept out of the crossing figure, so the author
                  comparison stays about the two programs.  It is about the
                  same size as [steps] on most subjects, which is the
                  argument for naming it rather than folding it in.

     canonicalisations
                  every time a bag's canonical order had to be produced,
                  which is the only cost value.ml's unordered bag defers.
                  Zero means no subject ever observes it -- and it IS zero,
                  at every subject, phase and size, now that an emptiness
                  test no longer sorts the bag it is asking about.  The three
                  sites that used to fire were all an OEq against the empty
                  bag; two of them compared two EMPTY bags, so the counter was
                  recording an event that cost nothing.

     steps        a unit of interpreter work: one entry into interp_expr,
                  plus one for each element a primitive that is linear in
                  its argument has to walk.  A scan over a table of n rows
                  evaluates its body n times and shows up here; so does a
                  fold over an n-element bag, which evaluates nothing but is
                  no cheaper for it.  An index probe shows up in neither, so
                  the two counters separate the two things the optimizer is
                  claimed to trade against each other.

                  The linear primitives are OLength, ODictValues, OConcat,
                  ORange and the two aggregate folds.  Everything else is a
                  tree operation, whose cost is comparisons, or genuinely
                  constant: OBagOfList is free here because a bag is its
                  elements in any order, so a list already IS one.

     rows         the stored elements an operation ITERATES, counted once
                  per NESTING LEVEL that iterates them -- per iterating
                  construct in the term, that is, and nothing to do with the
                  phases of the optimizer, which this harness does not run
                  and does not measure.  A scan of n rows is n, a
                  probe that yields one row is 1, a membership test is 0
                  because it yields nothing, and a write is 0 because it
                  writes.  This is the counter that crosses the boundary to
                  hand-written code in baseline.ml, because it means
                  something there: `steps` counts entries into interp_expr
                  and has no analogue outside this interpreter.

                  "ONCE PER NESTING LEVEL" IS NOT "ONCE", and the difference
                  is worth knowing before a ratio in this column is believed.
                  An intermediate collection is not storage, but iterating
                  one is still counted, so a term can count the same rows
                  once for each construct they pass through.  window_store's
                  optimized fetchAll answers a window of 8 rows and reports
                  24, because it is

                    EACFold (AGCount,            <- walk n      = 8
                      EFlatmap (LikeBag,         <- visit n     = 8
                        EUnop (ODictValues,      <- walk 1 each = 8
                          ETernop (ODictRange,   <- 0: a split, charged to cmps
                            ...))))

                  where cluster's forTopic is EACFold over an EOptMatch of one
                  OLookup -- one iterating construct, a probe that charges no
                  rows, and so 8.  Both are FLAT in the table size (480 and
                  160 per 20 queries at 1600 rows, and at 800, and at 400):
                  the depth is a constant of the term, so the EXPONENT is
                  unaffected and the claims are stated as exponents.  The
                  constant is comparable between two forms of the same subject
                  when they have the same depth, and is NOT comparable against
                  hand-written code, which has no nesting levels to count --
                  which is why the author table flags its rows constant and
                  rests its claim on the exponent and on cmp+hash.

   Both are global and both are reset before each run.  Nothing in the
   evaluator reads them, so they cannot change what it computes. *)

(* ---------- which structures the run charges for ----------

   A point-access collection can be a balanced tree or a hash table, and the
   two cost different things: a tree pays comparisons on a descent, a hash
   table pays the key's hash and one equality.  Which one a program gets is a
   BACKEND's choice, not a property of the program, so it is a parameter of
   the run rather than a fact about either side.

   BOTH SIDES OF THE AUTHOR COMPARISON READ THIS ONE REF.  That is the whole
   point of it: a ratio between two programs means something only if their
   structures were chosen the same way.  Before it existed, our dictionaries
   were charged as hash tables because their type said Unranged while the
   originals' were charged as whatever the author happened to write, so the
   Kafka subject whose author chose a NavigableMap compared our hash against
   their tree and the number flattered us for a reason that had nothing to do
   with the optimizer.

   The three settings are three honest columns, not one right answer:

     Typed   what the type system licenses TODAY.  An Unranged dictionary is
             a hash table because dict_kind says so and ODictRange is
             untypeable at it; a set is a tree because no set_kind exists to
             say otherwise; the originals are charged as the author wrote
             them.  This is the only column whose every charge is backed by
             the type system, and it reproduces every number this harness
             printed before the parameter existed.

     Trees   everything a balanced tree, on both sides.  The conservative
             floor: no structure is assumed to hash.

     Hashes  a hash table wherever the semantics permits, on both sides --
             our sets included, which is what a set_kind would license, and
             the originals' ordered-but-never-range-queried maps included.

   What NO setting does is hash a structure whose operations read the key
   order: our Ranged dictionaries and the originals' range-queried maps are
   trees in all three, because a range query is not answerable otherwise. *)

type structures = Typed | Trees | Hashes

let structures = ref Typed

let structures_name = function
  | Typed -> "typed" | Trees -> "trees" | Hashes -> "hashes"

let structures_of_string = function
  | "typed" -> Some Typed | "trees" -> Some Trees | "hashes" -> Some Hashes
  | _ -> None

(* ---------- what a given structure is charged as ----------

   Ordered: a balanced tree.  A point access costs the comparisons its descent
            performs -- whatever Value.compare charges on the way down,
            measured and not estimated from a log.
   Hashed:  a hash table.  A point access costs the key's hash, by the same
            per-value-node rule comparisons uses, plus the one equality that
            confirms the bucket.

   NOTHING CHARGES EITHER ANY MORE: a collection holds the store its setting
   named, and the store's own comparisons and hashes are what the counters
   see, on both sides.  The three classifiers below are how a call site says
   which situation its structure is in; the choice is the claim being made
   about that structure, so each is written at the site rather than
   defaulted. *)

type kind = Ordered | Hashed

let kind_name = function Ordered -> "tree" | Hashed -> "hash"

(* The order is NEVER read, and something in the program says so: a dictionary
   whose type is TDict Unranged, at which ODictRange is untypeable, or an
   original the author wrote as a hash map.  Only the conservative floor
   declines the hash. *)
let licensed () : kind =
  match !structures with Trees -> Ordered | Typed | Hashes -> Hashed

(* The order happens not to be read, but NOTHING IN THE PROGRAM SAYS SO, so a
   backend could not make the choice from the type alone:

     - our sets.  TSet carries no kind, and TyESort_Set takes any set to a
       sorted list, so the type permits an order read even where the term
       performs none.  Adding a set_kind is what would move these to
       [licensed]; the Hashes column is what that would be worth.
     - an original whose author chose an ordered map but whose MODELLED
       operations never range-query it.  Kafka's NamedCache is the one: the
       real class needs the ordering for operations this subject does not
       model, so its Hashes row is a hypothetical about a smaller program and
       not a claim that the author chose badly.

   Typed therefore charges these as the trees they are stored in, and only
   Hashes hashes them. *)
let unlicensed () : kind =
  match !structures with Trees | Typed -> Ordered | Hashes -> Hashed

(* The order IS read: a TDict Ranged under ODictRange, or an original that
   calls subMap/headMap.  No setting hashes this, because a range query is not
   answerable from a hash table at all -- the parameter exists to stop the
   structure choice confounding the comparison, not to pretend a structure can
   do what it cannot. *)
let ordered : kind = Ordered

let comparisons = ref 0
let steps = ref 0
let canonicalisations = ref 0
let rows = ref 0
let hashing = ref 0
let strings = ref 0
let fields = ref 0
let overhead = ref 0

let reset () =
  comparisons := 0;
  steps := 0;
  canonicalisations := 0;
  rows := 0;
  hashing := 0;
  strings := 0;
  fields := 0;
  overhead := 0

(* n value nodes hashed *)
let hash (n : int) = hashing := !hashing + n

(* n characters examined or produced by a string primitive, and n record
   fields or environment entries walked past by a name lookup.  See the note
   on `work` below for why these exist separately from [steps]. *)
let chars (n : int) = strings := !strings + n
let field (n : int) = fields := !fields + n
let over (n : int) = overhead := !overhead + n

(* ---------- the total, and the part of it that crosses ----------

   THE PROBLEM THESE TWO SOLVE.  Every counter above answers a question about
   one kind of work, which is what makes them readable -- and it is also how a
   cost gets left out.  A primitive whose dispatch is one [step] and whose body
   walks a string was counted as one unit however long the string was; a record
   projection walking an association list was free.  Neither changed an
   exponent in this development, because the strings and the records are fixed
   by the generators and by the terms -- but nothing in the instrument said so,
   and "it did not matter here" is not something a reader can check.

   So `work` is the sum of EVERY counter that represents work done, and the
   named counters are its decomposition rather than a selection from it.  The
   invariant to keep is the one in eval.ml's dispatch: every operator states
   its cost, and the match that would have to be edited to add a new one is
   exhaustive, so a new operator cannot arrive costing nothing by default.

   [rows] and [canonicalisations] are deliberately NOT in the sum.  [rows] is a
   different view of work already counted (a [walk] charges both), and
   [canonicalisations] is an event counter whose value is zero -- adding either
   would double-count.

   WHY THE TOTAL CANNOT BE THE ONE NUMBER FOR THE AUTHOR COMPARISON.  [steps]
   counts entries into interp_expr, and hand-written OCaml does not have any:
   charging it to our side and to nothing on theirs would make the comparison
   a measurement of this harness.  `data work` is therefore the crossing
   subset -- everything the two sides both really do, on keys, on strings and
   on fields -- and it is a strict superset of the cmp+hash figure it
   replaces.  The gap between `work` and `data work` is the interpreter's own
   dispatch, named rather than hidden. *)

(* The two are IMPLEMENTED in bench.ml, as [total] and [crossing] over a
   differenced pair of readings, because every figure the tables print is the
   op phase with the build subtracted and a counter read here would be the
   wrong number.  They are written out once, here, where the parts are:

     work      = steps + overhead + comparisons + hashing + strings + fields
     data work =                    comparisons + hashing + strings + fields

   If a counter is added above and does not appear in one of those two, that
   is the bug this note exists to make visible. *)

(* Run [f] without charging its comparisons.

   One use only, through Keyed.access: a structure charged as a hash table is
   still STORED in a balanced tree, on both sides of the comparison and under
   every setting above (see the note in value.ml on why the representation and
   the charge are separate questions).  The tree descent inside is then the
   harness's own bookkeeping, not work the measured program does, so it is
   charged to neither counter: the key's hash is charged instead, by [hash].

   Restoring the count rather than muting a flag keeps this exact under
   nesting and leaves Value.compare with no branch in it. *)
let quiet (f : unit -> 'a) : 'a =
  let c = !comparisons and k = !canonicalisations in
  let r = f () in
  comparisons := c;
  (* a key holding a bag would canonicalise on the way down; no key in these
     subjects does, and restoring it costs nothing and keeps the suppression
     total rather than nearly total *)
  canonicalisations := k;
  r

(* a primitive that walks n elements without evaluating anything *)
let walk (n : int) =
  steps := !steps + n;
  rows := !rows + n

(* n stored elements inspected.  [walk] implies this; [visit] is for the places
   that inspect elements by evaluating something for each of them, which the
   step counter already sees but the row counter would otherwise miss. *)
let visit (n : int) = rows := !rows + n
