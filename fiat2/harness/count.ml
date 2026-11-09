(* The counters the measurement is made of.

   THERE IS ONE FIGURE AND THESE ARE ITS PARTS.  `work` is the sum of every
   counter that represents work done; the names exist so the sum can be read
   rather than taken on trust, not so a table can quote one and omit the rest.
   `data work` is the part that crosses to hand-written code.  Both are spelt
   out at the bottom of this file.

     comparisons  every entry into Value.compare, including recursive entries
                  on sub-values.  This is where a dictionary, bag or set
                  operation's cost lives: a tree probe is logarithmically many,
                  a scan linearly many.  A string comparison is one of these
                  plus the characters examined, which go to [strings].

     hashing      value nodes walked to HASH a key, one per node, by the rule
                  [comparisons] uses for nodes walked to compare one -- so a
                  string is one unit on both and a four-field record of scalars
                  is five.  Charged on BOTH sides, so `comparisons + hashing`
                  is one figure for key work, comparable across a tree and a
                  hash table.

     strings      characters a string primitive examines or produces: the
                  positions a naive substring scan compares, the bytes a
                  substring copies or a concatenation writes, the digits an
                  int-to-string emits, and the bytes a string KEY costs a
                  structure (the shared prefix a comparison stops at, or the
                  whole length when a hash walks it).  Without it the one
                  subject that is ABOUT string matching had its characteristic
                  cost invisible, since OStrContains dispatches in one step
                  whatever its arguments.  Charged on both sides.

     fields       record fields a projection walks past.  Bounded by a
                  constant of the term, so it cannot bend an exponent, but a
                  projection happens once per row of a scan and so is a real
                  part of the constant.  Both columns are handed the same
                  VRecord association lists.

     overhead     work THIS INTERPRETER does that a backend would not: the
                  comparisons of its local-name map, and those that put a
                  record's fields in canonical order when one is built.  Kept
                  out of the crossing figure so the author comparison stays
                  about the two programs.  About the size of [steps] on most
                  subjects, which is why it is named rather than folded in.

     canonicalisations
                  every time a bag's canonical order had to be produced, the
                  only cost value.ml's unordered bag defers.  It is zero at
                  every subject, phase and size.

     steps        one entry into interp_expr, plus one per element a primitive
                  linear in its argument walks.  A scan over n rows evaluates
                  its body n times and shows up here; so does a fold over an
                  n-element bag, which evaluates nothing and is no cheaper.  An
                  index probe shows up in neither, so the two counters separate
                  the things the optimizer trades.

                  The linear primitives are OLength, ODictValues, OConcat,
                  ORange and the two aggregate folds.  Everything else is a
                  tree operation, whose cost is comparisons, or constant:
                  OBagOfList is free because a list already IS a bag.

     rows         stored elements an operation ITERATES, counted once per
                  NESTING LEVEL that iterates them -- per iterating construct
                  in the term, nothing to do with the optimizer's phases, which
                  this harness does not run.  A scan of n rows is n, a probe
                  yielding one row is 1, a membership test is 0 (it yields
                  nothing), a write is 0.  This is the counter that crosses to
                  baseline.ml, because [steps] has no analogue outside this
                  interpreter.

                  "ONCE PER NESTING LEVEL" IS NOT "ONCE", and the difference
                  matters before a ratio in this column is believed: a term can
                  count the same rows once per construct they pass through.
                  window_store's optimized fetchAll answers a window of 8 rows
                  and reports 24 (count over flatmap over dict-values, three
                  iterating levels), where cluster's forTopic reports 8 (one
                  level over a probe).  Both are FLAT in table size, so the
                  EXPONENT is unaffected and the claims are stated as
                  exponents.  The constant is comparable between two forms of
                  the same subject at equal depth, and NOT comparable against
                  hand-written code, which has no nesting levels to count --
                  which is why the author table flags its rows constant and
                  rests on the exponent and on cmp+hash.

   All are global and reset before each run.  Nothing in the evaluator reads
   them, so they cannot change what it computes. *)

(* ---------- which structures the run charges for ----------

   A point-access collection can be a balanced tree or a hash table, and the
   two cost different things: a tree pays comparisons on a descent, a hash
   table pays the key's hash and one equality.  Which one a program gets is a
   BACKEND's choice, so it is a parameter of the run rather than a fact about
   either side.

   ALL FOUR COLUMNS READ THIS ONE REF -- value.ml's dstore and sstore for the
   interpreted pair, Rt.SelMap and Rt.SelSet for the compiled pair.  That is
   the point of it: a ratio between two programs means something only if their
   structures were chosen the same way.

   The three settings are three honest columns, not one right answer:

     Typed   what the type system licenses today.  An Unranged dictionary
             hashes because dict_kind says so and ODictRange is untypeable at
             it; a set is a tree because no set_kind exists to say otherwise;
             the originals are charged as the author wrote them.  The only
             column whose every charge is backed by the type system.
     Trees   everything a balanced tree, both sides.  The conservative floor.
     Hashes  a hash table wherever the semantics permits, both sides -- our
             sets included, which is what a set_kind would license.

   NO setting hashes a structure whose operations read the key order: our
   Ranged dictionaries and the originals' range-queried maps are trees in all
   three, because a range query is not answerable otherwise. *)

type structures = Typed | Trees | Hashes

let structures = ref Typed

let structures_name = function
  | Typed -> "typed" | Trees -> "trees" | Hashes -> "hashes"

let structures_of_string = function
  | "typed" -> Some Typed | "trees" -> Some Trees | "hashes" -> Some Hashes
  | _ -> None

(* ---------- what a given structure is charged as ----------

   A collection HOLDS the store its setting named, and the store's own
   comparisons and hashes are what the counters see, on both sides.  The three
   classifiers below are how a call site says which situation its structure is
   in. *)

type kind = Ordered | Hashed

let kind_name = function Ordered -> "tree" | Hashed -> "hash"

(* The order is NEVER read, and something in the program says so: a TDict
   Unranged, at which ODictRange is untypeable, or an original the author
   wrote as a hash map.  Only the conservative floor declines the hash. *)
let licensed () : kind =
  match !structures with Trees -> Ordered | Typed | Hashes -> Hashed

(* The order happens not to be read, but NOTHING IN THE PROGRAM SAYS SO:

     - our sets.  TSet carries no kind and TyESort_Set takes any set to a
       sorted list, so the type permits an order read where the term performs
       none.  A set_kind is what would move these to [licensed]; the Hashes
       column is what that would be worth.
     - an original whose author chose an ordered map but whose MODELLED
       operations never range-query it.  Kafka's NamedCache is the one: the
       real class needs the ordering for operations this subject does not
       model, so its Hashes row is a hypothetical about a smaller program, not
       a claim that the author chose badly. *)
let unlicensed () : kind =
  match !structures with Trees | Typed -> Ordered | Hashes -> Hashed

(* The order IS read: a TDict Ranged under ODictRange, or an original calling
   subMap/headMap.  No setting hashes this -- the parameter exists to stop the
   structure choice confounding the comparison, not to pretend a structure can
   do what it cannot. *)
let ordered : kind = Ordered

(* ---------- what a call site CLAIMS about one structure ----------

   The classifiers above answer "what does this setting charge an
   Ordered/Hashed structure".  The compiled columns need it the other way
   round: a generated set or a transcribed HashMap picks a storage when it is
   created, decided by the setting together with one claim about THAT
   structure.  The claim is named here, beside the settings it resolves
   against, so there is exactly one copy of the vocabulary.

   Writing the claim at the site is deliberate: it is the one part that is a
   judgement rather than a measurement. *)

type situation = Licensed | Unlicensed | NeedsOrder

let kind_of : situation -> kind = function
  | Licensed -> licensed ()
  | Unlicensed -> unlicensed ()
  | NeedsOrder -> ordered

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

(* n characters examined or produced by a string primitive; n record fields or
   environment entries walked past. *)
let chars (n : int) = strings := !strings + n
let field (n : int) = fields := !fields + n
let over (n : int) = overhead := !overhead + n

(* ---------- the total, and the part of it that crosses ----------

   Every counter above answers a question about one kind of work, which is what
   makes them readable -- and is also how a cost gets left out.  So `work` is
   the sum of EVERY counter representing work done, and the named counters are
   its decomposition rather than a selection from it.  The invariant to keep is
   eval.ml's: every operator states its cost, and the match that would have to
   be edited to add one is exhaustive, so a new operator cannot arrive costing
   nothing by default.

   [rows] and [canonicalisations] are deliberately NOT in the sum.  [rows] is a
   different view of work already counted (a [walk] charges both) and
   [canonicalisations] is zero; adding either would double-count.

   [steps] counts entries into interp_expr, which hand-written OCaml does not
   have, so charging it to our side and nothing to theirs would make the author
   comparison a measurement of this harness.  `data work` is the crossing
   subset.  The gap between the two is the interpreter's own dispatch, named
   rather than hidden.

   Both are implemented in bench.ml, as [total] and [crossing] over a
   differenced pair of readings, because every figure the tables print is the
   op phase with the build subtracted.  Written out once, here, where the parts
   are:

     work      = steps + overhead + comparisons + hashing + strings + fields
     data work =                    comparisons + hashing + strings + fields

   A counter added above and absent from both is the bug this note exists to
   make visible.

   There is no suppression anywhere in this file: every counter is incremented
   by a primitive actually doing the work it charges for. *)

(* a primitive that walks n elements without evaluating anything *)
let walk (n : int) =
  steps := !steps + n;
  rows := !rows + n

(* n stored elements inspected.  [walk] implies this; [visit] is for places
   that inspect elements by evaluating something for each, which the step
   counter already sees but the row counter would otherwise miss. *)
let visit (n : int) = rows := !rows + n
