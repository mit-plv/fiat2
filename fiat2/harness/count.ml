(* The counters the measurement is made of.

   Wall-clock time is reported alongside them by bench.ml, but it is not the
   evidence: it depends on the machine, on the allocator, on how hard OCaml's
   Map happens to work on a given shape, and above all on the fact that it is
   timing a tree-walking interpreter rather than any backend anyone would
   ship.  These counters depend on none of that.  What the seconds are good
   for is a check on the SHAPE: a read these counters call flat had better
   not take eight times longer on an eight-times-larger table.

     comparisons  every entry into Value.compare, including the recursive
                  entries on sub-values.  This is where the cost of a
                  dictionary, bag or set operation lives: a probe into a
                  balanced tree is logarithmically many of them, a scan is
                  linearly many.  A string comparison counts as one, which is
                  honest only because the generators keep keys short; the one
                  subject whose keys are long strings (the trigram one) is
                  also the one where the counts are reported with that
                  caveat.

     canonicalisations
                  every time a bag's canonical order had to be produced,
                  which is the only cost value.ml's unordered bag defers.
                  Zero means no subject ever observes it.

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
                  constant: EBagOf is free here because a bag is its
                  elements in any order, so a list already IS one.

   Both are global and both are reset before each run.  Nothing in the
   evaluator reads them, so they cannot change what it computes. *)

let comparisons = ref 0
let steps = ref 0
let canonicalisations = ref 0
let rows = ref 0

let reset () =
  comparisons := 0;
  steps := 0;
  canonicalisations := 0;
  rows := 0

(* a primitive that walks n elements without evaluating anything *)
let walk (n : int) =
  steps := !steps + n;
  rows := !rows + n

(* n stored elements inspected.  [walk] implies this; [visit] is for the places
   that inspect elements by evaluating something for each of them, which the
   step counter already sees but the row counter would otherwise miss. *)
let visit (n : int) = rows := !rows + n
