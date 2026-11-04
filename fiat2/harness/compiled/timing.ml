(* The measurement the compiled backend exists for.

   WHAT IS TIMED.  One whole program per column -- the build phase and the
   queries together -- because a compiled subject is one function and the
   phases are not separable without running it twice and subtracting, which
   is what bench.ml does for the interpreter and what this will do once the
   per-phase question is worth asking.  For now the comparison is
   src against opt on the same input, which is what the optimizer's claim is
   about.

   WHAT IS NOT TIMED.  Marshalling.  `prepared_*` converts the inputs and
   returns a closure, so the conversion happens before the clock starts; the
   closure creates its own refs each call, so repeating a measurement repeats
   the program rather than a mutated leftover.

   REPETITION.  A single run of a small subject is far below the clock's
   resolution, so each measurement repeats until it has accumulated at least
   `min_secs` and reports the per-run mean -- the same discipline bench.ml
   uses, and for the same reason.

   The counters are read from a SEPARATE single run, because the repetition
   above would multiply them.  They are not switched off for the timed runs;
   see the note at the call site for why, and for what that does and does
   not affect.

   WHAT THIS DOES NOT YET MEASURE: the author comparison.  baseline.ml is
   still written against the boxed dynamic value, so timing our compiled
   column against it would compare two REPRESENTATIONS and not two
   programs -- the same confound the matched columns exist to defuse.  Both
   sides have to be monomorphic before that ratio means anything. *)

(* Each phase is repeated to at least this long, so each is precise to about
   a percent -- but the OPS phase is a DIFFERENCE of two such numbers, and
   the difference of two nearly equal measurements is noise with a sign.
   bench.ml solves that by scaling the op count until the difference clears a
   threshold; that cannot be done here without care, because the op queries
   include WRITES and scaling them would measure a table that grew while it
   was being measured.  So this reports the difference and SAYS SO when it is
   below what the clock can resolve, rather than printing a ratio computed
   from noise. *)
let min_secs = 0.2

let timed (f : unit -> unit) : float =
  (* warm once, so the first run's allocation is not charged to the mean *)
  f ();
  let n = ref 0 and t0 = Sys.time () in
  let rec go () =
    f ();
    incr n;
    if Sys.time () -. t0 < min_secs then go () in
  go ();
  (Sys.time () -. t0) /. float_of_int !n

let data_work () : int =
  !Count.comparisons + !Count.hashing + !Count.strings + !Count.fields

let counted (f : unit -> unit) : int * int =
  Count.reset ();
  f ();
  (data_work (), !Count.rows)

let lookup_of (w : Gen.workload) (n : string) : Value.t option =
  match List.assoc_opt n w.Gen.env with
  | Some v -> Some v
  | None -> List.assoc_opt n w.Gen.store

let run (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 100; 400; 1600 ] else sizes in
  let ops = 20 in
  Printf.printf
    "%-24s %6s %10s %10s %8s %10s %10s %8s\n" "subject" "rows" "src build"
    "opt build" "build x" "src ops" "opt ops" "ops x";
  Printf.printf "%s\n" (String.make 90 '-');
  List.iter
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.programs with
       | None -> Printf.printf "%-24s  no generated program\n" name
       | Some (psrc, popt) ->
           List.iter
             (fun rows ->
                (* the build phase alone, and the build plus the queries;
                   the difference is the queries, which is what the
                   optimizer's claim is about.  Without this split an index
                   that is BUILT once and probed twenty times looks slow,
                   which is the artifact `lookin` showed. *)
                let wb = Gen.workload sp ~rows ~ops:0 ~only:None in
                let wf = Gen.workload sp ~rows ~ops ~only:None in
                let t p w = timed (p (lookup_of w)) in
                let sb = t psrc wb and ob = t popt wb in
                let sf = t psrc wf and off_ = t popt wf in
                let so = sf -. sb and oo = off_ -. ob in
                let ratio a b = if b > 0. then a /. b else 0. in
                (* a phase difference under a percent of the phase it was
                   subtracted from is not a measurement *)
                let dubious x base = x <= 0. || x < 0.01 *. base in
                let ops_cell =
                  if dubious so sf || dubious oo off_ then "  below res"
                  else Printf.sprintf "%8.2f" (ratio so oo) in
                Printf.printf "%-24s %6d %10.3g %10.3g %8.2f %10.3g %10.3g %s\n"
                  name rows sb ob (ratio sb ob) so oo ops_cell)
             sizes)
    Gen.specs

(* and the counters, in the same two phases, printed separately so that a
   seconds table and a work table can be read against each other *)
let work (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 100; 400; 1600 ] else sizes in
  let ops = 20 in
  Printf.printf "%-24s %6s %12s %12s %8s %12s %12s %8s\n" "subject" "rows"
    "src build" "opt build" "build x" "src ops" "opt ops" "ops x";
  Printf.printf "%s\n" (String.make 98 '-');
  List.iter
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.programs with
       | None -> ()
       | Some (psrc, popt) ->
           List.iter
             (fun rows ->
                let wb = Gen.workload sp ~rows ~ops:0 ~only:None in
                let wf = Gen.workload sp ~rows ~ops ~only:None in
                let c p w = fst (counted (p (lookup_of w))) in
                let sb = c psrc wb and ob = c popt wb in
                let sf = c psrc wf and off_ = c popt wf in
                let so = sf - sb and oo = off_ - ob in
                let ratio a b = if b > 0 then float_of_int a /. float_of_int b else 0. in
                Printf.printf
                  "%-24s %6d %12d %12d %8.2f %12d %12d %8.2f\n" name rows sb ob
                  (ratio sb ob) so oo (ratio so oo))
             sizes)
    Gen.specs
