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

(* ---------- per op KIND, with the op count scaled ----------

   The whole-program table above leaves cells saying `below res`, and the
   reason is structural: the ops phase is a difference of two timings, and an
   optimized read can be too cheap to separate from its own build.  bench.ml
   solves that by timing ONE op kind at a time and DOUBLING the op count
   until the difference clears the floor, and Gen.workload's ~only parameter
   is what makes it possible here too.

   A kind named in `spec.mutating` is never scaled.  Timing a read with more
   operations is sound; timing a WRITE with more operations silently measures
   a table that grew while it was being measured, which is a different
   experiment.  That exclusion is declared in gen.ml rather than detected,
   and this honours it. *)

let floor_secs = 0.002
let max_ops = 20480

(* the per-operation cost of one kind: scale until the difference between the
   build and the build-plus-ops clears the floor, then divide *)
let per_op (p : (string -> Value.t option) -> unit -> unit) (sp : Gen.spec)
    ~(rows : int) ~(kind : string) ~(scalable : bool) : float option =
  let build = timed (p (lookup_of (Gen.workload sp ~rows ~ops:0 ~only:None))) in
  let rec go (ops : int) : float option =
    let w = Gen.workload sp ~rows ~ops ~only:(Some kind) in
    let full = timed (p (lookup_of w)) in
    let d = full -. build in
    if d >= floor_secs then Some (d /. float_of_int ops)
    else if (not scalable) || ops * 4 > max_ops then None
    else go (ops * 4) in
  go 20

let kinds (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 1600 ] else sizes in
  Printf.printf "%-22s %-16s %6s %12s %12s %9s\n" "subject" "kind" "rows"
    "src s/op" "opt s/op" "speedup";
  Printf.printf "%s\n" (String.make 82 '-');
  List.iter
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.programs with
       | None -> ()
       | Some (psrc, popt) ->
           List.iter
             (fun rows ->
                List.iter
                  (fun (kind, _) ->
                     let scalable = not (List.mem kind sp.Gen.mutating) in
                     let s = per_op psrc sp ~rows ~kind ~scalable in
                     let o = per_op popt sp ~rows ~kind ~scalable in
                     let fmt = function
                       | Some x -> Printf.sprintf "%12.3g" x
                       | None -> "  below res " in
                     let ratio =
                       match s, o with
                       | Some a, Some b when b > 0. -> Printf.sprintf "%9.2f" (a /. b)
                       | _ -> "        -" in
                     Printf.printf "%-22s %-16s %6d %s %s %s%s\n" name kind rows
                       (fmt s) (fmt o) ratio
                       (if scalable then "" else "  (write)"))
                  sp.Gen.kinds)
             sizes)
    Gen.specs

(* ---------- the write side, priced by the build phase's slope ----------

   Forty op kinds are writes, and a write cannot be scaled: more operations
   would measure a table that grew while it was being measured.  So they come
   out `below res` above, and raising the repetition count does not help,
   because the problem is the EXPERIMENT and not the clock.

   The build phase answers it instead.  For the subjects whose table is grown
   by queries the build IS a sequence of writes, so

     (build at 2n  -  build at n) / n

   is the cost of one write at that size, with no scaling and no subtraction
   of two nearly equal numbers -- the two builds differ by a factor, not by a
   hair.  For the subjects handed their table in the environment the same
   slope prices one ROW of index construction, which is the other thing a
   write pays for.  Both are what the optimizer trades reads against, so this
   is the column its claim has to survive. *)

let build_slope (p : (string -> Value.t option) -> unit -> unit)
    (sp : Gen.spec) ~(rows : int) : float =
  let at n = timed (p (lookup_of (Gen.workload sp ~rows:n ~ops:0 ~only:None))) in
  let a = at rows and b = at (2 * rows) in
  (b -. a) /. float_of_int rows

let writes (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 800 ] else sizes in
  Printf.printf "%-24s %6s %13s %13s %9s\n" "subject" "rows" "src s/write"
    "opt s/write" "opt cost";
  Printf.printf "%s\n" (String.make 70 '-');
  List.iter
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.programs with
       | None -> ()
       | Some (psrc, popt) ->
           List.iter
             (fun rows ->
                let s = build_slope psrc sp ~rows
                and o = build_slope popt sp ~rows in
                (* Reported as opt/src, since on the write path a number
                   above 1 is a price paid and not a win.
                   A source slope at or below a nanosecond per row is not a
                   small measurement, it is NO measurement: those subjects
                   are HANDED their table in the environment, so their source
                   build does nothing at all and there is no ratio to take --
                   only the absolute cost of index construction, which the
                   opt column already prints. *)
                let nothing = 1e-9 in
                Printf.printf "%-24s %6d %13.3g %13.3g %9s\n" name rows
                  (if abs_float s < nothing then 0. else s)
                  o
                  (if abs_float s < nothing then "src: none"
                   else if s > 0. && o > 0. then Printf.sprintf "%.2fx" (o /. s)
                   else "below res"))
             sizes)
    Gen.specs
