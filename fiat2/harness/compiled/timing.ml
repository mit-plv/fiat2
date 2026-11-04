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

   THE AUTHOR COMPARISON IS HERE, in `threeway` and `matched` below.  It was
   not, at first, and the reason is worth keeping: baseline.ml is written
   against the boxed dynamic value, so timing our compiled column against it
   would have compared two REPRESENTATIONS and not two programs.  Both sides
   had to be monomorphic first -- which is what compiled/authors.ml is -- and
   then both had to be able to hold the same STORAGE, which is Rt.SelMap and
   Rt.SelSet and what `matched` measures. *)

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

(* ---------- all three columns, compiled ----------

   The comparison the whole exercise was for, and the one harness/README
   calls the more important of the two: the query as WRITTEN with no index,
   the program the optimizer DERIVES from it, and the AUTHOR's own code --
   all three compiled, all three monomorphic, all three charging through
   rt.ml.  Within a row the representation is the same, so a ratio compares
   two programs.

   PARITY IS THE EXPECTED RESULT on opt/author.  The compiler is supposed to
   arrive back at what the author built by hand, so matching is the finding
   and a large win would mean one of the two is not what it claims to be.
   The two subjects where a win IS expected are named in their
   transcriptions: user_search, where the author never built the trigram
   index, and dependent_plugins, where the author built nothing at all.

   AND READ THE SECONDS AGAINST THE COUNTED COLUMN, which is why both are
   here.  At a point read both columns take about 200 NANOSECONDS, and at
   that granularity the clock measures how a column happens to be written --
   a wrapper, an allocation, a closure -- and not its algorithm.  The
   counters are exact and deterministic, and they say PARITY exactly where
   parity is predicted: keycloak/byId is 13.4 units against 11.4 and
   cluster/forTopic 9.0 against 8.0, while the same rows read 0.38 and 0.42
   in seconds.  So on a point read the counted column is the verdict and the
   seconds are not.

   Where the difference IS algorithmic the two agree sharply, which is the
   check that the counters are not simply insensitive: user_search/suggest
   is 0.02 counted and 0.01 in seconds, dependent_plugins/resolveAll 0.01 and
   0.02.  The rule of thumb this leaves: trust the seconds at an order of
   magnitude, trust the counters at a factor.

   READ opt/auth WITH THE STRUCTURE CHOICE IN MIND.  Where the two sides
   chose differently the ratio carries that and not the algorithm: lookin and
   item_deletion are a TSet stored as a tree (TSet carries no kind) against
   the author's hash set, and named_cache is the mirror image, our trie
   against the NavigableMap the author chose.  THIS TABLE REPRODUCES THAT
   RATHER THAN HIDING IT, which is why it is only half the answer; `matched`
   below is the other half, measuring every row at a storage both sides
   hold.  Read the two together: this one says what each column costs as the
   type system has it today, and that one says how much of the difference was
   the structure. *)

(* The same per-kind difference, COUNTED.  Counters are deterministic, so
   this needs no repetition and carries no noise -- which makes it the
   instrument that says whether a seconds ratio is algorithmic or is the
   constant factor of how a column happens to be written. *)
let per_op_work (p : (string -> Value.t option) -> unit -> unit)
    (sp : Gen.spec) ~(rows : int) ~(kind : string) : float option =
  let ops = 20 in
  let c w = fst (counted (p (lookup_of w))) in
  let b = c (Gen.workload sp ~rows ~ops:0 ~only:None) in
  let f = c (Gen.workload sp ~rows ~ops ~only:(Some kind)) in
  if f - b <= 0 then None else Some (float_of_int (f - b) /. float_of_int ops)

let threeway (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 1600 ] else sizes in
  Printf.printf "%-20s %-15s %6s %10s %10s %8s %9s %9s %8s\n" "subject" "kind"
    "rows" "opt s/op" "auth s/op" "opt/au" "opt work" "auth work" "work x";
  Printf.printf "%s\n" (String.make 100 '-');
  List.iter
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.programs with
       | None -> ()
       | Some (psrc, popt) ->
           let auth = List.assoc_opt name Authors.runners in
           List.iter
             (fun rows ->
                List.iter
                  (fun (kind, _) ->
                     let scalable = not (List.mem kind sp.Gen.mutating) in
                     let m p = per_op p sp ~rows ~kind ~scalable in
                     let wk p = per_op_work p sp ~rows ~kind in
                     ignore psrc;
                     let o = m popt in
                     let a = match auth with None -> None | Some p -> m p in
                     let ow = wk popt in
                     let aw = match auth with None -> None | Some p -> wk p in
                     let cell = function
                       | Some x -> Printf.sprintf "%10.3g" x
                       | None -> " below res" in
                     let wcell = function
                       | Some x -> Printf.sprintf "%9.1f" x
                       | None -> "        -" in
                     let r x y =
                       match x, y with
                       | Some a, Some b when b > 0. -> Printf.sprintf "%8.2f" (a /. b)
                       | _ -> "       -" in
                     Printf.printf "%-20s %-15s %6d %s %s %s %s %s %s%s\n" name
                       kind rows (cell o) (cell a) (r o a) (wcell ow) (wcell aw)
                       (r ow aw)
                       (if List.mem name Authors.hand_written then "  (no author)"
                        else if auth = None then "  (no transcription)"
                        else if scalable then ""
                        else "  (write)"))
                  sp.Gen.kinds)
             sizes)
    Gen.specs

(* ---------- the structure choice, taken out of the comparison ----------

   This is bench.ml's `matched` table on compiled code, and it closes the one
   gap `threeway` above names: three of its rows carry a structure choice
   rather than an algorithm, because the generated column stored what its type
   said and the transcription stored what its author wrote, and nothing could
   bring the two to a common storage.  Rt.SelMap and Rt.SelSet can, so each
   row below is measured three times and the question "did the compiler arrive
   where the author did" is asked at a storage both sides hold.

   WHAT THE THREE COLUMNS MEAN is count.ml's, unchanged:

     typed   what the type system licenses today -- an Unranged dictionary is
             a hash because dict_kind says so, a set is a tree because no
             set_kind says otherwise, and the transcriptions store what their
             authors wrote.  This is the column every earlier table printed.
     trees   everything a balanced tree, on both sides: the conservative floor.
     hashes  a hash wherever the semantics permits, on both sides -- our sets
             included, which is what a set_kind would license.

   HOW TO READ A ROW.  Each cell is opt/author, so 1.00 is parity, and parity
   IS the expected result: the compiler is supposed to arrive back at what the
   author built by hand.  A row whose three columns agree has no structure
   choice in it -- window_store and range_delete read their key order, so
   nothing can hash them.  A row that MOVES across the columns is one where
   the choice was carrying part of the ratio, and the column in which the two
   sides hold the same storage is the one that answers the question about the
   algorithm.

   THE SECONDS AND THE WORK COLUMN SAY DIFFERENT THINGS and both are printed,
   for the reason the header of `threeway` sets out: at a point read of about
   200ns the clock measures how a column happens to be written, so the counted
   figure is the verdict at a factor and the seconds at an order of magnitude.

   AND READ AN UNSTABLE SECONDS CELL AS A BROKEN EXPERIMENT, not as a large
   result.  Two defects in Rt.SelSet -- see the comment on its `union` -- made
   an index build and a keyed delete quadratic.  The delete is inside the ops
   phase and the COUNTERS priced it exactly, 1031x and 10595x, identical on
   two runs.  The build is not: this table subtracts it, so what the defect
   produced was one seconds cell reading 14.95, 916.44 and 1073.55 on three
   runs of the same measurement.  A per-op difference cannot see a pathological
   build, and that instability is the only signal it has to offer.

   ONLY THE SUBJECTS WITH A TRANSCRIPTION APPEAR.  Every cell here is a ratio
   against an author, so a subject with no author has nothing to put in three
   columns and is left out rather than printed with dashes -- `threeway` above
   is the table that lists all of them.  `range_delete` is marked, because
   what stands in for its author is the implementation its structure asks for.

   `agree` is the fourth check from compiled.exe re-made at each setting: the
   two columns computed the same answer.  It is not decoration -- a walk over
   a hashed store has no order, so `hashes` is where an order-sensitive
   accumulation in either column would show up as NO. *)

let settings = [ Count.Typed; Count.Trees; Count.Hashes ]

let matched (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 1600 ] else sizes in
  let saved = !Count.structures in
  Printf.printf
    "The optimizer's compiled output against the original author's code,\n\
     each pair measured at a storage BOTH sides hold.  Every cell is\n\
     opt/author, so 1.00 is parity and parity is the expected result; `s` is\n\
     seconds per operation and `w` is the crossing data-work figure\n\
     count.ml defines.  See the comment above this table in\n\
     compiled/timing.ml for what the three settings mean and which of the two\n\
     instruments to believe.\n\n";
  Printf.printf "%-20s %-15s %5s  %-15s %-15s %-15s %5s\n" "subject" "kind"
    "rows" "typed    s / w" "trees    s / w" "hashes   s / w" "agree";
  Printf.printf "%s\n" (String.make 96 '-');
  List.iter
    (fun (name, sp) ->
       match
         (List.assoc_opt name Monotypes.programs,
          List.assoc_opt name Authors.runners,
          List.assoc_opt name Authors.checks)
       with
       | Some (_, popt), Some pauth, Some chk ->
           List.iter
             (fun rows ->
                List.iter
                  (fun (kind, _) ->
                     let scalable = not (List.mem kind sp.Gen.mutating) in
                     let cell st =
                       Count.structures := st;
                       let m p = per_op p sp ~rows ~kind ~scalable in
                       let wk p = per_op_work p sp ~rows ~kind in
                       let r x y =
                         match x, y with
                         | Some a, Some b when b > 0. ->
                             let v = a /. b in
                             Printf.sprintf
                               (if v < 0.01 then format_of_string "%6.4f"
                                else format_of_string "%6.2f") v
                         | _ -> "     -" in
                       let s = r (m popt) (m pauth)
                       and w = r (wk popt) (wk pauth) in
                       (* the fourth check, re-made here so that an
                          agreement is asserted at the setting the numbers
                          beside it were taken at and not at some other one.
                          At 50 rows rather than at `rows`: compiled.exe
                          already runs every check at every setting, and what
                          this column adds is the pairing, not a new size. *)
                       let ok =
                         chk (Gen.workload sp ~rows:50 ~ops:5 ~only:None) in
                       (s ^ " /" ^ w, ok) in
                     let cells = List.map cell settings in
                     Printf.printf "%-20s %-15s %5d  %-15s %-15s %-15s %5s%s\n"
                       name kind rows
                       (fst (List.nth cells 0)) (fst (List.nth cells 1))
                       (fst (List.nth cells 2))
                       (if List.for_all snd cells then "yes" else "NO")
                       (if List.mem name Authors.hand_written then
                          "  (no author)"
                        else if scalable then "" else "  (write)"))
                  sp.Gen.kinds)
             sizes
       | _ -> ())
    Gen.specs;
  Count.structures := saved
