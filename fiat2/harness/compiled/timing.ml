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

(* ---------- a subject filter, so one row can be re-measured cheaply ----------

   Every table below walks `Gen.specs`, and most of them are timed, so asking
   one question about one subject meant paying for twenty-one others.  `only=a,b`
   anywhere in the arguments narrows every table to those subjects; with no
   `only=` the filter is empty and `subjects ()` IS `Gen.specs`, in order, so
   no published table changes.  It exists for the same reason `bench.ml`'s does:
   `dependent_plugins`'s quadratic source sets the price of a whole run. *)
let only : string list ref = ref []

let only_of_string (a : string) : string list option =
  match String.index_opt a '=' with
  | Some i when String.sub a 0 i = "only" ->
      Some (String.split_on_char ',' (String.sub a (i + 1) (String.length a - i - 1)))
  | _ -> None

let subjects () : (string * Gen.spec) list =
  if !only = [] then Gen.specs
  else List.filter (fun (n, _) -> List.mem n !only) Gen.specs

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
    (subjects ())

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
    (subjects ())

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
    (subjects ())

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
    (subjects ())

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
    (subjects ())

(* ---------- the fair baseline: the author WITH the index ----------

   `threeway` above compares against the code the author actually wrote, and
   on the two trigram subjects that code SCANS -- wagtail because the ORM
   handed them the one predicate form their own GIN indexes cannot serve,
   Jenkins because no index was ever built.  Both readings are faithful, and
   both make the comparison answer a weaker question than it looks like it
   answers.

   This table answers the stronger one.  The author column here is the same
   read served by `gin_trgm_ops` the way the database serves it when the
   indexable form IS written: wagtail's %> operator, and GitLab's documented
   `%q%` over `GIN(column gin_trgm_ops)` with its three-character guard.
   Same key scheme as the derived index, same recheck function, so the ratio
   measures what it costs to DERIVE a structure rather than declare one.

   PARITY IS THE EXPECTED RESULT, and here a win would be suspicious rather
   than welcome -- both columns run the same algorithm over the same keys.
   Whatever the number is, it is the honest price of derivation and is to be
   reported as that and not as a speedup.

   `scan s/op` is kept in the table on purpose: the three columns side by
   side are what make the claim checkable, because the gap between the two
   author columns is the part of any headline number that came from the
   author's hands being tied rather than from the compiler. *)
let indexed (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 1600 ] else sizes in
  Printf.printf "%-20s %-13s %5s %9s %9s %9s %7s %9s %9s %9s %7s\n" "subject"
    "kind" "rows" "opt s/op" "scan s/op" "gin s/op" "opt/gin" "opt work"
    "shapd work" "gin work" "work x";
  Printf.printf "%s\n" (String.make 118 '-');
  List.iter
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.programs, 
             List.assoc_opt name Authors.indexed_runners with
       | Some (_, popt), Some pgin ->
           let pscan = List.assoc_opt name Authors.runners in
           List.iter
             (fun rows ->
                List.iter
                  (fun (kind, _) ->
                     let scalable = not (List.mem kind sp.Gen.mutating) in
                     let m p = per_op p sp ~rows ~kind ~scalable in
                     let wk p = per_op_work p sp ~rows ~kind in
                     let o = m popt and g = m pgin in
                     let sc = match pscan with None -> None | Some p -> m p in
                     let ow = wk popt and gw = wk pgin in
                     (* the attribution control: the same index, the count
                        computed the way the derived term computes it *)
                     let shw =
                       match List.assoc_opt name Authors.shaped_runners with
                       | None -> None
                       | Some p -> wk p in
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
                     Printf.printf
                       "%-20s %-13s %5d %s %s %s %s %s %s %s %s%s\n" name kind
                       rows (cell o) (cell sc) (cell g) (r o g) (wcell ow)
                       (wcell shw) (wcell gw) (r ow gw)
                       (if scalable then "" else "  (write)"))
                  sp.Gen.kinds)
             sizes
       | _ -> ())
    (subjects ())

(* ---------- pricing one rule change at a time ----------

   COUNTED ONLY, and deliberately: the variants differ by tens of
   microseconds, which the clock cannot resolve (the `indexed` table's gin
   column gave opt/gin of 4.78, 21.2 and 31.2 on three runs at one setting).
   The counters are exact and deterministic, so each row here is a number
   that does not move between runs.

   Read it as a sequence.  `emitted` is the shape the pipeline produces
   today; each column after it applies ONE more change; `gin` is the
   hand-built index that computes no per-candidate count at all.  The gap
   between two adjacent columns is what that one rule change is worth, and
   nothing is worth proving that does not move its own column. *)
let shapes (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 6400 ] else sizes in
  match List.assoc_opt "fuzzy_search" Gen.specs,
        List.assoc_opt "fuzzy_search" Monotypes.programs,
        List.assoc_opt "fuzzy_search" Authors.indexed_runners with
  | Some sp, Some (_, popt), Some pgin ->
      let cols =
        ("opt", popt) :: Authors.shape_runners @ [ ("gin", pgin) ] in
      Printf.printf "%5s %-12s" "rows" "kind";
      List.iter (fun (n, _) -> Printf.printf " %12s" n) cols;
      Printf.printf " %9s %9s\n" "opt/gin" "emit/gin";
      Printf.printf "%s\n" (String.make (28 + (13 * List.length cols)) '-');
      List.iter
        (fun rows ->
           List.iter
             (fun (kind, _) ->
                if not (List.mem kind sp.Gen.mutating) then begin
                  let w = List.map (fun (_, p) -> per_op_work p sp ~rows ~kind) cols in
                  Printf.printf "%5d %-12s" rows kind;
                  List.iter
                    (fun c ->
                       Printf.printf " %12s"
                         (match c with
                          | Some x -> Printf.sprintf "%.0f" x
                          | None -> "-"))
                    w;
                  let g = List.nth w (List.length w - 1) in
                  let r x = match x, g with
                    | Some a, Some b when b > 0. -> Printf.sprintf "%9.2f" (a /. b)
                    | _ -> "        -" in
                  Printf.printf "%s%s\n" (r (List.hd w)) (r (List.nth w 1))
                end)
             sp.Gen.kinds)
        sizes
  | _ -> ()

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
    (subjects ());
  Count.structures := saved

(* ---------- the write-fraction sweep ----------

   WHY THIS TABLE EXISTS, and what was wrong with the ones above.  Every
   figure above is a difference of two whole-program timings -- the subject
   with no queries, and with k -- and at the k those tables use that difference
   is often a few percent of the build or inside its noise.  Nine of the
   twenty-two optimized op phases come out NEGATIVE in `run`.  Repeating a
   measurement cannot fix that, because a repetition re-runs the build with
   everything else; the only thing that can is running more OPERATIONS.

   For a read that is enough, and `per_op` does it.  For a write it is not:
   more writes mean a bigger table part-way through, so the experiment changes
   as it runs, and that is why all forty write kinds read `below res` and are
   priced instead by the build slope.

   PAIRING THE WRITES REMOVES THE OBSTACLE.  Gen.mixed interleaves one insert
   with one removal -- Gen.churn, declared per subject -- so the table returns
   to [rows] after every pair and a mixed workload can run as long as the
   clock needs.  The write fraction then becomes a parameter of the experiment
   rather than a thing to be avoided, which is what this table sweeps.

   THE OPS PHASE IS MADE TO DOMINATE, not assumed to.  The op count is scaled
   until the difference is at least [dominance] times the build.  `per_op`'s
   floor is an ABSOLUTE 2ms, which against a 39ms build accepts a difference
   that is 5% of it -- that is the criterion that let an unstable cell
   through, and a relative test is what it should have been.

   WHY [dominance] IS 3 AND NOT 20, which is what it was first.  Each phase is
   a mean repeated to [min_secs], so its own precision is some sigma -- call it
   a percent of its value.  The difference inherits that from the LARGER of the
   two, so

       sigma(d) / d  ~=  sigma(full) / d  =  1% * (1 + build/d)

   and the dominance factor enters only through that second term: 20 buys
   1.05% and 3 buys 1.33%.  Demanding 20 therefore bought a twentieth of a
   percent and cost nine cells, because a subject whose build is expensive
   against ONE operation -- lookin's set construction against one membership
   test -- cannot reach it inside any op count that fits in memory.  3 is the
   point past which more dominance buys nothing measurable.

   AND THAT DERIVATION IS NOT THE WHOLE ERROR, which is worth saying plainly
   because it was quoted as though it were.  1.33% is one cell's precision
   against its own repeats.  Running the entire sweep twice moves the median
   cell by 1.8% and the worst of 63 by 13%, and the read-only column is the
   noisy one while the 50% column reproduces inside 5%.  So the dominance
   factor is not what limits these figures, machine variance is, and nothing
   is gained by tightening it.

   The two columns are kept in the conventions their neighbours use: `src/opt`
   is a SPEEDUP, as in `kinds`, so bigger is better; `opt/auth` is a PARITY
   figure, as in `threeway` and `matched`, so 1.00 is arriving where the author
   did.

   WHAT A ROW WITH NO WRITE COLUMNS MEANS.  A subject with no removal in it
   has nothing to pair an insert with, and Gen.mixed returns None rather than
   inventing a pairing: keycloak, entity_registry and composite_key_decl are
   insert-only, and lookin, cluster and dependent_plugins write nothing at
   all.  Those rows carry their read-only column and dashes beside it, which
   is the honest shape of the question for them. *)

let dominance = 3.0
let max_mixed_ops = 262144

(* enough ops that the requested fraction is actually represented: at 1% a
   400-op list holds four writes, and the scaling multiplies from there *)
let start_ops (writes : int) : int =
  if writes <= 0 then 8 else max 8 (400 / writes)

(* ONE OP COUNT FOR EVERY COLUMN OF A CELL.

   The first version of this scaled each column on its own, until that
   column's ops phase cleared its own build, and divided by that column's own
   op count.  Seconds per operation sounds as though it licenses that -- a
   rate should not care how many operations it was averaged over.  The `scale`
   table below says otherwise, and says it twice.

   First, per-operation cost DRIFTS with the length of the list: on the src
   column sat4j reads 1.53e-5 at 512 ops and 8.09e-6 at 131072, a spread of
   1.89x, and cluster, range_delete, entity_registry and keyed_dict_delete all
   move by half again.  The drift is monotone, so it is not noise.

   Second, and worse, the drift was being sampled in ONE DIRECTION.  The opt
   column is so much cheaper per operation that it clears the 2ms floor only
   at 32768 ops and above, while the src column clears it at 512.  So
   independent scaling priced src at the small counts where it is dearest
   against opt at the large counts where it is cheapest, in every cell, and
   every src/opt figure inherited that bias.  It is why lowering the dominance
   factor -- which changes nothing but the chosen counts -- moved cells by
   29-88% when their own precision allows 1.3%.

   So a cell now picks one op count that satisfies every column in it, and
   measures them all there.  The count is found per column first, cheaply,
   because the expensive column clears early and stops; the maximum of those
   is the count, and only the columns that did not already land on it are
   re-measured.  A column that cannot clear at any affordable count is still
   dashed on its own, without taking its neighbours with it.

   The returned op count is printed in its own table, because a reader has to
   be able to see that the three figures in a cell came from the same
   workload. *)

let mixed_cell (ps : ((string -> Value.t option) -> unit -> unit) list)
    (sp : Gen.spec) ~(rows : int) ~(writes : int) :
    (int * float option list) option =
  let probe (p : (string -> Value.t option) -> unit -> unit) =
    let build = timed (p (lookup_of (Gen.workload sp ~rows ~ops:0 ~only:None))) in
    let rec go (ops : int) =
      match Gen.mixed sp ~rows ~ops ~writes with
      | None -> None
      | Some w ->
          let d = timed (p (lookup_of w)) -. build in
          if d >= floor_secs && d >= dominance *. build then Some (build, ops, d)
          else if ops * 4 > max_mixed_ops then None
          else go (ops * 4) in
    go (start_ops writes) in
  let probes = List.map probe ps in
  let n =
    List.fold_left
      (fun acc pr -> match pr with None -> acc | Some (_, ops, _) -> max acc ops)
      0 probes in
  if n = 0 then None
  else
    match Gen.mixed sp ~rows ~ops:n ~writes with
    | None -> None
    | Some w ->
        let at p pr =
          match pr with
          | None -> None
          | Some (build, ops, d) ->
              (* d only grows with ops, so a column that cleared at a lower
                 count clears here too; the test is kept as a guard, not as a
                 hope *)
              let d = if ops = n then d else timed (p (lookup_of w)) -. build in
              if d >= floor_secs && d >= dominance *. build then
                Some (d /. float_of_int n)
              else None in
        Some (n, List.map2 at ps probes)

(* the same difference, counted.  Deterministic, so one op count suffices and
   no scaling is needed -- and it is also what the stationarity check reads. *)
let mixed_per_op_work (p : (string -> Value.t option) -> unit -> unit)
    (sp : Gen.spec) ~(rows : int) ~(writes : int) ~(ops : int) : float option =
  match Gen.mixed sp ~rows ~ops ~writes with
  | None -> None
  | Some w ->
      let c ww = fst (counted (p (lookup_of ww))) in
      let b = c (Gen.workload sp ~rows ~ops:0 ~only:None) in
      let f = c w in
      if f - b <= 0 then None
      else Some (float_of_int (f - b) /. float_of_int ops)

(* ---------- the same sequence, IN SECONDS ----------

   `shapes` above is counted only, and for the stated reason: adjacent
   variants differ by tens of microseconds and the clock cannot resolve them.
   This table does not try to resolve adjacent variants.  It asks the ONE
   question the counters are structurally unable to answer -- whether the
   residual between `opt` and `rechecked` is in the wallclock too, or is an
   artifact of what the counters charge.

   Those two columns run the SAME ALGORITHM: the same index, the same
   candidate pool, the same per-candidate count, the same naive recheck.  One
   is the generated program, the other is hand-written OCaml.  So this is the
   one cell in the whole development where a seconds ratio cannot be excused
   as "two different algorithms" or "two different structures", and where the
   counters' stage charging (see harness/README on `rows`) is the obvious
   suspect precisely because it CANNOT be the explanation if the clock agrees.

   It uses `mixed_cell`'s discipline, not `per_op`'s, which is why it lives
   down here beside it: ONE op count per cell, satisfying every column, with
   the ops phase required to dominate the build phase.  Scaling each column
   to its own count is what biased the sweep by 29-88%, and this comparison
   is far too close to survive that.  The count and the build phase are
   printed so the reader can see the three figures came from one workload. *)
let kind_cell (ps : ((string -> Value.t option) -> unit -> unit) list)
    (sp : Gen.spec) ~(rows : int) ~(kind : string) :
    (int * float * float option list) option =
  let base = Gen.workload sp ~rows ~ops:0 ~only:None in
  let probe (p : (string -> Value.t option) -> unit -> unit) =
    let build = timed (p (lookup_of base)) in
    let rec go (ops : int) =
      let d = timed (p (lookup_of (Gen.workload sp ~rows ~ops ~only:(Some kind))))
              -. build in
      if d >= floor_secs && d >= dominance *. build then Some (build, ops, d)
      else if ops * 4 > max_mixed_ops then None
      else go (ops * 4) in
    go 20 in
  let probes = List.map probe ps in
  let n =
    List.fold_left
      (fun acc pr -> match pr with None -> acc | Some (_, ops, _) -> max acc ops)
      0 probes in
  if n = 0 then None
  else
    let w = Gen.workload sp ~rows ~ops:n ~only:(Some kind) in
    let builds = ref 0. in
    let at p pr =
      match pr with
      | None -> None
      | Some (build, ops, d) ->
          builds := Float.max !builds build;
          let d = if ops = n then d else timed (p (lookup_of w)) -. build in
          if d >= floor_secs && d >= dominance *. build then
            Some (d /. float_of_int n)
          else None in
    let out = List.map2 at ps probes in
    Some (n, !builds, out)

let shapesec (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 6400 ] else sizes in
  match List.assoc_opt "fuzzy_search" Gen.specs,
        List.assoc_opt "fuzzy_search" Monotypes.programs,
        List.assoc_opt "fuzzy_search" Authors.indexed_runners with
  | Some sp, Some (_, popt), Some pgin ->
      let cols = ("opt", popt) :: Authors.shape_runners @ [ ("gin", pgin) ] in
      Printf.printf "%5s %-12s %7s %9s" "rows" "kind" "ops" "build s";
      List.iter (fun (n, _) -> Printf.printf " %11s" n) cols;
      Printf.printf " %9s %9s\n" "opt/rech" "opt/gin";
      Printf.printf "%s\n" (String.make (46 + (12 * List.length cols)) '-');
      List.iter
        (fun rows ->
           List.iter
             (fun (kind, _) ->
                if not (List.mem kind sp.Gen.mutating) then
                  match kind_cell (List.map snd cols) sp ~rows ~kind with
                  | None -> Printf.printf "%5d %-12s   no count clears\n" rows kind
                  | Some (n, build, ts) ->
                      Printf.printf "%5d %-12s %7d %9.3g" rows kind n build;
                      List.iter
                        (fun c ->
                           Printf.printf " %11s"
                             (match c with
                              | Some x -> Printf.sprintf "%.3g" x
                              | None -> "-"))
                        ts;
                      (* BY NAME, not by position: the sequence grew a
                         column and a positional index would have silently
                         re-labelled this ratio *)
                      let col n =
                        let rec go cs vs = match cs, vs with
                          | (m, _) :: _, v :: _ when m = n -> v
                          | _ :: cs, _ :: vs -> go cs vs
                          | _ -> None in
                        go cols ts in
                      let r x y = match x, y with
                        | Some a, Some b when b > 0. -> Printf.sprintf "%9.2f" (a /. b)
                        | _ -> "        -" in
                      Printf.printf "%s%s\n"
                        (r (col "opt") (col "rechecked"))
                        (r (col "opt") (col "gin")))
             sp.Gen.kinds)
        sizes
  | _ -> ()

(* ---------- WHICH KIND OF WORK the residual factor is ----------

   `shapes` prices each rule change against the next; `shapesec` says the
   residual between `opt` and `rechecked` is in the clock too.  Neither says
   WHAT the residual is made of, because both report `data work`, which is a
   SUM of four counters.  This splits the sum.

   The four are not interchangeable and that is the point (see count.ml):
   comparisons and hashing are what a STRUCTURE costs on keys, strings is
   what a string PRIMITIVE examines, and fields is what a record projection
   walks past -- and fields is bounded by a constant of the TERM, so a factor
   that lives there is a property of the emitted shape rather than of the
   algorithm.  So the column that carries the residual names its cause.

   Counted, so deterministic and repeatable. *)
type tally = { cmp : int; hsh : int; str : int; fld : int; rws : int }

let tally_of (f : unit -> unit) : tally =
  Count.reset ();
  f ();
  { cmp = !Count.comparisons; hsh = !Count.hashing; str = !Count.strings;
    fld = !Count.fields; rws = !Count.rows }

let tally_sub (a : tally) (b : tally) (ops : int) : float * float array =
  let d x y = float_of_int (x - y) /. float_of_int ops in
  let v = [| d a.cmp b.cmp; d a.hsh b.hsh; d a.str b.str; d a.fld b.fld;
             d a.rws b.rws |] in
  (v.(0) +. v.(1) +. v.(2) +. v.(3), v)

let breakdown (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 6400 ] else sizes in
  let ops = 20 in
  match List.assoc_opt "fuzzy_search" Gen.specs,
        List.assoc_opt "fuzzy_search" Monotypes.programs,
        List.assoc_opt "fuzzy_search" Authors.indexed_runners with
  | Some sp, Some (_, popt), Some pgin ->
      let cols = ("opt", popt) :: Authors.shape_runners @ [ ("gin", pgin) ] in
      List.iter
        (fun rows ->
           List.iter
             (fun (kind, _) ->
                if not (List.mem kind sp.Gen.mutating) then begin
                  Printf.printf "\n%d rows, %s\n" rows kind;
                  Printf.printf "%-12s %11s %11s %11s %11s %11s %9s\n" "column"
                    "comparisons" "hashing" "strings" "fields" "data work"
                    "rows";
                  Printf.printf "%s\n" (String.make 82 '-');
                  let base = Gen.workload sp ~rows ~ops:0 ~only:None in
                  let full = Gen.workload sp ~rows ~ops ~only:(Some kind) in
                  List.iter
                    (fun (n, p) ->
                       let b = tally_of (p (lookup_of base))
                       and f = tally_of (p (lookup_of full)) in
                       let total, v = tally_sub f b ops in
                       Printf.printf
                         "%-12s %11.1f %11.1f %11.1f %11.1f %11.1f %9.1f\n" n
                         v.(0) v.(1) v.(2) v.(3) total v.(4))
                    cols
                end)
             sp.Gen.kinds)
        sizes
  | _ -> ()

let fractions = [ 0; 1; 10; 50 ]

(* The same sweep, COUNTED, printed beside the seconds for the reason
   `matched`'s header gives: at these per-operation costs the clock partly
   measures how a column was written, and the counters are exact.  It needs no
   scaling, since a counter does not have to clear a floor -- so one op count
   serves, and it is large enough that the build it subtracts is a small part
   of the whole. *)
let sweep_work (rows : int) : unit =
  let ops = 4096 in
  Printf.printf
    "\nAnd the same thing COUNTED -- data work per operation, which is exact\n\
     where the seconds above are not.  Read the two together: a ratio the two\n\
     agree on is algorithmic, and one they disagree on is telling you about\n\
     the constant factor of how a column happens to be written.\n\n";
  Printf.printf "%-22s %5s" "subject" "rows";
  List.iter (fun f -> Printf.printf "  %13s" (Printf.sprintf "%d%% writes" f))
    fractions;
  Printf.printf "\n%-22s %5s" "" "";
  List.iter (fun _ -> Printf.printf "  %13s" "src/opt opt/au") fractions;
  Printf.printf "\n%s\n" (String.make 92 '-');
  List.iter
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.programs with
       | None -> ()
       | Some (psrc, popt) ->
           let auth = List.assoc_opt name Authors.runners in
           Printf.printf "%-22s %5d" name rows;
           List.iter
             (fun writes ->
                let m p = mixed_per_op_work p sp ~rows ~writes ~ops in
                let o = m popt and sc = m psrc in
                let a = match auth with None -> None | Some p -> m p in
                let r x y =
                  match x, y with
                  | Some a, Some b when b > 0. ->
                      let v = a /. b in
                      Printf.sprintf
                        (if v < 0.01 then format_of_string "%6.4f"
                         else if v >= 1000. then format_of_string "%6.0f"
                         else format_of_string "%6.2f") v
                  | _ -> "     -" in
                Printf.printf "  %s %s" (r sc o) (r o a))
             fractions;
           Printf.printf "\n")
    (subjects ())

(* ---------- a THIRD instrument: bytes allocated per operation ----------

   This table exists for the one place where the counters and the clock
   disagree about a DIRECTION rather than a size.  `range_delete`'s advantage
   WIDENS with the write fraction on the clock -- 17x to 24x at 1600 rows --
   and NARROWS counted, 91x to 63x.  Both cannot be the statement about the
   algorithm, so the README reports the counted one and leaves the clock
   unexplained.  The obvious candidate is worth measuring rather than
   asserting: `data work` is comparisons, hashing, string characters and
   record fields -- every access a structure makes to a KEY -- and it charges
   nothing at all for BUILDING a result.  In compiled OCaml that cost is
   allocation, and a source form that deletes from a list by filtering it
   rebuilds the list where ours rewrites one path of a tree.

   If that is what the clock is seeing, the allocation ratio should follow the
   SECONDS and not the counters: it should rise with the write fraction where
   `data work` falls.  If it does not, the explanation is somewhere else and
   this table says so.

   `Gc.allocated_bytes` is a counter the runtime already keeps, so this needs
   no floor, no dominance and no repeats -- the same work allocates the same
   bytes.  It is read like `sweep_work` and not like `sweep`. *)
let allocated (f : unit -> unit) : float =
  f ();  (* warm once, for the same reason `timed` does: first-run work that
            a later run would not repeat belongs to neither figure *)
  let a0 = Gc.allocated_bytes () in
  f ();
  Gc.allocated_bytes () -. a0

let mixed_per_op_alloc (p : (string -> Value.t option) -> unit -> unit)
    (sp : Gen.spec) ~(rows : int) ~(writes : int) ~(ops : int) : float option =
  match Gen.mixed sp ~rows ~ops ~writes with
  | None -> None
  | Some w ->
      let b =
        allocated (p (lookup_of (Gen.workload sp ~rows ~ops:0 ~only:None))) in
      let f = allocated (p (lookup_of w)) in
      if f -. b <= 0. then None else Some ((f -. b) /. float_of_int ops)

(* the same instrument per OP KIND, which is what the fallback question needs:
   `kinds` times one kind at a time, and the two fallback kinds are the ones
   where the clock and the counters disagree about which column is cheaper *)
let per_op_alloc (p : (string -> Value.t option) -> unit -> unit) (sp : Gen.spec)
    ~(rows : int) ~(kind : string) ~(ops : int) : float option =
  let b = allocated (p (lookup_of (Gen.workload sp ~rows ~ops:0 ~only:None))) in
  let f = allocated (p (lookup_of (Gen.workload sp ~rows ~ops ~only:(Some kind)))) in
  if f -. b <= 0. then None else Some ((f -. b) /. float_of_int ops)

let kinds_alloc (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 1600 ] else sizes in
  let ops = 20 in
  Printf.printf
    "Bytes ALLOCATED per operation, one OP KIND at a time -- the instrument\n\
     `alloc` applies to a mixed workload, applied where `kinds` disagrees with\n\
     the counters about which column is cheaper.  Deterministic.\n\n";
  Printf.printf "%-22s %-16s %6s %13s %13s %9s\n" "subject" "kind" "rows"
    "src B/op" "opt B/op" "src/opt";
  Printf.printf "%s\n" (String.make 84 '-');
  List.iter
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.programs with
       | None -> ()
       | Some (psrc, popt) ->
           List.iter
             (fun rows ->
                List.iter
                  (fun (kind, _) ->
                     let m p = per_op_alloc p sp ~rows ~kind ~ops in
                     let sc = m psrc and o = m popt in
                     let cell = function
                       | Some (x : float) -> Printf.sprintf "%13.0f" x
                       | None -> Printf.sprintf "%13s" "-" in
                     let r =
                       match sc, o with
                       | Some a, Some b when b > 0. ->
                           Printf.sprintf "%9.2f" (a /. b)
                       | _ -> Printf.sprintf "%9s" "-" in
                     Printf.printf "%-22s %-16s %6d %s %s %s\n%!" name kind rows
                       (cell sc) (cell o) r)
                  sp.Gen.kinds)
             sizes)
    (subjects ())

let sweep_alloc (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 400 ] else sizes in
  let ops = 2048 in
  Printf.printf
    "Bytes ALLOCATED per operation, the third instrument.  `data work` prices\n\
     every access a structure makes to a key and prices building a result at\n\
     nothing; in compiled OCaml that cost is allocation, so where the clock\n\
     and the counters disagree this table says which of them allocation is\n\
     following.  Deterministic, so there are no repeats and no floor.\n\n";
  Printf.printf "%-22s %5s" "subject" "rows";
  List.iter (fun f -> Printf.printf "  %13s" (Printf.sprintf "%d%% w" f))
    fractions;
  Printf.printf "   %s\n" "src B/op @0%  opt B/op @0%  src @50%  opt @50%";
  Printf.printf "%-22s %5s" "" "";
  List.iter (fun _ -> Printf.printf "  %13s" "src/opt opt/au") fractions;
  Printf.printf "\n%s\n" (String.make 130 '-');
  List.iter
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.programs with
       | None -> ()
       | Some (psrc, popt) ->
           (* the author column too, because the parity question has the same
              shape: `item_deletion` reads 1.02 counted at a common storage
              and 0.62 on the clock, and whether allocation is what the clock
              is seeing there is the same question this table was built for *)
           let auth = List.assoc_opt name Authors.runners in
           List.iter
             (fun rows ->
                Printf.printf "%-22s %5d%!" name rows;
                let cells =
                  List.map
                    (fun writes ->
                       let m p = mixed_per_op_alloc p sp ~rows ~writes ~ops in
                       (m psrc, m popt,
                        match auth with None -> None | Some p -> m p))
                    fractions in
                let r x y =
                  match x, y with
                  | Some a, Some b when b > 0. ->
                      let v = a /. b in
                      Printf.sprintf
                        (if v < 0.01 then format_of_string "%6.4f"
                         else if v >= 1000. then format_of_string "%6.0f"
                         else format_of_string "%6.2f") v
                  | _ -> "     -" in
                List.iter
                  (fun (sc, o, a) ->
                     Printf.printf "  %s %s%!" (r sc o) (r o a))
                  cells;
                let abs = function
                  | Some (x : float) -> Printf.sprintf "%12.0f" x
                  | None -> Printf.sprintf "%12s" "-" in
                let s0, o0, _ = List.nth cells 0
                and s5, o5, _ = List.nth cells (List.length fractions - 1) in
                Printf.printf "   %s  %s  %s  %s\n%!" (abs s0) (abs o0)
                  (abs s5) (abs o5))
             sizes)
    (subjects ())

let sweep (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 1600 ] else sizes in
  let chosen = ref [] in
  Printf.printf
    "One operation at a time, with the build made negligible rather than\n\
     subtracted from: the op count is scaled until the ops phase is at least\n\
     %.0fx the build FOR EVERY COLUMN OF THE CELL AT ONCE, so the figures in\n\
     one cell come from one workload -- `mixed_cell` says why that is not the\n\
     pedantry it looks like, and the second table below gives each cell's\n\
     count.  Its precision is MEASURED and not derived: repeating the whole\n\
     sweep moves the median cell by 1.8%% and the worst by 13%%, so these are\n\
     two-significant-figure numbers and a FACTOR should be read off the\n\
     counted table below, which is identical across runs to the digit.\n\
     Writes are\n\
     PAIRED -- one insert, one removal in a slot pool above the table's own\n\
     rows -- so the table stays at `rows` however long the list, and every\n\
     read keeps the selectivity it has in the per-kind tables.  That is what\n\
     makes a write fraction a parameter instead of an obstacle.  `src/opt` is a speedup, so\n\
     bigger is better; `opt/auth` is parity, so 1.00 is arriving where the\n\
     author did.  A dash is a column the subject cannot be asked for -- see\n\
     the comment above this table.\n\n"
    dominance;
  Printf.printf "%-22s %5s" "subject" "rows";
  List.iter (fun f -> Printf.printf "  %13s" (Printf.sprintf "%d%% writes" f))
    fractions;
  Printf.printf "\n%-22s %5s" "" "";
  List.iter (fun _ -> Printf.printf "  %13s" "src/opt opt/au") fractions;
  Printf.printf "\n%s\n" (String.make 92 '-');
  List.iter
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.programs with
       | None -> ()
       | Some (psrc, popt) ->
           let auth = List.assoc_opt name Authors.runners in
           List.iter
             (fun rows ->
                Printf.printf "%-22s %5d%!" name rows;
                let counts = ref [] in
                List.iter
                  (fun writes ->
                     let ps =
                       psrc :: popt
                       :: (match auth with None -> [] | Some p -> [ p ]) in
                     let s, o, a =
                       match mixed_cell ps sp ~rows ~writes with
                       | None ->
                           counts := None :: !counts;
                           (None, None, None)
                       | Some (n, vs) ->
                           counts := Some n :: !counts;
                           (match vs with
                            | [ s; o ] -> (s, o, None)
                            | [ s; o; a ] -> (s, o, a)
                            | _ -> (None, None, None)) in
                     let r x y =
                       match x, y with
                       | Some a, Some b when b > 0. ->
                           let v = a /. b in
                           Printf.sprintf
                             (if v < 0.01 then format_of_string "%6.4f"
                              else if v >= 1000. then format_of_string "%6.0f"
                              else format_of_string "%6.2f") v
                       | _ -> "     -" in
                     Printf.printf "  %s %s%!" (r s o) (r o a))
                  fractions;
                Printf.printf "\n%!";
                chosen := (name, rows, List.rev !counts) :: !chosen)
             sizes)
    (subjects ());
  (* the op counts the cells were taken at.  Printed, not buried: the whole
     correction above is that the figures in one cell share a workload, and a
     reader can only check that if the count is on the page. *)
  Printf.printf
    "\nThe op count each cell was measured at -- one count for all three\n\
     columns of the cell, chosen as the smallest that clears the 2ms floor\n\
     and %.0fx the build for every column in it.\n\n"
    dominance;
  Printf.printf "%-22s %5s" "subject" "rows";
  List.iter (fun f -> Printf.printf " %10s" (Printf.sprintf "%d%% writes" f))
    fractions;
  Printf.printf "\n%s\n" (String.make 76 '-');
  List.iter
    (fun (name, rows, counts) ->
       Printf.printf "%-22s %5d" name rows;
       List.iter
         (fun c ->
            Printf.printf " %10s"
              (match c with Some n -> string_of_int n | None -> "-"))
         counts;
       Printf.printf "\n")
    (List.rev !chosen);
  List.iter sweep_work sizes

(* ---------- is the table actually stationary? ----------

   The sweep rests entirely on the claim that a paired write leaves |table|
   at `rows`, so the claim needs its own evidence rather than its own
   argument.  If a removal ever missed -- deleting a key already gone -- the
   inserts would outrun it and the table would GROW; if a removal took a row
   the inserts had not replaced, it would DRAIN, the deletes would turn into
   no-ops and the reads would start answering nothing.

   Count.rows is a direct probe of the size, on the SOURCE column: nearly
   every source read scans the table, so rows-per-op is proportional to the
   table it scanned, with the constant being how many nesting levels the term
   charges (see the note in count.ml -- a derived read can count the same rows
   more than once, so the ABSOLUTE value is not the table size, but it is
   proportional to it).

   So the test is a ratio against itself: measure rows-per-op at two op counts
   a factor apart, and they must agree.  A drain or a growth of any size shows
   up as a number that moves with the op count, and the printed pair is what
   makes the judgement checkable instead of asserted.

   WHAT IT DOES NOT CATCH, which is worth knowing because it did not: a
   SLIDING window keeps the size exactly right while moving the live keys out
   from under the reads, and this test passed 42 of 42 on one.  Size
   stationarity is not selectivity stationarity.  The pool is what makes the
   second hold, by construction rather than by measurement -- see Gen.churn. *)

let stationary_rows (p : (string -> Value.t option) -> unit -> unit)
    (sp : Gen.spec) ~(rows : int) ~(writes : int) ~(ops : int) : float option =
  match Gen.mixed sp ~rows ~ops ~writes with
  | None -> None
  | Some w ->
      let c ww = snd (counted (p (lookup_of ww))) in
      let b = c (Gen.workload sp ~rows ~ops:0 ~only:None) in
      let f = c w in
      if f - b <= 0 then None
      else Some (float_of_int (f - b) /. float_of_int ops)

(* the tolerance.  Not tight, deliberately: a read's key spread advances with
   the op index, so which rows each one answers -- and therefore rows-per-op --
   wanders a little even where the size is exact.  What the test has to catch
   is a table that grew or drained, and either of those moves this figure by a
   factor rather than by a tenth.  Measured, the worst cell is 0.4% off. *)
let stationary_tol = 1.25

let stationary (sizes : int list) : (string * int * float * float) list =
  let sizes = if sizes = [] then [ 400 ] else sizes in
  List.concat_map
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.programs with
       | None -> []
       | Some (psrc, _) ->
           List.concat_map
             (fun rows ->
                List.filter_map
                  (fun writes ->
                     (* 256 against 16384, a 64x span that CROSSES THE TEN
                        THOUSAND at which List.init changes implementation --
                        the boundary the sweep's op counts straddle and the
                        one a narrower span would have stayed inside *)
                     let a = stationary_rows psrc sp ~rows ~writes ~ops:256 in
                     let b = stationary_rows psrc sp ~rows ~writes ~ops:16384 in
                     match a, b with
                     | Some x, Some y -> Some (name, writes, x, y)
                     | _ -> None)
                  [ 1; 10; 50 ])
             sizes)
    (subjects ())

let stationary_report (sizes : int list) : unit =
  Printf.printf
    "Is the table stationary?  rows enumerated per op on the SOURCE column, at\n\
     256 ops and at 16384.  A table that grew or drained would move this by a\n\
     factor; see the comment above this table for why the absolute value is\n\
     not the table size and the ratio is what is being read.\n\n";
  Printf.printf "%-24s %7s %12s %12s %8s %s\n" "subject" "writes" "rows/op @256"
    "rows/op @16k" "ratio" "";
  Printf.printf "%s\n" (String.make 78 '-');
  List.iter
    (fun (name, writes, x, y) ->
       let r = if x > 0. then y /. x else 0. in
       Printf.printf "%-24s %6d%% %12.1f %12.1f %8.3f %s\n" name writes x y r
         (if r <= stationary_tol && r >= 1. /. stationary_tol then "" else "  DRIFTS"))
    (stationary sizes)

(* ---------- is the per-operation cost scale-invariant? ----------

   THE QUESTION THE SWEEP DEPENDED ON AND DID NOT ASK, now asked and ANSWERED
   NO -- so `mixed_cell` above measures every column of a cell at one count,
   and this table is the evidence for that discipline rather than a loose end.
   The version it corrected scaled each column independently until that
   column's ops phase cleared the build, so the src figure and the opt figure
   in one cell could be taken at op counts an order of magnitude apart.  Dividing by the op count makes that sound
   harmless -- seconds per operation, so the counts need not match.  It is
   harmless only if the per-operation cost does not DEPEND on the count, and a
   longer op list is a larger working set: more cache pressure, more minor
   collections, a longer list to walk.

   The evidence that this is not hypothetical: lowering the dominance factor
   from 20 to 3, which changes nothing but the op counts chosen, moved
   window_store's cell from 28.47 to 15.12 and keycloak's from 93.67 to
   130.35.  Those are far outside the ~1.3% the difference's own precision
   predicts, so something that is not noise is tracking the op count.

   This prints the ladder, so the question is answered by measurement.  A
   column whose numbers are flat across it can be compared against another
   column measured elsewhere on it; a column that drifts cannot, and then the
   cell has to be taken at ONE op count for every column in it.

   WHAT IT MEASURED, at 1600 rows: the src column drifts, monotonically and
   downwards, by up to 1.89x (sat4j 1.53e-5 at 512 ops against 8.09e-6 at
   131072; cluster 1.70x, range_delete 1.67x, keyed_dict_delete 1.54x,
   entity_registry 1.49x), while the opt column is flat to within 1.1x
   wherever two of its rungs resolve.  And the `-` cells are the other half of
   it: the opt column does not clear the 2ms floor below 32768 ops, where the
   src column clears it at 512, so independent scaling did not merely sample
   two points of a drifting curve -- it sampled the dear end for src and the
   cheap end for opt, every time. *)

(* The ladder is CLIMBED, not swept.  Each rung costs four times the one below
   it, and on a 1600-row table the src column is two to three orders dearer
   per operation than the opt column, so the top rung of a slow subject is an
   hour by itself -- and `timed` runs its argument at least twice.  A column
   therefore stops climbing once the next rung's predicted cost passes
   [scale_budget], and prints `>` for the rungs it declined.

   That costs the question nothing.  A column resolved over 512..8192 still
   spans 16x, and 16x is already wider than the gap between the two op counts
   a single sweep cell's columns are chosen at -- which is the thing being
   checked.  Each cell is printed and FLUSHED as it is measured, because the
   earlier attempt at this table buffered 44 rows into a file and showed
   nothing for 78 minutes of CPU. *)
let scale_budget = 8.0

let scale (sizes : int list) : unit =
  let sizes = if sizes = [] then [ 1600 ] else sizes in
  let ladder = [ 512; 2048; 8192; 32768; 131072 ] in
  Printf.printf
    "Seconds per operation at a ladder of op counts, 0%% writes, with the\n\
     build subtracted at each.  If a row is flat, per-op cost is independent\n\
     of the list length and two columns may be measured at different counts.\n\
     If it drifts, they may not.  `-` is below the 2ms floor; `>` is a rung\n\
     the column declined as too dear.\n\n";
  Printf.printf "%-22s %5s %-4s" "subject" "rows" "col";
  List.iter (fun n -> Printf.printf " %11s" (string_of_int n ^ " ops")) ladder;
  Printf.printf "   spread\n%s\n%!" (String.make 96 '-');
  List.iter
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.programs with
       | None -> ()
       | Some (psrc, popt) ->
           List.iter
             (fun rows ->
                List.iter
                  (fun (tag, p) ->
                     Printf.printf "%-22s %5d %-4s%!" name rows tag;
                     let build =
                       timed (p (lookup_of
                                   (Gen.workload sp ~rows ~ops:0 ~only:None))) in
                     let spent = ref build and got = ref [] in
                     List.iter
                       (fun ops ->
                          let cell =
                            if 4.0 *. !spent > scale_budget then ">"
                            else
                              match Gen.mixed sp ~rows ~ops ~writes:0 with
                              | None -> "-"
                              | Some w ->
                                  let full = timed (p (lookup_of w)) in
                                  spent := full;
                                  let d = full -. build in
                                  if d >= floor_secs then begin
                                    let per = d /. float_of_int ops in
                                    got := per :: !got;
                                    Printf.sprintf "%.3g" per
                                  end
                                  else "-" in
                          Printf.printf " %11s%!" cell)
                       ladder;
                     (match !got with
                      | [] -> Printf.printf "        -\n%!"
                      | g :: _ as all ->
                          let lo = List.fold_left min g all
                          and hi = List.fold_left max g all in
                          Printf.printf "   %6.2fx\n%!"
                            (if lo > 0. then hi /. lo else 0.)))
                  [ ("src", psrc); ("opt", popt) ])
             sizes)
    (subjects ())
