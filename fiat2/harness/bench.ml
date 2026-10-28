(* Running the subjects.

   For each subject and each table size, four runs: the source program and
   the optimized program, each over a build-only workload and over the same
   workload with an op phase appended.  Subtracting gives the cost of the op
   phase on its own, which is the number the optimizer is about; the build
   number is what it charges for it.

   Then the same again one op kind at a time, at the smallest and the
   largest size, which is what says WHICH read is responsible for a curve.
   A kind whose cost is flat across that span is served by an index; one
   that grows with the table is still a scan, and in the optimized column
   that is a finding rather than a failure -- the two that are there are
   named in the eval README.

   Every pair of runs also compares the final stores.  The optimizer's
   soundness theorem says they must be equal -- the table itself is gone by
   then, because CLetMut restores the outer binding on the way out, so what
   is left is exactly the program's output.  The check is a concrete witness
   of the theorem on each input, and it would catch a generator feeding a
   subject something it was never meant to see. *)

open Extracted

type run =
  { steps : int; cmps : int; canon : int; rows : int; hash : int;
    strs : int; flds : int; over : int; out : string }

(* THE SINGLE FIGURE, and the part of it that crosses to hand-written code.
   count.ml's note says why there are two of them and why [rows] and
   [canon] are in neither.  Everything printed below is one of these or a
   named component of one. *)
let total (r : run) : int = r.steps + r.over + r.cmps + r.hash + r.strs + r.flds
let crossing (r : run) : int = r.cmps + r.hash + r.strs + r.flds

let run_one (c : command) (w : Gen.workload) : run =
  let store = Gen.locals_of w.store and env = Gen.locals_of w.env in
  Count.reset ();
  let final = Eval.interp_command store env c in
  (* READ THE COUNTERS BEFORE FORMATTING.  Value.to_string sorts a bag to
     print it canonically, and that sort calls Value.compare, so formatting
     the store could charge comparisons to the program that produced it.

     MEASURED, because the obvious claim here would be wrong: with the two
     bound the other way round, every number this harness prints is the SAME
     one, at every subject and both phases.  No final store holds a bag whose
     canonical order has to be produced to print it -- the index buckets that
     would are singletons under a declared key, and `outputs` is a list of
     strings.  So this ordering is worth nothing today and is kept because the
     alternative is a cost that would appear silently the first time a subject
     stored a bag of two. *)
  let steps = !Count.steps and cmps = !Count.comparisons
  and canon = !Count.canonicalisations and rows = !Count.rows
  and hash = !Count.hashing and strs = !Count.strings
  and flds = !Count.fields and over = !Count.overhead in
  let out =
    String.concat "; "
      (List.map (fun (k, v) -> k ^ " = " ^ Value.to_string v) (Eval.SMap.bindings final))
  in
  { steps; cmps; canon; rows; hash; strs; flds; over; out }

let sub (a : run) (b : run) : run =
  { steps = a.steps - b.steps; cmps = a.cmps - b.cmps; canon = a.canon - b.canon;
    rows = a.rows - b.rows; hash = a.hash - b.hash;
    strs = a.strs - b.strs; flds = a.flds - b.flds; over = a.over - b.over;
    out = a.out }

(* ---- wall clock, which is a cross-check and not the evidence ----

   It measures this tree-walking interpreter on this machine, so its
   CONSTANTS say nothing about what a compiled backend would do.  Its SHAPE
   is worth printing anyway: if a read the counters call flat took eight
   times longer on an eight-times-larger table, one of the two would be
   wrong.

   An optimized op phase is a few hundred steps, which is microseconds --
   far below the resolution of Sys.time.  So each measurement is repeated
   until it has accumulated at least [min_secs] and then divided back down,
   which is the usual way round that problem and the reason these two
   columns cost more wall clock than everything else here put together. *)

let min_secs = 0.1

(* An op phase is timed as (build + ops) minus (build alone), so when the op
   phase is cheap that difference is two large nearly-equal numbers
   subtracted.  This threshold is where such a difference stops being
   readable.

   MEASURED with the `timing` mode at the end of this file, because it had
   been asserted and never checked.  At 1600 rows item_deletion/containsHit's
   optimized op phase over 20 operations is a few tens of microseconds with a
   spread of several hundred percent -- unreadable, as this threshold says.
   But the threshold is not a property of the CLOCK, it is a property of
   using twenty operations: the same measurement settles to about 7% at 1280
   and 5% at 5120, falling monotonically, and the implied cost per operation
   agrees across those points to about 10%.  So a flat read is perfectly
   timeable; it just has to be timed with enough operations.  (The absolute
   numbers moved when the string and field counters were added -- counting a
   character means comparing characters one at a time -- so the figures here
   are deliberately given as shapes rather than as constants.)  That is what secs_per_op below does, and the threshold
   survives only for the kinds it cannot be done for. *)
let resolvable = 50e-6

let seconds_per_run (f : unit -> unit) : float =
  let t0 = Sys.time () in
  let n = ref 0 in
  let rec go () =
    f ();
    incr n;
    if Sys.time () -. t0 < min_secs then go () in
  go ();
  (Sys.time () -. t0) /. float !n

(* the op phase alone, in seconds: the whole workload timed, less the
   build-only workload timed, each repeated separately *)
let op_phase_secs (c : command) (sp : Gen.spec) ~rows ~ops ~only : float =
  let time_it (w : Gen.workload) = seconds_per_run (fun () ->
    ignore (Eval.interp_command (Gen.locals_of w.store) (Gen.locals_of w.env) c)) in
  let base = time_it (Gen.workload sp ~rows ~ops:0 ~only)
  and full = time_it (Gen.workload sp ~rows ~ops ~only) in
  Float.max 0. (full -. base)

let ops_per_kind = 20

(* ---- seconds PER OPERATION, timed with enough operations to be readable ----

   The number worth reporting is the cost of one operation, not of a phase of
   twenty of them: it is comparable across table sizes, and it is the only
   wall-clock figure that could ever be compared against another
   implementation.  Getting it means making the op phase big enough that
   (build+ops) minus (build) is signal.  So the op count DOUBLES until the
   difference clears [timing_target], which costs nothing for a linear read
   -- it clears at once -- and a few thousand operations for a flat one,
   which is the right way round.

   A MUTATING kind is never scaled, and this is the part that would be wrong
   if it were silent: Gen.workload appends the op queries after the build, so
   five thousand inserts on a fifty-row table measure a table that grew a
   hundredfold while being measured.  Those kinds keep the table's own op
   count and stay unreadable when they are below the floor, which is honest
   and is what Gen.spec's `mutating` field exists to make possible. *)

let timing_target = 2e-3
let max_timed_ops = 20480

type per_op = { secs : float; ops_used : int; scaled : bool }

let secs_per_op_of (run1 : Gen.workload -> unit) (sp : Gen.spec) ~rows
      ~(kind : string) : per_op =
  let only = Some kind in
  let time_it (w : Gen.workload) = seconds_per_run (fun () -> run1 w) in
  let base = time_it (Gen.workload sp ~rows ~ops:0 ~only) in
  let diff ops = Float.max 0. (time_it (Gen.workload sp ~rows ~ops ~only) -. base) in
  if List.mem kind sp.Gen.mutating then
    { secs = diff ops_per_kind /. float ops_per_kind;
      ops_used = ops_per_kind; scaled = false }
  else
    let rec go ops =
      let d = diff ops in
      if d >= timing_target || ops * 4 > max_timed_ops
      then { secs = d /. float ops; ops_used = ops; scaled = true }
      else go (ops * 4) in
    go ops_per_kind

let interp_once (c : command) (w : Gen.workload) : unit =
  ignore (Eval.interp_command (Gen.locals_of w.store) (Gen.locals_of w.env) c)

let secs_per_op (c : command) (sp : Gen.spec) ~rows ~(kind : string) : per_op =
  secs_per_op_of (interp_once c) sp ~rows ~kind

(* the op phase of one workload, with the build phase subtracted off *)
let op_phase (c : command) (sp : Gen.spec) ~rows ~ops ~only : run =
  let base = run_one c (Gen.workload sp ~rows ~ops:0 ~only) in
  let full = run_one c (Gen.workload sp ~rows ~ops ~only) in
  sub full base

(* Six sizes spanning 32x, doubling.  Doubling rather than adding a constant
   because the quantity being estimated is an EXPONENT, and an exponent is
   read off evenly spaced points on a log axis -- equal additive steps crowd
   the small end of a log plot and tell you least where the curves separate.
   Thirty-two-fold is as wide as the quadratic build phases allow: the
   elaborated uniqueness guard makes a source build O(n^2), so the top size
   costs sixteen times the 400-row one for those four subjects. *)
let default_sizes = [ 50; 100; 200; 400; 800; 1600 ]

let factor (small : int) (large : int) : string =
  if small <= 0 then "    -" else Printf.sprintf "%5.1fx" (float large /. float small)

let factor_f (small : float) (large : float) : string =
  if small < resolvable || large < resolvable then "    -"
  else Printf.sprintf "%5.1fx" (large /. small)

let secs_str (x : float) : string =
  if x < resolvable then "   <50us" else Printf.sprintf "%8.6f" x

(* ---- the exponent, which is what an asymptotic claim actually says ----

   A ratio between two sizes cannot tell linear from n log n: over an 8x
   range n grows 8.0x and n log n grows 9.4x, and the generators' own
   bucketing moves the measured ratio by about that much.  So fit

     log(cost) = a * log(rows) + b

   by least squares over all the sizes and report a.  1.0 is linear in the
   table, 0.0 is independent of it, and about 0.2 is what a tree probe's
   COMPARISON count comes to over this range, log n being a weak power law
   in disguise.

   Reporting a fitted exponent without saying how well it fit would be
   worse than reporting nothing, so [fit] also returns the largest relative
   residual, and the printer marks an exponent whose fit is loose.  A cost
   that is genuinely logarithmic, or that has a large constant term beside
   a linear one, SHOULD fit a power law loosely; the mark is information,
   not a defect. *)

type fitted = { exponent : float; residual : float }

let fit (pts : (int * int) list) : fitted option =
  let pts = List.filter (fun (n, y) -> n > 0 && y > 0) pts in
  let m = float (List.length pts) in
  if m < 3. then None
  else begin
    let xs = List.map (fun (n, _) -> log (float n)) pts
    and ys = List.map (fun (_, y) -> log (float y)) pts in
    let mean l = List.fold_left ( +. ) 0. l /. m in
    let mx = mean xs and my = mean ys in
    let cov = List.fold_left2 (fun a x y -> a +. ((x -. mx) *. (y -. my))) 0. xs ys
    and var = List.fold_left (fun a x -> a +. ((x -. mx) ** 2.)) 0. xs in
    if var <= 0. then None
    else begin
      let a = cov /. var in
      let b = my -. (a *. mx) in
      (* residuals in the logs are relative errors in the costs *)
      let worst =
        List.fold_left2
          (fun acc x y -> Float.max acc (Float.abs (exp (y -. ((a *. x) +. b)) -. 1.)))
          0. xs ys in
      Some { exponent = a; residual = worst }
    end
  end

let exp_str (f : fitted option) : string =
  match f with
  | None -> "    -"
  | Some { exponent; residual } ->
      Printf.sprintf "%s%4.2f" (if residual > 0.15 then "~" else " ") exponent

(* ---- the same series, as data rather than as a table ----

   One row per (subject, kind, program, size), so the curves can be plotted
   or fitted by something other than the fit above.  It prints the op phase
   only, which is the phase the asymptotic claim is about; the build phase
   is in the table.  Nothing here is derived -- the exponents in the table
   are computed from exactly these numbers. *)

let csv (sizes : int list) =
  let sizes = if sizes = [] then default_sizes else sizes in
  print_string
    "subject,kind,program,rows,work,data_work,steps,overhead,cmps,hashing,\
     strings,fields,rows_touched\n";
  List.iter
    (fun ((name, src), opt) ->
       let sp = List.assoc name Gen.specs in
       List.iter
         (fun (kind, _) ->
            let only = Some kind in
            List.iter
              (fun rows ->
                 List.iter
                   (fun (tag, c) ->
                      let r = op_phase c sp ~rows ~ops:ops_per_kind ~only in
                      Printf.printf "%s,%s,%s,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d\n"
                        name kind tag rows (total r) (crossing r)
                        r.steps r.over r.cmps r.hash r.strs r.flds r.rows)
                   [ ("src", src); ("opt", opt) ])
              sizes)
         sp.kinds)
    subjects

(* ---------- a diagnostic, not part of the evidence ----------

   The op phase is timed by DIFFERENCE -- (build + ops) minus (build alone) --
   and when the op phase is cheap those are two large nearly-equal numbers.
   So this file declares anything under [resolvable] unreadable and prints
   "<50us" instead.  That threshold was asserted and never measured, and it
   decides something real: whether a flat read can be timed at all on this
   interpreter, or whether comparing seconds against hand-written code needs a
   compiled backend before it can mean anything.

   This mode measures it instead of assuming it.  For one subject, one kind
   and one table size it computes the op-phase difference [timing_reps] times
   at a doubling series of op counts, and prints the mean, the spread and the
   implied cost per operation.  Two things can then be read off: whether the
   spread is small against the signal, and whether the per-op cost is STABLE
   as the op count grows -- if it is, the difference is measuring the
   operations rather than the noise between two timings.

   One caution, which the output repeats.  Raising the op count is sound only
   for a READ.  Gen.workload appends the op queries after the build, so five
   thousand inserts on a fifty-row table are measuring a table that grew a
   hundredfold on the way.  For a write kind the per-op column is therefore
   confounded and says so. *)

let timing_reps = 7
let timing_counts = [ 20; 80; 320; 1280; 5120 ]

let raw_op_secs (c : command) (sp : Gen.spec) ~rows ~ops ~only : float =
  let time_it (w : Gen.workload) =
    seconds_per_run (fun () ->
      ignore (Eval.interp_command (Gen.locals_of w.store) (Gen.locals_of w.env) c)) in
  let base = time_it (Gen.workload sp ~rows ~ops:0 ~only)
  and full = time_it (Gen.workload sp ~rows ~ops ~only) in
  full -. base

let timing (args : string list) =
  let arg n d = match List.nth_opt args n with Some v -> v | None -> d in
  let subject = arg 0 "item_deletion" in
  let kind = arg 1 "containsHit" in
  let rows = match int_of_string_opt (arg 2 "1600") with Some n -> n | None -> 1600 in
  match List.find_opt (fun ((n, _), _) -> n = subject) subjects with
  | None -> Printf.eprintf "unknown subject %s\n" subject; exit 2
  | Some ((_, src), opt) ->
      let sp = List.assoc subject Gen.specs in
      if not (List.mem_assoc kind sp.Gen.kinds) then begin
        Printf.eprintf "unknown kind %s for %s\n" kind subject; exit 2 end;
      Printf.printf
        "How precise is the wall clock, measured rather than declared.\n\
         %s / %s at %d rows, %d repetitions per point.  The op phase is timed\n\
         as (build+ops) minus (build), so what matters is whether the spread of\n\
         that difference is small against the difference itself, and whether the\n\
         per-op cost stays put as the op count grows.\n\
         The declared floor this is checking is %.0fus.\n\
         NOTE: raising the op count is sound only for a READ -- op queries are\n\
         appended to the build, so a write kind grows the table it measures.\n"
        subject kind rows timing_reps (resolvable *. 1e6);
      List.iter
        (fun (tag, c) ->
           Printf.printf "\n  program=%s\n" tag;
           Printf.printf
             "    ops       mean        min        max   spread    per-op\n";
           List.iter
             (fun ops ->
                let xs =
                  List.init timing_reps (fun _ ->
                    raw_op_secs c sp ~rows ~ops ~only:(Some kind)) in
                let n = float (List.length xs) in
                let mean = List.fold_left ( +. ) 0. xs /. n in
                let lo = List.fold_left Float.min infinity xs
                and hi = List.fold_left Float.max neg_infinity xs in
                let spread = if mean <= 0. then nan else (hi -. lo) /. mean in
                Printf.printf "  %5d  %9.6f  %9.6f  %9.6f  %6.1f%%  %.3e\n"
                  ops mean lo hi (spread *. 100.) (mean /. float ops))
             timing_counts)
        [ ("src", src); ("opt", opt) ]

let run (sizes : int list) =
  let sizes = if sizes = [] then default_sizes else sizes in
  let lo = List.hd sizes and hi = List.nth sizes (List.length sizes - 1) in
  Printf.printf
    "Each op phase is %d queries of each kind the subject dispatches on.\n\
     `work` is the SINGLE figure: every elementary operation the run performs,\n\
     interpreter dispatch and its environment lookups included, as well as the\n\
     comparisons, hashes, characters and record fields the program itself\n\
     touches.  It is machine-independent, and count.ml says what it is the sum\n\
     of and why nothing else belongs in it.  cmp+hash is printed beside it\n\
     because it is the part the structure choice moves, and the line below\n\
     each table breaks the total into all five of its components at the\n\
     largest size, so no cost is hidden behind a name.  'agree' compares the\n\
     two programs' final stores, which is the soundness theorem on this input.\n\
     Wall clock is printed per kind below, as a check on the shape only: it\n\
     times this interpreter, so its constants mean nothing for a backend.\n"
    ops_per_kind;
  List.iter
    (fun ((name, src), opt) ->
       let sp = List.assoc name Gen.specs in
       Printf.printf "\n=== %s ===" name;
       Printf.printf
         "\n  rows  phase    src work     opt work  src cmp+hash  opt cmp+hash  agree\n";
       let canon = ref [] in
       List.iter
         (fun rows ->
            let only = None in
            let s0 = run_one src (Gen.workload sp ~rows ~ops:0 ~only)
            and o0 = run_one opt (Gen.workload sp ~rows ~ops:0 ~only) in
            let s1 = run_one src (Gen.workload sp ~rows ~ops:ops_per_kind ~only)
            and o1 = run_one opt (Gen.workload sp ~rows ~ops:ops_per_kind ~only) in
            canon := (rows, (sub s1 s0).canon, (sub o1 o0).canon) :: !canon;
            (* cmp+hash is printed beside the total because it is the part
               the structure setting moves; the full decomposition is on the
               line after the largest size.  A source program installs no
               index, so its hash column is always 0. *)
            let line phase (s : run) (o : run) agree =
              let w (r : run) = Printf.sprintf "%d+%d" r.cmps r.hash in
              Printf.printf "%6d  %-6s %10d   %10d  %12s  %12s  %s\n" rows phase
                (total s) (total o) (w s) (w o) agree in
            line "build" s0 o0 (if s0.out = o0.out then "yes" else "NO");
            line "ops" (sub s1 s0) (sub o1 o0) (if s1.out = o1.out then "yes" else "NO");
            (* THE WHOLE OF THE TOTAL, SPELT OUT, at the largest size: the
               five components the work column is the sum of.  It is printed
               so that the claim "nothing is left out" is something a reader
               can check against the column beside it rather than take on
               trust -- and so that a component which is zero here is visibly
               zero rather than absent. *)
            if rows = hi then begin
              let d (r : run) =
                Printf.sprintf
                  "%d = %d stp + %d ovh | %d cmp + %d hsh + %d str + %d fld"
                  (total r) r.steps r.over r.cmps r.hash r.strs r.flds in
              Printf.printf
                "         work, ops phase, in full (the bar separates this\n\
                \         interpreter's own overhead from what crosses):\n";
              Printf.printf "           src %s\n" (d (sub s1 s0));
              Printf.printf "           opt %s\n" (d (sub o1 o0))
            end)
         sizes;
       (* a bag is an unordered list here, so this counts the times a
          subject observed a bag's canonical order and had to pay for it.
          It now prints NOTHING, at every subject and size, and that is the
          finding rather than an absence: every site that used to fire was an
          OEq against the EMPTY bag, which asks nothing about order, and
          value.ml answers those directly.  Two of the three compared two
          empty bags and so cost nothing even before; the third was
          HA_AreaRegistry's keyed delete asking whether a bucket had emptied,
          and it was 62% of that kind's cost.  A line appearing here again
          would mean a subject had started to observe a bag's order for real,
          which is exactly when these numbers deserve a second look. *)
       (match List.filter (fun (_, a, b) -> a > 0 || b > 0) (List.rev !canon) with
        | [] -> ()
        | l ->
            Printf.printf "  bag canonicalisations in the op phase (src/opt): %s\n"
              (String.concat ", "
                 (List.map (fun (r, a, b) -> Printf.sprintf "%d rows %d/%d" r a b) l)));
       (* One kind at a time, at every size: which read is responsible for
          the curve, and what shape the curve is.  'a' is the fitted
          exponent; a leading ~ means the fit was loose, which for a
          probe's comparison count is the expected answer. *)
       Printf.printf
         "  per kind, op phase only, over all %d sizes.  a is the exponent in\n\
         \  cost ~ rows^a (1.0 linear, 0.0 independent, ~0.2 a probe's compares);\n\
         \  a leading ~ marks a loose fit.  Columns are at %d rows.\n"
         (List.length sizes) hi;
       Printf.printf "    %-14s %11s %6s %6s %11s %6s %6s\n" "kind"
         "src work" "a" "a data" "opt work" "a" "a data";
       let timings =
         List.map
           (fun (kind, _) ->
              let only = Some kind in
              let series c =
                List.map
                  (fun rows -> (rows, op_phase c sp ~rows ~ops:ops_per_kind ~only))
                  sizes in
              let ss = series src and os = series opt in
              let at l rows = List.assoc rows l in
              Printf.printf "    %-14s %11d %6s %6s %11d %6s %6s\n" kind
                (total (at ss hi))
                (exp_str (fit (List.map (fun (n, r) -> (n, total r)) ss)))
                (exp_str (fit (List.map (fun (n, r) -> (n, crossing r)) ss)))
                (total (at os hi))
                (exp_str (fit (List.map (fun (n, r) -> (n, total r)) os)))
                (exp_str (fit (List.map (fun (n, r) -> (n, crossing r)) os)));
              (kind,
               secs_per_op src sp ~rows:lo ~kind,
               secs_per_op src sp ~rows:hi ~kind,
               secs_per_op opt sp ~rows:lo ~kind,
               secs_per_op opt sp ~rows:hi ~kind))
           sp.kinds in
       Printf.printf
         "  wall-clock seconds PER OPERATION at the two end sizes, %d -> %d.\n\
         \  A read is timed with as many operations as it takes for the op phase\n\
         \  to clear the timer's noise; a WRITE is not, because op queries are\n\
         \  appended to the build and would grow the table being measured, so a\n\
         \  write below the floor still reads '<50us'.  'n' is the op count used.\n\
         \  These are this interpreter on this machine: the SHAPE is the check,\n\
         \  the constants say nothing about a backend.\n"
         lo hi;
       Printf.printf "    %-14s %11s %7s %7s %11s %7s %7s\n" "kind" "src s/op"
         "growth" "n" "opt s/op" "growth" "n";
       List.iter
         (fun (kind, sl, sh, ol, oh) ->
            let p x = if x.secs < resolvable /. float x.ops_used then "   <50us"
                      else Printf.sprintf "%8.3e" x.secs in
            let g a b =
              if a.secs < resolvable /. float a.ops_used
                 || b.secs < resolvable /. float b.ops_used then "    -"
              else Printf.sprintf "%5.1fx" (b.secs /. a.secs) in
            Printf.printf "    %-14s %11s %7s %7d %11s %7s %7d\n" kind (p sh)
              (g sl sh) sh.ops_used (p oh) (g ol oh) oh.ops_used)
         timings)
    subjects

(* ---------- the authors' own code, beside the optimizer's output ----------

   See baseline.ml for what is transcribed and for the constraints on what
   these numbers may be read as saying.  The short form: `steps` and the
   interpreter's `overhead` cannot cross the boundary and are not shown; the
   DATA WORK -- comparisons, hashes, string characters and record fields --
   can, and is counted by the same rules on both sides; seconds can, and are
   about 25% inflated on our side by the interpreter.  The BUILD phase is not
   comparable and is not shown.

   The column that matters is not either cost but `agree`.  Each
   transcription is run over the very workload the subject programs are run
   over, and its final store is printed the same way, so a transcription that
   computes something else is caught before any of its numbers are read. *)

type base_run =
  { b_cmps : int; b_rows : int; b_hash : int; b_strs : int; b_flds : int;
    b_out : string }

(* the same crossing figure as [crossing] above, on the author's column: the
   work the two sides both really do, on keys, on strings and on fields.
   [steps] and [overhead] have no counterpart here, which is the whole reason
   the total and the crossing figure are two different numbers. *)
let b_crossing (r : base_run) : int = r.b_cmps + r.b_hash + r.b_strs + r.b_flds

let baseline_phase (brun : Baseline.runner) (sp : Gen.spec) ~rows ~ops ~only
  : base_run =
  (* counters read before the store is formatted, for the reason given at
     run_one *)
  let go w =
    Count.reset ();
    let st = brun w in
    let c = !Count.comparisons and r = !Count.rows and h = !Count.hashing
    and st_ = !Count.strings and fl = !Count.fields in
    (c, r, h, st_, fl, Baseline.format_store st) in
  let c0, r0, h0, s0, f0, _ = go (Gen.workload sp ~rows ~ops:0 ~only) in
  let c1, r1, h1, s1, f1, out = go (Gen.workload sp ~rows ~ops ~only) in
  { b_cmps = c1 - c0; b_rows = r1 - r0; b_hash = h1 - h0;
    b_strs = s1 - s0; b_flds = f1 - f0; b_out = out }

let baseline (sizes : int list) =
  let sizes = if sizes = [] then default_sizes else sizes in
  let hi = List.nth sizes (List.length sizes - 1) in
  Printf.printf
    "The original authors' own structures, against what the optimizer derived.\n\
     PARITY is the expected result: the source form is not the author's code --\n\
     the author's structure was removed to write the query declaratively -- so\n\
     the claim is that the compiler arrives back at what the author built.\n\
     'a' is the fitted exponent over %d sizes; data work and s/op are at %d\n\
     rows.\n\
     The EXPONENT is the claim.  The rows constant is not comparable factor\n\
     for factor: it charges each pipeline stage that iterates a collection,\n\
     so a derived read counts the same rows once per stage and hand-written\n\
     code has no stages (see count.ml).\n\
     DATA WORK is everything the two sides both really do: comparisons and\n\
     hashes on keys, characters examined by a string primitive, and record\n\
     fields walked by a projection.  It is counted by the same rules on both,\n\
     and the line under each row breaks it into those four.  What it leaves\n\
     out is this interpreter's dispatch and its environment lookups, which\n\
     hand-written OCaml has no counterpart for -- that part is in the `work`\n\
     column of the bench table and nowhere here.  A dictionary the type\n\
     system marks Unranged is stored as a hash table on our side too, which\n\
     is what dict_kind exists to license; SETS have no such annotation and\n\
     are stored as trees outside the hashes column.\n\
     s/op is ~25%% inflated on the opt side by the interpreter.  It FOLLOWS\n\
     the charge for dictionaries and sets, which hold the store their setting\n\
     names, and not for bags, which are a list under every setting -- so it\n\
     stays a check on shape rather than evidence.\n\
     'agree' is the real check -- the two computed the same answer, at EVERY\n\
     size and not just the largest; a size that differed is named.\n"
    (List.length sizes) hi;
  List.iter
    (fun (name, brun) ->
       match List.find_opt (fun ((n, _), _) -> n = name) subjects with
       | None -> Printf.eprintf "  (no extracted subject named %s)\n" name
       | Some ((_, src), opt) ->
           let sp = List.assoc name Gen.specs in
           Printf.printf "\n=== %s ===%s\n" name
             (if List.mem name Baseline.hand_written then
                "  (no author: our own example, against the implementation its\n                 \         structure asks for -- weaker evidence than the rest)"
              else "");
           Printf.printf
             "    %-13s %18s %18s %13s %13s %11s %11s %6s\n"
             "kind" "rows a (src/opt/base)" "rows at n (s/o/b)"
             "opt data work" "base data work" "opt s/op" "base s/op" "agree";
           List.iter
             (fun (kind, _) ->
                let only = Some kind in
                (* Run each column once per size and KEEP the records, rather
                   than re-running per projection.  That is what lets the
                   agreement below be checked at every size instead of only
                   at the largest, and it also removes three duplicate runs
                   at `hi`, which the previous shape paid for. *)
                let runs_s = List.map (fun r ->
                  (r, op_phase src sp ~rows:r ~ops:ops_per_kind ~only)) sizes
                and runs_o = List.map (fun r ->
                  (r, op_phase opt sp ~rows:r ~ops:ops_per_kind ~only)) sizes
                and runs_b = List.map (fun r ->
                  (r, baseline_phase brun sp ~rows:r ~ops:ops_per_kind ~only))
                  sizes in
                let series l f = List.map (fun (r, x) -> (r, f x)) l in
                let series_s f = series runs_s f
                and series_o f = series runs_o f
                and series_b f = series runs_b f in
                let last l = snd (List.nth l (List.length l - 1)) in
                let s_hi = last runs_s
                and o_hi = last runs_o
                and b_hi = last runs_b in
                (* THE AGREEMENT IS THE POINT OF THIS TABLE, so it is checked
                   at every size.  A transcription that agreed at the largest
                   table and differed at the smallest would have passed the
                   old single-point check -- and a wrong transcription was in
                   fact caught here once, which is the reason not to leave
                   this at one input. *)
                let disagreed =
                  List.filter_map
                    (fun ((r, o), (_, b)) ->
                       if o.out = b.b_out then None else Some r)
                    (List.combine runs_o runs_b) in
                let agree_str = match disagreed with
                  | [] -> "yes"
                  | rs -> "NO@" ^ String.concat ","
                                    (List.map string_of_int rs) in
                let os = secs_per_op opt sp ~rows:hi ~kind
                and bs =
                  secs_per_op_of (fun w -> ignore (brun w)) sp ~rows:hi ~kind in
                let p x = if x.secs < resolvable /. float x.ops_used then "   <50us"
                          else Printf.sprintf "%8.3e" x.secs in
                Printf.printf
                  "    %-13s %5s %5s %5s %6d %5d %5d %13d %13d %11s %11s %6s\n"
                  kind
                  (exp_str (fit (series_s (fun r -> r.rows))))
                  (exp_str (fit (series_o (fun r -> r.rows))))
                  (exp_str (fit (series_b (fun r -> r.b_rows))))
                  s_hi.rows o_hi.rows b_hi.b_rows
                  (crossing o_hi) (b_crossing b_hi)
                  (p os) (p bs) agree_str;
                (* the four components, so that a reader can see which of
                   them the row is made of rather than taking the sum on
                   trust.  Printed only where the row has more than one
                   component on either side, since a row that is all
                   comparisons says so already. *)
                let parts (c, h, st_, f) =
                  Printf.sprintf "%d cmp + %d hsh + %d str + %d fld" c h st_ f in
                let ours = (o_hi.cmps, o_hi.hash, o_hi.strs, o_hi.flds)
                and theirs = (b_hi.b_cmps, b_hi.b_hash, b_hi.b_strs, b_hi.b_flds) in
                let nonzero (c, h, st_, f) =
                  List.length (List.filter (fun x -> x > 0) [c; h; st_; f]) in
                if nonzero ours > 1 || nonzero theirs > 1 then
                  Printf.printf "    %-13s   opt %s | base %s\n" "" (parts ours)
                    (parts theirs))
             sp.kinds)
    Baseline.runners

(* ============================================================
   THE THREE PROGRAMS SIDE BY SIDE

   The query as it is written with no index, the program the optimizer
   derives from it, and the original author's hand-written code -- one row
   per op kind, at the largest table, with each column's fitted exponent.

   What the three columns ARE, because the comparison is only as honest as
   this: `src` is the subject as WRITTEN -- the query over the plain table,
   no index installed.  It is not a straw man and it is not the author's
   code; it is what the programmer hands the compiler.  `opt` is what the
   compiler hands back.  `orig` is what the author actually wrote,
   transcribed in baseline.ml.  So src -> opt is what the optimizer buys,
   and opt -> orig is whether it arrived back where the author was by hand.

   The COSTS are DATA WORK, which is everything the three columns all
   really do: comparisons and hashes on keys, characters a string primitive
   examines, record fields a projection walks.  What it leaves out is this
   interpreter's dispatch and its environment lookups, because the author's
   OCaml has no counterpart for either; the src-against-opt comparison of
   the complete total is in the `bench` table, where both sides are the same
   interpreter.

   THIS COLUMN USED TO BE KEY WORK ALONE, and that misread two kinds badly
   enough to be worth recording, because both were fixed by completing the
   figure rather than by adding a caveat to it:

     window_store/fetchAll    a full scan that compares no keys -- its range
                              filter is OLess on ints, not a key descent --
                              so key work called it FLAT and the src/opt
                              ratio came out at 0.04x, which had to be
                              explained as an artifact.  Counting the field
                              each scanned row is projected through makes
                              the exponent 1.00 and the ratio 396x, and the
                              caveat is gone rather than documented.
     user_search/suggest      the author's own algorithm is a contains()
                              scan over every row.  Key work charged it 184,
                              because a character comparison is not a key
                              comparison; it really does about 200,000
                              character comparisons, and now that they are
                              counted the ratio moves from 2.53x against us
                              to 0.0064x in our favour -- which is also what
                              the wall clock had been saying all along.

   Both ratios are of the data-work totals.  A `--` is a ZERO DENOMINATOR,
   which now happens only where a column is absent rather than free.

   `agree` is the store check, re-made at EVERY size rather than only the
   largest: all three programs computed the same final store.  On the left
   that is the soundness theorem on this input; on the right it is the
   transcription's own correctness.  A size that differed is named. *)

let threeway (sizes : int list) =
  let sizes = if sizes = [] then default_sizes else sizes in
  let hi = List.nth sizes (List.length sizes - 1) in
  Printf.printf
    "The query as written, the program derived from it, and the author's own\n\
     code.  DATA WORK is everything the three columns all really do (see\n\
     count.ml): comparisons and hashes on keys, characters a string primitive\n\
     examines, record fields a projection walks.  At %d rows, counted by the\n\
     same rules in all three columns.  `aD` is its fitted exponent over %d\n\
     sizes, which is the claim -- 1.0 linear, 0.0 independent of the table,\n\
     ~0.1 a probe's descent, a leading ~ a loose fit; `src aT` is the\n\
     exponent of the source's TOTAL work, interpreter included, and is\n\
     printed beside it as a check that the two tell the same story.\n\
     The interpreter's own dispatch and environment lookups are NOT here:\n\
     the author's OCaml has no counterpart for them, so they would make this\n\
     a measurement of the harness.  They are in the `work` column of the\n\
     bench table, where both sides are the same interpreter.\n\
     src/opt is what the optimizer buys.  opt/orig is the parity claim: the\n\
     source form is not the author's code -- their structure was removed to\n\
     write the query declaratively -- so the claim is that the compiler\n\
     arrives back at what they built, and about 1x is the expected result.\n\
     `--` is a zero denominator, not a missing number, and a `-` exponent is\n\
     a column that is identically zero.  `agree` is checked at every size.\n\
     Structure setting: %s.\n"
    hi (List.length sizes) (Count.structures_name !Count.structures);
  List.iter
    (fun ((name, src), opt) ->
       let sp = List.assoc name Gen.specs in
       let brun = List.assoc_opt name Baseline.runners in
       Printf.printf "\n=== %s ===%s\n" name
         (match brun with
          | None ->
              "  (no author transcription: a third-party subject we did not\n\
               \                 choose, so its orig column is empty)"
          | Some _ when List.mem name Baseline.hand_written ->
              "  (no author: our own example, against the implementation its\n\
               \                 structure asks for -- weaker evidence than the rest)"
          | Some _ -> "");
       Printf.printf "    %-13s %13s %12s %12s %7s %7s %6s %6s %9s %9s %6s\n"
         "kind" "src data" "opt data" "orig data" "src aD" "src aT" "opt aD"
         "orig aD" "src/opt" "opt/orig" "agree";
       List.iter
         (fun (kind, _) ->
            let only = Some kind in
            (* Each column is run once per size and the records are KEPT, so
               that the exponents and the agreement below come from the same
               runs as the printed totals and cannot drift from them. *)
            let runs_s =
              List.map (fun r ->
                (r, op_phase src sp ~rows:r ~ops:ops_per_kind ~only)) sizes
            and runs_o =
              List.map (fun r ->
                (r, op_phase opt sp ~rows:r ~ops:ops_per_kind ~only)) sizes in
            let runs_b =
              Option.map (fun b ->
                List.map (fun r ->
                  (r, baseline_phase b sp ~rows:r ~ops:ops_per_kind ~only))
                  sizes)
                brun in
            let last l = snd (List.nth l (List.length l - 1)) in
            let s_hi = last runs_s and o_hi = last runs_o in
            let kw = crossing and bkw = b_crossing in
            let b_hi = Option.map last runs_b in
            (* The agreement spans every column that exists, at every size.
               src = opt is the optimizer's soundness theorem; opt = orig is
               the transcription's.  Either failing names the size. *)
            let differing =
              List.filter_map
                (fun (r, o) ->
                   let s = List.assoc r runs_s in
                   let b = Option.map (List.assoc r) runs_b in
                   if s.out <> o.out
                      || (match b with Some b -> b.b_out <> o.out | None -> false)
                   then Some r else None)
                runs_o in
            let agree_str = match differing with
              | [] -> "yes"
              | rs -> "NO@" ^ String.concat "," (List.map string_of_int rs) in
            (* four decimals below 0.01, because the one ratio down there --
               dependent_plugins, where the optimizer beats the author's own
               code by changing the exponent -- rounds to 0.00x otherwise and
               reads as a missing number *)
            let ratio a b =
              if b = 0 then "       --"
              else
                let x = float a /. float b in
                Printf.sprintf (if x < 0.01 then format_of_string "%8.4fx"
                                else format_of_string "%8.2fx") x in
            Printf.printf
              "    %-13s %13s %12s %12s %7s %7s %6s %6s %9s %9s %6s\n"
              kind
              (string_of_int (kw s_hi))
              (string_of_int (kw o_hi))
              (match b_hi with
               | None -> "--"
               | Some b -> string_of_int (bkw b))
              (exp_str (fit (List.map (fun (r, x) -> (r, kw x)) runs_s)))
              (exp_str (fit (List.map (fun (r, x) -> (r, total x)) runs_s)))
              (exp_str (fit (List.map (fun (r, x) -> (r, kw x)) runs_o)))
              (match runs_b with
               | None -> "     -"
               | Some l -> exp_str (fit (List.map (fun (r, x) -> (r, bkw x)) l)))
              (ratio (kw s_hi) (kw o_hi))
              (match b_hi with
               | None -> "       --"
               | Some b -> ratio (kw o_hi) (bkw b))
              agree_str)
         sp.kinds)
    subjects

(* ============================================================
   THE SAME TWO PROGRAMS UNDER THE SAME STRUCTURE CHOICE

   The table the structure parameter exists for.  Each kind is run six times:
   the optimizer's output and the original author's code, under each of the
   three settings count.ml describes.  WITHIN a column both sides were charged
   by the same function at the same structure, so the ratio compares two
   PROGRAMS and nothing else; ACROSS columns it is that same comparison under
   a different assumption about the backend.

   What each column is:

     typed   what the type system licenses today -- a dictionary carrying
             Unranged is a hash table because ODictRange is untypeable at it,
             a set is a tree because no set_kind exists to say otherwise, and
             the originals are charged as their authors wrote them.  The only
             column whose every charge is backed by the type system.
     trees   the floor: nothing hashes, on either side.
     hashes  what a set_kind would ADD to typed, since sets are the only thing
             standing between the two columns on our side.

   A kind whose three columns are identical has no structure choice in it at
   all, which is what a Ranged dictionary's row should look like -- its key
   order is read, so no setting can hash it.

   Data work is the crossing figure count.ml defines -- cmps + hashing +
   strings + fields, everything both sides really do.  Seconds are not shown
   here: the structure setting moves them only where the store it names
   differs from the store the other setting names, so three columns of them
   would invite exactly the misreading the parameter exists to prevent. *)

let settings = [ Count.Typed; Count.Trees; Count.Hashes ]

let matched (sizes : int list) =
  let sizes = if sizes = [] then default_sizes else sizes in
  let hi = List.nth sizes (List.length sizes - 1) in
  let saved = !Count.structures in
  Printf.printf
    "The optimizer's output and the original authors' code, each charged the\n\
     SAME way within a column.  Data work is the crossing figure count.ml\n\
     defines -- cmps + hashing + strings + fields -- at %d rows; `x` is\n\
     ours/theirs, so 1.00 is parity and below 1 is ours ahead.  See the\n\
     comment above this table in bench.ml for what the three columns mean,\n\
     and count.ml for what the settings do.  A row whose three columns agree\n\
     has no structure choice in it -- its key order is read, so nothing can\n\
     hash it.  'agree' is the same check the baseline table makes, re-made\n\
     under every setting: the two computed the same answer.  A dash in the\n\
     x column means the author's side does no data work there at all, which\n\
     no row does any more: a cached count still costs the field read that\n\
     fetches it, and that is now counted.\n" hi;
  List.iter
    (fun (name, brun) ->
       match List.find_opt (fun ((n, _), _) -> n = name) subjects with
       | None -> Printf.eprintf "  (no extracted subject named %s)\n" name
       | Some ((_, _src), opt) ->
           let sp = List.assoc name Gen.specs in
           Printf.printf "\n=== %s ===%s\n" name
             (if List.mem name Baseline.hand_written then
                "  (no author: our own example, against the implementation its\n                 \
                 structure asks for -- weaker evidence than the rest)"
              else "");
           Printf.printf "    %-13s %22s %22s %22s %6s\n"
             "kind" "typed  ours/theirs  x" "trees  ours/theirs  x"
             "hashes ours/theirs  x" "agree";
           List.iter
             (fun (kind, _) ->
                let only = Some kind in
                let cell st =
                  Count.structures := st;
                  let o = op_phase opt sp ~rows:hi ~ops:ops_per_kind ~only in
                  let b = baseline_phase brun sp ~rows:hi ~ops:ops_per_kind ~only in
                  let ow = crossing o and bw = b_crossing b in
                  (ow, bw, o.out = b.b_out) in
                let cells = List.map cell settings in
                (* a dash would mean the author's side does no data work at
                   all on that kind.  No row does any more: ArrayList.size()
                   and currentSizeBytes are field reads, and a field read is
                   now counted, so the cached answer costs what fetching it
                   costs instead of costing nothing. *)
                let fmt (ow, bw, _) =
                  Printf.sprintf "%7d /%7d %6s" ow bw
                    (if bw = 0 then "--"
                     else
                       let x = float ow /. float bw in
                       (* four decimals below 0.01, as in the threeway table:
                          the two rows down there are the two places the
                          derived form beats an author's own algorithm, and
                          0.01 reads as a rounding artifact *)
                       Printf.sprintf (if x < 0.01 then format_of_string "%.4f"
                                       else format_of_string "%.2f") x) in
                let agree_str =
                  if List.for_all (fun (_, _, a) -> a) cells then "yes" else "NO" in
                Printf.printf "    %-13s %s %s %s %6s\n" kind
                  (fmt (List.nth cells 0)) (fmt (List.nth cells 1))
                  (fmt (List.nth cells 2)) agree_str)
             sp.kinds)
    Baseline.runners;
  Count.structures := saved

(* ============================================================
   WHAT THE SELECTOR'S CHOICE IS WORTH -- a side note, deliberately kept
   out of every table above.

   Everything above compares programs: a declarative source against what
   the pipeline derives from it, and that derived form against the
   structure the original author built by hand.  Those are the claims.

   This is a different question and a smaller one.  Every program below is
   SOUND -- each is the output of the same verified pipeline on the same
   source, and each file's own soundness theorem covers both -- and the only
   difference between a pair is which indexes were listed and in what order.
   So nothing here bears on whether the rewriting works.  What it says is
   what a program would have paid if the selector had picked the other
   configuration, which is the quantitative half of a claim the development
   otherwise makes with term equalities: that the ORDER a configuration is
   written in changes the cost, and silently, because both configurations
   are correct.

   The pairs are the rule-ordering hazards catalogued in Selector.v, one
   file each, every one of them already pinned as an equality of terms in
   the file it belongs to.  This puts numbers on those pins.  `chosen` is
   the configuration eval/SelectorTests.v pins as the selector's own pick,
   so a row where the alternative wins would be a bug in the selector and
   not a caveat -- which is the other reason to run it.

   The build phase is reported here, unlike in the baseline comparison,
   because a hazard can land on a write rather than on a read: the
   table-representation pair degrades an insert, and the subjects whose
   inserts are their build would otherwise show nothing at all. *)

let subject_of (name : string) : string =
  match String.index_opt name '/' with
  | Some i -> String.sub name 0 i
  | None -> name

let build_only (c : command) (sp : Gen.spec) ~rows : run =
  run_one c (Gen.workload sp ~rows ~ops:0 ~only:None)

let alternatives_cost (sizes : int list) =
  let sizes = if sizes = [] then default_sizes else sizes in
  let hi = List.nth sizes (List.length sizes - 1) in
  Printf.printf
    "What the SELECTOR's choice is worth -- a side note, not the claim.\n\
     Every program here is sound and every one is this pipeline's own output;\n\
     the only difference within a pair is which indexes were listed, and in\n\
     what order.  So this says nothing about whether the rewriting works.  It\n\
     says what a program would have paid had the selector picked the other\n\
     configuration its file also pins -- the rule-ordering hazards of\n\
     Selector.v, with a number instead of a term equality.\n\
     'chosen' is what eval/SelectorTests.v pins as the selector's pick, so the\n\
     alternative winning a row would be a selector bug, not a caveat.\n\
     'a' is the fitted exponent over %d sizes; counts are at %d rows.\n"
    (List.length sizes) hi;
  List.iter
    (fun (name, alt) ->
       let subj = subject_of name in
       match List.find_opt (fun ((n, _), _) -> n = subj) subjects with
       | None -> Printf.eprintf "  (no extracted subject named %s)\n" subj
       | Some ((_, _), chosen) ->
           let sp = List.assoc subj Gen.specs in
           Printf.printf "\n=== %s ===\n" name;
           Printf.printf
             "    %-13s %11s %11s %7s %6s %6s %11s %11s %7s %6s\n"
             "phase/kind" "chosen work" "alt work" "x" "a ch" "a alt"
             "chosen data" "alt data" "x" "agree";
           (* one row: two series over the sizes, and the pair at hi *)
           let row (label : string) (f : int -> run * run) =
             let series = List.map (fun r -> (r, f r)) sizes in
             let ch_hi, alt_hi = f hi in
             let fit_of pick =
               fit (List.map (fun (r, p) -> (r, pick p)) series) in
             Printf.printf
               "    %-13s %11d %11d %7s %6s %6s %11d %11d %7s %6s\n"
               label (total ch_hi) (total alt_hi)
               (factor (total ch_hi) (total alt_hi))
               (exp_str (fit_of (fun (c, _) -> total c)))
               (exp_str (fit_of (fun (_, a) -> total a)))
               (crossing ch_hi) (crossing alt_hi)
               (factor (crossing ch_hi) (crossing alt_hi))
               (if ch_hi.out = alt_hi.out then "yes" else "NO") in
           row "build" (fun r ->
             (build_only chosen sp ~rows:r, build_only alt sp ~rows:r));
           List.iter
             (fun (kind, _) ->
                let only = Some kind in
                row kind (fun r ->
                  (op_phase chosen sp ~rows:r ~ops:ops_per_kind ~only,
                   op_phase alt sp ~rows:r ~ops:ops_per_kind ~only)))
             sp.kinds)
    alternatives
