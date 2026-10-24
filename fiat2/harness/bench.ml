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

type run = { steps : int; cmps : int; canon : int; out : string }

let run_one (c : command) (w : Gen.workload) : run =
  let store = Gen.locals_of w.store and env = Gen.locals_of w.env in
  Count.reset ();
  let final = Eval.interp_command store env c in
  let out =
    String.concat "; "
      (List.map (fun (k, v) -> k ^ " = " ^ Value.to_string v) (Eval.SMap.bindings final))
  in
  { steps = !Count.steps; cmps = !Count.comparisons;
    canon = !Count.canonicalisations; out }

let sub (a : run) (b : run) : run =
  { steps = a.steps - b.steps; cmps = a.cmps - b.cmps; canon = a.canon - b.canon;
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

(* An op phase is timed as (build + ops) minus (build alone), and when the
   op phase is a few hundred interpreter steps that difference is two large
   nearly-equal numbers subtracted -- so below this threshold the seconds
   are noise and a growth factor computed from them is noise with a decimal
   point on it.  Those rows say so instead.  They are not a gap in the
   result: they are the reads the step counts call flat, and the reason
   those counts are the evidence. *)
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
let ops_per_kind = 20

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
  print_string "subject,kind,program,rows,steps,cmps\n";
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
                      Printf.printf "%s,%s,%s,%d,%d,%d\n" name kind tag rows r.steps r.cmps)
                   [ ("src", src); ("opt", opt) ])
              sizes)
         sp.kinds)
    subjects

let run (sizes : int list) =
  let sizes = if sizes = [] then default_sizes else sizes in
  let lo = List.hd sizes and hi = List.nth sizes (List.length sizes - 1) in
  Printf.printf
    "Each op phase is %d queries of each kind the subject dispatches on.\n\
     steps counts interpreter work and cmps counts value comparisons; both\n\
     are machine-independent, and they are the evidence.  'agree' compares the\n\
     two programs' final stores, which is the soundness theorem on this input.\n\
     Wall clock is printed per kind below, as a check on the shape only: it\n\
     times this interpreter, so its constants mean nothing for a backend.\n"
    ops_per_kind;
  List.iter
    (fun ((name, src), opt) ->
       let sp = List.assoc name Gen.specs in
       Printf.printf "\n=== %s ===" name;
       Printf.printf
         "\n  rows  phase   src steps    opt steps     src cmps     opt cmps  agree\n";
       let canon = ref [] in
       List.iter
         (fun rows ->
            let only = None in
            let s0 = run_one src (Gen.workload sp ~rows ~ops:0 ~only)
            and o0 = run_one opt (Gen.workload sp ~rows ~ops:0 ~only) in
            let s1 = run_one src (Gen.workload sp ~rows ~ops:ops_per_kind ~only)
            and o1 = run_one opt (Gen.workload sp ~rows ~ops:ops_per_kind ~only) in
            canon := (rows, (sub s1 s0).canon, (sub o1 o0).canon) :: !canon;
            let line phase (s : run) (o : run) agree =
              Printf.printf "%6d  %-6s %10d   %10d   %10d   %10d  %s\n" rows phase
                s.steps o.steps s.cmps o.cmps agree in
            line "build" s0 o0 (if s0.out = o0.out then "yes" else "NO");
            line "ops" (sub s1 s0) (sub o1 o0) (if s1.out = o1.out then "yes" else "NO"))
         sizes;
       (* a bag is an unordered list here, so this counts the times a
          subject observed a bag's canonical order and had to pay for it.
          Both of the places it happens are an OEq against the empty bag:
          the emptiness test HA_LookinFunctions' source performs on a
          filter, which the optimized program replaces with a set
          membership test -- 40 down to 0 -- and a probe that
          HA_AreaRegistry's keyed delete compares, which the optimized
          program introduces and the source does not have. *)
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
         "src steps" "a" "a cmp" "opt steps" "a" "a cmp";
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
                (at ss hi).steps
                (exp_str (fit (List.map (fun (n, r) -> (n, r.steps)) ss)))
                (exp_str (fit (List.map (fun (n, r) -> (n, r.cmps)) ss)))
                (at os hi).steps
                (exp_str (fit (List.map (fun (n, r) -> (n, r.steps)) os)))
                (exp_str (fit (List.map (fun (n, r) -> (n, r.cmps)) os)));
              (kind,
               op_phase_secs src sp ~rows:lo ~ops:ops_per_kind ~only,
               op_phase_secs src sp ~rows:hi ~ops:ops_per_kind ~only,
               op_phase_secs opt sp ~rows:lo ~ops:ops_per_kind ~only,
               op_phase_secs opt sp ~rows:hi ~ops:ops_per_kind ~only))
           sp.kinds in
       Printf.printf
         "  wall-clock seconds at the two end sizes, %d -> %d, for the shape only\n\
         \  ('<50us' is an op phase too fast to separate from its build phase):\n"
         lo hi;
       Printf.printf "    %-14s %11s %7s %11s %7s\n" "kind" "src secs" "growth"
         "opt secs" "growth";
       List.iter
         (fun (kind, sl, sh, ol, oh) ->
            Printf.printf "    %-14s %11s %7s %11s %7s\n" kind (secs_str sh)
              (factor_f sl sh) (secs_str oh) (factor_f ol oh))
         timings)
    subjects
