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

type run = { steps : int; cmps : int; canon : int; secs : float; out : string }

let run_one (c : command) (w : Gen.workload) : run =
  let store = Gen.locals_of w.store and env = Gen.locals_of w.env in
  Count.reset ();
  let t0 = Sys.time () in
  let final = Eval.interp_command store env c in
  let t1 = Sys.time () in
  let out =
    String.concat "; "
      (List.map (fun (k, v) -> k ^ " = " ^ Value.to_string v) (Eval.SMap.bindings final))
  in
  { steps = !Count.steps; cmps = !Count.comparisons;
    canon = !Count.canonicalisations; secs = t1 -. t0; out }

let sub (a : run) (b : run) : run =
  { steps = a.steps - b.steps; cmps = a.cmps - b.cmps; canon = a.canon - b.canon;
    secs = a.secs -. b.secs; out = a.out }

(* the op phase of one workload, with the build phase subtracted off *)
let op_phase (c : command) (sp : Gen.spec) ~rows ~ops ~only : run =
  let base = run_one c (Gen.workload sp ~rows ~ops:0 ~only) in
  let full = run_one c (Gen.workload sp ~rows ~ops ~only) in
  sub full base

let default_sizes = [ 100; 200; 400; 800 ]
let ops_per_kind = 20

let factor (small : int) (large : int) : string =
  if small <= 0 then "    -" else Printf.sprintf "%5.1fx" (float large /. float small)

let run (sizes : int list) =
  let sizes = if sizes = [] then default_sizes else sizes in
  let lo = List.hd sizes and hi = List.nth sizes (List.length sizes - 1) in
  Printf.printf
    "Each op phase is %d queries of each kind the subject dispatches on.\n\
     steps counts interpreter work and cmps counts value comparisons; both\n\
     are machine-independent.  'agree' compares the two programs' final stores,\n\
     which is the soundness theorem on this input.\n"
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
       (* one kind at a time: which read is responsible for the curve *)
       Printf.printf "  per kind, op phase only, %d rows -> %d rows:\n" lo hi;
       Printf.printf "    %-14s %11s %7s %11s %7s\n" "kind" "src steps" "growth"
         "opt steps" "growth";
       List.iter
         (fun (kind, _) ->
            let only = Some kind in
            let sl = op_phase src sp ~rows:lo ~ops:ops_per_kind ~only
            and sh = op_phase src sp ~rows:hi ~ops:ops_per_kind ~only
            and ol = op_phase opt sp ~rows:lo ~ops:ops_per_kind ~only
            and oh = op_phase opt sp ~rows:hi ~ops:ops_per_kind ~only in
            Printf.printf "    %-14s %11d %7s %11d %7s\n" kind sh.steps
              (factor sl.steps sh.steps) oh.steps (factor ol.steps oh.steps))
         sp.kinds)
    subjects
