(* The compiled side: the generated programs, run.

   Four tests, each over the generators' own workloads, and each checking
   something the one before it cannot:

     read      every generated reader accepts its input, and re-reading it
               compares equal
     cross     the generated equality AGREES WITH Value.compare on two
               workloads, with both answers counted, so the equality is
               known to decide something
     agree     the compiled SOURCE column and the compiled OPTIMIZED column
               leave the same store on the same input.  This is bench.ml's
               store comparison performed on compiled code: both columns get
               the same converted inputs and their own fresh refs, so a
               difference can only come from the programs, and each
               agreement is a concrete witness of that subject's soundness
               theorem on that input
     interp    the compiled OPTIMIZED column against the INTERPRETER, on the
               same term and input.  This is the one a codegen that dropped
               the same work from BOTH columns could not pass, and the only
               one that says the compiled program computes what Interpret.v's
               transcription computes. *)

let failures = ref []
let setting = ref ""
let reads = ref 0
let yes = ref 0
let no = ref 0
let agreed = ref 0
let matched = ref 0
let authored = ref 0
let mixed_agreed = ref 0
let mixed_matched = ref 0

let sizes = [ 7; 50 ]

let lookup_of (w : Gen.workload) (n : string) : Value.t option =
  match List.assoc_opt n w.Gen.env with
  | Some v -> Some v
  | None -> List.assoc_opt n w.Gen.store

let fail (s : string) : unit =
  failures := (!setting ^ ": " ^ s) :: !failures

let guard (what : string) (f : unit -> unit) : unit =
  try f () with e -> fail (what ^ ": " ^ Printexc.to_string e)

let readers_of (name : string) (sp : Gen.spec) : unit =
  match List.assoc_opt name Monotypes.readers with
  | None -> fail (name ^ ": no generated reader")
  | Some (read, cross) ->
      List.iter
        (fun rows ->
           let w = Gen.workload sp ~rows ~ops:3 ~only:None in
           incr reads;
           guard (Printf.sprintf "%s/%d read" name rows) (fun () ->
               read (lookup_of w)))
        sizes;
      let a = Gen.workload sp ~rows:7 ~ops:3 ~only:None
      and b = Gen.workload sp ~rows:50 ~ops:3 ~only:None in
      guard (name ^ " cross") (fun () -> cross (lookup_of a) (lookup_of b) yes no);
      guard (name ^ " cross-same") (fun () ->
          cross (lookup_of a) (lookup_of a) yes no)

let agree_of (name : string) (sp : Gen.spec) : unit =
  match List.assoc_opt name Monotypes.agreements with
  | None -> fail (name ^ ": no generated program")
  | Some agree ->
      List.iter
        (fun rows ->
           let w = Gen.workload sp ~rows ~ops:5 ~only:None in
           guard (Printf.sprintf "%s/%d agree" name rows) (fun () ->
               if agree (lookup_of w) then incr agreed
               else
                 fail
                   (Printf.sprintf "%s at %d rows: src and opt stores differ"
                      name rows)))
        sizes

let interp_of (name : string) (sp : Gen.spec) : unit =
  match
    ( List.find_opt (fun ((n, _), _) -> String.equal n name)
        Extracted.annotated_nf,
      List.assoc_opt name Monotypes.vs_interps )
  with
  | None, _ -> fail (name ^ ": no annotated term")
  | _, None -> fail (name ^ ": no vs_interp")
  | Some ((_, _), opt_term), Some vs ->
      List.iter
        (fun rows ->
           let w = Gen.workload sp ~rows ~ops:5 ~only:None in
           guard (Printf.sprintf "%s/%d vs interp" name rows) (fun () ->
               let final =
                 Eval.interp_command
                   (Gen.locals_of w.Gen.store)
                   (Gen.locals_of w.Gen.env)
                   opt_term in
               let iget n = Eval.get_local final n in
               if vs (lookup_of w) iget then incr matched
               else
                 fail
                   (Printf.sprintf
                      "%s at %d rows: compiled opt differs from the interpreter"
                      name rows)))
        sizes

(* ---------- the same three checks, on MIXED workloads ----------

   The sweep measures a workload no other table uses: a long op list at a
   declared write fraction, with the writes paired in a slot pool so the table
   stays at `rows`.  A workload that nothing checks is a workload that can be
   wrong, and the way it would be wrong is subtle -- a removal that misses, or
   a churn key that collides with the body -- so src = opt and
   compiled = interpreter are re-made on it at every fraction.

   What this does NOT by itself establish is that the reads still hit, which
   is the flaw the slot pool exists to prevent.  That is guaranteed by
   construction: the churn addresses keys rows..rows+63 and every read kind
   addresses [0, rows), so the two ranges are disjoint.  Gen.churn_slots and
   the stationarity table are the other two legs of it. *)
let mixed_of (name : string) (sp : Gen.spec) : unit =
  List.iter
    (fun writes ->
       match Gen.mixed sp ~rows:50 ~ops:400 ~writes with
       | None -> ()
       | Some w ->
           let what = Printf.sprintf "%s/%d%% mixed" name writes in
           (match List.assoc_opt name Monotypes.agreements with
            | None -> fail (name ^ ": no generated program")
            | Some agree ->
                guard (what ^ " agree") (fun () ->
                    if agree (lookup_of w) then incr mixed_agreed
                    else fail (what ^ ": src and opt stores differ")));
           (match
              (List.find_opt (fun ((n, _), _) -> String.equal n name)
                 Extracted.annotated_nf,
               List.assoc_opt name Monotypes.vs_interps)
            with
            | Some ((_, _), opt_term), Some vs ->
                guard (what ^ " vs interp") (fun () ->
                    let final =
                      Eval.interp_command
                        (Gen.locals_of w.Gen.store)
                        (Gen.locals_of w.Gen.env)
                        opt_term in
                    let iget n = Eval.get_local final n in
                    if vs (lookup_of w) iget then incr mixed_matched
                    else fail (what ^ ": compiled opt differs from the interpreter"))
            | _ -> fail (name ^ ": no annotated term or vs_interp")))
    [ 0; 1; 10; 50 ]

(* and the author transcriptions that have been monomorphized so far.
   Parity is the expected result: the compiler is supposed to arrive back at
   what the author built, so a difference is a bug in the transcription or in
   the backend, not a finding. *)
let authors () : unit =
  List.iter
    (fun (name, check) ->
       match List.assoc_opt name Gen.specs with
       | None -> fail (name ^ ": no spec for the transcription")
       | Some sp ->
           let compare_on (what : string) (w : Gen.workload) : unit =
             guard what (fun () ->
                 if check w then incr authored
                 else
                   fail
                     (what
                      ^ ": the author transcription and the compiled optimized \
                         column disagree")) in
           List.iter
             (fun rows ->
                compare_on
                  (Printf.sprintf "%s/%d author" name rows)
                  (Gen.workload sp ~rows ~ops:5 ~only:None))
             sizes;
           (* and on the MIXED workloads, because the sweep measures the
              author column on those and nothing else checked it there *)
           List.iter
             (fun writes ->
                match Gen.mixed sp ~rows:50 ~ops:400 ~writes with
                | None -> ()
                | Some w ->
                    compare_on
                      (Printf.sprintf "%s/%d%% mixed author" name writes) w)
             [ 0; 1; 10; 50 ])
    Authors.checks

let () =
  (* `compiled.exe time [sizes]` measures; with no argument it CHECKS, so a
     measurement is never the thing that runs by accident.

     A structure setting may appear anywhere in the arguments, exactly as
     main.exe takes one, so that any single-setting table can be taken under
     `trees` or `hashes` as well.  It is pulled out first so it composes with
     the size lists.  `matched` reads all three itself and ignores it; the
     checks run all three too. *)
  let argv =
    List.filter
      (fun a ->
         match Count.structures_of_string a with
         | Some st -> Count.structures := st; false
         | None -> true)
      (Array.to_list Sys.argv) in
  match argv with
  | _ :: "time" :: rest ->
      Timing.run (List.filter_map int_of_string_opt rest);
      exit 0
  | _ :: "threeway" :: rest ->
      Timing.threeway (List.filter_map int_of_string_opt rest);
      exit 0
  | _ :: "writes" :: rest ->
      Timing.writes (List.filter_map int_of_string_opt rest);
      exit 0
  | _ :: "kinds" :: rest ->
      Timing.kinds (List.filter_map int_of_string_opt rest);
      exit 0
  | _ :: "work" :: rest ->
      Timing.work (List.filter_map int_of_string_opt rest);
      exit 0
  | _ :: "matched" :: rest ->
      Timing.matched (List.filter_map int_of_string_opt rest);
      exit 0
  | _ :: "sweep" :: rest ->
      Timing.sweep (List.filter_map int_of_string_opt rest);
      exit 0
  | _ :: "scale" :: rest ->
      Timing.scale (List.filter_map int_of_string_opt rest);
      exit 0
  | _ :: "stationary" :: rest ->
      Timing.stationary_report (List.filter_map int_of_string_opt rest);
      exit 0
  | _ -> ();
  (* ALL FOUR CHECKS UNDER ALL THREE SETTINGS.  Rt.SelMap and Rt.SelSet put a
     choice of storage behind one interface, and the thing that has to be
     established about such an interface is that it does not change what a
     program COMPUTES -- only what the program costs.  So each setting gets
     its own full pass: the readers accept their inputs, the generated
     equality still decides, src still equals opt, the compiled column still
     equals the interpreter, and each author transcription still equals the
     compiled optimized column.  `hashes` is the demanding one, because a walk
     over a hashed store has no order and anything built by insertion from one
     has to be order-insensitive to survive it. *)
  List.iter
    (fun st ->
       Count.structures := st;
       setting := Count.structures_name st;
       reads := 0; yes := 0; no := 0; agreed := 0; matched := 0; authored := 0;
       mixed_agreed := 0; mixed_matched := 0;
       let before = List.length !failures in
       List.iter
         (fun (name, sp) ->
            readers_of name sp;
            agree_of name sp;
            interp_of name sp;
            mixed_of name sp)
         Gen.specs;
       authors ();
       Printf.printf
         "%-6s: %d reader runs; equality agreed on %d equal and %d unequal \
          pairs; src = opt on %d runs; compiled = interpreter on %d runs; \
          author = compiled on %d runs (%d of 10 transcriptions); \
          mixed: src = opt on %d, = interpreter on %d; %d failures\n"
         !setting !reads !yes !no !agreed !matched !authored
         (List.length Authors.done_so_far)
         !mixed_agreed !mixed_matched
         (List.length !failures - before))
    [ Count.Typed; Count.Trees; Count.Hashes ];
  List.iter (fun s -> Printf.printf "  %s\n" s) (List.rev !failures);
  if !failures <> [] then exit 1
