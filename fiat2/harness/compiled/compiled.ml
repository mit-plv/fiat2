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
let reads = ref 0
let yes = ref 0
let no = ref 0
let agreed = ref 0
let matched = ref 0

let sizes = [ 7; 50 ]

let lookup_of (w : Gen.workload) (n : string) : Value.t option =
  match List.assoc_opt n w.Gen.env with
  | Some v -> Some v
  | None -> List.assoc_opt n w.Gen.store

let fail (s : string) : unit = failures := s :: !failures

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

let () =
  (* `compiled.exe time [sizes]` measures; with no argument it CHECKS, so a
     measurement is never the thing that runs by accident *)
  match Array.to_list Sys.argv with
  | _ :: "time" :: rest ->
      Timing.run (List.filter_map int_of_string_opt rest);
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
  | _ -> ();
  List.iter
    (fun (name, sp) ->
       readers_of name sp;
       agree_of name sp;
       interp_of name sp)
    Gen.specs;
  Printf.printf
    "compiled: %d reader runs; equality agreed on %d equal and %d unequal \
     pairs; src = opt on %d runs; compiled = interpreter on %d runs; %d \
     failures\n"
    !reads !yes !no !agreed !matched (List.length !failures);
  List.iter (fun s -> Printf.printf "  %s\n" s) (List.rev !failures);
  if !failures <> [] then exit 1
