(* The compiled side, and for now the test that its marshalling and its
   generated equality are real.

   A type-check says the generated code is well typed.  It does not say the
   readers read the right constructor, nor that the equality decides
   anything -- a read-twice check would pass if eq_ always said true.  So
   there are two tests, both over the generators' own workloads:

     run    every reader accepts its input, and re-reading it compares equal
     cross  the generated equality AGREES WITH Value.compare on two
            different workloads, and the counts below say how many pairs
            each answer was decided on -- so "both answers exercised" is
            reported rather than assumed

   What is still missing is the way back: there is no generated to_value, so
   nothing here compares a compiled program's final store against the
   interpreted run.  The plan is the other direction -- convert the
   interpreted store with these same readers and compare with eq_ -- which
   needs no new mechanism, only a program to compare. *)

let failures = ref []
let runs = ref 0
let yes = ref 0
let no = ref 0

let lookup_of (w : Gen.workload) (n : string) : Value.t option =
  match List.assoc_opt n w.Gen.env with
  | Some v -> Some v
  | None -> List.assoc_opt n w.Gen.store

let guard (what : string) (f : unit -> unit) : unit =
  try f () with e -> failures := (what ^ ": " ^ Printexc.to_string e) :: !failures

let () =
  List.iter
    (fun (name, sp) ->
       match List.assoc_opt name Monotypes.readers with
       | None -> failures := (name ^ ": no generated reader") :: !failures
       | Some (run, cross) ->
           List.iter
             (fun rows ->
                let w = Gen.workload sp ~rows ~ops:3 ~only:None in
                incr runs;
                guard (Printf.sprintf "%s/%d run" name rows) (fun () ->
                    run (lookup_of w)))
             [ 7; 50 ];
           (* two workloads of different sizes, so the values really differ *)
           let a = Gen.workload sp ~rows:7 ~ops:3 ~only:None
           and b = Gen.workload sp ~rows:50 ~ops:3 ~only:None in
           guard (name ^ " cross") (fun () ->
               cross (lookup_of a) (lookup_of b) yes no);
           (* and the same workload twice, so the equal answer is exercised *)
           guard (name ^ " cross-same") (fun () ->
               cross (lookup_of a) (lookup_of a) yes no))
    Gen.specs;
  Printf.printf
    "marshalling: %d reader runs; equality agreed with Value.compare on %d equal and %d unequal pairs; %d failures\n"
    !runs !yes !no (List.length !failures);
  List.iter (fun s -> Printf.printf "  %s\n" s) (List.rev !failures);
  if !failures <> [] then exit 1
