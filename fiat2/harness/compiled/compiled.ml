(* The compiled side, and for now the test that its marshalling is real.

   A type-check says the generated readers are well typed; it does not say
   they agree with the workloads the generators actually produce.  This runs
   every reader over those workloads, at two sizes, and reports what raised.

   What it cannot check yet is the way BACK: there is no generated
   to_value, so nothing here compares a converted input against the boxed
   one it came from.  That arrives with the expression codegen, which is
   what decides the shape a compiled program's final store has. *)

let failures = ref []
let ran = ref 0

let () =
  List.iter
    (fun rows ->
       List.iter
         (fun (name, sp) ->
            let w = Gen.workload sp ~rows ~ops:3 ~only:None in
            let lookup (n : string) : Value.t option =
              match List.assoc_opt n w.Gen.env with
              | Some v -> Some v
              | None -> List.assoc_opt n w.Gen.store in
            match List.assoc_opt name Monotypes.readers with
            | None -> failures := (name ^ ": no generated reader") :: !failures
            | Some run -> (
                incr ran;
                try run lookup
                with e ->
                  failures :=
                    Printf.sprintf "%s at %d rows: %s" name rows
                      (Printexc.to_string e)
                    :: !failures))
         Gen.specs)
    [ 7; 50 ];
  Printf.printf "marshalling: %d runs, %d failures\n" !ran
    (List.length !failures);
  List.iter (fun s -> Printf.printf "  %s\n" s) (List.rev !failures);
  if !failures <> [] then exit 1
