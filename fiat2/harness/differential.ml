(* The differential test.

   harness/eval.ml is hand-written and unverified, and it sits directly
   underneath the performance claim: if it computed something other than
   what the semantics says, every number bench.ml prints would be about a
   different program.  So it is run against the Gallina interpreter, which
   IS the semantics, on the real subject programs -- source and optimized --
   over the generated workloads, and the two final stores are compared
   through the bijection in bridge.ml.

   Sizes are small on purpose.  The oracle's dictionaries are association
   lists and its naturals are unary, so it is quadratic where the evaluator
   is logarithmic; what is being checked is agreement, which does not need a
   large table, and the empty and one-row cases are the ones worth having.

   A failure here is a bug in eval.ml, in bridge.ml, or in a generator --
   never in the development, which does not depend on any of them. *)

open Extracted

let sizes = [ 0; 1; 2; 7; 23 ]
let op_counts = [ 0; 1; 5 ]

(* both sides as one sorted association list, so they can be compared *)
let mine (c : command) (w : Gen.workload) : (string * Value.value) list =
  let final = Eval.interp_command (Gen.locals_of w.store) (Gen.locals_of w.env) c in
  Eval.SMap.bindings final

let theirs (c : command) (w : Gen.workload) : (string * Value.value) list =
  let conv l = List.map (fun (k, v) -> (k, Bridge.to_ref v)) l in
  ref_run (conv w.store) (conv w.env) c
  |> List.map (fun (k, v) -> (k, Bridge.of_ref v))
  |> List.sort (fun (a, _) (b, _) -> String.compare a b)

let same (a : (string * Value.value) list) (b : (string * Value.value) list) : bool =
  List.length a = List.length b
  && List.for_all2 (fun (k, v) (k', v') -> k = k' && Value.eqb v v') a b

let show (l : (string * Value.value) list) : string =
  String.concat "; " (List.map (fun (k, v) -> k ^ " = " ^ Value.to_string v) l)

let run () =
  Printf.printf
    "Each subject, source and optimized, against the Gallina interpreter.\n\
     Tables of %s rows, op phases of %s queries per kind.\n\n"
    (String.concat "/" (List.map string_of_int sizes))
    (String.concat "/" (List.map string_of_int op_counts));
  let failures = ref 0 and checks = ref 0 in
  List.iter
    (fun ((name, src), opt) ->
       let sp = List.assoc name Gen.specs in
       List.iter
         (fun rows ->
            List.iter
              (fun ops ->
                 let w = Gen.workload sp ~rows ~ops ~only:None in
                 List.iter
                   (fun (variant, c) ->
                      incr checks;
                      let m = mine c w and t = theirs c w in
                      if not (same m t) then begin
                        incr failures;
                        Printf.printf
                          "MISMATCH %s/%s at rows=%d ops=%d\n  evaluator: %s\n  oracle:    %s\n"
                          name variant rows ops (show m) (show t)
                      end)
                   [ ("src", src); ("opt", opt) ])
              op_counts)
         sizes;
       Printf.printf "  %-16s ok\n" name)
    subjects;
  Printf.printf "\n%d configurations checked, %d mismatches\n" !checks !failures;
  if !failures > 0 then exit 1
