(* Entry point.  One executable with three jobs, so that the shared modules
   (the evaluator, the generators) are compiled once and none of the three
   can quietly diverge from the others.

     report         what is in the extracted terms; evaluates nothing
     check          the differential test against the Gallina interpreter
     bench [n ...]  run the subjects and count

   With no argument it runs the report, which is what the README's one-line
   recipe does. *)

let () =
  match Array.to_list Sys.argv with
  | _ :: "report" :: _ | [ _ ] -> Report.run ()
  | _ :: "check" :: _ -> Differential.run ()
  | _ :: "bench" :: rest -> Bench.run (List.filter_map int_of_string_opt rest)
  | _ :: other :: _ ->
      Printf.eprintf "unknown command %s; expected report, check or bench\n" other;
      exit 2
  | [] -> ()
