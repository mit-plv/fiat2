(* Entry point.  One executable with four jobs, so that the shared modules
   (the evaluator, the generators) are compiled once and none of them can
   quietly diverge from the others.

     report         what is in the extracted terms; evaluates nothing
     check          the differential test against the Gallina interpreter
     bench [n ...]  run the subjects and count
     csv [n ...]    the same op-phase series as data, one row per point
     timing [subject kind rows]
                    a diagnostic: how precise the wall clock actually is,
                    which decides whether seconds can be compared against
                    hand-written code at all
     baseline [n ...]
                    the originals' own structures, beside what the
                    optimizer derived
     alternatives [n ...]
                    a SIDE NOTE, kept out of the other tables: what the
                    selector's own choice is worth, by running each
                    configuration a file pins against the one the selector
                    picks.  Both are sound; only the index list differs

   With no argument it runs the report, which is what the README's one-line
   recipe does. *)

let () =
  match Array.to_list Sys.argv with
  | _ :: "report" :: _ | [ _ ] -> Report.run ()
  | _ :: "check" :: _ -> Differential.run ()
  | _ :: "bench" :: rest -> Bench.run (List.filter_map int_of_string_opt rest)
  | _ :: "csv" :: rest -> Bench.csv (List.filter_map int_of_string_opt rest)
  | _ :: "timing" :: rest -> Bench.timing rest
  | _ :: "baseline" :: rest ->
      Bench.baseline (List.filter_map int_of_string_opt rest)
  | _ :: "alternatives" :: rest ->
      Bench.alternatives_cost (List.filter_map int_of_string_opt rest)
  | _ :: other :: _ ->
      Printf.eprintf
        "unknown command %s; expected report, check, bench, csv, timing, \
         baseline or alternatives\n" other;
      exit 2
  | [] -> ()
