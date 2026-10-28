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
     threeway [n ...]
                    all three programs in one table: the query as written,
                    the program derived from it, and the author's own code,
                    compared on the one cost that crosses to the author
     alternatives [n ...]
                    a SIDE NOTE, kept out of the other tables: what the
                    selector's own choice is worth, by running each
                    configuration a file pins against the one the selector
                    picks.  Both are sound; only the index list differs

   With no argument it runs the report, which is what the README's one-line
   recipe does.

   Any command may be preceded or followed by a STRUCTURE SETTING -- typed,
   trees or hashes -- which says what every point-access collection is charged
   as, on BOTH sides of the author comparison.  count.ml says what the three
   mean; the default is typed, which charges only what the type system
   licenses.  `baseline matched` prints all three in sequence, which is the
   comparison this parameter exists for. *)

let () =
  let argv = Array.to_list Sys.argv in
  (* pull the setting out of the arguments wherever it appears, so that it
     composes with the size lists the commands take *)
  let argv =
    List.filter
      (fun a ->
         match Count.structures_of_string a with
         | Some s -> Count.structures := s; false
         | None -> true)
      argv in
  match argv with
  | _ :: "report" :: _ | [ _ ] -> Report.run ()
  | _ :: "check" :: _ -> Differential.run ()
  | _ :: "bench" :: rest -> Bench.run (List.filter_map int_of_string_opt rest)
  | _ :: "csv" :: rest -> Bench.csv (List.filter_map int_of_string_opt rest)
  | _ :: "timing" :: rest -> Bench.timing rest
  | _ :: "baseline" :: rest ->
      Bench.baseline (List.filter_map int_of_string_opt rest)
  | _ :: "threeway" :: rest ->
      Bench.threeway (List.filter_map int_of_string_opt rest)
  | _ :: "matched" :: rest ->
      Bench.matched (List.filter_map int_of_string_opt rest)
  | _ :: "alternatives" :: rest ->
      Bench.alternatives_cost (List.filter_map int_of_string_opt rest)
  | _ :: other :: _ ->
      Printf.eprintf
        "unknown command %s; expected report, check, bench, csv, timing, \
         baseline, threeway, matched or alternatives, optionally with typed, \
         trees or hashes\n"
        other;
      exit 2
  | [] -> ()
