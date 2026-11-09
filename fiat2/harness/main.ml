(* Entry point for the interpreted side.  One executable so that the shared
   modules -- the evaluator, the generators, the counters -- are compiled once
   and cannot quietly diverge.  README.md lists the commands.

   Any command may be preceded or followed by a STRUCTURE SETTING (typed,
   trees, hashes), a name alphabet, the fuzzy column's two axes, or share=K;
   they are pulled out of argv below wherever they appear, so that they
   compose with the size lists the commands take.  count.ml says what the
   three settings charge. *)

let () =
  let argv = Array.to_list Sys.argv in
  (* pull the setting out of the arguments wherever it appears, so that it
     composes with the size lists the commands take *)
  let argv =
    List.filter
      (fun a ->
         match Count.structures_of_string a with
         | Some s -> Count.structures := s; false
         | None -> (
             (* and the name alphabet, the same way: a parameter of the
                WORKLOAD rather than of the storage, declared in gen.ml *)
             match Gen.names_of_string a with
             | Some m -> Gen.names_mode := m; false
             | None -> (
                 (* and the fuzzy column's two axes, the same way: how much
                    structure its vocabulary shares, and how many words the
                    indexed text holds *)
                 match Gen.titles_of_string a with
                 | Some m -> Gen.titles_mode := m; false
                 | None -> (
                     match Gen.words_of_string a with
                     | Some w -> Gen.title_words := w; false
                     | None -> (
                         (* share=K selects the funnel vocabulary AND its
                            group size, since neither is useful alone *)
                         match Gen.share_of_string a with
                         | Some k ->
                             Gen.share := k;
                             Gen.titles_mode := Gen.Funnel;
                             false
                         | None -> true)))))
      argv in
  match argv with
  | _ :: "report" :: _ | [ _ ] -> Report.run ()
  | _ :: "check" :: _ -> ignore (Probe.run ()); Differential.run ()
  | _ :: "stores" :: _ -> ignore (Probe.run ())
  | _ :: "types" :: _ -> Codegen.run ()
  | _ :: "bench" :: rest -> Bench.run (List.filter_map int_of_string_opt rest)
  | _ :: "csv" :: rest ->
      (* `only=a,b` restricts the subjects; anything else numeric is a size *)
      let only =
        List.concat_map
          (fun a ->
             match String.index_opt a '=' with
             | Some i when String.sub a 0 i = "only" ->
                 String.split_on_char ','
                   (String.sub a (i + 1) (String.length a - i - 1))
             | _ -> [])
          rest in
      Bench.csv ~only (List.filter_map int_of_string_opt rest)
  | _ :: "timing" :: rest -> Bench.timing rest
  | _ :: "baseline" :: rest ->
      Bench.baseline (List.filter_map int_of_string_opt rest)
  | _ :: "threeway" :: rest ->
      Bench.threeway (List.filter_map int_of_string_opt rest)
  | _ :: "matched" :: rest ->
      Bench.matched (List.filter_map int_of_string_opt rest)
  | _ :: "alternatives" :: rest ->
      Bench.alternatives_cost (List.filter_map int_of_string_opt rest)
  | _ :: "enumerate" :: rest ->
      let only =
        List.concat_map
          (fun a ->
             match String.index_opt a '=' with
             | Some i when String.sub a 0 i = "only" ->
                 String.split_on_char ','
                   (String.sub a (i + 1) (String.length a - i - 1))
             | _ -> [])
          rest in
      Bench.enumerate_cost ~only (List.filter_map int_of_string_opt rest)
  | _ :: other :: _ ->
      Printf.eprintf
        "unknown command %s; expected report, stores, types, check, bench, csv, \
         timing, baseline, threeway, matched, alternatives or enumerate, \
         optionally with typed, trees or hashes\n"
        other;
      exit 2
  | [] -> ()
