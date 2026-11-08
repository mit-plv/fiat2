(* Entry point.  One executable with four jobs, so that the shared modules
   (the evaluator, the generators) are compiled once and none of them can
   quietly diverge from the others.

     report         what is in the extracted terms; evaluates nothing
     types          the OCaml type declarations the compiled backend needs:
                    one record per Conquord record type, with a structural
                    compare and hash, and a Map/Hashtbl/Set instance per key
                    type with dict_kind deciding tree or hash.  Writes to
                    stdout; harness/monotypes.ml is where it goes, and
                    `dune build @check` is what type-checks it
     stores         the dictionary store against a reference map: that it is a
                    finite map on the keys these subjects use, and that one
                    delete removes one binding.  It exists because a library
                    got that last one wrong -- see probe.ml
     check          the store check, then the differential test against the
                    Gallina interpreter
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
     enumerate [only=<name>,<name>] [n ...]
                    the same question asked exhaustively: every
                    configuration eval/Enumerate.v admits, measured, and
                    the selector's pick ranked among them

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
  | _ :: "ops" :: _ -> Opcount.run ()
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
