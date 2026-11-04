(* The originals' own structures, monomorphized.

   WHY THIS FILE EXISTS.  baseline.ml transcribes the authors' structures
   against the boxed dynamic value, which is what makes the comparison FAIR
   while our side is interpreted: both columns pay the same representation
   costs, so a ratio compares two programs.  Once our side is compiled that
   stops being true -- a monomorphic record against an association-list walk
   is a comparison of REPRESENTATIONS, and it is the same confound the
   matched columns exist to defuse (harness/README, named_cache/get at
   0.50x).  So the author side has to be monomorphized too.

   HOW IT STAYS HONEST.  Each module below is the SAME transcription
   baseline.ml holds, with its citation carried over verbatim, changed only
   where the representation requires it: `field "name" r` becomes `r.f_name`,
   and the `keyed` wrapper becomes a structure over a monomorphic key.  The
   algorithm is not touched.  And each one is checked against the compiled
   optimized column's store, so a transcription that computes something else
   is caught before any of its numbers are read -- which is what the `agree`
   column already earned its place doing in baseline.ml.

   TYPES BY ALIAS, NOT BY NUMBER.  The generated record names are positional:
   adding a subject renumbers them.  So these modules name
   In_<subject>.t_queries and t_row, which the generator emits for exactly
   this purpose.

   ONE THING NOT YET CARRIED OVER.  baseline.ml takes its structure from
   Count.structures, so that `matched` can run both sides as trees or as
   hashes.  The modules below fix a tree, which is what the `typed` column
   charges a set as -- TSet carries no kind.  Re-plumbing that parameter to
   the compiled side is work, and until it is done only the `typed` column
   is available here. *)

open Monotypes

(* a set of strings, as a tree: what the typed column charges a TSet as,
   since TSet carries no kind.  Its comparison is rt.ml's, so it is priced
   exactly as the generated structures are. *)
module SSet = Set.Make (struct
  type t = string

  let compare = Rt.cmp_string
end)

module Lookin = struct
  let name = "lookin"

  (* home-assistant/core, commit e751cd2b,
     homeassistant/components/lookin/entity.py:91-94:

       self._device = device
       self._function_names = {function.name for function in self._device.functions}

     read at entity.py:152, :154 and media_player.py:87, :107, all four times
     as `name in self._function_names`.

     A Python set is a hash set, so a membership test is one key equality and
     ENUMERATES NO ROW: it yields a boolean.  The row column is therefore 0 on
     the author's side and 0 on the optimizer's, and the only cost is the
     source form's, which scans.  What this line measures is that the derived
     structure is the same one the programmer wrote by hand -- and the set is
     the whole of it, because the list does not survive the derivation here
     either: `self._device` is read only at :94. *)
  let run (functions : In_lookin.t_functions_tbl)
      (queries : In_lookin.t_queries) : string list =
    let names =
      List.fold_left
        (fun s (r : In_lookin.t_row) -> SSet.add r.f_name s)
        SSet.empty functions in
    let outputs = ref [] in
    let say (s : string) = outputs := s :: !outputs in
    let has (k : string) = SSet.mem k names in
    List.iter
      (fun (q : row70) ->
         match q.f_kind with
         (* media_player.py:87 -- the key varies with the loop *)
         | 0 -> say (if has q.f_k then "supported" else "unsupported")
         (* media_player.py:107 -- the key is a literal *)
         | _ -> say (if has "mode" then "has-mode" else "no-mode"))
      queries;
    !outputs
end

(* ---------- what has been monomorphized so far ----------

   One module, as a pilot: the pattern is proved end to end -- including the
   agreement check -- before the other ten are rewritten, because a rewrite
   that loses fidelity to the cited source is the one failure this cannot
   detect. *)

let done_so_far = [ Lookin.name ]

(* ---------- and the check ----------

   Each transcription is run on the same inputs as the compiled optimized
   column and its store compared.  Parity is the expected result: the
   compiler is supposed to arrive back at what the author built, so a
   difference is a bug in the transcription (or in the backend) and not a
   finding. *)

let lookup_of (w : Gen.workload) (n : string) : Value.t option =
  match List.assoc_opt n w.Gen.env with
  | Some v -> Some v
  | None -> List.assoc_opt n w.Gen.store

let check_lookin (w : Gen.workload) : bool =
  let get n =
    match lookup_of w n with
    | Some v -> v
    | None -> failwith ("missing input " ^ n) in
  let mine = Monotypes.store_opt_lookin (lookup_of w) in
  let theirs =
    Lookin.run
      (Monotypes.In_lookin.f_functions_tbl (get "functions_tbl"))
      (Monotypes.In_lookin.f_queries (get "queries")) in
  (* `outputs` is built by prepending, on both sides, so the orders agree *)
  Rt.eq_list Rt.eq_string mine theirs

let checks : (string * (Gen.workload -> bool)) list = [ ("lookin", check_lookin) ]
