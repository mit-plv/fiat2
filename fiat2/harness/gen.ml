(* Workloads.

   One spec per subject, each supplying exactly the free names that
   report.ml reads off the term -- an environment entry for every free EVar
   and a store entry for every free ELoc.  A missing name would not fail:
   get_local returns VUnit and the program would quietly do nothing, so the
   two lists are worth checking against each other when a subject changes.

   SHAPE OF A WORKLOAD.  Two phases, kept separate so the measurement can
   separate them:

     build   brings the table to [rows] rows.  For the four subjects whose
             table is introduced empty by SLetConstrained, that is [rows]
             insert queries, and the optimized program pays its index
             maintenance here.  For the four whose table arrives in the
             environment it is the initial list, and the optimized program
             pays once, before the loop, to build its indexes from it.

     ops     [ops] queries of each kind the subject dispatches on, round
             robin -- or of one named kind, which is how bench.ml finds out
             which read is responsible for a curve.

   Running a subject twice, once with ops = 0 and once with ops = k, and
   subtracting, gives the cost of the op phase alone.  That is the number
   the optimizer is about; the build number is what it charges for it.

   SELECTIVITY IS A CHOICE, AND IT IS THE ONE THAT MATTERS.  A read whose
   ANSWER is a constant fraction of the table is linear in the table however
   it is indexed, so a generator that asked for one would measure nothing
   but its own arithmetic.  Every bucket below -- floors, topics, keys --
   therefore grows with the table, keeping a bucket's size bounded, which is
   the regime the source programs' own callers are in:
   getRequiredActionProviderById returns one row.  Where a subject has a
   read that is inherently proportional (NamedCache's sizeInBytes over the
   whole cache, Keycloak's getRequiredActionProviderList), it is kept as it
   is, because a maintained aggregate is exactly what the optimizer offers
   for it.

   Jenkins's two short-token kinds are the other exception, and a different
   kind of one: a substring scan's answer is whatever matches, and no index
   is claimed for it.  What they measure is which BRANCH runs -- see the
   note beside them. *)

open Value

type workload = {
  store : (string * value) list;
  env : (string * value) list;
}

type spec = {
  queries_var : string;                            (* env name of the query list *)
  store : (string * value) list;                   (* the ambient store *)
  table : int -> (string * value) list;            (* a preloaded table, or none *)
  build : int -> value list;                       (* queries that grow the table *)
  kinds : (string * (int -> int -> value)) list;   (* name, rows -> index -> query *)
  (* Which of those kinds WRITE to the table.  Declared rather than detected,
     because the one consumer that needs it cannot detect it: bench times an op
     phase by appending op queries to the build, so timing a read with more
     operations is sound and timing a WRITE with more operations silently
     measures a table that grew while it was being measured.  A kind named here
     is never scaled. *)
  mutating : string list;
}

(* records must be built in the canonical field order, because that is the
   order interp_expr's ERecord produces and the order value comparison
   reads *)
let rcd (l : (string * value) list) : value = VRecord (Eval.record_sort l)

let s x = VString x
let i x = VInt x

(* a key index spread across the table rather than walking it in order, so
   that a probe is not accidentally measuring locality *)
let spread (n : int) (j : int) : int = if n <= 0 then 0 else j * 7919 mod n

(* one bucket per [bucket_size] rows, so that a bucketed read answers with a
   bounded number of rows however large the table is *)
let bucket_size = 8
let buckets (rows : int) : int = max 1 (rows / bucket_size)

(* the row a destructive op takes out, walking down from the top so that it
   never collides with the spread the reads use *)
let victim (rows : int) (j : int) : int = if rows <= 0 then 0 else (rows - 1 - j) mod rows

let outputs_only = [ ("outputs", VList []) ]
let no_table _ = []
let no_build _ = []

(* ---------- keycloak: one list, two unique keys ---------- *)

let keycloak =
  let row j =
    rcd [ ("id", s (Printf.sprintf "i%d" j)); ("alias", s (Printf.sprintf "a%d" j));
          ("name", s (Printf.sprintf "n%d" j)) ] in
  let q kind k = rcd [ ("kind", i kind); ("k", s k); ("new_action", row 0) ] in
  { queries_var = "queries"; store = outputs_only; table = no_table;
    build = (fun rows ->
      List.init rows (fun j ->
        rcd [ ("kind", i 0); ("k", s ""); ("new_action", row j) ]));
    kinds =
      [ ("byId", fun rows j -> q 1 (Printf.sprintf "i%d" (spread rows j)));
        ("byAlias", fun rows j -> q 2 (Printf.sprintf "a%d" (spread rows j)));
        ("wholeList", fun _ _ -> q 3 "") ];
    mutating = [] }

(* ---------- named cache: a unique key and a maintained total ---------- *)

let named_cache =
  let row j = rcd [ ("k", s (Printf.sprintf "k%d" j)); ("size", i (1 + (j mod 97))) ] in
  let q kind k = rcd [ ("kind", i kind); ("k", s k); ("node", row 0) ] in
  { queries_var = "ops"; store = outputs_only; table = no_table;
    build = (fun rows ->
      List.init rows (fun j ->
        rcd [ ("kind", i 1); ("k", s ""); ("node", row j) ]));
    kinds =
      [ ("get", fun rows j -> q 3 (Printf.sprintf "k%d" (spread rows j)));
        ("sizeInBytes", fun _ _ -> q 2 "");
        ("delete", fun rows j -> q 0 (Printf.sprintf "k%d" (victim rows j))) ];
    mutating = [ "delete" ] }

(* ---------- area registry: bucketed on floor, keyed on id ---------- *)

let area_registry =
  let row rows j =
    rcd [ ("id", s (Printf.sprintf "i%d" j)); ("name", s (Printf.sprintf "n%d" j));
          ("floor", VOption (Some (s (Printf.sprintf "f%d" (j mod buckets rows))))) ] in
  let q rows kind k fl =
    rcd [ ("kind", i kind); ("k", s k); ("fl", s fl); ("new_area", row rows 0) ] in
  { queries_var = "queries"; store = outputs_only; table = no_table;
    build = (fun rows ->
      List.init rows (fun j ->
        rcd [ ("kind", i 0); ("k", s ""); ("fl", s ""); ("new_area", row rows j) ]));
    kinds =
      [ ("byId", fun rows j -> q rows 2 (Printf.sprintf "i%d" (spread rows j)) "");
        ("byFloor", fun rows j -> q rows 3 "" (Printf.sprintf "f%d" (j mod buckets rows)));
        ("remove", fun rows j -> q rows 1 (Printf.sprintf "i%d" (victim rows j)) "") ];
    mutating = [ "remove" ] }

(* ---------- lookin: a membership test over a preloaded table ----------

   The component writes nothing: the function list is handed to the entity
   at construction and only read, so the table arrives in the environment
   as Cluster's does.

   Row 0 is named "mode", the literal the second read probes at, so that
   read hits; the varying read probes at names that are mostly absent, so
   both branches of both tests are exercised.  Which branch is taken costs
   the same either way -- the unindexed form is a flatmap over the whole bag
   whether or not it finds anything, and the probe is a tree descent -- so
   this is about exercising the program, not about the numbers. *)

let lookin =
  let row j = rcd [ ("name", if j = 0 then s "mode" else s (Printf.sprintf "f%d" j)) ] in
  let q kind k = rcd [ ("kind", i kind); ("k", s k) ] in
  { queries_var = "queries"; store = outputs_only;
    table = (fun rows -> [ ("functions_tbl", VList (List.init rows row)) ]);
    build = no_build;
    kinds =
      [ ("varyingKey", fun rows j -> q 0 (Printf.sprintf "f%d" (spread rows j)));
        ("literalKey", fun _ _ -> q 1 "") ];
    mutating = [] }

(* ---------- user search: a unique key and a trigram index ----------

   Names are four digits wide so that a three-digit token is a real trigram
   and selects a handful of rows; a token that matched a constant fraction
   of the table would be linear however it was indexed. *)

let user_search =
  let row j =
    rcd [ ("id", s (Printf.sprintf "u%d" j));
          ("fullName", s (Printf.sprintf "user%04d" j)) ] in
  let q kind k = rcd [ ("kind", i kind); ("k", s k); ("new_user", row 0) ] in
  { queries_var = "queries";
    store = ("suggested", VSet VSet.empty) :: outputs_only;
    table = no_table;
    build = (fun rows ->
      List.init rows (fun j ->
        rcd [ ("kind", i 0); ("k", s ""); ("new_user", row j) ]));
    kinds =
      [ ("byId", fun rows j -> q 2 (Printf.sprintf "u%d" (spread rows j)));
        ("suggest", fun _ j -> q 3 (Printf.sprintf "%03d" (spread 1000 j)));
        (* Three characters is the shortest token the trigram rule probes
           for, so these two kinds sit on the other side of its guard: the
           kind above always probes, these two always take the FALLBACK
           branch, which is the source query scanning the table as a set.

           They are here because that branch is the only reader keeping the
           list alive, and with every token three characters long it never
           ran -- so its cost was absent from the measurement rather than
           small in it.

           The two differ in what they match, which separates the two costs
           the fallback pays.  A token that occurs in no name isolates the
           fixed part: coercing the table to a set, and walking it.  A token
           drawn from the names also pays for the answer. *)
        ("suggestMiss", fun _ _ -> q 3 "zz");
        ("suggestShort", fun _ j -> q 3 (Printf.sprintf "%02d" (spread 100 j)));
        ("remove", fun rows j -> q 1 (Printf.sprintf "u%d" (victim rows j))) ];
    mutating = [ "remove" ] }

(* ---------- cluster: conjunctive reads over a preloaded table ----------

   One partition in five has no leader, so that the availability read has
   something to exclude. *)

let cluster =
  let row rows j =
    rcd [ ("topic", s (Printf.sprintf "t%d" (j mod buckets rows))); ("partition", i j);
          ("leader", if j mod 5 = 0 then VOption None
                     else VOption (Some (i (j mod buckets rows)))) ] in
  let q kind topic part node =
    rcd [ ("kind", i kind); ("topic", s topic); ("part", i part); ("node", i node) ] in
  { queries_var = "queries"; store = outputs_only;
    table = (fun rows -> [ ("partitions_tbl", VList (List.init rows (row rows))) ]);
    build = no_build;
    kinds =
      [ ("forTopic", fun rows j -> q 0 (Printf.sprintf "t%d" (j mod buckets rows)) 0 0);
        ("forNode", fun rows j -> q 1 "" 0 (j mod buckets rows));
        ("onePartition", fun rows j ->
           let p = spread rows j in
           q 2 (Printf.sprintf "t%d" (p mod buckets rows)) p 0);
        ("available", fun rows j -> q 3 (Printf.sprintf "t%d" (j mod buckets rows)) 0 0) ];
    mutating = [] }

(* ---------- window store: a range, a key, and an expiry ---------- *)

let window_store =
  let row rows j =
    rcd [ ("time", i j); ("k", s (Printf.sprintf "k%d" (j mod buckets rows)));
          ("val", s "v") ] in
  let q rows kind lo hi key =
    rcd [ ("kind", i kind); ("lo", i lo); ("hi", i hi); ("key", s key);
          ("new_rec", row rows 0) ] in
  { queries_var = "queries"; store = outputs_only;
    table = (fun rows -> [ ("segments_tbl", VList (List.init rows (row rows))) ]);
    build = no_build;
    kinds =
      [ (* fetchAll(timeFrom, timeTo): a window of bounded width *)
        ("fetchAll", fun rows j -> let lo = spread rows j in q rows 0 lo (lo + bucket_size) "");
        (* fetch(key, timeFrom, timeTo): one key, same bounded window.

           The key is one that IS in the window -- the key of the row at its
           lower bound -- because fetch is asked about a key its caller
           expects to find, and because of what the row column compares.
           Kafka descends its inner map once per segment and enumerates only
           what matches; the derived form enumerates the window and filters
           it.  With a key drawn independently of the window almost every
           query would answer nothing, and the comparison would be an empty
           answer against a window scan, which measures the generator's aim
           rather than the composite-key gap. *)
        ("fetch", fun rows j ->
           let lo = spread rows j in
           q rows 1 lo (lo + bucket_size)
             (Printf.sprintf "k%d" (lo mod buckets rows)));
        ("put", fun rows j ->
           rcd [ ("kind", i 2); ("lo", i 0); ("hi", i 0); ("key", s "");
                 ("new_rec", row rows (rows + j)) ]);
        (* removeExpiredSegments(): advances the live bound by one *)
        ("expire", fun rows j -> q rows 3 j 0 "") ];
    mutating = [ "put"; "expire" ] }

(* ---------- range delete: a band read and a band delete ---------- *)

let range_delete =
  let row j = rcd [ ("id", i j); ("price", i j) ] in
  let q typ lo hi order =
    rcd [ ("type", i typ); ("new_order", order); ("lo", i lo); ("hi", i hi) ] in
  { queries_var = "queries"; store = outputs_only;
    table = (fun rows -> [ ("orders_tbl", VList (List.init rows row)) ]);
    build = no_build;
    kinds =
      [ ("countBand", fun rows j ->
           let lo = spread rows j in q 1 lo (lo + bucket_size) (row 0));
        ("insert", fun rows j -> q 0 0 0 (row (rows + j)));
        ("deleteBand", fun _ j -> q 2 j (j + 1) (row 0)) ];
    mutating = [ "insert"; "deleteBand" ] }

(* ---------- item deletion: whole-row membership over a preloaded table ----------

   ItemDeletion.registrations is a Set<Item> asked contains(item), so the
   question is about a WHOLE ROW and there is no key to probe with.  The table
   is preloaded, as lookin's and cluster's are: registrations is handed the
   items that are in flight, and the ops then test, add and remove.

   Rows carry two fields because the read is whole-row equality.  With one
   field the test would be a membership test on a key, which a dictionary
   could serve -- and the subject exists precisely to isolate the read that
   no dictionary can serve.

   Four kinds, because the two configurations differ on reads in one
   direction and on writes in the other, and a single blended figure would
   hide both:

     containsHit / containsMiss  the read.  Hit and miss are separated
       because the unindexed form coerces the whole table either way while
       the probe does not, so a miss is the cleanest view of the fixed cost;
       and because OCaml's Set.mem returns early on a hit, which a
       hit-only measurement would read as a smaller saving than there is.
     register     the cons that becomes a set insert -- what the choice costs.
     deregister   the filter, which is linear over the list and linear over
       the member, and is therefore the write the choice does not touch.  It
       is here so that the write side is not represented only by its worst
       case. *)

let item_deletion =
  let row j =
    rcd [ ("name", s (Printf.sprintf "n%d" j));
          ("parent", s (Printf.sprintf "p%d" (j / 4))) ] in
  let q kind item = rcd [ ("kind", i kind); ("item", item) ] in
  { queries_var = "queries"; store = outputs_only;
    table = (fun rows -> [ ("items_tbl", VList (List.init rows row)) ]);
    build = no_build;
    kinds =
      [ ("containsHit", fun rows j -> q 0 (row (spread rows j)));
        ("containsMiss", fun rows j -> q 0 (row (rows + j)));
        ("register", fun rows j -> q 1 (row (rows + j)));
        ("deregister", fun rows j -> q 2 (row (victim rows j))) ];
    mutating = [ "register"; "deregister" ] }

(* ---------- the table ---------- *)

let specs =
  [ ("keycloak", keycloak); ("named_cache", named_cache);
    ("area_registry", area_registry); ("lookin", lookin);
    ("user_search", user_search); ("cluster", cluster);
    ("window_store", window_store); ("range_delete", range_delete);
    ("item_deletion", item_deletion) ]

let workload (sp : spec) ~(rows : int) ~(ops : int) ~(only : string option) : workload =
  let kinds =
    match only with
    | None -> sp.kinds
    | Some k -> List.filter (fun (name, _) -> name = k) sp.kinds in
  let phase =
    List.concat_map
      (fun j -> List.map (fun (_, f) -> f rows j) kinds)
      (List.init ops (fun j -> j)) in
  { store = sp.store;
    env = (sp.queries_var, VList (sp.build rows @ phase)) :: sp.table rows }

let of_subject (name : string) ~(rows : int) ~(ops : int) : workload option =
  match List.assoc_opt name specs with
  | None -> None
  | Some sp -> Some (workload sp ~rows ~ops ~only:None)

let locals_of (l : (string * value) list) : Eval.locals =
  List.fold_left (fun m (k, v) -> Eval.SMap.add k v m) Eval.SMap.empty l
