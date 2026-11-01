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
    store = ("suggested", VSet (Value.sempty ())) :: outputs_only;
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
        (* A token with MORE THAN ONE trigram, which is the only kind that
           tells the two trigram rules apart.

           Every kind above uses a token of exactly three characters, so it
           has exactly one trigram and there is nothing for an intersecting
           rule to narrow: probing one bucket and probing all of them are
           the same probe.  This kind takes five characters out of the
           middle of a name, "user0042" -> "r0042", so the token has three
           trigrams whose buckets differ by two orders of magnitude:

             "r00"  every name whose digits begin 00  -- about rows/16
             "004"  every name whose digits begin 004 -- about rows/160
             "042"  the one or two names containing 042

           So the first bucket alone leaves a hundred candidates to resolve
           and recheck, and the intersection of the three leaves one or two.
           That is the asymmetry gin_trgm_consistent exploits for LIKE, and
           without a kind like this one our measurement could not see it. *)
        ("suggestLong", fun rows j ->
           q 3 (String.sub (Printf.sprintf "user%04d" (spread rows j)) 3 5));
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

(* ---------- entity_registry: a THREE-attribute conjunctive read ----------

   THE ONE PLACE THIS DIRECTORY BREAKS ITS OWN SELECTIVITY RULE, AND WHY.
   Every other bucket above grows with the table so that a bucketed read
   answers a bounded number of rows.  `domain` does not: it is the entity
   component domain -- light, sensor, switch -- and Home Assistant has a few
   dozen of them however many entities an installation has.  So the number of
   domains here is a CONSTANT (16) and a domain's bucket grows with the table,
   which is the regime the source is actually in.

   That is what the arity-three measurement turns on.  A configuration that
   can only probe the first conjunct narrows to one domain and then scans it,
   which is rows/16 -- LINEAR.  The composite key answers the same read with
   one probe.  Against Kafka_Cluster, where bucket_size kept the residual
   filter bounded and the composite key therefore bought a constant, this
   subject is where it buys an exponent -- and the difference is a property of
   the data, not of the rule.

   `platform` is the integration domain (hue, zwave), also bounded, and varies
   independently of the domain; `unique_id` is unique per row, so the triple
   names exactly one entity, which is what async_get_entity_id asks for.  One
   entity in five has no device, so the device read has a None bucket nothing
   probes. *)

let entity_registry =
  let domains = 16 and platforms = 16 in
  let dom j = Printf.sprintf "d%d" (j mod domains) in
  let plat j = Printf.sprintf "p%d" (j / domains mod platforms) in
  let row rows j =
    rcd [ ("entity_id", s (Printf.sprintf "e%d" j));
          ("id", s (Printf.sprintf "i%d" j));
          ("domain", s (dom j)); ("platform", s (plat j));
          ("unique_id", s (Printf.sprintf "u%d" j));
          ("device_id", if j mod 5 = 0 then VOption None
                        else VOption (Some (s (Printf.sprintf "dv%d" (j mod buckets rows))))) ] in
  let q rows kind eid dm pl uid dev fresh =
    rcd [ ("kind", i kind); ("eid", s eid); ("dom", s dm); ("plat", s pl);
          ("uid", s uid); ("dev", s dev);
          ("new_entry", row rows fresh) ] in
  { queries_var = "queries"; store = outputs_only;
    table = (fun rows -> [ ("entries_tbl", VList (List.init rows (row rows))) ]);
    build = no_build;
    kinds =
      [ (* get_entry(id) (:1070) *)
        ("getEntry", fun rows j ->
           q rows 0 (Printf.sprintf "i%d" (spread rows j)) "" "" "" "" 0);
        (* get_entries_for_device_id(device_id) (:1074) *)
        ("forDevice", fun rows j ->
           q rows 1 "" "" "" "" (Printf.sprintf "dv%d" (j mod buckets rows)) 0);
        (* async_get_entity_id(domain, platform, unique_id) (:1264), asked
           about an entity that IS registered, which is what both of its
           callers do *)
        ("getEntityId", fun rows j ->
           let p = spread rows j in
           q rows 2 "" (dom p) (plat p) (Printf.sprintf "u%d" p) "" 0);
        (* _index_entry (:1015), reached by async_get_or_create.  The entity
           is a FRESH one -- registering an entity that already exists takes
           the update path, which is not modelled. *)
        ("register", fun rows j -> q rows 3 "" "" "" "" "" (rows + j)) ];
    mutating = [ "register" ] }

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

(* ---------- min delete: a cached minimum under deletes that do and do not
   remove it ----------

   Ex_MinDelete's guard rule keeps the cached minimum unless the delete removes
   it, and RECOMPUTES when it does.  The two delete kinds separate those two
   branches, which is the whole measurement -- a blended figure would hide
   both:

     deleteMin     always removes the current minimum, so always pays the
                   recompute.  Prices are 0..rows-1 and the j-th op removes
                   price j, which IS the minimum once 0..j-1 are gone, because
                   the ops accumulate within one run (Bench.secs_per_op_of
                   never scales a mutating kind, exactly so that this holds).
     deleteOther   removes from the TOP end, where it can never be the
                   minimum, so the cached value survives and the rule pays one
                   comparison.

   readMin is the read the index exists for, and insert is the write the
   choice costs.  With ops_per_kind = 20 against rows in the thousands,
   deleteMin cannot exhaust the table. *)

let min_delete =
  let row j = rcd [ ("id", i j); ("price", i j) ] in
  let q typ price order =
    rcd [ ("type", i typ); ("price", i price); ("new_order", order) ] in
  { queries_var = "queries"; store = outputs_only;
    table = (fun rows -> [ ("orders_tbl", VList (List.init rows row)) ]);
    build = no_build;
    kinds =
      [ ("readMin", fun _ _ -> q 2 0 (row 0));
        ("insert", fun rows j -> q 1 0 (row (rows + j)));
        ("deleteMin", fun _ j -> q 0 j (row 0));
        ("deleteOther", fun rows j -> q 0 (rows - 1 - j) (row 0)) ];
    mutating = [ "insert"; "deleteMin"; "deleteOther" ] }

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

(* ---------- sat4j literal storage: one declared key, eight reads ----------

   The only subject taken from someone else's benchmark suite, so its query
   mix is theirs and not ours: eight reads over one table, of which seven ask
   about one variable's record and one counts the table.

   Two things the writes have to get right, and both bite if they do not.

   `updateLevel` is a delete-then-insert pair under value semantics, so the
   row it inserts must carry THE SAME var as the row it removes.  A new_rec
   at a different key would leave two rows with one var, the declared-key
   guard the elaboration inserted would reject the write, and the op would
   silently do nothing -- measuring the guard rather than the update.  Hence
   `row_at v`, which varies the level and holds the key.

   Selectivity needs no arrangement here: `var` is declared unique, so every
   one of the seven key reads answers exactly one row however the table
   grows.  That is the regime SAT4J's own callers are in -- they reach these
   fields by variable number. *)

let sat4j =
  let row_at v lvl =
    rcd [ ("var", i v); ("level", i lvl); ("reason", i (v * 3));
          ("pos_watches", i (v * 5)); ("neg_watches", i (v * 7));
          ("undos", i (v mod 11)) ] in
  let row j = row_at j (1 + (j mod 31)) in
  let q kind v = rcd [ ("kind", i kind); ("v", i v); ("new_rec", row 0) ] in
  { queries_var = "queries"; store = outputs_only; table = no_table;
    build = (fun rows ->
      List.init rows (fun j ->
        rcd [ ("kind", i 0); ("v", i 0); ("new_rec", row j) ]));
    kinds =
      [ ("findRecord", fun rows j -> q 3 (spread rows j));
        ("belongsToPool", fun rows j -> q 4 (spread rows j));
        ("size", fun _ _ -> q 5 0);
        ("getLevel", fun rows j -> q 6 (spread rows j));
        ("getReason", fun rows j -> q 7 (spread rows j));
        ("getUndos", fun rows j -> q 8 (spread rows j));
        ("getPosWatches", fun rows j -> q 9 (spread rows j));
        ("getNegWatches", fun rows j -> q 10 (spread rows j));
        ("remove", fun rows j -> q 1 (victim rows j));
        (* the key is held; only the level changes *)
        ("updateLevel", fun rows j ->
           let v = spread rows j in
           rcd [ ("kind", i 2); ("v", i v); ("new_rec", row_at v 99) ]) ];
    mutating = [ "remove"; "updateLevel" ] }

(* ---------- dependent plugins: a nested-loop join over real state ----------

   PluginManager.resolveDependentPlugins() loops over `plugins` inside
   `plugins`, so its cost is quadratic in a field the program KEEPS.  Here
   the edges are their own table (see the subject's Faithfulness note), so
   one operation is the whole resolve: for every plugin, how many other
   plugins declare a dependency on it, and how many of those declarations
   are optional.

   Both collections grow together, which is what makes the measurement mean
   anything: `rows` plugins and `rows` dependency edges, each plugin
   declaring one dependency on a pseudo-random other plugin.  A plugin's
   DEPENDENTS are then bounded on average however large the table grows --
   the selectivity every other subject here is also arranged to have, because
   a read whose answer is a constant fraction of the table is linear whatever
   is installed.

   `deleted` is false throughout and `optional` alternates.  Neither varies
   with the table, because they are residual filters on the bucket rather
   than keys, and what is being measured is the bucket lookup. *)

let dependent_plugins =
  let edge j =
    rcd [ ("dependent", s (Printf.sprintf "p%d" j));
          ("dependency", s (Printf.sprintf "p%d" (spread (max 1 j) j)));
          ("optional", VBool (j mod 2 = 0));
          ("deleted", VBool false) ] in
  let plugin j = rcd [ ("name", s (Printf.sprintf "p%d" j)) ] in
  { queries_var = "queries"; store = outputs_only;
    table = (fun rows ->
      [ ("deps_tbl", VList (List.init rows edge));
        ("plugins_tbl", VList (List.init rows plugin)) ]);
    build = no_build;
    (* one query is one resolveDependentPlugins() *)
    kinds = [ ("resolveAll", fun _ _ -> i 0) ];
    mutating = [] }

(* ---------- composite_key: the composite index's own regression file ----------

   Extracted for its two MAINTENANCE rules.  The triple is unique per row (k3
   is the row index), and k1/k2 have BOUNDED cardinality for the same reason
   entity_registry's domain does -- so a configuration that can only probe one
   attribute scans a bucket that grows. *)

let composite_key =
  let k1 j = Printf.sprintf "a%d" (j mod 16) in
  let k2 j = Printf.sprintf "b%d" (j / 16 mod 16) in
  let row _ j =
    rcd [ ("k1", s (k1 j)); ("k2", s (k2 j)); ("k3", i j); ("v", s "v") ] in
  let q rows kind a b c fresh =
    rcd [ ("kind", i kind); ("a", s a); ("b", s b); ("c", i c);
          ("new_item", row rows fresh) ] in
  { queries_var = "queries"; store = outputs_only;
    table = (fun rows -> [ ("items_tbl", VList (List.init rows (row rows))) ]);
    build = no_build;
    kinds =
      [ ("readInOrder", fun rows j ->
           let p = spread rows j in q rows 0 (k1 p) (k2 p) p 0);
        ("readPermuted", fun rows j ->
           let p = spread rows j in q rows 1 (k1 p) (k2 p) p 0);
        ("readPermuted2", fun rows j ->
           let p = spread rows j in q rows 2 (k1 p) (k2 p) p 0);
        ("insert", fun rows j -> q rows 3 "" "" 0 (rows + j));
        (* the delete's key is the key OF A ROW, so it removes exactly one *)
        ("deleteAtKey", fun rows j ->
           let p = victim rows j in q rows 4 (k1 p) (k2 p) p 0) ];
    mutating = [ "insert"; "deleteAtKey" ] }

(* ---------- composite_keyed_delete: two deletes on one table ----------

   The table is declared with a unique key and carries a composite index on
   (k1, k2), and the program deletes in both shapes: at the whole composite
   key, which the index's own rule serves with no declaration, and at the
   declared key, which only the pair's gated rule can serve.

   The composite key is UNIQUE PER ROW -- k1 cycles through 16 values and k2
   counts the cycles -- so a bucket holds one row and the read is a probe
   that returns one row however large the table is.  That keeps the read's
   number about the probe rather than about the bucket.

   The table starts empty, as every SLetConstrained table does, so the rows
   arrive through the build phase as inserts.  The build is therefore not
   free on either side: the source's uniqueness guard is a scan and the
   optimized one is a probe, which is its own measured difference. *)

let composite_keyed_delete =
  let k1 j = Printf.sprintf "a%d" (j mod 16) in
  let k2 j = Printf.sprintf "b%d" (j / 16) in
  let row j =
    rcd [ ("id", s (Printf.sprintf "i%d" j)); ("k1", s (k1 j)); ("k2", s (k2 j));
          ("v", s "v") ] in
  let q kind a b k fresh =
    rcd [ ("kind", i kind); ("a", s a); ("b", s b); ("k", s k);
          ("new_item", row fresh) ] in
  { queries_var = "queries"; store = outputs_only; table = no_table;
    build = (fun rows -> List.init rows (fun j -> q 1 "" "" "" j));
    kinds =
      [ ("readAtKey", fun rows j ->
           let p = spread rows j in q 0 (k1 p) (k2 p) "" 0);
        ("insert", fun rows j -> q 1 "" "" "" (rows + j));
        (* at the declared key: the pair's gated rule.  Kind 3 names the
           keyed delete in BOTH programs, so the two specs below differ only
           in the kind the first does not have. *)
        ("deleteById", fun rows j ->
           let p = victim rows j in q 3 "" "" (Printf.sprintf "i%d" p) 0) ];
    mutating = [ "insert"; "deleteById" ] }

(* and the same table WITH the composite-key delete as well, which is where
   the two deletes are seen to coexist -- and where the one that cannot
   maintain the primary-key member keeps the row list installed, so every
   write pays a linear pass over it *)
let composite_two_deletes =
  let k1 j = Printf.sprintf "a%d" (j mod 16) in
  let k2 j = Printf.sprintf "b%d" (j / 16) in
  let row j =
    rcd [ ("id", s (Printf.sprintf "i%d" j)); ("k1", s (k1 j)); ("k2", s (k2 j));
          ("v", s "v") ] in
  let q kind a b k fresh =
    rcd [ ("kind", i kind); ("a", s a); ("b", s b); ("k", s k);
          ("new_item", row fresh) ] in
  { queries_var = "queries"; store = outputs_only; table = no_table;
    build = (fun rows -> List.init rows (fun j -> q 1 "" "" "" j));
    kinds =
      [ ("readAtKey", fun rows j ->
           let p = spread rows j in q 0 (k1 p) (k2 p) "" 0);
        ("insert", fun rows j -> q 1 "" "" "" (rows + j));
        ("deleteAtKey", fun rows j ->
           let p = victim rows j in q 2 (k1 p) (k2 p) "" 0);
        ("deleteById", fun rows j ->
           let p = victim rows j in q 3 "" "" (Printf.sprintf "i%d" p) 0) ];
    mutating = [ "insert"; "deleteAtKey"; "deleteById" ] }

let specs =
  [ ("keycloak", keycloak); ("named_cache", named_cache);
    ("area_registry", area_registry); ("lookin", lookin);
    ("user_search", user_search); ("cluster", cluster);
    ("entity_registry", entity_registry);
    ("window_store", window_store); ("range_delete", range_delete);
    ("min_delete", min_delete); ("composite_key", composite_key);
    ("composite_keyed_delete", composite_keyed_delete);
    ("composite_two_deletes", composite_two_deletes);
    ("item_deletion", item_deletion); ("sat4j", sat4j);
    ("dependent_plugins", dependent_plugins) ]

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
