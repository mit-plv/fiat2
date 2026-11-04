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

   AND THE STRUCTURE IS THE RUN'S, not each author's.  baseline.ml takes its
   storage from Count.structures so that `matched` can run both sides as trees
   or as hashes; the modules below used to fix whatever their author wrote, so
   only the `typed` column was available on this side.  They now go through
   Rt.SelMap and Rt.SelSet, which the GENERATED column goes through too, and
   what the author wrote is recorded as a Count.situation at each creation
   site.  compiled/timing.ml's `matched` is the table that needed it. *)

open Monotypes

(* The structures the transcriptions build, over a monomorphic string key.
   Their comparison and hash are rt.ml's, so they are priced exactly as the
   generated structures are -- which is the whole point of this file.

   WHICH SITUATION FOR WHICH AUTHOR.  A Java HashMap and a Python dict or set
   say the key order is never read, so those are created `Licensed` -- a hash
   under `typed` and `hashes`, a tree only under the conservative floor.  A
   Java NavigableMap or TreeMap whose order none of the MODELLED operations
   reads is `Unlicensed`: a tree under `typed`, hashed only under `hashes`,
   where the column is a hypothetical about a smaller program rather than a
   claim the author chose badly.  An original that really does range-query
   stays ordered under every setting, and for those the module is Map.Make
   directly, because `split` is the operation and no hash answers it. *)
module SKey = struct
  type t = string

  let compare = Rt.cmp_string
  let equal a b = Rt.cmp_string a b = 0
  let hash = Rt.hash_string
end

(* One selectable map and one selectable set on string keys, shared by every
   transcription below.  There used to be three modules here -- a Set.Make, a
   CCHashTrie and a Map.Make -- because each transcription stored what its
   author wrote.  The storage is now the run's `structures` setting, so what
   the author wrote is said at the CREATION SITE as a Count.situation instead:
   `Licensed` where the original is a HashMap or HashSet, `Unlicensed` where it
   is a TreeMap whose order none of the modelled operations reads.  That is the
   same word, resolved by the same function, as the generated column uses. *)
module SSet = Rt.SelSet (SKey)
module SSel = Rt.SelMap (SKey)

(* baseline.ml's kprobe: a probe that YIELDS a row charges one row, where a
   membership test charges none because it yields a boolean.  Reproduced, so
   the rows column means the same thing on both sides. *)
let lookup_of (w : Gen.workload) (n : string) : Value.t option =
  match List.assoc_opt n w.Gen.env with
  | Some v -> Some v
  | None -> List.assoc_opt n w.Gen.store

let probe (o : 'a option) : 'a option =
  (match o with Some _ -> Count.visit 1 | None -> ());
  o

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
        (SSet.make Count.Licensed) functions in
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

(* ---------- keycloak: one list and two maps on two unique keys ---------- *)

module Keycloak = struct
  let name = "keycloak"

  (* keycloak, commit dd4ae31d, CachedRealm.java:301, read at
     RealmAdapter.java:1572 and :1579:

       requiredActionProviderList = model.getRequiredActionProvidersStream()
                                         .collect(Collectors.toList());
       for (RequiredActionProviderModel action : requiredActionProviderList) {
           requiredActionProviders.put(action.getId(), action);
           requiredActionProvidersByAlias.put(action.getAlias(), action);
       }

     One list and two HashMaps on two unique attributes, maintained together.
     The list is kept because getRequiredActionProviderList() hands it back.

     `size` is explicit because java.util.ArrayList keeps its own: size() is
     O(1) there where List.length is O(n) here, and the whole-list read in this
     subject is a COUNT.  So the field is the author's structure and not a
     convenience -- and it is exactly what the optimizer derives as CountAgg,
     which makes this the cleanest parity line in the file. *)
  type state = {
    mutable rows : In_keycloak.t_row list;   (* requiredActionProviderList *)
    mutable size : int;                      (* ArrayList's own size field *)
    mutable by_id : In_keycloak.t_row SSel.t;    (* requiredActionProviders *)
    mutable by_alias : In_keycloak.t_row SSel.t; (* ...ByAlias *)
  }

  let run (queries : In_keycloak.t_queries) : string list =
    let st =
      { rows = []; size = 0; by_id = SSel.make Count.Licensed;
        by_alias = SSel.make Count.Licensed } in
    let outputs = ref [] in
    let say (n : int) = outputs := Rt.string_of_int_c n :: !outputs in
    List.iter
      (fun (q : In_keycloak.t_queries_elem) ->
         match q.f_kind with
         (* the write the translation adds; see the subject's Faithfulness note.
            The author builds once, so this is the put loop above, run per row.
            NO uniqueness check: Keycloak's model guarantees it. *)
         | 0 ->
             let row = q.f_new_action in
             st.rows <- row :: st.rows;
             st.size <- st.size + 1;
             st.by_id <- SSel.add row.f_id row st.by_id;
             st.by_alias <- SSel.add row.f_alias row st.by_alias
         (* getRequiredActionProviderById(id) -> ...get(id) *)
         | 1 ->
             say (match probe (SSel.get q.f_k st.by_id) with
                  | Some _ -> 1 | None -> 0)
         (* getRequiredActionProviderByAlias(alias) -> ...ByAlias().get(alias) *)
         | 2 ->
             say (match probe (SSel.get q.f_k st.by_alias) with
                  | Some _ -> 1 | None -> 0)
         (* getRequiredActionProviderList(), counted: ArrayList.size() *)
         | _ -> say st.size)
      queries;
    !outputs
end

(* ---------- named cache: an ordered map and a maintained total ---------- *)

module NamedCache = struct
  let name = "named_cache"

  (* kafka, commit 995cfcf9,
     streams/.../state/internals/NamedCache.java:44 and :49:

       private final NavigableMap<Bytes, LRUNode> cache = new TreeMap<>();
       private long currentSizeBytes = 0;

     corrected at :178/:192/:249/:281 and read at :196.  A keyed structure and
     a maintained SUM over it, which is the pair the optimizer derives as
     [UniqueDictIdx "k"; SumAgg "size"].

     An ORDERED map, not a trie: the author chose a NavigableMap, so the typed
     column charges the tree they wrote.  None of the operations this subject
     models reads the key order -- the real class needs it for operations the
     subject does not model -- so a hashed variant would be a hypothetical
     about a smaller program, not a claim that the author chose badly. *)
  type state = {
    mutable cache : In_named_cache.t_row SSel.t;
    mutable total : int;                     (* currentSizeBytes *)
  }

  let run (ops : In_named_cache.t_ops) : string list =
    let st = { cache = SSel.make Count.Unlicensed; total = 0 } in
    let outputs = ref [] in
    let say (n : int) = outputs := Rt.string_of_int_c n :: !outputs in
    (* remove(key), maintaining the total: the node has to be READ to know what
       to subtract, which is the one row a delete touches, and is why the
       optimizer's own delete probes rather than scans *)
    let remove (k : string) =
      match probe (SSel.find_opt k st.cache) with
      | Some (old : In_named_cache.t_row) ->
          st.total <- st.total - old.f_size;
          st.cache <- SSel.remove k st.cache
      | None -> () in
    List.iter
      (fun (q : In_named_cache.t_ops_elem) ->
         match q.f_kind with
         (* delete(key) -- :273 *)
         | 0 -> remove q.f_k
         (* put(key, value) -- :174-192: evict the old binding, then insert *)
         | 1 ->
             let node = q.f_node in
             let k = node.f_k in
             remove k;
             st.cache <- SSel.add k node st.cache;
             st.total <- st.total + node.f_size
         (* sizeInBytes() -- :196: a field read, no row *)
         | 2 -> say st.total
         (* get(key) -- :200-201 *)
         | _ ->
             say (match probe (SSel.find_opt q.f_k st.cache) with
                  | Some _ -> 1
                  | None -> 0))
      ops;
    !outputs
end

(* ---------- item deletion: a hash set of whole ROWS ---------- *)

module ItemDeletion = struct
  let name = "item_deletion"

  (* jenkins, commit 81dc9a3e,
     core/src/main/java/jenkins/model/queue/ItemDeletion.java:74, :129, :149, :165:

       private final Set<Item> registrations = new HashSet<>();
       contains(item)   -> registrations.contains(item)
       register(item)   -> registrations.add(item)
       deregister(item) -> registrations.remove(item)

     The elements are ROWS and there is no key, which is the whole reason this
     subject exists: the question is about a whole row, so no dictionary can
     answer it and TableRep is the only index that applies.

     Every operation here ENUMERATES no rows -- a membership test yields
     nothing, an add and a remove write -- so the row column is 0 on this side
     and on the optimizer's, and the source's whole cost is its coercion of the
     table.  What separates the two sides is entirely in `cmps`: a hash
     membership is one equality where our balanced tree is a descent. *)
  module Key = struct
    type t = In_item_deletion.t_row

    let compare = In_item_deletion.cmp_row
    let equal = In_item_deletion.eq_row
    let hash = In_item_deletion.hash_row
  end

  (* A HashSet keyed on the ROW.  This is the subject the missing set_kind
     showed up in: the author's storage is a hash and ours was a tree under
     every setting, so the gap was a per-subject ratio rather than a number.
     Both sides now hold what the setting names -- Licensed here because the
     author wrote `new HashSet<>()` -- and `hashes` is the column in which the
     two agree. *)
  module Reg = Rt.SelSet (Key)

  let run (items : In_item_deletion.t_items_tbl)
      (queries : In_item_deletion.t_queries) : string list =
    (* The items in flight arrive in the ENVIRONMENT rather than through build
       queries.  Missing this is what the `agree` column caught on the first
       run of baseline.ml: the transcription started empty, so every
       containsHit said "free" while the subject said "deleting". *)
    let reg =
      ref
        (List.fold_left
           (fun t (r : In_item_deletion.t_row) -> Reg.add r t)
           (Reg.make Count.Licensed) items) in
    let outputs = ref [] in
    let say (s : string) = outputs := s :: !outputs in
    List.iter
      (fun (q : In_item_deletion.t_queries_elem) ->
         let item = q.f_item in
         match q.f_kind with
         (* THE WHOLE ROW IS THE KEY -- registrations.contains(item) asks
            about a row and not an attribute -- so a hash of it walks the whole
            record, which Rt's generated hash does per field rather than by a
            convention. *)
         | 0 -> say (if Reg.mem item !reg then "deleting" else "free")
         | 1 -> reg := Reg.add item !reg
         | _ -> reg := Reg.remove item !reg)
      queries;
    !outputs
end

(* ---------- user search: a keyed map, and a scan the author kept ---------- *)

module UserSearch = struct
  let name = "user_search"

  (* jenkins, commit 81dc9a3e, hudson/model/User.java:1106 and
     hudson/search/*:

       private final ConcurrentMap<String, User> byName = new ConcurrentHashMap<>();

     find(id) is that map's get.  suggest(token) is NOT indexed by the author:
     it walks the users testing name.contains(token), which is why this is the
     one subject where the optimizer should come out AHEAD rather than level --
     it derives a trigram index the author never built. *)
  let run (suggested0 : In_user_search.t_suggested)
      (queries : In_user_search.t_queries) :
      In_user_search.t_outputs * In_user_search.t_suggested =
    let by_id = ref (SSel.make Count.Licensed) in
    let outputs = ref [] in
    let suggested = ref suggested0 in
    let say (n : int) = outputs := Rt.string_of_int_c n :: !outputs in
    List.iter
      (fun (q : In_user_search.t_queries_elem) ->
         match q.f_kind with
         (* User.get(id, true) -> AllUsers.putIfAbsent *)
         | 0 ->
             let u = q.f_new_user in
             by_id := SSel.add u.f_id u !by_id
         (* AllUsers.remove(id) *)
         | 1 -> by_id := SSel.remove q.f_k !by_id
         (* find(id): the ConcurrentHashMap lookup *)
         | 2 ->
             say (match probe (SSel.get q.f_k !by_id) with
                  | Some _ -> 1 | None -> 0)
         (* suggest(token): the author's own scan over every user *)
         | _ ->
             let tok = q.f_k in
             (* The author's work is the scan: n users, one contains() each.
                Accumulating the hits is not theirs -- Jenkins hands back a
                List -- but the SUBJECT models the result as a set, and that
                modelling choice is upstream of both columns, so both sides
                pay for building one.

                Collected first and SORTED before the set is built, because
                building it as the scan finds the hits would make the charge
                depend on the order the structure happens to iterate: in
                baseline.ml that was 184 comparisons under a hash's bucket
                order against 246 under a tree's key order, for an identical
                answer.  A number that moves when the storage changes
                underneath it is measuring the harness. *)
             let hits = ref [] in
             SSel.iter
               (fun _ (u : In_user_search.t_row) ->
                 Count.visit 1;
                 if Rt.str_contains u.f_fullName tok then hits := u :: !hits)
               !by_id;
             suggested :=
               List.fold_left
                 (fun s u -> In_user_search.M_suggested.add u s)
                 (In_user_search.M_suggested.make Count.Unlicensed)
                 (List.sort In_user_search.cmp_row !hits))
      queries;
    (!outputs, !suggested)
end

(* ---------- area registry: a dict and a secondary index on floor ------ *)

module AreaRegistry = struct
  let name = "area_registry"

  (* home-assistant/core, commit e751cd2b.
     homeassistant/helpers/area_registry.py:169 (class AreaRegistryItems),
     with the write hooks in homeassistant/helpers/registry.py:38, :56, :61
     and area_registry.py:180, :199, :211.

     The dict and ONE secondary index, maintained by hand on every insert and
     every delete.  This is the only subject here whose writes are its own:
     the other eight build once.

     Two structural details are the author's and are transcribed as such.

     The secondary index stores KEYS, not rows -- `_floors_index[floor]` is a
     dict of ids -- so get_areas_for_floor resolves every posting through the
     primary dict.  Our index stores the rows themselves.  Both enumerate the
     same rows, so the row column is parity; HA pays a probe per posting
     where we pay the storage, and that is a backend's choice, which is why
     it shows up in cmps and not in rows.

     And _unindex_entry READS the row before removing it (area_registry.py:199),
     because the row is where the floor it has to unindex is written.  So a
     delete costs exactly one row on the author's side -- which is what the
     optimizer's keyed delete costs too, and is the line this subject exists
     for.

     Only _floors_index is modelled, as in the subject: _labels_index and
     _aliases_index key on each element of a per-row collection, which is the
     gap the survey recorded and nothing here builds. *)
  type state = {
    mutable data : In_area_registry.t_row SSel.t;   (* self.data *)
    mutable floors : unit SSel.t SSel.t;           (* _floors_index *)
  }

  let run (queries : In_area_registry.t_queries) : string list =
    let st = { data = SSel.make Count.Licensed;
               floors = SSel.make Count.Licensed } in
    let outputs = ref [] in
    let say (n : int) = outputs := Rt.string_of_int_c n :: !outputs in
    (* _index_entry: the primary dict, then the floor posting list *)
    let index_entry (key : string) (row : In_area_registry.t_row) =
      st.data <- SSel.add key row st.data;
      match row.f_floor with
      | None -> ()                                 (* `if ... is not None` *)
      | Some f ->
          let b =
            match SSel.get f st.floors with
            | Some b -> b
            | None -> SSel.make Count.Licensed in
          st.floors <- SSel.add f (SSel.add key () b) st.floors in
    (* _unindex_entry, then UserDict.__delitem__ (registry.py:61) *)
    let unindex_entry (key : string) =
      match probe (SSel.get key st.data) with
      | None -> ()                                 (* HA raises; nothing to do *)
      | Some (row : In_area_registry.t_row) ->
          (match row.f_floor with
           | None -> ()
           | Some f -> (
               match SSel.get f st.floors with
               | None -> ()
               | Some b ->
                   let b = SSel.remove key b in
                   (* `if not entries: del index[value]` -- registry.py:56 *)
                   st.floors <-
                     (if SSel.is_empty b then SSel.remove f st.floors
                      else SSel.add f b st.floors)));
          st.data <- SSel.remove key st.data in
    List.iter
      (fun (q : In_area_registry.t_queries_elem) ->
         match q.f_kind with
         (* __setitem__ with a fresh key: the build's insert *)
         | 0 ->
             let row = q.f_new_area in
             index_entry row.f_id row
         (* __delitem__ *)
         | 1 -> unindex_entry q.f_k
         (* async_get_area(area_id) -- area_registry.py:241, a dict get at :247 *)
         | 2 ->
             say (match probe (SSel.get q.f_k st.data) with
                  | Some _ -> 1 | None -> 0)
         (* get_areas_for_floor(floor), counted *)
         | _ ->
             say
               (match SSel.get q.f_fl st.floors with
                | None -> 0
                | Some b ->
                    SSel.fold
                      (fun key () acc ->
                        match probe (SSel.get key st.data) with
                        | Some _ -> acc + 1
                        | None -> acc)
                      b 0))
      queries;
    !outputs
end

(* ---------- the ordered helpers, shared by the two ordered subjects ---- *)

module IKey = struct
  type t = int

  let compare = Rt.cmp_int
  let equal a b = Rt.cmp_int a b = 0
  let hash = Rt.hash_int
end

module IMap = Map.Make (IKey)
module ISel = Rt.SelMap (IKey)

(* subMap(lo, true, hi, false): the entries in [lo, hi), by two splits.
   Map.split is the ordered-map primitive that Java's subMap is, with one
   difference worth stating: Java's is a lazy VIEW and this rebuilds the
   subtree, so it charges the author a few comparisons extra and no rows. *)
let sub_range (lo : int) (hi : int) (m : 'a IMap.t) : 'a IMap.t =
  let _, at_lo, above = IMap.split lo m in
  let below_hi, _, _ = IMap.split hi above in
  match at_lo with
  | Some v when lo < hi -> IMap.add lo v below_hi
  | _ -> below_hi

(* headMap(lo, false).clear(): keep [lo, inf).  One split, and no row is read
   -- the entries are unlinked, not inspected. *)
let keep_from (lo : int) (m : 'a IMap.t) : 'a IMap.t =
  let _, at_lo, above = IMap.split lo m in
  match at_lo with Some v -> IMap.add lo v above | None -> above

(* ---------- cluster: four maps, and no list ---------- *)

module Cluster = struct
  let name = "cluster"

  (* apache/kafka, commit 995cfcf9, common/Cluster.java:47-50, built at
     :142-:157 and :164-:184, read at :289, :298, :317, :326.

     Cluster has a field for every map and NO field for `partitions`, which is
     the erasure the subject is about; four probes, four buckets, no scan.

     Two things to read carefully.  The subject counts what each accessor
     RETURNS, so these walk the bucket they hand back, which is what :298's
     and :317's and :326's callers do.  Kafka also has partitionCountForTopic
     at :307, answering the count in O(1) from ArrayList.size(); that one the
     optimizer cannot match, since it would need a maintained aggregate PER
     BUCKET -- the dict-of-aggregates combinator this development
     deliberately does not build.  And onePartition is the other way round:
     the key is composite, `new TopicPartition(p.topic(), p.partition())`,
     Kafka has a map on it, and the optimizer probes one attribute and filters
     the bucket.

     THE COMPOSITE KEY IS A RECORD, and it is charged exactly as a generated
     two-field record is: the record's own node, then its fields in
     name-sorted order.  That is what baseline.ml's key2 built as a VRecord,
     and writing it out here is what keeps the two sides priced alike. *)
  module TPKey = struct
    (* fields in the order the type system keeps them: partition < topic *)
    type t = { partition : int; topic : string }

    let compare (a : t) (b : t) : int =
      Rt.cmp_node ();
      let c = Rt.cmp_int a.partition b.partition in
      if c <> 0 then c else Rt.cmp_string a.topic b.topic

    let equal a b = compare a b = 0

    let hash (x : t) : int =
      Rt.node ();
      let h = 37 in
      let h = (h * 31) + Rt.hash_int x.partition in
      let h = (h * 31) + Rt.hash_string x.topic in
      h
  end

  module TPSel = Rt.SelMap (TPKey)

  type row = In_cluster.t_row

  (* computeIfAbsent(k, _ -> new ArrayList<>()).add(p) *)
  let sbucket_add (h : row list SSel.t) (k : string) (r : row) : row list SSel.t =
    match SSel.get k h with
    | Some b -> SSel.add k (r :: b) h
    | None -> SSel.add k [ r ] h

  let ibucket_add (h : row list ISel.t) (k : int) (r : row) : row list ISel.t =
    match ISel.get k h with
    | Some b -> ISel.add k (r :: b) h
    | None -> ISel.add k [ r ] h

  (* the rows an accessor hands back, counted by its caller *)
  let scount (h : row list SSel.t) (k : string) : int =
    match SSel.get k h with
    | None -> 0                                   (* getOrDefault(k, List.of()) *)
    | Some b -> let n = List.length b in Count.visit n; n

  let icount (h : row list ISel.t) (k : int) : int =
    match ISel.get k h with
    | None -> 0
    | Some b -> let n = List.length b in Count.visit n; n

  let run (partitions : In_cluster.t_partitions_tbl)
      (queries : In_cluster.t_queries) : string list =
    let by_tp = ref (TPSel.make Count.Licensed) in
    let by_topic = ref (SSel.make Count.Licensed) in
    let available = ref (SSel.make Count.Licensed) in
    let by_node = ref (ISel.make Count.Licensed) in
    List.iter
      (fun (p : row) ->
         by_tp :=
           TPSel.add { TPKey.partition = p.f_partition; topic = p.f_topic } p
             !by_tp;
         by_topic := sbucket_add !by_topic p.f_topic p;
         match p.f_leader with
         | Some n ->
             (* `if (p.leader() == null) continue` -- :150 *)
             by_node := ibucket_add !by_node n p;
             available := sbucket_add !available p.f_topic p
         | None -> ())
      partitions;
    let outputs = ref [] in
    let say (n : int) = outputs := Rt.string_of_int_c n :: !outputs in
    List.iter
      (fun (q : In_cluster.t_queries_elem) ->
         match q.f_kind with
         | 0 -> say (scount !by_topic q.f_topic)
         | 1 -> say (icount !by_node q.f_node)
         | 2 ->
             say
               (match
                  probe
                    (TPSel.get
                       { TPKey.partition = q.f_part; topic = q.f_topic }
                       !by_tp)
                with
                | Some _ -> 1 | None -> 0)
         | _ -> say (scount !available q.f_topic))
      queries;
    !outputs
end

(* ---------- window store: two ordered levels ---------- *)

module WindowStore = struct
  let name = "window_store"

  (* apache/kafka, commit 995cfcf9, state/internals/InMemoryWindowStore.java:78,
     read at :398, :287, :221, :637.

     TWO ordered levels, time then key, which is the one place in this file
     where the author's structure is strictly richer than the derived one.
     The subject flattens the rows and the optimizer chooses the nesting: a
     Ranged dict on time whose buckets are unindexed bags.  So fetchAll is
     parity -- both walk the window -- and `fetch` is the gap: Kafka descends
     the inner map once per segment and enumerates only the rows that match.

     The outer level is the ordered one: subMap and headMap read its key
     order, so it is Map.Make under every setting.  The inner per-segment map
     is `Unlicensed`, for the same reason NamedCache's is -- the author's
     level is a ConcurrentNavigableMap, so it is the tree they wrote under
     `typed`, and none of the operations this subject models reads that order,
     so `hashes` may hash it. *)
  let run (segments0 : In_window_store.t_segments_tbl)
      (queries : In_window_store.t_queries) : string list =
    let segments = ref (IMap.empty : In_window_store.t_row SSel.t IMap.t) in
    let put (r : In_window_store.t_row) =
      let seg =
        match IMap.find_opt r.f_time !segments with
        | Some s -> s
        | None -> SSel.make Count.Unlicensed in
      segments := IMap.add r.f_time (SSel.add r.f_k r seg) !segments in
    List.iter put segments0;
    let outputs = ref [] in
    let say (n : int) = outputs := Rt.string_of_int_c n :: !outputs in
    List.iter
      (fun (q : In_window_store.t_queries_elem) ->
         let lo = q.f_lo and hi = q.f_hi in
         match q.f_kind with
         (* fetchAll: every row in the window *)
         | 0 ->
             say
               (IMap.fold
                  (fun _ seg acc ->
                     let c = SSel.cardinal seg in
                     Count.visit c;
                     acc + c)
                  (sub_range lo hi !segments) 0)
         (* fetch: the window's segments, each asked for the one key *)
         | 1 ->
             say
               (IMap.fold
                  (fun _ seg acc ->
                     match probe (SSel.find_opt q.f_key seg) with
                     | Some _ -> acc + 1
                     | None -> acc)
                  (sub_range lo hi !segments) 0)
         (* put: computeIfAbsent, then the inner put.  No row is read. *)
         | 2 -> put q.f_new_rec
         (* removeExpiredSegments *)
         | _ -> segments := keep_from lo !segments)
      queries;
    !outputs
end

(* ---------- range delete: the one subject with NO author ---------- *)

module RangeDelete = struct
  let name = "range_delete"

  (* NOT A TRANSCRIPTION, and listed in `hand_written` so the report says so
     beside the numbers.  Ex_RangeDelete.v is our own example -- the witness
     for ODictRangeDelete -- so there is no original author.  What stands in
     is the implementation the structure asks for: an ordered map from price
     to the rows at that price, the band read as a subMap, and the band
     withdrawal as subMap(lo, hi).clear(). *)
  let run (orders : In_range_delete.t_orders_tbl)
      (queries : In_range_delete.t_queries) : string list =
    let by_price = ref (IMap.empty : In_range_delete.t_row list IMap.t) in
    let add (row : In_range_delete.t_row) =
      let b =
        match IMap.find_opt row.f_price !by_price with Some b -> b | None -> [] in
      by_price := IMap.add row.f_price (row :: b) !by_price in
    List.iter add orders;
    let outputs = ref [] in
    let say (n : int) = outputs := Rt.string_of_int_c n :: !outputs in
    List.iter
      (fun (q : In_range_delete.t_queries_elem) ->
         let lo = q.f_lo and hi = q.f_hi in
         match q.f_type with
         (* insert *)
         | 0 -> add q.f_new_order
         (* count the band: subMap, then its rows *)
         | 1 ->
             say
               (IMap.fold
                  (fun _ b acc ->
                     let c = List.length b in
                     Count.visit c;
                     acc + c)
                  (sub_range lo hi !by_price) 0)
         (* withdraw the band: subMap(lo, hi).clear(), the band's keys removed
            one at a time as TreeMap's iterator does it.  No row is read. *)
         | _ ->
             by_price :=
               IMap.fold
                 (fun k _ acc -> IMap.remove k acc)
                 (sub_range lo hi !by_price) !by_price)
      queries;
    !outputs
end

(* ---------- dependent plugins: the author built NOTHING ---------- *)

module DependentPlugins = struct
  let name = "dependent_plugins"

  (* jenkins, core/src/main/java/hudson/PluginManager.java:1042,
     resolveDependentPlugins(), over the field `plugins` at :325.

     THIS ROW IS THE OPPOSITE OF EVERY OTHER ROW, and that is not a bug in
     it.  Everywhere else the author built a structure, we took it away to
     make the `src` column, and the question is whether the optimizer puts it
     back -- so parity with `opt` is the result.  Here the author built
     NOTHING: resolveDependentPlugins is a raw nested loop with no map, no
     index and no cache.  So the expected result is parity with `src`, a
     large gap to `opt`, and what that gap measures is a speedup over code as
     SHIPPED rather than over a form we constructed.

     Transcribed as written in two places the subject could not be.  The
     dependency list is kept NESTED inside the plugin, which is what Jenkins
     has and what the development cannot express; and the `break` is kept,
     which the subject drops because after flattening at most one row can
     match.  On the measured workload each plugin declares exactly ONE
     dependency, so the inner list has length one and the break saves
     nothing -- at higher fan-out it would make this column up to 2x cheaper
     than `src` while leaving the exponent at 2, which is the one respect in
     which the subject's numbers flatter the optimizer. *)

  type dependency = { dep_name : string; optional : bool }
  type plugin = { short_name : string; deleted : bool; deps : dependency list }

  let run (edges : In_dependent_plugins.t_deps_tbl)
      (plugin_rows : In_dependent_plugins.t_plugins_tbl)
      (queries : In_dependent_plugins.t_queries) : string list =
    (* Group the edges ONCE.  Filtering the edge list per plugin would be
       quadratic before the method even starts, and Jenkins pays no such
       cost: a PluginWrapper already owns its dependency list, parsed from
       the manifest.

       A PLAIN Hashtbl, and the only one in this file: it is SETUP and not
       algorithm, so it must stay UNCHARGED.  Charging it would charge the
       author for work Jenkins does not do, which is the opposite of what the
       paragraph above is for.  The same goes for the two accumulators in
       [resolve]. *)
    let by_dependent : (string, dependency list) Hashtbl.t =
      Hashtbl.create 4096 in
    List.iter
      (fun (e : In_dependent_plugins.t_deps_tbl_elem) ->
         let d = { dep_name = e.f_dependency; optional = e.f_optional } in
         Hashtbl.replace by_dependent e.f_dependent
           (d :: (try Hashtbl.find by_dependent e.f_dependent with Not_found -> [])))
      edges;
    let deps_of (nm : string) : dependency list =
      try Hashtbl.find by_dependent nm with Not_found -> [] in
    let plugins =
      List.map
        (fun (r : In_dependent_plugins.t_plugins_tbl_elem) ->
           { short_name = r.f_name; deleted = false; deps = deps_of r.f_name })
        plugin_rows in
    let outputs = ref [] in
    let say (n : int) = outputs := Rt.string_of_int_c n :: !outputs in
    let resolve () =
      List.iter
        (fun plugin ->
           (* uncharged, deliberately: these are the two result sets
              setDependents/setOptionalDependents receive, and a HashSet
              insert into them is a cost this column does not charge -- an
              omission that runs AGAINST the optimizer, since it makes the
              author's column cheaper than it should be *)
           let dependents = Hashtbl.create 64 in
           let optional_dependents = Hashtbl.create 64 in
           List.iter
             (fun possible ->
                (* this inner iteration INSPECTS a stored plugin, which is
                   what the row column counts *)
                Count.visit 1;
                incr Count.comparisons;
                if possible.short_name = plugin.short_name then ()
                else if possible.deleted then ()
                else
                  (* the inner loop, with the break *)
                  let rec scan = function
                    | [] -> ()
                    | d :: rest ->
                        Count.visit 1;
                        incr Count.comparisons;
                        if d.dep_name = plugin.short_name then begin
                          Hashtbl.replace dependents possible.short_name ();
                          if d.optional then
                            Hashtbl.replace optional_dependents
                              possible.short_name ()
                        end
                        else scan rest in
                  scan possible.deps)
             plugins;
           (* setDependents / setOptionalDependents, as the two counts the
              subject reports *)
           say (Hashtbl.length dependents);
           say (Hashtbl.length optional_dependents))
        plugins in
    List.iter (fun _ -> resolve ()) queries;
    !outputs
end

(* The subjects above that no third party wrote, so a report can say so next
   to them instead of leaving a reader to assume an author. *)
let hand_written : string list = [ RangeDelete.name ]

(* ---------- prepared runners, for the measurement ----------

   Shaped exactly like the generated ones: the inputs are converted first and
   a closure is returned, so marshalling happens before the clock starts and
   is not charged to either column. *)

let prepared (f : (string -> Value.t) -> 'a)
    (lookup : string -> Value.t option) : unit -> unit =
  let get n =
    match lookup n with
    | Some v -> v
    | None -> failwith ("missing input " ^ n) in
  fun () -> ignore (f get)

(* Shaped exactly like Monotypes.programs' entries, so the same measurement
   code drives all three columns -- including the per-kind scaling, which the
   author column needs most: its ops phase at 1600 rows is a few
   microseconds, and the difference of two whole-program timings cannot
   resolve that (it moved named_cache from 0.30 to 3.34 between two runs
   before this). *)
let runners : (string * ((string -> Value.t option) -> unit -> unit)) list =
  [ ( "keycloak",
      prepared (fun get ->
          Keycloak.run (Monotypes.In_keycloak.f_queries (get "queries"))) );
    ( "named_cache",
      prepared (fun get ->
          NamedCache.run (Monotypes.In_named_cache.f_ops (get "ops"))) );
    ( "area_registry",
      prepared (fun get ->
          AreaRegistry.run
            (Monotypes.In_area_registry.f_queries (get "queries"))) );
    ( "lookin",
      prepared (fun get ->
          Lookin.run
            (Monotypes.In_lookin.f_functions_tbl (get "functions_tbl"))
            (Monotypes.In_lookin.f_queries (get "queries"))) );
    ( "cluster",
      prepared (fun get ->
          Cluster.run
            (Monotypes.In_cluster.f_partitions_tbl (get "partitions_tbl"))
            (Monotypes.In_cluster.f_queries (get "queries"))) );
    ( "window_store",
      prepared (fun get ->
          WindowStore.run
            (Monotypes.In_window_store.f_segments_tbl (get "segments_tbl"))
            (Monotypes.In_window_store.f_queries (get "queries"))) );
    ( "item_deletion",
      prepared (fun get ->
          ItemDeletion.run
            (Monotypes.In_item_deletion.f_items_tbl (get "items_tbl"))
            (Monotypes.In_item_deletion.f_queries (get "queries"))) );
    ( "user_search",
      prepared (fun get ->
          UserSearch.run
            (Monotypes.In_user_search.f_suggested (get "suggested"))
            (Monotypes.In_user_search.f_queries (get "queries"))) );
    ( "range_delete",
      prepared (fun get ->
          RangeDelete.run
            (Monotypes.In_range_delete.f_orders_tbl (get "orders_tbl"))
            (Monotypes.In_range_delete.f_queries (get "queries"))) );
    ( "dependent_plugins",
      prepared (fun get ->
          DependentPlugins.run
            (Monotypes.In_dependent_plugins.f_deps_tbl (get "deps_tbl"))
            (Monotypes.In_dependent_plugins.f_plugins_tbl (get "plugins_tbl"))
            (Monotypes.In_dependent_plugins.f_queries (get "queries"))) ) ]

(* ---------- what has been monomorphized so far ----------

   One module, as a pilot: the pattern is proved end to end -- including the
   agreement check -- before the other ten are rewritten, because a rewrite
   that loses fidelity to the cited source is the one failure this cannot
   detect. *)

let done_so_far =
  [ Lookin.name; Keycloak.name; NamedCache.name; ItemDeletion.name;
    UserSearch.name; AreaRegistry.name; Cluster.name;
    WindowStore.name; RangeDelete.name; DependentPlugins.name ]

(* ---------- and the check ----------

   Each transcription is run on the same inputs as the compiled optimized
   column and its store compared.  Parity is the expected result: the
   compiler is supposed to arrive back at what the author built, so a
   difference is a bug in the transcription (or in the backend) and not a
   finding. *)

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

let check_keycloak (w : Gen.workload) : bool =
  let get n =
    match lookup_of w n with
    | Some v -> v
    | None -> failwith ("missing input " ^ n) in
  let mine = Monotypes.store_opt_keycloak (lookup_of w) in
  let theirs = Keycloak.run (Monotypes.In_keycloak.f_queries (get "queries")) in
  Rt.eq_list Rt.eq_string mine theirs

let check_named_cache (w : Gen.workload) : bool =
  let get n =
    match lookup_of w n with
    | Some v -> v
    | None -> failwith ("missing input " ^ n) in
  let mine = Monotypes.store_opt_named_cache (lookup_of w) in
  let theirs = NamedCache.run (Monotypes.In_named_cache.f_ops (get "ops")) in
  Rt.eq_list Rt.eq_string mine theirs

let check_item_deletion (w : Gen.workload) : bool =
  let get n =
    match lookup_of w n with
    | Some v -> v
    | None -> failwith ("missing input " ^ n) in
  let mine = Monotypes.store_opt_item_deletion (lookup_of w) in
  let theirs =
    ItemDeletion.run
      (Monotypes.In_item_deletion.f_items_tbl (get "items_tbl"))
      (Monotypes.In_item_deletion.f_queries (get "queries")) in
  Rt.eq_list Rt.eq_string mine theirs

let check_user_search (w : Gen.workload) : bool =
  let get n =
    match lookup_of w n with
    | Some v -> v
    | None -> failwith ("missing input " ^ n) in
  let mine_out, mine_sug = Monotypes.store_opt_user_search (lookup_of w) in
  let theirs_out, theirs_sug =
    UserSearch.run
      (Monotypes.In_user_search.f_suggested (get "suggested"))
      (Monotypes.In_user_search.f_queries (get "queries")) in
  Rt.eq_list Rt.eq_string mine_out theirs_out
  && Monotypes.In_user_search.M_suggested.equal mine_sug theirs_sug

let check_area_registry (w : Gen.workload) : bool =
  let get n =
    match lookup_of w n with
    | Some v -> v
    | None -> failwith ("missing input " ^ n) in
  let mine = Monotypes.store_opt_area_registry (lookup_of w) in
  let theirs =
    AreaRegistry.run (Monotypes.In_area_registry.f_queries (get "queries")) in
  Rt.eq_list Rt.eq_string mine theirs

let simple (name : string) (f : (string -> Value.t) -> string list)
    (mine : (string -> Value.t option) -> string list) (w : Gen.workload) : bool =
  ignore name;
  let get n =
    match lookup_of w n with
    | Some v -> v
    | None -> failwith ("missing input " ^ n) in
  Rt.eq_list Rt.eq_string (mine (lookup_of w)) (f get)

let check_cluster =
  simple "cluster"
    (fun get ->
      Cluster.run
        (Monotypes.In_cluster.f_partitions_tbl (get "partitions_tbl"))
        (Monotypes.In_cluster.f_queries (get "queries")))
    Monotypes.store_opt_cluster

let check_window_store =
  simple "window_store"
    (fun get ->
      WindowStore.run
        (Monotypes.In_window_store.f_segments_tbl (get "segments_tbl"))
        (Monotypes.In_window_store.f_queries (get "queries")))
    Monotypes.store_opt_window_store

let check_range_delete =
  simple "range_delete"
    (fun get ->
      RangeDelete.run
        (Monotypes.In_range_delete.f_orders_tbl (get "orders_tbl"))
        (Monotypes.In_range_delete.f_queries (get "queries")))
    Monotypes.store_opt_range_delete

let checks : (string * (Gen.workload -> bool)) list =
  [ ("lookin", check_lookin);
    ("dependent_plugins",
      simple "dependent_plugins"
        (fun get ->
          DependentPlugins.run
            (Monotypes.In_dependent_plugins.f_deps_tbl (get "deps_tbl"))
            (Monotypes.In_dependent_plugins.f_plugins_tbl (get "plugins_tbl"))
            (Monotypes.In_dependent_plugins.f_queries (get "queries")))
        Monotypes.store_opt_dependent_plugins);
    ("cluster", check_cluster);
    ("window_store", check_window_store);
    ("range_delete", check_range_delete);
    ("area_registry", check_area_registry);
    ("user_search", check_user_search);
    ("item_deletion", check_item_deletion);
    ("keycloak", check_keycloak);
    ("named_cache", check_named_cache) ]
