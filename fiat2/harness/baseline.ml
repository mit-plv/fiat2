(* The ORIGINAL programs, transcribed.

   Every number elsewhere in this harness compares our own source form against
   our own optimized form.  That is the weaker of the two comparisons available,
   and the plan recorded why: in seven of eight subjects the `src` program is
   NOT the author's code.  We deliberately removed the structure the author had
   built and wrote the query against one plain collection, so `src -> opt`
   measures "declarative with no index" against "compiler-indexed" and a
   reviewer can fairly say nobody would write the baseline.

   This file is the other comparison: the author's own data structures and
   operations, in OCaml, as the source we read them from writes them.  Each
   module cites the file and line it came from, and transcribes what is there
   rather than what would be fastest.

   Eight of the nine subjects have an author.  The ninth, Ex_RangeDelete, is
   our own example -- there is nobody to transcribe -- so what stands in for
   an author there is the implementation its structure asks for, and it is
   named in `hand_written` so the report marks it rather than letting it pass
   as a transcription.

   THE EXPECTED RESULT IS PARITY.  The compiler is supposed to arrive back at
   the structure the author built, so matching asymptotics is the positive
   result and a win would mean one of the two is not what it claims to be.  The
   one subject to expect a better exponent from is Jenkins's `suggest`, which is
   the author's own linear `contains` scan.

   Two places go the other way and are measured rather than argued with, both
   of them a composite key the author indexed and this development cannot:
   Kafka's Cluster.partition(new TopicPartition(topic, partition)) and
   InMemoryWindowStore's inner map from key to value, which `fetch` descends
   once per segment.  Each shows up in the row column as a bounded constant
   rather than an exponent, and each is the gap its own subject file pins.

   HOW IT IS KEPT HONEST.  Each module consumes the SAME Gen.workload the
   subject programs consume, and returns the final store in the same form, so
   the driver can check that the author's code and the optimizer's output
   compute the SAME ANSWER on every input before comparing any cost.  A
   transcription that does not agree is a transcription that is wrong, and the
   check says so before a number is believed.

   WHAT THE NUMBERS CAN AND CANNOT SAY -- the three constraints settled before
   any of this was written:

   * `steps` cannot cross the boundary.  It counts entries into interp_expr,
     which has no analogue in hand-written OCaml.  It is not reported here.
   * `rows` CAN cross, and its EXPONENT is the headline.  It counts the
     elements an operation iterates, and not the rows a tree descent compares
     against on the way: a scan of n rows is n, a probe that yields one row is
     1, a membership test is 0 because it yields nothing, and an insert is 0
     because it writes rather than reads.  It is the instrument the other two
     cannot replace -- `cmps` is blind to a traversal that compares nothing,
     which is how Keycloak's whole-list COUNT came out at exponent 0.00 on the
     source side when its step count is linear.  The structural cost of
     FINDING a row is cmps's business, below.

     WHAT THE CONSTANT IN THIS COLUMN IS NOT.  The counter charges every
     PIPELINE STAGE that iterates a collection, and an intermediate
     collection is not storage, so a derived read can count the same rows
     more than once.  Measured, not supposed: window_store's fetchAll answers
     a window of 8 rows and reports 24 -- eight dict entries out of the
     ranged member, then the eight buckets they hold, then the eight rows
     inside them -- while cluster's forTopic answers a bucket of 8 through one
     LOOKUP and reports 8.  Hand-written code has no stages at all, so the
     opt-against-base RATIO on a multi-stage read is partly an artifact of
     how many stages the rewriting left, and the two sides are comparable in
     the exponent and in the SHAPE of what each one touches, not factor for
     factor.  Where this file claims a constant-factor gap below -- the two
     composite keys -- the claim is also stated structurally, as which
     structure each side descends, so that it does not rest on the ratio.
     See count.ml, which says the same thing where the counter lives.
   * `cmps` can, with a stated bias.  The transcriptions use the same
     Count.comparisons counter, counting one key equality per hash probe --
     which is what a hash lookup does beyond hashing the key.  It therefore
     UNDERCOUNTS a hash map and flatters the author.  Said out loud rather than
     hidden, because the gap it hides is the real one: our dictionaries are
     Map.Make(Value) at O(log n) and the originals are hash maps at O(1), a
     backend freedom the type system already records (Language.dict_kind) and
     not a defect in the rewriting.
   * Wall clock can, with the opposite bias.  Our side is a tree-walking
     interpreter; measured 2026-10-25, that costs about a quarter of a flat
     read's time at 1600 rows, the rest being structural work any ordered
     implementation also does.  So seconds are roughly 25% inflated on our
     side, by a cause that is quantified rather than waved at.
   * The BUILD phase is not comparable and is not reported.  Our source build
     is O(n^2) because the declared-key subjects elaborate a uniqueness guard
     into a table scan, and the originals check nothing -- Keycloak's model
     guarantees uniqueness, Home Assistant's __setitem__ and Kafka's put just
     overwrite.  That is a claim about constraint checking, not about a missing
     index. *)

type runner = Gen.workload -> (string * Value.t) list

(* the final store, printed exactly as Bench.run_one prints it, so that the two
   can be compared as strings *)
let format_store (l : (string * Value.t) list) : string =
  String.concat "; "
    (List.map (fun (k, v) -> k ^ " = " ^ Value.to_string v)
       (List.sort (fun (a, _) (b, _) -> compare a b) l))

(* ---------- shared accessors on the workload's values ---------- *)

let field (f : string) (v : Value.t) : Value.t =
  match v with VRecord l -> (try List.assoc f l with Not_found -> VUnit) | _ -> VUnit

let str (v : Value.t) : string = match v with VString s -> s | _ -> ""
let int_of (v : Value.t) : int = match v with VInt n -> n | _ -> min_int

let queries_of (w : Gen.workload) (var : string) : Value.t list =
  match List.assoc_opt var w.Gen.env with Some (Value.VList l) -> l | _ -> []

(* A hash lookup, instrumented under the conventions in the header: one key
   equality into `cmps` -- what it does beyond hashing, which this undercounts
   -- and, on a hit, one row ENUMERATED into `rows`, because the row comes out
   and is looked at. *)
let hash_probe (h : ('k, 'v) Hashtbl.t) (k : 'k) : 'v option =
  incr Count.comparisons;
  match Hashtbl.find_opt h k with
  | Some v -> Count.visit 1; Some v
  | None -> None

(* A probe whose RESULT IS NOT A STORED ROW: a posting list, a bucket, a
   segment.  It costs the same key equality and no row, because nothing has
   been enumerated yet -- whatever walks the thing it returns is what pays
   for the rows in it. *)
let hash_find (h : ('k, 'v) Hashtbl.t) (k : 'k) : 'v option =
  incr Count.comparisons;
  Hashtbl.find_opt h k

(* A put reads no stored row -- it writes one -- so it costs a key equality and
   no row.  The same is true of the optimizer's output, whose OInsert is a map
   add: the convention is the same on both sides, which is the point of it. *)
let hash_put (h : ('k, 'v) Hashtbl.t) (k : 'k) (v : 'v) : unit =
  incr Count.comparisons;
  Hashtbl.replace h k v

(* ---------- keycloak: one list, two maps on two unique keys ---------- *)

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
    mutable rows : Value.t list;                   (* requiredActionProviderList *)
    mutable size : int;                            (* ArrayList's own size field *)
    by_id : (string, Value.t) Hashtbl.t;           (* requiredActionProviders *)
    by_alias : (string, Value.t) Hashtbl.t;        (* ...ByAlias *)
  }

  let run (w : Gen.workload) : (string * Value.t) list =
    let st = { rows = []; size = 0;
               by_id = Hashtbl.create 1024; by_alias = Hashtbl.create 1024 } in
    let outputs = ref [] in
    let say (n : int) = outputs := Value.VString (string_of_int n) :: !outputs in
    List.iter
      (fun q ->
         match int_of (field "kind" q) with
         (* the write the translation adds; see the subject's Faithfulness note.
            The author builds once, so this is the put loop above, run per row.
            NO uniqueness check: Keycloak's model guarantees it. *)
         | 0 ->
             let row = field "new_action" q in
             st.rows <- row :: st.rows;
             st.size <- st.size + 1;
             hash_put st.by_id (str (field "id" row)) row;
             hash_put st.by_alias (str (field "alias" row)) row
         (* getRequiredActionProviderById(id) -> ...get(id) *)
         | 1 ->
             say (match hash_probe st.by_id (str (field "k" q)) with
                  | Some _ -> 1 | None -> 0)
         (* getRequiredActionProviderByAlias(alias) -> ...ByAlias().get(alias) *)
         | 2 ->
             say (match hash_probe st.by_alias (str (field "k" q)) with
                  | Some _ -> 1 | None -> 0)
         (* getRequiredActionProviderList(), counted: ArrayList.size() *)
         | _ -> say st.size)
      (queries_of w "queries");
    [ ("outputs", Value.VList !outputs) ]
end

(* ---------- named cache: an ordered map and a maintained total ---------- *)

(* The comparison the author's TREE performs, counted.  NamedCache's cache is a
   NavigableMap, so unlike the other three subjects here there is no
   hash-versus-tree gap to declare: both sides pay log n comparisons, which
   makes this the one line where `cmps` is comparable without a caveat. *)
module CountedString = struct
  type t = string
  let compare (a : string) (b : string) : int =
    incr Count.comparisons;
    String.compare a b
end

module SMap = Map.Make (CountedString)

module NamedCache = struct
  let name = "named_cache"

  (* kafka, commit 995cfcf9,
     streams/.../state/internals/NamedCache.java:44 and :49:

       private final NavigableMap<Bytes, LRUNode> cache = new TreeMap<>();
       private long currentSizeBytes = 0;

     corrected at :178/:192/:249/:281 and read at :196.  A keyed structure and
     a maintained SUM over it, which is the pair the optimizer derives as
     [UniqueDictIdx "k"; SumAgg "size"]. *)
  type state = {
    mutable cache : Value.t SMap.t;
    mutable total : int;                     (* currentSizeBytes *)
  }

  let size_of (row : Value.t) : int = int_of (field "size" row)

  let run (w : Gen.workload) : (string * Value.t) list =
    let st = { cache = SMap.empty; total = 0 } in
    let outputs = ref [] in
    let say (n : int) = outputs := Value.VString (string_of_int n) :: !outputs in
    (* remove(key), maintaining the total: the node has to be READ to know what
       to subtract, which is the one row a delete touches, and is why the
       optimizer's own delete probes rather than scans *)
    let remove (k : string) =
      match SMap.find_opt k st.cache with
      | Some old -> Count.visit 1;
                    st.total <- st.total - size_of old;
                    st.cache <- SMap.remove k st.cache
      | None -> () in
    List.iter
      (fun q ->
         match int_of (field "kind" q) with
         (* delete(key) -- :273 *)
         | 0 -> remove (str (field "k" q))
         (* put(key, value) -- :174-192: evict the old binding, then insert *)
         | 1 ->
             let node = field "node" q in
             let k = str (field "k" node) in
             remove k;
             st.cache <- SMap.add k node st.cache;
             st.total <- st.total + size_of node
         (* sizeInBytes() -- :196: a field read, no row *)
         | 2 -> say st.total
         (* get(key) -- :200-201 *)
         | _ ->
             say (match SMap.find_opt (str (field "k" q)) st.cache with
                  | Some _ -> Count.visit 1; 1
                  | None -> 0))
      (queries_of w "ops");
    [ ("outputs", Value.VList !outputs) ]
end

(* ---------- item deletion: a hash set of whole rows ---------- *)

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
  let run (w : Gen.workload) : (string * Value.t) list =
    let reg : (Value.t, unit) Hashtbl.t = Hashtbl.create 4096 in
    (* The items in flight arrive in the ENVIRONMENT rather than through build
       queries, as this subject's table does and as the other three subjects'
       do not.  Missing this is what the `agree` column caught on the first run:
       the transcription started empty, so every containsHit said "free" while
       the subject said "deleting".  The build is not part of the comparison --
       baseline_phase subtracts the ops=0 run -- so what this costs cancels. *)
    (match List.assoc_opt "items_tbl" w.Gen.env with
     | Some (Value.VList l) -> List.iter (fun r -> Hashtbl.replace reg r ()) l
     | _ -> ());
    let outputs = ref [] in
    let say (s : string) = outputs := Value.VString s :: !outputs in
    List.iter
      (fun q ->
         let item = field "item" q in
         match int_of (field "kind" q) with
         | 0 ->
             incr Count.comparisons;
             say (if Hashtbl.mem reg item then "deleting" else "free")
         | 1 -> incr Count.comparisons; Hashtbl.replace reg item ()
         | _ -> incr Count.comparisons; Hashtbl.remove reg item)
      (queries_of w "queries");
    [ ("outputs", Value.VList !outputs) ]
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
     it derives a trigram index the author never built.

     So the row column here is the result: parity on find and remove, and a
     difference on suggest. *)
  let run (w : Gen.workload) : (string * Value.t) list =
    let by_id : (string, Value.t) Hashtbl.t = Hashtbl.create 4096 in
    let outputs = ref [] in
    let suggested =
      ref (match List.assoc_opt "suggested" w.Gen.store with
           | Some v -> v
           | None -> Value.VSet Value.VSet.empty) in
    let say (n : int) = outputs := Value.VString (string_of_int n) :: !outputs in
    List.iter
      (fun q ->
         match int_of (field "kind" q) with
         (* User.get(id, true) -> AllUsers.putIfAbsent *)
         | 0 ->
             let u = field "new_user" q in
             hash_put by_id (str (field "id" u)) u
         (* AllUsers.remove(id) *)
         | 1 -> incr Count.comparisons; Hashtbl.remove by_id (str (field "k" q))
         (* find(id): the ConcurrentHashMap lookup, counted as the subject
            counts it *)
         | 2 ->
             say (match hash_probe by_id (str (field "k" q)) with
                  | Some _ -> 1 | None -> 0)
         (* suggest(token): the author's own scan over every user *)
         | _ ->
             let tok = str (field "k" q) in
             let hits = ref Value.VSet.empty in
             Hashtbl.iter
               (fun _ u ->
                  Count.visit 1;
                  if Eval.str_contains (str (field "fullName" u)) tok
                  then hits := Value.VSet.add u !hits)
               by_id;
             suggested := Value.VSet !hits)
      (queries_of w "queries");
    [ ("outputs", Value.VList !outputs); ("suggested", !suggested) ]
end

(* ---------- area registry: a dict and a secondary index on floor ---------- *)

module AreaRegistry = struct
  let name = "area_registry"

  (* home-assistant/core, commit e751cd2b.
     homeassistant/helpers/area_registry.py:169 (class AreaRegistryItems),
     with the write hooks in homeassistant/helpers/registry.py:

       def __setitem__(self, key, entry):              registry.py:38
           data = self.data
           if key in data:
               self._unindex_entry(key, entry)
           data[key] = entry
           self._index_entry(key, entry)

       def _index_entry(self, key, entry):             area_registry.py:180
           super()._index_entry(key, entry)
           if entry.floor_id is not None:
               self._floors_index[entry.floor_id][key] = True

       def _unindex_entry(self, key, replacement_entry=None):
           super()._unindex_entry(key, replacement_entry)
           entry = self.data[key]                      area_registry.py:199
           if floor_id := entry.floor_id:
               self._unindex_entry_value(key, floor_id, self._floors_index)

       def get_areas_for_floor(self, floor):           area_registry.py:211
           data = self.data
           return [data[key] for key in self._floors_index.get(floor, ())]

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
    data : (string, Value.t) Hashtbl.t;                      (* self.data *)
    floors : (string, (string, unit) Hashtbl.t) Hashtbl.t;   (* _floors_index *)
  }

  let floor_of (row : Value.t) : string option =
    match field "floor" row with Value.VOption (Some f) -> Some (str f) | _ -> None

  let run (w : Gen.workload) : (string * Value.t) list =
    let st = { data = Hashtbl.create 4096; floors = Hashtbl.create 1024 } in
    let outputs = ref [] in
    let say (n : int) = outputs := Value.VString (string_of_int n) :: !outputs in
    (* _index_entry: the primary dict, then the floor posting list *)
    let index_entry (key : string) (row : Value.t) =
      hash_put st.data key row;
      match floor_of row with
      | None -> ()                                 (* `if ... is not None` *)
      | Some f ->
          let b =
            match hash_find st.floors f with
            | Some b -> b
            | None -> let b = Hashtbl.create 8 in Hashtbl.replace st.floors f b; b in
          hash_put b key () in
    (* _unindex_entry, then UserDict.__delitem__ (registry.py:61) *)
    let unindex_entry (key : string) =
      match hash_probe st.data key with
      | None -> ()                                 (* HA raises; nothing to do *)
      | Some row ->
          (match floor_of row with
           | None -> ()
           | Some f ->
               (match hash_find st.floors f with
                | None -> ()
                | Some b ->
                    incr Count.comparisons;
                    Hashtbl.remove b key;
                    (* `if not entries: del index[value]` -- registry.py:56 *)
                    if Hashtbl.length b = 0 then Hashtbl.remove st.floors f));
          incr Count.comparisons;
          Hashtbl.remove st.data key in
    List.iter
      (fun q ->
         match int_of (field "kind" q) with
         (* __setitem__ with a fresh key: the build's insert *)
         | 0 -> let row = field "new_area" q in
                index_entry (str (field "id" row)) row
         (* __delitem__ *)
         | 1 -> unindex_entry (str (field "k" q))
         (* async_get_area(area_id) -- area_registry.py:241, a dict get at :247 *)
         | 2 -> say (match hash_probe st.data (str (field "k" q)) with
                     | Some _ -> 1 | None -> 0)
         (* get_areas_for_floor(floor), counted *)
         | _ ->
             let fl = str (field "fl" q) in
             say (match hash_find st.floors fl with
                  | None -> 0
                  | Some b ->
                      Hashtbl.fold
                        (fun key _ acc ->
                           match hash_probe st.data key with
                           | Some _ -> acc + 1
                           | None -> acc)
                        b 0))
      (queries_of w "queries");
    [ ("outputs", Value.VList !outputs) ]
end

(* ---------- lookin: a set of names, and nothing else ---------- *)

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
  let run (w : Gen.workload) : (string * Value.t) list =
    let names : (string, unit) Hashtbl.t = Hashtbl.create 4096 in
    (match List.assoc_opt "functions_tbl" w.Gen.env with
     | Some (Value.VList l) ->
         List.iter (fun r -> Hashtbl.replace names (str (field "name" r)) ()) l
     | _ -> ());
    let outputs = ref [] in
    let say (s : string) = outputs := Value.VString s :: !outputs in
    let has (k : string) = incr Count.comparisons; Hashtbl.mem names k in
    List.iter
      (fun q ->
         match int_of (field "kind" q) with
         (* media_player.py:87 -- the key varies with the loop *)
         | 0 -> say (if has (str (field "k" q)) then "supported" else "unsupported")
         (* media_player.py:107 -- the key is a literal *)
         | _ -> say (if has "mode" then "has-mode" else "no-mode"))
      (queries_of w "queries");
    [ ("outputs", Value.VList !outputs) ]
end

(* ---------- cluster: four maps, and no list ---------- *)

module Cluster = struct
  let name = "cluster"

  (* apache/kafka, commit 995cfcf9,
     clients/src/main/java/org/apache/kafka/common/Cluster.java:47-50:

       private final Map<TopicPartition, PartitionInfo> partitionsByTopicPartition;
       private final Map<String, List<PartitionInfo>> partitionsByTopic;
       private final Map<String, List<PartitionInfo>> availablePartitionsByTopic;
       private final Map<Integer, List<PartitionInfo>> partitionsByNode;

     built in the constructor at :142-:157 and :164-:184, and read at

       partition(tp)                     :289  partitionsByTopicPartition.get
       partitionsForTopic(topic)         :298  partitionsByTopic.get
       availablePartitionsForTopic(t)    :317  availablePartitionsByTopic.get
       partitionsForNode(nodeId)         :326  partitionsByNode.get

     Cluster has a field for every map and NO field for `partitions`, which is
     the erasure the subject is about; four probes, four buckets, no scan.

     TWO THINGS TO READ CAREFULLY HERE.

     The subject counts what each accessor returns, because its output channel
     is a list of strings, so these transcriptions walk the bucket they hand
     back -- which is what :298's and :317's and :326's callers do with it.
     Kafka also has partitionCountForTopic at :307, which answers the COUNT in
     O(1) from ArrayList.size() without touching a row.  That one the optimizer
     cannot match: it would need a maintained aggregate PER BUCKET, i.e. the
     dict-of-aggregates combinator this development deliberately does not
     build.  So the parity on forTopic below is parity with :298, and :307 is
     an unmatched O(1) the author has and we do not.  Said here rather than
     chosen silently -- and it changes no exponent, since both sides are
     linear in the bucket and the bucket is bounded.

     onePartition is the other way round and is measured, not noted: the key
     is composite, `new TopicPartition(p.topic(), p.partition())`, Kafka has a
     map on it, and Conquord has no composite-key index -- so the author
     probes once where the optimizer probes on topic and filters the bucket.
     That is the subject's own one_partition_probes_then_filters, in rows.

     availablePartitionsByTopic is built in a second pass over
     partitionsByTopic (:164-:184, with Kafka's shortcut for the common case
     where no partition is unavailable); built in the same loop here, since
     the structure is the same one and the build phase is not compared. *)
  type state = {
    by_tp : (string * int, Value.t) Hashtbl.t;
    by_topic : (string, Value.t list ref) Hashtbl.t;
    available : (string, Value.t list ref) Hashtbl.t;
    by_node : (int, Value.t list ref) Hashtbl.t;
  }

  (* computeIfAbsent(k, _ -> new ArrayList<>()).add(p) *)
  let bucket_add (h : ('k, Value.t list ref) Hashtbl.t) (k : 'k) (row : Value.t) =
    incr Count.comparisons;
    match Hashtbl.find_opt h k with
    | Some b -> b := row :: !b
    | None -> Hashtbl.replace h k (ref [ row ])

  (* the rows an accessor hands back, counted by its caller *)
  let bucket_count (h : ('k, Value.t list ref) Hashtbl.t) (k : 'k) : int =
    match hash_find h k with
    | None -> 0                                   (* getOrDefault(k, List.of()) *)
    | Some b -> let n = List.length !b in Count.visit n; n

  let run (w : Gen.workload) : (string * Value.t) list =
    let st = { by_tp = Hashtbl.create 4096; by_topic = Hashtbl.create 1024;
               available = Hashtbl.create 1024; by_node = Hashtbl.create 1024 } in
    (match List.assoc_opt "partitions_tbl" w.Gen.env with
     | Some (Value.VList l) ->
         List.iter
           (fun p ->
              let topic = str (field "topic" p) in
              hash_put st.by_tp (topic, int_of (field "partition" p)) p;
              bucket_add st.by_topic topic p;
              match field "leader" p with
              | Value.VOption (Some n) ->
                  (* `if (p.leader() == null) continue` -- :150 *)
                  bucket_add st.by_node (int_of n) p;
                  bucket_add st.available topic p
              | _ -> ())
           l
     | _ -> ());
    let outputs = ref [] in
    let say (n : int) = outputs := Value.VString (string_of_int n) :: !outputs in
    List.iter
      (fun q ->
         match int_of (field "kind" q) with
         | 0 -> say (bucket_count st.by_topic (str (field "topic" q)))
         | 1 -> say (bucket_count st.by_node (int_of (field "node" q)))
         | 2 ->
             say (match hash_probe st.by_tp
                          (str (field "topic" q), int_of (field "part" q)) with
                  | Some _ -> 1 | None -> 0)
         | _ -> say (bucket_count st.available (str (field "topic" q))))
      (queries_of w "queries");
    [ ("outputs", Value.VList !outputs) ]
end

(* ---------- the two ordered subjects ---------- *)

(* The comparison an ordered map on an INT key performs, counted the same way
   CountedString counts a string one.  Both of the subjects below are keyed on
   a number, and both chose an ordered structure on purpose. *)
module CountedInt = struct
  type t = int
  let compare (a : int) (b : int) : int = incr Count.comparisons; compare a b
end

module IMap = Map.Make (CountedInt)

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

module WindowStore = struct
  let name = "window_store"

  (* apache/kafka, commit 995cfcf9, streams/src/main/java/org/apache/kafka/
     streams/state/internals/InMemoryWindowStore.java:78:

       private final ConcurrentNavigableMap<Long,
           ConcurrentNavigableMap<Bytes, byte[]>> segmentMap
               = new ConcurrentSkipListMap<>();

       fetchAll(timeFrom, timeTo)   :398 -> segmentMap.subMap(minTime, true, timeTo, true)
       fetch(key, from, to)         :287 -> the same subMap, then the key's
                                            sub-range per segment, :1021-1029
       put(key, value, t)           :221 -> segmentMap.computeIfAbsent(t, ...)
                                                     .put(keyBytes, value)
       removeExpiredSegments()      :637 -> segmentMap.headMap(minLiveTime, false)
                                                     .clear()

     TWO ordered levels, time then key, which is the one place in this file
     where the author's structure is strictly richer than the derived one.
     The subject flattens the rows and the optimizer chooses the nesting: a
     Ranged dict on time whose buckets are unindexed bags.  So fetchAll is
     parity -- both walk the window -- and `fetch` is the D4 gap in the row
     column: Kafka descends the inner map once per segment and enumerates
     only the rows that match, where the optimizer enumerates the window and
     filters it.  Same exponent, and the constant is the window's width.

     Ranges here are [lo, hi) to match the subject, whose rule's shape is
     half-open; Kafka's subMap is closed with hi = timeTo.  Nothing turns on
     which end is open, and the generator's bounds are the same on both sides.

     One case that cannot arise in these workloads and would differ if it
     did: a put at a (time, key) that already exists OVERWRITES in Kafka,
     where the subject's table prepends a second row.  The generator's puts
     all carry fresh times, so no run distinguishes them; stated because the
     transcription would otherwise look like it had chosen. *)
  let run (w : Gen.workload) : (string * Value.t) list =
    let segments = ref (IMap.empty : Value.t SMap.t IMap.t) in
    (match List.assoc_opt "segments_tbl" w.Gen.env with
     | Some (Value.VList l) ->
         List.iter
           (fun r ->
              let t = int_of (field "time" r) and k = str (field "k" r) in
              let seg = match IMap.find_opt t !segments with
                        | Some s -> s | None -> SMap.empty in
              segments := IMap.add t (SMap.add k r seg) !segments)
           l
     | _ -> ());
    let outputs = ref [] in
    let say (n : int) = outputs := Value.VString (string_of_int n) :: !outputs in
    List.iter
      (fun q ->
         let lo = int_of (field "lo" q) and hi = int_of (field "hi" q) in
         match int_of (field "kind" q) with
         (* fetchAll: every row in the window *)
         | 0 ->
             let n = IMap.fold
                       (fun _ seg acc ->
                          let c = SMap.cardinal seg in Count.visit c; acc + c)
                       (sub_range lo hi !segments) 0 in
             say n
         (* fetch: the window's segments, each asked for the one key *)
         | 1 ->
             let key = str (field "key" q) in
             let n = IMap.fold
                       (fun _ seg acc ->
                          match SMap.find_opt key seg with
                          | Some _ -> Count.visit 1; acc + 1
                          | None -> acc)
                       (sub_range lo hi !segments) 0 in
             say n
         (* put: computeIfAbsent, then the inner put.  No row is read. *)
         | 2 ->
             let r = field "new_rec" q in
             let t = int_of (field "time" r) and k = str (field "k" r) in
             let seg = match IMap.find_opt t !segments with
                       | Some s -> s | None -> SMap.empty in
             segments := IMap.add t (SMap.add k r seg) !segments
         (* removeExpiredSegments *)
         | _ -> segments := keep_from lo !segments)
      (queries_of w "queries");
    [ ("outputs", Value.VList !outputs) ]
end

(* ---------- range delete: the one subject with no author ---------- *)

module RangeDelete = struct
  let name = "range_delete"

  (* THIS ONE IS NOT A TRANSCRIPTION, and it is listed in `hand_written`
     below so that the report says so beside the numbers.  Ex_RangeDelete.v
     is our own example -- the witness for ODictRangeDelete -- so there is no
     original author to compare against.  What stands in for one is the
     implementation the structure asks for: an ordered map from price to the
     rows at that price, the band read as a subMap, and the band WITHDRAWAL as
     subMap(lo, hi).clear(), which is how a programmer writes it in Java or
     C++ once they have reached for a sorted container at all.

     It is here because the claim it checks is still worth checking -- that
     the rewriting's output is the same shape as the obvious hand
     implementation, on the one operator whose witness is synthetic -- but it
     is evidence of a weaker kind than the four above, and the table should
     not read as though an author wrote it. *)
  type state = { mutable by_price : Value.t list IMap.t }

  let run (w : Gen.workload) : (string * Value.t) list =
    let st = { by_price = IMap.empty } in
    let add (row : Value.t) =
      let p = int_of (field "price" row) in
      let b = match IMap.find_opt p st.by_price with Some b -> b | None -> [] in
      st.by_price <- IMap.add p (row :: b) st.by_price in
    (match List.assoc_opt "orders_tbl" w.Gen.env with
     | Some (Value.VList l) -> List.iter add l
     | _ -> ());
    let outputs = ref [] in
    let say (n : int) = outputs := Value.VString (string_of_int n) :: !outputs in
    List.iter
      (fun q ->
         let lo = int_of (field "lo" q) and hi = int_of (field "hi" q) in
         match int_of (field "type" q) with
         (* insert *)
         | 0 -> add (field "new_order" q)
         (* count the band: subMap, then its rows *)
         | 1 ->
             say (IMap.fold
                    (fun _ b acc ->
                       let c = List.length b in Count.visit c; acc + c)
                    (sub_range lo hi st.by_price) 0)
         (* withdraw the band: subMap(lo, hi).clear(), which is the band's
            keys removed one at a time, as TreeMap's iterator does it.  No row
            is read -- the entries are unlinked. *)
         | _ ->
             st.by_price <-
               IMap.fold (fun k _ acc -> IMap.remove k acc)
                 (sub_range lo hi st.by_price) st.by_price)
      (queries_of w "queries");
    [ ("outputs", Value.VList !outputs) ]
end

(* ---------- the table ---------- *)

let runners : (string * runner) list =
  [ (Keycloak.name, Keycloak.run);
    (NamedCache.name, NamedCache.run);
    (AreaRegistry.name, AreaRegistry.run);
    (Lookin.name, Lookin.run);
    (Cluster.name, Cluster.run);
    (WindowStore.name, WindowStore.run);
    (ItemDeletion.name, ItemDeletion.run);
    (UserSearch.name, UserSearch.run);
    (RangeDelete.name, RangeDelete.run) ]

(* The subjects above that no third party wrote, so that the report can say so
   next to them instead of leaving a reader to assume an author. *)
let hand_written : string list = [ RangeDelete.name ]
