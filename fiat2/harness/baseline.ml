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

   THE EXPECTED RESULT IS PARITY.  The compiler is supposed to arrive back at
   the structure the author built, so matching asymptotics is the positive
   result and a win would mean one of the two is not what it claims to be.  The
   one subject to expect a better exponent from is Jenkins's `suggest`, which is
   the author's own linear `contains` scan.

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
   * `rows` CAN cross, and is the headline.  It counts the stored rows an
     operation ENUMERATES -- pulls out of a structure and looks at -- and not
     the rows a tree descent compares against on the way.  Under that reading a
     scan of n rows is n, a probe that yields one row is 1, a membership test
     is 0 because it yields nothing, and an insert is 0 because it writes
     rather than reads.  That is exactly the asymptotic claim, it means the same
     thing on both sides, and it is the instrument the other two cannot replace:
     `cmps` is blind to a traversal that compares nothing, which is how
     Keycloak's whole-list COUNT came out at exponent 0.00 on the source side
     when its step count is linear.  The structural cost of FINDING a row is
     cmps's business, below.
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

(* ---------- the table ---------- *)

let runners : (string * runner) list =
  [ (Keycloak.name, Keycloak.run);
    (NamedCache.name, NamedCache.run);
    (ItemDeletion.name, ItemDeletion.run);
    (UserSearch.name, UserSearch.run) ]
