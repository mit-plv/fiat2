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

(* The structures the transcriptions build, over a monomorphic string key.
   Their comparison and hash are rt.ml's, so they are priced exactly as the
   generated structures are -- which is the whole point of this file.

   WHICH STRUCTURE FOR WHICH AUTHOR.  A Java HashMap and a Python dict or set
   are hashed, so those become the persistent trie; a Java NavigableMap or
   TreeMap is ordered, so that becomes the ordered map.  A TSet on our side
   carries no kind, so the typed column charges it as a tree -- which is the
   asymmetry harness/README already names and prices, and it is reproduced
   here rather than quietly removed. *)
module SKey = struct
  type t = string

  let compare = Rt.cmp_string
  let equal a b = Rt.cmp_string a b = 0
  let hash = Rt.hash_string
end

module SSet = Set.Make (SKey)
module STrie = CCHashTrie.Make (SKey)
module SMap = Map.Make (SKey)

(* baseline.ml's kprobe: a probe that YIELDS a row charges one row, where a
   membership test charges none because it yields a boolean.  Reproduced, so
   the rows column means the same thing on both sides. *)
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
    mutable by_id : In_keycloak.t_row STrie.t;    (* requiredActionProviders *)
    mutable by_alias : In_keycloak.t_row STrie.t; (* ...ByAlias *)
  }

  let run (queries : In_keycloak.t_queries) : string list =
    let st =
      { rows = []; size = 0; by_id = STrie.empty; by_alias = STrie.empty } in
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
             st.by_id <- STrie.add row.f_id row st.by_id;
             st.by_alias <- STrie.add row.f_alias row st.by_alias
         (* getRequiredActionProviderById(id) -> ...get(id) *)
         | 1 ->
             say (match probe (STrie.get q.f_k st.by_id) with
                  | Some _ -> 1 | None -> 0)
         (* getRequiredActionProviderByAlias(alias) -> ...ByAlias().get(alias) *)
         | 2 ->
             say (match probe (STrie.get q.f_k st.by_alias) with
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
    mutable cache : In_named_cache.t_row SMap.t;
    mutable total : int;                     (* currentSizeBytes *)
  }

  let run (ops : In_named_cache.t_ops) : string list =
    let st = { cache = SMap.empty; total = 0 } in
    let outputs = ref [] in
    let say (n : int) = outputs := Rt.string_of_int_c n :: !outputs in
    (* remove(key), maintaining the total: the node has to be READ to know what
       to subtract, which is the one row a delete touches, and is why the
       optimizer's own delete probes rather than scans *)
    let remove (k : string) =
      match probe (SMap.find_opt k st.cache) with
      | Some (old : In_named_cache.t_row) ->
          st.total <- st.total - old.f_size;
          st.cache <- SMap.remove k st.cache
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
             st.cache <- SMap.add k node st.cache;
             st.total <- st.total + node.f_size
         (* sizeInBytes() -- :196: a field read, no row *)
         | 2 -> say st.total
         (* get(key) -- :200-201 *)
         | _ ->
             say (match probe (SMap.find_opt q.f_k st.cache) with
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

  (* a HashSet, so a trie keyed on the row, with unit values *)
  module Reg = CCHashTrie.Make (Key)

  let run (items : In_item_deletion.t_items_tbl)
      (queries : In_item_deletion.t_queries) : string list =
    (* The items in flight arrive in the ENVIRONMENT rather than through build
       queries.  Missing this is what the `agree` column caught on the first
       run of baseline.ml: the transcription started empty, so every
       containsHit said "free" while the subject said "deleting". *)
    let reg =
      ref
        (List.fold_left
           (fun t (r : In_item_deletion.t_row) -> Reg.add r () t)
           Reg.empty items) in
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
         | 1 -> reg := Reg.add item () !reg
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
    let by_id = ref STrie.empty in
    let outputs = ref [] in
    let suggested = ref suggested0 in
    let say (n : int) = outputs := Rt.string_of_int_c n :: !outputs in
    List.iter
      (fun (q : In_user_search.t_queries_elem) ->
         match q.f_kind with
         (* User.get(id, true) -> AllUsers.putIfAbsent *)
         | 0 ->
             let u = q.f_new_user in
             by_id := STrie.add u.f_id u !by_id
         (* AllUsers.remove(id) *)
         | 1 -> by_id := STrie.remove q.f_k !by_id
         (* find(id): the ConcurrentHashMap lookup *)
         | 2 ->
             say (match probe (STrie.get q.f_k !by_id) with
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
             STrie.iter
               ~f:(fun _ (u : In_user_search.t_row) ->
                 Count.visit 1;
                 if Rt.str_contains u.f_fullName tok then hits := u :: !hits)
               !by_id;
             suggested :=
               List.fold_left
                 (fun s u -> In_user_search.M_suggested.add u s)
                 In_user_search.M_suggested.empty
                 (List.sort In_user_search.cmp_row !hits))
      queries;
    (!outputs, !suggested)
end

(* ---------- what has been monomorphized so far ----------

   One module, as a pilot: the pattern is proved end to end -- including the
   agreement check -- before the other ten are rewritten, because a rewrite
   that loses fidelity to the cited source is the one failure this cannot
   detect. *)

let done_so_far =
  [ Lookin.name; Keycloak.name; NamedCache.name; ItemDeletion.name;
    UserSearch.name ]

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

let checks : (string * (Gen.workload -> bool)) list =
  [ ("lookin", check_lookin);
    ("user_search", check_user_search);
    ("item_deletion", check_item_deletion);
    ("keycloak", check_keycloak);
    ("named_cache", check_named_cache) ]
