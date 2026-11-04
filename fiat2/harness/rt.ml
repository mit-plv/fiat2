(* The runtime the GENERATED code links, and the author transcriptions with it.

   Everything here charges by exactly the rule value.ml uses, and the string
   comparison IS value.ml's rather than a copy of it, so a monomorphic record
   and a boxed one are priced by one convention and the two sides of the
   author comparison stay readable against each other.  That was the whole
   argument for the matched columns: "not one convention applied twice -- the
   same code".

   WHAT MONOMORPHIZATION LEGITIMATELY REMOVES, as against hides.  A boxed
   record carries its field NAMES at run time: value.ml's compare walks an
   association list, and its hash mixes in Hashtbl.hash of every name.  A
   generated record has its fields at constant offsets and no names at all, so
   that work does not happen rather than going uncounted.  It is the
   representation win the compiled backend exists to measure -- and it is why
   both sides have to be monomorphic before a ratio between them means
   anything.

   NOT Hashtbl.hash on a composite.  OCaml's polymorphic hash is
   seeded_hash_param 10 100 0: at most ten meaningful nodes examined and a
   hundred traversed.  On a whole-row key it hashes a prefix and stops, which
   would hand whichever side used it a flat cost it had not earned.  The
   generated hashes below walk the whole value, charging per node exactly as
   value.ml's does. *)

let cmp_int (a : int) (b : int) : int = incr Count.comparisons; Int.compare a b
let cmp_bool (a : bool) (b : bool) : int = incr Count.comparisons; Bool.compare a b
let cmp_unit (_ : unit) (_ : unit) : int = incr Count.comparisons; 0

let cmp_string (a : string) (b : string) : int =
  incr Count.comparisons; Value.string_compare a b

let cmp_option (cmp : 'a -> 'a -> int) (a : 'a option) (b : 'a option) : int =
  incr Count.comparisons;
  match a, b with
  | None, None -> 0
  | None, Some _ -> -1
  | Some _, None -> 1
  | Some a, Some b -> cmp a b

let cmp_list (cmp : 'a -> 'a -> int) (a : 'a list) (b : 'a list) : int =
  incr Count.comparisons; Value.list_compare cmp a b

(* ---------- hashing, by value.ml's rule: one unit per node ---------- *)

let hash_int (n : int) : int = incr Count.hashing; Hashtbl.hash n
let hash_bool (b : bool) : int = incr Count.hashing; Hashtbl.hash b
let hash_unit (_ : unit) : int = incr Count.hashing; 17

(* every byte, because a hash cannot stop early where a comparison can *)
let hash_string (s : string) : int =
  incr Count.hashing; Count.chars (String.length s); Hashtbl.hash s

let hash_option (h : 'a -> int) (o : 'a option) : int =
  incr Count.hashing;
  match o with None -> 19 | Some v -> 23 + (31 * h v)

let hash_list (h : 'a -> int) (l : 'a list) : int =
  incr Count.hashing;
  List.fold_left (fun acc v -> (acc * 31) + h v) 29 l

(* a generated record's own node, charged before its fields are walked, so a
   k-field record of scalars costs k+1 on both counters exactly as the boxed
   one does *)
let node () : unit = incr Count.hashing
let cmp_node () : unit = incr Count.comparisons

(* ---------- marshalling in, which is NOT counted ----------

   A workload arrives as the generators built it, in value.ml's boxed form,
   and the compiled program needs it in monomorphic form.  Converting is not
   work the program implies, so nothing below charges a counter -- and the
   conversion has to happen OUTSIDE the timed region, before Count.reset, or
   it would be measured as if it were.

   These raise rather than return an option: a shape mismatch here is a bug
   in the generator or in the type the backend was given, not an input a run
   should limp along with. *)

let as_int = function Value.VInt n -> n | _ -> failwith "of_value: expected an int"
let as_bool = function Value.VBool b -> b | _ -> failwith "of_value: expected a bool"
let as_string = function
  | Value.VString s -> s
  | _ -> failwith "of_value: expected a string"
let as_unit = function Value.VUnit -> () | _ -> failwith "of_value: expected unit"
let as_list = function
  | Value.VList l -> l
  | _ -> failwith "of_value: expected a list"
let as_option = function
  | Value.VOption o -> o
  | _ -> failwith "of_value: expected an option"
let as_record = function
  | Value.VRecord l -> l
  | _ -> failwith "of_value: expected a record"

(* a record's fields are name-sorted, so this is a lookup and not a search *)
let fld (l : (string * Value.t) list) (n : string) : Value.t =
  match List.assoc_opt n l with
  | Some v -> v
  | None -> failwith ("of_value: record has no field " ^ n)

(* The three collection stores, unwrapped.  A boxed bag or set is NOT a
   VList: it holds a store, so reading one is a fold and not a cast.  Getting
   that wrong is how `of_value` for a bag silently became a list cast -- the
   generated reader type-checked, and running it on a real workload is what
   said otherwise. *)
let as_set = function
  | Value.VSet s -> s
  | _ -> failwith "of_value: expected a set"

let as_dict = function
  | Value.VDict (_, d) -> d
  | _ -> failwith "of_value: expected a dictionary"

(* a bag in canonical order, which is what TBag's list representation holds.
   The ordering costs comparisons, and like everything else here it must
   happen before Count.reset. *)
let as_bag_list = function
  | Value.VBag b -> Value.bcanon b
  | _ -> failwith "of_value: expected a bag"

(* ---------- equality ----------

   value.ml defines `equal a b = compare a b = 0`, so these charge exactly as
   the comparisons do and the two sides stay priced alike.

   Why a generated EQUALITY and not a generated compare, for the collections.
   The semantics compares collections by canonical form, and value.ml has to
   produce that form for a hashed store because it needs an ORDERING.  An
   equality needs no order: equal bindings are an equal map, which a
   cardinality check and a fold-and-probe decide.  That is also why a record
   holding a dictionary has no compare -- a persistent trie has no key order
   to offer -- while it does have this.  Used only by the store comparison,
   which runs outside the timed region. *)

let eq_int (a : int) (b : int) : bool = cmp_int a b = 0
let eq_bool (a : bool) (b : bool) : bool = cmp_bool a b = 0
let eq_unit (a : unit) (b : unit) : bool = cmp_unit a b = 0
let eq_string (a : string) (b : string) : bool = cmp_string a b = 0

let eq_option (eq : 'a -> 'a -> bool) (a : 'a option) (b : 'a option) : bool =
  incr Count.comparisons;
  match a, b with
  | None, None -> true
  | Some a, Some b -> eq a b
  | _ -> false

let rec eq_list (eq : 'a -> 'a -> bool) (a : 'a list) (b : 'a list) : bool =
  incr Count.comparisons;
  match a, b with
  | [], [] -> true
  | x :: a, y :: b -> eq x y && eq_list eq a b
  | _ -> false

(* a bag's list representation has no canonical order of its own -- the
   program built it by consing and appending -- so equality is of MULTISETS,
   and sorting both is the cheapest way to decide it *)
let eq_bag (cmp : 'a -> 'a -> int) (a : 'a list) (b : 'a list) : bool =
  incr Count.comparisons;
  List.length a = List.length b
  && eq_list (fun x y -> cmp x y = 0) (List.sort cmp a) (List.sort cmp b)

(* ---------- the operators the generated code calls ----------

   Each one charges what eval.ml's transcription of the same operator
   charges, so the compiled and interpreted sides are priced alike wherever
   the work is the same.  Arithmetic charges nothing on either side: it is
   neither a key comparison nor a byte, and no exponent turns on it.

   `rows` is charged at the SITES eval.ml charges Count.visit, by the
   generated code itself rather than here, because only the generator knows
   how many elements a construct iterated. *)

let add_int (a : int) (b : int) : int = a + b
let sub_int (a : int) (b : int) : int = a - b
let mul_int (a : int) (b : int) : int = a * b
let div_int (a : int) (b : int) : int = if b = 0 then 0 else a / b
let mod_int (a : int) (b : int) : int = if b = 0 then a else a mod b

(* the digits an int-to-string emits *)
let string_of_int_c (n : int) : string =
  let s = string_of_int n in
  Count.chars (String.length s);
  s

(* the bytes a concatenation writes *)
let concat_string (a : string) (b : string) : string =
  Count.chars (String.length a + String.length b);
  a ^ b

(* the positions a naive substring scan really compares before it stops --
   eval.ml's str_contains, which is the function the author transcriptions
   call too, so the subject that is ABOUT string matching is priced the same
   on all three columns *)
let str_contains (s : string) (p : string) : bool = Eval.str_contains s p

(* three-character windows in order, charged as the bytes each one copies *)
let trigrams (s : string) : string list =
  let n = String.length s in
  let k = max 0 (n - 2) in
  Count.chars (3 * k);
  List.init k (fun i -> String.sub s i 3)

(* split on any separator, charging the string once and each word's bytes *)
let words (seps : string) (s : string) : string list =
  Count.chars (String.length s);
  let out = ref [] and buf = Buffer.create 16 in
  let flush () =
    if Buffer.length buf > 0 then begin
      Count.chars (Buffer.length buf);
      out := Buffer.contents buf :: !out;
      Buffer.clear buf
    end in
  String.iter
    (fun c -> if String.contains seps c then flush () else Buffer.add_char buf c)
    s;
  flush ();
  List.rev !out

(* ---------- the two structures whose storage the RUN chooses ----------

   count.ml's `structures` parameter was built for the interpreted columns,
   where value.ml's dstore and sstore already hold either a balanced tree or
   CCHashTrie's persistent HAMT and the setting picks between them.  The
   compiled columns had no equivalent: a generated set was Set.Make because
   its type said TSet, a transcription's HashMap was CCHashTrie because its
   author wrote a hash map, and the two could not be brought to a common
   storage at all.  That is what left `matched` unavailable on this side and
   made the missing set_kind show up as a per-subject ratio -- item_deletion
   at 2.68x, our tree against their hash -- rather than as one number.

   These two functors close it.  A key module gets one selectable map and one
   selectable set, each holding the storage its SITUATION and the setting name
   between them, and both columns create theirs through the same functor.  So
   the claim "the two sides run the same data structure" holds on the compiled
   side for the same reason it holds on the interpreted one: there is one
   implementation, not two priced alike.

   WHAT IS NOT SELECTABLE, and why that is the point rather than a gap.  A
   Ranged dictionary stays Map.Make under every setting, because codegen emits
   ODictRange as a `split` and no hash table answers a range query.  That is
   count.ml's `ordered` and it is the same refusal: the parameter exists to
   stop the structure choice confounding the comparison, not to pretend a
   structure can do what it cannot.

   WHAT THE DISPATCH COSTS.  One match on a two-constructor variant per
   operation, against a point access of roughly 200ns -- under a percent, and
   paid by all three columns alike, so it cannot move a ratio by more than
   that.  It is still a real change to the `typed` numbers, which is why those
   are re-measured rather than assumed to be the ones printed before.

   WHERE A SETTING CHANGES AN ASYMPTOTIC AND NOT A CONSTANT.  Two places, and
   both are in the set.  A hashed set has no least element, so min_elt_opt and
   max_elt_opt fold the whole store where a tree answers from a leftmost
   descent; and the set algebra becomes |a| probes where a tree merges two
   ordered structures -- see the comment on `union` below.  Neither is a
   defect in the Hashes column: they are what a backend that chose a hash set
   would really have to do, and they are the argument that a set_kind would
   have to be a CAPABILITY annotation in the manner of dict_kind and
   ODictRange rather than a free switch.  Hashing a set that the program takes
   a minimum of, or intersects, is not licensed by anything. *)

module type KEY = sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

(* A keyed map.  The operation names are CCHashTrie's where the two libraries
   disagree (`get`, not `find_opt`) because the generated code was written
   against a trie; `find_opt` is offered as well so that a transcription of an
   author's TreeMap still reads like one. *)
module SelMap (K : KEY) = struct
  module T = Map.Make (K)
  module H = CCHashTrie.Make (K)

  type key = K.t
  type 'v t = Tree of 'v T.t | Hash of 'v H.t

  (* The situation and the setting pick the storage ONCE, when the structure
     is created.  Nothing reads the setting between a `make` and the accesses
     on the result within a run, so this cannot capture a stale choice -- the
     same argument baseline.ml's kmake rests on. *)
  let make (sit : Count.situation) : 'v t =
    match Count.kind_of sit with
    | Count.Ordered -> Tree T.empty
    | Count.Hashed -> Hash H.empty

  let get (k : key) (d : 'v t) : 'v option =
    match d with Tree m -> T.find_opt k m | Hash h -> H.get k h

  let find_opt = get

  let add (k : key) (v : 'v) (d : 'v t) : 'v t =
    match d with Tree m -> Tree (T.add k v m) | Hash h -> Hash (H.add k v h)

  let remove (k : key) (d : 'v t) : 'v t =
    match d with Tree m -> Tree (T.remove k m) | Hash h -> Hash (H.remove k h)

  let mem (k : key) (d : 'v t) : bool =
    match d with Tree m -> T.mem k m | Hash h -> H.mem k h

  (* Neither is a key access and neither is charged as one: java.util.HashMap
     keeps its own size, and a walk charges the rows its caller looks at. *)
  let cardinal (d : 'v t) : int =
    match d with Tree m -> T.cardinal m | Hash h -> H.cardinal h

  (* NOT `cardinal d = 0`: cardinal is a FOLD in both libraries -- OCaml's
     Map keeps a height per node and CCHashTrie keeps nothing -- so asking for
     the size to compare it with zero walks the whole store. *)
  let is_empty (d : 'v t) : bool =
    match d with Tree m -> T.is_empty m | Hash h -> H.is_empty h

  (* Map's argument order, for both storages, so that generated code reads the
     same whichever kind of dictionary it holds.  A WALK OVER A HASHED STORE
     HAS NO ORDER: anything a caller builds by insertion from one of these has
     to be order-insensitive, and `agree` at every size is what checks it. *)
  let fold (f : key -> 'v -> 'a -> 'a) (d : 'v t) (init : 'a) : 'a =
    match d with
    | Tree m -> T.fold f m init
    | Hash h -> H.fold ~f:(fun acc k v -> f k v acc) ~x:init h

  let iter (f : key -> 'v -> unit) (d : 'v t) : unit =
    match d with Tree m -> T.iter f m | Hash h -> H.iter ~f h

  (* equal bindings, decided without producing a key order a trie does not
     have: same cardinality, and every binding of one found in the other *)
  let equal (eq : 'v -> 'v -> bool) (a : 'v t) (b : 'v t) : bool =
    match a, b with
    (* a tree can decide this by walking the two in step, which stops at the
       first difference; the cardinal-and-membership form below is what a store
       WITHOUT a key order has to do, and taking it for the tree as well would
       charge the ordered column for an absence it does not have *)
    | Tree x, Tree y -> T.equal eq x y
    | _ ->
        cardinal a = cardinal b
        && fold (fun k v acc -> acc && (match get k b with
                                        | Some w -> eq v w
                                        | None -> false))
             a true
end

(* A set.  `elements` is ASCENDING under both storages -- sorted where the
   store has no order -- because compare and equal are built on it and the
   `agree` and `interp` checks compare stores across columns: a set must mean
   the same thing under every setting even where it costs something
   different. *)
module SelSet (K : KEY) = struct
  module T = Set.Make (K)
  module H = CCHashTrie.Make (K)

  type elt = K.t
  type t = Tree of T.t | Hash of unit H.t

  let make (sit : Count.situation) : t =
    match Count.kind_of sit with
    | Count.Ordered -> Tree T.empty
    | Count.Hashed -> Hash H.empty

  let add (x : elt) (s : t) : t =
    match s with Tree m -> Tree (T.add x m) | Hash h -> Hash (H.add x () h)

  let mem (x : elt) (s : t) : bool =
    match s with Tree m -> T.mem x m | Hash h -> H.mem x h

  let remove (x : elt) (s : t) : t =
    match s with Tree m -> Tree (T.remove x m) | Hash h -> Hash (H.remove x h)

  let cardinal (s : t) : int =
    match s with Tree m -> T.cardinal m | Hash h -> H.cardinal h

  let is_empty (s : t) : bool =
    match s with Tree m -> T.is_empty m | Hash h -> H.is_empty h

  let fold (f : elt -> 'a -> 'a) (s : t) (init : 'a) : 'a =
    match s with
    | Tree m -> T.fold f m init
    | Hash h -> H.fold ~f:(fun acc k () -> f k acc) ~x:init h

  let iter (f : elt -> unit) (s : t) : unit = fold (fun x () -> f x) s ()

  let elements (s : t) : elt list =
    match s with
    | Tree m -> T.elements m
    | Hash h -> List.sort K.compare (List.map fst (H.to_list h))

  (* An empty set is an empty set whichever storage it is in, so a `make` on
     one side and a `make` on the other still compare equal; nothing in a run
     mixes the two, and this costs nothing to be right about. *)
  let compare (a : t) (b : t) : int =
    match a, b with
    | Tree x, Tree y -> T.compare x y
    | _ -> cmp_list K.compare (elements a) (elements b)

  (* HashSet.equals compares the two sizes before it compares the elements,
     and with java.util.HashSet's O(1) size that is free.  A hash trie's
     cardinal is a fold, so the size test below would be O(n) -- and the
     commonest caller is an EMPTINESS test, `equal (diff bkt {x}) empty`,
     which is what codegen emits to decide whether a keyed delete has emptied
     a bucket.  The two is_empty probes are the faithful stand-in for the size
     check that matters, and they keep that test O(1) as it is on a tree.

     value.ml ANSWERS THE SAME ARM FOR THE SAME REASON: its OEq against the
     empty BAG is special-cased, because asking whether a bucket has emptied
     asks nothing about order, and before it was answered directly it sorted
     the bucket to find out.  Same shape, same caller, a different
     collection. *)
  let equal (a : t) (b : t) : bool =
    match a, b with
    | Tree x, Tree y -> T.equal x y
    | _ when is_empty a -> is_empty b
    | _ when is_empty b -> false
    | _ -> cardinal a = cardinal b && fold (fun x acc -> acc && mem x b) a true

  (* A HASHED SET HAS NO LEAST ELEMENT.  The tree answers from a leftmost
     descent, which iterates no stored element and compares no key; the trie
     has to look at all of them.  See the header: this is one of the two
     places a setting moves an exponent, and it is the honest consequence of
     hashing a structure whose operations read the key order. *)
  let min_elt_opt (s : t) : elt option =
    match s with
    | Tree m -> T.min_elt_opt m
    | Hash _ ->
        fold
          (fun x acc ->
             match acc with
             | None -> Some x
             | Some m -> if K.compare x m < 0 then Some x else acc)
          s None

  let max_elt_opt (s : t) : elt option =
    match s with
    | Tree m -> T.max_elt_opt m
    | Hash _ ->
        fold
          (fun x acc ->
             match acc with
             | None -> Some x
             | Some m -> if K.compare x m > 0 then Some x else acc)
          s None

  (* THE SET ALGEBRA IS WHERE A TREE AND A HASH DIVERGE MOST, and the shapes
     below are the two real implementations rather than one emulating the
     other.  A tree combines two sets by MERGING them, walking both in key
     order and reusing whole subtrees; a hash table has no order to merge on,
     so java.util.HashSet's addAll, retainAll and removeAll iterate one side
     and probe or mutate the other -- one key access per element of the side
     they iterate, where the merge does far fewer.  That is why `hashes` is not uniformly the cheaper column, and
     item_deletion is where it shows: a whole-row key must be hashed in full,
     where a comparison stops at the first differing field.

     WHICH SIDE IS ITERATED IS NOT A FREE CHOICE, and getting it wrong is how
     this was first written.  ALL THREE ITERATE `b`, working into a copy of
     one operand, because `b` is the smaller in every shape codegen emits:
     `union acc {x}` for a LikeSet flatmap, `diff bucket {x}` for a keyed
     delete, and `inter bucket accumulator` for the trigram intersection,
     whose accumulator shrinks monotonically.  Iterating `a` instead walks the
     whole accumulator or bucket to add or remove ONE element, which turns an
     index build and a delete into n^2.

     value.ml DOES NOT DO IT THIS WAY, and the difference is not an oversight
     in either: its sunion and sinter call scardinal to pick the smaller side,
     the way AbstractSet does, which it can afford because it charges only key
     accesses and a cardinal is not one.  Here the cardinal is real time --
     both libraries fold to compute it -- so paying one per operation would
     itself be the n^2.  A compiled structure has to choose statically; these
     are the choices the emitted shapes make right.

     HOW THE TWO DEFECTS WERE FOUND, because they were found differently and
     that is the useful part.  The `diff` one is inside the ops phase, and the
     COUNTERS measured it exactly: item_deletion/deregister at 1031x and
     user_search/remove at 10595x, bit-identical across two runs, which is
     what a deterministic counter is for.  The `union` one is inside the index
     BUILD, which `matched` subtracts, so neither column measured it at all --
     what it produced was an UNSTABLE ratio in the seconds, the same cell
     reading 14.95, 916.44 and 1073.55 on three runs, which is the difference
     of two large noisy numbers and a symptom that the experiment had broken
     rather than a measurement of anything.

     So: a counted figure that moves is a finding, and a timed figure that
     moves BETWEEN RUNS is not a small version of one.  A per-op difference
     cannot see a pathological build, and the instability is the only thing it
     has to say so with. *)
  let union (a : t) (b : t) : t =
    match a, b with
    | Tree x, Tree y -> Tree (T.union x y)
    | _ -> fold (fun x acc -> add x acc) b a

  let inter (a : t) (b : t) : t =
    match a, b with
    | Tree x, Tree y -> Tree (T.inter x y)
    | _ -> fold (fun x acc -> if mem x a then acc else remove x acc) b b

  let diff (a : t) (b : t) : t =
    match a, b with
    | Tree x, Tree y -> Tree (T.diff x y)
    | _ -> fold (fun x acc -> remove x acc) b a
end
