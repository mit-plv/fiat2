(* The values the evaluator computes with.

   This is the one place where the implementation departs from the Gallina
   semantics on purpose, so it is worth being exact about what the departure
   is.

   Value.v represents a dictionary as an association list that is sorted and
   duplicate-free, a bag as a sorted duplicate-free list of (element,
   multiplicity) pairs, and a set as a sorted duplicate-free list.  Each of
   those is a CANONICAL form: for a given finite map, multiset or set there
   is exactly one list satisfying the invariant, which is why the semantics
   can compare two collections by comparing their representations.

   A representation here has to denote the same map, multiset or set, and it
   has to pay for anything the semantics can OBSERVE about the canonical
   form.  What the semantics observes is narrow: OEq on two collections, and
   ESort, which hands back the canonical order as a list.  Nothing else can
   see it.  So the three types are represented by what their own operations
   need, and the two observers pay:

     dict   a balanced tree ordered by the same comparison.  Canonical in
            the same sense as the sorted list, so the bijection is the
            identity on bindings; a lookup, an insert, a delete and a range
            restriction cost a path rather than a copy.

            Of those four operations only the RANGE RESTRICTION needs the
            order, and Language.v:79 says which dictionaries can be asked for
            one: AEmptyDict carries a dict_kind, outside the option, so it
            survives extraction on every dictionary a program creates.  Across
            the subject terms 19 are Unranged and 2 are Ranged.

            So the dictionary carries its [dict_rep] below, and REPRESENTATION
            AND CHARGE ARE SEPARATE QUESTIONS.  A dictionary charged as a hash
            table -- the key's hash, by Count.hash, as Count.structures
            directs -- is still STORED in the tree, because OCaml's standard
            library has no persistent hash map and a hand-written one would put
            the harness's own HAMT into the numbers instead of a backend's.
            The tree's descent is therefore charged to neither counter
            (Count.quiet).
            That is the same move the bag below makes, in the same direction:
            the counters are a cost model, and what the representation must
            do is denote the right value and pay for what the semantics can
            observe.  Wall-clock SECONDS do not follow the charge, so they
            remain what they always were -- a check on shape, not evidence.

     set    a balanced tree.  A set has to reject duplicates on insert, so
            it needs the order anyway, and OSetMem is a probe.

     bag    an UNORDERED list, with multiplicity as repetition.  A bag
            rejects nothing and probes nothing: every operation on one in
            these programs is an insert, a concatenation or a fold.  Keeping
            it sorted would charge a logarithmic factor, and a record-valued
            comparison, for work no backend would do.  Canonicalising is
            therefore deferred to the two places that can see it, and those
            places sort and are charged for it -- counted separately, as
            [canonicalisations], because a subject that triggered one often
            would be one whose numbers deserve a second look.

            That last sentence earned its keep.  A bag EQUALITY against the
            empty bag is not a question about order, but the generic arm
            answered it by sorting both sides, so asking whether a bucket had
            emptied cost the bucket a sort -- MEASURED at 48 comparisons per
            delete in HA_AreaRegistry, 62% of that kind's whole cost, and
            Theta(b log b) in the bucket size where a backend pays Theta(1).
            The empty cases are therefore answered directly below.  That is
            the same move the dictionary makes above -- the representation
            stays a list and the CHARGE is what a backend would pay -- and it
            is order-preserving, not an approximation: sorting [] yields [],
            and list_compare [] (_ :: _) is -1 whatever the order, so the
            three arms return exactly what the generic one returned.

   The comparison is NOT a free choice.  The semantics observes it -- OEq on
   two collections compares canonical forms, and ODictRange reads the key
   order directly -- so it has to be exactly Value.value_compare.  It is
   transcribed below line for line, and that transcription is the thing to
   audit in this file.

   Two facts about the transcription:
     * Rocq's String.compare walks the two strings comparing Ascii codes as
       unsigned numbers, which is what OCaml's String.compare does on bytes.
     * value_compare orders values of DIFFERENT constructors by the order its
       final fall-through arms are written in, which is the [rank] below.  No
       well-typed program ever compares across constructors, but the
       evaluator is not allowed to assume that. *)

(* The dict_kind the dictionary's AEmptyDict carried, retained at runtime.

   It is the TYPE's annotation and nothing more -- deliberately not a charging
   decision, because the charge also depends on Count.structures and the two
   must not be conflated.  Keeping the kind itself is what lets ODictRange
   reject an Unranged dictionary under EVERY setting of that parameter: if
   this said "tree" or "hash" instead, the conservative Trees setting would
   turn that rejection into a silent success.

   It is not part of the value: two dictionaries with the same bindings denote
   the same finite map and compare equal whatever they are charged as, which
   is why [compare] below ignores it. *)
type dict_rep =
  | RRanged    (* a range restriction may read the key order, so it is a tree *)
               (* under every setting and its descent is the cost *)
  | RUnranged  (* no operator on it can read the key order, so Count.licensed *)
               (* decides, and only the Trees floor declines the hash *)

(* The constructor order of value_compare's fall-through arms, read off
   Value.v: VUnit is Lt against everything, then VBool against everything
   remaining, and so on, leaving VSet greatest. *)

module rec V : sig
  type t =
    | VInt of int
    | VBool of bool
    | VString of string
    | VOption of t option
    | VList of t list
    | VRecord of (string * t) list   (* sorted by field name *)
    | VDict of dict_rep * dstore
    | VBag of t list                 (* UNORDERED; multiplicity is repetition *)
    | VSet of VSet.t
    | VUnit

  (* HOW a dictionary is stored, as against [dict_rep], which is what its
     TYPE says.  The two are now the same question for the first time: the
     setting picks the store at creation, and the store is what the operations
     actually run on, so a cost is counted rather than charged.

     DHash has no [split] -- CCHashTrie does not provide one, because a hash
     table has no key order to split at.  So ODictRange is not rejected by a
     [failwith] any more; it cannot be WRITTEN against a hashed store, and
     TyODictRange's restriction to TDict Ranged is enforced by OCaml's type
     checker rather than honoured by hand. *)
  and dstore =
    | DTree of t VMap.t
    | DHash of t VTrie.t

  val compare : t -> t -> int
  (* for CCHashTrie's functor, which wants an equal and a hash *)
  val equal : t -> t -> bool
  val hash : t -> int
  (* the one fold that may look inside a store, so that callers outside this
     module never case-split on the representation *)
  val dfold : (t -> t -> 'a -> 'a) -> dstore -> 'a -> 'a
end = struct
  type t =
    | VInt of int
    | VBool of bool
    | VString of string
    | VOption of t option
    | VList of t list
    | VRecord of (string * t) list
    | VDict of dict_rep * dstore
    | VBag of t list
    | VSet of VSet.t
    | VUnit

  and dstore =
    | DTree of t VMap.t
    | DHash of t VTrie.t

  let rank = function
    | VUnit -> 0 | VBool _ -> 1 | VInt _ -> 2 | VString _ -> 3
    | VOption _ -> 4 | VList _ -> 5 | VRecord _ -> 6 | VDict _ -> 7
    | VBag _ -> 8 | VSet _ -> 9

  (* list_compare: equal length compares elementwise, otherwise the shorter
     comes first *)
  let rec list_compare cmp l1 l2 =
    match l1, l2 with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | x :: l1, y :: l2 ->
        let c = cmp x y in
        if c <> 0 then c else list_compare cmp l1 l2

  let rec compare (a : t) (b : t) : int =
    incr Count.comparisons;
    match a, b with
    | VInt a, VInt b -> Int.compare a b
    | VBool a, VBool b -> Bool.compare a b
    | VString a, VString b -> String.compare a b
    | VOption a, VOption b ->
        (match a, b with
         | None, None -> 0
         | None, Some _ -> -1
         | Some _, None -> 1
         | Some a, Some b -> compare a b)
    | VList a, VList b -> list_compare compare a b
    | VRecord a, VRecord b ->
        list_compare
          (fun (s1, v1) (s2, v2) ->
             let c = String.compare s1 s2 in
             if c <> 0 then c else compare v1 v2)
          a b
    (* VMap.compare and VSet.compare walk their arguments in ascending key
       order and stop at the first difference, which is the same lexicographic
       comparison of canonical forms that dict_compare, bag_compare and
       list_compare perform on the sorted lists *)
    (* The bindings decide the answer -- equal bindings are an equal map, so
       the kind does not change what this returns.  It changes the CHARGE: a
       dictionary being charged as a hash table has no key order of its own,
       so OEq on one has to produce the canonical order the semantics compares,
       which is the same thing the bag below pays and is charged the same way.
       Under the Trees setting nothing is charged as a hash, and nothing here
       canonicalises. *)
    | VDict (_, DTree a), VDict (_, DTree b) -> VMap.compare compare a b
    | VDict (_, a), VDict (_, b) ->
        (* a hashed store has no key order of its own, so the order the
           semantics compares has to be produced -- which is the same cost
           the bag below pays, charged the same way *)
        let canon = function
          | DTree d -> VMap.bindings d
          | DHash h ->
              incr Count.canonicalisations;
              List.sort (fun (k1, _) (k2, _) -> compare k1 k2) (VTrie.to_list h) in
        list_compare
          (fun (k1, v1) (k2, v2) ->
             let c = compare k1 k2 in
             if c <> 0 then c else compare v1 v2)
          (canon a) (canon b)
    (* An emptiness test asks nothing about order, so it does not pay for
       one: these three return exactly what sorting both sides and comparing
       returned, for the reason given at the head of this file. *)
    | VBag [], VBag [] -> 0
    | VBag [], VBag _ -> -1
    | VBag _, VBag [] -> 1
    (* the only place a bag's canonical order is observable, and the only
       place it is paid for *)
    | VBag a, VBag b ->
        incr Count.canonicalisations;
        list_compare compare (List.sort compare a) (List.sort compare b)
    | VSet a, VSet b -> VSet.compare a b
    | VUnit, VUnit -> 0
    | _ -> Int.compare (rank a) (rank b)

  let equal (a : t) (b : t) : bool = compare a b = 0

  (* The hash a hashed store actually uses, and therefore the hash the
     counters actually count: one unit per value node, charged HERE, as
     [compare] charges one per node it walks.  So `comparisons + hashing`
     stays one figure for the work done on keys, and under a hashed store
     that figure is now measured rather than modelled.

     It must agree with [equal], which cannot see the order of a bag, a set
     or a dictionary -- so those combine their elements COMMUTATIVELY, with
     the cardinality mixed in.  Sorting to hash would defeat the point. *)
  let rec hash (v : t) : int =
    incr Count.hashing;
    match v with
    | VInt n -> Hashtbl.hash n
    | VBool b -> Hashtbl.hash b
    | VString s -> Hashtbl.hash s
    | VUnit -> 17
    | VOption None -> 19
    | VOption (Some v) -> 23 + (31 * hash v)
    | VList l -> List.fold_left (fun acc v -> (acc * 31) + hash v) 29 l
    | VRecord l ->
        List.fold_left
          (fun acc (f, v) -> (acc * 31) + Hashtbl.hash f + hash v) 37 l
    | VDict (_, d) ->
        dfold (fun k v acc -> acc + (hash k * 31) + hash v) d 41
    | VBag b ->
        List.fold_left (fun acc v -> acc + hash v) (43 + List.length b) b
    | VSet s -> VSet.fold (fun v acc -> acc + hash v) s 47

  (* the store's operations, in the one place that may look inside it *)
  and dfold : 'a. (t -> t -> 'a -> 'a) -> dstore -> 'a -> 'a =
    fun f d init ->
    match d with
    | DTree m -> VMap.fold f m init
    | DHash h -> VTrie.fold ~f:(fun acc k v -> f k v acc) ~x:init h
end
and VMap : (Map.S with type key = V.t) = Map.Make (V)
and VSet : (Set.S with type elt = V.t) = Set.Make (V)
and VTrie : (CCHashTrie.S with type key = V.t) = CCHashTrie.Make (V)

include V

(* [Value.value] reads better at the use sites than [Value.t] *)
type value = t

(* ---------- the dictionary store ----------

   Every operation a dictionary has, once per store, so that no caller outside
   this file case-splits on the representation.  Each is the operation the
   store really performs -- a tree path or a trie descent -- and the counters
   see it: [compare] charges the tree's comparisons, [hash] charges the trie's
   hash and [equal] its leaf comparison.  Nothing here is modelled.

   There is deliberately no [dsplit].  CCHashTrie has none to offer, which is
   the whole point: a range restriction is a question only an ordered store can
   answer, and the only store that can be asked is the one TyODictRange's
   TDict Ranged admits. *)

let dempty (r : dict_rep) : dstore =
  match r with
  | RRanged -> DTree VMap.empty
  (* Unranged is where the setting has a choice to make, and this is the one
     place it is made *)
  | RUnranged ->
      (match Count.licensed () with
       | Count.Ordered -> DTree VMap.empty
       | Count.Hashed -> DHash VTrie.empty)

let dfind (k : t) (d : dstore) : t option =
  match d with
  | DTree m -> VMap.find_opt k m
  | DHash h -> VTrie.get k h

let dmem (k : t) (d : dstore) : bool =
  match d with DTree m -> VMap.mem k m | DHash h -> VTrie.mem k h

let dadd (k : t) (v : t) (d : dstore) : dstore =
  match d with
  | DTree m -> DTree (VMap.add k v m)
  | DHash h -> DHash (VTrie.add k v h)

let dremove (k : t) (d : dstore) : dstore =
  match d with
  | DTree m -> DTree (VMap.remove k m)
  | DHash h -> DHash (VTrie.remove k h)

let dcardinal (d : dstore) : int =
  match d with DTree m -> VMap.cardinal m | DHash h -> VTrie.cardinal h

(* The bindings in CANONICAL order.  A tree is already in it; a trie is not,
   and producing it is the cost the semantics can observe, so it is charged
   exactly where [compare] charges it. *)
let dbindings (d : dstore) : (t * t) list =
  match d with
  | DTree m -> VMap.bindings m
  | DHash h ->
      incr Count.canonicalisations;
      List.sort (fun (k1, _) (k2, _) -> compare k1 k2) (VTrie.to_list h)

(* and in whatever order the store holds them, for the callers that do not
   care -- ODictValues builds a BAG, which has no order to get wrong *)
let dvalues_unordered (d : dstore) : t list =
  dfold (fun _ v acc -> v :: acc) d []

(* The work a KEY costs, by the same rule [compare] charges for walking one:
   one unit per node, with a string counting as one node because
   Value.compare charges one for String.compare.  That makes
   `comparisons + hashing` a single figure, and it carries the caveat cmps
   already carries -- it is honest while the generators keep keys short.

   A bag contributes its elements without their order, since a hash
   consistent with [eqb] cannot depend on an order [eqb] cannot see. *)
let rec key_work (v : t) : int =
  match v with
  | VInt _ | VBool _ | VString _ | VUnit | VOption None -> 1
  | VOption (Some v) -> 1 + key_work v
  | VList l -> List.fold_left (fun n v -> n + key_work v) 1 l
  | VRecord l -> List.fold_left (fun n (_, v) -> n + key_work v) 1 l
  | VDict (_, d) -> dfold (fun k v n -> n + key_work k + key_work v) d 1
  | VBag b -> List.fold_left (fun n v -> n + key_work v) 1 b
  | VSet s -> VSet.fold (fun v n -> n + key_work v) s 1

(* What a point access at key [k] costs on a structure of the given kind,
   performing the access with [f].  THE ONE RULE, called by eval.ml for the
   optimizer's output and by baseline.ml for the original authors' code, so
   the two columns are charged by the same function rather than by two helpers
   that agree on inspection.  That is the only reason a ratio between them
   means anything.

   WHAT IS LEFT OF THIS, AND WHAT IS NOT.  Dictionaries no longer come here:
   they hold the store the setting named, so their cost is counted and not
   charged, and ODictRange cannot even be written against a hashed one.  Sets
   and bags still do, because they are still a Set.Make tree and a list under
   every setting -- so for THEM the old caveat stands: under Hashed the descent
   [f] performs is the harness's bookkeeping, charged to neither counter, and
   the key's hash is charged instead.  Seconds do not follow the charge for a
   set or a bag, and converting those is the next step.

   The reason this wrapper existed at all -- "OCaml has no persistent hash map
   whose constants would not be the harness's own" -- no longer holds for a
   dictionary: CCHashTrie is a library, not our code.  What remains of the argument is only that a
   structure not yet converted cannot be measured.

   One asymmetry this closes, named because it MOVES A NUMBER.  The equality
   that confirms a hash bucket was charged by baseline.ml's probe and not by
   eval.ml's, so our hashed reads came out a comparison per probe cheaper than
   the originals' for no reason anyone had argued for.  It is charged here,
   once, for whoever calls.  Our columns go up by one comparison per hashed
   probe against what this harness printed before; the shift is against us. *)
let key_access (kind : Count.kind) (k : t) (f : unit -> 'a) : 'a =
  match kind with
  | Count.Ordered -> f ()
  | Count.Hashed ->
      Count.hash (key_work k);
      incr Count.comparisons;
      Count.quiet f

let eqb (a : t) (b : t) : bool = compare a b = 0
let ltb (a : t) (b : t) : bool = compare a b < 0

(* ---------- bags ----------

   A bag is just its elements, in whatever order they arrived.  list_to_bag
   and bag_to_list, which in Value.v move between a list and the canonical
   multiset, are therefore the identity here; the content of that claim is
   that nothing but [compare] and ESort looks at the order, which report.ml
   checks for ESort and [canonicalisations] counts for compare. *)

let bag_empty : t list = []
let bag_add (v : t) (b : t list) : t list = v :: b
let bag_of_list (l : t list) : t list = l

(* the canonical order, for the two operations that can see it *)
let bag_canonical (b : t list) : t list =
  incr Count.canonicalisations;
  List.sort compare b

(* Multiset difference, the value Interpret.v's bag_diff computes: one
   occurrence of each element of [rem] taken out of [b], and nothing below
   zero.  The list is UNORDERED, so this removes the first occurrence it
   meets rather than a canonical one -- which is the same multiset, and the
   only thing a bag's semantics asks of it.

   What it COSTS here is not what it costs a backend, and eval.ml's bag_pair
   is where that is said. *)
let bag_remove (v : t) (b : t list) : t list =
  let rec go seen = function
    | [] -> List.rev seen
    | x :: rest when compare x v = 0 -> List.rev_append seen rest
    | x :: rest -> go (x :: seen) rest in
  go [] b

let bag_diff (b : t list) (rem : t list) : t list =
  List.fold_left (fun acc v -> bag_remove v acc) b rem

(* ---------- sets ---------- *)

(* UNCHARGED, and used only by bridge.ml to carry the Gallina oracle's values
   across: nothing downstream of that bridge is measured.  The charged
   counterpart, which is what the evaluator's coercions go through, is
   Eval.set_build. *)
let set_of_list (l : t list) : VSet.t = List.fold_left (fun s v -> VSet.add v s) VSet.empty l

(* ---------- printing, for the differential test and for debugging ----------

   Collections print in canonical (ascending) order, so two values print the
   same string exactly when they are equal. *)

let rec to_string (v : t) : string =
  match v with
  | VInt z -> string_of_int z
  | VBool b -> if b then "true" else "false"
  | VString s -> "\"" ^ String.escaped s ^ "\""
  | VOption None -> "none"
  | VOption (Some v) -> "some(" ^ to_string v ^ ")"
  | VList l -> "[" ^ String.concat "; " (List.map to_string l) ^ "]"
  | VRecord l ->
      "{" ^ String.concat "; " (List.map (fun (s, v) -> s ^ " = " ^ to_string v) l) ^ "}"
  (* the rep is not printed: it is not part of the value, and two dictionaries
     that denote the same map have to print the same string for the
     differential test to compare them *)
  | VDict (_, d) ->
      "dict{"
      ^ String.concat "; "
          (List.map (fun (k, v) -> to_string k ^ " -> " ^ to_string v) (dbindings d))
      ^ "}"
  | VBag b ->
      (* printed canonically, so that two equal bags print the same string *)
      "bag{" ^ String.concat "; " (List.map to_string (List.sort compare b)) ^ "}"
  | VSet s -> "set{" ^ String.concat "; " (List.map to_string (VSet.elements s)) ^ "}"
  | VUnit -> "unit"
