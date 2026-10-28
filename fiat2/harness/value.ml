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
    | VDict of dict_rep * t VMap.t
    | VBag of t list                 (* UNORDERED; multiplicity is repetition *)
    | VSet of VSet.t
    | VUnit

  val compare : t -> t -> int
end = struct
  type t =
    | VInt of int
    | VBool of bool
    | VString of string
    | VOption of t option
    | VList of t list
    | VRecord of (string * t) list
    | VDict of dict_rep * t VMap.t
    | VBag of t list
    | VSet of VSet.t
    | VUnit

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
    | VDict (ra, a), VDict (rb, b) ->
        let hashed r = r = RUnranged && Count.licensed () = Count.Hashed in
        if hashed ra || hashed rb then incr Count.canonicalisations;
        VMap.compare compare a b
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
end
and VMap : (Map.S with type key = V.t) = Map.Make (V)
and VSet : (Set.S with type elt = V.t) = Set.Make (V)

include V

(* [Value.value] reads better at the use sites than [Value.t] *)
type value = t

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
  | VDict (_, d) -> VMap.fold (fun k v n -> n + key_work k + key_work v) d 1
  | VBag b -> List.fold_left (fun n v -> n + key_work v) 1 b
  | VSet s -> VSet.fold (fun v n -> n + key_work v) s 1

(* What a point access at key [k] costs on a structure of the given kind,
   performing the access with [f].  THE ONE RULE, called by eval.ml for the
   optimizer's output and by baseline.ml for the original authors' code, so
   the two columns are charged by the same function rather than by two helpers
   that agree on inspection.  That is the only reason a ratio between them
   means anything.

   [f] reaches into a balanced tree under BOTH kinds, on both sides, for the
   reason given at the top of this file: the storage and the charge are
   separate questions, and OCaml has no persistent hash map whose constants
   would not be the harness's own.  So under Hashed the descent [f] performs is
   the harness's bookkeeping and is charged to neither counter; the key's hash
   is charged instead.  WALL-CLOCK SECONDS THEREFORE DO NOT FOLLOW THIS
   CHARGE -- they time a tree in every column, and are a check on shape only.

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
          (List.map (fun (k, v) -> to_string k ^ " -> " ^ to_string v) (VMap.bindings d))
      ^ "}"
  | VBag b ->
      (* printed canonically, so that two equal bags print the same string *)
      "bag{" ^ String.concat "; " (List.map to_string (List.sort compare b)) ^ "}"
  | VSet s -> "set{" ^ String.concat "; " (List.map to_string (VSet.elements s)) ^ "}"
  | VUnit -> "unit"
