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
    | VDict of t VMap.t
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
    | VDict of t VMap.t
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
    | VDict a, VDict b -> VMap.compare compare a b
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
  | VDict d ->
      "dict{"
      ^ String.concat "; "
          (List.map (fun (k, v) -> to_string k ^ " -> " ^ to_string v) (VMap.bindings d))
      ^ "}"
  | VBag b ->
      (* printed canonically, so that two equal bags print the same string *)
      "bag{" ^ String.concat "; " (List.map to_string (List.sort compare b)) ^ "}"
  | VSet s -> "set{" ^ String.concat "; " (List.map to_string (VSet.elements s)) ^ "}"
  | VUnit -> "unit"
