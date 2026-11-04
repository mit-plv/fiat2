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
