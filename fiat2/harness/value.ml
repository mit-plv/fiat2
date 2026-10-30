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

     dict   a balanced tree ordered by the same comparison, or a persistent
            hash trie where the setting licenses one.  The tree is canonical
            in the same sense as the sorted list, so the bijection is the
            identity on bindings; either way a lookup, an insert, a delete
            and a range restriction cost a path rather than a copy.

            Of those four operations only the RANGE RESTRICTION needs the
            order, and Language.v:79 says which dictionaries can be asked for
            one: AEmptyDict carries a dict_kind, outside the option, so it
            survives extraction on every dictionary a program creates.  Across
            the subject terms 19 are Unranged and 2 are Ranged.

            So the dictionary carries its [dict_rep] below, and THE
            REPRESENTATION IS THE CHARGE.  A Ranged one is a balanced tree
            under every setting, because a range query is not answerable
            from anything else; an Unranged one is whichever store
            Count.licensed names, VMap or CCHashTrie's persistent HAMT, and
            [dempty] is the one place that choice is made.  Nothing models
            the cost of a structure the harness does not run: [compare]
            counts the descent a tree really performs and [hash] counts the
            hash a trie really takes, so the counters see the store's own
            work and cannot disagree with it.

            This replaced a wrapper that charged a hash-table price while
            storing the tree -- it existed because OCaml's standard library
            has no persistent hash map, and it stopped being needed when
            CCHashTrie turned out to be a library rather than our code.  Its
            obituary is at the foot of this file.

     set    a balanced tree, or a hash trie under `hashes`.  A set has to
            reject duplicates on insert and OSetMem is a probe, so it needs
            one structure or the other; what it does not need is the ORDER,
            and no set_kind exists for a program to say so.  That is why the
            choice is Count.unlicensed's and why only `hashes` takes it --
            the Hashes column is what adding a set_kind would be worth.

     bag    an UNORDERED list, with multiplicity as repetition.  A bag
            rejects nothing and probes nothing: every operation on one in
            these programs is an insert, a concatenation or a fold.  Keeping
            it sorted would charge a logarithmic factor, and a record-valued
            comparison, for work no backend would do.  The keyed stores exist
            below and are probed, but [bempty] deliberately does not pick one,
            because nothing in a program says which bags a backend would keep
            keyed -- see the note there.  Canonicalising is
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
    | VBag of bstore
    | VSet of sstore
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

  (* and the same two for a set, which is a map to unit.  A set has no kind
     annotation to consult -- TSet carries none -- so [Count.unlicensed] is
     what picks between them, exactly as it already decided the CHARGE. *)
  and sstore =
    | STree of VSet.t
    | SHash of unit VTrie.t

  (* A bag has THREE candidate implementations, not two, and that is not an
     accident of this harness -- it is the shape of the question.  A bag's
     operations in these programs are an insert, a concatenation and a fold,
     none of which wants an order, so a LIST is the cheapest faithful
     representation and the one a backend would pick for a bag it only builds
     and folds.  A bag something is REMOVED from wants an index, and then a
     multiset over a tree or a trie is right.  Which of those a given bag
     deserves is a per-bag question, and the dial answers it per RUN.

     [bempty] picks BTree for Ordered and BHash for Hashed, mirroring the set
     above, so that a removal costs a removal in every column.  BList is what
     the Ordered column would hold if the cheap-build reading won instead; the
     choice is one line in [bempty] and the probe exercises all three, so the
     measurement can decide rather than the comment. *)
  and bstore =
    | BList of t list        (* multiplicity by repetition, no order *)
    | BTree of int VMap.t    (* element -> multiplicity, balanced tree *)
    | BHash of int VTrie.t   (* element -> multiplicity, hash trie *)

  val compare : t -> t -> int
  (* for CCHashTrie's functor, which wants an equal and a hash *)
  val equal : t -> t -> bool
  val hash : t -> int
  (* the one fold that may look inside a store, so that callers outside this
     module never case-split on the representation *)
  val dfold : (t -> t -> 'a -> 'a) -> dstore -> 'a -> 'a
  val sfold : (t -> 'a -> 'a) -> sstore -> 'a -> 'a
  val bfold : (t -> 'a -> 'a) -> bstore -> 'a -> 'a
  val bcanon : bstore -> t list
end = struct
  type t =
    | VInt of int
    | VBool of bool
    | VString of string
    | VOption of t option
    | VList of t list
    | VRecord of (string * t) list
    | VDict of dict_rep * dstore
    | VBag of bstore
    | VSet of sstore
    | VUnit

  and dstore =
    | DTree of t VMap.t
    | DHash of t VTrie.t

  (* and the same two for a set, which is a map to unit.  A set has no kind
     annotation to consult -- TSet carries none -- so [Count.unlicensed] is
     what picks between them, exactly as it already decided the CHARGE. *)
  and sstore =
    | STree of VSet.t
    | SHash of unit VTrie.t

  (* A bag has THREE candidate implementations, not two, and that is not an
     accident of this harness -- it is the shape of the question.  A bag's
     operations in these programs are an insert, a concatenation and a fold,
     none of which wants an order, so a LIST is the cheapest faithful
     representation and the one a backend would pick for a bag it only builds
     and folds.  A bag something is REMOVED from wants an index, and then a
     multiset over a tree or a trie is right.  Which of those a given bag
     deserves is a per-bag question, and the dial answers it per RUN.

     [bempty] picks BTree for Ordered and BHash for Hashed, mirroring the set
     above, so that a removal costs a removal in every column.  BList is what
     the Ordered column would hold if the cheap-build reading won instead; the
     choice is one line in [bempty] and the probe exercises all three, so the
     measurement can decide rather than the comment. *)
  and bstore =
    | BList of t list        (* multiplicity by repetition, no order *)
    | BTree of int VMap.t    (* element -> multiplicity, balanced tree *)
    | BHash of int VTrie.t   (* element -> multiplicity, hash trie *)

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

  (* THE CHARACTERS A STRING COMPARISON REALLY EXAMINES.

     [compare] charges one unit per value node it walks, which priced a
     string -- however long -- at one.  That was an UNDER-count, and
     count.ml used to carry it as a caveat in prose: honest only because the
     generators keep keys short, with the one subject whose keys are long
     strings reported under that caveat.  A tree descent on a string key
     really compares the prefix the two keys share, once per level, and a
     scan over string keys really does the same.

     So the characters are charged here, by the same rule str_contains uses
     for its scan: the common prefix, PLUS the one position where the two
     differ, because that is where a byte comparison stops.  Equal strings
     cost their whole length; two strings differing in the first character
     cost one.  [hash] below charges the full length, because a hash cannot
     stop early -- that asymmetry is the two operations' real difference,
     not a convention.

     The sign is what every caller reads (Map, Set, the sorts and the
     leb/ltb derived from it), and this returns the same sign as
     String.compare at every input: equal prefixes fall through to the
     lengths, a difference returns the differing bytes compared as unsigned
     numbers, which is what Rocq's String.compare does on Ascii codes and
     what OCaml's does on bytes.  The differential test against the Gallina
     oracle is what checks it. *)
  let string_compare (a : string) (b : string) : int =
    let la = String.length a and lb = String.length b in
    let n = if la < lb then la else lb in
    let rec go i =
      if i = n then (Count.chars n; Int.compare la lb)
      else if Char.equal a.[i] b.[i] then go (i + 1)
      else (Count.chars (i + 1); Char.compare a.[i] b.[i])
    in
    go 0

  (* cardinality, needed by [compare] below and so needed INSIDE the knot;
     dcardinal and scardinal outside are these under their public names *)
  let dsize = function DTree m -> VMap.cardinal m | DHash h -> VTrie.cardinal h
  let ssize = function STree x -> VSet.cardinal x | SHash h -> VTrie.cardinal h
  (* occurrences, WITH multiplicity *)
  let bsize = function
    | BList l -> List.length l
    | BTree m -> VMap.fold (fun _ n acc -> acc + n) m 0
    | BHash h -> VTrie.fold ~f:(fun acc _ n -> acc + n) ~x:0 h

  let rec compare (a : t) (b : t) : int =
    incr Count.comparisons;
    match a, b with
    | VInt a, VInt b -> Int.compare a b
    | VBool a, VBool b -> Bool.compare a b
    | VString a, VString b -> string_compare a b
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
    | VDict (_, a), VDict (_, b) when dsize a = 0 || dsize b = 0 ->
        Int.compare (min 1 (dsize a)) (min 1 (dsize b))
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
    (* An emptiness test asks nothing about order, so it does not pay for one,
       for the reason given at the head of this file. *)
    | VBag a, VBag b when bsize a = 0 || bsize b = 0 ->
        Int.compare (min 1 (bsize a)) (min 1 (bsize b))
    (* and otherwise the canonical order is what the semantics compares, which
       a BList has to produce and the two multisets already hold *)
    | VBag a, VBag b -> list_compare compare (bcanon a) (bcanon b)
    (* Emptiness tests, for the reason given at the head of this file: the
       answer is settled by the cardinalities, and producing a canonical order
       to discover it would be the bag's old mistake in a new place.  MEASURED
       -- without these, user_search/remove costs 702235 under hashes against
       1680, because the trigram delete asks "did this bucket empty?" once per
       trigram and each ask sorted the bucket. *)
    | VSet a, VSet b when ssize a = 0 || ssize b = 0 ->
        Int.compare (min 1 (ssize a)) (min 1 (ssize b))
    | VSet (STree a), VSet (STree b) -> VSet.compare a b
    | VSet a, VSet b ->
        (* as for a dictionary: a hashed store has no order of its own *)
        let canon = function
          | STree x -> VSet.elements x
          | SHash h ->
              incr Count.canonicalisations;
              List.sort compare (List.map fst (VTrie.to_list h)) in
        list_compare compare (canon a) (canon b)
    | VUnit, VUnit -> 0
    | _ -> Int.compare (rank a) (rank b)
  (* THE CANONICAL ORDER, which only OEq above and ESort ask for.  The two
     multisets hold it already, so expanding their multiplicities costs no
     comparison; a BList does not, and sorting it is charged where every other
     canonicalisation is. *)
  and bcanon : bstore -> t list = function
    | BList l ->
        incr Count.canonicalisations;
        List.sort compare l
    | BTree m ->
        List.concat_map (fun (v, n) -> List.init n (fun _ -> v)) (VMap.bindings m)
    | BHash h ->
        incr Count.canonicalisations;
        List.concat_map (fun (v, n) -> List.init n (fun _ -> v))
          (List.sort (fun (a, _) (b, _) -> compare a b) (VTrie.to_list h))

  let equal (a : t) (b : t) : bool = compare a b = 0

  (* The hash a hashed store actually uses, and therefore the hash the
     counters actually count: one unit per value node, charged HERE, as
     [compare] charges one per node it walks -- plus, for a string, its
     bytes, to [strings], because a hash reads every one of them where a
     comparison stops at the first difference.  That asymmetry is the two
     operations' real difference and is why the charge is not symmetric.
     So the work a KEY costs is `comparisons + hashing + strings`, measured
     rather than modelled, and comparable across a tree and a trie because
     both now pay for the bytes they touch.

     It must agree with [equal], which cannot see the order of a bag, a set
     or a dictionary -- so those combine their elements COMMUTATIVELY, with
     the cardinality mixed in.  Sorting to hash would defeat the point. *)
  let rec hash (v : t) : int =
    incr Count.hashing;
    match v with
    | VInt n -> Hashtbl.hash n
    | VBool b -> Hashtbl.hash b
    (* every byte, because a hash cannot stop early where a comparison can *)
    | VString s -> Count.chars (String.length s); Hashtbl.hash s
    | VUnit -> 17
    | VOption None -> 19
    | VOption (Some v) -> 23 + (31 * hash v)
    | VList l -> List.fold_left (fun acc v -> (acc * 31) + hash v) 29 l
    | VRecord l ->
        List.fold_left
          (fun acc (f, v) -> (acc * 31) + Hashtbl.hash f + hash v) 37 l
    | VDict (_, d) ->
        dfold (fun k v acc -> acc + (hash k * 31) + hash v) d 41
    | VBag b -> bfold (fun v acc -> acc + hash v) b (43 + bsize b)
    | VSet s -> sfold (fun v acc -> acc + hash v) s 47

  (* the store's operations, in the one place that may look inside it *)
  and dfold : 'a. (t -> t -> 'a -> 'a) -> dstore -> 'a -> 'a =
    fun f d init ->
    match d with
    | DTree m -> VMap.fold f m init
    | DHash h -> VTrie.fold ~f:(fun acc k v -> f k v acc) ~x:init h

  (* UNORDERED on purpose.  Every caller of this either accumulates
     commutatively or is building something with no order of its own; the one
     operation that needs the canonical order is [selements], which says so
     and pays for it. *)
  and sfold : 'a. (t -> 'a -> 'a) -> sstore -> 'a -> 'a =
    fun f s init ->
    match s with
    | STree x -> VSet.fold f x init
    | SHash h -> VTrie.fold ~f:(fun acc k () -> f k acc) ~x:init h

  (* every OCCURRENCE, in whatever order the store holds them *)
  and bfold : 'a. (t -> 'a -> 'a) -> bstore -> 'a -> 'a =
    fun f b init ->
    let rep v n acc =
      let rec go n acc = if n <= 0 then acc else go (n - 1) (f v acc) in
      go n acc in
    match b with
    | BList l -> List.fold_left (fun acc v -> f v acc) init l
    | BTree m -> VMap.fold (fun v n acc -> rep v n acc) m init
    | BHash h -> VTrie.fold ~f:(fun acc v n -> rep v n acc) ~x:init h
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

(* ---------- the set store ----------

   A set is a map to unit, so it gets the same two stores.  Which one is
   [Count.unlicensed]'s call: TSet carries no kind, and TyESort_Set would take
   any set to a sorted list, so nothing in a program licenses the hash the way
   dict_kind does -- which is exactly why Hashes is the measurement of what a
   set_kind would be worth, and why it is now a measurement rather than a
   charge.

   CCHashTrie offers no union, intersection or difference, so those fold one
   side into the other.  That is not a compromise: it is the cost model the old
   [set_pair] already described -- one probe per element of the side that gets
   iterated -- with the probes now real. *)

let sempty () : sstore =
  match Count.unlicensed () with
  | Count.Ordered -> STree VSet.empty
  | Count.Hashed -> SHash VTrie.empty

let sadd (v : t) (s : sstore) : sstore =
  match s with
  | STree x -> STree (VSet.add v x)
  | SHash h -> SHash (VTrie.add v () h)

let sremove (v : t) (s : sstore) : sstore =
  match s with
  | STree x -> STree (VSet.remove v x)
  | SHash h -> SHash (VTrie.remove v h)

let smem (v : t) (s : sstore) : bool =
  match s with STree x -> VSet.mem v x | SHash h -> VTrie.mem v h

let scardinal (s : sstore) : int =
  match s with STree x -> VSet.cardinal x | SHash h -> VTrie.cardinal h

(* THE CANONICAL ORDER, which only ESort asks for.  A tree is already in it; a
   trie is not, and producing it is charged where every other canonicalisation
   is.  report.ml checks that no subject contains an ESort at all, so this
   should not fire -- and if it ever does, the counter says so. *)
let selements (s : sstore) : t list =
  match s with
  | STree x -> VSet.elements x
  | SHash h ->
      incr Count.canonicalisations;
      List.sort compare (List.map fst (VTrie.to_list h))

(* the elements in whatever order the store holds them, for the callers that
   accumulate commutatively *)
let selements_unordered (s : sstore) : t list =
  sfold (fun v acc -> v :: acc) s []

(* Union, intersection and difference, each iterating ONE side and probing the
   other.  Which side is iterated is the whole cost: for a union or an
   intersection it is the smaller, and for a difference it is the right
   operand, which is what makes the singleton idiom OSetDiff s {x} one probe
   rather than a traversal -- the shape SetRemoveTransf emits. *)
let sunion (a : sstore) (b : sstore) : sstore =
  match a, b with
  (* a balanced merge, which is what a backend holding two trees would do and
     what this harness has always charged for *)
  | STree x, STree y -> STree (VSet.union x y)
  | _ ->
      let small, big = if scardinal a <= scardinal b then (a, b) else (b, a) in
      sfold sadd small big

let sinter (a : sstore) (b : sstore) : sstore =
  match a, b with
  | STree x, STree y -> STree (VSet.inter x y)
  | _ ->
      let small, big = if scardinal a <= scardinal b then (a, b) else (b, a) in
      sfold (fun v acc -> if smem v big then sadd v acc else acc) small (sempty ())

let sdiff (a : sstore) (b : sstore) : sstore =
  match a, b with
  | STree x, STree y -> STree (VSet.diff x y)
  (* iterating the RIGHT operand is what makes the singleton idiom
     OSetDiff s {x} -- the shape SetRemoveTransf emits -- one probe *)
  | _ -> sfold sremove b a

(* [key_access] AND [key_work] USED TO LIVE HERE, and their absence is the
   point of the three commits that moved the stores.  It priced a point access -- a hash of the key plus one
   comparison for the bucket equality, with the structure's real descent
   credited to neither counter -- and eval.ml called it for the optimizer's
   output while baseline.ml called it for the originals, so that the two
   columns were charged by one function rather than by two helpers that agreed
   on inspection.

   [key_work] was the other half of it: the cost of a key, computed per value
   node, so that the pricing function had a number to multiply.  Both are
   gone, and nothing calls either, because every collection now HOLDS the
   structure its setting names and there is nothing left to price:
   [compare] counts a tree's descent, [hash] a trie's hash and [equal] its
   leaf comparison, on both sides, because both sides run the same store.  The reason the wrapper existed -- "OCaml has no persistent
   hash map whose constants would not be the harness's own" -- stopped being
   true when CCHashTrie turned out to be a library rather than our code.

   Count.quiet went with them, and its absence is worth as much as theirs: it
   ran a point access without charging the comparisons of the tree the hash
   price was pretending not to use.  With the store real there is no descent
   to suppress, so no counter in this harness is ever muted and no primitive
   does work silently.

   What the model got wrong, now that there is something to compare it with:
   it charged a flat +1 for the bucket equality, where a real trie calls
   [equal], which WALKS the key.  So a hit on a structured key cost more than
   the model said -- item_deletion keys on a whole row, and the author's
   containsHit went 80 to 120, exactly its extra nodes -- and a miss cost
   less, because a trie that reaches no leaf compares nothing. *)

let eqb (a : t) (b : t) : bool = compare a b = 0
let ltb (a : t) (b : t) : bool = compare a b < 0

(* ---------- the bag store ----------

   [bempty] is where the per-run choice is made, and the one line to change if
   the cheap-build reading of an Ordered bag should win instead (see bstore).

   Every operation is the one the store really performs, so the counters see
   it: a BList conses and scans, a BTree walks a path, a BHash hashes and
   descends a trie.  Nothing here is modelled. *)

(* A BAG IS A LIST UNDER EVERY SETTING, AND THE MEASUREMENT DECIDED THAT.

   The dial was tried both other ways and is badly wrong both times, because
   these programs BUILD bags constantly -- every flatmap and every coercion
   makes one -- and only one subject's rules ever remove from one.

     Ordered as a balanced tree: OBagOfList becomes n log n whole-row
     comparisons, and coercing the table to a bag is the whole of what a
     source-form membership test does.  user_search/suggestMiss went 60 ->
     612820, suggestShort 10074 -> 637464, window_store/fetchAll 508 -> 2599.

     Hashed as a trie: every bag construction hashes every element for a
     benefit no fold collects.  EVERY ratio in the hashes column got worse --
     suggestShort 1.02 -> 38.02, area_registry/remove 3.88 -> 22.57,
     cluster/available 7.03 -> 44.22 -- which would have wrecked the one thing
     that column is for, measuring what a set_kind is worth.

   So the structure choice for a bag CANNOT be made by a run-level dial, and
   that is a finding rather than a limitation of this harness.  A dictionary's
   choice is uniform because every dictionary here is probed; a set's is
   uniform because every set here is tested for membership.  A bag's is not:
   the right structure depends on whether THAT bag is ever removed from, which
   is a per-bag question, and the only thing that can answer a per-bag question
   is a per-bag annotation.  Both uniform answers are wrong by one to four
   orders of magnitude, which is a stronger argument than the one I first gave
   for an annotation, and it is the measured one.

   The three stores stay.  BTree and BHash are what a bag that is removed from
   should hold, they are what OBagDiff is fast on, and the probe exercises all
   three -- so when something can say which bags those are, the structures are
   already here and already checked. *)
let bempty () : bstore =
  (* ignore the setting, deliberately: see above *)
  BList []

let badd (v : t) (b : bstore) : bstore =
  match b with
  | BList l -> BList (v :: l)
  | BTree m ->
      BTree (VMap.update v (function None -> Some 1 | Some n -> Some (n + 1)) m)
  | BHash h ->
      BHash (VTrie.update v ~f:(function None -> Some 1 | Some n -> Some (n + 1)) h)

(* one occurrence out, and the entry with it if that was the last -- which is
   what keeps the empty bag the only representation of the empty multiset, and
   what [bsize]'s emptiness test in [compare] relies on *)
let bremove (v : t) (b : bstore) : bstore =
  match b with
  | BList l ->
      let rec go seen = function
        | [] -> List.rev seen
        | x :: rest when compare x v = 0 -> List.rev_append seen rest
        | x :: rest -> go (x :: seen) rest in
      BList (go [] l)
  | BTree m ->
      BTree (VMap.update v
               (function None -> None | Some 1 -> None | Some n -> Some (n - 1)) m)
  | BHash h ->
      BHash (VTrie.update v
               ~f:(function None -> None | Some 1 -> None | Some n -> Some (n - 1)) h)

let bcardinal (b : bstore) : int =
  match b with
  | BList l -> List.length l
  | BTree m -> VMap.fold (fun _ n acc -> acc + n) m 0
  | BHash h -> VTrie.fold ~f:(fun acc _ n -> acc + n) ~x:0 h

(* A LIST ALREADY IS A BAG, so under Ordered this costs nothing -- which is
   the point of holding it that way.  A multiset has to be built, and that is
   what a backend choosing one would pay. *)
let bof_list (l : t list) : bstore = BList l

(* Every occurrence, in whatever order the store holds them, for the callers
   that accumulate commutatively or build something with no order of its own.

   A BList hands back its own list rather than [bfold]'s reversal of it, and
   that is not cosmetic: a later sort or a sequence of tree inserts costs a
   different number of comparisons on a different permutation, so reversing
   here moved user_search/suggestShort by 142 under typed for no reason anyone
   could defend.  The multiset's order is its own and there is nothing to
   preserve. *)
let belements_unordered (b : bstore) : t list =
  match b with
  | BList l -> l
  | _ -> bfold (fun v acc -> v :: acc) b []

(* Multiset difference, truncated at zero: one removal per occurrence on the
   right, mirroring Interpret.v's bag_diff.  The iterated side is the right
   operand, which is what makes OBagDiff b {row} -- the shape the keyed delete
   wants -- one removal rather than a traversal. *)
let bdiff (a : bstore) (b : bstore) : bstore =
  bfold bremove b a

(* ---------- sets ---------- *)

(* UNCHARGED, and used only by bridge.ml to carry the Gallina oracle's values
   across: nothing downstream of that bridge is measured.  The charged
   counterpart, which is what the evaluator's coercions go through, is
   Eval.set_build. *)
let set_of_list (l : t list) : sstore = List.fold_left (fun s v -> sadd v s) (sempty ()) l

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
      "bag{" ^ String.concat "; " (List.map to_string (bcanon b)) ^ "}"
  | VSet s -> "set{" ^ String.concat "; " (List.map to_string (selements s)) ^ "}"
  | VUnit -> "unit"
