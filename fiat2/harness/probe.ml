(* The store, against a reference map.

   This exists because a library got it wrong.  The first persistent hash map
   tried here was `hamt` 1.0.0, whose remove -- and alter, update and extract,
   which share its code -- silently discards most of the table: wrong in 3032
   of 3660 two-key cases, under every configuration the library offers, and
   wrong for the same reason on a plain int key with the identity hash, so it
   is the library and not our use of it.  The harness's own differential test
   caught it only as ten mismatched subjects; what said WHICH operation was
   broken was a check of this shape.  So it stays, and `check` runs it first.

   It is not a cost check.  It asserts that a dictionary store behaves as a
   finite map on the kinds of key these subjects actually use, and that the
   two stores agree with each other and with Map. *)

let v s = Value.VString s
let rcd l = Value.VRecord l

(* scalars, a record key (Kafka's composite, Jenkins's whole row), an option
   key (AreaRegistry's floor), and keys that collide in a trie's first level *)
let keys =
  [ v "a"; v "b"; v ""; Value.VInt 3; Value.VInt 0; Value.VInt (-7);
    Value.VBool false; Value.VBool true; Value.VUnit;
    rcd [ ("k", v "x"); ("p", Value.VInt 1) ];
    rcd [ ("k", v "x"); ("p", Value.VInt 2) ];
    rcd [ ("k", v "y"); ("p", Value.VInt 1) ];
    Value.VOption (Some (v "o")); Value.VOption None;
    Value.VList [ v "p"; v "q" ]; Value.VList [] ]

let failures = ref 0

let fail fmt = Printf.ksprintf (fun s -> incr failures; print_string ("  STORE " ^ s)) fmt

(* equal keys must hash alike, or a trie loses bindings it holds *)
let check_hash_contract () =
  List.iter
    (fun a ->
       List.iter
         (fun b ->
            if Value.equal a b && Value.hash a <> Value.hash b then
              fail "hash disagrees with equal: %s vs %s\n"
                (Value.to_string a) (Value.to_string b))
         keys)
    keys

(* and the store must be a finite map: add, overwrite, look up, delete *)
let check_store (rep : Value.dict_rep) (what : string) =
  let d = List.fold_left (fun d k -> Value.dadd k (v "V") d) (Value.dempty rep) keys in
  if Value.dcardinal d <> List.length keys then
    fail "%s: cardinal %d, expected %d\n" what (Value.dcardinal d) (List.length keys);
  List.iter
    (fun k ->
       if Value.dfind k d = None then
         fail "%s: lost %s\n" what (Value.to_string k))
    keys;
  (* an overwrite replaces rather than duplicates *)
  let d = Value.dadd (List.hd keys) (v "W") d in
  if Value.dcardinal d <> List.length keys then
    fail "%s: overwrite changed cardinal to %d\n" what (Value.dcardinal d);
  (* and THE OPERATION THE LIBRARY GOT WRONG: one delete removes one binding *)
  List.iter
    (fun gone ->
       let d' = Value.dremove gone d in
       if Value.dcardinal d' <> List.length keys - 1 then
         fail "%s: removing %s left cardinal %d, expected %d\n" what
           (Value.to_string gone) (Value.dcardinal d') (List.length keys - 1);
       List.iter
         (fun k ->
            let want = not (Value.equal k gone) in
            if (Value.dfind k d' <> None) <> want then
              fail "%s: after removing %s, %s is %s\n" what (Value.to_string gone)
                (Value.to_string k) (if want then "absent" else "present"))
         keys)
    keys;
  (* the canonical order is the one the semantics compares, whatever the store *)
  let sorted = List.sort Value.compare keys in
  if List.map fst (Value.dbindings d) <> sorted then
    fail "%s: bindings are not in canonical order\n" what

(* and the set store must be a finite SET: insert twice is insert once, a
   delete removes one element, and union/intersection/difference agree with a
   reference set however the two sides are stored *)
let check_set_store () =
  let what = "set for " ^ Count.structures_name !Count.structures in
  let ref_of l = List.sort_uniq Value.compare l in
  let s = List.fold_left (fun s k -> Value.sadd k s) (Value.sempty ()) keys in
  (* a duplicate insert must not grow it *)
  let s = Value.sadd (List.hd keys) s in
  if Value.scardinal s <> List.length (ref_of keys) then
    fail "%s: cardinal %d, expected %d\n" what (Value.scardinal s)
      (List.length (ref_of keys));
  List.iter
    (fun k -> if not (Value.smem k s) then fail "%s: lost %s\n" what (Value.to_string k))
    keys;
  if Value.selements s <> ref_of keys then
    fail "%s: elements are not in canonical order\n" what;
  List.iter
    (fun gone ->
       let s' = Value.sremove gone s in
       if Value.scardinal s' <> List.length (ref_of keys) - 1 then
         fail "%s: removing %s left cardinal %d\n" what (Value.to_string gone)
           (Value.scardinal s');
       if Value.smem gone s' then
         fail "%s: %s survived its removal\n" what (Value.to_string gone))
    keys;
  (* the three set operations, against List as the reference *)
  let half l = List.filteri (fun i _ -> i mod 2 = 0) l in
  let a = half keys and b = half (List.tl keys) in
  let sa = List.fold_left (fun s k -> Value.sadd k s) (Value.sempty ()) a
  and sb = List.fold_left (fun s k -> Value.sadd k s) (Value.sempty ()) b in
  let cmp name got want =
    if Value.selements got <> ref_of want then
      fail "%s: %s disagrees with the reference\n" what name in
  cmp "union" (Value.sunion sa sb) (a @ b);
  cmp "intersect" (Value.sinter sa sb)
    (List.filter (fun k -> List.exists (Value.equal k) b) a);
  cmp "diff" (Value.sdiff sa sb)
    (List.filter (fun k -> not (List.exists (Value.equal k) b)) a);
  (* the singleton difference SetRemoveTransf emits *)
  let one = Value.sadd (List.hd a) (Value.sempty ()) in
  cmp "diff with a singleton" (Value.sdiff sa one) (List.tl a)

(* The bag store, all THREE of them, because the dial picks only one and the
   other two are what a bag that is removed from would hold -- so they have to
   be checked by something other than the subjects. *)
let check_bag_store (b0 : Value.bstore) (what : string) =
  (* multiplicity is the point: the same element twice is two occurrences *)
  let occ = keys @ [ List.hd keys; List.hd keys ] in
  let b = List.fold_left (fun b v -> Value.badd v b) b0 occ in
  if Value.bcardinal b <> List.length occ then
    fail "%s: cardinal %d, expected %d\n" what (Value.bcardinal b)
      (List.length occ);
  if Value.bcanon b <> List.sort Value.compare occ then
    fail "%s: canonical order disagrees with a sorted list of occurrences\n" what;
  (* one removal takes ONE occurrence, so the thrice-present key survives *)
  let b1 = Value.bremove (List.hd keys) b in
  if Value.bcardinal b1 <> List.length occ - 1 then
    fail "%s: a removal took %d occurrences\n" what
      (List.length occ - Value.bcardinal b1);
  if Value.bcanon b1 <> List.sort Value.compare (List.tl occ) then
    fail "%s: the wrong occurrence went\n" what;
  (* removing an absent element is a no-op, not an error *)
  let absent = Value.VString "!absent!" in
  if Value.bcardinal (Value.bremove absent b) <> List.length occ then
    fail "%s: removing an absent element changed the bag\n" what;
  (* and the difference OBagDiff computes, truncated at zero *)
  let one = Value.badd (List.hd keys) (Value.bempty ()) in
  if Value.bcardinal (Value.bdiff b one) <> List.length occ - 1 then
    fail "%s: a singleton difference took the wrong number\n" what;
  if Value.bcardinal (Value.bdiff b b) <> 0 then
    fail "%s: a self-difference did not empty it\n" what;
  if Value.bcardinal (Value.bdiff one b) <> 0 then
    fail "%s: a difference went below zero\n" what

let run () =
  failures := 0;
  check_hash_contract ();
  check_store Value.RRanged "tree";
  check_store Value.RUnranged ("store for " ^ Count.structures_name !Count.structures);
  check_set_store ();
  check_bag_store (Value.bempty ()) ("bag for " ^ Count.structures_name !Count.structures);
  check_bag_store (Value.BList []) "bag as a list";
  check_bag_store (Value.BTree Value.VMap.empty) "bag as a tree multiset";
  check_bag_store (Value.BHash Value.VTrie.empty) "bag as a trie multiset";
  Printf.printf "store check (%s): %s\n"
    (Count.structures_name !Count.structures)
    (if !failures = 0 then "ok" else Printf.sprintf "%d FAILURES" !failures);
  !failures = 0
