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

let run () =
  failures := 0;
  check_hash_contract ();
  check_store Value.RRanged "tree";
  check_store Value.RUnranged ("store for " ^ Count.structures_name !Count.structures);
  Printf.printf "store check (%s): %s\n"
    (Count.structures_name !Count.structures)
    (if !failures = 0 then "ok" else Printf.sprintf "%d FAILURES" !failures);
  !failures = 0
