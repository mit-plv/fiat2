(* An evaluator for the extracted programs.

   WHAT THIS IS.  A transcription of Interpret.v's interp_expr and
   interp_command, operator by operator, onto the tree-backed values of
   value.ml.  It is written by hand and it is not verified; the Gallina
   interpreter is the specification it is written against, not a source it is
   derived from.  differential.ml checks the two against each other on small
   inputs, which is the only link between them.

   WHY NOT EXTRACT interp_expr INSTEAD.  Because the specification's
   dictionaries are association lists.  Extracting it would give an evaluator
   in which a lookup, an insert and a delete are all linear, which is exactly
   the cost the optimizer is claimed to remove -- the measurement would be
   over a backend no one would write.

   WHERE THE COST MODEL LIVES.  The three collection types are balanced trees
   (value.ml), so a lookup, an insert, a delete and a range restriction are
   logarithmic, and a scan is linear.  The semantics is unchanged by that
   choice -- the representations are in bijection -- but the asymptotics is
   entirely determined by it, so it is an assumption of the measurement and
   belongs in the paper beside the two extraction mappings.

   Every function below names the Interpret.v definition it transcribes. *)

open Extracted
open Value

(* interp_* are total in Gallina: an operator applied to a value of the wrong
   shape returns VUnit rather than failing.  That is reproduced here, because
   a well-typed program never reaches those branches and silently differing
   on them would be a difference in the semantics rather than in the cost. *)

module SMap = Map.Make (String)

type locals = value SMap.t

(* get_local *)
let get_local (l : locals) (x : string) : value =
  match SMap.find_opt x l with Some v -> v | None -> VUnit

(* ---------- integers ----------

   Z.div is floor division and Z.modulo takes the sign of the divisor, where
   OCaml's / and mod truncate toward zero; and Z.div _ 0 = 0 while
   Z.modulo a 0 = a.  Both differences are reachable, so both are reproduced. *)

let zdiv (a : int) (b : int) : int =
  if b = 0 then 0
  else
    let q = a / b and r = a mod b in
    if r <> 0 && (r < 0) <> (b < 0) then q - 1 else q

let zmod (a : int) (b : int) : int = if b = 0 then a else a - (b * zdiv a b)

(* ---------- strings ----------

   String.index in Rocq is the naive scan, and the extraction maps a Rocq
   string to an OCaml string, so the naive scan is what belongs here: making
   this one call cleverer would improve a subject the optimizer is not
   claiming to improve. *)

let str_contains (s : string) (p : string) : bool =
  let n = String.length s and m = String.length p in
  let rec at i = i + m <= n && (String.sub s i m = p || at (i + 1)) in
  at 0

(* String.substring n m s: skip n, take m, stop at the end *)
let substring (s : string) (i : int) (n : int) : string =
  let start = max 0 i and len = max 0 n in
  if start >= String.length s then ""
  else String.sub s start (min len (String.length s - start))

(* ---------- atoms ---------- *)

(* interp_atom *)
let interp_atom (a : atom) : value =
  match a with
  | AInt n -> VInt n
  | ABool b -> VBool b
  | AString s -> VString s
  | ANone _ -> VOption None
  | ANil _ -> VList []
  (* the dict_kind the term carries is retained as it stands; what it is worth
     is decided at the use site, by [keyed] below *)
  | AEmptyDict (Ranged, _) -> VDict (RRanged, VMap.empty)
  | AEmptyDict (Unranged, _) -> VDict (RUnranged, VMap.empty)
  | AEmptyBag _ -> VBag bag_empty
  | AEmptySet _ -> VSet VSet.empty
  | AUnit -> VUnit

(* ---------- what a key-addressed operation costs ----------

   Both helpers defer to Value.key_access, which baseline.ml also calls, so
   the optimizer's output and the originals are charged by the same function.
   Neither changes what is computed: the bindings and the elements are the
   same whatever they are charged as.

   A dictionary's kind decides which situation it is in.  Ranged is a tree
   under every setting, because ODictRange reads the key order.  Unranged is
   [licensed]: the type says no operator on it can read that order, so only
   the conservative floor declines the hash. *)

let keyed (r : dict_rep) (k : value) (f : unit -> 'a) : 'a =
  Value.key_access
    (match r with RRanged -> Count.ordered | RUnranged -> Count.licensed ())
    k f

(* A set is [unlicensed]: these terms never sort one, but TSet carries no kind
   and TyESort_Set would take any set to a sorted list, so nothing in the
   program licenses the hash the way dict_kind does.  Typed therefore charges
   the tree it is stored in and only Hashes hashes it -- which is what makes
   the Hashes column the measurement of what a set_kind would be worth. *)

let in_set (k : value) (f : unit -> 'a) : 'a =
  Value.key_access (Count.unlicensed ()) k f

(* A set-vs-set operation.  On a tree it is a merge of the two shapes, and
   Set.union/inter/diff charge the comparisons they actually perform.  On a
   hash table there is no merge to do: it is one probe per element of the side
   that gets iterated, so that is what is charged, and the tree work this
   harness still performs is suppressed.  [iterated] is that side -- the right
   operand of a difference, the smaller of the two otherwise. *)
let set_pair (iterated : VSet.t) (f : unit -> 'a) : 'a =
  match Count.unlicensed () with
  | Count.Ordered -> f ()
  | Count.Hashed ->
      VSet.iter (fun e -> Value.key_access Count.Hashed e (fun () -> ())) iterated;
      Count.quiet f

(* A bag difference.  THE CHARGE IS THE WHOLE POINT OF THE OPERATOR, and it
   is also where this harness cannot have everything it would like.

   A bag is stored here as an unordered LIST (value.ml says why: every other
   bag operation in these programs is an insert, a concatenation or a fold,
   none of which wants an order).  So unlike the dictionary -- stored in a
   tree, charged as a hash, with the descent quieted -- there is no tree here
   whose descent could stand in for the Ordered cost of a multiset.  What the
   list really does is a scan.

   So the two settings say different things, and only one of them is a model
   of a multiset:

     Ordered  the scan the list really performs, Theta(b).  That is the
              honest charge for a bag with no kind annotation, in exactly the
              way a set with no set_kind is charged the tree it is stored in.
     Hashed   one point removal per element of the iterated side, which is
              what a backend holding the bag as a hashed multiset would pay,
              with the list's own scan quieted.

   A bag_kind, the analogue of dict_kind, is what would let the typed column
   charge a removal as a removal.  Until then the operator makes the INTENT
   expressible -- a filter cannot say "this row leaves", because a backend
   reading one cannot tell a removal from an arbitrary predicate -- and the
   hashes column is where that intent turns into a cost. *)
let bag_pair (iterated : value list) (f : unit -> 'a) : 'a =
  match Count.unlicensed () with
  | Count.Ordered -> f ()
  | Count.Hashed ->
      List.iter (fun e -> Value.key_access Count.Hashed e (fun () -> ())) iterated;
      Count.quiet f

(* Building a set from a list of n elements: n inserts, charged one at a time
   through the same rule, so a coercion costs what n insertions cost under
   whichever structure the run is charging.  The caller charges the rows. *)
let set_build (l : value list) : VSet.t =
  List.fold_left (fun s v -> in_set v (fun () -> VSet.add v s)) VSet.empty l

(* ---------- unary ---------- *)

(* interp_unop *)
let interp_unop (o : unop) (v : value) : value =
  match o, v with
  | ONeg, VInt z -> VInt (-z)
  | ONot, VBool b -> VBool (not b)
  | OLength, VList l -> let n = List.length l in Count.walk n; VInt n
  | OLengthString, VString s -> VInt (String.length s)
  | OStringOfInt, VInt z -> VString (string_of_int z)
  | OSome, v -> VOption (Some v)
  (* list_to_bag (map snd d) *)
  (* no key, and a hash table enumerates its entries as a tree does, so this
     is charged the same under either rep *)
  | ODictValues, VDict (_, d) ->
      VBag (VMap.fold (fun _ v b -> Count.walk 1; v :: b) d [])
  (* VSet (map fst l).  In Interpret.v this is a projection, because a
     well-typed bag is a sorted dedup'd association list already; here a bag is
     an UNORDERED list (see value.ml), so the order the set needs has to be paid
     for -- one tree insert per entry, charged to cmps.  That is the same price
     the source's own OSetOfList pays on its survivors, so the coercion is not
     somewhere a pessimization could hide. *)
  | OSetOfBag, VBag b -> VSet (set_build b)
  (* A coercion READS every row: bag_of_list and set_build walk the list, and
     set_build inserts each element one at a time.  Counting these is what keeps
     the row counter honest about the source programs, whose whole cost on a
     membership test is the coercion -- eval/Jenkins_ItemDeletion's source does
     nothing else, and would otherwise be reported as touching no rows at all. *)
  | OBagOfList, VList l -> Count.visit (List.length l); VBag (bag_of_list l)
  | OSetOfList, VList l -> Count.visit (List.length l); VSet (set_build l)
  | _, _ -> VUnit

(* ---------- binary ---------- *)

let int_binop (f : int -> int -> int) (a : value) (b : value) : value =
  match a, b with VInt a, VInt b -> VInt (f a b) | _ -> VUnit

let bool_binop (f : bool -> bool -> bool) (a : value) (b : value) : value =
  match a, b with VBool a, VBool b -> VBool (f a b) | _ -> VUnit

(* interp_binop *)
let interp_binop (o : binop) (a : value) (b : value) : value =
  match o with
  | OPlus -> int_binop ( + ) a b
  | OMinus -> int_binop ( - ) a b
  | OTimes -> int_binop ( * ) a b
  | ODiv -> int_binop zdiv a b
  | OMod -> int_binop zmod a b
  | OAnd -> bool_binop ( && ) a b
  | OOr -> bool_binop ( || ) a b
  | OConcat ->
      (match a, b with
       | VList a, VList b -> Count.walk (List.length a); VList (a @ b)
       | _ -> VUnit)
  | OConcatString -> (match a, b with VString a, VString b -> VString (a ^ b) | _ -> VUnit)
  | OLess -> (match a, b with VInt a, VInt b -> VBool (a < b) | _ -> VUnit)
  | OEq -> VBool (eqb a b)
  | OCons -> (match b with VList l -> VList (a :: l) | _ -> VUnit)
  | ORange ->
      (match a, b with
       | VInt s, VInt e ->
           let n = max 0 (e - s) in
           Count.walk n;
           VList (List.init n (fun i -> VInt (s + i)))
       | _ -> VUnit)
  | OBagInsert -> (match a with VBag m -> VBag (bag_add b m) | _ -> VUnit)
  | OSetInsert ->
      (match a with VSet s -> VSet (in_set b (fun () -> VSet.add b s)) | _ -> VUnit)
  | OSetUnion ->
      (match a, b with
       | VSet x, VSet y ->
           (* the smaller side is the one iterated either way *)
           VSet (set_pair (if VSet.cardinal x < VSet.cardinal y then x else y)
                   (fun () -> VSet.union x y))
       | _ -> VUnit)
  | OSetIntersect ->
      (match a, b with
       | VSet x, VSet y ->
           VSet (set_pair (if VSet.cardinal x < VSet.cardinal y then x else y)
                   (fun () -> VSet.inter x y))
       | _ -> VUnit)
  | OSetDiff ->
      (match a, b with
       | VSet x, VSet y -> VSet (set_pair y (fun () -> VSet.diff x y))
       | _ -> VUnit)
  | OBagDiff ->
      (match a, b with
       | VBag x, VBag y -> VBag (bag_pair y (fun () -> Value.bag_diff x y))
       | _ -> VUnit)
  | OSetMem ->
      (match a with VSet s -> VBool (in_set b (fun () -> VSet.mem b s)) | _ -> VUnit)
  (* a contains b *)
  | OStrContains ->
      (match a, b with VString s, VString p -> VBool (str_contains s p) | _ -> VUnit)
  | OLookup ->
      (match a with
       | VDict (r, d) -> VOption (keyed r b (fun () -> VMap.find_opt b d))
       | _ -> VUnit)
  | ODelete ->
      (match a with
       | VDict (r, d) -> VDict (r, keyed r b (fun () -> VMap.remove b d))
       | _ -> VUnit)

(* ---------- ternary ----------

   The two range operators are the reason the dictionary is a tree.  A bound
   is an option -- absent means unconstrained -- and the range is half-open,
   [lo, hi).  Map.split cuts at a key in logarithmic time and returns both
   sides already balanced, so the restriction costs a path and not a
   traversal; dict_range in Interpret.v is a filter, and this is that filter
   transported to the tree. *)

(* the part of d with keys >= lo *)
let split_lo (lo : value) (d : value VMap.t) : value VMap.t =
  match lo with
  | VOption (Some l) ->
      let _, at, above = VMap.split l d in
      (match at with None -> above | Some v -> VMap.add l v above)
  | _ -> d

(* the part of d with keys < hi *)
let split_hi (hi : value) (d : value VMap.t) : value VMap.t =
  match hi with
  | VOption (Some h) ->
      let below, _, _ = VMap.split h d in
      below
  | _ -> d

(* dict_range lo hi d *)
let dict_range (lo : value) (hi : value) (d : value VMap.t) : value VMap.t =
  split_hi hi (split_lo lo d)

(* dict_range_delete lo hi d: everything the range leaves out, which is the
   keys below lo together with the keys at or above hi.  The two pieces are
   key-disjoint, so the union never has to choose. *)
let dict_range_delete (lo : value) (hi : value) (d : value VMap.t) : value VMap.t =
  let below = match lo with VOption (Some l) -> let b, _, _ = VMap.split l d in b | _ -> VMap.empty in
  let above =
    match hi with
    | VOption (Some h) ->
        let _, at, a = VMap.split h d in
        (match at with None -> a | Some v -> VMap.add h v a)
    | _ -> VMap.empty
  in
  VMap.union (fun _ v _ -> Some v) below above

(* interp_ternop *)
let interp_ternop (o : ternop) (a : value) (b : value) (c : value) : value =
  match o with
  | OInsert ->
      (match a with
       | VDict (r, d) -> VDict (r, keyed r b (fun () -> VMap.add b c d))
       | _ -> VUnit)
  | OSubstring ->
      (match a, b, c with
       | VString s, VInt i, VInt n -> VString (substring s i n)
       | _ -> VUnit)
  (* The two operators that READ the key order, and the only two whose typing
     pins the kind: TyODictRange is stated at Ranged.  So RUnranged here is not an
     ill-typed program to be absorbed into VUnit like the arms above -- it
     would mean the dict_kind the term carries disagrees with the operator
     applied to it, i.e. that a type-preservation proof is wrong or that the
     extracted term is not the one that was checked.  That is worth a crash
     rather than a number. *)
  | ODictRange ->
      (match a with
       | VDict (RRanged, d) -> VDict (RRanged, dict_range b c d)
       | VDict (RUnranged, _) -> failwith "ODictRange on an Unranged dictionary"
       | _ -> VUnit)
  | ODictRangeDelete ->
      (match a with
       | VDict (RRanged, d) -> VDict (RRanged, dict_range_delete b c d)
       | VDict (RUnranged, _) -> failwith "ODictRangeDelete on an Unranged dictionary"
       | _ -> VUnit)

(* ---------- aggregates ----------

   interp_aggr folds over bag_to_list, so an element of multiplicity n is
   folded n times; interp_aci_aggr folds over the set's elements from the
   right.  Both fold with an operator that returns VUnit off its expected
   shape, and a VUnit accumulator poisons every later step, so a single
   element of the wrong shape makes the whole fold VUnit.  That is reproduced
   rather than assumed away. *)

let interp_ac_fold (ag : aggr) (b : value list) : value =
  Count.walk (List.length b);
  match ag with
  | AGSum ->
      List.fold_left
        (fun acc v -> match acc, v with VInt a, VInt z -> VInt (a + z) | _ -> VUnit)
        (VInt 0) b
  | AGCount -> VInt (List.length b)

let interp_aci_fold (ag : aci_aggr) (s : VSet.t) : value =
  Count.walk (VSet.cardinal s);
  let pick = match ag with AGMin -> min | AGMax -> max in
  List.fold_right
    (fun v acc ->
       match acc with
       | VOption None -> VOption (Some v)
       | VOption (Some (VInt v')) ->
           (match v with VInt z -> VOption (Some (VInt (pick z v'))) | _ -> VUnit)
       | _ -> VUnit)
    (VSet.elements s) (VOption None)

(* ---------- records ---------- *)

(* record_sort: by field name *)
let record_sort (l : (string * value) list) : (string * value) list =
  List.stable_sort (fun (a, _) (b, _) -> String.compare a b) l

(* record_proj *)
let record_proj (s : string) (l : (string * value) list) : value =
  match List.assoc_opt s l with Some v -> v | None -> VUnit

(* ---------- expressions ---------- *)

(* interp_expr *)
let rec interp_expr (store : locals) (env : locals) (e : expr) : value =
  incr Count.steps;
  match e with
  | EVar x -> get_local env x
  | ELoc x -> get_local store x
  | EAtom a -> interp_atom a
  | EUnop (o, e) -> interp_unop o (interp_expr store env e)
  | EBinop (o, e1, e2) ->
      interp_binop o (interp_expr store env e1) (interp_expr store env e2)
  | ETernop (o, e1, e2, e3) ->
      interp_ternop o (interp_expr store env e1) (interp_expr store env e2)
        (interp_expr store env e3)
  | EIf (e1, e2, e3) ->
      (match interp_expr store env e1 with
       | VBool b -> if b then interp_expr store env e2 else interp_expr store env e3
       | _ -> VUnit)
  | ELet (e1, x, e2) ->
      interp_expr store (SMap.add x (interp_expr store env e1) env) e2
  | EFlatmap (tag, e1, x, e2) -> interp_flatmap store env tag e1 x e2
  | EFold (e1, e2, x, y, e3) ->
      (match interp_expr store env e1 with
       | VList l ->
           Count.visit (List.length l);
           let a = interp_expr store env e2 in
           List.fold_right
             (fun v acc -> interp_expr store (SMap.add y acc (SMap.add x v env)) e3)
             l a
       | _ -> VUnit)
  | EACFold (ag, e) ->
      (match interp_expr store env e with VBag b -> interp_ac_fold ag b | _ -> VUnit)
  | EACIFold (ag, e) ->
      (match interp_expr store env e with VSet s -> interp_aci_fold ag s | _ -> VUnit)
  | ERecord l ->
      VRecord (record_sort (List.map (fun (s, e) -> (s, interp_expr store env e)) l))
  | EAccess (r, s) ->
      (match interp_expr store env r with VRecord l -> record_proj s l | _ -> VUnit)
  | EOptMatch (e, e_none, x, e_some) ->
      (match interp_expr store env e with
       | VOption None -> interp_expr store env e_none
       | VOption (Some v) -> interp_expr store (SMap.add x v env) e_some
       | _ -> VUnit)
  | ESort (tag, e) ->
      (match tag, interp_expr store env e with
       | LikeList, VList l ->
           Count.visit (List.length l); VList (List.stable_sort Value.compare l)
       | LikeBag, VBag b -> Count.visit (List.length b); VList (bag_canonical b)
       | LikeSet, VSet s -> Count.visit (VSet.cardinal s); VList (VSet.elements s)
       | _, _ -> VUnit)

(* EFlatmap, one case per tag.

   The bag case walks the elements with their repetitions, which is what
   bag_to_list hands the specification's flat_map. *)
and interp_flatmap store env tag e1 x e2 =
  match tag, interp_expr store env e1 with
  | LikeList, VList l ->
      Count.visit (List.length l);
      VList
        (List.concat_map
           (fun v ->
              match interp_expr store (SMap.add x v env) e2 with VList l2 -> l2 | _ -> [])
           l)
  | LikeBag, VBag b ->
      (* rev_append rather than append: a bag has no order to preserve, and
         the left fold would otherwise be quadratic *)
      Count.visit (List.length b);
      VBag
        (List.fold_left
           (fun acc v ->
              match interp_expr store (SMap.add x v env) e2 with
              | VBag b2 -> List.rev_append b2 acc
              | _ -> acc)
           bag_empty b)
  | LikeSet, VSet s ->
      Count.visit (VSet.cardinal s);
      VSet
        (VSet.fold
           (fun v acc ->
              match interp_expr store (SMap.add x v env) e2 with
              (* the union the set flatmap performs is charged like any other *)
              | VSet s2 ->
                  set_pair
                    (if VSet.cardinal acc < VSet.cardinal s2 then acc else s2)
                    (fun () -> VSet.union acc s2)
              | _ -> acc)
           s VSet.empty)
  | _, _ -> VUnit

(* ---------- commands ---------- *)

(* interp_command.  CLetMut restores the outer binding of x on the way out,
   including the case where there was none. *)
let rec interp_command (store : locals) (env : locals) (c : command) : locals =
  match c with
  | CSkip -> store
  | CSeq (c1, c2) -> interp_command (interp_command store env c1) env c2
  | CLet (e, x, c) ->
      interp_command store (SMap.add x (interp_expr store env e) env) c
  | CLetMut (e, x, c) ->
      let store' = SMap.add x (interp_expr store env e) store in
      let store'' = interp_command store' env c in
      (match SMap.find_opt x store with
       | Some v -> SMap.add x v store''
       | None -> SMap.remove x store'')
  | CAssign (x, e) -> SMap.add x (interp_expr store env e) store
  | CIf (e, c1, c2) ->
      (match interp_expr store env e with
       | VBool b -> if b then interp_command store env c1 else interp_command store env c2
       | _ -> store)
  | CForeach (e, x, c) ->
      (match interp_expr store env e with
       | VList l ->
           List.fold_left (fun st v -> interp_command st (SMap.add x v env) c) store l
       | _ -> store)
