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

(* The local environment is a map from names to values, and a lookup in one
   is a descent comparing strings.  The comparator charges them, so what an
   EVar costs is counted rather than assumed to be nothing.

   It is charged to [Count.over] and not to [Count.field], because this map
   is the INTERPRETER'S and not the program's: a compiled backend reads a
   local from a slot.  So it joins [steps] in the total and stays out of the
   figure that crosses to hand-written code.  It is not small -- on most
   subjects it is the same order as [steps] -- which is the reason it gets a
   counter instead of a remark. *)
module SMap = Map.Make (struct
  type t = string
  let compare (a : string) (b : string) : int = Count.over 1; String.compare a b
end)

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
  (* written out character by character, where this used to build a substring
     and compare it, so that what is charged is what the scan really does:
     the comparisons it performs before it stops, not an upper bound on them *)
  let rec at i =
    i + m <= n
    && (let rec eq j = j = m || ((Count.chars 1; s.[i + j] = p.[j]) && eq (j + 1)) in
        eq 0 || at (i + 1))
  in
  at 0

(* String.substring n m s: skip n, take m, stop at the end *)
let substring (s : string) (i : int) (n : int) : string =
  let start = max 0 i and len = max 0 n in
  if start >= String.length s then ""
  else
    let taken = min len (String.length s - start) in
    Count.chars taken;
    String.sub s start taken

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
  | AEmptyDict (Ranged, _) -> VDict (RRanged, Value.dempty RRanged)
  | AEmptyDict (Unranged, _) -> VDict (RUnranged, Value.dempty RUnranged)
  | AEmptyBag _ -> VBag (Value.bempty ())
  | AEmptySet _ -> VSet (Value.sempty ())
  | AUnit -> VUnit

(* ---------- what a key-addressed operation costs ----------

   NOTHING HERE PRICES ONE ANY MORE.  Every collection with a point access
   holds the store its setting named -- Value.dempty, Value.sempty,
   Value.bempty -- and the operations run on that store, so the cost is what
   the structure really does: Value.compare counts a tree's descent, and
   Value.hash and Value.equal count a trie's hash and its leaf comparison.
   The wrappers that used to model those costs are gone, and so is
   Value.key_access and Value.key_work, which baseline.ml called for the
   same purpose.

   That matters for the one claim the author comparison rests on.  The two
   columns used to be charged identically because they called the same pricing
   function; now they are charged identically because they RUN THE SAME DATA
   STRUCTURE.  The second is stronger, and unlike the first it cannot drift.

   Which store a collection gets, and on whose authority:

     a dictionary   its kind decides.  Ranged is a tree under every setting,
                    because ODictRange reads the key order -- and CCHashTrie
                    has no split, so a range restriction cannot even be
                    WRITTEN against a hashed store.  Unranged is [licensed]:
                    the type says no operator on it can read that order, so
                    only the Trees floor declines the hash.
     a set          [unlicensed].  TSet carries no kind and TyESort_Set would
                    take any set to a sorted list, so nothing in a program
                    licenses the hash the way dict_kind does.  That is what
                    makes the Hashes column a MEASUREMENT of what a set_kind
                    would be worth rather than a charge standing in for one.
     a bag          [unlicensed] too, and with a third option: a bag whose
                    operations are an insert, a concatenation and a fold wants
                    a list, and a bag something is REMOVED from wants an index.
                    value.ml's bstore says which the dial picks and why. *)

let set_build (l : value list) : Value.sstore =
  List.fold_left (fun s v -> Value.sadd v s) (Value.sempty ()) l

(* ---------- unary ---------- *)

(* interp_unop.

   MATCHED ON THE OPERATOR, EXHAUSTIVELY, with the value match nested inside
   each arm, and no wildcard over the operator.  That is deliberate and it is
   the thing that keeps the total honest: an operator added to the language
   cannot arrive here costing one step by falling into a catch-all, because
   there is no catch-all to fall into and the file will not compile until an
   arm is written.  Every arm below either charges what its body does or is
   constant, in which case the one step the dispatch already charged is the
   whole of it. *)
let interp_unop (o : unop) (v : value) : value =
  match o with
  (* constant: the dispatch is the whole cost *)
  | ONeg -> (match v with VInt z -> VInt (-z) | _ -> VUnit)
  | ONot -> (match v with VBool b -> VBool (not b) | _ -> VUnit)
  | OSome -> VOption (Some v)
  (* an OCaml string carries its length, so this reads a header word *)
  | OLengthString -> (match v with VString s -> VInt (String.length s) | _ -> VUnit)
  | OLength -> (match v with VList l -> let n = List.length l in Count.walk n; VInt n | _ -> VUnit)
  | OStringOfInt ->
      (match v with
       | VInt z -> let s = string_of_int z in Count.chars (String.length s); VString s
       | _ -> VUnit)
  (* list_to_bag (map snd d) *)
  (* no key, and a hash table enumerates its entries as a tree does, so this
     is charged the same under either rep *)
  | ODictValues ->
      (match v with
       (* the values, in whatever order the dictionary holds them: a bag has
          no order of its own to get wrong *)
       | VDict (_, d) ->
           VBag (Value.dfold (fun _ v b -> Count.walk 1; Value.badd v b) d
                   (Value.bempty ()))
       | _ -> VUnit)
  (* VSet (map fst l).  In Interpret.v this is a projection, because a
     well-typed bag is a sorted dedup'd association list already; here a bag is
     an UNORDERED list (see value.ml), so the order the set needs has to be paid
     for -- one tree insert per entry, charged to cmps.  That is the same price
     the source's own OSetOfList pays on its survivors, so the coercion is not
     somewhere a pessimization could hide. *)
  | OSetOfBag ->
      (match v with
       | VBag b -> VSet (set_build (Value.belements_unordered b))
       | _ -> VUnit)
  (* A coercion READS every row: bag_of_list and set_build walk the list, and
     set_build inserts each element one at a time.  Counting these is what keeps
     the row counter honest about the source programs, whose whole cost on a
     membership test is the coercion -- eval/Jenkins_ItemDeletion's source does
     nothing else, and would otherwise be reported as touching no rows at all. *)
  | OBagOfList ->
      (match v with
       | VList l -> Count.visit (List.length l); VBag (Value.bof_list l)
       | _ -> VUnit)
  | OSetOfList ->
      (match v with
       | VList l -> Count.visit (List.length l); VSet (set_build l)
       | _ -> VUnit)

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
  | OConcatString ->
      (match a, b with
       | VString a, VString b ->
           Count.chars (String.length a + String.length b);
           VString (a ^ b)
       | _ -> VUnit)
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
  | OBagInsert -> (match a with VBag m -> VBag (Value.badd b m) | _ -> VUnit)
  | OSetInsert ->
      (match a with VSet s -> VSet (Value.sadd b s) | _ -> VUnit)
  | OSetUnion ->
      (match a, b with
       (* the smaller side is the one iterated, inside Value.sunion *)
       | VSet x, VSet y -> VSet (Value.sunion x y)
       | _ -> VUnit)
  | OSetIntersect ->
      (match a, b with
       | VSet x, VSet y -> VSet (Value.sinter x y)
       | _ -> VUnit)
  | OSetDiff ->
      (match a, b with
       | VSet x, VSet y -> VSet (Value.sdiff x y)
       | _ -> VUnit)
  | OBagDiff ->
      (match a, b with
       | VBag x, VBag y -> VBag (Value.bdiff x y)
       | _ -> VUnit)
  | OSetMem ->
      (match a with VSet s -> VBool (Value.smem b s) | _ -> VUnit)
  (* a contains b *)
  | OStrContains ->
      (match a, b with VString s, VString p -> VBool (str_contains s p) | _ -> VUnit)
  (* the maximal runs of characters that are not separators, as pg_trgm's
     find_word walks them.  Charged as the scan plus the bytes copied into
     the words -- the class test is ONE step per character, as ISWORDCHR is,
     not a search of the separator alphabet, which is what a backend and
     pg_trgm both do. *)
  | OWords ->
      (match a, b with
       | VString seps, VString s ->
           Count.chars (String.length s);
           let out = ref [] and buf = Buffer.create 16 in
           let flush () =
             if Buffer.length buf > 0 then begin
               Count.chars (Buffer.length buf);
               out := VString (Buffer.contents buf) :: !out;
               Buffer.clear buf
             end in
           String.iter
             (fun c -> if String.contains seps c then flush () else Buffer.add_char buf c)
             s;
           flush ();
           VList (List.rev !out)
       | _ -> VUnit)
  | OLookup ->
      (match a with
       | VDict (_, d) -> VOption (Value.dfind b d)
       | _ -> VUnit)
  | ODelete ->
      (match a with
       | VDict (r, d) -> VDict (r, Value.dremove b d)
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
       | VDict (r, d) -> VDict (r, Value.dadd b c d)
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
       | VDict (RRanged, DTree d) -> VDict (RRanged, DTree (dict_range b c d))
       | VDict (RUnranged, _) -> failwith "ODictRange on an Unranged dictionary"
       (* Value.dempty gives a Ranged dictionary a tree under every setting,
          so this is unreachable -- and it is spelled out rather than left to
          a wildcard, because a wildcard here would silently accept a hashed
          store if that ever changed *)
       | VDict (RRanged, DHash _) -> failwith "a Ranged dictionary is never hashed"
       | _ -> VUnit)
  | ODictRangeDelete ->
      (match a with
       | VDict (RRanged, DTree d) -> VDict (RRanged, DTree (dict_range_delete b c d))
       | VDict (RUnranged, _) -> failwith "ODictRangeDelete on an Unranged dictionary"
       | VDict (RRanged, DHash _) -> failwith "a Ranged dictionary is never hashed"
       | _ -> VUnit)

(* ---------- aggregates ----------

   interp_aggr folds over bag_to_list, so an element of multiplicity n is
   folded n times; interp_aci_aggr folds over the set's elements from the
   right.  Both fold with an operator that returns VUnit off its expected
   shape, and a VUnit accumulator poisons every later step, so a single
   element of the wrong shape makes the whole fold VUnit.  That is reproduced
   rather than assumed away. *)

(* sum and count are commutative, so the order the store hands the
   occurrences over in cannot change the answer and is not paid for *)
let interp_ac_fold (ag : aggr) (b : value list) : value =
  Count.walk (List.length b);
  match ag with
  | AGSum ->
      List.fold_left
        (fun acc v -> match acc, v with VInt a, VInt z -> VInt (a + z) | _ -> VUnit)
        (VInt 0) b
  | AGCount -> VInt (List.length b)

(* min and max are picked by COMPARISON, so the order the store hands them
   over in cannot change the answer and is not paid for *)
let interp_aci_fold (ag : aci_aggr) (s : Value.sstore) : value =
  Count.walk (Value.scardinal s);
  let pick = match ag with AGMin -> min | AGMax -> max in
  List.fold_right
    (fun v acc ->
       match acc with
       | VOption None -> VOption (Some v)
       | VOption (Some (VInt v')) ->
           (match v with VInt z -> VOption (Some (VInt (pick z v'))) | _ -> VUnit)
       | _ -> VUnit)
    (Value.selements_unordered s) (VOption None)

(* ---------- records ---------- *)

(* record_sort: by field name *)
(* Putting a record's fields into canonical order is the interpreter keeping
   its values canonical, not work the program implies -- a backend fixes a
   record's layout at compile time -- so it is charged to [Count.over] with
   the environment lookups, and not to the crossing figure.  baseline.ml
   builds its records already ordered and would otherwise be getting this
   for free against us. *)
let record_sort (l : (string * value) list) : (string * value) list =
  List.stable_sort (fun (a, _) (b, _) -> Count.over 1; String.compare a b) l

(* record_proj.  An association list is walked, so the position reached is
   what a projection costs; a record is small and fixed by the term, so this
   can never bend an exponent, but it happens once per row of a scan. *)
let record_proj (s : string) (l : (string * value) list) : value =
  let rec go = function
    | [] -> VUnit
    | (k, v) :: rest -> Count.field 1; if k = s then v else go rest
  in
  go l

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
      (match interp_expr store env e with
       | VBag b -> interp_ac_fold ag (Value.belements_unordered b)
       | _ -> VUnit)
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
       | LikeBag, VBag b -> Count.visit (Value.bcardinal b); VList (Value.bcanon b)
       | LikeSet, VSet s -> Count.visit (Value.scardinal s); VList (Value.selements s)
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
      (* A BAG HAS NO ORDER TO PRESERVE, so each sub-bag's occurrences go in
         wherever the accumulator's store puts them.  Under BList that is a
         cons apiece, as the old rev_append was; under either multiset it is
         an insert apiece, which is what holding a bag that way costs. *)
      Count.visit (Value.bcardinal b);
      VBag
        (Value.bfold
           (fun v acc ->
              match interp_expr store (SMap.add x v env) e2 with
              | VBag b2 -> Value.bfold Value.badd b2 acc
              | _ -> acc)
           b (Value.bempty ()))
  | LikeSet, VSet s ->
      Count.visit (Value.scardinal s);
      VSet
        (Value.sfold
           (fun v acc ->
              match interp_expr store (SMap.add x v env) e2 with
              (* the union the set flatmap performs iterates the smaller side
                 and probes the other, like every other union *)
              | VSet s2 -> Value.sunion acc s2
              | _ -> acc)
           s (Value.sempty ()))
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
