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
  | AEmptyDict (_, _) -> VDict VMap.empty
  | AEmptyBag _ -> VBag bag_empty
  | AEmptySet _ -> VSet VSet.empty
  | AUnit -> VUnit

(* ---------- unary ---------- *)

(* interp_unop *)
let interp_unop (o : unop) (v : value) : value =
  match o, v with
  | ONeg, VInt z -> VInt (-z)
  | ONot, VBool b -> VBool (not b)
  | OLength, VList l -> let n = List.length l in Count.walk n; VInt n
  | OLengthString, VString s -> VInt (String.length s)
  | OIntToString, VInt z -> VString (string_of_int z)
  | OSome, v -> VOption (Some v)
  (* list_to_bag (map snd d) *)
  | ODictValues, VDict d ->
      VBag (VMap.fold (fun _ v b -> Count.walk 1; v :: b) d [])
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
  | OSetInsert -> (match a with VSet s -> VSet (VSet.add b s) | _ -> VUnit)
  | OSetUnion -> (match a, b with VSet x, VSet y -> VSet (VSet.union x y) | _ -> VUnit)
  | OSetIntersect -> (match a, b with VSet x, VSet y -> VSet (VSet.inter x y) | _ -> VUnit)
  | OSetDiff -> (match a, b with VSet x, VSet y -> VSet (VSet.diff x y) | _ -> VUnit)
  | OSetMem -> (match a with VSet s -> VBool (VSet.mem b s) | _ -> VUnit)
  (* a contains b *)
  | OStrContains ->
      (match a, b with VString s, VString p -> VBool (str_contains s p) | _ -> VUnit)
  | OLookup -> (match a with VDict d -> VOption (VMap.find_opt b d) | _ -> VUnit)
  | ODelete -> (match a with VDict d -> VDict (VMap.remove b d) | _ -> VUnit)

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
  | OInsert -> (match a with VDict d -> VDict (VMap.add b c d) | _ -> VUnit)
  | OSubstring ->
      (match a, b, c with
       | VString s, VInt i, VInt n -> VString (substring s i n)
       | _ -> VUnit)
  | ODictRange -> (match a with VDict d -> VDict (dict_range b c d) | _ -> VUnit)
  | ODictRangeDelete -> (match a with VDict d -> VDict (dict_range_delete b c d) | _ -> VUnit)

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
       | LikeList, VList l -> VList (List.stable_sort Value.compare l)
       | LikeBag, VBag b -> VList (bag_canonical b)
       | LikeSet, VSet s -> VList (VSet.elements s)
       | _, _ -> VUnit)
  | EBagOf e ->
      (match interp_expr store env e with VList l -> VBag (bag_of_list l) | _ -> VUnit)
  | ESetOf e ->
      (match interp_expr store env e with VList l -> VSet (set_of_list l) | _ -> VUnit)

(* EFlatmap, one case per tag.

   The bag case walks the elements with their repetitions, which is what
   bag_to_list hands the specification's flat_map. *)
and interp_flatmap store env tag e1 x e2 =
  match tag, interp_expr store env e1 with
  | LikeList, VList l ->
      VList
        (List.concat_map
           (fun v ->
              match interp_expr store (SMap.add x v env) e2 with VList l2 -> l2 | _ -> [])
           l)
  | LikeBag, VBag b ->
      (* rev_append rather than append: a bag has no order to preserve, and
         the left fold would otherwise be quadratic *)
      VBag
        (List.fold_left
           (fun acc v ->
              match interp_expr store (SMap.add x v env) e2 with
              | VBag b2 -> List.rev_append b2 acc
              | _ -> acc)
           bag_empty b)
  | LikeSet, VSet s ->
      VSet
        (VSet.fold
           (fun v acc ->
              match interp_expr store (SMap.add x v env) e2 with
              | VSet s2 -> VSet.union acc s2
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
