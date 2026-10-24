(* The bijection, written out.

   value.ml claims that its trees and the specification's canonical sorted
   lists represent the same maps, multisets and sets.  That claim is only
   worth as much as a function that exhibits it, so here it is, in both
   directions, and differential.ml runs the specification and the evaluator
   on the same programs and compares through it.

   Note which way the work falls.  A dictionary and a set are canonical on
   both sides, so their conversions are a traversal in ascending order.  A
   bag is canonical only on the specification's side, so to_ref has to sort
   and count -- which is exactly the cost value.ml says it defers, now paid
   in the one place that looks. *)

module R = Extracted
open Value

let rec nat_of_int (n : int) : R.nat = if n <= 0 then R.O else R.S (nat_of_int (n - 1))
let rec int_of_nat (n : R.nat) : int = match n with R.O -> 0 | R.S m -> 1 + int_of_nat m

(* a sorted list to its run-length encoding, which is Value.v's bag *)
let rec counted (l : value list) : (R.value * R.nat) list = match l with
  | [] -> []
  | x :: _ ->
      let same, rest = List.partition (fun y -> eqb x y) l in
      (to_ref x, nat_of_int (List.length same)) :: counted rest

and to_ref (v : value) : R.value =
  match v with
  | VInt z -> R.VInt z
  | VBool b -> R.VBool b
  | VString s -> R.VString s
  | VOption None -> R.VOption None
  | VOption (Some v) -> R.VOption (Some (to_ref v))
  | VList l -> R.VList (List.map to_ref l)
  | VRecord l -> R.VRecord (List.map (fun (s, v) -> (s, to_ref v)) l)
  | VDict d -> R.VDict (List.map (fun (k, v) -> (to_ref k, to_ref v)) (VMap.bindings d))
  | VBag b -> R.VBag (counted (List.sort compare b))
  | VSet s -> R.VSet (List.map to_ref (VSet.elements s))
  | VUnit -> R.VUnit

let rec of_ref (v : R.value) : value =
  match v with
  | R.VInt z -> VInt z
  | R.VBool b -> VBool b
  | R.VString s -> VString s
  | R.VOption None -> VOption None
  | R.VOption (Some v) -> VOption (Some (of_ref v))
  | R.VList l -> VList (List.map of_ref l)
  | R.VRecord l -> VRecord (List.map (fun (s, v) -> (s, of_ref v)) l)
  | R.VDict d ->
      VDict (List.fold_left (fun m (k, v) -> VMap.add (of_ref k) (of_ref v) m) VMap.empty d)
  | R.VBag b ->
      VBag (List.concat_map (fun (v, n) -> List.init (int_of_nat n) (fun _ -> of_ref v)) b)
  | R.VSet s -> VSet (set_of_list (List.map of_ref s))
  | R.VUnit -> VUnit
