(* What the subjects' terms are actually made of.

   The backend has 13 unops, 24 binops, 4 ternops, 2 aggregates and 4
   idempotent aggregates to cover.  Implementing them in a guessed order
   wastes effort on operators no subject uses and leaves common ones for
   last, so this counts them -- over both columns of every subject, which is
   exactly the set that has to compile. *)

open Extracted

let tally : (string, int) Hashtbl.t = Hashtbl.create 64
let bump (k : string) = Hashtbl.replace tally k (1 + Option.value ~default:0 (Hashtbl.find_opt tally k))

let unop = function
  | ONeg -> "ONeg" | ONot -> "ONot" | OLength -> "OLength"
  | OLengthString -> "OLengthString" | OStringOfInt -> "OStringOfInt"
  | OSome -> "OSome" | ODictValues -> "ODictValues" | OSetOfBag -> "OSetOfBag"
  | OBagOfList -> "OBagOfList" | OSetOfList -> "OSetOfList"
  | OSetSize -> "OSetSize" | ODictMinKey -> "ODictMinKey"
  | OTrigrams -> "OTrigrams"

let binop = function
  | OPlus -> "OPlus" | OMinus -> "OMinus" | OTimes -> "OTimes"
  | ODiv -> "ODiv" | OMod -> "OMod" | OAnd -> "OAnd" | OOr -> "OOr"
  | OConcat -> "OConcat" | OConcatString -> "OConcatString"
  | OLess -> "OLess" | OEq -> "OEq" | OCons -> "OCons" | ORange -> "ORange"
  | OBagInsert -> "OBagInsert" | OBagDiff -> "OBagDiff"
  | OSetInsert -> "OSetInsert" | OSetUnion -> "OSetUnion"
  | OSetIntersect -> "OSetIntersect" | OSetDiff -> "OSetDiff"
  | OSetMem -> "OSetMem" | OStrContains -> "OStrContains"
  | OLookup -> "OLookup" | ODelete -> "ODelete" | OWords -> "OWords"

let ternop = function
  | OInsert -> "OInsert" | OSubstring -> "OSubstring"
  | ODictRange -> "ODictRange" | ODictRangeDelete -> "ODictRangeDelete"

let tag = function LikeSet -> "Set" | LikeBag -> "Bag" | LikeList -> "List"

let rec ce (e : expr) : unit =
  match e with
  | EVar _ -> bump "EVar" | ELoc _ -> bump "ELoc"
  | EAtom _ -> bump "EAtom"
  | EUnop (o, e) -> bump (unop o); ce e
  | EBinop (o, a, b) -> bump (binop o); ce a; ce b
  | ETernop (o, a, b, c) -> bump (ternop o); ce a; ce b; ce c
  | EIf (a, b, c) -> bump "EIf"; ce a; ce b; ce c
  | ELet (a, _, b) -> bump "ELet"; ce a; ce b
  | EFlatmap (t, a, _, b) -> bump ("EFlatmap/" ^ tag t); ce a; ce b
  | EFold (a, b, _, _, c) -> bump "EFold"; ce a; ce b; ce c
  | EACFold (a, e) ->
      bump (match a with AGSum -> "EACFold/Sum" | AGCount -> "EACFold/Count"); ce e
  | EACIFold (a, e) ->
      bump (match a with AGMin -> "EACIFold/Min" | AGMax -> "EACIFold/Max"
                       | AGUnion -> "EACIFold/Union" | AGIntersect -> "EACIFold/Intersect");
      ce e
  | ERecord l -> bump "ERecord"; List.iter (fun (_, e) -> ce e) l
  | EAccess (e, _) -> bump "EAccess"; ce e
  | EOptMatch (a, b, _, c) -> bump "EOptMatch"; ce a; ce b; ce c
  | ESort (t, e) -> bump ("ESort/" ^ tag t); ce e

let rec cc (c : command) : unit =
  match c with
  | CSkip -> bump "CSkip"
  | CSeq (a, b) -> bump "CSeq"; cc a; cc b
  | CLet (e, _, c) -> bump "CLet"; ce e; cc c
  | CLetMut (e, _, c) -> bump "CLetMut"; ce e; cc c
  | CAssign (_, e) -> bump "CAssign"; ce e
  | CIf (e, a, b) -> bump "CIf"; ce e; cc a; cc b
  | CForeach (e, _, c) -> bump "CForeach"; ce e; cc c

let run () =
  List.iter (fun ((_, src), opt) -> cc src; cc opt) Extracted.annotated_nf;
  let l = Hashtbl.fold (fun k v acc -> (k, v) :: acc) tally [] in
  let l = List.sort (fun (_, a) (_, b) -> Int.compare b a) l in
  let total = List.fold_left (fun acc (_, v) -> acc + v) 0 l in
  Printf.printf "%d constructs across both columns of all 22 subjects\n\n" total;
  List.iter (fun (k, v) -> Printf.printf "%-22s %6d\n" k v) l
