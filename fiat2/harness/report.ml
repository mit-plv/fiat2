(* A static report over the extracted subject programs.

   Its job is deliberately narrow: walk the terms and say what is in them.
   It evaluates nothing -- bench.ml does that.  What this establishes is
   that the extracted terms are the terms we think they are.

   The last two sections are the point.  installed_fields recomputes, in
   OCaml, the projection that each subject's own Rocq file pins by
   vm_compute -- the field names of the record the table is bound to.
   Agreement is a check on the EXTRACTION rather than on the optimizer: the
   Rocq lemmas already say what those names are, so if OCaml reports the
   same names, the term that crossed the boundary is the term the theorems
   are about.  The free-name section says what a workload must supply, read
   off the terms rather than off the Rocq files, so the generators cannot
   drift away from the programs they feed. *)

open Extracted

(* ---------- walking ---------- *)

let rec expr_nodes (e : expr) : int =
  1 + match e with
  | EVar _ | ELoc _ | EAtom _ -> 0
  | EUnop (_, a) | EACFold (_, a) | EACIFold (_, a) | EAccess (a, _)
  | ESort (_, a) | EBagOf a | ESetOf a -> expr_nodes a
  | EBinop (_, a, b) | ELet (a, _, b) -> expr_nodes a + expr_nodes b
  | EFlatmap (_, a, _, b) -> expr_nodes a + expr_nodes b
  | ETernop (_, a, b, c) | EIf (a, b, c) | EOptMatch (a, b, _, c) ->
      expr_nodes a + expr_nodes b + expr_nodes c
  | EFold (a, b, _, _, c) -> expr_nodes a + expr_nodes b + expr_nodes c
  | ERecord l -> List.fold_left (fun n (_, a) -> n + expr_nodes a) 0 l

let rec cmd_nodes (c : command) : int =
  1 + match c with
  | CSkip -> 0
  | CSeq (a, b) -> cmd_nodes a + cmd_nodes b
  | CLet (e, _, a) | CLetMut (e, _, a) | CForeach (e, _, a) ->
      expr_nodes e + cmd_nodes a
  | CAssign (_, e) -> expr_nodes e
  | CIf (e, a, b) -> expr_nodes e + cmd_nodes a + cmd_nodes b

(* every operator occurrence in a command, as a name *)
let operators (c : command) : string list =
  let acc = ref [] in
  let add s = acc := s :: !acc in
  let unop = function
    | ONeg -> "ONeg" | ONot -> "ONot" | OLength -> "OLength"
    | OLengthString -> "OLengthString" | OIntToString -> "OIntToString"
    | OSome -> "OSome" | ODictValues -> "ODictValues" in
  let binop = function
    | OPlus -> "OPlus" | OMinus -> "OMinus" | OTimes -> "OTimes"
    | ODiv -> "ODiv" | OMod -> "OMod" | OAnd -> "OAnd" | OOr -> "OOr"
    | OConcat -> "OConcat" | OConcatString -> "OConcatString"
    | OLess -> "OLess" | OEq -> "OEq" | OCons -> "OCons" | ORange -> "ORange"
    | OBagInsert -> "OBagInsert" | OSetInsert -> "OSetInsert"
    | OSetUnion -> "OSetUnion" | OSetIntersect -> "OSetIntersect"
    | OSetDiff -> "OSetDiff" | OSetMem -> "OSetMem"
    | OStrContains -> "OStrContains" | OLookup -> "OLookup"
    | ODelete -> "ODelete" in
  let ternop = function
    | OInsert -> "OInsert" | OSubstring -> "OSubstring"
    | ODictRange -> "ODictRange" | ODictRangeDelete -> "ODictRangeDelete" in
  let rec ex (e : expr) = match e with
    | EVar _ | ELoc _ | EAtom _ -> ()
    | EUnop (o, a) -> add (unop o); ex a
    | EBinop (o, a, b) -> add (binop o); ex a; ex b
    | ETernop (o, a, b, c) -> add (ternop o); ex a; ex b; ex c
    | EIf (a, b, c) | EOptMatch (a, b, _, c) -> ex a; ex b; ex c
    | ELet (a, _, b) -> ex a; ex b
    | EFlatmap (_, a, _, b) -> add "EFlatmap"; ex a; ex b
    | EFold (a, b, _, _, c) -> add "EFold"; ex a; ex b; ex c
    | EACFold (_, a) -> add "EACFold"; ex a
    | EACIFold (_, a) -> add "EACIFold"; ex a
    | ERecord l -> List.iter (fun (_, a) -> ex a) l
    | EAccess (a, _) -> ex a
    | ESort (_, a) -> add "ESort"; ex a
    | EBagOf a -> add "EBagOf"; ex a
    | ESetOf a -> add "ESetOf"; ex a in
  let rec cm (c : command) = match c with
    | CSkip -> ()
    | CSeq (a, b) -> cm a; cm b
    | CLet (e, _, a) | CLetMut (e, _, a) | CForeach (e, _, a) -> ex e; cm a
    | CAssign (_, e) -> ex e
    | CIf (e, a, b) -> ex e; cm a; cm b in
  cm c; !acc

let count_of name c = List.length (List.filter (( = ) name) (operators c))

(* the field names of the record the table is bound to: this is the
   installed_fields projection the Rocq files pin *)
let rec installed_fields (c : command) : string list option =
  match c with
  | CLetMut (ERecord l, _, _) -> Some (List.map fst l)
  | CLetMut (_, _, body) | CLet (_, _, body) | CForeach (_, _, body) ->
      installed_fields body
  | CSeq (a, b) | CIf (_, a, b) ->
      (match installed_fields a with Some r -> Some r | None -> installed_fields b)
  | CSkip | CAssign _ -> None

(* ---------- the report ---------- *)

let probe_ops = [ "OLookup"; "ODictRange"; "ODictRangeDelete"; "OInsert";
                  "ODelete"; "ODictValues"; "OSetMem" ]

let run () =
  Printf.printf "%-16s %8s %8s   %s\n" "subject" "src" "opt" "installed fields";
  Printf.printf "%s\n" (String.make 72 '-');
  List.iter
    (fun ((name, src), opt) ->
       let fields =
         match installed_fields opt with
         | None -> "(table is still a plain list)"
         | Some fs -> String.concat ", " fs in
       Printf.printf "%-16s %8d %8d   %s\n" name (cmd_nodes src) (cmd_nodes opt) fields)
    subjects;

  Printf.printf "\noperators the optimizer INTRODUCED (count in opt, none in src):\n";
  List.iter
    (fun ((name, src), opt) ->
       let gained =
         List.filter_map
           (fun o ->
              let n = count_of o opt - count_of o src in
              if n > 0 then Some (Printf.sprintf "%s x%d" o n) else None)
           probe_ops in
       Printf.printf "  %-16s %s\n" name
         (if gained = [] then "(none)" else String.concat ", " gained))
    subjects;

  Printf.printf "\nalternatives:\n";
  List.iter
    (fun (name, c) ->
       let fields = match installed_fields c with
         | None -> "(plain list)" | Some fs -> String.concat ", " fs in
       Printf.printf "  %-22s %6d nodes   %s\n" name (cmd_nodes c) fields)
    alternatives;

  (* no subject sorts, so the canonical materialisation of a bag or set
     never has to be paid for; this is an assumption the asymptotic
     argument rests on, so it is checked rather than asserted *)
  let sorts =
    List.fold_left (fun n ((_, s), o) -> n + count_of "ESort" s + count_of "ESort" o)
      0 subjects in
  Printf.printf "\nESort occurrences across every subject, before and after: %d\n" sorts;

  (* What a workload has to supply, read off the terms themselves; a
     generator in gen.ml that forgot one of these would silently feed the
     program a VUnit *)
  Printf.printf "\nfree names (env variables | store locations):\n";
  List.iter
    (fun ((name, src), opt) ->
       let sv, sl = Free.of_command src and ov, ol = Free.of_command opt in
       Printf.printf "  %-16s src %s | %s\n" name
         (String.concat ", " sv) (String.concat ", " sl);
       if (sv, sl) <> (ov, ol) then
         Printf.printf "  %-16s opt %s | %s\n" "" (String.concat ", " ov)
           (String.concat ", " ol))
    subjects
