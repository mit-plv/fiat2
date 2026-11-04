(* The type level of the compiled backend: a Conquord type becomes an OCaml
   type, and the declarations that takes are generated.

   WHY THIS IS THE FOUNDATION AND NOT A DETAIL.  harness/README.md measured
   where the interpreter's seconds go: its own dispatch and environment
   lookups are about a FIFTH of the cost at 1600 rows, so generating OCaml
   from the interpreter would buy roughly 1.3x.  What separates those seconds
   from hand-written code is the REPRESENTATION -- boxed dynamic values
   compared structurally, a record walked as an association list -- and the
   structure choice.  So the backend's value is monomorphization, and
   monomorphization is a question about types before it is one about code.

   WHAT EACH TYPE BECOMES, and why.

     TInt     int        unboxed
     TBool    bool
     TString  string
     TUnit    unit
     TOption  option
     TList    list
     TRecord  a GENERATED record, fields at constant offsets and no names at
              run time.  This is the whole point: value.ml walks an
              association list and pays Count.field per field passed, and
              that work disappears rather than going uncounted.
     TBag     list       -- by MEASUREMENT, not convenience.  harness/README
              records the experiment: a tree multiset costs n log n whole-row
              comparisons at every OBagOfList (user_search/suggestMiss 60 ->
              612,820) and a hash trie hashes every element for a benefit no
              fold collects.  Both uniform answers are wrong by one to four
              orders of magnitude; the list is right for every bag these
              programs build.
     TSet     Set.Make over the element's compare
     TDict    the KIND decides, which is what dict_kind is for: Ranged gets
              Map.Make (an ordered tree, because a range query is a question
              only an ordered store can answer) and Unranged gets
              CCHashTrie.Make.  The type system makes that choice, not this
              file.

              CCHashTrie and NOT Hashtbl.Make, which would be the obvious
              reading of "a hash table".  Conquord's dictionary operations
              are FUNCTIONAL -- OInsert returns a new dictionary -- so an
              imperative table would have to be copied per insert, which is
              O(n) and destroys the incrementality the whole measurement
              exists to demonstrate.  A persistent hash-array-mapped trie is
              what a backend holding an Unranged dictionary would really
              use, and it is what value.ml already charges for on the
              interpreted side, so the two sides stay comparable.

   KEY TYPES ARE INTERNED ONCE and get all three functors, so a dictionary, a
   set and a hash table keyed on the same type share one comparison and one
   hash.  Nothing here picks a structure that the type does not license. *)

open Extracted

(* ---------- interning ---------- *)

(* A canonical string per type, so that two spellings of the same type get one
   declaration.  Record types are already name-sorted by the type system, so
   this is a faithful identity on them. *)
let rec key_of (t : type0) : string =
  match t with
  | TInt -> "i"
  | TBool -> "b"
  | TString -> "s"
  | TUnit -> "u"
  | TOption t -> "o(" ^ key_of t ^ ")"
  | TList t -> "l(" ^ key_of t ^ ")"
  | TBag t -> "g(" ^ key_of t ^ ")"
  | TSet t -> "e(" ^ key_of t ^ ")"
  | TRecord l ->
      "r(" ^ String.concat ";"
               (List.map (fun (n, t) -> n ^ ":" ^ key_of t) l) ^ ")"
  | TDict (dk, k, v) ->
      (match dk with Ranged -> "dr(" | Unranged -> "du(")
      ^ key_of k ^ "," ^ key_of v ^ ")"

(* declarations in dependency order: a record is registered only after the
   types of its fields are, because registration recurses first *)
let decls : string list ref = ref []
let names : (string, string) Hashtbl.t = Hashtbl.create 64
let next = ref 0

let fresh (prefix : string) : string =
  incr next; Printf.sprintf "%s%d" prefix !next

let emit (s : string) : unit = decls := s :: !decls

(* OCaml record fields must be lowercase identifiers, and Conquord field names
   need not be -- the index tags are "0" and "1".  Mangled with a prefix so
   that no name can collide with a keyword and every name is legal. *)
let field_name (f : string) : string =
  let b = Bytes.of_string f in
  Bytes.iteri
    (fun i c ->
       match c with
       | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> ()
       | _ -> Bytes.set b i '_')
    b;
  "f_" ^ Bytes.to_string b

(* ---------- the three things a type needs ---------- *)

let rec ocaml_ty (t : type0) : string =
  match t with
  | TInt -> "int"
  | TBool -> "bool"
  | TString -> "string"
  | TUnit -> "unit"
  | TOption t -> "(" ^ ocaml_ty t ^ ") option"
  | TList t -> "(" ^ ocaml_ty t ^ ") list"
  | TBag t -> "(" ^ ocaml_ty t ^ ") list"
  | TRecord _ -> record_name t
  | TSet e -> key_module e ^ "_Set.t"
  | TDict (Unranged, k, v) -> "(" ^ ocaml_ty v ^ ") " ^ key_module k ^ "_Tbl.t"
  | TDict (Ranged, k, v) -> "(" ^ ocaml_ty v ^ ") " ^ key_module k ^ "_Map.t"

and cmp_of (t : type0) : string =
  match t with
  | TInt -> "Rt.cmp_int"
  | TBool -> "Rt.cmp_bool"
  | TString -> "Rt.cmp_string"
  | TUnit -> "Rt.cmp_unit"
  | TOption t -> "(Rt.cmp_option " ^ cmp_of t ^ ")"
  | TList t | TBag t -> "(Rt.cmp_list " ^ cmp_of t ^ ")"
  | TRecord _ -> "cmp_" ^ record_name t
  | TSet e -> key_module e ^ "_Set.compare"
  | TDict _ ->
      (* No subject keys a collection on a dictionary, and a hash table has no
         comparison to offer, so this is a refusal rather than a stub: it says
         which shape is unsupported instead of silently ordering wrongly. *)
      "(fun _ _ -> failwith \"no comparison on a dictionary key\")"

and eq_of (t : type0) : string =
  match t with
  | TInt -> "Rt.eq_int"
  | TBool -> "Rt.eq_bool"
  | TString -> "Rt.eq_string"
  | TUnit -> "Rt.eq_unit"
  | TOption e -> "(Rt.eq_option " ^ eq_of e ^ ")"
  | TList e -> "(Rt.eq_list " ^ eq_of e ^ ")"
  | TBag e -> "(Rt.eq_bag " ^ cmp_of e ^ ")"
  | TRecord _ -> "eq_" ^ record_name t
  | TSet e -> key_module e ^ "_Set.equal"
  | TDict (Ranged, k, v) ->
      Printf.sprintf "(%s_Map.equal %s)" (key_module k) (eq_of v)
  | TDict (Unranged, k, v) ->
      (* equal bindings, decided without producing a key order a trie does
         not have: same cardinality, and every binding of one found in the
         other *)
      let m = key_module k ^ "_Tbl" in
      Printf.sprintf
        "(fun a b -> %s.cardinal a = %s.cardinal b && %s.fold ~f:(fun acc kk vv -> acc && (match %s.get kk b with Some w -> %s vv w | None -> false)) ~x:true a)"
        m m m m (eq_of v)

and hash_of (t : type0) : string =
  match t with
  | TInt -> "Rt.hash_int"
  | TBool -> "Rt.hash_bool"
  | TString -> "Rt.hash_string"
  | TUnit -> "Rt.hash_unit"
  | TOption t -> "(Rt.hash_option " ^ hash_of t ^ ")"
  | TList t | TBag t -> "(Rt.hash_list " ^ hash_of t ^ ")"
  | TRecord _ -> "hash_" ^ record_name t
  | TSet _ | TDict _ ->
      "(fun _ -> failwith \"no hash on a collection key\")"

(* ---------- records ---------- *)

and record_name (t : type0) : string =
  let k = key_of t in
  match Hashtbl.find_opt names k with
  | Some n -> n
  | None ->
      let fields = match t with TRecord l -> l | _ -> assert false in
      (* the field types first, so their declarations precede this one *)
      let parts =
        List.map (fun (f, ft) -> (field_name f, ft, ocaml_ty ft)) fields in
      let n = fresh "row" in
      Hashtbl.replace names k n;
      (match parts with
       | [] ->
           (* a record with no fields is not an OCaml record; it carries no
              information either, so unit is faithful *)
           emit (Printf.sprintf "type %s = unit" n);
           emit (Printf.sprintf "let cmp_%s (_ : %s) (_ : %s) = Rt.cmp_unit () ()" n n n);
           emit (Printf.sprintf "let hash_%s (_ : %s) = Rt.hash_unit ()" n n);
           emit (Printf.sprintf "let eq_%s (_ : %s) (_ : %s) = true" n n n);
           emit (Printf.sprintf "let of_%s (_ : Value.t) : %s = ()" n n)
       | _ ->
           emit
             (Printf.sprintf "type %s = { %s }" n
                (String.concat "; "
                   (List.map (fun (fn, _, ty) -> fn ^ " : " ^ ty) parts)));
           (* one Count.comparisons for the record's own node, then its fields
              in field-name order -- which is the order the type system keeps
              them in, so this is value_compare's order on the same values *)
           emit
             (Printf.sprintf
                "let cmp_%s (x : %s) (y : %s) : int =\n  Rt.cmp_node ();\n%s"
                n n n
                (let rec chain = function
                   | [] -> "  0"
                   | [ (fn, ft, _) ] ->
                       Printf.sprintf "  %s x.%s y.%s" (cmp_of ft) fn fn
                   | (fn, ft, _) :: rest ->
                       Printf.sprintf
                         "  let c = %s x.%s y.%s in\n  if c <> 0 then c else\n%s"
                         (cmp_of ft) fn fn (chain rest)
                 in
                 chain parts));
           emit
             (Printf.sprintf
                "let hash_%s (x : %s) : int =\n  Rt.node ();\n  let h = 37 in\n%s  h"
                n n
                (String.concat ""
                   (List.map
                      (fun (fn, ft, _) ->
                         Printf.sprintf "  let h = (h * 31) + %s x.%s in\n"
                           (hash_of ft) fn)
                      parts)));
           emit
             (Printf.sprintf
                "let eq_%s (x : %s) (y : %s) : bool =\n  Rt.cmp_node ();\n%s"
                n n n
                (String.concat " &&\n"
                   (List.map
                      (fun (fn, ft, _) ->
                         Printf.sprintf "  %s x.%s y.%s" (eq_of ft) fn fn)
                      parts)));
           (* and the way in from a boxed value: the Conquord field NAME is
              what the assoc list is keyed on, not the mangled one *)
           emit
             (Printf.sprintf
                "let of_%s (v : Value.t) : %s =\n  let l = Rt.as_record v in\n  { %s }"
                n n
                (String.concat ";\n    "
                   (List.map2
                      (fun (fn, ft, _) (cf, _) ->
                         Printf.sprintf "%s = %s (Rt.fld l \"%s\")"
                           fn (of_expr ft) cf)
                      parts fields))));
      n

(* ---------- marshalling a workload in ----------

   Only the INPUT direction is generated, and only for the shapes the
   subjects' store and environment actually hold.  The output direction --
   turning a compiled program's final store back into a boxed value so that
   bench.ml's `agree` column can compare it against the interpreted run --
   is deliberately not generated yet: what it has to produce depends on what
   the emitted program's store looks like, which the expression codegen
   decides.  A guess now would be a guess to maintain. *)

and of_expr (t : type0) : string =
  match t with
  | TInt -> "Rt.as_int"
  | TBool -> "Rt.as_bool"
  | TString -> "Rt.as_string"
  | TUnit -> "Rt.as_unit"
  | TOption e ->
      Printf.sprintf "(fun v -> Option.map %s (Rt.as_option v))" (of_expr e)
  | TList e ->
      Printf.sprintf "(fun v -> List.map %s (Rt.as_list v))" (of_expr e)
  | TBag e ->
      (* a bag's boxed form holds a STORE, so this is a fold into canonical
         order and not a cast -- see Rt.as_bag_list *)
      Printf.sprintf "(fun v -> List.map %s (Rt.as_bag_list v))" (of_expr e)
  | TRecord _ -> "of_" ^ record_name t
  | TSet e ->
      (* user_search's `suggested` is a TSet in the ambient store, so a set
         IS an input -- which the first run of the generated readers found,
         against the comment that used to be here saying it could not be. *)
      let m = key_module e ^ "_Set" in
      Printf.sprintf
        "(fun v -> Value.sfold (fun e acc -> %s.add (%s e) acc) (Rt.as_set v) %s.empty)"
        m (of_expr e) m
  | TDict (dk, k, v) ->
      let m = key_module k in
      (match dk with
       | Ranged ->
           Printf.sprintf
             "(fun d -> Value.dfold (fun kk vv acc -> %s_Map.add (%s kk) (%s vv) acc) (Rt.as_dict d) %s_Map.empty)"
             m (of_expr k) (of_expr v) m
       | Unranged ->
           Printf.sprintf
             "(fun d -> Value.dfold (fun kk vv acc -> %s_Tbl.add (%s kk) (%s vv) acc) (Rt.as_dict d) %s_Tbl.empty)"
             m (of_expr k) (of_expr v) m)

(* ---------- key modules ---------- *)

and key_module (t : type0) : string =
  let k = "K" ^ key_of t in
  match Hashtbl.find_opt names k with
  | Some n -> n
  | None ->
      (* the key's own type and operations first *)
      let ty = ocaml_ty t and cmp = cmp_of t and hash = hash_of t in
      let n = fresh "K" in
      Hashtbl.replace names k n;
      emit
        (Printf.sprintf
           "module %s = struct\n  type t = %s\n  let compare = %s\n  let equal a b = %s a b = 0\n  let hash = %s\nend"
           n ty cmp cmp hash);
      emit (Printf.sprintf "module %s_Map = Map.Make (%s)" n n);
      emit (Printf.sprintf "module %s_Tbl = CCHashTrie.Make (%s)" n n);
      emit (Printf.sprintf "module %s_Set = Set.Make (%s)" n n);
      n

(* ---------- which types a program needs ---------- *)

(* Read off the annotations, which is every collection the program CREATES,
   and closed under the element types by ocaml_ty's own recursion.

   NOT provably complete: a record built by ERecord carries no annotation, so
   a record type that is never put into an annotated collection would be
   missed.  The full backend pass types every node and will not have that
   gap; until then this is what the declarations are collected from, and the
   emitted module failing to compile is how a gap would show. *)
let ty_of_atom (a : atom) : type0 option =
  match a with
  | ANil (Some t) -> Some (TList t)
  | ANone (Some t) -> Some (TOption t)
  | AEmptyDict (dk, Some (k, v)) -> Some (TDict (dk, k, v))
  | AEmptyBag (Some t) -> Some (TBag t)
  | AEmptySet (Some t) -> Some (TSet t)
  | _ -> None

let rec tys_expr (acc : type0 list) (e : expr) : type0 list =
  match e with
  | EVar _ | ELoc _ -> acc
  | EAtom a -> (match ty_of_atom a with Some t -> t :: acc | None -> acc)
  | EUnop (_, e) | EACFold (_, e) | EACIFold (_, e) | EAccess (e, _)
  | ESort (_, e) -> tys_expr acc e
  | EBinop (_, a, b) | ELet (a, _, b) | EFlatmap (_, a, _, b) ->
      tys_expr (tys_expr acc a) b
  | ETernop (_, a, b, c) | EIf (a, b, c) | EFold (a, b, _, _, c) ->
      tys_expr (tys_expr (tys_expr acc a) b) c
  | ERecord l -> List.fold_left (fun acc (_, e) -> tys_expr acc e) acc l
  | EOptMatch (a, b, _, c) -> tys_expr (tys_expr (tys_expr acc a) b) c

let rec tys_command (acc : type0 list) (c : command) : type0 list =
  match c with
  | CSkip -> acc
  | CSeq (a, b) -> tys_command (tys_command acc a) b
  | CLet (e, _, c) | CLetMut (e, _, c) | CForeach (e, _, c) ->
      tys_command (tys_expr acc e) c
  | CAssign (_, e) -> tys_expr acc e
  | CIf (e, a, b) -> tys_command (tys_command (tys_expr acc e) a) b

(* ---------- per-subject input readers ----------

   One module per subject, with a reader per name its store and environment
   hold.  Two reasons they are emitted rather than written by hand: the
   mapping from a Conquord type to the generated OCaml name is known only
   here, and the expression codegen will need exactly these readers to give
   a program's free names monomorphic types.

   They are also what makes the marshalling TESTABLE rather than merely
   type-correct: compiled/compiled.ml runs them over the generators' own
   workloads. *)

let sanitize_id (s : string) : string =
  let b = Bytes.of_string s in
  Bytes.iteri
    (fun i c ->
       match c with
       | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> ()
       | _ -> Bytes.set b i '_')
    b;
  Bytes.to_string b

let module_name (subject : string) : string =
  let b = Bytes.of_string subject in
  Bytes.iteri
    (fun i c ->
       match c with
       | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> ()
       | _ -> Bytes.set b i '_')
    b;
  let s = Bytes.to_string b in
  "In_" ^ s

let emit_readers () : unit =
  let subjects = ref [] in
  List.iter
    (fun ((subject, gstore), genv) ->
       let names = gstore @ genv in
       let one (n, t) =
         Printf.sprintf "  let %s (v : Value.t) : %s = %s v"
           (field_name n) (ocaml_ty t) (of_expr t) in
       (* a runner that actually CALLS every reader, so that the marshalling
          can be exercised on the generators' own workloads instead of only
          type-checked.  ignore, because what is being tested is that the
          conversion accepts the data, not what it produces -- there is no
          way back yet to compare against. *)
       let call (n, t) =
         (* read it TWICE and check the generated equality agrees.  That
            exercises of_value and eq_ together on real data, which is what
            found the bag and set bugs: a reader that type-checks can still
            be reading the wrong constructor. *)
         Printf.sprintf
           "    (match lookup \"%s\" with\n     | Some v ->\n         let a = %s v and b = %s v in\n         if not (%s a b) then failwith \"%s: re-read differs\"\n     | None -> ());"
           n (field_name n) (field_name n) (eq_of t) n in
       (* The read-twice check above would pass if eq_ always said true.
          This one pins it against the reference: for two workloads, the
          generated equality on the converted values must agree with
          Value.compare on the boxed ones, which exercises BOTH answers. *)
       let cross (n, t) =
         Printf.sprintf
           "    (match l1 \"%s\", l2 \"%s\" with\n     | Some v1, Some v2 ->\n         let got = %s (%s v1) (%s v2) in\n         if got <> (Value.compare v1 v2 = 0) then\n           failwith \"%s: generated equality disagrees with Value.compare\";\n         if got then incr yes else incr no\n     | _ -> ());"
           n n (eq_of t) (field_name n) (field_name n) n in
       (* Stable aliases, so that code written BY HAND against these types --
          the author transcriptions -- names t_queries and t_row rather than
          row23 and row17.  The generated numbering is positional: adding a
          subject renumbers everything, and hand-written code referring to a
          number would break silently on the next run. *)
       let aliases =
         List.map
           (fun (n, t) ->
              Printf.sprintf "  type t_%s = %s" (sanitize_id n) (ocaml_ty t))
           names
         @ (match
              List.find_opt
                (fun ((s, _), _) -> String.equal s subject)
                Extracted.tbl_types_nf
            with
            | Some ((_, TList r), _) | Some ((_, TBag r), _) ->
                [ Printf.sprintf "  type t_row = %s" (ocaml_ty r) ]
            | _ -> []) in
       emit
         (Printf.sprintf
            "module %s = struct\n%s\n%s\n\n  let run (lookup : string -> Value.t option) : unit =\n%s\n    ()\n\n  let cross (l1 : string -> Value.t option) (l2 : string -> Value.t option) (yes : int ref) (no : int ref) : unit =\n%s\n    ()\nend"
            (module_name subject)
            (String.concat "\n" aliases)
            (String.concat "\n" (List.map one names))
            (String.concat "\n" (List.map call names))
            (String.concat "\n" (List.map cross names)));
       subjects := (subject, module_name subject) :: !subjects)
    Extracted.envs_nf;
  (* one registry, so a consumer need not know the module names *)
  emit
    (Printf.sprintf
       "let readers : (string * (((string -> Value.t option) -> unit) * ((string -> Value.t option) -> (string -> Value.t option) -> int ref -> int ref -> unit))) list =\n  [ %s ]"
       (String.concat ";\n    "
          (List.rev_map
             (fun (subject, m) ->
                Printf.sprintf "(\"%s\", (%s.run, %s.cross))" subject m m)
             !subjects)))

(* ---------- the emitted module ---------- *)

let module_text () : string =
  String.concat "\n\n" (List.rev !decls) ^ "\n"

let collect () =
  (* Two sources, and both are needed.  The annotations give every
     collection a program creates; tbl_types gives the table's own record
     before and after the rewrite, which no annotation mentions because
     ERecord carries none -- and which is where the dictionaries live.  The
     documented gap in ty_of_atom fired on the first run, in exactly that
     place, so this is not a precaution. *)
  let tys =
    List.fold_left
      (fun acc ((_, src), opt) -> tys_command (tys_command acc src) opt)
      [] Extracted.annotated_nf in
  let tys =
    List.fold_left
      (fun acc ((_, a), b) -> b :: a :: acc) tys Extracted.tbl_types_nf in
  (* registration order decides declaration order, so this is where the
     dependency order comes from *)
  List.iter (fun t -> ignore (ocaml_ty t)) (List.rev tys);
  let n_rows =
    Hashtbl.fold (fun k _ acc -> if k.[0] = 'K' then acc else acc + 1) names 0 in
  let n_keys = Hashtbl.length names - n_rows in
  (* diagnostic: which annotated atoms are actually present *)
  let nil = ref 0 and non = ref 0 and dict = ref 0 and bag = ref 0
  and set = ref 0 and unannot = ref 0 in
  let count_atom (a : atom) =
    match a with
    | ANil (Some _) -> incr nil
    | ANone (Some _) -> incr non
    | AEmptyDict (_, Some _) -> incr dict
    | AEmptyBag (Some _) -> incr bag
    | AEmptySet (Some _) -> incr set
    | ANil None | ANone None | AEmptyDict (_, None)
    | AEmptyBag None | AEmptySet None -> incr unannot
    | _ -> () in
  let rec ce (e : expr) = match e with
    | EVar _ | ELoc _ -> ()
    | EAtom a -> count_atom a
    | EUnop (_, e) | EACFold (_, e) | EACIFold (_, e) | EAccess (e, _)
    | ESort (_, e) -> ce e
    | EBinop (_, a, b) | ELet (a, _, b) | EFlatmap (_, a, _, b) -> ce a; ce b
    | ETernop (_, a, b, c) | EIf (a, b, c) | EFold (a, b, _, _, c) -> ce a; ce b; ce c
    | ERecord l -> List.iter (fun (_, e) -> ce e) l
    | EOptMatch (a, b, _, c) -> ce a; ce b; ce c in
  let rec cc (c : command) = match c with
    | CSkip -> ()
    | CSeq (a, b) -> cc a; cc b
    | CLet (e, _, c) | CLetMut (e, _, c) | CForeach (e, _, c) -> ce e; cc c
    | CAssign (_, e) -> ce e
    | CIf (e, a, b) -> ce e; cc a; cc b in
  List.iter (fun ((_, src), opt) -> cc src; cc opt) Extracted.annotated_nf;
  Printf.eprintf
    "annotated atoms: nil=%d none=%d dict=%d bag=%d set=%d | UNANNOTATED=%d\n"
    !nil !non !dict !bag !set !unannot;
  Printf.eprintf
    "%d distinct types collected, %d record types, %d key modules, %d declarations\n"
    (List.length tys) n_rows n_keys (List.length !decls);
  ()

let run () =
  collect ();
  emit_readers ();
  print_string
    ("(* Generated by harness/mono.ml from the annotated subject terms.\n\
     \   Do not edit by hand. *)\n\n" ^ module_text ())
