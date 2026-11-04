(* Expressions and commands, compiled.

   TYPE-DIRECTED, which is why eval/Elaborate.v had to come first: picking a
   record layout, an unboxed scalar or a structure needs the type at every
   node.  Annotations give the collections a program creates; everything else
   is asked of Extracted.synth -- the development's OWN typechecker, extracted
   rather than reimplemented, because a second synthesizer would drift and the
   gap would be invisible (a wrong type compiles and computes the wrong
   thing).

   WHAT IS CHARGED, and what is deliberately not.  The generated code charges
   the counters that CROSS to hand-written code -- comparisons, hashing,
   string bytes -- through rt.ml, and `rows` wherever eval.ml charges
   Count.visit, because rows is the exponent instrument and has to mean the
   same thing on both sides.  It charges neither `steps` nor `overhead`:
   those are the interpreter's own dispatch and its environment lookups, and
   compiled code has neither.  Nor `fields`: a monomorphic record has its
   fields at constant offsets, so that work does not happen rather than going
   uncounted.

   ONE OPEN QUESTION, recorded rather than silently decided.  eval.ml charges
   OLength and ODictValues to Count.walk, which lands in `steps` and so does
   not cross -- but a compiled backend walking a stored list to count it is
   doing real work.  This file follows eval.ml exactly (visit where it
   visits, nothing where it walks) so the two sides' `rows` stay comparable;
   whether `walk` on a STORED collection should cross is a cost-model
   question, not a codegen one.

   Coverage is reported rather than assumed: anything unimplemented raises
   Unsupported, and `main.exe codegen` prints what is still missing, per
   subject and per construct. *)

open Extracted

exception Unsupported of string

let unsupported (what : string) = raise (Unsupported what)

type ctx = {
  store : (string * type0) list;
  env : (string * type0) list;
}

let ty_of (c : ctx) (e : expr) : type0 =
  match Extracted.synth c.store c.env e with
  | Success (t, _) -> t
  | Failure _ -> unsupported "type synthesis failed"

let elem_of (t : type0) : type0 =
  match t with
  | TList e | TBag e | TSet e -> e
  | _ -> unsupported "expected a collection type"

(* OCaml identifiers from Conquord names, by the same mangling mono.ml uses
   for fields so that the two agree on what is a legal name *)
let sanitize (s : string) : string =
  let b = Bytes.of_string s in
  Bytes.iteri
    (fun i c ->
       match c with
       | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> ()
       | _ -> Bytes.set b i '_')
    b;
  Bytes.to_string b

let var (x : string) : string = "v_" ^ sanitize x

(* Every generated binder is annotated.  Field names are shared across the
   generated records -- f_kind occurs in several -- and OCaml resolves an
   unqualified field to the LAST record type that declares it, so an
   un-annotated binder silently takes an unrelated type and the error
   surfaces far from its cause.  Annotating makes each binder's type the
   one the TYPE SYSTEM gave it. *)
let binder (x : string) (t : type0) : string =
  Printf.sprintf "(%s : %s)" (var x) (Mono.ocaml_ty t)
let loc (x : string) : string = "r_" ^ sanitize x

let paren (s : string) : string = "(" ^ s ^ ")"

(* ---------- expressions ---------- *)

let rec gen (c : ctx) (e : expr) : string =
  match e with
  | EVar x -> var x
  | ELoc x -> "!" ^ loc x
  | EAtom a -> atom a
  | EUnop (o, a) -> unop c o a
  | EBinop (o, a, b) -> binop c o a b
  | ETernop (o, a, b, d) -> ternop c o a b d
  | EIf (a, b, d) ->
      paren (Printf.sprintf "if %s then %s else %s" (gen c a) (gen c b) (gen c d))
  | ELet (a, x, b) ->
      let t = ty_of c a in
      paren
        (Printf.sprintf "let %s = %s in %s" (binder x t) (gen c a)
           (gen { c with env = (x, t) :: c.env } b))
  | EFlatmap (tag, a, x, b) -> flatmap c tag a x b
  | EFold (a, seed, x, acc, body) ->
      let et = elem_of (ty_of c a) and st = ty_of c seed in
      let c' = { c with env = (acc, st) :: (x, et) :: c.env } in
      paren
        (Printf.sprintf
           "(let l = %s in Count.visit (List.length l); List.fold_right (fun %s %s -> %s) l %s)"
           (gen c a) (binder x et) (binder acc st) (gen c' body) (gen c seed))
  | EACFold (AGCount, a) ->
      paren
        (Printf.sprintf "(let l = %s in Count.visit (List.length l); List.length l)"
           (gen c a))
  | EACFold (AGSum, a) ->
      paren
        (Printf.sprintf
           "(let l = %s in Count.visit (List.length l); List.fold_left (fun acc x -> Rt.add_int acc x) 0 l)"
           (gen c a))
  | EACIFold (AGMin, a) -> aci c "min" a
  | EACIFold (AGMax, a) -> aci c "max" a
  | EACIFold (AGIntersect, a) -> aci c "intersect" a
  | EACIFold (AGUnion, a) -> aci c "union" a
  | ERecord l ->
      let t = ty_of c (ERecord l) in
      let fields = match t with TRecord fl -> fl | _ -> unsupported "ERecord" in
      (* a record type with no fields is unit on the OCaml side, so its
         literal is () and not an empty brace pair *)
      if fields = [] then "()"
      else
      (* the emitted record's fields are in the TYPE's order, which the type
         system keeps name-sorted; the term's order need not match *)
      (* annotated for the same reason binders are: a literal's type is
         resolved from its first field name, which several records share *)
      paren
        (Printf.sprintf "({ %s } : %s)"
           (String.concat "; "
              (List.map
                 (fun (f, _) ->
                    match List.assoc_opt f l with
                    | Some fe ->
                        Printf.sprintf "%s = %s" (Mono.field_name f) (gen c fe)
                    | None -> unsupported ("ERecord missing field " ^ f))
                 fields))
           (Mono.ocaml_ty t))
  | EAccess (a, f) -> paren (Printf.sprintf "%s.%s" (gen c a) (Mono.field_name f))
  | EOptMatch (a, none, x, some) ->
      let it =
        match ty_of c a with TOption i -> i | _ -> unsupported "EOptMatch" in
      paren
        (Printf.sprintf "(match %s with None -> %s | Some %s -> %s)" (gen c a)
           (gen c none) (binder x it)
           (gen { c with env = (x, it) :: c.env } some))
  | ESort (_, a) ->
      let et = elem_of (ty_of c a) in
      paren
        (Printf.sprintf
           "(let l = %s in Count.visit (List.length l); List.stable_sort %s l)"
           (gen c a) (Mono.cmp_of et))

and atom (a : atom) : string =
  match a with
  | AInt n -> paren (string_of_int n)
  | ABool b -> if b then "true" else "false"
  | AString s -> Printf.sprintf "%S" s
  | ANil _ -> "[]"
  | ANone _ -> "None"
  | AUnit -> "()"
  | AEmptyBag _ -> "[]"
  | AEmptySet (Some t) -> Mono.key_module t ^ "_Set.empty"
  | AEmptyDict (Ranged, Some (k, _)) -> Mono.key_module k ^ "_Map.empty"
  | AEmptyDict (Unranged, Some (k, _)) -> Mono.key_module k ^ "_Tbl.empty"
  | AEmptySet None | AEmptyDict (_, None) -> unsupported "unannotated atom"

and unop (c : ctx) (o : unop) (a : expr) : string =
  let g = gen c a in
  match o with
  | ONeg -> paren ("- " ^ g)
  | ONot -> paren ("not " ^ g)
  | OSome -> paren ("Some " ^ g)
  | OLength -> paren ("List.length " ^ g)
  | OLengthString -> paren ("String.length " ^ g)
  | OStringOfInt -> paren ("Rt.string_of_int_c " ^ g)
  | OBagOfList ->
      (* a bag is a list, so this is where the ORDER stops being observable
         and nothing else -- eval.ml charges the rows it visits *)
      paren (Printf.sprintf "(let l = %s in Count.visit (List.length l); l)" g)
  | OSetOfList ->
      let m = Mono.key_module (elem_of (ty_of c a)) ^ "_Set" in
      paren
        (Printf.sprintf
           "(let l = %s in Count.visit (List.length l); List.fold_left (fun s x -> %s.add x s) %s.empty l)"
           g m m)
  | OSetOfBag ->
      let m = Mono.key_module (elem_of (ty_of c a)) ^ "_Set" in
      paren
        (Printf.sprintf
           "(let l = %s in Count.visit (List.length l); List.fold_left (fun s x -> %s.add x s) %s.empty l)"
           g m m)
  | OSetSize -> paren (Mono.key_module (elem_of (ty_of c a)) ^ "_Set.cardinal " ^ g)
  | ODictValues -> dict_values c a
  | OTrigrams -> paren ("Rt.trigrams " ^ g)
  | ODictMinKey -> unsupported "ODictMinKey"

and dict_values (c : ctx) (a : expr) : string =
  match ty_of c a with
  | TDict (Ranged, k, _) ->
      paren
        (Printf.sprintf
           "(%s_Map.fold (fun _ v acc -> Count.visit 1; v :: acc) %s [])"
           (Mono.key_module k) (gen c a))
  | TDict (Unranged, k, _) ->
      paren
        (Printf.sprintf
           "(%s_Tbl.fold ~f:(fun acc _ v -> Count.visit 1; v :: acc) ~x:[] %s)"
           (Mono.key_module k) (gen c a))
  | _ -> unsupported "ODictValues on a non-dictionary"

and aci (c : ctx) (which : string) (a : expr) : string =
  (* An aci aggregate folds a SET with an operation that is associative,
     commutative and idempotent, so the order the structure hands elements
     over in cannot change the answer and is not paid for.  The result is an
     option: None on the empty set, which is the seed the aggregate saves
     against the fold of the binop it replaces.

     CHARGING.  eval.ml charges these to Count.walk, which lands in `steps`
     and does not cross to hand-written code.  So the generated code charges
     nothing here -- and for min and max that is not a shortcut but the
     representation difference: eval.ml materialises the elements and folds,
     where a tree answers with a leftmost descent that iterates no stored
     elements and compares no keys. *)
  let et = elem_of (ty_of c a) in
  let m = Mono.key_module et ^ "_Set" in
  match which with
  | "min" -> paren (Printf.sprintf "%s.min_elt_opt %s" m (gen c a))
  | "max" -> paren (Printf.sprintf "%s.max_elt_opt %s" m (gen c a))
  | "union" | "intersect" ->
      (* the elements are themselves sets, so the inner module is the one
         that combines them *)
      let im =
        match et with
        | TSet ie -> Mono.key_module ie ^ "_Set"
        | _ -> unsupported ("EACIFold/" ^ which ^ " over a non-set") in
      let op = if which = "union" then "union" else "inter" in
      paren
        (Printf.sprintf
           "(%s.fold (fun (e : %s.t) acc -> match acc with None -> Some e | Some a -> Some (%s.%s e a)) %s None)"
           m im im op (gen c a))
  | _ -> unsupported ("EACIFold/" ^ which)

and flatmap (c : ctx) (tag : collection_tag) (a : expr) (x : string) (b : expr)
    : string =
  let at = ty_of c a in
  let et = elem_of at in
  let c' = { c with env = (x, et) :: c.env } in
  match tag with
  | LikeList | LikeBag ->
      paren
        (Printf.sprintf
           "(let l = %s in Count.visit (List.length l); List.concat_map (fun %s -> %s) l)"
           (gen c a) (binder x et) (gen c' b))
  | LikeSet ->
      let em = Mono.key_module et ^ "_Set" in
      let rm = Mono.key_module (elem_of (ty_of c' b)) ^ "_Set" in
      paren
        (Printf.sprintf
           "(Count.visit (%s.cardinal %s); %s.fold (fun %s acc -> %s.union acc %s) %s %s.empty)"
           em (gen c a) em (binder x et) rm (gen c' b) (gen c a) rm)

and binop (c : ctx) (o : binop) (a : expr) (b : expr) : string =
  let ga () = gen c a and gb () = gen c b in
  match o with
  | OPlus -> paren (Printf.sprintf "Rt.add_int %s %s" (ga ()) (gb ()))
  | OMinus -> paren (Printf.sprintf "Rt.sub_int %s %s" (ga ()) (gb ()))
  | OTimes -> paren (Printf.sprintf "Rt.mul_int %s %s" (ga ()) (gb ()))
  | ODiv -> paren (Printf.sprintf "Rt.div_int %s %s" (ga ()) (gb ()))
  | OMod -> paren (Printf.sprintf "Rt.mod_int %s %s" (ga ()) (gb ()))
  | OAnd -> paren (Printf.sprintf "(%s && %s)" (ga ()) (gb ()))
  | OOr -> paren (Printf.sprintf "(%s || %s)" (ga ()) (gb ()))
  | OCons -> paren (Printf.sprintf "(%s :: %s)" (ga ()) (gb ()))
  | OBagInsert -> paren (Printf.sprintf "(%s :: %s)" (gb ()) (ga ()))
  | OConcat ->
      paren
        (Printf.sprintf "(let l = %s in Count.visit (List.length l); l @ %s)"
           (ga ()) (gb ()))
  | OConcatString -> paren (Printf.sprintf "Rt.concat_string %s %s" (ga ()) (gb ()))
  | OLess -> paren (Printf.sprintf "(Rt.cmp_int %s %s < 0)" (ga ()) (gb ()))
  | OEq -> paren (Printf.sprintf "%s %s %s" (Mono.eq_of (ty_of c a)) (ga ()) (gb ()))
  | OStrContains -> paren (Printf.sprintf "Rt.str_contains %s %s" (ga ()) (gb ()))
  | OWords -> paren (Printf.sprintf "Rt.words %s %s" (ga ()) (gb ()))
  | OSetInsert ->
      let m = Mono.key_module (elem_of (ty_of c a)) ^ "_Set" in
      paren (Printf.sprintf "%s.add %s %s" m (gb ()) (ga ()))
  | OSetMem ->
      let m = Mono.key_module (elem_of (ty_of c a)) ^ "_Set" in
      paren (Printf.sprintf "%s.mem %s %s" m (gb ()) (ga ()))
  | OSetUnion | OSetIntersect | OSetDiff ->
      let m = Mono.key_module (elem_of (ty_of c a)) ^ "_Set" in
      let f =
        match o with
        | OSetUnion -> "union"
        | OSetIntersect -> "inter"
        | _ -> "diff" in
      paren (Printf.sprintf "%s.%s %s %s" m f (ga ()) (gb ()))
  | OLookup -> lookup c a b
  | ODelete -> delete c a b
  | OBagDiff -> unsupported "OBagDiff"
  | ORange -> unsupported "ORange"

and lookup (c : ctx) (a : expr) (b : expr) : string =
  match ty_of c a with
  | TDict (Ranged, k, _) ->
      paren (Printf.sprintf "%s_Map.find_opt %s %s" (Mono.key_module k) (gen c b) (gen c a))
  | TDict (Unranged, k, _) ->
      paren (Printf.sprintf "%s_Tbl.get %s %s" (Mono.key_module k) (gen c b) (gen c a))
  | _ -> unsupported "OLookup on a non-dictionary"

and delete (c : ctx) (a : expr) (b : expr) : string =
  match ty_of c a with
  | TDict (Ranged, k, _) ->
      paren (Printf.sprintf "%s_Map.remove %s %s" (Mono.key_module k) (gen c b) (gen c a))
  | TDict (Unranged, k, _) ->
      paren (Printf.sprintf "%s_Tbl.remove %s %s" (Mono.key_module k) (gen c b) (gen c a))
  | _ -> unsupported "ODelete on a non-dictionary"

and ternop (c : ctx) (o : ternop) (a : expr) (b : expr) (d : expr) : string =
  match o with
  | OInsert -> (
      match ty_of c a with
      | TDict (Ranged, k, _) ->
          paren
            (Printf.sprintf "%s_Map.add %s %s %s" (Mono.key_module k) (gen c b)
               (gen c d) (gen c a))
      | TDict (Unranged, k, _) ->
          paren
            (Printf.sprintf "%s_Tbl.add %s %s %s" (Mono.key_module k) (gen c b)
               (gen c d) (gen c a))
      | _ -> unsupported "OInsert on a non-dictionary")
  (* Both range operators are emitted INLINE rather than through rt.ml,
     because Map.split lives on the specific module and the module is known
     here.  Half-open [lo, hi) with optional bounds, as eval.ml's split_lo
     and split_hi do -- and a split costs a path rather than a traversal,
     which is the whole reason TyODictRange is pinned at TDict Ranged. *)
  | ODictRange -> (
      match ty_of c a with
      | TDict (Ranged, k, _) ->
          let m = Mono.key_module k ^ "_Map" in
          paren
            (Printf.sprintf
               "(let d = %s in\n   let d = (match %s with Some l -> let _, at, above = %s.split l d in (match at with None -> above | Some v -> %s.add l v above) | None -> d) in\n   (match %s with Some h -> let below, _, _ = %s.split h d in below | None -> d))"
               (gen c a) (gen c b) m m (gen c d) m)
      | _ -> unsupported "ODictRange on an unordered dictionary")
  | ODictRangeDelete -> (
      match ty_of c a with
      | TDict (Ranged, k, _) ->
          (* everything the range leaves out: the keys below lo together with
             those at or above hi.  Key-disjoint, so the union never chooses. *)
          let m = Mono.key_module k ^ "_Map" in
          paren
            (Printf.sprintf
               "(let d = %s in\n   let below = (match %s with Some l -> let b, _, _ = %s.split l d in b | None -> %s.empty) in\n   let above = (match %s with Some h -> let _, at, aa = %s.split h d in (match at with None -> aa | Some v -> %s.add h v aa) | None -> %s.empty) in\n   %s.union (fun _ v _ -> Some v) below above)"
               (gen c a) (gen c b) m m (gen c d) m m m m)
      | _ -> unsupported "ODictRangeDelete on an unordered dictionary")
  | OSubstring -> unsupported "OSubstring"

(* ---------- commands ---------- *)

let rec gen_cmd (c : ctx) (k : command) : string =
  match k with
  | CSkip -> "()"
  | CSeq (a, b) -> Printf.sprintf "(%s);\n  (%s)" (gen_cmd c a) (gen_cmd c b)
  | CLet (e, x, body) ->
      let t = ty_of c e in
      Printf.sprintf "let %s = %s in\n  %s" (binder x t) (gen c e)
        (gen_cmd { c with env = (x, t) :: c.env } body)
  | CLetMut (e, x, body) ->
      (* a mutable binding is a ref, and the shadowing IS the restoration
         CLetMut performs on the way out *)
      let t = ty_of c e in
      Printf.sprintf "let (%s : %s ref) = ref (%s) in\n  %s" (loc x)
        (Mono.ocaml_ty t) (gen c e)
        (gen_cmd { c with store = (x, t) :: c.store } body)
  | CAssign (x, e) -> Printf.sprintf "%s := %s" (loc x) (gen c e)
  | CIf (e, a, b) ->
      Printf.sprintf "(if %s then (%s) else (%s))" (gen c e) (gen_cmd c a)
        (gen_cmd c b)
  | CForeach (e, x, body) ->
      let et = elem_of (ty_of c e) in
      Printf.sprintf
        "(let l = %s in Count.visit (List.length l);\n   List.iter (fun %s -> %s) l)"
        (gen c e) (binder x et)
        (gen_cmd { c with env = (x, et) :: c.env } body)

(* ---------- one function per subject column ---------- *)

let fname (prefix : string) (subject : string) : string =
  prefix ^ "_" ^ sanitize subject

let gen_subject (prefix : string) (subject : string)
    (store : (string * type0) list) (env : (string * type0) list)
    (k : command) : string * string option =
  let c = { store; env } in
  let params =
    List.map
      (fun (n, t) -> Printf.sprintf "(%s : %s ref)" (loc n) (Mono.ocaml_ty t))
      store
    @ List.map
        (fun (n, t) -> Printf.sprintf "(%s : %s)" (var n) (Mono.ocaml_ty t))
        env in
  let head =
    Printf.sprintf "let %s %s : unit =" (fname prefix subject)
      (String.concat " " params) in
  match gen_cmd c k with
  | body -> (Printf.sprintf "%s\n  %s" head body, None)
  | exception Unsupported why ->
      (* a stub, so the module still compiles and the gap is REPORTED rather
         than stopping everything behind it *)
      ( Printf.sprintf "%s\n  ignore (%s);\n  failwith %S" head
          (String.concat ", " (List.map (fun (n, _) -> loc n) store
                               @ List.map (fun (n, _) -> var n) env))
          ("unsupported: " ^ why),
        Some why )

(* ---------- running them, and the check that they agree ----------

   bench.ml's store comparison is the one check that comes free with a
   measurement: the source and the optimized program must leave the same
   store on every input, so each agreement is a concrete witness of that
   subject's soundness theorem on that input.  The compiled side can make
   the same check against itself, and it needs nothing from the interpreter
   to do it -- the inputs are marshalled once, each column runs on its own
   fresh refs, and the generated equality decides.

   Both columns are given the SAME converted inputs, so a difference cannot
   come from the conversion. *)

let runners : string list ref = ref []

(* One entry point per column, so a measurement times exactly one program.
   The inputs are converted FIRST and what is returned is a closure, so that
   marshalling -- which is not work the program implies -- happens before the
   clock starts and before Count.reset.  The refs are created INSIDE the
   closure, so repeating a measurement repeats the program and not a mutated
   leftover. *)
let emit_runner (prefix : string) (subject : string)
    (store : (string * type0) list) (env : (string * type0) list) : unit =
  let m = Mono.module_name subject in
  let inputs =
    List.map
      (fun (n, _) ->
         Printf.sprintf "  let %s_in = %s.%s (get %S) in" (var n) m
           (Mono.field_name n) n)
      env in
  let seeds =
    List.map
      (fun (n, _) ->
         Printf.sprintf "  let %s_in = %s.%s (get %S) in" (loc n) m
           (Mono.field_name n) n)
      store in
  let refs =
    List.map
      (fun (n, _) -> Printf.sprintf "    let %s = ref %s_in in" (loc n) (loc n))
      store in
  let args =
    String.concat " "
      (List.map (fun (n, _) -> loc n) store
       @ List.map (fun (n, _) -> Printf.sprintf "%s_in" (var n)) env) in
  runners :=
    Printf.sprintf
      "let prepared_%s_%s (lookup : string -> Value.t option) : unit -> unit =\n  let get n = match lookup n with Some v -> v | None -> failwith (\"missing input \" ^ n) in\n%s\n%s\n  fun () ->\n%s\n    %s %s"
      prefix (sanitize subject)
      (String.concat "\n" inputs)
      (String.concat "\n" seeds)
      (String.concat "\n" refs)
      (fname prefix subject) args
    :: !runners

let stores : string list ref = ref []

(* A typed getter for a column's final store, so that code written BY HAND --
   an author transcription -- has something to be checked against.  Returns
   the store names as a tuple, in the order the envs list gives them, so the
   type is determined and no conversion back to a boxed value is needed. *)
let emit_store (prefix : string) (subject : string)
    (store : (string * type0) list) (env : (string * type0) list) : unit =
  let m = Mono.module_name subject in
  let inputs =
    List.map
      (fun (n, _) ->
         Printf.sprintf "  let %s_in = %s.%s (get %S) in" (var n) m
           (Mono.field_name n) n)
      env in
  let refs =
    List.map
      (fun (n, _) ->
         Printf.sprintf "  let %s = ref (%s.%s (get %S)) in" (loc n) m
           (Mono.field_name n) n)
      store in
  let args =
    String.concat " "
      (List.map (fun (n, _) -> loc n) store
       @ List.map (fun (n, _) -> Printf.sprintf "%s_in" (var n)) env) in
  let ret =
    match store with
    | [] -> "()"
    | l -> "(" ^ String.concat ", " (List.map (fun (n, _) -> "!" ^ loc n) l) ^ ")" in
  let rty =
    match store with
    | [] -> "unit"
    | l -> "(" ^ String.concat " * " (List.map (fun (_, t) -> Mono.ocaml_ty t) l) ^ ")" in
  stores :=
    Printf.sprintf
      "let store_%s_%s (lookup : string -> Value.t option) : %s =\n  let get n = match lookup n with Some v -> v | None -> failwith (\"missing input \" ^ n) in\n%s\n%s\n  %s %s;\n  %s"
      prefix (sanitize subject) rty
      (String.concat "\n" inputs)
      (String.concat "\n" refs)
      (fname prefix subject) args ret
    :: !stores

let agrees : string list ref = ref []

let emit_agree (subject : string) (store : (string * type0) list)
    (env : (string * type0) list) : unit =
  let m = Mono.module_name subject in
  let fresh side (n, _) =
    Printf.sprintf "  let %s_%s = ref (%s.%s (get %S)) in" (loc n) side m
      (Mono.field_name n) n in
  let args side =
    String.concat " "
      (List.map (fun (n, _) -> Printf.sprintf "%s_%s" (loc n) side) store
       @ List.map (fun (n, _) -> Printf.sprintf "%s_in" (var n)) env) in
  let inputs =
    List.map
      (fun (n, _) ->
         Printf.sprintf "  let %s_in = %s.%s (get %S) in" (var n) m
           (Mono.field_name n) n)
      env in
  let cmp =
    match store with
    | [] -> "  true"
    | l ->
        "  "
        ^ String.concat "\n  && "
            (List.map
               (fun (n, t) ->
                  Printf.sprintf "%s !%s_a !%s_b" (Mono.eq_of t) (loc n) (loc n))
               l) in
  agrees := (Printf.sprintf
       "let agree_%s (lookup : string -> Value.t option) : bool =\n  let get n = match lookup n with Some v -> v | None -> failwith (\"missing input \" ^ n) in\n%s\n%s\n%s\n  %s %s;\n%s\n  %s %s;\n%s"
       (sanitize subject)
       (String.concat "\n" inputs)
       (String.concat "\n" (List.map (fresh "a") store))
       (String.concat "\n" (List.map (fresh "b") store))
       (fname "src" subject) (args "a")
       "" (fname "opt" subject) (args "b") cmp)
    :: !agrees

(* And the definitive one: the compiled optimized column against the
   INTERPRETER, on the same program and the same input.

   src = opt says the two compiled columns agree with each other, which a
   codegen that dropped the same work from both would also satisfy.  This
   says the compiled program computes what Interpret.v's transcription
   computes -- so a vacuous backend, or one that mis-ordered a fold, fails
   here and nowhere earlier. *)

let interps : string list ref = ref []

let emit_vs_interp (subject : string) (store : (string * type0) list)
    (env : (string * type0) list) : unit =
  let m = Mono.module_name subject in
  let inputs =
    List.map
      (fun (n, _) ->
         Printf.sprintf "  let %s_in = %s.%s (get %S) in" (var n) m
           (Mono.field_name n) n)
      env in
  let refs =
    List.map
      (fun (n, _) ->
         Printf.sprintf "  let %s = ref (%s.%s (get %S)) in" (loc n) m
           (Mono.field_name n) n)
      store in
  let args =
    String.concat " "
      (List.map (fun (n, _) -> loc n) store
       @ List.map (fun (n, _) -> Printf.sprintf "%s_in" (var n)) env) in
  let cmp =
    match store with
    | [] -> "  true"
    | l ->
        "  "
        ^ String.concat "\n  && "
            (List.map
               (fun (n, t) ->
                  Printf.sprintf "%s !%s (%s.%s (iget %S))" (Mono.eq_of t)
                    (loc n) m (Mono.field_name n) n)
               l) in
  interps :=
    Printf.sprintf
      "let vs_interp_%s (lookup : string -> Value.t option) (iget : string -> Value.t) : bool =\n  let get n = match lookup n with Some v -> v | None -> failwith (\"missing input \" ^ n) in\n%s\n%s\n  %s %s;\n%s"
      (sanitize subject)
      (String.concat "\n" inputs)
      (String.concat "\n" refs)
      (fname "opt" subject) args cmp
    :: !interps

let run () =
  (* the type declarations first, which is also what registers every type the
     subject functions below will name *)
  Mono.collect ();
  let missing = ref [] in
  let fns =
    List.filter_map
      (fun ((subject, src), opt) ->
         match
           List.find_opt
             (fun ((n, _), _) -> String.equal n subject)
             Extracted.envs_nf
         with
         | None -> None
         | Some ((_, store), env) ->
             let a, wa = gen_subject "src" subject store env src in
             let b, wb = gen_subject "opt" subject store env opt in
             List.iter
               (fun w ->
                  match w with
                  | Some why -> missing := (subject, why) :: !missing
                  | None -> ())
               [ wa; wb ];
             emit_runner "src" subject store env;
             emit_runner "opt" subject store env;
             emit_store "src" subject store env;
             emit_store "opt" subject store env;
             emit_agree subject store env;
             emit_vs_interp subject store env;
             Some (a ^ "\n\n" ^ b))
      Extracted.annotated_nf in
  Mono.emit_readers ();
  let registry =
    Printf.sprintf
      "let agreements : (string * ((string -> Value.t option) -> bool)) list =\n  [ %s ]"
      (String.concat ";\n    "
         (List.map
            (fun ((subject, _), _) ->
               Printf.sprintf "(%S, agree_%s)" subject (sanitize subject))
            Extracted.annotated_nf)) in
  print_string
    ("(* Generated by harness/codegen.ml from the annotated subject terms.\n\
     \   Do not edit by hand. *)\n\n" ^ Mono.module_text () ^ "\n"
    ^ String.concat "\n\n" fns ^ "\n\n"
    ^ String.concat "\n\n" (List.rev !runners) ^ "\n\n"
    ^ String.concat "\n\n" (List.rev !stores) ^ "\n\n"
    ^ String.concat "\n\n" (List.rev !agrees) ^ "\n\n"
    ^ String.concat "\n\n" (List.rev !interps) ^ "\n\n" ^ registry ^ "\n\n"
    ^ Printf.sprintf
        "let vs_interps : (string * ((string -> Value.t option) -> (string -> Value.t) -> bool)) list =\n  [ %s ]\n"
        (String.concat ";\n    "
           (List.map
              (fun ((subject, _), _) ->
                 Printf.sprintf "(%S, vs_interp_%s)" subject (sanitize subject))
              Extracted.annotated_nf))
    ^ Printf.sprintf
        "\n\nlet programs : (string * (((string -> Value.t option) -> unit -> unit) * ((string -> Value.t option) -> unit -> unit))) list =\n  [ %s ]\n"
        (String.concat ";\n    "
           (List.map
              (fun ((subject, _), _) ->
                 Printf.sprintf "(%S, (prepared_src_%s, prepared_opt_%s))" subject
                   (sanitize subject) (sanitize subject))
              Extracted.annotated_nf)));
  let n = List.length Extracted.annotated_nf in
  Printf.eprintf "codegen: %d subjects, %d columns, %d unsupported\n" n (2 * n)
    (List.length !missing);
  let tally : (string, int) Hashtbl.t = Hashtbl.create 16 in
  List.iter
    (fun (_, why) ->
       Hashtbl.replace tally why (1 + Option.value ~default:0 (Hashtbl.find_opt tally why)))
    !missing;
  Hashtbl.iter (fun why k -> Printf.eprintf "  %-44s %d\n" why k) tally
