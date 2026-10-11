From fiat2 Require Import Language Value.
From Stdlib Require Import String ZArith List Ascii BinaryString.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition paren (s:string) : string :=
  "(" ++ s ++ ")".

Definition brace (s:string) : string :=
  "{" ++ s ++ "}".

Definition bracket (s:string) : string :=
  "[" ++ s ++ "]".

Fixpoint join (sep:string) (l:list string) : string :=
  match l with
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ join sep xs
  end.

Definition bool_py (b : bool) :=
  if b then "True" else "False".

Definition ascii_of_digit (d : Z) : ascii :=
  Ascii.ascii_of_nat (Z.to_nat (48 + d)).

Fixpoint string_of_digits (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | d :: tl =>
      String (ascii_of_digit d) (string_of_digits tl)
  end.

Definition Z_py : Z -> string := of_Z.

Definition atom_py (a : atom) : string :=
  match a with
  | AWord n => Z_py n
  | AInt n => Z_py n
  | ABool b => bool_py b
  | AString s => """" ++ s ++ """"
  | ANil _ => "[]"
  | ANone _ => "None"
  | AEmptyDict _ => "{}"
  | AEmptyBag _ => "[]"
  | AEmptySet _ => "[]"
  | AUnit => "None"
  end.

Definition unop_py (o:unop) (e:string) : string :=
  match o with
  | OWNeg => paren ("-" ++ e)
  | ONeg => paren ("-" ++ e)
  | ONot => paren ("not " ++ e)
  | OLength => "len(" ++ e ++ ")"
  | OLengthString => "len(" ++ e ++ ")"
  | OIntToString => "str(" ++ e ++ ")"
  | OSome => e
  | ODictValues => "list(" ++ e ++ ".values())"
  end.

Definition binop_py (o:binop) (e1 e2:string) : string :=
  match o with
  | OWPlus | OPlus => paren (e1 ++ " + " ++ e2)
  | OWMinus | OMinus => paren (e1 ++ " - " ++ e2)
  | OWTimes | OTimes => paren (e1 ++ " * " ++ e2)
  | OWDivU | OWDivS | ODiv => paren (e1 ++ " // " ++ e2)
  | OWModU | OWModS | OMod => paren (e1 ++ " % " ++ e2)
  | OAnd => paren (e1 ++ " and " ++ e2)
  | OOr => paren (e1 ++ " or " ++ e2)
  | OConcat => paren (e1 ++ " + " ++ e2)
  | OConcatString => paren (e1 ++ " + " ++ e2)
  | OWLessU | OWLessS | OLess => paren (e1 ++ " < " ++ e2)
  | OEq => paren (e1 ++ " == " ++ e2)
  | OCons => paren ("[" ++ e1 ++ "] + " ++ e2)
  | ORange | OWRange => "list(range(" ++ e1 ++ "," ++ e2 ++ "))"
  | OBagInsert => paren ("[" ++ e2 ++ "]" ++ " + " ++ e1)
  | OSetInsert => paren ("[" ++ e2 ++ "]" ++ " + " ++ e1)
  (* | OSetInsert => paren ("{" ++ e2 ++ "}" ++ " | " ++ e1) *)
  (* sets are Python lists, since their elements may be unhashable dicts;
     the lambdas evaluate each operand once *)
  | OSetUnion => "(lambda s1, s2: s1 + [v for v in s2 if v not in s1])(" ++ e1 ++ ", " ++ e2 ++ ")"
  | OSetIntersect => "(lambda s1, s2: [v for v in s1 if v in s2])(" ++ e1 ++ ", " ++ e2 ++ ")"
  | OSetDiff => "(lambda s1, s2: [v for v in s1 if v not in s2])(" ++ e1 ++ ", " ++ e2 ++ ")"
  | OSetMem => paren (e2 ++ " in " ++ e1)
  | OStrContains => paren (e2 ++ " in " ++ e1)
  | OLookup => e1 ++ ".get(" ++ e2 ++ ")"
  | ODelete =>
      "{k:v for k,v in " ++ e1 ++ ".items() if k != " ++ e2 ++ "}"
  end.

Fixpoint expr_py (e:expr) : string :=
  match e with
  | EVar x => x
  | ELoc x => x
  | EAtom a =>
      atom_py a
  | EUnop o e1 =>
      unop_py o (expr_py e1)
  | EBinop o e1 e2 =>
      binop_py o (expr_py e1) (expr_py e2)
  | ETernop ODictRange e1 e2 e3 =>
      (* linear in the number of keys; an ordered map would make this logarithmic *)
      "(lambda d, lo, hi: {k: v for k, v in d.items() if lo <= k < hi})(" ++ expr_py e1 ++ ", " ++ expr_py e2 ++ ", " ++ expr_py e3 ++ ")"
  | ETernop OSubstring e1 e2 e3 =>
      (* negative start or length count as 0, as in the semantics *)
      "(lambda s, i, n: s[i:i+n])(" ++ expr_py e1 ++ ", max(" ++ expr_py e2 ++ ", 0), max(" ++ expr_py e3 ++ ", 0))"
  | ETernop OInsert e1 e2 e3 =>
      paren (expr_py e1 ++ " | {" ++
             expr_py e2 ++ ":" ++
             expr_py e3 ++ "}")
  | EIf e1 e2 e3 =>
      paren (expr_py e2 ++
             " if " ++ expr_py e1 ++
             " else " ++ expr_py e3)
  | ELet e1 x e2 =>
      paren ("(lambda " ++ x ++ ": " ++
             expr_py e2 ++ ")(" ++
             expr_py e1 ++ ")")
  | EFlatmap _ e1 x e2 =>
      (* Print the flatmap as one comprehension: a singleton body gives the result
         expression, an "if" whose else branch is empty gives an "if" clause, and a
         nested flatmap gives another "for" clause. Any other body is iterated over. *)
      let fix clauses (b : expr) : string * string :=
        match b with
        | EBinop OCons r (EAtom (ANil _))
        | EBinop OBagInsert (EAtom (AEmptyBag _)) r
        | EBinop OSetInsert (EAtom (AEmptySet _)) r => ("", expr_py r)
        | EIf p b' (EAtom (ANil _ | AEmptyBag _ | AEmptySet _)) =>
            let (cs, r) := clauses b' in (" if " ++ expr_py p ++ cs, r)
        | EFlatmap _ b1 y b' =>
            let (cs, r) := clauses b' in (" for " ++ y ++ " in " ++ expr_py b1 ++ cs, r)
        | ELet b1 y b' =>
            (* a let inside a comprehension binds y to a one-element list *)
            let (cs, r) := clauses b' in (" for " ++ y ++ " in [" ++ expr_py b1 ++ "]" ++ cs, r)
        | _ => (" for y in " ++ expr_py b, "y")
        end in
      let (cs, r) := clauses e2 in
      "[" ++ r ++ " for " ++ x ++ " in " ++ expr_py e1 ++ cs ++ "]"
  | ERecord l =>
      let compile_field '(k,v) :=
          """" ++ k ++ """: " ++ expr_py v in
      "{" ++ join ", " (map compile_field l) ++ "}"
  | EAccess r s =>
      expr_py r ++ "[""" ++ s ++ """]"
  | EOptMatch e e_none x e_some =>
      paren (expr_py e_none ++
             " if " ++ expr_py e ++
             " is None else (lambda " ++ x ++ ": " ++
             expr_py e_some ++ ")(" ++
             expr_py e ++ ")")
  | EBagOf l =>
      "list(" ++ expr_py l ++ ")"
  | ESetOf l =>
      (* Python can't have set of dicts *)
      "list(" ++ expr_py l ++ ")"
  | ESort _ l =>
      "sorted(" ++ expr_py l ++ ")"
  | EACFold AGSum e =>
      "sum(" ++ expr_py e ++ ")"
  | EACFold AGCount e =>
      "len(" ++ expr_py e ++ ")"
  | EACIFold AGMin e =>
      "optmin(" ++ expr_py e ++ ")"
  | EACIFold AGMax e =>
      "max(" ++ expr_py e ++ ")"
  | EFold e1 e2 v acc e3 =>
      "(foldr(" ++ "lambda " ++ acc ++ ", " ++ v ++ ": " ++ expr_py e3 ++ ", " ++
        expr_py e1 ++ "," ++
      expr_py e2 ++ "))"
  end.

Definition indent_unit := "    ".

Fixpoint indent (n:nat) : string :=
  match n with
  | O => ""
  | S n' => indent_unit ++ indent n'
  end.

Definition line (n:nat) (s:string) :=
  indent n ++ s ++ String "010"%char EmptyString.

Fixpoint command_py (n:nat) (c:command) : string :=
  match c with
  | CSkip =>
      line n "pass"
  | CSeq c1 c2 =>
      command_py n c1 ++
      command_py n c2
  | CLet e x c' =>
      (* functional let: just assign once *)
      line n (x ++ " = " ++ expr_py e) ++
      command_py n c'
  | CLetMut e x c' =>
      (* identical in Python; mutation allowed *)
      line n (x ++ " = " ++ expr_py e) ++
      command_py n c'
  | CAssign x (EBinop OCons e1 (ELoc x1)) =>
      if String.eqb x x1
      then line n (x ++ ".insert(0, " ++ expr_py e1 ++ ")")
      else line n (x ++ " = " ++ expr_py (EBinop OCons e1 (ELoc x1)))
  | CAssign x e =>
      line n (x ++ " = " ++ expr_py e)
  | CAssignChecked x e guard policy =>
      (* The guard reads the candidate value through x, so the write is made
         first and rolled back from a saved copy if the guard rejects it.  The
         saved name is derived from x; no fiat2 program can mention it. *)
      line n (x ++ "__prev = " ++ x) ++
      line n (x ++ " = " ++ expr_py e) ++
      line n ("if not " ++ paren (expr_py guard) ++ ":") ++
      line (S n) (x ++ " = " ++ x ++ "__prev") ++
      command_py (S n) policy
  | CIf e c1 c2 =>
      line n ("if " ++ expr_py e ++ ":") ++
      command_py (S n) c1 ++
      line n "else:" ++
      command_py (S n) c2
  | CForeach e x body =>
      line n ("for " ++ x ++ " in " ++ expr_py e ++ ":") ++
        command_py (S n) body

  end.

Definition program_py (c:command) : string :=
  command_py 0 c.

Definition sort_key_py (tbl : string) (sorted_attrs : list string) : string :=
  line 0 ("def " ++ tbl ++ "_key(tup) :") ++
    line 1 ("return (" ++ join ", " (map (fun attr => "tup[""" ++ attr ++ """]") sorted_attrs) ++ ")") ++
    line 0 "" ++
    line 0 ("def " ++ "sorted_" ++ tbl ++ "(l) :") ++
    line 1 ("return sorted(l, key=" ++ tbl ++ "_key)").

(* Compute sort_key_py "res" (Mergesort.Sectioned.sort String.leb ["name"; "department"; "feedback"]). *)
