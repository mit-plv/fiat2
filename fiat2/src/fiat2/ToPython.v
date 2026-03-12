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
  | AEmptySet _ => "set()"
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
  | OSetInsert => paren ("{" ++ e2 ++ "}" ++ " | " ++ e1)
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
  | EFlatmap tag e1 x e2 =>
      let c1 := expr_py e1 in
      let c2 := expr_py e2 in
      match tag with
      | LikeSet =>
          "{" ++ "y for " ++ x ++ " in " ++ c1 ++
          " for y in " ++ c2 ++ "}"
      | _ =>
          "[" ++ "y for " ++ x ++ " in " ++ c1 ++
          " for y in " ++ c2 ++ "]"
      end
  | EFilter tag l x p =>
      let cl := expr_py l in
      let cp := expr_py p in
      match tag with
      | LikeSet =>
          "{" ++ x ++ " for " ++ x ++ " in " ++ cl ++
          " if " ++ cp ++ "}"
      | _ =>
          "[" ++ x ++ " for " ++ x ++ " in " ++ cl ++
          " if " ++ cp ++ "]"
      end
  | EProj tag l x r =>
      let cl := expr_py l in
      let cr := expr_py r in
      match tag with
      | LikeSet =>
          "{" ++ cr ++ " for " ++ x ++ " in " ++ cl ++ "}"
      | _ =>
          "[" ++ cr ++ " for " ++ x ++ " in " ++ cl ++ "]"
      end
  | EJoin tag l1 l2 x y p r =>
      let c1 := expr_py l1 in
      let c2 := expr_py l2 in
      let cp := expr_py p in
      let cr := expr_py r in
      match tag with
      | LikeSet =>
          "{" ++ cr ++ " for " ++ x ++ " in " ++ c1 ++
          " for " ++ y ++ " in " ++ c2 ++
          " if " ++ cp ++ "}"
      | _ =>
          "[" ++ cr ++ " for " ++ x ++ " in " ++ c1 ++
          " for " ++ y ++ " in " ++ c2 ++
          " if " ++ cp ++ "]"
      end
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
      "set(" ++ expr_py l ++ ")"
  | ESort _ l =>
      "sorted(" ++ expr_py l ++ ")"
  | EACFold AGSum e =>
      "sum(" ++ expr_py e ++ ")"
  | EACFold AGCount e =>
      "len(" ++ expr_py e ++ ")"
  | EACIFold AGMin e =>
      "min(" ++ expr_py e ++ ")"
  | EACIFold AGMax e =>
      "max(" ++ expr_py e ++ ")"
  | EFold e1 e2 v acc e3 =>
      "(foldr(" ++ "lambda " ++ acc ++ ", " ++ v ++ ": " ++ expr_py e3 ++ ", " ++
        expr_py e1 ++ "," ++
      expr_py e2 ++ "))"
  | EFlatmap2 e1 e2 x1 x2 e3 =>
      "[" ++ expr_py e3 ++
      " for " ++ x1 ++ " in " ++ expr_py e1 ++
      " for " ++ x2 ++ " in " ++ expr_py e2 ++ "]"
  | EDictFold d e0 k v acc e => "" (* unused *)
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
  | CAssign x e =>
      line n (x ++ " = " ++ expr_py e)
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

Compute sort_key_py "res" (Mergesort.Sectioned.sort String.leb ["name"; "department"; "feedback"]).
