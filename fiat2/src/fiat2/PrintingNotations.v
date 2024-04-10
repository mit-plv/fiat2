Require Import fiat2.Language.
Require Import fiat2.Elaborate.
Require Import Coq.Lists.List.
Import ListNotations.

Declare Custom Entry fiat2_comm_elaborated.
Declare Custom Entry fiat2_elaborated.
Declare Custom Entry fiat2_record_access.
Declare Scope pretty_elab_scope.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Notation "'skip'"                     := (CSkip)
   (in custom fiat2_comm_elaborated at level 0, only printing) : pretty_elab_scope.
Notation "c1 ; c2"                    := (CSeq c1 c2)
   (in custom fiat2_comm_elaborated at level 90, only printing) : pretty_elab_scope.
Notation "'let' '$' x := p 'in' c"        := (CLet x p c)
  (in custom fiat2_comm_elaborated at level 100, only printing, x constr, p custom fiat2_elaborated, c custom fiat2_comm_elaborated, format "'let'  $ x  :=  p  'in'  c") : pretty_elab_scope.
Notation "'let' 'mut' x := p 'in' c"    := (CLetMut x%string p c)
   (in custom fiat2_comm_elaborated at level 100, only printing, p custom fiat2_elaborated, c custom fiat2_comm_elaborated) : pretty_elab_scope.
Notation "x <- p"                     := (CGets x p)
   (in custom fiat2_comm_elaborated at level 50, x constr, only printing, p custom fiat2_elaborated) : pretty_elab_scope.
Notation "'if' p 'then' c1 'else' c2 'end'" := (CIf p c1 c2)
   (in custom fiat2_comm_elaborated at level 80, only printing, p custom fiat2_elaborated, c1 custom fiat2_elaborated, c2 custom fiat2_elaborated) : pretty_elab_scope.
Notation "'for' x 'in' p : c 'end'"  := (CForeach x p c)
   (in custom fiat2_comm_elaborated at level 80, only printing, p custom fiat2_elaborated, c custom fiat2_elaborated) : pretty_elab_scope.

(* Unary operations (PEUnop) *)
Notation "- x"         := (EUnop ONeg x)
   (only printing, in custom fiat2_elaborated at level 10) : pretty_elab_scope.
Notation "! x"         := (EUnop ONot x)
   (only printing, in custom fiat2_elaborated at level 10) : pretty_elab_scope.
Notation "'length(' x ')'"   := (EUnop OLength x)
   (only printing, in custom fiat2_elaborated at level 10) : pretty_elab_scope.
Notation "'intToString(' x ')'"   := (EUnop OIntToString x)
   (only printing, in custom fiat2_elaborated at level 10, format "'intToString(' x ')'") : pretty_elab_scope.

(*
Notation "'fst(' x ')'" := (PEProj x "0")
   (only printing, in custom fiat2_elaborated at level 10, format "fst( x )") : pretty_elab_scope.
Notation "'snd(' x ')'" := (PEProj x "1")
   (only printing, in custom fiat2_elaborated at level 10) : pretty_elab_scope.
 *)


(* Binary operators (EBinop) *)
Notation "x + y"              := (EBinop OPlus x y)
   (only printing, in custom fiat2_elaborated at level 50, left associativity) : pretty_elab_scope.
Notation "x - y"              := (EBinop OMinus x y)
   (only printing, in custom fiat2_elaborated at level 50, left associativity) : pretty_elab_scope.
Notation "x * y"              := (EBinop OTimes x y)
   (only printing, in custom fiat2_elaborated at level 40, left associativity) : pretty_elab_scope.
Notation "x / y"              := (EBinop ODiv x y)
   (only printing, in custom fiat2_elaborated at level 40, left associativity) : pretty_elab_scope.
Notation "x % y"              := (EBinop OMod x y)
   (only printing, in custom fiat2_elaborated at level 40, left associativity) : pretty_elab_scope.
Notation "x && y"             := (EBinop OAnd x y)
   (only printing, in custom fiat2_elaborated at level 40, left associativity) : pretty_elab_scope.
Notation "x || y"             := (EBinop OOr x y)
   (only printing, in custom fiat2_elaborated at level 50, left associativity) : pretty_elab_scope.
Notation "x ++ y"             := (EBinop OConcatString x y)
   (only printing, in custom fiat2_elaborated at level 55, left associativity) : pretty_elab_scope.
Notation "x < y"              := (EBinop OLess x y)
   (only printing, in custom fiat2_elaborated at level 70, left associativity) : pretty_elab_scope.
Notation "x == y"             := (EBinop (OEq _ _) x y)
   (only printing, in custom fiat2_elaborated at level 70, left associativity) : pretty_elab_scope.
Notation "'repeat(' list ',' cnt ')'"       := (EBinop ORepeat list cnt)
   (only printing, in custom fiat2_elaborated at level 10, left associativity) : pretty_elab_scope.

Notation "( x , y )"          := (EBinop (OPair "0" _ _) x (EBinop (OPair "1" _ _) y (EAtom (ANil _))))
   (only printing, in custom fiat2_elaborated at level 0, x custom fiat2_elaborated at level 99,
    y custom fiat2_elaborated at level 99, left associativity) : pretty_elab_scope.

Notation "x :: y"             := (EBinop (OCons _) x y)
   (only printing, in custom fiat2_elaborated at level 55, right associativity) : pretty_elab_scope.
Notation "'range(' x ',' y ')'"  := (EBinop ORange x y)
   (only printing, in custom fiat2_elaborated at level 10, left associativity) : pretty_elab_scope.
Notation "[ x , .. , y ]"   := (EBinop (OCons _) x .. (EBinop (OCons _) y (EAtom (ANil _))) ..)
   (only printing, in custom fiat2_elaborated at level 0, left associativity) : pretty_elab_scope.
Notation "'nil[' t ']'"        := (ANil t)
   (only printing, in custom fiat2_elaborated at level 10, t constr) : pretty_elab_scope.


Declare Custom Entry pretty_record_fields.
Notation "s : x , y"          := (EBinop (OPair s%string _ _) x y)
   (only printing, format "s :  x , '/'  y", in custom pretty_record_fields at level 0, x custom fiat2_elaborated at level 99,
    y custom pretty_record_fields at level 99, s constr, left associativity) : pretty_elab_scope.
Notation "s : x"          := (EBinop (OPair s%string _ _) x (EAtom AEmpty))
   (only printing, format "s :  x", in custom pretty_record_fields at level 0, x custom fiat2_elaborated at level 99,
    s constr, left associativity) : pretty_elab_scope.


(* Other expr *)
Notation "'flatmap' e1 x e2"           := (EFlatmap e1 x%string e2)
   (only printing, in custom fiat2_elaborated at level 99, x constr at level 0,
   e1 custom fiat2_elaborated at level 9) : pretty_elab_scope.
Notation "'fold' e1 e2 x y e3"           := (EFold e1 e2 x%string y%string e3)
   (only printing, in custom fiat2_elaborated at level 99, x constr at level 0, y constr at level 0) : pretty_elab_scope.
Notation "'if' p1 'then' p2 'else' p3" := (EIf p1 p2 p3)
   (only printing, in custom fiat2_elaborated at level 99) : pretty_elab_scope.

Notation "$ x"           := (EVar _ x%string)
   (only printing, in custom fiat2_elaborated at level 0, x constr at level 0, format "$ x") : pretty_elab_scope.

Notation "'nil'"           := (EAtom (ANil _))
   (only printing, in custom fiat2_elaborated at level 0) : pretty_elab_scope.
Notation "n"           := (EAtom (_ n))
   (only printing, in custom fiat2_elaborated at level 0, n constr) : pretty_elab_scope.
Notation "( e )" := e (only printing, in custom fiat2_elaborated at level 0, e custom fiat2_elaborated at level 99) : pretty_elab_scope.
Notation "'let' x := p1 'in' p2"       := (ELet x p1 p2)
   (only printing, in custom fiat2_elaborated at level 99) : pretty_elab_scope.

(* Notation for printing record access. Weird tricks are used, but when expanded the brackets look correct *)
Notation "e [" := (e)
  (only printing, in custom fiat2_record_access at level 10, e custom fiat2_elaborated at level 0, format "e [") : pretty_elab_scope.
Notation "x" := (EUnop (OSnd _ _ _) x)
  (only printing, x at level 10, in custom fiat2_record_access at level 10) : pretty_elab_scope.
Notation "x k ] [" := (EUnop (OFst k _ _) x)
  (only printing, k constr, x at level 10, in custom fiat2_record_access at level 10, format "x k ] [") : pretty_elab_scope.
Notation "x k ']'" := (EUnop (OFst k _ _) x)
  (only printing, in custom fiat2_elaborated at level 10, x custom fiat2_record_access, k constr at level 0, format "x k ]") : pretty_elab_scope.

Notation "<{{ e }}>" := e (e custom fiat2_comm_elaborated) : pretty_elab_scope.
Notation "<{[ e ]}>" := e (e custom fiat2_elaborated) : pretty_elab_scope.
Notation "{ e }" := e (only printing, in custom fiat2_elaborated, e custom pretty_record_fields at level 99).
