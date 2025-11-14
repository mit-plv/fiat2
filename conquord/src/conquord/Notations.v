Require Import conquord.Language.
Require Import String ZArith.

Declare Scope conquord_scope.

Declare Custom Entry conquord_comm.
Declare Custom Entry conquord_expr.
Declare Custom Entry record_entry.
Declare Custom Entry dict_entry.

Delimit Scope conquord_scope with conquord.

Bind Scope conquord_scope with command.
Bind Scope conquord_scope with expr.

(* Notations *)
Coercion EVar : string >-> expr.
Coercion AInt : Z >-> atom.
Coercion ABool : bool >-> atom.
Coercion EAtom : atom >-> expr.

Definition EAtom_AInt (z : Z) := EAtom (AInt z).
Definition EAtom_AInt_inv (e : expr) : option Z :=
  match e with
  | EAtom (AInt z) => Some z
  | _ => None
  end.

Number Notation expr EAtom_AInt EAtom_AInt_inv : conquord_scope.

Notation "<{ c }>" := c%conquord
   (at level 0, c custom conquord_comm at level 100) : conquord_scope.
Notation "<[ e ]>" := e%conquord
   (at level 0, e custom conquord_expr) : conquord_scope.
Notation "( x )" := x
   (in custom conquord_comm at level 0, x custom conquord_comm).
Notation "( x )" := x
                      (in custom conquord_expr at level 0, x custom conquord_expr).
(* Rules that work with the Number Notation above
   since Number Notations do not work with custom non-terminals in the grammar *)
Notation "x" := x
   (in custom conquord_comm at level 0, x constr at level 0).
Notation "x" := x
   (in custom conquord_expr at level 0, x constr at level 0).
(* Escape to constr with special symbols only for easier notation overloading *)
Notation "<< x >>" := x
   (in custom conquord_comm at level 0, x constr).
Notation "<< x >>" := x
   (in custom conquord_expr at level 0, x constr).

(* Command parsing *)
Notation "'skip'" := CSkip
   (in custom conquord_comm at level 0).
Notation "c1 ; c2" := (CSeq c1 c2)
   (in custom conquord_comm at level 90, right associativity, c1 custom conquord_comm, c2 custom conquord_comm).
Notation "'let' x = e 'in' c"        := (CLet e x c)
   (in custom conquord_comm at level 100, x constr at level 0, e custom conquord_expr, c custom conquord_comm).
Notation "'let' 'mut' x := e 'in' c"    := (CLetMut e x c)
   (in custom conquord_comm at level 100, x constr at level 0, e custom conquord_expr, c custom conquord_comm).
Notation "'set' x := e"                     := (CAssign x e)
   (in custom conquord_comm at level 50, x constr at level 0, e custom conquord_expr).
Notation "'if' e 'then' c1 'else' c2 'end'" := (CIf e c1 c2)
   (in custom conquord_comm at level 80, e custom conquord_expr, c1 custom conquord_comm, c2 custom conquord_comm).
Notation "'for' x 'in' e : c 'end'"  := (CForeach e x c)
   (in custom conquord_comm at level 80, x constr at level 0, e custom conquord_expr, c custom conquord_comm).

(* Expression parsing *)

(* Unary operations *)
Notation "- x" := (EUnop ONeg x) (in custom conquord_expr at level 10).
Notation "! x" := (EUnop ONot x) (in custom conquord_expr at level 10).
Notation "'len(' x ')'"   := (EUnop OLength x) (in custom conquord_expr at level 10).
Notation "'strLen(' x ')'" := (EUnop OLengthString x) (in custom conquord_expr at level 10).
Notation "'toStr(' n ')'" := (EUnop OIntToString n) (in custom conquord_expr at level 10).
Notation "'some(' x ')'" := (EUnop OSome x) (in custom conquord_expr at level 10).

(* Binary operators *)
Notation "x + y"              := (EBinop OPlus x y)
   (in custom conquord_expr at level 50, left associativity).
Notation "x - y"              := (EBinop OMinus x y)
   (in custom conquord_expr at level 50, left associativity).
Notation "x * y"              := (EBinop OTimes x y)
   (in custom conquord_expr at level 40, left associativity).
Notation "x / y"              := (EBinop ODiv x y)
   (in custom conquord_expr at level 40, left associativity).
Notation "x % y"              := (EBinop OMod x y)
   (in custom conquord_expr at level 40, left associativity).
Notation "x && y"             := (EBinop OAnd x y)
   (in custom conquord_expr at level 80, left associativity).
Notation "x || y"             := (EBinop OOr x y)
   (in custom conquord_expr at level 90, left associativity).
Notation "x ++ y"             := (EBinop OConcat x y)
   (in custom conquord_expr at level 60, left associativity).
Notation "x +++ y"             := (EBinop OConcatString x y)
   (in custom conquord_expr at level 60, left associativity).
Notation "x < y"              := (EBinop OLess x y)
   (in custom conquord_expr at level 70, left associativity).
Notation "x == y"             := (EBinop OEq x y)
   (in custom conquord_expr at level 70, left associativity).
Notation "x :: y"             := (EBinop OCons x y)
   (in custom conquord_expr at level 55, right associativity).
Notation "'range(' x ',' y ')'"  := (EBinop ORange x y)
   (in custom conquord_expr at level 10, left associativity).
Notation "[ x , .. , y ]"   := (EBinop OCons x .. (EBinop OCons y (EAtom (ANil None))) ..)
   (in custom conquord_expr at level 0, left associativity).
Notation "[ ]" := (EAtom (ANil None))
   (in custom conquord_expr).
Notation "'nil[' t ']'"        := (EAtom (ANil (Some t)))
   (in custom conquord_expr at level 10, t constr).

Notation "<( x , y )>" := (ERecord (("0"%string, x) :: ("1"%string, y) :: nil))
   (in custom conquord_expr at level 0, x custom conquord_expr at level 99,
       y custom conquord_expr at level 99, left associativity).
Notation "'fst(' x ')'" := (EAccess x "0")
   (in custom conquord_expr at level 10, format "fst( x )").
Notation "'snd(' x ')'" := (EAccess x "1")
   (in custom conquord_expr at level 10, format "snd( x )").

Notation "'mut' x" := (ELoc x)
   (in custom conquord_expr at level 0, x constr at level 0).
Notation "'if' e1 'then' e2 'else' e3" := (EIf e1 e2 e3)
   (in custom conquord_expr at level 99).
Notation "'let' x = e1 'in' e2"        := (ELet e1 x e2)
   (in custom conquord_expr at level 100, x constr at level 0, e1 custom conquord_expr, e2 custom conquord_expr).
Notation "'flatmap' e1 x e2"           := (EFlatmap LikeList e1 x e2)
   (in custom conquord_expr at level 99, x constr at level 0).
Notation "'fold' e1 e2 x y e3"           := (EFold e1 e2 x y e3)
   (in custom conquord_expr at level 99, x constr at level 0, y constr at level 0).
Notation "{ x , .. , y }" := (ERecord (cons x .. (cons y nil)..))
   (in custom conquord_expr at level 99, x custom record_entry, y custom record_entry).
Notation "k : v" := (k, v)
                      (in custom record_entry at level 0, k constr at level 0, v custom conquord_expr, no associativity).
Notation "x [ k ]" := (EAccess x k)
   (in custom conquord_expr at level 10).
Notation "k : v" := (k, v)
   (in custom dict_entry at level 0, k custom conquord_expr, v custom conquord_expr, no associativity).
Notation "'insert(' d , k -> v ')'" := (ETernop OInsert d k v)
   (in custom conquord_expr at level 99, d custom conquord_expr, k custom conquord_expr, v custom conquord_expr).
Notation "'delete(' d , k ')'" := (EBinop ODelete d k)
   (in custom conquord_expr at level 99, d custom conquord_expr, k custom conquord_expr).
Notation "'lookup(' d , k ')'" := (EBinop OLookup d k)
   (in custom conquord_expr at level 99, d custom conquord_expr, k custom conquord_expr).

Notation "x <- e1 ; e2" := (EFlatmap LikeList e1 x e2)
   (in custom conquord_expr at level 0, e1 custom conquord_expr at level 100, e2 custom conquord_expr at level 100).
Notation "'check(' e1 ')' ; e2" := (EIf e1 e2 (EAtom (ANil None)))
   (in custom conquord_expr at level 100, e1 custom conquord_expr, e2 custom conquord_expr).
Notation "'ret' e" := (EBinop OCons e (EAtom (ANil None)))
   (in custom conquord_expr at level 100, e custom conquord_expr).


Section Tests.
Local Open Scope conquord_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

  Context (x : string).
(*  Print Notation "_ ; _" in custom conquord_comm.
  Print Scope conquord_scope.
  Compute (<[ [] ++ [ 2 ] ]>).
  Compute (<[ x <- <<EAtom AUnit>> :: [ ] ; ret x ]>).
  Compute (<{ let "x" = <<EAtom AUnit>> in set x := "x" }>). *)

   Goal <{ skip }> = CSkip. reflexivity. Abort.
   Goal <{ skip; skip }> = CSeq CSkip CSkip. reflexivity. Abort.

   Goal <{ set "x" := 0 }> = CAssign "x" (EAtom 0). reflexivity. Abort.

   Goal <{ set "_" := -3 }> = CAssign "_" (EUnop ONeg 3). reflexivity. Abort.
   Goal <{ set "_" := -(3) }> = CAssign "_" (EUnop ONeg 3). reflexivity. Abort.

   Goal <{ set "_" := !true }> = CAssign "_" (EUnop ONot true). reflexivity. Abort.
   Goal <{ set "_" := !(true) }> = CAssign "_" (EUnop ONot true). reflexivity. Abort.

   Goal <{ set "_" := len([ 1, 2, 3]) }> = CAssign "_"
     (EUnop OLength (EBinop OCons 1 (EBinop OCons 2 (EBinop OCons 3 (EAtom (ANil None)))))).
   reflexivity. Abort.

   Goal <{ set "_" := fst(0) }> = CAssign "_" (EAccess 0 "0"). reflexivity. Abort.
   Goal forall x, <{ set "_" := x["0"] }> = CAssign "_" (EAccess x "0"). reflexivity. Abort.

   Goal <{ set "_" := <((1 + 3) * 4, 2)> }> = CAssign "_" <[ {"0" : (<<EBinop OTimes (EBinop OPlus 1 3) 4>>) , "1" : 2} ]>.
   reflexivity. Abort.

   Goal <{ set "_" := [1, 2, 3] }> = CAssign "_" (EBinop OCons 1 (EBinop OCons 2 (EBinop OCons 3 (EAtom (ANil None))))).
   reflexivity. Abort.

   Goal <{ set "_" := [1, 2] }> = CAssign "_" (EBinop OCons 1 (EBinop OCons 2 (EAtom (ANil None)))).
   reflexivity. Abort.

   Goal <{ set "_" := true }> = CAssign "_" (EAtom (ABool true)).
   reflexivity. Abort.

   Goal <{ set "_" := [ 1 ] }> = CAssign "_" (EBinop OCons 1 (EAtom (ANil None))).
   reflexivity. Abort.

   Goal <{ set "_" := 1 :: 2 :: [3, 4] }> = CAssign "_"
      (EBinop OCons 1 (EBinop OCons 2 (EBinop OCons 3 (EBinop OCons 4 (EAtom (ANil None)))))).
   reflexivity. Abort.

   Goal <{ set "_" := 3 :: 4 :: nil[TInt] }> = CAssign "_"
      (EBinop OCons 3 (EBinop OCons 4 (ANil (Some TInt)))).
   reflexivity. Abort.
   Goal <{ set "_" := true :: false :: nil[TBool] }> = CAssign "_"
      (EBinop OCons true (EBinop OCons false (ANil (Some TBool)))).
   reflexivity. Abort.

   Goal <{ set "_" := [2,4] :: nil[TList TInt] }> = CAssign "_"
      (EBinop OCons (EBinop OCons 2 (EBinop OCons 4 (EAtom (ANil None)))) (ANil (Some (TList TInt)))).
   reflexivity. Abort.

   Local Close Scope Z_scope.
   Local Close Scope nat_scope.
   Goal <{ let "x" = 3 + 4 in set "y" := "x" + 1; set "z" := 5 + "x" }> =
      (CLet (EBinop OPlus 3 4) "x"
         (CSeq (CAssign "y" (EBinop OPlus "x" 1))
                (CAssign "z" (EBinop OPlus 5 "x")))).
   reflexivity. Abort.

   Goal <{ let "x" = 3 + 4 in
               (let "y" = "x" + 1 in
                  set "z" := "x" + "y" - 1) }> =
      (CLet (EBinop OPlus 3 4) "x"
         (CLet (EBinop OPlus "x" 1) "y"
                (CAssign "z" (EBinop OMinus (EBinop OPlus "x" "y") 1)))).
   reflexivity. Abort.

   Goal <{ (let mut "x" := 3 in set "y" := "x" + 1);
           set "x" := "y" * 2;
           skip }> =
           CSeq
               (CLetMut 3 "x" (CAssign "y" (EBinop OPlus "x" 1)))
               (CSeq
                  (CAssign "x" (EBinop OTimes "y" 2))
                  CSkip).
   reflexivity. Abort.

   Goal <{ if 3 == 3 then set "y" := 0 + 1 else set "y" := 0 + 10; set "a" := 0 end }> =
      CIf (EBinop OEq 3 3)
           (CAssign "y" (EBinop OPlus 0 1))
           (CSeq (CAssign "y" (EBinop OPlus 0 10))
                  (CAssign "a" 0)).
     reflexivity. Abort.

   Goal <{ for "x" in [1,2]++[3]:
             set "a" := "x" * 2;
             set "b" := "x" + 1
           end;
           set "z" := 123 }> =
         CSeq (CForeach (EBinop OConcat (EBinop OCons 1 (EBinop OCons 2 (EAtom (ANil None)))) (EBinop OCons 3 (EAtom (ANil None))))  "x"
                  (CSeq (CAssign "a" (EBinop OTimes "x" 2))
                         (CAssign "b" (EBinop OPlus "x" 1))))
               (CAssign "z" 123).
     reflexivity. Abort.
End Tests.
