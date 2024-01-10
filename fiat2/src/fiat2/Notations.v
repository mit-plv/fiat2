Require Import fiat2.Language.
Require Import fiat2.Elaborate.
Require Import fiat2.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.Properties.
Require Import coqutil.Datatypes.Result.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Import ResultMonadNotations.

Declare Scope fiat2_scope.
Declare Custom Entry fiat2_expr.
Declare Custom Entry fiat2_comm.


Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Open Scope fiat2_scope.

Coercion PEVar : string >-> pexpr.

Coercion PAInt : Z >-> patom.
Coercion PABool : bool >-> patom.
Coercion PEAtom : patom >-> pexpr.

Notation "<{ e }>"       := (e : pcommand) (at level 0, e custom fiat2_comm at level 99, only parsing) : fiat2_scope.
Notation "<{ e }>"       := e (at level 0, e custom fiat2_comm at level 99, only printing) : fiat2_scope.
Notation "<[ e ]>"       := e (in custom fiat2_expr at level 0, e constr at level 200) : fiat2_scope.
Notation "<[ e ]>"       := e (in custom fiat2_comm at level 0, e constr at level 200) : fiat2_scope.
Notation "( x )"         := x (in custom fiat2_expr at level 0, x custom fiat2_expr at level 99) : fiat2_scope.
Notation "( x )"         := x (in custom fiat2_comm at level 0, x custom fiat2_comm at level 99) : fiat2_scope.
Notation "x"             := x (in custom fiat2_expr at level 0, x constr at level 0) : fiat2_scope.
Notation "x"             := x (in custom fiat2_comm at level 0, x constr at level 0) : fiat2_scope.

(* TODO Allow string constants (which are different from vars) *)

(* Command parsing *)
Notation "'skip'"                     := (PCSkip)
   (in custom fiat2_comm at level 0) : fiat2_scope.
Notation "c1 ; c2"                    := (PCSeq c1 c2)
   (in custom fiat2_comm at level 90, right associativity, c1 custom fiat2_comm, c2 custom fiat2_comm) : fiat2_scope.
Notation "'let' x := p 'in' c"        := (PCLet x p c)
   (in custom fiat2_comm at level 100, p custom fiat2_expr, c custom fiat2_comm) : fiat2_scope.
Notation "'let' 'mut' x := p 'in' c"    := (PCLetMut x%string p c)
   (in custom fiat2_comm at level 100, p custom fiat2_expr, c custom fiat2_comm) : fiat2_scope.
Notation "x <- p"                     := (PCGets x p)
   (in custom fiat2_comm at level 50, p custom fiat2_expr) : fiat2_scope.
Notation "'if' p 'then' c1 'else' c2 'end'" := (PCIf p c1 c2)
   (in custom fiat2_comm at level 80, p custom fiat2_expr, c1 custom fiat2_comm, c2 custom fiat2_comm) : fiat2_scope.
Notation "'for' x 'in' p : c 'end'"  := (PCForeach x p c)
   (in custom fiat2_comm at level 80, p custom fiat2_expr, c custom fiat2_comm) : fiat2_scope.

(* Type parsing (Types are prefixed with @ so they do not become keywords and pollute the namespace *)
Notation Int    := TInt.
Notation Bool   := TBool.
Notation String := TString.
Notation Pair   := TPair.
Notation Unit   := TEmpty.
Notation List   := TList.


(* Expression parsing *)

(* Unary operations (PEUnop) *)
Notation "- x"         := (PEUnop PONeg x)
   (in custom fiat2_expr at level 10) : fiat2_scope.
Notation "! x"         := (PEUnop PONot x)
   (in custom fiat2_expr at level 10) : fiat2_scope.
Notation "'length(' x ')'"   := (PEUnop POLength x)
   (in custom fiat2_expr at level 10) : fiat2_scope.


(* not a unary operator, move *)
Notation "x [ field ]"        := (PEProj x field%string) (in custom fiat2_expr at level 10) : fiat2_scope.
(* syntactic sugar *)
Notation "'fst(' x ')'" := (PEProj x "0")
   (in custom fiat2_expr at level 10, format "fst( x )") : fiat2_scope.
Notation "'snd(' x ')'" := (PEProj x "1")
   (in custom fiat2_expr at level 10) : fiat2_scope.


(* Binary operators (PEBinop) *)
Notation "x + y"              := (PEBinop POPlus x y)
   (in custom fiat2_expr at level 50, left associativity) : fiat2_scope.
Notation "x - y"              := (PEBinop POMinus x y)
   (in custom fiat2_expr at level 50, left associativity) : fiat2_scope.
Notation "x * y"              := (PEBinop POTimes x y)
   (in custom fiat2_expr at level 40, left associativity) : fiat2_scope.
Notation "x / y"              := (PEBinop PODiv x y)
   (in custom fiat2_expr at level 40, left associativity) : fiat2_scope.
Notation "x % y"              := (PEBinop POMod x y)
   (in custom fiat2_expr at level 40, left associativity) : fiat2_scope.
Notation "x && y"             := (PEBinop POAnd x y)
   (in custom fiat2_expr at level 40, left associativity) : fiat2_scope.
Notation "x || y"             := (PEBinop POOr x y)
   (in custom fiat2_expr at level 50, left associativity) : fiat2_scope.
Notation "x ++ y"             := (PEBinop POConcat x y)
   (in custom fiat2_expr at level 60, left associativity) : fiat2_scope.
Notation "x < y"              := (PEBinop POLess x y)
   (in custom fiat2_expr at level 70, left associativity) : fiat2_scope.
Notation "x == y"             := (PEBinop POEq x y)
   (in custom fiat2_expr at level 70, left associativity) : fiat2_scope.
Notation "'repeat(' list ',' cnt ')'"       := (PEBinop PORepeat list cnt)
   (in custom fiat2_expr at level 10, left associativity) : fiat2_scope.
Notation "( x , y )"          := (PEBinop POPair x y)
   (in custom fiat2_expr at level 0, x custom fiat2_expr at level 99,
    y custom fiat2_expr at level 99, left associativity) : fiat2_scope.
Notation "x :: y"             := (PEBinop POCons x y)
   (in custom fiat2_expr at level 55, right associativity) : fiat2_scope.
Notation "'range(' x ',' y ')'"  := (PEBinop PORange x y)
   (in custom fiat2_expr at level 10, left associativity) : fiat2_scope.

Notation "[ x , .. , y , z ]"   := (PEBinop POCons x .. (PEBinop POCons y (PESingleton z)) ..)
   (in custom fiat2_expr at level 0, left associativity) : fiat2_scope.
Notation "[ x ]"                := (PESingleton x)
   (in custom fiat2_expr at level 0) : fiat2_scope.
Notation "'nil[' t ']'"        := (PANil t)
   (in custom fiat2_expr at level 10, t constr) : fiat2_scope.


(* Other pexpr *)
Notation "'flatmap' e1 x e2"           := (PEFlatmap e1 x%string e2)
   (in custom fiat2_expr at level 99, x constr at level 0) : fiat2_scope.
Notation "'fold' e1 e2 x y e3"           := (PEFold e1 e2 x%string y%string e3)
   (in custom fiat2_expr at level 99, x constr at level 0, y constr at level 0) : fiat2_scope.
Notation "'if' p1 'then' p2 'else' p3" := (PEIf p1 p2 p3)
   (in custom fiat2_expr at level 99) : fiat2_scope.
Notation "'let' x := p1 'in' p2"       := (PELet x p1 p2)
   (in custom fiat2_expr at level 99) : fiat2_scope.
(* TODO PERecord *)

Section Tests.
   Goal <{ skip }> = PCSkip. reflexivity. Abort.
   Goal <{ skip; skip }> = PCSeq PCSkip PCSkip. reflexivity. Abort.

   Goal <{ "x" <- 0 }> = PCGets "x" (PEAtom 0). reflexivity. Abort.

   Goal <{ "_" <- -3 }> = PCGets "_" (PEUnop PONeg 3). reflexivity. Abort.
   Goal <{ "_" <- -(3) }> = PCGets "_" (PEUnop PONeg 3). reflexivity. Abort.

   Goal <{ "_" <- !true }> = PCGets "_" (PEUnop PONot true). reflexivity. Abort.
   Goal <{ "_" <- !(true) }> = PCGets "_" (PEUnop PONot true). reflexivity. Abort.

   Goal <{ "_" <- length([ 1, 2, 3]) }> = PCGets "_"
     (PEUnop POLength (PEBinop POCons 1 (PEBinop POCons 2 (PESingleton 3)))).
   reflexivity. Abort.

   Goal <{ "_" <- fst(0) }> = PCGets "_" (PEProj 0 "0"). reflexivity. Abort.
   Goal forall x, <{ "_" <- x["0"] }> = PCGets "_" (PEProj x "0"). reflexivity. Abort.

   Goal <{ "_" <- ((1 + 3)*4, 2) }> = PCGets "_" ((PEBinop POPair (PEBinop POTimes (PEBinop POPlus 1 3) 4) 2)).
   reflexivity. Abort.

   Goal <{ "_" <- [1, 2, 3] }> = PCGets "_" (PEBinop POCons 1 (PEBinop POCons 2 (PESingleton 3))).
   reflexivity. Abort.

   Goal <{ "_" <- [1, 2] }> = PCGets "_" (PEBinop POCons 1 (PESingleton 2)).
   reflexivity. Abort.

   Goal <{ "_" <- true }> = PCGets "_" (PEAtom (PABool true)).
   reflexivity. Abort.

   Goal <{ "_" <- [ 1 ] }> = PCGets "_" (PESingleton 1).
   reflexivity. Abort.

   Goal <{ "_" <- true }> = PCGets "_" (PEAtom (PABool true)).
   reflexivity. Abort.

   Goal <{ "_" <- 1 :: 2 :: [3, 4] }> = PCGets "_"
      (PEBinop POCons 1 (PEBinop POCons 2 (PEBinop POCons 3 (PESingleton 4)))).
   reflexivity. Abort.

   Goal <{ "_" <- 3 :: 4 :: nil[Int] }> = PCGets "_"
      (PEBinop POCons 3 (PEBinop POCons 4 (PANil TInt))).
   reflexivity. Abort.
   Goal <{ "_" <- true :: false :: nil[Bool] }> = PCGets "_"
      (PEBinop POCons true (PEBinop POCons false (PANil TBool))).
   reflexivity. Abort.

   Goal <{ "_" <- [2,4] :: nil[List Int] }> = PCGets "_"
      (PEBinop POCons (PEBinop POCons 2 (PESingleton 4)) (PANil (TList TInt))).
   reflexivity. Abort.

   Goal <{ let "x" := 3 + 4 in "y" <- "x"+1; "z" <- 5+"x" }> =
      (PCLet "x" (PEBinop POPlus 3 4)
         (PCSeq (PCGets "y" (PEBinop POPlus "x" 1))
                (PCGets "z" (PEBinop POPlus 5 "x")))).
   reflexivity. Abort.

   Goal <{ let "x" := 3 + 4 in
               let "y" := "x" + 1 in
                  "z" <- "x" + "y" - 1 }> =
      (PCLet "x" (PEBinop POPlus 3 4)
         (PCLet "y" (PEBinop POPlus "x" 1)
                (PCGets "z" (PEBinop POMinus (PEBinop POPlus "x" "y") 1)))).
   reflexivity. Abort.

   Goal <{ (let mut "x" := 3 in "y" <- "x" + 1);
           "x" <- "y" * 2;
           skip }> =
           PCSeq
               (PCLetMut "x" 3 (PCGets "y" (PEBinop POPlus "x" 1)))
               (PCSeq
                  (PCGets "x" (PEBinop POTimes "y" 2))
                  PCSkip).
   reflexivity. Abort.

   Goal <{ if 3 == 3 then "y" <- 0+1 else "y" <- 0+10; "a" <- 0 end }> =
      PCIf (PEBinop POEq 3 3)
           (PCGets "y" (PEBinop POPlus 0 1))
           (PCSeq (PCGets "y" (PEBinop POPlus 0 10))
                  (PCGets "a" 0)).
   reflexivity. Abort.

   Goal <{ for "x" in [1,2]++[3]:
             "a" <- "x"*2;
             "b" <- "x"+1
           end;
           "z" <- 123 }> =
         PCSeq (PCForeach "x" (PEBinop POConcat (PEBinop POCons 1 (PESingleton 2)) (PESingleton 3))
                  (PCSeq (PCGets "a" (PEBinop POTimes "x" 2))
                         (PCGets "b" (PEBinop POPlus "x" 1))))
               (PCGets "z" 123).
   reflexivity. Abort.
End Tests.
