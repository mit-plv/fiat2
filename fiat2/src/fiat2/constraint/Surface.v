Require Import fiat2.Language fiat2.Invariant.
From Stdlib Require Import String List.
Import ListNotations.

(* A surface language with declared constraints, and its elaboration into the
   core.

   A declaration introduces a mutable variable born empty together with the
   constraints that must hold of it.  Each constraint is a condition on a row,
   which may read the table, or any other table in scope, through ELoc.
   Elaboration turns the constraints into the binder's invariants, and inserts
   a check at every assignment that can affect an invariant in scope, turning

     x := e  else  policy

   into

     if <every invariant mentioning x, read of e> then x := e else policy.

   So the policy a programmer writes at a write site is simply the else branch:
   it is an ordinary command, and if it assigns to a constrained variable it is
   elaborated too and gets its own check. *)

Inductive scommand : Type :=
| SSkip
| SSeq (c1 c2 : scommand)
| SLet (e : expr) (x : string) (c : scommand)
| SLetMut (e : expr) (x : string) (c : scommand)
(* x is born empty, holds rows of row_ty, and every (row, cond) in ds must hold
   of each of its rows for as long as it is in scope *)
| SLetConstrained (x : string) (row_ty : type) (ds : list (string * expr)) (c : scommand)
(* policy is what runs instead of the write when an invariant would break; it
   is dead syntax when no invariant in scope mentions x *)
| SAssign (x : string) (e : expr) (policy : scommand)
| SIf (e : expr) (c1 c2 : scommand)
| SForeach (e : expr) (x : string) (c : scommand).

Definition decl_invs (x : string) (ds : list (string * expr)) : list invariant :=
  List.map (fun d => ConstraintInv x nil (fst d) (snd d)) ds.

Definition guards (x : string) (e : expr) (ictx : list invariant) : expr :=
  fold_right (fun i g => EBinop OAnd (inv_guard x e i) g) (EAtom (ABool true)) ictx.

Fixpoint elab (ictx : list invariant) (sc : scommand) : command :=
  match sc with
  | SSkip => CSkip
  | SSeq c1 c2 => CSeq (elab ictx c1) (elab ictx c2)
  | SLet e x c => CLet e x (elab ictx c)
  | SLetMut e x c => CLetMut e x None nil (elab ictx c)
  | SLetConstrained x row_ty ds c =>
      CLetMut (EAtom (ANil (Some row_ty))) x (Some (TList row_ty)) (decl_invs x ds)
        (elab (decl_invs x ds ++ ictx) c)
  | SAssign x e policy =>
      match filter (inv_mentions x) ictx with
      | nil => CAssign x e
      | invs => CIf (guards x e invs) (CAssign x e) (elab ictx policy)
      end
  | SIf e c1 c2 => CIf e (elab ictx c1) (elab ictx c2)
  | SForeach e x c => CForeach e x (elab ictx c)
  end.
