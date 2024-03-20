Require Import fiat2.Language.

Section Phoas.
  (* PHOAS expression equivalent to source language *)
  Context {V : type -> Type}.
  Inductive phoas_expr : type -> Type :=
    (* Retain the variable name x as a hint for dephoasify *)
  | PhEVar (t : type) : V t -> phoas_expr t
  | PhELoc (t : type) (x : string) : phoas_expr t
  | PhEAtom {t : type} (a : atom t) : phoas_expr t
  | PhEUnop {t1 t2 : type} (o : unop t1 t2) (e : phoas_expr t1) : phoas_expr t2
  | PhEBinop {t1 t2 t3 : type} (o : binop t1 t2 t3)
      (e1 : phoas_expr t1) (e2: phoas_expr t2) : phoas_expr t3
  | PhEFlatmap {t1 t2 : type} (l1 : phoas_expr (TList t1)) (x : string) (fn_l2 : V t1 -> phoas_expr (TList t2))
    : phoas_expr (TList t2)
  | PhEFold {t1 t2 : type} (l1 : phoas_expr (TList t1)) (e2 : phoas_expr t2) (x y : string) (fn_e3 : V t1 -> V t2 -> phoas_expr t2) : phoas_expr t2
  | PhEIf {t : type} (e1 : phoas_expr TBool) (e2 e3 : phoas_expr t) : phoas_expr t
  | PhELet {t1 t2 : type} (x : string) (e1 : phoas_expr t1) (fn_e2 : V t1 -> phoas_expr t2) : phoas_expr t2.

  Inductive phoas_command : Type :=
  | PhCSkip
  | PhCSeq (c1 c2 : phoas_command)
  | PhCLet {t : type} (x : string) (e : phoas_expr t) (fn_c : V t -> phoas_command)
  | PhCLetMut {t : type} (x : string) (e : phoas_expr t) (c : phoas_command)
  | PhCGets {t : type} (x : string) (e : phoas_expr t)
  | PhCIf (e : phoas_expr TBool) (c1 c2 : phoas_command)
  | PhCForeach {t : type} (x : string) (l : phoas_expr (TList t)) (fn_c : V t -> phoas_command).
End Phoas.
Arguments phoas_expr : clear implicits.
Arguments phoas_command : clear implicits.

Definition Phoas_expr (t : type) := forall V, phoas_expr V t.

Definition Phoas_command := forall V, phoas_command V.
