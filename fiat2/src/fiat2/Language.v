Require Import String ZArith List.

(* Fiat2 types *)
Inductive type : Type :=
| TWord
| TInt
| TBool
| TString
| TUnit
| TOption (t : type)
| TList (t : type)
| TRecord (l : list (string * type))
| TDict (kt vt : type).

Section TypeIH.
  Context (P : type -> Prop).
    Hypothesis (f_word : P TWord) (f_int : P TInt) (f_bool : P TBool) (f_string : P TString) (f_unit : P TUnit)
      (f_option : forall t : type, P t -> P (TOption t)) (f_list : forall t : type, P t -> P (TList t))
      (f_record : forall l : list (string * type), Forall (fun p => P (snd p)) l -> P (TRecord l))
      (f_dict : forall tk tv : type, P tk -> P tv -> P (TDict tk tv)).
    Section __.
      Context (type_IH : forall t, P t).
      Fixpoint record_type_IH (l : list (string * type)) : Forall (fun p => P (snd p)) l :=
        match l as l0 return Forall (fun p => P (snd p)) l0 with
        | nil => Forall_nil (fun p => P (snd p))
        | p :: l' => Forall_cons p (type_IH (snd p)) (record_type_IH l')
        end.
    End __.
    Fixpoint type_IH (t : type) : P t :=
      match t with
      | TWord => f_word
      | TInt => f_int
      | TBool => f_bool
      | TString => f_string
      | TUnit => f_unit
      | TOption t => f_option t (type_IH t)
      | TList t => f_list t (type_IH t)
      | TRecord l => f_record l (record_type_IH type_IH l)
      | TDict tk tv => f_dict tk tv (type_IH tk) (type_IH tv)
       end.
End TypeIH.

Scheme Boolean Equality for type. (* creates type_beq *)

Declare Scope fiat2_scope. Local Open Scope fiat2_scope.
Notation "t1 =? t2" := (type_beq t1 t2) (at level 70) : fiat2_scope.

(* Abstract syntax tree *)

(* Literals *)
Inductive atom : Type :=
| AWord (n : Z)
| AInt (n : Z)
| ABool (b : bool)
| AString (s : string)
| ANil (t : option type)
| ANone (t : option type)
| AUnit.

(* Unary operators *)
Inductive unop : Type :=
| OWNeg
| ONeg
| ONot
| OLength
| OLengthString
| OIntToString
| OSome.

(* Binary operators *)
Inductive binop : Type :=
| OWPlus
| OPlus
| OWMinus
| OMinus
| OWTimes
| OTimes
| OWDivU
| OWDivS
| ODiv
| OWModU
| OWModS
| OMod
| OAnd
| OOr
| OConcat
| OConcatString
| OWLessU
| OWLessS
| OLess
| OEq
| ORepeat
| OCons
| ORange
| OWRange.

(* Expressions *)
Inductive expr : Type :=
| EVar (x : string)
| ELoc (x : string)
| EAtom (a : atom)
| EUnop (o : unop) (e : expr)
| EBinop (o : binop) (e1 e2: expr)
| EIf (e1 : expr) (e2 e3 : expr)
| ELet (e1 : expr) (x : string) (e2 : expr)
| EFlatmap (e1 : expr) (x : string) (e2 : expr)
| EFold (e1 e2 : expr) (v acc : string) (e3 : expr)
| ERecord (l : list (string * expr))
| EAccess (r : expr) (s : string)
| EDict (l : list (expr * expr))
| EInsert (d k v : expr)
| EDelete (d k : expr)
| ELookup (d k : expr)
| EOptMatch (e : expr) (e_none : expr) (x : string) (e_some : expr)
| EDictFold (d e0 : expr) (k v acc : string) (e : expr)
(* relational algebra *)
| EFilter (l : expr) (x : string) (p : expr) (* Select a subset of rows from table *)
| EJoin (l1 l2 : expr) (x y : string) (p r : expr) (* Join two tables *)
| EProj (l : expr) (x : string) (r : expr) (* Generalized projection *).

Section ExprIH.
  Context (P : expr -> Prop).
  Hypothesis (f_var : forall x, P (EVar x)) (f_loc : forall x, P (ELoc x)) (f_atom : forall a, P (EAtom a))
    (f_unop : forall o e, P e -> P (EUnop o e)) (f_binop : forall o e1 e2, P e1 -> P e2 -> P (EBinop o e1 e2))
    (f_if : forall e1 e2 e3, P e1 -> P e2 -> P e3 -> P (EIf e1 e2 e3))
    (f_let : forall e1 x e2, P e1 -> P e2 -> P (ELet e1 x e2))
    (f_flatmap : forall e1 x e2, P e1 -> P e2 -> P (EFlatmap e1 x e2))
    (f_fold : forall e1 e2 x y e3, P e1 -> P e2 -> P e3 -> P (EFold e1 e2 x y e3))
    (f_record : forall l, Forall (fun p => P (snd p)) l -> P (ERecord l))
    (f_access : forall r s, P r -> P (EAccess r s))
    (f_dict : forall l, Forall (fun p => P (fst p) /\ P (snd p)) l -> P (EDict l))
    (f_insert : forall d k v, P d -> P k -> P v -> P (EInsert d k v))
    (f_delete : forall d k, P d -> P k -> P (EDelete d k))
    (f_lookup : forall d k, P d -> P k -> P (ELookup d k))
    (f_optmatch : forall e e_none x e_some, P e -> P e_none -> P e_some -> P (EOptMatch e e_none x e_some))
    (f_dictfold : forall d e0 k v acc e, P d -> P e0 -> P e -> P (EDictFold d e0 k v acc e))
    (f_filter : forall l x p, P l -> P p -> P (EFilter l x p))
    (f_join : forall l1 l2 x y p r, P l1 -> P l2 -> P p -> P r -> P (EJoin l1 l2 x y p r))
    (f_proj : forall l x r, P l -> P r -> P (EProj l x r)).
    Section __.
      Context (expr_IH : forall e, P e).
      Fixpoint record_expr_IH (l : list (string * expr)) : Forall (fun p => P (snd p)) l :=
        match l as l0 return Forall (fun p => P (snd p)) l0 with
        | nil => Forall_nil (fun p => P (snd p))
        | p :: l' => Forall_cons p (expr_IH (snd p)) (record_expr_IH l')
        end.
      Fixpoint dict_expr_IH (l : list (expr * expr)) : Forall (fun v => P (fst v) /\ P (snd v)) l :=
        match l as l0 return Forall (fun v => P (fst v) /\ P (snd v)) l0 with
        | nil => Forall_nil (fun v => P (fst v) /\ P (snd v))
        | v :: l' => Forall_cons v (conj (expr_IH (fst v)) (expr_IH (snd v)))(dict_expr_IH l')
        end.
    End __.

    Fixpoint expr_IH (e : expr) : P e :=
      match e with
      | EVar x => f_var x
      | ELoc x => f_loc x
      | EAtom a => f_atom a
      | EUnop o e => f_unop o e (expr_IH e)
      | EBinop o e1 e2 => f_binop o e1 e2 (expr_IH e1) (expr_IH e2)
      | EIf e1 e2 e3 => f_if e1 e2 e3 (expr_IH e1) (expr_IH e2) (expr_IH e3)
      | ELet e1 x e2 => f_let e1 x e2 (expr_IH e1) (expr_IH e2)
      | EFlatmap e1 x e2 => f_flatmap e1 x e2 (expr_IH e1) (expr_IH e2)
      | EFold e1 e2 x y e3 => f_fold e1 e2 x y e3 (expr_IH e1) (expr_IH e2) (expr_IH e3)
      | ERecord l => f_record l (record_expr_IH expr_IH l)
      | EAccess r s => f_access r s (expr_IH r)
      | EDict l => f_dict l (dict_expr_IH expr_IH l)
      | EInsert d k v => f_insert d k v (expr_IH d) (expr_IH k) (expr_IH v)
      | EDelete d k => f_delete d k (expr_IH d) (expr_IH k)
      | ELookup d k => f_lookup d k (expr_IH d) (expr_IH k)
      | EOptMatch e e_none x e_some => f_optmatch e e_none x e_some (expr_IH e) (expr_IH e_none) (expr_IH e_some)
      | EDictFold d e0 k v acc e => f_dictfold d e0 k v acc e (expr_IH d) (expr_IH e0) (expr_IH e)
      | EFilter l x p => f_filter l x p (expr_IH l) (expr_IH p)
      | EJoin l1 l2 x y p r => f_join l1 l2 x y p r (expr_IH l1) (expr_IH l2) (expr_IH p) (expr_IH r)
      | EProj l x r => f_proj l x r (expr_IH l) (expr_IH r)
      end.
End ExprIH.

(* Commands *)
Inductive command : Type :=
| CSkip
| CSeq (c1 c2 : command)
| CLet (e : expr) (x : string) (c : command)
| CLetMut (e : expr) (x : string) (c : command)
| CAssign(x : string) (e : expr)
| CIf (e : expr) (c1 c2 : command)
| CForeach (e : expr) (x : string) (c : command).
