From Stdlib Require Import String ZArith List.

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
| TDict (kt vt : type)
| TBag (t : type)
| TSet (t : type).

Section TypeIH.
  Context (P : type -> Prop).
    Hypothesis (f_word : P TWord) (f_int : P TInt) (f_bool : P TBool) (f_string : P TString) (f_unit : P TUnit)
      (f_option : forall t : type, P t -> P (TOption t)) (f_list : forall t : type, P t -> P (TList t))
      (f_record : forall l : list (string * type), Forall (fun p => P (snd p)) l -> P (TRecord l))
      (f_dict : forall tk tv : type, P tk -> P tv -> P (TDict tk tv))
      (f_bag : forall t : type, P t -> P (TBag t))
      (f_set : forall t : type, P t -> P (TSet t)).
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
      | TBag t => f_bag t (type_IH t)
      | TSet t => f_set t (type_IH t)
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
| AEmptyDict (t : option (type * type))
| AEmptyBag (t : option type)
| AEmptySet (t : option type)
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
| OCons
| ORange
| OWRange
| OBagInsert
| OSetInsert
| OLookup
| ODelete.

(* Ternary operators *)
Inductive ternop : Set :=
| OInsert.

(* What an expr with a list type can be interpreted to *)
Inductive collection_tag := LikeSet | LikeBag | LikeList.

Inductive aggr := AGSum | AGCount.

Inductive aci_aggr := AGMin | AGMax.

(* Expressions *)
Inductive expr : Type :=
| EVar (x : string)
| ELoc (x : string)
| EAtom (a : atom)
| EUnop (o : unop) (e : expr)
| EBinop (o : binop) (e1 e2: expr)
| ETernop (o : ternop) (e1 e2 e3 : expr)
| EIf (e1 : expr) (e2 e3 : expr)
| ELet (e1 : expr) (x : string) (e2 : expr)
| EFlatmap (tag : collection_tag) (e1 : expr) (x : string) (e2 : expr)
| EFlatmap2 (e1 e2 : expr) (x1 x2 : string) (e3 : expr)
| EFold (e1 e2 : expr) (v acc : string) (e3 : expr)
| EACFold (ag : aggr) (e : expr) (* associative commutative operation over bag *)
| EACIFold (ag : aci_aggr) (e : expr) (* associative commutative idempotent operation over set *)
| ERecord (l : list (string * expr))
| EAccess (r : expr) (s : string)
| EOptMatch (e : expr) (e_none : expr) (x : string) (e_some : expr)
| EDictFold (d e0 : expr) (k v acc : string) (e : expr)
| ESort (tag : collection_tag) (l : expr) (* by value order *)
(* relational algebra *)
| EFilter (tag: collection_tag) (l : expr) (x : string) (p : expr) (* Select a subset of rows from table *)
| EJoin (tag: collection_tag) (l1 l2 : expr) (x y : string) (p r : expr) (* Join two tables *)
| EProj (tag: collection_tag) (l : expr) (x : string) (r : expr) (* Generalized projection *)
(* conversion to different collections *)
| EBagOf (l : expr)
| ESetOf (l : expr).

Section ExprIH.
  Context (P : expr -> Prop).
  Hypothesis (f_var : forall x, P (EVar x)) (f_loc : forall x, P (ELoc x)) (f_atom : forall a, P (EAtom a))
    (f_unop : forall o e, P e -> P (EUnop o e))
    (f_binop : forall o e1 e2, P e1 -> P e2 -> P (EBinop o e1 e2))
    (f_ternop : forall o e1 e2 e3, P e1 -> P e2 -> P e3 -> P (ETernop o e1 e2 e3))
    (f_if : forall e1 e2 e3, P e1 -> P e2 -> P e3 -> P (EIf e1 e2 e3))
    (f_let : forall e1 x e2, P e1 -> P e2 -> P (ELet e1 x e2))
    (f_flatmap : forall tag e1 x e2, P e1 -> P e2 -> P (EFlatmap tag e1 x e2))
    (f_flatmap2 : forall e1 e2 x1 x2 e3, P e1 -> P e2 -> P e3 -> P (EFlatmap2 e1 e2 x1 x2 e3))
    (f_acfold : forall ag e, P e -> P (EACFold ag e))
    (f_acifold : forall ag e, P e -> P (EACIFold ag e))
    (f_fold : forall e1 e2 x y e3, P e1 -> P e2 -> P e3 -> P (EFold e1 e2 x y e3))
    (f_record : forall l, Forall (fun p => P (snd p)) l -> P (ERecord l))
    (f_access : forall r s, P r -> P (EAccess r s))
    (f_optmatch : forall e e_none x e_some, P e -> P e_none -> P e_some -> P (EOptMatch e e_none x e_some))
    (f_dictfold : forall d e0 k v acc e, P d -> P e0 -> P e -> P (EDictFold d e0 k v acc e))
    (f_sort : forall tag l, P l -> P (ESort tag l))
    (f_filter : forall tag l x p, P l -> P p -> P (EFilter tag l x p))
    (f_join : forall tag l1 l2 x y p r, P l1 -> P l2 -> P p -> P r -> P (EJoin tag l1 l2 x y p r))
    (f_proj : forall tag l x r, P l -> P r -> P (EProj tag l x r))
    (f_bagof : forall l, P l -> P (EBagOf l))
    (f_setof : forall l, P l -> P (ESetOf l)).

    Section __.
      Context (expr_IH : forall e, P e).
      Fixpoint record_expr_IH (l : list (string * expr)) : Forall (fun p => P (snd p)) l :=
        match l as l0 return Forall (fun p => P (snd p)) l0 with
        | nil => Forall_nil (fun p => P (snd p))
        | p :: l' => Forall_cons p (expr_IH (snd p)) (record_expr_IH l')
        end.
    End __.

    Fixpoint expr_IH (e : expr) : P e :=
      match e with
      | EVar x => f_var x
      | ELoc x => f_loc x
      | EAtom a => f_atom a
      | EUnop o e => f_unop o e (expr_IH e)
      | EBinop o e1 e2 => f_binop o e1 e2 (expr_IH e1) (expr_IH e2)
      | ETernop o e1 e2 e3 => f_ternop o e1 e2 e3 (expr_IH e1) (expr_IH e2) (expr_IH e3)
      | EIf e1 e2 e3 => f_if e1 e2 e3 (expr_IH e1) (expr_IH e2) (expr_IH e3)
      | ELet e1 x e2 => f_let e1 x e2 (expr_IH e1) (expr_IH e2)
      | EFlatmap tag e1 x e2 => f_flatmap tag e1 x e2 (expr_IH e1) (expr_IH e2)
      | EFlatmap2 e1 e2 x1 x2 e3 => f_flatmap2 e1 e2 x1 x2 e3 (expr_IH e1) (expr_IH e2) (expr_IH e3)
      | EFold e1 e2 x y e3 => f_fold e1 e2 x y e3 (expr_IH e1) (expr_IH e2) (expr_IH e3)
      | EACFold ag e => f_acfold ag e (expr_IH e)
      | EACIFold ag e => f_acifold ag e (expr_IH e)
      | ERecord l => f_record l (record_expr_IH expr_IH l)
      | EAccess r s => f_access r s (expr_IH r)
      | EOptMatch e e_none x e_some => f_optmatch e e_none x e_some (expr_IH e) (expr_IH e_none) (expr_IH e_some)
      | EDictFold d e0 k v acc e => f_dictfold d e0 k v acc e (expr_IH d) (expr_IH e0) (expr_IH e)
      | ESort tag l => f_sort tag l (expr_IH l)
      | EFilter tag l x p => f_filter tag l x p (expr_IH l) (expr_IH p)
      | EJoin tag l1 l2 x y p r => f_join tag l1 l2 x y p r (expr_IH l1) (expr_IH l2) (expr_IH p) (expr_IH r)
      | EProj tag l x r => f_proj tag l x r (expr_IH l) (expr_IH r)
      | EBagOf l => f_bagof l (expr_IH l)
      | ESetOf l => f_setof l (expr_IH l)
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
