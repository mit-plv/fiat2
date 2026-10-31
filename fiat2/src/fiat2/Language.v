From Stdlib Require Import String ZArith List.

(* Which questions a dictionary may answer, and so which structure may represent
   it. Only a Ranged dictionary may be used to answer a range query, and dict_kind
   can inform its backend implementation. *)
Inductive dict_kind : Type := Ranged | Unranged.

(* Fiat2 types *)
Inductive type : Type :=
| TInt
| TBool
| TString
| TUnit
| TOption (t : type)
| TList (t : type)
| TRecord (l : list (string * type))
| TDict (dk : dict_kind) (kt vt : type)
| TBag (t : type)
| TSet (t : type).

Section TypeIH.
  Context (P : type -> Prop).
    Hypothesis (f_int : P TInt) (f_bool : P TBool) (f_string : P TString) (f_unit : P TUnit)
      (f_option : forall t : type, P t -> P (TOption t)) (f_list : forall t : type, P t -> P (TList t))
      (f_record : forall l : list (string * type), Forall (fun p => P (snd p)) l -> P (TRecord l))
      (f_dict : forall (dk : dict_kind) (tk tv : type), P tk -> P tv -> P (TDict dk tk tv))
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
      | TInt => f_int
      | TBool => f_bool
      | TString => f_string
      | TUnit => f_unit
      | TOption t => f_option t (type_IH t)
      | TList t => f_list t (type_IH t)
      | TRecord l => f_record l (record_type_IH type_IH l)
      | TDict dk tk tv => f_dict dk tk tv (type_IH tk) (type_IH tv)
      | TBag t => f_bag t (type_IH t)
      | TSet t => f_set t (type_IH t)
       end.
End TypeIH.

Scheme Boolean Equality for dict_kind. (* creates dict_kind_beq *)
Scheme Boolean Equality for type. (* creates type_beq *)

Lemma dict_kind_beq_refl : forall dk, dict_kind_beq dk dk = true.
Proof. destruct dk; reflexivity. Qed.

Lemma dict_kind_beq_eq : forall dk dk', dict_kind_beq dk dk' = true <-> dk = dk'.
Proof. destruct dk, dk'; cbn; intuition congruence. Qed.

Definition is_ranged (dk : dict_kind) : bool :=
  match dk with Ranged => true | Unranged => false end.

Lemma is_ranged_true : forall dk, is_ranged dk = true -> dk = Ranged.
Proof. destruct dk; cbn; congruence. Qed.

Declare Scope fiat2_scope. Local Open Scope fiat2_scope.
Notation "t1 =? t2" := (type_beq t1 t2) (at level 70) : fiat2_scope.

(* Abstract syntax tree *)

(* Literals *)
Inductive atom : Type :=
| AInt (n : Z)
| ABool (b : bool)
| AString (s : string)
| ANil (t : option type)
| ANone (t : option type)
| AEmptyDict (dk : dict_kind) (t : option (type * type))
| AEmptyBag (t : option type)
| AEmptySet (t : option type)
| AUnit.

(* Unary operators *)
Inductive unop : Type :=
| ONeg
| ONot
| OLength
| OLengthString
| OStringOfInt
| OSome
| ODictValues
(* The set form of a dictionary's values.

   The constructs that are generic in the collection come at every level the
   rules need: AEmptyBag/AEmptySet, OBagInsert/OSetInsert, OBagOfList/OSetOfList,
   EFlatmap LikeBag/LikeSet, EACFold over a bag beside EACIFold over a set.
   ODictValues was the one such construct available at the bag level only, so
   an order-insensitive read served from a dictionary could not deliver a set. *)
| OSetOfBag
| OBagOfList
| OSetOfList
(* A set's cardinality.

   NOT an overload of OLength, which stays list-only on purpose.
   CollectionTransf.annotate_collection rewrites EUnop OLength l into
   EACFold AGCount (EUnop OBagOfList l), and it is a SYNTACTIC rule with no
   type to consult, so an OLength that also typed at TSet would make that
   rewrite emit OBagOfList of a set, which does not typecheck.  The two reads
   want opposite things anyway: a list's length is an order-insensitive read
   that SHOULD be relaxed to a bag count, while a set is already the relaxed
   form and has nothing left to declare.

   Before this operator the only way to ask a set its size was OLength of
   ESort LikeSet, which pays n log n to canonicalize a representation the
   answer never looks at.  Deliberately NOT given at the bag level: a bag's
   size is the SUM of its multiplicities rather than the length of its entry
   list, and nothing asks for it. *)
| OSetSize
(* The least key of a dictionary, or None when it is empty.

   Pinned at TDict Ranged, exactly as ODictRange is, and for the same reason:
   a hash table has no least key, so letting this type at Unranged would let a
   term demand a minimum from a structure that can only scan for it.  With this
   operator the kind reads as "the key order is READ" -- a range query is one
   way to read it and a minimum is another -- which is what Count's third
   classifier already says in prose.

   Note it is definable on either kind: TyVDict makes every well-typed
   dictionary StronglySorted by dict_entry_leb, so the least key is the HEAD's
   whatever the kind.  Pinning it is therefore a deliberate REFUSAL, not a
   consequence. *)
| ODictMinKey
(* The three-character windows of a string, in order.  A LIST, not a set:
   the index folds them into a dictionary, and EFold is list-only because
   a foreign accumulator over a set would need the step to commute.
   Duplicates are harmless -- set_insert is idempotent.

   Deliberately NOT parameterized by padding widths: pg_trgm's LPADDING and
   RPADDING stay out of the language, written at the call site as ordinary
   concatenation, so that trigrams_pad keeps doing visible work. *)
| OTrigrams.

(* Binary operators *)
Inductive binop : Type :=
| OPlus
| OMinus
| OTimes
| ODiv
| OMod
| OAnd
| OOr
| OConcat
| OConcatString
| OLess
| OEq
| OCons
| ORange
| OBagInsert
(* The dual of OBagInsert, and the bag-level counterpart of OSetDiff: the
   multiset difference, which is how a program says a row LEAVES a bag.  A
   filter is the only other way to say it, and a filter cannot say it -- it
   walks every element that stays, so a backend reading one cannot tell a
   removal from an arbitrary predicate.  See BagRemoveTransf.v. *)
| OBagDiff
| OSetInsert
| OSetUnion
| OSetIntersect
| OSetDiff
| OSetMem
| OStrContains
| OLookup
| ODelete
| OWords.

(* Ternary operators *)
Inductive ternop : Set :=
| OInsert
| OSubstring
| ODictRange
(* The complement of ODictRange: the entries whose keys the range does
   NOT cover. *)
| ODictRangeDelete.

(* What an expr with a list type can be interpreted to *)
Inductive collection_tag := LikeSet | LikeBag | LikeList.

Inductive aggr := AGSum | AGCount.

(* An associative, commutative, IDEMPOTENT operation folded over a set.
   Because the operation has all three properties the fold commits to no
   order, so no direction appears in the syntax and none has to be proved
   unobservable -- contrast EFold, whose direction is part of its meaning.

   AGUnion and AGIntersect are the set-level pair.  They exist because a
   read that intersects one bucket per trigram had to be written as an
   EFold seeded at the FIRST bucket: intersection has no identity over an
   unknown universe, so there was no zero to start from and the seed became
   a positional wart.  An aci_aggr answers at TOption instead, and None --
   the empty input -- is exactly the case in which the caller must fall
   back to a scan. *)
Inductive aci_aggr := AGMin | AGMax | AGUnion | AGIntersect.

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
| EFold (e1 e2 : expr) (v acc : string) (e3 : expr)
| EACFold (ag : aggr) (e : expr) (* associative commutative operation over bag *)
| EACIFold (ag : aci_aggr) (e : expr) (* associative commutative idempotent operation over set *)
| ERecord (l : list (string * expr))
| EAccess (r : expr) (s : string)
| EOptMatch (e : expr) (e_none : expr) (x : string) (e_some : expr)
| ESort (tag : collection_tag) (l : expr) (* by value order *).

Section ExprIH.
  Context (P : expr -> Prop).
  Hypothesis (f_var : forall x, P (EVar x)) (f_loc : forall x, P (ELoc x)) (f_atom : forall a, P (EAtom a))
    (f_unop : forall o e, P e -> P (EUnop o e))
    (f_binop : forall o e1 e2, P e1 -> P e2 -> P (EBinop o e1 e2))
    (f_ternop : forall o e1 e2 e3, P e1 -> P e2 -> P e3 -> P (ETernop o e1 e2 e3))
    (f_if : forall e1 e2 e3, P e1 -> P e2 -> P e3 -> P (EIf e1 e2 e3))
    (f_let : forall e1 x e2, P e1 -> P e2 -> P (ELet e1 x e2))
    (f_flatmap : forall tag e1 x e2, P e1 -> P e2 -> P (EFlatmap tag e1 x e2))
    (f_acfold : forall ag e, P e -> P (EACFold ag e))
    (f_acifold : forall ag e, P e -> P (EACIFold ag e))
    (f_fold : forall e1 e2 x y e3, P e1 -> P e2 -> P e3 -> P (EFold e1 e2 x y e3))
    (f_record : forall l, Forall (fun p => P (snd p)) l -> P (ERecord l))
    (f_access : forall r s, P r -> P (EAccess r s))
    (f_optmatch : forall e e_none x e_some, P e -> P e_none -> P e_some -> P (EOptMatch e e_none x e_some))
    (f_sort : forall tag l, P l -> P (ESort tag l)).

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
      | EFold e1 e2 x y e3 => f_fold e1 e2 x y e3 (expr_IH e1) (expr_IH e2) (expr_IH e3)
      | EACFold ag e => f_acfold ag e (expr_IH e)
      | EACIFold ag e => f_acifold ag e (expr_IH e)
      | ERecord l => f_record l (record_expr_IH expr_IH l)
      | EAccess r s => f_access r s (expr_IH r)
      | EOptMatch e e_none x e_some => f_optmatch e e_none x e_some (expr_IH e) (expr_IH e_none) (expr_IH e_some)
      | ESort tag l => f_sort tag l (expr_IH l)
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
