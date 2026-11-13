From Stdlib Require Import String ZArith List.

(* Only a Ranged dictionary may be used to answer a range query, and dict_kind
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

Lemma dict_kind_beq_refl : forall dk, dict_kind_beq dk dk = true.
Proof. destruct dk; reflexivity. Qed.

Lemma dict_kind_beq_eq : forall dk dk', dict_kind_beq dk dk' = true <-> dk = dk'.
Proof. destruct dk, dk'; cbn; intuition congruence. Qed.

Definition is_ranged (dk : dict_kind) : bool :=
  match dk with Ranged => true | Unranged => false end.

Lemma is_ranged_true : forall dk, is_ranged dk = true -> dk = Ranged.
Proof. destruct dk; cbn; congruence. Qed.

Scheme Equality for list.
Arguments list_beq {A}.

Fixpoint type_eqb (t t' : type) {struct t} : bool :=
  match t, t' with
  | TInt, TInt
  | TBool, TBool
  | TString, TString
  | TUnit, TUnit => true
  | TOption t1, TOption t1' => type_eqb t1 t1'
  | TList t1, TList t1' => type_eqb t1 t1'
  | TRecord l, TRecord l' => list_beq (fun p p' => andb (String.eqb (fst p) (fst p'))
                                                       (type_eqb (snd p) (snd p'))) l l'
  | TDict dk kt vt, TDict dk' kt' vt' => andb (dict_kind_beq dk dk') (andb (type_eqb kt kt') (type_eqb vt vt'))
  | TBag t, TBag t' => type_eqb t t'
  | TSet t, TSet t' => type_eqb t t'
  | _, _ => false
  end.

Lemma type_eqb_refl : forall t, type_eqb t t = true.
Proof.
  induction t using type_IH; auto; cbn.
  1:{ induction H; try constructor.
      cbn; rewrite eqb_refl. rewrite IHForall, H; auto. }
  1:{ rewrite dict_kind_beq_refl, IHt1, IHt2; auto. }
Qed.

Lemma type_eqb_eq : forall t t', type_eqb t t' = true <-> t = t'.
Proof.
  split.
  1:{ revert t t'.
      induction t using type_IH; intros;
        destruct t'; try discriminate; simpl in *; intuition idtac;
      try (lazymatch goal with
             IH: context[_ -> _], H: type_eqb _ _ = _ |- _ =>
               apply IH in H end; congruence).
      - generalize dependent l0. induction l; destruct l0; simpl in *; try discriminate; intuition idtac.
        destruct (andb (fst a =? fst p)%string (type_eqb (snd a) (snd p))) eqn:E; simpl in *; try discriminate.
        inversion H; subst. apply (IHl H4) in H0. injection H0; intros; subst.
        destruct a, p; inversion H; simpl in *; subst. apply andb_prop in E as [EL ER].
        rewrite eqb_eq in EL. apply H3 in ER. congruence.
      - apply andb_prop in H as [HK H]. apply andb_prop in H as [HL HR].
        apply dict_kind_beq_eq in HK.
        apply IHt1 in HL; apply IHt2 in HR. congruence. }
  1: intro; subst; apply type_eqb_refl.
Qed.

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
| OSetOfBag
| OBagOfList
| OSetOfList
| OSetSize
(* The least key of a ranged dictionary, or None when it is empty. *)
| ODictMinKey
(* The three-character windows of a string, in order. *)
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
(* The complement of ODictRange. *)
| ODictRangeDelete.

(* Collection interpretations *)
Inductive collection_tag := LikeSet | LikeBag | LikeList.

(* An associative and commutative aggregate over a bag. *)
Inductive aggr := AGSum | AGCount.

(* An associative, commutative, and idempotent aggregate over a set. *)
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

Definition type_eq_dec (t t' : type) : {t = t'} + {t <> t'}.
Proof.
  destruct (type_eqb t t') eqn:E.
  1: left; apply type_eqb_eq; exact E.
  1: right; intro H; apply type_eqb_eq in H; congruence.
Defined.

Definition opt_type_eq_dec (t t' : option type) : {t = t'} + {t <> t'}.
Proof. decide equality; apply type_eq_dec. Defined.

Definition opt_type_pair_eq_dec (t t' : option (type * type)) : {t = t'} + {t <> t'}.
Proof. decide equality; decide equality; apply type_eq_dec. Defined.

Definition dict_kind_eq_dec (d d' : dict_kind) : {d = d'} + {d <> d'}.
Proof. decide equality. Defined.

Definition atom_eq_dec (a a' : atom) : {a = a'} + {a <> a'}.
Proof.
  decide equality;
    first [ apply Z.eq_dec | apply Bool.bool_dec | apply string_dec | apply opt_type_eq_dec
          | apply opt_type_pair_eq_dec | apply dict_kind_eq_dec ].
Defined.

Definition unop_eq_dec (o o' : unop) : {o = o'} + {o <> o'}.
Proof. decide equality. Defined.

Definition binop_eq_dec (o o' : binop) : {o = o'} + {o <> o'}.
Proof. decide equality. Defined.

Definition ternop_eq_dec (o o' : ternop) : {o = o'} + {o <> o'}.
Proof. decide equality. Defined.

Definition tag_eq_dec (t t' : collection_tag) : {t = t'} + {t <> t'}.
Proof. decide equality. Defined.

Definition aggr_eq_dec (a a' : aggr) : {a = a'} + {a <> a'}.
Proof. decide equality. Defined.

Definition aci_aggr_eq_dec (a a' : aci_aggr) : {a = a'} + {a <> a'}.
Proof. decide equality. Defined.

Definition dec_to_bool {A} (d : forall x y : A, {x = y} + {x <> y}) (x y : A) : bool :=
  if d x y then true else false.

Lemma dec_to_bool_true : forall A d (x y : A), dec_to_bool d x y = true -> x = y.
Proof. unfold dec_to_bool; intros; destruct (d x y); congruence. Qed.

Local Open Scope bool_scope.

Fixpoint expr_eqb (e e' : expr) {struct e} : bool :=
  match e, e' with
  | EVar x, EVar x' => String.eqb x x'
  | ELoc x, ELoc x' => String.eqb x x'
  | EAtom a, EAtom a' => dec_to_bool atom_eq_dec a a'
  | EUnop o e1, EUnop o' e1' => dec_to_bool unop_eq_dec o o' && expr_eqb e1 e1'
  | EBinop o e1 e2, EBinop o' e1' e2' =>
      dec_to_bool binop_eq_dec o o' && expr_eqb e1 e1' && expr_eqb e2 e2'
  | ETernop o e1 e2 e3, ETernop o' e1' e2' e3' =>
      dec_to_bool ternop_eq_dec o o' && expr_eqb e1 e1' && expr_eqb e2 e2'
      && expr_eqb e3 e3'
  | EIf e1 e2 e3, EIf e1' e2' e3' => expr_eqb e1 e1' && expr_eqb e2 e2' && expr_eqb e3 e3'
  | ELet e1 x e2, ELet e1' x' e2' => expr_eqb e1 e1' && String.eqb x x' && expr_eqb e2 e2'
  | EFlatmap t e1 x e2, EFlatmap t' e1' x' e2' =>
      dec_to_bool tag_eq_dec t t' && expr_eqb e1 e1' && String.eqb x x' && expr_eqb e2 e2'
  | EFold e1 e2 x y e3, EFold e1' e2' x' y' e3' =>
      expr_eqb e1 e1' && expr_eqb e2 e2' && String.eqb x x' && String.eqb y y'
      && expr_eqb e3 e3'
  | EACFold a e1, EACFold a' e1' => dec_to_bool aggr_eq_dec a a' && expr_eqb e1 e1'
  | EACIFold a e1, EACIFold a' e1' => dec_to_bool aci_aggr_eq_dec a a' && expr_eqb e1 e1'
  | ERecord l, ERecord l' =>
      list_beq (fun p p' => String.eqb (fst p) (fst p') && expr_eqb (snd p) (snd p')) l l'
  | EAccess r s, EAccess r' s' => expr_eqb r r' && String.eqb s s'
  | EOptMatch e1 e2 x e3, EOptMatch e1' e2' x' e3' =>
      expr_eqb e1 e1' && expr_eqb e2 e2' && String.eqb x x' && expr_eqb e3 e3'
  | ESort t e1, ESort t' e1' => dec_to_bool tag_eq_dec t t' && expr_eqb e1 e1'
  | _, _ => false
  end.

Lemma expr_eqb_true : forall e e', expr_eqb e e' = true -> e = e'.
Proof.
  induction e using expr_IH; destruct e'; cbn [expr_eqb]; intro Heq; try discriminate;
    repeat lazymatch goal with
      | E : (_ && _)%bool = true |- _ => apply andb_prop in E as [ ? ? ]
      end;
    repeat lazymatch goal with
      | E : String.eqb _ _ = true |- _ => apply String.eqb_eq in E
      | E : dec_to_bool _ _ _ = true |- _ => apply dec_to_bool_true in E
      | IH : forall e', expr_eqb ?e e' = true -> ?e = e', E : expr_eqb ?e _ = true |- _ =>
          apply IH in E
      end;
    subst; try reflexivity.
  revert l0 Heq. induction H as [ | [ s e ] l He Hl IHl ];
    intros [ | [ s' e' ] l0 ] E; cbn in E; try discriminate; auto.
  apply andb_prop in E as [ E1 E2 ]. apply andb_prop in E1 as [ Es Ee ].
  apply String.eqb_eq in Es. apply He in Ee. cbn in Es, Ee; subst.
  apply IHl in E2. injection E2 as E2. subst. reflexivity.
Qed.

Inductive invariant :=
  ConstraintInv (tbl : string) (path : list string) (row : string) (cond : expr)
| IndexInv (tbl : string) (id_path : list string) (aux_path : list string) (hole : string) (to_idx : expr).

(* Commands *)
Inductive command : Type :=
| CSkip
| CSeq (c1 c2 : command)
| CLet (e : expr) (x : string) (c : command)
| CLetMut (e : expr) (x : string) (ot : option type) (c : command)
| CAssign(x : string) (e : expr)
| CIf (e : expr) (c1 c2 : command)
| CForeach (e : expr) (x : string) (c : command).
