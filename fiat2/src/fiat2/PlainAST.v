Require Import String.
Require Import ZArith.
Require Import List Sorted.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
Require Import coqutil.Byte coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Tactics.Tactics.
Require Import Std.Sorting.Mergesort.
Require Import Coq.Sorting.Permutation.

(* ===== Fiat2 types ===== *)
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

Scheme Boolean Equality for type. (* creates type_beq *)
Declare Scope fiat2_scope. Local Open Scope fiat2_scope.
Notation "t1 =? t2" := (type_beq t1 t2) (at level 70) : fiat2_scope.

(* ===== Abstract syntax tree ===== *)

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
| EFold (e1 e2 : expr) (x y : string) (e3 : expr)
| ERecord (l : list (string * expr))
| EAccess (r : expr) (s : string)
| EDict (l : list (expr * expr))
| EInsert (d k v : expr)
| EDelete (d k : expr)
| ELookup (d k : expr)
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

(* ===== Interpreter ===== *)
Require Import coqutil.Word.Interface.
Require Import Coq.Numbers.DecimalString.
Require Import coqutil.Word.Properties.
Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.

  Inductive value :=
  | VWord (w : word)
  | VInt (z : Z)
  | VBool (b : bool)
  | VString (s : string)
  | VOption (m : option value)
  | VList (l : list value)
  | VRecord (l : list (string * value))
  | VDict (l : list (value * value))
  | VUnit.

  Definition interp_atom (a : atom) : value :=
    match a with
    | AWord n => VWord (word.of_Z n)
    | AInt n => VInt n
    | ABool b => VBool b
    | AString s => VString s
    | ANone _ => VOption None
    | ANil _ => VList nil
    | AUnit => VUnit
    end.

  Definition interp_unop (o : unop) (v : value) : value :=
    match o with
    | OWNeg => match v with
               | VWord w => VWord (word.opp w)
               | _ => VUnit
               end
    | ONeg => match v with
              | VInt z => VInt (Z.opp z)
              | _ => VUnit
              end
    | ONot => match v with
              | VBool b => VBool (negb b)
              | _ => VUnit
              end
    | OLength => match v with
                 | VList l => VInt (Z.of_nat (length l))
                 | _ => VUnit
                 end
    | OLengthString => match v with
                       | VString s => VInt (Z.of_nat (String.length s))
                       | _ => VUnit
                       end
    | OIntToString => match v with
                      | VInt z => VString (DecimalString.NilZero.string_of_int (BinInt.Z.to_int z))
                      | _ => VUnit
                      end
    | OSome => VOption (Some v)
    end.

  Definition apply_word_binop (o : word -> word -> word) (a b : value) : value :=
    match a, b with
    | VWord a, VWord b => VWord (o a b)
    | _, _ => VUnit
    end.

  Definition apply_int_binop (o : Z -> Z -> Z) (a b : value) : value :=
    match a, b with
    | VInt a, VInt b => VInt (o a b)
    | _, _ => VUnit
    end.

  Definition apply_bool_binop (o : bool -> bool -> bool) (a b : value) : value :=
    match a, b with
    | VBool a, VBool b => VBool (o a b)
    | _, _ => VUnit
    end.

  Fixpoint eval_range (lo : Z) (len : nat) : list value :=
    match len with
    | 0%nat => nil
    | S n => VInt lo :: eval_range (lo + 1) n
    end.

  Fixpoint eval_range_word (lo : word) (len : nat) : list value :=
    match len with
    | 0%nat => nil
    | S n => VWord lo :: eval_range_word (word.add lo (word.of_Z 1)) n
    end.

  (* ===== Comparison ===== *)
  Scheme Equality for list.

  Section __.
    Context {A} (A_compare : A -> A -> comparison).
    Fixpoint list_compare (l l' : list A) : comparison :=
      match l, l' with
      | nil, nil => Eq
      | nil, _ => Lt
      | _, nil => Gt
      | h :: l, h' :: l' => match A_compare h h' with
                            | Eq => list_compare l l'
                            | _ as c => c
                            end
      end.
  End __.

  Definition pair_compare {A B : Type} (fst_compare : A -> A -> comparison) (snd_compare : B -> B -> comparison) (p1 p2 : A * B) : comparison :=
    let '(a1, b1) := p1 in
    let '(a2, b2) := p2 in
    match fst_compare a1 a2 with
    | Eq => snd_compare b1 b2
    | c => c
    end.

  Section WithValueCompare.
    Context (value_compare : value -> value -> comparison).

    Definition record_compare : list (string * value) -> list (string * value) -> comparison :=
      list_compare (pair_compare String.compare value_compare).

    Definition dict_compare : list (value * value) -> list (value * value) -> comparison :=
      list_compare (pair_compare value_compare value_compare).
  End WithValueCompare.

  Fixpoint value_compare (a b : value) : comparison :=
    match a, b with
    | VWord a, VWord b =>
        if word.eqb a b then Eq else if word.ltu a b then Lt else Gt
    | VInt a, VInt b =>
        Z.compare a b
    (* if Z.eqb a b then Eq else if Z.ltb a b then Lt else Gt *)
    | VBool a, VBool b =>
        Bool.compare a b (* if Bool.eqb a b then Eq else if andb (negb a) b then Lt else Gt *)
    | VString a, VString b =>
        String.compare a b (* if String.eqb a b then Eq else if String.ltb a b then Lt else Gt *)
    | VOption a, VOption b =>
        match a with
        |None => match b with None => Eq | _ => Lt end
        | Some a => match b with None => Gt | Some b => value_compare a b end
        end
    | VList a, VList b => list_compare value_compare a b
    | VRecord a, VRecord b => record_compare value_compare a b
    | VDict a, VDict b => dict_compare value_compare a b
    | VUnit, VUnit => Eq
    | VUnit, _ => Lt | _, VUnit => Gt
    | VBool _, _ => Lt | _, VBool _ => Gt
    | VWord _, _ => Lt | _, VWord _ => Gt
    | VInt _, _ => Lt | _, VInt _ => Gt
    | VString _, _ => Lt | _, VString _ => Gt
    | VOption _, _ => Lt | _, VOption _ => Gt
    | VList _, _ => Lt | _, VList _ => Gt
    | VRecord _, _ => Lt | _, VRecord _ => Gt
    end.

  Definition value_eqb (a b : value) : bool :=
    match value_compare a b with
    | Eq => true
    | _ => false
    end.

  Definition value_ltb (a b : value) : bool :=
    match value_compare a b with
    | Lt => true
    | _ => false
    end.

  Section ValueIH.
    Context (P : value -> Prop).
    Hypothesis (f_word : forall w : word, P (VWord w)) (f_int : forall z : Z, P (VInt z)) (f_bool : forall b : bool, P (VBool b)) (f_string : forall s : string, P (VString s))
      (f_option : forall m : option value, match m with Some v => P v | None => True end -> P (VOption m))
      (f_list : forall l : list value, Forall P l -> P (VList l))
      (f_record : forall l : list (string * value), Forall (fun v => P (snd v)) l -> P (VRecord l))
      (f_dict : forall l : list (value * value), Forall (fun v => P (fst v) /\ P (snd v)) l -> P (VDict l)) (f_unit : P VUnit).
    Section __.
      Context (value_IH : forall v, P v).
      Fixpoint list_value_IH (l : list value) : Forall P l :=
        match l as l0 return Forall P l0 with
        | nil => Forall_nil P
        | v :: l' => Forall_cons v (value_IH v) (list_value_IH l')
        end.
      Fixpoint record_value_IH (l : list (string * value)) : Forall (fun v => P (snd v)) l :=
        match l as l0 return Forall (fun v => P (snd v)) l0 with
        | nil => Forall_nil (fun v => P (snd v))
        | v :: l' => Forall_cons v (value_IH (snd v)) (record_value_IH l')
        end.
      Fixpoint dict_value_IH (l : list (value * value)) : Forall (fun v => P (fst v) /\ P (snd v)) l :=
        match l as l0 return Forall (fun v => P (fst v) /\ P (snd v)) l0 with
        | nil => Forall_nil (fun v => P (fst v) /\ P (snd v))
        | v :: l' => Forall_cons v (conj (value_IH (fst v)) (value_IH (snd v)))(dict_value_IH l')
        end.
    End __.
    Fixpoint value_IH (v : value) {struct v} : P v :=
      match v with
      | VWord w => f_word w
      | VInt z => f_int z
      | VBool b => f_bool b
      | VString s => f_string s
      | VOption m => f_option m match m with Some v => value_IH v | None => I end
      | VList l => f_list l (list_value_IH value_IH l)
      | VRecord l => f_record l (record_value_IH value_IH l)
      | VDict l => f_dict l (dict_value_IH value_IH l)
      | VUnit => f_unit
      end.
  End ValueIH.

  Definition is_antisym {A : Type} (cmp : A -> A -> comparison) := forall x y : A, cmp x y = CompOpp (cmp y x).

  Lemma antisym__pair_antisym : forall (A B : Type) (A_cmp : A -> A -> comparison) (B_cmp : B -> B -> comparison),
      is_antisym A_cmp -> is_antisym B_cmp -> is_antisym (pair_compare A_cmp B_cmp).
  Proof.
    intros A B A_cmp B_cmp HA HB. unfold is_antisym. intros [xa xb] [ya yb].
    simpl. rewrite HA, HB. destruct (A_cmp ya xa), (B_cmp yb xb); auto.
  Qed.

  Definition leb_from_compare {A : Type} (cmp : A -> A -> comparison) (x y : A) : bool :=
    match cmp x y with
    | Lt | Eq => true
    | Gt => false
    end.

  Definition is_total {A : Type} (leb : A -> A -> bool) : Prop :=
    forall x y, leb x y = true \/ leb y x = true.

  Lemma compare_antisym__leb_total : forall (A : Type) (cmp : A -> A -> comparison), is_antisym cmp -> is_total (leb_from_compare cmp).
  Proof.
    unfold is_antisym, is_total, leb_from_compare.
    intros A cmp H x y. rewrite H; destruct (cmp y x); intuition.
  Qed.

  Lemma string_compare_refl : forall s : string, String.compare s s = Eq.
  Proof.
    induction s; trivial. simpl. unfold Ascii.compare.
    rewrite N.compare_refl; trivial.
  Qed.

  Lemma value_compare_refl : forall v : value, value_compare v v = Eq.
    apply value_IH; auto; intros; simpl.
    - rewrite word.eqb_eq; trivial.
    - apply Z.compare_refl.
    - destruct b; trivial.
    - apply string_compare_refl.
    - destruct m; auto.
    - induction l; auto. simpl. inversion H; subst; auto.
      rewrite H2. apply IHl. assumption.
    - induction l; auto. destruct a. simpl.
      rewrite string_compare_refl. inversion H; subst; simpl in *.
      rewrite H2. apply IHl. assumption.
    - induction l; auto. destruct a; simpl.
      inversion H; subst; simpl in *. destruct H2.
      rewrite H0, H1. apply IHl. assumption.
  Qed.

  Lemma value_compare_antisym : is_antisym value_compare.
  Proof.
    intro u. apply (value_IH ((fun u => forall v, value_compare u v = CompOpp (value_compare v u))));
      destruct v; auto; intros; simpl.
    - repeat match goal with
             | |- context[word.eqb ?a ?b] => destruct (word.eqb_spec a b)
             | |- context[word.ltu ?a ?b] => destruct (word.ltu_spec a b)
             | H1: ?a <> ?b, H2: ?b = ?a |- _ => symmetry in H2; intuition
             end; auto; intuition.
      + exfalso. apply (Z.lt_asymm _ _ H1). assumption.
      + exfalso. apply H. apply (Z.le_antisymm _ _ H1) in H2.
        rewrite <-word.of_Z_unsigned. rewrite <-word.of_Z_unsigned at 1. congruence.
    - apply Z.compare_antisym.
    - destruct b, b0; auto.
    - apply String.compare_antisym.
    - destruct m, m0; auto.
    - revert l0. induction l; destruct l0; auto.
      simpl. inversion H; subst. pose proof (H2 v) as H2. destruct (value_compare v a) eqn:E.
      + rewrite H2. simpl. apply IHl. assumption.
      + rewrite H2. trivial.
      + rewrite H2. trivial.
    - revert l0. induction l as [| a l IHl]; destruct l0 as [| b l0]; auto. destruct a as [sa va], b as [sb vb].
      simpl. inversion H; subst. pose proof (H2 vb) as H2. simpl in *.
      rewrite String.compare_antisym. destruct (sb ?= sa)%string; simpl; auto. rewrite H2.
      destruct (value_compare vb va); simpl; auto.
    - revert l0. induction l as [| a l IHl]; destruct l0 as [| b l0]; auto. destruct a as [ka va], b as [kb vb].
      simpl. inversion H; subst. destruct H2 as [H2L H2R]. pose proof (H2L kb) as H2L. pose proof (H2R vb) as H2R.
      simpl in *. rewrite H2L, H2R. destruct (value_compare kb ka), (value_compare vb va); simpl; auto.
  Qed.

  Local Coercion is_true : bool >-> Sortclass.

  Definition value_leb := leb_from_compare value_compare.
  Lemma value_leb_total : is_total value_leb.
  Proof.
    apply compare_antisym__leb_total. exact value_compare_antisym.
  Qed.

  Definition record_entry_compare := pair_compare String.compare value_compare.
  Definition record_entry_leb := leb_from_compare record_entry_compare.
  Definition record_sort := Sectioned.sort record_entry_leb.
  Lemma record_entry_compare_antisym : is_antisym record_entry_compare.
  Proof.
    apply antisym__pair_antisym.
    - exact String.compare_antisym.
    - exact value_compare_antisym.
  Qed.
  Lemma record_entry_leb_total : is_total record_entry_leb.
  Proof.
    apply compare_antisym__leb_total. exact record_entry_compare_antisym.
  Qed.
  Lemma LocallySorted_record_sort : forall l, LocallySorted record_entry_leb (record_sort l).
  Proof.
    exact (Sectioned.LocallySorted_sort _ record_entry_leb record_entry_leb_total).
  Qed.

  Definition dict_entry_compare := pair_compare value_compare value_compare.
  Definition dict_entry_leb := leb_from_compare dict_entry_compare.
  Definition dict_sort := Sectioned.sort dict_entry_leb.
  Lemma dict_entry_compare_antisym : is_antisym dict_entry_compare.
  Proof.
    apply antisym__pair_antisym; exact value_compare_antisym.
  Qed.
  Lemma dict_entry_leb_total : is_total dict_entry_leb.
  Proof.
    apply compare_antisym__leb_total. exact dict_entry_compare_antisym.
  Qed.
  Lemma LocallySorted_dict_sort : forall l, LocallySorted dict_entry_leb (dict_sort l).
  Proof.
    exact (Sectioned.LocallySorted_sort _ dict_entry_leb dict_entry_leb_total).
  Qed.

  Definition record_type_entry_leb (p p' : (string * type)) : bool := String.leb (fst p) (fst p').
  Definition record_type_sort := Sectioned.sort record_type_entry_leb.
  Lemma record_type_entry_leb_total : is_total record_type_entry_leb.
  Proof.
    unfold is_total. intros p p'. destruct p as [s t], p' as [s' t'].
    unfold record_type_entry_leb; simpl. destruct (String.leb s s') eqn:E; auto.
    right. pose proof String.leb_total as H. destruct (H s s'); congruence.
  Qed.
  Lemma LocallySorted_record_type_sort : forall l, LocallySorted record_type_entry_leb (record_type_sort l).
  Proof.
    exact (Sectioned.LocallySorted_sort _ record_type_entry_leb record_type_entry_leb_total).
  Qed.
  (* ----- End of comparison ----- *)
  Definition interp_binop (o : binop) (a b : value) : value :=
    match o with
    | OWPlus => apply_word_binop word.add a b
    | OPlus => apply_int_binop Z.add a b
    | OWMinus => apply_word_binop word.sub a b
    | OMinus => apply_int_binop Z.sub a b
    | OWTimes => apply_word_binop word.mul a b
    | OTimes => apply_int_binop Z.mul a b
    | OWDivU => apply_word_binop word.divu a b
    | OWDivS => apply_word_binop word.divs a b
    | ODiv => apply_int_binop Z.div a b
    | OWModU => apply_word_binop word.modu a b
    | OWModS => apply_word_binop word.mods a b
    | OMod => apply_int_binop Z.modulo a b
    | OAnd => apply_bool_binop andb a b
    | OOr => apply_bool_binop orb a b
    | OConcat => match a, b with
                 | VList a, VList b => VList (app a b)
                 | _, _ => VUnit
                 end
    | OConcatString => match a, b with
                       | VString a, VString b => VString (String.append a b)
                       | _, _ => VUnit
                       end
    | OWLessU => match a, b with
                 | VWord a, VWord b => VBool (word.ltu a b)
                 | _, _ => VUnit
                 end
    | OWLessS => match a, b with
                 | VWord a, VWord b => VBool (word.lts a b)
                 | _, _ => VUnit
                 end
    | OLess => match a, b with
               | VInt a, VInt b => VBool (Z.ltb a b)
               | _, _ => VUnit
               end
    | OEq => VBool (value_eqb a b)
    | ORepeat => match a, b with
                 | VList l, VInt n => VList (concat (repeat l (Z.to_nat n)))
                 | _, _ => VUnit
                 end
    | OCons => match b with
               | VList l => VList (cons a l)
               | _ => VUnit
               end
    | ORange => match a, b with
                | VInt s, VInt e => VList (eval_range s (Z.to_nat (e - s)))
                |_,  _ => VUnit
                end
    | OWRange => match a, b with
                 | VWord s, VWord e => VList (eval_range_word s (Z.to_nat (word.unsigned e - word.unsigned s)))
                 | _, _ => VUnit
                 end
    end.

  Fixpoint record_proj (s : string) (l : list (string * value)) : value :=
    match l with
    | nil => VUnit
    | (s', v) :: l => if String.eqb s s' then v else record_proj s l
    end.

  Fixpoint dict_insert (k v : value) (l : list (value * value)) : list (value * value) :=
    match l with
    | nil => (k, v) :: nil
    | (k', v) :: l => if value_ltb k k' then (k, v) :: (k', v) :: l
                      else if value_eqb k k' then (k, v) :: l
                           else (k', v) :: dict_insert k v l
    end.

  Fixpoint dict_delete (k : value) (l : list (value * value)) : list (value * value) :=
    match l with
    | nil => nil
    | (k', v) :: l => if value_eqb k k' then l else (k', v) :: dict_delete k l
    end.

  Fixpoint dict_lookup (k : value) (l : list (value * value)) : option value :=
    match l with
    | nil => None
    | (k', v) :: l => if value_eqb k k' then Some v else dict_lookup k l
    end.

  Section WithMap.
    Context {locals: map.map string value} {locals_ok: map.ok locals}.
    Definition get_local (l : locals) (x : string) : value :=
      match map.get l x with
      | Some v => v
      | None => VUnit
      end.

    Definition set_local (l : locals) (x : string) (v : value) :
      locals := map.put l x v.

    Fixpoint interp_expr (store env : locals) (e : expr) : value :=
      match e with
      | EVar x => get_local env x
      | ELoc x => get_local store x
      | EAtom a => interp_atom a
      | EUnop o e => interp_unop o (interp_expr store env e)
      | EBinop o e1 e2 => interp_binop o (interp_expr store env e1) (interp_expr store env e2)
      | EIf e1 e2 e3 => match interp_expr store env e1 with
                        | VBool b => if b then interp_expr store env e2 else interp_expr store env e3
                        | _ => VUnit
                        end
      | ELet e1 x e2 => interp_expr store (set_local env x (interp_expr store env e1)) e2
      | EFlatmap e1 x e2 =>
          match interp_expr store env e1 with
          | VList l1 => VList (flat_map (fun v => match interp_expr store (set_local env x v) e2 with
                                                  | VList l2 => l2
                                                  | _ => nil
                                                  end) l1)
          | _ => VUnit
          end
      | EFold e1 e2 x y e3 =>
          match interp_expr store env e1 with
          | VList l1 => let a := interp_expr store env e2 in
                        let f := fun v acc => interp_expr store (set_local (set_local env x v) y acc) e3 in
                        fold_right f a l1
          | _ => VUnit
          end
      | ERecord l => VRecord (record_sort
                                (List.map (fun '(s, e) => (s, (interp_expr store env e))) l))
      | EAccess r s => match interp_expr store env r with
                       | VRecord l => record_proj s l
                       | _ => VUnit
                       end
      | EDict l => VDict (dict_sort
                            (List.map (fun '(k, v) => (interp_expr store env k, interp_expr store env v)) l))
      | EInsert d k v =>
          match interp_expr store env d with
          | VDict l => VDict (dict_insert (interp_expr store env k) (interp_expr store env v) l)
          | _ => VUnit
          end
      | EDelete d k =>
          match interp_expr store env d with
          | VDict l => VDict (dict_delete (interp_expr store env k) l)
          | _ => VUnit
          end
      | ELookup d k =>
          match interp_expr store env d with
          | VDict l => VOption (dict_lookup (interp_expr store env k) l)
          | _ => VUnit
          end
      | EFilter l x p =>
          match interp_expr store env l with
          | VList l => VList (List.filter
                                (fun v =>
                                   let env' := set_local env x v in
                                   match interp_expr store env' p with
                                   | VBool b => b
                                   | _ => false
                                   end) l)
          | _ => VUnit
          end
      | EJoin l1 l2 x y p r =>
          match interp_expr store env l1 with
          | VList l1 =>
              match interp_expr store env l2 with
              | VList l2 => VList (flat_map
                                     (fun v1 =>
                                        List.map
                                          (fun v2 => let env' := set_local (set_local env x v1) y v2 in
                                                            interp_expr store env' r)
                                          (List.filter
                                             (fun v2 => let env' := set_local (set_local env x v1) y v2 in
                                                        match interp_expr store env' p with
                                                        | VBool b => b
                                                        | _ => false
                                                        end)
                                             l2))
                                     l1)
              | _ => VUnit
              end
          | _ => VUnit
          end
      | EProj l x r =>
          match interp_expr store env l with
          | VList l => VList (List.map (fun v => interp_expr store (set_local env x v) r) l)
          | _ => VUnit
          end
      end.

    Fixpoint interp_command (store env : locals) (c : command) : locals :=
      match c with
      | CSkip => store
      | CSeq c1 c2 =>
          let store' := interp_command store env c1 in
          interp_command store' env c2
      | CLet e x c =>
          let env' := set_local env x (interp_expr store env e) in
          interp_command store env' c
      | CLetMut e x c1 =>
          let store' := set_local store x (interp_expr store env e) in
          let store'' := interp_command store' env c1 in
          map.update store'' x (map.get store x)
      | CAssign x e => set_local store x (interp_expr store env e)
      | CIf e c1 c2 => match interp_expr store env e with
                       | VBool b => if b then interp_command store env c1 else interp_command store env c2
                       | _ => store (* unreachable cases *)
                       end
      | CForeach e x c =>
          match interp_expr store env e with
          | VList l => fold_left (fun store' v => interp_command store' (set_local env x v) c) l store
          | _ => store (* unreachable cases *)
          end
      end.
  End WithMap.

  (* ===== Order of entries in record and dict ===== *)
  Fixpoint record_wf (l : list (string * value)) : Prop :=
    match l with
    | nil => True
    | (s, v) :: l' => (forall s' v', In (s', v') l' -> String.ltb s s' = true)
                      /\ record_wf l'
    end.

  Fixpoint dict_wf (l : list (value * value)) : Prop :=
    match l with
    | nil => True
    | (k, v) :: l' => (forall k' v', In (k', v') l' -> value_ltb k k' = true)
                      /\ dict_wf l'
    end.
End WithWord.

(* ===== Bidirectional type checking ===== *)
Fixpoint type_eqb (t t' : type) {struct t} : bool :=
  match t, t' with
  | TWord, TWord
  | TInt, TInt
  | TBool, TBool
  | TString, TString
  | TUnit, TUnit => true
  | TOption t1, TOption t1' => type_eqb t1 t1'
  | TList t1, TList t1' => type_eqb t1 t1'
  | TRecord l, TRecord l' => list_beq _ (fun p p' => andb (String.eqb (fst p) (fst p'))
                                                       (type_eqb (snd p) (snd p'))) l l'
  | TDict kt vt, TDict kt' vt' => andb (type_eqb kt kt') (type_eqb vt vt')
  | _, _ => false
  end.

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

Lemma type_eqb_eq : forall t t', type_eqb t t' = true -> t = t'.
Proof.
  apply (type_IH (fun t => forall t', type_eqb t t' = true -> t = t')); intros;
    destruct t'; try discriminate; simpl in *; intuition;
  try (apply H in H0; congruence).
  - generalize dependent l0. induction l; destruct l0; simpl in *; try discriminate; intuition.
    destruct (andb (fst a =? fst p)%string (type_eqb (snd a) (snd p))) eqn:E; simpl in *; try discriminate.
    inversion H; subst. apply (IHl H4) in H0. injection H0; intros; subst.
    destruct a, p; inversion H; simpl in *; subst. apply andb_prop in E as [EL ER].
    rewrite eqb_eq in EL. apply H3 in ER. congruence.
  - apply andb_prop in H1 as [HL HR]. apply H in HL; apply H0 in HR. congruence.
Qed.

Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.

Definition compare_types (expected : type) (t : type) {A : Type} (a : A): result A :=
  if type_eqb expected t then Success a else error:(a "has type" t "but expected" expected).

Definition analyze_atom (expected : type) (a : atom) : result atom :=
  match a with
  | AWord n => compare_types expected TWord a
  | AInt n => compare_types expected TInt a
  | ABool b => compare_types expected TBool a
  | AString s => compare_types expected TString a
  | ANone t => match t with
               | Some t => compare_types expected (TOption t) a
               | None => match expected with
                         | TOption t' => Success (ANone (Some t'))
                         | _ => error:(a "is an option but expected" expected)
                         end
               end
  | ANil t => match t with
              | Some t => compare_types expected (TList t) a
              | None => match expected with
                        | TList t' => Success (ANil (Some t'))
                        | _ => error:(a "is a list but expected" expected)
                        end
              end
  | AUnit => compare_types expected TUnit a
  end.

(* Inductive typing relation *)
Inductive type_of_atom : atom -> type -> Prop :=
| TyAWord n : type_of_atom (AWord n) TWord
| TyAInt n : type_of_atom (AInt n) TInt
| TyABool b : type_of_atom (ABool b) TBool
| TyAString s : type_of_atom (AString s) TString
| TyANil' t : type_of_atom (ANil None) (TList t)
| TyANil t : type_of_atom (ANil (Some t)) (TList t)
| TyANone' t : type_of_atom (ANone None) (TOption t)
| TyANone t : type_of_atom (ANone (Some t)) (TOption t)
| TyAUnit : type_of_atom AUnit TUnit.

(* Computable type-checker *)
Definition synthesize_atom (a : atom) : result (type * atom) :=
  match a with
  | AWord n => Success (TWord, a)
  | AInt n => Success (TInt, a)
  | ABool b => Success (TBool, a)
  | AString s => Success (TString, a)
  | ANone t => match t with
               | Some t => Success (TOption t, a)
               | None => error:("Insufficient type information for" a)
               end
  | ANil t => match t with
              | Some t => Success (TList t, a)
              | None => error:("Insufficient type information for" a)
              end
  | AUnit => Success (TUnit, a)
  end.

Definition unop_types (o : unop) : (type * type) :=
  match o with
  | OWNeg => (TWord, TWord)
  | ONeg => (TInt, TInt)
  | ONot => (TBool, TBool)
  | OLengthString => (TString, TInt)
  | OIntToString => (TInt, TString)
  | _ => (TUnit, TUnit) (* unused *)
  end.

Definition binop_types (o : binop) : (type * type * type) :=
  match o with
  | OWPlus | OWMinus | OWTimes | OWDivU | OWDivS | OWModU | OWModS => (TWord, TWord, TWord)
  | OPlus | OMinus | OTimes | ODiv | OMod => (TInt, TInt, TInt)
  | OConcatString => (TString, TString, TString)
  | OAnd | OOr => (TBool, TBool, TBool)
  | OWLessU | OWLessS => (TWord, TWord, TBool)
  | OLess => (TInt, TInt, TBool)
  | OWRange => (TWord, TWord, TList TWord)
  | ORange => (TInt, TInt, TList TInt)
  | _ => (TUnit, TUnit, TUnit) (* unused *)
  end.

Inductive type_of_unop : unop -> type -> type -> Prop :=
| TyOWNeg : type_of_unop OWNeg TWord TWord
| TyONeg : type_of_unop ONeg TInt TInt
| TyONot : type_of_unop ONot TBool TBool
| TyOLength t : type_of_unop OLength (TList t) TInt
| TyOLengthString : type_of_unop OLengthString TString TInt
| TyOIntToString : type_of_unop OIntToString TInt TString
| TyOSome t : type_of_unop OSome t (TOption t).

Inductive type_of_binop : binop -> type -> type -> type -> Prop :=
| TyOWPlus : type_of_binop OWPlus TWord TWord TWord
| TyOPlus : type_of_binop OPlus TInt TInt TInt
| TyOWMinus : type_of_binop OWMinus TWord TWord TWord
| TyOMinus : type_of_binop OMinus TInt TInt TInt
| TyOWTimes : type_of_binop OWTimes TWord TWord TWord
| TyOTimes : type_of_binop OTimes TInt TInt TInt
| TyOWDivU : type_of_binop OWDivU TWord TWord TWord
| TyOWDivS : type_of_binop OWDivS TWord TWord TWord
| TyODiv : type_of_binop ODiv TInt TInt TInt
| TyOWModU : type_of_binop OWModU TWord TWord TWord
| TyOWModS : type_of_binop OWModS TWord TWord TWord
| TyOMod : type_of_binop OMod TInt TInt TInt
| TyOAnd : type_of_binop OAnd TBool TBool TBool
| TyOOr : type_of_binop OOr TBool TBool TBool
| TyOConcat t : type_of_binop OConcat (TList t) (TList t) (TList t)
| TyOConcatString : type_of_binop OConcatString TString TString TString
| TyOWLessU : type_of_binop OWLessU TWord TWord TBool
| TyOWLessS : type_of_binop OWLessS TWord TWord TBool
| TyOLess : type_of_binop OLess TInt TInt TBool
| TyOEq t : type_of_binop OEq t t TBool
| TyORepeat t : type_of_binop ORepeat (TList t) TInt (TList t)
| TyOCons t :  type_of_binop OCons t (TList t) (TList t)
| TyORange : type_of_binop ORange TInt TInt (TList TInt)
| TyOWRange : type_of_binop OWRange TWord TWord (TList TWord).

(* Whether a is in l *)
Fixpoint inb {A : Type} (A_eqb : A -> A -> bool) (l : list A) (a : A) : bool :=
  match l with
  | nil => false
  | h :: l => if A_eqb h a then true else inb A_eqb l a
  end.

(* Whether l is included in m *)
Definition inclb {A : Type} (A_eqb : A -> A -> bool) (l m : list A) : bool :=
  forallb (inb A_eqb m) l.

Fixpoint get_attr_type (tl : list (string * type)) (s : string) : type :=
  match tl with
  | nil => TUnit
  | (s', t) :: tl => if String.eqb s' s then t else get_attr_type tl s
  end.

Fixpoint record_type_from' (l : list (string * result (type * expr))) : result (list (string * type) * list (string * expr)) :=
  match l with
  | nil => Success (nil, nil)
  | (s, Success (t, e)) :: l => '(tl, el) <- record_type_from' l ;;
                                if inb (String.eqb) (List.map fst l) s then error:("Duplicate record key" s)
                                else Success ((s, t) :: tl, (s, e) :: el)
  | (_, Failure err) :: _ => Failure err
  end.

Definition record_type_from (l : list (string * result (type * expr))) : result (type * expr) :=
  '(tl, el) <- record_type_from' l ;; Success (TRecord (record_type_sort tl), ERecord el).

Fixpoint record_from' (l : list (string * result expr)) : result (list (string * expr)) :=
  match l with
  | nil => Success nil
  | (s, Success e) :: l => l' <- record_from' l ;;
                           if inb (String.eqb) (List.map fst l) s then error:("Duplicate record key" s)
                           else Success ((s, e) :: l')
  | (_, Failure err) :: _ => Failure err
  end.

Definition record_from (l : list (string * result expr)) : result expr :=
  l' <- record_from' l ;; Success (ERecord l').

Fixpoint proj_record_type (l : list (string * type)) (s : string) : result type :=
  match l with
  | nil => error:("Attribute" s "not found in record")
  | (s0, t) :: l => if String.eqb s s0 then Success t else proj_record_type l s
  end.

Fixpoint proj_record_field' (l : list (string * expr)) (s : string) : result expr :=
  match l with
  | nil => error:("Attribute" s "not found in record")
  | (s0, e) :: l => if String.eqb s s0 then Success e else proj_record_field' l s
  end.

Definition proj_record_field (e : expr) (s : string) : result expr :=
  match e with
  | ERecord l => proj_record_field' l s
  | _ => error:(e "is not a record")
  end.

Fixpoint first_success (l : list (result (type * expr))) :  result type :=
  match l with
  | nil => error:("Insufficient type information")
  | Success (t, e) :: l => Success t
  | _ :: l => first_success l
  end.

Fixpoint dict_type_from' (l : list (result (type * expr * type * expr))) : result (type * type * list (expr * expr)) :=
  match l with
  | nil => error:("Insufficient type information for dictionary")
  | Success (kt, ke, vt, ve) :: nil => Success (kt, vt, (ke, ve) :: nil)
  | Success (kt, ke, vt, ve) :: l => '(kt0, vt0, el) <- dict_type_from' l ;;
                                     if andb (type_eqb kt kt0) (type_eqb vt vt0) then Success (kt0, vt0, (ke, ve) :: el)
                                     else error:(ke "has type" kt "and" ve "has type" vt "but expected" kt0 "and" vt0 "respectively")
  | Failure err :: _ => Failure err
  end.

Definition dict_type_from (l : list (result (type * expr * type * expr))) : result (type * expr) :=
  '(kt, vt, el) <- dict_type_from' l ;; Success (TDict kt vt, EDict el).

Fixpoint dict_from' (l : list (result (expr * expr))) : result (list (expr * expr)) :=
  match l with
  | nil => Success nil
  | Success (k, v) :: l => l' <- dict_from' l ;; Success ((k, v) :: l')
  | Failure err :: _ => Failure err
  end.

Definition dict_from (l : list (result (expr * expr))) : result expr :=
  l' <- dict_from' l ;; Success (EDict l').


    Lemma NoDup_In_get_attr_type : forall tl,  NoDup (List.map fst tl) -> forall s t, In (s, t) tl -> get_attr_type tl s = t.
    Proof.
      clear. induction tl; simpl; intros.
      - intuition.
      - destruct a. destruct (String.eqb s0 s) eqn:E.
        + intuition; try congruence. rewrite String.eqb_eq in E; inversion H; subst.
          assert (In s (List.map fst tl)).
          { clear H H3 H4 IHtl. induction tl; auto. destruct a; inversion H1; subst; simpl.
            - left; congruence.
            - right; auto. }
          intuition.
        + inversion H; subst. apply IHtl; auto. destruct H0; auto.
          rewrite String.eqb_neq in E; inversion H0; congruence.
    Qed.

    Lemma Permutation_NoDup_In_get_attr_type : forall tl tl',
        Permutation tl tl' -> NoDup (List.map fst tl') ->
        forall s, In s (List.map fst tl') -> get_attr_type tl s = get_attr_type tl' s.
    Proof.
      intros.
      assert (exists t, In (s, t) tl').
      { clear H H0. induction tl'; simpl in *; intuition.
        - exists (snd a). left; subst. apply surjective_pairing.
        - destruct H0 as [t Ht]. firstorder. }
      assert (NoDup (List.map fst tl)).
      { apply Permutation_map with (f := fst) in H. apply Permutation_sym in H.
        eapply Permutation_NoDup; eauto. }
      destruct H2 as [t Ht]. repeat rewrite NoDup_In_get_attr_type with (t := t); auto.
      apply Permutation_sym in H. eapply Permutation_in; eauto.
    Qed.

    Lemma Permutation_incl : forall A (l l' : list A), Permutation l l' -> incl l l'.
    Proof.
      intros. unfold incl; intros.
      eapply Permutation_in; eauto.
    Qed.

    (* below 6 lemmas should be moved to coq utils
       used in relational algebra filter/join conversions *)

    (* filter of a flat_map = flat_map where filter is applied in the flat_map function*)
    Lemma filter_flat_map {A B : Type} (p : B -> bool) (f : A -> list B) (l : list A) :
      filter p (flat_map f l) = flat_map (fun x => filter p (f x)) l.
      induction l as [| h t IHn].
      - simpl. reflexivity.
      - simpl. rewrite filter_app. f_equal. apply IHn.
    Qed.

    (* for maps from A->A: filtering a map = doing a map on the filtered list*)
    Lemma filter_map_commute {A : Type} (f : A -> A) (p : A -> bool) (l : list A) :
      filter p (List.map f l) = List.map f (filter (fun x => p (f x)) l).
      induction l as [| h t IHn].
      - simpl. reflexivity.
      - simpl. destruct (p (f h)).
        + simpl. f_equal. apply IHn.
        + apply IHn.
    Qed.

    (* filter on another filtered list = filter on original list where function "and"s the two predicates*)
    Lemma filter_filter {A : Type} (p1 p2 : A -> bool) (l : list A) :
      filter p1 (filter p2 l) = filter (fun x => andb (p1 x) (p2 x)) l.
      induction l as [| h t IHn].
      - simpl. reflexivity.
      - simpl. destruct (p2 h).
        + simpl. destruct (p1 h).
          * simpl. f_equal. apply IHn.
          * simpl. apply IHn.
        + destruct (p1 h); apply IHn.
    Qed.

    (* flat_map of a filtered list = flat_map where filter is applied in the flat_map function*)
    Lemma flat_map_filter {A B : Type} (f : A -> list B) (p : A -> bool) (l : list A) :
      flat_map f (filter p l) = flat_map (fun x => if p x then f x else @nil B) l.
      induction l as [| h t IH].
      - simpl. reflexivity.
      - simpl. destruct (p h) eqn:H.
        + simpl. rewrite IH. reflexivity.
        + rewrite IH. reflexivity.
    Qed.

    Lemma filter_nil : forall (A : Type) (f : A -> bool) (l : list A),
        (forall x : A, In x l -> f x = false) -> filter f l = nil.
      intros A f l H.
      induction l as [|h t IH].
      - simpl. reflexivity.
      - simpl. rewrite H.
        + apply IH. intros h' H'. apply H. right. apply H'.
        + left. reflexivity.
    Qed.

    Lemma map_nil : forall (A B : Type) (f : A -> B) (l : list A),
        l = nil -> List.map f l = nil.
      intros A B f l H.
      rewrite H. simpl. reflexivity.
    Qed.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.

  Local Coercion is_true : bool >-> Sortclass.

  Inductive type_of (Gstore Genv : tenv) : expr -> type -> Prop :=
  | TyEVar x t : map.get Genv x = Some t -> type_of Gstore Genv (EVar x) t
  | TyELoc x t : map.get Gstore x = Some t -> type_of Gstore Genv (ELoc x) t
  | TyEAtom a t : type_of_atom a t -> type_of Gstore Genv (EAtom a) t
  | TyEUnop o e t1 t2 : type_of_unop o t1 t2 ->
                        type_of Gstore Genv e t1 ->
                        type_of Gstore Genv (EUnop o e) t2
  | TyEBinop o e1 e2 t1 t2 t3 : type_of_binop o t1 t2 t3 ->
                                type_of Gstore Genv e1 t1 ->
                                type_of Gstore Genv e2 t2 ->
                                type_of Gstore Genv (EBinop o e1 e2) t3
  | TyEIf e1 e2 e3 t : type_of Gstore Genv e1 TBool ->
                       type_of Gstore Genv e2 t ->
                       type_of Gstore Genv e3 t ->
                       type_of Gstore Genv (EIf e1 e2 e3) t
  | TyELet e1 t1 x e2 t2 : type_of Gstore Genv e1 t1 ->
                           type_of Gstore (map.put Genv x t1) e2 t2 ->
                           type_of Gstore Genv (ELet e1 x e2) t2
  | TyEFlatmap e1 t1 x e2 t2 : type_of Gstore Genv e1 (TList t1) ->
                               type_of Gstore (map.put Genv x t1) e2 (TList t2) ->
                               type_of Gstore Genv (EFlatmap e1 x e2) (TList t2)
  | TyEFold e1 t1 e2 t2 x y e3 : type_of Gstore Genv e1 (TList t1) ->
                                 type_of Gstore Genv e2 t2 ->
                                 type_of Gstore (map.put (map.put Genv x t1) y t2) e3 t2 ->
                                 type_of Gstore Genv (EFold e1 e2 x y e3) t2
  | TyERecord (l : list (string * expr)) (tl tl' : list (string * type)) :
    List.map fst l = List.map fst tl ->
    Forall2 (type_of Gstore Genv) (List.map snd l) (List.map snd tl) ->
    NoDup (List.map fst l) ->
    Permutation tl tl' ->
    StronglySorted record_type_entry_leb tl' ->
    type_of Gstore Genv (ERecord l) (TRecord tl')
  | TyEAccess e tl x t : type_of Gstore Genv e (TRecord tl) ->
                         In (x, t) tl ->
                         type_of Gstore Genv (EAccess e x) t
  | TyEDict l kt vt : Forall (fun p => type_of Gstore Genv (fst p) kt /\ type_of Gstore Genv (snd p) vt) l ->
                      type_of Gstore Genv (EDict l) (TDict kt vt)
  (* ??? Why is this a non-strictly positive occurrence of type_of? Forall (fun '(k, v) => type_of Gstore Genv k kt /\ type_of Gstore Genv v vt) l -> type_of Gstore Genv (EDict l) (TDict kt vt). *)
  | TyInsert d kt vt k v : type_of Gstore Genv d (TDict kt vt) ->
                           type_of Gstore Genv k kt ->
                           type_of Gstore Genv v vt ->
                           type_of Gstore Genv (EInsert d k v) (TDict kt vt)
  | TyDelete d kt vt k : type_of Gstore Genv d (TDict kt vt) ->
                           type_of Gstore Genv k kt ->
                           type_of Gstore Genv (EDelete d k) (TDict kt vt)
  | TyLookup d kt vt k : type_of Gstore Genv d (TDict kt vt) ->
                         type_of Gstore Genv k kt ->
                         type_of Gstore Genv (ELookup d k) (TOption vt)
  | TyEFilter e t x p : type_of Gstore Genv e (TList t) ->
                        type_of Gstore (map.put Genv x t) p TBool ->
                        type_of Gstore Genv (EFilter e x p) (TList t)
  | TyEJoin e1 t1 e2 t2 x y p r t3 : type_of Gstore Genv e1 (TList t1) ->
                                     type_of Gstore Genv e2 (TList t2) ->
                                     type_of Gstore (map.put (map.put Genv x t1) y t2) p TBool ->
                                     type_of Gstore (map.put (map.put Genv x t1) y t2) r t3 ->
                                     type_of Gstore Genv (EJoin e1 e2 x y p r) (TList t3)
  | TyEProj e t1 x r t2 : type_of Gstore Genv e (TList t1) ->
                          type_of Gstore (map.put Genv x t1) r t2 ->
                          type_of Gstore Genv (EProj e x r) (TList t2).

  Section __.
    Context (analyze_expr : tenv -> tenv -> type -> expr -> result expr).

    Definition analyze_dict_body (Gstore Genv : tenv) (kt vt : type) (l : list (expr * expr)) :=
      dict_from (List.map (fun '(k, v) => k' <- analyze_expr Gstore Genv kt k ;;
                                          v' <- analyze_expr Gstore Genv vt v ;;
                                          Success (k', v')) l).
  End __.

  Fixpoint analyze_expr (Gstore Genv : tenv) (expected : type) (e : expr) : result expr :=
    match e with
    | EVar x => match map.get Genv x with
                | Some t => if type_eqb expected t then Success (EVar x)
                            else error:("Immutable variable" x "has type" t "but expected" expected)
                | None => error:(x "not found in the immutable variable type environment")
                end
    | ELoc x => match map.get Gstore x with
                | Some t => if type_eqb expected t then Success (ELoc x)
                            else error:("Mutable variable" x "has type" t "but expected" expected)
                | None => error:(x "not found in the mutable variable type environment")
                end
    | EAtom a => a' <- analyze_atom expected a ;; Success (EAtom a')
    | EUnop o e1 => match o with
                    | OLength => '(t, e') <- synthesize_expr Gstore Genv e1 ;;
                                 match t with
                                 | TList _ => if type_eqb expected TInt then Success (EUnop o e')
                                              else error:(e "has type" TInt "but expected" expected)
                                 | _ => error:(e1 "has type" t "but expected a list")
                                 end
                    | OSome => match expected with
                               | TOption t => analyze_expr Gstore Genv t e1
                               | _ => error:(e "is an option but expected" expected)
                               end
                    | o => let '(t1, t2) := unop_types o in
                           if type_eqb expected t2 then analyze_expr Gstore Genv t1 e1
                           else error:(e "has type" e1 "but expected" expected)
                    end
    | EBinop o e1 e2 => match o with
                        | OCons =>
                            match expected with
                            | TList t => e1' <- analyze_expr Gstore Genv t e1 ;; e2' <- analyze_expr Gstore Genv (TList t) e2 ;;
                                         Success (EBinop o e1' e2')
                            | _ => error:(e "is a list but expected" expected)
                            end
                        | OConcat =>
                            match expected with
                            | TList t => e1' <- analyze_expr Gstore Genv (TList t) e1 ;; e2' <- analyze_expr Gstore Genv (TList t) e2 ;;
                                         Success (EBinop o e1' e2')
                            | _ => error:(e "is a list but expected" expected)
                            end
                        | ORepeat =>
                            match expected with
                            | TList t => e1' <- analyze_expr Gstore Genv (TList t) e1 ;; e2' <- analyze_expr Gstore Genv TInt e2 ;;
                                         Success (EBinop o e1' e2')
                            | _ => error:(e "is a list but expected" expected)
                            end
                        | OEq =>
                            match expected with
                            | TBool => match synthesize_expr Gstore Genv e1 with
                                       | Success (t, e1') => e2' <- analyze_expr Gstore Genv t e2 ;;
                                                              Success (EBinop OEq e1' e2')
                                       | Failure err => '(t, e2') <- synthesize_expr Gstore Genv e2 ;;
                                                        e1' <- analyze_expr Gstore Genv t e1 ;;
                                                        Success (EBinop OEq e1' e2')
                                       end
                            | _ => error:(e "is a boolean but expected" expected)
                            end
                        | o => let '(t1, t2, t3) := binop_types o in
                               if type_eqb expected t3
                               then e1' <- analyze_expr Gstore Genv t1 e1 ;;
                                    e2' <- analyze_expr Gstore Genv t2 e2 ;;
                                    Success (EBinop o e1' e2')
                               else error:(e "has type" t3 "but expected" expected)
                        end
    | EIf e1 e2 e3 => e1' <- analyze_expr Gstore Genv TBool e1 ;;
                      e2' <- analyze_expr Gstore Genv expected e2 ;;
                      e3' <- analyze_expr Gstore Genv expected e3 ;;
                      Success (EIf e1' e2' e3')
    | ELet e1 x e2 => '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                      e2' <- analyze_expr Gstore (map.put Genv x t1) expected e2 ;;
                      Success (ELet e1' x e2')
    | EFlatmap e1 x e2 => match expected with
                          | TList t2 =>
                              '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                              match t1 with
                              | TList t1 => e2' <- analyze_expr Gstore (map.put Genv x t1) (TList t2) e2 ;;
                                            Success (EFlatmap e1' x e2')
                              | t1 => error:(e1 "has type" t1 "but expected a list")
                              end
                          | _ => error:(e "is a list but expected" expected)
                          end
    | EFold e1 e2 x y e3 => '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                            match t1 with
                            | TList t1 => e2' <- analyze_expr Gstore Genv expected e2 ;;
                                          e3' <- analyze_expr Gstore (map.put (map.put Genv x t1) y expected) expected e3 ;;
                                          Success (EFold e1' e2' x y e3')
                            | t1 => error:(e1 "has type" t1 "but expected a list")
                            end
    | ERecord l => match expected with
                   | TRecord tl =>
                       if type_eqb (TRecord tl) (TRecord (record_type_sort tl))
                       then
                         if leb (length tl) (length l)
                         then
                           if inclb String.eqb (List.map fst l) (List.map fst tl) &&
                                inclb String.eqb (List.map fst tl) (List.map fst l)
                           then record_from (List.map
                                               (fun '(s, e) => (s, analyze_expr Gstore Genv(get_attr_type tl s) e))
                                               l)
                           else error:(e "does not have all expected attributes" tl)
                         else error:("Record type" tl "has more fields than record" l)
                       else error:("Record type" tl "not sorted by record entry names")
                   | _ => error:(e "is a record but expected" expected)
                   end
    | EAccess e s => '(t, e') <- synthesize_expr Gstore Genv e ;;
                     match t with
                     | TRecord l => t <- proj_record_type l s ;;
                                    if type_eqb expected t then Success (EAccess e' s)
                                    else error:("Attribute" s "has type" t "but expected" expected)
                     | t => error:(e "has type" t "but expected a record")
                     end
    | EDict l => match expected with
                 | TDict kt vt => analyze_dict_body analyze_expr Gstore Genv kt vt l
                 | _ => error:(e "is a dictionary but expected" expected)
                 end
    | EInsert d k v => match expected with
                       | TDict kt vt =>
                           d' <- analyze_expr Gstore Genv (TDict kt vt) d ;;
                           k' <- analyze_expr Gstore Genv kt k ;;
                           v' <- analyze_expr Gstore Genv vt v ;;
                           Success (EInsert d' k' v')
                       | _ => error:(e "is a dictionary but expected" expected)
                       end
    | EDelete d k => match expected with
                     | TDict kt vt =>
                         d' <- analyze_expr Gstore Genv (TDict kt vt) d ;;
                         k' <- analyze_expr Gstore Genv kt k ;;
                         Success (EDelete d' k')
                     | _ => error:(e "is a dictionary but expected" expected)
                     end
    | ELookup d k => '(t1, d') <- synthesize_expr Gstore Genv d ;;
                     match t1 with
                     | TDict kt vt => if type_eqb expected (TOption vt)
                                      then k' <- analyze_expr Gstore Genv kt k ;;
                                           Success (ELookup d' k')
                                      else error:(e "has type" (TOption vt) "but expected" expected)
                     | t => error:(e "has type" t "but expected a record")
                     end
    | EFilter l x p => match expected with
                       | TList t => l' <- analyze_expr Gstore Genv expected l ;;
                                    p' <- analyze_expr Gstore (map.put Genv x t) TBool p ;;
                                    Success (EFilter l' x p')
                       | _ => error:(e "is a list but expected" expected)
                       end
    | EJoin l1 l2 x y p r => '(t1, l1') <- synthesize_expr Gstore Genv l1 ;;
                             match t1 with
                             | TList t1 => '(t2, l2') <- synthesize_expr Gstore Genv l2 ;;
                                           match t2 with
                                           | TList t2 => let Genv' := map.put (map.put Genv x t1) y t2 in
                                                         p' <- analyze_expr Gstore Genv' TBool p ;;
                                                         match expected with
                                                         | TList t3 =>
                                                             r' <- analyze_expr Gstore Genv' t3 r ;;
                                                             Success (EJoin l1' l2' x y p' r')
                                                         | _ => error:(e "is a list but expected" expected)
                                                         end
                                           | t => error:(l2 "has type" t "but expected a list")
                                           end
                             | t => error:(l1 "has type" t "but expected a list")
                             end
    | EProj l x r => '(t1, l') <- synthesize_expr Gstore Genv l ;;
                     match t1 with
                     | TList t1 => match expected with
                                   | TList t2 => r' <- analyze_expr Gstore (map.put Genv x t1) t2 r ;;
                                                 Success (EProj l' x r')
                                   | _ => error:(e "is a list but expected" expected)
                                   end
                     | t => error:(l "has type" t "but expected a list")
                     end
    end

  with synthesize_expr (Gstore Genv : tenv) (e : expr) : result (type * expr) :=
         match e with
         | EVar x => match map.get Genv x with
                     | Some t => Success (t, e)
                     | None => error:(x "not found in the immutable variable type environment")
                     end
         | ELoc x => match map.get Gstore x with
                     | Some t => Success (t, e)
                     | None => error:(x "not found in the mutable variable type environment")
                     end
         | EAtom a => '(t, a') <- synthesize_atom a ;; Success (t, EAtom a')
         | EUnop o e => match o with
                        | OLength => '(t, e') <- synthesize_expr Gstore Genv e ;;
                                     match t with
                                     | TList _ => Success (TInt, EUnop o e')
                                     | _ => error:(e "has type" t "but expected a list")
                                     end
                        | OSome => '(t, e') <- synthesize_expr Gstore Genv e ;; Success (TOption t, EUnop o e')
                        | o => let '(t1, t2) := unop_types o in
                               e' <- analyze_expr Gstore Genv t1 e ;; Success (t2, EUnop o e')
                        end
         | EBinop o e1 e2 => match o with
                             | OCons =>
                                 match synthesize_expr Gstore Genv e1 with
                                 | Success (t, e1') => e2' <- analyze_expr Gstore Genv (TList t) e2 ;; Success (TList t, EBinop o e1' e2')
                                 | Failure err1 => '(t2, e2') <- synthesize_expr Gstore Genv e2 ;;
                                                   match t2 with
                                                   | TList t => e1' <- analyze_expr Gstore Genv t e1 ;; Success (TList t, EBinop o e1' e2')
                                                   | t => error:(e2 "has type" t "but expected a list")
                                                   end
                                 end
                             | OConcat =>
                                 match synthesize_expr Gstore Genv e1 with
                                 | Success (TList t, e1') => e2' <- analyze_expr Gstore Genv (TList t) e2 ;; Success (TList t, EBinop o e1' e2')
                                 | Success (t, _) => error:(e1 "has type" t "but expected a list")
                                 | Failure err1 => '(t2, e2') <- synthesize_expr Gstore Genv e2 ;;
                                                   match t2 with
                                                   | TList t => e1' <- analyze_expr Gstore Genv (TList t) e1 ;; Success (TList t, EBinop o e1' e2')
                                                   | t => error:(e2 "has type" t "but expected a list")
                                                   end
                                 end
                             | ORepeat =>
                                 '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                                 match t1 with
                                 | TList t => e2' <- analyze_expr Gstore Genv TInt e2 ;; Success (TList t, EBinop o e1' e2')
                                 | t => error:(e1 "has type" t "but expected a list")
                                 end
                             | OEq =>
                                 match synthesize_expr Gstore Genv e1 with
                                 | Success (t, e1') => e2' <- analyze_expr Gstore Genv t e2 ;; Success (TBool, EBinop o e1' e2')
                                 | Failure err => '(t, e2') <- synthesize_expr Gstore Genv e2 ;;
                                                  e1' <- analyze_expr Gstore Genv t e1 ;;
                                                  Success (TBool, EBinop o e1' e2')
                                 end
                             | o => let '(t1, t2, t3) := binop_types o in
                                    e1' <- analyze_expr Gstore Genv t1 e1 ;;
                                    e2' <- analyze_expr Gstore Genv t2 e2 ;;
                                    Success (t3, EBinop o e1' e2')
                             end
         | EIf e1 e2 e3 => e1' <- analyze_expr Gstore Genv TBool e1 ;;
                           match synthesize_expr Gstore Genv e2 with
                           | Success (t, e2') => e3' <- analyze_expr Gstore Genv t e3 ;; Success (t, EIf e1' e2' e3')
                           | Failure err2 => '(t, e3') <- synthesize_expr Gstore Genv e3 ;;
                                             e2' <- analyze_expr Gstore Genv t e2 ;; Success (t, EIf e1' e2' e3')
                           end
         | ELet e1 x e2 => '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                           '(t2, e2') <- synthesize_expr Gstore (map.put Genv x t1) e2 ;;
                           Success (t2, ELet e1' x e2')
         | EFlatmap e1 x e2 => '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                               match t1 with
                               | TList t1 => '(t2, e2') <- synthesize_expr Gstore (map.put Genv x t1) e2 ;;
                                             match t2 with
                                             | TList t2 => Success (TList t2, EFlatmap e1' x e2')
                                             | t2 => error:(e2 "has type" t2 "but expected a list")
                                             end
                               | t1 => error:(e1 "has type" t1 "but expected a list")
                               end
         | EFold e1 e2 x y e3 => '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                                 match t1 with
                                 | TList t1 => '(t2, e2') <- synthesize_expr Gstore Genv e2 ;;
                                               e3' <- analyze_expr Gstore (map.put (map.put Genv x t1) y t2) t2 e3 ;;
                                               Success (t2, EFold e1' e2' x y e3')
                                 | t1 => error:(e1 "has type" t1 "but expected a list")
                                 end
         | ERecord l => record_type_from (List.map (fun '(s, e') => (s, synthesize_expr Gstore Genv e')) l)
         | EAccess e s => '(t, e') <- synthesize_expr Gstore Genv e ;;
                          match t with
                          | TRecord l => t <- proj_record_type l s ;; Success (t, EAccess e' s)
                          | t => error:(e "has type" t "but expected a record")
                          end
         | EDict l => let kl := List.map (fun '(k, _) => synthesize_expr Gstore Genv k) l in
                      let vl := List.map (fun '(_, v) => synthesize_expr Gstore Genv v) l in
                      fst_kt <- first_success kl ;; fst_vt <- first_success vl ;;
                      d <- analyze_dict_body analyze_expr Gstore Genv fst_kt fst_vt l ;;
                      Success (TDict fst_kt fst_vt, d)

         | EInsert d k v => '(t1, d') <- synthesize_expr Gstore Genv d ;;
                            match t1 with
                            | TDict kt vt => k' <- analyze_expr Gstore Genv kt k ;;
                                             v' <- analyze_expr Gstore Genv vt v ;;
                                             Success (t1, EInsert d' k' v')
                            | t => error:(e "has type" t "but expected a record")
                            end
         | EDelete d k => '(t1, d') <- synthesize_expr Gstore Genv d ;;
                          match t1 with
                          | TDict kt _ => k' <- analyze_expr Gstore Genv kt k ;;
                                          Success (t1, EDelete d' k')
                          | t => error:(e "has type" t "but expected a record")
                          end
         | ELookup d k => '(t1, d') <- synthesize_expr Gstore Genv d ;;
                          match t1 with
                          | TDict kt vt => k' <- analyze_expr Gstore Genv kt k ;;
                                           Success (TOption vt, ELookup d' k')
                          | t => error:(e "has type" t "but expected a record")
                          end
         | EFilter l x p => '(t, l') <- synthesize_expr Gstore Genv l ;;
                              match t with
                              | TList t => p' <- analyze_expr Gstore (map.put Genv x t) TBool p ;;
                                           Success (TList t, EFilter l' x p')
                              | t => error:(l "has type" t "but expected a list")
                              end
         | EJoin l1 l2 x y p r => '(t1, l1') <- synthesize_expr Gstore Genv l1 ;;
                                  match t1 with
                                  | TList t1 => '(t2, l2') <- synthesize_expr Gstore Genv l2 ;;
                                                match t2 with
                                                | TList t2 => let Genv' := map.put (map.put Genv x t1) y t2 in
                                                              p' <- analyze_expr Gstore Genv' TBool p ;;
                                                              '(t3, r') <- synthesize_expr Gstore Genv' r ;;
                                                              Success (TList t3, EJoin l1' l2' x y p' r')
                                                | t => error:(l2 "has type" t "but expected a list")
                                                end
                                  | t => error:(l1 "has type" t "but expected a list")
                                  end
         | EProj l x r => '(t1, l') <- synthesize_expr Gstore Genv l ;;
                          match t1 with
                          | TList t1 => '(t2, r') <- synthesize_expr Gstore (map.put Genv x t1) r ;;
                                        Success (TList t2, EProj l' x r')
                          | t => error:(l "has type" t "but expected a list")
                          end
         end.

  (* ===== type soundness ===== *)
  Section WithWord.
    Context {width: Z} {word: word.word width}.
    Context {word_ok: word.ok word}.

    Local Notation value := (value (word := word)).
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    Inductive has_type : value -> type -> Prop :=
    | TyVWord w : has_type (VWord w) TWord
    | TyVInt n : has_type (VInt n) TInt
    | TyVBool b : has_type (VBool b) TBool
    | TyVString s : has_type (VString s) TString
    | TyVOptionNone t : has_type (VOption None) (TOption t)
    | TyVOptionSome v t : has_type v t ->
                          has_type (VOption (Some v)) (TOption t)
    | TyVList l t : Forall (fun v => has_type v t) l -> has_type (VList l) (TList t)
    | TyVRecordNil : has_type (VRecord nil) (TRecord nil)
    | TyVRecordCons s v l tv tl : has_type v tv ->
                                  has_type (VRecord l) (TRecord tl) ->
                                  has_type (VRecord ((s, v) :: l)) (TRecord ((s, tv) :: tl))
    | TyVDictNil tk tv : has_type (VDict nil) (TDict tk tv)
    | TyVDictCons k v l tk tv : has_type k tk ->
                                has_type v tv ->
                                has_type (VDict l) (TDict tk tv) ->
                                has_type (VDict ((k, v) :: l)) (TDict tk tv)
    | TyVUnit : has_type VUnit TUnit.

    Definition tenv_env_agree (G : tenv) (E : locals) :=
      forall x t, map.get G x = Some t ->
                  match map.get E x with
                  | Some v => has_type v t
                  | _ => False
                  end.

    Lemma typeof_to_hastype : forall (store env: locals) (Gstore Genv: tenv) (e: expr) (t: type),
      type_of Gstore Genv e t -> has_type (interp_expr store env e) t.
    Admitted.

    Theorem filter_into_join : forall (store env: locals) (Gstore Genv: tenv) (db1 db2 pj rj pf: expr) (xj yj xf: string) (t tx ty: type),
      type_of Gstore (map.put (map.put Genv xj tx) yj ty) pj (TList t) ->
      let pnew := EBinop OAnd pj (ELet rj xf pf) in
      interp_expr store env (EFilter (EJoin db1 db2 xj yj pj rj) xf pf)
      = interp_expr store env (EJoin db1 db2 xj yj pnew rj).
    Proof.
      intros store env Gstore Genv db1 db2 pj rj pf xj yj xf t tx ty H. simpl.
      destruct (interp_expr store env db1); try reflexivity.
      destruct (interp_expr store env db2); try reflexivity. f_equal.
      rewrite filter_flat_map. apply flat_map_ext. intros a.
      rewrite filter_map_commute. f_equal.
      rewrite filter_filter. apply filter_ext. intros b.
      apply typeof_to_hastype with store (set_local (set_local env xj a) yj b) Gstore (map.put (map.put Genv xj tx) yj ty) pj (TList t) in H.
      inversion H. rewrite Bool.andb_false_r. simpl. reflexivity.
    Qed.

    Lemma interp_invariant : forall (store env: locals) (Gstore Genv: tenv) (db: expr) (k: string) (v: value) (t: type),
      type_of Gstore Genv db t -> map.get Genv k = None ->
      interp_expr store env db = interp_expr store (set_local env k v) db.
    Proof.
      intros store env0 Gstore Genv db k v t T K.
      generalize env0 as env.
      induction T; intros env; simpl; try reflexivity.
      - unfold get_local, set_local. destruct (eqb k x) eqn:KX.
        + exfalso. rewrite String.eqb_eq in KX. rewrite KX in K. rewrite K in H. discriminate H.
        + rewrite String.eqb_neq in KX. rewrite map.get_put_diff.
          * reflexivity.
          * symmetry. apply KX.
      - rewrite IHT.
        + reflexivity.
        + apply K.
      - rewrite IHT1.
        + rewrite IHT2.
          * reflexivity.
          * apply K.
        + apply K.
      - rewrite IHT1.
        + rewrite IHT2.
          * rewrite IHT3.
            -- reflexivity.
            -- apply K.
          * apply K.
        + apply K.
      - rewrite <- IHT1.
        + destruct (eqb k x) eqn:KX.
          * rewrite String.eqb_eq in KX. rewrite KX. unfold set_local.
            rewrite Properties.map.put_put_same. reflexivity.
          * rewrite String.eqb_neq in KX. rewrite IHT2.
            -- unfold set_local. rewrite Properties.map.put_comm.
               ++ reflexivity.
               ++ symmetry. apply KX.
            -- rewrite map.get_put_diff.
               ++ apply K.
               ++ apply KX.
        + apply K.
      - rewrite <- IHT1.
        + destruct (interp_expr store env e1) eqn:H; try reflexivity.
          f_equal. apply flat_map_ext. intros a. destruct (eqb k x) eqn:KX.
          * rewrite String.eqb_eq in KX. rewrite KX. unfold set_local.
            rewrite Properties.map.put_put_same. reflexivity.
          * rewrite String.eqb_neq in KX. rewrite IHT2.
            -- unfold set_local. rewrite Properties.map.put_comm.
               ++ reflexivity.
               ++ symmetry. apply KX.
            -- rewrite map.get_put_diff.
               ++ apply K.
               ++ apply KX.
        + apply K.
      - rewrite <- IHT1. (*EFold*)
        + destruct (interp_expr store env e1) eqn:H; try reflexivity. f_equal.
          * apply FunctionalExtensionality.functional_extensionality. intros a.
            apply FunctionalExtensionality.functional_extensionality. intros b.
            destruct (eqb y k) eqn:KY.
            -- admit. (*admitted due to 'rewrite IHT3' making 'set k=v' outermost*)
            -- rewrite String.eqb_neq in KY. destruct (eqb x k) eqn:KX.
               ++ admit.
               ++ rewrite String.eqb_neq in KX. rewrite IHT3.
                  ** unfold set_local. rewrite Properties.map.put_comm.
                     --- rewrite Properties.map.put_comm with (k1:=x) (k2:=k).
                         +++ reflexivity.
                         +++ apply KX.
                     --- apply KY.
                  ** rewrite map.get_put_diff.
                     --- rewrite map.get_put_diff.
                         +++ apply K.
                         +++ symmetry. apply KX.
                     --- symmetry. apply KY.
          * apply IHT2.
            -- apply K.
        + apply K.
      - f_equal. f_equal. f_equal. apply FunctionalExtensionality.functional_extensionality.
        intros x. admit. (*ERecord, nested induction*)
      - rewrite IHT.
        + reflexivity.
        + apply K.
      - f_equal. f_equal. f_equal. apply FunctionalExtensionality.functional_extensionality.
        intros x. admit. (*EDict, nested induction*)
      - rewrite <- IHT1.
        + destruct (interp_expr store env d) eqn:H; try reflexivity. rewrite <- IHT2.
          * rewrite <- IHT3.
            -- reflexivity.
            -- apply K.
          * apply K.
        + apply K.
      - rewrite <- IHT1.
        + destruct (interp_expr store env d) eqn:H; try reflexivity. intuition congruence.
        + apply K.
      - rewrite <- IHT1.
        + destruct (interp_expr store env d) eqn:H; try reflexivity.  intuition congruence.
        + apply K.
      - rewrite <- IHT1.
        + destruct (interp_expr store env e) eqn:H; try reflexivity.
          f_equal. apply filter_ext. intros a. destruct (eqb k x) eqn:KX.
          * rewrite String.eqb_eq in KX. rewrite KX. unfold set_local.
            rewrite Properties.map.put_put_same. reflexivity.
          * rewrite String.eqb_neq in KX. rewrite IHT2.
            -- unfold set_local. rewrite Properties.map.put_comm.
               ++ reflexivity.
               ++ symmetry. apply KX.
            -- rewrite map.get_put_diff.
               ++ apply K.
               ++ apply KX.
        + apply K.
      - rewrite <- IHT1. (*EJoin*)
        + destruct (interp_expr store env e1) eqn:H1; try reflexivity. rewrite <- IHT2.
          * destruct (interp_expr store env e2) eqn:H2; try reflexivity.
            f_equal. apply flat_map_ext. intros a. destruct (eqb k y) eqn:KY.
            -- admit. (*admitted due to 'rewrite IHT4' making 'set k=v' outermost*)
            -- rewrite String.eqb_neq in KY. destruct (eqb k x) eqn:KX.
               ++ admit.
               ++ rewrite String.eqb_neq in KX. f_equal.
                  ** apply FunctionalExtensionality.functional_extensionality. intros b. rewrite IHT4.
                     --- unfold set_local. rewrite Properties.map.put_comm.
                         +++ rewrite Properties.map.put_comm with (k1:=k) (k2:=x); congruence.
                         +++ congruence.
                     --- rewrite !map.get_put_diff; assumption.
                  ** apply filter_ext. intros b. rewrite IHT3.
                     --- unfold set_local. rewrite Properties.map.put_comm.
                         +++ rewrite Properties.map.put_comm with (k1:=k) (k2:=x); congruence.
                         +++ congruence.
                     --- rewrite !map.get_put_diff; assumption.
          * apply K.
        + apply K.
      - rewrite <- IHT1.
        + destruct (interp_expr store env e) eqn:H; try reflexivity. f_equal. f_equal.
          apply FunctionalExtensionality.functional_extensionality. intros a. unfold set_local.
          destruct (eqb k x) eqn:KX.
          * rewrite String.eqb_eq in KX. rewrite KX. rewrite Properties.map.put_put_same. reflexivity.
          * rewrite String.eqb_neq in KX. rewrite IHT2.
            -- unfold set_local. rewrite Properties.map.put_comm.
               ++ reflexivity.
               ++ symmetry. apply KX.
            -- rewrite map.get_put_diff; assumption.
        + apply K.
    Admitted.

    Theorem filters_into_join : forall (store env: locals) (Gstore Genv: tenv) (db1 db2 p1 p2 pj rj: expr) (x y: string) (tx ty: type),
      x <> y ->
      map.get Genv x = None ->
      map.get Genv y = None ->
      type_of Gstore (map.put Genv x tx) p1 TBool ->
      type_of Gstore (map.put Genv y ty) p2 TBool ->
      type_of Gstore (map.put (map.put Genv x tx) y ty) pj TBool ->
      let pnew := EBinop OAnd pj (EBinop OAnd p1 p2) in
      interp_expr store env (EJoin (EFilter db1 x p1) (EFilter db2 y p2) x y pj rj)
      = interp_expr store env (EJoin db1 db2 x y pnew rj).
    Proof.
      intros store env Gstore Genv db1 db2 p1 p2 pj rj x y tx ty EXY EX EY T1 T2 TJ. simpl.
      destruct (interp_expr store env db1) eqn: DB1; try reflexivity.
      destruct (interp_expr store env db2) eqn: DB2; try reflexivity. f_equal.
      rewrite flat_map_filter. apply flat_map_ext. intros a.
      apply typeof_to_hastype with store (set_local env x a) Gstore (map.put Genv x tx) p1 TBool in T1 as T1'.
      inversion T1'. symmetry in H0. destruct b.
      - f_equal. rewrite filter_filter. apply filter_ext_in. intros b HB.
        (*apply typeof_to_hastype with (store:=store) (env:=set_local env x a) in TJ as TJ'.*)
        apply typeof_to_hastype with store (set_local (set_local env x a) y b) Gstore (map.put (map.put Genv x tx) y ty) pj TBool in TJ as TJ'.
        inversion TJ'. symmetry in H1. simpl.
        rewrite interp_invariant with store (set_local env x a) Gstore (map.put Genv x tx) p1 y b TBool in H0.
        + rewrite H0. simpl.
          apply typeof_to_hastype with store (set_local env y b) Gstore (map.put Genv y ty) p2 TBool in T2 as T2'.
          inversion T2'. symmetry in H2. unfold set_local. rewrite Properties.map.put_comm.
          * rewrite interp_invariant with store (set_local env y b) Gstore (map.put Genv y ty) p2 x a TBool in H2.
            -- unfold set_local in H2. rewrite H2. reflexivity.
            -- apply T2.
            -- rewrite map.get_put_diff.
               ++ apply EX.
               ++ apply EXY.
          * apply EXY.
        + apply T1.
        + rewrite map.get_put_diff.
          * apply EY.
          * symmetry. apply EXY.
      - symmetry. apply map_nil. apply filter_nil. intros b HB. unfold apply_bool_binop.
        destruct (interp_expr store (set_local (set_local env x a) y b) pj) eqn:H4; try reflexivity.
        rewrite interp_invariant with store (set_local env x a) Gstore (map.put Genv x tx) p1 y b TBool in H0.
        + rewrite H0.
          destruct (interp_expr store (set_local (set_local env x a) y b) p2) eqn:H5; try reflexivity.
          apply Bool.andb_false_r.
        + apply T1.
        + rewrite map.get_put_diff.
          * apply EY.
          * symmetry. apply EXY.
    Qed.

    Section EnvGenvRelation. (*env-genv relation definitions and related proofs 
                              for possible use in filter/join conversions (not currently used)*)
    Definition sub_domain1 (env: locals) (Genv: tenv) : Prop := (* in env -> in Genv *)
      forall (k: string),
        (exists v: value, map.get env k = Some v) -> (exists t: type, map.get Genv k = Some t).

    Definition sub_domain2 (env: locals) (Genv: tenv) : Prop := (* in Genv -> in env *)
      forall (k: string),
        (exists t: type, map.get Genv k = Some t) -> (exists v: value, map.get env k = Some v).

    Definition same_domain2 (env: locals) (Genv: tenv) : Prop :=
      sub_domain1 env Genv /\ sub_domain2 env Genv.
                                                
    Definition env_genv_relation (env: locals) (Genv: tenv) : Prop :=
      same_domain2 env Genv /\
      forall (k: string) (v: value) (t: type),
        (map.get env k = Some v) -> (map.get Genv k = Some t) -> has_type v t.
    
    Lemma same_domain_inductive : forall (env: locals) (Genv: tenv) (x: string) (a: value) (tx: type),
        same_domain2 env Genv ->
        same_domain2 (set_local env x a) (map.put Genv x tx).
      intros env Genv x a tx [EG1 EG2]. split.
      - unfold sub_domain1. intros k [v EV]. unfold set_local in EV. destruct (eqb k x) eqn:KX.
        + rewrite String.eqb_eq in KX. rewrite KX. exists tx. apply map.get_put_same.
        + rewrite String.eqb_neq in KX. rewrite map.get_put_diff.
          * apply EG1. rewrite map.get_put_diff in EV.
            -- exists v. apply EV.
            -- apply KX.
          * apply KX.
      - unfold sub_domain2. intros k [t EV]. unfold set_local. destruct (eqb k x) eqn:KX.
        + rewrite String.eqb_eq in KX. rewrite KX. exists a. apply map.get_put_same.
        + rewrite String.eqb_neq in KX. rewrite map.get_put_diff.
          * apply EG2. rewrite map.get_put_diff in EV.
            -- exists t. apply EV.
            -- apply KX.
          * apply KX. Qed.
    
    Lemma env_genv_inductive: forall (env: locals) (Genv: tenv) (x: string) (a: value) (tx: type),
      has_type a tx ->  
      (forall (k : string) (v : value) (t : type),
        map.get env k = Some v -> map.get Genv k = Some t -> has_type v t) ->
      forall (k : string) (v : value) (t : type),
        map.get (set_local env x a) k = Some v ->
        map.get (map.put Genv x tx) k = Some t -> has_type v t.
    intros env Genv x a tx T EG k v t KV KT. unfold set_local in KV. destruct (eqb k x) eqn:KX.
    - rewrite String.eqb_eq in KX. rewrite KX in KV, KT.
      rewrite map.get_put_same in KV. rewrite map.get_put_same in KT. inversion KV. inversion KT.
      rewrite <- H0. rewrite <- H1. apply T.
    - rewrite String.eqb_neq in KX. apply EG with k.
      + rewrite map.get_put_diff in KV.
        * apply KV.
        * apply KX.
      + rewrite map.get_put_diff in KT.
        * apply KT.
        * apply KX. Qed.  
    End EnvGenvRelation.
              

    Local Ltac destruct_match :=
      lazymatch goal with
      | H : (if type_eqb ?x ?y then _ else _) = _ |- _ =>
          let E := fresh "E" in
          destruct (type_eqb x y) eqn:E; try discriminate; apply type_eqb_eq in E; subst
      | H: (match ?x with _ => _ end) = Success _ |- _ =>
          let E := fresh "E" in
          destruct x eqn:E; try discriminate
      end.

    Local Ltac destruct_compare_types :=
      unfold compare_types in *; destruct_match; constructor.

    Local Ltac invert_result :=
      lazymatch goal with
      | H: Success _ = Success _ |- _ => inversion H; clear H; intros; subst
      end.

    Lemma atom_typechecker_sound : forall a t a',
        (synthesize_atom a = Success (t, a') -> type_of_atom a t) /\
          (analyze_atom t a = Success a' -> type_of_atom a t).
    Proof.
      destruct a; split; simpl; intro;
        repeat (try destruct_compare_types; try destruct_match; try invert_result; try constructor).
    Qed.

    Lemma atom_type_sound : forall a t, type_of_atom a t -> has_type (interp_atom a) t.
    Proof.
      intros a t H. inversion H; subst; repeat constructor.
    Qed.

    Local Ltac apply_typechecker_IH :=
       match goal with
           | IH: (forall _ _ _ _, (synthesize_expr _ _ ?e = _ -> _) /\ _),
               H: synthesize_expr _ _ ?e = _ |- _ => eapply IH in H; eauto
           | IH: (forall _ _ _ _, _ /\ (analyze_expr _ _ _ ?e = _ -> _)),
               H: analyze_expr _ _ _ ?e = _ |- _ => eapply IH in H; eauto
       end.

    Section __.
      Lemma string_compare_trans : forall s1 s2 s3,
          String.compare s1 s2 = Lt -> String.compare s2 s3 = Lt -> String.compare s1 s3 = Lt.
      Proof.
        induction s1; destruct s2, s3; auto; simpl in *; try discriminate.
        - intros. destruct (Ascii.compare a a0) eqn:E1, (Ascii.compare a0 a1) eqn:E2; try discriminate; auto.
          + apply Ascii.compare_eq_iff in E2; subst. rewrite E1. eapply IHs1; eauto.
          + apply Ascii.compare_eq_iff in E1; subst. rewrite E2. auto.
          + apply Ascii.compare_eq_iff in E2; subst. rewrite E1. auto.
          + unfold Ascii.compare in *. rewrite N.compare_lt_iff in E1, E2.
            pose proof (N.lt_trans _ _ _ E1 E2). rewrite <-  N.compare_lt_iff in H1.
            rewrite H1. easy.
      Qed.

      Lemma record_type_entry_leb_trans : RelationClasses.Transitive record_type_entry_leb.
      Proof.
        unfold RelationClasses.Transitive. destruct x, y, z. unfold record_type_entry_leb. simpl.
        unfold String.leb. destruct (String.compare s s0) eqn:E1, (String.compare s0 s1) eqn:E2; intuition.
        - apply compare_eq_iff in E2. subst. rewrite E1; easy.
        - apply compare_eq_iff in E1. subst. rewrite E2; easy.
        - apply compare_eq_iff in E2. subst. rewrite E1; easy.
        - pose proof (string_compare_trans _ _ _ E1 E2). rewrite H1; easy.
      Qed.

      Lemma StronglySorted_record_type_sort : forall l, StronglySorted (record_type_entry_leb) (record_type_sort l).
      Proof.
        intros. apply Sectioned.StronglySorted_sort.
        - apply record_type_entry_leb_total.
        - apply record_type_entry_leb_trans.
      Qed.

      Lemma Permuted_record_type_sort : forall l, Permutation l (record_type_sort l).
      Proof.
        apply Sectioned.Permuted_sort.
      Qed.

    Lemma fst_map_fst : forall (A B C : Type) (l : list (A * B)) (f : A -> B -> C),
        List.map fst (List.map (fun '(a, b) => (a, f a b)) l) = List.map fst l.
    Proof.
      induction l; auto.
      intros. destruct a. simpl. f_equal. auto.
    Qed.

    Lemma inb_false_iff : forall s l, inb eqb l s = false <-> ~ In s l.
    Proof.
      induction l; simpl; intros.
      - intuition.
      - destruct (String.eqb a s) eqn:E; intuition.
        + rewrite String.eqb_eq in E; intuition.
        + rewrite String.eqb_neq in E; intuition.
    Qed.

    Lemma inb_true_iff : forall s l, inb eqb l s = true <-> In s l.
    Proof.
      induction l; simpl; intros.
      - split; intuition.
      - destruct (String.eqb a s) eqn:E; intuition.
        + rewrite String.eqb_eq in E; intuition.
        + rewrite String.eqb_neq in E; intuition.
    Qed.

    Lemma inclb_correct : forall l l', inclb String.eqb l l' = true -> incl l l'.
    Proof.
      induction l; simpl; intros.
      - apply incl_nil_l.
      - rewrite Bool.andb_true_iff in H. destruct H as [HL HR].
        apply IHl in HR. rewrite inb_true_iff in HL.
        unfold incl. intros. inversion H; subst; intuition.
    Qed.

    Lemma inclb_complete : forall l l', incl l l' -> inclb String.eqb l l' = true.
    Proof.
      intros l l' H. unfold inclb. rewrite forallb_forall; intros.
      rewrite inb_true_iff. intuition.
    Qed.

    Lemma record_type_from'_sound : forall l tl el Gstore Genv,
        Forall
        (fun p : string * expr =>
         forall (Gstore Genv : tenv) (t : type) (e' : expr),
         (synthesize_expr Gstore Genv (snd p) = Success (t, e') -> type_of Gstore Genv (snd p) t) /\
         (analyze_expr Gstore Genv t (snd p) = Success e' -> type_of Gstore Genv (snd p) t)) l ->
        record_type_from' (List.map (fun '(s, e') => (s, synthesize_expr Gstore Genv e')) l) = Success (tl, el) ->
        List.map fst l = List.map fst tl /\ Forall2 (type_of Gstore Genv) (List.map snd l) (List.map snd tl) /\ NoDup (List.map fst l).
    Proof.
      induction l; intros.
      - simpl in *. invert_result. intuition. apply NoDup_nil.
      - simpl in *. repeat destruct_match. invert_result. destruct a. inversion E; subst; simpl.
        inversion H; subst. apply (IHl _ _ _ _ H4)in E2 as [IHl1 [IHl2 IHl3]]. split; [| split].
        + f_equal. auto.
        + constructor; auto. apply H3 in H2. auto.
        + constructor; auto. apply inb_false_iff. erewrite <- fst_map_fst. apply E4.
    Qed.

    Lemma record_from'_sound :
      forall l tl' el Gstore Genv,
        Forall
        (fun p : string * expr =>
         forall (Gstore Genv : tenv) (t : type) (e' : expr),
         (synthesize_expr Gstore Genv (snd p) = Success (t, e') -> type_of Gstore Genv (snd p) t) /\
         (analyze_expr Gstore Genv t (snd p) = Success e' -> type_of Gstore Genv (snd p) t)) l ->
        record_from' (List.map (fun '(s, e) => (s, analyze_expr Gstore Genv (get_attr_type tl' s) e)) l) = Success el ->
        let tl := List.map (fun '(s, _) => (s, get_attr_type tl' s)) l in
        List.map fst l = List.map fst tl /\ Forall2 (type_of Gstore Genv) (List.map snd l) (List.map snd tl) /\ NoDup (List.map fst l).
    Proof.
      induction l; intros.
      - simpl in *. invert_result. intuition. apply NoDup_nil.
      - simpl in *. repeat destruct_match. destruct a. inversion H; inversion E; subst.
        invert_result. simpl in *. intuition.
        + f_equal. rewrite fst_map_fst. auto.
        + constructor.
          * eapply H3; eauto.
          * eapply IHl; eauto.
        + rewrite fst_map_fst in E2. apply inb_false_iff in E2. apply NoDup_cons; auto.
          eapply IHl; eauto.
    Qed.

    Lemma double_incl_NoDup_Permuted : forall (l : list (string * expr)) (tl' : list (string * type)),
        inclb String.eqb (List.map fst l) (List.map fst tl') = true ->
        inclb String.eqb (List.map fst tl') (List.map fst l) = true ->
        NoDup (List.map fst l) ->
        length (List.map fst tl') <= length (List.map fst l) ->
        Permutation (List.map (fun '(s, _) => (s, get_attr_type tl' s)) l) tl'.
    Proof.
      intros.
      assert (NoDup (List.map fst tl')).
      { apply inclb_correct in H, H0. eapply NoDup_incl_NoDup; eauto. }
      generalize dependent tl'. induction l; simpl; intros.
      - destruct tl'; simpl in *; intuition; discriminate.
      - destruct a; simpl in *. remember (s, get_attr_type tl' s) as p.
        rewrite Bool.andb_true_iff in H; destruct H. rewrite inb_true_iff in H.
        assert (forall s, In s (List.map fst tl') -> In (s, get_attr_type tl' s) tl').
        { clear; induction tl'; simpl; intros.
          - auto.
          - destruct a; simpl in *. destruct (String.eqb s0 s) eqn:E.
            + rewrite String.eqb_eq in E; subst; auto.
            + rewrite String.eqb_neq in E. right. apply IHtl'. intuition. }
        apply H5 in H.
        assert (forall A (x : A) l', In x l' -> exists l, Permutation (x :: l) l').
        { clear. induction l'; intros.
          - apply in_nil in H; intuition.
          - inversion H.
            + exists l'; subst; auto.
            + apply IHl' in H0 as [l Hl]. exists (a :: l). eapply perm_trans; try apply perm_swap.
              constructor; assumption. }
        apply H6 in H. destruct H as [tl Htl].
        eapply Permutation_trans; [| apply Htl].
        subst; apply perm_skip.
        assert (forall (l : list (string * expr)) tl tl' s t,
                   incl (List.map fst l) (List.map fst tl') ->
                   Permutation ((s, t) :: tl) tl' ->
                   ~ In s (List.map fst l) -> NoDup (List.map fst tl') ->
                   List.map (fun '(s, _) => (s, get_attr_type tl' s)) l = List.map (fun '(s, _) => (s, get_attr_type tl s)) l).
        { clear. induction l; simpl; intros; auto.
          destruct a; simpl in *. f_equal.
          - rewrite <- Permutation_NoDup_In_get_attr_type with (tl := (s,t) :: tl) (tl' := tl'); auto.
            + simpl. destruct (String.eqb s s0) eqn:E; auto.
              exfalso; apply H1; left; symmetry; apply String.eqb_eq; auto.
            + intuition.
          - eapply IHl; eauto. apply incl_cons_inv in H. intuition. }
        erewrite H; eauto.
        + apply IHl.
          * inversion H1. auto.
          * apply Permutation_sym in Htl. apply inclb_complete. apply inclb_correct in H4. auto.
            apply Permutation_map with (f := fst) in Htl. apply Permutation_incl in Htl. unfold incl; intros.
            apply H4 in H7 as H8. apply Htl in H8. inversion H8; auto. simpl in *; subst. inversion H1; intuition.
          * apply inclb_complete. apply inclb_correct in H0.
            apply Permutation_map with (f := fst) in Htl. apply Permutation_sym in Htl. apply (Permutation_NoDup Htl) in H3.
            apply Permutation_sym in Htl. apply Permutation_incl in Htl.
            unfold incl; intros. simpl in *. apply incl_cons_inv in Htl. apply Htl in H7 as H8. apply H0 in H8. inversion H8; auto.
            subst. inversion H3; intuition.
          * apply Permutation_map with (f := fst) in Htl; apply Permutation_length in Htl. simpl in Htl.
            rewrite <- Htl in H2. apply le_S_n in H2. auto.
          * apply Permutation_map with (f := fst) in Htl. apply Permutation_sym in Htl. apply (Permutation_NoDup Htl) in H3.
            simpl in *. inversion H3; intuition.
        + apply inclb_correct; auto.
        + inversion H1; auto.
    Qed.
    End __.

    Lemma proj_record_type_sound : forall l s t, proj_record_type l s = Success t -> In (s, t) l.
    Proof.
      induction l; simpl in *; try discriminate. intros.
      destruct a. destruct_match; auto.
      rewrite String.eqb_eq in E. invert_result. auto.
    Qed.

    Lemma dict_from'_sound : forall l,
        Forall (fun p =>
                  (forall (Gstore Genv : tenv) (t : type) (e' : expr),
                      (synthesize_expr Gstore Genv (fst p) = Success (t, e') -> type_of Gstore Genv (fst p) t) /\
                        (analyze_expr Gstore Genv t (fst p) = Success e' -> type_of Gstore Genv (fst p) t)) /\
                    (forall (Gstore Genv : tenv) (t : type) (e' : expr),
                        (synthesize_expr Gstore Genv (snd p) = Success (t, e') -> type_of Gstore Genv (snd p) t) /\
                          (analyze_expr Gstore Genv t (snd p) = Success e' -> type_of Gstore Genv (snd p) t))) l ->
        forall Gstore Genv kt vt l',
          dict_from' (List.map (fun '(k, v) => k' <- analyze_expr Gstore Genv kt k;; v' <- analyze_expr Gstore Genv vt v;; Success (k', v')) l) = Success l' -> Forall (fun p => type_of Gstore Genv (fst p) kt /\ type_of Gstore Genv (snd p) vt) l.
    Proof.
      induction l; simpl; intros.
      - apply Forall_nil.
      - repeat destruct_match. invert_result. inversion H; subst; simpl in *.
        constructor.
        + split; simpl.
          * apply H2 in E3. apply E3.
          * apply H2 in E4. apply E4.
        + eapply IHl; eauto.
    Qed.

    Lemma analyze_dict_body_sound : forall l,
        Forall (fun p =>
                  (forall (Gstore Genv : tenv) (t : type) (e' : expr),
                      (synthesize_expr Gstore Genv (fst p) = Success (t, e') -> type_of Gstore Genv (fst p) t) /\
                        (analyze_expr Gstore Genv t (fst p) = Success e' -> type_of Gstore Genv (fst p) t)) /\
                    (forall (Gstore Genv : tenv) (t : type) (e' : expr),
                        (synthesize_expr Gstore Genv (snd p) = Success (t, e') -> type_of Gstore Genv (snd p) t) /\
                          (analyze_expr Gstore Genv t (snd p) = Success e' -> type_of Gstore Genv (snd p) t))) l ->
        forall Gstore Genv kt vt e',
          analyze_dict_body analyze_expr Gstore Genv kt vt l = Success e' -> Forall (fun p => type_of Gstore Genv (fst p) kt /\ type_of Gstore Genv (snd p) vt) l.
    Proof.
      unfold analyze_dict_body, dict_from. intros.
      destruct_match. invert_result. eapply dict_from'_sound; eauto.
    Qed.

    Lemma typechecker_sound : forall e Gstore Genv t e',
        (synthesize_expr Gstore Genv e = Success (t, e') -> type_of Gstore Genv e t) /\
          (analyze_expr Gstore Genv t e = Success e' -> type_of Gstore Genv e t).
    Proof.
      apply (expr_IH (fun e => forall (Gstore Genv : tenv) (t : type) (e' : expr),
  (synthesize_expr Gstore Genv e = Success (t, e') -> type_of Gstore Genv e t) /\
  (analyze_expr Gstore Genv t e = Success e' -> type_of Gstore Genv e t))); intros; simpl.
      - (* EVar *)
        split; intros; repeat destruct_match; invert_result; constructor; easy.
      - (* ELoc *)
        split; intros; repeat destruct_match; invert_result; constructor; easy.
      - (* EAtom *)
        split; intros; repeat destruct_match; constructor;
          invert_result; apply atom_typechecker_sound in E; auto.
      - (* EUnop *)
        split; intros; destruct o; simpl in *;
          repeat (repeat destruct_match; try invert_result; apply_typechecker_IH; repeat econstructor; eauto).
      - (* EBinop *)
        split; intros; destruct o; simpl in *;
        try (repeat destruct_match; try invert_result; repeat apply_typechecker_IH; repeat econstructor; eauto).
      - (* EIf *)
        split; intros; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - (* ELet *)
        split; intros; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - (* EFlatmap *)
        split; intros; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - (* EFold *)
        split; intros; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - (* ERecord *)
        split; intros; repeat destruct_match.
        + unfold record_type_from in *. repeat destruct_match. invert_result.
          pose proof record_type_from'_sound. eapply H0 in H; eauto.
          apply TyERecord with (tl := l0); intuition;
          [ apply Permuted_record_type_sort | apply StronglySorted_record_type_sort ].
        + assert (type_eqb (TRecord l0) (TRecord (record_type_sort l0))); auto.
          apply type_eqb_eq in H1. injection H1; intro. unfold record_from in *. destruct_match. invert_result.
          pose proof record_from'_sound. eapply H0 in H; eauto.
          apply TyERecord with (tl := List.map (fun '(s, e) => (s, get_attr_type l0 s)) l); intuition.
          * rewrite Bool.andb_true_iff in E2. apply double_incl_NoDup_Permuted; intuition.
            apply leb_complete. repeat rewrite map_length. auto.
          * rewrite H2. apply StronglySorted_record_type_sort.
      - split; intros; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto;
          auto using proj_record_type_sound.
      - split; intros; repeat destruct_match; try invert_result; constructor;
        eapply analyze_dict_body_sound; eauto.
      - split; intros; repeat destruct_match; repeat apply_typechecker_IH; invert_result; constructor; auto.
      - split; intros; repeat destruct_match; repeat apply_typechecker_IH; invert_result; constructor; auto.
      - split; intros; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - split; intros; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - split; intros; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
      - split; intros; repeat destruct_match; repeat apply_typechecker_IH; invert_result; econstructor; eauto.
    Qed.

(*
    Lemma app_has_type : forall l r t, has_type (VList l) t /\ has_type (VList r) t -> has_type (VList (l ++ r)) t.
    Proof.
      induction l; intros r t [HL HR].
      - easy.
      - simpl. inversion HL; subst. constructor; auto.
    Qed.
*)
  End WithWord.
End WithMap.

(* ===== PHOAS ===== *)
Section WithPhoasEnv.
  Context {V : Type}.
  Context {phoas_env: map.map string V} {phoas_env_ok: map.ok phoas_env}.

  (* ===== PHOAS abstract syntax tree ===== *)
  Inductive phoas_expr : Type :=
  | PhEVar (v : V)
  | PhELoc (x : string)
  | PhEAtom (a : atom)
  | PhEUnop (o : unop) (e : phoas_expr)
  | PhEBinop (o : binop) (e1 e2: phoas_expr)
  | PhEFlatmap (e : phoas_expr) (x : string) (f : V -> phoas_expr) (* Retain the variable names as hints for dephoasify *)
  | PhEFold (e1 e2 : phoas_expr) (x y : string) (f : V -> V -> phoas_expr)
  | PhEIf (e1 e2 e3 : phoas_expr)
  | PhELet (e : phoas_expr) (x : string) (f : V -> phoas_expr)
  | PhERecord (l : list (string * phoas_expr))
  | PhEAccess (r : phoas_expr) (s : string)
  | PhEDict (l : list (phoas_expr * phoas_expr))
  | PhEInsert (d k v : phoas_expr)
  | PhEDelete (d k : phoas_expr)
  | PhELookup (d k : phoas_expr)
  | PhEFilter (l : phoas_expr) (x : string) (p : V -> phoas_expr)
  | PhEJoin (l1 l2 : phoas_expr) (x y : string) (p r : V -> V -> phoas_expr)
  | PhEProj (l : phoas_expr) (x : string) (r : V -> phoas_expr).

  Inductive phoas_command : Type :=
  | PhCSkip
  | PhCSeq (c1 c2 : phoas_command)
  | PhCLet (e : phoas_expr) (x : string) (f : V -> phoas_command)
  | PhCLetMut (e : phoas_expr) (x : string) (c : phoas_command)
  | PhCAssign (x : string) (e : phoas_expr)
  | PhCIf (e : phoas_expr) (c1 c2 : phoas_command)
  | PhCForeach (e : phoas_expr) (x : string) (f : V -> phoas_command).

  Fixpoint phoasify (env : phoas_env) (e : expr) : phoas_expr :=
    match e with
    | EVar x => match map.get env x with
                | Some v => PhEVar v
                | None => PhEAtom AUnit
                end
    | ELoc x => PhELoc x
    | EAtom a => PhEAtom a
    | EUnop o e => PhEUnop o (phoasify env e)
    | EBinop o e1 e2 => PhEBinop o (phoasify env e1) (phoasify env e2)
    | EIf e1 e2 e3 => PhEIf (phoasify env e1) (phoasify env e2) (phoasify env e3)
    | ELet e1 x e2 => PhELet (phoasify env e1) x (fun v => phoasify (map.put env x v) e2)
    | EFlatmap e1 x e2 => PhEFlatmap (phoasify env e1) x (fun v => phoasify (map.put env x v) e2)
    | EFold e1 e2 x y e3 => PhEFold (phoasify env e1) (phoasify env e2) x y
                              (fun v acc => phoasify (map.put (map.put env x v) y acc) e3)
    | ERecord l => PhERecord (List.map (fun '(s, e)  => (s, phoasify env e)) l)
    | EAccess e s => PhEAccess (phoasify env e) s
    | EDict l => PhEDict (List.map (fun '(k, v)  => (phoasify env k, phoasify env v)) l)
    | EInsert d k v => PhEInsert (phoasify env d) (phoasify env k) (phoasify env v)
    | EDelete d k => PhEDelete (phoasify env d) (phoasify env k)
    | ELookup d k  => PhELookup (phoasify env d) (phoasify env k)
    | EFilter l x p => PhEFilter (phoasify env l) x (fun v => phoasify (map.put env x v) p)
    | EJoin l1 l2 x y p r => PhEJoin (phoasify env l1) (phoasify env l2) x y
                                     (fun v1 v2 => phoasify (map.put (map.put env x v1) y v2) p)
                                     (fun v1 v2 => phoasify (map.put (map.put env x v1) y v2) r)
    | EProj l x r => PhEProj (phoasify env l) x (fun v => phoasify (map.put env x v) r)
    end.

  Fixpoint phoasify_command (env : phoas_env) (c : command) : phoas_command :=
    match c with
    | CSkip => PhCSkip
    | CSeq c1 c2 => PhCSeq (phoasify_command env c1) (phoasify_command env c2)
    | CLet e x c => PhCLet (phoasify env e) x (fun v => phoasify_command (map.put env x v) c)
    | CLetMut e x c => PhCLetMut (phoasify env e) x (phoasify_command env c)
    | CAssign x e => PhCAssign x (phoasify env e)
    | CIf e c1 c2 => PhCIf (phoasify env e) (phoasify_command env c1) (phoasify_command env c2)
    | CForeach e x c => PhCForeach (phoasify env e) x (fun v => phoasify_command (map.put env x v) c)
    end.
End WithPhoasEnv.

Arguments phoas_expr : clear implicits.
Arguments phoas_command : clear implicits.

Definition Phoas_expr := forall V, phoas_expr V.
Definition Phoas_command := forall V, phoas_command V.

Section WithGeneralPhoasEnv.
  Context {width: Z} {word: Interface.word width}.
  Context {word_ok: word.ok word}.
  Context {phoas_env: forall V, map.map string V} {phoas_env_ok: forall V, map.ok (phoas_env V)}.
  Definition Phoasify (e : expr) : Phoas_expr := fun V => phoasify map.empty e.
  Definition Phoasify_command (c : command) : Phoas_command := fun V => phoasify_command map.empty c.

  Local Notation interp_unop := (interp_unop (width:=width)).
  (* ===== PHOAS interpreter ===== *)
  Fixpoint interp_phoas_expr (store : phoas_env value) (e : phoas_expr value) : value :=
    match e with
    | PhEVar v => v
    | PhELoc x => get_local store x
    | PhEAtom a => interp_atom a
    | PhEUnop o e => interp_unop o (interp_phoas_expr store e)
    | PhEBinop o e1 e2 => interp_binop o (interp_phoas_expr store e1) (interp_phoas_expr store e2)
    | PhEIf e1 e2 e3 =>
        match interp_phoas_expr store e1 with
        | VBool true => interp_phoas_expr store e2
        | VBool false => interp_phoas_expr store e3
        | _ => VUnit
        end
    | PhELet e _ f => interp_phoas_expr store (f (interp_phoas_expr store e))
    | PhEFlatmap e _ f => match interp_phoas_expr store e with
                          | VList l1 =>
                              VList (flat_map (fun y => match interp_phoas_expr store (f y) with
                                                        | VList l2 => l2
                                                        | _ => nil
                                                        end) l1)
                          | _ => VUnit
                          end
    | PhEFold e1 e2 _ _ f => match interp_phoas_expr store e1 with
                             | VList l1 =>
                                 let a := interp_phoas_expr store e2 in
                                 let f := fun v acc => interp_phoas_expr store (f v acc) in
                                 fold_right f a l1
                             | _ => VUnit
                             end
    | PhERecord l => VRecord (record_sort (List.map (fun '(s, e) => (s, interp_phoas_expr store e)) l))
    | PhEAccess r s => match interp_phoas_expr store r with
                       | VRecord l => record_proj s l
                       | _ => VUnit
                       end
    | PhEDict l => VDict (dict_sort (List.map (fun '(k, v) => (interp_phoas_expr store k, interp_phoas_expr store v)) l))
    | PhEInsert d k v => match interp_phoas_expr store d with
                         | VDict l => VDict (dict_insert (interp_phoas_expr store k) (interp_phoas_expr store v) l)
                         | _ => VUnit
                         end
    | PhEDelete d k => match interp_phoas_expr store d with
                       | VDict l => VDict (dict_delete (interp_phoas_expr store k) l)
                       | _ => VUnit
                       end
    | PhELookup d k => match interp_phoas_expr store d with
                       | VDict l => VOption (dict_lookup (interp_phoas_expr store k) l)
                       | _ => VUnit
                       end
    | PhEFilter l x p => match interp_phoas_expr store l with
                           | VList l =>
                               VList
                                 (List.filter (fun v =>
                                              match interp_phoas_expr store (p v) with
                                              | VBool b => b
                                              | _ => false
                                              end) l)
                           | _ => VUnit
                           end
    | PhEJoin l1 l2 x y p r =>
        match interp_phoas_expr store l1 with
        | VList l1 =>
            match interp_phoas_expr store l2 with
            | VList l2 =>
                VList (flat_map
                         (fun v1 =>
                            List.map
                              (fun v2 => interp_phoas_expr store (r v1 v2))
                              (List.filter (fun v2 =>
                                             match interp_phoas_expr store (p v1 v2) with
                                             | VBool b => b
                                             | _ => false
                                             end) l2))
                         l1)
            | _ => VUnit
            end
        | _ => VUnit
        end
    | PhEProj l x r =>
        match interp_phoas_expr store l with
        | VList l => VList (List.map (fun v => interp_phoas_expr store (r v)) l)
        | _ => VUnit
        end
    end.

End WithGeneralPhoasEnv.

(* Notations *)
Coercion EVar : string >-> expr.
Coercion AInt : Z >-> atom.
Coercion ABool : bool >-> atom.
Coercion EAtom : atom >-> expr.
