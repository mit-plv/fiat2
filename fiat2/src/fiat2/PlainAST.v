Require Export String.
Require Export ZArith.
Require Export List.
Require Export coqutil.Map.Interface coqutil.Map.SortedListString.
Require Export coqutil.Byte coqutil.Word.Interface coqutil.Word.Bitwidth.

(* ===== Fiat2 types ===== *)
Inductive type : Type :=
| TWord
| TInt
| TBool
| TString
| TOption (t : type)
| TList (t : type)
| TRecord (l : list (string * type))
| TDict (kt vt : type)
| TUnit.

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
| EProj (r : expr) (s : string)
| EDict (l : list (expr * expr))
| EInsert (d k v : expr)
| EDelete (d k : expr)
| ELookup (d k : expr).

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

  Section WithValueCompare.
    Context (value_compare : value -> value -> comparison).

    Definition record_compare (l l' : list (string * value)) : comparison :=
      let f := fun '(s, e) '(s', e') => match String.compare s s' with
                           | Eq => value_compare e e'
                           | _ as c => c
                           end in
      list_compare f l l'.

    Definition dict_compare (l l' : list (value * value)) : comparison :=
      let f := fun '(k, v) '(k', v') => match value_compare k k' with
                           | Eq => value_compare v v'
                           | _ as c => c
                           end in
      list_compare f l l'.
  End WithValueCompare.

  Fixpoint value_compare (a b : value) : comparison :=
    match a, b with
    | VWord a, VWord b =>
        if word.eqb a b then Eq else if word.ltu a b then Lt else Gt
    | VInt a, VInt b =>
        if Z.eqb a b then Eq else if Z.ltb a b then Lt else Gt
    | VBool a, VBool b =>
        if Bool.eqb a b then Eq else if andb (negb a) b then Lt else Gt
    | VString a, VString b =>
        if String.eqb a b then Eq else if String.ltb a b then Lt else Gt
    | VOption a, VOption b =>
        match a with
        |None => match b with None => Eq | _ => Lt end
        | Some a => match b with None => Gt | Some b => value_compare a b end
        end
    | VList a, VList b => list_compare value_compare a b
    | VRecord a, VRecord b => record_compare value_compare a b
    | VDict a, VDict b => dict_compare value_compare a b
    | VUnit, VUnit => Eq
    | _, _ => Lt (* unreachable cases, must compare values of the same type *)
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
  (* ----- End of comparison ----- *)
  Definition record_sort (l : list (string * value)) : list (string * value). Admitted.
  Definition dict_sort (l : list (value * value)) : list (value * value). Admitted.

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
    | (k', v) :: l => if value_ltb k k' then (k, v) :: (k', v) :: l else (k', v) :: dict_insert k v l
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
      | EProj r s => match interp_expr store env r with
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
  | TString, TString
  | TUnit, TUnit => true
  | TOption t1, TOption t1' => type_eqb t1 t1'
  | TList t1, TList t1' => type_eqb t1 t1'
  | TRecord l, TRecord l' => list_beq _ (fun p p' => andb (String.eqb (fst p) (fst p'))
                                                          (type_eqb (snd p) (snd p'))) l l'
  | TDict kt vt, TDict kt' vt' => andb (type_eqb kt kt') (type_eqb vt vt')
  | _, _ => false
  end.

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
  | OLess | OEq => (TInt, TInt, TBool)
  | OWRange => (TWord, TWord, TList TWord)
  | ORange => (TInt, TInt, TList TInt)
  | _ => (TUnit, TUnit, TUnit) (* unused *)
  end.

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

Definition record_type_sort (l : list (string * type)) : list (string * type). Admitted.

Fixpoint record_type_from' (l : list (string * result (type * expr))) : result (list (string * type) * list (string * expr)) :=
  match l with
  | nil => Success (nil, nil)
  | (s, Success (t, e)) :: l => '(tl, el) <- record_type_from' l ;;
                                Success ((s, t) :: tl, (s, e) :: el)
  | (_, Failure err) :: _ => Failure err
  end.

Definition record_type_from (l : list (string * result (type * expr))) : result (type * expr) :=
  '(tl, el) <- record_type_from' l ;; Success (TRecord (record_type_sort tl), ERecord el).

Fixpoint record_from' (l : list (string * result expr)) : result (list (string * expr)) :=
  match l with
  | nil => Success nil
  | (s, Success e) :: l => l' <- record_from' l ;; Success ((s, e) :: l')
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

(* ??? Should we try to infer the type of dict from a single key and a single value whose types are successfully synthesized? *)
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

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.

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
                   | TRecord tl => if inclb String.eqb (List.map fst tl) (List.map fst l)
                                   then record_from (List.map
                                                       (fun '(s, e) => (s, analyze_expr Gstore Genv(get_attr_type tl s) e))
                                                       l)
                                   else error:(e "does not have all expected attributes" tl)
                   | _ => error:(e "is a record but expected" expected)
                   end
    | EProj e s => '(t, e') <- synthesize_expr Gstore Genv e ;;
                   match t with
                   | TRecord l => t <- proj_record_type l s ;; e <- proj_record_field e' s ;;
                                  if type_eqb expected t then Success e
                                  else error:("Attribute" s "has type" t "but expected" expected)
                   | t => error:(e "has type" t "but expected a record")
                   end
    | EDict l => match expected with
                 | TDict kt vt =>
                     dict_from (List.map (fun '(k, v) => k' <- analyze_expr Gstore Genv kt k ;;
                                                              v' <- analyze_expr Gstore Genv vt v ;;
                                                              Success (k', v')) l)
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
    | EProj e s => '(t, e') <- synthesize_expr Gstore Genv e ;;
                   match t with
                   | TRecord l => t <- proj_record_type l s ;; e <- proj_record_field e' s ;; Success (t, e)
                   | t => error:(e "has type" t "but expected a record")
                   end
    | EDict l => dict_type_from (List.map (fun '(k, v) => '(kt, k') <- synthesize_expr Gstore Genv k ;;
                                                          '(vt, v') <- synthesize_expr Gstore Genv v ;;
                                                          Success (kt, k', vt, v')) l)
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
    end.
End WithMap.
(* ?????
For sorting, use the bookmarked modification of coqstdlib.
If it works, make it a submodule like bedrock2, with Makefiles doing the right things.

Use inclb to check each attribute in expected is in the record expr (after two maps)
                                                      For each entry in record expr, grab its type from expected and analyze

*)
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
  (* Retain the variable names as hints for dephoasify *)
  | PhEFlatmap (e : phoas_expr) (x : string) (f : V -> phoas_expr)
  | PhEFold (e1 e2 : phoas_expr) (x y : string) (f : V -> V -> phoas_expr)
  | PhEIf (e1 e2 e3 : phoas_expr)
  | PhELet (e : phoas_expr) (x : string) (f : V -> phoas_expr)
  | PhERecord (l : list (string * phoas_expr))
  | PhEProj (r : phoas_expr) (s : string)
  | PhEDict (l : list (phoas_expr * phoas_expr))
  | PhEInsert (d k v : phoas_expr)
  | PhEDelete (d k : phoas_expr)
  | PhELookup (d k : phoas_expr).

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
    | EProj e s => PhEProj (phoasify env e) s
    | EDict l => PhEDict (List.map (fun '(k, v)  => (phoasify env k, phoasify env v)) l)
    | EInsert d k v => PhEInsert (phoasify env d) (phoasify env k) (phoasify env v)
    | EDelete d k => PhEDelete (phoasify env d) (phoasify env k)
    | ELookup d k  => PhELookup (phoasify env d) (phoasify env k)
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
  Fixpoint phoas_interp_expr (store : phoas_env value) (e : phoas_expr value) : value :=
    match e with
    | PhEVar v => v
    | PhELoc x => match map.get store x with
                  | Some v => v
                  | None => VUnit
                  end
    | PhEAtom a => interp_atom a
    | PhEUnop o e => interp_unop o (phoas_interp_expr store e)
    | PhEBinop o e1 e2 => interp_binop o (phoas_interp_expr store e1) (phoas_interp_expr store e2)
    | PhEIf e1 e2 e3 =>
        match phoas_interp_expr store e1 with
        | VBool true => phoas_interp_expr store e2
        | VBool false => phoas_interp_expr store e3
        | _ => VUnit
        end
    | PhELet e _ f => phoas_interp_expr store (f (phoas_interp_expr store e))
    | PhEFlatmap e _ f => match phoas_interp_expr store e with
                          | VList l1 =>
                              VList (flat_map (fun y => match phoas_interp_expr store (f y) with
                                                        | VList l2 => l2
                                                        | _ => nil
                                                        end) l1)
                          | _ => VUnit
                          end
    | PhEFold e1 e2 _ _ f => match phoas_interp_expr store e1 with
                             | VList l1 =>
                                 let a := phoas_interp_expr store e2 in
                                 let f := fun v acc => phoas_interp_expr store (f v acc) in
                                 fold_right f a l1
                             | _ => VUnit
                             end
    | PhERecord l => VRecord (record_sort (List.map (fun '(s, e) => (s, phoas_interp_expr store e)) l))
    | PhEProj r s => match phoas_interp_expr store r with
                     | VRecord l => record_proj s l
                     | _ => VUnit
                     end
    | PhEDict l => VDict (dict_sort (List.map (fun '(k, v) => (phoas_interp_expr store k, phoas_interp_expr store v)) l))
    | PhEInsert d k v => match phoas_interp_expr store d with
                         | VDict l => VDict (dict_insert (phoas_interp_expr store k) (phoas_interp_expr store v) l)
                         | _ => VUnit
                         end
  | PhEDelete d k => match phoas_interp_expr store d with
                   | VDict l => VDict (dict_delete (phoas_interp_expr store k) l)
                   | _ => VUnit
                   end
  | PhELookup d k => match phoas_interp_expr store d with
                   | VDict l => VOption (dict_lookup (phoas_interp_expr store k) l)
                   | _ => VUnit
                   end
  end.

End WithGeneralPhoasEnv.

Inductive rel_expr : Type :=
| REVar (x : string)
| RELoc (x : string)
| REAtom (a : atom)
| REUnop (o : unop) (e : rel_expr)
| REBinop (o : binop) (e1 e2: rel_expr)
| REIf (e1 e2 e3 : rel_expr)
| RELet (e1 : rel_expr) (x : string) (e2 : rel_expr)
| REFlatmap (e1 : rel_expr) (x : string) (e2 : rel_expr)
| REFold (e1 e2 : rel_expr) (x y : string) (e3 : rel_expr)
| RERecord (l : list (string * rel_expr))
| REProj (e : rel_expr) (s : string)
| REDict (l : list (rel_expr * rel_expr))
| REInsert (d k v : rel_expr)
| REDelete (d k : rel_expr)
| RELookup (d k : rel_expr)
(* constructs for relational algebra *)
| REFilter (e1 : rel_expr) (x : string) (p : rel_expr) (e2 : rel_expr)
| REJoin (e1 : rel_expr) (x : string) (e2 : rel_expr) (y : string) (p e3 : rel_expr)
| REProject (e1 : rel_expr) (cols : list string) (x : string) (e2 : rel_expr)
| RExpr (e : expr) (* ??? placeholer *).

Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Section WithMap.
    Local Notation value := (value (word := word)).
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    Fixpoint restrict_record_to_col (r : list (string * value)) (col : string) : list (string * value) :=
      match r with
      | nil => nil
      | (s, v) :: r => if String.eqb s col then (s, v) :: nil else restrict_record_to_col r col
      end.

    Definition restrict_record_to_cols (r : list (string * value)) (cols : list string) : list (string * value) :=
      concat (List.map (restrict_record_to_col r) cols).

    Definition restrict_record (cols : list string) (v : value) : value :=
      match v with
      | VRecord l => VRecord (restrict_record_to_cols l cols)
      | v => v
      end.

    Fixpoint rel_interp_expr (store env : locals) (e : rel_expr) :=
      match e with
      | REVar x => get_local env x
      | RELoc x => get_local store x
      | REAtom a => interp_atom a
      | REUnop o e => (interp_unop o) (rel_interp_expr store env e)
      | REBinop o e1 e2 => (interp_binop o) (rel_interp_expr store env e1) (rel_interp_expr store env e2)
      | REIf e1 e2 e3 =>
          match rel_interp_expr store env e1 with
          | VBool true => rel_interp_expr store env e2
          | VBool false => rel_interp_expr store env e3
          | _ => VUnit
          end
      | RELet e1 x e2 => rel_interp_expr store (set_local env x (rel_interp_expr store env e1)) e2
      | REFlatmap e1 x e2 =>
          match rel_interp_expr store env e1 with
          | VList l1 =>
              VList (flat_map (fun v =>
                                 match rel_interp_expr store (set_local env x v) e2 with
                                 | VList l2 => l2
                                 | _ => nil
                                 end) l1)
          | _ => VUnit
          end
      | REFold e1 e2 x y e3 =>
          match rel_interp_expr store env e1 with
          | VList l1 =>
              let a := rel_interp_expr store env e2 in
              let f := fun v acc => rel_interp_expr store (set_local (set_local env x v) y acc) e3 in
              fold_right f a l1
          | _ => VUnit
          end
      | RERecord l => VRecord (record_sort (List.map (fun '(s, e) => (s, rel_interp_expr store env e)) l))
      | REProj r s =>
          match rel_interp_expr store env r with
          | VRecord l => record_proj s l
          | _ => VUnit
          end
      | REDict l => VDict (dict_sort (List.map
                                        (fun '(k, v) => (rel_interp_expr store env k, rel_interp_expr store env v))
                                        l))
      | REInsert d k v =>
          match rel_interp_expr store env d with
          | VDict l => VDict (dict_insert (rel_interp_expr store env k) (rel_interp_expr store env v) l)
          | _ => VUnit
          end
      | REDelete d k =>
          match rel_interp_expr store env d with
          | VDict l => VDict (dict_delete (rel_interp_expr store env k) l)
          | _ => VUnit
          end
      | RELookup d k =>
          match rel_interp_expr store env d with
          | VDict l => VOption (dict_lookup (rel_interp_expr store env k) l)
          | _ => VUnit
          end
      (* constructs for relational algebra *)
      | REFilter e1 x p e2 => match rel_interp_expr store env e1 with
                              | VList l1 => VList (flat_map (fun v =>
                                                               match rel_interp_expr store (map.put env x v) p with
                                                               | VBool true =>
                                                                   match rel_interp_expr store (map.put env x v) e2 with
                                                                   | VList l2 => l2
                                                                   | _ => nil
                                                                   end
                                                               | _ => nil
                                                               end) l1)
                              | _ => VUnit
                              end
      | REJoin e1 x e2 y p e3 => match rel_interp_expr store env e1 with
                                   | VList l1 =>
                                       match rel_interp_expr store env e2 with
                                       | VList l2 =>
                                           VList (flat_map (fun v1 =>
                                                              flat_map (fun v2 =>
                                                                          let env' := map.put (map.put env x v1) y v2 in
                                                                          match rel_interp_expr store env' p with
                                                                          | VBool true => match rel_interp_expr store env' e3 with
                                                                                          | VList l3 => l3
                                                                                          | _ => nil
                                                                                          end
                                                                          | _ => nil
                                                                          end) l2) l1)
                                       | _ => VUnit
                                       end
                                 | _ => VUnit
                                 end
      | REProject e1 cols x e2 => match rel_interp_expr store env e1 with
                                  | VList l => VList (flat_map (fun v =>
                                                                  match rel_interp_expr store (map.put env x v) e2 with
                                                                  | VList l2 => l2
                                                                  | _ => nil
                                                                  end)
                                                        (List.map (restrict_record cols) l))
                                  | _ => VUnit
                                  end
      | RExpr e => interp_expr store env e (* ??? placeholer *)
      end.

    (* Some correspondence between expr and rel_expr *)
    Fixpoint to_rel_expr (e : expr) : rel_expr :=
      match e with
      | EFlatmap e1 x (EIf p e2 (EAtom (ANil _))) =>
          REFilter (to_rel_expr e1) x (to_rel_expr p) (to_rel_expr e2)
      | EFlatmap e1 x (EFlatmap e2 y (EIf p e3 (EAtom (ANil _)))) =>
          REJoin (to_rel_expr e1) x (to_rel_expr e2) y (to_rel_expr p) (to_rel_expr e3)
      | e' => RExpr e'
      end.
  End WithMap.
End WithWord.

(* Notations *)
Coercion EVar : string >-> expr.
Coercion AInt : Z >-> atom.
Coercion ABool : bool >-> atom.
Coercion EAtom : atom >-> expr.
