Require Import ZArith String List DecimalString.
Require Import fiat2.Language fiat2.Value.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.

Local Open Scope Z_scope.

Section WithWord.
  Context {width: Z} {word: word.word width}.
  Context {word_ok: word.ok word}.

  Notation value := (value (word := word)).

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
                 | VList l => VInt (Z.of_nat (List.length l))
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
    | (k', v') :: l => if value_ltb k k' then (k, v) :: (k', v') :: l
                      else if value_eqb k k' then (k, v) :: l
                           else (k', v') :: dict_insert k v l
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
      | ELet e1 x e2 => interp_expr store (map.put env x (interp_expr store env e1)) e2
      | EFlatmap e1 x e2 =>
          match interp_expr store env e1 with
          | VList l1 => VList (flat_map (fun v => match interp_expr store (map.put env x v) e2 with
                                                  | VList l2 => l2
                                                  | _ => nil
                                                  end) l1)
          | _ => VUnit
          end
      | EFold e1 e2 x y e3 =>
          match interp_expr store env e1 with
          | VList l1 => let a := interp_expr store env e2 in
                        let f := fun v acc => interp_expr store (map.put (map.put env x v) y acc) e3 in
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
                            (List.dedup (fun p p' => value_eqb (fst p) (fst p'))
                               (List.map (fun '(k, v) => (interp_expr store env k, interp_expr store env v)) l)))
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
      | EOptMatch e e_none x e_some =>
          match interp_expr store env e with
          | VOption None => interp_expr store env e_none
          | VOption (Some v) => interp_expr store (map.put env x v) e_some
          | _ => VUnit
          end
      | EDictFold d e0 x y z e =>
          match interp_expr store env d with
          | VDict l => fold_right (fun v acc => interp_expr store (map.put (map.put (map.put env x (fst v)) y (snd v)) z acc) e) (interp_expr store env e0) l
          | _ => VUnit
          end
      | ESort l =>
          match interp_expr store env l with
          | VList l => VList (value_sort l)
          | _ => VUnit
          end
      | EFilter l x p =>
          match interp_expr store env l with
          | VList l => VList (List.filter
                                (fun v =>
                                   let env' := map.put env x v in
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
                                          (fun v2 => interp_expr store (map.put (map.put env x v1) y v2) r)
                                          (List.filter
                                             (fun v2 => match interp_expr store (map.put (map.put env x v1) y v2) p with
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
          | VList l => VList (List.map (fun v => interp_expr store (map.put env x v) r) l)
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
          let env' := map.put env x (interp_expr store env e) in
          interp_command store env' c
      | CLetMut e x c1 =>
          let store' := map.put store x (interp_expr store env e) in
          let store'' := interp_command store' env c1 in
          map.update store'' x (map.get store x)
      | CAssign x e => map.put store x (interp_expr store env e)
      | CIf e c1 c2 => match interp_expr store env e with
                       | VBool b => if b then interp_command store env c1 else interp_command store env c2
                       | _ => store (* unreachable cases *)
                       end
      | CForeach e x c =>
          match interp_expr store env e with
          | VList l => fold_left (fun store' v => interp_command store' (map.put env x v) c) l store
          | _ => store (* unreachable cases *)
          end
      end.
  End WithMap.
End WithWord.
