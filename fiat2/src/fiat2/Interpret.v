From Stdlib Require Import ZArith String List DecimalString.
Require Import fiat2.Language fiat2.Value.
Require Import coqutil.Word.Interface coqutil.Map.Interface coqutil.Datatypes.Result.

Local Open Scope Z_scope.

Fixpoint flat_map2 {A B C : Type} (f : A -> B -> list C) (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
  | nil, _ | _, nil => nil
  | x1 :: l1, x2 :: l2 => f x1 x2 ++ flat_map2 f l1 l2
  end.

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
    | AEmptyDict _ => VDict nil
    | AEmptyBag _ => VBag nil
    | AEmptySet _ => VSet nil
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

  Fixpoint bag_insert (v : value) (l : list (value * nat)) :=
    match l with
    | nil => (v, S 0) :: nil
    | (v', n') :: l => if value_ltb v v' then (v, S 0) :: (v', n') :: l
                      else if value_eqb v v' then (v, (S n')%nat) :: l
                           else (v', n') :: bag_insert v l
    end.

  Definition list_to_bag : list value -> list (value * nat):=
    fold_right bag_insert nil.

  Definition bag_to_list : list (value * nat) -> list value :=
    flat_map (fun p => repeat (fst p) (snd p)).

  Fixpoint set_insert (v : value) (l : list value) :=
    match l with
    | nil => v :: nil
    | v' :: l' => if value_ltb v v' then v :: v' :: l'
                  else if value_eqb v v' then l
                       else v' :: set_insert v l'
    end.

  Definition list_to_set : list value -> list value :=
    fold_right set_insert nil.

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
    | OBagInsert => match a with
                    | VBag l => VBag (bag_insert b l)
                    | _ => VUnit
                    end
    | OSetInsert => match a with
                    | VSet l => VSet (set_insert b l)
                    | _ => VUnit
                    end
    | OLookup => match a, b with
                 | VDict d, k => VOption (dict_lookup k d)
                 | _, _ => VUnit
                 end
    | ODelete => match a, b with
                 | VDict d, k => VDict (dict_delete k d)
                 | _, _ => VUnit
                 end
    end.

  Definition interp_ternop (o : ternop) (a b c : value) : value :=
    match o with
    | OInsert => match a, b, c with
                 | VDict d, k, v => VDict (dict_insert k v d)
                 | _, _, _ => VUnit
                 end
    end.

  Definition interp_aggr (ag : aggr) : (value * (value -> value -> value)) :=
    match ag with
    | AGSum => (VInt 0, apply_int_binop Z.add)
    | AGCount => (VInt 0, fun _ => apply_int_binop Z.add (VInt 1))
    end.

  Definition interp_aci_aggr (ag : aci_aggr) : (value * (value -> value -> value)) :=
    match ag with
    | AGMin => (VOption None, fun v acc => match acc with
                                           | VOption None => VOption (Some v)
                                           | VOption (Some (VInt v')) =>
                                               match v with
                                               | VInt v => VOption (Some (VInt (Z.min v v')))
                                               | _ => VUnit
                                               end
                                           | _ => VUnit
                                           end)
    | AGMax => (VOption None, fun v acc => match acc with
                                           | VOption None => VOption (Some v)
                                           | VOption (Some (VInt v')) =>
                                               match v with
                                               | VInt v => VOption (Some (VInt (Z.max v v')))
                                               | _ => VUnit
                                               end
                                           | _ => VUnit
                                           end)
    end.

  Definition record_proj (s : string) (l : list (string * value)) : value :=
    match access_record l s with
    | Success v => v
    | _ => VUnit
    end.

  Lemma access_record__record_proj : forall l x v, access_record l x = Success v -> record_proj x l = v.
  Proof.
    intros * H. unfold record_proj; rewrite H. reflexivity.
  Qed.

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
      | ETernop o e1 e2 e3 => interp_ternop o (interp_expr store env e1)
                                (interp_expr store env e2) (interp_expr store env e3)
      | EIf e1 e2 e3 => match interp_expr store env e1 with
                        | VBool b => if b then interp_expr store env e2 else interp_expr store env e3
                        | _ => VUnit
                        end
      | ELet e1 x e2 => interp_expr store (map.put env x (interp_expr store env e1)) e2
      | EFlatmap tag e1 x e2 =>
          match tag with
          | LikeList =>
              match interp_expr store env e1 with
              | VList l1 => VList (flat_map (fun v => match interp_expr store (map.put env x v) e2 with
                                                      | VList l2 => l2
                                                      | _ => nil
                                                      end) l1)
              | _ => VUnit
              end
          | LikeBag =>
              match interp_expr store env e1 with
              | VBag l1 => VBag (list_to_bag (flat_map (fun v => match interp_expr store (map.put env x v) e2 with
                                                        | VBag l2 => bag_to_list l2
                                                        | _ => nil
                                                        end) (bag_to_list l1)))
              | _ => VUnit
              end
          | LikeSet =>
              match interp_expr store env e1 with
              | VSet l1 => VSet (list_to_set (flat_map (fun v => match interp_expr store (map.put env x v) e2 with
                                                        | VSet l2 => l2
                                                        | _ => nil
                                                        end) l1))
              | _ => VUnit
              end
          end
      | EFlatmap2 e1 e2 x1 x2 e3 =>
          match interp_expr store env e1 with
          | VList l1 =>
              match interp_expr store env e2 with
              | VList l2 =>
                  VList (flat_map2 (fun v1 v2 => match interp_expr store (map.put (map.put env x1 v1) x2 v2) e3 with
                                           | VList l3 => l3
                                           | _ => nil
                                                 end) l1 l2)
              | _ => VUnit
              end
          | _ => VUnit
          end
      | EFold e1 e2 x y e3 =>
          match interp_expr store env e1 with
          | VList l1 => let a := interp_expr store env e2 in
                        let f := fun v acc => interp_expr store (map.put (map.put env x v) y acc) e3 in
                        fold_right f a l1
          | _ => VUnit
          end
      | EACFold ag e =>
          let '(zr, op) := interp_aggr ag in
          match interp_expr store env e with
          | VBag l =>
              fold_right op zr (bag_to_list l)
          | _ => VUnit
          end
      | EACIFold ag e =>
          let '(zr, op) := interp_aci_aggr ag in
          match interp_expr store env e with
          | VSet l =>
              fold_right op zr l
          | _ => VUnit
          end
      | ERecord l => VRecord (record_sort
                                (List.map (fun '(s, e) => (s, (interp_expr store env e))) l))
      | EAccess r s => match interp_expr store env r with
                       | VRecord l => record_proj s l
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
      | ESort tag l =>
          match tag with
          | LikeList =>
              match interp_expr store env l with
              | VList l => VList (value_sort l)
              | _ => VUnit
            end
          | LikeBag =>
              match interp_expr store env l with
              | VBag l => VList (bag_to_list l)
              | _ => VUnit
              end
          | LikeSet =>
              match interp_expr store env l with
              | VSet l => VList l
              | _ => VUnit
              end
          end
      | EFilter tag l x p =>
          match tag with
          | LikeList =>
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
          | LikeBag =>
              match interp_expr store env l with
              | VBag l => VBag (List.filter
                                    (fun v =>
                                       let env' := map.put env x (fst v) in
                                       match interp_expr store env' p with
                                       | VBool b => b
                                       | _ => false
                                       end) l)
              | _ => VUnit
              end
          | LikeSet =>
              match interp_expr store env l with
              | VSet l => VSet (List.filter
                                  (fun v =>
                                     let env' := map.put env x v in
                                     match interp_expr store env' p with
                                     | VBool b => b
                                     | _ => false
                                     end) l)
              | _ => VUnit
              end
          end
      | EJoin tag l1 l2 x y p r =>
          match tag with
          | LikeList =>
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
          | LikeBag =>
              match interp_expr store env l1 with
              | VBag l1 =>
                  match interp_expr store env l2 with
                  | VBag l2 => VBag (list_to_bag
                                       (flat_map
                                          (fun v1 =>
                                             List.map
                                               (fun v2 => interp_expr store (map.put (map.put env x v1) y v2) r)
                                               (List.filter
                                                  (fun v2 => match interp_expr store (map.put (map.put env x v1) y v2) p with
                                                             | VBool b => b
                                                             | _ => false
                                                             end)
                                                  (bag_to_list l2)))
                                          (bag_to_list l1)))
                  | _ => VUnit
                  end
              | _ => VUnit
              end
          | LikeSet =>
              match interp_expr store env l1 with
              | VSet l1 =>
                  match interp_expr store env l2 with
                  | VSet l2 => VSet (list_to_set
                                       (flat_map
                                          (fun v1 =>
                                             List.map
                                               (fun v2 => interp_expr store (map.put (map.put env x v1) y v2) r)
                                               (List.filter
                                                  (fun v2 => match interp_expr store (map.put (map.put env x v1) y v2) p with
                                                             | VBool b => b
                                                             | _ => false
                                                             end)
                                                  l2))
                                          l1))
                  | _ => VUnit
                  end
              | _ => VUnit
              end
          end
      | EProj tag l x r =>
          match tag with
          | LikeList =>
            match interp_expr store env l with
            | VList l => VList (List.map (fun v => interp_expr store (map.put env x v) r) l)
            | _ => VUnit
            end
          | LikeBag =>
              match interp_expr store env l with
              | VBag l => VBag (list_to_bag
                                  (List.map
                                     (fun v => interp_expr store (map.put env x v) r)
                                     (bag_to_list l)))
              | _ => VUnit
            end
          | LikeSet =>
              match interp_expr store env l with
              | VSet l => VSet (list_to_set
                                  (List.map
                                     (fun v => interp_expr store (map.put env x v) r)
                                     l))
              | _ => VUnit
            end
          end
      | EBagOf l => match interp_expr store env l with
                    | VList l => VBag (list_to_bag l)
                    | _ => VUnit
                    end
      | ESetOf l => match interp_expr store env l with
                    | VList l => VSet (list_to_set l)
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
