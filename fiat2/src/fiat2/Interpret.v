From Stdlib Require Import ZArith String List DecimalString.
Require Import fiat2.Language fiat2.Value.
Require Import coqutil.Word.Interface coqutil.Map.Interface coqutil.Datatypes.Result.

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
    | AEmptyDict _ _ => VDict nil
    | AEmptyBag _ => VBag nil
    | AEmptySet _ => VSet nil
    | AUnit => VUnit
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
    | ODictValues => match v with
                     | VDict d => VBag (list_to_bag (List.map snd d))
                     | _ => VUnit
                     end
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

  Fixpoint set_insert (v : value) (l : list value) :=
    match l with
    | nil => v :: nil
    | v' :: l' => if value_ltb v v' then v :: v' :: l'
                  else if value_eqb v v' then l
                       else v' :: set_insert v l'
    end.

  Definition list_to_set : list value -> list value :=
    fold_right set_insert nil.

  Definition set_mem (v : value) (l : list value) : bool :=
    existsb (value_eqb v) l.

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
    (* inserting the elements of one set into the other keeps the result sorted and duplicate-free *)
    | OSetUnion => match a, b with
                   | VSet l1, VSet l2 => VSet (fold_right set_insert l2 l1)
                   | _, _ => VUnit
                   end
    | OSetIntersect => match a, b with
                       | VSet l1, VSet l2 => VSet (filter (fun v => set_mem v l2) l1)
                       | _, _ => VUnit
                       end
    | OSetDiff => match a, b with
                  | VSet l1, VSet l2 => VSet (filter (fun v => negb (set_mem v l2)) l1)
                  | _, _ => VUnit
                  end
    | OSetMem => match a with
                 | VSet l => VBool (set_mem b l)
                 | _ => VUnit
                 end
    (* whether the second string occurs in the first *)
    | OStrContains => match a, b with
                      | VString s, VString p =>
                          VBool (match String.index 0 p s with
                                 | Some _ => true
                                 | None => false
                                 end)
                      | _, _ => VUnit
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

  (* A bound is an OPTION because a key type need not have a least or a greatest
     element to name: a TInt key has no infinity.  An absent bound therefore does
     not constrain the key, which is how a one-sided range is written.  Only
     well-typed values reach these, where the bound is a VOption; anything else
     is read as absent, in the same spirit as the VUnit defaults above. *)
  Definition above_lo (lo k : value) : bool :=
    match lo with
    | VOption (Some l) => negb (value_ltb k l)
    | _ => true
    end.

  Definition below_hi (hi k : value) : bool :=
    match hi with
    | VOption (Some h) => value_ltb k h
    | _ => true
    end.

  (* k is in range when it satisfies every bound that is present *)
  Definition in_key_range (lo hi k : value) : bool := andb (above_lo lo k) (below_hi hi k).

  (* the entries of d whose keys are in range: lo <= k < hi, half-open, and
     either side may be absent *)
  Definition dict_range (lo hi : value) (d : list (value * value)) : list (value * value) :=
    filter (fun p => in_key_range lo hi (fst p)) d.

  (* and the entries whose keys are NOT.  Defined as the negation of the same
     test, so that dict_range and dict_range_delete partition the dictionary by
     construction rather than by a lemma. *)
  Definition dict_range_delete (lo hi : value) (d : list (value * value)) : list (value * value) :=
    filter (fun p => negb (in_key_range lo hi (fst p))) d.

  Definition interp_ternop (o : ternop) (a b c : value) : value :=
    match o with
    | OInsert => match a, b, c with
                 | VDict d, k, v => VDict (dict_insert k v d)
                 | _, _, _ => VUnit
                 end
    (* the substring of a starting at position b with length c;
       negative positions and lengths count as 0, and it stops at the end of a *)
    | OSubstring => match a, b, c with
                    | VString s, VInt i, VInt n => VString (String.substring (Z.to_nat i) (Z.to_nat n) s)
                    | _, _, _ => VUnit
                    end
    | ODictRange => match a with
                    | VDict d => VDict (dict_range b c d)
                    | _ => VUnit
                    end
    | ODictRangeDelete => match a with
                          | VDict d => VDict (dict_range_delete b c d)
                          | _ => VUnit
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
