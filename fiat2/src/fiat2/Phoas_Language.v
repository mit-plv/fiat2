Require Import fiat2.Language fiat2.Interpret fiat2.Value.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import String ZArith List.

Section WithPhoasEnv.
  Context {V : Type}.
  Context {phoas_env: map.map string V} {phoas_env_ok: map.ok phoas_env}.

  (* PHOAS abstract syntax tree *)
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

  (* PHOAS interpreter *)
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
