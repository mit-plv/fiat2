Require Import fiat2.Language fiat2.Value fiat2.Interpret fiat2.TypeSystem fiat2.TypeSound.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import List String ZArith.

Fixpoint repeat_string (s : string) (n : nat) : string :=
  match n with
  | O => ""
  | S n => s ++ repeat_string s n
  end.

Definition fresh_var (x : string) (free_vars : list string) :=
  if inb String.eqb x free_vars
  then append x (repeat_string "'" (S (list_max (List.map length free_vars))))
  else x.

Fixpoint sub_lookup {A} (x : string) (l : list (string * A)) : option A :=
  match l with
  | nil => None
  | (y, a) :: l => if String.eqb x y then Some a else sub_lookup x l
  end.

Fixpoint substitute (sub : list (string * expr)) (free_vars : list string) (e0 : expr) : expr :=
  (* Expect sub to map every free immutable variable in e0 to some expression *)
  (* free_vars should contain all free variables in the range of the sub argument that must not be captured *)
  match e0 with
  | EVar x => match sub_lookup x sub with
              | Some e => e
              | None => EVar x
              end
  | ELoc x => ELoc x
  | EAtom a => EAtom a
  | EUnop o e0 => EUnop o (substitute sub free_vars e0)
  | EBinop o e1 e2 => EBinop o (substitute sub free_vars e1) (substitute sub free_vars e2)
  | EIf e1 e2 e3 => EIf (substitute sub free_vars e1) (substitute sub free_vars e2) (substitute sub free_vars e3)
  | ELet e1 x e2 =>
      let x' := fresh_var x free_vars in
      ELet (substitute sub free_vars e1) x'
        (substitute ((x, EVar x') :: sub) (x' :: free_vars) e2)
  | EFlatmap e1 x e2  =>
      let x' := fresh_var x free_vars in
      EFlatmap (substitute sub free_vars e1) x'
        (substitute ((x, EVar x') :: sub) (x' :: free_vars) e2)
  | EFold e1 e2 v acc e3 =>
      let v' := fresh_var v free_vars in
      let acc' := fresh_var acc (v' :: free_vars) in
      EFold (substitute sub free_vars e1) (substitute sub free_vars e2) v' acc'
        (substitute ((acc, EVar acc') :: (v, EVar v') :: sub) (acc' :: v' :: free_vars) e3)
  | ERecord l => ERecord (List.map (fun '(s, e) => (s, substitute sub free_vars e)) l)
  | EAccess e s => EAccess (substitute sub free_vars e) s
  | EDict l => EDict (List.map (fun '(ke, ve) => (substitute sub free_vars ke, substitute sub free_vars ve)) l)
  | EInsert d k v => EInsert (substitute sub free_vars d) (substitute sub free_vars k) (substitute sub free_vars v)
  | EDelete d k => EDelete (substitute sub free_vars d) (substitute sub free_vars k)
  | ELookup d k => ELookup (substitute sub free_vars d) (substitute sub free_vars k)
  | EOptMatch e1 e2 x e3 =>
      let x' := fresh_var x free_vars in
      EOptMatch (substitute sub free_vars e1) (substitute sub free_vars e2) x'
        (substitute ((x, EVar x') :: sub) (x' :: free_vars) e3)
  | EDictFold d e0 k v acc e =>
      let k' := fresh_var k free_vars in
      let v' := fresh_var v (k' :: free_vars) in
      let acc' := fresh_var acc (v' :: k' :: free_vars) in
      EDictFold (substitute sub free_vars d) (substitute sub free_vars e0) k' v' acc'
        (substitute ((acc, EVar acc') :: (v, EVar v') :: (k, EVar k') :: sub) (acc' :: v' :: k' :: free_vars) e)
  | ESort e => ESort (substitute sub free_vars e)
  | EFilter l x p =>
      let x' := fresh_var x free_vars in
      EFilter (substitute sub free_vars l) x'
        (substitute ((x, EVar x') :: sub) (x' :: free_vars) p)
  | EJoin l1 l2 x y p r =>
      let x' := fresh_var x free_vars in
      let y' := fresh_var y (x' :: free_vars) in
      EJoin (substitute sub free_vars l1) (substitute sub free_vars l2) x' y'
        (substitute ((y, EVar y') :: (x, EVar x') :: sub) (y' :: x' :: free_vars) p)
        (substitute ((y, EVar y') :: (x, EVar x') :: sub) (y' :: x' :: free_vars) r)
  | EProj l x r =>
      let x' := fresh_var x free_vars in
      EProj (substitute sub free_vars l) x'
        (substitute ((x, EVar x') :: sub) (x' :: free_vars) r)
  end.

Definition get_free_vars {A} {tenv : map.map string A} : tenv -> list string :=
  map.fold (fun l x _ => x :: l) nil.

Definition expr_consistent {width : Z} {word : word width} {locals : map.map string value}
  (consistent : value (width:=width) -> value -> Prop) (store env : locals) (e1 e2 : expr) :=
  consistent (interp_expr store env e1) (interp_expr store env e2).

Class index :=
  mk {
      hole : string;
      to_idx : expr;
      from_idx : expr;
      idx_ty : type -> type;
      is_tbl_ty : type -> bool;
    }.

Class ok {consistency : Type} (to_from_con from_to_con : consistency) (idx : index)
  {width: Z} {word: word.word width} {word_ok: word.ok word} (idx_wf : value -> Prop)
  (consistent : consistency -> value (width:=width) -> value -> Prop)
  {tenv : map.map string type} {tenv_ok : map.ok tenv}
  {locals : map.map string value} {locals_ok : map.ok locals} :=
  { idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t);
    to_idx_ty : forall (t : type),
      type_wf t -> is_tbl_ty t = true ->
      type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t);
    from_idx_ty : forall (t : type),
      type_wf t -> is_tbl_ty t = true ->
      type_of map.empty (map.put map.empty hole (idx_ty t)) from_idx t;
    to_idx_wf : forall (v : value) (t : type),
      type_wf t -> is_tbl_ty t = true ->
      type_of_value v t ->
      idx_wf (interp_expr map.empty (map.put map.empty hole v) to_idx);
    (* to_from_consistent : forall (e : expr) (Gstore Genv : tenv)  (t : type),
      is_tbl_ty t = true ->
      tenv_wf Gstore -> tenv_wf Genv ->
      type_of Gstore Genv e t ->
      forall (store env : locals),
      locals_wf Gstore store -> locals_wf Genv env ->
      expr_consistent (consistent to_from_con) store env e
        (substitute ((hole, (substitute ((hole, e) :: nil) (get_free_vars Genv) to_idx)) :: nil)
           (get_free_vars Genv) from_idx); *)
    to_from_consistent : forall v t,
      type_wf t -> is_tbl_ty t = true ->
      type_of_value v t ->
      consistent to_from_con
        v
        (interp_expr map.empty (map.put map.empty hole (interp_expr map.empty (map.put map.empty hole v) to_idx)) from_idx);
    (* from_to_consistent : forall (e : expr) (Gstore Genv : tenv) (t : type),
      is_tbl_ty t = true ->
      tenv_wf Gstore -> tenv_wf Genv ->
      type_of Gstore Genv e (idx_ty t) ->
      forall (store env : locals),
      locals_wf Gstore store -> locals_wf Genv env ->
      idx_wf (interp_expr store env e) ->
      expr_consistent (consistent from_to_con) store env e
        (substitute ((hole, (substitute ((hole, e) :: nil) (get_free_vars Genv) from_idx)) :: nil)
           (get_free_vars Genv) to_idx); *)
    from_to_consistent : forall v t,
      type_wf t -> is_tbl_ty t = true ->
      type_of_value v (idx_ty t) ->
      idx_wf v ->
      consistent from_to_con
        v
        (interp_expr map.empty (map.put map.empty hole (interp_expr map.empty (map.put map.empty hole v) from_idx)) to_idx);
  }.

Arguments IndexInterface.Build_ok {consistency}%type_scope {to_from_con} {from_to_con} idx {width}%Z_scope {word}
  {word_ok} idx_wf {consistent}%function_scope {tenv tenv_ok locals locals_ok}
  (idx_ty_wf to_idx_ty from_idx_ty to_idx_wf to_from_consistent from_to_consistent)%function_scope.

(*
Using collection_tag as consistency, state the corresponding consistent predicate. Show that assuming to_from_consistent and from_to_consistent, with the corresponding "can_transf_to_idx" under that consistency model, we can "transf_to_idx for write and transf_from_idx for read" and maintain the semantics of the top-level expr and command.
 *)
