Require Import fiat2.Language fiat2.Value fiat2.Interpret fiat2.TypeSystem fiat2.TypeSound.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import List String ZArith.

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
    to_from_consistent : forall v t,
      type_wf t -> is_tbl_ty t = true ->
      type_of_value v t ->
      consistent to_from_con
        v
        (interp_expr map.empty (map.put map.empty hole (interp_expr map.empty (map.put map.empty hole v) to_idx)) from_idx);
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
