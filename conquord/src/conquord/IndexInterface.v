Require Import conquord.Language conquord.Value conquord.Interpret conquord.TypeSystem conquord.TypeSound.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import List String ZArith.

Class index :=
  mk {
      hole : string;
      to_idx : expr;
      idx_ty : type -> type;
      is_tbl_ty : type -> bool;
    }.

Class ok (idx : index)
  {width: Z} {word: word.word width} {word_ok: word.ok word} (idx_wf : value (width:=width) -> value (width:=width) -> Prop)
  {tenv : map.map string type} {tenv_ok : map.ok tenv}
  {locals : map.map string value} {locals_ok : map.ok locals} :=
  { idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t);
    to_idx_ty : forall (t : type),
      type_wf t -> is_tbl_ty t = true ->
      type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t);
    to_idx_wf : forall (v : value) (t : type),
      type_wf t -> is_tbl_ty t = true ->
      type_of_value v t ->
      idx_wf v (interp_expr map.empty (map.put map.empty hole v) to_idx);
  }.

Arguments IndexInterface.Build_ok idx {width}%Z_scope {word}
  {word_ok} idx_wf {tenv tenv_ok locals locals_ok}
  (idx_ty_wf to_idx_ty to_idx_wf)%function_scope.
