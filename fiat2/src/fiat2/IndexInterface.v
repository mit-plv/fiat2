Require Import fiat2.Language fiat2.Value fiat2.Interpret fiat2.TypeSystem fiat2.TypeSound.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
From Stdlib Require Import List String ZArith.

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

(* There is no second interface for an index that needs a precondition on the
   table before it may be built, and there cannot need to be one: to_idx is an
   expression of the language, hence total, so "the index is what to_idx
   computed" is an idx_wf that holds of every well-typed table and makes every
   index an instance of ok above.

   A claim that holds of some tables and not others -- a primary-key index's
   dictionary mapping each key to a SINGLE row, say -- is therefore not stated
   here.  It is a strictly stronger relation stated beside the index
   (UniqueDictIndexImpl.idx_wf_unique), assembled where a rewrite needs it from
   the unconditional relation the installation gives and the constraint the
   program maintains (UniqueIndexInstall.idx_wf__idx_wf_unique).  A declaration
   decides which questions an index can answer, not whether it may be built. *)
