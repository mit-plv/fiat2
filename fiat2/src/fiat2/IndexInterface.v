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

(* An index whose well-formedness is a claim about some tables and not others.

   A primary-key index is the reason this exists.  The dictionary it builds
   maps a key to a single row, so "this index represents that table" is a
   statement about tables whose keys are distinct and about no others.  ok
   cannot say that: its to_idx_wf quantifies over every well-typed table, so an
   index that needs a precondition is not an instance of it at the idx_wf it
   actually wants.

   tbl_pre does not make the interface stronger.  Instantiated with
   fun v => idx_wf v (interp_expr ...), to_idx_wf_pre is a tautology, exactly as
   ok says nothing once idx_wf is instantiated with a predicate that holds
   everywhere.  What tbl_pre does is record, at the interface, what a
   transformation owes before it may install the index: being a well-typed
   table is no longer enough.  Whoever installs the index discharges it, and
   for a declared constraint the declaration is what discharges it. *)
Class ok_pre (idx : index)
  {width: Z} {word: word.word width} {word_ok: word.ok word}
  (idx_wf : value (width:=width) -> value (width:=width) -> Prop)
  (tbl_pre : value (width:=width) -> Prop)
  {tenv : map.map string type} {tenv_ok : map.ok tenv}
  {locals : map.map string value} {locals_ok : map.ok locals} :=
  { ok_pre_idx_ty_wf : forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t);
    ok_pre_to_idx_ty : forall (t : type),
      type_wf t -> is_tbl_ty t = true ->
      type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t);
    ok_pre_to_idx_wf : forall (v : value) (t : type),
      type_wf t -> is_tbl_ty t = true ->
      type_of_value v t ->
      tbl_pre v ->
      idx_wf v (interp_expr map.empty (map.put map.empty hole v) to_idx);
  }.

(* An ordinary index is the case where the precondition is trivial, so nothing
   that already satisfies ok has to be restated to be used through ok_pre. *)
Definition ok__ok_pre (idx : index)
  {width: Z} {word: word.word width} {word_ok: word.ok word}
  (idx_wf : value (width:=width) -> value (width:=width) -> Prop)
  {tenv : map.map string type} {tenv_ok : map.ok tenv}
  {locals : map.map string value} {locals_ok : map.ok locals}
  (idx_ok : ok idx idx_wf) : ok_pre idx idx_wf (fun _ => True) :=
  {| ok_pre_idx_ty_wf := idx_ty_wf;
     ok_pre_to_idx_ty := to_idx_ty;
     ok_pre_to_idx_wf := fun v t H_wf H_tbl H_v _ => to_idx_wf v t H_wf H_tbl H_v |}.
