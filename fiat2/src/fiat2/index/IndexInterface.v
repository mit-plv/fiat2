Require Import fiat2.Language fiat2.Value fiat2.Interpret fiat2.TypeSystem fiat2.TypeSound fiat2.Utils.
Require Import coqutil.Map.Interface.
From Stdlib Require Import List String ZArith.

Class index :=
  mk {
      hole : string;
      to_idx : expr;
      idx_ty : type -> type;
      is_tbl_ty : type -> bool;
    }.

Class ok (idx : index) {tenv : map.map string type} {tenv_ok : map.ok tenv} :=
  { to_idx_ty : forall (t : type),
      type_wf t -> is_tbl_ty t = true ->
      type_of map.empty (map.put map.empty hole t) to_idx (idx_ty t) }.

Arguments IndexInterface.Build_ok idx {tenv tenv_ok} to_idx_ty%_function_scope.

Lemma idx_ty_wf {idx : index} {tenv : map.map string type} {tenv_ok : map.ok tenv} {idx_ok : ok idx} :
  forall t, type_wf t -> is_tbl_ty t = true -> type_wf (idx_ty t).
Proof.
  intros t H_wf H_is.
  eapply type_of__type_wf; [ | | apply to_idx_ty; eauto ].
  1: apply tenv_wf_empty.
  1: apply tenv_wf_step; auto using tenv_wf_empty.
Qed.
