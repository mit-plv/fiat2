Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.Utils fiat2.Substitute
  fiat2.index.IndexTransf.
Require Import coqutil.Map.Interface.
From Stdlib Require Import String List.

Import ListNotations.

(* ====================================================================
   INDEX WELLFORMEDNESS AS A FACT ABOUT THE PROGRAM.

   Today a rewrite that reads an index receives the index's invariant by
   BUNDLING: apply_idx_related_transfs installs at a table and immediately
   hands the rules it just established.  That is why only one table's
   gated rules can run -- the hypothesis is produced and consumed in one
   step, so a second table has nowhere to get it from.

   Declarations already avoid this.  UniqueIndexGate puts them in a cenv
   BESIDE the program, gates rewrites on a decidable match against it, and
   makes the pipeline owe cenv_respected.  Its reason applies verbatim to
   index facts, and more sharply: the syntax that witnesses "this table is
   indexed" is the record initializer, and the erase phase DELETES the
   list field once nothing reads it, so the witness is itself a rewrite
   target.

   What an environment of index facts needs is this file's subject: the
   facts have to be stable under what the rest of the pipeline does.  An
   installation at one table must not disturb another table's fact.
   ==================================================================== *)

Section IndexFactAcrossTables.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Notation value := (value).
  Context {locals : map.map string value} {locals_ok : map.ok locals}.
  Context (id_tag aux_tag : string) (H_tags_diff : id_tag <> aux_tag).

  (* the table being installed now, with its index *)
  Context {idx_a : IndexInterface.index} {idx_wf_a : value -> value -> Prop}
    {idx_ok_a : IndexInterface.ok idx_a idx_wf_a}.
  (* and another table's index, whose wellformedness we are carrying *)
  Context {idx_b : IndexInterface.index} {idx_wf_b : value -> value -> Prop}
    {idx_ok_b : IndexInterface.ok idx_b idx_wf_b}.

  (* WHAT AN ENTRY CLAIMS.  Two things, and the second is the one a rewrite
     needs: the store types the table as the installed record, and the
     program maintains the index's invariant for it.  A rule receives exactly
     this today, as aug_transf_sound's hypothesis, so moving it here changes
     not what any rule assumes but only where it comes from. *)
  Definition idx_fact (tbl : string) (t : type)
    (Gstore Genv : tenv) (c : command) : Prop :=
    map.get Gstore tbl = Some (aux_ty (idx:=idx_b) id_tag aux_tag t)
    /\ parameterized_wf Gstore Genv
         (value_wf_with_globals (aux_wf (idx_wf:=idx_wf_b) id_tag aux_tag) (tbl :: nil))
         (fun _ _ => True) c.

  (* LAW 1, ESTABLISHMENT.  Installing at b establishes b's own entry from
     well-typedness alone: transf_to_idx' writes both fields of the record
     from the same expression, so the invariant is MANUFACTURED, not
     assumed.  This is why the table being installed never needs an entry
     supplied by the caller. *)
  Lemma idx_fact_established :
    forall (b : string) b_ty c free_vars (Gstore Genv : tenv),
      map.get Gstore b = Some b_ty ->
      is_tbl_ty (index:=idx_b) b_ty = true ->
      well_typed Gstore Genv c ->
      incl (get_free_vars Genv) free_vars ->
      tenv_wf Gstore -> tenv_wf Genv ->
      idx_fact b b_ty (map.put Gstore b (aux_ty (idx:=idx_b) id_tag aux_tag b_ty)) Genv
        (transf_to_idx' (idx:=idx_b) id_tag aux_tag b free_vars c).
  Proof.
    intros * H_b H_is H_wt H_incl H_Gs H_Ge; unfold idx_fact; split.
    1: apply map.get_put_same.
    1:{ eapply transf_to_idx'_index_wf;
          [ exact H_tags_diff | exact H_b | exact H_is | exact H_wt
          | exact H_incl | exact H_Gs | exact H_Ge ]. }
  Qed.

  (* LAW 2, STABILITY.  Installing at ANOTHER table leaves the entry
     standing -- the same predicate, not a fused one -- so the fact can be
     stated about the program rather than threaded out of the installation
     that established it.  That is what lets installation and rule
     application be separate phases, and so what lets several tables' gated
     rules run.

     It is an instance of transf_to_idx'_wf_keep: b's invariant says nothing
     about a, which is the side condition that lemma asks for. *)
  Lemma install_preserves_other_idx_wf :
    forall (a b : string) a_ty c free_vars (Gstore Genv : tenv) A A',
      a <> b ->
      map.get Gstore a = Some a_ty ->
      is_tbl_ty (index:=idx_a) a_ty = true ->
      incl (get_free_vars Genv) free_vars ->
      tenv_wf Gstore -> tenv_wf Genv ->
      (forall (store env : locals),
          locals_wf (map.put Gstore a (aux_ty (idx:=idx_a) id_tag aux_tag a_ty)) store ->
          locals_wf Genv env ->
          holds_for_all_entries
            (value_wf_with_globals (aux_wf (idx_wf:=idx_wf_b) id_tag aux_tag) (b :: nil)) store ->
          A' store env -> A (strip_aux id_tag a store) env) ->
      parameterized_wf Gstore Genv
        (value_wf_with_globals (aux_wf (idx_wf:=idx_wf_b) id_tag aux_tag) (b :: nil)) A c ->
      parameterized_wf (map.put Gstore a (aux_ty (idx:=idx_a) id_tag aux_tag a_ty)) Genv
        (value_wf_with_globals (aux_wf (idx_wf:=idx_wf_b) id_tag aux_tag) (b :: nil)) A'
        (transf_to_idx' (idx:=idx_a) id_tag aux_tag a free_vars c).
  Proof.
    intros * H_ne H_a H_is H_incl H_Gs H_Ge H_sim H_wf.
    eapply transf_to_idx'_wf_keep;
      [ exact H_tags_diff
      | intros v; apply value_wf_with_globals_single; left; congruence
      | exact H_a | exact H_is | exact H_incl | exact H_Gs | exact H_Ge
      | exact H_sim | exact H_wf ].
  Qed.

  (* the same, stated on the entry, with the typing carried too *)
  Corollary idx_fact_preserved :
    forall (a b : string) a_ty b_ty c free_vars (Gstore Genv : tenv),
      a <> b ->
      map.get Gstore a = Some a_ty ->
      is_tbl_ty (index:=idx_a) a_ty = true ->
      incl (get_free_vars Genv) free_vars ->
      tenv_wf Gstore -> tenv_wf Genv ->
      idx_fact b b_ty Gstore Genv c ->
      idx_fact b b_ty (map.put Gstore a (aux_ty (idx:=idx_a) id_tag aux_tag a_ty)) Genv
        (transf_to_idx' (idx:=idx_a) id_tag aux_tag a free_vars c).
  Proof.
    intros * H_ne H_a H_is H_incl H_Gs H_Ge [ H_ty H_wf ]; unfold idx_fact; split.
    1: rewrite map.get_put_diff by congruence; exact H_ty.
    1:{ eapply install_preserves_other_idx_wf with (A := fun (_ _ : locals) => True);
          [ exact H_ne | exact H_a | exact H_is | exact H_incl
          | exact H_Gs | exact H_Ge | intros; exact I | exact H_wf ]. }
  Qed.
End IndexFactAcrossTables.
