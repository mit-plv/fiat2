Require Import fiat2.Language fiat2.TypeSystem.
Require fiat2.eval.Extract.
Require fiat2.eval.Keycloak_CachedRealm fiat2.eval.Kafka_NamedCache
  fiat2.eval.Kafka_Cluster fiat2.eval.Kafka_WindowStore
  fiat2.eval.HA_AreaRegistry fiat2.eval.HA_LookinFunctions
  fiat2.eval.HA_EntityRegistry
  fiat2.eval.Jenkins_UserSearch fiat2.eval.Jenkins_ItemDeletion
  fiat2.eval.Sat4j_LiteralStorage fiat2.eval.Jenkins_DependentPlugins
  fiat2.examples.Ex_RangeDelete fiat2.examples.Ex_MinDelete fiat2.examples.Ex_CompositeKey
  fiat2.examples.Ex_CompositeKeyedDelete fiat2.examples.Ex_CompositeKeyDecl
  fiat2.examples.Ex_KeyedDictTwoDeletes.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
Require Import coqutil.Datatypes.Result.
From Stdlib Require Import List String.
Import ListNotations.
Local Open Scope string.

(* ============================================================
   The backend's precondition: every term that crosses the boundary
   can be made FULLY TYPE-ANNOTATED by the existing typechecker.

   WHY THIS FILE EXISTS.  A monomorphizing backend has to know, at every
   node, what type it is compiling: a row becomes an OCaml record with
   constant-offset field access, a TInt becomes an unboxed int, a
   TDict Unranged becomes a hash table over a monomorphic key.  The
   extracted terms do NOT carry that information.  They cannot: every
   index's to_idx builds its accumulator with `AEmptyDict Unranged None`
   and `ANil None`, so the optimizer's own output has holes wherever a
   collection is created.

   What fills them is already here.  TypeSystem.typecheck returns a
   `result command`, and the command it returns is the ELABORATED one --
   synthesize_expr's second component is the term with its annotations
   filled in.  So the backend needs no type inference of its own, and in
   particular no SECOND typechecker in OCaml that could drift from this
   one.  It needs this function to succeed and to leave nothing behind.

   This file checks exactly that, by computation, on every term the
   harness measures.  A `false` here is a term the backend would have to
   guess a type for, which is the one thing it must never do.

   WHAT THIS DOES NOT CLAIM.  typecheck is unverified, and the two
   theorems that are about it -- TypeSound.atom_typechecker_sound and
   TypeSound.command_typechecker_sound -- both conclude about the
   checker's INPUT (`well_typed Gstore Genv c`), not about the elaborated
   term it returns.  So nothing here says the annotations are CORRECT;
   it says they are PRESENT, which is a different and weaker thing.  What
   makes that acceptable is that annotations are semantically inert --
   interp_atom (Interpret.v) matches `AEmptyDict _ _`, `ANil _` and the
   rest without reading the annotation at all -- so an elaboration that
   got one wrong could mislead the BACKEND but could not change what the
   program means, and the differential test against the Gallina oracle
   runs on the same terms.  A theorem that the elaborated term is
   well_typed would replace that argument with a proof; it is not written.

   WHY IT READS THE TERMS FROM eval/Extract.v rather than from the
   subject files.  Extract.v is where the choice of WHICH configuration
   each subject contributes is made, with reasons attached -- which
   `nth` of a prog_transformed, which of the two columns item_deletion
   pairs.  Checking the subject files' definitions instead would be
   checking a copy of that choice, and the copy could drift.  The terms
   below are the same constants that get extracted.

   WHAT IT FOUND, which is the reason the file is shaped around a
   DIFFERENCE rather than a single `= true`.

   Every SOURCE column elaborates.  No OPTIMIZED column that builds a
   dictionary does, and the two theorems at the bottom say that those are
   the same set: the terms the checker cannot elaborate are exactly the
   terms holding an unannotated empty DICTIONARY.

   The cause is not that the checker is missing a case.  analyze_atom has
   one for every unannotated empty collection, the dictionary's included,
   and analyze_expr pushes an expected type down through EFold into its
   accumulator seed -- so a to_idx-shaped fold IS analyzable.  What is
   missing is a type to push.  The optimizer emits

       CLetMut (ERecord [("id_tag", ...); ("aux_tag", ...)]) tbl c'

   and `typecheck` must SYNTHESIZE that record to learn tbl's new type;
   ERecord synthesizes its fields; and synthesize_atom cannot invent a
   dictionary's key and value types, because at that point nothing in the
   term determines them.  The four sibling collections escape this only
   because nothing in these programs puts one in a synthesizing position.

   So the missing input is the TYPE OF THE TRANSFORMED TABLE, which is
   computable and which the optimizer itself builds and discards:
   IndexTransf.aux_ty is
   `TRecord (record_sort [(id_tag, t); (aux_tag, idx_ty t)])`, and
   Pipeline.apply_all_transfs has the composed index
   (`mk_compo_idx idxs`) in hand when it rewrites the table.  Supply that
   type at the CLetMut and the existing analyze path does the rest; no
   second typechecker is needed, and none should be written.
   ============================================================ *)

(* ---------- what "fully annotated" means ---------- *)

(* The AST has exactly five annotation holes, all of them in `atom`
   (Language.v:76-84); expr and command carry no `option type` at all.
   So this is the whole obligation, not a sample of it. *)
Definition atom_annotated (a : atom) : bool :=
  match a with
  | ANil t | ANone t | AEmptyBag t | AEmptySet t =>
      match t with Some _ => true | None => false end
  | AEmptyDict _ t =>
      match t with Some _ => true | None => false end
  | AInt _ | ABool _ | AString _ | AUnit => true
  end.

(* The traversal is parameterised by the atom predicate, so that
   "fully annotated" and "holds an unannotated dictionary" are the same
   walk asked two questions, and cannot disagree about which nodes they
   looked at. *)
Fixpoint expr_all (p : atom -> bool) (e : expr) : bool :=
  match e with
  | EVar _ | ELoc _ => true
  | EAtom a => p a
  | EUnop _ e | EACFold _ e | EACIFold _ e | EAccess e _ | ESort _ e =>
      expr_all p e
  | EBinop _ e1 e2 | ELet e1 _ e2 | EFlatmap _ e1 _ e2 =>
      expr_all p e1 && expr_all p e2
  | ETernop _ e1 e2 e3 | EIf e1 e2 e3 | EFold e1 e2 _ _ e3 =>
      expr_all p e1 && expr_all p e2 && expr_all p e3
  | ERecord l => forallb (fun '(_, e) => expr_all p e) l
  | EOptMatch e1 e2 _ e3 =>
      expr_all p e1 && expr_all p e2 && expr_all p e3
  end.

Fixpoint command_all (p : atom -> bool) (c : command) : bool :=
  match c with
  | CSkip => true
  | CSeq c1 c2 => command_all p c1 && command_all p c2
  | CLet e _ c | CLetMut e _ c | CForeach e _ c =>
      expr_all p e && command_all p c
  | CAssign _ e => expr_all p e
  | CIf e c1 c2 =>
      expr_all p e && command_all p c1 && command_all p c2
  end.

Definition command_annotated (c : command) : bool :=
  command_all atom_annotated c.

(* the one hole with no analyzing position to be filled from *)
Definition dict_annotated (a : atom) : bool :=
  match a with AEmptyDict _ None => false | _ => true end.

Definition holds_unannotated_dict (c : command) : bool :=
  negb (command_all dict_annotated c).

Module KC := Keycloak_CachedRealm.
Module NC := Kafka_NamedCache.
Module AR := HA_AreaRegistry.
Module ER := HA_EntityRegistry.
Module LF := HA_LookinFunctions.
Module JU := Jenkins_UserSearch.
Module KCl := Kafka_Cluster.
Module KWS := Kafka_WindowStore.
Module JID := Jenkins_ItemDeletion.
Module ERD := Ex_RangeDelete.
Module EMD := Ex_MinDelete.
Module ECK := Ex_CompositeKey.
Module CKD := Ex_CompositeKeyedDelete.
Module CKDecl := Ex_CompositeKeyDecl.
Module KDTD := Ex_KeyedDictTwoDeletes.
Module S4J := Sat4j_LiteralStorage.
Module JDP := Jenkins_DependentPlugins.
Module X := Extract.

Section WithConcreteMaps.
  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  (* One list of terms, each with the envs it typechecks in. *)
  Definition entry (Gstore Genv : ctenv) (c : command)
    : ctenv * ctenv * command := (Gstore, Genv, c).

  (* typecheck, then ask whether anything was left for the backend to
     guess.  A Failure is a `false`: the backend has no term at all. *)
  Definition annotates (e : ctenv * ctenv * command) : bool :=
    let '(Gstore, Genv, c) := e in
    match typecheck Gstore Genv c with
    | Success c' => command_annotated c'
    | Failure _ => false
    end.

  Definition dictful (e : ctenv * ctenv * command) : bool :=
    let '(_, _, c) := e in holds_unannotated_dict c.


  (* Each subject's two columns, under that subject's own type
     environments -- the optimizer's output typechecks in the SAME envs
     as its input, because the record-valued table is introduced by a
     CLetMut inside the command and the outer binding is restored on the
     way out. *)
  (* The scan form each subject starts from.  These are the programs the
     subject files' own `checks` lemmas already run typecheck on, so that
     they elaborate is expected; it is here to make the CONTRAST below a
     measurement rather than an assertion. *)
  Definition source_terms : list (string * (ctenv * ctenv * command)) :=
    [ ("keycloak/src", entry KC.init_Gstore KC.init_Genv X.keycloak_src)
    ; ("named_cache/src", entry NC.init_Gstore NC.init_Genv X.named_cache_src)
    ; ("area_registry/src", entry AR.init_Gstore AR.init_Genv X.area_registry_src)
    ; ("lookin/src", entry LF.init_Gstore LF.init_Genv X.lookin_src)
    ; ("user_search/src", entry JU.init_Gstore JU.init_Genv X.user_search_src)
    ; ("cluster/src", entry KCl.init_Gstore KCl.init_Genv X.cluster_src)
    ; ("entity_registry/src", entry ER.init_Gstore ER.init_Genv X.entity_registry_src)
    ; ("window_store/src", entry KWS.init_Gstore KWS.init_Genv X.window_store_src)
    ; ("range_delete/src", entry ERD.init_Gstore ERD.init_Genv X.range_delete_src)
    ; ("min_delete/src", entry EMD.init_Gstore EMD.init_Genv X.min_delete_src)
    ; ("composite_key/src", entry ECK.init_Gstore ECK.init_Genv X.composite_key_src)
    ; ("composite_keyed_delete/src",
        entry CKD.init_Gstore CKD.init_Genv X.composite_keyed_delete_src)
    ; ("composite_two_deletes/src",
        entry CKD.init_Gstore CKD.init_Genv X.composite_two_deletes_src)
    ; ("composite_key_decl/src",
        entry CKDecl.init_Gstore CKDecl.init_Genv X.composite_key_decl_src)
    ; ("keyed_dict_delete/src",
        entry KDTD.init_Gstore KDTD.init_Genv X.keyed_dict_delete_src)
    ; ("keyed_two_deletes/src",
        entry KDTD.init_Gstore KDTD.init_Genv X.keyed_two_deletes_src)
    ; ("named_cache_lru/src",
        entry NC.init_Gstore NC.init_Genv X.named_cache_lru_src)
    ; ("named_cache_lru_ordered/src",
        entry NC.init_Gstore NC.init_Genv X.named_cache_lru_ordered_src)
    ; ("named_cache_lru_noevict/src",
        entry NC.init_Gstore NC.init_Genv X.named_cache_lru_noevict_src)
    ; ("item_deletion/src", entry JID.init_Gstore JID.init_Genv X.item_deletion_src)
    ; ("sat4j/src", entry S4J.init_Gstore S4J.init_Genv X.sat4j_src)
    ; ("dependent_plugins/src",
        entry JDP.init_Gstore JDP.init_Genv X.dependent_plugins_src) ].

  (* and what the optimizer makes of them, under the configuration the
     deterministic selector picks.  The optimizer's output typechecks in
     the SAME envs as its input: the record-valued table is introduced by
     a CLetMut inside the command, and the outer binding is restored on
     the way out. *)
  Definition optimized_terms : list (string * (ctenv * ctenv * command)) :=
    [ ("keycloak/opt", entry KC.init_Gstore KC.init_Genv X.keycloak_opt)
    ; ("named_cache/opt", entry NC.init_Gstore NC.init_Genv X.named_cache_opt)
    ; ("area_registry/opt", entry AR.init_Gstore AR.init_Genv X.area_registry_opt)
    ; ("lookin/opt", entry LF.init_Gstore LF.init_Genv X.lookin_opt)
    ; ("user_search/opt", entry JU.init_Gstore JU.init_Genv X.user_search_opt)
    ; ("cluster/opt", entry KCl.init_Gstore KCl.init_Genv X.cluster_opt)
    ; ("entity_registry/opt", entry ER.init_Gstore ER.init_Genv X.entity_registry_opt)
    ; ("window_store/opt", entry KWS.init_Gstore KWS.init_Genv X.window_store_opt)
    ; ("range_delete/opt", entry ERD.init_Gstore ERD.init_Genv X.range_delete_opt)
    ; ("min_delete/opt", entry EMD.init_Gstore EMD.init_Genv X.min_delete_opt)
    ; ("composite_key/opt", entry ECK.init_Gstore ECK.init_Genv X.composite_key_opt)
    ; ("composite_keyed_delete/opt",
        entry CKD.init_Gstore CKD.init_Genv X.composite_keyed_delete_opt)
    ; ("composite_two_deletes/opt",
        entry CKD.init_Gstore CKD.init_Genv X.composite_two_deletes_opt)
    ; ("composite_key_decl/opt",
        entry CKDecl.init_Gstore CKDecl.init_Genv X.composite_key_decl_opt)
    ; ("keyed_dict_delete/opt",
        entry KDTD.init_Gstore KDTD.init_Genv X.keyed_dict_delete_opt)
    ; ("keyed_two_deletes/opt",
        entry KDTD.init_Gstore KDTD.init_Genv X.keyed_two_deletes_opt)
    ; ("named_cache_lru/opt",
        entry NC.init_Gstore NC.init_Genv X.named_cache_lru_opt)
    ; ("named_cache_lru_ordered/opt",
        entry NC.init_Gstore NC.init_Genv X.named_cache_lru_ordered_opt)
    ; ("named_cache_lru_noevict/opt",
        entry NC.init_Gstore NC.init_Genv X.named_cache_lru_noevict_opt)
    ; ("item_deletion/opt", entry JID.init_Gstore JID.init_Genv X.item_deletion_opt)
    ; ("sat4j/opt", entry S4J.init_Gstore S4J.init_Genv X.sat4j_opt)
    ; ("dependent_plugins/opt",
        entry JDP.init_Gstore JDP.init_Genv X.dependent_plugins_opt) ].

  Definition subject_terms : list (string * (ctenv * ctenv * command)) :=
    source_terms ++ optimized_terms.

  (* The alternative configurations too.  They are not measured in either
     of the two headline tables, but every one of them is a program this
     pipeline emits, and the enumeration the selector is to be judged
     against runs them -- so the backend has to accept them as well. *)
  Definition alternative_terms : list (string * (ctenv * ctenv * command)) :=
    [ ("keycloak/uncounted",
        entry KC.init_Gstore KC.init_Genv X.keycloak_opt_uncounted)
    ; ("named_cache/swapped",
        entry NC.init_Gstore NC.init_Genv X.named_cache_opt_swapped)
    ; ("user_search/table-rep",
        entry JU.init_Gstore JU.init_Genv X.user_search_opt_rep)
    ; ("cluster/unsplit",
        entry KCl.init_Gstore KCl.init_Genv X.cluster_opt_unsplit)
    ; ("cluster/composite",
        entry KCl.init_Gstore KCl.init_Genv X.cluster_opt_composite)
    ; ("cluster/composite-split",
        entry KCl.init_Gstore KCl.init_Genv X.cluster_opt_composite_split)
    ; ("entity_registry/split-dicts",
        entry ER.init_Gstore ER.init_Genv X.entity_registry_opt_split_dicts)
    ; ("entity_registry/unsplit",
        entry ER.init_Gstore ER.init_Genv X.entity_registry_opt_unsplit)
    ; ("entity_registry/composite",
        entry ER.init_Gstore ER.init_Genv X.entity_registry_opt_composite)
    ; ("entity_registry/composite-split",
        entry ER.init_Gstore ER.init_Genv X.entity_registry_opt_composite_split)
    ; ("window_store/unsplit",
        entry KWS.init_Gstore KWS.init_Genv X.window_store_opt_unsplit)
    ; ("sat4j/unsplit",
        entry S4J.init_Gstore S4J.init_Genv X.sat4j_opt_unsplit)
    ; ("dependent_plugins/unpromoted",
        entry JDP.init_Gstore JDP.init_Genv X.dependent_plugins_unpromoted)
    ; ("dependent_plugins/transposed",
        entry JDP.init_Gstore JDP.init_Genv X.dependent_plugins_transposed)
    ; ("min_delete/noset",
        entry EMD.init_Gstore EMD.init_Genv X.min_delete_opt_noset)
    ; ("min_delete/rangeddict",
        entry EMD.init_Gstore EMD.init_Genv X.min_delete_opt_ranged)
    ; ("min_delete/dictmin",
        entry EMD.init_Gstore EMD.init_Genv X.min_delete_probe_dictmin)
    ; ("min_delete/dictmin-erased",
        entry EMD.init_Gstore EMD.init_Genv X.min_delete_probe_dictmin_erased) ].

  Definition all_terms : list (string * (ctenv * ctenv * command)) :=
    subject_terms ++ alternative_terms.

  Definition names_where (f : ctenv * ctenv * command -> bool)
    (l : list (string * (ctenv * ctenv * command))) : list string :=
    List.map fst (List.filter (fun p => f (snd p)) l).

  (* A name on either list identifies itself, so a mismatch reports which
     term moved rather than just that the count changed. *)
  Definition not_elaborated : list string :=
    names_where (fun e => negb (annotates e)) all_terms.
  Definition dict_bearing : list string := names_where dictful all_terms.

  (* ------------------------------------------------------------------
     The two facts.
     ------------------------------------------------------------------ *)

  (* Nothing in the language or in the subjects is the obstacle: every
     scan form elaborates, and none of them even reaches the hole. *)
  Theorem every_source_elaborates :
    names_where (fun e => negb (annotates e)) source_terms = [].
  Proof. vm_compute; reflexivity. Qed.

  Theorem no_source_holds_an_unannotated_dict :
    names_where dictful source_terms = [].
  Proof. vm_compute; reflexivity. Qed.

  (* The gap is exactly the unannotated dictionary -- not a scatter of
     unrelated failures.  This is the statement a fix has to move: supply
     the transformed table's type at the CLetMut and both lists go empty
     together. *)
  Theorem the_gap_is_exactly_the_unannotated_dictionary :
    not_elaborated = dict_bearing.
  Proof. vm_compute; reflexivity. Qed.

  Lemma how_many_do_not_elaborate : List.length not_elaborated = 36.
  Proof. vm_compute; reflexivity. Qed.

  Lemma how_many_terms : List.length all_terms = 62.
  Proof. reflexivity. Qed.

End WithConcreteMaps.
