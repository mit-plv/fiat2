Require Import fiat2.Language fiat2.TypeSystem fiat2.Utils fiat2.Surface
  fiat2.OptimizeAnno fiat2.IndexInterface fiat2.IndexTransf fiat2.Selector.
Require fiat2.Value.
Require fiat2.eval.Annotations.
Require fiat2.eval.Extract.
Require fiat2.eval.Keycloak_CachedRealm fiat2.eval.Kafka_NamedCache
  fiat2.eval.Kafka_Cluster fiat2.eval.Kafka_WindowStore
  fiat2.eval.HA_AreaRegistry fiat2.eval.HA_LookinFunctions
  fiat2.eval.HA_EntityRegistry
  fiat2.eval.Jenkins_UserSearch fiat2.eval.Jenkins_ItemDeletion
  fiat2.eval.Sat4j_LiteralStorage fiat2.eval.Jenkins_DependentPlugins
  fiat2.Ex_RangeDelete fiat2.Ex_MinDelete fiat2.Ex_CompositeKey
  fiat2.Ex_CompositeKeyedDelete fiat2.Ex_CompositeKeyDecl
  fiat2.Ex_KeyedDictTwoDeletes.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.
From Stdlib Require Import List String.
Import ListNotations.
Local Open Scope string.

(* ============================================================
   Supplying the one type the optimizer's output does not carry.

   eval/Annotations.v establishes that the terms `typecheck` cannot
   elaborate are exactly those holding an unannotated empty dictionary,
   and that the obstacle is a MISSING TYPE rather than a missing case:
   analyze_expr pushes an expected type down through EFold into the
   accumulator seed, but the optimizer wraps the index in

       CLetMut (ERecord [("id_tag", ...); ("aux_tag", ...)]) tbl c'

   which `typecheck` must SYNTHESIZE in order to give tbl its new type.
   Synthesis cannot invent a dictionary's key and value types, and
   IndexInterface.to_idx_ty is why: it quantifies ONE to_idx expression
   over every admissible table type, so those annotations have to be None.

   This file computes the missing type and hands it over.  Everything
   that does the actual work below is the development's own: mk_idxs,
   mk_compo_idx and idx_ty are the functions apply_all_transfs itself
   calls, so this is not a model of what the optimizer does to the
   table's type -- it is the same computation.

   WHERE THE CHOICE LIST COMES FROM.  Not from a copy of each subject's
   hand-written list, which would be free to drift.  From the
   deterministic selector, whose pick eval/SelectorTests.v already pins
   against that list subject by subject.  So a configuration that changes
   breaks SelectorTests first, and this file follows it.

   UNVERIFIED, like the rest of eval/.  A wrong type here cannot produce a
   wrong program: it makes analyze_expr fail, and the check below is that
   it does not.
   ============================================================ *)

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
  Instance clocals : map.map string Value.value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* what apply_all_transfs passes *)
  Definition reps : nat := 10000.

  (* The record the optimizer rewrites the table into.  `installed` is read
     off the emitted term rather than assumed, because erase_dead_field may
     have dropped id_tag -- which is the "the list is erased" result several
     subjects pin, and the reason this cannot be a fixed two-field type. *)
  Definition transformed_tbl_ty (ics : list index_choice) (t : type)
    (installed : list string) : type :=
    let '(idxs, _, _) := mk_idxs [] O reps ics in
    let aux := @IndexInterface.idx_ty (mk_compo_idx idxs) t in
    TRecord (Value.record_sort
               (List.filter (fun p => existsb (String.eqb (fst p)) installed)
                  [("id_tag", t); ("aux_tag", aux)])).

  Definition installed_of (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  (* the table's type before the rewrite, synthesized from what the SOURCE
     binds -- so it is not written down here either *)
  Definition orig_tbl_ty (Gstore Genv : ctenv) (src : command) : result type :=
    match src with
    | CLetMut e _ _ =>
        p <- synthesize_expr Gstore Genv e ;;
        Success (fst p)
    | _ => error:("the source program binds no table")
    end.

  (* typecheck, with a type supplied for each leading CLetMut.  Below the
     supplied ones it is the ordinary checker, unchanged. *)
  Fixpoint typecheck_with (tys : list type) (Gstore Genv : ctenv) (c : command)
    : result command :=
    match tys with
    | [] => typecheck Gstore Genv c
    | t :: tys' =>
        match c with
        | CLetMut e x c' =>
            e' <- analyze_expr Gstore Genv t e ;;
            c'' <- typecheck_with tys' (map.put Gstore x t) Genv c' ;;
            Success (CLetMut e' x c'')
        | _ => error:("expected a table binding to supply a type for")
        end
    end.

  Definition elaborate (ce : cenv) (tbl : string) (Gstore Genv : ctenv)
    (src opt : command) : result command :=
    t <- orig_tbl_ty Gstore Genv src ;;
    typecheck_with
      [transformed_tbl_ty (select_choices ce tbl src) t (installed_of opt)]
      Gstore Genv opt.

  (* did it elaborate, and is nothing left for a backend to guess? *)
  Definition elaborated_fully (r : result command) : bool :=
    match r with
    | Success c => Annotations.command_annotated c
    | Failure _ => false
    end.

  (* the declaration environments, as eval/SelectorTests.v writes them *)
  Definition ce_kc : cenv := ("actions", (KC.row_ty, KC.decls)) :: cenv_rm "actions" [].
  Definition ce_nc : cenv := ("cache", (NC.row_ty, NC.decls)) :: cenv_rm "cache" [].
  Definition ce_ar : cenv := ("areas", (AR.row_ty, AR.decls)) :: cenv_rm "areas" [].
  Definition ce_ju : cenv := ("users", (JU.row_ty, JU.decls)) :: cenv_rm "users" [].
  Definition ce_ckd : cenv := ("items", (CKD.row_ty, CKD.decls)) :: cenv_rm "items" [].
  Definition ce_ckdecl : cenv :=
    ("items", (CKDecl.row_ty, CKDecl.decls)) :: cenv_rm "items" [].
  Definition ce_kdtd : cenv :=
    ("items", (KDTD.row_ty, KDTD.decls)) :: cenv_rm "items" [].
  Definition ce_s4j : cenv :=
    ("records", (S4J.row_ty, S4J.decls)) :: cenv_rm "records" [].

  Definition checks : list (string * bool) :=
    [ ("keycloak", elaborated_fully (elaborate ce_kc "actions"
         KC.init_Gstore KC.init_Genv X.keycloak_src X.keycloak_opt))
    ; ("named_cache", elaborated_fully (elaborate ce_nc "cache"
         NC.init_Gstore NC.init_Genv X.named_cache_src X.named_cache_opt))
    ; ("area_registry", elaborated_fully (elaborate ce_ar "areas"
         AR.init_Gstore AR.init_Genv X.area_registry_src X.area_registry_opt))
    ; ("lookin", elaborated_fully (elaborate [] "functions"
         LF.init_Gstore LF.init_Genv X.lookin_src X.lookin_opt))
    ; ("user_search", elaborated_fully (elaborate ce_ju "users"
         JU.init_Gstore JU.init_Genv X.user_search_src X.user_search_opt))
    ; ("cluster", elaborated_fully (elaborate [] "partitions"
         KCl.init_Gstore KCl.init_Genv X.cluster_src X.cluster_opt))
    ; ("entity_registry", elaborated_fully (elaborate [] "entries"
         ER.init_Gstore ER.init_Genv X.entity_registry_src X.entity_registry_opt))
    ; ("window_store", elaborated_fully (elaborate [] "segments"
         KWS.init_Gstore KWS.init_Genv X.window_store_src X.window_store_opt))
    ; ("range_delete", elaborated_fully (elaborate [] "orders"
         ERD.init_Gstore ERD.init_Genv X.range_delete_src X.range_delete_opt))
    ; ("min_delete", elaborated_fully (elaborate [] "orders"
         EMD.init_Gstore EMD.init_Genv X.min_delete_src X.min_delete_opt))
    ; ("composite_key", elaborated_fully (elaborate [] "items"
         ECK.init_Gstore ECK.init_Genv X.composite_key_src X.composite_key_opt))
    ; ("composite_keyed_delete", elaborated_fully (elaborate ce_ckd "items"
         CKD.init_Gstore CKD.init_Genv
         X.composite_keyed_delete_src X.composite_keyed_delete_opt))
    ; ("composite_two_deletes", elaborated_fully (elaborate ce_ckd "items"
         CKD.init_Gstore CKD.init_Genv
         X.composite_two_deletes_src X.composite_two_deletes_opt))
    ; ("composite_key_decl", elaborated_fully (elaborate ce_ckdecl "items"
         CKDecl.init_Gstore CKDecl.init_Genv
         X.composite_key_decl_src X.composite_key_decl_opt))
    ; ("keyed_dict_delete", elaborated_fully (elaborate ce_kdtd "items"
         KDTD.init_Gstore KDTD.init_Genv
         X.keyed_dict_delete_src X.keyed_dict_delete_opt))
    ; ("keyed_two_deletes", elaborated_fully (elaborate ce_kdtd "items"
         KDTD.init_Gstore KDTD.init_Genv
         X.keyed_two_deletes_src X.keyed_two_deletes_opt))
    ; ("named_cache_lru", elaborated_fully (elaborate ce_nc "cache"
         NC.init_Gstore NC.init_Genv X.named_cache_lru_src X.named_cache_lru_opt))
    ; ("named_cache_lru_ordered", elaborated_fully (elaborate ce_nc "cache"
         NC.init_Gstore NC.init_Genv
         X.named_cache_lru_ordered_src X.named_cache_lru_ordered_opt))
    ; ("named_cache_lru_noevict", elaborated_fully (elaborate ce_nc "cache"
         NC.init_Gstore NC.init_Genv
         X.named_cache_lru_noevict_src X.named_cache_lru_noevict_opt))
    (* item_deletion is the one subject whose two extracted columns are not
       source and optimized: Extract.v pairs configuration 0 (the same basic
       rewrites, NO index) against TableRep, so that what is measured is what
       TableRep alone is worth.  The left column is therefore already
       optimizer output, and the selector must be shown the ELABORATED
       program instead -- which is also the one SelectorTests pins
       (select_choices [] "registrations" JID.elaborated = [TableRep LikeSet]).
       The table's type is the same either way; only the demands differ. *)
    ; ("item_deletion", elaborated_fully (elaborate [] "registrations"
         JID.init_Gstore JID.init_Genv JID.elaborated X.item_deletion_opt))
    ; ("sat4j", elaborated_fully (elaborate ce_s4j "records"
         S4J.init_Gstore S4J.init_Genv X.sat4j_src X.sat4j_opt))
    ; ("dependent_plugins", elaborated_fully (elaborate [] "deps"
         JDP.init_Gstore JDP.init_Genv
         X.dependent_plugins_src X.dependent_plugins_opt)) ].

  Definition still_failing : list string :=
    List.map fst (List.filter (fun p => negb (snd p)) checks).

  (* The result.  Against Annotations.the_gap_is_exactly_the_unannotated_
     dictionary, which lists 19 of these as unelaborable by `typecheck`
     alone, every one of them now elaborates FULLY -- nothing is left for a
     backend to guess a type for -- and the only thing supplied was the
     table's transformed type, computed by the optimizer's own functions.

     NOT YET COVERED: the 18 alternative configurations.  Each is defined BY
     its hand-written choice list rather than by the selector's pick, so
     select_choices cannot supply one, and they need their lists passed
     explicitly.  That is what the enumeration step wants anyway, so it is
     left until then rather than half-done here. *)
  Theorem every_optimized_program_elaborates : still_failing = [].
  Proof. vm_compute; reflexivity. Qed.

  Lemma how_many_subjects : List.length checks = 22.
  Proof. reflexivity. Qed.

End WithConcreteMaps.
