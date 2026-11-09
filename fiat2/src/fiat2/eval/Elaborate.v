Require Import fiat2.Language fiat2.TypeSystem fiat2.Utils fiat2.constraint.Decl fiat2.constraint.Surface
  fiat2.pipeline.Pipeline fiat2.IndexInterface fiat2.index.IndexTransf fiat2.pipeline.Selector.
Require fiat2.Value.
Require fiat2.eval.Annotations.
Require fiat2.eval.Extract.
Require fiat2.eval.Keycloak_CachedRealm fiat2.eval.Kafka_NamedCache
  fiat2.eval.Kafka_Cluster fiat2.eval.Kafka_WindowStore
  fiat2.eval.HA_AreaRegistry fiat2.eval.HA_LookinFunctions
  fiat2.eval.HA_EntityRegistry
  fiat2.eval.Jenkins_UserSearch fiat2.eval.Jenkins_ItemDeletion
  fiat2.eval.Wagtail_FuzzySearch
  fiat2.eval.Sat4j_LiteralStorage fiat2.eval.Jenkins_DependentPlugins
  fiat2.examples.Ex_RangeDelete fiat2.examples.Ex_MinDelete fiat2.examples.Ex_CompositeKey
  fiat2.examples.Ex_CompositeKeyedDelete fiat2.examples.Ex_CompositeKeyDecl
  fiat2.examples.Ex_KeyedDictTwoDeletes.
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
Module WFS := Wagtail_FuzzySearch.
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
  Definition ce_wfs : cenv :=
    ("entries", (WFS.row_ty, WFS.decls)) :: cenv_rm "entries" [].
  Definition ce_ckd : cenv := ("items", (CKD.row_ty, CKD.decls)) :: cenv_rm "items" [].
  Definition ce_ckdecl : cenv :=
    ("items", (CKDecl.row_ty, CKDecl.decls)) :: cenv_rm "items" [].
  Definition ce_kdtd : cenv :=
    ("items", (KDTD.row_ty, KDTD.decls)) :: cenv_rm "items" [].
  Definition ce_s4j : cenv :=
    ("records", (S4J.row_ty, S4J.decls)) :: cenv_rm "records" [].

  (* One row per subject, so the checks below and the TERMS the backend
     consumes come from the same place rather than from two lists that
     could disagree.

     s_sel is the program the SELECTOR reads and the table's type is
     synthesized from; s_src is the source column the harness measures.
     They differ for exactly one subject -- see item_deletion below. *)
  Record subj := mk_subj {
      s_name : string;
      s_ce : cenv;
      s_tbl : string;
      s_Gstore : ctenv;
      s_Genv : ctenv;
      s_sel : command;
      s_src : command;
      s_opt : command }.

  Definition subjects : list subj :=
    [ mk_subj "keycloak" ce_kc "actions"
        KC.init_Gstore KC.init_Genv
        X.keycloak_src X.keycloak_src X.keycloak_opt
    ; mk_subj "named_cache" ce_nc "cache"
        NC.init_Gstore NC.init_Genv
        X.named_cache_src X.named_cache_src X.named_cache_opt
    ; mk_subj "area_registry" ce_ar "areas"
        AR.init_Gstore AR.init_Genv
        X.area_registry_src X.area_registry_src X.area_registry_opt
    ; mk_subj "lookin" [] "functions"
        LF.init_Gstore LF.init_Genv
        X.lookin_src X.lookin_src X.lookin_opt
    ; mk_subj "user_search" ce_ju "users"
        JU.init_Gstore JU.init_Genv
        X.user_search_src X.user_search_src X.user_search_opt
    ; mk_subj "cluster" [] "partitions"
        KCl.init_Gstore KCl.init_Genv
        X.cluster_src X.cluster_src X.cluster_opt
    ; mk_subj "entity_registry" [] "entries"
        ER.init_Gstore ER.init_Genv
        X.entity_registry_src X.entity_registry_src X.entity_registry_opt
    ; mk_subj "window_store" [] "segments"
        KWS.init_Gstore KWS.init_Genv
        X.window_store_src X.window_store_src X.window_store_opt
    ; mk_subj "range_delete" [] "orders"
        ERD.init_Gstore ERD.init_Genv
        X.range_delete_src X.range_delete_src X.range_delete_opt
    ; mk_subj "min_delete" [] "orders"
        EMD.init_Gstore EMD.init_Genv
        X.min_delete_src X.min_delete_src X.min_delete_opt
    ; mk_subj "composite_key" [] "items"
        ECK.init_Gstore ECK.init_Genv
        X.composite_key_src X.composite_key_src X.composite_key_opt
    ; mk_subj "composite_keyed_delete" ce_ckd "items"
        CKD.init_Gstore CKD.init_Genv
        X.composite_keyed_delete_src X.composite_keyed_delete_src X.composite_keyed_delete_opt
    ; mk_subj "composite_two_deletes" ce_ckd "items"
        CKD.init_Gstore CKD.init_Genv
        X.composite_two_deletes_src X.composite_two_deletes_src X.composite_two_deletes_opt
    ; mk_subj "composite_key_decl" ce_ckdecl "items"
        CKDecl.init_Gstore CKDecl.init_Genv
        X.composite_key_decl_src X.composite_key_decl_src X.composite_key_decl_opt
    ; mk_subj "keyed_dict_delete" ce_kdtd "items"
        KDTD.init_Gstore KDTD.init_Genv
        X.keyed_dict_delete_src X.keyed_dict_delete_src X.keyed_dict_delete_opt
    ; mk_subj "keyed_two_deletes" ce_kdtd "items"
        KDTD.init_Gstore KDTD.init_Genv
        X.keyed_two_deletes_src X.keyed_two_deletes_src X.keyed_two_deletes_opt
    ; mk_subj "named_cache_lru" ce_nc "cache"
        NC.init_Gstore NC.init_Genv
        X.named_cache_lru_src X.named_cache_lru_src X.named_cache_lru_opt
    ; mk_subj "named_cache_lru_ordered" ce_nc "cache"
        NC.init_Gstore NC.init_Genv
        X.named_cache_lru_ordered_src X.named_cache_lru_ordered_src X.named_cache_lru_ordered_opt
    ; mk_subj "named_cache_lru_noevict" ce_nc "cache"
        NC.init_Gstore NC.init_Genv
        X.named_cache_lru_noevict_src X.named_cache_lru_noevict_src X.named_cache_lru_noevict_opt
    ; mk_subj "item_deletion" [] "registrations"
        JID.init_Gstore JID.init_Genv
        JID.elaborated X.item_deletion_src X.item_deletion_opt
    ; mk_subj "sat4j" ce_s4j "records"
        S4J.init_Gstore S4J.init_Genv
        X.sat4j_src X.sat4j_src X.sat4j_opt
    ; mk_subj "dependent_plugins" [] "deps"
        JDP.init_Gstore JDP.init_Genv
        X.dependent_plugins_src X.dependent_plugins_src X.dependent_plugins_opt
    (* appended, for the reason eval/Extract.v's list gives *)
    ; mk_subj "fuzzy_search" ce_wfs "entries"
        WFS.init_Gstore WFS.init_Genv
        X.fuzzy_search_src X.fuzzy_search_src X.fuzzy_search_opt ].

  Definition elaborate_subj (s : subj) : result command :=
    elaborate (s_ce s) (s_tbl s) (s_Gstore s) (s_Genv s) (s_sel s) (s_opt s).

  Definition checks : list (string * bool) :=
    List.map (fun s => (s_name s, elaborated_fully (elaborate_subj s))) subjects.

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

  Lemma how_many_subjects : List.length checks = 23.
  Proof. reflexivity. Qed.

  (* ------------------------------------------------------------------
     What crosses the boundary: both columns of every subject, FULLY
     TYPE-ANNOTATED.

     The source column needs nothing special -- plain typecheck elaborates
     it, which Annotations.every_source_elaborates establishes -- and the
     optimized column goes through `elaborate` above.  Both are reduced to
     a normal form here, exactly as eval/Extract.v does for the unannotated
     terms, so what the backend receives is DATA and no part of the
     optimizer or the checker is extracted alongside it.

     CSkip as the failure value is not a silent fallback: the two theorems
     above say neither arm is reachable, and a CSkip appearing downstream
     would be a loud failure rather than a quiet wrong answer, since every
     subject's store comparison would disagree. *)
  Definition tc_or_skip (Gstore Genv : ctenv) (c : command) : command :=
    match typecheck Gstore Genv c with
    | Success c' => c'
    | Failure _ => CSkip
    end.

  Definition elab_or_skip (r : result command) : command :=
    match r with
    | Success c => c
    | Failure _ => CSkip
    end.

  Definition annotated : list (string * command * command) :=
    List.map (fun s =>
                (s_name s,
                  tc_or_skip (s_Gstore s) (s_Genv s) (s_src s),
                  elab_or_skip (elaborate_subj s)))
      subjects.

  (* and the check that no arm above was taken, on the very list that gets
     extracted rather than on the definitions it was built from *)
  Definition no_skips : bool :=
    forallb (fun '(_, src, opt) =>
               match src, opt with
               | CSkip, _ | _, CSkip => false
               | _, _ => true
               end) annotated.

  Theorem annotated_terms_are_real : no_skips = true.
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     The two table types, per subject.

     WHY THESE HAVE TO CROSS TOO.  The annotations give the backend every
     collection a program CREATES, which is most of what it needs -- but
     not the table's own record.  `CLetMut (ERecord [("id_tag", ...);
     ("aux_tag", ...)]) tbl c'` is built by ERecord, which carries no
     annotation, so the record pairing the rows with their indexes is
     exactly the type a reader of the annotations alone cannot see.  It is
     also the most important one: it is where the dictionaries live, and a
     backend that cannot name it cannot monomorphize the table at all.

     Nothing new is computed here.  transformed_tbl_ty is what the
     elaboration above already used, so these are the types the terms were
     annotated AGAINST rather than a second opinion about them. *)
  Definition tbl_tys (s : subj) : result (type * type) :=
    t <- orig_tbl_ty (s_Gstore s) (s_Genv s) (s_sel s) ;;
    Success (t,
      transformed_tbl_ty (select_choices (s_ce s) (s_tbl s) (s_sel s)) t
        (installed_of (s_opt s))).

  Definition tbl_types : list (string * type * type) :=
    List.map (fun s =>
                match tbl_tys s with
                | Success (a, b) => (s_name s, a, b)
                | Failure _ => (s_name s, TUnit, TUnit)
                end)
      subjects.

  (* A table is a list of records, so TUnit is a value no real answer takes
     and its absence is the check that no Failure arm was reached. *)
  Definition no_unit_tbl_ty : bool :=
    forallb (fun '(_, a, b) =>
               match a, b with
               | TUnit, _ | _, TUnit => false
               | _, _ => true
               end) tbl_types.

  Theorem tbl_types_are_real : no_unit_tbl_ty = true.
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     The store and environment types, per subject.

     The generated code needs these for its INPUTS.  A workload arrives as
     the generators built it -- `queries`, and for most subjects a table
     read out of the environment -- and the compiled program has to know
     what each name holds in order to give it a monomorphic type.  Handed
     over as association lists rather than as the map, so the boundary
     carries no coqutil representation into OCaml, exactly as ref_run
     does. *)
  Definition envs : list (string * list (string * type) * list (string * type)) :=
    List.map (fun s =>
                (s_name s, map.tuples (s_Gstore s), map.tuples (s_Genv s)))
      subjects.

End WithConcreteMaps.
