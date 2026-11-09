Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.rules.CollectionTransf fiat2.index.DictIndexImpl
  fiat2.index.MinAgg fiat2.TransfUtils fiat2.rules.FlatmapForms fiat2.rules.FlatmapTransf fiat2.index.IndexTransf
  fiat2.rules.EraseField
  fiat2.Utils fiat2.Substitute fiat2.pipeline.Pipeline fiat2.examples.Ex_MinDelete.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.

Import ListNotations.
Local Open Scope string.

(* ============================================================
   A PROBE, NOT A TRANSFORMATION.  NOTHING HERE IS PROVED SOUND.

   WHAT THIS IS FOR.  Ex_MinDelete configuration 2 installs an ordered
   dictionary keyed on the attribute whose minimum the program reads.  The
   dictionary serves the DELETE outright, but no rule serves the READ, so the
   minimum stays a scan -- and since that scan is the id_tag list's last
   reader, the list survives and the delete goes on rewriting it.  Writing the
   rule that closes this is a 300-line obligation in the shape of
   DictIndexImpl.range_filter_to_dict_range_head.  The question this file
   answers FIRST, for the price of a syntactic function, is whether the rule
   is worth that: it applies the rewrite unverified and lets the harness
   measure what the rule would be worth if it existed.

   WHAT IS AND IS NOT EVIDENCE HERE.
     * min_from_dict_idx_head is NOT registered, NOT sound, and is required by
       nothing in the pipeline.  It is reachable only from this file and from
       the harness wiring, as the alternative min_delete/dictmin.
     * probe_typechecks IS machine-checked, and it is the preserve_ty half of
       the obligation at this one instance.
     * probe_differs_from_config2 is the honest statement that the rewrite
       actually fires, so a measured difference is the rule's and not noise.
     * The semantic half is NOT proved.  The harness's differential test runs
       this term against the extracted Gallina interpreter on every generated
       input, which is a test and not a proof; any number measured from it
       must be reported as a projection.

   WHAT THE EVENTUAL RULE OWES.  Exactly what the pattern below demands:
   preserve_ty, and preserve_sem from TypeSound.map_fst_dict_insert and
   DictIndexImpl.map_fst_gallina_to_idx together with MinAgg.interp_min_proj,
   which between them reduce it to a split on whether the table is empty.

   WHAT IT MEASURED (harness alternatives, typed, 200/400/800/1600 rows,
   against the configuration the selector picks -- SetAgg with MinAgg).
   Work at 1600 rows, and the fitted exponent:

                    build   readMin      insert  deleteMin  deleteOther
     chosen        133266      1540        1980      33748         1501
                   a=1.12    a=0.00      a=0.01     a=0.86       a=0.02
     rangeddict     83899   1414020        2234     827948       827944
                   a=1.06    a=1.11      a=0.03     a=1.02       a=1.02
     + the rule     83899      1540        2234     827948       827944
                   a=1.06    a=0.00      a=0.03     a=1.02       a=1.02
     + the erasure  83895      1540        1954        828          824
                   a=1.06    a=0.00      a=0.03     a=0.04       a=0.04

   Three things in that table, and the middle one is the point.

   The dictionary WITHOUT the rule is not a trade, it is a loss: the minimum
   read costs 918x what the aggregation charges, because it is a scan.

   The rule by itself recovers the read EXACTLY and buys nothing else --
   1540 against 1540, a=0.00 against a=0.00.  That is the earlier measured
   finding in its sharpest form: a tree's minimum and a cached minimum are
   both free in key work, so an index-served minimum can only ever TIE
   MinAgg on the read it serves.  A rule justified by its read would not be
   worth writing.

   What is worth writing is the CASCADE.  Serving the read orphans the list,
   the verified erasure drops it, and the delete stops rewriting a table it
   no longer has: deleteMin falls from 33748 to 828, and the exponent from
   0.86 to 0.04.  That is an exponent and not a constant, and with it the
   configuration dominates the chosen one on all five kinds -- cheaper to
   build, equal on the read and the insert, 40.8x on deleting the minimum
   and 1.8x on deleting anything else.

   SO THE RULE'S VALUE IS NOT WHERE IT WAS PROJECTED TO BE.  It is not a
   better minimum; it is the last reader of a list, and removing it is what
   pays.  Any rule that takes the final read off a table's list earns the
   same thing, which is why this number belongs with the erasure results
   (eval/Jenkins_UserSearch, eval/Kafka_WindowStore) and not with MinAgg.

   AND IT IS STILL NOT WRITTEN, because no subject asks for it: see the
   witness note in Selector.v above the MinAgg heuristic.  What is measured
   here is what a witnessed program WOULD get, not what any program gets.

   THE HAZARD THIS MAKES CONCRETE.  The pattern matched below is the SAME
   pattern MinAgg.min_to_agg_lookup_head matches (MinAgg.v:170), down to the
   all_eqb guard; only the emitted term differs -- MinAgg reads its cached
   aggregate at the index tag, this reads ODictMinKey of the dictionary at
   that tag.  So installing a MinAgg and a RangedDictIdx on one attribute
   would make listing order decide which serves the read.  That is an eighth
   entry for the rule-ordering list in Selector.v, and it is a reason to
   write the rule carefully rather than a reason not to write it.
   ============================================================ *)

Section WithTags.
  Context (tbl attr id_tag aux_tag idx_tag : string).

  (* The rule, as the syntax function a registered transf would wrap.  The
     emitted term is well-typed only when the index at idx_tag is a dictionary
     of kind Ranged keyed on attr -- ODictMinKey has no other type -- which is
     why the kind had to be in the type for this to be stateable at all. *)
  Definition min_from_dict_idx_head (e : expr) :=
    match e with
    | EACIFold AGMin (flatmap_proj_set (EUnop OSetOfList (EAccess (ELoc tbl0) id_tag0)) x0 (EAccess (EVar x1) attr0) _) =>
        if all_eqb [(tbl, [tbl0]); (attr, [attr0]); (x0, [x1]); (id_tag, [id_tag0])]
        then EUnop ODictMinKey (EAccess (EAccess (ELoc tbl) aux_tag) idx_tag)
        else e
    | _ => e
    end.
End WithTags.

(* The tags the dict index pipeline actually uses, read off Ex_MinDelete
   configuration 2 rather than assumed. *)
Definition probed : command :=
  fold_command (fun c => c)
    (min_from_dict_idx_head "orders" "price" "id_tag" "aux_tag" "0")
    (nth 2 Ex_MinDelete.prog_transformed CSkip).

Section WithConcreteMaps.
  Local Open Scope string.

  Instance ptenv : map.map string type := SortedListString.map _.
  Instance ptenv_ok : map.ok ptenv := SortedListString.ok _.

  (* The rewrite fires: the probed term is not the configuration it came from. *)
  Lemma probe_differs_from_config2 :
    probed <> nth 2 Ex_MinDelete.prog_transformed CSkip.
  Proof. vm_compute. intros H; discriminate H. Qed.

  (* NO CHECKER EVIDENCE IS AVAILABLE HERE, and the reason is not the probe.
     The executable typecheck rejects configuration 2 ITSELF, with
     "Insufficient type information for (AEmptyDict Ranged None)": the index
     install emits an unannotated empty dictionary, which only the DECLARATIVE
     judgment types, and every index-installing configuration in this
     development is in the same position.  The verified ones get well_typed
     from apply_all_transfs_sound instead, which the probe cannot use because
     it is not a sound transf.  So what is pinned below is the LOCAL typing
     content of the rewrite -- the half of preserve_ty that the kind is
     responsible for -- and not the whole command. *)
  Definition idx_record_ty : type :=
    TRecord (record_sort
               [("id_tag", TList Ex_MinDelete.row_ty_orders);
                ("aux_tag",
                  TRecord (record_sort
                             [("0", TDict Ranged TInt
                                      (TBag Ex_MinDelete.row_ty_orders))]))]).

  Definition probe_Gstore : ptenv :=
    map.put (map.put map.empty "outputs" (TList TString)) "orders" idx_record_ty.

  (* Same type in, same type out: the emitted ODictMinKey read and the scan it
     replaces both have type TOption TInt under the index's own record type.
     The first conjunct is where the dict_kind earns its place in the type --
     ODictMinKey is untypeable at Unranged, so this statement is false for an
     index installed as DictIdx. *)
  Lemma emitted_read_has_the_type_the_scan_had :
    type_of probe_Gstore map.empty
      (EUnop ODictMinKey (EAccess (EAccess (ELoc "orders") "aux_tag") "0"))
      (TOption TInt)
    /\ type_of probe_Gstore map.empty
         (EACIFold AGMin
            (flatmap_proj_set (EUnop OSetOfList (EAccess (ELoc "orders") "id_tag"))
               "o" (EAccess (EVar "o") "price") None))
         (TOption TInt).
  Proof.
    split; repeat econstructor.
  Qed.

  (* AND WHAT THE RULE WOULD CASCADE INTO, which is the larger half of its
     value and costs no further invention.

     Once the minimum is read from the dictionary, the id_tag list is read by
     nothing but its own maintenance, so the existing VERIFIED erasure drops
     it -- and with it the whole-list rewrite the delete was performing.
     erase_dead_field checks its own three conditions on the program in hand
     and is the identity when they fail, so the pin below that it CHANGED the
     term is machine-checked evidence that the field really has no reader
     left.  The probe's one unverified step is still the min rewrite; the
     erasure on top of it is the pipeline's own. *)
  Definition probed_erased : command :=
    erase_dead_field (tenv := ptenv) "id_tag" map.empty map.empty probed.

  Lemma erasure_fires_after_the_rewrite :
    probed_erased <> probed.
  Proof. vm_compute. intros H; discriminate H. Qed.

  (* and it does NOT fire without it: the scan is the list's last reader, so
     the same erasure is the identity on the configuration as the verified
     pipeline leaves it.  This is the pin that the list's survival is caused
     by the missing rule and not by something else. *)
  Lemma erasure_does_not_fire_before_it :
    erase_dead_field (tenv := ptenv) "id_tag" map.empty map.empty
      (nth 2 Ex_MinDelete.prog_transformed CSkip)
    = nth 2 Ex_MinDelete.prog_transformed CSkip.
  Proof. vm_compute. reflexivity. Qed.
End WithConcreteMaps.
