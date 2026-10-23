Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.FlatmapForms fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   Source
     home-assistant/core, commit e751cd2b
     homeassistant/helpers/area_registry.py:169 (class AreaRegistryItems)
     the base dict and its write hooks at homeassistant/helpers/registry.py:38
       (__setitem__) and :61 (__delitem__)

       def _index_entry(self, key, entry):
           super()._index_entry(key, entry)
           if entry.floor_id is not None:
               self._floors_index[entry.floor_id][key] = True
           ...
       def _unindex_entry(self, key, replacement_entry=None):
           super()._unindex_entry(key, replacement_entry)
           entry = self.data[key]
           ...
           if floor_id := entry.floor_id:
               self._unindex_entry_value(key, floor_id, self._floors_index)

       def get_areas_for_floor(self, floor):
           data = self.data
           return [data[key] for key in self._floors_index.get(floor, ())]

     A dict of areas by id, plus three secondary indexes, maintained by hand
     on every insert and every delete.  This is the only exemplar found whose
     writes are its own, which is why it is here: Keycloak_CachedRealm and
     Kafka_Cluster both build once and never mutate.

   Pattern
     A1a maintained, A2.  Of the three secondary indexes only _floors_index
     is modelled: _labels_index and _aliases_index key on each element of a
     per-row collection, which is the one gap identified in the 2026-10-19
     survey and is not built.

   Claim
     C3.  A representation chosen AND maintained across destructive updates,
     from a program that performs only the two writes the source performs.

   Faithfulness -- what this translation drops, and why
     * AreaEntry carries aliases, labels, icon, picture, created_at,
       modified_at, humidity_entity_id and temperature_entity_id.  Only id,
       name and floor_id are kept; of the dropped fields only aliases and
       labels are keys, and those are the two indexes left out.
     * floor_id is `str | None`.  As in Kafka_Cluster it is TOption here, and
       the index is keyed by the option: HA's `if entry.floor_id is not None`
       makes _floors_index partial, whereas this index is total and the rows
       HA skips sit in a None bucket that no query probes.
     * __setitem__ unindexes before reindexing when the key already exists.
       Only the two paths that reach a single hook are modelled -- a fresh
       insert and a delete -- because an update is their composition.
     * get_areas_for_floor resolves postings through the primary dict; this
       index stores the rows themselves.  Both answer the same query from the
       same derived structure; HA pays a second lookup per row, we pay the
       storage.  That choice is the backend's, not the rewrite's.
     * The read returns the areas and here it is counted, as in the other
       two files, because the output channel is a list of strings.
     * Nothing is added.

     * The insert prepends the row.  The source stores into a dict keyed by
       id, so it names no position, and nothing here observes row order --
       see the note on row order in this directory's README.
   Expected
     Both members installed; both reads probe; both writes maintain both
     members incrementally.  THE DELETE IS THE POINT: the primary member
     loses one key in O(1), and so does the secondary one -- the floor
     index is no longer rebuilt.  It is maintained the way HA maintains it:
     probe the primary member for the row the key names, then take that row
     out of the one bucket its floor names.  See delete_is_incremental.

     And because nothing reads the list any more, the list is gone: the
     table IS its two indexes.  See delete_drops_the_list.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort
             [("id", TString); ("name", TString); ("floor", TOption TString)]).

Definition query_ty :=
  TRecord (record_sort
             [("kind", TInt); ("k", TString); ("fl", TString); ("new_area", row_ty)]).

Section WithConcreteMaps.
  Notation value := (value).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Definition count_where (pred : expr) : expr :=
    EUnop OLength
      (EFlatmap LikeList (ELoc "areas") "a"
         (EIf pred (EBinop OCons (EVar "a") (EAtom (ANil None))) (EAtom (ANil None)))).

  Definition q_by_id : expr :=
    count_where (EBinop OEq (EAccess (EVar "a") "id") (EAccess (EVar "q") "k")).

  Definition q_by_floor : expr :=
    count_where (EBinop OEq (EAccess (EVar "a") "floor")
                   (EUnop OSome (EAccess (EVar "q") "fl"))).

  Definition without_key : expr :=
    EFlatmap LikeList (ELoc "areas") "a"
      (EIf (EUnop ONot (EBinop OEq (EAccess (EVar "a") "id") (EAccess (EVar "q") "k")))
         (EBinop OCons (EVar "a") (EAtom (ANil None))) (EAtom (ANil None))).

  Definition report (e : expr) : scommand :=
    SLet e "n"
      (SAssign "outputs"
         (EBinop OCons (EUnop OIntToString (EVar "n")) (ELoc "outputs")) SSkip).

  Definition dispatch (k : Z) (thn els : scommand) : scommand :=
    SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt k))) thn els.

  Definition prog_s (ds : list decl) : scommand :=
    SLetConstrained "areas" row_ty ds
      (SForeach (EVar "queries") "q"
         (dispatch 0
            (SAssign "areas"
               (EBinop OCons (EAccess (EVar "q") "new_area") (ELoc "areas")) SSkip)
            (dispatch 1
               (SAssign "areas" without_key SSkip)
               (dispatch 2 (report q_by_id) (report q_by_floor))))).

  Definition init_Gstore : ctenv := map.put map.empty "outputs" (TList TString).
  Definition init_Genv : ctenv := map.put map.empty "queries" (TList query_ty).

  Definition elaborated (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_s ds).

  Definition decls := [DUnique "id"].

  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition anno : canno_command :=
    CAC (("areas", (row_ty, decls)) :: cenv_rm "areas" []) O
      basics [KeyedDictIdx "floor" "id"] [] (elaborated decls).

  Definition optimized : command :=
    apply_optimize_anno_constrained anno init_Gstore init_Genv.

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  (* ------------------------------------------------------------------
     What the pipeline produced. *)

  Definition member (i : string) : expr := EAccess (EAccess (ELoc "areas") "aux_tag") i.
  Definition new_area : expr := EAccess (EVar "q") "new_area".

  Definition row_list_ty : type :=
    TRecord [("floor", TOption TString); ("id", TString); ("name", TString)].
  Definition empty_rows : expr := EAtom (ANil (Some row_list_ty)).

  (* a unique index holds the row, so a probe wraps it into a bag *)
  Definition unique_probe (idx k : expr) : expr :=
    EOptMatch (EBinop OLookup idx k) (EAtom (AEmptyBag None)) "y"
      (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "y")).

  (* a bucketed index holds a bag already *)
  Definition bucket_probe (idx k : expr) : expr :=
    EOptMatch (EBinop OLookup idx k) (EAtom (AEmptyBag None)) "b" (EVar "b").

  (* add one row to its bucket, reading the bucket out of the accumulator *)
  Definition bucket_add (acc_e key_e row_e : expr) : expr :=
    ETernop OInsert acc_e key_e
      (EBinop OBagInsert
         (EOptMatch (EBinop OLookup acc_e key_e)
            (EAtom (AEmptyBag None)) "x" (EVar "x"))
         row_e).

  (* ---- the installation ---- *)

  Definition build_by_id : expr :=
    EFold empty_rows (EAtom (AEmptyDict Unranged None)) "tup" "acc"
      (ETernop OInsert (EVar "acc") (EAccess (EVar "tup") "id") (EVar "tup")).

  Definition build_by_floor (src : expr) : expr :=
    EFold src (EAtom (AEmptyDict Unranged None)) "tup" "acc"
      (bucket_add (EVar "acc") (EAccess (EVar "tup") "floor") (EVar "tup")).

  (* No id_tag: nothing reads the list, so the erasure rule drops it and
     the table is its two indexes and nothing else. *)
  Definition install_expected : expr :=
    ERecord
      [("aux_tag",
         ERecord [("0", build_by_floor empty_rows); ("1", build_by_id)])].

  Definition install_of (c : command) : option expr :=
    match c with
    | CLetMut e _ _ => Some e
    | _ => None
    end.

  (* The declared key and the secondary attribute, as two members of one
     index record: a key-to-row dictionary and a key-to-bag dictionary. *)
  Lemma installs_both_members : install_of optimized = Some install_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* ---- the two reads ---- *)

  Definition read_by_id (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CIf _ (CLet e _ _) _)))) => Some e
    | _ => None
    end.

  Definition read_by_floor (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CIf _ _ (CLet e _ _))))) => Some e
    | _ => None
    end.

  (* async_get_area(area_id) (:241): the dict the UserDict already is. *)
  Lemma get_area_probes :
    read_by_id optimized
    = Some (EACFold AGCount (unique_probe (member "1") (EAccess (EVar "q") "k"))).
  Proof. vm_compute; reflexivity. Qed.

  (* get_areas_for_floor(floor) (:211): one probe into the secondary member,
     at key `some floor`.  HA's index omits the rows with no floor; this one
     puts them in the None bucket, which nothing probes. *)
  Lemma areas_for_floor_probes :
    read_by_floor optimized
    = Some (EACFold AGCount
              (bucket_probe (member "0") (EUnop OSome (EAccess (EVar "q") "fl")))).
  Proof. vm_compute; reflexivity. Qed.

  (* ---- the insert: _index_entry ---- *)

  Definition insert_write (c : command) : option (expr * expr) :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ (CIf g (CAssign _ e) _) _)) => Some (g, e)
    | _ => None
    end.

  Definition insert_guard_expected : expr :=
    EBinop OAnd
      (ELet new_area "_pk_row"
         (EBinop OEq (unique_probe (member "1") (EAccess (EVar "_pk_row") "id"))
            (EAtom (AEmptyBag None))))
      (EAtom (ABool true)).

  Definition insert_expected : expr :=
    ERecord
      [("aux_tag",
         ERecord
           [("0", ELet (member "0") "y"
                    (bucket_add (EVar "y") (EAccess new_area "floor") new_area));
            ("1", ELet (member "1") "acc"
                    (ELet new_area "tup"
                       (ETernop OInsert (EVar "acc")
                          (EAccess (EVar "tup") "id") (EVar "tup"))))])].

  (* Both members take one insertion, neither is rebuilt, and the uniqueness
     check is a probe.  This half matches _index_entry line for line. *)
  Lemma insert_is_incremental :
    insert_write optimized = Some (insert_guard_expected, insert_expected).
  Proof. vm_compute; reflexivity. Qed.

  (* ---- the delete: _unindex_entry ---- *)

  Definition delete_write (c : command) : option (expr * expr) :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ (CIf g (CAssign _ e) _) _))) => Some (g, e)
    | _ => None
    end.

  (* The bucket with the leaving row taken out.  A bag has no removal
     operator, so this is a filter: a flatmap keeping the rows whose key
     differs.  The emptiness test beside it is a generic OEq against the
     empty bag. *)
  Definition bucket_without (bkt_e key_e : expr) : expr :=
    flatmap_filter_bag bkt_e "rvar"
      (EUnop ONot (EBinop OEq (EAccess (EVar "rvar") "id") key_e))
      "rvar" None None.

  Definition delete_guard_expected : expr :=
    EBinop OAnd (EAtom (ABool true)) (EAtom (ABool true)).

  Definition delete_expected : expr :=
    ERecord
      [("aux_tag",
         ERecord
           [("0",
             (* the floor index, maintained exactly as _unindex_entry does:
                read the row out of the primary member, find the bucket its
                floor names, and take the row out of that one bucket --
                dropping the bucket if it was the last row in it *)
             ELet (member "0") "acc"
               (EOptMatch (EBinop OLookup (member "1") (EAccess (EVar "q") "k"))
                  (EVar "acc") "tup"
                  (EOptMatch
                     (EBinop OLookup (EVar "acc") (EAccess (EVar "tup") "floor"))
                     (EVar "acc") "bkt"
                     (EIf
                        (EBinop OEq
                           (bucket_without (EVar "bkt") (EAccess (EVar "tup") "id"))
                           (EAtom (AEmptyBag None)))
                        (EBinop ODelete (EVar "acc") (EAccess (EVar "tup") "floor"))
                        (ETernop OInsert (EVar "acc") (EAccess (EVar "tup") "floor")
                           (bucket_without (EVar "bkt")
                              (EAccess (EVar "tup") "id")))))));
            ("1", EBinop ODelete (member "1") (EAccess (EVar "q") "k"))])].

  (* The point of the file.

     Member 1, the primary dict, loses exactly the key named: one ODelete.
     Member 0, the floor index, is NOT rebuilt.  It reads the leaving row
     out of member 1, computes that row's floor, and rewrites the single
     bucket that floor names -- deleting the bucket outright when the row
     was its last.  No fold over the table appears anywhere in it.

     This is _unindex_entry.  HA reads `entry = self.data[key]` and uses
     that row's floor_id to find the bucket to remove the key from, which
     is what the two nested OLookups here do.

     What it cost: the key has to be DECLARED.  The rule is gated on
     DUnique "id" (keyed_delete_gated), because without uniqueness another
     row could carry the same key and its contribution would be left behind
     in a bucket this rewrite never visits.  The declaration is the whole
     price, and it is one the source pays too -- AreaRegistryItems is a dict
     keyed by id, so the uniqueness is a fact about the data structure HA
     chose, not an assumption added here.

     The guard being on "id" and the index being bucketed on "floor" is the
     case the dictionary's own delete rule cannot serve:
     filter_neq_to_delete_head (DictIndexImpl.v:1109) requires the filtered
     attribute to BE the index's attribute.  The two rules are mutually
     exclusive by construction, so both are installed and the applicable
     one fires. *)
  Lemma delete_is_incremental :
    delete_write optimized = Some (delete_guard_expected, delete_expected).
  Proof. vm_compute; reflexivity. Qed.

  (* The delete's guard is free, and that is not an accident of this example:
     classify_write sees a write that only removes rows, and neither a key
     nor a row predicate can be broken by removing rows, so decl_guard emits
     no test.  What is left is the conjunction's unit. *)
  Lemma delete_guard_is_free :
    option_map fst (delete_write optimized) = Some delete_guard_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* And so the list goes.  Both reads probe, and now both writes maintain
     the members in place, so after the rewrite nothing reads the list at
     all and the erasure rule drops the field.  The table IS its indexes.

     This is the third time the erasure rule decides this example: it kept
     the list while the delete rebuilt, and drops it now that the delete
     does not.  The representation gap and the maintenance gap really were
     one gap -- closing the second closed the first, with no change to the
     erasure rule itself. *)
  Lemma delete_drops_the_list :
    installed_fields optimized = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     Sound, and the soundness is the same theorem as before: the pipeline
     proves it, the rewrite did not have to be trusted. *)

  Lemma row_ty_wf : type_wf row_ty.
  Proof.
    unfold row_ty. repeat constructor; cbn; intuition congruence.
  Qed.

  Lemma query_ty_wf : type_wf query_ty.
  Proof.
    unfold query_ty, row_ty. repeat constructor; cbn; intuition congruence.
  Qed.

  Lemma init_Gstore_wf : tenv_wf init_Gstore.
  Proof.
    unfold init_Gstore.
    apply tenv_wf_step; [ apply tenv_wf_empty | repeat constructor ].
  Qed.

  Lemma init_Genv_wf : tenv_wf init_Genv.
  Proof.
    unfold init_Genv.
    apply tenv_wf_step; [ apply tenv_wf_empty | constructor; apply query_ty_wf ].
  Qed.

  Lemma decls_wf : Forall (decl_wf (tenv:=ctenv) row_ty) decls.
  Proof.
    unfold decls, row_ty; cbn [decl_wf].
    repeat constructor;
      exists [("floor", TOption TString); ("id", TString); ("name", TString)], TString;
      split; reflexivity.
  Qed.

  Lemma elaborated_well_typed :
    well_typed init_Gstore init_Genv (elaborated decls).
  Proof.
    eapply command_typechecker_sound with (c := elaborated decls).
    1: apply init_Gstore_wf.
    1: apply init_Genv_wf.
    reflexivity.
  Qed.

  Theorem optimized_sound :
    well_typed init_Gstore init_Genv optimized /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized
        = interp_command store env (elaborated decls).
  Proof.
    unfold optimized, anno, elaborated, prog_s.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply row_ty_wf
      | apply incl_refl | apply decls_wf | apply elaborated_well_typed ].
  Qed.
End WithConcreteMaps.
