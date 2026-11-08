Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem
  fiat2.TypeSound fiat2.TransfSound fiat2.IndexInterface fiat2.rules.CollectionTransf
  fiat2.TransfUtils fiat2.rules.FlatmapForms fiat2.rules.FlatmapTransf fiat2.index.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.Pipeline fiat2.constraint.Decl fiat2.constraint.Surface.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString
  coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith.
Import ListNotations.

(* ============================================================
   Source
     netbox-community/netbox
     netbox/netbox/plugins/registration.py:69-75  (register_template_extensions)

       if template_extension.models:
           models = template_extension.models
       else:
           models = [None]                       # global registration
       for model in models:
           registry['plugins']['template_extensions'][model].append(template_extension)

     netbox/utilities/templatetags/plugins.py:26-48  (_get_registered_content)

       template_extensions = list(registry['plugins']['template_extensions'].get(None, []))
       if hasattr(obj, '_meta'):
           model_name = obj._meta.label_lower
           template_extensions.extend(registry['plugins']['template_extensions'].get(model_name, []))
       for template_extension in template_extensions:
           ...
           html += content

     A dictionary from a model name to the plugin extensions registered for
     it, kept AS A LIST in registration order, appended to at the end, and
     read back in that order.

   Why this subject exists
     Every other dictionary index in this development buckets rows into a
     BAG.  That is sound wherever the read does not look at the order inside
     a group -- and it is almost always enough, which is why the bag-valued
     index came first.  Here it is not enough, and the reason is visible in
     one line of the source: `html += content` concatenates the bucket's
     contents IN ORDER, so a different bucket order is a different answer.
     A bag-valued bucket cannot answer that question at all.

     So the claim is not that this index is faster.  It is that the
     bag-valued index CANNOT SERVE THIS READ: pinned below, with
     DictIdx "model" installed the two reads stay whole-table scans and the
     index is built, maintained, and never read.  That is the gap the
     list-valued index closes, and it is the first place where the LIST
     level of the collection hierarchy is load-bearing inside an INDEX
     rather than only at a table.

   Pattern
     An order-preserving keyed read of an append-built structure.  The read
     is an (N+1): _get_registered_content runs once per rendered object and
     scans the whole registration table each time.

   Claim
     C1 through the collection interpretation, as in HA_LookinFunctions but
     in the opposite direction: there the query observed neither order nor
     multiplicity, so the SET level was available and a membership test
     became a probe.  Here the query DOES observe order, so nothing above
     the list level is available -- and the index that serves it must keep
     its buckets as lists.  Nothing is declared; what licenses the rewrite
     is what the query observes.

     C3: the structure the optimizer derives is the one the plugin registry
     builds by hand -- a dict from model name to an ordered list.

   Faithfulness -- what this translation drops, and why
     * One registration contributes one row PER MODEL (registration.py:69-75
       loops over `models`), so the table is a flat list of (model, content)
       rows and the write adds one.  Registering a global extension is the
       same write at the global key; netbox spells that key `None`, which is
       modelled as the empty string, because Conquord dictionary keys are
       values and a TString key cannot be absent.
     * `html += content` is modelled as the fold below.  EFold is a
       fold_right, so `fold_right (fun e acc => e.content ++ acc) ""` is
       exactly left-to-right concatenation -- the source's order, not its
       reverse.
     * The two buckets are concatenated GLOBAL FIRST (plugins.py:26 then
       :29), so the order BETWEEN buckets is observable as well as the order
       within each.  Both are preserved by the rewrite.
     * The per-extension skip at plugins.py:33-35 (a method the subclass did
       not override) and the exception handling at :44-47 are control flow
       around the concatenation, not reads of the collection, and are
       dropped.  `settings.PLUGINS_CONFIG` is not a collection of the table.
     * Nothing is declared about the table and no uniqueness holds of it: a
       model may have many extensions, which is the point of a bucket.
     * Nothing is added.

   Expected
     With ListDictIdx "model": the row list is ERASED, each of the two reads
     becomes one probe, and the write appends the row to the end of one
     bucket.

     With DictIdx "model": the list SURVIVES and is still appended to, both
     reads stay scans, and the dictionary is dead weight.  That contrast is
     the measurement.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort [("model", TString); ("content", TString)]).

Definition query_ty :=
  TRecord (record_sort [("kind", TInt); ("model", TString); ("row", row_ty)]).

(* the bucket at a key, as a programmer writes it with no index: a filter
   over the whole table.  AT LIST LEVEL, because what consumes it observes
   the order -- and annotate_collection leaves it there, since it relaxes a
   fold only when the fold is a sum or a min. *)
Definition bucket_from (src : expr) (k : expr) : expr :=
  flatmap_filter_list src "e"
    (EBinop OEq (EAccess (EVar "e") "model") k) "e" None None.

Definition bucket (k : expr) : expr := bucket_from (ELoc "exts") k.

(* `html += content` over the bucket, in order *)
Definition render (l : expr) : expr :=
  EFold l (EAtom (AString "")) "e" "acc"
    (EBinop OConcatString (EAccess (EVar "e") "content") (EVar "acc")).

(* the global bucket FOLLOWED BY the model's, as plugins.py:26-29 builds it *)
Definition render_from (src : expr) (m : expr) : expr :=
  render (EBinop OConcat (bucket_from src (EAtom (AString "")))
            (bucket_from src m)).

(* registration.py:75 -- an append at the END of the key's bucket *)
Definition write_register : expr :=
  EBinop OConcat (ELoc "exts")
    (EBinop OCons (EAccess (EVar "q") "row") (EAtom (ANil None))).

Definition prog : command :=
  CLetMut (EVar "exts_tbl") "exts"
    (CForeach (EVar "queries") "q"
       (CIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt 0)))
          (CAssign "outputs"
             (EBinop OCons (render_from (ELoc "exts") (EAccess (EVar "q") "model"))
                (ELoc "outputs")))
          (CAssign "exts" write_register))).

Section WithConcreteMaps.
  Notation value := (value).
  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.
  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put (map.put map.empty "exts_tbl" (TList row_ty))
      "queries" (TList query_ty).

  Definition checks (c : command) : bool :=
    match typecheck init_Gstore init_Genv c with
    | Success _ => true
    | Failure _ => false
    end.

  Lemma prog_typechecks : checks prog = true.
  Proof. vm_compute; reflexivity. Qed.

  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition optimized_with (ics : list index_choice) : command :=
    apply_optimize_anno (AC basics [ics] prog) init_Gstore init_Genv.

  Definition opt_list := optimized_with [ListDictIdx "model"].
  Definition opt_bag  := optimized_with [DictIdx "model"].

  (* ------------------------------------------------------------------
     The projections the pins read off.
     ------------------------------------------------------------------ *)
  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  Fixpoint read_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ c' | CForeach _ _ c' => read_of c'
    | CIf _ c' _ => read_of c'
    | CAssign "outputs" (EBinop OCons r _) => Some r
    | _ => None
    end.

  Fixpoint write_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ c' | CForeach _ _ c' => write_of c'
    | CIf _ _ c' => write_of c'
    | CAssign "exts" e => Some e
    | _ => None
    end.

  (* the table read, as it is spelled once the table has become a record *)
  Definition tbl_field : expr := EAccess (ELoc "exts") "id_tag".

  (* the index member, and a probe into it *)
  Definition idx_field : expr :=
    EAccess (EAccess (ELoc "exts") "aux_tag") "0".

  (* a probe into a dictionary, with the binder the emitting rule uses:
     the read rule binds "b", the maintenance rule binds "x" *)
  Definition probe_as (v : string) (d : expr) (k : expr) : expr :=
    EOptMatch (EBinop OLookup d k) (EAtom (ANil None)) v (EVar v).

  Definition probe (d : expr) (k : expr) : expr := probe_as "b" d k.

  (* ------------------------------------------------------------------
     PIN 1.  With list-valued buckets the row list is ERASED: the only
     installed field is the index, so the table IS its index.
     ------------------------------------------------------------------ *)
  Lemma list_idx_erases_the_list :
    installed_fields opt_list = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* and with bag-valued buckets it is NOT -- the list survives because the
     reads still need it *)
  Lemma bag_idx_keeps_the_list :
    installed_fields opt_bag = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     PIN 2.  The read.  Both buckets become probes, and the concatenation
     and the fold are untouched -- so the order within each bucket and the
     order between them are exactly the source's.
     ------------------------------------------------------------------ *)
  Lemma list_read_is_two_probes :
    read_of opt_list
    = Some (render (EBinop OConcat
                      (probe idx_field (EAtom (AString "")))
                      (probe idx_field (EAccess (EVar "q") "model")))).
  Proof. vm_compute; reflexivity. Qed.

  (* THE NEGATIVE CONTROL, and the reason this index exists: with the
     bag-valued dictionary installed, the read is the SOURCE'S SCAN, with
     the table read through its field and nothing else changed.  The filter
     is still EFlatmap LikeList -- the demand analysis never relaxed it,
     because the fold observes the order -- and no rule of the bag-valued
     index matches a filter at that level. *)
  Lemma bag_read_is_still_two_scans :
    read_of opt_bag = Some (render_from tbl_field (EAccess (EVar "q") "model")).
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     PIN 3.  The write.  One probe and one insert: the row is appended to
     the END of its own bucket and no other bucket is touched.  No fold
     over the table is left.
     ------------------------------------------------------------------ *)
  Definition row_key : expr := EAccess (EAccess (EVar "q") "row") "model".

  Lemma list_write_appends_into_one_bucket :
    write_of opt_list
    = Some (ERecord
              [("aux_tag",
                 ERecord
                   [("0",
                      ELet idx_field "y"
                        (ETernop OInsert (EVar "y") row_key
                           (EBinop OConcat
                              (probe_as "x" (EVar "y") row_key)
                              (EBinop OCons (EAccess (EVar "q") "row")
                                 (EAtom (ANil None))))))])]).
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     And both are sound: each optimized program computes what the source
     computes, on every store and environment.  The bag-valued one is sound
     too -- it is useless here, not wrong.
     ------------------------------------------------------------------ *)
  Theorem opt_list_sound : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      interp_command store env opt_list = interp_command store env prog.
  Proof.
    unfold opt_list, optimized_with, apply_optimize_anno; intros.
    eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
  Qed.

  Theorem opt_bag_sound : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      interp_command store env opt_bag = interp_command store env prog.
  Proof.
    unfold opt_bag, optimized_with, apply_optimize_anno; intros.
    eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
  Qed.
End WithConcreteMaps.
