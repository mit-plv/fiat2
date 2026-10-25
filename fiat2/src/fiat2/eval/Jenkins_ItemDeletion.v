Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.FlatmapForms fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   Source
     jenkinsci/jenkins, commit 81dc9a3e13a3ec4c4f74bedb772e3382b8de0760
     core/src/main/java/jenkins/model/queue/ItemDeletion.java:74, :129, :149, :165

       private final Set<Item> registrations = new HashSet<>();

       public static boolean contains(@NonNull Item item) {
           return instance.registrations.contains(item);
       }
       static boolean register(@NonNull Item item) {
           return instance.registrations.add(item);
       }
       static void deregister(@NonNull Item item) {
           instance.registrations.remove(item);
       }

     The same shape occurs a second time in the corpus, in
     connect/runtime/.../WorkerTransactionContext.java:38-39, where two
     Set<SourceRecord> fields are added to, removed from, and asked
     contains(record) at :101 -- so it is an idiom rather than a one-off.

   Pattern
     D1 multiplicity discarded and B3 membership scan, as in
     HA_LookinFunctions -- but at ROW level.  Lookin derives a set of an
     attribute's VALUES, which is SetAgg; here the elements of the set are the
     rows themselves.

     The distinction is the whole reason this file exists.  `contains` is
     handed an Item, not an id, so the question is about a whole row and there
     is no key to probe with.  No DICTIONARY can answer it: a dictionary needs
     a key, and the only key here would be the row.  So of the indexes in this
     development exactly one serves this read -- TableRep -- and that is what
     makes this the subject on which TableRep can be measured rather than
     merely exhibited.

   Claim
     C1 by the collection interpretation, as in Lookin: nothing is declared,
     and what licenses the rewrite is that the read observes neither order nor
     multiplicity.  C4 secondarily: the author chose a Set, and the optimizer
     derives one.

   What this file is FOR
     The two configurations differ only in whether TableRep is asked for, and
     the question they settle is where the coercion is paid.

       WITHOUT it the table is a list and every membership test builds the set
         again: linear in the table, per read.
       WITH it the set IS the stored member and the test reads it directly;
         what moves to the writes is a set insert in place of a cons.

     That is the ordinary index bargain -- pay per read or pay per write --
     and it is the one cost argument for TableRep that the other subjects
     cannot make, because in all of them a dictionary can serve the read that
     keeps the list alive.

   WHAT IT MEASURED (harness/, subject "item_deletion", 20 ops of each kind,
   COMPARISONS, which is where a tree operation's cost lives -- count.ml says
   so, and it is why the read's step counts are equal: neither configuration
   walks the table at the AST level for a membership test)

     kind            50 rows   1600 rows            32x the rows
     containsHit  src  10,872     764,164   70.3x   -- the coercion, n log n
                  opt     232         444    1.9x   -- a tree descent
     containsMiss src  10,860     764,200   70.4x
                  opt     220         480    2.2x
     register     src      40          40    1.0x   -- a cons
                  opt     340         578    1.7x   -- a set insert
     deregister   src   1,680      63,680   37.9x   -- filter a list
                  opt     268         532    2.0x   -- a tree deletion

   Every read and every write is FLAT.  The exponents in cost ~ rows^a are
   0.18, 0.21, 0.15 and 0.20, against the source's 1.22, 1.22, 0.00 and 1.04,
   and the op phase as a whole falls from 289,220 steps and 1,592,358
   comparisons to 1,200 and 2,126.  The one column TableRep loses is
   register, by 538 comparisons on an operation whose cost does not grow.

   THE DELETE DID NOT START OUT THAT WAY, and the history is the point.
   Before SetRemoveTransf existed it cost 744,280 comparisons -- 11.7x WORSE
   than the source's list filter, and asymptotically worse, because the
   semantics of a set-level filter rebuilds the member and every surviving
   row pays a logarithmic insert.  So the first measurement of this subject
   was a trade: a large win on the read, a log factor given back on the
   write.  What rules that out is rep_delete_is_a_set_removal -- the filter
   recognised for what it is, one row leaving a set -- and the column drops
   by a factor of 1399.  The rule is not about TableRep and is stated for any
   set (SetRemoveTransf.v); this subject is only where its absence showed.

   Faithfulness -- what this translation drops, and why
     * Item carries a name, a parent and much else.  Two fields are kept:
       `name` and `parent`.  Two rather than one because with a single field a
       whole-row membership test degenerates into a membership test on a key,
       which a dictionary COULD serve -- and that would make the measurement
       answer a different question.
     * _contains (:78-93) walks an item's ancestors, testing each: a loop
       whose body is this read.  The loop is not modelled; the per-test cost
       is what differs between the configurations, and the loop multiplies
       both sides by the same factor.
     * registrations is guarded by a lock and reached through a singleton.
       Conquord has neither, and neither affects the shape of the read.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort [("name", TString); ("parent", TString)]).

Definition query_ty :=
  TRecord (record_sort [("kind", TInt); ("item", row_ty)]).

Section WithConcreteMaps.
  Notation value := (value).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* registrations.contains(item), written as the author wrote it: the table
     AS A SET, and a membership test on it.  The coercion is the
     PROGRAMMER's -- it is not something the collection phase inferred -- and
     with no index it is paid on every evaluation. *)
  Definition is_registered : expr :=
    EBinop OSetMem (ESetOf (ELoc "registrations"))
      (EAccess (EVar "q") "item").

  (* registrations.remove(item): the row leaves, identified by nothing but
     itself. *)
  Definition without_row : expr :=
    flatmap_filter_list (ELoc "registrations") "r"
      (EUnop ONot (EBinop OEq (EVar "r") (EAccess (EVar "q") "item")))
      "r" (Some row_ty) (Some row_ty).

  Definition say (s : string) : scommand :=
    SAssign "outputs" (EBinop OCons (EAtom (AString s)) (ELoc "outputs")) SSkip.

  Definition dispatch (k : Z) (thn els : scommand) : scommand :=
    SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt k))) thn els.

  (* The table arrives in the environment rather than being born empty, for
     the reason recorded in this directory's README: a table that starts empty
     and is only grown by the workload makes every read cheap for a reason
     that has nothing to do with the index. *)
  Definition prog_s : scommand :=
    SLetMut (EVar "items_tbl") "registrations"
      (SForeach (EVar "queries") "q"
         (dispatch 0
            (* ItemDeletion.contains(item) *)
            (SIf is_registered (say "deleting") (say "free"))
            (dispatch 1
               (* ItemDeletion.register(item) *)
               (SAssign "registrations"
                  (EBinop OCons (EAccess (EVar "q") "item") (ELoc "registrations"))
                  SSkip)
               (* ItemDeletion.deregister(item) *)
               (SAssign "registrations" without_row SSkip)))).

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put (map.put map.empty "items_tbl" (TList row_ty))
      "queries" (TList query_ty).

  Definition elaborated : command :=
    elab [] (get_free_vars init_Genv) prog_s.

  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  (* configuration 0: nothing is installed.  The membership test keeps
     coercing the table. *)
  Definition anno_scan : anno_command := AC basics [[]] elaborated.

  Definition optimized_scan : command :=
    apply_optimize_anno anno_scan init_Gstore init_Genv.

  (* configuration 1: the table's own set is a member. *)
  Definition anno_rep : anno_command := AC basics [[TableRep LikeSet]] elaborated.

  Definition optimized_rep : command :=
    apply_optimize_anno anno_rep init_Gstore init_Genv.

  (* ---------- what the two configurations are, pinned ---------- *)

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  Definition read_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ (CIf g _ _) _)) => Some g
    | _ => None
    end.

  Definition insert_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ (CAssign _ e) _))) => Some e
    | _ => None
    end.

  Definition delete_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CAssign _ e)))) => Some e
    | _ => None
    end.

  Definition the_item : expr := EAccess (EVar "q") "item".
  Definition the_list : expr := EAccess (ELoc "registrations") "id_tag".
  Definition member (tag : string) : expr :=
    EAccess (EAccess (ELoc "registrations") "aux_tag") tag.

  (* ============ configuration 0: no index ============ *)

  Lemma scan_keeps_the_list :
    installed_fields optimized_scan = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* The read the author wrote, unchanged: the whole table coerced to a set,
     and then one membership test on it.  Nothing is wrong with this program
     -- it is what the source says -- and the coercion is linear in the table
     ON EVERY EVALUATION.  That is the cost the next configuration moves. *)
  Lemma scan_coerces_the_table :
    read_of optimized_scan
    = Some (EBinop OSetMem (ESetOf the_list) the_item).
  Proof. vm_compute; reflexivity. Qed.

  Lemma scan_insert_is_a_cons :
    insert_of optimized_scan
    = Some (ERecord [("id_tag", EBinop OCons the_item the_list);
                     ("aux_tag", ERecord [])]).
  Proof. vm_compute; reflexivity. Qed.

  (* ============ configuration 1: the table IS its set ============ *)

  (* The list is gone, and here that is not a restatement of some other
     index's work: TableRep's member is the only structure in the program. *)
  Lemma rep_erases_the_list :
    installed_fields optimized_rep = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* The read is now a membership test on STORED state.  The coercion is not
     cheaper, it is absent -- which is the one thing no dictionary in this
     development can do for this read, because a dictionary needs a key and
     the question here is about a whole row. *)
  Lemma rep_reads_the_member :
    read_of optimized_rep
    = Some (EBinop OSetMem (member "0") the_item).
  Proof. vm_compute; reflexivity. Qed.

  (* and this is what it costs: the cons becomes a set insert *)
  Lemma rep_insert_is_a_set_insert :
    insert_of optimized_rep
    = Some (ERecord [("aux_tag",
                      ERecord [("0", EBinop OSetInsert (member "0") the_item)])]).
  Proof. vm_compute; reflexivity. Qed.

  (* The delete is no longer a filter at all.  push_down_collection puts the
     source's row-by-row filter at set level over the member, and
     filter_neq_to_set_remove_head then says what that filter IS: the member,
     less the one row.  A tree deletion rather than a rebuild. *)
  Lemma rep_delete_is_a_set_removal :
    delete_of optimized_rep
    = Some (ERecord
              [("aux_tag",
                ERecord
                  [("0", EBinop OSetDiff (member "0")
                           (EBinop OSetInsert (EAtom (AEmptySet None)) the_item))])]).
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     And both compute what the source computes, on every store and
     environment. *)

  Lemma row_ty_wf : type_wf row_ty.
  Proof. unfold row_ty. repeat constructor; cbn; intuition congruence. Qed.

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
    apply tenv_wf_step;
      [ apply tenv_wf_step; [ apply tenv_wf_empty | constructor; apply row_ty_wf ]
      | constructor; apply query_ty_wf ].
  Qed.

  Lemma elaborated_well_typed :
    well_typed init_Gstore init_Genv elaborated.
  Proof.
    eapply command_typechecker_sound with (c := elaborated).
    1: apply init_Gstore_wf.
    1: apply init_Genv_wf.
    reflexivity.
  Qed.

  Theorem optimized_scan_sound :
    well_typed init_Gstore init_Genv optimized_scan /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized_scan
        = interp_command store env elaborated.
  Proof.
    unfold optimized_scan, anno_scan.
    apply apply_all_transfs_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply elaborated_well_typed ].
  Qed.

  Theorem optimized_rep_sound :
    well_typed init_Gstore init_Genv optimized_rep /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized_rep
        = interp_command store env elaborated.
  Proof.
    unfold optimized_rep, anno_rep.
    apply apply_all_transfs_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply elaborated_well_typed ].
  Qed.
End WithConcreteMaps.
