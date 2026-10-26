Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.FlatmapForms fiat2.OptimizeAnno fiat2.Selector.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   Source
     SAT4J's per-variable literal storage, as the Cozy benchmark suite
     states it: examples/sat4j-literal-storage.ds in that distribution.

       handletype Record = { var : Int, level : Int, reason : Constr,
                             posWatches : PropagatableVector,
                             negWatches : PropagatableVector,
                             undos : UndoVector }
       state records : Bag<Record>
       invariant unique [record.val.var | record <- records];

       query size()                 sum [1 | _ <- records]
       query findRecord(varId)      the [ r | r <- records, r.val.var == varId ]
       query belongsToPool(varId)   exists [ r | r <- records, r.val.var == varId ]
       query getLevel(varId)        the [ r.val.level | ... == varId ]
       query getReason(varId)       the [ r.val.reason | ... == varId ]
       query getUndos(varId)        the [ r.val.undos | ... == varId ]
       query getPosWatches(varId)   the [ r.val.posWatches | ... == varId ]
       query getNegWatches(varId)   the [ r.val.negWatches | ... == varId ]

   WHY THIS SUBJECT IS HERE, AND IT IS NOT THE USUAL REASON
     Every other subject in this directory was found by us, in a corpus we
     chose, by a search we designed.  That is the standing objection to an
     evaluation like this one and it cannot be answered from inside our own
     selection.  This subject is not ours: it is one of the five
     application-derived specifications in the benchmark suite of Cozy
     (Loncaract et al., ICSE'18), chosen by other people, for other people's
     paper, before this system existed.  Two of their five turned out to be
     expressible in our language; this is the one of the two that needs no
     capability we lack.  See comparison/cozy/README.md for the audit of all
     twenty of their examples and why the other three are out of reach.

     The claim it supports is therefore about representativeness and nothing
     else.  It is not evidence that we beat Cozy -- Cozy runs on it too, and
     what it derives is recorded beside what we derive.

   Pattern
     A1a with a declared key, at an extreme: EIGHT reads over one table, of
     which SEVEN are the same single-row lookup wearing different clothes --
     one asks for the row, five project one field each, and one asks only
     whether the row is there.  The eighth is a whole-table count.

     That shape is the reason the subject is worth having.  Our other
     declared-key subject (Keycloak) has two keys and three reads; this one
     has one key and eight, so it is the case where a single index either
     serves everything or is exposed as serving only the shape it was
     pattern-matched against.

   Claim
     C1: uniqueness is what licenses a single-row answer, and here it
     licenses seven of them from one index.
     C4: nothing in the source mentions an index.  SAT4J's own code reaches
     these fields through arrays indexed by variable number; the
     specification above, written by someone else, is the scan form.

   Faithfulness -- what this translation drops, and why
     * The three Native types (Constr, PropagatableVector, UndoVector) are
       opaque: no query reads INTO them, each is only fetched whole.  They
       are TInt here.  This is the honest encoding precisely because the
       queries treat them as atoms, and it is recorded in the Cozy spec for
       this subject as well.
     * `handletype` gives Cozy reference semantics: a Record is a mutable
       object with identity, and `updateLevel(rec, level)` mutates through
       the caller's handle.  We have value rows.  So the two update ops are
       written here as the delete-then-insert pair they are under value
       semantics, keyed on `var` -- which is also what the caller must do,
       since it reached the record by findRecord(var) in the first place.
       This is a translation decision, not a simplification: it is the one
       place where the source has a capability the translation does not, and
       it is the reason classify_write matters below.
     * `the [...]` is a partial operation: on an absent key Cozy's `the` is
       undefined and this translation's reads answer 0 rows (for the row
       read) or 0 (for a projection, being a sum over no rows).  Under the
       declared key both agree wherever `the` is defined.
     * The output channel is a list of strings, so each read is counted; a
       projection read is reported as the sum of the projected field over
       the matching rows, which under uniqueness is that row's field.

   What happened -- and HALF OF IT IS A GAP WE DID NOT KNOW WE HAD
     The selector, given nothing but the program and the declaration, chooses
     [UniqueDictIdx "var"; CountAgg] by itself: pinned as `selector_chooses`.
     It also declines FilterEmptyToSetMem, because the table has a declared
     key (Selector.v:405, the third rule-ordering hazard) -- so this is the
     first subject where that decision is forced by a program we did not
     write.  Pinned as `selector_declines_set_mem`.

     Served by the one index, as probes:
       * findRecord      -- `find_read_is_a_probe`
       * belongsToPool   -- `exists_read_is_a_probe`.  This is the good
         surprise: with FilterEmptyToSetMem unavailable, the DECLARED KEY
         answers the existence test by itself.  Our other existence subject
         (Lookin) needs SetAgg and that rewrite; a declared key needs
         neither, because the filter becomes a probe and the emptiness test
         then reads the probe's result.
       * both uniqueness guards, one per insert.

     NOT served -- the five projection reads, `getLevel`, `getReason`,
     `getUndos`, `getPosWatches`, `getNegWatches`, each of which stays a FULL
     SCAN of the list.  Pinned as `projection_read_is_left_alone`.

     The cause is a pattern gap, not a soundness obstacle, and it is exact.
     `unique_lookup_head` (UniqueIndexUse.v:432) matches
     `flatmap_filter_bag`, whose then-branch the notation fixes as
     `OBagInsert (AEmptyBag _) (EVar y)` (FlatmapForms.v:17) -- the row
     ITSELF -- and the rule further requires that variable to be the bound
     row.  A projection is the separate form `flatmap_proj_bag`
     (FlatmapForms.v:26).  A read that FILTERS AND PROJECTS IN ONE FLATMAP,
     i.e. `[ r.attr | r <- rows, r.key == k ]`, is neither form, so no rule
     claims it.  Five of the eight queries in this third-party specification
     are written exactly that way.

     The consequence is measurable and is the reason this subject is not a
     victory lap: because those five scans still read the list, CountAgg
     cannot erase it, and `counted_keeps_the_list` pins that -- the opposite
     of Keycloak's ending, from the same two index choices.

     What would close it is a normalisation that splits a filtering
     projection into the two forms the rules already match; whether to add
     one is a language decision and is not taken here.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort
             [("var", TInt); ("level", TInt); ("reason", TInt);
              ("pos_watches", TInt); ("neg_watches", TInt); ("undos", TInt)]).

Definition query_ty :=
  TRecord (record_sort [("kind", TInt); ("v", TInt); ("new_rec", row_ty)]).

Section WithConcreteMaps.
  Notation value := (value).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* The scan a programmer writes with no index: walk the table, keep the
     rows whose var is the one asked for.  Every key read below is this
     filter with a different thing done to the result. *)
  Definition at_var : expr :=
    EBinop OEq (EAccess (EVar "r") "var") (EAccess (EVar "q") "v").

  (* findRecord: the row itself, counted. *)
  Definition q_find : expr :=
    EUnop OLength
      (EFlatmap LikeList (ELoc "records") "r"
         (EIf at_var (EBinop OCons (EVar "r") (EAtom (ANil None)))
            (EAtom (ANil None)))).

  (* getLevel / getReason / getUndos / getPosWatches / getNegWatches: the
     same filter, projecting one field.  Under the declared key the sum is
     over at most one row, so it IS that row's field. *)
  Definition q_project (attr : string) : expr :=
    EACFold AGSum
      (EFlatmap LikeBag (EBagOf (ELoc "records")) "r"
         (EIf at_var
            (EBinop OBagInsert (EAtom (AEmptyBag None)) (EAccess (EVar "r") attr))
            (EAtom (AEmptyBag None)))).

  (* belongsToPool: is the filter non-empty?  No field is read at all. *)
  Definition q_exists : expr :=
    EUnop ONot
      (EBinop OEq
         (EFlatmap LikeBag (EBagOf (ELoc "records")) "r"
            (EIf at_var (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "r"))
               (EAtom (AEmptyBag None))))
         (EAtom (AEmptyBag None))).

  (* size(): the whole table, counted.  This is the read that decides
     whether the list survives. *)
  Definition q_size : expr :=
    EACFold AGCount (EBagOf (ELoc "records")).

  (* remove(rec), and the first half of an update: drop the row at this key. *)
  Definition without_var : expr :=
    EFlatmap LikeList (ELoc "records") "r"
      (EIf (EUnop ONot at_var)
         (EBinop OCons (EVar "r") (EAtom (ANil None))) (EAtom (ANil None))).

  Definition report (e : expr) : scommand :=
    SLet e "n"
      (SAssign "outputs"
         (EBinop OCons (EUnop OIntToString (EVar "n")) (ELoc "outputs")) SSkip).

  Definition say (s : string) : scommand :=
    SAssign "outputs" (EBinop OCons (EAtom (AString s)) (ELoc "outputs")) SSkip.

  Definition dispatch (k : Z) (thn els : scommand) : scommand :=
    SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt k))) thn els.

  Definition prog_s (ds : list decl) : scommand :=
    SLetConstrained "records" row_ty ds
      (SForeach (EVar "queries") "q"
         (dispatch 0
            (* add(rec): the declared key is checked here *)
            (SAssign "records"
               (EBinop OCons (EAccess (EVar "q") "new_rec") (ELoc "records")) SSkip)
            (dispatch 1
               (* remove(rec) *)
               (SAssign "records" without_var SSkip)
               (dispatch 2
                  (* updateLevel(rec, level): under value semantics, the row
                     at this key is dropped and the new one inserted.  Two
                     recognized writes where the source has one mutation. *)
                  (SSeq (SAssign "records" without_var SSkip)
                     (SAssign "records"
                        (EBinop OCons (EAccess (EVar "q") "new_rec") (ELoc "records"))
                        SSkip))
                  (dispatch 3 (report q_find)
                     (dispatch 4
                        (SIf q_exists (say "in-pool") (say "absent"))
                        (dispatch 5 (report q_size)
                           (dispatch 6 (report (q_project "level"))
                              (dispatch 7 (report (q_project "reason"))
                                 (dispatch 8 (report (q_project "undos"))
                                    (dispatch 9 (report (q_project "pos_watches"))
                                       (report (q_project "neg_watches"))))))))))))).

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put map.empty "queries" (TList query_ty).

  Definition elaborated (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_s ds).

  Definition decls := [DUnique "var"].

  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition anno : canno_command :=
    CAC (("records", (row_ty, decls)) :: cenv_rm "records" []) O
      basics [UniqueDictIdx "var"] [] (elaborated decls).

  Definition optimized : command :=
    apply_optimize_anno_constrained anno init_Gstore init_Genv.

  (* The second configuration adds the maintained count, which is the only
     thing that can retire size()'s whole-table read. *)
  Definition anno_counted : canno_command :=
    CAC (("records", (row_ty, decls)) :: cenv_rm "records" []) O
      basics [UniqueDictIdx "var"; CountAgg] [] (elaborated decls).

  Definition optimized_counted : command :=
    apply_optimize_anno_constrained anno_counted init_Gstore init_Genv.

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  (* ------------------------------------------------------------------
     What the pipeline produced.

     Every claim is an equality of closed terms, so it reduces by
     computation and can be read as a diff against the program above. *)

  (* The dispatch chain is a right-nested CIf, so an arm is reached by going
     n else-branches down and taking the then-branch.  Arm k is the branch
     for `kind = k`. *)
  Fixpoint nth_arm (n : nat) (c : command) : option command :=
    match c with
    | CLetMut _ _ c' => nth_arm n c'
    | CForeach _ _ c' => nth_arm n c'
    | CIf _ thn els => match n with O => Some thn | S k => nth_arm k els end
    | _ => None
    end.

  Definition ce : cenv := [("records", (row_ty, decls))].

  (* ---- what the selector chooses, given only the program ---- *)

  (* Not hand-picked: the configuration used above is the one the selector
     computes for this table. *)
  Lemma selector_chooses :
    select_choices ce "records" (elaborated decls)
    = [UniqueDictIdx "var"; CountAgg].
  Proof. vm_compute; reflexivity. Qed.

  (* And FilterEmptyToSetMem is absent, although this program HAS an
     emptiness test of an equality filter -- the demand that rewrite exists
     for.  It is declined because the table carries a declared key, which is
     the third rule-ordering hazard in Selector.v:405.  Until now that
     decision was exercised only by programs we wrote. *)
  Lemma selector_declines_set_mem :
    select_basics ce "records" (elaborated decls)
    = [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].
  Proof. vm_compute; reflexivity. Qed.

  (* ---- the reads the index serves ---- *)

  (* the shape a lookup has when the key is declared unique: the one row, or
     no row *)
  Definition probe : expr :=
    EOptMatch
      (EBinop OLookup (EAccess (EAccess (ELoc "records") "aux_tag") "0")
         (EAccess (EVar "q") "v"))
      (EAtom (AEmptyBag None)) "y"
      (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "y")).

  Definition reported (e : expr) : command :=
    CLet e "n"
      (CAssign "outputs"
         (EBinop OCons (EUnop OIntToString (EVar "n")) (ELoc "outputs"))).

  (* findRecord(varId): the scan is gone. *)
  Lemma find_read_is_a_probe :
    nth_arm 3 optimized_counted = Some (reported (EACFold AGCount probe)).
  Proof. vm_compute; reflexivity. Qed.

  (* belongsToPool(varId): the declared key answers an existence test on its
     own.  FilterEmptyToSetMem is not in the pipeline (above), and SetAgg is
     not in the configuration -- the filter became a probe and the emptiness
     test now reads the probe's result. *)
  Lemma exists_read_is_a_probe :
    nth_arm 4 optimized_counted
    = Some (CIf (EUnop ONot (EBinop OEq probe (EAtom (AEmptyBag None))))
              (CAssign "outputs"
                 (EBinop OCons (EAtom (AString "in-pool")) (ELoc "outputs")))
              (CAssign "outputs"
                 (EBinop OCons (EAtom (AString "absent")) (ELoc "outputs")))).
  Proof. vm_compute; reflexivity. Qed.

  (* ---- the reads it does NOT serve, pinned so they cannot be forgotten ---- *)

  (* getLevel(varId) is `[ r.level | r <- records, r.var == varId ]`: it
     filters AND projects in one flatmap.  unique_lookup_head matches
     flatmap_filter_bag, whose then-branch must be the bound row itself, so
     nothing claims this read and it stays a full scan of the list.  The
     other four projection reads (arms 7, 8, 9 and the last) are the same
     term with a different attribute. *)
  Definition projection_scan (attr : string) : expr :=
    EACFold AGSum
      (EFlatmap LikeBag (EBagOf (EAccess (ELoc "records") "id_tag")) "r"
         (EIf (EBinop OEq (EAccess (EVar "r") "var") (EAccess (EVar "q") "v"))
            (EBinop OBagInsert (EAtom (AEmptyBag None))
               (EAccess (EVar "r") attr))
            (EAtom (AEmptyBag None)))).

  Lemma projection_read_is_left_alone :
    nth_arm 6 optimized_counted = Some (reported (projection_scan "level")).
  Proof. vm_compute; reflexivity. Qed.

  Lemma projection_read_is_left_alone_reason :
    nth_arm 7 optimized_counted = Some (reported (projection_scan "reason")).
  Proof. vm_compute; reflexivity. Qed.

  (* And the consequence.  Keycloak's list is ERASED by exactly these two
     index choices, because its only remaining reader was a whole-table
     count.  Here five scans still read the list, so CountAgg cannot retire
     it.  Same two choices, opposite ending -- which is why "CountAgg erases
     the list" is a statement about a program and not about the rule. *)
  Lemma counted_keeps_the_list :
    installed_fields optimized_counted = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ---- soundness: the whole point, and it is one lemma ---- *)

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
      exists [("level", TInt); ("neg_watches", TInt); ("pos_watches", TInt);
              ("reason", TInt); ("undos", TInt); ("var", TInt)], TInt;
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

  Theorem optimized_counted_sound :
    well_typed init_Gstore init_Genv optimized_counted /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized_counted
        = interp_command store env (elaborated decls).
  Proof.
    unfold optimized_counted, anno_counted, elaborated, prog_s.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply row_ty_wf
      | apply incl_refl | apply decls_wf | apply elaborated_well_typed ].
  Qed.
End WithConcreteMaps.
