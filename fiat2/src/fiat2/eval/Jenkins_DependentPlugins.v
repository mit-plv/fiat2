Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.FlatmapForms fiat2.OptimizeAnno fiat2.Selector
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.FlatmapTransf fiat2.IndexTransf.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   Source
     jenkins, core/src/main/java/hudson/PluginManager.java:1042,
     resolveDependentPlugins(), over the field `plugins` at :325

       for (PluginWrapper plugin : plugins) {
           Set<String> optionalDependents = new HashSet<>();
           Set<String> dependents = new HashSet<>();
           for (PluginWrapper possibleDependent : plugins) {
               if (possibleDependent.getShortName().equals(plugin.getShortName()))
                   continue;                                  // (1) not itself
               if (possibleDependent.isDeleted())
                   continue;                                  // (2) nor deleted
               for (Dependency dependency : possibleDependent.getDependencies())
                   if (dependency.shortName.equals(plugin.getShortName())) {
                       dependents.add(possibleDependent.getShortName());
                       if (dependency.optional)               // (3) THE JOIN
                           optionalDependents.add(possibleDependent.getShortName());
                       break;
                   }
           }
           plugin.setDependents(dependents);
           plugin.setOptionalDependents(optionalDependents);
       }

   This is the first subject here whose SOURCE IS QUADRATIC.  Every other one
   scans a table once per read; this one iterates `plugins` inside `plugins`
   and then walks each inner plugin's dependency list, so it costs
   |plugins| x |plugins| x |dependencies| -- and `plugins` is a maintained
   field, not a request-scoped list.

   Pattern
     A nested-loop EQUIJOIN: one collection iterated inside itself, with an
     equality relating the outer row to the inner one.  Found by searching
     the corpora for exactly this shape (corpus/joins) and then reading every
     candidate; of the survivors this is the one whose cost is most clearly
     quadratic in state the program keeps, which is why it is the one written
     up.

     NO CODE FROM THE PATTERN CATALOGUE IS CLAIMED HERE, and that is
     deliberate.  Every other file in this directory names codes -- A1a, B7,
     D1 and so on -- from the catalogue the paper cites, but those codes are
     not reproduced anywhere in this repository, so assigning one from memory
     would be a guess dressed as a citation.  If the catalogue has a code for
     a nested-loop join, this is the one header in this directory where it
     should be filled in by hand.  The eval README's pattern table says the
     same thing in the one place a reader would look for it.

     What the join adds to the set is coverage rather than another instance:
     every other subject reads its table once per read, and this one reads it
     once per ROW.  It is the only quadratic source here, and the only
     subject whose two collections are the same collection.

   Claim
     C4, and more sharply than elsewhere: the author wrote the join as two
     nested loops and there is no structure here at all, derived or
     hand-built.  What the optimizer offers is the dictionary that turns the
     inner loop into a probe.

   THE GUARD ORDER IS THE POINT, AND IT FAVOURS NOTHING HERE
     Read the three conditions in the order the source evaluates them.  The
     indexable one -- an equality between a dependency's name and the outer
     plugin's name -- is THIRD.  In front of it sit a NOT-equality (not
     itself) and a boolean flag test (not deleted), neither of which any
     index rule matches.

     `if_nil_into_flatmap_head` splits a loop on its OUTERMOST guard, so what
     the index rules are offered here is the not-equality.  Nothing serves
     that, and the equality that would be served is behind it.  Promoting it
     needs to know which attribute is indexed, which is decided in a later
     phase than the one that would have to do the promoting.

     That limit was identified while adding SwapFlatmapIf to the selector and
     recorded as having NO witness in the corpus.  This file was that witness,
     and finding it is what prompted the fix: the selector used to ask for no
     index on this program at all.  It now asks for the right one, because
     `PromoteGuard` (PromoteGuard.v) moves the equality to the head of its
     chain and the demand that emits it is about guard POSITION rather than
     about any attribute.  What it reaches is pinned below, beside the two
     hand-written configurations it beats.

   Faithfulness -- what this translation changes, and why
     * A DEPENDENCY LIST IS A COLLECTION INSIDE A ROW, which this development
       cannot express (see the collection-keyed index entry in the limits
       table).  So the edges are flattened into their own table: one row per
       (dependent, dependency) pair.  That is the standard relational
       encoding of a nested collection and it is the one real change here.
       It turns a three-level loop into a two-collection join, which is the
       shape the index rules are stated against anyway.
     * `isDeleted()` is read on the DEPENDENT plugin, so after flattening it
       belongs to the plugin and not to the edge.  Carrying it on the edge
       instead is a denormalisation, and the alternative -- a second join
       from the edge back to the plugin row -- is expressible here but is not
       what this subject is for.  Keeping the flag on the edge preserves all
       three guards IN SOURCE ORDER, which is the thing being measured.
     * The `break` after a match stops scanning one plugin's dependency list.
       After flattening, a (dependent, dependency) pair occurs at most once,
       so at most one row matches per pair and the break has no effect on the
       answer.  It is dropped.
     * The source WRITES its answer back onto the plugin row
       (`setDependents`).  The output channel here is a list of strings, as in
       every other subject, so each plugin's two answers are reported as
       counts.  Under the source's `Set<String>` semantics those counts are
       the sizes of the two sets.
     * `plugins` arrives as an input list rather than a second table, because
       nothing indexes it: the join drives from it.
   ============================================================ *)

Definition dep_ty :=
  TRecord (record_sort
             [("dependent", TString); ("dependency", TString);
              ("optional", TBool); ("deleted", TBool)]).

Definition plugin_ty := TRecord (record_sort [("name", TString)]).

Section WithConcreteMaps.
  Notation value := (value).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* the inner loop, with the three guards in the order the source writes
     them: not itself, not deleted, and only then the join *)
  Definition inner (extra : expr -> expr) : expr :=
    EUnop OLength
      (EFlatmap LikeList (ELoc "deps") "d"
         (EIf (EUnop ONot (EBinop OEq (EAccess (EVar "d") "dependent")
                             (EAccess (EVar "p") "name")))
            (EIf (EUnop ONot (EAccess (EVar "d") "deleted"))
               (EIf (EBinop OEq (EAccess (EVar "d") "dependency")
                       (EAccess (EVar "p") "name"))
                  (extra (EBinop OCons (EVar "d") (EAtom (ANil None))))
                  (EAtom (ANil None)))
               (EAtom (ANil None)))
            (EAtom (ANil None)))).

  Definition dependents : expr := inner (fun keep => keep).

  (* and the optional ones, which the source collects in the same pass *)
  Definition optional_dependents : expr :=
    inner (fun keep => EIf (EAccess (EVar "d") "optional") keep (EAtom (ANil None))).

  Definition report (e : expr) : scommand :=
    SLet e "n"
      (SAssign "outputs"
         (EBinop OCons (EUnop OIntToString (EVar "n")) (ELoc "outputs")) SSkip).

  (* One query is one resolveDependentPlugins(): the whole loop over every
     plugin, which is what the source's one public method does. *)
  Definition prog_s : scommand :=
    SLetMut (EVar "deps_tbl") "deps"
      (SForeach (EVar "queries") "q"
         (SForeach (EVar "plugins_tbl") "p"
            (SSeq (report dependents) (report optional_dependents)))).

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put (map.put (map.put map.empty "deps_tbl" (TList dep_ty))
               "plugins_tbl" (TList plugin_ty))
      "queries" (TList TInt).

  Definition elaborated : command :=
    elab [] (get_free_vars init_Genv) prog_s.

  (* ---- what the selector does with it, computed and not predicted ---- *)

  Definition sel_basics : list basic_transf := select_basics [] "deps" elaborated.
  Definition sel_choices : list index_choice := select_choices [] "deps" elaborated.

  Definition selected : command :=
    apply_optimize_anno (AC sel_basics [sel_choices] elaborated)
      init_Gstore init_Genv.

  (* ---- and the configurations that DO serve it ----

     Two of them, because the difference between them is the limit.

     SwapFlatmapIf cannot help here: it hoists a guard that does not mention
     the loop variable, and all three of these guards mention `d`.  With the
     index forced but the guards left alone, one of the two reads becomes a
     probe and the other does not.

     `SwapIfNil` can bring the equality to the front -- ONCE is enough here --
     and that is what `anno_swapped` does.  But it is UNCONDITIONAL, which is
     why `basics_of` does not emit it: applied twice it undoes itself, so
     there is no normal form to iterate to and the right count is found by
     hand.  Measured on this program, the counts that work are 1, 2 and 4 and
     the counts that fail are 0, 3 and 5 -- not monotone, because
     `fold_command` rotates every chain in the program at once.

     Both are kept as the comparison, because the selector's own
     configuration now beats them: `PromoteGuard` is AIMED, so it needs no
     count, and the demand that emits it is about guard position rather than
     about this program. *)

  Definition anno_hoist : anno_command :=
    AC [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap; SwapFlatmapIf;
        SplitIf]
      [[DictIdx "dependency"]] elaborated.

  Definition optimized_hoist : command :=
    apply_optimize_anno anno_hoist init_Gstore init_Genv.

  Definition anno_swapped : anno_command :=
    AC [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap; SwapIfNil]
      [[DictIdx "dependency"]] elaborated.

  Definition optimized_swapped : command :=
    apply_optimize_anno anno_swapped init_Gstore init_Genv.

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  (* ---- soundness: both configurations compute what the source computes ---- *)

  Lemma dep_ty_wf : type_wf dep_ty.
  Proof. unfold dep_ty. repeat constructor; cbn; intuition congruence. Qed.

  Lemma plugin_ty_wf : type_wf plugin_ty.
  Proof. unfold plugin_ty. repeat constructor; cbn; intuition congruence. Qed.

  Lemma init_Gstore_wf : tenv_wf init_Gstore.
  Proof.
    unfold init_Gstore.
    apply tenv_wf_step; [ apply tenv_wf_empty | repeat constructor ].
  Qed.

  Lemma init_Genv_wf : tenv_wf init_Genv.
  Proof.
    unfold init_Genv.
    apply tenv_wf_step;
      [ apply tenv_wf_step;
        [ apply tenv_wf_step;
          [ apply tenv_wf_empty | constructor; apply dep_ty_wf ]
        | constructor; apply plugin_ty_wf ]
      | repeat constructor ].
  Qed.

  Lemma elaborated_well_typed :
    well_typed init_Gstore init_Genv elaborated.
  Proof.
    eapply command_typechecker_sound with (c := elaborated).
    1: apply init_Gstore_wf.
    1: apply init_Genv_wf.
    reflexivity.
  Qed.

  (* ------------------------------------------------------------------
     What the pipeline produced.  Probes are counted because this subject is
     about WHETHER the join is indexed at all; what it costs is measured in
     the harness, not here. *)

  Fixpoint probes_e (e : expr) : nat :=
    match e with
    | EBinop OLookup a b => S (Nat.add (probes_e a) (probes_e b))
    | EBinop _ a b => Nat.add (probes_e a) (probes_e b)
    | EUnop _ a => probes_e a
    | ETernop _ a b c => Nat.add (probes_e a) (Nat.add (probes_e b) (probes_e c))
    | EIf a b c => Nat.add (probes_e a) (Nat.add (probes_e b) (probes_e c))
    | ELet a _ b => Nat.add (probes_e a) (probes_e b)
    | EFlatmap _ a _ b => Nat.add (probes_e a) (probes_e b)
    | EFold a b _ _ c => Nat.add (probes_e a) (Nat.add (probes_e b) (probes_e c))
    | EACFold _ a | EACIFold _ a => probes_e a
    | EAccess a _ => probes_e a
    | EOptMatch a b _ c => Nat.add (probes_e a) (Nat.add (probes_e b) (probes_e c))
    | ESort _ a | EBagOf a | ESetOf a => probes_e a
    | ERecord l => fold_right (fun q acc => Nat.add (probes_e (snd q)) acc) O l
    | _ => O
    end.

  Fixpoint probes (c : command) : nat :=
    match c with
    | CSkip => O
    | CSeq a b => Nat.add (probes a) (probes b)
    | CLet e _ c | CLetMut e _ c => Nat.add (probes_e e) (probes c)
    | CAssign _ e => probes_e e
    | CIf e a b => Nat.add (probes_e e) (Nat.add (probes a) (probes b))
    | CForeach e _ c => Nat.add (probes_e e) (probes c)
    end.

  (* THE LIMIT, on real code.  The demand analysis finds NOTHING on this
     program -- not the equality, not a shape to normalise -- so the selector
     asks for no index and the join stays two nested scans. *)
  (* COUNTING PROBES HONESTLY.  A plain count of OLookup conflates two
     different things: a probe of the installed MEMBER, which is a read made
     cheap, and a probe of a fold's own ACCUMULATOR, which is the bucketed
     dictionary being BUILT and is not a read at all.  Every configuration
     here installs the same index, so every one carries exactly one build
     probe, and comparing raw counts across them overstates each by one.

     The distinction is load-bearing, not pedantic.  On a raw count of two,
     `optimized_swapped` reads as though it served both of this program's two
     reads; one of those two is the build, so it serves ONE.  The raw counts
     are pinned below beside the read counts so that the two metrics cannot
     be confused again. *)
  Definition is_member_probe (e : expr) : bool :=
    match e with
    | EBinop OLookup (EAccess (EAccess (ELoc _) _) _) _ => true
    | _ => false
    end.

  Fixpoint read_probes_e (e : expr) : nat :=
    Nat.add (if is_member_probe e then 1 else 0)
      (match e with
       | EBinop _ a b => Nat.add (read_probes_e a) (read_probes_e b)
       | EUnop _ a => read_probes_e a
       | ETernop _ a b c =>
           Nat.add (read_probes_e a) (Nat.add (read_probes_e b) (read_probes_e c))
       | EIf a b c =>
           Nat.add (read_probes_e a) (Nat.add (read_probes_e b) (read_probes_e c))
       | ELet a _ b => Nat.add (read_probes_e a) (read_probes_e b)
       | EFlatmap _ a _ b => Nat.add (read_probes_e a) (read_probes_e b)
       | EFold a b _ _ c =>
           Nat.add (read_probes_e a) (Nat.add (read_probes_e b) (read_probes_e c))
       | EACFold _ a | EACIFold _ a => read_probes_e a
       | EAccess a _ => read_probes_e a
       | EOptMatch a b _ c =>
           Nat.add (read_probes_e a) (Nat.add (read_probes_e b) (read_probes_e c))
       | ESort _ a | EBagOf a | ESetOf a => read_probes_e a
       | ERecord l =>
           fold_right (fun q acc => Nat.add (read_probes_e (snd q)) acc) O l
       | _ => O
       end).

  Fixpoint read_probes (c : command) : nat :=
    match c with
    | CSkip => O
    | CSeq a b => Nat.add (read_probes a) (read_probes b)
    | CLet e _ c | CLetMut e _ c => Nat.add (read_probes_e e) (read_probes c)
    | CAssign _ e => read_probes_e e
    | CIf e a b => Nat.add (read_probes_e e) (Nat.add (read_probes a) (read_probes b))
    | CForeach e _ c => Nat.add (read_probes_e e) (read_probes c)
    end.

  (* WHAT THE SELECTOR REACHES.  It sees that this loop's indexable guard is
     not its outermost one, asks for the promotion by position, and the
     second analysis -- which always handled a head-position equality -- then
     finds the key. *)
  Lemma selector_demands_the_promotion :
    Selector.demands_of "deps" elaborated = [DPromote "dependency"].
  Proof. vm_compute; reflexivity. Qed.

  Lemma selector_emits_the_promotion :
    sel_basics = [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap;
                  PromoteGuard "dependency"].
  Proof. vm_compute; reflexivity. Qed.

  Lemma selector_asks_for_the_key : sel_choices = [DictIdx "dependency"].
  Proof. vm_compute; reflexivity. Qed.

  (* This program has TWO reads.  The selector serves both of them; the two
     hand-written configurations serve one and none.  And it erases the list,
     which neither of them does. *)
  Lemma selector_serves_both_reads : read_probes selected = 2%nat.
  Proof. vm_compute; reflexivity. Qed.

  Lemma transposition_serves_one_read : read_probes optimized_swapped = 1%nat.
  Proof. vm_compute; reflexivity. Qed.

  Lemma hoisting_serves_neither_read : read_probes optimized_hoist = 0%nat.
  Proof. vm_compute; reflexivity. Qed.

  (* and the raw counts, so the difference between the two metrics is on the
     record rather than in a commit message: each is one higher, and the one
     is the index build *)
  Lemma raw_counts_are_one_higher :
    probes selected = 3%nat /\ probes optimized_swapped = 2%nat
    /\ probes optimized_hoist = 1%nat.
  Proof. repeat split; vm_compute; reflexivity. Qed.

  Lemma selector_erases_the_list : installed_fields selected = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  Lemma hand_written_keep_the_list :
    installed_fields optimized_hoist = ["id_tag"; "aux_tag"]
    /\ installed_fields optimized_swapped = ["id_tag"; "aux_tag"].
  Proof. split; vm_compute; reflexivity. Qed.



  Theorem optimized_hoist_sound : forall (store env : clocals),
      locals_wf init_Gstore store -> locals_wf init_Genv env ->
      interp_command store env optimized_hoist = interp_command store env elaborated.
  Proof.
    unfold optimized_hoist, anno_hoist, apply_optimize_anno; intros.
    eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
  Qed.

  Theorem optimized_swapped_sound : forall (store env : clocals),
      locals_wf init_Gstore store -> locals_wf init_Genv env ->
      interp_command store env optimized_swapped = interp_command store env elaborated.
  Proof.
    unfold optimized_swapped, anno_swapped, apply_optimize_anno; intros.
    eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
  Qed.

  Theorem selected_sound : forall (store env : clocals),
      locals_wf init_Gstore store -> locals_wf init_Genv env ->
      interp_command store env selected = interp_command store env elaborated.
  Proof.
    unfold selected, apply_optimize_anno; intros.
    eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
  Qed.
End WithConcreteMaps.
