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
     A nested-loop equijoin, which the corpus search in corpus/joins found by
     looking for exactly this shape and then reading every candidate.  Of the
     survivors this is the one whose cost is most clearly quadratic in state
     the program keeps, which is why it is the one written up.

   Claim
     C4, and more sharply than elsewhere: the author wrote the join as two
     nested loops and there is no structure here at all, derived or
     hand-built.  What the optimizer offers is the dictionary that turns the
     inner loop into a probe.

   THE GUARD ORDER IS THE POINT, AND IT IS NOT IN OUR FAVOUR
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
     recorded as having NO witness in the corpus.  It has one now, and this
     file is it.  What the selector actually does with this program is
     computed below rather than asserted, and the configuration that would
     serve it is pinned beside it so the gap is the difference between two
     terms rather than a sentence.

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
       (`setDependents`).  Our output channel is a list of strings, as in
       every other subject here, so each plugin's two answers are reported as
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

     The rule that reaches both is `SwapIfNil`, which transposes two adjacent
     nil-guards and so can bring the equality to the front -- ONCE is enough
     here.  It is UNCONDITIONAL, which is why `basics_of` does not emit it at
     all: applied twice it undoes itself, so there is no normal form to
     iterate to and the right number of applications is found by hand.  That
     is the whole of the gap, on this program. *)

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
  Lemma selector_finds_no_demand :
    Selector.demands_of "deps" elaborated = [].
  Proof. vm_compute; reflexivity. Qed.

  Lemma selector_asks_for_no_index : sel_choices = [].
  Proof. vm_compute; reflexivity. Qed.

  Lemma selector_reaches_no_probe : probes selected = 0%nat.
  Proof. vm_compute; reflexivity. Qed.

  (* with the index supplied by hand but the guards left in source order, one
     of the two reads is served *)
  Lemma hoisting_alone_reaches_one_probe : probes optimized_hoist = 1%nat.
  Proof. vm_compute; reflexivity. Qed.

  (* and one transposition reaches both *)
  Lemma one_transposition_reaches_both : probes optimized_swapped = 2%nat.
  Proof. vm_compute; reflexivity. Qed.

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
