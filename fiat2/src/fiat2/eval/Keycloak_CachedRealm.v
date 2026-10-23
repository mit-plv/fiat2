Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.FlatmapForms fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   Source
     keycloak, commit dd4ae31d1b67c91a7f85f7c60df5c9718b111f0a
     model/infinispan/src/main/java/org/keycloak/models/cache/infinispan/
       entities/CachedRealm.java:301
     reads at .../infinispan/RealmAdapter.java:1572 and :1579

       requiredActionProviderList = model.getRequiredActionProvidersStream()
                                         .collect(Collectors.toList());
       for (RequiredActionProviderModel action : requiredActionProviderList) {
           requiredActionProviders.put(action.getId(), action);
           requiredActionProvidersByAlias.put(action.getAlias(), action);
       }

     One list, two maps over it, keyed on two different unique attributes.  The
     callers resolve to exactly two point lookups:
       getRequiredActionProviderById(id)       -> ...getRequiredActionProviders().get(id)
       getRequiredActionProviderByAlias(alias) -> ...ByAlias().get(alias)
     and getRequiredActionProviderList() hands back the list itself.

   Pattern
     A1a, built once, multi-index.  The same shape occurs a second time in the
     same class, at :295, for requiredActionProviderConfigs -- so it is the
     class's idiom rather than a one-off.

   Claim
     C4, chiefly: the programmer built and maintained by hand two structures
     that the optimizer derives from the scan form.  C1 secondarily: both keys
     are unique, and it is uniqueness that makes a single-row lookup sound
     where a bucketed index would not be.

   Faithfulness -- what this translation drops, and why
     * RequiredActionProviderModel carries providerId, enabled, defaultAction,
       priority and a config map.  Only id, alias and name are kept: the others
       are never used as keys and never read by the two callers above.
     * Java hands the caller a whole Map and the caller calls .get.  Conquord
       has no map-valued expression, so the two getters are written here as the
       queries their callers actually perform -- which is the honest comparison
       anyway, since the point is that the SOURCE need not mention an index.
     * Keycloak builds the structure once in a constructor and never mutates
       it.  An insert is included here so that the declared keys have something
       to be checked against; Keycloak checks nothing, because the upstream
       model guarantees uniqueness.  This is the one place the translation adds
       rather than drops, and it is marked in the program below.
     * The Java reads return the model or null.  The output channel here is a
       list of strings, so each read is counted; under a declared unique key
       that count is 0 or 1.

     * The added insert prepends the row.  The source puts into two maps, so
       it names no position, and nothing here observes row order -- see the
       note on row order in this directory's README.
   Expected
     Both scans become single-row probes into the two declared members, and the
     list survives, because getRequiredActionProviderList() still reads it --
     matching Keycloak, which keeps requiredActionProviderList alongside both
     maps.

     A second configuration adds the maintained row count, and with it the
     list's one remaining reader becomes a field read, so the list is erased.
     Both are pinned.  Which of the two to prefer is a question about the
     program and not about soundness: Keycloak hands the list itself back to
     its callers, and this translation narrows that read to its length (see
     Faithfulness), so the erasure is honest here and would not be if the
     caller really needed the rows.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort [("id", TString); ("alias", TString); ("name", TString)]).

Definition query_ty :=
  TRecord (record_sort [("kind", TInt); ("k", TString); ("new_action", row_ty)]).

Section WithConcreteMaps.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* [a <- bag(actions), check(a.attr = q.k), ret a] -- the scan a programmer
     writes when the language offers no index. *)
  Definition lookup_by (attr : string) : expr :=
    EACFold AGCount
      (EFlatmap LikeBag (EBagOf (ELoc "actions")) "a"
         (EIf (EBinop OEq (EAccess (EVar "a") attr) (EAccess (EVar "q") "k"))
            (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "a"))
            (EAtom (AEmptyBag None)))).

  Definition report (e : expr) : scommand :=
    SLet e "n"
      (SAssign "outputs"
         (EBinop OCons (EUnop OIntToString (EVar "n")) (ELoc "outputs")) SSkip).

  Definition prog_s (ds : list decl) : scommand :=
    SLetConstrained "actions" row_ty ds
      (SForeach (EVar "queries") "q"
         (SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt 0)))
            (* the added write; see Faithfulness above *)
            (SAssign "actions"
               (EBinop OCons (EAccess (EVar "q") "new_action") (ELoc "actions")) SSkip)
            (SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt 1)))
               (report (lookup_by "id"))
               (SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt 2)))
                  (report (lookup_by "alias"))
                  (* getRequiredActionProviderList(): the whole list, which is
                     why Keycloak keeps it beside both maps *)
                  (report (EACFold AGCount (EBagOf (ELoc "actions")))))))).

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put map.empty "queries" (TList query_ty).

  Definition elaborated (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_s ds).

  Definition decls := [DUnique "id"; DUnique "alias"].

  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  (* Both declared keys, as one two-member index on the one table. *)
  Definition anno : canno_command :=
    CAC (("actions", (row_ty, decls)) :: cenv_rm "actions" []) O
      basics [UniqueDictIdx "id"; UniqueDictIdx "alias"] [] (elaborated decls).

  Definition optimized : command :=
    apply_optimize_anno_constrained (width:=width) anno init_Gstore init_Genv.

  (* A second configuration, adding the maintained row count.  The only read
     this example had left on the list is a whole-table count, so this is the
     choice that decides whether the list survives.  CountAgg is listed last,
     so it runs first; whether that matters is measured below, not assumed. *)
  Definition anno_counted : canno_command :=
    CAC (("actions", (row_ty, decls)) :: cenv_rm "actions" []) O
      basics [UniqueDictIdx "id"; UniqueDictIdx "alias"; CountAgg] [] (elaborated decls).

  Definition optimized_counted : command :=
    apply_optimize_anno_constrained (width:=width) anno_counted init_Gstore init_Genv.

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  (* ------------------------------------------------------------------
     What the pipeline produced.

     Every claim below is an equality of closed terms under a small
     projection, so it reduces by computation and can be read as a diff
     against the source program above. *)

  (* a member of the installed index record *)
  Definition member (i : string) : expr :=
    EAccess (EAccess (ELoc "actions") "aux_tag") i.

  (* a lookup that yields the one row under the key, or no row: the shape a
     probe has when the key is declared unique *)
  Definition probe (idx k : expr) : expr :=
    EOptMatch (EBinop OLookup idx k)
      (EAtom (AEmptyBag None)) "y"
      (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "y")).

  Definition row_list_ty : type :=
    TRecord [("alias", TString); ("id", TString); ("name", TString)].

  (* ---- the installation ---- *)

  Definition build (attr : string) : expr :=
    EFold (EAtom (ANil (Some row_list_ty)))
      (EAtom (AEmptyDict Unranged None)) "tup" "acc"
      (ETernop OInsert (EVar "acc") (EAccess (EVar "tup") attr) (EVar "tup")).

  Definition install_expected : expr :=
    ERecord
      [("id_tag", EAtom (ANil (Some row_list_ty)));
       ("aux_tag", ERecord [("0", build "id"); ("1", build "alias")])].

  Definition install_of (c : command) : option expr :=
    match c with
    | CLetMut e _ _ => Some e
    | _ => None
    end.

  (* Two declarations, two members, each keyed on its own attribute -- the
     two maps of CachedRealm.java:301-304, derived rather than written.  A
     point lookup needs no ordering, so both ask a backend for a hash table. *)
  Lemma installs_both_maps : install_of optimized = Some install_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* And the list stays beside them, because getRequiredActionProviderList()
     still reads it.  This is the comparison with Keycloak that matters: it
     keeps requiredActionProviderList for the same reason. *)
  Lemma keeps_the_list :
    installed_fields optimized = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ---- the two reads ---- *)

  Definition count_probe (i : string) : expr :=
    EACFold AGCount (probe (member i) (EAccess (EVar "q") "k")).

  Definition read_by_id (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ (CLet e _ _) _))) => Some e
    | _ => None
    end.

  Definition read_by_alias (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CIf _ (CLet e _ _) _)))) => Some e
    | _ => None
    end.

  Definition read_list (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CIf _ _ (CLet e _ _))))) => Some e
    | _ => None
    end.

  (* getRequiredActionProviderById: the scan became a probe into member 0. *)
  Lemma id_read_is_a_probe : read_by_id optimized = Some (count_probe "0").
  Proof. vm_compute; reflexivity. Qed.

  (* getRequiredActionProviderByAlias: the same, into member 1.  The two
     queries differ in the source only by the attribute they compare, and the
     rule sends each to the member declared on that attribute. *)
  Lemma alias_read_is_a_probe : read_by_alias optimized = Some (count_probe "1").
  Proof. vm_compute; reflexivity. Qed.

  (* getRequiredActionProviderList: untouched, and the reason the list lives. *)
  Lemma list_read_is_the_list :
    read_list optimized
    = Some (EACFold AGCount (EBagOf (EAccess (ELoc "actions") "id_tag"))).
  Proof. vm_compute; reflexivity. Qed.

  (* ---- and the same program with the count maintained ---- *)

  (* getRequiredActionProviderList(): the one read still on the list becomes a
     field read of member 2. *)
  Lemma counted_list_read_is_a_field :
    read_list optimized_counted
    = Some (EAccess (EAccess (ELoc "actions") "aux_tag") "2").
  Proof. vm_compute; reflexivity. Qed.

  (* And then nothing reads the list at all, so the erasure pass drops it.
     Read against keeps_the_list above: the same program, one more choice, and
     the opposite answer about the list -- because this example kept its list
     for exactly one reason and the count is that reason. *)
  Lemma counted_erases_the_list :
    installed_fields optimized_counted = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* And the two declared-key probes are untouched.  CountAgg is listed last,
     so it runs FIRST, and the hazard of a rule eating another's read does not
     materialise here: its pattern wants the table read directly under the
     count, so the filter the dict rules are after blocks it. *)
  Lemma counted_id_read_is_still_a_probe :
    read_by_id optimized_counted = Some (count_probe "0").
  Proof. vm_compute; reflexivity. Qed.

  Lemma counted_alias_read_is_still_a_probe :
    read_by_alias optimized_counted = Some (count_probe "1").
  Proof. vm_compute; reflexivity. Qed.

  (* ---- the write ---- *)

  (* the uniqueness check elaboration emits for one declared key *)
  Definition key_free (i attr : string) : expr :=
    ELet (EAccess (EVar "q") "new_action") "_pk_row"
      (EBinop OEq (probe (member i) (EAccess (EVar "_pk_row") attr))
         (EAtom (AEmptyBag None))).

  Definition guard_expected : expr :=
    EBinop OAnd (key_free "0" "id")
      (EBinop OAnd (key_free "1" "alias") (EAtom (ABool true))).

  Definition write_guard (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ (CIf g _ _) _)) => Some g
    | _ => None
    end.

  (* Both checks are probes.  The guard is what this translation adds to
     Keycloak (see Faithfulness above); the point here is only that a declared
     key costs a lookup rather than a scan of the table. *)
  Lemma guard_is_two_probes : write_guard optimized = Some guard_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* the maintenance of one member on an insert *)
  Definition add_to (i attr : string) : expr :=
    ELet (member i) "acc"
      (ELet (EAccess (EVar "q") "new_action") "tup"
         (ETernop OInsert (EVar "acc") (EAccess (EVar "tup") attr) (EVar "tup"))).

  Definition write_expected : expr :=
    ERecord
      [("id_tag", EBinop OCons (EAccess (EVar "q") "new_action")
                    (EAccess (ELoc "actions") "id_tag"));
       ("aux_tag", ERecord [("0", add_to "0" "id"); ("1", add_to "1" "alias")])].

  Definition write_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ (CIf _ (CAssign _ e) _) _)) => Some e
    | _ => None
    end.

  (* Neither member is rebuilt: each takes one OInsert at its own key.  This
     is the half Keycloak never writes, because it never mutates. *)
  Lemma write_is_incremental : write_of optimized = Some write_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     And all of it is sound: the program above computes what the scan form
     computes, on every store and environment. *)

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

  (* Both declarations name a field of the row type.  That is all uniqueness
     has to check, and it is decidable. *)
  Lemma decls_wf : Forall (decl_wf (tenv:=ctenv) row_ty) decls.
  Proof.
    unfold decls, row_ty; cbn [decl_wf].
    repeat constructor;
      exists [("alias", TString); ("id", TString); ("name", TString)], TString;
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
