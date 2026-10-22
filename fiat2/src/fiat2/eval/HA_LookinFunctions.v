Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.FlatmapForms fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   Source
     home-assistant/core, commit e751cd2b
     homeassistant/components/lookin/entity.py:91-94 (LookinEntityMixIn)

       self._device = device
       self._function_names = {function.name for function in self._device.functions}

     and every read of it -- there are four, and all four are membership
     tests:

       media_player.py:86-88   for function_name, feature in _FUNCTION_NAME_TO_FEATURE.items():
                                   if function_name in self._function_names:
                                       self._attr_supported_features |= feature
       media_player.py:107     if self._source_list is None and "mode" in self._function_names:
       entity.py:152           if POWER_ON_CMD in self._function_names:
       entity.py:154           if POWER_OFF_CMD in self._function_names:

     A list of remote-control functions, and a SET of their names derived from
     it.  The programmer chose a set -- not a list, not a map -- because
     neither multiplicity nor order of the names is ever observed: the only
     question asked of the structure is whether a name is present.

     And the list does not survive the derivation.  `self._device` is written
     at :91 and read ONLY at :94, to build the set; nothing else in the
     component touches it.

   Pattern
     D1 multiplicity discarded, with a hand-written witness.  B3 membership
     scan.  B5 (N+1) as well: the first read is a membership test inside a
     loop over the eight constant keys of _FUNCTION_NAME_TO_FEATURE
     (media_player.py:30-39), so without the set each iteration is a scan.

   Claim
     C1, in the pairing the other eval files do not exercise: no constraint is
     declared here, and what licenses the rewrite is the COLLECTION
     INTERPRETATION -- the query observes neither order nor multiplicity, so
     the set level is available, and at the set level a membership test is a
     probe.  Keycloak_CachedRealm and HA_AreaRegistry both demonstrate the
     other pairing, where a declared uniqueness licenses an index rule.

     C3 and C4 secondarily: the structure the optimizer derives is the one the
     programmer built by hand, and the list is erased because nothing reads
     it.

   Faithfulness -- what this translation drops, and why
     * `device.functions` is typed in the external `aiolookin` package, which
       is not vendored.  The component reads only `.name`, so the row is
       modelled as that one field; whatever else a Function carries is never
       read here.  The derivation and all four reads are Home Assistant's.
     * The set is built once per entity and the function list does not change
       during the entity's life, so this is A1a built-once, as in
       Keycloak_CachedRealm and Kafka_Cluster.  There is no write.  The
       write-side evidence is HA_AreaRegistry's.
     * POWER_ON_CMD and POWER_OFF_CMD are string constants from aiolookin, so
       those two reads probe at a literal.  The loop at media_player.py:86-88
       probes at a key that varies, which is the `q.k` case below; the two
       shapes are kept separate because only the second is an N+1.
     * Each read decides something in its then-branch -- a feature flag, a
       command name.  The output channel here is a list of strings, as in the
       other three files, so each branch reports which way it went.  Nothing
       downstream of the decision is modelled.
     * FilterEmptyToSetMem is enabled here.  It must NOT be enabled on a table
       that also carries a unique-dict member -- it would rewrite the
       emptiness test before the index rule could make it a probe, turning a
       probe into a scan.  This table declares nothing, so the hazard does not
       arise.
     * Nothing is added.

   Expected
     The set of names is installed as the one member; both membership tests
     become probes into it; and the list is erased, because after the rewrite
     nothing reads it -- which is what the source does too.

     One wart, pinned rather than hidden: each probe comes out under a double
     negation.  The source asks `k in names`, which with no index is "the
     filter is NOT empty", and FilterEmptyToSetMem rewrites an emptiness test
     to a NEGATED membership -- so the two negations compose and no peephole
     collapses them.  `not (not (set_mem s k))` is still one probe; what is
     missing is a one-line simplification rule, not an index.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort [("name", TString)]).

Definition query_ty :=
  TRecord (record_sort [("kind", TInt); ("k", TString)]).

Section WithConcreteMaps.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* `k in function_names`, as a programmer writes it with no index: is the
     bag of rows whose name is k empty?  This is the scan form -- O(n) per
     test, and the loop at media_player.py:86-88 runs it eight times. *)
  Definition has_function (k : expr) : expr :=
    EUnop ONot
      (EBinop OEq
         (EFlatmap LikeBag (EBagOf (ELoc "functions")) "f"
            (EIf (EBinop OEq (EAccess (EVar "f") "name") k)
               (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "f"))
               (EAtom (AEmptyBag None))))
         (EAtom (AEmptyBag None))).

  Definition say (s : string) : scommand :=
    SAssign "outputs" (EBinop OCons (EAtom (AString s)) (ELoc "outputs")) SSkip.

  Definition prog_s (ds : list decl) : scommand :=
    SLetConstrained "functions" row_ty ds
      (SForeach (EVar "queries") "q"
         (SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt 0)))
            (* media_player.py:86-88 -- the key varies with the iteration *)
            (SIf (has_function (EAccess (EVar "q") "k"))
               (say "supported") (say "unsupported"))
            (* media_player.py:107 -- the key is a literal *)
            (SIf (has_function (EAtom (AString "mode")))
               (say "has-mode") (say "no-mode")))).

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put map.empty "queries" (TList query_ty).

  Definition elaborated (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_s ds).

  (* Nothing is declared.  That is the point: the rewrite here is licensed by
     what the queries observe, not by a constraint on the state. *)
  Definition decls : list decl := [].

  (* FilterEmptyToSetMem first in the list, so it runs LAST
     (compose_basic_transfs is a fold_right): it has to see the bag-level
     filter the push-down leaves behind. *)
  Definition basics : list basic_transf :=
    [FilterEmptyToSetMem; PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition anno : canno_command :=
    CAC (("functions", (row_ty, decls)) :: cenv_rm "functions" []) O
      basics [SetAgg "name"] [] (elaborated decls).

  Definition optimized : command :=
    apply_optimize_anno_constrained (width:=width) anno init_Gstore init_Genv.

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  Definition install_of (c : command) : option expr :=
    match c with
    | CLetMut e _ _ => Some e
    | _ => None
    end.

  Definition read_varying (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ (CIf g _ _) _)) => Some g
    | _ => None
    end.

  Definition read_literal (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf g _ _))) => Some g
    | _ => None
    end.

  Definition empty_rows : expr := EAtom (ANil (Some row_ty)).

  (* the index: the set of the values `name` takes over the table *)
  Definition name_set (src : expr) : expr :=
    flatmap_proj_set (ESetOf src) "x" (EAccess (EVar "x") "name") None.

  Definition install_expected : expr :=
    ERecord [("aux_tag", ERecord [("0", name_set empty_rows)])].

  Definition member0 : expr :=
    EAccess (EAccess (ELoc "functions") "aux_tag") "0".

  (* see Expected: the double negation is the source's `any` composed with
     the rule's negative form *)
  Definition probe (k : expr) : expr :=
    EUnop ONot (EUnop ONot (EBinop OSetMem member0 k)).

  (* ------------------------------------------------------------------
     What the pipeline produced. *)

  (* The structure the programmer wrote by hand, derived: a set of the names,
     and nothing else.  No declaration was needed to get it -- what makes the
     set level available is that no query observes order or multiplicity. *)
  Lemma installs_the_name_set : install_of optimized = Some install_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* And the list is gone.  `self._device` is written and then read exactly
     once, to build the set; the optimizer reaches the same conclusion from
     the queries alone.  Contrast Keycloak_CachedRealm, where a getter reads
     the list and the same rule keeps it. *)
  Lemma erases_the_list : installed_fields optimized = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* media_player.py:86-88, the N+1: the scan inside the loop over the eight
     constant keys becomes one probe per iteration. *)
  Lemma varying_read_is_a_probe :
    read_varying optimized = Some (probe (EAccess (EVar "q") "k")).
  Proof. vm_compute; reflexivity. Qed.

  (* media_player.py:107, the same rewrite at a literal key. *)
  Lemma literal_read_is_a_probe :
    read_literal optimized = Some (probe (EAtom (AString "mode"))).
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
    unfold query_ty. repeat constructor; cbn; intuition congruence.
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

  (* Nothing is declared, so there is nothing to check. *)
  Lemma decls_wf : Forall (decl_wf (tenv:=ctenv) row_ty) decls.
  Proof. unfold decls; apply Forall_nil. Qed.

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
