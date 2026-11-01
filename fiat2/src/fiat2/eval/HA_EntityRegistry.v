Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.CollectionTransf fiat2.DictIndexImpl
  fiat2.TransfUtils fiat2.FlatmapTransf fiat2.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString
  coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   Source
     home-assistant/core, commit e751cd2b
     homeassistant/helpers/entity_registry.py:982 (class EntityRegistryItems)
     the index at :1007, its maintenance at :1015 and :1035, and the three
     readers at :1062, :1070 and :1074

       self._entry_ids: dict[str, RegistryEntry] = {}
       self._index: dict[tuple[str, str, str], str] = {}
       self._device_id_index: RegistryIndexType = defaultdict(dict)
       ...
       def _index_entry(self, key, entry):
           self._entry_ids[entry.id] = entry
           self._index[(entry.domain, entry.platform, entry.unique_id)] = entry.entity_id
           ...
       def get_entity_id(self, key: tuple[str, str, str]) -> str | None:
           return self._index.get(key)

     THE REASON THIS FILE EXISTS.  `self._index` is keyed on a THREE-tuple,
     built by hand, and read by one accessor -- async_get_entity_id(domain,
     platform, unique_id) at :1264, used at :1486 to decide whether an entity
     is already registered and at :1986 to reject a unique-id collision.  It
     is the arity-three witness for the composite-key index: the key Kafka
     builds in eval/Kafka_Cluster has two attributes, and two is the arity a
     fixed pattern can still be written out by hand.  Three cannot, which is
     what makes this subject a test of the index and not a second instance of
     it.

     TWO THINGS TO READ IN THE TERMS BELOW, both consequences of the index
     being n-ary rather than binary.

     First, the conjunction in the source is RIGHT-NESTED -- `dom && (plat &&
     uid)` -- and the rule matches it anyway, because its matcher collects the
     conjuncts of an arbitrary tree instead of matching a fixed one.  Nothing
     in the program was written to suit the rule.

     Second, and this is the difference from Kafka_Cluster: at arity three the
     composite index REPLACES a single-attribute index rather than joining it.
     Kafka's composite key was a third member beside two others and cost 1.66x
     to build for a read that a split conjunction already served to within a
     constant.  Here the split conjunction needs an index on `domain` to probe
     with, and the composite index makes that index dead -- configuration 4
     installs the same NUMBER of members as configuration 0 and answers every
     read with one probe.  See the configuration table below.

   What it measured (harness alternatives, typed, 200/400/800/1600 rows;
   work at 1600 rows and the fitted exponent).  Configuration 4 is the CHOSEN
   column, because it is what the deterministic selector emits
   (eval/SelectorTests.ha_entity_registry), and every other row is against it:

                        build  getEntry forDevice getEntityId  register
     4 CHOSEN          323334      1268      1586        2540      6386
                       a=1.01    a=0.01   a=-0.00      a=0.01    a=0.00
     0 split + dicts   239297      1248      1566      116555      5434
                       a=1.01    a=0.01   a=-0.00      a=0.95    a=0.00
     1 unsplit, no cmp 239301      1248      1566     2450692      5794
                       a=1.01    a=0.01   a=-0.00      a=1.00    a=0.00
     2 cmp + dead dict 402364      1268      1586        2540      7970
                       a=1.01    a=0.01   a=-0.00      a=0.01    a=0.00
     3 cmp + split     402364      1268      1586      116575      7970
                       a=1.01    a=0.01   a=-0.00      a=0.95    a=0.00

   THE NUMBER TO READ IS THE EXPONENT, NOT THE RATIO.  Configuration 0 can
   probe only the first conjunct, so its read is one domain's bucket -- and a
   domain's bucket GROWS WITH THE TABLE, because the number of domains is a
   property of Home Assistant and not of the installation's size (see the
   note in harness/gen.ml).  So 0.95 is linear, and the composite key takes it
   to 0.01: 45.9x at 1600 rows and widening.  Against configuration 1, the
   pair that isolates the index, 965x.  This is where the composite key
   differs from eval/Kafka_Cluster, where the same index bought 2.8x and a
   constant because that generator's buckets are bounded by construction.

   WHAT THE CHOSEN COLUMN COSTS, stated against the configuration the
   selector used to emit: 1.35x on the build and 1.18x on each insert.  Both
   are constants and both are KEY WORK, not an extra structure -- a key that
   is a record of three strings costs about three comparisons where a string
   key costs one.  Configuration 4 installs THREE members, the same number as
   configuration 0, because the composite index REPLACES the dictionary on
   `domain` rather than joining it.  So the trade the selector takes is a
   constant on every write against an exponent on a read, which is the trade
   it takes everywhere else too.

   AND CONFIGURATION 2 IS WHY THE SUBSUMPTION MATTERS.  It is configuration 4
   plus the dictionary on `domain` that nothing reads any more: identical on
   all four operations, 1.2x on the build and 1.2x on each insert.  The
   selector does not emit it, and not by a rule about this program -- a read
   whose predicate is a composite conjunction yields DComposite and not DEq,
   so the single-attribute dictionary is emitted only where some other read
   asks for it independently.  Nothing here asks for `domain`.

   AND CONFIGURATION 3 IS THE HAZARD WITH A PRICE ON IT: configuration 0's
   reads at configuration 2's cost.  An index installed, maintained on every
   write, and never read.  The selector declines it for the general reason --
   a composite demand and a split demand on one table conflict, and the split
   wins -- which is what keeps eval/Kafka_Cluster out of this state.

   AND THE WRITE STAYS CONSTANT in every configuration: `register` is a=0.00,
   so the composite index is MAINTAINED and not rebuilt.  That takes two rules
   working as a pair -- the insert rule turns rebuilding the index of
   `row :: rest` into building the index of `rest` and inserting one row, and
   the use rule replaces that `index of rest` by the member already stored.
   Either alone leaves the O(n) rebuild it found; see
   insert_maintains_every_member for what the pair produces.

   Against the scan form the whole op phase is 4002998 work for the source and
   11780 for the chosen column, 340x, and EVERY read in the chosen column is
   flat -- getEntry 0.01, forDevice -0.01, getEntityId 0.01, register 0.01.

   Pattern
     A1a, built once, multi-index.  D4 composite key at arity three, served.
     Like Kafka_Cluster and unlike Keycloak_CachedRealm the keys are not
     unique on two of the three members, so each bucket is a bag of rows.

   Claim
     C3 and C4.  The optimizer reaches the author's own storage decision --
     three dictionaries, one of them keyed on a tuple -- from a program that
     names no index and writes its filter as an ordinary conjunction.

   Faithfulness -- what this translation drops, and why
     * RegistryEntry carries about thirty fields.  Six are kept: entity_id,
       id, domain, platform, unique_id, device_id.  Of the dropped ones only
       config_entry_id, area_id and labels are keys, and those three indexes
       are the ones left out -- config_entry_id and area_id because they are
       the same shape as device_id and would measure nothing new, labels
       because it keys on each element of a per-row collection, which is the
       gap identified in the 2026-10-19 survey and is not built.
     * device_id is `str | None`.  As in Kafka_Cluster and HA_AreaRegistry it
       is TOption here and the index is keyed by the option: HA's
       `if (device_id := entry.device_id) is not None` makes its index
       partial, whereas this one is total and the rows HA skips sit in a None
       bucket that no query probes.
     * get_entries_for_device_id also filters on `disabled_by` and, when the
       bucket is empty, resolves a pre-migration composite device id through
       the device registry.  Neither is modelled: the first is a residual
       predicate over the bucket this read already reaches, and the second
       consults a different registry.
     * `self._index` maps the tuple to an entity_id, and the primary dict then
       resolves that to the entry; this index stores the rows.  Both answer
       the same question from the same derived structure -- HA pays a second
       lookup per row, we pay the storage.  That choice is the backend's, not
       the rewrite's.  Same note as HA_AreaRegistry.
     * The reads return rows and here they are counted, as in the other files,
       because the output channel is a list of strings.
     * THE INSERT IS MODELLED AND THE DELETE IS NOT, and the reason is exact
       rather than general.  The composite index has BOTH maintenance rules,
       but its delete is stated on ITS OWN key -- remove the rows whose
       (domain, platform, unique_id) is this tuple -- and _unindex_entry
       removes by entity_id, dropping the tuple index's entry as a side
       effect.  Serving that needs the KEYED form: probe the primary member
       for the row, then drop it from the one bucket its composite key names,
       as DictIndexKeyedDelete does for a single attribute.  That rule does
       not exist for a composite key, so _unindex_entry is out of scope here;
       Ex_CompositeKey.v prices the delete the index DOES have, and
       HA_AreaRegistry carries this family's maintained keyed delete on
       single-attribute indexes.
     * The insert prepends the row.  The source stores into dicts keyed by
       entity_id and by the tuple, so it names no position in a sequence of
       rows, and nothing here observes row order -- see the note on row order
       in this directory's README.
     * Nothing else is added: the table is initialised from an input
       collection, as the registry's own loader does.

   Expected
     Three members installed off the input collection; get_entry and
     get_entries_for_device_id become probes in every configuration, because
     their filters were never conjunctions; and async_get_entity_id becomes
     ONE probe at a three-field record key exactly when the composite index is
     present and the conjunction has not been split.  Without the index the
     best available is a probe on one attribute and a residual filter on the
     other two; without the index AND without SplitIf it is a full scan, and
     then the row list survives because that scan reads it.

     The insert maintains every member incrementally -- one OInsert each, no
     rebuild -- and because nothing reads the row list any more the list is
     erased even though the program writes: the table IS its three indexes,
     across a write.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort
             [("entity_id", TString); ("id", TString); ("domain", TString);
              ("platform", TString); ("unique_id", TString);
              ("device_id", TOption TString)]).

Definition query_ty :=
  TRecord (record_sort
             [("kind", TInt); ("eid", TString); ("dom", TString);
              ("plat", TString); ("uid", TString); ("dev", TString);
              ("new_entry", row_ty)]).

Section WithConcreteMaps.

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string (value) := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* ---- the source program: three accessors, no index named ---- *)

  (* [e <- entries, check(pred), ret e], counted *)
  Definition filt (pred : expr) : expr :=
    EUnop OLength
      (EFlatmap LikeList (ELoc "entries") "e"
         (EIf pred (EBinop OCons (EVar "e") (EAtom (ANil None))) (EAtom (ANil None)))).

  Definition by_id : expr :=
    EBinop OEq (EAccess (EVar "e") "id") (EAccess (EVar "q") "eid").

  Definition by_device : expr :=
    EBinop OEq (EAccess (EVar "e") "device_id")
      (EUnop OSome (EAccess (EVar "q") "dev")).

  Definition by_domain : expr :=
    EBinop OEq (EAccess (EVar "e") "domain") (EAccess (EVar "q") "dom").
  Definition by_platform : expr :=
    EBinop OEq (EAccess (EVar "e") "platform") (EAccess (EVar "q") "plat").
  Definition by_unique : expr :=
    EBinop OEq (EAccess (EVar "e") "unique_id") (EAccess (EVar "q") "uid").

  (* the tuple key, as the conjunction it is -- and RIGHT-nested, which is
     the association a reader would write and not the one a binary rule
     would need.  The matcher collects conjuncts; association is free. *)
  Definition by_triple : expr :=
    EBinop OAnd by_domain (EBinop OAnd by_platform by_unique).

  Definition report (e : expr) : command :=
    CLet e "n"
      (CAssign "outputs"
         (EBinop OCons (EUnop OStringOfInt (EVar "n")) (ELoc "outputs"))).

  Definition dispatch (k : Z) (thn els : command) : command :=
    CIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt k))) thn els.

  Definition prog : command :=
    CLetMut (EVar "entries_tbl") "entries"
      (CForeach (EVar "queries") "q"
         (dispatch 0 (report (filt by_id))            (* get_entry (:1070) *)
            (dispatch 1 (report (filt by_device))     (* ...for_device_id (:1074) *)
               (dispatch 2 (report (filt by_triple))  (* get_entity_id (:1062) *)
                  (* _index_entry (:1015), reached by async_get_or_create *)
                  (CAssign "entries"
                     (EBinop OCons (EAccess (EVar "q") "new_entry")
                        (ELoc "entries"))))))).

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put (map.put map.empty "entries_tbl" (TList row_ty))
      "queries" (TList query_ty).

  (* ---- five configurations, of which 4 is the one the selector emits ----

     0  what the selector emitted BEFORE it could read a conjunction of
        equalities as one demand: SplitIf, and a dictionary per attribute.
        The triple read probes on `domain` and filters the rest.
     1  the same choices without SplitIf.  1 and 2 differ ONLY in the
        composite index, so that pair isolates it.
     2  the composite index ADDED to 1's three dictionaries.  The triple read
        becomes one probe -- and the `domain` dictionary becomes dead, which
        is what makes 4 strictly better than 2.
     3  configuration 2 with SplitIf, which is the ordering hazard: the
        composite index is installed and never read.
     4  THE CHOSEN ONE: the composite index INSTEAD OF the `domain`
        dictionary.  Three members, as in configuration 0, and every read a
        single probe. *)

  Definition triple := CompositeDictIdx ["domain"; "platform"; "unique_id"].

  (* The three single-attribute choices are listed in the order the
     deterministic selector emits them, so that configuration 0 IS the
     selector's own output -- eval/SelectorTests.ha_entity_registry. *)
  Definition dicts := [DictIdx "id"; DictIdx "device_id"; DictIdx "domain"].

  (* Every configuration shares the same basics and differs only in SplitIf
     and in the index list, so the table below compares one thing at a time.
     The basics are the ones the deterministic selector emits. *)
  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition heuristics :=
    [ AC (basics ++ [SplitIf]) [dicts]
    ; AC basics [dicts]
    ; AC basics [triple :: dicts]
    ; AC (basics ++ [SplitIf]) [triple :: dicts]
    ; AC basics [[triple; DictIdx "id"; DictIdx "device_id"]]
    ].

  Definition prog_transformed :=
    map (fun heu => apply_optimize_anno (heu prog) init_Gstore init_Genv)
      heuristics.

  (* ---- projections, so every claim is an equality of closed terms ---- *)

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

  (* the expression bound in the n-th arm of the dispatch chain *)
  Fixpoint branch (n : nat) (c : command) : option expr :=
    match n, c with
    | O, CIf _ (CLet e _ _) _ => Some e
    | O, CLet e _ _ => Some e
    | S n', CIf _ _ c' => branch n' c'
    | _, _ => None
    end.

  Definition query_at (n : nat) (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ b) => branch n b
    | _ => None
    end.

  Definition write_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CIf _ _ (CAssign _ e))))) =>
        Some e
    | _ => None
    end.

  (* ---- the expected output ---- *)

  (* one pass over the input collection, appending each row to its bucket.
     The key is an EXPRESSION over the row, which is the whole of what makes
     this index n-ary: a single attribute and a record of three are the same
     fold with a different key. *)
  Definition bucket_by (k : expr) : expr :=
    EFold (EVar "entries_tbl") (EAtom (AEmptyDict Unranged None)) "tup" "acc"
      (ETernop OInsert (EVar "acc") k
         (EBinop OBagInsert
            (EOptMatch (EBinop OLookup (EVar "acc") k)
               (EAtom (AEmptyBag None)) "x" (EVar "x"))
            (EVar "tup"))).

  Definition row_triple : expr :=
    ERecord [("domain", EAccess (EVar "tup") "domain");
             ("platform", EAccess (EVar "tup") "platform");
             ("unique_id", EAccess (EVar "tup") "unique_id")].

  Definition install_expected : expr :=
    ERecord [("aux_tag",
               ERecord [("0", bucket_by row_triple);
                        ("1", bucket_by (EAccess (EVar "tup") "id"));
                        ("2", bucket_by (EAccess (EVar "tup") "device_id"))])].

  Definition probe (i : string) (k : expr) : expr :=
    EOptMatch
      (EBinop OLookup (EAccess (EAccess (ELoc "entries") "aux_tag") i) k)
      (EAtom (AEmptyBag None)) "b" (EVar "b").

  (* a residual filter over whatever collection it is given *)
  Definition refine (src pred : expr) : expr :=
    EFlatmap LikeBag src "e"
      (EIf pred (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "e"))
         (EAtom (AEmptyBag None))).

  Definition scan (pred : expr) : expr :=
    refine (EUnop OBagOfList (EAccess (ELoc "entries") "id_tag")) pred.

  Definition dom_key : expr := EAccess (EVar "q") "dom".
  Definition rest_eq : expr := EBinop OAnd by_platform by_unique.

  (* the three-tuple key HA builds by hand, as a record literal.  Written in
     the order the index was declared; the stored key is record_sort's order,
     and the two agree because interp canonicalises an ERecord literal either
     way -- which is what makes a composite key an ordinary dictionary key at
     any arity. *)
  Definition triple_key : expr :=
    ERecord [("domain", EAccess (EVar "q") "dom");
             ("platform", EAccess (EVar "q") "plat");
             ("unique_id", EAccess (EVar "q") "uid")].

  (* ---- the program is well typed before anything is done to it ---- *)
  Definition is_success {A} (r : result A) : bool :=
    match r with Success _ => true | _ => false end.

  Lemma prog_typechecks :
    is_success (typecheck init_Gstore init_Genv prog) = true.
  Proof. vm_compute; reflexivity. Qed.

  (* ================= what each configuration stores ================= *)

  (* Configuration 1 is the only one that keeps the row list, and the reason
     is visible in get_entity_id_scans_unsplit below: its triple read is a
     scan, and a scan reads the list.  Every other configuration answers all
     three reads out of dictionaries, so the erasure rule drops the list and
     the table IS its indexes -- which is what EntityRegistryItems is, a
     UserDict whose `data` is one of the indexes rather than a list beside
     them. *)
  Lemma what_each_configuration_stores :
    List.map installed_fields prog_transformed
    = [["aux_tag"]; ["id_tag"; "aux_tag"]; ["aux_tag"]; ["aux_tag"];
       ["aux_tag"]].
  Proof. vm_compute; reflexivity. Qed.

  (* Configuration 4: three members, one of them keyed on a RECORD of three
     attributes -- the dict HA declares as dict[tuple[str, str, str], str]. *)
  Lemma installs_the_tuple_keyed_dict :
    install_of (nth 4 prog_transformed CSkip) = Some install_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* ================= the two single-attribute reads ================= *)

  (* get_entry(id) (:1070): the dict the _entry_ids field already is. *)
  Lemma get_entry_probes :
    query_at 0 (nth 4 prog_transformed CSkip)
    = Some (EACFold AGCount (probe "1" (EAccess (EVar "q") "eid"))).
  Proof. vm_compute; reflexivity. Qed.

  (* get_entries_for_device_id(device_id) (:1074): one probe, at key
     `some device_id`.  HA's index holds only the rows with a device; this one
     holds all of them, and the rows HA skipped sit in the None bucket, which
     nothing probes.  The partial index needed no partiality. *)
  Lemma entries_for_device_probes :
    query_at 1 (nth 4 prog_transformed CSkip)
    = Some (EACFold AGCount
              (probe "2" (EUnop OSome (EAccess (EVar "q") "dev")))).
  Proof. vm_compute; reflexivity. Qed.

  (* ============ the triple read, in all five configurations ============ *)

  (* THE ARITY-THREE WITNESS.  async_get_entity_id(domain, platform,
     unique_id) is ONE probe at a three-field record key: no residual filter,
     and so no scan of the domain's bucket.  The source conjunction was
     right-nested and nothing re-associated it. *)
  Lemma get_entity_id_probes_triple :
    query_at 2 (nth 4 prog_transformed CSkip)
    = Some (EACFold AGCount (probe "0" triple_key)).
  Proof. vm_compute; reflexivity. Qed.

  (* Configuration 0, which is what the selector can emit today: the probe
     narrows to one domain and the residual filter picks the row out of it.
     O(entities in the domain) where the tuple key is O(1) -- and `domain` is
     the coarsest of the three attributes, so that bucket is the largest one
     a prefix of this key can name. *)
  Lemma get_entity_id_probes_then_filters :
    query_at 2 (nth 0 prog_transformed CSkip)
    = Some (EACFold AGCount (refine (probe "2" dom_key) rest_eq)).
  Proof. vm_compute; reflexivity. Qed.

  (* Configuration 1: with neither the composite index nor SplitIf the read
     is a full scan.  1 and 2 differ only in the index, so this and
     get_entity_id_probes_with_dead_domain_index are the isolating pair. *)
  Lemma get_entity_id_scans_unsplit :
    query_at 2 (nth 1 prog_transformed CSkip)
    = Some (EACFold AGCount (scan by_triple)).
  Proof. vm_compute; reflexivity. Qed.

  (* Configuration 2: the same probe as configuration 4, one tag along,
     because the `domain` dictionary is still installed between them.
     Nothing reads it any more -- which is why configuration 4 exists and
     why the composite index at arity three REPLACES rather than ADDS. *)
  Lemma get_entity_id_probes_with_dead_domain_index :
    query_at 2 (nth 2 prog_transformed CSkip)
    = Some (EACFold AGCount (probe "0" triple_key)).
  Proof. vm_compute; reflexivity. Qed.

  (* THE HAZARD, EXECUTABLE, AT ARITY THREE.  Configuration 3 asks for the
     same four choices and adds SplitIf.  SplitIf peels the first conjunct off
     and hands it to the dictionary on `domain`, after which the composite
     rule's pattern no longer matches -- so the composite index is INSTALLED
     AND NEVER READ and the read is configuration 0's probe-then-filter again,
     with a fourth member paid for in full.

     Not two rules racing for one read, but a BASIC rewrite destroying the
     shape an index rule needs.  Same hazard as in eval/Kafka_Cluster; the
     arity does not change it, which is worth having pinned twice. *)
  Lemma composite_unused_when_split :
    query_at 2 (nth 3 prog_transformed CSkip)
    = Some (EACFold AGCount (refine (probe "3" dom_key) rest_eq)).
  Proof. vm_compute; reflexivity. Qed.

  (* ================= the write: _index_entry, derived ================= *)

  (* THE POINT OF THE MAINTENANCE RULES, and they only work as a pair: the
     insert rule turns rebuilding the index of `row :: rest` into building the
     index of `rest` and inserting one row, and the use rule then replaces
     that `index of rest` by the member already stored.  Either alone leaves
     an O(n) rebuild where it found one.

     What is left is ONE OInsert PER MEMBER -- which is _index_entry's own
     three assignments, line for line -- and because nothing reads the row
     list any more it is gone.  The table IS its three indexes ACROSS A WRITE,
     which is what EntityRegistryItems is: a UserDict whose `data` is one of
     the indexes rather than a list beside them. *)

  Definition member (i : string) : expr :=
    EAccess (EAccess (ELoc "entries") "aux_tag") i.
  Definition new_entry : expr := EAccess (EVar "q") "new_entry".

  (* the composite member: the key is a record built from the inserted row,
     and the row binder is the fold's own, which is what lets the rule reuse
     the matched body verbatim *)
  Definition composite_bucket_add : expr :=
    ELet new_entry "tup"
      (ELet (member "0") "acc"
         (ETernop OInsert (EVar "acc") row_triple
            (EBinop OBagInsert
               (EOptMatch (EBinop OLookup (EVar "acc") row_triple)
                  (EAtom (AEmptyBag None)) "x" (EVar "x"))
               (EVar "tup")))).

  (* a single-attribute member, maintained by DictIndexImpl's own rules *)
  Definition dict_bucket_add (i attr : string) : expr :=
    ELet (member i) "y"
      (ETernop OInsert (EVar "y") (EAccess new_entry attr)
         (EBinop OBagInsert
            (EOptMatch (EBinop OLookup (EVar "y") (EAccess new_entry attr))
               (EAtom (AEmptyBag None)) "x" (EVar "x"))
            new_entry)).

  Lemma insert_maintains_every_member :
    write_of (nth 4 prog_transformed CSkip)
    = Some (ERecord [("aux_tag",
                       ERecord [("0", composite_bucket_add);
                                ("1", dict_bucket_add "1" "id");
                                ("2", dict_bucket_add "2" "device_id")])]).
  Proof. vm_compute; reflexivity. Qed.

  (* ================= soundness ================= *)

  Theorem prog_transformed_sem : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      forall prog', In prog' prog_transformed ->
                    interp_command store env prog' = interp_command store env prog.
  Proof.
    unfold prog_transformed, heuristics, apply_optimize_anno; cbn [map]; intros.
    repeat destruct_In;
      try eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
    lazymatch goal with H: In _ [] |- _ => apply in_nil in H; intuition idtac end.
  Qed.
End WithConcreteMaps.
