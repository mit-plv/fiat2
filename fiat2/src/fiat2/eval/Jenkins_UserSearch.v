Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.FlatmapForms fiat2.TrigramIndexUse
  fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   Source
     jenkins, commit 81dc9a3e13a3ec4c4f74bedb772e3382b8de0760
     core/src/main/java/hudson/search/CollectionSearchIndex.java:54-75

       public void find(String token, List<SearchItem> result) {
           SearchItem p = get(token);                  // a hand-built MAP lookup
           if (p != null) result.add(p);
       }
       public void suggest(String token, List<SearchItem> result) {
           for (SMT o : allAsIterable()) {             // a LINEAR SCAN
               String name = getName(o);
               if (o != null && name.contains(token)) result.add(o);
           }
       }

     instantiated for users at core/src/main/java/jenkins/model/Jenkins.java:2437

       protected User get(String key) { return User.get(key, false); }
       protected Collection<User> all() { return User.getAll(); }

     over the table User.AllUsers holds in memory:

       private final ConcurrentMap<String, User> byName
           = new ConcurrentHashMap<>();                     User.java:1106
       static void put(String id, User u) { ...putIfAbsent... }    :1198
       static void remove(String id)                               :1190
       static Collection<User> values()                            :1202
       public static Collection<User> getAll()                     :693

     Live code, not a fallback: Search.java:233 serves the autocomplete
     endpoint and reaches index.suggest(token, result) at :347.

   Pattern
     B8 substring scan, beside A1a hand-built index and A2 maintained on
     insert and remove.  The two lookups are in ONE class over ONE
     collection, which is what makes this file short.

   Claim
     C3 for the substring read, and it is the strongest claim in these files:
     the author did not hand-build a structure for it.  They built the
     dictionary for exact match and left the substring match a scan, in the
     same class.  So here the optimizer is not matching hand-written storage
     but replacing hand-written scanning -- while, in the same program, the
     exact-match read reproduces the ConcurrentMap the author did build (C4).

     Worth being precise about what was and was not found in the corpus.
     There is NO hand-built substring index anywhere in the seven corpora --
     no trigram, n-gram, trie or suffix array -- and that is structural
     rather than accidental: substring search is outsourced, to a database
     (LIKE %x%, pg_trgm) or to a search engine.  What the corpus witnesses
     is the QUERY over a table the program itself maintains, which is what
     this file is.  NetBox hand-builds the other half of the same idea --
     netbox/search/backends.py's CachedValue is an inverted index held as a
     table, one row per indexed field per object, postings carrying object
     identity rather than the row, maintained on save and delete, queried
     with icontains -- so the architecture is witnessed too, with only the
     key derivation left to the database.

   Faithfulness -- what this translation drops, and why
     * getDisplayName() falls back to the id when no full name is set.  Here
       fullName is an ordinary attribute and the fallback is dropped; it is a
       per-row computation on the text, not a property of the search.
     * idStrategy().keyFor(id) case-folds the key, and suggest() lower-cases
       both sides of contains().  This model folds neither: the table is read
       as already holding the text in the form it is searched in.  Case
       folding on the KEY would be a different declared key (the folded one),
       and on the TEXT it is a per-row function of the attribute; neither
       changes what the index does.
     * getAll() sorts by id (User.java:696) before suggest() walks it, so the
       suggestions come out in id order.  Dropped: Search.java ranks the
       results it collects, so the scan's own order is not observed.  The
       suggestion read is therefore written as a SET, which loses nothing
       else either -- ids are declared unique, so no two rows are equal.
     * The exact-match read is written at BAG level and counted, as in the
       other eval files, because the output channel is a list of strings.
       This is a real choice and not a neutral one: the same read written as
       a set is NOT rewritten, because unique_lookup_head's pattern
       (UniqueIndexUse.v:438) is bag-level only.  Measured, not assumed --
       the first draft of this file wrote it as a set and got a scan.  The
       gap is the rule's collection level, not the index: the trigram read
       below resolves its keys to single rows at SET level, so the machinery
       exists.
     * Jenkins's real index is a union of nested SearchIndexes with ranking
       and truncation in Search.java, and four CollectionSearchIndex
       instances sit beside this one in the same method (items, computers,
       views; nine makeSearchIndex overrides in core).  One level, one
       collection is modelled.
     * Nothing is added.  Both writes are the writes the source performs.

     * The insert prepends the row, where the source quoted above appends
       (result.add).  The two differ as lists and agree as bags, and nothing
       here observes row order -- the suggestion read is a set and the
       exact-match read is counted -- so the substitution is sound.  See the
       note on row order in this directory's README.
   Expected
     ONE choice installs two members, because a trigram dictionary holds KEYS
     and cannot resolve them on its own: the postings on fullName, and the
     primary-key dictionary on id that turns a posting back into a row.

     find(token) becomes a single probe into the key member -- the
     ConcurrentHashMap lookup, derived.  suggest(token) becomes a probe of
     one trigram's bucket, a resolution of each key it names, and a recheck
     of contains on the way out; the recheck is not a leftover, since sharing
     a trigram is necessary for a substring match and not sufficient.

     The token comes from the request, so its length is not known at rewrite
     time and the rule emits the test: longer than two characters, probe;
     shorter, scan.  The scan branch is the source query unchanged, and the
     length condition is a soundness obligation and not a heuristic.

     Both writes maintain both members.  The delete is the one worth reading:
     it probes the key member for the row that is leaving and removes that
     row's id from each bucket its own text names, dropping a bucket that
     empties -- it does not rebuild the postings.

     The list survives, for one reason only: the fallback branch scans it.  A
     second configuration asks for the table's set representation as well,
     and then the fallback scans THAT -- so nothing reads the list and the
     list is erased.  Both are pinned.

     Which to prefer is settled below rather than left to the reader, and
     the answer is the FIRST.  The erasure substitutes the structure the
     remaining readers and writers walk instead of removing one: the delete
     applies the same filter to the rep member that it applied to the list,
     and the insert degrades from a cons to a set insert.

     The second configuration is therefore not a faster program, and that
     is not what it is for.  What it establishes is a REPRESENTATION fact.
     The collection phase had already found that nothing downstream of the
     suggestion read observes order or multiplicity -- that is what the set
     coercion on the table read means -- and TableRep lets that conclusion
     be realised in storage rather than only in the plan.  The member it
     installs has type TSet row_ty (RepIdx's idx_ty), the program is well
     typed holding it, and it computes what the scan form computes; both
     conjuncts are optimized_rep_sound.  So a set suffices here stops being
     a remark about one read and becomes a checked property of what is
     stored, and once the list field is erased, no stored copy of the rows
     is finer than the level the program needs.

     What it does NOT say is that the table may be stored as a set, and the
     difference matters.  TableRep at set level ALONE does not erase this
     list: find is a counted bag-level filter, so multiplicity is observed,
     and the rep rule matches only a set coercion -- the list stays and
     find keeps scanning it.  At bag level alone it is not erased either,
     since the suggestion read is at set level.  The erasure below happens
     only because the trigram pair has already taken find.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort [("id", TString); ("fullName", TString)]).

Definition query_ty :=
  TRecord (record_sort [("kind", TInt); ("k", TString); ("new_user", row_ty)]).

Section WithConcreteMaps.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* find(token) -> get(token): the scan a programmer writes when the
     language offers no index.  Counted, as in the other eval files. *)
  Definition by_id : expr :=
    EACFold AGCount
      (flatmap_filter_bag (EBagOf (ELoc "users")) "r"
         (EBinop OEq (EAccess (EVar "r") "id") (EAccess (EVar "q") "k"))
         "r" None None).

  (* suggest(token): name.contains(token) over the same collection, which is
     how Jenkins itself writes it. *)
  Definition by_substring : expr :=
    ESetOf (flatmap_filter_list (ELoc "users") "r"
              (EBinop OStrContains (EAccess (EVar "r") "fullName")
                 (EAccess (EVar "q") "k"))
              "r" (Some row_ty) (Some row_ty)).

  (* AllUsers.remove(id) *)
  Definition without_key : expr :=
    flatmap_filter_list (ELoc "users") "r"
      (EUnop ONot (EBinop OEq (EAccess (EVar "r") "id") (EAccess (EVar "q") "k")))
      "r" (Some row_ty) (Some row_ty).

  Definition report (e : expr) : scommand :=
    SLet e "n"
      (SAssign "outputs"
         (EBinop OCons (EUnop OIntToString (EVar "n")) (ELoc "outputs")) SSkip).

  Definition dispatch (k : Z) (thn els : scommand) : scommand :=
    SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt k))) thn els.

  Definition prog_s (ds : list decl) : scommand :=
    SLetConstrained "users" row_ty ds
      (SForeach (EVar "queries") "q"
         (dispatch 0
            (* User.get(id, true) -> AllUsers.putIfAbsent *)
            (SAssign "users"
               (EBinop OCons (EAccess (EVar "q") "new_user") (ELoc "users")) SSkip)
            (dispatch 1
               (* AllUsers.remove(id) *)
               (SAssign "users" without_key SSkip)
               (dispatch 2
                  (report by_id)
                  (SAssign "suggested" by_substring SSkip))))).

  Definition init_Gstore : ctenv :=
    map.put (map.put map.empty "outputs" (TList TString)) "suggested" (TSet row_ty).

  Definition init_Genv : ctenv :=
    map.put map.empty "queries" (TList query_ty).

  Definition elaborated (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_s ds).

  Definition decls := [DUnique "id"].

  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  (* One choice, two members.  UniqueDictIdx "id" is deliberately not asked
     for: the pair's second member carries every rule that choice would
     install (trigram_subsumes_unique_dict), so asking for both would build
     and maintain a second copy of the same dictionary. *)
  Definition anno : canno_command :=
    CAC (("users", (row_ty, decls)) :: cenv_rm "users" []) O
      basics [TrigramIdx "fullName" "id"] [] (elaborated decls).

  Definition optimized : command :=
    apply_optimize_anno_constrained (width:=width) anno init_Gstore init_Genv.

  (* The second configuration.  TableRep is listed FIRST, which is what makes
     it run last: its pattern is the bare coercion of the table's read, which
     the trigram read rule's pattern contains as a subterm. *)
  Definition anno_rep : canno_command :=
    CAC (("users", (row_ty, decls)) :: cenv_rm "users" []) O
      basics [TableRep LikeSet; TrigramIdx "fullName" "id"] [] (elaborated decls).

  Definition optimized_rep : command :=
    apply_optimize_anno_constrained (width:=width) anno_rep init_Gstore init_Genv.

  (* ---- projections, so every claim below is an equality of closed terms ---- *)

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  Definition install_of (c : command) : option expr :=
    match c with CLetMut e _ _ => Some e | _ => None end.

  Definition write_guard (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ (CIf g _ _) _)) => Some g
    | _ => None
    end.

  Definition insert_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ (CIf _ (CAssign _ e) _) _)) => Some e
    | _ => None
    end.

  Definition delete_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ (CIf _ (CAssign _ e) _) _))) => Some e
    | _ => None
    end.

  Definition find_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CIf _ (CLet e _ _) _)))) => Some e
    | _ => None
    end.

  Definition suggest_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ (CForeach _ _ (CIf _ _ (CIf _ _ (CIf _ _ (CAssign _ e))))) => Some e
    | _ => None
    end.

  (* ---- the shapes the claims are stated against ---- *)

  Definition member (i : string) : expr :=
    EAccess (EAccess (ELoc "users") "aux_tag") i.
  Definition the_list : expr := EAccess (ELoc "users") "id_tag".
  Definition new_user : expr := EAccess (EVar "q") "new_user".
  Definition token : expr := EAccess (EVar "q") "k".
  Definition no_rows : expr := EAtom (ANil (Some row_ty)).

  (* the trigram starting at pos of a text, and the positions at which a text
     has one -- 0 .. len-2, which is why a pattern shorter than three
     characters has none *)
  Definition tri_at (text pos : expr) : expr :=
    ETernop OSubstring text pos (EAtom (AInt 3)).
  Definition positions (text : expr) : expr :=
    EBinop ORange (EAtom (AInt 0))
      (EBinop OMinus (EUnop OLengthString text) (EAtom (AInt 2))).

  Definition tup_text : expr := EAccess (EVar "tup") "fullName".
  Definition tup_key : expr := EAccess (EVar "tup") "id".

  (* add one row's id to the bucket of every trigram of its text *)
  Definition post_row (acc : expr) : expr :=
    EFold (positions tup_text) acc "pos" "sacc"
      (ETernop OInsert (EVar "sacc") (tri_at tup_text (EVar "pos"))
         (EOptMatch (EBinop OLookup (EVar "sacc") (tri_at tup_text (EVar "pos")))
            (EBinop OSetInsert (EAtom (AEmptySet None)) tup_key)
            "bkt" (EBinop OSetInsert (EVar "bkt") tup_key))).

  Definition build_postings (src : expr) : expr :=
    EFold src (EAtom (AEmptyDict Unranged None)) "tup" "acc" (post_row (EVar "acc")).

  Definition build_keys (src : expr) : expr :=
    EFold src (EAtom (AEmptyDict Unranged None)) "tup" "acc"
      (ETernop OInsert (EVar "acc") tup_key (EVar "tup")).

  (* the one row under a key, or no row: a probe's shape when the key is
     declared unique *)
  Definition key_probe (idx k : expr) : expr :=
    EOptMatch (EBinop OLookup idx k)
      (EAtom (AEmptyBag None)) "y"
      (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "y")).

  (* probe the bucket at g, resolve each key through the key member, recheck *)
  Definition tri_probe (tri_tag key_tag : string) (g : expr) : expr :=
    EFlatmap LikeSet
      (EOptMatch (EBinop OLookup (member tri_tag) g)
         (EAtom (AEmptySet None)) "b" (EVar "b"))
      "k"
      (EOptMatch (EBinop OLookup (member key_tag) (EVar "k"))
         (EAtom (AEmptySet None)) "y"
         (EIf (EBinop OStrContains (EAccess (EVar "y") "fullName") token)
            (EBinop OSetInsert (EAtom (AEmptySet None)) (EVar "y"))
            (EAtom (AEmptySet None)))).

  (* the source query, left as the fallback, over whatever it is given *)
  Definition scan (src : expr) : expr :=
    flatmap_filter_set src "r"
      (EBinop OStrContains (EAccess (EVar "r") "fullName") token)
      "r" (Some row_ty) (Some row_ty).

  Definition long_enough : expr :=
    EBinop OLess (EAtom (AInt 2)) (EUnop OLengthString token).

  (* ==================== configuration 0: the trigram pair ============== *)

  (* Two members from one choice: the postings on fullName at "0", the
     primary-key dictionary on id at "1".  Both ask a backend for a hash
     table -- a trigram lookup is a point lookup on a derived key. *)
  Definition install_expected : expr :=
    ERecord
      [("id_tag", no_rows);
       ("aux_tag", ERecord [("0", build_postings no_rows);
                            ("1", build_keys no_rows)])].

  Lemma installs_the_pair : install_of optimized = Some install_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* find(token): the scan became one probe into the key member.  This is
     User.AllUsers.byName.get(id), derived from a program that names no
     structure -- the C4 half. *)
  Lemma find_is_a_probe :
    find_of optimized = Some (EACFold AGCount (key_probe (member "1") token)).
  Proof. vm_compute; reflexivity. Qed.

  (* suggest(token): the C3 half, and the reason this file exists.  One
     trigram's bucket, each key resolved through the key member, contains
     rechecked on the way out.  The guard is a soundness obligation: a
     pattern shorter than three characters has no trigram, so the rule emits
     the test and keeps the source query as the other branch. *)
  Lemma suggest_is_a_guarded_trigram_probe :
    suggest_of optimized
    = Some (EIf long_enough
              (tri_probe "0" "1" (tri_at token (EAtom (AInt 0))))
              (scan (ESetOf the_list))).
  Proof. vm_compute; reflexivity. Qed.

  (* AllUsers.putIfAbsent: the declared key costs one lookup, not a scan. *)
  Lemma guard_is_a_probe :
    write_guard optimized
    = Some (EBinop OAnd
              (ELet new_user "_pk_row"
                 (EBinop OEq (key_probe (member "1") (EAccess (EVar "_pk_row") "id"))
                    (EAtom (AEmptyBag None))))
              (EAtom (ABool true))).
  Proof. vm_compute; reflexivity. Qed.

  (* and the insert maintains both members: the new row's id is added to the
     bucket of each trigram of its own text, and to the key member at its
     key.  Neither member is rebuilt. *)
  Definition insert_expected : expr :=
    ERecord
      [("id_tag", EBinop OCons new_user the_list);
       ("aux_tag",
         ERecord
           [("0", ELet (member "0") "acc" (ELet new_user "tup" (post_row (EVar "acc"))));
            ("1", ELet (member "1") "acc"
                    (ELet new_user "tup"
                       (ETernop OInsert (EVar "acc") tup_key (EVar "tup"))))])].

  Lemma insert_maintains_both : insert_of optimized = Some insert_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* THE DELETE IS THE POINT.  The row that leaves is not known to the write
     -- the write names a key -- so the postings are corrected by PROBING the
     key member for that row, then removing its id from each bucket its own
     text names, and dropping a bucket that empties.  Nothing is rebuilt and
     nothing scans the table. *)
  Definition unpost_row (acc : expr) : expr :=
    EFold (positions tup_text) acc "pos" "sacc"
      (EOptMatch (EBinop OLookup (EVar "sacc") (tri_at tup_text (EVar "pos")))
         (EVar "sacc") "bkt"
         (EIf (EBinop OEq
                 (EBinop OSetDiff (EVar "bkt")
                    (EBinop OSetInsert (EAtom (AEmptySet None)) tup_key))
                 (EAtom (AEmptySet None)))
            (EBinop ODelete (EVar "sacc") (tri_at tup_text (EVar "pos")))
            (ETernop OInsert (EVar "sacc") (tri_at tup_text (EVar "pos"))
               (EBinop OSetDiff (EVar "bkt")
                  (EBinop OSetInsert (EAtom (AEmptySet None)) tup_key))))).

  Definition delete_expected : expr :=
    ERecord
      [("id_tag", flatmap_filter_list the_list "r"
                    (EUnop ONot (EBinop OEq (EAccess (EVar "r") "id") token))
                    "r" (Some row_ty) (Some row_ty));
       ("aux_tag",
         ERecord
           [("0", ELet (member "0") "acc"
                    (EOptMatch (EBinop OLookup (member "1") token)
                       (EVar "acc") "tup" (unpost_row (EVar "acc"))));
            ("1", EBinop ODelete (member "1") token)])].

  Lemma delete_maintains_both : delete_of optimized = Some delete_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* And the list survives.  Not because find reads it -- find is a probe now
     -- but because the fallback branch of suggest scans it.  That is a READ
     the index rules could not take, and nothing about guards or maintenance
     is involved. *)
  Lemma the_fallback_keeps_the_list :
    installed_fields optimized = ["id_tag"; "aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ============ configuration 1: and the table's set as well ============ *)

  (* Nothing about either read's rewrite changes; what changes is what the
     fallback scans.  Above it coerces the whole list on every evaluation;
     here that coercion IS a member, so the fallback reads it -- and then the
     list has no reader left and is erased.  The table IS its three indexes. *)
  Lemma rep_erases_the_list :
    installed_fields optimized_rep = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* The set is "0", so the postings are "1" and the keys they point through
     are "2".  The probe is otherwise the same term. *)
  Lemma rep_suggest_falls_back_to_the_set :
    suggest_of optimized_rep
    = Some (EIf long_enough
              (tri_probe "1" "2" (tri_at token (EAtom (AInt 0))))
              (scan (member "0"))).
  Proof. vm_compute; reflexivity. Qed.

  Lemma rep_find_is_still_a_probe :
    find_of optimized_rep = Some (EACFold AGCount (key_probe (member "2") token)).
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     WHAT THE SECOND CONFIGURATION COSTS, measured rather than assumed.

     The erasure above is easy to misread as a win -- a field disappears.
     It is not one.  TableRep IS a copy of the table, so what the erasure
     does is SUBSTITUTE the structure the remaining readers and writers
     walk, and the four lemmas below are the comparison, side by side.

     The delete applies the SAME filter either way -- the source's own,
     over whatever holds the rows -- so the O(n) scan moves from the list
     to the rep member and does not go away.  And the insert degrades: a
     cons onto a list becomes an insert into a set.

     So the two configurations are a wash on the delete and the second is
     slightly worse on the insert, and the honest reading of the pair is
     that TableRep here is an EXPRESSIVENESS result -- a table can be its
     own index, and the fallback scan is served by a member rather than by
     a field -- and not a performance one.  Contrast the erasures that ARE
     wins: in Kafka_Cluster, HA_AreaRegistry, Kafka_NamedCache and
     Keycloak with its count, every read is answered by an index and
     NOTHING replaces the list.

     This is why the deterministic selector (src/fiat2/Selector.v) does not
     emit TableRep.  A feedback step that runs the pipeline, finds the
     surviving read and adds TableRep for it does reach the configuration
     below -- it was built and then removed, because "the list was erased"
     is not a proxy for "this paid". *)

  (* the body a write assigns to a named field, at the top level of the
     record or one level down inside aux_tag *)
  Definition field (f : string) (l : list (string * expr)) : option expr :=
    option_map snd (find (fun p => String.eqb f (fst p)) l).

  Definition written_to (f : string) (e : option expr) : option expr :=
    match e with
    | Some (ERecord l) =>
        match field f l with
        | Some b => Some b
        | None =>
            match field "aux_tag" l with
            | Some (ERecord l') => field f l'
            | _ => None
            end
        end
    | _ => None
    end.

  Definition drop_named (src : expr) (tag : collection_tag) : expr :=
    EFlatmap tag src "r"
      (EIf (EUnop ONot (EBinop OEq (EAccess (EVar "r") "id") token))
         (match tag with
          | LikeList => EBinop OCons (EVar "r") (EAtom (ANil (Some row_ty)))
          | LikeBag => EBinop OBagInsert (EAtom (AEmptyBag (Some row_ty))) (EVar "r")
          | LikeSet => EBinop OSetInsert (EAtom (AEmptySet (Some row_ty))) (EVar "r")
          end)
         (match tag with
          | LikeList => EAtom (ANil (Some row_ty))
          | LikeBag => EAtom (AEmptyBag (Some row_ty))
          | LikeSet => EAtom (AEmptySet (Some row_ty))
          end)).

  Lemma delete_filters_the_list :
    written_to "id_tag" (delete_of optimized) = Some (drop_named the_list LikeList).
  Proof. vm_compute; reflexivity. Qed.

  (* the same filter, over the member that replaced the list *)
  Lemma rep_delete_filters_the_rep :
    written_to "0" (delete_of optimized_rep)
    = Some (drop_named (member "0") LikeSet).
  Proof. vm_compute; reflexivity. Qed.

  Lemma insert_conses_onto_the_list :
    written_to "id_tag" (insert_of optimized)
    = Some (EBinop OCons new_user the_list).
  Proof. vm_compute; reflexivity. Qed.

  (* and this is the price: a cons becomes a set insert *)
  Lemma rep_insert_is_a_set_insert :
    written_to "0" (insert_of optimized_rep)
    = Some (EBinop OSetInsert (member "0") new_user).
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     And all of it is sound: both programs compute what the scan form
     computes, on every store and environment. *)

  Lemma row_ty_wf : type_wf row_ty.
  Proof. unfold row_ty. repeat constructor; cbn; intuition congruence. Qed.

  Lemma query_ty_wf : type_wf query_ty.
  Proof. unfold query_ty, row_ty. repeat constructor; cbn; intuition congruence. Qed.

  Lemma init_Gstore_wf : tenv_wf init_Gstore.
  Proof.
    unfold init_Gstore; apply tenv_wf_step;
      [ apply tenv_wf_step; [ apply tenv_wf_empty | repeat constructor ]
      | constructor; apply row_ty_wf ].
  Qed.

  Lemma init_Genv_wf : tenv_wf init_Genv.
  Proof.
    unfold init_Genv; apply tenv_wf_step;
      [ apply tenv_wf_empty | constructor; apply query_ty_wf ].
  Qed.

  Lemma decls_wf : Forall (decl_wf (tenv:=ctenv) row_ty) decls.
  Proof.
    unfold decls, row_ty; cbn [decl_wf].
    repeat constructor;
      exists [("fullName", TString); ("id", TString)], TString;
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

  Theorem optimized_rep_sound :
    well_typed init_Gstore init_Genv optimized_rep /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized_rep
        = interp_command store env (elaborated decls).
  Proof.
    unfold optimized_rep, anno_rep, elaborated, prog_s.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply row_ty_wf
      | apply incl_refl | apply decls_wf | apply elaborated_well_typed ].
  Qed.
End WithConcreteMaps.
