Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem
  fiat2.TypeSound fiat2.TransfSound fiat2.IndexInterface fiat2.rules.CollectionTransf
  fiat2.TransfUtils fiat2.rules.FlatmapForms fiat2.rules.FlatmapTransf fiat2.index.IndexTransf
  fiat2.Utils fiat2.Substitute fiat2.pipeline.Pipeline fiat2.constraint.Decl fiat2.constraint.Surface fiat2.rules.SortBy.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString
  coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

(* ============================================================
   Source
     netbox-community/netbox
     netbox/netbox/core/jobs.py:160-168  (ChangelogHousekeeping)

       # Keep the most recent update per object only where no delete exists
       latest_update_pks_to_keep = (
           ObjectChange.objects.filter(action=ObjectChangeActionChoices.ACTION_UPDATE)
           .annotate(has_delete=Exists(deleted_exists))
           .filter(has_delete=False)
           .order_by('changed_object_type_id', 'changed_object_id', '-time', '-pk')
           .distinct('changed_object_type_id', 'changed_object_id')
           .values('pk')
       )

   Why this subject exists
     A FOUR-key order, MIXED direction, whose order SELECTS THE ANSWER.
     Postgres `DISTINCT ON (a, b)` keeps the first row of each (a, b) group
     IN THE ORDER BY's order -- so this is an argmin per group, and a
     different order is a different set of surviving records.  It is the
     hardest shape the desugaring has to reach, and it is real code.

     The grouping key is a PREFIX of the sort key, which is what Postgres
     requires of `DISTINCT ON`, and the two trailing keys are descending.
     Both facts are visible in the transcription: the prefix becomes the
     index's composite key, and descending becomes a projected negation --
     the limit `SortBy.v` states, exercised rather than hidden.

     The synergy is the point of the file.  The per-group read filters the
     table and then sorts, and the SORT RELAXES ITS INPUT TO A BAG
     (`Kafka_ConsumerProtocol`'s firewall) -- which is exactly what lets
     the ordinary BAG-VALUED composite dictionary serve the filter.  So the
     filter becomes one probe and the sort runs over the BUCKET rather than
     the table.  The firewall is not only a limitation; it is what makes
     the existing indexes usable underneath a sort.

   Pattern
     An argmin per group under a user-specified order, over an append-only
     log.  The read is an (N+1): the subquery is evaluated per group.  No
     catalogue code claimed, for the reason stated in `README.md`.

   Claim
     C1 and C3.  The order the programmer wrote in four fields with two
     directions is reached by the collection hierarchy and one `ESort`; and
     the structure that serves it -- a dictionary on the grouping prefix --
     is the one Postgres would build for `DISTINCT ON`.

   Faithfulness -- what this translation drops, and why
     * `time` is a datetime and `pk` an integer id; both are modelled as
       TInt, which is what the ordering needs of them.
     * DESCENDING is modelled by projecting the negation, so `-time, -pk`
       becomes `order by neg_time, neg_pk` ascending.  That is sound for
       integers and is exactly the limit `SortBy.v` records; a descending
       STRING key would not be expressible this way.
     * The `has_delete=Exists(...)` semijoin is dropped.  It is a second
       correlated subquery over the same table and is orthogonal to the
       ordering -- it would add a join to a file about a sort.  The
       `action=UPDATE` filter is kept, because it shares the read with the
       grouping key and shows the residual conjunct the composite rule
       leaves behind.
     * The key conjuncts are written FIRST and in the order the index is
       declared in, because the composite read rule collects them in that
       order; `action` is the residual.  `SplitIf` is NOT enabled here --
       it would peel the first conjunct and the composite pattern would
       stop matching, which is the ninth rule-ordering hazard and is
       pinned elsewhere (`HA_EntityRegistry`).
     * `DISTINCT ON` is spelled as the head of the ordered group, with a
       default for the empty group.  `EFold` is a fold_right, so a fold
       that DISCARDS its accumulator returns the FIRST element -- the same
       mechanism as the unique index's "the first row of the list wins".
       No head operator is needed or added.
     * The changelog is append-only, so the write is an append at the end,
       and it is the composite index's append maintenance that keeps it
       incremental.
     * Nothing is added.

   Expected
     The four-key mixed-direction order is honoured; the per-group read
     becomes one probe into a composite dictionary followed by a sort of
     the BUCKET; and the append is maintained without rebuilding.
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort [("action", TInt); ("type_id", TInt); ("object_id", TInt);
                        ("time", TInt); ("pk", TInt)]).

Definition query_ty :=
  TRecord (record_sort [("kind", TInt); ("type_id", TInt); ("object_id", TInt);
                        ("row", row_ty)]).

Definition ACTION_UPDATE : expr := EAtom (AInt 1).

(* The GROUP: the grouping key alone, which is what the composite
   dictionary is keyed on. *)
Definition group_of (t o : expr) : expr :=
  flatmap_filter_list (ELoc "changes") "c"
    (EBinop OAnd (EBinop OEq (EAccess (EVar "c") "type_id") t)
       (EBinop OEq (EAccess (EVar "c") "object_id") o))
    "c" None None.

(* `.filter(action=UPDATE)` -- the RESIDUAL, applied to the group rather
   than folded into the same filter.  The composite read rule checks the
   number of equality pairs against the key's arity
   (`Nat.eqb (List.length attrs) (List.length prs)`), so a residual conjunct
   in the same filter stops it firing.  Splitting the two is faithful --
   Django's `.filter()` calls compose -- and it is what a planner does
   anyway: probe the index, then apply what is left. *)
Definition updates_of (t o : expr) : expr :=
  flatmap_filter_list (group_of t o) "u"
    (EBinop OEq (EAccess (EVar "u") "action") ACTION_UPDATE)
    "u" None None.

(* `-time, -pk` : descending by projected negation *)
Definition neg_keys (src : expr) : expr :=
  EFlatmap LikeList src "c"
    (EBinop OCons
       (ERecord [("neg_time", EUnop ONeg (EAccess (EVar "c") "time"));
                 ("neg_pk", EUnop ONeg (EAccess (EVar "c") "pk"));
                 ("pk", EAccess (EVar "c") "pk")])
       (EAtom (ANil None))).

(* `DISTINCT ON (type_id, object_id) ... .values('pk')` for one group: the
   head of the ordered list.  A fold_right that discards its accumulator
   returns the FIRST element, so no head operator is needed. *)
Definition latest_update_str (t o : expr) : expr :=
  EFold (sort_by ["neg_time"; "neg_pk"] "r" "p" (neg_keys (updates_of t o)))
    (EAtom (AString "none")) "x" "acc"
    (EUnop OStringOfInt (EAccess (EVar "x") "pk")).

(* the FULL `order_by('changed_object_type_id', 'changed_object_id',
   '-time', '-pk')`, as one sort over the whole table.  The per-group read
   below needs only the two trailing keys, because it has already filtered
   to one group; this is the source's clause entire. *)
Definition keyed4 (src : expr) : expr :=
  EFlatmap LikeList src "c"
    (EBinop OCons
       (ERecord [("type_id", EAccess (EVar "c") "type_id");
                 ("object_id", EAccess (EVar "c") "object_id");
                 ("neg_time", EUnop ONeg (EAccess (EVar "c") "time"));
                 ("neg_pk", EUnop ONeg (EAccess (EVar "c") "pk"));
                 ("pk", EAccess (EVar "c") "pk")])
       (EAtom (ANil None))).

Definition full_order : expr :=
  sort_by ["type_id"; "object_id"; "neg_time"; "neg_pk"] "r" "p"
    (keyed4 (ELoc "changes")).

Definition prog : command :=
  CLetMut (EVar "changes_tbl") "changes"
    (CForeach (EVar "queries") "q"
       (CIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt 0)))
          (CAssign "outputs"
             (EBinop OCons
                (latest_update_str (EAccess (EVar "q") "type_id")
                   (EAccess (EVar "q") "object_id"))
                (ELoc "outputs")))
          (* the changelog is append-only *)
          (CAssign "changes"
             (EBinop OConcat (ELoc "changes")
                (EBinop OCons (EAccess (EVar "q") "row") (EAtom (ANil None))))))).

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
    map.put (map.put map.empty "changes_tbl" (TList row_ty))
      "queries" (TList query_ty).

  Definition checks (c : command) : bool :=
    match typecheck init_Gstore init_Genv c with
    | Success _ => true
    | Failure _ => false
    end.

  (* ------------------------------------------------------------------
     PIN 1.  Both orders this file needs are expressible: the two-key one
     the per-group read uses, and the FULL FOUR-KEY one the source writes.
     ------------------------------------------------------------------ *)
  Lemma per_group_order_is_expressible : names_ok ["neg_time"; "neg_pk"] = true.
  Proof. vm_compute; reflexivity. Qed.

  Lemma full_four_key_order_is_expressible :
    names_ok ["type_id"; "object_id"; "neg_time"; "neg_pk"] = true.
  Proof. vm_compute; reflexivity. Qed.

  Lemma prog_typechecks : checks prog = true.
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     PIN 2.  The four-key MIXED-direction order, on a table small enough
     to read.  Groups ascend by (type_id, object_id); inside a group the
     rows descend by time and then by pk -- pk 99 before pk 12 at the same
     time 9, which is what `-pk` means.
     ------------------------------------------------------------------ *)
  Definition ch (a t o tm k : Z) : value :=
    VRecord (record_sort [("action", VInt a); ("type_id", VInt t);
                          ("object_id", VInt o); ("time", VInt tm); ("pk", VInt k)]).

  Definition key4 (t o tm k : Z) : value :=
    VRecord (record_sort [("type_id", VInt t); ("object_id", VInt o);
                          ("neg_time", VInt (- tm)); ("neg_pk", VInt (- k));
                          ("pk", VInt k)]).

  (* object (7,100) has two UPDATEs, at t=5 pk=11 and t=9 pk=12, and a
     CREATE at t=9 pk=99 that the residual filter must drop;
     object (7,101) has one UPDATE at t=3 pk=13 *)
  Definition sample : list value :=
    [ ch 1 7 100 5 11; ch 0 7 100 9 99; ch 1 7 100 9 12; ch 1 7 101 3 13 ].

  Definition sample_store : clocals := map.put map.empty "changes" (VList sample).

  Definition run (e : expr) : value :=
    interp_expr sample_store (map.empty : clocals) e.

  Lemma four_key_mixed_order :
    run full_order
    = VList [ key4 7 100 9 99; key4 7 100 9 12; key4 7 100 5 11; key4 7 101 3 13 ].
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     PIN 3.  `DISTINCT ON (type_id, object_id)` is the head of the ordered
     group, so each read is an ARGMIN under the user's order -- and the
     residual action filter is what keeps the CREATE from winning.
     ------------------------------------------------------------------ *)
  Lemma latest_update_of_100 :
    run (latest_update_str (EAtom (AInt 7)) (EAtom (AInt 100))) = VString "12".
  Proof. vm_compute; reflexivity. Qed.

  Lemma latest_update_of_101 :
    run (latest_update_str (EAtom (AInt 7)) (EAtom (AInt 101))) = VString "13".
  Proof. vm_compute; reflexivity. Qed.

  Lemma empty_group_has_no_latest :
    run (latest_update_str (EAtom (AInt 7)) (EAtom (AInt 999))) = VString "none".
  Proof. vm_compute; reflexivity. Qed.

  (* and the general theorem applies at this order, so the three pins
     above are not three lucky computations *)
  Corollary per_group_order_is_the_comparator :
    forall (store env : clocals) e rows out,
      interp_expr store env e = VList rows ->
      Forall (fun v => exists rc, v = VRecord rc) rows ->
      interp_expr store env (sort_by ["neg_time"; "neg_pk"] "r" "p" e) = VList out ->
      Permutation rows out /\
      StronglySorted (fun u v => is_true (lex_leb ["neg_time"; "neg_pk"] u v)) out.
  Proof.
    intros store env e rows out H_rows H_rec H_out; split.
    1: eapply sort_by_permutes;
       [ apply per_group_order_is_expressible | exact H_rows | exact H_rec | exact H_out ].
    1: eapply sort_by_sorted;
       [ apply per_group_order_is_expressible | exact H_rows | exact H_rec | exact H_out ].
  Qed.

  (* ------------------------------------------------------------------
     PIN 4.  THE SYNERGY.  The sort relaxes its input to a bag
     (`Kafka_ConsumerProtocol.sort_is_a_demand_firewall`), and that is
     precisely what lets the ordinary BAG-VALUED composite dictionary
     serve the filter underneath it.  So the per-group read becomes ONE
     PROBE and the sort runs over the BUCKET, not the table.
     ------------------------------------------------------------------ *)
  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition optimized_with (ics : list index_choice) : command :=
    apply_optimize_anno (AC basics [ics] prog) init_Gstore init_Genv.

  Definition opt_composite := optimized_with [CompositeDictIdx ["type_id"; "object_id"]].
  Definition opt_none := apply_optimize_anno (AC basics [] prog) init_Gstore init_Genv.

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
    | CAssign "changes" e => Some e
    | _ => None
    end.

  (* peel every fold, flatmap and sort: what is at the bottom is what the
     query actually reads *)
  Fixpoint innermost_source (e : expr) : expr :=
    match e with
    | EFold e1 _ _ _ _ => innermost_source e1
    | EFlatmap _ e1 _ _ => innermost_source e1
    | ESort _ e1 => innermost_source e1
    | _ => e
    end.

  Definition group_key : expr :=
    ERecord [("type_id", EAccess (EVar "q") "type_id");
             ("object_id", EAccess (EVar "q") "object_id")].

  Definition idx_field : expr :=
    EAccess (EAccess (ELoc "changes") "aux_tag") "0".

  Lemma group_read_is_one_probe :
    option_map innermost_source (read_of opt_composite)
    = Some (EOptMatch (EBinop OLookup idx_field group_key)
              (EAtom (AEmptyBag None)) "b" (EVar "b")).
  Proof. vm_compute; reflexivity. Qed.

  (* without the index it is the table, i.e. a scan per group *)
  Lemma without_the_index_it_is_a_scan :
    option_map innermost_source (read_of opt_none)
    = Some (EUnop OBagOfList (ELoc "changes")).
  Proof. vm_compute; reflexivity. Qed.

  (* and because the only read goes through the index, the row list is
     ERASED even though the program writes: the table IS its index *)
  Lemma index_erases_the_list :
    installed_fields opt_composite = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     PIN 5.  The append is maintained.  The changelog is append-only, and
     the write comes out as one probe and one insert into the one bucket
     the new row's key names -- no fold over the table is left.
     ------------------------------------------------------------------ *)
  Lemma append_is_maintained :
    write_of opt_composite
    = Some (ERecord
              [("aux_tag",
                 ERecord
                   [("0",
                      ELet (EAccess (EVar "q") "row") "tup"
                        (ELet idx_field "acc"
                           (ETernop OInsert (EVar "acc")
                              (ERecord [("type_id", EAccess (EVar "tup") "type_id");
                                        ("object_id", EAccess (EVar "tup") "object_id")])
                              (EBinop OBagInsert
                                 (EOptMatch
                                    (EBinop OLookup (EVar "acc")
                                       (ERecord [("type_id", EAccess (EVar "tup") "type_id");
                                                 ("object_id", EAccess (EVar "tup") "object_id")]))
                                    (EAtom (AEmptyBag None)) "x" (EVar "x"))
                                 (EVar "tup")))))])]).
  Proof. vm_compute; reflexivity. Qed.

  (* ------------------------------------------------------------------
     And both configurations compute what the source computes.
     ------------------------------------------------------------------ *)
  Theorem opt_composite_sound : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      interp_command store env opt_composite = interp_command store env prog.
  Proof.
    unfold opt_composite, optimized_with, apply_optimize_anno; intros.
    eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
  Qed.

  Theorem opt_none_sound : forall (store env : clocals),
      locals_wf init_Gstore store ->
      locals_wf init_Genv env ->
      interp_command store env opt_none = interp_command store env prog.
  Proof.
    unfold opt_none, apply_optimize_anno; intros.
    eapply transf_sound__preserve_sem;
      eauto using apply_all_transfs_sound with transf_hints.
  Qed.
End WithConcreteMaps.
