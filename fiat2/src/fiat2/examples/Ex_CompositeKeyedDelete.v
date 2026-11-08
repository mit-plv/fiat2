Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.constraint.Decl fiat2.constraint.Surface fiat2.constraint.Constraint fiat2.Substitute fiat2.constraint.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.rules.FlatmapForms fiat2.Pipeline.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* ============================================================
   TWO DELETES ON ONE TABLE, AND ONLY ONE OF THEM NEEDS A DECLARATION.

   A regression test, not an evaluation subject.  The table carries a
   composite index on (k1, k2) and declares id unique, and the program
   deletes in both of the shapes a composite index can be asked for:

     * AT THE COMPOSITE KEY -- a filter naming k1 and k2.  Served by the
       index's own rule, which needs no declaration: every row in the bucket
       leaves, so the entry goes with one ODelete.
     * AT THE DECLARED KEY -- a filter naming id, which the index is not
       keyed on at all.  No rule of the index can serve this: the row that
       leaves is not in the expression, only its key is.  The pair's rule
       probes the primary-key member for that row and takes it out of the one
       bucket its composite key names, and THAT is what the declaration pays
       for -- with two rows at one id, taking one row's contributions out
       would lose the other's.

   So the declaration ADDS a rule and trades none: both deletes are
   incremental here, and the first one would still be incremental with the
   declarations empty.  keyed_composite_subsumes_composite is the general
   statement; this file is the instance, with both emitted forms pinned.

   WHAT IT MEASURES (harness `csv typed 200 400 800 1600`; work at 1600 rows
   and the fitted exponent).  Two programs, because the second one isolates
   the keyed delete -- see prog_keyed_s below.

   composite_keyed_delete -- the read, the insert and the KEYED delete, with
   the row list erased because nothing reads it:

     kind          source     a     optimized     a      ratio
     readAtKey    1160800  1.00          1412  0.01      822x
     insert        659870  0.98          3930  0.01      168x
     deleteById    780130  1.02          4200  0.01      186x

   THE KEYED DELETE IS THE NUMBER THIS FILE EXISTS FOR: 1.02 to 0.01, an
   exponent and not a constant.  The insert's 168x is a second thing the
   declaration buys and is not this rule's doing: the source checks the
   declared key with an O(n) scan and the optimized form checks it with one
   probe into the key member, which is what PrimaryKeyCheck is about.

   composite_two_deletes -- the same table with the composite-key delete as
   well, which is where the two rules coexist:

     kind          source     a     optimized     a      ratio
     readAtKey    1160800  1.00          1412  0.01      822x
     insert        659870  0.98          3930  0.01      168x
     deleteAtKey  1313955  1.02          3360  0.01      391x
     deleteById    780350  1.02          4420  0.01      177x

   EVERY OPERATION IS AN EXPONENT, and the two deletes cost each other
   nothing: adding the composite-key delete leaves the keyed delete at 177x
   against its own 186x alone, which is the one extra record field.

   THE LAST TWO ROWS USED TO BE THIS FILE'S PRICED GAP, and they are worth
   keeping in view because they are what a measurement bought.  Before
   CompositeKeyBucketDelete existed, a delete at the whole composite key
   could not maintain the primary-key member -- that member is keyed on id,
   which the filter does not name -- so the member was REBUILT.  Measured,
   that made deleteAtKey 3305310 at a=1.02, which is 2.5x WORSE than the
   source's own filter, and the rebuild kept the row list installed, which
   cost deleteById its whole 186x (784070, a=1.00, 1.0x).  The rule that
   closed it needed no new primitive: the composite member's bucket at the
   deleted key holds exactly the rows that are leaving, and ESort LikeBag is
   already a TBag -> TList coercion, so an ordinary EFold deletes their ids
   from the key member one by one -- which is sound because deleting keys
   COMMUTES, so the order the sort picks cannot be observed
   (CompositeKeyBucketDelete.fold_pk_del_Permutation).
   ============================================================ *)

Definition row_ty :=
  TRecord (record_sort
             [("id", TString); ("k1", TString); ("k2", TString); ("v", TString)]).

Definition query_ty :=
  TRecord (record_sort
             [("kind", TInt); ("a", TString); ("b", TString); ("k", TString);
              ("new_item", row_ty)]).

Section WithConcreteMaps.
  Notation value := (value).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* [r <- items, check(pred), ret r], counted *)
  Definition filt (pred : expr) : expr :=
    EUnop OLength
      (EFlatmap LikeList (ELoc "items") "r"
         (EIf pred (EBinop OCons (EVar "r") (EAtom (ANil None)))
            (EAtom (ANil None)))).

  Definition c1 : expr := EBinop OEq (EAccess (EVar "r") "k1") (EAccess (EVar "q") "a").
  Definition c2 : expr := EBinop OEq (EAccess (EVar "r") "k2") (EAccess (EVar "q") "b").
  Definition c_id : expr :=
    EBinop OEq (EAccess (EVar "r") "id") (EAccess (EVar "q") "k").

  (* keep the rows the composite key does NOT name *)
  Definition drop_at_key : expr :=
    EFlatmap LikeList (ELoc "items") "r"
      (EIf (EUnop ONot (EBinop OAnd c2 c1))
         (EBinop OCons (EVar "r") (EAtom (ANil None))) (EAtom (ANil None))).

  (* keep the rows whose DECLARED key is not the one named *)
  Definition drop_at_id : expr :=
    EFlatmap LikeList (ELoc "items") "r"
      (EIf (EUnop ONot c_id)
         (EBinop OCons (EVar "r") (EAtom (ANil None))) (EAtom (ANil None))).

  Definition report (e : expr) : scommand :=
    SLet e "n"
      (SAssign "outputs"
         (EBinop OCons (EUnop OStringOfInt (EVar "n")) (ELoc "outputs")) SSkip).

  Definition dispatch (k : Z) (thn els : scommand) : scommand :=
    SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt k))) thn els.

  (*   0  read at the composite key
       1  an insert
       2  a delete AT the composite key   (needs no declaration)
       3  a delete at the DECLARED key    (gated on it) *)
  Definition prog_s (ds : list decl) : scommand :=
    SLetConstrained "items" row_ty ds
      (SForeach (EVar "queries") "q"
         (dispatch 0 (report (filt (EBinop OAnd c1 c2)))
            (dispatch 1
               (SAssign "items"
                  (EBinop OCons (EAccess (EVar "q") "new_item") (ELoc "items")) SSkip)
               (dispatch 2
                  (SAssign "items" drop_at_key SSkip)
                  (SAssign "items" drop_at_id SSkip))))).

  (* THE SAME TABLE WITHOUT THE COMPOSITE-KEY DELETE, which is how the keyed
     delete is measured on its own.

     It used to be a necessity rather than a control: the composite-key
     delete rebuilt the primary-key member, the rebuild read the row list, so
     the list could not be erased, and with the list installed every write
     paid a linear pass over it -- which hid what the keyed delete does.  That
     gap is closed (composite_delete_maintains_the_key_member below), so both
     programs now erase the list and the two measure the same way.  The pair
     is kept because it is what isolates the keyed delete's own cost: the
     difference between the two is one record field and nothing else. *)
  Definition prog_keyed_s (ds : list decl) : scommand :=
    SLetConstrained "items" row_ty ds
      (SForeach (EVar "queries") "q"
         (dispatch 0 (report (filt (EBinop OAnd c1 c2)))
            (dispatch 1
               (SAssign "items"
                  (EBinop OCons (EAccess (EVar "q") "new_item") (ELoc "items")) SSkip)
               (SAssign "items" drop_at_id SSkip)))).

  Definition init_Gstore : ctenv := map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv := map.put map.empty "queries" (TList query_ty).

  Definition elaborated (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_s ds).

  Definition decls := [DUnique "id"].

  Definition basics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition anno : canno_command :=
    CAC (("items", (row_ty, decls)) :: cenv_rm "items" []) O
      basics [KeyedCompositeIdx ["k1"; "k2"] "id"] [] (elaborated decls).

  Definition optimized : command :=
    apply_optimize_anno_constrained anno init_Gstore init_Genv.

  Definition elaborated_keyed (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_keyed_s ds).

  Definition anno_keyed : canno_command :=
    CAC (("items", (row_ty, decls)) :: cenv_rm "items" []) O
      basics [KeyedCompositeIdx ["k1"; "k2"] "id"] [] (elaborated_keyed decls).

  Definition optimized_keyed : command :=
    apply_optimize_anno_constrained anno_keyed init_Gstore init_Genv.

  (* ---- projections ---- *)

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  Fixpoint peel (c : command) : command :=
    match c with
    | CLetMut _ _ c' => peel c'
    | CForeach _ _ c' => c'
    | _ => c
    end.

  Fixpoint write_branch (n : nat) (c : command) : option expr :=
    match n, c with
    | O, CIf _ (CAssign _ e) _ => Some e
    (* a write that carries a declared constraint's guard *)
    | O, CIf _ (CIf _ (CAssign _ e) _) _ => Some e
    | O, CAssign _ e => Some e
    | S n', CIf _ _ c' => write_branch n' c'
    | _, _ => None
    end.

  Definition write_at (n : nat) (c : command) : option expr :=
    write_branch n (peel c).

  Fixpoint read_branch (n : nat) (c : command) : option expr :=
    match n, c with
    | O, CIf _ (CLet e _ _) _ => Some e
    | O, CLet e _ _ => Some e
    | S n', CIf _ _ c' => read_branch n' c'
    | _, _ => None
    end.

  Definition query_at (n : nat) (c : command) : option expr :=
    read_branch n (peel c).

  Fixpoint assoc_expr (k : string) (l : list (string * expr)) : option expr :=
    match l with
    | [] => None
    | (k', e) :: l' => if String.eqb k k' then Some e else assoc_expr k l'
    end.

  (* one member's maintenance, out of the record a write rebinds *)
  Definition member_at (n : nat) (tg : string) (c : command) : option expr :=
    match write_at n c with
    | Some (ERecord l) =>
        match assoc_expr "aux_tag" l with
        | Some (ERecord al) => assoc_expr tg al
        | _ => None
        end
    | _ => None
    end.

  (* and the row list's own maintenance *)
  Definition list_at (n : nat) (c : command) : option expr :=
    match write_at n c with
    | Some (ERecord l) => assoc_expr "id_tag" l
    | _ => None
    end.

  (* the source a member is REBUILT from, where it is rebuilt at all: the
     fold's collection.  A member maintained incrementally is not a fold, so
     this is None of it. *)
  Definition rebuild_src (e : option expr) : option expr :=
    match e with
    | Some (EFold d _ _ _ _) => Some d
    | _ => None
    end.

  (* ---- what the terms are written in ---- *)

  Definition mem (t : string) : expr :=
    EAccess (EAccess (ELoc "items") "aux_tag") t.
  Definition list_e : expr := EAccess (ELoc "items") "id_tag".
  Definition q_fld (f : string) : expr := EAccess (EVar "q") f.

  (* a composite key built out of one row expression's attributes, and one
     built out of the query's -- in the order the matched conjunction had
     them, which is why the delete's is permuted *)
  Definition ckey_of_row (r : string) : expr :=
    ERecord [("k1", EAccess (EVar r) "k1"); ("k2", EAccess (EVar r) "k2")].
  Definition ckey_of_q : expr :=
    ERecord [("k1", q_fld "a"); ("k2", q_fld "b")].
  Definition ckey_of_q_permuted : expr :=
    ERecord [("k2", q_fld "b"); ("k1", q_fld "a")].

  (* ---- the read: one probe ---- *)

  Lemma read_is_one_probe :
    query_at 0 optimized
    = Some (EACFold AGCount
              (EOptMatch (EBinop OLookup (mem "0") ckey_of_q)
                 (EAtom (AEmptyBag None)) "b" (EVar "b"))).
  Proof. vm_compute; reflexivity. Qed.

  (* ---- the insert: both members, incrementally ---- *)

  Lemma insert_maintains_the_composite_member :
    member_at 1 "0" optimized
    = Some (ELet (q_fld "new_item") "tup"
              (ELet (mem "0") "acc"
                 (ETernop OInsert (EVar "acc") (ckey_of_row "tup")
                    (EBinop OBagInsert
                       (EOptMatch (EBinop OLookup (EVar "acc") (ckey_of_row "tup"))
                          (EAtom (AEmptyBag None)) "x" (EVar "x"))
                       (EVar "tup"))))).
  Proof. vm_compute; reflexivity. Qed.

  Lemma insert_maintains_the_key_member :
    member_at 1 "1" optimized
    = Some (ELet (mem "1") "acc"
              (ELet (q_fld "new_item") "tup"
                 (ETernop OInsert (EVar "acc") (EAccess (EVar "tup") "id")
                    (EVar "tup")))).
  Proof. vm_compute; reflexivity. Qed.

  (* ---- the delete AT THE COMPOSITE KEY, which needs no declaration ----

     One ODelete, and the key it deletes is written in the order the matched
     conjunction had the conjuncts in -- k2 before k1 -- which is the read
     rule's order-insensitivity showing up on the write side. *)

  Lemma composite_delete_is_one_odelete :
    member_at 2 "0" optimized
    = Some (EBinop ODelete (mem "0") ckey_of_q_permuted).
  Proof. vm_compute; reflexivity. Qed.

  (* AND ITS OTHER MEMBER, which used to be this file's priced gap and is
     now a probe and a fold.  The primary-key member is keyed on id, which
     this filter does not name, so no rule can read off WHICH entries leave
     -- but the composite member's bucket at the deleted key holds exactly
     the rows that are leaving, so their ids can be deleted one at a time.
     That is what CompositeKeyBucketDelete emits, and ESort LikeBag is the
     coercion that lets an EFold walk a bag.

     The two members are now maintained in OPPOSITE directions by the two
     deletes: this one probes the composite member to maintain the key
     member, and the keyed delete below probes the key member to maintain
     the composite one. *)
  Lemma composite_delete_maintains_the_key_member :
    member_at 2 "1" optimized
    = Some (ELet (mem "1") "acc"
              (EOptMatch (EBinop OLookup (mem "0") ckey_of_q_permuted)
                 (EVar "acc") "bkt"
                 (EFold (ESort LikeBag (EVar "bkt")) (EVar "acc") "tup" "acc"
                    (EBinop ODelete (EVar "acc")
                       (EAccess (EVar "tup") "id"))))).
  Proof. vm_compute; reflexivity. Qed.

  (* ---- the delete AT THE DECLARED KEY, which is what the declaration buys ----

     THE POINT OF THE FILE.  Neither member is rebuilt and neither reads the
     row list: the key member drops one entry with one ODelete, and the
     composite member is reached by probing the key member for the row that
     is leaving and taking just that row out of the one bucket its composite
     key names -- deleting the entry if it empties, since the index of a
     table never holds an empty bucket. *)

  Definition bucket_without_the_row : expr :=
    flatmap_filter_bag (EVar "bkt") "rvar"
      (EUnop ONot (EBinop OEq (EAccess (EVar "rvar") "id")
                     (EAccess (EVar "tup") "id")))
      "rvar" None None.

  Lemma keyed_delete_unindexes_the_composite_member :
    member_at 3 "0" optimized
    = Some (ELet (mem "0") "acc"
              (EOptMatch (EBinop OLookup (mem "1") (q_fld "k"))
                 (EVar "acc") "tup"
                 (EOptMatch (EBinop OLookup (EVar "acc") (ckey_of_row "tup"))
                    (EVar "acc") "bkt"
                    (EIf (EBinop OEq bucket_without_the_row
                            (EAtom (AEmptyBag None)))
                       (EBinop ODelete (EVar "acc") (ckey_of_row "tup"))
                       (ETernop OInsert (EVar "acc") (ckey_of_row "tup")
                          bucket_without_the_row))))).
  Proof. vm_compute; reflexivity. Qed.

  Lemma keyed_delete_is_one_odelete_on_the_key_member :
    member_at 3 "1" optimized
    = Some (EBinop ODelete (mem "1") (q_fld "k")).
  Proof. vm_compute; reflexivity. Qed.

  (* Neither of the two deletes was traded for the other: the composite
     member is maintained incrementally by BOTH, with no declaration needed
     for the first.  keyed_composite_subsumes_composite is the general
     statement; these two lemmas are its instance. *)

  (* ---- what is installed ----

     THE TABLE IS ITS TWO INDEXES, across BOTH deletes.  The row list is
     erased: with the key member maintained incrementally by the
     composite-key delete too, nothing reads the list any more.  This
     equality is what closing the gap bought, and it is why prog_keyed_s
     below now measures the same way. *)
  Lemma the_table_is_its_two_indexes :
    installed_fields optimized = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* and the same fact from the write side: no arm of any write carries a
     row list, so there is no linear pass left anywhere in the program *)
  Lemma no_write_keeps_a_row_list :
    list_at 3 optimized = None.
  Proof. vm_compute; reflexivity. Qed.

  (* ---- the same keyed delete with nothing to keep the list alive ----

     THE TABLE IS ITS TWO INDEXES.  With the composite-key delete gone,
     nothing reads the row list and the field is erased, so the keyed delete
     is index work only: one ODelete on the key member, and one bucket
     reached by probing it. *)

  Lemma keyed_only_erases_the_list :
    installed_fields optimized_keyed = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  Lemma keyed_only_delete_is_index_work :
    write_at 2 optimized_keyed
    = Some (ERecord
              [("aux_tag",
                 ERecord
                   [("0",
                      ELet (mem "0") "acc"
                        (EOptMatch (EBinop OLookup (mem "1") (q_fld "k"))
                           (EVar "acc") "tup"
                           (EOptMatch (EBinop OLookup (EVar "acc") (ckey_of_row "tup"))
                              (EVar "acc") "bkt"
                              (EIf (EBinop OEq bucket_without_the_row
                                      (EAtom (AEmptyBag None)))
                                 (EBinop ODelete (EVar "acc") (ckey_of_row "tup"))
                                 (ETernop OInsert (EVar "acc") (ckey_of_row "tup")
                                    bucket_without_the_row)))));
                    ("1", EBinop ODelete (mem "1") (q_fld "k"))])]).
  Proof. vm_compute; reflexivity. Qed.

  (* and the read is still the one probe *)
  Lemma keyed_only_read_is_one_probe :
    query_at 0 optimized_keyed
    = Some (EACFold AGCount
              (EOptMatch (EBinop OLookup (mem "0") ckey_of_q)
                 (EAtom (AEmptyBag None)) "b" (EVar "b"))).
  Proof. vm_compute; reflexivity. Qed.

  (* ---- and it is all sound ---- *)

  Lemma row_ty_wf : type_wf row_ty.
  Proof. unfold row_ty; repeat constructor; cbn; intuition congruence. Qed.

  Lemma query_ty_wf : type_wf query_ty.
  Proof. unfold query_ty, row_ty; repeat constructor; cbn; intuition congruence. Qed.

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
      exists [("id", TString); ("k1", TString); ("k2", TString); ("v", TString)],
        TString;
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

  Lemma elaborated_keyed_well_typed :
    well_typed init_Gstore init_Genv (elaborated_keyed decls).
  Proof.
    eapply command_typechecker_sound with (c := elaborated_keyed decls).
    1: apply init_Gstore_wf.
    1: apply init_Genv_wf.
    reflexivity.
  Qed.

  Theorem optimized_keyed_sound :
    well_typed init_Gstore init_Genv optimized_keyed /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized_keyed
        = interp_command store env (elaborated_keyed decls).
  Proof.
    unfold optimized_keyed, anno_keyed, elaborated_keyed, prog_keyed_s.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply row_ty_wf
      | apply incl_refl | apply decls_wf | apply elaborated_keyed_well_typed ].
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
