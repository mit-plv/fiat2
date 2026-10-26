Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.FlatmapForms fiat2.OptimizeAnno fiat2.Selector.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* A FOREIGN-KEY JOIN.  IT IS ALREADY INDEXED, AND THIS FILE PINS THAT.

   With the relational constructs gone, a join is a nested flatmap:

     [ {o.oid, c.name} | o <- orders, c <- custs, c.cid == o.cust ]

   The inner flatmap filters `custs` by the join condition and builds the
   output row, so its body is `if p then [record ...] else []` -- it filters
   AND projects at once, which is the shape no INDEX rule matches.

   This file was written expecting that to leave the inner loop a scan.  It
   does not.  `inner_loop_is_a_probe` pins the inner loop as ONE PROBE of the
   declared-key member, so the join is linear in the orders and not
   quadratic, and the customer list is erased.  The reason is
   `if_nil_into_flatmap_head` (FlatmapTransf.v), which splits exactly
   this shape at LikeList and is already in the standard basics list: by the
   time the index rules look, the filter and the projection are two flatmaps
   and the filter is in the shape they read.

   `both_configurations_agree` pins the other half, which is the honest part:
   adding SplitFilterProj to the pipeline changes this program NOT AT ALL.
   That rule is the bag-level counterpart of the same split, and a join
   written as a list comprehension never reaches bag level with the `if`
   still inside, so the list-level rule claims it first.  The two rules
   overlap in intent and not in reach; the witness that needs the bag-level
   one is eval/Sat4j_LiteralStorage.v, whose five projection reads arrive at
   bag level through an aggregate over `EBagOf`.

   So the limit worth stating about joins is NOT the filtering projection.
   It is the ORDER OF THE CONDITIONS, and Ex_Triangle is the witness: a
   three-way self-join whose innermost body is four nested ifs, which it
   reaches its lookups through only by a hand-ordered chain of
   SwapIfNil / SwapFlatmapIf / IfNilIntoFlatmap repeated once per nested if,
   written out per configuration.  The deterministic selector emits none of
   those chains (`basics_of`, Selector.v), which is why no join appears in
   SelectorTests.v -- the join examples' configurations are hand-written, and
   this file's is the only one the selector's own basics list would produce.

   The shape is also the one gap in the Cozy comparison that the selected
   subjects do not cover: their `select-flatmap` and `listcomp-flatmap` examples are
   value-typed multi-collection joins (comparison/cozy/README.md), and this is
   that shape with a declared key on the inner relation.

   Faithfulness: `orders` is an input list rather than a second table, because
   nothing here indexes it -- the join drives from it.  `custs` is the table,
   and its key is declared, which is what makes one matching row sound.  The
   join is counted rather than returned, so nothing observes the order of the
   result and the collection phase is free to relax both levels to bags. *)

Definition cust_ty :=
  TRecord (record_sort [("cid", TInt); ("name", TString)]).

Definition order_ty :=
  TRecord (record_sort [("oid", TInt); ("cust", TInt)]).

Definition query_ty :=
  TRecord (record_sort [("kind", TInt); ("new_cust", cust_ty)]).

Section WithConcreteMaps.
  Notation value := (value).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* The join, as a programmer writes it with no index: a list comprehension
     over the two collections, kept where the keys match.  It is counted, so
     nothing observes the order of the result and the collection phase is
     free to relax both levels to bags. *)
  Definition join_count : expr :=
    EACFold AGCount
      (EBagOf
         (EFlatmap LikeList (EVar "orders_tbl") "o"
         (EFlatmap LikeList (ELoc "custs") "c"
            (EIf (EBinop OEq (EAccess (EVar "c") "cid") (EAccess (EVar "o") "cust"))
               (EBinop OCons
                  (ERecord [("oid", EAccess (EVar "o") "oid");
                            ("name", EAccess (EVar "c") "name")])
                  (EAtom (ANil None)))
               (EAtom (ANil None)))))).

  Definition report (e : expr) : scommand :=
    SLet e "n"
      (SAssign "outputs"
         (EBinop OCons (EUnop OIntToString (EVar "n")) (ELoc "outputs")) SSkip).

  Definition prog_s (ds : list decl) : scommand :=
    SLetConstrained "custs" cust_ty ds
      (SForeach (EVar "queries") "q"
         (SIf (EBinop OEq (EAccess (EVar "q") "kind") (EAtom (AInt 0)))
            (SAssign "custs"
               (EBinop OCons (EAccess (EVar "q") "new_cust") (ELoc "custs")) SSkip)
            (report join_count))).

  Definition init_Gstore : ctenv :=
    map.put map.empty "outputs" (TList TString).

  Definition init_Genv : ctenv :=
    map.put (map.put map.empty "orders_tbl" (TList order_ty))
      "queries" (TList query_ty).

  Definition elaborated (ds : list decl) : command :=
    elab [] (get_free_vars init_Genv) (prog_s ds).

  Definition decls := [DUnique "cid"].

  (* The configuration the development had before this file: the collection
     phase and nothing that can see a filtering projection. *)
  Definition basics_unsplit : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  (* SplitFilterProj goes FIRST in the list and therefore runs LAST, after
     the collection phase has left the bag-level flatmap its pattern reads. *)
  Definition basics_split : list basic_transf :=
    [SplitFilterProj; PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition anno_unsplit : canno_command :=
    CAC (("custs", (cust_ty, decls)) :: cenv_rm "custs" []) O
      basics_unsplit [UniqueDictIdx "cid"] [] (elaborated decls).

  Definition anno_split : canno_command :=
    CAC (("custs", (cust_ty, decls)) :: cenv_rm "custs" []) O
      basics_split [UniqueDictIdx "cid"] [] (elaborated decls).

  Definition optimized_unsplit : command :=
    apply_optimize_anno_constrained anno_unsplit init_Gstore init_Genv.

  Definition optimized_split : command :=
    apply_optimize_anno_constrained anno_split init_Gstore init_Genv.

  Definition installed_fields (c : command) : list string :=
    match c with
    | CLetMut (ERecord l) _ _ => List.map fst l
    | _ => []
    end.

  (* ------------------------------------------------------------------
     What the pipeline produced. *)

  (* the read sits in the else-arm of the kind dispatch *)
  Fixpoint read_of (c : command) : option expr :=
    match c with
    | CLetMut _ _ c' => read_of c'
    | CForeach _ _ c' => read_of c'
    | CIf _ _ els => read_of els
    | CLet e _ _ => Some e
    | _ => None
    end.

  (* one row, or none, out of the declared-key member *)
  Definition probe (k : expr) : expr :=
    EOptMatch (EBinop OLookup (EAccess (EAccess (ELoc "custs") "aux_tag") "0") k)
      (EAtom (AEmptyBag None)) "y"
      (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "y")).

  (* The join, as the optimizer leaves it: drive the orders, and for each
     one probe the customers.  The inner collection is no longer the table. *)
  Definition join_expected : expr :=
    EACFold AGCount
      (EFlatmap LikeBag (EBagOf (EVar "orders_tbl")) "o"
         (EFlatmap LikeBag (probe (EAccess (EVar "o") "cust")) "c"
            (EBinop OBagInsert (EAtom (AEmptyBag None))
               (ERecord [("oid", EAccess (EVar "o") "oid");
                         ("name", EAccess (EVar "c") "name")])))).

  Lemma inner_loop_is_a_probe :
    read_of optimized_unsplit = Some join_expected.
  Proof. vm_compute; reflexivity. Qed.

  (* Nothing reads the customer list once the inner loop is a probe, so the
     field is erased and the table IS its index. *)
  Lemma join_erases_the_list :
    installed_fields optimized_unsplit = ["aux_tag"].
  Proof. vm_compute; reflexivity. Qed.

  (* And the honest half: the bag-level rule changes this program not at all.
     The list-level if_nil_into_flatmap_head claims the shape first. *)
  Lemma both_configurations_agree :
    optimized_split = optimized_unsplit.
  Proof. vm_compute; reflexivity. Qed.

  (* ---- soundness, for both configurations ---- *)

  Lemma cust_ty_wf : type_wf cust_ty.
  Proof. unfold cust_ty. repeat constructor; cbn; intuition congruence. Qed.

  Lemma order_ty_wf : type_wf order_ty.
  Proof. unfold order_ty. repeat constructor; cbn; intuition congruence. Qed.

  Lemma query_ty_wf : type_wf query_ty.
  Proof.
    unfold query_ty, cust_ty. repeat constructor; cbn; intuition congruence.
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
      [ apply tenv_wf_step;
        [ apply tenv_wf_empty | constructor; apply order_ty_wf ]
      | constructor; apply query_ty_wf ].
  Qed.

  Lemma decls_wf : Forall (decl_wf (tenv:=ctenv) cust_ty) decls.
  Proof.
    unfold decls, cust_ty; cbn [decl_wf].
    repeat constructor;
      exists [("cid", TInt); ("name", TString)], TInt; split; reflexivity.
  Qed.

  Lemma elaborated_well_typed :
    well_typed init_Gstore init_Genv (elaborated decls).
  Proof.
    eapply command_typechecker_sound with (c := elaborated decls).
    1: apply init_Gstore_wf.
    1: apply init_Genv_wf.
    reflexivity.
  Qed.

  Theorem optimized_unsplit_sound :
    well_typed init_Gstore init_Genv optimized_unsplit /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized_unsplit
        = interp_command store env (elaborated decls).
  Proof.
    unfold optimized_unsplit, anno_unsplit, elaborated, prog_s.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply cust_ty_wf
      | apply incl_refl | apply decls_wf | apply elaborated_well_typed ].
  Qed.

  Theorem optimized_split_sound :
    well_typed init_Gstore init_Genv optimized_split /\
      forall (store env : clocals),
        locals_wf init_Gstore store -> locals_wf init_Genv env ->
        interp_command store env optimized_split
        = interp_command store env (elaborated decls).
  Proof.
    unfold optimized_split, anno_split, elaborated, prog_s.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply init_Gstore_wf | apply init_Genv_wf | apply cust_ty_wf
      | apply incl_refl | apply decls_wf | apply elaborated_well_typed ].
  Qed.
End WithConcreteMaps.
