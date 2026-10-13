Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.OptimizeAnno.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* The declared index inside the pipeline the other indexes go through.

   apply_optimize_anno_constrained is apply_optimize_anno with two extra
   arguments: the declaration environment the program was elaborated with, and
   which declared index to install.  Everything else is as before -- a list of
   basic rewrites and a list of index choices, and no claim about either.

   What this file shows is that the three phases compose: the basic rewrites
   run first and keep the gate's premise, the declared index is then installed
   where the declarations allow it, and the unconstrained index layer runs last
   on the result. *)

Section WithConcreteMaps.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string (value (width:=width)) := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Definition prow_ty := TRecord [("id", TInt); ("name", TString)].

  (* one checked insertion, with whatever is declared about the table *)
  Definition pprog (ds : list decl) : scommand :=
    SLetConstrained "users" prow_ty ds
      (SAssign "users" (EBinop OCons (EVar "u") (ELoc "users")) SSkip).

  Definition pGstore0 : ctenv := map.empty.
  Definition pGenv0 : ctenv := map.put map.empty "u" prow_ty.

  Definition pelaborated (ds : list decl) : command :=
    elab [] (get_free_vars pGenv0) (pprog ds).

  (* the basic rewrites the unconstrained examples use *)
  Definition pbasics : list basic_transf :=
    [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

  Definition panno (ds : list decl) (icss : list (list index_choice)) : canno_command :=
    CAC (("users", (prow_ty, ds)) :: cenv_rm "users" [])
      pbasics (Some (UniqueDictIdx "id")) icss (pelaborated ds).

  Definition poptimized (ds : list decl) : command :=
    apply_optimize_anno_constrained (width:=width) (panno ds []) pGstore0 pGenv0.

  (* Declared key on "id": the dictionary goes in, and the guard that decided
     whether the key was free -- a scan of the table -- is one lookup in it. *)
  Compute (poptimized [DUnique "id"]).

  (* The same, machine-checked rather than read off the output above.

     Before: the guard iterates over the whole table and keeps the rows whose
     id matches the new row's, then tests that there are none. *)
  Definition pelaborated_expected : command :=
    CLetMut (EAtom (ANil (Some prow_ty))) "users"
      (CIf (EBinop OAnd
              (ELet (EVar "u") "_pk_row"
                 (EBinop OEq
                    (EFlatmap LikeBag (EBagOf (ELoc "users")) "_pk_scan"
                       (EIf (EBinop OEq (EAccess (EVar "_pk_scan") "id")
                               (EAccess (EVar "_pk_row") "id"))
                          (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "_pk_scan"))
                          (EAtom (AEmptyBag None))))
                    (EAtom (AEmptyBag None))))
              (EAtom (ABool true)))
         (CAssign "users" (EBinop OCons (EVar "u") (ELoc "users")))
         CSkip).

  Lemma pelaborated_is : pelaborated [DUnique "id"] = pelaborated_expected.
  Proof. reflexivity. Qed.

  (* The index that is installed is the unique one: each id maps to THE row.
     DictIndexImpl's to_idx reads the bucket already at the key and
     OBagInsert's into it; this one inserts the row itself, which is only
     faithful to the table because the key is declared. *)
  Definition punique_idx_of (tbl : expr) : expr :=
    EFold tbl (EAtom (AEmptyDict None)) "tup" "acc"
      (ETernop OInsert (EVar "acc") (EAccess (EVar "tup") "id") (EVar "tup")).

  (* After: the table is the pair of the list and that dictionary, every read
     of the table goes through id_tag, and the guard is one lookup in
     aux_tag. *)
  Definition poptimized_expected : command :=
    CLetMut (ERecord [("id_tag", EAtom (ANil (Some prow_ty)));
                      ("aux_tag", punique_idx_of (EAtom (ANil (Some prow_ty))))])
      "users"
      (CIf (EBinop OAnd
              (ELet (EVar "u") "_pk_row"
                 (EBinop OEq
                    (EOptMatch
                       (EBinop OLookup (EAccess (ELoc "users") "aux_tag")
                          (EAccess (EVar "_pk_row") "id"))
                       (EAtom (AEmptyBag None)) "y"
                       (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "y")))
                    (EAtom (AEmptyBag None))))
              (EAtom (ABool true)))
         (CAssign "users"
            (ERecord
               [("id_tag", EBinop OCons (EVar "u") (EAccess (ELoc "users") "id_tag"));
                ("aux_tag",
                  punique_idx_of (EBinop OCons (EVar "u") (EAccess (ELoc "users") "id_tag")))]))
         CSkip).

  Lemma poptimized_is : poptimized [DUnique "id"] = poptimized_expected.
  Proof. reflexivity. Qed.

  (* So the two differ: the pipeline did something, and what it did was install
     and use the declared index. *)
  Lemma poptimized_neq_pelaborated :
    poptimized [DUnique "id"] <> pelaborated [DUnique "id"].
  Proof.
    rewrite poptimized_is, pelaborated_is.
    unfold poptimized_expected, pelaborated_expected.
    intro H; injection H as H_init _; discriminate H_init.
  Qed.

  (* Without the declaration the declared index is not installed, and what is
     left is exactly the basic phase: the pipeline does what it would have done
     with no constrained choice at all. *)
  Lemma pgate_closed_without_decl :
    poptimized [] = compose_basic_transfs (map mk_basic_transf pbasics) (pelaborated []).
  Proof. reflexivity. Qed.

  (* A key, but on another attribute: the same.  This is the case a gate that
     looked for the guard's syntax would get wrong. *)
  Lemma pgate_closed_on_other_key :
    poptimized [DUnique "name"]
    = compose_basic_transfs (map mk_basic_transf pbasics) (pelaborated [DUnique "name"]).
  Proof. reflexivity. Qed.

  (* The unconstrained layer still runs, and finds nothing left to do on a
     table the declared index already owns: its is_tbl_ty is false of the
     record the installation leaves behind. *)
  Lemma punconstrained_layer_after :
    apply_optimize_anno_constrained (width:=width) (panno [DUnique "id"] [[DictIdx "id"]]) pGstore0 pGenv0
    = poptimized [DUnique "id"].
  Proof. reflexivity. Qed.

  (* And the whole thing is sound. *)
  Lemma prow_ty_wf : type_wf prow_ty.
  Proof.
    unfold prow_ty. repeat constructor; cbn; intuition auto; try discriminate.
  Qed.

  Lemma pGenv0_wf : tenv_wf pGenv0.
  Proof.
    unfold pGenv0. apply tenv_wf_step; [ apply tenv_wf_empty | apply prow_ty_wf ].
  Qed.

  Lemma pGstore0_wf : tenv_wf pGstore0.
  Proof. apply tenv_wf_empty. Qed.

  Lemma pdecl_wf_unique_id : Forall (decl_wf prow_ty) [DUnique "id"].
  Proof.
    constructor; [ | constructor ].
    cbn [decl_wf]. exists [("id", TInt); ("name", TString)], TInt.
    split; reflexivity.
  Qed.

  Theorem poptimized_sound : forall icss,
      well_typed pGstore0 pGenv0 (pelaborated [DUnique "id"]) ->
      well_typed pGstore0 pGenv0
        (apply_optimize_anno_constrained (width:=width) (panno [DUnique "id"] icss) pGstore0 pGenv0) /\
        forall (store env : clocals),
          locals_wf pGstore0 store -> locals_wf pGenv0 env ->
          interp_command store env
            (apply_optimize_anno_constrained (width:=width) (panno [DUnique "id"] icss) pGstore0 pGenv0)
          = interp_command store env (pelaborated [DUnique "id"]).
  Proof.
    intros icss H_wt. unfold panno, pelaborated, pprog in *.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply pGstore0_wf | apply pGenv0_wf | apply prow_ty_wf
      | apply incl_refl | apply pdecl_wf_unique_id | exact H_wt ].
  Qed.


  (* And the soundness claim, restated on those two explicit programs: the one
     that probes the declared index computes what the one that scans the table
     computes. *)
  Corollary poptimized_expected_sound :
      well_typed pGstore0 pGenv0 pelaborated_expected ->
      well_typed pGstore0 pGenv0 poptimized_expected /\
        forall (store env : clocals),
          locals_wf pGstore0 store -> locals_wf pGenv0 env ->
          interp_command store env poptimized_expected
          = interp_command store env pelaborated_expected.
  Proof.
    rewrite <- poptimized_is, <- pelaborated_is.
    unfold poptimized; apply poptimized_sound.
  Qed.

End WithConcreteMaps.
