Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Surface fiat2.Constraint fiat2.Substitute fiat2.PrimaryKeyCheck
  fiat2.TransfUtils fiat2.Utils fiat2.FlatmapForms fiat2.TrigramIndexUse
  fiat2.OptimizeAnno.
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
    CAC (("users", (prow_ty, ds)) :: cenv_rm "users" []) O
      pbasics [UniqueDictIdx "id"] icss (pelaborated ds).

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

  (* The index RECORD the installation builds.  One member here, sitting under
     a tag of its own -- which is why every read of the index goes through
     aux_tag and then that tag, exactly as a set or range index's would. *)
  (* "0" because the declared index is now an ordinary member of the record
     and takes the first tag mk_idxs hands out, exactly as a set or range
     index would. *)
  Definition punique_rec_of (tbl : expr) : expr :=
    ERecord [("0", punique_idx_of tbl)].

  Definition pidx : expr := EAccess (EAccess (ELoc "users") "aux_tag") "0".

  (* What the write does to the index now: it reads the stored dictionary and
     puts one row in it, instead of folding over the whole table again.  This
     is the index's own fold body, run once -- the same shape the trigram
     member's insert rule leaves. *)
  Definition punique_insert_of (idx_e row : expr) : expr :=
    ELet idx_e "acc"
      (ELet row "tup"
         (ETernop OInsert (EVar "acc") (EAccess (EVar "tup") "id") (EVar "tup"))).

  (* After: the table is the pair of the list and that index record, every read
     of the table goes through id_tag, and the guard is one lookup in the
     dictionary. *)
  Definition poptimized_expected : command :=
    CLetMut (ERecord [("id_tag", EAtom (ANil (Some prow_ty)));
                      ("aux_tag", punique_rec_of (EAtom (ANil (Some prow_ty))))])
      "users"
      (CIf (EBinop OAnd
              (ELet (EVar "u") "_pk_row"
                 (EBinop OEq
                    (EOptMatch
                       (EBinop OLookup pidx
                          (EAccess (EVar "_pk_row") "id"))
                       (EAtom (AEmptyBag None)) "y"
                       (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "y")))
                    (EAtom (AEmptyBag None))))
              (EAtom (ABool true)))
         (CAssign "users"
            (ERecord
               [("id_tag", EBinop OCons (EVar "u") (EAccess (ELoc "users") "id_tag"));
                ("aux_tag", ERecord [("0", punique_insert_of pidx (EVar "u"))])]))
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

  (* The same pipeline told nothing about the table.  The declared index is
     still INSTALLED -- it is an ordinary index, sound on any table -- so this
     is not the basic phase alone; it is the installation with a use rule that
     never fires. *)
  Definition pinstall_only (ds : list decl) : command :=
    apply_optimize_anno_constrained (width:=width)
      (CAC [] O pbasics [UniqueDictIdx "id"] [] (pelaborated ds))
      pGstore0 pGenv0.

  (* Without the declaration the use rule is the identity, so the pipeline is
     the installation and nothing else.  Asking for this index on a table with
     no declared key therefore costs a dictionary nobody reads: it is still
     sound, and it disables nothing. *)
  Lemma puse_closed_without_decl : poptimized [] = pinstall_only [].
  Proof. reflexivity. Qed.

  (* A key, but on another attribute: the same.  This is the case a rule that
     looked for the guard's syntax would get wrong, since the program does
     carry a primary key check -- just not this index's. *)
  Lemma puse_closed_on_other_key :
    poptimized [DUnique "name"] = pinstall_only [DUnique "name"].
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


  (* ====================================================================
     A read query, not just the write guard.

     The rule the installation brings is not about guards: it matches a
     key-equality filter of the table at bag level, which is what a read of
     one row by its key looks like once the collection phase has annotated
     it.  Here one program does both -- insert if the key is free, then look
     a key up -- so the same rule fires twice.
     ==================================================================== *)

  Definition qGstore0 : ctenv := map.put map.empty "out" (TBag prow_ty).
  Definition qGenv0 : ctenv :=
    map.put (map.put map.empty "u" prow_ty) "k" TInt.

  (* The query is written as a list filter, as one would write it, and
     converted to a bag by the context that consumes it.  push_down_collection
     moves that coercion inside, which is what puts the query in the shape the
     rule matches. *)
  Definition qprog (ds : list decl) : scommand :=
    SLetConstrained "users" prow_ty ds
      (SSeq (SAssign "users" (EBinop OCons (EVar "u") (ELoc "users")) SSkip)
         (SAssign "out"
            (EBagOf (flatmap_filter_list (ELoc "users") "r"
                       (EBinop OEq (EAccess (EVar "r") "id") (EVar "k")) "r"
                       (Some prow_ty) (Some prow_ty)))
            SSkip)).

  Definition qelaborated (ds : list decl) : command :=
    elab [] (get_free_vars qGenv0) (qprog ds).

  Definition qanno (ds : list decl) (icss : list (list index_choice)) : canno_command :=
    CAC (("users", (prow_ty, ds)) :: cenv_rm "users" []) O
      pbasics [UniqueDictIdx "id"] icss (qelaborated ds).

  Definition qoptimized (ds : list decl) : command :=
    apply_optimize_anno_constrained (width:=width) (qanno ds []) qGstore0 qGenv0.

  Compute (qelaborated [DUnique "id"]).
  Compute (qoptimized [DUnique "id"]).

  (* The probe the rule leaves behind: the bag of rows stored at the key,
     which the declaration guarantees holds at most one row. *)
  Definition qprobe (k : expr) : expr :=
    EOptMatch (EBinop OLookup pidx k)
      (EAtom (AEmptyBag None)) "y"
      (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "y")).

  Definition qoptimized_expected : command :=
    CLetMut (ERecord [("id_tag", EAtom (ANil (Some prow_ty)));
                      ("aux_tag", punique_rec_of (EAtom (ANil (Some prow_ty))))])
      "users"
      (CSeq
         (* the write guard: one probe *)
         (CIf (EBinop OAnd
                 (ELet (EVar "u") "_pk_row"
                    (EBinop OEq (qprobe (EAccess (EVar "_pk_row") "id"))
                       (EAtom (AEmptyBag None))))
                 (EAtom (ABool true)))
            (CAssign "users"
               (ERecord
                  [("id_tag", EBinop OCons (EVar "u") (EAccess (ELoc "users") "id_tag"));
                   ("aux_tag", ERecord [("0", punique_insert_of pidx (EVar "u"))])]))
            CSkip)
         (* and the read query: the same probe, at the key the query asks for *)
         (CAssign "out" (qprobe (EVar "k")))).

  Lemma qoptimized_is : qoptimized [DUnique "id"] = qoptimized_expected.
  Proof. reflexivity. Qed.

  Lemma qGstore0_wf : tenv_wf qGstore0.
  Proof.
    unfold qGstore0; apply tenv_wf_step;
      [ apply tenv_wf_empty | constructor; apply prow_ty_wf ].
  Qed.

  Lemma qGenv0_wf : tenv_wf qGenv0.
  Proof.
    unfold qGenv0; apply tenv_wf_step;
      [ apply tenv_wf_step; [ apply tenv_wf_empty | apply prow_ty_wf ]
      | constructor ].
  Qed.

  Theorem qoptimized_sound :
      well_typed qGstore0 qGenv0 (qelaborated [DUnique "id"]) ->
      well_typed qGstore0 qGenv0 qoptimized_expected /\
        forall (store env : clocals),
          locals_wf qGstore0 store -> locals_wf qGenv0 env ->
          interp_command store env qoptimized_expected
          = interp_command store env (qelaborated [DUnique "id"]).
  Proof.
    intros H_wt. rewrite <- qoptimized_is.
    unfold qoptimized, qanno, qelaborated, qprog in *.
    apply elab_apply_optimize_anno_constrained_sound;
      [ apply qGstore0_wf | apply qGenv0_wf | apply prow_ty_wf
      | apply incl_refl | apply pdecl_wf_unique_id | exact H_wt ].
  Qed.

  (* ====================================================================
     The write guard as a set membership test, with no declaration at all.

     "Is there already a row with this key" does not depend on how many such
     rows there are, so it does not need the key-to-row dictionary -- the SET
     of the table's keys answers it, and that set is sound for every table.
     So this pipeline installs no declared index: the constrained choice is
     None, the only index is SetAgg, and the rewrite that gets the program
     there is an ordinary basic rewrite.

     The same program as above, then, with different choices.  What the
     declaration buys is not the check; it is the read that returns the row.
     ==================================================================== *)

  Definition mbasics : list basic_transf := [FilterEmptyToSetMem].

  Definition manno (ds : list decl) : canno_command :=
    CAC (("users", (prow_ty, ds)) :: cenv_rm "users" []) O
      mbasics [] [[SetAgg "id"]] (pelaborated ds).

  Definition moptimized (ds : list decl) : command :=
    apply_optimize_anno_constrained (width:=width) (manno ds) pGstore0 pGenv0.

  Compute (moptimized [DUnique "id"]).

  (* the set of the table's keys, which is what SetAgg maintains *)
  Definition mkeys (tbl : expr) : expr :=
    flatmap_proj_set (ESetOf tbl) "x" (EAccess (EVar "x") "id") None.

  Definition moptimized_expected : command :=
    CLetMut (ERecord [("id_tag", EAtom (ANil (Some prow_ty)));
                      ("aux_tag",
                        ERecord [("0", mkeys (EAtom (ANil (Some prow_ty))))])])
      "users"
      (CIf (EBinop OAnd
              (ELet (EVar "u") "_pk_row"
                 (* the scan is gone: one membership test *)
                 (EUnop ONot
                    (EBinop OSetMem
                       (EAccess (EAccess (ELoc "users") "aux_tag") "0")
                       (EAccess (EVar "_pk_row") "id"))))
              (EAtom (ABool true)))
         (CAssign "users"
            (ERecord
               [("id_tag", EBinop OCons (EVar "u") (EAccess (ELoc "users") "id_tag"));
                (* and the set is kept up to date by one insert, not refolded *)
                ("aux_tag",
                  ERecord
                    [("0", EBinop OSetInsert
                             (EAccess (EAccess (ELoc "users") "aux_tag") "0")
                             (EAccess (EVar "u") "id"))])]))
         CSkip).

  Lemma moptimized_is : moptimized [DUnique "id"] = moptimized_expected.
  Proof. reflexivity. Qed.

  (* And it is sound with no premise about the declarations at all -- not even
     the one the gated layer needs -- because this pipeline consults none. *)
  Theorem moptimized_sound :
      well_typed pGstore0 pGenv0 (pelaborated [DUnique "id"]) ->
      well_typed pGstore0 pGenv0 moptimized_expected /\
        forall (store env : clocals),
          locals_wf pGstore0 store -> locals_wf pGenv0 env ->
          interp_command store env moptimized_expected
          = interp_command store env (pelaborated [DUnique "id"]).
  Proof.
    intros H_wt. rewrite <- moptimized_is.
    unfold moptimized, manno.
    apply apply_all_transfs_constrained_None_sound;
      [ apply pGstore0_wf | apply pGenv0_wf | exact H_wt ].
  Qed.

  (* ------------------------------------------------------------------
     One record, both kinds of index.

     This is what folding the declared index into index_choice buys.  Before,
     a declared table could carry ONLY the declared index: the second layer
     installed its own record on a table whose is_tbl_ty was already false,
     so it did nothing (punconstrained_layer_after above pins exactly that).
     Now the declared member and an ordinary one are members of the same
     record, chosen in the same list, installed by the same transformation.
     ------------------------------------------------------------------ *)
  Definition banno (ds : list decl) : canno_command :=
    CAC (("users", (prow_ty, ds)) :: cenv_rm "users" []) O
      pbasics [UniqueDictIdx "id"; SetAgg "id"] [] (pelaborated ds).

  Definition boptimized (ds : list decl) : command :=
    apply_optimize_anno_constrained (width:=width) (banno ds) pGstore0 pGenv0.

  (* The table is now a record of the list, the key-to-row dictionary at tag
     "0", and the set of keys at tag "1". *)
  Compute (boptimized [DUnique "id"]).

  (* Both members really went in: the table's index field is a record holding
     the key-to-row dictionary at "0" and the set of keys at "1".  Only the
     initializer is pinned -- that is where the record's shape is decided. *)
  Lemma boptimized_installs_both :
    exists rest,
      boptimized [DUnique "id"]
      = CLetMut
          (ERecord [("id_tag", EAtom (ANil (Some prow_ty)));
                    ("aux_tag",
                      ERecord [("0", punique_idx_of (EAtom (ANil (Some prow_ty))));
                               ("1", mkeys (EAtom (ANil (Some prow_ty))))])])
          "users" rest.
  Proof. eexists; reflexivity. Qed.

  (* And the mixed record is sound, on the same premise as before: that the
     cenv describes the program.  Nothing is assumed about which choices were
     made, declared or not. *)
  Theorem boptimized_sound :
    well_typed pGstore0 pGenv0 (pelaborated [DUnique "id"]) ->
    well_typed pGstore0 pGenv0 (boptimized [DUnique "id"]) /\
      forall (store env : clocals),
        locals_wf pGstore0 store -> locals_wf pGenv0 env ->
        interp_command store env (boptimized [DUnique "id"])
        = interp_command store env (pelaborated [DUnique "id"]).
  Proof.
    intros H_wt. unfold boptimized, banno, pelaborated, pprog in *.
    apply (elab_apply_optimize_anno_constrained_sound (width:=width));
      [ apply pGstore0_wf | apply pGenv0_wf | apply prow_ty_wf
      | apply incl_refl | apply pdecl_wf_unique_id | exact H_wt ].
  Qed.

  (* ------------------------------------------------------------------
     The declared table one level down.

     An ordinary mutable variable encloses the declared one.  The pipeline is
     the same; only the depth it is told to look at changes, and the premise
     with it -- the enclosing initializer has to synthesize, which an integer
     literal does.
     ------------------------------------------------------------------ *)
  Definition nprog (ds : list decl) : scommand :=
    SLetMut (EAtom (AInt 0)) "n"
      (SLetConstrained "users" prow_ty ds
         (SAssign "users" (EBinop OCons (EVar "u") (ELoc "users")) SSkip)).

  Definition nelaborated (ds : list decl) : command :=
    elab [] (get_free_vars pGenv0) (nprog ds).

  Definition nanno (depth : nat) (ds : list decl) : canno_command :=
    CAC [("users", (prow_ty, ds))] depth pbasics [UniqueDictIdx "id"] []
      (nelaborated ds).

  Definition noptimized (depth : nat) (ds : list decl) : command :=
    apply_optimize_anno_constrained (width:=width) (nanno depth ds) pGstore0 pGenv0.

  Compute (noptimized (S O) [DUnique "id"]).

  (* Told to look at the outermost letmut, the layer finds "n" -- which no
     index is a table type of -- and the pipeline is the basic phase alone. *)
  Lemma noptimized_depth_0_is_basics_only :
    noptimized O [DUnique "id"]
    = compose_basic_transfs (map mk_basic_transf pbasics) (nelaborated [DUnique "id"]).
  Proof. reflexivity. Qed.

  (* Told to look one letmut down, it finds the declared table and installs
     the index there. *)
  Lemma noptimized_installs_at_depth_1 :
    exists rest,
      noptimized (S O) [DUnique "id"]
      = CLetMut (EAtom (AInt 0)) "n"
          (CLetMut (ERecord [("id_tag", EAtom (ANil (Some prow_ty)));
                             ("aux_tag", punique_rec_of (EAtom (ANil (Some prow_ty))))])
             "users" rest).
  Proof. eexists; reflexivity. Qed.

  Theorem noptimized_sound :
    well_typed pGstore0 pGenv0 (nelaborated [DUnique "id"]) ->
    well_typed pGstore0 pGenv0 (noptimized (S O) [DUnique "id"]) /\
      forall (store env : clocals),
        locals_wf pGstore0 store -> locals_wf pGenv0 env ->
        interp_command store env (noptimized (S O) [DUnique "id"])
        = interp_command store env (nelaborated [DUnique "id"]).
  Proof.
    intros H_wt. unfold noptimized, nanno, nelaborated, nprog in *.
    apply (elab_apply_optimize_anno_constrained_nested_sound (width:=width)
             "n" (EAtom (AInt 0)) _ [] _ pbasics [UniqueDictIdx "id"] []
             pGstore0 pGenv0 "users" prow_ty [DUnique "id"] TInt (EAtom (AInt 0)));
      [ apply pGstore0_wf | apply pGenv0_wf | apply prow_ty_wf
      | apply incl_refl | apply pdecl_wf_unique_id | reflexivity | exact H_wt ].
  Qed.

  (* ------------------------------------------------------------------
     The pairing a trigram index needs: the inverted index beside the
     primary-key index, in one record.

     The trigram dictionary holds KEYS, not rows, so on its own it can only
     narrow a substring search down to a set of keys.  What turns a key back
     into its row is the primary-key index -- which is why a trigram index is
     only useful on a table that declares a key, and why ONE choice installs
     both members: TrigramIdx brings the primary-key index it leans on.
     Written out below is exactly what the installation builds at "0": the
     fold over rows, the fold over the positions at which the row's text has
     a trigram, and the read-modify-write of the bucket at that trigram.
     ------------------------------------------------------------------ *)
  Definition ptri_at (p : expr) : expr :=
    ETernop OSubstring (EAccess (EVar "tup") "name") p (EAtom (AInt 3)).

  Definition ptrigram_of (tbl : expr) : expr :=
    EFold tbl (EAtom (AEmptyDict None)) "tup" "acc"
      (EFold (EBinop ORange (EAtom (AInt 0))
                (EBinop OMinus
                   (EUnop OLengthString (EAccess (EVar "tup") "name"))
                   (EAtom (AInt 2))))
         (EVar "acc") "pos" "sacc"
         (ETernop OInsert (EVar "sacc") (ptri_at (EVar "pos"))
            (EOptMatch (EBinop OLookup (EVar "sacc") (ptri_at (EVar "pos")))
               (EBinop OSetInsert (EAtom (AEmptySet None))
                  (EAccess (EVar "tup") "id"))
               "bkt"
               (EBinop OSetInsert (EVar "bkt") (EAccess (EVar "tup") "id"))))).

  (* One choice, two members -- and UniqueDictIdx "id" is not among the
     choices, because it would be pointless: the pair's second member is a
     primary-key dictionary carrying all four of that choice's rules
     (trigram_subsumes_unique_dict), so asking for both would build and
     maintain a second copy of the same dictionary for nothing. *)
  Definition tanno (ds : list decl) : canno_command :=
    CAC (("users", (prow_ty, ds)) :: cenv_rm "users" []) O
      pbasics [TrigramIdx "name" "id"] [] (pelaborated ds).

  Definition toptimized (ds : list decl) : command :=
    apply_optimize_anno_constrained (width:=width) (tanno ds) pGstore0 pGenv0.

  Compute (toptimized [DUnique "id"]).

  (* The one choice installs the trigram dictionary at "0" and the
     key-to-row dictionary it points through at "1". *)
  Lemma toptimized_installs_both :
    exists rest,
      toptimized [DUnique "id"]
      = CLetMut
          (ERecord [("id_tag", EAtom (ANil (Some prow_ty)));
                    ("aux_tag",
                      ERecord [("0", ptrigram_of (EAtom (ANil (Some prow_ty))));
                               ("1", punique_idx_of (EAtom (ANil (Some prow_ty))))])])
          "users" rest.
  Proof. eexists; reflexivity. Qed.

  (* And the write no longer recomputes the dictionary.  What the install
     leaves at the write is the index of the EXTENDED table; the maintenance
     rule turns that into the index of the rest, with one row's buckets added
     -- the index's own per-row body, run once.  This is the rewrite as it
     applies to exactly the shape the install produces. *)
  (* one row's trigrams, added to whatever dictionary it is given *)
  Definition ptri_add (idx_e row : expr) : expr :=
    ELet idx_e "acc"
      (ELet row "tup"
         (EFold (EBinop ORange (EAtom (AInt 0))
                   (EBinop OMinus
                      (EUnop OLengthString (EAccess (EVar "tup") "name"))
                      (EAtom (AInt 2))))
            (EVar "acc") "pos" "sacc"
            (ETernop OInsert (EVar "sacc") (ptri_at (EVar "pos"))
               (EOptMatch (EBinop OLookup (EVar "sacc") (ptri_at (EVar "pos")))
                  (EBinop OSetInsert (EAtom (AEmptySet None))
                     (EAccess (EVar "tup") "id"))
                  "bkt"
                  (EBinop OSetInsert (EVar "bkt")
                     (EAccess (EVar "tup") "id")))))).

  Lemma tri_insert_is_incremental :
    cons_to_tri_insert_head "name" "id" "tup" "acc" "pos" "sacc" "bkt"
      (ptrigram_of (EBinop OCons (EVar "u") (EAccess (ELoc "users") "id_tag")))
    = ptri_add (ptrigram_of (EAccess (ELoc "users") "id_tag")) (EVar "u").
  Proof. reflexivity. Qed.

  (* And the whole write, as the pipeline leaves it: NEITHER member is
     recomputed.  The trigram dictionary is the stored one with this row's
     trigrams added, and the primary-key dictionary is the stored one with
     this row's entry put in -- both read through aux_tag rather than folded
     over the table.  The recomputations the two insert rules leave behind
     are what the two use rules turn into those reads, so this is the
     statement that says maintenance actually paid. *)
  (* The write guard, too, is now one probe -- into the SECOND member.  The
     primary-key member of this pair carries the same four rules the
     UniqueDictIdx choice installs, this lookup among them, so the
     uniqueness check that used to scan the table as a bag is the same
     single dictionary probe it is there (qprobe), only read at "1". *)
  Definition tprobe (k : expr) : expr :=
    EOptMatch
      (EBinop OLookup (EAccess (EAccess (ELoc "users") "aux_tag") "1") k)
      (EAtom (AEmptyBag None)) "y"
      (EBinop OBagInsert (EAtom (AEmptyBag None)) (EVar "y")).

  Lemma tri_pair_insert_is_incremental : exists inst,
      toptimized [DUnique "id"]
      = CLetMut inst "users"
          (CIf (EBinop OAnd
                  (ELet (EVar "u") "_pk_row"
                     (EBinop OEq (tprobe (EAccess (EVar "_pk_row") "id"))
                        (EAtom (AEmptyBag None))))
                  (EAtom (ABool true)))
             (CAssign "users"
                (ERecord
                   [("id_tag",
                     EBinop OCons (EVar "u") (EAccess (ELoc "users") "id_tag"));
                    ("aux_tag",
                      ERecord
                        [("0",
                          ptri_add (EAccess (EAccess (ELoc "users") "aux_tag") "0")
                            (EVar "u"));
                         ("1",
                          punique_insert_of
                            (EAccess (EAccess (ELoc "users") "aux_tag") "1")
                            (EVar "u"))])]))
             CSkip).
  Proof. eexists; reflexivity. Qed.

  (* And the pair is sound on the same premise as before: nothing is assumed
     about which indexes were chosen, only that the cenv describes the
     program. *)
  Theorem toptimized_sound :
    well_typed pGstore0 pGenv0 (pelaborated [DUnique "id"]) ->
    well_typed pGstore0 pGenv0 (toptimized [DUnique "id"]) /\
      forall (store env : clocals),
        locals_wf pGstore0 store -> locals_wf pGenv0 env ->
        interp_command store env (toptimized [DUnique "id"])
        = interp_command store env (pelaborated [DUnique "id"]).
  Proof.
    intros H_wt. unfold toptimized, tanno, pelaborated, pprog in *.
    apply (elab_apply_optimize_anno_constrained_sound (width:=width));
      [ apply pGstore0_wf | apply pGenv0_wf | apply prow_ty_wf
      | apply incl_refl | apply pdecl_wf_unique_id | exact H_wt ].
  Qed.

  (* ====================================================================
     The read a trigram index is for: a substring filter.

     The query is written as a list filter and consumed as a set, so the
     collection pushdown is what puts it in the shape the rule matches --
     which is why set_of needed the EIf case bag_of already had.  The index
     answers it in two hops: the bucket at one trigram of the pattern gives a
     set of KEYS, and the key-to-row dictionary turns each one back into its
     row.  The recheck on the way out is not a leftover: a shared trigram is
     necessary for a substring match and not sufficient, so the rows the
     bucket names still have to be filtered.
     ==================================================================== *)

  Definition sGstore0 : ctenv := map.put map.empty "out" (TSet prow_ty).
  Definition sGenv0 : ctenv := map.put (map.put map.empty "u" prow_ty) "p" TString.

  Definition sprog (p : expr) (ds : list decl) : scommand :=
    SLetConstrained "users" prow_ty ds
      (SSeq (SAssign "users" (EBinop OCons (EVar "u") (ELoc "users")) SSkip)
         (SAssign "out"
            (ESetOf (flatmap_filter_list (ELoc "users") "r"
                       (EBinop OStrContains (EAccess (EVar "r") "name") p) "r"
                       (Some prow_ty) (Some prow_ty)))
            SSkip)).

  Definition selaborated (p : expr) (ds : list decl) : command :=
    elab [] (get_free_vars sGenv0) (sprog p ds).

  Definition sanno (p : expr) (ds : list decl) : canno_command :=
    CAC (("users", (prow_ty, ds)) :: cenv_rm "users" []) O
      pbasics [TrigramIdx "name" "id"] [] (selaborated p ds).

  Definition soptimized (p : expr) (ds : list decl) : command :=
    apply_optimize_anno_constrained (width:=width) (sanno p ds) sGstore0 sGenv0.

  Compute (soptimized (EAtom (AString "abc")) [DUnique "id"]).
  Compute (soptimized (EVar "p") [DUnique "id"]).

  (* probe the bucket at g, resolve each key, recheck p *)
  Definition sprobe (g p : expr) : expr :=
    EFlatmap LikeSet
      (EOptMatch (EBinop OLookup (EAccess (EAccess (ELoc "users") "aux_tag") "0") g)
         (EAtom (AEmptySet None)) "b" (EVar "b"))
      "k"
      (EOptMatch (EBinop OLookup (EAccess (EAccess (ELoc "users") "aux_tag") "1")
                    (EVar "k"))
         (EAtom (AEmptySet None)) "y"
         (EIf (EBinop OStrContains (EAccess (EVar "y") "name") p)
            (EBinop OSetInsert (EAtom (AEmptySet None)) (EVar "y"))
            (EAtom (AEmptySet None)))).

  (* the query the pushdown leaves, which is also the fallback below *)
  Definition sscan (p : expr) : expr :=
    flatmap_filter_set (ESetOf (EAccess (ELoc "users") "id_tag")) "r"
      (EBinop OStrContains (EAccess (EVar "r") "name") p) "r"
      (Some prow_ty) (Some prow_ty).

  (* A literal pattern that has a trigram: the trigram is computed at rewrite
     time, and nothing of the scan is left. *)
  Lemma sliteral_probes : exists inst grd,
      soptimized (EAtom (AString "abc")) [DUnique "id"]
      = CLetMut inst "users"
          (CSeq grd
             (CAssign "out"
                (sprobe (EAtom (AString "abc")) (EAtom (AString "abc"))))).
  Proof. do 2 eexists; reflexivity. Qed.

  (* A pattern that is not a literal cannot be measured at rewrite time, so
     the rule emits the test instead: long enough, probe; shorter than a
     trigram, scan.  The fallback is the source query, unchanged -- the
     length condition is a soundness obligation of probe_recheck_eq, not a
     heuristic, so it cannot be dropped the way two mainstream n-gram indexes
     drop it (and silently return nothing). *)
  Lemma sguarded_splits : exists inst grd,
      soptimized (EVar "p") [DUnique "id"]
      = CLetMut inst "users"
          (CSeq grd
             (CAssign "out"
                (EIf (EBinop OLess (EAtom (AInt 2))
                        (EUnop OLengthString (EVar "p")))
                   (sprobe (ETernop OSubstring (EVar "p")
                              (EAtom (AInt 0)) (EAtom (AInt 3)))
                      (EVar "p"))
                   (sscan (EVar "p"))))).
  Proof. do 2 eexists; reflexivity. Qed.

  Lemma sGstore0_wf : tenv_wf sGstore0.
  Proof.
    unfold sGstore0; apply tenv_wf_step;
      [ apply tenv_wf_empty | constructor; apply prow_ty_wf ].
  Qed.

  Lemma sGenv0_wf : tenv_wf sGenv0.
  Proof.
    unfold sGenv0; apply tenv_wf_step;
      [ apply tenv_wf_step; [ apply tenv_wf_empty | apply prow_ty_wf ]
      | constructor ].
  Qed.

  (* and the whole thing -- install, maintenance, and the guarded probe --
     is sound on the same premise as every other pipeline here *)
  Theorem soptimized_sound :
    well_typed sGstore0 sGenv0 (selaborated (EVar "p") [DUnique "id"]) ->
    well_typed sGstore0 sGenv0 (soptimized (EVar "p") [DUnique "id"]) /\
      forall (store env : clocals),
        locals_wf sGstore0 store -> locals_wf sGenv0 env ->
        interp_command store env (soptimized (EVar "p") [DUnique "id"])
        = interp_command store env (selaborated (EVar "p") [DUnique "id"]).
  Proof.
    intros H_wt. unfold soptimized, sanno, selaborated, sprog in *.
    apply (elab_apply_optimize_anno_constrained_sound (width:=width));
      [ apply sGstore0_wf | apply sGenv0_wf | apply prow_ty_wf
      | apply incl_refl | apply pdecl_wf_unique_id | exact H_wt ].
  Qed.

  (* ====================================================================
     A delete, maintained.

     The row that leaves is not in the program -- only its key is -- so the
     rule reads it out of the primary-key member and then walks that row's
     own trigrams, taking its key out of each bucket and dropping a bucket
     that empties.  That is also why this rule, unlike the insert rule, is
     gated on the declaration: without a unique key another row could carry
     the same one, and taking its contributions out of buckets this rule
     never visits would lose rows from the index.
     ==================================================================== *)
  Definition dGenv0 : ctenv := map.put (map.put map.empty "u" prow_ty) "k" TInt.

  Definition dfiltered (tbl_e : expr) : expr :=
    flatmap_filter_list tbl_e "r"
      (EUnop ONot (EBinop OEq (EAccess (EVar "r") "id") (EVar "k"))) "r"
      (Some prow_ty) (Some prow_ty).

  Definition dprog (ds : list decl) : scommand :=
    SLetConstrained "users" prow_ty ds
      (SAssign "users" (dfiltered (ELoc "users")) SSkip).

  Definition delaborated (ds : list decl) : command :=
    elab [] (get_free_vars dGenv0) (dprog ds).

  Definition danno (ds : list decl) : canno_command :=
    CAC (("users", (prow_ty, ds)) :: cenv_rm "users" []) O
      pbasics [TrigramIdx "name" "id"] [] (delaborated ds).

  Definition doptimized (ds : list decl) : command :=
    apply_optimize_anno_constrained (width:=width) (danno ds) pGstore0 dGenv0.

  Compute (doptimized [DUnique "id"]).

  (* the removal, as the rule emits it: the stored dictionary, the row the
     key names, and one fold over that row's trigram positions *)
  Definition dremove (idx_e : expr) : expr :=
    ELet idx_e "acc"
      (EOptMatch
         (EBinop OLookup (EAccess (EAccess (ELoc "users") "aux_tag") "1")
            (EVar "k"))
         (EVar "acc") "tup"
         (EFold (EBinop ORange (EAtom (AInt 0))
                   (EBinop OMinus
                      (EUnop OLengthString (EAccess (EVar "tup") "name"))
                      (EAtom (AInt 2))))
            (EVar "acc") "pos" "sacc"
            (EOptMatch (EBinop OLookup (EVar "sacc") (ptri_at (EVar "pos")))
               (EVar "sacc") "bkt"
               (EIf (EBinop OEq
                       (EBinop OSetDiff (EVar "bkt")
                          (EBinop OSetInsert (EAtom (AEmptySet None))
                             (EAccess (EVar "tup") "id")))
                       (EAtom (AEmptySet None)))
                  (EBinop ODelete (EVar "sacc") (ptri_at (EVar "pos")))
                  (ETernop OInsert (EVar "sacc") (ptri_at (EVar "pos"))
                     (EBinop OSetDiff (EVar "bkt")
                        (EBinop OSetInsert (EAtom (AEmptySet None))
                           (EAccess (EVar "tup") "id")))))))).

  (* The write recomputes NEITHER member: the trigram dictionary reads the
     stored one and takes one row's keys out of it, and the primary-key
     dictionary loses exactly the entry the filter named.  Only the list at
     id_tag is still traversed, which is the table itself. *)
  Lemma dtri_delete_is_incremental : exists inst grd,
      doptimized [DUnique "id"]
      = CLetMut inst "users"
          (CIf grd
             (CAssign "users"
                (ERecord
                   [("id_tag", dfiltered (EAccess (ELoc "users") "id_tag"));
                    ("aux_tag",
                      ERecord
                        [("0",
                          dremove (EAccess (EAccess (ELoc "users") "aux_tag") "0"));
                         ("1",
                          EBinop ODelete
                            (EAccess (EAccess (ELoc "users") "aux_tag") "1")
                            (EVar "k"))])]))
             CSkip).
  Proof. do 2 eexists; reflexivity. Qed.

  Lemma dGenv0_wf : tenv_wf dGenv0.
  Proof.
    unfold dGenv0; apply tenv_wf_step;
      [ apply tenv_wf_step; [ apply tenv_wf_empty | apply prow_ty_wf ]
      | constructor ].
  Qed.

  Theorem doptimized_sound :
    well_typed pGstore0 dGenv0 (delaborated [DUnique "id"]) ->
    well_typed pGstore0 dGenv0 (doptimized [DUnique "id"]) /\
      forall (store env : clocals),
        locals_wf pGstore0 store -> locals_wf dGenv0 env ->
        interp_command store env (doptimized [DUnique "id"])
        = interp_command store env (delaborated [DUnique "id"]).
  Proof.
    intros H_wt. unfold doptimized, danno, delaborated, dprog in *.
    apply (elab_apply_optimize_anno_constrained_sound (width:=width));
      [ apply pGstore0_wf | apply dGenv0_wf | apply prow_ty_wf
      | apply incl_refl | apply pdecl_wf_unique_id | exact H_wt ].
  Qed.

End WithConcreteMaps.
