Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.Utils fiat2.Substitute
  fiat2.IndexTransf fiat2.Constraint fiat2.UniqueDictIndexImpl
  fiat2.UniqueIndexInstall fiat2.UniqueIndexGate fiat2.UniqueIndexUse
  fiat2.Surface.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface
  coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* The gate fires on the declarations and on nothing else.

   Three surface programs, identical but for what they declare about the
   table.  The index is the key-to-row dictionary on "id", so the gate fires
   on the first and is the identity on the other two -- and the one that
   declares a key on "name" is the case that matters, since it has a primary
   key, just not the one this index is built on.

   The programs are not contrived to make the gate's pattern appear or
   disappear: the pattern is in the cenv, and the three differ only there. *)

Definition row_ty := TRecord [("id", TInt); ("name", TString)].

Definition uhole := "hole".
Definition utup := "tup".
Definition uacc := "acc".
Definition uid := "id_tag".
Definition uaux := "aux_tag".

Lemma utup_neq_uacc : utup <> uacc.
Proof. unfold utup, uacc; intro H; discriminate H. Qed.

Lemma uid_neq_uaux : uid <> uaux.
Proof. unfold uid, uaux; intro H; discriminate H. Qed.

Section WithConcreteMaps.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  Local Open Scope string.

  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.

  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  Notation uidx := (unique_dict_idx uhole "id" utup uacc).

  (* one checked insertion, with whatever is declared about the table *)
  Definition prog (ds : list decl) : scommand :=
    SLetConstrained "users" row_ty ds
      (SAssign "users" (EBinop OCons (EVar "u") (ELoc "users")) SSkip).

  Definition Gstore0 : ctenv := map.empty.
  Definition Genv0 : ctenv := map.put map.empty "u" row_ty.

  Definition inner_cenv (ds : list decl) : cenv := [("users", (row_ty, ds))].

  Definition elaborated (ds : list decl) : command :=
    elab [] (get_free_vars Genv0) (prog ds).

  (* The rewrites that run below the installation.  The identity is enough to
     show what the gate does: the question here is whether the index is
     installed at all, which is what the declarations decide. *)
  Definition no_transf : string -> command -> command := fun _ => id.

  Lemma no_transf_aug_transf_sound : forall is_tbl_ty aux_ty aux_wf,
      aug_transf_sound (locals:=clocals) is_tbl_ty aux_ty aux_wf no_transf.
  Proof.
    unfold aug_transf_sound, no_transf, id; intros; repeat split; auto.
  Qed.

  Definition gated (ds : list decl) : command :=
    apply_unique_idx_transfs uhole "id" utup uacc uid uaux
      (inner_cenv ds) no_transf Gstore0 Genv0 (elaborated ds).

  (* Declared key on "id": the index goes in.  The table now holds a record
     pairing the list with the dictionary, and every read of it goes through
     the id_tag field. *)
  Compute (gated [DUnique "id"]).

  (* No declaration: identity. *)
  Lemma gate_closed_without_decl : gated [] = elaborated [].
  Proof. reflexivity. Qed.

  (* A key, but on another attribute: identity.  This is the case a gate that
     looked for the guard's syntax in the program would get wrong, since the
     program does carry a primary key check. *)
  Lemma gate_closed_on_other_key : gated [DUnique "name"] = elaborated [DUnique "name"].
  Proof. reflexivity. Qed.

  (* And where it fires, it is sound -- with no premise about the hints. *)
  Lemma row_ty_wf : type_wf row_ty.
  Proof.
    unfold row_ty. repeat constructor; cbn; intuition auto; try discriminate.
  Qed.

  Lemma Genv0_wf : tenv_wf Genv0.
  Proof.
    unfold Genv0. apply tenv_wf_step; [ apply tenv_wf_empty | apply row_ty_wf ].
  Qed.

  Lemma Gstore0_wf : tenv_wf Gstore0.
  Proof. apply tenv_wf_empty. Qed.

  Lemma decl_wf_unique_id : Forall (decl_wf row_ty) [DUnique "id"].
  Proof.
    constructor; [ | constructor ].
    cbn [decl_wf]. exists [("id", TInt); ("name", TString)], TInt.
    split; reflexivity.
  Qed.

  Theorem gated_sound :
    well_typed Gstore0 Genv0 (elaborated [DUnique "id"]) ->
    well_typed Gstore0 Genv0 (gated [DUnique "id"]) /\
      forall (store env : clocals),
        locals_wf Gstore0 store -> locals_wf Genv0 env ->
        interp_command store env (gated [DUnique "id"])
        = interp_command store env (elaborated [DUnique "id"]).
  Proof.
    intros H_wt. unfold gated, elaborated, inner_cenv, prog in *.
    apply (elab_unique_idx_transfs_sound uhole "id" utup uacc utup_neq_uacc
             uid uaux uid_neq_uaux);
      [ intros; apply no_transf_aug_transf_sound
      | apply Gstore0_wf | apply Genv0_wf | apply row_ty_wf
      | apply incl_refl | apply decl_wf_unique_id | exact H_wt ].
  Qed.

  (* ------------------------------------------------------------------
     And with the rule installed below it, the write guard stops scanning.
     ------------------------------------------------------------------ *)

  Definition uhit := "_pk_hit".
  Definition uix := "u".

  (* The index goes in whatever is declared -- it is an ordinary index, sound
     on any table.  What the declarations decide is whether the use rule may
     fire, and that decision is taken inside the soundness proof, not by the
     transformation. *)
  Definition optimized (ds : list decl) : command :=
    unique_idx_transf (locals := clocals) (word := word)
      uhole "id" utup uacc uid uaux uix uhit (inner_cenv ds) Gstore0 Genv0
      (elaborated ds).

  (* The same pipeline told nothing about the table: the installation alone. *)
  Definition installed (ds : list decl) : command :=
    unique_idx_transf (locals := clocals) (word := word)
      uhole "id" utup uacc uid uaux uix uhit [] Gstore0 Genv0 (elaborated ds).

  (* The quadratic guard -- scan the table, keep the rows whose id matches the
     new row's, test that there are none -- has become one dictionary lookup. *)
  Compute (optimized [DUnique "id"]).

  (* Where the declarations are silent the rule is literally the identity, so
     the pipeline is the installation and nothing else.  A hint asking for
     this index on a table with no declared key therefore costs a dictionary
     nobody reads -- it does not disable anything and it is still sound. *)
  Lemma optimized_without_decl_is_install_only : optimized [] = installed [].
  Proof. reflexivity. Qed.

  (* And the declaration is what introduces the lookup: same installation,
     different program. *)
  Lemma decl_introduces_the_lookup :
    optimized [DUnique "id"] <> installed [DUnique "id"].
  Proof. unfold optimized, installed; cbn; congruence. Qed.

  Theorem optimized_sound :
    well_typed Gstore0 Genv0 (elaborated [DUnique "id"]) ->
    well_typed Gstore0 Genv0 (optimized [DUnique "id"]) /\
      forall (store env : clocals),
        locals_wf Gstore0 store -> locals_wf Genv0 env ->
        interp_command store env (optimized [DUnique "id"])
        = interp_command store env (elaborated [DUnique "id"]).
  Proof.
    intros H_wt. unfold optimized, elaborated, inner_cenv, prog in *.
    apply (elab_unique_idx_transf_sound uhole "id" utup uacc utup_neq_uacc
             uid uaux uid_neq_uaux uix uhit);
      [ apply Gstore0_wf | apply Genv0_wf | apply row_ty_wf
      | apply incl_refl | apply decl_wf_unique_id | exact H_wt ].
  Qed.

End WithConcreteMaps.
