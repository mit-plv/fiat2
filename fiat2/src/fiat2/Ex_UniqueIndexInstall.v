Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.Utils fiat2.Substitute
  fiat2.IndexTransf fiat2.Constraint fiat2.UniqueDictIndexImpl
  fiat2.UniqueIndexInstall fiat2.PrimaryKeyCheck.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Word.Interface
  coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* An index whose correctness depends on a constraint, installed and used.

   The program is one checked insertion into a table declared with a primary
   key on "id": the guard PrimaryKeyCheck emits decides whether the key is
   free, and the write happens only if it is.  That program maintains the
   key, which is checked_cons_wf.

   transf_to_idx' then installs the dictionary that maps each id to a single
   row.  What is proved here is that the installed program maintains the
   index's *strong* well-formedness -- the index is a faithful key-to-row map
   of the table, which is false for a table with duplicate keys and therefore
   not something to_idx establishes on its own.  It holds because the program
   maintains the key, and the two travel together through
   transf_to_idx'_unique_install.

   run_installed_keeps_unique_idx is the end of the chain: run the installed
   program from the empty table and whatever it leaves at the table satisfies
   idx_wf_unique. *)

Definition row_ty := TRecord [("id", TInt); ("name", TString)].
Definition rt0 := [("id", TInt); ("name", TString)].

(* the variables the index's own fold binds, and the two field names the
   installation pairs *)
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

  (* ---------------------------------------------------------------------
     The program: one checked insertion.
     --------------------------------------------------------------------- *)
  Definition body : command :=
    CIf (fresh_guard "users" "id" "r" (EVar "u"))
      (CAssign "users" (EBinop OCons (EVar "u") (ELoc "users")))
      CSkip.

  Definition Gstore0 : ctenv := map.put map.empty "users" (TList row_ty).
  Definition Genv0 : ctenv := map.put map.empty "u" row_ty.

  Definition Gstore1 : ctenv :=
    map.put map.empty "users" (aux_ty (idx := uidx) uid uaux (TList row_ty)).

  (* the same store the installation lemma names, with the shadowed entry
     collapsed *)
  Lemma Gstore1_eq :
    Gstore1 = map.put Gstore0 "users" (aux_ty (idx := uidx) uid uaux (TList row_ty)).
  Proof.
    unfold Gstore1, Gstore0; symmetry; apply Properties.map.put_put_same.
  Qed.

  Definition installed : command :=
    transf_to_idx' (idx := uidx) uid uaux "users" (get_free_vars Genv0) body.

  (* ---------------------------------------------------------------------
     Well-formedness of the types and of the starting store.
     --------------------------------------------------------------------- *)
  Lemma row_ty_wf : type_wf row_ty.
  Proof. unfold row_ty; repeat constructor; cbn; intuition congruence. Qed.

  Lemma Gstore0_wf : tenv_wf Gstore0.
  Proof.
    unfold Gstore0; apply tenv_wf_step;
      [ apply tenv_wf_empty | constructor; apply row_ty_wf ].
  Qed.

  Lemma Genv0_wf : tenv_wf Genv0.
  Proof.
    unfold Genv0; apply tenv_wf_step; [ apply tenv_wf_empty | apply row_ty_wf ].
  Qed.

  Lemma Gstore1_wf : tenv_wf Gstore1.
  Proof.
    unfold Gstore1; apply tenv_wf_step.
    1: apply tenv_wf_empty.
    1: apply (aux_ty_wf (idx_ok := unique_dict_idx_ok uhole "id" utup uacc utup_neq_uacc));
       [ apply uid_neq_uaux | constructor; apply row_ty_wf | reflexivity ].
  Qed.

  (* The store the installed program starts in: the empty table paired with
     the index of it. *)
  Definition store0 : clocals :=
    map.put map.empty "users" (VRecord [(uaux, VDict nil); (uid, VList nil)]).

  Lemma store0_wf : locals_wf Gstore1 store0.
  Proof.
    unfold Gstore1, store0.
    apply locals_wf_step; [ apply locals_wf_empty | ].
    replace (aux_ty (idx := uidx) uid uaux (TList row_ty))
      with (TRecord [(uaux, TDict TInt row_ty); (uid, TList row_ty)])
      by reflexivity.
    econstructor.
    1: unfold uid, uaux; repeat constructor; cbn; intuition congruence.
    1: unfold uid, uaux; repeat constructor; cbn; intuition congruence.
    1: repeat constructor; cbn; intuition congruence.
  Qed.

  (* ---------------------------------------------------------------------
     The program maintains the declared key.
     --------------------------------------------------------------------- *)
  Lemma body_keeps_key :
    parameterized_wf Gstore0 Genv0
      (value_wf_with_globals (key_holds (locals := clocals) "id" rt0) ["users"])
      (fun _ _ => True) body.
  Proof.
    unfold body, key_holds, rt0.
    eapply checked_cons_wf with (kt := TInt).
    1: apply Gstore0_wf.
    1: apply Genv0_wf.
    1: apply row_ty_wf.
    1: reflexivity.
    1: unfold Gstore0, row_ty; rewrite map.get_put_same; reflexivity.
    1: constructor; unfold Genv0, row_ty; rewrite map.get_put_same; reflexivity.
    1: reflexivity.
    1: constructor.
  Qed.

  (* ---------------------------------------------------------------------
     So the installed program maintains the strong index invariant.
     --------------------------------------------------------------------- *)
  Theorem installed_keeps_unique_idx :
    parameterized_wf Gstore1 Genv0
      (value_wf_with_globals
         (unique_aux_pre uhole "id" utup uacc uid uaux (locals := clocals) rt0)
         ["users"])
      (fun _ _ => True) installed.
  Proof.
    rewrite Gstore1_eq; unfold installed.
    eapply (transf_to_idx'_unique_install uhole "id" utup uacc utup_neq_uacc
              uid uaux uid_neq_uaux "users" rt0 TInt body (get_free_vars Genv0)
              Gstore0 Genv0 (fun (_ _ : clocals) => True) (fun (_ _ : clocals) => True));
      [ apply row_ty_wf
      | reflexivity
      | unfold Gstore0, row_ty; rewrite map.get_put_same; reflexivity
      | apply incl_refl
      | apply Gstore0_wf
      | apply Genv0_wf
      | intros; exact I
      | apply body_keeps_key ].
  Qed.

  (* ---------------------------------------------------------------------
     And whatever the installed program leaves at the table is an index
     whose correctness depends on the key.
     --------------------------------------------------------------------- *)
  Theorem run_installed_keeps_unique_idx : forall (env : clocals) (v : value),
      locals_wf Genv0 env ->
      map.get (interp_command store0 env installed) "users" = Some v ->
      unique_aux_wf uhole "id" utup uacc uid uaux (locals := clocals) v.
  Proof.
    intros env v H_env E_tbl.
    eapply (installed_unique_aux_wf uhole "id" utup uacc uid uaux uid_neq_uaux
              "users" rt0 TInt Gstore1).
    1: apply row_ty_wf.
    1: reflexivity.
    1: unfold Gstore1; rewrite map.get_put_same; reflexivity.
    1:{ eapply command_type_sound.
        1: eapply parameterized_wf__well_typed, installed_keeps_unique_idx.
        1: apply Gstore1_wf.
        1: apply Genv0_wf.
        1: apply store0_wf.
        1: exact H_env. }
    2: exact E_tbl.
    (* the invariant holds at the start and is preserved *)
    eapply parameterized_wf__preserve_P.
    1: apply Gstore1_wf.
    1: apply Genv0_wf.
    1: apply installed_keeps_unique_idx.
    1: exact I.
    1: apply store0_wf.
    1: exact H_env.
    unfold holds_for_all_entries, value_wf_with_globals; intros k v' E_k.
    constructor; auto.
    destruct (String.eqb k "users") eqn:E_ku;
      rewrite ?eqb_eq, ?eqb_neq in *; subst; [ | left; assumption ].
    right.
    unfold store0 in E_k; rewrite map.get_put_same in E_k.
    injection E_k as E_v; subst.
    unfold unique_aux_pre, aux_wf, at_id_tag, key_holds, uid, uaux; cbn.
    split; [ reflexivity | apply constrs_hold_nil ].
  Qed.

  (* ---------------------------------------------------------------------
     The same thing by computation, for inspection: the installed program,
     and what three attempted insertions leave behind.
     --------------------------------------------------------------------- *)
  Compute installed.

  Definition row (i : Z) (n : string) : value :=
    VRecord [("id", VInt i); ("name", VString n)].

  Definition run (rows : list value) : clocals :=
    fold_left (fun st r => interp_command st (map.put map.empty "u" r) installed)
      rows store0.

  (* the second row reuses id 1, so it is rejected *)
  Definition demo_result : clocals := run [row 1 "a"; row 1 "z"; row 2 "b"].

  Compute (map.get demo_result "users").
End WithConcreteMaps.
