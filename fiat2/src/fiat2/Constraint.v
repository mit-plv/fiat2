Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.TransfSound fiat2.CollectionTransf fiat2.FlatmapForms.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith Lia List.
Import ListNotations.

(* Declared constraints, and the uniqueness constraint that a primary key asks
   for.

   A constraint is an ordinary boolean expression over the mutable variables,
   and a program keeps one standing by writing through CAssignChecked: the
   guard is the constraint, and a write that would break it runs the policy
   instead.  What makes a constraint useful to the optimizer is a pair of
   facts -- a predicate on the stored value, which an index may then assume,
   and a lemma saying the guard decides that predicate.  This file supplies
   the pair for uniqueness, and the lemma that turns it into the per-write
   obligation of parameterized_wf. *)

Section WithWord.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
  Notation value := (value (width:=width)).

  (* Deduplicating a list loses nothing exactly when its elements are already
     distinct, so comparing the two lengths decides NoDup. *)
  Lemma NoDup__list_to_set_length : forall (l : list value),
      NoDup l -> length (list_to_set l) = length l.
  Proof.
    intros. apply Nat.le_antisymm.
    - apply NoDup_incl_length;
        auto using list_to_set_NoDup, list_to_set_incl.
    - apply NoDup_incl_length; auto using list_to_set_incl_r.
  Qed.

  Lemma list_to_set_length__NoDup : forall (l : list value),
      length (list_to_set l) = length l -> NoDup l.
  Proof.
    intros. eapply NoDup_incl_NoDup.
    1: apply list_to_set_NoDup.
    2: apply list_to_set_incl.
    lia.
  Qed.
  Section WithAttr.
    Context (attr : string).

    Notation proj_attr :=
      (fun v => match v with
                | VRecord r => record_proj attr r
                | _ => VUnit
                end).

    (* No two rows of a table agree on attr: what a primary key declares, and
       what a unique index may assume.  A value of the wrong shape fails the
       predicate rather than satisfying it vacuously, so the invariant also
       records that the variable holds a list. *)
    Definition unique_on (v : value) : Prop :=
      match v with
      | VList rows => NoDup (List.map proj_attr rows)
      | _ => False
      end.

    (* A table born empty satisfies the constraint, which is why a constraint
       can be declared along with the table and never has to be checked
       retroactively. *)
    Lemma unique_on_nil : unique_on (VList nil).
    Proof.
      cbn. constructor.
    Qed.

    (* The guard counts the rows and the distinct keys.  Both counts are
       expressions a program could have written itself; nothing about the
       checked assignment is special-cased in the language. *)
    Definition unique_guard (tbl r : string) (kt : type) : expr :=
      EBinop OEq
        (EUnop OLength (ELoc tbl))
        (EUnop OLength
           (ESort LikeSet
              (ESetOf (EFlatmap LikeList (ELoc tbl) r
                         (EBinop OCons (EAccess (EVar r) attr)
                            (EAtom (ANil (Some kt)))))))).

    Section WithMap.
      Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
      Context {locals : map.map string value} {locals_ok : map.ok locals}.

      Lemma interp_unique_guard : forall (store env : locals) tbl r kt rows,
          map.get store tbl = Some (VList rows) ->
          interp_expr store env (unique_guard tbl r kt) =
            VBool (value_eqb
                     (VInt (Z.of_nat (List.length rows)) : value)
                     (VInt (Z.of_nat (List.length
                                        (list_to_set (List.map proj_attr rows)))))).
      Proof.
        intros * H_get. cbn [interp_expr unique_guard].
        unfold get_local. rewrite H_get. clear H_get.
        cbn [interp_unop interp_binop interp_atom].
        do 6 f_equal.
        induction rows as [| a rows IH]; cbn [flat_map List.map]; auto.
        rewrite map.get_put_same. cbn. f_equal; apply IH.
      Qed.

      (* The guard decides the predicate: this is the one fact an index needs
         about a declared uniqueness constraint. *)
      Lemma unique_guard_spec : forall (store env : locals) tbl r kt rows,
          map.get store tbl = Some (VList rows) ->
          interp_expr store env (unique_guard tbl r kt) = VBool true <->
            unique_on (VList rows).
      Proof.
        intros. erewrite interp_unique_guard by eauto.
        unfold unique_on. split; intros.
        1:{ apply list_to_set_length__NoDup.
            rewrite List.length_map.
            lazymatch goal with
              H: VBool _ = VBool _ |- _ => inversion H as [H'] end.
            apply value_eqb_eq in H'. inversion H'. lia. }
        1:{ do 2 f_equal.
            rewrite NoDup__list_to_set_length, List.length_map by assumption.
            unfold value_eqb. rewrite value_compare_refl; reflexivity. }
      Qed.
      Corollary unique_guard_sound : forall (store env : locals) tbl r kt rows,
          map.get store tbl = Some (VList rows) ->
          interp_expr store env (unique_guard tbl r kt) = VBool true ->
          unique_on (VList rows).
      Proof.
        intros * H_get H_guard.
        apply (proj1 (unique_guard_spec store env tbl r kt rows H_get)), H_guard.
      Qed.

      Lemma unique_guard_ty : forall (Gstore Genv : tenv) tbl r kt rt,
          tenv_wf Gstore -> tenv_wf Genv ->
          map.get Gstore tbl = Some (TList (TRecord rt)) ->
          access_record rt attr = Success kt ->
          type_of Gstore Genv (unique_guard tbl r kt) TBool.
      Proof.
        unfold unique_guard; intros.
        assert (type_wf (TRecord rt)) by
          (lazymatch goal with
             Hg: tenv_wf Gstore |- _ => apply Hg in H1; invert_type_wf; auto
           end).
        repeat econstructor; eauto.
        1: rewrite_map_get_put_goal; reflexivity.
        (* the key's type is well formed because the row type is *)
        lazymatch goal with
          H: type_wf (TRecord rt) |- _ => inversion H; subst
        end.
        lazymatch goal with
          H: access_record rt _ = Success _ |- _ => apply access_record_sound in H
        end.
        lazymatch goal with
          H: In _ rt |- _ => apply (in_map snd) in H; cbn in H
        end.
        apply_Forall_In.
      Qed.

      (* A checked write whose guard is the uniqueness constraint keeps the
         constraint standing, whatever expression it assigns.  This is what
         lets a program, rather than the optimizer, establish an invariant that
         an index may then rely on, and it is proved once for the constraint
         rather than once per program. *)
      Lemma unique_checked_assign_wf : forall (Gstore Genv : tenv) tbl r kt rt e policy,
          tenv_wf Gstore -> tenv_wf Genv ->
          map.get Gstore tbl = Some (TList (TRecord rt)) ->
          access_record rt attr = Success kt ->
          type_of Gstore Genv e (TList (TRecord rt)) ->
          parameterized_wf Gstore Genv (value_wf_with_globals unique_on (tbl :: nil)) policy ->
          parameterized_wf Gstore Genv (value_wf_with_globals unique_on (tbl :: nil))
            (CAssignChecked tbl e (unique_guard tbl r kt) policy).
      Proof.
        intros * H_str H_env H_get H_attr H_e H_pol.
        econstructor; eauto using unique_guard_ty.
        intros store env H_P H_lstr H_lenv H_guard.
        (* the candidate value is a list of rows, so the guard's reading of it
           is the reading unique_guard_spec talks about *)
        assert (H_ty : type_of_value (interp_expr store env e) (TList (TRecord rt)))
          by (eapply type_sound with (Gstore := Gstore) (Genv := Genv); eauto).
        invert_type_of_value_clear.
        unfold value_wf_with_globals. constructor; [ | constructor ].
        right.
        eapply unique_guard_sound.
        2: eassumption.
        rewrite map.get_put_same; congruence.
      Qed.
    End WithMap.
  End WithAttr.
End WithWord.
