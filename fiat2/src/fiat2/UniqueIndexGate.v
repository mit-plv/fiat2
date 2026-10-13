Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.Utils fiat2.Substitute
  fiat2.IndexTransf fiat2.Constraint fiat2.UniqueDictIndexImpl
  fiat2.UniqueIndexInstall fiat2.Surface.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Datatypes.Result.
From Stdlib Require Import String ZArith List.

Import ListNotations.

(* Gating a constraint-dependent rewrite on the declarations, not on the
   program.

   Every other rewrite in the pipeline is a total function that fires when it
   finds its pattern in the program and is the identity otherwise, which is
   what makes the pipeline sound for any sequence of hints.  A rewrite that
   depends on a primary key cannot be gated that way: that a table maintains
   its key is a property of the whole program, and the one piece of syntax that
   witnesses it -- the guard at a write -- is itself a rewrite target, so a gate
   that looked for it would answer differently depending on what ran before.

   The declarations are the pattern instead.  They sit in a cenv, beside the
   program rather than inside it, so no rewrite can alter them; decl already
   classifies them, so matching one is a constructor match and a string
   compare, with no need to compare expressions.  The gate is then exactly as
   local and as decidable as every other rewrite's pattern match, and it fires
   only on a table whose declarations name the key the index is built on.

   What the cenv cannot supply by itself is that the declarations are true of
   the running program.  That is cenv_respected below, a condition on the
   command the pipeline is handed rather than on the hints it is handed -- so
   soundness is still uniform in the hints.  For an elaborated program it is
   discharged by construction, since elaboration is what inserts the guards.  A
   cenv is therefore program text, never a hint: a cenv claiming a key that the
   program does not maintain is an input the pipeline is not sound for. *)

Section WithIndexVars.
  (* the names the index's own fold binds *)
  Context (hole attr tup acc : string).
  Context (H_ne : tup <> acc).
  (* the two fields the installation pairs *)
  Context (id_tag aux_tag : string).
  Context (H_tags_diff : id_tag <> aux_tag).

  Notation uidx := (unique_dict_idx hole attr tup acc).

  (* The pattern, matched on a declaration rather than on an expression. *)
  Definition decl_is_unique (d : decl) : bool :=
    match d with
    | DUnique a => String.eqb a attr
    | _ => false
    end.

  Definition declares_unique (ds : list decl) : bool := existsb decl_is_unique ds.

  Section WithMap.
    Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (width:=width)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.

    Notation uidx_wf := (UniqueDictIndexImpl.idx_wf hole attr tup acc (locals:=locals)).

    (* The invariant carried is that every declared constraint holds, not just
       the key.  Carrying the whole set is what lets elaboration's own theorem
       be used unchanged: parameterized_wf needs an iff to move between
       predicates, not an implication, so a derivation about the conjunction
       cannot be weakened to one about a single conjunct.  The key is extracted
       instead where it is used, and there the value's type is at hand, which
       is what the extraction needs. *)
    Definition declared_holds (row_ty : type) (ds : list decl) : value -> Prop :=
      constrs_hold (locals:=locals) (constrs_of_decls row_ty ds).

    Definition unique_aux_declared (row_ty : type) (ds : list decl) (v : value) : Prop :=
      aux_wf (idx_wf := uidx_wf) id_tag aux_tag v
      /\ at_id_tag id_tag (declared_holds row_ty ds) v.

    (* A declared key is one of the constraints, so the conjunction gives it. *)
    Lemma declares_unique__key_holds : forall rt ds (v : value),
        declares_unique ds = true ->
        declared_holds (TRecord rt) ds v ->
        key_holds attr (locals:=locals) rt v.
    Proof.
      unfold declares_unique, declared_holds, key_holds, constrs_hold.
      intros * H_ex H_all.
      apply existsb_exists in H_ex as [ d [ H_in H_d ] ].
      destruct d; cbn [decl_is_unique] in H_d; try discriminate.
      rewrite String.eqb_eq in H_d; subst.
      constructor; [ | constructor ].
      rewrite Forall_forall in H_all. apply H_all.
      unfold constrs_of_decls. apply in_map_iff.
      exists (DUnique attr); split; [ reflexivity | assumption ].
    Qed.

    Lemma unique_aux_declared__unique_aux_pre : forall rt ds (v : value),
        declares_unique ds = true ->
        unique_aux_declared (TRecord rt) ds v ->
        unique_aux_pre hole attr tup acc id_tag aux_tag (locals:=locals) rt v.
    Proof.
      unfold unique_aux_declared, unique_aux_pre, at_id_tag.
      intros * H_ex [ H_aux H_id ].
      split; [ assumption | ].
      repeat destruct_match_hyp; try contradiction.
      eapply declares_unique__key_holds; eassumption.
    Qed.

    Section WithGate.
      (* The gated transformation.  Same shape as every other: match, and be
         the identity when the match fails. *)
      Definition apply_unique_idx_transfs (ce : cenv)
        (f : string -> command -> command) (Gstore Genv : tenv) (c : command) : command :=
        match c with
        | CLetMut _ tbl _ =>
            match cenv_lookup tbl ce with
            | Some (_, ds) =>
                if declares_unique ds
                then apply_idx_related_transfs (idx := uidx) id_tag aux_tag f Gstore Genv c
                else c
            | None => c
            end
        | _ => c
        end.

      (* The cenv describes the program it is paired with: a declared variable
         is born satisfying its declarations and every write keeps them. *)
      Definition cenv_respected (ce : cenv) (Gstore Genv : tenv) (c : command) : Prop :=
        match c with
        | CLetMut e tbl body =>
            forall row_ty ds,
              cenv_lookup tbl ce = Some (row_ty, ds) ->
              idx_install_pre (declared_holds row_ty ds) Gstore Genv (CLetMut e tbl body)
        | _ => True
        end.

      Theorem apply_unique_idx_transfs_sound : forall ce f,
          (forall row_ty ds,
              aug_transf_sound (@IndexInterface.is_tbl_ty uidx)
                (aux_ty (idx := uidx) id_tag aux_tag)
                (unique_aux_declared row_ty ds) f) ->
          forall (Gstore Genv : tenv) c,
            tenv_wf Gstore -> tenv_wf Genv ->
            well_typed Gstore Genv c ->
            cenv_respected ce Gstore Genv c ->
            well_typed Gstore Genv (apply_unique_idx_transfs ce f Gstore Genv c) /\
              forall (store env : locals),
                locals_wf Gstore store -> locals_wf Genv env ->
                interp_command store env (apply_unique_idx_transfs ce f Gstore Genv c)
                = interp_command store env c.
      Proof.
        intros ce f H_f * H_Gs H_Ge H_wt H_ce.
        unfold apply_unique_idx_transfs.
        destruct c; auto.
        cbn [cenv_respected] in H_ce.
        destruct (cenv_lookup x ce) as [ [ row_ty ds ] | ] eqn:E_look; auto.
        destruct (declares_unique ds) eqn:E_uq; auto.
        unfold unique_aux_declared in H_f.
        eapply (apply_idx_related_transfs_pre_sound
                  (idx_ok := unique_dict_idx_ok hole attr tup acc H_ne)
                  id_tag aux_tag H_tags_diff
                  (declared_holds row_ty ds) f);
          [ apply H_f | assumption .. | ].
        apply H_ce; reflexivity.
      Qed.
    End WithGate.
  End WithMap.
End WithIndexVars.
