Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.IndexInterface fiat2.Utils fiat2.Substitute
  fiat2.IndexTransf fiat2.Constraint fiat2.UniqueDictIndexImpl
  fiat2.UniqueIndexInstall fiat2.Surface fiat2.TransfUtils.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
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
   only on a table whose declarations name the key the index is built on.  The
   gate itself is UniqueIndexUse.unique_lookup_gated; this file supplies what
   it decides on (declares_unique) and what the pipeline owes for it
   (cenv_respected).

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
    Notation value := (value).
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

    (* An annotated empty list has only the one type, which both the
       installation's precondition and the elaborated letmut's own typing
       derivation speak about.  Stated separately because there are two such
       derivations in scope at once below, and the inversion tactics pick
       whichever they find first. *)
    Lemma type_of_ANil_Some : forall (Gstore Genv : tenv) rty t,
        type_of Gstore Genv (EAtom (ANil (Some rty))) t -> t = TList rty.
    Proof.
      intros * H. invert_type_of_clear; invert_type_of_atom. reflexivity.
    Qed.

    Section CenvRespected.
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

      (* The premise is not vacuous: elaboration discharges it.

         A declared variable is born empty, so its declarations hold of the
         initial value outright, and elab_constr_wf is exactly the statement
         that every write elaboration inserts a guard at keeps them.  So for a
         program the surface language can express, the gate's premise is free
         -- which is what it means for the declarations to be part of the
         program rather than a hint about it. *)
      Lemma elab_cenv_respected :
        forall sc ce free_vars (Gstore Genv : tenv) tbl row_ty ds,
          tenv_wf Gstore -> tenv_wf Genv -> type_wf row_ty ->
          incl (get_free_vars Genv) free_vars ->
          Forall (decl_wf row_ty) ds ->
          well_typed Gstore Genv (elab ce free_vars (SLetConstrained tbl row_ty ds sc)) ->
          cenv_respected ((tbl, (row_ty, ds)) :: cenv_rm tbl ce) Gstore Genv
            (elab ce free_vars (SLetConstrained tbl row_ty ds sc)).
      Proof.
        intros * H_Gs H_Ge H_rt H_fv H_ds H_wt.
        cbn [elab] in H_wt |- *.
        cbn [cenv_respected]; intros row_ty0 ds0 E_look.
        cbn [cenv_lookup] in E_look; rewrite String.eqb_refl in E_look.
        injection E_look as E_rt E_ds; subst row_ty0 ds0.
        cbn [idx_install_pre]; split.
        (* born empty *)
        1:{ intros. unfold declared_holds. cbn [interp_expr interp_atom].
            apply constrs_hold_nil. }
        (* and every write keeps the declarations *)
        1:{ intros t H_t.
            apply type_of_ANil_Some in H_t; subst t.
            invert_well_typed.
            lazymatch goal with
              H : type_of _ _ (EAtom (ANil (Some row_ty))) ?t' |- _ =>
                apply type_of_ANil_Some in H; subst t'
            end.
            unfold declared_holds.
            eapply elab_constr_wf with (row_ty := row_ty) (ds := ds);
              [ | exact H_Ge | exact H_rt | exact H_fv
              | apply map.get_put_same
              | exact H_ds
              | cbn [cenv_lookup]; rewrite String.eqb_refl; reflexivity
              | assumption ].
            apply tenv_wf_step; [ exact H_Gs | constructor; exact H_rt ]. }
      Qed.


      (* The premise also survives the phase that runs before the installation.

         A basic rewrite is an expression rewrite under fold_command id: it
         leaves the command skeleton alone, and it leaves an annotated empty
         list -- what elaboration gives a declared variable as its initial
         value -- untouched.  The body's judgment then transports by
         fold_command_id_preserve_parameterized_wf.

         The initial value is pinned syntactically rather than only
         semantically because idx_install_pre quantifies over every type the
         initializer can be given, and type_of is not deterministic: an
         unannotated empty list has every list type.  Semantic preservation
         alone would give the invariant of the new initializer's value but not
         the body's judgment at the new initializer's types. *)
      Lemma fold_command_id_preserve_cenv_respected : forall f,
          (forall (Gstore : tenv), preserve_ty Gstore f) ->
          (forall (Gstore : tenv) (store : locals), preserve_sem Gstore store f) ->
          forall (a : atom) ce (Gstore Genv : tenv) tbl body,
            f (EAtom a) = EAtom a ->
            tenv_wf Gstore -> tenv_wf Genv ->
            cenv_respected ce Gstore Genv (CLetMut (EAtom a) tbl body) ->
            cenv_respected ce Gstore Genv (fold_command id f (CLetMut (EAtom a) tbl body)).
      Proof.
        intros f H_ty H_sem * H_fix H_Gs H_Ge H_ce.
        cbn [fold_command fold_expr]; unfold id at 1; rewrite H_fix.
        cbn [cenv_respected] in H_ce |- *.
        intros row_ty ds E_look.
        specialize (H_ce _ _ E_look).
        cbn [idx_install_pre] in H_ce |- *.
        destruct H_ce as [ H_init H_body ]; split; [ exact H_init | ].
        intros t H_t.
        eapply fold_command_id_preserve_parameterized_wf;
          [ exact H_ty | exact H_sem | | exact H_Ge | apply H_body; exact H_t ].
        apply tenv_wf_step; [ exact H_Gs | ].
        eapply type_of__type_wf; [ exact H_Gs | exact H_Ge | exact H_t ].
      Qed.


      (* The same, stated for the hypothesis the basic rewrites are proved
         against, so a phase of them can be composed without reopening what
         each rule does. *)
      Corollary expr_transf_sound__preserve_cenv_respected : forall f,
          expr_transf_sound (locals:=locals) f ->
          forall (a : atom) ce (Gstore Genv : tenv) tbl body,
            f (EAtom a) = EAtom a ->
            tenv_wf Gstore -> tenv_wf Genv ->
            cenv_respected ce Gstore Genv (CLetMut (EAtom a) tbl body) ->
            cenv_respected ce Gstore Genv (fold_command id f (CLetMut (EAtom a) tbl body)).
      Proof.
        unfold expr_transf_sound; intros f H_f.
        apply fold_command_id_preserve_cenv_respected;
          unfold preserve_ty, preserve_sem; intros;
          lazymatch goal with
            H : context[_ -> _ /\ _], H' : type_of _ _ _ _ |- _ =>
              apply H in H'; auto
          end; intuition auto.
      Qed.



    End CenvRespected.
  End WithMap.
End WithIndexVars.
