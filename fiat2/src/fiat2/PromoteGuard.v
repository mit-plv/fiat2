Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.TransfUtils fiat2.TransfSound.
Require Import coqutil.Map.Interface.
From Stdlib Require Import List String ZArith Permutation.
Import ListNotations.

(* THE INDEXABLE GUARD IS NOT ALWAYS THE ONE THE RULES ARE OFFERED.

   A loop body is a chain of nil-guards, and `if_nil_into_flatmap_head`
   splits a loop on the OUTERMOST one.  So whichever condition the programmer
   happened to write first is the one the index rules see, and if the
   equality an index could serve sits behind it, nothing fires.

   eval/Jenkins_DependentPlugins.v is that case in real code.  Its three
   guards, in the order the source evaluates them, are: not itself, not
   deleted, and only THIRD the equality on the attribute a dictionary would
   be keyed by.  The selector asks for no index at all, so the join stays two
   nested scans.

   The development could already fix it: `swap_if_nil_head` transposes two
   adjacent nil-guards, so enough of them bring any guard to the front.  But
   it is UNCONDITIONAL, so it cannot be aimed, and `fold_command` applies it
   to every chain in the program at once.  Measured on that subject, the
   number of applications that works is 1, 2 or 4 and the number that fails
   is 0, 3 or 5 -- not monotone, and not derivable from where the guard sits,
   because the chains interact.  A selector emitting "swap k times" would be
   fitting k to a program, which is the hand-tuning the selector exists to
   remove.

   THIS RULE IS AIMED INSTEAD.  `promote_guard_head attr` moves the first
   guard of the form `row.attr = k` -- with k not mentioning the row, which
   is the same condition the lookup rule itself checks -- to the front of its
   chain.  Being aimed, it needs no count: after one application that guard
   is at the front, so a second application does nothing.

   WHY THE SELECTOR CAN AIM IT, which is the part that makes this work.  The
   demand "there is an equality on attr somewhere in this chain" is STABLE
   UNDER THIS RULE: promotion reorders the chain and does not consume the
   guard, so the demand still holds afterwards.  That is the property the
   hoist and conjunction-split demands lack -- a program that has been
   hoisted no longer demands hoisting -- and it is why this one needs no new
   phase in Selector.v: the existing first analysis names the attribute, the
   basics promote it, and the existing second analysis then sees a plain
   head-position equality, which it already handles.

   The rule is stated on the GUARD CHAIN and not on the flatmap, as
   `swap_if_nil_head` is, for two reasons.  It makes `fold_command` reach
   every chain without the rule having to know the loop variable; and it
   makes soundness a pure reordering of nil-guards, with no argument about
   what the loop is iterating.  A consequence worth stating: the rule takes
   the row variable FROM THE GUARD, so it will also promote a guard whose
   variable is not the loop's.  That is sound -- a reordering is a reordering
   -- and merely useless, which is the right way for a rewrite to be wrong. *)

(* a chain of nil-guards, and the body it guards *)
Fixpoint guard_chain (body : expr) : list (expr * option type) * expr :=
  match body with
  | EIf p thn (EAtom (ANil t)) =>
      ((p, t) :: fst (guard_chain thn), snd (guard_chain thn))
  | _ => ([], body)
  end.

Definition rebuild (gs : list (expr * option type)) (e : expr) : expr :=
  fold_right (fun g acc => EIf (fst g) acc (EAtom (ANil (snd g)))) e gs.

(* `row.attr = k`, with k independent of row: the shape the lookup rules
   match, checked here with the same condition they check *)
Definition is_key_eq (attr : string) (p : expr) : bool :=
  match p with
  | EBinop OEq (EAccess (EVar y) a) k =>
      (String.eqb a attr && negb (free_immut_in y k))%bool
  | _ => false
  end.

Fixpoint first_key_eq (attr : string) (gs : list (expr * option type)) : option nat :=
  match gs with
  | [] => None
  | g :: gs' =>
      if is_key_eq attr (fst g) then Some O
      else match first_key_eq attr gs' with
           | Some n => Some (S n)
           | None => None
           end
  end.

Definition move_to_front {A} (i : nat) (gs : list A) : list A :=
  match nth_error gs i with
  | Some g => g :: (firstn i gs ++ skipn (S i) gs)
  | None => gs
  end.

(* What the SELECTOR needs: not "is this guard an equality on attr", which is
   what the rewrite asks, but "which attribute, and is it already first".
   Shared with the rule rather than restated, so the two cannot drift: a
   selector that asked for a promotion the rule declines would install an
   index nothing serves.

   The loop variable is required here, unlike in the rewrite.  The rewrite
   may reorder any chain soundly; the selector should only ASK when the guard
   filters the loop it sits in, which is the only case an index on it helps. *)
Definition key_eq_attr_for (x : string) (p : expr) : option string :=
  match p with
  | EBinop OEq (EAccess (EVar y) a) k =>
      if (String.eqb x y && negb (free_immut_in x k))%bool then Some a else None
  | _ => None
  end.

Fixpoint first_key_attr_for (x : string) (gs : list (expr * option type))
  : option (nat * string) :=
  match gs with
  | [] => None
  | g :: gs' =>
      match key_eq_attr_for x (fst g) with
      | Some a => Some (O, a)
      | None =>
          match first_key_attr_for x gs' with
          | Some (n, a) => Some (S n, a)
          | None => None
          end
      end
  end.

Definition promote_guard_head (attr : string) (e : expr) : expr :=
  match e with
  | EIf _ _ (EAtom (ANil _)) =>
      match first_key_eq attr (fst (guard_chain e)) with
      | Some O | None => e        (* already at the front, or not there *)
      | Some i =>
          rebuild (move_to_front i (fst (guard_chain e))) (snd (guard_chain e))
      end
  | _ => e
  end.

Section WithWord.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.
  Notation value := (value).
  Context {locals: map.map string value} {locals_ok: map.ok locals}.

  (* ---- the decomposition is syntactic ---- *)

  Lemma rebuild_cons : forall g gs e,
      rebuild (g :: gs) e = EIf (fst g) (rebuild gs e) (EAtom (ANil (snd g))).
  Proof. reflexivity. Qed.

  Lemma guard_chain_eq : forall body,
      rebuild (fst (guard_chain body)) (snd (guard_chain body)) = body.
  Proof.
    intros body. induction body using expr_IH; try reflexivity.
    cbn [guard_chain].
    destruct body3; try reflexivity.
    destruct a; try reflexivity.
    cbn [fst snd]. rewrite rebuild_cons; cbn [fst snd].
    rewrite IHbody2; reflexivity.
  Qed.

  (* ---- moving one element to the front is a permutation ---- *)

  Lemma skipn_nth_error : forall A i (gs : list A) a,
      nth_error gs i = Some a -> skipn i gs = a :: skipn (S i) gs.
  Proof.
    induction i; intros gs a E.
    - destruct gs; cbn in *; congruence.
    - destruct gs; cbn in *; [ congruence | auto ].
  Qed.

  Lemma move_to_front_Permutation : forall A i (gs : list A),
      Permutation (move_to_front i gs) gs.
  Proof.
    intros. unfold move_to_front.
    destruct (nth_error gs i) eqn:E; auto.
    pose proof (skipn_nth_error _ _ _ _ E) as Hsk.
    pose proof (firstn_skipn i gs) as Hfs.
    rewrite Hsk in Hfs.
    remember (firstn i gs) as l1.
    remember (skipn (S i) gs) as l2.
    rewrite <- Hfs.
    apply Permutation_middle.
  Qed.

  (* ---- the semantics of a chain, as one conjunction ---- *)

  Fixpoint all_true (store env : locals) (gs : list (expr * option type)) : bool :=
    match gs with
    | [] => true
    | g :: gs' =>
        match interp_expr store env (fst g) with
        | VBool b => (b && all_true store env gs')%bool
        | _ => false
        end
    end.

  (* `all_true` does not depend on the order, and needs no hypothesis for
     that: a guard whose value is not a boolean makes the whole conjunction
     false wherever it sits. *)
  Lemma all_true_perm : forall gs gs' (store env : locals),
      Permutation gs gs' -> all_true store env gs = all_true store env gs'.
  Proof.
    intros gs gs' store env H. induction H; cbn; auto.
    - (* a common head: the tails agree by induction *)
      repeat case_match; congruence.
    - (* two adjacent guards swapped: && is commutative, and a guard whose
         value is not a boolean makes the conjunction false either way *)
      repeat case_match; auto;
        repeat match goal with b : bool |- _ => destruct b end; reflexivity.
    - congruence.
  Qed.

  Lemma interp_rebuild : forall gs body (store env : locals),
      Forall (fun g => exists b, interp_expr store env (fst g) = VBool b) gs ->
      interp_expr store env (rebuild gs body)
      = (if all_true store env gs
         then interp_expr store env body else VList nil).
  Proof.
    induction gs; intros * H_b.
    - cbn [rebuild fold_right all_true]; reflexivity.
    - invert_Forall. destruct_exists.
      rewrite rebuild_cons.
      cbn [interp_expr all_true].
      lazymatch goal with
      | H: interp_expr _ _ (fst a) = VBool _ |- _ => rewrite H
      end.
      rewrite IHgs by assumption.
      repeat match goal with b : bool |- _ => destruct b end;
        cbn [interp_expr interp_atom]; reflexivity.
  Qed.

  (* reordering a chain of nil-guards does not change what it computes *)
  Lemma interp_reorder : forall gs gs' body (store env : locals),
      Permutation gs' gs ->
      Forall (fun g => exists b, interp_expr store env (fst g) = VBool b) gs ->
      interp_expr store env (rebuild gs' body)
      = interp_expr store env (rebuild gs body).
  Proof.
    intros * Hp Hb.
    rewrite (interp_rebuild gs');
      [ | eapply Permutation_Forall; [ apply Permutation_sym, Hp | exact Hb ] ].
    rewrite (interp_rebuild gs) by exact Hb.
    erewrite all_true_perm by exact Hp.
    reflexivity.
  Qed.

  (* ---- typing ----

     A guard carries its own nil annotation, and that annotation has to be
     correct at the CHAIN's type for the reordered chain to typecheck.  It
     is, because the original chain typechecked; carrying the fact alongside
     the guard is what lets the permutation be type-preserving without
     knowing anything about the annotations syntactically. *)

  Definition guard_ok (Gstore Genv : tenv) (u : type) (g : expr * option type) : Prop :=
    type_of Gstore Genv (fst g) TBool
    /\ type_of Gstore Genv (EAtom (ANil (snd g))) (TList u).

  Lemma guard_chain_ty : forall body (Gstore Genv : tenv) u,
      type_of Gstore Genv body (TList u) ->
      Forall (guard_ok Gstore Genv u) (fst (guard_chain body))
      /\ type_of Gstore Genv (snd (guard_chain body)) (TList u).
  Proof.
    intros body. induction body using expr_IH; intros * Hty;
      cbn [guard_chain fst snd]; auto.
    destruct body3; cbn [fst snd]; auto.
    destruct a; cbn [fst snd]; auto.
    invert_type_of_clear.
    lazymatch goal with
    | H: type_of _ _ body2 _ |- _ => specialize (IHbody2 _ _ _ H) as [? ?]
    end.
    split; [ constructor | ]; auto.
    split; assumption.
  Qed.

  (* The guards are booleans whatever the chain's type is, which is all the
     SEMANTICS needs -- so it never has to learn that the type is a list. *)
  Lemma guard_chain_bool : forall body (Gstore Genv : tenv) t,
      type_of Gstore Genv body t ->
      Forall (fun g => type_of Gstore Genv (fst g) TBool) (fst (guard_chain body)).
  Proof.
    intros body. induction body using expr_IH; intros * Hty;
      cbn [guard_chain fst]; auto.
    destruct body3; cbn [fst]; auto.
    destruct a; cbn [fst]; auto.
    invert_type_of_clear.
    constructor; eauto.
  Qed.

  Lemma rebuild_ty : forall gs body (Gstore Genv : tenv) u,
      Forall (guard_ok Gstore Genv u) gs ->
      type_of Gstore Genv body (TList u) ->
      type_of Gstore Genv (rebuild gs body) (TList u).
  Proof.
    induction gs; cbn [rebuild fold_right]; intros * H_g H_b; auto.
    invert_Forall.
    lazymatch goal with H: guard_ok _ _ _ a |- _ => destruct H as [? ?] end.
    econstructor; eauto.
  Qed.

  Lemma promote_guard_head_preserve_ty : forall attr (Gstore : tenv),
      preserve_ty Gstore (promote_guard_head attr).
  Proof.
    unfold preserve_ty; intros * H_Gs H_Ge H_ty.
    destruct e; cbn [promote_guard_head]; auto.
    destruct e3; auto. destruct a; auto.
    repeat (case_match; auto).
    (* the chain's type is a list, because its nil branch is.  Derived from a
       COPY of the hypothesis, so the chain survives for guard_chain_ty, and
       by bounded inversions rather than a search, which does not terminate
       here.  The atom inversion splits on whether the nil carries an
       annotation; both cases give a list. *)
    assert (Hl : exists u, t = TList u).
    { inversion H_ty; subst.
      lazymatch goal with
      | H: type_of _ _ (EAtom (ANil _)) _ |- _ => inversion H; subst
      end.
      lazymatch goal with
      | H: type_of_atom (ANil _) _ |- _ => inversion H; subst
      end.
      all: eexists; reflexivity. }
    destruct Hl as [u ?]; subst.
    pose proof (guard_chain_ty _ _ _ _ H_ty) as [Hg Hb].
    apply rebuild_ty; auto.
    eapply Permutation_Forall;
      [ apply Permutation_sym, move_to_front_Permutation | assumption ].
  Qed.

  Lemma guards_bool : forall (gs : list (expr * option type))
      (Gstore Genv : tenv) (store env : locals),
      tenv_wf Gstore -> tenv_wf Genv ->
      locals_wf Gstore store -> locals_wf Genv env ->
      Forall (fun g => type_of Gstore Genv (fst g) TBool) gs ->
      Forall (fun g => exists b, interp_expr store env (fst g) = VBool b) gs.
  Proof.
    intros gs Gstore Genv store env H_Gs H_Ge H_st H_en.
    induction gs; intros H_all; auto.
    invert_Forall. constructor.
    - lazymatch goal with
      | H: type_of _ _ _ TBool |- _ =>
          eapply type_sound in H; [ | eassumption .. ]
      end.
      lazymatch goal with
      | H: type_of_value _ TBool |- _ => inversion H; subst
      end.
      eexists; (eassumption || (symmetry; eassumption) || reflexivity).
    - apply IHgs; assumption.
  Qed.

  Lemma promote_guard_head_preserve_sem :
    forall attr (Gstore : tenv) (store : locals),
      preserve_sem Gstore store (promote_guard_head attr).
  Proof.
    unfold preserve_sem; intros * H_Gs H_Ge H_ty H_st H_en.
    destruct e; cbn [promote_guard_head]; auto.
    destruct e3; auto. destruct a; auto.
    repeat (case_match; auto).
    (* The semantics needs only that the guards are booleans, so it never has
       to learn that the chain's type is a list.  The chain itself is taken
       from the goal rather than written out, so this does not depend on how
       the earlier destructs happened to name things. *)
    pose proof (guard_chain_bool _ _ _ _ H_ty) as Hg.
    lazymatch goal with
    | |- _ = interp_expr _ _ ?ch =>
        assert (Hb : Forall (fun g => exists b,
                                 interp_expr store env (fst g) = VBool b)
                  (fst (guard_chain ch)))
          by (eapply guards_bool with (Gstore := Gstore) (Genv := Genv);
              eassumption);
        transitivity (interp_expr store env
                        (rebuild (fst (guard_chain ch)) (snd (guard_chain ch))))
    end.
    - apply interp_reorder;
        [ apply move_to_front_Permutation | exact Hb ].
    - rewrite guard_chain_eq; reflexivity.
  Qed.

  Lemma promote_guard_head_sound : forall attr,
      expr_transf_sound (locals:=locals) (promote_guard_head attr).
  Proof.
    unfold expr_transf_sound; split; intros.
    1: apply promote_guard_head_preserve_ty; auto.
    eapply promote_guard_head_preserve_sem; resolve_locals_wf; eauto.
  Qed.
End WithWord.

#[export] Hint Resolve promote_guard_head_sound : transf_hints.
