Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.TransfSound fiat2.TransfUtils.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
From Stdlib Require Import List String ZArith Sorted Permutation.
Import ListNotations.

Open Scope string_scope.

(* Erasing a field nothing reads.

   After an index installation a table variable holds a record pairing the
   table with its indexes, and every read of the table goes through one of
   the record's fields.  When the index rules have captured every read, the
   field holding the original collection is written on every assignment and
   read by nothing but those writes -- a self-contained dead loop, and an
   O(n) one whenever the write is a filter.  This pass removes it.

   The order is the whole design: erasure is unconditional, and the CHECK
   runs on its OUTPUT.  A write that feeds the previous field value back into
   the same field is therefore accepted, because that read disappears along
   with the component it sits in.  The predicate below is never asked of the
   input program.

   Nothing here mentions an index.  The pass runs after every index rewrite,
   so it never has to re-establish aux_wf or any bridge, and it needs no
   declaration: it is a plain dead-store elimination that happens to be
   enabled by the index rules having done their work. *)

(* ----------------------------------------------------------------
   Two facts about filter that Stdlib does not have (it has NoDup_filter
   and filter_map_swap, which the record-level lemmas below use directly).
   ---------------------------------------------------------------- *)

Lemma StronglySorted_filter : forall A (R : A -> A -> Prop) (p : A -> bool) (l : list A),
    StronglySorted R l -> StronglySorted R (filter p l).
Proof.
  induction l as [| a l IH]; cbn; intros H_ss; [ assumption | ].
  apply StronglySorted_inv in H_ss as [ H_ss H_fa ].
  destruct (p a); [ | apply IH; assumption ].
  constructor; [ apply IH; assumption | ].
  rewrite Forall_forall in *; intros x H_in.
  apply filter_In in H_in as [ H_in _ ]; apply H_fa; assumption.
Qed.

Lemma Permutation_filter : forall A (p : A -> bool) (l l' : list A),
    Permutation l l' -> Permutation (filter p l) (filter p l').
Proof.
  intros A p l l' H_perm; induction H_perm; cbn; auto.
  - destruct (p x); auto.
  - destruct (p x), (p y); auto using perm_swap.
  - eapply perm_trans; eassumption.
Qed.

Section WithField.
  (* the table's variable, and the field to remove from the record it holds *)
  Context (tbl f : string).

  (* ----------------------------------------------------------------
     Step 1: the erasure, unconditional and total.
     ---------------------------------------------------------------- *)

  Definition rm_field {A} (l : list (string * A)) : list (string * A) :=
    filter (fun p => negb (String.eqb (fst p) f)) l.

  Definition erase_record_field (e : expr) : expr :=
    match e with
    | ERecord l => ERecord (rm_field l)
    | _ => e
    end.

  (* Only an assignment to tbl changes, and only when what it assigns is a
     record literal.  Expressions are otherwise untouched -- unlike
     transf_to_idx', this pass rewrites no reads.  Dropping a component is
     observationally safe because interp_expr is total: the work it did is
     unobservable. *)
  Fixpoint erase_body (c : command) : command :=
    match c with
    | CSkip => CSkip
    | CSeq c1 c2 => CSeq (erase_body c1) (erase_body c2)
    | CLet e x c => CLet e x (erase_body c)
    (* stop where the table's name is shadowed: the inner binding is a
       different variable and still has the field *)
    | CLetMut e x c =>
        CLetMut e x (if String.eqb x tbl then c else erase_body c)
    | CAssign x e =>
        CAssign x (if String.eqb x tbl then erase_record_field e else e)
    | CIf e c1 c2 => CIf e (erase_body c1) (erase_body c2)
    | CForeach e x c => CForeach e x (erase_body c)
    end.

  (* ----------------------------------------------------------------
     Step 2: the check, run on the erased program.

     Every occurrence of ELoc tbl must be the immediate argument of an
     EAccess at a field other than f.  A bare ELoc tbl elsewhere hands the
     whole record over, so it counts as a read of every field.

     This is positional: a self-use that reaches the field through a binder,
     as in CLet (EAccess (ELoc tbl) f) x (CAssign tbl (ERecord [(f, <uses x>); ...])),
     leaves a live read behind once the component is gone, and the check then
     declines to erase.  That is conservative rather than wrong.  Making it a
     liveness test instead would mean eliminating the dead binding first,
     which is cheap here (expressions are pure and total, so CLet e x c with
     x not free in c is c) but needs a command-level analogue of
     not_free_immut_put_sem.  Deferred on purpose.
     ---------------------------------------------------------------- *)

  Fixpoint expr_reads_no_field (e : expr) : bool :=
    match e with
    | EVar _ | EAtom _ => true
    | ELoc x => negb (String.eqb x tbl)
    (* intercepted before the congruence case below *)
    | EAccess (ELoc x) s =>
        if String.eqb x tbl then negb (String.eqb s f) else true
    | EAccess r _ => expr_reads_no_field r
    | EUnop _ e | EACFold _ e | EACIFold _ e | ESort _ e | EBagOf e | ESetOf e =>
        expr_reads_no_field e
    | EBinop _ e1 e2 | ELet e1 _ e2 | EFlatmap _ e1 _ e2 =>
        (expr_reads_no_field e1 && expr_reads_no_field e2)%bool
    | ETernop _ e1 e2 e3 | EIf e1 e2 e3 | EFold e1 e2 _ _ e3 =>
        (expr_reads_no_field e1 && expr_reads_no_field e2
         && expr_reads_no_field e3)%bool
    | EOptMatch e e_none _ e_some =>
        (expr_reads_no_field e && expr_reads_no_field e_none
         && expr_reads_no_field e_some)%bool
    | ERecord l => forallb (fun p => expr_reads_no_field (snd p)) l
    end.

  Fixpoint command_reads_no_field (c : command) : bool :=
    match c with
    | CSkip => true
    | CSeq c1 c2 => (command_reads_no_field c1 && command_reads_no_field c2)%bool
    | CLet e _ c => (expr_reads_no_field e && command_reads_no_field c)%bool
    (* shadowing is refused outright: one proof case fewer, and the index
       layer already declines to descend through such a binder *)
    | CLetMut e x c =>
        (negb (String.eqb x tbl) && expr_reads_no_field e
         && command_reads_no_field c)%bool
    | CAssign _ e => expr_reads_no_field e
    | CIf e c1 c2 =>
        (expr_reads_no_field e && command_reads_no_field c1
         && command_reads_no_field c2)%bool
    | CForeach e _ c => (expr_reads_no_field e && command_reads_no_field c)%bool
    end.

End WithField.

(* record_entry_leb is bool-valued, as everywhere else in the development *)
Local Coercion is_true : bool >-> Sortclass.

(* ----------------------------------------------------------------
   What removing one field does to a record's invariants.  Every one of
   these is needed because the table's type loses an entry, and TRecord
   carries NoDup, sortedness and well-formedness of its field types.
   ---------------------------------------------------------------- *)

Lemma rm_field_NoDup : forall A f (l : list (string * A)),
    NoDup (List.map fst l) -> NoDup (List.map fst (rm_field f l)).
Proof.
  unfold rm_field; intros * H.
  (* the instance has to be given: matching filter_map_swap's right-hand
     side would ask Coq to invent the predicate under the composition *)
  rewrite <- (filter_map_swap (fun s => negb (String.eqb s f)) fst l).
  apply NoDup_filter; assumption.
Qed.

Lemma rm_field_SSorted : forall A f (l : list (string * A)),
    StronglySorted record_entry_leb l ->
    StronglySorted record_entry_leb (rm_field f l).
Proof.
  unfold rm_field; intros; apply StronglySorted_filter; assumption.
Qed.

Lemma Forall_snd_rm_field : forall A (P : A -> Prop) f (l : list (string * A)),
    Forall P (List.map snd l) -> Forall P (List.map snd (rm_field f l)).
Proof.
  unfold rm_field; intros * H.
  rewrite Forall_forall in *; intros x H_in.
  apply in_map_iff in H_in as [ q [ E_q H_in ] ].
  apply filter_In in H_in as [ H_in _ ].
  apply H, in_map_iff; exists q; auto.
Qed.

Lemma Permutation_rm_field : forall A f (l l' : list (string * A)),
    Permutation l l' -> Permutation (rm_field f l) (rm_field f l').
Proof.
  unfold rm_field; intros; apply Permutation_filter; assumption.
Qed.

(* The one that makes the whole pass work: every other field is still
   reachable, and at the same type. *)
Lemma access_record_rm_field : forall A f t (l : list (string * A)),
    t <> f -> access_record (rm_field f l) t = access_record l t.
Proof.
  induction l as [| [ s a ] l IH ]; cbn; intros H_ne; [ reflexivity | ].
  destruct (String.eqb s f) eqn:E_sf; cbn.
  - apply String.eqb_eq in E_sf; subst s.
    destruct (String.eqb t f) eqn:E_tf;
      [ apply String.eqb_eq in E_tf; congruence | apply IH; assumption ].
  - destruct (String.eqb t s); [ reflexivity | apply IH; assumption ].
Qed.

Lemma type_wf_rm_field : forall f tl,
    type_wf (TRecord tl) -> type_wf (TRecord (rm_field f tl)).
Proof.
  intros * H; inversion H; subst.
  constructor;
    [ apply rm_field_NoDup | apply rm_field_SSorted | apply Forall_snd_rm_field ];
    assumption.
Qed.

(* ----------------------------------------------------------------
   Step 3: the pass.  Identity unless the erased body reads nothing.
   ---------------------------------------------------------------- *)

Definition erase_dead_field (f : string) {tenv : map.map string type}
  (_ _ : tenv) (c : command) : command :=
  match c with
  | CLetMut e tbl c0 =>
      let c0' := erase_body tbl f c0 in
      if command_reads_no_field tbl f c0'
      then CLetMut (erase_record_field f e) tbl c0'
      else c
  | _ => c
  end.
