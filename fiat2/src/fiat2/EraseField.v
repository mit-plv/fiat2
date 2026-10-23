Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.TransfSound fiat2.TransfUtils.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
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

  (* A write the pass can shorten: a record literal with distinct field
     names.  Crossing the sort the interpreter applies to a literal is only
     invisible when the names are distinct, and a well-typed literal always
     is (TyERecord's fourth premise), so the condition costs no
     applicability. *)
  Definition erasable_record (e : expr) : bool :=
    match e with
    | ERecord l => NoDup_comp String.eqb (List.map fst l)
    | _ => false
    end.

  Definition erase_record_field (e : expr) : expr :=
    match e with
    | ERecord l =>
        if NoDup_comp String.eqb (List.map fst l)
        then ERecord (rm_field l)
        else e
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

  (* ----------------------------------------------------------------
     What type preservation needs beyond the reads.

     The table's type loses a field, so every WRITE to the table must lose
     one too.  A write that is not an erasable record literal would keep the
     field and no longer match the table's shortened type, so the pass
     refuses it.  Every write the index installation and its maintenance
     rules produce is such a literal, so nothing is lost in practice.
     ---------------------------------------------------------------- *)
  Fixpoint writes_erasable (c : command) : bool :=
    match c with
    | CSkip => true
    | CSeq c1 c2 => (writes_erasable c1 && writes_erasable c2)%bool
    | CLet _ _ c => writes_erasable c
    | CLetMut _ x c => if String.eqb x tbl then true else writes_erasable c
    | CAssign x e => if String.eqb x tbl then erasable_record e else true
    | CIf _ c1 c2 => (writes_erasable c1 && writes_erasable c2)%bool
    | CForeach _ _ c => writes_erasable c
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

(* Both field lists lose the same positions, since the names agree and the
   predicate looks only at names. *)
Lemma Forall2_rm_field : forall A B (P : A -> B -> Prop) f
    (l : list (string * A)) (l' : list (string * B)),
    List.map fst l = List.map fst l' ->
    Forall2 P (List.map snd l) (List.map snd l') ->
    Forall2 P (List.map snd (rm_field f l)) (List.map snd (rm_field f l')).
Proof.
  unfold rm_field; induction l as [| [ s a ] l IH ]; cbn;
    intros l' E_fst H_all2.
  1: destruct l'; cbn in *; [ constructor | discriminate ].
  destruct l' as [| [ s' b ] l' ]; cbn in *; [ discriminate | ].
  injection E_fst as E_s E_fst; subst s'.
  inversion H_all2 as [| a0 b0 la lb H_head H_tail ]; subst.
  destruct (String.eqb s f); cbn; [ apply IH; assumption | ].
  constructor; [ exact H_head | apply IH; assumption ].
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

(* ----------------------------------------------------------------
   The pass.

   Three conditions, all decidable and all checked on the program in hand:
   the initializer and every write to the table are record literals the
   erasure can shorten, and once it has, nothing reads the field.  Identity
   otherwise, as every other rule in the pipeline is.
   ---------------------------------------------------------------- *)
Definition erase_dead_field (f : string) {tenv : map.map string type}
  (_ _ : tenv) (c : command) : command :=
  match c with
  | CLetMut e tbl c0 =>
      let c0' := erase_body tbl f c0 in
      if (erasable_record e && writes_erasable tbl c0
          && command_reads_no_field tbl f c0')%bool
      then CLetMut (erase_record_field f e) tbl c0'
      else c
  | _ => c
  end.

(* The erasure, computed, on the one shape it acts on. *)
Lemma erase_record_field_ERecord : forall f l,
    NoDup_comp String.eqb (List.map fst l) = true ->
    erase_record_field f (ERecord l) = ERecord (rm_field f l).
Proof.
  intros * H; unfold erase_record_field; rewrite H; reflexivity.
Qed.

Lemma access_record_not_In : forall A (l : list (string * A)) s,
    ~ In s (List.map fst l) -> access_record l s = access_record nil s.
Proof.
  induction l as [| [ s0 a ] l IH ]; cbn; intros s H_nin; [ reflexivity | ].
  destruct (String.eqb s s0) eqn:E;
    [ apply String.eqb_eq in E; subst; exfalso; apply H_nin; left; reflexivity | ].
  apply IH; intro H_in; apply H_nin; right; exact H_in.
Qed.

Lemma access_record_record_sort : forall A (l : list (string * A)) t,
    NoDup (List.map fst l) ->
    access_record (record_sort l) t = access_record l t.
Proof.
  intros * H_nd.
  destruct (in_dec String.string_dec t (List.map fst l)) as [ H_in | H_nin ].
  - symmetry.
    apply NoDup_Permutation_access_record; auto using Permuted_record_sort.
  - rewrite (access_record_not_In _ l t H_nin).
    apply access_record_not_In.
    intro H_in; apply H_nin.
    eapply Permutation_in; [ | exact H_in ].
    apply Permutation_sym, Permutation_map, Permuted_record_sort.
Qed.

(* map over a record's values leaves its field names alone, so removing a
   field commutes with it *)
Lemma map_rm_field : forall A B f (g : (string * A) -> (string * B)) l,
    (forall p, fst (g p) = fst p) ->
    List.map g (rm_field f l) = rm_field f (List.map g l).
Proof.
  unfold rm_field; induction l as [| p l IH ]; cbn; intros H_fst; [ reflexivity | ].
  rewrite H_fst. destruct (String.eqb (fst p) f); cbn; rewrite IH; auto.
Qed.

Section WithMap.
  Notation value := (value).
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  (* ----------------------------------------------------------------
     The store relation.

     The two stores agree away from the table, and at the table they agree on
     every field read EXCEPT the erased one.  Stated through a projection
     rather than as rv' = rm_field f rv for two reasons: the equational form
     would need uniqueness of sorted permutations, which this development does
     not have; and the projection form does not insist that the table hold a
     record at all, so nothing here needs type soundness.  A field read is
     exactly what the check permits a program to do, so this is exactly what
     the program can observe.
     ---------------------------------------------------------------- *)
  Definition proj_field (t : string) (v : value) : value :=
    match v with
    | VRecord rv => record_proj t rv
    | _ => VUnit
    end.

  Definition field_at (t : string) (store : locals) (tbl : string) : value :=
    match map.get store tbl with
    | Some v => proj_field t v
    | None => VUnit
    end.

  Definition erased_at (tbl f : string) (store store' : locals) : Prop :=
    (forall t, t <> f -> field_at t store' tbl = field_at t store tbl)
    /\ (forall x, x <> tbl -> map.get store x = map.get store' x).

  Lemma field_at_get_local : forall t (store : locals) tbl,
      field_at t store tbl = proj_field t (get_local store tbl).
  Proof.
    unfold field_at, get_local; intros.
    destruct (map.get store tbl); reflexivity.
  Qed.

  Lemma erased_at__get_local : forall tbl f (store store' : locals) x,
      erased_at tbl f store store' ->
      x <> tbl ->
      get_local store' x = get_local store x.
  Proof.
    intros * [ _ H_off ] H_ne; unfold get_local.
    rewrite (H_off x H_ne); reflexivity.
  Qed.

  (* The one case the whole pass turns on: a read of any field but f sees the
     same value on both sides. *)
  Lemma erased_at__access : forall tbl f (store store' : locals) t,
      erased_at tbl f store store' ->
      t <> f ->
      match get_local store' tbl with
      | VRecord l => record_proj t l
      | _ => VUnit
      end
      = match get_local store tbl with
        | VRecord l => record_proj t l
        | _ => VUnit
        end.
  Proof.
    intros * [ H_fields _ ] H_ne.
    change (proj_field t (get_local store' tbl) = proj_field t (get_local store tbl)).
    rewrite <- 2 field_at_get_local.
    apply H_fields; assumption.
  Qed.

  (* ----------------------------------------------------------------
     Closure: the relation survives the three ways a command changes a
     store.  Writing some other variable, writing the table itself with a
     value whose fields agree off f, and restoring a variable at a letmut's
     end.
     ---------------------------------------------------------------- *)

  Lemma erased_at_put : forall tbl f (store store' : locals) x v,
      erased_at tbl f store store' ->
      x <> tbl ->
      erased_at tbl f (map.put store x v) (map.put store' x v).
  Proof.
    intros * [ H_fields H_off ] H_ne; split.
    1:{ intros t H_t; unfold field_at.
        repeat rewrite map.get_put_diff by congruence.
        apply H_fields; assumption. }
    1:{ intros y H_y. destruct (String.eqb y x) eqn:E_y.
        1:{ apply String.eqb_eq in E_y; subst y.
            repeat rewrite map.get_put_same; reflexivity. }
        1:{ apply String.eqb_neq in E_y.
            repeat rewrite map.get_put_diff by congruence.
            apply H_off; assumption. } }
  Qed.

  Lemma erased_at_put_tbl : forall tbl f (store store' : locals) v v',
      erased_at tbl f store store' ->
      (forall t, t <> f -> proj_field t v' = proj_field t v) ->
      erased_at tbl f (map.put store tbl v) (map.put store' tbl v').
  Proof.
    intros * [ _ H_off ] H_v; split.
    1:{ intros t H_t; unfold field_at.
        repeat rewrite map.get_put_same.
        apply H_v; assumption. }
    1:{ intros y H_y. repeat rewrite map.get_put_diff by congruence.
        apply H_off; assumption. }
  Qed.

  (* general in x, as the letmut case needs: at x = tbl the restored values
     are the ones the enclosing stores held, and those were already related *)
  Lemma erased_at_update : forall tbl f (l0 l0' l l' : locals),
      erased_at tbl f l0 l0' ->
      erased_at tbl f l l' ->
      forall x,
        erased_at tbl f (map.update l x (map.get l0 x)) (map.update l' x (map.get l0' x)).
  Proof.
    intros * [ H_fields0 H_off0 ] [ H_fields H_off ] x.
    destruct (String.eqb x tbl) eqn:E_x.
    1:{ apply String.eqb_eq in E_x; subst x; split.
        1:{ intros t H_t; unfold field_at.
            repeat rewrite Properties.map.get_update_same.
            apply H_fields0; assumption. }
        1:{ intros y H_y.
            repeat rewrite Properties.map.get_update_diff by congruence.
            apply H_off; assumption. } }
    1:{ apply String.eqb_neq in E_x; split.
        1:{ intros t H_t; unfold field_at.
            repeat rewrite Properties.map.get_update_diff by congruence.
            apply H_fields; assumption. }
        1:{ intros y H_y. destruct (String.eqb y x) eqn:E_y.
            1:{ apply String.eqb_eq in E_y; subst y.
                repeat rewrite Properties.map.get_update_same.
                apply H_off0; assumption. }
            1:{ apply String.eqb_neq in E_y.
                repeat rewrite Properties.map.get_update_diff by congruence.
                apply H_off; assumption. } } }
  Qed.

  (* expr_IH renames its binders, so the induction hypotheses cannot be
     addressed by name.  Both tactics below pick whichever one applies. *)
  Local Ltac rewrite_IH :=
    match goal with
    | IH : expr_reads_no_field _ _ _ = true -> _ |- _ => rewrite IH by assumption
    end.

  Local Ltac apply_IH :=
    match goal with
    | IH : expr_reads_no_field _ _ _ = true -> _ |- _ => apply IH; assumption
    end.

  (* ----------------------------------------------------------------
     Expressions: plain equality.

     No typing hypothesis is needed.  The expression itself is unchanged, and
     interp_expr is total, so all this says is that a program never reading
     tbl.f cannot tell the two stores apart.  The stores are fixed before the
     induction; env is not, since a binder extends it.
     ---------------------------------------------------------------- *)
  Lemma erase_preserve_sem_expr : forall tbl f (store store' : locals),
      erased_at tbl f store store' ->
      forall e, expr_reads_no_field tbl f e = true ->
        forall (env : locals), interp_expr store' env e = interp_expr store env e.
  Proof.
    intros tbl f store store' H_er e.
    induction e using expr_IH; cbn [expr_reads_no_field]; intros H_rd env;
      cbn [interp_expr].
    (* EVar *)
    1: reflexivity.
    (* ELoc: a bare read of tbl would hand over every field, so the check
       says this is some other variable *)
    1:{ apply Bool.negb_true_iff, String.eqb_neq in H_rd.
        eapply erased_at__get_local; eassumption. }
    (* EAtom *)
    1: reflexivity.
    (* Split what the congruence cases carry.  Only genuine conjunctions:
       destruct on H_rd itself would rewrite true backwards through every
       hypothesis, the IHs included. *)
    all: repeat rewrite Bool.andb_true_iff in H_rd.
    all: repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
    (* Every congruence case is then its subterms' IHs.  Matched on shape
       rather than by name, since the scheme names them after its binders. *)
    all: repeat rewrite_IH.
    all: try reflexivity.
    (* What is left are the cases whose body runs under a binder, where the
       IH cannot be used as a rewrite: the extended environment mentions the
       bound element, so there is no closed instance to rewrite at.  Each one
       instead goes pointwise, exactly as transf_to_idx's does -- but with no
       typing hypothesis, because here the two sides run the SAME expression
       and the scrutinee is already equal once e1's IH has been used. *)
    (* EFlatmap *)
    1:{ (* e1's IH was already used above: the scrutinee is equal on both
           sides, so only the body is left *)
        destruct tag; case_match; try reflexivity.
        all: repeat lazymatch goal with
               | |- VList _ = VList _ => f_equal
               | |- VBag _ = VBag _ => f_equal
               | |- VSet _ = VSet _ => f_equal
               | |- list_to_bag _ = list_to_bag _ => f_equal
               | |- list_to_set _ = list_to_set _ => f_equal
               end.
        (* the two sides are beta-redexes of LIST type here, so the IH is
           rewritten inside rather than applied to the goal *)
        all: apply In_flat_map_ext; intros a H_in;
          cbn beta; rewrite_IH; reflexivity. }
    (* EFold *)
    1:{ case_match; try reflexivity.
        apply In_fold_right_ext with (P := fun _ => True); [ exact I | ].
        intros acc0 v0 _ H_in; cbn beta;
          split; [ apply_IH | exact I ]. }
    (* ERecord: the fields, one at a time *)
    1:{ do 2 f_equal. apply map_ext_in; intros [ s e ] H_in; cbn.
        rewrite forallb_forall in H_rd.
        f_equal.
        lazymatch goal with
        | IH : Forall _ _ |- _ =>
            rewrite Forall_forall in IH;
            specialize (IH (s, e) H_in); cbn in IH;
            apply IH, (H_rd (s, e) H_in)
        end. }
    (* EAccess, the case the relation exists for.  The check's own match on
       the accessed expression is what has to be taken apart; the goal is
       left unreduced, since the IHs speak about interp_expr applied to the
       whole subexpression. *)
    1:{ lazymatch goal with x : expr |- _ => destruct x end;
          cbn [expr_reads_no_field] in H_rd;
          try (rewrite_IH; reflexivity).
        (* only a read of a mutable variable is left *)
        lazymatch goal with
        | |- context [ interp_expr _ _ (ELoc ?y) ] =>
            destruct (String.eqb y tbl) eqn:E_y;
            [ apply String.eqb_eq in E_y; subst y | ]
        end;
          cbn [interp_expr].
        (* the table itself, at a field that is not the erased one *)
        1:{ (* destruct ... eqn: already replaced the test in H_rd *)
            cbn in H_rd.
            apply Bool.negb_true_iff, String.eqb_neq in H_rd.
            eapply erased_at__access; eassumption. }
        (* some other mutable variable, where the stores simply agree *)
        1:{ apply String.eqb_neq in E_y.
            erewrite erased_at__get_local; eauto. } }
    (* EOptMatch: the bound value is free once the match is taken apart *)
    1:{ case_match; try reflexivity.
        (* once more, for the option the match scrutinises *)
        case_match; try reflexivity.
        apply_IH. }
  Qed.


  Lemma record_proj_access : forall (X Y : list (string * value)) t,
      access_record X t = access_record Y t ->
      record_proj t X = record_proj t Y.
  Proof.
    unfold record_proj; intros * H; rewrite H; reflexivity.
  Qed.

  Lemma erased_at_refl : forall tbl f (store : locals), erased_at tbl f store store.
  Proof.
    intros; split; intros; reflexivity.
  Qed.

  (* Erasing a component leaves every other field reading the same.  This is
     the whole content of the pass, and it is shared by the write case and by
     the initializer: both sides are interpreted in the SAME store here, so no
     expression lemma is involved. *)
  Lemma proj_field_erase_record : forall f (store env : locals) e t,
      t <> f ->
      proj_field t (interp_expr store env (erase_record_field f e))
      = proj_field t (interp_expr store env e).
  Proof.
    intros f store env e t H_t.
    destruct e; cbn [erase_record_field]; try reflexivity.
    destruct (NoDup_comp String.eqb (List.map fst l)) eqn:E_nd; [ | reflexivity ].
    apply NoDup_comp_true_iff in E_nd.
    cbn [interp_expr proj_field].
    apply record_proj_access.
    assert (E_fst : List.map fst
                      (List.map (fun '(s, e) => (s, interp_expr store env e)) l)
                    = List.map fst l)
      by (rewrite map_map; apply map_ext; intros [ ? ? ]; reflexivity).
    rewrite map_rm_field by (intros [ ? ? ]; reflexivity).
    rewrite access_record_record_sort
      by (apply rm_field_NoDup; rewrite E_fst; exact E_nd).
    rewrite access_record_rm_field by exact H_t.
    symmetry. apply access_record_record_sort.
    rewrite E_fst; exact E_nd.
  Qed.

  (* Rewriting with the expression lemma has to be given its instance: the
     pattern interp_expr ?store ?env ?e matches the unprimed occurrence too,
     and rewriting that one first leaves an unsatisfiable side condition. *)
  Local Ltac rw_expr :=
    match goal with
    | H_er : erased_at ?tbl ?f ?st ?st',
        H : expr_reads_no_field ?tbl ?f ?e = true |- _ =>
        rewrite (erase_preserve_sem_expr tbl f st st' H_er e H)
    end.

  Lemma erased_at_fold_left : forall tbl f (F F' : locals -> value -> locals) l,
      (forall s s' v, erased_at tbl f s s' -> erased_at tbl f (F s v) (F' s' v)) ->
      forall (store store' : locals),
        erased_at tbl f store store' ->
        erased_at tbl f (fold_left F l store) (fold_left F' l store').
  Proof.
    intros * H_step; induction l as [| v l IH ]; cbn; intros store store' H_er;
      [ exact H_er | ].
    apply IH, H_step; exact H_er.
  Qed.

  (* ----------------------------------------------------------------
     Commands: the relation in, the relation out.

     This cannot be an equality -- inside the body the two stores really do
     differ at the table, one record carrying the field and the other not.
     The most that holds is that the difference stays confined to that field,
     which is what erased_at says.  Equality comes back only at the letmut,
     below.
     ---------------------------------------------------------------- *)
  Lemma erase_preserve_sem_cmd : forall tbl f c,
      command_reads_no_field tbl f (erase_body tbl f c) = true ->
      forall (store store' env : locals),
        erased_at tbl f store store' ->
        erased_at tbl f (interp_command store env c)
                        (interp_command store' env (erase_body tbl f c)).
  Proof.
    intros tbl f c; induction c; intros H_rd store store' env H_er;
      cbn [erase_body] in H_rd |- *; cbn [command_reads_no_field] in H_rd;
      cbn [interp_command].
    (* CSkip *)
    1: exact H_er.
    (* CSeq *)
    1:{ rewrite Bool.andb_true_iff in H_rd; destruct H_rd as [ H1 H2 ].
        apply IHc2; [ exact H2 | apply IHc1; [ exact H1 | exact H_er ] ]. }
    (* CLet: the bound value is the same on both sides *)
    1:{ rewrite Bool.andb_true_iff in H_rd; destruct H_rd as [ H1 H2 ].
        rw_expr.
        apply IHc; [ exact H2 | exact H_er ]. }
    (* CLetMut: the check refuses a binder that shadows the table, so the
       body really was erased, and the restored value is the same *)
    1:{ repeat rewrite Bool.andb_true_iff in H_rd.
        destruct H_rd as [ [ H_ne H1 ] H2 ].
        apply Bool.negb_true_iff, String.eqb_neq in H_ne.
        rewrite (proj2 (String.eqb_neq _ _) H_ne) in H2 |- *.
        rw_expr.
        apply erased_at_update; [ exact H_er | ].
        apply IHc; [ exact H2 | apply erased_at_put; assumption ]. }
    (* CAssign *)
    1:{ destruct (String.eqb x tbl) eqn:E_x.
        2:{ (* some other variable: the same value goes into both *)
            apply String.eqb_neq in E_x.
            rw_expr.
            apply erased_at_put; assumption. }
        apply String.eqb_eq in E_x; subst x.
        (* the table itself: move to the common store with the expression
           lemma, then the field agreement is the shared lemma above *)
        rw_expr.
        apply erased_at_put_tbl; [ exact H_er | ].
        intros t H_t; apply proj_field_erase_record; exact H_t. }
    (* CIf *)
    1:{ repeat rewrite Bool.andb_true_iff in H_rd.
        destruct H_rd as [ [ H1 H2 ] H3 ].
        rw_expr.
        (* every value shape but VBool leaves the store alone *)
        case_match; try exact H_er.
        destruct b; [ apply IHc1 | apply IHc2 ]; assumption. }
    (* CForeach *)
    1:{ rewrite Bool.andb_true_iff in H_rd; destruct H_rd as [ H1 H2 ].
        rw_expr.
        case_match; try exact H_er.
        apply erased_at_fold_left; [ | exact H_er ].
        intros s s' v H_s. apply IHc; assumption. }
  Qed.


  (* ----------------------------------------------------------------
     The letmut, where the simulation becomes an equality.

     The table is let-bound, so at the end of the binding its entry is
     restored to whatever the ENCLOSING store held -- the same value in both
     runs.  The simulation gives agreement away from the table, and that is
     exactly what stores_eq_except__update_eq needs.  So the field's absence
     is unobservable not because the two runs agree at the table, but because
     the table does not outlive the binding.
     ---------------------------------------------------------------- *)
  Lemma erase_letmut_preserve_sem : forall tbl f e c0 (store env : locals),
      command_reads_no_field tbl f (erase_body tbl f c0) = true ->
      interp_command store env
        (CLetMut (erase_record_field f e) tbl (erase_body tbl f c0))
      = interp_command store env (CLetMut e tbl c0).
  Proof.
    intros * H_rd; cbn [interp_command].
    apply stores_eq_except__update_eq; intros x H_x; symmetry.
    apply (proj2 (erase_preserve_sem_cmd tbl f c0 H_rd
                    (map.put store tbl (interp_expr store env e))
                    (map.put store tbl
                       (interp_expr store env (erase_record_field f e)))
                    env
                    (erased_at_put_tbl tbl f store store _ _
                       (erased_at_refl tbl f store)
                       (fun t H_t => proj_field_erase_record f store env e t H_t)))).
    exact H_x.
  Qed.


  (* ================================================================
     Type preservation.

     The table's type loses one entry, so every read of it has to be retyped.
     Every other field is still reachable at the same type
     (access_record_rm_field), and a bare read of the table is refused by the
     check, so no expression changes type at all.
     ================================================================ *)
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.

  Local Ltac apply_erase_ty_IH :=
    lazymatch goal with
    | IH : context[type_of _ _ ?e _] |- type_of _ _ ?e _ => apply IH
    end.

  (* Discharging a Forall2 whose relation is an implication, when the
     antecedent holds of every element.  The record literal's components come
     out of type_of_IH in exactly that shape. *)
  Lemma Forall2_impl_In : forall A B (P : A -> B -> Prop) (Q : A -> Prop) la lb,
      Forall2 (fun a b => Q a -> P a b) la lb ->
      (forall a, In a la -> Q a) ->
      Forall2 P la lb.
  Proof.
    intros * H_all2; induction H_all2 as [| a b la lb H_head H_tail IH ];
      intros H_Q; [ constructor | ].
    constructor.
    1: apply H_head, H_Q; left; reflexivity.
    1: apply IH; intros a0 H_a0; apply H_Q; right; exact H_a0.
  Qed.

  (* A field read through a mutable variable, which is the only place the
     table's own type is consulted.  Stated as a lemma so the induction below
     does not have to take two store-type lookups apart inline. *)
  Lemma erase_ty_access : forall tbl f tl (Gstore : tenv) Genv y tl0 s T,
      map.get (map.put Gstore tbl (TRecord tl)) y = Some (TRecord tl0) ->
      access_record tl0 s = Success T ->
      (y = tbl -> s <> f) ->
      type_of (map.put Gstore tbl (TRecord (rm_field f tl))) Genv
        (EAccess (ELoc y) s) T.
  Proof.
    intros * E_y E_s H_s.
    destruct (String.eqb y tbl) eqn:E.
    - apply String.eqb_eq in E; subst y.
      rewrite map.get_put_same in E_y.
      injection E_y as E_y; subst tl0.
      econstructor; [ constructor; apply map.get_put_same | ].
      rewrite access_record_rm_field by (apply H_s; reflexivity); exact E_s.
    - apply String.eqb_neq in E.
      rewrite map.get_put_diff in E_y by congruence.
      econstructor;
        [ constructor; rewrite map.get_put_diff by congruence; exact E_y
        | exact E_s ].
  Qed.

  Lemma erase_preserve_ty_expr : forall tbl f tl (Gstore : tenv) Genv e T,
      type_of (map.put Gstore tbl (TRecord tl)) Genv e T ->
      expr_reads_no_field tbl f e = true ->
      type_of (map.put Gstore tbl (TRecord (rm_field f tl))) Genv e T.
  Proof.
    intros tbl f tl Gstore Genv e T H_ty.
    induction H_ty using type_of_IH; cbn [expr_reads_no_field]; intros H_rd.
    all: repeat rewrite Bool.andb_true_iff in H_rd.
    all: repeat lazymatch goal with H : _ /\ _ |- _ => destruct H end.
    (* The cases that mention the table are picked by shape, not by position,
       so the uniform step below cannot half-solve them. *)
    (* ELoc: the check says this is not the table *)
    all: try lazymatch goal with
           | |- type_of _ _ (ELoc _) _ =>
               apply Bool.negb_true_iff, String.eqb_neq in H_rd;
               constructor;
               rewrite map.get_put_diff by congruence;
               lazymatch goal with
               | Hg : map.get (map.put _ _ _) _ = Some _ |- _ =>
                   rewrite map.get_put_diff in Hg by congruence; exact Hg
               end
           end.
    (* ERecord: the literal is unchanged, so the same field types serve and
       only each component has to be retyped *)
    all: try lazymatch goal with
           | |- type_of _ _ (ERecord _) _ =>
               rewrite forallb_forall in H_rd;
               econstructor; eauto
           end.
    (* EAccess: the check's own match on the accessed expression is what
       distinguishes a read of the table, so take it apart *)
    all: try lazymatch goal with
           | |- type_of _ _ (EAccess _ _) _ =>
               lazymatch goal with x : expr |- _ => destruct x end;
               cbn [expr_reads_no_field] in H_rd
           end.
    (* the field read, settled before the uniform step can commit it to an
       induction hypothesis it cannot discharge *)
    all: try lazymatch goal with
           | |- type_of _ _ (EAccess (ELoc _) _) _ =>
               eapply erase_ty_access;
               [ lazymatch goal with
                 | H : type_of _ _ (ELoc _) _ |- _ =>
                     inversion H; subst; eassumption
                 end
               | eassumption
               | intros ->; cbn in H_rd; rewrite String.eqb_refl in H_rd;
                 apply Bool.negb_true_iff, String.eqb_neq in H_rd; assumption ]
           end.
    (* everything whose type does not mention the table rebuilds as it was *)
    all: try (econstructor; eauto; try apply_erase_ty_IH; eauto).
    (* and the record literal's components: the literal is unchanged, so the
       same field types serve and each component is retyped by its own IH *)
    1:{ (* the relation is read off the goal: unifying it with the lemma's
           implication shape would ask Coq to split an arrow it cannot *)
        match goal with
        | H : Forall2 _ ?la ?lb |- Forall2 ?P ?la ?lb =>
            apply (Forall2_impl_In _ _ P
                     (fun e => expr_reads_no_field tbl f e = true) la lb H)
        end.
        intros a H_a; apply in_map_iff in H_a as [ q [ E_q H_q ] ]; subst a.
        apply H_rd; exact H_q. }
  Qed.


  Lemma Forall2_impl_In' : forall A B (P P' : A -> B -> Prop) (Q : A -> Prop) la lb,
      Forall2 P la lb ->
      (forall a, In a la -> Q a) ->
      (forall a b, Q a -> P a b -> P' a b) ->
      Forall2 P' la lb.
  Proof.
    intros * H_all2; induction H_all2 as [| a b la lb H_head H_tail IH ];
      intros H_Q H_imp; [ constructor | ].
    constructor.
    1: apply H_imp; [ apply H_Q; left; reflexivity | exact H_head ].
    1: apply IH; [ intros a0 H_a0; apply H_Q; right; exact H_a0 | exact H_imp ].
  Qed.

  (* A record literal written to the table, retyped at the shortened type.
     The same field-type list serves, minus the entry that went. *)
  Lemma erase_record_ty : forall tbl f tl (Gstore : tenv) Genv l,
      type_of (map.put Gstore tbl (TRecord tl)) Genv (ERecord l) (TRecord tl) ->
      expr_reads_no_field tbl f (ERecord (rm_field f l)) = true ->
      type_of (map.put Gstore tbl (TRecord (rm_field f tl))) Genv
        (ERecord (rm_field f l)) (TRecord (rm_field f tl)).
  Proof.
    intros * H_ty H_rd.
    inversion H_ty as [| | | | | | | | | | | | | | l0 tl0 tl1 E_fst H_all2 H_perm H_nd H_ss | | | | | | | ];
      subst.
    cbn [expr_reads_no_field] in H_rd; rewrite forallb_forall in H_rd.
    econstructor.
    (* the names of the surviving components still agree *)
    1:{ unfold rm_field.
        rewrite <- 2 (filter_map_swap (fun s => negb (String.eqb s f)) fst).
        rewrite E_fst; reflexivity. }
    (* each surviving component retypes *)
    1:{ eapply Forall2_impl_In' with
          (P := type_of (map.put Gstore tbl (TRecord tl)) Genv)
          (Q := fun e => expr_reads_no_field tbl f e = true).
        1: apply Forall2_rm_field; assumption.
        1:{ intros a H_a; apply in_map_iff in H_a as [ q [ E_q H_q ] ]; subst a.
            apply H_rd; exact H_q. }
        1: intros a b H_q H_P; apply erase_preserve_ty_expr; assumption. }
    1: apply Permutation_rm_field; assumption.
    1: apply rm_field_NoDup; assumption.
    1: apply rm_field_SSorted; assumption.
  Qed.

  (* ----------------------------------------------------------------
     Commands, under the table's shortened type.
     ---------------------------------------------------------------- *)
  Lemma erase_preserve_ty_cmd : forall tbl f c tl (Gstore : tenv) Genv,
      well_typed (map.put Gstore tbl (TRecord tl)) Genv c ->
      command_reads_no_field tbl f (erase_body tbl f c) = true ->
      writes_erasable tbl c = true ->
      well_typed (map.put Gstore tbl (TRecord (rm_field f tl))) Genv
        (erase_body tbl f c).
  Proof.
    intros tbl f c; induction c; intros tl Gstore Genv H_wt H_rd H_we;
      cbn [erase_body] in H_rd |- *;
      cbn [command_reads_no_field writes_erasable erasable_record] in H_rd, H_we;
      invert_well_typed.
    (* CSkip *)
    1: constructor.
    (* CSeq *)
    1:{ rewrite Bool.andb_true_iff in H_rd, H_we.
        destruct H_rd as [ R1 R2 ]; destruct H_we as [ W1 W2 ].
        constructor; [ apply IHc1 | apply IHc2 ]; eassumption. }
    (* CLet *)
    1:{ rewrite Bool.andb_true_iff in H_rd; destruct H_rd as [ R1 R2 ].
        econstructor.
        1: apply erase_preserve_ty_expr; eassumption.
        1: apply IHc; eassumption. }
    (* CLetMut: the check refuses a binder shadowing the table, so the two
       puts commute and the body's induction hypothesis applies *)
    1:{ repeat rewrite Bool.andb_true_iff in H_rd.
        destruct H_rd as [ [ H_ne R1 ] R2 ].
        apply Bool.negb_true_iff, String.eqb_neq in H_ne.
        rewrite (proj2 (String.eqb_neq _ _) H_ne) in R2, H_we |- *.
        econstructor; [ apply erase_preserve_ty_expr; eassumption | ].
        (* the two puts commute, so the body's hypothesis can be read with
           the binder folded into the store and the IH applies *)
        rewrite (Properties.map.put_comm tbl x
                   (TRecord (rm_field f tl)) t Gstore (not_eq_sym H_ne)).
        apply IHc; [ | exact R2 | exact H_we ].
        rewrite <- (Properties.map.put_comm tbl x
                      (TRecord tl) t Gstore (not_eq_sym H_ne)).
        eassumption. }
    (* CAssign *)
    1:{ destruct (String.eqb x tbl) eqn:E_x.
        2:{ apply String.eqb_neq in E_x.
            econstructor;
              [ rewrite map.get_put_diff in * by congruence; eassumption
              | apply erase_preserve_ty_expr; eassumption ]. }
        apply String.eqb_eq in E_x; subst x.
        rewrite map.get_put_same in *.
        lazymatch goal with
        | H : Some (TRecord tl) = Some ?t0 |- _ =>
            injection H as H; subst t0
        end.
        (* the check says the write is an erasable record literal *)
        destruct e; cbn [writes_erasable erasable_record] in H_we;
          try discriminate.
        cbn [erase_record_field] in H_rd |- *.
        rewrite H_we in H_rd |- *.
        econstructor; [ apply map.get_put_same | ].
        apply erase_record_ty; eassumption. }
    (* CIf *)
    1:{ repeat rewrite Bool.andb_true_iff in H_rd.
        rewrite Bool.andb_true_iff in H_we.
        destruct H_rd as [ [ R1 R2 ] R3 ]; destruct H_we as [ W1 W2 ].
        constructor.
        1: apply erase_preserve_ty_expr; eassumption.
        1: apply IHc1; eassumption.
        1: apply IHc2; eassumption. }
    (* CForeach *)
    1:{ rewrite Bool.andb_true_iff in H_rd; destruct H_rd as [ R1 R2 ].
        econstructor.
        1: apply erase_preserve_ty_expr; eassumption.
        1: apply IHc; eassumption. }
  Qed.


  (* The initializer, where the store type is not yet changed and so no
     expression has to be retyped. *)
  Lemma erase_record_ty_init : forall f (Gstore : tenv) Genv l tl,
      type_of Gstore Genv (ERecord l) (TRecord tl) ->
      type_of Gstore Genv (ERecord (rm_field f l)) (TRecord (rm_field f tl)).
  Proof.
    intros * H_ty.
    inversion H_ty as [| | | | | | | | | | | | | | l0 tl0 tl1 E_fst H_all2 H_perm H_nd H_ss | | | | | | | ];
      subst.
    econstructor.
    1:{ unfold rm_field.
        rewrite <- 2 (filter_map_swap (fun s => negb (String.eqb s f)) fst).
        rewrite E_fst; reflexivity. }
    1: apply Forall2_rm_field; assumption.
    1: apply Permutation_rm_field; assumption.
    1: apply rm_field_NoDup; assumption.
    1: apply rm_field_SSorted; assumption.
  Qed.

  (* ================================================================
     The pass is sound.

     transf_sound quantifies over ONE store type environment for input and
     output, which a body-level pass changing a variable's type could not
     satisfy.  This is a letmut-level pass, so the outer environment is
     untouched and only the body's differs -- the same reason
     apply_idx_related_transfs is stated this way.
     ================================================================ *)
  Theorem erase_dead_field_sound : forall f,
      transf_sound (locals := locals) (erase_dead_field f).
  Proof.
    unfold transf_sound, erase_dead_field; intros f Gstore Genv c H_Gs H_Ge H_wt.
    destruct c as [ | | | e tbl c0 | | | ];
      try (split; [ exact H_wt | intros; reflexivity ]).
    destruct (erasable_record e && writes_erasable tbl c0
              && command_reads_no_field tbl f (erase_body tbl f c0))%bool eqn:E;
      [ | split; [ exact H_wt | intros; reflexivity ] ].
    repeat rewrite Bool.andb_true_iff in E.
    destruct E as [ [ E_init E_writes ] E_reads ].
    (* the initializer is a record literal, so the table's type is a record
       type and the erasure shortens both together *)
    destruct e as [ | | | | | | | | | | | | l | | | | | ];
      cbn [erasable_record] in E_init; try discriminate.
    invert_well_typed.
    lazymatch goal with
    | H : type_of Gstore Genv (ERecord l) ?t |- _ =>
        assert (E_t : exists tl, t = TRecord tl)
          by (inversion H; subst; eauto)
    end.
    destruct E_t as [ tl E_t ]; subst.
    rewrite (erase_record_field_ERecord f l E_init).
    split.
    (* type preservation *)
    1:{ econstructor.
        1: apply erase_record_ty_init; eassumption.
        1: apply erase_preserve_ty_cmd; assumption. }
    (* and semantics *)
    1:{ intros store env H_store H_env.
        rewrite <- (erase_record_field_ERecord f l E_init).
        apply (erase_letmut_preserve_sem tbl f (ERecord l) c0 store env E_reads). }
  Qed.

End WithMap.
