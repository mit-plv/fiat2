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
