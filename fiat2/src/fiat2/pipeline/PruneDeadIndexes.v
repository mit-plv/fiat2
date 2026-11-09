(* ====================================================================
   Dropping an index choice whose member nothing reads.

   THE PROBLEM, and it is measured rather than imagined.  An index is
   installed because a read asked for it, and a later rule can take that
   read away: SplitIf peels the first conjunct off a conjunction and hands
   it to a single-attribute dictionary, after which the composite rule's
   pattern no longer matches, so the composite member is installed,
   maintained on every write, and never read.  eval/Kafka_Cluster's
   configuration 3 is that program -- 1.66x on the build against
   configuration 0, for a member no query touches -- and
   eval/HA_EntityRegistry's configuration 2 is the same shape at 1.2x on the
   build and 1.2x on every insert.  Both are pinned there as alternatives.
   It is the ninth entry in this development's list of silent
   pessimizations, and the only defence so far has been that the selector
   declines to emit the pair.

   THE APPROACH, and why it needs no new verified pass.  EraseField removes
   the row list by rewriting the program: the field is dropped from every
   record literal and the result is checked to read it nowhere.  That is a
   real transformation and it costs ~700 lines of soundness.  An index
   member needs none of that, because an index member exists only because a
   CHOICE asked for it -- so instead of erasing the member, drop the choice
   and run the pipeline again.

   What makes that free is the shape of the pipeline's soundness theorem:
   apply_all_transfs_sound and apply_all_transfs_constrained_sound are
   universally quantified over the choice lists with NO side condition on
   them ("Nothing is assumed about the index choices").  So any choice list
   yields a sound program, and a pruned list is just another choice list.
   The soundness proofs below are three lines each, and they are the same
   theorem instantiated at the pruned list.

   WHAT THIS MEANS FOR THE DECISION PROCEDURE: it needs no correctness
   proof, and that is not a gap.  If cmd_reads_member says "dead" of a
   member something does read, the pruned program simply does not have that
   member, the rewrite that wanted it does not fire, and the read stays a
   scan -- slower, never wrong.  The procedure is a heuristic in the same
   sense the selector is, and it is the only part of this file that could be
   wrong in a way the compiler would not catch.  It is written to be read.

   WHAT IT DOES NOT DO.  It does not prune a member that is read only
   because another member exists; one round of pruning can expose another,
   so the driver takes a round count.  And it decides deadness per TABLE
   NAME: a program with two indexed tables must be pruned at each, since
   members of different tables share the numbering "0", "1", ... .
   ==================================================================== *)
Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.TransfSound fiat2.constraint.Decl fiat2.constraint.Surface fiat2.pipeline.Pipeline.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import List String ZArith.
Import ListNotations.

Section WithTable.
  (* the table's variable and the field its index record sits at *)
  Context (tbl aux_tag : string).

  (* ----------------------------------------------------------------
     Does an expression read the member at tag m?

     Three ways it can, and the first two are why this is not a search for
     the string m.  A bare ELoc tbl hands the whole record over, and an
     EAccess of it at aux_tag hands the whole index record over; either way
     every member is read.  Otherwise only the two-step access names a
     member, and it names exactly one.
     ---------------------------------------------------------------- *)
  Fixpoint reads_member (m : string) (e : expr) : bool :=
    match e with
    | EVar _ | EAtom _ => false
    | ELoc x => String.eqb x tbl
    | EAccess (EAccess (ELoc x) a) s =>
        if (String.eqb x tbl && String.eqb a aux_tag)%bool
        then String.eqb s m
        else false
    | EAccess (ELoc x) a => (String.eqb x tbl && String.eqb a aux_tag)%bool
    | EAccess r _ => reads_member m r
    | EUnop _ e1 | EACFold _ e1 | EACIFold _ e1 | ESort _ e1 =>
        reads_member m e1
    | EBinop _ e1 e2 | ELet e1 _ e2 | EFlatmap _ e1 _ e2 =>
        (reads_member m e1 || reads_member m e2)%bool
    | ETernop _ e1 e2 e3 | EIf e1 e2 e3 | EFold e1 e2 _ _ e3 =>
        (reads_member m e1 || reads_member m e2 || reads_member m e3)%bool
    | EOptMatch e1 e_none _ e_some =>
        (reads_member m e1 || reads_member m e_none
         || reads_member m e_some)%bool
    | ERecord l => existsb (fun p => reads_member m (snd p)) l
    end.

  (* ----------------------------------------------------------------
     A write to the table rebuilds the whole record, and the member's own
     new value is allowed to read the member's old value -- that is the
     self-feeding loop a maintenance rule produces, and it does not keep
     the member alive.  Everything ELSE in the write does: the row list's
     new value, and the other members' new values.

     This is the same decision EraseField makes by running its check on
     the pass's OUTPUT; here there is no output to check, so the exclusion
     is written down.
     ---------------------------------------------------------------- *)
  Definition write_reads_member (m : string) (e : expr) : bool :=
    match e with
    | ERecord l =>
        existsb
          (fun p =>
             if String.eqb (fst p) aux_tag
             then match snd p with
                  | ERecord al =>
                      existsb (fun q => (negb (String.eqb (fst q) m)
                                         && reads_member m (snd q))%bool) al
                  | other => reads_member m other
                  end
             else reads_member m (snd p))
          l
    | other => reads_member m other
    end.

  Fixpoint cmd_reads_member (m : string) (c : command) : bool :=
    match c with
    | CSkip => false
    | CSeq c1 c2 => (cmd_reads_member m c1 || cmd_reads_member m c2)%bool
    | CLet e _ c1 => (reads_member m e || cmd_reads_member m c1)%bool
    (* the table's own binder is where the record is introduced, so its
       initializer is a write and the body is where the reads are *)
    | CLetMut e x c1 =>
        if String.eqb x tbl
        then (write_reads_member m e || cmd_reads_member m c1)%bool
        else (reads_member m e || cmd_reads_member m c1)%bool
    | CAssign x e =>
        if String.eqb x tbl then write_reads_member m e else reads_member m e
    | CIf e c1 c2 =>
        (reads_member m e || cmd_reads_member m c1
         || cmd_reads_member m c2)%bool
    | CForeach e _ c1 => (reads_member m e || cmd_reads_member m c1)%bool
    end.

End WithTable.

(* ----------------------------------------------------------------
   Which tags a choice owns.

   Read off mk_idx rather than tabulated, so a choice that changes how many
   members it installs cannot drift away from this file.
   ---------------------------------------------------------------- *)
Fixpoint choice_tags (ds : list decl) (reps cur : nat) (ics : list index_choice)
  : list (index_choice * list string) :=
  match ics with
  | [] => []
  | ic :: ics' =>
      let '(idxs, _, next) := mk_idx ds cur reps ic in
      (ic, List.map (fun p => fst (fst p)) idxs)
        :: choice_tags ds reps next ics'
  end.

(* A choice survives when the program reads at least one of its members. *)
Definition live_ics (tbl aux_tag : string) (ds : list decl) (reps : nat)
  (out : command) (ics : list index_choice) : list index_choice :=
  List.map fst
    (List.filter
       (fun p => existsb (fun t => cmd_reads_member tbl aux_tag t out) (snd p))
       (choice_tags ds reps O ics)).

Section WithPipeline.

  (* ----------------------------------------------------------------
     The unconstrained pipeline, pruned.
     ---------------------------------------------------------------- *)

  Definition prune_icss_once (tbl : string) (reps : nat) (fs : list basic_transf)
    (icss : list (list index_choice)) (Gstore Genv : ctenv) (c : command)
    : list (list index_choice) :=
    let out := apply_all_transfs reps fs icss Gstore Genv c in
    List.map (live_ics tbl "aux_tag" [] reps out) icss.

  Fixpoint prune_icss (rounds : nat) (tbl : string) (reps : nat)
    (fs : list basic_transf) (icss : list (list index_choice))
    (Gstore Genv : ctenv) (c : command) : list (list index_choice) :=
    match rounds with
    | O => icss
    | S rounds' =>
        prune_icss rounds' tbl reps fs
          (prune_icss_once tbl reps fs icss Gstore Genv c) Gstore Genv c
    end.

  Definition apply_all_transfs_pruned (rounds : nat) (tbl : string) (reps : nat)
    (fs : list basic_transf) (icss : list (list index_choice))
    (Gstore Genv : ctenv) (c : command) : command :=
    apply_all_transfs reps fs
      (prune_icss rounds tbl reps fs icss Gstore Genv c) Gstore Genv c.

  (* THE SOUNDNESS, and it is three lines because the pipeline's own theorem
     assumes nothing about the choice list.  Pruning does not need to be
     RIGHT for this to hold -- it needs only to produce a choice list. *)
  Theorem apply_all_transfs_pruned_sound :
    forall rounds tbl reps fs icss,
      transf_sound (locals := clocals)
        (fun Gstore Genv c =>
           apply_all_transfs_pruned rounds tbl reps fs icss Gstore Genv c).
  Proof.
    unfold transf_sound, apply_all_transfs_pruned; intros.
    apply (apply_all_transfs_sound reps fs
             (prune_icss rounds tbl reps fs icss Gstore Genv c));
      assumption.
  Qed.

  Definition apply_optimize_anno_pruned (rounds : nat) (tbl : string)
    (ac : anno_command) (Gstore Genv : ctenv) : command :=
    match ac with
    | AC fs icss c => apply_all_transfs_pruned rounds tbl 10000 fs icss Gstore Genv c
    end.

  Theorem apply_optimize_anno_pruned_sound :
    forall rounds tbl fs icss (Gstore Genv : ctenv) c,
      tenv_wf Gstore -> tenv_wf Genv -> well_typed Gstore Genv c ->
      well_typed Gstore Genv
        (apply_optimize_anno_pruned rounds tbl (AC fs icss c) Gstore Genv)
      /\ forall (store env : clocals),
          locals_wf Gstore store -> locals_wf Genv env ->
          interp_command store env
            (apply_optimize_anno_pruned rounds tbl (AC fs icss c) Gstore Genv)
          = interp_command store env c.
  Proof.
    intros.
    apply (apply_all_transfs_pruned_sound rounds tbl 10000 fs icss);
      assumption.
  Qed.

End WithPipeline.
