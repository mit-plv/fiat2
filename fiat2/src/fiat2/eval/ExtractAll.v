Require Import fiat2.Language fiat2.Value fiat2.Interpret fiat2.TypeSystem.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
Require Import coqutil.Datatypes.Result.
Require fiat2.eval.Extract fiat2.eval.Elaborate fiat2.eval.Enumerate.
From Stdlib Require Import List String extraction.Extraction
  extraction.ExtrOcamlBasic extraction.ExtrOcamlZInt
  extraction.ExtrOcamlNativeString.
Import ListNotations.

(* ============================================================
   The one extraction driver.

   eval/Extract.v chooses WHICH configuration each subject contributes and
   says why; eval/Elaborate.v turns both of a subject's columns into fully
   type-annotated terms.  Both leave through here, in one Extraction
   command, so the AST types are emitted once and the two lists are of the
   same OCaml type.  Two drivers would emit two copies and OCaml would
   treat them as unrelated.

   The output filename is unchanged, so harness/generated/dune and
   everything that already reads Extracted.subjects keeps working; what is
   new is annotated_nf beside it.

   WHY A NORMAL FORM.  annotated is a computation over the optimizer's own
   functions -- mk_idxs, mk_compo_idx, idx_ty, and the typechecker.
   Reducing it here means the backend receives DATA: no part of the
   optimizer and no part of the checker is extracted alongside it, and
   there is no transcription step between the verified optimizer's output
   and the thing that gets compiled.  Same discipline as the unannotated
   terms in eval/Extract.v.
   ============================================================ *)

Definition annotated_nf : list (string * command * command) :=
  Eval vm_compute in Elaborate.annotated.

(* and the table's type before and after the rewrite, which the annotations
   cannot show -- see eval/Elaborate.v's note on tbl_tys *)
Definition tbl_types_nf : list (string * type * type) :=
  Eval vm_compute in Elaborate.tbl_types.

(* and what each subject's inputs are named and typed *)
Definition envs_nf : list (string * list (string * type) * list (string * type)) :=
  Eval vm_compute in Elaborate.envs.

(* ============================================================
   The typechecker itself, callable from OCaml.

   The backend is a type-directed pass: at every node it needs to know what
   it is compiling, in order to pick a record layout, an unboxed scalar or a
   structure.  The annotations give it the collection types a program
   creates; for everything else it has to ask.

   It asks THIS function.  Writing a second synthesizer in OCaml would be
   the one thing the development's own comments warn against -- "being in
   sync is not something to keep checking, it is the same function" -- and
   the gap would be invisible, since a wrong type produces compiling code
   that computes the wrong thing.  Environments cross as association lists
   so that no coqutil representation does.
   ============================================================ *)

Section Synth.
  Instance stenv : map.map string type := SortedListString.map _.
  Instance stenv_ok : map.ok stenv := SortedListString.ok _.

  Definition synth (store env : list (string * type)) (e : expr)
    : result (type * expr) :=
    synthesize_expr (map.of_list store) (map.of_list env) e.
End Synth.

Extraction Language OCaml.
Set Extraction Output Directory "harness/generated".

(* The enumeration crosses as DATA PLUS FUNCTIONS, not as terms: there are
   864 configurations and each term is the size of a program, so normalising
   them here would cost the Rocq build minutes and this module megabytes.
   eval/Enumerate.v says why, and runner_reproduces_every_subject is the pin
   that run_al -- the function the harness calls -- is the same pipeline
   whose output each subject file proves sound.

   This is also why the three files the optimizer reached through a module
   ALIAS no longer use one: monolithic extraction cannot follow an alias,
   and this is the first thing to ask for a function from inside the
   optimizer rather than a term it produced. *)
Extraction "extracted.ml"
  Extract.subjects Extract.alternatives Extract.ref_run
  annotated_nf tbl_types_nf envs_nf synth
  Enumerate.esubjects Enumerate.configs_al Enumerate.run_al
  Enumerate.describe Enumerate.is_sel_al.
