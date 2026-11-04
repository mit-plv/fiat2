Require Import fiat2.Language fiat2.Value fiat2.Interpret.
Require fiat2.eval.Extract fiat2.eval.Elaborate.
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

Extraction Language OCaml.
Set Extraction Output Directory "harness/generated".

Extraction "extracted.ml"
  Extract.subjects Extract.alternatives Extract.ref_run
  annotated_nf tbl_types_nf envs_nf.
