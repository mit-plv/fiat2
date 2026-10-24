Require Import fiat2.Language fiat2.Value fiat2.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
Require fiat2.eval.Keycloak_CachedRealm fiat2.eval.Kafka_NamedCache
  fiat2.eval.Kafka_Cluster fiat2.eval.Kafka_WindowStore
  fiat2.eval.HA_AreaRegistry fiat2.eval.HA_LookinFunctions
  fiat2.eval.Jenkins_UserSearch fiat2.Ex_RangeDelete.
From Stdlib Require Import List String extraction.Extraction
  extraction.ExtrOcamlBasic extraction.ExtrOcamlZInt
  extraction.ExtrOcamlNativeString.
Import ListNotations.
Local Open Scope string.

(* ============================================================
   The subject programs, as OCaml values.

   WHAT CROSSES THE BOUNDARY, and why exactly this much.

   The abstract syntax -- type, atom, unop, binop, ternop, expr, command,
   and the three tags -- the subject programs themselves, each one both
   before and after the optimizer, and the Gallina interpreter.

   THE INTERPRETER IS HERE AS AN ORACLE, NOT AS THE EVALUATOR.  Nothing
   that measures anything calls it.  The measurement runs harness/eval.ml,
   which is written by hand against the denotations with persistent maps,
   because the specification's dictionaries are canonical sorted
   association lists: extracting it as the evaluator would give one in
   which every insert and every lookup is linear, destroying the
   incrementality the measurement exists to show, in exactly the direction
   that matters.

   What the extracted interpreter is for is harness/differential.ml, which
   runs it and the hand-written evaluator on the same subject programs over
   the same generated inputs and compares the results.  That is the only
   link between the two, and it is the right one: a specification is a
   thing to be checked against, and the hand-written evaluator is otherwise
   unverified code sitting directly underneath the performance claim.

   ref_run takes and returns association lists rather than the map type, so
   that the boundary carries no coqutil representation into OCaml; the
   locals instance is fixed here, where it is an implementation detail of
   the oracle and of nothing else.

   WHY EXTRACT THE PROGRAMS rather than print and re-parse them.  Each
   term below is the normal form of the very definition the soundness
   theorem in its own file is about, reduced here by vm_compute and handed
   to OCaml as data.  So there is no transcription step between the
   verified optimizer's output and the thing that gets benchmarked.  That
   link would otherwise sit exactly where the performance claim is made.

   TWO UNVERIFIED MAPPINGS, which belong in the paper's assumptions beside
   the choice of persistent maps:

     Z      -> OCaml int     (ExtrOcamlZInt).  Sound while every integer
                             in a run stays in range; the generators keep
                             them small, and nothing here does arithmetic
                             that could overflow silently into a wrong
                             ANSWER rather than a wrong cost.
     string -> OCaml string  (ExtrOcamlNativeString).  This one is not
                             cosmetic: the default extraction of a Rocq
                             string is a list of characters, which would
                             make OStrContains and OSubstring linear in
                             the wrong parameter and would distort the
                             trigram subject specifically.
   ============================================================ *)

Section Oracle.
  Instance rlocals : map.map string value := SortedListString.map _.

  Definition ref_run (store env : list (string * value)) (c : command)
    : list (string * value) :=
    map.tuples (interp_command (map.of_list store) (map.of_list env) c).
End Oracle.

Extraction Language OCaml.
Set Extraction Output Directory "harness/generated".

Module KC := Keycloak_CachedRealm.
Module NC := Kafka_NamedCache.
Module AR := HA_AreaRegistry.
Module LF := HA_LookinFunctions.
Module JU := Jenkins_UserSearch.
Module KCl := Kafka_Cluster.
Module KWS := Kafka_WindowStore.
Module ERD := Ex_RangeDelete.

(* ---- the scan form each subject starts from ---- *)

Definition keycloak_src : command := Eval vm_compute in KC.elaborated KC.decls.
Definition named_cache_src : command := Eval vm_compute in NC.elaborated NC.decls.
Definition area_registry_src : command := Eval vm_compute in AR.elaborated AR.decls.
Definition lookin_src : command := Eval vm_compute in LF.elaborated.
Definition user_search_src : command := Eval vm_compute in JU.elaborated JU.decls.
Definition cluster_src : command := Eval vm_compute in KCl.prog.
Definition window_store_src : command := Eval vm_compute in KWS.prog.
Definition range_delete_src : command := Eval vm_compute in ERD.prog.

(* ---- what the optimizer produces under the configuration the
       deterministic selector picks (eval/SelectorTests.v) ---- *)

Definition keycloak_opt : command := Eval vm_compute in KC.optimized_counted.
Definition named_cache_opt : command := Eval vm_compute in NC.optimized.
Definition area_registry_opt : command := Eval vm_compute in AR.optimized.
Definition lookin_opt : command := Eval vm_compute in LF.optimized.
Definition user_search_opt : command := Eval vm_compute in JU.optimized.
Definition cluster_opt : command :=
  Eval vm_compute in nth 0 KCl.prog_transformed CSkip.
Definition window_store_opt : command :=
  Eval vm_compute in nth 1 KWS.prog_transformed CSkip.
Definition range_delete_opt : command :=
  Eval vm_compute in nth 0 ERD.prog_transformed CSkip.

(* ---- the alternatives worth measuring against, each one a
       configuration its own file pins and argues about ---- *)

(* without the maintained row count: the whole-table count stays a fold
   and the list survives to be folded over *)
Definition keycloak_opt_uncounted : command := Eval vm_compute in KC.optimized.
(* the aggregate listed before its dictionary -- hazard 4, where the
   delete's correction term is left scanning *)
Definition named_cache_opt_swapped : command := Eval vm_compute in NC.optimized_swapped.
(* with the table's set representation: the list is erased and replaced *)
Definition user_search_opt_rep : command := Eval vm_compute in JU.optimized_rep.
(* without SplitIf: both conjunctive reads stay scans *)
Definition cluster_opt_unsplit : command :=
  Eval vm_compute in nth 1 KCl.prog_transformed CSkip.
(* without SplitIf: fetchAll keeps both of its bounds, and fetch stays a
   scan -- over a list that therefore survives, and that retention then
   rewrites in full on every call *)
Definition window_store_opt_unsplit : command :=
  Eval vm_compute in nth 0 KWS.prog_transformed CSkip.

(* ---- one value for the harness to iterate over ---- *)

Definition subjects : list (string * command * command) :=
  [ ("keycloak", keycloak_src, keycloak_opt)
  ; ("named_cache", named_cache_src, named_cache_opt)
  ; ("area_registry", area_registry_src, area_registry_opt)
  ; ("lookin", lookin_src, lookin_opt)
  ; ("user_search", user_search_src, user_search_opt)
  ; ("cluster", cluster_src, cluster_opt)
  ; ("window_store", window_store_src, window_store_opt)
  ; ("range_delete", range_delete_src, range_delete_opt) ].

Definition alternatives : list (string * command) :=
  [ ("keycloak/uncounted", keycloak_opt_uncounted)
  ; ("named_cache/swapped", named_cache_opt_swapped)
  ; ("user_search/table-rep", user_search_opt_rep)
  ; ("cluster/unsplit", cluster_opt_unsplit)
  ; ("window_store/unsplit", window_store_opt_unsplit) ].

Extraction "extracted.ml" subjects alternatives ref_run.
