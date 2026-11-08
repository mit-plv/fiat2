Require Import fiat2.Language fiat2.constraint.Decl fiat2.constraint.Surface fiat2.Pipeline fiat2.Selector.
Require fiat2.eval.Extract.
Require Import fiat2.eval.Elaborate.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
From Stdlib Require Import String List.
Import ListNotations.
Local Open Scope string.

(* ============================================================
   ENUMERATE AND MEASURE.

   eval/Selector.v picks one configuration per table and argues for it.
   This file does not argue: it generates every configuration the demands
   admit, with every policy decision of `choices_of` turned into an
   alternative, and hands all of them to the harness to be measured.

   WHY THIS IS SOUND FOR FREE, and why it is cheap here and expensive
   elsewhere.  elab_apply_optimize_anno_constrained_sound quantifies over
   the rewrite list and both index-choice lists --
   `forall sc ce free_vars fs cics icss` -- with NO hypothesis constraining
   any of them.  So every configuration this file emits is well-typed and
   semantics-preserving by that theorem, whatever the enumeration does.  A
   candidate too many costs a measurement, never a wrong program.  Nothing
   below is a new trusted component; the enumerator is a generator of
   inputs to a function whose soundness is already proved for all inputs.

   WHAT IS ENUMERATED.  Six decisions that `choices_of` and `basics_of`
   make by policy, each with the hazard it was written to avoid:

     - the trigram subsumption (a trigram index's key member subsumes a
       standalone key dictionary)
     - the min veto on a delete key (a dictionary bucketed where a minimum
       is cached answers nothing)
     - the composite/split conflict (hazard 9: SplitIf destroys the pattern
       the composite rule needs)
     - at most one keyed pairing (two pairings would install two key
       members)
     - the keys-gate on FilterEmptyToSetMem (hazard 3: it breaks the
       elaborated unique-key guard)
     - the ORDER of the choice list, which is the ordering spec the other
       hazards impose

   Each of those is an assertion in eval/Selector.v today, pinned by a
   lemma that says the selector's pick is a particular term.  Enumerating
   them turns each into a measurement: if the selector's policy is right,
   no enumerated configuration beats it, and that is checkable rather than
   argued.

   WHAT IS NOT ENUMERATED, so the claim is not read wider than it is.  The
   pool is derived from the DEMANDS, so a configuration no demand offers is
   not reached -- the list-valued dictionary of eval/Netbox_TemplateExtensions
   is the known case, since no demand is raised by a key-equality filter at
   list level.  Enumerating index kinds no read asks for is a different and
   much larger search, and this file does not attempt it.  The POSITIONS of
   the basic rewrites are also fixed, at the order basics_of gives them;
   only their presence is enumerated.
   ============================================================ *)

(* ---------- the arrangements of a candidate pool ---------- *)

Fixpoint insert_everywhere {A} (x : A) (l : list A) : list (list A) :=
  match l with
  | [] => [[x]]
  | y :: l' => ((x :: y :: l') :: map (fun r => y :: r) (insert_everywhere x l'))%list
  end.

Fixpoint perms {A} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: l' => flat_map (insert_everywhere x) (perms l')
  end.

Fixpoint sublists {A} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: l' => let r := sublists l' in (map (cons x) r ++ r)%list
  end.

(* every ordering of every subset of size at most [cap].  The empty
   arrangement is included, and is the no-index configuration. *)
Definition arrangements {A} (cap : nat) (l : list A) : list (list A) :=
  flat_map perms (filter (fun s => Nat.leb (length s) cap) (sublists l)).

(* ---------- the index-choice pool ---------- *)

(* Every index choice some demand offers, with the policy vetoes of
   choices_of lifted.  Permuted composites are still collapsed, because an
   index on (a, b) IS an index on (b, a) -- that is deduplication of one
   structure, not a policy about two. *)
Definition choice_pool (ce : cenv) (tbl : string) (ds : list demand)
  : list index_choice :=
  let keys := unique_keys ce tbl in
  let dicts := omap (fun d => match d with
     | DEq a => Some (if str_mem a keys then UniqueDictIdx a else DictIdx a)
     | DRange a => Some (RangedDictIdx a)
     | DSubstr a => match keys with k :: _ => Some (TrigramIdx a k) | [] => None end
     | DSimilar a => match keys with k :: _ => Some (TrigramIdx a k) | [] => None end
     (* the min veto lifted: choices_of declines this dictionary when a
        minimum is cached on the same attribute *)
     | DDelKey a => Some (if str_mem a keys then UniqueDictIdx a else DictIdx a)
     | _ => None end) ds in
  (* the composite/split conflict lifted: choices_of emits nothing here
     when DConjSplit is present *)
  let composites := drop_permuted_composites []
     (omap (fun d => match d with
                     | DComposite attrs => Some (CompositeDictIdx attrs)
                     | _ => None end) ds) in
  let reps := omap (fun d => match d with
                             | DRep ct => Some (TableRep ct) | _ => None end) ds in
  let aggs := (omap (fun d => match d with
                              | DSetOf a => Some (SetAgg a)
                              | DDelKey a => Some (SetAgg a)
                              | _ => None end) ds
     ++ omap (fun d => match d with DSum a => Some (SumAgg a) | _ => None end) ds
     ++ omap (fun d => match d with DMin a => Some (MinAgg a) | _ => None end) ds
     ++ (if demand_mem DCount ds then [CountAgg] else []))%list in
  (* both pairings offered as ADDITIONAL candidates rather than as
     replacements, so "at most one pairing" and the trigram subsumption are
     both decisions the measurement makes *)
  let kd := flat_map (fun k =>
     omap (fun c => match dict_attr c with
                    | Some a => if negb (String.eqb a k)
                                then Some (KeyedDictIdx a k) else None
                    | None => None end) dicts) (keyed_delete_keys keys ds) in
  let kc := flat_map (fun k =>
     omap (fun c => match c with
                    | CompositeDictIdx attrs => Some (KeyedCompositeIdx attrs k)
                    | _ => None end) composites) (keyed_delete_keys keys ds) in
  dedup_choices ((reps ++ composites ++ dicts ++ kd ++ kc ++ aggs)%list).

(* ---------- the basic-rewrite variants ---------- *)

Definition core_basics : list basic_transf :=
  [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap].

(* the optional slots of basics_of, in its order.  FilterEmptyToSetMem is
   offered whenever its demand is present, WITHOUT the keys-gate, which is
   what puts hazard 3 into the measurement. *)
Definition opt_pre (ds : list demand) : list (list basic_transf) :=
  ((if demand_mem DFilterProj ds then [[SplitFilterProj]] else [])
   ++ (if demand_mem DEmptyEqFilter ds then [[FilterEmptyToSetMem]] else []))%list.

Definition opt_post (ds : list demand) : list (list basic_transf) :=
  (map (fun a => [PromoteGuard a])
     (omap (fun d => match d with DPromote a => Some a | _ => None end) ds)
   ++ (if demand_mem DHoist ds then [[SwapFlatmapIf]] else [])
   ++ (if demand_mem DConjSplit ds then [[SplitIf]] else [])
   ++ (if existsb (fun d => match d with DFlag _ => true | _ => false end) ds
       then [[FlagFilterToEq]] else []))%list.

Definition basics_variants (ds : list demand) : list (list basic_transf) :=
  flat_map (fun p => map (fun q => (concat p ++ core_basics ++ concat q)%list)
                       (sublists (opt_post ds)))
    (sublists (opt_pre ds)).

(* ---------- the configurations of one subject ---------- *)

(* The pool is computed from the demands of the program AFTER the basic
   rewrites, exactly as `select` does, so it is recomputed per basics
   variant: whether SplitIf ran decides whether a conjunction is still a
   conjunction, and therefore whether a composite index is offered at all. *)
Definition configs (cap : nat) (s : subj)
  : list (list basic_transf * list index_choice) :=
  let ce := s_ce s in let tbl := s_tbl s in let c := s_sel s in
  flat_map (fun fs =>
     let c' := compose_basic_transfs (map mk_basic_transf fs) c in
     map (fun cs => (fs, cs))
       (arrangements cap (choice_pool ce tbl (demands_of tbl c'))))
    (basics_variants (demands_of tbl c)).

(* The cap is 3 because the longest configuration the selector itself picks
   is 3 (keycloak and entity_registry), and the enumeration has to contain
   the selector's pick for the comparison to mean anything -- which
   selector_config_is_enumerated below checks. *)
Definition cap : nat := 3.

(* ---------- running one configuration ---------- *)

(* One runner for every subject.  A table with declarations goes through the
   constrained pipeline with its choices as the DECLARED table's choices; a
   table without goes through the plain one with its choices as the only
   index-choice list.  That is the same split the subject files make, and
   runner_reproduces_every_subject is the check that this reproduces them. *)
Definition run (s : subj) (fc : list basic_transf * list index_choice) : command :=
  let '(fs, cs) := fc in
  match s_ce s with
  | [] => apply_optimize_anno (AC fs [cs] (s_sel s)) (s_Gstore s) (s_Genv s)
  | _ => apply_optimize_anno_constrained
           (CAC (s_ce s) O fs cs [] (s_sel s)) (s_Gstore s) (s_Genv s)
  end.

Definition sel_config (s : subj) : list basic_transf * list index_choice :=
  select (s_ce s) (s_tbl s) (s_sel s).

(* ---------- comparing configurations ---------- *)

Scheme Boolean Equality for basic_transf.

Fixpoint list_eqb {A} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: l1', y :: l2' => (eqb x y && list_eqb eqb l1' l2')%bool
  | _, _ => false
  end.

Definition cfg_beq (a b : list basic_transf * list index_choice) : bool :=
  (list_eqb basic_transf_beq (fst a) (fst b)
   && list_eqb index_choice_beq (snd a) (snd b))%bool.

(* ---------- what the harness prints ---------- *)

Definition show_ctag (c : collection_tag) : string :=
  match c with LikeList => "LikeList" | LikeBag => "LikeBag" | LikeSet => "LikeSet" end.

Fixpoint show_attrs (l : list string) : string :=
  match l with
  | [] => ""
  | [a] => a
  | a :: l' => a ++ "," ++ show_attrs l'
  end.

Definition show_choice (c : index_choice) : string :=
  match c with
  | SumAgg a => "SumAgg " ++ a
  | MinAgg a => "MinAgg " ++ a
  | SetAgg a => "SetAgg " ++ a
  | DictIdx a => "DictIdx " ++ a
  | RangedDictIdx a => "RangedDictIdx " ++ a
  | UniqueDictIdx a => "UniqueDictIdx " ++ a
  | TrigramIdx a k => "TrigramIdx " ++ a ++ "/" ++ k
  | KeyedDictIdx a k => "KeyedDictIdx " ++ a ++ "/" ++ k
  | TableRep ct => "TableRep " ++ show_ctag ct
  | CountAgg => "CountAgg"
  | CompositeDictIdx attrs => "CompositeDictIdx [" ++ show_attrs attrs ++ "]"
  | KeyedCompositeIdx attrs k =>
      "KeyedCompositeIdx [" ++ show_attrs attrs ++ "]/" ++ k
  | ListDictIdx a => "ListDictIdx " ++ a
  end.

Definition show_basic (b : basic_transf) : string :=
  match b with
  | SwapIfNil => "SwapIfNil" | MergeIf => "MergeIf" | SplitIf => "SplitIf"
  | SwapFlatmapIf => "SwapFlatmapIf" | IfNilIntoFlatmap => "IfNilIntoFlatmap"
  | SwapConjuncts => "SwapConjuncts" | AnnotateCollection => "AnnotateCollection"
  | PushdownCollection => "PushdownCollection" | FlatmapAssoc => "FlatmapAssoc"
  | FlatmapSingleton => "FlatmapSingleton" | FlatmapIdentity => "FlatmapIdentity"
  | FlatmapIf => "FlatmapIf" | SwapBagFlatmaps => "SwapBagFlatmaps"
  | FilterEmptyToSetMem => "FilterEmptyToSetMem" | FlagFilterToEq => "FlagFilterToEq"
  | SplitFilterProj => "SplitFilterProj" | PromoteGuard a => "PromoteGuard " ++ a
  end.

Fixpoint show_choices (l : list index_choice) : string :=
  match l with
  | [] => "(none)"
  | [c] => show_choice c
  | c :: l' => show_choice c ++ " + " ++ show_choices l'
  end.

(* only the optional rewrites are enumerated, so only they are reported *)
Fixpoint show_basics (l : list basic_transf) : string :=
  match l with
  | [] => ""
  | b :: l' =>
      match b with
      | PushdownCollection | AnnotateCollection | IfNilIntoFlatmap => show_basics l'
      | _ => "+" ++ show_basic b ++ show_basics l'
      end
  end.

Definition describe (fc : list basic_transf * list index_choice) : string :=
  show_choices (snd fc) ++ " " ++ show_basics (fst fc).

(* ---------- what crosses to the harness ----------

   NOT the configurations' terms.  There are hundreds of them per subject
   and each is the size of a program, so normalising them here would cost
   the Rocq build minutes and the extracted module megabytes.  What crosses
   instead is each subject's DATA and the two FUNCTIONS, so the harness
   generates and optimizes the configurations itself, by the same verified
   pipeline -- eval/ExtractAll.v already does this for `synth`, which is why
   the interface below takes environments as association lists: the map
   representation stays on this side of the boundary. *)

Record esubj := mk_esubj {
    es_name : string;
    es_ce : cenv;
    es_tbl : string;
    es_Gstore : list (string * type);
    es_Genv : list (string * type);
    es_prog : command }.

(* Normalised, for the reason eval/Extract.v normalises its terms: the
   subject rows reach here through a module alias, and monolithic
   extraction cannot follow one.  It is cheap -- 23 SOURCE programs, which
   the extracted module already carries, and not one optimized term. *)
Definition esubjects : list esubj :=
  Eval vm_compute in
  map (fun s => mk_esubj (s_name s) (s_ce s) (s_tbl s)
                  (map.tuples (s_Gstore s)) (map.tuples (s_Genv s)) (s_sel s))
    subjects.

Definition configs_al (e : esubj) : list (list basic_transf * list index_choice) :=
  let ce := es_ce e in let tbl := es_tbl e in let c := es_prog e in
  flat_map (fun fs =>
     let c' := compose_basic_transfs (map mk_basic_transf fs) c in
     map (fun cs => (fs, cs))
       (arrangements cap (choice_pool ce tbl (demands_of tbl c'))))
    (basics_variants (demands_of tbl c)).

Definition run_al (e : esubj) (fc : list basic_transf * list index_choice)
  : command :=
  let '(fs, cs) := fc in
  let Gstore : ctenv := map.of_list (es_Gstore e) in
  let Genv : ctenv := map.of_list (es_Genv e) in
  match es_ce e with
  | [] => apply_optimize_anno (AC fs [cs] (es_prog e)) Gstore Genv
  | _ => apply_optimize_anno_constrained
           (CAC (es_ce e) O fs cs [] (es_prog e)) Gstore Genv
  end.

Definition sel_config_al (e : esubj) : list basic_transf * list index_choice :=
  select (es_ce e) (es_tbl e) (es_prog e).

Definition is_sel_al (e : esubj) (fc : list basic_transf * list index_choice)
  : bool := cfg_beq fc (sel_config_al e).

(* ---------- what the generation is pinned to ----------

   The enumeration is only as good as two facts about it, and neither is
   argued: the function the HARNESS calls must be the pipeline the subject
   files use, and the selector's own configuration must be among those
   enumerated.  Without the first the measurement is of something else;
   without the second there is nothing to rank the selector against. *)

(* THE HEADLINE PIN.  run_al -- the function the harness calls, through the
   association-list interface, on the configuration the selector picks --
   reproduces every subject's own optimized term, the one eval/Extract.v
   hands the measurement and each subject file proves sound. *)
Lemma runner_reproduces_every_subject :
  map (fun e => run_al e (sel_config_al e)) esubjects = map s_opt subjects.
Proof. vm_compute; reflexivity. Qed.

(* and the harness's view of the configurations is the one above *)
Lemma configs_al_agrees : map configs_al esubjects = map (configs cap) subjects.
Proof. vm_compute; reflexivity. Qed.

(* THE SECOND PIN.  Every subject's selector configuration is enumerated,
   so "no enumerated configuration is cheaper" is a statement about a set
   that contains the selector's pick. *)
Lemma selector_config_is_enumerated :
  forallb (fun e => existsb (is_sel_al e) (configs_al e)) esubjects = true.
Proof. vm_compute; reflexivity. Qed.

(* the size of the search, so the claim carries its own scale *)
Lemma how_many_configurations :
  fold_right Nat.add O (map (fun e => length (configs_al e)) esubjects) = 864.
Proof. vm_compute; reflexivity. Qed.

Lemma how_many_subjects_enumerated : length esubjects = 23.
Proof. reflexivity. Qed.
