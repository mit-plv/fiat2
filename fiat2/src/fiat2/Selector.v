Require Import fiat2.Language fiat2.Utils fiat2.Surface fiat2.FlatmapForms
  fiat2.OptimizeAnno.
From Stdlib Require Import List String ZArith.
Import ListNotations.

(* ============================================================
   A deterministic heuristic selector.

   Every example in this development names its own heuristics: a list of
   basic rewrites and a list of index choices, written by hand beside the
   program.  That is fine for a soundness claim -- the optimizer is sound
   for ANY choice list -- but it is not fine for a performance claim, where
   "with appropriate heuristics" has to mean something a program can compute
   rather than something a person chose after looking at the answer.

   This file computes them.  It is UNTRUSTED: nothing below is proved, and
   nothing below needs to be, because a wrong choice costs an optimization
   and never soundness (every index_choice is sound on every table, and
   every basic rewrite is semantics-preserving).  What it owes instead is
   that it does not look at the examples, and that claim is checkable: this
   file mentions no table name, no attribute name and no example.  The
   examples appear only in eval/SelectorTests.v, which pins what the
   selector picks against what each example asks for by hand.

   Three phases, in order:

     1. BASICS.  Scan the source program for the shapes that decide a basic
        rewrite -- an emptiness test, a conjunctive filter, a filter on a
        boolean attribute -- and emit the list.
     2. DEMANDS.  Run the basics, then scan the result for the shapes the
        index rules match.  The basics have to run first: the collection
        push-down is what turns a list filter into the bag or set filter
        every index rule is stated at, and FilterEmptyToSetMem is what turns
        an emptiness test into the set-of-attribute read SetAgg answers.  A
        demand read off the source would be read off the wrong program.
     3. CHOICES.  Map each demand to the index that answers it, prune the
        ones another choice subsumes, and order the result by the ordering
        spec the five rule-ordering hazards impose.

   The demands are read off the program's SHAPES, not off its row type: an
   index is asked for where the program contains a read or a write that
   index makes cheaper, and nowhere else.  Asking for every index the row
   type would admit is also sound, and strictly worse -- an index with no
   reader still has to be maintained by every write.  A WRITE counts: the
   keyed pair in HA_AreaRegistry and the dictionary in Ex_SumDelete are
   both asked for by a delete and read by nothing, and declining them
   because no query probes them would be declining the point.

   SCOPE.  One table at a time, and join-free: a program with several
   tables is selected by one call per table, and a read of two tables
   nested inside each other is not attempted.  A join needs its inner read
   brought into the shape an index rule matches, by a sequence of flatmap
   shuffles that differs per program, and choosing that sequence is a
   different problem from choosing an index.  Every evaluation subject is
   join-free.
   ============================================================ *)

(* ---------- what a program can ask an index for ---------- *)

Variant demand :=
  (* A read or a write some index answers.  Each one names the rule it is
     evidence for; the rule's pattern is reproduced in the matcher below. *)
  | DEq (attr : string)      (* eq_filter_to_lookup / unique_lookup *)
  | DRange (attr : string)   (* range_filter_to_dict_range, and the two
                                range-shaped write rules *)
  | DSubstr (attr : string)  (* trigram_lookup_guarded *)
  | DDelKey (key : string)   (* a write that keeps the rows an equality
                                does NOT match: filter_neq_to_delete,
                                filter_neq_to_unique_delete,
                                filter_neq_to_keyed_delete,
                                filter_neq_to_min_guard *)
  | DSetOf (attr : string)   (* set_to_lookup *)
  | DSum (attr : string)     (* sum_to_agg_lookup *)
  | DMin (attr : string)     (* min_to_agg_lookup *)
  | DCount                   (* count_to_agg_lookup *)
  (* Shapes that decide a BASIC rewrite rather than an index.  They are
     collected by the same traversal and read by a different phase. *)
  | DEmptyEqFilter           (* FilterEmptyToSetMem applies *)
  | DConjSplit               (* SplitIf would expose an indexable conjunct
                                of a filter no rule matches as it stands *)
  | DFlag (attr : string).   (* FlagFilterToEq applies *)

Scheme Boolean Equality for collection_tag. (* creates collection_tag_beq *)
Scheme Boolean Equality for demand.         (* creates demand_beq *)

Definition str_mem (a : string) (l : list string) : bool :=
  existsb (String.eqb a) l.

Definition demand_mem (d : demand) (l : list demand) : bool :=
  existsb (demand_beq d) l.

(* first occurrence wins, so the order of the output follows the order of
   the program text *)
Fixpoint dedup_acc (seen : list demand) (l : list demand) : list demand :=
  match l with
  | [] => rev seen
  | d :: l' =>
      if demand_mem d seen then dedup_acc seen l' else dedup_acc (d :: seen) l'
  end.
Definition dedup_demands (l : list demand) : list demand := dedup_acc [] l.

Definition opt_list {A} (o : option A) : list A :=
  match o with Some a => [a] | None => [] end.

Definition omap {A B} (f : A -> option B) (l : list A) : list B :=
  flat_map (fun a => opt_list (f a)) l.

(* ---------- phase 2a: the shapes, as the rules write them ---------- *)

(* range_bounds (DictIndexImpl.v) decides whether a predicate is a range on
   the ONE attribute the index is already built on.  Here the attribute is
   what we are looking for, so the same three shapes are matched and the
   attribute read out of them.  A two-sided range is a conjunction of the
   two one-sided ones and must be tried first. *)
Definition range_attr (x : string) (p : expr) : option string :=
  match p with
  (* !(row.attr < lo) && row.attr < hi *)
  | EBinop OAnd (EUnop ONot (EBinop OLess (EAccess (EVar x1) a1) _))
      (EBinop OLess (EAccess (EVar x2) a2) _) =>
      if (String.eqb x x1 && String.eqb x x2 && String.eqb a1 a2)%bool
      then Some a1 else None
  (* !(row.attr < lo) *)
  | EUnop ONot (EBinop OLess (EAccess (EVar x1) a1) _) =>
      if String.eqb x x1 then Some a1 else None
  (* row.attr < hi *)
  | EBinop OLess (EAccess (EVar x1) a1) _ =>
      if String.eqb x x1 then Some a1 else None
  | _ => None
  end.

(* Is this predicate one that an index rule matches AS IT STANDS, with no
   splitting?  Three shapes are: a range on a row attribute (one- or
   two-sided -- range_bounds matches the two-sided pair as a whole), an
   equality against something the row does not determine, and a substring
   test.  This is the selector's model of what the read rules can see, and
   both the demand below and the SplitIf decision are phrased in terms of
   it rather than in terms of any particular program. *)
Definition indexable (x : string) (p : expr) : option demand :=
  match range_attr x p with
  | Some a => Some (DRange a)
  | None =>
      match p with
      | EBinop OEq (EAccess (EVar x1) a) k =>
          if (String.eqb x x1 && negb (free_immut_in x k))%bool
          then Some (DEq a) else None
      | EBinop OStrContains (EAccess (EVar x1) a) _ =>
          if String.eqb x x1 then Some (DSubstr a) else None
      | _ => None
      end
  end.

(* The predicate of a READ, where x is the row the filter binds.  A
   conjunction nothing matches whole is analysed by its FIRST conjunct,
   which is the one SplitIf would peel off and hand to an index; the rest
   stays a filter.  That is why a composite key is a measured gap and not a
   silent one -- only half of it is ever indexed. *)
Fixpoint pred_demand (x : string) (p : expr) : option demand :=
  match indexable x p with
  | Some d => Some d
  | None =>
      match p with
      | EBinop OAnd p1 _ => pred_demand x p1
      | _ => None
      end
  end.

(* The predicate of a WRITE that keeps some rows and drops the rest.  Three
   shapes are maintained incrementally: keep a range, drop a range, and drop
   the rows a declared key names. *)
Definition write_pred_demand (x : string) (p : expr) : option demand :=
  match range_attr x p with
  | Some a => Some (DRange a)
  | None =>
      match p with
      | EUnop ONot q =>
          match range_attr x q with
          | Some a => Some (DRange a)
          | None =>
              match q with
              | EBinop OEq (EAccess (EVar x1) k) kexp =>
                  if (String.eqb x x1 && negb (free_immut_in x kexp))%bool
                  then Some (DDelKey k) else None
              | _ => None
              end
          end
      | _ => None
      end
  end.

(* Evidence that SplitIf would pay on this filter.  Splitting peels the
   first conjunct into a position an index rule can match, so it pays
   exactly when the predicate as a whole is matched by NOTHING -- it would
   otherwise be a full scan -- and the conjunct that gets peeled IS
   matched.

   The second half of that is what keeps a bare range pair out.  A
   two-sided range is itself a conjunction, and range_bounds already
   matches it whole, so it is served without splitting and splitting it
   can only cost it one of its two bounds.  The condition declines it for
   the general reason -- there is nothing to expose -- rather than by a
   special case. *)
Definition conj_evidence (x : string) (p : expr) : list demand :=
  match p with
  | EBinop OAnd p1 _ =>
      match indexable x p, indexable x p1 with
      | None, Some _ => [DConjSplit]
      | _, _ => []
      end
  | _ => []
  end.

(* evidence about FlagFilterToEq: a filter on a boolean attribute, which is
   an equality against the flag written without the equality (FlagFilter) *)
Definition flag_evidence (x : string) (p : expr) : list demand :=
  match p with
  | EAccess (EVar x1) a => if String.eqb x x1 then [DFlag a] else []
  | EUnop ONot (EAccess (EVar x1) a) => if String.eqb x x1 then [DFlag a] else []
  | _ => []
  end.

(* ---------- phase 2b: one node of the program ---------- *)

Definition is_read (tbl : string) (e : expr) : bool :=
  match e with ELoc t => String.eqb tbl t | _ => false end.

(* What the node e asks for, if anything.  Each branch names the rule whose
   pattern it reproduces, with the table read written as the program writes
   it before any index is installed: ELoc tbl, where the rule -- which runs
   after -- sees EAccess (ELoc tbl) id_tag.

   The index rules are stated at BAG and SET level, so a read the collection
   phase left at LIST level demands no index; it still contributes its
   SplitIf evidence, which the basics phase reads off the source. *)
Definition node_demands (tbl : string) (e : expr) : list demand :=
  match e with
  (* a filter over a bag read: eq_filter_to_lookup, unique_lookup,
     range_filter_to_dict_range *)
  | flatmap_filter_bag (EBagOf (ELoc t)) x p y _ _ =>
      if (String.eqb tbl t && String.eqb x y)%bool
      then opt_list (pred_demand x p) ++ conj_evidence x p ++ flag_evidence x p
      else []
  (* a filter over a set read: trigram_lookup_guarded *)
  | flatmap_filter_set (ESetOf (ELoc t)) x p y _ _ =>
      if (String.eqb tbl t && String.eqb x y)%bool
      then opt_list (pred_demand x p) ++ conj_evidence x p ++ flag_evidence x p
      else []
  (* a filter left at list level: basics evidence only *)
  | flatmap_filter_list (ELoc t) x p y _ _ =>
      if (String.eqb tbl t && String.eqb x y)%bool
      then conj_evidence x p ++ flag_evidence x p else []
  (* the set of an attribute's values: set_to_lookup *)
  | flatmap_proj_set (ESetOf (ELoc t)) x (EAccess (EVar x1) a) _ =>
      if (String.eqb tbl t && String.eqb x x1)%bool then [DSetOf a] else []
  (* sum_to_agg_lookup *)
  | EACFold AGSum (flatmap_proj_bag (EBagOf (ELoc t)) x (EAccess (EVar x1) a) _) =>
      if (String.eqb tbl t && String.eqb x x1)%bool then [DSum a] else []
  (* min_to_agg_lookup *)
  | EACIFold AGMin (flatmap_proj_set (ESetOf (ELoc t)) x (EAccess (EVar x1) a) _) =>
      if (String.eqb tbl t && String.eqb x x1)%bool then [DMin a] else []
  (* count_to_agg_lookup: the whole table, counted *)
  | EACFold AGCount (EBagOf (ELoc t)) =>
      if String.eqb tbl t then [DCount] else []
  (* the emptiness test of an equality filter, which FilterEmptyToSetMem
     turns into a membership test in the set of the keys (ExistsTransf) *)
  | EBinop OEq
      (flatmap_filter_bag (EBagOf (ELoc t)) x (EBinop OEq (EAccess (EVar x1) _) k) y _ _)
      (EAtom (AEmptyBag _)) =>
      if (String.eqb tbl t && String.eqb x x1 && String.eqb x y
          && negb (free_immut_in x k))%bool
      then [DEmptyEqFilter] else []
  | _ => []
  end.

(* The node matchers above cover reads.  A write is recognised at the
   assignment, because the same filter shape in a read position asks for a
   lookup and in a write position asks for incremental maintenance.  Writes
   stay at LIST level: filter_neq_to_keyed_delete and the two range-write
   rules are all stated there. *)
Definition write_demands (tbl : string) (e : expr) : list demand :=
  match e with
  | flatmap_filter_list (ELoc t) x p y _ _ =>
      if (String.eqb tbl t && String.eqb x y)%bool
      then opt_list (write_pred_demand x p) else []
  | flatmap_filter_bag (EBagOf (ELoc t)) x p y _ _ =>
      if (String.eqb tbl t && String.eqb x y)%bool
      then opt_list (write_pred_demand x p) else []
  | flatmap_filter_set (ESetOf (ELoc t)) x p y _ _ =>
      if (String.eqb tbl t && String.eqb x y)%bool
      then opt_list (write_pred_demand x p) else []
  | _ => []
  end.

(* ---------- phase 2c: the traversal ---------- *)

Fixpoint collect_expr (tbl : string) (e : expr) : list demand :=
  node_demands tbl e ++
    match e with
    | EVar _ | ELoc _ | EAtom _ => []
    | EUnop _ e1 => collect_expr tbl e1
    | EBinop _ e1 e2 => collect_expr tbl e1 ++ collect_expr tbl e2
    | ETernop _ e1 e2 e3 =>
        collect_expr tbl e1 ++ collect_expr tbl e2 ++ collect_expr tbl e3
    | EIf e1 e2 e3 =>
        collect_expr tbl e1 ++ collect_expr tbl e2 ++ collect_expr tbl e3
    | ELet e1 _ e2 => collect_expr tbl e1 ++ collect_expr tbl e2
    | EFlatmap _ e1 _ e2 => collect_expr tbl e1 ++ collect_expr tbl e2
    | EFold e1 e2 _ _ e3 =>
        collect_expr tbl e1 ++ collect_expr tbl e2 ++ collect_expr tbl e3
    | EACFold _ e1 => collect_expr tbl e1
    (* The argument of a cached minimum IS the set-of-attribute read, and it
       is the minimum's input rather than a second reader of that set.
       Descending would ask for a set index the program never reads. *)
    | EACIFold AGMin (flatmap_proj_set (ESetOf (ELoc _)) _ (EAccess (EVar _) _) _) => []
    | EACIFold _ e1 => collect_expr tbl e1
    | ERecord l =>
        (fix go (l : list (string * expr)) : list demand :=
           match l with
           | [] => []
           | p :: l' => collect_expr tbl (snd p) ++ go l'
           end) l
    | EAccess e1 _ => collect_expr tbl e1
    | EOptMatch e1 e2 _ e3 =>
        collect_expr tbl e1 ++ collect_expr tbl e2 ++ collect_expr tbl e3
    | ESort _ e1 => collect_expr tbl e1
    | EBagOf e1 => collect_expr tbl e1
    | ESetOf e1 => collect_expr tbl e1
    end.

Fixpoint collect_command (tbl : string) (c : command) : list demand :=
  match c with
  | CSkip => []
  | CSeq c1 c2 => collect_command tbl c1 ++ collect_command tbl c2
  | CLet e _ c1 => collect_expr tbl e ++ collect_command tbl c1
  | CLetMut e _ c1 => collect_expr tbl e ++ collect_command tbl c1
  | CAssign x e =>
      (if String.eqb x tbl then write_demands tbl e else []) ++ collect_expr tbl e
  | CIf e c1 c2 =>
      collect_expr tbl e ++ collect_command tbl c1 ++ collect_command tbl c2
  | CForeach e _ c1 => collect_expr tbl e ++ collect_command tbl c1
  end.

Definition demands_of (tbl : string) (c : command) : list demand :=
  dedup_demands (collect_command tbl c).

(* ---------- phase 1: the basic rewrites ---------- *)

(* Three always run, and three are decisions.  The three that always run
   are the collection phase -- annotate, then push down, which is what
   every index rule's pattern is written against -- and IfNilIntoFlatmap,
   which keeps a filter in the one shape those rules match.

   FilterEmptyToSetMem goes FIRST in the list and therefore runs LAST
   (compose_basic_transfs is a fold_right), because it has to see the
   bag-level filter the push-down leaves behind.

   FilterEmptyToSetMem is declined on a table with a DECLARED key, and that
   is not a conservatism -- it is the third rule-ordering hazard.  The
   uniqueness check the elaboration inserts for an insert is an emptiness
   test of an equality filter on the key, i.e. exactly this rewrite's
   pattern, and rewriting it to a set membership test leaves a shape
   unique_lookup no longer matches, so the guard stops being a probe.  A
   table with a declared key has that guard; a table without one cannot.

   SplitIf goes LAST and therefore runs FIRST, and is the one real decision
   here.  It is emitted when some conjunctive filter over the table is
   matched by NO rule as it stands while the conjunct the splitter peels IS
   matched -- that is, when splitting turns a full scan into a probe with a
   residual filter, and only then.

   There is no veto, and the case a veto would have covered is handled by
   the same condition.  A two-sided range is itself a conjunction, and
   range_bounds matches it whole, so it is already served; splitting it
   would cost it one of its two bounds and expose nothing that was not
   exposed before, so the condition does not fire on it.

   What the condition cannot weigh is a program that has both -- a
   conjunction worth splitting and, elsewhere, a bare range pair that the
   same global rewrite will split anyway and so will cost a bound.  SplitIf
   is a whole-program rewrite, so the two cannot be separated here.  The
   selector takes the split, on the ground that the gain is a read that
   stops being a scan while the loss is a read that stays a range read and
   merely widens; which is the better trade in general is a comparison, and
   comparisons are what this file is built to avoid.  The one subject where
   both occur pins both configurations side by side.

   A related limitation, stated because it is easy to miss: the selector
   looks at the FIRST conjunct, since that is the one split_if_head peels.
   An indexable conjunct in any other position is invisible to it.  The
   development has swap_conjuncts_head, but it is unconditional -- it
   reverses every conjunction it meets -- so it cannot be used to bring one
   forward without reordering the others.  A guarded swap does not exist.

   FlagFilterToEq goes last of all and so runs first: it normalises a filter
   on a boolean attribute into the equality it is, which is the shape the
   index rules read.  Nothing orders it against SplitIf -- one rewrites a
   predicate's leaf and the other its conjunction -- so it is placed after
   by convention. *)
Definition basics_of (keys : list string) (ds : list demand) : list basic_transf :=
  (if (demand_mem DEmptyEqFilter ds
       && match keys with [] => true | _ :: _ => false end)%bool
   then [FilterEmptyToSetMem] else [])
  ++ [PushdownCollection; AnnotateCollection; IfNilIntoFlatmap]
  ++ (if demand_mem DConjSplit ds then [SplitIf] else [])
  ++ (if existsb (fun d => match d with DFlag _ => true | _ => false end) ds
      then [FlagFilterToEq] else []).

(* ---------- phase 3: the index choices ---------- *)

Definition unique_keys (ce : cenv) (tbl : string) : list string :=
  match find (fun p => String.eqb tbl (fst p)) ce with
  | Some (_, (_, ds)) =>
      omap (fun d => match d with DUnique a => Some a | _ => None end) ds
  | None => []
  end.

(* One dictionary per dictionary-shaped demand.  An equality filter on a
   DECLARED key is answered by the single-row index, which is what makes a
   lookup return a row rather than a bucket; on any other attribute it is
   the bucketed one.  A substring filter needs a key-to-row dictionary
   beside the postings, so it is declined where nothing is declared. *)
Definition dict_of_demand (keys : list string) (ds : list demand) (d : demand)
  : option index_choice :=
  match d with
  | DEq a => Some (if str_mem a keys then UniqueDictIdx a else DictIdx a)
  | DRange a => Some (RangedDictIdx a)
  | DSubstr a => match keys with k :: _ => Some (TrigramIdx a k) | [] => None end
  (* A delete that filters on an attribute is maintained in ONE bucket by a
     structure bucketed on that attribute -- filter_neq_to_delete for the
     plain dictionary, filter_neq_to_unique_delete for the declared one --
     where without it the correction term goes back to the table.  The one
     exception is a minimum cached on the same attribute: its guard rule
     reads the SET of the attribute's values to find the new minimum, so a
     dictionary there would be a second structure answering nothing. *)
  | DDelKey a =>
      if demand_mem (DMin a) ds then None
      else if str_mem a keys then Some (UniqueDictIdx a) else Some (DictIdx a)
  | _ => None
  end.

Definition is_dict_on (attr : string) (c : index_choice) : bool :=
  match c with DictIdx a => String.eqb attr a | _ => false end.

Definition dict_attr (c : index_choice) : option string :=
  match c with DictIdx a => Some a | _ => None end.

(* A delete that names a declared key, beside a dictionary bucketed on some
   OTHER attribute, is the keyed pair: the pair probes the key member for
   the row that is leaving and takes just that row out of the one bucket its
   attribute names, where the standalone dictionary would rebuild.  The pair
   subsumes both of the choices it replaces -- keyed_dict_subsumes_dict and
   keyed_dict_subsumes_unique_dict -- so both are dropped.

   At most one pair is formed, on the first such key and the first such
   dictionary.  A table with a keyed delete and two bucketed dictionaries
   would want two pairs sharing one key member; that is not expressible as a
   choice list today, and the second dictionary keeps rebuilding. *)
Definition pair_keyed_delete (keys : list string) (ds : list demand)
  (cs : list index_choice) : list index_choice :=
  match omap (fun d => match d with
                       | DDelKey k => if str_mem k keys then Some k else None
                       | _ => None end) ds with
  | [] => cs
  | k :: _ =>
      match omap (fun c => match dict_attr c with
                           | Some a => if negb (String.eqb a k) then Some a else None
                           | None => None end) cs with
      | [] => cs
      | a :: _ =>
          omap (fun c =>
                  if is_dict_on a c then Some (KeyedDictIdx a k)
                  else match c with
                       | UniqueDictIdx k' => if String.eqb k k' then None else Some c
                       | _ => Some c
                       end) cs
      end
  end.

(* A trigram index brings a key-to-row dictionary as its second member, and
   that member carries every rule the standalone one would
   (trigram_subsumes_unique_dict), so asking for both would build two copies
   of the same dictionary. *)
Definition drop_subsumed_by_trigram (cs : list index_choice) : list index_choice :=
  let keyed := omap (fun c => match c with
                              | TrigramIdx _ k => Some k
                              | _ => None end) cs in
  filter (fun c => match c with
                   | UniqueDictIdx k => negb (str_mem k keyed)
                   | _ => true end) cs.

Scheme Boolean Equality for index_choice. (* creates index_choice_beq *)

Fixpoint dedup_choices_acc (seen l : list index_choice) : list index_choice :=
  match l with
  | [] => rev seen
  | c :: l' =>
      if existsb (index_choice_beq c) seen
      then dedup_choices_acc seen l' else dedup_choices_acc (c :: seen) l'
  end.
Definition dedup_choices (l : list index_choice) : list index_choice :=
  dedup_choices_acc [] l.

(* The output order IS the ordering spec the rule-ordering hazards impose.
   The transfs of the choices are concatenated in list order and the LAST to
   be listed is the FIRST to run, so this list reads backwards from the
   order the rules fire in:

     - dictionaries before aggregates, so an aggregate's rules run first.
       An aggregate listed before its dictionary loses: the dictionary's
       maintenance rule reaches the write first and the aggregate's
       correction is left scanning (measured in eval/Kafka_NamedCache.v).
     - SetAgg before MinAgg, so MinAgg's rules run first; both read the set
       of an attribute's values and MinAgg's pattern is the narrower one.
     - CountAgg last, so its rules run first.

   Those two and the dictionary boundary are the constraints; SumAgg's place
   between them is free, and the aggregates come out in the fixed kind order
   SetAgg, SumAgg, MinAgg, CountAgg.

   TableRep, which has to be listed first of all, is not emitted here; see
   the note at the end of this file. *)
Definition choices_of (ce : cenv) (tbl : string) (ds : list demand)
  : list index_choice :=
  let keys := unique_keys ce tbl in
  let dicts := drop_subsumed_by_trigram
                 (pair_keyed_delete keys ds (omap (dict_of_demand keys ds) ds)) in
  let aggs :=
    omap (fun d => match d with
                   | DSetOf a => Some (SetAgg a)
                   | DDelKey a => if demand_mem (DMin a) ds then Some (SetAgg a) else None
                   | _ => None end) ds
    ++ omap (fun d => match d with DSum a => Some (SumAgg a) | _ => None end) ds
    ++ omap (fun d => match d with DMin a => Some (MinAgg a) | _ => None end) ds
    ++ (if demand_mem DCount ds then [CountAgg] else []) in
  dedup_choices (dicts ++ aggs).

(* ---------- the selector ---------- *)

(* The two scans run on two different programs, which is the whole reason
   they are separate: the basics are decided by the source, and the index
   demands by what the basics leave behind. *)
Definition select (ce : cenv) (tbl : string) (c : command)
  : list basic_transf * list index_choice :=
  let fs := basics_of (unique_keys ce tbl) (demands_of tbl c) in
  let c' := compose_basic_transfs (map mk_basic_transf fs) c in
  (fs, choices_of ce tbl (demands_of tbl c')).

Definition select_basics (ce : cenv) (tbl : string) (c : command) :=
  fst (select ce tbl c).
Definition select_choices (ce : cenv) (tbl : string) (c : command) :=
  snd (select ce tbl c).

(* Packaged as the annotation the constrained pipeline takes.  A program
   with one table is every eval subject; more than one table is a map over
   the tables, with one choice list each, and the depth each list is
   installed at is the depth of the letmut that binds it. *)
Definition select_anno (ce : cenv) (tbl : string) (depth : nat) (c : command)
  : canno_command :=
  let '(fs, cs) := select ce tbl c in
  CAC ce depth fs cs [] c.

(* ---------- what is deliberately not selected ---------- *)



(* TableRep.  Not emitted, and the reason is measured rather than assumed.

   It could not be demanded by a shape in any case: the read it serves is
   one the REWRITING leaves behind -- trigram_lookup_guarded_head rewrites
   e into EIf (pattern_has_trigram p) (probe) e, keeping its own input as
   the else branch -- so there is no second read in the program to map to a
   choice.  A feedback step closes that gap easily: run the pipeline, look
   for a surviving coercion of the table's list member, add TableRep at
   that level and run again, keeping it if the list is now erased.  That
   was built, and it does reach eval/Jenkins_UserSearch's second
   configuration.

   It was removed again, because "the list was erased" is not a proxy for
   "this paid".  TableRep IS a copy of the table, so it SUBSTITUTES the
   structure the remaining readers and writers walk rather than removing
   one.  Measured on eval/Jenkins_UserSearch, the one eval subject that
   carries a TableRep configuration, and the comparison is one-sided:

     the configuration WITHOUT it writes nothing to a list, because the
       declared key has already erased the list (delete_writes_no_list,
       insert_writes_no_list);
     the configuration WITH it still pays the source's own row-by-row
       filter on the delete, now over the rep member
       (rep_delete_filters_the_rep), and degrades the insert from a cons
       to a set insert (rep_insert_is_a_set_insert);
     and its rep member is read by no query at all
       (rep_suggest_also_uses_the_key_member, rep_find_is_still_a_probe).
       The scan rule runs after TableRep's, so where both could serve the
       fallback the declared key wins -- the right way round, since the key
       member is one the source already maintains and the rep member is a
       copy.

   So on the only subject where the two can be compared, TableRep is
   dominated.  Nothing here measures a surviving list with NO declared key,
   where the choice would be lateral rather than dominated: the same scan,
   one structure either way, and a cons degraded to a collection insert.

   Erasing the list is a real win where another index already answers
   every read and NOTHING replaces the list -- Kafka_Cluster,
   HA_AreaRegistry, Kafka_NamedCache, Keycloak with its count, and now
   Jenkins_UserSearch through its declared key.  TableRep erases by
   substitution, which is an expressiveness result (a table can BE its
   index) and not a performance one, so it is not selected.  The mechanism
   that would make it pay is nameable and does not exist: a rule that
   maintains a rep member AT ITS OWN LEVEL -- a set-level removal rather
   than a filter over the set -- would make the member cheaper than the
   list it replaces.  The feedback step is the way to ask for that, and the
   test it needs is a cost comparison rather than a boolean. *)

(* MinAgg.  Emitted when the program asks for it, but no eval subject does.
   The corpus witnesses for a minimum are per-key counters held in a
   dictionary -- the dictionary-of-aggregates shape, which is deferred. *)
