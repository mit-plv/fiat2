Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Datatypes.Result.
From Stdlib Require Import List String ZArith Sorted.

Import ListNotations.
Local Open Scope string_scope.

(* ODictMinKey: the least key of a ranged dictionary.

   Two things are pinned here, and the second is the point.

   1. It answers the minimum, and it does so independently of the order the
      dictionary was BUILT in -- which is what makes it a projection of the
      head rather than a fold.  dict_min_key_is_least is the general statement;
      these are its instances on a concrete dictionary.

   2. It does not typecheck at TDict Unranged.  That is the whole reason the
      rule pins Ranged: the minimum is perfectly DEFINABLE on either kind,
      because TyVDict makes every well-typed dictionary key-sorted whatever its
      kind, so refusing it at Unranged is a deliberate choice and not a
      consequence.  A hash table has no least key, and the type is where that
      is said.  Without the negative pin this file would not show that the kind
      is doing any work. *)

Section WithConcreteMaps.
  Instance ctenv : map.map string type := SortedListString.map _.
  Instance ctenv_ok : map.ok ctenv := SortedListString.ok _.
  Instance clocals : map.map string value := SortedListString.map _.
  Instance clocals_ok : map.ok clocals := SortedListString.ok _.

  (* Keys inserted in a scrambled order, so that "the head" is a claim about
     the dictionary's invariant and not about the writing order.

     The empty dictionaries carry their key/value annotation because
     AEmptyDict _ None is rejected by BOTH directions of the bidirectional
     checker -- only the declarative TyAEmptyDict' types it -- and these pins
     run the checker. *)
  Definition d_scrambled : expr :=
    ETernop OInsert
      (ETernop OInsert
         (ETernop OInsert
            (ETernop OInsert (EAtom (AEmptyDict Ranged (Some (TInt, TString))))
               (EAtom (AInt 40)) (EAtom (AString "d")))
            (EAtom (AInt 10)) (EAtom (AString "a")))
         (EAtom (AInt 30)) (EAtom (AString "c")))
      (EAtom (AInt 20)) (EAtom (AString "b")).

  (* ... and the same four entries written smallest-first *)
  Definition d_ascending : expr :=
    ETernop OInsert
      (ETernop OInsert
         (ETernop OInsert
            (ETernop OInsert (EAtom (AEmptyDict Ranged (Some (TInt, TString))))
               (EAtom (AInt 10)) (EAtom (AString "a")))
            (EAtom (AInt 20)) (EAtom (AString "b")))
         (EAtom (AInt 30)) (EAtom (AString "c")))
      (EAtom (AInt 40)) (EAtom (AString "d")).

  Definition min_of (d : expr) : expr := EUnop ODictMinKey d.

  Lemma min_key_is_the_least_and_build_order_free :
    interp_expr map.empty (map.empty : clocals) (min_of d_scrambled)
      = VOption (Some (VInt 10))
    /\ interp_expr map.empty (map.empty : clocals) (min_of d_ascending)
       = VOption (Some (VInt 10)).
  Proof. repeat apply conj; vm_compute; reflexivity. Qed.

  (* The empty dictionary answers None rather than failing, so a caller
     unwraps with EOptMatch and needs no emptiness guard of its own. *)
  Lemma min_key_of_empty_is_none :
    interp_expr map.empty (map.empty : clocals)
      (min_of (EAtom (AEmptyDict Ranged (Some (TInt, TString)))))
    = VOption None.
  Proof. vm_compute; reflexivity. Qed.

  (* It is a well-typed TOption of the KEY type. *)
  Lemma min_key_synthesizes_at_ranged :
    match synthesize_expr map.empty (map.empty : ctenv) (min_of d_scrambled) with
    | Success (t, _) => t = TOption TInt
    | _ => False
    end.
  Proof. vm_compute; reflexivity. Qed.

  (* THE NEGATIVE PIN.  The same term over an Unranged dictionary does not
     typecheck -- the operator is not merely unregistered at that kind, it is
     untypeable there. *)
  Definition d_unranged : expr :=
    ETernop OInsert (EAtom (AEmptyDict Unranged (Some (TInt, TString))))
      (EAtom (AInt 10)) (EAtom (AString "a")).

  Lemma min_key_does_not_typecheck_at_unranged :
    match synthesize_expr map.empty (map.empty : ctenv) (min_of d_unranged) with
    | Success _ => False
    | Failure _ => True
    end.
  Proof. vm_compute; exact I. Qed.

  (* And the dictionary itself is fine at Unranged -- it is the MINIMUM that
     the kind refuses, not the dictionary.  Without this the pin above would
     not distinguish "the operator is refused" from "the term is malformed". *)
  Lemma the_unranged_dictionary_itself_typechecks :
    match synthesize_expr map.empty (map.empty : ctenv) d_unranged with
    | Success (t, _) => t = TDict Unranged TInt TString
    | _ => False
    end.
  Proof. vm_compute; reflexivity. Qed.
End WithConcreteMaps.
