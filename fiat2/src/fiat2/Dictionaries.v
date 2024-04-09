Require Import fiat2.Language.
Require Import coqutil.Datatypes.Result.
Require Import String.

Open Scope string_scope.

Section Dictionary.
  (* Dictionaries may be altered at run time *)

  Context {s : string}.
  Context {kType vType : type}.

  Definition Assoc := TPair s kType vType.
  Definition Dict := TList Assoc.

  Definition getFromDict {H : can_eq kType = true} (d : expr Dict) (k : expr kType) : expr (TList vType) :=
    EFold d (EAtom (ANil _)) "p" "foo"
      (EIf (EBinop (OEq _ H) (EUnop (OFst _ _ _) (EVar Assoc "p")) k)
         (EBinop (OCons _) (EUnop (OSnd _ _ _) (EVar Assoc "p")) (EAtom (ANil _)))
         (EAtom (ANil _))  (* If k is not found, return an empty list *)
      ).

  Definition updateToDict {H : can_eq kType = true} (d : expr Dict) (k : expr kType) (v : expr vType) : expr Dict :=
    EBinop (OCons _) (EBinop (OPair _ _ _) k v)
      (EFold d (EAtom (ANil _)) "p" "acc"
         (EIf (EBinop (OEq _ H) (EUnop (OFst _ _ _) (EVar Assoc "p")) k)
            (EVar _ "acc")
            (EBinop (OCons _) (EVar _ "p") (EVar _ "acc"))
         ) (* Remove the entry with key k if one exists in d *)
      ).
End Dictionary.

(* We use "key" to refer to the key in a key-value pair of a dictionary and "index key" to refer to the attribute(s) that a database index is built on *)

Section DupIdxKeyIndex.
  (* Database index on an attribute that may have duplicate values *)
  Context (s : string).
  Context (kType vType : type).

  Definition DupIdxKeyIndex := @Dict s kType (TList vType).

  Definition  getFromDupIdxKeyIndex {H : can_eq kType = true} (d : expr DupIdxKeyIndex) (k : expr kType) : expr (TList vType) := EFlatmap (getFromDict (H := H) d k) "x" (EVar _ "x").

  Definition updateToDupIdxKeyIndex {H : can_eq kType = true} (d : expr DupIdxKeyIndex) (k : expr kType) (v : expr vType) : expr DupIdxKeyIndex :=
    let curValues := getFromDupIdxKeyIndex (H := H) d k in
    updateToDict (H := H) d k (EBinop (OCons _) v curValues).
End DupIdxKeyIndex.

Section UniqueIdxKeyIndex.
  (* Index on an attribute with unique values in a table *)
  Context (s : string).
  Context (kType vType : type).

  Definition UniqueIdxKeyIndex := @Dict s kType vType.

  Definition getFromUniqueIdxKeyIndex {H : can_eq kType = true} (d : expr UniqueIdxKeyIndex) (k : expr kType) : expr (TList vType) := getFromDict (H := H) d k.

  Definition updateToUniqueIdxKeyIndex {H : can_eq kType = true} (d : expr UniqueIdxKeyIndex) (k : expr kType) (v : expr vType) : expr UniqueIdxKeyIndex := updateToDict (H := H) d k v.
End UniqueIdxKeyIndex.

(* Identify the accessing of an attribute in the variable x
 and return which attribute it is *)
Fixpoint isNthAttr' {t} (x : string) (e : expr t) : option nat :=
  match e with
  | EVar _ x => Some O
  | EUnop (OSnd s t1 t2) e' => match isNthAttr' x e' with
                               | Some n => Some (S n)
                               | None => None
                               end
  | _ => None
  end.

Definition isNthAttr {t} (x : string) (e : expr t) : option nat :=
  match e with
  | EUnop (OFst _ _ _) e' => isNthAttr' x e'
  | _ => None
  end.

Definition record (ts : list type) : type :=
  fold_right (TPair "") TEmpty ts.

Compute record (TBool :: TInt :: TEmpty :: nil).

Definition pair_rhs (t : type) : type :=
  match t with
  | TPair _ _ t' => t'
  | _ => TEmpty
  end.

Definition unsafe_snd {t} : expr t -> expr (pair_rhs t) :=
  match t with
  | TPair _ _ _ => EUnop (OSnd _ _ _)
  | _ => fun _ => EAtom AEmpty
  end.

Fixpoint skip (ts : list type) (e : expr (record ts)) (n : nat) : expr (record (skipn n ts)) :=
  match n, ts return expr (record ts) -> expr (record (skipn n ts)) with
  | O, _ => fun e => e
  | S n', t :: ts' => fun e => skip ts' (unsafe_snd e) n'
  | S n', nil => fun _ => EAtom AEmpty
  end e.

Definition getNthAttr (ts : list type) (x : string) (n : nat) : expr (hd TEmpty (skipn n ts)) :=
  match skipn n ts as ts' return expr (record ts') -> expr (hd TEmpty ts') with
  | nil => fun _ => EAtom AEmpty
  | t :: ts'' => fun e => EUnop (OFst _ _ _) e
  end (skip ts (EVar (record ts) x) n).

Definition emap {t1 t2} (l : expr (TList t1)) (x : string) (e : expr t2) : expr (TList t2):=
  EFlatmap l x (EBinop (OCons _) e (EAtom (ANil _))).

(* Initialize a unique-key index of the table with the nth attribute as the key *)
Definition initUniqueKeyIdx (n : nat) (ts : list type) (row : string) {t} (table : expr (TList t)) : expr (UniqueIdxKeyIndex "" _ (record ts)):=
  emap table row (EBinop (OPair _ _ _) (getNthAttr ts row n) (EVar _ row)).

Definition isEqualityOfNthAttr {t} (table : string) (e : expr t) : option nat :=
  match e with
  | @EFlatmap tRec _ (ELoc (TList _) table') r
      (EIf (EBinop (OEq t1 H) e1 (EAtom _)) _ (EAtom (ANil _))) =>
      if table =? table' then isNthAttr r e1 else None
  | _ => None
  end.

Fixpoint allAttrOfTable' {t} (table : string) (e : expr t) : list nat :=
  match e with
  | EVar _ _ | ELoc _ _ | EAtom _ => nil
  | EUnop o e' => allAttrOfTable' table e'
  | EBinop o e1 e2 => allAttrOfTable' table e1 ++ allAttrOfTable' table e2
  | EFlatmap l1 y l2 => match isEqualityOfNthAttr table e with
                        | Some n => n :: nil
                        | None => allAttrOfTable' table l1 ++ allAttrOfTable' table l2
                        end
  | EFold l1 e2 v acc e3 => allAttrOfTable' table l1 ++ allAttrOfTable' table e2 ++
                              allAttrOfTable' table e3
  | EIf e1 e2 e3 => allAttrOfTable' table e1 ++ allAttrOfTable' table e2 ++ allAttrOfTable' table e3
  | ELet y e1 e2 => allAttrOfTable' table e1 ++ allAttrOfTable' table e2
  end.

Fixpoint allAttrOfTable (table : string) (c : command) : list nat :=
  match c with
  | CSkip => nil
  | CSeq c1 c2 => allAttrOfTable table c1 ++ allAttrOfTable table c2
  | CLet x e c => (* Assume x is not equal to table *)
      allAttrOfTable' table e ++ allAttrOfTable table c
  | CLetMut x e c => (* Assume x is not equal to table *)
      allAttrOfTable' table e ++ allAttrOfTable table c
  | CGets x e => allAttrOfTable' table e
  | CIf e c1 c2 => allAttrOfTable' table e ++ allAttrOfTable table c1 ++ allAttrOfTable table c2
  | CForeach x l c => allAttrOfTable' table l ++ allAttrOfTable table c
  end.

Definition allAttrOfTopTable (c : command) : list nat :=
  match c with
  | CLetMut table e c' => allAttrOfTable table c
  | _ => nil
  end.

(* Insert n into a sorted list l and maintain the increasing order *)
Fixpoint sortedInsert {A : Type} (f : A -> nat) (n : A) (l : list A) :=
  match l with
  | nil => n :: nil
  | m :: l' => if Nat.leb (f n) (f m) then n :: m :: l' else m :: sortedInsert f n l'
  end.

Require Import Coq.Sorting.Sorted.
Definition ascending {A} (f : A -> nat) (l : list A) :=
  StronglySorted (fun u v => Nat.le (f u) (f v)) l.

Lemma Forall_sortedInsert : forall A (R : A -> Prop) (n : A) l f, R n -> Forall R l -> Forall R (sortedInsert f n l).
Proof.
  induction l.
  - simpl. intuition.
  - intros f HR HForall; simpl. destruct (f n <=? f a)%nat; intuition.
    apply Forall_inv in HForall as H1. apply Forall_inv_tail in HForall as H2.
    apply Forall_cons; intuition.
Qed.

Lemma sortedInsert_ascending : forall A (f : A -> nat) (l : list A),
    ascending f l ->
    forall n, ascending f (sortedInsert f n l).
Proof.
  intros A f l H. induction H.
  - repeat constructor; intuition.
  - simpl. intro n. destruct (f n <=? f a)%nat eqn:E.
    + apply leb_complete in E. repeat constructor; intuition.
      apply Forall_impl with (fun v : A => Nat.le (f a) (f v)); intuition.
    + apply leb_complete_conv in E. constructor; try apply IHStronglySorted.
      apply Forall_sortedInsert; intuition.
Qed.

(* Insertion sort *)
Fixpoint sort {A : Type} (f : A -> nat) (l : list A) : list A :=
  match l with
  | nil => nil
  | n :: l' => sortedInsert f n (sort f l')
  end.

Corollary sort_ascending : forall A f (l : list A), ascending f (sort f l).
Proof.
  induction l.
  - constructor.
  - simpl. apply sortedInsert_ascending. assumption.
Qed.

(* Given a sorted list, return a list of (element, count) pairs *)
Fixpoint aggregate (l : list nat) : list (nat * nat) :=
  match l with
  | nil => nil
  | n :: l' => match aggregate l' with
               | nil => (n, 1) :: nil
               | (m, c) :: l' => if Nat.eqb m n then (m, S c) :: l' else (n, 1) :: (m, c) :: l'
               end
  end.

(* Sort, aggregate, then sort by count *)
Definition aggrAfterSort (l : list nat) :=
  sort snd (aggregate (sort id l)).

Compute aggrAfterSort (4 :: 2 :: 2 :: 6 :: 1 :: 6 :: nil).

Require Import fiat2.Queries.
Section ExampleForAttrOfTopTable.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Compute artist.
  Fixpoint listify (t : type) :=
    match t with
    | TPair _ t1 t2 => t1 :: listify t2
    | _ => nil
    end.
  Compute (listify artist).

  Definition getNthArtistAttr := getNthAttr (listify artist).
  Definition eq_pattern1 H : expr (TList artist) :=
    EFlatmap (ELoc (TList artist) "artists") "r"
      (EIf (EBinop (OEq _ H) (getNthArtistAttr "r" 0) (EAtom (AInt 1)))
         (EBinop (OCons _) (EVar _ "r") (EAtom (ANil _)))
         (EAtom (ANil artist))).
  Definition eq_pattern2 H : expr (TList TString) :=
    EFlatmap (ELoc (TList artist) "artists") "r"
      (EIf (EBinop (OEq _ H) (getNthArtistAttr "r" 1) (EAtom (AString "Accept")))
         (EBinop (OCons _) (EAtom (AString "Acpt")) (EAtom (ANil _)))
         (EAtom (ANil _))).
(* Why can't I replace H with eq_refl above??? *)
  Definition cmd_ex := CLetMut "artists" artists
                         (CLetMut "artists'" artists
                            (CSeq
                               (CLet "x" (eq_pattern2 eq_refl) CSkip)
                               (CIf (EAtom (ABool false))
                                  (CGets "artists" (eq_pattern1 eq_refl))
                                  (CGets "artists'" (eq_pattern1 eq_refl))
                         ))).
End ExampleForAttrOfTopTable.
