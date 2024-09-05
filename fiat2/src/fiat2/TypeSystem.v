Require Import fiat2.Language fiat2.Value.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
Import ResultMonadNotations.
Require Import String List Permutation Sorted.

(* Whether a is in l *)
Fixpoint inb {A : Type} (A_eqb : A -> A -> bool) (a : A) (l : list A) : bool :=
  match l with
  | nil => false
  | h :: l => if A_eqb h a then true else inb A_eqb a l
  end.

Lemma inb_false_iff : forall s l, inb eqb s l = false <-> ~ In s l.
Proof.
  induction l; simpl; intros.
  - intuition.
  - destruct (String.eqb a s) eqn:E; intuition.
    + rewrite String.eqb_eq in E; intuition.
    + rewrite String.eqb_neq in E; intuition.
Qed.

Lemma inb_true_iff : forall s l, inb eqb s l = true <-> In s l.
Proof.
  induction l; simpl; intros.
  - split; intuition.
  - destruct (String.eqb a s) eqn:E; intuition.
    + rewrite String.eqb_eq in E; intuition.
    + rewrite String.eqb_neq in E; intuition.
Qed.

(* Whether l is included in m *)
Definition inclb {A : Type} (A_eqb : A -> A -> bool) (l m : list A) : bool :=
  forallb (fun a => inb A_eqb a m) l.

Lemma inclb_correct : forall l l', inclb String.eqb l l' = true -> incl l l'.
Proof.
  induction l; simpl; intros.
  - apply incl_nil_l.
  - rewrite Bool.andb_true_iff in H. destruct H as [HL HR].
    apply IHl in HR. rewrite inb_true_iff in HL.
    unfold incl. intros. inversion H; subst; intuition.
Qed.

Lemma inclb_complete : forall l l', incl l l' -> inclb String.eqb l l' = true.
Proof.
  intros l l' H. unfold inclb. rewrite forallb_forall; intros.
  rewrite inb_true_iff. intuition.
Qed.

Fixpoint NoDup_comp {A : Type} (A_eqb : A -> A -> bool) (l : list A) : bool :=
  match l with
  | nil => true
  | x :: l => if inb A_eqb x l then false else NoDup_comp A_eqb l
  end.

Lemma NoDup_comp_true_iff : forall l, NoDup_comp String.eqb l = true <-> NoDup l.
Proof.
  induction l; simpl in *; intuition.
  - apply NoDup_nil.
  - destruct (inb eqb a l) eqn:E; try discriminate. constructor; auto.
    apply inb_false_iff; auto.
  - inversion H1; subst. apply inb_false_iff in H4; rewrite H4. auto.
Qed.

Fixpoint StronglySorted_comp {A : Type} (R : A -> A -> bool) (l : list A) : bool :=
  match l with
  | nil => true
  | a :: l => forallb (R a) l && StronglySorted_comp R l
  end.

Local Coercion is_true : bool >-> Sortclass.

Lemma StronglySorted_comp_true_iff : forall A (l : list (string * A)),
    StronglySorted_comp record_entry_leb l = true <-> StronglySorted record_entry_leb l.
Proof.
  induction l.
  - intuition. constructor.
  - simpl. split; intros.
    + apply Bool.andb_true_iff in H as [HL HR]. rewrite forallb_forall in HL. constructor.
      * apply IHl; auto.
      * apply Forall_forall; auto.
    + inversion H; subst. apply Bool.andb_true_iff. split.
      * rewrite Forall_forall in H3. rewrite forallb_forall. auto.
      * apply IHl; auto.
Qed.

Inductive type_wf : type -> Prop :=
| WFTWord : type_wf TWord
| WFTInt : type_wf TInt
| WFTBool : type_wf TBool
| WFTString : type_wf TString
| WFTUnit : type_wf TUnit
| WFTOption t : type_wf t ->
                type_wf (TOption t)
| WFTList t : type_wf t ->
              type_wf (TList t)
| WFTRecord l : NoDup (List.map fst l) ->
                StronglySorted record_entry_leb l ->
                Forall type_wf (List.map snd l) ->
                type_wf (TRecord l)
| WFTDict kt vt : type_wf kt ->
                  type_wf vt ->
                  type_wf (TDict kt vt).

Fixpoint type_wf_comp (t : type) : bool :=
  match t with
  | TWord | TInt | TBool | TString | TUnit => true
  | TOption t | TList t => type_wf_comp t
  | TRecord tl => NoDup_comp String.eqb (List.map fst tl) &&
                    StronglySorted_comp record_entry_leb tl &&
                    (fix forall_snd (tl : list (string * type)) :=
                       match tl with
                       | nil => true
                       | (_, t) :: tl => (type_wf_comp t && forall_snd tl)%bool
                       end) tl
  | TDict kt vt => type_wf_comp kt && type_wf_comp vt
  end.

Lemma type_wf_comp_sound : forall t, type_wf_comp t = true -> type_wf t.
Proof.
  intros t H; induction t using type_IH; simpl in *; constructor; auto;
    repeat rewrite Bool.andb_true_iff in *; intuition.
  - apply NoDup_comp_true_iff; auto.
  - apply StronglySorted_comp_true_iff; auto.
  - clear H H3. induction l; auto. destruct a; simpl in *.
    inversion H0; subst. constructor;
      try apply IHl; auto; rewrite Bool.andb_true_iff in *; intuition.
Qed.

(* Inductive typing relation *)
Inductive type_of_atom : atom -> type -> Prop :=
| TyAWord n : type_of_atom (AWord n) TWord
| TyAInt n : type_of_atom (AInt n) TInt
| TyABool b : type_of_atom (ABool b) TBool
| TyAString s : type_of_atom (AString s) TString
| TyANil' t : type_wf t ->
              type_of_atom (ANil None) (TList t)
| TyANil t : type_wf t ->
             type_of_atom (ANil (Some t)) (TList t)
| TyANone' t : type_wf t ->
               type_of_atom (ANone None) (TOption t)
| TyANone t : type_wf t ->
              type_of_atom (ANone (Some t)) (TOption t)
| TyAUnit : type_of_atom AUnit TUnit.

Inductive type_of_unop : unop -> type -> type -> Prop :=
| TyOWNeg : type_of_unop OWNeg TWord TWord
| TyONeg : type_of_unop ONeg TInt TInt
| TyONot : type_of_unop ONot TBool TBool
| TyOLength t : type_wf t -> type_of_unop OLength (TList t) TInt
| TyOLengthString : type_of_unop OLengthString TString TInt
| TyOIntToString : type_of_unop OIntToString TInt TString
| TyOSome t : type_wf t -> type_of_unop OSome t (TOption t).

Inductive type_of_binop : binop -> type -> type -> type -> Prop :=
| TyOWPlus : type_of_binop OWPlus TWord TWord TWord
| TyOPlus : type_of_binop OPlus TInt TInt TInt
| TyOWMinus : type_of_binop OWMinus TWord TWord TWord
| TyOMinus : type_of_binop OMinus TInt TInt TInt
| TyOWTimes : type_of_binop OWTimes TWord TWord TWord
| TyOTimes : type_of_binop OTimes TInt TInt TInt
| TyOWDivU : type_of_binop OWDivU TWord TWord TWord
| TyOWDivS : type_of_binop OWDivS TWord TWord TWord
| TyODiv : type_of_binop ODiv TInt TInt TInt
| TyOWModU : type_of_binop OWModU TWord TWord TWord
| TyOWModS : type_of_binop OWModS TWord TWord TWord
| TyOMod : type_of_binop OMod TInt TInt TInt
| TyOAnd : type_of_binop OAnd TBool TBool TBool
| TyOOr : type_of_binop OOr TBool TBool TBool
| TyOConcat t : type_wf t ->
                type_of_binop OConcat (TList t) (TList t) (TList t)
| TyOConcatString : type_of_binop OConcatString TString TString TString
| TyOWLessU : type_of_binop OWLessU TWord TWord TBool
| TyOWLessS : type_of_binop OWLessS TWord TWord TBool
| TyOLess : type_of_binop OLess TInt TInt TBool
| TyOEq t : type_wf t ->
            type_of_binop OEq t t TBool
| TyORepeat t : type_wf t ->
                type_of_binop ORepeat (TList t) TInt (TList t)
| TyOCons t : type_wf t ->
              type_of_binop OCons t (TList t) (TList t)
| TyORange : type_of_binop ORange TInt TInt (TList TInt)
| TyOWRange : type_of_binop OWRange TWord TWord (TList TWord).

Fixpoint access_record {A : Type} (l : list (string * A)) (s : string) : result A :=
  match l with
  | nil => error:("Attribute" s "not found in record" l)
  | (s0, a) :: l => if String.eqb s s0 then Success a else access_record l s
  end.

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.

  (* ??? Move to soundness *)
  Definition tenv_wf (G : tenv) := forall x t, map.get G x = Some t -> type_wf t.

  Inductive type_of (Gstore Genv : tenv) : expr -> type -> Prop :=
  | TyEVar x t : map.get Genv x = Some t -> type_of Gstore Genv (EVar x) t
  | TyELoc x t : map.get Gstore x = Some t -> type_of Gstore Genv (ELoc x) t
  | TyEAtom a t : type_of_atom a t -> type_of Gstore Genv (EAtom a) t
  | TyEUnop o e t1 t2 : type_of_unop o t1 t2 ->
                        type_of Gstore Genv e t1 ->
                        type_of Gstore Genv (EUnop o e) t2
  | TyEBinop o e1 e2 t1 t2 t3 : type_of_binop o t1 t2 t3 ->
                                type_of Gstore Genv e1 t1 ->
                                type_of Gstore Genv e2 t2 ->
                                type_of Gstore Genv (EBinop o e1 e2) t3
  | TyEIf e1 e2 e3 t : type_of Gstore Genv e1 TBool ->
                       type_of Gstore Genv e2 t ->
                       type_of Gstore Genv e3 t ->
                       type_of Gstore Genv (EIf e1 e2 e3) t
  | TyELet e1 t1 x e2 t2 : type_of Gstore Genv e1 t1 ->
                           type_of Gstore (map.put Genv x t1) e2 t2 ->
                           type_of Gstore Genv (ELet e1 x e2) t2
  | TyEFlatmap e1 t1 x e2 t2 : type_of Gstore Genv e1 (TList t1) ->
                               type_of Gstore (map.put Genv x t1) e2 (TList t2) ->
                               type_of Gstore Genv (EFlatmap e1 x e2) (TList t2)
  | TyEFold e1 t1 e2 t2 x y e3 : type_of Gstore Genv e1 (TList t1) ->
                                 type_of Gstore Genv e2 t2 ->
                                 type_of Gstore (map.put (map.put Genv x t1) y t2) e3 t2 ->
                                 type_of Gstore Genv (EFold e1 e2 x y e3) t2
  | TyERecord (l : list (string * expr)) (tl tl' : list (string * type)) :
    List.map fst l = List.map fst tl ->
    Forall2 (type_of Gstore Genv) (List.map snd l) (List.map snd tl) ->
    Permutation tl tl' ->
    NoDup (List.map fst tl) ->
    StronglySorted record_entry_leb tl' ->
    type_of Gstore Genv (ERecord l) (TRecord tl')
  | TyEAccess e tl x t : type_of Gstore Genv e (TRecord tl) ->
                         access_record tl x = Success t ->
                         type_of Gstore Genv (EAccess e x) t
  | TyEDict l kt vt : type_wf kt -> type_wf vt -> (* needed in case l = nil*)
                      Forall (fun p => type_of Gstore Genv (fst p) kt /\ type_of Gstore Genv (snd p) vt) l ->
                      type_of Gstore Genv (EDict l) (TDict kt vt)
  | TyEInsert d kt vt k v : type_of Gstore Genv d (TDict kt vt) ->
                           type_of Gstore Genv k kt ->
                           type_of Gstore Genv v vt ->
                           type_of Gstore Genv (EInsert d k v) (TDict kt vt)
  | TyEDelete d kt vt k : type_of Gstore Genv d (TDict kt vt) ->
                           type_of Gstore Genv k kt ->
                           type_of Gstore Genv (EDelete d k) (TDict kt vt)
  | TyELookup d kt vt k : type_of Gstore Genv d (TDict kt vt) ->
                         type_of Gstore Genv k kt ->
                         type_of Gstore Genv (ELookup d k) (TOption vt)
  | TyEOptMatch e t1 e_none t2 x e_some : type_of Gstore Genv e (TOption t1) ->
                                    type_of Gstore Genv e_none t2 ->
                                    type_of Gstore (map.put Genv x t1) e_some t2 ->
                                    type_of Gstore Genv (EOptMatch e e_none x e_some) t2
  | TyEDictFold d kt vt e0 t k v acc e : type_of Gstore Genv d (TDict kt vt) ->
                                         type_of Gstore Genv e0 t ->
                                         type_of Gstore (map.put (map.put (map.put Genv k kt) v vt) acc t) e t ->
                                         type_of Gstore Genv (EDictFold d e0 k v acc e) t
  | TyESort l t : type_of Gstore Genv l (TList t) ->
                  type_of Gstore Genv (ESort l) (TList t)
  | TyEFilter e t x p : type_of Gstore Genv e (TList t) ->
                        type_of Gstore (map.put Genv x t) p TBool ->
                        type_of Gstore Genv (EFilter e x p) (TList t)
  | TyEJoin e1 t1 e2 t2 x y p r t3 : type_of Gstore Genv e1 (TList t1) ->
                                     type_of Gstore Genv e2 (TList t2) ->
                                     type_of Gstore (map.put (map.put Genv x t1) y t2) p TBool ->
                                     type_of Gstore (map.put (map.put Genv x t1) y t2) r t3 ->
                                     type_of Gstore Genv (EJoin e1 e2 x y p r) (TList t3)
  | TyEProj e t1 x r t2 : type_of Gstore Genv e (TList t1) ->
                          type_of Gstore (map.put Genv x t1) r t2 ->
                          type_of Gstore Genv (EProj e x r) (TList t2).

  Inductive well_typed (Gstore Genv : tenv) : command -> Prop :=
  | WTCSkip : well_typed Gstore Genv CSkip
  | WTCSeq c1 c2 : well_typed Gstore Genv c1 -> well_typed Gstore Genv c2 ->
                   well_typed Gstore Genv (CSeq c1 c2)
  | WTCLet e t x c : type_of Gstore Genv e t ->
                     well_typed Gstore (map.put Genv x t) c ->
                     well_typed Gstore Genv (CLet e x c)
  | WTCLetMut e t x c : type_of Gstore Genv e t ->
                        well_typed (map.put Gstore x t) Genv c ->
                        well_typed Gstore Genv (CLetMut e x c)
  | WTCAssign x t e : map.get Gstore x = Some t ->
                    type_of Gstore Genv e t ->
                    well_typed Gstore Genv (CAssign x e)
  | WTCIf e c1 c2 : type_of Gstore Genv e TBool ->
                    well_typed Gstore Genv c1 -> well_typed Gstore Genv c2 ->
                    well_typed Gstore Genv (CIf e c1 c2)
  | WTCForeach e t x c : type_of Gstore Genv e (TList t) ->
                       well_typed Gstore (map.put Genv x t) c ->
                       well_typed Gstore Genv (CForeach e x c).

  Section TypeOfIH.
    Context (Gstore : tenv).
    Context (P : tenv -> expr -> type -> Prop).

    Hypothesis (f_var : forall Genv x t, map.get Genv x = Some t -> P Genv (EVar x) t).
    Hypothesis (f_loc : forall Genv x t, map.get Gstore x = Some t -> P Genv (ELoc x) t).
    Hypothesis (f_atom : forall Genv a t, type_of_atom a t -> P Genv (EAtom a) t).
    Hypothesis (f_unop : forall Genv o e t1 t2, type_of_unop o t1 t2 -> type_of Gstore Genv e t1 -> P Genv e t1 -> P Genv (EUnop o e) t2).
    Hypothesis (f_binop : forall Genv o e1 e2 t1 t2 t3, type_of_binop o t1 t2 t3 -> type_of Gstore Genv e1 t1 -> P Genv e1 t1 ->
                                                        type_of Gstore Genv e2 t2 -> P Genv e2 t2 -> P Genv (EBinop o e1 e2) t3).
    Hypothesis (f_if : forall Genv e1 e2 e3 t, type_of Gstore Genv e1 TBool -> P Genv e1 TBool ->
                                               type_of Gstore Genv e2 t -> P Genv e2 t ->
                                               type_of Gstore Genv e3 t -> P Genv e3 t ->
                                               P Genv (EIf e1 e2 e3) t).
    Hypothesis (f_let : forall Genv e1 t1 x e2 t2, type_of Gstore Genv e1 t1 -> P Genv e1 t1 ->
                                                   type_of Gstore (map.put Genv x t1) e2 t2 -> P (map.put Genv x t1) e2 t2 ->
                                                   P Genv (ELet e1 x e2) t2).
    Hypothesis (f_flatmap : forall Genv e1 t1 x e2 t2, type_of Gstore Genv e1 (TList t1) -> P Genv e1 (TList t1) ->
                                                       type_of Gstore (map.put Genv x t1) e2 (TList t2) -> P (map.put Genv x t1) e2 (TList t2) ->
                                                       P Genv (EFlatmap e1 x e2) (TList t2)).
    Hypothesis (f_fold : forall Genv e1 t1 e2 t2 x y e3,
                   type_of Gstore Genv e1 (TList t1) -> P Genv e1 (TList t1) ->
                   type_of Gstore Genv e2 t2 -> P Genv e2 t2 ->
                   type_of Gstore (map.put (map.put Genv x t1) y t2) e3 t2 -> P (map.put (map.put Genv x t1) y t2) e3 t2 ->
                   P Genv (EFold e1 e2 x y e3) t2).
    Hypothesis (f_record : forall Genv l tl tl', List.map fst l = List.map fst tl ->
                                                 Forall2 (type_of Gstore Genv) (List.map snd l) (List.map snd tl) ->
                                                 Forall2 (P Genv) (List.map snd l) (List.map snd tl) ->
                                                 Permutation tl tl' ->
                                                 NoDup (List.map fst tl) ->
                                                 StronglySorted record_entry_leb tl' ->
                                                 P Genv (ERecord l) (TRecord tl')).
    Hypothesis (f_access : forall Genv e tl x t, type_of Gstore Genv e (TRecord tl) -> P Genv e (TRecord tl) ->
                                                 access_record tl x = Success t ->
                                                 P Genv (EAccess e x) t).
    Hypothesis (f_dict : forall Genv l kt vt, type_wf kt -> type_wf vt ->
                                              Forall (fun p => type_of Gstore Genv (fst p) kt /\ type_of Gstore Genv (snd p) vt) l ->
                                              Forall (fun p => P Genv (fst p) kt /\ P Genv (snd p) vt) l -> P Genv (EDict l) (TDict kt vt)).
    Hypothesis (f_insert : forall Genv d kt vt k v, type_of Gstore Genv d (TDict kt vt) -> P Genv d (TDict kt vt) ->
                                                    type_of Gstore Genv k kt -> P Genv k kt -> type_of Gstore Genv v vt -> P Genv v vt ->
                                                    P Genv (EInsert d k v) (TDict kt vt)).
    Hypothesis (f_delete : forall Genv d kt vt k, type_of Gstore Genv d (TDict kt vt) ->
                                                  P Genv d (TDict kt vt) -> type_of Gstore Genv k kt -> P Genv k kt ->
                                                  P Genv (EDelete d k) (TDict kt vt)).
    Hypothesis (f_lookup : forall Genv d kt vt k, type_of Gstore Genv d (TDict kt vt) -> P Genv d (TDict kt vt) ->
                                                  type_of Gstore Genv k kt -> P Genv k kt -> P Genv (ELookup d k) (TOption vt)).
    Hypothesis (f_optmatch : forall Genv e t1 e_none t2 x e_some, type_of Gstore Genv e (TOption t1) -> P Genv e (TOption t1) ->
                                                                  type_of Gstore Genv e_none t2 -> P Genv e_none t2 ->
                                                                  type_of Gstore (map.put Genv x t1) e_some t2 -> P (map.put Genv x t1) e_some t2 ->
                                                                  P Genv (EOptMatch e e_none x e_some) t2).
    Hypothesis (f_dictfold : forall Genv d kt vt e0 t k v acc e, type_of Gstore Genv d (TDict kt vt) -> P Genv d (TDict kt vt) ->
                                                                  type_of Gstore Genv e0 t -> P Genv e0 t ->
                                                                  type_of Gstore (map.put (map.put (map.put Genv k kt) v vt) acc t) e t -> P (map.put (map.put (map.put Genv k kt) v vt) acc t) e t ->
                                                                  P Genv (EDictFold d e0 k v acc e) t).
    Hypothesis (f_sort : forall Genv l t, type_of Gstore Genv l (TList t) -> P Genv l (TList t) ->
                                          P Genv (ESort l) (TList t)).
    Hypothesis (f_filter : forall Genv e t x p, type_of Gstore Genv e (TList t) -> P Genv e (TList t) ->
                                                type_of Gstore (map.put Genv x t) p TBool -> P (map.put Genv x t) p TBool ->
                                                P Genv (EFilter e x p) (TList t)).
    Hypothesis (f_join : forall Genv e1 t1 e2 t2 x y p r t3,
                   type_of Gstore Genv e1 (TList t1) -> P Genv e1 (TList t1) ->
                   type_of Gstore Genv e2 (TList t2) -> P Genv e2 (TList t2) ->
                   type_of Gstore (map.put (map.put Genv x t1) y t2) p TBool -> P (map.put (map.put Genv x t1) y t2) p TBool ->
                   type_of Gstore (map.put (map.put Genv x t1) y t2) r t3 -> P (map.put (map.put Genv x t1) y t2) r t3 ->
                   P Genv (EJoin e1 e2 x y p r) (TList t3)).
    Hypothesis (f_proj : forall Genv e t1 x r t2, type_of Gstore Genv e (TList t1) -> P Genv e (TList t1) ->
                                                  type_of Gstore (map.put Genv x t1) r t2 -> P (map.put Genv x t1) r t2 ->
                                                  P Genv (EProj e x r) (TList t2)).
    Section __.
      Context (type_of_IH : forall Genv e t, type_of Gstore Genv e t -> P Genv e t).

      Fixpoint dict_type_of_IH Genv kt vt l (H : Forall (fun p => type_of Gstore Genv (fst p) kt /\ type_of Gstore Genv (snd p) vt) l) : Forall (fun p => P Genv (fst p) kt /\ P Genv (snd p) vt) l :=
        match H with
        | Forall_nil _ => Forall_nil _
        | @Forall_cons _ _ p l Hp Hl =>
            match Hp with
            | conj Hfst Hsnd =>
                @Forall_cons _ _ p l (conj (type_of_IH _ _ _ Hfst) (type_of_IH _ _ _ Hsnd)) (dict_type_of_IH Genv kt vt l Hl)
            end
        end.

      Fixpoint record_type_of_IH Genv (l : list expr) (tl : list type) (H : Forall2 (type_of Gstore Genv) l tl) : Forall2 (P Genv) l tl :=
        match H with
        | Forall2_nil _ => Forall2_nil _
        | @Forall2_cons _ _ _ e t l tl He Hl => @Forall2_cons _ _ _ e t l tl (type_of_IH _ _ _ He) (record_type_of_IH Genv l tl Hl)
        end.
    End __.

    Fixpoint type_of_IH Genv e t (H : type_of Gstore Genv e t) : P Genv e t :=
      match H with
      | TyEVar _ _ x t Hvar => f_var Genv x t Hvar
      | TyELoc _ _ x t Hloc => f_loc Genv x t Hloc
      | TyEAtom _ _ a t Hatom => f_atom Genv a t Hatom
      | TyEUnop _ _ o e t1 t2 Ho He => f_unop Genv o e t1 t2 Ho He (type_of_IH Genv e t1 He)
      | TyEBinop _ _ o e1 e2 t1 t2 t3 Ho He1 He2 => f_binop Genv o e1 e2 t1 t2 t3 Ho He1 (type_of_IH Genv e1 t1 He1) He2 (type_of_IH Genv e2 t2 He2)
      | TyEIf _ _ e1 e2 e3 t He1 He2 He3 => f_if Genv e1 e2 e3 t He1 (type_of_IH Genv e1 TBool He1) He2 (type_of_IH Genv e2 t He2) He3 (type_of_IH Genv e3 t He3)
      | TyELet _ _ e1 t1 x e2 t2 He1 He2 => f_let Genv e1 t1 x e2 t2 He1 (type_of_IH Genv e1 t1 He1) He2 (type_of_IH (map.put Genv x t1) e2 t2 He2)
      | TyEFlatmap _ _ e1 t1 x e2 t2 He1 He2 => f_flatmap Genv e1 t1 x e2 t2 He1 (type_of_IH Genv e1 (TList t1) He1) He2 (type_of_IH (map.put Genv x t1) e2 (TList t2) He2)
      | TyEFold _ _ e1 t1 e2 t2 x y e3 He1 He2 He3 => f_fold Genv e1 t1 e2 t2 x y e3 He1 (type_of_IH Genv e1 (TList t1) He1) He2 (type_of_IH Genv e2 t2 He2) He3 (type_of_IH (map.put (map.put Genv x t1) y t2) e3 t2 He3)
      | TyERecord _ _ l tl tl' Hname Hfield Hpermu Hnodup Hsort => f_record Genv l tl tl' Hname Hfield (record_type_of_IH type_of_IH Genv (List.map snd l) (List.map snd tl) Hfield) Hpermu Hnodup Hsort
      | TyEAccess _ _ e tl x t He Hin => f_access Genv e tl x t He (type_of_IH Genv e (TRecord tl) He) Hin
      | TyEDict _ _ l kt vt Hkt Hvt Hl => f_dict Genv l kt vt Hkt Hvt Hl (dict_type_of_IH type_of_IH Genv kt vt l Hl)
      | TyEInsert _ _ d kt vt k v Hd Hk Hv => f_insert Genv d kt vt k v Hd (type_of_IH Genv d (TDict kt vt) Hd) Hk (type_of_IH Genv k kt Hk) Hv (type_of_IH Genv v vt Hv)
      | TyEDelete _ _ d kt vt k Hd Hk => f_delete Genv d kt vt k Hd (type_of_IH Genv d (TDict kt vt) Hd) Hk (type_of_IH Genv k kt Hk)
      | TyELookup _ _ d kt vt k Hd Hk => f_lookup Genv d kt vt k Hd (type_of_IH Genv d (TDict kt vt) Hd) Hk (type_of_IH Genv k kt Hk)
      | TyEOptMatch _ _ e t1 e_none t2 x e_some He He_none He_some => f_optmatch Genv e t1 e_none t2 x e_some He (type_of_IH Genv e (TOption t1) He) He_none (type_of_IH Genv e_none t2 He_none) He_some (type_of_IH (map.put Genv x t1) e_some t2 He_some)
      | TyEDictFold _ _ d kt vt e0 t k v acc e Hd He0 He => f_dictfold Genv d kt vt e0 t k v acc e Hd (type_of_IH Genv d (TDict kt vt) Hd) He0 (type_of_IH Genv e0 t He0)  He (type_of_IH (map.put (map.put (map.put Genv k kt) v vt) acc t) e t He)
      | TyESort _ _ l t Hl => f_sort Genv l t Hl (type_of_IH Genv l (TList t) Hl)
      | TyEFilter _ _ e t x p He Hp => f_filter Genv e t x p He (type_of_IH Genv e (TList t) He) Hp (type_of_IH (map.put Genv x t) p TBool Hp)
      | TyEJoin _ _ e1 t1 e2 t2 x y p r t3 He1 He2 Hp Hr => f_join Genv e1 t1 e2 t2 x y p r t3 He1
                   (type_of_IH Genv e1 (TList t1) He1) He2 (type_of_IH Genv e2 (TList t2) He2) Hp (type_of_IH (map.put (map.put Genv x t1) y t2) p TBool Hp) Hr (type_of_IH (map.put (map.put Genv x t1) y t2) r t3 Hr)
      | TyEProj _ _ e t1 x r t2 He Hr => f_proj Genv e t1 x r t2 He (type_of_IH Genv e (TList t1) He) Hr (type_of_IH (map.put Genv x t1) r t2 Hr)
      end.
    End TypeOfIH.

    Lemma tenv_wf_step : forall G t, tenv_wf G -> type_wf t -> forall x, tenv_wf (map.put G x t).
    Proof.
      unfold tenv_wf; intros. destruct (String.eqb x x0) eqn:E.
      - rewrite eqb_eq in *; subst. rewrite map.get_put_same in *.
        injection H1; intro; subst; auto.
      - rewrite eqb_neq in *. rewrite map.get_put_diff in *; eauto.
    Qed.

    Lemma Forall_access_record : forall A P l k (v : A),
        Forall P (List.map snd l) -> access_record l k = Success v -> P v.
    Proof.
      induction l; simpl; intros; try discriminate.
      - inversion H; subst. destruct a; simpl in *.
        destruct (String.eqb k s).
        + injection H0; intros; subst; auto.
        + eapply IHl; eauto.
    Qed.

    Lemma type_of__type_wf : forall Gstore Genv e t,
        tenv_wf Gstore ->
        tenv_wf Genv ->
        type_of Gstore Genv e t ->
        type_wf t.
    Proof.
      intros Gstore Genv e t H_store H_env H. induction H using type_of_IH; eauto.
      - inversion H; constructor; auto.
      - inversion H; constructor; auto.
      - inversion H; repeat constructor; auto.
      - auto using tenv_wf_step.
      - apply IHtype_of2. apply tenv_wf_step; auto.
        apply IHtype_of1 in H_env as H_wf1. inversion H_wf1; auto.
      - constructor; auto.
        + apply Permutation_map with (f := fst) in H2. eapply Permutation_NoDup; eauto.
        + apply Permutation_map with (f := snd), Permutation_sym in H2.
          rewrite Forall_forall; intros t H_in. eapply Permutation_in in H_in; eauto.
          remember (List.map snd tl) as tl2. revert H_env H1 H_in; clear; intros.
          induction H1; try apply in_nil in H_in; intuition.
          inversion H_in; subst; auto.
      - apply IHtype_of in H_env as H_wf. inversion H_wf; subst.
        eapply Forall_access_record; eauto.
      - constructor; auto.
      - apply IHtype_of1 in H_env as H_wf1. inversion H_wf1; constructor; auto.
      - constructor; apply IHtype_of4. repeat apply tenv_wf_step; auto.
        + apply IHtype_of1 in H_env as H_wf1. inversion H_wf1; auto.
        + apply IHtype_of2 in H_env as H_wf2. inversion H_wf2; auto.
      - constructor; apply IHtype_of2, tenv_wf_step; auto.
        apply IHtype_of1 in H_env as H_wf1. inversion H_wf1; auto.
    Qed.
End WithMap.

(* Bidirectional type checking *)
Fixpoint type_eqb (t t' : type) {struct t} : bool :=
  match t, t' with
  | TWord, TWord
  | TInt, TInt
  | TBool, TBool
  | TString, TString
  | TUnit, TUnit => true
  | TOption t1, TOption t1' => type_eqb t1 t1'
  | TList t1, TList t1' => type_eqb t1 t1'
  | TRecord l, TRecord l' => list_beq _ (fun p p' => andb (String.eqb (fst p) (fst p'))
                                                       (type_eqb (snd p) (snd p'))) l l'
  | TDict kt vt, TDict kt' vt' => andb (type_eqb kt kt') (type_eqb vt vt')
  | _, _ => false
  end.

Lemma type_eqb_eq : forall t t', type_eqb t t' = true -> t = t'.
Proof.
  apply (type_IH (fun t => forall t', type_eqb t t' = true -> t = t')); intros;
    destruct t'; try discriminate; simpl in *; intuition;
  try (apply H in H0; congruence).
  - generalize dependent l0. induction l; destruct l0; simpl in *; try discriminate; intuition.
    destruct (andb (fst a =? fst p)%string (type_eqb (snd a) (snd p))) eqn:E; simpl in *; try discriminate.
    inversion H; subst. apply (IHl H4) in H0. injection H0; intros; subst.
    destruct a, p; inversion H; simpl in *; subst. apply andb_prop in E as [EL ER].
    rewrite eqb_eq in EL. apply H3 in ER. congruence.
  - apply andb_prop in H1 as [HL HR]. apply H in HL; apply H0 in HR. congruence.
Qed.

Definition compare_types (expected : type) (t : type) {A : Type} (a : A): result A :=
  if type_eqb expected t then Success a else error:(a "has type" t "but expected" expected).

Definition analyze_atom (expected : type) (a : atom) : result atom :=
  match a with
  | AWord n => compare_types expected TWord a
  | AInt n => compare_types expected TInt a
  | ABool b => compare_types expected TBool a
  | AString s => compare_types expected TString a
  | ANone t => match t with
               | Some t => compare_types expected (TOption t) a
               | None => match expected with
                         | TOption t' => Success (ANone (Some t'))
                         | _ => error:(a "is an option but expected" expected)
                         end
               end
  | ANil t => match t with
              | Some t => compare_types expected (TList t) a
              | None => match expected with
                        | TList t' => Success (ANil (Some t'))
                        | _ => error:(a "is a list but expected" expected)
                        end
              end
  | AUnit => compare_types expected TUnit a
  end.

(* Computable type-checker *)
Definition synthesize_atom (a : atom) : result (type * atom) :=
  match a with
  | AWord n => Success (TWord, a)
  | AInt n => Success (TInt, a)
  | ABool b => Success (TBool, a)
  | AString s => Success (TString, a)
  | ANone t => match t with
               | Some t => if type_wf_comp t
                           then Success (TOption t, a)
                           else error:("Malformed type" t)
               | None => error:("Insufficient type information for" a)
               end
  | ANil t => match t with
              | Some t => if type_wf_comp t
                          then Success (TList t, a)
                          else error:("Malformed type" t)
              | None => error:("Insufficient type information for" a)
              end
  | AUnit => Success (TUnit, a)
  end.

Definition unop_types (o : unop) : (type * type) :=
  match o with
  | OWNeg => (TWord, TWord)
  | ONeg => (TInt, TInt)
  | ONot => (TBool, TBool)
  | OLengthString => (TString, TInt)
  | OIntToString => (TInt, TString)
  | _ => (TUnit, TUnit) (* unused *)
  end.

Definition binop_types (o : binop) : (type * type * type) :=
  match o with
  | OWPlus | OWMinus | OWTimes | OWDivU | OWDivS | OWModU | OWModS => (TWord, TWord, TWord)
  | OPlus | OMinus | OTimes | ODiv | OMod => (TInt, TInt, TInt)
  | OConcatString => (TString, TString, TString)
  | OAnd | OOr => (TBool, TBool, TBool)
  | OWLessU | OWLessS => (TWord, TWord, TBool)
  | OLess => (TInt, TInt, TBool)
  | OWRange => (TWord, TWord, TList TWord)
  | ORange => (TInt, TInt, TList TInt)
  | _ => (TUnit, TUnit, TUnit) (* unused *)
  end.

Fixpoint record_type_from' (l : list (string * result (type * expr))) : result (list (string * type) * list (string * expr)) :=
  match l with
  | nil => Success (nil, nil)
  | (s, Success (t, e)) :: l => '(tl, el) <- record_type_from' l ;;
                                if inb (String.eqb) s (List.map fst l) then error:("Duplicate record key" s)
                                else Success ((s, t) :: tl, (s, e) :: el)
  | (_, Failure err) :: _ => Failure err
  end.

Definition record_type_from (l : list (string * result (type * expr))) : result (type * expr) :=
  '(tl, el) <- record_type_from' l ;; Success (TRecord (record_sort tl), ERecord el).

Fixpoint record_from' (l : list (string * result expr)) : result (list (string * expr)) :=
  match l with
  | nil => Success nil
  | (s, Success e) :: l => l' <- record_from' l ;;
                           if inb (String.eqb) s (List.map fst l) then error:("Duplicate record key" s)
                           else Success ((s, e) :: l')
  | (_, Failure err) :: _ => Failure err
  end.

Definition record_from (l : list (string * result expr)) : result expr :=
  l' <- record_from' l ;; Success (ERecord l').

Definition access_record_field (e : expr) (s : string) : result expr :=
  match e with
  | ERecord l => access_record l s
  | _ => error:(e "is not a record")
  end.

Definition get_attr_type (tl : list (string * type)) (s : string) : type :=
  match access_record tl s with
  | Success t => t
  | Failure _ => TUnit
  end.

Fixpoint first_success (l : list (result (type * expr))) :  result type :=
  match l with
  | nil => error:("Insufficient type information")
  | Success (t, e) :: l => Success t
  | _ :: l => first_success l
  end.

Fixpoint dict_type_from' (l : list (result (type * expr * type * expr))) : result (type * type * list (expr * expr)) :=
  match l with
  | nil => error:("Insufficient type information for dictionary")
  | Success (kt, ke, vt, ve) :: nil => Success (kt, vt, (ke, ve) :: nil)
  | Success (kt, ke, vt, ve) :: l => '(kt0, vt0, el) <- dict_type_from' l ;;
                                     if andb (type_eqb kt kt0) (type_eqb vt vt0) then Success (kt0, vt0, (ke, ve) :: el)
                                     else error:(ke "has type" kt "and" ve "has type" vt "but expected" kt0 "and" vt0 "respectively")
  | Failure err :: _ => Failure err
  end.

Definition dict_type_from (l : list (result (type * expr * type * expr))) : result (type * expr) :=
  '(kt, vt, el) <- dict_type_from' l ;; Success (TDict kt vt, EDict el).

Fixpoint dict_from' (l : list (result (expr * expr))) : result (list (expr * expr)) :=
  match l with
  | nil => Success nil
  | Success (k, v) :: l => l' <- dict_from' l ;; Success ((k, v) :: l')
  | Failure err :: _ => Failure err
  end.

Definition dict_from (l : list (result (expr * expr))) : result expr :=
  l' <- dict_from' l ;; Success (EDict l').

Section WithMap.
  Context {tenv: map.map string type} {tenv_ok: map.ok tenv}.

    Section __.
      Context (analyze_expr : tenv -> tenv -> type -> expr -> result expr).

      Definition analyze_dict_body (Gstore Genv : tenv) (kt vt : type) (l : list (expr * expr)) :=
        dict_from (List.map (fun '(k, v) => k' <- analyze_expr Gstore Genv kt k ;;
                                            v' <- analyze_expr Gstore Genv vt v ;;
                                            Success (k', v')) l).
    End __.

  Local Open Scope bool_scope.
  Fixpoint analyze_expr (Gstore Genv : tenv) (expected : type) (e : expr) : result expr :=
    match e with
    | EVar x => match map.get Genv x with
                | Some t => if type_eqb expected t then Success (EVar x)
                            else error:("Immutable variable" x "has type" t "but expected" expected)
                | None => error:(x "not found in the immutable variable type environment")
                end
    | ELoc x => match map.get Gstore x with
                | Some t => if type_eqb expected t then Success (ELoc x)
                            else error:("Mutable variable" x "has type" t "but expected" expected)
                | None => error:(x "not found in the mutable variable type environment")
                end
    | EAtom a => a' <- analyze_atom expected a ;; Success (EAtom a')
    | EUnop o e1 => match o with
                    | OLength => '(t, e') <- synthesize_expr Gstore Genv e1 ;;
                                 match t with
                                 | TList t => if type_eqb expected TInt then Success (EUnop o e')
                                              else error:(e "has type" TInt "but expected" expected)
                                 | _ => error:(e1 "has type" t "but expected a list")
                                 end
                    | OSome => match expected with
                               | TOption t => analyze_expr Gstore Genv t e1
                               | _ => error:(e "is an option but expected" expected)
                               end
                    | o => let '(t1, t2) := unop_types o in
                           if type_eqb expected t2 then analyze_expr Gstore Genv t1 e1
                           else error:(e "has type" e1 "but expected" expected)
                    end
    | EBinop o e1 e2 => match o with
                        | OCons =>
                            match expected with
                            | TList t => e1' <- analyze_expr Gstore Genv t e1 ;; e2' <- analyze_expr Gstore Genv (TList t) e2 ;;
                                         Success (EBinop o e1' e2')
                            | _ => error:(e "is a list but expected" expected)
                            end
                        | OConcat =>
                            match expected with
                            | TList t => e1' <- analyze_expr Gstore Genv (TList t) e1 ;; e2' <- analyze_expr Gstore Genv (TList t) e2 ;;
                                         Success (EBinop o e1' e2')
                            | _ => error:(e "is a list but expected" expected)
                            end
                        | ORepeat =>
                            match expected with
                            | TList t => e1' <- analyze_expr Gstore Genv (TList t) e1 ;; e2' <- analyze_expr Gstore Genv TInt e2 ;;
                                              Success (EBinop o e1' e2')
                            | _ => error:(e "is a list but expected" expected)
                            end
                        | OEq =>
                            match expected with
                            | TBool => match synthesize_expr Gstore Genv e1 with
                                       | Success (t, e1') => e2' <- analyze_expr Gstore Genv t e2 ;;
                                                             Success (EBinop OEq e1' e2')
                                       | Failure err => '(t, e2') <- synthesize_expr Gstore Genv e2 ;;
                                                        e1' <- analyze_expr Gstore Genv t e1 ;;
                                                        Success (EBinop OEq e1' e2')
                                       end
                            | _ => error:(e "is a boolean but expected" expected)
                            end
                        | o => let '(t1, t2, t3) := binop_types o in
                               if type_eqb expected t3
                               then e1' <- analyze_expr Gstore Genv t1 e1 ;;
                                    e2' <- analyze_expr Gstore Genv t2 e2 ;;
                                    Success (EBinop o e1' e2')
                               else error:(e "has type" t3 "but expected" expected)
                        end
    | EIf e1 e2 e3 => e1' <- analyze_expr Gstore Genv TBool e1 ;;
                      e2' <- analyze_expr Gstore Genv expected e2 ;;
                      e3' <- analyze_expr Gstore Genv expected e3 ;;
                      Success (EIf e1' e2' e3')
    | ELet e1 x e2 => '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                      e2' <- analyze_expr Gstore (map.put Genv x t1) expected e2 ;;
                      Success (ELet e1' x e2')
    | EFlatmap e1 x e2 => match expected with
                          | TList t2 =>
                              '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                              match t1 with
                              | TList t1 => e2' <- analyze_expr Gstore (map.put Genv x t1) (TList t2) e2 ;;
                                            Success (EFlatmap e1' x e2')
                              | t1 => error:(e1 "has type" t1 "but expected a list")
                              end
                          | _ => error:(e "is a list but expected" expected)
                          end
    | EFold e1 e2 x y e3 => '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                            match t1 with
                            | TList t1 => e2' <- analyze_expr Gstore Genv expected e2 ;;
                                          e3' <- analyze_expr Gstore (map.put (map.put Genv x t1) y expected) expected e3 ;;
                                          Success (EFold e1' e2' x y e3')
                            | t1 => error:(e1 "has type" t1 "but expected a list")
                            end
    | ERecord l => match expected with
                   | TRecord tl =>
                       if Nat.leb (length tl) (length l)
                       then
                         if inclb String.eqb (List.map fst l) (List.map fst tl) &&
                              inclb String.eqb (List.map fst tl) (List.map fst l)
                         then record_from (List.map
                                             (fun '(s, e) => (s, analyze_expr Gstore Genv (get_attr_type tl s) e))
                                             l)
                         else error:(e "does not have all expected attributes" tl)
                       else error:("Record type" tl "has more attributes than record" l)
                   | _ => error:(e "is a record but expected" expected)
                   end
    | EAccess e s => '(t, e') <- synthesize_expr Gstore Genv e ;;
                     match t with
                     | TRecord l =>
                         t <- access_record l s ;;
                              if type_eqb expected t then Success (EAccess e' s)
                              else error:("Attribute" s "has type" t "but expected" expected)
                     | t => error:(e "has type" t "but expected a record")
                     end
    | EDict l => match expected with
                 | TDict kt vt => analyze_dict_body analyze_expr Gstore Genv kt vt l
                 | _ => error:(e "is a dictionary but expected" expected)
                 end
    | EInsert d k v => match expected with
                       | TDict kt vt =>
                           d' <- analyze_expr Gstore Genv (TDict kt vt) d ;;
                           k' <- analyze_expr Gstore Genv kt k ;;
                           v' <- analyze_expr Gstore Genv vt v ;;
                           Success (EInsert d' k' v')
                       | _ => error:(e "is a dictionary but expected" expected)
                       end
    | EDelete d k => match expected with
                     | TDict kt vt =>
                         d' <- analyze_expr Gstore Genv (TDict kt vt) d ;;
                         k' <- analyze_expr Gstore Genv kt k ;;
                         Success (EDelete d' k')
                     | _ => error:(e "is a dictionary but expected" expected)
                     end
    | ELookup d k => '(t1, d') <- synthesize_expr Gstore Genv d ;;
                     match t1 with
                     | TDict kt vt => if type_eqb expected (TOption vt)
                                      then k' <- analyze_expr Gstore Genv kt k ;;
                                           Success (ELookup d' k')
                                      else error:(e "has type" (TOption vt) "but expected" expected)
                     | t => error:(e "has type" t "but expected a record")
                     end
    | EOptMatch e e_none x e_some =>
        e_none' <- analyze_expr Gstore Genv expected e_none ;;
        '(t, e') <- synthesize_expr Gstore Genv e ;;
        match t with
        | TOption t =>
            e_some' <- analyze_expr Gstore (map.put Genv x t) expected e_some ;;
            Success (EOptMatch e' e_none' x e_some')
        | t => error:(e "has type" t "but expected an option")
        end
    | EDictFold d e0 k v acc e =>
        '(t, d') <- synthesize_expr Gstore Genv d ;;
        match t with
        | TDict kt vt => e0' <- analyze_expr Gstore Genv expected e0 ;;
                         e' <- analyze_expr Gstore (map.put (map.put (map.put Genv k kt) v vt) acc expected) expected e ;;
                         Success (EDictFold d' e0' k v acc e')
        | t => error:(d "has type" t "but expected a dictionary")
        end
    | ESort l => match expected with
                 | TList t => analyze_expr Gstore Genv (TList t) l
                 | _ => error:(l "is a list but expected" expected)
                 end
    | EFilter l x p => match expected with
                       | TList t => l' <- analyze_expr Gstore Genv expected l ;;
                                    p' <- analyze_expr Gstore (map.put Genv x t) TBool p ;;
                                    Success (EFilter l' x p')
                       | _ => error:(e "is a list but expected" expected)
                       end
    | EJoin l1 l2 x y p r => '(t1, l1') <- synthesize_expr Gstore Genv l1 ;;
                             match t1 with
                             | TList t1 => '(t2, l2') <- synthesize_expr Gstore Genv l2 ;;
                                           match t2 with
                                           | TList t2 => let Genv' := map.put (map.put Genv x t1) y t2 in
                                                         p' <- analyze_expr Gstore Genv' TBool p ;;
                                                         match expected with
                                                         | TList t3 =>
                                                             r' <- analyze_expr Gstore Genv' t3 r ;;
                                                             Success (EJoin l1' l2' x y p' r')
                                                         | _ => error:(e "is a list but expected" expected)
                                                         end
                                           | t => error:(l2 "has type" t "but expected a list")
                                           end
                             | t => error:(l1 "has type" t "but expected a list")
                             end
    | EProj l x r => '(t1, l') <- synthesize_expr Gstore Genv l ;;
                     match t1 with
                     | TList t1 => match expected with
                                   | TList t2 => r' <- analyze_expr Gstore (map.put Genv x t1) t2 r ;;
                                                 Success (EProj l' x r')
                                   | _ => error:(e "is a list but expected" expected)
                                   end
                     | t => error:(l "has type" t "but expected a list")
                     end
    end

  with synthesize_expr (Gstore Genv : tenv) (e : expr) : result (type * expr) :=
         match e with
         | EVar x => match map.get Genv x with
                     | Some t => Success (t, e)
                     | None => error:(x "not found in the immutable variable type environment")
                     end
         | ELoc x => match map.get Gstore x with
                     | Some t => Success (t, e)
                     | None => error:(x "not found in the mutable variable type environment")
                     end
         | EAtom a => '(t, a') <- synthesize_atom a ;; Success (t, EAtom a')
         | EUnop o e => match o with
                        | OLength => '(t, e') <- synthesize_expr Gstore Genv e ;;
                                     match t with
                                     | TList _ => Success (TInt, EUnop o e')
                                     | _ => error:(e "has type" t "but expected a list")
                                     end
                        | OSome => '(t, e') <- synthesize_expr Gstore Genv e ;; Success (TOption t, EUnop o e')
                        | o => let '(t1, t2) := unop_types o in
                               e' <- analyze_expr Gstore Genv t1 e ;; Success (t2, EUnop o e')
                        end
         | EBinop o e1 e2 => match o with
                             | OCons =>
                                 match synthesize_expr Gstore Genv e1 with
                                 | Success (t, e1') => e2' <- analyze_expr Gstore Genv (TList t) e2 ;; Success (TList t, EBinop o e1' e2')
                                 | Failure err1 => '(t2, e2') <- synthesize_expr Gstore Genv e2 ;;
                                                   match t2 with
                                                   | TList t => e1' <- analyze_expr Gstore Genv t e1 ;; Success (TList t, EBinop o e1' e2')
                                                   | t => error:(e2 "has type" t "but expected a list")
                                                   end
                                 end
                             | OConcat =>
                                 match synthesize_expr Gstore Genv e1 with
                                 | Success (TList t, e1') => e2' <- analyze_expr Gstore Genv (TList t) e2 ;; Success (TList t, EBinop o e1' e2')
                                 | Success (t, _) => error:(e1 "has type" t "but expected a list")
                                 | Failure err1 => '(t2, e2') <- synthesize_expr Gstore Genv e2 ;;
                                                   match t2 with
                                                   | TList t => e1' <- analyze_expr Gstore Genv (TList t) e1 ;; Success (TList t, EBinop o e1' e2')
                                                   | t => error:(e2 "has type" t "but expected a list")
                                                   end
                                 end
                             | ORepeat =>
                                 '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                                 match t1 with
                                 | TList t => e2' <- analyze_expr Gstore Genv TInt e2 ;; Success (TList t, EBinop o e1' e2')
                                 | t => error:(e1 "has type" t "but expected a list")
                                 end
                             | OEq =>
                                 match synthesize_expr Gstore Genv e1 with
                                 | Success (t, e1') => e2' <- analyze_expr Gstore Genv t e2 ;; Success (TBool, EBinop o e1' e2')
                                 | Failure err => '(t, e2') <- synthesize_expr Gstore Genv e2 ;;
                                                  e1' <- analyze_expr Gstore Genv t e1 ;;
                                                  Success (TBool, EBinop o e1' e2')
                                 end
                             | o => let '(t1, t2, t3) := binop_types o in
                                    e1' <- analyze_expr Gstore Genv t1 e1 ;;
                                    e2' <- analyze_expr Gstore Genv t2 e2 ;;
                                    Success (t3, EBinop o e1' e2')
                             end
         | EIf e1 e2 e3 => e1' <- analyze_expr Gstore Genv TBool e1 ;;
                           match synthesize_expr Gstore Genv e2 with
                           | Success (t, e2') => e3' <- analyze_expr Gstore Genv t e3 ;; Success (t, EIf e1' e2' e3')
                           | Failure err2 => '(t, e3') <- synthesize_expr Gstore Genv e3 ;;
                                             e2' <- analyze_expr Gstore Genv t e2 ;; Success (t, EIf e1' e2' e3')
                           end
         | ELet e1 x e2 => '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                           '(t2, e2') <- synthesize_expr Gstore (map.put Genv x t1) e2 ;;
                           Success (t2, ELet e1' x e2')
         | EFlatmap e1 x e2 => '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                               match t1 with
                               | TList t1 => '(t2, e2') <- synthesize_expr Gstore (map.put Genv x t1) e2 ;;
                                             match t2 with
                                             | TList t2 => Success (TList t2, EFlatmap e1' x e2')
                                             | t2 => error:(e2 "has type" t2 "but expected a list")
                                             end
                               | t1 => error:(e1 "has type" t1 "but expected a list")
                               end
         | EFold e1 e2 x y e3 => '(t1, e1') <- synthesize_expr Gstore Genv e1 ;;
                                 match t1 with
                                 | TList t1 => '(t2, e2') <- synthesize_expr Gstore Genv e2 ;;
                                               e3' <- analyze_expr Gstore (map.put (map.put Genv x t1) y t2) t2 e3 ;;
                                               Success (t2, EFold e1' e2' x y e3')
                                 | t1 => error:(e1 "has type" t1 "but expected a list")
                                 end
         | ERecord l => record_type_from (List.map (fun '(s, e') => (s, synthesize_expr Gstore Genv e')) l)
         | EAccess e s => '(t, e') <- synthesize_expr Gstore Genv e ;;
                          match t with
                          | TRecord l =>
                              t <- access_record l s ;; Success (t, EAccess e' s)
                          | t => error:(e "has type" t "but expected a record")
                          end
         | EDict l => let kl := List.map (fun '(k, _) => synthesize_expr Gstore Genv k) l in
                      let vl := List.map (fun '(_, v) => synthesize_expr Gstore Genv v) l in
                      fst_kt <- first_success kl ;; fst_vt <- first_success vl ;;
                      d <- analyze_dict_body analyze_expr Gstore Genv fst_kt fst_vt l ;;
                      Success (TDict fst_kt fst_vt, d)

         | EInsert d k v => '(t1, d') <- synthesize_expr Gstore Genv d ;;
                            match t1 with
                            | TDict kt vt => k' <- analyze_expr Gstore Genv kt k ;;
                                             v' <- analyze_expr Gstore Genv vt v ;;
                                             Success (t1, EInsert d' k' v')
                            | t => error:(e "has type" t "but expected a record")
                            end
         | EDelete d k => '(t1, d') <- synthesize_expr Gstore Genv d ;;
                          match t1 with
                          | TDict kt _ => k' <- analyze_expr Gstore Genv kt k ;;
                                          Success (t1, EDelete d' k')
                          | t => error:(e "has type" t "but expected a record")
                          end
         | ELookup d k => '(t1, d') <- synthesize_expr Gstore Genv d ;;
                          match t1 with
                          | TDict kt vt => k' <- analyze_expr Gstore Genv kt k ;;
                                           Success (TOption vt, ELookup d' k')
                          | t => error:(e "has type" t "but expected a record")
                          end
         | EOptMatch e e_none x e_some =>
             '(t1, e') <- synthesize_expr Gstore Genv e ;;
             match t1 with
             | TOption t1 =>
                 match synthesize_expr Gstore Genv e_none with
                 | Success (t2, e_none') =>
                     e_some' <- analyze_expr Gstore (map.put Genv x t1) t2 e_some ;;
                     Success (t2, EOptMatch e' e_none' x e_some')
                 | Failure _ =>
                     '(t2, e_some') <- synthesize_expr Gstore (map.put Genv x t1) e_some ;;
                     e_none' <- analyze_expr Gstore Genv t2 e_none ;;
                     Success (t2, EOptMatch e' e_none' x e_some')
                 end
             | t1 => error:(e "has type" t1 "but expected an option")
             end
         | EDictFold d e0 k v acc e =>
             '(t, d') <- synthesize_expr Gstore Genv d ;;
             match t with
             | TDict kt vt =>
                 '(t, e0') <- synthesize_expr Gstore Genv e0 ;;
                 e' <- analyze_expr Gstore (map.put (map.put (map.put Genv k kt) v vt) acc t) t e ;;
                 Success (t, EDictFold d' e0' k v acc e')
             | t => error:(d "has type" t "but expected a dictionary")
             end
         | ESort l =>
             '(t, l') <- synthesize_expr Gstore Genv l ;;
             match t with
             | TList t => Success (TList t, ESort l')
             | t => error:(l "has type" t "but expected a list")
             end
         | EFilter l x p => '(t, l') <- synthesize_expr Gstore Genv l ;;
                              match t with
                              | TList t => p' <- analyze_expr Gstore (map.put Genv x t) TBool p ;;
                                           Success (TList t, EFilter l' x p')
                              | t => error:(l "has type" t "but expected a list")
                              end
         | EJoin l1 l2 x y p r => '(t1, l1') <- synthesize_expr Gstore Genv l1 ;;
                                  match t1 with
                                  | TList t1 => '(t2, l2') <- synthesize_expr Gstore Genv l2 ;;
                                                match t2 with
                                                | TList t2 => let Genv' := map.put (map.put Genv x t1) y t2 in
                                                              p' <- analyze_expr Gstore Genv' TBool p ;;
                                                              '(t3, r') <- synthesize_expr Gstore Genv' r ;;
                                                              Success (TList t3, EJoin l1' l2' x y p' r')
                                                | t => error:(l2 "has type" t "but expected a list")
                                                end
                                  | t => error:(l1 "has type" t "but expected a list")
                                  end
         | EProj l x r => '(t1, l') <- synthesize_expr Gstore Genv l ;;
                          match t1 with
                          | TList t1 => '(t2, r') <- synthesize_expr Gstore (map.put Genv x t1) r ;;
                                        Success (TList t2, EProj l' x r')
                          | t => error:(l "has type" t "but expected a list")
                          end
         end.

  Fixpoint typecheck (Gstore Genv : tenv) (c : command) : result command :=
    match c with
    | CSkip => Success CSkip
    | CSeq c1 c2 => c1' <- typecheck Gstore Genv c1 ;;
                    c2' <- typecheck Gstore Genv c2 ;;
                    Success (CSeq c1' c2')
    | CLet e x c => '(t, e') <- synthesize_expr Gstore Genv e ;;
                    c' <- typecheck Gstore (map.put Genv x t) c ;;
                    Success (CLet e' x c')
    | CLetMut e x c => '(t, e') <- synthesize_expr Gstore Genv e ;;
                    c' <- typecheck (map.put Gstore x t) Genv c ;;
                    Success (CLetMut e' x c')
    | CAssign x e => match map.get Gstore x with
                     | Some t => e' <- analyze_expr Gstore Genv t e ;;
                                 Success (CAssign x e')
                     | None => error:(x "not found in the mutable variable type environment")
                     end
    | CIf e c1 c2 => e' <- analyze_expr Gstore Genv TBool e ;;
                     c1' <- typecheck Gstore Genv c1 ;;
                     c2' <- typecheck Gstore Genv c2 ;;
                     Success (CIf e' c1' c2')
    | CForeach e x c => '(t, e') <- synthesize_expr Gstore Genv e ;;
                        match t with
                        | TList t => c' <- typecheck Gstore (map.put Genv x t) c ;;
                                     Success (CForeach e' x c')
                        | t => error:(e "has type" t "but expected a list")
                        end
    end.
End WithMap.
