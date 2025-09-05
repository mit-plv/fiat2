Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import List String ZArith Permutation.

(* What an expr with a list type can be interpreted to *)
Inductive collection_tag := LikeSet | LikeBag | LikeList.

Section WithMap.
  Context {aenv: map.map string collection_tag} {aenv_ok: map.ok aenv}.

  Definition ordered_update {key value map} (leb : value -> value -> bool) (m : @map.rep key value map) (k : key) (v : value) :=
    match map.get m k with
    | Some v' => if leb v' v then map.put m k v else m
    | None => map.put m k v
    end.

  Definition collection_tag_leb (i1 i2 : collection_tag) : bool :=
    match i1, i2 with
    | LikeBag, LikeSet => false
    | LikeList, LikeSet => false
    | LikeList, LikeBag => false
    | _, _ => true
    end.

  Definition collection_tag_lub (i1 i2 : collection_tag) : collection_tag :=
    match i1, i2 with
    | LikeList, _ | _, LikeList => LikeList
    | LikeBag, _ |  _, LikeBag => LikeBag
    | _, _ => LikeSet
    end.

  Definition lub_merge : aenv -> aenv -> aenv := map.fold (ordered_update collection_tag_leb).

  Definition glb (i1 i2 : collection_tag) : collection_tag :=
    if collection_tag_leb i1 i2 then i1 else i2.

  (* Given the interpretation of the output of the unop if it is list
     return the interpretation of the input *)
  Definition unop_collection_tag (i : collection_tag) (o : unop) : collection_tag :=
    match o with
    | OLength => LikeBag
    | _ => LikeList
    end.

  Definition binop_collection_tag (i : collection_tag) (o : binop) : collection_tag * collection_tag :=
    match o with
    | OConcat => (i, i)
    | ORepeat => (i, LikeList)
    | OCons => (LikeList, i)
    | _ => (LikeList, LikeList)
    end.

  Definition get_collection_tag (m : aenv) (x : string) : collection_tag :=
    match map.get m x with
    | Some i => i
    | None => LikeSet (* x not used *)
    end.

  Section __.
    Context (tag_req : collection_tag -> (aenv * aenv)).
    Fixpoint tag_req_times (x : string) (i : collection_tag) (n : nat) : collection_tag :=
      match n with
      | O => i
      | S n =>
          let '(istr, ienv) := tag_req i in
          if collection_tag_leb (get_collection_tag ienv x) i then i
          else tag_req_times x (get_collection_tag ienv x) n
      end.
  End __.

  Fixpoint tag_req (i : collection_tag) (e : expr) : (aenv * aenv) :=
    match e with
    | EVar x => (map.empty, map.put map.empty x i)
    | ELoc x => (map.put map.empty x i, map.empty)
    | EAtom a => (map.empty, map.empty)
    | EUnop o e => tag_req (unop_collection_tag i o) e
    | EBinop o e1 e2 =>
        let '(i1, i2) := binop_collection_tag i o in
        let '(istr1, ienv1) := tag_req i1 e1 in
        let '(istr2, ienv2) := tag_req i2 e2 in
        (lub_merge istr1 istr2, lub_merge ienv1 ienv2)
    | EIf e1 e2 e3 =>
        let '(istr1, ienv1) := tag_req LikeList e1 in
        let '(istr2, ienv2) := tag_req i e2 in
        let '(istr3, ienv3) := tag_req i e3 in
        (lub_merge (lub_merge istr1 istr2) istr3,
          lub_merge (lub_merge ienv1 ienv2) ienv3)
    | ELet e1 x e2 =>
        let '(istr2, ienv2) := tag_req i e2 in
        let '(istr1, ienv1) := tag_req (get_collection_tag ienv2 x) e1 in
        (lub_merge istr1 istr2, map.update (lub_merge ienv1 ienv2) x (map.get ienv1 x))
    | EFlatmap e1 x e2 =>
        let '(istr1, ienv1) := tag_req i e1 in
        let '(istr2, ienv2) := tag_req i e2 in
        (lub_merge istr1 istr2, map.update (lub_merge ienv1 ienv2) x (map.get ienv1 x))
    | EFold e1 e2 x y e3 =>
        let '(istr1, ienv1) := tag_req LikeList e1 in
        let i' :=  tag_req_times (fun i => tag_req i e3) y i 3 in
        let '(istr3, ienv3) := tag_req i' e3 in
        let '(istr2, ienv2) := tag_req (collection_tag_lub i (get_collection_tag ienv3 y)) e2 in
        let ienv := lub_merge ienv1 ienv2 in
        (lub_merge (lub_merge istr1 istr2) istr3,
          map.update (map.update (lub_merge ienv ienv3) x (map.get ienv x)) y (map.get ienv y))
    | ERecord l =>
        fold_right (fun p acc => let '(istr', ienv') := tag_req LikeList (snd p) in
                                 let '(istr, ienv) := acc in
                                 (lub_merge istr' istr, lub_merge ienv' ienv))
          (map.empty, map.empty) l
    | EAccess e s =>
        let '(istr, ienv) := tag_req LikeList e in
        (istr, ienv)
    | EDict l =>
        fold_right (fun p acc => let '(istr1', ienv1') := tag_req LikeList (fst p) in
                                 let '(istr2', ienv2') := tag_req LikeList (snd p) in
                                 let '(istr, ienv) := acc in
                                 (lub_merge (lub_merge istr1' istr2') istr,
                                   lub_merge (lub_merge ienv1' ienv2') ienv))
          (map.empty, map.empty) l
    | EInsert d k v =>
        let '(istr1, ienv1) := tag_req LikeList d in
        let '(istr2, ienv2) := tag_req LikeList k in
        let '(istr3, ienv3) := tag_req LikeList v in
        (lub_merge (lub_merge istr1 istr2) istr3,
          lub_merge (lub_merge ienv1 ienv2) ienv3)
    | EDelete d k =>
        let '(istr1, ienv1) := tag_req LikeList d in
        let '(istr2, ienv2) := tag_req LikeList k in
        (lub_merge istr1 istr2,
          lub_merge ienv1 ienv2)
    | ELookup d k =>
        let '(istr1, ienv1) := tag_req LikeList d in
        let '(istr2, ienv2) := tag_req LikeList k in
        (lub_merge istr1 istr2,
          lub_merge ienv1 ienv2)
    | EOptMatch e1 e2 x e3 =>
        let '(istr1, ienv1) := tag_req LikeList e1 in
        let '(istr2, ienv2) := tag_req i e2 in
        let '(istr3, ienv3) := tag_req i e3 in
        let ienv := lub_merge ienv1 ienv2 in
        (lub_merge (lub_merge istr1 istr2) istr3,
          map.update (lub_merge ienv ienv3) x (map.get ienv x))
    | EDictFold d e0 k v acc e =>
        (* ??? Not using fixedpoint for this construct for now? *)
        let '(istr1, ienv1) := tag_req LikeList d in
        let '(istr3, ienv3) := tag_req LikeList e in
        let '(istr2, ienv2) := tag_req LikeList e0 in
        let ienv := lub_merge ienv1 ienv2 in
        (lub_merge (lub_merge istr1 istr2) istr3,
          map.update (map.update (map.update (lub_merge ienv ienv3) k (map.get ienv k))
                        v (map.get ienv v)) acc (map.get ienv acc))
    | ESort l => let i' := glb i LikeBag in
                 tag_req i' l
    | EFilter l x p => let '(istr1, ienv1) := tag_req i l in
                       let '(istr2, ienv2) := tag_req LikeList p in
                       (lub_merge istr1 istr2,
                         map.update (lub_merge ienv1 ienv2) x (map.get ienv1 x))
    | EJoin l1 l2 x y p r => let '(istr1, ienv1) := tag_req i l1 in
                             let '(istr2, ienv2) := tag_req i l2 in
                             let '(istr3, ienv3) := tag_req LikeList p in
                             let '(istr4, ienv4) := tag_req LikeList r in
                             let ienv12 := lub_merge ienv1 ienv2 in
                             let ienv34 := lub_merge ienv3 ienv4 in
                             (lub_merge (lub_merge (lub_merge istr1 istr2) istr3) istr4,
                               map.update (map.update (lub_merge ienv12 ienv34) x (map.get ienv12 x)) y (map.get ienv12 y))
    | EProj l x r => let '(istr1, ienv1) := tag_req i l in
                     let '(istr2, ienv2) := tag_req LikeList r in
                     (lub_merge istr1 istr2, map.update (lub_merge ienv1 ienv2) x (map.get ienv1 x))
    end.

  Definition aenv_leb (ienv ienv' : aenv) : bool :=
    map.fold (fun b x i => match map.get ienv' x with
                           | Some i' => andb b (collection_tag_leb i i')
                           | None => false
                           end) true ienv.

  Definition aenv_le_at (x : string) (ienv ienv' : aenv) : Prop :=
    match map.get ienv x with
    | Some i => match map.get ienv' x with
                | Some i' => collection_tag_leb i i' = true
                | None => False
                end
    | None => True
    end.

  Definition aenv_le (ienv ienv' : aenv) : Prop :=
    forall x, aenv_le_at x ienv ienv'.

  Lemma aenv_leb_le : forall (ienv ienv' : aenv), aenv_leb ienv ienv' = true <-> aenv_le ienv ienv'.
  Proof.
    unfold aenv_leb, aenv_le, aenv_le_at; intros.
    apply map.fold_spec.
    1:{ intuition auto. rewrite map.get_empty; trivial. }
    1:{ intros. destruct r; simpl in *.
        1:{ case_match; intuition auto; try congruence.
            1:{ specialize (H0 x). destruct_get_put_strings.
                clear_refl; repeat rewrite_l_to_r; auto. }
            all: specialize (H2 k); rewrite_map_get_put_hyp; rewrite_l_to_r; auto. }
        1:{ case_match; intuition auto; try congruence.
            all: lazymatch goal with H: _ -> ?G |- ?G => apply H end.
            all: intros; specialize (H0 x).
            all: destruct_get_put_strings.
            all: case_match; auto; congruence. } }
  Qed.

  Record analysis_res := mk_res { istr_res : aenv; ienv_res : aenv; invariant_res : aenv }.

  Section __.
    Context (command_tag_req : aenv -> analysis_res).

    Fixpoint command_tag_req_times (istr0 : aenv) (n : nat) : aenv :=
      match n with
      | O => istr0
      | S n =>
          let (istr, ienv, inv) := command_tag_req istr0 in
          if aenv_leb istr istr0 then istr0
          else command_tag_req_times (lub_merge istr istr0) n
      end.
  End __.

  Section WithGlobal.
    Context (tbl : string).

    Fixpoint command_tag_req (istr : aenv) (c : command) {struct c} : analysis_res :=
      (* command_tag_req istr c = (istr', ienv', invariant) means
       To obtain stores related by istr after c executes, we need to start with stores related by istr' and envs related by ienv', with invariant upper bounding the istr throughout the command execution *)
      match c with
      | CSkip => mk_res istr map.empty istr
      | CSeq c1 c2 =>
          let (istr2, ienv2, inv2) := command_tag_req istr c2 in
          let (istr1, ienv1, inv1) := command_tag_req istr2 c1 in
          mk_res istr1 (lub_merge ienv1 ienv2) (lub_merge inv1 inv2)
      | CLet e x c =>
          let (istr2, ienv2, inv2) := command_tag_req istr c in
          let '(istr1, ienv1) := tag_req (get_collection_tag ienv2 x) e in
          mk_res (lub_merge istr1 istr2) (map.update (lub_merge ienv1 ienv2) x (map.get ienv1 x)) (lub_merge inv2 istr1)
      | CLetMut e x c =>
          let (istr2, ienv2, inv2) := command_tag_req (map.put istr x LikeSet) c in
          let '(istr1, ienv1) := tag_req (get_collection_tag istr2 x) e in
          mk_res (lub_merge istr1 (map.update istr2 x (map.get istr x))) (lub_merge ienv1 ienv2) (lub_merge istr1 (map.update inv2 x (map.get istr x)))
      | CAssign x e =>
          let '(istr1, ienv1) := tag_req (get_collection_tag istr x) e in
          let istr01 := lub_merge (map.put istr x LikeSet) istr1 in
          mk_res istr01 ienv1 istr01
      | CIf e c1 c2 =>
          let '(istr1, ienv1) := tag_req LikeList e in
          let (istr2, ienv2, inv2) := command_tag_req istr c1 in
          let (istr3, ienv3, inv3) := command_tag_req istr c2 in
          mk_res (lub_merge istr1 (lub_merge istr2 istr3))
            (lub_merge ienv1 (lub_merge ienv2 ienv3))
            (lub_merge istr1 (lub_merge inv2 inv3))
      | CForeach e x c =>
          let '(istr1, ienv1) := tag_req LikeList e in
          let istr' := command_tag_req_times (fun istr => command_tag_req istr c) istr (Nat.mul 2 (size_of_map istr) + 1) in
          let (istr2, ienv2, inv2) := command_tag_req istr' c in
          mk_res (lub_merge istr (lub_merge istr1 istr2))
            (map.update (lub_merge ienv1 ienv2) x (map.get ienv1 x))
            (lub_merge istr (lub_merge istr1 inv2))
      end.
  End WithGlobal.

  Inductive tag_of (istr ienv : aenv) : expr -> collection_tag -> Prop :=
  (* the permissible collection_tag annotations at a node, given the tags attached to the free variables *)
  | WTAEVar i_avail x i_expect : map.get ienv x = Some i_avail ->
                                 collection_tag_leb i_expect i_avail = true ->
                                 tag_of istr ienv (EVar x) i_expect
  | WTAELoc i_avail x i_expect : map.get istr x = Some i_avail ->
                                 collection_tag_leb i_expect i_avail = true ->
                                 tag_of istr ienv (ELoc x) i_expect
  | WTAEAtom a i_expect : tag_of istr ienv (EAtom a) i_expect
  | WTAEUnop o e i_expect : tag_of istr ienv e (unop_collection_tag i_expect o) ->
                            tag_of istr ienv (EUnop o e) i_expect
  | WTAEBinop i1 i2 o e1 e2 i_expect : binop_collection_tag i_expect o = (i1, i2) ->
                                       tag_of istr ienv e1 i1 ->
                                       tag_of istr ienv e2 i2 ->
                                       tag_of istr ienv (EBinop o e1 e2) i_expect
  | WTAEIf e1 e2 e3 i_expect : tag_of istr ienv e1 LikeList ->
                               tag_of istr ienv e2 i_expect ->
                               tag_of istr ienv e3 i_expect ->
                               tag_of istr ienv (EIf e1 e2 e3) i_expect
  | WTAELet i_x e1 x e2 i_expect : tag_of istr ienv e1 i_x ->
                                   tag_of istr (map.put ienv x i_x) e2 i_expect ->
                                   tag_of istr ienv (ELet e1 x e2) i_expect
  | WTAEFlatmap e1 x e2 i_expect : tag_of istr ienv e1 i_expect ->
                                   tag_of istr (map.put ienv x LikeList) e2 i_expect ->
                                   tag_of istr ienv (EFlatmap e1 x e2) i_expect
  | WTAEFold i2 i3 e1 e2 x y e3 i_expect : collection_tag_leb i_expect i3 = true ->
                                           collection_tag_leb i3 i2 = true ->
                                           tag_of istr ienv e1 LikeList ->
                                           tag_of istr ienv e2 i2 ->
                                           tag_of istr (map.put (map.put ienv x LikeList) y i3) e3 i3 ->
                                           tag_of istr ienv (EFold e1 e2 x y e3) i_expect
  | WTAERecord l i_expect : Forall (fun p => tag_of istr ienv (snd p) LikeList) l ->
                            tag_of istr ienv (ERecord l) i_expect
  | WTAEAccess e s i_expect : tag_of istr ienv e LikeList ->
                              tag_of istr ienv (EAccess e s) i_expect
  | WTAEDict l i_expect : Forall (fun p => tag_of istr ienv (fst p) LikeList /\ tag_of istr ienv (snd p) LikeList) l ->
                          tag_of istr ienv (EDict l) i_expect
  | WTAEInsert d k v i_expect : tag_of istr ienv d LikeList ->
                                tag_of istr ienv k LikeList ->
                                tag_of istr ienv v LikeList ->
                                tag_of istr ienv (EInsert d k v) i_expect
  | WTAEDelete d k i_expect : tag_of istr ienv d LikeList ->
                              tag_of istr ienv k LikeList ->
                              tag_of istr ienv (EDelete d k) i_expect
  | WTAELookup d k i_expect : tag_of istr ienv d LikeList ->
                              tag_of istr ienv k LikeList ->
                              tag_of istr ienv (ELookup d k) i_expect
  | WTAEOptMatch e1 e2 x e3 i_expect : tag_of istr ienv e1 LikeList ->
                                       tag_of istr ienv e2 i_expect ->
                                       tag_of istr (map.put ienv x LikeList) e3 i_expect ->
                                       tag_of istr ienv (EOptMatch e1 e2 x e3) i_expect
  | WTAEDictFold d e0 k v acc e i_expect : tag_of istr ienv d LikeList ->
                                           tag_of istr ienv e0 LikeList ->
                                           tag_of istr (map.put (map.put (map.put ienv k LikeList) v LikeList) acc LikeList) e LikeList ->
                                           tag_of istr ienv (EDictFold d e0 k v acc e) i_expect
  | WTAESort e i_expect : tag_of istr ienv e (glb i_expect LikeBag) ->
                          tag_of istr ienv (ESort e) i_expect
  | WTAEFilter l x p i_expect : tag_of istr ienv l i_expect ->
                                tag_of istr (map.put ienv x LikeList) p LikeList ->
                                tag_of istr ienv (EFilter l x p) i_expect
  | WTAEJoin l1 l2 x1 x2 p r i_expect : tag_of istr ienv l1 i_expect ->
                                        tag_of istr ienv l2 i_expect ->
                                        tag_of istr (map.put (map.put ienv x1 LikeList) x2 LikeList) p LikeList ->
                                        tag_of istr (map.put (map.put ienv x1 LikeList) x2 LikeList) r LikeList ->
                                        tag_of istr ienv (EJoin l1 l2 x1 x2 p r) i_expect
  | WTAEProj l x r i_expect : tag_of istr ienv l i_expect ->
                              tag_of istr (map.put ienv x LikeList) r LikeList ->
                              tag_of istr ienv (EProj l x r) i_expect.

  Inductive well_tagged (istr ienv inv : aenv) : command -> aenv -> Prop :=
  (* Given the tags in istr and ienv, command execution achieves istr_expect *)
  | WTACSkip istr_expect : aenv_le istr inv ->
                           aenv_le istr_expect istr ->
                           well_tagged istr ienv inv CSkip istr_expect
  | WTACSeq istr1 c1 c2 istr_expect : well_tagged istr ienv inv c1 istr1 ->
                                      well_tagged istr1 ienv inv c2 istr_expect ->
                                      well_tagged istr ienv inv (CSeq c1 c2) istr_expect
  | WTACLet e x c i istr_expect : tag_of istr ienv e i ->
                                  well_tagged istr (map.put ienv x i) inv c istr_expect ->
                                  well_tagged istr ienv inv (CLet e x c) istr_expect
  | WTACLetMut e x c i i' istr_expect: aenv_le istr inv ->
                                       tag_of istr ienv e i ->
                                       well_tagged (map.put istr x i) ienv (map.put inv x i') c (map.put istr_expect x LikeSet) ->
                                       aenv_le_at x istr_expect istr ->
                                       well_tagged istr ienv inv (CLetMut e x c) istr_expect
  | WTACAssign x e istr_expect : aenv_le istr inv ->
                                 aenv_le istr_expect (map.put istr x LikeList) ->
                                 tag_of istr ienv e (get_collection_tag istr_expect x) ->
                                 well_tagged istr ienv inv (CAssign x e) istr_expect
  | WTACIf e c1 c2 istr_expect : tag_of istr ienv e LikeList ->
                                 well_tagged istr ienv inv c1 istr_expect ->
                                 well_tagged istr ienv inv c2 istr_expect ->
                                 well_tagged istr ienv inv (CIf e c1 c2) istr_expect
  | WTACForeach l x c istr' istr_expect : aenv_le istr_expect istr' ->
                                          aenv_le istr' istr ->
                                          aenv_le istr inv ->
                                          tag_of istr ienv l LikeList ->
                                          well_tagged istr' (map.put ienv x LikeList) inv c istr' ->
                                          well_tagged istr ienv inv (CForeach l x c) istr_expect.

  Ltac invert_tag_of :=
    lazymatch goal with H: tag_of _ _ _ _ |- _ => inversion H; subst end.

  Lemma collection_tag_leb_refl : forall i, collection_tag_leb i i = true.
  Proof.
    destruct i; auto.
  Qed.

  Lemma aenv_le_at_refl : forall x iG, aenv_le_at x iG iG.
  Proof.
    unfold aenv_le_at; intros.
    case_match; auto using collection_tag_leb_refl.
  Qed.

  Lemma aenv_le_refl : forall iG, aenv_le iG iG.
  Proof.
    unfold aenv_le; auto using aenv_le_at_refl.
  Qed.

  Lemma collection_tag_leb_tran : forall i1 i2 i3,
      collection_tag_leb i1 i2 = true ->
      collection_tag_leb i2 i3 = true ->
      collection_tag_leb i1 i3 = true.
  Proof.
    destruct i1, i2, i3; auto.
  Qed.

  Lemma collection_tag_leb_antisym : forall i1 i2,
      collection_tag_leb i1 i2 = true ->
      collection_tag_leb i2 i1 = true ->
      i1 = i2.
  Proof.
    destruct i1, i2; simpl; intros; congruence.
  Qed.

  Lemma collection_tag_leb_neg : forall i1 i2,
      collection_tag_leb i1 i2 = false ->
      collection_tag_leb i2 i1 = true.
  Proof.
    destruct i1, i2; simpl; auto.
  Qed.

  Lemma aenv_le_at_tran : forall iG1 iG2 iG3 x,
      aenv_le_at x iG1 iG2 ->
      aenv_le_at x iG2 iG3 ->
      aenv_le_at x iG1 iG3.
  Proof.
    unfold aenv_le_at; intros.
    repeat destruct_match_hyp; intuition idtac.
    eapply collection_tag_leb_tran; eauto.
  Qed.

  Lemma aenv_le_tran : forall iG1 iG2 iG3,
      aenv_le iG1 iG2 ->
      aenv_le iG2 iG3 ->
      aenv_le iG1 iG3.
  Proof.
    intros * H1 H2. unfold aenv_le; intros; auto.
    specialize (H1 x); specialize (H2 x).
    eapply aenv_le_at_tran; eauto.
  Qed.

  Lemma binop_collection_tag_increasing : forall o i i' i1 i1' i2 i2',
      collection_tag_leb i i' = true ->
      binop_collection_tag i o = (i1, i2) ->
      binop_collection_tag i' o = (i1', i2') ->
      collection_tag_leb i1 i1' = true /\ collection_tag_leb i2 i2' = true.
  Proof.
    destruct o; simpl; intros; repeat invert_pair; auto.
  Qed.

  Lemma glb_increasing : forall i1 i1' i2 i2',
      collection_tag_leb i1 i1' = true ->
      collection_tag_leb i2 i2' = true ->
      collection_tag_leb (glb i1 i2) (glb i1' i2') = true.
  Proof.
    destruct i1, i1', i2, i2'; auto.
  Qed.

  Lemma tag_of_weaken : forall (e : expr) (istr ienv : aenv) (i i' : collection_tag),
      collection_tag_leb i i' = true ->
      tag_of istr ienv e i' ->
      tag_of istr ienv e i.
  Proof.
    induction e; simpl; intros.
    all: invert_tag_of;
      try now (econstructor; eauto using collection_tag_leb_tran).
    1:{ destruct (binop_collection_tag i o) eqn:E.
        eapply binop_collection_tag_increasing in H; eauto.
        econstructor; intuition eauto. }
    1:{ econstructor; [ | | | | eauto ]; eauto using collection_tag_leb_tran. }
    1:{ constructor. eapply IHe; eauto. apply glb_increasing; auto. }
  Qed.

  Lemma aenv_le_step : forall iG iG' x i i',
      aenv_le iG iG' ->
      collection_tag_leb i i' = true ->
      aenv_le (map.put iG x i) (map.put iG' x i').
  Proof.
    unfold aenv_le, aenv_le_at; intros.
    destruct_get_put_strings; auto.
    apply H.
  Qed.

  Lemma aenv_le_update_step : forall iG iG' x i,
      aenv_le iG iG' ->
      aenv_le (map.update iG x i) (map.update iG' x i).
  Proof.
    unfold aenv_le, aenv_le_at; intros.
    specialize (H x0).
    repeat destruct_get_update_strings; auto.
    all: repeat destruct_match_hyp; intuition auto.
    all: case_match; auto using collection_tag_leb_refl.
  Qed.

  Lemma aenv_le_at__collection_tag_leb : forall x ienv ienv',
      aenv_le_at x ienv ienv' ->
      collection_tag_leb (get_collection_tag ienv x) (get_collection_tag ienv' x) = true.
    intros. unfold aenv_le_at in *.
    unfold get_collection_tag.
    repeat destruct_match_hyp; intuition auto.
  Qed.

  Lemma aenv_le__collection_tag_leb : forall ienv ienv',
      aenv_le ienv ienv' ->
      forall x, collection_tag_leb (get_collection_tag ienv x) (get_collection_tag ienv' x) = true.
    auto using aenv_le_at__collection_tag_leb.
  Qed.

  Ltac invert_well_tagged :=
    lazymatch goal with
      H: well_tagged _ _ _ _ _ |- _ => inversion H; subst end.

  Lemma well_tagged_weaken : forall c (istr ienv inv istr_expect istr_expect' : aenv),
      aenv_le istr_expect istr_expect' ->
      well_tagged istr ienv inv c istr_expect' ->
      well_tagged istr ienv inv c istr_expect.
  Proof.
    induction c; intros.
    all: invert_well_tagged.
    7:{ econstructor. 5: eauto. all: eauto using aenv_le_tran. }
    all: econstructor; eauto using aenv_le_tran, aenv_le_at_tran, aenv_le_step,
      tag_of_weaken, aenv_le__collection_tag_leb.
  Qed.

  Lemma aenv_le_empty : forall iG, aenv_le map.empty iG.
  Proof.
    unfold aenv_le, aenv_le_at; intros.
    rewrite map.get_empty; trivial.
  Qed.

  Lemma ordered_update_sound : forall iG x i k,
     map.get (ordered_update collection_tag_leb iG x i) k =
       if andb (String.eqb x k)
            match map.get iG k with
            | Some i' => collection_tag_leb i' i
            | None => true
            end
       then Some i else map.get iG k.
  Proof.
    intros. repeat case_match; unfold ordered_update;
      try rewrite Bool.andb_true_iff, eqb_eq in *; intuition idtac; subst.
    1,3: repeat rewrite_l_to_r; rewrite_map_get_put_goal; auto.
    1,2: rewrite Bool.andb_false_iff, eqb_neq in *;
    destruct (String.eqb x k) eqn:E_xk; rewrite ?eqb_eq, ?eqb_neq in *; subst.
    1,3: intuition idtac; try discriminate; repeat rewrite_l_to_r; auto.
    1,2: repeat case_match; try rewrite_map_get_put_goal; auto.
  Qed.

  Lemma ordered_update_comm : forall (iG : aenv) x1 x2 i1 i2,
      ordered_update collection_tag_leb (ordered_update collection_tag_leb iG x1 i1) x2 i2 =
        ordered_update collection_tag_leb (ordered_update collection_tag_leb iG x2 i2) x1 i1.
  Proof.
    intros. apply map.map_ext; intros.
    repeat rewrite ordered_update_sound.
    repeat case_match; repeat rewrite Bool.andb_true_iff, eqb_eq in *; intuition idtac;
      try now (f_equal; auto using collection_tag_leb_antisym).
    all: rewrite Bool.andb_false_iff, eqb_neq in *; intuition idtac.
    all: try lazymatch goal with
             H: collection_tag_leb ?i1 ?i2 = true,
               H': collection_tag_leb ?i2 ?i3 = true |- _ =>
          eapply collection_tag_leb_tran in H'; eauto end;
      try congruence.
    all: repeat lazymatch goal with
             H: collection_tag_leb _ _ = false |- _ => apply collection_tag_leb_neg in H end;
      f_equal; auto using collection_tag_leb_antisym.
  Qed.

  Lemma lub_merge_sound : forall iG iG' x,
      map.get (lub_merge iG iG') x =
        match map.get iG x with
        | Some i => match map.get iG' x with
                    | Some i' => Some (if (collection_tag_leb i' i) then i else i')
                    | None => Some i
                    end
        | None => map.get iG' x
        end.
  Proof.
    intros. unfold lub_merge. apply map.fold_spec.
    1: rewrite map.get_empty; case_match; auto.
    1:{ intros. rewrite ordered_update_sound.
        destruct_String_eqb k x; simpl in *;
          rewrite_map_get_put_goal.
        rewrite H0. repeat case_match; f_equal;
          auto using collection_tag_leb_antisym, collection_tag_leb_neg.
        all: try lazymatch goal with
                 H: collection_tag_leb ?i1 ?i2 = true,
                   H': collection_tag_leb ?i2 ?i3 = true |- _ =>
                   eapply collection_tag_leb_tran in H'; eauto end;
          congruence. }
  Qed.

  Lemma lub_merge_put : forall iG iG' x i,
      map.get iG x = None ->
      lub_merge (map.put iG x i) iG' = ordered_update collection_tag_leb (lub_merge iG iG') x i.
  Proof.
    intros. unfold lub_merge. apply map.fold_spec.
    1:{ simpl. rewrite Properties.map.fold_empty.
        unfold ordered_update; rewrite_l_to_r; congruence. }
    1:{ intros. rewrite Properties.map.fold_put; auto.
        1: rewrite_l_to_r; auto.
        all: auto using ordered_update_comm. }
  Qed.

  Lemma lub_merge_comm : forall iG iG',
      lub_merge iG iG' = lub_merge iG' iG.
  Proof.
    intros. apply map.map_ext; intros.
    rewrite !lub_merge_sound; repeat case_match; f_equal;
      auto using collection_tag_leb_neg, collection_tag_leb_antisym.
  Qed.

  Lemma ordered_update_increasing : forall iG x i,
      aenv_le iG (ordered_update collection_tag_leb iG x i).
  Proof.
    intros. unfold ordered_update. repeat case_match.
    2: apply aenv_le_refl.
    all: unfold aenv_le, aenv_le_at; intro;
      destruct_get_put_strings; try rewrite_l_to_r; auto;
      case_match; auto using collection_tag_leb_refl.
  Qed.

  Lemma lub_merge__aenv_le_l : forall iG iG',
      aenv_le iG (lub_merge iG iG').
  Proof.
    unfold lub_merge. intros *. eapply map.fold_spec.
    1: apply aenv_le_refl.
    intros. eapply aenv_le_tran; eauto using ordered_update_increasing.
  Qed.

  Lemma lub_merge__aenv_le_r : forall iG iG',
      aenv_le iG' (lub_merge iG iG').
  Proof.
    intros; rewrite lub_merge_comm.
    apply lub_merge__aenv_le_l.
  Qed.

  Ltac use_tag_of_strengthen_IH :=
    lazymatch goal with
      IH: context[_ -> tag_of _ _ ?e _] |- tag_of _ _ ?e _ =>
        eapply IH end.

  Lemma tag_of_strengthen : forall e (istr istr' ienv ienv' : aenv) i,
      aenv_le istr istr' -> aenv_le ienv ienv' ->
      tag_of istr ienv e i ->
      tag_of istr' ienv' e i.
  Proof.
    induction e using expr_IH; intros; invert_tag_of.
    all: try now (econstructor; eauto; use_tag_of_strengthen_IH;
                  eauto using aenv_le_step, collection_tag_leb_refl).
    1,2: [> specialize (H0 x) | specialize (H x) ];
    unfold aenv_le_at in *; rewrite_l_to_r; destruct_match_hyp; intuition idtac;
    econstructor; eauto using collection_tag_leb_tran.
    1:{ econstructor; eauto. use_tag_of_strengthen_IH; eauto.
        repeat apply aenv_le_step, collection_tag_leb_refl. auto. }
    1,2: econstructor; lazymatch goal with H: tag_of _ _ _ _ |- _ => clear H end;
        lazymatch goal with H: Forall _ _ |- _ => induction H end; auto;
        invert_Forall; constructor; intuition eauto.
  Qed.

  Lemma aenv_le__istr_inv : forall istr ienv inv c istr_expect,
      well_tagged istr ienv inv c istr_expect ->
      aenv_le istr inv.
  Proof.
    induction 1; auto.
  Qed.

  Ltac use_well_tagged_strengthen_IH :=
    lazymatch goal with
    | |- tag_of _ _ _ _ => eapply tag_of_strengthen
    | IH: context[_ -> well_tagged _ _ _ ?c _] |- well_tagged _ _ _ ?c _ =>
        eapply IH
    end.

  Lemma well_tagged_strengthen : forall c (istr istr' ienv ienv' inv inv' istr_expect : aenv),
      well_tagged istr ienv inv c istr_expect ->
      aenv_le ienv ienv' -> aenv_le istr istr' ->
      aenv_le inv inv' -> aenv_le istr' inv' ->
      well_tagged istr' ienv' inv' c istr_expect.
  Proof.
    induction c; intros.
    all: invert_well_tagged.
    all: try now (econstructor; try use_well_tagged_strengthen_IH;
                  eauto using aenv_le_step, aenv_le__istr_inv,
                    collection_tag_leb_refl, aenv_le_refl, aenv_le_tran).
    econstructor; eauto using aenv_le_at_tran;
      use_well_tagged_strengthen_IH;
      eauto using aenv_le_step, collection_tag_leb_refl, aenv_le_tran.
    eapply aenv_le_step; eauto using aenv_le_tran.
    lazymatch goal with
      H: well_tagged _ _ _ _ _ |- _ => apply aenv_le__istr_inv in H; specialize (H x) end.
    unfold aenv_le_at in *. repeat rewrite_map_get_put_hyp. auto.
  Qed.

  Ltac strengthen_tag_judgements :=
    lazymatch goal with
    | |- tag_of _ _ _ _ => eapply tag_of_strengthen
    | |- well_tagged _ _ _ ?c _ => eapply well_tagged_strengthen
    end.

  Lemma aenv_le_update : forall iG iG' x,
      aenv_le iG iG' ->
      aenv_le iG (map.update iG' x (map.get iG x)).
  Proof.
    unfold aenv_le, aenv_le_at; intros.
    destruct (String.eqb x0 x) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
    1:{ rewrite Properties.map.get_update_same.
        case_match; auto using collection_tag_leb_refl. }
    1:{ specialize (H x0).
        rewrite Properties.map.get_update_diff; auto. }
  Qed.

  Lemma aenv_le_put : forall iG iG' x i i',
      aenv_le iG iG' -> collection_tag_leb i i' = true ->
      aenv_le (map.put iG x i) (map.put iG' x i').
  Proof.
    unfold aenv_le, aenv_le_at; intros.
    destruct_get_put_strings; auto.
    specialize (H x0). repeat destruct_match_hyp; auto.
  Qed.

  Lemma aenv_le_put_back : forall iG iG' x,
      aenv_le iG iG' ->
      aenv_le iG (map.put iG' x (get_collection_tag iG x)).
  Proof.
    unfold aenv_le, aenv_le_at; intros.
    destruct_get_put_strings.
    1: unfold get_collection_tag;
    case_match; auto using collection_tag_leb_refl.
    1: specialize (H x0); case_match; auto.
  Qed.

  Lemma aenv_le_put_inv : forall iG iG' x i,
      map.get iG x = None ->
      aenv_le (map.put iG x i) iG' ->
      aenv_le iG (map.update iG' x None) /\ match map.get iG' x with
                        | Some i' => collection_tag_leb i i' = true
                        | None => False
                        end.
  Proof.
    unfold aenv_le, aenv_le_at; split; intros.
    1:{ specialize (H0 x0); destruct_get_put_strings.
        1: rewrite_l_to_r; auto.
        1: rewrite Properties.map.get_update_diff; auto. }
    1: specialize (H0 x); rewrite_map_get_put_hyp; auto.
  Qed.

  Lemma put_ordered_update_diff : forall iG (x x' : string) i i',
      x <> x' ->
      map.put (ordered_update collection_tag_leb iG x i) x' i' =
        ordered_update collection_tag_leb (map.put iG x' i') x i.
  Proof.
    intros. unfold ordered_update. rewrite_map_get_put_goal.
    repeat case_match; auto.
    all: rewrite Properties.map.put_put_diff; auto.
  Qed.

  Lemma put_ordered_update_same : forall iG (x : string) i i',
      map.put (ordered_update collection_tag_leb iG x i) x i' = map.put iG x i'.
  Proof.
    intros. unfold ordered_update.
    repeat case_match; auto.
    all: rewrite Properties.map.put_put_same; auto.
  Qed.

  Lemma put_lub_merge : forall iG iG' x i,
      map.put (lub_merge iG iG') x i = lub_merge (map.put iG x i) (map.put iG' x i).
  Proof.
    intros. apply map.map_ext; intros.
    rewrite lub_merge_sound.
    destruct_get_put_strings.
    1: case_match; auto.
    rewrite lub_merge_sound; repeat case_match; auto.
  Qed.

  Lemma lub_merge_preserve_aenv_le : forall iG1 iG2 iG3,
      aenv_le iG1 iG3 ->
      aenv_le iG2 iG3 ->
      aenv_le (lub_merge iG1 iG2) iG3.
  Proof.
    unfold aenv_le, aenv_le_at; intros * H1 H2 x.
    rewrite lub_merge_sound. specialize (H1 x). specialize (H2 x).
    repeat case_match; auto.
  Qed.

  Lemma aenv_le_at__aenv_le : forall iG1 iG2 iG3 x,
      aenv_le_at x iG1 iG2 ->
      aenv_le iG2 iG3 ->
      aenv_le_at x iG1 iG3.
  Proof.
    unfold aenv_le; intros. eauto using aenv_le_at_tran.
  Qed.

  Lemma aenv_le__put_LikeList : forall iG x,
      aenv_le iG (map.put iG x LikeList).
  Proof.
    unfold aenv_le, aenv_le_at; intros.
    destruct_get_put_strings; case_match;
      auto using collection_tag_leb_refl.
    destruct c; auto.
  Qed.

  Lemma aenv_le__lub_merge : forall iG1 iG1' iG2 iG2',
      aenv_le iG1 iG1' -> aenv_le iG2 iG2' ->
      aenv_le (lub_merge iG1 iG2) (lub_merge iG1' iG2').
  Proof.
    eauto using lub_merge_preserve_aenv_le,
      aenv_le_tran, lub_merge__aenv_le_l, lub_merge__aenv_le_r.
  Qed.

  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.

  Definition collection_tag_metric (i : collection_tag) : nat :=
    match i with
    | LikeSet => 1
    | LikeBag => 2
    | LikeList => 3
    end.

  Definition aenv_metric : aenv -> nat :=
    map.fold (fun s _ i =>
                collection_tag_metric i + s) 0.

  Lemma collection_tag_leb_metric : forall i i',
      collection_tag_leb i i' = true ->
      collection_tag_metric i <= collection_tag_metric i'.
  Proof.
    destruct i, i'; simpl; auto; congruence.
  Qed.

  Lemma collection_tag_gt_metric : forall i i',
      collection_tag_leb i i' = false ->
      S (collection_tag_metric i') <= collection_tag_metric i.
  Proof.
    destruct i, i'; simpl; auto; congruence.
  Qed.

  Lemma collection_tag_leb_lub : forall i i',
      collection_tag_leb i (collection_tag_lub i i') = true.
  Proof.
    destruct i, i'; simpl; auto.
  Qed.

  Lemma collection_tag_lub_leb : forall i1 i2 i3,
      collection_tag_leb i1 i3 = true ->
      collection_tag_leb i2 i3 = true ->
      collection_tag_leb (collection_tag_lub i1 i2) i3 = true.
  Proof.
    destruct i1, i2, i3; simpl; auto.
  Qed.

  Lemma tag_req_times_sound' : forall e x n i i' istr ienv,
      tag_req_times (fun i => tag_req i e) x i n = i' ->
      tag_req i' e = (istr, ienv) ->
      collection_tag_leb i i' = true /\
        (collection_tag_leb (get_collection_tag ienv x) i' = true \/
          collection_tag_metric i + n <= collection_tag_metric i').
  Proof.
    induction n; simpl; intros.
    1:{ subst. intuition auto using collection_tag_leb_refl.
        right. destruct i'; simpl; auto. }
    1:{ repeat destruct_match_hyp.
        1:{ subst. rewrite_l_to_r; invert_pair.
            intuition auto using collection_tag_leb_refl. }
        1:{ eapply IHn in H; eauto. split;
            intuition eauto using collection_tag_leb_neg, collection_tag_leb_tran.
            right. apply collection_tag_gt_metric in E0.
            rewrite <- Nat.add_succ_comm.
            eauto using le_trans, Plus.plus_le_compat_r_stt. } }
  Qed.

  Lemma tag_req_times_sound : forall e x i i' istr ienv,
      tag_req_times (fun i => tag_req i e) x i 3 = i' ->
      tag_req i' e = (istr, ienv) ->
      collection_tag_leb i i' = true /\
        collection_tag_leb (get_collection_tag ienv x) i' = true.
  Proof.
    intros. eapply tag_req_times_sound' in H; intuition eauto.
    destruct i, i'; simpl in *;
      repeat lazymatch goal with
          H: _ <= _ |- _ => inversion H; subst; clear H end.
  Qed.

  Lemma collection_tag_lub_comm : forall i i',
      collection_tag_lub i i' = collection_tag_lub i' i.
  Proof.
    destruct i, i'; auto.
  Qed.

  Ltac use_tag_req_sound_IH :=
    lazymatch goal with
      IH: context[tag_of _ _ ?e _], H: tag_req _ ?e = _ |- _ =>
        apply IH in H end.

  Lemma tag_req_sound : forall e i istr ienv,
      tag_req i e = (istr, ienv) ->
      tag_of istr ienv e i.
  Proof.
    induction e using expr_IH.
    9:{ cbn [tag_req]; intros.
        repeat (destruct_match_hyp; []); invert_pair.
        remember (tag_req_times
                    (fun i : collection_tag => tag_req i e3) y i 3) as i'.
        symmetry in Heqi'; eapply tag_req_times_sound in Heqi';
          intuition eauto.
        repeat use_tag_req_sound_IH.
        econstructor; try strengthen_tag_judgements.
        8: eauto.
        10: eapply tag_of_weaken with (i:=(collection_tag_lub i (get_collection_tag r2 y))); [ | eauto ].
        all: eauto using collection_tag_leb_refl, collection_tag_leb_lub, collection_tag_lub_leb.
        all: eauto using  aenv_le_tran, lub_merge__aenv_le_l,
            lub_merge__aenv_le_r, aenv_le_update.
        destruct_String_eqb x y.
        1:{ rewrite Properties.map.put_put_same, !put_update_same; auto.
            eapply aenv_le_tran;
              [ | eapply aenv_le_put;
                  eauto using lub_merge__aenv_le_r;
                  rewrite collection_tag_lub_comm;
                  eapply collection_tag_leb_lub ].
            apply aenv_le_put_back; auto using aenv_le_refl. }
        1:{ repeat rewrite Properties.map.put_put_diff, put_update_same; auto.
            eapply aenv_le_tran;
              [ | eapply aenv_le_put;
                  eauto using aenv_le__put_LikeList;
                  rewrite collection_tag_lub_comm;
                  eapply collection_tag_leb_lub ].
            eauto using aenv_le_tran, aenv_le_put, lub_merge__aenv_le_r, collection_tag_leb_refl, aenv_le_put_back, aenv_le_refl. } }
    all: simpl; intros.
    all: try (invert_pair; econstructor; eauto using collection_tag_leb_refl;
              rewrite_map_get_put_goal; auto).
    all: repeat (destruct_match_hyp; []); invert_pair;
      repeat use_tag_req_sound_IH.
    all: try now (econstructor; try strengthen_tag_judgements; eauto;
                  repeat rewrite put_update_same;
                  eauto using aenv_le_update, aenv_le_put_back,
                    aenv_le_tran, aenv_le__put_LikeList,
                    lub_merge__aenv_le_l, lub_merge__aenv_le_r).
    1:{ generalize dependent istr; generalize dependent ienv.
        induction l; simpl in *.
        1: constructor; auto.
        repeat constructor; invert_Forall;
          repeat (destruct_match_hyp; invert_pair); use_tag_req_sound_IH.
        1:{ strengthen_tag_judgements; eauto; eauto using lub_merge__aenv_le_l. }
        1:{ lazymatch goal with
            IH: ?x -> _, H: ?x |- _ =>
              eapply IH in H; eauto; inversion H; subst end.
            rewrite Forall_forall; intros. apply_Forall_In.
            eapply tag_of_strengthen; eauto; eauto using lub_merge__aenv_le_r. } }
    1: constructor; auto.
    1:{ generalize dependent istr; generalize dependent ienv.
        induction l; simpl in *.
        1: constructor; auto.
        repeat constructor; invert_Forall;
          repeat (destruct_match_hyp; invert_pair); repeat use_tag_req_sound_IH.
        1:{ strengthen_tag_judgements; eauto; eauto using aenv_le_tran, lub_merge__aenv_le_l. }
        all: repeat lazymatch goal with
            IH: ?x -> _, H: ?x |- _ =>
              eapply IH in H; eauto; inversion H; subst end.
        2: rewrite Forall_forall; intros; apply_Forall_In; intuition idtac.
        all: eapply tag_of_strengthen; eauto;
          eauto using aenv_le_tran, lub_merge__aenv_le_l, lub_merge__aenv_le_r. }
    1:{ econstructor; try strengthen_tag_judgements; eauto;
                  eauto using aenv_le_update, aenv_le_tran,
          lub_merge__aenv_le_l, lub_merge__aenv_le_r.
        destruct_String_eqb k v; destruct_String_eqb v acc; try destruct_String_eqb k acc.
        all: repeat (lazymatch goal with
        | |- context[map.put (map.put _ ?x _) ?x _] => rewrite Properties.map.put_put_same
        | |- context[map.put (map.update _ ?x _) ?x _] => rewrite put_update_same
        | |- context[map.put (map.update _ ?x _) _ _] => rewrite Properties.map.put_put_diff with (k2:=x)
        end; auto); eauto using aenv_le_tran, aenv_le__put_LikeList, lub_merge__aenv_le_r. }
    1:{ constructor; try strengthen_tag_judgements; eauto.
        all: eauto using aenv_le_update, aenv_le_tran,
            lub_merge__aenv_le_l, lub_merge__aenv_le_r.
        all: destruct_String_eqb x y;
          [ rewrite Properties.map.put_put_same, !put_update_same
          | repeat rewrite Properties.map.put_put_diff, put_update_same ]; eauto using aenv_le_tran, lub_merge__aenv_le_l, lub_merge__aenv_le_r, aenv_le__put_LikeList. }
  Qed.

  Lemma aenv_le__lub_merge_absorb : forall iG iG',
      aenv_le iG iG' -> lub_merge iG iG' = iG'.
  Proof.
    intros. apply map.map_ext; intros.
    rewrite lub_merge_sound. specialize (H k).
    unfold aenv_le_at in *. repeat case_match; intuition idtac.
    f_equal; auto using collection_tag_leb_antisym.
  Qed.

  Ltac use_tag_req_domain_IH :=
    lazymatch goal with
      IH: context[type_of _ _ ?e _ -> _], H: type_of _ _ ?e _ |- _ =>
        eapply IH in H; [ | eauto ] end.

  Lemma lub_merge__domain_incl : forall {vt : Type} {m : map.map string vt}
                                        iG iG' (G : m),
      domain_incl iG G -> domain_incl iG' G ->
      domain_incl (lub_merge iG iG') G.
  Proof.
    unfold domain_incl; intros.
    specialize (H x). specialize (H0 x).
    rewrite lub_merge_sound.
    repeat destruct_match_hyp; intuition idtac.
  Qed.

  Lemma tag_req_domain : forall e Gstore Genv t i istr ienv,
                   type_of Gstore Genv e t -> tag_req i e = (istr, ienv) ->
                   domain_incl istr Gstore.
  Proof.
    induction e using expr_IH; simpl; intros; invert_pair; invert_type_of.
    1,3: try apply domain_incl_empty.
    1:{ unfold domain_incl; intros.
        destruct_get_put_strings;
          [ rewrite_l_to_r | rewrite map.get_empty ]; auto. }
    1: use_tag_req_domain_IH; auto.
    all: try now (repeat destruct_match_hyp; repeat invert_pair2;
                  repeat use_tag_req_domain_IH; auto using lub_merge__domain_incl).
    1:{ lazymatch goal with
        H1: type_of _ _ (ERecord _) _, H2: List.map fst _ = _,
            H3: Permutation _ _, H4: NoDup _, H5: Sorted.StronglySorted _ _ |- _ =>
          clear H1 H2 H3 H4 H5 end.
        generalize dependent istr. generalize dependent ienv.
        generalize dependent tl.
        lazymatch goal with
          H: Forall _ _ |- _ => induction H end;
        simpl in *; intros.
        1: invert_pair2; apply domain_incl_empty.
        repeat destruct_match_hyp; repeat invert_pair2.
        invert_Forall2.
        destruct tl; try discriminate. simpl in *. invert_cons.
        use_tag_req_domain_IH; auto.
        lazymatch goal with
          H: context[Forall2 _ _ _ -> _], H': Forall2 _ _ _ |- _ =>
            eapply H in H' end; [ | eauto ].
        auto using lub_merge__domain_incl. }
    1:{ lazymatch goal with
        H: type_of _ _ (EDict _) _ |- _ => clear H end.
        generalize dependent istr. generalize dependent ienv.
        lazymatch goal with
        H: Forall _ _ |- _ => induction H end; simpl in *; intros.
        1: invert_pair2; apply domain_incl_empty.
        repeat destruct_match_hyp; repeat invert_pair2.
        invert_Forall.
        lazymatch goal with
          H: context[Forall _ _ -> _], H': Forall _ _ |- _ =>
            eapply H in H' end; [ | eauto ].
        intuition idtac. repeat use_tag_req_domain_IH.
        auto using lub_merge__domain_incl. }
  Qed.

  Lemma domain_incl__lub_merge_r : forall (G1 G2 : aenv),
      domain_incl G2 (lub_merge G1 G2).
  Proof.
    unfold domain_incl; intros.
    rewrite lub_merge_sound.
    repeat case_match; auto.
  Qed.

  Lemma domain_incl__lub_merge_domain_eq : forall (G1 G2 : aenv),
      domain_incl G1 G2 -> domain_eq G2 (lub_merge G1 G2).
  Proof.
    unfold domain_eq. split;
      eauto using domain_incl__lub_merge_r,
      domain_incl_refl, lub_merge__domain_incl.
  Qed.

  Lemma domain_eq__domain_incl_l : forall {vt1 vt2 : Type} {m1 : map.map string vt1}
                                        {m2 : map.map string vt2} (G1 G1' : m1) (G2 : m2),
      domain_eq G1 G1' -> domain_incl G1 G2 ->
      domain_incl G1' G2.
  Proof.
    unfold domain_eq; intuition eauto using domain_incl_tran.
  Qed.

  Lemma domain_eq__domain_incl_r : forall {vt1 vt2 : Type} {m1 : map.map string vt1}
                                        {m2 : map.map string vt2} (G1 : m1) (G2 G2' : m2),
      domain_eq G2 G2' -> domain_incl G1 G2 ->
      domain_incl G1 G2'.
  Proof.
    unfold domain_eq; intuition eauto using domain_incl_tran.
  Qed.

  Lemma domain_incl_step : forall (Gstore : tenv) (istr : aenv) y t i,
      domain_incl Gstore istr -> domain_incl (map.put Gstore y t) (map.put istr y i).
  Proof.
    unfold domain_incl; intros.
    specialize (H x). destruct_get_put_strings;
      repeat rewrite_map_get_put_goal; trivial.
  Qed.

  Lemma domain_eq_put_update : forall {vt : Type} {m : map.map string vt}
                                      {m_ok : map.ok m} (G G' : m) x i,
      domain_eq (map.put G x i) G' ->
                  domain_eq G (map.update G' x (map.get G x)).
  Proof.
    unfold domain_eq, domain_incl; intuition idtac.
    all: [> specialize (H0 x0)
         | specialize (H1 x0) ];
      destruct_get_update_strings;
      rewrite_map_get_put_hyp; case_match; auto.
  Qed.

  Lemma domain_incl_step_r : forall {vt : Type} {m : map.map string vt}
                                   {m_ok : map.ok m} (G : m) x v,
      domain_incl G (map.put G x v).
  Proof.
    unfold domain_incl; intros.
    destruct_get_put_strings; case_match; auto.
  Qed.

  Lemma in_domain_eq : forall {vt : Type} {m : map.map string vt}
                                   {m_ok : map.ok m} (G : m) x v,
      match map.get G x with
      | Some _ => True | None => False end ->
      domain_eq G (map.put G x v).
  Proof.
    unfold domain_eq, domain_incl; intuition idtac.
    all: destruct_get_put_strings; case_match; auto.
  Qed.

  Ltac specialize_forall_string :=
    lazymatch goal with
      H: forall _, _, x : string |- _ => specialize (H x) end.

  Lemma domain_eq__lub_merge : forall (G1 G2 G3 : aenv),
      domain_eq G1 G2 -> domain_eq G1 G3 ->
      domain_eq G1 (lub_merge G2 G3).
  Proof.
    unfold domain_eq, domain_incl; intuition idtac; intros.
    all: repeat specialize_forall_string.
    all: rewrite lub_merge_sound; repeat case_match; auto.
  Qed.

  Ltac apply_tag_req_domain :=
          lazymatch goal with
            H: tag_req _ _ = _ |- _ =>
              eapply tag_req_domain in H
          end.

  Ltac invert_res :=
    lazymatch goal with
      H: mk_res _ _ _ = mk_res _ _ _ |- _ => inversion H; subst end.

  Ltac use_command_tag_req_preserve_domain_IH' c :=
    lazymatch goal with
          IH: context[command_tag_req _ c = _ -> _],
            H: command_tag_req _ c = _ |- _ =>
            eapply IH in H; [ | eauto .. ] end.

  Ltac use_command_tag_req_preserve_domain_IH :=
    lazymatch goal with
      IH: context[command_tag_req _ ?c = _ -> _],
        H: command_tag_req _ ?c = _ |- _ =>
        use_command_tag_req_preserve_domain_IH' c end.

  Lemma command_tag_req_times_preserve_domain' : forall Gstore Genv c n istr_expect istr,
      well_typed Gstore Genv c ->
      command_tag_req_times (fun istr => command_tag_req istr c) istr_expect n = istr ->
      domain_incl Gstore istr_expect ->
      (forall istr_expect res istr,
          command_tag_req istr_expect c = res -> istr = istr_res res ->
          domain_incl Gstore istr_expect -> domain_eq istr_expect istr) ->
      domain_eq istr_expect istr.
  Proof.
    induction n; simpl; intros; subst.
    1: apply domain_eq_refl.
    repeat case_match; simpl; auto using domain_eq_refl.
    eapply domain_eq_tran.
    2: eapply IHn; eauto using domain_incl_tran, domain_incl__lub_merge_r.
    eauto using domain_eq__lub_merge, domain_eq_refl.
  Qed.

  Lemma domain_eq__domain_incl : forall (G G' : aenv),
      domain_eq G G' -> domain_incl G G'.
  Proof.
    unfold domain_eq; intuition idtac.
  Qed.

  Lemma command_tag_req_preserve_domain : forall c res Gstore Genv istr_expect istr,
      well_typed Gstore Genv c ->
      command_tag_req istr_expect c = res ->
      istr = istr_res res ->
      domain_incl Gstore istr_expect ->
      domain_eq istr_expect istr.
  Proof.
    induction c; simpl; intros; subst; auto.
    all: invert_well_typed.
    all: repeat case_match; simpl.
    1: unfold domain_eq; auto using domain_incl_refl.
    1:{ use_command_tag_req_preserve_domain_IH' c2;
          use_command_tag_req_preserve_domain_IH' c1;
          unfold domain_eq in *; intuition eauto using domain_incl_tran. }
    1:{ use_command_tag_req_preserve_domain_IH; simpl in *.
        apply_tag_req_domain; eauto using domain_eq_tran,
          domain_incl__lub_merge_domain_eq,
          domain_eq__domain_incl_r, domain_incl_tran. }
    1:{ use_command_tag_req_preserve_domain_IH; simpl in *;
        auto using domain_incl_step.
        apply_tag_req_domain; eauto.
        eapply domain_eq_tran.
        1: eapply domain_eq_put_update; eauto.
        eapply domain_incl__lub_merge_domain_eq.
        eapply domain_eq__domain_incl_r; eauto using domain_incl_tran.
        eapply domain_eq_put_update; eauto. }
    1:{ apply_tag_req_domain; eauto.
        eapply domain_eq_tran.
        1:{ specialize (H2 x). rewrite_l_to_r.
            eapply in_domain_eq; eauto. }
        1:{ rewrite lub_merge_comm. eapply domain_incl__lub_merge_domain_eq.
            eapply domain_incl_tran; eauto.
            eapply domain_incl_tran; eauto. eapply domain_incl_step_r. } }
    1:{ repeat use_command_tag_req_preserve_domain_IH; simpl in *.
        apply_tag_req_domain; eauto.
        unfold domain_eq in *.
        eapply domain_eq_tran.
        2:{ apply domain_incl__lub_merge_domain_eq.
            unfold domain_eq in *; intuition eauto using domain_incl_tran, domain_incl__lub_merge_r. }
        auto using domain_eq__lub_merge. }
    1:{ remember (command_tag_req_times
                    (fun istr : aenv => command_tag_req istr c) istr_expect
                    (size_of_map istr_expect + (size_of_map istr_expect + 0) + 1)) as istr'.
        symmetry in Heqistr'.
        eapply command_tag_req_times_preserve_domain' in Heqistr'; eauto.
        use_command_tag_req_preserve_domain_IH; simpl in *;
          [ | unfold domain_eq in *;
              intuition eauto using domain_incl_tran,
                domain_incl__lub_merge_r ].
        apply domain_eq__lub_merge; eauto using domain_eq_refl.
        eapply domain_eq_tran, domain_incl__lub_merge_domain_eq.
        1: eauto using domain_eq_tran.
        apply_tag_req_domain; eauto.
        unfold domain_eq in *.
        intuition eauto using domain_incl_tran,
          domain_incl__lub_merge_r. }
  Qed.

  Lemma command_tag_req_times_preserve_domain : forall Gstore Genv c n istr_expect istr,
      well_typed Gstore Genv c ->
      command_tag_req_times (fun istr => command_tag_req istr c) istr_expect n = istr ->
      domain_incl Gstore istr_expect ->
      domain_eq istr_expect istr.
  Proof.
    intros. eapply command_tag_req_times_preserve_domain';
      eauto using command_tag_req_preserve_domain.
  Qed.

  Lemma aenv_le_antisym : forall iG iG',
      aenv_le iG iG' -> aenv_le iG' iG -> iG = iG'.
  Proof.
    unfold aenv_le, aenv_le_at; intros. apply map.map_ext; intros.
    repeat specialize_forall_string.
    repeat destruct_match_hyp; f_equal;
      intuition auto using collection_tag_leb_antisym.
  Qed.

  Lemma aenv_metric__ge_size_of_map : forall (iG : aenv), aenv_metric iG >= size_of_map iG.
  Proof.
    unfold aenv_metric, collection_tag_metric, size_of_map; intros.
    apply map.fold_spec; simpl; intros.
    1: rewrite Properties.map.fold_empty; auto.
    rewrite Properties.map.fold_put; simpl; auto.
    destruct v; eauto using le_n_S, Nat.le_le_succ_r.
  Qed.

  Lemma aenv_metric__le_3_size_of_map : forall (iG : aenv), aenv_metric iG <= 3 * size_of_map iG.
  Proof.
    unfold aenv_metric, collection_tag_metric, size_of_map; intros.
    apply map.fold_spec; simpl; intros.
    1: rewrite Properties.map.fold_empty; auto.
    rewrite Properties.map.fold_put; simpl; auto.
    rewrite !Nat.add_succ_r.
    lazymatch goal with
      |- context[_ <= S (S (S ?n))] => change (S (S (S n))) with (3 + n) end.
    apply Nat.add_le_mono; auto.
    destruct v; auto.
  Qed.

  Lemma domain_incl_empty_r : forall (G : aenv),
      domain_incl G (map.empty (map:=aenv)) -> G = map.empty.
  Proof.
    unfold domain_eq, domain_incl; intuition idtac.
    apply map.map_ext; intros. specialize_forall_string.
    rewrite map.get_empty in *. destruct_match_hyp; intuition idtac.
  Qed.

  Lemma aenv_le__domain_incl : forall G G',
      aenv_le G G' -> domain_incl G G'.
  Proof.
    unfold aenv_le, aenv_le_at, domain_incl; intros.
    specialize_forall_string.
    repeat case_match; auto.
  Qed.

  Lemma domain_eq__size_of_map : forall (G G' : aenv),
      domain_eq G G' -> size_of_map G = size_of_map G'.
    unfold size_of_map; intro. apply map.fold_spec; intros.
    1:{ unfold domain_eq in *; intuition idtac.
        apply domain_incl_empty_r in H1; subst.
        rewrite Properties.map.fold_empty; trivial. }
    1:{ assert(exists v', map.get G' k = Some v').
        { unfold domain_eq, domain_incl in *; intuition idtac.
          repeat specialize_forall_string. repeat rewrite_map_get_put_hyp.
          destruct_match_hyp; intuition eauto. }
        lazymatch goal with H: exists _, _ |- _ => destruct H; subst end.
      apply domain_eq_put_update, H0 in H1.
        replace G' with (map.put (map.update G' k (map.get m k)) k x).
        1:{ rewrite Properties.map.fold_put; auto.
            rewrite Properties.map.get_update_same; auto. }
        rewrite put_update_same; auto. apply Properties.map.put_noop; auto. }
  Qed.

  Lemma get_None__aenv_metric_put : forall iG x i,
      map.get iG x = None ->
      aenv_metric (map.put iG x i) = aenv_metric iG + collection_tag_metric i.
  Proof.
    unfold aenv_metric; intro; apply map.fold_spec; intros.
    1: rewrite Properties.map.fold_singleton; apply Nat.add_comm.
    destruct_get_put_strings; try congruence.
    rewrite Properties.map.put_put_diff, Properties.map.fold_put; auto.
    1: rewrite H0; auto using Nat.add_assoc.
    1: auto using Nat.add_shuffle3.
    1: rewrite_map_get_put_goal.
  Qed.

  Lemma collection_tag_gt_aenv_metric : forall iG x i i',
      map.get iG x = Some i ->
      collection_tag_leb i' i = false ->
      S (aenv_metric iG) <= aenv_metric (map.put iG x i').
  Proof.
    intros.
    replace iG with (map.put (map.update iG x None) x i).
    2:{ rewrite put_update_same; auto.
        apply Properties.map.put_noop; auto. }
    rewrite Properties.map.put_put_same.
    rewrite !get_None__aenv_metric_put.
    2,3: rewrite Properties.map.get_update_same; reflexivity.
    rewrite <- Nat.add_1_r, <- Nat.add_assoc.
    apply Plus.plus_le_compat_l_stt.
    destruct i, i'; simpl; try discriminate; auto.
  Qed.

  Lemma aenv_gtb_exists : forall iG iG',
      aenv_leb iG iG' = false ->
      exists x, ~ aenv_le_at x iG iG'.
  Proof.
    unfold aenv_leb; intros *; apply map.fold_spec; intros;
      try congruence.
    destruct_match_hyp.
    1:{ destruct r; simpl in *.
        1:{ exists k. unfold aenv_le_at. rewrite_map_get_put_goal.
            rewrite E; congruence. }
        1:{ intuition idtac. destruct_exists. exists x.
            unfold aenv_le_at in *.
            assert(x <> k).
            { intro contra; subst. rewrite_l_to_r; intuition fail. }
            rewrite_map_get_put_goal. } }
    1:{ exists k. unfold aenv_le_at. rewrite_map_get_put_goal.
        rewrite E; auto. }
  Qed.

  Lemma domain_incl__aenv_gt_exists : forall iG iG',
      domain_incl iG iG' ->
      ~ aenv_le iG iG' ->
      exists x i i', map.get iG x = Some i /\
                       map.get iG' x = Some i' /\
                       collection_tag_leb i i' = false /\
                       aenv_le (map.put iG' x i) (lub_merge iG iG').
  Proof.
    intros * H_incl H.
    rewrite <- aenv_leb_le in H.
    apply Bool.not_true_is_false, aenv_gtb_exists in H.
    destruct_exists. specialize (H_incl x).
    unfold aenv_le_at in *. repeat destruct_match_hyp; intuition idtac.
    apply Bool.not_true_is_false in H.
    repeat eexists; eauto.
    replace (lub_merge iG iG') with (map.put (lub_merge iG iG') x c).
    1: apply aenv_le_put; auto using collection_tag_leb_refl, lub_merge__aenv_le_r.
    apply map.map_ext; intro. destruct_get_put_strings.
    rewrite lub_merge_sound. repeat rewrite_l_to_r.
    rewrite collection_tag_leb_neg; auto.
  Qed.

  Lemma aenv_le__aenv_metric : forall iG iG',
      aenv_le iG iG' -> aenv_metric iG <= aenv_metric iG'.
  Proof.
    unfold aenv_metric; intro. apply map.fold_spec; intros.
    1: apply Nat.le_0_l.
    apply aenv_le_put_inv in H1; auto.
    destruct_match_hyp; intuition idtac.
    replace iG' with (map.put (map.update iG' k None) k c).
    2: rewrite put_update_same, Properties.map.put_noop; auto.
    rewrite Properties.map.fold_put; auto using Nat.add_shuffle3;
      [ | rewrite Properties.map.get_update_same; auto ].
    apply Nat.add_le_mono; auto using collection_tag_leb_metric.
  Qed.

  Lemma domain_incl__aenv_gt_metric : forall iG iG',
      domain_incl iG iG' ->
      ~ aenv_le iG iG' ->
      S (aenv_metric iG') <= aenv_metric (lub_merge iG iG').
  Proof.
    intros. specialize (domain_incl__aenv_gt_exists _ _ H H0) as H_exists.
    repeat destruct_exists; intuition idtac.
    eapply le_trans.
    2: apply aenv_le__aenv_metric; eauto.
    eauto using collection_tag_gt_aenv_metric.
  Qed.

  Lemma command_tag_req_times_sound' : forall Gstore Genv c n istr_expect res istr',
      well_typed Gstore Genv c ->
      domain_incl Gstore istr_expect ->
      command_tag_req_times (fun istr => command_tag_req istr c) istr_expect n = istr' ->
      command_tag_req istr' c = res ->
      aenv_le istr_expect istr' /\
        (aenv_le (istr_res res) istr' \/
           aenv_metric istr' >= n + aenv_metric istr_expect).
  Proof.
    induction n; simpl; intros; subst.
    1: intuition auto using aenv_le_refl.
    repeat case_match; simpl.
    1:{ intuition auto using aenv_le_refl. rewrite_l_to_r; simpl.
        left; apply aenv_leb_le; assumption. }
    1:{ eapply IHn with (istr_expect:=lub_merge istr_res0 istr_expect) in H as H'.
        3,4: reflexivity.
        2: eauto using domain_incl_tran, domain_incl__lub_merge_r.
        intuition eauto using aenv_le_tran, lub_merge__aenv_le_r.
        right. eapply le_trans; [ | eauto ].
        eapply command_tag_req_preserve_domain in E; eauto; simpl in *.
        rewrite <- Nat.add_succ_r. apply Plus.plus_le_compat_l_stt.
        eapply le_trans; [ apply Nat.le_refl | apply domain_incl__aenv_gt_metric ].
        1: unfold domain_eq in *; intuition eauto.
        1: intro contra; rewrite <- aenv_leb_le in *; congruence. }
  Qed.

  Lemma command_tag_req_times_sound : forall (Gstore Genv : tenv) istr_expect c istr' res,
      well_typed Gstore Genv c ->
      domain_incl Gstore istr_expect ->
      command_tag_req_times (fun istr => command_tag_req istr c) istr_expect
        (Nat.mul 2 (size_of_map istr_expect) + 1) = istr' ->
      command_tag_req istr' c = res ->
      aenv_le istr_expect istr' /\ aenv_le (istr_res res) istr'.
  Proof.
    intros.
    eapply command_tag_req_times_preserve_domain in H1 as H_eq; eauto.
    apply domain_eq__size_of_map in H_eq.
    eapply command_tag_req_times_sound' in H1; intuition eauto.
    specialize (aenv_metric__le_3_size_of_map istr') as H_ub.
    eapply le_trans in H1;
      [ | apply add_le_mono_l_proj_l2r, aenv_metric__ge_size_of_map ].
    rewrite Nat.add_comm, Nat.add_assoc in H1.
    eapply le_trans in H_ub; eauto.
    repeat rewrite_l_to_r. rewrite Nat.add_1_r in H_ub.
    simpl in *. apply Nat.nle_succ_diag_l in H_ub. intuition fail.
  Qed.

  Ltac use_command_tag_req_sound_IH :=
    lazymatch goal with
      | H: tag_req _ _ = _ |- _ => apply tag_req_sound in H
      | IH: context[well_tagged _ _ _ ?c _], H: command_tag_req _ ?c = _ |- well_tagged _ _ _ _ _ =>
        eapply IH in H
    end.

  Lemma command_tag_req_sound : forall c Gstore Genv istr_expect istr ienv inv,
      well_typed Gstore Genv c ->
      domain_incl Gstore istr_expect ->
      command_tag_req istr_expect c = mk_res istr ienv inv ->
      well_tagged istr ienv inv c istr_expect.
  Proof.
    induction c; simpl; intros.
    all: repeat destruct_match_hyp; invert_well_typed.
    all: invert_res.
    1: constructor; apply aenv_le_refl.
    1:{ eapply command_tag_req_preserve_domain in E as H_dom; eauto; simpl in *.
        repeat use_command_tag_req_sound_IH; eauto.
        2: unfold domain_eq in *; intuition eauto using domain_incl_tran.
        econstructor; strengthen_tag_judgements;
    eauto using aenv_le_refl, aenv_le__istr_inv, aenv_le_tran,
          lub_merge__aenv_le_l, lub_merge__aenv_le_r. }
    1:{ repeat use_command_tag_req_sound_IH; eauto. econstructor; strengthen_tag_judgements; eauto.
       all: eauto using aenv_le_refl, aenv_le__istr_inv, aenv_le_tran,
           lub_merge__aenv_le_l, lub_merge__aenv_le_r, aenv_le_update,
           lub_merge_preserve_aenv_le.
       rewrite put_update_same; auto using aenv_le_put_back, lub_merge__aenv_le_r. }
    1:{ repeat use_command_tag_req_sound_IH; eauto using domain_incl_step.
        econstructor; try strengthen_tag_judgements; eauto.
        all: eauto using aenv_le_refl, aenv_le__istr_inv, aenv_le_tran,
            lub_merge__aenv_le_l, lub_merge__aenv_le_r,
            lub_merge_preserve_aenv_le, aenv_le_update_step.
        all: try rewrite !put_lub_merge, !put_update_same; auto.
        1,2: eauto using lub_merge__aenv_le_r, aenv_le_tran, aenv_le_refl, aenv_le_put_back.
        1: apply aenv_le__lub_merge; eauto using aenv_le_put,
          aenv_le_refl, aenv_le__istr_inv, aenv_le__collection_tag_leb.
        1:{ eapply aenv_le_at__aenv_le; eauto using lub_merge__aenv_le_r.
            unfold aenv_le_at. rewrite Properties.map.get_update_same.
            case_match; auto using collection_tag_leb_refl. } }
    1:{ repeat use_command_tag_req_sound_IH; eauto.
        constructor; try strengthen_tag_judgements; eauto.
        all: eauto using aenv_le_refl, aenv_le__istr_inv, aenv_le_tran,
      lub_merge__aenv_le_l, lub_merge__aenv_le_r.
        rewrite put_lub_merge, Properties.map.put_put_same.
        eauto using aenv_le_tran, lub_merge__aenv_le_l, aenv_le__put_LikeList. }
    1:{ repeat use_command_tag_req_sound_IH; eauto.
        constructor; strengthen_tag_judgements; eauto.
        all: eauto using aenv_le_refl, aenv_le__istr_inv, aenv_le_tran,
            lub_merge__aenv_le_l, lub_merge__aenv_le_r, aenv_le__lub_merge. }
    1:{ eapply command_tag_req_times_sound in H6 as H_times; eauto.
        simpl in *; remember (command_tag_req_times (fun istr : aenv => command_tag_req istr c) istr_expect
            (size_of_map istr_expect + (size_of_map istr_expect + 0) + 1)) as istr'.
        repeat use_command_tag_req_sound_IH; eauto.
        2: eauto using domain_incl_tran, domain_eq__domain_incl,
            command_tag_req_times_preserve_domain. clear_refl.
        intuition idtac. eapply lub_merge_preserve_aenv_le in H1 as H_merge; eauto.
        econstructor; try strengthen_tag_judgements.
        7: eapply well_tagged_weaken; eauto.
        all: eauto.
        6: rewrite put_update_same; eauto using aenv_le_tran, lub_merge__aenv_le_r, aenv_le__put_LikeList.
        all: eauto using aenv_le_refl, aenv_le__istr_inv, lub_merge__aenv_le_l,
            lub_merge__aenv_le_r, aenv_le__lub_merge, aenv_le_update.
        1,4: rewrite lub_merge_comm.
        all: eauto using aenv_le_refl, aenv_le__istr_inv, aenv_le_tran,
            lub_merge__aenv_le_l, lub_merge__aenv_le_r,
            aenv_le__lub_merge, aenv_le_update. }
  Qed.

  Section WithWord.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Notation value := (value (word:=word)).
    Context {locals: map.map string value} {locals_ok: map.ok locals}.

    Definition consistent (i : collection_tag) (v1 v2 : value) : Prop :=
      match i with
      | LikeSet => match v1 with
                   | VList v1 =>
                       match v2 with
                       | VList v2 => Permutation (List.dedup value_eqb v1) (List.dedup value_eqb v2)
                       | _ => False
                       end
                   | _ => v1 = v2
                   end
      | LikeBag => match v1 with
                   | VList v1 =>
                       match v2 with
                       | VList v2 => Permutation v1 v2
                       | _ => False
                       end
                   | _ => v1 = v2
                   end
      | LikeList => v1 = v2
      end.

    Lemma consistent_step : forall i1 i2 v v',
        consistent i2 v v' ->
        collection_tag_leb i1 i2 = true ->
        consistent i1 v v'.
    Proof.
      destruct i1, i2; simpl in *; try discriminate; intros; auto.
      all: repeat case_match; try discriminate; auto.
      1:{ apply NoDup_Permutation. 1,2: apply (@List.NoDup_dedup _ _ value_eqb_dec).
          intro; split; intro.
          all: rewrite <- (@List.dedup_preserves_In _ _ value_eqb_dec).
          2: apply Permutation_sym in H.
          all: eapply Permutation_in; eauto using dedup_In. }
      1,2: do_injection; apply Permutation_refl.
    Qed.

    Lemma consistent_refl : forall i v, consistent i v v.
    Proof.
      unfold consistent; intros. repeat case_match; auto.
    Qed.

    Lemma consistent_sym : forall i v v', consistent i v v' -> consistent i v' v.
    Proof.
      unfold consistent; intros.
      repeat destruct_match_hyp; intuition idtac; subst; try congruence.
      all: auto using Permutation_sym.
    Qed.

    Lemma consistent_tran' : forall i v1 v2 v3,
        consistent i v1 v2 -> consistent i v2 v3 ->
        consistent i v1 v3.
    Proof.
      intros. unfold consistent in *.
      repeat destruct_match_hyp; intuition auto; try congruence.
      all: rewrite H; auto.
    Qed.

    Lemma consistent_tran : forall i1 i2 i3 v1 v2 v3,
        consistent i1 v1 v2 -> consistent i2 v2 v3 ->
        collection_tag_leb i3 i1 = true ->
        collection_tag_leb i3 i2 = true ->
        consistent i3 v1 v3.
    Proof.
      intros. eauto using consistent_tran', consistent_step.
    Qed.

    Lemma consistent_LikeList_eq : forall v v', consistent LikeList v v' <-> v = v'.
    Proof.
      split; auto.
    Qed.

    Lemma consistent__type_of_value : forall t i v1 v2, consistent i v1 v2 -> type_of_value v1 t -> type_of_value v2 t.
    Proof.
      intros. destruct i; simpl in *; subst; auto.
      1:{ destruct_match_hyp; subst; auto.
          destruct_match_hyp; intuition auto.
          invert_type_of_value. constructor. rewrite Forall_forall; intros.
          assert (In x l).
          { pose proof value_eqb_dec. rewrite List.dedup_preserves_In.
            rewrite H. rewrite <- List.dedup_preserves_In. auto. }
          apply_Forall_In. }
      1:{ destruct_match_hyp; subst; auto.
          destruct_match_hyp; intuition auto.
          invert_type_of_value. constructor.
          rewrite Forall_forall; intros.
          rewrite <- H in H1. apply_Forall_In. }
    Qed.

    Section WithRelMap.
      Context {rel_map : map.map string (value -> value -> Prop)} {rel_map_ok : map.ok rel_map }.

      Definition lifted_related (mR : option (value -> value -> Prop)) (mv mv' : option value) : Prop :=
        match mv with
        | Some v => match mv' with
                    | Some v' => match mR with
                                 | Some R => R v v'
                                 | None => True
                                 end
                    | None => False
                    end
        | None => mv' = None
        end.

      Definition locals_related (Renv : rel_map) (l l' : locals) :=
        forall x, lifted_related (map.get Renv x) (map.get l x) (map.get l' x).

      Lemma locals_related_step : forall (Renv : rel_map) R l l' x v v',
          locals_related Renv l l' ->
          R v v' ->
          locals_related (map.put Renv x R) (map.put l x v) (map.put l' x v').
      Proof.
        unfold locals_related; intros.
        destruct_get_put_strings; auto.
      Qed.

      Definition rel_refl {A} (R : A -> A -> Prop) : Prop :=
        forall x, R x x.

      Lemma locals_related_refl : forall Renv,
          (forall x R, map.get Renv x = Some R -> rel_refl R) ->
          forall l, locals_related Renv l l.
      Proof.
        unfold locals_related, lifted_related; intros.
        repeat case_match; auto.
        apply H in E0; auto.
      Qed.

      Definition consistent_Renv (ienv : aenv) : rel_map :=
        mmap consistent ienv.

      Lemma consistent_Renv_sound : forall ienv x,
          map.get (consistent_Renv ienv) x =
            match map.get ienv x with
            | Some i => Some (consistent i)
            | None => None
            end.
      Proof.
        unfold consistent_Renv; intros. unfold mmap. apply map.fold_spec.
        1: rewrite !map.get_empty; auto.
        intros. destruct_get_put_strings; auto.
      Qed.

      Lemma locals_related_consistent_Renv_refl : forall iG G,
          locals_related (consistent_Renv iG) G G.
      Proof.
        intros; apply locals_related_refl.
        intros; rewrite consistent_Renv_sound in *.
        destruct_match_hyp; try congruence; do_injection.
        unfold rel_refl; auto using consistent_refl.
      Qed.

      Definition R_le (R R' : option (value -> value -> Prop)) : Prop :=
        forall v v', lifted_related R' v v' -> lifted_related R v v'.

      Definition Renv_le (Renv Renv' : rel_map) : Prop :=
        forall x, R_le (map.get Renv x) (map.get Renv' x).

      Lemma R_le_refl : forall R, R_le R R.
      Proof.
        unfold R_le; intros; auto.
      Qed.

      Lemma R_le_tran : forall R1 R2 R3,
          R_le R1 R2 -> R_le R2 R3 ->
          R_le R1 R3.
      Proof.
        unfold R_le; auto.
      Qed.

      Lemma Renv_le_refl : forall Renv, Renv_le Renv Renv.
      Proof.
        unfold Renv_le; intros. apply R_le_refl.
      Qed.

      Lemma Renv_le_tran : forall Renv1 Renv2 Renv3,
          Renv_le Renv1 Renv2 ->
          Renv_le Renv2 Renv3 ->
          Renv_le Renv1 Renv3.
      Proof.
        unfold Renv_le; intros. eauto using R_le_tran.
      Qed.

      Lemma lifted_related__Renv_le : forall R R' v v',
          R_le R R' -> lifted_related R' v v' -> lifted_related R v v'.
      Proof.
        unfold R_le; auto.
      Qed.

      Lemma locals_related__Renv_le : forall Renv Renv' l l',
          Renv_le Renv Renv' ->
          locals_related Renv' l l' ->
          locals_related Renv l l'.
      Proof.
        unfold Renv_le, R_le, locals_related; auto.
      Qed.

      Ltac apply_locals_related :=
        lazymatch goal with
          H: locals_related _ ?l _ |- context[map.get ?l ?x] => specialize (H x) end.

      Lemma consistent_Renv_put : forall iG x i,
          consistent_Renv (map.put iG x i) = map.put (consistent_Renv iG) x (consistent i).
      Proof.
        unfold consistent_Renv; intros. apply mmap_put; auto.
      Qed.

      Lemma put_consistent_Renv_remove_same : forall istr x R,
          map.put (consistent_Renv istr) x R = map.put (consistent_Renv (map.update istr x None)) x R.
      Proof.
        unfold consistent_Renv; intros.
        rewrite mmap_update; auto.
        rewrite put_update_same; auto.
      Qed.

      Lemma put_consistent_Renv_put_same : forall istr x i R,
          map.put (consistent_Renv istr) x R = map.put (consistent_Renv (map.put istr x i)) x R.
      Proof.
        intros. rewrite consistent_Renv_put, Properties.map.put_put_same.
        reflexivity.
      Qed.

      Lemma locals_related_lifted_step : forall Renv l l' R v v' x,
          locals_related Renv l l' ->
          lifted_related (Some R) v v' ->
          locals_related (map.put Renv x R) (map.update l x v) (map.update l' x v').
      Proof.
        unfold locals_related; intros.
        destruct_get_put_strings.
        1: rewrite !Properties.map.get_update_same; auto.
        1: rewrite !Properties.map.get_update_diff; auto.
      Qed.

      Lemma locals_related_lifted_step2 : forall Renv x l l' v v',
          locals_related (map.put Renv x (consistent LikeSet)) l l' ->
          lifted_related (map.get Renv x) v v' ->
          locals_related Renv (map.update l x v) (map.update l' x v').
      Proof.
        intros; unfold locals_related; intros.
        destruct_String_eqb x x0.
        1: rewrite !Properties.map.get_update_same; auto.
        1:{ rewrite !Properties.map.get_update_diff; auto.
            apply_locals_related. rewrite_map_get_put_hyp. }
      Qed.

      Lemma aenv_le_at__R_le : forall iG iG' x,
          aenv_le_at x iG iG' ->
          R_le (map.get (consistent_Renv iG) x) (map.get (consistent_Renv iG') x).
      Proof.
        unfold aenv_le_at, R_le, lifted_related; intros.
        rewrite consistent_Renv_sound in *.
        repeat destruct_match_hyp; try congruence; intuition auto.
        do_injection; eauto using consistent_step.
      Qed.

      Lemma Renv_le_except__locals_related : forall Renv Renv' l l' x v v',
          locals_related Renv l l' ->
          (forall y, y <> x -> R_le (map.get Renv' y) (map.get Renv y)) ->
          lifted_related (map.get Renv' x) (Some v) (Some v') ->
          locals_related Renv' (map.put l x v) (map.put l' x v').
      Proof.
        unfold locals_related; intros.
        destruct_get_put_strings; eauto using lifted_related__Renv_le.
      Qed.

      Lemma collection_tag_leb__R_le : forall i i',
          collection_tag_leb i i' = true -> R_le (Some (consistent i)) (Some (consistent i')).
      Proof.
        destruct i, i'; simpl; try congruence; auto; intros.
        all: unfold R_le; intros.
        1:{ destruct v, v'; simpl in *; auto.
            repeat case_match; auto.
            auto using dedup_preserve_Permutation, value_eqb_sym, value_eqb_refl, value_eqb_eq. }
        1,2: destruct v, v'; simpl in *; auto;
        repeat case_match;
        try congruence; do_injection; auto.
      Qed.

      Lemma aenv_le__consistent_Renv_le: forall (istr istr' : aenv),
          aenv_le istr istr' ->
          Renv_le (consistent_Renv istr) (consistent_Renv istr').
      Proof.
        intros. unfold Renv_le; intros.
        apply aenv_le_at__R_le; auto.
      Qed.

      Lemma aenv_le_at__lifted_related : forall istr istr' store store' x,
          aenv_le_at x istr istr' ->
          locals_related (consistent_Renv istr') store store' ->
          lifted_related (map.get (consistent_Renv istr') x) (map.get store x) (map.get store' x) ->
          lifted_related (map.get (consistent_Renv istr) x) (map.get store x) (map.get store' x).
      Proof.
        intros.
        eapply lifted_related__Renv_le; eauto.
        apply aenv_le_at__R_le; auto.
      Qed.

      Lemma consistent_Renv_remove : forall iG x,
          consistent_Renv (map.update iG x None) = map.update (consistent_Renv iG) x None.
      Proof.
        intros. unfold consistent_Renv. rewrite mmap_update; auto.
      Qed.

      Lemma R_le_None_l : forall r, R_le None r.
      Proof.
        unfold R_le, lifted_related; intros.
        repeat case_match; auto.
      Qed.

      Lemma concat_repeat_preserve_consistent : forall i l l' n,
          consistent i (VList l) (VList l') ->
          consistent i (VList (List.concat (repeat l n))) (VList (List.concat (repeat l' n))).
      Proof.
        destruct i; simpl; try congruence; intros;
          induction n; simpl; auto using Permutation_dedup_app, Permutation_app.
      Qed.

      Lemma cons_preserve_consistent : forall i l l' v,
          consistent i (VList l) (VList l') ->
          consistent i (VList (v :: l)) (VList (v :: l')).
      Proof.
        destruct i; simpl; auto; try congruence; intros.
        repeat case_match; auto;
          [ apply find_some in E | apply find_some in E0 ]; intuition auto;
          lazymatch goal with
            H: value_eqb _ _ = true |- _ => apply value_eqb_eq in H; subst
          end.
        all: [> eapply find_none in E0 | eapply find_none in E ].
        4: apply Permutation_sym in H.
        2,4: pose proof value_eqb_dec;
        rewrite List.dedup_preserves_In in *;
        eapply Permutation_in; eauto.
        1,2: rewrite value_eqb_refl in *; congruence.
      Qed.

      Lemma app_preserve_consistent : forall i l1 l2 l1' l2',
          consistent i (VList l1) (VList l1') ->
          consistent i (VList l2) (VList l2') ->
          consistent i (VList (l1 ++ l2)) (VList (l1' ++ l2')).
      Proof.
        destruct i; simpl; intros; try congruence.
        1:{ apply Permutation_dedup_app;
            auto using value_eqb_dec, dedup_preserve_Permutation,
              value_eqb_eq, value_eqb_refl, value_eqb_sym, Permutation_app. }
        1: apply Permutation_app; auto.
      Qed.

      Lemma map_preserve_consistent : forall i l l' f g,
          consistent i (VList l) (VList l') ->
          (forall x, In x l -> f x = g x) ->
          consistent i (VList (map f l)) (VList (map g l')).
      Proof.
        destruct i; simpl; intros.
        1:{ rewrite dedup_map_dedup. rewrite (dedup_map_dedup g).
            apply dedup_preserve_Permutation; auto using value_eqb_refl, value_eqb_eq, value_eqb_sym.
            apply In_Permutation_map; auto. intros. eauto using dedup_In. }
        1:{ assert(E: List.map f l = List.map g l).
            { apply map_ext_in; auto. }
            rewrite E. apply Permutation_map; auto. }
        1:{ f_equal. do_injection. apply map_ext_in; auto. }
      Qed.

      Lemma filter_preserve_consistent : forall i l l' f g,
          consistent i (VList l) (VList l') ->
          (forall x, In x l -> f x = g x) ->
          consistent i (VList (filter f l)) (VList (filter g l')).
      Proof.
        destruct i; simpl; intros.
        1:{ rewrite dedup_filter_dedup. rewrite (dedup_filter_dedup g).
            apply dedup_preserve_Permutation; auto using value_eqb_refl, value_eqb_eq, value_eqb_sym.
            apply In_Permutation_filter; auto; intros.
            lazymatch goal with
              H: In _ _ |- _ => apply dedup_In in H end; auto. }
        1: apply Permutation_filter; auto.
        1: do_injection; f_equal; apply In_filter_ext; auto.
      Qed.

      Lemma flat_map_preserve_consistent : forall i l l' f g,
          consistent i (VList l) (VList l') ->
          (forall x, In x l -> consistent i (VList (f x)) (VList (g x))) ->
          consistent i (VList (flat_map f l)) (VList (flat_map g l')).
      Proof.
        destruct i; simpl; intros.
        2: apply Utils.Permutation_flat_map; auto.
        1:{ rewrite dedup_flat_map_dedup. rewrite (dedup_flat_map_dedup g).
            remember (List.dedup value_eqb l) as u. remember (List.dedup value_eqb l') as u'.
            assert(Forall (fun x => In x l) u).
            { rewrite Forall_forall; intros; subst. eapply dedup_In; eauto. }
            rewrite dedup_flat_map_dedup2. rewrite (dedup_flat_map_dedup2 g).
            clear Hequ Hequ'. generalize dependent f; generalize dependent g.
            induction H; simpl; auto; intros.
            1:{ invert_Forall. apply Permutation_dedup_app; auto.
                apply dedup_preserve_Permutation; auto using value_eqb_refl, value_eqb_eq, value_eqb_sym. }
            1:{ repeat invert_Forall.
                apply dedup_preserve_Permutation; auto using value_eqb_refl, value_eqb_eq, value_eqb_sym.
                rewrite Permutation_app_swap_app.
                repeat apply Permutation_app; auto. apply Utils.Permutation_flat_map; intros; auto.
                apply_Forall_In. }
            1:{ eapply perm_trans. 1: apply IHPermutation1; auto.
                apply IHPermutation2; auto.
                rewrite Forall_forall; intros.
                lazymatch goal with H: Forall _ _ |- _ =>  eapply List.Forall_In in H end;
                eauto using Permutation_in, Permutation_sym. } }
        1:{ do_injection; subst. f_equal.
            apply In_flat_map_ext; intros.
            specialize (H0 a H1). congruence. }
      Qed.

      Lemma unop_tag_sound : forall i o v v' t1 t2,
          type_of_unop o t1 t2 ->
          type_of_value v t1 ->
          consistent (unop_collection_tag i o) v v' ->
          consistent i (interp_unop o v) (interp_unop o v').
      Proof.
        destruct o; simpl; intros; subst.
        all: try apply consistent_refl.
        invert_type_of_op.
        lazymatch goal with
          H: type_of_value _ _ |- _ => inversion H; subst end.
        destruct_match_hyp; intuition idtac. invert_type_of_value.
        erewrite Permutation_length; eauto using consistent_refl.
      Qed.

      Lemma binop_tag_sound : forall i i1 i2 o v1 v1' v2 v2' t1 t2 t3,
          type_of_binop o t1 t2 t3 ->
          type_of_value v1 t1 ->
          type_of_value v2 t2 ->
          binop_collection_tag i o = (i1, i2) ->
          consistent i1 v1 v1' -> consistent i2 v2 v2' ->
          consistent i (interp_binop o v1 v2) (interp_binop o v1' v2').
      Proof.
        destruct o; simpl; intros; invert_pair.
        all: try rewrite consistent_LikeList_eq in *; subst.
        all: try apply consistent_refl.
        all: invert_type_of_op;
          repeat lazymatch goal with
              H: type_of_value ?v (_ _), H1: consistent _ ?v _ |- _ =>
                eapply consistent__type_of_value in H1 as H'; eauto;
                inversion H; inversion H'; subst; clear H; clear H' end.
        1: apply app_preserve_consistent; auto.
        1:{ lazymatch goal with
              H: type_of_value ?v _ |- _ => inversion H; subst; clear H end.
            apply concat_repeat_preserve_consistent; auto. }
        1: apply cons_preserve_consistent; auto.
      Qed.

      Ltac use_tag_of_sound_IH' e :=
        lazymatch goal with
        | IH: context[consistent _ (interp_expr _ _ e) _] |- context[consistent _ (interp_expr _ _ e) _] => eapply IH
        | IH: context[consistent _ (interp_expr _ _ e) _], H: tag_of _ _ e _ |- _ => eapply IH in H; clear IH
        end.

      Ltac use_tag_of_sound_IH :=
        multimatch goal with
          |- context[interp_expr _ _ ?e] => use_tag_of_sound_IH' e
        end.

      Ltac use_tag_of_sound_IH_eauto :=
        use_tag_of_sound_IH; [ | | | | | | | eauto | eauto ]; auto.

      Ltac use_tag_of_sound_IH_eauto2 :=
        use_tag_of_sound_IH_eauto;
        [ |
        | apply locals_wf_step; [ | eassumption ]
        | apply locals_wf_step; [ | eassumption ]
        | rewrite consistent_Renv_put; apply locals_related_step; eauto ];
        eauto using consistent_refl with fiat2_hints.

      Ltac get_consistent_values e :=
        apply_type_sound e; eauto with fiat2_hints;
        lazymatch goal with
        | H: consistent LikeList ?v _ |- context[?v] =>
            rewrite consistent_LikeList_eq in *
        | H: consistent _ ?v _ |- context[?v] =>
            let H' := fresh "H'" in
            eapply consistent_sym, consistent__type_of_value in H as H'
        end; eauto;
        repeat invert_type_of_value_clear; repeat rewrite_expr_value.

      Ltac use_tag_of_sound_IH2 :=
        lazymatch goal with
          |- context[match interp_expr _ _ ?e with _ => _ end] =>
            use_tag_of_sound_IH' e; [ | | | | | | | eauto | eauto ]; auto;
            get_consistent_values e
        end.

      Lemma tag_of_sound : forall (Gstore Genv : tenv) e t,
          type_of Gstore Genv e t ->
          tenv_wf Gstore -> tenv_wf Genv ->
          forall istr ienv store store' env env' i,
            locals_wf Gstore store -> locals_wf Genv env ->
            locals_wf Gstore store' -> locals_wf Genv env' ->
            locals_related (consistent_Renv istr) store store' ->
            locals_related (consistent_Renv ienv) env env' ->
            tag_of istr ienv e i ->
            consistent i (interp_expr store env e) (interp_expr store' env' e).
      Proof.
        induction 1 using type_of_IH; simpl; intros.
        all: invert_tag_of.
        1,2: eapply consistent_step; eauto;
        lazymatch goal with
          H: locals_related _ ?G _ |- context[get_local ?G ?x] =>
            specialize (H x) end;
        rewrite consistent_Renv_sound in *; rewrite_l_to_r;
        unfold lifted_related, get_local in *;
        [> apply_locals_wf env; apply_locals_wf env'
        | apply_locals_wf store; apply_locals_wf store' ];
        repeat case_match; intuition idtac.
        1: apply consistent_refl.
        1: eapply unop_tag_sound; eauto using type_sound.
        1: eapply binop_tag_sound; eauto using type_sound.
        1:{ use_tag_of_sound_IH2.
            case_match; use_tag_of_sound_IH; eauto. }
        1:{ use_tag_of_sound_IH; eauto with fiat2_hints.
            rewrite consistent_Renv_put. apply locals_related_step; auto.
            use_tag_of_sound_IH; eauto. }
        1:{ use_tag_of_sound_IH2.
            apply flat_map_preserve_consistent; auto using consistent_sym.
            intros. apply_Forall_In.
            use_tag_of_sound_IH_eauto2.
            get_consistent_values e2; auto using consistent_sym. }
        1:{ use_tag_of_sound_IH2.
            eapply consistent_step; eauto.
            repeat lazymatch goal with
                     H: VList _ = _, H': _ = VList _ |- _ => clear H H'
                   end.
            lazymatch goal with
              |- consistent ?i ?v ?v' => assert(type_of_value v t2 /\ consistent i v v')
            end.
            { lazymatch goal with
                H: Forall _ _ |- _ => induction H end; simpl.
              1:{ split; eauto with fiat2_hints.
                  use_tag_of_sound_IH; eauto using tag_of_weaken. }
              split.
              1:{ eapply type_sound; eauto;
                  [ repeat apply tenv_wf_step | repeat apply locals_wf_step ];
                  intuition eauto with fiat2_hints. }
              use_tag_of_sound_IH; eauto.
              1: repeat apply tenv_wf_step; eauto with fiat2_hints.
              1,2: repeat apply locals_wf_step; intuition eauto with fiat2_hints.
              1: eauto using consistent__type_of_value.
              repeat rewrite consistent_Renv_put. repeat apply locals_related_step;
                intuition auto using consistent_refl. }
            intuition idtac. }
        1:{ eapply consistent_step; [ rewrite consistent_LikeList_eq | destruct i; auto ].
            do 2 f_equal.
            clear H H0 H2 H3 H4 H13.
            generalize dependent tl.
            lazymatch goal with
              H: Forall _ _ |- _ => induction H end; simpl; auto; intros.
            invert_Forall2. destruct tl; try discriminate. cbn in *; invert_cons.
            erewrite IHForall; eauto. f_equal.
            case_match; cbn in *. f_equal.
            rewrite <- consistent_LikeList_eq. use_tag_of_sound_IH; eauto. }
        1:{ use_tag_of_sound_IH2; apply consistent_refl. }
        1:{ eapply consistent_step; [ rewrite consistent_LikeList_eq | destruct i; auto ].
            do 3 f_equal.
            apply map_ext_in; intros. repeat apply_Forall_In.
            case_match; cbn in *; intuition idtac.
            repeat (use_tag_of_sound_IH; [ | | | | | eauto | eauto ]; auto).
            rewrite consistent_LikeList_eq in *. congruence. }
        1:{ use_tag_of_sound_IH2.
            eapply consistent_step; [ rewrite consistent_LikeList_eq | destruct i; auto ].
            repeat rewrite_expr_value.
            repeat use_tag_of_sound_IH_eauto; congruence. }
        1:{ use_tag_of_sound_IH2.
            eapply consistent_step; [ rewrite consistent_LikeList_eq | destruct i; auto ].
            repeat rewrite_expr_value.
            use_tag_of_sound_IH_eauto; congruence. }
        1:{ use_tag_of_sound_IH2.
            eapply consistent_step; [ rewrite consistent_LikeList_eq | destruct i; auto ].
            repeat rewrite_expr_value.
            use_tag_of_sound_IH_eauto; congruence. }
        1:{ use_tag_of_sound_IH_eauto.
            apply_type_sound e; eauto with fiat2_hints.
            rewrite consistent_LikeList_eq in *.
            invert_type_of_value_clear; rewrite_expr_value;
              lazymatch goal with H: _ = VOption _ |- _ => rewrite H end.
            all: use_tag_of_sound_IH; eauto with fiat2_hints.
            rewrite consistent_Renv_put. apply locals_related_step; auto.
            rewrite consistent_LikeList_eq in *; congruence. }
        1:{ use_tag_of_sound_IH2.
            lazymatch goal with H: VDict _ = _ |- _ => clear H end.
            eapply consistent_step; [rewrite consistent_LikeList_eq | destruct i; auto ].
            use_tag_of_sound_IH' e0; [ | | | | | | | eauto | eauto ]; auto.
            rewrite consistent_LikeList_eq in *; rewrite_l_to_r.
            eapply In_fold_right_ext with (P:=fun v => type_of_value v t);
              intros; intuition eauto with fiat2_hints; apply_Forall_In.
            2: apply_type_sound e; intuition eauto with fiat2_hints.
            rewrite <- consistent_LikeList_eq.
            use_tag_of_sound_IH; eauto with fiat2_hints.
            1,2: repeat apply locals_wf_step; intuition eauto with fiat2_hints.
            repeat rewrite consistent_Renv_put.
            repeat apply locals_related_step; auto using consistent_refl. }
        1:{ use_tag_of_sound_IH2.
            destruct i; cbn in *.
            1:{ eapply Permutation_sym, Permutation_dedup_Permuted; eauto using Permuted_value_sort. }
            1:{ eauto using Permutation_sym, perm_trans, Permuted_value_sort. }
            1:{ f_equal. apply Permutation_SSorted_eq; auto using StronglySorted_value_sort.
                eauto using perm_trans, Permutation_sym, Permuted_value_sort. } }
        1:{ use_tag_of_sound_IH2.
            apply filter_preserve_consistent; auto using consistent_sym.
            intros; apply_Forall_In.
            use_tag_of_sound_IH_eauto2.
            rewrite consistent_LikeList_eq in *; repeat rewrite_l_to_r; congruence. }
        1:{ repeat use_tag_of_sound_IH2.
            apply flat_map_preserve_consistent; auto using consistent_sym.
            intros; apply_Forall_In. apply map_preserve_consistent.
            1: apply filter_preserve_consistent; auto using consistent_sym; intros.
            2: intros;
            lazymatch goal with H: In _ (filter _ _) |- _ => apply filter_In in H as [HL _] end.
            all: apply_Forall_In;
              use_tag_of_sound_IH_eauto;
              [ rewrite consistent_LikeList_eq in *
              | repeat apply tenv_wf_step; eauto with fiat2_hints
              | repeat apply locals_wf_step; [ | eassumption | eassumption ]
              | repeat apply locals_wf_step; [ | eassumption | eassumption ]
              | repeat rewrite consistent_Renv_put; repeat apply locals_related_step; eauto ];
              eauto using consistent_refl.
            repeat rewrite_l_to_r; congruence. }
        1:{ use_tag_of_sound_IH2. apply map_preserve_consistent; auto using consistent_sym.
            intros; apply_Forall_In.
            use_tag_of_sound_IH_eauto2. }
      Qed.

      Ltac apply_tag_of_sound :=
        lazymatch goal with
          H: tag_of _ _ ?e _ |- _ => eapply tag_of_sound in H
        end.

      Ltac use_well_tagged_sound_IH :=
        lazymatch goal with
          IH: context[locals_related _ (interp_command _ _ ?c) _] |-
            context[locals_related _ (interp_command _ _ ?c) _] =>
            eapply IH
        end.

      Lemma well_tagged_sound : forall (Gstore Genv : tenv) c,
          well_typed Gstore Genv c ->
          tenv_wf Gstore -> tenv_wf Genv ->
          forall istr ienv inv istr_expect store store' env env',
            locals_wf Gstore store -> locals_wf Genv env ->
            locals_wf Gstore store' -> locals_wf Genv env' ->
            locals_related (consistent_Renv istr) store store' ->
            locals_related (consistent_Renv ienv) env env' ->
            well_tagged istr ienv inv c istr_expect ->
            locals_related (consistent_Renv istr_expect) (interp_command store env c) (interp_command store' env' c).
      Proof.
        induction 1; simpl; intros.
        all: invert_well_tagged.
        1:{ eapply locals_related__Renv_le; eauto.
            apply aenv_le__consistent_Renv_le; auto. }
        1:{ use_well_tagged_sound_IH; eauto.
            all: eapply command_type_sound; eauto. }
        1:{ use_well_tagged_sound_IH; eauto with fiat2_hints.
            rewrite consistent_Renv_put. apply locals_related_step; auto.
            eapply tag_of_sound; eauto. }
        1:{ apply locals_related_lifted_step2.
            2: eapply aenv_le_at__lifted_related; eauto.
            eapply locals_related__Renv_le.
            2: use_well_tagged_sound_IH; eauto with fiat2_hints.
            1: rewrite consistent_Renv_put. 1: apply Renv_le_refl.
            rewrite consistent_Renv_put. apply locals_related_step; auto.
            eapply tag_of_sound; eauto. }
        1:{ eapply locals_related__Renv_le.
            2: apply locals_related_step; eauto.
            2: eapply tag_of_sound; eauto.
            unfold Renv_le; intros. destruct (String.eqb x x0) eqn:E;
              rewrite ?eqb_eq, ?eqb_neq in *; subst;
              rewrite_map_get_put_goal.
            1:{ rewrite consistent_Renv_sound. unfold get_collection_tag.
                case_match; [ apply R_le_refl | apply R_le_None_l ]. }
            1:{ apply aenv_le_at__R_le.
                lazymatch goal with
                  H: aenv_le istr_expect _ |- _ =>
                    specialize (H x0) end.
                unfold aenv_le_at in *.
                repeat destruct_match_hyp; intuition idtac.
                rewrite_map_get_put_hyp. rewrite_l_to_r; auto. } }
        1:{ apply_type_sound e; invert_type_of_value.
            apply_tag_of_sound.
            9,10: eauto. all: eauto.
            rewrite_expr_value. rewrite consistent_LikeList_eq in *.
            lazymatch goal with
              H: interp_expr _ _ _ = _ |- _ => rewrite H end.
            case_match; use_well_tagged_sound_IH; eauto. }
        1:{ apply_type_sound e; invert_type_of_value.
            apply_tag_of_sound.
            9,10: eauto. all: eauto.
            rewrite_expr_value. rewrite consistent_LikeList_eq in *.
            lazymatch goal with
              H: interp_expr _ _ _ = _ |- _ => rewrite H end.
            repeat lazymatch goal with
                     H: _ = _ |- _ => clear H end.
            lazymatch goal with H: type_of_value _ _ |- _ => clear H end.
            eapply locals_related__Renv_le; [ eapply aenv_le__consistent_Renv_le; eauto | ].
            lazymatch goal with
              H: locals_related (consistent_Renv istr) _ _ |- _ =>
                eapply locals_related__Renv_le in H end; [ | apply aenv_le__consistent_Renv_le; eauto ].
            generalize dependent store; generalize dependent store'.
            lazymatch goal with
              H: Forall _ _ |- _ => induction H end; simpl; intros.
            1:{ eapply locals_related__Renv_le; eauto. apply Renv_le_refl. }
            1:{ apply IHForall.
                1,2: eapply command_type_sound; eauto with fiat2_hints.
                use_well_tagged_sound_IH; eauto with fiat2_hints.
                rewrite consistent_Renv_put. apply locals_related_step; auto.
                apply consistent_refl. } }
      Qed.
    End WithRelMap.
  End WithWord.
End WithMap.
