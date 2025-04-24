Require Import String List.
Require Import fiat2.Language.
Require Import coqutil.Map.Interface.
Require Import ZArith Permutation.
Require Import coqutil.Word.Interface fiat2.IndexInterface fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Interpret.
Require Import fiat2.Examples.
Require Import Morphisms.

(* What an expr with a list type can be interpreted to *)
Inductive collection_tag := LikeSet | LikeBag | LikeList.

Section fold_command_with_global.
  Context (tbl : string).
  Context (f : list string -> command -> command).
  Context (g : expr -> expr).
  Fixpoint fold_command_with_global (free_vars : list string) (c : command) : command :=
    f free_vars
      match c with
      | CSkip => CSkip
      | CSeq c1 c2 => CSeq (fold_command_with_global free_vars c1) (fold_command_with_global free_vars c2)
      | CLet e x c => CLet (fold_expr g e) x (fold_command_with_global (x :: free_vars) c)
      | CLetMut e x c =>
          (* Avoid applying the transformation if the global variable is shadowed *)
          CLetMut (fold_expr g e) x
            (if String.eqb x tbl then c else fold_command_with_global free_vars c)
      | CAssign x e => CAssign x (fold_expr g e)
      | CIf e c1 c2 =>
          CIf (fold_expr g e) (fold_command_with_global free_vars c1) (fold_command_with_global free_vars c2)
      | CForeach e x c =>
          CForeach (fold_expr g e) x (fold_command_with_global (x :: free_vars) c)
      end.
End fold_command_with_global.

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

  Definition size_of_map {key value map} (m : @map.rep key value map) :=
    map.fold (fun n _ _ => S n) O m.

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

  Ltac invert_type_of :=
    lazymatch goal with
    | H: type_of _ _ (_ _) _ |- _ => inversion H; subst end.

  Ltac invert_well_typed :=
    lazymatch goal with
    | H: well_typed _ _ (_ _) |- _ => inversion H; subst
    | H: well_typed _ _ _ |- _ => inversion H; subst end.

  Ltac rewrite_map_get_put_hyp :=
    multimatch goal with
    | H: context[map.get (map.put _ ?x _) ?x] |- _ =>
        rewrite map.get_put_same in H
    | H: context[map.get (map.put _ _ _) _] |- _ =>
        rewrite map.get_put_diff in H; try now (simpl in *; intuition)
    end.

  Ltac rewrite_map_get_put_goal :=
    multimatch goal with
    | |- context[map.get (map.put _ ?x _) ?x] =>
        rewrite map.get_put_same
    | |- context[map.get (map.put _ _ _) _] =>
        rewrite map.get_put_diff; try now (simpl in *; intuition)
    end.

  Ltac case_match' c :=
    lazymatch c with
    | context [match ?c' with _ => _ end] => case_match' c'
    | _ =>
        let E := fresh "E" in
        destruct c eqn:E
    end.
  Ltac case_match :=
    match goal with
    | |- context [ match ?e with
                   | _ => _
                   end ] => case_match' e
    end.

  Ltac clear_refl := lazymatch goal with H: ?x = ?x |- _ => clear H end.

  Ltac rewrite_l_to_r :=
    lazymatch goal with
    | H: ?x = _, H': context[?x] |- _ => rewrite H in H'
    | H: ?x = _ |- context[?x] => rewrite H
    end.

  Ltac rewrite_r_to_l :=
    lazymatch goal with
    | H: _ = ?x, H': context[?x] |- _ => rewrite <- H in H'
    | H: _ = ?x |- context[?x] => rewrite <- H
    end.

  Ltac destruct_String_eqb x y :=
    let E := fresh "E" in
    destruct (String.eqb x y) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.

  Ltac destruct_get_put_strings :=
    lazymatch goal with
    | |- context[map.get(map.put _ ?x _) ?y] =>
        destruct_String_eqb x y;
        repeat rewrite_map_get_put_hyp; repeat rewrite_map_get_put_goal
    | _: context[map.get(map.put _ ?x _) ?y] |- _ =>
        destruct_String_eqb x y;
        repeat rewrite_map_get_put_hyp
    end.

  Ltac destruct_get_update_strings :=
    lazymatch goal with
    | |- context[map.get(map.update _ ?x _) ?y] =>
        destruct_String_eqb x y;
        [ rewrite Properties.map.get_update_same
        | rewrite Properties.map.get_update_diff]; auto
    end.

  Ltac do_injection :=
    lazymatch goal with
      H: ?c _ = ?c _ |- _ => injection H; intros; subst
    end.

  Ltac apply_Forall_In :=
    lazymatch goal with
      H: Forall _ ?l, _: In _ ?l |- _ =>
        eapply List.Forall_In in H; eauto end.

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

  Ltac destruct_match_hyp :=
    lazymatch goal with
      H: context[match ?x with _ => _ end] |- _ =>
        let E := fresh "E" in
        destruct x eqn:E end.

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

  Ltac invert_pair :=
    lazymatch goal with
      H: _ = (_, _) |- _ => inversion H; subst; clear H
    end.

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

  Lemma put_update_same : forall vt (mt : map.map string vt) {mt_ok : map.ok mt}
                                 (m : mt) k v v',
      map.put (map.update m k v) k v' = map.put m k v'.
  Proof.
    intros; apply map.map_ext; intro x.
    destruct_get_put_strings; auto.
    destruct_get_update_strings; intuition idtac.
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

  Ltac invert_Forall :=
    lazymatch goal with
    | H: Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    end.

  Ltac invert_Forall2 :=
    lazymatch goal with
    | H: Forall2 _ (_ :: _) _ |- _ => inversion H; subst; clear H
    | H: Forall2 _ _ (_ :: _) |- _ => inversion H; subst; clear H
    | H: Forall2 _ _ _ |- _ => inversion H; subst; clear H
    end.

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

  Definition domain_incl {vt1 vt2 : Type} {m1 : map.map string vt1} {m2 : map.map string vt2}
    (G1 : m1) (G2 : m2) :=
    forall x, match map.get G1 x with
              | Some _ => match map.get G2 x with
                          | Some _ => True
                          | None => False
                          end
              | None => True
              end.

  Definition domain_eq {vt1 vt2 : Type} {m1 : map.map string vt1} {m2 : map.map string vt2}
    (G1 : m1) (G2 : m2) :=
    domain_incl G1 G2 /\ domain_incl G2 G1.

  Lemma domain_incl_refl : forall {vt : Type} {m : map.map string vt} (G : m),
      domain_incl G G.
  Proof.
    unfold domain_incl; intros. case_match; auto.
  Qed.

  Lemma domain_incl_tran : forall {vt1 vt2 vt3: Type} {m1 : map.map string vt1}
                                  {m2 : map.map string vt2} {m3 : map.map string vt3}
                                  (G1 : m1) (G2 : m2) (G3 : m3),
      domain_incl G1 G2 -> domain_incl G2 G3 ->
      domain_incl G1 G3.
  Proof.
    unfold domain_incl; intros * H1 H2 x.
    specialize (H1 x); specialize (H2 x).
    repeat destruct_match_hyp; intuition idtac.
  Qed.

  Lemma domain_eq_refl : forall {vt : Type} {m : map.map string vt} (G : m),
      domain_eq G G.
  Proof.
    unfold domain_eq; auto using domain_incl_refl.
  Qed.

  Lemma domain_eq_sym : forall {vt1 vt2 : Type} {m1 : map.map string vt1} {m2 : map.map string vt2}
                               (G1 : m1) (G2 : m2),
      domain_eq G1 G2 -> domain_eq G2 G1.
  Proof.
    unfold domain_eq; intuition auto.
  Qed.

  Lemma domain_eq_tran : forall {vt1 vt2 vt3: Type} {m1 : map.map string vt1}
                                  {m2 : map.map string vt2} {m3 : map.map string vt3}
                                  (G1 : m1) (G2 : m2) (G3 : m3),
      domain_eq G1 G2 -> domain_eq G2 G3 ->
      domain_eq G1 G3.
  Proof.
    unfold domain_eq; intuition eauto using domain_incl_tran.
  Qed.

  Lemma domain_incl_empty : forall {vt1 vt2 : Type} {m1 : map.map string vt1}
                                   {m1_ok : map.ok m1}
                                   {m2 : map.map string vt2} (G : m2),
      domain_incl (map.empty (map:=m1)) G.
  Proof.
    unfold domain_incl; intros.
    rewrite map.get_empty; auto.
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

  Ltac invert_pair2 :=
    lazymatch goal with
    | H: (_,_) = (_, _) |- _ => inversion H; subst; clear H
    end.

  Ltac invert_cons :=
    lazymatch goal with H: _ :: _ = _ :: _ |- _ => inversion H; subst end.

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

  Ltac destruct_exists :=
    lazymatch goal with
      H: exists _, _ |- _ => destruct H end.

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

  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.

  Definition consistent (i : collection_tag) (v1 v2 : value (word:=word)) : Prop :=
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

  Section LikeDictIndex.
    Notation value := (value (width:=width)).
    Context {locals : map.map string value} {locals_ok : map.ok locals}.
    Context {to_from_con from_to_con : collection_tag}.
    Context {idx : index} {idx_wf : value -> Prop} {idx_ok : ok to_from_con from_to_con idx idx_wf consistent}.
    (* ??? TODO: try generalizing to a consistency lattice structure *)

    Definition can_transf_to_index' (max_i : collection_tag) (istr0 : aenv) (tbl : string) (c : command) :=
      let (_, _, inv) := command_tag_req istr0 c in
      match map.get inv tbl with
      | Some i => collection_tag_leb i max_i
      | _ => true
      end.

    Definition make_LikeList_aenv (G : tenv) : aenv :=
      map.fold (fun m x _ => map.put m x LikeList) map.empty G.

    Definition can_transf_to_index (max_i : collection_tag) (t : type) (istr : aenv) (c : command) :=
      (* expect t to be the type of e, istr to map all free mut vars in c except tbl to LikeList *)
      match c with
      | CLetMut e tbl c' =>
          (is_tbl_ty t && can_transf_to_index' max_i (map.put istr tbl LikeSet) tbl c')%bool
      | _ => false
      end.

    Definition idx_read_to_list_read (tbl : string) (e : expr) :=
      match e with
      | ELoc tbl' => if String.eqb tbl tbl'
                     then substitute ((hole, (ELoc tbl)) :: nil) nil from_idx
                     else e
      | _ => e
      end.

    Definition list_write_to_idx_write (tbl : string) (free_vars : list string) (c : command) :=
      match c with
      | CAssign tbl' e =>
          if String.eqb tbl tbl'
          then CAssign tbl (substitute ((hole, e) :: nil) free_vars to_idx)
          else c
      | _ => c
      end.

    Definition transf_to_idx' (free_vars : list string) (tbl : string) (c : command) : command :=
      fold_command_with_global tbl (list_write_to_idx_write tbl) (idx_read_to_list_read tbl) free_vars c.

    Definition transf_to_idx (free_vars : list string) (c : command) : command :=
      match c with
      | CLetMut e tbl c =>
          CLetMut (substitute ((hole, e)::nil) free_vars to_idx) tbl
            (transf_to_idx' free_vars tbl c)
      | _ => c
      end.

    (* ??? TODO: move *)
    Lemma value_eqb_refl : forall (v : value), value_eqb v v = true.
    Proof.
      unfold value_eqb. intro; rewrite value_compare_refl; auto.
    Qed.

    Lemma value_eqb_neq : forall (x y : value), value_eqb x y = false -> x <> y.
    Proof.
      intros; intro; subst. rewrite value_eqb_refl in *; congruence.
    Qed.

    Lemma value_eqb_dec : forall (x y : value), BoolSpec (x = y) (x <> y) (value_eqb x y).
      intros. destruct (value_eqb x y) eqn:E.
      1: constructor; auto using value_eqb_eq.
      1: constructor. 1: auto using value_eqb_neq.
    Qed.

    Lemma NoDup_dedup_value_eqb : forall (l : list value), NoDup (List.dedup value_eqb l).
    Proof.
      induction l; simpl.
      1: apply NoDup_nil.
      case_match; trivial. constructor; auto.
      intro H. apply dedup_In in H. apply (find_none _ _ E) in H.
      rewrite value_eqb_refl in *; discriminate.
    Qed.

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

    Ltac invert_type_of_op :=
      lazymatch goal with
      | H: type_of_unop _ _ _ |- _ => inversion H; subst
      | H: type_of_binop _ _ _ _ |- _ => inversion H; subst
      end.

    Ltac apply_type_sound e :=
      lazymatch goal with
        H: type_of _ _ e _ |- _ =>
          let H' := fresh "H'" in
          eapply type_sound in H as H'; eauto
      end.

    Ltac invert_type_of_value :=
      lazymatch goal with
        H: type_of_value (_ _) _ |- _ =>
          inversion H; subst
      end.

    Ltac invert_type_wf :=
      lazymatch goal with
      | H: type_wf (TList ?t) |- type_wf ?t => inversion H; clear H; subst
      | H: type_wf (TOption ?t) |- type_wf ?t => inversion H; clear H; subst
      | H: type_wf (TDict ?t _) |- type_wf ?t => inversion H; clear H; subst
      | H: type_wf (TDict _ ?t) |- type_wf ?t => inversion H; clear H; subst
      | H: type_wf (TRecord ?tl) |- Forall type_wf (List.map snd ?tl) => inversion H; clear H; subst
      end.

    Lemma invert_TList_wf: forall t, type_wf (TList t) -> type_wf t.
    Proof.
      intros. invert_type_wf; auto.
    Qed.

    Lemma invert_TOption_wf: forall t, type_wf (TOption t) -> type_wf t.
    Proof.
      intros. invert_type_wf; auto.
    Qed.

    Lemma invert_TDict_wf_l: forall kt vt, type_wf (TDict kt vt) -> type_wf kt.
    Proof.
      intros. invert_type_wf; auto.
    Qed.

    Lemma invert_TDict_wf_r: forall kt vt, type_wf (TDict kt vt) -> type_wf vt.
    Proof.
      intros. invert_type_wf; auto.
    Qed.

    Lemma invert_TRecord_wf: forall tl, type_wf (TRecord tl) -> Forall type_wf (List.map snd tl).
    Proof.
      intros. invert_type_wf; auto.
    Qed.

    Create HintDb fiat2_hints.
    Hint Resolve type_of__type_wf : fiat2_hints.
    Hint Resolve invert_TList_wf : fiat2_hints.
    Hint Resolve invert_TOption_wf : fiat2_hints.
    Hint Resolve invert_TDict_wf_l : fiat2_hints.
    Hint Resolve invert_TDict_wf_r : fiat2_hints.
    Hint Resolve invert_TRecord_wf : fiat2_hints.
    Hint Resolve tenv_wf_step : fiat2_hints.
    Hint Resolve locals_wf_step : fiat2_hints.
    Hint Resolve type_sound : fiat2_hints.

    Lemma get_free_vars_empty : get_free_vars (map.empty (map:=tenv)) = nil.
    Proof.
      unfold get_free_vars. apply Properties.map.fold_empty.
    Qed.

    Definition map_incl {key value : Type} {map : map.map key value} (m m' : map) : Prop :=
      forall k v, map.get m k = Some v -> map.get m' k = Some v.

    Lemma map_incl_refl : forall {key value : Type} {map : map.map key value}
                                 (m : map), map_incl m m.
    Proof.
      unfold map_incl; intros. assumption.
    Qed.

    Lemma map_incl_empty : forall {key value : Type} {map : map.map key value} {map_ok : map.ok map}
                                  (m : map), map_incl map.empty m.
    Proof.
      unfold map_incl; intros. rewrite map.get_empty in H; congruence.
    Qed.

    Lemma tenv_wf_empty : tenv_wf map.empty.
    Proof.
      unfold tenv_wf; intros. rewrite map.get_empty in H; congruence.
    Qed.

    Lemma map_incl_step : forall {kt vt : Type} {m : map.map kt vt} {m_ok : map.ok m}
                                 (H_dec: forall k1 k2 : kt, {k1 = k2} + {k1 <> k2}) (G G' : m) k v,
        map_incl G G' -> map_incl (map.put G k v) (map.put G' k v).
    Proof.
      unfold map_incl; intros.
      destruct (H_dec k k0); subst.
      1: rewrite map.get_put_same in *; auto.
      1: rewrite map.get_put_diff in *; auto.
    Qed.

    Ltac apply_type_of_strengthen_IH :=
      lazymatch goal with
        IH: context[_ -> type_of _ _ ?e _] |- type_of _ _ ?e _ =>
          apply IH end.

    Lemma type_of_strengthen : forall e (Gstore Genv: tenv) t,
        type_of Gstore Genv e t ->
        forall (Gstore' Genv' : tenv),
          map_incl Gstore Gstore' -> map_incl Genv Genv' ->
          type_of Gstore' Genv' e t.
    Proof.
      induction 1 using @type_of_IH; simpl; intros.
      all: econstructor; eauto.
      all: try (apply_type_of_strengthen_IH; auto;
                repeat apply map_incl_step; auto using string_dec).
      1:{ eapply Forall2_impl; [ | eauto ]; auto. }
      1:{ eapply Forall_impl; [ | eauto ].
          simpl; intros. intuition auto. }
    Qed.

    Lemma make_LikeList_aenv_sound : forall Gstore x t,
        map.get Gstore x = Some t -> map.get (make_LikeList_aenv Gstore) x = Some LikeList.
    Proof.
      unfold make_LikeList_aenv. intros. revert H. apply map.fold_spec; intros.
      1: rewrite map.get_empty in * |-; discriminate.
      destruct_get_put_strings; auto.
    Qed.

    Lemma stores_eq_except__update_eq : forall (store store' : locals) tbl v,
        (forall x, x <> tbl -> map.get store x = map.get store' x) ->
        map.update store tbl v = map.update store' tbl v.
    Proof.
      intros. apply map.map_ext. intros.
      destruct_String_eqb k tbl.
      1: repeat rewrite Properties.map.get_update_same; reflexivity.
      1: repeat rewrite Properties.map.get_update_diff; auto.
    Qed.

    Lemma command_preserve_untouched_store : forall c (Gstore Genv :tenv) (store env : locals),
        tenv_wf Gstore -> tenv_wf Genv ->
        well_typed Gstore Genv c ->
        locals_wf Gstore store -> locals_wf Genv env ->
        forall x, map.get Gstore x = None ->
                  map.get (interp_command store env c) x = map.get store x.
    Proof.
      induction c; simpl; auto; intros.
      all: invert_well_typed.
      1:{ erewrite IHc2. 4: eauto. all: auto.
          2: eapply command_type_sound; eauto.
          eapply IHc1. 4: eauto. all: eauto. }
      1:{ erewrite IHc. 4: eauto. all: eauto with fiat2_hints. }
      1:{ destruct_String_eqb x0 x.
          1: rewrite Properties.map.get_update_same; reflexivity.
          1: rewrite Properties.map.get_update_diff; auto.
          erewrite IHc. 4: eauto. all: eauto with fiat2_hints.
          all: rewrite_map_get_put_goal. }
      1:{ destruct_get_put_strings; try congruence. }
      1:{ case_match; auto. case_match; subst; eauto. }
      1:{ apply_type_sound e. invert_type_of_value.
          lazymatch goal with H: VList _ = _ |- _ => clear H end.
          generalize dependent store. induction l; simpl; auto; intros.
          rewrite IHl; auto; invert_Forall.
          1: eapply IHc. 3: eauto. all: eauto with fiat2_hints.
          1: eapply command_type_sound; eauto with fiat2_hints.
          1:{ apply_type_sound e. eapply command_type_sound; eauto with fiat2_hints. }}
    Qed.

    Lemma map_incl_step_r : forall {A : Type} {map : map.map string A} {map_ok : map.ok map}
                                   k v (m m' : map),
        map_incl m m' -> map.get m k = None -> map_incl m (map.put m' k v).
    Proof.
      unfold map_incl; intros.
      destruct_get_put_strings; congruence.
    Qed.

    Definition locals_equiv (G : tenv) (l l' : locals) : Prop :=
      forall x t, map.get G x = Some t ->
                  map.get l x = map.get l' x.

    Lemma locals_equiv_refl : forall G l, locals_equiv G l l.
    Proof.
      unfold locals_equiv. auto.
    Qed.

    Lemma locals_equiv_step : forall G l l' x t v v',
        locals_equiv G l l' ->
        v = v' ->
        locals_equiv (map.put G x t) (map.put l x v) (map.put l' x v').
    Proof.
      unfold locals_equiv; intros.
      destruct_get_put_strings; eauto.
    Qed.

    Hint Resolve locals_equiv_step : fiat2_hints.

    Ltac apply_locals_equiv :=
      lazymatch goal with
      | H: locals_equiv ?G _ _, H': map.get ?G _ = Some _ |- _ =>
          apply H in H' end.

    Ltac use_interp_expr__locals_equiv_IH :=
      lazymatch goal with
        IH: context[interp_expr _ _ ?e] |- context[interp_expr _ _ ?e] =>
          erewrite IH; clear IH end.

    Lemma interp_expr__locals_equiv : forall e Gstore Genv t,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e t ->
        forall (store env store' env' : locals),
          locals_wf Gstore store -> locals_wf Genv env ->
          locals_equiv Gstore store store' -> locals_equiv Genv env env' ->
          interp_expr store' env' e = interp_expr store env e.
    Proof.
      induction e using expr_IH; simpl; auto; intros.
      all: invert_type_of.
      1,2: unfold get_local; apply_locals_equiv; rewrite_l_to_r; auto.
      all: try now (repeat (use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto)).
      1:{ revert IHe2. use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; intros;
          eauto using locals_equiv_refl with fiat2_hints.
          use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ];
            eauto using locals_equiv_refl with fiat2_hints. }
      1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
          apply_type_sound e1; invert_type_of_value. f_equal.
          apply In_flat_map_ext; intros; apply_Forall_In.
          use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints. }
      1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
          apply_type_sound e1; invert_type_of_value.
          revert IHe3. use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto; intros.
          eapply In_fold_right_ext with (P:=fun v => type_of_value v t); intros.
          1: apply_type_sound e2.
          1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints.
              2: repeat apply tenv_wf_step; eauto with fiat2_hints.
              2: repeat apply locals_wf_step; apply_Forall_In; intuition auto.
              apply_type_sound e3;
                [ repeat apply tenv_wf_step; eauto with fiat2_hints
                | repeat apply locals_wf_step; apply_Forall_In; intuition auto ]. } }
      1:{ do 2 f_equal. lazymatch goal with
          H1: type_of _ _ _ _, H2: Permutation _ _, H3: NoDup _, H4: List.map fst _ = _ |- _ =>
            clear H1 H2 H3 H4 end.
          generalize dependent tl; induction l; simpl; auto; intros. case_match.
          destruct tl; invert_Forall; invert_Forall2; simpl in *. f_equal.
          1: f_equal; use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
          1: eapply IHl; eauto. }
      1:{ do 3 f_equal. apply map_ext_in; intros.
          repeat apply_Forall_In; case_match; simpl in *.
          intuition auto.
          repeat (use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto). }
      1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
          apply_type_sound e1; invert_type_of_value.
          all: use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints. }
      1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
          apply_type_sound e1; invert_type_of_value.
          revert IHe3. use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto; intros.
          eapply In_fold_right_ext with (P:=fun v => type_of_value v t); intros.
          1: apply_type_sound e2.
          1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints.
              2: repeat apply tenv_wf_step; eauto with fiat2_hints.
              2: repeat apply locals_wf_step; apply_Forall_In; intuition auto.
              apply_type_sound e3;
                [ repeat apply tenv_wf_step; eauto with fiat2_hints
                | repeat apply locals_wf_step; apply_Forall_In; intuition auto ]. } }
      1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
          apply_type_sound e1; invert_type_of_value.
          f_equal. apply In_filter_ext; auto; intros. apply_Forall_In.
          use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints. }
      1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
          apply_type_sound e1; invert_type_of_value.
          use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
          apply_type_sound e2; invert_type_of_value.
          f_equal. apply In_flat_map_ext; intros. apply_Forall_In.
          erewrite In_filter_ext; eauto.
          2:{ intros. apply_Forall_In.
              use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints.
              1: reflexivity.
              repeat apply tenv_wf_step; eauto with fiat2_hints. }
          apply map_ext_in; intros.
          lazymatch goal with H: In _ (filter _ _) |- _ => apply filter_In in H; intuition auto end.
          apply_Forall_In.
          use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints.
          repeat apply tenv_wf_step; eauto with fiat2_hints. }
      1:{ use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto.
          apply_type_sound e1; invert_type_of_value.
          f_equal. apply map_ext_in; intros. apply_Forall_In.
          use_interp_expr__locals_equiv_IH; [ | | | eauto | .. ]; eauto with fiat2_hints. }
    Qed.

    Lemma map_incl__locals_equiv : forall G l l',
        locals_wf G l -> map_incl l l' -> locals_equiv G l l'.
    Proof.
      unfold locals_wf, map_incl, locals_equiv. intros * H_wf H_incl * H.
      apply H_wf in H. destruct_match_hyp; intuition auto.
      apply H_incl in E. congruence.
    Qed.

    Lemma interp_expr_strengthen : forall e Gstore Genv t,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e t ->
        forall (store env store' env' : locals),
          locals_wf Gstore store -> locals_wf Genv env ->
          map_incl store store' -> map_incl env env' ->
          interp_expr store' env' e = interp_expr store env e.
    Proof.
      intros.
      eapply interp_expr__locals_equiv; [ | | eauto | .. ]; auto using map_incl__locals_equiv.
    Qed.

    Lemma locals_wf_empty : forall (l : locals), locals_wf map.empty l.
    Proof.
      unfold locals_wf; intros. rewrite map.get_empty in *; congruence.
    Qed.

    Lemma locals_wf_step_r : forall G (l : locals) x v,
        locals_wf G l -> map.get G x = None ->
        locals_wf G (map.put l x v).
    Proof.
      unfold locals_wf; intros.
      destruct_get_put_strings; try congruence.
      apply H in H1. auto.
    Qed.

    Definition sub_wf (Genv0 Gstore Genv : tenv) (sub : list (string * expr)) : Prop :=
      forall x t, map.get Genv0 x = Some t ->
                  match sub_lookup x sub with
                  | Some e => type_of Gstore Genv e t
                  | None => False
                  end.

    Lemma In_length_le_max : forall x l,
        In x l -> le (String.length x) (list_max (List.map String.length l)).
    Proof.
      induction l; simpl; intros; intuition auto.
      1:{ subst. apply Nat.le_max_l. }
      1:{ eapply Nat.le_trans; eauto. apply Nat.le_max_r. }
    Qed.

    Lemma string_app_length : forall x y,
        String.length (x ++ y) = String.length x + String.length y.
    Proof.
      induction x; simpl; auto.
    Qed.

    Lemma repeat_string_length : forall s n,
        String.length (repeat_string s n) = String.length s * n.
    Proof.
      induction n; simpl; auto.
      rewrite string_app_length. intuition auto with *.
    Qed.

    Lemma add_l_le : forall m n p, m + n <= p -> n <= p.
    Proof.
      induction 1; intuition auto with *.
    Qed.

    Lemma fresh_var_is_fresh : forall x l, ~ In (fresh_var x l) l.
    Proof.
      unfold fresh_var; intros. case_match.
      2: rewrite inb_false_iff in *; auto.
      intro contra. apply In_length_le_max in contra.
      rewrite string_app_length, repeat_string_length in contra.
      simpl in *. rewrite Nat.add_0_r in contra.
      apply add_l_le in contra. intuition auto with *.
    Qed.

    Lemma get_free_vars__map_get_None : forall x (G : tenv),
        ~ In x (get_free_vars G) <-> map.get G x = None.
    Proof.
      intros. unfold get_free_vars. apply map.fold_spec; intuition auto.
      1: apply map.get_empty.
      1:{ destruct (String.eqb x k) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          1: simpl in *; intuition auto.
          1: rewrite_map_get_put_goal. }
      1:{ destruct (String.eqb x k) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          all: rewrite_map_get_put_hyp; congruence. }
    Qed.

    Ltac destruct_In :=
      lazymatch goal with
        H: In _ (_ :: _) |- _ => destruct H; subst end.

    Lemma get_free_vars__map_get_Some : forall x (G : tenv),
        In x (get_free_vars G) <-> exists t, map.get G x = Some t.
    Proof.
      intros. unfold get_free_vars. apply map.fold_spec; intuition auto.
      1: apply in_nil in H; intuition auto.
      1: destruct_exists; rewrite map.get_empty in *; congruence.
      1:{ destruct (String.eqb x k) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          all: rewrite_map_get_put_goal.
          1: exists v; auto.
                    1: destruct_In; intuition auto. }
      1:{ destruct (String.eqb x k) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          1: constructor; auto.
          1: rewrite_map_get_put_hyp. }
    Qed.

    Lemma get_free_vars_put : forall (G : tenv) x t,
        incl (get_free_vars (map.put G x t)) (x :: get_free_vars G).
    Proof.
      unfold incl; intros.
      destruct (String.eqb a x) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst.
      1: constructor; auto.
      rewrite get_free_vars__map_get_Some in *. rewrite_map_get_put_hyp.
      rewrite <- get_free_vars__map_get_Some in *. auto using in_cons.
    Qed.

    Lemma incl_cons_step : forall A l l' (x : A), incl l l' -> incl (x :: l) (x :: l').
    Proof.
      unfold incl; intros. destruct_In.
      1: constructor; auto.
      1: auto using in_cons.
    Qed.

    Ltac use_substitute_preserve_ty_IH :=
      lazymatch goal with
        IH: context[type_of _ _ (substitute _ _ ?e) _] |- type_of _ _ (substitute _ _ ?e) _ =>
          eapply IH end.

    Ltac apply_sub_wf :=
      lazymatch goal with
        H: forall _ _, map.get _ _ = Some _ -> _, H': map.get _ _ = Some _ |- _ =>
      apply H in H' end.

    Lemma map_get_fresh_var_None : forall (G : tenv) x free_vars,
        incl (get_free_vars G) free_vars ->
        map.get G (fresh_var x free_vars) = None.
    Proof.
      intros * H; apply get_free_vars__map_get_None. intro contra.
      apply H, fresh_var_is_fresh in contra; auto.
    Qed.

    Lemma fresh_var_neq : forall x y l, y <> fresh_var x (y :: l).
    Proof.
      intros; intro contra.
      lazymatch goal with
        _: _ = fresh_var ?y ?l |- _ =>
          assert(contra' : In (fresh_var y l) l) end.
      { rewrite <- contra; constructor; auto. }
      apply fresh_var_is_fresh in contra'; auto.
    Qed.

    Lemma fresh_var_neq2 : forall x y z l, y <> fresh_var x (z :: y :: l).
    Proof.
      intros; intro contra.
      lazymatch goal with
        _: _ = fresh_var ?y ?l |- _ =>
          assert(contra' : In (fresh_var y l) l) end.
      { rewrite <- contra. right. left. auto. }
      apply fresh_var_is_fresh in contra'; auto.
    Qed.

    Ltac apply_sub_wf_with_map_incl :=
      apply_sub_wf; case_match; intuition auto;
      eapply type_of_strengthen; eauto;
      repeat apply map_incl_step_r; auto using map_incl_refl;
      apply map_get_fresh_var_None; auto; repeat apply incl_tl; auto.

    Ltac case_match_string_eqb :=
      case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
      rewrite_map_get_put_hyp; auto.

    Ltac apply_incl_lemmas := eapply incl_tran; eauto using get_free_vars_put; apply incl_cons_step; auto.

    Ltac inj_constr_get_put := try do_injection; constructor; repeat rewrite_map_get_put_goal; auto.

    Lemma substitute_preserve_ty : forall e0 Gstore Genv0 Genv t0 sub free_vars,
        tenv_wf Gstore -> tenv_wf Genv0 ->
        type_of Gstore Genv0 e0 t0 ->
        sub_wf Genv0 Gstore Genv sub ->
        incl (get_free_vars Genv) free_vars ->
        type_of Gstore Genv (substitute sub free_vars e0) t0.
    Proof.
      unfold sub_wf; induction e0 using expr_IH; simpl; intros.
      all: invert_type_of.
      all: try now (econstructor; eauto).
      1: apply_sub_wf; case_match; intuition auto.
      all: try (econstructor; eauto;
                use_substitute_preserve_ty_IH; simpl; intros;
                [ | | eauto | .. ]; auto;
                [ repeat apply tenv_wf_step | ..]; eauto with fiat2_hints;
                [ | repeat apply_incl_lemmas ];
                repeat (case_match_string_eqb;
                        [ inj_constr_get_put; try apply fresh_var_neq; try apply fresh_var_neq2 | ]);
                apply_sub_wf_with_map_incl).
      1:{ econstructor; eauto.
          1: rewrite fst_map_fst; auto.
          lazymatch goal with
            H0: type_of _ _ _ _, H1: Permutation _ _, H2: NoDup _,
                  H3: Sorted.StronglySorted _ _, H4: map fst _ = _ |- _ =>
              clear H0 H1 H2 H3 H4 end.
          generalize dependent tl. induction H; simpl; intros.
          all: destruct tl; simpl in *; invert_Forall2; intuition auto.
          constructor.
          1:{ case_match; simpl in *. eapply H; eauto. }
          1: apply IHForall; auto. }
      1:{ constructor; auto.
          lazymatch goal with H: type_of _ _ _ _ |- _ => clear H end.
          induction H8; simpl; auto. constructor; invert_Forall.
          1:{ case_match; simpl in *; intuition auto.
              all: lazymatch goal with
                     H: context[type_of _ _ (substitute _ _ ?e) _] |-
                       type_of _ _ (substitute _ _ ?e) _ =>
                       eapply H end; eauto. }
          1: apply IHForall; auto. }
      1:{ econstructor; eauto;
          use_substitute_preserve_ty_IH; simpl; intros.
          3,8: eauto.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
          all: repeat apply_incl_lemmas.
          all: repeat (case_match_string_eqb;
                       [ inj_constr_get_put; try apply fresh_var_neq; try apply fresh_var_neq2 | ]);
            apply_sub_wf_with_map_incl. }
    Qed.

    Fixpoint make_sub_env (store env : locals) (sub : list (string * expr)) : locals :=
      match sub with
      | nil => map.empty
      | (x, e) :: sub => map.put (make_sub_env store env sub) x (interp_expr store env e)
      end.

    Lemma sub_lookup_Some__make_sub_env : forall x sub e (store env : locals),
        sub_lookup x sub = Some e ->
        map.get (make_sub_env store env sub) x = Some (interp_expr store env e).
    Proof.
      induction sub; simpl; intros.
      1: congruence.
      case_match; simpl in *.
      destruct_match_hyp; rewrite ?eqb_eq, ?eqb_neq in *; try do_injection; subst.
      all: rewrite_map_get_put_goal; auto.
    Qed.

    Lemma make_sub_env_wf : forall Genv0 Gstore Genv store env sub,
        tenv_wf Gstore -> tenv_wf Genv ->
        locals_wf Gstore store -> locals_wf Genv env ->
        sub_wf Genv0 Gstore Genv sub ->
        locals_wf Genv0 (make_sub_env store env sub).
    Proof.
      unfold sub_wf, locals_wf; intros. apply_sub_wf.
      destruct_match_hyp; intuition auto.
      erewrite sub_lookup_Some__make_sub_env; eauto.
      eapply type_sound; eauto.
    Qed.

    Lemma make_sub_env__locals_equiv : forall Genv0 Gstore Genv store env store' env' sub,
        tenv_wf Gstore -> tenv_wf Genv ->
        sub_wf Genv0 Gstore Genv sub ->
        locals_wf Gstore store -> locals_wf Genv env ->
        locals_equiv Gstore store store' -> locals_equiv Genv env env' ->
        locals_equiv Genv0 (make_sub_env store env sub) (make_sub_env store' env' sub).
    Proof.
      unfold sub_wf; intros. unfold locals_equiv; intros. apply_sub_wf.
      destruct_match_hyp; intuition auto.
      erewrite !sub_lookup_Some__make_sub_env; eauto. f_equal.
      symmetry. eapply interp_expr__locals_equiv; [ | | eauto | .. ]; auto.
    Qed.

    Lemma locals_equiv__put_fresh : forall G l x v,
        map.get G x = None -> locals_equiv G l (map.put l x v).
    Proof.
      unfold locals_equiv. intros. rewrite_map_get_put_goal. congruence.
    Qed.

    Lemma locals_equiv_sym : forall G l l',
        locals_equiv G l l' -> locals_equiv G l' l.
    Proof.
      unfold locals_equiv; intros.
      symmetry; eauto.
    Qed.

    Lemma locals_equiv_tran : forall G l l' l'',
        locals_equiv G l l' -> locals_equiv G l' l'' -> locals_equiv G l l''.
    Proof.
      unfold locals_equiv; intros.
      erewrite H; eauto.
    Qed.

    Ltac use_substitute_preserve_sem_IH :=
      lazymatch goal with
        IH: context[_ = interp_expr _ _ ?e] |- context[interp_expr _ _ (substitute _ _ ?e)] =>
          erewrite IH end.

    Lemma substitute_preserve_sem : forall e0 Gstore Genv0 Genv t0 sub free_vars store env,
        tenv_wf Genv0 -> tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv0 e0 t0 ->
        sub_wf Genv0 Gstore Genv sub ->
        incl (get_free_vars Genv) free_vars ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_expr store env (substitute sub free_vars e0) = interp_expr store (make_sub_env store env sub) e0.
    Proof.
      unfold sub_wf. induction e0 using expr_IH; simpl; auto; intros.
      all: invert_type_of.
      all: try now (repeat (use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto)).
      1:{ apply_sub_wf. unfold get_local. destruct_match_hyp; simpl; intuition auto.
          erewrite sub_lookup_Some__make_sub_env; eauto. }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; auto.
          6:{ eapply locals_wf_step; eauto. eapply type_sound;
              [ eapply substitute_preserve_ty | .. ]; [ | | eauto | .. ]; eauto. }
          all: eauto with fiat2_hints.
          all: [> | simpl; intros; case_match_string_eqb;
                    [ inj_constr_get_put | apply_sub_wf_with_map_incl ]
               | repeat apply_incl_lemmas ].
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          eapply interp_expr__locals_equiv; [ | | eauto | .. ]; eauto using locals_equiv_refl with fiat2_hints.
          1:{ apply locals_wf_step; [ | eapply type_sound; eauto ].
              all: eapply make_sub_env_wf; [ | | | | eauto ]; auto. }
          1:{ apply locals_equiv_step;
              [ eapply make_sub_env__locals_equiv; [ | | eauto | .. ];
                auto using locals_equiv_refl, locals_equiv__put_fresh, map_get_fresh_var_None
              | simpl; unfold get_local; rewrite_map_get_put_goal; auto ]. } }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ].
          invert_type_of_value. f_equal.
          apply In_flat_map_ext; intros; apply_Forall_In.
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
          8: eapply locals_wf_step; eauto.
          all: eauto with fiat2_hints.
          all: [> | simpl; intros; case_match_string_eqb;
                    [ inj_constr_get_put | apply_sub_wf_with_map_incl ]
               | repeat apply_incl_lemmas ].
          erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; eauto using locals_equiv_refl with fiat2_hints;
            [ apply locals_wf_step; auto; eapply make_sub_env_wf; [ | | | | eauto ]; auto
            | apply locals_equiv_step;
              [ eapply make_sub_env__locals_equiv; [ | | eauto | .. ];
                auto using locals_equiv_refl, locals_equiv__put_fresh, map_get_fresh_var_None
              | simpl; unfold get_local; rewrite_map_get_put_goal; auto ] ]. }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ].
          invert_type_of_value.
          revert IHe0_3. use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto; intros.
          eapply In_fold_right_ext with (P:=fun v => type_of_value v t0).
          1: eapply type_sound; eauto; eapply make_sub_env_wf; [ | | | | eauto ]; auto.
          intros. apply_Forall_In.
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
          8: repeat eapply locals_wf_step; eauto.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
          all: [> | repeat (simpl; intros; case_match_string_eqb;
                            [ inj_constr_get_put; try apply fresh_var_neq | try apply_sub_wf_with_map_incl ])
               | repeat apply_incl_lemmas ].
          erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; intuition auto.
          1: eapply type_sound; eauto.
          all: repeat apply tenv_wf_step; repeat apply locals_wf_step;
            eauto using locals_equiv_refl with fiat2_hints.
          all: try (eapply make_sub_env_wf; [ | | | | eauto ]; auto).
          repeat apply locals_equiv_step.
          2,3: simpl; unfold get_local; repeat rewrite_map_get_put_goal; auto using fresh_var_neq.
          eapply make_sub_env__locals_equiv; [ | | eauto | .. ]; auto using locals_equiv_refl.
          repeat eapply locals_equiv_tran, locals_equiv__put_fresh, map_get_fresh_var_None.
          all: auto using locals_equiv_refl, incl_tl. }
      1:{ do 2 f_equal. lazymatch goal with
          H1: type_of _ _ _ _, H2: List.map fst _ = _, H3: Permutation _ _, H4: NoDup _, H5: Sorted.StronglySorted _ _ |- _ =>
            clear H1 H2 H3 H4 H5 end.
          generalize dependent tl; induction l; simpl; auto; intros. invert_Forall; invert_Forall2.
          case_match. destruct tl; try discriminate; simpl in *.
          lazymatch goal with H: _ :: _ = _ :: _ |- _ => inversion H; subst end. erewrite IHl; eauto.
          do 2 f_equal. eauto. }
      1:{ do 3 f_equal. rewrite map_map. apply map_ext_in; intros.
          case_match. repeat apply_Forall_In; simpl in *. intuition auto.
          f_equal; eauto. }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ].
          invert_type_of_value.
          1: use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto with fiat2_hints.
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
          8: repeat eapply locals_wf_step; eauto.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
          all: [> | repeat (simpl; intros; case_match_string_eqb;
                            [ inj_constr_get_put; try apply fresh_var_neq | try apply_sub_wf_with_map_incl ])
               | repeat apply_incl_lemmas ].
          erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; eauto using locals_equiv_refl with fiat2_hints;
            [ apply locals_wf_step; auto; eapply make_sub_env_wf; [ | | | | eauto ]; auto
            | apply locals_equiv_step;
              [ eapply make_sub_env__locals_equiv; [ | | eauto | .. ];
                auto using locals_equiv_refl, locals_equiv__put_fresh, map_get_fresh_var_None
              | simpl; unfold get_local; rewrite_map_get_put_goal; auto ] ]. }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ].
          invert_type_of_value.
          revert IHe0_3. use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto; intros.
          apply In_fold_right_ext with (P:=fun v => type_of_value v t0); intros.
          1: eapply type_sound; eauto; eapply make_sub_env_wf; [ .. | eauto ]; auto.
          apply_Forall_In. use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
          8: repeat eapply locals_wf_step; eauto.
          8,9: intuition eauto.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
          all: [> | repeat (simpl; intros; case_match_string_eqb;
                            [ inj_constr_get_put; try apply fresh_var_neq; try apply fresh_var_neq2
                            | try apply_sub_wf_with_map_incl ])
               | repeat apply_incl_lemmas ].
          erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; intuition auto.
          1: eapply type_sound; eauto.
          all: repeat apply tenv_wf_step; repeat apply locals_wf_step;
            eauto using locals_equiv_refl with fiat2_hints.
          all: try (eapply make_sub_env_wf; [ | | | | eauto ]; auto).
          repeat apply locals_equiv_step.
          2-4: simpl; unfold get_local; repeat rewrite_map_get_put_goal; auto using fresh_var_neq, fresh_var_neq2.
          eapply make_sub_env__locals_equiv; [ | | eauto | .. ]; auto using locals_equiv_refl.
          repeat eapply locals_equiv_tran, locals_equiv__put_fresh, map_get_fresh_var_None.
          all: auto using locals_equiv_refl, incl_tl. }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ].
          invert_type_of_value. f_equal.
          apply In_filter_ext; intros. apply_Forall_In.
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
          8: repeat eapply locals_wf_step; eauto.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
          all: [> | repeat (simpl; intros; case_match_string_eqb;
                            [ inj_constr_get_put; try apply fresh_var_neq | try apply_sub_wf_with_map_incl ])
               | repeat apply_incl_lemmas ].
          erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; eauto using locals_equiv_refl with fiat2_hints;
            [ apply locals_wf_step; auto; eapply make_sub_env_wf; [ | | | | eauto ]; auto
            | apply locals_equiv_step;
              [ eapply make_sub_env__locals_equiv; [ | | eauto | .. ];
                auto using locals_equiv_refl, locals_equiv__put_fresh, map_get_fresh_var_None
              | simpl; unfold get_local; rewrite_map_get_put_goal; auto ] ]. }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ];
            invert_type_of_value.
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_2; eauto; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ];
            invert_type_of_value.
          f_equal. apply In_flat_map_ext; intros. apply_Forall_In.
          erewrite In_filter_ext; [ apply map_ext_in | ]; simpl; intros.
          1:{ lazymatch goal with H: In _ (filter _ _) |- _ => apply filter_In in H; intuition auto end.
              apply_Forall_In.
              use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
              8: repeat eapply locals_wf_step; eauto.
              all: repeat apply tenv_wf_step; eauto with fiat2_hints.
              all: [> | repeat (simpl; intros; case_match_string_eqb;
                                [ inj_constr_get_put; try apply fresh_var_neq | try apply_sub_wf_with_map_incl ])
                   | repeat apply_incl_lemmas ].
              erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; eauto using locals_equiv_refl;
                [ repeat apply tenv_wf_step; eauto with fiat2_hints
                | repeat apply locals_wf_step; auto; eapply make_sub_env_wf; [ | | | | eauto ]; auto | ].
              repeat apply locals_equiv_step.
              2,3: simpl; unfold get_local; repeat rewrite_map_get_put_goal; auto using fresh_var_neq.
              eapply make_sub_env__locals_equiv; [ | | eauto | .. ]; auto using locals_equiv_refl.
              repeat eapply locals_equiv_tran, locals_equiv__put_fresh, map_get_fresh_var_None.
              all: auto using locals_equiv_refl, incl_tl. }
          1:{ apply_Forall_In. use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
              8: repeat eapply locals_wf_step; eauto.
              all: repeat apply tenv_wf_step; eauto with fiat2_hints.
              all: [> | repeat (simpl; intros; case_match_string_eqb;
                                [ inj_constr_get_put; try apply fresh_var_neq | try apply_sub_wf_with_map_incl ])
                   | repeat apply_incl_lemmas ].
              erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; eauto using locals_equiv_refl;
                [ repeat apply tenv_wf_step; eauto with fiat2_hints
                | repeat apply locals_wf_step; auto; eapply make_sub_env_wf; [ | | | | eauto ]; auto | ].
              repeat apply locals_equiv_step.
              2,3: simpl; unfold get_local; repeat rewrite_map_get_put_goal; auto using fresh_var_neq.
              eapply make_sub_env__locals_equiv; [ | | eauto | .. ]; auto using locals_equiv_refl.
              repeat eapply locals_equiv_tran, locals_equiv__put_fresh, map_get_fresh_var_None.
              all: auto using locals_equiv_refl, incl_tl. } }
      1:{ use_substitute_preserve_sem_IH; [ | | | | eauto | .. ]; eauto.
          apply_type_sound e0_1; [ | eapply make_sub_env_wf; [ .. | eauto ]; eauto ];
            invert_type_of_value.
          f_equal. apply map_ext_in; intros; apply_Forall_In.
          use_substitute_preserve_sem_IH; [ | | | | eauto | .. ].
          8: repeat eapply locals_wf_step; eauto.
          all: repeat apply tenv_wf_step; eauto with fiat2_hints.
          all: [> | repeat (simpl; intros; case_match_string_eqb;
                            [ inj_constr_get_put; try apply fresh_var_neq | try apply_sub_wf_with_map_incl ])
               | repeat apply_incl_lemmas ].
          erewrite interp_expr__locals_equiv; [ | | | eauto | .. ]; eauto using locals_equiv_refl with fiat2_hints;
            [ apply locals_wf_step; auto; eapply make_sub_env_wf; [ | | | | eauto ]; auto
            | apply locals_equiv_step;
              [ eapply make_sub_env__locals_equiv; [ | | eauto | .. ];
                auto using locals_equiv_refl, locals_equiv__put_fresh, map_get_fresh_var_None
              | simpl; unfold get_local; rewrite_map_get_put_goal; auto ] ]. }
    Qed.

    Lemma to_idx_preserve_ty : forall Gstore Genv free_vars e t,
        type_wf t -> is_tbl_ty t = true ->
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e t ->
        incl (get_free_vars Genv) free_vars ->
        type_of Gstore Genv (substitute ((hole, e) :: nil) free_vars to_idx) (idx_ty t).
    Proof.
      intros. eapply substitute_preserve_ty;
        [ | | eapply type_of_strengthen; eauto using to_idx_ty | .. ]; auto.
      2: apply map_incl_empty.
      2: apply map_incl_refl.
      1: eauto using tenv_wf_empty with fiat2_hints.
      1:{ unfold sub_wf; simpl; intros.
          case_match_string_eqb; try congruence.
          rewrite map.get_empty in *; discriminate. }
    Qed.

    Lemma to_idx_idx_wf : forall Gstore Genv e t free_vars,
        type_wf t -> is_tbl_ty t = true ->
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e t ->
        incl (get_free_vars Genv) free_vars ->
        forall store env,
          locals_wf Gstore store -> locals_wf Genv env ->
          idx_wf (interp_expr store env (substitute ((hole, e) :: nil) free_vars to_idx)).
    Proof.
      intros.
      erewrite substitute_preserve_sem with (Genv0:=map.put map.empty hole t).
      7-9: eauto.
      6:{ unfold sub_wf; intros; simpl.
          case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
            rewrite_map_get_put_hyp; rewrite ?map.get_empty in *; congruence. }
      all: eauto with fiat2_hints.
      2: apply tenv_wf_step; eauto using tenv_wf_empty with fiat2_hints.
      2:{ eapply type_of_strengthen. 1: apply to_idx_ty.
          all: eauto with fiat2_hints.
          1: apply map_incl_empty.
          1: apply map_incl_refl. }
      erewrite interp_expr_strengthen.
      1: eapply to_idx_wf; eauto.
      4: apply to_idx_ty.
      9: simpl; apply map_incl_refl.
      all: eauto using tenv_wf_empty, locals_wf_empty,
          map_incl_empty, type_sound with fiat2_hints.
    Qed.

    Lemma from_idx_preserve_ty : forall Gstore Genv e t free_vars,
        type_wf t -> is_tbl_ty t = true ->
        incl (get_free_vars Genv) free_vars ->
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e (idx_ty t) ->
        type_of Gstore Genv (substitute ((hole, e) :: nil) free_vars from_idx) t.
    Proof.
      intros. eapply substitute_preserve_ty;
        [ | | eapply type_of_strengthen; eauto using from_idx_ty | .. ]; auto.
      2: apply map_incl_empty.
      2: apply map_incl_refl.
      1: eauto using tenv_wf_empty with fiat2_hints.
      1:{ unfold sub_wf; simpl; intros.
          case_match_string_eqb; try congruence.
          rewrite map.get_empty in *; discriminate. }
    Qed.

    Ltac apply_tenv_wf :=
      lazymatch goal with
        H: tenv_wf ?G, H': map.get ?G _ = Some ?t |- type_wf ?t =>
          apply H in H' end.

    Ltac apply_transf_to_idx_preserve_ty''_IH :=
      lazymatch goal with IH: context[type_of _ _ ?e _ ] |- type_of _ _ ?e _ => apply IH end.

    Lemma transf_to_idx_preserve_ty'' : forall tbl tbl_ty e Gstore Genv t,
        tenv_wf Gstore -> tenv_wf Genv ->
        map.get Gstore tbl = Some tbl_ty ->
        is_tbl_ty tbl_ty = true ->
        type_of Gstore Genv e t ->
        type_of (map.put Gstore tbl (idx_ty tbl_ty)) Genv (fold_expr (idx_read_to_list_read tbl) e) t.
    Proof.
      induction 5 using @type_of_IH; simpl; intros.
      all: try (econstructor; eauto; apply_transf_to_idx_preserve_ty''_IH; apply tenv_wf_step; eauto with fiat2_hints).
      4: repeat apply tenv_wf_step; eauto with fiat2_hints.
      1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          1:{ repeat rewrite_l_to_r; do_injection. eapply type_of_strengthen.
              1: apply from_idx_preserve_ty with (Gstore:=map.put map.empty x (idx_ty t)) (Genv:=map.empty);
              simpl; auto.
              1: apply_tenv_wf; auto.
              1: rewrite get_free_vars_empty.
              all: eauto using idx_ty_wf, incl_nil_l, tenv_wf_empty with fiat2_hints.
              1: constructor; rewrite_map_get_put_goal; auto.
              1: apply map_incl_step; auto using string_dec.
              1,2: apply map_incl_empty. }
          1: constructor; rewrite_map_get_put_goal. }
      1:{ econstructor; eauto.
          1: rewrite fst_map_fst; assumption.
          lazymatch goal with
            H1: map fst _ = _, H2: Forall2 (type_of _ _) _ _,
                H3: Permutation _ _, H4: NoDup _ |- _ => clear H1 H2 H3 H4 end.
          generalize dependent tl.
          induction l; intros; simpl in *; invert_Forall2; auto.
          case_match; simpl in *. constructor; auto.
          destruct tl; simpl in *; try congruence. invert_cons.
          apply IHl; auto. }
      1:{ constructor; auto. lazymatch goal with H: Forall _ _ |- _ => induction H end.
          all: simpl; auto.
          case_match; simpl in *; constructor; intuition auto.
          invert_Forall; apply IHForall; auto. }
    Qed.

    Ltac use_transf_to_idx_preserve_ty'_IH :=
      lazymatch goal with
        IH: context[well_typed _ _ (transf_to_idx' _ _ ?c)] |- well_typed _ _ (transf_to_idx' _ _ ?c) =>
          apply IH
      end.

    Lemma transf_to_idx_preserve_ty' : forall tbl_ty tbl c (Gstore Genv :tenv) free_vars,
        tenv_wf Gstore -> tenv_wf Genv ->
        map.get Gstore tbl = Some tbl_ty ->
        is_tbl_ty tbl_ty = true ->
        well_typed Gstore Genv c ->
        incl (get_free_vars Genv) free_vars ->
        well_typed (map.put Gstore tbl (idx_ty tbl_ty)) Genv (transf_to_idx' free_vars tbl c).
    Proof.
      induction c; simpl; intros; try invert_well_typed; try now (constructor; auto).
      1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
          use_transf_to_idx_preserve_ty'_IH; eauto with fiat2_hints.
          apply_incl_lemmas. }
      1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
          case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
            [ rewrite Properties.map.put_put_same in *; auto
            | rewrite Properties.map.put_put_diff in *; auto;
              use_transf_to_idx_preserve_ty'_IH; eauto with fiat2_hints ].
          rewrite_map_get_put_goal. }
      1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          1:{ econstructor; [ rewrite_map_get_put_goal; eauto | ].
              eapply substitute_preserve_ty with (Genv0:=map.put map.empty hole tbl_ty); auto.
              1,2: apply tenv_wf_step; auto using tenv_wf_empty.
              1: apply idx_ty_wf; auto.
              1,2: apply_tenv_wf; auto.
              1:{ eapply type_of_strengthen; eauto using to_idx_ty, map_incl_refl.
                  apply map_incl_empty. }
              1:{ unfold sub_wf. simpl; intros.
                  case_match_string_eqb; rewrite_l_to_r; repeat do_injection;
                    [ auto using transf_to_idx_preserve_ty''
                    | rewrite map.get_empty in *; discriminate ]. } }
          1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
              rewrite_map_get_put_goal; eauto. } }
      1: constructor; auto using transf_to_idx_preserve_ty''.
      1:{ econstructor; eauto using transf_to_idx_preserve_ty''.
          use_transf_to_idx_preserve_ty'_IH; eauto with fiat2_hints.
          apply_incl_lemmas. }
    Qed.

    Lemma transf_to_idx_preserve_ty'2 : forall tbl_ty tbl c (Gstore Gstore' Genv :tenv) free_vars,
        tenv_wf Gstore -> tenv_wf Genv ->
        map.get Gstore tbl = Some tbl_ty ->
        is_tbl_ty tbl_ty = true ->
        well_typed Gstore Genv c ->
        incl (get_free_vars Genv) free_vars ->
        Gstore' = map.put Gstore tbl (idx_ty tbl_ty) ->
        well_typed Gstore' Genv (transf_to_idx' free_vars tbl c).
    Proof.
      intros; subst; apply transf_to_idx_preserve_ty'; auto.
    Qed.

    Lemma transf_to_idx_preserve_ty : forall tbl_ty tbl e c free_vars Gstore Genv,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e tbl_ty ->
        well_typed (map.put Gstore tbl tbl_ty) Genv c ->
        is_tbl_ty tbl_ty = true ->
        incl (get_free_vars Genv) free_vars ->
        well_typed Gstore Genv (transf_to_idx free_vars (CLetMut e tbl c)).
    Proof.
      simpl; intros. subst. econstructor.
      1:{ eapply substitute_preserve_ty with (Genv0:=map.put map.empty hole tbl_ty); eauto using tenv_wf_empty, incl_refl with fiat2_hints.
          1: eapply type_of_strengthen; [ apply to_idx_ty; eauto | apply map_incl_empty | apply map_incl_refl ].
          1: eapply type_of__type_wf; [ | | eauto ]; auto.
          1:{ unfold sub_wf. simpl; intros.
              destruct_get_put_strings;
                [ do_injection; rewrite eqb_refl; auto
                | rewrite map.get_empty in *; discriminate ]. } }
      1:{ erewrite <- Properties.map.put_put_same.
          apply transf_to_idx_preserve_ty'; eauto using incl_refl with fiat2_hints.
          rewrite_map_get_put_goal; auto. }
    Qed.

    Definition gallina_to_idx (v : value) : value :=
      interp_expr map.empty (map.put map.empty hole v) to_idx.

    Lemma fiat2_gallina_to_idx : forall e Gstore Genv store env t free_vars,
        is_tbl_ty t = true ->
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e t ->
        locals_wf Gstore store -> locals_wf Genv env ->
        incl (get_free_vars Genv) free_vars ->
        interp_expr store env (substitute ((hole, e) :: nil) free_vars to_idx) =
          gallina_to_idx (interp_expr store env e).
    Proof.
      unfold gallina_to_idx. simpl; intros.
      erewrite substitute_preserve_sem with (Gstore:=Gstore) (Genv0:=map.put map.empty hole t); eauto.
      3: eapply type_of_strengthen.
      1: eapply interp_expr_strengthen.
      all: try apply to_idx_ty; eauto.
      all: try apply tenv_wf_step; eauto with fiat2_hints; try apply tenv_wf_empty.
      all: try apply locals_wf_step; auto; try apply locals_wf_empty.
      1: eapply type_sound; eauto.
      all: try apply map_incl_step; auto using string_dec;
        try apply map_incl_empty; try apply incl_refl.
      unfold sub_wf; intros; simpl.
      destruct (String.eqb x hole) eqn:E_x; rewrite ?eqb_eq, ?eqb_neq in *; subst.
      all: rewrite_map_get_put_hyp; try rewrite map.get_empty in *; congruence.
    Qed.

    Definition gallina_from_idx (v : value) : value :=
      interp_expr map.empty (map.put map.empty hole v) from_idx.

    Lemma fiat2_gallina_from_idx : forall e Gstore Genv store env t free_vars,
        type_wf t -> is_tbl_ty t = true ->
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e (idx_ty t) ->
        locals_wf Gstore store -> locals_wf Genv env ->
        incl (get_free_vars Genv) free_vars ->
        interp_expr store env (substitute ((hole, e) :: nil) free_vars from_idx) =
          gallina_from_idx (interp_expr store env e).
    Proof.
      unfold gallina_from_idx. simpl; intros.
      erewrite substitute_preserve_sem
        with (Gstore:=Gstore) (Genv0:=map.put map.empty hole (idx_ty t)); eauto.
      3: eapply type_of_strengthen.
      1: eapply interp_expr_strengthen.
      all: try apply from_idx_ty; eauto.
      all: try apply tenv_wf_step; eauto with fiat2_hints; try apply tenv_wf_empty.
      all: try apply locals_wf_step; auto; try apply locals_wf_empty.
      1: eapply type_sound; eauto.
      all: try apply map_incl_step; auto using string_dec;
        try apply map_incl_empty; try apply incl_refl.
      unfold sub_wf; intros; simpl.
      destruct (String.eqb x hole) eqn:E_x; rewrite ?eqb_eq, ?eqb_neq in *; subst.
      all: rewrite_map_get_put_hyp; try rewrite map.get_empty in *; congruence.
    Qed.

    Lemma consistent_refl : forall i v, consistent i v v.
    Proof.
      unfold consistent; intros. repeat case_match; auto.
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

      Definition mmap {k v1 v2} {map1 : map.map k v1} {map2 : map.map k v2}
        (f : v1 -> v2) (m : map1) : map2 :=
        map.fold (fun m k v => map.put m k (f v)) map.empty m.

      Definition consistent_Renv (ienv : aenv) : rel_map :=
        mmap consistent ienv.

      Definition consistent_with_global_Renv (tbl : string) (istr : aenv) : rel_map :=
        map.put
          (consistent_Renv istr)
          tbl
          (fun v v' => exists u,
               consistent (get_collection_tag istr tbl) v u
               /\ v' = gallina_to_idx u).

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

      Definition R_le (R R' : option (value -> value -> Prop)) : Prop :=
        forall v v', lifted_related R' v v' -> lifted_related R v v'.

      Definition Renv_le (Renv Renv' : rel_map) : Prop :=
        forall x, R_le (map.get Renv x) (map.get Renv' x).

      Lemma locals_related__Renv_le : forall Renv Renv' l l',
          Renv_le Renv Renv' ->
          locals_related Renv' l l' ->
          locals_related Renv l l'.
      Proof.
        unfold Renv_le, R_le, locals_related; auto.
      Qed.

      Lemma aenv_le__consistent_with_global_Renv_le : forall tbl istr istr',
          aenv_le istr istr' ->
          Renv_le (consistent_with_global_Renv tbl istr) (consistent_with_global_Renv tbl istr').
      Proof.
        unfold Renv_le, consistent_with_global_Renv; intros.
        destruct_get_put_strings.
        1:{ unfold R_le; intros.
            destruct v, v'; simpl in *; auto. destruct_exists.
            exists x0; intuition eauto using aenv_le__collection_tag_leb, consistent_step. }
        1:{ unfold aenv_le, R_le in *; intros. rewrite consistent_Renv_sound in *.
            specialize (H x). unfold aenv_le_at in *. repeat destruct_match_hyp; intuition auto.
            all: destruct v, v'; simpl in *; eauto using consistent_step. }
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

      Ltac apply_locals_wf l :=
        lazymatch goal with H: locals_wf ?G l, H': map.get ?G _ = Some _ |- _ =>
                              let H'' := fresh in
                              apply H in H' as H'' end.

      Ltac apply_locals_related :=
        lazymatch goal with
          H: locals_related _ ?l _ |- context[map.get ?l ?x] => specialize (H x) end.

      Lemma get_mmap : forall vt vt' (mt : map.map string vt) (mt_ok : map.ok mt)
                              (mt' : map.map string vt') (mt'_ok : map.ok mt')
                              (m : mt) (f : vt -> vt') k,
          map.get (mmap f m) k = option_map f (map.get m k).
      Proof.
        intros. unfold mmap. apply map.fold_spec.
        1: rewrite !map.get_empty; trivial.
        intros. destruct_String_eqb k0 k; repeat rewrite_map_get_put_goal.
        auto.
      Qed.

      Lemma mmap_put : forall vt vt' (mt : map.map string vt) (mt_ok : map.ok mt)
                              (mt' : map.map string vt') (mt'_ok : map.ok mt')
                              (m : mt) k v (f : vt -> vt'),
          mmap f (map.put m k v) = map.put (mmap f m) k (f v).
      Proof.
        intros. apply map.map_ext; intro x.
        rewrite get_mmap; auto.
        destruct_String_eqb k x; repeat rewrite_map_get_put_goal; simpl; auto.
        rewrite get_mmap; auto.
      Qed.

      Lemma mmap_update : forall vt vt' (mt : map.map string vt) (mt_ok : map.ok mt)
                                 (mt' : map.map string vt') (mt'_ok : map.ok mt')
                                 (m : mt) k v (f : vt -> vt'),
          mmap f (map.update m k v) = map.update (mmap f m) k (option_map f v).
      Proof.
        intros. apply map.map_ext; intro x.
        rewrite get_mmap; auto.
        destruct_String_eqb k x.
        1: rewrite !Properties.map.get_update_same; reflexivity.
        1:{ rewrite !Properties.map.get_update_diff; auto.
            rewrite get_mmap; auto. }
      Qed.

      Lemma consistent_Renv_put : forall iG x i,
          consistent_Renv (map.put iG x i) = map.put (consistent_Renv iG) x (consistent i).
      Proof.
        unfold consistent_Renv; intros. apply mmap_put; auto.
      Qed.

      Lemma consistent_Renv_put_global : forall istr tbl R,
          map.put (consistent_Renv istr) tbl R = map.put (consistent_with_global_Renv tbl istr) tbl R.
      Proof.
        unfold consistent_Renv, consistent_with_global_Renv; intros.
        rewrite Properties.map.put_put_same; reflexivity.
      Qed.

      Lemma put_consistent_Renv_remove_same : forall istr x R,
          map.put (consistent_Renv istr) x R = map.put (consistent_Renv (map.update istr x None)) x R.
      Proof.
        unfold consistent_Renv; intros.
        rewrite mmap_update; auto.
        rewrite put_update_same; auto.
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

      Lemma R_le_refl : forall R, R_le R R.
      Proof.
        unfold R_le; intros; auto.
      Qed.

      Lemma Renv_le_refl : forall Renv, Renv_le Renv Renv.
      Proof.
        unfold Renv_le; intros. apply R_le_refl.
      Qed.

      Lemma update_put_diff : forall (vt : Type) (mt : map.map string vt),
          map.ok mt -> forall (m : mt) (k k' : string) (v : vt) (v' : option vt),
            k <> k' ->
            map.update (map.put m k v) k' v' = map.put (map.update m k' v') k v.
      Proof.
        intros. apply map.map_ext; intro x.
        destruct_get_put_strings.
        1: rewrite Properties.map.get_update_diff, map.get_put_same; auto.
        destruct_String_eqb x k'.
        1: rewrite !Properties.map.get_update_same; auto.
        1: rewrite !Properties.map.get_update_diff, map.get_put_diff; auto.
      Qed.

      Lemma consistent_with_global_Renv_remove_local : forall x tbl istr,
          x <> tbl ->
          Renv_le (map.update (consistent_with_global_Renv tbl istr) x None)
            (consistent_with_global_Renv tbl (map.update istr x None)).
      Proof.
        unfold Renv_le; intros. destruct_String_eqb x0 tbl.
        1:{ unfold consistent_with_global_Renv.
            rewrite Properties.map.get_update_diff; auto.
            rewrite !map.get_put_same. unfold R_le; intros.
            destruct v, v'; simpl in *; auto.
            destruct_exists. eexists; intuition eauto.
            unfold get_collection_tag in *.
            rewrite map.get_remove_diff in *; auto. }
        1:{ unfold consistent_with_global_Renv. rewrite update_put_diff; auto.
            rewrite !map.get_put_diff; auto.
            unfold consistent_Renv. rewrite mmap_update; simpl; auto.
            apply R_le_refl. }
      Qed.

      Lemma consistent_with_global_Renv_put_local : forall tbl x istr i,
          x <> tbl ->
          Renv_le (consistent_with_global_Renv tbl (map.put istr x i))
            (map.put (consistent_with_global_Renv tbl istr) x (consistent i)).
      Proof.
        unfold Renv_le; intros. destruct_String_eqb x0 tbl.
        1:{ unfold consistent_with_global_Renv.
            repeat rewrite_map_get_put_goal. unfold R_le; intros.
            destruct v, v'; simpl in *; auto.
            destruct_exists. eexists; intuition eauto.
            unfold get_collection_tag in *. rewrite_map_get_put_goal. }
        1:{ unfold consistent_with_global_Renv. rewrite_map_get_put_goal.
            rewrite Properties.map.put_put_diff; auto. rewrite_map_get_put_goal.
            rewrite consistent_Renv_put. apply R_le_refl. }
      Qed.

      Lemma consistent_with_global_Renv_put_local2 : forall tbl x istr i,
          x <> tbl ->
          Renv_le
            (map.put (consistent_with_global_Renv tbl istr) x (consistent i))
            (consistent_with_global_Renv tbl (map.put istr x i)).
      Proof.
        unfold Renv_le; intros. destruct_String_eqb x0 tbl.
        1:{ unfold consistent_with_global_Renv.
            repeat rewrite_map_get_put_goal. unfold R_le; intros.
            destruct v, v'; simpl in *; auto.
            destruct_exists. eexists; intuition eauto.
            unfold get_collection_tag in *. rewrite_map_get_put_hyp. }
        1:{ unfold consistent_with_global_Renv.
            rewrite Properties.map.put_put_diff; auto.
            rewrite_map_get_put_goal.
            rewrite map.get_put_diff with (k':=tbl); auto.
            rewrite consistent_Renv_put. apply R_le_refl. }
      Qed.

      Lemma lifted_related__Renv_le : forall R R' v v',
          R_le R R' -> lifted_related R' v v' -> lifted_related R v v'.
      Proof.
        unfold R_le; auto.
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

      Lemma In_find_some : forall A A_eqb a (l : list A),
          (forall a, A_eqb a a = true) ->
          In a l ->
          match find (A_eqb a) l with
          | Some _ => True
          | None => False
          end.
      Proof.
        intros * H_refl. induction l; simpl; auto; intros.
        intuition auto.
        1: subst; rewrite H_refl; auto.
        1: case_match; auto.
      Qed.

      Lemma not_In_find_none : forall A A_eqb a (l : list A),
          (forall a a', A_eqb a a' = true -> a = a') ->
          ~ In a l -> find (A_eqb a) l = None.
      Proof.
        intros * H_eq. induction l; simpl; auto; intros.
        intuition auto. case_match; auto.
        apply H_eq in E; congruence.
      Qed.

      Lemma dedup_preserve_Permutation : forall A A_eqb (l l' : list A),
          (forall a a', A_eqb a a' = true -> a = a') ->
          (forall a, A_eqb a a = true) ->
          (forall a a', A_eqb a a' = A_eqb a' a) ->
          Permutation l l' ->
          Permutation (List.dedup A_eqb l) (List.dedup A_eqb l').
      Proof.
        intros * H_eq H_refl H_sym. induction 1; simpl; auto.
        1:{ case_match.
            1:{ apply find_some in E as [HL HR]; apply H_eq in HR; subst;
                eapply Permutation_in in HL; eauto.
                eapply In_find_some in HL; eauto.
                destruct_match_hyp; intuition auto. }
            1:{ specialize (find_none _ _ E x); intros. rewrite not_In_find_none; auto.
                intro contra. eapply Permutation_in in contra.
                2: apply Permutation_sym; eauto.
                intuition auto. congruence. } }
        1:{ rewrite H_sym. case_match.
            1:{ apply H_eq in E; subst. case_match; auto. }
            1:{ repeat case_match; auto. apply perm_swap. } }
        1: eapply perm_trans; eauto.
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

      Lemma R_le_tran : forall R1 R2 R3,
          R_le R1 R2 -> R_le R2 R3 ->
          R_le R1 R3.
      Proof.
        unfold R_le; auto.
      Qed.

      Lemma Renv_le_tran : forall Renv1 Renv2 Renv3,
          Renv_le Renv1 Renv2 ->
          Renv_le Renv2 Renv3 ->
          Renv_le Renv1 Renv3.
      Proof.
        unfold Renv_le; intros. eauto using R_le_tran.
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

      Lemma dedup_nil : forall A A_eqb (l : list A),
          List.dedup A_eqb l = nil -> l = nil.
      Proof.
        induction l; simpl; auto; intros.
        destruct_match_hyp; try congruence.
        apply find_some in E. intuition auto; subst.
        apply in_nil in H0. intuition auto.
      Qed.

      Lemma dedup_dedup : forall A A_eqb (l : list A),
          List.dedup A_eqb (List.dedup A_eqb l) = List.dedup A_eqb l.
      Proof.
        induction l; simpl; auto.
        case_match; auto. simpl.
        case_match; try congruence.
        apply find_some in E0; intuition auto.
        apply dedup_In in H. eapply find_none in E; eauto. congruence.
      Qed.

      Lemma find_app_Some : forall A p (l l' : list A) a,
          find p (l ++ l') = Some a ->
          find p l = Some a \/ find p l' = Some a.
      Proof.
        induction l; simpl; auto; intros.
        case_match; intuition auto.
      Qed.

      Lemma find_app_None : forall A p  (l l' : list A),
          find p (l ++ l') = None ->
          find p l = None /\ find p l' = None.
      Proof.
        induction l; simpl; auto; intros.
        case_match; try congruence. auto.
      Qed.

      Lemma dedup_app : forall A A_eqb (l l' : list A),
          (forall x y : A, BoolSpec (x = y) (x <> y) (A_eqb x y)) ->
          List.dedup A_eqb (l ++ l') = List.dedup A_eqb (List.dedup A_eqb l ++ List.dedup A_eqb l').
      Proof.
        induction l; simpl; intros.
        1: rewrite dedup_dedup; reflexivity.
        pose proof List.dedup_preserves_In as dedup_preserves_In.
        case_match.
        1:{ apply find_app_Some in E. case_match; auto.
            intuition auto; try congruence. simpl.
            case_match; auto.
            lazymatch goal with H: find _ _ = Some _ |- _ => apply find_some in H end.
            lazymatch goal with H: find _ _ = None |- _ => eapply find_none in H end.
            2:{ apply in_or_app. right. rewrite <- dedup_preserves_In.
                intuition eauto. }
            intuition auto; congruence. }
        1:{ apply find_app_None in E. intuition auto. rewrite_l_to_r.
            simpl. case_match.
            2: rewrite IHl; auto.
            lazymatch goal with H: find _ _ = Some _ |- _ => apply find_some in H end.
            intuition auto.
            lazymatch goal with H: In _ (_ ++ _) |- _ => apply in_app_or in H end.
            rewrite <- !dedup_preserves_In in *. intuition auto;
              lazymatch goal with H: find _ ?l = None, _: In _ ?l |- _ => eapply find_none in H end;
              eauto; congruence. }
      Qed.

      Lemma Permutation_dedup_app : forall (l1 l2 l3 l4 : list value),
          Permutation (List.dedup value_eqb l1) (List.dedup value_eqb l2) ->
          Permutation (List.dedup value_eqb l3) (List.dedup value_eqb l4) ->
          Permutation (List.dedup value_eqb (l1 ++ l3)) (List.dedup value_eqb (l2 ++ l4)).
      Proof.
        intros.
        rewrite dedup_app; [ rewrite (dedup_app _ _ l2) | ]; auto using value_eqb_dec.
        apply dedup_preserve_Permutation;
          auto using value_eqb_refl, value_eqb_sym, value_eqb_eq, Permutation_app.
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

      Lemma fold_right__type_of_value : forall t1 t2 l (acc0 : value) f,
          Forall (fun v : value => type_of_value v t1) l ->
          type_of_value acc0 t2 ->
          (forall v acc, type_of_value v t1 -> type_of_value acc t2 ->
                         type_of_value (f v acc) t2) ->
          type_of_value (fold_right f acc0 l) t2.
      Proof.
        induction l; simpl; auto; intros.
        invert_Forall. apply H1; auto.
      Qed.

      Lemma Permutation_SSorted_eq : forall (l l' : list value),
          Permutation l l' ->
          Sorted.StronglySorted (fun v v' => is_true (value_leb v v')) l ->
          Sorted.StronglySorted (fun v v' => is_true (value_leb v v')) l' ->
          l = l'.
      Proof.
        induction l; intros l' H H_sort H_sort'.
        - apply Permutation_nil in H; congruence.
        - destruct l'.
          1: apply Permutation_sym, Permutation_nil in H; discriminate.
          inversion H_sort; inversion H_sort'; subst.
          apply Permutation_in with (x:=a) in H as H_in; intuition auto with *.
          apply Permutation_sym in H as H'.
          apply Permutation_in with (x:=v) in H' as H_in'; intuition auto with *.
          inversion H_in; inversion H_in'; subst.
          1-3: f_equal; apply IHl; auto; eapply Permutation_cons_inv; eauto.
          eapply List.Forall_In in H3, H7; eauto.
          apply value_leb_antisym in H3; auto; subst. f_equal.
          apply IHl; auto. eapply Permutation_cons_inv; eauto.
      Qed.

      Lemma concat_repeat_preserve_consistent : forall i l l' n,
          consistent i (VList l) (VList l') ->
          consistent i (VList (concat (repeat l n))) (VList (concat (repeat l' n))).
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

      Lemma Permutation_flat_map : forall A B (f g : A -> list B),
        forall l l', (forall x, In x l -> Permutation (f x) (g x)) ->
                     Permutation l l' ->
                     Permutation (flat_map f l) (flat_map g l').
      Proof.
        intros * H_fg. generalize dependent l'. induction l; simpl; intros l' H.
        - apply Permutation_nil in H; subst; auto.
        - apply Permutation_sym in H as H'. apply Permutation_vs_cons_inv in H'.
          repeat lazymatch goal with H: exists _, _ |- _ => destruct H end. subst.
          rewrite flat_map_app. simpl. pose proof H_fg a as H_a.
          assert (H_a_in: In a (a :: l)). { intuition auto with *. } apply H_a in H_a_in as H_p.
          destruct (f a) eqn:E.
          + simpl. apply Permutation_nil in H_p.
            rewrite H_p; simpl. rewrite <- flat_map_app.
            apply Permutation_cons_app_inv in H. intuition auto with *.
          + eapply perm_trans. 2: apply Permutation_app_swap_app.
            apply Permutation_app; auto. rewrite <- flat_map_app. apply IHl.
            2: apply Permutation_cons_app_inv in H.
            all: intuition auto with *.
      Qed.

      Lemma In_dedup_app : forall (l l' : list value),
          Forall (fun x => In x l') l ->
          List.dedup value_eqb (l ++ l') = List.dedup value_eqb l'.
      Proof.
        induction l; simpl; auto; intros.
        invert_Forall.
        assert(H: In a (l ++ l')).
        { apply in_or_app; auto. }
        apply (In_find_some _ value_eqb) in H; auto using value_eqb_refl.
        destruct_match_hyp; intuition auto.
      Qed.

      Ltac apply_value_eqb_eq :=
        lazymatch goal with
          H: value_eqb _ _ = _ |- _ =>
            apply value_eqb_eq in H; subst
        end.

      Lemma dedup_flat_map_dedup : forall (f : value -> list value) l,
          List.dedup value_eqb (flat_map f l) = List.dedup value_eqb (flat_map f (List.dedup value_eqb l)).
      Proof.
        induction l; simpl; auto.
        case_match.
        1:{ rewrite In_dedup_app; auto. apply find_some in E; intuition auto.
            apply_value_eqb_eq.
            rewrite Forall_forall; intros. apply in_flat_map; eauto. }
        1:{ simpl. rewrite dedup_app; auto using value_eqb_dec. rewrite IHl.
            rewrite <- dedup_app; auto using value_eqb_dec. }
      Qed.

      Lemma dedup_flat_map_dedup2 : forall (f : value -> list value) l,
          List.dedup value_eqb (flat_map f l) = List.dedup value_eqb (flat_map (fun v => List.dedup value_eqb (f v)) l).
      Proof.
        induction l; simpl; auto.
        rewrite dedup_app; auto using value_eqb_dec.
        lazymatch goal with
          |- _ = _ _ (_ ++ ?l') =>
            rewrite (dedup_app _ _ _ l') end; auto using value_eqb_dec.
        do 2 f_equal; auto using dedup_dedup.
      Qed.

      Lemma flat_map_preserve_consistent : forall i l l' f g,
          consistent i (VList l) (VList l') ->
          (forall x, In x l -> consistent i (VList (f x)) (VList (g x))) ->
          consistent i (VList (flat_map f l)) (VList (flat_map g l')).
      Proof.
        destruct i; simpl; intros.
        2: apply Permutation_flat_map; auto.
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
                repeat apply Permutation_app; auto. apply Permutation_flat_map; intros; auto.
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

      Lemma dedup_map_dedup : forall (f : value -> value) l,
          List.dedup value_eqb (List.map f l) = List.dedup value_eqb (List.map f (List.dedup value_eqb l)).
      Proof.
        induction l; simpl; auto. repeat case_match; simpl; auto.
        1:{ apply find_some in E; intuition auto.
            pose proof value_eqb_dec; rewrite List.dedup_preserves_In in H.
            apply_value_eqb_eq.
            rewrite IHl in * |-. rewrite <- List.dedup_preserves_In in H.
            eapply In_find_some in H; eauto using value_eqb_refl.
            destruct_match_hyp; intuition auto. }
        1:{ apply find_some in E0; intuition auto; apply_value_eqb_eq.
            eapply in_map in H.
            eapply find_none in E; intuition eauto.
            rewrite value_eqb_refl in *; congruence. }
        1:{ case_match; try congruence.
            apply find_some in E1; intuition auto; apply_value_eqb_eq.
            pose proof value_eqb_dec; rewrite List.dedup_preserves_In in H.
            rewrite <- IHl, <- List.dedup_preserves_In in * |-.
            eapply find_none in E; eauto.
            rewrite value_eqb_refl in *; congruence. }
      Qed.

      Lemma In_Permutation_map : forall (f g : value -> value) l l',
          (forall x, In x l -> f x = g x) ->
          Permutation l l' ->
          Permutation (List.map f l) (List.map g l').
      Proof.
        induction l; simpl; intros.
        1:{ apply Permutation_nil in H0; subst; auto. }
        1:{ apply Permutation_sym, Permutation_vs_cons_inv in H0 as H1.
            repeat destruct_exists; subst. rewrite map_app; simpl.
            eapply perm_trans in H0; [ | apply Permutation_middle ].
            eapply perm_trans; [ | apply Permutation_middle ].
            apply Permutation_cons; intuition auto.
            rewrite <- map_app. apply IHl; auto.
            eapply Permutation_cons_inv; eauto using Permutation_sym. }
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

      Lemma Permutation_filter : forall f g l l',
          (forall x : value, In x l -> f x = g x) ->
          Permutation l l' ->
          Permutation (filter f l) (filter g l').
        induction l; simpl; intros.
        1:{ apply Permutation_nil in H0; subst; auto. }
        1:{ apply Permutation_sym, Permutation_vs_cons_inv in H0 as H1.
            repeat destruct_exists; subst. rewrite filter_app; simpl.
            rewrite H; intuition auto. case_match.
            all: eapply perm_trans in H0; [ | apply Permutation_middle ].
            1:{ eapply perm_trans; [ | apply Permutation_middle ].
                apply Permutation_cons; auto. rewrite <- filter_app.
                apply IHl; intros; auto.
                eapply Permutation_cons_inv; eauto using Permutation_sym. }
            1:{ rewrite <- filter_app; apply IHl; auto.
                eapply Permutation_cons_inv; eauto using Permutation_sym. } }
      Qed.

      Lemma dedup_filter_dedup : forall (f : value -> bool) l,
          List.dedup value_eqb (filter f l) = List.dedup value_eqb (filter f (List.dedup value_eqb l)).
      Proof.
        induction l; simpl; auto.
        repeat case_match; simpl; repeat rewrite_l_to_r; simpl; auto.
        1:{ apply find_some in E0; intuition auto. apply_value_eqb_eq.
            assert(E_f : In v (filter f l)). { apply filter_In; intuition auto. }
            eapply In_find_some in E_f; eauto using value_eqb_refl.
            destruct_match_hyp; intuition auto. }
        1:{ pose proof (find_none _ _ E0 a).
            case_match.
            1:{ apply find_some in E1; intuition auto. apply_value_eqb_eq.
                apply filter_In in H0; intuition auto.
                rewrite value_eqb_refl in *; congruence. }
            1:{ pose proof (find_none _ _ E1 a). rewrite value_eqb_refl in *.
                case_match; auto.
                apply find_some in E2; intuition auto; apply_value_eqb_eq.
                pose proof value_eqb_dec.
                rewrite List.dedup_preserves_In, <- IHl, <- List.dedup_preserves_In in H1.
                apply H0 in H1. congruence. } }
      Qed.

      Lemma In_Permutation_filter : forall f g l l',
          (forall x : value, In x l -> f x = g x) ->
          Permutation l l' ->
          Permutation (filter f l) (filter g l').
      Proof.
        induction l; simpl; intros.
        1:{ apply Permutation_nil in H0; subst; auto. }
        1:{ apply Permutation_sym, Permutation_vs_cons_inv in H0 as H1.
            repeat destruct_exists; subst. rewrite filter_app; simpl.
            rewrite H; [ | left; auto ].
            case_match.
            all: eapply perm_trans in H0; [ | apply Permutation_middle ];
              apply Permutation_cons_inv in H0.
            1:{ eapply perm_trans; [ | apply Permutation_middle ].
                apply Permutation_cons; auto. rewrite <- filter_app.
                apply IHl; auto using Permutation_sym. }
            1:{ rewrite <- filter_app.
                apply IHl; auto using Permutation_sym. } }
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

      Lemma Permutation_dedup_Permuted : forall (l1 l2 l1' l2' : list value),
          Permutation (List.dedup value_eqb l1) (List.dedup value_eqb l2) ->
          Permutation l1 l1' -> Permutation l2 l2' ->
          Permutation (List.dedup value_eqb l1') (List.dedup value_eqb l2').
      Proof.
        intros. eapply dedup_preserve_Permutation in H0, H1;
          eauto using value_eqb_refl, value_eqb_eq, value_eqb_sym,
          Permutation_sym, perm_trans.
      Qed.

      Ltac apply_type_sound2 e :=
        lazymatch goal with
        | H:type_of _ _ e _ |- context[interp_expr _ ?env0 e] =>
            let H' := fresh "H'" in
            eapply type_sound with (env:=env0) in H as H'; eauto
        end.

      Ltac rewrite_expr_value :=
        multimatch goal with
        | H: VList _ = interp_expr _ _ _ |- _ => rewrite <- H in *
        | H: VBool _ = interp_expr _ _ _ |- _ => rewrite <- H in *
        | H: VRecord _ = interp_expr _ _ _ |- _ => rewrite <- H in *
        | H: VDict _ = interp_expr _ _ _ |- _ => rewrite <- H in *
        | H: VOption _ = interp_expr _ _ _ |- _ => rewrite <- H in *
        | H: interp_expr _ _ _ = VList _ |- _ => rewrite H in *
        | H: interp_expr _ _ _ = VBool _ |- _ => rewrite H in *
        | H: interp_expr _ _ _ = VRecord _ |- _ => rewrite H in *
        | H: interp_expr _ _ _ = VDict _ |- _ => rewrite H in *
        | H: interp_expr _ _ _ = VOption _ |- _ => rewrite H in * end.

      Ltac apply_type_sound_consistent_value e :=
        apply_type_sound2 e;
        invert_type_of_value;
        lazymatch goal with
          H: consistent _ (interp_expr _ _ e) _ |- _ =>
            let H' := fresh in
            eapply consistent__type_of_value in H as H'; eauto end;
        repeat rewrite_expr_value;
        invert_type_of_value; repeat rewrite_expr_value.

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

      Lemma consistent_sym : forall i v v', consistent i v v' -> consistent i v' v.
      Proof.
        unfold consistent; intros.
        repeat destruct_match_hyp; intuition idtac; subst; try congruence.
        all: auto using Permutation_sym.
      Qed.

      Lemma locals_related_consistent_Renv_refl : forall iG G,
          locals_related (consistent_Renv iG) G G.
      Proof.
        intros; apply locals_related_refl.
        intros; rewrite consistent_Renv_sound in *.
        destruct_match_hyp; try congruence; do_injection.
        unfold rel_refl; auto using consistent_refl.
      Qed.

      Ltac invert_type_of_value_clear :=
      lazymatch goal with
        H: type_of_value (_ _) _ |- _ =>
          inversion H; subst; clear H
      end.

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
        induction 1 using @type_of_IH; simpl; intros.
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


      Ltac use_transf_to_idx_preserve_sem''_IH :=
        lazymatch goal with
          IH: context[consistent _ (interp_expr _ _ ?e)],
            H: tag_of _ _ ?e _ |- context[interp_expr _ _ ?e] =>
            eapply IH in H end;
        [ | | | | | | | | | eauto | eauto ]; auto.

      Ltac use_transf_to_idx_preserve_sem''_IH_on e :=
        lazymatch goal with
          IH: context[consistent _ (interp_expr _ _ e)],
            H: tag_of _ _ e _ |- _ =>
            eapply IH in H end;
        [ | | | | | | | | | eauto | eauto ]; auto.

      Lemma transf_to_idx_preserve_sem'' : forall tbl tbl_ty Gstore Genv e t,
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv e t ->
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          forall store store' env env' istr ienv i,
            collection_tag_leb (get_collection_tag istr tbl) to_from_con = true ->
            tag_of istr ienv e i ->
            locals_wf Gstore store -> locals_wf Genv env ->
            locals_wf (map.put Gstore tbl (idx_ty tbl_ty)) store' -> locals_wf Genv env' ->
            locals_related (consistent_with_global_Renv tbl istr) store store' ->
            locals_related (consistent_Renv ienv) env env' ->
            consistent i (interp_expr store env e) (interp_expr store' env' (fold_expr (idx_read_to_list_read tbl) e)).
      Proof.
        intros * ? ? H. induction H using @type_of_IH; intros; simpl.
        all: invert_tag_of.
        all: try now (repeat use_transf_to_idx_preserve_sem''_IH;
                      rewrite consistent_LikeList_eq in *; repeat rewrite_r_to_l;
                      eapply consistent_step;
                      [ apply consistent_LikeList_eq; auto
                      |  destruct i; auto ]).
        1:{ eapply consistent_step; eauto. unfold get_local.
            apply_locals_related.
            rewrite consistent_Renv_sound in *. rewrite_l_to_r.
            apply_locals_wf env. apply_locals_wf env'. repeat destruct_match_hyp; intuition auto. }
        1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
            1:{ erewrite fiat2_gallina_from_idx with (Genv:=map.empty); simpl.
                7: eauto. all: eauto using idx_ty_wf, tenv_wf_empty, locals_wf_empty with fiat2_hints.
                2: constructor; rewrite_map_get_put_goal; auto.
                2: rewrite get_free_vars_empty; apply incl_refl.
                unfold get_local. apply_locals_related.
                apply_locals_wf store.
                assert(map.get (map.put Gstore x (idx_ty tbl_ty)) x = Some (idx_ty tbl_ty)).
                { rewrite_map_get_put_goal; auto. }
                apply_locals_wf store'.
                unfold consistent_with_global_Renv in *. repeat rewrite_map_get_put_hyp.
                repeat destruct_match_hyp; simpl in *; intuition auto.
                destruct_exists. unfold get_collection_tag in *; rewrite_l_to_r.
                intuition auto; subst. unfold gallina_from_idx, gallina_to_idx.
                eapply consistent_step; eauto using consistent__type_of_value.
                eapply consistent_tran.
                2: eapply to_from_consistent; eauto using consistent__type_of_value.
                1,2: eauto using collection_tag_leb_refl.
                1: rewrite_l_to_r; auto. }
            1:{ simpl. unfold get_local. apply_locals_related.
                unfold consistent_with_global_Renv in *. rewrite_map_get_put_hyp.
                rewrite consistent_Renv_sound in *. rewrite_l_to_r.
                lazymatch goal with H: map.get _ tbl = _ |- _ => clear H end.
                apply_locals_wf store.
                assert(map.get (map.put Gstore tbl (idx_ty tbl_ty)) x = Some t).
                { rewrite_map_get_put_goal; auto. }
                apply_locals_wf store'. repeat case_match; intuition auto.
                simpl in *. eapply consistent_step; eauto. } }
        1: apply consistent_refl.
        1:{ destruct o; simpl in * |-; use_transf_to_idx_preserve_sem''_IH.
            all: try (rewrite consistent_LikeList_eq in *; repeat rewrite_l_to_r;
                      eapply consistent_step;
                      [ rewrite consistent_LikeList_eq; eauto
                      | destruct i; auto ]).
            eapply consistent_step;
              [ rewrite consistent_LikeList_eq | destruct i; auto ].
            lazymatch goal with H: type_of_unop _ _ _ |- _ => inversion H; subst end.
            simpl in *. repeat case_match; try congruence; intuition auto.
            erewrite Permutation_length; eauto. }
        1:{ destruct o; simpl in * |-; repeat use_transf_to_idx_preserve_sem''_IH.
            all: lazymatch goal with
                   H: (_, _) = (_, _) |- _ => inversion H; subst end;
              repeat rewrite consistent_LikeList_eq in *; repeat rewrite_r_to_l;
              try (eapply consistent_step;
                   [ rewrite consistent_LikeList_eq; eauto
                   | destruct i; auto ]).
            all: lazymatch goal with H: type_of_binop _ _ _ _ |- _ => inversion H; subst end.
            all: simpl in *.
            1:{ apply_type_sound_consistent_value e1.
                apply_type_sound_consistent_value e2.
                apply app_preserve_consistent; auto. }
            1:{ apply_type_sound_consistent_value e1.
                apply_type_sound2 e2. invert_type_of_value.
                apply concat_repeat_preserve_consistent; auto. }
            1:{ apply_type_sound_consistent_value e2.
                apply cons_preserve_consistent; auto. } }
        1:{ repeat use_transf_to_idx_preserve_sem''_IH.
            rewrite consistent_LikeList_eq in *; repeat rewrite_r_to_l.
            apply_type_sound2 e1. invert_type_of_value. case_match; auto. }
        1:{ use_transf_to_idx_preserve_sem''_IH_on e1.
            apply_type_sound2 e1.
            lazymatch goal with
              H: consistent _ ?v ?v', H': type_of_value ?v _ |- _ =>
                let H'' := fresh in
                eapply consistent__type_of_value in H' as H''; eauto end.
            use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints.
            rewrite consistent_Renv_put; apply locals_related_step; auto. }
        1:{ use_transf_to_idx_preserve_sem''_IH_on e1.
            apply_type_sound_consistent_value e1.
            apply flat_map_preserve_consistent; auto; intros. apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH; [ | eauto with fiat2_hints | .. ].
            4: rewrite consistent_Renv_put; apply locals_related_step; [ eauto | ].
            1: apply_type_sound_consistent_value e2; eauto with fiat2_hints.
            1,2: eapply type_sound; eauto with fiat2_hints.
            1,2: apply locals_wf_step; auto.
            1: apply consistent_refl. }
        1:{ use_transf_to_idx_preserve_sem''_IH_on e1.
            lazymatch goal with
              H: consistent LikeList _ _ |- _ =>
                rewrite consistent_LikeList_eq in H; rewrite <- H
            end.
            apply_type_sound2 e1. invert_type_of_value. rewrite_expr_value.
            use_transf_to_idx_preserve_sem''_IH_on e2. apply_type_sound2 e2.
            eapply consistent_step; eauto.
            repeat lazymatch goal with
                     H: VList _ = _ |- _ => clear H end.
            induction l; simpl.
            1: eapply consistent_step; eauto.
            1:{ invert_Forall.
                use_transf_to_idx_preserve_sem''_IH_on e3; eauto.
                1: repeat apply tenv_wf_step; eauto with fiat2_hints.
                1,2: repeat apply locals_wf_step; auto;
                eapply fold_right__type_of_value; eauto using consistent__type_of_value; intros.
                1:{ eapply type_sound; eauto with fiat2_hints.
                    repeat apply tenv_wf_step; eauto with fiat2_hints. }
                1:{ use_transf_to_idx_preserve_sem''_IH_on e3; eauto.
                    1: eapply consistent__type_of_value; eauto.
                    5: repeat rewrite consistent_Renv_put; repeat apply locals_related_step;
                    eauto using consistent_refl.
                    1: apply_type_sound2 e3.
                    all: repeat apply tenv_wf_step; eauto with fiat2_hints. }
                1:{ repeat rewrite consistent_Renv_put.
                    repeat apply locals_related_step; auto using consistent_refl.
                    apply IHl; auto. constructor; auto. } } }
        1:{ lazymatch goal with
            H1: map fst _ = _, H2: Forall2 (type_of _ _) _ _, H3: Permutation _ _,
                  H4: NoDup _, H5: Sorted.StronglySorted _ _ |- _ =>
              clear H1 H2 H3 H4 H5 end.
            apply consistent_step with (i2:=LikeList).
            2: destruct i; auto.
            rewrite consistent_LikeList_eq. do 2 f_equal.
            generalize dependent tl. induction l; simpl; auto using consistent_refl; intros.
            invert_Forall; invert_Forall2; repeat case_match; f_equal; simpl in *.
            1:{ f_equal. use_transf_to_idx_preserve_sem''_IH. }
            1:{ destruct tl; simpl in *; try congruence; invert_cons.
                lazymatch goal with
                  H: Forall _ l |- _ => eapply IHl in H; eauto end.
                constructor; auto. } }
        1:{ eapply consistent_step.
            1: apply consistent_LikeList_eq; auto.
            2: destruct i; auto.
            do 3 f_equal. induction l; simpl; auto.
            case_match; repeat invert_Forall; simpl in *.
            f_equal.
            2: apply IHl; auto; constructor; auto.
            intuition auto.
            repeat (lazymatch goal with
                    | IH:context [ consistent _ (interp_expr _ _ ?e) ], H:tag_of _ _ ?e _ |- _ => eapply IH in H
                    end; [ | | | | | | eauto | eauto ]; auto).
            rewrite consistent_LikeList_eq in *. congruence. }
        1:{ use_transf_to_idx_preserve_sem''_IH;
            rewrite consistent_LikeList_eq in *; repeat rewrite_r_to_l.
            apply_type_sound2 e. invert_type_of_value.
            all: use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints.
            rewrite consistent_Renv_put. apply locals_related_step; auto using consistent_refl. }
        1:{ use_transf_to_idx_preserve_sem''_IH;
            rewrite consistent_LikeList_eq in *; repeat rewrite_r_to_l.
            apply_type_sound2 d. invert_type_of_value.
            eapply consistent_step;
              [ apply consistent_LikeList_eq; auto
              |  destruct i; auto ].
            use_transf_to_idx_preserve_sem''_IH_on e0.
            apply_type_sound2 e0.
            rewrite consistent_LikeList_eq in *. repeat rewrite_r_to_l.
            eapply In_fold_right_ext with (P:=fun v => type_of_value v t); intros.
            2:{ apply_Forall_In. split.
                1:{ use_transf_to_idx_preserve_sem''_IH; eauto with fiat2_hints.
                    1,2: repeat apply locals_wf_step; intuition auto.
                    1:{ repeat rewrite consistent_Renv_put.
                        repeat apply locals_related_step; auto using consistent_refl. } }
                eapply type_sound; eauto with fiat2_hints.
                repeat apply locals_wf_step; intuition auto. }
            eapply type_sound; eauto. }
        1:{ destruct i; unfold glb in *; simpl in *.
            all: use_transf_to_idx_preserve_sem''_IH;
              apply_type_sound_consistent_value l; simpl in *.
            1: eapply Permutation_dedup_Permuted; eauto using Permuted_value_sort.
            1: eauto using perm_trans, Permuted_value_sort, Permutation_sym.
            1:{ f_equal. apply Permutation_SSorted_eq; auto using StronglySorted_value_sort.
                eauto using perm_trans, Permuted_value_sort, Permutation_sym. } }
        1:{ use_transf_to_idx_preserve_sem''_IH.
            apply_type_sound_consistent_value e.
            apply filter_preserve_consistent; auto.
            intros. apply_Forall_In.
            use_transf_to_idx_preserve_sem''_IH.
            1:{ rewrite consistent_LikeList_eq in *;
                lazymatch goal with
                  H: interp_expr _ _ p = _ |- _ => rewrite <- H
                end. eauto. }
            all: eauto with fiat2_hints.
            rewrite consistent_Renv_put. apply locals_related_step; auto using consistent_refl. }
        1:{ use_transf_to_idx_preserve_sem''_IH. apply_type_sound_consistent_value e1.
            use_transf_to_idx_preserve_sem''_IH. apply_type_sound_consistent_value e2.
            apply flat_map_preserve_consistent; auto; intros.
            apply map_preserve_consistent; auto; intros.
            2:{ use_transf_to_idx_preserve_sem''_IH.
                1: rewrite consistent_LikeList_eq in *; eauto.
                1: repeat apply tenv_wf_step; eauto with fiat2_hints.
                1,2: rewrite filter_In in *; intuition auto;
                repeat apply_Forall_In; repeat apply locals_wf_step; auto.
                1:{ repeat rewrite consistent_Renv_put.
                    repeat apply locals_related_step; auto using consistent_refl. } }
            apply filter_preserve_consistent; auto; intros.
            use_transf_to_idx_preserve_sem''_IH.
            1: rewrite consistent_LikeList_eq in *;
            lazymatch goal with
              H: interp_expr _ _ p = _ |- _ => rewrite <- H
            end; eauto.
            all: [> repeat apply tenv_wf_step; eauto with fiat2_hints
                 | repeat apply_Forall_In; repeat apply locals_wf_step; auto
                 | repeat apply_Forall_In; repeat apply locals_wf_step; auto
                 | repeat rewrite consistent_Renv_put;
                   repeat apply locals_related_step; auto using consistent_refl ]. }
        1:{ use_transf_to_idx_preserve_sem''_IH. apply_type_sound_consistent_value e.
            apply map_preserve_consistent; auto; intros.
            use_transf_to_idx_preserve_sem''_IH;
              [ rewrite consistent_LikeList_eq in *; eauto | .. ].
            all: [> repeat apply tenv_wf_step; eauto with fiat2_hints
                 | repeat apply_Forall_In; repeat apply locals_wf_step; auto
                 | repeat apply_Forall_In; repeat apply locals_wf_step; auto
                 | repeat rewrite consistent_Renv_put;
                   repeat apply locals_related_step; auto using consistent_refl ]. }
      Qed.

      Lemma put_consistent_Renv_put_same : forall istr x i R,
          map.put (consistent_Renv istr) x R = map.put (consistent_Renv (map.put istr x i)) x R.
      Proof.
        intros. rewrite consistent_Renv_put, Properties.map.put_put_same.
        reflexivity.
      Qed.

      Ltac use_transf_to_idx_preserve_sem'' :=
        eapply transf_to_idx_preserve_sem''; [ | | eauto | | | | eauto | .. ]; eauto;
        eapply collection_tag_leb_tran;
        eauto using aenv_le__collection_tag_leb, aenv_le__istr_inv.

      Ltac use_transf_to_idx_preserve_sem'_IH :=
        lazymatch goal with
          IH: context[locals_related _ (interp_command _ _ ?c) _] |-
            locals_related _ (interp_command _ _ ?c) _ =>
            eapply IH
        end.

      Lemma transf_to_idx_preserve_sem' : forall tbl tbl_ty c (Gstore Genv : tenv) free_vars,
          tenv_wf Gstore -> tenv_wf Genv ->
          well_typed Gstore Genv c ->
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          incl (get_free_vars Genv) free_vars ->
          forall (istr ienv inv istr_expect : aenv) (store store' env env': locals),
            collection_tag_leb (get_collection_tag inv tbl) to_from_con = true ->
            well_tagged istr ienv inv c istr_expect ->
            locals_wf Gstore store -> locals_wf Genv env ->
            locals_wf (map.put Gstore tbl (idx_ty tbl_ty)) store' -> locals_wf Genv env' ->
            locals_related (consistent_with_global_Renv tbl istr) store store' ->
            locals_related (consistent_Renv ienv) env env' ->
            locals_related (consistent_with_global_Renv tbl istr_expect) (interp_command store env c) (interp_command store' env' (transf_to_idx' free_vars tbl c)).
      Proof.
        intros * ? ? H. revert free_vars. induction H; simpl; intros.
        all: invert_well_tagged.
        1:{ eapply locals_related__Renv_le; eauto.
            apply aenv_le__consistent_with_global_Renv_le; auto. }
        1:{ use_transf_to_idx_preserve_sem'_IH; eauto.
            all: eapply command_type_sound; eauto.
            1: apply transf_to_idx_preserve_ty'; eauto with fiat2_hints.
            apply tenv_wf_step; auto. apply idx_ty_wf; auto. apply_tenv_wf; auto. }
        1:{ use_transf_to_idx_preserve_sem'_IH; eauto with fiat2_hints.
            1: apply_incl_lemmas.
            1:{ apply locals_wf_step; auto.
                eapply type_sound; [ | | eauto | eauto | ];
                  eauto using idx_ty_wf with fiat2_hints.
                apply transf_to_idx_preserve_ty''; auto. }
            rewrite consistent_Renv_put. apply locals_related_step; auto.
            use_transf_to_idx_preserve_sem''. }
        1:{ case_match_string_eqb.
            1:{ unfold consistent_with_global_Renv.
                erewrite put_consistent_Renv_put_same.
                apply locals_related_lifted_step.
                1:{ eapply locals_related__Renv_le.
                    1: apply Renv_le_refl.
                    eapply well_tagged_sound with (istr:=map.put istr tbl i); [ | | eauto | .. ]; eauto with fiat2_hints.
                    1:{ erewrite <- Properties.map.put_put_same. apply locals_wf_step; eauto.
                        eapply consistent__type_of_value;
                          [ eapply transf_to_idx_preserve_sem'' with (env:=env) | ];
                          [ | | eauto | | | | eauto | .. ]; eauto; [ | eapply type_sound; eauto ].
                        lazymatch goal with
                        | H: well_tagged istr _ inv _ _ |- _ =>
                            let H' := fresh in
                            apply aenv_le__istr_inv in H as H';
                            eapply aenv_le__collection_tag_leb in H';
                            eapply collection_tag_leb_tran; eauto
                        end. }
                    rewrite consistent_Renv_put. rewrite consistent_Renv_put_global.
                    apply locals_related_step; auto.
                    use_transf_to_idx_preserve_sem''. }
                1:{ apply_locals_related. unfold consistent_with_global_Renv in H12.
                    rewrite_map_get_put_hyp. apply_locals_wf store.
                    assert(map.get (map.put Gstore tbl (idx_ty tbl_ty)) tbl = Some (idx_ty tbl_ty)).
                    { rewrite_map_get_put_goal; auto. }
                    apply_locals_wf store'.
                    repeat destruct_match_hyp; intuition auto. simpl in *. destruct_exists.
                    eexists; intuition eauto.
                    lazymatch goal with H: aenv_le_at _ _ _ |- _ => apply aenv_le_at__collection_tag_leb in H end.
                    eapply consistent_step; eauto. } }
            1:{ apply locals_related_lifted_step2.
                1:{ eapply locals_related__Renv_le; eauto using consistent_with_global_Renv_put_local2.
                    use_transf_to_idx_preserve_sem'_IH; [ | | | | | | eauto | .. ]; eauto with fiat2_hints.
                    1: unfold get_collection_tag; rewrite_map_get_put_goal.
                    1:{ rewrite Properties.map.put_put_diff; auto. apply locals_wf_step; auto.
                        eapply type_sound. 1: apply transf_to_idx_preserve_ty''.
                        8: eauto. all: eauto using idx_ty_wf with fiat2_hints. }
                    eapply locals_related__Renv_le; [ apply consistent_with_global_Renv_put_local | ]; auto.
                    apply locals_related_step; auto.
                    use_transf_to_idx_preserve_sem''. }
                apply_locals_related. eapply lifted_related__Renv_le; eauto.
                unfold consistent_with_global_Renv; repeat rewrite_map_get_put_goal.
                apply aenv_le_at__R_le; auto. } }
        1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst; simpl.
            1:{ rewrite_l_to_r; do_injection. erewrite fiat2_gallina_to_idx.
                5: eapply transf_to_idx_preserve_ty''.
                9: eauto. all: eauto using idx_ty_wf with fiat2_hints.
                eapply Renv_le_except__locals_related; eauto.
                1:{ intros. unfold consistent_with_global_Renv; repeat rewrite_map_get_put_goal.
                    lazymatch goal with
                      H: aenv_le ?istr _ |- context[map.get (consistent_Renv ?istr) ?y] => specialize (H y) end.
                    unfold aenv_le_at in *. rewrite_map_get_put_hyp.
                    repeat rewrite consistent_Renv_sound.
                    repeat case_match; intuition auto using R_le_refl, collection_tag_leb__R_le.
                    unfold R_le, lifted_related; intros. repeat case_match; auto. }
                unfold consistent_with_global_Renv; repeat rewrite_map_get_put_goal; simpl.
                eexists; intuition eauto. use_transf_to_idx_preserve_sem''. }
            1:{ eapply locals_related__Renv_le.
                2:{ apply locals_related_step; eauto. use_transf_to_idx_preserve_sem''. }
                eapply Renv_le_tran.
                2: apply consistent_with_global_Renv_put_local; auto.
                apply aenv_le__consistent_with_global_Renv_le.
                unfold aenv_le, aenv_le_at; intro y. destruct_get_put_strings.
                1:{ unfold get_collection_tag; case_match; auto.
                    destruct c; auto. }
                1:{ lazymatch goal with
                    H: aenv_le ?istr _ |- context[map.get ?istr ?y] => specialize (H y) end.
                    unfold aenv_le_at in *. rewrite_map_get_put_hyp. } } }
        1:{ lazymatch goal with H: tag_of _ _ _ _ |- _ => eapply transf_to_idx_preserve_sem'' in H end.
            10-13: eauto. all: eauto.
            1: rewrite consistent_LikeList_eq in *; repeat rewrite_r_to_l;
            apply_type_sound2 e; invert_type_of_value;
            case_match; use_transf_to_idx_preserve_sem'_IH; eauto.
            eapply collection_tag_leb_tran;
              eauto using aenv_le__collection_tag_leb, aenv_le__istr_inv. }
        1:{ lazymatch goal with
              H: tag_of _ _ _ _ |- _ =>
                let H' := fresh in
                eapply transf_to_idx_preserve_sem'' in H as H' end.
            1: rewrite consistent_LikeList_eq in H14.
            10-13: eauto. all: eauto.
            2: eapply collection_tag_leb_tran;
            eauto using aenv_le__collection_tag_leb, aenv_le__istr_inv.
            rewrite <- H14. apply_type_sound2 e. invert_type_of_value.
            eapply locals_related__Renv_le; eauto using aenv_le__consistent_with_global_Renv_le.
            lazymatch goal with H: VList _ = _, H1: interp_expr _ _ _ = interp_expr _ _ _ |- _ => clear H H1 end.
            destruct l; simpl.
            1: eapply locals_related__Renv_le; eauto using aenv_le__consistent_with_global_Renv_le.
            eapply locals_related__Renv_le in H12; [ | apply aenv_le__consistent_with_global_Renv_le; eauto ].
            generalize dependent v; generalize dependent store'; generalize dependent store.
            induction l; simpl; intros;  invert_Forall.
            1:{ use_transf_to_idx_preserve_sem'_IH; [ | | | | | | eauto | .. ]; eauto with fiat2_hints.
                1: apply_incl_lemmas.
                rewrite consistent_Renv_put.
                1: apply locals_related_step; auto using consistent_refl. }
            1:{ apply IHl; intuition auto.
                1: eapply command_type_sound; eauto with fiat2_hints.
                1:{ eapply type_sound; eauto. eapply command_type_sound; eauto with fiat2_hints. }
                1:{ eapply command_type_sound.
                    1: apply transf_to_idx_preserve_ty'; [ | | | | eauto | .. ].
                    all: eauto using idx_ty_wf with fiat2_hints.
                    apply_incl_lemmas. }
                1:{ use_transf_to_idx_preserve_sem'_IH; [ | | | | | eauto | .. ]; eauto with fiat2_hints.
                    1: apply_incl_lemmas.
                    rewrite consistent_Renv_put. apply locals_related_step; auto using consistent_refl. } } }
      Qed.

      Lemma consistent_tenv_LikeList : forall tbl Gstore store store' x t,
          locals_related (consistent_with_global_Renv tbl (map.put (make_LikeList_aenv Gstore) tbl LikeSet)) store store' ->
          x <> tbl -> map.get Gstore x = Some t -> map.get store x = map.get store' x.
      Proof.
        unfold locals_related, consistent_with_global_Renv; intros.
        specialize (H x). unfold lifted_related in *.
        repeat destruct_match_hyp; intuition auto; try congruence.
        all: rewrite_map_get_put_hyp; rewrite consistent_Renv_sound in *;
        rewrite_map_get_put_hyp.
        all: erewrite make_LikeList_aenv_sound in *; eauto.
        1: do_injection.
        all: congruence.
      Qed.

      Lemma put_to_idx__consistent_with_global : forall tbl istr e Gstore Genv store env t free_vars,
          is_tbl_ty t = true ->
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv e t ->
          incl (get_free_vars Genv) free_vars ->
          locals_wf Gstore store -> locals_wf Genv env ->
          locals_related (consistent_with_global_Renv tbl istr) (map.put store tbl (interp_expr store env e)) (map.put store tbl (interp_expr store env (substitute ((hole, e) :: nil) free_vars to_idx))).
      Proof.
        intros. unfold locals_related, consistent_with_global_Renv; intros.
        destruct_get_put_strings.
        1:{ eexists; intuition eauto using consistent_refl.
            eapply fiat2_gallina_to_idx; [ | | | eauto | .. ]; eauto using incl_refl. }
        1:{ unfold lifted_related. rewrite consistent_Renv_sound.
            repeat case_match; auto using consistent_refl. }
      Qed.

      Lemma make_LikeList_aenv__domain_incl : forall Gstore,
          domain_incl Gstore (make_LikeList_aenv Gstore).
      Proof.
        unfold domain_incl; intros. case_match; auto.
        erewrite make_LikeList_aenv_sound; eauto.
      Qed.

      Lemma transf_to_idx_preserve_sem : forall tbl_ty tbl e c (Gstore Genv : tenv) free_vars,
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv e tbl_ty ->
          well_typed (map.put Gstore tbl tbl_ty) Genv c ->
          can_transf_to_index to_from_con tbl_ty (make_LikeList_aenv Gstore) (CLetMut e tbl c) = true ->
          incl (get_free_vars Genv) free_vars ->
          forall (store env : locals),
            locals_wf Gstore store -> locals_wf Genv env ->
            interp_command store env (transf_to_idx free_vars (CLetMut e tbl c)) = interp_command store env (CLetMut e tbl c).
      Proof.
        simpl; intros. subst.
        rewrite Bool.andb_true_iff in *; intuition auto.
        unfold can_transf_to_index' in *. destruct_match_hyp.
        apply stores_eq_except__update_eq.
        intros. eapply command_tag_req_sound in E; eauto using domain_incl_step, make_LikeList_aenv__domain_incl.
        destruct (map.get Gstore x) eqn:E_x.
        1:{ symmetry. eapply consistent_tenv_LikeList; eauto.
            eapply transf_to_idx_preserve_sem' with (Gstore:=map.put Gstore tbl tbl_ty); eauto.
            all: try rewrite_map_get_put_goal; eauto with fiat2_hints.
            1: unfold get_collection_tag; repeat destruct_match_hyp; simpl; congruence.
            1:{ rewrite Properties.map.put_put_same. apply locals_wf_step; auto.
                eapply type_sound. 1: apply to_idx_preserve_ty; auto.
                1: eapply type_of__type_wf; [ | | eauto ]; auto.
                3: eauto. all: auto. }
            1:{ eapply put_to_idx__consistent_with_global. 4: eauto. all: auto. }
            1: apply locals_related_consistent_Renv_refl. }
        1:{ repeat erewrite command_preserve_untouched_store. 4: eauto.
            9: apply transf_to_idx_preserve_ty' with (Gstore:=map.put Gstore tbl tbl_ty); eauto.
            all: repeat rewrite_map_get_put_goal; eauto with fiat2_hints.
            1:{ apply tenv_wf_step; eauto with fiat2_hints. apply idx_ty_wf; eauto with fiat2_hints. }
            1:{ rewrite Properties.map.put_put_same.
                apply locals_wf_step; auto. eapply type_sound. 1: apply to_idx_preserve_ty.
                1: eapply type_of__type_wf; [ | | eauto ]; auto.
                4: eauto. all: auto. } }
      Qed.

      Print Assumptions transf_to_idx_preserve_sem.

      Lemma transf_to_idx_preserve_sem2 : forall tbl_ty tbl e e' c c' (Gstore Genv : tenv) free_vars,
          tenv_wf Gstore -> tenv_wf Genv ->
          type_of Gstore Genv e' tbl_ty ->
          well_typed (map.put Gstore tbl tbl_ty) Genv c' ->
          can_transf_to_index to_from_con tbl_ty (make_LikeList_aenv Gstore) (CLetMut e' tbl c') = true ->
          incl (get_free_vars Genv) free_vars ->
          forall (store env : locals),
            locals_wf Gstore store -> locals_wf Genv env ->
            interp_command store env (CLetMut e tbl c) = interp_command store env (CLetMut e' tbl c') ->
            interp_command store env (CLetMut e tbl c) = interp_command store env (transf_to_idx free_vars (CLetMut e' tbl c')).
      Proof.
        intros. symmetry. rewrite H7. eapply transf_to_idx_preserve_sem.
        3-8: eauto.
        all: auto.
      Qed.
    End WithRelMap.

    Lemma to_idx_satisfy_idx_wf : forall free_vars e Gstore Genv t store env,
        tenv_wf Gstore -> tenv_wf Genv ->
        type_of Gstore Genv e t ->
        is_tbl_ty t = true ->
        incl (get_free_vars Genv) free_vars ->
        locals_wf Gstore store -> locals_wf Genv env ->
        idx_wf (interp_expr store env (substitute ((hole, e) :: nil) free_vars to_idx)).
    Proof.
      intros. erewrite substitute_preserve_sem with (Genv0:=map.put map.empty hole t).
      5: eauto. 8,9: eauto. all: auto.
      3: eapply type_of_strengthen; try apply to_idx_ty.
      all: eauto using tenv_wf_empty with fiat2_hints.
      3: apply map_incl_step; try apply string_dec.
      2,3: apply map_incl_empty.
      2:{ unfold sub_wf; intros. simpl.
          case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst;
            rewrite_map_get_put_hyp;
            [ do_injection; auto
            | rewrite map.get_empty in *; discriminate ]. }
      erewrite interp_expr_strengthen; [ eapply to_idx_wf | .. ].
      6: apply to_idx_ty.
      all: eauto using tenv_wf_empty, locals_wf_empty with fiat2_hints.
      1: apply map_incl_empty.
      1: simpl; apply map_incl_step; auto using string_dec, map_incl_empty.
    Qed.

    Definition holds_for_all_entries {A : Type} {m : map.map string A} (P : string -> A -> Prop) (G : m) :=
      forall k v, map.get G k = Some v -> P k v.

    Definition rm_from_pred (P : string -> value -> Prop) (x : string) :=
      fun s v => s = x \/ P s v.

    Inductive parameterized_wf (Gstore Genv : tenv) (P : string -> value -> Prop) : command -> Prop :=
    | PWCSkip : parameterized_wf Gstore Genv P CSkip
    | PWCSeq c1 c2 : parameterized_wf Gstore Genv P c1 ->
                     parameterized_wf Gstore Genv P c2 ->
                     parameterized_wf Gstore Genv P (CSeq c1 c2)
    | PWCLet e t x c : type_of Gstore Genv e t ->
                       parameterized_wf Gstore (map.put Genv x t) P c ->
                       parameterized_wf Gstore Genv P (CLet e x c)
    | PWCLetMut e t x c :
      type_of Gstore Genv e t ->
      parameterized_wf (map.put Gstore x t) Genv (rm_from_pred P x) c ->
      parameterized_wf Gstore Genv P (CLetMut e x c)
    | PWCAssign x t e :
      (forall store env, holds_for_all_entries P store ->
                         locals_wf Gstore store -> locals_wf Genv env ->
                         P x (interp_expr store env e)) ->
      map.get Gstore x = Some t ->
      type_of Gstore Genv e t ->
      parameterized_wf Gstore Genv P (CAssign x e)
    | PWCIf e c1 c2 : type_of Gstore Genv e TBool ->
                      parameterized_wf Gstore Genv P c1 ->
                      parameterized_wf Gstore Genv P c2 ->
                      parameterized_wf Gstore Genv P (CIf e c1 c2)
    | PWCForeach e t x c : type_of Gstore Genv e (TList t) ->
                           parameterized_wf Gstore (map.put Genv x t) P c ->
                           parameterized_wf Gstore Genv P (CForeach e x c).

    Lemma parameterized_wf__well_typed : forall Gstore Genv P c,
        parameterized_wf Gstore Genv P c -> well_typed Gstore Genv c.
    Proof.
      intros. induction H.
      all: econstructor; eauto.
    Qed.

    Hint Resolve type_sound : fiat2_hints.

    Ltac get_update_same_diff x y :=
      let E := fresh "E" in
      destruct (String.eqb x y) eqn:E;
      [ rewrite eqb_eq in E; subst; repeat rewrite Properties.map.get_update_same
      | rewrite eqb_neq in E; repeat rewrite Properties.map.get_update_diff ]; auto.

    Ltac get_put_same_diff x y :=
      let E := fresh "E" in
      destruct (String.eqb x y) eqn:E;
      [ rewrite eqb_eq in E; subst; repeat rewrite map.get_put_same
      | rewrite eqb_neq in E; repeat rewrite map.get_put_diff ]; auto.

    Lemma parameterized_wf__preserve_P : forall Gstore Genv store env P c,
        tenv_wf Gstore -> tenv_wf Genv ->
        parameterized_wf Gstore Genv P c ->
        locals_wf Gstore store -> locals_wf Genv env ->
        holds_for_all_entries P store ->
        holds_for_all_entries P (interp_command store env c).
    Proof.
      intros. generalize dependent store; generalize dependent env.
      induction H1; simpl; auto; intros.
      1:{ apply IHparameterized_wf2; auto. eapply command_type_sound; eauto.
          eapply parameterized_wf__well_typed; eauto. }
      1:{ apply IHparameterized_wf; eauto with fiat2_hints. }
      1:{ unfold holds_for_all_entries. intros. get_update_same_diff x k.
          1:{ rewrite Properties.map.get_update_same in *. auto. }
          1:{ rewrite Properties.map.get_update_diff in *; try congruence.
              unfold rm_from_pred in *.
              apply IHparameterized_wf in H6; eauto with fiat2_hints.
              1:{ intuition auto. congruence. }
              unfold holds_for_all_entries; intros.
              get_put_same_diff x k0; rewrite_map_get_put_hyp. } }
      1:{ unfold holds_for_all_entries; intros.
          get_put_same_diff x k; rewrite_map_get_put_hyp.
          do_injection. apply H1; auto. }
      1:{ apply_type_sound e. invert_type_of_value. case_match; auto. }
      1:{ apply_type_sound e. invert_type_of_value. clear H' H6.
          generalize dependent store. induction l; simpl; auto; intros.
          invert_Forall; apply IHl; auto.
          2:{ apply IHparameterized_wf; eauto with fiat2_hints. }
          eapply command_type_sound.
          5: apply locals_wf_step. all: eauto with fiat2_hints.
          eapply parameterized_wf__well_typed; eauto. }
    Qed.


    Definition preserve_param_wf Gstore Genv (P : string -> value -> Prop) f :=
      forall c, parameterized_wf Gstore Genv P c -> parameterized_wf Gstore Genv P (f c).

    Lemma compose_op_transf_preserve_parameterized_wf :
      forall Gstore Genv P f g,
        preserve_param_wf Gstore Genv P f ->
        preserve_param_wf Gstore Genv P g ->
        preserve_param_wf Gstore Genv P (fun c => g (f c)).
    Proof.
      unfold preserve_param_wf; auto.
    Qed.

    Definition command_wf_preserve_sem Gstore Genv P f :=
      forall (store env : locals) c,
        locals_wf Gstore store -> locals_wf Genv env ->
        parameterized_wf Gstore Genv P c ->
        holds_for_all_entries P store ->
        interp_command store env c = interp_command store env (f c).

    Lemma compose_op_transf_preserve_sem : forall Gstore Genv (P : string -> value -> Prop) f g,
        preserve_param_wf Gstore Genv P g ->
        command_wf_preserve_sem Gstore Genv P f ->
        command_wf_preserve_sem Gstore Genv P g ->
        command_wf_preserve_sem Gstore Genv P (fun c => f (g c)).
    Proof.
      unfold command_wf_preserve_sem; intros.
      rewrite H1, H0; auto.
    Qed.

    Definition index_wf_with_globals globals (x : string) (v : value) :=
      Forall (fun tbl => x <> tbl \/ idx_wf v) globals.

    Lemma holds_for_all_entries_singleton_put : forall tbl store v,
        idx_wf v ->
        holds_for_all_entries (index_wf_with_globals (tbl :: nil))
          (map.put store tbl v).
    Proof.
      constructor; intuition auto.
      lazymatch goal with
            |- context[?x = ?y] =>
              let E := fresh "E" in
              destruct (String.eqb x y) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *; subst;
              intuition auto; right; rewrite_map_get_put_hyp
      end. congruence.
    Qed.

    Lemma CLetMut_Proper2 : forall Gstore Genv (store env : locals) tbl_ty e tbl f c,
        tenv_wf Gstore -> tenv_wf Genv ->
        is_tbl_ty tbl_ty = true -> type_wf tbl_ty ->
        type_of Gstore Genv e (idx_ty tbl_ty) ->
        parameterized_wf (map.put Gstore tbl (idx_ty tbl_ty)) Genv (index_wf_with_globals (tbl::nil)) c ->
        (forall store env,
            locals_wf Gstore store -> locals_wf Genv env ->
            idx_wf (interp_expr store env e)) ->
        (forall store' env c,
            locals_wf (map.put Gstore tbl (idx_ty tbl_ty)) store' -> locals_wf Genv env ->
            parameterized_wf (map.put Gstore tbl (idx_ty tbl_ty)) Genv (index_wf_with_globals (tbl::nil)) c ->
            holds_for_all_entries (index_wf_with_globals (tbl::nil)) store' ->
            interp_command store' env c = interp_command store' env (f c)) ->
        locals_wf Gstore store -> locals_wf Genv env ->
        interp_command store env (CLetMut e tbl c) = interp_command store env (CLetMut e tbl (f c)).
    Proof.
      intros. simpl.
      f_equal. apply H6.
      all: eauto with fiat2_hints.
      unfold holds_for_all_entries; intros.
      unfold index_wf_with_globals; constructor; auto.
      destruct (String.eqb k tbl) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *;
        subst; intuition auto.
      right. rewrite_map_get_put_hyp. do_injection.
      apply H5; auto.
    Qed.

    Lemma well_typed__index_wf_nil : forall c Gstore Genv,
        tenv_wf Gstore -> tenv_wf Genv ->
        well_typed Gstore Genv c ->
        forall P,
          (forall x v, P x v <-> index_wf_with_globals nil x v) ->
          parameterized_wf Gstore Genv P c.
    Proof.
      induction 3; intros.
      all: try now (constructor; auto).
      1:{ econstructor; eauto. apply IHwell_typed; eauto with fiat2_hints. }
      1:{ econstructor; eauto. apply IHwell_typed; eauto with fiat2_hints.
          intros. split.
          1: constructor.
          1:{ unfold rm_from_pred. intros; right. rewrite H3. constructor. } }
      1:{ econstructor; eauto. intros. rewrite H3; constructor. }
      1:{ econstructor; eauto. apply IHwell_typed; eauto with fiat2_hints. }
    Qed.

    Lemma rm_from_index_wf__index_wf_nil : forall (tbl x : string) (v : value),
        rm_from_pred (index_wf_with_globals (tbl :: nil)) tbl x v <-> index_wf_with_globals nil x v.
    Proof.
      intros. split.
      1: constructor.
      1:{ intros. unfold rm_from_pred.
          destruct (String.eqb x tbl) eqn:E; rewrite ?eqb_eq, ?eqb_neq in *;
            subst; intuition auto.
          right. constructor; auto. }
    Qed.

    Ltac apply_transf_to_idx'_index_wf_IH :=
      lazymatch goal with
        IH: context[parameterized_wf _ _ _ (transf_to_idx' _ _ ?c)] |- context[?c] =>
          apply IH
      end.

    Definition iff2 {A B} (P Q : A -> B -> Prop) :=
      forall a b, P a b <-> Q a b.


    Lemma iff2_refl : forall A B (P : A -> B -> Prop),
        iff2 P P.
    Proof.
      unfold iff2; intros; intuition auto.
    Qed.

    Lemma iff2_sym : forall A B (P Q : A -> B -> Prop),
        iff2 P Q -> iff2 Q P.
    Proof.
      unfold iff2; intros; apply iff_sym; auto.
    Qed.

    Lemma iff2_trans : forall A B (P Q R : A -> B -> Prop),
        iff2 P Q -> iff2 Q R -> iff2 P R.
    Proof.
      unfold iff2; split; intros.
      1: apply H0, H; auto.
      1: apply H, H0; auto.
    Qed.

    Add Parametric Relation A B : (A -> B -> Prop) iff2
        reflexivity proved by (iff2_refl A B)
        symmetry proved by (iff2_sym A B)
        transitivity proved by (iff2_trans A B)
        as iff2_rel.


    Instance rm_from_pred_Proper : Proper (iff2 ==> eq ==> iff2) rm_from_pred.
    Proof.
      intros P Q H x x' Hx.
      unfold iff2, rm_from_pred; intros.
      subst; intuition auto.
      all: right; apply H; auto.
    Qed.

    Instance holds_for_all_entries_Proper {A : Type} {m : map.map string A} : Proper (iff2 ==> eq ==> iff) (holds_for_all_entries (m:=m)).
    Proof.
      intros P Q H x x' Hx.
      unfold holds_for_all_entries. split; intros.
      all: subst; apply H, H0; auto.
    Qed.

    Lemma iff2_parameterized_wf : forall x y z P Q,
        iff2 P Q ->
        parameterized_wf x y P z -> parameterized_wf x y Q z.
    Proof.
      intros * H_iff2 H_wf. generalize dependent Q.
      induction H_wf; intros.
      all: econstructor; eauto.
      1:{ apply IHH_wf. erewrite H_iff2; auto using iff2_refl. }
      1:{ intros. apply H_iff2, H; auto.
          rewrite H_iff2; auto. }
    Qed.

    Instance parameterized_wf_Proper : Proper (eq ==> eq ==> iff2 ==> eq ==> iff) parameterized_wf.
    Proof.
      intros x x' Hx y y' Hy P Q H z z' Hz.
      split; subst; apply iff2_parameterized_wf;
        auto using iff2_sym.
    Qed.

    Lemma rm_not_in_globals : forall x globals,
        ~In x globals ->
        iff2 (rm_from_pred (index_wf_with_globals globals) x) (index_wf_with_globals globals).
    Proof.
      unfold iff2, rm_from_pred, index_wf_with_globals; intros.
      induction globals; intuition auto; subst.
      rewrite Forall_forall; intros.
      left. intro contra; subst; auto.
    Qed.

    Lemma transf_to_idx'_index_wf : forall tbl tbl_ty c free_vars Gstore Genv,
        tenv_wf Gstore -> tenv_wf Genv ->
        map.get Gstore tbl = Some tbl_ty ->
        is_tbl_ty tbl_ty = true ->
        well_typed Gstore Genv c ->
        incl (get_free_vars Genv) free_vars ->
        parameterized_wf (map.put Gstore tbl (idx_ty tbl_ty)) Genv (index_wf_with_globals (tbl :: nil)) (transf_to_idx' free_vars tbl c).
    Proof.
      induction c; simpl in *; intros.
      all: invert_well_typed.
      all: unfold is_true in *; repeat rewrite Bool.andb_true_iff in *; intuition.
      1: constructor.
      1: constructor; apply_transf_to_idx'_index_wf_IH; auto.
      1:{ econstructor.
          2: apply_transf_to_idx'_index_wf_IH; eauto; intuition auto.
          2: eauto with fiat2_hints.
          2: apply_incl_lemmas.
          apply transf_to_idx_preserve_ty''; auto; simpl; intuition. }
      1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          all: econstructor; [ apply transf_to_idx_preserve_ty''; eauto | ].
          1:{ rewrite Properties.map.put_put_same.
              apply well_typed__index_wf_nil; eauto with fiat2_hints.
              apply rm_from_index_wf__index_wf_nil. }
          1:{ rewrite Properties.map.put_put_diff; auto.
              rewrite rm_not_in_globals.
              2:{ intro contra. inversion contra; auto. }
              apply IHc; eauto with fiat2_hints.
              rewrite_map_get_put_goal. } }
      1:{ case_match; rewrite ?eqb_eq, ?eqb_neq in *; subst.
          1:{ econstructor.
              2: rewrite_map_get_put_goal; eauto.
              2:{ apply to_idx_preserve_ty; eauto using idx_ty_wf with fiat2_hints.
                  rewrite_l_to_r. do_injection.
                  apply transf_to_idx_preserve_ty''; auto. }
              intros. unfold index_wf_with_globals. constructor; auto. right.
              lazymatch goal with H: ?x = _, H': ?x = _ |- _ => rewrite H in H' end.
              do_injection; auto.
              eapply to_idx_satisfy_idx_wf; [ | | apply transf_to_idx_preserve_ty'' | .. ].
              7: eauto. all: eauto using idx_ty_wf with fiat2_hints. }
          1:{ econstructor.
              2: rewrite_map_get_put_goal; eauto.
              2: apply transf_to_idx_preserve_ty''; auto.
              intros. unfold index_wf_with_globals. constructor; auto. } }
      1:{ constructor; try apply_transf_to_idx'_index_wf_IH; intuition.
          apply transf_to_idx_preserve_ty''; auto. }
      1:{ econstructor; eauto.
          1: apply transf_to_idx_preserve_ty''; eauto.
          apply_transf_to_idx'_index_wf_IH; eauto with fiat2_hints.
          apply_incl_lemmas. }
    Qed.

    Lemma transf_to_idx'_index_wf2 : forall tbl tbl_ty c free_vars Gstore Gstore' Genv,
          tenv_wf Gstore -> tenv_wf Genv ->
          map.get Gstore tbl = Some tbl_ty ->
          is_tbl_ty tbl_ty = true ->
          well_typed Gstore Genv c ->
          incl (get_free_vars Genv) free_vars ->
          Gstore' = map.put Gstore tbl (idx_ty tbl_ty) ->
          parameterized_wf Gstore' Genv
            (index_wf_with_globals (tbl :: nil)) (transf_to_idx' free_vars tbl c).
    Proof.
      intros; subst; apply transf_to_idx'_index_wf; auto.
    Qed.
  End LikeDictIndex.
End WithMap.
