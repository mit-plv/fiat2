Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound fiat2.Utils
  fiat2.TransfSound fiat2.Invariant fiat2.constraint.Surface fiat2.constraint.GuardRules
  fiat2.index.IndexInterface fiat2.index.CompoIndex fiat2.index.DictIndex
  fiat2.rules.CollectionTransf fiat2.rules.BoolTransf fiat2.rules.EraseField.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
From Stdlib Require Import List String.

(* The compiler: typecheck the elaborated program, run the passes that keep the
   invariant context, then the passes that only keep well-typedness. *)

Variant index_choice := DictIdx (attr : string).

Definition choice_idx (ic : index_choice) : string * IndexInterface.index :=
  match ic with
  | DictIdx attr => (String.append "dict_" attr, dict_idx attr)
  end.

Variant rule :=
  | Guard | AndTrue | IfConst | AnnotateCollection | PushDownCollection
  | DictSnoc | FoldCons | DictDelete | DictLookup | DictRead
  | CreateIdxs (tbl : string) (ics : list index_choice).

Section WithMap.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Definition run_passes (ps : list (tenv -> tenv -> command -> command)) (c : command) : command :=
    fold_left (fun c f => f map.empty map.empty c) ps c.

  Definition compile (ipasses fpasses : list (tenv -> tenv -> command -> command)) (sc : scommand)
    : result command :=
    match typecheck map.empty map.empty (elab nil sc) with
    | Success c => Success (run_passes fpasses (run_passes ipasses c))
    | Failure err => Failure err
    end.

  Lemma run_passes_cons : forall f ps c,
      run_passes (f :: ps) c = run_passes ps (f map.empty map.empty c).
  Proof. reflexivity. Qed.

  Lemma run_inv_passes : forall ps c,
      Forall (inv_transf_sound (locals := locals)) ps ->
      maintains_invs (locals := locals) map.empty map.empty nil (fun _ _ => True) c ->
      maintains_invs (locals := locals) map.empty map.empty nil (fun _ _ => True) (run_passes ps c) /\
        forall store env : locals, interp_command store env (run_passes ps c) = interp_command store env c.
  Proof.
    induction ps as [ | f ps IH ]; intros c H_ps H_c.
    1: split; [ exact H_c | reflexivity ].
    rewrite run_passes_cons. inversion H_ps as [ | ? ? H_f H_ps' ]; subst.
    destruct (H_f map.empty map.empty nil _ c tenv_wf_empty tenv_wf_empty (Forall_nil _) H_c) as [ H_c' H_sem ].
    destruct (IH _ H_ps' H_c') as [ H_r H_rsem ].
    split; [ exact H_r | ].
    intros store env. rewrite H_rsem. apply H_sem; auto using locals_wf_empty. constructor.
  Qed.

  Lemma run_wt_passes : forall ps c,
      Forall (transf_sound (locals := locals)) ps ->
      well_typed map.empty map.empty c ->
      well_typed map.empty map.empty (run_passes ps c) /\
        forall store env : locals, interp_command store env (run_passes ps c) = interp_command store env c.
  Proof.
    induction ps as [ | f ps IH ]; intros c H_ps H_c.
    1: split; [ exact H_c | reflexivity ].
    rewrite run_passes_cons. inversion H_ps as [ | ? ? H_f H_ps' ]; subst.
    destruct (H_f map.empty map.empty c tenv_wf_empty tenv_wf_empty H_c) as [ H_c' H_sem ].
    destruct (IH _ H_ps' H_c') as [ H_r H_rsem ].
    split; [ exact H_r | ].
    intros store env. rewrite H_rsem. apply H_sem; apply locals_wf_empty.
  Qed.

  Theorem compile_sound : forall ipasses fpasses sc c,
      Forall (inv_transf_sound (locals := locals)) ipasses ->
      Forall (transf_sound (locals := locals)) fpasses ->
      compile ipasses fpasses sc = Success c ->
      well_typed map.empty map.empty c /\
        forall store env : locals, interp_command store env c = interp_command store env (elab nil sc).
  Proof.
    unfold compile; intros * H_ip H_fp H_c.
    destruct (typecheck map.empty map.empty (elab nil sc)) as [ c0 | ] eqn:E; [ | discriminate ].
    injection H_c as <-.
    pose proof (elab_prog_maintains_invs (locals := locals) sc map.empty map.empty c0
                  tenv_wf_empty tenv_wf_empty E) as H_m.
    destruct (run_inv_passes ipasses c0 H_ip H_m) as [ H_m' H_isem ].
    destruct (run_wt_passes fpasses _ H_fp (maintains_invs__well_typed _ _ _ _ _ H_m')) as [ H_wt H_fsem ].
    split; [ exact H_wt | ].
    intros store env. rewrite H_fsem, H_isem.
    exact (command_typechecker_preserve_sem _ _ _ _ E store env).
  Qed.

  Corollary erase_dead_field_at_sound : forall tbl fld,
      transf_sound (locals := locals)
        (fun Gstore _ c => at_letmut tbl (fun Gstore c => erase_dead_field fld Gstore Gstore c) Gstore c).
  Proof.
    intros. apply at_letmut_wt_sound. exact (erase_dead_field_sound fld).
  Qed.

  Definition create_at (tbl : string) (ics : list index_choice) (c : command) : command :=
    match c with
    | CLetMut _ x _ _ _ =>
        if andb (String.eqb x tbl) (nodupb (List.map fst (List.map choice_idx ics)))
        then create_idxs (List.map choice_idx ics) "_h" "tbl" "idx" c
        else c
    | _ => c
    end.

  Definition expr_rule_of (r : rule) : list invariant -> tenv -> expr -> expr :=
    match r with
    | Guard => guard_rule
    | AndTrue => fun _ _ => and_true_head
    | AnnotateCollection => fun _ _ => annotate_collection
    | PushDownCollection => fun _ _ => push_down_collection
    | DictSnoc => fun _ _ => dict_snoc_head
    | FoldCons => fun _ _ => fold_cons_head
    | DictDelete => fun _ _ => dict_delete_head
    | DictLookup => dict_lookup_rule
    | DictRead => dict_read_rule
    | IfConst | CreateIdxs _ _ => fun _ _ e => e
    end.

  Definition cmd_rule_of (r : rule) : list invariant -> tenv -> command -> command :=
    match r with
    | IfConst => fun _ _ => if_const_head
    | CreateIdxs tbl ics => fun _ _ => create_at tbl ics
    | _ => fun _ _ c => c
    end.

  Definition pass_of (r : rule) : tenv -> tenv -> command -> command :=
    fun Gstore _ c => fold_command_with_ictx (expr_rule_of r) (cmd_rule_of r) nil Gstore c.

  Definition erase_pass (tf : string * string) : tenv -> tenv -> command -> command :=
    fun Gstore _ c => at_letmut (fst tf) (fun Gstore c => erase_dead_field (snd tf) Gstore Gstore c) Gstore c.

  Definition compile_with (rs : list rule) (es : list (string * string)) : scommand -> result command :=
    compile (List.map pass_of rs) (List.map erase_pass es).

  Lemma choice_idxs_ok : forall ics, Forall (fun '(_, idx) => IndexInterface.ok idx) (List.map choice_idx ics).
  Proof.
    intros. apply Forall_map, Forall_forall. intros [ attr ] _. apply dict_idx_ok.
  Qed.

  Lemma choice_idxs_holes : forall ics, Forall (fun '(_, idx) => @hole idx = "_h") (List.map choice_idx ics).
  Proof.
    intros. apply Forall_map, Forall_forall. intros [ attr ] _. reflexivity.
  Qed.

  Lemma create_at_sound : forall tbl ics, inv_transf_sound (locals := locals) (fun _ _ => create_at tbl ics).
  Proof.
    unfold inv_transf_sound; intros * H_Gs H_Ge H_ictx H_m.
    destruct c; try (split; [ exact H_m | intros; reflexivity ]). cbn [create_at].
    destruct (andb (String.eqb x tbl) (nodupb _)) eqn:E; [ | split; [ exact H_m | intros; reflexivity ] ].
    apply andb_prop in E as [ _ E ].
    exact (create_idxs_sound _ (idxs_ok := choice_idxs_ok ics) (nodupb_NoDup _ E) "_h" (choice_idxs_holes ics)
             "tbl" "idx" ltac:(discriminate) Gstore Genv ictx path_cond _ H_Gs H_Ge H_ictx H_m).
  Qed.

  Lemma expr_rule_of_sound : forall r, ictx_rule_sound (locals := locals) (expr_rule_of r).
  Proof.
    destruct r; cbn [expr_rule_of];
      try apply id_rule_sound; try apply guard_rule_sound; try apply dict_lookup_rule_sound;
      try apply dict_read_rule_sound; apply expr_transf__ictx_rule_sound.
    1: apply and_true_head_sound.
    1: apply annotate_collection_sound.
    1: apply push_down_collection_sound.
    1: apply dict_snoc_head_sound.
    1: apply fold_cons_head_sound.
    1: apply dict_delete_head_sound.
  Qed.

  Lemma cmd_rule_of_sound : forall r, ictx_cmd_rule_sound (locals := locals) (cmd_rule_of r).
  Proof.
    destruct r; cbn [cmd_rule_of]; try apply id_cmd_rule_sound; apply inv_transf__ictx_cmd_rule_sound.
    1: apply if_const_head_sound.
    1: apply create_at_sound.
  Qed.

  Lemma pass_of_sound : forall r, inv_transf_sound (locals := locals) (pass_of r).
  Proof.
    intros. apply fold_command_with_ictx_sound; [ apply expr_rule_of_sound | apply cmd_rule_of_sound ].
  Qed.

  Theorem compile_with_sound : forall rs es sc c,
      compile_with rs es sc = Success c ->
      well_typed map.empty map.empty c /\
        forall store env : locals, interp_command store env c = interp_command store env (elab nil sc).
  Proof.
    intros * H. eapply compile_sound; [ | | exact H ]; apply Forall_map, Forall_forall; intros.
    1: apply pass_of_sound.
    1: apply erase_dead_field_at_sound.
  Qed.
End WithMap.
