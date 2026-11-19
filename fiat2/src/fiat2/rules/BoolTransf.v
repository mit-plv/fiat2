Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem fiat2.TypeSound
  fiat2.Utils fiat2.TransfSound.
Require Import coqutil.Map.Interface.
From Stdlib Require Import String.

Definition and_true_of (e : expr) : option expr :=
  match e with
  | EBinop OAnd e1 (EAtom (ABool true)) => Some e1
  | EBinop OAnd (EAtom (ABool true)) e2 => Some e2
  | _ => None
  end.

Definition and_true_head (e : expr) : expr :=
  match and_true_of e with
  | Some e' => e'
  | None => e
  end.

Lemma and_true_of_spec : forall e e',
    and_true_of e = Some e' ->
    e = EBinop OAnd e' (EAtom (ABool true)) \/ e = EBinop OAnd (EAtom (ABool true)) e'.
Proof.
  unfold and_true_of; intros * H.
  repeat (destruct_match_hyp; try discriminate); injection H as <-; auto.
Qed.

Section WithMap.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Theorem and_true_head_sound : expr_transf_sound (locals := locals) and_true_head.
  Proof.
    unfold expr_transf_sound, and_true_head; intros Gstore Genv e t H_Gs H_Ge H_e.
    destruct (and_true_of e) as [ e' | ] eqn:E; [ | split; [ exact H_e | intros; reflexivity ] ].
    apply and_true_of_spec in E as [ -> | -> ];
      inversion H_e; subst;
      lazymatch goal with H : type_of_binop OAnd _ _ _ |- _ => inversion H; subst; clear H end;
      split; try assumption; intros store env H_str H_env;
      lazymatch goal with
      | H : type_of _ _ e' TBool |- _ =>
          pose proof (type_sound _ _ _ _ H H_Gs H_Ge _ _ H_str H_env) as H_v
      end;
      cbn [interp_expr interp_binop interp_atom]; inversion H_v;
      cbn; rewrite ?Bool.andb_true_r; reflexivity.
  Qed.
End WithMap.
