Require Import fiat2.Language fiat2.Interpret fiat2.Value fiat2.TypeSystem
  fiat2.TypeSound fiat2.Utils.
Require Import coqutil.Map.Interface coqutil.Datatypes.Result.
Require Import coqutil.Datatypes.String.
From Stdlib Require Import List String ZArith Permutation Sorted.
Import ListNotations.

Open Scope string_scope.

(* ------------------------------------------------------------------------
   SORTING BY A USER-SPECIFIED ATTRIBUTE ORDER, with no language change.

   `ESort` sorts by `value_leb`, the canonical order on values, and on
   records that order is LEXICOGRAPHIC IN FIELD-NAME ORDER:
   `record_compare` is `list_compare (pair_compare String.compare
   value_compare)` (Value.v:102), record values are kept sorted by name, and
   two records of one type have the same name sequence -- so every name
   comparison returns Eq and what is left is the values, compared in the
   order the names sort.

   That is normally a nuisance: it is exactly why `CompositeDictIdx` is
   `Unranged`, since a range over a record key would range on whichever
   attribute happens to sort first.  Here it is the mechanism.  `order by
   salary, age, name` elaborates to a projection onto a record whose field
   NAMES are generated to sort in the requested order,

     { a0_salary ; a1_age ; a2_name ; z_row }

   a single `ESort`, and a projection back out of `z_row`.  Nothing is added
   to the AST, the type system, the interpreter, or any rewrite rule, and a
   backend that already implements `ESort` implements this for free.

   What makes it more than a trick is the theorem at the bottom: the result
   is a PERMUTATION of the input and is SORTED with respect to
   `lex_leb attrs`, the lexicographic order on the listed attributes
   themselves.  Without that the naming convention would be an assertion.

   The generated names must sort in the order they were written, and
   `z_row` must sort after all of them.  That is a property of the ATTRIBUTE
   NAMES the user supplied, so it cannot be a theorem -- it is a boolean,
   `names_ok`, discharged by computation at each use site.  It FAILS loudly
   rather than silently misbehaving: with ten or more sort keys
   `String.of_nat` gives "a10_" < "a2_" and the check rejects it, which is
   the honest outcome (the fix is to pad the index, and the same check then
   accepts it).

   Two limits, stated here rather than discovered later.

   - DESCENDING is not expressible by renaming.  For an integer attribute a
     caller can project its negation and sort ascending, which is what
     `Netbox_ChangelogRetention` does for `-time` and `-pk`; for a string
     attribute there is no such move.
   - TIES are broken by the whole row (`z_row` is the last field), not left
     in input order.  A stable sort is not expressible in this language at
     all: `CollectionTransf` rewrites `ESort LikeList l` into
     `ESort LikeBag (EBagOf l)`, which discards the input order, so the
     limit is the existing design's and not this desugaring's. *)

(* the field a sort key at position i on attribute a is projected into *)
Definition key_name (i : nat) (a : string) : string :=
  "a" ++ String.of_nat i ++ "_" ++ a.

(* the field the whole row is carried in.  It must sort AFTER every
   generated key name, and does: every key name begins with "a". *)
Definition payload_name : string := "z_row".

Fixpoint key_names_from (i : nat) (attrs : list string) : list string :=
  match attrs with
  | [] => []
  | a :: attrs => key_name i a :: key_names_from (S i) attrs
  end.

Definition string_ltb (a b : string) : bool :=
  match String.compare a b with Lt => true | _ => false end.

Fixpoint all_ltb (a : string) (l : list string) : bool :=
  match l with
  | [] => true
  | b :: l => andb (string_ltb a b) (all_ltb a l)
  end.

(* strictly increasing, checked against EVERY later name rather than only
   the next one, so that no transitivity of String.compare is needed *)
Fixpoint names_strict (l : list string) : bool :=
  match l with
  | [] => true
  | a :: l => andb (all_ltb a l) (names_strict l)
  end.

Definition names_ok (attrs : list string) : bool :=
  names_strict (key_names_from 0 attrs ++ [payload_name]).

Section Desugaring.
  Notation value := (value).

  (* ---------------- the expression ---------------- *)
  Fixpoint key_fields_expr (i : nat) (r : string) (attrs : list string)
    : list (string * expr) :=
    match attrs with
    | [] => []
    | a :: attrs => (key_name i a, EAccess (EVar r) a) :: key_fields_expr (S i) r attrs
    end.

  Definition key_expr (r : string) (attrs : list string) : expr :=
    ERecord (key_fields_expr 0 r attrs ++ [(payload_name, EVar r)]).

  (* `order by attrs` : project, sort once, project back *)
  Definition sort_by (attrs : list string) (r p : string) (e : expr) : expr :=
    EFlatmap LikeList
      (ESort LikeList
         (EFlatmap LikeList e r
            (EBinop OCons (key_expr r attrs) (EAtom (ANil None)))))
      p (EBinop OCons (EAccess (EVar p) payload_name) (EAtom (ANil None))).

  (* ---------------- the Gallina counterpart ---------------- *)
  Fixpoint key_fields_val (i : nat) (attrs : list string) (rc : list (string * value))
    : list (string * value) :=
    match attrs with
    | [] => []
    | a :: attrs => (key_name i a, record_proj a rc) :: key_fields_val (S i) attrs rc
    end.

  Definition gallina_key (attrs : list string) (v : value) : value :=
    match v with
    | VRecord rc => VRecord (key_fields_val 0 attrs rc ++ [(payload_name, VRecord rc)])
    | _ => VUnit
    end.

  (* ---------------- what "sorted by attrs" means ---------------- *)
  Definition attr_vals (attrs : list string) (v : value) : list value :=
    match v with
    | VRecord rc => List.map (fun a => record_proj a rc) attrs
    | _ => []
    end.

  Definition lex_leb (attrs : list string) (u v : value) : bool :=
    leb_from_compare (list_compare value_compare) (attr_vals attrs u) (attr_vals attrs v).

  (* ---------------- the names are a strictly sorted record shape ---------------- *)
  Lemma all_ltb_In : forall a l b, all_ltb a l = true -> In b l -> string_ltb a b = true.
  Proof.
    induction l; cbn; intros b H H_in; [ contradiction | ].
    apply Bool.andb_true_iff in H as [ H1 H2 ].
    destruct H_in as [ -> | H_in ]; auto.
  Qed.

  Lemma string_ltb_neq : forall a b, string_ltb a b = true -> a <> b.
  Proof.
    unfold string_ltb; intros a b H ->.
    rewrite string_compare_refl in H; discriminate.
  Qed.

  Lemma string_ltb_leb : forall a b, string_ltb a b = true -> String.leb a b = true.
  Proof.
    unfold string_ltb, String.leb; intros a b H.
    destruct (String.compare a b); auto; discriminate.
  Qed.

  Lemma names_strict_NoDup : forall l, names_strict l = true -> NoDup l.
  Proof.
    induction l as [ | a l IH ]; cbn; intros H; [ constructor | ].
    apply Bool.andb_true_iff in H as [ H1 H2 ].
    constructor; auto.
    intro H_in. apply (all_ltb_In _ _ _ H1) in H_in.
    apply string_ltb_neq in H_in; auto.
  Qed.

  Lemma names_strict_SSorted : forall l,
      names_strict l = true -> StronglySorted (fun a b => String.leb a b = true) l.
  Proof.
    induction l as [ | a l IH ]; cbn; intros H; [ constructor | ].
    apply Bool.andb_true_iff in H as [ H1 H2 ].
    constructor; auto.
    rewrite Forall_forall; intros b H_in.
    apply string_ltb_leb, (all_ltb_In _ _ _ H1 H_in).
  Qed.

  Lemma StronglySorted_map_inv : forall A B (f : A -> B) (R : B -> B -> Prop) l,
      StronglySorted R (List.map f l) ->
      StronglySorted (fun x y => R (f x) (f y)) l.
  Proof.
    induction l as [ | a l IH ]; cbn; intros H; [ constructor | ].
    apply StronglySorted_inv in H as [ H_ss H_fa ].
    constructor; [ apply IH; assumption | ].
    rewrite Forall_forall in H_fa |- *; intros y H_in.
    apply H_fa, in_map; assumption.
  Qed.

  (* A canonical record list is its own sort.  record_entry_leb is not
     antisymmetric -- two entries with one name and different values are
     mutually <= -- so the sorted permutation is unique only when the names
     are DISTINCT, which is what the NoDup premise supplies.  The work is
     done by Forall2_Permuted_StronglySorted at R := eq. *)
  Lemma record_sort_id : forall (l : list (string * value)),
      NoDup (List.map fst l) ->
      StronglySorted (fun p p' => is_true (record_entry_leb p p')) l ->
      record_sort l = l.
  Proof.
    intros l H_nd H_ss.
    rewrite <- Forall2_eq.
    eapply Forall2_Permuted_StronglySorted with (l1 := l) (l2 := l).
    1: rewrite Forall2_eq; reflexivity.
    1: assumption.
    1: intros [ ? ? ] [ ? ? ] H'; inversion H'; reflexivity.
    1: apply Permuted_record_sort.
    1: apply Permutation_refl.
    1: apply StronglySorted_record_sort.
    1: assumption.
  Qed.

  Lemma map_fst_key_fields_val : forall attrs i rc,
      List.map fst (key_fields_val i attrs rc) = key_names_from i attrs.
  Proof.
    induction attrs as [ | a attrs IH ]; cbn; intros; auto.
    f_equal; auto.
  Qed.

  Lemma map_fst_key_fields_expr : forall attrs i r,
      List.map fst (key_fields_expr i r attrs) = key_names_from i attrs.
  Proof.
    induction attrs as [ | a attrs IH ]; cbn; intros; auto.
    f_equal; auto.
  Qed.

  Lemma access_record_app_last : forall (A : Type) (l : list (string * A)) s (v : A),
      ~ In s (List.map fst l) -> access_record (l ++ [(s, v)])%list s = Success v.
  Proof.
    induction l as [ | [ n x ] l IH ]; cbn; intros s v H.
    1: rewrite String.eqb_refl; reflexivity.
    destruct (String.eqb s n) eqn:E.
    1:{ apply String.eqb_eq in E; subst. exfalso; intuition auto. }
    apply IH; intuition auto.
  Qed.

  (* The one boolean check, delivered in the two forms a record needs --
     for any payload type, so that the VALUE side and the TYPE side of the
     desugaring are served by the same lemma. *)
  Lemma names_ok__record : forall (A : Type) attrs (L : list (string * A)),
      names_ok attrs = true ->
      List.map fst L = (key_names_from 0 attrs ++ [payload_name])%list ->
      NoDup (List.map fst L) /\
      StronglySorted (fun p p' => is_true (record_entry_leb p p')) L.
  Proof.
    unfold names_ok; intros A attrs L H_ok H_names; split.
    1:{ rewrite H_names. apply names_strict_NoDup; assumption. }
    apply names_strict_SSorted in H_ok.
    rewrite <- H_names in H_ok.
    apply StronglySorted_map_inv in H_ok.
    unfold record_entry_leb, is_true. exact H_ok.
  Qed.

  Lemma payload_not_a_key : forall attrs,
      names_ok attrs = true -> ~ In payload_name (key_names_from 0 attrs).
  Proof.
    unfold names_ok; intros attrs H.
    apply names_strict_NoDup in H.
    apply NoDup_remove_2 in H.
    rewrite app_nil_r in H. exact H.
  Qed.

  Lemma map_fst_key_fields_val_app : forall attrs rc,
      List.map fst (key_fields_val 0 attrs rc ++ [(payload_name, VRecord rc)])%list
      = (key_names_from 0 attrs ++ [payload_name])%list.
  Proof.
    intros. rewrite map_app, map_fst_key_fields_val; reflexivity.
  Qed.

  (* the two premises record_sort_id wants, from the one boolean check *)
  Lemma names_ok__NoDup : forall attrs rc,
      names_ok attrs = true ->
      NoDup (List.map fst (key_fields_val 0 attrs rc ++ [(payload_name, VRecord rc)])%list).
  Proof.
    intros attrs rc H.
    eapply (proj1 (names_ok__record _ attrs _ H (map_fst_key_fields_val_app _ _))).
  Qed.

  Lemma names_ok__SSorted : forall attrs rc,
      names_ok attrs = true ->
      StronglySorted (fun p p' => is_true (record_entry_leb p p'))
        (key_fields_val 0 attrs rc ++ [(payload_name, VRecord rc)])%list.
  Proof.
    intros attrs rc H.
    eapply (proj2 (names_ok__record _ attrs _ H (map_fst_key_fields_val_app _ _))).
  Qed.
End Desugaring.

Section WithMap.
  Notation value := (value).
  Context {locals : map.map string value} {locals_ok : map.ok locals}.

  Definition proj_payload (v : value) : value :=
    match v with
    | VRecord rc => record_proj payload_name rc
    | _ => VUnit
    end.

  Lemma flat_map_single : forall A B (f : A -> B) l,
      flat_map (fun v => [f v]) l = List.map f l.
  Proof. induction l; cbn; auto. Qed.

  Lemma map_interp_key_fields_expr : forall attrs i (store env : locals) r rc,
      map.get env r = Some (VRecord rc) ->
      List.map (fun '(s, e) => (s, interp_expr store env e)) (key_fields_expr i r attrs)
      = key_fields_val i attrs rc.
  Proof.
    induction attrs as [ | a attrs IH ]; cbn; intros; auto.
    f_equal; [ | apply IH; assumption ].
    cbn. unfold get_local. rewrite H. reflexivity.
  Qed.

  (* the projection onto the key record denotes gallina_key -- which is
     where names_ok earns its place: without it record_sort would permute
     the generated fields and the comparison below would be on some other
     order *)
  Lemma interp_key_expr : forall attrs (store env : locals) r rc,
      names_ok attrs = true ->
      map.get env r = Some (VRecord rc) ->
      interp_expr store env (key_expr r attrs) = gallina_key attrs (VRecord rc).
  Proof.
    unfold key_expr, gallina_key; intros attrs store env r rc H_ok H_get.
    cbn [interp_expr]. rewrite map_app. cbn [List.map].
    erewrite map_interp_key_fields_expr by eassumption.
    cbn [interp_expr]. unfold get_local. rewrite H_get.
    f_equal. apply record_sort_id.
    1: apply names_ok__NoDup; assumption.
    1: apply names_ok__SSorted; assumption.
  Qed.

  (* the row comes back out unchanged *)
  Lemma proj_gallina_key : forall attrs rc,
      names_ok attrs = true ->
      proj_payload (gallina_key attrs (VRecord rc)) = VRecord rc.
  Proof.
    unfold proj_payload, gallina_key, record_proj; intros attrs rc H.
    rewrite access_record_app_last; auto.
    rewrite map_fst_key_fields_val.
    apply payload_not_a_key; assumption.
  Qed.

  (* ---------------- what the desugaring computes ---------------- *)
  Lemma interp_sort_by : forall attrs r p (store env : locals) e rows,
      names_ok attrs = true ->
      interp_expr store env e = VList rows ->
      Forall (fun v => exists rc, v = VRecord rc) rows ->
      interp_expr store env (sort_by attrs r p e)
      = VList (List.map proj_payload (value_sort (List.map (gallina_key attrs) rows))).
  Proof.
    unfold sort_by; intros attrs r p store env e rows H_ok H_e H_rec.
    cbn [interp_expr]. rewrite H_e.
    (* the INNER flatmap; naming l keeps the rewrite off the outer one,
       which rewrite would otherwise reach first *)
    erewrite In_flat_map_ext with (l := rows) (g := fun v => [gallina_key attrs v]).
    2:{ intros v H_in. rewrite Forall_forall in H_rec.
        destruct (H_rec v H_in) as [ rc -> ].
        cbn [interp_expr].
        erewrite interp_key_expr; [ | eassumption | apply map.get_put_same ].
        reflexivity. }
    rewrite flat_map_single.
    cbn [interp_expr].
    erewrite In_flat_map_ext with (g := fun v => [proj_payload v]).
    2:{ intros v _. cbn [interp_expr]. unfold get_local, proj_payload.
        rewrite map.get_put_same. destruct v; reflexivity. }
    rewrite flat_map_single. reflexivity.
  Qed.

  (* ---------------- it is a permutation ---------------- *)
  Lemma map_proj_gallina_key : forall attrs l,
      names_ok attrs = true ->
      Forall (fun v => exists rc, v = VRecord rc) l ->
      List.map proj_payload (List.map (gallina_key attrs) l) = l.
  Proof.
    intros attrs l H_ok H; induction H as [ | v l H_v H_l IH ]; cbn; auto.
    destruct H_v as [ rc -> ]. f_equal; auto.
    apply proj_gallina_key; assumption.
  Qed.

  Theorem sort_by_permutes : forall attrs r p (store env : locals) e rows out,
      names_ok attrs = true ->
      interp_expr store env e = VList rows ->
      Forall (fun v => exists rc, v = VRecord rc) rows ->
      interp_expr store env (sort_by attrs r p e) = VList out ->
      Permutation rows out.
  Proof.
    intros attrs r p store env e rows out H_ok H_e H_rec H_out.
    erewrite interp_sort_by in H_out by eassumption.
    injection H_out as H_out; subst out.
    rewrite <- (map_proj_gallina_key attrs rows) at 1 by assumption.
    apply Permutation_map, Permuted_value_sort.
  Qed.

  (* ---------------- it is sorted by the attributes themselves ---------------- *)
  Lemma StronglySorted_map_In : forall A B (R : A -> A -> Prop) (S : B -> B -> Prop) (f : A -> B) l,
      StronglySorted R l ->
      (forall x y, In x l -> In y l -> R x y -> S (f x) (f y)) ->
      StronglySorted S (List.map f l).
  Proof.
    induction l as [ | a l IH ]; cbn; intros H_ss H_imp; [ constructor | ].
    apply StronglySorted_inv in H_ss as [ H_ss H_fa ].
    constructor.
    1:{ apply IH.
        1: assumption.
        intros x y Hx Hy; apply H_imp; cbn; auto. }
    rewrite Forall_forall in H_fa |- *. intros b H_in.
    apply in_map_iff in H_in as [ y [ <- H_in ] ].
    apply H_imp; cbn; auto.
  Qed.

  (* Two records with the SAME field names compare on their values alone:
     every name comparison returns Eq.  This is the step that turns
     record_compare -- which is a comparison of (name, value) pairs -- into
     the lexicographic order the user asked for. *)
  Lemma list_compare_pair_same_names : forall (l1 l2 : list (string * value)),
      List.map fst l1 = List.map fst l2 ->
      list_compare (pair_compare String.compare value_compare) l1 l2
      = list_compare value_compare (List.map snd l1) (List.map snd l2).
  Proof.
    induction l1 as [ | [ n1 x1 ] l1 IH ]; intros [ | [ n2 x2 ] l2 ] H; cbn in *;
      try discriminate; auto.
    injection H as H_n H_l; subst n2.
    rewrite string_compare_refl.
    destruct (value_compare x1 x2); auto.
  Qed.

  Lemma list_compare_app_single : forall (l1 l2 : list value) a b,
      List.length l1 = List.length l2 ->
      list_compare value_compare (l1 ++ [a])%list (l2 ++ [b])%list
      = match list_compare value_compare l1 l2 with
        | Eq => value_compare a b
        | c => c
        end.
  Proof.
    induction l1 as [ | x1 l1 IH ]; intros [ | x2 l2 ] a b H; cbn in *;
      try discriminate.
    1: destruct (value_compare a b); reflexivity.
    destruct (value_compare x1 x2); auto.
  Qed.

  Lemma map_snd_key_fields_val : forall attrs i rc,
      List.map snd (key_fields_val i attrs rc)
      = List.map (fun a => record_proj a rc) attrs.
  Proof.
    induction attrs as [ | a attrs IH ]; cbn; intros; auto.
    f_equal; auto.
  Qed.

  (* THE refinement: the canonical order on key records implies the
     lexicographic order on the listed attributes.  The payload field is
     last, so it only ever breaks a tie. *)
  Lemma key_leb__lex_leb : forall attrs rc1 rc2,
      value_leb (gallina_key attrs (VRecord rc1)) (gallina_key attrs (VRecord rc2)) = true ->
      lex_leb attrs (VRecord rc1) (VRecord rc2) = true.
  Proof.
    unfold value_leb, lex_leb, leb_from_compare, gallina_key, attr_vals.
    intros attrs rc1 rc2 H.
    cbn [value_compare] in H. unfold record_compare in H.
    rewrite list_compare_pair_same_names in H
      by (rewrite !map_app, !map_fst_key_fields_val; reflexivity).
    rewrite !map_app, !map_snd_key_fields_val in H. cbn [List.map] in H.
    rewrite list_compare_app_single in H
      by (rewrite !List.length_map; reflexivity).
    destruct (list_compare value_compare
                (List.map (fun a => record_proj a rc1) attrs)
                (List.map (fun a => record_proj a rc2) attrs));
      cbn in *; auto.
  Qed.

  Theorem sort_by_sorted : forall attrs r p (store env : locals) e rows out,
      names_ok attrs = true ->
      interp_expr store env e = VList rows ->
      Forall (fun v => exists rc, v = VRecord rc) rows ->
      interp_expr store env (sort_by attrs r p e) = VList out ->
      StronglySorted (fun u v => is_true (lex_leb attrs u v)) out.
  Proof.
    intros attrs r p store env e rows out H_ok H_e H_rec H_out.
    erewrite interp_sort_by in H_out by eassumption.
    injection H_out as H_out; subst out.
    apply StronglySorted_map_In with (R := fun u v => is_true (value_leb u v)).
    1: apply StronglySorted_value_sort.
    intros x y H_x H_y H_leb.
    (* both are key records of rows, so the refinement above applies *)
    apply Permutation_in with (l' := List.map (gallina_key attrs) rows) in H_x, H_y;
      try (apply Permutation_sym, Permuted_value_sort).
    apply in_map_iff in H_x as [ vx [ <- H_vx ] ].
    apply in_map_iff in H_y as [ vy [ <- H_vy ] ].
    rewrite Forall_forall in H_rec.
    destruct (H_rec _ H_vx) as [ rcx -> ]. destruct (H_rec _ H_vy) as [ rcy -> ].
    rewrite !proj_gallina_key by assumption.
    apply key_leb__lex_leb; exact H_leb.
  Qed.

End WithMap.

(* The typing side needs a type environment and no value environment, so it
   gets its own section. *)
Section WithTenv.
  Context {tenv : map.map string type} {tenv_ok : map.ok tenv}.

  (* ---------------- the desugaring preserves types ---------------- *)
  Fixpoint key_types_from (i : nat) (attrs : list string) (rt : list (string * type))
    : list (string * type) :=
    match attrs with
    | [] => []
    | a :: attrs => (key_name i a, get_attr_type rt a) :: key_types_from (S i) attrs rt
    end.

  Definition key_ty (attrs : list string) (rt : list (string * type)) : type :=
    TRecord (key_types_from 0 attrs rt ++ [(payload_name, TRecord rt)])%list.

  (* every listed attribute is a field of the row type.  A boolean, so a
     use site discharges it by computation along with names_ok. *)
  Definition attrs_present (rt : list (string * type)) (attrs : list string) : bool :=
    List.forallb (fun a => match access_record rt a with
                           | Success _ => true
                           | Failure _ => false
                           end) attrs.

  Lemma map_fst_key_types_from : forall attrs i rt,
      List.map fst (key_types_from i attrs rt) = key_names_from i attrs.
  Proof.
    induction attrs as [ | a attrs IH ]; cbn; intros; auto. f_equal; auto.
  Qed.

  Lemma map_fst_key_types_app : forall attrs rt,
      List.map fst (key_types_from 0 attrs rt ++ [(payload_name, TRecord rt)])%list
      = (key_names_from 0 attrs ++ [payload_name])%list.
  Proof.
    intros. rewrite map_app, map_fst_key_types_from; reflexivity.
  Qed.

  Lemma map_snd_key_types_from : forall attrs i rt,
      List.map snd (key_types_from i attrs rt) = List.map (get_attr_type rt) attrs.
  Proof.
    induction attrs as [ | a attrs IH ]; cbn; intros; auto. f_equal; auto.
  Qed.

  Lemma key_ty_wf : forall attrs rt,
      names_ok attrs = true ->
      type_wf (TRecord rt) ->
      type_wf (key_ty attrs rt).
  Proof.
    unfold key_ty; intros attrs rt H_ok H_wf.
    pose proof (names_ok__record _ attrs _ H_ok (map_fst_key_types_app attrs rt)) as [ H_nd H_ss ].
    constructor; auto.
    rewrite map_app, map_snd_key_types_from; cbn [List.map].
    apply Forall_app; split.
    1:{ rewrite Forall_map, Forall_forall; intros a _.
        apply get_attr_type_ty_wf; assumption. }
    1:{ cbn [List.map snd]. constructor; [ exact H_wf | constructor ]. }
  Qed.

  Lemma Forall2_key_fields_ty : forall attrs i Gstore Genv r rt,
      attrs_present rt attrs = true ->
      map.get Genv r = Some (TRecord rt) ->
      Forall2 (type_of Gstore Genv)
        (List.map snd (key_fields_expr i r attrs))
        (List.map snd (key_types_from i attrs rt)).
  Proof.
    induction attrs as [ | a attrs IH ]; cbn; intros i Gstore Genv r rt H_p H_get;
      [ constructor | ].
    apply Bool.andb_true_iff in H_p as [ H_a H_p ].
    destruct (access_record rt a) eqn:E_a; [ | discriminate ].
    constructor; [ | apply IH; assumption ].
    econstructor.
    1: constructor; eassumption.
    unfold get_attr_type; rewrite E_a; reflexivity.
  Qed.

  Lemma key_expr_ty : forall Gstore Genv attrs r rt,
      names_ok attrs = true ->
      attrs_present rt attrs = true ->
      map.get Genv r = Some (TRecord rt) ->
      type_of Gstore Genv (key_expr r attrs) (key_ty attrs rt).
  Proof.
    unfold key_expr, key_ty; intros Gstore Genv attrs r rt H_ok H_p H_get.
    pose proof (names_ok__record _ attrs _ H_ok (map_fst_key_types_app attrs rt)) as [ H_nd H_ss ].
    (* tl must be given: TyERecord's conclusion mentions only tl', so an
       eapply leaves tl existential and the first obligation becomes a
       higher-order unification rather than a computation *)
    eapply TyERecord with (tl := (key_types_from 0 attrs rt ++ [(payload_name, TRecord rt)])%list).
    1:{ rewrite !map_app, map_fst_key_fields_expr, map_fst_key_types_from;
        reflexivity. }
    1:{ rewrite !map_app; cbn [List.map snd].
        apply Forall2_app.
        1: apply Forall2_key_fields_ty; assumption.
        (* explicit: `repeat constructor` on a type_of goal searches every
           constructor of the judgment and does not terminate *)
        constructor; [ apply TyEVar; exact H_get | constructor ]. }
    1: apply Permutation_refl.
    1: exact H_nd.
    1: exact H_ss.
  Qed.

  (* `order by attrs` is a list-to-list rewrite at the SAME type: the rows
     that go in are the rows that come out, and the renamed key record is
     invisible from outside. *)
  Lemma sort_by_ty : forall Gstore Genv attrs r p e rt,
      names_ok attrs = true ->
      attrs_present rt attrs = true ->
      type_wf (TRecord rt) ->
      type_of Gstore Genv e (TList (TRecord rt)) ->
      type_of Gstore Genv (sort_by attrs r p e) (TList (TRecord rt)).
  Proof.
    unfold sort_by; intros Gstore Genv attrs r p e rt H_ok H_p H_wf H_e.
    eapply TyEFlatmap_List with (t1 := key_ty attrs rt).
    1:{ apply TyESort_List.
        eapply TyEFlatmap_List with (t1 := TRecord rt); [ exact H_e | ].
        econstructor.
        1: apply TyOCons.
        1: apply key_expr_ty; [ assumption | assumption | apply map.get_put_same ].
        1: apply TyEAtom; constructor; apply key_ty_wf; assumption. }
    econstructor.
    1: apply TyOCons.
    1:{ eapply TyEAccess.
        1: constructor; apply map.get_put_same.
        unfold key_ty. apply access_record_app_last.
        rewrite map_fst_key_types_from. apply payload_not_a_key; assumption. }
    1: apply TyEAtom; constructor; assumption.
  Qed.
End WithTenv.
