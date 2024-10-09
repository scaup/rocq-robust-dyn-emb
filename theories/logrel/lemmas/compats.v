From main.prelude Require Import imports autosubst big_op_three.
From main.cast_calc Require Import types typing.
From main.dyn_lang Require Import definition lemmas tactics lib casts contexts.
From main.logrel Require Import definition.
From main.logrel.lib Require Import weakestpre rfn small_helpers.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

Lemma compat_var (Γ : list type) (L : LabelRel) (x : var) (τ : type) (H : Γ !! x = Some τ) :
  open_exprel_typed Γ L (Var x) (Var x) τ.
Proof.
  iIntros (Δ HΔ vs vs') "#Hvsvs'".
  asimpl.
  assert (H' : x < length Γ) by by apply lookup_lt_is_Some_1.
  iDestruct (big_sepL3_length with "Hvsvs'") as "[%eq %eq']".
  destruct (lookup_lt_is_Some_2 vs x ltac:(lia)) as [v eqv].
  destruct (lookup_lt_is_Some_2 vs' x ltac:(lia)) as [v' eqv'].
  iDestruct (big_sepL3_lookup _ _ _ _ x with "Hvsvs'") as "Hvv'"; eauto.
  assert (reqv : (of_val <$> vs) !! x = Some (of_val v)) by by rewrite list_lookup_fmap eqv; simplify_option_eq.
  assert (reqv' : (of_val <$> vs') !! x = Some (of_val v')) by by rewrite list_lookup_fmap eqv'; simplify_option_eq.
  rewrite (subst_list_lookup_some _ _ _ reqv) (subst_list_lookup_some _ _ _ reqv').
  rfn_val.
Qed.

Lemma compat_base (Γ : list type) (L : LabelRel) b :
  open_exprel_typed Γ L (Lit b) (Lit b) (Base $ base_lit_base b).
Proof. iIntros (Δ HΔ vs vs') "#Hvsvs'". asimpl. rfn_val. destruct b; auto. Qed.

Lemma compat_lam (Γ : list type) (L : LabelRel) τ1 τ2 e e'
  (He : open_exprel_typed (τ1 :: Γ) L e e' τ2) :
  open_exprel_typed Γ L (Lam e) (Lam e') (Bin Arrow τ1 τ2).
Proof.
  iIntros (Δ HΔ vs vs') "#Hvsvs'". asimpl.
  rfn_val. iIntros (w w') "#Hww'". fold valrel_typed. asimpl.
  change (of_val ?v .: subst_list (?es)) with (subst_list ((of_val v) :: es)). repeat rewrite -fmap_cons.
  iApply He; auto. simpl. auto.
Qed.

Lemma compat_pair (Γ : list type) (L1 L2 : LabelRel) e1 e1' e2 e2' τ1 τ2
  (H1 : open_exprel_typed Γ L1 e1 e1' τ1)
  (H2 : open_exprel_typed Γ L2 e2 e2' τ2) :
  open_exprel_typed Γ (L1 ⊔ L2) (Pair e1 e2) (Pair e1' e2') (Bin Product τ1 τ2).
(* Lemma compat_pair (Γ : list type) (L1 L2 L : LabelRel) (HL : le_permissive (disj L1 L2) L) e1 e1' e2 e2' τ1 τ2 *)
(*   (H1 : open_exprel_typed Γ L1 e1 e1' τ1) *)
(*   (H2 : open_exprel_typed Γ L2 e2 e2' τ2) : *)
(*   open_exprel_typed Γ L (Pair e1 e2) (Pair e1' e2') (Bin Product τ1 τ2). *)
Proof.
  iIntros (Δ HΔ vs vs') "#Hvsvs'".
  rfn_bind. iApply H1; auto.
  eapply le_permissive_trans'; eauto. eapply le_permissive_join_l.
  (* eapply le_permissive_trans'; eauto. eapply le_permissive_trans'; eauto. eapply le_permissive_join_l. *)
  iIntros (v1 v1') "#Hvv1'".
  rfn_bind. iApply H2; auto.
  eapply le_permissive_trans'; eauto. eapply le_permissive_join_r.
  iIntros (v2 v2') "#Hvv2'".
  rfn_val. rewrite /prod_rel. auto.
Qed.

Lemma compat_injl (Γ : list type) (L : LabelRel) e e' τ1 τ2
  (H : open_exprel_typed Γ L e e' τ1) :
  open_exprel_typed Γ L (InjL e) (InjL e') (Bin Sum τ1 τ2).
Proof.
  iIntros (Δ HΔ vs vs') "#Hvsvs'".
  rfn_bind. iApply H; auto.
  iIntros (v v') "#Hvv'".
  rfn_val.
Qed.

Lemma compat_injr (Γ : list type) (L : LabelRel) e e' τ1 τ2
  (H : open_exprel_typed Γ L e e' τ2) :
  open_exprel_typed Γ L (InjR e) (InjR e') (Bin Sum τ1 τ2).
Proof.
  iIntros (Δ HΔ vs vs') "#Hvsvs'".
  rfn_bind. iApply H; auto.
  iIntros (v v') "#Hvv'".
  rfn_val.
Qed.

Lemma compat_seq (Γ : list type) (L1 L2 : LabelRel) e1 e1' e2 e2' κ κ' τ
  (H1 : open_exprel_typed Γ L1 e1 e1' (Base Unit))
  (H2 : open_exprel_typed Γ L2 e2 e2' τ) :
  open_exprel_typed Γ (L1 ⊔ L2) (Seq κ e1 e2) (Seq κ' e1' e2') τ.
Proof.
  iIntros (Δ HΔ vs vs') "#Hvsvs'".
  rfn_bind.
  iApply H1; auto. eapply le_permissive_trans'; eauto. eapply le_permissive_join_l.
  iIntros (v v') "#Hvv'". dvals v v'.
  rfn_steps.
  iApply H2; auto. eapply le_permissive_trans'; eauto. eapply le_permissive_join_r.
Qed.

Lemma compat_if (Γ : list type) (L1 L2 L3 : LabelRel) e0 e0' e1 e1' e2 e2' κ κ' τ
  (H0 : open_exprel_typed Γ L1 e0 e0' (Base Bool))
  (H1 : open_exprel_typed Γ L2 e1 e1' τ)
  (H2 : open_exprel_typed Γ L3 e2 e2' τ) :
  open_exprel_typed Γ (L1 ⊔ L2 ⊔ L3) (If κ e0 e1 e2) (If κ' e0' e1' e2') τ.
Proof.
  iIntros (Δ HΔ vs vs') "#Hvsvs'".
  rfn_bind.
  iApply H0; auto. eapply le_permissive_trans'; eauto.
  { intros ℓ ℓ' H. rewrite /join /join_LabelRel_inst /join_LabelRel. naive_solver. }
  iIntros (v v') "#Hvv'". dvals v v'.
  rfn_steps.
  iRewrite "Hvv'". destruct b0.
  - iApply H1; auto. eapply le_permissive_trans'; eauto.
    { intros ℓ ℓ' H. rewrite /join /join_LabelRel_inst /join_LabelRel. naive_solver. }
  - iApply H2; auto. eapply le_permissive_trans'; eauto.
    { intros ℓ ℓ' H. rewrite /join /join_LabelRel_inst /join_LabelRel. naive_solver. }
Qed.

Lemma compat_binop (Γ : list type) (L1 L2 : LabelRel) e1 e1' e2 e2' κ κ' op
  (H1 : open_exprel_typed Γ L1 e1 e1' (Base Int))
  (H2 : open_exprel_typed Γ L2 e2 e2' (Base Int)) :
  open_exprel_typed Γ (L1 ⊔ L2) (BinOp κ op e1 e2) (BinOp κ' op e1' e2') (binop_res_type op).
Proof.
  iIntros (Δ HΔ vs vs') "#Hvsvs'".
  rfn_bind.
  iApply H1; auto. eapply le_permissive_trans'; eauto. eapply le_permissive_join_l.
  iIntros (v v') "#Hvv'".
  rfn_bind.
  iApply H2; auto. eapply le_permissive_trans'; eauto. eapply le_permissive_join_r.
  iIntros (w w') "#Hww'".
  dvals v v'. dvals w w'. iRewrite "Hvv'". iRewrite "Hww'".
  destruct op; rfn_steps; rfn_val.
Qed.

Lemma compat_app (Γ : list type) (L1 L2 : LabelRel) e1 e1' e2 e2' κ κ' τ1 τ2
  (H1 : open_exprel_typed Γ L1 e1 e1' (Bin Arrow τ1 τ2))
  (H2 : open_exprel_typed Γ L2 e2 e2' τ1) :
  open_exprel_typed Γ (L1 ⊔ L2) (App κ e1 e2) (App κ' e1' e2') τ2.
Proof.
  iIntros (Δ HΔ vs vs') "#Hvsvs'".
  rfn_bind.
  iApply H1; auto. eapply le_permissive_trans'; eauto. eapply le_permissive_join_l.
  iIntros (v v') "#Hvv'".
  rfn_bind.
  iApply H2; auto. eapply le_permissive_trans'; eauto. eapply le_permissive_join_r.
  iIntros (w w') "#Hww'". dvals v v'.
  rfn_steps. by iApply "Hvv'".
Qed.

Lemma compat_fst (Γ : list type) (L : LabelRel) e e' κ κ' τ1 τ2
  (H1 : open_exprel_typed Γ L e e' (Bin Product τ1 τ2)) :
  open_exprel_typed Γ L (Fst κ e) (Fst κ' e') τ1.
Proof.
  iIntros (Δ HΔ vs vs') "#Hvsvs'".
  rfn_bind.
  iApply H1; auto.
  iIntros (v v') "#Hvv'".
  dvals v v'.
  iDestruct "Hvv'" as "[H1 H2]".
  rfn_steps.
  rfn_val.
Qed.

Lemma compat_snd (Γ : list type) (L : LabelRel) e e' κ κ' τ1 τ2
  (H1 : open_exprel_typed Γ L e e' (Bin Product τ1 τ2)) :
  open_exprel_typed Γ L (Snd κ e) (Snd κ' e') τ2.
Proof.
  iIntros (Δ HΔ vs vs') "#Hvsvs'".
  rfn_bind.
  iApply H1; auto.
  iIntros (v v') "#Hvv'".
  dvals v v'.
  iDestruct "Hvv'" as "[H1 H2]".
  rfn_steps.
  rfn_val.
Qed.

Lemma compat_case (Γ : list type) (L1 L2 L3 : LabelRel) e0 e0' e1 e1' e2 e2' κ κ' τ1 τ2 τ
  (H0 : open_exprel_typed Γ L1 e0 e0' (Bin Sum τ1 τ2))
  (H1 : open_exprel_typed (τ1 :: Γ) L2 e1 e1' τ)
  (H2 : open_exprel_typed (τ2 :: Γ) L3 e2 e2' τ) :
  open_exprel_typed Γ (L1 ⊔ L2 ⊔ L3) (Case κ e0 e1 e2) (Case κ' e0' e1' e2') τ.
Proof.
  iIntros (Δ HΔ vs vs') "#Hvsvs'".
  rfn_bind.
  iApply H0; auto. eapply le_permissive_trans'; eauto.
  { intros ℓ ℓ' H. rewrite /join /join_LabelRel_inst /join_LabelRel. naive_solver. }
  iIntros (v v') "#Hvv'".
  dvals v v'; rfn_steps; change (of_val ?v .: subst_list (?es)) with (subst_list ((of_val v) :: es));
    repeat rewrite -fmap_cons.
  - iApply H1; auto. eapply le_permissive_trans'; eauto.
    { intros ℓ ℓ' H. rewrite /join /join_LabelRel_inst /join_LabelRel. naive_solver. }
    iNext. by simpl; auto.
  - iApply H2; auto. eapply le_permissive_trans'; eauto.
    { intros ℓ ℓ' H. rewrite /join /join_LabelRel_inst /join_LabelRel. naive_solver. }
    iNext. by simpl; auto.
Qed.

From main.logrel.lemmas Require Import compat_cast_help.

Section compat_cast.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma compat_cast (Γ : list type) (L : LabelRel) e e' ℓ ℓ' τ1 τ2 (H : consistency τ1 τ2)
    (H0 : open_exprel_typed Γ L e e' τ1) :
    open_exprel_typed Γ (L ⊔ (fun x x' => x = ℓ ∧ x' = ℓ'))
      (AppAn (of_val $ cast ℓ τ1 τ2 H) e) (AppAn (of_val $ cast ℓ' τ1 τ2 H) e') τ2.
  Proof.
    iIntros (Δ HΔ vs vs') "#Hvsvs'". repeat rewrite /= cast_closed.
    iApply compat_cast. apply HΔ.
    { rewrite /join /join_LabelRel_inst /join_LabelRel. naive_solver. }
    iApply H0; auto. eapply le_permissive_trans'; eauto.
    { intros y y' H'. rewrite /join /join_LabelRel_inst /join_LabelRel. naive_solver. }
  Qed.

End compat_cast.
