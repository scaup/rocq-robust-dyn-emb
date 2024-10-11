From main.prelude Require Import autosubst.
From main.dyn_lang Require Import definition lemmas tactics labels.
From main.logrel.lib Require Import weakestpre.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

Section rfn.

  Definition val_lift_r : (val -d> val -d> siProp) -d> val -d> expr -d> siProp :=
    λ Φ v e', (∃ v', ⌜ rtc step_ne e' (of_val v') ⌝ ∗ Φ v v')%I.

  Definition lbl_lift_r : (label -> label -> Prop) -> label -> expr -> Prop :=
    λ L ℓ e', ((∃ t' ℓ', rtc step_ne e' t' ∧ faulty t' ℓ' ∧ True)).
    (* λ L ℓ e', ((∃ t' ℓ', rtc step_ne e' t' ∧ faulty t' ℓ' ∧ L ℓ ℓ')). *)

  Definition rfn : (val -d> val -d> siProp) -d> (label -> label -> Prop) -d> expr -d> expr -d> siProp :=
    λ Φ L e e', wp (λ v, val_lift_r Φ v e')%I
                   (λ ℓ, ⌜ lbl_lift_r L ℓ e' ⌝)%I e.

  Lemma eval_stable_val_lift_r Φ v e e' (H : rtc step_ne e e') :
    val_lift_r Φ v e ≡ val_lift_r Φ v e'.
  Proof.
    rewrite /val_lift_r. do 3 f_equiv. iApply bi.pure_iff.
    split; intros H'.
    - eapply (rtc_ind_r (fun t => rtc step_ne t (of_val a)) e H'); eauto.
      intros x y Hex Hxy Hxa. clear Hex H' H.
      destruct (rtc_inv _ _ Hxa) as [-> | (y' & Hxy' & Hy'a)].
      + exfalso.
        assert (H := (step_no_val _ _ Hxy)). by rewrite to_of_val in H.
      + by rewrite (ne_step_det _ _ _ Hxy Hxy').
    - by eapply rtc_transitive.
  Qed.

  Lemma eval_stable_lbl_lift_r L ℓ e e' (H : rtc step_ne e e') :
    lbl_lift_r L ℓ e <-> lbl_lift_r L ℓ e'.
  Proof.
    rewrite /lbl_lift_r. do 4 f_equiv. rename a0 into ℓ'.
    split; intros (H' & Hf & Hl); split; eauto.
    - eapply (rtc_ind_r (fun t => rtc step_ne t a) e H'); eauto.
      intros x y Hex Hxy Hxa. clear Hex H' H.
      destruct (rtc_inv _ _ Hxa) as [-> | (y' & Hxy' & Hy'a)].
      + exfalso. by eapply faulty_not_stop.
      + by rewrite (ne_step_det _ _ _ Hxy Hxy').
    - by eapply rtc_transitive.
  Qed.

  Lemma rfn_bind_with_termination K e K' e' Ψ Φ L :
    ⊢ rfn Ψ L e e' -∗ (∀ v v', Ψ v v' -∗ ⌜ rtc step_ne e (of_val v) ⌝ -∗ ⌜ rtc step_ne e' (of_val v') ⌝ -∗ rfn Φ L (fill K (of_val v)) (fill K' (of_val v'))) -∗ rfn Φ L (fill K e) (fill K' e').
  Proof.
    iIntros "Hee' Hc". rewrite /rfn.
    iApply (wp_bind_with_termination with "[Hee' Hc]").
    iApply (wp_impl with "Hee'").
    { iIntros (ℓ). iApply bi.pure_mono. rewrite /lbl_lift_r.
      intros (t' & ℓ' & He't & Hf & Hl). exists (fill K' t'), ℓ'. repeat split; auto.
      - eapply rtc_congruence; eauto. intros. by eapply fill_step.
      - by eapply fill_faulty. }
    iIntros (v) "H %Hsteps".  iDestruct "H" as (v') "[%Hsteps' HΨ]".
    iSpecialize ("Hc" with "HΨ"). iSpecialize ("Hc" $! Hsteps Hsteps').
    iApply (wp_impl with "Hc").
    { iIntros (ℓ). iApply bi.pure_mono. apply eval_stable_lbl_lift_r.
      eapply rtc_congruence; eauto. intros. by eapply fill_step. }
    { iIntros (w) "Hw". iApply (eval_stable_val_lift_r with "Hw").
      eapply rtc_congruence; eauto. intros. by eapply fill_step. }
  Qed.

  Lemma rfn_impl e1 e2 Φ Φ' L L' (HLL' : le_permissive L' L) :
    ⊢ rfn Φ' L' e1 e2 -∗ (∀ v v', Φ' v v' -∗ Φ v v') -∗ rfn Φ L e1 e2.
  Proof.
    iIntros "He Hv".
    rewrite /rfn. iApply (wp_impl with "He").
    - iIntros (ℓ) "%H". iPureIntro. destruct H as (t' & ℓ' & Hs & Hf & HL). exists t', ℓ'. naive_solver.
    - iIntros (v) "H". iDestruct "H" as (v') "(Hs & HΦ)". iExists v'. iFrame. by iApply "Hv".
  Qed.

  Lemma rfn_bind' K e K' e' Ψ Φ L :
    ⊢ rfn Ψ L e e' -∗ (∀ v v', Ψ v v' -∗ rfn Φ L (fill K (of_val v)) (fill K' (of_val v'))) -∗ rfn Φ L (fill K e) (fill K' e').
  Proof.
    iIntros "Hee' Hc". iApply (rfn_bind_with_termination with "Hee'").
    iIntros (v v') "Hvv' Hs Hs'". by iApply "Hc".
  Qed.

  Lemma rfn_val v1 v2 e1 (H1 : e1 = of_val v1) e2 (H2 : e2 = of_val v2) Φ L : Φ v1 v2 ⊢ rfn Φ L e1 e2.
  Proof. rewrite /rfn. iIntros "HΦ". iApply wp_val. eauto. iExists v2. iFrame. iPureIntro. rewrite H2. by apply rtc_refl. Qed.

  Lemma rfn_val_l_inv v1 e2 Φ L : rfn Φ L (of_val v1) e2 ⊢ val_lift_r Φ v1 e2.
  Proof. rewrite /rfn. iIntros "H". by iDestruct (wp_val_inv with "H") as "H'". Qed.

  Lemma rfn_faulty e ℓ (H : faulty e ℓ) e' ℓ' (H' : faulty e' ℓ') Φ L (HL : L ℓ ℓ') : ⊢ rfn Φ L e e'.
  Proof. rewrite /rfn /lbl_lift_r. iApply wp_faulty; eauto. iPureIntro. eexists _, _; eauto. naive_solver. Qed.

  Instance rfn_proper : NonExpansive rfn.
  Proof. rewrite /rfn. intros n P P' dP L e e'. apply wp_proper. solve_proper. Qed.

  (* Definition stable_spec (  ) *)

  Lemma rfn_impl_r {e e1} e2 Φ L
     (HΦ : ⊢ ∀ v, val_lift_r Φ v e2 -∗ val_lift_r Φ v e1)
     (HL : ∀ ℓ, lbl_lift_r L ℓ e2 → lbl_lift_r L ℓ e1)
    : ⊢ rfn Φ L e e2 -∗ rfn Φ L e e1.
  Proof. iIntros "H". iApply (wp_impl with "H"); eauto. Qed.

  Lemma rfn_steps_l {e e1} e2 {Φ L}
     (H : rtc step_ne e1 e2)
    : ⊢ rfn Φ L e2 e -∗ rfn Φ L e1 e.
  Proof. by iApply wp_rtc. Qed.

  Lemma rfn_steps_r {e e1} e2 {Φ L}
     (H : rtc step_ne e1 e2)
    : ⊢ rfn Φ L e e2 -∗ rfn Φ L e e1.
  Proof.
    iApply rfn_impl_r.
    - iIntros (v) "H". by iApply eval_stable_val_lift_r.
    - intros ℓ. by eapply eval_stable_lbl_lift_r.
  Qed.

  Lemma rfn_steps_r_inv {e e1} e2 {Φ L}
     (H : rtc step_ne e2 e1)
    : ⊢ rfn Φ L e e2 -∗ rfn Φ L e e1.
  Proof.
    iApply rfn_impl_r.
    - iIntros (v) "H". by rewrite eval_stable_val_lift_r.
    - intros ℓ H'. by rewrite <- eval_stable_lbl_lift_r.
  Qed.

  Lemma rfn_s_l {e1 e2} (H : step_ne e1 e2) Φ L e' :
    ▷ rfn Φ L e2 e' ⊢ rfn Φ L e1 e'.
  Proof. by iApply wp_s. Qed.

  Lemma rfn_s_l_inv {e1 e2} (H : step_ne e1 e2) Φ L e' :
    rfn Φ L e1 e' ⊢ ▷ rfn Φ L e2 e'.
  Proof. by iApply wp_s_inv. Qed.

  Lemma rfn_s_r {e1 e2} (H : step_ne e1 e2) Φ L e :
    ⊢ rfn Φ L e e2 -∗ rfn Φ L e e1.
  Proof. iApply rfn_steps_r. by eapply rtc_once. Qed.

  Lemma rfn_s_r_inv {e1} e2 (H : step_ne e1 e2) Φ L e :
    ⊢ rfn Φ L e e1 -∗ rfn Φ L e e2.
  Proof. iApply rfn_steps_r_inv. by eapply rtc_once. Qed.

End rfn.
