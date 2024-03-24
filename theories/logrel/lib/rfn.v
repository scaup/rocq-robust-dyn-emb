From main.prelude Require Import autosubst.
From main.dyn_lang Require Import definition lemmas tactics labels.
From main.logrel.lib Require Import weakestpre.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

Section rfn.

  Definition val_lift_r : (val -d> val -d> siProp) -d> val -d> expr -d> siProp :=
    λ Φ v e', (∃ v', ⌜ rtc step_not_error e' (of_val v') ⌝ ∗ Φ v v')%I.

  (* Definition lbl_lift_r : (label -> label -> Prop) -d> label -d> expr -d> siProp := *)
  (* Definition lbl_lift_r : (label -d> label -d> iProp) -> label -> expr -> Prop := *)
  Definition lbl_lift_r : (label -> label -> Prop) -> label -> expr -> Prop :=
    λ L ℓ e', ((∃ t' ℓ', rtc step_not_error e' t' ∧ faulty t' ℓ' ∧ L ℓ ℓ')).

  Definition rfn : (val -d> val -d> siProp) -d> (label -> label -> Prop) -d> expr -d> expr -d> siProp :=
    λ Φ L e e', wp (λ v, val_lift_r Φ v e')%I
                   (λ ℓ, ⌜ lbl_lift_r L ℓ e' ⌝)%I e.

  (* Definition rfn : (val -d> val -d> siProp) -d> (label -d> label -d> siProp) -d> expr -d> expr -d> siProp := *)
  (*   λ Φ L e e', wp (λ v, ∃ v', ⌜ rtc step_not_error e' (of_val v') ⌝ ∗ Φ v v')%I *)
  (*               (λ ℓ, ∃ t' ℓ', ⌜ rtc step_not_error e' t' ⌝ ∗ ⌜ faulty t' ℓ' ⌝ ∗ L ℓ ℓ')%I e. *)

  Lemma rfn_bind' K e K' e' Ψ Φ L :
    ⊢ rfn Ψ L e e' -∗ (∀ v v', Ψ v v' -∗ rfn Φ L (fill K (of_val v)) (fill K' (of_val v'))) -∗ rfn Φ L (fill K e) (fill K' e').
  Proof.
    iIntros "Hee' Hc". rewrite /rfn.
    iApply (wp_bind with "[Hee' Hc]").
    iApply (wp_impl with "Hee'").
    { iIntros (ℓ) "H". iDestruct "H" as (t' ℓ') "(Hsteps & Hf & HΨ)".
      iExists (fill K' t'), ℓ'. admit. }
    iIntros (v) "H".  iDestruct "H" as (v') "[%Hsteps HΨ]".
    iSpecialize ("Hc" with "HΨ").
    iApply (wp_impl with "Hc").
    { iIntros (ℓ) "H". iDestruct "H" as (t' ℓ') "(Hsteps & Hf & HΨ)".
      iExists (fill K' t'), ℓ'. admit. }
    { iIntros (w) "H". iDestruct "H" as (w') "(Hsteps & HΨ)".
      iExists w'. iFrame. admit. }
  Admitted.

  Lemma rfn_impl e1 e2 Φ Φ' L L' (HLL' : le_permissive L' L) :
    ⊢ rfn Φ' L' e1 e2 -∗ (∀ v v', Φ' v v' -∗ Φ v v') -∗ rfn Φ L e1 e2.
  Proof.
    iIntros "He Hv".
    rewrite /rfn. iApply (wp_impl with "He").
    - iIntros (ℓ) "%H". iPureIntro. destruct H as (t' & ℓ' & Hs & Hf & HL). exists t', ℓ'. naive_solver.
    - iIntros (v) "H". iDestruct "H" as (v') "(Hs & HΦ)". iExists v'. iFrame. by iApply "Hv".
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

  Lemma rfn_s_r {e1 e2} (H : step_not_error e1 e2) Φ L e :
    ⊢ rfn Φ L e e2 -∗ rfn Φ L e e1.
  Proof.
    iApply rfn_impl_r.
    - iIntros (v) "H". iDestruct "H" as (v') "[%Hs Hv]". iExists v'. iFrame.
      iPureIntro. by eapply rtc_l.
    - intros ℓ Hr. destruct Hr as (e' & ℓ' & Hs & Hf & HL).
      rewrite /lbl_lift_r. exists e', ℓ'. split; auto. by eapply rtc_l.
  Qed.

  Lemma rfn_s_l {e1 e2} (H : step_not_error e1 e2) Φ L e' :
    ▷ rfn Φ L e2 e' ⊢ rfn Φ L e1 e'.
  Proof. by iApply wp_s. Qed.

  Lemma rfn_s_l_inv {e1 e2} (H : step_not_error e1 e2) Φ L e' :
    rfn Φ L e1 e' ⊢ ▷ rfn Φ L e2 e'.
  Proof. by iApply wp_s_inv. Qed.

  Lemma rfn_s_r_inv {e1} e2 (H : step_not_error e1 e2) Φ L e :
    ⊢ rfn Φ L e e1 -∗ rfn Φ L e e2.
  Proof.
    iApply rfn_impl_r.
    - iIntros (v) "H". iDestruct "H" as (v') "[%Hs Hv]". iExists v'. iFrame.
      iPureIntro.
      { inversion Hs.
        - simplify_eq. exfalso.
          assert (H' := step_no_val _ _ H). by rewrite to_of_val in H'.
        - simplify_eq. by rewrite (ne_step_det _ _ _ H H0). }
    - intros ℓ Hℓ. rewrite /lbl_lift_r. destruct Hℓ as (e' & ℓ' & Hs & Hf & HL).
      rewrite /lbl_lift_r.
      { inversion Hs; simplify_eq.
        - exfalso. by eapply faulty_not_stop.
        - rewrite (ne_step_det _ _ _ H H0). exists e', ℓ'. split; auto. }
  Qed.

  (* Lemma rfn_lam_app_later_body Φ L e e' w w' ν ν' : *)
  (*   rfn Φ L (App ν (Lam e) (of_val w)) (App ν' (Lam e') (of_val w')) ⊣⊢ ▷ rfn Φ L e.[of_val w/] e'.[of_val w'/]. *)
  (* Proof. *)
  (*   assert (Hstep : step_not_error (App ν (Lam e) (of_val w)) e.[of_val w/]) by step_solver. *)
  (*   assert (Hstep' : step_not_error (App ν' (Lam e') (of_val w')) e'.[of_val w'/]) by step_solver. *)
  (*   iSplit. *)
  (*   - iIntros "H". iApply rfn_s_r_inv; eauto. iApply rfn_s_l_inv; eauto. *)
  (*   - iIntros "H". iApply rfn_s_r; eauto. iApply rfn_s_l; eauto. *)
  (* Qed. *)

End rfn.
