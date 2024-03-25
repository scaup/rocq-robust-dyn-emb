From main.prelude Require Import imports autosubst.
From main.dyn_lang Require Import definition lemmas tactics.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

Section wp.

  Inductive class (e : expr) : Type :=
    | Is_Value v (H : e = of_val v)
    | Is_Faulty ℓ (H : faulty e ℓ)
    | Take_NE_Step e' (H : step_not_error e e').

  Definition wp_pre (wp : (val -d> siProp) -d> (label -d> siProp) -d> (expr -d> siProp)) :
    (val -d> siProp) -d> (label -d> siProp) -d> (expr -d> siProp) := λ Φ L e,
    (∃ (C : class e), match C with
                     | Is_Value _ v H => Φ v
                     | Is_Faulty _ ℓ H => L ℓ
                     | Take_NE_Step _ e' H => ▷ wp Φ L e'
                     end)%I.

  Instance wp_pre_contractive : Contractive wp_pre.
  Proof. intros n wp wp' Hwp Φ L e. rewrite /wp_pre. do 3 f_equiv. f_contractive. apply Hwp. Qed.

  Definition wp : (val -d> siProp) -d> (label -d> siProp) -d> (expr -d> siProp) :=
    fixpoint wp_pre.

  Lemma wp_unfold Φ L e : wp Φ L e ≡ wp_pre wp Φ L e.
  Proof. by rewrite /wp (fixpoint_unfold wp_pre Φ L e). Qed.

  Lemma wp_val Φ L e v (H : e = of_val v) : Φ v ⊢ wp Φ L e.
  Proof. iIntros "HΦ". rewrite wp_unfold /wp_pre. by iExists (Is_Value _ _ H). Qed.

  Lemma wp_val_inv Φ L v : wp Φ L (of_val v) ⊢ Φ v.
  Proof.
    iIntros "H". rewrite wp_unfold. iDestruct "H" as (C) "H".
    destruct C.
    - by rewrite (inj of_val _ _ H).
    - exfalso. eapply faulty_not_val; eauto.
    - assert (H' := step_no_val _ _ H). by rewrite to_of_val in H'.
  Qed.

  Lemma wp_faulty Φ L e ℓ (H : faulty e ℓ) : L ℓ ⊢ wp Φ L e.
  Proof. iIntros "HΦ". rewrite wp_unfold /wp_pre. by iExists (Is_Faulty _ _ H). Qed.

  Lemma wp_bind K e Φ L :
    ⊢ wp (fun v => wp Φ L (fill K (of_val v))) L e -∗ wp Φ L (fill K e).
  Proof.
    iIntros "Hwp". iLöb as "HLöb" forall (e).
    (* checkout reason for wp e ... *)
    rewrite (wp_unfold _ _ e) /wp_pre /=.
    iDestruct "Hwp" as (C) "HCe".
    destruct C as [v -> | ℓ H | e' Hstep ].
    - (* value case is trivial *) auto.
    - (* faulty case as well very easy *)
      iApply wp_faulty; [apply (fill_faulty _ _ H K) | auto ].
    - (* step case where we use lob induction *)
      rewrite (wp_unfold _ _ (fill K e)) /wp_pre /=.
      assert (Hstep' : step_not_error (fill K e) (fill K e')).
      { inversion_clear Hstep. repeat rewrite -fill_app. by eapply SNE_Normal. }
      iExists (Take_NE_Step _ _ Hstep').
      iNext. by iApply "HLöb".
  Qed.

  Lemma wp_s {e2} {e1} (H : step_not_error e1 e2) Φ L :
    ▷ wp Φ L e2 ⊢ wp Φ L e1.
  Proof.
    iIntros "H".
    rewrite (wp_unfold _ _ e1) /wp_pre.
    by iExists (Take_NE_Step _ _ H).
  Qed.

  Lemma wp_s_inv {e2} {e1} (H : step_not_error e1 e2) Φ L :
    wp Φ L e1 ⊢ ▷ wp Φ L e2.
  Proof.
    iIntros "H".
    do 1 rewrite wp_unfold.
    iDestruct "H" as (C) "HC". destruct C.
    * (* absurd *) exfalso.
      assert (H' := step_no_val _ _ H). by rewrite H0 to_of_val in H'.
    * (* absurd *) exfalso. by eapply faulty_not_stop.
    * by rewrite (ne_step_det _ _ _ H H0).
  Qed.

  Lemma wp_bind_inv K e Φ L (* Hnv : to_val e = None *) :
    ⊢ wp Φ L (fill K e) -∗ wp (fun v => wp Φ L (fill K (of_val v))) L e.
  Proof.
    iIntros "Hwp". iLöb as "HLöb" forall (e).
    (* checkout reason for wp e ... *)
    rewrite (wp_unfold _ _ (fill K e)) /wp_pre /=.
    iDestruct "Hwp" as (C) "HCe".
    destruct (to_val e) as [v|] eqn:eq.
    - assert (eq' := of_to_val _ _ eq). simplify_eq. clear eq.
      iApply (wp_val _ _ _ v); auto.
      destruct C.
      + rewrite H. by iApply wp_val.
      + iApply wp_faulty; eauto.
      + iApply wp_s; eauto.
    - destruct C as [v eq' | ℓ H | e' Hstep ].
      + (* value case is trivial *)
        destruct (fill_val K e) as [w eq'']; first by eexists; rewrite eq' to_of_val.
        naive_solver.
      + (* faulty case as well very easy *)
        iApply (wp_faulty _ _ _ ℓ); auto. by eapply fill_faulty_inv.
      + (* step case where we use lob induction *)
        rewrite (wp_unfold _ _ e) /wp_pre /=.
        destruct (fill_pure_step_inv K _ _ eq Hstep) as (t & eq' & Hstp).
        iExists (Take_NE_Step _ _ Hstp).
        iNext. iApply "HLöb". by rewrite eq'.
  Qed.

  Lemma wp_impl e Φ Φ' L L' :
    ⊢ wp Φ' L' e -∗ (∀ ℓ, L' ℓ -∗ L ℓ) -∗ (∀ v, Φ' v -∗ Φ v) -∗ wp Φ L e.
  Proof.
    iLöb as "HLöb" forall (e).
    iIntros "He Hl Hv".
    repeat rewrite (wp_unfold _ _ e) /wp_pre /=.
    iDestruct "He" as (C) "HCe". iExists C.
    destruct C as [v -> | ℓ H | e' Hstep ]; [ by iApply "Hv" | by iApply "Hl" | ].
    iNext. iApply ("HLöb" with "HCe Hl Hv").
  Qed.

  Lemma wp_impl_faulty e Φ L L' :
    ⊢ wp Φ L' e -∗ (∀ ℓ, L' ℓ -∗ L ℓ) -∗ wp Φ L e.
  Proof. iIntros "He Hv". iApply (wp_impl with "He Hv"). intros; auto. Qed.

  Lemma wp_impl_val e Φ Φ' L :
    ⊢ wp Φ' L e -∗ (∀ v, Φ' v -∗ Φ v) -∗ wp Φ L e.
  Proof. iIntros "He Hv". by iApply (wp_impl with "He"); [ intros; auto | ]. Qed.

 Lemma wp_bind' K e Ψ Φ L :
    ⊢ wp Ψ L e -∗ (∀ v, Ψ v -∗ wp Φ L (fill K (of_val v))) -∗ wp Φ L (fill K e).
  Proof. iIntros "Hwp Hc". iApply wp_bind. by iApply (wp_impl_val with "Hwp"). Qed.

  Instance wp_proper : NonExpansive wp.
  Proof.
    intros n. induction n.
    - intros P P' dP L e.
      rewrite /dist.
      repeat rewrite wp_unfold /wp_pre.
      f_equiv. intros C.
      destruct C; auto. apply later_contractive, dist_later_0.
    - intros P P' dP L e.
      rewrite /dist.
      repeat rewrite wp_unfold /wp_pre.
      f_equiv. intros C.
      destruct C; auto. apply later_contractive.
      apply dist_later_S. apply IHn. eapply dist_le; try by exact dP. lia.
  Qed.

End wp.

From iris.si_logic Require Export siprop.

Section wp_adequacy.

  (* inspecting only current step *)

  Inductive adequate_now (ϕ : val → Prop) (l : label → Prop) (e : expr) : Prop :=
    | Ad_Value v (H : e = of_val v) (Hϕ : ϕ v)
    | Ad_Faulty ℓ (H : faulty e ℓ) (Hl : l ℓ)
    | Ad_Step_NE e' (H : step_not_error e e').

  Lemma wp_adequacy_now ϕ l e
    (H : ⊢ (wp (fun v => ⌜ ϕ v ⌝) (fun ℓ => ⌜ l ℓ ⌝) e)%I) : adequate_now ϕ l e.
  Proof.
    apply siProp.pure_soundness.
    iDestruct H as "H". clear H.
    rewrite wp_unfold /wp_pre.
    iDestruct "H" as (C) "H".
    destruct C as [v -> | ℓ H | e' Hstep].
    - iDestruct "H" as "%H". iPureIntro. by eapply Ad_Value.
    - iDestruct "H" as "%H'". iPureIntro. by eapply Ad_Faulty.
    - iPureIntro. by eapply Ad_Step_NE.
  Qed.

  (* general adequacy *)

  Lemma wp_later_soundness (Φ : val → siProp) L e e' (H : step_not_error e e') (H' : ⊢ wp Φ L e) : ⊢ wp Φ L e'.
  Proof.
    apply siProp.later_soundness.
    (* apply (@pure_soundness (iResUR Σ)). *)
    rewrite wp_unfold /wp_pre in H'.
    iDestruct H' as "H'". clear H'. iDestruct "H'" as (C) "H'".
    destruct C.
    - (* absurd case *) exfalso.
      assert (H' := step_no_val _ _ H). by rewrite H0 to_of_val in H'.
    - (* absurd case *) exfalso.
      by eapply faulty_not_stop.
    - (* follows from purity *)
      by rewrite (ne_step_det _ _ _ H H0).
  Qed.

  Lemma wp_adequacy_nlater ϕ l :
    ∀ n e (H : ⊢ (wp (fun v => ⌜ ϕ v ⌝) (fun ℓ => ⌜ l ℓ ⌝))%I e) e' (H : nsteps step_not_error n e e'),
      adequate_now ϕ l e'.
  Proof.
    induction n.
    - intros. inversion H0. simplify_eq. by eapply wp_adequacy_now.
    - intros. inversion H0. simplify_eq. rename y into e1.
      apply (IHn e1). { by eapply wp_later_soundness. } auto.
  Qed.

  Record adequate (ϕ : val → Prop) (l : label → Prop) e := {
    adequate_val : ∀ v, rtc step_not_error e (of_val v) → ϕ v ;
    adequate_faulty : ∀ e' ℓ, faulty e' ℓ → rtc step_not_error e e' → l ℓ ;
    }.

  Lemma adequate_alt e1 (φ : val → Prop) (l : label → Prop) :
    adequate φ l e1 ↔ ∀ t2,
      rtc step_not_error e1 t2 →
        (∀ v2, t2 = of_val v2 → φ v2) ∧
        (∀ ℓ, faulty t2 ℓ → l ℓ).
  Proof.
    split.
    - intros []; naive_solver.
    - constructor; naive_solver.
  Qed.

  Lemma adequate_alt' e1 (φ : val → Prop) (l : label → Prop) :
    adequate φ l e1 ↔ ∀ n t2,
      nsteps step_not_error n e1 t2 →
        (∀ v2, t2 = of_val v2 → φ v2) ∧
        (∀ ℓ, faulty t2 ℓ → l ℓ).
  Proof.
    eapply (Logic.iff_trans (adequate_alt _ _ _)).
    split; intros.
    - apply H. eapply rtc_nsteps. by exists n.
    - destruct ((iffLR (rtc_nsteps _ _) H0)) as [n Hnsteps]. apply (H n _ Hnsteps).
  Qed.

  Lemma wp_adequacy ϕ l e (H : ⊢ (wp (fun v => ⌜ ϕ v ⌝) (fun ℓ => ⌜ l ℓ ⌝))%I e) :
    adequate ϕ l e.
  Proof.
    apply adequate_alt'. intros. cut (adequate_now ϕ l t2); [| by eapply wp_adequacy_nlater].
    intro A.  destruct A.
    - split.
      + intros v' eq. by simplify_eq.
      + intros ℓ Hf. simplify_eq.
        exfalso. eapply faulty_not_val; eauto.
    - split.
      + intros v eq. exfalso. simplify_eq.
        exfalso. eapply faulty_not_val; eauto.
      + intros ℓ' Hf. simplify_eq. rewrite -(faulty_unique_label _ _ _ H1 Hf); auto.
    - split.
      + intros v eq. exfalso. simplify_eq.
        assert (H' := step_no_val _ _ H1). by rewrite to_of_val in H'.
      + intros ℓ Hf. exfalso. simplify_eq.
        eapply faulty_not_stop; eauto.
  Qed.

End wp_adequacy.
