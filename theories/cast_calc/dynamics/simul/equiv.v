From main Require Import imports prelude.autosubst prelude.tactics.
From main.cast_calc Require Import types definition typing lemmas.
From main.cast_calc.dynamics Require Import std.
From main.cast_calc.dynamics.simul Require Import invariant prog_pres.
From main.dyn_lang Require Import definition casts lib lemmas tactics.

Section universal.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma universal e τ (He : typed [] e τ) e' (HI : Invariant e e') :
    ∀ n en, nsteps cc.step n e en →
            typed [] en τ ∧ ∃ m em', n ≤ m ∧ nsteps dn.step m e' em' ∧ Invariant_EC en em'.
  Proof.
    intros n. induction n; intros.
    - invclear H. split; auto. exists 0, e'. repeat split; eauto; repeat constructor; auto.
    - rename en into eSn. destruct (nsteps_inv_r _ _ _ H) as (en & Hn & Hs).
      specialize (IHn en Hn) as (Hτen & m & em & Hnm & Hms & HIm).
      split. by eapply preservation.
      destruct (left_step_Invariant_EC _ _ Hτen _ HIm _ Hs) as (efm & Hemefm & HIf).
      destruct (iffLR (tc_nsteps _ _) Hemefm) as (k & Hk & Hksteps).
      exists (m + k), efm. split; [ lia |]. split; auto.
      by eapply nsteps_trans.
  Qed.

End universal.

Section simulation.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma ref_terminating e τ (He : typed [] e τ) v :
    rtc cc.step e (cc.of_val v) →
    ∃ v', rtc step ⟨e⟩ (of_val v') ∧ Invariant (cc.of_val v) (of_val v').
  Proof.
    intros H. destruct (iffLR (rtc_nsteps _ _) H) as (k & Hksteps).
    destruct (universal e τ He (trns e) (simul_expr_Invariant _ e _ He) k (cc.of_val v) Hksteps) as (Hτv & m & ev & _ & Hdmsteps & HIvev).
    invclear HIvev.
    2:{ exfalso. assert (Hmm := cc.to_of_val v). rewrite -H1 in Hmm.
        by rewrite (cast_calc.dynamics.lemmas.fill_not_val K) in Hmm. }
    destruct (left_val_Invariant _ _ HI _ Hτv v (cc.to_of_val v)) as (v' & Hsteps & HIvv').
    exists v'. split; eauto. eapply rtc_transitive. by eapply rtc_nsteps_2.
    eapply (rtc_congruence id); [| apply Hsteps ]. by apply step_ne_step.
  Qed.

  Lemma ref_diverging e τ (He : typed [] e τ) :
    (∀ n, ∃ e', nsteps cc.step n e e') →
    (∀ n, ∃ e', nsteps step n ⟨e⟩ e').
  Proof.
    intros H n. destruct (H n) as (e' & Hnsteps).
    destruct (universal e τ He (trns e) (simul_expr_Invariant _ e _ He) n _ Hnsteps) as (Hτv & m & ev & Hm & Hdmsteps & HIvev).
    assert (∃ k, n + k = m) as [k eq]. exists (m - n). lia.
    rewrite -eq in Hdmsteps.
    destruct (nsteps_add_inv _ _ _ _ Hdmsteps) as (ei & Hstepsi & Hstepsf).
    exists ei. auto.
  Qed.

  Lemma ref_erroring e τ (He : typed [] e τ) ℓ :
    (rtc cc.step e (cc.Error ℓ)) →
    (rtc step ⟨e⟩ (Error ℓ)).
  Proof.
    intros H. destruct (iffLR (rtc_nsteps _ _) H) as (k & Hksteps).
    destruct (universal e τ He (trns e) (simul_expr_Invariant _ e _ He) k _ Hksteps) as (Hτv & m & t & _ & Hdmsteps & HIvev).
    invclear HIvev. 2:{ exfalso. destruct K as [|Ki K]; invclear H1. destruct Ki; invclear H2. }
    destruct t; invclear HI. apply rtc_nsteps. by eexists.
  Qed.

End simulation.

Section simulation_rev.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma rev_div_help e τ (He : typed [] e τ) :
    diverging ⟨e⟩ →
    ∀ α, ∃ k e2 e2', α ≤ k ∧ nsteps cc.step α e e2 ∧ nsteps step k ⟨e⟩ e2'. (* take k to be... *)
  Proof.
    intros HeDIV α.
    destruct (eval_possibilities _ _ He α) as [(eα & Heeα & Heατ) | [(n & K & ℓ & Hnα & Hstps) | (n & v & Hnα & Hstps)] ].
    - (* HeDiv on α *)
      assert (Heeα' : nsteps cc.step α e eα).
      { eapply (nsteps_congruence id); try eapply Heeα. apply step_np_step. }
      destruct (universal _ _ He _ (simul_expr_Invariant _ _ _ He) α eα Heeα') as (Hτ & k & ek' & Hαk & He'e'k & HI').
      exists k, eα, ek'. split; auto.
    - (* ref_error + HeDIV → False *)
      exfalso.
      assert (Hstps' : rtc cc.step e (cc.Error ℓ)).
      { eapply (rtc_transitive _ (cc.fill K (cc.Error ℓ))).
        assert (Hstps' := rtc_nsteps_2 _ _ _ Hstps).
        eapply (rtc_congruence id); try eapply Hstps'. apply step_np_step.
        destruct K; [ apply rtc_refl | by apply rtc_once; constructor ]. }
      assert (Herr := ref_erroring _ _ He _ Hstps').
      (* Herr + HeDiv *)
      by eapply eval_error_divergence_False.
    - (* ref_terminating + HeDIV → False *)
      exfalso.
      assert (Hstps' : rtc cc.step e (cc.of_val v)).
      { assert (Hstps' := rtc_nsteps_2 _ _ _ Hstps).
        eapply (rtc_congruence id); try eapply Hstps'. apply step_np_step. }
      destruct (ref_terminating _ _ He _ Hstps') as (w & Hval & _).
      (* Hval + HeDiv *)
      by eapply eval_val_divergence_False.
  Qed.

  Lemma rev_diverging e τ (He : typed [] e τ) :
    diverging ⟨e⟩ → cc.diverging e.
  Proof.
    intros. assert (HH := rev_div_help _ _ He H).
    intros α. specialize (HH α).
    destruct HH as (k & e2 & e2' & Hαk & Hee2 & He'e2').
    exists e2. apply Hee2.
  Qed.

  Lemma Invariant_of_val_r v' : ∀ e, Invariant e (of_val v') → ∃ v, e = cc.of_val v.
  Proof.
    induction v'; intros ? H; try by invclear H.
    - invclear H. eexists; by cc.rw_of_val.
      eexists (CastGroundUpV ℓ G _). eauto.
    - invclear H.
      + eexists; by cc.rw_of_val.
      + eexists (CastArrowV ℓ _ _ _ _ _). eauto.
      + eexists (CastGroundUpV ℓ G _). eauto.
      + eexists (CastArrowDownV ℓ _). eauto.
    - invclear H.
      + destruct (IHv' _ H2) as [w ->]. eexists; by cc.rw_of_val.
      + eexists (CastGroundUpV ℓ G _). eauto.
    - invclear H.
      + destruct (IHv' _ H2) as [w ->]. eexists; by cc.rw_of_val.
      + eexists (CastGroundUpV ℓ G _). eauto.
    - invclear H.
      + destruct (IHv'1 _ H3) as [w ->]. destruct (IHv'2 _ H4) as [w' ->].
        eexists; by cc.rw_of_val.
      + eexists (CastGroundUpV ℓ G _). eauto.
  Qed.

  Lemma Invariant_EC_of_val_r v' : ∀ e, Invariant_EC e (of_val v') → ∃ v, e = cc.of_val v.
  Proof.
    intros. invclear H. by eapply Invariant_of_val_r.
    exfalso. assert (is_Some (to_val (Error ℓ))). apply (fill_val K').
    exists v'. by rewrite -to_of_val H2. destruct H. destruct x; simplify_eq.
  Qed.

  Lemma rev_terminating e τ (He : typed [] e τ) :
    ∀ v', terminating ⟨e⟩ v' → ∃ v, cc.terminating e v ∧ Invariant (cc.of_val v) (of_val v').
  Proof.
    intros. rewrite /terminating in H.
    destruct (rtc_nsteps_1 _ _ H) as [α He'v'].
    (* it will have to happen before α *)
    destruct (eval_possibilities _ _ He α) as [(eα & Heeα & Heατ) | [(n & K & ℓ & Hnα & Hstps) | (n & v & Hnα & Hstps)] ].
    - (* HeDiv on α *)
      assert (Heeα' : nsteps cc.step α e eα).
      { eapply (nsteps_congruence id); try eapply Heeα. apply step_np_step. }
      destruct (universal _ _ He _ (simul_expr_Invariant _ _ _ He) α eα Heeα') as (Hτ & k & ek' & Hαk & He'e'k & HI').
      destruct (decide (α = k)) as [-> | neq].
      + assert (ek' = (of_val v')) as ->. by eapply dn.nsteps_det.
        destruct (Invariant_EC_of_val_r _ _ HI') as [v ->].
        exists v. split; auto. by eapply rtc_nsteps_2.
        invclear HI'. auto.
        (* in sep lemma... *)
        { exfalso. assert (is_Some (to_val (Error ℓ))). apply (fill_val K').
        exists v'. by rewrite -to_of_val H2. destruct H0. destruct x; simplify_eq. }
      + (* (α < k) + He'v' + He'e'k → False *)
        exfalso.
        assert (∃ β, k = α + (1 + β)). exists (k - α - 1). lia. destruct H0 as [β eq].
        rewrite eq in He'e'k.
        destruct (nsteps_add_inv _ _ _ _ He'e'k) as (ei' & Hs1 & Hs2).
        destruct (nsteps_add_inv _ _ _ _ Hs2) as (ei'' & Hs2' & Hs2'').
        assert (ei' = (of_val v')) as ->. by eapply dn.nsteps_det.
        (* Hs'' *)
        invclear Hs2'. invclear H2.
        assert (abs := step_no_val' _ _ H1). by rewrite to_of_val in abs.
    - (* Hstps' + ref_error + He'v' → False *)
      exfalso.
      assert (Hstps' : rtc cc.step e (cc.Error ℓ)).
      { eapply (rtc_transitive _ (cc.fill K (cc.Error ℓ))).
        assert (Hstps' := rtc_nsteps_2 _ _ _ Hstps).
        eapply (rtc_congruence id); try eapply Hstps'. apply step_np_step.
        destruct K; [ apply rtc_refl | by apply rtc_once; constructor ]. }
      assert (HH := ref_erroring _ _ He _ Hstps').
      eapply eval_val_error_False; eauto.
    - (* easy *)
      assert (Hstps' : rtc cc.step e (cc.of_val v)).
      { assert (Hstps' := rtc_nsteps_2 _ _ _ Hstps).
        eapply (rtc_congruence id); try eapply Hstps'. apply step_np_step. }
      destruct (ref_terminating _ _ He _ Hstps') as (w' & Hstps'' & HI).
      exists v. split; auto.
      by rewrite (eval_vals _ _ _ Hstps'' H) in HI.
  Qed.

  Lemma Invariant_EC_error_r ℓ : ∀ e, Invariant_EC e (Error ℓ) → e = cc.Error ℓ.
  Proof.
    intros. invclear H. invclear HI.  destruct v'; invclear He'. auto.
    destruct K'; auto. by exfalso.  destruct e; invclear H2.
  Qed.

  Lemma rev_erroring e τ (He : typed [] e τ) :
    ∀ ℓ, erroring ⟨e⟩ ℓ → cc.erroring e ℓ.
  Proof.
    intros. rewrite /erroring in H.
    destruct (rtc_nsteps_1 _ _ H) as [α He'v'].
    (* it will have to happen before α *)
    destruct (eval_possibilities _ _ He α) as [(eα & Heeα & Heατ) | [(n & K & ℓ' & Hnα & Hstps) | (n & v & Hnα & Hstps)] ].
    - (* HeDiv on α *)
      assert (Heeα' : nsteps cc.step α e eα).
      { eapply (nsteps_congruence id); try eapply Heeα. apply step_np_step. }
      destruct (universal _ _ He _ (simul_expr_Invariant _ _ _ He) α eα Heeα') as (Hτ & k & ek' & Hαk & He'e'k & HI').
      destruct (decide (α = k)) as [-> | neq].
      + assert (ek' = (Error ℓ)) as ->.
        eapply nsteps_det; eauto.
        rewrite (Invariant_EC_error_r _ _ HI') in Heeα'.
        rewrite /cc.erroring. by eapply rtc_nsteps_2.
      + (* (α < k) + He'v' + He'e'k → False *)
        exfalso.
        assert (∃ β, k = α + (1 + β)). exists (k - α - 1). lia. destruct H0 as [β eq].
        rewrite eq in He'e'k.
        destruct (nsteps_add_inv _ _ _ _ He'e'k) as (ei' & Hs1 & Hs2).
        destruct (nsteps_add_inv _ _ _ _ Hs2) as (ei'' & Hs2' & Hs2'').
        assert (ei' = (Error ℓ)) as ->.
        eapply nsteps_det; eauto.
        invclear Hs2'. invclear H2.
        by eapply Error_step_absurd.
    - (* easy *)
      assert (Hstps' : rtc cc.step e (cc.Error ℓ')).
      { eapply rtc_transitive. eapply rtc_nsteps_2.
        eapply (nsteps_congruence id); try eapply Hstps. apply step_np_step.
        destruct K; [ apply rtc_refl | by apply rtc_once; constructor ]. }
      assert (HH := ref_erroring _ _ He _ Hstps').
      assert (ℓ = ℓ') as ->. eapply eval_errors; eauto.
      auto.
    - (*  *)
      exfalso.
      assert (Hstps' : rtc cc.step e (cc.of_val v)).
      { eapply rtc_nsteps_2. eapply (nsteps_congruence id); try eapply Hstps. apply step_np_step. }
      destruct (ref_terminating _ _ He _ Hstps') as (w' & Hstps'' & HI).
      by eapply eval_val_error_False.
  Qed.


End simulation_rev.

Section equiv.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma equi_terminating e τ (He : typed [] e τ) :
    (∀ v, cc.terminating e v -> ∃ v', terminating ⟨e⟩ v' ∧ Invariant (cc.of_val v) (of_val v')) ∧
    (∀ v', terminating ⟨e⟩ v' -> ∃ v, cc.terminating e v ∧ Invariant (cc.of_val v) (of_val v')).
  Proof. split; [ by eapply ref_terminating | by eapply rev_terminating ]. Qed.

  Lemma equi_divergencing e τ (He : typed [] e τ) :
    (cc.diverging e <-> diverging ⟨e⟩).
  Proof. split; intros H n; [ by eapply ref_diverging | by eapply rev_diverging ]. Qed.

  Lemma equi_errororing e τ (He : typed [] e τ) :
    (∀ ℓ, cc.erroring e ℓ -> erroring ⟨e⟩ ℓ) ∧ (∀ ℓ, erroring ⟨e⟩ ℓ -> cc.erroring e ℓ).
  Proof. split; [ by eapply ref_erroring | by eapply rev_erroring ]. Qed.

End equiv.
