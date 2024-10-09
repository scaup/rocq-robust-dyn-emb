From main Require Import imports prelude.autosubst prelude.tactics.
From main.grad_lang Require Import types definition typing lemmas.
From main.grad_lang.dynamics Require Import std.
From main.grad_lang.dynamics.simul Require Import invariant prog_pres.
From main.dyn_lang Require Import definition casts lib lemmas tactics.

Section universal.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma universal e τ (He : typed [] e τ) e' (HI : Invariant e e') :
    ∀ n en, nsteps cc_step n e en →
            typed [] en τ ∧ ∃ m em', n ≤ m ∧ nsteps dn_step m e' em' ∧ Invariant_EC en em'.
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

  Lemma ref_val e τ (He : typed [] e τ) v :
    rtc cc_step e (cc_of_val v) →
    ∃ v', rtc step ⌜e⌝ (of_val v') ∧ Invariant (cc_of_val v) (of_val v').
  Proof.
    intros H. destruct (iffLR (rtc_nsteps _ _) H) as (k & Hksteps).
    destruct (universal e τ He (simul_expr e) (simul_expr_Invariant _ e _ He) k (cc_of_val v) Hksteps) as (Hτv & m & ev & _ & Hdmsteps & HIvev).
    invclear HIvev.
    2:{ exfalso. assert (Hmm := cc_to_of_val v). rewrite -H1 in Hmm.
        by rewrite (grad_lang.dynamics.lemmas.fill_not_val K) in Hmm. }
    destruct (left_val_Invariant _ _ HI _ Hτv v (cc_to_of_val v)) as (v' & Hsteps & HIvv').
    exists v'. split; eauto. eapply rtc_transitive. by eapply rtc_nsteps_2.
    eapply (rtc_congruence id); [| apply Hsteps ]. by apply step_ne_step.
  Qed.

  Lemma ref_div e τ (He : typed [] e τ) :
    (∀ n, ∃ e', nsteps cc_step n e e') →
    (∀ n, ∃ e', nsteps step n ⌜e⌝ e').
  Proof.
    intros H n. destruct (H n) as (e' & Hnsteps).
    destruct (universal e τ He (simul_expr e) (simul_expr_Invariant _ e _ He) n _ Hnsteps) as (Hτv & m & ev & Hm & Hdmsteps & HIvev).
    assert (∃ k, n + k = m) as [k eq]. exists (m - n). lia.
    rewrite -eq in Hdmsteps.
    destruct (nsteps_add_inv _ _ _ _ Hdmsteps) as (ei & Hstepsi & Hstepsf).
    exists ei. auto.
  Qed.

  Lemma ref_error e τ (He : typed [] e τ) ℓ :
    (rtc cc_step e (cc_Error ℓ)) →
    (rtc step ⌜e⌝ (Error ℓ)).
  Proof.
    intros H. destruct (iffLR (rtc_nsteps _ _) H) as (k & Hksteps).
    destruct (universal e τ He (simul_expr e) (simul_expr_Invariant _ e _ He) k _ Hksteps) as (Hτv & m & t & _ & Hdmsteps & HIvev).
    invclear HIvev. 2:{ exfalso. destruct K as [|Ki K]; invclear H1. destruct Ki; invclear H2. }
    destruct t; invclear HI. apply rtc_nsteps. by eexists.
  Qed.

End simulation.
