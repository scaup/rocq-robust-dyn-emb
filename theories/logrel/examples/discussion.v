From main.prelude Require Import imports autosubst big_op_three.
From main.grad_lang Require Import types.
From main.dyn_lang Require Import definition lemmas lib labels tactics.
From main.logrel.lib Require Import weakestpre rfn small_helpers.
From main.logrel Require Import definition examples.help.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.
(* From iris.proofmode Require Import base proofmode classes. *)

Section example_disc.

  Context {ν : label} {Hν : NeverOccurs ν}.

  (* Context (Omega : expr). *)
  (* Context (Omega_closed : Closed Omega). *)
  (* Context (Omega_step : step_ne Omega Omega). *)

  Definition Omega : expr :=
    App ν (Lam (App ν (Var 0) (Var 0))) (Lam (App ν (Var 0) (Var 0))).

  Lemma Omega_closed : Closed Omega.
  Proof. intro σ. by asimpl. Qed.

  Lemma Omega_step : step_ne Omega Omega.
  Proof. rewrite /Omega. step_solver. Qed.

  Lemma wp_Omega L Φ : ⊢ wp Φ L Omega.
  Proof. iLöb as "HLöb". iApply wp_s; eauto. apply Omega_step. Qed.

  Definition example : expr :=
    Lam(*g.*) (Seq ν
           (App ν (Var 0)(*g*) (Lam(*_.*) Omega))
           (App ν (Var 0)(*g*) (Lit LitUnit))
      ).

  Lemma rfn_bind_wt_K {K K' t t' e e' Ψ Φ L} :
    t = fill K e →
    t' = fill K' e' →
    ⊢ rfn Ψ L e e' -∗ (∀ v v', Ψ v v' -∗ ⌜ rtc step_ne e (of_val v) ⌝ -∗ ⌜ rtc step_ne e' (of_val v') ⌝ -∗ rfn Φ L (fill K (of_val v)) (fill K' (of_val v'))) -∗ rfn Φ L t t'.
  Proof. intros. simplify_eq. iApply rfn_bind_with_termination. Qed.

  Lemma example_sem_typed :
    sem_typed [] example (Bin Arrow (Bin Arrow (Bin Arrow (Base Unit) (Base Unit)) (Base Unit)) (Base Unit)).
  Proof.
    split; [| by intros σ; asimpl ].
    iIntros (Δ HΔ vs vs') "_". asimpl. rfn_val.
    iIntros (w w') "#Hee'". dvals w w'. simpl in *.
    rfn_steps.
    iApply rfn_bind_wt_K. 1-2: rw_fill; eauto.
    iApply "Hee'". { iIntros (u u') "Huu'". rewrite Omega_closed. iApply wp_Omega. } iClear "Hee'".
    iNext. iIntros (u u') "#Huu'". dvals u u'. iClear "Huu'". iIntros "%Hsteps %Hsteps'". simpl.
    rfn_steps. repeat iNext.
    destruct (rtc_nsteps_1 _ _ Hsteps) as [n Hn].
    destruct (rtc_nsteps_1 _ _ Hsteps') as [n' Hn'].
    iApply rfn_steps_l.
    apply (help Omega Omega_closed Omega_step _ _ Hn (LitV LitUnit)).
    iApply rfn_steps_r.
    apply (help Omega Omega_closed Omega_step _ _ Hn' (LitV LitUnit)).
    rfn_val.
  Qed.


End example_disc.

Section equiv_untyped.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Context (Omega : expr).
  Context (Omega_closed : Closed Omega).
  Context (Omega_step : step_ne Omega Omega).

  Context (wp_Omega : ∀ L Φ, ⊢ wp Φ L Omega).


  (* equiv in dyn langauge *)
  Context (ℓ ℓ' : label).

  Definition term1 : expr :=
    Lam(*g.*) (Seq ℓ
           (App ℓ' (Var 0)(*g*) (Lam(*_.*) Omega))
           (App ν (Var 0)(*g*) (Lit LitUnit))
      ).

  Definition term2 : expr :=
    Lam(*g.*) (Seq ℓ
           (App ℓ' (Var 0)(*g*) (Lam(*_.*) Omega))
           (Lit LitUnit)
      ).

  Lemma rel_term1_ref_ℓ_term2 :
    open_exprel_typed [] (diagonal ({[ ℓ; ℓ' ]} : listset label)) term1 term2 Unknown.
  Proof.
    iIntros (Δ HΔ vs vs') "_". asimpl. rfn_val.
    rewrite /valrel_typed valrel_unknown_unfold.
    iNext. iIntros (w w') "#Hee'". asimpl.
    assert (Hℓ : Δ ℓ ℓ). { apply HΔ. rewrite /diagonal. set_solver. }
    assert (Hℓ' : Δ ℓ' ℓ'). { apply HΔ. rewrite /diagonal. set_solver. }
    rewrite valrel_unknown_unfold. dvals w w'; try by rfn_faulty.
    rfn_steps. iNext. repeat rewrite Omega_closed.
    iApply (@rfn_bind_wt_K). 1-2:rw_fill; eauto. iApply "Hee'".
    { rewrite valrel_unknown_unfold /=. iNext.
      iIntros (w w') "Hww'". repeat rewrite Omega_closed. iApply wp_Omega. } iClear "Hee'".
    simpl.
    iIntros (u u') "#Huu' %Hsteps %Hsteps'".
    rewrite valrel_unknown_unfold. dvals u u'; try by rfn_faulty.
    rfn_steps.
    destruct (rtc_nsteps_1 _ _ Hsteps) as [n Hn].
    iApply rfn_steps_l.
    apply (help Omega Omega_closed Omega_step _ _ Hn (LitV LitUnit)).
    rfn_val. by rewrite valrel_unknown_unfold.
  Qed.

  Lemma rel_term2_ref_ℓ_term1 :
    open_exprel_typed [] (diagonal ({[ ℓ; ℓ' ]} : listset label)) term2 term1 Unknown.
  Proof.
    iIntros (Δ HΔ vs vs') "_". asimpl. rfn_val.
    rewrite /valrel_typed valrel_unknown_unfold.
    iNext. iIntros (w w') "#Hee'". asimpl.
    assert (Hℓ : Δ ℓ ℓ). { apply HΔ. rewrite /diagonal. set_solver. }
    assert (Hℓ' : Δ ℓ' ℓ'). { apply HΔ. rewrite /diagonal. set_solver. }
    rewrite valrel_unknown_unfold. dvals w w'; try by rfn_faulty.
    rfn_steps. iNext. repeat rewrite Omega_closed.
    iApply (@rfn_bind_wt_K). 1-2:rw_fill; eauto. iApply "Hee'".
    { rewrite valrel_unknown_unfold /=. iNext.
      iIntros (w w') "Hww'". repeat rewrite Omega_closed. iApply wp_Omega. } iClear "Hee'".
    simpl.
    iIntros (u u') "#Huu' %Hsteps %Hsteps'".
    rewrite valrel_unknown_unfold. dvals u u'; try by rfn_faulty.
    rfn_steps.
    destruct (rtc_nsteps_1 _ _ Hsteps') as [n Hn].
    iApply rfn_steps_r.
    apply (help Omega Omega_closed Omega_step _ _ Hn (LitV LitUnit)).
    rfn_val. by rewrite valrel_unknown_unfold.
  Qed.

End equiv_untyped.
