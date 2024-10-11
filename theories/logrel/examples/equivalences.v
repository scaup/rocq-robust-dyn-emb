From main.prelude Require Import imports autosubst big_op_three.
From main.cast_calc Require Import types.
From main.dyn_lang Require Import definition lemmas lib labels tactics.
From main.logrel.lib Require Import weakestpre rfn small_helpers recursion.
From main.logrel Require Import definition.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.
(* From iris.proofmode Require Import base proofmode classes. *)

Section examples.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Context (ℓ : label).


  Definition example1 : expr :=
    Lam (
        If ν (BinOp ℓ LeOp 0 (Var 0))
          (Var 0)
          0
      ).

  Definition pos : expr :=
    Rec (If ν (BinOp ν EqOp (Var 0) 0)
            (0)
            (BinOp ν PlusOp 1 ((Var 1) (BinOp ν MinusOp (Var 0) 1)))
            ).

  Lemma pos_Closed : Closed pos.
  Proof. intros σ. rewrite Rec_subst. by asimpl. Qed.

  Lemma rtc_step_ne_bind K e e1 e' :
      rtc step_ne e e1 → rtc step_ne (fill K e1) e' → rtc step_ne (fill K e) e'.
  Proof.
    intros. eapply rtc_transitive; eauto. eapply rtc_congruence; eauto. intros. by apply fill_step.
  Qed.

  Lemma pos_app_N (z : nat) :
    rtc step_ne (pos z)
      (match (decide (0 ≤ z)%Z) with
         | left p => z
         | right p => 0
       end).
  Proof.
    induction z.
    - eapply rtc_transitive. apply rtc_nsteps. exists 4. rw_of_val. apply App_Rec_eval.
      asimpl. eapply rtc_l. step_solver. simpl.
      eapply rtc_l. step_solver. simpl. apply rtc_refl.
    - eapply rtc_transitive. apply rtc_nsteps. exists 4. rw_of_val. apply App_Rec_eval.
      asimpl. eapply rtc_l. step_solver. simpl.
      asimpl. eapply rtc_l. step_solver. simpl.
      asimpl. eapply rtc_l. step_solver. simpl.
      assert ((S z - 1%nat)%Z = z) as ->. lia.
      rw_fill_popped. eapply rtc_step_ne_bind. simpl. apply IHz. simpl.
      destruct (decide (0 ≤ z)%Z).
      + eapply rtc_l. step_solver. simpl.
        assert ((1%nat + z)%Z = S z) as ->. lia.
        apply rtc_refl.
      + eapply rtc_l. step_solver. simpl.
        assert ((1%nat + 0%nat)%Z = S z) as ->. lia.
        apply rtc_refl.
  Qed.

  Definition example1' : expr :=
    Lam (
        If ν (BinOp ℓ LeOp 0 (Var 0))
          (pos (Var 0))
          0
      ).

  Ltac rwu := (try rewrite /(valrel_typed Unknown)); rewrite valrel_unknown_unfold.

  Lemma example1_ref :
    open_exprel_typed [] (diagonal (eq ℓ)) example1 example1' Unknown.
  Proof.
    iIntros (Δ HΔ vs vs') "_". asimpl. rfn_val.
    rewrite /valrel_typed /= valrel_unknown_unfold /=. iNext.
    iIntros (w w') "Hww'". dvals w w'; (try by rewrite valrel_unknown_unfold); try rfn_faulty.
    rfn_steps. rewrite valrel_unknown_unfold /=. iRewrite "Hww'".
    destruct (decide (0%nat ≤ n)%Z) as [Hy | Hn]; [ repeat rewrite bool_decide_true; auto | rewrite bool_decide_false; auto ].
    - assert (exists (z : nat), (Z.of_nat z = n)) as [z eq]. exists (Z.to_nat n). lia. rewrite -eq.
      rewrite pos_Closed. iApply rfn_steps_r.
      eapply pos_app_N. rewrite decide_True. rfn_val. rwu. auto. lia.
    - rfn_val. rwu. auto.
  Qed.

  Lemma example1_ref_rev :
    open_exprel_typed [] (diagonal (eq ℓ)) example1' example1 Unknown.
  Proof.
    iIntros (Δ HΔ vs vs') "_". asimpl. rfn_val.
    rewrite /valrel_typed /= valrel_unknown_unfold /=. iNext.
    iIntros (w w') "Hww'". dvals w w'; (try by rewrite valrel_unknown_unfold); try rfn_faulty.
    rfn_steps. rewrite valrel_unknown_unfold /=. iRewrite "Hww'".
    destruct (decide (0%nat ≤ n)%Z) as [Hy | Hn]; [ repeat rewrite bool_decide_true; auto | rewrite bool_decide_false; auto ].
    - assert (exists (z : nat), (Z.of_nat z = n)) as [z eq]. exists (Z.to_nat n). lia. rewrite -eq.
      rewrite pos_Closed. iApply rfn_steps_l.
      eapply pos_app_N. rewrite decide_True. rfn_val. rwu. auto. lia.
    - rfn_val. rwu. auto.
  Qed.

  Definition example2 : expr :=
    Lam (Case ℓ (Var 0) (Var 1) (InjL (Lit LitUnit))).

  Definition example2' : expr :=
    Lam (Case ℓ (Var 0) (InjL (Var 0)) (InjL (Lit LitUnit))).

  Lemma example2_ref :
    open_exprel_typed [] (diagonal (eq ℓ)) example2 example2' Unknown.
  Proof.
    iIntros (Δ HΔ vs vs') "_". asimpl. rfn_val. rwu. simpl.
    iNext. iIntros (s s') "#Hss'". dvals s s'; (try by rwu); try rfn_faulty.
    - rfn_steps. iNext. rfn_val.
    - rfn_steps. iNext. rfn_val. iClear "Hss'". rwu. simpl. iNext. by rwu.
  Qed.

  Lemma example2_ref_rev :
    open_exprel_typed [] (diagonal (eq ℓ)) example2' example2 Unknown.
  Proof.
    iIntros (Δ HΔ vs vs') "_". asimpl. rfn_val. rwu. simpl.
    iNext. iIntros (s s') "#Hss'". dvals s s'; (try by rwu); try rfn_faulty.
    - rfn_steps. iNext. rfn_val.
    - rfn_steps. iNext. rfn_val. iClear "Hss'". rwu. simpl. iNext. by rwu.
  Qed.

  Definition example3 : expr :=
    Lam 0.

  Definition example3' : expr :=
    Lam (BinOp ν MinusOp (Var 0) (Var 0)).

  Lemma example3_ref :
    open_exprel_typed [] (diagonal (eq ℓ)) example3 example3' (Bin Arrow (Base Int) (Base Int)).
  Proof.
    iIntros (Δ HΔ vs vs') "_". asimpl. rfn_val. simpl.
    iIntros (z z') "#Hzz'". dvals z z'. iRewrite "Hzz'". rfn_steps.
    rfn_val. assert ((n - n)%Z = 0) as ->. lia. auto.
  Qed.

  Lemma example3_ref_rev :
    open_exprel_typed [] (diagonal (eq ℓ)) example3' example3 (Bin Arrow (Base Int) (Base Int)).
  Proof.
    iIntros (Δ HΔ vs vs') "_". asimpl. rfn_val. simpl.
    iIntros (z z') "#Hzz'". dvals z z'. iRewrite "Hzz'". rfn_steps.
    rfn_val. assert ((n - n)%Z = 0) as ->. lia. auto.
  Qed.

End examples.
