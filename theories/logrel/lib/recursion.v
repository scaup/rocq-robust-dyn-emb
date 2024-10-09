From main.prelude Require Import imports autosubst big_op_three.
From main.grad_lang Require Import types.
From main.dyn_lang Require Import definition lemmas lib labels tactics.
From main.logrel.lib Require Import weakestpre rfn small_helpers.
From main.logrel Require Import definition.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.
(* From iris.proofmode Require Import base proofmode classes. *)

Section recursion.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Coercion LitInt : Z >-> base_lit.
  Coercion LitBool : bool >-> base_lit.
  Coercion Lit : base_lit >-> expr.
  Coercion AppAn : expr >-> Funclass.
  Coercion Var : var >-> expr.

  Definition FixArrow (f : expr) : expr :=
    (Lam ((f.[ren (+1)]) (Lam ((Var 1) (Var 1) (Var 0)))))
      ((Lam (f.[ren (+1)] (Lam ((Var 1) (Var 1) (Var 0)))))).

  Lemma FixArrow_subst e σ : (FixArrow e).[σ] = FixArrow e.[σ].
  Proof. rewrite /FixArrow. by asimpl. Qed.

  Lemma FixArrow_eval f : step_ne (FixArrow f) (f (Lam ((FixArrow f).[ren (+1)] (Var 0)))).
  Proof.
    eassert (step_ne (FixArrow f) _). rewrite /FixArrow. step_solver.
    asimpl in H. rewrite /FixArrow. by asimpl.
  Qed.

  Definition RecV' (e : {bind 2 of expr}) : val :=
    LamV ((FixArrow (Lam (Lam e))).[ren (+1)] (Var 0)).
  (* we'll leave RecV for sealed one *)

  Definition Rec' e := of_val (RecV' e).

  Lemma Rec'_subst (e : {bind 2 of expr}) σ : (Rec' e).[σ] = Rec' (e.[ids 0 .: ids 1 .: σ >> ren (+2)]).
  Proof. by asimpl. Qed.

  Global Opaque FixArrow.

  Lemma App_Rec'_eval e1 v2 :
    nsteps step_ne 4 ((Rec' e1) (of_val v2)) e1.[(of_val v2), (Rec' e1)/].
  Proof.
    intros.
    eapply nsteps_l. rewrite /Rec'. step_solver. asimpl. rewrite FixArrow_subst.
    change 3 with (1 + 2).
    eapply nsteps_trans.
    assert (Hf := FixArrow_eval (Lam (Lam e1))).
    apply nsteps_once. rw_fill. eapply fill_step. apply Hf.
    eapply nsteps_l. step_solver. asimpl.
    eapply nsteps_l. step_solver. asimpl.
    rewrite FixArrow_subst. asimpl.
    constructor.
  Qed.

  (* this does not work sadly *)
  (* Global Opaque Rec. *)
  (* Global Opaque RecV. *)

  (* Definition Rec_aux : seal Rec. Proof. by eexists. Qed. *)
  (* Definition Rec' := Rec_aux.(unseal). *)
  (* Lemma Rec_unseal : Rec = Rec'. *)
  (* Proof. by rewrite -Rec_aux.(seal_eq) /=. Qed. *)

  Definition RecV_aux : seal RecV'. Proof. by eexists. Qed.
  Definition RecV := RecV_aux.(unseal).
  Lemma RecV_unseal : RecV = RecV'.
  Proof. by rewrite -RecV_aux.(seal_eq) /=. Qed.
  Lemma RecV_seal : RecV' = RecV.
  Proof. by rewrite -RecV_unseal. Qed.

  Notation Rec e := (of_val (RecV e)).

  Lemma wp_Rec L e e' v' (He' : to_val e' = Some v') Φ :
    ▷ wp Φ L e.[e', (Rec e)/] ⊢ wp Φ L (Rec e e').
  Proof.
    iIntros.
    rewrite -(of_to_val _ _ He'). iApply wp_nsteps.
    rewrite RecV_unseal.
    change (of_val (RecV' e)) with (Rec' e). apply App_Rec'_eval.
    change (Rec' e) with (of_val (RecV' e)). rewrite RecV_seal. auto.
  Qed.

  Lemma Rec_subst (e : {bind 2 of expr}) σ : (Rec e).[σ] = Rec (e.[ids 0 .: ids 1 .: σ >> ren (+2)]).
  Proof. rewrite RecV_unseal. by rewrite Rec'_subst. Qed.

  Lemma App_Rec_eval e1 v2 :
    nsteps step_ne 4 ((Rec e1) (of_val v2)) e1.[(of_val v2), (Rec e1)/].
  Proof. rewrite RecV_unseal. apply App_Rec'_eval. Qed.

  Lemma rfn_r_Rec_App L t e e' v' (He' : to_val e' = Some v') Φ :
    rfn Φ L t e.[e', (Rec e)/] ⊢ rfn Φ L t (Rec e e').
  Proof.
    rewrite -(of_to_val _ _ He').
    iIntros. iApply rfn_steps_r. eapply rtc_nsteps_2. eapply App_Rec_eval. auto.
  Qed.

  Lemma rfn_lr_Rec_App L t t' w' (Ht' : to_val t' = Some w') e e' v' (He' : to_val e' = Some v') Φ :
    ▷ rfn Φ L t.[t', (Rec t)/] e.[e', (Rec e)/] ⊢ rfn Φ L (Rec t t') (Rec e e').
  Proof.
    rewrite -(of_to_val _ _ Ht') -(of_to_val _ _ He').
    iIntros. iApply rfn_steps_r. eapply rtc_nsteps_2. eapply App_Rec_eval.
    iApply wp_impl. iApply wp_Rec. by rewrite to_of_val. auto.
    auto. auto.
  Qed.

End recursion.

Notation Rec e := (of_val (RecV e)).
