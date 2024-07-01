From main.prelude Require Import imports autosubst big_op_three.
From main.grad_lang Require Import types definition typing labels contexts.
From main.dyn_lang Require Import definition lemmas tactics lib casts contexts.
From main.logrel.lib Require Import weakestpre rfn small_helpers.

(* From main.logrel.lemmas Require Import casts_compat. *)

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

From main.logrel Require Import definition lemmas.compats.
From main.maps Require Import grad_into_dyn.definition.

Section fundamental.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Ltac permissive_solver :=
    by rewrite /InGradExpr /diagonal /join /join_LabelRel_inst /join_LabelRel; intros x x'; set_solver.

  Lemma fundamental Γ e τ (H : typed Γ e τ) :
    open_exprel_typed Γ (InGradExpr e) (⟨ e ⟩) (⟨ e ⟩) τ.
  Proof.
    induction H; simpl; rewrite /InGradExpr /=.
    - by apply compat_var.
    - by apply compat_base.
    - eapply open_exprel_typed_weaken.
      eauto using compat_seq.
      permissive_solver.
    - eapply open_exprel_typed_weaken.
      eauto using compat_if.
      permissive_solver.
    - eapply open_exprel_typed_weaken.
      eauto using compat_binop.
      permissive_solver.
    - apply compat_lam; eauto.
    - eapply open_exprel_typed_weaken.
      eapply compat_app; eauto.
      permissive_solver.
    - eapply open_exprel_typed_weaken.
      apply compat_pair; eauto.
      permissive_solver.
    - eauto using compat_fst.
    - eauto using compat_snd.
    - eauto using compat_injl.
    - eauto using compat_injr.
    - eapply open_exprel_typed_weaken.
      eauto using compat_case.
      permissive_solver.
    - rewrite /cast'. destruct (consistency_decision τ1 τ2); [ | by exfalso].
      eapply open_exprel_typed_weaken.
      eauto using compat_cast.
      permissive_solver.
  Qed.

  Ltac permissive_solver'  :=
    try by (lazymatch goal with
            | H : _ ⊑ _ |- _ ⊑ _ =>
                rewrite /InGradCtx_item /InGradExpr /diagonal /labels_ctx_item /join /join_LabelRel_inst /join_LabelRel in H |- *;
                intros x x'; specialize (H x x'); set_solver end).


  Lemma fundamental_ctx_item Ci Γ τ Γ' τ' (HCi : typed_ctx_item Ci Γ τ Γ' τ') :
    ctx_rel_typed (InGradCtx_item Ci) [trns_ctx_item Ci] [trns_ctx_item Ci] Γ τ Γ' τ'.
  Proof.
    intros L HCiL e e' Hee'.
    simpl. destruct HCi; simpl.
    - by apply compat_lam.
    - eapply open_exprel_typed_weaken.
      eauto using compat_app, fundamental.
      permissive_solver'.
    - eapply open_exprel_typed_weaken.
      eauto using compat_app, fundamental. permissive_solver'.
    - eapply open_exprel_typed_weaken.
      eauto using compat_pair, fundamental. permissive_solver'.
    - eapply open_exprel_typed_weaken.
      eauto using compat_pair, fundamental. permissive_solver'.
    - by eapply compat_fst.
    - by eapply compat_snd.
    - by eapply compat_injl.
    - by eapply compat_injr.
    - eapply open_exprel_typed_weaken.
      eauto using compat_case, fundamental. permissive_solver'.
    - eapply open_exprel_typed_weaken.
      eauto using compat_case, fundamental. permissive_solver'.
    - eapply open_exprel_typed_weaken.
      eauto using compat_case, fundamental. permissive_solver'.
    - eapply open_exprel_typed_weaken.
      eauto using compat_binop, fundamental. permissive_solver'.
    - eapply open_exprel_typed_weaken.
      eauto using compat_binop, fundamental. permissive_solver'.
    - eapply open_exprel_typed_weaken.
      eauto using compat_if, fundamental. permissive_solver'.
    - eapply open_exprel_typed_weaken.
      eauto using compat_if, fundamental. permissive_solver'.
    - eapply open_exprel_typed_weaken.
      eauto using compat_if, fundamental. permissive_solver'.
    - eapply open_exprel_typed_weaken.
      eauto using compat_seq, fundamental. permissive_solver'.
    - eapply open_exprel_typed_weaken.
      eauto using compat_seq, fundamental. permissive_solver'.
    - rewrite /cast'. destruct (consistency_decision τ1 τ2); [ | by exfalso].
      eapply open_exprel_typed_weaken.
      eauto using compat_cast. permissive_solver'.
  Qed.

  Lemma fundamental_ctx C Γ τ Γ' τ' (HC : typed_ctx C Γ τ Γ' τ') :
    ctx_rel_typed (InGradCtx C) (trns_ctx C) (trns_ctx C) Γ τ Γ' τ'.
  Proof.
    intros L HCiL e e' Hee'. induction HC; simpl. auto.
    eapply fundamental_ctx_item; eauto. rewrite /InGradCtx in HCiL.
    apply (le_permissive_trans' _ _ _ HCiL). apply le_permissive_diagonal. intros k Hk; set_solver.
    apply IHHC.
    apply (le_permissive_trans' _ _ _ HCiL). apply le_permissive_diagonal. intros k Hk; set_solver.
    auto.
  Qed.

End fundamental.
