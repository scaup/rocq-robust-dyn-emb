From main.prelude Require Import imports autosubst.
From main.maps Require Import
  dyn_embedding.definition linker.definition grad_into_dyn.definition.
From main.grad_lang Require Import definition types typing contexts labels.
From main.dyn_lang Require Import definition contexts labels casts.
From main.logrel Require Import definition adequacy.
From main.logrel.lemmas Require Import fun_grad_into_dyn fun_dyn_embedding.

Notation dexpr := dyn_lang.definition.expr.
Notation gexpr := grad_lang.definition.expr.
Notation gctx := grad_lang.contexts.ctx.
Notation gfill_ctx := grad_lang.contexts.fill_ctx.

Section dyn_emb.

  Context {ν : label} {Hν : NeverOccurs ν}.
  (* Definition irrelevant := Lbl 11. *)
  (* Instance irrelevant : NeverOccurs (Lbl 11) := {}. *)

  Definition Innocent Γ τ (e : gexpr) : Prop :=
     ∀ (C : gctx) τ' (HC : typed_ctx C Γ τ [] τ'),
     (∀ ℓ, rtc step ⌊ gfill_ctx C e ⌋ (Error ℓ) → ℓ ∈ (labels_ctx C)).

  Definition WellBehaved Γ (e : dexpr) τ : Prop :=
     open_exprel_typed Γ ∅ e e τ ∧ Closed_n (length Γ) e.

  Definition import ℓ Γ τ (e : dexpr) : gexpr :=
     gfill_ctx (linker ℓ Γ τ) ⌜⌜ e ⌝⌝.

  Theorem importing_well_behaved_innocent Γ (e : dexpr) τ :
    WellBehaved Γ e τ → ∀ ℓ, Innocent Γ τ (import ℓ Γ τ e).
  Proof.
    intros [Hee HCe] ℓ C τ' HC ℓ' H.
    repeat rewrite trns_fill_ctx in H.
    (* *)
    assert (HC' := fundamental_ctx C _ _ _ _ HC).
    assert (Hee' := fundamental_l _ _ HCe).
    (* *)
    assert (HR12 : RefineL (InGradCtx C ⊔ (unary_conj (eq ℓ)) ⊔ InDynExpr e)
              (fill_ctx (trns_ctx C)
                  (fill_ctx (trns_ctx (linker ℓ Γ τ)) ⌊ ⌜⌜ e ⌝⌝ ⌋))
              (fill_ctx (trns_ctx C)
                  (fill_ctx (trns_ctx (linker ℓ Γ τ)) e))).
    { eapply logrel_adequacy. apply HC'.
      { eapply le_permissive_trans'. apply compats.disj_le1. apply compats.disj_le1. }
      apply linker_compat; auto.
      { eapply le_permissive_trans'. apply compats.disj_le1. apply compats.disj_le2. rewrite /unary_conj. auto. }
      by apply dyn_emb_trns_pres_closed_n.
      eapply open_exprel_typed_weaken. apply Hee'. apply compats.disj_le2.
    }
    assert (HR23 : RefineL (InGradCtx C)
              (fill_ctx (trns_ctx C)
                  (fill_ctx (trns_ctx (linker ℓ Γ τ)) e))
              (fill_ctx (trns_ctx C) e)).
    { eapply logrel_adequacy. apply HC'. apply le_permissive_same.
      apply linker_superfluous_l. auto.
      eapply open_exprel_typed_weaken. apply Hee. intros l l' H'. by exfalso. }
    assert (HR13 := (refineL_trans _ _ _ _ _ HR12 HR23)). clear HR12 HR23.
    (* *)
    destruct HR13 as [H1 H2]. specialize (H2 _ H).
    destruct H2 as [l' (P & H')].
    rewrite /comb_trans_lblrel /disj in P.
    destruct P as (l2 & PP). rewrite /InGradCtx /diag /InDynExpr /InGradCtx in PP.
    destruct PP. repeat destruct H0; try set_solver.
  Qed.

End dyn_emb.
