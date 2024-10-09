From main.prelude Require Import imports autosubst.
From main.maps Require Import
  dyn_embedding.definition dyn_embedding.typing linker.definition grad_into_dyn.definition.
From main.cast_calc Require Import definition types typing contexts labels.
From main.cast_calc.dynamics Require Import std simul.equiv.
From main.dyn_lang Require Import definition contexts labels casts.
From main.logrel Require Import definition adequacy.
From main.logrel.lemmas Require Import fun_grad_into_dyn fun_dyn_embedding.

Notation dexpr := dyn_lang.definition.expr.
Notation gexpr := cast_calc.definition.expr.

Notation gctx := cast_calc.contexts.ctx.

Notation dfill_ctx := dyn_lang.contexts.fill_ctx.
Notation gfill_ctx := cast_calc.contexts.fill_ctx.

Ltac rw_labelrel :=
    (repeat
        ((try rewrite /InCastCalcCtx);
        (try rewrite /InDynExpr);
        (try rewrite /diagonal);
        (try rewrite /combine_LabelRel);
        (try rewrite /elemhood);
        (try rewrite /join /join_LabelRel_inst /join_LabelRel);
        (try rewrite /join /join_LabelPred_inst))
    ).

Ltac le_perm_solver := rw_labelrel; intros ?; set_solver.
Ltac labelrel_solver := rw_labelrel; set_solver.

Section refined_dyn_emb_criterion.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Notation cc_Error := cast_calc.definition.Error.

  Definition robust_up_to (L : label → Prop) Γ (e : gexpr) τ : Prop :=
    Γ ⊢ e : τ  ∧
    ∀ (C : gctx) τ' (HC : typed_ctx C Γ τ [] τ'),
    (∀ ℓ, rtc std.step (gfill_ctx C e) (cc_Error ℓ) → L ℓ ∨ ℓ ∈ (labels_ctx C)).

  Definition robust_up_to_alt (L : label → Prop) Γ (e : gexpr) τ : Prop :=
    Γ ⊢ e : τ  ∧
    ∀ (C : gctx) τ' (HC : typed_ctx C Γ τ [] τ'),
    (∀ ℓ, rtc step ⟨ gfill_ctx C e ⟩ (Error ℓ) → L ℓ ∨ ℓ ∈ (labels_ctx C)).

  Notation robust_alt := (robust_up_to_alt (fun _ => False)).
  Notation robust := (robust_up_to (fun _ => False)).

  Lemma robust_up_to_alt_valid L Γ e τ :
    robust_up_to_alt L Γ e τ → robust_up_to L Γ e τ.
  Proof.
    intros H. destruct H as [Heτ H]. split; auto. intros C τ' HC ℓ Hsteps. apply (H C τ' HC ℓ).
    eapply ref_error; eauto. by eapply typed_ctx_typed.
  Qed.

  Definition import ℓ Γ τ (e : dexpr) : gexpr :=
     gfill_ctx (linker ℓ Γ τ) ⌈⌈ e ⌉⌉.

  Lemma rel_ctx_fill_expr {L} (Le Lc : LabelRel) {Γ τ Γ' τ' e e' C C'}
      (HCC' : ctx_rel_typed Lc C C' Γ τ Γ' τ')
      (Hee' : open_exprel_typed Γ Le e e' τ)
      (H : Le ⊔ Lc ⊑ L) :
    open_exprel_typed Γ' L (fill_ctx C e) (fill_ctx C' e') τ'.
  Proof.
    eapply open_exprel_typed_weaken.
    apply (HCC' (Le ⊔ Lc)). by apply le_permissive_join_r.
    eapply open_exprel_typed_weaken. apply Hee'.
    by apply le_permissive_join_l. auto.
  Qed.

  Theorem general_theorem_lose_import ℓ Γ L (e e' : dexpr) (H : Closed_n (length Γ) e) τ
    (Hee' : open_exprel_typed Γ L e e' τ)
    (C : gctx) τ' (HC : typed_ctx C Γ τ [] τ') :
       ⟨gfill_ctx C (import ℓ Γ τ e)⟩ ≤{L ⊔ (InCastCalcCtx C)}
          (fill_ctx (trns_ctx C) e').
  Proof.
    repeat rewrite trns_fill_ctx.
    apply (refineL_trans
              ((InCastCalcCtx C) ⊔ (diagonal ({[ ℓ ]} : listset label)) ⊔ (InDynExpr e))
              ((InCastCalcCtx C) ⊔ L)
                (dfill_ctx (trns_ctx C)
                     (dfill_ctx (trns_ctx (linker ℓ Γ τ)) e))); [le_perm_solver | | ].
    - (* taking care of dyn embedding *)
      eapply logrel_adequacy.
      eapply (rel_ctx_fill_expr (diagonal ({[ℓ]} : listset label) ⊔ (InDynExpr e))). by eapply fundamental_ctx. 2: le_perm_solver.
      apply linker_compat; auto; try by labelrel_solver.
        by apply dyn_emb_trns_pres_closed_n.
        eapply open_exprel_typed_weaken. apply fundamental_l; auto. le_perm_solver.
    - (* superfluous linker *)
      eapply logrel_adequacy.
      eapply (rel_ctx_fill_expr L). by eapply fundamental_ctx. 2: le_perm_solver.
      apply linker_superfluous_l; auto.
  Qed.

  Theorem refined_dyn_emb_criterion_generalized Γ L (e : dexpr) τ
    (He : sem_typed_liable_to L Γ e τ) κ : robust_up_to L Γ (import κ Γ τ e) τ.
  Proof.
    apply robust_up_to_alt_valid.
    rewrite /robust_up_to. destruct He as [He Hc]. split.
    { rewrite /import. eapply typed_ctx_typed; [| apply linker_typed]. by apply typed_app_r, dyn_emb_typed. }
    intros. assert (HRef := general_theorem_lose_import κ _ _ _ _ Hc _ He _ _ HC).
    destruct HRef as [_ Hl]. specialize (Hl ℓ H). destruct Hl as (ℓ' & Hℓ' & _).
    revert Hℓ'. labelrel_solver.
  Qed.

  Theorem refined_dyn_emb_criterion Γ (e : dexpr) (H : Closed_n (length Γ) e) τ
    (He : sem_typed Γ e τ) κ : robust Γ (import κ Γ τ e) τ.
  Proof. by apply refined_dyn_emb_criterion_generalized. Qed.

End refined_dyn_emb_criterion.

(* below just stated in terms of dynamic language... *)
Section rrhp_sem_typed.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Theorem general_theorem_gain_import ℓ Γ L (e e' : dexpr) (H : Closed_n (length Γ) e') τ
    (Hee' : open_exprel_typed Γ L e e' τ)
    (C : gctx) τ' (HC : typed_ctx C Γ τ [] τ') :
    RefineL (L ⊔ (InCastCalcCtx C))
       (fill_ctx (trns_ctx C) e)
       ⟨gfill_ctx C (import ℓ Γ τ e')⟩.
  Proof.
    repeat rewrite trns_fill_ctx.
    apply (refineL_trans
              ((InCastCalcCtx C) ⊔ L)
              ((InCastCalcCtx C) ⊔ (diagonal ({[ ℓ ]} : listset label)) ⊔ (InDynExpr e'))
                (dfill_ctx (trns_ctx C)
                     (dfill_ctx (trns_ctx (linker ℓ Γ τ)) e'))); [le_perm_solver | | ].
    - (* superfluous linker *)
      eapply logrel_adequacy.
      eapply (rel_ctx_fill_expr L). by eapply fundamental_ctx. 2: le_perm_solver.
      apply linker_superfluous_r; auto.
    - (* taking care of dyn embedding *)
      eapply logrel_adequacy.
      eapply (rel_ctx_fill_expr (diagonal ({[ℓ]} : listset label) ⊔ (InDynExpr e'))). by eapply fundamental_ctx. 2: le_perm_solver.
      apply linker_compat; auto; try by labelrel_solver.
        by apply dyn_emb_trns_pres_closed_n.
        eapply open_exprel_typed_weaken. apply fundamental_r; auto. le_perm_solver.
  Qed.

  Theorem rrhp_import_sem_typed Γ L (e : dexpr) τ (He : sem_typed_liable_to L Γ e τ) :
   ∀ ℓ (C : gctx) τ' (HC : typed_ctx C Γ τ [] τ'),
       ⟨gfill_ctx C (import ℓ Γ τ e)⟩
           ≡{ L ⊔ labels_ctx C }
       (fill_ctx (trns_ctx C) e).
  Proof.
    intros. destruct He as [He Hc]. split.
    - eapply RefineL_weaken.
      eapply general_theorem_lose_import; eauto. le_perm_solver.
    - eapply RefineL_weaken.
      eapply general_theorem_gain_import; eauto. le_perm_solver.
  Qed.


End rrhp_sem_typed.

Section rrhp_untyped.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Theorem general_theorem_gain_dyn_emb n (e : dexpr) (H : Closed_n n e)
    (C : gctx) τ (HC : typed_ctx C (replicate n Unknown) Unknown [] τ) :
    RefineL (InCastCalcCtx C ⊔ InDynExpr e)
       (fill_ctx (trns_ctx C) e)
       ⟨gfill_ctx C ⌈⌈ e ⌉⌉⟩.
  Proof.
    repeat rewrite trns_fill_ctx.
    eapply logrel_adequacy.
    eapply (rel_ctx_fill_expr (InDynExpr e)).
    by eapply fundamental_ctx. 2: le_perm_solver.
    eapply open_exprel_typed_weaken. apply fundamental_r; auto. le_perm_solver.
  Qed.

  Theorem general_theorem_lose_dyn_emb n (e : dexpr) (H : Closed_n n e)
    (C : gctx) τ (HC : typed_ctx C (replicate n Unknown) Unknown [] τ) :
    RefineL (InCastCalcCtx C ⊔ InDynExpr e)
       ⟨gfill_ctx C ⌈⌈ e ⌉⌉⟩
       (fill_ctx (trns_ctx C) e).
  Proof.
    repeat rewrite trns_fill_ctx.
    eapply logrel_adequacy.
    eapply (rel_ctx_fill_expr (InDynExpr e)).
    by eapply fundamental_ctx. 2: le_perm_solver.
    eapply open_exprel_typed_weaken. apply fundamental_l; auto. le_perm_solver.
  Qed.

  Theorem rrhp_dyn_emb_untyped n (e : dexpr) (H : Closed_n n e) :
    ∀ (C : gctx) τ (HC : typed_ctx C (replicate n Unknown) Unknown [] τ),
       (fill_ctx (trns_ctx C) e)
           ≡{ (labels_expr e : label → Prop) ⊔ (labels_ctx C) }
       ⟨gfill_ctx C ⌈⌈ e ⌉⌉⟩.
  Proof.
    intros. split.
    - eapply RefineL_weaken.
      eapply general_theorem_gain_dyn_emb; eauto. le_perm_solver.
    - eapply RefineL_weaken.
      eapply general_theorem_lose_dyn_emb; eauto. le_perm_solver.
  Qed.

End rrhp_untyped.
