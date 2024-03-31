From main.prelude Require Import imports autosubst base_lang lists labels.
From main.grad_lang Require Import types typing labels.
From main.dyn_lang Require Import definition contexts lib casts.
From main.maps.linker.components Require Import grd common agree dyn.



From main.prelude Require Import big_op_three.
From main.dyn_lang Require Import lemmas tactics.
From main.logrel Require Import rfn definition lib.small_helpers lemmas.casts_superfluous lemmas.fun_grad_into_dyn.
From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

Section superfluous_l.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma LamN_ctx_no_lables n : InGradCtx (grd.LamN_ctx n) ⊑ ⊥.
  Proof. rewrite /InGradCtx /unary_conj. intros l l'. induction n; set_solver. Qed.

  Lemma LamN_ctx_rel_typed Γ τ :
    ctx_rel_typed ⊥ (LamN_ctx (length Γ)) (LamN_ctx (length Γ)) Γ τ [] (LamN_type Γ τ).
  Proof.
    rewrite -LamN_ctx_agree.
    eapply ctx_rel_typed_weaken.
    2: apply fundamental_ctx. apply LamN_ctx_no_lables.
    apply LamN_ctx_typed.
  Qed.

  Lemma open_exprel_LamN_type Γ L e e' τ :
    open_exprel_typed Γ L e e' τ →
    open_exprel_typed [] L
      (LamN (length Γ) e)
      (LamN (length Γ) e') (LamN_type Γ τ).
  Proof. intro Hee'. do 2 rewrite -fill_LamN_ctx. apply LamN_ctx_rel_typed. intros ℓ ℓ' Hll. exfalso. apply Hll. auto. Qed.

  Lemma open_exprel_superfluous_ctx_l  L ℓ Γ e (HCe : Closed_n (length Γ) e) e' τ :
    open_exprel_typed Γ L e e' τ →
    open_exprel_typed Γ L
      (AppWithList (LamN (length Γ) ((App ν (of_val $ cast' ℓ Unknown τ) e)))
                   (wrap_ctx_vars_ascribe_up ℓ Γ))
      e' τ.
  Proof.
    intros Hee'.
    iIntros (Δ HLΔ vs vs') "#Hvsvs'".
    iDestruct (big_sepL3_length with "Hvsvs'") as "[%eq1 %eq2]". rewrite -eq1 in eq2.
    iApply (rfn_steps_r_inv (AppWithList (LamN _ e') (zip_with (λ τ0 e0, AppAn (of_val (LamV (Var 0))) e0) Γ (of_val <$> vs')))).
    { eapply LamN_AppWithList_rtc_to_vals.
      rewrite zip_with_fmap_r.
      assert (zip_with
       (λ (_ : type) (z : val),
          AppAn (of_val (LamV (Var 0))) (of_val z)) Γ vs' = fmap (fun (z : val) => AppAn (of_val (LamV (Var 0))) (of_val z)) vs') as ->.
      { apply list_eq.
        intros i. destruct (decide (i < length Γ)).
        rewrite lookup_zip_with. rewrite list_lookup_fmap.
        destruct (lookup_lt_is_Some_2 vs' i) as [v' eq]. lia. rewrite eq. simpl.
        destruct (lookup_lt_is_Some_2 Γ i) as [t eq']. lia. simplify_option_eq. auto.
        rewrite lookup_zip_with. rewrite list_lookup_fmap.
        assert (HHH := lookup_ge_None_2 vs' i ltac:(lia)).
        assert (HHHH := lookup_ge_None_2 Γ i ltac:(lia)). by simplify_option_eq. }
      apply Forall2_fmap_l. apply Forall_Forall2_diag. simpl.
      apply Forall_true. intros. apply rtc_once. step_solver. }
    rewrite AppWithList_subst.
    rewrite wrap_ctx_vars_ascribe_up_subst.
    rewrite LamN_subst. change (App ν ?a ?b).[?σ] with (App ν a.[σ] b.[σ]). rewrite HCe /= cast'_closed.
    iApply (open_exprel_superfluous_ctx_l_help ℓ τ Δ Γ with "Hvsvs'").
    rewrite zip_with_length_l.
    assert (Hee'' := (open_exprel_superfluous_rtn_l _ ℓ _ _ _ _ Hee')).
    assert (Hee''' := open_exprel_LamN_type Γ L _ _ τ Hee'').
    specialize (Hee''' Δ HLΔ [] []). asimpl in Hee'''.
    rewrite -cast_downwards_rw in Hee'''. iApply Hee'''. eauto.
    rewrite fmap_length. lia.
    rewrite fmap_length. lia.
  Qed.


End superfluous_l.
