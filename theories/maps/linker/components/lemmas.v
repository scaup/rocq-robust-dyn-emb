From main.cast_calc Require Import types labels.
From main.dyn_lang Require Import definition casts lib tactics lemmas.
From main.logrel Require Import rfn definition lib.small_helpers lemmas.casts_superfluous lemmas.fun_grad_into_dyn.
From main.maps.linker.components Require Import common grd dyn agree.

From main.prelude Require Import big_op_three labels autosubst.
From iris.proofmode Require Import tactics.

Section superfluous_l.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma open_exprel_superfluous_rtn_l L ℓ Γ e e' τ :
    open_exprel_typed Γ L e e' τ →
    open_exprel_typed Γ L
      (App ν (of_val $ cast' ℓ Unknown τ) e) e' τ.
  Proof.
    iIntros (Hee' Δ HLΔ vs vs') "#Hvsvs'". rewrite /= cast'_closed.
    rw_fill.
    iApply (@rfn_bindK [AppRCtx _ _] []). eauto. eauto. iApply Hee'; eauto.
    simpl.
    iApply cast_upwards_val_superfluous_l.
  Qed.

  Lemma open_exprel_superfluous_ctx_l_help ℓ α L (Γ : list type) :
    ⊢ ∀ Λ Λ' vs vs', big_sepL3 (fun τ v v' => valrel_typed τ L v v') Γ vs vs' -∗
        exprel_typed (LamN_type Γ α) L Λ Λ' -∗
          exprel_typed α L
            (AppWithList Λ (zip_with (λ τ0 e0, App ν (of_val (cast' ℓ τ0 Unknown)) e0) Γ (of_val <$> vs)))
            (AppWithList Λ' (zip_with (λ τ0 e0, App ν (of_val (LamV (Var 0))) e0) Γ (of_val <$> vs'))).
  Proof.
    induction Γ as [|τ Γn IHΓ] using rev_ind; try by auto.
    iIntros (Λ Λ' vs vs') "#Hvsvs'".
    (* pure admin to get lists of right shape etc.. *)
    iDestruct (big_sepL3_length with "Hvsvs'") as "[%eq1 %eq2]".
    rewrite -eq1 in eq2. rewrite app_length Nat.add_1_r in eq1, eq2.
    destruct vs as [| v vsn] using rev_ind; try by inversion eq1. clear IHvsn.
    destruct vs' as [| v' vsn'] using rev_ind; try by inversion eq2. clear IHvsn'.
    iDestruct (big_sepL3_app_inv with "Hvsvs'") as "[#Hvsvs'' [#Hvv' _]]"; auto.
    repeat rewrite app_length Nat.add_1_r in eq1, eq2. inversion eq1. inversion eq2. clear eq1 eq2.
    iIntros "#HΛΛ'".
    (* make it to values *)
    rewrite LamN_type_snoc. do 2 rewrite AppWithList_ectx_agree'.
    rfn_bind. iApply "HΛΛ'". iClear "HΛΛ'". clear Λ Λ'. iIntros (Λ Λ') "#HΛΛ'".
    (* some more rewriting *)
    do 2 rewrite fmap_app.
    do 2 (rewrite zip_with_app; [|by rewrite fmap_length]). simpl.
    rewrite /AppWithList_ectx. do 2 rewrite fmap_app. do 2 rewrite fill_app.
    change (AppLCtx ν <$> zip_with ?f ?a ?b) with (@AppWithList_ectx ν (zip_with f a b)). simpl.
    rw_fill_popped. do 4 rewrite -(fill_app).
    rfn_bind. rfn_steps.
    { rewrite cast_upwards_rw. change (App ν) with (AppAn).
      iApply (cast_upwards_val_superfluous_l ℓ τ L $! Normal with "Hvv'"). }
    iIntros (w w') "#Hww'".
    (* prepare to use HΛΛ' *)
    do 2 rewrite app_nil_r.
    do 2 rewrite fill_app. simpl. dvals Λ Λ'.
    rfn_bind. rfn_steps. by iApply "HΛΛ'". iClear "Hww' HΛΛ'".
    (* use IH *)
    iIntros (Λ Λ') "HΛΛ'".
    do 2 rewrite -(AppWithList_ectx_agree').
    iApply IHΓ; eauto. rfn_val.
  Qed.

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
                   (WrapVars ((fun τ => App ν (of_val $ cast' ℓ τ Unknown)) <$> Γ)))
      e' τ.
  Proof.
    intros Hee'.
    iIntros (Δ HLΔ vs vs') "#Hvsvs'".
    iDestruct (big_sepL3_length with "Hvsvs'") as "[%eq1 %eq2]". rewrite -eq1 in eq2.
    iApply (rfn_steps_r_inv (AppWithList (LamN _ e') (zip_with (λ τ0 e0, AppAn (of_val (LamV (Var 0))) e0) Γ (of_val <$> vs')))).
    { eapply LamN_AppWithList_to_vals.
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
    rewrite WrapVars_subst.
    rewrite LamN_subst. change (App ν ?a ?b).[?σ] with (App ν a.[σ] b.[σ]). rewrite HCe /= cast'_closed.
    rewrite zip_with_fmap_l.
    iApply (open_exprel_superfluous_ctx_l_help ℓ τ Δ Γ with "Hvsvs'").
    rewrite zip_with_length_l.
    assert (Hee'' := (open_exprel_superfluous_rtn_l _ ℓ _ _ _ _ Hee')).
    assert (Hee''' := open_exprel_LamN_type Γ L _ _ τ Hee'').
    specialize (Hee''' Δ HLΔ [] []). asimpl in Hee'''.
    rewrite -cast_downwards_rw in Hee'''. iApply Hee'''. eauto.
    rewrite fmap_length. lia. apply Forall_fmap, Forall_true.
    intros t σ. asimpl. by rewrite cast'_closed.
    repeat rewrite fmap_length. lia.
  Qed.

End superfluous_l.

From main.logrel Require Import lib.weakestpre.

Section superfluous_r.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma open_exprel_superfluous_rtn_r L ℓ Γ e e' τ :
    open_exprel_typed Γ L e e' τ →
    open_exprel_typed Γ L
      e (App ν (of_val $ cast' ℓ Unknown τ) e') τ.
  Proof.
    iIntros (Hee' Δ HLΔ vs vs') "#Hvsvs'". rewrite /= cast'_closed.
    rw_fill.
    iApply (@rfn_bindK [] [AppRCtx _ _]). eauto. eauto. iApply Hee'; eauto.
    simpl.
    iApply cast_upwards_val_superfluous_r.
  Qed.

  Lemma help_r Δ ℓ Γ vs vs' :
    ⊢ big_sepL3
        (λ (τ : type) (v v' : val), valrel_typed τ Δ v v') Γ vs vs' -∗
    ∃ (ws' : list val),
      big_sepL3
        (λ (τ : type) (v w' : val), valrel_typed τ Δ v w') Γ vs ws' ∗
      ⌜ Forall3 (λ (τ : type) (v' w' : val), rtc step_ne (App ν (of_val $ cast' ℓ τ Unknown) (of_val v')) (of_val w') ) Γ vs' ws' ⌝.
  Proof.
    revert vs vs'.
    iInduction Γ as [|τ  Γ] "IH".
    - iIntros (vs vs') "Hvsvs'"; destruct vs as [|v vs]; auto; destruct vs' as [|v' vs']; auto; simpl. iExists []. iSplit; auto. iPureIntro. constructor.
    - iIntros (vs vs') "Hvsvs'"; destruct vs as [|v vs]; destruct vs' as [|v' vs']; auto.
      simpl. iDestruct "Hvsvs'" as "[Hvv' Hvsvs']". iSpecialize ("IH" with "Hvsvs'").
      iDestruct "IH" as (ws') "[H1 %H2]".
      (* use superfluous lemma *)
      iDestruct (cast_upwards_val_superfluous_r ℓ τ Δ $! Normal with "Hvv'") as "HHH".
      iDestruct (wp_val_inv with "HHH") as "HHH'".
      iDestruct "HHH'" as (w') "[%Hs Hvw']".
      iExists (w' :: ws'). iFrame. iPureIntro. constructor. by rewrite cast_upwards_rw. auto.
  Qed.

  Lemma open_exprel_superfluous_ctx_r_help L ℓ Γ e e' (He' : Closed_n (length Γ) e') τ :
    open_exprel_typed Γ L e e' τ →
    open_exprel_typed Γ L
      e
      (AppWithList (LamN (length Γ) e')
                   (WrapVars ((fun τ => App ν (of_val $ cast' ℓ τ Unknown)) <$> Γ))) τ.
  Proof.
    intros Hee'.
    iIntros (Δ HLΔ vs vs') "#Hvsvs'".
    iDestruct (big_sepL3_length with "Hvsvs'") as "[%eq1 %eq2]". rewrite -eq1 in eq2.
    iDestruct (help_r Δ ℓ with "Hvsvs'") as (ws') "[Hvs'ws' %Hs]".
    assert (eq3 := Forall3_length_lr _ _ _ _ Hs).
    iApply (rfn_steps_r e'.[subst_list (of_val <$> ws')]).
    { rewrite AppWithList_subst LamN_subst.
      rewrite WrapVars_subst.
      rewrite zip_with_fmap_r.
      repeat rewrite /= He'.
      assert (length Γ = length ((zip_with (λ (x : expr → expr) (z : val), x (of_val z))
          ((λ τ0 : type, App ν (of_val (cast' ℓ τ0 Unknown))) <$> Γ)
          vs'))) as eq.
      { rewrite zip_with_length fmap_length. lia. }
      rewrite -> eq at 1. clear eq. apply LamN_AppWithList_to_vals.
      rewrite zip_with_fmap_l.
      apply Forall2_same_length_lookup_2.
      rewrite zip_with_length. try lia.
      intros i x x' Hl Hl'.
      rewrite lookup_zip_with in Hl.
      assert (lt1 := lookup_lt_Some _ _ _  Hl').
      destruct (lookup_lt_is_Some_2 Γ i) as [t eq']. lia.
      simplify_option_eq.
      eapply (Forall3_lookup_lmr _ _ _ _ i _ _ _ Hs); auto.
      apply Forall_fmap, Forall_true. by intros t σ x; rewrite /= cast'_closed.
      by repeat rewrite fmap_length.
    } iApply Hee'; auto.
  Qed.

  Lemma open_exprel_superfluous_ctx_r L ℓ Γ e e' (He' : Closed_n (length Γ) e') τ :
    open_exprel_typed Γ L e e' τ →
    open_exprel_typed Γ L
      e
      (AppWithList (LamN (length Γ) ((App ν (of_val $ cast' ℓ Unknown τ) e')))
                   (WrapVars ((fun τ => App ν (of_val $ cast' ℓ τ Unknown)) <$> Γ))) τ.
  Proof.
    intros Hee'.
    apply open_exprel_superfluous_ctx_r_help; auto.
    intros σ. asimpl. by rewrite He' -cast_downwards_rw cast'_closed.
    by apply open_exprel_superfluous_rtn_r.
  Qed.

End superfluous_r.
