From main.prelude Require Import imports autosubst base_lang lists labels.
From main.grad_lang Require Import types.
From main.dyn_lang Require Import definition contexts lib casts.
From main.maps.linker.components Require Import common.

Section dyn.

  Notation App := AppAn.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Definition LamN (n : nat) : expr → expr := Nat.iter n Lam.

  Definition LamN_ctx (n : nat) : ctx := repeat CTX_Lam n.

  Definition AppWithList (e : expr) (ts : list expr) :=
    foldr (fun f e => App e f) e ts.

  Definition AppWithList_ctx {Hν : NeverOccurs ν} (ts : list expr) : ctx :=
    CTX_AppL ν <$> ts.

  Definition wrap_ctx_vars_ascribe_up (ℓ : label) (Γ : list type) : list expr :=
    imap (fun l τ => (App (of_val $ cast' ℓ τ Unknown) (Var l))) Γ.

End dyn.

From main.prelude Require Import big_op_three.
From main.dyn_lang Require Import lemmas tactics.
From main.logrel Require Import rfn definition lib.small_helpers lemmas.casts_superfluous.
From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

Section lemmas.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma fill_AppWithList_ctx es e :
    fill_ctx (AppWithList_ctx es) e = AppWithList e es.
  Proof. revert e. induction es; intros. auto. by rewrite /= /AppAn IHes. Qed.

  Lemma fill_LamN_ctx n e :
    fill_ctx (LamN_ctx n) e = LamN n e.
  Proof. revert e. induction n; intros. auto. by rewrite /= /AppAn IHn. Qed.

  Lemma AppWithList_subst e fs σ :
    (AppWithList e fs).[σ] = AppWithList e.[σ] (subst σ <$> fs).
  Proof.
    induction fs. by asimpl.
    simpl. rewrite /AppAn. f_equiv. by rewrite IHfs.
  Qed.

  Definition wrap_ctx_vars_ascribe_up_subst ℓ Γ (es : list expr) (H : length Γ = length es) :
    subst (subst_list es) <$> (wrap_ctx_vars_ascribe_up ℓ Γ) = zip_with (fun τ e => AppAn (of_val $ cast' ℓ τ Unknown) e) Γ es.
  Proof.
    eapply (list_eq_same_length _ _ (length Γ)).
    rewrite zip_with_length. lia.
    rewrite /wrap_ctx_vars_ascribe_up. by rewrite fmap_length imap_length.
    intros.
    rewrite list_lookup_fmap /wrap_ctx_vars_ascribe_up list_lookup_imap in H1.
    rewrite lookup_zip_with /= in H2. simplify_option_eq.
    rewrite /AppAn. f_equiv. rewrite /cast'. destruct (consistency_decision H3 Unknown). by rewrite cast_closed. by asimpl.
    by apply subst_list_lookup_some.
  Qed.

  Definition AppWithList_ectx (fs : list expr) : list ectx_item :=
    (AppLCtx ν) <$> fs.

  Definition AppWithList_ectx_agree' e (es : list expr) :
    AppWithList e es = fill (AppWithList_ectx es) e.
  Proof.
    induction es as [|e' es]; first by simpl.
    simpl. rewrite /AppAn. by rewrite IHes.
  Qed.

  Lemma LamN_subst (n : nat) e σ : (LamN n e).[σ] = (LamN n e.[upn n σ]).
  Proof.
    generalize dependent σ.
    induction n; first by simpl. intro σ. specialize (IHn (up σ)).
    simpl. f_equiv. rewrite IHn. by asimpl.
  Qed.

  Lemma LamN_AppWithList_rtc_to_vals ts :
    ∀ vs (H : Forall2 (fun t v => rtc step_ne t (of_val v)) ts vs) e,
    rtc step_ne (AppWithList (LamN (length ts) e) ts)
                (e.[subst_list (of_val <$> vs)]).
  Proof.
    intros vs H.
    (* induction H using Forall2_ind_rev. *)
    eapply (Forall2_rev_ind _ (fun ts vs => ∀ e : expr, rtc step_ne (AppWithList (LamN (length ts) e) ts) e.[subst_list (of_val <$> vs)])); eauto.
    - intros. asimpl. apply rtc_refl.
    - clear H ts vs. simpl. intros t v ts' vs' Htv HF2' IH e.
      rewrite app_length /= Nat.add_comm /=.
      rewrite AppWithList_ectx_agree'. rewrite /AppWithList_ectx (fmap_app _ ts' [t]).
      rewrite fill_app. fold (AppWithList_ectx ts'). simpl.
      change (Lam ?e) with (of_val (LamV e)).
      eapply rtc_transitive. rw_fill. rewrite -fill_app.
      eapply (rtc_congruence (fill _)); intros. eapply fill_step; eauto. apply Htv.
      eapply rtc_transitive. rewrite fill_app. rw_fill_popped.
      eapply (rtc_congruence (fill _)); intros. eapply fill_step; eauto. apply rtc_once. step_solver. simpl.
      rewrite LamN_subst. rewrite fmap_app. rewrite subst_list_snoc -subst_comp.
      rewrite -(AppWithList_ectx_agree'). rewrite map_length.
      rewrite -(Forall2_length _ _ _ HF2'). apply IH.
  Qed.

  Lemma rfn_bindK {K K' t t' e e' Ψ Φ L} :
    t = fill K e →
    t' = fill K' e' →
    ⊢ rfn Ψ L e e' -∗ (∀ v v', Ψ v v' -∗ rfn Φ L (fill K (of_val v)) (fill K' (of_val v'))) -∗ rfn Φ L t t'.
  Proof. intros. simplify_eq. iApply rfn_bind'. Qed.

  (* "bind pop left" *)
  Ltac rfn_bind_pr :=
    iApply rfn_bindK; [ simpl; by rw_fill; eauto | simpl; by rw_fill_popped; eauto | simpl | simpl ].

  Ltac rfn_bind_pl :=
    iApply rfn_bindK; [ simpl; by rw_fill_popped; eauto | simpl; by rw_fill; eauto | simpl | simpl ].

  Ltac rfn_bind_pp :=
    iApply rfn_bindK; [ simpl; by rw_fill_popped; eauto | simpl; by rw_fill_popped; eauto | simpl | simpl ].

  Ltac rfn_bind :=
    iApply rfn_bindK; [ simpl; by rw_fill; eauto | simpl; by rw_fill; eauto | simpl | simpl ].

  Lemma open_exprel_superfluous_ctx_l_help ℓ α L (Γ : list type) :
    ⊢ ∀ Λ Λ' vs vs', big_sepL3 (fun τ v v' => valrel_typed τ L v v') Γ vs vs' -∗
        exprel_typed (LamN_type Γ α) L Λ Λ' -∗
          exprel_typed α L
            (AppWithList Λ (zip_with (λ τ0 e0, AppAn (of_val (cast' ℓ τ0 Unknown)) e0) Γ (of_val <$> vs)))
            (AppWithList Λ' (zip_with (λ τ0 e0, AppAn (of_val (LamV (Var 0))) e0) Γ (of_val <$> vs'))).
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
    change (AppLCtx ν <$> zip_with ?f ?a ?b) with (AppWithList_ectx (zip_with f a b)). simpl.
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

End lemmas.
