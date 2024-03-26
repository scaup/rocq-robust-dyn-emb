From main.prelude Require Import imports autosubst.
From main.dyn_lang Require Import definition lib lemmas tactics labels.
From main.maps.wrapper Require Import definition.

Section lemmas.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma AppWithList_d_subst e fs σ :
    (AppWithList_d e fs).[σ] = AppWithList_d e.[σ] (subst σ <$> fs).
  Proof.
    induction fs. by asimpl.
    simpl. rewrite /AppAn. f_equiv. by rewrite IHfs.
  Qed.

  Definition WrapContextVarsSubst_d (fs es : list expr) (H : length fs = length es) (Hfs : Forall Closed fs) :
    subst (subst_list es) <$> (WrapContextVars_d fs) = zip_with AppAn fs es.
  Proof.
    eapply (list_eq_same_length _ _ (length fs)).
    rewrite zip_with_length. lia.
    rewrite /WrapContextVars_d. by rewrite fmap_length imap_length.
    intros.
    rewrite list_lookup_fmap /WrapContextVars_d list_lookup_imap in H1.
    rewrite lookup_zip_with /= in H2. simplify_option_eq.
    rewrite /AppAn. f_equiv. assert (Hf := Forall_lookup_1 _ _ _ _ Hfs Heqo). by rewrite Hf.
    by rewrite -Nat.add_comm (subst_list_lookup_some  _ _ _ Heqo0).
  Qed.

  Definition AppWithList_ectx_d (fs : list expr) : list ectx_item :=
    (AppLCtx ν) <$> fs.

  Definition AppWithList_ectx_agree_d' e (es : list expr) :
    AppWithList_d e es = fill (AppWithList_ectx_d es) e.
  Proof.
    induction es as [|e' es]; first by simpl.
    simpl. rewrite /AppAn. by rewrite IHes.
  Qed.

  Definition LamN_d (n : nat) : expr → expr := Nat.iter n Lam.

  Lemma LamN_subst_d (n : nat) e σ : (LamN_d n e).[σ] = (LamN_d n e.[upn n σ]).
  Proof.
    generalize dependent σ.
    induction n; first by simpl. intro σ. specialize (IHn (up σ)).
    simpl. f_equiv. rewrite IHn. by asimpl.
  Qed.

  Lemma Forall2_ind_rev {A B : Type} : ∀ (R : A → B → Prop) ( P : list A → list B → Prop ),
    P [] []
    → (∀ (x : A) (y : B) (l : list A) (l' : list B), R x y → Forall2 R l l' → P l l' → P (l ++ [x]) (l' ++ [y]))
      → ∀ (l : list A) (l' : list B), Forall2 R l l' → P l l'.
  Proof.
    intros R P HP0 HPS l.
    induction l using rev_ind.
    - intros l' HF.
      assert (abs := Forall2_length _ _ _ HF). destruct l'; inversion abs. auto.
    - intros l' HF.
      destruct l' as [|x' l'] using rev_ind.
      assert (abs := Forall2_length _ _ _ HF). rewrite app_length /= in abs. lia.
      assert (H := Forall2_length _ _ _ HF). repeat rewrite app_length /= Nat.add_comm /= in H. inversion H.
      edestruct (Forall2_app_inv _ l [x] l' [x'] H1 HF) as [a b].
      apply HPS; auto. by inversion b; simplify_eq.
  Qed.

  Lemma LamN_AppWithList_rtc_to_vals ts :
    ∀ vs (H : Forall2 (fun t v => rtc step_ne t (of_val v)) ts vs) e,
    rtc step_ne (AppWithList_d (LamN_d (length ts) e) ts)
                (e.[subst_list (of_val <$> vs)]).
  Proof.
    intros vs H.
    (* induction H using Forall2_ind_rev. *)
    eapply (Forall2_ind_rev _ (fun ts vs => ∀ e : expr, rtc step_ne (AppWithList_d (LamN_d (length ts) e) ts) e.[subst_list (of_val <$> vs)])); eauto.
    - intros. asimpl. apply rtc_refl.
    - clear H ts vs. simpl. intros t v ts' vs' Htv HF2' IH e.
      rewrite app_length /= Nat.add_comm /=.
      rewrite AppWithList_ectx_agree_d'. rewrite /AppWithList_ectx_d (fmap_app _ ts' [t]).
      rewrite fill_app. fold (AppWithList_ectx_d ts'). simpl.
      change (Lam ?e) with (of_val (LamV e)).
      eapply rtc_transitive. rw_fill. rewrite -fill_app.
      eapply (rtc_congruence (fill _)); intros. eapply fill_step; eauto. apply Htv.
      eapply rtc_transitive. rewrite fill_app. rw_fill_popped.
      eapply (rtc_congruence (fill _)); intros. eapply fill_step; eauto. apply rtc_once. step_solver. simpl.
      rewrite LamN_subst_d. rewrite fmap_app. rewrite subst_list_snoc -subst_comp.
      rewrite -(AppWithList_ectx_agree_d'). rewrite map_length.
      rewrite -(Forall2_length _ _ _ HF2'). apply IH.
  Qed.

End lemmas.
