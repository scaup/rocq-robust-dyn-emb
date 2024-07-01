From main.prelude Require Import imports.
From main.dyn_lang Require Import definition contexts lib.

Section dyn.

  Notation App := AppAn.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Definition LamN (n : nat) : expr → expr := Nat.iter n Lam.

  Definition LamN_ctx (n : nat) : ctx := repeat CTX_Lam n.

  Definition AppWithList (e : expr) (ts : list expr) :=
    foldr (fun f e => App e f) e ts.

  Definition AppWithList_ctx {Hν : NeverOccurs ν} (ts : list expr) : ctx :=
    CTX_AppL ν <$> ts.

  Definition WrapVars (Ks : list (expr → expr)) : list expr :=
    imap (fun l K => (K (Var l))) Ks.

End dyn.

From main.prelude Require Import lists autosubst.
From main.dyn_lang Require Import lemmas tactics.

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

  Definition Closed_map (K : expr → expr) := ∀ σ e, (K e).[σ] = K e.[σ].

  Definition WrapVars_subst Ks (Hfs : Forall Closed_map Ks) (es : list expr) (H : length Ks = length es) :
    subst (subst_list es) <$> (WrapVars Ks) = zip_with (fun K e => K e) Ks es.
  Proof.
    eapply (list_eq_same_length _ _ (length Ks)).
    rewrite zip_with_length. lia.
    rewrite /WrapVars. by rewrite fmap_length imap_length.
    intros.
    rewrite list_lookup_fmap /WrapVars list_lookup_imap in H1.
    rewrite lookup_zip_with /= in H2. simplify_option_eq.
    rewrite (Forall_lookup_1  _ _ _ _ Hfs Heqo).
    f_equiv. by apply subst_list_lookup_some.
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

  Lemma LamN_AppWithList_to_vals ts :
    ∀ vs (H : Forall2 (fun t v => rtc step_ne t (of_val v)) ts vs) e,
    rtc step_ne (AppWithList (LamN (length ts) e) ts)
                (e.[subst_list (of_val <$> vs)]).
  Proof.
    intros vs H.
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

End lemmas.
