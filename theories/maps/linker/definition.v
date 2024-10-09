From main.prelude Require Import imports labels.
From main.grad_lang Require Import definition types typing contexts.
From main.maps.linker.components Require Import common dyn grd.

(* Notation gexpr := grad_lang.definition.expr. *)
(* Notation dexpr := dyn_lang.definition.expr. *)
(* Notation gVar := grad_lang.definition.Var. *)
(* Notation gApp := grad_lang.definition.Var. *)

Section linker.

  (* todo; generalize to list of labels? *)
  Definition linker (ℓ : label) (Γ : list type) (τ : type) : ctx :=
     AppWithList_ctx (WrapVars ((fun τ => Cast ℓ τ Unknown) <$> Γ))
  ++ LamN_ctx (length Γ)
  ++ [ CTX_Cast ℓ Unknown τ ].

  Lemma linker_typed ℓ Γ τ :
    let n := length Γ in
    typed_ctx (linker ℓ Γ τ) (replicate n Unknown ++ Γ) Unknown
                             Γ τ.
  Proof.
    apply (typed_ctx_compose _ Γ _ _ _ _ (LamN_type (replicate (length Γ) Unknown) τ)).
    apply AppWithList_ctx_typed'.
    { apply Forall2_replicate_l. by rewrite /WrapVars imap_length fmap_length.
      apply wrap_ctx_vars_ascribe_up_typed. }
    apply (typed_ctx_compose _ (replicate (length Γ) Unknown ++ Γ) _ _ _ _ τ).
    rewrite <- (app_nil_l Γ) at 4.
    apply typed_ctx_app_r. rewrite <- (replicate_length (length Γ) Unknown) at 1.
    apply LamN_ctx_typed. repeat econstructor.
  Qed.

End linker.

From main.prelude Require Import autosubst.
From main.grad_lang Require Import labels.
From main.maps Require Import grad_into_dyn.definition.
From main.logrel Require Import definition lemmas.fun_grad_into_dyn.
From main.dyn_lang Require Import definition contexts.
From main.maps.linker.components Require Import lemmas agree.

Section lemmas.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma linker_compat' L ℓ (H : L ℓ ℓ) Γ τ :
            ctx_rel_typed L
              (trns_ctx $ linker ℓ Γ τ)
              (trns_ctx $ linker ℓ Γ τ) (replicate (length Γ) Unknown ++ Γ) Unknown Γ τ.
  Proof.
    eapply ctx_rel_typed_weaken.
    2: { apply fundamental_ctx. apply linker_typed. }
    rewrite /linker.
    intros l l' Hll'.
    rewrite /InGradCtx /diagonal in Hll'.
    assert (Ha := AppWithList_ctx_wrap_ctx_vars_ascribe_up_lables ℓ Γ).
    (* Set Printing Coercions. *)
    rewrite /elemhood in Hll'.
    repeat rewrite labels_ctx_app in Hll'.
    rewrite LamN_ctx_lables in Hll'. simpl in Hll'. destruct Hll' as [a b].
    assert ((l ∈ ({[ℓ]} : listset label))). set_solver.
    assert ((l' ∈ ({[ℓ]} : listset label))). set_solver.
    by rewrite (elem_of_singleton_1 _ _ H0) (elem_of_singleton_1 _ _ H1).
  Qed.

  Lemma linker_compat L ℓ (H : L ℓ ℓ) Γ e e' (HCe : Closed_n (length Γ) e) (HCe' : Closed_n (length Γ) e') τ :
    open_exprel_typed (replicate (length Γ) Unknown) L e e' Unknown →
    open_exprel_typed Γ L (fill_ctx (trns_ctx (linker ℓ Γ τ)) e)
                          (fill_ctx (trns_ctx (linker ℓ Γ τ)) e') τ.
  Proof.
    intros Hee'.
    apply (linker_compat' L ℓ H Γ τ L (le_permissive_refl_inst L) e e').
    apply open_exprel_typed_app_ctx; eauto; try by rewrite replicate_length.
  Qed.

  Lemma linker_superfluous_l L ℓ Γ e e' (HCe : Closed_n (length Γ) e) τ :
    open_exprel_typed Γ L e e' τ →
    open_exprel_typed Γ L (fill_ctx (trns_ctx (linker ℓ Γ τ)) e) e' τ.
  Proof.
    intro Hee'.
    rewrite /linker. repeat rewrite trns_ctx_app.
    rewrite AppWithList_ctx_agree LamN_ctx_agree /=.
    rewrite wrap_ctx_vars_ascribe_up_agree /=.
    repeat rewrite -fill_ctx_app /=.
    rewrite fill_LamN_ctx fill_AppWithList_ctx.
    apply open_exprel_superfluous_ctx_l; auto.
  Qed.

  Lemma linker_superfluous_r L ℓ Γ e e' (HCe' : Closed_n (length Γ) e') τ :
    open_exprel_typed Γ L e e' τ →
    open_exprel_typed Γ L e (fill_ctx (trns_ctx (linker ℓ Γ τ)) e') τ.
  Proof.
    intro Hee'.
    rewrite /linker. repeat rewrite trns_ctx_app.
    rewrite AppWithList_ctx_agree LamN_ctx_agree /=.
    rewrite wrap_ctx_vars_ascribe_up_agree /=.
    repeat rewrite -fill_ctx_app /=.
    rewrite fill_LamN_ctx fill_AppWithList_ctx.
    apply open_exprel_superfluous_ctx_r; auto.
  Qed.

End lemmas.
