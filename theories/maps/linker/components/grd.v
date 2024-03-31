From main.prelude Require Import imports autosubst base_lang lists labels.
From main.grad_lang Require Import types.
From main.grad_lang Require Import definition contexts labels.
From main.maps.linker.components Require Import common.

(* Notation App := App. *)

Section components.

  Definition LamN (n : nat) : expr → expr := Nat.iter n Lam.

  Definition LamN_ctx (n : nat) : ctx := repeat CTX_Lam n.

  Definition AppWithList (e : expr) (ts : list expr) :=
    foldr (fun f e => App e f) e ts.

  Definition AppWithList_ctx (ts : list expr) : ctx :=
    CTX_AppL <$> ts.

  Definition wrap_ctx_vars_ascribe_up (ℓ : label) (Γ : list type) : list expr :=
    imap (fun l τ => (Ascribe ℓ τ Unknown (Var l))) Γ.

End components.

From main.grad_lang Require Import typing.

Section lemmas.

  Lemma LamN_ctx_no_lables n : InGradCtx (grd.LamN_ctx n) ⊑ ⊥.
  Proof. rewrite /InGradCtx /unary_conj. intros l l'. induction n; set_solver. Qed.

  Lemma LamN_ctx_lables n : labels_ctx (grd.LamN_ctx n) ≡ ∅.
  Proof. induction n; set_solver. Qed.

  Lemma AppWithList_ctx_lables (fs : list expr) :
    labels_ctx (AppWithList_ctx fs) ≡ fold_right (fun (e : expr) (L : listset label) => L ∪ labels_expr e) ∅ fs.
  Proof. induction fs. by simpl. simpl. rewrite IHfs. set_solver. Qed.

  Lemma AppWithList_ctx_wrap_ctx_vars_ascribe_up_lables ℓ Γ :
    labels_ctx (AppWithList_ctx (wrap_ctx_vars_ascribe_up ℓ Γ)) ⊆ {[ ℓ ]}.
  Proof.
    induction Γ using rev_ind. simpl. set_solver.
    rewrite /AppWithList_ctx /wrap_ctx_vars_ascribe_up. rewrite imap_app fmap_app.
    rewrite labels_ctx_app. set_solver.
  Qed.

 Lemma LamN_sane (n : nat) : ∀ e, LamN n e = fill_ctx (LamN_ctx n) e.
 Proof. induction n; intros; simpl; try done. by rewrite IHn. Qed.

  Lemma LamN_ctx_typed Γ τ :
    typed_ctx (LamN_ctx (length Γ)) Γ τ [] (LamN_type Γ τ).
  Proof.
    induction Γ as [|τ' τs IHτs] using rev_ind. simpl; econstructor.
    rewrite app_length /= Nat.add_1_r. econstructor.
    rewrite /LamN_type foldl_snoc. econstructor.
    change [τ'] with ([] ++ [τ']). by apply typed_ctx_app_r.
  Qed.

  Definition AppWithList_ctx_snoc (ts : list expr) t' :
    AppWithList_ctx (ts ++ [t']) = AppWithList_ctx ts ++ [CTX_AppL t'].
  Proof. by rewrite /AppWithList_ctx fmap_app. Qed.

  Definition AppWithList_ctx_typed Γ τ (es : list expr)
    (H : Forall2 (fun τ e => typed [] e τ) Γ es) :
    typed_ctx (AppWithList_ctx es) [] (LamN_type Γ τ) [] τ.
  Proof.
    eapply (Forall2_rev_ind' H). by econstructor. clear es H.
    intros t e ts es Het HF IH.
    rewrite AppWithList_ctx_snoc LamN_type_snoc.
    eapply typed_ctx_compose. eapply IH.
    econstructor. econstructor. eauto.
    econstructor.
  Qed.

  Definition AppWithList_ctx_typed' α Γ τ (es : list expr)
    (H : Forall2 (fun τ e => typed α e τ) Γ es) :
    typed_ctx (AppWithList_ctx es) α (LamN_type Γ τ) α τ.
  Proof.
    eapply (Forall2_rev_ind' H). by econstructor. clear es H.
    intros t e ts es Het HF IH.
    rewrite AppWithList_ctx_snoc LamN_type_snoc.
    eapply typed_ctx_compose. eapply IH.
    econstructor. econstructor. eauto.
    econstructor.
  Qed.

  Lemma wrap_ctx_vars_ascribe_up_typed ℓ Γ :
    Forall (fun a => typed Γ a Unknown) (wrap_ctx_vars_ascribe_up ℓ Γ).
  Proof.
    rewrite /wrap_ctx_vars_ascribe_up.
    induction Γ using rev_ind. constructor.
    rewrite imap_app. apply Forall_app. split.
    eapply (Forall_impl _ _ _ IHΓ). { intros. by apply typed_app_r. }
    repeat constructor. apply list_lookup_middle. lia.
  Qed.

End lemmas.
