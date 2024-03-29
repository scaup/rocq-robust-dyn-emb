From main.prelude Require Import imports autosubst base_lang.
From main.grad_lang Require Import definition contexts types typing.

(* Local Notation "|- C : Γh <---> τh --------- Γr <---> τr " := *)
(*   (typed_ctx C Γh τh Γr τr) (at level 74, Γr, C, Γh, τh, τr at next level). *)
(* Local Notation "\- C : Γh <--->  τh --------- Γr <---> τr " := *)
(*   (typed_ctx_item C Γh τh Γr τr) (at level 74, Γr, C, Γh, τh, τr at next level). *)

Definition LamN (n : nat) : expr → expr := Nat.iter n Lam.

Definition LamN_ctx (n : nat) : ctx := repeat CTX_Lam n.

Lemma LamN_sane (n : nat) : ∀ e, LamN n e = fill_ctx (LamN_ctx n) e.
Proof. induction n; intros; simpl; try done. by rewrite IHn. Qed.

Definition LamN_type (Γ : list type) τ : type :=
  foldl (fun T t => Bin Arrow t T) τ Γ.

Definition LamN_type_snoc (Γ : list type) τ' τ :
  LamN_type (Γ ++ [τ']) τ = (Bin Arrow τ' (LamN_type Γ τ)).
Proof. by rewrite /LamN_type foldl_snoc. Qed.

(* Context (τ1 τ2 τ3 τ4 τ : type). *)
(* Compute (LamN_type [τ1;τ2;τ3;τ4] τ). *)
(* Bin Arrow τ4 (Bin Arrow τ3 (Bin Arrow τ2 (Bin Arrow τ1 τ))) *)

Lemma LamN_ctx_typed Γ τ :
  typed_ctx (LamN_ctx (length Γ)) Γ τ [] (LamN_type Γ τ).
Proof.
  induction Γ as [|τ' τs IHτs] using rev_ind. simpl; econstructor.
  rewrite app_length /= Nat.add_1_r. econstructor.
  rewrite /LamN_type foldl_snoc. econstructor.
  change [τ'] with ([] ++ [τ']). by apply typed_ctx_app_r.
Qed.

Definition AppWithList (e : expr) (ts : list expr) :=
  foldr (fun f e => App e f) e ts.

(* Context (e1 e2 e3 e4 e : expr). *)
(* Compute (AppWithList e [e1;e2;e3;e4]). *)
(* App (App (App (App e e4) e3) e2) e1 *)

Definition AppWithList_ctx (ts : list expr) : ctx :=
  CTX_AppL <$> ts.

  (* foldr (fun t T => CTX_AppL t :: T) [] ts. *)
  (* foldl (fun T t => T ++ [ CTX_AppL t ] ) [] ts. *)

Definition AppWithList_ctx_snoc (ts : list expr) t' :
  AppWithList_ctx (ts ++ [t']) = AppWithList_ctx ts ++ [CTX_AppL t'].
Proof. by rewrite /AppWithList_ctx fmap_app. Qed.

(* Context (e1 e2 e3 e4 e : expr). *)
(* Compute (AppWithList_ctx [e1;e2;e3;e4]). *)
(* (* = [CTX_AppL e1; CTX_AppL e2; CTX_AppL e3; CTX_AppL e4] *) *)
(* Compute (fill_ctx (AppWithList_ctx [e1;e2;e3;e4]) e). *)
(* App (App (App (App e e4) e3) e2) e1 *)


Lemma Forall2_rev_ind {A B : Type} : ∀ (R : A → B → Prop) ( P : list A → list B → Prop ),
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

Lemma Forall2_rev_ind' {A B : Type} {l : list A} {l' : list B} {R : A → B → Prop} :
  Forall2 R l l' → ∀ ( P : list A → list B → Prop ),
    P [] []
    → (∀ (x : A) (y : B) (l : list A) (l' : list B), R x y → Forall2 R l l' → P l l' → P (l ++ [x]) (l' ++ [y]))
      → P l l'.
Proof. intros. eapply Forall2_rev_ind; eauto. Qed.

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

From main.prelude Require Import labels.

Definition wrap_ctx_vars_ascribe_up (ℓ : label) (Γ : list type) : list expr :=
  imap (fun l τ => (Ascribe ℓ τ Unknown (Var l))) Γ.

(* Definition WrapContextVars (fs : list expr) : list expr := *)
(*   (imap (fun l f => (App f (Var l))) fs). *)

Context (τ0 τ1 τ2 τ3 τ4 τ : type) (ℓ : label).
Compute (wrap_ctx_vars_ascribe_up ℓ [τ0;τ1;τ2;τ3;τ4]).

Lemma wrap_ctx_vars_ascribe_up_typed ℓ Γ :
  Forall (fun a => typed Γ a Unknown) (wrap_ctx_vars_ascribe_up ℓ Γ).
Proof.
  rewrite /wrap_ctx_vars_ascribe_up.
  induction Γ using rev_ind. constructor.
  rewrite imap_app. apply Forall_app. split.
  eapply (Forall_impl _ _ _ IHΓ). { intros. by apply typed_app_r. }
  repeat constructor. apply list_lookup_middle. lia.
Qed.
