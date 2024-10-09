From main.prelude Require Import base_lang imports autosubst.
From main.grad_lang Require Import definition types.

Definition binop_res_type (op : bin_op) : type :=
  Base match op with
  | PlusOp => Int | MinusOp => Int
  | EqOp => Bool | LeOp => Bool | LtOp => Bool
  end.

Reserved Notation "Γ ⊢ e : τ" (at level 74, e, τ at next level).

Inductive typed (Γ : list type) : expr → type → Prop :=
 | Var_typed x τ : Γ !! x = Some τ → Γ ⊢ Var x : τ
 | Base_typed b : Γ ⊢ Lit b : base_lit_type b
 (* | Unit_typed : Γ ⊢ Lit (LitUnit) : Base Unit *)
 (* | Bool_typed b : Γ ⊢ Lit (LitBool b) : Base Bool *)
 (* | Int_typed z : Γ ⊢ Lit (LitInt z) : Base Int *)
 | Seq_typed e1 e2 τ :
     Γ ⊢ e1 : Base Unit → Γ ⊢ e2 : τ → Γ ⊢ Seq e1 e2 : τ
 | If_typed e0 e1 e2 τ :
    Γ ⊢ e0 : Base Bool → Γ ⊢ e1 : τ → Γ ⊢ e2 : τ → Γ ⊢ If e0 e1 e2 : τ
 | BinOp_typed op e1 e2 :
     Γ ⊢ e1 : Base Int → Γ ⊢ e2 : Base Int → Γ ⊢ BinOp op e1 e2 : binop_res_type op
 (* functions *)
 | Lam_typed e τ1 τ2 :
    τ1 :: Γ ⊢ e : τ2 → Γ ⊢ Lam e : Bin Arrow τ1 τ2
 | App_typed e1 e2 τ1 τ2 :
    Γ ⊢ e1 : Bin Arrow τ1 τ2 → Γ ⊢ e2 : τ1 → Γ ⊢ App e1 e2 : τ2
 (* pairs *)
 | Pair_typed e1 e2 τ1 τ2 :
    Γ ⊢ e1 : τ1 → Γ ⊢ e2 : τ2 → Γ ⊢ Pair e1 e2 : Bin Product τ1 τ2
 | Fst_typed e τ1 τ2 : Γ ⊢ e : Bin Product τ1 τ2 → Γ ⊢ Fst e : τ1
 | Snd_typed e τ1 τ2 : Γ ⊢ e : Bin Product τ1 τ2 → Γ ⊢ Snd e : τ2
 (* sums *)
 | InjL_typed e τ1 τ2 : Γ ⊢ e : τ1 → Γ ⊢ InjL e : Bin Sum τ1 τ2
 | InjR_typed e τ1 τ2 : Γ ⊢ e : τ2 → Γ ⊢ InjR e : Bin Sum τ1 τ2
 | Case_typed e0 e1 e2 τ1 τ2 τ3 :
    Γ ⊢ e0 : Bin Sum τ1 τ2 → τ1 :: Γ ⊢ e1 : τ3 → τ2 :: Γ ⊢ e2 : τ3 →
    Γ ⊢ Case e0 e1 e2 : τ3
 (* assert! *)
 | Cast_typed ℓ τ1 τ2 (H : consistency τ1 τ2) e :
    Γ ⊢ e : τ1 → Γ ⊢ Cast ℓ τ1 τ2 e : τ2
 | Error_typed ℓ τ :
    Γ ⊢ Error ℓ : τ

where "Γ ⊢ e : τ" := (typed Γ e τ).

From main.grad_lang Require Import contexts.

Inductive typed_ctx_item :
    ctx_item → list type → type → list type → type → Prop :=
  | TP_CTX_Lam Γ τ τ' :
    typed_ctx_item CTX_Lam (τ :: Γ) τ' Γ (Bin Arrow τ τ')
  | TP_CTX_AppL Γ e2 τ τ' :
    typed Γ e2 τ →
    typed_ctx_item (CTX_AppL e2) Γ (Bin Arrow τ τ') Γ τ'
  | TP_CTX_AppR Γ e1 τ τ' :
    typed Γ e1 (Bin Arrow τ τ') →
    typed_ctx_item (CTX_AppR e1) Γ τ Γ τ'
  | TP_CTX_PairL Γ e2 τ τ' :
    typed Γ e2 τ' →
    typed_ctx_item (CTX_PairL e2) Γ τ Γ (Bin Product τ τ')
  | TP_CTX_PairR Γ e1 τ τ' :
    typed Γ e1 τ →
    typed_ctx_item (CTX_PairR e1) Γ τ' Γ (Bin Product τ τ')
  | TP_CTX_Fst Γ τ τ' :
    typed_ctx_item CTX_Fst Γ (Bin Product τ τ') Γ τ
  | TP_CTX_Snd Γ τ τ' :
    typed_ctx_item CTX_Snd Γ (Bin Product τ τ') Γ τ'
  | TP_CTX_InjL Γ τ τ' :
    typed_ctx_item CTX_InjL Γ τ Γ (Bin Sum τ τ')
  | TP_CTX_InjR Γ τ τ' :
    typed_ctx_item CTX_InjR Γ τ' Γ (Bin Sum τ τ')
  | TP_CTX_CaseL Γ e1 e2 τ1 τ2 τ' :
    typed (τ1 :: Γ) e1 τ' → typed (τ2 :: Γ) e2 τ' →
    typed_ctx_item (CTX_CaseL e1 e2) Γ (Bin Sum τ1 τ2) Γ τ'
  | TP_CTX_CaseM Γ e0 e2 τ1 τ2 τ' :
    typed Γ e0 (Bin Sum τ1 τ2) → typed (τ2 :: Γ) e2 τ' →
    typed_ctx_item (CTX_CaseM e0 e2) (τ1 :: Γ) τ' Γ τ'
  | TP_CTX_CaseR Γ e0 e1 τ1 τ2 τ' :
    typed Γ e0 (Bin Sum τ1 τ2) → typed (τ1 :: Γ) e1 τ' →
    typed_ctx_item (CTX_CaseR e0 e1) (τ2 :: Γ) τ' Γ τ'
  | TP_CTX_BinOpL op Γ e2 :
    typed Γ e2 (Base Int) →
    typed_ctx_item (CTX_BinOpL op e2) Γ (Base Int) Γ (binop_res_type op)
  | TP_CTX_BinOpR op e1 Γ :
    typed Γ e1 (Base Int) →
    typed_ctx_item (CTX_BinOpR op e1) Γ (Base Int) Γ (binop_res_type op)
  | TP_CTX_IfL Γ e1 e2 τ :
    typed Γ e1 τ → typed Γ e2 τ →
    typed_ctx_item (CTX_IfL e1 e2) Γ ((Base Bool)) Γ τ
  | TP_CTX_IfM Γ e0 e2 τ :
    typed Γ e0 ((Base Bool)) → typed Γ e2 τ →
    typed_ctx_item (CTX_IfM e0 e2) Γ τ Γ τ
  | TP_CTX_IfR Γ e0 e1 τ :
    typed Γ e0 ((Base Bool)) → typed Γ e1 τ →
    typed_ctx_item (CTX_IfR e0 e1) Γ τ Γ τ
  | TP_CTX_SeqL Γ e2 τ :
    typed Γ e2 τ →
    typed_ctx_item (CTX_SeqL e2) Γ (Base Unit) Γ τ
  | TP_CTX_SeqR Γ e1 τ :
    typed Γ e1 (Base Unit) →
    typed_ctx_item (CTX_SeqR e1) Γ τ Γ τ
  | TP_CTX_Cast Γ ℓ τ1 τ2 (H : consistency τ1 τ2) :
    typed_ctx_item (CTX_Cast ℓ τ1 τ2) Γ τ1 Γ τ2.

Lemma typed_ctx_item_typed k Γ τ Γ' τ' e :
  typed Γ e τ → typed_ctx_item k Γ τ Γ' τ' →
  typed Γ' (fill_ctx_item k e) τ'.
Proof. induction 2; simpl; eauto using typed. Qed.

Inductive typed_ctx : ctx → list type → type → list type → type → Prop :=
  | TPCTX_nil Γ τ :
    typed_ctx nil Γ τ Γ τ
  | TPCTX_cons Γ1 τ1 Γ2 τ2 Γ3 τ3 Ci C :
    typed_ctx_item Ci Γ2 τ2 Γ3 τ3 →
    typed_ctx C Γ1 τ1 Γ2 τ2 →
    typed_ctx (Ci :: C) Γ1 τ1 Γ3 τ3.

Lemma typed_ctx_typed K Γ τ Γ' τ' e :
  typed Γ e τ → typed_ctx K Γ τ Γ' τ' → typed Γ' (fill_ctx K e) τ'.
Proof. induction 2; simpl; eauto using typed_ctx_item_typed. Qed.

Lemma typed_app_r Γ Γ' e τ (H : typed Γ e τ) :
  typed (Γ ++ Γ') e τ.
Proof.
  induction H; try by econstructor.
  econstructor. rewrite (lookup_app_l Γ Γ' x); eauto. by eapply lookup_lt_Some.
Qed.

Lemma typed_ctx_item_app_r Ci Γ τ Γ' τ' τs :
  typed_ctx_item Ci Γ τ Γ' τ' →
  typed_ctx_item Ci (Γ ++ τs) τ (Γ' ++ τs) τ'.
Proof.
  intro H. destruct H; try by econstructor; (try done);
    (try change (?τ :: Γ ++ τs) with ((τ :: Γ) ++ τs)); apply typed_app_r; auto.
Qed.

Lemma typed_ctx_app_r C Γ τ Γ' τ' τs :
  typed_ctx C Γ τ Γ' τ' →
  typed_ctx C (Γ ++ τs) τ (Γ' ++ τs) τ'.
Proof.
  intro H. induction H.
  - constructor.
  - econstructor. 2: eapply IHtyped_ctx.
    by apply typed_ctx_item_app_r.
Qed.

Lemma typed_ctx_compose Γ1 Γ2 Γ3 K12 K23 τ1 τ2 τ3 :
  typed_ctx K23 Γ2 τ2 Γ3 τ3 →
  typed_ctx K12 Γ1 τ1 Γ2 τ2 →
  typed_ctx (K23 ++ K12) Γ1 τ1 Γ3 τ3.
Proof.
  revert K12 Γ1 Γ2 Γ3 τ1 τ2 τ3; induction K23 => K12 Γ Γ2 Γ3 τ1 τ2 τ3; simpl.
  - by inversion 1; subst.
  - intros Htc1 Htc2. inversion Htc1; subst.
    econstructor; last eapply IHK23; eauto.
Qed.
