From main Require Import imports.
From main.grad_lang Require Import types definition.
From main.dyn_lang Require Import definition casts lib.

(* The translation to define the semantics of surface language. *)

Definition sf_expr := grad_lang.definition.expr .

Section expr.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Fixpoint trns (e : sf_expr) : expr :=
    match e with
    | grad_lang.definition.Lit b => Lit b
    | grad_lang.definition.Seq e1 e2 => Seq ν (trns e1) (trns e2)
    | grad_lang.definition.If e0 e1 e2 => If ν (trns e0) (trns e1) (trns e2)
    | grad_lang.definition.BinOp binop e1 e2 => BinOp ν binop (trns e1) (trns e2)
    | grad_lang.definition.Var v => Var v
    | grad_lang.definition.Lam e => Lam (trns e)
    | grad_lang.definition.App e1 e2 => App ν (trns e1) (trns e2)
    | grad_lang.definition.InjL e => InjL (trns e)
    | grad_lang.definition.InjR e => InjR (trns e)
    | grad_lang.definition.Case e0 e1 e2 => Case ν (trns e0) (trns e1) (trns e2)
    | grad_lang.definition.Fst e => Fst ν (trns e)
    | grad_lang.definition.Snd e => Snd ν (trns e)
    | grad_lang.definition.Pair e1 e2 => Pair (trns e1) (trns e2)
    | grad_lang.definition.Error ℓ => Error ℓ
    | Ascribe ℓ τ1 τ2 e => App ν (of_val $ cast' ℓ τ1 τ2) (trns e)
    end.

End expr.

Notation "⟨ e ⟩" := (trns e).
(* corresponds to ⌊ _ ⌋ in paper; latter is quite confusing in unicode though so we avoid it *)


From main.grad_lang Require Import contexts.
From main.dyn_lang Require Import contexts.

Section contexts.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Definition trns_ctx_item (Ci : grad_lang.contexts.ctx_item) : ctx_item :=
    match Ci with
    | grad_lang.contexts.CTX_Lam => CTX_Lam
    | grad_lang.contexts.CTX_AppL e2 => CTX_AppL ν (trns e2)
    | grad_lang.contexts.CTX_AppR e1 => CTX_AppR ν (trns e1)
    | grad_lang.contexts.CTX_PairL e2 => CTX_PairL (trns e2)
    | grad_lang.contexts.CTX_PairR e1 => CTX_PairR (trns e1)
    | grad_lang.contexts.CTX_Fst => CTX_Fst ν
    | grad_lang.contexts.CTX_Snd => CTX_Snd ν
    | grad_lang.contexts.CTX_InjL => CTX_InjL
    | grad_lang.contexts.CTX_InjR => CTX_InjR
    | grad_lang.contexts.CTX_CaseL e1 e2 => CTX_CaseL ν (trns e1) (trns e2)
    | grad_lang.contexts.CTX_CaseM e0 e2 => CTX_CaseM ν (trns e0) (trns e2)
    | grad_lang.contexts.CTX_CaseR e0 e1 => CTX_CaseR ν (trns e0) (trns e1)
    | grad_lang.contexts.CTX_BinOpL op e2 => CTX_BinOpL ν op (trns e2)
    | grad_lang.contexts.CTX_BinOpR op e1 => CTX_BinOpR ν op (trns e1)
    | grad_lang.contexts.CTX_IfL e1 e2 => CTX_IfL ν (trns e1) (trns e2)
    | grad_lang.contexts.CTX_IfM e0 e2 => CTX_IfM ν (trns e0) (trns e2)
    | grad_lang.contexts.CTX_IfR e0 e1 => CTX_IfR ν (trns e0) (trns e1)
    | grad_lang.contexts.CTX_SeqL e2 => CTX_SeqL ν (trns e2)
    | grad_lang.contexts.CTX_SeqR e1 => CTX_SeqR ν (trns e1)
    | CTX_Ascribe ℓ τ1 τ2 => CTX_AppR ν (of_val $ cast' ℓ τ1 τ2)
        (* (CTX_AppR ν $ match consistency_decision τ1 τ2 with *)
        (*               | inl Pc => (of_val $ cast ℓ τ1 τ2 Pc) *)
        (*               | inr _ => Lit LitUnit *)
        (*               end) *)
    end.

  Definition trns_ctx (C : grad_lang.contexts.ctx) : ctx :=
    trns_ctx_item <$> C.

  Lemma trns_fill_ctx_item Ci e :
    ⟨ grad_lang.contexts.fill_ctx_item Ci e ⟩ = fill_ctx_item (trns_ctx_item Ci) ⟨ e ⟩.
  Proof. destruct Ci; eauto. Qed.
  Lemma trns_fill_ctx C e :
    ⟨ grad_lang.contexts.fill_ctx C e ⟩ = fill_ctx (trns_ctx C) ⟨ e ⟩.
  Proof. induction C; auto. by rewrite /= -IHC trns_fill_ctx_item. Qed.

  Lemma trns_ctx_app C C' : trns_ctx (C ++ C') = trns_ctx C ++ trns_ctx C'.
  Proof. by rewrite /trns_ctx fmap_app. Qed.

End contexts.
