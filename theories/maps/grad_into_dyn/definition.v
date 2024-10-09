From main Require Import imports.
From main.cast_calc Require Import types definition.
From main.dyn_lang Require Import definition casts lib.

(* The translation to define the semantics of surface language. *)

Definition sf_expr := cast_calc.definition.expr .

Section expr.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Fixpoint trns (e : sf_expr) : expr :=
    match e with
    | cast_calc.definition.Lit b => Lit b
    | cast_calc.definition.Seq e1 e2 => Seq ν (trns e1) (trns e2)
    | cast_calc.definition.If e0 e1 e2 => If ν (trns e0) (trns e1) (trns e2)
    | cast_calc.definition.BinOp binop e1 e2 => BinOp ν binop (trns e1) (trns e2)
    | cast_calc.definition.Var v => Var v
    | cast_calc.definition.Lam e => Lam (trns e)
    | cast_calc.definition.App e1 e2 => App ν (trns e1) (trns e2)
    | cast_calc.definition.InjL e => InjL (trns e)
    | cast_calc.definition.InjR e => InjR (trns e)
    | cast_calc.definition.Case e0 e1 e2 => Case ν (trns e0) (trns e1) (trns e2)
    | cast_calc.definition.Fst e => Fst ν (trns e)
    | cast_calc.definition.Snd e => Snd ν (trns e)
    | cast_calc.definition.Pair e1 e2 => Pair (trns e1) (trns e2)
    | Cast ℓ τ1 τ2 e => App ν (of_val $ cast' ℓ τ1 τ2) (trns e)
    | cast_calc.definition.Error ℓ => Error ℓ
    end.

End expr.

Notation "⟨ e ⟩" := (trns e).
(* corresponds to ⌊ _ ⌋ in paper; latter is quite confusing in unicode though so we avoid it *)


From main.cast_calc Require Import contexts.
From main.dyn_lang Require Import contexts.

Section contexts.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Definition trns_ctx_item (Ci : cast_calc.contexts.ctx_item) : ctx_item :=
    match Ci with
    | cast_calc.contexts.CTX_Lam => CTX_Lam
    | cast_calc.contexts.CTX_AppL e2 => CTX_AppL ν (trns e2)
    | cast_calc.contexts.CTX_AppR e1 => CTX_AppR ν (trns e1)
    | cast_calc.contexts.CTX_PairL e2 => CTX_PairL (trns e2)
    | cast_calc.contexts.CTX_PairR e1 => CTX_PairR (trns e1)
    | cast_calc.contexts.CTX_Fst => CTX_Fst ν
    | cast_calc.contexts.CTX_Snd => CTX_Snd ν
    | cast_calc.contexts.CTX_InjL => CTX_InjL
    | cast_calc.contexts.CTX_InjR => CTX_InjR
    | cast_calc.contexts.CTX_CaseL e1 e2 => CTX_CaseL ν (trns e1) (trns e2)
    | cast_calc.contexts.CTX_CaseM e0 e2 => CTX_CaseM ν (trns e0) (trns e2)
    | cast_calc.contexts.CTX_CaseR e0 e1 => CTX_CaseR ν (trns e0) (trns e1)
    | cast_calc.contexts.CTX_BinOpL op e2 => CTX_BinOpL ν op (trns e2)
    | cast_calc.contexts.CTX_BinOpR op e1 => CTX_BinOpR ν op (trns e1)
    | cast_calc.contexts.CTX_IfL e1 e2 => CTX_IfL ν (trns e1) (trns e2)
    | cast_calc.contexts.CTX_IfM e0 e2 => CTX_IfM ν (trns e0) (trns e2)
    | cast_calc.contexts.CTX_IfR e0 e1 => CTX_IfR ν (trns e0) (trns e1)
    | cast_calc.contexts.CTX_SeqL e2 => CTX_SeqL ν (trns e2)
    | cast_calc.contexts.CTX_SeqR e1 => CTX_SeqR ν (trns e1)
    | CTX_Cast ℓ τ1 τ2 => CTX_AppR ν (of_val $ cast' ℓ τ1 τ2)
        (* (CTX_AppR ν $ match consistency_decision τ1 τ2 with *)
        (*               | inl Pc => (of_val $ cast ℓ τ1 τ2 Pc) *)
        (*               | inr _ => Lit LitUnit *)
        (*               end) *)
    end.

  Definition trns_ctx (C : cast_calc.contexts.ctx) : ctx :=
    trns_ctx_item <$> C.

  Lemma trns_fill_ctx_item Ci e :
    ⟨ cast_calc.contexts.fill_ctx_item Ci e ⟩ = fill_ctx_item (trns_ctx_item Ci) ⟨ e ⟩.
  Proof. destruct Ci; eauto. Qed.
  Lemma trns_fill_ctx C e :
    ⟨ cast_calc.contexts.fill_ctx C e ⟩ = fill_ctx (trns_ctx C) ⟨ e ⟩.
  Proof. induction C; auto. by rewrite /= -IHC trns_fill_ctx_item. Qed.

  Lemma trns_ctx_app C C' : trns_ctx (C ++ C') = trns_ctx C ++ trns_ctx C'.
  Proof. by rewrite /trns_ctx fmap_app. Qed.

End contexts.
