From main Require Import imports cast_calc.definition prelude.labels cast_calc.contexts.

Fixpoint labels_expr (e : expr) : listset label :=
  match e with
  | Lit b => ∅
  | Seq e1 e2 =>
        labels_expr e1 ∪ labels_expr e2
  | If e0 e1 e2 =>
        labels_expr e0 ∪ labels_expr e1 ∪ labels_expr e2
  | BinOp binop e1 e2 =>
        labels_expr e1 ∪ labels_expr e2
  | Var v => ∅
  | Lam e =>
        labels_expr e
  | App e1 e2 =>
        labels_expr e1 ∪ labels_expr e2
  | InjL e =>
        labels_expr e
  | InjR e =>
        labels_expr e
  | Case e0 e1 e2 =>
        labels_expr e0 ∪ labels_expr e1 ∪ labels_expr e2
  | Fst e =>
        labels_expr e
  | Snd e =>
        labels_expr e
  | Pair e1 e2 =>
        labels_expr e1 ∪ labels_expr e2
  | Error ℓ =>
        {[ ℓ ]}
  | Cast ℓ τ1 τ2 e =>
        {[ ℓ ]} ∪ labels_expr e
  end.

Definition labels_ctx_item (Ci : ctx_item) : listset label :=
  match Ci with
  | CTX_Lam => ∅
  | CTX_AppL e2 => labels_expr e2
  | CTX_AppR e1 => labels_expr e1
  | CTX_PairL e2 => labels_expr e2
  | CTX_PairR e1 => labels_expr e1
  | CTX_Fst => ∅
  | CTX_Snd => ∅
  | CTX_InjL => ∅
  | CTX_InjR => ∅
  | CTX_CaseL e1 e2 => labels_expr e1 ∪ labels_expr e2
  | CTX_CaseM e0 e2 => labels_expr e0 ∪ labels_expr e2
  | CTX_CaseR e0 e1 => labels_expr e0 ∪ labels_expr e1
  | CTX_BinOpL op e2 => labels_expr e2
  | CTX_BinOpR op e1 => labels_expr e1
  | CTX_IfL e1 e2 => labels_expr e1 ∪ labels_expr e2
  | CTX_IfM e0 e2 => labels_expr e0 ∪ labels_expr e2
  | CTX_IfR e0 e1 => labels_expr e0 ∪ labels_expr e1
  | CTX_SeqL e2 => labels_expr e2
  | CTX_SeqR e1 => labels_expr e1
  | CTX_Cast ℓ τ1 τ2 => {[ ℓ ]}
  end.

Definition labels_ctx (C : ctx) : listset label :=
  foldr (fun Ci ℓs => labels_ctx_item Ci ∪ ℓs) ∅ C.

Lemma labels_ctx_app C C' :
  labels_ctx (C ++ C') ≡ labels_ctx C ∪ labels_ctx C'.
Proof. induction C. rewrite app_nil_l. set_solver. simpl. set_solver. Qed.

Definition InCastCalcExpr (e : expr) : LabelRel :=
  diagonal (labels_expr e).

Definition InCastCalcCtx_item (Ci : ctx_item) : LabelRel :=
  diagonal (labels_ctx_item Ci).

Definition InCastCalcCtx (C : ctx) : LabelRel :=
  diagonal (labels_ctx C).
