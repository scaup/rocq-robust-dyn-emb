From main.prelude Require Import imports autosubst base_lang labels.
From main.grad_lang Require Import definition types.

Inductive ctx_item :=
  | CTX_Lam
  | CTX_AppL (e2 : expr)
  | CTX_AppR (e1 : expr)
  | CTX_PairL (e2 : expr)
  | CTX_PairR (e1 : expr)
  | CTX_Fst
  | CTX_Snd
  | CTX_InjL
  | CTX_InjR
  | CTX_CaseL (e1 : expr) (e2 : expr)
  | CTX_CaseM (e0 : expr) (e2 : expr)
  | CTX_CaseR (e0 : expr) (e1 : expr)
  | CTX_BinOpL (op : bin_op) (e2 : expr)
  | CTX_BinOpR (op : bin_op) (e1 : expr)
  | CTX_IfL (e1 : expr) (e2 : expr)
  | CTX_IfM (e0 : expr) (e2 : expr)
  | CTX_IfR (e0 : expr) (e1 : expr)
  | CTX_SeqL (e2 : expr)
  | CTX_SeqR (e1 : expr)
  | CTX_Cast (ℓ : label) (τ1 τ2 : type).

Definition fill_ctx_item (ctx : ctx_item) (e : expr) : expr :=
  match ctx with
  | CTX_Lam => Lam e
  | CTX_AppL e2 => App e e2
  | CTX_AppR e1 => App e1 e
  | CTX_PairL e2 => Pair e e2
  | CTX_PairR e1 => Pair e1 e
  | CTX_Fst => Fst e
  | CTX_Snd => Snd e
  | CTX_InjL => InjL e
  | CTX_InjR => InjR e
  | CTX_CaseL e1 e2 => Case e e1 e2
  | CTX_CaseM e0 e2 => Case e0 e e2
  | CTX_CaseR e0 e1 => Case e0 e1 e
  | CTX_BinOpL op e2 => BinOp op e e2
  | CTX_BinOpR op e1 => BinOp op e1 e
  | CTX_IfL e1 e2 => If e e1 e2
  | CTX_IfM e0 e2 => If e0 e e2
  | CTX_IfR e0 e1 => If e0 e1 e
  | CTX_SeqL e2 => Seq e e2
  | CTX_SeqR e1 => Seq e1 e
  | CTX_Cast ℓ τ1 τ2 => Cast ℓ τ1 τ2 e
  end.

Notation ctx := (list ctx_item).

Definition fill_ctx (C : ctx) (e : expr) : expr :=
 foldr fill_ctx_item e C.
