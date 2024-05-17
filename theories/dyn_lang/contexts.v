From main.prelude Require Import imports autosubst.
From main.dyn_lang Require Import definition.

Inductive ctx_item :=
  | CTX_Lam
  | CTX_AppL (ℓ : label) (e2 : expr)
  | CTX_AppR (ℓ : label) (e1 : expr)
  | CTX_PairL (e2 : expr)
  | CTX_PairR (e1 : expr)
  | CTX_Fst (ℓ : label)
  | CTX_Snd (ℓ : label)
  | CTX_InjL
  | CTX_InjR
  | CTX_CaseL (ℓ : label) (e1 : expr) (e2 : expr)
  | CTX_CaseM (ℓ : label) (e0 : expr) (e2 : expr)
  | CTX_CaseR (ℓ : label) (e0 : expr) (e1 : expr)
  | CTX_BinOpL (ℓ : label) (op : bin_op) (e2 : expr)
  | CTX_BinOpR (ℓ : label) (op : bin_op) (e1 : expr)
  | CTX_IfL (ℓ : label) (e1 : expr) (e2 : expr)
  | CTX_IfM (ℓ : label) (e0 : expr) (e2 : expr)
  | CTX_IfR (ℓ : label) (e0 : expr) (e1 : expr)
  | CTX_SeqL (ℓ : label) (e2 : expr)
  | CTX_SeqR (ℓ : label) (e1 : expr).

Definition fill_ctx_item (ctx : ctx_item) (e : expr) : expr :=
  match ctx with
  | CTX_Lam => Lam e
  | CTX_AppL ℓ e2 => App ℓ e e2
  | CTX_AppR ℓ e1 => App ℓ e1 e
  | CTX_PairL e2 => Pair e e2
  | CTX_PairR e1 => Pair e1 e
  | CTX_Fst ℓ => Fst ℓ e
  | CTX_Snd ℓ => Snd ℓ e
  | CTX_InjL => InjL e
  | CTX_InjR => InjR e
  | CTX_CaseL ℓ e1 e2 => Case ℓ e e1 e2
  | CTX_CaseM ℓ e0 e2 => Case ℓ e0 e e2
  | CTX_CaseR ℓ e0 e1 => Case ℓ e0 e1 e
  | CTX_BinOpL ℓ op e2 => BinOp ℓ op e e2
  | CTX_BinOpR ℓ op e1 => BinOp ℓ op e1 e
  | CTX_IfL ℓ e1 e2 => If ℓ e e1 e2
  | CTX_IfM ℓ e0 e2 => If ℓ e0 e e2
  | CTX_IfR ℓ e0 e1 => If ℓ e0 e1 e
  | CTX_SeqL ℓ e2 => Seq ℓ e e2
  | CTX_SeqR ℓ e1 => Seq ℓ e1 e
  end.

Notation ctx := (list ctx_item).

Definition fill_ctx (C : ctx) (e : expr) : expr :=
 foldr fill_ctx_item e C.

Lemma fill_ctx_app e K K' : fill_ctx K' (fill_ctx K e) = fill_ctx (K' ++ K) e.
Proof. revert K. induction K' => K; simpl; auto. by rewrite IHK'. Qed.
