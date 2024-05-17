From main Require Import imports dyn_lang.definition.

Fixpoint labels_expr (e : expr) : listset label :=
    match e with
    | Lit b => ∅
    | Seq ℓ e1 e2 =>
        {[ ℓ ]} ∪ labels_expr e1 ∪ labels_expr e2
    | If ℓ e0 e1 e2 =>
        {[ ℓ ]} ∪ labels_expr e0 ∪ labels_expr e1 ∪ labels_expr e2
    | BinOp ℓ binop e1 e2 =>
        {[ ℓ ]} ∪ labels_expr e1 ∪ labels_expr e2
    | Var v => ∅
    | Lam e =>
        labels_expr e
    | App ℓ e1 e2 =>
        {[ ℓ ]} ∪ labels_expr e1 ∪ labels_expr e2
    | InjL e =>
        labels_expr e
    | InjR e =>
        labels_expr e
    | Case ℓ e0 e1 e2 =>
        {[ ℓ ]} ∪ labels_expr e0 ∪ labels_expr e1 ∪ labels_expr e2
    | Fst ℓ e =>
        {[ ℓ ]} ∪ labels_expr e
    | Snd ℓ e =>
        {[ ℓ ]} ∪ labels_expr e
    | Pair e1 e2 =>
        labels_expr e1 ∪ labels_expr e2
    | Error ℓ =>
        {[ ℓ ]}
    end.

Definition InDynExpr (e : expr) : LabelRel :=
  unary_conj (fun ℓ => ℓ ∈ (labels_expr e)).
