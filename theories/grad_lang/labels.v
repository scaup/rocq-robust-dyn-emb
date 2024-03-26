From main Require Import imports grad_lang.definition prelude.labels.

Fixpoint getLabels (e : expr) : listset label :=
  match e with
  | Lit b => ∅
  | Seq e1 e2 =>
        getLabels e1 ∪ getLabels e2
  | If e0 e1 e2 =>
        getLabels e0 ∪ getLabels e1 ∪ getLabels e2
  | BinOp binop e1 e2 =>
        getLabels e1 ∪ getLabels e2
  | Var v => ∅
  | Lam e =>
        getLabels e
  | App e1 e2 =>
        getLabels e1 ∪ getLabels e2
  | InjL e =>
        getLabels e
  | InjR e =>
        getLabels e
  | Case e0 e1 e2 =>
        getLabels e0 ∪ getLabels e1 ∪ getLabels e2
  | Fst e =>
        getLabels e
  | Snd e =>
        getLabels e
  | Pair e1 e2 =>
        getLabels e1 ∪ getLabels e2
  | Error ℓ =>
        {[ ℓ ]}
  | Ascribe ℓ τ1 τ2 e =>
        {[ ℓ ]} ∪ getLabels e
  end.

Definition occursIn (e : expr) : label → Prop := fun ℓ => ℓ ∈ getLabels e.

Definition AscriptLbls (e : expr) : LabelRel :=
  unary_conj (occursIn e).

(* Notation "Δ e" := (Diagonal e) (at level 0). *)
