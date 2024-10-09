From main.prelude Require Import imports base_lang.
From main.cast_calc Require Import types.

Definition LamN_type (Γ : list type) τ : type :=
  foldl (fun T t => Bin Arrow t T) τ Γ.

Definition LamN_type_snoc (Γ : list type) τ' τ :
  LamN_type (Γ ++ [τ']) τ = (Bin Arrow τ' (LamN_type Γ τ)).
Proof. by rewrite /LamN_type foldl_snoc. Qed.
