From main.prelude Require Import base_lang imports.
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
 | Ascribe_typed ℓ τ1 τ2 e :
    Γ ⊢ e : τ1 → Γ ⊢ Ascribe ℓ τ1 τ2 e : τ2

where "Γ ⊢ e : τ" := (typed Γ e τ).
