From main.prelude Require Import imports.

Inductive base_lit : Set :=
  | LitUnit | LitBool (b : bool) | LitInt (n : Z).

Inductive bin_op : Set :=
| PlusOp | MinusOp | LeOp | LtOp | EqOp.

Inductive base :=
  | Unit
  | Bool
  | Int.

Inductive bin_const :=
  | Arrow
  | Sum
  | Product.

Instance base_eq : EqDecision base.
Proof. solve_decision. Qed.

Instance bin_const_eq : EqDecision bin_const.
Proof. solve_decision. Qed.

Inductive shape :=
  | S_Base (b : base)
  | S_Bin (bin : bin_const).

Definition base_lit_base (b : base_lit) : base :=
  match b with
  | LitUnit => Unit
  | LitBool b => Bool
  | LitInt n => Int
  end.

Instance shape_eq : EqDecision shape.
Proof. solve_decision. Qed.
