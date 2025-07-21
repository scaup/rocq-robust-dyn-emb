From main.prelude Require Import imports autosubst.
From main.prelude Require Export labels base_lang.

Inductive expr :=
  (* base values *)
  | Lit (b : base_lit)
  | Seq (ℓ : label) (e1 e2 : expr)
  | If (ℓ : label) (e0 e1 e2 : expr)
  | BinOp (ℓ : label) (binop : bin_op) (e1 e2 : expr)
  (* functions *)
  | Var (v : var)
  | Lam (e : {bind 1 of expr})
  | App (ℓ : label) (e1 e2 : expr)
  (* sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (ℓ : label) (e0 : expr) (e1 e2 : {bind 1 of expr})
  (* pairs *)
  | Fst (ℓ : label) (e : expr)
  | Snd (ℓ : label) (e : expr)
  | Pair (e1 e2 : expr)
  (* error *)
  | Error (ℓ : label).

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Inductive val : Type :=
  | LitV (b : base_lit)
  | LamV (e : {bind 1 of expr})
  | InjLV (v : val)
  | InjRV (v : val)
  | PairV (v1 v2 : val).

Fixpoint of_val (v : val) : expr :=
 match v with
 | LamV e => Lam e
 | LitV v => Lit v
 | PairV v1 v2 => Pair (of_val v1) (of_val v2)
 | InjLV v => InjL (of_val v)
 | InjRV v => InjR (of_val v)
 end.

Fixpoint to_val (e : expr) : option val :=
 match e with
 | Lam e => Some (LamV e)
 | Lit e => Some (LitV e)
 | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
 | InjL e => InjLV <$> to_val e
 | InjR e => InjRV <$> to_val e
 | _ => None
 end.

Fixpoint val_subst (v : val) (σ : var → expr) : val :=
  match v with
  | LamV e => LamV (e.[up σ])
  | LitV v => LitV v
  | PairV v1 v2 => PairV (val_subst v1 σ) (val_subst v2 σ)
  | InjLV v => InjLV (val_subst v σ)
  | InjRV v => InjRV (val_subst v σ)
  end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
 by induction v; try simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.
Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
 revert v; induction e; intros ? ?; simplify_option_eq; auto with f_equal.
Qed.

(** Equality and other typeclass stuff *)
Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Instance label_eq_dec : EqDecision label.
Proof. solve_decision. Defined.
Instance expr_eq_dec : EqDecision expr.
Proof. solve_decision. Defined.
Instance val_eq_dec : EqDecision val.
Proof.
 refine (λ v v', cast_if (decide (of_val v = of_val v')));
   abstract naive_solver.
Defined.

Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).

(** The head stepping relation *)

Definition bin_op_eval (op : bin_op) (z1 z2 : Z) : val :=
 match op with
 | PlusOp => LitV $ LitInt (z1 + z2)%Z
 | MinusOp => LitV $ LitInt (z1 - z2)
 | LeOp => LitV $ LitBool $ bool_decide (z1 ≤ z2)%Z
 | LtOp => LitV $ LitBool $ bool_decide (z1 < z2)%Z
 | EqOp => LitV $ LitBool $ bool_decide (z1 = z2)
 end.

(* "head step not error" *)
Inductive head_step_ne : expr → expr → Prop :=
  (* base values destructors *)
  | HNE_Seq ℓ e :
    head_step_ne (Seq ℓ (Lit LitUnit) e) e
  | HNE_If ℓ b e1 e2 :
    head_step_ne (If ℓ (Lit $ LitBool $ b) e1 e2) (match b with
                                              | true => e1
                                              | false => e2
                                              end)
  | HNE_BinOp (ℓ : label) (op : bin_op) z1 z2 :
    head_step_ne (BinOp ℓ op (Lit $ LitInt z1) (Lit $ LitInt z2))
                        (of_val $ bin_op_eval op z1 z2)
  (* sums values destructors *)
  | HNE_Case_L ℓ e0 v0 e1 e2 :
    to_val e0 = Some v0 →
    head_step_ne (Case ℓ (InjL e0) e1 e2) (e1.[of_val v0/])
  | HNE_Case_R ℓ e0 v0 e1 e2 :
    to_val e0 = Some v0 →
    head_step_ne (Case ℓ (InjR e0) e1 e2) (e2.[of_val v0/])
  (* pair values destructors *)
  | HNE_Fst ℓ e1 v1 e2 v2 :
    to_val e1 = Some v1 →
    to_val e2 = Some v2 →
    head_step_ne (Fst ℓ (Pair e1 e2)) e1
  | HNE_Snd ℓ e1 v1 e2 v2 :
    to_val e1 = Some v1 →
    to_val e2 = Some v2 →
    head_step_ne (Snd ℓ (Pair e1 e2)) e2
  (* lambda destructors *)
  | HNE_App ℓ eb ea va :
    to_val ea = Some va →
    head_step_ne (App ℓ (Lam eb) ea) (eb.[ea/]).

Definition shape_val (v : val) : shape :=
 match v with
 | LitV b => match b with
            | LitUnit => S_Base Unit
            | LitBool b => S_Base Bool
            | LitInt n => S_Base Int
            end
 | LamV e => S_Bin Arrow
 | InjLV v => S_Bin Sum
 | InjRV v => S_Bin Sum
 | PairV v1 v2 => S_Bin Product
 end.

Inductive head_faulty : expr → label → Prop :=
  | HE_Seq ℓ e1 v1 e2 :
    to_val e1 = Some v1 →
    shape_val v1 ≠ S_Base Unit →
    head_faulty (Seq ℓ e1 e2) ℓ
  | HE_If ℓ e0 v0 e1 e2 :
    to_val e0 = Some v0 →
    shape_val v0 ≠ S_Base Bool →
    head_faulty (If ℓ e0 e1 e2) ℓ
  | HE_BinOp_L ℓ (binop : bin_op) e1 e2 v1 v2 :
    to_val e1 = Some v1 →
    to_val e2 = Some v2 →
    shape_val v1 ≠ S_Base Int →
    head_faulty (BinOp ℓ binop e1 e2) ℓ
  | HE_BinOp_R ℓ (binop : bin_op) e1 e2 v1 v2 :
    to_val e1 = Some v1 →
    to_val e2 = Some v2 →
    shape_val v2 ≠ S_Base Int →
    head_faulty (BinOp ℓ binop e1 e2) ℓ
  | HE_Case ℓ e0 v0 e1 e2 :
    to_val e0 = Some v0 →
    shape_val v0 ≠ S_Bin Sum →
    head_faulty (Case ℓ e0 e1 e2) ℓ
  | HE_Fst ℓ e v :
    to_val e = Some v →
    shape_val v ≠ S_Bin Product →
    head_faulty (Fst ℓ e) ℓ
  | HE_Snd ℓ e v :
    to_val e = Some v →
    shape_val v ≠ S_Bin Product →
    head_faulty (Snd ℓ e) ℓ
  (* lambda destructors *)
  | HE_App ℓ e1 v1 e2 v2 :
    to_val e1 = Some v1 →
    shape_val v1 ≠ S_Bin Arrow →
    to_val e2 = Some v2 →
    head_faulty (App ℓ e1 e2) ℓ.

Inductive head_step : expr → expr → Prop :=
  | H_error e ℓ (H : head_faulty e ℓ) : head_step e (Error ℓ)
  | H_not_error e e' (H : head_step_ne e e') : head_step e e'.

(** Evaluation contexts *)
Inductive ectx_item :=
| AppLCtx (ℓ : label) (e2 : expr)
| AppRCtx (ℓ : label) (v1 : val)
| PairLCtx (e2 : expr)
| PairRCtx (v1 : val)
| FstCtx (ℓ : label)
| SndCtx (ℓ : label)
| InjLCtx
| InjRCtx
| CaseCtx (ℓ : label) (e1 : {bind expr}) (e2 : {bind expr})
| IfCtx (ℓ : label) (e2 : expr) (e3 : expr)
| BinOpLCtx (ℓ : label) (op : bin_op) (e2 : expr)
| BinOpRCtx (ℓ : label) (op : bin_op) (v1 : val)
| SeqCtx (ℓ : label) (e2 : expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
 match Ki with
 | AppLCtx ℓ e2 => App ℓ e e2
 | AppRCtx ℓ v1 => App ℓ (of_val v1) e
 | PairLCtx e2 => Pair e e2
 | PairRCtx v1 => Pair (of_val v1) e
 | FstCtx ℓ => Fst ℓ e
 | SndCtx ℓ => Snd ℓ e
 | InjLCtx => InjL e
 | InjRCtx => InjR e
 | CaseCtx ℓ e1 e2 => Case ℓ e e1 e2
 | IfCtx ℓ e1 e2 => If ℓ e e1 e2
 | BinOpLCtx ℓ op e2 => BinOp ℓ op e e2
 | BinOpRCtx ℓ op v1 => BinOp ℓ op (of_val v1) e
 | SeqCtx ℓ e2 => Seq ℓ e e2
 end.

Notation ectx := (list ectx_item).

Definition fill (K : ectx) (e : expr) : expr :=
 foldr fill_item e K.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Inductive step_ne : expr → expr → Prop :=
  | SNE_Normal (K : ectx) e_h e_h' (HS : head_step_ne e_h e_h') :
    step_ne (fill K e_h) (fill K e_h').

Inductive step : expr → expr → Prop :=
  | S_Normal (K : ectx) e_h e_h' (HS : head_step e_h e_h') :
    step (fill K e_h) (fill K e_h')
  | S_Error (K : ectx) (H : K ≠ []) ℓ :
    step (fill K (Error ℓ)) (Error ℓ).

Definition faulty (e : expr) (ℓ : label) : Prop :=
  ∃ K e', e = fill K e' ∧ (head_faulty e' ℓ ∨ e' = Error ℓ).

Definition diverging (e : expr) : Prop :=
  ∀ n, ∃ e', nsteps step n e e'.

Definition terminating (e : expr) v : Prop :=
  rtc step e (of_val v).

Definition erroring (e : expr) ℓ : Prop :=
  rtc step e (Error ℓ).
