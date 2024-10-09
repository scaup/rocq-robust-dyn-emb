From main.prelude Require Import base_lang imports.

Inductive type :=
  | Base (B : base)
  | Bin (bin : bin_const) (τ1 τ2 : type)
  | Unknown.

Instance type_const_eq : EqDecision type.
Proof. solve_decision. Qed.

Definition of_shape (s : shape) : type :=
  match s with
  | S_Base b => Base b
  | S_Bin bin => Bin bin Unknown Unknown
  end.

Definition closed_ground (τ : type) : option shape :=
  match τ with
  | Base B => None
  | Bin bin Unknown Unknown => None
  | Unknown => None
  | Bin bin _ _ => Some (S_Bin bin)
  end.

Inductive consistency : type → type → Set :=
  | C_Arb_Unknown τ : consistency τ Unknown
  | C_Unknown_Arb τ : consistency Unknown τ
  | C_Base_Base B : consistency (Base B) (Base B)
  | C_Bin_Bin bin τ1 τ1' τ2 τ2'
        (H1 : consistency τ1 τ1') (H2 : consistency τ2 τ2') :
          consistency (Bin bin τ1 τ2) (Bin bin τ1' τ2').

Lemma consistency_sym τ τ' (H : consistency τ τ') :
        consistency τ' τ.
Proof. induction H; try by constructor. Qed.

Lemma consistency_decision τ τ' : sum (consistency τ τ') (consistency τ τ' → False).
Proof.
  generalize dependent τ'.
  induction τ.
  - destruct τ'.
    + destruct (decide (B = B0)) as [-> | neg].
       * left. constructor.
       * right; intro abs; by inversion abs.
    + right; intro abs; by inversion abs.
    + left. constructor.
  - destruct τ'.
    + right; intro abs; by inversion abs.
    + destruct (decide (bin = bin0)) as [-> | neg].
       * destruct (IHτ1 τ'1).
         -- destruct (IHτ2 τ'2).
            ++ left. by constructor.
            ++ right. intro abs; inversion abs. naive_solver.
         -- right. intro abs; inversion abs. naive_solver.
       * right; intro abs; by inversion abs.
    + left; constructor.
  - left. constructor.
Defined.

Definition to_ground (τ : type) : option shape :=
  match τ with
  | Base B => Some $ S_Base B
  | Bin bin τ1 τ2 => match decide (τ1 = Unknown), decide (τ2 = Unknown) with
                    | left _, left _ => Some (S_Bin bin)
                    | _, _ => None
                    end
  | Unknown => None
  end.

Definition base_lit_type (b : base_lit) : type :=
  Base (base_lit_base b).

From main.prelude Require Import autosubst.

Ltac closed_solver :=
  lazymatch goal with
  | H : Closed_n _ _ |- Closed_n _ _ => intros σ; specialize (H σ); simpl in H; by simplify_eq
  | |- Closed_n _ _ => fail "goal detected suc"
  | _ => fail "wrong goal"
  end.
