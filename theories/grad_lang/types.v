From main.prelude Require Import base_lang imports.

Inductive type :=
  | Base (B : base)
  | Bin (bin : bin_const) (τ1 τ2 : type)
  | Unknown.

Instance type_const_eq : EqDecision type.
Proof. solve_decision. Qed.

Inductive consistency : type → type → Set :=
  | C_Arb_Unknown τ : consistency τ Unknown
  | C_Unknown_Arb τ : consistency Unknown τ
  | C_Base_Base B : consistency (Base B) (Base B)
  | C_Bin_Bin bin τ1 τ1' τ2 τ2'
        (H1 : consistency τ1 τ1') (H2 : consistency τ2 τ2') :
          consistency (Bin bin τ1 τ2) (Bin bin τ1' τ2').

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

(* On their own *)

(* B => B *)
(* ? => ? *)
(* G => ? *)
(* ? => G *)

(* By mutual induction on type *)

(* τ => ? (τ ≠ G, τ ≠ ?) *)
(* ? => τ (τ ≠ G, τ ≠ ?) *)

(* τ1 → τ2 => τ1' → τ2' *)




(* Inductive cast_structure : type → type → Set := *)
(*   | C_U_U : cast_structure Unknown Unknown *)
(*   | C_G_U G (s : shape) (H : to_ground G = Some s) : cast_structure G Unknown *)
(*   | C_U_G G (s : shape) (H : to_ground G = Some s) : cast_structure Unknown G *)
(*   | C_G_G G (s : shape) (H : to_ground G = Some s) : cast_structure G G *)

(*   | C_Bin τ1 τ1' τ2 bin G (s : shape) (H : to_ground G = Some s) : cast_structure G G *)

(* Instance type_eq : EqDecision type. *)
(* Proof. *)
(*   intros τ. induction τ; intros τ'. *)
(*   destruct τ'; solve_decision. *)



(* Inductive type := *)
(*   | Unit *)
(*   | Bool *)
(*   | Int *)
(*   | Arrow (τ1 τ2 : type) *)
(*   | Sum (τ1 τ2 : type) *)
(*   | Product (τ1 τ2 : type) *)
(*   | Unknown *)
(* . *)

(* Instance type_eq : EqDecision type. *)
(* Proof. solve_decision. Qed. *)

(* Inductive base := *)
(*   | B_Unit *)
(*   | B_Bool *)
(*   | B_Int. *)

(* Definition base_type (B : base) : type := *)
(*   match B with *)
(*   | B_Unit => Unit *)
(*   | B_Bool => Bool *)
(*   | B_Int => Int *)
(*   end. *)

(* Inductive bin_const := *)
(*   | BC_Arrow *)
(*   | BC_Sum *)
(*   | BC_Product. *)

(* Definition bin_type (bin : bin_const) τ1 τ2 : type := *)
(*   match bin with *)
(*   | BC_Arrow => Arrow τ1 τ2 *)
(*   | BC_Sum => Sum τ1 τ2 *)
(*   | BC_Product => Product τ1 τ2 *)
(*   end. *)

(* Inductive consistency : type → type → Set := *)
(*   | C_Arb_Unknown τ : consistency τ Unknown *)
(*   | C_Unknown_Arb τ : consistency Unknown τ *)
(*   | C_Base_Base B : consistency (base_type B) (base_type B) *)
(*   | C_Bin_Bin bin τ1 τ1' τ2 τ2' (H1 : consistency τ1 τ1') (H2 : consistency τ2 τ2') : *)
(*           consistency (bin_type bin τ1 τ2) (bin_type bin τ1' τ2'). *)



(* (* Inductive base := *) *)
(* (*   | Unit *) *)
(* (*   | Bool *) *)
(* (*   | Int. *) *)

(* (* Inductive bin_const := *) *)
(* (*   | Arrow *) *)
(* (*   | Sum *) *)
(* (*   | Product. *) *)

(* (* Inductive type := *) *)
(* (*   | Base (B : base) *) *)
(* (*   | Bin (bin : bin_const) (τ1 τ2 : type) *) *)
(* (*   | Unknown. *) *)

(* (* Inductive consistency : relation type := *) *)
(* (*   | C_Arb_Unknown τ : consistency τ Unknown *) *)
(* (*   | C_Unknown_Arb τ : consistency Unknown τ *) *)
(* (*   | C_Base_Base B : consistency (Base B) (Base B) *) *)
(* (*   | C_Bin_Bin bin τ1 τ1' τ2 τ2' *) *)
(* (*         (H1 : consistency τ1 τ1') (H2 : consistency τ2 τ2') : *) *)
(* (*           consistency (Bin bin τ1 τ2) (Bin bin τ1' τ2'). *) *)

(* (* Instance type_eq : EqDecision type. *) *)
(* (* Proof. *) *)
(* (*   intros τ. induction τ; intros τ'. *) *)
(* (*   destruct τ'; solve_decision. *) *)
