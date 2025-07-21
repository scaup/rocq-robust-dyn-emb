From main Require Import imports.
From stdpp Require Import listset.

Inductive label : Set := Lbl (ℓ : Z).

Class NeverOccurs (ℓ : label) : Type.

Definition LabelRel := relation label.

(* relations on LabelRel *)

Definition le_permissive : relation LabelRel :=
  fun L1 L2 => (∀ ℓ ℓ', L1 ℓ ℓ' → L2 ℓ ℓ') .
Instance le_permissive_inst : SqSubsetEq LabelRel :=
  le_permissive.
(* Allows for ⊑-notation *)

Definition equiv_LabelRel : relation LabelRel :=
  fun L L' => ∀ ℓ ℓ', L ℓ ℓ' <-> L' ℓ ℓ' .
Instance equiv_LabelRel_inst : Equiv LabelRel :=
  equiv_LabelRel.
(* Allows for ≡-notation *)

(* basic examples LabelRel *)
(* --------------------------- *)

Definition PermitNone : LabelRel :=
  fun _ _ => False.
Instance PermitNone_inst : Empty LabelRel :=
  PermitNone.
(* Allow for "∅" notation *)
Instance PermitNone_bot_inst : Bottom LabelRel :=
  PermitNone.
(* Allow for "⊥" notation *)

Definition PermitAll : LabelRel :=
  fun _ _ => True.
Instance PermitAll_top_inst : Top LabelRel :=
  PermitAll.
(* Allow fro "⊤" notation *)

Definition join_LabelRel (L1 L2 : LabelRel) : LabelRel :=
  fun ℓ ℓ' => L1 ℓ ℓ' ∨ L2 ℓ ℓ'.
Instance join_LabelRel_inst : Join LabelRel :=
  join_LabelRel.
(* Allows for ⊔-notation *)

Definition diagonal (L : label → Prop) : LabelRel :=
  fun ℓ ℓ' => ℓ = ℓ' ∧ L ℓ ∧ L ℓ'.

Definition combine_LabelRel (L L' : LabelRel) : LabelRel :=
  fun ℓ1 ℓ3 => ∃ ℓ2, L ℓ1 ℓ2 ∧ L' ℓ2 ℓ3.

Notation "L ⋅ L'" := (combine_LabelRel L L') (at level 10).

(* ⊑ froms preorder; todo *)
(* --------------------------- *)

Instance le_permissive_trans_inst : Transitive le_permissive.
Proof. intros R1 R2 R3 H12 H23 ℓ ℓ' Hℓℓ'. by apply H23, H12. Qed.
Lemma le_permissive_trans' Δ1 Δ2 Δ3 :
  le_permissive Δ2 Δ3 → le_permissive Δ1 Δ2 → le_permissive Δ1 Δ3.
Proof. intros. by eapply transitivity. Qed.

Instance le_permissive_refl_inst : Reflexive le_permissive.
Proof. intros L l l'; auto. Qed.

Lemma le_permissive_join_l (L1 L2 : LabelRel) : L1 ⊑ (L1 ⊔ L2).
Proof. intros ℓ ℓ' H. rewrite /join /join_LabelRel_inst. by left. Qed.

Lemma le_permissive_join_r (L1 L2 : LabelRel) : L2 ⊑ (L1 ⊔ L2).
Proof. intros ℓ ℓ' H. rewrite /join /join_LabelRel_inst. by right. Qed.

(* trivial lemmas *)
(* --------------------------- *)

Lemma diagonal_auto H ℓ : H ℓ → diagonal H ℓ ℓ.
Proof. intro. by split. Qed.

Lemma le_permissive_diagonal L L' (H : ∀ ℓ, L ℓ → L' ℓ) :
  le_permissive (diagonal L) (diagonal L').
Proof. rewrite /diagonal. intros ℓ ℓ' H'. naive_solver. Qed.

(* tactics *)
(* --------------------------- *)

Ltac delta_solver :=
  lazymatch goal with
  | HΔ : _ ⊑ ?Δ |- ?Δ _ _ =>
      (apply HΔ, diagonal_auto; set_solver)
      (* (apply HΔ, unary_conj_id; rewrite /elemhood; set_solver) *)
  | _ => fail "ads"
  end.

Ltac permissive_solver :=
  lazymatch goal with
  | HΔ : _ ⊑ ?Δ |- _ ⊑ ?Δ =>
      (apply (le_permissive_trans' _ _ _ HΔ), le_permissive_diagonal; intros k Hk; set_solver)
  | _ => fail "ads"
  end.

(* coercions *)
(* --------------------------- *)

Definition elemhood {A : Type} (ℓs : listset A) : A → Prop :=
  fun ℓ => ℓ ∈ ℓs.

Coercion elemhood : listset >-> Funclass.

(* instantiations *)
(* --------------------------- *)

Instance join_LabelPred_inst : Join (label → Prop) :=
  fun L L' => fun l => L l ∨ L' l.
