From main Require Import imports.
From stdpp Require Import listset.

Inductive label : Set := Lbl (ℓ : Z).

Class NeverOccurs (ℓ : label) : Type.

Definition LabelRel := relation label.

Definition le_permissive : relation LabelRel :=
  fun L1 L2 => (∀ ℓ ℓ', L1 ℓ ℓ' → L2 ℓ ℓ') .

Definition equiv_LabelRel (L L' : LabelRel) :=
  ∀ ℓ ℓ', L ℓ ℓ' <-> L' ℓ ℓ' .

Notation "L1 ≤ L2" := (le_permissive L1 L2).

Instance le_permissive_trans : Transitive le_permissive.
Proof. intros R1 R2 R3 H12 H23 ℓ ℓ' Hℓℓ'. by apply H23, H12. Qed.

Lemma le_permissive_trans' Δ1 Δ2 Δ3 :
  le_permissive Δ2 Δ3 → le_permissive Δ1 Δ2 → le_permissive Δ1 Δ3.
Proof. intros. by eapply transitivity. Qed.

Definition PermitNone : LabelRel := fun _ _ => False.
(* Notation "∅" := (PermitNone). *)

Instance empty_labelrel : Empty LabelRel := PermitNone.

Definition PermitAll : LabelRel := fun _ _ => True.
(* Notation "#" := (PermitAll). *)

Definition disj (L1 L2 : LabelRel) : LabelRel :=
  fun ℓ ℓ' => L1 ℓ ℓ' ∨ L2 ℓ ℓ'.

Notation "L ⋎ L'" := (disj L L') (at level 5).

Definition unary_conj (L : label → Prop) : LabelRel :=
  fun ℓ ℓ' => ℓ = ℓ' ∧ L ℓ ∧ L ℓ'.

Notation diag := unary_conj.

Lemma le_perm_unary_conj L L' (H : ∀ ℓ, L ℓ → L' ℓ) :
  le_permissive (unary_conj L) (unary_conj L').
Proof. rewrite /diag. intros ℓ ℓ' H'. naive_solver. Qed.

Definition elemhood (ℓs : listset label) : label → Prop :=
  fun ℓ => ℓ ∈ ℓs.

Lemma le_permissive_same L : le_permissive L L.
Proof. intros x x'; naive_solver. Qed.


(* Lemma disj_union (ℓs ℓs' : listset label) : *)
(*   equiv_LabelRel (disj (unary_conj (fun ℓ => ℓ ∈ ℓs)) (unary_conj (fun ℓ => ℓ ∈ ℓs'))) *)
(*     (unary_conj (fun ℓ => ℓ ∈ ℓs ∪ ℓs')). *)
(* Proof. *)
(*   intros ℓ ℓ'. split; intro H. eauto. *)


Instance le_permissive_sqsubseteq : SqSubsetEq LabelRel :=
  le_permissive.
Instance le_permissive_equiv : Equiv LabelRel :=
  equiv_LabelRel.
Instance le_permissive_join : Join LabelRel :=
  disj.
(* Instance le_permissive_meet : Meet LabelRel := *)
(*   disj. *)

Instance le_permissive_top : Top LabelRel :=
  PermitAll.

Instance le_permissive_bot : Bottom LabelRel :=
  PermitNone.

Definition comb_trans_lblrel (L L' : LabelRel) : LabelRel :=
  fun ℓ1 ℓ3 => ∃ ℓ2, L ℓ1 ℓ2 ∧ L' ℓ2 ℓ3.

Notation "L ∘ L'" := (comb_trans_lblrel L L').

Lemma le_meet_l (L1 L2 : LabelRel) : L1 ⊑ (L1 ⊔ L2).
Proof. intros ℓ ℓ' H. rewrite /join /le_permissive_join. by left. Qed.

Lemma le_meet_r (L1 L2 : LabelRel) : L2 ⊑ (L1 ⊔ L2).
Proof. intros ℓ ℓ' H. rewrite /join /le_permissive_join. by right. Qed.
