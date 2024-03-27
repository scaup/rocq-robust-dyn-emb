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

Definition PermitAll : LabelRel := fun _ _ => False.
(* Notation "#" := (PermitAll). *)

Definition disj (L1 L2 : LabelRel) : LabelRel :=
  fun ℓ ℓ' => L1 ℓ ℓ' ∨ L2 ℓ ℓ'.

Definition unary_conj (L : label → Prop) : LabelRel :=
  fun ℓ ℓ' => L ℓ ∧ L ℓ'.

Lemma le_perm_unary_conj L L' (H : ∀ ℓ, L ℓ → L' ℓ) :
  le_permissive (unary_conj L) (unary_conj L').
Proof. intros ℓ ℓ' H'. destruct H'. split; by eapply H. Qed.

Definition elemhood (ℓs : listset label) : label → Prop :=
  fun ℓ => ℓ ∈ ℓs.

(* Lemma disj_union (ℓs ℓs' : listset label) : *)
(*   equiv_LabelRel (disj (unary_conj (fun ℓ => ℓ ∈ ℓs)) (unary_conj (fun ℓ => ℓ ∈ ℓs'))) *)
(*     (unary_conj (fun ℓ => ℓ ∈ ℓs ∪ ℓs')). *)
(* Proof. *)
(*   intros ℓ ℓ'. split; intro H. eauto. *)
