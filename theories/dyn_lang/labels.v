From main Require Import imports dyn_lang.definition.

Definition LabelRel := relation label.

Definition le_permissive : relation LabelRel :=
  fun L1 L2 => (∀ ℓ ℓ', L1 ℓ ℓ' → L2 ℓ ℓ') .

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

Definition unary_conj (L : label → Prop) : LabelRel :=
  fun ℓ ℓ' => L ℓ ∧ L ℓ'.

Lemma le_perm_unary_conj L L' (H : ∀ ℓ, L ℓ → L' ℓ) :
  le_permissive (unary_conj L) (unary_conj L').
Proof. intros ℓ ℓ' H'. destruct H'. split; by eapply H. Qed.

Fixpoint getLabels (e : expr) : listset label :=
    match e with
    | Lit b => ∅
    | Seq ℓ e1 e2 =>
        {[ ℓ ]} ∪ getLabels e1 ∪ getLabels e2
    | If ℓ e0 e1 e2 =>
        {[ ℓ ]} ∪ getLabels e0 ∪ getLabels e1 ∪ getLabels e2
    | BinOp ℓ binop e1 e2 =>
        {[ ℓ ]} ∪ getLabels e1 ∪ getLabels e2
    | Var v => ∅
    | Lam e =>
        getLabels e
    | App ℓ e1 e2 =>
        {[ ℓ ]} ∪ getLabels e1 ∪ getLabels e2
    | InjL e =>
        getLabels e
    | InjR e =>
        getLabels e
    | Case ℓ e0 e1 e2 =>
        {[ ℓ ]} ∪ getLabels e0 ∪ getLabels e1 ∪ getLabels e2
    | Fst ℓ e =>
        {[ ℓ ]} ∪ getLabels e
    | Snd ℓ e =>
        {[ ℓ ]} ∪ getLabels e
    | Pair e1 e2 =>
        getLabels e1 ∪ getLabels e2
    | Error ℓ =>
        {[ ℓ ]}
    end.

Definition occursIn (e : expr) : label → Prop := fun ℓ => ℓ ∈ getLabels e.

Definition Lbls (e : expr) : LabelRel :=
  unary_conj (occursIn e).

(* Notation "Δ e" := (Diagonal e) (at level 0). *)
