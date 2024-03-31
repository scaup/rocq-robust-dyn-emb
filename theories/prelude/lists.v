From main Require Import prelude.imports.
From stdpp Require Import list.

Lemma Forall2_rev_ind {A B : Type} : ∀ (R : A → B → Prop) ( P : list A → list B → Prop ),
  P [] []
  → (∀ (x : A) (y : B) (l : list A) (l' : list B), R x y → Forall2 R l l' → P l l' → P (l ++ [x]) (l' ++ [y]))
    → ∀ (l : list A) (l' : list B), Forall2 R l l' → P l l'.
Proof.
  intros R P HP0 HPS l.
  induction l using rev_ind.
  - intros l' HF.
    assert (abs := Forall2_length _ _ _ HF). destruct l'; inversion abs. auto.
  - intros l' HF.
    destruct l' as [|x' l'] using rev_ind.
    assert (abs := Forall2_length _ _ _ HF). rewrite app_length /= in abs. lia.
    assert (H := Forall2_length _ _ _ HF). repeat rewrite app_length /= Nat.add_comm /= in H. inversion H.
    edestruct (Forall2_app_inv _ l [x] l' [x'] H1 HF) as [a b].
    apply HPS; auto. by inversion b; simplify_eq.
Qed.

Lemma Forall2_rev_ind' {A B : Type} {l : list A} {l' : list B} {R : A → B → Prop} :
  Forall2 R l l' → ∀ ( P : list A → list B → Prop ),
    P [] []
    → (∀ (x : A) (y : B) (l : list A) (l' : list B), R x y → Forall2 R l l' → P l l' → P (l ++ [x]) (l' ++ [y]))
      → P l l'.
Proof. intros. eapply Forall2_rev_ind; eauto. Qed.
