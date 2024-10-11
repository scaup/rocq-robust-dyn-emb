From main.prelude Require Import imports labels autosubst.
(* From main.cast_calc Require Import types. *)
From main.dyn_lang Require Import definition lemmas labels.
From main.logrel Require Import definition lib.rfn lib.weakestpre.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

Definition RefineL (L : LabelRel) (e e' : expr) : Prop :=
  ((∃ v, rtc step e (of_val v)) → (∃ v', rtc step e' (of_val v'))) ∧
  (∀ ℓ, rtc step e (Error ℓ) → ∃ ℓ', True ∧ rtc step e' (Error ℓ')).

Lemma logrel_adequacy L e e' τ
  (H : open_exprel_typed [] L e e' τ) :
    RefineL L e e'.
Proof.
  rewrite /open_exprel_typed /exprel_typed /rfn in H.
  specialize (H L (le_permissive_refl_inst L) [] []). asimpl in H.
  rewrite /val_lift_r /lbl_lift_r in H.
  assert (H' : ⊢ wp (fun v => ⌜∃ v', rtc step_ne e' (of_val v')⌝)
                    (fun ℓ => ⌜∃ t' ℓ', rtc step_ne e' t' ∧ faulty t' ℓ' ∧ True ⌝) e).
  { iApply wp_impl. iApply H; auto. auto. iIntros (v) "H".
    iDestruct "H" as (v') "[%H' _]". eauto. } clear H.
  assert (H := wp_adequacy _ _ _ H'). clear H'.
  split.
  - destruct H as [H _]. intros Hev. destruct Hev as [v Hev].
    rewrite rtc_step_step_ne_to_val in Hev.
    destruct (H _ Hev) as [v' G].
    rewrite -rtc_step_step_ne_to_val in G. eauto.
  - destruct H as [_ H]. intros ℓ Heℓ.
    destruct (iffLR (rtc_step_step_ne_to_error _ _) Heℓ) as (t' & Htℓ & et'). clear Heℓ.
    specialize (H t' ℓ Htℓ et'). destruct H as (t'' & ℓ' & He't'' & Hf & HL).
    exists ℓ'. split; auto. apply rtc_step_step_ne_to_error. eauto.
Qed.

Lemma refineL_trans (L L' : LabelRel) {Lf} {e1} e2 {e3}
  (Hf : L ⋅ L' ⊑ Lf)
  (H12 : RefineL L e1 e2) (H23 : RefineL L' e2 e3) :
  RefineL Lf e1 e3.
Proof.
  split.
  - destruct H12 as [R12 _]; destruct H23 as [R23 _].
    intro H1. apply R23. apply R12. apply H1.
  - destruct H12 as [_ R12]; destruct H23 as [_ R23]. intros ℓ1 H1.
    destruct (R12 ℓ1 H1) as (ℓ2 & L12 & H2). clear R12.
    destruct (R23 ℓ2 H2) as (ℓ3 & L23 & H3). clear R23.
    exists ℓ3. split; auto.
    (* apply Hf. exists ℓ2. split; auto. *)
Qed.

Notation "e ≤{ L } e' " := (RefineL L e e') (at level 10).

Definition EquiBehaveL (L : label → Prop) (e e' : expr) : Prop :=
    e ≤{diagonal L} e' ∧ e' ≤{diagonal L} e.

Notation "e ≡{ L } e' " := (EquiBehaveL L e e') (at level 10).

Lemma RefineL_weaken {L L' e e'} :
  RefineL L e e' →
  (L ⊑ L') →
  RefineL L' e e'.
Proof. intros; destruct H. split; naive_solver. Qed.
