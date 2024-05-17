From main.dyn_lang Require Import definition lib tactics.
From main.prelude Require Import imports autosubst.
From main.logrel.lib Require Import rfn weakestpre.
From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

(* Some wrappers for step_solver and faulty_solver tactics *)

(* Ltac rfn_bind H := rw_fill; iApply (rfn_bind' with H); simpl. *)
(* Ltac rfn_bind' := rw_fill; iApply (rfn_bind'); simpl. *)
(* Ltac rfn_bind_pop H := rw_fill_popped; iApply (rfn_bind' with H); simpl. *)
(* Ltac rfn_bind_pop' := rw_fill_popped; iApply rfn_bind'; simpl. *)

Ltac rfn_l_s := iApply rfn_s_l; first by step_solver.
Ltac rfn_r_s := iApply rfn_s_r; first by step_solver.

Ltac rfn_steps :=
  asimpl; repeat (rfn_l_s; asimpl); repeat (rfn_r_s; asimpl).

Ltac rfn_val := rw_of_val; iApply rfn_val; eauto.

Ltac dvals v v' := destruct v, v'; repeat (lazymatch goal with | x : base_lit |- _ => destruct x end); auto.

(* Ltac rfn_faulty := by (iApply (rfn_faulty _ _ with "Hp"); faulty_solver). *)

Ltac rfn_faulty := (iApply rfn_faulty; [ by faulty_solver| by faulty_solver | auto; by delta_solver ]).

Section lemmas.

  Lemma wp_lam_app_rw Φ L ν' e w :
    ⊢ wp Φ L (App ν' (Lam e) (of_val w)) -∗ ▷ wp Φ L e.[of_val w/].
  Proof. iIntros "H". iApply (wp_s_inv with "H").
         rw_fill_popped. step_solver. Qed.

  Lemma rfn_l_lam_app_rw ν Φ L e w e' :
    ⊢ rfn Φ L (App ν (Lam e) (of_val w)) e' -∗ ▷ rfn Φ L e.[of_val w/] e'.
  Proof. iApply wp_lam_app_rw. Qed.

  Lemma rfn_r_lam_app_rw ν Φ L e w' e' :
    ⊢ rfn Φ L e (App ν (Lam e') (of_val w')) -∗ rfn Φ L e e'.[of_val w'/].
  Proof. iIntros "H". iApply (rfn_s_r_inv with "H"). step_solver. Qed.

End lemmas.

Lemma rfn_bindK {K K' t t' e e' Ψ Φ L} :
  t = fill K e →
  t' = fill K' e' →
  ⊢ rfn Ψ L e e' -∗ (∀ v v', Ψ v v' -∗ rfn Φ L (fill K (of_val v)) (fill K' (of_val v'))) -∗ rfn Φ L t t'.
Proof. intros. simplify_eq. iApply rfn_bind'. Qed.

(* "bind pop left" *)
Ltac rfn_bind_pr :=
  iApply rfn_bindK; [ simpl; by rw_fill; eauto | simpl; by rw_fill_popped; eauto | simpl | simpl ].

Ltac rfn_bind_pl :=
  iApply rfn_bindK; [ simpl; by rw_fill_popped; eauto | simpl; by rw_fill; eauto | simpl | simpl ].

Ltac rfn_bind_pp :=
  iApply rfn_bindK; [ simpl; by rw_fill_popped; eauto | simpl; by rw_fill_popped; eauto | simpl | simpl ].

Ltac rfn_bind :=
  iApply rfn_bindK; [ simpl; by rw_fill; eauto | simpl; by rw_fill; eauto | simpl | simpl ].
