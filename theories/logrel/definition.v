From main.prelude Require Import imports autosubst big_op_three.
From main.grad_lang Require Import types.
From main.dyn_lang Require Import definition lemmas lib labels.
From main.logrel.lib Require Import weakestpre rfn.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

Section logrel.

  Definition unit_rel : val -d> val -d> siProp :=
    λ v v', (match v, v' with
            | LitV (LitUnit), LitV (LitUnit) => True
            | _, _ => False
            end)%I.

  Definition bool_rel : val -d> val -d> siProp :=
    λ v v', (match v, v' with
            | LitV (LitBool b), LitV (LitBool b') => b ≡ b'
            | _, _ => False
            end)%I.

  Definition int_rel : val -d> val -d> siProp :=
    λ v v', (match v, v' with
            | LitV (LitInt z), LitV (LitInt z') => z ≡ z'
            | _, _ => False
            end)%I.

  Definition prod_rel (Φ1 Φ2 : val -d> val -d> siProp) : val -d> val -d> siProp :=
    λ v v', (match v, v' with
            | PairV v1 v2, PairV v1' v2' => Φ1 v1 v1' ∗ Φ2 v2 v2'
            | _, _ => False
            end)%I.

  Definition sum_rel (Φ1 Φ2 : val -d> val -d> siProp) : val -d> val -d> siProp :=
    λ v v', (match v, v' with
            | InjLV w, InjLV w' => Φ1 w w'
            | InjRV w, InjRV w' => Φ2 w w'
            | _, _ => False
            end)%I.

  Definition arrow_rel (MaybeLater : siProp -> siProp) (Φ1 Φ2 : val -d> val -d> siProp) (L2 : label -> label -> Prop) :
    val -d> val -d> siProp :=
    λ v v', (match v, v' with
            | LamV e, LamV e' => (MaybeLater (∀ w w', Φ1 w w' -∗ rfn Φ2 L2 e.[of_val w/] e'.[of_val w'/]))
            | _, _ => False
            end)%I.

  Definition later_rfn (Φ : val -d> val -d> siProp) : val -d> val -d> siProp :=
    λ v v', (▷ Φ v v')%I.

  Definition valrel_unknown_pre Δ (Ψ : val -d> val -d> siProp) :
    val -d> val -d> siProp :=
    λ v v', match v, v' with
            | LitV LitUnit, LitV LitUnit => unit_rel v v'
            | LitV (LitBool _), LitV (LitBool _) => bool_rel v v'
            | LitV (LitInt _), LitV (LitInt _) => int_rel v v'
            | LamV _, LamV _ => (arrow_rel bi_later Ψ Ψ Δ) v v'
                                 (* only a later at the start to enforce contractiveness *)
            | InjLV _, InjLV _ => sum_rel (later_rfn Ψ) (later_rfn Ψ) v v'
            | InjRV _, InjRV _ => sum_rel (later_rfn Ψ) (later_rfn Ψ) v v'
            | PairV _ _, PairV _ _ => prod_rel (later_rfn Ψ) (later_rfn Ψ) v v'
            | _, _ => False%I
            end.

  Instance valrel_unknown_gen_contractive Δ : Contractive (valrel_unknown_pre Δ).
  Proof.
    rewrite /valrel_unknown_pre.
    intros n P1 P2 dl v v'.
    destruct v, v'; (try destruct (_ : base_lit)); auto.
    - rewrite /arrow_rel. apply later_contractive. constructor. intros.
      do 5 f_equiv. by apply dl. apply rfn_proper. by apply dl.
    - rewrite /sum_rel; solve_contractive.
    - rewrite /sum_rel; solve_contractive.
    - rewrite /prod_rel. f_equiv; solve_contractive.
  Qed.

  Definition valrel_unknown Δ := fixpoint (valrel_unknown_pre Δ).

  Lemma valrel_unknown_unfold Δ v v' :
    valrel_unknown Δ v v' ≡ valrel_unknown_pre Δ (valrel_unknown Δ) v v'.
  Proof.
    unfold valrel_unknown at 1.
    by rewrite (fixpoint_unfold (valrel_unknown_pre Δ) v v').
  Qed.

  Fixpoint valrel_typed (τ : type) : (label → label → Prop) -d> val -d> val -d> siProp :=
    λ Δ v v', (
      match τ with
      | Base B => match B with
                 | Unit => unit_rel v v'
                 | Bool => bool_rel v v'
                 | Int => int_rel v v'
                 end
      | Bin bin τ1 τ2 => match bin with
                        | Arrow => arrow_rel id (valrel_typed τ1 Δ) (valrel_typed τ2 Δ) Δ v v'
                                 (* only a later for the return expressions; such that they are equivalent to app; \x.e w ~ \x.e' w' *)
                        | Sum => sum_rel (valrel_typed τ1 Δ) (valrel_typed τ2 Δ) v v'
                        | Product => prod_rel (valrel_typed τ1 Δ) (valrel_typed τ2 Δ) v v'
                        end
      | Unknown => valrel_unknown Δ v v'
      end)%I.

  Definition exprel_typed (τ : type) (Δ : LabelRel) : expr -d> expr -d> siProp :=
    λ e e', rfn (valrel_typed τ Δ) Δ e e'.

End logrel.

Definition open_exprel_typed (Γ : list type) (L : LabelRel) (e e' : expr) (τ : type) : Prop :=
  ∀ (Δ : LabelRel) (H : L ⊑ Δ) (vs vs' : list val),
      big_sepL3 (fun τ v v' => valrel_typed τ Δ v v') Γ vs vs' ⊢
          exprel_typed τ Δ e.[subst_list (of_val <$> vs)] e'.[subst_list (of_val <$> vs')].

Lemma open_exprel_typed_weaken (L L' : LabelRel) (H : L ⊑ L')
  (Γ : list type) (e e' : expr) (τ : type) :
  open_exprel_typed Γ L e e' τ → open_exprel_typed Γ L' e e' τ.
Proof. intros. intros Δ HL'Δ. apply H0. by eapply le_permissive_trans'. Qed.

Lemma open_exprel_typed_app_ctx Γ' (L : LabelRel)
  (Γ : list type) (e e' : expr) (He : Closed_n (length Γ) e) (He' : Closed_n (length Γ) e') (τ : type) :
  open_exprel_typed Γ L e e' τ → open_exprel_typed (Γ ++ Γ') L e e' τ.
Proof.
  intros. intros Δ HL'Δ.
  iIntros (vsws vsws') "H".
  iDestruct (big_sepL3_length with "H") as "[%eq1 %eq2]". repeat rewrite app_length in eq1 eq2.
  rewrite -(take_drop (length Γ) vsws). rewrite -(take_drop (length Γ) vsws').
  iDestruct (big_sepL3_app_inv with "H") as "[Hint Htrash]".
  { left. split; repeat rewrite firstn_length_le; try lia. }
  repeat rewrite fmap_app subst_list_app fmap_length firstn_length_le; try lia.
  assert (bf : ∀ e n (H : Closed_n n e) σ σ', e.[upn n σ >> σ'] = e.[σ']).
  { intros. replace e0.[upn n σ >> σ'] with e0.[upn n σ].[σ'] by by asimpl. by rewrite H0. } repeat rewrite bf; auto.
  by iApply (H with "Hint").
Qed.

From main.dyn_lang Require Import contexts.

Definition ctx_rel_typed (L : LabelRel) (C C' : ctx)
  (Γ : list type)(*hole*) (τ : type)(*hole*) (Γout : list type)(*outer*) (τout : type)(*outer*) : Prop :=
  ∀ L' (H : L ⊑ L') e e' (Hee' : open_exprel_typed Γ L' e e' τ),
      open_exprel_typed Γout L' (fill_ctx C e) (fill_ctx C' e') τout.

Lemma ctx_rel_typed_weaken C C' (L L' : LabelRel) (H : le_permissive L L')
  (Γ1 Γ2 : list type) (τ1 τ2 : type) :
  ctx_rel_typed L C C' Γ1 τ1 Γ2 τ2 → ctx_rel_typed L' C C' Γ1 τ1 Γ2 τ2.
Proof.
  intros. intros Δ HL'Δ e e' Hee'. apply H0; auto. eapply le_permissive_trans_inst; eauto. Qed.

(* Lemma open_exprel_typed_compose L12 L23 Γ1 Γ2 Γ3 C12 C12' C23 C23' τ1 τ2 τ3 : *)
(*   ctx_rel_typed L12 C12 C12' Γ1 τ1 Γ2 τ2 → *)
(*   ctx_rel_typed L23 C23 C23' Γ2 τ2 Γ3 τ3 → *)
(*   ctx_rel_typed (L23 ⊔ L12) (C23 ++ C12) (C23' ++ C12') Γ1 τ1 Γ3 τ3. *)
(* Proof. *)
(*   intros. intros L1' HL1 e e' Hee. *)
(*   repeat rewrite /fill_ctx foldr_app. *)
(*   repeat change (foldr fill_ctx_item ?e ?C) with (fill_ctx C e). *)
(*   apply H0. { intros l l' Hll. apply HL1. by left. } *)
(*   apply H. { intros l l' Hll. apply HL1. by right. } *)
(*   auto. *)
(* Qed. *)
