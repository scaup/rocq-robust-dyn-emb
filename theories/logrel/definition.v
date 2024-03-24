From main.prelude Require Import imports autosubst big_op_three.
From main.surf_lang Require Import types.
From main.dyn_lang Require Import definition lemmas lib.
From main.logrel.lib Require Import weakestpre rfn.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.
(* From iris.proofmode Require Import base proofmode classes. *)

Section logrel.

  Context {ν : label} {Hν : NeverOccurs ν}.

  (* Definition pairs := list (prod label label). *)
  Definition pairs := label -d> label -d> siProp.

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

  Inductive guarded := G_YesPlz | G_NoThanks.

  Definition arrow_rel (g : guarded) (Φ1 Φ2 : val -d> val -d> siProp) (L2 : label -d> label -d> siProp) :
    val -d> val -d> siProp :=
    λ v v', (match v, v' with
            | LamV e, LamV e' => (match g with
                                | G_YesPlz => bi_later
                                | G_NoThanks => id
                                 end (∀ w w', Φ1 w w' -∗ ▷ rfn Φ2 L2 e.[of_val w/] e'.[of_val w'/]))
                  (* end) (∀ w w', ▷ Φ1 w w' -∗ rfn Φ2 L2 (AppAn (Lam e) (of_val w)) (AppAn (Lam e') (of_val w')))) *)
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
            | LamV _, LamV _ => (arrow_rel G_YesPlz Ψ Ψ Δ) v v'
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
      do 5 f_equiv. by apply dl. f_equiv. apply rfn_proper. by apply dl.
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

  Fixpoint valrel_typed (τ : type) : pairs -d> val -d> val -d> siProp :=
    λ Δ v v', (
      match τ with
      | Base B => match B with
                 | Unit => unit_rel v v'
                 | Bool => bool_rel v v'
                 | Int => int_rel v v'
                 end
      | Bin bin τ1 τ2 => match bin with
                        | Arrow => arrow_rel G_NoThanks (valrel_typed τ1 Δ) (valrel_typed τ2 Δ) Δ v v'
                        | Sum => sum_rel (valrel_typed τ1 Δ) (valrel_typed τ2 Δ) v v'
                        | Product => prod_rel (valrel_typed τ1 Δ) (valrel_typed τ2 Δ) v v'
                        end
      | Unknown => valrel_unknown Δ v v'
      end)%I.

  Definition exprel_typed (τ : type) (Δ : pairs) : expr -d> expr -d> siProp :=
    λ e e', rfn (valrel_typed τ Δ) Δ e e'.

  Definition less_possibilities_then : relation pairs :=
    fun Δ1 Δ2 => ∀ ℓ ℓ', Δ2 ℓ ℓ' -∗ Δ1 ℓ ℓ'.

  Notation "a ⪯ b" := (less_possibilities_then a b) (at level 30).

  Definition open_exprel_typed (Γ : list type) (e e' : expr) (R : pairs) (τ : type) :=
    ∀ (Δ : pairs) (vs vs' : list val),
        ⌜ R ⪯ Δ ⌝ ∗ big_sepL3 (fun τ v v' => valrel_typed τ Δ v v') Γ vs vs' ⊢
            exprel_typed τ Δ e.[subst_list (of_val <$> vs)] e'.[subst_list (of_val <$> vs')].

End logrel.


  (*  Lemma open_exprel_typed_nil τ e e' : (⊢ exprel_typed τ e e') -> open_exprel_typed [] e e' τ. *)
  (* Proof. iIntros (Hee' vs vs') "Hvv'". destruct vs, vs'; auto. asimpl. iApply Hee'. Qed. *)

  (* Lemma open_exprel_typed_nil' τ e e' : open_exprel_typed [] e e' τ → (⊢ exprel_typed τ e e'). *)
  (* Proof. rewrite /open_exprel_typed. iIntros (Hee'). iDestruct (Hee' [] []) as "H". asimpl. by iApply "H". Qed. *)

  (* Definition ctx_item_rel_typed (Ci Ci' : ctx_item) Γ τ Γ' τ' := *)
  (*   ∀ e e' (pe : expr_scoped (length Γ) e) (pe' : expr_scoped (length Γ) e'), open_exprel_typed Γ e e' τ → open_exprel_typed Γ' (fill_ctx_item Ci e) (fill_ctx_item Ci' e') τ'. *)

  (* Definition ctx_rel_typed (C C' : ctx) Γ τ Γ' τ' := *)
  (*   ∀ e e' (pe : expr_scoped (length Γ) e) (pe' : expr_scoped (length Γ) e'), open_exprel_typed Γ e e' τ → open_exprel_typed Γ' (fill_ctx C e) (fill_ctx C' e') τ'. *)



  (* Definition valrel_unknown_pre Δ (Ψ : val -d> val -d> siProp) : *)
  (*   val -d> val -d> siProp := *)
  (*   λ v v', (∃ S : shape, match S with *)
  (*                         | S_Base b => match b with *)
  (*                                      | Unit => unit_rel v v' *)
  (*                                      | Bool => bool_rel v v' *)
  (*                                      | Int => int_rel v v' *)
  (*                                      end *)
  (*                         | S_Bin bin => match bin with *)
  (*                                       | Product => prod_rel (later_rfn Ψ) (later_rfn Ψ) v v' *)
  (*                                       | Sum => sum_rel (later_rfn Ψ) (later_rfn Ψ) v v' *)
  (*                                       | Arrow => (arrow_rel G_YesPlz Ψ Ψ Δ) v v' *)
  (*                                       end *)
  (*                        end)%I. *)
