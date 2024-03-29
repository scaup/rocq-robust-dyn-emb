From main.prelude Require Import imports labels.
From main.grad_lang Require Import definition types typing contexts.
From main.maps Require Import linker.components.

(* Notation gexpr := grad_lang.definition.expr. *)
(* Notation dexpr := dyn_lang.definition.expr. *)
(* Notation gVar := grad_lang.definition.Var. *)
(* Notation gApp := grad_lang.definition.Var. *)

Section linker.

  Context {ν : label} {Hν : NeverOccurs ν}.

  (* todo; generalize to list of labels? *)
  Definition linker (ℓ : label) (Γ : list type) (τ : type) : ctx :=
     AppWithList_ctx (wrap_ctx_vars_ascribe_up ℓ Γ)
  ++ LamN_ctx (length Γ)
  ++ [ CTX_Ascribe ℓ Unknown τ ].

  Lemma linker_typed ℓ Γ τ :
    let n := length Γ in
    typed_ctx (linker ℓ Γ τ) (replicate n Unknown ++ Γ) Unknown
                             Γ τ.
  Proof.
    apply (typed_ctx_compose _ Γ _ _ _ _ (LamN_type (replicate (length Γ) Unknown) τ)).
    apply AppWithList_ctx_typed'.
    { apply Forall2_replicate_l. by rewrite /wrap_ctx_vars_ascribe_up imap_length.
      apply wrap_ctx_vars_ascribe_up_typed. }
    apply (typed_ctx_compose _ (replicate (length Γ) Unknown ++ Γ) _ _ _ _ τ).
    rewrite <- (app_nil_l Γ) at 4.
    apply typed_ctx_app_r. rewrite <- (replicate_length (length Γ) Unknown) at 1.
    apply LamN_ctx_typed. repeat econstructor.
  Qed.


End linker.

(* Section dyn_emb. *)

(*   Context {ν : label} {Hν : NeverOccurs ν}. *)

(*   Definition import (ℓ : label) (Γ : list type) (τ : type) (e : dexpr) : gexpr := *)
(*      Wrap_g (Ascribe ℓ Unknown τ ⌜⌜e⌝⌝) *)
(*        ((fun τ => Lam (Ascribe ℓ τ Unknown (Var 0))) <$> Γ). *)

(* End dyn_emb. *)
