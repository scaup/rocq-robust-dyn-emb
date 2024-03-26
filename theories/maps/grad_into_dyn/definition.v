From main Require Import imports.

From main.grad_lang Require Import types definition.
From main.dyn_lang Require Import definition casts lib.

(* The translation to define the semantics of surface language. *)

Definition sf_expr := grad_lang.definition.expr .

Section anon.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Fixpoint trns (e : sf_expr) : expr :=
    match e with
    | grad_lang.definition.Lit b => Lit b
    | grad_lang.definition.Seq e1 e2 => Seq ν (trns e1) (trns e2)
    | grad_lang.definition.If e0 e1 e2 => If ν (trns e0) (trns e1) (trns e2)
    | grad_lang.definition.BinOp binop e1 e2 => BinOp ν binop (trns e1) (trns e2)
    | grad_lang.definition.Var v => Var v
    | grad_lang.definition.Lam e => Lam (trns e)
    | grad_lang.definition.App e1 e2 => App ν (trns e1) (trns e2)
    | grad_lang.definition.InjL e => InjL (trns e)
    | grad_lang.definition.InjR e => InjR (trns e)
    | grad_lang.definition.Case e0 e1 e2 => Case ν (trns e0) (trns e1) (trns e2)
    | grad_lang.definition.Fst e => Fst ν (trns e)
    | grad_lang.definition.Snd e => Snd ν (trns e)
    | grad_lang.definition.Pair e1 e2 => Pair (trns e1) (trns e2)
    | grad_lang.definition.Error ℓ => Error ℓ
    | Ascribe ℓ τ1 τ2 e => match consistency_decision τ1 τ2 with
                         | inl Pc => App ν (of_val $ cast ℓ τ1 τ2 Pc) (trns e)
                         | inr _ => Lit LitUnit
                         end
    end.

End anon.

Notation "⌊ e ⌋" := (trns e).
