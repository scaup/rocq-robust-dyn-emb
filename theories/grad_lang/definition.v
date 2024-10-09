From main.prelude Require Import imports autosubst.
From main.prelude Require Export labels base_lang.
From main.grad_lang Require Export types.

Inductive expr :=
  (* base values *)
  | Lit (b : base_lit)
  | Seq (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | BinOp (binop : bin_op) (e1 e2 : expr)
  (* functions *)
  | Var (v : var)
  | Lam (e : {bind 1 of expr})
  | App (e1 e2 : expr)
  (* sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 e2 : {bind 1 of expr})
  (* pairs *)
  | Fst (e : expr)
  | Snd (e : expr)
  | Pair (e1 e2 : expr)
  (* error *)
  (* | Error (ℓ : label) *)
  (* Easier if we have source type, then translation is easier *)
  (* Also a proof of consistency? *)
  (* | Cast (τ1 τ2 : type) (e : expr) *)
  (* We want translation from surface to cast calculus to be definable without typing derivation... *)
  | Cast (ℓ : label) (τ1 τ2 : type) (e : expr)
  | Error (ℓ : label).
  (* | Ascribe (ℓ : label) (τ1 τ2 : type) (e : expr). *)
