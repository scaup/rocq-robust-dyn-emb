From main.prelude Require Import base_lang labels imports.
From main.grad_lang Require Import types.

(* Important; we don't have labels anymore on destructors. *)
(* Only on cast constructs *)

Inductive expr :=
  (* base values *)
  | Lit (b : base_lit)
  | Seq (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | BinOp (binop : bin_op) (e1 e2 : expr)
  (* functions *)
  | Var (v : nat)
  | Lam (e : expr)
  | App (e1 e2 : expr)
  (* sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 e2 : expr)
  (* pairs *)
  | Fst (e : expr)
  | Snd (e : expr)
  | Pair (e1 e2 : expr)
  (* error *)
  | Error (ℓ : label)
  (* Easier if we have source type, then translation is easier *)
  (* Also a proof of consistency? *)
  (* | Cast (τ1 τ2 : type) (e : expr) *)
  (* We want translation from surface to cast calculus to be definable without typing derivation... *)
  | Ascribe (ℓ : label) (τ1 τ2 : type) (e : expr).
