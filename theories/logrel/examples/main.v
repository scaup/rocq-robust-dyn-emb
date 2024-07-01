From main.prelude Require Import imports autosubst big_op_three.
From main.grad_lang Require Import types.
From main.dyn_lang Require Import definition lemmas lib labels tactics.
From main.logrel.lib Require Import weakestpre rfn small_helpers.
From main.logrel Require Import definition.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.
(* From iris.proofmode Require Import base proofmode classes. *)

Section examples.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Definition example1 : expr :=
    Lam (
        If ν (BinOp ν LtOp (Var 0) (BinOp ν PlusOp (Var 0) (Lit $ LitInt 1)))
          (Var 0)
          (App ν (Lit $ LitInt 5) (Lit $ LitBool true))
      ).

  Lemma example1_sem_typed :
    sem_typed [] example1 (Bin Arrow (Base Int) (Base Int)).
  Proof.
    split; [| by intros σ; asimpl ].
    iIntros (Δ HΔ vs vs') "_". asimpl. rfn_val.
    iIntros (w w') "Hww'". dvals w w'. iRewrite "Hww'". simpl.
    rfn_steps. rewrite bool_decide_true; try by lia. rfn_val.
  Qed.

  Definition example2 : expr :=
    LetIn (Lam (Pair (Snd ν (Var 0)) (Fst ν (Var 0)))) (* flip *)
      (Lam (*h*) (
           Fst ν
             (AppAn (Var 1) (
                  (AppAn (Var 1)
                     (Pair
                        (BinOp ν PlusOp (AppAn (Var 0) (Lit $ LitInt 6)) (Lit $ LitInt 1))
                        (Lit $ LitBool true)
                     )
                  )
                )
             )
         )
      ).


  Lemma example2_sem_typed :
    sem_typed [] example2 (Bin Arrow (Bin Arrow (Base Int) (Base Int)) (Base Int)).
  Proof.
    split; [| by intros σ; asimpl ].
    iIntros (Δ HΔ vs vs') "_". rfn_steps. rfn_val. iNext.
    iIntros (h h') "#Hhh'". dvals h h'. simpl. rfn_steps.
    rfn_bind. rw_of_val. iApply "Hhh'". auto. iNext.
    iIntros (v v') "Hvv'". dvals v v'. iRewrite "Hvv'".
    rfn_steps. rfn_val.
  Qed.

  Definition example3 : expr :=
    Lam (Case ν (Var 0) (Var 1) (InjL (Lit LitUnit))).

  Lemma example3_sem_typed :
    sem_typed [] example3 (Bin Arrow (Bin Sum (Base Unit) (Base Bool))
                             (Bin Sum (Base Unit) (Base Unit))).
  Proof.
    split; [| by intros σ; asimpl ].
    iIntros (Δ HΔ vs vs') "_". asimpl. rfn_val.
    iIntros (s s') "#Hss'". dvals s s'; rfn_steps; rfn_val.
  Qed.

End examples.
