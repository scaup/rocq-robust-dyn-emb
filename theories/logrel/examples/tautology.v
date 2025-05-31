From main.prelude Require Import imports autosubst big_op_three.
From main.cast_calc Require Import types.
From main.dyn_lang Require Import definition lemmas lib labels tactics.
From main.logrel.lib Require Import weakestpre rfn small_helpers recursion.
From main.logrel Require Import definition.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.
(* From iris.proofmode Require Import base proofmode classes. *)

Section tautology_example.

  Context {ν : label} {Hν : NeverOccurs ν}.

  (* "David Turner’s tautology program" *)
  (* Courtesy to reviewer A *)

  Definition isZero (e : expr) : expr :=
     BinOp ν EqOp 0 e.

  Definition MinusOne (e : expr) : expr :=
     BinOp ν MinusOp e 1.

  Definition And (e1 e2 : expr) : expr :=
     If ν e1 (If ν e2 true false) false.

  Definition tautV : val :=
    RecV (*n*) (*f*) (
     If ν (isZero (Var 0(*n*)))
     (* then *) (Lam (Var 0))
     (* esle *) (Lam (*g*) (And ((Var 2(*r*)) (MinusOne (Var 1(*n*))) ((Var 0(*g*)) true))
                                ((Var 2(*r*)) (MinusOne (Var 1(*n*))) ((Var 0(*g*)) false))))
      ).
  (* taut 0 g  =  g *)
  (* taut n g  =  taut (n-1) (g false) && taut (n-1) (g true) *)


  Notation taut := (of_val tautV).

  Ltac rfn_steps :=
    asimpl; (rfn_l_s; asimpl); (rfn_r_s; asimpl).

  Fixpoint dom_taut (n : nat) : type :=
    match n with
    | O => Base Bool
    | S n => Bin Arrow (Base Bool) (dom_taut n)
    end.

  Definition type_taut (n : nat) : type := Bin Arrow (dom_taut n) (Base Bool).

  Lemma taut_closed : Closed taut.
  Proof. intros σ. rewrite /taut Rec_subst. by asimpl. Qed.

  Lemma taut_sem_typed (n : nat) : sem_typed [] (taut n) (type_taut n).
  Proof.
    split. 2: { intros σ. rewrite /taut. asimpl. rewrite Rec_subst. by asimpl. }
    induction n; rewrite /taut.
    - iIntros (Δ HΔ vs vs') "_". asimpl. rewrite /type_taut /=.
      do 2 rewrite Rec_subst. asimpl.
      iApply rfn_lr_Rec_App; auto. asimpl.
      rfn_steps. repeat rewrite bool_decide_true; auto. rfn_steps. rfn_val.
      repeat iNext. iIntros (v v') "#Hvv'". rfn_val.
    - iIntros (Δ HΔ vs vs') "#H". asimpl.
      do 2 rewrite Rec_subst. asimpl.
      iApply rfn_lr_Rec_App; auto. asimpl.
      rfn_steps. repeat rewrite bool_decide_false; auto. repeat rfn_steps.
      repeat iNext. rfn_val.
      iIntros (g g') "#Hgg'".

      repeat rfn_steps.
      assert ((S n - 1%nat)%Z = n) as -> by by lia.

      specialize (IHn Δ HΔ vs vs').
      iDestruct (IHn with "H") as "HHH".

      change ((Rec
                  (If ν (BinOp ν EqOp 0 (ids 0))
                     (Lam (ids 0))
                     (Lam
                        (If ν
                           (App ν
                              (App ν (ids 2)
                                 (BinOp ν MinusOp (ids 1) 1))
                              (App ν (ids 0) true))
                           (If ν
                              (App ν
                                 (App ν (ids 2)
                                    (BinOp ν MinusOp (ids 1) 1))
                                 (App ν (ids 0) false)) true false)
                           false)))) ) with (taut).
      repeat rewrite /= taut_closed.
      rfn_bind_pp. iApply "HHH".
      iNext.

      iIntros (k k') "#Hkk'".
      dvals g g'. rfn_bind_pp. rfn_steps. rw_of_val. by iApply "Hgg'".

      iIntros (l l') "#Hll'".

      dvals k k'. rfn_steps. rfn_bind. by iApply "Hkk'".

      iNext. iIntros (b b') "#Hbb'".
      dvals b b'. iDestruct "Hbb'" as "<-". destruct b; repeat rfn_steps; [| rfn_val].
      assert ((S n - 1%nat)%Z = n) as -> by by lia.
      rfn_bind_pp. iApply "HHH".
      repeat iNext. iIntros (m m') "#Hmm'".
      dvals m m'. rfn_steps. rfn_bind. rw_of_val. iApply "Hgg'". auto.
      iNext. iIntros (o o') "#Hoo'". rfn_steps. iNext.
      rfn_bind. by iApply "Hmm'".
      iIntros (b b') "Hbb'". dvals b b'. iDestruct "Hbb'" as "<-".
      rfn_steps. destruct b; rfn_val.
  Qed.


  (* just as illustration; tautology function is well typed in coq *)

  Fixpoint dom_taut_coq (n : nat) : Type :=
    match n with
    | O => bool
    | S n => bool → (dom_taut_coq n)
    end.

  Definition type_taut_coq (n : nat) : Type :=
    dom_taut_coq n → bool.

  Compute (type_taut_coq 3).

  Fixpoint taut_coq (n : nat) : (type_taut_coq n) :=
    match n with
    | O => id
    | S n => fun g => (taut_coq n (g false)) && (taut_coq n (g true))
    end.

  Fail Fixpoint taut_coq_naive (n : nat) (h : dom_taut_coq n) : bool :=
    match n with
    | O => h
    | S n => (taut_coq n (h false)) && (taut_coq n (h true))
    end.

End tautology_example.
