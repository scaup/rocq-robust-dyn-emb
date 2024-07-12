From main.prelude Require Import imports autosubst big_op_three.
From main.grad_lang Require Import types.
From main.dyn_lang Require Import definition lemmas tactics labels lib.
From main.logrel.lib Require Import weakestpre rfn small_helpers.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

From main.logrel Require Import definition.
From main.maps Require Import dyn_embedding.definition grad_into_dyn.definition.

From main.grad_lang Require Import typing.

Section typing.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma dyn_emb_typed e n : Closed_n n e →
    typed (replicate n Unknown) (⌈⌈ e ⌉⌉) Unknown.
  Proof.
    revert n.
    induction e; intros; simpl; (repeat econstructor);
        (try by eapply IHe0; closed_solver);
        (try by eapply IHe; closed_solver);
        (try by eapply IHe1; closed_solver);
        (try by eapply IHe2; closed_solver);
        (try by eapply IHe3; closed_solver).
    assert (H' := (ids_lt_Closed_n v n)).
    apply lookup_replicate_2. apply H'.  apply H.
    eapply (IHe (S n)). closed_solver.
    apply (IHe0 (S n)). closed_solver.
    apply (IHe1 (S n)). closed_solver.
  Qed.

End typing.
