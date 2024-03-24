From main.dyn_lang Require Import definition lib.
From main.prelude Require Import imports.

Ltac rw_of_val :=
  repeat (
      try change (Lam ?e) with (of_val $ LamV e);
      try change (Lit ?b) with (of_val $ LitV b);
      try change (InjL (of_val ?v)) with (of_val $ InjLV v);
      try change (InjR (of_val ?v)) with (of_val $ InjRV v);
      try change (Pair (of_val ?v) (of_val ?w)) with (of_val $ PairV v w)
    ).

Ltac rw_fill_item :=
  simpl;
  (try (rewrite /AppAn));
  rw_of_val;
  (repeat (
      try change (App ?ℓ (of_val ?v) ?e) with (fill_item (AppRCtx ℓ v) e);
      try change (App ?ℓ ?e1 ?e2) with (fill_item (AppLCtx ℓ e1) e2);
      try change (Pair (of_val ?v1) ?e2) with (fill_item (PairRCtx v1) e2);
      try change (Pair ?e1 ?e2) with (fill_item (PairLCtx e2) e1);
      try change (Fst ?ℓ ?e) with (fill_item (FstCtx ℓ) e);
      try change (Snd ?ℓ ?e) with (fill_item (SndCtx ℓ) e);
      try change (InjL ?e) with (fill_item InjLCtx e);
      try change (InjR ?e) with (fill_item InjRCtx e);
      try change (Case ?ℓ ?e1 ?e2 ?e3) with (fill_item (CaseCtx ℓ e2 e3) e1);
      try change (If ?ℓ ?e1 ?e2 ?e3) with (fill_item (IfCtx ℓ e2 e3) e1);
      try change (BinOp ?ℓ ?op (of_val ?v1) ?e2) with (fill_item (BinOpRCtx ℓ op v1) e2);
      try change (BinOp ?ℓ ?op ?e1 ?e2) with (fill_item (BinOpLCtx ℓ e2) e1);
      try change (Seq ?ℓ ?e1 ?e2) with (fill_item (SeqCtx ℓ e2) e1)
    )).

Ltac rw_fill := (* for e.g. bind lemmas *)
  rw_fill_item;
  (change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 (fill_item ?Ki4 (fill_item ?Ki5 (fill_item ?Ki6 ?e))))))
    with (fill [Ki1 ; Ki2 ; Ki3 ; Ki4; Ki5; Ki6] e);
   change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 (fill_item ?Ki4 (fill_item ?Ki5 ?e)))))
     with (fill [Ki1 ; Ki2 ; Ki3 ; Ki4 ; Ki5] e);
   change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 (fill_item ?Ki4 ?e))))
     with (fill [Ki1 ; Ki2 ; Ki3 ; ?Ki4] e);
   change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 ?e)))
     with (fill [Ki1 ; Ki2 ; Ki3] e);
   change (fill_item ?Ki1 (fill_item ?Ki2 ?e))
     with (fill [Ki1; Ki2] e);
   change (fill_item ?Ki ?e)
     with (fill [Ki] e)
  ).

Ltac rw_fill_popped := (* for e.g. faulty and step solving *)
  rw_fill_item;
  (change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 (fill_item ?Ki4 (fill_item ?Ki5 (fill_item ?Ki6 ?e))))))
    with (fill [Ki1 ; Ki2 ; Ki3 ; Ki4; Ki5] (fill_item Ki6 e));
   change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 (fill_item ?Ki4 (fill_item ?Ki5 ?e)))))
     with (fill [Ki1 ; Ki2 ; Ki3 ; Ki4 ] (fill_item Ki5 e));
   change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 (fill_item ?Ki4 ?e))))
     with (fill [Ki1 ; Ki2 ; Ki3 ] (fill_item Ki4 e));
   change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 ?e)))
     with (fill [Ki1 ; Ki2] (fill_item Ki3 e));
   change (fill_item ?Ki (fill_item ?Ki2 ?e))
     with (fill [Ki] (fill_item Ki2 e));
   change (fill_item ?Ki ?e)
     with (fill [] (fill_item Ki e))
  ).

Ltac head_step_sides :=
  by (lazymatch goal with
      | |- to_val (_) = Some _ => rw_of_val; eauto; by rewrite to_of_val
      (* | |- to_val (of_val _) = Some _ => simplify_option_eq; by rewrite to_of_val *)
      | _ => fail "head_step_sides"
      end).

Ltac head_step_solver :=
  by (lazymatch goal with
      | |- head_step_not_error _ _ => simpl; econstructor; head_step_sides
      | _ => fail "head_step_solver"
      end).

Ltac head_faulty_sides :=
 by (lazymatch goal with
      | |- to_val (_) = Some _ => rw_of_val; eauto; by rewrite to_of_val
      (* | |- to_val (of_val _) = Some _ => by rewrite to_of_val *)
      | |- shape_val (LitV ?z) ≠ S_Bin _ => by destruct z
      | |- _ => eauto; naive_solver
      (* | _ => fail "head_faulty_sides" *)
      end).

Ltac head_faulty_solver :=
  by (lazymatch goal with
      | |- head_faulty _ _ => econstructor; head_faulty_sides
      (* | |- faulty  *)
      | _ => fail "head_faulty_solver"
      end).

Lemma stepK (K : ectx) {e t t' e'} :
  e = fill K t →
  head_step_not_error t t' →
  e' = fill K t' →
  step_not_error e e'.
Proof. intros. simplify_eq. by constructor. Qed.

(* Ltac rw_pop_head := *)
(*     (change (fill [?Ki] ?e) with (fill [] (fill_item Ki e))). *)

Ltac step_solver :=
  by (lazymatch goal with
      | |- step_not_error _ _ => rw_fill_popped; eapply (stepK _ ltac:(eauto)); eauto;
                                 head_step_solver
      | _ => fail "step_solver"
      end).

Lemma faultyK (K : ectx) {e t ℓ} :
  e = fill K t →
  head_faulty t ℓ →
  faulty e ℓ.
Proof. exists K, t. split; auto. Qed.

Ltac faulty_solver :=
  by (lazymatch goal with
      | |- faulty _ _ => rw_fill; rw_fill_popped; eapply (faultyK _ ltac:(eauto)); eauto;
                                 head_faulty_solver
      (* | |- faulty _ _ => auto *)
      | _ => fail "faulty_step_solver"
      end).
