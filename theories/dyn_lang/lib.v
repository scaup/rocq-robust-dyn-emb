From main.prelude Require Import imports autosubst.
From main.dyn_lang Require Import definition.

(* Definition AppAn {ν : label} {Hν : NeverOccurs ν} (e e' : expr) := *)
(*   App ν e e'. *)

Section anon.

  Context {ν : label}.

  Definition AppAn {Hν : NeverOccurs ν} (e e' : expr) :=
    App ν e e'.

End anon.

Section lib.

  Context {ν : label} {Hν : NeverOccurs ν}.

  (* Global Instance asdf : NeverOccurs ν := _. *)

  Definition LetIn (e1 e2 : expr) : expr :=
    AppAn (Lam e2) e1.

  (* We'll always be using this with f1, f2 lambdas. *)
  Definition bimap_prod (ℓ : label) (f1 f2 : val) : val :=
    LamV (LetIn (Fst ℓ (Var 0))
            (LetIn (Snd ℓ (Var 1))
               (Pair (AppAn (of_val f1).[ren (+3)] (Var 1))
                     (AppAn (of_val f2).[ren (+3)] (Var 0))
               )
            )
      ).

  (* We'll always be using this with f1, f2 lambdas. *)
  Definition bimap_sum (ℓ : label) (f1 f2 : val) : val :=
    LamV (Case ℓ (Var 0)
               (InjL (AppAn (of_val f1).[ren (+2)] (Var 0)))
               (InjR (AppAn (of_val f2).[ren (+2)] (Var 0)))
      ).

  Definition Id : val := LamV (Var 0).

  (* We'll always be using this with f_in, f_out lambdas. *)
  Definition surround (ℓ : label) (f_in f_out : val) : val :=
    LamV (Lam (AppAn (of_val f_out).[ren (+2)] (App ℓ (Var 1) (AppAn (of_val f_in).[ren (+2)] (Var 0))))).

  Definition assert_unit (ℓ : label) : val :=
    LamV (Seq ℓ (Var 0) (Lit LitUnit)).

  Definition assert_bool (ℓ : label) : val :=
    LamV (If ℓ (Var 0) (Lit (LitBool true)) (Lit (LitBool false))).

  Definition assert_int (ℓ : label) : val :=
    LamV (BinOp ℓ PlusOp (Lit (LitInt 0)) (Var 0)).

  Definition comp (f1 f2 : val) : val :=
    LamV (AppAn (of_val f2) (AppAn (of_val f1) (Var 0))) .

  Definition of_shape (ℓ : label) (G : shape) : val :=
    match G with
    | S_Base b => match b with
                 | Unit => assert_unit ℓ
                 | Bool => assert_bool ℓ
                 | Int => assert_int ℓ
                 end
    | S_Bin bin => match bin with
                  | Arrow => surround ℓ Id Id
                  | Sum => bimap_sum ℓ Id Id
                  | Product => bimap_prod ℓ Id Id
                  end
    end.

End lib.


(* Ltac head_step_solver := *)
(*   econstructor; *)
(*     by (repeat ((try simplify_option_eq); (try rewrite to_of_val))). *)

(* Ltac naive_step_solver := *)
(*   apply (SNE_Normal []); head_step_solver. *)

(* Lemma stepK (K : ectx) {e t t'} e' : *)
(*   e = fill K t → *)
(*   head_step_not_error t t' → *)
(*   e' = fill K t' → *)
(*   step_not_error e e'. *)
(* Proof. intros. simplify_eq. by constructor. Qed. *)

(* Instance decision_eq : EqDecision shape. *)
(* Proof. solve_decision. Qed. *)

(* Section lib_lemmas. *)

(*   Context {ν : label} {Hν : NeverOccurs ν}. *)

(*   Lemma bimap_prod_eval (ℓ : label) (f1 f2 : val) (v1 v2 : val) : *)
(*     nsteps step_not_error 5 *)
(*       (App ℓ (of_val $ bimap_prod ℓ f1 f2) (Pair (of_val v1) (of_val v2))) *)
(*       (Pair (AppAn (of_val f1) (of_val v1)) (AppAn (of_val f2) $ (of_val v2))). *)
(*   Proof. *)
(*     eapply nsteps_l. naive_step_solver. *)
(*     eapply nsteps_l. *)
(*     { eapply (stepK [AppRCtx ν _]). asimpl. *)
(*       change (Lam ?e) with (of_val $ LamV e). eauto. *)
(*       head_step_solver. eauto. } *)
(*     simpl. *)
(*     eapply nsteps_l. naive_step_solver. *)
(*     simpl. *)
(*     eapply nsteps_l. *)
(*     { eapply (stepK [AppRCtx ν _]). asimpl. *)
(*       change (Lam ?e) with (of_val $ LamV e). eauto. *)
(*       head_step_solver. eauto. } *)
(*     eapply nsteps_l. naive_step_solver. *)
(*     asimpl; apply nsteps_O. *)
(*   Qed. *)

(*   Lemma bimap_prod_gauge (ℓ : label) (f1 f2 : val) v : *)
(*     (shape_val v ≠ (S_Bin Product) ∧ faulty (App ℓ (of_val $ bimap_prod ℓ f1 f2) (of_val v)) ℓ) *)
(*     ∨ *)
(*     (∃ v1 v2, v = PairV v1 v2 ∧ *)
(*               nsteps step_not_error 5 *)
(*                  (App ℓ (of_val $ bimap_prod ℓ f1 f2) (of_val v)) *)
(*                  (Pair (AppAn (of_val f1) (of_val v1)) (AppAn (of_val f2) $ (of_val v2)))). *)
(*   Proof. *)
(*     destruct (decide (shape_val v = S_Bin Product)). *)
(*     - right. destruct v; (try destruct b); inversion e. *)
(*       exists v1, v2.  split; auto. apply bimap_prod_eval. *)
(*     - left. split; auto. *)


(*   Lemma bimap_sum_eval (ℓ : label) (f1 f2 : val) (v1 v2 : val) : *)
(*     nsteps step_not_error 5 *)
(*       (App ℓ (of_val $ bimap_prod ℓ f1 f2) (Pair (of_val v1) (of_val v2))) *)
(*       (Pair (AppAn (of_val f1) (of_val v1)) (AppAn (of_val f2) $ (of_val v2))). *)
