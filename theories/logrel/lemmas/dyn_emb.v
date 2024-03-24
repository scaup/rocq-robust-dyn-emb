From main.prelude Require Import imports autosubst big_op_three.
From main.surf_lang Require Import types.
From main.dyn_lang Require Import definition lemmas.
From main.logrel.lib Require Import weakestpre rfn.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

From main.logrel Require Import definition.
From main.maps Require Import dyn_to_surf.definition surf_to_dyn.definition.

Section fundamental_bare_rfn_demb.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Definition Δ (e : expr) : label -d> label -d> siProp.
  Admitted.

  Lemma cast_closed ℓ τ1 τ2 : Closed (of_val $ cast ℓ τ1 τ2).
  Proof.


  Lemma emb_subst (e : expr) σ : ⌊ (⌜⌜ e ⌝⌝) ⌋.[σ] = ⌊ (⌜⌜ e.[σ] ⌝⌝) ⌋.
  Proof.
    induction e.
    - rewrite 1 /dyn_emb. simpl.

    (asimpl; naive_solver). try by naive_solver.

  Lemma fundamental_bare_rfn_demb (e : expr) n (Hne : Closed_n n e) :
    open_exprel_typed (replicate n Unknown) e  (⌊ (⌜⌜ e ⌝⌝) ⌋) (Δ e) Unknown.
  Proof.
    generalize dependent n.
    iInduction e as
      [ (* Lit *) b | (* Seq *) ℓ e1 e2 | (*If*) ℓ e0 e1 e2
      | (* BinOp *) ℓ binop e1 e2 | (* Var *) v | (* Lam *) e
      | (* App *) ℓ e1 e2 | (* InjL *) e | (* InjR *) e
      | (* Case *) ℓ e e1 e2 | (* Fst *) ℓ e | (* Snd *) ℓ e
      | (* Pair *) e1 e2 | (* Error *) ℓ] "IH";
      iIntros (n Hn P vs vs') "[%Hlp Hvsvs']".
    - admit.
    - asimpl. admit.
    - asimpl. iSpecialize ("IH" $! n ).
      (* specialize with P, *)
      (* proof obligation for using "IH"; less_possibilities_then (Δ e0) P *)
      (* should be easy; we have Δ e0 ≤ Δ (If ℓ e0 e2 e3) *)

      (* ℓ toegelaten, *)
      (* (If ℓ e0 e1 e2) (If ν (cast ℓ B e0') e1' e2') *)

      admit.


    - admit.
    - asimpl. admit.
    - (* Lam *)
      (* simpl. *)
      (* just prove that the two lambdas are in the value relation for unknown *)
      (* ok, so to prove : ▷ (∀ w, w'. unknown P w w' -∗ \x.e w \x.e w'   ) *)
      (* forget about later... *)
      (* yeah, we can use "IH" with extended list and P... *)

      (* --------- correction *)
      (* this would now be ∃ e, e', v = λe, v'=λe' ∗ ▷ (∀ w w'...)  *)
      admit.
    - (* app *)
      (* exprel_untyped P e1 e1' -∗ *)
      (* exprel_untyped P e2 e2' -∗ *)
      (* exprel_untyped P (App ℓ e1 e2) (AppAn (e1' : (?=>?→?)ℓ) e2') *)

      (* one bind *)
      (* valrel_untyped P v1 v1' -∗ *)
      (* exprel_untyped P e2 e2' -∗ *)
      (* exprel_untyped P (App ℓ v1 e2) (AppAn (v1' : (?=>?→?)ℓ) e2') *)

      (* just a step *)
      (* valrel_untyped P v1 v1' -∗ *)
      (* exprel_untyped P e2 e2' -∗ *)
      (* exprel_untyped P (App ℓ v1 e2) (AppAn (λx. App ℓ v1' x) e2') *)

      (* second bind *)
      (* valrel_untyped P v1 v1' -∗ *)
      (* valrel_untyped P v2 v2' -∗ *)
      (* exprel_untyped P (App ℓ v1 v2) (App ℓ v1' v2') *)

      (* Can we do this? *)

      (* case analyis on v1 v1'; *)
      (*   in all the different branches but the arrow branch, we get (on left and right!) stuckness on ℓ *)
      (*      succes! becasuse ℓ is in P *)
      (*   in the arrow branch, we have (▷ ∀ w w', ....) *)
      (*      we have to adjust definition I think... *)
      (*      suppose this as its definition : (∃ e, e', v = λe, v'=λe' ∗ ▷ (∀ w w'. Rww' -> E (e.[v/]) (e'.[v/]) ...) ) *)
      (*      then we can take a step (both sides); and get what we need *)



      admit.




    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.




    (* open_exprel_typed (replicate n (valrel_unknown (Δ e))) e  (⌊ ⌜⌜ e ⌝⌝ ⌋) Unknown. *)
