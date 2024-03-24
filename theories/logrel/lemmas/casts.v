From main.surf_lang Require Import types.
From main.dyn_lang Require Import definition lib casts.
From main.prelude Require Import imports labels autosubst.

From main.logrel Require Import definition lib.trivialities rfn.
From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

Section casts.

  Context {ν : label} {Hν : NeverOccurs ν}.

  (* Definition app_funs_transforms (Φ1 Φ2 : val -d> val -d> siProp) (L2 : label -d> label -d> siProp) (f f' : val) : siProp := *)
  (*   ∀ (v v' : val), Φ1 v v' -∗ rfn Φ2 L2 (AppAn (of_val f) (of_val v)) (AppAn (of_val f') (of_val v')). *)

  (* Lemma compat_cast_upwards L ℓ ℓ' (Hp : ⊢ L ℓ ℓ') (τ : type) : *)
  (*   ⊢ ∀ (dir : direction),  *)
  (*      match dir with *)
  (*     | Normal => *)
  (*         app_funs_transforms *)
  (*               (valrel_typed τ L) (valrel_unknown L) L *)
  (*               (cast_upwards ℓ τ Normal) (cast_upwards ℓ' τ Normal) *)
  (*     | Opposite => *)
  (*         app_funs_transforms *)
  (*               (valrel_unknown L) (valrel_typed τ L) L *)
  (*               (cast_upwards ℓ τ Opposite) (cast_upwards ℓ' τ Opposite) *)
  (*   end. *)
  (* Proof. *)
  (*   iInduction τ as [ B | const | asdf] "IH"; iIntros (dir). *)
  (*   - admit. *)
  (*   - destruct const; [ iSpecialize ("IH" $! (switch dir)); iSpecialize ("IH1" $! dir) *)
  (*                     | iSpecialize ("IH" $! dir); iSpecialize ("IH1" $! dir) *)
  (*                     | iSpecialize ("IH" $! dir); iSpecialize ("IH1" $! dir) ]. *)
  (*     + (* arrow case *) *)
  (*       destruct (decide ((τ1 = Unknown) ∧ (τ2 = Unknown))) as [[-> ->] | bbb]; *)
  (*         [ iClear "IH"; iClear "IH1"; auto |  ]. *)
  (*       * admit. *)
  (*       * admit. *)


  (*       destruct dir. *)
  (*       * (* ? → ? => ? *) simpl. *)


  (*   -  *)




  Ltac naive_step_solver := apply (SNE_Normal []); econstructor; by rewrite to_of_val.

  Lemma superfluous_cast_upwards (τ : type) L :
    ⊢ ∀ (dir : direction),
       (∀ e e', exprel_typed τ L e e' -∗
                exprel_typed τ L (AppAn (of_val $ cast_upwards ν τ dir) e)
                                 (AppAn (of_val $ cast_upwards ν τ dir) e')).
  Proof.
    iInduction τ as [ B | const | asdf] "IH"; iIntros (dir); iIntros (e e') "Hee'".
    - change (AppAn (of_val ?v) ?e) with (fill [ AppRCtx ν v ] e).
      iApply (rfn_bind' with "Hee'").
      iIntros (v v') "Hvv'".
      destruct dir.
      + destruct B; iApply rfn_id_lr; by iApply rfn_val.
      + destruct B.
        * iApply rfn_s_l. naive_step_solver. iApply rfn_s_r. naive_step_solver. simpl.
          iDestruct "Hvv'" as "[-> ->]".
          iApply rfn_s_l. naive_step_solver. iApply rfn_s_r. naive_step_solver. simpl.
          iApply (rfn_val (LitV LitUnit) (LitV LitUnit)); eauto.
        * iApply rfn_s_l. naive_step_solver. iApply rfn_s_r. naive_step_solver. simpl.
          iDestruct "Hvv'" as (b) "[-> ->]".
          iApply rfn_s_l. naive_step_solver. iApply rfn_s_r. naive_step_solver. simpl.
          iApply (rfn_val (LitV $ LitBool b) (LitV $ LitBool b)); destruct b; simpl; eauto.
        * iApply rfn_s_l. naive_step_solver. iApply rfn_s_r. naive_step_solver. simpl.
          iDestruct "Hvv'" as (z) "[-> ->]".
          iApply rfn_s_l. naive_step_solver. iApply rfn_s_r. naive_step_solver. simpl.
          iApply (rfn_val (LitV $ LitInt z) (LitV $ LitInt z)); simpl; eauto.
    - change (AppAn (of_val ?v) ?e) with (fill [ AppRCtx ν v ] e).
      iApply (rfn_bind' with "Hee'"). clear e e'.
      destruct (decide ((τ1 = Unknown) ∧ (τ2 = Unknown))) as [[-> ->] | bbb];
        [ iClear "IH"; iClear "IH1"; repeat rewrite /= decide_True; auto;
          (destruct dir; [ iIntros (v v') "Hvv'"; iApply rfn_id_lr ; by iApply rfn_val | ])

        |
          repeat rewrite /= decide_False; auto ].
      + (* working with a ground type *)
        destruct const; iIntros (v v') "Hvv'".
        * iDestruct "Hvv'" as (e e') "(-> & -> & H)".
          admit.
        * admit.
        * admit.
      + (* *)
        destruct const; [ iSpecialize ("IH" $! (switch dir)); iSpecialize ("IH1" $! dir)
                      | iSpecialize ("IH" $! dir); iSpecialize ("IH1" $! dir)
                      | iSpecialize ("IH" $! dir); iSpecialize ("IH1" $! dir) ].
        * admit.
        * admit.
        * destruct dir.


        admit.
  Admitted.

  Lemma compat_cast_upwards L ℓ ℓ' (Hp : ⊢ L ℓ ℓ') (τ : type) :
    ⊢ ∀ (dir : direction), match dir with
      | Normal =>
          (∀ e e', exprel_typed τ L e e' -∗
                      exprel_typed Unknown L (AppAn (of_val $ cast_upwards ℓ τ Normal) e)
                                             (AppAn (of_val $ cast_upwards ℓ' τ Normal) e'))
      | Opposite =>
         (∀ e e', exprel_typed Unknown L e e' -∗
                     exprel_typed τ L (AppAn (of_val $ cast_upwards ℓ τ Opposite) e)
                                      (AppAn (of_val $ cast_upwards ℓ' τ Opposite) e'))
    end.
  Proof.
    iInduction τ as [ B | const | asdf] "IH"; iIntros (dir).
    - admit.
    - destruct const; [ iSpecialize ("IH" $! (switch dir)); iSpecialize ("IH1" $! dir)
                      | iSpecialize ("IH" $! dir); iSpecialize ("IH1" $! dir)
                      | iSpecialize ("IH" $! dir); iSpecialize ("IH1" $! dir) ].
      + (* arrow case *)
        destruct (decide ((τ1 = Unknown) ∧ (τ2 = Unknown))) as [[-> ->] | bbb];
          [ iClear "IH"; iClear "IH1"; auto | repeat rewrite /= decide_False; auto ].
        * (* ? -> ? *)
          destruct dir; repeat rewrite /cast_upwards decide_True; auto; iIntros (e e') "Hee'".
          { simpl. iApply rfn_id_lr. iApply (rfn_impl with "Hee'"); auto.
            iIntros (v v') "Hvv'". repeat rewrite /valrel_typed.
            iDestruct "Hvv'" as (t t') "(-> & -> & H)".
            rewrite valrel_unknown_unfold. iExists (S_Bin Arrow).
            rewrite /arrow_rel. iExists _, _. do 2 (iSplit; first eauto). auto. }
          { change (AppAn (of_val ?v) ?e) with (fill [ AppRCtx ν v ] e).
            iApply (rfn_bind' with "Hee'"). iIntros (v v') "Hvv'".
            admit.
          }
        * (* τ1 -> τ2 *)
          destruct dir; iIntros (e e') "Hee'".
          { admit. }
          { admit. }
      + (* arrow case *)
        destruct (decide ((τ1 = Unknown) ∧ (τ2 = Unknown))) as [[-> ->] | bbb]; [ repeat rewrite /= decide_True; auto | repeat rewrite /= decide_False; auto ].
        * (* ? -> ? *)
          destruct dir; iIntros (e e') "Hee'"; simpl.
          { admit. }
          { admit. }
        * (* τ1 -> τ2 *)
          destruct dir; iIntros (e e') "Hee'"; simpl.
          { admit. }
          { admit. }
      + (* arrow case *)
        destruct (decide ((τ1 = Unknown) ∧ (τ2 = Unknown))) as [[-> ->] | bbb]; [ repeat rewrite /= decide_True; auto | repeat rewrite /= decide_False; auto ].
        * (* ? -> ? *)
          destruct dir; iIntros (e e') "Hee'"; simpl.
          { admit. }
          { admit. }
        * (* τ1 -> τ2 *)
          destruct dir; iIntros (e e') "Hee'"; simpl.
          { admit. }
          { admit. }
    - (* unknown case *) simpl. destruct dir.
      + admit.
      + admit.
  Admitted.

  Lemma compat_cast (τ τ' : type) (H : consistency τ τ') L ℓ ℓ' (Hp : ⊢ L ℓ ℓ') :
    ⊢ ∀ (dir : direction), match dir with
      | Normal =>
          (∀ e e', exprel_typed τ L e e' -∗
                      exprel_typed τ' L (AppAn (of_val $ cast_pre ℓ τ τ' H Normal) e)
                                        (AppAn (of_val $ cast_pre ℓ' τ τ' H Normal) e'))
      | Opposite =>
         (∀ e e', exprel_typed τ' L e e' -∗
                     exprel_typed τ L (AppAn (of_val $ cast_pre ℓ τ τ' H Opposite) e)
                                      (AppAn (of_val $ cast_pre ℓ' τ τ' H Opposite) e'))
    end.
  Proof.
    iInduction H as [ τ | τ | B | bin τ1 τ1' τ2 τ2' H1 H2 ] "IH"; iIntros (dir).
    - by iApply compat_cast_upwards.
    - destruct dir.
      + iApply (compat_cast_upwards _ _ _ Hp τ $! Opposite).
      + iApply (compat_cast_upwards _ _ _ Hp τ $! Normal).
    - simpl. admit.
    - destruct bin; iSpecialize ("IH1" $! dir);
        [ iSpecialize ("IH" $! (switch dir))
        | iSpecialize ("IH" $! dir)
        | iSpecialize ("IH" $! dir) ].
      + destruct dir; rewrite /switch; iIntros (e e') "Hee'".
        * admit.
        * admit.
      + destruct dir; rewrite /switch; iIntros (e e') "Hee'".
        * admit.
        * admit.
      + destruct dir; rewrite /switch; iIntros (e e') "Hee'".
        * admit.
        * admit.
  Admitted.

End casts.
