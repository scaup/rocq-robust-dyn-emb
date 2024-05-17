From main.grad_lang Require Import types.
From main.dyn_lang Require Import definition lib casts tactics.
From main.prelude Require Import imports labels autosubst.

From main.logrel Require Import definition.
From main.logrel.lib Require Import rfn weakestpre small_helpers.
From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.


Section casts_compat.

  Context {ν : label} {Hν : NeverOccurs ν}.

  (* Ltac rfn_faulty := (iApply rfn_faulty; [ by faulty_solver| by faulty_solver| auto ]). *)

  Lemma compat_cast_upwards_val L ℓ ℓ' (HL : L ℓ ℓ') (τ : type) :
    ⊢ ∀ (dir : direction), match dir with
      | Normal =>
          (∀ v v', valrel_typed τ L v v' -∗
                      exprel_typed Unknown L (AppAn (of_val $ cast_upwards ℓ τ Normal) (of_val v))
                                             (AppAn (of_val $ cast_upwards ℓ' τ Normal) (of_val v')))
      | Opposite =>
         (∀ v v', valrel_typed Unknown L v v' -∗
                     exprel_typed τ L (AppAn (of_val $ cast_upwards ℓ τ Opposite) (of_val v))
                                      (AppAn (of_val $ cast_upwards ℓ' τ Opposite) (of_val v')))
    end.
  Proof.
    iInduction τ as [ B | const | ] "IH"; iIntros (dir).
    - destruct dir; simpl; iIntros (v v') "Hvv'".
      + rfn_steps. iNext. rfn_val.
        rewrite valrel_unknown_unfold.
        destruct B; dvals v v'; auto.
      + rewrite valrel_unknown_unfold.
        destruct B; rfn_steps.
        * dvals v v'; try rfn_faulty.
          rfn_steps. rfn_val.
        * dvals v v'; try rfn_faulty.
          rfn_steps. destruct b, b0; rfn_val.
        * dvals v v'; try rfn_faulty.
          rfn_steps. rfn_val.
    - destruct const; iSpecialize ("IH1" $! dir);
        [ iSpecialize ("IH" $! (switch dir))
        | iSpecialize ("IH" $! dir)
        | iSpecialize ("IH" $! dir) ].
      + (* arrow case *)
        destruct (decide ((τ1 = Unknown) ∧ (τ2 = Unknown))) as [[-> ->] | bbb];
          [ iClear "IH"; iClear "IH1"; auto | repeat rewrite /= decide_False; auto ].
        * (* ? -> ? *)
          destruct dir; repeat rewrite /cast_upwards decide_True; auto; iIntros (v v') "#Hvv'".
          { rfn_steps. rfn_val. rewrite /arrow_rel.
            dvals v v'. rewrite valrel_unknown_unfold /=. auto. }
          { rfn_steps. rfn_val. iNext.
            iIntros (w w') "#Hww'". rfn_steps.
            rewrite (valrel_unknown_unfold _ v v').
            dvals v v'; auto; try rfn_faulty.
            rewrite /valrel_unknown_pre /arrow_rel. iNext.
            iSpecialize ("Hvv'" with "Hww'"). rfn_steps.
            rfn_bind. iApply "Hvv'". repeat iNext; iIntros (x x') "Hxx'"; rfn_steps; rfn_val. }
        * destruct dir; repeat rewrite /cast_upwards decide_False; auto; iIntros (v v') "#Hvv'".
          { asimpl. rfn_steps. rfn_val.
            rewrite (valrel_unknown_unfold) /=. repeat iNext.
            iIntros (w w') "#Hww'". asimpl. rfn_bind_pp. by iApply "IH".
            iIntros (x x') "#Hxx'". dvals v v'; try rfn_faulty.
            rfn_steps. iSpecialize ("Hvv'" with "Hxx'"). iNext. rfn_bind. by iApply "Hvv'". iApply "IH1". }
          { rfn_steps. rfn_val. rewrite (valrel_unknown_unfold) /=. iNext.
            iIntros (w w') "#Hww'". asimpl. rfn_bind_pp. iApply ("IH" with "Hww'").
            iIntros (x x') "#Hxx'". dvals v v'; try rfn_faulty.
            rfn_steps. iNext. iSpecialize ("Hvv'" with "Hxx'"). rfn_bind. by iApply "Hvv'". iApply "IH1". }
      + (* sum case *)
        destruct (decide ((τ1 = Unknown) ∧ (τ2 = Unknown))) as [[-> ->] | bbb];
          [ repeat rewrite /= decide_True; auto | repeat rewrite /= decide_False; auto ].
        * (* ? -> ? *)
          destruct dir; iIntros (v v') "Hvv'"; simpl.
          { rfn_steps. rfn_val. dvals v v';
            by rewrite valrel_unknown_unfold. }
          { rfn_steps. rewrite valrel_unknown_unfold.
            dvals v v'; (try rfn_faulty); rfn_steps; rfn_val. }
        * (* τ1 -> τ2 *)
          destruct dir; iIntros (v v') "#Hvv'"; simpl.
          { rfn_steps. dvals v v'; rfn_steps; repeat iNext.
            - rfn_bind_pp. by iApply "IH". iIntros (w w') "Hww'".
              rfn_val. rewrite valrel_unknown_unfold. by iNext.
            - rfn_bind_pp. by iApply "IH1". iIntros (w w') "Hww'".
              rfn_val. rewrite valrel_unknown_unfold. by iNext. }
          { rfn_steps. rewrite valrel_unknown_unfold. dvals v v'; try rfn_faulty; rfn_steps; repeat iNext.
            - rfn_bind_pp. by iApply "IH". iIntros (w w') "Hww'". rfn_val.
            - rfn_bind_pp. by iApply "IH1". iIntros (w w') "Hww'". rfn_val. }
      + (* prodcut case *)
        destruct (decide ((τ1 = Unknown) ∧ (τ2 = Unknown))) as [[-> ->] | bbb];
          [ repeat rewrite /= decide_True; auto | repeat rewrite /= decide_False; auto ].
        * (* ? × ? *)
          destruct dir; iIntros (v v') "Hvv'"; simpl.
          { rfn_steps. rfn_val. dvals v v'. iDestruct "Hvv'" as "[a b]".
            rewrite (valrel_unknown_unfold _ (PairV _ _)). iNext. iFrame. }
          { rfn_steps. rewrite valrel_unknown_unfold. dvals v v'; try rfn_faulty.
            rfn_steps. rfn_val. }
        * destruct dir; iIntros (v v') "#Hvv'"; simpl.
          { rfn_steps. dvals v v'; try rfn_faulty. rfn_steps. iDestruct "Hvv'" as "[a b]".
            rfn_bind_pp. by iApply "IH". repeat iNext. simpl. iIntros (v v') "Hvv'".
            rfn_bind_pp. by iApply "IH1". simpl. iIntros (w w') "Hww'". rfn_val.
            iApply valrel_unknown_unfold. simpl. iSplit; iNext; iFrame. }
          { rfn_steps. rewrite valrel_unknown_unfold. dvals v v'; try rfn_faulty. rfn_steps.
            iDestruct "Hvv'" as "[a b]". repeat iNext.
            rfn_bind_pp. by iApply "IH". iIntros (v v') "Hvv'".
            rfn_bind_pp. by iApply "IH1". simpl. iIntros (w w') "Hww'". rfn_val. iFrame. }
    - destruct dir; iIntros (v v') "Hvv'"; rfn_steps; rfn_val.
  Qed.

  Lemma compat_cast_val (τ τ' : type) (H : consistency τ τ') L ℓ ℓ' (HL : L ℓ ℓ')  :
    ⊢ ∀ (dir : direction), match dir with
      | Normal =>
          (∀ v v', valrel_typed τ L v v' -∗
                      exprel_typed τ' L (AppAn (of_val $ cast_pre ℓ τ τ' H Normal) (of_val v))
                                        (AppAn (of_val $ cast_pre ℓ' τ τ' H Normal) (of_val v')))
      | Opposite =>
         (∀ v v', valrel_typed τ' L v v' -∗
                     exprel_typed τ L (AppAn (of_val $ cast_pre ℓ τ τ' H Opposite) (of_val v))
                                      (AppAn (of_val $ cast_pre ℓ' τ τ' H Opposite) (of_val v')))
    end.
  Proof.
    iInduction H as [ τ | τ | B | bin τ1 τ1' τ2 τ2' H1 H2 ] "IH"; iIntros (dir).
    - by iApply compat_cast_upwards_val.
    - destruct dir.
      + iApply (compat_cast_upwards_val _ _ _ HL τ $! Opposite).
      + iApply (compat_cast_upwards_val _ _ _ HL τ $! Normal).
    - destruct dir; iIntros (v v') "Hvv'"; rfn_steps;
        destruct B; dvals v v'; rfn_val.
    - destruct bin; iSpecialize ("IH1" $! dir);
        [ iSpecialize ("IH" $! (switch dir))
        | iSpecialize ("IH" $! dir)
        | iSpecialize ("IH" $! dir) ].
      + destruct dir; rewrite /switch; iIntros (v v') "#Hvv'".
        * rfn_steps. rfn_val. iNext. iIntros (w w') "#Hww'". asimpl.
          rfn_bind_pp. by iApply "IH". iIntros (x x') "#Hxx'". dvals v v'. rfn_steps.
          iSpecialize ("Hvv'" with "Hxx'"). iNext. rfn_bind. by iApply "Hvv'". iApply "IH1".
        * rfn_steps. rfn_val. iNext. iIntros (w w') "#Hww'". asimpl.
          rfn_bind_pp. by iApply "IH". iIntros (x x') "#Hxx'". dvals v v'. rfn_steps.
          iSpecialize ("Hvv'" with "Hxx'"). iNext. rfn_bind. by iApply "Hvv'". iApply "IH1".
      + destruct dir; rewrite /switch; iIntros (v v') "#Hvv'".
        * rfn_steps. dvals v v'; try rfn_faulty; rfn_steps.
          { rfn_bind_pp. by iApply "IH". do 2 iNext. iIntros (w w') "Hww'". rfn_val. }
          { rfn_bind_pp. by iApply "IH1". do 2 iNext. iIntros (w w') "Hww'". rfn_val. }
        * rfn_steps. dvals v v'; try rfn_faulty; rfn_steps.
          { rfn_bind_pp. by iApply "IH". do 2 iNext. iIntros (w w') "Hww'". rfn_val. }
          { rfn_bind_pp. by iApply "IH1". do 2 iNext. iIntros (w w') "Hww'". rfn_val. }
      + destruct dir; rewrite /switch; iIntros (v v') "#Hvv'";
          dvals v v'; rfn_steps.
        * iDestruct "Hvv'" as "[a b]".
          rfn_bind_pp. by iApply "IH".
          repeat iNext. iIntros (w w') "Hww'".
          rfn_bind_pp. by iApply "IH1".
          iIntros (x x') "Hxx'". rfn_val. iFrame.
        * iDestruct "Hvv'" as "[a b]".
          rfn_bind_pp. by iApply "IH".
          repeat iNext. iIntros (w w') "Hww'".
          rfn_bind_pp. by iApply "IH1".
          iIntros (x x') "Hxx'". rfn_val. iFrame.
  Qed.

  Lemma compat_cast (τ τ' : type) (H : consistency τ τ') L ℓ ℓ' (HL : L ℓ ℓ') :
    ⊢ (∀ e e', exprel_typed τ L e e' -∗
                      exprel_typed τ' L (AppAn (of_val $ cast ℓ τ τ' H) e)
                                        (AppAn (of_val $ cast ℓ' τ τ' H) e')).
  Proof.
    iIntros (e e') "#Hee'". rfn_bind; auto.
    by iDestruct (compat_cast_val _ _ H _ _ _ HL $! Normal) as "H".
  Qed.

End casts_compat.
