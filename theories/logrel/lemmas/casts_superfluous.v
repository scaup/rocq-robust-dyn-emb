From main.surf_lang Require Import types.
From main.dyn_lang Require Import definition lib casts tactics lemmas.
From main.prelude Require Import imports labels autosubst.

From main.logrel Require Import definition.
From main.logrel.lib Require Import rfn weakestpre wrappers.
From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

Section casts_superfluous.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma cast_upwards_val_superfluous_r (τ : type) L :
    ⊢ ∀ (dir : direction),
       (∀ v v', valrel_typed τ L v v' -∗
                exprel_typed τ L (of_val v)
                                 (AppAn (of_val $ cast_upwards ν τ dir) (of_val v'))).
  Proof.
    iInduction τ as [ B | const | asdf] "IH";
      iIntros (dir); iIntros (v v') "#Hvv'"; rfn_steps.
    - destruct B, dir; rfn_steps; (try by rfn_val).
      * dvals v v'; rfn_steps; rfn_val.
      * dvals v v'; rfn_steps. destruct b, b0; rfn_val.
      * dvals v v'; rfn_steps; rfn_val.
    - destruct (decide ((τ1 = Unknown) ∧ (τ2 = Unknown))) as [[-> ->] | bbb];
        [ iClear "IH"; iClear "IH1"; repeat rewrite /= decide_True; auto; (destruct dir; [ rfn_steps; rfn_val |  ])
        | repeat rewrite /= decide_False; auto ].
      + (* working with a ground type *)
        destruct const.
        * dvals v v'. rfn_steps. rfn_val. iIntros (w w') "#Hww'". rfn_steps.
          asimpl. iSpecialize ("Hvv'" with "Hww'"). rw_fill. iApply (rfn_bind' [] _). by iApply "Hvv'".
          iIntros (x x') "Hxx'". rfn_steps. rfn_val.
        * dvals v v'; rfn_steps; rfn_val.
        * dvals v v'. rfn_steps. rfn_val.
      + (* *)
        destruct const; [ iSpecialize ("IH" $! (switch dir)); iSpecialize ("IH1" $! dir)
                      | iSpecialize ("IH" $! dir); iSpecialize ("IH1" $! dir)
                      | iSpecialize ("IH" $! dir); iSpecialize ("IH1" $! dir) ].
        * dvals v v'. destruct dir; asimpl.
          { rfn_steps. rfn_val. iIntros (w w') "#Hww'". rfn_steps.
            iSpecialize ("IH" with "Hww'"). iDestruct (rfn_val_l_inv with "IH") as (w'') "[%Hs Hww'']".
            iApply rfn_steps_r.
            { rw_fill_popped. eapply rtc_congruence. intros; eapply fill_step; eauto. apply Hs. }
            rfn_steps.
            rw_fill. iApply (rfn_bind' [] _). by iApply "Hvv'".
            iIntros (x x') "Hxx'". by iApply "IH1". }
          { rfn_steps. rfn_val. iIntros (w w') "#Hww'". rfn_steps.
            iSpecialize ("IH" with "Hww'"). iDestruct (rfn_val_l_inv with "IH") as (w'') "[%Hs Hww'']".
            iApply rfn_steps_r.
            { rw_fill_popped. eapply rtc_congruence. intros; eapply fill_step; eauto. apply Hs. }
            rfn_steps.
            rw_fill. iApply (rfn_bind' [] _). by iApply "Hvv'".
            iIntros (x x') "Hxx'". by iApply "IH1". }
       * dvals v v'.
          { destruct dir; rfn_steps.
            - rw_fill. iApply (rfn_bind' [InjLCtx] _ [InjLCtx]).
              by iApply "IH". iIntros (w w') "Hww'". simpl. rfn_val.
            - rw_fill. iApply (rfn_bind' [InjLCtx] _ [InjLCtx]).
              by iApply "IH". iIntros (w w') "Hww'". simpl. rfn_val. }
          { destruct dir; rfn_steps.
            - rw_fill. iApply (rfn_bind' [InjRCtx] _ [InjRCtx]).
              by iApply "IH1". iIntros (w w') "Hww'". simpl. rfn_val.
            - rw_fill. iApply (rfn_bind' [InjRCtx] _ [InjRCtx]).
              by iApply "IH1". iIntros (w w') "Hww'". simpl. rfn_val. }
        * dvals v v'. iDestruct "Hvv'" as "[a b]"; destruct dir; rfn_steps.
          { iApply (rfn_bind' [PairLCtx _] _ [PairLCtx _]). by iApply "IH". repeat iNext.
            iIntros (w w') "Hww'". iApply (rfn_bind' [PairRCtx _] _ [PairRCtx _]). by iApply "IH1".
            iIntros (x x') "Hxx'". simpl. rfn_val. iFrame. }
          { iApply (rfn_bind' [PairLCtx _] _ [PairLCtx _]). by iApply "IH". repeat iNext.
            iIntros (w w') "Hww'". iApply (rfn_bind' [PairRCtx _] _ [PairRCtx _]). by iApply "IH1".
            iIntros (x x') "Hxx'". simpl. rfn_val. iFrame. }
    - by rfn_val.
  Qed.

  Lemma cast_upwards_val_superfluous_l (τ : type) L :
    ⊢ ∀ (dir : direction),
       (∀ v v', valrel_typed τ L v v' -∗
                exprel_typed τ L (AppAn (of_val $ cast_upwards ν τ dir) (of_val v))
                                 (of_val v')).
  Proof.
    iInduction τ as [ B | const | asdf] "IH";
      iIntros (dir); iIntros (v v') "#Hvv'"; rfn_steps.
    - destruct B, dir; rfn_steps; (try by rfn_val).
      * dvals v v'; rfn_steps; rfn_val.
      * dvals v v'; rfn_steps. destruct b, b0; rfn_val.
      * dvals v v'; rfn_steps; rfn_val.
    - destruct (decide ((τ1 = Unknown) ∧ (τ2 = Unknown))) as [[-> ->] | bbb];
        [ iClear "IH"; iClear "IH1"; repeat rewrite /= decide_True; auto; (destruct dir; [ rfn_steps; rfn_val |  ])
        | repeat rewrite /= decide_False; auto ].
      + (* working with a ground type *)
        destruct const.
        * dvals v v'. rfn_steps. rfn_val. asimpl. iNext. iIntros (w w') "#Hww'". rfn_steps.
          iSpecialize ("Hvv'" with "Hww'"). iNext. rw_fill. iApply (rfn_bind' [AppRCtx _ _] _ []).
          by iApply "Hvv'". repeat iNext. iIntros (x x') "Hxx'". rfn_steps. rfn_val.
        * dvals v v'; rfn_steps; rfn_val.
        * dvals v v'. rfn_steps. rfn_val.
      + (* *)
        destruct const; [ iSpecialize ("IH" $! (switch dir)); iSpecialize ("IH1" $! dir)
                      | iSpecialize ("IH" $! dir); iSpecialize ("IH1" $! dir)
                      | iSpecialize ("IH" $! dir); iSpecialize ("IH1" $! dir) ].
        * dvals v v'. destruct dir; rfn_l_s; simpl; iNext; rfn_val; iIntros (w w') "#Hww'"; iApply (rfn_r_lam_app_rw ν).
          { asimpl. rw_fill. iApply (rfn_bind' [ AppRCtx _  _ ; _ ] _ [ _ ]). by iApply "IH". iIntros (x x') "#Hxx'". rfn_steps.
            iSpecialize ("Hvv'" with "Hxx'"). iNext. iApply (rfn_bind' [ AppRCtx _ _ ] _ []).
            by iApply "Hvv'". iApply "IH1". }
          { asimpl. rw_fill. iApply (rfn_bind' [ AppRCtx _  _ ; _ ] _ [ _ ]). by iApply "IH". iIntros (x x') "#Hxx'". rfn_steps.
            iSpecialize ("Hvv'" with "Hxx'"). iNext. iApply (rfn_bind' [ AppRCtx _ _ ] _ []).
            by iApply "Hvv'". iApply "IH1". }
        * dvals v v'.
          { destruct dir; rfn_steps.
            - rw_fill. iApply (rfn_bind' [InjLCtx] _ [InjLCtx]).
              by iApply "IH". repeat iNext. iIntros (w w') "Hww'". simpl. rfn_val.
            - rw_fill. iApply (rfn_bind' [InjLCtx] _ [InjLCtx]).
              by iApply "IH". repeat iNext. iIntros (w w') "Hww'". simpl. rfn_val. }
          { destruct dir; rfn_steps.
            - rw_fill. iApply (rfn_bind' [InjRCtx] _ [InjRCtx]).
              by iApply "IH1". repeat iNext. iIntros (w w') "Hww'". simpl. rfn_val.
            - rw_fill. iApply (rfn_bind' [InjRCtx] _ [InjRCtx]).
              by iApply "IH1". repeat iNext. iIntros (w w') "Hww'". simpl. rfn_val. }
        * dvals v v'. iDestruct "Hvv'" as "[a b]"; destruct dir; rfn_steps.
          { iApply (rfn_bind' [PairLCtx _] _ [PairLCtx _]). by iApply "IH". repeat iNext.
            iIntros (w w') "Hww'". iApply (rfn_bind' [PairRCtx _] _ [PairRCtx _]). by iApply "IH1".
            iIntros (x x') "Hxx'". simpl. rfn_val. iFrame. }
          { iApply (rfn_bind' [PairLCtx _] _ [PairLCtx _]). by iApply "IH". repeat iNext.
            iIntros (w w') "Hww'". iApply (rfn_bind' [PairRCtx _] _ [PairRCtx _]). by iApply "IH1".
            iIntros (x x') "Hxx'". simpl. rfn_val. iFrame. }
    - by rfn_val.
  Qed.

  Lemma cast_upwards_val_superfluous_lr (τ : type) L :
    ⊢ ∀ (dir : direction),
       (∀ v v', valrel_typed τ L v v' -∗
                exprel_typed τ L (AppAn (of_val $ cast_upwards ν τ dir) (of_val v))
                                 (AppAn (of_val $ cast_upwards ν τ dir) (of_val v'))).
  Proof.
    iInduction τ as [ B | const | asdf] "IH";
      iIntros (dir); iIntros (v v') "#Hvv'"; rfn_steps.
    - destruct B, dir; rfn_steps; (try by rfn_val).
      * dvals v v'; rfn_steps; rfn_val.
      * dvals v v'; rfn_steps. destruct b, b0; rfn_val.
      * dvals v v'; rfn_steps; rfn_val.
    - destruct (decide ((τ1 = Unknown) ∧ (τ2 = Unknown))) as [[-> ->] | bbb];
        [ iClear "IH"; iClear "IH1"; repeat rewrite /= decide_True; auto; (destruct dir; [ rfn_steps; rfn_val |  ])
        | repeat rewrite /= decide_False; auto ].
      + (* working with a ground type *)
        destruct const.
        * dvals v v'. rfn_steps. rfn_val. asimpl. iNext. iIntros (w w') "#Hww'". rfn_steps.
          iSpecialize ("Hvv'" with "Hww'"). iNext. rfn_bind'. by iApply "Hvv'". repeat iNext.
          iIntros (x x') "Hxx'". rfn_steps. rfn_val.
        * dvals v v'; rfn_steps; rfn_val.
        * dvals v v'. rfn_steps. rfn_val.
      + (* *)
        destruct const; [ iSpecialize ("IH" $! (switch dir)); iSpecialize ("IH1" $! dir)
                      | iSpecialize ("IH" $! dir); iSpecialize ("IH1" $! dir)
                      | iSpecialize ("IH" $! dir); iSpecialize ("IH1" $! dir) ].
        * dvals v v'. destruct dir; rfn_steps; rfn_val; iNext; iIntros (w w') "#Hww'"; rfn_steps.
          { rfn_bind_pop'. by iApply "IH". iIntros (x x') "#Hxx'". rfn_steps.
            iSpecialize ("Hvv'" with "Hxx'"). iNext.
            rfn_bind'. by iApply "Hvv'". iApply "IH1". }
          { rfn_bind_pop'. by iApply "IH". iIntros (x x') "#Hxx'". rfn_steps.
            iSpecialize ("Hvv'" with "Hxx'"). iNext.
            rfn_bind'. by iApply "Hvv'". iApply "IH1". }
        * dvals v v'.
          { destruct dir; rfn_steps.
            rfn_bind_pop'. by iApply "IH". do 2 iNext. iIntros (w w') "Hww'". rfn_val.
            rfn_bind_pop'. by iApply "IH". do 2 iNext. iIntros (w w') "Hww'". rfn_val. }
          { destruct dir; rfn_steps.
            rfn_bind_pop'. by iApply "IH1". do 2 iNext. iIntros (w w') "Hww'". rfn_val.
            rfn_bind_pop'. by iApply "IH1". do 2 iNext. iIntros (w w') "Hww'". rfn_val. }
        * dvals v v'. iDestruct "Hvv'" as "[a b]"; destruct dir; rfn_steps.
          { rfn_bind_pop'. by iApply "IH". repeat iNext.
            iIntros (w w') "Hww'". rfn_bind_pop'. by iApply "IH1".
            iIntros (x x') "Hxx'". rfn_val. iFrame. }
          { rfn_bind_pop'. by iApply "IH". repeat iNext.
            iIntros (w w') "Hww'". rfn_bind_pop'. by iApply "IH1".
            iIntros (x x') "Hxx'". rfn_val. iFrame. }
    - iNext. rfn_val.
  Qed.

  Lemma cast_upwards_superfluous_r (τ : type) L :
    ⊢ ∀ (dir : direction),
       (∀ e e', exprel_typed τ L e e' -∗
                exprel_typed τ L e
                                 (AppAn (of_val $ cast_upwards ν τ dir) e')).
  Proof.
    iIntros (dir e e') "Hee'".
    iApply (rfn_bind' [] _ [AppRCtx _ _] with "Hee'"). iApply cast_upwards_val_superfluous_r.
  Qed.

  Lemma cast_upwards_superfluous_l (τ : type) L :
    ⊢ ∀ (dir : direction),
       (∀ e e', exprel_typed τ L e e' -∗
                exprel_typed τ L (AppAn (of_val $ cast_upwards ν τ dir) e) e').
  Proof.
    iIntros (dir e e') "Hee'".
    iApply (rfn_bind' [AppRCtx _ _] _ [] with "Hee'"). iApply cast_upwards_val_superfluous_l.
  Qed.

  Lemma cast_upwards_superfluous_lr (τ : type) L :
    ⊢ ∀ (dir : direction),
       (∀ e e', exprel_typed τ L e e' -∗
                exprel_typed τ L (AppAn (of_val $ cast_upwards ν τ dir) e) (AppAn (of_val $ cast_upwards ν τ dir) e')).
  Proof.
    iIntros (dir e e') "Hee'".
    iApply (rfn_bind' [AppRCtx _ _] _ [AppRCtx _ _] with "Hee'"). iApply cast_upwards_val_superfluous_lr.
  Qed.

End casts_superfluous.
