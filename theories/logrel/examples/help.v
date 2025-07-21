From main.prelude Require Import imports autosubst big_op_three.
From main.cast_calc Require Import types.
From main.dyn_lang Require Import definition lemmas lib labels tactics.
From main.logrel.lib Require Import weakestpre rfn small_helpers.
From main.logrel Require Import definition.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

Lemma subst_val_val e v (H : is_Some (to_val e.[of_val v/])) :
  ∀ w, is_Some (to_val e.[of_val w/]).
Proof.
  revert v H.
  induction e; intros a H w; asimpl; (try by inversion H); (try by (eexists; eauto)).
  - destruct v; [asimpl; rewrite to_of_val; eauto | asimpl in H; simpl in H; auto].
  - rewrite fmap_is_Some in H. destruct (IHe _ H w) as [b eq].
    by simplify_option_eq.
  - rewrite fmap_is_Some in H. destruct (IHe _ H w) as [b eq].
    by simplify_option_eq.
  - inversion H. simplify_option_eq.
    edestruct (IHe1 a ltac:(eauto) w) as [b1 eq1].
    edestruct (IHe2 a ltac:(eauto) w) as [b2 eq2].
    simplify_option_eq. eauto.
Qed.

Section help.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Context (Omega : expr).
  Context (Omega_closed : Closed Omega).
  Context (Omega_step : step_ne Omega Omega).

  Lemma Omega_not_val : to_val Omega = None.
  Proof. by eapply step_no_val. Qed.

  Lemma subst_val_val' e a (H : (to_val e.[Lam Omega/] = Some a)) :
    ∀ w, is_Some (to_val e.[of_val w/]).
  Proof. eapply subst_val_val. change (Lam ?e) with (of_val (LamV e)) in H. by eexists. Qed.

  Lemma help_invariant (e t : expr) (Hs : step_ne e.[Lam Omega/] t) :
    (∃ K , t = fill K Omega) ∨ (∃ e', ∀ (v : val), step_ne e.[of_val v/] e'.[of_val v/]).
  Proof.
    generalize dependent t.
    induction e; intros t Hs; simpl in Hs; simpl.
    - assert (abs := step_no_val _ _ Hs). inversion abs.
    - inversion Hs.
      destruct K as [|Ki K]; simpl in *; simplify_eq.
      + clear Hs.
        inversion HS; simpl in *; simplify_eq. clear IHe1 IHe2.
        destruct e1; (try by inversion H1); [destruct b; inversion H1| by destruct v; asimpl in H1; inversion H1].
        right. exists e2. intros v. step_solver.
      + destruct Ki; simpl in H0; try by inversion H0.
        inversion H0. simplify_eq.
        assert (Hs1 : step_ne e1.[Lam Omega/] (fill K e_h')).
        { rewrite -H0. by econstructor. }
        specialize (IHe1 (fill K e_h') Hs1). destruct IHe1 as [[K' eq] | [e1' He1']].
        * left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
        * right. exists (Seq ℓ e1' e2). simpl. intros v.
          rw_fill. by apply fill_step.
    - inversion Hs.
      destruct K as [|Ki K]; simpl in *; simplify_eq.
      + clear Hs.
        inversion HS; simpl in *; simplify_eq. clear IHe1 IHe2 IHe3.
        destruct e1; (try by inversion H1); [destruct b0; inversion H1; simplify_eq | by destruct v; asimpl in H1; inversion H1]. destruct b0.
        * right. exists e2. intros v. step_solver.
        * right. exists e3. intros v. step_solver.
      + destruct Ki; simpl in H0; try by inversion H0.
        inversion H0. simplify_eq.
        assert (Hs1 : step_ne e1.[Lam Omega/] (fill K e_h')).
        { rewrite -H0. by econstructor. }
        specialize (IHe1 (fill K e_h') Hs1). destruct IHe1 as [[K' eq] | [e1' He1']].
        * left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
        * right. exists (If ℓ e1' e2 e3). simpl. intros v.
          rw_fill. by apply fill_step.
    - inversion Hs.
      destruct K as [|Ki K]; simpl in *; simplify_eq.
      + clear Hs.
        inversion HS; simpl in *; simplify_eq. clear IHe1 IHe2.
        destruct e1; (inversion H2; try done); (try destruct b; inversion H2);
          (try destruct v; asimpl in H2; inversion H2).
        destruct e2; (inversion H3; try done); (try destruct b; inversion H3);
          (try destruct v; asimpl in H3; inversion H3). simplify_eq.
        asimpl. right. exists ((of_val (bin_op_eval binop n n0))). intros v.
        eapply (stepK []). econstructor. econstructor. asimpl. destruct binop; by asimpl.
      + destruct Ki; simpl in H0; try by inversion H0.
        * simpl in *. inversion H0. simplify_eq.
          (* IHe1 *)
          assert (Hs1 : step_ne e1.[Lam Omega/] (fill K e_h')).
          { rewrite -H0. by econstructor. }
          specialize (IHe1 (fill K e_h') Hs1). destruct IHe1 as [[K' eq] | [e1' He1']].
          -- left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
          -- right. exists (BinOp ℓ binop e1' e2). simpl. intros v.
              rw_fill. by apply fill_step.
        * simpl in *. inversion H0. simplify_eq.
          (* IHe2 *)
          assert (Hs2 : step_ne e2.[Lam Omega/] (fill K e_h')).
          { rewrite -H4. by econstructor. }
          specialize (IHe2 (fill K e_h') Hs2). destruct IHe2 as [[K' eq] | [e2' He2']].
          -- left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
          -- right. exists (BinOp ℓ binop e1 e2'). simpl. intros v.
             destruct (subst_val_val' e1 v1 ltac:(rewrite -H0 to_of_val; eauto) v) as [a b].
             rewrite -(of_to_val _ _ b).
             rw_fill. by apply fill_step.
    - assert (abs := step_no_val _ _ Hs).
      destruct v; asimpl in abs; inversion abs. asimpl in Hs. inversion Hs.
      destruct K as [|Ki K]. simpl in *; simplify_eq. inversion HS.
      destruct Ki; inversion H0.
    - assert (abs := step_no_val _ _ Hs). inversion abs.
    - (* interesting *)
      inversion Hs.
      destruct K as [|Ki K]; simpl in *; simplify_eq.
      + clear Hs.
        inversion HS; simpl in *; simplify_eq. clear IHe1 IHe2.
        destruct e1; try by inversion H1.
        * (* actual substitution *)
          asimpl in H1. destruct v; inversion H1. simplify_eq.
          left. exists []. by rewrite Omega_closed.
        * right. simpl in H1. simplify_eq.
          exists e.[((rename (+1) e2).[Var 0/])/]. intros v.
          destruct (subst_val_val' _ _ H3 v) as [a b].
          eapply (stepK []). econstructor. econstructor. eauto. by asimpl.
      + destruct Ki; simpl in H0; try by inversion H0.
        * simpl in *. inversion H0. simplify_eq.
          (* IHe1 *)
          assert (Hs1 : step_ne e1.[Lam Omega/] (fill K e_h')).
          { rewrite -H0. by econstructor. }
          specialize (IHe1 (fill K e_h') Hs1). destruct IHe1 as [[K' eq] | [e1' He1']].
          -- left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
          -- right. exists (App ℓ e1' e2). simpl. intros v.
              rw_fill. by apply fill_step.
        * simpl in *. inversion H0. simplify_eq.
          (* IHe2 *)
          assert (Hs2 : step_ne e2.[Lam Omega/] (fill K e_h')).
          { rewrite -H3. by econstructor. }
          specialize (IHe2 (fill K e_h') Hs2). destruct IHe2 as [[K' eq] | [e2' He2']].
          (* destruct (IHe2 (fill K e_h') Hs2) as [[K' eq] | [e2' bb]]. *)
          -- left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
          -- right. exists (App ℓ e1 e2'). simpl. intros v.
             destruct (subst_val_val' e1 v1 ltac:(rewrite -H0 to_of_val; eauto) v) as [a b].
             rewrite -(of_to_val _ _ b).
             rw_fill. by apply fill_step.
    - inversion Hs.
      destruct K as [|Ki K]; simpl in *; simplify_eq.
      + clear Hs.
        inversion HS; simpl in *; simplify_eq.
      + destruct Ki; simpl in H0; try by inversion H0. inversion H0.
        assert (Hs' : step_ne e.[Lam Omega/] (fill K e_h')).
        { rewrite -H1. by econstructor. }
        specialize (IHe (fill K e_h') Hs'). destruct IHe as [[K' eq] | [e2' He2']].
          -- left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
          -- right. exists (InjL e2'). simpl. intros v. rw_fill. by apply fill_step.
    - inversion Hs.
      destruct K as [|Ki K]; simpl in *; simplify_eq.
      + clear Hs.
        inversion HS; simpl in *; simplify_eq.
      + destruct Ki; simpl in H0; try by inversion H0. inversion H0.
        assert (Hs' : step_ne e.[Lam Omega/] (fill K e_h')).
        { rewrite -H1. by econstructor. }
        specialize (IHe (fill K e_h') Hs'). destruct IHe as [[K' eq] | [e2' He2']].
          -- left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
          -- right. exists (InjR e2'). simpl. intros v. rw_fill. by apply fill_step.
    - inversion Hs.
      destruct K as [|Ki K]; simpl in *; simplify_eq.
      + clear Hs.
        inversion HS; simpl in *; simplify_eq; clear IHe IHe0 IHe1.
        * destruct e; (try by inversion H1); [ destruct v; inversion H1 | ].
          simpl. inversion H1. rewrite H0 in H4.
          right.
          exists e1.[((rename (+1) e).[Var 0/])/].
          intros v.
          destruct (subst_val_val' _ _ H4 v) as [a b].
          eapply (stepK []). auto. constructor. 2: asimpl.
          apply b. by rewrite -(of_to_val _ _ b).
        * destruct e; (try by inversion H1); [ destruct v; inversion H1 | ].
          simpl. inversion H1. rewrite H0 in H4.
          right.
          exists e2.[((rename (+1) e).[Var 0/])/].
          intros v.
          destruct (subst_val_val' _ _ H4 v) as [a b].
          eapply (stepK []). auto. constructor. 2: asimpl.
          apply b. by rewrite -(of_to_val _ _ b).
      + destruct Ki; simpl in H0; try by inversion H0.
        inversion H0. simplify_eq.
        assert (Hs' : step_ne e.[Lam Omega/] (fill K e_h')).
        { rewrite -H0. by econstructor. }
        specialize (IHe (fill K e_h') Hs'). destruct IHe as [[K' eq] | [e' He']].
        * left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
        * right. exists (Case ℓ e' e1 e2). simpl. intros v.
          rw_fill. by apply fill_step.
    - inversion Hs.
      destruct K as [|Ki K]; simpl in *; simplify_eq.
      + clear Hs.
        inversion HS; simpl in *; simplify_eq; clear IHe.
        destruct e; (try by inversion H0); [ destruct v; inversion H0 | ].
        simpl. inversion H0. simplify_eq. right. exists e1. intros v.
        destruct (subst_val_val' _ _ H1 v) as [a1 b1].
        destruct (subst_val_val' _ _ H3 v) as [a2 b2].
        eapply (stepK []). auto. econstructor; eauto. auto.
      + destruct Ki; simpl in H0; try by inversion H0.
        inversion H0. simplify_eq.
        assert (Hs' : step_ne e.[Lam Omega/] (fill K e_h')).
        { rewrite -H0. by econstructor. }
        specialize (IHe (fill K e_h') Hs'). destruct IHe as [[K' eq] | [e' He']].
        * left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
        * right. exists (Fst ℓ e'). simpl. intros v.
          rw_fill. by apply fill_step.
    - inversion Hs.
      destruct K as [|Ki K]; simpl in *; simplify_eq.
      + clear Hs.
        inversion HS; simpl in *; simplify_eq; clear IHe.
        destruct e; (try by inversion H0); [ destruct v; inversion H0 | ].
        simpl. inversion H0. simplify_eq. right. exists e3. intros v.
        destruct (subst_val_val' _ _ H1 v) as [a1 b1].
        destruct (subst_val_val' _ _ H3 v) as [a2 b2].
        eapply (stepK []). auto. econstructor; eauto. auto.
      + destruct Ki; simpl in H0; try by inversion H0.
        inversion H0. simplify_eq.
        assert (Hs' : step_ne e.[Lam Omega/] (fill K e_h')).
        { rewrite -H0. by econstructor. }
        specialize (IHe (fill K e_h') Hs'). destruct IHe as [[K' eq] | [e' He']].
        * left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
        * right. exists (Snd ℓ e'). simpl. intros v.
          rw_fill. by apply fill_step.
    - inversion Hs.
      destruct K as [|Ki K]; simpl in *; simplify_eq.
      + clear Hs.
        inversion HS; simpl in *; simplify_eq.
      + destruct Ki; simpl in H0; try by inversion H0.
        * simpl in *. inversion H0. simplify_eq.
          (* IHe1 *)
          assert (Hs1 : step_ne e1.[Lam Omega/] (fill K e_h')).
          { rewrite -H0. by econstructor. }
          specialize (IHe1 (fill K e_h') Hs1). destruct IHe1 as [[K' eq] | [e1' He1']].
          -- left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
          -- right. exists (Pair e1' e2). simpl. intros v.
              rw_fill. by apply fill_step.
        * simpl in *. inversion H0. simplify_eq.
          (* IHe2 *)
          assert (Hs2 : step_ne e2.[Lam Omega/] (fill K e_h')).
          { rewrite -H2. by econstructor. }
          specialize (IHe2 (fill K e_h') Hs2). destruct IHe2 as [[K' eq] | [e2' He2']].
          -- left. rewrite eq. rw_fill. rewrite -fill_app. eexists; auto.
          -- right. exists (Pair e1 e2'). simpl. intros v.
             destruct (subst_val_val' e1 v1 ltac:(rewrite -H0 to_of_val; eauto) v) as [a b].
             rewrite -(of_to_val _ _ b).
             rw_fill. by apply fill_step.
    - exfalso. eapply (faulty_not_stop (Error ℓ)). exists [], (Error ℓ). eauto. eauto.
  Qed.

  Lemma omega_terminate_false K n v : nsteps step_ne n (fill K Omega) (of_val v) → False.
  Proof.
    induction n; simpl.
    - intros abs. inversion abs.
      assert (obv := (fill_not_val K Omega Omega_not_val)).
      by rewrite H to_of_val in obv.
    - intros hmm. inversion hmm. simplify_eq.
      assert (eq := (ne_step_det _ _ _ (fill_step _ _ Omega_step K) H0)). simplify_eq.
      by apply IHn.
  Qed.

  Lemma help n e (Hsteps : nsteps step_ne n e.[Lam Omega/] (Lit LitUnit)) :
      ∀ (v : val), rtc step_ne e.[of_val v/] (Lit LitUnit).
  Proof.
    revert e Hsteps. induction n.
    - intros. inversion Hsteps. simplify_eq.
      destruct e; inversion H. apply rtc_refl.
      destruct v0; inversion H.
    - intros. inversion Hsteps. simplify_eq.
      destruct (help_invariant _ _ H0) as [[K eq] | [e' H]].
      + exfalso. simplify_eq. change (Lit LitUnit) with (of_val $ LitV LitUnit) in H1.
        by eapply omega_terminate_false.
      + assert (eq := (ne_step_det e.[Lam Omega/] _ _ H0 (H (LamV Omega)))).
        simplify_eq.
        specialize (IHn e' H1).
        eapply rtc_l. apply H. apply IHn.
  Qed.

End help.
