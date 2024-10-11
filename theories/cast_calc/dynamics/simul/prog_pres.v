From main Require Import imports prelude.autosubst prelude.tactics.
(* From main.cast_calc Require Import types definition. *)
From main.cast_calc Require Import types definition typing.
From main.cast_calc.dynamics Require Import std lemmas.
From main.cast_calc.dynamics.simul Require Import invariant.
From main.dyn_lang Require Import definition casts lib lemmas tactics.

Require Import main.cast_calc.cc.
Require Import main.dyn_lang.dn.

Section progress_and_preservation.

  Context {ν : label} {Hν : NeverOccurs ν}.

  (* considering dyn steps that are not otf K[error] → error *)
  Definition pp_step (e e' : expr) : Prop :=
     ∃ (K : ectx) e_h e_h' (HS : head_step e_h e_h'),
        e = fill K e_h ∧ e' = fill K e_h'.

  Lemma pp_step_dn_step e e' : pp_step e e' → dn.step e e'.
  Proof. destruct 1 as (K & e_h & e_h' & Hh & -> & ->). by constructor. Qed.

  Lemma step_ne_pp_step e e' : step_ne e e' → pp_step e e'.
  Proof. inversion 1. repeat eexists. by constructor. Qed.

  (* v : ? + ? ⇒ ? × ? → Error *)
  (* Pair (pi_1 v) () → Pair *)
  Definition InvariantR e e1 :=
        ∃ e2, tc pp_step e1 e2 ∧
              (match e with
              | cc.Error ℓ => ∃ K, e2 = fill K (Error ℓ)
              | _ => Invariant e e2
              end ).

  Lemma helpR {e e'} e'' :
      Invariant e e'' → tc pp_step e' e'' → InvariantR e e'.
  Proof.
    intros. exists e''; split; auto. destruct e; auto. invclear H. exists []; auto.
  Qed.

  Instance blaaa e : Decision (∃ ℓ : label, e = cc.Error ℓ).
  Proof.
    destruct e; try by right; intros abs; destruct abs as [ℓ' abs]; simplify_eq.
    left. by eexists.
  Qed.

  Lemma helpR' {e e'} e'' :
      InvariantR e e'' → tc pp_step e' e'' → InvariantR e e'.
  Proof.
    intros. destruct H as (e2 & H12 & HH). rewrite /InvariantR.
    destruct (decide (∃ ℓ, e = cc.Error ℓ)) as [[ℓ ->] | neq].
    - destruct HH as [K ->]. exists (fill K (Error ℓ)).
      split. by eapply tc_transitive. by exists K.
    - simpl. assert (Invariant e e2). destruct e; try done. exfalso. apply neq. by eexists.
      exists e2. split. by eapply tc_transitive.
      destruct e; try done.
  Qed.

  Lemma tc_step_bind K e v e' :
      rtc step_ne e (of_val v) → tc pp_step (fill K (of_val v)) e' → tc pp_step (fill K e) e'.
  Proof.
    intros. eapply tc_rtc_l; eauto.
    eapply rtc_congruence; eauto. intros. apply step_ne_pp_step. by apply fill_step.
  Qed.

  Lemma rtc_step_bind K e v e' :
      rtc step_ne e (of_val v) → rtc pp_step (fill K (of_val v)) e' → rtc pp_step (fill K e) e'.
  Proof.
    intros. eapply rtc_transitive; eauto.
    eapply rtc_congruence; eauto. intros. apply step_ne_pp_step. by apply fill_step.
  Qed.

  Ltac bind' := rw_fill; eapply rtc_step_bind; eauto.
  Ltac take_step' :=
        eapply rtc_l; first apply step_ne_pp_step; first step_solver.

  Ltac one_step :=
        eapply tc_once; first apply step_ne_pp_step; first step_solver.

  Lemma tc_one_rtc : ∀ {A : Type} {R : relation A} (x y z : A),
     R x y → rtc R y z → tc R x z.
  Proof. intros. eapply tc_rtc_r. by apply tc_once. auto. Qed.

  Ltac take_step :=
        eapply tc_one_rtc; first apply step_ne_pp_step; first step_solver.

  Ltac bind := rw_fill; eapply tc_step_bind; eauto.

  Ltac refl := by eapply rtc_refl.

  Lemma error_faulty e ℓ :
      faulty e ℓ → rtc step e (Error ℓ).
  Proof.
    intros. destruct H as (K & e_h & -> & [Hf | ->]).
    - eapply (rtc_l _ _ (fill K (Error ℓ))). apply S_Normal. by apply H_error.
      destruct K; econstructor; eauto. apply S_Error; auto. refl.
    - destruct K; econstructor; eauto. apply S_Error; auto. refl.
  Qed.

  Lemma help_val {τ e v e'}
    (Hee' : Invariant e e') (Heτ : typed [] e τ) (He : cc.to_val e = Some v) :
      ∃ v', rtc step_ne e' (of_val v') ∧ Invariant e (dn.of_val v').
  Proof. eapply left_val_Invariant; eauto. Qed.

  Tactic Notation "helpV" constr(H) "as" simple_intropattern(x) :=
    destruct (help_val H ltac:(by eauto) ltac:(by eauto)) as x.

  Lemma asdf K ℓ e :
      (∃ e_h, e = fill K e_h ∧ head_faulty e_h ℓ) → pp_step e (fill K (Error ℓ)).
  Proof.
    intros H. destruct H as (e_h & -> & Hf).
    by exists K, e_h, (Error ℓ), (H_error _ _ Hf).
  Qed.

  Lemma down_ground_fail ℓ G (HG : G ≠ S_Bin Arrow) v :
    shape_val v ≠ G →
    InvariantR (cc.Error ℓ) (App ν (of_val $ (cast' ℓ Unknown (types.of_shape G))) (of_val v)).
  Proof.
    rewrite /InvariantR. intros Hv.
    rewrite cast_downwards_rw /=. destruct G.
    - exists (Error ℓ). split; [ | by exists [] ].
      destruct b; take_step; simpl;
        apply rtc_once; apply (asdf []); rw_fill; eexists; eauto; split; eauto; head_faulty_solver.
    - destruct bin; [ by simplify_eq | | ]; rewrite /= decide_True; auto.
      + eexists; split. simpl. take_step. asimpl.
        apply rtc_once; apply (asdf []); rw_fill; eexists; eauto; split; eauto; head_faulty_solver. by eexists.
      + eexists; split. simpl. take_step. asimpl.
        apply rtc_once. eapply (asdf [ PairLCtx _ ]). eexists; eauto; split; eauto; head_faulty_solver. by eexists.
  Qed.

  Lemma left_head_step_Invariant e τ (Heτ : typed [] e τ) e' (HIe : Invariant e e') :
      ∀ e2, cc.head_step e e2 → InvariantR e2 e'.
      (* ∀ e2, cc.head_step e e2 → InvariantR e2 e'. *)
  Proof.
    intros e2 Hstep. inversion Hstep; simplify_eq; clear Hstep.
    - (* non-cast related *) invclear Hs.
      + invclear HIe. eapply helpR; eauto.
        { destruct e1'; invclear H3. one_step. }
      + destruct b.
        * invclear HIe.
          eapply helpR; eauto.
          { destruct e0'; invclear H4. one_step. }
        * invclear HIe.
          eapply helpR; eauto.
          { destruct e0'; invclear H4. one_step. }
      + invclear HIe.
        eapply (helpR (of_val $ bin_op_eval op z1 z2)). destruct op; constructor.
        { destruct e1'; invclear H4.
          destruct e2'; invclear H5. one_step. }
      + invclear HIe.
        invclear H3.
        invclear Heτ. invclear H4.
        helpV H1 as (v0' & Hsteps & HIv0').
        apply (helpR (e1'.[of_val v0'/])). apply subst_Invariant; auto. erewrite cc.of_to_val; eauto.

        bind. one_step.
      + invclear HIe.
        invclear H3.
        invclear Heτ. invclear H4.
        helpV H1 as (v0' & Hsteps & HIv0').
        apply (helpR (e2'.[of_val v0'/])). apply subst_Invariant; auto. erewrite cc.of_to_val; eauto.
        bind. one_step.
      + invclear HIe. invclear H2.
        invclear Heτ. invclear H2.
        helpV H4 as (v1' & Hsteps & HIv1').
        helpV H6 as (v2' & Hsteps2 & HIv2').
        eapply helpR; eauto. do 2 bind. one_step.
      + invclear HIe. invclear H2.
        invclear Heτ. invclear H2.
        helpV H4 as (v1' & Hsteps & HIv1').
        helpV H6 as (v2' & Hsteps2 & HIv2').
        eapply helpR; eauto. do 2 bind. one_step.
      + invclear HIe. invclear H0.
        invclear Heτ. invclear H3.
        helpV H4 as (va' & Hsteps & HIva').
        eapply helpR; eauto. 2: { bind. one_step. } simpl.
        eapply subst_Invariant; eauto.
    - (* cast related *) invclear Hs.
      + invclear HIe.
        invclear Heτ.
        helpV H5 as (v' & Hsteps & HIv').
        eapply helpR; eauto. bind. simpl. rewrite cast_B_rw. one_step.
        (* novel degenerate case *)
        (* { destruct G; inversion H6. repeat rewrite decide_True in H2; auto. inversion H2. } *)
      + invclear HIe; [| destruct G; inversion H2 ].
        (* invclear HIe; [| destruct G; inversion H2 |]. *)
        invclear Heτ.
        helpV H5 as (v' & Hsteps & HIv').
        eapply helpR; eauto. bind. simpl. one_step.
        (* novel degenerate case *)
        (* { destruct G; inversion H1. } *)
      + (* G ⇒ ? ⇒ G *) (* G not ? → ?, because is a value *)
        invclear HIe.
        (* only one non-degenerate case *)
        { invclear Heτ.
          assert (Heq : cc.to_val (Cast ℓ1 (types.of_shape G) Unknown e2) = Some $ CastGroundUpV ℓ1 G v).
            { destruct G; (try destruct bin); simplify_option_eq; auto. }
          destruct (help_val H6 ltac:(by eauto) Heq) as (v1' & Hsteps & HIv1').
          inversion HIv1'; simplify_eq; [ destruct v1'; inversion H9 | ].
          eapply helpR; eauto. bind. simpl.
          destruct (decide (G0 = G)); simplify_eq.
          2:{ destruct G0; destruct G; inversion H3.
              exfalso. apply n. simplify_eq. exfalso. apply n. by f_equiv. }
          rewrite cast_downwards_rw.
          (* v' is of the right shape, so should be good *)
          { invclear H8.
            destruct G.
            - destruct v0; invclear H10. simpl.
              destruct b0; take_step; simpl; invclear H5; repeat take_step'; try done.
              destruct b; refl.
            - destruct bin; simplify_eq.
              + (* sum *) destruct v0; invclear H10.
                * invclear H5; rewrite H2.
                  destruct v'; inversion H2.
                  repeat rewrite /= decide_True; auto. take_step. repeat take_step'. by simplify_eq.
                * invclear H5; rewrite H2.
                  destruct v'; inversion H2.
                  repeat rewrite /= decide_True; auto. take_step. repeat take_step'. by simplify_eq.
              + (* product *) destruct v0; invclear H10.
                invclear H5. destruct v'; invclear H4.
                repeat rewrite /= decide_True; auto. take_step. by repeat (take_step'; asimpl). }
        }
        exfalso; destruct G0; inversion H3.
        exfalso; destruct G; inversion H0; simplify_option_eq.
        (* novel degenerate case *)
        (* { destruct G0; inversion H2. } *)
      + (* G1 ⇒ ? ⇒ G2 *) (* G1 ≠ G2, and G2 ≠ ? → ? *)
        invclear HIe; [ | destruct G; inversion H4 | destruct G2; invclear H4 ].
        (* invclear HIe; [ | destruct G; inversion H4 | destruct G2; invclear H4 | ]. *)
        invclear Heτ. invclear H9.
        invclear H7.
        * (* first should go through (because id), second should fail because of shape argument *)
          rewrite cast_GU_rw.
          destruct (help_val H11 ltac:(by eauto) ltac:(by eauto)) as (v' & Hsteps & HIv').
          eapply helpR'. 2:{ bind. simpl. one_step. } simpl.
          apply down_ground_fail. auto.
          rewrite -(cc.of_to_val _ _ H1) in HIv' H10.
          rewrite -(val_shape_Invariant _ _ H10 _ HIv').
          by rewrite (typed_shape _ _ H10).
        * (* should fail because of shape arugment *)
          apply down_ground_fail. auto.
          rewrite -(val_shape_Invariant _ _ H10 _ H9).
          by rewrite (typed_shape _ _ H10).
      + (* application case *) invclear Heτ.
        invclear H3. invclear H10.
        destruct (decide (G = S_Bin Arrow)) as [-> | neq].
        * (* application goes through: G = ? → ? *)
          invclear HIe.
          invclear H6.
          -- invclear H12.
             ++ rewrite cast_upwards_rw cast_downwards_rw /=. repeat rewrite decide_True; auto.
                helpV H9 as (v0' & Hsteps & HIv0').
                destruct (help_val H11 ltac:(by eauto) ltac:(by eauto)) as (v1' & Hsteps1 & HIv1').
                eapply helpR. 2:{ bind. simpl. take_step. repeat take_step'. asimpl. bind'. repeat take_step'. asimpl. refl. }
                constructor; eauto.
             ++ destruct G; invclear H6.
                rewrite cast_downwards_rw /=. repeat rewrite decide_True; auto.
                helpV H9 as (va' & Hstepsa & HIva').
                eapply helpR. 2:{ simpl. take_step. asimpl. bind'. asimpl. take_step'. asimpl. refl. }
                repeat constructor; eauto.
          -- helpV H9 as (va' & Hstepsa & HIva').
             eapply helpR. 2:{ bind. asimpl. take_step. asimpl. rewrite HCe'. refl. }
             repeat constructor; eauto.
             invclear H10. destruct v'; inversion H12. auto.
        * (* application does not go through *)
          apply (helpR (Error ℓ2)). destruct G; (try destruct bin); try by constructor. exfalso. by apply neq.
          invclear HIe.
          invclear H6.
          -- (* e' will be of non-arrow shape *)
            invclear H12.
            ++ rewrite cast_GU_rw. destruct (help_val H11 ltac:(by eauto) ltac:(by eauto)) as (v0' & Hsteps & HIv0').
               helpV H9 as (v1' & Hsteps1 & HIv1').
               bind. simpl.
               rewrite cast_downwards_rw /=. repeat rewrite decide_True; auto.
               take_step. repeat take_step'. asimpl. bind'. take_step'. asimpl.

               assert (shape_val v0' ≠ S_Bin Arrow).
               { rewrite -(cc.of_to_val _ _ H) in HIv0' H11 H8.
                 rewrite -(val_shape_Invariant _ _ H8 _ HIv0').
                 by rewrite (typed_shape _ _ H8). }
               apply rtc_once; apply (asdf []); rw_fill; eexists; eauto; split; eauto; head_faulty_solver.
            ++ rewrite cast_downwards_rw /=. repeat rewrite decide_True; auto.
               helpV H9 as (v2' & Hsteps2 & HIv2').
               take_step. bind'. repeat take_step'. asimpl.
               assert (shape_val v' ≠ S_Bin Arrow).
               { rewrite -(cc.of_to_val _ _ H) in H10 H8.
                 rewrite -(val_shape_Invariant _ _ H8 _ H10).
                 by rewrite (typed_shape _ _ H8). }
                 apply rtc_once; apply (asdf []); rw_fill; eexists; eauto; split; eauto; head_faulty_solver.
          -- (* e2' will be of non-arrow shape *)
             helpV H9 as (v2' & Hsteps2 & HIv2').
             bind. take_step. asimpl. rewrite HCe'.
             assert (shape_val v' ≠ S_Bin Arrow).
             { invclear H10. destruct v'; invclear H12.
               rewrite -(val_shape_Invariant _ _ H8 _ H11).
               by rewrite (typed_shape _ _ H8). }
             apply rtc_once; apply (asdf []); rw_fill; eexists; eauto; split; eauto; head_faulty_solver.
      + (* arrow to arrow (with app) *) invclear Heτ. invclear H3.
        invclear HIe. invclear H3.
        * destruct (help_val H11 ltac:(by eauto) ltac:(by eauto)) as (v1' & Hsteps1 & HIv1').
          helpV H7 as (v2' & Hsteps2 & HIv2').
          eapply helpR. 2:{ invclear H4. rewrite cast_arrow_rw /=; auto.
                            bind. simpl. take_step. simpl. bind'. simpl. take_step'. asimpl. refl. }
          repeat constructor; auto.
        * helpV H7 as (v2' & Hsteps2 & HIv2').
          eapply helpR. 2:{ bind. simpl. take_step. simpl. repeat rewrite cast'_closed. rewrite HCe'. refl. }
          repeat constructor; auto.
      + (* product to product *)
        invclear HIe. invclear Heτ. invclear H7. rewrite cast_product_rw; auto.
        invclear H6. invclear H8.
        helpV H4 as (v1' & Hsteps1 & HIv1').
        helpV H7 as (v2' & Hsteps2 & HIv2').
        eapply helpR. 2:{ do 2 bind. take_step. repeat take_step'. asimpl. repeat take_step'. asimpl. refl. }
        repeat constructor; eauto.
      + (* injl case *)
        invclear HIe. invclear H5. invclear Heτ. invclear H7.
        helpV H1 as (v2' & Hsteps2 & HIv2').
        eapply helpR. 2:{ bind. invclear H6. rewrite cast_sum_rw; auto. take_step. repeat take_step'. asimpl. refl. }
        repeat constructor; auto.
      + (* injr case *)
        invclear HIe. invclear H5. invclear Heτ. invclear H7.
        helpV H1 as (v2' & Hsteps2 & HIv2').
        eapply helpR. 2:{ bind. invclear H6. rewrite cast_sum_rw; auto. take_step. repeat take_step'. asimpl. refl. }
        repeat constructor; auto.
      + (* τ0 (≠ G) ⇒ G ⇒ ? *)
        invclear HIe; [| destruct G0; inversion H0; repeat rewrite decide_True in H3; auto; simplify_eq ].
        invclear Heτ.
        helpV H7 as (v' & Hsteps & HIv').
        eapply helpR.
        2:{ rewrite (cast_factor_up_rw ℓ τ0 G); auto.
            rewrite /casts.compd /=. bind. simpl. take_step. asimpl. refl. }
        repeat constructor; auto.
      + (* ? ⇒ G ⇒ τ0 (≠G) *)
        invclear HIe; [| destruct G0; inversion H4].
        invclear Heτ.
        helpV H7 as (v' & Hsteps & HIv').
        eapply helpR.
        2:{ rewrite (cast_factor_down_rw ℓ τ G); auto.
            rewrite /casts.compd /=. bind. simpl. take_step. asimpl. refl. }
        repeat constructor; auto.
  Qed.

  Definition Invariant_ectx_item Ki Ki' : Prop :=
      ∀ e e', Invariant e e' → Invariant (cc.fill_item Ki e) (fill_item Ki' e').

  Definition Invariant_ectx K K' : Prop :=
      ∀ e e', Invariant e e' → Invariant (cc.fill K e) (fill K' e').

  Lemma Invariant_ectx_empty_l K : Invariant_ectx [] K → K = [].
  Proof.
    intros. destruct K as [|Ki K]; auto. exfalso.
    specialize (H (cast_calc.definition.Lit LitUnit) (Lit LitUnit) ltac:(constructor)).
    invclear H. destruct Ki; invclear H2.
  Qed.

  Lemma Invariant_ectx_non_empty_l K (HK : K ≠ []) K' : Invariant_ectx K K' → K' ≠ [].
  Proof.
    intros. destruct K as [|Ki K]; auto. destruct K' as [|Ki' K']; auto. exfalso.
    specialize (H (cc.Error (Lbl 0)) (Error (Lbl 0)) ltac:(constructor)).
    simpl in H. destruct Ki; invclear H. destruct v'; inversion He'.
  Qed.

  Lemma help_val' {τ v e'}
    (Hee' : Invariant (cc.of_val v) e') (Heτ : typed [] (cc.of_val v) τ) :
      ∃ v', rtc step_ne e' (of_val v') ∧ Invariant (cc.of_val v) (dn.of_val v').
  Proof. eapply left_val_Invariant; eauto. by erewrite cc.to_of_val. Qed.

  Lemma ectx_item_Invariant_decompose Ki e (He : cc.to_val e = None) τ (Hτ : [] ⊢ cc.fill_item Ki e : τ) t (HI : Invariant (cc.fill_item Ki e) t) :
      ∃ Ki' e', rtc pp_step t (fill_item Ki' e') ∧ Invariant_ectx_item Ki Ki' ∧ Invariant e e'.
  Proof.
    destruct Ki; simpl in *; try by invclear HI; rw_fill; eexists _, _; split;
       [ apply rtc_refl; eauto | repeat constructor; auto ].
    - invclear HI. invclear Hτ.
      destruct (help_val' H3 ltac:(eauto)) as (v1' & Hsteps & HIv1').
      eexists _, _. split. bind'. simpl. rw_fill. refl. split; auto.
      intros t t' HI. constructor; auto.
    - invclear HI. invclear Hτ.
      destruct (help_val' H3 ltac:(eauto)) as (v1' & Hsteps & HIv1').
      eexists _, _. split. bind'. simpl. rw_fill. refl. split; auto.
      intros t t' HI. constructor; auto.
    - invclear HI. invclear Hτ.
      destruct (help_val' H4 ltac:(eauto)) as (v1' & Hsteps & HIv1').
      eexists _, _. split. bind'. simpl. rw_fill. refl. split; auto.
      intros t t' HI. constructor; auto.
    - invclear HI; (try by erewrite cc.to_of_val in He; inversion He).
      rw_fill. eexists _, _. split. refl. split; auto. by constructor.
  Qed.

(* rtc_step_not_error_fill *)
  Lemma pp_step_fill e e' K :
      pp_step e e' → pp_step (fill K e) (fill K e').
  Proof.
    intros H. destruct H as (K' & e_h & e_h' & Hh & -> & ->).
    repeat rewrite -fill_app. repeat eexists; eauto.
  Qed.

  Lemma rtc_pp_step_fill e e' K :
      rtc pp_step e e' → rtc pp_step (fill K e) (fill K e').
  Proof.
    intros H. eapply rtc_congruence; eauto. intros.
    destruct H0 as (K' & e_h & e_h' & Hh & -> & ->).
    repeat rewrite -fill_app. repeat eexists; eauto.
  Qed.

  Lemma ectx_Invariant_decompose K e (He : cc.to_val e = None) τ (Hτ : [] ⊢ cc.fill K e : τ) t (HI : Invariant (cc.fill K e) t) :
      ∃ K' e', rtc pp_step t (fill K' e') ∧ Invariant_ectx K K' ∧ Invariant e e'.
  Proof.
    generalize dependent e.
    generalize dependent τ.
    generalize dependent t.
    induction K as [|Ki K] using rev_ind; intros.
    - eexists [], t. simpl. (repeat split); [ refl | intros k k' Hkk'; eauto | auto ].
    - rewrite cast_calc.dynamics.lemmas.fill_app in Hτ HI.
      destruct (ectx_decompose _ _ _ _ Hτ) as (τ' & dKie & dK).
      assert (cc.to_val (cc.fill_item Ki e) = None) by by destruct e; destruct Ki; simpl; repeat rewrite cc.to_of_val; auto; simplify_option_eq.
      specialize (IHK t τ _ H Hτ HI) as (K' & e' & Hsteps & HKK' & HI'). simpl in dKie.
      destruct (ectx_item_Invariant_decompose Ki e He τ' dKie _ HI') as (Ki' & t' & Hsteps' & HKiKi' & HI'').
      exists (K' ++ [Ki']), t'; repeat split; auto.
      eapply rtc_transitive; eauto. rewrite fill_app.
      by apply rtc_pp_step_fill.
      intros k k' Hkk'. rewrite fill_app cast_calc.dynamics.lemmas.fill_app. apply HKK'. by apply HKiKi'.
  Qed.

  Inductive Invariant_EC : cc.expr → dn.expr → Prop :=
  | Standard e e' (HI : Invariant e e') : Invariant_EC e e'
  | K_Error K (HK : K ≠ []) K' (HK' : K' ≠ []) ℓ :
      Invariant_EC (cc.fill K (cc.Error ℓ)) (fill K' (Error ℓ)).

  Lemma left_step_Invariant_EC e τ (Heτ : typed [] e τ) e' (HIe : Invariant_EC e e') :
      ∀ e2, cc.step e e2 → ∃ e2', tc step e' e2' ∧ (Invariant_EC e2 e2').
  Proof.
    intros e2 Hee2. invclear HIe.
    - invclear Hee2.
      (* regular head step *)
      + assert (He_h := (cc.head_step_not_val _ _ HS)).
        destruct (ectx_decompose _ _ _ _ Heτ) as (τ' & Hτ' & HK).
        destruct (ectx_Invariant_decompose _ _ He_h _ Heτ _ HI) as (K' & e'' & Hsteps & IKK & Iee').
        (* assert (HH := left_head_step_Invariant _ _ Hτ' _ Iee' _ HS). *)
        (* rewrite /InvariantR in HH.  *)
        destruct (left_head_step_Invariant _ _ Hτ' _ Iee' _ HS) as (e2 & Hpp & HI').
        destruct (decide (∃ ℓ, e_h' = cc.Error ℓ)) as [[ℓ ->] | neg].
        * (* e_h → Error *) destruct HI' as [L ->].
          destruct (decide (K = [])) as [-> | neq].
          -- (* happens a top level *)
             assert (eq := Invariant_ectx_empty_l _ IKK). simplify_eq.
             exists (Error ℓ). split; [| repeat constructor ]. simpl in Hsteps.
             apply (tc_rtc_l _ e'').
             eapply (rtc_congruence id); try eapply Hsteps. apply pp_step_dn_step.
             apply (tc_rtc_r _ (fill L (Error ℓ))).
             eapply (tc_congruence id); try eapply Hpp. apply pp_step_dn_step.
             destruct L as [|Li L]; [ apply rtc_refl | by apply rtc_once; repeat constructor ].
          -- (* does not happen at top level *)
             assert (neq' := Invariant_ectx_non_empty_l _ neq _ IKK). simplify_eq.
             exists (fill (K' ++ L) (Error ℓ)). split; [| apply K_Error; auto; destruct K'; auto ].
             rewrite fill_app.
             eapply (tc_rtc_l _ (fill K' e'')).
             eapply (rtc_congruence id); try eapply pp_step_dn_step; eauto.
             eapply (tc_congruence (fill K')); try eapply pp_step_dn_step; eauto.
             intros. apply pp_step_dn_step. by apply pp_step_fill.
        * (* e_h → e_h' *)
          assert (Invariant e_h' e2) as HI''. destruct e_h'; try auto. exfalso. apply neg. by eexists. clear HI'.
          exists (fill K' e2). split; [ | repeat constructor; auto ].
          eapply (tc_rtc_l _ (fill K' e'')).
          eapply (rtc_congruence id). apply pp_step_dn_step.
          apply Hsteps.
          eapply (tc_congruence (fill K')); try eapply pp_step_dn_step; eauto.
          intros. apply pp_step_dn_step. by apply pp_step_fill.
      + (* K[error] → Error *)
        exists (Error ℓ). split; [|repeat constructor].
        assert (He_h : cc.to_val (cc.Error ℓ) = None). auto.
        destruct (ectx_decompose _ _ _ _ Heτ) as (τ' & Hτ' & HK).
        destruct (ectx_Invariant_decompose _ _ He_h _ Heτ _ HI) as (K' & e'' & Hsteps & IKK & Iee').
        assert (neq' := Invariant_ectx_non_empty_l _ H _ IKK).
        assert (e'' = Error ℓ) as ->. by destruct e''; invclear Iee'.
        eapply (tc_rtc_l _ (fill K' (Error ℓ))).
        eapply (rtc_congruence id); try eapply pp_step_dn_step; eauto.
        apply tc_once. by constructor.
  - assert (e2 = cc.Error ℓ) as ->.
    eapply (cc.step_det _ _ _ Hee2). by constructor.
    exists (Error ℓ). split; [|repeat constructor]. apply tc_once. constructor. auto.
  Qed.

End progress_and_preservation.
