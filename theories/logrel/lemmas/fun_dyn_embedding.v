From main.prelude Require Import imports autosubst big_op_three.
From main.grad_lang Require Import types.
From main.dyn_lang Require Import definition lemmas tactics labels lib.
From main.logrel.lib Require Import weakestpre rfn small_helpers.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

From main.logrel Require Import definition.
From main.maps Require Import dyn_embedding.definition grad_into_dyn.definition.

Section fundamental.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma fundamental_r (e : expr) n (Hne : Closed_n n e) :
    open_exprel_typed (replicate n Unknown) (InDynExpr e) e (⟨ (⌈⌈ e ⌉⌉) ⟩) Unknown.
  Proof.
    generalize dependent n.
    induction e; iIntros (n Hn Δ HΔ vs vs') "#Hvsvs'".
    - simpl. asimpl. rfn_steps. rfn_val. rewrite valrel_unknown_unfold. destruct b; eauto.
      (* let's fix later *) Unshelve. exact (fun _ => Lit LitUnit).
    - asimpl.
      rfn_bind.
      iApply (IHe1 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v1 v1') "#H1". asimpl.
      rfn_steps.
      rewrite valrel_unknown_unfold. dvals v1 v1'; try by rfn_faulty.
      rfn_steps.
      iApply (IHe2 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
    - rfn_bind. iApply (IHe1 n with "Hvsvs'"). { intros σ. specialize (Hn σ). inversion Hn. by repeat rewrite H0.  } permissive_solver.
      iIntros (v v') "#Hvv'". simpl. rfn_steps.
      rewrite valrel_unknown_unfold. dvals v v'; try by rfn_faulty.
      iRewrite "Hvv'". destruct b0; rfn_steps; iNext.
      iApply (IHe2 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iApply (IHe3 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
    - rfn_bind.
      iApply (IHe1 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v1 v1') "#H1". asimpl.
      rfn_bind.
      iApply (IHe2 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v2 v2') "#H2".
      rfn_steps.
      do 2 rewrite valrel_unknown_unfold. dvals v1 v1'; try by rfn_faulty.
      dvals v2 v2'; rfn_steps; try by rfn_faulty. rfn_val. iRewrite "H1". iRewrite "H2". do 2 rewrite Z.add_0_l.
      rewrite valrel_unknown_unfold; destruct binop; auto.
    - assert (Hlt := (iffLR (ids_lt_Closed_n _ _) Hn)). iDestruct ((big_sepL3_length _ (replicate n Unknown) vs vs' with "Hvsvs'")) as "[%eq %eq']".
      destruct (lookup_lt_is_Some_2 (replicate n Unknown) v) as [τ Hτ].
      rewrite replicate_length. lia. rewrite replicate_length in eq. simplify_eq.
      destruct (ids_subst_list_lt_length (v) (of_val <$> vs)) as (w1 & eq1 & eq1'). by rewrite map_length.
      destruct (ids_subst_list_lt_length (v) (of_val <$> vs')) as (w2 & eq2 & eq2'). rewrite map_length. lia.
      asimpl in *. rewrite eq1' eq2'. clear eq1' eq2'.
      destruct (list_lookup_fmap_inv _ _ _ _ eq1) as (a1 & eq1' & eq1'').
      destruct (list_lookup_fmap_inv _ _ _ _ eq2) as (a2 & eq2' & eq2'').
      simplify_eq. rfn_val. iApply (big_sepL3_lookup with "Hvsvs'"); eauto. apply lookup_replicate. split; auto.
    - asimpl. rewrite decide_True; auto. rfn_steps. rfn_val. rewrite valrel_unknown_unfold.
      simpl. iNext. iIntros (w w') "Hww'". asimpl.
      change (of_val ?v .: subst_list (?es)) with (subst_list ((of_val v) :: es)). repeat rewrite -fmap_cons.
      iApply (IHe (S n) ltac:(closed_solver) Δ ltac:(permissive_solver)). simpl. auto.
    - asimpl. rewrite decide_True; auto. rfn_steps.
      rfn_bind.
      iApply (IHe1 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v1 v1') "#H1". asimpl.
      rfn_steps.
      rfn_bind.
      iApply (IHe2 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v2 v2') "#H2". asimpl.
      rfn_steps.
      rewrite valrel_unknown_unfold. dvals v1 v1'; try by rfn_faulty.
      rewrite /valrel_unknown_pre /arrow_rel.
      rfn_steps. iNext.
      iApply (@rfn_bindK []). eauto. rw_fill. eauto. by iApply "H1".
      iIntros (w w') "#Hww'". rfn_steps. rfn_val.
    - asimpl. rewrite decide_True; auto. rfn_steps.
      rfn_bind.
      iApply (IHe n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v v') "#H". rfn_steps. rfn_val. by rewrite (valrel_unknown_unfold _ (InjLV _)).
    - asimpl. rewrite decide_True; auto. rfn_steps.
      rfn_bind.
      iApply (IHe n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v v') "#H". rfn_steps. rfn_val. by rewrite (valrel_unknown_unfold _ (InjRV _)).
    - asimpl. rewrite decide_True; auto.
      rfn_bind.
      iApply (IHe n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v v') "#H". asimpl. rfn_steps.
      rewrite valrel_unknown_unfold. dvals v v'; try by rfn_faulty.
      + rfn_steps.
        change (of_val ?v .: subst_list (?es)) with (subst_list ((of_val v) :: es)). repeat rewrite -fmap_cons.
        iApply (IHe0 (S n) ltac:(closed_solver) Δ ltac:(permissive_solver)). simpl. by iFrame "H".
      + rfn_steps.
        change (of_val ?v .: subst_list (?es)) with (subst_list ((of_val v) :: es)). repeat rewrite -fmap_cons.
        iApply (IHe1 (S n) ltac:(closed_solver) Δ ltac:(permissive_solver)). simpl. by iFrame "H".
    - asimpl. rewrite decide_True; auto.
      rfn_bind.
      iApply (IHe n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      asimpl.
      iIntros (v v') "#H". rfn_steps.
      rewrite valrel_unknown_unfold. dvals v v'; try by rfn_faulty.
      rfn_steps. rfn_val. by iDestruct "H" as "[a b]".
    - asimpl. rewrite decide_True; auto.
      rfn_bind.
      iApply (IHe n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      asimpl.
      iIntros (v v') "#H". rfn_steps.
      rewrite valrel_unknown_unfold. dvals v v'; try by rfn_faulty.
      rfn_steps. rfn_val. by iDestruct "H" as "[a b]".
    - asimpl. rewrite decide_True; auto.
      rfn_bind.
      iApply (IHe1 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v1 v1') "#H1". asimpl.
      rfn_bind.
      iApply (IHe2 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v2 v2') "#H2". asimpl.
      rfn_steps. rfn_val. rewrite (valrel_unknown_unfold _ (PairV _ _)). by iFrame "H1 H2".
    - asimpl. rfn_steps. iApply (rfn_faulty); try by faulty_solver. eexists [], _; eauto.
      apply HΔ; split; set_solver.
  Qed.


  Lemma fundamental_l (e : expr) n (Hne : Closed_n n e) :
    open_exprel_typed (replicate n Unknown) (InDynExpr e) (⟨ (⌈⌈ e ⌉⌉) ⟩) e Unknown.
  Proof.
    generalize dependent n.
    induction e; iIntros (n Hn Δ HΔ vs vs') "#Hvsvs'".
    - simpl. rfn_steps. rfn_val. rewrite valrel_unknown_unfold. destruct b; eauto.
      (* let's fix later *) Unshelve. exact (fun _ => Lit LitUnit).
    - asimpl.
      rfn_bind.
      iApply (IHe1 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v1 v1') "#H1". asimpl.
      rfn_steps.
      rewrite valrel_unknown_unfold. dvals v1 v1'; try by rfn_faulty.
      rfn_steps.
      iApply (IHe2 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
    - rfn_bind. iApply (IHe1 n with "Hvsvs'"). { intros σ. specialize (Hn σ). inversion Hn. by repeat rewrite H0.  } permissive_solver.
      iIntros (v v') "#Hvv'". simpl. rfn_steps.
      rewrite valrel_unknown_unfold. dvals v v'; try by rfn_faulty.
      iRewrite "Hvv'". destruct b0; rfn_steps; iNext.
      iApply (IHe2 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iApply (IHe3 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
    - rfn_bind.
      iApply (IHe1 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v1 v1') "#H1". asimpl.
      rfn_bind.
      iApply (IHe2 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v2 v2') "#H2".
      rfn_steps.
      do 2 rewrite valrel_unknown_unfold. dvals v1 v1'; try by rfn_faulty.
      dvals v2 v2'; rfn_steps; try by rfn_faulty. rfn_val. iRewrite "H1". iRewrite "H2". do 2 rewrite Z.add_0_l.
      rewrite valrel_unknown_unfold; destruct binop; auto.
    - assert (Hlt := (iffLR (ids_lt_Closed_n _ _) Hn)). iDestruct ((big_sepL3_length _ (replicate n Unknown) vs vs' with "Hvsvs'")) as "[%eq %eq']".
      destruct (lookup_lt_is_Some_2 (replicate n Unknown) v) as [τ Hτ].
      rewrite replicate_length. lia. rewrite replicate_length in eq. simplify_eq.
      destruct (ids_subst_list_lt_length (v) (of_val <$> vs)) as (w1 & eq1 & eq1'). by rewrite map_length.
      destruct (ids_subst_list_lt_length (v) (of_val <$> vs')) as (w2 & eq2 & eq2'). rewrite map_length. lia.
      asimpl in *. rewrite eq1' eq2'. clear eq1' eq2'.
      destruct (list_lookup_fmap_inv _ _ _ _ eq1) as (a1 & eq1' & eq1'').
      destruct (list_lookup_fmap_inv _ _ _ _ eq2) as (a2 & eq2' & eq2'').
      simplify_eq. rfn_val. iApply (big_sepL3_lookup with "Hvsvs'"); eauto. apply lookup_replicate. split; auto.
    - asimpl. rewrite decide_True; auto. rfn_steps. rfn_val. rewrite valrel_unknown_unfold.
      simpl. repeat iNext. iIntros (w w') "Hww'". asimpl.
      change (of_val ?v .: subst_list (?es)) with (subst_list ((of_val v) :: es)). repeat rewrite -fmap_cons.
      iApply (IHe (S n) ltac:(closed_solver) Δ ltac:(permissive_solver)). simpl. auto.
    - asimpl. rewrite decide_True; auto. rfn_steps.
      rfn_bind.
      iApply (IHe1 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v1 v1') "#H1". asimpl.
      rfn_steps.
      rfn_bind.
      iApply (IHe2 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iNext. iIntros (v2 v2') "#H2". asimpl.
      rfn_steps.
      rewrite valrel_unknown_unfold. dvals v1 v1'; try by rfn_faulty.
      rewrite /valrel_unknown_pre /arrow_rel.
      rfn_steps. repeat iNext.
      rw_fill. iApply (rfn_bind' [AppRCtx _  _] _ []). iApply ("H1" with "H2").
      iIntros (w w') "#Hww'". rfn_steps. rfn_val.
    - asimpl. rewrite decide_True; auto. rfn_steps.
      rfn_bind.
      iApply (IHe n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v v') "#H". rfn_steps. rfn_val. by rewrite (valrel_unknown_unfold _ (InjLV _)).
    - asimpl. rewrite decide_True; auto. rfn_steps.
      rfn_bind.
      iApply (IHe n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v v') "#H". rfn_steps. rfn_val. by rewrite (valrel_unknown_unfold _ (InjRV _)).
    - asimpl. rewrite decide_True; auto.
      rfn_bind.
      iApply (IHe n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v v') "#H". asimpl. rfn_steps.
      rewrite valrel_unknown_unfold. dvals v v'; try by rfn_faulty.
      + rfn_steps.
        change (of_val ?v .: subst_list (?es)) with (subst_list ((of_val v) :: es)). repeat rewrite -fmap_cons.
        iApply (IHe0 (S n) ltac:(closed_solver) Δ ltac:(permissive_solver)). simpl. by iFrame "H".
      + rfn_steps.
        change (of_val ?v .: subst_list (?es)) with (subst_list ((of_val v) :: es)). repeat rewrite -fmap_cons.
        iApply (IHe1 (S n) ltac:(closed_solver) Δ ltac:(permissive_solver)). simpl. by iFrame "H".
    - asimpl. rewrite decide_True; auto.
      rfn_bind.
      iApply (IHe n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      asimpl.
      iIntros (v v') "#H". rfn_steps.
      rewrite valrel_unknown_unfold. dvals v v'; try by rfn_faulty.
      rfn_steps. rfn_val. by iDestruct "H" as "[a b]".
    - asimpl. rewrite decide_True; auto.
      rfn_bind.
      iApply (IHe n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      asimpl.
      iIntros (v v') "#H". rfn_steps.
      rewrite valrel_unknown_unfold. dvals v v'; try by rfn_faulty.
      rfn_steps. rfn_val. by iDestruct "H" as "[a b]".
    - asimpl. rewrite decide_True; auto.
      rfn_bind.
      iApply (IHe1 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v1 v1') "#H1". asimpl.
      rfn_bind.
      iApply (IHe2 n ltac:(closed_solver) Δ ltac:(permissive_solver) with "Hvsvs'").
      iIntros (v2 v2') "#H2". asimpl.
      rfn_steps. rfn_val. rewrite (valrel_unknown_unfold _ (PairV _ _)). by iFrame "H1 H2".
    - asimpl. rfn_steps. iApply (rfn_faulty); try by faulty_solver. eexists [], _; eauto.
      apply HΔ; split; set_solver.
  Qed.


  (* alternatively; we can define logrel at Γ such that arbitrary substitution larger... *)
  (* or just enforce closedness in logrel; might be more natural.. *)

  Lemma dyn_emb_trns_pres_closed_n e n : Closed_n n e → Closed_n n (⟨ (⌈⌈ e ⌉⌉) ⟩).
  Proof.
    revert n.
    induction e; intros; (try by asimpl); intros σ'; asimpl; (try rewrite decide_True; auto);
    try by repeat f_equiv;
        (try by rewrite IHe; [auto | closed_solver]);
        (try by rewrite IHe0; [auto | closed_solver]);
        (try by rewrite IHe1; [auto | closed_solver]);
        (try by rewrite IHe2; [auto | closed_solver]);
        (try by rewrite IHe3; [auto | closed_solver]).
  Qed.


End fundamental.
