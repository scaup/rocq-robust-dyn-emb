From main Require Import imports prelude.autosubst prelude.tactics.
(* From main.grad_lang Require Import types definition. *)
From main.grad_lang Require Import types typing.
From main.grad_lang.dynamics Require Import std lemmas.
From main.dyn_lang Require Import definition casts lib lemmas tactics.

Notation cc_expr := grad_lang.definition.expr.
Notation dn_expr := dyn_lang.definition.expr.

Notation cc_of_val := std.of_val.

Notation cc_Error := grad_lang.definition.Error.
Notation cc_fill := std.fill.

Section simul_map.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Reserved Notation "⌜ e ⌝" (at level 5, e at next level).

  Fixpoint simul_expr (e : cc_expr) : expr :=
    match e with
    | grad_lang.definition.Lit b => Lit b
    | grad_lang.definition.Seq e1 e2 => Seq ν ⌜e1⌝ ⌜e2⌝
    | grad_lang.definition.If e0 e1 e2 => If ν ⌜e0⌝ ⌜e1⌝ ⌜e2⌝
    | grad_lang.definition.BinOp binop e1 e2 => BinOp ν binop ⌜e1⌝ ⌜e2⌝
    | grad_lang.definition.Var v => Var v
    | grad_lang.definition.Lam e => Lam ⌜e⌝
    | grad_lang.definition.App e1 e2 => App ν ⌜e1⌝ ⌜e2⌝
    | grad_lang.definition.InjL e => InjL ⌜e⌝
    | grad_lang.definition.InjR e => InjR ⌜e⌝
    | grad_lang.definition.Case e0 e1 e2 => Case ν ⌜e0⌝ ⌜e1⌝ ⌜e2⌝
    | grad_lang.definition.Fst e => Fst ν ⌜e⌝
    | grad_lang.definition.Snd e => Snd ν ⌜e⌝
    | grad_lang.definition.Pair e1 e2 => Pair ⌜e1⌝ ⌜e2⌝
    | Cast ℓ τ1 τ2 e =>
        App ν (of_val $ cast' ℓ τ1 τ2) ⌜e⌝
    | grad_lang.definition.Error ℓ => Error ℓ
    end where "⌜ e ⌝" := (simul_expr e).

End simul_map.

Notation "⌜ e ⌝" := (simul_expr e) (at level 5, e at next level).

Section invariant.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Inductive Invariant : cc_expr → dn_expr → Prop :=
  | I_Lit b : Invariant (grad_lang.definition.Lit b) (Lit b)
  | I_Seq e1 e1' (H1 : Invariant e1 e1')
      e2 e2' (H2 : Invariant e2 e2') :
      Invariant (grad_lang.definition.Seq e1 e2) (Seq ν e1' e2')
  | I_If e0 e0' (H1 : Invariant e0 e0')
      e1 e1' (H2 : Invariant e1 e1')
      e2 e2' (H2 : Invariant e2 e2') :
      Invariant (grad_lang.definition.If e0 e1 e2) (If ν e0' e1' e2')
  | I_BinOp binop e1 e1' (H1 : Invariant e1 e1')
      e2 e2' (H2 : Invariant e2 e2') :
      Invariant (grad_lang.definition.BinOp binop e1 e2) (BinOp ν binop e1' e2')
  | I_Var x : Invariant (grad_lang.definition.Var x) (Var x)
  | I_Lam e e' (H : Invariant e e') :
      Invariant (grad_lang.definition.Lam e) (Lam e')
  | I_App ℓ e1 e1' (H1 : Invariant e1 e1')
      e2 e2' (H2 : Invariant e2 e2') :
      Invariant (grad_lang.definition.App e1 e2) (App ℓ e1' e2')
  | I_InjL e e' (H : Invariant e e') :
      Invariant (grad_lang.definition.InjL e) (InjL e')
  | I_InjR e e' (H : Invariant e e') :
      Invariant (grad_lang.definition.InjR e) (InjR e')
  | I_Case e0 e0' (H1 : Invariant e0 e0')
      e1 e1' (H2 : Invariant e1 e1')
      e2 e2' (H2 : Invariant e2 e2') :
      Invariant (grad_lang.definition.Case e0 e1 e2) (Case ν e0' e1' e2')
  | I_Fst e e' (H : Invariant e e') :
      Invariant (grad_lang.definition.Fst e) (Fst ν e')
  | I_Snd e e' (H : Invariant e e') :
      Invariant (grad_lang.definition.Snd e) (Snd ν e')
  | I_Pair e1 e1' (H1 : Invariant e1 e1')
      e2 e2' (H2 : Invariant e2 e2') :
      Invariant (grad_lang.definition.Pair e1 e2) (Pair e1' e2')
  (* ..... *)
  (* for direct translation of cast *)
  | I_Cast ℓ τ1 τ2 e e' (H : Invariant e e') :
      Invariant (Cast ℓ τ1 τ2 e) (App ν (of_val $ cast' ℓ τ1 τ2) e')
  (* ..... *)
  (* for relating terminated stuff *)
  (* between arrows *)
  | I_Cast_Arrow_Arrow ℓ ℓ' τ1 τ2 τ3 τ4
      e v (He : e = cc_of_val v) (HCe : Closed e) e' v' (He' : e' = of_val v') (HCe' : Closed e') (H : Invariant e e') :
      Invariant (Cast ℓ (Bin Arrow τ1 τ2) (Bin Arrow τ3 τ4) e)
        (Lam
           (App ν (of_val $ cast' ℓ τ2 τ4)
              (App ℓ' e'
                 (App ν (of_val $ cast' ℓ τ3 τ1) (Var 0)))))
  (* G => ? *)
  | I_Cast_GroundUp ℓ (G : shape)
      e v (He : e = cc_of_val v) (HCe : Closed e) e' v' (He' : e' = of_val v') (HCe' : Closed e') (H : Invariant e e') :
      Invariant (Cast ℓ (types.of_shape G) Unknown e) e'
  (* ? => ? → ?*)
  | I_Cast_ArrowDown ℓ
      e v (He : e = cc_of_val v) (HCe : Closed e) e' v' (He' : e' = of_val v') (HCe' : Closed e') (H : Invariant e e') :
      Invariant (Cast ℓ Unknown (Bin Arrow Unknown Unknown) e)
        (Lam (App ℓ e' (Var 0)))
  (* ..... *)
  (* relating errors *)
  | I_Error ℓ :
      Invariant (grad_lang.definition.Error ℓ) (Error ℓ).

End invariant.

Notation cc_step := grad_lang.dynamics.std.step.
Notation dn_step := dyn_lang.definition.step.

Notation cc_head_step := grad_lang.dynamics.std.head_step.

Notation dn_of_val := dyn_lang.definition.of_val.

Notation cc_to_val := grad_lang.dynamics.std.to_val.
Notation dn_to_val := dyn_lang.definition.to_val.

Notation cc_of_to_val := grad_lang.dynamics.std.of_to_val.
Notation cc_to_of_val := grad_lang.dynamics.std.to_of_val.

Notation cc_fill_app := grad_lang.dynamics.lemmas.fill_app.

Section basic_lemmas.

  Context {ν : label} {Hν : NeverOccurs ν}.
  Lemma simul_expr_Invariant Γ (e : cc_expr) τ (de : Γ ⊢ e : τ) :
    Invariant e ⌜e⌝.
  Proof.
    induction de; simpl; try by constructor.
  Qed.

  Instance Var_Inj : Inj eq eq grad_lang.definition.Var. intros x1 x2 eq. by inversion eq. Qed.

  Lemma closed_Invariant e e' n : Invariant e e' →
      Closed_n n e → Closed_n n e'.
  Proof.
    intros HI.
    generalize dependent n.
    induction HI; intros; try by intros σ'; asimpl.
    - intros σ'.
      asimpl; f_equiv.
      rewrite IHHI1; auto; closed_solver.
      rewrite IHHI2; auto; closed_solver.
    - intros σ'.
      asimpl; f_equiv.
      rewrite IHHI1; auto; closed_solver.
      rewrite IHHI2; auto; closed_solver.
      rewrite IHHI3; auto; closed_solver.
    - intros σ'.
      asimpl; f_equiv.
      rewrite IHHI1; auto; closed_solver.
      rewrite IHHI2; auto; closed_solver.
    - apply ids_lt_Closed_n. apply ((@iffLR _ (x < n) $ ids_lt_Closed_n x n) H).
    - intros σ'. asimpl. rewrite IHHI; auto.
      closed_solver.
    - intros σ'.
      asimpl; f_equiv.
      rewrite IHHI1; auto; closed_solver.
      rewrite IHHI2; auto; closed_solver.
    - intros σ'.
      asimpl; f_equiv.
      rewrite IHHI; auto; closed_solver.
    - intros σ'.
      asimpl; f_equiv.
      rewrite IHHI; auto; closed_solver.
    - intros σ'. asimpl. rewrite IHHI1; auto.
      f_equiv.
      rewrite IHHI2; auto. closed_solver.
      rewrite IHHI3; auto. closed_solver.
      closed_solver.
    - intros σ'.
      asimpl; f_equiv.
      rewrite IHHI; auto; closed_solver.
    - intros σ'.
      asimpl; f_equiv.
      rewrite IHHI; auto; closed_solver.
    - intros σ'.
      asimpl; f_equiv.
      rewrite IHHI1; auto; closed_solver.
      rewrite IHHI2; auto; closed_solver.
    - intros σ'.
      asimpl; f_equiv. by rewrite cast'_closed.
      rewrite IHHI; auto. closed_solver.
    - intros σ'.
      asimpl; f_equiv. repeat f_equiv. by rewrite cast'_closed.
      rewrite IHHI; auto. eapply Closed_n_weaken; eauto. lia.
      by rewrite cast'_closed.
    - eapply Closed_n_weaken; eauto. lia.
    - intros σ; asimpl. repeat f_equiv.
      assert (S n = n + 1) as -> by lia. by rewrite upn_add HCe'.
  Qed.

  Lemma rtc_step_ne_step e e' : rtc step_ne e e' → rtc step_ne e e'.
  Proof. induction 1. constructor. eapply rtc_l; eauto. Qed.

  Lemma rtc_ne_step_bind K e v e' :
      rtc step_ne e (of_val v) → rtc step_ne (fill K (of_val v)) e' → rtc step_ne (fill K e) e'.
  Proof.
    intros. eapply rtc_transitive; eauto.
    eapply rtc_congruence; eauto. intros. by apply fill_step.
  Qed.

  Ltac bind := rw_fill; eapply rtc_ne_step_bind; eauto.
  Ltac refl := by eapply rtc_refl.
  Ltac take_step := eapply rtc_l; first by step_solver.

  (* Needed to prove that if initial goes to a value, so must alternative  *)
  Lemma left_val_Invariant e :
    ∀ e', Invariant e e' → ∀ τ (He : typed [] e τ) v (He : cc_to_val e = Some v), ∃ v', rtc step_ne e' (of_val v') ∧ Invariant e (dn_of_val v').
  Proof.
    intros e' I.
    induction I; intros τ Hτ w Hw; try by simplify_option_eq.
    - exists (LitV b). split; eauto. apply rtc_refl. constructor.
    - exists (LamV e'). split; eauto. apply rtc_refl. by constructor.
    - simplify_option_eq. rename H into v. inversion Hτ. simplify_eq.
      destruct (IHI _ H0 v ltac:(eauto)) as (w & Hs & Hw).
      exists (InjLV w). split. bind. refl. by constructor.
    - simplify_option_eq. rename H into v. inversion Hτ. simplify_eq.
      destruct (IHI _ H0 v ltac:(eauto)) as (w & Hs & Hw).
      exists (InjRV w). split. bind. refl. by constructor.
    - simplify_option_eq. rename H into v1. rename H0 into v2. inversion Hτ; simplify_eq.
      destruct (IHI1 τ1 H1 v1 ltac:(eauto)) as (w1 & Hs1 & Hw1).
      destruct (IHI2 τ2 H3 v2 ltac:(eauto)) as (w2 & Hs2 & Hw2).
      exists (PairV w1 w2). split. do 2 bind. refl. constructor; auto.
    - inversion Hτ; simplify_option_eq. rename H into v. destruct (IHI _ H5 v ltac:(auto)) as (v' & Hs & Hi).
      destruct τ1; try by inversion Hw; simplify_option_eq.
      + inversion H4; simplify_eq. exists v'.
        split. bind. take_step. refl.
        change (Base B) with (types.of_shape (S_Base B)).
        eapply (I_Cast_GroundUp _ _ e v); eauto.
        by erewrite cc_of_to_val. by eapply (typed_Closed []).
        eapply closed_Invariant; eauto. by eapply (typed_Closed []).
      + inversion H4; simplify_eq.
        * rewrite cast_upwards_rw /=.
          destruct (decide (τ1_1 = Unknown ∧ τ1_2 = Unknown)) as [[-> ->] | HHH]; simplify_eq.
          -- exists v'. split; auto. bind. take_step. refl.

             assert (Bin bin Unknown Unknown = (types.of_shape (S_Bin bin))) as -> by auto.
             econstructor; eauto.
             by erewrite cc_of_to_val. by eapply (typed_Closed []).
             eapply closed_Invariant; eauto. by eapply (typed_Closed []).
          -- destruct bin; by simplify_option_eq.
        * destruct bin; inversion Hw. simplify_option_eq.
          exists (LamV
               (App ν (of_val $ cast' ℓ τ1_2 τ2')
                  (App ν (of_val v')
                     (App ν (of_val $ cast' ℓ  τ1' τ1_1) (Var 0))))).
          split. bind. simpl.
          { rewrite cast_arrow_rw; auto.
            take_step. asimpl. repeat rewrite cast'_closed.
            assert (Closed (dn_of_val v')). eapply closed_Invariant; eauto.
            by eapply (typed_Closed []). rewrite H. refl. }
          simpl. eapply I_Cast_Arrow_Arrow; eauto.
          by erewrite cc_of_to_val. by eapply (typed_Closed []).
          eapply closed_Invariant; eauto. by eapply (typed_Closed []).
      + destruct τ; inversion Hw.
        destruct bin; inversion Hw.
        destruct τ1; inversion Hw.
        destruct τ2; inversion Hw. simplify_eq.
        exists (LamV (App ℓ (dn_of_val v') (Var 0))).
        split.
        { bind. rewrite /= cast_downwards_rw /= decide_True; auto.
          take_step. asimpl.
          assert (Closed (dn_of_val v')). eapply closed_Invariant; eauto.
          by eapply (typed_Closed []). rewrite H. refl. }
          eapply I_Cast_ArrowDown; eauto.
          by erewrite cc_of_to_val. by eapply (typed_Closed []).
          eapply closed_Invariant; eauto. by eapply (typed_Closed []).
    - eexists. split. change (Lam ?e) with (of_val (LamV e)). refl.
      econstructor; eauto.
    - inversion Hτ. simplify_eq.
      exists v'. split. refl. econstructor; eauto.
    - inversion Hτ. simplify_eq.
      eexists. split. change (Lam ?e) with (of_val (LamV e)). refl.
      econstructor; eauto.
  Qed.

  Lemma ren_gen_Invariant e1 e1'
    (H1 : Invariant e1 e1') :
    ∀ k l, Invariant e1.[upn l (ren (+k))] e1'.[upn l (ren (+k))].
  Proof.
    induction H1; (try by econstructor); intros k m; asimpl.
    - do 2 rewrite (iter_up m x (ren (+k))).
      destruct (lt_dec x m); asimpl; constructor.
    - constructor. apply IHInvariant.
    - constructor; eauto.
    - rewrite cast'_closed. constructor; eauto.
    - repeat rewrite cast'_closed. rewrite HCe HCe'.
      econstructor; eauto.
    - rewrite HCe HCe'. econstructor; eauto.
    - rewrite HCe HCe'. econstructor; eauto.
  Qed.

  Lemma ren_Invariant e1 e1'
    (H1 : Invariant e1 e1') :
    ∀ k, Invariant e1.[ren (+k)] e1'.[ren (+k)].
  Proof. intros. assert (A := ren_gen_Invariant _ _ H1 k 0). generalize A. by asimpl. Qed.

  Lemma subst_gen_Invariant e e' (HH: Invariant e e')
 es es' (Hs: Invariant es es')   :
    ∀ n, Invariant e.[upn n (es .: ids)] e'.[upn n (es' .: ids)].
  Proof.
    induction HH; intros n; asimpl; try by constructor.
    - rewrite (iter_up n x (es .: ids)) (iter_up n x (es' .: ids)).
      destruct (lt_dec x n); try by constructor.
      destruct (decide (x - n = 0)); asimpl. rewrite e. asimpl.
      by apply ren_Invariant.
      destruct (x - n). exfalso; lia. asimpl. constructor.
    - rewrite cast'_closed. constructor. apply IHHH.
    - rewrite  HCe HCe'. repeat rewrite cast'_closed.
      eapply I_Cast_Arrow_Arrow; eauto.
    - rewrite  HCe HCe'. econstructor; eauto.
    - rewrite  HCe HCe'. econstructor; eauto.
  Qed.

  (* closedness would probably enough here, but who cares *)
  Lemma val_shape_Invariant v τ (Hv : typed [] (cc_of_val v) τ) v' :
      Invariant (cc_of_val v) (of_val v') →
      grad_lang.dynamics.std.shape_val v = shape_val v'.
  Proof.
    intros I. destruct v; inversion I; simplify_eq.
    - by destruct v'; inversion H; simplify_eq.
    - by destruct v'; inversion H0; simplify_eq.
    - by destruct v'; inversion H0; simplify_eq.
    - by destruct v'; inversion H0; simplify_eq.
    - by destruct v'; inversion H0; simplify_eq.
    - inversion Hv; simplify_eq. simpl. clear G0 H1 H6.
      destruct G.
      + destruct v0; inversion H7; simplify_eq. inversion H3; simplify_eq.
        destruct v'0; inversion H; simplify_eq. destruct b; auto.
      + destruct bin.
        * destruct v0; inversion H7; simplify_eq.
          -- inversion H3; simplify_eq. by destruct v'0; simplify_eq.
          -- inversion H3; simplify_eq. destruct v'0; inversion H6.
             by destruct v'0; inversion H10.
          -- inversion H3; simplify_eq. destruct v'0; inversion H8.
             by destruct v'0; inversion H4.
        * destruct v0; inversion H7; simplify_eq.
          -- inversion H3; simplify_eq. by destruct v'0; simplify_eq.
          -- inversion H3; simplify_eq. by destruct v'0; inversion H0.
        * destruct v0; inversion H7; simplify_eq.
          inversion H3; simplify_eq. by destruct v'0; inversion H.
    - by destruct v'; inversion H0; simplify_eq.
    - by destruct v'; inversion H0; simplify_eq.
    - by destruct v'; inversion H0; simplify_eq.
    - by destruct v'; inversion H0; simplify_eq.
    - by destruct v'; inversion H.
  Qed.

  Lemma subst_Invariant e e' (HH: Invariant e e')
 es es' (Hs: Invariant es es')   :
    Invariant e.[es/] e'.[es'/].
  Proof. intros. assert (A := subst_gen_Invariant _ _ HH _ _ Hs 0). generalize A. by asimpl. Qed.

End basic_lemmas.
