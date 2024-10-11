From main.prelude Require Import imports base_lang tactics.
From main.cast_calc Require Import definition dynamics.std.

Lemma fill_app K K' e : fill (K ++ K') e = fill K (fill K' e).
Proof.
  generalize dependent e.
  induction K; auto.
  intro e. simpl. by rewrite IHK.
Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma head_step_not_val e1 e2 :
  head_step e1 e2 → to_val e1 = None.
Proof.
  destruct 1; destruct Hs; auto; (try done);
    simplify_option_eq; (try done).
  destruct (_ : shape); [ | destruct (_ : bin_const) ]; simplify_option_eq; auto.
  - destruct G1. destruct b; simplify_option_eq; destruct G2; simplify_option_eq; try done;
    destruct bin; auto; by exfalso.
    destruct bin; simplify_option_eq; destruct G2; simplify_option_eq; (try destruct bin); done.
  - destruct τ; (try destruct bin); auto.
  - destruct τ; (try destruct bin); auto. destruct τ1, τ2; auto. by exfalso.
Qed.

Lemma fill_item_not_val Ki e :
  to_val e = None → to_val (fill_item Ki e) = None.
Proof. intros. by destruct Ki; simpl; (try rewrite to_of_val); auto; simplify_option_eq. Qed.

Lemma fill_not_val K :
  ∀ e, to_val e = None → to_val (fill K e) = None.
Proof.
  induction K as [|Ki K] using rev_ind ; auto. intros.
  rewrite /fill foldr_snoc /=. fold (fill K (fill_item Ki e)).
  apply IHK. by apply fill_item_not_val.
Qed.

Lemma step_no_val e1 e2 :
  step e1 e2 → to_val e1 = None.
Proof.
  destruct 1; auto. apply fill_not_val.
  by eapply head_step_not_val. by apply fill_not_val.
Qed.

Instance fill_inj K : Inj (=) (=) (fill K).
Proof.
  induction K as [| Ki K IH]; rewrite /Inj; naive_solver.
Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Instance Var_Inj : Inj eq eq Var. intros x1 x2 eq. by inversion eq. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
  repeat match goal with
          | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
          end; auto.
Qed.

Lemma pure_step_by_val' K K' e1 e1' ℓ :
  fill K e1 = fill K' e1' →
  to_val e1 = None →
  (e1' = Error ℓ) →
  ∃ K'', K' = K ++ K''.
Proof.
  intros Hfill Hred ->.
  revert K' Hfill.
  induction K as [|Ki K IH]=> /= K' Hfill; eauto using app_nil_l.
  destruct K' as [|Ki' K']; simplify_eq/=.
  { assert (H := (fill_not_val K _ Hred)).
    destruct Ki; inversion Hfill. }
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_val_inj, Hfill.
    by apply fill_not_val. apply fill_not_val. auto.
  }
  simplify_eq. destruct (IH K') as [K'' ->]; auto. by exists K''.
Qed.

Lemma pure_head_ctx_step_val Ki e e2 :
  head_step (fill_item Ki e) e2 → is_Some (to_val e).
Proof.
  intros H. invclear H; invclear Hs; simplify_eq; destruct Ki; simplify_option_eq; try by eexists; eauto.
  destruct G; (try destruct bin); simplify_option_eq; eexists; eauto.
  destruct G1; (try destruct bin); simplify_option_eq; eexists; eauto.
  destruct G; (try destruct bin); simplify_option_eq; eexists; eauto.
Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  revert e. induction K as [|Ki K IHK] using rev_ind; first by simpl.
  intros e pev. apply fill_item_val with (Ki := Ki).
  apply IHK. rewrite fill_app in pev. by simpl.
Qed.

Lemma pure_step_by_val K K' e1 e1' e2 :
  fill K e1 = fill K' e1' →
  to_val e1 = None →
  head_step e1' e2 →
  ∃ K'', K' = K ++ K''.
Proof.
  intros Hfill Hred Hstep.
  revert K' Hfill.
  induction K as [|Ki K IH]=> /= K' Hfill; eauto using app_nil_l.
  destruct K' as [|Ki' K']; simplify_eq/=.
  { apply pure_head_ctx_step_val in Hstep.
    apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
  (* change (fill_item ?Ki (fill ?K ?e)) with (fill (Ki :: K) e) in Hfill. *)
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_val_inj, Hfill.
    by apply fill_not_val. apply fill_not_val.  eauto using head_step_not_val. }
  simplify_eq. destruct (IH K') as [K'' ->]; auto. by exists K''.
Qed.

Lemma head_step_det e e1 e2 : head_step e e1 → head_step e e2 → e1 = e2.
Proof.
  intros H1 H2.
  invclear H1.
  - invclear H2.
    + try by invclear Hs; invclear Hs0.
    + exfalso.
      try by invclear Hs; invclear Hs0.
  - invclear H2.
    + exfalso. try by invclear Hs; invclear Hs0.
    + invclear Hs; invclear Hs0; try done.
      * destruct G; invclear H1.
      * destruct G2; invclear H1.
      * destruct G; invclear H3.
      * destruct G1; destruct G2; simplify_eq.
      * destruct G; destruct G0; simplify_eq.
      * destruct G2; invclear H4.
      * destruct G; destruct G1; destruct G2; simplify_eq.
      * destruct G2; invclear H7.
      * destruct G; destruct G0; auto; try by destruct bin; destruct b; simplify_eq.
        by destruct bin; destruct bin0; simplify_eq.
      * destruct G0; inversion H0. repeat rewrite decide_True in H3; auto.
        simplify_eq.
      * destruct G2; inversion H0. repeat rewrite decide_True in H3; auto.
        simplify_eq.
Qed.

Lemma fill_item_Error_head_step_false Ki ℓ eh' : head_step (fill_item Ki (Error ℓ)) eh' → False.
Proof. intros Hs. invclear Hs; invclear Hs0; destruct Ki; simplify_eq; try by invclear H. Qed.

Lemma fill_Error_head_step_false K ℓ eh' : head_step (fill K (Error ℓ)) eh' → False.
Proof.
  destruct K as [| Ki K].
  intros Hs. invclear Hs; invclear Hs0; simplify_eq.
  simpl. intros abs.
  destruct (pure_head_ctx_step_val _ _ _ abs) as [v abs'].
  rewrite (fill_not_val K) in abs'; simplify_eq. auto.
Qed.

Lemma step_det e e1 e2 : step e e1 → step e e2 → e1 = e2.
Proof.
  intros H1 H2.
  invclear H1; invclear H2.
  - assert (K = K0) as <-.
    { destruct (pure_step_by_val K0 K e_h0 e_h e_h' H0 ltac:(by eapply head_step_not_val) ltac:(eauto)) as [Kred eq].
      destruct (pure_step_by_val K K0 _ _ e_h'0 (eq_Symmetric _ _ H0) ltac:(by eapply head_step_not_val) ltac:(eauto)) as [Kred' eq'].
      assert (H: length K = length ((K ++ Kred') ++ Kred)). by rewrite -eq' eq. rewrite -app_assoc app_length app_length in H.
      destruct Kred'; [ | exfalso; simpl in *; lia ]. destruct Kred; [ | exfalso; simpl in *; lia ].
      by rewrite app_nil_r in eq. }
    f_equal. rewrite (fill_inj K _ _ H0) in HS0. by eapply head_step_det.
  - exfalso.
    destruct (pure_step_by_val' K K0 e_h (Error ℓ) ltac:(eauto) (eq_Symmetric _ _ H) ltac:(by eapply head_step_not_val)) as [Kred eq]; auto. simplify_eq.
    rewrite fill_app in H.
    assert (fill Kred (Error ℓ) = e_h). eapply fill_inj. apply H. simplify_eq.
    by eapply fill_Error_head_step_false.
  - exfalso.
    destruct (pure_step_by_val' K0 K e_h (Error ℓ) ltac:(eauto) (H1) ltac:(by eapply head_step_not_val)) as [Kred eq]; auto. simplify_eq.
    rewrite fill_app in H1.
    assert (e_h = fill Kred (Error ℓ)). eapply fill_inj. apply H1. simplify_eq.
    by eapply fill_Error_head_step_false.
  - destruct (pure_step_by_val' K K0 (Error ℓ) (Error ℓ0) ℓ0 ltac:(eapply (eq_Symmetric _ _ H0)) ltac:(eauto) ltac:(eauto)) as [Kred eq].
    destruct (pure_step_by_val' K0 K (Error ℓ0) (Error ℓ) ℓ H0 ltac:(eauto) ltac:(eauto)) as [Kred' eq'].

    simplify_eq.
    assert (length (Kred') = 0).
    { assert (length K0 = length ((K0 ++ Kred') ++ Kred)). by rewrite -eq.
      destruct Kred; destruct Kred';
      repeat rewrite app_length /= in H2; auto; lia.
    }
    destruct Kred'; destruct Kred; simplify_eq. simpl in *.
    rewrite app_nil_r in H0. by eapply fill_inj.
    rewrite app_nil_r in H0. by eapply fill_inj.
Qed.

Require Import main.prelude.autosubst.
From main.cast_calc Require Import definition typing.

Lemma typed_Closed Γ e τ (de : Γ ⊢ e : τ) : Closed_n (length Γ) e.
Proof.
  induction de; intros σ; try by asimpl; (try by f_equal).
  rewrite ids_subst_no; auto.  by eapply lookup_lt_Some.
Qed.

Lemma context_gen_weakening ξ Γ' Γ e τ :
  Γ' ++ Γ ⊢ e : τ →
  Γ' ++ ξ ++ Γ ⊢ e.[upn (length Γ') (ren (+ (length ξ)))] : τ.
Proof.
  intros H1.
  remember (Γ' ++ Γ) as Ξ. revert Γ' Γ ξ HeqΞ.
  induction H1 => Γ1 Γ2 ξ HeqΞ; subst; asimpl in *; eauto using typed.
  - rewrite iter_up; destruct lt_dec as [Hl | Hl].
    + constructor. rewrite lookup_app_l; trivial. by rewrite lookup_app_l in H.
    + asimpl. constructor. rewrite lookup_app_r; auto with lia.
      rewrite lookup_app_r; auto with lia.
      rewrite lookup_app_r in H; auto with lia.
      match goal with
        |- _ !! ?A = _ => by replace A with (x - length Γ1) by lia
      end.
  - econstructor; eauto. by apply (IHtyped (_::_)).
  - econstructor; eauto. by apply (IHtyped2 (_::_)). by apply (IHtyped3 (_::_)).
Qed.

Lemma context_weakening ξ Γ e τ :
  Γ ⊢ e : τ → ξ ++ Γ ⊢ e.[(ren (+ (length ξ)))] : τ.
Proof. eapply (context_gen_weakening _ []). Qed.

Lemma typed_nil e τ : [] ⊢ e : τ  → ∀Γ, Γ ⊢ e : τ.
Proof.
  intros de Γ. replace Γ with (Γ ++ []) by by rewrite app_nil_r.
  replace e with e.[ren (+ (length Γ))]. by apply context_weakening.
  by rewrite (typed_Closed _ _ _ de).
Qed.

Lemma typed_gen_subst Γ1 Γ2 e1 τ1 e2 τ2 :
  Γ1 ++ τ2 :: Γ2 ⊢ e1 : τ1 →
  Γ2 ⊢ e2 : τ2 →
  Γ1 ++ Γ2 ⊢ e1.[upn (length Γ1) (e2 .: ids)] : τ1.
Proof.
  remember (Γ1 ++ τ2 :: Γ2) as ξ. intros Ht. revert Γ1 Γ2 e2 τ2 Heqξ.
  induction Ht => Γ1 Γ2 oe2 oτ2 Heqξ; asimpl in *; eauto using typed.
  - subst. rewrite iter_up; destruct lt_dec as [Hl | Hl].
    + econstructor.
      match goal with
        H : _ !! _ = Some _ |- _ => revert H
      end.
      rewrite !lookup_app_l; auto.
    + asimpl. remember (x - length Γ1) as n. destruct n.
       * match goal with
           H : (Γ1 ++ oτ2 :: Γ2) !! x = Some τ |- _ =>
           rewrite lookup_app_r in H; auto with lia; rewrite -Heqn in H;
             inversion H; subst
         end.
         by apply context_weakening.
       * asimpl.
         match goal with
           H : (Γ1 ++ oτ2 :: Γ2) !! x = Some τ |- _ =>
           rewrite lookup_app_r in H; auto with lia; rewrite -Heqn in H;
             inversion H; subst
         end.
         change (ids (length Γ1 + n)) with (@ids expr _ n).[ren (+(length Γ1))].
         by apply context_weakening; constructor.
  - econstructor; eauto.
    eapply (IHHt (_ :: _)); eauto; by simpl; f_equal.
  - econstructor; eauto.
    + eapply (IHHt2 (_ :: _)); eauto; by simpl; f_equal.
    + eapply (IHHt3 (_ :: _)); eauto; by simpl; f_equal.
Qed.

Lemma typed_subst Γ2 e1 τ1 e2 τ2 :
  τ2 :: Γ2 ⊢ e1 : τ1 → Γ2 ⊢ e2 : τ2 → Γ2 ⊢ e1.[e2/] : τ1.
Proof. apply (typed_gen_subst []). Qed.

Lemma preservation_head_step Γ e e' τ : typed Γ e τ → head_step e e' → typed Γ e' τ.
Proof.
  intros He Hs.
  inversion_clear Hs.
  - inversion Hs0; simplify_eq.
    + by inversion He.
    + inversion He; by destruct b.
    + inversion He; simplify_eq. destruct op; simpl; constructor.
    + inversion He; simplify_eq. inversion_clear H3.
      eapply typed_subst; eauto.
      by erewrite of_to_val.
    + inversion He; simplify_eq. inversion_clear H3.
      eapply typed_subst; eauto.
      by erewrite of_to_val.
    + inversion He; simplify_eq. by inversion_clear H2.
    + inversion He; simplify_eq. by inversion_clear H2.
    + inversion He; simplify_eq.
      eapply typed_subst; eauto. by inversion H2.
  - inversion Hs0; simplify_eq; try by inversion He.
    + inversion_clear He. by inversion_clear H2.
    + constructor.
    + destruct G; eauto. constructor. destruct bin; try by constructor.
      inversion He. simplify_eq. inversion H3. simplify_eq. inversion H10. simplify_eq.
      econstructor; eauto.
    + inversion He. simplify_eq.
      inversion H3. simplify_eq.
      constructor. inversion H4; simplify_eq. auto.
      eapply App_typed. eauto. eapply Cast_typed.
      inversion H4. simplify_eq. by apply consistency_sym. auto.
    + inversion He. simplify_eq. inversion H6; simplify_eq.
      inversion H7; simplify_eq.
      constructor; eauto. constructor; eauto.
      constructor; eauto.
    + inversion He. simplify_eq. inversion H6; simplify_eq.
      inversion H5; simplify_eq.
      constructor; eauto. constructor; eauto.
    + inversion He. simplify_eq. inversion H6; simplify_eq.
      inversion H5; simplify_eq.
      constructor; eauto. constructor; eauto.
    + inversion He. simplify_eq.
      constructor; auto. constructor.
      constructor; auto.
      destruct G.
      * destruct τ0; inversion H. simpl in H.
        destruct τ0_1; try by inversion H.
        destruct τ0_2; try by inversion H.
      * simpl.
        destruct τ0; inversion H.
        destruct τ0_1; try by inversion H.
        inversion H. simplify_eq. repeat constructor.
        inversion H. simplify_eq. repeat constructor.
        destruct τ0_2; try by inversion H2.
        inversion H. simplify_eq. repeat constructor.
        inversion H. simplify_eq.
        repeat constructor. inversion H3.
    + inversion He. simplify_eq. constructor.
      * destruct τ; simplify_eq.
        destruct G; simplify_eq.
        inversion H.
        destruct τ1; inversion H3.
        destruct τ2; inversion H3. simpl in H.
        destruct τ1; inversion H.
        simplify_eq. simpl. repeat constructor.
        simpl. repeat constructor.
        simpl.
        destruct τ2; inversion H; simplify_eq; repeat constructor.
      * constructor; auto.
        destruct τ; inversion H.
        destruct τ1; inversion H3; repeat constructor.
Qed.

Definition typed_ectx_item (Ki : ectx_item) Γ τ τ' : Prop := (* evaluation context do not generate extre free variables *)
  ∀ e, Γ ⊢ e : τ → Γ ⊢ (fill_item Ki e) : τ'.

Lemma ectx_item_decompose Ki e Γ τ' : Γ ⊢ fill_item Ki e : τ' →
  ∃ τ, Γ ⊢ e : τ ∧ typed_ectx_item Ki Γ τ τ'.
Proof.
  intros. destruct Ki; simpl in H; simpl;
    (inversion H; simplify_eq; eexists  _; split; eauto; by econstructor).
Qed.

Definition typed_ectx (Ki : ectx) Γ τ τ' : Prop :=
  ∀ e, Γ ⊢ e : τ → Γ ⊢ (fill Ki e) : τ'.

Lemma ectx_decompose K e Γ τ' : Γ ⊢ fill K e : τ' →
  ∃ τ, Γ ⊢ e : τ ∧ typed_ectx K Γ τ τ'.
Proof.
  generalize dependent e.
  generalize dependent K. induction K as [|Ki K] using rev_ind; intros.
  - exists τ'. split; auto; try by econstructor. by intros e'.
  - rewrite fill_app in H. specialize (IHK (fill [Ki] e) H).
    destruct IHK as (τ & HKie & HK).
    simpl in HKie.
    destruct (ectx_item_decompose _ _ _ _ HKie) as (τ'' & He & HKi).
    exists τ''. split; auto. intros t Ht. rewrite fill_app. apply HK. by apply HKi.
Qed.

Lemma preservation Γ e e' τ : typed Γ e τ → step e e' → typed Γ e' τ.
Proof.
  intros He Hs. destruct Hs; try by constructor.
  destruct (ectx_decompose _ _ _ _ He) as (τ' & Hd & HHH).
  apply HHH.
  eapply preservation_head_step; eauto.
Qed.

Lemma typed_shape G v : [] ⊢ (of_val v) : types.of_shape G → shape_val v = G.
Proof.
  intros H. destruct v; invclear H.
  - destruct G; invclear H2.
    by destruct b.
  - by destruct G; invclear H1.
  - by destruct G; invclear H5.
  - destruct G; invclear H5.
  - by destruct G; invclear H5.
  - by destruct G; invclear H1.
  - by destruct G; invclear H1.
  - by destruct G; invclear H2.
Qed.

(* step that is "not propagating" (i.e. not otf K[error] → error) *)
Definition step_np (e e' : expr) : Prop :=
    ∃ (K : ectx) e_h e_h', e = fill K e_h ∧ e' = fill K e_h' ∧ head_step e_h e_h'.

Lemma step_np_step (e e' : expr) :
    step_np e e' → step e e'.
Proof. intros H. destruct H as (K & e_h & e_h' & -> & -> & Hs). by econstructor. Qed.

Inductive Progress e : Prop :=
  | IsVal v (H : e = of_val v)
  | IsKError K ℓ (H : e = fill K (Error ℓ))
  | TakesStep e' (H : step_np e e').

Ltac rw_of_val :=
  repeat (
      repeat change (Lam ?e) with (of_val $ LamV e);
      repeat change (Lit ?b) with (of_val $ LitV b);
      repeat change (InjL (of_val ?v)) with (of_val $ InjLV v);
      repeat change (InjR (of_val ?v)) with (of_val $ InjRV v);
      repeat change (Pair (of_val ?v) (of_val ?w)) with (of_val $ PairV v w)
    ).

Ltac rw_fill_item :=
  simpl;
  rw_of_val;
  (repeat (
      repeat change (App (of_val ?v) ?e) with (fill_item (AppRCtx v) e);
      repeat change (App ?e1 ?e2) with (fill_item (AppLCtx e2) e1);
      repeat change (Pair (of_val ?v1) ?e2) with (fill_item (PairRCtx v1) e2);
      repeat change (Pair ?e1 ?e2) with (fill_item (PairLCtx e2) e1);
      repeat change (Fst ?e) with (fill_item (FstCtx ) e);
      repeat change (Snd ?e) with (fill_item (SndCtx ) e);
      repeat change (InjL ?e) with (fill_item InjLCtx e);
      repeat change (InjR ?e) with (fill_item InjRCtx e);
      repeat change (Case ?e1 ?e2 ?e3) with (fill_item (CaseCtx e2 e3) e1);
      repeat change (If ?e1 ?e2 ?e3) with (fill_item (IfCtx e2 e3) e1);
      repeat change (BinOp ?op (of_val ?v1) ?e2) with (fill_item (BinOpRCtx op v1) e2);
      repeat change (BinOp ?op ?e1 ?e2) with (fill_item (BinOpLCtx op e2) e1);
      repeat change (Seq ?e1 ?e2) with (fill_item (SeqCtx e2) e1);
      repeat change (Cast ?ℓ ?τ1 ?τ2 ?e) with (fill_item (CastCtx ℓ τ1 τ2) e)
    )).


Ltac rw_fill := (* for e.g. bind lemmas *)
  rw_fill_item;
  (change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 (fill_item ?Ki4 (fill_item ?Ki5 (fill_item ?Ki6 ?e))))))
    with (fill [Ki1 ; Ki2 ; Ki3 ; Ki4; Ki5; Ki6] e);
   change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 (fill_item ?Ki4 (fill_item ?Ki5 ?e)))))
     with (fill [Ki1 ; Ki2 ; Ki3 ; Ki4 ; Ki5] e);
   change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 (fill_item ?Ki4 ?e))))
     with (fill [Ki1 ; Ki2 ; Ki3 ; Ki4] e);
   change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 ?e)))
     with (fill [Ki1 ; Ki2 ; Ki3] e);
   change (fill_item ?Ki1 (fill_item ?Ki2 ?e))
     with (fill [Ki1; Ki2] e);
   change (fill_item ?Ki ?e)
     with (fill [Ki] e)
  ).


Lemma step_np_fill e1 e2 K : step_np e1 e2 → step_np (fill K e1) (fill K e2).
Proof. intros. destruct H as (K' & e_h & e_h' & -> & -> & Hh). repeat rewrite -fill_app. by eexists; eauto. Qed.

Lemma progress e τ Γ (Heτ : Γ ⊢ e : τ) :
  Γ = [] → Progress e.
Proof.
  intros eq. induction Heτ; simplify_eq;
    repeat (lazymatch goal with | H : [] = [] → _ |- _ => (specialize (H ltac:(auto))) end).
  - eapply IsVal. by rw_of_val.
  - inversion IHHeτ1 as [v1 -> | K ℓ -> | e1' Hs1 ].
    + destruct v1; invclear Heτ1. destruct b; invclear H.
      eapply TakesStep; eexists [], _, _; repeat split; eauto; repeat constructor.
    + eapply IsKError; rw_fill; rewrite -fill_app; eauto.
    + eapply TakesStep; rw_fill; by eapply step_np_fill.
  - inversion IHHeτ1 as [v1 -> | K ℓ -> | e1' Hs1 ].
    + destruct v1; invclear Heτ1. destruct b; invclear H.
      eapply TakesStep; eexists [], _, _; repeat split; eauto; repeat constructor.
    + eapply IsKError; rw_fill; rewrite -fill_app; eauto.
    + eapply TakesStep; rw_fill; by eapply step_np_fill.
  - inversion IHHeτ1 as [v1 -> | K ℓ -> | e1' Hs1 ].
    + destruct v1; invclear Heτ1. destruct b; invclear H.
      inversion IHHeτ2 as [v2 -> | K ℓ -> | e2' Hs2 ].
      * destruct v2; invclear Heτ2. destruct b; invclear H.
        eapply TakesStep. eexists [], _, _; repeat split; eauto; repeat constructor.
      * eapply IsKError; rw_fill; rewrite -fill_app; eauto.
      * eapply TakesStep; rw_fill; by eapply step_np_fill.
    + eapply IsKError; rw_fill; rewrite -fill_app; eauto.
    + eapply TakesStep; rw_fill; by eapply step_np_fill.
  - eapply IsVal; rw_of_val; eauto.
  - inversion IHHeτ1 as [v1 -> | K ℓ -> | e1' Hs1 ].
    + inversion IHHeτ2 as [v2 -> | K ℓ -> | e2' Hs2 ].
      * destruct v1; invclear Heτ1.
        -- eapply TakesStep. eexists [], _, _; repeat split.
           apply HN_No_Cast. econstructor. by rewrite to_of_val.
        -- eapply TakesStep. eexists [], _, _. repeat split.
           apply HN_Cast. econstructor; by rewrite to_of_val.
        -- destruct v1; invclear H6. simpl.
           eapply TakesStep.
           eexists [], _, _. repeat split; eauto.
           apply HN_Cast.
           eapply HN_Cast_GG_App; by rewrite to_of_val.
      * eapply IsKError; rw_fill; rewrite -fill_app; eauto.
      * eapply TakesStep; rw_fill; by eapply step_np_fill.
    + eapply IsKError; rw_fill; rewrite -fill_app; eauto.
    + eapply TakesStep; rw_fill; by eapply step_np_fill.
  - inversion IHHeτ1 as [v1 -> | K ℓ -> | e1' Hs1 ].
    + inversion IHHeτ2 as [v2 -> | K ℓ -> | e2' Hs2 ].
      * eapply IsVal. by rw_of_val.
      * eapply IsKError; rw_fill; rewrite -fill_app; eauto.
      * eapply TakesStep; rw_fill; by eapply step_np_fill.
    + eapply IsKError; rw_fill; rewrite -fill_app; eauto.
    + eapply TakesStep; rw_fill; by eapply step_np_fill.
  - inversion IHHeτ as [v -> | K ℓ -> | e' Hs ].
    + destruct v; invclear Heτ.
      eapply TakesStep; eexists [], _, _; repeat split; eauto; repeat econstructor; by rewrite to_of_val.
    + eapply IsKError; rw_fill; rewrite -fill_app; eauto.
    + eapply TakesStep; rw_fill; by eapply step_np_fill.
  - inversion IHHeτ as [v -> | K ℓ -> | e' Hs ].
    + destruct v; invclear Heτ.
      eapply TakesStep; eexists [], _, _; repeat split; eauto; repeat econstructor; by rewrite to_of_val.
    + eapply IsKError; rw_fill; rewrite -fill_app; eauto.
    + eapply TakesStep; rw_fill; by eapply step_np_fill.
  - inversion IHHeτ as [v -> | K ℓ -> | e' Hs ].
    + eapply IsVal. by rw_of_val.
    + eapply IsKError; rw_fill; rewrite -fill_app; eauto.
    + eapply TakesStep; rw_fill; by eapply step_np_fill.
  - inversion IHHeτ as [v -> | K ℓ -> | e' Hs ].
    + eapply IsVal. by rw_of_val.
    + eapply IsKError; rw_fill; rewrite -fill_app; eauto.
    + eapply TakesStep; rw_fill; by eapply step_np_fill.
  - inversion IHHeτ1 as [v1 -> | K ℓ -> | e1' Hs1 ].
    + destruct v1; invclear Heτ1;
      eapply TakesStep; eexists [], _, _; repeat split; eauto; repeat econstructor; by rewrite to_of_val.
    + eapply IsKError; rw_fill; rewrite -fill_app; eauto.
    + eapply TakesStep; rw_fill; by eapply step_np_fill.
  - inversion IHHeτ as [v -> | K ℓ' -> | e' Hs ].
    + invclear H.
      * destruct τ1; simplify_eq.
        -- by apply (IsVal _ (CastGroundUpV ℓ (S_Base B) v)).
        -- destruct (decide (τ1_1 = Unknown ∧ τ1_2 = Unknown)) as [[-> ->] | neq ].
           ++ by apply (IsVal _ (CastGroundUpV ℓ (S_Bin bin) v)).
           ++ eapply TakesStep; eexists [], _, _; repeat split; eauto.
              apply HN_Cast. eapply HN_Cast_Ground; try by rewrite to_of_val.
              destruct τ1_1; destruct τ1_2; eauto.
              exfalso. by apply neq.
              destruct bin; auto.
              destruct τ1_1; destruct τ1_2; eauto; try by simplify_option_eq.
              exfalso. by apply neq.
              destruct τ1_1; destruct τ1_2; eauto; try by simplify_option_eq.
              exfalso. by apply neq.
              destruct τ1_1; destruct τ1_2; eauto; try by simplify_option_eq.
              exfalso. by apply neq.
        -- eapply TakesStep. eexists [], _, _; repeat split; eauto.
           apply HN_Cast. econstructor. by rewrite to_of_val.
      * destruct τ2; simplify_eq.
        -- destruct v; invclear Heτ. simpl.
           change (Base B) with (of_shape (S_Base B)).
           destruct (decide (G = S_Base B)) as [-> | neq].
           ++ eapply TakesStep. eexists [], _, _; repeat split; eauto.
              apply HN_Cast. eapply HN_Cast_GG_Succeed. auto. by rewrite to_of_val.
           ++ eapply TakesStep. eexists [], _, _; repeat split; eauto.
              apply HN_Cast. eapply HN_Cast_GG_Fail; auto. by rewrite to_of_val.
        -- destruct (decide (τ2_1 = Unknown ∧ τ2_2 = Unknown)) as [[-> ->] | neq ].
           ++ change (Bin bin Unknown Unknown) with (of_shape (S_Bin bin)).
              destruct (decide (bin = Arrow)) as [-> | neq].
              ** by apply (IsVal _ (CastArrowDownV ℓ v)).
              ** destruct v; invclear Heτ.
                 destruct (decide (G = (S_Bin bin))) as [-> | neq'].
                 --- eapply TakesStep. eexists [], _, _; repeat split; eauto.
                     apply HN_Cast. eapply HN_Cast_GG_Succeed; auto. intros abs. exfalso. apply neq. by inversion abs.
                     by rewrite to_of_val.
                 --- eapply TakesStep. eexists [], _, _; repeat split; eauto.
                     apply HN_Cast. eapply HN_Cast_GG_Fail; auto. intros abs. exfalso. apply neq. by inversion abs.
                     by rewrite to_of_val.
           ++ eapply TakesStep. eexists [], _, _; repeat split; eauto.
              apply HN_Cast. econstructor.
              destruct τ2_1; destruct τ2_2; eauto; try by simplify_option_eq.
              exfalso. by apply neq.
              destruct τ2_1; destruct τ2_2; eauto; try by simplify_option_eq.
              exfalso. by apply neq.
              by rewrite to_of_val.
        -- eapply TakesStep. eexists [], _, _; repeat split; eauto.
           apply HN_Cast. econstructor. by rewrite to_of_val.
      * eapply TakesStep. eexists [], _, _; repeat split; eauto.
        apply HN_Cast. econstructor. by rewrite to_of_val.
      * destruct bin.
        -- destruct v; invclear Heτ.
           ++ by eapply (IsVal _ (CastArrowV _ _ _ _ _ (LamV e))).
           ++ by eapply (IsVal _ (CastArrowV _ _ _ _ _ (CastArrowV ℓ0 τ1 τ2 τ0 τ3 v))).
           ++ by eapply (IsVal _ (CastArrowV _ _ _ _ _ (CastArrowDownV ℓ0 v))).
        -- destruct v; invclear Heτ.
           ++ eapply TakesStep. eexists [], _, _; repeat split; eauto.
              apply HN_Cast. econstructor. by rewrite to_of_val.
           ++ eapply TakesStep. eexists [], _, _; repeat split; eauto.
              apply HN_Cast. econstructor. by rewrite to_of_val.
        -- destruct v; invclear Heτ.
           eapply TakesStep. eexists [], _, _; repeat split; eauto.
           apply HN_Cast. econstructor; by rewrite to_of_val.
    + rw_fill. rewrite -fill_app. by eapply IsKError.
    + eapply TakesStep; rw_fill; by eapply step_np_fill.
  - eapply (IsKError _ []); eauto.
Qed.

Definition diverging (e : expr) : Prop :=
  ∀ n, ∃ e', nsteps step n e e'.

Definition terminating (e : expr) v : Prop :=
  rtc step e (of_val v).

Definition erroring (e : expr) ℓ : Prop :=
  rtc step e (Error ℓ).

Lemma eval_possibilities e τ (Heτ : [] ⊢ e : τ) :
  ∀ n,
  (∃ e', nsteps step_np n e e' ∧ [] ⊢ e' : τ) ∨
  (∃ m K ℓ, m ≤ n ∧ nsteps step_np m e (fill K (Error ℓ))) ∨
  (∃ m v, m ≤ n ∧ nsteps step_np m e (of_val v)).
Proof.
  intros n. induction n; [ left; exists e; split; auto; constructor | ].
  destruct IHn as [Hdivn | [(m & K & ℓ & Hmn & Hsteps) | (m & v & Hmn & Hsteps)]].
  - destruct Hdivn as (en & Hstep & Henτ).
    destruct (progress _ _ _ Henτ ltac:(auto)) as [ v eq | K ℓ eq | e' Hstep' ].
    + right. right. exists n, v. split; [lia|]. by rewrite -eq.
    + right. left. exists n, K, ℓ. split; [lia|]. by rewrite -eq.
    + left. exists e'. split; auto. by eapply nsteps_r. eapply preservation; eauto.
      destruct Hstep' as (K & eh & eh' & -> & -> & Hh). by apply S_Normal.
  - right. left. exists m, K, ℓ. by split; [lia|].
  - right. right. exists m, v. by split; [lia|].
Qed.
