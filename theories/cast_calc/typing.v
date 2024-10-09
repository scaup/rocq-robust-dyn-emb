From main.prelude Require Import base_lang imports autosubst tactics.
From main.grad_lang Require Import types.
From main.cast_calc Require Import definition lemmas.

Definition binop_res_type (op : bin_op) : type :=
  Base match op with
  | PlusOp => Int | MinusOp => Int
  | EqOp => Bool | LeOp => Bool | LtOp => Bool
  end.

Reserved Notation "Γ ⊢ e : τ" (at level 74, e, τ at next level).

Inductive typed (Γ : list type) : expr → type → Prop :=
 | Var_typed x τ : Γ !! x = Some τ → Γ ⊢ Var x : τ
 | Base_typed b : Γ ⊢ Lit b : base_lit_type b
 | Seq_typed e1 e2 τ :
     Γ ⊢ e1 : Base Unit → Γ ⊢ e2 : τ → Γ ⊢ Seq e1 e2 : τ
 | If_typed e0 e1 e2 τ :
    Γ ⊢ e0 : Base Bool → Γ ⊢ e1 : τ → Γ ⊢ e2 : τ → Γ ⊢ If e0 e1 e2 : τ
 | BinOp_typed op e1 e2 :
     Γ ⊢ e1 : Base Int → Γ ⊢ e2 : Base Int → Γ ⊢ BinOp op e1 e2 : binop_res_type op
 (* functions *)
 | Lam_typed e τ1 τ2 :
    τ1 :: Γ ⊢ e : τ2 → Γ ⊢ Lam e : Bin Arrow τ1 τ2
 | App_typed e1 e2 τ1 τ2 :
    Γ ⊢ e1 : Bin Arrow τ1 τ2 → Γ ⊢ e2 : τ1 → Γ ⊢ App e1 e2 : τ2
 (* pairs *)
 | Pair_typed e1 e2 τ1 τ2 :
    Γ ⊢ e1 : τ1 → Γ ⊢ e2 : τ2 → Γ ⊢ Pair e1 e2 : Bin Product τ1 τ2
 | Fst_typed e τ1 τ2 : Γ ⊢ e : Bin Product τ1 τ2 → Γ ⊢ Fst e : τ1
 | Snd_typed e τ1 τ2 : Γ ⊢ e : Bin Product τ1 τ2 → Γ ⊢ Snd e : τ2
 (* sums *)
 | InjL_typed e τ1 τ2 : Γ ⊢ e : τ1 → Γ ⊢ InjL e : Bin Sum τ1 τ2
 | InjR_typed e τ1 τ2 : Γ ⊢ e : τ2 → Γ ⊢ InjR e : Bin Sum τ1 τ2
 | Case_typed e0 e1 e2 τ1 τ2 τ3 :
    Γ ⊢ e0 : Bin Sum τ1 τ2 → τ1 :: Γ ⊢ e1 : τ3 → τ2 :: Γ ⊢ e2 : τ3 →
    Γ ⊢ Case e0 e1 e2 : τ3
 (* assert! *)
 | Cast_typed ℓ τ1 τ2 (H : consistency τ1 τ2) e :
    Γ ⊢ e : τ1 → Γ ⊢ Cast ℓ τ1 τ2 e : τ2
 | Error_typed ℓ τ :
    Γ ⊢ Error ℓ : τ
where "Γ ⊢ e : τ" := (typed Γ e τ).

Lemma typed_Closed Γ e τ (de : Γ ⊢ e : τ) : Closed_n (length Γ) e.
Proof.
  induction de; intros σ; try by asimpl; (try by f_equal).
  rewrite ids_subst_no; auto.  by eapply lookup_lt_Some.
Qed.

Lemma typed_app_r Γ Γ' e τ (H : typed Γ e τ) :
  typed (Γ ++ Γ') e τ.
Proof.
  induction H; try by econstructor.
  econstructor. rewrite (lookup_app_l Γ Γ' x); eauto. by eapply lookup_lt_Some.
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
