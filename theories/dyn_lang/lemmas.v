From main.prelude Require Import imports tactics.
From main.dyn_lang Require Import definition.

Instance Var_Inj : Inj eq eq Var. intros x1 x2 eq. by inversion eq. Qed.

(** fill-stuff *)
(** ----------------------------------- *)

Lemma fill_app K K' e : fill (K ++ K') e = fill K (fill K' e).
Proof.
  generalize dependent e.
  induction K; auto.
  intro e. simpl. by rewrite IHK.
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
  repeat match goal with
          | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
          end; auto.
Qed.

Instance fill_inj K : Inj (=) (=) (fill K).
Proof.
  induction K as [| Ki K IH]; rewrite /Inj; naive_solver.
Qed.

(** is-val *)
(** ----------------------------------- *)

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  revert e. induction K as [|Ki K IHK] using rev_ind; first by simpl.
  intros e pev. apply fill_item_val with (Ki := Ki).
  apply IHK. rewrite fill_app in pev. by simpl.
Qed.

(** not-val *)
(** ----------------------------------- *)

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

(** faulty *)
(** ----------------------------------- *)

Lemma fill_faulty (e : expr) (ℓ : label) (H : faulty e ℓ) : ∀ K, faulty (fill K e) ℓ.
Proof. intro K. destruct H as (K' & e' & -> & H'). rewrite -fill_app. by repeat eexists. Qed.

Lemma head_faulty_no_val e ℓ (H : head_faulty e ℓ) :
  to_val e = None.
Proof. inversion H; naive_solver. Qed.

Lemma fill_item_faulty_inv Ki e (He : to_val e = None) ℓ
  (H : faulty (fill_item Ki e) ℓ) :
  faulty e ℓ.
Proof.
  rewrite /faulty. rewrite /faulty in H.
  destruct H as (K & e' & eq & disj).
  destruct K as [ | Ki' K].
  - destruct disj; inversion H; destruct Ki; simpl in eq; simplify_eq.
  - assert (Ki = Ki').
    { apply (fill_item_no_val_inj Ki Ki' e (fill K e')); auto.
      apply fill_not_val. destruct disj as [a | b]; [by inversion a | by inversion b]. }
    simplify_eq. exists K, e'; auto. split; auto. simpl in eq.
    apply (fill_item_inj Ki' _ _ eq).
Qed.

Lemma fill_faulty_inv K e (He : to_val e = None) ℓ
  (H : faulty (fill K e) ℓ) :
  faulty e ℓ.
Proof. induction K; auto. apply IHK. eapply fill_item_faulty_inv. by apply fill_not_val. eauto. Qed.

(** pure step *)
(** ----------------------------------- *)

Lemma fill_step e e' (H : step_ne e e') K :
  step_ne (fill K e) (fill K e').
Proof. inversion H. repeat rewrite -fill_app. by econstructor. Qed.

Lemma pure_head_ctx_step_val Ki e e2 :
  head_step_ne (fill_item Ki e) e2 → is_Some (to_val e).
Proof.
  inversion 1; simplify_eq; destruct Ki; simplify_option_eq; eexists; eauto.
Qed.

Lemma val_pure_head_stuck e1 e2 :
  head_step_ne e1 e2 → to_val e1 = None.
Proof. destruct 1; auto. Qed.

Lemma step_no_val e1 e2 :
  step_ne e1 e2 → to_val e1 = None.
Proof.
  destruct 1; auto. apply fill_not_val.
  by eapply val_pure_head_stuck.
Qed.

Lemma step_no_val' e1 e2 :
  step e1 e2 → to_val e1 = None.
Proof.
  destruct 1; auto. apply fill_not_val.
  destruct HS. by invclear H.
  by eapply val_pure_head_stuck.
  by apply fill_not_val.
Qed.

Lemma pure_step_by_val K K' e1 e1' e2 :
  fill K e1 = fill K' e1' →
  to_val e1 = None →
  head_step_ne e1' e2 →
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
    by apply fill_not_val. apply fill_not_val. eauto using val_pure_head_stuck. }
  simplify_eq. destruct (IH K') as [K'' ->]; auto. by exists K''.
Qed.

Lemma pure_step_by_val' K K' e1 e1' ℓ :
  fill K e1 = fill K' e1' →
  to_val e1 = None →
  (head_faulty e1' ℓ ∨ e1' = Error ℓ) →
  ∃ K'', K' = K ++ K''.
Proof.
  intros Hfill Hred disj.
  revert K' Hfill.
  induction K as [|Ki K IH]=> /= K' Hfill; eauto using app_nil_l.
  destruct K' as [|Ki' K']; simplify_eq/=.
  { assert (H := (fill_not_val K _ Hred)).
    destruct disj as [hf | he]; [destruct Ki; inversion hf; simplify_eq | by destruct Ki]. }
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_val_inj, Hfill.
    by apply fill_not_val. apply fill_not_val.
    destruct disj as [hf | he]. by inversion hf. by simplify_eq.
  }
  simplify_eq. destruct (IH K') as [K'' ->]; auto. by exists K''.
Qed.

Lemma fill_pure_step_inv (K : ectx) e1' e2 :
  to_val e1' = None → step_ne (fill K e1') e2 →
  ∃ e2', e2 = fill K e2' ∧ step_ne e1' e2'.
Proof.
  intros Hnval Hstep.
  inversion Hstep.
  destruct (pure_step_by_val K K0 e1' e_h e_h') as [K' ->]; eauto.
  rewrite fill_app in H0. apply (inj (fill _)) in H0.
  exists (fill K' e_h'). rewrite -fill_app; split; auto.
  rewrite -H0. by econstructor.
Qed.


Lemma ne_head_step_det e e1 e2 : head_step_ne e e1 → head_step_ne e e2 → e1 = e2.
Proof. intros H1 H2. inversion H1; inversion H2; simplify_eq; auto. Qed.


Lemma ne_step_det (e e1 e2 : expr) : step_ne e e1 → step_ne e e2 → e1 = e2.
Proof.
  intros H1 H2.
  inversion H1; inversion H2. simplify_eq.
  assert (K = K0) as <-.
  { destruct (pure_step_by_val K0 K e_h0 e_h e_h' H3 ltac:(by eapply val_pure_head_stuck) ltac:(eauto)) as [Kred eq].
    destruct (pure_step_by_val K K0 _ _ e_h'0 (eq_Symmetric _ _ H3) ltac:(by eapply val_pure_head_stuck) ltac:(eauto)) as [Kred' eq'].
    assert (H: length K = length ((K ++ Kred') ++ Kred)). by rewrite -eq' eq. rewrite -app_assoc app_length app_length in H.
    destruct Kred'; [ | exfalso; simpl in *; lia ]. destruct Kred; [ | exfalso; simpl in *; lia ].
    by rewrite app_nil_r in eq. }
  f_equal. rewrite (fill_inj K _ _ H3) in HS0. by eapply ne_head_step_det.
Qed.

Lemma ne_head_step_not_head_faulty e e' (H : head_step_ne e e') ℓ (H' : head_faulty e ℓ): False.
Proof. inversion H; inversion H'; simplify_eq; simpl in *; simplify_eq; simplify_option_eq. Qed.

Lemma faulty_not_stop e ℓ (H : faulty e ℓ) e' (Hstep : step_ne e e') : False.
Proof.
  destruct H as (K & e_h & -> & disj).
  inversion Hstep. simplify_eq.
  assert (K = K0) as <-.
  { destruct (pure_step_by_val K K0 _ _ e_h' (eq_Symmetric _ _ H0)) as [Kred eq].
    destruct disj. eapply head_faulty_no_val;  eauto. by rewrite H. auto.
    destruct (pure_step_by_val' _ _ _ _ ℓ (H0)) as [Kred' eq'].
    by eapply val_pure_head_stuck. auto.
    assert (H: length K = length ((K ++ Kred) ++ Kred')). by rewrite -eq eq'. rewrite -app_assoc app_length app_length in H.
    destruct Kred'; [ | exfalso; simpl in *; lia ]. destruct Kred; [ | exfalso; simpl in *; lia ].
    by rewrite app_nil_r in eq. }
  rewrite (fill_inj K _ _ H0) in HS. inversion disj.
  - by eapply ne_head_step_not_head_faulty.
  - simplify_eq. inversion HS.
Qed.

Lemma faulty_unique_label (e : expr) (ℓ1 ℓ2 : label) : faulty e ℓ1 → faulty e ℓ2 → ℓ1 = ℓ2.
Proof.
  intros H1 H2.
  destruct H1 as (K1 & e_h1 & eq1 & disj1).
  destruct H2 as (K2 & e_h2 & eq2 & disj2). simplify_eq.
  assert (K1 = K2) as <-.
  { destruct (pure_step_by_val' K1 K2 _ _ ℓ2 eq2) as [Kred eq]; eauto. destruct disj1 as [a | b]; [by inversion a| by inversion b].
    destruct (pure_step_by_val' K2 K1 _ _ ℓ1 (eq_Symmetric _ _ eq2)) as [Kred' eq']; eauto. destruct disj2 as [a | b]; [by inversion a| by inversion b].
    assert (H: length K1 = length ((K1 ++ Kred) ++ Kred')). by rewrite -eq eq'. rewrite -app_assoc app_length app_length in H.
    destruct Kred'; [ | exfalso; simpl in *; lia ]. destruct Kred; [ | exfalso; simpl in *; lia ].
    by rewrite app_nil_r in eq. }
  destruct disj1 as [a1 | b1], disj2 as [a2 | b2].
  - inversion a1; inversion a2; simplify_eq; try done.
  - inversion a1; inversion b2; simplify_eq; try done.
  - inversion b1; inversion a2; simplify_eq; try done.
  - inversion b1; inversion b2; simplify_eq; try done.
Qed.

Lemma faulty_not_val v e ℓ (Hv : of_val v = e) (H : faulty e ℓ) : False.
Proof.
  destruct H as (K & e_h & -> & disj).
  destruct K as [|Ki K]; inversion Hv.
  - simpl in *. simplify_eq. inversion disj; destruct v; inversion H; simplify_option_eq.
  - destruct Ki; destruct v; inversion H0; simplify_eq.
    + simpl in *. destruct (fill_val K e_h) as [w eq]. by rewrite -H1 to_of_val.
      rewrite -(of_to_val _ _ eq) in disj.
      destruct disj as [a | b]. destruct w; inversion a. destruct w; inversion b.
    + simpl in *. destruct (fill_val K e_h) as [w eq]. by rewrite -H2 to_of_val.
      rewrite -(of_to_val _ _ eq) in disj.
      destruct disj as [a | b]. destruct w; inversion a. destruct w; inversion b.
    + simpl in *. destruct (fill_val K e_h) as [w eq]. by rewrite -H1 to_of_val.
      rewrite -(of_to_val _ _ eq) in disj.
      destruct disj as [a | b]. destruct w; inversion a. destruct w; inversion b.
    + simpl in *. destruct (fill_val K e_h) as [w eq]. by rewrite -H1 to_of_val.
      rewrite -(of_to_val _ _ eq) in disj.
      destruct disj as [a | b]. destruct w; inversion a. destruct w; inversion b.
Qed.

(** normal step *)
(** ----------------------------------- *)

Lemma head_ctx_step_val Ki e e2 :
  head_step (fill_item Ki e) e2 → is_Some (to_val e).
Proof.
  inversion 1; simplify_eq; destruct Ki; inversion H0; simplify_option_eq; eexists; eauto.
Qed.

Lemma val_head_stuck e1 e2 :
  head_step e1 e2 → to_val e1 = None.
Proof. destruct 1; destruct H; auto. Qed.

Lemma step_by_val K K' e1 e1' e2 :
  fill K e1 = fill K' e1' →
  to_val e1 = None →
  head_step e1' e2 →
  ∃ K'', K' = K ++ K''.
Proof.
  intros Hfill Hred Hstep.
  revert K' Hfill.
  induction K as [|Ki K IH]=> /= K' Hfill; eauto using app_nil_l.
  destruct K' as [|Ki' K']; simplify_eq/=.
  { apply head_ctx_step_val in Hstep.
    apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
  (* change (fill_item ?Ki (fill ?K ?e)) with (fill (Ki :: K) e) in Hfill. *)
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_val_inj, Hfill.
    by apply fill_not_val. apply fill_not_val. eauto using val_head_stuck. }
  simplify_eq. destruct (IH K') as [K'' ->]; auto. by exists K''.
Qed.

Definition to_error (e : expr) : option label :=
  match e with
  | Error ℓ => Some ℓ
  | _ => None
  end.

Lemma fill_step_inv (K : ectx) e1' e2 : (to_error e2 = None) →
  to_val e1' = None → step (fill K e1') e2 →
  ∃ e2', e2 = fill K e2' ∧ step e1' e2'.
Proof.
  intros neq Hnval Hprimstep.
  inversion Hprimstep.
  - simplify_eq.
    destruct (step_by_val K K0 e1' e_h e_h') as [K' ->]; eauto.
    rewrite fill_app in H0. apply (inj (fill _)) in H0.
    exists (fill K' e_h'). rewrite -fill_app; split; auto.
    rewrite -H0. by eapply S_Normal.
  - simplify_eq.
Qed.

Lemma fill_Error_empty K e ℓ : Error ℓ = fill K e → K = [].
Proof.
  generalize dependent e.
  induction K as [|Ki K IHK] using rev_ind; first by simpl.
  intros. simpl in H. assert (K = []).
  rewrite fill_app in H.
  by eapply IHK. rewrite H0 in H. simpl in H. exfalso.
  destruct Ki; inversion H.
Qed.

Lemma fill_item_step_Error_inv Ki e (eNeqCE : to_error e = None) (Hnv : to_val e = None) ℓ
  (Hstep : step (fill_item Ki e) (Error ℓ)) :
  step e (Error ℓ).
Proof.
  inversion Hstep.
  - assert (K = []) as ->. by eapply fill_Error_empty. simpl in *.
    assert (fill [Ki] e = fill [] e_h). auto.
    edestruct (step_by_val [Ki] [] e _ _ H1 Hnv HS) as [K' eq]; eauto. inversion eq.
  - simplify_eq.
    destruct K as [|Ki' K'].
    { exfalso. by apply H1. }
    assert (e = fill K' (Error ℓ)).
    { simpl in H.
      assert (Ki' = Ki).
      eapply (fill_item_no_val_inj _ _ (fill K' (Error ℓ)) e); auto.
      apply fill_not_val; eauto. simplify_eq.
      auto. }
    rewrite H0. simplify_eq.
    apply S_Error. intro abs. by rewrite abs /= in eNeqCE.
Qed.

Lemma fill_step_Error_inv K e (eNeqCE : to_error e = None) (Hnv : to_val e = None) ℓ
  (Hstep : step (fill K e) (Error ℓ)) : step e (Error ℓ).
Proof.
  generalize dependent e.
  induction K as [| Ki K IHK] using rev_ind.
  - intros. by simpl in Hstep.
  - intros.
    assert (H : to_error (fill_item Ki e) = None). destruct Ki; auto.
    rewrite fill_app in Hstep.
    specialize (IHK (fill_item Ki e) H (fill_item_not_val Ki _ Hnv) Hstep).
    by eapply fill_item_step_Error_inv.
Qed.

(* ------------- *)
Lemma step_ne_step e e' : step_ne e e' → step e e'.
Proof. destruct 1. by apply S_Normal, H_not_error. Qed.

Lemma step_faulty_error e ℓ (H : faulty e ℓ) :
  rtc step e (Error ℓ).
Proof.
  destruct H as (K & eh & -> & [hf | ->]).
  - simpl.
    eapply (rtc_transitive _ (fill K (Error ℓ))).
    apply rtc_once. econstructor. by econstructor.
    destruct K as [|Ki K]. apply rtc_refl.
    apply rtc_once. econstructor. auto.
  - destruct K as [|Ki K]. apply rtc_refl.
    apply rtc_once. econstructor. auto.
Qed.

(* step preservers faultyness *)

Lemma step_preserves_faulty e ℓ (H : faulty e ℓ) e' (H' : step e e') : faulty e' ℓ.
Proof.
  inversion H'; simplify_eq.
  - destruct HS.
    + assert (faulty (fill K e) ℓ0). exists K, e. split; eauto.
      rewrite (faulty_unique_label _ _ _ H H1). eexists; eauto.
    + exfalso. eapply (faulty_not_stop _ _ H). by econstructor.
  - exists [], (Error ℓ); split; eauto.
    assert (faulty (fill K (Error ℓ0)) ℓ0). repeat eexists; eauto.
    by rewrite (faulty_unique_label _ _ _ H H1).
Qed.

Lemma rtc_step_ne_step_invariant e :
  ∀ t, rtc step e t → (rtc step_ne e t ∨ (∃ ℓ, faulty t ℓ ∧ ∃ t', rtc step_ne e t' ∧ faulty t' ℓ)).
Proof.
  apply (rtc_ind_r (fun t => (rtc step_ne e t ∨ (∃ ℓ, faulty t ℓ ∧ ∃ t', rtc step_ne e t' ∧ faulty t' ℓ)))); [ left; apply rtc_refl |  ].
  intros y z Hey Hyz [Hney | (ℓ & Hf & t' & Het' & Hft')].
  - inversion Hyz; simplify_eq.
    + inversion HS; simplify_eq.
      * right. exists ℓ. split. exists K, (Error ℓ). auto. exists (fill K e_h). split; auto. exists K, e_h. eauto.
      * left. apply (rtc_transitive _ (fill K e_h)); auto.
        eapply rtc_congruence. intros. by eapply fill_step. apply rtc_once. by apply (SNE_Normal []).
    + right. exists ℓ. split. exists [], (Error ℓ). auto. exists (fill K (Error ℓ)). split; auto.
      exists K, (Error ℓ). split; auto.
  - right. exists ℓ. split; auto.
    eapply (step_preserves_faulty y); eauto.
    exists t'. split; auto.
Qed.


Lemma rtc_step_step_ne_to_val e v :
  rtc step e (of_val v) <-> rtc step_ne e (of_val v).
Proof.
  split.
  - intro H. destruct (rtc_step_ne_step_invariant _ _ H) as [yeah | (ℓ & absurd & _)]; auto.
    exfalso. by eapply faulty_not_val.
  - apply (rtc_congruence id _ _ _ step_ne_step).
Qed.

Lemma rtc_step_step_ne_to_error e ℓ :
  rtc step e (Error ℓ) <-> ∃ t, faulty t ℓ ∧ rtc step_ne e t.
Proof.
  split.
  - intro H. destruct (rtc_step_ne_step_invariant _ _ H) as [yeah | (ℓ' & ft & t' & Hs & Hf)]; auto.
    + exists (Error ℓ). split; eauto. eexists []; eauto.
    + exists t'. split; auto. assert (faulty (Error ℓ) ℓ). by exists []; eauto.
      by rewrite -(faulty_unique_label _ _ _ ft H0).
  - intros (t & Hf & Hs).
    apply (rtc_transitive _ t).
    by apply (rtc_congruence id _ _ _ step_ne_step). by apply step_faulty_error.
Qed.

Lemma Error_step_absurd ℓ e : step (Error ℓ) e → False.
Proof.
  intros abs. invclear abs.
  - destruct K as [|Ki K]; simpl in *; simplify_eq.
    + invclear HS. invclear H.
      invclear H.
    + destruct Ki; invclear H0.
  - destruct K as [|Ki K]; simpl in *; simplify_eq.
    destruct Ki; invclear H.
Qed.

Lemma head_step_not_error_fill e e' :
  head_step e e' → ∀ K, step (fill K e) (fill K e').
Proof.
  intros. by constructor.
Qed.

Lemma step_not_error_fill_item :
  ∀ Ki e e' (He' : ¬ ∃ ℓ, e' = Error ℓ) (Hs : step e e'), step (fill_item Ki e) (fill_item Ki e').
Proof.
  intros. destruct Hs.
  - change (fill_item Ki (fill K ?e)) with (fill [Ki] (fill K e)). repeat rewrite -fill_app.
    by constructor.
  - exfalso. apply He'. by exists ℓ.
Qed.

Lemma step_not_error_fill :
  ∀ K e e' (He' : ¬ ∃ ℓ, e' = Error ℓ) (Hs : step e e'), step (fill K e) (fill K e').
Proof.
  intros K. generalize dependent K.
  induction K as [|Ki K] using rev_ind. auto.
  intros. do 2 rewrite fill_app. apply IHK.
  intros abs. destruct abs as [ℓ abs]. destruct Ki; inversion abs.
  by apply step_not_error_fill_item.
Qed.

Lemma rtc_step_not_error_fill e :
  ∀ e', rtc step e e' -> ∀ (He' : ¬ ∃ ℓ, e' = Error ℓ) K, rtc step (fill K e) (fill K e').
Proof.
  apply (rtc_ind_r (fun e' => (∀ (He' : ¬ ∃ ℓ, e' = Error ℓ) K, rtc step (fill K e) (fill K e')))); [ left; apply rtc_refl |  ].
  intros.
  apply (rtc_transitive _ (fill K y)). apply H1; auto.
  intro absurd. destruct absurd as [ℓ ->]. by eapply Error_step_absurd.
  apply rtc_once. apply step_not_error_fill; auto.
Qed.

Definition K_error e := ∃ K ℓ, (e = fill K (Error ℓ)).

Lemma not_K_error_step_fill_item :
  ∀ Ki e e' (He' : ¬ K_error e) (Hs : step e e'), step (fill_item Ki e) (fill_item Ki e').
Proof.
  intros. destruct Hs.
  - change (fill_item Ki (fill K ?e)) with (fill [Ki] (fill K e)). repeat rewrite -fill_app.
    by constructor.
  - exfalso. apply He'. by exists K, ℓ.
Qed.

Lemma not_K_error_step_fill :
  ∀ K e e' (He : ¬ K_error e) (Hs : step e e'), step (fill K e) (fill K e').
Proof.
  intros K. generalize dependent K.
  induction K as [|Ki K] using rev_ind. auto.
  intros. do 2 rewrite fill_app. apply IHK.
  intros abs. apply He. destruct abs as (K' & ℓ & abs).
  destruct (pure_step_by_val' _ _ _ _ _ abs ltac:(by eapply step_no_val') ltac:(by right) ) as (K'' & ->).
  rewrite fill_app in abs.
  exists K'', ℓ. eapply fill_inj. apply abs.
  by apply not_K_error_step_fill_item.
Qed.
