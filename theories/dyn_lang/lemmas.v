From main.prelude Require Import imports.
From main.dyn_lang Require Import definition.

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

Lemma pure_step_by_val K K' e1 e1' e2 :
  fill K e1 = fill K' e1' →
  to_val e1 = None →
  head_step_ne e1' e2 →
  ∃ K'', K' = K ++ K''.
Proof.
  intros Hfill Hred Hstep.
  revert K' Hfill.
  induction K as [|Ki K IH]=> /= K' Hfill; eauto using app_nil_l.
  destruct K' as [|Ki' K' _]; simplify_eq/=.
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
  destruct K' as [|Ki' K' _]; simplify_eq/=.
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
  destruct K' as [|Ki' K' _]; simplify_eq/=.
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

(* Lemma head_step_not_error_head_step_ne e e' (H : head_step e e') (H' : to_error e' = None) : *)
(*   head_step_ne e e'. *)
(* Proof. inversion H. by simplify_eq. auto. Qed. *)

(* Lemma step_not_error_step_ne e e' (H : step e e') (H' : ¬ ∃ ℓ, faulty e ℓ) : *)
(*   step_ne e e'. *)
(* Proof. *)
(*   inversion H; simplify_eq. *)
(*   - inversion HS; simplify_eq. *)
(*     + exfalso. apply H'. exists ℓ, K, e_h. split; auto. *)
(*     + by constructor. *)
(*   - exfalso. apply H'. eexists ℓ, K, _. split; eauto. *)
(* Qed. *)

(* Lemma step_step_ne_or_faulty e e' (H : step e e') : *)
(*   (step_ne e e') ∨ (∃ ℓ, faulty e ℓ). *)
(* Proof. *)
(*   inversion H; simplify_eq. *)
(*   - inversion HS; simplify_eq. *)
(*     + right. exists ℓ, K, e_h. split; auto. *)
(*     + by constructor. *)
(*   - right. eexists ℓ, K, _. split; eauto. *)
(* Qed. *)

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

(* Lemma step_step_ne_val e v : *)
(*   step e (of_val v) -> step_ne e (of_val v). *)
(* Proof. *)
(*   intros. inversion H; simplify_eq. *)
(*   - inversion HS; simplify_eq. *)
(*     + exfalso. *)
(*       destruct (fill_val K (Error ℓ)) as [w eq]. *)
(*       { exists v. by rewrite H2 to_of_val. } *)
(*       inversion eq. *)
(*     + by constructor. *)
(*   - destruct v; inversion H0. *)
(* Qed. *)

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


(* ----- *)


(* Lemma head_step_det e e1 e2 : head_step e e1 → head_step e e2 → e1 = e2. *)
(* Proof. intros H1 H2. inversion H1; inversion H2; ((by simplify_eq) || (try done) || simplify_eq; inversion G2). Qed. *)

(* Lemma prim_step_det e e1 e2 ws xs ys zs : prim_step e ws e1 xs → prim_step e ys e2 zs → e1 = e2. *)
(* Proof. *)
(*   intros H1 H2. *)
(*   inversion H1 as [K d e' d1 e1' eq1 eq2 Hstep1|L neq]. *)
(*   - inversion H2 as [L f e'' f1 e2' eq3 eq4 Hstep2| L neq]; simplify_eq. *)
(*     + assert (K = L) as ->. *)
(*       { destruct (step_by_val K L e' e'' e2' eq3) as [M eq]; auto. by eapply val_head_stuck. *)
(*         destruct (step_by_val L K e'' e' e1') as [N eq']; auto. by eapply val_head_stuck. *)
(*         rewrite eq in eq'. assert (length K = length (N ++ M ++ K)). by rewrite -eq'. *)
(*         do 2 rewrite app_length in H. assert (M = []) as ->. apply length_zero_iff_nil. lia. *)
(*         by simpl in eq. } *)
(*       f_equal. *)
(*       rewrite (inj (fill L) e' e'' eq3) in Hstep1. *)
(*       apply (head_step_det _ _ _ Hstep1 Hstep2). *)
(*     + exfalso. destruct (step_by_val L K CastError e' e1' H5) as [L' ->]; auto. *)
(*       rewrite -fill_app in H5. assert (CastError = fill L' e'). by apply (inj (fill L)). *)
(*       rewrite (fill_CastError L' e' (eq_sym H)) in Hstep1. *)
(*       inversion Hstep1. *)
(*   - inversion H2 as [K f e'' f1 e2' eq3 eq4 Hstep2| K neq']; simplify_eq. *)
(*     + exfalso. destruct (step_by_val L K CastError e'' e2') as [L' ->]; auto. *)
(*       rewrite -fill_app in eq3. assert (CastError = fill L' e''). by apply (inj (fill L)). *)
(*       rewrite (fill_CastError L' e'' (eq_sym H)) in Hstep2. *)
(*       inversion Hstep2. *)
(*     + done. *)
(* Qed. *)

(* Lemma head_ctx_step_val Ki e e2 : *)
(*   head_step (fill_item Ki e) e2 → is_Some (to_val e). *)
(* Proof. *)
(*   inversion 1; simplify_eq; destruct Ki; inversion H0; simplify_option_eq; eexists; eauto. *)
(* Qed. *)

(* Lemma val_head_stuck e1 e2 : *)
(*   head_step e1 e2 → to_val e1 = None. *)
(* Proof. destruct 1; destruct H; auto. Qed. *)

(* Lemma step_by_val K K' e1 e1' e2 : *)
(*   fill K e1 = fill K' e1' → *)
(*   to_val e1 = None → *)
(*   head_step e1' e2 → *)
(*   ∃ K'', K' = K ++ K''. *)
(* Proof. *)
(*   intros Hfill Hred Hstep. *)
(*   revert K' Hfill. *)
(*   induction K as [|Ki K IH]=> /= K' Hfill; eauto using app_nil_l. *)
(*   destruct K' as [|Ki' K' _]; simplify_eq/=. *)
(*   { apply head_ctx_step_val in Hstep. *)
(*     apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. } *)
(*   (* change (fill_item ?Ki (fill ?K ?e)) with (fill (Ki :: K) e) in Hfill. *) *)
(*   assert (Ki = Ki') as ->. *)
(*   { eapply fill_item_no_val_inj, Hfill. *)
(*     by apply fill_not_val. apply fill_not_val. eauto using val_head_stuck. } *)
(*   simplify_eq. destruct (IH K') as [K'' ->]; auto. by exists K''. *)
(* Qed. *)

(* Definition to_error (e : expr) : option label := *)
(*   match e with *)
(*   | Error ℓ => Some ℓ *)
(*   | _ => None *)
(*   end. *)

(* Lemma fill_Error K ℓ : ∀ e, fill K e = Error ℓ → e = Error ℓ. *)
(* Proof. *)
(*   induction K as [|Ki K IHK] using rev_ind. by simpl. *)
(*   simpl. intros. assert (H' : fill_item Ki e = Error ℓ). *)
(*   rewrite fill_app in H. *)
(*   by apply IHK. *)
(*   destruct Ki; by inversion H'. *)
(* Qed. *)

(* Lemma fill_Error_empty K e ℓ : Error ℓ = fill K e → K = []. *)
(* Proof. *)
(*   generalize dependent e. *)
(*   induction K as [|Ki K IHK] using rev_ind; first by simpl. *)
(*   intros. simpl in H. assert (K = []). *)
(*   rewrite fill_app in H. *)
(*   by eapply IHK. rewrite H0 in H. simpl in H. exfalso. *)
(*   destruct Ki; inversion H. *)
(* Qed. *)

(* Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki). *)
(* Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed. *)

(* Instance fill_inj K : Inj (=) (=) (fill K). *)
(* Proof. *)
(*   induction K as [| Ki K IH]; rewrite /Inj; naive_solver. *)
(* Qed. *)

(* Lemma fill_step_inv (K : ectx) e1' e2 : to_error e2 = None → *)
(*   to_val e1' = None → step (fill K e1') e2 → *)
(*   ∃ e2', e2 = fill K e2' ∧ step e1' e2'. *)
(* Proof. *)
(*   intros neq Hnval Hprimstep. *)
(*   inversion Hprimstep. *)
(*   - simplify_eq. *)
(*     destruct (step_by_val K K0 e1' e_h e_h') as [K' ->]; eauto. *)
(*     rewrite fill_app in H0. apply (inj (fill _)) in H0. *)
(*     exists (fill K' e_h'). rewrite -fill_app; split; auto. *)
(*     rewrite -H0. by eapply S_Normal. *)
(*   - simplify_eq. *)
(* Qed. *)

(* Lemma fill_step_Error_inv K e (eNeqCE : to_error e = None) (Hnv : to_val e = None) ℓ *)
(*   (Hstep : step (fill K e) (Error ℓ)) : step e (Error ℓ). *)
(* Proof. *)
(*   generalize dependent e. *)
(*   induction K as [| Ki K IHK] using rev_ind. *)
(*   - intros. by simpl in Hstep. *)
(*   - intros. *)
(*     assert (H : to_error (fill_item Ki e) = None). destruct Ki; auto. *)
(*     rewrite fill_app in Hstep. *)
(*     specialize (IHK (fill_item Ki e) H (fill_item_not_val Ki _ Hnv) Hstep). *)
(*     by eapply fill_item_step_Error_inv. *)
(* Qed. *)























(* Lemma fill_step_inv (K : ectx) e1' e2 : to_error e2 = None → *)
(*   to_val e1' = None → step (fill K e1') e2 → *)
(*   ∃ e2', e2 = fill K e2' ∧ step e1' e2'. *)
(* Proof. *)
(*   intros neq Hnval Hstep. *)
(*   inversion Hstep. *)
(*   - simplify_eq. *)



(*     destruct (step_by_val K K0 e1' e1'0 e2') as [K' ->]; eauto. *)
(*     rewrite -fill_app in H. apply (inj (fill _)) in H. *)
(*     exists (fill K' e2'). rewrite -fill_app; split; auto. *)
(*     eapply Ectx_step; eauto. *)
(*   - simplify_eq. *)
(* Qed. *)




(* Lemma fill_item_step : ∀ Ki e1 e2 (H : step e1 e2), *)
(*   step (fill_item Ki e1) (fill_item Ki e2). *)
(* Proof. *)
(*   intros Ki e1 e2 H. inversion H. *)
(*   change (fill_item Ki (fill K ?e)) with (fill (Ki :: K) e). by apply S_Normal. *)


(*   inversion H. *)
(*   destruct Ki. *)


(*   induction K as [|Ki K] using rev_ind ; auto. intros. *)
(*   rewrite /fill foldr_snoc /=. fold (fill K (fill_item Ki e)). *)
(*   apply IHK. by apply fill_item_not_val. *)
(* Qed. *)


(* Lemma fill_step : ∀ K e1 e2 (H : step e1 e2), *)
(*   step (fill K e1) (fill K e2). *)
(* Proof. *)
(*   induction K as [|Ki K] using rev_ind ; auto. intros. *)
(*   rewrite /fill foldr_snoc /=. fold (fill K (fill_item Ki e)). *)
(*   apply IHK. by apply fill_item_not_val. *)
(* Qed. *)




(*  (K : expr Λ → expr Λ) : Prop := Build_LanguageCtx *)
(*   { fill_not_val : ∀ e : expr Λ, to_val e = None → to_val (K e) = None; *)
(*     fill_step : ∀ (e1 : expr Λ) (σ1 : state Λ) (κ : list (observation Λ)) *)
(*                   (e2 : expr Λ) (σ2 : state Λ) (efs : list (expr Λ)), *)
(*                   prim_step e1 σ1 κ e2 σ2 efs *)
(*                   → prim_step (K e1) σ1 κ (K e2) σ2 efs; *)
(*     fill_step_inv : ∀ (e1' : expr Λ) (σ1 : state Λ) *)
(*                       (κ : list (observation Λ)) (e2 : expr Λ) *)
(*                       (σ2 : state Λ) (efs : list (expr Λ)), *)
(*                       to_val e1' = None *)
(*                       → prim_step (K e1') σ1 κ e2 σ2 efs *)
(*                         → ∃ e2' : expr Λ, *)
(*                             e2 = K e2' ∧ prim_step e1' σ1 κ e2' σ2 efs }. *)











(* Lemma CastError_stuck : stuck CastError tt. *)
(* Proof. *)
(*   split. by simpl. *)
(*   intros l e σ efs Hstep. inversion Hstep; simplify_eq. *)
(*   + assert (eq : e1' = CastError). by eapply fill_CastError. *)
(*     rewrite eq in H1. inversion H1. *)
(*   + exfalso. destruct K. contradiction. *)
(*     simpl in H0. *)
(*     assert (eq : fill_item e CastError = CastError). by eapply fill_CastError. *)
(*     destruct e; simpl in eq; inversion eq. *)
(* Qed. *)

(* Lemma fill_app K K' e : fill K' (fill K e) = fill (K ++ K') e. *)
(* Proof. *)
(*   generalize dependent e. *)
(*   induction K. *)
(*   by simpl. intro e. simpl. by rewrite IHK. *)
(* Qed. *)

(* Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e). *)
(* Proof. *)
(*   revert e. induction K as [|Ki K IHK]; first by simpl. *)
(*   intros e pev. apply fill_item_val with (Ki := Ki). *)
(*   apply IHK. by simpl. *)
(* Qed. *)

(* Lemma step_by_val K K' e1 e1' e2 : *)
(*   fill K e1 = fill K' e1' → *)
(*   to_val e1 = None → *)
(*   head_step e1' e2 → *)
(*   ∃ K'', K' = K'' ++ K. *)
(* Proof. *)
(*   intros Hfill Hred Hstep. *)
(*   revert K' Hfill. *)
(*   induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r. *)
(*   destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=. *)
(*   { rewrite -fill_app in Hstep. apply head_ctx_step_val in Hstep. *)
(*     apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. } *)
(*   do 2 rewrite -fill_app /= in Hfill. *)
(*   assert (Ki = Ki') as ->. *)
(*   { eapply fill_item_no_val_inj, Hfill. *)
(*     by apply fill_not_val. apply fill_not_val; eauto using val_head_stuck. } *)
(*   simplify_eq. destruct (IH K') as [K'' ->]; auto. *)
(*   exists K''. by rewrite assoc. *)
(* Qed. *)

(* Lemma cast_error_step K : K ≠ [] → pure_step (fill K CastError) CastError. *)
(* Proof. *)
(*   intro neq. split. *)
(*   - intros σ. exists CastError, tt, []. *)
(*     by apply CastError_step. *)
(*   - intros. destruct σ1, σ2. inversion H; simplify_eq. *)
(*     + exfalso. destruct (step_by_val K K0 CastError e1' e2'0 H0 ltac:(by simpl) H2) as [K'' ->]. *)
(*       rewrite -fill_app in H0. *)
(*       assert (CastError = fill K'' e1'). by apply (inj (fill K) _ _). *)
(*       assert (e1' = CastError). eapply fill_CastError. by symmetry. rewrite H3 in H2. *)
(*       inversion H2. *)
(*     + done. *)
(* Qed. *)

(* Lemma fill_step_inv (K : ectx) e1' κ e2 efs : e2 ≠ CastError → *)
(*   to_val e1' = None → prim_step (fill K e1') κ e2 efs → *)
(*   ∃ e2', e2 = fill K e2' ∧ prim_step e1' κ e2' efs. *)
(* Proof. *)
(*   intros neq Hnval Hprimstep. *)
(*   inversion Hprimstep. *)
(*   - simplify_eq. *)
(*     destruct (step_by_val K K0 e1' e1'0 e2') as [K' ->]; eauto. *)
(*     rewrite -fill_app in H. apply (inj (fill _)) in H. *)
(*     exists (fill K' e2'). rewrite -fill_app; split; auto. *)
(*     eapply Ectx_step; eauto. *)
(*   - simplify_eq. *)
(* Qed. *)

(* Lemma chop_off_last {A} (ls : list A) n : length ls = S n → exists ks x, ls = ks ++ [x]. *)
(* Proof. *)
(*   intro. *)
(*   generalize dependent n. *)
(*   induction ls. *)
(*   - intros. exfalso. simpl in H. lia. *)
(*   - intros. destruct n. *)
(*     + simpl in H. inversion H. destruct ls. exists [], a. by simpl. inversion H1. *)
(*     + simpl in H. inversion H. destruct (IHls n H1) as [ks [x ->]]. *)
(*       exists (a :: ks), x. by simpl. *)
(* Qed. *)

(* Lemma split_list {A : Type} (a : A) (ls : list A) : exists ls' a', (a :: ls) = ls' ++ [a']. *)
(* Proof. eapply chop_off_last. done. Qed. *)

(* Lemma fill_CastError_empty K e : CastError = fill K e → K = []. *)
(* Proof. *)
(*   generalize dependent e. *)
(*   induction K as [|Ki K IHK]; first by simpl. *)
(*   intros. simpl in H. assert (K = []). by eapply IHK. rewrite H0 in H. simpl in H. exfalso. *)
(*   destruct Ki; inversion H. *)
(* Qed. *)

(* Lemma fill_item_step_CastError_inv Ki e (eNeqCE : e ≠ CastError) (Hnv : to_val e = None) (Hstep : prim_step (fill_item Ki e) [] CastError []) : *)
(*   prim_step e [] CastError []. *)
(* Proof. *)
(*   inversion Hstep. *)
(*   - simplify_eq. *)
(*     assert (eq : e2' = CastError). by rewrite (fill_CastError K e2'). *)
(*     destruct (step_by_val [Ki] K e e1' CastError) as [K' ->]; eauto. by rewrite -eq. *)
(*     assert (abs : K' ++ [Ki] = []). eapply fill_CastError_empty. by rewrite eq in H0. *)
(*     assert (abs' : length (K' ++ [Ki]) = 0). by rewrite abs. rewrite app_length in abs'. simpl in abs'. *)
(*     exfalso. lia. *)
(*   - destruct K. *)
(*     { exfalso. destruct Ki; simpl in H0; inversion H0. } *)
(*     destruct (split_list e0 K) as [K' [Ki' eq]]. rewrite eq in H0. *)
(*     rewrite -fill_app in H0. *)
(*     simpl in H0. *)
(*     destruct Ki, Ki'; *)
(*       (try by inversion H0); inversion H0; (try simpl in H0); *)
(*         try by (destruct K'; simplify_eq; simpl in Hstep; by apply CastError_step). *)
(*     + exfalso. rewrite -H1 in Hnv. rewrite to_of_val in Hnv. inversion Hnv. *)
(*     + assert (abs : to_val (fill K' CastError) = Some v1). rewrite H1. by rewrite to_of_val. assert (true : to_val (fill K' CastError) = None). by rewrite fill_not_val. *)
(*       rewrite true in abs. inversion abs. *)
(*     + exfalso. rewrite -H1 in Hnv. rewrite to_of_val in Hnv. inversion Hnv. *)
(*     + assert (abs : to_val (fill K' CastError) = Some v1). rewrite H1. by rewrite to_of_val. assert (true : to_val (fill K' CastError) = None). by rewrite fill_not_val. *)
(*       rewrite true in abs. inversion abs. *)
(* Qed. *)

(* Lemma fill_step_CastError_inv K e (eNeqCE : e ≠ CastError) (Hnv : to_val e = None) (Hstep : prim_step (fill K e) [] CastError []) : prim_step e [] CastError []. *)
(* Proof. *)
(*   generalize dependent e. *)
(*   induction K as [| Ki K IHK]. *)
(*   - intros. by simpl in Hstep. *)
(*   - intros. simpl in Hstep. *)
(*     assert (H : fill_item Ki e ≠ CastError). intro abs. destruct Ki; inversion abs. *)
(*     specialize (IHK (fill_item Ki e) H (fill_item_not_val Ki _ Hnv) Hstep). *)
(*     by eapply fill_item_step_CastError_inv. *)
(* Qed. *)

(* Lemma head_step_det e e1 e2 : head_step e e1 → head_step e e2 → e1 = e2. *)
(* Proof. intros H1 H2. inversion H1; inversion H2; ((by simplify_eq) || (try done) || simplify_eq; inversion G2). Qed. *)

(* Lemma prim_step_det e e1 e2 ws xs ys zs : prim_step e ws e1 xs → prim_step e ys e2 zs → e1 = e2. *)
(* Proof. *)
(*   intros H1 H2. *)
(*   inversion H1 as [K d e' d1 e1' eq1 eq2 Hstep1|L neq]. *)
(*   - inversion H2 as [L f e'' f1 e2' eq3 eq4 Hstep2| L neq]; simplify_eq. *)
(*     + assert (K = L) as ->. *)
(*       { destruct (step_by_val K L e' e'' e2' eq3) as [M eq]; auto. by eapply val_head_stuck. *)
(*         destruct (step_by_val L K e'' e' e1') as [N eq']; auto. by eapply val_head_stuck. *)
(*         rewrite eq in eq'. assert (length K = length (N ++ M ++ K)). by rewrite -eq'. *)
(*         do 2 rewrite app_length in H. assert (M = []) as ->. apply length_zero_iff_nil. lia. *)
(*         by simpl in eq. } *)
(*       f_equal. *)
(*       rewrite (inj (fill L) e' e'' eq3) in Hstep1. *)
(*       apply (head_step_det _ _ _ Hstep1 Hstep2). *)
(*     + exfalso. destruct (step_by_val L K CastError e' e1' H5) as [L' ->]; auto. *)
(*       rewrite -fill_app in H5. assert (CastError = fill L' e'). by apply (inj (fill L)). *)
(*       rewrite (fill_CastError L' e' (eq_sym H)) in Hstep1. *)
(*       inversion Hstep1. *)
(*   - inversion H2 as [K f e'' f1 e2' eq3 eq4 Hstep2| K neq']; simplify_eq. *)
(*     + exfalso. destruct (step_by_val L K CastError e'' e2') as [L' ->]; auto. *)
(*       rewrite -fill_app in eq3. assert (CastError = fill L' e''). by apply (inj (fill L)). *)
(*       rewrite (fill_CastError L' e'' (eq_sym H)) in Hstep2. *)
(*       inversion Hstep2. *)
(*     + done. *)
(* Qed. *)

(* Lemma prim_step_pure e e' : prim_step e [] e' [] → pure_step e e'. *)
(* Proof. *)
(*   intro Hp. split. *)
(*   + intro σ. destruct σ. exists e', tt, []. by simpl. *)
(*   + intros. destruct σ1, σ2. simpl in H. *)
(*     assert (efs = []) as ->; first by inversion H. assert (κ = []) as ->; first by inversion H. *)
(*     erewrite (prim_step_det e e' e2'); eauto. *)
(* Qed. *)

(* Instance expr_eqdec : EqDecision expr. *)
(* Proof. solve_decision. Qed. *)


(* Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core. *)

(* Local Hint Constructors head_step : core. *)
(* Local Hint Resolve to_of_val : core. *)
(* Global Instance pure_lam e1 e2 `{!AsVal e2} : *)
(*   PureExec True 1 (App (Lam e1) e2) e1.[e2 /]. *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_fold e `{!AsVal e}: *)
(*   PureExec True 1 (Unfold (Fold e)) e. *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_fst e1 e2 `{!AsVal e1, !AsVal e2} : *)
(*   PureExec True 1 (Fst (Pair e1 e2)) e1. *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   destruct AsVal1 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)
(* Proof. *)

(* Global Instance pure_snd e1 e2 `{!AsVal e1, !AsVal e2} : *)
(*   PureExec True 1 (Snd (Pair e1 e2)) e2. *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   destruct AsVal1 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_case_inl e0 e1 e2 `{!AsVal e0}: *)
(*   PureExec True 1 (Case (InjL e0) e1 e2) e1.[e0/]. *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_case_inr e0 e1 e2 `{!AsVal e0}: *)
(*   PureExec True 1 (Case (InjR e0) e1 e2) e2.[e0/]. *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_cast_between_sum1 e1 τ1 τ2 τ1' τ2' `{!AsVal e1}: *)
(*   PureExec True 1 (Cast (InjL e1) (TSum τ1 τ2) (TSum τ1' τ2')) (InjL (Cast e1 τ1 τ1')). *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_cast_between_sum2 e2 τ1 τ2 τ1' τ2' `{!AsVal e2}: *)
(*   PureExec True 1 (Cast (InjR e2) (TSum τ1 τ2) (TSum τ1' τ2')) (InjR (Cast e2 τ2 τ2')). *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_cast_between_rec e τl τr `{!AsVal e}: *)
(*   PureExec True 1 (Cast (Fold e) (TRec τl) (TRec τr)) *)
(*             (Fold (Cast e τl.[TRec τl/] τr.[TRec τr/])). *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_app_cast f e2 τ1 τ2 τ1' τ2' `{!AsVal f,!AsVal e2} : *)
(*   PureExec True 1 (App (Cast f (TArrow τ1 τ2) (TArrow τ1' τ2')) e2) (Cast (App f (Cast e2 τ1' τ1)) τ2 τ2'). *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   destruct AsVal1 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_same_ground e τ `{!AsVal e, !Ground τ} : *)
(*   PureExec True 1 (Cast (Cast e τ TUnknown) TUnknown τ) e. *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_different_ground e τ τ' (neq : τ ≠ τ') `{!AsVal e, !Ground τ, !Ground τ'} : *)
(*   PureExec True 1 (Cast (Cast e τ TUnknown) TUnknown τ') CastError. *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Lemma pure_fact_up e τ τG (neq : τ ≠ TUnknown) (nG : Ground τ → False) (G : get_shape τ = Some τG) `{!AsVal e} : *)
(*   PureExec True 1 (Cast e τ TUnknown) (Cast (Cast e τ τG) τG TUnknown). *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Lemma pure_fact_down e τ τG (neq : τ ≠ TUnknown) (nG : Ground τ → False) (G : get_shape τ = Some τG) `{!AsVal e} : *)
(*   PureExec True 1 (Cast e TUnknown τ) (Cast (Cast e TUnknown τG) τG τ). *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_cast_pair e1 e2 τ1 τ2 τ1' τ2' `{!AsVal e1, !AsVal e2} : *)
(*   PureExec True 1 (Cast (Pair e1 e2) (TProd τ1 τ2) (TProd τ1' τ2')) (Pair (Cast e1 τ1 τ1') (Cast e2 τ2 τ2')). *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   destruct AsVal1 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_cast_tunit_tunit e  `{!AsVal e} : *)
(*   PureExec True 1 (Cast e TUnit TUnit) e. *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)

(* Global Instance pure_cast_tunk_tunk e  `{!AsVal e} : *)
(*   PureExec True 1 (Cast e TUnknown TUnknown) e. *)
(* Proof. *)
(*   intros _. apply nsteps_once. apply prim_step_pure. *)
(*   destruct AsVal0 as [??];subst. *)
(*   eapply (Ectx_step []); eauto. *)
(* Qed. *)
