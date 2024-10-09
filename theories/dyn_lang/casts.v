From main.cast_calc Require Import types.
From main.dyn_lang Require Import definition lib.
From main.prelude Require Import imports labels autosubst.

(* Definition of the casts to be used when defining translation from surface lang. *)

Section casts.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Inductive direction := Normal | Opposite.

  Definition switch (dir : direction) : direction :=
    match dir with
    | Normal => Opposite
    | Opposite => Normal
    end.

  Definition comp (dir : direction) (f1 f2 : val) :=
    match dir with
    | Normal => LamV (AppAn (of_val f2).[ren (+1)] (AppAn (of_val f1).[ren (+1)] (Var 0)))
    | Opposite => LamV (AppAn (of_val f1).[ren (+1)] (AppAn (of_val f2).[ren (+1)] (Var 0)))
    end.

  Fixpoint cast_upwards (ℓ : label) (τ : type) (dir : direction) : val :=
    match τ with
    | Base B => match dir with
               | Normal => (* B => ? *) Id
               | Opposite => (* ? => B *) of_shape ℓ (S_Base B)
               end
    | Bin bin τ1 τ2 =>
        match decide (τ1 = Unknown ∧ τ2 = Unknown) with
        | left x => match dir with
                   | Normal => (* ? ∘ ? => ? *) Id
                   | Opposite => (* ? => ? ∘ ? *) of_shape' ℓ (S_Bin bin)
                   end
        | right x => comp dir
                     (match bin with
                      | Arrow => surround ν
                      | Sum => bimap_sum ν
                      | Product => bimap_prod ν
                      end
                       (cast_upwards ℓ τ1 (match bin with | Arrow => switch (dir) | _ => dir end))
                       (cast_upwards ℓ τ2 dir)
                     )
                     (match dir with
                      | Normal => Id
                      | Opposite => of_shape' ℓ (S_Bin bin)
                      end)
        end
    | Unknown => Id
    end.

  Fixpoint cast_pre (ℓ : label) τ τ' (H : consistency τ τ') (dir : direction) : val :=
    match H with
    | C_Arb_Unknown τ => cast_upwards ℓ τ dir
    | C_Unknown_Arb τ => cast_upwards ℓ τ (switch dir)
    | C_Base_Base B => Id
    | C_Bin_Bin bin τ1 τ1' τ2 τ2' H1 H2 =>
        match bin with
        | Arrow => surround ν
                      (cast_pre ℓ τ1 τ1' H1 (switch dir))
                      (cast_pre ℓ τ2 τ2' H2 dir)
        | Sum => bimap_sum ν
                      (cast_pre ℓ τ1 τ1' H1 dir)
                      (cast_pre ℓ τ2 τ2' H2 dir)
        | Product => bimap_prod ν
                      (cast_pre ℓ τ1 τ1' H1 dir)
                      (cast_pre ℓ τ2 τ2' H2 dir)
        end
    end.

  Definition cast (ℓ : label) τ τ' (H : consistency τ τ') : val := cast_pre ℓ τ τ' H Normal.

  Lemma cast_upwards_closed ℓ τ : ∀ dir, Closed (of_val $ cast_upwards ℓ τ dir).
  Proof.
    induction τ; intros; intro σ; asimpl.
    - destruct dir, B; auto.
    - destruct (decide ((τ1 = Unknown) ∧ (τ2 = Unknown))) as [[-> ->] | bbb].
      + destruct dir, bin; asimpl; try done.
      + destruct bin, dir; asimpl; repeat rewrite IHτ1 IHτ2; auto.
    - auto.
  Qed.

  Lemma cast_closed ℓ τ1 τ2 (H : consistency τ1 τ2) : ∀ dir, Closed (of_val $ cast_pre ℓ τ1 τ2 H dir).
  Proof.
    induction H; intros dir σ.
    - by rewrite cast_upwards_closed.
    - by rewrite cast_upwards_closed.
    - by asimpl.
    - destruct bin; asimpl; by repeat rewrite IHconsistency1 IHconsistency2.
  Qed.

End casts.

Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.

Section casts_alt.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma cast_pre_const_rw (ℓ : label) τ τ' (H : consistency τ τ') :
    ∀ H' dir, cast_pre ℓ τ τ' H dir = cast_pre ℓ τ τ' H' dir.
  Proof.
    induction H; intros.
    - dependent destruction H'; auto.
    - dependent destruction H'; auto.
    - dependent destruction H'; auto.
    - dependent destruction H'; auto.
      simpl. destruct bin; (f_equiv; [ apply IHconsistency1 | apply IHconsistency2 ]).
  Qed.

  Lemma cast_pre_sym ℓ τ τ' (H : consistency τ τ') :
    ∀ dir (H' : consistency τ' τ), cast_pre ℓ τ τ' H dir = cast_pre ℓ τ' τ H' (switch dir).
  Proof.
    induction H; intros.
    - dependent destruction H'; simpl; auto.
      destruct dir; auto.
    - dependent destruction H'; simpl; auto.
    - dependent destruction H'; simpl; auto.
    - dependent destruction H'; simpl; auto;
      destruct bin; auto.
      + f_equiv.
        apply IHconsistency1.
        apply IHconsistency2.
      + f_equiv.
        apply IHconsistency1.
        apply IHconsistency2.
      + f_equiv.
        apply IHconsistency1.
        apply IHconsistency2.
  Qed.

  Definition cast' ℓ τ τ' := (match consistency_decision τ τ' with
                              | inl p => cast ℓ τ τ' p
                              | inr _ => LitV LitUnit
                              end).

  Lemma cast'_closed ℓ τ1 τ2 : Closed (of_val $ cast' ℓ τ1 τ2).
  Proof. rewrite /cast'. destruct (consistency_decision τ1 τ2). apply cast_closed. by asimpl. Qed.

  Lemma cast_upwards_rw ℓ τ : cast' ℓ τ Unknown = cast_upwards ℓ τ Normal.
  Proof.
    rewrite /cast'.
    rewrite /cast /cast_pre.
    destruct (consistency_decision τ Unknown).
    2:{ exfalso. apply f. econstructor. }
    dependent destruction c; auto.
  Qed.

  Lemma cast_downwards_rw ℓ τ : cast' ℓ Unknown τ = cast_upwards ℓ τ Opposite.
  Proof.
    rewrite /cast'.
    rewrite /cast /cast_pre.
    destruct (consistency_decision τ Unknown).
    2:{ exfalso. apply f. econstructor. }
    dependent destruction c; auto.
  Qed.

  Lemma cast_U_rw ℓ :
    cast' ℓ Unknown Unknown = Id.
  Proof.
    rewrite /cast'.
    destruct (consistency_decision Unknown Unknown) as [C | nC] eqn:eq.
    2: { exfalso. apply nC. by constructor. }
    rewrite /cast /=. by dependent destruction C.
  Qed.

  Lemma cast_B_rw ℓ B :
    cast' ℓ (Base B) (Base B) = Id.
  Proof.
    rewrite /cast'.
    destruct (consistency_decision (Base B) (Base B)) as [C | nC] eqn:eq.
    2: { exfalso. apply nC. by constructor. }
    rewrite /cast /=. by dependent destruction C.
  Qed.

  Lemma cast_arrow_rw ℓ τ1 τ2 τ3 τ4 (H13 : consistency τ1 τ3) (H24: consistency τ2 τ4) :
    cast' ℓ (Bin Arrow τ1 τ2) (Bin Arrow τ3 τ4) =
    surround ν (cast' ℓ τ3 τ1) (cast' ℓ τ2 τ4).
  Proof.
    rewrite /(cast' ℓ (Bin Arrow τ1 τ2) (Bin Arrow τ3 τ4)).
    destruct (consistency_decision (Bin Arrow τ1 τ2) (Bin Arrow τ3 τ4)) as [C | nC] eqn:eq.
    2: { exfalso. apply nC. by constructor. }
    rewrite /cast. dependent destruction C. simpl.
    f_equiv.
    - rewrite /cast'.
      destruct (consistency_decision τ3 τ1) as [C' | nC'] eqn:eq'; [| ].
      2:{ exfalso. apply nC'. by apply consistency_sym. }
      rewrite /cast. apply cast_pre_sym.
    - rewrite /cast'.
      destruct (consistency_decision τ2 τ4) as [C' | nC'] eqn:eq'; [| ].
      2:{ exfalso. by apply nC'. }
      rewrite /cast. apply cast_pre_const_rw.
  Qed.

  Lemma cast_product_rw ℓ τ1 τ2 τ3 τ4 (H13 : consistency τ1 τ3) (H24: consistency τ2 τ4) :
    cast' ℓ (Bin Product τ1 τ2) (Bin Product τ3 τ4) =
    bimap_prod ν (cast' ℓ τ1 τ3) (cast' ℓ τ2 τ4).
  Proof.
    rewrite /(cast' ℓ (Bin Product τ1 τ2) (Bin Product τ3 τ4)).
    destruct (consistency_decision (Bin Product τ1 τ2) (Bin Product τ3 τ4)) as [C | nC] eqn:eq.
    2: { exfalso. apply nC. by constructor. }
    rewrite /cast. dependent destruction C. simpl.
    f_equiv.
    - rewrite /cast'.
      destruct (consistency_decision τ1 τ3) as [C' | nC'] eqn:eq'; [| ].
      2:{ exfalso. apply nC'. by apply consistency_sym. }
      rewrite /cast. apply cast_pre_const_rw.
    - rewrite /cast'.
      destruct (consistency_decision τ2 τ4) as [C' | nC'] eqn:eq'; [| ].
      2:{ exfalso. by apply nC'. }
      rewrite /cast. apply cast_pre_const_rw.
  Qed.

  Lemma cast_sum_rw ℓ τ1 τ2 τ3 τ4 (H13 : consistency τ1 τ3) (H24: consistency τ2 τ4) :
    cast' ℓ (Bin Sum τ1 τ2) (Bin Sum τ3 τ4) =
    bimap_sum ν (cast' ℓ τ1 τ3) (cast' ℓ τ2 τ4).
  Proof.
    rewrite /(cast' ℓ (Bin Sum τ1 τ2) (Bin Sum τ3 τ4)).
    destruct (consistency_decision (Bin Sum τ1 τ2) (Bin Sum τ3 τ4)) as [C | nC] eqn:eq.
    2: { exfalso. apply nC. by constructor. }
    rewrite /cast. dependent destruction C. simpl.
    f_equiv.
    - rewrite /cast'.
      destruct (consistency_decision τ1 τ3) as [C' | nC'] eqn:eq'; [| ].
      2:{ exfalso. apply nC'. by apply consistency_sym. }
      rewrite /cast. apply cast_pre_const_rw.
    - rewrite /cast'.
      destruct (consistency_decision τ2 τ4) as [C' | nC'] eqn:eq'; [| ].
      2:{ exfalso. by apply nC'. }
      rewrite /cast. apply cast_pre_const_rw.
  Qed.

  Lemma cast_GU_rw ℓ G :
    cast' ℓ (types.of_shape G) Unknown = Id.
  Proof.
    rewrite /cast' /cast.
    destruct (consistency_decision (types.of_shape G) Unknown) as [C | nC] eqn:eq.
    dependent destruction C; destruct G; (try destruct bin); simpl; try done; by repeat rewrite decide_True; auto.
    exfalso. apply nC. destruct G; constructor.
  Qed.

  Lemma cast_factor_up_rw ℓ τ G :
    to_ground τ = None → closed_ground τ = Some G →
    cast' ℓ τ Unknown = comp Normal (cast' ℓ τ (types.of_shape G)) (cast' ℓ (types.of_shape G) Unknown).
  Proof.
    intros.
    rewrite /(cast' ℓ τ Unknown).
    destruct (consistency_decision τ Unknown) as [C | nC] eqn:eq. 2:{ exfalso. apply nC. constructor. }
    rewrite /cast /cast_pre. dependent destruction C; simpl. 2:{ inversion H0. }
    destruct τ; simplify_eq. simpl.
    destruct (decide (τ1 = Unknown ∧ τ2 = Unknown)) as [[ -> -> ] | neq]. repeat rewrite /= decide_True in H; auto. inversion H.
    assert (G = S_Bin bin) as ->. { simpl in H0. by destruct τ1; destruct τ2; simplify_eq. }
    rewrite cast_GU_rw. asimpl. destruct bin.
    - rewrite cast_arrow_rw; auto; try constructor.
      by repeat rewrite -cast_downwards_rw; repeat rewrite -cast_upwards_rw.
    - rewrite cast_sum_rw; auto; try constructor.
      by repeat rewrite -cast_downwards_rw; repeat rewrite -cast_upwards_rw.
    - rewrite cast_product_rw; auto; try constructor.
      by repeat rewrite -cast_downwards_rw; repeat rewrite -cast_upwards_rw.
  Qed.

  Lemma cast_factor_down_rw ℓ τ G :
    to_ground τ = None → closed_ground τ = Some G →
    cast' ℓ Unknown τ = comp Normal (cast' ℓ Unknown (types.of_shape G)) (cast' ℓ (types.of_shape G) τ).
  Proof.
    intros.
    rewrite /(cast' ℓ Unknown τ).
    destruct (consistency_decision Unknown τ) as [C | nC] eqn:eq. 2:{ exfalso. apply nC. constructor. }
    rewrite /cast /cast_pre. dependent destruction C; simpl. destruct G; inversion H0.
    destruct τ; simplify_eq. simpl.
    destruct (decide (τ1 = Unknown ∧ τ2 = Unknown)) as [[ -> -> ] | neq]. repeat rewrite /= decide_True in H; auto. inversion H.
    assert (G = S_Bin bin) as ->. { simpl in H0. by destruct τ1; destruct τ2; simplify_eq. }
    destruct bin.
    - rewrite cast_downwards_rw /=. repeat rewrite decide_True; auto.
      rewrite cast_arrow_rw; auto; try constructor.
      repeat rewrite -cast_downwards_rw; repeat rewrite -cast_upwards_rw.
      repeat rewrite cast'_closed. asimpl.
      repeat rewrite -cast_downwards_rw; repeat rewrite -cast_upwards_rw.
      repeat rewrite cast'_closed. auto.
    - rewrite cast_downwards_rw /=. repeat rewrite decide_True; auto.
      rewrite cast_sum_rw; auto; try constructor.
    - rewrite cast_downwards_rw /=. repeat rewrite decide_True; auto.
      rewrite cast_product_rw; auto; try constructor.
  Qed.

End casts_alt.

(* From main.dyn_lang Require Import lemmas tactics. *)

(* Section lemmas. *)

(*   Context {ν : label} {Hν : NeverOccurs ν}. *)

(*   Lemma rtc_step_ne_step e e' : rtc step_ne e e' → rtc step e e'. *)
(*   Proof. induction 1. constructor. eapply rtc_l. by apply step_ne_step. auto. Qed. *)

(*   Ltac take_step' := *)
(*         (eapply rtc_l; first apply step_ne_step; first step_solver); asimpl. *)

(*   Lemma error_faulty e ℓ : *)
(*       faulty e ℓ → rtc step e (Error ℓ). *)
(*   Proof. *)
(*     intros. destruct H as (K & e_h & -> & [Hf | ->]). *)
(*     - eapply (rtc_l _ _ (fill K (Error ℓ))). apply S_Normal. by apply H_error. *)
(*       destruct K; econstructor; eauto. apply S_Error; auto. apply rtc_refl. *)
(*     - destruct K; econstructor; eauto. apply S_Error; auto. apply rtc_refl. *)
(*   Qed. *)

(* End lemmas. *)
