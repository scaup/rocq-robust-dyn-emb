From main.prelude Require Import imports autosubst big_op_three.
From main.surf_lang Require Import types.
From main.dyn_lang Require Import definition lemmas tactics labels lib.
From main.logrel.lib Require Import weakestpre rfn wrappers.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

From main.logrel Require Import definition.
From main.maps Require Import dyn_to_surf.definition surf_to_dyn.definition.

Section fundamental_bare_rfn_demb.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma rfn_bindK {K K' t t' e e' Ψ Φ L} :
    t = fill K e →
    t' = fill K' e' →
    ⊢ rfn Ψ L e e' -∗ (∀ v v', Ψ v v' -∗ rfn Φ L (fill K (of_val v)) (fill K' (of_val v'))) -∗ rfn Φ L t t'.
  Proof. intros. simplify_eq. iApply rfn_bind'. Qed.

  (* "bind pop left" *)
  Ltac rfn_bind_pr :=
    iApply rfn_bindK; [ simpl; by rw_fill; eauto | simpl; by rw_fill_popped; eauto | simpl | simpl ].

  Ltac rfn_bind_pl :=
    iApply rfn_bindK; [ simpl; by rw_fill_popped; eauto | simpl; by rw_fill; eauto | simpl | simpl ].

  Ltac rfn_bind_pp :=
    iApply rfn_bindK; [ simpl; by rw_fill_popped; eauto | simpl; by rw_fill_popped; eauto | simpl | simpl ].

  Ltac rfn_bind :=
    iApply rfn_bindK; [ simpl; by rw_fill; eauto | simpl; by rw_fill; eauto | simpl | simpl ].

  Ltac permissive_solver :=
      lazymatch goal with
      | HΔ : le_permissive _ ?Δ |- le_permissive _ ?Δ =>
          (apply (le_permissive_trans' _ _ _ HΔ), le_perm_unary_conj; intros k Hk; rewrite /occursIn; set_solver)
      | _ => fail "ads"
      end.

 Lemma unary_conj_id H ℓ : H ℓ → unary_conj H ℓ ℓ.
 Proof. intro. by split. Qed.

    Ltac delta_solver :=
      lazymatch goal with
      | HΔ : le_permissive _ ?Δ |- ?Δ _ _ =>
          (apply HΔ, unary_conj_id; rewrite /occursIn; set_solver)
      | _ => fail "ads"
      end.


  Ltac rfn_faulty := (iApply rfn_faulty; [ by faulty_solver| by faulty_solver| by delta_solver ]).
(*                      (iApply (rfn_faulty _ _ with "Hp"); faulty_solver). *)



  Ltac dvals v v' := destruct v, v'; repeat (lazymatch goal with | x : base_lit |- _ => destruct x end); auto.

  Instance Ids_expr : Ids expr. derive. Defined.
  Instance Var_Inj : Inj eq eq Var. intros x1 x2 eq. by inversion eq. Qed.

Ltac closed_solver :=
  lazymatch goal with
  | H : Closed_n _ _ |- Closed_n _ _ => intros σ; specialize (H σ); simpl in H; by simplify_eq
  | |- Closed_n _ _ => fail "goal detected suc"
  | _ => fail "wrong goal"
  end.



  Lemma fundamental_bare_rfn_demb (e : expr) n (Hne : Closed_n n e) :
    open_exprel_typed (replicate n Unknown) (Lbls e) e (⌊ (⌜⌜ e ⌝⌝) ⌋) Unknown.
  Proof.
    generalize dependent n.
    induction e; iIntros (n Hn Δ HΔ vs vs') "#Hvsvs'".
    - admit.
    - admit.
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
      simpl. iNext. iIntros (w w') "Hww'". asimpl. iNext.
      replace e.[of_val w .: subst_list (of_val <$> vs)] with e.[subst_list ((of_val w) :: (of_val <$> vs))] by by asimpl.
      replace (⌊ ⌜⌜ e ⌝⌝ ⌋).[of_val w' .: subst_list (of_val <$> vs')] with (⌊ ⌜⌜ e ⌝⌝ ⌋).[subst_list ((of_val w') :: (of_val <$> vs'))] by by asimpl.
      do 2 rewrite -fmap_cons.
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
      iNext.


      rfn_bind_pl.


      iApply rfn_s_r.
      rw_of_val.
      change (App ?ℓ (of_val ?v) ?e) with (fill_item (AppRCtx ℓ v) e).
      change (App ?ℓ (of_val ?v) ?e) with (fill_item (AppRCtx ℓ v) e).
      change (App ?ℓ (of_val ?v) ?e) with (fill_item (AppRCtx ℓ v) e).
      change (App ?ℓ (of_val ?v) ?e) with (fill_item (AppRCtx ℓ v) e).
      rw_fill_popped.
      eapply stepK. eauto. simpl.
      econstructor.



      rw_fill_item. rw_fill.
      rw_fill_popped.
      eapply stepK. eauto. simpl.
   change (fill_item ?Ki1 (fill_item ?Ki2 ?e))
     with (fill [Ki1; Ki2] e).

   change (fill_item ?Ki1 (fill_item ?Ki2 (fill_item ?Ki3 ?e)))
          (fill [Ki1] (fill_item ?Ki2 (fill_item ?Ki3 ?e))).
     with (fill [Ki1 ; Ki2] (fill_item Ki3 e)).


      iApply rfn_bindK. rw_fill_item.
      change (App ?ℓ ?e1 ?e2) with (fill_item (AppLCtx ℓ e2) e1).

      iApply rfn_bindK; [ simpl; by rw_fill; eauto | simpl; by rw_fill_popped; eauto | simpl | simpl ].

      rfn_bind_pr.

    iApply (IHe (S n) ltac:(closed_solver) Δ ltac:(permissive_solver)). simpl. auto.
    -






Ltac rfn_faulty := by (iApply (rfn_faulty _ _ with "Hp"); faulty_solver).

      lazymatch goal with
      | HΔ : le_permissive _ Δ |- le_permissive _ Δ =>
          (apply (le_permissive_trans' _ _ _ HΔ), le_perm_unary_conj; intros k Hk; rewrite /occursIn; set_solver)
      | _ => fail "ads"
      end.



      assert (Hc1 : Closed_n n e1). admit.
      assert (Hl1 : le_permissive (Lbls e1) Δ).

      iDestruct (IHe1 _ Hc1 Δ Hl1 vs vs' with "Hvsvs'") as "HH".
      simpl.

       iApply rfn_bindK. simpl. rw_fill; eauto. rw_fill_popped; eauto. simpl.
      iApply ("IH" $! n). admit. iFrame "Hvsvs'". iPureIntro.


      iSpecialize

    - admit.
    - admit.
    - admit.










    generalize dependent n.
    iInduction e as
      [ (* Lit *) b | (* Seq *) ℓ e1 e2 | (*If*) ℓ e0 e1 e2
      | (* BinOp *) ℓ binop e1 e2 | (* Var *) v | (* Lam *) e
      | (* App *) ℓ e1 e2 | (* InjL *) e | (* InjR *) e
      | (* Case *) ℓ e e1 e2 | (* Fst *) ℓ e | (* Snd *) ℓ e
      | (* Pair *) e1 e2 | (* Error *) ℓ] "IH";
      iIntros (n Hn P vs vs') "[%Hlp #Hvsvs']".
    - rfn_steps. rfn_val. rewrite valrel_unknown_unfold /=. destruct b; auto.
    - rfn_bind. iApply ("IH" $! n). admit. iFrame "Hvsvs'".
      iPureIntro.

      Δ(Seq ℓ e1 e3) ≤ P, then Δ e1 ≤ P
      in general, if P

    - asimpl.

      (* rfn_bind_pr. *)
      iApply rfn_bindK. rw_fill; eauto. rw_fill_popped; eauto. simpl.
      iApply ("IH" $! n). admit. iFrame "Hvsvs'". iPureIntro.




      intros        cha
      rfn_bind

      rfn_steps. rfn_val. rewrite valrel_unknown_unfold /=. destruct b; auto.


    - asimpl. admit.
    - asimpl. iSpecialize ("IH" $! n ).
      (* specialize with P, *)
      (* proof obligation for using "IH"; less_possibilities_then (Δ e0) P *)
      (* should be easy; we have Δ e0 ≤ Δ (If ℓ e0 e2 e3) *)

      (* ℓ toegelaten, *)
      (* (If ℓ e0 e1 e2) (If ν (cast ℓ B e0') e1' e2') *)

      admit.


    - admit.
    - asimpl. admit.
    - (* Lam *)
      (* simpl. *)
      (* just prove that the two lambdas are in the value relation for unknown *)
      (* ok, so to prove : ▷ (∀ w, w'. unknown P w w' -∗ \x.e w \x.e w'   ) *)
      (* forget about later... *)
      (* yeah, we can use "IH" with extended list and P... *)

      (* --------- correction *)
      (* this would now be ∃ e, e', v = λe, v'=λe' ∗ ▷ (∀ w w'...)  *)
      admit.
    - (* app *)
      (* exprel_untyped P e1 e1' -∗ *)
      (* exprel_untyped P e2 e2' -∗ *)
      (* exprel_untyped P (App ℓ e1 e2) (AppAn (e1' : (?=>?→?)ℓ) e2') *)

      (* one bind *)
      (* valrel_untyped P v1 v1' -∗ *)
      (* exprel_untyped P e2 e2' -∗ *)
      (* exprel_untyped P (App ℓ v1 e2) (AppAn (v1' : (?=>?→?)ℓ) e2') *)

      (* just a step *)
      (* valrel_untyped P v1 v1' -∗ *)
      (* exprel_untyped P e2 e2' -∗ *)
      (* exprel_untyped P (App ℓ v1 e2) (AppAn (λx. App ℓ v1' x) e2') *)

      (* second bind *)
      (* valrel_untyped P v1 v1' -∗ *)
      (* valrel_untyped P v2 v2' -∗ *)
      (* exprel_untyped P (App ℓ v1 v2) (App ℓ v1' v2') *)

      (* Can we do this? *)

      (* case analyis on v1 v1'; *)
      (*   in all the different branches but the arrow branch, we get (on left and right!) stuckness on ℓ *)
      (*      succes! becasuse ℓ is in P *)
      (*   in the arrow branch, we have (▷ ∀ w w', ....) *)
      (*      we have to adjust definition I think... *)
      (*      suppose this as its definition : (∃ e, e', v = λe, v'=λe' ∗ ▷ (∀ w w'. Rww' -> E (e.[v/]) (e'.[v/]) ...) ) *)
      (*      then we can take a step (both sides); and get what we need *)



      admit.




    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.




    (* open_exprel_typed (replicate n (valrel_unknown (Δ e))) e  (⌊ ⌜⌜ e ⌝⌝ ⌋) Unknown. *)
