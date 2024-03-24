From stdpp Require Import prelude.
From iris Require Import prelude.
From Autosubst Require Export Autosubst.

Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term} {ids_inj : Inj (=) (=) Ids_term}.

  Definition Closed_n (n : nat) (t : term) : Prop := ∀ σ, t.[upn n σ] = t.
  Definition Closed : term → Prop := Closed_n 0.

  (* TODO clean up *)

  Lemma iter_up (m x : nat) (f : var → term) :
    upn m f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
  Proof.
    revert x; induction m as [|m IH]=> -[|x];
      repeat (destruct (lt_dec _ _) || asimpl || rewrite IH); auto with lia.
  Qed.

  Lemma iter_up_cases k n σ : (upn n σ k = ids k ∧ k < n) +
                                   { j : nat | (k = (n + j)%nat) ∧ upn n σ k = (σ j).[ren (+n)]  }.
  Proof.
    destruct (decide (k < n)).
    - left. split. rewrite iter_up. destruct (lt_dec k n). auto. exfalso;lia. auto.
    - apply inr. exists (k - n). split. lia. rewrite iter_up. destruct (lt_dec k n).
      contradiction. by asimpl.
  Qed.

  Lemma upn_lt i n σ : i < n → upn n σ i = ids i.
  Proof.
    generalize dependent i.
    induction n.
    - intros. exfalso. lia.
    - intros. destruct i.
      + by asimpl.
      + asimpl. rewrite IHn. by asimpl. lia.
  Qed.

  Lemma ids_subst_yes n m σ : (ids (n + m)).[upn n σ] = ((ids m).[σ].[ren (+n)]).
  Proof.
    asimpl.
    induction n.
    - by asimpl.
    - asimpl. rewrite IHn. by asimpl.
  Qed.

  Lemma ids_subst_no n m σ : n < m → (ids n).[upn m σ] = ids n.
  Proof.
    generalize dependent n.
    induction m.
    - intros. exfalso. lia.
    - intros. destruct n.
      + by asimpl.
      + asimpl. specialize (IHm n). asimpl in IHm. rewrite IHm. by asimpl. lia.
  Qed.

  Lemma ids_subst_cases k n σ : ((ids k).[upn n σ] = ids k ∧ k < n) +
                                  { j : nat | (k = (n + j)%nat) ∧ (ids k).[upn n σ] = (ids j).[σ].[ren (+n)]  }.
  Proof.
    destruct (decide (k < n)).
    - apply inl. split. apply ids_subst_no; auto. auto.
    - apply inr. exists (k - n). split. lia. rewrite -ids_subst_yes.
      assert (triv : k = n + (k - n)). lia. by rewrite -triv.
  Qed.

  Lemma ids_lt_Closed_n (x n : nat) : Closed_n n (ids x) ↔ x < n.
  Proof.
    split.
    - intros.
      destruct (ids_subst_cases x n (ren (+1))) as [[_ eq] | [j [-> _]]].
      + auto.
      + exfalso. unfold Closed_n in H.
        specialize (H (ren (+1))).
        rewrite ids_subst_yes in H.
        asimpl in H. assert (S (n + j) = n + j). by apply (inj ids). lia.
    - intros. intro σ. by apply ids_subst_no.
  Qed.

  Definition subst_list_old (vs : list term) : var → term :=
    fun (x : var) => from_option id (ids x) (vs !! x).

  Fixpoint subst_list (vs : list term) : var → term :=
    match vs with
    | [] => ids
    | v :: vs' => v .: subst_list vs'
    end.

  (* Lemma simul_subst_closed (s t1 t2 : term) (Ct1 : Closed t1) (Ct2 : Closed t2) : s.[t1/].[t2/] = s.[t1,t2/]. *)
  (* Proof. asimpl. by rewrite Ct1. Qed. *)

  (* Lemma scomp_closed_term (t : term) (Ct : Closed t) σ : t .: σ = t .: ids >> σ. *)
  (* Proof. *)
  (*   f_ext. intro x. induction x. *)
  (*   - by simpl. *)
  (*   - by asimpl. *)
  (* Qed. *)

  Lemma subst_list_snoc vs v : subst_list (vs ++ [v]) = (upn (length vs) (v .: ids)) >> (subst_list vs).
  Proof.
    induction vs.
    - by asimpl.
    - simpl. rewrite IHvs. by asimpl.
  Qed.

  Lemma ids_subst_list_lookup (x : var) (ts : list term) t (H : ts !! x = Some t) :
    (ids x).[subst_list ts] = t.
  Proof.
    generalize dependent x.
    induction ts. intros. inversion H.
    destruct x. intro H. inversion_clear H. by asimpl.
    intro H. simpl in H. specialize (IHts _ H). by asimpl in *.
  Qed.

  Lemma ids_subst_list_lookup2 (x : var) (ts : list term) :
    (exists t, ts !! x = Some t ∧ (ids x).[subst_list ts] = t) ∨ (ts !! x = None).
  Proof.
    destruct (ts !! x) eqn:eq.
    + left. exists t. split; auto. by apply ids_subst_list_lookup.
    + right; auto.
  Qed.

  Lemma ids_subst_list_lt_length (x : var) (ts : list term) (p : x < length ts) :
    (exists t, ts !! x = Some t ∧ (ids x).[subst_list ts] = t).
  Proof.
    destruct (ts !! x) eqn:eq. exists t. split; auto. by apply ids_subst_list_lookup.
    assert (p' : length ts ≤ x). by apply lookup_ge_None. lia.
  Qed.




End Autosubst_Lemmas.


  (* Definition subst_list_val (vs : list term) : var → term := subst_list (map of_val vs). *)


  (* Lemma subst_list_val_cons v vs : of_val v .: subst_list_val vs = subst_list_val (v :: vs). *)
  (* Proof. intros. by asimpl. Qed. *)

  (* (* Lemma var_subst_list_val_lt_length (vs : list val) (x : var) (p : x < length vs) : *) *)
  (* (*   (exists v : val, vs !! x = Some v ∧ (Var x).[subst_list_val vs] = v). *) *)
  (* (* Proof. *) *)
  (* (*   destruct (vs !! x) eqn:eq. exists v. split; auto. apply ids_subst_list_lookup. by rewrite list_lookup_fmap eq /=. *) *)
  (* (*   assert (length vs ≤ x). by apply lookup_ge_None. lia. *) *)
  (* (* Qed. *) *)
  (* Lemma Var_subst_list_closed_n_length (vs : list val) (x : var) (p : Closed_n (length vs) (Var x)) : *)
  (*   (exists v : val, vs !! x = Some v ∧ (Var x).[subst_list_val vs] = v). *)
  (* Proof. *)
  (*   destruct (vs !! x) eqn:eq. exists v. split; auto. apply ids_subst_list_lookup. by rewrite list_lookup_fmap eq /=. *)
  (*   assert (length vs ≤ x). by apply lookup_ge_None. *)
  (*   assert (x < length vs). by apply ids_lt_Closed_n. lia. *)
  (* Qed. *)

  (* Lemma Var_subst_list_val_lookup (x : var) (ts : list val) t (H : ts !! x = Some t) : *)
  (*   (ids x).[subst_list_val ts] = t. *)
  (* Proof. rewrite /subst_list_val. apply ids_subst_list_lookup. by rewrite list_lookup_fmap H. Qed. *)
