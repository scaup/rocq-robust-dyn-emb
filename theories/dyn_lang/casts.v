From main.surf_lang Require Import types.
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
                   | Opposite => (* ? => ? ∘ ? *) of_shape ℓ (S_Bin bin)
                   end
        | right x => (match bin with
                     | Arrow => surround
                     | Sum => bimap_sum
                     | Product => bimap_prod
                     end)
                      (match dir with
                       | Normal => ν
                       | Opposite => ℓ
                       end)
                      (cast_upwards ℓ τ1 (match bin with
                                          | Arrow => switch (dir)
                                          | _ => dir
                                          end)) (cast_upwards ℓ τ2 dir)
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
      + by destruct dir, bin; asimpl.
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
