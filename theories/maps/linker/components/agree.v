From main.prelude Require Import imports autosubst base_lang lists labels.
From main.grad_lang Require Import types.
From main.dyn_lang Require Import definition contexts lib casts.
From main.maps Require Import grad_into_dyn.definition.
From main.maps.linker.components Require Import dyn grd.

Section agree.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Lemma LamN_agree n e : ⌊ grd.LamN n e ⌋ = dyn.LamN n ⌊ e ⌋.
  Proof. induction n; auto. simpl. by rewrite IHn. Qed.

  Lemma LamN_ctx_agree n : trns_ctx $ grd.LamN_ctx n = dyn.LamN_ctx n.
  Proof. induction n; auto. simpl. by rewrite IHn. Qed.

  Lemma AppWithList_agree e fs :
    ⌊ grd.AppWithList e fs ⌋ = dyn.AppWithList ⌊ e ⌋ ((fun f => ⌊ f ⌋) <$> fs).
  Proof.
    induction fs as [|f fs']; first auto.
    rewrite /= /AppAn. f_equiv. by rewrite /IHfs'.
  Qed.

  Lemma AppWithList_ctx_agree ts :
    trns_ctx $ grd.AppWithList_ctx ts = dyn.AppWithList_ctx (trns <$> ts).
  Proof.
    induction ts as [|t ts']; first auto.
    rewrite /=. f_equiv. by rewrite IHts'.
  Qed.

  Lemma wrap_ctx_vars_ascribe_up_agree (ℓ : label) (Γ : list type) :
    trns <$> (grd.wrap_ctx_vars_ascribe_up ℓ Γ) = dyn.wrap_ctx_vars_ascribe_up ℓ Γ.
  Proof.
    rewrite /grd.wrap_ctx_vars_ascribe_up /dyn.wrap_ctx_vars_ascribe_up.
    rewrite fmap_imap. apply imap_ext. intros. simpl. rewrite /cast'.
    destruct (consistency_decision x Unknown); auto.
  Qed.

End agree.
