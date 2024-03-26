From main.prelude Require Import imports autosubst.
From main.grad_lang Require Import definition.

Section min_def_grad.

  Definition LamN_g (n : nat) : expr → expr := Nat.iter n Lam.

  Definition AppWithList_g (e : expr) (ts : list expr) :=
    fold_right (fun f e => App e f) e ts.

  Definition WrapContextVarsFrom_g (n : nat) (fs : list expr) : list expr :=
    (imap (fun l f => (App f (Var (l + n)))) fs).
  Definition WrapContextVars_g (fs : list expr) : list expr :=
    WrapContextVarsFrom_g 0 fs.

  Definition Wrap_g (e : expr) (fs : list expr) :=
    let n := length fs in
    AppWithList_g (LamN_g n e) (WrapContextVars_g fs).

End min_def_grad.

From main.maps Require Import dyn_embedding.definition.
From main.maps Require Import grad_into_dyn.definition.
From main.dyn_lang Require Import definition lib.

Section min_def_dyn.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Definition LamN_d (n : nat) : expr → expr := Nat.iter n Lam.
  Lemma LamN_dg_agree n e : ⌊ LamN_g n e ⌋ = LamN_d n ⌊ e ⌋.
  Proof. induction n; auto. simpl. by rewrite IHn. Qed.

  Definition AppWithList_d (e : expr) (fs : list expr) :=
    fold_right (fun f e => AppAn e f) e fs.
  Lemma AppWithList_gd_agree e fs :
    ⌊ AppWithList_g e fs ⌋ = AppWithList_d ⌊ e ⌋ ((fun f => ⌊ f ⌋) <$> fs).
  Proof.
    induction fs as [|f fs']; first auto.
    rewrite /= /AppAn. f_equiv. by rewrite /IHfs'.
  Qed.

  Definition WrapContextVarsFrom_d (n : nat) (fs : list expr) : list expr :=
    (imap (fun l f => (AppAn f (Var (l + n)))) fs).
    (* zip_with AppAn fs (Var <$> seq n (length fs)). *)
  Lemma WrapContextsVarsFrom_dg_agree (n : nat) fs :
    trns <$> (WrapContextVarsFrom_g n fs) = WrapContextVarsFrom_d n (trns <$> fs).
  Proof.
    rewrite /WrapContextVarsFrom_d /WrapContextVarsFrom_g /=.
    apply list_eq. intro i.
    destruct (decide (i < length fs)) as [H' | H'].
    - destruct (lookup_lt_is_Some_2 fs i) as [f eq]; try lia.
      repeat rewrite list_lookup_fmap.
      repeat rewrite list_lookup_imap.
      repeat rewrite list_lookup_fmap /=. simplify_option_eq.
      by rewrite /AppAn.
    - repeat rewrite lookup_ge_None_2; try lia; auto.
      repeat rewrite imap_length fmap_length. by apply Nat.le_ngt.
      repeat rewrite fmap_length imap_length. by apply Nat.le_ngt.
  Qed.

 Definition WrapContextVars_d (fs : list expr) : list expr :=
    WrapContextVarsFrom_d 0 fs.
  Lemma WrapContextsVars_dg_agree (fs : list sf_expr) :
    trns <$> (WrapContextVars_g fs) = WrapContextVars_d (trns <$> fs).
  Proof. apply WrapContextsVarsFrom_dg_agree. Qed.

  Definition Wrap_d (e : expr) (fs : list expr) :=
    let n := length fs in
    AppWithList_d (LamN_d n e) (WrapContextVars_d fs).
  Lemma Wrap_dg_agree e fs :
    ⌊ Wrap_g e fs ⌋ = Wrap_d ⌊ e ⌋ (trns <$> fs) .
  Proof.
    rewrite /Wrap_d /Wrap_g fmap_length AppWithList_gd_agree.
    rewrite -WrapContextsVars_dg_agree LamN_dg_agree. auto.
  Qed.

End min_def_dyn.

(* check stuff *)
(*   Context (e t0 t1 t2 t3 t4 f0 f1 f2 f3 f4 : expr). *)
(*   Compute (AppWithList_g e ([t0; t1; t2; t3] )). *)
(*   (* e1 = f0 (var 0) *) *)
(*   (* e2 = f1 (var 1) *) *)
(*   (* ... *) *)

(*   Compute (WrapContextVars_g ([f0; f1; f2; f3])). *)

(*   Compute (WrapContextVarsFrom_g 5 ([f0; f1; f2; f3])). *)
(*   Compute (WrapContextVarsFrom_g 5 ([f0; f1; f2; f3])). *)


(*   Compute (AppWithList_g (LamN_g 4 e) (WrapContextVars_g ([f0; f1; f2; f3]))). *)
(*   Compute (AppWithList_g (LamN_g 0 e) (WrapContextVars_g ([]))). *)


(*   Compute ((Wrap_g e ([f0; f1; f2; f3]))). *)
