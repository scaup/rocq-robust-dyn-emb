From main.prelude Require Import imports autosubst big_op_three.
From main.surf_lang Require Import types.
From main.dyn_lang Require Import definition lemmas lib.
From main.logrel Require Import definition.
From main.logrel.lib Require Import weakestpre rfn.

From iris.si_logic Require Export bi.
From iris.proofmode Require Import tactics.

Section trivialities.

  Context {ν : label} {Hν : NeverOccurs ν}.


  (* Lemma rfn_bind'' Ki e Ki' e' Ψ Φ L t t' (eq : t = (fill_item Ki e)) (eq' : t' = (fill_item Ki' e')) : *)
  (*   ⊢ rfn Ψ L e e' -∗ (∀ v v', Ψ v v' -∗ rfn Φ L (fill_item Ki (of_val v)) (fill_item Ki' (of_val v'))) -∗ rfn Φ L t t'. *)
  (* Proof. rewrite eq eq'. Admitted. *)

  Lemma rfn_s_l e2 {e1} (H : step_not_error e1 e2) Φ L e' :
    ⊢ ▷ rfn Φ L e2 e' -∗ rfn Φ L e1 e'.
  Proof.
    iIntros "H".
    rewrite /rfn (wp_unfold _ _ e1) /wp_pre.
    by iExists (Take_NE_Step _ _ H).
  Qed.

  Lemma rfn_s_r e2 {e1} (H : step_not_error e1 e2) Φ L e :
    ⊢ rfn Φ L e e2 -∗ rfn Φ L e e1.
  Proof.
    iIntros "H". iApply (wp_impl with "H").
    iIntros (ℓ) "H". iDestruct "H" as (t' ℓ') "(%Hs & Hf & Hl)".
    iExists t', ℓ'. iFrame. iPureIntro.
    { by eapply rtc_l. }
    iIntros (v) "H". iDestruct "H" as (v') "[%Hs Hf]". iExists v'. iFrame.
    { iPureIntro. by eapply rtc_l. }
  Qed.

  (* Lemma head_step_step_not_error {e} {e'} (H : head_step_not_error e e') : *)
  (*   step_not_error e e'. *)
  (* Proof. apply (SNE_Normal []). Qed. *)

  Lemma rfn_id_lr Φ L e e' :
    ⊢ rfn Φ L e e' -∗ rfn Φ L (AppAn (of_val Id) e) (AppAn (of_val Id) e').
  Proof.
    (* bind *)
    change (AppAn (of_val ?v) ?e') with (fill [AppRCtx ν v] e').
    iIntros "H". iApply (rfn_bind' with "H").
    (* steps *)
    iIntros (v v') "H".
    iApply (rfn_s_l (of_val v)).
    { apply (SNE_Normal []). econstructor.
      by rewrite to_of_val. }
    iApply (rfn_s_r (of_val v')).
    { apply (SNE_Normal []). econstructor.
      by rewrite to_of_val. }
    (* bookkeeping *)
    iNext. iApply rfn_val; auto.
  Qed.

  (* Definition to_body (v : val) : option expr := *)
  (*   match v with *)
  (*   | LamV e => Some e *)
  (*   | _ => None *)
  (*   end. *)

  (* Lemma to_body_sane v e (H : to_body v = Some e) : v = LamV e. *)
  (* Proof. destruct v; naive_solver. Qed. *)


  Definition to_elim_help (Ki : ectx_item) : option (label * shape) :=
    match Ki with
    | AppLCtx ℓ e2 => Some (ℓ, S_Bin Arrow) (* ? *)
    (* | AppRCtx ℓ v1 => Some (ℓ, S_Bin Arrow) *)
    | FstCtx ℓ => Some (ℓ, S_Bin Product)
    | SndCtx ℓ => Some (ℓ, S_Bin Product)
    | CaseCtx ℓ e1 e2 => Some (ℓ, S_Bin Sum)
    | IfCtx ℓ e2 e3 => Some (ℓ, S_Base Bool)
    (* | BinOpLCtx ℓ op e2 => Some (ℓ, S_Base Int) *)
    | BinOpRCtx ℓ op v1 => Some (ℓ, S_Base Int)
    | SeqCtx ℓ e2 => Some (ℓ, S_Base Unit)
    | _ => None
    end.

  Definition anonimize (Ki : ectx_item) : ectx_item :=
    match Ki with
    | AppLCtx ℓ e2 => AppLCtx ν e2
    | AppRCtx ℓ v1 => AppRCtx ν v1
    | FstCtx ℓ => FstCtx ν
    | SndCtx ℓ => FstCtx ν
    | CaseCtx ℓ e1 e2 => CaseCtx ν e1 e2
    | IfCtx ℓ e2 e3 => IfCtx ν e2 e3
    | BinOpLCtx ℓ op e2 => BinOpLCtx ν op e2
    | BinOpRCtx ℓ op v1 => BinOpRCtx ν op v1
    | SeqCtx ℓ e2 => SeqCtx ν e2
    | rem => rem
    end.

  Instance decision_eq : EqDecision shape.
  Proof. solve_decision. Qed.

  Lemma converging_wp {e e'} t (H : step_not_error e t) (H' : step_not_error e' t) Φ L :
    wp Φ L e' ⊣⊢ wp Φ L e.
  Proof. iSplit; iIntros "H"; by rewrite -(wp_s H) -(wp_s H'). Qed.


        (*   to_elim_help Ki = Some (ℓ, s) → *)
        (* shape v ≠ Ki → *)
        (* faulty ℓ (fill_item Ki v) *)

  Definition assume_shape_val Ki ℓ s Φ L (H : to_elim_help Ki = Some (ℓ, s)) v :
     ⊢ (⌜ shape_val v = s ⌝ -∗ wp Φ L (fill_item (anonimize Ki) (of_val v))) -∗ L ℓ -∗
         wp Φ L (fill_item Ki (of_val v)).
  Proof.
    iIntros "H Hℓ".
    destruct Ki; inversion_clear H.
    - simpl. destruct (decide (shape_val v = S_Bin Arrow)) as [eq | neq];
        [iSpecialize ("H" $! eq) | iClear "H"].
      + destruct v; try by (try destruct (_ : base_lit); inversion eq).
        change (App ?ℓ (of_val ?v) ?e) with (fill [AppRCtx ℓ v] e).
        iApply wp_bind. iDestruct (wp_bind_inv with "H") as "H".
        iApply (wp_impl with "H"); auto.
        iIntros (v) "H".
        iApply (converging_wp with "H"); by apply (SNE_Normal []); econstructor; rewrite to_of_val.
      + iApply wp_faulty. constr
      (*   simpl.k *)

      (*   inversion eq. *)

      (*   ; [ destruct b; by inversion eq | | ]. try by inversion eq; naive_solver. *)
      (*   iApply (converging_wp  with "H"). *)
      (*   admit. admit. *)
      (* + *)

  Admitted.

  Definition assume_shape Ki ℓ s Ψ Φ L (H : to_elim_help Ki = Some (ℓ, s)) e :
     ⊢ wp Ψ L e -∗ L ℓ -∗
       (∀ v, Ψ v -∗ ⌜ shape_val v = s ⌝ -∗ wp Φ L (fill_item (anonimize Ki) (of_val v))) -∗
         wp Φ L (fill_item Ki e).
  Proof.
    iIntros "#H1 #H2 #H3".
    change (fill_item Ki e) with (fill [Ki] e).
    iApply (wp_bind' with "H1"). iIntros (v) "#HΨ".
    iApply assume_shape_val; eauto. by iApply "H3".
  Qed.


  Lemma prod_rel_lr f1 f1' Φ1 Φ1' f2 f2' Φ2 Φ2' L :
    ⊢ ▷^4 arrow_rel G_NoThanks
         Φ1 Φ1' L f1 f1' -∗
      ▷^4 arrow_rel G_NoThanks
         Φ2 Φ2' L f2 f2' -∗
      arrow_rel G_NoThanks
         (prod_rel Φ1 Φ2) (prod_rel Φ1' Φ2') L
         (bimap_prod ν f1  f2) (bimap_prod ν f1' f2').
  Proof.
    iIntros "H1 H2".
    iExists _, _. repeat iSplit; eauto. simpl.
    iIntros (w w') "Hww'". iDestruct "Hww'" as (v1 v1' v2 v2') "(-> & -> & Hv1 & Hv2)".
    change (App ν (Lam ?e) ?e') with (fill [AppRCtx ν (LamV e)] e').
    iApply rfn_s_l.
    { eapply (SNE_Normal [AppRCtx _ _ ]).
      repeat econstructor; by rewrite to_of_val. }
    iApply rfn_s_r.
    { eapply (SNE_Normal [AppRCtx _ _ ]).
      repeat econstructor; by rewrite to_of_val. }
    iApply rfn_s_l.
    { eapply (SNE_Normal []).
      repeat econstructor; by rewrite to_of_val. }
    iApply rfn_s_r.
    { eapply (SNE_Normal []).
      repeat econstructor; by rewrite to_of_val. }
    asimpl.
    change (App ν (Lam ?e) ?e') with (fill [AppRCtx ν (LamV e)] e').
    iApply rfn_s_l.
    { eapply (SNE_Normal [AppRCtx _ _ ]).
      repeat econstructor; by rewrite to_of_val. }
    iApply rfn_s_r.
    { eapply (SNE_Normal [AppRCtx _ _ ]).
      repeat econstructor; by rewrite to_of_val. }
    iApply rfn_s_l.
    { eapply (SNE_Normal []).
      repeat econstructor; by rewrite to_of_val. }
    iApply rfn_s_r.
    { eapply (SNE_Normal []).
      repeat econstructor; by rewrite to_of_val. }
    repeat iNext.
    asimpl.
    change (Pair ?e ?e') with (fill [PairLCtx e'] e).
    iDestruct "H1" as (e1 e1') "(-> & -> & H1)".
    iSpecialize ("H1" with "Hv1").
    iApply rfn_s_l.
    { eapply SNE_Normal.
      repeat econstructor; by rewrite to_of_val. }
    iApply rfn_s_r.
    { eapply (SNE_Normal).
      repeat econstructor; by rewrite to_of_val. }
    iApply (rfn_bind' with "H1").
    iNext. iIntros (w w') "HΦ".
    iDestruct "H2" as (e2 e2') "(-> & -> & H2)". simpl.
    change (Pair (of_val ?v) ?e') with (fill [PairRCtx v] e').
    iApply rfn_s_l.
    { eapply SNE_Normal.
      repeat econstructor; by rewrite to_of_val. }
    iApply rfn_s_r.
    { eapply SNE_Normal.
      repeat econstructor; by rewrite to_of_val. }
    iSpecialize ("H2" with "Hv2").
    iApply (rfn_bind' with "H2").
    iNext. iIntros (v v') "Hvv'". simpl.
    iApply (rfn_val (PairV _ _) (PairV _ _)); eauto.
    iExists _, _, _, _. iFrame; auto.
  Qed.

End trivialities.


(*     iExists (to_body ()) *)

(*     rewrite /arrow_rel. iIntros (v v'). *)




(*   rfn Φ L ((bimap_prod f1 f2) (bimap_prod f1 f2)) *)

(*   Lemma rfn_bimap_prod ℓ f1 f1' f2 f2' : *)
(*     rfn Φ L (of_val f1) (of_val f2) *)
(*         rfn Φ L ((bimap_prod f1 f2) () ) *)



(*   casts makes use of ... *)
(*   so first lets get ... *)


(*   "Hee'" : exprel_typed (Base B) L e e' *)

(*   --------------------------------------∗ *)
(*   exprel_typed (Base B) L (AppAn (of_val (of_shape ν (S_Base B))) e) *)
(*     (AppAn (of_val (of_shape ν (S_Base B))) e') *)



(* (* very small lemmas for bimap etc... *) *)
(* (* ----------------------- *) *)


(* (* stating fundeamental... *) *)
(* (* ----------------------- *) *)


(* From main.logrel Require Import definition. *)
(* From main.maps Require Import dyn_to_surf.definition surf_to_dyn.definition. *)

(* Section fundamental_bare_rfn_demb. *)

(*   Context {ν : label} {Hν : NeverOccurs ν}. *)

(*   Definition Δ (e : expr) : label -d> label -d> siProp. *)
(*   Admitted. *)

(*   Lemma cast_closed ℓ τ1 τ2 : Closed (of_val $ cast ℓ τ1 τ2). *)
(*   Proof. *)


(*   Lemma emb_subst (e : expr) σ : ⌊ (⌜⌜ e ⌝⌝) ⌋.[σ] = ⌊ (⌜⌜ e.[σ] ⌝⌝) ⌋. *)
(*   Proof. *)
(*     induction e. *)
(*     - rewrite 1 /dyn_emb. simpl. *)

(*     (asimpl; naive_solver). try by naive_solver. *)

(*   Lemma fundamental_bare_rfn_demb (e : expr) n (Hne : Closed_n n e) : *)
(*     open_exprel_typed (replicate n Unknown) e  (⌊ (⌜⌜ e ⌝⌝) ⌋) (Δ e) Unknown. *)
(*   Proof. *)
(*     generalize dependent n. *)
(*     iInduction e as *)
(*       [ (* Lit *) b | (* Seq *) ℓ e1 e2 | (*If*) ℓ e0 e1 e2 *)
(*       | (* BinOp *) ℓ binop e1 e2 | (* Var *) v | (* Lam *) e *)
(*       | (* App *) ℓ e1 e2 | (* InjL *) e | (* InjR *) e *)
(*       | (* Case *) ℓ e e1 e2 | (* Fst *) ℓ e | (* Snd *) ℓ e *)
(*       | (* Pair *) e1 e2 | (* Error *) ℓ] "IH"; *)
(*       iIntros (n Hn P vs vs') "[%Hlp Hvsvs']". *)
(*     - admit. *)
(*     - asimpl. admit. *)
(*     - asimpl. iSpecialize ("IH" $! n ). *)
(*       (* specialize with P, *) *)
(*       (* proof obligation for using "IH"; less_possibilities_then (Δ e0) P *) *)
(*       (* should be easy; we have Δ e0 ≤ Δ (If ℓ e0 e2 e3) *) *)

(*       (* ℓ toegelaten, *) *)
(*       (* (If ℓ e0 e1 e2) (If ν (cast ℓ B e0') e1' e2') *) *)

(*       admit. *)


(*     - admit. *)
(*     - asimpl. admit. *)
(*     - (* Lam *) *)
(*       (* simpl. *) *)
(*       (* just prove that the two lambdas are in the value relation for unknown *) *)
(*       (* ok, so to prove : ▷ (∀ w, w'. unknown P w w' -∗ \x.e w \x.e w'   ) *) *)
(*       (* forget about later... *) *)
(*       (* yeah, we can use "IH" with extended list and P... *) *)

(*       (* --------- correction *) *)
(*       (* this would now be ∃ e, e', v = λe, v'=λe' ∗ ▷ (∀ w w'...)  *) *)
(*       admit. *)
(*     - (* app *) *)
(*       (* exprel_untyped P e1 e1' -∗ *) *)
(*       (* exprel_untyped P e2 e2' -∗ *) *)
(*       (* exprel_untyped P (App ℓ e1 e2) (AppAn (e1' : (?=>?→?)ℓ) e2') *) *)

(*       (* one bind *) *)
(*       (* valrel_untyped P v1 v1' -∗ *) *)
(*       (* exprel_untyped P e2 e2' -∗ *) *)
(*       (* exprel_untyped P (App ℓ v1 e2) (AppAn (v1' : (?=>?→?)ℓ) e2') *) *)

(*       (* just a step *) *)
(*       (* valrel_untyped P v1 v1' -∗ *) *)
(*       (* exprel_untyped P e2 e2' -∗ *) *)
(*       (* exprel_untyped P (App ℓ v1 e2) (AppAn (λx. App ℓ v1' x) e2') *) *)

(*       (* second bind *) *)
(*       (* valrel_untyped P v1 v1' -∗ *) *)
(*       (* valrel_untyped P v2 v2' -∗ *) *)
(*       (* exprel_untyped P (App ℓ v1 v2) (App ℓ v1' v2') *) *)

(*       (* Can we do this? *) *)

(*       (* case analyis on v1 v1'; *) *)
(*       (*   in all the different branches but the arrow branch, we get (on left and right!) stuckness on ℓ *) *)
(*       (*      succes! becasuse ℓ is in P *) *)
(*       (*   in the arrow branch, we have (▷ ∀ w w', ....) *) *)
(*       (*      we have to adjust definition I think... *) *)
(*       (*      suppose this as its definition : (∃ e, e', v = λe, v'=λe' ∗ ▷ (∀ w w'. Rww' -> E (e.[v/]) (e'.[v/]) ...) ) *) *)
(*       (*      then we can take a step (both sides); and get what we need *) *)



(*       admit. *)




(*     - admit. *)
(*     - admit. *)
(*     - admit. *)
(*     - admit. *)
(*     - admit. *)
(*     - admit. *)




(*     (* open_exprel_typed (replicate n (valrel_unknown (Δ e))) e  (⌊ ⌜⌜ e ⌝⌝ ⌋) Unknown. *) *)





(*   Fixpoint getLabels (e : expr) := *)
(*     match e with *)
(*     | Lit b => ∅ *)
(*     | Seq ℓ e1 e2 => *)
(*         {[ ℓ ]} ∪ getLabels e1 ∪ getLabels e2 *)
(*     | If ℓ e0 e1 e2 => *)
(*         {[ ℓ ]} ∪ getLabels e0 ∪ getLabels e1 ∪ getLabels e2 *)
(*     | BinOp ℓ binop e1 e2 => *)
(*         {[ ℓ ]} ∪ getLabels e1 ∪ getLabels e2 *)
(*     | Var v => ∅ *)
(*     | Lam e => *)
(*         getLabels e *)
(*     | App ℓ e1 e2 => *)
(*         {[ ℓ ]} ∪ getLabels e1 ∪ getLabels e2 *)
(*     | InjL e => *)
(*         getLabels e *)
(*     | InjR e => *)
(*         getLabels e *)
(*     | Case ℓ e0 e1 e2 => *)
(*         {[ ℓ ]} ∪ getLabels e0 ∪ getLabels e1 ∪ getLabels e2 *)
(*     | Fst ℓ e => *)
(*         {[ ℓ ]} ∪ getLabels e *)
(*     | Snd ℓ e => *)
(*         {[ ℓ ]} ∪ getLabels e *)
(*     | Pair e1 e2 => *)
(*         getLabels e1 ∪ getLabels e2 *)
(*     | Error ℓ => *)
(*         {[ ℓ ]} *)
(*     end. *)



(*     {[ e ]}. Set *)

(*   getLabels (e1 e2) *)

(*   e Δe (Δ = all labels in e) *)

(*   Δe1   e2 *)

(*   Fixpoint labelInExpr (ℓ : label) (e : expr) : Prop := *)
(*     match e with *)
(*     | Lit b => False *)
(*     | Seq ℓ' e1 e2 => (ℓ = ℓ') ∨ labelInExpr ℓ e1 ∨ labelInExpr ℓ e2 *)
(*     | If ℓ' e0 e1 e2 => (ℓ = ℓ') ∨ labelInExpr ℓ e0 ∨ labelInExpr ℓ e1 ∨ labelInExpr *)
(*     | BinOp ℓ binop e1 e2 => False *)
(*     | Var v => False *)
(*     | Lam e => False *)
(*     | App ℓ e1 e2 => False *)
(*     | InjL e => False *)
(*     | InjR e => False *)
(*     | Case ℓ e0 e1 e2 => False *)
(*     | Fst ℓ e => False *)
(*     | Snd ℓ e => False *)
(*     | Pair e1 e2 => False *)
(*     | Error ℓ => False *)
(*     end. *)


(*   Fixpoint labelInExpr (ℓ : label) (e : expr) : bool := *)
(*     match e with *)
(*     | Lit b => false *)
(*     | Seq ℓ' e1 e2 => (ℓ = ℓ') ∨ labelInExpr ℓ e1 ∨ labelInExpr ℓ e2 *)
(*     | If ℓ e0 e1 e2 => false *)
(*     | BinOp ℓ binop e1 e2 => false *)
(*     | Var v => false *)
(*     | Lam e => false *)
(*     | App ℓ e1 e2 => false *)
(*     | InjL e => false *)
(*     | InjR e => false *)
(*     | Case ℓ e0 e1 e2 => false *)
(*     | Fst ℓ e => false *)
(*     | Snd ℓ e => false *)
(*     | Pair e1 e2 => false *)
(*     | Error ℓ => false *)
(*     end. *)
