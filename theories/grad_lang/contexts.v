From main.prelude Require Import imports autosubst base_lang labels.
From main.grad_lang Require Import definition types.

Inductive ctx_item :=
  | CTX_Lam
  | CTX_AppL (e2 : expr)
  | CTX_AppR (e1 : expr)
  | CTX_PairL (e2 : expr)
  | CTX_PairR (e1 : expr)
  | CTX_Fst
  | CTX_Snd
  | CTX_InjL
  | CTX_InjR
  | CTX_CaseL (e1 : expr) (e2 : expr)
  | CTX_CaseM (e0 : expr) (e2 : expr)
  | CTX_CaseR (e0 : expr) (e1 : expr)
  | CTX_BinOpL (op : bin_op) (e2 : expr)
  | CTX_BinOpR (op : bin_op) (e1 : expr)
  | CTX_IfL (e1 : expr) (e2 : expr)
  | CTX_IfM (e0 : expr) (e2 : expr)
  | CTX_IfR (e0 : expr) (e1 : expr)
  | CTX_SeqL (e2 : expr)
  | CTX_SeqR (e1 : expr)
  | CTX_Ascribe (ℓ : label) (τ1 τ2 : type).

Definition fill_ctx_item (ctx : ctx_item) (e : expr) : expr :=
  match ctx with
  | CTX_Lam => Lam e
  | CTX_AppL e2 => App e e2
  | CTX_AppR e1 => App e1 e
  | CTX_PairL e2 => Pair e e2
  | CTX_PairR e1 => Pair e1 e
  | CTX_Fst => Fst e
  | CTX_Snd => Snd e
  | CTX_InjL => InjL e
  | CTX_InjR => InjR e
  | CTX_CaseL e1 e2 => Case e e1 e2
  | CTX_CaseM e0 e2 => Case e0 e e2
  | CTX_CaseR e0 e1 => Case e0 e1 e
  | CTX_BinOpL op e2 => BinOp op e e2
  | CTX_BinOpR op e1 => BinOp op e1 e
  | CTX_IfL e1 e2 => If e e1 e2
  | CTX_IfM e0 e2 => If e0 e e2
  | CTX_IfR e0 e1 => If e0 e1 e
  | CTX_SeqL e2 => Seq e e2
  | CTX_SeqR e1 => Seq e1 e
  | CTX_Ascribe ℓ τ1 τ2 => Ascribe ℓ τ1 τ2 e
  end.

Notation ctx := (list ctx_item).

Definition fill_ctx (C : ctx) (e : expr) : expr :=
 foldr fill_ctx_item e C.

(* Section context. *)

(*   Definition ctx := (list ctx_item). *)

(*   (* Does not define fill convention as in ectxi_language! *) *)
(*   Definition fill_ctx (K : ctx) (e : expr) : expr := foldr (fill_ctx_item) e K. *)

(*   Lemma fill_ctx_behavior Ki K e : fill_ctx (Ki :: K) e = fill_ctx_item Ki (fill_ctx K e). *)
(*   Proof. by simpl. Qed. *)

(*   Inductive typed_ctx : ctx → list type → type → list type → type → Prop := *)
(*     | TPCTX_nil Γ τ : *)
(*       typed_ctx nil Γ τ Γ τ *)
(*     | TPCTX_cons Γ1 τ1 Γ2 τ2 Γ3 τ3 k K : *)
(*       typed_ctx_item k Γ2 τ2 Γ3 τ3 → *)
(*       typed_ctx K Γ1 τ1 Γ2 τ2 → *)
(*       typed_ctx (k :: K) Γ1 τ1 Γ3 τ3. *)

(*   Lemma typed_ctx_typed K Γ τ Γ' τ' e : *)
(*     typed Γ e τ → typed_ctx K Γ τ Γ' τ' → typed Γ' (fill_ctx K e) τ'. *)
(*   Proof. induction 2; simpl; eauto using typed_ctx_item_typed. Qed. *)

(*   Lemma fill_ctx_app e K K' : fill_ctx K' (fill_ctx K e) = fill_ctx (K' ++ K) e. *)
(*   Proof. revert K. induction K' => K; simpl; auto. by rewrite IHK'. Qed. *)

(*   (* Alternative that follows the convention *) *)
(*   Definition fill_ctx' (K : ctx) (e : expr) : expr := foldl (flip fill_ctx_item) e K. *)

(*   Lemma fill_ctx'_behavior Ki e K : (fill_ctx' (Ki :: K) e = fill_ctx' K (fill_ctx_item Ki e)). *)
(*   Proof. by simpl. Qed. *)

(* End context. *)

(* Local Notation "|C> Γr ⊢ₙₒ C ☾ Γh ; τh ☽ : τr" := (typed_ctx C Γh τh Γr τr) (at level 74, Γr, C, Γh, τh, τr at next level). *)
(* Local Notation "|Ci> Γr ⊢ₙₒ C ☾ Γh ; τh ☽ : τr" := (typed_ctx_item C Γh τh Γr τr) (at level 74, Γr, C, Γh, τh, τr at next level). *)

(* Lemma typed_expr_append Γ e τ τs : *)
(*   Γ ⊢ₙₒ e : τ → Γ ++ τs ⊢ₙₒ e : τ. *)
(* Proof. *)
(*   intro H. *)
(*   replace e with (e.[upn (length Γ) (ren (+ (length τs)))]). *)
(*   replace (Γ ++ τs) with (Γ ++ τs ++ []) by by rewrite app_nil_r. *)
(*   apply context_gen_weakening. by rewrite app_nil_r. *)
(*   by eapply typed_n_closed. *)
(* Qed. *)

(* Lemma typed_ctx_item_append C Γ τ Γ' τ' τs : *)
(*   |Ci> Γ' ⊢ₙₒ C ☾ Γ ; τ ☽ : τ' → *)
(*   |Ci> Γ' ++ τs ⊢ₙₒ C ☾ Γ ++ τs ; τ ☽ : τ'. *)
(* Proof. *)
(*   intro H. destruct H; try econstructor; try by apply typed_expr_append. *)
(*   change (τ :: Γ ++ τs ) with ((τ :: Γ) ++ τs). by apply typed_expr_append. *)
(*   change (τ1 :: Γ ++ τs ) with ((τ1 :: Γ) ++ τs). by apply typed_expr_append. *)
(*   change (τ2 :: Γ ++ τs ) with ((τ2 :: Γ) ++ τs). by apply typed_expr_append. *)
(*   change (τ2 :: Γ ++ τs ) with ((τ2 :: Γ) ++ τs). by apply typed_expr_append. *)
(*   change (τ1 :: Γ ++ τs ) with ((τ1 :: Γ) ++ τs). by apply typed_expr_append. *)
(* Qed. *)

(* Lemma typed_ctx_append C Γ τ Γ' τ' τs : *)
(*   |C> Γ' ⊢ₙₒ C ☾ Γ ; τ ☽ : τ' → *)
(*   |C> Γ' ++ τs ⊢ₙₒ C ☾ Γ ++ τs ; τ ☽ : τ'. *)
(* Proof. *)
(*   intro H. *)
(*   induction H. *)
(*   - constructor. *)
(*   - econstructor. 2: eapply IHtyped_ctx. *)
(*     by apply typed_ctx_item_append. *)
(* Qed. *)

(* Lemma typed_ctx_app Γ Γ' Γ'' K K' τ τ' τ'' : *)
(*   |C> Γ'' ⊢ₙₒ K' ☾ Γ' ; τ' ☽ : τ'' → *)
(*   |C> Γ' ⊢ₙₒ K ☾ Γ ; τ ☽ : τ' → *)
(*   |C> Γ'' ⊢ₙₒ (K' ++ K) ☾ Γ ; τ ☽ : τ''. *)
(* Proof. *)
(*   revert K Γ Γ' Γ'' τ τ' τ''; induction K' => K Γ Γ' Γ'' τ τ' τ''; simpl. *)
(*   - by inversion 1; subst. *)
(*   - intros Htc1 Htc2. inversion Htc1; subst. *)
(*     econstructor; last eapply IHK'; eauto. *)
(* Qed. *)
