From main.prelude Require Import base_lang labels imports.
From main.surf_lang Require Import types.

Require Import Autosubst.Autosubst.

(* TODO remove autosubst stuf... *)

(* Important; we don't have labels anymore on destructors. *)
(* Only on cast constructs *)

Inductive expr :=
  (* base values *)
  | Lit (b : base_lit)
  | Seq (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | BinOp (binop : bin_op) (e1 e2 : expr)
  (* functions *)
  | Var (v : var)
  | Lam (e : expr)
  | App (e1 e2 : expr)
  (* sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 e2 : expr)
  (* pairs *)
  | Fst (e : expr)
  | Snd (e : expr)
  | Pair (e1 e2 : expr)
  (* error *)
  | Error (ℓ : label)
  (* Easier if we have source type, then translation is easier *)
  (* Also a proof of consistency? *)
  (* | Cast (τ1 τ2 : type) (e : expr) *)
  (* We want translation from surface to cast calculus to be definable without typing derivation... *)
  | Assert (ℓ : label) (τ1 τ2 : type) (e : expr).

Inductive typing (Γ : list type) : expr → type → Prop :=
  | Var_typed x τ : Γ !! x = Some τ → typing Γ (Var x) τ
  | Assert_typed ℓ τ1 τ2 e (Hc : consistency τ1 τ2) (H : typing Γ e τ1) :
      typing Γ (Assert ℓ τ1 τ2 e) τ2.
  (* | Unit_typed : Γ ⊢ₙₒ Lit (LitUnit) : TUnit *)
  (* | Bool_typed b : Γ ⊢ₙₒ Lit (LitBool b) : TBool *)
  (* | Int_typed z : Γ ⊢ₙₒ Lit (LitInt z) : TInt *)
  (* | BinOp_typed op e1 e2 : *)
  (*     Γ ⊢ₙₒ e1 : TInt → Γ ⊢ₙₒ e2 : TInt → Γ ⊢ₙₒ BinOp op e1 e2 : binop_res_type op *)
  (* | Seq_typed e1 e2 τ : *)
  (*     Γ ⊢ₙₒ e1 : TUnit → Γ ⊢ₙₒ e2 : τ → Γ ⊢ₙₒ Seq e1 e2 : τ *)
  (* | Pair_typed e1 e2 τ1 τ2 : *)
  (*     Γ ⊢ₙₒ e1 : τ1 → Γ ⊢ₙₒ e2 : τ2 → Γ ⊢ₙₒ Pair e1 e2 : TProd τ1 τ2 *)
  (* | Fst_typed e τ1 τ2 : Γ ⊢ₙₒ e : TProd τ1 τ2 → Γ ⊢ₙₒ Fst e : τ1 *)
  (* | Snd_typed e τ1 τ2 : Γ ⊢ₙₒ e : TProd τ1 τ2 → Γ ⊢ₙₒ Snd e : τ2 *)
  (* | InjL_typed e τ1 τ2 : Γ ⊢ₙₒ e : τ1 → Γ ⊢ₙₒ InjL e : τ1 + τ2 *)
  (* | InjR_typed e τ1 τ2 : Γ ⊢ₙₒ e : τ2 → Γ ⊢ₙₒ InjR e : TSum τ1 τ2 *)
  (* | Case_typed e0 e1 e2 τ1 τ2 τ3 : *)
  (*     Γ ⊢ₙₒ e0 : TSum τ1 τ2 → τ1 :: Γ ⊢ₙₒ e1 : τ3 → τ2 :: Γ ⊢ₙₒ e2 : τ3 → *)
  (*     Γ ⊢ₙₒ Case e0 e1 e2 : τ3 *)
  (* | If_typed e0 e1 e2 τ : *)
  (*     Γ ⊢ₙₒ e0 : TBool → Γ ⊢ₙₒ e1 : τ → Γ ⊢ₙₒ e2 : τ → Γ ⊢ₙₒ If e0 e1 e2 : τ *)
  (* | LetIn_typed e2 e1 τ1 τ2 : *)
  (*     τ1 :: Γ ⊢ₙₒ e2 : τ2 → Γ ⊢ₙₒ e1 : τ1 → Γ ⊢ₙₒ LetIn e1 e2 : τ2 *)
  (* | Lam_typed e τ1 τ2 : *)
  (*     τ1 :: Γ ⊢ₙₒ e : τ2 → Γ ⊢ₙₒ Lam e : TArrow τ1 τ2 *)
  (* (* | Fix_typed e τ : *) *)
  (*     (* Γ ⊢ₙₒ e : TArrow τ τ → Γ ⊢ₙₒ Fix e : τ *) *)
  (* (* | Rec_typed e τ1 τ2 : *) *)
  (*     (* TArrow τ1 τ2 :: τ1 :: Γ ⊢ₙₒ e : τ2 → Γ ⊢ₙₒ Rec e : TArrow τ1 τ2 *) *)
  (* | App_typed e1 e2 τ1 τ2 : *)
  (*     Γ ⊢ₙₒ e1 : TArrow τ1 τ2 → Γ ⊢ₙₒ e2 : τ1 → Γ ⊢ₙₒ App e1 e2 : τ2 *)
  (* (* | TLam_typed e τ : *) *)
  (*     (* subst (ren (+1)) <$> Γ ⊢ₙₒ e : τ → Γ ⊢ₙₒ TLam e : TForall τ *) *)
  (* (* | TApp_typed e τ τ' : Γ ⊢ₙₒ e : TForall τ → Γ ⊢ₙₒ TApp e : τ.[τ'/] *) *)
  (* | Fold_typed e τ : Γ ⊢ₙₒ e : τ.[TRec τ/] → Γ ⊢ₙₒ Fold e : TRec τ *)


(* From main.dyn_lang Require Import definition. *)

(* Fixpoint translation (e : expr) : *)

(* Inductive typing *)

(* (* Typing rules. *) *)
(* (* Only place where consistency is used are the casts.. *) *)

(* Inductive shape := S_Unit | S_Bool | S_Int | S_Inj | S_Pair | S_Lam. *)

(* Definition shape_val (v : val) := *)
(*  match v with *)
(*  | LitV b => match b with *)
(*             | LitUnit => S_Unit *)
(*             | LitBool b => S_Bool *)
(*             | LitInt n => S_Int *)
(*             end *)
(*  | LamV e => S_Lam *)
(*  | InjLV v => S_Inj *)
(*  | InjRV v => S_Inj *)
(*  | PairV v1 v2 => S_Pair *)
(*  end. *)
