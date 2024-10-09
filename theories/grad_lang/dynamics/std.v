From main.prelude Require Import base_lang labels imports autosubst.
From main.grad_lang Require Export definition types definition.

(* this is a standard representation for the dynamics of our cast calculus *)

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Inductive val : Type :=
  | LitV (b : base_lit)
  | LamV (e : {bind 1 of expr})
  | CastArrowV (ℓ : label) (τ1 τ2 τ3 τ4 : type) (v : val)
  | CastGroundUpV (ℓ : label) (G : shape) (v : val)
  (* | CastGroundDownArrowV (ℓu ℓd : label) (G : shape) (nG : G ≠ S_Bin Arrow) (v : val) *)
  | CastArrowDownV (ℓ : label) (v : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | PairV (v1 v2 : val).

Definition shape_val (v : val) : shape :=
 match v with
 | LitV b => match b with
            | LitUnit => S_Base Unit
            | LitBool b => S_Base Bool
            | LitInt n => S_Base Int
            end
 | LamV e => S_Bin Arrow
 | InjLV v => S_Bin Sum
 | InjRV v => S_Bin Sum
 | PairV v1 v2 => S_Bin Product
 | CastArrowV ℓ τ1 τ2 τ3 τ4 v => S_Bin Arrow
 | CastGroundUpV ℓ G v => G
 | CastArrowDownV ℓ v => S_Bin Arrow
 end.

Fixpoint of_val (v : val) : expr :=
 match v with
 | LamV e => Lam e
 | LitV v => Lit v
 | CastArrowV ℓ τ1 τ2 τ3 τ4 v =>
     Cast ℓ (Bin Arrow τ1 τ2) (Bin Arrow τ3 τ4) (of_val v)
 | CastGroundUpV ℓ G v =>
     Cast ℓ (of_shape G) Unknown (of_val v)
 | CastArrowDownV ℓ v =>
     Cast ℓ Unknown (Bin Arrow Unknown Unknown) (of_val v)
 (* | CastGroundDownArrowV ℓu ℓd G nG v => *)
 (*     Cast ℓd Unknown (Bin Arrow Unknown Unknown) *)
       (* (Cast ℓu (of_shape G) Unknown (of_val v)) *)
 | PairV v1 v2 => Pair (of_val v1) (of_val v2)
 | InjLV v => InjL (of_val v)
 | InjRV v => InjR (of_val v)
 end.

Fixpoint to_val (e : expr) : option val :=
 match e with
 | Lam e => Some (LamV e)
 | Lit e => Some (LitV e)
 | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
 | InjL e => InjLV <$> to_val e
 | InjR e => InjRV <$> to_val e
 | Cast ℓ τ1 τ2 e => v ← to_val e;
    (match τ1, τ2 with
     | τ1, Unknown => (fun G => CastGroundUpV ℓ G v) <$> to_ground τ1
     | Unknown, Bin Arrow Unknown Unknown => Some $ CastArrowDownV ℓ v
     | Bin Arrow τ1' τ2', Bin Arrow τ3' τ4' => Some $ CastArrowV ℓ τ1' τ2' τ3' τ4' v
     | _, _ => None
     end)
 | _ => None
 end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  induction v; try simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
  destruct G; (try destruct bin); simpl; by simplify_option_eq.
Qed.
Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
 revert v; induction e; intros ? ?; simplify_option_eq; auto with f_equal.
 destruct τ1; destruct τ2; (try destruct bin);
   (try destruct bin0); simplify_option_eq; auto with f_equal.
 destruct τ2_1; destruct τ2_2; simplify_option_eq; auto with f_equal.
Qed.

Definition bin_op_eval (op : bin_op) (z1 z2 : Z) : val :=
 match op with
 | PlusOp => LitV $ LitInt (z1 + z2)%Z
 | MinusOp => LitV $ LitInt (z1 - z2)
 | LeOp => LitV $ LitBool $ bool_decide (z1 ≤ z2)%Z
 | LtOp => LitV $ LitBool $ bool_decide (z1 < z2)%Z
 | EqOp => LitV $ LitBool $ bool_decide (z1 = z2)
 end.

Inductive head_step_no_cast : expr → expr → Prop :=
  (* base values destructors *)
  | HN_Seq e :
    head_step_no_cast (Seq (Lit LitUnit) e) e
  | HN_If b e1 e2 :
    head_step_no_cast (If (Lit $ LitBool $ b) e1 e2) (match b with
                                              | true => e1
                                              | false => e2
                                              end)
  | HN_BinOp (op : bin_op) z1 z2 :
    head_step_no_cast (BinOp op (Lit $ LitInt z1) (Lit $ LitInt z2))
                        (of_val $ bin_op_eval op z1 z2)
  (* sums values destructors *)
  | HN_Case_L e0 v0 e1 e2 :
    to_val e0 = Some v0 →
    head_step_no_cast (Case (InjL e0) e1 e2) (e1.[of_val v0/])
  | HN_Case_R e0 v0 e1 e2 :
    to_val e0 = Some v0 →
    head_step_no_cast (Case (InjR e0) e1 e2) (e2.[of_val v0/])
  (* pair values destructors *)
  | HN_Fst e1 v1 e2 v2 :
    to_val e1 = Some v1 →
    to_val e2 = Some v2 →
    head_step_no_cast (Fst (Pair e1 e2)) e1
  | HN_Snd e1 v1 e2 v2 :
    to_val e1 = Some v1 →
    to_val e2 = Some v2 →
    head_step_no_cast (Snd (Pair e1 e2)) e2
  (* lambda destructors *)
  | HN_App eb ea va :
    to_val ea = Some va →
    head_step_no_cast (App (Lam eb) ea) (eb.[ea/]).

Inductive head_step_cast : expr → expr → Prop :=
  (* CASTS *)
  (* Between same base, unknown *)
  | HN_Cast_IdBase ℓ B e v :
    to_val e = Some v →
    head_step_cast (Cast ℓ (Base B) (Base B) e) e
  | HN_Cast_IdUnk ℓ e v :
    to_val e = Some v →
    head_step_cast (Cast ℓ Unknown Unknown e) e
  (* Ground => unknown => ground (that is not a ground) *)
  | HN_Cast_GG_Succeed ℓ1 ℓ2 G e v :
    G ≠ S_Bin Arrow →
    to_val e = Some v →
    head_step_cast (Cast ℓ2 Unknown (of_shape G) (Cast ℓ1 (of_shape G) Unknown e)) e
  | HN_Cast_GG_Fail ℓ1 ℓ2 G1 G2 e v :
    G2 ≠ S_Bin Arrow →
    G1 ≠ G2 →
    to_val e = Some v →
    head_step_cast (Cast ℓ2 Unknown (of_shape G2) (Cast ℓ1 (of_shape G1) Unknown e)) (Error ℓ2)
  (* Ground => unknown => ground; with lazy down-cast to function *)
  | HN_Cast_GG_App ℓ1 ℓ2 G e v ea va :
    to_val e = Some v →
    to_val ea = Some va →
    head_step_cast
      (App (Cast ℓ2 Unknown (Bin Arrow Unknown Unknown) (Cast ℓ1 (of_shape G) Unknown e))
           ea
      ) (match G with
         | S_Bin Arrow => App e ea
         | _ => Error ℓ2
         end)
  (* between arrows on application *)
  | HN_App_Cast ℓ τ1 τ2 τ3 τ4 e v ea va :
    to_val e = Some v →
    to_val ea = Some va →
    head_step_cast
      (App (Cast ℓ (Bin Arrow τ1 τ2) (Bin Arrow τ3 τ4) e) ea)
      (Cast ℓ τ2 τ4 (App e (Cast ℓ τ3 τ1 ea)))
  (* between prods *)
  | HN_Prod_Cast ℓ τ1 τ2 τ1' τ2' e1 v1 e2 v2 :
    to_val e1 = Some v1 →
    to_val e2 = Some v2 →
    head_step_cast
      (Cast ℓ (Bin Product τ1 τ2) (Bin Product τ1' τ2') (Pair e1 e2))
      (Pair (Cast ℓ τ1 τ1' e1) (Cast ℓ τ2 τ2' e2))
  (* between sums *)
  | HN_Sum_CastL ℓ τ1 τ2 τ1' τ2' e1 v1 :
    to_val e1 = Some v1 →
    head_step_cast
      (Cast ℓ (Bin Sum τ1 τ2) (Bin Sum τ1' τ2') (InjL e1))
      (InjL (Cast ℓ τ1 τ1' e1))
  | HN_Sum_CastR ℓ τ1 τ2 τ1' τ2' e2 v2 :
    to_val e2 = Some v2 →
    head_step_cast
      (Cast ℓ (Bin Sum τ1 τ2) (Bin Sum τ1' τ2') (InjR e2))
      (InjR (Cast ℓ τ2 τ2' e2))
  (* factoring from/to non-ground to/from unknown *)
  | HN_Cast_Ground ℓ τ G e v :
    closed_ground τ = Some G →
    to_ground τ = None →
    to_val e = Some v →
    head_step_cast
      (Cast ℓ τ Unknown e)
      ((Cast ℓ (of_shape G) Unknown) (Cast ℓ τ (of_shape G) e))
  | HN_Cast_Expand ℓ τ G e v :
    closed_ground τ = Some G →
    to_ground τ = None →
    to_val e = Some v →
    head_step_cast
      (Cast ℓ Unknown τ e)
      ((Cast ℓ (of_shape G) τ) (Cast ℓ Unknown (of_shape G) e)).

Inductive head_step : expr → expr → Prop :=
  | HN_No_Cast e e' (Hs : head_step_no_cast e e') :
    head_step e e'
  | HN_Cast e e' (Hs : head_step_cast e e') :
    head_step e e'.

(* λx.x : (? → ?) => ? => (? → ?) => ? => (? → ?) *)

(** Evaluation contexts *)
Inductive ectx_item :=
| AppLCtx (e2 : expr)
| AppRCtx (v1 : val)
| PairLCtx (e2 : expr)
| PairRCtx (v1 : val)
| FstCtx
| SndCtx
| InjLCtx
| InjRCtx
| CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
| IfCtx (e2 : expr) (e3 : expr)
| BinOpLCtx (op : bin_op) (e2 : expr)
| BinOpRCtx (op : bin_op) (v1 : val)
| SeqCtx (e2 : expr)
| CastCtx (ℓ : label) (τ1 τ2 : type).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
 match Ki with
 | AppLCtx e2 => App e e2
 | AppRCtx v1 => App (of_val v1) e
 | PairLCtx e2 => Pair e e2
 | PairRCtx v1 => Pair (of_val v1) e
 | FstCtx => Fst e
 | SndCtx => Snd e
 | InjLCtx => InjL e
 | InjRCtx => InjR e
 | CaseCtx e1 e2 => Case e e1 e2
 | IfCtx e1 e2 => If e e1 e2
 | BinOpLCtx op e2 => BinOp op e e2
 | BinOpRCtx op v1 => BinOp op (of_val v1) e
 | SeqCtx e2 => Seq e e2
 | CastCtx ℓ τ1 τ2 => Cast ℓ τ1 τ2 e
 end.

Notation ectx := (list ectx_item).

Definition fill (K : ectx) (e : expr) : expr :=
 foldr fill_item e K.

Inductive step : expr → expr → Prop :=
  | S_Normal (K : ectx) e_h e_h' (HS : head_step e_h e_h') :
    step (fill K e_h) (fill K e_h')
  | S_Error (K : ectx) (H : K ≠ []) ℓ :
    step (fill K (Error ℓ)) (Error ℓ).
