From main Require Import imports.

From main.dyn_lang Require Import definition.
From main.surf_lang Require Import types definition.

(* The dynamic embedding, of the dynamic language into the gradual one. *)

Definition AssertAn {ν : label} {Hν : NeverOccurs ν} := Assert ν.

Section dyn_emb.

  Context {ν : label} {Hν : NeverOccurs ν}.

  
  Fixpoint dyn_emb (e : dyn_lang.definition.expr) : surf_lang.definition.expr :=
    match e with
    | dyn_lang.definition.Lit b =>
        AssertAn (base_lit_type b) Unknown (Lit b)
    | dyn_lang.definition.Seq ℓ e1 e2 =>
        Seq
           (Assert ℓ Unknown (Base Unit) (dyn_emb e1))
           (dyn_emb e2)
    | dyn_lang.definition.If ℓ e0 e1 e2 =>
        If
           (Assert ℓ Unknown (Base Bool) (dyn_emb e0))
           (dyn_emb e1)
           (dyn_emb e2)
    | dyn_lang.definition.BinOp ℓ binop e1 e2 =>
        BinOp binop
           (Assert ℓ Unknown (Base Int) (dyn_emb e1))
           (Assert ℓ Unknown (Base Int) (dyn_emb e2))
    | dyn_lang.definition.Var v =>
        Var v
    | dyn_lang.definition.Lam e =>
        AssertAn (Bin Arrow Unknown Unknown) Unknown (Lam (dyn_emb e))
    | dyn_lang.definition.App ℓ e1 e2 =>
        App (Assert ℓ Unknown (Bin Arrow Unknown Unknown) (dyn_emb e1)) (dyn_emb e2)
    | dyn_lang.definition.InjL e =>
        AssertAn (Bin Sum Unknown Unknown) Unknown (InjL $ dyn_emb e)
    | dyn_lang.definition.InjR e =>
        AssertAn (Bin Sum Unknown Unknown) Unknown (InjR $ dyn_emb e)
    | dyn_lang.definition.Case ℓ e0 e1 e2 =>
        Case (Assert ℓ Unknown (Bin Sum Unknown Unknown) (dyn_emb e0)) (dyn_emb e1) (dyn_emb e2)
    | dyn_lang.definition.Fst ℓ e =>
        Fst (Assert ℓ Unknown (Bin Product Unknown Unknown) (dyn_emb e))
    | dyn_lang.definition.Snd ℓ e =>
        Snd (Assert ℓ Unknown (Bin Product Unknown Unknown) (dyn_emb e))
    | dyn_lang.definition.Pair e1 e2 =>
        AssertAn (Bin Product Unknown Unknown) Unknown (Pair (dyn_emb e1) (dyn_emb e2))
    | dyn_lang.definition.Error ℓ => Error ℓ
    end.

  (* (at level 4, e at next level). *)

End dyn_emb.

Notation "⌜⌜ e ⌝⌝" := (dyn_emb e).
