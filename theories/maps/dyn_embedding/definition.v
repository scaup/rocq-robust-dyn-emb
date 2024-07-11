From main Require Import imports.  (* prelude.autosubst. *)
From main.dyn_lang Require Import definition.  (* lib. *)
From main.grad_lang Require Import types definition typing.

(* The dynamic embedding, of the dynamic language into the gradual one. *)

Definition AscribeAn {ν : label} {Hν : NeverOccurs ν} := Ascribe ν.

Section dyn_emb.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Definition LetIn (e1 e2 : expr) : expr :=
    App (Lam e2) e1.

  Fixpoint dyn_emb (e : dyn_lang.definition.expr) : grad_lang.definition.expr :=
    match e with
    | dyn_lang.definition.Lit b =>
        AscribeAn (base_lit_type b) Unknown (Lit b)
    | dyn_lang.definition.Seq ℓ e1 e2 =>
        Seq
           (Ascribe ℓ Unknown (Base Unit) (dyn_emb e1))
           (dyn_emb e2)
    | dyn_lang.definition.If ℓ e0 e1 e2 =>
        If
           (Ascribe ℓ Unknown (Base Bool) (dyn_emb e0))
           (dyn_emb e1)
           (dyn_emb e2)
    | dyn_lang.definition.BinOp ℓ binop e1 e2 =>
        LetIn (Pair (dyn_emb e1) (dyn_emb e2)) (
          LetIn (Fst (Var 0)) (
            LetIn (Snd (Var 1)) (
                  (Ascribe ℓ (binop_res_type binop) Unknown
                      (BinOp binop
                          (Ascribe ℓ Unknown (Base Int) (Var 1))
                          (Ascribe ℓ Unknown (Base Int) (Var 0)))
                  )
               )
             )
           )
    | dyn_lang.definition.Var v =>
        Var v
    | dyn_lang.definition.Lam e =>
        AscribeAn (Bin Arrow Unknown Unknown) Unknown (Lam (dyn_emb e))
    | dyn_lang.definition.App ℓ e1 e2 =>
        App (Ascribe ℓ Unknown (Bin Arrow Unknown Unknown) (dyn_emb e1)) (dyn_emb e2)
    | dyn_lang.definition.InjL e =>
        AscribeAn (Bin Sum Unknown Unknown) Unknown (InjL $ dyn_emb e)
    | dyn_lang.definition.InjR e =>
        AscribeAn (Bin Sum Unknown Unknown) Unknown (InjR $ dyn_emb e)
    | dyn_lang.definition.Case ℓ e0 e1 e2 =>
        Case (Ascribe ℓ Unknown (Bin Sum Unknown Unknown) (dyn_emb e0)) (dyn_emb e1) (dyn_emb e2)
    | dyn_lang.definition.Fst ℓ e =>
        Fst (Ascribe ℓ Unknown (Bin Product Unknown Unknown) (dyn_emb e))
    | dyn_lang.definition.Snd ℓ e =>
        Snd (Ascribe ℓ Unknown (Bin Product Unknown Unknown) (dyn_emb e))
    | dyn_lang.definition.Pair e1 e2 =>
        AscribeAn (Bin Product Unknown Unknown) Unknown (Pair (dyn_emb e1) (dyn_emb e2))
    | dyn_lang.definition.Error ℓ => Ascribe ℓ (Base Bool) Unknown (Ascribe ℓ Unknown (Base Bool)
                                        (Ascribe ℓ (Base Unit) Unknown (Lit LitUnit)))
    end.

  (* (at level 4, e at next level). *)

End dyn_emb.

Notation "⌈⌈ e ⌉⌉" := (dyn_emb e).
