From main.prelude Require Import imports autosubst.
From main.dyn_lang Require Import definition.

Section anon.

  Context {ν : label}.

  Definition AppAn {Hν : NeverOccurs ν} (e e' : expr) :=
    App ν e e'.

End anon.

Section lib.

  Context {ν : label} {Hν : NeverOccurs ν}.

  Definition LetIn (e1 e2 : expr) : expr :=
    AppAn (Lam e2) e1.

  (* We'll always be using this with f1, f2 lambdas. *)
  Definition bimap_prod (ℓ : label) (f1 f2 : val) : val :=
    LamV (LetIn (Fst ℓ (Var 0))
            (LetIn (Snd ℓ (Var 1))
               (Pair (AppAn (of_val f1).[ren (+3)] (Var 1))
                     (AppAn (of_val f2).[ren (+3)] (Var 0))
               )
            )
      ).

  (* We'll always be using this with f1, f2 lambdas. *)
  Definition bimap_sum (ℓ : label) (f1 f2 : val) : val :=
    LamV (Case ℓ (Var 0)
               (InjL (AppAn (of_val f1).[ren (+2)] (Var 0)))
               (InjR (AppAn (of_val f2).[ren (+2)] (Var 0)))
      ).

  Definition Id : val := LamV (Var 0).

  (* We'll always be using this with f_in, f_out lambdas. *)
  Definition surround (ℓ : label) (f_in f_out : val) : val :=
    LamV (Lam (AppAn (of_val f_out).[ren (+2)] (App ℓ (Var 1) (AppAn (of_val f_in).[ren (+2)] (Var 0))))).

  Definition assert_unit (ℓ : label) : val :=
    LamV (Seq ℓ (Var 0) (Lit LitUnit)).

  Definition assert_bool (ℓ : label) : val :=
    LamV (If ℓ (Var 0) (Lit (LitBool true)) (Lit (LitBool false))).

  Definition assert_int (ℓ : label) : val :=
    LamV (BinOp ℓ PlusOp (Lit (LitInt 0)) (Var 0)).

  Definition comp (f1 f2 : val) : val :=
    LamV (AppAn (of_val f2) (AppAn (of_val f1) (Var 0))) .

  Definition of_shape (ℓ : label) (G : shape) : val :=
    match G with
    | S_Base b => match b with
                 | Unit => assert_unit ℓ
                 | Bool => assert_bool ℓ
                 | Int => assert_int ℓ
                 end
    | S_Bin bin => match bin with
                  | Arrow => surround ℓ Id Id
                  | Sum => bimap_sum ℓ Id Id
                  | Product => bimap_prod ℓ Id Id
                  end
    end.

  Definition of_shape' (ℓ : label) (G : shape) : val :=
    match G with
    | S_Base b => match b with
                 | Unit => assert_unit ℓ
                 | Bool => assert_bool ℓ
                 | Int => assert_int ℓ
                 end
    | S_Bin bin => match bin with
                  | Arrow => LamV (Lam (App ℓ (Var 1) (Var 0)))
                  | Sum => LamV (Case ℓ (Var 0)
                                  (InjL (Var 0))
                                  (InjR (Var 0)))
                  | Product => LamV (Pair (Fst ℓ (Var 0)) (Snd ℓ (Var 0)))
                  end
    end.

End lib.
