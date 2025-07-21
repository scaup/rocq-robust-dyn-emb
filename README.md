Rocq development accompanying the paper titled "Robust Dynamic Embedding for Gradual Typing".

# Hyperlinks paper

Hyperlinks in paper link the stated properties/definitions to their corresponding ones in this development.

# Top-down verification of result?

Checkout file `theories/theorems.v` for the main theorem of this paper: `robust_dyn_emb_criterion`.

# Folder Structure `theories` and most important files (bottom-up verification)

- `dyn_lang`
  + `definition.v` definition of dynamic language (fig. 2)
  + `casts.v` casts as functions (fig. 4)
- `cast_calc`definition of cast calculus with typing rules as in gradual language (S4.2)
  + `definition.v` grammar cast calculus (fig. 3)
  + `dynamics`
    * `std.v` standard dynamics (evaluation steps fig. 3)
    * `simul/equiv.v` equivalence to to alternative dynamics (S4.2.3, Prop. 1)
- `maps`
  + `dyn_embedding`
    * `definition.v` embedding dyn_lang into cast_calc (S4.3)
    * `typing.v` well-typedness of this embedding
  + `grad_into_dyn`
    * `definition.v` map defining alternative semantics for cast_calc by translating casts into dynamic functions (fig. 4, S4.2.3)
  + `linker/definitions.v` defines generalized cast operators (Notation 1, Notation 2)
- `logrel`
  + `definition.v` definition of typed-indexed logical relation/semantic typing (S5.1, fig. 5, S6.2) 
  + `lib`
    * `weakestpre.v` definition weakest precondition (S5.1, fig. 5)
    * `rfn.v` definition refinement operator (S5.1, fig. 5)
  + `lemmas` most hyperlinked lemmas/properties from paper
  + `examples`
    * `main.v` example from paper (Ex. 2)
    * `tautology.v` example from paper (Ex. 2)
    * `discussion.v` example from paper (Ex. 3)
- `prelude` bureaucracy
- `theorems.v` final theorem of paper

# Axioms?

Run `make validate`.

```
Coq.Logic.FunctionalExtensionality.functional_extensionality_dep
Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq
```

# How to compile?

## Step 1. Create compatible opam switch

Install opam; https://opam.ocaml.org/doc/Install.html
Create opam switch with correct versions of Rocq (previously coq), iris, stdpp and autosubst.

```
opam switch create dyn-emb ocaml-base-compiler
eval $(opam env --switch=dyn-emb)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.19.1 coq-iris.4.2.0 coq-stdpp.1.10.0 coq-autosubst.1.9
```

## Step 2. run “make” in the root of this directory

Run `make clean` to clean up.
