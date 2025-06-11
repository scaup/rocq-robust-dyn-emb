Rocq development accompanying the paper titled "Robust Dynamic Embedding for Gradual Typing".

# Hyperlinks paper

Hyperlinks in paper link the stated properties/definitions to their corresponding ones in this development.

# Top-down verification of result?

Checkout file `theories/theorems.v`; main theorem of paper `robust_dyn_emb_criterion`.

# Folder Structure theories (bottom-up verification)

## dyn_lang (S4.1)
definition of dynamic (fig. 2) language + casts as functions (fig. 4)

## cast_calc (S4.2)
definition of cast calculus with typing rules as in gradual langauge (fig 3)
### dynamics
standard dynamics (fig 3) + simulation argument with emulation map from cast_calc into dyn_lang (S4.2.3, fig. 4, Prop. 1)

## maps
### dyb_emb dynamic 
embedding dyn_lang into cast_calc (S4.3)
### grad_into_dyn
map from cast_calc into dyn_lang (alternative semantics for cast_calc by translating casts into dynamic functions) (fig. 4)
### linker
Defines generalized cast operators (Notation 1, Notation 2).
## logrel (S5.1, fig. 5)
defintion of typed-indexed logical relation
### lib (S5.1, fig. 5 )
definitions of weakestpre and rfn-operator (fig. 5)
### lemmas
most lemmas from paper, fundamental props...
### examples
Examples from paper (example 2, example 3)
## prelude
Bureaucracy.

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
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

opam install coq.8.19.1 coq-iris.4.2.0 coq-stdpp.1.10.0 coq-autosubst.1.9

```

## Step 2. run “make” in the root of this directory

Run `make clean` to clean up.