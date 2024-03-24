From main Require Import imports.
From stdpp Require Import listset.

Inductive label : Set := Lbl (ℓ : Z).

Class NeverOccurs (ℓ : label) : Type.
