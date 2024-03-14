# Create compatible opam switch

latest stdpp requires coq < 8.19, so we'll be using 8.18

```
opam switch create latest-release-iris-stdpp ocaml-base-compiler
eval $(opam env --switch=latest-release-iris-stdpp)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

opam install coq.8.18.0 coq-iris.4.1.0 coq-stdpp.1.9.0 coq-iris-heap-lang.4.1.0 coq-autosubst.1.8
```
