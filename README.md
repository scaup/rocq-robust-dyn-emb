# Create compatible opam switch


```
opam switch create latest-release-iris-stdpp ocaml-base-compiler
eval $(opam env --switch=latest-release-iris-stdpp)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

opam install coq.8.19.1 coq-iris.4.2.0 coq-stdpp.1.10.0 coq-autosubst

```
