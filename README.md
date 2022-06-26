## Installation instructions

`IPDL` requires the Coq proof assistant, and the `mathcomp` libraries. IPDL is compatible with
the current Coq distribution (as of 12/16/2021), `8.14.1`. 
We recommend installing Coq via [opam](https://coq.inria.fr/opam-using.html).
The `mathcomp` libraries can be installed via opam:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
opam install coq-mathcomp-algebra
```

Once the above libraries are installed,
simply type `make` to compile the IPDL library and examples.