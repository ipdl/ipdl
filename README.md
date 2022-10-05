## Installation instructions

`IPDL` currently requires Coq `8.14.1`. Assuming `opam` is installed, perform
the following in the root directory to install Coq and required dependencies, and build IPDL:
```
opam pin add coq 8.14.1
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
opam install coq-mathcomp-algebra
opam install coq-aac-tactics
coq_makefile -f _CoqProject -o Makefile
make
```

## Overview of Respository

### IPDL definitions
Reactions and reaction equality is specified in `theories/Exp.v`. 
The core language of IPDL and exact protocol equality is given in
`theories/Core.v`. Approximate equality is given in `theories/Approx.v`.

Protocol families are defined in `theories/Big.v`, and make use of the `bigop`
notations in `ssreflect`. We pervasively make use of n-ary parallel composition,
defined using lists in `theories/Pars.v`.
Tactics for manipulating IPDL proof goals are given in `theories/Tacs.v`.

### Case studies

Proof developments for case studies studies can be found in the following files:
- Authenticated to Secure channel from CPA: 
    - Definitions for CPA security: `theories/protocols/Chan/CPA.v`
    - Case study: `theories/protocols/Chan/MultiChan.v`
- Authenticated to Secure channel from Diffie-Hellman key exchange:
    - Definitions for DDH, protocol and proof for key exchange: `theories/protocols/DHKE/DHKE.v`
    - One-time pad from Diffie-Hellman key exchange: `theories/protocols/DHKE/OTP_KE.v`
- Oblivious Transfer protocols:
    - Oblivious Transfer functionality: `theories/protocols/OT/OTIdeal.v` 
    - OT from Trapdoor permutations: `theories/protocols/OT/HCBit.v` for the
        hard-core bit predicate; `theories/protocols/OT/TrapdoorOT` for the
        protocol
    - 1-out-of-4 OT from 1-out-of-2: `theories/protocols/OT/OutOf4.v`
    - Pre-processing OT: `theories/protocols/OT/OTPreprocess.v`
- GMW MPC protocol:
    - Ideal protocol: `theories/protocols/GMW/GMWIdeal.v` 
    - Our model of boolean circuits: `theories/protocols/GMW/Circ.v` 
    - Real protocol: `theories/protocols/GMW/GMWReal.v`
    - Proofs:
      - Simplifying the real protocol: `theories/protocols/GMW/Proof/RealCleanup.v`
      - Simplifying the ideal protocol: `theories/protocols/GMW/Proof/IdealSimpl.v`
      - Definition of the simulator: `theories/protocols/GMW/Proof/SimComp.v`
      - Final proof (given as `GMWProof`): `theories/protocols/GMW/Proof/RealIdeal.v`
- Multi-party Coin Flip:
    - Auxiliary definitions for folding over channels:`theories/protocols/CoinFlip/CFold.v`
    - Real and Ideal protocols: `theories/protocols/CoinFlip/CFold.v`
    - Proofs:
        - Simplifying the real protocol: `theories/protocols/CoinFlip/Proof/CFReal.v`
        - Definition of simulator: `theories/protocols/CoinFlip/Proof/CFSimComp.v`
        - Final proof (`CoinFlip_main`): `theories/protocols/CoinFlip/Proof/CTRealIdeal.v`

### Citations for external Coq sources

We borrow `lib/Crush.v` from [CPDT](http://adam.chlipala.net/cpdt/).
We also borrow `lib/setoid_bigop.v` from the corresponding [Coq community
respository](https://github.com/coq-community/graph-theory/blob/master/theories/setoid_bigop.v).
