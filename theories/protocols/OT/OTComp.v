
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Pars Lib.Set.
Require Import OTIdeal OTPreprocess OutOf4 TrapdoorOT HCBit.

Module OTComp (P : HCParams).
  Module M := TrapdoorOT(P).
  Import M.


Check OT_Trapdoor_Security.
  Lemma tst : OT_trapdoor =0 prot0.
    rewrite OT_Trapdoor_Security.

    Check OT14_security.


    Definition OTCompSim (leakO : chan TBool) (leakC : chan TBool) (leak_base_o : chan TBool) (leaky : chan (TBool ** TBool)) :=
      pars [:: OT_trapdoor_OTSim leakO; OTPre_Sim TBool M.i leakC leak_base_o leaky leakO ].
