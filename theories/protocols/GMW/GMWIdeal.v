
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Lib.setoid_bigop Lib.Crush Ipdl.Big Pars.

Require Import Circ.

Record party := { party_val :> bool }.
Canonical party_sub := Eval hnf in [newType for party_val].
Canonical party_eq_mix := Eval hnf in [eqMixin of party by <:].
Canonical party_eq := EqType party party_eq_mix.

Definition alice : party := {| party_val := false |}.
Definition bob : party := {| party_val := true |}.
Definition other : party -> party :=
  fun p =>
    {| party_val := ~~ p.(party_val) |}.


Section IdealGMW.
  Context (I O : nat).
  Definition IdealParty_bob (i p2f : I.-tuple (chan TBool)) (f2p o : O.-tuple (chan TBool)) (leakTimingI : I.-tuple (chan TUnit)) :=
    pars [::
            copy_tup i p2f;
            Outvec leakTimingI (fun j => _ <-- Read (tnth i j);; Ret vtt);
            copy_tup f2p o].

  Definition IdealParty_alice (i p2f p2advI : I.-tuple (chan TBool)) (f2p o p2advO : O.-tuple (chan TBool)) :=
    pars [::
            copy_tup i p2f;
            copy_tup i p2advI;
            copy_tup f2p o;
            copy_tup f2p p2advO
         ].
End IdealGMW.

Definition deliverOuts {n o} (outs : circOuts n o) (w : n.-tuple (chan TBool)) (out : o.-tuple (chan TBool)) :=
  Outvec out (fun j => copy (tnth w (tnth outs j))).

Check evalCirc.

Definition Funct {A B n O : nat}
           (inA : A.-tuple (chan TBool))
           (inB : B.-tuple (chan TBool))
           (outA outB :  O.-tuple (chan TBool))
           (c : Circ A B n)
           (outs : circOuts n O)
  :=
    wires <- newvec n @ TBool ;;
    pars [::
            evalCirc inA inB c wires;
            deliverOuts outs wires outA;
            deliverOuts outs wires outB ].
            
Definition GMWIdeal {A B n O : nat}
           (inA : A.-tuple (chan TBool))
           (inB : B.-tuple (chan TBool))
           (outA outB : O.-tuple (chan TBool))
           a2advI a2advO b2advI_timing 
           (c : Circ A B n)
           (outs : circOuts n O)
  :=
  a2f <- newvec A @ TBool ;;
  b2f <- newvec B @ TBool ;;
  f2a <- newvec O @ TBool ;;
  f2b <- newvec O @ TBool ;;
  pars [::
          Funct a2f b2f f2a f2b c outs;
          IdealParty_alice A O inA a2f a2advI f2a outA a2advO;
          IdealParty_bob B O inB b2f f2b outB b2advI_timing].


