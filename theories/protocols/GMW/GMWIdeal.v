
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Lib.setoid_bigop Lib.Crush Ipdl.Big Pars Typ Permutation Lib.Perm.

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
  Context {chan : Type -> Type}.
  Context (I O : nat).
  Definition IdealParty_bob (i p2f : I.-tuple (chan bool)) (f2p o : O.-tuple (chan bool)) (leakTimingI : I.-tuple (chan unit)) :=
    pars [::
            copy_tup i p2f;
            Outvec leakTimingI (fun j => _ <-- Read (tnth i j);; Ret tt);
            copy_tup f2p o].

  Definition IdealParty_alice (i p2f p2advI : I.-tuple (chan bool)) (f2p o p2advO : O.-tuple (chan bool)) :=
    pars [::
            copy_tup i p2f;
            copy_tup i p2advI;
            copy_tup f2p o;
            copy_tup f2p p2advO
         ].
End IdealGMW.

Definition deliverOuts {chan : Type -> Type} {n o} (outs : circOuts n o) (w : n.-tuple (chan bool)) (out : o.-tuple (chan bool)) :=
  Outvec out (fun j => copy (tnth w (tnth outs j))).

Definition Funct {chan : Type -> Type} {A B n O : nat}
           (inA : A.-tuple (chan bool))
           (inB : B.-tuple (chan bool))
           (outA outB :  O.-tuple (chan bool))
           (c : Circ A B n)
           (outs : circOuts n O)
  :=
    wires <- newvec n @ bool ;;
    pars [::
            evalCirc inA inB c wires;
            deliverOuts outs wires outA;
            deliverOuts outs wires outB ].
            
Definition GMWIdeal {chan : Type -> Type} {A B n O : nat}
           (inA : A.-tuple (chan bool))
           (inB : B.-tuple (chan bool))
           (outA outB : O.-tuple (chan bool))
           a2advI a2advO b2advI_timing 
           (c : Circ A B n)
           (outs : circOuts n O)
  :=
  a2f <- newvec A @ bool ;;
  b2f <- newvec B @ bool ;;
  f2a <- newvec O @ bool ;;
  f2b <- newvec O @ bool ;;
  pars [::
          Funct a2f b2f f2a f2b c outs;
          IdealParty_alice A O inA a2f a2advI f2a outA a2advO;
          IdealParty_bob B O inB b2f f2b outB b2advI_timing].

Lemma GMWIdeal_t {chan : Type -> Type} {A B n O : nat} 
           (inA : A.-tuple (chan bool))
           (inB : B.-tuple (chan bool))
           (outA outB : O.-tuple (chan bool))
           a2advI a2advO b2advI_timing 
           (c : Circ A B n)
           (outs : circOuts n O) :
  ipdl_t (tags outA ++ tags outB ++ tags a2advI ++ tags a2advO ++ tags b2advI_timing) (GMWIdeal inA inB outA outB a2advI a2advO b2advI_timing c outs).
  rewrite /GMWIdeal /Funct /evalCirc /deliverOuts /IdealParty_alice /IdealParty_bob /copy_tup.
  repeat type_tac. 
  rewrite !catA.
  cat_perm_tac.
  setoid_rewrite (SeqOps.Perm_swap 0 1) at 1; rewrite /SeqOps.swap //= /SeqOps.lset //=.
  apply perm_skip.
  apply perm_skip.
  setoid_rewrite (SeqOps.Perm_swap 0 1) at 1; rewrite /SeqOps.swap //= /SeqOps.lset //=.
  apply perm_skip.
  setoid_rewrite (SeqOps.Perm_swap 0 3) at 1; rewrite /SeqOps.swap //= /SeqOps.lset //=.
  apply perm_skip.
  apply perm_skip.
  setoid_rewrite (SeqOps.Perm_swap 0 2) at 1; rewrite /SeqOps.swap //= /SeqOps.lset //=.
  apply perm_skip.
  apply perm_skip.
  setoid_rewrite (SeqOps.Perm_swap 0 1) at 1; rewrite /SeqOps.swap //= /SeqOps.lset //=.
Qed.
