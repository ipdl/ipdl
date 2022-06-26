(* Oblivious transfer in IPDL. *)


Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Base Ipdl.Big Pars Lib.Set Typ.

(* Oblivious transfer is parametrized by the type of messages.  The ideal protocol reads a tuple from channel 'm' (coming from the sender), reads a boolean from channel 'i' (coming from the receiver), and outputs the i'th element of m (back to the receiver. *)
Definition OTIdeal {chan : Type -> Type} (L : Type) (i : chan bool) (m : chan (L * L)%type)
           (o : chan L) :=
  o ::= (
        x_i <-- Read i ;;
        x_m <-- Read m ;;
        Ret (if x_i then x_m.2 else x_m.1)).

(* We additionally consider the 1-out-of-4 variant. *)
Definition OT14Ideal {chan : Type -> Type} L (i : chan (bool * bool)%type)
           (m : chan ((L * L) * (L * L))%type)
           (o : chan L) :=
  Out o (
        x <-- Read i ;;
        y <-- Read m ;;
        Ret (((y # x.1) # x.2))).

(* The following is a combinator that spawns a 1-out-of-4 OT protocol, to be used in P. *)
Definition withOT14 {chan : Type -> Type} L (P : chan (bool * bool)%type * chan ((L * L) * (L * L))%type * chan L -> ipdl) :=
  i <- new (bool * bool) ;;
  m <- new ((L * L) * (L * L)) ;;
  o <- new L ;;
  pars [:: OT14Ideal _ i m o; P (i, m, o) ].

Lemma withOT14_irrel {chan} L r :
  @withOT14 chan L (fun '(i, m, o) => pars [:: i ::= Read i; m ::= Read m; r]) =p r.
  rewrite /withOT14.
  swap_tac 0 1.
  setoid_rewrite pars_pars; simpl.
  rewrite /OT14Ideal.
  swap_tac 0 3.
  setoid_rewrite new_pars_remove.
  setoid_rewrite new_pars_remove.
  swap_tac 0 1.
  rewrite new_pars_remove.
  rewrite pars1 //=.
Qed.

Instance withOT14_NewLike chan L : NewLike chan (withOT14 L).
   constructor.
   intros.
   rewrite /withOT14.
   repeat setoid_rewrite newComp.
   Intro => i.
   Intro => m.
   Intro => o.
   rewrite pars_rcons //=.
   symmetry; swap_tac 0 1.
   rewrite par_in_pars //=.
   align.
   intros.
   rewrite /withOT14.
   Intro => i.
   Intro => m.
   Intro => o.
   rewrite H.
   done.
   intros.
   rewrite /withOT14.
   symmetry.
   rewrite EqNewExch.
   Intro => i.
   rewrite EqNewExch.
   Intro => m.
   rewrite EqNewExch.
   Intro => o.
   symmetry.
   swap_tac 0 1.
   rewrite newPars.
   Intro => c.
   swap_tac 0 1; done.
Qed.

Require Import Lib.SeqOps.

Lemma OTIdeal_t {chan} L i (m : chan (L * L)%type) o :
  ipdl_t [:: tag o] (OTIdeal L i m o).
  rewrite /OTIdeal.
  repeat type_tac.
Qed.


Lemma withOT14_t {chan} L P o :
  (forall x y z, @ipdl_t chan [:: tag x, tag y & o] (P (x, y, z))) ->
  ipdl_t o (withOT14 L P).
  rewrite /withOT14; intros.
  apply new_t => i.
  apply new_t => m.
  apply new_t => v.
  rewrite /OT14Ideal.
  repeat type_tac.
  setoid_rewrite (Perm_swap 1 2) at 1; rewrite /swap //= /lset //= !insert_0 //=.
Qed.
