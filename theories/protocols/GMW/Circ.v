
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun finfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Big Lib.OrdLems.

(*
  
  1 := in 5
  2 := 1 + 1
  3 := not 2
  end
*)


Program Definition tuple_trunc {n: nat} {A} (t : n.-tuple A) (j : 'I_n) : j.-tuple A := [tuple of take j t]. 
Next Obligation.
  apply/minn_idPl.
  destruct j; simpl.
  apply ltnW; done.
Qed.

Lemma tuple_truncE {n} {A} (t : n.-tuple A) (j : 'I_n) :
  val (tuple_trunc t j) = take j t.
  unfold tuple_trunc.
  destruct (tuple_trunc_obligation_1 n j).
  simpl.
  have -> : minn j n = j.
  apply/minn_idPl.
  destruct j; simpl.
  apply ltnW; done.
  done.
Qed.

Lemma leq_ord' {n} (i : 'I_n) : i <= n.
  destruct n.
  destruct i; done.
  eapply leq_trans.
  apply leq_ord.
  apply leqnSn.
Qed.

Lemma tnth_tuple_trunc {n} {A} (j : 'I_n) (t : n.-tuple A) (x : 'I_j) :
  tnth (tuple_trunc t j) x = tnth t (widen_ord (leq_ord' j) x).
  destruct n.
  destruct j; done.
  destruct (tupleP t).
  rewrite !(tnth_nth x0).
  rewrite tuple_truncE.
  simpl.
  rewrite nth_take.
  done.
  destruct x; done.
Qed.

Section CircDef.
  Context (A B : nat).

Inductive Op n :=
  | InA : 'I_A -> Op n
  | InB : 'I_B -> Op n
  | And : 'I_n -> 'I_n -> Op n
  | Xor : 'I_n -> 'I_n -> Op n
  | Not : 'I_n -> Op n.

Definition Circ n := forall (x : 'I_n), Op x.

Definition circOuts n o := o.-tuple ('I_n).

End CircDef.

Definition circ0 {A B} : Circ A B 0.
  intro.
  destruct x.
  done.
Defined.

Definition extend_circ {A B n} (c : Circ A B n) (o : Op A B n) : Circ A B n.+1. 
  intro x.
  destruct (ordP_r x).
  subst.
  apply o.
  subst.
  simpl in *.
  apply c.
Defined.

Definition pred_circ {A B n} (c : Circ A B n.+1) : Circ A B n. 
  intro j.
  apply (c (widen_ord (leqnSn n) j)).
Defined.

Lemma Circ_ind_r {A B} (P : forall n, Circ A B n -> Prop) :
  P _ circ0 ->
  (forall n c o, P n c -> P n.+1 (extend_circ c o)) ->
  forall n c, P n c.
  intros.
  induction n.
  have -> : c = circ0.
  funext => i.
  destruct i; done.
  done.
  have -> : c = extend_circ (pred_circ c) (c ord_max).
  funext => i.
  rewrite /extend_circ.
  destruct (ordP_r i).
  subst; rewrite /eq_rect_r //=.
  subst; rewrite /eq_rect_r //=.
  apply H0.
  apply IHn.
Qed.



Arguments InA {A B n}.
Arguments InB {A B n}.
Arguments And {A B n}.
Arguments Xor {A B n}.
Arguments Not {A B n}.

Definition evalOp {A B n : nat} (inA : A.-tuple (chan TBool)) (inB : B.-tuple (chan TBool)) (w : n.-tuple (chan TBool)) (op : Op A B n) : rxn TBool :=
        match op with
            | InA j => copy (tnth inA j)
            | InB j => copy (tnth inB j)
            | And x y => x <-- Read (tnth w x) ;; y <-- Read (tnth w y) ;; Ret (x && y : TBool)
            | Xor x y => x <-- Read (tnth w x) ;; y <-- Read (tnth w y) ;; Ret (x (+) y : TBool)
            | Not x => x <-- Read (tnth w x) ;; Ret (~~ x : TBool) end.

Definition evalCirc {A B n : nat} (inA : A.-tuple (chan TBool)) (inB : B.-tuple (chan TBool)) (c : Circ A B n) (w : n.-tuple (chan TBool)) :=
  Outvec w (fun j =>
              evalOp inA inB (tuple_trunc w j) (c j)
           ).


(*
Definition evalOp {A B} {n} (inA : A.-tuple bool) (inB : B.-tuple bool) (wires : n.-tuple bool) (op : Op A B n) :=
  match op with
    | InA a => tnth inA a
    | InB b => tnth inB b
    | And x y => (tnth wires x) && (tnth wires y)
    | Xor x y => (tnth wires x) (+) (tnth wires y)
    | Not x => ~~ (tnth wires x)
                  end.

Print Circ.

Fixpoint evalCirc {A B} {n} (inA : A.-tuple bool) (inB : B.-tuple bool) (circ : Circ A B n) : n.-tuple bool.
  destruct circ.
  simpl in *.
  set w := evalCirc _ _ _ inA inB circ.
  apply [tuple of rcons w (evalOp inA inB w o)].
  apply [tuple].
Defined.

Definition succ_ord {n} (x : 'I_n) : 'I_(n.+1) :=
  (widen_ord (leqnSn _) x).

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).



Inductive Circ : nat -> Type :=
  | CLet n : Circ n -> Op n -> Circ n.+1
  | CBegin : Circ 0.


Arguments CLet [A B n o].
Arguments CBegin {A B}.

Notation "c ;;; o" := (CLet c o) (at level 43, left associativity).
Notation cbegin := CBegin.

*)
