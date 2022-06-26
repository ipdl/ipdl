
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple fintype.
From mathcomp Require Import choice path bigop fintype.

(* The below file collects a number of lemms about ordinals (finitely-bounded nats) in ssreflect. *)

Lemma ltSS {a b} (H : a.+1 < b.+1) : a < b.
    done.
Defined.

Inductive ord_spec {n} : 'I_(n.+1) -> Type :=
| Ord0 i : i = @ord0 n -> ord_spec i
| OrdS i (j : 'I_n) : i = lift ord0 j -> ord_spec i.

(* The below lemmas allow us to induct up and down on the finite set [0...n]. *)

Definition ordP {n} (i : 'I_(n.+1)) : ord_spec i.
  destruct i as [x Hx].
  destruct x.
  apply Ord0.
  apply/eqP; rewrite eqE //=.
  apply (OrdS _ (Ordinal (ltSS Hx))).
  apply/eqP; rewrite eqE //=.
Defined.

Require Import Lia.

Lemma ltnS_neq_n {a b} (H : a < b.+1) (H' : a != b) : a < b.
  move/ltP: H => H.
  move/eqP: H' => h'.
  apply/ltP.
  lia.
Qed.
  
Inductive ord_spec_r {n} : 'I_(n.+1) -> Type :=
| OrdMax i : i = ord_max -> ord_spec_r i
| OrdPred i (j : 'I_n) : i = widen_ord (leqnSn n) j -> ord_spec_r i.         

Definition ordP_r {n} (i : 'I_(n.+1)) : ord_spec_r i.
  destruct i as [x Hx].
  destruct (eqVneq x n).
  subst.
  apply OrdMax.
  apply/eqP; rewrite eqE //=.
  apply (OrdPred _ (Ordinal (ltnS_neq_n Hx i))).
  apply/eqP; rewrite eqE //=.
Defined.

Lemma ord_cast_ind {n} (p2 p1 : 'I_n) (P : 'I_n -> Prop) :
  P p1 ->
  val p1 = val p2 ->
  P p2.
  intros.
  have: p1 = p2.
  apply/eqP; rewrite eqE //= H0 //=.
  intro; subst; done.
Qed.

Lemma ord_indP {n} (P : 'I_(n.+1) -> Prop) :
  P ord0 -> 
  (forall (j : 'I_n), P (widen_ord (leqnSn n) j) -> P (lift ord0 j)) ->
  (forall j, P j).
  intros.
  destruct j as [j Hj].
  induction j.
  eapply ord_cast_ind.
  apply H.
  done.
  have Hj1 : j < n by done.
  have Hj2 : j < n.+1.
  eapply leq_trans.
  apply Hj1.
  done.
  eapply (ord_cast_ind _ (lift ord0 (Ordinal Hj1))).
  apply H0.
  eapply ord_cast_ind.
  apply (IHj Hj2).
  done.
  done.
Qed.


Lemma ordP_r_max {n} (i : 'I_n.+1) : i = ord_max ->
                         exists h, 
                         ordP_r i = OrdMax _ h.
  intros; subst.
  rewrite /ordP_r.
  simpl.
  destruct (eqVneq).
  have: e = erefl by apply eq_irrelevance.
  intro; subst.

  eexists.
  rewrite /eq_rect_r //=.
  exfalso.
  rewrite eq_refl in i; done.
Qed.

Lemma ordP_r_widen {n} (i : 'I_(n.+1)) :
  i < n -> 
  exists j h,
  ordP_r i = OrdPred i j h.
  intros.
  rewrite /ordP_r.
  rewrite //=.
  destruct i as [i Hi].
  destruct eqVneq.
  subst.
  simpl in *.
  rewrite ltnn in H; done.
  eexists; eexists.
  done.
Qed.

Lemma subn_gt0_lt n m :
  n - m > 0 ->
  m < n.
  move: m; induction n; intros.
  rewrite /subn //= in H.
  intros.
  destruct m.
  done.

  have //= : m < n.
  apply IHn.
  rewrite subSS in H; done.
Qed.

Lemma ord_indP_r {n} (P : 'I_(n.+1) -> Prop) :
  P ord_max -> 
  (forall (j : 'I_n), P (lift ord0 j) -> P (widen_ord (leqnSn n) j)) ->
  (forall j, P j).
  intros.
  remember (n - j) as k; symmetry in Heqk.
  move: j Heqk.
  induction k; intros.
  have : j = ord_max.
    apply/eqP; rewrite eqE //= eqn_leq; apply/andP; split.
    destruct j; done.

    move/eqP: Heqk => Heqk.
    rewrite subn_eq0 in Heqk; done.
 intro; subst; apply H.

 have: j < n.
   apply subn_gt0_lt.
   rewrite Heqk //=.
 intros.
 move/ordP_r_widen: x.
 elim; intro.
 elim; intro.
 subst.
 intros.
 apply H0.
 apply IHk.
 simpl.
 have -> : bump 0 x = x.+1.
 rewrite /bump //=.
 rewrite subnS.
 simpl in Heqk.
 rewrite Heqk.
 done.
Qed.
