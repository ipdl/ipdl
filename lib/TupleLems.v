From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path bigop finfun fintype matrix div ssralg.

(* Various lemmas around tuples (static length lists) in ssreflect *)

Program Definition tsplit_def {n} (x : (n.*2).-tuple bool) : n.-tuple bool * n.-tuple bool :=
  ([tuple of take n x], [tuple of drop n x]).
Next Obligation.
  apply/minn_idPl.
  clear x.
  induction n.
  done.
  eapply leq_trans.
  instantiate (1 := n.+1).
  done.
  rewrite doubleS.
  rewrite ltnS.
  eapply leq_trans.
  apply IHn.
  done.
Defined.
Next Obligation.
  rewrite -addnn.
  rewrite -addnBA.
  rewrite subnn addn0 //=.
  done.
Defined.

Program Definition tjoin_def {n} (p : (n.-tuple bool) * (n.-tuple bool)) : (n.*2).-tuple bool :=
  [tuple of fst p ++ snd p].
Next Obligation.
  rewrite addnn //=.
Defined.

Definition tsplit {n} := locked (@tsplit_def n).
Definition tjoin {n} := locked (@tjoin_def n).


Lemma tsplitK n : cancel (@tsplit n) tjoin.
  unlock tjoin tsplit.
  move => x.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
  rewrite /tsplit_def //=.
  rewrite /tjoin_def //=.
  rewrite /eq_rect /eq_ind_r /eq_ind //=.
  destruct (addnn n); simpl.
  move: x.
  destruct (tsplit_def_obligation_1 n).
  destruct (tsplit_def_obligation_2 n).
  simpl; intro.
  have -> : n.*2 - n = n.
  rewrite -addnn -addnBA.
  rewrite subnn addn0 //=.
  done.
  rewrite cat_take_drop //=.
Qed.

Lemma tjoinK n : cancel (@tjoin n) tsplit.
  unlock tjoin tsplit.
  move => x.
  apply/eqP; rewrite /eq_op //= /eq_op //=; apply/eqP.
  rewrite /tsplit_def //=.
  rewrite /tjoin_def //=.
  rewrite /eq_rect.
  move: x.
  destruct (tsplit_def_obligation_1 n).
  destruct (tsplit_def_obligation_2 n).
  simpl; intro.
  destruct (tjoin_def_obligation_1 n x).
  simpl.
  apply/eqP; simpl.
  have -> : n + n - n = n.
  rewrite -addnBA.
  rewrite subnn addn0 //=.
  done.
  rewrite take_size_cat.
  rewrite drop_size_cat.
  rewrite !eq_refl //=.
  rewrite size_tuple //=.
  rewrite size_tuple //=.
Qed.



Definition select4 {A} (x : A * A * A * A) (sel : 2.-tuple bool) :=
  match tnth sel (inord 0), tnth sel (inord 1) with
    | false, false => x.1.1.1
    | false, true => x.1.1.2
    | true, false => x.1.2                     
    | true, true => x.2 end.

Definition xort {n : nat} (x y : n.-tuple bool) : n.-tuple bool :=
  [tuple of map (fun p => addb p.1 p.2) (zip x y)].

Infix "+t" := xort (at level 80).

Definition andt {n} (x y : n.-tuple bool) :=
  [tuple of [seq p.1 && p.2 | p <- zip x y]].

Infix "&t" := andt (at level 80).

Definition negt {n} (x : n.-tuple bool) :=
  [tuple of map negb x].

Notation "~t" := (negt).

Definition tzero (n : nat) : n.-tuple bool := [tuple of nseq n false].
Definition tone (n : nat) : n.-tuple bool := [tuple of nseq n true].

Lemma tnth_zip {n : nat} (x y : n.-tuple bool) i :
  tnth [tuple of zip x y] i = (tnth x i, tnth y i).
  rewrite (tnth_nth (false, false)).
  rewrite //=.
  rewrite nth_zip.
  rewrite -!tnth_nth //=.
  rewrite !size_tuple //=.
Qed.

Lemma xortK {n : nat} (x : n.-tuple bool) :
  xort x x = tzero n.
  apply/eqP; rewrite eqEtuple; apply/forallP => i.
  rewrite /xort.
  rewrite tnth_map.
  rewrite tnth_zip //=.
  rewrite addbb //=.
  rewrite /tzero tnth_nseq //=.
Qed.

Lemma xortC {n : nat} (x y : n.-tuple bool) :
  xort x y = xort y x.
  apply/eqP; rewrite eqE //=.
  induction n.
  rewrite (tuple0 x) (tuple0 y); done.
  rewrite (tuple_eta x) (tuple_eta y) //=.
  rewrite addbC.
  apply/eqP.
  congr (_ :: _).
  move: (IHn [tuple of behead x] [tuple of behead y]).
  simpl.
  move/eqP; done.
Qed.

Lemma xortA {n : nat} (x y z : n.-tuple bool) :
  xort (xort x y) z = xort x (xort y z).
  apply/eqP; rewrite eqE //=.
  induction n.
  rewrite (tuple0 x) (tuple0 y) (tuple0 z) //=.
  rewrite (tuple_eta x) (tuple_eta y) (tuple_eta z) //=.
  rewrite addbA; apply/eqP; congr(_ :: _).
  rewrite (eqP (IHn [tuple of behead x] [tuple of behead y] [tuple of behead z])) //=.
Qed.

Lemma andtC {n : nat} (x y : n.-tuple bool) :
  andt x y = andt y x.
  apply/eqP; rewrite eqE //=.
  induction n.
  rewrite (tuple0 x) (tuple0 y); done.
  rewrite (tuple_eta x) (tuple_eta y) //=.
  rewrite andbC.
  apply/eqP.
  congr (_ :: _).
  move: (IHn [tuple of behead x] [tuple of behead y]).
  simpl.
  move/eqP; done.
Qed.

Lemma andtA {n : nat} (x y z : n.-tuple bool) :
  andt (andt x y) z = andt x (andt y z).
  apply/eqP; rewrite eqE //=.
  induction n.
  rewrite (tuple0 x) (tuple0 y) (tuple0 z) //=.
  rewrite (tuple_eta x) (tuple_eta y) (tuple_eta z) //=.
  rewrite andbA; apply/eqP; congr(_ :: _).
  rewrite (eqP (IHn [tuple of behead x] [tuple of behead y] [tuple of behead z])) //=.
Qed.

Lemma xort_andt {n} (x y z : n.-tuple bool) :
  ((x +t y) &t z) = ((x &t z) +t (y &t z)).
  apply/eqP; rewrite eqE //=.
  induction n.
  rewrite (tuple0 x) (tuple0 y) (tuple0 z) //=.
  rewrite (tuple_eta x) (tuple_eta y) (tuple_eta z) //=.
  rewrite andb_addl; apply/eqP; congr (_ :: _).
  rewrite (eqP (IHn [tuple of behead x] [tuple of behead y] [tuple of behead z])) //=.
Qed.

Lemma xort_andt_xort {n} (x y z w : n.-tuple bool) :
  ((x +t y) &t (z +t w)) = ((x &t z) +t (y &t z) +t (x &t w) +t (y &t w)).
  rewrite xort_andt.
  rewrite (andtC x) xort_andt.
  rewrite (andtC y) xort_andt.
  rewrite (andtC z).
  rewrite !xortA.
  congr (xort _ _).
  rewrite -!xortA.
  congr (xort _ _); last by apply andtC.
  rewrite xortC.
  rewrite (andtC z).
  rewrite (andtC w).
  done.
Qed.

Lemma xort0 {n} (x : n.-tuple bool) : 
  xort x (tzero n) = x.
  apply/eqP; rewrite eqE //=.
  induction n.
  rewrite (tuple0 x) //=.
  rewrite (tuple_eta x) //=.
  rewrite addbF.
  rewrite (eqP (IHn [tuple of behead x])) //=.
Qed.

  Lemma xort_inj_l {n} (x : n.-tuple bool) :
    injective (xort x).
    move => a b.
    intro.
    apply/eqP; rewrite eqE //=.
    move/eqP: H => H; rewrite eqE //= in H.
    induction n.
    rewrite (tuple0 a) (tuple0 b); done .
    rewrite (tuple_eta a) (tuple_eta b) //=.
    rewrite (tuple_eta a) (tuple_eta b) (tuple_eta x) //= in H.
    have -> : thead a = thead b.
    rewrite eqE //= in H; destruct (andP H).
    eapply addbI.
    apply (eqP H0).
    move/eqP: H => H.
    inversion H.
    suff : behead a == behead b.
    intros.
    rewrite eqE //= (eqP x0).
    rewrite //= eqseqE !eq_refl //=.
    suff : [tuple of behead a] == [tuple of behead b].
    rewrite eqE //=.
    eapply IHn.
    simpl.
    apply/eqP.
    apply H2.
  Qed.

  Lemma xort_inj_r {n} (x : n.-tuple bool) :
    injective (fun a => xort a x).
    move => a b.
    rewrite (xortC a) (xortC b).
    move/xort_inj_l; done.
  Qed.

Lemma thead_xort {n} (x y : n.+1.-tuple bool) :
  thead (xort x y) = (thead x) (+) (thead y).
  rewrite (tuple_eta x) (tuple_eta y) //=.
Qed.

Definition tnot {n} (x : n.-tuple bool) :=
  [tuple of map negb x].

Lemma thead_tnot {n} (x : n.+1.-tuple bool) :
  thead (tnot x) = ~~ (thead x).
    rewrite (tuple_eta x) //=.
Qed.

Lemma tsplitE1 {L} (m : (L.*2).-tuple bool) :
    (eq_rect (minn L L.*2) (tuple_of^~ bool) [tuple of 
                take L m] L (TupleLems.tsplit_def_obligation_1 L))
      = (tsplit m).1.
  unlock tsplit.
  rewrite //=.
Qed.

Lemma tsplitE2 {L} (m : (L.*2).-tuple bool) :
    (eq_rect (L.*2 - L) (tuple_of^~ bool) [tuple of 
                drop L m] L (TupleLems.tsplit_def_obligation_2 L))
      = (tsplit m).2.
  unlock tsplit; rewrite //=.
Qed.

Lemma tsplitE {L} (m : (L.*2).-tuple bool) :
  tsplit m = ((tsplit m).1, (tsplit m).2).
  destruct (tsplit m); done.
Qed.

Lemma leq_n_double n :
  n <= n.*2.
  rewrite -mul2n.
  rewrite leq_pmull //=.
Qed.

Lemma tsplit_nseq {L} b :
  tsplit [tuple of nseq L.*2 b] = ([tuple of nseq L b], [tuple of nseq L b]).
  rewrite tsplitE.
  apply/eqP; rewrite eqE //= eqE //=.
  rewrite -tsplitE1 //=.
  rewrite -tsplitE2 //=.
  apply/andP; split.
  destruct (tsplit_def_obligation_1 L); rewrite //=.
  rewrite take_nseq.
  have {1}-> //= : L = minn L L.*2.
  rewrite tsplit_def_obligation_1 //=.
  apply leq_n_double.
  destruct (tsplit_def_obligation_2 L); rewrite //=.
  rewrite eqE //=.
  rewrite drop_nseq //=.
Qed.

Lemma thead_nseq {n} {A} (b : A) : thead [tuple of nseq (n.+1) b] = b.
  rewrite (tuple_eta [tuple of nseq n.+1 b]) //=.
Qed.

Definition osplit {m n : nat} (x : 'I_(n * m)) :=
  (enum_val \o cast_ord (esym (mxvec_cast n m))) x.

Definition ojoin {n m} (x : 'I_n) (y : 'I_m) : 'I_(n * m) := mxvec_index x y.

Lemma ojoinK {m n : nat} (x : 'I_(n * m)) :
  ojoin (osplit x).1 (osplit x).2 = x.
    rewrite /ojoin /osplit.
    case/mxvec_indexP: x => i j /=.
    rewrite cast_ordK enum_rankK //=.
Qed.

Lemma osplitK {m n : nat} (x : 'I_n) (y : 'I_m) :
  osplit (ojoin x y) = (x, y).
  rewrite /ojoin /osplit.
  destruct x as [x Hx].
  destruct y as [y Hy].
  rewrite //=.
  rewrite cast_ordK enum_rankK //=.
Qed.


Definition tuple_of_matrix {n m} {A} (M : 'M[A]_(n, m)) : (n * m).-tuple A :=
  mktuple (fun i => M (osplit i).1 (osplit i).2).


Definition matrix_of_tuple {n m} {A} (t : (n * m).-tuple A) : 'M[A]_(n, m) :=
  \matrix_(i < n, j < m) (tnth t (ojoin i j)).

Lemma tuple_matrixK n m A :
  cancel (@tuple_of_matrix n m A) (@matrix_of_tuple n m A).
  move => M.
  apply/matrixP => i j.
  rewrite /tuple_of_matrix /matrix_of_tuple.
  rewrite mxE.
  rewrite !tnth_mktuple.
  rewrite osplitK //=.
Qed.

Lemma matrix_tupleK n m A :
  cancel (@matrix_of_tuple n m A) (@tuple_of_matrix n m A).
  move => t.
  apply/eq_from_tnth => i.
  rewrite /tuple_of_matrix.
  rewrite !tnth_mktuple.
  rewrite /matrix_of_tuple.
  rewrite mxE.
  rewrite ojoinK //=.
Qed.

Definition ttranspose {A} {m n} (t : (m * n).-tuple A) : (n * m).-tuple A :=
  tcast (mulnC _ _) t.

Definition texpand {A} {m} (t : m.-tuple A) : m.-tuple (1.-tuple A) :=
  [tuple of map (fun x => [tuple x]) t].

Lemma theadE' {n} {A} (xs : (n.+1).-tuple A) y (ys : seq A) :
  tval xs = y :: ys ->
  thead xs = y.
  intros.
  destruct xs; simpl in *.
  subst.
  rewrite //=.
Qed. 

Ltac simp_tuple :=
  match goal with
    | [ |- context[thead _] ] => erewrite theadE'; last by done
  end.

Definition tflatten {n} {m} {A} (x : n.-tuple (m.-tuple A)) : (n * m).-tuple A :=
  tuple_of_matrix (\matrix_(i < n, j < m) tnth (tnth x i) j).

Definition tunflatten {n} {m} {A} (x : (n * m).-tuple A) : n.-tuple (m.-tuple A) :=
  mktuple (fun i =>
             mktuple (fun j =>
                        matrix_of_tuple x i j )).

Lemma tflattenK n m A :
  cancel (@tflatten n m A) (@tunflatten n m A).
  move => t; rewrite /tflatten /tunflatten.
  rewrite tuple_matrixK //=.
  apply eq_from_tnth => i; apply eq_from_tnth => j.
  rewrite //=.
  rewrite !tnth_mktuple mxE //=.
Qed.

Lemma tunflattenK n m A :
  cancel (@tunflatten n m A) (@tflatten n m A).
  move => t; rewrite /tflatten /tunflatten.
  erewrite eq_mx; last first.
  move => i j.
  rewrite !tnth_mktuple mxE //=.
  rewrite /tuple_of_matrix.
  apply eq_from_tnth => i.
  rewrite tnth_mktuple mxE.
  rewrite ojoinK //=.
Qed.

Definition tuple_of_rv {n} {A} (r : 'rV[A]_n) : n.-tuple A :=
  mktuple (fun i => r ord0 i).

Definition rv_of_tuple {n} {A} (r : n.-tuple A) : 'rV[A]_n :=
  \row_i (tnth r i).

Lemma tuple_rvK {n} {A} :
  cancel (@tuple_of_rv n A) (@rv_of_tuple n A).
  move => t; rewrite /rv_of_tuple /tuple_of_rv.
  apply rowP => i.
  rewrite mxE tnth_mktuple //=.
Qed.

Lemma rv_tupleK {n} {A} :
  cancel  (@rv_of_tuple n A) (@tuple_of_rv n A).
  move => t; rewrite /rv_of_tuple /tuple_of_rv.
  apply eq_from_tnth => i.
  rewrite tnth_mktuple.
  rewrite !mxE //=.
Qed.

Definition tuple_of_cv {n} {A} (r : 'cV[A]_n) : n.-tuple A :=
  mktuple (fun i => r i ord0).

Definition cv_of_tuple {n} {A} (r : n.-tuple A) : 'cV[A]_n :=
  \col_i (tnth r i).

Lemma tuple_cvK {n} {A} :
  cancel (@tuple_of_cv n A) (@cv_of_tuple n A).
  move => t; rewrite /cv_of_tuple /tuple_of_cv.
  apply colP => i.
  rewrite mxE tnth_mktuple //=.
Qed.

Lemma cv_tupleK {n} {A} :
  cancel  (@cv_of_tuple n A) (@tuple_of_cv n A).
  move => t; rewrite /cv_of_tuple /tuple_of_cv.
  apply eq_from_tnth => i.
  rewrite tnth_mktuple.
  rewrite !mxE //=.
Qed.


Definition tsplit4 {n} (x : n.*2.*2.-tuple bool) : n.-tuple bool * n.-tuple bool * n.-tuple bool * n.-tuple bool :=
  let p := tsplit x in
  let p1 := tsplit p.1 in
  let p2 := tsplit p.2 in
  (p1.1, p1.2, p2.1, p2.2).

Definition tjoin4 {n} (x : n.-tuple bool * n.-tuple bool * n.-tuple bool * n.-tuple bool) :
n.*2.*2.-tuple bool.
  set p := tjoin (x.1.1.1, x.1.1.2).
  set p2 := tjoin (x.1.2, x.2).
  exact (tjoin (p, p2)).
Defined.

Lemma tsplit4K {n} : cancel (@tsplit4 n) (@tjoin4 n).
  move => x.
  rewrite /tsplit4 //=.
  rewrite /tjoin4 //=.
 rewrite -tsplitE tsplitK.
 rewrite -tsplitE tsplitK.
 rewrite -tsplitE tsplitK.
 done.
Qed.

Lemma tjoin4K {n} : cancel (@tjoin4 n) (@tsplit4 n).
  move => x.
  rewrite /tsplit4 /tjoin4 //=.
  rewrite !tjoinK.
  destruct x as [[[a b] c] d].
  done.
Qed.


Definition thead1 {A} {n} (x : (S (S n)).-tuple A) : A :=
  thead [tuple of behead x].

Lemma eq_tuple {A} {n} (x y : n.-tuple A) :
  (tval x) = (tval y) ->
  x = y.
  destruct x, y; simpl in *.
  intro; subst.
  have: i = i0 by apply bool_irrelevance.
  intro; subst.
  done.
Qed.

Lemma tuple1P (x : 1.-tuple bool) :
  exists y, 
  x = [tuple y].
  destruct x.
  destruct tval.
  done.
  destruct tval.
  simpl in *.
  exists b.
  apply eq_tuple; simpl; done.
  done.
Qed.

Notation "n .-bv" := (n.-tuple bool)
  (at level 2, format "n .-bv") : type_scope.

