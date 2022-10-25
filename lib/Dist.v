From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path bigop finfun fintype.

(* IPDL only needs a simple, terminating model for distributions. A probability distribution is a program that depends on a finite number of coin flips. *)


Inductive Dist A :=
  | DRet : A -> Dist A
  | Flip : (bool -> Dist A) -> Dist A.

Arguments DRet [A].
Arguments Flip [A].

Fixpoint dbind {A B} (d : Dist A) (k : A -> Dist B) : Dist B :=
  match d with
    | DRet x => k x
    | Flip f =>
      Flip (fun b => dbind (f b) k)
  end.


(* Distributions are given semantics by simply counting the number of occurences of return values. *)

Fixpoint interpDist {A} (d : Dist A) : list A :=
  match d with
  | DRet y => [:: y]
  | Flip k =>
    interpDist (k false) ++ interpDist (k true) end.

Lemma interp_dbind {A B} (d : Dist A) (k : A -> Dist B) :
  interpDist (dbind d k) = flatten (map (fun x => interpDist (k x)) (interpDist d)).
    induction d; rewrite //=.
    rewrite cats0 //=.
    rewrite !H.
    rewrite map_cat //= flatten_cat //=.
Qed.


(* A distribution is uniform if every return value appears the same amount of times in the interpretation. *)
Definition uniform {A : finType} (d : Dist A) :=
  exists n,
    forall x, \sum_(j <- interpDist d) (j == x) = n.


Class unif (A : finType) :=
  {
    Unif : Dist A;
    is_unif : uniform Unif }.

Fixpoint Unif_bv (n : nat) : Dist (n.-tuple bool) :=
  match n with
    | 0%nat => DRet [tuple]
    | S n' =>
      Flip (fun x =>
              dbind (Unif_bv n') (fun t => DRet [tuple of x :: t])) end.

Lemma uniform_Unif n : uniform (Unif_bv n).
    exists 1.
    induction n.
    intro.
    simpl.
    rewrite big_cons big_nil //=.
    have -> : x = [tuple] by apply tuple0.
    done.
    intro; rewrite //= !big_cat //= !interp_dbind !big_flatten //= !big_map //=.
    under eq_bigr => m do rewrite !big_cons big_nil addn0.
    rewrite addnC.
    under eq_bigr => m do rewrite !big_cons big_nil addn0.
    destruct (tupleP x); simpl.
    under eq_bigr => m do rewrite eqE //=.
    rewrite addnC.
    under eq_bigr => m do rewrite eqE //=.
    destruct x; simpl.

    rewrite big_const_seq //=.
    rewrite iter_addn_0 mul0n //=.
    under eq_bigr => m do rewrite eqE //=.
                          rewrite IHn //=.

    rewrite big_const_seq //=.
    rewrite iter_addn_0 mul0n //=.
    under eq_bigr => m do rewrite eqE //=.
                          rewrite IHn //=.
Qed.

#[export]
Instance unif_bv (n : nat) : unif [finType of n.-tuple bool] :=
  {
  Unif := Unif_bv n;
  is_unif := (uniform_Unif n) }.

Definition uniform_bool : Dist bool := Flip (fun b => DRet b).
Lemma uniform_boolP : uniform uniform_bool.
  exists 1.
  intro.
  simpl.
  rewrite !big_cons big_nil; destruct x; rewrite //=.
Qed.
  
#[export]
Instance unif_bool : unif [finType of bool] :=
  {
  Unif := uniform_bool;
  is_unif := uniform_boolP
             }.

Definition Unif_pair X Y `{unif X} `{unif Y} : Dist (X * Y) :=
  dbind Unif (fun x => dbind Unif (fun y => DRet (x, y))).
Lemma Unif_pair_unif X Y `{unif X} `{unif Y} : 
    uniform (Unif_pair X Y).
    destruct H.
    destruct H0.
    destruct is_unif0.
    destruct is_unif1.
    exists (x * x0).
    intro.
    rewrite interp_dbind.
    rewrite big_flatten //=.
    rewrite big_map //=.
    etransitivity.
    apply eq_bigr; intros.
    rewrite interp_dbind.
    rewrite big_flatten //=.
    simpl.
    etransitivity.
    apply eq_bigr; intros.
    rewrite big_map.
    simpl.
    etransitivity.
    apply eq_bigr; intros.
    rewrite big_cons big_nil addn0 //=.
    done.
    simpl.
    destruct x1; simpl.
    etransitivity.
    apply eq_bigr; intros.
    have -> :
      \sum_(i0 <- interpDist Unif1) ((i, i0) == (s, s0)) =
      (i == s) * \sum_(i0 <- interpDist Unif1) (i0 == s0).
      rewrite big_distrr //=; apply eq_bigr; intros.
      rewrite eqE //= mulnb //=.
    rewrite e0.
    done.
    simpl.
    have -> :
      \sum_(i <- interpDist Unif0) ((i == s) * x0) =
      x0 * \sum_(i <- interpDist Unif0) ((i == s)).
      rewrite big_distrr //=; apply eq_bigr; intros.
      rewrite mulnC //=.
    rewrite e mulnC //=.
Qed.

#[export]
Instance unif_pair X Y `{unif X} `{unif Y} : unif [finType of X * Y] :=
  {|
    Unif := Unif_pair X Y;
    is_unif := Unif_pair_unif X Y
  |}.
