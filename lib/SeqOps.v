

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
Require Import Permutation Lib.Perm.

(* Various lemmas and tactics around sequences. 
  n-ary composition in IPDL is done using sequences, so 
  we need random access and swapping combinators. *)

Fixpoint rot_rcons {A} (n : nat) (xs : list A) :=
  match n, xs with
    | 0, _ => xs
    | S n, (x :: xs) => rot_rcons n (rcons xs x)
    | _, _ => xs
                end.

(* split the sequence in two; the nth element will be the head of the second list *)
Fixpoint seq_split {A} (n : nat) (xs : seq A) : seq A * seq A :=
  match n, xs with
    | 0, xs => (nil, xs) 
    | (S n), (x :: xs) => let p := seq_split n xs in (x :: p.1, p.2)
    | (S n), nil => (nil, nil)
                      end.

Lemma seq_splitE  {A} n (xs : seq A) : (seq_split n xs).1 ++ (seq_split n xs).2 = xs.
  move: xs; induction n.
  done.
  induction xs.
  done.
  simpl.
  rewrite -{3}(IHn xs) //=.
Defined.

Lemma Perm_rcons {A} a (xs : seq A) :
  Permutation (a :: xs) (rcons xs a).
  induction xs.
  rewrite //=.
  rewrite //=.
  eapply perm_trans.
  apply perm_swap.
  apply perm_skip.
  done.
Qed.

Lemma Perm_rot {A} n (xs : list A) : Permutation xs (rot_rcons n xs).
  move: xs; induction n.
  simpl.
  done.
  simpl.
  induction xs.
  done.
  eapply perm_trans.
  apply Perm_rcons.
  apply IHn.
Qed.


(* inserts into list. if n >= size xs, appends to end *)
Fixpoint insert {A} (xs : seq A) (n : nat) (x : A) : seq A :=
    match n with
    | 0 => x :: xs
    | S n =>
    match xs with
        | y :: ys => y :: insert ys n x
        | nil => x :: nil
    end
        end.

Lemma size_insert {A} (xs : seq A) n x :
    size (insert xs n x) = S (size xs).
    move: xs; induction n.
    by destruct xs.
    induction xs.
    done.
    simpl.
    rewrite IHn //=.
Qed.

Lemma nth_error_insert_same {A} (xs : seq A) n x :
    n < (S (size xs)) ->
    List.nth_error (insert xs n x) n = Some x.
    move: n; induction xs.
    simpl.
    destruct n.
    done.
    induction n.
    done.
    done.
    induction n.
    simpl.
    done.
    simpl.
    intro; rewrite IHxs //=.
Qed.

Lemma nth_error_insert_lt {A} (xs : seq A) n m x :
  n < size xs ->
  m < n ->
  List.nth_error (insert xs n x) m = List.nth_error xs m.
  move: n m.
  induction xs.
  done.
  induction n.
  done.
  simpl.
  intros.
  induction m.
  done.
  rewrite //=.
  rewrite IHxs //=.
Qed.

Lemma nth_error_insert_gt {A} (xs : seq A) n m x :
  n < size xs ->
  m > n ->
  List.nth_error (insert xs n x) (S m) = List.nth_error xs (m).
  move: n m.
  induction xs.
  done.
  induction n.
  simpl.
  done.
  simpl.
  intros.
  destruct m.
  done.
  rewrite IHxs.
  done.
  done.
  done.
Qed.

Lemma insert_0 {A} (xs : seq A) (x : A) :
insert xs 0 x = x :: xs.
induction xs; done.
Qed.

Fixpoint insert_seq {A} (xs : seq A) (n : nat) (xs' : seq A) :=
match xs' with
| nil => xs
| x :: xs'' =>
    insert_seq (insert xs n x) n xs''
                end.

(* if x < len xs, remove nth element from xs *)
Fixpoint remove {A} (xs : seq A) (n : nat) : seq A :=
  match n, xs with
  | _, nil => nil
  | 0, (x :: xs) => xs
  | S n, (x :: xs) => x :: remove xs n
                        end.

Lemma remove_oob {A} (xs : seq A) n :
  n >= size xs ->
  remove xs n = xs.
  move: xs; induction n.
  induction xs.
  done.
  done.
  induction xs.
  done.
  simpl.
  intro.
  rewrite IHn //=.
Qed. 

Lemma size_remove {A} (xs : seq A) n :
  n < size xs ->
  size (remove xs n) = predn (size xs).
  move: xs; induction n.
  induction xs; done.
  induction xs; rewrite //=.
  move => h; rewrite IHn.
  destruct (size xs); done.
  done.
Qed.

Fixpoint remove_range {A} (xs : seq A) from len :=
  match len with
    | 0 => xs
    | S l => remove_range (remove xs from) from l
                           end.

Lemma remove_insert {A} (xs : seq A) n x :
  n < size xs ->
  remove (insert xs n x) n = xs.
  move: n; induction xs.
  induction n; rewrite //=.
  destruct n.
  done.
  simpl.
  move => h.
  rewrite IHxs //=.
Qed.

Lemma insert_remove_eq {A} (xs : seq A) n x :
  n < size xs ->
  List.nth_error xs n = Some x ->
  insert (remove xs n) n x = xs.
  move: n; induction xs.
  done.
  simpl.
  induction n.
  simpl.
  move => _ h; injection h => ->; destruct xs; done.
  simpl.
  move => h h'.
  rewrite IHxs //=.
Qed.

Lemma insert_removeC {A} (xs : seq A) n x :
  n < size xs ->
  List.nth_error xs n = Some x ->
  insert (remove xs n) n x =
  remove (insert xs n x) n.
  intros.
  rewrite insert_remove_eq.
  rewrite remove_insert.
  done.
  done.
  done.
  done.
Qed.

Lemma insert2_remove2 {A} (xs : seq A) pos x y :
  List.nth_error xs pos = Some x ->
  List.nth_error xs (S pos) = Some y ->
  insert (insert (remove (remove xs pos) pos) pos y) pos x = xs.
  move : xs.
  induction pos.
  destruct xs.
  done.
  destruct xs.
  done.
  simpl.
  rewrite !insert_0.
  move => h1 h2; injection h1; injection h2 => -> ->; done.
  destruct xs.
  done.
  simpl.
  destruct xs.
  done.
  intros.
  rewrite (IHpos (a0 :: xs)).
  done.
  done.
  done.
Qed.
  

Definition lset {A} (xs : seq A) (n : nat) (x : A) :=
  if n < size xs then
  insert (remove xs n) n x else xs.

Lemma lset_0_cons {A} (xs : seq A) x y :
  lset (x :: xs) 0 y = y :: xs.
  rewrite /lset.
  rewrite ltn0Sn.
  rewrite insert_0 //=.
Qed.

Lemma lset_Sn_cons {A} (xs : seq A) x y n :
  lset (x :: xs) (S n) y = x :: lset xs n y.
rewrite /lset.
simpl.
have -> : (n.+1 < (size xs).+1) = (n < size xs) by done.
destruct (n < size xs); done.
Qed.

(* if n < len xs, equal to xs[0..n] ++ xs' ++ xs[n+1 ..] *)
Definition  lset_seq {A} (xs : seq A) (n : nat) (xs' : seq A) : seq A :=
  insert_seq (remove xs n) n xs'.

Lemma insert_seq_Sn_cons {A} (xs : seq A) x n ys :
  insert_seq (x :: xs) n.+1 ys =
  x :: insert_seq xs n ys.
  move: n xs; induction ys.
  done.
  simpl.
  intros.
  rewrite IHys.
  done.
Qed.

Lemma lset_seq_Sn_cons {A} (xs : seq A) x ys n :
  lset_seq (x :: xs) (S n) ys =
  x :: lset_seq xs n ys.
  rewrite /lset_seq.
  simpl.
  rewrite insert_seq_Sn_cons //=.
Qed.


Lemma lset_lset {A} (xs : seq A) n (x x' : A) :
  n < size xs ->
  lset (lset xs n x') n x = lset xs n x.
  move: xs; induction n.
  induction xs.
  simpl.
  rewrite /lset //=.
  simpl.
  intro.
  rewrite !lset_0_cons //=.
  induction xs.
  done.
  move => h.
  rewrite !lset_Sn_cons //=.
  rewrite IHn //=.
Qed.

Lemma lset_nth_error {A} (xs : seq A) (n : nat) x :
  n < size xs ->
  List.nth_error xs n = Some x ->
  xs = lset xs n x.
  move: n.
  induction xs.
  done.
  induction n.
  simpl.
  intro.
  intro H'; injection H'; intro; subst.
  rewrite lset_0_cons //=.
  simpl.
  move => h.
  move/IHxs => ->.
  rewrite lset_Sn_cons lset_lset //=.
  done.
Qed.

Lemma nth_error_lset {A} (xs : seq A) (n m : nat) x :
  n < size xs ->
  List.nth_error (lset xs n x) m = if n == m then Some x else List.nth_error xs m.
  move: m n.
  induction xs.
  simpl.
  done.
  induction m.
  induction n.
  simpl.
  rewrite /lset /= insert_0; done.
  simpl.
  rewrite lset_Sn_cons.
  done.
  induction n.
  simpl.
  rewrite /lset /=.
  rewrite insert_0.
  done.
  simpl.
  move => h.
  rewrite lset_Sn_cons.
  rewrite IHxs.
  rewrite /eq_op //=.
  done.
Qed.

Lemma size_lset {A} (xs : seq A) n x :
  n < size xs ->
  size (lset xs n x) = size xs.
  intro.
  rewrite /lset H.
  rewrite size_insert size_remove.
  destruct (size xs); done.
  done.
Qed.



Lemma nth_error_remove {A} (xs : seq A) n m :
  n < size xs ->
  List.nth_error (remove xs n) m = if m < n then List.nth_error xs m else List.nth_error xs m.+1.
  move: m n.
  induction xs.
  done.
  induction n.
  simpl.
  done.
  simpl.
  move => h.
  destruct m.
  done.
  simpl.
  rewrite IHxs.
  have -> : (m.+1 < n.+1) = (m < n) by done.
  destruct (m < n).
  done.
  destruct xs; done.
  done.
Qed.

Lemma nth_error_eqP {A} (xs xs' : seq A) :
  (forall n, List.nth_error xs n = List.nth_error xs' n) -> xs = xs'.
  move: xs'; induction xs.
  induction xs'.
  done.
  move/(_ 0).
  done.
  intros.
  destruct xs'.
  move: (H 0); done.
  move: (H 0) => h; injection h => ->.
  erewrite IHxs.
  apply: erefl.
  intros.
  move: (H (S n)).
  done.
Qed.

Definition swap {A} n m (xs : seq A) :=
  match List.nth_error xs n, List.nth_error xs m with
    | Some x, Some y =>
      lset (lset xs n y) m x
    | _, _ => xs end.

Lemma size_length {A} (xs : seq A) :
  size xs = length xs.
  induction xs; rewrite //=.
Qed.

Lemma nth_error_size_lt {A} (xs : seq A) n :
  isSome (List.nth_error xs n) =
  (n < size xs).
  rewrite size_length.
  apply Bool.eq_true_iff_eq; split.
  intro.
  apply/ltP.
  apply List.nth_error_Some.
  destruct (List.nth_error xs n); done.
  move/ltP.
  move/List.nth_error_Some.
  destruct (List.nth_error xs n); done.
Qed.

Lemma Perm_swap {A} n m (xs : seq A) :
  Permutation xs (swap n m xs).
rewrite /swap.
remember (List.nth_error xs n) as o1; destruct o1; rewrite //=; symmetry in Heqo1.
remember (List.nth_error xs m) as o2; destruct o2; rewrite //=; symmetry in Heqo2.
apply Permutation_nth_error.
split.
rewrite -!size_length.
rewrite size_lset.
rewrite size_lset.
done.
rewrite -nth_error_size_lt Heqo1 //=.
rewrite size_lset.
rewrite -nth_error_size_lt Heqo2 //=.
rewrite -nth_error_size_lt Heqo1 //=.

exists (fun x =>
     if x == n then m else
       if x == m then n else
         x).
split.
move => x y.
destruct (eqVneq x n); subst.
destruct (eqVneq y n); subst.
done.
destruct (eqVneq y m); subst.
done.
intro; subst.
rewrite eq_refl //= in i0.
destruct (eqVneq x m); subst.
destruct (eqVneq y n); subst.
done.
destruct (eqVneq y m); subst.
done.
intro; subst.
rewrite eq_refl //= in i0.
destruct (eqVneq y n); subst.
intro; subst.
rewrite eq_refl //= in i0.
destruct (eqVneq y m); subst.
intro; subst.
rewrite eq_refl //= in i.
done.

intros.
rewrite !nth_error_lset.
destruct (eqVneq m n0); subst.
destruct (eqVneq n0 n); subst.
congruence.
congruence.
destruct (eqVneq n n0); subst.
congruence.
done.

rewrite -nth_error_size_lt Heqo1 //=.
rewrite size_lset.
rewrite -nth_error_size_lt Heqo2 //=.
rewrite -nth_error_size_lt Heqo1 //=.
Qed.



Definition remove2 {A} (xs : seq A) (n1 n2 : nat) :=
  if n1 < n2 then remove (remove xs n1) (predn n2) else remove (remove xs n2) (predn n1).

Lemma insert0 {A} (xs : seq A) x : 
  insert xs 0 x = x :: xs.
  destruct xs; done.
Qed.

Lemma nth_error_cons {A} (xs : seq A) x i :
  List.nth_error (x :: xs) i = 
  if i is 0 then Some x else List.nth_error xs (i.-1).
  destruct i; rewrite //=.
Qed.

Lemma nth_error_swap {A} (xs : seq A) n m i :
  List.nth_error (swap n m xs) i =
  if [&& n < size xs & m < size xs] then
    if i == n then List.nth_error xs m else
      if i == m then List.nth_error xs n else
        List.nth_error xs i
  else List.nth_error xs i.
  rewrite /swap.
  rewrite -nth_error_size_lt.
  rewrite -nth_error_size_lt.
  remember (List.nth_error xs n) as o; destruct o; rewrite //=.
  remember (List.nth_error xs m) as o'; destruct o'; rewrite //=.
  rewrite !nth_error_lset.
  destruct (eqVneq m i); subst.
  destruct (eqVneq n i); subst.
  rewrite Heqo Heqo'; done.
  done.
  rewrite eq_sym //=.
  rewrite -nth_error_size_lt -Heqo //=.
  rewrite size_lset.
  rewrite -nth_error_size_lt -Heqo' //=.
  rewrite -nth_error_size_lt -Heqo //=.
Qed.

Lemma nth_error_behead {A} (xs : seq A) i :
  List.nth_error (behead xs) i =
  List.nth_error xs i.+1.
  destruct xs; simpl.
  destruct i; done.
  done.
Qed.

Lemma swap0E {A} (xs : seq A) n b a : 
  n != 0 ->
  List.nth_error xs 0 = Some a ->
  List.nth_error xs n = Some b ->
  swap 0 n xs = b :: (lset (behead xs) (n.-1) a).
  intros.
  apply nth_error_eqP => i.
  rewrite nth_error_swap.
  rewrite nth_error_cons.
  rewrite nth_error_lset.
  rewrite nth_error_behead.
  rewrite -!nth_error_size_lt.
  rewrite H0 H1 //=.
  destruct i; rewrite //=.
  have -> : (i.+1 == n) = (n.-1 == i).
  apply Bool.eq_true_iff_eq; split.
  move/eqP => <-.
  rewrite //= eq_refl //=.
  move/eqP => <-.
  destruct n.
  rewrite //=.
  rewrite //= eq_refl //=.
  done.
  rewrite size_behead.
  destruct n; destruct xs; simpl in *.
  done.
  done.
  done.
  rewrite -nth_error_size_lt H1 //=.
Qed.

Lemma swapSS {A} (xs : seq A) x n m :
  swap n.+1 m.+1 (x :: xs) = x :: swap n m xs.
  rewrite /swap //=.
  destruct (List.nth_error xs n); rewrite //=.
  destruct (List.nth_error xs m); rewrite //=.
  rewrite !lset_Sn_cons //=.
Qed.

Lemma ltn_pred_pred x y :
  y > 1 ->
  x < y ->
  x.-1 < y.-1. 
  destruct x; destruct y; rewrite //=.
Qed.

Lemma size_swap {A} a b (rs : seq A) :
  size (swap a b rs) = size rs.
  rewrite /swap.
  case h0 : (List.nth_error rs a).
  case h1 : (List.nth_error rs b).
  rewrite size_lset.
  rewrite size_lset //=.
  rewrite -nth_error_size_lt h0 //=.
  rewrite size_lset.
  rewrite -nth_error_size_lt h1 //=.
  rewrite -nth_error_size_lt h0 //=.
  done.
  done.
Qed.

Lemma nth_to_head {A} (x : A) n rs:
  List.nth_error rs n = Some x ->
  Permutation rs (x :: remove rs n).
  move: n; induction rs.
  intros.
  destruct n; done.
  intros.
  destruct n.
  simpl in *.
  inversion H; subst.
  done.
  simpl in *.
  symmetry.
  rewrite perm_swap.
  apply perm_skip.
  symmetry; apply IHrs.
  done.
Qed.

Lemma nth_to_head2 {A} (x y : A) n1 n2 rs :
  n1 != n2 ->
  List.nth_error rs n1 = Some x ->
  List.nth_error (remove rs n1) n2.-1 = Some y ->
  Permutation rs (x :: y :: remove (remove rs n1) n2.-1).
  intros.
  etransitivity.
  apply (nth_to_head x n1 rs).
  done.
  apply perm_skip.
  etransitivity.
  apply (nth_to_head y n2.-1).
  done.
  apply perm_skip.
  done.
Qed.


Require Import Setoid Relation_Definitions Morphisms.
Close Scope bool_scope.

#[export]
Instance cat_Proper t : Proper (@Permutation t ==> @Permutation t ==> @Permutation t) cat.
  move => x y z a b c.
  rewrite z c //=.
Qed.

Lemma cons_catE {t} (x : t) xs :
  x :: xs = [:: x] ++ xs.
  by done.
Qed.

Ltac find_in_rec x xs n :=
  match xs with
  | nil => n
  | (?x' :: ?xs') =>
    let a := eval simpl in x' in
    let b := eval simpl in x in
    match a with
      | b => n
      | _ => find_in_rec x xs' (S n) end end.
Ltac find_in x xs := find_in_rec x xs 0.

Ltac perm_match_step :=
  match goal with
    | |- Permutation ?xs (?y :: ?ys) => 
        let n := find_in y xs in
        setoid_rewrite (Perm_swap 0 n) at 1; rewrite /swap /lset //=;
        apply perm_skip end.                                               
  

Ltac perm_match :=
  match goal with
  | |- Permutation nil nil => done
  | |- Permutation ?xs (?y :: ?ys) =>
    let n := find_in y xs in
    setoid_rewrite (Perm_swap 0 n) at 1; rewrite /swap /lset //=;
    apply perm_skip; perm_match end.        

Ltac perm_tac := cat_perm_tac; perm_match.

Ltac perm_tac' xs :=
  match xs with
    | nil => perm_tac
    | ?x :: ?xs' => setoid_rewrite (cons_catE x) at 1; setoid_rewrite (cons_catE x) at 3; perm_tac' xs' end.

