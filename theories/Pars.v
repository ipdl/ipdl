
(* This file constructs a notion of N-ary parallel composition for IPDL protocols, rather than only binary. We then lift 
our reasoning to be about N-ary composition (with prefix 'pars').
*)


From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple fintype.
From mathcomp Require Import choice path bigop.
Require Import FunctionalExtensionality Classes.Equivalence.
Require Import Lib.SeqOps.
Require Import Lib.Base Ipdl.Exp Lib.TupleLems Lib.setoid_bigop.
Require Import Lib.Set Core.

Definition pars_def {C} (r : list (@ipdl C)) : ipdl := foldr Par (prot0) r.

Definition pars {C} r := (nosimpl (@pars_def C r)).


Notation "[pars xs ]" := (pars xs) (format "[pars  xs ]").
Notation "[|| x1 ]" := (pars (x1 :: [::]))
  (at level 0, format "[||  x1 ]") : seq_scope.

Notation "[|| x1 ; x2 ; .. ; xn ]" := (pars (x1 :: x2 :: .. [:: xn] ..))
  (at level 0, format "[||  '[' x1 ; '/' x2 ; '/' .. ; '/' xn ']' ]"
  ) : ipdl_scope.

Arguments pars : simpl never.

Section Pars.
  Context {chan : Type -> Type}.
  Local Notation EqProt := (@EqProt chan).


Lemma pars_cons r rs : 
  EqProt (pars (r :: rs)) (r ||| pars rs).
  rewrite //=.
Qed.

Lemma pars_prot0 (rs : seq (ipdl)) :
  EqProt (pars (prot0 :: rs)) (pars rs).
  rewrite pars_cons -eq_0par //=.
Qed.

Lemma pars_cons_cong r1 r2 rs1 rs2 :
  EqProt r1 r2 ->
  EqProt (pars rs1) (pars rs2) ->
  EqProt (pars (r1 :: rs1)) (pars (r2 :: rs2)).
  intros; rewrite !pars_cons.
  apply EqCong; done.
Qed.

Lemma pars_rcons rs r :
  EqProt (pars rs ||| r) (pars (rcons rs r)).
  induction rs.
  rewrite //=.
  rewrite EqCompComm; reflexivity.
  rewrite //= !pars_cons.
  rewrite -IHrs.
  rewrite EqCompAssoc.
  reflexivity.
Qed.

Lemma pars_nil : @pars chan nil = prot0.
  rewrite /pars //=.
Qed.

Lemma pars_cat rs1 rs2 : 
  EqProt (pars (rs1 ++ rs2)) (pars rs1 ||| pars rs2).
  move:rs2; induction rs1; rewrite //=; intro.
  rewrite pars_nil -eq_0par //=.
  rewrite !pars_cons.
  rewrite IHrs1 EqCompAssoc; reflexivity.
Qed.

Lemma pars1 r : EqProt (pars [:: r]) r.
  rewrite /pars //= -eq_par0 //=.
Qed.

Lemma pars_pars rs rs' : EqProt (pars (pars rs :: rs')) (pars (rs ++ rs')).
  rewrite pars_cons.
  rewrite pars_cat.
  reflexivity.
Qed.

  Lemma pars2 r1 r2 :
    EqProt (pars [:: r1; r2]) (r1 ||| r2).
    rewrite !pars_cons /pars -eq_par0 //=.
  Qed.

Lemma Perm_pars (xs ys : seq ipdl) :
  Permutation.Permutation xs ys ->
  EqProt (pars xs) (pars ys).
  elim.
  reflexivity.
  intros.
  rewrite !pars_cons //= H0; reflexivity.
  intros.
  rewrite !pars_cons //= EqCompAssoc (EqCompComm y) -EqCompAssoc; reflexivity.
  intros.
  rewrite (H0); done.
Qed.

   Lemma pars_split (n : nat) (ps : seq ipdl) :
     EqProt (pars ps) (pars (take n ps) ||| pars (drop n ps)).
    rewrite -pars_cat.
    rewrite cat_take_drop //=.
   Qed.

   Lemma par_in_pars r1 r2 rs :
     EqProt (pars ((r1 ||| r2) :: rs))
                (pars (r1 :: r2 :: rs)).
     rewrite !pars_cons EqCompAssoc //=.
   Qed.

    Lemma par_in_pars2 r rs r1 r2 :
        EqProt (pars (r :: (r1 ||| r2) :: rs))
                    (pars (r :: r1 :: r2 :: rs)).
        rewrite !pars_cons.
        apply EqCong; rewrite //=.
        rewrite EqCompAssoc; done.
    Qed.

    Lemma par_in_pars3 r r' rs r1 r2 :
        EqProt (pars (r :: r' :: (r1 ||| r2) :: rs))
                    (pars (r :: r' :: r1 :: r2 :: rs)).
        rewrite !pars_cons.
        apply EqCong; rewrite //=.
        apply EqCong; rewrite //=.
        rewrite EqCompAssoc; done.
    Qed.

    Lemma par_in_pars4 r r' r'' rs r1 r2 :
        EqProt (pars (r :: r' :: r'' :: (r1 ||| r2) :: rs))
                    (pars (r :: r' :: r'' :: r1 :: r2 :: rs)).
        rewrite !pars_cons.
        apply EqCong; rewrite //=.
        apply EqCong; rewrite //=.
        apply EqCong; rewrite //=.
        rewrite EqCompAssoc; done.
    Qed.


Lemma cat_nil_nil {A : eqType} (x y : seq A) :
  x = nil ->
  y = nil ->
  (x ++ y = nil).
  move => -> ->; done.
Qed.

Lemma filter_none {A} (xs : seq A) (P : pred A) :
  all (fun x => ~~ (P x)) xs ->
  filter P xs = nil.
  intros; induction xs; rewrite //=.
  simpl in H; destruct (andP H).
  rewrite (negbTE H0) IHxs //=.
Qed.

Lemma New_in_pars t k rs :
  pars [:: New t k & rs] =p @New chan t (fun x => pars [:: k x & rs]).
  rewrite pars_cons.
  rewrite EqCompNew.
  apply EqCongNew; intros.
  rewrite pars_cons //=.
Qed.

(* Rewriting in pars *)

Inductive list_eqprot : list ipdl -> list ipdl -> Prop :=
  | nil_equiv : list_eqprot nil nil
  | cons_equiv x y s t : EqProt x y -> list_eqprot s t -> list_eqprot (x :: s) (y :: t).

Instance list_eqprot_refl : Reflexive list_eqprot.
   intro.
   induction x.
   constructor.
   constructor.
   done.
   done.
Qed.

Instance list_eqprot_tr : Transitive list_eqprot.
   intro; intros.
   move: z H0; induction H; intros.
   done.
   inversion H1; subst.
   constructor.
   rewrite H //=.
   apply IHlist_eqprot.
   done.
Qed.

Instance list_eqprot_sym : Symmetric list_eqprot.
   intro; intros.
   induction H.
   done.
   constructor.
   rewrite H //=.
   done.
Qed.



Lemma swapE  n k rs :
  EqProt (pars rs) (pars (swap n k rs)).
  apply Perm_pars.
  apply Perm_swap.
Qed.

Lemma pars_fold t1 t2 (a : chan t1) (r : rxn t2)
      (k : t2 -> rxn t1) rs :
  EqProt 
         (New t2 (fun c => pars [:: Out a (x <-- Read c ;; k x), Out c r & rs]))
         (pars [:: Out a (x <-- r ;; k x) & rs]).
  etransitivity.
  apply EqCongNew => c.
  rewrite !pars_cons.
  rewrite EqCompAssoc.
  apply EqRefl.
  rewrite -EqCompNew.
  setoid_rewrite EqCompComm at 2.
  rewrite EqFold. 
  rewrite -pars_cons //=.
Qed.

(* Tactics for basic permutations / editing *)

Lemma pars_edit' r1 r2 rs :
  EqProt r1 r2 ->
  EqProt (pars (r1 :: rs)) (pars (r2 :: rs)).
  intros.
  rewrite //=.
  apply EqCong.
  done.
  reflexivity.
Qed.

Open Scope bool_scope.

Lemma pars_edit n r1 r2 rs : 
  EqProt r1 r2 ->
  List.nth_error rs n = Some r1 ->
  EqProt (pars rs) (pars (lset rs n r2)).
  intros.
  destruct (eqVneq n 0); subst.
  destruct rs.
  rewrite //=.
  simpl in H.
  inversion H0; subst.
  erewrite pars_edit'.
  rewrite lset_0_cons.
  reflexivity.
  done.
  
  etransitivity.
  apply (swapE 0 n).
  destruct rs; simpl in *.
  destruct n; done.
  erewrite swap0E; last first.
  apply H0.
  done.
  done.
  erewrite pars_edit'; last by apply H.
  etransitivity.
  apply (swapE 0 n).
  simpl.
  have -> : swap 0 n (r2 :: lset rs n.-1 i0) =
           lset (i0 :: rs) n (r2).
  apply nth_error_eqP => j.
  rewrite nth_error_swap //=.
  rewrite nth_error_lset.
  destruct (eqVneq n j); subst.
  rewrite size_lset.
  have: List.nth_error (i0 :: rs) j by rewrite H0.
  rewrite nth_error_size_lt => ->.
  rewrite (negbTE i) //=.
  rewrite -nth_error_size_lt.
  destruct j.
  done.
  simpl.
  simpl in H0.
  rewrite H0 //=.
  rewrite size_lset; last first.
  rewrite -nth_error_size_lt.
  destruct n.
  done.
  simpl in *; rewrite H0 //=.
  destruct n.
  done.
  simpl in *.
  have -> : (n.+1 < (size rs).+1) = (n < size rs) by done.
  rewrite -nth_error_size_lt H0 //=.
  destruct j; simpl.
  rewrite nth_error_lset.
  rewrite eq_refl //=.
  rewrite -nth_error_size_lt H0 //=.
  rewrite nth_error_lset.
  rewrite eqE //= in i1. 
  have hnj: n != j by done.
  rewrite (negbTE hnj); done.
  rewrite -nth_error_size_lt H0 //=.
  rewrite -nth_error_size_lt H0 //=.
  reflexivity.
Qed.

Lemma pars_edit_out n m (cm : chan m) (r1 r2 : rxn m) (rs : seq (ipdl)) : 
  r1 =r r2 ->
  List.nth_error rs n = Some (Out cm r1) ->
  EqProt (pars rs) (pars (lset rs n (Out cm r2))).
  intros.
  eapply pars_edit.
  apply EqCongReact.
  apply H.
  done.
Qed.

   Lemma inline {t} {t'} (b : chan t') (c : chan t) k r :
     isDet _ r ->
     EqProt (Out b (x <-- Read c ;; k x) ||| Out c r)
                      (Out b (x <-- r ;; k x) ||| Out c r).
     intros.
     rewrite EqCompComm.
     rewrite EqSubst //=.
     rewrite EqCompComm.
     done.
   Qed.

   Lemma pars_inline {t} {t'} (b : chan t') (c : chan t) k r rs :
     isDet _ r ->
     EqProt (pars [:: (Out b (x <-- Read c ;; k x)), Out c r & rs])
                      (pars [:: (Out b (x <-- r ;; k x)), Out c r & rs]).
     intros.
     rewrite !pars_cons.
     rewrite !EqCompAssoc.
     rewrite inline.
     done.
     done.
   Qed.

Lemma pars_mkdep {t1 t2} (c : chan t1) (d : chan t2) r1 r2 rs :
  (forall t (c0 : chan t), can_read c0 r2 -> reads_from c0 r1) ->
  pars [::
          c ::= r1, d ::= r2 & rs] =p
  pars [::
          c ::= (_ <-- Read d ;; r1), d ::= r2 & rs].
  intros.
  symmetry.
  rewrite pars_cons.
  rewrite pars_cons.
  rewrite EqCompAssoc.
  rewrite EqCompComm.
  etransitivity.
  apply EqCongComp.
  rewrite EqCompComm.
  apply EqUnused.
  done.
  symmetry; rewrite !pars_cons.
  symmetry.
  rewrite EqCompComm.
  rewrite EqCompAssoc.
  rewrite (EqCompComm (c ::= r1)).
  done.
Qed.

Lemma pars_unused {t1 t2} (c1 : chan t1) (c2 : chan t2) rs r r' :
  (forall (t : Type) (c0 : chan t), can_read c0 r -> reads_from c0 r') ->
  (pars [:: Out c2 (_ <-- Read c1;; r'), Out c1 r & rs]) =p
  (pars [:: Out c2 (r'), Out c1 r & rs]).
  intros.
  rewrite -pars_mkdep.
  done.
  done.
Qed.


Lemma pars_tr {t1 t2 t3} (c : chan t1) (d : chan t3) k1 (e : chan t2) k2 rs :
  pars [::
          c ::= (x <-- Read d ;; k1 x),
          e ::= (x <-- Read c ;; k2 x) & rs]
  =p
  pars [::
          c ::= (x <-- Read d ;; k1 x),
          e ::= (_ <-- Read d ;; x <-- Read c ;; k2 x) & rs].
  intros; rewrite !pars_cons !EqCompAssoc.
  rewrite EqSubsume; last first.
  done.
Qed.

Lemma new_pars_remove {t1} (r : chan t1 -> rxn t1) rs :
  (a <- new t1 ;; pars [:: Out a (r a) & rs]) =p pars rs.
  intros.
  setoid_rewrite pars_cons.
  rewrite RRemove; done.
Qed.

Lemma generalize_pars_eq2_1 r1 r2 r1' r2' :
  (forall rs, pars [:: r1, r2 & rs] =p pars [:: r1', r2' & rs] ) ->
  forall rs1 rs2,
    @pars chan ([:: r1] ++ rs1 ++ [:: r2] ++ rs2) =p pars (r1' :: rs1 ++ [:: r2'] ++ rs2).
  intros.
  induction rs1.
  simpl.
  rewrite H.
  done.
  simpl.
  rewrite (swapE 0 1); rewrite /swap /lset //=.
  rewrite insert_0.
  rewrite (pars_split 1); simpl.
  rewrite IHrs1.
  rewrite -pars_cat; simpl.
  rewrite (swapE 0 1); rewrite /swap /lset //=.
  rewrite insert_0.
  done.
Qed.


End Pars.

Add Parametric Relation {C} : (list (@ipdl C)) (list_eqprot ) 
                                       reflexivity proved by (list_eqprot_refl )
                                       symmetry proved by (list_eqprot_sym )
                                           transitivity proved by (list_eqprot_tr ) as list_eqprot_rel.

Close Scope bool_scope.
Require Import Setoid Relation_Definitions Morphisms.

Add Parametric Morphism {C} : (@pars C) with signature
    list_eqprot ==> EqProt as pars_mor.
  intros.
  induction H.
  done.
  rewrite !pars_cons.
  rewrite H.
  rewrite IHlist_eqprot.
  done.
Qed.

Add Parametric Morphism {C} : cons with signature
    (@EqProt C) ==> list_eqprot ==> list_eqprot as cons_mor.
  intros.
  constructor; done.
Qed.


Ltac find_in_pars_rec p rs acc :=
  lazymatch eval simpl in rs with
    | nil => acc
    | (?r :: ?rs') =>
      lazymatch r with
        | context[p] => acc
        | _ => find_in_pars_rec p rs' (S acc)
      end
   end.

Ltac find_in_pars p rs := find_in_pars_rec p rs 0.

Ltac get_idx nxx :=
  let t := type of nxx in
  lazymatch eval simpl in t with
    | nat => constr:(nxx)
    | _ =>
      match goal with
      | [ |- EqProt (pars ?rs) _ ] =>
        let j := find_in_pars nxx rs in j
      end
  end.

Ltac swap_tac nxx mxx :=
  let m___ := get_idx mxx in
  setoid_rewrite (swapE nxx m___) at 1; rewrite /swap /lset /=.

Ltac split_tac n :=
    match goal with
      | [ |- @EqProt  _ _ ] => setoid_rewrite (pars_split n _) at 1; rewrite /= end.

Ltac join_tac :=
    match goal with
      | [ |- EqProt  _ ] => setoid_rewrite <- (pars_cat _ _ ) at 1; rewrite /= end.



Lemma nth_errorP {T} (xs : seq T) x n :
  List.nth_error xs n = Some x ->
  exists xs1 xs2,
    (xs = xs1 ++ [:: x] ++ xs2) /\ (size xs1 = n).
  move: xs x; induction n.
  intros.
  destruct xs.
  done.
  simpl in *.
  inversion H; subst.
  exists nil.
  simpl.
  exists xs; split; done.
  intros.
  destruct xs.
  done.
  simpl in *.
  move/IHn: H => [A [B [h1 h2]]].
  subst.
  exists (t :: A).
  exists B.
  simpl.
  split; done.
Qed.


  
