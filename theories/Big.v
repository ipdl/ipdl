
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple fintype.
From mathcomp Require Import choice path bigop.
Require Import FunctionalExtensionality Classes.Equivalence.
Require Import Lib.Base Ipdl.Exp Lib.TupleLems Lib.setoid_bigop.
Require Import Lib.Crush Lib.Set Core Lib.OrdLems Lib.Learn Classical Pars.


Reserved Notation "\||_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \||_ ( i <- r | P ) '/ ' F ']'").
Reserved Notation "\||_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \||_ ( i <- r ) '/ ' F ']'").
Reserved Notation "\||_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \||_ ( m <= i < n | P ) '/ ' F ']'").
Reserved Notation "\||_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \||_ ( m <= i < n ) '/ ' F ']'").
Reserved Notation "\||_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \||_ ( i | P ) '/ ' F ']'").
Reserved Notation "\||_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50). (* only parsing *)
Reserved Notation "\||_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50). (* only parsing *)
Reserved Notation "\||_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \||_ ( i < n | P ) '/ ' F ']'").
Reserved Notation "\||_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \||_ ( i < n ) '/ ' F ']'").
Reserved Notation "\||_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \||_ ( i 'in' A | P ) '/ ' F ']'").
Reserved Notation "\||_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \||_ ( i 'in' A ) '/ ' F ']'").

Notation "\||_ ( i <- r | P ) F" :=
  (\big[Par/prot0]_(i <- r | P%ipdl) F%ipdl) : ipdl_scope.
Notation "\||_ ( i <- r ) F" :=
  (\big[Par/prot0]_(i <- r) F%ipdl) : ipdl_scope.
Notation "\||_ ( m <= i < n | P ) F" :=
  (\big[Par/prot0]_(m <= i < n | P%ipdl) F%ipdl) : ipdl_scope.
Notation "\||_ ( m <= i < n ) F" :=
  (\big[Par/prot0]_(m <= i < n) F%ipdl) : ipdl_scope.
Notation "\||_ ( i | P ) F" :=
  (\big[Par/prot0]_(i | P%ipdl) F%ipdl) : ipdl_scope.
Notation "\||_ ( i : t | P ) F" :=
  (\big[Par/prot0]_(i : t | P%ipdl) F%ipdl) (only parsing) : ipdl_scope.
Notation "\||_ ( i : t ) F" :=
  (\big[Par/prot0]_(i : t) F%ipdl) (only parsing) : ipdl_scope.
Notation "\||_ ( i < n | P ) F" :=
  (\big[Par/prot0]_(i < n | P%ipdl) F%ipdl) : ipdl_scope.
Notation "\||_ ( i < n ) F" :=
  (\big[Par/prot0]_(i < n) F%ipdl) : ipdl_scope.
Notation "\||_ ( i 'in' A | P ) F" :=
  (\big[Par/prot0]_(i in A | P%ipdl) F%ipdl) : ipdl_scope.
Notation "\||_ ( i 'in' A ) F" :=
  (\big[Par/prot0]_(i in A) F%ipdl) : ipdl_scope.

(* Bigop lemmas *)

Open Scope bool_scope.


Lemma EqProt_big {I : eqType} (r : seq I) (P1 P2 : pred I)
      (F1 F2 : I -> rset) :
  {in r, P1 =i P2} ->
  (forall x, x \in r -> P1 x -> EqProt (F1 x) (F2 x)) ->
  EqProt
    (\||_(x <- r | P1 x) (F1 x))
    (\||_(x <- r | P2 x) (F2 x)).
  induction r; rewrite //=.
  rewrite !big_nil //=.
  rewrite !big_cons //=.
  intros.
  have -> : P1 a = P2 a.
  apply H; rewrite in_cons eq_refl //=.
  case h : (P2 a).
  rewrite H0.
  rewrite IHr.
  done.
  move => x Hx; apply H.
  rewrite in_cons Hx orbT //=.
  intros; apply H0.
  rewrite in_cons H1 orbT //=.
  done.
  rewrite in_cons eq_refl //=.
  have: a \in a::r by rewrite in_cons eq_refl //=.
  move/H => //= Ha.
  rewrite /in_mem //= in Ha.
  congruence.
  apply IHr.
  move => x Hx; apply H.
  rewrite in_cons Hx orbT //=.
  intros; apply H0.
  rewrite in_cons H1 orbT //=.
  done.
Qed.

   Lemma EqProt_big_r {I : eqType} (xs : seq I) (p : pred I) f g : 
     (forall x, x \in xs -> p x -> EqProt (f x) (g x)) ->
     EqProt (\||_(x <- xs | p x) (f x))
                (\||_(x <- xs | p x) (g x)).
     intros.
     apply EqProt_big; done.
   Qed.

Lemma bigpar_par {I} (ms : seq I) (P : pred I) (A B : I -> rset) :
  EqProt (\||_ (i <- ms | P i) (A i ||| B i)) ((\||_(i <- ms | P i) A i) ||| (\||_(i <- ms | P i) B i)).
  induction ms.
  rewrite !big_nil -eq_par0 //=; reflexivity.
  rewrite !big_cons.
  case h: (P a).
  rewrite IHms.
  rewrite -ParAssoc.
  rewrite -ParAssoc.
  apply EqCong.
  reflexivity.
  rewrite ParSym.
  rewrite -ParAssoc.
  apply EqCong.
  reflexivity.
  apply ParSym.
  rewrite IHms.
  done.
Qed.

Lemma bigpar_nat_par n p f g :
    EqProt ((\||_(0 <= x < n | p x) (f x)) ||| (\||_(0 <= x < n | p x) (g x)))
                (\||_(0 <= x < n | p x) (f x ||| g x)).
    rewrite bigpar_par //=.
   Qed.

Open Scope bool_scope.

Lemma bigpar_D1 {I : eqType} (x : I) (rs : seq I) (P : pred I) F :
  x \in rs ->
  P x ->       
  uniq rs ->
  EqProt (\||_(r <- rs | P r) F r) ((F x) ||| \||_(r <- rs | P r && (r != x)) (F r)).
  move : x.
  induction rs.
  done.
  intros.
  rewrite in_cons in H.
  move/orP: H; elim.
  move/eqP; intro; subst.
  rewrite !big_cons eq_refl andbF //=.
  case h : (P a).
  apply EqPar.
  apply EqProt_big.
  move => b //=; intros.
  rewrite /in_mem //=.
  destruct (eqVneq b a); subst.
  simpl in H1; rewrite H //= in H1.
  rewrite andbT //=.
  done.
  rewrite h //= in H0.
  intros.
  rewrite !big_cons.
  destruct (eqVneq a x); subst.
  simpl in H1.
  rewrite H //= in H1.
  rewrite andbT.
  case h : (P a).
  rewrite IHrs.
  rewrite ParAssoc.
  rewrite (ParSym (F a)).
  rewrite ParAssoc.
  reflexivity.
  done.
  done.
  simpl in H1; by destruct (andP H1).
  apply IHrs; rewrite //=.
  simpl in H1; by destruct (andP H1).
Qed.

   Lemma bigpar_nat_D1 n x (p : pred nat) (F : nat -> rset) :
     x < n ->
     p x ->
     EqProt (\||_(0 <= i < n | p i) (F i))
                (F x ||| (\||_(0 <= i < n | p i && (i != x)) (F i))).
     intros.
     rewrite (bigpar_D1  x).
     reflexivity.
     rewrite mem_index_iota; done.
     done.
     apply iota_uniq.
   Qed.

Lemma bigpar_D1_ord {N : nat} (x : 'I_N) (P : pred 'I_N) F :
  P x ->       
  EqProt (\||_(n < N | P n) F n) ((F x) ||| \||_(n < N | P n && (n != x)) (F n)).
  intros.
  rewrite bigpar_D1.
  reflexivity.
  apply mem_index_enum.
  done.
  apply index_enum_uniq.
Qed.

    Lemma bigpar_cat {A} (xs ys : seq A) P  (f : A -> rset) :
      EqProt (\||_(x <- (xs ++ ys) | P x) (f x)) ((\||_(x <- xs | P x) (f x)) ||| (\||_(x <- ys | P x) (f x))).
      induction xs; rewrite //=.
      rewrite !big_nil -eq_0par //=.
      rewrite !big_cons.
      destruct (P a).
      rewrite IHxs ParAssoc //=.
      rewrite IHxs //=.
    Qed.

    Lemma In_big {I : eqType} (xs : seq I) (P :  pred I) (f : I -> rset) a j :
      P j ->
      In (f j) a ->
      j \in xs ->
      In (\||_(x <- xs | P x) f x) a.
      intros.
      induction xs.
      done.
      rewrite big_cons.
      rewrite in_cons in H1; move/orP: H1; elim => [H1 | H1].
      move/eqP: H1 => H1; subst.
      rewrite H //=.
      left; apply H0.
      destruct (P a0).
      right; apply IHxs; done.
      apply IHxs; done.
    Qed.
    
    Require Import Lib.setoid_bigop.
    
    Print big_cat_nat.
    
    (* From mathcomp *)
    Lemma iotaD m n1 n2 : iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
Proof. by elim: n1 m => [|n1 IHn1] m; rewrite ?addn0 // -addSnnS /= -IHn1. Qed.

    Lemma iotaS_r m n : iota m (n.+1) = iota m n ++ iota (m + n) 1.
      rewrite -iotaD //=.
      rewrite addn1 //=.
    Qed.
    
    Lemma bigpar_nat_recr  n (F : nat -> rset) (P : pred nat) :
      EqProt (\||_(0 <= i < n.+1 | P i) (F i))
                 ((\||_(0 <= i < n | P i) (F i)) ||| (if P n then F n else prot0)).
      rewrite /index_iota.
      rewrite !subn0.
      rewrite iotaS_r //= bigpar_cat //=.
      rewrite add0n.
      rewrite big_cons big_nil.
      destruct (P n).
      rewrite -eq_par0 //=.
      done.
    Qed.


    Lemma bigpar_const_prot0 {I} (xs : seq I) (P : pred I) :
    EqProt (\||_(x <- xs | P x) (prot0)) prot0.
    induction xs.
    rewrite big_nil //=.
    rewrite big_cons.
    destruct (P a).
    rewrite IHxs; rewrite -eq_par0 //=.
    done.
    Qed.

    Lemma exchange_bigpar {I} {J} (xs : seq I) (ys : seq J) (p : pred I) (q : pred J) (R : I -> J -> rset) :
    EqProt (\||_(x <- xs | p x) \||_(y <- ys | q y) (R x y))
    (\||_(y <- ys | q y) \||_(x <- xs | p x) (R x y)).
    move: ys; induction xs.
    intros; rewrite !big_nil.
    symmetry; etransitivity.
    apply Setoid.eqv_bigr.
    apply _.
    intros; rewrite big_nil //=.
    instantiate (1 := (fun=>prot0)).
    done.
    rewrite bigpar_const_prot0 //=.
    intros.
    rewrite big_cons.
    case h : (p a).
    rewrite IHxs.
    rewrite -bigpar_par.
    apply Setoid.eqv_bigr.
    apply _.
    intros; rewrite /Setoid.eqv //=.
    rewrite big_cons h //=.
    symmetry; etransitivity.
    apply Setoid.eqv_bigr.
    apply _.
    intros; rewrite big_cons h.
    rewrite /Setoid.eqv //=.
    instantiate (1 := fun i => \||_(j <- xs | p j) (R j i)).
    done.
    rewrite //=.
    rewrite IHxs.
    done.
    Qed.

Lemma bigpar_mkcond {I : eqType} (xs : seq I) (p : pred I) f :
  EqProt (\||_(x <- xs | p x) (f x)) 
             (\||_(x <- xs) (if p x then f x else prot0)).
  rewrite Setoid.big_mkcond //=.
Qed.

  Lemma bigpar_partition_nat n (p : pred nat) (q : pred nat) (f : nat -> rset) :
    EqProt (\||_(0 <= i < n | p i) f i)
               ((\||_(0 <= i < n | p i && q i) f i) ||| (\||_(0 <= i < n | p i && (~~ q i)) f i)).
    induction n.
    rewrite !big_nil -eq_par0 //=.
    rewrite !bigpar_nat_recr.
    case h : (p n); rewrite //=; last by rewrite -!eq_par0 //=.
    case h' : (q n); rewrite //= -eq_par0.
    rewrite IHn.
    rewrite -!ParAssoc.
    apply EqCong.
    done.
    apply ParSym.
    rewrite IHn.
    rewrite -!ParAssoc.
    done.
 Qed.


Lemma behead_cons_tuple {n} {A} (x : A) (xs : n.-tuple A) : behead_tuple (cons_tuple x xs) = xs.
  apply eq_tuple; done.
Qed.

  Definition Outvec {I} {t} (o : I.-tuple (chan t)) (r : 'I_I -> rxn t) :=
    \||_(j < I) Out (tnth o j) (r j).

  Lemma Outvec0 {t} (o : 0.-tuple (chan t)) r :
    Outvec o r ~= prot0.
    rewrite /Outvec big_ord0 //=.
  Qed.

  Lemma OutvecS {I} {t} (o : (I.+1).-tuple (chan t)) r :
    Outvec o r ~= (Out (thead o) (r ord0)) ||| Outvec [tuple of behead o] (fun i => r (lift ord0 i)).
    rewrite /Outvec big_ord_recl //=.
    apply EqCong.
    done.
    apply EqProt_big_r; intros.
    destruct (tupleP o); simpl.
    rewrite tnthS //=.
    rewrite tupleE //=.
    rewrite tupleE //=.
    rewrite behead_cons_tuple //=.
  Qed.

  Definition copy_tup {I} {t} (i o : I.-tuple (chan t)) :=
    Outvec o (fun j => copy (tnth i j)).

Lemma copy_tupS {I} {t} (c1 c2 : (I.+1).-tuple (chan t)) :
  copy_tup c1 c2 ~= Out (thead c2) (copy (thead c1)) ||| copy_tup [tuple of behead c1] [tuple of behead c2].
  rewrite /copy_tup.
  rewrite OutvecS.
  apply EqCong.
  done.
  apply eq_EqRefl.
  congr (_ _ _).
  simpl.
  funext => j.
  destruct (tupleP c1).
  simpl.
  rewrite tnthS.
  rewrite tupleE //=.
  rewrite behead_cons_tuple.
  done.
Qed.

Definition vec_foreach2 {I} {t1 t1' t2} (r : 'I_I -> chan t1 -> chan t1' -> rxn t2) (i : I.-tuple (chan t1)) (i' : I.-tuple (chan t1')) (o : I.-tuple (chan t2)) :=
  Outvec o (fun j =>
              r j (tnth i j) (tnth i' j)).

Lemma notin_big_ord {n} (f : 'I_n -> rset) c :
  (forall i, ~ In (f i) c) <->
  ~ In (\||_(i < n) (f i)) c.
  split; induction n.
  rewrite big_ord0 //=.
  set_tac.
  intros.
  rewrite big_ord_recl //=.
  repeat set_tac.
  set_tac.
  by destruct i.
  set_tac.
  destruct (ordP i); subst.
  rewrite big_ord_recl in H.
  repeat set_tac.
  rewrite big_ord_recl in H.
  repeat set_tac.
  apply (IHn (fun j => f (lift ord0 j))).
  done.
Qed.

Lemma notin_copy_tup {I} {t} (i o : I.-tuple (chan t)) c :
  (forall j, c <> mkChan (tnth i j) /\ c <> mkChan (tnth o j)) <->
  ~ In (copy_tup i o) c.
  split.
  rewrite /copy_tup /Outvec.
  intros.
  rewrite -notin_big_ord.
  intros.
  simpl.
  specialize (H i0).
  repeat set_tac.
  move/notin_big_ord.
  move => h j.
  specialize (h j).
  repeat set_tac.
Qed.

Lemma noOutput_big_ord {n} (f : 'I_n -> rset) c :
  (forall i, ~ outputs (f i) c) <->
  ~ outputs (\||_(i < n) (f i)) c.
  split; induction n.
  rewrite big_ord0 //=; set_tac.
  rewrite big_ord_recl //=; set_tac.
  intros.
  apply H.
  apply IHn.
  intros; apply H.
  intros.
  destruct i; done.
  rewrite big_ord_recl //=; repeat set_tac.
  destruct (ordP i); subst; auto.
  apply (IHn (fun j => f (lift ord0 j))).
  done.
Qed.

Lemma noOutput_copy_tup {I} {t} (i o : I.-tuple (chan t)) c :
  (forall j, c <> mkChan (tnth o j)) <->
  ~ outputs (copy_tup i o) c.
  split.
  rewrite /copy_tup /Outvec.
  intros.
  rewrite -noOutput_big_ord.
  intros.
  simpl.
  specialize (H i0).
  repeat set_tac.
  move/noOutput_big_ord.
  move => h j.
  specialize (h j).
  repeat set_tac.
Qed.


Lemma pars_big_replace {I : eqType} (xs : seq I) (p : pred I) f1 f2 rs :
  (forall i, i \in xs -> p i -> pars [:: f1 i & rs] ~= pars [:: f2 i & rs]) ->
  pars [:: \||_(i <- xs | p i) f1 i & rs] ~= pars [:: \||_(i <- xs | p i) f2 i & rs].
  intros.
  induction xs.
  rewrite !big_nil //=.
  rewrite !big_cons.
  case h : (p a).
  rewrite !par_in_pars.
  swap_tac 0 1; rewrite SeqOps.insert_0.
  rewrite (pars_split 1) //=.
  rewrite H.
  rewrite -pars_cat //=.
  swap_tac 0 1; rewrite SeqOps.insert_0.
  apply pars_cons_cong.
  done.
  apply IHxs.
  intros.
  apply H.
  rewrite in_cons H0 orbT //=.
  done.
  rewrite in_cons eq_refl //=.
  done.
  apply IHxs.
  intros.
  apply H.
  rewrite in_cons H0 orbT //=.
  done.
Qed.

(** Begin newvec stuff **)
(* newvec stuff *)


Fixpoint newvec (n : nat) t (f : n.-tuple (chan t) ->  rset) {struct n} : rset.
  destruct n.
  apply (f [tuple]).
  apply (New t); intro c.
  apply (newvec n t (fun tup => f [tuple of c :: tup])).
Defined.

Lemma newvecS n t f :
  newvec n.+1 t f = New t (fun c =>
                              newvec n t (fun tup => f [tuple of c :: tup])).
    done.
Qed.

Lemma newvecS_r n t f :
  newvec n.+1 t f ~= New t ( fun c =>
                              newvec n t (fun tup => f [tuple of rcons tup c])).
  induction n.
  simpl.
  apply EqNew; intros.
  apply eq_EqRefl.
  congr (_ _).
  apply eq_tuple; done.
  simpl in IHn.
  simpl.
  symmetry.
  rewrite NewNew.
  apply EqNew; intros.
  symmetry.
  move: (IHn (fun t => f [tuple of c :: t])); intro h.
  simpl in *.
  rewrite h.
  apply EqNew; intros.
  apply eq_EqRefl.
  congr (_ _ _).
  funext => tup.
  congr (_ _).
  apply eq_tuple; done.
Qed.

Lemma newvec0 t f :
  newvec 0 t f ~= f [tuple].
  rewrite /newvec //=.
Qed.
                        
Instance newlike_tup n t : NewLike (@newvec n t).
  constructor.
  - induction n.
    - rewrite //=.
    - intro; rewrite newvecS.
        rewrite newUnused.
        apply IHn.
  - intros; induction n.
    - rewrite //=.
    - rewrite !newvecS.
      rewrite newComp.
      apply EqNew; intros.
      apply IHn.
 -  intros; induction n.
    - rewrite //=.
    - rewrite !newvecS; apply EqNew; intros; apply IHn; done.
Qed.

Notation "x <- 'newvec' n @ t ;; P" := (newvec n t (fun x => P)) (at level 41, right associativity) : ipdl_scope.


Lemma New_newvec {I} {t1 t2} P :
  (x <- newvec I @ t1 ;; y <- new t2 ;; P x y) ~=
  (y <- new t2;; x <- newvec I @ t1 ;; P x y). 
  move: t2 t1 P .
  induction I; intros.
  rewrite newvec0.
  setoid_rewrite newvec0.
  done.
  rewrite newvecS.
  symmetry.
  etransitivity.
  apply EqNew; intros.
  rewrite newvecS.
  apply EqRefl.
  setoid_rewrite IHI.
  rewrite (NewNew t1 t2).
  done.
Qed.

Lemma newvec_newvec I1 I2 t1 t2 P :
  (x <- newvec I1 @ t1 ;; y <- newvec I2 @ t2 ;; P x y) ~=
  (y <- newvec I2 @ t2 ;; x <- newvec I1 @ t1 ;; P x y).
  move: t1 t2 I2 P.
  induction I1; intros.
  rewrite //=.
  rewrite newvecS.
  setoid_rewrite IHI1.
  simpl.
  rewrite (New_newvec).
  apply EqNew; intros.
  done.
Qed.

(* Eq on newvec *)

Lemma EqNew_vec {I} {t} (r1 r2 : I.-tuple (chan t) -> rset) :
  (forall (v : I.-tuple (chan t)),
      (forall i, ~ In  (x <- newvec I @ t ;; r1 x) (mkChan (tnth v i))) ->
      (forall i, ~ In  (x <- newvec I @ t ;; r2 x) (mkChan (tnth v i))) ->
      r1 v ~= r2 v) -> 
  (x <- newvec I @ t ;; r1 x) ~= (x <- newvec I @ t ;; r2 x).
  move: r1 r2.
  induction I; intros.
  apply H; by case.
  simpl.
  apply EqNew; intros.
  apply IHI.
  intros; apply H.
  intros.
  simpl; intros.
  destruct (ordP i); subst.
  rewrite tnth0.
  simpl in H0.
  apply H0.

  rewrite tnthS.
  have: (~ In (c0 <- new t ;; x <- newvec I @ t ;; r1 [tuple of c0 :: x]) (mkChan (tnth v j))).
  eapply notin_mono.
  apply H2.
  simpl; intros.
  apply x.

  simpl; intros.
  destruct (ordP i); subst.
  
  rewrite tnth0.
  simpl in H1.
  apply H1.
  rewrite tnthS.
  have: (~ In (c0 <- new t ;; x <- newvec I @ t ;; r2 [tuple of c0 :: x]) (mkChan (tnth v j))).
  eapply notin_mono.
  apply H3.
  simpl; intros.
  apply x.
Qed.

Require Import Setoid Relation_Definitions Morphisms.
Close Scope bool_scope.

Add Parametric Morphism t I : (newvec I t)
   with signature (pointwise_relation _ (EqProt)) ==> EqProt as new_rel.
  intros.
  apply EqNew_vec.
  intros.
  rewrite /pointwise_relation in H.
  done.
Qed.

Open Scope bool_scope.




(* Lifting of logic to vectors *)

Require Import Lib.SeqOps.


From AAC_tactics Require Import AAC.


Lemma pars_big_fold {n} {t1 t2} (o : n.-tuple (chan t2)) (ri : 'I_n -> rxn t1) (ro : 'I_n -> t1 -> rxn t2) rs :
  c <- newvec n @ t1 ;;
  pars [::
          Outvec o (fun j => x <-- Read (tnth c j) ;; ro j x),
        Outvec c ri &
          rs ] ~= 
  pars [::
          Outvec o (fun j => x <-- ri j ;; ro j x)  & rs].
  induction n.
  rewrite //=.
  rewrite !Outvec0.
  rewrite pars_prot0 //=.
  simpl.
  rewrite -New_newvec.
  symmetry.
  rewrite OutvecS.
  rewrite par_in_pars.
  rewrite pars_cons.
  rewrite -IHn.
  rewrite newComp_r.
  apply EqNew_vec => c _ _.
  rewrite -RFold.
  rewrite NewComp.
  apply EqNew => c0 _ _.
  rewrite !OutvecS.
  rewrite !tnth0.
  simpl.
  rewrite theadE !tupleE.
  rewrite -pars_cons.
  rewrite !par_in_pars.
  symmetry; swap_tac 0 2.
  rewrite !par_in_pars.
  apply pars_cons_cong; rewrite //=.
  rewrite insert_0 //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  rewrite insert_0.
  apply pars_cons_cong; rewrite //=.
  apply eq_EqRefl; congr (_ _ _).
  funext => j.
  rewrite tnthS //=.
  apply eq_EqRefl; congr (_ _).
  congr (_ :: _).
  congr (_ _ _).
  rewrite tupleE //= behead_cons_tuple //=.
Qed.

Lemma pars_big_tr_general {n1 n2 n3} {t1 t2 t3} (a : n1.-tuple (chan t1)) (b : n2.-tuple (chan t2)) (r1 : 'I_n1 -> rxn t1) (r2 : 'I_n2 -> rxn t2) (m : n3.-tuple (chan t3)) f f' rs :
  (forall j, In (rxn_inputs (r1 j)) (mkChan (tnth m (f j)))) ->
  (forall j, In (rxn_inputs (r2 j)) (mkChan (tnth a (f' j)))) ->
  (forall j, wfRxn (r2 j)) ->
  pars [::
          Outvec a r1,
       Outvec b r2 & rs] ~=
  pars [::
          Outvec a r1,
          Outvec b (fun j => _ <-- Read (tnth m (f (f' j))) ;; r2 j) & rs].
  intros.
  swap_tac 0 1; rewrite insert_0 //=.
  symmetry; 
  swap_tac 0 1; rewrite insert_0 //=.
  apply pars_big_replace => j.
  rewrite /Outvec.
  rewrite (bigpar_D1_ord (f' j)).
  swap_tac 0 1; rewrite insert_0 par_in_pars //=.
  symmetry.
  swap_tac 0 1; rewrite insert_0 par_in_pars //=.
  symmetry.

  swap_tac 1 2; rewrite insert_0.
  rewrite -pars_tr //=.
  swap_tac 1 2; rewrite insert_0.
  done.
  done.
Qed.

Lemma pars_big_tr {n} {t1 t2 t3} (a : n.-tuple (chan t1)) (b : n.-tuple (chan t2)) (r1 : 'I_n -> rxn t1) (r2 : 'I_n -> rxn t2) (m : n.-tuple (chan t3)) rs :
  (forall j, In (rxn_inputs (r1 j)) (mkChan (tnth m (j)))) ->
  (forall j, In (rxn_inputs (r2 j)) (mkChan (tnth a (j)))) ->
  (forall j, wfRxn (r2 j)) ->
  pars [::
          Outvec a r1,
       Outvec b r2 & rs] ~=
  pars [::
          Outvec a r1,
          Outvec b (fun j => _ <-- Read (tnth m j) ;; r2 j) & rs].
  intros.
  change (
      pars ( [:: Outvec a r1, Outvec b r2 & rs]) ~=
      pars ([:: Outvec a r1, Outvec b (fun j : 'I_n => _ <-- Read (tnth m (id (id j)));; r2 j)
          & rs] )).
  apply pars_big_tr_general.
  done.
  done.
  done.
Qed.

Lemma big_remove {I} {t} r (P : rset) :
  (forall j x, In (rxn_inputs (r j)) x -> In P x) ->
  (x <- newvec I @ t ;; \||_(j < I) Out (tnth x j) (r j)) ||| P ~= P.
  intros.
  induction I.
  rewrite //= big_ord0 -eq_0par //=.
  simpl.
  etransitivity.
  apply EqCong.
  apply EqNew; intros.
  apply EqNew_vec; intros.
  rewrite big_ord_recl.
  rewrite tnth0.
  apply EqCong.
  done.
  apply EqProt_big_r; intros.
  rewrite tnthS.
  apply EqRefl.
  done.
  simpl.
  setoid_rewrite <- newComp_r.
  setoid_rewrite newComp.
  setoid_rewrite <- ParAssoc.
  rewrite RRemove.
  apply IHI.
  intros; eapply H.
  apply H0.
  simpl.
  intros; right.
  eapply H.
  apply H0.
  apply _.
Qed.


Lemma pars_big_remove {I} {t} r rs :
  (forall j x, In (rxn_inputs (r j)) x -> In (pars rs) x) ->
  (x <- newvec I @ t ;; pars [:: \||_(j < I) Out (tnth x j) (r j) & rs ]) ~= pars rs.
  intros.
  setoid_rewrite pars_cons.
  rewrite -newComp.
  rewrite big_remove.
  done.
  done.
Qed.

Lemma pars_big_undep {n1 n2} {t1 t2} (a : n1.-tuple (chan t1)) (b : n2.-tuple (chan t2)) (r1 : 'I_n1 -> rxn t1) (r2 : 'I_n2 -> rxn t2) f rs :
  (forall j, List.Forall (In (rxn_inputs (r2 j))) (rxn_inputs (r1 (f j)))) -> 
  pars [::
          Outvec b (fun j => _ <-- Read (tnth a (f j)) ;; r2 j),
          Outvec a r1 &
          rs] ~=
  pars [::
          Outvec b r2,
          Outvec a r1 &
          rs].
    intros.
    apply pars_big_replace.
    intros.
    rewrite /Outvec.
    rewrite (bigpar_D1_ord (f i)) //=.
    swap_tac 0 1; rewrite insert_0 par_in_pars.
    swap_tac 0 2; rewrite insert_0.
    swap_tac 1 2; rewrite insert_0.
    rewrite pars_undep //=.
    symmetry.
    swap_tac 0 1; rewrite insert_0 par_in_pars.
    swap_tac 0 2; rewrite insert_0.
    swap_tac 1 2; rewrite insert_0.
    done.
Qed.

Lemma pars_undep_from_big {n} {t t'}
      (b : chan t') (c : n.-tuple (chan t)) (k : rxn t') (r : 'I_n -> rxn t) i rs :
  List.Forall [eta In (rxn_inputs k)] (rxn_inputs (r i)) ->
  pars [::
          Out b (_ <-- Read (tnth c i) ;; k),
          Outvec c r & rs] ~=
  pars [::
          Out b (k),
          Outvec c r & rs]. 
    intros.
    rewrite !pars_cons.
    rewrite !ParAssoc.
    apply EqCong.
    unfold Outvec.
    rewrite {1}(bigpar_D1_ord i).
    rewrite ParAssoc.
    rewrite (ParSym (Out b _)).
    rewrite RUndep.
    rewrite (ParSym _ (Out b _)).
    rewrite -ParAssoc.
    rewrite -(bigpar_D1_ord i).
    done.
    done.
    done.
    done.
    done.
Qed.

Lemma pars_big_subst {I1 I2} {t1 t2} (a : I1.-tuple (chan t1)) (b : I2.-tuple (chan t2)) (r1 : 'I_I1 -> rxn t1) (k : 'I_I2 -> t1 -> rxn t2) f rs :
  (forall j, isDet _ (r1 j)) ->
  pars [::
          Outvec a r1,
        Outvec b (fun j => x <-- Read (tnth a (f j)) ;; k j x) &
        rs ]
  ~=
     pars [::
          Outvec a r1,
        Outvec b (fun j => x <-- r1 (f j);; _ <-- Read (tnth a (f j)) ;; k j x) &
        rs ].
  intros.
  swap_tac 0 1; rewrite insert_0.
  symmetry; swap_tac 0 1; rewrite insert_0.
  apply pars_big_replace; intros.
  rewrite /Outvec.
  rewrite (bigpar_D1_ord (f i)).
  swap_tac 0 1; rewrite insert_0 par_in_pars.
  swap_tac 0 2; rewrite insert_0.
  swap_tac 1 2; rewrite insert_0.
  rewrite -pars_subst.
  symmetry.
  swap_tac 0 1; rewrite insert_0 par_in_pars.
  swap_tac 0 2; rewrite insert_0.
  swap_tac 1 2; rewrite insert_0.
  done.
  done.
  done.
Qed.


Lemma pars_big_inline {n1 n2} {t t'} (b : n1.-tuple (chan t'))
      (c : n2.-tuple (chan t)) (k : 'I_n1 -> t -> rxn t')
      (r : 'I_n2 -> rxn t) f rs :
  (forall j, isDet _ (r j)) ->
  pars [::
          Outvec b (fun j => x <-- Read (tnth c (f j)) ;; k j x),
        Outvec c r & rs]
  ~=     
  pars [::
          Outvec b (fun j => x <-- r (f j) ;; k j x),
        Outvec c r & rs].
  intros.
    swap_tac 0 1.
    rewrite insert_0.
    rewrite pars_big_subst; last by done.
    etransitivity.
    apply pars_cons_cong.
    done.
    apply pars_cons_cong.
    apply EqProt_big_r; intros.
    rewrite EqBindC.
    apply EqRefl.
    done.
    simpl.
    swap_tac 0 1.
    rewrite insert_0.
    rewrite pars_big_undep.
    done.
    intros.
    simpl.
    apply List.Forall_forall; intros.
    rewrite /In.
    apply in_app_union.
    left.
    apply in_listP.
    done.
 Qed.

Lemma pars_big_inline_from_single {n} {t t'}
      (b : n.-tuple (chan t'))
      (c : chan t) (k : 'I_n -> t -> rxn t') (r : rxn t) rs :
  isDet _ r ->
  pars [::
          Outvec b (fun j => x <-- Read c ;; k j x),
        Out c r & rs]
  ~=     
  pars [::
          Outvec b (fun j => x <-- r ;; k j x),
        Out c r & rs].
    intros.
    induction n.
    rewrite !Outvec0 //=.
    rewrite !OutvecS !par_in_pars.
    swap_tac 1 2.
    rewrite insert_0.
    rewrite pars_inline.
    apply pars_cons_cong.
    done.
    swap_tac 0 1.
    rewrite insert_0.
    apply IHn.
    done.
Qed.

Lemma pars_inline_from_big {n} {t t'}
      (b : chan t') (c : n.-tuple (chan t)) (p : pred 'I_n) (k : t -> rxn t') (r : 'I_n -> rxn t) i rs :
  isDet _ (r i) ->
  p i ->
  pars [::
          Out b (x <-- Read (tnth c i) ;; k x),
          \||_(i < n | p i) (Out (tnth c i) (r i)) & rs] ~=
  pars [::
          Out b (x <-- r i ;; k x),
          \||_(i < n | p i) (Out (tnth c i) (r i)) & rs].
    intros.
    rewrite !pars_cons.
    rewrite !ParAssoc.
    apply EqCong.
    unfold Outvec.
    rewrite (bigpar_D1_ord i).
    rewrite ParAssoc.
    rewrite inline.
    rewrite -ParAssoc.
    rewrite -(bigpar_D1_ord i).
    done.
    done.
    done.
    done.
    done.
Qed.

Lemma pars_tr_from_big {n} {t1 t2 t3} (m : chan t3) (a : chan t1) (b : n.-tuple (chan t2))
      (r1 : rxn t1) (r2 : 'I_n -> rxn t2) (j : 'I_n) rs (p : pred _) :
  p j ->
  In (rxn_inputs r1) (mkChan (tnth b j)) ->
  In (rxn_inputs (r2 j)) (mkChan m) ->
  wfRxn r1 ->
  pars [:: Out a r1, \||_(i < n | p i) (Out (tnth b i) (r2 i)) & rs] ~=
  pars [:: Out a (_ <-- Read m ;; r1), \||_(i < n | p i) (Out (tnth b i) (r2 i)) & rs].                                           
  intros.
  rewrite !pars_cons.
  rewrite !ParAssoc.
  apply EqCong.
  unfold Outvec.
    rewrite (bigpar_D1_ord j).
    rewrite ParAssoc.
    rewrite (ParSym (Out a _)).
    rewrite RTr.
    rewrite (ParSym _ (Out a _)).
    rewrite -ParAssoc.
    rewrite -(bigpar_D1_ord j).
    done.
    done.
    done.
    done.
    done.
    done.
    done.
Qed.
  


Lemma bigpar_ord_recr {n} f :
  \||_(j < n.+1) (f j) ~= (f ord_max) ||| \||_(j < n) f (widen_ord (leqnSn n) j).
    transitivity (\big[Par/prot0]_(0 <= i < n.+1) f (inord i)).
        rewrite big_mkord.
        apply EqProt_big_r; intros.
        rewrite inord_val //=.

    rewrite bigpar_nat_recr //=.
    rewrite ParSym.
    apply EqCong.
    have -> : inord n = (@ord_max n).
    apply/eqP; rewrite eqE //=.
    rewrite inordK //=.
    done.

    rewrite big_mkord.
    apply EqProt_big_r; intros.
    have <- : inord x = widen_ord (leqnSn n) x.
    apply/eqP; rewrite eqE //=.
    rewrite inordK //=.
    destruct x.
    simpl.
    apply leqW; done.
    done.
Qed.

Definition tup_disj {I1 I2} {t1 t2} (x : I1.-tuple (chan t1)) (y : I2.-tuple (chan t2)) := forall i j, mkChan (tnth x i) <> mkChan (tnth y j).


Lemma inputsOn_big_ord n (r : 'I_n -> rset) c i :
  inputs (r i) c ->
  inputs (\||_(j < n) (r j)) c.
  induction n.
  rewrite big_ord0 //=.
  destruct i; done.
  rewrite big_ord_recl //=; intros.
  destruct (ordP i); subst.
  left; done.
  right; eapply IHn.
  apply H.
Qed.

Lemma in_big_ord n (r : 'I_n -> rset) c i :
  In(r i) c ->
  In (\||_(j < n) (r j)) c.
  induction n.
  rewrite big_ord0 //=.
  destruct i; done.
  rewrite big_ord_recl //=; intros.
  destruct (ordP i); subst.
  left; done.
  right; eapply IHn.
  apply H.
Qed.

Lemma in_big_ord_cond n (r : 'I_n -> rset) c i (p : pred 'I_n) :
  p i -> 
  In (r i) c ->
  In (\||_(j < n | p i) (r j)) c.
  intros.
  eapply In_big.
  apply H.
  apply H0.
  apply mem_index_enum.
Qed.

Require Import Lia.

Ltac ssr_lia :=
  repeat match goal with
  | [ H : is_true (_ < _) |- _ ] => move/ltP: H => H
  | [ H : is_true (_ <= _) |- _ ] => move/leP: H => H
  | [ H : is_true (_ == _) |- _ ] => move/eqP: H => H
  | [ H : is_true (_ != _) |- _ ] => move/eqP: H => H

  | [ |- is_true (_ < _) ] => apply/ltP
  | [ |- is_true (_ <= _) ] => apply/leP
  | [ |- is_true (_ == _) ] => apply/eqP
  | [ |- is_true (_ != _) ] => apply/eqP
  end.

Lemma bigpar_ord_recl_D1 {n} (f : 'I_(n.+1) -> rset) :
  \||_(j < n) f (lift ord0 j) ~= \||_(j < n.+1 | j != ord0) f j.
  symmetry.
  rewrite bigpar_mkcond.
  simpl.
  rewrite big_ord_recl.
  simpl.
  rewrite -eq_0par //=.
Qed.

Lemma bigpar_ord_recl_cond {n} f p  :
  \||_(i < n.+1 | p i) f i ~= (if p ord0 then f ord0 else prot0) ||| \||_(i < n | p (lift ord0 i)) f (lift ord0 i).
  rewrite bigpar_mkcond.
  rewrite big_ord_recl.
  rewrite -bigpar_mkcond.
  done.
Qed.

Lemma bigpar_ord_recr_cond {n} f p  :
  \||_(i < n.+1 | p i) f i ~= (if p ord_max then f ord_max else prot0) ||| \||_(i < n | p (widen_ord (leqnSn n) i)) f (widen_ord (leqnSn n) i).
  rewrite bigpar_mkcond.
  rewrite bigpar_ord_recr.
  simpl.
  rewrite -bigpar_mkcond.
  done.
Qed.

Lemma bigpar_ord_lt_Sr {n} j (h : j < n) f :
  \||_(i < n | i < j.+1) f i ~= (\||_(i < n | i < j) f i) ||| f (Ordinal h).
  rewrite big_ord_narrow //=.
  rewrite big_ord_narrow //=.
  ssr_lia; lia.
  intros.
  rewrite bigpar_ord_recr.
  rewrite -pars2.
  rewrite -pars2.
  swap_tac 0 1.
  apply pars_cons_cong.
  apply EqProt_big.
  done.
  intros.
  apply eq_EqRefl.
  congr (_ _).
  apply/eqP; rewrite eqE //=.
  apply pars_cons_cong.
  apply eq_EqRefl.
  congr (_ _).
  apply/eqP; rewrite eqE //=.
  done.
Qed.


Lemma bigpar_ord_lt_Sl {n} k (h : k.+1 < n) f :
  \||_(i < n | k < i) f i ~= f (Ordinal h) ||| \||_(i < n | k.+1 < i) f i.
  rewrite bigpar_D1_ord.
  apply EqCong.
  reflexivity.
  apply EqProt_big.
  rewrite //=.
  move => x Hx; rewrite /in_mem //=.
  apply Bool.eq_true_iff_eq; split.
  move/andP; elim => h1 h2.
  rewrite eqE //= in h2.
  have -> //= : k.+1 < x.
  ssr_lia; lia.
  intros.
  have H2: k.+1 < x by done .
  apply/andP; split.
  ssr_lia; lia.
  rewrite eqE //=.
  ssr_lia; lia.
  done.
  simpl.
  done.
Qed.

Lemma bool_iffP (b1 b2 : bool) :
  b1 <-> b2 -> b1 = b2.
  intros.
  destruct b1; destruct b2; intuition.
Qed.

Lemma pars_big_hybrid {n} (f1 f2 : 'I_n -> rset) (rs : seq rset) :
  (forall (k : 'I_n),
      pars [:: \||_(i < n | i < k) f2 i, f1 k, \||_(i < n | k < i) f1 i & rs] ~=
      pars [:: \||_(i < n | i < k) f2 i, f2 k, \||_(i < n | k < i) f1 i & rs]) -> 
  pars [:: (\||_(i < n) f1 i) & rs] ~= pars [:: \||_(i < n) f2 i & rs].
  intros.
  have h:
    forall (k : 'I_n),
      pars [:: \||_(i < n) f1 i & rs] ~=
      pars [:: \||_(i < n | i < k) f2 i,  f1 k, \||_(i < n | k < i) f1 i & rs].                                       
    intros.
    destruct k as [k Hk].
    simpl.
    induction k.
    symmetry.
    rewrite big_pred0 //= pars_prot0.
    rewrite -par_in_pars; apply pars_cons_cong.
    symmetry; rewrite bigpar_D1_ord.
    apply EqCong.
    done.
    apply EqProt_big.
    move => [x Hx] _ //=; rewrite /in_mem //= eqE //=.
    apply bool_iffP; split; intro; ssr_lia; lia.
    done.
    done.
    done.
    have Hk0 : k < n by ssr_lia; lia.
    rewrite (IHk Hk0).
    rewrite bigpar_ord_lt_Sr par_in_pars.
    instantiate (1 := Hk0).
    rewrite (H (Ordinal Hk0)).
    simpl.
    apply pars_cons_cong.
    done.
    apply pars_cons_cong.
    done.
    rewrite !pars_cons.
    rewrite ParAssoc.
    apply EqCong; last by done.
    apply bigpar_ord_lt_Sl.

  destruct n.
  rewrite !big_ord0 //=.
  rewrite (h ord_max).
  rewrite H.
  rewrite -par_in_pars.
  apply pars_cons_cong.
  symmetry.
  rewrite bigpar_D1_ord.
  rewrite ParSym.
  apply EqCong; last first.
  reflexivity.
  apply EqProt_big.
  rewrite //= => x Hx; rewrite /in_mem //=.
  clear Hx.
  destruct x as [x Hx].
  rewrite eqE //=.
  apply bool_iffP; split; intros; ssr_lia; lia.
  done.
  done.
  rewrite big_pred0 //=.
  rewrite pars_prot0 //=.
  move => i; apply bool_iffP.
  destruct i as [i Hi].
  simpl; split.
  intros.
  ssr_lia.
  lia.
  done.
Qed.

Lemma pars_big_hybrid2 {n} (f1 f2 : 'I_n -> rset) (rs : seq rset) :
  (forall (k : 'I_n),
      pars [:: \||_(i < n | i < k) f1 i & rs] ~=
      pars [:: \||_(i < n | i < k) f2 i & rs]  ->
      pars [:: \||_(i < n | i < k) f1 i, f1 k & rs] ~=
      pars [:: \||_(i < n | i < k) f1 i, f2 k & rs]) ->
  pars [:: (\||_(i < n) f1 i) & rs] ~= pars [:: \||_(i < n) f2 i & rs].
  intros.
  have h :
    forall (k : 'I_(n.+1)) ,
      pars [:: \||_(i < n | i < k) f1 i & rs] ~=
      pars [:: \||_(i < n | i < k) f2 i & rs].
  intros.
  destruct k as [k Hk].
  simpl.
  induction k.
  rewrite !big_pred0 //=.
  have Hk0: k < n by ssr_lia; lia.
  rewrite bigpar_ord_lt_Sr par_in_pars //=.
  instantiate (1 := Hk0).
  rewrite (H (Ordinal Hk0)).
  simpl.
  swap_tac 0 1; rewrite insert_0.
  rewrite (pars_split 1); simpl.
  rewrite IHk.
  rewrite -pars_cat //=.
  swap_tac 0 1; rewrite insert_0.
  rewrite bigpar_ord_lt_Sr par_in_pars //=.
  ssr_lia; lia.
  simpl.
  apply IHk.
  ssr_lia; lia.

  have -> : \||_(i < n) f1 i ~= \||_(i < n | i < n) f1 i.
      apply EqProt_big.
      move => x //= _; apply bool_iffP; split; rewrite /in_mem //=.
      done.
  rewrite (h ord_max).
  apply pars_cons_cong.
      apply EqProt_big.
      move => x //= _; apply bool_iffP; split; rewrite /in_mem //=.
      done.
  done.
Qed.

Lemma bigpar_new {n} {t} (f : 'I_n -> chan t -> rset) :
  \||_(i < n) (x <- new t ;; f i x) ~= 
  x <- newvec n @ t ;; \||_(i < n) (f i (tnth x i)).
  induction n.
  rewrite //= !big_ord0 //=.
  rewrite big_ord_recl.
  rewrite newvecS.
  rewrite newComp.
  apply EqNew => c _ _.
  rewrite IHn.
  rewrite newComp_r.
  apply EqNew_vec => v _ _.
  rewrite big_ord_recl.
  apply EqCong.
  rewrite tnth0 //=.
  apply EqProt_big_r; intros.
  rewrite tnthS //=.
Qed.

Lemma bigpar_prot0 {n} : \||_(i < n) prot0 ~= prot0.
  induction n.
  rewrite big_ord0 //=.
  rewrite big_ord_recl.
  rewrite IHn.
  rewrite -eq_par0 //=.
Qed.


Lemma big_pars2 n r1 r2 :
  \||_(i < n) pars [:: r1 i; r2 i] ~= pars [:: \||_(i < n) r1 i; \||_(i < n) r2 i].
  rewrite !bigpar_par.
  rewrite bigpar_prot0 -eq_par0.
  rewrite !pars_cons //= -eq_par0.
  done.
Qed.

(* TODO: unify with above *)

Lemma big_remove_cond {I} {t} r (p : pred 'I_I) (P : rset) :
  (forall j x, p j -> In (rxn_inputs (r j)) x -> In P x) ->
  (x <- newvec I @ t ;; \||_(j < I | p j) Out (tnth x j) (r j)) ||| P ~= P.
  intros.
  induction I.
  rewrite //= big_ord0 -eq_0par //=.
  simpl.
  etransitivity.
  apply EqCong.
  apply EqNew; intros.
  apply EqNew_vec; intros.
  rewrite bigpar_ord_recl_cond.
  rewrite tnth0.
  apply EqCong.
  done.
  apply EqProt_big_r; intros.
  rewrite tnthS.
  apply EqRefl.
  done.
  simpl.
  setoid_rewrite <- newComp_r.
  setoid_rewrite newComp.
  setoid_rewrite <- ParAssoc.
  case h : (p ord0).
  rewrite RRemove.
  apply IHI.
  intros; eapply H.
  apply H0.
  done.
  simpl.
  intros; right.
  eapply H.
  apply h.
  done.
  rewrite NewUnused.
  rewrite -eq_0par.
  rewrite IHI.
  done.
  intros.
  eapply H.
  apply H0.
  done.
  apply _.
Qed.

Lemma pars_big_remove_cond {I} {t} (p : pred 'I_I)  r rs :
  (forall j x, p j -> In (rxn_inputs (r j)) x -> In (pars rs) x) ->
  (x <- newvec I @ t ;; pars [:: \||_(j < I | p j) Out (tnth x j) (r j) & rs ]) ~= pars rs.
  intros.
  setoid_rewrite pars_cons.
  rewrite -newComp.
  rewrite big_remove_cond.
  done.
  done.
Qed.
