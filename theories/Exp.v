(* This file formalizes:
   - Channels in IPDL
   - Rections in IPDL, including reaction equivalence *) 

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path bigop fintype matrix.
Require Import FunctionalExtensionality Classes.Equivalence.
Require Import Lib.Perm Lib.Dist Lib.Base.
Require Import Lib.TupleLems Lib.Set.


Section RxnDef.
  Context {chan : Type -> Type}.
  
  Inductive rxn : Type -> Type :=
  | Samp {t} : Dist t -> rxn t
  | Ret {t} : t -> rxn t
  | Read {t} (c : chan t) : rxn t
  | Bind {t1 t2} : rxn t1 -> (t1 -> rxn t2) -> rxn t2.
  
(* Deterministic channels do not sample from distributions. *)
Fixpoint isDet n (r : rxn n) : Prop :=
  match r with
    | Samp _ _ => False 
    | Read _ _ => True
    | Ret _ _ => True 
    | Bind _ _ c k => isDet _ c /\ forall x, isDet _ (k x) end.

Arguments Samp [t].
Arguments Ret [t].
Arguments Bind [t1 t2].

Notation "x <-- c ;; k" := (Bind c (fun x => k)) (at level 41, right associativity).

(* (Exact) equality of reactions. Of particular interest:
  - EqBindC says that the bind operation on reactions is commutative.
 - EqSampBijection says that the reacting sampling from a distribution is equivalent to the one that samples from the distribution, and applies a bijection to it. The hypothesis only requires the function is injective, but this is enough, since we assume the type is finite.
 - EqSampBind says that sampling from a monadic bind on distributions is the same as lifting the bind to reactions.
 - EqSampRet says that sampling from the point mass distribution is the same as returning the value. 
 *)
Inductive EqRxn : forall A, rxn A -> rxn A ->  Prop := 
  | EqReadSame {n} {m} (c : chan n) (k : n -> n -> rxn m) :
      EqRxn _ (@Bind _ _ (Read c) (fun x => @Bind _ _ (Read c) (fun y => k x y)))
            (@Bind _ _ (Read c) (fun x => k x x))
  | EqSampUnused n (d : Dist n) m (k : rxn m) :
      EqRxn _ (Bind (Samp d) (fun _ => k)) k
  | EqRxnRefl n (r : rxn n) : EqRxn _ r r
  | EqRxnSym n (r1 : rxn n) (r2 : rxn n) : EqRxn _ r1 r2 -> EqRxn _ r2 r1
  | EqRxnTr n (r1 : rxn n) (r2 : rxn n) (r3 : rxn n) : EqRxn _ r1 r2 -> EqRxn _ r2 r3 -> EqRxn _ r1 r3
  | EqRetBind n m (x : n) (k : n -> rxn m) :
      EqRxn _ (Bind (Ret x) k) (k x)
  | EqBindRet n (r : rxn n) :
      EqRxn _ (Bind r (@Ret n)) r
  | EqBindC n1 n2 n3  (r : rxn n1) (r' : rxn n2) (k : n1 -> n2 -> rxn n3) :
      EqRxn _ (Bind r (fun x => Bind r' (fun y => k x y)))
            (Bind r' (fun y => Bind r (fun x => k x y)))
  | EqBindA n1 n2 n3 (r : rxn n1) (r' : n1 -> rxn n2) (r'' : n2 -> rxn n3) :
      EqRxn _ (Bind (Bind r r') r'')
            (Bind r (fun x => Bind (r' x) r''))
  | EqRxnBind n1 n2 (r1 : rxn n1) (r2 : rxn n1) (k1 : n1 -> rxn n2) (k2 : n1 -> rxn n2) :
      EqRxn _ r1 r2 ->
      (forall x, EqRxn _ (k1 x) (k2 x)) ->
      EqRxn _ (Bind r1 k1) (Bind r2 k2)
  | EqSampBijection {A : finType} (d : Dist A) (f : A -> A) :
      injective f ->
      uniform d ->
      EqRxn _ (Samp d) (Bind (Samp d) (fun x => Ret (f x)))
| EqSampBind {t1 t2} (d : Dist t1) (f : t1 -> Dist t2) :
    EqRxn _ (Samp (dbind d f)) (x <-- Samp d ;; Samp (f x))
| EqSampRet {t} (x : t) :
    EqRxn _ (Samp (DRet x)) (Ret x)
.

Infix "=r" := (@EqRxn _) (at level 40).

Lemma EqBind_r {n m} (r : rxn n) (k1 k2 : n -> rxn m) :
  (forall x, k1 x =r k2 x) ->
  Bind r k1 =r Bind r k2.
  intros; apply EqRxnBind.
  apply EqRxnRefl.
  done.
Qed.

Lemma EqBind_l {n m}  (r1 r2 : rxn n) (k : n -> rxn m) :
  r1 =r r2 ->
  Bind r1 k =r Bind r2 k.
  intros ; apply EqRxnBind.
  done.
  intro.
  apply EqRxnRefl.
Qed.



End RxnDef.

Require Import Setoid Relation_Definitions Morphisms.
Close Scope bool_scope.

Add Parametric Relation {C} n : (@rxn C n) (@EqRxn C n)
                                    reflexivity proved by (@EqRxnRefl _ _)
                                    symmetry proved by (@EqRxnSym _ _ )
                                    transitivity proved by (@EqRxnTr _ _) as rxn_rel.

Add Parametric Morphism  {C} n m : (@Bind _ n m)
    with signature (@EqRxn C n) ==> pointwise_relation _ (@EqRxn _ m) ==> (@EqRxn _ m) as bind_mor2.
  intros; apply EqRxnBind.
  apply H.
  done.
Qed.

Notation "x <-- c ;; k" := (Bind c (fun x => k)) (at level 41, right associativity).

Infix "=r" := (@EqRxn _ _) (at level 40).

  
Require Import Lib.TupleLems.


(** Tactics for reactions **)

(* This tactic simplifies the left hand side of a reaction equivalence. *)
Ltac simp_rxn :=
  etransitivity; [repeat lazymatch goal with
    | [ |- EqRxn _ (Bind (Read _) (fun x => Ret x)) _ ] => idtac (* Refuse to simplify bare copy *)
    | [ |- EqRxn _ (Bind (Samp _) (fun x => Ret x)) _ ] => idtac (* Refuse to simplify bare samp *)
    | [ |- EqRxn _ (Bind (Bind _ _) _) _ ] => etransitivity; [apply EqBindA |]
    | [ |- EqRxn _ (Bind _ (fun qqq => Ret qqq)) _ ] => etransitivity; [apply EqBindRet|]
    | [ |- EqRxn _ (Bind (Ret _) _) _ ] => etransitivity; [apply EqRetBind |]
    | [ |- EqRxn _ (Bind _ _) _ ] => apply EqBind_r; intro
    | [ |- EqRxn _ (Read _) _ ] => apply EqRxnRefl
    | [ |- EqRxn _ (Ret _) _ ] => apply EqRxnRefl    
   end; apply EqRxnRefl | ].

Lemma EqRxnRet {C} {n} (x y : n) : 
  x = y -> (@Ret C _ x) =r (Ret y).
  move => ->; reflexivity.
Qed.

Ltac r_move_up m :=
  lazymatch eval simpl in m with
    | 0 => idtac 
    | S 0 => apply EqBindC; rewrite /=
    | S (S ?m') =>
      apply EqBind_r; intro; r_move_up (S m')
                                     end; rewrite //=.

Ltac r_move_to_front m :=
  lazymatch eval simpl in m with
    | 0 => idtac 
    | S 0 => etransitivity; [ r_move_up (S 0) |] ; rewrite /=
    | S (S ?m') => etransitivity; [ r_move_up (S (S m')) | rewrite /=; r_move_to_front (S m') ] end.

(* Swaps position n with m (if possible). Assumes m is larger than m. Works on left hand side. *)
Ltac r_swap n m :=
  lazymatch eval simpl in n with
    | 0 => r_move_to_front m
    | S ?n' => 
      etransitivity; [ apply EqBind_r; intro; r_swap n' (m.-1); apply EqRxnRefl | ] end.


Ltac r_combine n m :=
  r_swap 0 n;
  r_swap 1 m;
  rewrite //= EqReadSame.


Lemma EqBindSame {C} {n m} (r : @rxn C m) (k : m -> m -> rxn n) :
  isDet _ r ->
  (x <-- r ;; 
   y <-- r ;;
   k x y) =r (x <-- r ;; k x x).
  induction r.
  simpl.
  intros.
  done.
  intros; rewrite !EqRetBind; reflexivity.
  intros.
  rewrite EqReadSame; reflexivity.
  simpl; case => h1 h2.
  simp_rxn.
  symmetry; simp_rxn; symmetry.
  rewrite -EqBindA.
  rewrite EqBindC.
  simp_rxn.
  rewrite IHr.
  apply EqBind_r => x.
  rewrite H.
  reflexivity.
  done.
  done.
Qed.

Definition tagged {chan : Type -> Type} :=
  {t : Type & chan t}.

Definition tag {chan : Type -> Type} {t} (c : chan t) : tagged :=
  existT chan t c.
  

(* Reaction r always reads from channel c. *)
Fixpoint reads_from {chan} {t1 t2} (c : chan t1) (r : @rxn chan t2) :=
  match r with
    | Samp _ _ => False
    | Ret _ _ => False
    | Read _ c' => tag c = tag c'
    | Bind _ _ r' k => 
      reads_from c r' \/ (forall x, reads_from c (k x)) end.

Require Import Program.

(* If r reads from c, then you can remove a superflous read from c. *) 
Lemma remove_read {chan} {t1 t2} (c : chan t1) (r : @rxn chan t2) :
  reads_from c r ->
  (_ <-- Read c ;; r) =r r.
  induction r; rewrite //=.
  intro h.
  dependent destruction h.
  etransitivity.
  apply EqBind_r; intro.
  symmetry; apply EqBindRet.
  rewrite EqReadSame.
  rewrite EqBindRet //=.
  apply EqRxnRefl.
  intro.
  destruct H0.
  etransitivity.
  rewrite -EqBindA.
  apply EqBind_r.
  intro; apply EqRxnRefl.
  apply EqRxnBind.
  apply IHr; done.
  intro; apply EqRxnRefl.
  symmetry; etransitivity.
  apply EqBind_r; intro.
  symmetry; apply H; done.
  rewrite EqBindC.
  apply EqRxnRefl.
Qed.

(* Reaction r might read from channel c. *)
Fixpoint can_read {chan} {t1 t2} (c : chan t1) (r : @rxn chan t2) :=
  match r with
    | Samp _ _ => False
    | Ret _ _ => False
    | Read _ c' => tag c = tag c'
    | Bind _ _ r' k => 
      can_read c r' \/ (exists x, can_read c (k x)) end.

(* You can remove an unused bind if all the reads are preserved. *)
Lemma remove_bind {chan} {t1 t2} (r : @rxn chan t1) (r' : rxn t2) :
  (forall t (c : chan t), can_read c r -> reads_from c r') ->
  (_ <-- r ;; r') =r r'.
  move: r'; induction r; intros.
  rewrite EqSampUnused; apply EqRxnRefl.
  rewrite EqRetBind; apply EqRxnRefl.
  apply remove_read.
  simpl in H.
  apply H; done.
  simpl in *.
  rewrite EqBindA.
  etransitivity.
  apply EqBind_r; intro.
  apply H.
  intros; apply H0.
  right; exists x; done.
  apply IHr; intros.
  apply H0; left; done.
Qed.

Lemma EqBind_r_samp_bijection {c} (t : finType) t2 (d : Dist t) (k : t -> @rxn c t2) (f : t -> t) :
  uniform d -> 
  injective f ->
  (x <-- Samp d ;; k x) =r (x <-- Samp d ;; k (f x)).
  intros.
  etransitivity.
  apply EqRxnBind.
  apply EqSampBijection.
  apply H0.
  done.
  intros; apply EqRxnRefl.
  simp_rxn.
  apply EqRxnRefl.
Qed.
