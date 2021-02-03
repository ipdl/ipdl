
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path bigop fintype matrix.
Require Import FunctionalExtensionality Classes.Equivalence.
Require Import Lib.Perm Lib.Dist Lib.Base.
Require Import Lib.TupleLems Lib.Set.

Inductive type :=
  | TBool : type
  | TUnit : type
  | TBits : nat -> type
  | TPair : type -> type -> type.

Lemma type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
   repeat decide equality.
Qed.

Fixpoint interp_type (t : type) : finType :=
  match t with
    | TBool => [finType of bool]
    | TUnit => [finType of unit]
    | TBits n => [finType of n.-tuple bool]
    | TPair t1 t2 => [finType of interp_type t1 * interp_type t2] end.

Coercion interp_type : type >-> finType.

Instance inhabited_type t : Inhabited (interp_type t).
induction t.
apply _.
apply _.
apply _.
apply inhabit_prod.
    done.
    done.
Defined.

(* Declared opaquely. *)
Axiom chan : type -> Type.


Definition Chan :=
  { t : type & chan t}.

Definition mkChan {t} (c : chan t) : Chan := ltac:(exists t; exact c).

Section RxnDef.
  
  Inductive rxn : type -> Type :=
  | Samp {t : type} : Dist t -> rxn t
  | Ret {t : type} : t -> rxn t
  | Read {t : type} (c : chan t) : rxn t
  | Bind {t1 t2 : type} : rxn t1 -> (t1 -> rxn t2) -> rxn t2.
  
Fixpoint isDet n (r : rxn n) : Prop :=
  match r with
    | Samp _ _ => False 
    | Read _ _ => True
    | Ret _ _ => True 
    | Bind _ _ c k => isDet _ c /\ forall x, isDet _ (k x) end.

Fixpoint rxn_inputs {n} (r : rxn n) : list (Chan) :=
  match r with
    | Samp _ _ => nil 
    | Read _ c => [:: mkChan c]
    | Ret _ _ => nil 
    | Bind _ _ c k => rxn_inputs c ++ rxn_inputs (k witness) end.
 
Arguments Samp [t].
Arguments Ret [t].
Arguments Bind [t1 t2].

Notation "x <-- c ;; k" := (Bind c (fun x => k)) (at level 41, right associativity).


(* convenience constructors *)

Definition bv_of {n} (t : n.-tuple bool) : TBits n := t.
Definition pair_of {t1 t2 : type} (p : t1 * t2) : TPair t1 t2 := p.
Notation "[bv t ]" := (bv_of [tuple of t]).
Notation "{{ x , y }}" := (pair_of (x, y)).

Fixpoint Unif (t : type) : rxn t :=
  match t with
  | TBool => @Samp TBool (Flip (fun b => DRet b))
  | TUnit => Ret (tt : TUnit)
  | TBits n => @Samp (TBits n) (uniform n)
  | TPair t1 t2 =>
    (x <-- Unif t1 ;; y <-- Unif t2 ;; Ret {{ x, y }}) end.

Inductive EqRxn : forall A, rxn A -> rxn A ->  Prop := 
  | EqReadSame {n} {m} (c : chan n) (k : n -> n -> rxn m) :
      EqRxn _ (@Bind _ _ (Read c) (fun x => @Bind _ _ (Read c) (fun y => k x y)))
            (@Bind _ _ (Read c) (fun x => k x x))
  | EqSampUnused (n : type) (d : Dist n) m (k : rxn m) :
      EqRxn _ (Bind (Samp d) (fun _ => k)) k
  | EqRxnRefl n (r : rxn n) : EqRxn _ r r
  | EqRxnSym n (r1 : rxn n) (r2 : rxn n) : EqRxn _ r1 r2 -> EqRxn _ r2 r1
  | EqRxnTr n (r1 : rxn n) (r2 : rxn n) (r3 : rxn n) : EqRxn _ r1 r2 -> EqRxn _ r2 r3 -> EqRxn _ r1 r3
  | EqRetBind (n m : type) (x : n) (k : n -> rxn m) :
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
  | EqSampBijection (n : type) (f : n -> n) :
      injective f -> 
      EqRxn _ (Unif n) (Bind (Unif n) (fun x => Ret (f x)))
  (* only sound if r is wfRxn, as below *)
  | EqMkRead {t t2 : type} (r : rxn t) (c : chan t2) :
      In (rxn_inputs r) (mkChan c) ->
      EqRxn _ r (Bind (Read c) (fun _ => r))
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

Notation "x <-- c ;; k" := (Bind c (fun x => k)) (at level 41, right associativity).

Notation "[bv t ]" := (bv_of [tuple of t]).

Notation "{{ x , y }}" := (pair_of (x, y)).

Definition vtrue : TBool := true.
Definition vfalse : TBool := false.
Definition vtt : TUnit := tt.

Definition psel1 {t1 t2 : type} (p : TPair t1 t2) : t1 := p.1.
Definition psel2 {t1 t2 : type} (p : TPair t1 t2) : t2 := p.2.

Notation "x .`1" := (psel1 x) (at level 20).
Notation "x .`2" := (psel2 x) (at level 20).

Coercion TBits : nat >-> type.

Notation "x ** y" := (TPair x y) (at level 30).

Add Parametric Relation n : (rxn n) (@EqRxn n)
                                    reflexivity proved by (@EqRxnRefl  _)
                                    symmetry proved by (@EqRxnSym _ )
                                    transitivity proved by (@EqRxnTr  _) as rxn_rel.

Require Import Setoid Relation_Definitions.
Close Scope bool_scope.

Add Parametric Morphism (n m : type) (k : n -> rxn m) : (fun r => Bind r k)
    with signature (@EqRxn n) ==> (@EqRxn m) as bind_mor.                                                         
  intros; apply EqRxnBind.

  done.
  intro; reflexivity.
Qed.

Infix "=r" := (@EqRxn _) (at level 40).
  
Require Import Lib.TupleLems.


(** Tactics for reactions **)

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

Lemma EqRxnRet {n : type} (x y : n) : 
  x = y -> (Ret x) =r (Ret y).
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


Lemma EqBindSame {n m} (r : rxn m) (k : m -> m -> rxn n) :
  isDet _ r ->
  (x <-- r ;; 
   y <-- r ;;
   k x y) =r (x <-- r ;; k x x).
  induction r.
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

Lemma EqBind_r_samp_bijection (t t2 : type) (k : t -> rxn (t2)) (f : t -> t) :
  injective f ->
  (x <-- Unif t ;; k x) =r (x <-- Unif t ;; k (f x)).
  intros.
  etransitivity.
  apply EqRxnBind.
  apply EqSampBijection.
  apply H.
  intro; apply EqRxnRefl.
  simp_rxn.
  apply EqRxnRefl.
Qed.

(* Well-formed ness *)
Inductive WfRxn : forall t, seq Chan -> rxn t -> Prop :=
| WfRet (t : type) (x : t) : WfRxn _ nil (Ret x)
| WfSamp (t  :type) (d : Dist t) : WfRxn _ nil (Samp d)
| WfRead t (c : chan t) : WfRxn _ [:: mkChan c] (Read c)
| WfBind t1 t2 c1 c2 (r1 : rxn t1) (r2 : t1 -> rxn t2) :
    WfRxn _ c1 r1 ->
    (forall x, WfRxn _ c2 (r2 x)) ->
    WfRxn _ (c1 ++ c2) (Bind r1 r2)
.

Definition wfRxn {t} (r : rxn t) := exists c, WfRxn _ c r.

Definition Rxn t := {r : rxn t | wfRxn r}.

(* Smart constructor for reactions which performs type checking *)
Notation "[rxn r ]" :=
  (ltac:( let i := eval simpl in (proj1_sig ((exist wfRxn r ltac:(eexists; repeat econstructor)) : Rxn _)) in exact i)) (at level 30).

Section Test.
  Context (x y z : chan (TBits 3)).

  Definition r :=
    [rxn
        a <-- Read x ;;
        b <-- Unif (TBits 2) ;;
        c <-- Read y ;;
        Ret [bv nil]
     ].


  Fail Definition r2 :=
    [rxn 
        a <-- Read x ;;
        b <-- Unif (TBits 2) ;;
        c <-- if thead b then Read y else Read x ;;
                                          Ret [bv nil] ]
  .

End Test.

