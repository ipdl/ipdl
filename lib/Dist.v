From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path bigop finfun fintype.
Require Import Strings.BinaryString String FunctionalExtensionality.
Require Import QArith Lia.


Inductive Dist A :=
  | DRet : A -> Dist A
  | Flip : (bool -> Dist A) -> Dist A.

Arguments DRet [A].
Arguments Flip [A].

Fixpoint dbind {A B} (d :  Dist A) (k : A -> Dist B) : Dist B :=
  match d with
    | DRet x => k x
    | Flip f =>
      Flip (fun b => dbind (f b) k)
  end.

Fixpoint uniform (n : nat) : Dist (n.-tuple bool) :=
  match n with
    | 0%nat => DRet [tuple]
    | S n' =>
      Flip (fun x =>
              dbind (uniform n') (fun t => DRet [tuple of x :: t])) end.

      
