From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path bigop finfun fintype matrix. 
Require Import Strings.BinaryString String FunctionalExtensionality.
Require Import Sets.Ensembles.

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).


Class Inhabited A :=
  witness : A.

Instance inhabit_bool : Inhabited bool := false.
Instance inhabit_unit : Inhabited unit := tt.
Instance inhabit_prod A B `{Inhabited A} `{Inhabited B} : Inhabited (A * B) := (witness, witness).
Instance inhabit_tup A `{Inhabited A} {n} : Inhabited (n.-tuple A) := [tuple of nseq n witness].
Instance inhabit_seq A : Inhabited (seq A) := nil.
Instance inhabit_fun A B `{Inhabited B} : Inhabited (A -> B) := fun _ => witness.
Instance inhabit_nat : Inhabited nat := 0.
Instance inhabit_matrix A `{Inhabited A} {n m} : Inhabited 'M[A]_(n, m) := const_mx witness.
Instance inhabit_ord n : Inhabited 'I_(n.+1) :=
  ord0.

Ltac funext := apply  functional_extensionality_dep.

Definition olet {A B} (x : option A) (k : A -> option B) := obind k x.



(** Notations for pairs **)

Definition psel {A} (x : A * A) (b : bool) :=
  if b then x.2 else x.1.

Infix "#" := psel (at level 30).

Definition mkpair {A} (f : bool -> A) : A * A :=
  (f false, f true).

Notation "[ 'pair' i => f ] " := (mkpair (fun i => f)).


(* Logical tactics *)

Ltac split_hyp :=
  repeat lazymatch goal with
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : is_true (_ && _) |- _ ] => destruct (andP H)
                                    end.



(* Misc lemmas *)
Lemma mem_flatten {A : eqType} x (xs : seq (seq A)) :
  (x \in flatten xs) = has (fun s => x \in s) xs.
  apply Bool.eq_true_iff_eq; split.
  move/flattenP.
  elim => s Hs.
  intro; apply/hasP.
  exists s; done.
  move/hasP; elim => s h1 h2.
  apply/flattenP; exists s; done.
Qed.

Lemma all_implybT {I : eqType} (xs : seq I) p :
  all (fun x => (p x) ==> true) xs.
  apply/allP => x Hx; rewrite implybT //=.
Qed.


