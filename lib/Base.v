From mathcomp Require Import ssreflect ssrnat seq tuple matrix fintype ssrfun.
Require Import FunctionalExtensionality.

(* Haskell-style notation for application (when convenient) *)
Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).


(* Inhabited typeclass. Used to enforce the type is not empty *)
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

(** Notations for pairs **)

Definition psel {A} (x : A * A) (b : bool) :=
  if b then x.2 else x.1.

Infix "#" := psel (at level 30).

Definition mkpair {A} (f : bool -> A) : A * A :=
  (f false, f true).

Notation "[ 'pair' i => f ] " := (mkpair (fun i => f)).
