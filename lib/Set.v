From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
Require Import Lib.Crush.
Require Import Classical FunctionalExtensionality PropExtensionality.

(* A library for classical sets. *) 
(* Adapted from coq ensembles *)

Definition set A := A -> Prop.
Definition In {A} (s : set A) x := s x.
Definition subset {A} (x y : set A) :=
  forall a, x a -> y a.
Definition empty {A} : set A := fun _ => False.
Definition full {A} : set A := fun _ => True.
Inductive singleton {A} (x : A) : set A :=
  | Singleton : singleton x x.

Inductive union {A} (s t : set A) : set A :=
| Union_l y : s y -> union s t y
| Union_r y : t y -> union s t y.

Definition add {A} (s : set A) (x : A) :=
  union s (singleton x).

Inductive intersection {A} (s t : set A) : set A :=
| Intersection x : s x -> t x -> intersection s t x.

Inductive complement {A} (s : set A) : set A :=
  | Complement x : ~ s x -> complement s x.

Definition minus {A} (s t : set A) : set A :=
  intersection s (complement t).

Definition remove {A} (s : set A) x :=
  minus s (singleton x).

Definition disjoint {A} (s t : set A) :=
  forall x, (s x -> ~ t x) /\ (t x -> ~ s x).

Inductive inhabited {A} (s : set A) :=
  | Inhabit x : s x -> inhabited s.

Definition eq_set {A} (s t : set A) :=
  subset s t /\ subset t s.

Axiom eq_set_eq : forall {A} (s t : set A),
    eq_set s t -> s = t.

Fixpoint list_set {A} (x : list A) : set A :=
  match x with
    | nil => empty
    | a :: xs => add (list_set xs) a end.

Coercion list_set : list >-> set.

Lemma not_union {A} (s t : set A) x :
  ~ union s t x <-> intersection (complement s) (complement t) x.
  split.
  intros; constructor; constructor.
  intro; apply H; left; done.
  intro; apply H; right; done.
  elim; intros.
  intro.
  destruct H1.
  inversion H; subst; auto.
  inversion H0; subst; auto.
Qed.

Lemma complement_union {A} (s t : set A) :
  complement (union s t) = intersection (complement s) (complement t).
  apply functional_extensionality; intros.
  apply propositional_extensionality; intros.
  split.
  elim; intro.
  move/not_union; done.
  move/not_union; done.
Qed.

Lemma not_intersection {A} (s t : set A) x :
  ~ intersection s t x <-> union (complement s) (complement t) x.
  split.
  intros.
  have: ~ ((s x) /\ (t x)).
  intro.
  apply H.
  constructor; destruct H0; done.
  move/not_and_or.
  intro h.
  destruct h.
  left; done.
  right; done.
  case; intros.
  intro h.
  inversion h; subst.
  inversion s0; subst.
  done.
  inversion t0; subst.
  intro.
  inversion H0; subst.
  done.
Qed.

Lemma complement_intersection {A} (s t : set A) :
  complement (intersection s t) = union (complement s) (complement t).
  apply functional_extensionality; intros.
  apply propositional_extensionality; intros.
  split.
  elim; intro.
  move/not_intersection; done.
  move/not_intersection; done.
Qed.

Lemma not_singleton {A} (x y : A) :
  ~ singleton x y <-> x <> y.
  split; intros; intro.
  subst.
  apply H; constructor.
  inversion H0; subst; done.
Qed.

Lemma not_complement {A} (s : set A) x :
  ~ (complement s) x <-> s x.
  split.
  intros.
  have: (~ (~ s x)).
  intro.
  apply H.
  constructor; done.
  apply NNPP.
  intros.
  intro.
  inversion H0; subst.
  done.
Qed.


Lemma in_listP {A} (l : list A) x :
  In l x <-> List.In x l.
  move: x.
  induction l.
  simpl.
  crush.
  simpl.
  intros.
  split.
  elim; intros.
  right; apply IHl; done.
  left; destruct H; done.
  elim; intros; [right | left].
  subst; constructor.
  apply IHl; done.
Qed.

Lemma in_app_union {A} (l1 l2 : list A) x :
  (list_set (l1 ++ l2)) x <-> union l1 l2 x.
  split.
  induction l1.
  crush.
  right; done.
  simpl.
  intros.
  destruct H.
  destruct (IHl1 H).
  left; left; done.
  right; done.
  left; right; done.
  induction l1.
  crush.
  destruct H; done.
  intros; simpl in *.
  destruct H.
  destruct H.
  left; apply IHl1.
  left; done.
  right; done.
  left; apply (IHl1).
  right; done.
Qed.

Lemma in_cat_iff {A} (xs ys : list A) x :
  In (xs ++ ys) x <-> In xs x \/ In ys x.
  split.
  induction xs; rewrite //=.
  intros; right; done.
  intros.
  destruct H.
  move/IHxs: H; elim; intro.
  left; left; done.
  right; done.
  left; right; done.
  elim; induction xs.
  done.
  simpl; intros.
  destruct H.
  left; apply IHxs; done.
  right; done.
  simpl; done.
  simpl; intros.
  left; apply IHxs; done.
Qed.

Lemma in_map_iff {A B} (f : A -> B) l x :
  In (map f l) x <-> exists y, In l y /\ f y = x.
  split.
  move/in_listP.
  move/List.in_map_iff.
  elim => y [h1 h2]; exists y; split.
  apply in_listP; done.
  done.
  elim => y [h1 h2].
  apply in_listP.
  apply List.in_map_iff.
  exists y; split.
  done.
  apply in_listP; done.
Qed.

(* from software foundations *)
Ltac has_evar_as_bool E :=
  constr:(ltac:(first
    [ has_evar E; exact true
    | exact false ])).

Ltac set_tac :=
  intros; subst; auto; unfold remove, minus, add, In in *; simpl in *; try done; repeat match goal with
    (* Hypotheses *)                                                            
    | [ H : union _ _ _ |- _ ] => inversion H; subst; clear H
    | [ H : intersection _ _ _ |- _ ] => inversion H; subst; clear H
    | [ H : singleton _ _ |- _ ] => inversion H; subst; clear H
    | [ H : complement _ _ |- _ ] => inversion H; subst; clear H
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : _ \/ _ |- _ ] => destruct H
    | [ H : False |- _ ] => inversion H
    | [ H : empty _ |- _ ] => inversion H
    | [ H : ~ union _ _ _ |- _ ] => apply not_union in H
    | [ H : ~ intersection _ _ _ |- _ ] => apply not_union in H
    | [ H : ~ singleton _ _ |- _ ] => apply not_singleton in H
    | [ H : ~ complement _ _ |- _ ] => apply not_complement in H
    | [ H : ~ (forall x, _ ) |- _ ] => apply not_all_ex_not in H
    | [ H : exists _, _ |- _ ] => destruct H
    | [ H : _ <-> _ |- _ ] => destruct H
    | [ H : ~ (_ \/ _) |- _ ] => apply not_or_and in H
    | [ H : (list_set (_ ++ _)) _ |- _ ] => apply in_app_union in H
    (* Goals *)
    | [ |- ~ (forall _, _) ] => apply ex_not_not_all
    | [ |- intersection _ _ _ ] => constructor
    | [ |- eq_set _ _ ] => split
    | [ |- subset _ _ ] => intro; intro
    | [ |- complement _ _ ] => constructor
    | [ |- singleton ?c ?c ] => done
    | [ |- union ?l ?r ?c ] =>
      match l with
      | context [c] =>
        match r with
          | context [c] => fail
          | _ => left
        end
      | _ =>
        match r with
        | context [c] => right
        | _ => fail
        end 
      end
    | [ H : ?s ?x |- union ?s _ ?x ] => left
    | [ H : ?s ?x |- union _ ?s ?x ] => right
    | [ |- ~ union _ _ _ ] => apply not_union
    | [ |- ~ intersection _ _ _ ] => apply not_intersection
    | [ |- ~ singleton _ _ ] => apply not_singleton
    | [ |- @eq (set ?t) ?a ?b ] =>
      let b := has_evar_as_bool constr:(eq a b) in
      match b with
        | false => apply eq_set_eq (* Only apply lemma to fully concrete set equalities *)
        | _ => fail end
    | [ |- union (fun _ => False) _ _ ] => right
    | [ |- union _ (fun _ => False) _ ] => left
    | [ |- disjoint _ _ ] => intro; split; intro
    | [ |- (list_set (_ ++ _)) _ ] => apply in_app_union
    | [ |- _ /\ _ ] => split
    | [ |- _ <-> _ ] => split

                                                          end.

Ltac union_split :=
  match goal with
  | [ |- union _ _ _ ] =>
    (left; by repeat set_tac) + (right; by repeat set_tac) end.


Fixpoint Uniq {A} (xs : list A) :=
  match xs with
  | nil => True
  | x :: xs' =>
    (~ In xs' x) /\ Uniq xs' end.


