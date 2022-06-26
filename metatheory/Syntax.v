From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple fintype.
From mathcomp Require Import choice path bigop ssrnum ssralg.
Require Import Coq.Program.Equality.

Require Import FunctionalExtensionality.


Inductive Ctx :=
| Nil
| CCons : finType -> Ctx -> Ctx.

Inductive Pos : Ctx -> Type :=
| PHere {t} {c} : Pos (CCons t c)
| PThere {t} {c} : Pos c -> Pos (CCons t c) .

Fixpoint eq_pos {c} (p1 p2 : Pos c) : {p1 = p2} + {p1 <> p2}.
  dependent destruction p1.
  dependent destruction p2.
  left; done.
  right; done.
  dependent destruction p2.
  right; done.
  destruct (eq_pos _ p1 p2).
  subst; left; done.
  right.
  intro.
  apply n.
  inversion H.
  move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1) => H2.
  done.
Qed.

Definition eqb_pos {c} (p1 p2 : Pos c) :=
  match eq_pos p1 p2 with
    | left _ => true
    | right _ => false end.

Lemma eqb_pos_spec {c} (p1 p2 : Pos c) :
  if eqb_pos p1 p2 then p1 = p2 else p1 <> p2.
    rewrite /eqb_pos.
    destruct (eq_pos p1 p2); done.
Qed.

Fixpoint insertCtx (c : Ctx) (n : nat) (t : finType) {struct n}  : Ctx :=
  match n with
  | 0 => CCons t c
  | S n' =>
      match c with
      | Nil => CCons t Nil
      | CCons t' c' => CCons t' (insertCtx c' n' t) end end.

Fixpoint typeAt {c} (p : Pos c) : finType :=
  match p with | @PHere t _ => t | PThere _ _ p => typeAt p end.

Fixpoint lift_pos {c} {n} {t'} (p : Pos c) : Pos (insertCtx c n t').
  dependent destruction p.
  destruct n.
  simpl.
  apply (PThere PHere).
  simpl.
  apply PHere.
  destruct n; simpl.
  apply (PThere (PThere p)).
  apply PThere.
  apply lift_pos.
  apply p.
Defined.

Definition bump_pos {c} {t} (p : Pos c) : Pos (CCons t c) :=
  @lift_pos c 0 t p.

Lemma lift_pos_PThere t' c n t (p : Pos c) :
  @lift_pos (CCons t' c) n t (PThere p) =
    match n with
    | 0 => PThere (PThere p)
    | S n' => PThere (@lift_pos c n' t p) end.
  destruct n.
  done.
  dependent destruction p; done.
Qed.

Lemma typeAt_lift_pos {c} {n} {t'} (p : Pos c) :
  typeAt p = typeAt (@lift_pos c n t' p).
  move: n t' p.
  dependent induction c.
  intros; inversion p.
  intros.
  dependent destruction p.
  destruct n; rewrite //=.
  rewrite lift_pos_PThere.
  destruct n.
  done.
  simpl.
  apply IHc.
Qed.

Inductive rxn c : Type -> Type :=
  | Ret {t} : t -> rxn c t
  | Read (p : Pos c) : rxn c (typeAt p)
  | Bind {t1 t2} : rxn c t1 -> (t1 -> rxn c t2) -> rxn c t2.

Fixpoint lift_rxn {c} {n} {t} {a} (r : rxn c a) : rxn (insertCtx c n t) a.
    destruct r.
    apply (Ret _ t1).
    rewrite (@typeAt_lift_pos c n t p).
    apply (Read _ (lift_pos p)).
    apply (Bind _ (lift_rxn _ _ _ _ r)
                  (fun x => lift_rxn _ _ _ _ (r0 x))).
Defined.
                         
Inductive ipdl c :=
  | Zero : ipdl c
  | Out (p : Pos c) : rxn c (typeAt p) -> ipdl c              
  | Par : ipdl c -> ipdl c -> ipdl c
  | New (t : finType) : ipdl (CCons t c) -> ipdl c.

Fixpoint lift_ipdl {c} {n} {T} (p : ipdl c) {struct p} : ipdl (insertCtx c n T).
destruct p.
apply Zero.
apply (Out _ (lift_pos p)).
rewrite (@typeAt_lift_pos c n T p) in r.
apply (lift_rxn r).
apply (Par _ (lift_ipdl _ _ _ p1) (lift_ipdl _ _ _ p2)).
apply (New _ t (lift_ipdl (CCons t c) n.+1 T p)).
Defined.

Definition bump_ipdl {c} {T} (p : ipdl c) := @lift_ipdl c 0 T p.

Definition disjoint {a} (f g : a -> bool) :=
  forall x, ~~ (f x && g x).

Inductive ipdl_t : forall c, ipdl c -> (Pos c -> bool) -> Prop :=
| Zero_t {c} o : o = (fun _ => false) -> ipdl_t c (Zero _) o
| Out_t  {c} {p : Pos c } (r : rxn c (typeAt p)) o :
  o = (fun p' => eqb_pos p p') -> 
  ipdl_t c (Out _ p r) o
| Par_t {c} {p} {q} o1 o2 o :
  ipdl_t c p o1 -> ipdl_t c q o2 ->
  disjoint o1 o2 ->
  o = (fun x => o1 x || o2 x) -> 
  ipdl_t c (Par _ p q) o
| New_t {c} t p o o' :
   ipdl_t (CCons t c) p o -> 
   o' = (fun x => o (bump_pos x)) -> 
   ipdl_t c (New _ t p) o'
.

Lemma par_t_inv {c} (p q : ipdl c) o :
  ipdl_t _ (Par _ p q) o ->
  exists o1 o2,
    [/\
       disjoint o1 o2,
      ipdl_t _ p o1,
      ipdl_t _ q o2 &
      o = (fun x => o1 x || o2 x)
    ].
    intro h; inversion h; subst.
    exists o1; exists o2; split.
    done.
    move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H) => H'; subst.
    done.
    move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H0) => H'; subst.
    done.
    apply functional_extensionality => x.
    move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1) => H'; subst.
    done.
Qed.

Lemma new_t_inv {c} {t} (p : ipdl (CCons t c)) o :
  ipdl_t _ (New _ t p) o ->
  exists o',
    ipdl_t _ p o' /\
    o = (fun x => o' (bump_pos x)).
    intro h; inversion h; subst.
    exists o0; split.
    move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H0) => H'; subst.
    move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H') => H''; subst.
    done.
    apply functional_extensionality => x.
    move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H2) => H''; subst.
    done.
Qed.

Fixpoint unlift_pos {c} n t (p : Pos (insertCtx c n t)) : option (Pos c).
  destruct n.
  dependent destruction p.
  apply None.
  apply (Some p).

  dependent destruction c.
  simpl in *.
  apply None.
  simpl in *.
  dependent destruction p.
  apply (Some PHere).
  destruct (unlift_pos _ _ _ p).
  apply (Some (PThere p0)).
  apply None.
Defined.

Lemma unlift_lift_pos {c} n t (p : Pos c) :
  unlift_pos n t (@lift_pos c n t p) = Some p.
  move: n t.
  induction p; intros; destruct n; rewrite //=.
  rewrite /solution_left //=.
  rewrite /eq_rect_r //=.
  rewrite IHp.
  done.
Qed.

Lemma lift_unlift_pos {c} n t (p : Pos (insertCtx c n t)) p' :
  unlift_pos _ _ p = Some p' ->
  @lift_pos c n t p' = p.
Admitted.

Lemma lift_ipdl_t {c} n t (p : ipdl c) o :
  ipdl_t _ p o ->
  ipdl_t _ (@lift_ipdl c n t p) (fun x => match unlift_pos n t x with | Some y => o y | None => false end).
intro h; move: n t; induction h; intros.
simpl.
apply Zero_t.
apply functional_extensionality => x.
destruct (unlift_pos n t x).
rewrite H //=.
done.
apply Out_t.
apply functional_extensionality => x.
remember (unlift_pos n t x) as p'; destruct p'.
rewrite H //=.
Check (eqb_pos_spec p p0).
have h0 := eqb_pos_spec p p0.
have h1 := eqb_pos_spec (lift_pos p) x.
destruct (eqb_pos p p0); destruct (eqb_pos (lift_pos p) x); subst.
done.
symmetry in Heqp'.
move/lift_unlift_pos: Heqp' => h; done.
rewrite unlift_lift_pos in Heqp'.
inversion Heqp'; subst; done.
done.
have h := eqb_pos_spec (lift_pos p) x.
destruct (eqb_pos (lift_pos p) x).
subst.
rewrite unlift_lift_pos in Heqp'; done.
done.
eapply Par_t.
simpl.
apply IHh1.
apply IHh2.
admit. (* disjoint unlift *)
admit. (* disjoint unlift *)

simpl.
eapply New_t.
specialize (IHh n.+1 t0).
apply IHh.
apply functional_extensionality => x.
subst.
remember (unlift_pos n t0 x) as y; destruct y.
remember (@unlift_pos (CCons t c) n.+1 t0 (@bump_pos (insertCtx c n t0) t x)) as z; destruct z.
congr (_ _).
admit.
admit.
admit.
(* Round trip properties wrt lift, unlift *)
Admitted.


Inductive ipdl_eq {c} : ipdl c -> ipdl c -> Prop :=
| ERefl p : ipdl_eq p p
| ESym p1 p2 : ipdl_eq p1 p2 -> ipdl_eq p2 p1
| ETr p1 p2 p3 : ipdl_eq p1 p2 -> ipdl_eq p2 p3 -> ipdl_eq p1 p3
| EEqCompNew t p q :
  ipdl_eq (Par _ (New _ t p) q)
          (New _ t (Par _ p (bump_ipdl q)))
.

Lemma ipdl_eq_t {c} (p q : ipdl c) o :
  ipdl_eq p q ->
  ipdl_t _ p o <-> ipdl_t _ q o.
  intro h; induction h.
  done.
  rewrite IHh //=.
  rewrite IHh1 IHh2 //=.
  split => h.
  move/par_t_inv: h; elim => o1; elim => o2; elim => h1 h2 h3 h4.
  subst.
  move/new_t_inv: h2; elim => o1' [h4 h5]; subst.
  eapply New_t.
  eapply Par_t.
  apply h4.
  apply (@lift_ipdl_t c 0 t).  
  apply h3.
  simpl.
  admit. (* disjointness *)
  done.
  apply functional_extensionality.
  intro.
  rewrite unlift_lift_pos; done.

  move/new_t_inv: h; elim => o1 [h1 h2]; subst.
  move/par_t_inv: h1; elim => o2; elim => o3; elim; intros.
  subst.
  eapply Par_t.
  eapply New_t.
  apply H0.
  done.
  have: ipdl_t c q (fun x => o3 (bump_pos x)).
    admit.
    intro.
    apply x.
  admit. (* disjoint *)
  apply functional_extensionality => x.
  done.
Admitted.
