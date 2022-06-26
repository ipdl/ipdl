

Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Lib.Set Ipdl.Approx.  

(* some lemmas about EqSplitBranch *)
Check EqSplitBranch.
Require Import Lib.SeqOps Lib.Perm Permutation.



Lemma pars_split_branch' {chan} t (c : chan t) b (l r : chan t -> rxn t) rs :
  pars [:: c ::= (x <-- Read b ;; if x then l c else r c) & rs] =p
  L <- new t ;; R <- new t ;;
  pars [::
          L ::= (_ <-- Read b ;; l c),
          R ::= (_ <-- Read b ;; r c),
       c ::= (x <-- Read b ;; if x then copy L else copy R) & rs].
rewrite EqSplitBranch.
rewrite newPars.
setoid_rewrite newPars.
Intro => L.
Intro => R.
rewrite par_in_pars.
apply pars_cons_cong; rewrite //=.
rewrite par_in_pars.
apply pars_cons_cong; rewrite //=.
apply pars_cons_cong; rewrite //=.
apply EqCongReact.
apply EqBind_r => x; destruct x.
rewrite /copy; rewrite EqBindRet //=.
rewrite /copy; rewrite EqBindRet //=.
apply _.
Qed.

Lemma pars_split_branch {chan : Type -> Type} {t} (c : chan t) (b : chan bool) r1 r2 rs :
  pars [::c ::= (b <-- Read b;; if b then r1 c else r2 c) & rs]
       =p
                                          (L <- new t ;;
                                           R <- new t ;;
                                           pars [::
                                                   L ::= r1 c,
                                                   R ::= r2 c,
                                                   c ::= (b <-- Read b ;; if b then copy L else copy R) & rs]).
  rewrite pars_split_branch'.
  symmetry.
  etransitivity.
  Intro => L.
  Intro => R.
  swap_tac 0 2; rewrite insert_0.
  rewrite pars_split_branch'.
  apply EqRefl.
  simpl.
  symmetry.
  swap_tac 0 2.
  etransitivity.
  Intro => L.
  Intro => R.
  rewrite pars_split_branch'.
  apply EqRefl.
  simpl.
  rotate_news; simpl.
  rotate_news; simpl.
  etransitivity.
  Intro => L.
  Intro => R.
  etransitivity.
  Intro => l.
  Intro => r.
  rewrite insert_0.
  edit_tac 0.
  instantiate (1 := x <-- Read l ;; _ <-- Read b ;; Ret x).
  rewrite /copy; r_swap 0 1; done.
  edit_tac 1.
  instantiate (1 := x <-- Read r ;; _ <-- Read b ;; Ret x).
  rewrite /copy; r_swap 0 1; done.
  apply EqRefl.
  simpl.
  swap_tac 0 1.
  swap_tac 1 3.
  setoid_rewrite pars_fold at 1.
  swap_tac 0 2.
  swap_tac 1 3.
  setoid_rewrite pars_fold at 1.
  rewrite insert_0; apply EqRefl.
  simpl.
  symmetry.
  rotate_news.
  rotate_news.
  etransitivity.
  Intro => L.
  Intro => R.
  etransitivity.
  Intro => l.
  Intro => r.
  edit_tac 0.
  instantiate (1 := x <-- Read l ;; _ <-- Read b ;; Ret x).
  rewrite /copy; r_swap 0 1; done.
  edit_tac 1.
  instantiate (1 := x <-- Read r ;; _ <-- Read b ;; Ret x).
  rewrite /copy; r_swap 0 1; done.
  apply EqRefl.
  simpl.
  swap_tac 0 1.
  swap_tac 1 3.
  setoid_rewrite pars_fold at 1.
  swap_tac 0 2.
  swap_tac 1 3.
  setoid_rewrite pars_fold at 1.
  rewrite insert_0.
  apply EqRefl.
  Intro => L.
  Intro => R.
  apply pars_cons_cong.
  apply EqCongReact.
  r_swap 0 1.
  symmetry; simp_rxn.
  r_swap 1 2.
  rewrite EqReadSame //=.
  apply pars_cons_cong.
  apply EqCongReact.
  r_swap 0 1.
  symmetry; simp_rxn.
  r_swap 1 2.
  rewrite EqReadSame //=.
  done.
Qed.
          
Lemma pars_fold_under_branch_l {chan : Type -> Type} {t t'} (b : chan bool) (o : chan t') rs r r' k :
  (c <- new t ;;
  pars [::
          c ::= r,
                o ::= (b <-- Read b;; if b then (x <-- Read c ;; k x) else r') & rs])
  =p
     (pars [:: o ::= (b <-- Read b;; if b then (x <-- r ;; k x) else r') & rs]).
  etransitivity.
  swap_tac 0 1.
  setoid_rewrite insert_0; simpl.
  etransitivity.
  Intro => c.
  rewrite pars_split_branch.
  apply EqRefl.
  simpl.
  swap_tac 1 3.
  rotate_news; simpl.
  setoid_rewrite pars_fold.
  setoid_rewrite insert_0; simpl. 
  swap_tac 1 2; setoid_rewrite insert_0; simpl.
  rewrite -(pars_split_branch o b (fun _ => (x1 <-- r ;; k x1))).
  apply EqRefl.
  apply pars_cons_cong.
  apply EqCongReact.
  apply EqBind_r; intro; destruct x.
  simp_rxn; done.
  done.
  done.
Qed.

Lemma pars_fold_under_branch_r {chan : Type -> Type} {t t'} (b : chan bool) (o : chan t') rs r r' k :
  (c <- new t ;;
  pars [::
          c ::= r,
                o ::= (b <-- Read b;; if b then r' else (x <-- Read c ;; k x)) & rs])
  =p
     (pars [:: o ::= (b <-- Read b;; if b then r' else (x <-- r ;; k x)) & rs]).
  etransitivity.
  swap_tac 0 1.
  setoid_rewrite insert_0; simpl.
  etransitivity.
  Intro => c.
  rewrite pars_split_branch.
  apply EqRefl.
  simpl.
  swap_tac 0 1.
  swap_tac 1 3.
  rotate_news; simpl.
  setoid_rewrite pars_fold.
  setoid_rewrite insert_0; simpl. 
  swap_tac 1 2; setoid_rewrite insert_0; simpl.
  swap_tac 0 1.
  rewrite -(pars_split_branch o b).
  apply EqRefl.
  apply pars_cons_cong.
  apply EqCongReact.
  apply EqBind_r; intro; destruct x.
  done.
  simp_rxn; done.
  done.
Qed.

Definition branch {chan : Type -> Type} {t t'} (b : chan bool)
            (P Q : chan t -> chan t' -> ipdl) (* input, return *) 
            (i : chan t) 
            (o : chan t') :=
  diverge <- new t ;;
  i1 <- new t ;;
  i2 <- new t ;;
  o1 <- new t' ;;
  o2 <- new t' ;;
  pars [::
          diverge ::= Read diverge;
          i1 ::= (b <-- Read b ;; if b then copy i else copy diverge);
          i2 ::= (b <-- Read b ;; if b then copy diverge else copy i);
          P i1 o1;
          Q i2 o2;
          o ::= (b <-- Read b ;; if b then copy o1 else copy o2)
               ].


Lemma branch_eq {chan : Type -> Type} {t t'} (b : chan bool)
      (P P' Q Q' : chan t -> chan t' -> ipdl)
      bnd1 bnd2 bnd3 bnd4
      `{forall x y, IPDLBnd (P x y) bnd1}
      `{forall x y, IPDLBnd (P' x y) bnd3}
      `{forall x y, IPDLBnd (Q x y) bnd2}
      `{forall x y, IPDLBnd (Q' x y) bnd4}
      i o e e' :
  (forall i o, P i o =a_(e) P' i o) ->
  (forall i o, Q i o =a_(e') Q' i o) ->
  branch b P Q i o =a_(
  comp_err e (bnd2 + 4) +e comp_err e' (bnd3 + 4)) branch b P' Q' i o.
  intros; rewrite /branch.
  eapply AEq_err_eq; last first.
  apply AEq_new => diverge.
  apply AEq_new => i1.
  apply AEq_new => i2.
  apply AEq_new => o1.
  apply AEq_new => o2.
  arewrite (H3 i1 o1).
  arewrite (H4 i2 o2).
  apply AEq_zero; done.
  done.
  rewrite !comp_err_comp !add_err0.
  done.
  congr (_ +e _).
  congr (_ _ _).
  rewrite -!addnA.
  congr (_ + _).
  congr (_ _ _).
  rewrite !(addnC bnd3).
  rewrite addnA.
  congr (_ + _).
Qed.

Require Import Typ Lib.SeqOps Lib.Perm.

Lemma branch_t {chan : Type -> Type} {t t'} (P Q : chan t -> chan t' -> ipdl) b i o :
  (forall x y, ipdl_t [:: tag y] (P x y)) ->
  (forall x y, ipdl_t [:: tag y] (Q x y)) ->
  ipdl_t [:: tag o] (branch b P Q i o).
  intros; rewrite /branch.
  type_tac.
  apply H.
  apply H0.
  rewrite cats0 //=.
  done.
  done.
  done.
  done.
  simpl; perm_match.
Qed.

Lemma EqReadBranch {chan : Type -> Type} {t t'} (b : chan bool) (i : chan t) (k1 k2 : t -> rxn t') :
  (x <-- Read b ;; if x then (y <-- Read i ;; k1 y) else (y <-- Read i ;; k2 y)) =r (x <-- Read b ;; y <-- Read i ;; if x then k1 y else k2 y).
  apply EqBind_r => x.
  destruct x; done.
Qed.

Lemma BranchRxn {chan : Type -> Type}{t t'} (b : chan bool) (i : chan t) (o : chan t') k1 k2 :
  branch b (fun i o => o ::= (x <-- Read i ;; k1 x))
         (fun i o => o ::= (x <-- Read i ;; k2 x)) i o =p
  (o ::= (b <-- Read b ;; x <-- Read i ;; if b then k1 x else k2 x)).    
    rewrite /branch.
    etransitivity.
    swap_tac 0 4.
    swap_tac 1 5.
    setoid_rewrite (pars_fold_under_branch_r b o) at 1.
    swap_tac 0 1.
    swap_tac 0 2.
    setoid_rewrite (pars_fold_under_branch_l b o) at 1.
    etransitivity.
    Intro => d.
    Intro => i1.
    Intro => i2.
    edit_tac 0.
    instantiate (1 :=
                   b0 <-- Read b ;;
                   if b0 then
                     x <-- Read i1 ;; k1 x
                   else x <-- Read i2 ;; k2 x).
    apply EqBind_r => x; destruct x; simp_rxn; done.
    apply EqRefl.
    simpl.
    swap_tac 0 1.
    setoid_rewrite (pars_fold_under_branch_r b o) at 1.
    swap_tac 0 2.
    swap_tac 1 2.
    setoid_rewrite (pars_fold_under_branch_l b o) at 1.
    etransitivity.
    Intro => diverge.
    edit_tac 0.
    etransitivity.
    instantiate (1 := ((c <-- Read b ;;
                    if c then (y <-- Read b ;; if y then z <-- Read i ;; k1 z else z <-- Read diverge ;; k1 z)
                            else
                    (y <-- Read b ;; if y then z <-- Read diverge ;; k2 z else z <-- Read i ;; k2 z)))).
    rewrite EqReadBranch.
    apply EqBind_r => b0.
    destruct b0.
    simp_rxn.
    apply EqBind_r => b1.
    destruct b1; rewrite /copy; simp_rxn; done.
    simp_rxn.
    apply EqBind_r => b1.
    destruct b1; rewrite /copy; simp_rxn; done.
    rewrite EqReadBranch.
    rewrite EqReadSame.
    instantiate (1 := (x <-- Read b;; z <-- Read i ;; if x then k1 z else k2 z)).
    apply EqBind_r => x; destruct x; done.
    apply EqRefl.
    simpl.
    swap_tac 0 1.
    rewrite new_pars_remove.
    apply EqRefl.
    rewrite pars1 //=.
Qed.

Lemma BranchSameRxn {chan : Type -> Type} {t t'} (b : chan bool) (i : chan t) (o : chan t') k :
  branch b (fun i o => o ::= (x <-- Read i ;; k x))
           (fun i o => o ::= (x <-- Read i ;; k x))
           i o =p (o ::= (_ <-- Read b ;; x <-- Read i ;; k x)).
  rewrite BranchRxn.
  apply EqCongReact.
  apply EqBind_r => x; destruct x; done.
Qed.

Lemma BranchFlip {chan : Type -> Type} {t t'} (b : chan bool) (i : chan t) (o : chan t') P Q :
  (b' <- new bool ;; pars [:: b' ::= (x <-- Read b ;; Ret (negb x)); branch b' P Q i o]) =p branch b Q P i o.
  rewrite /branch.
  swap_tac 0 1.
  repeat setoid_rewrite newPars.
  rotate_news; simpl.
  Intro => diverge.
  setoid_rewrite pars_pars; simpl.
  setoid_rewrite (EqNewExch t t) at 1.
  Intro => i1.
  Intro => i2.
  setoid_rewrite (EqNewExch t' t') at 1.
  Intro => o1.
  Intro => o2.
  swap_tac 0 6.
  etransitivity.
  Intro => b'.
  swap_tac 0 1.
  rewrite pars_inline.
  swap_tac 0 2; rewrite pars_inline.
  swap_tac 0 5; rewrite pars_inline.
  apply EqRefl.
  done.
  done.
  done.
  simpl.
  swap_tac 0 1.
  rewrite new_pars_remove.
  align.
  apply EqCongReact; simp_rxn; apply EqBind_r => x; destruct x; simpl; done.
  apply EqCongReact; simp_rxn; apply EqBind_r => x; destruct x; simpl; done.
  apply EqCongReact; simp_rxn; apply EqBind_r => x; destruct x; simpl; done.
  apply _.
  apply _.
  apply _.
  apply _.
  apply _.
Qed.

Lemma BranchSeq_l {chan : Type -> Type} {t t' t''} (b : chan bool) (i : chan t) (o : chan t'') (r : rxn t') k1 k2 : 
  isDet _ r -> 
  branch b (fun i o => o ::= (y <-- Read i ;; x <-- r ;; k1 x y))
         (fun i o => o ::= (y <-- Read i ;; x <-- r ;; k2 x y)) i o =p
 c <- new t' ;; pars [:: c ::= r; branch b
       (fun i o => o ::= (y <-- Read i ;; x <-- Read c ;; k1 x y ))
       (fun i o => o ::= (y <-- Read i ;; x <-- Read c ;; k2 x y ))
       i o].
  intros.
  rewrite BranchRxn.
  setoid_rewrite BranchRxn.
  symmetry.
  etransitivity.
  Intro => c.
  edit_tac 1.
  instantiate (1 := 
                 z <-- Read c ;; b0 <-- Read b ;; x <-- Read i ;; if b0 then k1 z x else k2 z x).
  symmetry.
  r_swap 0 1.
  apply EqBind_r => x; destruct x; r_swap 0 1; done.
  apply EqRefl.
  simpl.
  swap_tac 0 1.
  rewrite pars_fold.
  rewrite pars1.
  apply EqCongReact.
  r_swap 0 1.
  apply EqBind_r => x; destruct x; r_swap 0 1; done.
Qed.

Require Import Setoid Relation_Definitions Morphisms.
Close Scope bool_scope.
Add Parametric Morphism {chan} t t' : (@branch chan t t')
    with signature (eq ==>
                    (pointwise_relation _ (pointwise_relation _ EqProt)) ==>                                  
                    (pointwise_relation _ (pointwise_relation _ EqProt)) ==>                                  
                    eq ==> eq ==> EqProt) as branch_rel.
  intros.
  rewrite /branch.
  repeat ltac:(Intro; intro).
  rewrite H H0.
  done.
Qed.

Lemma BranchSeq_r {chan : Type -> Type} {t t' t''} (b : chan bool) (i : chan t) (o : chan t'') (k1 k2 : t -> rxn t') (k : t' -> rxn t'') : 
  branch b (fun i o => o ::= (x <-- Read i ;; y <-- k1 x ;; k y))
         (fun i o => o ::= (x <-- Read i ;; y <-- k2 x ;; k y)) i o =p
  o' <- new t';;
pars [::
        branch b (fun i o => o ::= (x <-- Read i ;; k1 x))
        (fun i o => o ::= (x <-- Read i ;; k2 x)) i o';
        o ::= (x <-- Read o';; k x)].
  intros; symmetry; rewrite /branch.
  repeat setoid_rewrite newPars.
  rotate_news; simpl.
  Intro => d.
  Intro => i1.
  Intro => i2.
  symmetry.
  swap_tac 0 4.
  swap_tac 1 5.
  setoid_rewrite pars_fold_under_branch_r.
  swap_tac 0 1.
  swap_tac 0 2.
  setoid_rewrite pars_fold_under_branch_l.
  symmetry.
  setoid_rewrite pars_pars; simpl.
  etransitivity.
  rotate_news; simpl.
  swap_tac 0 3.
  swap_tac 1 5.
  setoid_rewrite pars_fold_under_branch_l.
  rewrite EqNewExch.
  swap_tac 0 1.
  swap_tac 0 3.
  setoid_rewrite pars_fold_under_branch_r.
  swap_tac 0 1.
  swap_tac 0 4.
  rewrite pars_fold.
  apply EqRefl.
  align.
  apply EqCongReact.
  simp_rxn.
  apply EqBind_r => x; destruct x; simp_rxn; symmetry; simp_rxn; done.
  apply _.
  apply _.
  apply _.
  apply _.
  apply _.
Qed.

