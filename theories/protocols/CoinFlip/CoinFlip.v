Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Lib.Set CFold.  

Section CFIdeal.
  Context {chan : Type -> Type}.
  Context (k : nat) (n : nat) (honest : pred 'I_n).
  Context (leak : chan (k.-tuple bool)).
  Context (ok : chan unit).
  Context (out : n.-tuple (chan (k.-bv))).

  Definition CFIdealParty (i : 'I_n) (send : chan (k.-bv)) :=
         (if honest i then Out (tnth out i) (copy send) else prot0).


  Definition CFIdealFunc (send : chan (k.-bv)) :=
    b <- new (k.-bv) ;;
    pars [::
            Out b (Samp (Unif));
            Out leak (copy b);
            Out send (_ <-- Read ok ;; copy b) ].

  Definition CFIdeal :=
    send <- new (k.-bv) ;;
    pars [::
            CFIdealFunc send;
            \||_(i < n) CFIdealParty i send
    ].

End CFIdeal.            


Section CFReal.
  Context {chan : Type -> Type}.
  Context (k : nat) (n_ : nat).
  Definition n := n_.+1.
  Context (honest : pred 'I_n).
  Context (out : n.-tuple (chan (k.-bv))).

  Context (advCommit : n.-tuple (chan (k.-bv))).
  Context (advOpen : n.-tuple (chan unit)).

  Context (advCommitted : n.-tuple (n.-tuple (chan unit))).
  Context (advOpened : n.-tuple (n.-tuple (chan (k.-bv)))).

  Definition CFRealParty_honest 
             (committed : n.-tuple (chan unit)) (opened : n.-tuple (chan (k.-bv)))
             (commit : chan (k.-bv)) (open : chan unit) (out : chan (k.-bv))
    :=
      committed_sum <- newvec n @ unit ;; 
      opened_sum <- newvec n @ k.-bv ;; 
      pars [::
            Out commit (Samp (Unif));
            read_all committed committed_sum;
            Out open (copy (tnth committed_sum ord_max));

            @cfold chan _ (k.-bv) (k.-bv) opened xort id opened_sum;
            Out out (copy (tnth opened_sum ord_max))
           ].

  Definition CFRealParty_corr (i : 'I_n)
             (committed : n.-tuple (chan unit))
             (opened : n.-tuple (chan (k.-bv)))
             (commit : chan k.-bv) (open : chan unit) :=
    pars [::
            Out commit (copy (tnth advCommit i));
            Out open (copy (tnth advOpen i));
            Outvec (tnth advCommitted i) (fun j => copy (tnth committed j));
            Outvec (tnth advOpened i) (fun j => copy (tnth opened j))
    ].

  Definition CFParty (i : 'I_n)
             (committed : n.-tuple (chan unit)) (opened : n.-tuple (chan k.-bv))
             (commit : chan k.-bv) (open : chan unit) (out : chan k.-bv) :=
    if honest i then CFRealParty_honest committed opened commit open out
                else CFRealParty_corr i committed opened commit open.                        
            
  Definition FComm
             (commit : chan k.-bv)
             (committed : chan unit)
             (open : chan unit)
             (opened : chan k.-bv) :=
    pars [::
            Out committed (_ <-- Read commit ;; Ret tt);
            Out opened (_ <-- Read open ;; copy commit)
         ].

  Definition CFReal :=
    commit <- newvec n @ k.-bv ;;
    committed <- newvec n @ unit ;;
    open <- newvec n @ unit ;;
    opened <- newvec n @ k.-bv ;;
    pars [::
            \||_(i < n) FComm (tnth commit i) (tnth committed i) (tnth open i) (tnth opened i);
         \||_(i < n) CFParty i committed opened (tnth commit i) (tnth open i) (tnth out i)
    ].

End CFReal.                   
                                     
           

    
           
