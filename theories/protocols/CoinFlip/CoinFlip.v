Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Typing Lib.Set CFold.  

Section CFIdeal.
  Context (k : nat) (n : nat) (honest : pred 'I_n).
  Context (leak : chan k).
  Context (ok : chan TUnit).
  Context (out : n.-tuple (chan k)).

  Definition CFIdealParty (i : 'I_n) (send : chan k) :=
         (if honest i then Out (tnth out i) (copy send) else prot0).

  Definition CFIdealFunc (send : chan k) :=
    b <- new k ;;
    pars [::
            Out b (Unif k);
            Out leak (copy b);
            Out send (_ <-- Read ok ;; copy b) ].

  Definition CFIdeal :=
    send <- new k ;;
    pars [::
            CFIdealFunc send;
            \||_(i < n) CFIdealParty i send
    ].

End CFIdeal.            

Section CFReal.
  Context (k : nat) (n_ : nat).
  Definition n := n_.+1.
  Context (honest : pred 'I_n).
  Context (out : n.-tuple (chan k)).

  Context (advCommit : n.-tuple (chan k)).
  Context (advOpen : n.-tuple (chan TUnit)).

  Context (advCommitted : n.-tuple (n.-tuple (chan TUnit))).
  Context (advOpened : n.-tuple (n.-tuple (chan k))).

  Definition CFRealParty_honest 
             (committed : n.-tuple (chan TUnit)) (opened : n.-tuple (chan k))
             (commit : chan k) (open : chan TUnit) (out : chan k)
    :=
      committed_sum <- newvec n @ TUnit ;; 
      opened_sum <- newvec n @ k ;; 
      pars [::
            Out commit (Unif k);
            read_all committed committed_sum;
            Out open (copy (tnth committed_sum ord_max));

            @cfold _ k k opened xort id opened_sum;
            Out out (copy (tnth opened_sum ord_max))
           ].

  Definition CFRealParty_corr (i : 'I_n)
             (committed : n.-tuple (chan TUnit))
             (opened : n.-tuple (chan k))
             (commit : chan k) (open : chan TUnit) :=
    pars [::
            Out commit (copy (tnth advCommit i));
            Out open (copy (tnth advOpen i));
            Outvec (tnth advCommitted i) (fun j => copy (tnth committed j));
            Outvec (tnth advOpened i) (fun j => copy (tnth opened j))
    ].

  Definition CFParty (i : 'I_n)
             (committed : n.-tuple (chan TUnit)) (opened : n.-tuple (chan k))
             (commit : chan k) (open : chan TUnit) (out : chan k) :=
    if honest i then CFRealParty_honest committed opened commit open out
                else CFRealParty_corr i committed opened commit open.                        
            
  Definition FComm
             (commit : chan k)
             (committed : chan TUnit)
             (open : chan TUnit)
             (opened : chan k) :=
    pars [::
            Out committed (_ <-- Read commit ;; Ret vtt);
            Out opened (_ <-- Read open ;; copy commit)
         ].

  Definition CFReal :=
    commit <- newvec n @ k ;;
    committed <- newvec n @ TUnit ;;
    open <- newvec n @ TUnit ;;
    opened <- newvec n @ k ;;
    pars [::
            \||_(i < n) FComm (tnth commit i) (tnth committed i) (tnth open i) (tnth opened i);
         \||_(i < n) CFParty i committed opened (tnth commit i) (tnth open i) (tnth out i)
    ].

End CFReal.                   
                                     
           

    
           
