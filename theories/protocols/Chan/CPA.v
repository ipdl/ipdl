(* Our main CPA example. *)


Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Lib.Set Ipdl.Approx.  

Module Type CPA.

  (* Our example is parameterized on lengths for the message, ciphertexts, and keys. (For our IPDL assumption to be realizable by IND-CPA, all messges in the type 'msg' must have the same length. ) *)
  Parameter (msg ctxt key : nat).
  Parameter (q : nat).

  Parameter (genK : Dist key.-bv).
  Parameter (enc : msg.-bv -> key.-bv -> Dist ctxt.-bv).
  Parameter (dec : ctxt.-bv -> key.-bv -> msg.-bv).

  (* In CPA0, we generate a secret key k randomly, and for j = 0..q,
    we read the j'th input message, and return the encryption of that
    message under k.  By the semantics of IPDL, the j'th output, o ## j,
     is available whenever the i'th input, i ## j, is
    available. Thus the below game enables all adversary queries to be
    made adversarially. *)
  
Definition CPA0 {chan:  Type -> Type} (i : q.-tuple (chan msg.-bv)) (o : q.-tuple (chan ctxt.-bv)) :=
  k <- new key.-bv ;;
  pars [::
          k ::= (Samp genK);
          \||_(j < q) (o ## j) ::=  (
                      m <-- Read (i ## j) ;; K <-- Read k ;;
                      c <-- Samp (enc m K) ;;
                      Ret c)].

(* CPA1 is the same as CPA0, but we encrypt a dummy message of all zeores *)
Definition CPA1 {chan : Type -> Type} (i : q.-tuple (chan msg.-bv)) (o : q.-tuple (chan ctxt.-bv)) :=
  k <- new key.-bv ;;
  pars [::
          k ::= (Samp genK);
          \||_(j < q) (o ## j) ::= (
                      _ <-- Read (i ##  j) ;; K <-- Read k ;;
                      c <-- Samp (enc [tuple of nseq msg false]  K) ;;
                      Ret c)].

  (* Security parameter for CPA security. For security, it must be that the length of keys and number of queries q is polynomial in lambda. *)
Parameter (lambda : nat).
Parameter (CPA_security : 
              forall {chan : Type -> Type} (i : q.-tuple (chan msg.-bv)) o, CPA0 i o =a_(lambda, err1) CPA1 i o).


(* The following exact equivalence on protocols states correctness of decryption. It states that 
the tuple (k, c, o) where k is a random key, c is an encryption of some message on an input channel i, 
and o is the decryption of c, is equivalent to the tuple (k, c, i). *)

Definition dec_correct_def  := forall (chan : Type -> Type) (k : chan key.-bv) (c : chan ctxt.-bv) (i : chan msg.-bv) (o : chan msg.-bv),
    pars [::
            k ::= (Samp genK);
            c ::= (x <-- Read k ;; m <-- Read i ;; c <-- Samp (enc m x) ;; Ret c);
            o ::= (x <-- Read c ;; y <-- Read k ;; Ret (dec x y)) ] =p 
    pars [::
            k ::= (Samp genK);
            c ::= (x <-- Read k ;; m <-- Read i ;; c <-- Samp (enc m x) ;; Ret c);
            o ::= (copy i) ].

Parameter (dec_correct : dec_correct_def).
(* Decryption correctness for a single message implies decryption correctness for q messages. *)
Lemma Multi_dec_correct {chan : Type -> Type} : forall (k : chan key.-bv) (c : q.-tuple (chan ctxt.-bv)) (i : q.-tuple (chan msg.-bv)) (o : q.-tuple (chan msg.-bv)),
    pars [::
            k ::= (Samp genK);
            \||_(j < q) (c ## j)  ::= (x <-- Read k ;; m <-- Read (tnth i j) ;; c <-- Samp (enc m x) ;; Ret c);
            \||_(j < q) (o ## j) ::= (x <-- Read (tnth c j) ;; y <-- Read k ;; Ret (dec x y)) ] =p 
    pars [::
            Out k (Samp genK);
            \||_(j < q) (c ## j) ::= (x <-- Read k ;; m <-- Read (tnth i j) ;; c <-- Samp (enc m x) ;; Ret c);
            \||_(j < q) (o ## j) ::= (copy (tnth i j)) ].
  intros.
  swap_tac 0 2.
  rewrite -par_in_pars.
  rewrite -bigpar_par.
  symmetry.
  swap_tac 0 2.
  rewrite -par_in_pars.
  rewrite -bigpar_par.
  symmetry.
  apply pars_big_hybrid2; intros.
  rewrite bigpar_par par_in_pars.
  swap_tac 0 2; rewrite par_in_pars.
  symmetry.
  rewrite par_in_pars.
  swap_tac 0 2; rewrite par_in_pars.
  symmetry.
  swap_tac 0 4.
  swap_tac 2 4.
  rewrite (pars_split 3); simpl.
  rewrite dec_correct.
  rewrite -pars_cat //=.
  symmetry.
  swap_tac 0 (Out k).
  apply pars_cons_cong; rewrite //=.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
Qed.

End CPA.

