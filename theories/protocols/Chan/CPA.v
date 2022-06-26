(* Our main CPA example. *)


Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Lib.Set Ipdl.Approx.  

(* ----------- *) 

Section CPA.
  (* Our example is parameterized on types for the message, ciphertexts, and keys. (For our IPDL assumption to be realizable by IND-CPA, all messges in the type 'msg' must have the same length. ) *)
  Context {chan : Type -> Type}.
  Context {msg ctxt key : finType}.
  Context (msg0 : msg).
  Context (q : nat).


  (* In CPA0, we generate a secret key k randomly, and for j = 0..q,
    we read the j'th input message, and return the encryption of that
    message under k.  By the semantics of IPDL, the j'th output, o ## j,
     is available whenever the i'th input, i ## j, is
    available. Thus the below game enables all adversary queries to be
    made adversarially. *)


Definition CPA0 (genK : Dist key) (enc : msg -> key -> Dist ctxt) (i : q.-tuple (chan msg)) (o : q.-tuple (chan ctxt)) :=
  k <- new key ;;
  pars [::
          k ::= (Samp genK);
          \||_(j < q) (o ## j) ::=  (
                      m <-- Read (i ## j) ;; K <-- Read k ;;
                      c <-- Samp (enc m K) ;;
                      Ret c)].

(* CPA1 is the same as CPA0, but we encrypt a dummy message, msg0. *)
Definition CPA1 (genK : Dist key) (enc : msg -> key -> Dist ctxt) (i : q.-tuple (chan msg)) (o : q.-tuple (chan ctxt)) :=
  k <- new key ;;
  pars [::
          k ::= (Samp genK);
          \||_(j < q) (o ## j) ::= (
                      _ <-- Read (i ##  j) ;; K <-- Read k ;;
                      c <-- Samp (enc msg0 K) ;;
                      Ret c)].

(* The definition of CPA security. *)
Definition CPA_Secure (genK : Dist key) (enc : msg -> key -> Dist ctxt) cpa_err := forall (i : q.-tuple (chan msg)) (o : q.-tuple (chan ctxt)), CPA0 genK enc i o =a_(cpa_err) CPA1 genK enc i o.

(* The following exact equivalence on protocols states correctness of decryption. It states that 
the tuple (k, c, o) where k is a random key, c is an encryption of some message on an input channel i, 
and o is the decryption of c, is equivalent to the tuple (k, c, i). *)

Definition dec_correct (genK : Dist key) (enc : msg -> key -> Dist ctxt) (dec : ctxt -> key -> msg) := forall (k : chan key) (c : chan ctxt) (i : chan msg) (o : chan msg),
    pars [::
            k ::= (Samp genK);
            c ::= (x <-- Read k ;; m <-- Read i ;; c <-- Samp (enc m x) ;; Ret c);
            o ::= (x <-- Read c ;; y <-- Read k ;; Ret (dec x y)) ] =p 
    pars [::
            k ::= (Samp genK);
            c ::= (x <-- Read k ;; m <-- Read i ;; c <-- Samp (enc m x) ;; Ret c);
            o ::= (copy i) ].

(* Decryption correctness for a single message implies decryption correctness for q messages. *)
Lemma Multi_dec_correct (genK : Dist key) (enc : msg -> key -> Dist ctxt) (dec : ctxt -> key -> msg) : dec_correct genK enc dec -> forall (k : chan key) (c : q.-tuple (chan ctxt)) (i : q.-tuple (chan msg)) (o : q.-tuple (chan msg)),
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
  rewrite H.
  rewrite -pars_cat //=.
  symmetry.
  swap_tac 0 (Out k).
  apply pars_cons_cong; rewrite //=.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
Qed.

End CPA.
