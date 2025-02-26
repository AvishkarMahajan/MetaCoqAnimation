Require Import Coq.Lists.List.
Require Import List.
            
Require Import MetaCoq.Template.All.
Import monad_utils.MCMonadNotation.


(* a, b designated as input, c d e designated as output *)
Inductive foo : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr : forall a b c d e, (c + 1 = 2 * a /\ e = b /\ d = c /\ c = a + e) -> foo a b c d e.


(* Target output function *)

Definition animateFoo (a : nat) (b : nat) : option (list nat) :=
 let e := b in
 let c := a + e in
 let d := c in
 if (Nat.eqb (c + 1) (2 * a)) then Some ([c ; d ; e]) else None. 
 

Parameter a : nat.
Parameter b : nat.

Parameter partialProg : nat -> nat.

MetaCoq Quote Definition letTerm := (let a := b in partialProg).

Print letTerm.

Definition oneConjunctAnimate (conjunct : Prop) (known_vars : (list nat)) (partialProg : term) : 
                                                              ((list nat) × term). Admitted.
                                                              
                                                              
                                                              





MetaCoq Quote Definition propTerm := (a = b).

Print propTerm.

Print TemplateMonad.


Check (@tmReturn).

MetaCoq Run (x <- tmQuote partialProg ;; tmPrint x).

Definition testProg {A : Type} (p : A) : TemplateMonad unit :=
 x <- tmQuote p ;; tmPrint x. 

Definition testProg' (p : (nat -> nat)) : TemplateMonad unit :=
 x <- @tmReturn (nat -> nat) p ;; tmPrint x.
 
 
MetaCoq Run (testProg partialProg).

Compute (testProg partialProg).

Definition testProg2 (p : (nat -> nat)) : TemplateMonad unit :=
 x <- tmQuote p ;; y <- @tmUnquoteTyped (nat -> nat) x ;; tmPrint y.
 
MetaCoq Run (testProg2 partialProg).
     