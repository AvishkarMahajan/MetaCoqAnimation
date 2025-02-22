Require Import Coq.Lists.List.
            
Require Import MetaCoq.Template.All.
Import monad_utils.MCMonadNotation.




(* a, b designated as input, c d e designated as output *)
Inductive foo : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr : forall a b c d e, (e = b /\ d = c /\ c = a + e) -> foo a b c d e.

(* Let clauses in the same order as foo, leads to error since d depends on c but only a b e are known at that point. *) 
Definition animate1 (a : nat) (b : nat) : list nat :=
 let e := b in
 let d := c in
 let c := a + e in
 [c ; d ; e].

(** Let Clauses rearranged to be in the right order. The RHS of each let clause only contains input vars or previously calculated vars. **)
Definition animate2 (a : nat) (b : nat) : list nat :=
 let e := b in
 let c := a + e in
 let d := c in
 [c ; d ; e].
 
 
(** Aim : turn foo into foo' : | cstr' : forall a b c d e, (e = b /\ c = a + e /\ d = c) -> foo' a b c d e.
Then turn foo' into animate2 by turning conjuncts in premise of foo' to let clauses in the same order. **)

(** Simpler Problem from the perspective of MetaCoq term size, and to avoid conversion between de bruijn indicies and named 
representations for now, given : **)   
 
Parameter a : nat.
Parameter b : nat.
Parameter c : nat.
Parameter d : nat.
Parameter e : nat.

(** Write a function to turn  (e = b /\ d = c /\ c = a + e) into 
Some ((e = b /\c = a + e /\ d = c)) using the greedy algorithm to compute the correct order of the conjuncts. 
Function should fail with a None if no correct order exists **)  

MetaCoq Quote Definition propTerm := (e = b /\ d = c /\ c = a + e).

Print propTerm.


