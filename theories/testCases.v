From Stdlib Require Import List.

Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.

Require Import Animation.animationModules.
Require Import Animation.utils.

Import utils.MetaRocqNotations.

Require Import PeanoNat.
Local Open Scope nat_scope.
Open Scope bs.

(* 1 *)
Section s.
(*
Variable g1 : nat -> nat.
Variable g2 : nat -> nat.
Variable g3 : nat -> nat -> nat.
*)

(* Can also use context ? *) 
Context (g1 : nat -> nat) (g2 : nat -> nat) (g3 : nat -> nat -> nat) (g4 : nat -> nat -> nat -> nat -> nat).

Lemma beq_nat_eq : forall n m, true = (n =? m) -> n = m. Proof. Admitted.
Lemma beq_nat_neq : forall n m, false = (n =? m) -> (n = m -> False). Proof. Admitted.


(* a, b designated as input, c d e designated as output *)
Inductive foo : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr : forall a b c d e, (e = b /\ d = c /\ c = (g3 a e) /\ g1 d = g2 a) -> foo a b c d e.
 

MetaRocq Run (animateEqual.animate'' <? foo ?> foo ["a"; "b"] ["c"; "d";"e"] 10).

Next Obligation.
Proof. unfold animateEqual.soundness'. (* exists ((fun n1 n2 => if Nat.eqb (g1 (g3 n1 n2)) (g2 n1) then Some [g3 n1 n2; g3 n1 n2; n2] else None) n1 n2). *)
remember (Nat.eqb (g1 (g3 n1 n2)) (g2 n1)) as H. destruct H.
+ split.
++ (*apply cstr.*) apply beq_nat_eq in HeqH. rewrite -> HeqH.
auto. 
+ intros. inversion H ; subst. apply beq_nat_neq in HeqH.
*  auto.
* destruct H0. rewrite H0 in H1. destruct H1.
rewrite H1 in H2. destruct H2. rewrite H2 in H3. auto.
 Qed.

Inductive foo' : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr' : forall a b c d e, (g1 d = g2 a /\ d = c /\ c = (g3 a e) /\ e = b ) -> foo' a b c d e.
 
MetaRocq Run (animateEqual.animate'' <? foo' ?> foo' ["a" ; "b"] ["c"; "d";"e"] 30).

Next Obligation.
Proof. unfold animateEqual.soundness'. (* exists ((fun n1 n2 => if Nat.eqb (g1 (g3 n1 n2)) (g2 n1) then Some [g3 n1 n2; g3 n1 n2; n2] else None) n1 n2). *)
remember (Nat.eqb (g1 (g3 n1 n2)) (g2 n1)) as H. destruct H.
+ split.
++ (*apply cstr.*) apply beq_nat_eq in HeqH. rewrite -> HeqH.
auto. 
+ intros. inversion H ; subst. apply beq_nat_neq in HeqH.
*  auto.
* destruct H0. destruct H1. rewrite H1 in H0. destruct H2. rewrite H3 in H2. rewrite H2 in H0. auto.

 Qed.
     
(* known var 'b' is on LHS not RHS *)



Inductive foo'' : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr'' : forall a b c d e, (g1 d = g2 a /\ d = c /\ c = (g3 a e) /\ b = e ) -> foo'' a b c d e.
 

MetaRocq Run (animateEqual.animate'' <? foo'' ?>  foo'' ["a" ; "b"] ["c"; "d";"e"] 30).
Next Obligation.
Proof. unfold animateEqual.soundness'. (* exists ((fun n1 n2 => if Nat.eqb (g1 (g3 n1 n2)) (g2 n1) then Some [g3 n1 n2; g3 n1 n2; n2] else None) n1 n2). *)
remember (Nat.eqb (g1 (g3 n1 n2)) (g2 n1)) as H. destruct H.
+ split.
++ (*apply cstr.*) apply beq_nat_eq in HeqH. rewrite -> HeqH.
auto. 
+ intros. inversion H ; subst. apply beq_nat_neq in HeqH.
*  auto.
* destruct H0. destruct H1. rewrite H1 in H0. destruct H2.  apply beq_nat_neq in HeqH. 
- auto.
- rewrite <- H3 in H2. rewrite <- H2. auto.

 Qed.




 
Inductive foo4 : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr4 : forall a b c d e, ((fun x => x) d = (fun x => x + 1) a /\ d = b /\  ((fun x y w z => x + w) a e a e) = c /\ b = e ) -> foo4 a b c d e.
 


MetaRocq Run (animateEqual.justAnimate <? foo4 ?> ["a" ; "b"] ["c"; "d";"e"] "foo4Fn" 100). 

(* Print foo4Fn. *)

Example testfoo4 : foo4Fn 2 3 = Some [4; 3; 3].
Proof. reflexivity. Qed.

Example test2foo4 : foo4Fn 1 1 = None.
Proof. reflexivity. Qed.

Example test3foo4 : foo4Fn 3 4 = Some [6; 4; 4].
Proof. reflexivity. Qed.




Inductive foo5 : nat -> nat -> Prop :=
 | cstr5 : forall a b, a = b  -> foo5 a b.
 

MetaRocq Run (animateEqual.justAnimate <? foo5 ?> ["a"] ["b"] "foo5Fn" 100).

(* Print foo5Fn. *)

Example testfoo5 : foo5Fn 1 = Some [1]. 
Proof. reflexivity. Qed.

Example test2foo5 : foo5Fn 3 = Some [3]. 
Proof. reflexivity. Qed. 
  

End s.


Inductive tuple : nat -> nat -> (prod nat nat) -> Prop :=
 | tupleCon : forall (a : nat), forall (b : nat), forall (y : (prod nat nat)), (a, S b) = y -> tuple a b y. (*RHS of equality not v imp*)
 
MetaRocq Run (typeConstrPatMatch.justAnimatePatMat tuple ["a" ; "b"] "tupleFn" 25).

(* Print tupleFn. *)

Example testtupleFn : tupleFn (2, 4) = Some [2 ; 3].
Proof. reflexivity. Qed. 

Example test2tupleFn : tupleFn (3, 1) = Some [3 ; 0].
Proof. reflexivity. Qed.

Example test3tupleFn : tupleFn (1, 0) = None.
Proof. reflexivity. Qed.
 

         


Inductive singleton : nat -> list nat -> Prop :=
 | singletonCon : forall (a : nat), forall (y : list nat), (a :: [])  = y -> singleton a  y.  (*RHS of equality not v imp*)
 

MetaRocq Run (typeConstrPatMatch.justAnimatePatMat singleton ["a"] "singletonFn" 25).

Example testsingletonFn : singletonFn [4] = Some [4].
Proof. reflexivity. Qed.

Example test2singletonFn : singletonFn [] = None.
Proof. reflexivity. Qed.

Example test3singletonFn : singletonFn [4 ; 5] = None.
Proof. reflexivity. Qed.





(* 4 *)

Inductive myType' : Set :=
| mycr1' : nat -> myType'
| mycr2' : nat -> myType'.

Inductive myType : Set :=
| mycr2 : myType' -> nat -> myType
| mycr3 : myType.


Inductive baz' : nat -> nat -> myType -> Prop :=
 | bazCon' : forall (a : nat), forall (x : nat), forall (y : myType), mycr2 (mycr1' a) (S x) = y -> baz' a x y.  (*RHS of equality not v imp*)
 
MetaRocq Run (typeConstrPatMatch.justAnimatePatMat baz' ["a"; "x"] "baz'Fn" 25).



Example testbaz'Fn : baz'Fn (mycr2 (mycr1' 4) 3) = Some [4; 2].
Proof. reflexivity. Qed.

Example test2baz'Fn : baz'Fn (mycr2 (mycr1' 4) 0) = None.
Proof. reflexivity. Qed.



Inductive fooCon : nat -> nat -> nat -> nat -> Prop :=
 | cstrCon : forall a b c d,  [S a ; S c]  = [S b ; d]  -> fooCon a b c d.
 


MetaRocq Run (typeConstrReduce.justAnimateElimConstr <? fooCon ?> ["a" ; "c"] ["b" ; "d"] "fooConFn" 50).
(* Print fooConFn. *)

Example testfooConFn : fooConFn 2 3 = Some [2 ; 4].
Proof. reflexivity. Qed.

Example test2fooConFn : fooConFn 4 3 = Some [4 ; 4].
Proof. reflexivity. Qed.


Inductive fooCon' : nat -> nat -> nat -> nat -> Prop :=
 | cstrCon' : forall a b c d, [S b ; d] = [S a ; S c]  -> fooCon' a b c d.
 
MetaRocq Run (typeConstrReduce.justAnimateElimConstr <? fooCon' ?> ["b" ; "c"] ["a" ; "d"] "fooCon'Fn" 50).


Example testfooCon'Fn : fooConFn 2 3 = Some [2 ; 4].
Proof. reflexivity. Qed.

Example test2fooCon'Fn : fooConFn 4 3 = Some [4 ; 4].
Proof. reflexivity. Qed.




  
 










