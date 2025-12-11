From Stdlib Require Import List.

Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.

Require Import Animation.animationModules.
Require Import Animation.utils.

Import utils.MetaRocqNotations.

Require Import PeanoNat.
Local Open Scope nat_scope.
Open Scope bs.

Inductive tl1Rel2 : (list nat) -> nat -> nat -> nat -> bool -> Prop :=
 | tl1RelCons2: forall (a : list nat) (c b d : nat), ((fun x y => x :: y) b a) = [c ; d] -> tl1Rel2 a c (S d) (S b) true.

MetaRocq Run (c <- general.animate2 <? tl1Rel2 ?> ;; tmPrint c). 
MetaRocq Run (extractPatMatBinders7 <? tl1Rel2 ?> tl1Rel2 [([3;0],[1])] 1 50).

Compute (tl1Rel2Animated 25 (successPoly (nat × list nat) (2, [5]))).


Inductive tlRel3 : list nat -> (nat) -> Prop :=
 | tlRelCons3: forall (a : nat) (b : nat),  b = S a -> tlRel3  [b] a.

MetaRocq Run (extractPatMatBinders7 <? tlRel3 ?> tlRel3 [([0],[1])] 1 50).

Compute tlRel3Animated 5 (successPoly (list nat) [2]).
(*
Inductive tlRel4 : list nat -> (nat) -> Prop :=
 | tlRelCons4: forall (b : nat), tlRel4  [b] b.
 

MetaRocq Run (animateInductivePredicate' tlRel4 "tlRel4" <? tlRel4 ?> [([0],[1])] 50).
Print tlRelCons4Animated.

Compute tlRel3Animated 5 (successPoly (list nat) [2]).

*)


(* Mode : rel38 : [0 ; 2] input, [1; 3] output, rel39 : [0;1] input, [2;3] output *)

Inductive rel38: nat -> nat -> nat -> nat -> Prop :=
 | rel38Base : forall a, rel38 1 3 a (S a) 
 | rel38Cons : forall a1 a2 b1 b2, rel38 a1 b1 a2 b2 /\ rel39 a1 a2 b1 b2 -> rel38 (S a1) (S b1) (S a2) (S b2)
with rel39: nat -> nat -> nat -> nat -> Prop := 
 | rel39Cons : forall a b c d, rel38 a c b d  -> rel39 a b c d.



MetaRocq Run (animateInductivePredicate' rel38 "rel38" <? rel38 ?> [([0;2], [1;3]) ; ([0;1], [2;3])] 50).



Print tmFreshName.
Print ident.



(* Parameter (g1 : nat -> nat) (g2 : nat -> nat) (g3 : nat -> nat -> nat) (g4 : nat -> nat -> nat -> nat -> nat). *)

Inductive foo' : bool -> nat -> bool -> nat -> Prop :=
 | cstr' : forall (b  d : bool) (e f : nat), d = b /\ e = f /\ ((fun x => x + 1) e) = ((fun x => x + 1) f) -> foo' b (S f) d (S e).
(*
Inductive foo' : bool -> nat -> bool -> nat -> Prop :=
 | cstr' : forall (b  d : bool) (e f : nat), d = b /\ [e] = [f] /\ ((fun x => x + 1) e) = ((fun x => x + 1) f) -> foo' b (S f) d (S e).
*)


MetaRocq Run (animateEqual.genFunAnimateEq7 <? foo' ?> foo' [([0;1],[2;3])] 50).

Print foo'Animated.

Inductive foo'' : bool -> nat -> bool -> nat -> Prop :=
 | cstr'' : forall (b  d : bool) (e f : nat), d = b /\ e =  f /\ ((fun x => x) e) = ((fun x => x + 1) f) -> foo'' b (S f) d (S e).

Print hole.

MetaRocq Run (animateEqual.genFunAnimateEq7 <? foo'' ?> foo'' [([0;1],[3])] 50).

Check foo''Animated.


Inductive foo'lst : list nat -> list nat -> Prop :=
 | cstr'lst : forall (a  b : list nat), (fun l => tl l) a = (fun l => tl (tl l)) b -> foo'lst a b.

MetaRocq Run (animateEqual.genFunAnimateEq7 <? foo'lst ?> foo'lst [([0;1],[])] 50).



Inductive foo5lst : nat -> nat -> Prop :=
 | cstr5lst : forall (a b c : nat), b :: [a] = b :: [c] -> foo5lst a c.

Print hole.
(*
MetaRocq Run (extractPatMatBinders7 <? foo5lst ?> foo5lst [([0],[1])] 1 50).
*)

Compute rel38AnimatedTopFn 20 (successPoly (nat × nat) (5, 2)).

(**

Example foo1Ex : foo'lstAnimated 5 (successPoly (list nat × list nat) ([1;2], [1;2])) = noMatchPoly bool.
Proof. reflexivity. Qed.

Example foo2Ex : foo'lstAnimated 5 (successPoly (list nat × list nat) ([1;2], [3;1;2])) = successPoly bool true.
Proof. reflexivity. Qed.

Example tlRel2Ex : tl1Rel2Animated 5 (successPoly (nat × list nat) (2, [5])) = (successPoly (nat × nat) (1,6)).
Proof. reflexivity. Qed.

Example tlRel2Ex2 : tl1Rel2Animated 5 (successPoly (nat × list nat) (0, [5])) = (noMatchPoly (nat × nat)).
Proof. reflexivity. Qed.

Example tlRel2Ex3 : tl1Rel2Animated 5 (successPoly (nat × list nat) (1, [5;6])) = (noMatchPoly (nat × nat)).
Proof. reflexivity. Qed.

Example foo'Ex : foo'Animated 5 (successPoly (bool × nat) (true, 1)) = (successPoly (bool × nat) (true, 1)).
Proof. reflexivity. Qed.

Example foo'Ex2 : foo'Animated 5 (successPoly (bool × nat) (true, 0)) = (noMatchPoly (bool × nat)).
Proof. reflexivity. Qed.
(*
Example foo''Ex : foo''Animated 5 (successPoly (bool × nat) (true, 1)) = (noMatchPoly (bool × nat)).
Proof. reflexivity. Qed.
*)
Example rel38Ex : rel38AnimatedTopFn 10 (successPoly (nat × nat) (2, 4)) = (successPoly (nat × nat) (4, 5)).
Proof. reflexivity. Qed.

Example rel38Ex2 : rel38AnimatedTopFn 20 (successPoly (nat × nat) (5, 2)) = (noMatchPoly (nat × nat)).
Proof. reflexivity. Qed.

Example foo'lstEx : foo'lstAnimated 9 (successPoly (list nat × list nat) ([3;0], [0;3;0])) = (successPoly (bool) true).
Proof. reflexivity. Qed.

Example foo'lstEx2 : foo'lstAnimated 9 (successPoly (list nat × list nat) ([3;0], [0;3;1])) = (noMatchPoly (bool)).
Proof. reflexivity. Qed.

Example tlRel3Ex : tlRel3Animated 5 (successPoly (list nat) [2]) = (successPoly nat 1).
Proof. reflexivity. Qed.

Example tlRel3Ex2 : tlRel3Animated 5 (successPoly (list nat) [0]) = (noMatchPoly nat).
Proof. reflexivity. Qed.

Example tlRel3Ex3 : tlRel3Animated 5 (successPoly (list nat) [1;1]) = (noMatchPoly nat).
Proof. reflexivity. Qed.
**)
    


