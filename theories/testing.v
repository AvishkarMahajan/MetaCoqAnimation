Require Import Animation.animationModulesIntegration.
Require Import Animation.animationModulesSimplEq.

Require Import Animation.utils2.
Require Import Animation.animationModulesPatMat.

Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.


Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.


Inductive genRel14 : nat -> nat -> nat -> nat -> Prop :=
 | genRelcstr14 : forall (a b c d : nat), a = b /\ c = d -> genRel14 a b c d. (* a c input k d output *)

Inductive genRel13 : nat -> list nat -> nat -> Prop :=
 | genRelcstr13 : forall (a d b c e f : nat) (l : list nat), d = c /\ a::l = [b;c] /\ b = c /\ genRel14 (S a) e d (S f)  -> genRel13 a l f .
MetaRocq Run (animateListLetAndPredGuard' genRel13 <? genRel13 ?>  [("a", <%nat%>); ("l", <%list nat%>)]  [("f", <%nat%>)] [("genRel14", ([0;2],[1;3])); ("genRel13",([0;1],[2]))] 
              [("genRel14", [<%nat%>;<%nat%>;<%nat%>;<%nat%>]); ("genRel13",[<%nat%>;<%list nat%>; <%nat%>])] [("d", <%nat%>); ("e", <%nat%>); ("f", <%nat%>); ("a", <%nat%>); ("b", <%nat%>); ("c", <%nat%>); ("l", <%list nat%>)] 
              [("genRel14",<% nat -> outcomePoly (nat * nat) -> outcomePoly (nat * nat)%>)] 50).

Print genRel13Animated.




Definition genRel14AnimatedTopFn (fuel: nat) (i: outcomePoly (nat × nat)) : outcomePoly (nat × nat) :=
 match fuel with
  | 0 => fuelErrorPoly (nat * nat)
  | S m => match i with 
            | successPoly (n1, n2) => successPoly (nat * nat) (n1, n2) 
            | fuelErrorPoly => fuelErrorPoly (nat * nat) 
            | _ => noMatchPoly (nat * nat)
           end
 end.
 
Compute genRel13Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (1, [1])). 

Compute genRel13Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (3, [3])). 

Compute genRel13Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (3, [3;4])). 

Compute genRel13Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (3, [4])).
 
Compute genRel13Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (0, [0])).
 
(*WRONG RESULT when PREDICATE should be animated partially as guard and partially as let)
Inductive genRel15 : nat -> list nat -> nat -> Prop :=
 | genRelcstr15 : forall (a d b c e f : nat) (l : list nat), d = c /\ a::l = [b;c] /\ e = c /\ (*c = f  /\*) genRel14 a (S e) d f  -> genRel15 a l f .

MetaRocq Run (animateListLetAndPredGuard' genRel15 <? genRel15 ?>  [("a", <%nat%>); ("l", <%list nat%>)]  [("f", <%nat%>)] [("genRel14", ([0;2],[1;3])); ("genRel15",([0;1],[2]))] 
              [("genRel14", [<%nat%>;<%nat%>;<%nat%>;<%nat%>]); ("genRel15",[<%nat%>;<%list nat%>; <%nat%>])] [("d", <%nat%>); ("e", <%nat%>); ("f", <%nat%>); ("a", <%nat%>); ("b", <%nat%>); ("c", <%nat%>); ("l", <%list nat%>)] 
              [("genRel14",<% nat -> outcomePoly (nat * nat) -> outcomePoly (nat * nat)%>)] 50).

Compute genRel15Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (4, [3])).

Compute genRel15Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (4, [4])).

Print genRel15Animated.
*)               
Inductive genRel15 : nat -> list nat -> nat -> Prop :=
 | genRelcstr15 : forall (a d b c e f : nat) (l : list nat), d = c /\ a::l = [b;c] /\ e = c /\ c = f  /\ genRel14 a (S e) d f  -> genRel15 a l f .

MetaRocq Run (animateListLetAndPredGuard' genRel15 <? genRel15 ?>  [("a", <%nat%>); ("l", <%list nat%>)]  [("f", <%nat%>)] [("genRel14", ([0;2],[1;3])); ("genRel15",([0;1],[2]))] 
              [("genRel14", [<%nat%>;<%nat%>;<%nat%>;<%nat%>]); ("genRel15",[<%nat%>;<%list nat%>; <%nat%>])] [("d", <%nat%>); ("e", <%nat%>); ("f", <%nat%>); ("a", <%nat%>); ("b", <%nat%>); ("c", <%nat%>); ("l", <%list nat%>)] 
              [("genRel14",<% nat -> outcomePoly (nat * nat) -> outcomePoly (nat * nat)%>)] 50).

Compute genRel15Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (4, [3])).

Compute genRel15Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (4, [4])).
          
                         
              