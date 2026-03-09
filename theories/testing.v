Require Import Animation.animationModulesFixPt.

Require Import Animation.animationModulesIntegration2.
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


Inductive append2 : list nat -> list nat -> list nat -> Prop := (* mode = ([1;2], [0] *)
 | appNil2 : forall (l1 l2 l3 : list nat), l1 = (fun x : bool => []) true   -> append2 l1 l2 l3.

MetaRocq Run (animateListLetAndPredGuard' append2 <? append2 ?> "appNil2" [("l2", <%list nat%>); ("l3", <%list nat%>)] [("l1", <%list nat%>)] [("append2",([1;2],[0]))] [("append2",[<%list nat%>;<%list nat%>;<%list nat%>])] 
               [("l1", <%list nat%>); ("l2", <%list nat%>); ("l3", <%list nat%>)] [] 100). 

Compute appNil2Animated 5 (successPoly ((list nat) * (list nat)) ([0;7],[0])). 

Inductive genRel14 : nat -> nat -> nat -> nat -> Prop :=
 | genRelcstr14 : forall (a b c d : nat), a = b /\ c = d -> genRel14 a b c d. (* a c input k d output *)

Inductive genRel13 : nat -> list nat -> nat -> Prop :=
 | genRelcstr13 : forall (a d b c e f : nat) (l : list nat), d = c /\  [b;c] = a::l /\ b = c /\ genRel14 (S a) e d (S f)  -> genRel13 a l f .





MetaRocq Run (animateListLetAndPredGuard' genRel13 <? genRel13 ?> "genRelcstr13" [("a", <%nat%>); ("l", <%list nat%>)]  [("f", <%nat%>)] [("genRel14", ([0;2],[1;3])); ("genRel13",([0;1],[2]))] 
              [("genRel14", [<%nat%>;<%nat%>;<%nat%>;<%nat%>]); ("genRel13",[<%nat%>;<%list nat%>; <%nat%>])] [("d", <%nat%>); ("e", <%nat%>); ("f", <%nat%>); ("a", <%nat%>); ("b", <%nat%>); ("c", <%nat%>); ("l", <%list nat%>)] 
              [("genRel14",<% nat -> outcomePoly (nat * nat) -> outcomePoly (nat * nat)%>)] 50).






Definition genRel14AnimatedTopFn (fuel: nat) (i: outcomePoly (nat × nat)) : outcomePoly (nat × nat) :=
 match fuel with
  | 0 => fuelErrorPoly (nat * nat)
  | S m => match i with 
            | successPoly (n1, n2) => successPoly (nat * nat) (n1, n2) 
            | fuelErrorPoly => fuelErrorPoly (nat * nat) 
            | _ => noMatchPoly (nat * nat)
           end
 end.
 
Compute genRelcstr13Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (1, [1])). 
(* Should return successPoly 0 *)

Compute genRelcstr13Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (3, [3])). 
(*Should return successPoly 2*)

Compute genRelcstr13Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (3, [3;4])). 

Compute genRelcstr13Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (3, [4])).
 
Compute genRelcstr13Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (0, [0])).

(*All should return noMatch *)
 

Inductive genRel15 : nat -> list nat -> nat -> Prop :=
 | genRelcstr15 : forall (a d b c e f : nat) (l : list nat), d = c /\ a::l = [b;c] /\ e = c /\ c = f  /\ genRel14 a (S e) d f  -> genRel15 a l f .

MetaRocq Run (animateListLetAndPredGuard' genRel15 <? genRel15 ?> "genRelcstr15"  [("a", <%nat%>); ("l", <%list nat%>)]  [("f", <%nat%>)] [("genRel14", ([0;2],[1;3])); ("genRel15",([0;1],[2]))] 
              [("genRel14", [<%nat%>;<%nat%>;<%nat%>;<%nat%>]); ("genRel15",[<%nat%>;<%list nat%>; <%nat%>])] [("d", <%nat%>); ("e", <%nat%>); ("f", <%nat%>); ("a", <%nat%>); ("b", <%nat%>); ("c", <%nat%>); ("l", <%list nat%>)] 
              [("genRel14",<% nat -> outcomePoly (nat * nat) -> outcomePoly (nat * nat)%>)] 50).

Compute genRelcstr15Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (4, [3])).
(*Should return successPoly 3*)
Compute genRelcstr15Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (4, [4])).
(*should return noMatch *)          
Inductive genRel16 : nat -> list nat -> nat -> Prop :=
 | genRelcstr16 : forall (a d b c e f : nat) (l : list nat), d = c /\ a::l = [b;c] /\ e = c /\ (*c = f  /\*) genRel14 a (S e) d f  -> genRel16 a l f .

MetaRocq Run (animateListLetAndPredGuard' genRel16 <? genRel16 ?> "genRelcstr16" [("a", <%nat%>); ("l", <%list nat%>)]  [("f", <%nat%>)] [("genRel14", ([0;2],[1;3])); ("genRel16",([0;1],[2]))] 
              [("genRel14", [<%nat%>;<%nat%>;<%nat%>;<%nat%>]); ("genRel16",[<%nat%>;<%list nat%>; <%nat%>])] [("d", <%nat%>); ("e", <%nat%>); ("f", <%nat%>); ("a", <%nat%>); ("b", <%nat%>); ("c", <%nat%>); ("l", <%list nat%>)] 
              [("genRel14",<% nat -> outcomePoly (nat * nat) -> outcomePoly (nat * nat)%>)] 50).

Compute genRelcstr16Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (4, [3])).
(*Should return successPoly 3*)
Compute genRelcstr16Animated genRel14AnimatedTopFn 5 (successPoly (nat * (list nat)) (4, [4])).
(*should return noMatch *)



Inductive append : list nat -> list nat -> list nat -> Prop := (* mode = ([1;2], [0] *)
 | appNil : forall (l1 l2 l3 : list nat), (fun x : bool => []) true = l1  /\ l2 = l3 -> append l1 l2 l3
 | appCons : forall (w : nat) (l1 l2 l3 l4 l5 : list nat), l1 = w :: l2 /\ append l2 l3 l4 /\ l5 = w :: l4 -> append l1 l3 l5.
          
MetaRocq Run (g <- getData' <? append ?> [("append", ([1;2], [0]))] ;; tmDefinition "dataApp" g).

Compute dataApp.

Definition appNilLHS :=
(tApp <%and%>
                [tApp <%eq%>
                   [tApp <%list%> [<%nat%>];
                    tApp
                      (tLam "x" <%bool%>
                         (tApp (tConstruct {| inductive_mind := <?list?>; inductive_ind := 0 |} 0 [])
                            [<%nat%>]))
                      [tConstruct {| inductive_mind := <?bool?>; inductive_ind := 0 |} 0 []];
                    tVar "l1"];
                 tApp <%eq%> [tApp <%list%> [<%nat%>]; tVar "l2"; tVar "l3"]]).
                 
Definition appConsLHS :=
(tApp <%and%>
                [tApp <%eq%>
                   [tApp <%list%> [<%nat%>]; tVar "l1";
                    tApp (tConstruct {| inductive_mind := <?list?>; inductive_ind := 0 |} 1 [])
                      [<%nat%>; tVar "w"; tVar "l2"]];
                 tApp <%and%>
                   [tApp (tVar "append") [tVar "l2"; tVar "l3"; tVar "l4"];
                    tApp <%eq%>
                      [tApp <%list%> [<%nat%>]; tVar "l5";
                       tApp (tConstruct {| inductive_mind := <?list?>; inductive_ind := 0 |} 1 [])
                         [<%nat%>; tVar "w"; tVar "l4"]]]]).
                 


(* Mode [1;2] [0] *)

MetaRocq Run (animateListLetAndPredGuard3 append <? append ?> appNilLHS "appNil" [("l2", <%list nat%>); ("l3", <%list nat%>)] [("l1", <%list nat%>)] [("append",([1;2],[0]))] [("append",[<%list nat%>;<%list nat%>;<%list nat%>])] 
               [("l1", <%list nat%>); ("l2", <%list nat%>); ("l3", <%list nat%>)] [] 50). 


           
MetaRocq Run (animateListLetAndPredGuard3 append <? append ?> appConsLHS "appCons" [("l3", <%list nat%>); ("l5", <%list nat%>)] [("l1", <%list nat%>)] [("append",([1;2],[0]))] [("append",[<%list nat%>;<%list nat%>;<%list nat%>])] 
               [("l1", <%list nat%>); ("l2", <%list nat%>);("l3", <%list nat%>); ("l4", <%list nat%>);("l5", <%list nat%>); ("w", <%nat%>)] [("append", <% nat -> outcomePoly ((list nat) * (list nat)) -> outcomePoly (list nat) %>)] 50). 




Definition appendIndData :=
[((("append", <%prod (list nat) (list nat) %>), <%list nat%>), [("appNil", []); ("appCons", ["append"])])].


MetaRocq Run (mkBigFixpt "append" appendIndData <?append?> 50).



(* Mode [0;2] [1] *)

MetaRocq Run (animateListLetAndPredGuard3 append <? append ?> appNilLHS "appNil'" [("l1", <%list nat%>); ("l3", <%list nat%>)] [("l2", <%list nat%>)] [("append",([0;2],[1]))] [("append",[<%list nat%>;<%list nat%>;<%list nat%>])] 
               [("l1", <%list nat%>); ("l2", <%list nat%>); ("l3", <%list nat%>)] [] 50). 


           
MetaRocq Run (animateListLetAndPredGuard3 append <? append ?> appConsLHS "appCons'" [("l1", <%list nat%>); ("l5", <%list nat%>)] [("l3", <%list nat%>)] [("append",([0;2],[1]))] [("append",[<%list nat%>;<%list nat%>;<%list nat%>])] 
               [("l1", <%list nat%>); ("l2", <%list nat%>);("l3", <%list nat%>); ("l4", <%list nat%>);("l5", <%list nat%>); ("w", <%nat%>)] [("append", <% nat -> outcomePoly ((list nat) * (list nat)) -> outcomePoly (list nat) %>)] 50). 




Definition append'IndData :=
[((("append", <%prod (list nat) (list nat) %>), <%list nat%>), [("appNil'", []); ("appCons'", ["append"])])].


MetaRocq Run (mkBigFixpt "append'" append'IndData <?append?> 50).




(* Mode [0;1] [2] *)

MetaRocq Run (animateListLetAndPredGuard3 append <? append ?> appNilLHS "appNil''" [("l1", <%list nat%>);("l2", <%list nat%>)] [("l3", <%list nat%>)] [("append",([0;1],[2]))] [("append",[<%list nat%>;<%list nat%>;<%list nat%>])] 
               [("l1", <%list nat%>); ("l2", <%list nat%>); ("l3", <%list nat%>)] [] 50). 


           
MetaRocq Run (animateListLetAndPredGuard3 append <? append ?> appConsLHS "appCons''" [("l1", <%list nat%>); ("l3", <%list nat%>)] [("l5", <%list nat%>)] [("append",([0;1],[2]))] [("append",[<%list nat%>;<%list nat%>;<%list nat%>])] 
               [("l1", <%list nat%>); ("l2", <%list nat%>);("l3", <%list nat%>); ("l4", <%list nat%>);("l5", <%list nat%>); ("w", <%nat%>)] [("append", <% nat -> outcomePoly ((list nat) * (list nat)) -> outcomePoly (list nat) %>)] 50). 




Definition append''IndData :=
[((("append", <%prod (list nat) (list nat) %>), <%list nat%>), [("appNil''", []); ("appCons''", ["append"])])].


MetaRocq Run (mkBigFixpt "append''" append''IndData <?append?> 50).



(* Mode [1;2] [0]*)
Compute appendAnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([7;8], [8;7;9;7;8])).
Compute appendAnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([8;7;9;7;8], [8;7;9;7;8])).

Compute appendAnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([5;7;8], [8;7;9;7;8])).

(* Mode [0;2] [1] *) 
Compute append'AnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([8;7], [8;7;9;7;8])).
Compute append'AnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([8;7;9;7;8], [8;7;9;7;8])).

Compute append'AnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([8;7;9;7;5], [8;7;9;7;8])).
Compute append'AnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([8;6], [8;7;9;7;8])).

(* Mode [0;1] [2] *) 
Compute append''AnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([8;7], [8;7;9;7;8])).
Compute append''AnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([], [8;7;9;7;8])).


Inductive even : nat -> bool -> Prop := (* mode = ([0], [1] *)
 | even0 : forall (w : nat), w = 0 -> even w true 
 | evenSucc : forall (w w1 : nat), odd w true /\ w1 = (S w) -> even w1 true
with odd : nat -> bool -> Prop :=
 | oddSucc : forall (w w1 : nat), even w true /\ w1 = (S w) -> odd w1 true. 
 
 
 
 
 
 
Inductive type : Type :=
| N : type
| Arr : type -> type -> type.
Inductive term : Type :=
| Con : nat -> term
| Add : term -> term -> term
| Var : nat -> term
| App : term -> term -> term
| Abs : type -> term -> term.



Inductive typing Γ : term -> type -> Prop := (* Mode [0], [1]  = type inference, Mode [0;1] [] = type checking *) 
| TCon : forall n, typing Γ (Con n) N
| TAdd : forall e1 e2,
typing Γ e1 N -> typing Γ e2 N ->
typing Γ (Add e1 e2) N
| TAbs : forall e t1 t2,
typing (t1 :: Γ) e t2 ->
typing Γ (Abs t1 e) (Arr t1 t2)
| TVar : forall x t,
lookup Γ x t -> typing Γ (Var x) t
| TApp : forall e1 e2 t1 t2,
typing Γ e2 t1 -> typing Γ e1 (Arr t1 t2) ->
typing Γ (App e1 e2) t2
with lookup Γ : nat -> type -> Prop :=
 | lookupFn0 : forall (n : nat), n = 0 -> lookup Γ n N
 | lookUpFnRec : forall (n m : nat) (t : type) , n = S m /\ lookup Γ m t -> lookup Γ n (Arr N t).  
 
Inductive append' : list nat -> list nat -> list nat -> Prop := (* mode = ([1;2], [0] *)
 | appNil' : forall (l1 l2  : list nat), l1 = [] -> append' l1 l2 l2
 | appCons' : forall (w : nat) (l1 l2 l3 l4 l5 : list nat), l1 = w :: l2 /\ append' l2 l3 l4 /\ l5 = w :: l4 -> append' l1 l3 l5.
                                                     
Inductive rtc : (nat -> nat -> bool) -> nat -> nat -> Prop :=
 | rtcRef : forall (n m : nat) (rel : nat -> nat -> bool), n = m -> rtc rel n n
 | rtcTrans : forall (a b c : nat) (rel : nat -> nat -> bool), (rel a b = true) /\ (rel b c = true) -> rtc rel a c.               
 
 
 
 
 
 
 
 