Require Import Animation.animationModulesIntegration2.
Require Import Animation.animationModulesFixPt.


Require Import Animation.animationModulesSimplEq.

Require Import Animation.utils2.
Require Import Animation.animationModulesPatMat.

Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.


Import MetaRocqNotations.
(*
Set Universe Polymorphism.
Unset Strict Universe Declaration.
*)
Local Open Scope nat_scope.
Open Scope bs.
Print option.







Unset Universe Checking.

                      
Definition animateListLetAndPredGuard10 {A : Type} (ind : A) (kn : kername) (cstrNm : string) (inVars : list (prod string term))  (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=
bigConj <- general.animate2 kn ;;
let listAllConjs := getListConjAll bigConj in
let gConjsEq := filterConjsEq listAllConjs in
(*
lAC' <- tmEval all listAllConjs ;;
*)
(*tmPrint lAC';;*)

lConjs' <- (getSortedOrientedConjsLet modes listAllConjs [] [] [] (map fst inVars) fuel) ;;
lc'' <- tmEval all lConjs' ;;
tmPrint lc'';;
let lConjs := removeDuplicateDefs (attachOutputVarToSortedConjs lConjs' allVarTpInf modes predTypeInf) (map fst inVars) in
(*
gConjs' <- (getSortedOrientedConjsGuard modes listAllConjs [] [] [] (map fst inVars) fuel) ;;
gConjs <- tmEval (all) gConjs' ;;
*)

let gConjsPred := filterConjsPred' (attachOutputVarToSortedConjs listAllConjs allVarTpInf modes predTypeInf)  in

(*tmPrint lConjs;;
tmPrint gConjsEq;;*)
t <- animateListLetAndPredGuard ind kn lConjs gConjsEq gConjsPred inVars outVars (modes) (predTypeInf) (allVarTpInf) (lhsPreds) fuel ;;
t'' <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption t)) ;;
(*
tmPrint t'';;
*)
(*
f <- tmUnquote t'' ;;
tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (String.append cstrNm "Animated") (Some hnf) ;;
*)
tmReturn t''.

Set Universe Checking.








Inductive state' : Type :=
| stCons.

Definition state := state'.


Inductive trivialRel : (state) ->  bool ->  bool -> Prop :=
 | trivCl2 : forall f n m, m = n ->  trivialRel f m n.

MetaRocq Run (myT <-animateListLetAndPredGuard10 trivialRel <? trivialRel ?> "trivCl2" [("f",<%state%>); ("m", <%bool%>)] [("n", <%bool%>)] [("trivialRel",([0;1],[2]))] [("trivialRel",[<%state%>; <%bool%>;<%bool%>])] 
               [("f",<%state%>); ("m", <%bool%>);("n", <%bool%>)] [] 100 ;; tmDefinition "wrongT" myT).

Compute wrongT.


Inductive trivialRel' : (state') ->  bool ->  bool -> Prop :=
 | trivCl2' : forall f n m, m = n ->  trivialRel' f m n.

MetaRocq Run (myT <-animateListLetAndPredGuard10 trivialRel' <? trivialRel' ?> "trivCl2'" [("f",<%state'%>); ("m", <%bool%>)] [("n", <%bool%>)] [("trivialRel",([0;1],[2]))] [("trivialRel",[<%state%>; <%bool%>;<%bool%>])] 
               [("f",<%state'%>); ("m", <%bool%>);("n", <%bool%>)] [] 100 ;; tmDefinition "rightT" myT).

Compute rightT.

MetaRocq Run (f <- tmUnquote rightT ;; tmPrint f).

MetaRocq Run (f <- tmUnquote wrongT ;; tmPrint f).


