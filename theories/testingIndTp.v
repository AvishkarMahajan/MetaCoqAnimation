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


Inductive trivialRel : (state) -> Prop :=
 | trivCl2 : forall f, trivialRel f.

MetaRocq Run (myT <-animateListLetAndPredGuard10 trivialRel <? trivialRel ?> "trivCl2" [("f",<%state%>)] [] [("trivialRel",([0],[]))] [("trivialRel",[<%state%>])] 
               [("f",<%state%>)] [] 100 ;; tmDefinition "wrongT" myT).

Compute wrongT.

MetaRocq Run (f <- tmUnquote wrongT ;; tmPrint f).




Inductive trivialRel' : (state') ->  bool ->  bool -> Prop :=
 | trivCl2' : forall f n m, m = n ->  trivialRel' f m n.

MetaRocq Run (myT <-animateListLetAndPredGuard10 trivialRel' <? trivialRel' ?> "trivCl2'" [("f",<%state'%>); ("m", <%bool%>)] [("n", <%bool%>)] [("trivialRel",([0;1],[2]))] [("trivialRel",[<%state%>; <%bool%>;<%bool%>])] 
               [("f",<%state'%>); ("m", <%bool%>);("n", <%bool%>)] [] 100 ;; tmDefinition "rightT" myT).

Compute rightT.

MetaRocq Run (f <- tmUnquote rightT ;; tmPrint f).

MetaRocq Run (t <- tmQuote (fun (fuel : nat) (input : outcomePoly (state × bool)) =>
    let f := splitOutcomePolyFst state bool input in
    let m := splitOutcomePolySnd state bool input in
    let n :=
      optionToOutcome bool bool
        (fun fuel0 : nat =>
         match fuel0 with
         | 0 => fuelErrorPolyCstFn (outcomePoly bool) (option bool)
         | S _ =>
             defaultVal (outcomePoly bool) (outcomePoly (option bool)) (noMatchPoly (option bool))
               (dispatchInternal (outcomePoly bool) (outcomePoly (option bool))
                  [fun v2 : outcomePoly bool =>
                   match v2 with
                   | @successPoly _ m0 =>
                       Some (successPoly (option bool) (let n := m0 in if true then Some n else None))
                   | _ => None
                   end;
                   fun v2 : outcomePoly bool =>
                   match v2 with
                   | @fuelErrorPoly _ => Some (fuelErrorPoly (option bool))
                   | _ => None
                   end])
         end)
        fuel m
      in
    (fun gcPred : outcomePoly bool =>
     match gcPred with
     | @fuelErrorPoly _ => fuelErrorPoly bool
     | @successPoly _ true =>
         optionToOutcome (state × bool × bool) bool
           (fun fuel0 : nat =>
            match fuel0 with
            | 0 => fuelErrorPolyCstFn (outcomePoly (state × bool × bool)) (option bool)
            | S _ =>
                defaultVal (outcomePoly (state × bool × bool)) (outcomePoly (option bool))
                  (noMatchPoly (option bool))
                  (dispatchInternal (outcomePoly (state × bool × bool)) (outcomePoly (option bool))
                     [fun v2 : outcomePoly (state × bool × bool) =>
                      match v2 with
                      | @successPoly _ (_, (m0, n0)) =>
                          Some
                            (successPoly (option bool)
                               (if (true && Bool.eqb m0 n0)%bool then Some n0 else None))
                      | _ => None
                      end;
                      fun v2 : outcomePoly (state × bool × bool) =>
                      match v2 with
                      | @fuelErrorPoly _ => Some (fuelErrorPoly (option bool))
                      | _ => None
                      end])
            end)
           fuel
           ((fun (o0 : outcomePoly state) (o1 o2 : outcomePoly bool) =>
             joinOutcome state' (bool × bool) o0 (joinOutcome bool bool o1 o2)) f m n)
     | _ => noMatchPoly bool
     end) (successPoly bool true)) ;; tmPrint t ;; f' <- tmUnquote t;; tmPrint f').
Print rightT.

MetaRocq Run (f <- tmUnquoteTyped (nat -> outcomePoly (state × bool) -> outcomePoly bool) wrongT ;; tmPrint f).


