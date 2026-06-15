
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

Definition idFn (A : Type) (x : A) := x.
(** ** Integration of All Animation Pieces
    This section combines the various animation strategies into a unified framework
    that handles let-bindings, pattern matches, partial application, and complex conjunctions. *)





(** Animate any conjunction, handling both variable equalities and pattern matches.
    Dispatches to appropriate animation strategy based on conjunction structure. *)
Definition animateAnyLet {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (inputTm : term) (inputTp : term)
                                 (inputVars : list string) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term))  (fuel : nat) : TemplateMonad term :=

outputTm <- tmEval all (tVar (fst (snd conjunct'))) ;;
outputTp <- tmEval all ((snd (snd conjunct'))) ;;
let conjunct := fst conjunct' in

match conjunct with
 | tApp <%eq%> [typeVar; t1; t2] => match t1 with
                                    | tVar str =>  match inputVars with 
                                                    | [] => tmReturn (tApp <%successPoly%> [typeVar;t2])
                                                    | h :: rest => genFunAnimateEqPartialLetClause' ind kn conjunct inputTm inputTp outputTm outputTp inputVars fuel
                                                   end 
                                    | tApp (tConstruct ind_type k lst) lstArgs => extractPatMatBindersPartial' ind kn conjunct inputTm inputTp outputTm outputTp inputVars fuel
                                    | _ => tmFail "incorrect Conj shape"
                                    end
 
 | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) _lstArgs => match (fst (getModeFmLst indNm modes)) with
                                                                                         | [] =>  animatePredicateEmptyIn (ind) (kn) (conjunct') (modes) (predTypeInf) (allVarTpInf) (fuel)
                                                                                         | _ => animatePredicate (ind) (kn) (conjunct') (modes) (predTypeInf) (allVarTpInf) (fuel)
                                                                                         end


 | tApp (tVar indNm) _lstArgs => match (fst (getModeFmLst indNm modes)) with
                                  | [] =>  animatePredicateEmptyIn (ind) (kn) (conjunct') (modes) (predTypeInf) (allVarTpInf) (fuel)
                                  | _ => animatePredicate (ind) (kn) (conjunct') (modes) (predTypeInf) (allVarTpInf) (fuel)
                                  end
                                                                                         
 
 | _ => tmFail "incorrect Conj shape"
end.






(*

Definition animateOneConjAnyLet' (outputVarNm : string) (outputVarTp : term) (inputVarsLst : list (prod term term)) (animationFn : term) (partialLetfn : term -> term) : (term -> term) :=
 match inputVarsLst with
  | [] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [tVar "fuel"]) (tApp <%outcomePoly%> [outputVarTp]))  t) )
  | [h] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); fst h]) (tApp <%outcomePoly%> [outputVarTp])) t ))
  | _ =>  (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); (tApp (mkJoinOutcomeTm (map snd inputVarsLst)) (map fst inputVarsLst))]) (tApp <%outcomePoly%> [outputVarTp])) t))
 end.

*)



Definition animateOneConjAnyLet' (outputVarNm : string) (outputVarTp : term) (inputVarsLst : list (prod term term)) (animationFn : term) (partialLetfn : term -> term) : (term -> term) :=
 match inputVarsLst with
  | [] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (animationFn) (tApp <%outcomePoly%> [outputVarTp]))  t) )
  | [h] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); fst h]) (tApp <%outcomePoly%> [outputVarTp])) t ))
  | _ =>  (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); (tApp (mkJoinOutcomeTm (map snd inputVarsLst)) (map fst inputVarsLst))]) (tApp <%outcomePoly%> [outputVarTp])) t))
 end.
 
Definition animateOneConjAnyLetPredEmptyIn' (outputVarNm : string) (outputVarTp : term) (inputVarsLst : list (prod term term)) (animationFn : term) (partialLetfn : term -> term) : (term -> term) :=
 match inputVarsLst with
  | [] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 ((tApp animationFn [(tVar "fuel"); <%successPoly true%>])) (tApp <%outcomePoly%> [outputVarTp]))  t) )
  | [h] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); fst h]) (tApp <%outcomePoly%> [outputVarTp])) t ))
  | _ =>  (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); (tApp (mkJoinOutcomeTm (map snd inputVarsLst)) (map fst inputVarsLst))]) (tApp <%outcomePoly%> [outputVarTp])) t))
 end. 

Print mkLstTm.


Definition animateOneConjAnyLet {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (inputVarsLst : list (prod string term)) (partialLetfn : term -> term) 
                                           (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=



let inputTm := mkProdTmVars inputVarsLst in
let inputTp := mkProdTypeVars inputVarsLst in
let inputVarsLstTm := mkLstTm inputVarsLst in
outputVarNm <- tmEval all ((fst (snd conjunct'))) ;;
outputVarTp <- tmEval all ((snd (snd conjunct'))) ;;   
animationFn <-  animateAnyLet (ind) (kn) (conjunct') (inputTm) (inputTp) (map fst inputVarsLst) (modes) (predTypeInf) (allVarTpInf) fuel ;;
                                                                                                                  
tmReturn (animateOneConjAnyLet' (outputVarNm) (outputVarTp) (inputVarsLstTm) (animationFn) (partialLetfn)).
                                                                                        
                                 




                               



Definition animateOneConjPredGuard {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (inputVarsLst : list (prod string term)) (partialGuard : term) 
                                           (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad term :=
let inputTm := mkProdTmVars inputVarsLst in
let inputTp := mkProdTypeVars inputVarsLst in
let inputVarsLstTm := mkLstTm inputVarsLst in
inputTm' <- tmEval all inputTm;;
inputTp' <- tmEval all inputTp;;
outputVarNm <- tmEval all ((fst (snd conjunct'))) ;;
outputVarTp <- tmEval all ((snd (snd conjunct'))) ;;  

animationFn <- animateAnyLet (ind) (kn) (conjunct') (inputTm) (inputTp)
                                 (map fst inputVarsLst) (modes) (predTypeInf) (allVarTpInf) fuel ;;
                                 
                                 tmReturn (tApp <%compOutcomeBool%> [partialGuard ; tApp (typeToBoolEqOutcome outputVarTp (typeToBoolEq outputVarTp)) [tVar outputVarNm ; 
                                 (
                                 (tApp animationFn [(tVar "fuel"); (tApp (mkJoinOutcomeTm (map snd inputVarsLst)) (map fst inputVarsLstTm))])) ]]).




Definition getConjInputVarLst (conjunct' : (term * (string * term))) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (prod string term) :=
let conjunct := fst conjunct' in
match conjunct with
 | tApp <%eq%> [typeVar; t1; t2] => lookUpVars (extractOrderedVars t2) allVarTpInf
 | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => let mode := getModeFmLst indNm modes in
                     
                                                                                        let predInArgsTm := getInArgs' mode lstArgs in
                     
                                                                                        lookUpVars (extractOrderedVarsfmLst predInArgsTm) allVarTpInf 
 
 
 | tApp (tVar indNm) lstArgs => let mode := getModeFmLst indNm modes in
                     
                                let predInArgsTm := getInArgs' mode lstArgs in
                     
                                lookUpVars (extractOrderedVarsfmLst predInArgsTm) allVarTpInf 

 
 | _ => [] 
end.



Definition animateOneConjLetCl {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
let  inputVarsLst := getConjInputVarLst conjunct' allVarTpInf (modes) (predTypeInf) in
animateOneConjAnyLet ind kn conjunct' inputVarsLst partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel.

Definition animateOneConjPredGuardCl {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (partialGuard : term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term) :=

let  inputVarsLst := getConjInputVarLst conjunct' allVarTpInf (modes) (predTypeInf) in
animateOneConjPredGuard ind kn conjunct' inputVarsLst partialGuard (modes) (predTypeInf) (allVarTpInf) fuel.

Fixpoint animateListConjLetCl {A : Type} (ind : A) (kn : kername) (conjs : list (term * (string * term))) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
match conjs with
 | [] => tmReturn partialLetfn
 | h :: t => lFn' <- animateOneConjLetCl ind kn h partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel ;; animateListConjLetCl ind kn t lFn' (modes) (predTypeInf) (allVarTpInf) fuel
end.



Fixpoint animateListConjPredGuardCl {A : Type} (ind : A) (kn : kername) (conjs : list (term * (string * term))) (partialGuard : term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term) :=
match conjs with
 | [] => tmReturn partialGuard
 | h :: t => pg <- animateOneConjPredGuardCl ind kn h partialGuard (modes) (predTypeInf) (allVarTpInf) fuel ;; animateListConjPredGuardCl ind kn t pg (modes) (predTypeInf) (allVarTpInf) fuel
end.




Fixpoint animateListConjEqGuard (conj : list term) : term :=
  match conj with
  | [] => <% true %>
  | h :: t =>
    match animateListConjEqGuard t with
    | gt => animateOneConjEqGuard h gt
    end
  end.


Print animateOneConjEqGuard.


Definition genFunAnimateEqPartialGuardCon' {A : Type} (induct : A) (kn : kername) (gConjsEq : list term)  (inputTm : term) (inputTp : term)  (outputTm : term) (outputTp : term) (fuel : nat) : TemplateMonad term :=


  (let postOut' := (constrFnBodyGuardCon outputTm outputTp

    (animateListConjEqGuard (gConjsEq) )) in
    

    let postOutType' := tApp <% @option %> [outputTp] in
    
    let postInType' := inputTp in
    
    let postIn' := inputTm in
    
    let postIn := tApp <%successPoly%> [postInType'; postIn'] in
    let postInType := tApp <%outcomePoly%> [postInType'] in

    let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
    let postOutType := tApp <%outcomePoly%> [postOutType'] in






     t0 <- constrFunAnimateEq induct postIn' postInType' postOut' postOutType'  fuel ;;
      
     let t1 := (tApp <%optionToOutcome%> [postInType'; outputTp; t0]) in
     t' <- tmEval all (removeopTm (DB.deBruijnOption t1)) ;;
     tmReturn t').

Definition animateListConjGuardEq {A : Type} (induct : A) (kn : kername) (gConjsEq : list term) (allVarTpInf : list (prod string term))  (outVars : list (prod string term)) (fuel : nat) : TemplateMonad term :=
genFunAnimateEqPartialGuardCon' induct kn gConjsEq  (mkProdTmVars allVarTpInf) (mkProdTypeVars allVarTpInf) (mkProdTmVars outVars) (mkProdTypeVars outVars) fuel.


                                                  
Definition branchOutcomeBoolfn (retType : term) (succTrueRetTm : term) (succFalseRetTm : term) (noMatchRetTm : term) (fuelErrorRetTm : term) : term :=                                                  
(tLam "gcPred"
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile ["utils2"; "Animation"], "outcomePoly");
           inductive_ind := 0
         |} [])
      [<%bool%>])
   (tCase
      {|
        ci_ind :=
          {|
            inductive_mind :=
              (MPfile ["utils2"; "Animation"], "outcomePoly");
            inductive_ind := 0
          |};
        ci_npar := 1;
        ci_relevance := Relevant
      |}
      {|
        puinst :=
          puinst
            {|
              puinst := [];
              pparams := [<%bool%>];
              pcontext :=
                [{|
                   binder_name := nNamed "gcPred";
                   binder_relevance := Relevant
                 |}];
              preturn := <%nat%>
            |};
        pparams := [<%bool%>];
        pcontext :=
          pcontext
            {|
              puinst := [];
              pparams := [<%bool%>];
              pcontext :=
                [{|
                   binder_name := nNamed "gcPred";
                   binder_relevance := Relevant
                 |}];
              preturn := retType
            |};
        preturn := retType
      |} (tVar "gcPred")
      [{|
         bcontext :=
           bcontext
             {|
               bcontext := [];
               bbody :=
                 fuelErrorRetTm
             |};
         bbody :=
           fuelErrorRetTm
       |};
       {|
         bcontext :=
           bcontext
             {|
               bcontext :=
                 [{|
                    binder_name := nNamed "splitSuccCase"; binder_relevance := Relevant
                  |}];
               bbody :=
                 tCase
                   {|
                     ci_ind :=
                       {| inductive_mind := <?bool?>; inductive_ind := 0 |};
                     ci_npar := 0;
                     ci_relevance := Relevant
                   |}
                   {|
                     puinst := [];
                     pparams := [];
                     pcontext :=
                       [{|
                          binder_name := nNamed "splitSuccCase";
                          binder_relevance := Relevant
                        |}];
                     preturn := retType
                   |} (tRel 0)
                   [{|
                      bcontext := [];
                      bbody :=
                        succTrueRetTm
                    |};
                    {|
                      bcontext := [];
                      bbody :=
                       succFalseRetTm
                    |}]
             |};
         bbody :=
           tCase
             {|
               ci_ind := {| inductive_mind := <?bool?>; inductive_ind := 0 |};
               ci_npar := 0;
               ci_relevance := Relevant
             |}
             {|
               puinst :=
                 puinst
                   {|
                     puinst := [];
                     pparams := [];
                     pcontext :=
                       [{|
                          binder_name := nNamed "splitSuccCase";
                          binder_relevance := Relevant
                        |}];
                     preturn := retType
                   |};
               pparams := [];
               pcontext :=
                 pcontext
                   {|
                     puinst := [];
                     pparams := [];
                     pcontext :=
                       [{|
                          binder_name := nNamed "splitSuccCase";
                          binder_relevance := Relevant
                        |}];
                     preturn := retType
                   |};
               preturn := retType
             |} (tVar "splitSuccCase")
             [{|
                bcontext :=
                  bcontext
                    {|
                      bcontext := [];
                      bbody :=
                        succTrueRetTm
                    |};
                bbody :=
                  succTrueRetTm
              |};
              {|
                bcontext :=
                  bcontext
                    {|
                      bcontext := [];
                      bbody :=
                        succFalseRetTm
                    |};
                bbody :=
                  succFalseRetTm
              |}]
       |};
       {|
         bcontext :=
           bcontext
             {|
               bcontext := [];
               bbody :=
                 noMatchRetTm
             |};
         bbody :=
           noMatchRetTm
       |}])).
                                                  
                                                  

Definition animateListConjPredGuardBrOutBool {A : Type} (ind : A) (kn : kername) (predGuardConjs : list (term × string × term))  (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (outVars : list (prod string term)) (guardConEqAn : term) (fuel : nat) : TemplateMonad (term) :=
predGuardCon <- animateListConjPredGuardCl (ind) (kn) (predGuardConjs) <%successPoly bool true%> (modes) (predTypeInf) (allVarTpInf) (fuel) ;;
let brOutBool := branchOutcomeBoolfn (tApp <%outcomePoly%> [mkProdTypeVars outVars]) (guardConEqAn) (tApp <%noMatchPoly%> [mkProdTypeVars outVars]) (tApp <%noMatchPoly%> [mkProdTypeVars outVars]) (tApp <%fuelErrorPoly%> [mkProdTypeVars outVars]) in
tmReturn (tApp brOutBool [predGuardCon]).


Fixpoint animateListLetClLam (inVars : list (prod string term)) (fnBody : term) :=
match inVars with
| [] => fnBody

| h :: t => tLam (fst h) (tApp <%outcomePoly%> [snd h]) (animateListLetClLam t fnBody)
end.



Fixpoint splitInputs (inVars : list (string * term)) (inTerm : term) (fnBody : term) : term :=
match inVars with
| [] => fnBody
| [h] => (tLetIn {| binder_name := nNamed (fst h); binder_relevance := Relevant |}
                                 inTerm (tApp <%outcomePoly%> [(snd h)])) fnBody
| h' :: rest' =>  (tLetIn {| binder_name := nNamed (fst h'); binder_relevance := Relevant |}
                                 (tApp <% splitOutcomePolyFst %> [(snd h'); (mkProdTypeVars rest'); inTerm])  (tApp <%outcomePoly%> [(snd h')])) (splitInputs rest' (tApp <% splitOutcomePolySnd %> [(snd h'); (mkProdTypeVars rest'); inTerm]) fnBody)
end.
(*
Definition splitInputs' (inVars : list (string * term)) (fnBody : term) : term :=
splitInputs inVars (tVar "input") fnBody.                                                                    
*)
Definition splitInputs' (inVars : list (string * term)) (fnBody : term) : term :=
match inVars with
| [] => fnBody
| _ => splitInputs inVars (tVar "input") fnBody
end.
                                                                    


Check successPoly bool true.







Definition animateListLetAndPredGuard {A : Type} (ind : A) (kn : kername) (lConjs'' : list (term × (string × term))) (gConjsEq'' : list term) (gConjsPred'' : list (term × (string × term))) (inVars : list (prod string term)) (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=
lConjs <- tmEval all lConjs'';;
gConjsEq <- tmEval all gConjsEq'';;
gConjsPred <- tmEval all gConjsPred'';;
letBind <- animateListConjLetCl  (ind) kn  lConjs  (fun t : term => t) (modes) (predTypeInf) (allVarTpInf) (fuel) ;;
gFun <- animateListConjGuardEq ind kn gConjsEq allVarTpInf outVars fuel ;;
let guardConEqAn := (tApp gFun [tVar "fuel"; mkOutPolyProdTm (allVarTpInf)]) in 
combineGuard <- animateListConjPredGuardBrOutBool (ind) (kn) (gConjsPred) (modes) (predTypeInf) (allVarTpInf) (outVars) (guardConEqAn) (fuel);;
match inVars with
 | h :: rest => tmReturn (mkLamTp (app (mkAnimatedFnNm lhsPreds) [("fuel", <%nat%>)]) (tLam "input" (tApp <%outcomePoly%> [mkProdTypeVars inVars])(splitInputs' inVars (letBind combineGuard))))
 | [] => tmReturn (mkLamTp (app (mkAnimatedFnNm lhsPreds) [("fuel", <%nat%>)]) (tLam "input" (tApp <%outcomePoly%> [<%bool%>]) ((*tLetIn {| binder_name := nNamed "input"; binder_relevance := Relevant |} <%successPoly bool true%>  <%outcomePoly bool%> *) (splitInputs' inVars (letBind combineGuard)))))

end.

Print tLet. 











Fixpoint filterConjsEq (lst : list term) : list term :=
match lst with
| [] => []
| (tApp <%eq%> [typeVar; t1; t2]) :: rest =>  (tApp <%eq%> [typeVar; t1; t2]) :: filterConjsEq rest
                                             
| _h :: rest => filterConjsEq rest
end.
Fixpoint filterConjsPred (lst : list term) : list term :=
match lst with
| [] => []
| (tApp <%eq%> [typeVar; t1; t2]) :: rest =>  filterConjsPred rest
   
| (tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs) :: rest => (tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs) :: filterConjsPred rest

| (tApp (tVar indNm) lstArgs) :: rest => (tApp (tVar indNm) lstArgs) :: filterConjsPred rest

| _h :: rest => filterConjsPred rest
end.

(** Sort and orient conjunctions for animation.
    Separates guard conditions from let-binding equalities and orients equations
    so that known variables appear on the right. *)
Definition hasRightShape (t : term) : bool :=
match t with
| tVar str => true
| tApp (tConstruct ind_type k lst) lstArgs => true
| _ => false
end.   
Print getModeFmLst.
Fixpoint mklhsProdType2NonMonad (lhsIndPre : list (term * term)) :  term :=
  match lhsIndPre with
  | [] =>  <%bool%>
  | [h] =>  (snd h)
  | h :: t =>
      let res := mklhsProdType2NonMonad t in
       (tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; res])
  end.



(* Construct a product term from a list of term-type pairs. *)
Fixpoint mklhsProdTm2NonMonad (lhsIndPre : list (term * term)) : term :=
  match lhsIndPre with
  | [] =>  <%true%>
  | [h] =>  (fst h)
  | h :: t =>
      let res := mklhsProdTm2NonMonad t in
      let resT := mklhsProdType2NonMonad t in
       (tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
                     [snd h; resT; fst h; res])
                     
 end.  
 

Fixpoint getPredTpFmLst (indNm : string) (predTypeInf : list (string * (list term))) : list term :=
match predTypeInf with
| [] => []
| h :: rest => if String.eqb indNm (fst h) then (snd h) else getPredTpFmLst indNm rest
end.
         
Definition rewritePredConj (conj' : term) (modes : list (string * (list nat * list nat))) (predTypeInf : list (string * (list term))) : term :=
match conj' with
| tApp <%eq%> [typeVar; t1; t2] => conj'
| tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => match fst (getModeFmLst indNm modes) with
                                                                                        | [] => let outputType := mklhsProdType2NonMonad (crossList lstArgs (getPredTpFmLst indNm predTypeInf)) in 
                                                                                                let outputTm := mklhsProdTm2NonMonad (crossList lstArgs (getPredTpFmLst indNm predTypeInf)) in
                                                                                                 tApp <%eq%> [tApp <%outcomePoly%> [outputType] ; tApp <%successPoly%> [outputType; outputTm] ; tApp (tVar (String.append indNm "AnimatedTopFn")) [tVar "fuel"]]
                                                                                        
                                                                                        | _nonEmpty => match snd (getModeFmLst indNm modes) with
                                                                                                       | [] => let outputType := <%bool%> in 
                                                                                                               let outputTm := <%true%> in
                                                                                                               let inputType := mklhsProdType2NonMonad (crossList lstArgs (getPredTpFmLst indNm predTypeInf)) in 
                                                                                                               let inputTm := mklhsProdTm2NonMonad (crossList lstArgs (getPredTpFmLst indNm predTypeInf)) in
                                                                                                 
                                                                                                               tApp <%eq%> [tApp <%outcomePoly%> [outputType] ; tApp <%successPoly%> [outputType; outputTm] ; tApp (tVar (String.append indNm "AnimatedTopFn")) [tVar "fuel"; tApp <%successPoly%> [inputType; inputTm]]]
                                                                                                               
                                                                                                       | _ => conj'
                                                                                                       end
                                                                                       end
 | tApp (tVar indNm) lstArgs =>                                                        match fst (getModeFmLst indNm modes) with
                                                                                        | [] => let outputType := mklhsProdType2NonMonad (crossList lstArgs (getPredTpFmLst indNm predTypeInf)) in 
                                                                                                let outputTm := mklhsProdTm2NonMonad (crossList lstArgs (getPredTpFmLst indNm predTypeInf)) in
                                                                                                 tApp <%eq%> [tApp <%outcomePoly%> [outputType] ; tApp <%successPoly%> [outputType; outputTm] ; tApp (tVar (String.append indNm "AnimatedTopFn")) [tVar "fuel"]]
                                                                                        
                                                                                        | _nonEmpty => match snd (getModeFmLst indNm modes) with
                                                                                                       | [] => let outputType := <%bool%> in 
                                                                                                               let outputTm := <%true%> in
                                                                                                               let inputType := mklhsProdType2NonMonad (crossList lstArgs (getPredTpFmLst indNm predTypeInf)) in 
                                                                                                               let inputTm := mklhsProdTm2NonMonad (crossList lstArgs (getPredTpFmLst indNm predTypeInf)) in
                                                                                                 
                                                                                                               tApp <%eq%> [tApp <%outcomePoly%> [outputType] ; tApp <%successPoly%> [outputType; outputTm] ; tApp (tVar (String.append indNm "AnimatedTopFn")) [tVar "fuel"; tApp <%successPoly%> [inputType; inputTm]]]
                                                                                                               
                                                                                                       | _ => conj'
                                                                                                       end
                                                                                       end



| _ => conj'
end.                                                                                                                          
                                 

Fixpoint getSortedOrientedConjs (modes : list (string * ((list nat) * (list nat)))) (currentConjs : list term) (remConjs : list term) (sortedConjs : list term) (guardConjs : list term) (kv : (list string)) (fuel : nat) : TemplateMonad (prod (list term) (list term)) :=
match fuel with
 | 0 => if andb (isEmptyLst remConjs) (isEmptyLst currentConjs) then tmReturn (sortedConjs, guardConjs) else tmFail "insufficient fuel to sort conjs"
 | S n => if (andb (isEmptyLst remConjs) (isEmptyLst currentConjs)) then tmReturn (sortedConjs, guardConjs) else
           match currentConjs with
            | [] => getSortedOrientedConjs modes remConjs [] sortedConjs guardConjs kv n
            | conj' :: t => match conj' with
                        | tApp <%eq%> [typeVar; t1; t2] => if andb (isListSubStr (extractOrderedVars t1) kv) (isListSubStr (extractOrderedVars t2) kv) then
                                                            getSortedOrientedConjs modes t remConjs sortedConjs (conj' :: guardConjs) kv n else
                                                            (if (andb (isListSubStr (extractOrderedVars t1) kv) (hasRightShape t2)) then 
                                                            
                                                            getSortedOrientedConjs modes t remConjs (tApp <%eq%> [typeVar; t2; t1] :: sortedConjs) (guardConjs) (app (extractOrderedVars t2) kv) n else
                                                            (if  (andb (isListSubStr (extractOrderedVars t2) kv) (hasRightShape t1)) then getSortedOrientedConjs modes t remConjs (tApp <%eq%> [typeVar; t1; t2] :: sortedConjs) (guardConjs) (app (extractOrderedVars t1) kv) n else
                                                            (getSortedOrientedConjs modes t (conj' :: remConjs) (sortedConjs) (guardConjs) (kv) n)))
                        
                        | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => if isListSubStr (concat (map extractOrderedVars lstArgs)) kv then (getSortedOrientedConjs modes t (remConjs) (sortedConjs) (conj':: guardConjs) (kv) n) else
                                                                                                              if isListSubStr (extractOrderedVarsfmLst (getInArgs indNm modes lstArgs)) kv then getSortedOrientedConjs modes t remConjs (conj' :: sortedConjs) (guardConjs) (app (extractOrderedVarsfmLst (getOutArgs indNm modes lstArgs)) kv) n else 
                                                                                                              (getSortedOrientedConjs modes t (conj' :: remConjs) (sortedConjs) (guardConjs) (kv) n)                             
                        
                        
                        
                        | tApp (tVar indNm) lstArgs => if isListSubStr (concat (map extractOrderedVars lstArgs)) kv then (getSortedOrientedConjs modes t (remConjs) (sortedConjs) (conj':: guardConjs) (kv) n) else
                                                                                                              if isListSubStr (extractOrderedVarsfmLst (getInArgs indNm modes lstArgs)) kv then getSortedOrientedConjs modes t remConjs (conj' :: sortedConjs) (guardConjs) (app (extractOrderedVarsfmLst (getOutArgs indNm modes lstArgs)) kv) n else 
                                                                                                              (getSortedOrientedConjs modes t (conj' :: remConjs) (sortedConjs) (guardConjs) (kv) n)                             
                        
                        
                        | _ => tmFail "incorrect conj shape"
                        end
           end
end.

(** Extract just the let-binding conjunctions (in sorted order). *)
Definition getSortedOrientedConjsLet (modes : list (string * ((list nat) * (list nat)))) (currentConjs : list term) (remConjs : list term) (sortedConjs : list term) (guardConjs : list term) (kv : (list string)) (fuel : nat) : TemplateMonad (list term) :=
sConjs <- getSortedOrientedConjs modes (currentConjs) (remConjs) (sortedConjs) (guardConjs) (kv) (fuel) ;;
lConjs <- tmEval all (rev (fst sConjs));;
tmReturn lConjs.

(** Extract just the guard conjunctions. *)
Definition getSortedOrientedConjsGuard (modes : list (string * ((list nat) * (list nat)))) (currentConjs : list term) (remConjs : list term) (sortedConjs : list term) (guardConjs : list term) (kv : (list string)) (fuel : nat) : TemplateMonad (list term) :=
sConjs <- getSortedOrientedConjs modes (currentConjs) (remConjs) (sortedConjs) (guardConjs) (kv) (fuel) ;;
gConjs <- tmEval all (snd sConjs);;
tmReturn gConjs.

Definition getConjAllOutputVars (conj : term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (prod string term) :=
match conj with
 | tApp <%eq%> [typeVar; t1; t2] => lookUpVars (extractOrderedVars t1) allVarTpInf
 | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => let mode := getModeFmLst indNm modes in
                     
                                                                                        let predOutArgsTm := getOutArgs' mode lstArgs in
                     
                                                                                        lookUpVars (extractOrderedVarsfmLst predOutArgsTm) allVarTpInf 
 
 
 | tApp (tVar indNm) lstArgs => let mode := getModeFmLst indNm modes in
                     
                                                                                        let predOutArgsTm := getOutArgs' mode lstArgs in
                     
                                                                                        lookUpVars (extractOrderedVarsfmLst predOutArgsTm) allVarTpInf 

 
 | _ => [] 
end.

Fixpoint attachOutputVarLst (lconjs : list term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : (list (prod term (list (prod string term)))) :=
match lconjs with
 | [] => []
 | h :: t => (h, getConjAllOutputVars h allVarTpInf modes predTypeInf) :: attachOutputVarLst t allVarTpInf modes predTypeInf
end. 

Fixpoint attachOutputVar' (lconjt : term) (lconjV : (((list (string * term))))) : list (term * (string * term)) :=
match (lconjV) with
| [] => []
| (h :: rest) => ((lconjt), h) :: attachOutputVar' lconjt rest
end. 

Fixpoint attachOutputVar (lconjs : (list (prod term (list (prod string term))))) : list (term * (string * term)) := 
match lconjs with
| [] => []
| h :: rest => app (attachOutputVar' (fst h) (snd h)) (attachOutputVar rest)
end.  
Definition attachOutputVarToSortedConjs (lconjs : list term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (term * (string * term)) :=
attachOutputVar (attachOutputVarLst lconjs allVarTpInf modes predTypeInf). 

Search (string -> list string -> bool).


Fixpoint removeDuplicateDefs (lconjs : list (term * (string * term))) (kv : list string) : list (term * (string * term))  :=
match lconjs with
| [] => []
| h :: rest => if (inStrLst (fst (snd h)) kv) then removeDuplicateDefs rest kv  else h :: (removeDuplicateDefs rest ((fst (snd h)) :: kv)) 
end.

Fixpoint keepDuplicateDefs (lconjs : list (term * (string * term))) (kv : list string) : list (term * (string * term))  :=
match lconjs with
| [] => []
| h :: rest => if (inStrLst (fst (snd h)) kv) then h :: (keepDuplicateDefs rest kv)  else (keepDuplicateDefs rest ((fst (snd h)) :: kv)) 
end.

Fixpoint filterConjsPred' (lst : list (term * (string * term))) : list (term * (string * term)) :=
match lst with
| [] => []
| ((tApp <%eq%> [typeVar; t1; t2]), (str,t'')) :: rest => filterConjsPred' rest
| ((tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs), (str, t2)) :: rest => ((tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs), (str, t2)) :: filterConjsPred' rest

| ((tApp (tVar indNm) lstArgs), (str, t2)) :: rest => ((tApp (tVar indNm) lstArgs), (str, t2)) :: filterConjsPred' rest


| _h :: rest => filterConjsPred' rest
end.