
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


(** ** Integration of All Animation Pieces
    This section combines the various animation strategies into a unified framework
    that handles let-bindings, pattern matches, partial application, and complex conjunctions. *)



(** Sort and orient conjunctions for animation.
    Separates guard conditions from let-binding equalities and orients equations
    so that known variables appear on the right. *)
    

Fixpoint getSortedOrientedConjs (modes : list (string * ((list nat) * (list nat)))) (currentConjs : list term) (remConjs : list term) (sortedConjs : list term) (guardConjs : list term) (kv : (list string)) (fuel : nat) : TemplateMonad (prod (list term) (list term)) :=
match fuel with
 | 0 => if andb (isEmptyLst remConjs) (isEmptyLst currentConjs) then tmReturn (sortedConjs, guardConjs) else tmFail "insufficient fuel to sort conjs"
 | S n => if (andb (isEmptyLst remConjs) (isEmptyLst currentConjs)) then tmReturn (sortedConjs, guardConjs) else
           match currentConjs with
            | [] => getSortedOrientedConjs modes remConjs [] sortedConjs guardConjs kv n
            | conj' :: t => match conj' with
                        | tApp <%eq%> [typeVar; t1; t2] => if andb (isListSubStr (extractOrderedVars t1) kv) (isListSubStr (extractOrderedVars t2) kv) then
                                                            getSortedOrientedConjs modes t remConjs sortedConjs (conj' :: guardConjs) kv n else
                                                            (if (isListSubStr (extractOrderedVars t1) kv) then getSortedOrientedConjs modes t remConjs (tApp <%eq%> [typeVar; t2; t1] :: sortedConjs) (guardConjs) (app (extractOrderedVars t2) kv) n else
                                                            (if  (isListSubStr (extractOrderedVars t2) kv) then getSortedOrientedConjs modes t remConjs (tApp <%eq%> [typeVar; t1; t2] :: sortedConjs) (guardConjs) (app (extractOrderedVars t1) kv) n else
                                                            (getSortedOrientedConjs modes t (conj' :: remConjs) (sortedConjs) (guardConjs) (kv) n)))
                        
                        | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => if isListSubStr (extractOrderedVars conj') kv then (getSortedOrientedConjs modes t (remConjs) (sortedConjs) (conj':: guardConjs) (kv) n) else
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




Definition animatePredicate {A : Type} (induct : A) (kn : kername) (conjunct : named_term) (outputTm : term) (outputTp : term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad term :=

match conjunct with
 | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => 
                     (*let outputTm := tVar outputVar in 
                     let outputTp := lookUpVarsOneDefBool outputVar allVarTpInf in *)
                     let mode := getModeFmLst indNm modes in
                     let predTp := getPredTp indNm predTypeInf in
                     let predInArgsTm := getInArgs' mode lstArgs in
                     let predInArgsTp := getInArgs' mode predTp in
                     let predOutArgsTm := getOutArgs' mode lstArgs in
                     let predOutArgsTp := getOutArgs' mode predTp in
                     let inputVars := extractOrderedVarsfmLst predInArgsTm in
                     let inputVarsTmTp := mkLstTm (lookUpVars inputVars allVarTpInf) in
                     let predInArgs := crossList predInArgsTm predInArgsTp in
                     let predOutArgs := crossList predOutArgsTm predOutArgsTp in
                     
                     inputVarProdTp <- mklhsProdType inputVarsTmTp ;;
                     inputVarProdTm <- mklhsProdTm inputVarsTmTp ;;
                     
                     
                     
                     
                      
                      
                      
                      predOutProdTp <- mklhsProdType predOutArgs ;;
                      predOutProdTm <- mklhsProdTm predOutArgs ;;
                      predInProdTp <- mklhsProdType predInArgs ;;
                      predInProdTm <- mklhsProdTm predInArgs ;; 
                      tIn' <- joinPatMatPolyGenFuelAwareNoLHSTm induct (inputVarProdTm) (inputVarProdTp) predInProdTm predInProdTp (String.append (snd kn) "IN") fuel ;;
                                         
                      let tIn :=  (tApp <%composeOutcomePoly%> [(inputVarProdTp); predInProdTp ; (predOutProdTp) ; tIn' ;  (tVar (String.append indNm "AnimatedTopFn"))])   in 
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  predOutProdTm predOutProdTp  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;
                      



                      let u :=
                       (tApp <%composeOutcomePoly%> [(inputVarProdTp); predOutProdTp ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      
                      u' <- DB.deBruijn u ;;
                      tmReturn u'
                     




 | _ => tmFail "incorrect inductive shape"
 end.
 

(** Animate any conjunction, handling both variable equalities and pattern matches.
    Dispatches to appropriate animation strategy based on conjunction structure. *)
Definition animateAnyLet {A : Type} (ind : A) (kn : kername) (conj : term) (inputTm : term) (inputTp : term)
                                 (outputTm : term) (outputTp : term) (inputVars : list string) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term))  (fuel : nat) : TemplateMonad term :=
match conj with
 | tApp <%eq%> [typeVar; t1; t2] => match t1 with
                                    | tVar str =>  genFunAnimateEqPartialLetClause' ind kn conj inputTm inputTp outputTm outputTp inputVars fuel
                                    | tApp (tConstruct ind_type k lst) lstArgs => extractPatMatBindersPartial' ind kn conj inputTm inputTp outputTm outputTp inputVars fuel
                                    | _ => tmFail "incorrect Conj shape"
                                    end
 
 | tApp (tInd {| inductive_mind := (_path, _indNm); inductive_ind := 0 |} []) _lstArgs => animatePredicate (ind) (kn) (conj) (outputTm) (outputTp) (modes) (predTypeInf) (allVarTpInf) (fuel)

 
 | _ => tmFail "incorrect Conj shape"
end.








Definition animateOneConjAnyLet' (outputVarNm : string) (outputVarTp : term) (inputVarsLst : list (prod term term)) (animationFn : term) (partialLetfn : term -> term) : (term -> term) :=
 match inputVarsLst with
  | [] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [tVar "fuel"]) (tApp <%outcomePoly%> [outputVarTp]))  t) )
  | [h] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); fst h]) (tApp <%outcomePoly%> [outputVarTp])) t ))
  | _ =>  (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); (tApp (mkJoinOutcomeTm (map snd inputVarsLst)) (map fst inputVarsLst))]) (tApp <%outcomePoly%> [outputVarTp])) t))
 end.



Definition animateOneConjAnyLet {A : Type} (ind : A) (kn : kername) (conj : term) (outputVarNm : string) (outputVarTp : term) (inputVarsLst : list (prod string term)) (partialLetfn : term -> term) 
                                           (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
let inputTm := mkProdTmVars inputVarsLst in
let inputTp := mkProdTypeVars inputVarsLst in
let inputVarsLstTm := mkLstTm inputVarsLst in
animationFn <-  animateAnyLet (ind) (kn) (conj) (inputTm) (inputTp)
                                 (tVar outputVarNm) (outputVarTp) (map fst inputVarsLst) (modes) (predTypeInf) (allVarTpInf) fuel ;;
tmReturn (animateOneConjAnyLet' (outputVarNm) (outputVarTp) (inputVarsLstTm) (animationFn) (partialLetfn)).

(*
Definition animatePredGuard {A : Type} (ind : A) (kn : kername) (conj : term) (inputTm : term) (inputTp : term)
                                 (outputTm : term) (outputTp : term) (inputVars : list string) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term))  (fuel : nat) : TemplateMonad term :=
match conj with
 
 
 | tApp (tInd {| inductive_mind := (_path, _indNm); inductive_ind := 0 |} []) _lstArgs => animatePredicate (ind) (kn) (conj) (outputTm) (outputTp) (modes) (predTypeInf) (allVarTpInf) (fuel)

 
 | _ => tmFail "incorrect Conj shape"
end.
*)
                              

Definition animateOneConjPredGuard {A : Type} (ind : A) (kn : kername) (conj : term) (outputVarNm : string) (outputVarTp : term) (inputVarsLst : list (prod string term)) (partialGuard : term) 
                                           (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad term :=
let inputTm := mkProdTmVars inputVarsLst in
let inputTp := mkProdTypeVars inputVarsLst in
let inputVarsLstTm := mkLstTm inputVarsLst in
inputTm' <- tmEval all inputTm;;
inputTp' <- tmEval all inputTp;;
tmPrint inputTm';;
tmPrint inputTp';;
 
match conj with
 
  | tApp (tInd {| inductive_mind := (_path, _indNm); inductive_ind := 0 |} []) _lstArgs => 
                                  animationFn <- animateAnyLet (ind) (kn) (conj) (inputTm) (inputTp)
                                 (tVar outputVarNm) (outputVarTp) (map fst inputVarsLst) (modes) (predTypeInf) (allVarTpInf) fuel ;;
                                 
                                 tmReturn (tApp <%compOutcomeBool%> [partialGuard ; tApp (typeToBoolEqOutcome outputVarTp (typeToBoolEq outputVarTp)) [tVar outputVarNm ; 
                                 (
                                 (tApp animationFn [(tVar "fuel"); (tApp (mkJoinOutcomeTm (map snd inputVarsLst)) (map fst inputVarsLstTm))])) ]])

     

  | _ => tmReturn partialGuard
  end.




Definition getConjOutputVars (conj : term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (prod string term) :=
match conj with
 | tApp <%eq%> [typeVar; t1; t2] => lookUpVars (extractOrderedVars t1) allVarTpInf
 | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => let mode := getModeFmLst indNm modes in
                     
                                                                                        let predOutArgsTm := getOutArgs' mode lstArgs in
                     
                                                                                        lookUpVars (extractOrderedVarsfmLst predOutArgsTm) allVarTpInf 
 | _ => [] 
end.
Definition getConjInputVarLst (conj : term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (prod string term) :=

match conj with
 | tApp <%eq%> [typeVar; t1; t2] => lookUpVars (extractOrderedVars t2) allVarTpInf
 | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => let mode := getModeFmLst indNm modes in
                     
                                                                                        let predInArgsTm := getInArgs' mode lstArgs in
                     
                                                                                        lookUpVars (extractOrderedVarsfmLst predInArgsTm) allVarTpInf 
 | _ => [] 
end.
Fixpoint animateOneConjAnyLetMult {A : Type} (ind : A) (kn : kername) (conj : term)
                                 (outputVars : list (prod string term)) (inputVarsLst : list (prod string term)) (partialFn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
match outputVars with
 | [] => tmReturn partialFn
 | h :: t =>  lFn' <- animateOneConjAnyLet A kn conj (fst h) (snd h) inputVarsLst partialFn (modes) (predTypeInf) (allVarTpInf) fuel ;; animateOneConjAnyLetMult ind kn conj t inputVarsLst lFn'  (modes) (predTypeInf) (allVarTpInf) fuel
end.

Fixpoint animateOneConjPredGuardMult {A : Type} (ind : A) (kn : kername) (conj : term) (outputVars : list (string * term)) (inputVarsLst : list (prod string term)) (partialGuard : term) 
                                           (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad term :=
match outputVars with
 | [] => tmReturn partialGuard
 | h :: t =>  pg <- animateOneConjPredGuard A kn conj (fst h) (snd h) inputVarsLst partialGuard (modes) (predTypeInf) (allVarTpInf) fuel ;; animateOneConjPredGuardMult ind kn conj t inputVarsLst pg (modes) (predTypeInf) (allVarTpInf) fuel
end.


Definition animateOneConjLetCl {A : Type} (ind : A) (kn : kername) (conj : term) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
let outputVars := getConjOutputVars conj allVarTpInf (modes) (predTypeInf) in
let  inputVarsLst := getConjInputVarLst conj allVarTpInf (modes) (predTypeInf) in
animateOneConjAnyLetMult ind kn conj outputVars inputVarsLst partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel.

Definition animateOneConjPredGuardCl {A : Type} (ind : A) (kn : kername) (conj : term) (partialGuard : term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term) :=
let outputVars := getConjOutputVars conj allVarTpInf (modes) (predTypeInf) in
let  inputVarsLst := getConjInputVarLst conj allVarTpInf (modes) (predTypeInf) in
animateOneConjPredGuardMult ind kn conj outputVars inputVarsLst partialGuard (modes) (predTypeInf) (allVarTpInf) fuel.

Fixpoint animateListConjLetCl {A : Type} (ind : A) (kn : kername) (conjs : list term) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
match conjs with
 | [] => tmReturn partialLetfn
 | h :: t => lFn' <- animateOneConjLetCl ind kn h partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel ;; animateListConjLetCl ind kn t lFn' (modes) (predTypeInf) (allVarTpInf) fuel
end.



Fixpoint animateListConjPredGuardCl {A : Type} (ind : A) (kn : kername) (conjs : list term) (partialGuard : term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term) :=
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
                                                  
                                                  

Definition animateListConjPredGuardBrOutBool {A : Type} (ind : A) (kn : kername) (predGuardConjs : list term)  (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (outVars : list (prod string term)) (guardConEqAn : term) (fuel : nat) : TemplateMonad (term) :=
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

Definition splitInputs' (inVars : list (string * term)) (fnBody : term) : term :=
splitInputs inVars (tVar "input") fnBody.                                                                    











Definition animateListLetAndPredGuard {A : Type} (ind : A) (kn : kername) (lConjs : list term) (gConjsEq : list term) (gConjsPred : list term) (inVars : list (prod string term)) (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=
letBind <- animateListConjLetCl  (ind) kn  lConjs  (fun t : term => t) (modes) (predTypeInf) (allVarTpInf) (fuel) ;;
gFun <- animateListConjGuardEq ind kn gConjsEq allVarTpInf outVars fuel ;;
let guardConEqAn := (tApp gFun [tVar "fuel"; mkOutPolyProdTm (allVarTpInf)]) in 
combineGuard <- animateListConjPredGuardBrOutBool (ind) (kn) (gConjsPred) (modes) (predTypeInf) (allVarTpInf) (outVars) (guardConEqAn) (fuel);;

tmReturn (mkLamTp (app (mkAnimatedFnNm lhsPreds) [("fuel", <%nat%>)]) (tLam "input" (tApp <%outcomePoly%> [mkProdTypeVars inVars])(splitInputs' inVars (letBind combineGuard)))).







Unset Universe Checking.

Fixpoint filterConjsEq (lst : list term) : list term :=
match lst with
| [] => []
| (tApp <%eq%> [typeVar; t1; t2]) :: rest => (tApp <%eq%> [typeVar; t1; t2]) :: filterConjsEq rest
| _h :: rest => filterConjsEq rest
end.
Fixpoint filterConjsPred (lst : list term) : list term :=
match lst with
| [] => []
| (tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs) :: rest => (tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs) :: filterConjsPred rest
| _h :: rest => filterConjsPred rest
end.
                      
Definition animateListLetAndPredGuard' {A : Type} (ind : A) (kn : kername) (inVars : list (prod string term))  (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=
bigConj <- general.animate2 kn ;;
let listAllConjs := getListConjAll bigConj in
lAC' <- tmEval all listAllConjs ;;
tmPrint lAC';;
lConjs' <- (getSortedOrientedConjsLet modes listAllConjs [] [] [] (map fst inVars) fuel) ;;
lConjs <- tmEval (all) lConjs' ;;
gConjs' <- (getSortedOrientedConjsGuard modes listAllConjs [] [] [] (map fst inVars) fuel) ;;
gConjs <- tmEval (all) gConjs' ;;
let gConjsEq := filterConjsEq gConjs in
let gConjsPred := filterConjsPred gConjs in
(*tmPrint lConjs;;
tmPrint gConjsEq;;*)
t <- animateListLetAndPredGuard ind kn lConjs gConjsEq gConjsPred inVars outVars (modes) (predTypeInf) (allVarTpInf) (lhsPreds) fuel ;;
t'' <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption t)) ;;
tmPrint t'';;
f <- tmUnquote t'' ;;
tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (String.append (snd kn) "Animated") (Some hnf) ;;

tmReturn t''.

Set Universe Checking.

