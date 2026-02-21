Require Import Animation.utils2.
Require Import Animation.animationModulesPatMat.

Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.


Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.






Definition typeToBoolEq (t : term) : term :=
 match t with
  | (tInd {| inductive_mind := <?nat?>; inductive_ind := 0 |} []) => <%Nat.eqb%>
  | <%bool%> => <%Bool.eqb%>
  | (tApp
         (tInd
            {|
              inductive_mind := <?list?>; inductive_ind := 0
            |} [])
         [<%nat%>]) => <%eqLstNat%>
  | _ => <% (false) %>
 end.

Definition chkEqType (t : term) : bool :=
  match t with
  | (tInd {| inductive_mind := <?nat?>; inductive_ind := 0 |} []) => true
  | <%bool%> => true
  | (tApp
         (tInd
            {|
              inductive_mind := <?list?>; inductive_ind := 0
            |} [])
         [<%nat%>]) => true
  | _ => false
 end.

Parameter inValidConj : term.

Fixpoint getListConjLetBind (bigConj : term) : list term :=

     match bigConj with
     | tApp <%and%> ls => concat (map (getListConjLetBind) ls)

  
     | tApp <%eq%> [typeT; tVar str1; tVar str2] => [tApp <% @eq %> [typeT; tVar str1; tVar str2]]

     | tApp <%eq%> [typeT; tVar str1; tApp fn lst] =>
      [tApp <%eq%> [typeT; tVar str1; tApp fn lst]]

     | tApp <%eq%> [typeT; tApp fn lst; tVar str1] =>
      [tApp <%eq%> [typeT; tApp fn lst; tVar str1]]

     | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>
      [tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst]]

     | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] =>
      [tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1]]




  
     | _ => []
     end.



(* extract list of conjuncts from big conjunction *)
Fixpoint getListConjGuardCon (bigConj : term) : list term :=
  match bigConj with
  | tApp <%and%> ls => concat (map getListConjGuardCon ls)
  | tApp <%eq%> [typeT; t1; t2] =>
      [tApp <%eq%> [typeT; t1; t2]]

  | tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs => [tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs]
  
  | _ => []
 end.

Definition getListConjAll (bigConj : term) : list term :=
  match bigConj with
  | tApp <%and%> ls => concat (map getListConjGuardCon ls)
  | tApp <%eq%> [typeT; t1; t2] =>
      [tApp <%eq%> [typeT; t1; t2]]
  | tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs => [tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs]
  | _ => []
 end.

Fixpoint filterListConj (bigConj : term) : list bool :=
 match bigConj with
  | tApp <%and%> ls => concat (map filterListConj ls)

  | tApp <%eq%> [typeT; tVar str1; tVar str2] => [chkEqType typeT]

  | tApp <%eq%> [typeT; tVar str1; tApp fn lst] =>
      [chkEqType typeT]

  | tApp <%eq%> [typeT; tApp fn lst; tVar str1] =>
      [chkEqType typeT]

  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>
      [chkEqType typeT]

  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] =>
      [chkEqType typeT]


  | tApp <%eq%> [typeT; tApp fn1 lst1; tApp fn2 lst2] =>
      [chkEqType typeT]
  | tApp <%eq%> [typeT; tApp fn1 lst1; tConstruct ind_type k lst] =>
      [chkEqType typeT]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tApp fn1 lst1] =>
      [chkEqType typeT]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tConstruct ind_type2 k2 lst2] =>
      [chkEqType typeT]
  | _ => [false]
 end.


Fixpoint extractOrderedVarsHelper (ls : list term) : list string :=
 match ls with
 | [] => []
 | (tVar str) :: t => str :: (extractOrderedVarsHelper t)
 | _ :: t => (extractOrderedVarsHelper t)
 end.




(* extract ordered list of vars from conjunct *)
Fixpoint extractOrderedVars (t : term) : list string :=
  match t with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => [str1 ; str2]
  | tApp <%eq%> [typeT; tVar str1; tApp fn lst] => str1 :: extractOrderedVarsHelper (lst)
  | tApp <%eq%> [typeT; tApp fn lst; tVar str1] => app (extractOrderedVarsHelper (lst)) [str1]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] => [str1]
  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>  [str1]

  (* Combine the pattern matches to handle fns of arbitrary arity *)

  | tVar str  => [str]
  | tApp _ lst => concat (map extractOrderedVars lst)
  | _ => []
  end.


(* Instantiate partialLetFun with identity *)



Definition animateOneConjSucc (conj : term) (partialLetfn : term -> term) : option (term -> term) :=
  match conj with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1; binder_relevance := Relevant |}
                                 (tVar str2) typeT) t))

  
  | tApp <%eq%> [typeT; tVar str1; tApp fn lstTerm] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn lstTerm) typeT) t))

  | tApp <%eq%> [typeT; tApp fn lstTerm; tVar str1] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn lstTerm) typeT) t))

  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tConstruct ind_type k lst) typeT) t))

  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tConstruct ind_type k lst) typeT) t))


  | _ => None
 end.
 
 
 
Definition flipConj (conj : term) : term :=
 match conj with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => tApp <%eq%> [typeT; tVar str2; tVar str1]
  | tApp <%eq%> [typeT; tApp fn lstTerm; tVar str1] => tApp <%eq%> [typeT; tVar str1; tApp fn lstTerm]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] => tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst]
  | t' => t'
 end.

(* Instantiate partialGuard with Identity * No need to check for known vars when animating guard condition since all
vars should be known at this point in the computation *)

 Definition animateOneConjSuccGuard (conj : term) (partialGuard : term)  :  term :=
  match conj with
  | tApp <%eq%> [typeT; t1; t2] =>
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (typeToBoolEq typeT) [t1
         ; t2]]

  | _ => <% false %>
  end.

Definition animateOneConj (conj : term) (knownVar : list string) (partialProg : term -> term) : option (list string * (term -> term)) :=
 match conj with
  | tApp <%eq%> [typeT; t1; t2] => if andb (isListSubStr (extractOrderedVars t2 ) knownVar) (negb (isListSubStr (extractOrderedVars t1 ) knownVar)) then

    (let t' := animateOneConjSucc conj partialProg in
      match t' with
      | Some t'' => Some (app knownVar (extractOrderedVars conj), t'')
      | None => None
      end)
    else (if andb (isListSubStr (extractOrderedVars t1 ) knownVar) (negb (isListSubStr (extractOrderedVars t2 ) knownVar)) then

          (let t' := animateOneConjSucc (flipConj conj) partialProg in
           match t' with
            | Some t'' => Some (app knownVar (extractOrderedVars (flipConj conj)), t'')
            | None => None
           end)
         else None)

  | _ => None
 end. 
 
Fixpoint animateListConj (conjs : (list term)) (remConjs : (list term)) (knownVar : list string)
                         (fuel : nat) (partialProg : term -> term) : term -> term :=
  match fuel with
  | 0 => partialProg
  | S n =>
    match conjs with
    | [] =>
      match remConjs with
      | [] => partialProg
      | lst => animateListConj lst nil knownVar n partialProg
      end
    | h :: t =>
      let res := animateOneConj h knownVar partialProg in
      match res with
      | Some res' => animateListConj t remConjs (fst res') n (snd res')
      | None => animateListConj t (h :: remConjs) knownVar n partialProg
      end
    end
  end.


Definition constrRetBodylst (outputTm : term) (outputTp : term) : term :=
 tApp <% @Some %> [outputTp; outputTm].

Definition constrFnBody  (outputTm : term) (outputTp : term) (letBind : term -> term)  : term :=
 (letBind (tCase {| ci_ind := {| inductive_mind := <? bool ?>; inductive_ind := 0 |}
                ; ci_npar := 0; ci_relevance := Relevant |}
               {| puinst := []
                ; pparams := []
                ; pcontext := [{| binder_name := nAnon; binder_relevance := Relevant |}]
                ; preturn := tApp <% @option %> [outputTp]
                |}
                <%true %>
                [{| bcontext := []
                  ; bbody :=

                          (constrRetBodylst outputTm outputTp)
                   |};
                   {| bcontext := []
                    ; bbody :=
                       tApp <% @None %> [outputTp]
                   |}])).


Definition constrFnBodyGuardCon  (outputTm : term) (outputTp : term) (guardCon : term) : term :=
 ((tCase {| ci_ind := {| inductive_mind := <? bool ?>; inductive_ind := 0 |}
                ; ci_npar := 0; ci_relevance := Relevant |}
               {| puinst := []
                ; pparams := []
                ; pcontext := [{| binder_name := nAnon; binder_relevance := Relevant |}]
                ; preturn := tApp <% @option %> [outputTp]
                |}
                guardCon
                [{| bcontext := []
                  ; bbody :=

                          (constrRetBodylst outputTm outputTp)
                   |};
                   {| bcontext := []
                    ; bbody :=
                       tApp <% @None %> [outputTp]
                   |}])).
                   
Definition constrFunAnimateEq {A : Type} (induct : A)
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term)
                        (fuel : nat) : TemplateMonad term :=


let postIn := tApp <%successPoly%> [postInType'; postIn'] in
let postInType := tApp <%outcomePoly%> [postInType'] in

let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
let postOutType := tApp <%outcomePoly%> [postOutType'] in






tBody' <-  mkMulPatMatFn (induct) ([(postIn, (postOut)); ((tApp <%fuelErrorPoly%> [postInType']),(tApp <%fuelErrorPoly%> [postOutType'])) ]) postInType postOutType (tApp <%noMatchPoly%> [postOutType']) fuel ;;
tmPrint tBody' ;;


let u :=
 (tLam "fuel" <%nat%>
            (tCase
               {|
                 ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                 ci_npar := 0;
                 ci_relevance := Relevant
               |}
               {|
                 puinst := [];
                 pparams := [];
                 pcontext := [{| binder_name := nNamed "fuel"; binder_relevance := Relevant |}];
                 preturn := (tProd {| binder_name := nAnon; binder_relevance := Relevant |} postInType postOutType)

               |} (tVar "fuel")
               [{|
                  bcontext := [];
                  bbody :=
                    (tApp <%fuelErrorPolyCstFn%> [postInType; postOutType'])
                |};
                {|
                  bcontext := [{| binder_name := nNamed "remFuel"; binder_relevance := Relevant |}];
                  bbody := tBody'

                              |}]
                     )) in






ret u.


Definition genFunAnimateEqPartialLetClause' {A : Type} (induct : A) (kn : kername) (fooTerm : named_term)  (inputTm : term) (inputTp : term)  (outputTm : term) (outputTp : term) (inputVars : list string) (fuel : nat) : TemplateMonad term :=

  if checkBool (filterListConj fooTerm) then
  (let postOut' := (constrFnBody outputTm outputTp
    (animateListConj
       (getListConjLetBind fooTerm) nil (inputVars) fuel (fun t : term => t))
     ) in
    

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
     tmReturn t')
     else tmFail "cannot process conj".

Definition animateOneConjEqGuard (conj : term) (partialGuard : term)  :  term :=
  match conj with
  | tApp <%eq%> [typeT; t1; t2] =>
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (typeToBoolEq typeT) [t1
         ; t2]]

  | _ => <% false %>
  end.
     
Fixpoint extractOrderedVarsfmLst (l : list term) : list string :=
match l with
| [] => []
| h :: t => app (extractOrderedVars h) (extractOrderedVarsfmLst t)
end.
Fixpoint listSearch' {A : Type} (ind : nat) (l : list A) : list A :=
match ind with
| 0 => match l with
     | h :: t => [h]
     | [] => []
     end
| S m => listSearch' m (tl l)
end.     


Fixpoint listSearch {A : Type} (indLst : list nat) (l : list A) : list A :=
match indLst with 
| [] => []
| h :: t => app (listSearch' h l) (listSearch t l)
end. 

Fixpoint getInArgs (indNm : string) (modes : list (string * ((list nat) * (list nat)))) (lstArgs : list term) : list term :=
match modes with
| [] => []
| h :: t => if String.eqb indNm (fst h) then listSearch (fst (snd h)) lstArgs else getInArgs indNm t lstArgs
end. 

Fixpoint getOutArgs (indNm : string) (modes : list (string * ((list nat) * (list nat)))) (lstArgs : list term) : list term :=
match modes with
| [] => []
| h :: t => if String.eqb indNm (fst h) then listSearch (snd (snd h)) lstArgs else getOutArgs indNm t lstArgs
end.     

Search (list (term * term) -> TemplateMonad term).
Print tLam.


 
Fixpoint lookUpVarsOne (varNm: string) (allVarTpInf : list (prod string term)) : list (prod string term) :=
match allVarTpInf with
| [] => []
| h :: t => if String.eqb varNm (fst h) then [h] else lookUpVarsOne varNm t
end.

Fixpoint mkLstTm (lst : list (prod string term)) : list (prod term term) :=
match lst with
| [] => []
| (str,tp) :: t => (tVar str, tp) :: mkLstTm t
end.
Fixpoint lookUpVars (lst : list string) (allVarTpInf : list (prod string term)) : list (prod string term) :=
match lst with
| [] => []
| h :: t => match lookUpVarsOne h allVarTpInf with
             | [h'] => h' :: lookUpVars t allVarTpInf
             | _ =>  lookUpVars t allVarTpInf
            end
end.


Definition lookUpVarsOneDefBool (varNm: string) (allVarTpInf : list (prod string term)) : (term) :=
match lookUpVarsOne varNm allVarTpInf with
| [h] => snd h
| _ => <%bool%>
end.
Fixpoint getModeFmLst (indNm : string) (modes : list (string * ((list nat) * (list nat)))) : (list nat) * (list nat) :=
 match modes with
  | [] => ([],[])
  | h :: t => if String.eqb indNm (fst h) then (snd h) else getModeFmLst indNm t
 end.

Definition getInArgs'  (mode : (list nat) * (list nat)) (lstArgs : list term) : list term :=
listSearch (fst mode) lstArgs.
 
Definition getOutArgs'  (mode : (list nat) * (list nat)) (lstArgs : list term) : list term :=
listSearch (snd mode) lstArgs.
 
 

Search (list (term * term) -> TemplateMonad term).
Print tLam.

Fixpoint getPredTp (indNm : string) (predTypeInf : list (string * (list term))) : list term :=
match predTypeInf with
| [] => []
| h :: t => if String.eqb indNm (fst h) then snd h else getPredTp indNm t 
end. 

Fixpoint crossList {A : Type} {B : Type} (lst1 : list A) (lst2 : list B) : list (A * B) :=
match lst1 with
 | [] => []
 | (h :: t) => match lst2 with
                | [] => []
                | h' :: t' => (h,h') :: crossList t t'
               end  
end.
                

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
 

                   
      
