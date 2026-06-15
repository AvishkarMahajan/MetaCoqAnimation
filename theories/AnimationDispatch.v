(** * AnimationDispatch — Unified Conjunction Dispatcher

    Integrates equality resolution and pattern-match compilation into a
    single dispatch layer.  Given a list of conjuncts from a constructor
    clause, this module separates them into let-binding equalities, guard
    predicates, and recursive calls, then animates each piece and
    assembles the final executable term via [animateListLetAndPredGuard].

    Depends on: [MetaRocqUtils], [PatternCompilation], [EqualityResolution]. *)

Require Import Animation.EqualityResolution.

Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.

Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.

Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.

(** The polymorphic identity function, used as a placeholder in generated terms. *)
Definition idFn (A : Type) (x : A) := x.

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
                                                    | [] => tmReturn (tApp <%Success%> [typeVar;t2])
                                                    | h :: rest => genFunAnimateEqPartialLetClause' ind kn conjunct inputTm inputTp outputTm outputTp inputVars fuel
                                                   end
                                    | tApp (tConstruct ind_type k lst) lstArgs => extractPatMatBindersPartial' ind kn conjunct inputTm inputTp outputTm outputTp inputVars fuel
                                    | _ => tmFail "incorrect Conj shape"
                                    end

 | _ => match extractIndName conjunct with
        | Some (indNm, _lstArgs) =>
            match fst (getModeFmLst indNm modes) with
            | [] => animatePredicateEmptyIn ind kn conjunct' modes predTypeInf allVarTpInf fuel
            | _ => compileRelationClause ind kn conjunct' modes predTypeInf allVarTpInf fuel
            end
        | None => tmFail "incorrect Conj shape"
        end
end.

(** Wrap an animation function call in a [tLetIn] that binds the output variable,
    extending [partialLetfn].  Handles three cases: no inputs (direct value),
    a single input (apply with fuel + input), or multiple inputs (join first). *)
Definition animateOneConjAnyLet' (outputVarNm : string) (outputVarTp : term) (inputVarsLst : list (prod term term)) (animationFn : term) (partialLetfn : term -> term) : (term -> term) :=
 match inputVarsLst with
  | [] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (animationFn) (tApp <%AnimationResult%> [outputVarTp]))  t) )
  | [h] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); fst h]) (tApp <%AnimationResult%> [outputVarTp])) t ))
  | _ =>  (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); (tApp (mkJoinOutcomeTm (map snd inputVarsLst)) (map fst inputVarsLst))]) (tApp <%AnimationResult%> [outputVarTp])) t))
 end.

(** Animate one conjunction as a let-binding step: compile [conjunct'] into
    a function and wrap it in a let that extends [partialLetfn]. *)
Definition animateOneConjAnyLet {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (inputVarsLst : list (prod string term)) (partialLetfn : term -> term)
                                           (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
let inputTm := telescopeToProdTerm inputVarsLst in
let inputTp := telescopeToProdType inputVarsLst in
let inputVarsLstTm := mkLstTm inputVarsLst in
outputVarNm <- tmEval all ((fst (snd conjunct'))) ;;
outputVarTp <- tmEval all ((snd (snd conjunct'))) ;;
animationFn <-  animateAnyLet (ind) (kn) (conjunct') (inputTm) (inputTp) (map fst inputVarsLst) (modes) (predTypeInf) (allVarTpInf) fuel ;;
tmReturn (animateOneConjAnyLet' (outputVarNm) (outputVarTp) (inputVarsLstTm) (animationFn) (partialLetfn)).

(** Animate one conjunction as a boolean predicate guard: compile [conjunct'] and
    produce a [compOutcomeBool] expression that extends [partialGuard]. *)
Definition animateOneConjPredGuard {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (inputVarsLst : list (prod string term)) (partialGuard : term)
                                           (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad term :=
let inputTm := telescopeToProdTerm inputVarsLst in
let inputTp := telescopeToProdType inputVarsLst in
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

(** Extract input or output variables from a conjunct using [eqProj] for
    equalities and [modeProj] for inductive predicate applications. *)
Definition getConjVarsByRole (eqProj : term -> term -> list string) (modeProj : (list nat * list nat) -> list term -> list term) (conjunct' : (term * (string * term))) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (prod string term) :=
let conjunct := fst conjunct' in
match conjunct with
 | tApp <%eq%> [typeVar; t1; t2] => lookUpVars (eqProj t1 t2) allVarTpInf
 | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs =>
     let mode := getModeFmLst indNm modes in
     lookUpVars (extractOrderedVarsfmLst (modeProj mode lstArgs)) allVarTpInf
 | tApp (tVar indNm) lstArgs =>
     let mode := getModeFmLst indNm modes in
     lookUpVars (extractOrderedVarsfmLst (modeProj mode lstArgs)) allVarTpInf
 | _ => []
end.

(** Get the input variable list for a conjunct: RHS variables of equalities,
    or in-mode arguments of inductive predicate applications. *)
Definition getConjInputVarLst := getConjVarsByRole (fun _t1 t2 => extractOrderedVars t2) (fun mode lstArgs => getInArgs' mode lstArgs).

(** Animate one let-clause by first computing its input variable list from
    context, then delegating to [animateOneConjAnyLet]. *)
Definition animateOneConjLetCl {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
let  inputVarsLst := getConjInputVarLst conjunct' allVarTpInf (modes) (predTypeInf) in
animateOneConjAnyLet ind kn conjunct' inputVarsLst partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel.

(** Animate one guard-predicate clause by first computing its input variable
    list from context, then delegating to [animateOneConjPredGuard]. *)
Definition animateOneConjPredGuardCl {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (partialGuard : term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term) :=

let  inputVarsLst := getConjInputVarLst conjunct' allVarTpInf (modes) (predTypeInf) in
animateOneConjPredGuard ind kn conjunct' inputVarsLst partialGuard (modes) (predTypeInf) (allVarTpInf) fuel.

(** Animate a list of let-binding conjuncts left-to-right, threading the
    accumulated let-binding function [partialLetfn] through each step. *)
Fixpoint animateListConjLetCl {A : Type} (ind : A) (kn : kername) (conjs : list (term * (string * term))) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
match conjs with
 | [] => tmReturn partialLetfn
 | h :: t => lFn' <- animateOneConjLetCl ind kn h partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel ;; animateListConjLetCl ind kn t lFn' (modes) (predTypeInf) (allVarTpInf) fuel
end.

(** Animate a list of predicate guard conjuncts, threading the accumulated
    boolean guard [partialGuard] through each step. *)
Fixpoint animateListConjPredGuardCl {A : Type} (ind : A) (kn : kername) (conjs : list (term * (string * term))) (partialGuard : term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term) :=
match conjs with
 | [] => tmReturn partialGuard
 | h :: t => pg <- animateOneConjPredGuardCl ind kn h partialGuard (modes) (predTypeInf) (allVarTpInf) fuel ;; animateListConjPredGuardCl ind kn t pg (modes) (predTypeInf) (allVarTpInf) fuel
end.

(** Combine a list of equality conjuncts into a single boolean guard expression
    by folding [animateOneConjSuccGuard] right-to-left, starting from [true]. *)
Fixpoint animateListConjEqGuard (conj : list term) : term :=
  match conj with
  | [] => <% true %>
  | h :: t =>
    match animateListConjEqGuard t with
    | gt => animateOneConjSuccGuard h gt
    end
  end.

(** Compile a guard-equality clause into an executable function: build a boolean
    guard from [gConjsEq] via [animateListConjEqGuard], wrap it in a
    [constrFnBodyGuardCon] body, and generate a pattern-matching function. *)
Definition genFunAnimateEqPartialGuardCon' {A : Type} (induct : A) (kn : kername) (gConjsEq : list term)  (inputTm : term) (inputTp : term)  (outputTm : term) (outputTp : term) (fuel : nat) : TemplateMonad term :=

  (let postOut' := (constrFnBodyGuardCon outputTm outputTp

    (animateListConjEqGuard (gConjsEq) )) in

    let postOutType' := tApp <% @option %> [outputTp] in

    let postInType' := inputTp in

    let postIn' := inputTm in

    let postIn := tApp <%Success%> [postInType'; postIn'] in
    let postInType := tApp <%AnimationResult%> [postInType'] in

    let postOut := tApp <%Success%> [postOutType'; postOut'] in
    let postOutType := tApp <%AnimationResult%> [postOutType'] in

     t0 <- constrFunAnimateEq induct postIn' postInType' postOut' postOutType'  fuel ;;

     let t1 := (tApp <%optionToOutcome%> [postInType'; outputTp; t0]) in
     t' <- tmEval all (typeConstrPatMatch.unwrapOptionTerm (DB.deBruijnOption t1)) ;;
     tmReturn t').

(** Lift [genFunAnimateEqPartialGuardCon'] to work directly with variable
    type lists by computing the product input/output types from [allVarTpInf] and [outVars]. *)
Definition animateListConjGuardEq {A : Type} (induct : A) (kn : kername) (gConjsEq : list term) (allVarTpInf : list (prod string term))  (outVars : list (prod string term)) (fuel : nat) : TemplateMonad term :=
genFunAnimateEqPartialGuardCon' induct kn gConjsEq  (telescopeToProdTerm allVarTpInf) (telescopeToProdType allVarTpInf) (telescopeToProdTerm outVars) (telescopeToProdType outVars) fuel.

(** Build a term that pattern-matches an [AnimationResult bool] guard and
    dispatches to one of four continuations: [succTrueRetTm] (guard true),
    [succFalseRetTm] (guard false), [noMatchRetTm], or [fuelErrorRetTm]. *)
Definition branchOutcomeBoolfn (retType succTrueRetTm succFalseRetTm noMatchRetTm fuelErrorRetTm : term) : term :=
let splitSuccBinder := {| binder_name := nNamed "splitSuccCase"; binder_relevance := Relevant |} in
let gcPredBinder := {| binder_name := nNamed "gcPred"; binder_relevance := Relevant |} in
let boolCase :=
  tCase
    {| ci_ind := {| inductive_mind := <?bool?>; inductive_ind := 0 |};
       ci_npar := 0; ci_relevance := Relevant |}
    {| puinst := []; pparams := [];
       pcontext := [splitSuccBinder]; preturn := retType |}
    (tVar "splitSuccCase")
    [{| bcontext := []; bbody := succTrueRetTm |};
     {| bcontext := []; bbody := succFalseRetTm |}] in
tLam "gcPred" (tApp <%AnimationResult%> [<%bool%>])
  (tCase
    {| ci_ind := {| inductive_mind := (MPfile ["MetaRocqUtils"; "Animation"], "AnimationResult");
                     inductive_ind := 0 |};
       ci_npar := 1; ci_relevance := Relevant |}
    {| puinst := []; pparams := [<%bool%>];
       pcontext := [gcPredBinder]; preturn := retType |}
    (tVar "gcPred")
    [{| bcontext := []; bbody := fuelErrorRetTm |};
     {| bcontext := [splitSuccBinder]; bbody := boolCase |};
     {| bcontext := []; bbody := noMatchRetTm |}]).

(** Animate predicate guard conjuncts and branch on their boolean result:
    passes [guardConEqAn] (the equality guard) as the [true] branch and
    [NoMatch] as the [false] branch. *)
Definition animateListConjPredGuardBrOutBool {A : Type} (ind : A) (kn : kername) (predGuardConjs : list (term × string × term))  (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (outVars : list (prod string term)) (guardConEqAn : term) (fuel : nat) : TemplateMonad (term) :=
predGuardCon <- animateListConjPredGuardCl (ind) (kn) (predGuardConjs) <%Success bool true%> (modes) (predTypeInf) (allVarTpInf) (fuel) ;;
let brOutBool := branchOutcomeBoolfn (tApp <%AnimationResult%> [telescopeToProdType outVars]) (guardConEqAn) (tApp <%NoMatch%> [telescopeToProdType outVars]) (tApp <%NoMatch%> [telescopeToProdType outVars]) (tApp <%FuelError%> [telescopeToProdType outVars]) in
tmReturn (tApp brOutBool [predGuardCon]).

(** Insert [tLetIn] bindings that split a product [inTerm] into individual
    variable names according to [inVars], using [splitOutcomePolyFst]/[Snd]. *)
Fixpoint splitInputs (inVars : list (string * term)) (inTerm : term) (fnBody : term) : term :=
match inVars with
| [] => fnBody
| [h] => (tLetIn {| binder_name := nNamed (fst h); binder_relevance := Relevant |}
                                 inTerm (tApp <%AnimationResult%> [(snd h)])) fnBody
| h' :: rest' =>  (tLetIn {| binder_name := nNamed (fst h'); binder_relevance := Relevant |}
                                 (tApp <% splitOutcomePolyFst %> [(snd h'); (telescopeToProdType rest'); inTerm])  (tApp <%AnimationResult%> [(snd h')])) (splitInputs rest' (tApp <% splitOutcomePolySnd %> [(snd h'); (telescopeToProdType rest'); inTerm]) fnBody)
end.
(** Convenience wrapper: split the [input] variable into [inVars] bindings,
    or leave [fnBody] unchanged if [inVars] is empty. *)
Definition splitInputs' (inVars : list (string * term)) (fnBody : term) : term :=
match inVars with
| [] => fnBody
| _ => splitInputs inVars (tVar "input") fnBody
end.

(** Assemble the full animated body of a constructor clause: animate the
    let-binding conjuncts [lConjs''], combine the equality guard [gConjsEq''] and
    predicate guards [gConjsPred''] into a single branching guard, and wrap
    everything in lambdas for the animated recursive functions and the input. *)
Definition animateListLetAndPredGuard {A : Type} (ind : A) (kn : kername) (lConjs'' : list (term × (string × term))) (gConjsEq'' : list term) (gConjsPred'' : list (term × (string × term))) (inVars : list (prod string term)) (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=
lConjs <- tmEval all lConjs'';;
gConjsEq <- tmEval all gConjsEq'';;
gConjsPred <- tmEval all gConjsPred'';;
letBind <- animateListConjLetCl  (ind) kn  lConjs  (fun t : term => t) (modes) (predTypeInf) (allVarTpInf) (fuel) ;;
gFun <- animateListConjGuardEq ind kn gConjsEq allVarTpInf outVars fuel ;;
let guardConEqAn := (tApp gFun [tVar "fuel"; mkOutPolyProdTm (allVarTpInf)]) in
combineGuard <- animateListConjPredGuardBrOutBool (ind) (kn) (gConjsPred) (modes) (predTypeInf) (allVarTpInf) (outVars) (guardConEqAn) (fuel);;
match inVars with
 | h :: rest => tmReturn (mkLamTp (app (mkAnimatedFnNm lhsPreds) [("fuel", <%nat%>)]) (tLam "input" (tApp <%AnimationResult%> [telescopeToProdType inVars])(splitInputs' inVars (letBind combineGuard))))
 | [] => tmReturn (mkLamTp (app (mkAnimatedFnNm lhsPreds) [("fuel", <%nat%>)]) (tLam "input" (tApp <%AnimationResult%> [<%bool%>]) ((*tLetIn {| binder_name := nNamed "input"; binder_relevance := Relevant |} <%Success bool true%>  <%AnimationResult bool%> *) (splitInputs' inVars (letBind combineGuard)))))

end.

(** Keep only the equality ([eq]) conjuncts from a list, discarding predicates. *)
Fixpoint filterConjsEq (lst : list term) : list term :=
match lst with
| [] => []
| (tApp <%eq%> [typeVar; t1; t2]) :: rest =>  (tApp <%eq%> [typeVar; t1; t2]) :: filterConjsEq rest

| _h :: rest => filterConjsEq rest
end.
(** Keep only inductive predicate application conjuncts from a list,
    discarding equalities and other forms. *)
Fixpoint filterConjsPred (lst : list term) : list term :=
match lst with
| [] => []
| (tApp <%eq%> [typeVar; t1; t2]) :: rest =>  filterConjsPred rest

| (tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs) :: rest => (tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs) :: filterConjsPred rest

| (tApp (tVar indNm) lstArgs) :: rest => (tApp (tVar indNm) lstArgs) :: filterConjsPred rest

| _h :: rest => filterConjsPred rest
end.

(** Check whether a term is a bare variable or a constructor application —
    shapes that can appear on the output side of a let-binding equation. *)
Definition hasRightShape (t : term) : bool :=
match t with
| tVar str => true
| tApp (tConstruct ind_type k lst) lstArgs => true
| _ => false
end.

(** Build a product type from a list of (term * type) pairs; base case is [bool]. *)
Fixpoint mk_lhs_prod_type2_non_monad (lhsIndPre : list (term * term)) : term :=
  match lhsIndPre with
  | []      => <%bool%>
  | [h]     => snd h
  | h :: t  => tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; mk_lhs_prod_type2_non_monad t]
  end.

(** Build a product term from a list of (term * type) pairs; base case is [true]. *)
Fixpoint mk_lhs_prod_tm2_non_monad (lhsIndPre : list (term * term)) : term :=
  match lhsIndPre with
  | []     => <%true%>
  | [h]    => fst h
  | h :: t => tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
                     [snd h; mk_lhs_prod_type2_non_monad t; fst h; mk_lhs_prod_tm2_non_monad t]
  end.

(** Look up the argument types for predicate [indNm] in [predTypeInf]. *)
Fixpoint get_pred_tp_fm_lst (indNm : string) (predTypeInf : list (string * (list term))) : list term :=
  match predTypeInf with
  | []         => []
  | h :: rest  => if String.eqb indNm (fst h) then snd h else get_pred_tp_fm_lst indNm rest
  end.

(** Rewrite a predicate conjunct into an equality against the animated function.
    Currently a stub — returns the conjunct unchanged. *)
Definition rewrite_pred_conj (conj' : term) (modes : list (string * (list nat * list nat))) (predTypeInf : list (string * (list term))) : term := conj'.

(** Topologically sort and orient conjuncts by known variables [kv]:
    equalities where one side is fully known go to [sortedConjs] (let-bindings);
    equalities where both sides are known go to [guardConjs] (boolean guards);
    predicate applications ready to evaluate go to [sortedConjs];
    all others are deferred in [remConjs] for the next pass. *)
Fixpoint classifyPremisesByMode (modes : list (string * ((list nat) * (list nat)))) (currentConjs : list term) (remConjs : list term) (sortedConjs : list term) (guardConjs : list term) (kv : (list string)) (fuel : nat) : TemplateMonad (prod (list term) (list term)) :=
match fuel with
 | 0 => if andb (isEmptyLst remConjs) (isEmptyLst currentConjs) then tmReturn (sortedConjs, guardConjs) else tmFail "insufficient fuel to sort conjs"
 | S n => if (andb (isEmptyLst remConjs) (isEmptyLst currentConjs)) then tmReturn (sortedConjs, guardConjs) else
           match currentConjs with
            | [] => classifyPremisesByMode modes remConjs [] sortedConjs guardConjs kv n
            | conj' :: t => match conj' with
                        | tApp <%eq%> [typeVar; t1; t2] => if andb (isListSubStr (extractOrderedVars t1) kv) (isListSubStr (extractOrderedVars t2) kv) then
                                                            classifyPremisesByMode modes t remConjs sortedConjs (conj' :: guardConjs) kv n else
                                                            (if (andb (isListSubStr (extractOrderedVars t1) kv) (hasRightShape t2)) then

                                                            classifyPremisesByMode modes t remConjs (tApp <%eq%> [typeVar; t2; t1] :: sortedConjs) (guardConjs) (app (extractOrderedVars t2) kv) n else
                                                            (if  (andb (isListSubStr (extractOrderedVars t2) kv) (hasRightShape t1)) then classifyPremisesByMode modes t remConjs (tApp <%eq%> [typeVar; t1; t2] :: sortedConjs) (guardConjs) (app (extractOrderedVars t1) kv) n else
                                                            (classifyPremisesByMode modes t (conj' :: remConjs) (sortedConjs) (guardConjs) (kv) n)))

                        | _ => match extractIndName conj' with
                               | Some (indNm, lstArgs) =>
                                   if isListSubStr (concat (map extractOrderedVars lstArgs)) kv then classifyPremisesByMode modes t remConjs sortedConjs (conj' :: guardConjs) kv n
                                   else if isListSubStr (extractOrderedVarsfmLst (getInArgs indNm modes lstArgs)) kv then classifyPremisesByMode modes t remConjs (conj' :: sortedConjs) guardConjs (app (extractOrderedVarsfmLst (getOutArgs indNm modes lstArgs)) kv) n
                                   else classifyPremisesByMode modes t (conj' :: remConjs) sortedConjs guardConjs kv n
                               | None => tmFail "incorrect conj shape"
                               end
                        end
           end
end.

(** Run [classifyPremisesByMode] and extract one half of the result via [proj],
    optionally reversing (let-bindings are reversed to restore declaration order). *)
Definition getClassifiedConjs (proj : list term * list term -> list term) (doReverse : bool) (modes : list (string * ((list nat) * (list nat)))) (currentConjs : list term) (remConjs : list term) (sortedConjs : list term) (guardConjs : list term) (kv : (list string)) (fuel : nat) : TemplateMonad (list term) :=
sConjs <- classifyPremisesByMode modes (currentConjs) (remConjs) (sortedConjs) (guardConjs) (kv) (fuel) ;;
result <- tmEval all (if doReverse then rev (proj sConjs) else proj sConjs) ;;
tmReturn result.

(** Classify and extract the let-binding conjuncts (sorted, reversed to declaration order). *)
Definition getSortedOrientedConjsLet := getClassifiedConjs fst true.
(** Classify and extract the guard conjuncts (sorted, kept in natural order). *)
Definition getSortedOrientedConjsGuard := getClassifiedConjs snd false.

(** Get all output variables introduced by a conjunct (LHS of an equality,
    or out-mode arguments of a predicate). *)
Definition getConjAllOutputVars (conj : term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (prod string term) :=
getConjVarsByRole (fun t1 _t2 => extractOrderedVars t1) (fun mode lstArgs => getOutArgs' mode lstArgs) (conj, (""%bs, <%bool%>)) allVarTpInf modes predTypeInf.

(** Pair each conjunct in [lconjs] with the output variables it introduces. *)
Fixpoint attachOutputVarLst (lconjs : list term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : (list (prod term (list (prod string term)))) :=
match lconjs with
 | [] => []
 | h :: t => (h, getConjAllOutputVars h allVarTpInf modes predTypeInf) :: attachOutputVarLst t allVarTpInf modes predTypeInf
end.

(** Tag a single conjunct term [lconjt] with each output variable in [lconjV],
    producing one [(conjunct, output_var)] pair per variable. *)
Fixpoint attachOutputVar' (lconjt : term) (lconjV : (((list (string * term))))) : list (term * (string * term)) :=
match (lconjV) with
| [] => []
| (h :: rest) => ((lconjt), h) :: attachOutputVar' lconjt rest
end.

(** Flatten a list of [(conjunct, output_vars)] pairs into a flat list of
    [(conjunct, output_var)] pairs by applying [attachOutputVar']. *)
Fixpoint attachOutputVar (lconjs : (list (prod term (list (prod string term))))) : list (term * (string * term)) :=
match lconjs with
| [] => []
| h :: rest => app (attachOutputVar' (fst h) (snd h)) (attachOutputVar rest)
end.
(** Convert a sorted conjunct list to a tagged [(conjunct, output_var)] list. *)
Definition attachOutputVarToSortedConjs (lconjs : list term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (term * (string * term)) :=
attachOutputVar (attachOutputVarLst lconjs allVarTpInf modes predTypeInf).

(** Remove conjuncts whose output variable already appears in [kv] (already defined),
    adding newly seen output variables to [kv] as they are encountered. *)
Fixpoint removeDuplicateDefs (lconjs : list (term * (string * term))) (kv : list string) : list (term * (string * term))  :=
match lconjs with
| [] => []
| h :: rest => if (inStrLst (fst (snd h)) kv) then removeDuplicateDefs rest kv  else h :: (removeDuplicateDefs rest ((fst (snd h)) :: kv))
end.

(** Keep only conjuncts whose output variable already appears in [kv] (duplicates),
    adding first occurrences to [kv] so subsequent duplicates are kept. *)
Fixpoint keepDuplicateDefs (lconjs : list (term * (string * term))) (kv : list string) : list (term * (string * term))  :=
match lconjs with
| [] => []
| h :: rest => if (inStrLst (fst (snd h)) kv) then h :: (keepDuplicateDefs rest kv)  else (keepDuplicateDefs rest ((fst (snd h)) :: kv))
end.

(** Keep only inductive predicate application entries from a tagged conjunct list,
    discarding equalities and other shapes. *)
Fixpoint filterConjsPred' (lst : list (term * (string * term))) : list (term * (string * term)) :=
match lst with
| [] => []
| ((tApp <%eq%> [typeVar; t1; t2]), (str,t'')) :: rest => filterConjsPred' rest
| ((tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs), (str, t2)) :: rest => ((tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs), (str, t2)) :: filterConjsPred' rest

| ((tApp (tVar indNm) lstArgs), (str, t2)) :: rest => ((tApp (tVar indNm) lstArgs), (str, t2)) :: filterConjsPred' rest

| _h :: rest => filterConjsPred' rest
end.
