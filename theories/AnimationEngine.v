(** * AnimationEngine — Main Animation Pipeline

    Top-level entry points [animateInductive] and [animateCoinductive] that
    orchestrate the full animation pipeline: clause data extraction, term
    rewriting, clause-by-clause compilation via [compileLetBindingsAndGuards],
    and final fixpoint assembly into a quoted Rocq definition.

    Depends on: [MetaRocqUtils], [PatternCompilation], [EqualityResolution],
    [AnimationDispatch]. *)

Require Import Animation.AnimationDispatch.

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

(** Replace any variable appearing in a function-position in [conjRHS] with
    an [idFn] application, so that the variable is treated as data rather
    than as a function call during pattern compilation. *)
Fixpoint removeVarFromFnPosition (conjRHS : term)  (allVarTpInf : list (string * term)) :=
match conjRHS with
| tApp (tVar str) lstArgs =>                            match lookUpVarsOne str allVarTpInf with
                                                         | [h] => tApp <%idFn%> ((snd h) :: (tVar str) :: (map (fun arg => removeVarFromFnPosition arg allVarTpInf) lstArgs))
                                                         | _ => tApp (tVar str) (map (fun arg => removeVarFromFnPosition arg allVarTpInf) lstArgs)
                                                        end
| tApp fn lstArgs => tApp (removeVarFromFnPosition fn allVarTpInf) (map (fun arg => removeVarFromFnPosition arg allVarTpInf) lstArgs)
| _ => conjRHS
end.

(** Apply [removeVarFromFnPosition] to the RHS of an equality conjunct,
    leaving non-equality conjuncts unchanged. *)
Definition removeVarfmFnPos (conjunct' : (term * (string * term))) (allVarTpInf : list (string * term)) :=
match fst conjunct' with
| tApp <%eq%> [typeVar; t1; t2] => let newConj := tApp <%eq%> [typeVar; t1; removeVarFromFnPosition t2 allVarTpInf] in (newConj, (snd conjunct'))
| _ => conjunct'
end.

(** Functor map over [AnimationResult]: applies [f] to a [Success] value and
    propagates [FuelError] and [NoMatch] unchanged. *)
Definition mapOutcomePoly (A : Type) (B : Type) (f : A -> B) (a : AnimationResult A) : AnimationResult B :=
match a with
| FuelError  => FuelError B
| Success a' => Success B (f a')
| NoMatch => NoMatch B
end.

(** Extract inductive names from bodies. *)
Definition getIndNames (l : list one_inductive_body) :=
map (fun o => ind_name o) l.

(** Generate context from inductive names. *)
Definition genCxt (l : list one_inductive_body) :=
(map (fun s => nNamed s) (rev (getIndNames l))).

(** Extract all argument types from an inductive type. *)
Fixpoint getType (o : term) : list term :=
match o with
       | (tProd {| binder_name := nAnon; binder_relevance := Relevant |} t (tSort sProp)) => [t]
       | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1  t2 => t1 :: getType t2
       | _ => [sentinel_term]
end.

(** Select types according to mode indices. *)
Definition getType' (mode : list nat) (l : list term) :=
map (fun n => nth n l sentinel_term) mode.

(** Get input type according to mode. *)
Definition getInTp (inMode : list nat) (o : one_inductive_body) : list term  :=
 let lstType := getType (ind_type o) in
  (getType' inMode lstType).

(** Strip all top-level foralls/products from a term to get to the body. *)
Fixpoint reduceClauseTm (t : term) :=
 match t with
  | (tPro str typ t') => reduceClauseTm t'
  | t'' => t''
 end.

(** Extract preconditions (hypotheses) from a constructor clause. *)
Definition getPreCons (t : term) :=
match t with
 | (tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2) => [t1]
 | _ => []
end.

(** Process preconditions, splitting conjunctions. *)
Definition processPreCon (l : list term) :=
match l with
 | [] => []
 | [tApp <%and%> l'] => l'
 | [t'] => [t']
 | _ :: (h' :: _) => []
end.

(** Get the body (recursive premises) of a constructor clause. *)
Definition getClBody' (t : term) : list term :=
processPreCon (getPreCons (reduceClauseTm t)).

(** Get the head (conclusion) of a constructor clause. *)
Definition getClHead' (t : term) : term :=
 match reduceClauseTm t with
  | (tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2) => t2
  | t' => t'
 end.

(** Extract body from a constructor. *)
Definition getClBody (c : constructor_body) : list term :=
 getClBody' (cstr_type c).

(** Extract head from a constructor. *)
Definition getClHead (c : constructor_body) :  term :=
 getClHead' (cstr_type c).

(** Check if a string is in a list of strings. *)
Fixpoint memberOfStringList (s : string) (l1 : list string) : bool :=
  match l1 with
  | [] => false
  | h :: t => if String.eqb s h then true else memberOfStringList s t
  end.

(** Extract names of inductive predicates applied in a list of terms. *)
Fixpoint getIndApp (l : list term) (indNames : list string) : list string :=
 match l with
  | [] => []
  | h :: t => match h with
              | tApp (tVar str) args => if (memberOfStringList str indNames) then (str :: (getIndApp t indNames)) else (getIndApp t indNames)
              | _ => (getIndApp t indNames)
              end
 end.

(** Annotate each clause with the inductive predicate names it applies. *)
Fixpoint getIndApp' (l : list (string * term)) (indNames : list string) : list (string * (list string)) :=
 match l with
  | [] => []
  | h :: t => (fst h, getIndApp (getClBody' (snd h)) indNames) :: getIndApp' t indNames
 end.

(** Get input/output types for all inductives according to mode specifications. *)
Fixpoint getInOutTpsOne (mode : (string * ((list nat) * (list nat)))) (b : list one_inductive_body) : list ((string * list term) * list term) :=
  match b with
    | h' :: t' => if String.eqb (fst mode) (ind_name h') then  [(ind_name h', getInTp (fst (snd mode)) h', getInTp (snd (snd mode)) h')] else getInOutTpsOne mode t'
    | _ => []
    end.

(** Get input/output types for all inductives in the mode list. *)
Fixpoint getInOutTps (modes : list (string * ((list nat) * (list nat)))) (b : list one_inductive_body) : list ((string * list term) * list term) :=
match modes with
 | [] => []
 | h :: t => app (getInOutTpsOne h b) (getInOutTps t b)
end.

(** Convert constructor bodies to named terms by unquoting from de Bruijn into
    the named context [l], returning [(constructor_name, clause_term)] pairs. *)
Fixpoint mkNmTm (c : list constructor_body) (l : list name) :TemplateMonad (list (string * term)) :=
 match c with
  | [] => tmReturn []
  | (h :: t) => r <- DB.undeBruijn' l ((cstr_type h )) ;; r' <- tmEval all r ;; let hres := (cstr_name h, (reduceClauseTm r')) in rest <- mkNmTm t l ;; tmReturn (hres :: rest)
 end.

(** Retrieve clause data for all inductives in [lib]: for each body, convert
    constructors to named terms and pair them with their input/output type info. *)
Fixpoint getData (lib : list one_inductive_body) (ln : list (string * ((list nat) * (list nat)))) (nmCxt : list name) (inOutTps : list ((string * list term) * list term)) : TemplateMonad (list (((string * list term) * list term) * (list (string * term))))  :=

 match lib with
  | [] => tmReturn []
  | h' :: t' => match inOutTps with
                 | h :: t => dbth <- mkNmTm (ind_ctors h') nmCxt ;; rest <- getData t' (ln) nmCxt (tl inOutTps) ;; tmReturn ((h, dbth) :: rest)
                 | _ => tmReturn []
                 end

 end.

(** Replace non-variable subterms in [l] with fresh variables (prefixed by
    [varPfix]), emitting equality constraints to bind the originals.
    Returns triples [(replacement_vars, equality_constraints, new_var_bindings)]. *)
Fixpoint substitutePatternVariables (l : list term) (varPfix : string) (n : nat) (argTps : list term) : list ((list term * list term) * list (string * term)) :=
match l with
| [] => []
| (tVar str) :: rest => (([(tVar str)], []), []) :: (substitutePatternVariables rest varPfix n (tl argTps))
| t' :: rest =>
      (([(tVar (String.append varPfix (string_of_nat n)))], [tApp <%eq%> [(hd <%bool%> argTps) ; (tVar (String.append varPfix (string_of_nat n))); t']]) , ([(String.append varPfix (string_of_nat n),(hd <%bool%> argTps))]))  :: (substitutePatternVariables rest varPfix (S n) (tl argTps))

end.
(** Look up the argument types for predicate named [s] in the type environment. *)
Fixpoint findTp (s : string) (allPredArgTps : list (string * (list term))) : list term :=
match allPredArgTps with
| [] => []
| h :: t => if String.eqb s (fst h) then snd h else findTp s t
end.

(** For each conjunct in [l], replace non-variable arguments of predicates with
    fresh variables and collect the resulting equality side-conditions and
    new variable bindings.  Equality conjuncts are passed through unchanged. *)
Fixpoint resolveConjunctionInputs (l : list term) (varPfix : string) (n : nat) (allPredArgTps : list (string * (list term))) :  list ((term * list term) * list (string * term)) :=
match l with
| [] => []
| (tApp <%eq%> lstArgs) :: rest => (((tApp <%eq%> lstArgs) , []), []) :: resolveConjunctionInputs (rest) (varPfix) (n) (allPredArgTps)
| (tApp (tVar str) lstArgs) :: rest =>  let result := substitutePatternVariables lstArgs varPfix n (findTp str allPredArgTps) in ((((tApp (tVar str) (concat (map (fun y => fst (fst y)) result)))), (concat (map (fun y => snd (fst y)) result))), (concat (map snd result))) :: resolveConjunctionInputs (rest) (varPfix) ((length lstArgs) + (S n)) (allPredArgTps)
| (tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs) :: rest =>
     let result := substitutePatternVariables lstArgs varPfix n (findTp indNm allPredArgTps) in ((((tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) (concat (map (fun y => fst (fst y)) result)))), (concat (map (fun y => snd (fst y)) result))), (concat (map snd result))) :: resolveConjunctionInputs (rest) (varPfix) ((length lstArgs) + (S n)) (allPredArgTps)

| t'' :: rest => ((t'', []), []) :: resolveConjunctionInputs (rest) (varPfix) (n) (allPredArgTps)

end.

(** Collect variable and inductive names from a term, with arguments listed
    before the function (used for computing fresh-variable prefix lengths). *)
Fixpoint extractOrderedVars2 (t : term) : list string :=
  match t with
  | tVar str  => [str]
  | (tInd {| inductive_mind := (_path, str); inductive_ind := k |} []) => [str]
  | tApp fn lst => app (concat (map extractOrderedVars2 lst)) (extractOrderedVars2 fn)

  | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2 => app (extractOrderedVars2 t1) (extractOrderedVars2 t2)
  | _ => []
  end.

(** Build a fresh variable prefix of length [n+1] using the letter "j".
    Used to guarantee freshness: choose [n] larger than the longest existing name. *)
Fixpoint mkFreshVPrefix (n : nat) : string :=
match n with
| 0 => "j"
| S m => String.append "j" (mkFreshVPrefix m)
end.

(** Extract the [(name, type)] pairs for every inductive predicate. *)
Definition findPredTps' (allTpInf : list ((string × term) × list (string × list (string × term)))) :=
map fst allTpInf.

(** Build a [(name, arg_types)] environment for all inductive predicates by
    destructuring each predicate's type into its argument list. *)
Definition findPredTps (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * list term) :=
map (fun y => (fst y , getType (snd y))) (findPredTps' allTpInf).
(** Flatten a right-nested [and] tree into a list of conjuncts. *)
Fixpoint flattenAnd (t : term) : list term :=
match t with
| tApp <%and%> [h;h1] => h :: (flattenAnd h1)
| t' => [t']
end.

(** Split a clause of the form [P1 /\ P2 /\ ... -> conclusion] into the list
    [P1, P2, ..., conclusion]; handles a conjunction in the premise position. *)
Definition flattenClause (t : term) : list term :=
match t with
| tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tApp <%and%> lst) t' => app ((flattenAnd (tApp <%and%> lst))) [t']
| tProd {| binder_name := nAnon; binder_relevance := Relevant |} t'' t' =>  [t''; t']
| t''' => [t''']
end.
(** Rebuild a right-nested [and] term from a flat list of conjuncts. *)
Fixpoint buildAnd (l : list term) : term :=
match l with
| [] => sentinel_term
| [h] => h
| h :: rest => tApp <%and%> [h; buildAnd rest]
end.
(** Inverse of [flattenClause]: reassemble a flat list [P1, ..., Pn, conclusion]
    back into a single clause term. *)
Definition buildClause (ts : list term) : term :=
match rev ts with
| [] => sentinel_term
| [h] => h
| [h1; h2] => tProd {| binder_name := nAnon; binder_relevance := Relevant |} h2 h1
| h :: t => tProd {| binder_name := nAnon; binder_relevance := Relevant |} (buildAnd (rev t)) h
end.

(** Rewrite a clause by substituting non-variable predicate arguments with fresh
    variables and splicing in the resulting equality side-conditions. *)
Definition rewriteCl (t : term) (allTpInf : list ((string × term) × list (string × list (string × term)))) : term :=
let prefix := mkFreshVPrefix (S (list_max (map String.length (extractOrderedVars2 t)))) in
let lstTm := flattenClause t in
let allPredArgTp := findPredTps allTpInf in
let resolved := resolveConjunctionInputs lstTm prefix 0 allPredArgTp in
buildClause (app (concat (map (fun y => (snd (fst y))) resolved)) (map (fun y => (fst (fst y))) resolved)).

(** Collect the new variable-type bindings introduced by rewriting clause [t]. *)
Definition getExtraTpInf (t : term) (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * term) :=

let prefix := mkFreshVPrefix (S (list_max (map String.length (extractOrderedVars2 t)))) in
let lstTm := flattenClause t in
let allPredArgTp := findPredTps allTpInf in
(concat (map (fun y => (snd (y))) (resolveConjunctionInputs lstTm prefix 0 allPredArgTp))).

(** Rewrite all clause terms in a flat [(constructor_name, clause)] list. *)
Fixpoint rewriteClAll1 (allClauseData1 : list (string × term)) (allTpInf : list ((string × term) × list (string × list (string × term)))) : (list (string × term)) :=
match allClauseData1 with
| [] => []
| (cstrNm,t) :: rest => (cstrNm, rewriteCl t allTpInf) :: (rewriteClAll1 rest allTpInf)
end.

(** Rewrite the clause data block for a single inductive. *)
Definition rewriteClAll1' (allClauseData1 : (((string × list term) × list term) × list (string × term))) (allTpInf : list ((string × term) × list (string × list (string × term)))) :  (((string × list term) × list term) × list (string × term)) :=
match allClauseData1 with
| (((indNm, inTps), outTps), cstrData) => (((indNm, inTps), outTps), (rewriteClAll1 cstrData allTpInf))
end.

(** Rewrite all clause data blocks across all inductives. *)
Definition rewriteClAll (allClauseData : list (((string × list term) × list term) × list (string × term))) (allTpInf : list ((string × term) × list (string × list (string × term)))) :  list (((string × list term) × list term) × list (string × term)) :=
map (fun y => rewriteClAll1' y allTpInf) allClauseData.

(** Collect new variable-type bindings for each clause in a flat clause list. *)
Fixpoint getExtraTpInfLst (allClauseData1 : list (string × term)) (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * list (string * term)) :=
match allClauseData1 with
| [] => []
| (cstrNm, t) :: rest => (cstrNm, getExtraTpInf t allTpInf) :: getExtraTpInfLst rest allTpInf
end.

(** Collect new variable-type bindings for every inductive's clause data. *)
Fixpoint getExtraTpInfLstAll (allClauseData : list (((string × list term) × list term) × list (string × term))) (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * (list (string * list (string * term)))) :=
match allClauseData with
| [] => []
| (((indNm, inTps), outTps), listCons) :: rest => (indNm, getExtraTpInfLst listCons allTpInf) :: (getExtraTpInfLstAll rest allTpInf)
end.

(** Look up [cstrNm] in an association list of constructor-name → type bindings. *)
Fixpoint retrieve (cstrNm : string) (l : list (string × list (string × term))) : list (string * term) :=
match l with
| [] => []
| h :: rest => if (String.eqb cstrNm (fst h)) then (snd h) else retrieve cstrNm rest
end.

(** Retrieve the original type bindings for constructor [cstrNm] of [indNm]. *)
Fixpoint getOldTpInf (indNm : string) (cstrNm : string) (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * term) :=
match allTpInf with
| [] => []
| (str, t, lst) :: rest => if (String.eqb indNm str) then retrieve cstrNm lst else getOldTpInf indNm cstrNm rest
end.

(** Retrieve the newly-introduced (fresh-variable) type bindings for
    constructor [cstrNm] of [indNm] after clause rewriting. *)
Fixpoint getNewTpInf (indNm : string) (cstrNm : string) (extraTpInf : list ((string) × list (string × list (string × term)))) : list (string * term) :=
match extraTpInf with
| [] => []
| (str, lst) :: rest => if (String.eqb indNm str) then retrieve cstrNm lst else getNewTpInf indNm cstrNm rest
end.
(** Merge original and fresh-variable type bindings for one inductive block. *)
Definition updateTpInf (allTpInf1 :  ((string × term) × list (string × list (string × term)))) (allTpInf :  list((string × term) × list (string × list (string × term)))) (extraTpInf : list ((string) × list (string × list (string × term)))) :=
match allTpInf1 with

| ((indNm, t), lst) => ((indNm, t), map (fun y => ((fst y), app (getOldTpInf indNm (fst y) allTpInf) (getNewTpInf indNm (fst y) extraTpInf))) lst)
end.

(** Apply [updateTpInf] to every inductive block in [allTpInf1l]. *)
Definition updateTpInfLst (allTpInf1l :  list ((string × term) × list (string × list (string × term)))) (allTpInf :  list((string × term) × list (string × list (string × term)))) (extraTpInf : list ((string) × list (string × list (string × term)))) :=
map (fun y => updateTpInf y allTpInf extraTpInf) allTpInf1l.

(** Self-update: merge each inductive block's extra type info into itself. *)
Definition updateTpInfFinal' (allTpInf :  list ((string × term) × list (string × list (string × term)))) (extraTpInf : list ((string) × list (string × list (string × term)))) :=
updateTpInfLst allTpInf allTpInf extraTpInf.

(** Compute the final, fully-merged type environment after clause rewriting:
    derives extra bindings from [allClauseData] and folds them into [allTpInf]. *)
Definition updateTpInfFinal (allClauseData : list (((string × list term) × list term) × list (string × term))) (allTpInf : list ((string × term) × list (string × list (string × term)))) : (list ((string × term) × list (string × list (string × term)))) :=
updateTpInfFinal' allTpInf  (getExtraTpInfLstAll allClauseData allTpInf).

(** Extract the list of definitions from a fixpoint term. *)
Definition inspectFix (t : term) : list (def term) :=
 match t with
  | tFix l k => l
  | _ => []
 end.

(** Build a [tConst] reference to definition [nm] in the module of [kn]. *)
Definition quoteConst' (kn : kername) (nm : string) :=
tConst (fst kn, nm) [].

(** For each clause, build the quoted reference to its compiled [Animated]
    definition, applied to the animated top-level functions of any predicates
    it calls recursively. *)
Fixpoint applyTopFn (kn : kername) (clauseData : list (string * (list string))) : list term :=
match clauseData with
| [] => []
| (postConCons, preConInd) :: t => match preConInd with
                                   | [] => (quoteConst' kn (String.append postConCons animatedSuffix)) :: applyTopFn kn t
                                   | l => tApp (quoteConst' kn (String.append postConCons animatedSuffix)) (map (fun nm => (tVar (String.append nm animatedTopFnSuffix))) l) :: applyTopFn kn t
                                   end
end.

(** Return the input-position indices for [indNm] in the mode list, or [[]]
    if [indNm] has no explicit input positions (empty-input mode). *)
Fixpoint getModeIn (indNm : string) (modes : list (string * ((list nat) * (list nat)))) :=
match modes with
| [] => []
| (h :: rest) => if String.eqb indNm (fst h) then fst (snd h) else getModeIn indNm rest
end.
(** Shared base for building one fixpoint definition for a top-level animated inductive.
    Parameterized by the zero-fuel branch, dispatch construction, and whether input is explicit. *)
Definition mkOneIndTopBase (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername)
  (zeroBranch : term) (mkDispatchBody : term -> term)
  (hasInput : bool) : def term :=
let fnListTp := tProd {| binder_name := nAnon; binder_relevance := Relevant |}
      <%nat%> (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
     (tApp <%AnimationResult%> [inputType]) (tApp <%AnimationResult%> [outputType])) in
let listTm := mkLstTm' (applyTopFn kn clauseData) fnListTp in
let caseExpr :=
  tCase
    {| ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
       ci_npar := 0; ci_relevance := Relevant |}
    {| puinst := []; pparams := [];
       pcontext := [{| binder_name := nNamed "fuel"; binder_relevance := Relevant |}];
       preturn := tApp <%AnimationResult%> [outputType] |}
    (tVar "fuel")
    [{| bcontext := []; bbody := zeroBranch |};
     {| bcontext := [{| binder_name := nNamed "remFuel"; binder_relevance := Relevant |}];
        bbody := mkDispatchBody listTm |}] in
let inputLam := tLam "input" (tApp <%AnimationResult%> [inputType]) caseExpr in
let body :=
  tLam "fuel" <%nat%>
    (if hasInput then inputLam else tApp inputLam [<%Success bool true%>]) in
let tp :=
  if hasInput
  then tPro "fuel" <%nat%> (tPro "input" (tApp <%AnimationResult%> [inputType])
         (tApp <%AnimationResult%> [outputType]))
  else tPro "fuel" <%nat%> (tApp <%AnimationResult%> [outputType]) in
{| dname := {| binder_name := nNamed (String.append indNm animatedTopFnSuffix);
               binder_relevance := Relevant |};
   dtype := tp; dbody := body; rarg := 0 |}.

(** Build a top-level fixpoint definition for an inductive with explicit input. *)
Definition mkOneIndTop' (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername) : def term :=
mkOneIndTopBase indNm inputType outputType clauseData kn
  (tApp <%FuelError%> [outputType])
  (fun listTm => tApp (tVar "dispatchOutcomePolyExt")
     [inputType; outputType; listTm; tVar "remFuel"; tVar "input"])
  true.

(** Build a top-level fixpoint definition for an inductive with no input
    (empty-input mode: the argument is always [Success bool true]). *)
Definition mkOneIndTopEmptyIn' (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername) : def term :=
mkOneIndTopBase indNm inputType outputType clauseData kn
  (tApp <%FuelError%> [outputType])
  (fun listTm => tApp (tVar "dispatchOutcomePolyExt")
     [inputType; outputType; listTm; tVar "remFuel"; tVar "input"])
  false.

(** Build a top-level fixpoint definition for a coinductive with explicit input,
    using [mapOutcomePoly Rest] as the zero-fuel branch. *)
Definition mkOneIndTopCoInd' (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername) : def term :=
let restFn := quoteConst' kn (String.append indNm "Rest") in
mkOneIndTopBase indNm inputType outputType clauseData kn
  (tApp <%mapOutcomePoly%> [inputType; outputType; restFn; tVar "input"])
  (fun listTm => tApp (tVar "dispatchOutcomePolyExtCoInd")
     [inputType; outputType; restFn; listTm; tVar "remFuel"; tVar "input"])
  true.

(** Build a top-level fixpoint definition for a coinductive with no input,
    using [mapOutcomePoly Rest] as the zero-fuel branch. *)
Definition mkOneIndTopCoIndEmptyIn' (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername) : def term :=
let restFn := quoteConst' kn (String.append indNm "Rest") in
mkOneIndTopBase indNm inputType outputType clauseData kn
  (tApp <%mapOutcomePoly%> [inputType; outputType; restFn; tVar "input"])
  (fun listTm => tApp (tVar "dispatchOutcomePolyExtCoInd")
     [inputType; outputType; restFn; listTm; tVar "remFuel"; tVar "input"])
  false.

(** Dispatch to [mkOneIndTop'] or [mkOneIndTopEmptyIn'] based on the mode for [indNm]. *)
Definition mkOneIndTop (indNm : string) (inputType : term) (outputType : term) (clauseData : list (string * (list string))) (kn : kername) (modes : list (string * ((list nat) * (list nat))))  : def term :=
match getModeIn indNm modes with
| [] => mkOneIndTopEmptyIn' indNm inputType outputType clauseData kn
| _ => mkOneIndTop' indNm inputType outputType clauseData kn
end.

(** Dispatch to [mkOneIndTopCoInd'] or [mkOneIndTopCoIndEmptyIn'] based on mode. *)
Definition mkOneIndTopCoInd (indNm : string) (inputType : term) (outputType : term) (clauseData : list (string * (list string))) (kn : kername) (modes : list (string * ((list nat) * (list nat))))  : def term :=
match getModeIn indNm modes with
| [] => mkOneIndTopCoIndEmptyIn' indNm inputType outputType clauseData kn
| _ => mkOneIndTopCoInd' indNm inputType outputType clauseData kn
end.

(** Construct a fixpoint term from a list of definitions. *)
Definition mkrecFn (ls : list (def term)) (j : nat) : term :=
 tFix ls j.

(** Apply [mkOneFn] to every inductive in [inductData], building the full list
    of fixpoint definitions for the mutual recursive block. *)
Definition mkAllIndTopWith (mkOneFn : string -> term -> term -> list (string * list string) -> kername -> list (string * (list nat * list nat)) -> def term)
  (inductData : list ((((string) * (term)) * (term)) * (list (string * (list string))))) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) : list (def term) :=
  map (fun h => mkOneFn (fst (fst (fst h))) (snd (fst (fst h))) (snd (fst h)) (snd h) kn modes) inductData.

(** Extended dispatch for AnimationResult types with fuel.
    Tries each function in the list, skipping noMatch results. *)
Fixpoint dispatchOutcomePolyExt
  (A B : Type) (lst : list (nat -> AnimationResult A -> AnimationResult B)) (fuel' : nat)
  (input' : AnimationResult A) {struct fuel'} : AnimationResult B :=
  match fuel' with
  | 0 => FuelError B
  | S remFuel' =>
      match lst with
      | [] => NoMatch B
      | h :: t =>
          let res := h remFuel' input' in
          match res with
          | @NoMatch _ => dispatchOutcomePolyExt A B t remFuel' input'
          | _ => res
          end
      end
  end.

Fixpoint dispatchOutcomePolyExtCoInd
  (A B : Type) (f : A -> B) (lst : list (nat -> AnimationResult A -> AnimationResult B)) (fuel' : nat)
  (input' : AnimationResult A) {struct fuel'} : AnimationResult B :=
  match fuel' with
  | 0 => mapOutcomePoly (A) (B) (f) (input')
  | S remFuel' =>
      match lst with
      | [] => NoMatch B
      | h :: t =>
          let res := h (S remFuel') input' in
          match res with
          | @NoMatch _ => dispatchOutcomePolyExtCoInd A B f t remFuel' input'
          | @FuelError _ => mapOutcomePoly (A) (B) (f) (input')
          | _ => res
          end
      end
  end.

(** Quote the dispatch function for embedding in generated code. *)
MetaRocq Quote Definition dt := Eval compute in dispatchOutcomePolyExt.
MetaRocq Run (dt' <- DB.undeBruijn dt ;; tmDefinition "dispatchExtTm'" dt').

MetaRocq Quote Definition dtCo := Eval compute in dispatchOutcomePolyExtCoInd.
MetaRocq Run (dtCo' <- DB.undeBruijn dtCo ;; tmDefinition "dispatchExtTmCoInd'" dtCo').

(** Extract the dispatch term for use in fixpoint generation. *)
Definition dispatchExtTm := hd sentinel_def_term (inspectFix dispatchExtTm').
Definition dispatchExtTmCoInd := hd sentinel_def_term (inspectFix dispatchExtTmCoInd').

(** Create all top-level animated inductive definitions with dispatch. *)
Definition mkAllIndTop (inductData : (list ((((string) * (term)) * (term)) * (list (string * (list string)))))) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) : list (def term) :=
app (mkAllIndTopWith mkOneIndTop inductData kn modes) [dispatchExtTm].

(** Build all coinductive top-level definitions plus the coinductive dispatch term. *)
Definition mkAllIndTopCoInd (inductData : (list ((((string) * (term)) * (term)) * (list (string * (list string)))))) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) : list (def term) :=
app (mkAllIndTopWith mkOneIndTopCoInd inductData kn modes) [dispatchExtTmCoInd].

(** Annotate each inductive's clause list with the inductive names it calls,
    producing the [(inductive_data, recursive_calls)] structure used for
    building the mutual fixpoint. *)
Fixpoint mkIndData (data : (list (((string * list term) * list term) * (list (string * term))))) (indNames : list string) :=
 match data with
  | [] => []
  | h :: t => match h with
               | (nm, linT, loutT, lCons) => (nm, linT, loutT, (getIndApp' lCons indNames)) :: mkIndData t indNames
              end
 end.

Unset Universe Checking.

(** Compile a constructor clause: classify premises, animate let-bindings and guard predicates,
    then assemble into a single executable term. *)
Definition compileLetBindingsAndGuards {A : Type} (ind : A) (kn : kername) (bigConj : term) (cstrNm : string) (inVars : list (prod string term))  (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=
let listAllConjs := getListConjAll bigConj in
gConjs' <- (getSortedOrientedConjsGuard modes listAllConjs [] [] [] (map fst inVars) fuel) ;;

gConjsEq <- tmEval all (filterConjsEq gConjs') ;;

lConjs' <- (getSortedOrientedConjsLet modes listAllConjs [] [] [] (map fst inVars) fuel) ;;
lc'' <- tmEval all lConjs' ;;
lConjs00 <- tmEval all (removeDuplicateDefs (attachOutputVarToSortedConjs lConjs' allVarTpInf modes predTypeInf) (map fst inVars)) ;;
lConjs <- tmEval all (map (fun lc => removeVarfmFnPos lc allVarTpInf) lConjs00) ;;

gConjsPred1 <- tmEval all (filterConjsPred' (attachOutputVarToSortedConjs gConjs' allVarTpInf modes predTypeInf));;
gConjsPred2 <- tmEval all ( (keepDuplicateDefs (attachOutputVarToSortedConjs lConjs' allVarTpInf modes predTypeInf) (map fst inVars))) ;;
gConjsPred <- tmEval all (app gConjsPred1 gConjsPred2) ;;

t <- animateListLetAndPredGuard ind kn lConjs gConjsEq gConjsPred inVars outVars (modes) (predTypeInf) (allVarTpInf) (lhsPreds) fuel ;;
t'' <- tmEval all  (typeConstrPatMatch.unwrapOptionTerm (DB.deBruijnOption t)) ;;

f <- tmUnquote t'' ;;
tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (String.append cstrNm animatedSuffix) (Some hnf) ;;

tmReturn t''.

Set Universe Checking.

(** Quote the inductive at [kn] and extract clause data for all mode-specified
    constructors using [getData]. *)
Definition getData' (kn : kername) (modes : list (string * ((list nat) * (list nat)))) : TemplateMonad (list (((string * list term) * list term) * (list (string * term))))  :=
mut <- tmQuoteInductive kn ;;

let lib := ind_bodies mut in
let nmCxt := genCxt lib in
let inOutTps := getInOutTps modes lib in
getData lib modes nmCxt inOutTps.

(** Extract [(name, type, constructors)] triples from inductive bodies. *)
Definition getCstrData (lo : list one_inductive_body) : list (string × term × list constructor_body) :=
map (fun (o : one_inductive_body) => ((ind_name o), ((ind_type o), (ind_ctors o)))) lo.

(** Convert a context declaration list to [(name, type)] pairs,
    dropping anonymous binders. *)
Fixpoint procCxtDclLst (c : list context_decl) : list (string * term) :=
match c with
| [] => []
| h :: t => match decl_name h with
             | {| binder_name := nNamed str; binder_relevance := Relevant |} => (str, decl_type h) :: procCxtDclLst t
             | _ =>  procCxtDclLst t
            end
end.

(** Process constructor data into [(inductive_name, type, [(cstr_name, arg_types)])] triples
    by converting each constructor's argument context. *)
Fixpoint getCstrData' (inDat : list (string × term × list constructor_body)) :=
match inDat with
| [] => []
| h :: t => match h with
            | (str, (tp, lst)) => (str, tp, (map (fun x => (cstr_name x, procCxtDclLst (cstr_args x))) lst)) :: getCstrData' t
            end
end.

(** Extract full clause type information from a list of inductive bodies. *)
Definition getClauseTpInfo (lo : list one_inductive_body) :=
getCstrData' (getCstrData lo).

(** Extract the predicate-applications appearing as premises in a constructor clause. *)
Definition getPredOcc (cstr : string * term) : list term :=
match snd cstr with
| tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2 =>  filterConjsPred (getListConjAll t1)
| _ => []
end.
(** Remove duplicate strings from [l], accumulating unique elements in [l']. *)
Fixpoint removeDupStr (l : list string) (l' : list string) : list string :=
match l with
| [] => l'
| h :: t => if inStrLst h l' then removeDupStr t l' else removeDupStr t (h :: l')
end.

(** Extract predicate names (possibly with duplicates) from a list of terms. *)
Fixpoint getPredNms'' (l : list term) : list string :=
match l with
| [] => []
| (tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs) :: rest => indNm :: getPredNms'' rest
| (tApp (tVar indNm) lstArgs) :: rest => indNm :: getPredNms'' rest
| _ :: rest => getPredNms'' rest
end.
(** Extract deduplicated predicate names from a list of terms. *)
Definition getPredNms (l : list term) : list string :=
removeDupStr (getPredNms'' l) [].

(** Return [(constructor_name, predicate_names_called)] for one clause. *)
Definition getCstrPredOcc (cstr : string * term) : string * list string :=
(fst cstr, getPredNms (getPredOcc cstr)).

(** Convert clause data to fixpoint-structure data by annotating each clause
    with the predicates it calls (for building the mutual recursive block). *)
Fixpoint getFixptData (data : list (((string × list term) × list term) × list (string × term))) : list (((string × list term) × list term) × list (string × list string)) :=
match data with
| [] => []
| h :: t => (fst h, (map getCstrPredOcc (snd h))) :: getFixptData t
end.

(** Convert the input and output type lists in each inductive block to single
    product types, suitable for building the fixpoint signature. *)
Fixpoint prodInOut (ls : list (((string × list term) × list term) × list (string × list string))) : ((list (((string × term) × term) × list (string × list string)))) :=
match ls with
| [] => []
| ((((p1,p2),p3), l4) :: rest) => ((((p1, (prodTerm p2)), (prodTerm p3)), l4) :: prodInOut rest)
end.

(** Extract the premise (LHS) of a clause, or [true] if the clause has no premise. *)
Definition conjLHS (c : ((string * string) * term)) : term :=
match snd c with
| tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2 => t1
| _ => <%true%>
end.

(** Return the variable name at position [n] in [vArgs], or [[]] if absent. *)
Fixpoint getVNmsOne (n : nat) (vArgs : list term) : list string :=
match vArgs with
| [] => []
| tVar str :: rest => match n with
                      | 0 => [str]
                      | S m => getVNmsOne m rest
                      end
| _ :: rest =>        match n with
                      | 0 => []
                      | S m => getVNmsOne m rest
                      end
end.

(** Collect variable names at a list of positions [l] from [vArgs]. *)
Fixpoint getVNms (l : list nat) (vArgs : list term) : list string :=
match l with
| [] => []
| h :: rest => app (getVNmsOne h vArgs) (getVNms rest vArgs)
end.

(** Extract variable names from a clause's conclusion according to the positions
    selected by [proj] (either [fst] for inputs or [snd] for outputs) in the mode list. *)
Fixpoint conjVarsByProjection (proj : list nat * list nat -> list nat) (c : ((string * string) * term)) (modes : list (string * ((list nat) * (list nat)))) : list string :=
match modes with
| [] => []
| h :: rest => if String.eqb (fst h) (fst (fst c)) then match snd c with
                                                        | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 (tApp (tVar str) lstVar) => getVNms (proj (snd h)) lstVar
                                                        | _ => []
                                                        end
                                                        else conjVarsByProjection proj c rest
end.

(** Names of the input variables of a clause according to the mode. *)
Definition conjInVars := conjVarsByProjection fst.
(** Names of the output variables of a clause according to the mode. *)
Definition conjOutVars := conjVarsByProjection snd.

(** Look up all variable type bindings for the constructor [snd (fst c)] in [tpData]. *)
Fixpoint getAllVarsTpInf' (c : ((string * string) * term))  (tpData : list (string × list (string × term))) : list (string * term) :=
match tpData with
| [] => []
| h :: rest => if String.eqb (snd (fst c)) (fst h) then snd h else   getAllVarsTpInf' c rest
end.

(** Retrieve all variable type bindings for a clause from the full type environment. *)
Definition getAllVarsTpInf (c : ((string * string) * term)) (tpData : list ((string × term) × list (string × list (string × term)))) :=
getAllVarsTpInf' c (concat (map snd tpData)).

(** Build a flat list of [(inductive_name, all_argument_types)] for every inductive,
    concatenating input and output types in order. *)
Definition allIndTpData (data : list (((string × list term) × list term) × list (string × term))) : list (string * list term) :=
map (fun x => (fst (fst (fst x)), app (snd (fst (fst x))) (snd (fst x )))) data.

(** Compute the type of the animated top-level function for one inductive:
    [nat -> AnimationResult inputTp -> AnimationResult outputTp]. *)
Definition animationTpOne (data :  (((string × list term) × list term) × list (string × term))) :  (string * term) :=
((fst (fst (fst data))), (tProd {| binder_name := nAnon; binder_relevance := Relevant |} <%nat%> (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tApp <%AnimationResult%> [prodTerm (snd (fst (fst data)))]) (tApp <%AnimationResult%> [prodTerm ((snd (fst data)))])))).

(** Compute animation types for all inductives in [data]. *)
Definition animationTp (data :  list (((string × list term) × list term) × list (string × term))) :  list (string * term) :=
map animationTpOne data.

(** Return the first [(k, v)] pair in [l'] with key [l], or [[]] if absent. *)
Fixpoint getfmLstOne {A : Type} (l : string) (l' : list (string * A)) : list (string * A) :=
match l' with
| [] => []
| h :: rest => if String.eqb l (fst h) then [h] else getfmLstOne l rest
end.

(** Retrieve all entries from [l'] whose keys appear in [l]. *)
Fixpoint getfmLst {A : Type} (l : list string) (l' : list (string * A)) : list (string * A) :=
match l with
| [] => []
| h :: rest => app (getfmLstOne h l') (getfmLst rest l')
end.

(** Look up the animation types of all predicates called by constructor [snd (fst c)]. *)
Fixpoint getPredOccAn' (c : ((string * string) * term)) (fixptInf' : list (string × list string)) (anTp : list (string * term)) : list (string * term) :=
match fixptInf' with
| [] => []
| h :: rest => if String.eqb (snd (fst c)) (fst h) then (getfmLst (snd h) anTp) else getPredOccAn' c rest anTp
end.

(** Retrieve animation types for all predicates called by clause [c]. *)
Definition getPredOccAn (c : ((string * string) * term)) (fixptInf : list (((string × term) × term) × list (string × list string)))
                        (anTp : list (string * term))  : list (string * term) :=

getPredOccAn' c (concat (map snd fixptInf)) anTp.

(** Filter [listallVTp] to only include entries whose names are in [lstVar]. *)
Definition getVarsTp (lstVar : list string) (listallVTp : list (string * term)) : list (string * term) :=
getfmLst lstVar listallVTp.

(** Tag each [(cstr_name, clause)] pair with its parent inductive name. *)
Fixpoint clauseLstOne'  (indNm :   string) (cstrs : list (string * term)) : list ((string * string) * term):=
match cstrs with
| [] => []
| (str, t) :: rest => ((indNm, str), t) :: clauseLstOne' indNm rest
end.

(** Convert a single inductive's data block to a tagged clause list. *)
Definition clauseLstOne'' (dataOne :   (((string × list term) × list term) × list (string × term)))
                         : list ((string * string) * term):=
clauseLstOne' (fst (fst (fst dataOne))) (snd dataOne).

(** Flatten all inductive data blocks into a single tagged clause list. *)
Definition clauseLst (data :   list (((string × list term) × list term) × list (string × term))) : list ((string * string) * term):=
concat (map clauseLstOne'' data).

(** Coinductive stream of animation results, used for lazy enumeration of coinductive outputs. *)
CoInductive ResultStream (A : Type) :=
| Scons : A -> ResultStream A -> ResultStream A.

(** Internal corecursive worker for [streamFromFunction]: produces the stream
    [f n0 inp, f (n0+1) inp, …] using an incrementing fuel counter. *)
CoFixpoint makeStm (A : Type) (B : Type) (f : nat -> A -> B) (n0 : nat) (inp : A) : ResultStream B :=
Scons B (f n0 inp) (makeStm A B f (S n0) inp).

(** Build an infinite stream of results by applying [f] to [inp] with
    increasing fuel values starting from 0. *)
Definition streamFromFunction (A : Type) (B : Type) (f : nat -> A -> B) (inp : A) : ResultStream B :=
makeStm A B f 0 inp.

(** Find an inductive by name in [inductData] and return [proj h] for its record,
    failing with [errMsg] if not found. *)
Fixpoint searchTpByProjection (proj : (((string * term) * term) * list (string * list string)) -> term)
  (inductData : list ((((string) * (term)) * (term)) * (list (string * (list string))))) (nm : string) (errMsg : string) : TemplateMonad term :=
match inductData with
 | [] => tmFail errMsg
 | h :: t => if String.eqb (fst (fst (fst h))) nm then tmReturn (proj h) else searchTpByProjection proj t nm errMsg
end.

(** Find the input type of a named inductive in the data. *)
Definition searchInTp := searchTpByProjection (fun h => snd (fst (fst h))).
(** Find the output type of a named inductive in the data. *)
Definition searchOutTp := searchTpByProjection (fun h => snd (fst h)).

Unset Universe Checking.

(** Compile a single clause [oneClause] of inductive [kn]: extract type and
    clause data, rewrite non-variable arguments, then call
    [compileLetBindingsAndGuards] to produce the compiled term. *)
Definition anOneCl {A : Type} (ind : A) (kn : kername)  (oneClause : ((string * string) * term)) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad term :=
allClauseData' <- getData' kn modes ;;
mut <- tmQuoteInductive kn ;;
allTpData' <- tmEval all (getClauseTpInfo (ind_bodies mut)) ;;
allClauseData <- tmEval all (rewriteClAll allClauseData' allTpData') ;;
allTpData <- tmEval all (updateTpInfFinal allClauseData' allTpData') ;;
cstrNm  <- tmEval all (snd (fst oneClause)) ;;

fixptData <- tmEval all (prodInOut (getFixptData allClauseData)) ;;
conjlhs <- tmEval all (conjLHS oneClause) ;;

allVarTp <- tmEval all (getAllVarsTpInf oneClause allTpData) ;;
inV <- tmEval all (getVarsTp (conjInVars oneClause modes) (allVarTp)) ;;
outV <- tmEval all (getVarsTp (conjOutVars oneClause modes) (allVarTp));;
predTps <- tmEval all (allIndTpData allClauseData) ;;
predTpsAn <- tmEval all (animationTp allClauseData) ;;
predTpsOccAn <- tmEval all (getPredOccAn oneClause fixptData predTpsAn) ;;

(compileLetBindingsAndGuards ind kn conjlhs cstrNm inV outV modes predTps allVarTp predTpsOccAn fuel).

(** Compile every clause in [clLst] sequentially, collecting compiled terms. *)
Fixpoint animAllClLst {A : Type} (ind : A) (kn : kername) (clLst : list ((string * string) * term)) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad (list term) :=

match clLst with
| [] => tmReturn []
| c1 :: cRest => c1An <- anOneCl ind kn c1 modes fuel ;; cRestAn <- animAllClLst ind kn cRest modes fuel ;; tmReturn (c1An :: cRestAn)
end.

(** Main entry point: animate an inductive relation into an executable function.
    Generates a fixpoint that tries each clause with bounded fuel. *)
Definition animateInductive {A : Type} (ind : A) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad (list term) :=
allClauseData' <- getData' kn modes ;;
mut <- tmQuoteInductive kn ;;
allTpData' <- tmEval all (getClauseTpInfo (ind_bodies mut)) ;;
allClauseData <- tmEval all (rewriteClAll allClauseData' allTpData') ;;
allTpData <- tmEval all (updateTpInfFinal allClauseData' allTpData') ;;

clLst <- tmEval all (clauseLst allClauseData) ;;

tms <- animAllClLst ind kn clLst modes fuel ;;

inductData <- tmEval all (prodInOut (getFixptData allClauseData)) ;;

let u := (mkrecFn (mkAllIndTop (inductData) kn modes) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (typeConstrPatMatch.unwrapOptionTerm (DB.deBruijnOption u)) ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append (snd kn) animatedTopFnSuffix) (Some hnf) ;; tmReturn tms.

(** Main entry point: animate a coinductive relation into an executable corecursive stream.
    Generates both a fixpoint and a ResultStream for lazy enumeration. *)
Definition animateCoinductive {A : Type} (ind : A) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad (list term) :=
allClauseData' <- getData' kn modes ;;
mut <- tmQuoteInductive kn ;;
allTpData' <- tmEval all (getClauseTpInfo (ind_bodies mut)) ;;
allClauseData <- tmEval all (rewriteClAll allClauseData' allTpData') ;;
allTpData <- tmEval all (updateTpInfFinal allClauseData' allTpData') ;;

let clLst := clauseLst allClauseData in

tms <- animAllClLst ind kn clLst modes fuel ;;

let inductData := prodInOut (getFixptData allClauseData) in

let u := (mkrecFn (mkAllIndTopCoInd (inductData) kn modes) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (typeConstrPatMatch.unwrapOptionTerm (DB.deBruijnOption u)) ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append (snd kn) animatedTopFnSuffix) (Some hnf) ;;
              fnInTp <- searchInTp inductData (snd kn) "cannot find input type" ;;
              fnOutTp <- searchOutTp inductData (snd kn) "cannot find output type" ;;
              let tCoInd := tApp <%streamFromFunction%> [(tApp <%AnimationResult%> [fnInTp]) ; (tApp <%AnimationResult%> [fnOutTp]); t'] in
              tCoInd'' <- tmEval all tCoInd ;;
              fStm <- tmUnquote tCoInd'' ;;

              tmEval hnf (my_projT2 fStm) >>=
              tmDefinitionRed_ false (String.append (snd kn) animatedStreamSuffix) (Some hnf) ;;

              tmReturn tms.

(** Compile all clauses for a list of mutually recursive inductives [knLst],
    returning the combined fixpoint structure data. *)
Fixpoint animAllClMultiDef {A : Type} (ind : A) (knLst : list kername)
 (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad ((list (((string × term) × term) × list (string × list string)))) :=

match knLst with
| [] => tmReturn []
| kn :: t => allClauseData' <- getData' kn modes ;;
             mut <- tmQuoteInductive kn ;;
             allTpData' <- tmEval all (getClauseTpInfo (ind_bodies mut)) ;;
             allClauseData <- tmEval all (rewriteClAll allClauseData' allTpData') ;;
             allTpData <- tmEval all (updateTpInfFinal allClauseData' allTpData') ;;

             clLst <- tmEval all (clauseLst allClauseData) ;;

             animAllClLst ind kn clLst modes fuel ;;

             inductData <- tmEval all (prodInOut (getFixptData allClauseData)) ;;
             restDefs <- animAllClMultiDef  ind  t  (modes) (fuel) ;; tmReturn (app inductData restDefs)

end.

(** Compile all clauses across a multi-definition mutual block ([topKn :: knLst]),
    assemble a single mutual fixpoint, and define it as [topKn.AnimatedTopFn]. *)
Definition animAllClMultiDef' {A : Type} (topInd : A) (topKn : kername) (knLst : list kername)
 (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad term:=

inductData'' <- animAllClMultiDef (topInd) (topKn :: knLst) (modes) (fuel);;
inductData <- tmEval all inductData'';;

let u := (mkrecFn (mkAllIndTop (inductData) topKn modes) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (typeConstrPatMatch.unwrapOptionTerm (DB.deBruijnOption u)) ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append (snd topKn) animatedTopFnSuffix) (Some hnf) ;; tmReturn u'.

Set Universe Checking.
