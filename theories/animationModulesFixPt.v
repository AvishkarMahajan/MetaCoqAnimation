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

(** Error term for partial type functions. *)
Parameter errTpTm : term.

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
       | _ => [errTpTm]
end.

(** Select types according to mode indices. *)
Definition getType' (mode : list nat) (l : list term) :=
map (fun n => nth n l errTpTm) mode.



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
Fixpoint inStrLst'' (s : string) (l1 : list string) : bool :=
  match l1 with
  | [] => false
  | h :: t => if String.eqb s h then true else inStrLst'' s t
  end.

(** Extract names of inductive predicates applied in a list of terms. *)
Fixpoint getIndApp (l : list term) (indNames : list string) : list string :=
 match l with
  | [] => []
  | h :: t => match h with
              | tApp (tVar str) args => if (inStrLst'' str indNames) then (str :: (getIndApp t indNames)) else (getIndApp t indNames)
              | _ => (getIndApp t indNames)
              end
 end.
 
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

Fixpoint getInOutTps (modes : list (string * ((list nat) * (list nat)))) (b : list one_inductive_body) : list ((string * list term) * list term) :=
match modes with
 | [] => []
 | h :: t => app (getInOutTpsOne h b) (getInOutTps t b)
end.    


 
(** Change the next 2 functions to not always return the full clause data but only bits of it **)
Fixpoint mkNmTm (c : list constructor_body) (l : list name) :TemplateMonad (list (string * term)) :=
 match c with
  | [] => tmReturn []
  | (h :: t) => r <- DB.undeBruijn' l ((cstr_type h )) ;; r' <- tmEval all r ;; let hres := (cstr_name h, (reduceClauseTm r')) in rest <- mkNmTm t l ;; tmReturn (hres :: rest)
 end.


Fixpoint getData (lib : list one_inductive_body) (ln : list (string * ((list nat) * (list nat)))) (nmCxt : list name) (inOutTps : list ((string * list term) * list term)) : TemplateMonad (list (((string * list term) * list term) * (list (string * term))))  :=

 match lib with
  | [] => tmReturn []
  | h' :: t' => match inOutTps with
                 | h :: t => dbth <- mkNmTm (ind_ctors h') nmCxt ;; rest <- getData t' (ln) nmCxt (tl inOutTps) ;; tmReturn ((h, dbth) :: rest)
                 | _ => tmReturn []
                 end

 end.








 
(* Change above 2 functions *)




 







(** Default term definition for error cases. *)
Parameter default : (def term).

(** Extract the list of definitions from a fixpoint term. *)
Definition inspectFix (t : term) : list (def term) :=
 match t with
  | tFix l k => l
  | _ => []
 end.

Definition quoteConst' (kn : kername) (nm : string) :=
tConst (fst kn, nm) [].
 
Fixpoint applyTopFn (kn : kername) (clauseData : list (string * (list string))) : list term :=
match clauseData with
| [] => []
| (postConCons, preConInd) :: t => match preConInd with
                                   | [] => (quoteConst' kn (String.append postConCons "Animated")) :: applyTopFn kn t
                                   | l => tApp (quoteConst' kn (String.append postConCons "Animated")) (map (fun nm => (tVar (String.append nm "AnimatedTopFn"))) l) :: applyTopFn kn t
                                   end
end. 
 

(** Create one fixpoint definition for a top-level animated inductive.
    Builds the dispatch function that tries each constructor case. *)
Definition mkOneIndTop (indNm : string) (inputType : term) (outputType : term) (clauseData : list (string * (list string))) (kn : kername) : def term :=

{|
     dname := {| binder_name := nNamed (String.append indNm "AnimatedTopFn") ; binder_relevance := Relevant |};
     dtype :=
       tPro "fuel" <%nat%> (tPro "input" (tApp (<%outcomePoly%>) [inputType])


            (tApp (<%outcomePoly%>) [outputType]));
     dbody :=


          tLam "fuel" <%nat%>

           (tLam "input" (tApp (<%outcomePoly%>) [inputType])
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
                 preturn := (tApp (<%outcomePoly%>) [outputType])

               |} (tVar "fuel")
               [{|
                  bcontext := [];
                  bbody :=
                    (tApp (<%fuelErrorPoly%>) [outputType])
                |};
                {|
                  bcontext := [{| binder_name := nNamed "remFuel"; binder_relevance := Relevant |}];
                  bbody := tApp (tVar "dispatchOutcomePolyExt") [inputType ; outputType; (mkLstTm' (applyTopFn kn clauseData) (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
         <%nat%> (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
        (tApp <%outcomePoly%> [inputType]) (tApp <%outcomePoly%> [outputType])) ) ); tVar "remFuel"; tVar "input"]

                              |}]
                     ))  ; rarg := 0 |}.




(** Construct a fixpoint term from a list of definitions. *)
Definition mkrecFn (ls : list (def term)) (j : nat) : term :=
 tFix ls j.

(** Create all top-level animated inductive definitions (auxiliary). *)
Fixpoint mkAllIndTop' (inductData : (list ((((string) * (term)) * (term)) * (list (string * (list string)))))) (kn : kername) : list (def term) :=
 match inductData with
  | [] => []
  | h :: t => (mkOneIndTop (fst (fst (fst h))) (snd (fst (fst h))) (snd (fst h)) (snd h) kn) :: mkAllIndTop' t kn
 end.

(** Add a definition to a recursive fixpoint block. *)
Definition addToRecBlk (recBlock : term) (t : def term) :=
 match recBlock with
  | tFix ls j => tFix (app ls [t]) j
  | _ => recBlock
 end.

(** Extended dispatch for outcomePoly types with fuel.
    Tries each function in the list, skipping noMatch results. *)
Fixpoint dispatchOutcomePolyExt
  (A B : Type) (lst : list (nat -> outcomePoly A -> outcomePoly B)) (fuel' : nat)
  (input' : outcomePoly A) {struct fuel'} : outcomePoly B :=
  match fuel' with
  | 0 => fuelErrorPoly B
  | S remFuel' =>
      match lst with
      | [] => noMatchPoly B
      | h :: t =>
          let res := h remFuel' input' in
          match res with
          | @noMatchPoly _ => dispatchOutcomePolyExt A B t remFuel' input'
          | _ => res
          end
      end
  end.

(** Quote the dispatch function for embedding in generated code. *)
MetaRocq Quote Definition dt := Eval compute in dispatchOutcomePolyExt.
MetaRocq Run (dt' <- DB.undeBruijn dt ;; tmDefinition "dispatchExtTm'" dt').

(** Extract the dispatch term for use in fixpoint generation. *)
Definition dispatchExtTm := hd default (inspectFix dispatchExtTm').

(** Create all top-level animated inductive definitions with dispatch. *)
Definition mkAllIndTop (inductData : (list ((((string) * (term)) * (term)) * (list (string * (list string)))))) (kn : kername) : list (def term) :=
app (mkAllIndTop' inductData kn) [dispatchExtTm].

Fixpoint mkIndData (data : (list (((string * list term) * list term) * (list (string * term))))) (indNames : list string) :=
 match data with
  | [] => []
  | h :: t => match h with
               | (nm, linT, loutT, lCons) => (nm, linT, loutT, (getIndApp' lCons indNames)) :: mkIndData t indNames
              end
 end.

 

Unset Universe Checking.

                      
Definition animateListLetAndPredGuard3 {A : Type} (ind : A) (kn : kername) (bigConj : term) (cstrNm : string) (inVars : list (prod string term))  (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=

let listAllConjs := getListConjAll bigConj in
let gConjsEq := filterConjsEq listAllConjs in
(*
lAC' <- tmEval all listAllConjs ;;
*)
(*tmPrint lAC';;*)

lConjs' <- (getSortedOrientedConjsLet modes listAllConjs [] [] [] (map fst inVars) fuel) ;;

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

f <- tmUnquote t'' ;;
tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (String.append cstrNm "Animated") (Some hnf) ;;


tmReturn t''.

Set Universe Checking. 




(** Main entry point: animate an entire inductive predicate.
    Generates animated functions for all constructors and composes them into
    a mutually recursive fixpoint. *)
Definition mkBigFixpt (nmTopInduct : string) (inductData : (list ((((string) * (term)) * (term)) * (list (string * (list string))))))
                        (kn : kername) (fuel : nat) : TemplateMonad unit :=
          
          let u := (mkrecFn (mkAllIndTop (inductData) kn) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (removeopTm (DB.deBruijnOption u)) ;;
          tmPrint t' ;;
               f <- tmUnquote t';;
               tmPrint f ;;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append nmTopInduct "AnimatedTopFn") (Some hnf) ;; tmMsg "done".




Definition getData' (kn : kername) (modes : list (string * ((list nat) * (list nat)))) : TemplateMonad (list (((string * list term) * list term) * (list (string * term))))  :=
mut <- tmQuoteInductive kn ;;

let lib := ind_bodies mut in
let nmCxt := genCxt lib in
let inOutTps := getInOutTps modes lib in
getData lib modes nmCxt inOutTps.


 

Definition getCstrData (lo : list one_inductive_body) : list (string × term × list constructor_body) :=
map (fun (o : one_inductive_body) => ((ind_name o), ((ind_type o), (ind_ctors o)))) lo.



Fixpoint procCxtDclLst (c : list context_decl) : list (string * term) := 
match c with
| [] => []
| h :: t => match decl_name h with
             | {| binder_name := nNamed str; binder_relevance := Relevant |} => (str, decl_type h) :: procCxtDclLst t
             | _ =>  procCxtDclLst t
            end
end.  

Fixpoint getCstrData' (inDat : list (string × term × list constructor_body)) :=
match inDat with
| [] => []
| h :: t => match h with
            | (str, (tp, lst)) => (str, tp, (map (fun x => (cstr_name x, procCxtDclLst (cstr_args x))) lst)) :: getCstrData' t
            end
end.  

Definition getClauseTpInfo (lo : list one_inductive_body) :=
getCstrData' (getCstrData lo).

Definition getPredOcc (cstr : string * term) : list term :=
match snd cstr with
| tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2 =>  filterConjsPred (getListConjAll t1)
| _ => []
end.
Fixpoint removeDupStr (l : list string) (l' : list string) : list string :=
match l with
| [] => l'
| h :: t => if inStrLst h l' then removeDupStr t l' else removeDupStr t (h :: l')
end.   

Fixpoint getPredNms'' (l : list term) : list string :=
match l with
| [] => []
| (tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs) :: rest => indNm :: getPredNms'' rest
| (tApp (tVar indNm) lstArgs) :: rest => indNm :: getPredNms'' rest
| _ :: rest => getPredNms'' rest
end.
Definition getPredNms (l : list term) : list string :=
removeDupStr (getPredNms'' l) [].

Definition getCstrPredOcc (cstr : string * term) : string * list string :=
(fst cstr, getPredNms (getPredOcc cstr)). 
(*
list (((string × list Ast.term) × list Ast.term) × list (string × Ast.term))
*)

Fixpoint getFixptData (data : list (((string × list term) × list term) × list (string × term))) : list (((string × list term) × list term) × list (string × list string)) :=
match data with
| [] => []
| h :: t => (fst h, (map getCstrPredOcc (snd h))) :: getFixptData t
end.

Fixpoint prodInOut (ls : list (((string × list term) × list term) × list (string × list string))) : ((list (((string × term) × term) × list (string × list string)))) :=
match ls with
| [] => []
| ((((p1,p2),p3), l4) :: rest) => ((((p1, (prodTerm p2)), (prodTerm p3)), l4) :: prodInOut rest)
end. 
             
Definition conjLHS (c : ((string * string) * term)) : term :=
match snd c with
| tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2 => t1
| _ => <%true%>
end. 
Check nth.

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

Fixpoint getVNms (l : list nat) (vArgs : list term) : list string :=
match l with
| [] => []
| h :: rest => app (getVNmsOne h vArgs) (getVNms rest vArgs)
end.                                         
                       


Fixpoint conjInVars (c : ((string * string) * term)) (modes : list (string * ((list nat) * (list nat)))) : list string :=
match modes with
| [] => []
| h :: rest => if String.eqb (fst h) (fst (fst c)) then match snd c with 
                                                        | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 (tApp (tVar str) lstVar) => getVNms (fst (snd h)) lstVar                                                                        
                                                        | _ => []
                                                        end
                                                        else conjInVars c rest
end.                                                          



Fixpoint conjOutVars (c : ((string * string) * term)) (modes : list (string * ((list nat) * (list nat)))) : list string :=
match modes with
| [] => []
| h :: rest => if String.eqb (fst h) (fst (fst c)) then match snd c with 
                                                        | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 (tApp (tVar str) lstVar) => getVNms (snd (snd h)) lstVar                                                                        
                                                        | _ => []
                                                        end
                                                        else conjOutVars c rest
end. 
Check concat.

Fixpoint getAllVarsTpInf' (c : ((string * string) * term))  (tpData : list (string × list (string × term))) : list (string * term) :=
match tpData with
| [] => []
| h :: rest => if String.eqb (snd (fst c)) (fst h) then snd h else   getAllVarsTpInf' c rest
end.
                                                         

Compute app [1] [2;3].
Definition getAllVarsTpInf (c : ((string * string) * term)) (tpData : list ((string × term) × list (string × list (string × term)))) :=
getAllVarsTpInf' c (concat (map snd tpData)).

Definition allIndTpData (data : list (((string × list term) × list term) × list (string × term))) : list (string * list term) :=
map (fun x => (fst (fst (fst x)), app (snd (fst (fst x))) (snd (fst x )))) data.



Definition animationTpOne (data :  (((string × list term) × list term) × list (string × term))) :  (string * term) :=
((fst (fst (fst data))), (tProd {| binder_name := nAnon; binder_relevance := Relevant |} <%nat%> (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tApp <%outcomePoly%> [prodTerm (snd (fst (fst data)))]) (tApp <%outcomePoly%> [prodTerm ((snd (fst data)))])))). 

Definition animationTp (data :  list (((string × list term) × list term) × list (string × term))) :  list (string * term) :=
map animationTpOne data.



Fixpoint getfmLstOne {A : Type} (l : string) (l' : list (string * A)) : list (string * A) :=
match l' with
| [] => []
| h :: rest => if String.eqb l (fst h) then [h] else getfmLstOne l rest
end.

Fixpoint getfmLst {A : Type} (l : list string) (l' : list (string * A)) : list (string * A) :=
match l with
| [] => []
| h :: rest => app (getfmLstOne h l') (getfmLst rest l') 
end.



Fixpoint getPredOccAn' (c : ((string * string) * term)) (fixptInf' : list (string × list string)) (anTp : list (string * term)) : list (string * term) :=
match fixptInf' with
| [] => []
| h :: rest => if String.eqb (snd (fst c)) (fst h) then (getfmLst (snd h) anTp) else getPredOccAn' c rest anTp
end.  

Definition getPredOccAn (c : ((string * string) * term)) (fixptInf : list (((string × term) × term) × list (string × list string))) 
                        (anTp : list (string * term))  : list (string * term) :=
                        
getPredOccAn' c (concat (map snd fixptInf)) anTp.

Definition getVarsTp (lstVar : list string) (listallVTp : list (string * term)) : list (string * term) :=
getfmLst lstVar listallVTp. 

Fixpoint clauseLstOne'  (indNm :   string) (cstrs : list (string * term)) : list ((string * string) * term):=
match cstrs with
| [] => []
| (str, t) :: rest => ((indNm, str), t) :: clauseLstOne' indNm rest  
end.

Definition clauseLstOne'' (dataOne :   (((string × list term) × list term) × list (string × term))) 
                         : list ((string * string) * term):=
clauseLstOne' (fst (fst (fst dataOne))) (snd dataOne).

Definition clauseLst (data :   list (((string × list term) × list term) × list (string × term))) : list ((string * string) * term):=
concat (map clauseLstOne'' data).  
  
Unset Universe Checking.
 
Definition anOneCl {A : Type} (ind : A) (kn : kername)  (oneClause : ((string * string) * term)) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad term :=
allClauseData <- getData' kn modes ;;
mut <- tmQuoteInductive kn ;; 
let allTpData := (getClauseTpInfo (ind_bodies mut)) in
let cstrNm := snd (fst oneClause) in 

                       
let fixptData := prodInOut (getFixptData allClauseData) in
let conjlhs := conjLHS oneClause in

let allVarTp := getAllVarsTpInf oneClause allTpData in
let inV := getVarsTp (conjInVars oneClause modes) (allVarTp) in
let outV := getVarsTp (conjOutVars oneClause modes) (allVarTp) in
let predTps := allIndTpData allClauseData in
let predTpsAn := animationTp allClauseData in
let predTpsOccAn := getPredOccAn oneClause fixptData predTpsAn in

(animateListLetAndPredGuard3 ind kn conjlhs cstrNm inV outV modes predTps allVarTp predTpsOccAn fuel). 


Fixpoint animAllClLst {A : Type} (ind : A) (kn : kername) (clLst : list ((string * string) * term)) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad (list term) :=


match clLst with
| [] => tmReturn []
| c1 :: cRest => c1An <- anOneCl ind kn c1 modes fuel ;; cRestAn <- animAllClLst ind kn cRest modes fuel ;; tmReturn (c1An :: cRestAn) 
end.

Definition animAllCl {A : Type} (ind : A) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad (list term) :=
allClauseData <- getData' kn modes ;;

let clLst := clauseLst allClauseData in


tms <- animAllClLst ind kn clLst modes fuel ;;

let inductData := prodInOut (getFixptData allClauseData) in

let u := (mkrecFn (mkAllIndTop (inductData) kn) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (removeopTm (DB.deBruijnOption u)) ;;
          tmPrint t' ;;
               f <- tmUnquote t';;
               tmPrint f ;;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append (snd kn) "AnimatedTopFn") (Some hnf) ;; tmReturn tms.


Set Universe Checking.

(*

Inductive type : Type :=
| N : type
| Arr : type -> type -> type.
Inductive term : Type :=
| Con : nat -> term
| Add : term -> term -> term
| Var : nat -> term
| App : term -> term -> term
| Abs : type -> term -> term.


Fixpoint eqFntype (t1 : type) (t2 : type) : bool :=
match t1 with
| N => match t2 with
        | N => true
        | _ => false
       end
| Arr t1' t1'' => match t2 with
                   | Arr t2' t2'' => if andb (eqFntype t1' t2') (eqFntype t1'' t2'') then true else false 
                   | _ => false
                  end
end.

Fixpoint eqFnterm (e1 : term) (e2 : term) : bool := 
match e1 with
| Con n => match e2 with
           | Con m => if Nat.eqb n m then true else false
           | _ => false
           end
                                      
| Add e1' e1'' => match e2 with
                  | Add e2' e2'' => if andb (eqFnterm e1' e2') (eqFnterm e1'' e2'') then true else false
                  | _ => false
                  end

| Var j => match e2 with
           | Var k => if Nat.eqb j k then true else false
           | _ => false
           end

| App e1' e1''  => match e2 with
                        | App e2' e2''  => if (andb (eqFnterm e1' e2') (eqFnterm e1'' e2''))  then true else false
                        | _ => false
                        end

| Abs t1 e1'  =>  match e2 with
                        | Abs t2 e2'  => if andb (eqFnterm e1' e2') (eqFntype t1 t2) then true else false
                        | _ => false
                        end
end.                                                

      
Inductive typing : list type -> term -> type -> Prop := (* Mode [0;1], [2]  = type inference, Mode [0;1;2] [] = type checking *) 
| TCon : forall (n : nat) (cxt : list type) (ttm : term) (tp : type), ttm = Con n /\ (N) = tp -> typing cxt ttm tp


| TAdd : forall (e1 e2 e3 : term) (cxt : list type) (tp : type),  tp = N  /\  
typing cxt e1 tp /\ typing cxt e2 tp /\ e3 = Add e1 e2 ->
typing cxt e3 tp


| TAbs : forall (e e2 : term) (t1 t2 t3 : type) (cxt cxt' : list type), cxt' = t1 :: cxt /\ e2 = Abs t1 e /\ t3 = Arr t1 t2 /\
typing cxt' e t2 ->
typing cxt e2 t3


| TVar : forall (j : nat) (e : term) (t : type) (cxt : list type),
lookup cxt j t /\ e = Var j -> typing cxt e t

| TApp : forall (e1 e2 e3 : term) (t1 t2 t3 : type) (cxt : list type), e3 = App e1 e2 /\ t3 = Arr t1 t2 /\
typing cxt e2 t1 /\ typing cxt e1 t3 ->
typing cxt e3 t2 

with lookup : list type -> nat -> type -> Prop :=
 | lookupFn0 : forall (n : nat) (cxt : list type) (t : type) , 0 = n /\ N = t -> lookup cxt n t
 | lookupFnRec : forall (n m : nat) (t t' : type) (cxt : list type) , n = S m /\ lookup cxt m t /\ t' = Arr N t -> lookup cxt n t'.  
 


MetaRocq Run (animAllCl typing <? typing ?> [("typing", ([0;1], [2]));("lookup", ([0;1], [2]))] 100).

Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(Abs (N) (Con 5))))).
Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(Abs (N) (Add (Con 5) (Var 0)))))).
 
Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(Abs (N) (Add (Con 5) (Var 1)))))).

Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],((Add (Con 5) (Var 1)))))).

Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(App (Abs (N) (Add (Con 5) (Var 0))) (Con 1))))).
 
Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(App (Abs (N) (Add (Con 5) (Var 0))) (Var 0))))).
 
Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(App (Abs (N) (Add (Con 5) (Var 0))) (Var 1))))).

Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(App (Abs (Arr N N) (Add (Con 5) (Var 0))) (Var 1))))).

 

MetaRocq Run (g <- getData' <? typing ?> [("typing", ([0;1], [2]));("lookup", ([0;1], [2]))] ;; tmDefinition "clauseDataTyping" g).

Compute clauseDataTyping.
Compute prodInOut (getFixptData clauseDataTyping).


MetaRocq Run (mut <- tmQuoteInductive <? typing ?> ;; tmDefinition "typingDatatyping" (getClauseTpInfo (ind_bodies mut))).

Compute typingDatatyping.

*)



 



(* GOAL :


Definition typingFixptData :=


[((("typing", <%prod (list type) (term) %>), <%type%>), [("TCon", []); ("TAdd", ["typing"]); ("TAbs", ["typing"]); ("TVar", ["lookup"]); ("TApp", ["typing"])]); 
((("lookup", <%prod (list type) (nat) %>), <%type%>), [("lookupFn0", []); ("lookupFnRec", ["lookup"])])].





MetaRocq Run (animateListLetAndPredGuard3 typing <? typing ?> TVarLHS "TVar" [("cxt", <%list type%>);("e", <%term%>)] 
                                         [("t", <%type%>)] [("typing",([0;1],[2]));("lookup",([0;1],[2])) ] [("typing",[<%list type%>;<%term%>;<%type%>]); ("lookup",[<%list type%>;<%nat%>;<%type%>])] 
               [("cxt", <%list type%>); ("e", <%term%>); ("t", <%type%>); ("j", <%nat%>)] [("lookup", <% nat -> outcomePoly ((list type) * nat) -> outcomePoly type%>)] 100). 




*)






























(*

Definition mkIndData' (kn : kername) (modes : (list (string × (list nat × list nat)))) :=
data <- getData' kn modes;;
mut <- tmQuoteInductive kn ;;
let lib := ind_bodies mut in
let nmCxt := genCxt lib in
let inOutTps := getInOutTps modes lib in
data <- getData lib modes nmCxt inOutTps ;;
let indNames := map (fun d => (fst (fst (fst d)))) data in
tmReturn (mkIndData data indNames).

*)






(*

MetaRocq Run (animateListLetAndPredGuard3 typing <? typing ?> TVarLHS "TVar" [("cxt", <%list type%>);("e", <%term%>)] 
                                         [("t", <%type%>)] [("typing",([0;1],[2]));("lookup",([0;1],[2])) ] [("typing",[<%list type%>;<%term%>;<%type%>]); ("lookup",[<%list type%>;<%nat%>;<%type%>])] 
               [("cxt", <%list type%>); ("e", <%term%>); ("t", <%type%>); ("j", <%nat%>)] [("lookup", <% nat -> outcomePoly ((list type) * nat) -> outcomePoly type%>)] 100). 


*)




(*

(*
(** Construct a list term from a list of variable names. *)
Fixpoint mkLstTm (eltType : term) (lst : list string) : term :=
 match lst with
  | [] => tApp
           (tConstruct
              {|
                inductive_mind := <?list?>; inductive_ind := 0
              |} 0 []) [eltType]
  | h :: t =>  tApp
               (tConstruct
               {| inductive_mind := <?list?>; inductive_ind := 0 |} 1 [])
               [eltType; tVar h; mkLstTm eltType t]
 end.
*)

(*

Fixpoint findInType (s : string) (ls : list (((string * term) * term) * (list nat * list nat))) : option term :=
match ls with
  | [] => None
  | (h :: t) => if (String.eqb s (fst (fst (fst h)))) then Some (snd (fst (fst h))) else findInType s t
end.
(* ls is (nameOfInductive, inputType, outputType, modeInfo) *)
Fixpoint findOutType (s : string) (ls : list (((string * term) * term) * (list nat * list nat))) : option term :=
match ls with
  | [] => None
  | (h :: t) => if (String.eqb s (fst (fst (fst h)))) then Some ((snd (fst h))) else findOutType s t
end.
*)
(*
Definition mkProdTm3Helper (mode : list nat) (lsArgs : list term) : (list term) :=
map (fun n => nth n lsArgs errTpTm) mode. 
*) 







(*
Fixpoint findIndex (s : string) (ls : list (((string * term) * term) * (list nat * list nat))) : option (list nat * list nat) :=
 match ls with
  | [] => None
  | (h :: t) => if (String.eqb s (fst (fst (fst h)))) then Some (snd h) else findIndex s t
 end.
*) 




(*
Fixpoint mkProdTm3' (lsArgs : list term) (tpTm : term) : term :=
match lsArgs with
 | [] => <%true%>
 | [h] => h
 | h' :: t => match tpTm with
               | (tApp <%prod%> [(tp1) ; res]) => tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0
                                                                                  |} 0 []) [tp1 ; res; h' ; (mkProdTm3' t res)]

               | _ => errTpTm
              end
 end.

*)



(*
Definition mkProdTm3 (mode : list nat) (lsArgs : list term) (tpTm : term) : term :=
mkProdTm3' (mkProdTm3Helper mode lsArgs) tpTm.
*)
Fixpoint extractClinfo (ts : list term) (ls : list (((string * term) * term) * (string * (list nat * list nat))))
                              : list ((((string * term) * term) * term) * term)  :=
(* output is list of (inductiveNm, inputTerm, inputType, outputTerm, outputType) one tuple per conjunct in precondition *)
match ts with
| [] => []
| h :: rest => match h with
                | tApp (tVar str) lstArgs => match findIndex str ls with
                                                | Some mode => match findInType str ls with
                                                             | Some tp => match findOutType str ls with
                                                                           | Some tp' => (str, (mkProdTm3 (fst mode) lstArgs tp), tp, (mkProdTm3 (snd mode) lstArgs tp'), tp') :: extractClinfo rest ls
                                                                           | _ => extractClinfo rest ls
                                                                           end
                                                             | _ => extractClinfo rest ls
                                                             end





                                                | _ => extractClinfo rest ls
                                               end

                | _ => extractClinfo rest ls
               end

end.

Parameter noClHdError :((((term) * term) * term) * term).

Definition extractClinfoHd (h : term) (ls : list (((string * term) * term) * (list nat * list nat)))
                              : ((((term) * term) * term) * term) :=
                match h with
                | tApp (tVar str) lstArgs => match findIndex str ls with
                                                | Some mode => match findInType str ls with
                                                             | Some tp => match findOutType str ls with
                                                                           | Some tp' => ((mkProdTm3 (fst mode) lstArgs tp), tp, (mkProdTm3 (snd mode) lstArgs tp'), tp')
                                                                           | _ => noClHdError
                                                                           end
                                                             | _ => noClHdError
                                                             end





                                                | _ => noClHdError
                                               end

                | _ => noClHdError
               end.

Definition mkClauseInfo  (ls : list (((string * list term) * list term) * (list nat * list nat))) (cl : (string * term)) :=
 match extractClinfoHd (getClHead' (snd cl)) ls with
  | (t1, t2, t3, t4) => ((extractClinfo (getClBody' (snd cl)) ls), t1, t2, t3, t4, (fst cl))
 end.

Fixpoint mkClauseInfoLst  (ls : list (((string * list term) * list term) * (string * (list nat * list nat)))) (clist : list (string * term)) :=
 match clist with
  | [] => []
  | h :: t => (mkClauseInfo ls h) :: mkClauseInfoLst ls t
 end.

Fixpoint appendIndex (modes : list (string * (list nat * list nat))) (ls : list (((string * list term) * list term))) :=
match modes with
 | [] => []
 | h :: t => match ls with
             | [] => []
             | h' :: t' => match h' with
                            | (p1,p2,p3) => (p1,p2,p3,h) :: appendIndex t t'
             end            end
end.
(*
Check mkClauseInfo.

Search (forall A : Type, list (list A) -> list A).
*)
Search (string -> string -> string).

(*
Fixpoint mkProdTypeVars3 (outputData : list (term)) :  term :=
 match outputData with
  | [] => <%bool%>
  | [h] =>  (h)
  | h :: t => let res := mkProdTypeVars3 t in  (tApp
                                            (tInd
                                             {|
                                             inductive_mind := <?prod?>; inductive_ind := 0
                                              |} []) [(h) ; res])
 end.
*)
Definition mkClData' (kn : kername) (modes : list (string * (list nat * list nat))) :=
mut <- tmQuoteInductive kn ;;
let lib := ind_bodies mut in
let nmCxt := genCxt lib in
let inOutTps := getInOutTps modes lib in
myData <- getData lib modes nmCxt inOutTps ;;
myData' <- tmEval all myData;;
tmDefinition (String.append (snd kn) "myData'") myData' ;;
let ls' := getInOutTps modes lib in
let ls'' := appendIndex modes ls' in
ls <- tmEval all ls'' ;;
(*tmPrint ls ;; *)
let lislisCons := map (fun p => snd p) myData in
let lisCons' := concat lislisCons in
lisCons <- tmEval all lisCons' ;;
(*tmPrint lisCons ;;*)

tmReturn (mkClauseInfoLst ls lisCons).
*)
 