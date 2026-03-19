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
 
Search (string -> string -> bool).

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
Definition getData' (kn : kername) (modes : list (string * ((list nat) * (list nat)))) : TemplateMonad (list (((string * list term) * list term) * (list (string * term))))  :=
mut <- tmQuoteInductive kn ;;

let lib := ind_bodies mut in
let nmCxt := genCxt lib in
let inOutTps := getInOutTps modes lib in
getData lib modes nmCxt inOutTps.




 
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









(** Default term definition for error cases. *)
Parameter default : (def term).

(** Extract the list of definitions from a fixpoint term. *)
Definition inspectFix (t : term) : list (def term) :=
 match t with
  | tFix l k => l
  | _ => []
 end.

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

