Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.


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


Inductive type : Type :=
| N : type
| Arr : type -> type -> type.
Inductive Term : Type :=
| Con : nat -> Term
| Add : Term -> Term -> Term
| Var : nat -> Term
| App : Term -> Term -> Term
| Abs : type -> Term -> Term.


Fixpoint decEqType : forall (t1 t2 : type), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.
 
Fixpoint decEqTerm : forall (t1 t2 : Term), {t1 = t2} + {t1 <> t2}.
Proof.

  decide equality. decide equality. decide equality. decide equality.
Defined.

Definition eqFntype (t1 t2 : type) : bool

 :=
  if decEqType t1 t2 then true else false.
 
Definition eqFnTerm (t1 t2 : Term) : bool
:=
  if decEqTerm t1 t2 then true else false.
  
Print sumbool.  



(* Original paper 

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
typing Γ (App e1 e2) t2.
*)





(*
Inductive typing : list type -> Term -> type -> Prop := (* Mode [0;1], [2]  = type inference, Mode [0;1;2] [] = type checking *) 
| TCon : forall (n : nat) (cxt : list type) (ttm : Term) (tp : type), ttm = Con n /\ (N) = tp -> typing cxt ttm tp


| TAdd : forall (e1 e2 e3 : Term) (cxt : list type) (tp : type),  tp = N  /\  
typing cxt e1 tp /\ typing cxt e2 tp /\ e3 = Add e1 e2 ->
typing cxt e3 tp


| TAbs : forall (e e2 : Term) (t1 t2 t3 : type) (cxt cxt' : list type), cxt' = t1 :: cxt /\ e2 = Abs t1 e /\ t3 = Arr t1 t2 /\
typing cxt' e t2 ->
typing cxt e2 t3


| TVar : forall (j : nat) (e : Term) (t : type) (cxt : list type),
lookup cxt j t /\ e = Var j -> typing cxt e t

| TApp : forall (e1 e2 e3 : Term) (t1 t2 t3 : type) (cxt : list type), e3 = App e1 e2 /\ t3 = Arr t1 t2 /\
typing cxt e2 t1 /\ typing cxt e1 t3 ->
typing cxt e3 t2 

with lookup : list type -> nat -> type -> Prop :=
 | lookupFn0 : forall (n : nat) (cxt : list type) (t : type) , 0 = n /\ N = t -> lookup cxt n t
 | lookupFnRec : forall (n m : nat) (t t' : type) (cxt : list type) , n = S m /\ lookup cxt m t /\ t' = Arr N t -> lookup cxt n t'.  

Print TemplateMonad.
*)


Inductive typing : list type -> Term -> type -> Prop := (* Mode [0;1], [2]  = type inference, Mode [0;1;2] [] = type checking *) 
| TCon : forall (n : nat) (cxt : list type), typing cxt (Con n) N


| TAdd : forall (e1 e2 : Term) (cxt : list type), 
typing cxt e1 N /\ typing cxt e2 N ->
typing cxt (Add e1 e2) N


| TAbs : forall (e  : Term) (t1 t2 : type) (cxt cxt' : list type), cxt' = t1 :: cxt /\  
typing cxt' e t2 ->
typing cxt (Abs t1 e) (Arr t1 t2)


| TVar : forall (j : nat)  (t : type) (cxt : list type),
lookup cxt j t  -> typing cxt (Var j) t

| TApp : forall (e1 e2  : Term) (t1 t2  : type) (cxt : list type),
typing cxt e2 t1 /\ typing cxt e1 (Arr t1 t2) ->
typing cxt (App e1 e2) t2 

with lookup : list type -> nat -> type -> Prop :=
 | lookupFn0 : forall (cxt : list type), lookup cxt 0 N
 | lookupFnRec : forall (m : nat) (t  : type) (cxt : list type) , lookup cxt m t  -> lookup cxt (S m) (Arr N t).  



MetaRocq Run (animateInductive typing <? typing ?> [("typing", ([0;1], [2]));("lookup", ([0;1], [2]))] 100).

Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(Abs (N) (Con 5))))). 

Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(Abs (N) (Add (Con 5) (Var 0)))))).
 
Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(Abs (N) (Add (Con 5) (Var 1)))))).

Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],((Add (Con 5) (Var 1)))))).

Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(App (Abs (N) (Add (Con 5) (Var 0))) (Con 1))))).
 
Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(App (Abs (N) (Add (Con 5) (Var 0))) (Var 0))))).
 
Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(App (Abs (N) (Add (Con 5) (Var 0))) (Var 1))))).

Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(App (Abs (Arr N N) (Add (Con 5) (Var 0))) (Var 1))))).



Inductive even : nat -> bool -> Prop := (* mode = ([0], [1] *)
 | even0 : even 0 true 
 | evenSucc : forall (w  : nat), odd w true -> even (S w) true
with odd : nat -> bool -> Prop :=
 | oddSucc : forall (w : nat), even w true -> odd (S w) true. 
 

MetaRocq Run (animateInductive even <? even ?> [("even", ([0], [1]));("odd", ([0], [1]))] 100).

Compute evenAnimatedTopFn 30 (Success nat 5).
Compute evenAnimatedTopFn 30 (Success nat 4).
Compute evenAnimatedTopFn 30 (Success nat 3).
Compute evenAnimatedTopFn 30 (Success nat 0).



Inductive suffix : list nat -> list nat -> list nat -> Prop := (* mode = ([0;2], [1] *)
 | suffixNil : forall (l2  : list nat), suffix [] l2 l2
 | suffixCons : forall (w : nat) (l2 l3 l4 : list nat), suffix l2 l3 l4  -> suffix (w :: l2) l3 (w :: l4).

MetaRocq Run (animateInductive suffix <? suffix ?> [("suffix", ([0;2], [1]))] 100).

Compute suffixAnimatedTopFn 50 (Success ((list nat) * (list nat)) ([8;7], [8;7;9;7;8])).
Compute suffixAnimatedTopFn 50 (Success ((list nat) * (list nat)) ([8;7;9;7;8], [8;7;9;7;8])).

Compute suffixAnimatedTopFn 50 (Success ((list nat) * (list nat)) ([8;7;9;7;5], [8;7;9;7;8])).
Compute suffixAnimatedTopFn 50 (Success ((list nat) * (list nat)) ([8;6], [8;7;9;7;8])).


Inductive prefix : list nat -> list nat -> list nat -> Prop := (* mode = ([0;2], [1] *)
 | prefixNil : forall (l2  : list nat), prefix [] l2 l2
 | prefixCons : forall (w : nat) (l2 l3 l4 : list nat), prefix l2 l3 l4 -> prefix (w :: l2) l3 (w :: l4).

MetaRocq Run (animateInductive prefix <? prefix ?> [("prefix", ([1;2], [0]))] 100).

Inductive append : list nat -> list nat -> list nat -> Prop := (* mode = ([0;1], [2] *)
 | appendNil : forall (l2  : list nat), append [] l2 l2
 | appendCons : forall (w : nat) (l2 l3 l4 : list nat), append l2 l3 l4 -> append (w :: l2) l3 (w :: l4).

MetaRocq Run (animateInductive append <? append ?> [("append", ([0;1], [2]))] 100).

(*
Print TemplateMonad.

MetaRocq Run (allClauseData <- getData'  <? typing ?> [("typing", ([0;1], [2]));("lookup", ([0;1], [2]))] ;; tmDefinition "typingData" allClauseData).
MetaRocq Run (mut <- tmQuoteInductive <?typing?> ;; 
allTpData <- tmEval all (getClauseTpInfo (ind_bodies mut)) ;; tmDefinition "allTpDTyping" allTpData).

Compute allTpDTyping.
Compute typingData.
Search (nat -> string).
Search (forall A : Type, A -> list A -> A).

Fixpoint substitutePatternVariables (l : list term) (varPfix : string) (n : nat) (argTps : list term) : list ((list term * list term) * list (string * term)) :=
match l with
| [] => []
| (tVar str) :: rest => (([(tVar str)], []), []) :: (substitutePatternVariables rest varPfix n (tl argTps))
| t' :: rest => 
      (([(tVar (String.append varPfix (string_of_nat n)))], [tApp <%eq%> [(hd <%bool%> argTps) ; (tVar (String.append varPfix (string_of_nat n))); t']]) , ([(String.append varPfix (string_of_nat n),(hd <%bool%> argTps))]))  :: (substitutePatternVariables rest varPfix (S n) (tl argTps))
       
end.
Fixpoint findTp (s : string) (allPredArgTps : list (string * (list term))) : list term :=
match allPredArgTps with
| [] => []
| h :: t => if String.eqb s (fst h) then snd h else findTp s t
end. 

Fixpoint resolveConjunctionInputs (l : list term) (varPfix : string) (n : nat) (allPredArgTps : list (string * (list term))) :  list ((term * list term) * list (string * term)) :=
match l with
| [] => []
| (tApp <%eq%> lstArgs) :: rest => (((tApp <%eq%> lstArgs) , []), []) :: resolveConjunctionInputs (rest) (varPfix) (n) (allPredArgTps) 
| (tApp (tVar str) lstArgs) :: rest =>  let result := substitutePatternVariables lstArgs varPfix n (findTp str allPredArgTps) in ((((tApp (tVar str) (concat (map (fun y => fst (fst y)) result)))), (concat (map (fun y => snd (fst y)) result))), (concat (map snd result))) :: resolveConjunctionInputs (rest) (varPfix) ((length lstArgs) + (S n)) (allPredArgTps)    
| (tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs) :: rest => 
     let result := substitutePatternVariables lstArgs varPfix n (findTp indNm allPredArgTps) in ((((tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) (concat (map (fun y => fst (fst y)) result)))), (concat (map (fun y => snd (fst y)) result))), (concat (map snd result))) :: resolveConjunctionInputs (rest) (varPfix) ((length lstArgs) + (S n)) (allPredArgTps)    

     
| t'' :: rest => ((t'', []), []) :: resolveConjunctionInputs (rest) (varPfix) (n) (allPredArgTps)    

end.          

Fixpoint extractOrderedVars2 (t : term) : list string :=
  match t with
  
  (* Combine the pattern matches to handle fns of arbitrary arity *)

  | tVar str  => [str]
  | (tInd {| inductive_mind := (_path, str); inductive_ind := k |} []) => [str]
  | tApp fn lst => app (concat (map extractOrderedVars2 lst)) (extractOrderedVars2 fn)  
  
  | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2 => app (extractOrderedVars2 t1) (extractOrderedVars2 t2) 
  | _ => []
  end.  

Compute extractOrderedVars2 (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
             (tApp <%and%>
                [tApp
                   (tInd
                      {|
                        inductive_mind := (MPfile ["testing2"; "Animation"], "even"); inductive_ind := 1
                      |} [])
                   [tVar "w"; tConstruct {| inductive_mind := <?bool?>; inductive_ind := 0 |} 0 []];
                 tApp (tVar "even'")
                   [tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 0 [];
                    tConstruct {| inductive_mind := <?bool?>; inductive_ind := 0 |} 0 []]])
             (tApp (tVar "even'")
                [tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "w"];
                 tConstruct {| inductive_mind := <?bool?>; inductive_ind := 0 |} 0 []])).
Compute list_max (map String.length  ["w"; "even'"; "even'"; "w"]).
Fixpoint mkFreshVPrefix (n : nat) : string :=
match n with
| 0 => "j"
| S m => String.append "j" (mkFreshVPrefix m)
end.

              
Search (term -> list term).

Definition findPredTps' (allTpInf : list ((string × term) × list (string × list (string × term)))) :=
map fst allTpInf.

Definition findPredTps (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * list term) :=
map (fun y => (fst y , getType (snd y))) (findPredTps' allTpInf).

Definition flattenClause (t : term) : list term :=
match t with
| tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tApp <%and%> lst) t' => app lst [t']
| tProd {| binder_name := nAnon; binder_relevance := Relevant |} t'' t' =>  [t''; t']
| t''' => [t''']
end.
Definition buildClause (ts : list term) : term :=
match rev ts with
| [] => errTpTm
| [h] => h
| [h1; h2] => tProd {| binder_name := nAnon; binder_relevance := Relevant |} h2 h1
| h :: t => tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tApp <%and%> t) h
end.

Definition rewriteCl (t : term) (allTpInf : list ((string × term) × list (string × list (string × term)))) : term :=
let prefix := mkFreshVPrefix (S (list_max (map String.length (extractOrderedVars2 t)))) in
let lstTm := flattenClause t in
let allPredArgTp := findPredTps allTpInf in
buildClause (app (concat (map (fun y => (snd (fst y))) (resolveConjunctionInputs lstTm prefix 0 allPredArgTp)))  (map (fun y => (fst (fst y))) (resolveConjunctionInputs lstTm prefix 0 allPredArgTp))).


Definition getExtraTpInf (t : term) (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * term) :=

let prefix := mkFreshVPrefix (S (list_max (map String.length (extractOrderedVars2 t)))) in
let lstTm := flattenClause t in
let allPredArgTp := findPredTps allTpInf in
(concat (map (fun y => (snd (y))) (resolveConjunctionInputs lstTm prefix 0 allPredArgTp))).  

Compute typingData.

Fixpoint rewriteClAll1 (allClauseData1 : list (string × term)) (allTpInf : list ((string × term) × list (string × list (string × term)))) : (list (string × term)) :=
match allClauseData1 with
| [] => []
| (cstrNm,t) :: rest => (cstrNm, rewriteCl t allTpInf) :: (rewriteClAll1 rest allTpInf)
end.

Definition rewriteClAll1' (allClauseData1 : (((string × list term) × list term) × list (string × term))) (allTpInf : list ((string × term) × list (string × list (string × term)))) :  (((string × list term) × list term) × list (string × term)) :=
match allClauseData1 with
| (((indNm, inTps), outTps), cstrData) => (((indNm, inTps), outTps), (rewriteClAll1 cstrData allTpInf))
end.

Definition rewriteClAll (allClauseData : list (((string × list term) × list term) × list (string × term))) (allTpInf : list ((string × term) × list (string × list (string × term)))) :  list (((string × list term) × list term) × list (string × term)) :=
map (fun y => rewriteClAll1' y allTpInf) allClauseData.


Compute allTpDTyping.

Fixpoint getExtraTpInfLst (allClauseData1 : list (string × term)) (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * list (string * term)) :=
match allClauseData1 with
| [] => []
| (cstrNm, t) :: rest => (cstrNm, getExtraTpInf t allTpInf) :: getExtraTpInfLst rest allTpInf
end.
 
Fixpoint getExtraTpInfLstAll (allClauseData : list (((string × list term) × list term) × list (string × term))) (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * (list (string * list (string * term)))) :=
match allClauseData with
| [] => []
| (((indNm, inTps), outTps), listCons) :: rest => (indNm, getExtraTpInfLst listCons allTpInf) :: (getExtraTpInfLstAll rest allTpInf)
end.

Fixpoint retrieve (cstrNm : string) (l : list (string × list (string × term))) : list (string * term) :=
match l with
| [] => []
| h :: rest => if (String.eqb cstrNm (fst h)) then (snd h) else retrieve cstrNm rest
end.

Fixpoint getOldTpInf (indNm : string) (cstrNm : string) (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * term) :=
match allTpInf with
| [] => []
| (str, t, lst) :: rest => if (String.eqb indNm str) then retrieve cstrNm lst else getOldTpInf indNm cstrNm rest
end.

Fixpoint getNewTpInf (indNm : string) (cstrNm : string) (extraTpInf : list ((string) × list (string × list (string × term)))) : list (string * term) :=
match extraTpInf with
| [] => []
| (str, lst) :: rest => if (String.eqb indNm str) then retrieve cstrNm lst else getNewTpInf indNm cstrNm rest
end.
Definition updateTpInf (allTpInf1 :  ((string × term) × list (string × list (string × term)))) (allTpInf :  list((string × term) × list (string × list (string × term)))) (extraTpInf : list ((string) × list (string × list (string × term)))) :=
match allTpInf1 with 

| ((indNm, t), lst) => ((indNm, t), map (fun y => ((fst y), app (getOldTpInf indNm (fst y) allTpInf) (getNewTpInf indNm (fst y) extraTpInf))) lst)
end.

Definition updateTpInfLst (allTpInf1l :  list ((string × term) × list (string × list (string × term)))) (allTpInf :  list((string × term) × list (string × list (string × term)))) (extraTpInf : list ((string) × list (string × list (string × term)))) :=
map (fun y => updateTpInf y allTpInf extraTpInf) allTpInf1l.

Definition updateTpInfFinal' (allTpInf :  list ((string × term) × list (string × list (string × term)))) (extraTpInf : list ((string) × list (string × list (string × term)))) :=
updateTpInfLst allTpInf allTpInf extraTpInf.
  

Definition updateTpInfFinal (allClauseData : list (((string × list term) × list term) × list (string × term))) (allTpInf : list ((string × term) × list (string × list (string × term)))) : (list ((string × term) × list (string × list (string × term)))) :=
updateTpInfFinal' allTpInf  (getExtraTpInfLstAll allClauseData allTpInf).

MetaRocq Run (mut <- tmQuoteInductive <?even'?> ;; 
allTpData <- tmEval all (getClauseTpInfo (ind_bodies mut)) ;; tmDefinition "allTpDataEven'" allTpData).

Compute even'Data.
Compute allTpDataEven'.

Compute rewriteClAll even'Data allTpDataEven'.
Compute updateTpInfFinal even'Data allTpDataEven'.
*)
(*    
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
*)                                                     

                
