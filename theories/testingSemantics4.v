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
(* Things to fix 
- relations with empty input/output modes
- handle case where auxillary relation defined separately - not able to fix :( 
- use pattern matchning not boolean equality for equalities with unary constructors

- rewrite to avoid any var name clashes
- rewrite to separate pattern matching from general function inversion
Optionally :
- mechanism for function inversion

CoInduction :
- Automate generation of augmented types/ (co)inductive relations
- map result back to original types
*)
Definition hdPoly {A : Type} (s : ResultStream A) : A :=
match s with 
| Scons h0 t0 => h0
end.

Definition tlPoly {A : Type} (s : ResultStream A) : ResultStream A :=
match s with 
| Scons h0 t0 => t0
end.


Fixpoint streamNth {A : Type} (n : nat) (s : ResultStream A) :  A :=
match n with
| 0 => hdPoly s
| S n => streamNth n (tlPoly s)
end.



Module typingQuickChick.

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
Print TemplateMonad.
(*
Inductive lookup : list type -> nat -> type -> Prop :=
 | lookupFn0 : forall (cxt : list type), lookup cxt 0 N
 | lookupFnRec : forall (m : nat) (t  : type) (cxt : list type) , lookup cxt m t  -> lookup cxt (S m) (Arr N t).  
 
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
 


 



MetaRocq Run (animateInductive typing <?typing?> [("typing", ([0;1], [2]));("lookup", ([0;1], [2]))] 100).


              
(*

MetaRocq Run (mut <- tmQuoteInductive <? lookup ?>;; tmPrint mut).
MetaRocq Run (tDat <- getData' <? typing ?> [("typing", ([0;1], [2]));("lookup", ([0;1], [2]))] ;; tmDefinition "tDat" tDat).

Compute tDat.

Definition animAllCl30 {A : Type} (ind : A) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad (bool) :=
allClauseData' <- getData' kn modes ;;
mut <- tmQuoteInductive kn ;; 
allTpData' <- tmEval all (getClauseTpInfo (ind_bodies mut)) ;;
allClauseData <- tmEval all (rewriteClAll allClauseData' allTpData') ;;
allTpData <- tmEval all (updateTpInfFinal allClauseData' allTpData') ;;
tmDefinition "rewriteData" allClauseData;;
tmReturn true.
(*
clLst <- tmEval all (clauseLst allClauseData) ;;


tms <- animAllClLst ind kn clLst modes fuel ;;

inductData <- tmEval all (prodInOut (getFixptData allClauseData)) ;; 

let u := (mkrecFn (mkAllIndTop (inductData) kn) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (typeConstrPatMatch.unwrapOptionTerm (DB.deBruijnOption u)) ;;
          tmPrint t' ;;
               f <- tmUnquote t';;
               tmPrint f ;;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append (snd kn) "AnimatedTopFn") (Some hnf) ;; tmReturn tms.


*)
MetaRocq Run (animAllCl30 typing <? typing ?> [("typing", ([0;1], [2]));("lookup", ([0;1], [2]))] 100).

Compute rewriteData.

*)
Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(Abs (N) (Con 5))))). 

Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(Abs (N) (Add (Con 5) (Var 0)))))).
 
Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(Abs (N) (Add (Con 5) (Var 1)))))).

Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],((Add (Con 5) (Var 1)))))).

Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(App (Abs (N) (Add (Con 5) (Var 0))) (Con 1))))).
 
Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(App (Abs (N) (Add (Con 5) (Var 0))) (Var 0))))).
 
Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(App (Abs (N) (Add (Con 5) (Var 0))) (Var 1))))).

Compute (typingAnimatedTopFn 50 (Success ((list type) * Term) ([],(App (Abs (Arr N N) (Add (Con 5) (Var 0))) (Var 1))))).

End typingQuickChick. 










Module STLC.
Open Scope bs.
Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty
 (* | unDefinedTy : ty *).

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | undefinedTm : tm.

Inductive coBool : Type :=
| coT
| coF
| undefinedBool.  
(*
Fixpoint decEqTerm : forall (t1 t2 : tm), {t1 = t2} + {t1 <> t2}.
Proof.

  decide equality. decide equality. decide equality. decide equality. decide equality. decide equality.
Defined.

Fixpoint decEqTy : forall (t1 t2 : ty), {t1 = t2} + {t1 <> t2}.
Proof.

  decide equality. Defined.
  
Fixpoint decEqCB : forall (t1 t2 : coBool), {t1 = t2} + {t1 <> t2}.
Proof.

  decide equality. Defined.  

Definition eqFntm (t1 t2 : tm) : bool :=  

  if decEqTerm t1 t2 then true else false.

Definition eqFnty (t1 t2 : ty) : bool :=

 if decEqTy t1 t2 then true else false.
Compute eqFnty. 
*)
Definition eqFntm (t1 t2 : tm) : bool :=  
match t1 with
| tm_true => match t2 with
              | tm_true => true
              | _ => false
              end
| tm_false => match t2 with
              | tm_false => true
              | _ => false
              end              
              
| _ => false
end.
  
Definition eqFncoBool (t1 t2 : coBool) : bool :=
match t1 with
| coT => match t2 with
          | coT => true
          | _ => false
          end
| coF =>  match t2 with
          | coF => true
          | _ => false
          end  

| _ => false
end.              

 
 
 
CoInductive coList : Type := 
| undefinedLst : coList
| coNil : coList
| coCons : tm -> coList -> coList. 

(*
Definition eqcoList (s1 : coList) (s2 : coList) : bool := 
match s1 with
| undefinedLst => match s2 with
                   | undefinedLst => true
                   | _ => false
                   end
| coNil =>         match s2 with
                   | coNil => true
                   | _ => false
                   end         
| _s3 => match s2 with
        | undefinedLst => false
        | coNil => false
        | _ => false
        end                   
end.
*)    
Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.
Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.
Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.
Notation "<{{ x }}>" := x (x custom stlc_ty).
Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) : stlc_scope.
Notation "$( t )" := t (in custom stlc_ty at level 0, t constr) : stlc_scope.
Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0) : stlc_scope.
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc_tm at level 200,
                    x custom stlc_tm,
                    y custom stlc_tm,
                    z custom stlc_tm at level 200,
                    left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true (in custom stlc_tm at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom stlc_tm at level 0).
Check <{{ Bool }}>.
Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.
Notation "x y" := (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.

Definition testTm : tm :=
tm_app (tm_app (tm_abs "x" (Ty_Arrow Ty_Bool Ty_Bool) (tm_var "x"))
         (tm_abs "x" Ty_Bool (tm_if (tm_var "x")  tm_false tm_true)))
         tm_true.


(*Original in SF 

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.
Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 [x:=s] t2}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if [x:=s] t1 then [x:=s] t2 else [x:=s] t3}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).
     
Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t v,
         value v ->
         <{(\x:T, t) v}> --> <{ [x:=v]t }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 /\
         t2 --> t2' ->
         <{v1 t2}> --> <{v1 t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').
*)
(*
Hint Constructors step : core.



Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
*)


Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 [x:=s] t2}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if [x:=s] t1 then [x:=s] t2 else [x:=s] t3}>
  | undefinedTm => undefinedTm    
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).

Reserved Notation "t '-->' t'" (at level 40).



CoInductive bigStep : tm -> coList -> Prop :=
| bigStepVal : forall t, isValue t coT -> bigStep t (coNil)
| bigStepStep : forall t t' t'', bigStep t' t'' /\ step t t' -> bigStep t (coCons t'  t'') 
| bigStepValU : forall t, bigStep t undefinedLst

with step : tm -> tm -> Prop :=
  | ST_Val : forall t t1, isValue t coT /\ t1 = t -> t --> t1
  
  | ST_AppAbs : forall z T t w,  
         isValue w coT  ->
        <{(\z:T, t) w}> --> <{ [z:=w]t }>
  
           
  | ST_App1 : forall t1 t1' t2,
        isValue t1 coF /\ t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}> 
     
  
  | ST_App2 : forall w t2 t2',
         isValue w coT /\ 
         t2 --> t2' ->
         <{w t2}> --> <{w t2'}>
  | ST_IfTrue : forall t1 t2,
       <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' -> <{if t1 then t2 else t3}> -->  <{if t1' then t2 else t3}>
   
  
  | ST_U : forall t, t --> undefinedTm 
     
      
with isValue : tm -> coBool -> Prop :=

| v_abs : forall z T2 t1,
     isValue <{\z:T2, t1}> coT
| v_true :  isValue <{true}> coT
| v_false : isValue <{false}> coT
| v_var : forall s, isValue (tm_var s) coT
| v_app : forall t1 t2, isValue (tm_app t1 t2) coF
| v_if : forall t1 t2 t3, isValue (tm_if t1 t2 t3) coF
| v_undef : forall t, isValue t undefinedBool 
          

where "t '-->' t'" := (step t t').





Definition bigStepRest := fun t : tm => undefinedLst.

Definition stepRest := fun t : tm => undefinedTm.

Definition isValueRest := fun t : tm => undefinedBool.



MetaRocq Run (animateCoinductive bigStep <? bigStep ?> [("bigStep", ([0], [1])); ("step", ([0], [1])); ("isValue", ([0], [1]))] 100).




MetaRocq Run (r <- tmEval all (streamNth 25 (bigStepAnimatedTopFnStream (Success (tm) ((testTm))))) ;; tmPrint r).

Definition omega : tm :=
tm_app (tm_abs "x" (Ty_Arrow Ty_Bool Ty_Bool) (tm_app (tm_var "x") (tm_var "x"))) (tm_abs "x" (Ty_Arrow Ty_Bool Ty_Bool) (tm_app (tm_var "x") (tm_var "x"))).

MetaRocq Run (r <- tmEval all (streamNth 30 (bigStepAnimatedTopFnStream (Success (tm) ((omega))))) ;; tmPrint r).
Check bigStepAnimatedTopFnStream.
Definition testTm' : tm :=
tm_app (tm_abs "x" (Ty_Arrow Ty_Bool Ty_Bool) (tm_var "x")) (tm_app (tm_abs "x" (Ty_Arrow Ty_Bool Ty_Bool) (tm_var "x")) (tm_abs "x" (Ty_Bool) (tm_var "x"))).

MetaRocq Run (r <- tmEval all (streamNth 30 (bigStepAnimatedTopFnStream (Success (tm) ((testTm'))))) ;; tmPrint r).

End STLC.




Module StackStep. 
Definition total_map (A : Type) := string -> A.
Definition state := total_map nat.


Compute <%state%>.


   

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.
(*
Fixpoint decEqsinstr : forall (t1 t2 : sinstr), {t1 = t2} + {t1 <> t2}.
Proof.

  decide equality. decide equality. decide equality. decide equality. 
Defined.

*)
Definition stack := list nat.
Definition prog := list sinstr.


(*
Definition eqFnsinstr (t1 t2 : sinstr) : bool :=

  if decEqsinstr t1 t2 then true else false.  
*)    
(*
Inductive stack_step (st : state) : prog × stack → prog × stack → Prop :=
  | SS_Push : ∀ stk n p,
    stack_step st (SPush n :: p, stk) (p, n :: stk)
  | SS_Load : ∀ stk i p,
    stack_step st (SLoad i :: p, stk) (p, st i :: stk)
  | SS_P : ∀ stk n m p,
    stack_step st (SPlus :: p, n::m::stk) (p, (m+n)::stk)
  | SS_Minus : ∀ stk n m p,
    stack_step st (SMinus :: p, n::m::stk) (p, (m-n)::stk)
  | SS_Mult : ∀ stk n m p,
    stack_step st (SMult :: p, n::m::stk) (p, (m×n)::stk).
*)

 
Inductive stack_step : (state) -> list sinstr × list nat -> list sinstr × list nat -> Prop :=
   | SS_Push : forall  st stk n p,
    stack_step st (SPush n :: p, stk) (p, n :: stk) 
  
(* Need to fix *)    
   | SS_Load : forall  st stk i p,
    stack_step st (SLoad i :: p, stk) (p, (((  st)) i) :: stk) 
    
  | SS_P : forall st stk n m p,
    stack_step st (SPlus :: p, n::m::stk) (p, (m+n)::stk)  
   | SS_Minus : forall st stk n m p,
    stack_step st (SMinus :: p, n::m::stk) (p, (m-n)::stk) 
   | SS_Mult : forall st stk n m p,
    stack_step st (SMult :: p, n::m::stk) (p, (m*n)::stk)  .
    
    
    
MetaRocq Run (animateInductive stack_step <?stack_step?> [("stack_step",([0;1],[2]))] 200).

End StackStep.

Module ImpSem.



CoInductive coVars : Type :=
| pure : ((nat -> nat)) -> coVars
| undefinedCoV : coVars.
Compute <%coVars%>.


Definition set (vs : (nat -> nat)) (v : nat) (n : nat) :  (nat -> nat) :=
 (fun v' => if Nat.eqb v v' then n else vs v'). 


  

Inductive exp : Type :=
| Const : nat -> exp
| Var : nat -> exp
| Plus : exp -> exp -> exp.

Fixpoint evalExp (vs : (nat -> nat)) (e : exp) : nat :=
  match e with
    | Const n => n
    | Var v => (vs) v
    | Plus e1 e2 => evalExp (vs) e1 + evalExp (vs) e2
  end.
  
Inductive cmd : Type :=
| Assign : nat -> exp -> cmd
| Seq : cmd -> cmd -> cmd
| While : exp -> cmd -> cmd.
(*
CoInductive coList : Type := 
| undefinedLst : coList
| coNil : coList
| coCons : coVars -> coList -> coList. 
Definition eqcoList (s1 : coList) (s2 : coList) : bool := 
match s1 with
| undefinedLst => match s2 with
                   | undefinedLst => false
                   | _ => false
                   end
| coNil =>         match s2 with
                   | coNil => true
                   | _ => false
                   end         
| _s3 => match s2 with
        | undefinedLst => false
        | coNil => false
        | _ => false
        end                   
end.
*)
(*
CoInductive evalCmd : vars -> cmd -> vars -> Prop :=
| EvalAssign : forall vs v e, evalCmd vs (Assign v e) (set vs v (evalExp vs e))
| EvalSeq : forall vs1 vs2 vs3 c1 c2, evalCmd vs1 c1 vs2
  /\ evalCmd vs2 c2 vs3
  -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs e c, evalExp vs e = 0
  -> evalCmd vs (While e c) vs
| EvalWhileTrue : forall vs1 vs2 vs3 e c, evalExp vs1 e <> 0
  /\ evalCmd vs1 c vs2
  /\ evalCmd vs2 (While e c) vs3
  -> evalCmd vs1 (While e c) vs3 .  

Parameter evalCmdRest : (vars * cmd) -> vars.

MetaRocq Run (animateCoinductive evalCmd <? evalCmd ?> [("evalCmd", ([0;1], [2]))] 500).
*)


CoInductive evalCmd : coVars -> cmd -> coVars -> Prop :=
| EvalAssign : forall vs' vs v e, vs' = pure vs -> evalCmd vs' (Assign v e)  (pure (set vs v (evalExp vs e))) 
| EvalSeq : forall vs1 vs2 vs3 c1 c2, evalCmd vs1 c1 vs2
  /\ evalCmd vs2 c2 vs3 -> evalCmd vs1 (Seq c1 c2) vs3


| EvalWhileFalse : forall vs' vs e c, vs' = pure vs /\ evalExp vs e = 0
  -> evalCmd vs' (While e c) vs'
  

  
| EvalWhileTrue : forall vs1' vs2' vs3' vs1 e c, vs1' = pure vs1 /\
      evalExp vs1 e <> 0
  /\ evalCmd vs1' c vs2'
  /\ evalCmd vs2' (While e c) vs3'
  -> evalCmd vs1' (While e c) vs3'

| EvalUndef : forall c c', evalCmd c c' undefinedCoV.


(*   
Definition eqFncoVars (c : coVars) (c1 : coVars) : bool :=
match c with
| undefinedCoV => match c1 with
                  | undefinedCoV => true
                  | _   => false
                  end
| _c3 => match c1 with
         | undefinedCoV => false
         | _ => true 
         end
end.                            
*)

Definition evalCmdRest := fun vc : (coVars * cmd) => undefinedCoV.

MetaRocq Run (animateCoinductive evalCmd <? evalCmd ?> [("evalCmd", ([0;1], [2]))] 500).

Definition prog :=
While (Var 4) (Assign 8 (Const 8)).


Definition initFn :=
pure (fun m : nat => m + 1).



MetaRocq Run (r <- tmEval all (streamNth 25 (evalCmdAnimatedTopFnStream (Success (coVars * cmd) (initFn, prog)))) ;; tmPrint r).



Definition prog' :=
While (Var 0) (Assign 8 (Const 9)).


Definition initFn' :=
pure  (fun m : nat => m).

MetaRocq Run (r <- tmEval all (streamNth 25 (evalCmdAnimatedTopFnStream (Success (coVars * cmd) (initFn', prog')))) ;; tmPrint r).

End ImpSem.

Module ImpSemTr.



CoInductive coVars : Type :=

| empty : coVars
| pure : ((nat -> nat)) -> coVars
| undefinedCoV : coVars.
CoInductive coVarsTr : Type :=
| coVNil : coVarsTr
| covSeq : coVars -> coVarsTr -> coVarsTr
| undefinedCoVTr : coVarsTr.



Definition set (vs :  (nat -> nat)) (v : nat) (n : nat) : (nat -> nat) :=
 (fun v' => if Nat.eqb v v' then n else vs v').


  

Inductive exp : Type :=
| Const : nat -> exp
| Var : nat -> exp
| Plus : exp -> exp -> exp.

Fixpoint evalExp (vs : (nat -> nat)) (e : exp) : nat :=
  match e with
    | Const n => n
    | Var v => (vs) v
    | Plus e1 e2 => evalExp (vs) e1 + evalExp (vs) e2
  end.
  
Inductive cmd : Type :=
| Assign : nat -> exp -> cmd
| Seq : cmd -> cmd -> cmd
| While : exp -> cmd -> cmd.
(*
CoInductive coList : Type := 
| undefinedLst : coList
| coNil : coList
| coCons : coVars -> coList -> coList. 
Definition eqcoList (s1 : coList) (s2 : coList) : bool := 
match s1 with
| undefinedLst => match s2 with
                   | undefinedLst => false
                   | _ => false
                   end
| coNil =>         match s2 with
                   | coNil => true
                   | _ => false
                   end         
| _s3 => match s2 with
        | undefinedLst => false
        | coNil => false
        | _ => false
        end                   
end.
*)
(*
CoInductive evalCmd : vars -> cmd -> vars -> Prop :=
| EvalAssign : forall vs v e, evalCmd vs (Assign v e) (set vs v (evalExp vs e))
| EvalSeq : forall vs1 vs2 vs3 c1 c2, evalCmd vs1 c1 vs2
  /\ evalCmd vs2 c2 vs3
  -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs e c, evalExp vs e = 0
  -> evalCmd vs (While e c) vs
| EvalWhileTrue : forall vs1 vs2 vs3 e c, evalExp vs1 e <> 0
  /\ evalCmd vs1 c vs2
  /\ evalCmd vs2 (While e c) vs3
  -> evalCmd vs1 (While e c) vs3 .  

Parameter evalCmdRest : (vars * cmd) -> vars.

MetaRocq Run (animateCoinductive evalCmd <? evalCmd ?> [("evalCmd", ([0;1], [2]))] 500).
*)


CoInductive evalCmd : coVars -> cmd -> coVarsTr -> Prop :=
| EvalEmpty : forall c', evalCmd empty c' coVNil
| EvalAssign : forall vs' vs v e, vs' = pure vs -> evalCmd vs' (Assign v e)  (covSeq (pure (set vs v (evalExp vs e))) coVNil)
| EvalSeq : forall vs1 vs2 vs2' vs3 vs4 c1 c2, evalCmd vs1 c1 vs2 /\ last vs2 vs2' /\ appTr vs2 vs3 vs4
  /\ evalCmd vs2' c2 vs3 -> evalCmd vs1 (Seq c1 c2) vs4


| EvalWhileFalse : forall vs' vs e c, vs' = pure vs /\ evalExp vs e = 0
  -> evalCmd vs' (While e c) (covSeq vs' coVNil)
  

  
| EvalWhileTrue : forall vs1' vs2' vs2'' vs3' vs1 vs4 e c, vs1' = pure vs1 /\
      evalExp vs1 e <> 0
  /\ evalCmd vs1' c vs2' /\ last vs2' vs2''
  /\ evalCmd vs2'' (While e c) vs3' /\ appTr vs2' vs3' vs4
  -> evalCmd vs1' (While e c) vs4

| EvalUndef : forall c c', evalCmd c c' undefinedCoVTr
with last : coVarsTr -> coVars -> Prop :=
| lastEmpty : last coVNil empty
| lastNil: forall  c c1, c1 = c -> last (covSeq c coVNil) c1 
| lastSeq : forall c c' ctr, last ctr c -> last (covSeq c' ctr) c
| lastUndef : forall ctr, last ctr undefinedCoV
with appTr : coVarsTr -> coVarsTr -> coVarsTr -> Prop :=
| appNil : forall ctr ctr', ctr' = ctr -> appTr coVNil ctr ctr
| appSeq : forall c c1 ctr ctr' ctr'', appTr ctr ctr' ctr''/\ c1 = c -> appTr (covSeq c ctr) ctr' (covSeq c1 ctr'') 
| appUndef : forall ctr ctr1, appTr ctr ctr1 undefinedCoVTr.   


   
Definition eqFncoVars (c : coVars) (c1 : coVars) : bool :=
match c with
| empty => match c1 with
                  | empty => true
                  | _   => false
                  end
| _ => false
end.                            

Definition eqFncoVarsTr (c : coVarsTr) (c1 : coVarsTr) : bool :=
match c with
| coVNil => match c1 with
                  | coVNil => true
                  | _   => false
                  end
| _ => false
end.     
Definition evalCmdRest := fun vc : (coVars * cmd) => undefinedCoVTr.
Definition lastRest := fun ct : coVarsTr => undefinedCoV.
Definition appTrRest := fun ctct : (coVarsTr * coVarsTr) => undefinedCoVTr. 


MetaRocq Run (animateCoinductive evalCmd <? evalCmd ?> [("evalCmd", ([0;1], [2]));("last", ([0], [1]));("appTr", ([0;1], [2]))] 500).

Definition prog :=
While (Var 4) (Assign 8 (Const 8)).

Definition add1 := fun m : nat => m + 1.
Definition initFn :=
pure ( add1).



MetaRocq Run (r <- tmEval all (streamNth 30 (evalCmdAnimatedTopFnStream (Success (coVars * cmd) (initFn, prog)))) ;; tmPrint r).



Definition prog' :=
While (Var 4) (Seq (Assign 4 (Var 3)) (Seq (Assign 3 (Var 2)) (Seq (Assign 2 (Var 1)) (Assign 1 (Var 0))))).


Definition initFn' :=
pure ( (fun m : nat => m)).

MetaRocq Run (r <- tmEval all (streamNth 40 (evalCmdAnimatedTopFnStream (Success (coVars * cmd) (initFn', prog')))) ;; tmPrint r).

End ImpSemTr.



   
