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
(*
Inductive indTp (A : Type) : Type :=
| indWrap : A -> indTp A.

Compute <%indWrap (nat -> nat)%>.
*)

Print indTp.





Unset Universe Checking.

Definition animAllClTerm {A : Type} (ind : A) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad (term) :=
allClauseData <- getData' kn modes ;;

let clLst := clauseLst allClauseData in


tms <- animAllClLst ind kn clLst modes fuel ;;

let inductData := prodInOut (getFixptData allClauseData) in

let u := (mkrecFn (mkAllIndTop (inductData) kn) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (removeopTm (DB.deBruijnOption u)) ;;
          tmReturn t' (*;;
               f <- tmUnquote t';;
               tmPrint f ;;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append (snd kn) "AnimatedTopFn") (Some hnf) ;; tmReturn tms*).



Set Universe Checking.
(*

MetaRocq Run (myT <-animateListLetAndPredGuard10 trivialRel <? trivialRel ?> "trivCl2" [("f",<%nat -> nat%>); ("m", <%bool%>)] [("n", <%bool%>)] [("trivialRel",([0;1],[2]))] [("trivialRel",[<%nat -> nat%>; <%bool%>;<%bool%>])] 
               [("f",<%nat -> nat%>); ("m", <%bool%>);("n", <%bool%>)] [] 100 ;; tmDefinition "wrongT" myT).

MetaRocq Run (f <- tmUnquote wrongT ;; tmPrint f).
*)

Definition total_map (A : Type) := string -> A.
Definition state := total_map nat.

Definition eqFnstate (s1 s2 : state) : bool := true.

Inductive trivialRel : (*sinstr*) (state) ->  bool ->  bool -> Prop :=
 | trivCl : forall f n m, m = n ->  trivialRel f m n.

MetaRocq Run (animAllCl trivialRel <? trivialRel ?> [("trivialRel", ([0;1], [2]))] 200).
   
 
 
MetaRocq Run (animAllCl trivialRel <? trivialRel ?> [("trivialRel", ([0;1], [2]))] 200).
   




   

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Fixpoint decEqsinstr : forall (t1 t2 : sinstr), {t1 = t2} + {t1 <> t2}.
Proof.

  decide equality. decide equality. decide equality. decide equality. 
Defined.


Definition stack := list nat.
Definition prog := list sinstr.



Definition eqFnsinstr (t1 t2 : sinstr) : bool :=

  if decEqsinstr t1 t2 then true else false.  
    
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
Definition unwrap (A: Type) (x : indTp A) : A :=
match x with
| indWrap x' => x'
end.
Print indTp.
 
Inductive stack_step : (indTp state) -> list sinstr × list nat -> list sinstr × list nat -> Prop :=
   | SS_Push : forall  st stk n p ps0 ps1, ps0 = (SPush n :: p, stk) /\ ps1 = (p, n :: stk)  -> 
    stack_step st ps0 ps1 
   
    
   | SS_Load : forall  st stk i p ps0 ps1, ps0 = (SLoad i :: p, stk) /\ ps1 = (p, ((unwrap state st) i) :: stk) ->
    stack_step st ps0 ps1 
    
 | SS_P : forall st stk n m p ps0 ps1, ps0 = (SPlus :: p, n::m::stk) /\ ps1 = (p, (m+n)::stk) ->
    stack_step st ps0 ps1 
  | SS_Minus : forall st stk n m p ps0 ps1, ps0 = (SMinus :: p, n::m::stk) /\ ps1 = (p, (m-n)::stk) ->
    stack_step st ps0 ps1 
  | SS_Mult : forall st stk n m p ps0 ps1, ps0 = (SMult :: p, n::m::stk) /\ ps1 = (p, (m*n)::stk) ->
    stack_step st ps0 ps1 . 

    
MetaRocq Run (animAllCl stack_step <? stack_step ?> [("stack_step", ([0;1], [2]))] 500).


