(** * TestStack: Stack Machine Step Relation
    Tests animation of a small-step stack machine relation.
    The machine executes a list of stack instructions over a state
    (variable environment) and a stack of natural numbers. *)

Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.
Require Import Animation.EqualityResolution.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.

From Stdlib Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.

Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.

Definition total_map (A : Type) := string -> A.
Definition state := total_map nat.

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

Definition eqFnsinstr (t1 t2 : sinstr) : bool :=
  if decEqsinstr t1 t2 then true else false.

Definition stack := list nat.
Definition prog  := list sinstr.



Inductive stack_step : state -> list sinstr * list nat -> list sinstr * list nat -> Prop :=
| SS_Push  : forall st stk n p ps0 ps1,
    ps0 = (SPush n :: p, stk) /\ ps1 = (p, n :: stk)
    -> stack_step st ps0 ps1 
| SS_Load  : forall st stk i p ps0 ps1,
    ps0 = (SLoad i :: p, stk) /\ ps1 = (p, (st) i :: stk)
    -> stack_step st ps0 ps1
| SS_Plus  : forall st stk n m p ps0 ps1,
    ps0 = (SPlus :: p, n :: m :: stk) /\ ps1 = (p, (m + n) :: stk)
    -> stack_step st ps0 ps1
| SS_Minus : forall st stk n m p ps0 ps1,
    ps0 = (SMinus :: p, n :: m :: stk) /\ ps1 = (p, (m - n) :: stk)
    -> stack_step st ps0 ps1
| SS_Mult  : forall st stk n m p ps0 ps1,
    ps0 = (SMult :: p, n :: m :: stk) /\ ps1 = (p, (m * n) :: stk)
    -> stack_step st ps0 ps1 .

MetaRocq Run (animate_inductive <? stack_step ?>
  [("stack_step", ([0;1], [2]))] 200).

Definition empty_state : state := fun (_ : string) => 0.
Definition one_state : state := fun (_ : string) => 1.

(** Push 3, push 4, then add: stack should end up as [7]. *)
Example Push : 
 (stack_stepAnimatedTopFn 50
  (Success (state * (list sinstr * list nat))
    (empty_state, ([SPush 3; SPush 4; SPlus], [])))) = (Success (list sinstr * list nat)
    ([SPush 4; SPlus], [3])). 
    Proof. reflexivity. Qed.

Example Load : 
 (stack_stepAnimatedTopFn 50
  (Success (state * (list sinstr * list nat))
    (one_state , ([SLoad "x"; SPush 2; SMinus], [4])))) = (Success (list sinstr * list nat)
    ([SPush 2; SMinus], [1;4])). Proof. reflexivity. Qed.

(** Push 3, push 4, then multiply: result [12]. *)
Example Mult :
(stack_stepAnimatedTopFn 50
  (Success (state * (list sinstr * list nat))
    (empty_state, ([SMult; SPush 2], [3;5;6])))) = Success (list sinstr × list nat) ([SPush 2], [15; 6]).
Proof. reflexivity. Qed.    
