(** * TestSTLC: Simply Typed Lambda Calculus
    Tests animation of STLC typing and small-step reduction.
    Demonstrates the animation of mutually defined relations and
    relations that call auxiliary Fixpoint functions (substitution). *)

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


(** ** STLC Typing *)

Module STLCTyping.

Inductive ty : Type :=
| TBool : ty
| TArrow : ty -> ty -> ty.

Inductive tm : Type :=
| tcon : nat -> tm
| tadd : tm -> tm -> tm
| tvar : nat -> tm
| tapp : tm -> tm -> tm
| tabs : ty -> tm -> tm.

Fixpoint decEqTy : forall (t1 t2 : ty), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Fixpoint decEqTm : forall (t1 t2 : tm), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. decide equality. decide equality. decide equality. Defined.

Definition eqFnty (t1 t2 : ty) : bool :=
  if decEqTy t1 t2 then true else false.

Definition eqFntm (t1 t2 : tm) : bool :=
  if decEqTm t1 t2 then true else false.

Inductive typing : list ty -> tm -> ty -> Prop :=
| TCon : forall (n : nat) (cxt : list ty), typing cxt (tcon n) TBool

| TAdd : forall (e1 e2 : tm) (cxt : list ty),
    typing cxt e1 TBool /\ typing cxt e2 TBool ->
    typing cxt (tadd e1 e2) TBool

| TAbs : forall (e : tm) (t1 t2 : ty) (cxt cxt' : list ty),
    cxt' = t1 :: cxt /\ typing cxt' e t2 ->
    typing cxt (tabs t1 e) (TArrow t1 t2)

| TVar : forall (j : nat) (t : ty) (cxt : list ty),
    lookup cxt j t -> typing cxt (tvar j) t

| TApp : forall (e1 e2 : tm) (t1 t2 : ty) (cxt : list ty),
    typing cxt e2 t1 /\ typing cxt e1 (TArrow t1 t2) ->
    typing cxt (tapp e1 e2) t2

with lookup : list ty -> nat -> ty -> Prop :=
| LookupHere : forall (t : ty) (cxt : list ty), lookup (t :: cxt) 0 t
| LookupThere : forall (m : nat) (t t' : ty) (cxt : list ty),
    lookup cxt m t -> lookup (t' :: cxt) (S m) t.

MetaRocq Run (animate_inductive typing <?typing?> [("typing", ([0;1], [2])); ("lookup", ([0;1], [2]))] 100).

(* --- Typing tests --- *)

(* A constant has type TBool *)
Example test_typing_con :
  typingAnimatedTopFn 50
    (Success (list ty * tm) ([], tcon 5))
  = Success ty TBool.
Proof. reflexivity. Qed.

(* Lambda abstraction: \x:TBool. con 5 has type TBool -> TBool *)
Example test_typing_tabs_tcon :
  typingAnimatedTopFn 50
    (Success (list ty * tm) ([], tabs TBool (tcon 5)))
  = Success ty (TArrow TBool TBool).
Proof. reflexivity. Qed.

(* Addition of two constants *)
Example test_typing_tadd :
  typingAnimatedTopFn 50
    (Success (list ty * tm) ([], tadd (tcon 1) (tcon 2)))
  = Success ty TBool.
Proof. reflexivity. Qed.

(* Lambda with variable reference: \x:TBool. x has type TBool -> TBool *)
Example test_typing_tabs_tvar :
  typingAnimatedTopFn 50
    (Success (list ty * tm) ([], tabs TBool (tvar 0)))
  = Success ty (TArrow TBool TBool).
Proof. reflexivity. Qed.

(* Application: (\x:TBool. x) (con 3) has type TBool *)
Example test_typing_tapp :
  typingAnimatedTopFn 50
    (Success (list ty * tm) ([], tapp (tabs TBool (tvar 0)) (tcon 3)))
  = Success ty TBool.
Proof. reflexivity. Qed.

(* Nested abstraction: \f:TBool->TBool. \x:TBool. f x *)
Example test_typing_nested_tabs :
  typingAnimatedTopFn 50
    (Success (list ty * tm) ([], tabs (TArrow TBool TBool)
                                         (tabs TBool (tapp (tvar 1) (tvar 0)))))
  = Success ty (TArrow (TArrow TBool TBool) (TArrow TBool TBool)).
Proof. reflexivity. Qed.

(* Ill-typed: adding a lambda and a constant should fail *)
Example test_typing_ill_typed_tadd :
  typingAnimatedTopFn 50
    (Success (list ty * tm) ([], tadd (tabs TBool (tcon 1)) (tcon 2)))
  = NoMatch ty.
Proof. reflexivity. Qed.

(* Type mismatch in application: (\f:TBool->TBool. f) applied to a constant *)
Example test_typing_ill_typed_tapp :
  typingAnimatedTopFn 50
    (Success (list ty * tm) ([], tapp (tabs (TArrow TBool TBool) (tvar 0)) (tcon 5)))
  = NoMatch ty.
Proof. reflexivity. Qed.

End STLCTyping.


(** ** STLC Small-Step Reduction *)

Module STLCStep.

Inductive ty : Type :=
| TBool : ty
| TArrow : ty -> ty -> ty.

Inductive tm : Type :=
| tvar : string -> tm
| tapp : tm -> tm -> tm
| tabs : string -> ty -> tm -> tm
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm.

Definition eqFnty (t1 t2 : ty) : bool :=
  match t1, t2 with
  | TBool, TBool => true
  | TArrow a1 b1, TArrow a2 b2 => false
  | _, _ => false
  end.

Definition eqFntm (t1 t2 : tm) : bool :=
  match t1, t2 with
  | ttrue, ttrue => true
  | tfalse, tfalse => true
  | _, _ => false
  end.

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tvar y => if String.eqb x y then s else t
  | tabs y T t1 => if String.eqb x y then t else tabs y T (subst x s t1)
  | tapp t1 t2 => tapp (subst x s t1) (subst x s t2)
  | ttrue => ttrue
  | tfalse => tfalse
  | tif t1 t2 t3 => tif (subst x s t1) (subst x s t2) (subst x s t3)
  end.

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall (z : string) (T : ty) (t w : tm),
    step (tapp (tabs z T t) w) (subst z w t)
| ST_App1 : forall (t1 t1' t2 : tm),
    step t1 t1' ->
    step (tapp t1 t2) (tapp t1' t2)
| ST_IfTrue : forall (t1 t2 : tm),
    step (tif ttrue t1 t2) t1
| ST_IfFalse : forall (t1 t2 : tm),
    step (tif tfalse t1 t2) t2
| ST_If : forall (t1 t1' t2 t3 : tm),
    step t1 t1' ->
    step (tif t1 t2 t3) (tif t1' t2 t3).

MetaRocq Run (animate_inductive step <?step?> [("step", ([0], [1]))] 100).

(* --- Step tests --- *)

(* Beta reduction: (\x:Bool. x) true --> true *)
Example test_step_app_abs_true :
  stepAnimatedTopFn 50
    (Success tm (tapp (tabs "x" TBool (tvar "x")) ttrue))
  = Success tm ttrue.
Proof. reflexivity. Qed.

(* Beta reduction: (\x:Bool. x) false --> false *)
Example test_step_app_abs_false :
  stepAnimatedTopFn 50
    (Success tm (tapp (tabs "x" TBool (tvar "x")) tfalse))
  = Success tm tfalse.
Proof. reflexivity. Qed.

(* If-true: if true then t else f --> t *)
Example test_step_if_true :
  stepAnimatedTopFn 50
    (Success tm (tif ttrue ttrue tfalse))
  = Success tm ttrue.
Proof. reflexivity. Qed.

(* If-false: if false then t else f --> f *)
Example test_step_if_false :
  stepAnimatedTopFn 50
    (Success tm (tif tfalse ttrue tfalse))
  = Success tm tfalse.
Proof. reflexivity. Qed.

(* Step under application: ((\x. x) true) false --> true false *)
Example test_step_app1 :
  stepAnimatedTopFn 50
    (Success tm (tapp (tapp (tabs "x" TBool (tvar "x")) ttrue) tfalse))
  = Success tm (tapp ttrue tfalse).
Proof. reflexivity. Qed.

(* Value: true cannot step *)
Example test_step_value_no_step :
  stepAnimatedTopFn 50
    (Success tm ttrue)
  = NoMatch tm.
Proof. reflexivity. Qed.

(* Step under if: if ((\x. x) true) then f else t --> if true then f else t *)
Example test_step_if_cond :
  stepAnimatedTopFn 50
    (Success tm (tif (tapp (tabs "x" TBool (tvar "x")) ttrue) tfalse ttrue))
  = Success tm (tif ttrue tfalse ttrue).
Proof. reflexivity. Qed.

End STLCStep.
