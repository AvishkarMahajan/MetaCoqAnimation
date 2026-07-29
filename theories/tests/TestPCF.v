(** * TestPCF: Call-by-Value PCF Big-Step Semantics
    Standard CBV big-step evaluation for PCF (Programming Computable Functions),
    following Section 2 of:
      "Big-Stop Semantics: Small-Step Semantics in a Big-Step Judgment"
      Kahn, Hoffmann, Li — POPL 2026.
    (This file formalises the ordinary big-step semantics, not the BigStop extension.) *)

Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.
Require Import Animation.EqualityResolution.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.
Require Import Animation.coIndPreProc.
From Stdlib Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.
Import MetaRocqNotations.
Local Open Scope nat_scope.
Open Scope bs.

Module PCFBigStep.

(* ------------------------------------------------------------------ *)
(** ** Syntax                                                          *)
(* ------------------------------------------------------------------ *)

Inductive ty : Type :=
| TNat   : ty
| TArrow : ty -> ty -> ty.

(** Terms include variables (string names), abstractions, application,
    the natural-number spine (zero/succ/pred), a conditional on zero,
    and the general-recursion operator fix. *)
Inductive tm : Type :=
| tvar  : string -> tm
| tabs  : string -> ty -> tm -> tm
| tapp  : tm -> tm -> tm
| tzero : tm
| tsucc : tm -> tm
| tpred : tm -> tm
| tifz  : tm -> tm -> tm -> tm   (** ifz e e1 e2 : if e = 0 then e1 else e2 *)
| tfix  : string -> ty -> tm -> tm.

(* ------------------------------------------------------------------ *)
(** ** Equality (needed by the animation framework)                   *)
(* ------------------------------------------------------------------ *)

Fixpoint eqFnty (t1 t2 : ty) : bool :=
  match t1, t2 with
  | TNat, TNat           => true
  | TArrow a1 b1, TArrow a2 b2 => andb (eqFnty a1 a2) (eqFnty b1 b2)
  | _, _                 => false
  end.

Fixpoint eqFntm (t1 t2 : tm) : bool :=
  match t1, t2 with
  | tvar x,  tvar y  => String.eqb x y
  | tabs x T1 e1, tabs y T2 e2 =>
      andb (String.eqb x y) (andb (eqFnty T1 T2) (eqFntm e1 e2))
  | tapp e1 e2, tapp e3 e4 =>
      andb (eqFntm e1 e3) (eqFntm e2 e4)
  | tzero, tzero => true
  | tsucc e1, tsucc e2 => eqFntm e1 e2
  | tpred e1, tpred e2 => eqFntm e1 e2
  | tifz e1 e2 e3, tifz e4 e5 e6 =>
      andb (eqFntm e1 e4) (andb (eqFntm e2 e5) (eqFntm e3 e6))
  | tfix f T1 e1, tfix g T2 e2 =>
      andb (String.eqb f g) (andb (eqFnty T1 T2) (eqFntm e1 e2))
  | _, _ => false
  end.

(* ------------------------------------------------------------------ *)
(** ** Capture-avoiding substitution                                  *)
(* ------------------------------------------------------------------ *)

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tvar y          => if String.eqb x y then s else t
  | tabs y T t1     => if String.eqb x y then t else tabs y T (subst x s t1)
  | tapp t1 t2      => tapp (subst x s t1) (subst x s t2)
  | tzero           => tzero
  | tsucc t1        => tsucc (subst x s t1)
  | tpred t1        => tpred (subst x s t1)
  | tifz t1 t2 t3   => tifz (subst x s t1) (subst x s t2) (subst x s t3)
  | tfix f T t1     => if String.eqb x f then t else tfix f T (subst x s t1)
  end.

(* ------------------------------------------------------------------ *)
(** ** CBV big-step evaluation                                         *)
(*                                                                     *)
(*  Values: tabs (lambda), tzero, tsucc v.                             *)
(*  eval e v  means  e evaluates to value v.                           *)
(* ------------------------------------------------------------------ *)

CoInductive eval : tm -> tm -> Prop :=

| E_Lam : forall x T t,
    eval (tabs x T t) (tabs x T t)

| E_Zero :
    eval tzero tzero

| E_Succ : forall t v,
    eval t v ->
    eval (tsucc t) (tsucc v)

| E_PredZero : forall t,
    eval t tzero ->
    eval (tpred t) tzero

| E_PredSucc : forall t v,
    eval t (tsucc v) ->
    eval (tpred t) v

(** CBV application: evaluate operator to a lambda, evaluate argument,
    then evaluate the substituted body. *)
| E_App : forall t1 t2 x T t3 v2 v,
    eval t1 (tabs x T t3) /\ eval t2 v2 /\ eval (subst x v2 t3) v ->
    eval (tapp t1 t2) v

(** ifz: zero branch *)
| E_IfzZero : forall t t1 t2 v,
    eval t tzero /\ eval t1 v ->
    eval (tifz t t1 t2) v

(** ifz: successor branch (the value of the discriminant is discarded) *)
| E_IfzSucc : forall t vn t1 t2 v,
    eval t (tsucc vn) /\ eval t2 v ->
    eval (tifz t t1 t2) v

(** Fixpoint: unroll once, then evaluate the substituted body. *)
| E_Fix : forall f T t v,
    eval (subst f (tfix f T t) t) v ->
    eval (tfix f T t) v.

MetaRocq Run (animate_coinductive_transparent <?eval?> [("eval", ([0], [1]))] 500).

(* ------------------------------------------------------------------ *)
(** ** Helper: PCF numeral [num n] = succ^n zero                      *)
(* ------------------------------------------------------------------ *)

Fixpoint num (n : nat) : tm :=
  match n with
  | O   => tzero
  | S m => tsucc (num m)
  end.

(** The [double] function in PCF:
    fix f:nat→nat. λx:nat. ifz x  zero  (succ (succ (f (pred x)))) *)
Definition double :=
  tfix "f" (TArrow TNat TNat)
    (tabs "x" TNat
      (tifz (tvar "x")
            tzero
            (tsucc (tsucc (tapp (tvar "f") (tpred (tvar "x"))))))).

(* ------------------------------------------------------------------ *)
(** ** Tests                                                           *)
(* ------------------------------------------------------------------ *)

(** zero is a value *)
Example test_eval_zero :
  evalTransparentAnimatedTopFn 50 (Success tm tzero)
  = Success tm tzero.
Proof. reflexivity. Qed.

(** numerals are values *)
Example test_eval_numeral :
  evalTransparentAnimatedTopFn 50 (Success tm (num 3))
  = Success tm (num 3).
Proof. reflexivity. Qed.

(** pred(zero) = zero *)
Example test_eval_pred_zero :
  evalTransparentAnimatedTopFn 50 (Success tm (tpred tzero))
  = Success tm tzero.
Proof. reflexivity. Qed.

(** pred(succ(succ(zero))) = succ(zero) *)
Example test_eval_pred_succ :
  evalTransparentAnimatedTopFn 50 (Success tm (tpred (num 2)))
  = Success tm (num 1).
Proof. reflexivity. Qed.

(** lambda is a value *)
Example test_eval_lam :
  evalTransparentAnimatedTopFn 50 (Success tm (tabs "x" TNat (tvar "x")))
  = Success tm (tabs "x" TNat (tvar "x")).
Proof. reflexivity. Qed.

(** identity function applied to zero: (λx.x) 0 → 0 *)
Example test_eval_app_id_zero :
  evalTransparentAnimatedTopFn 100 (Success tm (tapp (tabs "x" TNat (tvar "x")) tzero))
  = Success tm tzero.
Proof. reflexivity. Qed.

(** (λx. succ x) 0 → succ 0 *)
Example test_eval_app_succ_body :
  evalTransparentAnimatedTopFn 100
    (Success tm (tapp (tabs "x" TNat (tsucc (tvar "x"))) tzero))
  = Success tm (num 1).
Proof. reflexivity. Qed.

(** ifz 0 1 2 → 1  (zero branch) *)
Example test_eval_ifz_zero :
  evalTransparentAnimatedTopFn 100 (Success tm (tifz tzero (num 1) (num 2)))
  = Success tm (num 1).
Proof. reflexivity. Qed.

(** ifz 1 1 2 → 2  (successor branch) *)
Example test_eval_ifz_succ :
  evalTransparentAnimatedTopFn 100 (Success tm (tifz (num 1) (num 1) (num 2)))
  = Success tm (num 2).
Proof. reflexivity. Qed.

(** Constant fixpoint: (fix f:nat→nat. λx. 0) 1 → 0
    The body never references f, so it terminates in one unrolling. *)
Example test_eval_fix_const :
  evalTransparentAnimatedTopFn 200
    (Success tm (tapp
      (tfix "f" (TArrow TNat TNat) (tabs "x" TNat tzero))
      (num 1)))
  = Success tm tzero.
Proof. reflexivity. Qed.

(** double 0 = 0 *)
Example test_eval_double_zero :
  evalTransparentAnimatedTopFn 500 (Success tm (tapp double tzero))
  = Success tm tzero.
Proof. reflexivity. Qed.

(** double 1 = 2 *)
Example test_eval_double_one :
  evalTransparentAnimatedTopFn 500 (Success tm (tapp double (num 1)))
  = Success tm (num 2).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Non-terminating terms                                           *)
(*                                                                     *)
(*  Each term diverges because E_Fix unrolls indefinitely.             *)
(*  With finite fuel the animator exhausts its steps; the Compute      *)
(*  shows the partial result (typically an fnSymb sentinel).           *)
(* ------------------------------------------------------------------ *)

(** omega_nat = fix f:nat. f
    E_Fix: eval(f[omega_nat/f]) = eval(omega_nat) → forever *)
Definition omega_nat : tm :=
  tfix "f" TNat (tvar "f").

Compute (evalTransparentAnimatedTopFn 10 (Success tm omega_nat)).

(** omega_fn = fix f:nat→nat. f
    Evaluating (omega_fn applied to 0) first evaluates the operator, which diverges. *)
Definition omega_fn : tm :=
  tfix "f" (TArrow TNat TNat) (tvar "f").

Compute (evalTransparentAnimatedTopFn 20 (Success tm (tapp omega_fn tzero))).

(** omega_succ = fix f:nat→nat. λx. f (succ x)
    Applied to 0: each unrolling increments the argument, never reaching a base case. *)
Definition omega_succ : tm :=
  tfix "f" (TArrow TNat TNat)
    (tabs "x" TNat (tapp (tvar "f") (tsucc (tvar "x")))).

Compute (evalTransparentAnimatedTopFn 40 (Success tm (tapp omega_succ tzero))).

(* ------------------------------------------------------------------ *)
(** ** CBV small-step semantics                                        *)
(*                                                                     *)
(*  Values: lambda abstractions, zero, and succ applied to a value.   *)
(*  step t t'  means t reduces to t' in one step.                     *)
(* ------------------------------------------------------------------ *)

Inductive is_value : tm -> Prop :=
| V_Lam  : forall x T t,  is_value (tabs x T t)
| V_Zero :                 is_value tzero
| V_Succ : forall v,       is_value v -> is_value (tsucc v).

Inductive step : tm -> tm -> Prop :=
(** Beta reduction: operator is a lambda, argument is a value. *)
| ST_AppAbs  : forall x T t v,
    is_value v ->
    step (tapp (tabs x T t) v) (subst x v t)
(** Reduce the operator first. *)
| ST_App1    : forall t1 t1' t2,
    step t1 t1' ->
    step (tapp t1 t2) (tapp t1' t2)
(** Operator is a value; reduce the argument. *)
| ST_App2    : forall v t2 t2',
    is_value v /\ step t2 t2' ->
    step (tapp v t2) (tapp v t2')
(** Reduce under succ. *)
| ST_Succ    : forall t t',
    step t t' ->
    step (tsucc t) (tsucc t')
(** pred zero → zero *)
| ST_PredZero :
    step (tpred tzero) tzero
(** pred (succ v) → v *)
| ST_PredSucc : forall v,
    is_value v ->
    step (tpred (tsucc v)) v
(** Reduce under pred. *)
| ST_Pred    : forall t t',
    step t t' ->
    step (tpred t) (tpred t')
(** ifz zero t1 t2 → t1 *)
| ST_IfzZero : forall t1 t2,
    step (tifz tzero t1 t2) t1
(** ifz (succ v) t1 t2 → t2 *)
| ST_IfzSucc : forall v t1 t2,
    is_value v ->
    step (tifz (tsucc v) t1 t2) t2
(** Reduce the discriminant of ifz. *)
| ST_Ifz     : forall t t' t1 t2,
    step t t' ->
    step (tifz t t1 t2) (tifz t' t1 t2)
(** Unroll fixpoint by one step. *)
| ST_Fix     : forall f T t,
    step (tfix f T t) (subst f (tfix f T t) t).
    
Inductive stepRTCBounded : tm -> nat -> tm -> Prop :=
| RTCVal : forall t m, is_value t -> stepRTCBounded t m t
| RTC0 : forall t, stepRTCBounded t 0 t
| RTCSuccVal : forall t m t', stepRTCBounded t m t' /\ is_value t'-> stepRTCBounded t (S m) t'  
| RTCSuccValst : forall t m t' t'', stepRTCBounded t m t' /\ step t' t''-> stepRTCBounded t (S m) t''.

MetaRocq Run (animate_inductive <?stepRTCBounded?> [("stepRTCBounded", ([0;1], [2])); ("step", ([0],[1])); ("is_value", ([0],[]))] 800).


Compute (evalTransparentAnimatedTopFn 55 (Success tm (tapp omega_succ tzero))).  

(*
Compute (stepRTCBoundedAnimatedTopFn 200 (Success (tm * nat) (tapp omega_succ tzero, 14))).
*)  
Compute  (subst "x"
               (tsucc (tsucc (tsucc (tsucc ((tsucc (tsucc tzero)))))))
               (tapp (tfix "f" (TArrow TNat TNat) (tabs "x" TNat (tapp (tvar "f") (tsucc (tvar "x")))))
                  (tsucc (tvar "x")))). 
                  
                  
(*
StepRTC bounded inductive animation with input : (tapp omega_succ tzero, 14)  
Success tm
         (tapp (tfix "f" (TArrow TNat TNat) (tabs "x" TNat (tapp (tvar "f") (tsucc (tvar "x")))))
            (tsucc (tsucc (tsucc (tsucc (tsucc (tsucc (tsucc tzero))))))))
     : animation_result tm
     
eval coinductive animation input (tapp omega_succ tzero) fuel : 55

(evalAn1fnSymb
            (substLiftedCstrfnSymb "x"
               (tsucc (tsucc (tsucc (tsucc (evalAn1fnSymb (tsucc (tsucc tzero)))))))
               (tapp (tfix "f" (TArrow TNat TNat) (tabs "x" TNat (tapp (tvar "f") (tsucc (tvar "x")))))
                  (tsucc (tvar "x")))))
 
using evalAn1fnSymb t = t' => eval t t' 
substLiftCsstrfnSymb = subst
the result evaluates to 
eval1An1fnSymb 
(tapp (tfix "f" (TArrow TNat TNat) (tabs "x" TNat (tapp (tvar "f") (tsucc (tvar "x")))))
         (tsucc (tsucc (tsucc (tsucc (tsucc (tsucc (tsucc tzero))))))))
                       

In bigStop paper : bigStop = smallstepRTCBounded
Aim : Demonstrate that bigStep animated using coinductive animation = evalAn1fnSymb (smallstepRTCBounded)
=> bigStep-coind animation = evalAn1fnSymb (bigStop)     
*) 

(* ------------------------------------------------------------------ *)
(** ** Big-Stop Semantics (Kahn, Hoffmann, Li — POPL 2026, Figure 5) *)
(*                                                                     *)
(*  The judgment [bigstop e e'] means that e partially evaluates to   *)
(*  e' in finitely many steps; e' need not be a value.                *)
(*                                                                     *)
(*  Rules split into two groups:                                       *)
(*  - Stopping rules (St-Stop schema): nondeterministically halt at   *)
(*    any sub-expression, leaving the rest unevaluated.               *)
(*  - Progressing rules: mirror the big-step rules, but with bigstop  *)
(*    in the premises and explicit [is_value] premises where big-step  *)
(*    previously got them for free.                                    *)
(*                                                                     *)
(*  Key theorem (Stop/Multi Equivalence, Thm 7 of the paper):         *)
(*    bigstop e e'  iff  e -->* e'                                     *)
(* ------------------------------------------------------------------ *)

Inductive bigstop : tm -> tm -> Prop :=

(** -- Stopping rules (St-Stop schema, expanded) -------------------- *)

(** St-Stop (k=0): any expression can stop at itself. *)
| BS_Stop : forall e,
    bigstop e e

(** St-Succ (k=1): stop inside the argument of succ. *)
| BS_Succ : forall e e',
    bigstop e e' ->
    bigstop (tsucc e) (tsucc e')

(** St-Pred (k=1): stop inside the argument of pred. *)
| BS_Pred : forall e e',
    bigstop e e' ->
    bigstop (tpred e) (tpred e')

(** St-IfzDisc (k=1): stop inside the discriminant of ifz. *)
| BS_IfzDisc : forall e e' t1 t2,
    bigstop e e' ->
    bigstop (tifz e t1 t2) (tifz e' t1 t2)

(** St-App1 (k=1): stop inside the operator of an application. *)
| BS_App1 : forall t1 t1' t2,
    bigstop t1 t1' ->
    bigstop (tapp t1 t2) (tapp t1' t2)

(** St-App2 (k=2): operator has reached a value; stop inside the operand. *)
| BS_App2 : forall t1 v1 t2 t2',
    bigstop t1 v1 /\ is_value v1 /\ bigstop t2 t2' ->
    bigstop (tapp t1 t2) (tapp v1 t2')

(** -- Progressing rules (St-CaseZ / St-CaseS / St-App analogues) --- *)

(** St-PredZero: discriminant big-stops to zero. *)
| BS_PredZero : forall e,
    bigstop e tzero ->
    bigstop (tpred e) tzero

(** St-PredSucc: discriminant big-stops to succ v (v a value). *)
| BS_PredSucc : forall e v,
    bigstop e (tsucc v) /\ is_value v ->
    bigstop (tpred e) v

(** St-IfzZero: discriminant big-stops to zero; then big-stop the zero branch. *)
| BS_IfzZero : forall e t1 t1' t2,
    bigstop e tzero /\ bigstop t1 t1' ->
    bigstop (tifz e t1 t2) t1'

(** St-IfzSucc: discriminant big-stops to succ vn; big-stop the succ branch.
    (vn is the predecessor; our ifz has no binding for it in the succ branch.) *)
| BS_IfzSucc : forall e vn t1 t2 t2',
    bigstop e (tsucc vn) /\ is_value vn /\ bigstop t2 t2' ->
    bigstop (tifz e t1 t2) t2'

(** St-App: operator big-stops to a lambda, operand to a value, body big-stopped. *)
| BS_App : forall t1 x T t3 t2 v2 e',
    bigstop t1 (tabs x T t3) /\ bigstop t2 v2 /\ is_value v2 /\
    bigstop (subst x v2 t3) e' ->
    bigstop (tapp t1 t2) e'

(** St-Fix: unroll the fixpoint once, then big-stop the substituted body. *)
| BS_Fix : forall f T t e',
    bigstop (subst f (tfix f T t) t) e' ->
    bigstop (tfix f T t) e'.

End PCFBigStep.
