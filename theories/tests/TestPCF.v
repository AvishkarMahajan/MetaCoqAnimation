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
Require Import Animation.coIndLambdaRet.
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

MetaRocq Run (animate_coinductive_with_fn_pos <?eval?> [("eval", ([0], [1]))] 500).

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
  evalTransparentSigma2AnimatedTopFn 50 (Success tm tzero)
  = fun evalAn1 : tm -> tm => Success tm tzero.
Proof. reflexivity. Qed.

(** numerals are values *)
Example test_eval_numeral :
  evalTransparentSigma2AnimatedTopFn 50 (Success tm (num 3))
  = fun evalAn1 : tm -> tm => Success tm (num 3).
Proof. reflexivity. Qed.


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

Inductive is_value : tm -> Prop :=
| V_Lam  : forall x T t,  is_value (tabs x T t)
| V_Zero :                 is_value tzero
| V_Succ : forall v,       is_value v -> is_value (tsucc v).
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

(* ------------------------------------------------------------------ *)
(** ** CBV Small-Step Reduction                                        *)
(* ------------------------------------------------------------------ *)

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall x T t v2,
    is_value v2 ->
    step (tapp (tabs x T t) v2) (subst x v2 t)
| ST_App1 : forall t1 t1' t2,
    step t1 t1' ->
    step (tapp t1 t2) (tapp t1' t2)
| ST_App2 : forall v1 t2 t2',
    is_value v1 ->
    step t2 t2' ->
    step (tapp v1 t2) (tapp v1 t2')
| ST_Succ : forall t t',
    step t t' ->
    step (tsucc t) (tsucc t')
| ST_PredZero :
    step (tpred tzero) tzero
| ST_PredSucc : forall v,
    is_value v ->
    step (tpred (tsucc v)) v
| ST_Pred : forall t t',
    step t t' ->
    step (tpred t) (tpred t')
| ST_IfzZero : forall t1 t2,
    step (tifz tzero t1 t2) t1
| ST_IfzSucc : forall vn t1 t2,
    is_value vn ->
    step (tifz (tsucc vn) t1 t2) t2
| ST_IfzDisc : forall t t' t1 t2,
    step t t' ->
    step (tifz t t1 t2) (tifz t' t1 t2)
| ST_Fix : forall f T t,
    step (tfix f T t) (subst f (tfix f T t) t).

Inductive stepRTC : tm -> tm -> Prop :=
| RTC_refl : forall t,
    stepRTC t t
| RTC_step : forall t t' t'',
    step t t' ->
    stepRTC t' t'' ->
    stepRTC t t''.



(** Key completeness auxiliary: if [stepRTC inputTm middleTm] holds,
    [step middleTm outputTm] takes one more small step, and the animation
    at fuel [n] already yields [middleTm], then there exists [k <= 3]
    such that the animation at fuel [n + k] yields [outputTm].
    The bound [3] reflects the worst-case PCF constructor ([ST_AppAbs],
    which nests evaluation of operator, argument, and body). *)
Lemma animate_step_shift : forall (inputTm middleTm outputTm : tm) (n : nat),
  stepRTC inputTm middleTm ->
  step middleTm outputTm ->
  (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm middleTm ->
  exists (k : nat), 1 <= k <= 3 /\
    (evalTransparentSigma2AnimatedTopFn (n + k) (Success tm inputTm)) (fun t' : tm => t') = Success tm outputTm.
Proof.
Admitted.

(** --- Main correspondence theorems --------------------------------------- *)

(** Soundness: the animation only produces terms reachable from the input
    by zero or more CBV small steps.
    Proof sketch: by induction on [n]; base case is [animate_zero] +
    [RTC_refl]; inductive step uses [animate_step_shift] or
    [bigstop_iff_stepRTC] composed with [correspondence_soundness_bigstop]. *)
Theorem correspondence_soundness : forall (n : nat) (inputTm outputTm : tm),
  (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm outputTm ->
  stepRTC inputTm outputTm.
Proof.
Admitted.

(** Completeness: every term reachable from the input by finitely many
    CBV small steps can be produced by the animation at some fuel level.
    Proof sketch: induction on [stepRTC inputTm outputTm].
    - [RTC_refl]: [n = 0] by [animate_zero].
    - [RTC_step] ([step* inputTm middleTm] then [step middleTm outputTm]):
      IH gives fuel [n] with [animate n inputTm id = Success middleTm];
      [animate_step_shift] yields [k <= 3] and fuel [n + k] for [outputTm]. *)
Theorem correspondence_completeness : forall (inputTm outputTm : tm),
  stepRTC inputTm outputTm ->
  exists (n : nat),
    (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm outputTm.
Proof.
Admitted.


(* Connect to bigStop via Thm7 of paper *)

(** Theorem 7 of Kahn, Hoffmann, Li (POPL 2026): bigstop coincides with
    the reflexive-transitive closure of the CBV small-step relation. *)
Theorem bigstop_iff_stepRTC : forall e e',
  bigstop e e' <-> stepRTC e e'.
Proof.
Admitted.
Lemma correspondence_soundness_bigstop : forall (n : nat) (inputTm outputTm : tm),
  (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm outputTm ->
  bigstop inputTm outputTm.
Proof.
Admitted.

Lemma correspondence_completeness_bigstop : forall (inputTm outputTm : tm),
  bigstop inputTm outputTm ->
  exists (n : nat),
    (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm outputTm.
Proof.
Admitted.




(*    

(** The purely progressing fragment of [bigstop]: the six constructors that
    advance the computation.  Sub-derivations still use full [bigstop] (stops
    are allowed inside), but the top-level step must be a progressing rule.
    Stopping/congruence rules ([BS_Stop], [BS_Succ], [BS_Pred], [BS_App1],
    [BS_App2], [BS_IfzDisc]) are excluded. *)
Inductive bigstop_prog_step : tm -> tm -> Prop :=
| BSP_PredZero : forall e,
    bigstop e tzero ->
    bigstop_prog_step (tpred e) tzero
| BSP_PredSucc : forall e v,
    bigstop e (tsucc v) /\ is_value v ->
    bigstop_prog_step (tpred e) v
| BSP_IfzZero  : forall e t1 t1' t2,
    bigstop e tzero /\ bigstop t1 t1' ->
    bigstop_prog_step (tifz e t1 t2) t1'
| BSP_IfzSucc  : forall e vn t1 t2 t2',
    bigstop e (tsucc vn) /\ is_value vn /\ bigstop t2 t2' ->
    bigstop_prog_step (tifz e t1 t2) t2'
| BSP_App      : forall t1 x T t3 t2 v2 e',
    bigstop t1 (tabs x T t3) /\ bigstop t2 v2 /\ is_value v2 /\
    bigstop (subst x v2 t3) e' ->
    bigstop_prog_step (tapp t1 t2) e'
| BSP_Fix      : forall f T t e',
    bigstop (subst f (tfix f T t) t) e' ->
    bigstop_prog_step (tfix f T t) e'.

(** --- Auxiliary lemmas ---------------------------------------------------- *)

(** At fuel 0 the animation falls back to the identity oracle and returns the
    input unchanged. *)
Lemma animate_zero : forall (inputTm : tm),
  (evalTransparentSigma2AnimatedTopFn 0 (Success tm inputTm)) (fun t' : tm => t') = Success tm inputTm.
Proof.
Admitted.

(** More fuel evaluates further via a progressing step: if [outputN] is not
    already a value, and the animation at fuel [n] returns [outputN] and at
    fuel [m >= n] returns [outputM], then [bigstop_prog_step outputN outputM].
    The [~ is_value outputN] guard is necessary: values are fixed points of the
    animation, so increasing fuel on a value leaves [outputM = outputN] with no
    progressing step available.
    Used for soundness: applying from [n=0] (via [animate_zero]) yields a chain
    of [bigstop_prog_step]s from [inputTm] to [outputTm]. *)
Lemma animate_mono_bigstop : forall (n m : nat) (inputTm outputN outputM : tm),
  n <= m ->
  
  (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm outputN ->
  (evalTransparentSigma2AnimatedTopFn m (Success tm inputTm)) (fun t' : tm => t') = Success tm outputM ->
  bigstop outputN outputM.
Proof.
Admitted.

(** One progressing bigstop step corresponds to a bounded fuel increment.
    If the animation at exact fuel [n] gives [outputN], then there exists
    [k] in [[1, C]] such that at fuel [n + k] it gives [outputM] where
    [bigstop_prog_step outputN outputM].
    [C] is a small constant determined by the worst-case eval constructor
    (for PCF, at most the cost of [E_App] with three sub-evaluations). *)
Lemma animate_one_bigstop_step : forall (C n : nat) (inputTm outputN : tm),
   ~ is_value outputN -> (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm outputN ->
  exists (k : nat) (outputM : tm),
    1 <= k <= C /\
    (evalTransparentSigma2AnimatedTopFn (n + k) (Success tm inputTm)) (fun t' : tm => t') = Success tm outputM /\
    bigstop_prog_step outputN outputM.
Proof.
Admitted.

(** Every progressing step is also a [bigstop] step.  Bridges the chain of
    [bigstop_prog_step]s produced by [animate_mono_bigstop] into the full
    [bigstop] relation needed for soundness. *)
Lemma bigstop_prog_step_to_bigstop : forall (e e' : tm),
  bigstop_prog_step e e' ->
  bigstop e e'.
Proof.
  intros e e' H. destruct H.
  - apply BS_PredZero. assumption.
  - apply BS_PredSucc. assumption.
  - apply BS_IfzZero. assumption.
  - eapply BS_IfzSucc. eassumption.
  - eapply BS_App. eassumption.
  - apply BS_Fix. assumption.
Qed.
*)
(** --- Correspondence via bigstop (intermediate) --------------------------- *)




End PCFBigStep.













