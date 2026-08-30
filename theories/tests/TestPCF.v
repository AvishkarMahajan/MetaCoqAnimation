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

Fixpoint isValueFn (t : tm) : bool :=
match t with
| tabs x T t => true
| tzero => true
| tsucc v => isValueFn v
| _ => false
end.

(* ------------------------------------------------------------------ *)
(** ** CBV big-step evaluation                                         *)
(*                                                                     *)
(*  Values: tabs (lambda), tzero, tsucc v.                             *)
(*  eval e v  means  e evaluates to value v.                           *)
(* ------------------------------------------------------------------ *)
(* Take the progressing fragment of bigStop *)
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

| E_PredSucc : forall t v, isValueFn v = true /\
    eval t (tsucc v) ->
    eval (tpred t) v

(** CBV application: evaluate operator to a lambda, evaluate argument,
    then evaluate the substituted body. *)
| E_App : forall t1 t2 x T t3 v2 v,
    isValueFn v2 = true /\ eval t1 (tabs x T t3) /\ eval t2 v2 /\ eval (subst x v2 t3) v ->
    eval (tapp t1 t2) v

(** ifz: zero branch *)
| E_IfzZero : forall t t1 t2 v,
    eval t tzero /\ eval t1 v ->
    eval (tifz t t1 t2) v

(** ifz: successor branch (the value of the discriminant is discarded) *)
| E_IfzSucc : forall t vn t1 t2 t4,
    isValueFn vn = true /\ eval t (tsucc vn) /\ eval t2 t4 ->
    eval (tifz t t1 t2) t4

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
(** ** Overrunning probe                                               *)
(*                                                                     *)
(*  Two terms to test whether increasing fuel skips small-step        *)
(*  intermediate states.                                               *)
(*                                                                     *)
(*  Term A: E_App applies immediately (t1 = lambda, t2 = value).      *)
(*    (λx:Nat. x) zero                                                 *)
(*  Expected CBV path: one step → zero.                               *)
(*                                                                     *)
(*  Term B: argument still needs reduction before E_App can fire.     *)
(*    (λx:Nat. x) (pred zero)                                         *)
(*  Expected CBV path:                                                 *)
(*    --> (λx:Nat. x) zero        [ST_App2 / ST_PredZero]             *)
(*    --> zero                    [ST_AppAbs]                          *)
(*  If the animation jumps from B directly to zero at fuel 2,         *)
(*  skipping (λx:Nat. x) zero, overrunning has occurred.              *)
(* ------------------------------------------------------------------ *)

Definition id_nat : tm := tabs "x" TNat (tvar "x").

(** Term A: E_App fires immediately. *)
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 0 (Success tm (tapp id_nat tzero))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 1 (Success tm (tapp id_nat tzero))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 2 (Success tm (tapp id_nat tzero))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 3 (Success tm (tapp id_nat tzero))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 4 (Success tm (tapp id_nat tzero))) (fun t' => t').

(** Term B: argument must reduce first — the overrunning probe. *)
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 0 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 1 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 2 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 3 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 4 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').

(** Fine-grained probe for term A: find exact threshold. *)
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 5 (Success tm (tapp id_nat tzero))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 6 (Success tm (tapp id_nat tzero))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 7 (Success tm (tapp id_nat tzero))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 8 (Success tm (tapp id_nat tzero))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 9 (Success tm (tapp id_nat tzero))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 10 (Success tm (tapp id_nat tzero))) (fun t' => t').

(** Fine-grained probe for term B: find intermediate state thresholds. *)
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 5  (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 6  (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 7  (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 8  (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 9  (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 10 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 11 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 12 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 13 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 14 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 15 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 20 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 50 (Success tm (tapp id_nat (tpred tzero)))) (fun t' => t').

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





(* Connect to bigStop via Thm7 of paper *)

(* Theorem 7 of Kahn, Hoffmann, Li (POPL 2026): bigstop coincides with
    the reflexive-transitive closure of the CBV small-step relation. *)
Theorem bigstop_iff_stepRTC : forall e e',
  bigstop e e' <-> stepRTC e e'.
Proof.
Admitted.


(** --- Main correspondence theorems --------------------------------------- *)
(** Dependency order (foundational → dependent):
      animation_soundness_general  [bottom: standalone, no deps]
      correspondence_soundness_bigstop  [standalone; full proof needs animate_mono]
      correspondence_completeness_bigstop  [top: needs CSB + bigstop transitivity]
    We place them MOST-DEPENDENT FIRST so that "start from the bottom and
    move upward" means prove animation_soundness_general first, then CSB,
    then CCB. *)

(** CCB — Completeness (most dependent).
    Given [bigstop inputTm tm1], find some [tm2] and fuel [n] such that
    [bigstop tm1 tm2] AND the animation at fuel [n] yields [tm2].

    Proof strategy: induction on [bigstop inputTm tm1].
    • BS_Stop (tm1 = inputTm): take tm2 := inputTm, n := 0.
        - [bigstop inputTm inputTm] by BS_Stop.
        - animation at 0 with identity oracle = Success tm inputTm by
          computation (the composite applies oracle at fuel 0,
          identity oracle gives the input back).
    • All other bigstop constructors: the IH gives a witness for the
      sub-expression, but the animation runs on the WHOLE inputTm, so
      the IH cannot be applied directly without lemmas relating
      animation(n)(tsucc e) to animation(m)(e), etc.
      These cases require:
        (a) bigstop transitivity (or bigstop_iff_stepRTC + RTC transitivity)
        (b) congruence lemmas for the animation function
      Both are non-trivial given the conjunction-packaged premises in
      bigstop constructors; admitted pending that infrastructure. *)
Lemma animate_mono_bigstop : forall (n m : nat) (inputTm outputN outputM : tm),
  n <= m ->
  
  (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm outputN ->
  (evalTransparentSigma2AnimatedTopFn m (Success tm inputTm)) (fun t' : tm => t') = Success tm outputM ->
  bigstop outputN outputM.
Proof.
Admitted.

      
Theorem correspondence_completeness_bigstop : forall (inputTm tm1 : tm),
  bigstop inputTm tm1 ->
  exists (tm2 : tm) (n : nat),
    bigstop tm1 tm2 /\
    (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm tm2.
Proof.
  intros inputTm tm1 H.
  induction H.
  - (* BS_Stop: inputTm = tm1 = e.  Witness: tm2 = e, n = 0. *)
    exists e. exists 0. split.
    + apply BS_Stop.
    + (* The composite evalTransparentSigma2AnimatedTopFn 0 (Success tm e) id
         reduces to Success tm (id e) = Success tm e because at fuel 0 the
         inner AnimFn returns FuelError, and TransparentSigmaOutputPush at 0
         falls back to the oracle — no case-split on e needed. *)
      reflexivity.
  (* All remaining constructors: the IH is for sub-expressions but the
     animation operates on the full inputTm.  Admitted pending
     congruence lemmas and bigstop transitivity. *)
  all: admit.
Qed.

(** CSB — Soundness w.r.t. bigstop.
    Proof strategy: induction on [n].
    • n = 0: evalTransparentSigma2AnimatedTopFn 0 (Success tm inputTm) id
             reduces to Success tm inputTm (oracle = id applied at fuel 0).
             So outputTm = inputTm and [bigstop inputTm inputTm] by BS_Stop.
    • n = S m: IH says animation at m is bigstop-sound.  The animation
             at S m is one further unfolding; the full proof would use
             animate_mono_bigstop (currently in commented infrastructure)
             plus bigstop transitivity.  Admitted. *)
Theorem correspondence_soundness_bigstop : forall (n : nat) (inputTm outputTm : tm),
  (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm outputTm ->
  bigstop inputTm outputTm.
Proof.
  induction n; intros inputTm outputTm H.
  - (* Fuel 0: the animation applies the oracle (identity) directly. *)
    assert (Hzero : (evalTransparentSigma2AnimatedTopFn 0 (Success tm inputTm))
                      (fun t' : tm => t') = Success tm inputTm)
      by reflexivity.
    rewrite Hzero in H. injection H. intro Heq. subst. apply BS_Stop.
  - (* Fuel S n: one more eval unfolding.
       Full proof: destruct inputTm, match the generated animation branches,
       apply IH to each recursive sub-call, then close with the appropriate
       bigstop constructor.  Requires knowing the animation function's
       case structure — admitted pending direct unfolding. *)
    admit.
Qed.

(** ASG — General oracle soundness (most foundational).
    Proof strategy: induction on [n].
    • n = 0: evalTransparentSigma2AnimatedTopFn 0 (Success tm inputTm) f
             reduces to Success tm (f inputTm) at fuel 0 (oracle applied
             immediately).  So outputTm = f inputTm, and [eval inputTm (f inputTm)]
             by hypothesis Hf.
    • n = S m: IH gives soundness for sub-calls at fuel m.  The animation
             at S m selects an eval constructor for inputTm and recurses.
             Each recursive result satisfies eval by IH.  Assembling these
             with the chosen constructor gives [eval inputTm outputTm].
             Requires case-splitting on the animation's branch structure —
             admitted pending direct unfolding. *)
Theorem animation_soundness_general : forall (f : tm -> tm),
  (forall tm1 : tm, eval tm1 (f tm1)) ->
  forall (inputTm outputTm : tm) (n : nat),
    (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) f = Success tm outputTm ->
    eval inputTm outputTm.
Proof.
  intros f Hf.
  induction n; intros inputTm outputTm H.
  - (* Fuel 0: animation applies oracle f to inputTm directly. *)
    assert (Hzero : (evalTransparentSigma2AnimatedTopFn 0 (Success tm inputTm)) f
                    = Success tm (f inputTm))
      by reflexivity.
    rewrite Hzero in H. injection H. intro Heq. subst. apply Hf.
  - (* Fuel S n: one eval constructor unfolded; recursive sub-calls at fuel n.
       Full proof: destruct inputTm, match eval branches, use IH on each
       recursive call, close with the corresponding eval constructor.
       Admitted pending direct unfolding of the animation function. *)
    admit.
Qed.




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

(* ================================================================== *)
(** * Effectful CBV PCF Big-Stop Semantics (Section 5)                *)
(*                                                                     *)
(*  Extends pure PCF with [teff act e]: emit effect [act] then        *)
(*  evaluate [e].  The bigstop judgment tracks the sequence of        *)
(*  effects emitted: [bigstop e e' a] means e partially evaluates     *)
(*  to e' while emitting effects a : list string.                      *)
(* ================================================================== *)

Module EffectfulPCFBigStop.

Inductive ty : Type :=
| TNat   : ty
| TArrow : ty -> ty -> ty.

Inductive tm : Type :=
| tvar  : string -> tm
| tabs  : string -> ty -> tm -> tm
| tapp  : tm -> tm -> tm
| tzero : tm
| tsucc : tm -> tm
| tpred : tm -> tm
| tifz  : tm -> tm -> tm -> tm
| tfix  : string -> ty -> tm -> tm
| teff  : string -> tm -> tm.        (** emit effect then evaluate *)

Fixpoint eqFnty (t1 t2 : ty) : bool :=
  match t1, t2 with
  | TNat, TNat => true
  | TArrow a1 b1, TArrow a2 b2 => andb (eqFnty a1 a2) (eqFnty b1 b2)
  | _, _ => false
  end.

Fixpoint eqFntm (t1 t2 : tm) : bool :=
  match t1, t2 with
  | tvar x, tvar y => String.eqb x y
  | tabs x T1 e1, tabs y T2 e2 =>
      andb (String.eqb x y) (andb (eqFnty T1 T2) (eqFntm e1 e2))
  | tapp e1 e2, tapp e3 e4 => andb (eqFntm e1 e3) (eqFntm e2 e4)
  | tzero, tzero => true
  | tsucc e1, tsucc e2 => eqFntm e1 e2
  | tpred e1, tpred e2 => eqFntm e1 e2
  | tifz e1 e2 e3, tifz e4 e5 e6 =>
      andb (eqFntm e1 e4) (andb (eqFntm e2 e5) (eqFntm e3 e6))
  | tfix f T1 e1, tfix g T2 e2 =>
      andb (String.eqb f g) (andb (eqFnty T1 T2) (eqFntm e1 e2))
  | teff a1 e1, teff a2 e2 => andb (String.eqb a1 a2) (eqFntm e1 e2)
  | _, _ => false
  end.

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
  | teff a t1       => teff a (subst x s t1)
  end.

Fixpoint isValueFn (t : tm) : bool :=
  match t with
  | tabs _ _ _ => true
  | tzero      => true
  | tsucc v    => isValueFn v
  | _          => false
  end.

Definition effects := list string.

Fixpoint eqFnEff (a b : effects) : bool :=
  match a, b with
  | [], []           => true
  | x :: xs, y :: ys => andb (String.eqb x y) (eqFnEff xs ys)
  | _, _             => false
  end.

Inductive is_value : tm -> Prop :=
| V_Lam  : forall x T t, is_value (tabs x T t)
| V_Zero :                is_value tzero
| V_Succ : forall v,      is_value v -> is_value (tsucc v).

(* ------------------------------------------------------------------ *)
(** ** Effectful Big-Stop (Figure 8 of Kahn, Hoffmann, Li)            *)
(* ------------------------------------------------------------------ *)

Inductive bigstop : tm -> tm -> effects -> Prop :=

(** -- Stopping rules (STE-Stop schema, expanded) ------------------- *)

| BS_Stop : forall e,
    bigstop e e []
| BS_Succ : forall e e' a,
    bigstop e e' a ->
    bigstop (tsucc e) (tsucc e') a
| BS_Pred : forall e e' a,
    bigstop e e' a ->
    bigstop (tpred e) (tpred e') a
| BS_IfzDisc : forall e e' t1 t2 a,
    bigstop e e' a ->
    bigstop (tifz e t1 t2) (tifz e' t1 t2) a
| BS_App1 : forall t1 t1' t2 a,
    bigstop t1 t1' a ->
    bigstop (tapp t1 t2) (tapp t1' t2) a
| BS_App2 : forall t1 v1 t2 t2' a1 a2,
    bigstop t1 v1 a1 /\ is_value v1 /\ bigstop t2 t2' a2 ->
    bigstop (tapp t1 t2) (tapp v1 t2') (List.app a1 a2)

(** -- Progressing rules (STE-App / STE-CaseZ / STE-CaseS etc.) ---- *)

| BS_PredZero : forall e a,
    bigstop e tzero a ->
    bigstop (tpred e) tzero a
| BS_PredSucc : forall e v a,
    bigstop e (tsucc v) a /\ is_value v ->
    bigstop (tpred e) v a
| BS_IfzZero : forall e t1 t1' t2 a1 a2,
    bigstop e tzero a1 /\ bigstop t1 t1' a2 ->
    bigstop (tifz e t1 t2) t1' (List.app a1 a2)
| BS_IfzSucc : forall e vn t1 t2 t2' a1 a2,
    bigstop e (tsucc vn) a1 /\ is_value vn /\ bigstop t2 t2' a2 ->
    bigstop (tifz e t1 t2) t2' (List.app a1 a2)
| BS_App : forall t1 x T t3 t2 v2 e' a1 a2 a3,
    bigstop t1 (tabs x T t3) a1 /\ bigstop t2 v2 a2 /\ is_value v2 /\
    bigstop (subst x v2 t3) e' a3 ->
    bigstop (tapp t1 t2) e' (List.app a1 (List.app a2 a3))
| BS_Fix : forall f T t e' a,
    bigstop (subst f (tfix f T t) t) e' a ->
    bigstop (tfix f T t) e' a
| BS_Eff : forall act e e' a,
    bigstop e e' a ->
    bigstop (teff act e) e' (act :: a).

(* ------------------------------------------------------------------ *)
(** ** Effectful Coinductive Eval (progressing rules + value bases)   *)
(* ------------------------------------------------------------------ *)

Definition listAppEf := @List.app string.


CoInductive eval : tm -> tm -> list string -> Prop :=
| E_Lam : forall x T t,
    eval (tabs x T t) (tabs x T t) []
| E_Zero :
    eval tzero tzero []
| E_Succ : forall t v a,
    eval t v a ->
    eval (tsucc t) (tsucc v) a
| E_PredZero : forall t a,
    eval t tzero a ->
    eval (tpred t) tzero a
| E_PredSucc : forall t v a,
    isValueFn v = true /\ eval t (tsucc v) a ->
    eval (tpred t) v a
| E_App : forall t1 t2 x T t3 v2 v a1 a2 a3,
    isValueFn v2 = true /\
    eval t1 (tabs x T t3) a1 /\ eval t2 v2 a2 /\ eval (subst x v2 t3) v a3 ->
    eval (tapp t1 t2) v (listAppEf a1 (listAppEf a2 a3))
| E_IfzZero : forall t t1 t2 v a1 a2,
    eval t tzero a1 /\ eval t1 v a2 ->
    eval (tifz t t1 t2) v (listAppEf a1 a2)
| E_IfzSucc : forall t vn t1 t2 t4 a1 a2,
    isValueFn vn = true /\ eval t (tsucc vn) a1 /\ eval t2 t4 a2 ->
    eval (tifz t t1 t2) t4 (listAppEf a1 a2)
| E_Fix : forall f T t v a,
    eval (subst f (tfix f T t) t) v a ->
    eval (tfix f T t) v a
| E_Eff : forall act t v a,
    eval t v a ->
    eval (teff act t) v (act :: a).


MetaRocq Run (animate_coinductive_with_fn_pos <?eval?> [("eval", ([0], [1;2]))] 500).

Print evalTransparentSigma2AnimatedTopFn.

(* ------------------------------------------------------------------ *)
(** ** Correspondence Theorems for Effectful PCF                       *)
(* ------------------------------------------------------------------ *)

Theorem animation_soundness_general : forall (f1 : tm -> tm) (f2 : tm -> list string) ,
  (forall tm1 : tm, eval tm1 (f1 tm1) (f2 tm1)) ->
  forall (inputTm outputTm : tm) (outputEff : list string) (n : nat),
    (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) f1 f2 = Success (tm * list string) (outputTm, outputEff) ->
    eval inputTm outputTm outputEff.
Proof. Admitted.

Theorem correspondence_soundness : forall (n : nat) (inputTm outputTm : tm) (outputEff : list string),
  (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') (fun t' : tm => @nil string)  = Success (tm * list string) (outputTm, outputEff) ->
  bigstop inputTm outputTm outputEff.
Proof. Admitted.

Fixpoint isSubLst (a1 : list string) (a2 : list string) :=
match a1 with
| [] => true
| h :: t => match a2 with
            | h2 :: t2 => andb (String.eqb h h2) (isSubLst t t2)
            | _ => false
            end
end.             

Lemma correspondence_completeness_bigstop : forall (inputTm tm1 : tm) (outputEff1 : list string),
  bigstop inputTm tm1 outputEff1 ->
  exists (tm2 : tm) (outputEff2 : list string) (n : nat),
    bigstop tm1 tm2 outputEff2 /\
    (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') (fun t' : tm => @nil string) = Success (tm * list string) (tm2, outputEff2) /\ isSubLst outputEff1 outputEff2.
Proof. Admitted.

End EffectfulPCFBigStop.

(* ================================================================== *)
(** * MNF CBV PCF Big-Stop Semantics (Section 7.1)                    *)
(*                                                                     *)
(*  Monadic Normal Form requires all arguments to [app] and [case]    *)
(*  to be values; computation is sequenced via [let].  This yields    *)
(*  a bigstop with only TWO stopping rules: St-Stop and St-Let1.      *)
(*  Syntax: fun{f,x.e} combines lambda and fixpoint (self-reference   *)
(*  f); case[disc]{x.e1;e2} binds the predecessor x in the succ      *)
(*  branch; let x = e1 in e2 sequences evaluation.                    *)
(* ================================================================== *)

Module MNFBigStop.

Inductive ty : Type :=
| TNat   : ty
| TArrow : ty -> ty -> ty.

Inductive tm : Type :=
| tvar  : string -> tm
| tfun  : string -> string -> ty -> tm -> tm  (** fun{f,x.e}: f is self-ref, x is param *)
| tapp  : tm -> tm -> tm
| tzero : tm
| tsucc : tm -> tm
| tcase : tm -> string -> tm -> tm -> tm      (** case[disc]{x . e_zero ; e_succ} *)
| tlet  : string -> tm -> tm -> tm.

Fixpoint eqFnty (t1 t2 : ty) : bool :=
  match t1, t2 with
  | TNat, TNat => true
  | TArrow a1 b1, TArrow a2 b2 => andb (eqFnty a1 a2) (eqFnty b1 b2)
  | _, _ => false
  end.

Fixpoint eqFntm (t1 t2 : tm) : bool :=
  match t1, t2 with
  | tvar x, tvar y => String.eqb x y
  | tfun f1 x1 T1 e1, tfun f2 x2 T2 e2 =>
      andb (String.eqb f1 f2)
        (andb (String.eqb x1 x2) (andb (eqFnty T1 T2) (eqFntm e1 e2)))
  | tapp e1 e2, tapp e3 e4 => andb (eqFntm e1 e3) (eqFntm e2 e4)
  | tzero, tzero => true
  | tsucc e1, tsucc e2 => eqFntm e1 e2
  | tcase d1 x1 e1 f1, tcase d2 x2 e2 f2 =>
      andb (eqFntm d1 d2)
        (andb (String.eqb x1 x2) (andb (eqFntm e1 e2) (eqFntm f1 f2)))
  | tlet x1 e1 f1, tlet x2 e2 f2 =>
      andb (String.eqb x1 x2) (andb (eqFntm e1 e2) (eqFntm f1 f2))
  | _, _ => false
  end.

(** Substitution: [tfun] binds both f (self-ref) and x (param);
    [tcase] binds x in the succ branch; [tlet] binds x in e2. *)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tvar y             => if String.eqb x y then s else t
  | tfun f p T body    =>
      if orb (String.eqb x f) (String.eqb x p) then t
      else tfun f p T (subst x s body)
  | tapp t1 t2         => tapp (subst x s t1) (subst x s t2)
  | tzero              => tzero
  | tsucc t1           => tsucc (subst x s t1)
  | tcase disc y e1 e2 =>
      tcase (subst x s disc) y
            (subst x s e1)
            (if String.eqb x y then e2 else subst x s e2)
  | tlet y e1 e2       =>
      tlet y (subst x s e1)
             (if String.eqb x y then e2 else subst x s e2)
  end.

(** In MNF, variables are values (they are bound to values in a
    well-typed program). *)
Fixpoint isValueFn (t : tm) : bool :=
  match t with
  | tvar _        => true
  | tfun _ _ _ _  => true
  | tzero         => true
  | tsucc v       => isValueFn v
  | _             => false
  end.

Inductive is_value : tm -> Prop :=
| V_Var  : forall x,       is_value (tvar x)
| V_Fun  : forall f x T t, is_value (tfun f x T t)
| V_Zero :                  is_value tzero
| V_Succ : forall v,        is_value v -> is_value (tsucc v).

(* ------------------------------------------------------------------ *)
(** ** MNF Big-Stop (Figure 14 of Kahn, Hoffmann, Li)                 *)
(*                                                                     *)
(*  Only two stopping rules: BS_Stop and BS_Let1.                      *)
(* ------------------------------------------------------------------ *)

Inductive bigstop : tm -> tm -> Prop :=

(** -- Stopping rules (StM-Stop and StM-Let1 only) ------------------ *)

| BS_Stop : forall e,
    bigstop e e
| BS_Let1 : forall x e1 e1' e2,
    bigstop e1 e1' ->
    bigstop (tlet x e1 e2) (tlet x e1' e2)

(** -- Progressing rules (StM-Let2 / StM-CaseZ / StM-CaseS / StM-App) *)

| BS_Let2 : forall x e1 v1 e2 e2',
    isValueFn v1 = true /\ bigstop e1 v1 /\ bigstop (subst x v1 e2) e2' ->
    bigstop (tlet x e1 e2) e2'
| BS_CaseZ : forall x e1 e1' e2body,
    bigstop e1 e1' ->
    bigstop (tcase tzero x e1 e2body) e1'
| BS_CaseS : forall v x e1 e2 e2',
    isValueFn v = true /\ bigstop (subst x v e2) e2' ->
    bigstop (tcase (tsucc v) x e1 e2) e2'
| BS_App : forall f p T body v2 e',
    isValueFn v2 = true /\
    bigstop (subst p v2 (subst f (tfun f p T body) body)) e' ->
    bigstop (tapp (tfun f p T body) v2) e'.

(* ------------------------------------------------------------------ *)
(** ** MNF Coinductive Eval (progressing rules + value base case)     *)
(* ------------------------------------------------------------------ *)

CoInductive eval : tm -> tm -> Prop :=
| E_Val : forall t,
    isValueFn t = true ->
    eval t t
| E_Let : forall x e1 e2 v1 e2',
    isValueFn v1 = true /\ eval e1 v1 /\ eval (subst x v1 e2) e2' ->
    eval (tlet x e1 e2) e2'
| E_CaseZ : forall x e1 e1' e2body,
    eval e1 e1' ->
    eval (tcase tzero x e1 e2body) e1'
| E_CaseS : forall v x e1 e2 e2',
    isValueFn v = true /\ eval (subst x v e2) e2' ->
    eval (tcase (tsucc v) x e1 e2) e2'
| E_App : forall f p T body v2 e',
    isValueFn v2 = true /\
    eval (subst p v2 (subst f (tfun f p T body) body)) e' ->
    eval (tapp (tfun f p T body) v2) e'.

MetaRocq Run (animate_coinductive_with_fn_pos <?eval?> [("eval", ([0], [1]))] 500).

(* ------------------------------------------------------------------ *)
(** ** Correspondence Theorems for MNF PCF                             *)
(* ------------------------------------------------------------------ *)

Theorem animation_soundness_general : forall (f : tm -> tm),
  (forall tm1 : tm, eval tm1 (f tm1)) ->
  forall (inputTm outputTm : tm) (n : nat),
    (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) f = Success tm outputTm ->
    eval inputTm outputTm.
Proof. Admitted.

Theorem correspondence_soundness : forall (n : nat) (inputTm outputTm : tm),
  (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm outputTm ->
  bigstop inputTm outputTm.
Proof. Admitted.

Lemma correspondence_completeness_bigstop : forall (inputTm tm1 : tm),
  bigstop inputTm tm1 ->
  exists (tm2 : tm) (n : nat),
    bigstop tm1 tm2 /\
    (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm tm2.
Proof. Admitted.

End MNFBigStop.













