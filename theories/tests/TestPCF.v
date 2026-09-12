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
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
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

| E_PredSucc : forall t v,
    isValueFn v = true /\ eval t (tsucc v) ->
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
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 0 (Success tm (tapp id_nat tzero))) .
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 1 (Success tm (tapp id_nat tzero))).
Eval vm_compute in (evalTransparentSigma2AnimatedTopFn 3 (Success tm (tapp id_nat tzero))).
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

(** Helper: isValueFn b = true implies is_value. *)
Lemma isValueFn_to_is_value : forall v, isValueFn v = true -> is_value v.
Proof.
  induction v; simpl; intros H; try discriminate.
  - apply V_Lam.
  - apply V_Zero.
  - apply V_Succ. apply IHv. exact H.
Qed.

(** Round-trip identity: lifting a [tm] to [tm'] then projecting back (without
    hitting any oracle-marked nodes) recovers the original term.  The proof is
    a straightforward structural induction: [tmLift] and [tmTransparentSigmaPushBody]
    are defined by mutual case analysis on the same constructors. *)
Lemma tmTransparentSigmaPushBody_tmLift : forall (f : tm -> tm) (t : tm),
  tmTransparentSigmaPushBody f (tmLift t) = t.
Proof.
  intros f t. induction t; simpl.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1. rewrite IHt2. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1. rewrite IHt2. rewrite IHt3. reflexivity.
  - rewrite IHt. reflexivity.
Qed.

(** At fuel 0 the animated function wraps the lifted input in [evalremoveFnPosAn1]
    (the oracle marker), and [tmTransparentSigmaPushBody] converts that marker
    back via the oracle [f].  The identity [tmTransparentSigmaPushBody_tmLift]
    then simplifies [f (push (lift inputTm))] to [f inputTm]. *)
Lemma anim_0_oracle : forall (f : tm -> tm) (inputTm : tm),
  evalTransparentSigma2AnimatedTopFn 0 (Success tm inputTm) f = Success tm (f inputTm).
Proof.
  intros f inputTm.
  unfold evalTransparentSigma2AnimatedTopFn. cbn.
  rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
Qed.

(** At fuel 1 the inner dispatch also runs at oracle-level (dispatch fuel 0),
    so for the identity oracle (fun t' => t'), any input returns itself.
    The inner dispatch for a tabs input at fuel 1 fires E_Lam (not the oracle
    wrapper), but the push still yields [tabs x T t] = [id (tabs x T t)].
    This specialised form is used in correspondence_soundness_bigstop. *)
Lemma anim_1_oracle_f : forall (inputTm : tm) (f : tm -> tm),
  evalTransparentSigma2AnimatedTopFn 1 (Success tm inputTm) f =
  Success tm (f inputTm).
Proof.
  intros inputTm f.
  unfold evalTransparentSigma2AnimatedTopFn. cbn.
  rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
Qed.

Lemma anim_1_oracle_id : forall (inputTm : tm),
  evalTransparentSigma2AnimatedTopFn 1 (Success tm inputTm) (fun t' => t') =
  Success tm inputTm.
Proof.
  intro inputTm. rewrite anim_1_oracle_f. reflexivity.
Qed.

(** Below-threshold oracle lemmas.  For each constructor C with handler
    threshold T, the oracle fires (returning [f (C args)]) for any outer
    fuel [n < T].  Proof: case-split on [n]; each concrete case reduces by
    [cbn] through [dispatch_coind_ext] until fuel reaches 0 and the oracle
    fires, then [rewrite tmTransparentSigmaPushBody_tmLift] recovers [f t]. *)

Lemma anim_below_thr_tzero : forall n f,
  n <= 2 ->
  evalTransparentSigma2AnimatedTopFn n (Success tm tzero) f = Success tm (f tzero).
Proof.
  intros n f Hn.
  destruct n as [|[|[| n']]].
  - apply anim_0_oracle.
  - apply anim_1_oracle_f.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
(*    rewrite tmTransparentSigmaPushBody_tmLift.*) reflexivity.
  - lia.
Qed.

Lemma anim_below_thr_tsucc : forall n t f,
  n <= 3 ->
  evalTransparentSigma2AnimatedTopFn n (Success tm (tsucc t)) f = Success tm (f (tsucc t)).
Proof.
  intros n t f Hn.
  destruct n as [|[|[|[| n']]]].
  - apply anim_0_oracle.
  - apply anim_1_oracle_f.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - lia.
Qed.

Lemma anim_below_thr_tpred : forall n t f,
  n <= 5 ->
  evalTransparentSigma2AnimatedTopFn n (Success tm (tpred t)) f = Success tm (f (tpred t)).
Proof.
  intros n t f Hn.
  destruct n as [|[|[|[|[|[| n']]]]]].
  - apply anim_0_oracle.
  - apply anim_1_oracle_f.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - lia.
Qed.

Lemma anim_below_thr_tapp : forall n t1 t2 f,
  n <= 6 ->
  evalTransparentSigma2AnimatedTopFn n (Success tm (tapp t1 t2)) f = Success tm (f (tapp t1 t2)).
Proof.
  intros n t1 t2 f Hn.
  destruct n as [|[|[|[|[|[|[| n']]]]]]].
  - apply anim_0_oracle.
  - apply anim_1_oracle_f.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - lia.
Qed.

Lemma anim_below_thr_tifz : forall n t t1 t2 f,
  n <= 8 ->
  evalTransparentSigma2AnimatedTopFn n (Success tm (tifz t t1 t2)) f = Success tm (f (tifz t t1 t2)).
Proof.
  intros n t t1 t2 f Hn.
  destruct n as [|[|[|[|[|[|[|[|[| n']]]]]]]]].
  - apply anim_0_oracle.
  - apply anim_1_oracle_f.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - lia.
Qed.

Lemma anim_below_thr_tfix : forall n fn T t f,
  n <= 9 ->
  evalTransparentSigma2AnimatedTopFn n (Success tm (tfix fn T t)) f = Success tm (f (tfix fn T t)).
Proof.
  intros n fn T t f Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[| n']]]]]]]]]].
  - apply anim_0_oracle.
  - apply anim_1_oracle_f.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - unfold evalTransparentSigma2AnimatedTopFn. cbn.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity.
  - lia.
Qed.

(** Helper lemmas: reduction of the animation at S n for each tm constructor.
    After unfolding the composite (inputLift; animatedFn; outputPush), [cbn]
    reduces through the concrete tm' constructor produced by [tmLift], and
    [tmTransparentSigmaPushBody_tmLift] closes any residual sub-term push. *)

(** Dispatch helper lemmas.  The animation handler list is tried in order:
    E_Lam (0), E_Zero (1), E_Succ (2), …  Each handler that does NOT match the
    input constructor returns [NoMatch] and the dispatch recurses with one less
    fuel unit.  For a handler at list-index [i] to fire with abstract [n], the
    dispatch fuel must carry at least [i+1] concrete [S] constructors.  We prove
    these helpers by firing [cbn [dispatch_coind_ext]] once per skipped handler. *)

(** [E_Zero] is at index 1.  The tail list starting at [E_Zero] has it as its
    first element, so any fuel [S n] suffices. *)

(** [E_Succ] is at index 2.  After [E_Lam] and [E_Zero] have returned [NoMatch],
    the sub-list starting at [E_Succ] has it as its first element.  At fuel
    [S (S n)], [E_Succ] fires for [tsucc'] inputs; the handler makes a recursive
    call — CRUCIALLY at the SAME fuel [S n] it itself received, not at [n].
    (The generated handler body never peels a further [S] off its own fuel
    before recursing; the "one less fuel per step" behaviour only emerges when
    the callee happens to be [evalremoveFnPos'AnimatedTopFn] itself, since
    THAT function decrements its own fuel at its own top-level match. For an
    arbitrary [evalFn] — as this lemma is stated — there is no such decrement.
    An earlier version of this lemma claimed the recursive call happens at
    [n]; that is false in general, witnessed concretely by an [evalFn] whose
    result depends on the exact fuel value it receives.)

    The generated E_Succ handler body uses compose_outcome / join_pair /
    dispatch_clauses combinators that cbn [E_Succ] will not reduce when evalFn
    is abstract (cbn's lazy strategy refuses to delta-unfold a constant whose
    result would be stuck).  We therefore prove a SPEC LEMMA [E_Succ_result]
    first: it characterises the handler's concrete input/fuel reductions while
    leaving the abstract evalFn call unexpanded.  Proof: unfold the handler and
    all the combinators it's built from by name (compose_outcome,
    option_to_result, join_pair, with_default, dispatch_clauses,
    fuel_error_fn) — plain [simpl]/[cbn] refuse to see through these on their
    own — then [simpl] to fire every structural match on the concrete
    input/fuel, leaving [evalFn (S n) (Success tm' v)] as a literal residual
    scrutinee; destructing it and closing each case by [reflexivity] finishes
    it. All dispatch helpers then use [rewrite E_Succ_result] instead of
    trying to reduce the complex combinator body inline. *)

Lemma E_Succ_result :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n v,
  E_SuccremoveFnPos'Animated evalFn (S n) (Success tm' (tsucc' v)) =
  match evalFn (S n) (Success tm' v) with
  | FuelError  => FuelError  tm'
  | Success w  => Success tm' (tsucc' w)
  | NoMatch    => NoMatch    tm'
  end.
Proof.
  intros evalFn n v.
  unfold E_SuccremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn.
  simpl.
  destruct (evalFn (S n) (Success tm' v)); simpl; reflexivity.
Qed.

Lemma dispatch_tsucc_from_succ_gen :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n t,
  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
    [E_SuccremoveFnPos'Animated evalFn;
     E_PredZeroremoveFnPos'Animated evalFn;
     E_PredSuccremoveFnPos'Animated evalFn;
     E_AppremoveFnPos'Animated evalFn;
     E_IfzZeroremoveFnPos'Animated evalFn;
     E_IfzSuccremoveFnPos'Animated evalFn;
     E_FixremoveFnPos'Animated evalFn;
     evalremoveFnPos'UndefinedAnimated]
    (S n) (Success tm' (tsucc' (tmLift t))) =
  match evalFn (S n) (Success tm' (tmLift t)) with
  | Success v' => Success tm' (tsucc' v')
  | FuelError => Success tm' (evalremoveFnPos'Rest (tsucc' (tmLift t)))
  | NoMatch =>
      dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_PredZeroremoveFnPos'Animated evalFn;
         E_PredSuccremoveFnPos'Animated evalFn;
         E_AppremoveFnPos'Animated evalFn;
         E_IfzZeroremoveFnPos'Animated evalFn;
         E_IfzSuccremoveFnPos'Animated evalFn;
         E_FixremoveFnPos'Animated evalFn;
         evalremoveFnPos'UndefinedAnimated]
        n (Success tm' (tsucc' (tmLift t)))
  end.
Proof.
  intros evalFn n t.
  cbn [dispatch_coind_ext].
  rewrite (E_Succ_result evalFn n (tmLift t)).
  destruct (evalFn (S n) (Success tm' (tmLift t))) as [| w |]; reflexivity.
Qed.
Lemma dispatch_tsucc_from_succ : forall n t,
  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
    [E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     evalremoveFnPos'UndefinedAnimated]
    (S n) (Success tm' (tsucc' (tmLift t))) =
  match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
  | Success v' => Success tm' (tsucc' v')
  | FuelError => Success tm' (evalremoveFnPos'Rest (tsucc' (tmLift t)))
  | NoMatch =>
      dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        n (Success tm' (tsucc' (tmLift t)))
  end.
Proof.
  exact (dispatch_tsucc_from_succ_gen evalremoveFnPos'AnimatedTopFn).
Qed.



Lemma dispatch_tsucc : forall n t,
  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
    [E_LamremoveFnPos'Animated;
     E_ZeroremoveFnPos'Animated;
     E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     evalremoveFnPos'UndefinedAnimated]
    (S (S (S n))) (Success tm' (tsucc' (tmLift t))) =
  match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
  | Success v' => Success tm' (tsucc' v')
  | FuelError => Success tm' (evalremoveFnPos'Rest (tsucc' (tmLift t)))
  | NoMatch =>
      dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        n (Success tm' (tsucc' (tmLift t)))
  end.
Proof.
  intros n t.
  cbn [dispatch_coind_ext].
  assert (HE_Lam : E_LamremoveFnPos'Animated (S (S (S n))) (Success tm' (tsucc' (tmLift t))) = NoMatch tm')
    by (unfold E_LamremoveFnPos'Animated; reflexivity).
  rewrite HE_Lam.
  cbn [dispatch_coind_ext].
  assert (HE_Zero : E_ZeroremoveFnPos'Animated (S (S n)) (Success tm' (tsucc' (tmLift t))) = NoMatch tm')
    by (unfold E_ZeroremoveFnPos'Animated; reflexivity).
  rewrite HE_Zero.
  exact (dispatch_tsucc_from_succ n t).
Qed.

Lemma dispatch_tzero_from_zero : forall n,
  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
    [E_ZeroremoveFnPos'Animated;
     E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     evalremoveFnPos'UndefinedAnimated]
    (S n) (Success tm' tzero') = Success tm' tzero'.
Proof.
  intros.
  cbn [dispatch_coind_ext].
  assert (HE_Zero : E_ZeroremoveFnPos'Animated (S n) (Success tm' tzero') = Success tm' tzero')
    by (unfold E_ZeroremoveFnPos'Animated; reflexivity).
  rewrite HE_Zero. reflexivity.
Qed.

(** Full handler list starting at [E_Lam] (index 0): need [S (S n)] so that
    after E_Lam fails (returning [NoMatch]) the recursion is at [S n], which
    lets [dispatch_tzero_from_zero] close the goal. *)
Lemma dispatch_tzero : forall n,
  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
    [E_LamremoveFnPos'Animated;
     E_ZeroremoveFnPos'Animated;
     E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     evalremoveFnPos'UndefinedAnimated]
    (S (S n)) (Success tm' tzero') = Success tm' tzero'.
Proof.
  intros.
  cbn [dispatch_coind_ext].
  assert (HE_Lam : E_LamremoveFnPos'Animated (S (S n)) (Success tm' tzero') = NoMatch tm')
    by (unfold E_LamremoveFnPos'Animated; reflexivity).
  rewrite HE_Lam.
  exact (dispatch_tzero_from_zero n).
Qed.

(** Non-recursive value cases: at fuel [S (S n)] the dispatch fires its [S n]
    branch, the appropriate value handler matches, and [tmTransparentSigmaPushBody]
    reconstructs the original term.  These require [S (S n)] because at [S n]
    with [n = 0] the dispatch fires the oracle-wrap branch and returns [f t]
    rather than [t] for abstract [f].
    [anim_S_tzero] needs [S (S (S n))] because [E_Zero] is at dispatch index 1:
    after [E_Lam] fails at [S (S n)] dispatch fuel the recursion is at [S n],
    which is still concrete [S], allowing [dispatch_tzero_from_zero] to fire. *)

(** Peels one S from evalremoveFnPos'AnimatedTopFn via kernel reduction.
    Use instead of [cbn [evalremoveFnPos'AnimatedTopFn]] to avoid the latter
    also delta-reducing instances of [evalremoveFnPos'AnimatedTopFn] that
    appear inside the handler list, which would break dispatch rewrite patterns. *)

   
Lemma evalTop_stepSuccess : forall n (x : tm'),
  evalremoveFnPos'AnimatedTopFn (S n) (Success tm' x) =
  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
    [E_LamremoveFnPos'Animated;
     E_ZeroremoveFnPos'Animated;
     E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     evalremoveFnPos'UndefinedAnimated]
    n (Success tm' x).

Proof. intros. unfold evalremoveFnPos'AnimatedTopFn. 
remember n. destruct n0.
-- simpl. reflexivity.
-- remember (E_LamremoveFnPos'Animated (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext. 
rewrite <- Heqr0.
--- simpl. reflexivity.
--- simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity.
--- simpl. unfold dispatch_coind_ext. destruct n0.
---- rewrite <- Heqr0. reflexivity.
---- remember (E_ZeroremoveFnPos'Animated (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext. 
rewrite <- Heqr0.
----- simpl. reflexivity.
----- simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity.
----- unfold dispatch_coind_ext. destruct n0.
* rewrite <- Heqr0. auto.
* remember (E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext. 
rewrite <- Heqr0.
** simpl. fold evalremoveFnPos'AnimatedTopFn.  rewrite <- Heqr2. reflexivity.
** fold evalremoveFnPos'AnimatedTopFn.  rewrite <- Heqr0. rewrite <- Heqr2. reflexivity.
** fold evalremoveFnPos'AnimatedTopFn. rewrite <- Heqr2. destruct n0.
*** rewrite <- Heqr0. reflexivity.
*** remember (E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext. 
rewrite <- Heqr0.
**** simpl. auto.
**** rewrite <- Heqr0. auto.
**** fold evalremoveFnPos'AnimatedTopFn. destruct n0.
***** rewrite <- Heqr0. auto.
***** remember (E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext. 
rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
****** rewrite <- Heqr0. simpl. auto.
****** destruct n0. 
******* rewrite <- Heqr0. auto.
******* remember (E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0.
********  rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
******** rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
******** destruct n0. 
********* rewrite <- Heqr0. auto.
********* remember (E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0.
**********  rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
********** rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
********** destruct n0. 
*********** rewrite <- Heqr0. auto.
*********** remember (E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0.
************  rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
************ rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
************ destruct n0. 
************* rewrite <- Heqr0. auto.
************* remember (E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0.
**************  rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
************** rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
************** destruct n0. 
*************** rewrite <- Heqr0. auto.
*************** remember (E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0.
****************  rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
**************** rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
**************** remember (evalremoveFnPos'UndefinedAnimated (S n0) (Success tm' x)) as r0. destruct r0. 
***************** rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
***************** rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
***************** assert (H_undefined_Succ : Success tm' (evalremoveFnPosAn1 x) = evalremoveFnPos'UndefinedAnimated (S n0) (Success tm' x)).
****************** simpl. reflexivity.
****************** exfalso. rewrite <- Heqr10 in H_undefined_Succ. discriminate H_undefined_Succ. Qed.

(** Key auxiliary: the tm'-level evaluator always returns [Success tm' _] when
    given [Success tm' x] as input, for any fuel and any [x : tm'].
    At fuel 0 the oracle fires; at positive fuel every exit path leads to
    Success — a handler succeeds directly, a handler returns FuelError and the
    oracle fires, or UndefinedAnimated fires (it is FuelError only at fuel 0,
    which dispatch_coind_ext never passes to a handler; at any positive fuel
    it always returns Success).

    Proof: strong induction on fuel via [lt_wf_ind], then [evalTop_stepSuccess]
    to reach the explicit 10-handler dispatch, then the same handler-by-handler
    walk as [evalTop_stepSuccess] itself (remember each handler's call result,
    destruct into FuelError/Success/NoMatch, recurse into the tail on NoMatch).
    Unlike [evalTop_stepSuccess], the goal here is a bare existential rather
    than an equality against a hand-written RHS, so the [fold
    evalremoveFnPos'AnimatedTopFn] / handler-specific [Heqr2]-style rewrites
    that template needs to match a specific target are unnecessary — each
    branch closes via [rewrite <- Heqr0] (called BEFORE any [simpl], since
    [simpl] first can over-reduce the goal and erase the very subterm the
    rewrite needs to find) followed by [reflexivity]. UndefinedAnimated's
    FuelError and NoMatch branches are closed the same way
    [evalTop_stepSuccess] closes them: asserting the handler call equals
    [Success tm' (evalremoveFnPosAn1 x)] and deriving a contradiction via
    [discriminate]. *)
Lemma evalremoveFnPos'AnimatedTopFn_always_success :
  forall n (x : tm'),
  exists w, evalremoveFnPos'AnimatedTopFn n (Success tm' x) = Success tm' w.
Proof.
  intro n.
  apply (lt_wf_ind n (fun n => forall x,
    exists w, evalremoveFnPos'AnimatedTopFn n (Success tm' x) = Success tm' w)).
  clear n. intros n IH x.
  destruct n as [| m].
  { eexists. unfold evalremoveFnPos'AnimatedTopFn. simpl. reflexivity. }
  rewrite evalTop_stepSuccess.
  destruct m as [| n0].
  { eexists. simpl. reflexivity. }
  remember (E_LamremoveFnPos'Animated (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  { eexists. simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity. }
  simpl. unfold dispatch_coind_ext. destruct n0.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  remember (E_ZeroremoveFnPos'Animated (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  { eexists. simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity. }
  unfold dispatch_coind_ext. destruct n0.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  remember (E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  { eexists. simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity. }
  simpl. unfold dispatch_coind_ext. destruct n0.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  remember (E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  { eexists. simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity. }
  simpl. unfold dispatch_coind_ext. destruct n0.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  remember (E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  { eexists. simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity. }
  simpl. unfold dispatch_coind_ext. destruct n0.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  remember (E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  { eexists. simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity. }
  simpl. unfold dispatch_coind_ext. destruct n0.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  remember (E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  { eexists. simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity. }
  simpl. unfold dispatch_coind_ext. destruct n0.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  remember (E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  { eexists. simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity. }
  simpl. unfold dispatch_coind_ext. destruct n0.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  remember (E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  { eexists. simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity. }
  simpl. unfold dispatch_coind_ext. destruct n0.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  remember (E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (Success tm' x)) as r0. destruct r0. unfold dispatch_coind_ext.
  { eexists. rewrite <- Heqr0. simpl. reflexivity. }
  { eexists. simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity. }
  simpl. unfold dispatch_coind_ext.
  remember (evalremoveFnPos'UndefinedAnimated (S n0) (Success tm' x)) as r0. destruct r0.
  { assert (H_undefined_Succ : Success tm' (evalremoveFnPosAn1 x) = evalremoveFnPos'UndefinedAnimated (S n0) (Success tm' x)).
    { simpl. reflexivity. }
    exfalso. rewrite <- Heqr10 in H_undefined_Succ. discriminate H_undefined_Succ. }
  { eexists. rewrite <- Heqr0. reflexivity. }
  assert (H_undefined_Succ2 : Success tm' (evalremoveFnPosAn1 x) = evalremoveFnPos'UndefinedAnimated (S n0) (Success tm' x)).
  { simpl. reflexivity. }
  exfalso. rewrite <- Heqr10 in H_undefined_Succ2. discriminate H_undefined_Succ2.
Qed.

Lemma evalTop_stepNoMatch : forall n,
  evalremoveFnPos'AnimatedTopFn (S n) (NoMatch tm') =
  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
    [E_LamremoveFnPos'Animated;
     E_ZeroremoveFnPos'Animated;
     E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     evalremoveFnPos'UndefinedAnimated]
    n (NoMatch tm').


Proof. intros. unfold evalremoveFnPos'AnimatedTopFn.
remember n. destruct n0.
-- simpl. reflexivity.
-- remember (E_LamremoveFnPos'Animated (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
rewrite <- Heqr0.
--- simpl. reflexivity.
--- simpl. assert (H0 : E_LamremoveFnPos'Animated (S n0) (NoMatch tm') = (NoMatch tm')).
---- auto.
---- rewrite H0 in Heqr0. discriminate Heqr0.
--- destruct n0.
---- reflexivity.
---- remember (E_ZeroremoveFnPos'Animated (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
rewrite <- Heqr1.
{ simpl. reflexivity. }
{ simpl. assert (H0 : E_ZeroremoveFnPos'Animated (S n0) (NoMatch tm') = NoMatch tm'). auto.
  rewrite H0 in Heqr1. discriminate Heqr1. }
{ destruct n0.
  { reflexivity. }
  { remember (E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
    fold evalremoveFnPos'AnimatedTopFn.
    rewrite <- Heqr2.
    { simpl. reflexivity. }
    { simpl. assert (H0 : E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm') = NoMatch tm'). auto.
      rewrite H0 in Heqr2. discriminate Heqr2. }
    { destruct n0.
      { reflexivity. }
      { remember (E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
        fold evalremoveFnPos'AnimatedTopFn.
        rewrite <- Heqr3.
        { simpl. reflexivity. }
        { simpl. assert (H0 : E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm') = NoMatch tm'). auto.
          rewrite H0 in Heqr3. discriminate Heqr3. }
        { destruct n0.
          { reflexivity. }
          { remember (E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
            fold evalremoveFnPos'AnimatedTopFn.
            rewrite <- Heqr4.
            { simpl. reflexivity. }
            { simpl. assert (H0 : E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm') = NoMatch tm'). auto.
              rewrite H0 in Heqr4. discriminate Heqr4. }
            { destruct n0.
              { reflexivity. }
              { remember (E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
                fold evalremoveFnPos'AnimatedTopFn.
                rewrite <- Heqr5.
                { simpl. reflexivity. }
                { simpl. assert (H0 : E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm') = NoMatch tm'). auto.
                  rewrite H0 in Heqr5. discriminate Heqr5. }
                { destruct n0.
                  { reflexivity. }
                  { remember (E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
                    fold evalremoveFnPos'AnimatedTopFn.
                    rewrite <- Heqr6.
                    { simpl. reflexivity. }
                    { simpl. assert (H0 : E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm') = NoMatch tm'). auto.
                      rewrite H0 in Heqr6. discriminate Heqr6. }
                    { destruct n0.
                      { reflexivity. }
                      { remember (E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
                        fold evalremoveFnPos'AnimatedTopFn.
                        rewrite <- Heqr7.
                        { simpl. reflexivity. }
                        { simpl. assert (H0 : E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm') = NoMatch tm'). auto.
                          rewrite H0 in Heqr7. discriminate Heqr7. }
                        { destruct n0.
                          { reflexivity. }
                          { remember (E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
                            fold evalremoveFnPos'AnimatedTopFn.
                            rewrite <- Heqr8.
                            { simpl. reflexivity. }
                            { simpl. assert (H0 : E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm') = NoMatch tm'). auto.
                              rewrite H0 in Heqr8. discriminate Heqr8. }
                            { destruct n0.
                              { reflexivity. }
                              { remember (E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0.
                                { simpl. assert (H0 : E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm') = NoMatch tm'). auto.
                                  rewrite H0 in Heqr9. discriminate Heqr9. }
                                { simpl. assert (H0 : E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm') = NoMatch tm'). auto.
                                  rewrite H0 in Heqr9. discriminate Heqr9. }
                                { destruct n0.
                                  { reflexivity. }
                                  { remember (evalremoveFnPos'UndefinedAnimated (S n0) (NoMatch tm')) as r0. destruct r0.
                                    { simpl. assert (H0 : evalremoveFnPos'UndefinedAnimated (S n0) (NoMatch tm') = NoMatch tm'). auto.
                                      rewrite H0 in Heqr10. discriminate Heqr10. }
                                    { simpl. assert (H0 : evalremoveFnPos'UndefinedAnimated (S n0) (NoMatch tm') = NoMatch tm'). auto.
                                      rewrite H0 in Heqr10. discriminate Heqr10. }
                                    { auto. }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}
Qed.

(*




rewrite <- Heqr0. simpl. reflexivity. unfold dispatch_coind_ext. destruct n0.
----- auto.
----- rewrite <- Heqr0. simpl. reflexivity.
--- simpl. unfold dispatch_coind_ext. destruct n0.
---- rewrite <- Heqr0. reflexivity.
---- remember (E_ZeroremoveFnPos'Animated (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
rewrite <- Heqr0.
----- simpl. reflexivity.
----- simpl. unfold dispatch_coind_ext. rewrite <- Heqr0. simpl. reflexivity.
----- unfold dispatch_coind_ext. destruct n0.
* rewrite <- Heqr0. auto.
* remember (E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
rewrite <- Heqr0.
** simpl. fold evalremoveFnPos'AnimatedTopFn.  rewrite <- Heqr2. reflexivity.
** fold evalremoveFnPos'AnimatedTopFn.  rewrite <- Heqr0. rewrite <- Heqr2. reflexivity.
** fold evalremoveFnPos'AnimatedTopFn. rewrite <- Heqr2. destruct n0.
*** rewrite <- Heqr0. reflexivity.
*** remember (E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
rewrite <- Heqr0.
**** simpl. auto.
**** rewrite <- Heqr0. auto.
**** fold evalremoveFnPos'AnimatedTopFn. destruct n0.
***** rewrite <- Heqr0. auto.
***** remember (E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0. unfold dispatch_coind_ext.
rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
****** rewrite <- Heqr0. simpl. auto.
****** destruct n0.
******* rewrite <- Heqr0. auto.
******* remember (E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0.
********  rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
******** rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
******** destruct n0.
********* rewrite <- Heqr0. auto.
********* remember (E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0.
**********  rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
********** rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
********** destruct n0.
*********** rewrite <- Heqr0. auto.
*********** remember (E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0.
************  rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
************ rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
************ destruct n0.
************* rewrite <- Heqr0. auto.
************* remember (E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0.
**************  rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
************** rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
************** destruct n0.
*************** rewrite <- Heqr0. auto.
*************** remember (E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S n0) (NoMatch tm')) as r0. destruct r0.
****************  rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
**************** rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
**************** remember (evalremoveFnPos'UndefinedAnimated (S n0) (NoMatch tm')) as r0. destruct r0.
***************** rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
***************** rewrite <- Heqr0; (try rewrite <- Heqr0; try auto).
***************** auto. Qed.
*)
Lemma evalTop_step : forall n x,
  evalremoveFnPos'AnimatedTopFn (S n) (x) =
  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
    [E_LamremoveFnPos'Animated;
     E_ZeroremoveFnPos'Animated;
     E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     evalremoveFnPos'UndefinedAnimated]
    n (x).
Proof. intros. destruct x; (try eapply evalTop_stepSuccess; try eapply evalTop_stepNoMatch).
* assert (H0 : evalremoveFnPos'AnimatedTopFn (S n) (FuelError tm') =  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
    [E_LamremoveFnPos'Animated;
     E_ZeroremoveFnPos'Animated;
     E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     evalremoveFnPos'UndefinedAnimated] n (FuelError tm')).
** destruct n.
*** simpl. reflexivity.
*** unfold evalremoveFnPos'AnimatedTopFn. remember (E_LamremoveFnPos'Animated (S n) (FuelError tm')) as r0. destruct r0. 
**** reflexivity.
**** assert (H1 : E_LamremoveFnPos'Animated (S n) (FuelError tm') = (FuelError tm')).
***** auto.
***** rewrite -> H1 in Heqr0. auto.
**** assert (H1 : E_LamremoveFnPos'Animated (S n) (FuelError tm') = (FuelError tm')).
***** auto.
***** rewrite -> H1 in Heqr0. discriminate Heqr0.
** auto. Qed. 


  
Lemma anim_S_tabs : forall n x T t f,
  evalTransparentSigma2AnimatedTopFn (S (S n)) (Success tm (tabs x T t)) f =
  Success tm (tabs x T t).
Proof.
  intros.
  unfold evalTransparentSigma2AnimatedTopFn,
         evalremoveFnPosinputLift,
         evalremoveFnPosTransparentSigmaOutputPush,
         tmTransparentSigmaPush.
  assert (HE_Lam : E_LamremoveFnPos'Animated (S n) (Success tm' (tabs' x T (tmLift t))) =
                    Success tm' (tabs' x T (tmLift t)))
    by (unfold E_LamremoveFnPos'Animated; reflexivity).
  assert (Hdisp : evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift (tabs x T t))) =
                   Success tm' (tabs' x T (tmLift t))).
  { cbn [tmLift evalremoveFnPos'AnimatedTopFn dispatch_coind_ext].
    rewrite HE_Lam. reflexivity. }
  rewrite Hdisp.
  simpl tmTransparentSigmaPushBody.
  rewrite tmTransparentSigmaPushBody_tmLift.
  reflexivity.
Qed.

Lemma anim_S_tzero : forall n f,
  evalTransparentSigma2AnimatedTopFn (S (S (S n))) (Success tm tzero) f =
  Success tm tzero.
Proof.
  intros.
  unfold evalTransparentSigma2AnimatedTopFn,
         evalremoveFnPosinputLift,
         evalremoveFnPosTransparentSigmaOutputPush,
         tmTransparentSigmaPush.
  assert (Hdisp : evalremoveFnPos'AnimatedTopFn (S (S (S n))) (Success tm' (tmLift tzero)) =
                   Success tm' tzero').
  { cbn [tmLift evalremoveFnPos'AnimatedTopFn].
    exact (dispatch_tzero n). }
  rewrite Hdisp.
  simpl tmTransparentSigmaPushBody. reflexivity.
Qed.

Lemma anim_S_tsucc : forall n t f,
  evalTransparentSigma2AnimatedTopFn (S (S (S (S n)))) (Success tm (tsucc t)) f =
  match evalTransparentSigma2AnimatedTopFn (S n) (Success tm t) f with
  | Success v => Success tm (tsucc v)
  | other => other
  end.
Proof.
  intros n t f.
  unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
         evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
  cbn [tmLift].
  destruct (evalremoveFnPos'AnimatedTopFn_always_success (S n) (tmLift t)) as [w Hw].
  assert (Hdisp : evalremoveFnPos'AnimatedTopFn (S (S (S (S n)))) (Success tm' (tsucc' (tmLift t))) =
                   Success tm' (tsucc' w)).
  { rewrite evalTop_step.
    rewrite (dispatch_tsucc n t).
    rewrite Hw. reflexivity. }
  rewrite Hw, Hdisp.
  simpl tmTransparentSigmaPushBody.
  reflexivity.
Qed.

(** Direct dispatch characterisation starting at E_PredZero (index 3), for [tpred'] input.
    Requires [evalremoveFnPos'AnimatedTopFn_always_success] (always returns Success) to rule
    out FuelError paths.  The isValueFn check inside E_PredSucc and the oracle equation
    both require knowing that the always_success witness [w] equals [tmLift v] for some
    concrete PCF value [v] — a fact not stated by always_success.  Admitted pending either
    an [always_value] lemma or a transparent [evalremoveFnPos'AnimatedTopFn]. *)
Lemma dispatch_tpred_from_pred : forall n t f,
  (match dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
      [E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      (S (S n)) (Success tm' (tpred' (tmLift t))) with
   | Success x => Success tm (tmTransparentSigmaPushBody f x)
   | _ => NoMatch tm
   end) =
  match (match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t)) with
         | Success x => Success tm (tmTransparentSigmaPushBody f x)
         | _ => NoMatch tm
         end) with
  | Success tzero => Success tm tzero
  | _ =>
      match (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
             | Success x => Success tm (tmTransparentSigmaPushBody f x)
             | _ => NoMatch tm
             end) with
      | Success (tsucc v) =>
          if isValueFn v then Success tm v else Success tm (f (tpred t))
      | _ => Success tm (f (tpred t))
      end
  end.
Proof.
Admitted.

(** Full dispatch characterisation for [tpred'] inputs at the [tm] level
    (post push-through-oracle [f]).  After unfolding [evalTransparentSigma2AnimatedTopFn],
    [evalremoveFnPosinputLift], [evalremoveFnPosTransparentSigmaOutputPush], and
    [tmTransparentSigmaPush], and reducing [tmLift (tpred t)] to [tpred' (tmLift t)], the
    goal of [anim_S_tpred] is exactly this lemma.
    E_Lam / E_Zero / E_Succ return [NoMatch] on [tpred'] inputs (three fuel
    units consumed).  E_PredZero fires at fuel [S(S n)]; if the argument
    evaluates to [tzero'] it returns zero.  E_PredSucc fires at fuel [S n];
    if the argument evaluates to [tsucc' u] and the pushed value is a value,
    it returns [u]; otherwise the oracle fires. *)
Lemma dispatch_tpred : forall n t f,
  (match evalremoveFnPos'AnimatedTopFn (S (S (S (S (S (S n)))))) (Success tm' (tpred' (tmLift t))) with
   | Success x => Success tm (tmTransparentSigmaPushBody f x)
   | _ => NoMatch tm
   end)
  =
  match (match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t)) with
         | Success x => Success tm (tmTransparentSigmaPushBody f x)
         | _ => NoMatch tm
         end) with
  | Success tzero => Success tm tzero
  | _ =>
      match (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
             | Success x => Success tm (tmTransparentSigmaPushBody f x)
             | _ => NoMatch tm
             end) with
      | Success (tsucc v) =>
          if isValueFn v then Success tm v else Success tm (f (tpred t))
      | _ => Success tm (f (tpred t))
      end
  end.
Proof.
  intros n t f.
  rewrite evalTop_step.
  cbn [dispatch_coind_ext].
  assert (HE_Lam : E_LamremoveFnPos'Animated (S (S (S (S (S n))))) (Success tm' (tpred' (tmLift t))) = NoMatch tm')
    by (unfold E_LamremoveFnPos'Animated; reflexivity).
  rewrite HE_Lam.
  cbn [dispatch_coind_ext].
  assert (HE_Zero : E_ZeroremoveFnPos'Animated (S (S (S (S n)))) (Success tm' (tpred' (tmLift t))) = NoMatch tm')
    by (unfold E_ZeroremoveFnPos'Animated; reflexivity).
  rewrite HE_Zero.
  cbn [dispatch_coind_ext].
  assert (HE_Succ : E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                      (S (S (S n))) (Success tm' (tpred' (tmLift t))) = NoMatch tm')
    by (unfold E_SuccremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_Succ.
  exact (dispatch_tpred_from_pred n t f).
Qed.

Lemma anim_S_tpred : forall n t f,
  evalTransparentSigma2AnimatedTopFn (S (S (S (S (S (S n)))))) (Success tm (tpred t)) f =
  match evalTransparentSigma2AnimatedTopFn (S (S n)) (Success tm t) f with
  | Success tzero =>
      Success tm tzero
  | _ =>
      match evalTransparentSigma2AnimatedTopFn (S n) (Success tm t) f with
      | Success (tsucc v) =>
          if isValueFn v then Success tm v else Success tm (f (tpred t))
      | _ => Success tm (f (tpred t))
      end
  end.
Proof.
  intros n t f.
  unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
         evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
  cbn [tmLift].
  exact (dispatch_tpred n t f).
Qed.

(** Direct dispatch characterisation starting at E_IfzZero (index 6), for [tifz'] input.
    Same gap as [dispatch_tpred_from_pred]: the isValueFn check in E_IfzSucc requires
    [always_value] or evalTop transparency.  Admitted for the same reason. *)
Lemma dispatch_tifz_from_ifz : forall n t t1 t2 f,
  (match dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
      [E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      (S (S n)) (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))) with
   | Success x => Success tm (tmTransparentSigmaPushBody f x)
   | _ => NoMatch tm
   end) =
  match (match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t)) with
         | Success x => Success tm (tmTransparentSigmaPushBody f x)
         | _ => NoMatch tm
         end) with
  | Success tzero =>
      (match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t1)) with
       | Success x => Success tm (tmTransparentSigmaPushBody f x)
       | _ => NoMatch tm
       end)
  | _ =>
      match (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
             | Success x => Success tm (tmTransparentSigmaPushBody f x)
             | _ => NoMatch tm
             end) with
      | Success (tsucc vn) =>
          if isValueFn vn
          then (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t2)) with
                | Success x => Success tm (tmTransparentSigmaPushBody f x)
                | _ => NoMatch tm
                end)
          else Success tm (f (tifz t t1 t2))
      | _ => Success tm (f (tifz t t1 t2))
      end
  end.
Proof.
Admitted.

Lemma dispatch_tifz : forall n t t1 t2 f,
  (match evalremoveFnPos'AnimatedTopFn
     (S (S (S (S (S (S (S (S (S n))))))))) (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))) with
   | Success x => Success tm (tmTransparentSigmaPushBody f x)
   | _ => NoMatch tm
   end)
  =
  match (match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t)) with
         | Success x => Success tm (tmTransparentSigmaPushBody f x)
         | _ => NoMatch tm
         end) with
  | Success tzero =>
      (match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t1)) with
       | Success x => Success tm (tmTransparentSigmaPushBody f x)
       | _ => NoMatch tm
       end)
  | _ =>
      match (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
             | Success x => Success tm (tmTransparentSigmaPushBody f x)
             | _ => NoMatch tm
             end) with
      | Success (tsucc vn) =>
          if isValueFn vn
          then (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t2)) with
                | Success x => Success tm (tmTransparentSigmaPushBody f x)
                | _ => NoMatch tm
                end)
          else Success tm (f (tifz t t1 t2))
      | _ => Success tm (f (tifz t t1 t2))
      end
  end.
Proof.
  intros n t t1 t2 f.
  rewrite evalTop_step.
  cbn [dispatch_coind_ext].
  assert (HE_Lam : E_LamremoveFnPos'Animated (S (S (S (S (S (S (S (S n)))))))) (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))) = NoMatch tm')
    by (unfold E_LamremoveFnPos'Animated; reflexivity).
  rewrite HE_Lam.
  cbn [dispatch_coind_ext].
  assert (HE_Zero : E_ZeroremoveFnPos'Animated (S (S (S (S (S (S (S n))))))) (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))) = NoMatch tm')
    by (unfold E_ZeroremoveFnPos'Animated; reflexivity).
  rewrite HE_Zero.
  cbn [dispatch_coind_ext].
  assert (HE_Succ : E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                      (S (S (S (S (S (S n)))))) (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))) = NoMatch tm')
    by (unfold E_SuccremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_Succ.
  cbn [dispatch_coind_ext].
  assert (HE_PredZero : E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                          (S (S (S (S (S n))))) (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))) = NoMatch tm')
    by (unfold E_PredZeroremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_PredZero.
  cbn [dispatch_coind_ext].
  assert (HE_PredSucc : E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                          (S (S (S (S n)))) (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))) = NoMatch tm')
    by (unfold E_PredSuccremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_PredSucc.
  cbn [dispatch_coind_ext].
  assert (HE_App : E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                     (S (S (S n))) (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))) = NoMatch tm')
    by (unfold E_AppremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_App.
  exact (dispatch_tifz_from_ifz n t t1 t2 f).
Qed.

Lemma anim_S_tifz : forall n t t1 t2 f,
  evalTransparentSigma2AnimatedTopFn
    (S (S (S (S (S (S (S (S (S n))))))))) (Success tm (tifz t t1 t2)) f =
  match evalTransparentSigma2AnimatedTopFn (S (S n)) (Success tm t) f with
  | Success tzero =>
      evalTransparentSigma2AnimatedTopFn (S (S n)) (Success tm t1) f
  | _ =>
      match evalTransparentSigma2AnimatedTopFn (S n) (Success tm t) f with
      | Success (tsucc vn) =>
          if isValueFn vn
          then evalTransparentSigma2AnimatedTopFn (S n) (Success tm t2) f
          else Success tm (f (tifz t t1 t2))
      | _ => Success tm (f (tifz t t1 t2))
      end
  end.
Proof.
  intros n t t1 t2 f.
  unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
         evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
  cbn [tmLift].
  exact (dispatch_tifz n t t1 t2 f).
Qed.

(** Direct dispatch characterisation starting at E_App (index 5), for [tapp'] input.
    Same gap as [dispatch_tpred_from_pred]: [isValueFn v2] in the E_App rule
    requires [always_value] or evalTop transparency.  Admitted for the same reason. *)
Lemma dispatch_tapp_from_app : forall n t1 t2 f,
  (match dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
      [E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      (S n) (Success tm' (tapp' (tmLift t1) (tmLift t2))) with
   | Success x => Success tm (tmTransparentSigmaPushBody f x)
   | _ => NoMatch tm
   end) =
  match (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t1)) with
         | Success x => Success tm (tmTransparentSigmaPushBody f x)
         | _ => NoMatch tm
         end) with
  | Success (tabs x T t3) =>
      match (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t2)) with
             | Success x => Success tm (tmTransparentSigmaPushBody f x)
             | _ => NoMatch tm
             end) with
      | Success v2 =>
          if isValueFn v2
          then (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift (subst x v2 t3))) with
                | Success x => Success tm (tmTransparentSigmaPushBody f x)
                | _ => NoMatch tm
                end)
          else Success tm (f (tapp t1 t2))
      | _ => Success tm (f (tapp t1 t2))
      end
  | Success _ => Success tm (f (tapp t1 t2))
  | _ => Success tm (f (tapp t1 t2))
  end.
Proof.
Admitted.

Lemma dispatch_tapp : forall n t1 t2 f,
  (match evalremoveFnPos'AnimatedTopFn
     (S (S (S (S (S (S (S n))))))) (Success tm' (tapp' (tmLift t1) (tmLift t2))) with
   | Success x => Success tm (tmTransparentSigmaPushBody f x)
   | _ => NoMatch tm
   end)
  =
  match (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t1)) with
         | Success x => Success tm (tmTransparentSigmaPushBody f x)
         | _ => NoMatch tm
         end) with
  | Success (tabs x T t3) =>
      match (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t2)) with
             | Success x => Success tm (tmTransparentSigmaPushBody f x)
             | _ => NoMatch tm
             end) with
      | Success v2 =>
          if isValueFn v2
          then (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift (subst x v2 t3))) with
                | Success x => Success tm (tmTransparentSigmaPushBody f x)
                | _ => NoMatch tm
                end)
          else Success tm (f (tapp t1 t2))
      | _ => Success tm (f (tapp t1 t2))
      end
  | Success _ => Success tm (f (tapp t1 t2))
  | _ => Success tm (f (tapp t1 t2))
  end.
Proof.
  intros n t1 t2 f.
  rewrite evalTop_step.
  cbn [dispatch_coind_ext].
  assert (HE_Lam : E_LamremoveFnPos'Animated (S (S (S (S (S (S n)))))) (Success tm' (tapp' (tmLift t1) (tmLift t2))) = NoMatch tm')
    by (unfold E_LamremoveFnPos'Animated; reflexivity).
  rewrite HE_Lam.
  cbn [dispatch_coind_ext].
  assert (HE_Zero : E_ZeroremoveFnPos'Animated (S (S (S (S (S n))))) (Success tm' (tapp' (tmLift t1) (tmLift t2))) = NoMatch tm')
    by (unfold E_ZeroremoveFnPos'Animated; reflexivity).
  rewrite HE_Zero.
  cbn [dispatch_coind_ext].
  assert (HE_Succ : E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                      (S (S (S (S n)))) (Success tm' (tapp' (tmLift t1) (tmLift t2))) = NoMatch tm')
    by (unfold E_SuccremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_Succ.
  cbn [dispatch_coind_ext].
  assert (HE_PredZero : E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                          (S (S (S n))) (Success tm' (tapp' (tmLift t1) (tmLift t2))) = NoMatch tm')
    by (unfold E_PredZeroremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_PredZero.
  cbn [dispatch_coind_ext].
  assert (HE_PredSucc : E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                          (S (S n)) (Success tm' (tapp' (tmLift t1) (tmLift t2))) = NoMatch tm')
    by (unfold E_PredSuccremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_PredSucc.
  exact (dispatch_tapp_from_app n t1 t2 f).
Qed.

Lemma anim_S_tapp : forall n t1 t2 f,
  evalTransparentSigma2AnimatedTopFn
    (S (S (S (S (S (S (S n))))))) (Success tm (tapp t1 t2)) f =
  match evalTransparentSigma2AnimatedTopFn (S n) (Success tm t1) f with
  | Success (tabs x T t3) =>
      match evalTransparentSigma2AnimatedTopFn (S n) (Success tm t2) f with
      | Success v2 =>
          if isValueFn v2
          then evalTransparentSigma2AnimatedTopFn (S n) (Success tm (subst x v2 t3)) f
          else Success tm (f (tapp t1 t2))
      | _ => Success tm (f (tapp t1 t2))
      end
  | Success _ => Success tm (f (tapp t1 t2))
  | _ => Success tm (f (tapp t1 t2))
  end.
Proof.
  intros n t1 t2 f.
  unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
         evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
  cbn [tmLift].
  exact (dispatch_tapp n t1 t2 f).
Qed.

Lemma dispatch_tfix_from_fix : forall n fn T t f,
  (match dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
      [E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      (S n) (Success tm' (tfix' fn T (tmLift t))) with
   | Success x => Success tm (tmTransparentSigmaPushBody f x)
   | _ => NoMatch tm
   end) =
  (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift (subst fn (tfix fn T t) t))) with
   | Success x => Success tm (tmTransparentSigmaPushBody f x)
   | _ => NoMatch tm
   end).
Admitted.

Lemma dispatch_tfix : forall n fn T t f,
  (match evalremoveFnPos'AnimatedTopFn
     (S (S (S (S (S (S (S (S (S (S n)))))))))) (Success tm' (tfix' fn T (tmLift t))) with
   | Success x => Success tm (tmTransparentSigmaPushBody f x)
   | _ => NoMatch tm
   end)
  =
  (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift (subst fn (tfix fn T t) t))) with
   | Success x => Success tm (tmTransparentSigmaPushBody f x)
   | _ => NoMatch tm
   end).
Proof.
  intros n fn T t f.
  rewrite evalTop_step.
  cbn [dispatch_coind_ext].
  assert (HE_Lam : E_LamremoveFnPos'Animated (S (S (S (S (S (S (S (S (S n))))))))) (Success tm' (tfix' fn T (tmLift t))) = NoMatch tm')
    by (unfold E_LamremoveFnPos'Animated; reflexivity).
  rewrite HE_Lam.
  cbn [dispatch_coind_ext].
  assert (HE_Zero : E_ZeroremoveFnPos'Animated (S (S (S (S (S (S (S (S n)))))))) (Success tm' (tfix' fn T (tmLift t))) = NoMatch tm')
    by (unfold E_ZeroremoveFnPos'Animated; reflexivity).
  rewrite HE_Zero.
  cbn [dispatch_coind_ext].
  assert (HE_Succ : E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                      (S (S (S (S (S (S (S n))))))) (Success tm' (tfix' fn T (tmLift t))) = NoMatch tm')
    by (unfold E_SuccremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_Succ.
  cbn [dispatch_coind_ext].
  assert (HE_PredZero : E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                          (S (S (S (S (S (S n)))))) (Success tm' (tfix' fn T (tmLift t))) = NoMatch tm')
    by (unfold E_PredZeroremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_PredZero.
  cbn [dispatch_coind_ext].
  assert (HE_PredSucc : E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                          (S (S (S (S (S n))))) (Success tm' (tfix' fn T (tmLift t))) = NoMatch tm')
    by (unfold E_PredSuccremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_PredSucc.
  cbn [dispatch_coind_ext].
  assert (HE_App : E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                     (S (S (S (S n)))) (Success tm' (tfix' fn T (tmLift t))) = NoMatch tm')
    by (unfold E_AppremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_App.
  cbn [dispatch_coind_ext].
  assert (HE_IfzZero : E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                         (S (S (S n))) (Success tm' (tfix' fn T (tmLift t))) = NoMatch tm')
    by (unfold E_IfzZeroremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_IfzZero.
  cbn [dispatch_coind_ext].
  assert (HE_IfzSucc : E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn
                         (S (S n)) (Success tm' (tfix' fn T (tmLift t))) = NoMatch tm')
    by (unfold E_IfzSuccremoveFnPos'Animated, option_to_result; reflexivity).
  rewrite HE_IfzSucc.
  exact (dispatch_tfix_from_fix n fn T t f).
Qed.

Lemma anim_S_tfix : forall n fn T t f,
  evalTransparentSigma2AnimatedTopFn
    (S (S (S (S (S (S (S (S (S (S n)))))))))) (Success tm (tfix fn T t)) f =
  evalTransparentSigma2AnimatedTopFn (S n) (Success tm (subst fn (tfix fn T t) t)) f.
Proof.
  intros n fn T t f.
  unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
         evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
  cbn [tmLift].
  exact (dispatch_tfix n fn T t f).
Qed.

Lemma anim_S_tvar : forall n s f,
  evalTransparentSigma2AnimatedTopFn (S n) (Success tm (tvar s)) f =
  Success tm (f (tvar s)).
Proof.
  intros n s f.
  (* Split on the first 9 successor layers; the last case (n9) is abstract
     but has 10 concrete S-constructors available so cbn can chain through
     all 9 handlers (E_Lam … E_Fix return NoMatch for tvar) and fire
     UndefinedAnimated (or reach fuel 0) to produce the oracle result. *)
  destruct n as [|[|[|[|[|[|[|[|[|[|n10]]]]]]]]]]
  ; unfold evalTransparentSigma2AnimatedTopFn; cbn;
    try rewrite tmTransparentSigmaPushBody_tmLift; reflexivity.
Qed.


Theorem correspondence_completeness_bigstop : forall (inputTm tm1 : tm),
  bigstop inputTm tm1 ->
  exists (tm2 : tm) (n : nat),
    bigstop tm1 tm2 /\
    (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm tm2.
Proof.
  (* BS_Stop is the base case: take tm2 = inputTm, n = 0; animation at 0
     applies the oracle (id) and returns inputTm directly.
     Remaining cases (BS_Succ, BS_Pred, BS_App*, BS_Ifz*, BS_PredZero,
     BS_PredSucc, BS_Fix) require either:
       (a) congruence lemmas: animation(S n)(C e) relates to animation(n)(e)
           with the SAME fuel for all subterms — but fuel usage is non-uniform
           across subterms, so a monotonicity argument (animate_mono_bigstop)
           is needed to align witnesses;
       (b) bigstop transitivity to chain IH witnesses.
     Both are non-trivial given the conjunction-packaged premises in bigstop
     constructors; admitted pending that infrastructure. *)
Admitted.

(** CSB — Soundness w.r.t. bigstop.
    Proof by strong induction on fuel [n] via [lt_wf_ind].
    At each [n], destruct the input constructor and dispatch on whether
    the handler lemma [anim_S_*] applies (large [n]) or the oracle fires
    (small [n]); oracle cases give [outputTm = inputTm] → [BS_Stop].
    Small-fuel oracle cases for medium [n] (e.g. [tapp] at [n=2..6])
    are [admit]ted pending a general oracle lemma. *)
Theorem correspondence_soundness_bigstop : forall (n : nat) (inputTm outputTm : tm),
  (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t') = Success tm outputTm ->
  bigstop inputTm outputTm.
Proof.
  intro n.
  apply (lt_wf_ind n (fun n => forall inputTm outputTm,
    (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' => t') = Success tm outputTm ->
    bigstop inputTm outputTm)).
  clear n. intros n IH inputTm outputTm Hanim.
  destruct n as [| n'].
  { (* n = 0: oracle fires *)
    rewrite anim_0_oracle in Hanim. injection Hanim as <-. apply BS_Stop. }
  (* n = S n' *)
  destruct inputTm as [s | lx lT lbody | t1 t2 | | t | t | tdisc t1 t2 | fn T fbody].

  (* ---- tvar s: oracle fires for any S n' via anim_S_tvar ---- *)
  - rewrite anim_S_tvar in Hanim. injection Hanim as <-. apply BS_Stop.

  (* ---- tabs lx lT lbody: E_Lam fires at n ≥ 2; n=1 is oracle ---- *)
  - destruct n' as [| m].
    + (* n = 1: oracle *)
      rewrite anim_1_oracle_id in Hanim. injection Hanim as <-. apply BS_Stop.
    + (* n = S(S m) ≥ 2: E_Lam fires, result is tabs *)
      rewrite anim_S_tabs in Hanim. injection Hanim as <-. apply BS_Stop.

  (* ---- tapp t1 t2: E_App fires at n ≥ 7; n=1..6 are oracle ---- *)
  - destruct n' as [|[|[|[|[|[|k]]]]]].
    (* n = 1: oracle *)
    + rewrite anim_1_oracle_id in Hanim. injection Hanim as <-. apply BS_Stop.
    (* n = 2..6: oracle fires (E_App handler needs ≥ 7 fuel) *)
    + rewrite (anim_below_thr_tapp 2 t1 t2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tapp 3 t1 t2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tapp 4 t1 t2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tapp 5 t1 t2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tapp 6 t1 t2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    (* n = 7+k: E_App handler fires *)
    + rewrite anim_S_tapp in Hanim.
      destruct (evalTransparentSigma2AnimatedTopFn (S k) (Success tm t1) (fun t' => t'))
        as [| v1 |] eqn:H1.
      * (* inner t1 eval = FuelError → oracle *)
        injection Hanim as <-. apply BS_Stop.
      * destruct v1 as [| lx' lT' lbody' | | | | | | ];
          try (injection Hanim as <-; apply BS_Stop).
        (* v1 = tabs lx' lT' lbody' *)
        destruct (evalTransparentSigma2AnimatedTopFn (S k) (Success tm t2) (fun t' => t'))
          as [| v2 |] eqn:H2.
        -- injection Hanim as <-. apply BS_Stop.
        -- destruct (isValueFn v2) eqn:Hv2.
           ++ destruct (evalTransparentSigma2AnimatedTopFn (S k) (Success tm (subst lx' v2 lbody')) (fun t' => t'))
                as [| r |] eqn:H3.
              ** discriminate.
              ** injection Hanim as <-.
                 eapply BS_App. repeat split.
                 --- apply (IH (S k)). lia. exact H1.
                 --- apply (IH (S k)). lia. exact H2.
                 --- apply isValueFn_to_is_value. exact Hv2.
                 --- apply (IH (S k)). lia. exact H3.
              ** discriminate.
           ++ injection Hanim as <-. apply BS_Stop.
        -- injection Hanim as <-. apply BS_Stop.
      * (* inner t1 eval = NoMatch → oracle *)
        injection Hanim as <-. apply BS_Stop.

  (* ---- tzero: E_Zero fires at n ≥ 3; n=1,2 are oracle ---- *)
  - destruct n' as [|[| m]].
    + rewrite anim_1_oracle_id in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tzero 2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite anim_S_tzero in Hanim. injection Hanim as <-. apply BS_Stop.

  (* ---- tsucc t: E_Succ fires at n ≥ 4; n=1,2,3 are oracle ---- *)
  - destruct n' as [|[|[|k]]].
    + rewrite anim_1_oracle_id in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tsucc 2 t (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tsucc 3 t (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + (* n = 4+k: E_Succ fires *)
      rewrite anim_S_tsucc in Hanim.
      destruct (evalTransparentSigma2AnimatedTopFn (S k) (Success tm t) (fun t' => t'))
        as [| v |] eqn:H1.
      * discriminate.
      * injection Hanim as <-.
        apply BS_Succ. apply (IH (S k)). lia. exact H1.
      * discriminate.

  (* ---- tpred t: E_PredZero/E_PredSucc fire at n ≥ 6; n=1..5 oracle ---- *)
  - destruct n' as [|[|[|[|[|k]]]]].
    + rewrite anim_1_oracle_id in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tpred 2 t (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tpred 3 t (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tpred 4 t (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tpred 5 t (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + (* n = 6+k: anim_S_tpred fires; use set so destruct substitutes into Hanim *)
      rewrite anim_S_tpred in Hanim.
      set (rh := evalTransparentSigma2AnimatedTopFn (S (S k)) (Success tm t) (fun t' => t')) in Hanim.
      set (rl := evalTransparentSigma2AnimatedTopFn (S k) (Success tm t) (fun t' => t')) in Hanim.
      (* Now Hanim: match rh with | Success tzero => ... | _ => match rl with ... end end = ... *)
      destruct rh as [| predv |] eqn:Hpz; simpl in Hanim.
      * (* rh = FuelError: Hanim = match rl with ... *)
        destruct rl as [| v2 |] eqn:Hps; simpl in Hanim;
          try (injection Hanim as <-; apply BS_Stop).
        destruct v2 as [vs | vx vT1 vb1 | va1 va2 | | sv | vp | vd vt1 vt2 | vf vT2 vb2];
          simpl in Hanim; try (injection Hanim as <-; apply BS_Stop).
        (* only tsucc sv left: Hanim = (if isValueFn sv then Success sv else Success (tpred t)) = ... *)
        destruct (isValueFn sv) eqn:Hsv; simpl in Hanim; injection Hanim as <-.
        -- eapply BS_PredSucc. split; [apply (IH (S k)); [lia | exact Hps] |
             apply isValueFn_to_is_value; exact Hsv].
        -- apply BS_Stop.
      * (* rh = Success predv: simpl exposed outer match; need predv destruct to reduce *)
        destruct predv as [ps | px pT1 pb1 | pa1 pa2 | | psn | pp | pd pt1 pt2 | pf pT2 pb2];
          simpl in Hanim.
        (* Constructor order: tvar, tabs, tapp, tzero, tsucc, tpred, tifz, tfix *)
        (* Close tzero branch (4th) via try; all others need r_low check *)
        all: try (injection Hanim as <-; apply BS_PredZero;
                  apply (IH (S (S k))); [lia | exact Hpz]).
        (* Non-tzero: Hanim = match rl with ... *)
        all: destruct rl as [| v2 |] eqn:Hps; simpl in Hanim;
             try (injection Hanim as <-; apply BS_Stop).
        all: destruct v2 as [vs | vx vT1 vb1 | va1 va2 | | sv | vp | vd vt1 vt2 | vf vT2 vb2];
             simpl in Hanim; try (injection Hanim as <-; apply BS_Stop).
        all: destruct (isValueFn sv) eqn:Hsv; simpl in Hanim; injection Hanim as <-.
        all: try apply BS_Stop.
        all: eapply BS_PredSucc; split; [apply (IH (S k)); [lia | exact Hps] |
               apply isValueFn_to_is_value; exact Hsv].
      * (* rh = NoMatch: Hanim = match rl with ... *)
        destruct rl as [| v2 |] eqn:Hps; simpl in Hanim;
          try (injection Hanim as <-; apply BS_Stop).
        destruct v2 as [vs | vx vT1 vb1 | va1 va2 | | sv | vp | vd vt1 vt2 | vf vT2 vb2];
          simpl in Hanim; try (injection Hanim as <-; apply BS_Stop).
        destruct (isValueFn sv) eqn:Hsv; simpl in Hanim; injection Hanim as <-.
        -- eapply BS_PredSucc. split; [apply (IH (S k)); [lia | exact Hps] |
             apply isValueFn_to_is_value; exact Hsv].
        -- apply BS_Stop.

  (* ---- tifz tdisc t1 t2: fires at n ≥ 9; n=1..8 oracle ---- *)
  - destruct n' as [|[|[|[|[|[|[|[|k]]]]]]]].
    + rewrite anim_1_oracle_id in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tifz 2 tdisc t1 t2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tifz 3 tdisc t1 t2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tifz 4 tdisc t1 t2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tifz 5 tdisc t1 t2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tifz 6 tdisc t1 t2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tifz 7 tdisc t1 t2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tifz 8 tdisc t1 t2 (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + (* n = 9+k: anim_S_tifz fires; use set so destruct substitutes into Hanim *)
      rewrite anim_S_tifz in Hanim.
      set (rh := evalTransparentSigma2AnimatedTopFn (S (S k)) (Success tm tdisc) (fun t' => t')) in Hanim.
      set (rl := evalTransparentSigma2AnimatedTopFn (S k) (Success tm tdisc) (fun t' => t')) in Hanim.
      (* Hanim: match rh with | Success tzero => anim(S(S k)) t1 id | _ => match rl with ... end end = ... *)
      destruct rh as [| dv |] eqn:Hd; simpl in Hanim.
      * (* rh = FuelError: _ => branch: check rl *)
        destruct rl as [| v2 |] eqn:Hd2; simpl in Hanim;
          try (injection Hanim as <-; apply BS_Stop).
        destruct v2 as [vs | vx vT1 vb1 | va1 va2 | | svn | vp | vid vt1 vt2 | vf vT2 vb2];
          simpl in Hanim; try (injection Hanim as <-; apply BS_Stop).
        destruct (isValueFn svn) eqn:Hsvn; simpl in Hanim;
          try (injection Hanim as <-; apply BS_Stop).
        set (rt2 := evalTransparentSigma2AnimatedTopFn (S k) (Success tm t2) (fun t' => t')) in Hanim.
        destruct rt2 as [| r |] eqn:Ht2; simpl in Hanim; try discriminate.
        injection Hanim as <-.
        eapply BS_IfzSucc. repeat split.
        -- apply (IH (S k)). lia. exact Hd2.
        -- apply isValueFn_to_is_value. exact Hsvn.
        -- apply (IH (S k)). lia. exact Ht2.
      * (* rh = Success dv: check if dv = tzero *)
        destruct dv as [ds | dx dT1 db1 | da1 da2 | | dsn | dp | did dt1 dt2 | df dT2 db2];
          simpl in Hanim.
        (* Constructor order: tvar(1), tabs(2), tapp(3), tzero(4), tsucc(5), tpred(6), tifz(7), tfix(8) *)
        (* Close tzero (4th) branch via try; all others go to _ => branch and need rl check *)
        all: try (eapply BS_IfzZero; split;
                  [apply (IH (S (S k))); [lia | exact Hd] |
                   apply (IH (S (S k))); [lia | exact Hanim]]).
        all: destruct rl as [| v2 |] eqn:Hd2; simpl in Hanim;
             try (injection Hanim as <-; apply BS_Stop).
        all: destruct v2 as [vs | vx vT1 vb1 | va1 va2 | | svn | vp | vid vt1 vt2 | vf vT2 vb2];
             simpl in Hanim; try (injection Hanim as <-; apply BS_Stop).
        all: destruct (isValueFn svn) eqn:Hsvn; simpl in Hanim;
             try (injection Hanim as <-; apply BS_Stop).
        all: set (rt2 := evalTransparentSigma2AnimatedTopFn (S k) (Success tm t2) (fun t' => t')) in Hanim.
        all: destruct rt2 as [| r |] eqn:Ht2; simpl in Hanim; try discriminate.
        all: injection Hanim as <-.
        all: eapply BS_IfzSucc; repeat split;
             [apply (IH (S k)); [lia | exact Hd2] |
              apply isValueFn_to_is_value; exact Hsvn |
              apply (IH (S k)); [lia | exact Ht2]].
      * (* rh = NoMatch: _ => branch: check rl (same as FuelError) *)
        destruct rl as [| v2 |] eqn:Hd2; simpl in Hanim;
          try (injection Hanim as <-; apply BS_Stop).
        destruct v2 as [vs | vx vT1 vb1 | va1 va2 | | svn | vp | vid vt1 vt2 | vf vT2 vb2];
          simpl in Hanim; try (injection Hanim as <-; apply BS_Stop).
        destruct (isValueFn svn) eqn:Hsvn; simpl in Hanim;
          try (injection Hanim as <-; apply BS_Stop).
        set (rt2 := evalTransparentSigma2AnimatedTopFn (S k) (Success tm t2) (fun t' => t')) in Hanim.
        destruct rt2 as [| r |] eqn:Ht2; simpl in Hanim; try discriminate.
        injection Hanim as <-.
        eapply BS_IfzSucc. repeat split.
        -- apply (IH (S k)). lia. exact Hd2.
        -- apply isValueFn_to_is_value. exact Hsvn.
        -- apply (IH (S k)). lia. exact Ht2.

  (* ---- tfix fn T fbody: E_Fix fires at n ≥ 10; n=1..9 oracle ---- *)
  - destruct n' as [|[|[|[|[|[|[|[|[|k]]]]]]]]].
    + rewrite anim_1_oracle_id in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tfix 2 fn T fbody (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tfix 3 fn T fbody (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tfix 4 fn T fbody (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tfix 5 fn T fbody (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tfix 6 fn T fbody (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tfix 7 fn T fbody (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tfix 8 fn T fbody (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + rewrite (anim_below_thr_tfix 9 fn T fbody (fun t' => t') ltac:(lia)) in Hanim.
      cbn in Hanim. injection Hanim as <-. apply BS_Stop.
    + (* n = 10+k: E_Fix fires, unrolls fixpoint *)
      rewrite anim_S_tfix in Hanim.
      eapply BS_Fix.
      apply (IH (S k)). lia. exact Hanim.
Qed.

(** ASG — General oracle soundness.
    Same strong-induction structure as CSB; oracle cases use [Hf] in place
    of [BS_Stop], and eval constructors mirror the bigstop ones.
    Medium-fuel oracle cases are [admit]ted as in CSB. *)
Theorem animation_soundness_general : forall (f : tm -> tm),
  (forall tm1 : tm, eval tm1 (f tm1)) ->
  forall (inputTm outputTm : tm) (n : nat),
    (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) f = Success tm outputTm ->
    eval inputTm outputTm.
Proof.
  intros f Hf.
  intro inputTm. intro outputTm. intro n. revert inputTm outputTm.
  apply (lt_wf_ind n (fun n => forall inputTm outputTm,
    (evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) f = Success tm outputTm ->
    eval inputTm outputTm)).
  clear n. intros n IH inputTm outputTm Hanim.
  destruct n as [| n'].
  { rewrite anim_0_oracle in Hanim. injection Hanim as <-. apply Hf. }
  destruct inputTm as [s | lx lT lbody | t1 t2 | | t | t | tdisc t1 t2 | fn T fbody].

  (* tvar: oracle for all S n' *)
  - rewrite anim_S_tvar in Hanim. injection Hanim as <-. apply Hf.

  (* tabs: E_Lam fires at n ≥ 2 *)
  - destruct n' as [| m].
    + rewrite anim_1_oracle_f in Hanim. injection Hanim as <-. apply Hf.
    + rewrite anim_S_tabs in Hanim. injection Hanim as <-. apply E_Lam.

  (* tapp: E_App fires at n ≥ 7 *)
  - destruct n' as [|[|[|[|[|[|k]]]]]].
    + rewrite anim_1_oracle_f in Hanim. injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tapp 2 t1 t2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tapp 3 t1 t2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tapp 4 t1 t2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tapp 5 t1 t2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tapp 6 t1 t2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite anim_S_tapp in Hanim.
      destruct (evalTransparentSigma2AnimatedTopFn (S k) (Success tm t1) f)
        as [| v1 |] eqn:H1.
      * injection Hanim as <-. apply Hf.
      * destruct v1 as [| lx' lT' lbody' | | | | | | ];
          try (injection Hanim as <-; apply Hf).
        destruct (evalTransparentSigma2AnimatedTopFn (S k) (Success tm t2) f)
          as [| v2 |] eqn:H2.
        -- injection Hanim as <-. apply Hf.
        -- destruct (isValueFn v2) eqn:Hv2.
           ++ destruct (evalTransparentSigma2AnimatedTopFn (S k) (Success tm (subst lx' v2 lbody')) f)
                as [| r |] eqn:H3.
              ** discriminate.
              ** injection Hanim as <-.
                 eapply E_App. repeat split.
                 --- exact Hv2.
                 --- apply (IH (S k)). lia. exact H1.
                 --- apply (IH (S k)). lia. exact H2.
                 --- apply (IH (S k)). lia. exact H3.
              ** discriminate.
           ++ injection Hanim as <-. apply Hf.
        -- injection Hanim as <-. apply Hf.
      * injection Hanim as <-. apply Hf.

  (* tzero: E_Zero fires at n ≥ 3 *)
  - destruct n' as [|[| m]].
    + rewrite anim_1_oracle_f in Hanim. injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tzero 2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite anim_S_tzero in Hanim. injection Hanim as <-. apply E_Zero.

  (* tsucc t: E_Succ fires at n ≥ 4 *)
  - destruct n' as [|[|[|k]]].
    + rewrite anim_1_oracle_f in Hanim. injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tsucc 2 t f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tsucc 3 t f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite anim_S_tsucc in Hanim.
      set (r := evalTransparentSigma2AnimatedTopFn (S k) (Success tm t) f) in Hanim.
      destruct r as [| v |] eqn:H1; simpl in Hanim.
      * discriminate.
      * injection Hanim as <-.
        apply E_Succ. apply (IH (S k)). lia. exact H1.
      * discriminate.

  (* tpred t: E_PredZero/E_PredSucc fire at n ≥ 6 *)
  - destruct n' as [|[|[|[|[|k]]]]].
    + rewrite anim_1_oracle_f in Hanim. injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tpred 2 t f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tpred 3 t f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tpred 4 t f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tpred 5 t f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite anim_S_tpred in Hanim.
      set (rh := evalTransparentSigma2AnimatedTopFn (S (S k)) (Success tm t) f) in Hanim.
      set (rl := evalTransparentSigma2AnimatedTopFn (S k) (Success tm t) f) in Hanim.
      destruct rh as [| predv |] eqn:Hpz; simpl in Hanim.
      * (* rh = FuelError: _ => check rl *)
        destruct rl as [| v2 |] eqn:Hps; simpl in Hanim;
          try (injection Hanim as <-; apply Hf).
        destruct v2 as [vs | vx vT1 vb1 | va1 va2 | | sv | vp | vd vt1 vt2 | vf vT2 vb2];
          simpl in Hanim; try (injection Hanim as <-; apply Hf).
        destruct (isValueFn sv) eqn:Hsv; simpl in Hanim; injection Hanim as <-.
        -- eapply E_PredSucc. split; [exact Hsv | apply (IH (S k)); [lia | exact Hps]].
        -- apply Hf.
      * (* rh = Success predv: close tzero (4th ctor) via try; others need rl check *)
        destruct predv as [ps | px pT1 pb1 | pa1 pa2 | | psn | pp | pd pt1 pt2 | pf pT2 pb2];
          simpl in Hanim.
        all: try (injection Hanim as <-; apply E_PredZero;
                  apply (IH (S (S k))); [lia | exact Hpz]).
        all: destruct rl as [| v2 |] eqn:Hps; simpl in Hanim;
             try (injection Hanim as <-; apply Hf).
        all: destruct v2 as [vs | vx vT1 vb1 | va1 va2 | | sv | vp | vd vt1 vt2 | vf vT2 vb2];
             simpl in Hanim; try (injection Hanim as <-; apply Hf).
        all: destruct (isValueFn sv) eqn:Hsv; simpl in Hanim; injection Hanim as <-.
        all: try apply Hf.
        all: eapply E_PredSucc; split; [exact Hsv | apply (IH (S k)); [lia | exact Hps]].
      * (* rh = NoMatch: _ => check rl *)
        destruct rl as [| v2 |] eqn:Hps; simpl in Hanim;
          try (injection Hanim as <-; apply Hf).
        destruct v2 as [vs | vx vT1 vb1 | va1 va2 | | sv | vp | vd vt1 vt2 | vf vT2 vb2];
          simpl in Hanim; try (injection Hanim as <-; apply Hf).
        destruct (isValueFn sv) eqn:Hsv; simpl in Hanim; injection Hanim as <-.
        -- eapply E_PredSucc. split; [exact Hsv | apply (IH (S k)); [lia | exact Hps]].
        -- apply Hf.

  (* tifz: fires at n ≥ 9 *)
  - destruct n' as [|[|[|[|[|[|[|[|k]]]]]]]].
    + rewrite anim_1_oracle_f in Hanim. injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tifz 2 tdisc t1 t2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tifz 3 tdisc t1 t2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tifz 4 tdisc t1 t2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tifz 5 tdisc t1 t2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tifz 6 tdisc t1 t2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tifz 7 tdisc t1 t2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tifz 8 tdisc t1 t2 f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite anim_S_tifz in Hanim.
      set (rh := evalTransparentSigma2AnimatedTopFn (S (S k)) (Success tm tdisc) f) in Hanim.
      set (rl := evalTransparentSigma2AnimatedTopFn (S k) (Success tm tdisc) f) in Hanim.
      destruct rh as [| dv |] eqn:Hd; simpl in Hanim.
      * (* rh = FuelError: _ => check rl *)
        destruct rl as [| v2 |] eqn:Hd2; simpl in Hanim;
          try (injection Hanim as <-; apply Hf).
        destruct v2 as [vs | vx vT1 vb1 | va1 va2 | | svn | vp | vid vt1 vt2 | vf vT2 vb2];
          simpl in Hanim; try (injection Hanim as <-; apply Hf).
        destruct (isValueFn svn) eqn:Hsvn; simpl in Hanim;
          try (injection Hanim as <-; apply Hf).
        set (rt2 := evalTransparentSigma2AnimatedTopFn (S k) (Success tm t2) f) in Hanim.
        destruct rt2 as [| r |] eqn:Ht2; simpl in Hanim; try discriminate.
        injection Hanim as <-.
        eapply E_IfzSucc. repeat split.
        -- exact Hsvn.
        -- apply (IH (S k)). lia. exact Hd2.
        -- apply (IH (S k)). lia. exact Ht2.
      * (* rh = Success dv: close tzero (4th ctor) via try; others need rl check *)
        destruct dv as [ds | dx dT1 db1 | da1 da2 | | dsn | dp | did dt1 dt2 | df dT2 db2];
          simpl in Hanim.
        all: try (eapply E_IfzZero; split;
                  [apply (IH (S (S k))); [lia | exact Hd] |
                   apply (IH (S (S k))); [lia | exact Hanim]]).
        all: destruct rl as [| v2 |] eqn:Hd2; simpl in Hanim;
             try (injection Hanim as <-; apply Hf).
        all: destruct v2 as [vs | vx vT1 vb1 | va1 va2 | | svn | vp | vid vt1 vt2 | vf vT2 vb2];
             simpl in Hanim; try (injection Hanim as <-; apply Hf).
        all: destruct (isValueFn svn) eqn:Hsvn; simpl in Hanim;
             try (injection Hanim as <-; apply Hf).
        all: set (rt2 := evalTransparentSigma2AnimatedTopFn (S k) (Success tm t2) f) in Hanim.
        all: destruct rt2 as [| r |] eqn:Ht2; simpl in Hanim; try discriminate.
        all: injection Hanim as <-.
        all: eapply E_IfzSucc; repeat split;
             [exact Hsvn |
              apply (IH (S k)); [lia | exact Hd2] |
              apply (IH (S k)); [lia | exact Ht2]].
      * (* rh = NoMatch: _ => check rl (same as FuelError) *)
        destruct rl as [| v2 |] eqn:Hd2; simpl in Hanim;
          try (injection Hanim as <-; apply Hf).
        destruct v2 as [vs | vx vT1 vb1 | va1 va2 | | svn | vp | vid vt1 vt2 | vf vT2 vb2];
          simpl in Hanim; try (injection Hanim as <-; apply Hf).
        destruct (isValueFn svn) eqn:Hsvn; simpl in Hanim;
          try (injection Hanim as <-; apply Hf).
        set (rt2 := evalTransparentSigma2AnimatedTopFn (S k) (Success tm t2) f) in Hanim.
        destruct rt2 as [| r |] eqn:Ht2; simpl in Hanim; try discriminate.
        injection Hanim as <-.
        eapply E_IfzSucc. repeat split.
        -- exact Hsvn.
        -- apply (IH (S k)). lia. exact Hd2.
        -- apply (IH (S k)). lia. exact Ht2.

  (* tfix: E_Fix fires at n ≥ 10 *)
  - destruct n' as [|[|[|[|[|[|[|[|[|k]]]]]]]]].
    + rewrite anim_1_oracle_f in Hanim. injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tfix 2 fn T fbody f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tfix 3 fn T fbody f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tfix 4 fn T fbody f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tfix 5 fn T fbody f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tfix 6 fn T fbody f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tfix 7 fn T fbody f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tfix 8 fn T fbody f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite (anim_below_thr_tfix 9 fn T fbody f ltac:(lia)) in Hanim.
      injection Hanim as <-. apply Hf.
    + rewrite anim_S_tfix in Hanim.
      eapply E_Fix.
      apply (IH (S k)). lia. exact Hanim.
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













