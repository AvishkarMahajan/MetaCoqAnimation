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
| E_IfzSucc : forall t vn t1 t2 t4,
     eval t (tsucc vn) /\ eval t2 t4 ->
    eval (tifz t t1 t2) t4

(** Fixpoint: unroll once, then evaluate the substituted body. *)
| E_Fix : forall f T t v,
    eval (subst f (tfix f T t) t) v ->
    eval (tfix f T t) v.

MetaRocq Run (animate_coinductive_with_fn_pos <?eval?> [("eval", ([0], [1]))] 500).


(* ------------------------------------------------------------------ *)
(** ** Helper: PCF numeral [num n] = succ^n zero                      *)
(* ------------------------------------------------------------------ *)


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
    bigstop t1 v1 /\ bigstop t2 t2' ->
    bigstop (tapp t1 t2) (tapp v1 t2')

(** -- Progressing rules (St-CaseZ / St-CaseS / St-App analogues) --- *)

(** St-PredZero: discriminant big-stops to zero. *)
| BS_PredZero : forall e,
    bigstop e tzero ->
    bigstop (tpred e) tzero

(** St-PredSucc: discriminant big-stops to succ v (v a value). *)
| BS_PredSucc : forall e v,
    bigstop e (tsucc v) ->
    bigstop (tpred e) v

(** St-IfzZero: discriminant big-stops to zero; then big-stop the zero branch. *)
| BS_IfzZero : forall e t1 t1' t2,
    bigstop e tzero /\ bigstop t1 t1' ->
    bigstop (tifz e t1 t2) t1'

(** St-IfzSucc: discriminant big-stops to succ vn; big-stop the succ branch.
    (vn is the predecessor; our ifz has no binding for it in the succ branch.) *)
| BS_IfzSucc : forall e vn t1 t2 t2',
    bigstop e (tsucc vn) /\ bigstop t2 t2' ->
    bigstop (tifz e t1 t2) t2'

(** St-App: operator big-stops to a lambda, operand to a value, body big-stopped. *)
| BS_App : forall t1 x T t3 t2 v2 e',
    bigstop t1 (tabs x T t3) /\ bigstop t2 v2 /\
    bigstop (subst x v2 t3) e' ->
    bigstop (tapp t1 t2) e'

(** St-Fix: unroll the fixpoint once, then big-stop the substituted body. *)
| BS_Fix : forall f T t e',
    bigstop (subst f (tfix f T t) t) e' ->
    bigstop (tfix f T t) e'.


(* ------------------------------------------------------------------ *)
(** ** Full beta reduction                                             *)
(*                                                                     *)
(*  Non-deterministic: reduction may occur anywhere in the term,      *)
(*  including under binders, and the beta/delta redexes are not       *)
(*  restricted to value arguments/discriminants.                      *)
(* ------------------------------------------------------------------ *)

Inductive step : tm -> tm -> Prop :=

(** -- Redexes, unrestricted (no value-guards) ----------------------- *)

| FB_AppAbs : forall x T t s,
    step (tapp (tabs x T t) s) (subst x s t)

| FB_PredZero :
    step (tpred tzero) tzero

| FB_PredSucc : forall t,
    step (tpred (tsucc t)) t

| FB_IfzZero : forall t1 t2,
    step (tifz tzero t1 t2) t1

| FB_IfzSucc : forall t t1 t2,
    step (tifz (tsucc t) t1 t2) t2

| FB_Fix : forall f T t,
    step (tfix f T t) (subst f (tfix f T t) t)

(** -- Congruence rules: reduction may occur anywhere, including      *)
(**    inside binders.                                                 *)

| FB_Abs : forall x T t t',
    step t t' ->
    step (tabs x T t) (tabs x T t')

| FB_App1 : forall t1 t1' t2,
    step t1 t1' ->
    step (tapp t1 t2) (tapp t1' t2)

| FB_App2 : forall t1 t2 t2',
    step t2 t2' ->
    step (tapp t1 t2) (tapp t1 t2')

| FB_Succ : forall t t',
    step t t' ->
    step (tsucc t) (tsucc t')

| FB_Pred : forall t t',
    step t t' ->
    step (tpred t) (tpred t')

| FB_IfzDisc : forall t t' t1 t2,
    step t t' ->
    step (tifz t t1 t2) (tifz t' t1 t2)

| FB_IfzThen : forall t t1 t1' t2,
    step t1 t1' ->
    step (tifz t t1 t2) (tifz t t1' t2)

| FB_IfzElse : forall t t1 t2 t2',
    step t2 t2' ->
    step (tifz t t1 t2) (tifz t t1 t2')

| FB_FixBody : forall f T t t',
    step t t' ->
    step (tfix f T t) (tfix f T t').

(* ------------------------------------------------------------------ *)
(** ** Transitive (non-reflexive) closure of full beta reduction      *)
(* ------------------------------------------------------------------ *)

Inductive stepTC : tm -> tm -> Prop :=
| TC_step : forall t t',
    step t t' ->
    stepTC t t'
| TC_trans : forall t t' t'',
    step t t' ->
    stepTC t' t'' ->
    stepTC t t''.








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

    CORRECTED: an earlier version of this lemma checked the shape of the discriminant's
    evaluation AFTER pushing it through the oracle [f] (i.e. [match ... tmTransparentSigmaPushBody
    f x ... with Success tzero => ...]).  That is unsound for arbitrary [f]: if the discriminant's
    evaluation does not complete within the given fuel, the raw [tm'] result is an
    [evalremoveFnPosAn1]-wrapped residual — not [tzero'] or [tsucc' _] — so neither
    [E_PredZero] nor [E_PredSucc] actually fires, regardless of what pushing that residual
    through an adversarial [f] happens to look like.  Concretely, with [t := tapp id_nat tzero]
    (needs >= 7 fuel) and [f] mapping any [tapp]-shaped term to [tzero], the old statement's RHS
    computed [tzero] while the real dispatch computed [tsucc tzero].  The fix: check the shape of
    the RAW (unpushed) [tm'] result directly — this is what [E_PredZero]/[E_PredSucc] actually
    look at — and only push through [f] once a shape decision has already been made. *)
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
  match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t)) with
  | Success tzero' => Success tm tzero
  | _ =>
      match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
      | Success (tsucc' v') =>
          if andb (tmChkNoExtraCstrs v') (isValueFn (tmPushPlain v'))
          then Success tm (tmTransparentSigmaPushBody f v')
          else Success tm (f (tpred t))
      | _ => Success tm (f (tpred t))
      end
  end.
Proof.
  intros n t f.
  (* Spec lemma for E_PredZero's own reduction, generic in evalFn (same style as
     E_Succ_result): unfold every combinator by name, then let simpl fire every
     structural match on the concrete input/fuel, leaving evalFn's call as a residual. *)
  assert (E_PredZero_result :
    forall (evalFn : nat -> animation_result tm' -> animation_result tm') m v,
    E_PredZeroremoveFnPos'Animated evalFn (S m) (Success tm' (tpred' v)) =
    match evalFn (S m) (Success tm' v) with
    | Success tzero' => Success tm' tzero'
    | Success _ => NoMatch tm'
    | FuelError => FuelError tm'
    | NoMatch => NoMatch tm'
    end).
  { clear. intros evalFn m v.
    unfold E_PredZeroremoveFnPos'Animated, AnimationResult.compose_outcome,
           AnimationResult.option_to_result, AnimationResult.join_pair,
           TermUtils.with_default, TermUtils.dispatch_clauses,
           AnimationResult.fuel_error_fn.
    simpl.
    destruct (evalFn (S m) (Success tm' v)) as [| w |] eqn:E.
    - reflexivity.
    - destruct w; reflexivity.
    - reflexivity. }
  (* Spec lemma for E_PredSucc's own reduction. The isValueFn check is decided by
     isValueFnliftedFunc: definite (via tmChkNoExtraCstrs + isValueFn/tmPushPlain) when the
     predecessor carries no oracle marker, deferred (hence NoMatch overall) otherwise. *)
  assert (E_PredSucc_result :
    forall (evalFn : nat -> animation_result tm' -> animation_result tm') m v,
    E_PredSuccremoveFnPos'Animated evalFn (S m) (Success tm' (tpred' v)) =
    match evalFn (S m) (Success tm' v) with
    | Success (tsucc' v') =>
        if andb (tmChkNoExtraCstrs v') (isValueFn (tmPushPlain v'))
        then Success tm' v'
        else NoMatch tm'
    | Success _ => NoMatch tm'
    | FuelError => FuelError tm'
    | NoMatch => NoMatch tm'
    end).
  { clear. intros evalFn m v.
    unfold E_PredSuccremoveFnPos'Animated, AnimationResult.compose_outcome,
           AnimationResult.option_to_result, AnimationResult.join_pair,
           TermUtils.with_default, TermUtils.dispatch_clauses,
           AnimationResult.fuel_error_fn, isValueFnliftedFunc.
    simpl.
    destruct (evalFn (S m) (Success tm' v)) as [| w |] eqn:E.
    - reflexivity.
    - destruct w; simpl; try reflexivity.
      destruct (tmChkNoExtraCstrs w); simpl.
      + destruct (isValueFn (tmPushPlain w)); reflexivity.
      + reflexivity.
    - reflexivity. }
  (* If neither E_PredZero nor E_PredSucc fires, every remaining handler
     (E_App/E_IfzZero/E_IfzSucc/E_Fix) also fails to match a [tpred'] input, so the
     whole dispatch bottoms out at UndefinedAnimated's oracle escape — which, pushed,
     is exactly [f (tpred t)] (the escape wraps the ORIGINAL [tpred' (tmLift t)] input,
     and pushing a marker-free lift always round-trips to the original term). *)
  assert (Hfall : forall m,
    (match dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        m (Success tm' (tpred' (tmLift t))) with
     | Success x => Success tm (tmTransparentSigmaPushBody f x)
     | _ => NoMatch tm
     end) = Success tm (f (tpred t))).
  { intro m.
    assert (Hraw :
      dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        m (Success tm' (tpred' (tmLift t))) = Success tm' (evalremoveFnPosAn1 (tpred' (tmLift t)))).
    { clear. destruct m.
      - simpl. reflexivity.
      - unfold dispatch_coind_ext.
        assert (HA : E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S m) (Success tm' (tpred' (tmLift t))) = NoMatch tm')
          by (unfold E_AppremoveFnPos'Animated, option_to_result; reflexivity).
        rewrite HA. destruct m.
        + simpl. reflexivity.
        + unfold dispatch_coind_ext.
          assert (HIZ : E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S m) (Success tm' (tpred' (tmLift t))) = NoMatch tm')
            by (unfold E_IfzZeroremoveFnPos'Animated, option_to_result; reflexivity).
          rewrite HIZ. destruct m.
          * simpl. reflexivity.
          * unfold dispatch_coind_ext.
            assert (HIS : E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S m) (Success tm' (tpred' (tmLift t))) = NoMatch tm')
              by (unfold E_IfzSuccremoveFnPos'Animated, option_to_result; reflexivity).
            rewrite HIS. destruct m.
            -- simpl. reflexivity.
            -- unfold dispatch_coind_ext.
               assert (HF : E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S m) (Success tm' (tpred' (tmLift t))) = NoMatch tm')
                 by (unfold E_FixremoveFnPos'Animated, option_to_result; reflexivity).
               rewrite HF. destruct m.
               ++ simpl. reflexivity.
               ++ unfold dispatch_coind_ext.
                  assert (HU : Success tm' (evalremoveFnPosAn1 (tpred' (tmLift t))) = evalremoveFnPos'UndefinedAnimated (S m) (Success tm' (tpred' (tmLift t))))
                    by (simpl; reflexivity).
                  rewrite <- HU. reflexivity. }
    rewrite Hraw. simpl.
    rewrite tmTransparentSigmaPushBody_tmLift. reflexivity. }
  cbn [dispatch_coind_ext].
  rewrite (E_PredZero_result evalremoveFnPos'AnimatedTopFn (S n) (tmLift t)).
  destruct (evalremoveFnPos'AnimatedTopFn_always_success (S (S n)) (tmLift t)) as [w1 Hw1].
  rewrite Hw1.
  assert (Hcont :
    (match dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        (S n) (Success tm' (tpred' (tmLift t))) with
     | Success x => Success tm (tmTransparentSigmaPushBody f x)
     | _ => NoMatch tm
     end) =
    match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
    | Success (tsucc' v') =>
        if andb (tmChkNoExtraCstrs v') (isValueFn (tmPushPlain v'))
        then Success tm (tmTransparentSigmaPushBody f v')
        else Success tm (f (tpred t))
    | _ => Success tm (f (tpred t))
    end).
  { cbn [dispatch_coind_ext].
    rewrite (E_PredSucc_result evalremoveFnPos'AnimatedTopFn n (tmLift t)).
    destruct (evalremoveFnPos'AnimatedTopFn_always_success (S n) (tmLift t)) as [w2 Hw2].
    rewrite Hw2.
    destruct w2 as [s1|s2 ty2 b2|a1 a2| |v2|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
      simpl; try (apply Hfall).
    destruct (andb (tmChkNoExtraCstrs v2) (isValueFn (tmPushPlain v2))) eqn:Hchk.
    - simpl. reflexivity.
    - apply Hfall.
  }
  destruct w1; simpl; try apply Hcont.
  reflexivity.
Qed.

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
  match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t)) with
  | Success tzero' => Success tm tzero
  | _ =>
      match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
      | Success (tsucc' v') =>
          if andb (tmChkNoExtraCstrs v') (isValueFn (tmPushPlain v'))
          then Success tm (tmTransparentSigmaPushBody f v')
          else Success tm (f (tpred t))
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

(** CORRECTED (see [dispatch_tpred_from_pred]): the shape decision (is the discriminant
    zero? a successor of a value?) is made on the raw [tm'] result of
    [evalremoveFnPos'AnimatedTopFn], before any push through the oracle [f]. *)
Lemma anim_S_tpred : forall n t f,
  evalTransparentSigma2AnimatedTopFn (S (S (S (S (S (S n)))))) (Success tm (tpred t)) f =
  match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t)) with
  | Success tzero' => Success tm tzero
  | _ =>
      match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
      | Success (tsucc' v') =>
          if andb (tmChkNoExtraCstrs v') (isValueFn (tmPushPlain v'))
          then Success tm (tmTransparentSigmaPushBody f v')
          else Success tm (f (tpred t))
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
    CORRECTED (same issue as [dispatch_tpred_from_pred]): the discriminant's shape
    (tzero'/tsucc') must be decided on the RAW tm' result, before pushing through the
    oracle — pushing first and comparing to tm-level [tzero]/[tsucc _] is unsound for
    adversarial [f], by the same counterexample construction as for tpred/tapp
    (discriminant that doesn't finish evaluating, pushed through an [f] that makes the
    escaped residual coincidentally look like the wrong shape).  The t1/t2 branch
    evaluations themselves are fine to leave push-first, since nothing further branches
    on their shape — they're just returned opaquely, exactly as with tsucc.
    STILL ADMITTED pending the same [always_value]-style gap as before (the isValueFn
    check on the extracted predecessor needs to know it is marker-free), tracked
    separately; the statement below is the corrected target. *)
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
  match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t)) with
  | Success tzero' =>
      (match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t1)) with
       | Success x => Success tm (tmTransparentSigmaPushBody f x)
       | _ => NoMatch tm
       end)
  | _ =>
      match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
      | Success (tsucc' vn') =>
          if andb (tmChkNoExtraCstrs vn') (isValueFn (tmPushPlain vn'))
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
  (* Spec lemma for E_IfzZero's own reduction (sequential: only checks the zero-branch
     once the discriminant is known to be tzero'). *)
  assert (E_IfzZero_result :
    forall (evalFn : nat -> animation_result tm' -> animation_result tm') m u1 u2 u3,
    E_IfzZeroremoveFnPos'Animated evalFn (S m) (Success tm' (tifz' u1 u2 u3)) =
    match evalFn (S m) (Success tm' u1) with
    | Success tzero' => evalFn (S m) (Success tm' u2)
    | Success _ => NoMatch tm'
    | FuelError => FuelError tm'
    | NoMatch => NoMatch tm'
    end).
  { clear. intros evalFn m u1 u2 u3.
    unfold E_IfzZeroremoveFnPos'Animated, AnimationResult.compose_outcome,
           AnimationResult.option_to_result, AnimationResult.join_pair,
           TermUtils.with_default, TermUtils.dispatch_clauses,
           AnimationResult.fuel_error_fn.
    simpl.
    destruct (evalFn (S m) (Success tm' u1)) as [| w |] eqn:E; simpl.
    - reflexivity.
    - destruct w; simpl; try reflexivity.
      destruct (evalFn (S m) (Success tm' u2)) as [| res |]; reflexivity.
    - reflexivity. }
  (* Spec lemma for E_IfzSucc's own reduction, SPECIALIZED to the case where both the
     discriminant and the succ-continuation are already known to succeed (always true for
     [evalremoveFnPos'AnimatedTopFn] via [evalremoveFnPos'AnimatedTopFn_always_success]).
     The raw generated code actually checks the succ-continuation's status before the
     discriminant's (an asymmetry from how E_IfzZero is generated), which only matters when
     either could genuinely be FuelError/NoMatch; since neither ever is here, this
     specialized statement is all that's needed. *)
  assert (E_IfzSucc_result_spec :
    forall (evalFn : nat -> animation_result tm' -> animation_result tm') m u1 u2 u3 w1 w3,
    evalFn (S m) (Success tm' u1) = Success tm' w1 ->
    evalFn (S m) (Success tm' u3) = Success tm' w3 ->
    E_IfzSuccremoveFnPos'Animated evalFn (S m) (Success tm' (tifz' u1 u2 u3)) =
    match w1 with
    | tsucc' vn' =>
        if andb (tmChkNoExtraCstrs vn') (isValueFn (tmPushPlain vn'))
        then Success tm' w3
        else NoMatch tm'
    | _ => NoMatch tm'
    end).
  { clear. intros evalFn m u1 u2 u3 w1 w3 H1 H3.
    unfold E_IfzSuccremoveFnPos'Animated, AnimationResult.compose_outcome,
           AnimationResult.option_to_result, AnimationResult.join_pair,
           TermUtils.with_default, TermUtils.dispatch_clauses,
           AnimationResult.fuel_error_fn, isValueFnliftedFunc.
    simpl.
    rewrite H1, H3.
    destruct w1 as [s1|s2 ty2 b2|a1 a2| |vn'|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
      simpl; try reflexivity.
    destruct (tmChkNoExtraCstrs vn'); simpl.
    - destruct (isValueFn (tmPushPlain vn')); reflexivity.
    - reflexivity. }
  (* If neither E_IfzZero nor E_IfzSucc matches, E_Fix + UndefinedAnimated bottom out at
     the oracle escape, exactly as in [dispatch_tpred_from_pred]'s [Hfall]. *)
  assert (Hfall : forall m,
    (match dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        m (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))) with
     | Success x => Success tm (tmTransparentSigmaPushBody f x)
     | _ => NoMatch tm
     end) = Success tm (f (tifz t t1 t2))).
  { clear E_IfzZero_result E_IfzSucc_result_spec. intro m.
    assert (Hraw :
      dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        m (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2)))
      = Success tm' (evalremoveFnPosAn1 (tifz' (tmLift t) (tmLift t1) (tmLift t2)))).
    { clear. destruct m.
      - simpl. reflexivity.
      - unfold dispatch_coind_ext.
        assert (HF : E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S m)
                       (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))) = NoMatch tm')
          by (unfold E_FixremoveFnPos'Animated, option_to_result; reflexivity).
        rewrite HF. destruct m.
        + simpl. reflexivity.
        + unfold dispatch_coind_ext.
          assert (HU : Success tm' (evalremoveFnPosAn1 (tifz' (tmLift t) (tmLift t1) (tmLift t2)))
                       = evalremoveFnPos'UndefinedAnimated (S m)
                           (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))))
            by (simpl; reflexivity).
          rewrite <- HU. reflexivity. }
    rewrite Hraw. simpl.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity. }
  cbn [dispatch_coind_ext].
  rewrite (E_IfzZero_result evalremoveFnPos'AnimatedTopFn (S n) (tmLift t) (tmLift t1) (tmLift t2)).
  destruct (evalremoveFnPos'AnimatedTopFn_always_success (S (S n)) (tmLift t)) as [w1 Hw1].
  rewrite Hw1.
  assert (Hcont :
    (match dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        (S n) (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))) with
     | Success x => Success tm (tmTransparentSigmaPushBody f x)
     | _ => NoMatch tm
     end) =
    match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
    | Success (tsucc' vn') =>
        if andb (tmChkNoExtraCstrs vn') (isValueFn (tmPushPlain vn'))
        then (match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t2)) with
              | Success x => Success tm (tmTransparentSigmaPushBody f x)
              | _ => NoMatch tm
              end)
        else Success tm (f (tifz t t1 t2))
    | _ => Success tm (f (tifz t t1 t2))
    end).
  { cbn [dispatch_coind_ext].
    destruct (evalremoveFnPos'AnimatedTopFn_always_success (S n) (tmLift t)) as [w2 Hw2].
    destruct (evalremoveFnPos'AnimatedTopFn_always_success (S n) (tmLift t2)) as [w3 Hw3].
    rewrite (E_IfzSucc_result_spec evalremoveFnPos'AnimatedTopFn n (tmLift t) (tmLift t1) (tmLift t2) w2 w3 Hw2 Hw3).
    rewrite Hw2, Hw3.
    destruct w2 as [s1|s2 ty2 b2|a1 a2| |v2|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
      simpl; try (apply Hfall).
    destruct (andb (tmChkNoExtraCstrs v2) (isValueFn (tmPushPlain v2))) eqn:Hchk.
    - simpl. reflexivity.
    - apply Hfall.
  }
  destruct w1 as [s1|s2 ty2 b2|a1 a2| |v1|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
    [ simpl; apply Hcont
    | simpl; apply Hcont
    | simpl; apply Hcont
    | destruct (evalremoveFnPos'AnimatedTopFn_always_success (S (S n)) (tmLift t1)) as [w1' Hw1'];
      rewrite Hw1'; reflexivity
    | simpl; apply Hcont
    | simpl; apply Hcont
    | simpl; apply Hcont
    | simpl; apply Hcont
    | simpl; apply Hcont
    | simpl; apply Hcont ].
Qed.

Lemma dispatch_tifz : forall n t t1 t2 f,
  (match evalremoveFnPos'AnimatedTopFn
     (S (S (S (S (S (S (S (S (S n))))))))) (Success tm' (tifz' (tmLift t) (tmLift t1) (tmLift t2))) with
   | Success x => Success tm (tmTransparentSigmaPushBody f x)
   | _ => NoMatch tm
   end)
  =
  match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t)) with
  | Success tzero' =>
      (match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t1)) with
       | Success x => Success tm (tmTransparentSigmaPushBody f x)
       | _ => NoMatch tm
       end)
  | _ =>
      match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
      | Success (tsucc' vn') =>
          if andb (tmChkNoExtraCstrs vn') (isValueFn (tmPushPlain vn'))
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

(** CORRECTED (see [dispatch_tifz_from_ifz]): the discriminant's shape is decided on the
    raw [tm'] result of [evalremoveFnPos'AnimatedTopFn], before any push through [f]. *)
Lemma anim_S_tifz : forall n t t1 t2 f,
  evalTransparentSigma2AnimatedTopFn
    (S (S (S (S (S (S (S (S (S n))))))))) (Success tm (tifz t t1 t2)) f =
  match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t)) with
  | Success tzero' =>
      match evalremoveFnPos'AnimatedTopFn (S (S n)) (Success tm' (tmLift t1)) with
      | Success x => Success tm (tmTransparentSigmaPushBody f x)
      | _ => NoMatch tm
      end
  | _ =>
      match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t)) with
      | Success (tsucc' vn') =>
          if andb (tmChkNoExtraCstrs vn') (isValueFn (tmPushPlain vn'))
          then match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t2)) with
               | Success x => Success tm (tmTransparentSigmaPushBody f x)
               | _ => NoMatch tm
               end
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
    CORRECTED (same issue as [dispatch_tpred_from_pred]): [t1]'s shape (is it a lambda?)
    and [v2]'s value-ness must be decided on the RAW [tm'] results, before pushing
    through [f] — see the comment there for why push-then-compare is unsound.  Unlike
    tpred/tifz, tapp additionally REUSES the extracted lambda body [t3'] inside a further
    substitution+recursive-evaluation step; the statement below states the INTENDED
    target directly in terms of genuine PCF substitution ([subst x (tmPushPlain v2')
    (tmPushPlain t3')]), which is only justified once [t3'] is known to carry no oracle
    marker — an extra fact beyond [always_success]/[always_value] for tzero'/tsucc'
    shapes, since here a SUB-PIECE of a Success result must itself be marker-free, not
    just the whole result.  STILL ADMITTED pending that fact; tracked separately. *)
(** Extra gap specific to tapp, beyond [dispatch_tapp_from_app] itself: whenever
    evaluating [t1] yields a lambda value, ITS BODY must carry no oracle-escape marker
    for the substitution step used by [dispatch_tapp_from_app]/[anim_S_tapp] (and by
    the tapp branches of the two main correspondence theorems, which reuse the extracted
    body inside a further recursive evaluation) to line up with genuine PCF substitution.
    Proved by strong induction on the fuel, generalized to an arbitrary marker-free tm'
    input (not just [tmLift t1] specifically) so that every handler's own recursive
    sub-evaluation — which always operates on either a structural subterm of a marker-free
    input or a substitution re-wrapped via [tmLift]/[substliftedFunc] once its own pieces
    are known marker-free by the very same induction — falls back into IH's scope. The
    helper infrastructure below ([dispatch_coind_ext_escape]/[_skip]/[_fire]/[_reach] and
    the per-handler "_result" specs) mirrors the pattern established in
    [dispatch_tpred_from_pred]/[dispatch_tifz_from_ifz], generalized to handle: (a) cases
    where fuel may run out before a given handler is even reached ([_reach]/[_escape]
    return that possibility explicitly rather than assuming enough fuel survived), and
    (b) [E_App]/[E_Fix]'s handlers, which were not needed by the tpred/tifz proofs. *)

Lemma tmChkNoExtraCstrs_tmLift : forall t, tmChkNoExtraCstrs (tmLift t) = true.
Proof.
  induction t; simpl; try reflexivity; try (rewrite IHt; reflexivity);
  try (rewrite IHt1, IHt2; reflexivity);
  try (rewrite IHt1, IHt2, IHt3; reflexivity).
Qed.

Lemma tmPushPlain_tmLift : forall t, tmPushPlain (tmLift t) = t.
Proof.
  induction t; simpl; try reflexivity; try (rewrite IHt; reflexivity);
  try (rewrite IHt1, IHt2; reflexivity);
  try (rewrite IHt1, IHt2, IHt3; reflexivity).
Qed.

Lemma substliftedFunc_no_extra_cstrs : forall s A B,
  tmChkNoExtraCstrs A = true -> tmChkNoExtraCstrs B = true ->
  tmChkNoExtraCstrs (substliftedFunc s A B) = true.
Proof.
  intros s A B HA HB.
  unfold substliftedFunc.
  rewrite HA, HB. simpl.
  apply tmChkNoExtraCstrs_tmLift.
Qed.

Lemma dispatch_coind_ext_escape :
  forall (prefix : list (nat -> animation_result tm' -> animation_result tm')) (u : tm'),
  (forall h k, In h prefix -> h (S k) (Success tm' u) = NoMatch tm') ->
  forall m, dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
              (prefix ++ [evalremoveFnPos'UndefinedAnimated]) m (Success tm' u) =
            Success tm' (evalremoveFnPosAn1 u).
Proof.
  induction prefix as [| h rest IHrest]; intros u Hall m.
  - simpl. destruct m.
    + simpl. reflexivity.
    + unfold dispatch_coind_ext.
      assert (HU : evalremoveFnPos'UndefinedAnimated (S m) (Success tm' u) = Success tm' (evalremoveFnPosAn1 u))
        by (simpl; reflexivity).
      rewrite HU. reflexivity.
  - destruct m.
    + simpl. reflexivity.
    + assert (Hh : h (S m) (Success tm' u) = NoMatch tm')
        by (apply Hall; left; reflexivity).
      change (h :: rest ++ [evalremoveFnPos'UndefinedAnimated])
        with ((h :: rest) ++ [evalremoveFnPos'UndefinedAnimated]).
      cbn [dispatch_coind_ext app].
      rewrite Hh.
      apply IHrest.
      intros h' k Hin. apply Hall. right. exact Hin.
Qed.

Lemma base_result : forall x,
  evalremoveFnPos'AnimatedTopFn 0 (Success tm' x) = Success tm' (evalremoveFnPosAn1 x).
Proof.
  intro x. unfold evalremoveFnPos'AnimatedTopFn. simpl. reflexivity.
Qed.

Lemma E_Lam_result :
  forall n t1', E_LamremoveFnPos'Animated (S n) (Success tm' t1') =
  match t1' with
  | tabs' _ _ _ => Success tm' t1'
  | _ => NoMatch tm'
  end.
Proof.
  intros n t1'.
  unfold E_LamremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn.
  simpl.
  destruct t1'; reflexivity.
Qed.

Lemma E_Zero_result :
  forall n t1', E_ZeroremoveFnPos'Animated (S n) (Success tm' t1') =
  match t1' with
  | tzero' => Success tm' tzero'
  | _ => NoMatch tm'
  end.
Proof.
  intros n t1'.
  unfold E_ZeroremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn.
  simpl.
  destruct t1'; reflexivity.
Qed.

Lemma E_Succ_result_generic :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n t1',
  E_SuccremoveFnPos'Animated evalFn (S n) (Success tm' t1') =
  match t1' with
  | tsucc' v =>
      match evalFn (S n) (Success tm' v) with
      | Success w => Success tm' (tsucc' w)
      | FuelError => FuelError tm'
      | NoMatch => NoMatch tm'
      end
  | _ => NoMatch tm'
  end.
Proof.
  intros evalFn n t1'.
  unfold E_SuccremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn.
  simpl.
  destruct t1'; try reflexivity.
  destruct (evalFn (S n) (Success tm' t1')) as [| w |]; reflexivity.
Qed.

Lemma E_Succ_result_generic_spec :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n v1 w,
  evalFn (S n) (Success tm' v1) = Success tm' w ->
  E_SuccremoveFnPos'Animated evalFn (S n) (Success tm' (tsucc' v1)) = Success tm' (tsucc' w).
Proof.
  intros evalFn n v1 w H.
  rewrite E_Succ_result_generic. rewrite H. reflexivity.
Qed.

Lemma E_PredZero_result :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n v,
  E_PredZeroremoveFnPos'Animated evalFn (S n) (Success tm' (tpred' v)) =
  match evalFn (S n) (Success tm' v) with
  | Success tzero' => Success tm' tzero'
  | Success _ => NoMatch tm'
  | FuelError => FuelError tm'
  | NoMatch => NoMatch tm'
  end.
Proof.
  intros evalFn n v.
  unfold E_PredZeroremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn.
  simpl.
  destruct (evalFn (S n) (Success tm' v)) as [| w |] eqn:E.
  - reflexivity.
  - destruct w; reflexivity.
  - reflexivity.
Qed.

Lemma E_PredZero_result_spec :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n v w,
  evalFn (S n) (Success tm' v) = Success tm' w ->
  E_PredZeroremoveFnPos'Animated evalFn (S n) (Success tm' (tpred' v)) =
  match w with
  | tzero' => Success tm' tzero'
  | _ => NoMatch tm'
  end.
Proof.
  intros evalFn n v w H. rewrite E_PredZero_result. rewrite H. reflexivity.
Qed.

Lemma E_PredZero_result_wrongshape :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n t1',
  (forall v, t1' <> tpred' v) ->
  E_PredZeroremoveFnPos'Animated evalFn (S n) (Success tm' t1') = NoMatch tm'.
Proof.
  intros evalFn n t1' Hne.
  unfold E_PredZeroremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn.
  simpl.
  destruct t1'; simpl; try reflexivity.
  exfalso. eapply Hne. reflexivity.
Qed.

Lemma E_PredSucc_result :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n v,
  E_PredSuccremoveFnPos'Animated evalFn (S n) (Success tm' (tpred' v)) =
  match evalFn (S n) (Success tm' v) with
  | Success (tsucc' v') =>
      if andb (tmChkNoExtraCstrs v') (isValueFn (tmPushPlain v'))
      then Success tm' v'
      else NoMatch tm'
  | Success _ => NoMatch tm'
  | FuelError => FuelError tm'
  | NoMatch => NoMatch tm'
  end.
Proof.
  intros evalFn n v.
  unfold E_PredSuccremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn, isValueFnliftedFunc.
  simpl.
  destruct (evalFn (S n) (Success tm' v)) as [| w |] eqn:E.
  - reflexivity.
  - destruct w; simpl; try reflexivity.
    destruct (tmChkNoExtraCstrs w); simpl.
    + destruct (isValueFn (tmPushPlain w)); reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma E_PredSucc_result_spec2 :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n v w,
  evalFn (S n) (Success tm' v) = Success tm' w ->
  E_PredSuccremoveFnPos'Animated evalFn (S n) (Success tm' (tpred' v)) =
  match w with
  | tsucc' v' =>
      if andb (tmChkNoExtraCstrs v') (isValueFn (tmPushPlain v'))
      then Success tm' v'
      else NoMatch tm'
  | _ => NoMatch tm'
  end.
Proof.
  intros evalFn n v w H. rewrite E_PredSucc_result. rewrite H. reflexivity.
Qed.

Lemma E_PredSucc_result_wrongshape :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n t1',
  (forall v, t1' <> tpred' v) ->
  E_PredSuccremoveFnPos'Animated evalFn (S n) (Success tm' t1') = NoMatch tm'.
Proof.
  intros evalFn n t1' Hne.
  unfold E_PredSuccremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn, isValueFnliftedFunc.
  simpl.
  destruct t1'; simpl; try reflexivity.
  exfalso. eapply Hne. reflexivity.
Qed.

Lemma E_App_result_spec :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm')
         n t1' t2' xx tty tt3 w2 w3,
  evalFn (S n) (Success tm' t1') = Success tm' (tabs' xx tty tt3) ->
  evalFn (S n) (Success tm' t2') = Success tm' w2 ->
  tmChkNoExtraCstrs w2 = true ->
  isValueFn (tmPushPlain w2) = true ->
  evalFn (S n) (Success tm' (substliftedFunc xx w2 tt3)) = Success tm' w3 ->
  E_AppremoveFnPos'Animated evalFn (S n) (Success tm' (tapp' t1' t2')) = Success tm' w3.
Proof.
  intros evalFn n t1' t2' xx tty tt3 w2 w3 H1 H2 Hchk Hval H3.
  unfold E_AppremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn, isValueFnliftedFunc.
  simpl.
  rewrite H1, H2, H3.
  simpl.
  rewrite Hchk, Hval.
  reflexivity.
Qed.

Lemma E_App_result_nomatch2 :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm')
         n t1' t2' xx tty tt3 w2 w3,
  evalFn (S n) (Success tm' t1') = Success tm' (tabs' xx tty tt3) ->
  evalFn (S n) (Success tm' t2') = Success tm' w2 ->
  evalFn (S n) (Success tm' (substliftedFunc xx w2 tt3)) = Success tm' w3 ->
  (tmChkNoExtraCstrs w2 = false \/ isValueFn (tmPushPlain w2) = false) ->
  E_AppremoveFnPos'Animated evalFn (S n) (Success tm' (tapp' t1' t2')) = NoMatch tm'.
Proof.
  intros evalFn n t1' t2' xx tty tt3 w2 w3 H1 H2 H3 [Hf | Hf].
  - unfold E_AppremoveFnPos'Animated, AnimationResult.compose_outcome,
           AnimationResult.option_to_result, AnimationResult.join_pair,
           TermUtils.with_default, TermUtils.dispatch_clauses,
           AnimationResult.fuel_error_fn, isValueFnliftedFunc.
    simpl.
    rewrite H1, H2, H3.
    simpl.
    rewrite Hf.
    reflexivity.
  - unfold E_AppremoveFnPos'Animated, AnimationResult.compose_outcome,
           AnimationResult.option_to_result, AnimationResult.join_pair,
           TermUtils.with_default, TermUtils.dispatch_clauses,
           AnimationResult.fuel_error_fn, isValueFnliftedFunc.
    simpl.
    rewrite H1, H2, H3.
    simpl.
    destruct (tmChkNoExtraCstrs w2) eqn:Hchk; simpl.
    + rewrite Hf. reflexivity.
    + reflexivity.
Qed.

Lemma E_App_result_nomatch1 :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm')
         n t1' t2' w1,
  evalFn (S n) (Success tm' t1') = Success tm' w1 ->
  (forall xx tty tt3, w1 <> tabs' xx tty tt3) ->
  E_AppremoveFnPos'Animated evalFn (S n) (Success tm' (tapp' t1' t2')) = NoMatch tm'.
Proof.
  intros evalFn n t1' t2' w1 H1 Hne.
  unfold E_AppremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn, isValueFnliftedFunc.
  simpl.
  rewrite H1.
  destruct w1; simpl; try reflexivity.
  exfalso. eapply Hne. reflexivity.
Qed.

Lemma E_App_result_wrongshape :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n t1',
  (forall a1 a2, t1' <> tapp' a1 a2) ->
  E_AppremoveFnPos'Animated evalFn (S n) (Success tm' t1') = NoMatch tm'.
Proof.
  intros evalFn n t1' Hne.
  unfold E_AppremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn, isValueFnliftedFunc.
  simpl.
  destruct t1'; simpl; try reflexivity.
  exfalso. eapply Hne. reflexivity.
Qed.

Lemma E_IfzZero_result :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') m u1 u2 u3,
  E_IfzZeroremoveFnPos'Animated evalFn (S m) (Success tm' (tifz' u1 u2 u3)) =
  match evalFn (S m) (Success tm' u1) with
  | Success tzero' => evalFn (S m) (Success tm' u2)
  | Success _ => NoMatch tm'
  | FuelError => FuelError tm'
  | NoMatch => NoMatch tm'
  end.
Proof.
  intros evalFn m u1 u2 u3.
  unfold E_IfzZeroremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn.
  simpl.
  destruct (evalFn (S m) (Success tm' u1)) as [| w |] eqn:E; simpl.
  - reflexivity.
  - destruct w; simpl; try reflexivity.
    destruct (evalFn (S m) (Success tm' u2)) as [| res |]; reflexivity.
  - reflexivity.
Qed.

Lemma E_IfzZero_result_wrongshape :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n t1',
  (forall c1 c2 c3, t1' <> tifz' c1 c2 c3) ->
  E_IfzZeroremoveFnPos'Animated evalFn (S n) (Success tm' t1') = NoMatch tm'.
Proof.
  intros evalFn n t1' Hne.
  unfold E_IfzZeroremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn.
  simpl.
  destruct t1'; simpl; try reflexivity.
  exfalso. eapply Hne. reflexivity.
Qed.

Lemma E_IfzZero_result_spec2 :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') m u1 u2 u3 w1 w2,
  evalFn (S m) (Success tm' u1) = Success tm' w1 ->
  evalFn (S m) (Success tm' u2) = Success tm' w2 ->
  E_IfzZeroremoveFnPos'Animated evalFn (S m) (Success tm' (tifz' u1 u2 u3)) =
  match w1 with
  | tzero' => Success tm' w2
  | _ => NoMatch tm'
  end.
Proof.
  intros evalFn m u1 u2 u3 w1 w2 H1 H2.
  rewrite E_IfzZero_result. rewrite H1.
  destruct w1; simpl; try reflexivity.
  rewrite H2. reflexivity.
Qed.

Lemma E_IfzSucc_result_spec :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') m u1 u2 u3 w1 w3,
  evalFn (S m) (Success tm' u1) = Success tm' w1 ->
  evalFn (S m) (Success tm' u3) = Success tm' w3 ->
  E_IfzSuccremoveFnPos'Animated evalFn (S m) (Success tm' (tifz' u1 u2 u3)) =
  match w1 with
  | tsucc' vn' =>
      if andb (tmChkNoExtraCstrs vn') (isValueFn (tmPushPlain vn'))
      then Success tm' w3
      else NoMatch tm'
  | _ => NoMatch tm'
  end.
Proof.
  intros evalFn m u1 u2 u3 w1 w3 H1 H3.
  unfold E_IfzSuccremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn, isValueFnliftedFunc.
  simpl.
  rewrite H1, H3.
  destruct w1 as [s1|s2 ty2 b2|a1 a2| |vn'|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
    simpl; try reflexivity.
  destruct (tmChkNoExtraCstrs vn'); simpl.
  - destruct (isValueFn (tmPushPlain vn')); reflexivity.
  - reflexivity.
Qed.

Lemma E_IfzSucc_result_wrongshape :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n t1',
  (forall c1 c2 c3, t1' <> tifz' c1 c2 c3) ->
  E_IfzSuccremoveFnPos'Animated evalFn (S n) (Success tm' t1') = NoMatch tm'.
Proof.
  intros evalFn n t1' Hne.
  unfold E_IfzSuccremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn, isValueFnliftedFunc.
  simpl.
  destruct t1'; simpl; try reflexivity.
  exfalso. eapply Hne. reflexivity.
Qed.

Lemma E_Fix_result_spec :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm')
         n fn T body w,
  evalFn (S n) (Success tm' (substliftedFunc fn (tfix' fn T body) body)) = Success tm' w ->
  E_FixremoveFnPos'Animated evalFn (S n) (Success tm' (tfix' fn T body)) = Success tm' w.
Proof.
  intros evalFn n fn T body w H.
  unfold E_FixremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma E_Fix_result_wrongshape :
  forall (evalFn : nat -> animation_result tm' -> animation_result tm') n u,
  (forall fn T body, u <> tfix' fn T body) ->
  E_FixremoveFnPos'Animated evalFn (S n) (Success tm' u) = NoMatch tm'.
Proof.
  intros evalFn n u Hne.
  unfold E_FixremoveFnPos'Animated, AnimationResult.compose_outcome,
         AnimationResult.option_to_result, AnimationResult.join_pair,
         TermUtils.with_default, TermUtils.dispatch_clauses,
         AnimationResult.fuel_error_fn.
  simpl.
  destruct u; simpl; try reflexivity.
  exfalso. eapply Hne. reflexivity.
Qed.

Lemma dispatch_coind_ext_skip :
  forall h rest (u : tm') m,
  h (S m) (Success tm' u) = NoMatch tm' ->
  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest (h::rest) (S m) (Success tm' u) =
  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest rest m (Success tm' u).
Proof.
  intros h rest u m Hh.
  cbn [dispatch_coind_ext]. rewrite Hh. reflexivity.
Qed.

Lemma dispatch_coind_ext_fire :
  forall h rest (u : tm') m w,
  h (S m) (Success tm' u) = Success tm' w ->
  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest (h::rest) (S m) (Success tm' u) = Success tm' w.
Proof.
  intros h rest u m w Hh.
  cbn [dispatch_coind_ext]. rewrite Hh. reflexivity.
Qed.

Lemma dispatch_coind_ext_reach :
  forall (prefix : list (nat -> animation_result tm' -> animation_result tm'))
         (tail : list (nat -> animation_result tm' -> animation_result tm')) (u : tm') m,
  (forall h k, In h prefix -> h (S k) (Success tm' u) = NoMatch tm') ->
  dispatch_coind_ext tm' tm' evalremoveFnPos'Rest (prefix++tail) m (Success tm' u) =
  Success tm' (evalremoveFnPosAn1 u) \/
  (exists k, k <= m /\ 
             dispatch_coind_ext tm' tm' evalremoveFnPos'Rest (prefix++tail) m (Success tm' u) =
             dispatch_coind_ext tm' tm' evalremoveFnPos'Rest tail k (Success tm' u)).
Proof.
  induction prefix as [| hh rr IHrest]; intros tail u m Hall.
  - right. exists m. split; [lia | reflexivity].
  - destruct m as [| m].
    + left. simpl. reflexivity.
    + assert (Hhh : hh (S m) (Success tm' u) = NoMatch tm')
        by (apply Hall; left; reflexivity).
      pose proof (dispatch_coind_ext_skip hh (List.app rr tail) u m Hhh) as Hstep.
      change (List.app (cons hh rr) tail) with (cons hh (List.app rr tail)).
      rewrite Hstep.
      destruct (IHrest tail u m ltac:(intros h' k Hin; apply Hall; right; exact Hin))
        as [Hesc | [k [Hkm Heqk]]].
      * left. exact Hesc.
      * right. exists k. split; [lia | exact Heqk].
Qed.




Ltac escape_app_ifz_fix u k H :=
  change
    [E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     evalremoveFnPos'UndefinedAnimated]
    with
    (List.app
      [E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
      [evalremoveFnPos'UndefinedAnimated]) in H;
  rewrite (dispatch_coind_ext_escape
    [E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
     E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
    u
    ltac:(intros hh kk Hin; simpl in Hin;
          repeat destruct Hin as [<- | Hin]; [ | | | | contradiction];
          [ apply E_App_result_wrongshape; intros aa1 aa2; discriminate
          | apply E_IfzZero_result_wrongshape; intros cc1 cc2 cc3; discriminate
          | apply E_IfzSucc_result_wrongshape; intros cc1 cc2 cc3; discriminate
          | apply E_Fix_result_wrongshape; intros ffn TT bb; discriminate ])
    k) in H;
  discriminate H.

Lemma E_App_lambda_body_no_extra_cstrs_general : forall n (u : tm') x ty t3',
  tmChkNoExtraCstrs u = true ->
  evalremoveFnPos'AnimatedTopFn n (Success tm' u) = Success tm' (tabs' x ty t3') ->
  tmChkNoExtraCstrs t3' = true.
Proof.
  intro n.
  apply (lt_wf_ind n (fun n => forall (u : tm') x ty t3',
    tmChkNoExtraCstrs u = true ->
    evalremoveFnPos'AnimatedTopFn n (Success tm' u) = Success tm' (tabs' x ty t3') ->
    tmChkNoExtraCstrs t3' = true)).
  clear n. intros n IH u x ty t3' Hu Heq.
  destruct n as [| m].
  { rewrite base_result in Heq. discriminate Heq. }
  rewrite evalTop_stepSuccess in Heq.
  destruct u as [s1|lx lT lbody|a1 a2| |v1|b1|c1 c2 c3|fn0 T0 fbody0|mk|s4 n1 n2] eqn:Hu_eq;
    simpl in Hu; try discriminate Hu.

  - (* tvar' s1: every handler NoMatch, escape *)
    change
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      with
      (List.app
        [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
         E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
        [evalremoveFnPos'UndefinedAnimated]) in Heq.
    rewrite (dispatch_coind_ext_escape
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
      (tvar' s1)
      ltac:(intros hh k Hin;
            simpl in Hin;
            repeat destruct Hin as [<- | Hin]; [ | | | | | | | | | contradiction];
            [ rewrite E_Lam_result; reflexivity
            | rewrite E_Zero_result; reflexivity
            | rewrite E_Succ_result_generic; reflexivity
            | apply E_PredZero_result_wrongshape; intros v'; discriminate
            | apply E_PredSucc_result_wrongshape; intros v'; discriminate
            | apply E_App_result_wrongshape; intros aa1 aa2; discriminate
            | apply E_IfzZero_result_wrongshape; intros cc1 cc2 cc3; discriminate
            | apply E_IfzSucc_result_wrongshape; intros cc1 cc2 cc3; discriminate
            | apply E_Fix_result_wrongshape; intros ffn TT bb; discriminate ])
      m) in Heq.
    discriminate Heq.

  - (* tabs' lx lT lbody: E_Lam fires directly *)
    destruct m as [| m'].
    { simpl in Heq. discriminate Heq. }
    rewrite (dispatch_coind_ext_fire E_LamremoveFnPos'Animated _ _ m'
               (tabs' lx lT lbody)
               (E_Lam_result m' (tabs' lx lT lbody))) in Heq.
    injection Heq as -> -> <-.
    exact Hu.

  - (* tapp' a1 a2: only E_App can produce a tabs' result *)
    change
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      with
      (List.app
        [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
         E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
        [E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]) in Heq.
    destruct (dispatch_coind_ext_reach
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
      [E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      (tapp' a1 a2)
      m
      ltac:(intros hh k Hin;
            simpl in Hin;
            repeat destruct Hin as [<- | Hin]; [ | | | | | contradiction];
            [ rewrite E_Lam_result; reflexivity
            | rewrite E_Zero_result; reflexivity
            | rewrite E_Succ_result_generic; reflexivity
            | apply E_PredZero_result_wrongshape; intros v'; discriminate
            | apply E_PredSucc_result_wrongshape; intros v'; discriminate ]))
      as [Hesc | [k [Hkm Hk]]].
    { rewrite Hesc in Heq. discriminate Heq. }
    rewrite Hk in Heq. clear Hk.
    destruct k as [| k].
    { simpl in Heq. discriminate Heq. }
    destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) a1) as [w1 Hw1].
    destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) a2) as [w2 Hw2].
    destruct w1 as [s1'|xx tty tt3|a1'' a2''| |v1'|b1'|c1' c2' c3'|fn0' T0' fbody0'|mk'|s4' n1' n2']
      eqn:Hw1shape.
    1,3,4,5,6,7,8,9,10 :
      (rewrite (dispatch_coind_ext_skip _ _ _ _
                  (E_App_result_nomatch1 evalremoveFnPos'AnimatedTopFn k a1 a2 _ Hw1
                     ltac:(discriminate))) in Heq;
       change
         [E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
          E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
          E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
          evalremoveFnPos'UndefinedAnimated]
         with
         (List.app
           [E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
            E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
            E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
           [evalremoveFnPos'UndefinedAnimated]) in Heq;
       rewrite (dispatch_coind_ext_escape
         [E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
          E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
          E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
         (tapp' a1 a2)
         ltac:(intros hh kk Hin;
               simpl in Hin;
               repeat destruct Hin as [<- | Hin]; [ | | | contradiction];
               [ apply E_IfzZero_result_wrongshape; intros cc1 cc2 cc3; discriminate
               | apply E_IfzSucc_result_wrongshape; intros cc1 cc2 cc3; discriminate
               | apply E_Fix_result_wrongshape; intros ffn TT bb; discriminate ])
         k) in Heq;
       discriminate Heq).
    (* remaining case (2nd): w1 = tabs' xx tty tt3 *)
    destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k)
                (substliftedFunc xx w2 tt3)) as [w3 Hw3].
    destruct (andb (tmChkNoExtraCstrs w2) (isValueFn (tmPushPlain w2))) eqn:Hchk.
    + apply andb_prop in Hchk as [Hchk1 Hchk2].
      rewrite (dispatch_coind_ext_fire _ _ _ _ _
                 (E_App_result_spec evalremoveFnPos'AnimatedTopFn k a1 a2 xx tty tt3 w2 w3
                    Hw1 Hw2 Hchk1 Hchk2 Hw3)) in Heq.
      injection Heq as Heqw3.
      rewrite Heqw3 in Hw3.
      assert (Htt3 : tmChkNoExtraCstrs tt3 = true).
      { apply andb_prop in Hu as [Hu1 Hu2].
        apply andb_prop in Hu2 as [Hu2 _].
        apply (IH (S k) ltac:(lia) a1 xx tty tt3 Hu2 Hw1). }
      apply (IH (S k) ltac:(lia) (substliftedFunc xx w2 tt3) x ty t3').
      * apply substliftedFunc_no_extra_cstrs; assumption.
      * exact Hw3.
    + rewrite (dispatch_coind_ext_skip _ _ _ _
                 (E_App_result_nomatch2 evalremoveFnPos'AnimatedTopFn k a1 a2 xx tty tt3 w2 w3
                    Hw1 Hw2 Hw3
                    ltac:(destruct (tmChkNoExtraCstrs w2) eqn:E; simpl in Hchk;
                          [right | left]; congruence))) in Heq.
      change
        [E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        with
        (List.app
          [E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
           E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
           E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
          [evalremoveFnPos'UndefinedAnimated]) in Heq.
      rewrite (dispatch_coind_ext_escape
        [E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
        (tapp' a1 a2)
        ltac:(intros hh kk Hin;
              simpl in Hin;
              repeat destruct Hin as [<- | Hin]; [ | | | contradiction];
              [ apply E_IfzZero_result_wrongshape; intros cc1 cc2 cc3; discriminate
              | apply E_IfzSucc_result_wrongshape; intros cc1 cc2 cc3; discriminate
              | apply E_Fix_result_wrongshape; intros ffn TT bb; discriminate ])
        k) in Heq.
      discriminate Heq.

  - (* tzero': only E_Zero can produce a Success at all (tzero'-shaped, not tabs') *)
    change
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      with
      (List.app [E_LamremoveFnPos'Animated]
        [E_ZeroremoveFnPos'Animated;
         E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]) in Heq.
    destruct (dispatch_coind_ext_reach [E_LamremoveFnPos'Animated]
      [E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      tzero' m
      ltac:(intros hh k Hin; simpl in Hin; destruct Hin as [<- | []];
            rewrite E_Lam_result; reflexivity))
      as [Hesc | [k [Hkm Hk]]].
    { rewrite Hesc in Heq. discriminate Heq. }
    rewrite Hk in Heq. clear Hk.
    destruct k as [| k].
    { simpl in Heq. discriminate Heq. }
    rewrite (dispatch_coind_ext_fire _ _ _ _ _ (E_Zero_result k tzero')) in Heq.
    discriminate Heq.

  - (* tsucc' v1: only E_Succ can fire, always giving a tsucc'-shaped (not tabs') value *)
    change
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      with
      (List.app [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated]
        [E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]) in Heq.
    destruct (dispatch_coind_ext_reach
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated]
      [E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      (tsucc' v1) m
      ltac:(intros hh k Hin; simpl in Hin;
            repeat destruct Hin as [<- | Hin]; [ | | contradiction];
            [ rewrite E_Lam_result; reflexivity
            | rewrite E_Zero_result; reflexivity ]))
      as [Hesc | [k [Hkm Hk]]].
    { rewrite Hesc in Heq. discriminate Heq. }
    rewrite Hk in Heq. clear Hk.
    destruct k as [| k].
    { simpl in Heq. discriminate Heq. }
    destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) v1) as [wv Hwv].
    rewrite (dispatch_coind_ext_fire _ _ _ _ _
               (E_Succ_result_generic_spec evalremoveFnPos'AnimatedTopFn k v1 wv Hwv)) in Heq.
    discriminate Heq.
  - (* tpred' b1: PredZero or PredSucc may produce a result; PredSucc's own gate gives
       marker-freeness of its passthrough value for free. *)
    change
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      with
      (List.app
        [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
         E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
        [E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]) in Heq.
    destruct (dispatch_coind_ext_reach
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
      [E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      (tpred' b1) m
      ltac:(intros hh k Hin; simpl in Hin;
            repeat destruct Hin as [<- | Hin]; [ | | | contradiction];
            [ rewrite E_Lam_result; reflexivity
            | rewrite E_Zero_result; reflexivity
            | rewrite E_Succ_result_generic; reflexivity ]))
      as [Hesc | [k [Hkm Hk]]].
    { rewrite Hesc in Heq. discriminate Heq. }
    rewrite Hk in Heq. clear Hk.
    (* Factor "whenever PredZero doesn't fire, here's what the rest gives" once, exactly as
       [dispatch_tpred_from_pred]'s own proof does for its analogous continuation. *)
    assert (Hcont : forall k0,
      dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        k0 (Success tm' (tpred' b1)) = Success tm' (tabs' x ty t3') ->
      tmChkNoExtraCstrs t3' = true).
    { clear Heq Hkm k. intros k0 Heq2.
      destruct k0 as [| k].
      { simpl in Heq2. discriminate Heq2. }
      destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) b1) as [w1' Hw1'].
      destruct w1' as [s1'|xx tty tt3|a1' a2'| |v1'|b1'|c1' c2' c3'|fn0' T0' fbody0'|mk'|s4' n1' n2']
        eqn:Hw1'shape.
      1,2,3,4,6,7,8,9,10:
        (pose proof (E_PredSucc_result_spec2 evalremoveFnPos'AnimatedTopFn k b1 _ Hw1') as HPS;
         simpl in HPS;
         rewrite (dispatch_coind_ext_skip _ _ _ _ HPS) in Heq2;
         escape_app_ifz_fix (tpred' b1) k Heq2).
      (* remaining case (5th, tsucc' v1'): PredSucc may fire *)
      pose proof (E_PredSucc_result_spec2 evalremoveFnPos'AnimatedTopFn k b1 _ Hw1') as HPS.
      simpl in HPS.
      destruct (andb (tmChkNoExtraCstrs v1') (isValueFn (tmPushPlain v1'))) eqn:Hchk.
      + apply andb_prop in Hchk as [Hchk1 Hchk2].
        rewrite (dispatch_coind_ext_fire _ _ _ _ _ HPS) in Heq2.
        injection Heq2 as Heqv1.
        rewrite Heqv1 in Hchk1. simpl in Hchk1.
        exact Hchk1.
      + rewrite (dispatch_coind_ext_skip _ _ _ _ HPS) in Heq2.
        escape_app_ifz_fix (tpred' b1) k Heq2. }
    destruct k as [| k].
    { simpl in Heq. discriminate Heq. }
    destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) b1) as [w1 Hw1].
    destruct w1 as [s1'|xx tty tt3|a1' a2'| |v1'|b1'|c1' c2' c3'|fn0' T0' fbody0'|mk'|s4' n1' n2']
      eqn:Hw1shape.
    1,2,3,5,6,7,8,9,10:
      (pose proof (E_PredZero_result_spec evalremoveFnPos'AnimatedTopFn k b1 _ Hw1) as HPZ;
       simpl in HPZ;
       rewrite (dispatch_coind_ext_skip _ _ _ _ HPZ) in Heq;
       apply (Hcont k Heq)).
    (* remaining case (4th, tzero'): PredZero fires directly *)
    pose proof (E_PredZero_result_spec evalremoveFnPos'AnimatedTopFn k b1 _ Hw1) as HPZ.
    simpl in HPZ.
    rewrite (dispatch_coind_ext_fire _ _ _ _ _ HPZ) in Heq.
    discriminate Heq.
  - (* tifz' c1 c2 c3: IfzZero or IfzSucc may produce a result. *)
    change
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      with
      (List.app
        [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
         E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
        [E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]) in Heq.
    destruct (dispatch_coind_ext_reach
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
      [E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      (tifz' c1 c2 c3) m
      ltac:(intros hh k Hin; simpl in Hin;
            repeat destruct Hin as [<- | Hin]; [ | | | | | | contradiction];
            [ rewrite E_Lam_result; reflexivity
            | rewrite E_Zero_result; reflexivity
            | rewrite E_Succ_result_generic; reflexivity
            | apply E_PredZero_result_wrongshape; intros v'; discriminate
            | apply E_PredSucc_result_wrongshape; intros v'; discriminate
            | apply E_App_result_wrongshape; intros aa1 aa2; discriminate ]))
      as [Hesc | [k [Hkm Hk]]].
    { rewrite Hesc in Heq. discriminate Heq. }
    rewrite Hk in Heq. clear Hk.
    (* Factor "whenever IfzZero doesn't fire, here's what the rest gives" once. Threads the
       fuel bound [k0 <= m] through so the IH application below (needed for the IfzSucc/c3
       case, which — unlike PredSucc — has no "andb gives it for free" shortcut) stays
       well-founded. *)
    assert (Hcont : forall k0, k0 <= m ->
      dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        k0 (Success tm' (tifz' c1 c2 c3)) = Success tm' (tabs' x ty t3') ->
      tmChkNoExtraCstrs t3' = true).
    { clear Heq Hkm k. intros k0 Hk0m Heq2.
      destruct k0 as [| k].
      { simpl in Heq2. discriminate Heq2. }
      destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) c1) as [w1' Hw1'].
      destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) c3) as [w3' Hw3'].
      destruct w1' as [s1'|xx tty tt3|a1' a2'| |v1'|b1'|cc1' cc2' cc3'|fn0' T0' fbody0'|mk'|s4' n1' n2']
        eqn:Hw1'shape.
      1,2,3,4,6,7,8,9,10:
        (pose proof (E_IfzSucc_result_spec evalremoveFnPos'AnimatedTopFn k c1 c2 c3 _ w3'
                       Hw1' Hw3') as HIS;
         rewrite (dispatch_coind_ext_skip _ _ _ _ HIS) in Heq2;
         change
           [E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
            evalremoveFnPos'UndefinedAnimated]
           with
           (List.app [E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
             [evalremoveFnPos'UndefinedAnimated]) in Heq2;
         rewrite (dispatch_coind_ext_escape
           [E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
           (tifz' c1 c2 c3)
           ltac:(intros hh kk Hin; simpl in Hin;
                 destruct Hin as [<- | []];
                 apply E_Fix_result_wrongshape; intros ffn TT bb; discriminate)
           k) in Heq2;
         discriminate Heq2).
      (* remaining case (5th, tsucc' v1'): IfzSucc may fire *)
      pose proof (E_IfzSucc_result_spec evalremoveFnPos'AnimatedTopFn k c1 c2 c3 _ w3'
                    Hw1' Hw3') as HIS.
      simpl in HIS.
      destruct (andb (tmChkNoExtraCstrs v1') (isValueFn (tmPushPlain v1'))) eqn:Hchk.
      + rewrite (dispatch_coind_ext_fire _ _ _ _ _ HIS) in Heq2.
        injection Heq2 as Heqw3.
        rewrite Heqw3 in Hw3'.
        apply (IH (S k) ltac:(lia) c3 x ty t3').
        * apply andb_prop in Hu as [Hu1 Hu2].
          exact Hu1.
        * exact Hw3'.
      + rewrite (dispatch_coind_ext_skip _ _ _ _ HIS) in Heq2.
        change
          [E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
           evalremoveFnPos'UndefinedAnimated]
          with
          (List.app [E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
            [evalremoveFnPos'UndefinedAnimated]) in Heq2.
        rewrite (dispatch_coind_ext_escape
          [E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
          (tifz' c1 c2 c3)
          ltac:(intros hh kk Hin; simpl in Hin;
                destruct Hin as [<- | []];
                apply E_Fix_result_wrongshape; intros ffn TT bb; discriminate)
          k) in Heq2.
        discriminate Heq2. }
    destruct k as [| k].
    { simpl in Heq. discriminate Heq. }
    destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) c1) as [w1 Hw1].
    destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) c2) as [w2 Hw2].
    destruct w1 as [s1'|xx tty tt3|a1' a2'| |v1'|b1'|cc1 cc2 cc3|fn0' T0' fbody0'|mk'|s4' n1' n2']
      eqn:Hw1shape.
    1,2,3,5,6,7,8,9,10:
      (pose proof (E_IfzZero_result_spec2 evalremoveFnPos'AnimatedTopFn k c1 c2 c3 _ w2
                     Hw1 Hw2) as HIZ;
       rewrite (dispatch_coind_ext_skip _ _ _ _ HIZ) in Heq;
       apply (Hcont k ltac:(lia) Heq)).
    (* remaining case (4th, tzero'): IfzZero fires directly *)
    rewrite (dispatch_coind_ext_fire _ _ _ _ _
               (E_IfzZero_result_spec2 evalremoveFnPos'AnimatedTopFn k c1 c2 c3 tzero' w2
                  Hw1 Hw2)) in Heq.
    injection Heq as Heqw2.
    rewrite Heqw2 in Hw2.
    apply (IH (S k) ltac:(lia) c2 x ty t3').
    + apply andb_prop in Hu as [Hu1 Hu2].
      apply andb_prop in Hu2 as [Hu2 Hu3].
      exact Hu2.
    + exact Hw2.

  - (* tfix' fn0 T0 fbody0: E_Fix always fires once reached (its own shape check is already
       satisfied, since u itself is tfix'-shaped); no gating condition, so [fbody0]'s
       marker-freeness (needed for [substliftedFunc]'s smart branch) comes directly from
       [Hu]. *)
    change
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      with
      (List.app
        [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
         E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
        [E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]) in Heq.
    destruct (dispatch_coind_ext_reach
      [E_LamremoveFnPos'Animated; E_ZeroremoveFnPos'Animated;
       E_SuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_PredSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_AppremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn]
      [E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
       evalremoveFnPos'UndefinedAnimated]
      (tfix' fn0 T0 fbody0) m
      ltac:(intros hh k Hin; simpl in Hin;
            repeat destruct Hin as [<- | Hin]; [ | | | | | | | | contradiction];
            [ rewrite E_Lam_result; reflexivity
            | rewrite E_Zero_result; reflexivity
            | rewrite E_Succ_result_generic; reflexivity
            | apply E_PredZero_result_wrongshape; intros v'; discriminate
            | apply E_PredSucc_result_wrongshape; intros v'; discriminate
            | apply E_App_result_wrongshape; intros aa1 aa2; discriminate
            | apply E_IfzZero_result_wrongshape; intros cc1 cc2 cc3; discriminate
            | apply E_IfzSucc_result_wrongshape; intros cc1 cc2 cc3; discriminate ]))
      as [Hesc | [k [Hkm Hk]]].
    { rewrite Hesc in Heq. discriminate Heq. }
    rewrite Hk in Heq. clear Hk.
    destruct k as [| k].
    { simpl in Heq. discriminate Heq. }
    assert (Hbody : tmChkNoExtraCstrs (substliftedFunc fn0 (tfix' fn0 T0 fbody0) fbody0) = true).
    { apply substliftedFunc_no_extra_cstrs.
      - simpl. exact Hu.
      - exact Hu. }
    destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k)
                (substliftedFunc fn0 (tfix' fn0 T0 fbody0) fbody0)) as [w Hw].
    rewrite (dispatch_coind_ext_fire _ _ _ _ _
               (E_Fix_result_spec evalremoveFnPos'AnimatedTopFn k fn0 T0 fbody0 w Hw)) in Heq.
    injection Heq as Heqw.
    rewrite Heqw in Hw.
    apply (IH (S k) ltac:(lia) (substliftedFunc fn0 (tfix' fn0 T0 fbody0) fbody0) x ty t3').
    + exact Hbody.
    + exact Hw.
Qed.

Lemma E_App_lambda_body_no_extra_cstrs : forall n t1 x ty t3',
  evalremoveFnPos'AnimatedTopFn n (Success tm' (tmLift t1)) = Success tm' (tabs' x ty t3') ->
  tmChkNoExtraCstrs t3' = true.
Proof.
  intros n t1 x ty t3' H.
  apply (E_App_lambda_body_no_extra_cstrs_general n (tmLift t1) x ty t3').
  - apply tmChkNoExtraCstrs_tmLift.
  - exact H.
Qed.


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
  match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t1)) with
  | Success (tabs' x ty t3') =>
      match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t2)) with
      | Success v2' =>
          if andb (tmChkNoExtraCstrs v2') (isValueFn (tmPushPlain v2'))
          then (match evalremoveFnPos'AnimatedTopFn (S n)
                        (Success tm' (tmLift (subst x (tmPushPlain v2') (tmPushPlain t3')))) with
                | Success x0 => Success tm (tmTransparentSigmaPushBody f x0)
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
  (* Fallthrough: whenever App doesn't match at all, IfzZero/IfzSucc/Fix/Undefined also
     don't match a tapp'-shaped input, bottoming out at the oracle escape — exactly the
     [Hfall] pattern from [dispatch_tpred_from_pred], for this handler tail. *)
  assert (Hfall : forall m,
    (match dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        m (Success tm' (tapp' (tmLift t1) (tmLift t2))) with
     | Success x => Success tm (tmTransparentSigmaPushBody f x)
     | _ => NoMatch tm
     end) = Success tm (f (tapp t1 t2))).
  { intro m.
    assert (Hraw :
      dispatch_coind_ext tm' tm' evalremoveFnPos'Rest
        [E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn;
         evalremoveFnPos'UndefinedAnimated]
        m (Success tm' (tapp' (tmLift t1) (tmLift t2)))
      = Success tm' (evalremoveFnPosAn1 (tapp' (tmLift t1) (tmLift t2)))).
    { clear. destruct m.
      - simpl. reflexivity.
      - unfold dispatch_coind_ext.
        assert (HIZ : E_IfzZeroremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S m)
                        (Success tm' (tapp' (tmLift t1) (tmLift t2))) = NoMatch tm')
          by (unfold E_IfzZeroremoveFnPos'Animated, option_to_result; reflexivity).
        rewrite HIZ. destruct m.
        + simpl. reflexivity.
        + unfold dispatch_coind_ext.
          assert (HIS : E_IfzSuccremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S m)
                          (Success tm' (tapp' (tmLift t1) (tmLift t2))) = NoMatch tm')
            by (unfold E_IfzSuccremoveFnPos'Animated, option_to_result; reflexivity).
          rewrite HIS. destruct m.
          * simpl. reflexivity.
          * unfold dispatch_coind_ext.
            assert (HF : E_FixremoveFnPos'Animated evalremoveFnPos'AnimatedTopFn (S m)
                           (Success tm' (tapp' (tmLift t1) (tmLift t2))) = NoMatch tm')
              by (unfold E_FixremoveFnPos'Animated, option_to_result; reflexivity).
            rewrite HF. destruct m.
            -- simpl. reflexivity.
            -- unfold dispatch_coind_ext.
               assert (HU : Success tm' (evalremoveFnPosAn1 (tapp' (tmLift t1) (tmLift t2)))
                            = evalremoveFnPos'UndefinedAnimated (S m)
                                (Success tm' (tapp' (tmLift t1) (tmLift t2))))
                 by (simpl; reflexivity).
               rewrite <- HU. reflexivity. }
    rewrite Hraw. simpl.
    repeat rewrite tmTransparentSigmaPushBody_tmLift. reflexivity. }
  destruct (evalremoveFnPos'AnimatedTopFn_always_success (S n) (tmLift t1)) as [w1 Hw1].
  rewrite Hw1.
  destruct w1 as [s1|x ty t3'|a1 a2| |v1|b1|c1 c2 c3|s2 ty2 b2|m1|s3 n1 n2] eqn:Hw1shape.
  1,3,4,5,6,7,8,9,10:
    (rewrite (dispatch_coind_ext_skip _ _ _ _
                (E_App_result_nomatch1 evalremoveFnPos'AnimatedTopFn n (tmLift t1) (tmLift t2) _
                   Hw1 ltac:(discriminate)));
     apply Hfall).
  (* w1 = tabs' x ty t3' *)
  destruct (evalremoveFnPos'AnimatedTopFn_always_success (S n) (tmLift t2)) as [w2 Hw2].
  rewrite Hw2.
  destruct (andb (tmChkNoExtraCstrs w2) (isValueFn (tmPushPlain w2))) eqn:Hchk.
  - apply andb_prop in Hchk as [Hchk1 Hchk2].
    assert (Ht3 : tmChkNoExtraCstrs t3' = true)
      by (apply (E_App_lambda_body_no_extra_cstrs (S n) t1 x ty t3'); exact Hw1).
    assert (Hsubst_eq :
      substliftedFunc x w2 t3' = tmLift (subst x (tmPushPlain w2) (tmPushPlain t3'))).
    { unfold substliftedFunc. rewrite Hchk1, Ht3. reflexivity. }
    destruct (evalremoveFnPos'AnimatedTopFn_always_success (S n)
                (substliftedFunc x w2 t3')) as [w3 Hw3].
    rewrite (dispatch_coind_ext_fire _ _ _ _ _
               (E_App_result_spec evalremoveFnPos'AnimatedTopFn n (tmLift t1) (tmLift t2) x ty t3'
                  w2 w3 Hw1 Hw2 Hchk1 Hchk2 Hw3)).
    rewrite Hsubst_eq in Hw3.
    rewrite Hw3.
    reflexivity.
  - destruct (evalremoveFnPos'AnimatedTopFn_always_success (S n)
                (substliftedFunc x w2 t3')) as [w3 Hw3].
    rewrite (dispatch_coind_ext_skip _ _ _ _
               (E_App_result_nomatch2 evalremoveFnPos'AnimatedTopFn n (tmLift t1) (tmLift t2) x ty t3'
                  w2 w3 Hw1 Hw2 Hw3
                  ltac:(destruct (tmChkNoExtraCstrs w2) eqn:E; simpl in Hchk;
                        [right | left]; congruence))).
    apply Hfall.
Qed.

Lemma dispatch_tapp : forall n t1 t2 f,
  (match evalremoveFnPos'AnimatedTopFn
     (S (S (S (S (S (S (S n))))))) (Success tm' (tapp' (tmLift t1) (tmLift t2))) with
   | Success x => Success tm (tmTransparentSigmaPushBody f x)
   | _ => NoMatch tm
   end)
  =
  match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t1)) with
  | Success (tabs' x ty t3') =>
      match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t2)) with
      | Success v2' =>
          if andb (tmChkNoExtraCstrs v2') (isValueFn (tmPushPlain v2'))
          then (match evalremoveFnPos'AnimatedTopFn (S n)
                        (Success tm' (tmLift (subst x (tmPushPlain v2') (tmPushPlain t3')))) with
                | Success x0 => Success tm (tmTransparentSigmaPushBody f x0)
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

(** CORRECTED (see [dispatch_tapp_from_app]): shape/value decisions on raw [tm'] results. *)
Lemma anim_S_tapp : forall n t1 t2 f,
  evalTransparentSigma2AnimatedTopFn
    (S (S (S (S (S (S (S n))))))) (Success tm (tapp t1 t2)) f =
  match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t1)) with
  | Success (tabs' x ty t3') =>
      match evalremoveFnPos'AnimatedTopFn (S n) (Success tm' (tmLift t2)) with
      | Success v2' =>
          if andb (tmChkNoExtraCstrs v2') (isValueFn (tmPushPlain v2'))
          then match evalremoveFnPos'AnimatedTopFn (S n)
                       (Success tm' (tmLift (subst x (tmPushPlain v2') (tmPushPlain t3')))) with
               | Success x0 => Success tm (tmTransparentSigmaPushBody f x0)
               | _ => NoMatch tm
               end
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
Proof.
  intros n fn T t f.
  assert (Hsubst_eq :
    substliftedFunc fn (tfix' fn T (tmLift t)) (tmLift t) = tmLift (subst fn (tfix fn T t) t)).
  { unfold substliftedFunc.
    assert (Hc := tmChkNoExtraCstrs_tmLift t).
    simpl. rewrite Hc.
    rewrite (tmPushPlain_tmLift t).
    reflexivity. }
  destruct (evalremoveFnPos'AnimatedTopFn_always_success (S n)
              (substliftedFunc fn (tfix' fn T (tmLift t)) (tmLift t))) as [w Hw].
  rewrite (dispatch_coind_ext_fire _ _ _ _ _
             (E_Fix_result_spec evalremoveFnPos'AnimatedTopFn n fn T (tmLift t) w Hw)).
  rewrite Hsubst_eq in Hw.
  rewrite Hw.
  reflexivity.
Qed.

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


Theorem correspondence_soundness_productive : forall (n : nat) (inputTm outputTm : tm), (exists m : nat, (exists outputTm2 : tm,
  m > n /\ 
  ((evalTransparentSigma2AnimatedTopFn n (Success tm inputTm)) (fun t' : tm => t')  = Success (tm) (outputTm) -> 
  isValueFn outputTm = false -> (evalTransparentSigma2AnimatedTopFn m (Success tm inputTm)) (fun t' : tm => t')  = Success (tm) (outputTm2) /\
  stepTC outputTm outputTm2))).
Proof. Admitted.


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
    (* n = 7+k: E_App handler fires. CORRECTED anim_S_tapp checks raw tm'-level shapes
       before any push — see the comment on [dispatch_tapp_from_app]. NOTE: every
       sub-evaluation's result is extracted via [evalremoveFnPos'AnimatedTopFn_always_success]
       and [rewrite]-substituted into Hanim BEFORE any [simpl] touches Hanim. [simpl] is
       eager and will silently unfold not-yet-relevant sub-evaluations nested deeper inside
       Hanim (e.g. the t2/subst sub-computation, even while still underneath the unresolved
       t1-shape match); once that happens a later [destruct <that same sub-eval> eqn:H] no
       longer syntactically matches what's actually sitting in Hanim, and any [injection]
       downstream of it fails with "Nothing to inject" despite the branch being genuinely
       provable. Extracting+rewriting every sub-evaluation up front (in dependency order)
       before ever calling [simpl in Hanim] avoids this entirely. *)
    + rewrite anim_S_tapp in Hanim.
      destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) (tmLift t1)) as [w1 Hw1].
      rewrite Hw1 in Hanim.
      destruct w1 as [s1|x ty t3'|a1 a2| |v1|b1|c1 c2 c3|s2 ty2 b2|m1|s3 n1 n2];
        [ simpl in Hanim; injection Hanim as <-; apply BS_Stop
        | idtac
        | simpl in Hanim; injection Hanim as <-; apply BS_Stop
        | simpl in Hanim; injection Hanim as <-; apply BS_Stop
        | simpl in Hanim; injection Hanim as <-; apply BS_Stop
        | simpl in Hanim; injection Hanim as <-; apply BS_Stop
        | simpl in Hanim; injection Hanim as <-; apply BS_Stop
        | simpl in Hanim; injection Hanim as <-; apply BS_Stop
        | simpl in Hanim; injection Hanim as <-; apply BS_Stop
        | simpl in Hanim; injection Hanim as <-; apply BS_Stop ].
      (* w1 = tabs' x ty t3'; Hanim is still fully unreduced here (no simpl run yet). *)
      destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) (tmLift t2)) as [w2 Hw2].
      rewrite Hw2 in Hanim.
      destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k)
                  (tmLift (subst x (tmPushPlain w2) (tmPushPlain t3')))) as [w3 Hw3].
      rewrite Hw3 in Hanim.
      simpl in Hanim.
      destruct (andb (tmChkNoExtraCstrs w2) (isValueFn (tmPushPlain w2))) eqn:Hchk;
        simpl in Hanim.
      * injection Hanim as <-.
        apply andb_prop in Hchk as [Hchk1 Hchk2].
        pose proof (E_App_lambda_body_no_extra_cstrs (S k) t1 x ty t3' Hw1) as Ht3.
        assert (Hpush : forall (g : tm -> tm) (w : tm'), tmChkNoExtraCstrs w = true ->
                        tmTransparentSigmaPushBody g w = tmPushPlain w).
        { clear. intros g w. induction w; simpl; intros H; try reflexivity; try discriminate.
          - rewrite IHw; [reflexivity | exact H].
          - destruct (tmChkNoExtraCstrs w1) eqn:E1; destruct (tmChkNoExtraCstrs w2) eqn:E2;
              simpl in H; try discriminate.
            rewrite (IHw1 eq_refl), (IHw2 eq_refl). reflexivity.
          - rewrite IHw; [reflexivity | exact H].
          - rewrite IHw; [reflexivity | exact H].
          - destruct (tmChkNoExtraCstrs w1) eqn:E1; destruct (tmChkNoExtraCstrs w2) eqn:E2;
              destruct (tmChkNoExtraCstrs w3) eqn:E3; simpl in H; try discriminate.
            rewrite (IHw1 eq_refl), (IHw2 eq_refl), (IHw3 eq_refl). reflexivity.
          - rewrite IHw; [reflexivity | exact H]. }
        assert (Htm1 : evalTransparentSigma2AnimatedTopFn (S k) (Success tm t1) (fun t' : tm => t') =
                        Success tm (tabs x ty (tmTransparentSigmaPushBody (fun t' : tm => t') t3'))).
        { unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                 evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
          cbn [tmLift]. rewrite Hw1. reflexivity. }
        assert (Htm2 : evalTransparentSigma2AnimatedTopFn (S k) (Success tm t2) (fun t' : tm => t') =
                        Success tm (tmTransparentSigmaPushBody (fun t' : tm => t') w2)).
        { unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                 evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
          cbn [tmLift]. rewrite Hw2. reflexivity. }
        assert (Htm3 : evalTransparentSigma2AnimatedTopFn (S k)
                          (Success tm (subst x (tmTransparentSigmaPushBody (fun t' : tm => t') w2)
                                               (tmTransparentSigmaPushBody (fun t' : tm => t') t3')))
                          (fun t' : tm => t') =
                        Success tm (tmTransparentSigmaPushBody (fun t' : tm => t') w3)).
        { unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                 evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
          cbn [tmLift].
          rewrite (Hpush (fun t' : tm => t') w2 Hchk1).
          rewrite (Hpush (fun t' : tm => t') t3' Ht3).
          rewrite Hw3. reflexivity. }
        eapply BS_App. repeat split.
        -- apply (IH (S k)). lia. exact Htm1.
        -- apply (IH (S k)). lia. exact Htm2.
        -- apply isValueFn_to_is_value.
           rewrite (Hpush (fun t' : tm => t') w2 Hchk1). exact Hchk2.
        -- apply (IH (S k)). lia. exact Htm3.
      * injection Hanim as <-. apply BS_Stop.

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
    + (* n = 6+k: anim_S_tpred fires. CORRECTED anim_S_tpred checks the RAW (unpushed)
         tm'-level result of evalremoveFnPos'AnimatedTopFn to decide the PredZero/PredSucc
         shape, then only pushes once the shape decision is made — see the comment on
         [dispatch_tpred_from_pred] for why the old push-first version was unsound. *)
      rewrite anim_S_tpred in Hanim.
      (* Whenever the PredZero check doesn't fire (whatever the reason), the remaining
         "PredSucc or bail out to the oracle" structure is IDENTICAL; factor it once. *)
      assert (Hinner : forall outputTm2,
        match evalremoveFnPos'AnimatedTopFn (S k) (Success tm' (tmLift t)) with
        | Success (tsucc' v') =>
            if andb (tmChkNoExtraCstrs v') (isValueFn (tmPushPlain v'))
            then Success tm (tmTransparentSigmaPushBody (fun t' : tm => t') v')
            else Success tm ((fun t' : tm => t') (tpred t))
        | _ => Success tm ((fun t' : tm => t') (tpred t))
        end = Success tm outputTm2 -> bigstop (tpred t) outputTm2).
      { intros outputTm2 Heq.
        destruct (evalremoveFnPos'AnimatedTopFn (S k) (Success tm' (tmLift t))) as [| w2 |] eqn:Hw2;
          simpl in Heq.
        - injection Heq as <-. apply BS_Stop.
        - destruct w2 as [s1|s2 ty2 b2|a1 a2| |v2|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
            simpl in Heq; try (injection Heq as <-; apply BS_Stop).
          destruct (andb (tmChkNoExtraCstrs v2) (isValueFn (tmPushPlain v2))) eqn:Hchk;
            simpl in Heq; injection Heq as <-.
          + assert (Htm : evalTransparentSigma2AnimatedTopFn (S k) (Success tm t) (fun t' : tm => t') =
                           Success tm (tsucc (tmTransparentSigmaPushBody (fun t' : tm => t') v2))).
            { unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                     evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
              cbn [tmLift]. rewrite Hw2. reflexivity. }
            apply andb_prop in Hchk as [Hchk1 Hchk2].
            assert (Hpush : forall (g : tm -> tm) (w : tm'), tmChkNoExtraCstrs w = true ->
                            tmTransparentSigmaPushBody g w = tmPushPlain w).
            { clear. intros g w. induction w; simpl; intros H; try reflexivity; try discriminate.
              - rewrite IHw; [reflexivity | exact H].
              - destruct (tmChkNoExtraCstrs w1) eqn:E1; destruct (tmChkNoExtraCstrs w2) eqn:E2;
                  simpl in H; try discriminate.
                rewrite (IHw1 eq_refl), (IHw2 eq_refl). reflexivity.
              - rewrite IHw; [reflexivity | exact H].
              - rewrite IHw; [reflexivity | exact H].
              - destruct (tmChkNoExtraCstrs w1) eqn:E1; destruct (tmChkNoExtraCstrs w2) eqn:E2;
                  destruct (tmChkNoExtraCstrs w3) eqn:E3; simpl in H; try discriminate.
                rewrite (IHw1 eq_refl), (IHw2 eq_refl), (IHw3 eq_refl). reflexivity.
              - rewrite IHw; [reflexivity | exact H]. }
            eapply BS_PredSucc. split.
            * apply (IH (S k)). lia. exact Htm.
            * apply isValueFn_to_is_value.
              rewrite (Hpush (fun t' : tm => t') v2 Hchk1). exact Hchk2.
          + apply BS_Stop.
        - injection Heq as <-. apply BS_Stop. }
      destruct (evalremoveFnPos'AnimatedTopFn (S (S k)) (Success tm' (tmLift t))) as [| w1 |] eqn:Hw1;
        simpl in Hanim.
      * apply (Hinner outputTm Hanim).
      * destruct w1 as [s1|s2 ty2 b2|a1 a2| |v1|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
          simpl in Hanim; try (apply (Hinner outputTm Hanim)).
        injection Hanim as <-. apply BS_PredZero.
        apply (IH (S (S k))). lia.
        unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
               evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
        cbn [tmLift]. rewrite Hw1. reflexivity.
      * apply (Hinner outputTm Hanim).

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
    + (* n = 9+k: anim_S_tifz fires. CORRECTED anim_S_tifz checks the raw tm'-level
         discriminant shape before any push; see comment on [dispatch_tpred_from_pred]. *)
      rewrite anim_S_tifz in Hanim.
      (* Whenever the IfzZero check doesn't fire, the "IfzSucc or bail out" structure
         is identical regardless of why; factor it once (mirrors the tpred branch). *)
      assert (Hinner : forall outputTm2,
        match evalremoveFnPos'AnimatedTopFn (S k) (Success tm' (tmLift tdisc)) with
        | Success (tsucc' vn') =>
            if andb (tmChkNoExtraCstrs vn') (isValueFn (tmPushPlain vn'))
            then match evalremoveFnPos'AnimatedTopFn (S k) (Success tm' (tmLift t2)) with
                 | Success x => Success tm (tmTransparentSigmaPushBody (fun t' : tm => t') x)
                 | _ => NoMatch tm
                 end
            else Success tm ((fun t' : tm => t') (tifz tdisc t1 t2))
        | _ => Success tm ((fun t' : tm => t') (tifz tdisc t1 t2))
        end = Success tm outputTm2 -> bigstop (tifz tdisc t1 t2) outputTm2).
      { intros outputTm2 Heq.
        (* Extract + rewrite every sub-evaluation into Heq BEFORE any [simpl] touches it —
           see the comment on the [tapp] branch above for why this ordering matters. *)
        destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) (tmLift tdisc)) as [w2 Hw2].
        rewrite Hw2 in Heq.
        destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) (tmLift t2)) as [w3 Hw3].
        rewrite Hw3 in Heq.
        destruct w2 as [s1|s2 ty2 b2|a1 a2| |vn'|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
          [ simpl in Heq; injection Heq as <-; apply BS_Stop
          | simpl in Heq; injection Heq as <-; apply BS_Stop
          | simpl in Heq; injection Heq as <-; apply BS_Stop
          | simpl in Heq; injection Heq as <-; apply BS_Stop
          | idtac
          | simpl in Heq; injection Heq as <-; apply BS_Stop
          | simpl in Heq; injection Heq as <-; apply BS_Stop
          | simpl in Heq; injection Heq as <-; apply BS_Stop
          | simpl in Heq; injection Heq as <-; apply BS_Stop
          | simpl in Heq; injection Heq as <-; apply BS_Stop ].
        (* w2 = tsucc' vn' *)
        simpl in Heq.
        destruct (andb (tmChkNoExtraCstrs vn') (isValueFn (tmPushPlain vn'))) eqn:Hchk;
          simpl in Heq.
        + injection Heq as <-.
          apply andb_prop in Hchk as [Hchk1 Hchk2].
          assert (Hpush : forall (g : tm -> tm) (w : tm'), tmChkNoExtraCstrs w = true ->
                          tmTransparentSigmaPushBody g w = tmPushPlain w).
          { clear. intros g w. induction w; simpl; intros H; try reflexivity; try discriminate.
            - rewrite IHw; [reflexivity | exact H].
            - destruct (tmChkNoExtraCstrs w1) eqn:E1; destruct (tmChkNoExtraCstrs w2) eqn:E2;
                simpl in H; try discriminate.
              rewrite (IHw1 eq_refl), (IHw2 eq_refl). reflexivity.
            - rewrite IHw; [reflexivity | exact H].
            - rewrite IHw; [reflexivity | exact H].
            - destruct (tmChkNoExtraCstrs w1) eqn:E1; destruct (tmChkNoExtraCstrs w2) eqn:E2;
                destruct (tmChkNoExtraCstrs w3) eqn:E3; simpl in H; try discriminate.
              rewrite (IHw1 eq_refl), (IHw2 eq_refl), (IHw3 eq_refl). reflexivity.
            - rewrite IHw; [reflexivity | exact H]. }
          eapply BS_IfzSucc. repeat split.
          * apply (IH (S k)). lia.
            unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                   evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
            cbn [tmLift]. rewrite Hw2. reflexivity.
          * apply isValueFn_to_is_value.
            change (isValueFn (tmTransparentSigmaPushBody (fun t' : tm => t') vn') = true).
            rewrite (Hpush (fun t' : tm => t') vn' Hchk1). exact Hchk2.
          * apply (IH (S k)). lia.
            unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                   evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
            cbn [tmLift]. rewrite Hw3. reflexivity.
        + injection Heq as <-. apply BS_Stop. }
      destruct (evalremoveFnPos'AnimatedTopFn (S (S k)) (Success tm' (tmLift tdisc))) as [| w1 |] eqn:Hw1;
        simpl in Hanim.
      * apply (Hinner outputTm Hanim).
      * destruct w1 as [s1|s2 ty2 b2|a1 a2| |v1|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
          simpl in Hanim; try (apply (Hinner outputTm Hanim)).
        eapply BS_IfzZero. split.
        -- apply (IH (S (S k))). lia.
           unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                  evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
           cbn [tmLift]. rewrite Hw1. reflexivity.
        -- apply (IH (S (S k))). lia. exact Hanim.
      * apply (Hinner outputTm Hanim).

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
    (* n = 7+k: E_App handler fires. CORRECTED anim_S_tapp checks raw tm'-level shapes
       before any push — see the comment on [dispatch_tapp_from_app] and on the
       [correspondence_soundness_bigstop] tapp branch for why every sub-evaluation is
       extracted via [evalremoveFnPos'AnimatedTopFn_always_success] and [rewrite]-substituted
       into Hanim BEFORE any [simpl] touches it. *)
    + rewrite anim_S_tapp in Hanim.
      destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) (tmLift t1)) as [w1 Hw1].
      rewrite Hw1 in Hanim.
      destruct w1 as [s1|x ty t3'|a1 a2| |v1|b1|c1 c2 c3|s2 ty2 b2|m1|s3 n1 n2];
        [ simpl in Hanim; injection Hanim as <-; apply Hf
        | idtac
        | simpl in Hanim; injection Hanim as <-; apply Hf
        | simpl in Hanim; injection Hanim as <-; apply Hf
        | simpl in Hanim; injection Hanim as <-; apply Hf
        | simpl in Hanim; injection Hanim as <-; apply Hf
        | simpl in Hanim; injection Hanim as <-; apply Hf
        | simpl in Hanim; injection Hanim as <-; apply Hf
        | simpl in Hanim; injection Hanim as <-; apply Hf
        | simpl in Hanim; injection Hanim as <-; apply Hf ].
      (* w1 = tabs' x ty t3'; Hanim is still fully unreduced here (no simpl run yet). *)
      destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) (tmLift t2)) as [w2 Hw2].
      rewrite Hw2 in Hanim.
      destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k)
                  (tmLift (subst x (tmPushPlain w2) (tmPushPlain t3')))) as [w3 Hw3].
      rewrite Hw3 in Hanim.
      simpl in Hanim.
      destruct (andb (tmChkNoExtraCstrs w2) (isValueFn (tmPushPlain w2))) eqn:Hchk;
        simpl in Hanim.
      * injection Hanim as <-.
        apply andb_prop in Hchk as [Hchk1 Hchk2].
        pose proof (E_App_lambda_body_no_extra_cstrs (S k) t1 x ty t3' Hw1) as Ht3.
        assert (Hpush : forall (g : tm -> tm) (w : tm'), tmChkNoExtraCstrs w = true ->
                        tmTransparentSigmaPushBody g w = tmPushPlain w).
        { clear. intros g w. induction w; simpl; intros H; try reflexivity; try discriminate.
          - rewrite IHw; [reflexivity | exact H].
          - destruct (tmChkNoExtraCstrs w1) eqn:E1; destruct (tmChkNoExtraCstrs w2) eqn:E2;
              simpl in H; try discriminate.
            rewrite (IHw1 eq_refl), (IHw2 eq_refl). reflexivity.
          - rewrite IHw; [reflexivity | exact H].
          - rewrite IHw; [reflexivity | exact H].
          - destruct (tmChkNoExtraCstrs w1) eqn:E1; destruct (tmChkNoExtraCstrs w2) eqn:E2;
              destruct (tmChkNoExtraCstrs w3) eqn:E3; simpl in H; try discriminate.
            rewrite (IHw1 eq_refl), (IHw2 eq_refl), (IHw3 eq_refl). reflexivity.
          - rewrite IHw; [reflexivity | exact H]. }
        assert (Htm1 : evalTransparentSigma2AnimatedTopFn (S k) (Success tm t1) f =
                        Success tm (tabs x ty (tmTransparentSigmaPushBody f t3'))).
        { unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                 evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
          cbn [tmLift]. rewrite Hw1. reflexivity. }
        assert (Htm2 : evalTransparentSigma2AnimatedTopFn (S k) (Success tm t2) f =
                        Success tm (tmTransparentSigmaPushBody f w2)).
        { unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                 evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
          cbn [tmLift]. rewrite Hw2. reflexivity. }
        assert (Htm3 : evalTransparentSigma2AnimatedTopFn (S k)
                          (Success tm (subst x (tmTransparentSigmaPushBody f w2)
                                               (tmTransparentSigmaPushBody f t3')))
                          f =
                        Success tm (tmTransparentSigmaPushBody f w3)).
        { unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                 evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
          cbn [tmLift].
          rewrite (Hpush f w2 Hchk1).
          rewrite (Hpush f t3' Ht3).
          rewrite Hw3. reflexivity. }
        (* E_App's components are ordered (isValueFn, t1-eval, t2-eval, subst-eval) — apply
           it with every existential (x, ty, t3-val, v2-val) supplied explicitly so no
           metavariable-ordering issue arises across the [repeat split] subgoals. *)
        apply (E_App t1 t2 x ty (tmTransparentSigmaPushBody f t3') (tmTransparentSigmaPushBody f w2)).
        repeat split.
        -- rewrite (Hpush f w2 Hchk1). exact Hchk2.
        -- apply (IH (S k)). lia. exact Htm1.
        -- apply (IH (S k)). lia. exact Htm2.
        -- apply (IH (S k)). lia. exact Htm3.
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
    + (* CORRECTED anim_S_tpred checks the raw tm'-level result before any push;
         see the comment on [dispatch_tpred_from_pred]. *)
      rewrite anim_S_tpred in Hanim.
      assert (Hinner : forall outputTm2,
        match evalremoveFnPos'AnimatedTopFn (S k) (Success tm' (tmLift t)) with
        | Success (tsucc' v') =>
            if andb (tmChkNoExtraCstrs v') (isValueFn (tmPushPlain v'))
            then Success tm (tmTransparentSigmaPushBody f v')
            else Success tm (f (tpred t))
        | _ => Success tm (f (tpred t))
        end = Success tm outputTm2 -> eval (tpred t) outputTm2).
      { intros outputTm2 Heq.
        destruct (evalremoveFnPos'AnimatedTopFn (S k) (Success tm' (tmLift t))) as [| w2 |] eqn:Hw2;
          simpl in Heq.
        - injection Heq as <-. apply Hf.
        - destruct w2 as [s1|s2 ty2 b2|a1 a2| |v2|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
            simpl in Heq; try (injection Heq as <-; apply Hf).
          destruct (andb (tmChkNoExtraCstrs v2) (isValueFn (tmPushPlain v2))) eqn:Hchk;
            simpl in Heq; injection Heq as <-.
          + assert (Htm : evalTransparentSigma2AnimatedTopFn (S k) (Success tm t) f =
                           Success tm (tsucc (tmTransparentSigmaPushBody f v2))).
            { unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                     evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
              cbn [tmLift]. rewrite Hw2. reflexivity. }
            apply andb_prop in Hchk as [Hchk1 Hchk2].
            assert (Hpush : forall (g : tm -> tm) (w : tm'), tmChkNoExtraCstrs w = true ->
                            tmTransparentSigmaPushBody g w = tmPushPlain w).
            { clear. intros g w. induction w; simpl; intros H; try reflexivity; try discriminate.
              - rewrite IHw; [reflexivity | exact H].
              - destruct (tmChkNoExtraCstrs w1) eqn:E1; destruct (tmChkNoExtraCstrs w2) eqn:E2;
                  simpl in H; try discriminate.
                rewrite (IHw1 eq_refl), (IHw2 eq_refl). reflexivity.
              - rewrite IHw; [reflexivity | exact H].
              - rewrite IHw; [reflexivity | exact H].
              - destruct (tmChkNoExtraCstrs w1) eqn:E1; destruct (tmChkNoExtraCstrs w2) eqn:E2;
                  destruct (tmChkNoExtraCstrs w3) eqn:E3; simpl in H; try discriminate.
                rewrite (IHw1 eq_refl), (IHw2 eq_refl), (IHw3 eq_refl). reflexivity.
              - rewrite IHw; [reflexivity | exact H]. }
            eapply E_PredSucc. split.
            * rewrite (Hpush f v2 Hchk1). exact Hchk2.
            * apply (IH (S k)). lia. exact Htm.
          + apply Hf.
        - injection Heq as <-. apply Hf. }
      destruct (evalremoveFnPos'AnimatedTopFn (S (S k)) (Success tm' (tmLift t))) as [| w1 |] eqn:Hw1;
        simpl in Hanim.
      * apply (Hinner outputTm Hanim).
      * destruct w1 as [s1|s2 ty2 b2|a1 a2| |v1|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
          simpl in Hanim; try (apply (Hinner outputTm Hanim)).
        injection Hanim as <-. apply E_PredZero.
        apply (IH (S (S k))). lia.
        unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
               evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
        cbn [tmLift]. rewrite Hw1. reflexivity.
      * apply (Hinner outputTm Hanim).

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
    + (* n = 9+k: anim_S_tifz fires. CORRECTED anim_S_tifz checks the raw tm'-level
         discriminant shape before any push; see comment on [dispatch_tpred_from_pred]
         and on the [correspondence_soundness_bigstop] tifz branch. *)
      rewrite anim_S_tifz in Hanim.
      (* Whenever the IfzZero check doesn't fire, the "IfzSucc or bail out" structure
         is identical regardless of why; factor it once (mirrors CSB's tifz branch). *)
      assert (Hinner : forall outputTm2,
        match evalremoveFnPos'AnimatedTopFn (S k) (Success tm' (tmLift tdisc)) with
        | Success (tsucc' vn') =>
            if andb (tmChkNoExtraCstrs vn') (isValueFn (tmPushPlain vn'))
            then match evalremoveFnPos'AnimatedTopFn (S k) (Success tm' (tmLift t2)) with
                 | Success x => Success tm (tmTransparentSigmaPushBody f x)
                 | _ => NoMatch tm
                 end
            else Success tm (f (tifz tdisc t1 t2))
        | _ => Success tm (f (tifz tdisc t1 t2))
        end = Success tm outputTm2 -> eval (tifz tdisc t1 t2) outputTm2).
      { intros outputTm2 Heq.
        (* Extract + rewrite every sub-evaluation into Heq BEFORE any [simpl] touches it —
           see the comment on the [correspondence_soundness_bigstop] tapp branch. *)
        destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) (tmLift tdisc)) as [w2 Hw2].
        rewrite Hw2 in Heq.
        destruct (evalremoveFnPos'AnimatedTopFn_always_success (S k) (tmLift t2)) as [w3 Hw3].
        rewrite Hw3 in Heq.
        destruct w2 as [s1|s2 ty2 b2|a1 a2| |vn'|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
          [ simpl in Heq; injection Heq as <-; apply Hf
          | simpl in Heq; injection Heq as <-; apply Hf
          | simpl in Heq; injection Heq as <-; apply Hf
          | simpl in Heq; injection Heq as <-; apply Hf
          | idtac
          | simpl in Heq; injection Heq as <-; apply Hf
          | simpl in Heq; injection Heq as <-; apply Hf
          | simpl in Heq; injection Heq as <-; apply Hf
          | simpl in Heq; injection Heq as <-; apply Hf
          | simpl in Heq; injection Heq as <-; apply Hf ].
        (* w2 = tsucc' vn' *)
        simpl in Heq.
        destruct (andb (tmChkNoExtraCstrs vn') (isValueFn (tmPushPlain vn'))) eqn:Hchk;
          simpl in Heq.
        + injection Heq as <-.
          apply andb_prop in Hchk as [Hchk1 Hchk2].
          assert (Hpush : forall (g : tm -> tm) (w : tm'), tmChkNoExtraCstrs w = true ->
                          tmTransparentSigmaPushBody g w = tmPushPlain w).
          { clear. intros g w. induction w; simpl; intros H; try reflexivity; try discriminate.
            - rewrite IHw; [reflexivity | exact H].
            - destruct (tmChkNoExtraCstrs w1) eqn:E1; destruct (tmChkNoExtraCstrs w2) eqn:E2;
                simpl in H; try discriminate.
              rewrite (IHw1 eq_refl), (IHw2 eq_refl). reflexivity.
            - rewrite IHw; [reflexivity | exact H].
            - rewrite IHw; [reflexivity | exact H].
            - destruct (tmChkNoExtraCstrs w1) eqn:E1; destruct (tmChkNoExtraCstrs w2) eqn:E2;
                destruct (tmChkNoExtraCstrs w3) eqn:E3; simpl in H; try discriminate.
              rewrite (IHw1 eq_refl), (IHw2 eq_refl), (IHw3 eq_refl). reflexivity.
            - rewrite IHw; [reflexivity | exact H]. }
          (* E_IfzSucc's components are ordered (isValueFn, discriminant-eval, t2-eval) —
             apply it with every existential supplied explicitly, as with E_App above. *)
          apply (E_IfzSucc tdisc (tmTransparentSigmaPushBody f vn') t1 t2
                   (tmTransparentSigmaPushBody f w3)).
          repeat split.
          * rewrite (Hpush f vn' Hchk1). exact Hchk2.
          * apply (IH (S k)). lia.
            unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                   evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
            cbn [tmLift]. rewrite Hw2. reflexivity.
          * apply (IH (S k)). lia.
            unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                   evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
            cbn [tmLift]. rewrite Hw3. reflexivity.
        + injection Heq as <-. apply Hf. }
      destruct (evalremoveFnPos'AnimatedTopFn (S (S k)) (Success tm' (tmLift tdisc))) as [| w1 |] eqn:Hw1;
        simpl in Hanim.
      * apply (Hinner outputTm Hanim).
      * destruct w1 as [s1|s2 ty2 b2|a1 a2| |v1|b3|c1 c2 c3|s3 ty3 b4|m1|s4 n1 n2];
          simpl in Hanim; try (apply (Hinner outputTm Hanim)).
        eapply E_IfzZero. split.
        -- apply (IH (S (S k))). lia.
           unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
                  evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush.
           cbn [tmLift]. rewrite Hw1. reflexivity.
        -- apply (IH (S (S k))). lia. exact Hanim.
      * apply (Hinner outputTm Hanim).

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





(** --- Correspondence via bigstop (intermediate) --------------------------- *)




End PCFBigStep.


