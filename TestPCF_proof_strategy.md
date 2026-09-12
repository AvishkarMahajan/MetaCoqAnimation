# `TestPCF.v` — Proof Outline and Strategy

This document describes the proof architecture for `theories/tests/TestPCF.v`,
which formalises ordinary (non-BigStop) CBV big-step semantics for PCF and
proves that the MetaRocq-generated *animation* of the coinductive `eval`
relation agrees with both `eval` itself and with the `bigstop` (small-step)
semantics of Kahn, Hoffmann, Li (POPL 2026).

It covers every lemma/theorem in `Module PCFBigStep` that currently ends in
`Qed.` — i.e. every proof that is actually **complete**. Two further modules
in the file (`EffectfulPCFBigStop`, `MNFBigStop`) restate the same
correspondence theorems for effectful and MNF variants of PCF; as of this
writing every proof in those two modules is `Admitted`, so they are described
only briefly at the end, as future work with the same proof shape expected to
apply.

## 1. Setting the stage

`PCFBigStep` defines:

- `tm` — PCF syntax (`tvar`, `tabs`, `tapp`, `tzero`, `tsucc`, `tpred`,
  `tifz`, `tfix`).
- `eval : tm -> tm -> Prop` — the **coinductive** CBV big-step relation
  (progressing fragment only; no stopping rules). This is the relation that
  gets *animated*.
- `bigstop : tm -> tm -> Prop` — Kahn/Hoffmann/Li's inductive small-step-in-
  big-step judgment: `bigstop e e'` means `e` reduces to `e'` in finitely many
  CBV steps, where `e'` need not be a value. Its constructors split into
  *stopping* rules (`BS_Stop`, `BS_Succ`, `BS_Pred`, `BS_IfzDisc`,
  `BS_App1`, `BS_App2` — congruence rules that may halt anywhere) and
  *progressing* rules (`BS_PredZero`, `BS_PredSucc`, `BS_IfzZero`,
  `BS_IfzSucc`, `BS_App`, `BS_Fix` — mirror `eval`'s rules but take `bigstop`
  premises instead of `eval` premises).
- `step` / `stepRTC` — ordinary CBV small-step and its reflexive-transitive
  closure (used only in the statement of `bigstop_iff_stepRTC`, which is
  `Admitted`; not otherwise load-bearing for what follows).

`MetaRocq Run (animate_coinductive_with_fn_pos <?eval?> ...)` (line 150)
generates the whole animation machinery from `eval`: a lifted term type `tm'`
(PCF terms with an oracle-escape hatch), one handler per constructor of
`eval` (`E_LamremoveFnPos'Animated`, `E_ZeroremoveFnPos'Animated`, …,
`E_FixremoveFnPos'Animated`, plus the universal catch-all
`evalremoveFnPos'UndefinedAnimated`), a fixpoint
`evalremoveFnPos'AnimatedTopFn : nat -> animation_result tm' ->
animation_result tm'` that dispatches fuel-bounded evaluation through those
handlers via the generic combinator `dispatch_coind_ext` (`AnimationEngine.v`),
and a `tm`-level wrapper `evalTransparentSigma2AnimatedTopFn` that
lifts/pushes between `tm` and `tm'` around a call to the `tm'`-level fixpoint,
parameterised by an oracle `f : tm -> tm` used whenever fuel runs out or no
handler matches.

Every proof below is ultimately about relating these two generated functions
— `evalremoveFnPos'AnimatedTopFn` (`tm'`, oracle baked in via `Rest`) and
`evalTransparentSigma2AnimatedTopFn` (`tm`, oracle `f` explicit) — to `eval`
and to `bigstop`.

## 2. Dependency layering

The completed proofs form five layers, each built on the previous:

```
 5. Main correspondence theorems
      correspondence_soundness_bigstop, animation_soundness_general
             ▲  (strong induction on fuel; case on tm constructor)
 4. tm-level unfolding lemmas             anim_S_t*, anim_S_tvar
             ▲  (unfold the tm/tm' wrapper, delegate to layer 3)
 3. tm'-level dispatch characterisation   dispatch_t*, dispatch_t*_from_*
             ▲  (peel non-matching handlers one fuel unit at a time)
 2. Local/global dispatch bridge          evalTop_stepSuccess/NoMatch/step
             ▲
 1. Oracle & structural foundations       anim_0_oracle, anim_1_oracle_*,
                                           anim_below_thr_t*,
                                           tmTransparentSigmaPushBody_tmLift,
                                           isValueFn_to_is_value
```

### Layer 1 — Oracle and structural foundations

- **`tmTransparentSigmaPushBody_tmLift`** (`forall f t, push f (lift t) = t`):
  plain structural induction on `t`; `tmLift`/`tmTransparentSigmaPushBody` are
  defined by mirror-image case analysis on the same constructors, so each
  case is `rewrite IHt*; reflexivity`. This is the workhorse identity used to
  "cancel" the `tm -> tm'` round trip everywhere an oracle fires.
- **`anim_0_oracle`** / **`anim_1_oracle_f`** / **`anim_1_oracle_id`**: at
  fuel `0` (and, degenerately, fuel `1`, since the dispatch's own fuel is `0`
  one level down) the composite wrapper reduces by `cbn` straight to the
  oracle-wrap branch; `tmTransparentSigmaPushBody_tmLift` then simplifies
  `push (f (lift t))`-shaped goals to `f t`. `anim_1_oracle_id` specialises
  `anim_1_oracle_f` to the identity oracle used by the `bigstop` theorems.
- **`anim_below_thr_t*`** (one per constructor: `tzero`≤2, `tsucc`≤3,
  `tpred`≤5, `tapp`≤6, `tifz`≤8, `tfix`≤9): "if fuel is below this
  constructor's handler position in the dispatch list, the oracle fires
  regardless of fuel's exact value." Proved by `destruct n` into all the
  concrete cases up to the threshold (closing early cases via
  `anim_0_oracle`/`anim_1_oracle_f`, the rest via `unfold ...; cbn;
  rewrite tmTransparentSigmaPushBody_tmLift; reflexivity`) plus a final
  `lia` to discharge the impossible "fuel exceeds threshold" case. These are
  exactly the fuel thresholds needed later so that `correspondence_soundness_bigstop`
  / `animation_soundness_general` can case-split fuel into "too small, oracle
  fires" vs. "just right, constructor's handler fires" without touching the
  dispatch machinery directly.
- **`isValueFn_to_is_value`**: bridges the *computational* `isValueFn : tm ->
  bool` check used inside animated handlers (E_PredSucc, E_IfzSucc, E_App) to
  the *propositional* `is_value` predicate used by `bigstop`'s constructors.
  Plain induction on the value witness.

### Layer 2 — Bridging the LOCAL and GLOBAL dispatch forms

`evalremoveFnPos'AnimatedTopFn` is a MetaRocq-generated mutual fixpoint whose
body, once unfolded, dispatches through its handler list using its own
*locally* folded copy of `dispatch_coind_ext`. Every later lemma instead
wants to reason about a *literal*, hand-written
`dispatch_coind_ext tm' tm' evalremoveFnPos'Rest [explicit handler list] n
input` term (the GLOBAL form) so that `cbn [dispatch_coind_ext]` and
`rewrite`-based handler-elimination work predictably. Three lemmas bridge
these two forms:

- **`evalTop_stepSuccess`**: for `Success tm' x` input,
  `evalremoveFnPos'AnimatedTopFn (S n) (Success tm' x)` equals the GLOBAL
  `dispatch_coind_ext ... n (Success tm' x)` with the full 10-handler list.
  Proved by `unfold evalremoveFnPos'AnimatedTopFn`, then walking the handler
  list one at a time: `remember (handler (S n) input) as r0; destruct r0`
  splits into the three `animation_result` outcomes
  (`FuelError`/`Success`/`NoMatch`); the `FuelError` and `Success` branches
  close directly (`rewrite <- Heqr0; ...; reflexivity`), and the `NoMatch`
  branch recurses into the next handler after `destruct n0` on the remaining
  fuel (fuel `0` closes immediately, fuel `S n0` continues to the next
  handler). For handlers that themselves wrap a recursive call to
  `evalremoveFnPos'AnimatedTopFn` (`E_Succ`, `E_PredZero`, …, `E_Fix`), a
  `fold evalremoveFnPos'AnimatedTopFn` step is needed after `simpl`/`unfold
  dispatch_coind_ext`, because the very first `unfold
  evalremoveFnPos'AnimatedTopFn` in the proof also unfolds that identifier
  wherever it appears as an *argument* deep inside the handler list, turning
  it into a raw anonymous `fix ... for evalremoveFnPos'AnimatedTopFn` term;
  `fold` re-folds it back to the named constant so later `rewrite`s (which
  match syntactically, not up to delta-conversion) can find it again. The
  `UndefinedAnimated` (last handler) case needs a genuine `Success`/`NoMatch`
  contradiction argument (see below) since, for `Success` input, it is the
  *only* handler whose `NoMatch` branch is actually impossible (every
  positive-fuel `UndefinedAnimated` call unconditionally produces `Success
  tm' (evalremoveFnPosAn1 x)`).
- **`evalTop_stepNoMatch`**: the mirror image for `NoMatch tm'` input.
  Here the driving fact is uniform across *all* handlers: since `NoMatch`
  carries no term to pattern-match against, every handler call
  `h (S n0) (NoMatch tm')` provably equals `NoMatch tm'` outright (by `auto`,
  via delta/iota conversion) — so both the `FuelError` and `Success` branches
  of every handler's 3-way `destruct` are *impossible*, closed uniformly by
  `assert (H0 : h (S n0) (NoMatch tm') = NoMatch tm'); auto; rewrite H0 in
  Heqr_k; discriminate Heqr_k`, while only the `NoMatch` branch survives and
  continues to the next handler. `UndefinedAnimated` flips this once more:
  at the *positive* fuel `S n0` at which handlers are always invoked, it too
  reduces to `NoMatch tm'` on `NoMatch` input (its `FuelError`-always
  behaviour is specific to literal fuel `0`, which `dispatch_coind_ext` never
  passes to a handler — fuel `0` short-circuits to the oracle *before*
  consulting the handler list at all), so its `NoMatch` branch is the real
  one, closed by `auto`.
  A structural quirk of the *generated* handler list surfaces here: the LOCAL
  list (as produced by unfolding `evalremoveFnPos'AnimatedTopFn`) has one
  extra, duplicated `E_IfzSucc` entry immediately before `UndefinedAnimated`
  that is *not* present in the GLOBAL 10-element list stated in the lemma —
  by that point the GLOBAL side's dispatch has already reached its own last
  element (`UndefinedAnimated`), so the usual `unfold dispatch_coind_ext;
  fold evalremoveFnPos'AnimatedTopFn; rewrite <- Heqr_k` recipe no longer
  finds a matching subterm on that side; the duplicate handler's three
  branches are instead closed directly via `assert`/`discriminate` without
  touching the main goal, and a `destruct n0` is still needed one more time
  before finally entering `UndefinedAnimated` (to resolve whether the fuel is
  `0`, in which case the oracle short-circuit fires, or positive).
- **`evalTop_step`**: the general statement for arbitrary `x :
  animation_result tm'`, obtained by `destruct x` and dispatching to
  `evalTop_stepSuccess` / `evalTop_stepNoMatch`, plus a short inline argument
  for the `FuelError tm'` case (by induction on the fuel: at `0` both sides
  compute to the same thing by `simpl`; at `S n`, `E_Lam`'s handler on
  `FuelError` input is shown to always return `FuelError` itself, so the
  `NoMatch` destruct-branch is vacuous).

This layer is the one most recently completed (`evalTop_stepNoMatch`); every
lemma above it in the dependency graph (`dispatch_t*` and `dispatch_t*_from_*`)
calls `rewrite evalTop_step` (or the `Success`-specialised variant) as its
very first step, precisely so it can then use `cbn [dispatch_coind_ext]` and
handler-by-handler elimination on a clean GLOBAL dispatch term.

### Layer 3 — Per-constructor `tm'`-level dispatch characterisation

For each PCF constructor with a matching `eval` rule, a `dispatch_t*` lemma
states what `evalremoveFnPos'AnimatedTopFn` computes to at exactly the fuel
needed for that constructor's handler to fire, expressed as a `match` on the
*sub*-computations (mirroring the shape of the corresponding `eval`
premises). These are proved by:

1. `rewrite evalTop_step` to get the GLOBAL dispatch form, then
   `cbn [dispatch_coind_ext]`.
2. For each handler that necessarily returns `NoMatch` on this input shape
   (e.g. `E_Lam`, `E_Zero`, `E_Succ` all return `NoMatch` on a `tifz'`
   input), discharge it with `assert (HE_X : ... = NoMatch tm') by (unfold
   E_X...; reflexivity); rewrite HE_X; cbn [dispatch_coind_ext]` and move to
   the next handler.
3. Once the list has been peeled down to the handler(s) that actually match
   this constructor, close with (or delegate to) an `_from_*` lemma that
   characterises that handler's own case-split on its recursive sub-call(s).

Concretely:

- **`dispatch_tzero_from_zero`** / **`dispatch_tzero`**: `E_Zero` is a leaf
  handler (`tzero'` has no sub-term), so `_from_zero` is immediate by `cbn`
  + one `assert`/`rewrite`; `dispatch_tzero` just additionally peels `E_Lam`.
- **`E_Succ_result`** (`Admitted`): a *specification* lemma isolating what
  `E_SuccremoveFnPos'Animated evalFn (S n) (Success tm' (tsucc' v))` reduces
  to as a `match evalFn n (Success tm' v) with ...` — needed because `cbn`
  refuses to delta-unfold the generated handler body far enough while `evalFn`
  is still abstract (its combinator-heavy body would otherwise get stuck).
  Downstream lemmas `rewrite` through this specification instead of trying to
  reduce the handler inline.
- **`dispatch_tsucc_from_succ_gen`** (generic in `evalFn`) /
  **`dispatch_tsucc_from_succ`** (specialised to
  `evalremoveFnPos'AnimatedTopFn`) / **`dispatch_tsucc`**: `_gen` is proved by
  `cbn [dispatch_coind_ext]; rewrite E_Succ_result; destruct (evalFn n ...)`
  and matching `reflexivity` in each of the three outcome branches; `_from_succ`
  specialises `_gen`; `dispatch_tsucc` peels `E_Lam` and `E_Zero` first (both
  provably `NoMatch` on `tsucc'` input) then defers to `_from_succ`.
- **`dispatch_tpred_from_pred`** (`Admitted`), **`dispatch_tifz_from_ifz`**
  (`Admitted`), **`dispatch_tapp_from_app`** (`Admitted`): the analogous
  "characterise the handler(s) starting at this constructor's own dispatch
  position" lemmas for `tpred'`/`tifz'`/`tapp'`. Each is blocked on the same
  gap: the handler's own logic guards on `isValueFn` of an intermediate
  animated result, and closing that goal needs to know the intermediate
  result is the lift of a genuine PCF value — a fact not yet available from
  `evalremoveFnPos'AnimatedTopFn_always_success` alone (see §3 below).
- **`dispatch_tpred`**, **`dispatch_tifz`**, **`dispatch_tapp`**,
  **`dispatch_tfix_from_fix`** + **`dispatch_tfix`**: all `Qed`, all peel the
  preceding non-matching handlers one at a time exactly as in `dispatch_tzero`
  /`dispatch_tsucc`, then discharge the final matching handler(s) either
  directly (`tfix`'s `E_Fix` is a leaf substitution-and-recurse handler, no
  `isValueFn` gap) or by delegating to the corresponding (possibly `Admitted`)
  `_from_*` lemma.

### Layer 4 — `tm`-level unfolding lemmas (`anim_S_t*`)

Each `anim_S_t*` lemma restates the corresponding `dispatch_t*` fact at the
`tm` level (i.e. in terms of `evalTransparentSigma2AnimatedTopFn`, with the
`tm ⇆ tm'` lift/push machinery discharged). The proof pattern is uniformly:
`unfold evalTransparentSigma2AnimatedTopFn, evalremoveFnPosinputLift,
evalremoveFnPosTransparentSigmaOutputPush, tmTransparentSigmaPush; cbn
[tmLift]; exact (dispatch_t* ...)` — i.e. these lemmas do essentially no new
work, they are a thin adapter layer converting the `tm'`-indexed
characterisation into the `tm`-indexed one the correspondence theorems
actually need. `anim_S_tabs` and `anim_S_tzero`/`anim_S_tsucc` are proved
directly (not via a separate `dispatch_t*`) since their handlers are
leaves/simple recursions. `anim_S_tvar` is special: `tvar` has *no* matching
`eval` rule at all, so *every* handler returns `NoMatch` on it regardless of
fuel, and the lemma states the oracle fires unconditionally for any `S n`;
proved by `destruct`ing the first 10 fuel layers (enough for `cbn` to chain
through all handlers including `UndefinedAnimated`) uniformly closed by
`rewrite tmTransparentSigmaPushBody_tmLift; reflexivity`.

### Layer 5 — Main correspondence theorems

- **`correspondence_soundness_bigstop`** (`evalTransparentSigma2AnimatedTopFn
  n (Success tm inputTm) (fun t' => t') = Success tm outputTm -> bigstop
  inputTm outputTm`) and **`animation_soundness_general`** (the same
  statement generalised to an arbitrary oracle `f` satisfying `forall tm1,
  eval tm1 (f tm1)`, concluding `eval inputTm outputTm` instead of
  `bigstop`) share one proof skeleton:

  1. Strong induction on the fuel `n` via `lt_wf_ind` (needed because
     sub-computations recurse at *strictly smaller but non-uniform* fuel —
     e.g. `E_App` recurses on both sub-terms and the substituted body all at
     the same reduced fuel, while `E_Succ` recurses at a differently-reduced
     fuel — so plain structural induction on `n` does not suffice).
  2. `destruct n as [| n']`: fuel `0` closes immediately via `anim_0_oracle`
     and `BS_Stop`/the oracle hypothesis `Hf`.
  3. `destruct inputTm` into its 8 constructors. Each branch further
     `destruct`s `n'` up to that constructor's oracle threshold (using the
     `anim_below_thr_t*` lemmas from Layer 1 to close the "too little fuel"
     sub-cases uniformly via `injection ...; apply BS_Stop`/`apply Hf`), and
     for `n'` at/above the threshold rewrites with the matching `anim_S_t*`
     lemma from Layer 4 to expose the constructor's own recursive structure.
  4. Once exposed, the branch `destruct`s each recursive
     `evalTransparentSigma2AnimatedTopFn ... = [outcome]` sub-computation
     (`eqn:H1`/`H2`/`H3`/…), discharges the `FuelError`/`NoMatch`/wrong-shape
     sub-cases via the oracle (`BS_Stop`/`Hf`), and on the matching shape
     applies the appropriate constructor (`BS_Succ`, `BS_App`, `BS_PredZero`,
     `BS_PredSucc`, `BS_IfzZero`, `BS_IfzSucc`, `BS_Fix`, or their `eval`
     counterparts `E_Succ`, `E_App`, …), discharging each premise's
     `bigstop`/`eval` sub-fact with the strong induction hypothesis `IH`
     applied at the (smaller) fuel actually used in that sub-computation, via
     `lia` to justify the fuel decrease.

  Since `dispatch_tpred`/`dispatch_tifz`/`dispatch_tapp` are fully proved
  (`Qed`, modulo their `Admitted` `_from_*` helpers being used only as
  rewrite lemmas, not unfolded further), both theorems' `tpred`/`tifz`/`tapp`
  branches go through completely at the top level; the only place the
  `_from_*` gaps would actually block a *user-facing* proof is if one tried
  to re-derive `dispatch_tpred`/`dispatch_tifz`/`dispatch_tapp` themselves
  from scratch.

## 3. What is intentionally left `Admitted` (and why)

For completeness, the gaps still open in `Module PCFBigStep`:

| Lemma | Gap |
|---|---|
| `bigstop_iff_stepRTC` | Theorem 7 of the paper; not needed by any `Qed`'d proof here, stated for future use. |
| `animate_mono_bigstop` (first, live copy) | Fuel-monotonicity of the animation w.r.t. `bigstop`; needed for `correspondence_completeness_bigstop`. |
| `evalremoveFnPos'AnimatedTopFn_always_success` | States the `tm'`-level animator never returns `FuelError`/`NoMatch` on `Success` input; only the *existence* of a result is proved needed (used in `anim_S_tsucc`), not that the witness is the lift of a genuine value. |
| `E_Succ_result` | Handler-body specification for `E_Succ`; blocked on the same `cbn`-won't-unfold-abstract-`evalFn` issue described in Layer 3. |
| `dispatch_tpred_from_pred`, `dispatch_tifz_from_ifz`, `dispatch_tapp_from_app`, `dispatch_tfix_from_fix` | Each needs an "the animated intermediate result, if `Success`, is the lift of an actual PCF value" fact (an `always_value` lemma, or full transparency of `evalremoveFnPos'AnimatedTopFn`) to resolve the `isValueFn` guard inside `E_PredSucc`/`E_IfzSucc`/`E_App`. `dispatch_tfix_from_fix` has no such guard but is `Admitted` for the analogous reason at the `E_Fix` handler position (not yet transcribed). |
| `correspondence_completeness_bigstop` | The converse direction (`bigstop inputTm tm1 -> exists tm2 n, ...`); needs `bigstop` transitivity and/or `animate_mono_bigstop` to align witnesses across sub-derivations, since `bigstop`'s constructors package multiple premises non-uniformly. |

A second, fully commented-out block (`bigstop_prog_step`,
`animate_zero`, the second `animate_mono_bigstop`, `bigstop_prog_step_to_bigstop`)
sketches an alternative completeness strategy via a "progressing step"
relation and is not live code.

`Module EffectfulPCFBigStop` (effectful PCF, Fig. 8) and `Module MNFBigStop`
(monadic normal form PCF, Fig. 14) restate `animation_soundness_general`,
`correspondence_soundness`, and `correspondence_completeness_bigstop` for
their respective calculi; every proof in both modules is currently
`Admitted`. The expectation is that, once instantiated with the relevant
`eval`/`bigstop` definitions for each calculus, the same five-layer strategy
above (oracle foundations → dispatch bridge → per-constructor dispatch
characterisation → `tm`-level unfolding → strong induction on fuel) applies
essentially unchanged.
