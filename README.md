# MetaRocqAnimation

A Rocq library that automatically compiles inductive `Prop` relations into executable functions at elaboration time using MetaRocq's `TemplateMonad`. You declare an inductive relation and a mode (which arguments are inputs vs outputs), and the library generates a function that evaluates the relation.

## What it does

Given a relation like:

```coq
Inductive add : nat -> nat -> nat -> Prop :=
| add_zero : forall (n : nat), add 0 n n
| add_succ : forall (m n k : nat), add m n k -> add (S m) n (S k).
```

and a mode declaration `([0;1], [2])` (arguments 0 and 1 are inputs, argument 2 is output), the library generates `addAnimatedTopFn : nat -> animation_result nat -> animation_result nat` at compile time. No runtime interpretation, no external tools — the function is produced by Rocq's elaborator and is callable like any other definition.

### Result type

All generated functions return `animation_result A`:

```coq
Inductive animation_result (A : Type) : Type :=
| Success    : A -> animation_result A   (* derivation found, output is the value *)
| NoMatch    : animation_result A        (* no rule applies — relation is false *)
| FuelError  : animation_result A.       (* recursion limit reached *)
```

### Calling convention

Generated functions take a fuel argument and an `animation_result` wrapping the inputs:

```coq
addAnimatedTopFn 100 (Success (nat * nat) (3, 2)) = Success nat 5
```

The `Success (nat * nat) (3, 2)` input wraps `(3, 2)` as "these inputs are known". Using the result type for both input and output lets animated functions compose directly:

```coq
(* Chain: compute (3+2), then check if (result, 4) adds to 9 *)
addAnimatedTopFn 100 (addAnimatedTopFn 100 (Success (nat * nat) (3, 2)) >>= fun k => Success (nat * nat) (k, 4))
```

## Animating a relation

```coq
Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.
Require Import Animation.EqualityResolution.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.
Import MetaRocqNotations.

(* 1. Define your relation *)
Inductive add : nat -> nat -> nat -> Prop :=
| add_zero : forall (n : nat), add 0 n n
| add_succ : forall (m n k : nat), add m n k -> add (S m) n (S k).

(* 2. Run the animation *)
MetaRocq Run (animate_inductive add <?add?> [("add", ([0;1], [2]))] 100).

(* 3. Call the generated function *)
Compute addAnimatedTopFn 100 (Success (nat * nat) (3, 2)).
(* ==> Success nat 5 *)
```

The mode list `[("add", ([0;1], [2]))]` maps each predicate name to a pair `(input_positions, output_positions)`. Position indices are 0-based, counting only the non-uniform arguments (not the `forall`-quantified type parameters).

## Mutual recursion

Mutually defined relations are animated together by listing all of them in the mode map:

```coq
Inductive even : nat -> bool -> Prop :=
| even0    : even 0 true
| evenSucc : forall (w : nat), odd w true -> even (S w) true
with odd : nat -> bool -> Prop :=
| oddSucc  : forall (w : nat), even w true -> odd (S w) true.

MetaRocq Run (animate_inductive even <?even?>
  [("even", ([0], [1])); ("odd", ([0], [1]))] 100).

(* evenAnimatedTopFn and oddAnimatedTopFn are both generated *)
Compute evenAnimatedTopFn 30 (Success nat 4).  (* ==> Success bool true  *)
Compute evenAnimatedTopFn 30 (Success nat 3).  (* ==> Success bool false, i.e. NoMatch bool *)
```

## Equality functions

For relations whose clauses involve equality guards between user-defined types, you must provide a boolean equality function named `eqFn<TypeName>`. For example, if your relation mentions `ty`, define:

```coq
Fixpoint decEqTy : forall (t1 t2 : ty), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Definition eqFnty (t1 t2 : ty) : bool :=
  if decEqTy t1 t2 then true else false.
```

The `eqFn` prefix is the convention the library uses to look up the equality function for each type at animation time.

## Fuel

The first argument to every generated function is a fuel count that bounds recursion depth. A `FuelError` result means the fuel was exhausted before a derivation was found or disproved — increase the fuel or inspect whether the relation terminates. A fuel of 50–100 is sufficient for most small examples.

## Building

You need the `rocq-released` opam registry:

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
```

Install dependencies and build:

```sh
opam install . --deps-only
make
```

Requires Rocq ≥ 9.0.0 and `rocq-metarocq`.

## Running tests

```sh
./run_tests.sh
```

Or build individual test files:

```sh
make -f Makefile.coq theories/tests/TestNat.vo theories/tests/TestList.vo theories/tests/TestSTLC.vo
```

## Project structure

| File | Contents |
|---|---|
| `theories/MetaRocqUtils.v` | Core types (`animation_result`, `Stream`), term-building utilities, and combinators |
| `theories/PatternCompilation.v` | Pattern matching compilation: translates constructor patterns into equality constraints |
| `theories/EqualityResolution.v` | Equality analysis: determines which equalities become let-bindings vs guards |
| `theories/AnimationDispatch.v` | Clause sorting and the top-level dispatch over multiple clauses |
| `theories/AnimationEngine.v` | Main compilation driver: `animate_inductive`, `animate_coinductive`, fixpoint construction |
| `theories/tests/TestNat.v` | Tests for natural number relations (addition, multiplication, even/odd, ≤) |
| `theories/tests/TestList.v` | Tests for list relations (append, length, suffix, reverse) |
| `theories/tests/TestSTLC.v` | Tests for STLC typing and small-step reduction |
| `theories/tests/TestLambdaCalc.v` | Additional lambda calculus tests |
| `theories/tests/TestStack.v` | Tests for a small-step stack machine relation |
| `theories/tests/TestImp.v` | Tests for imperative language semantics (Assign/Seq/While) |
| `theories/tests/TestCoinductive.v` | Tests for coinductive stream relations |

## Examples in detail

### STLC typing (mutual induction, auxiliary functions)

```coq
Inductive typing : list ty -> tm -> ty -> Prop :=
| TCon : forall (n : nat) (cxt : list ty), typing cxt (tcon n) TBool
| TApp : forall (e1 e2 : tm) (t1 t2 : ty) (cxt : list ty),
    typing cxt e2 t1 /\ typing cxt e1 (TArrow t1 t2) ->
    typing cxt (tapp e1 e2) t2
...

MetaRocq Run (animate_inductive typing <?typing?>
  [("typing", ([0;1], [2])); ("lookup", ([0;1], [2]))] 100).

(* Type an application — checks argument type matches parameter type *)
Compute typingAnimatedTopFn 50
  (Success (list ty * tm) ([], tapp (tabs TBool (tvar 0)) (tcon 3))).
(* ==> Success ty TBool *)

(* Ill-typed: type mismatch in application *)
Compute typingAnimatedTopFn 50
  (Success (list ty * tm) ([], tapp (tabs (TArrow TBool TBool) (tvar 0)) (tcon 5))).
(* ==> NoMatch ty *)
```

### STLC small-step reduction (calls a Fixpoint for substitution)

```coq
Fixpoint subst (x : string) (s : tm) (t : tm) : tm := ...

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall (z : string) (T : ty) (t w : tm),
    step (tapp (tabs z T t) w) (subst z w t)
| ST_IfTrue  : forall (t1 t2 : tm), step (tif ttrue  t1 t2) t1
| ST_IfFalse : forall (t1 t2 : tm), step (tif tfalse t1 t2) t2
| ST_If      : forall (t1 t1' t2 t3 : tm),
    step t1 t1' -> step (tif t1 t2 t3) (tif t1' t2 t3).

MetaRocq Run (animate_inductive step <?step?> [("step", ([0], [1]))] 100).

Compute stepAnimatedTopFn 50 (Success tm (tif ttrue ttrue tfalse)).
(* ==> Success tm ttrue *)

Compute stepAnimatedTopFn 50 (Success tm ttrue).
(* ==> NoMatch tm  (ttrue is a value, no step applies) *)
```

## Limitations

- **Mode must be deterministic**: the relation should define a function (at most one output per input). Non-deterministic relations may return only the first derivation found.
- **Termination via fuel**: the library does not verify termination; use adequate fuel and check for `FuelError`.
- **Equality functions must be provided**: for user-defined inductive types used in guard positions, `eqFn<TypeName>` must be in scope before the `MetaRocq Run` call.
- **Type parameters**: polymorphic relations are supported, but the mode indices count only the non-type arguments.
