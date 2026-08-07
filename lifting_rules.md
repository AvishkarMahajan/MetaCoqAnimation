# Lifting Rules for `animate_coinductive_with_fn_pos`

## Which relation to derive on

The entire procedure is applied **unchanged** to the **`removeFnPos` version** of the relation (e.g. `evalCmdremoveFnPos`), since that is the relation that actually gets lifted. The original relation (e.g. `evalCmd`) is only used to produce `removeFnPos`; all inputs to the derivation — initial lifting set, seeds, named functions, relation extra ctor — are read from `removeFnPos`.

**What `remove_from_fn_pos` does**: scans constructors for (a) var-app patterns — `tApp (tRel i) args` where a locally-bound function variable is applied to arguments — and (b) closed anonymous lambdas. Each unique pattern gets a named wrapper (`fnApp_N` or `fnLam_N`), and occurrences in constructors are replaced by those wrappers. The relation's type signature and overall constructor structure are otherwise unchanged.

In simple cases (like `evalCmd`) where the function-typed variable `vs` is only ever passed as an *argument* to named constants and never applied as a function head, `removeFnPos` is essentially just a rename. In general it may differ structurally from the original.

---

## Initial Sets

- **Initial lifting set**: types in the signature of `removeFnPos` (inductive → σ2, arrow → arrow lifting set)
- **Seeds for dependency search**: `removeFnPos` signature types PLUS types appearing in equality premises of `removeFnPos`'s constructors

---

## Lifting Set Expansion Rules

These rules both (a) expand the lifting sets and (b) determine what extra constructors appear in the lifted types.

**Scope of "named functions"**: only consider named functions that actually appear in the constructors of `removeFnPos`. Named functions that are in scope but never referenced in any constructor body are ignored.

### a2i
Named function `f` with Ar (arrow, in lifting set) among its inputs and inductive B as output:
- Add B to σ2
- Add `fLiftedCstr` to B' with arg types lifted (σ2 → T', arrow → fnTypeK, else unchanged)

### a2a
Named function `f` with Ar1 (arrow, in lifting set) among its inputs and arrow Ar2 as output:
- Add Ar2 to arrow lifting set
- Add `fLiftedCstr` to fnType for Ar2, with arg types lifted

### i2a
Named function `f` with B (σ2) among its inputs and arrow Ar as output:
- Add Ar to arrow lifting set
- Add `fLiftedCstr` to fnType for Ar, with arg types lifted

### i2i (fn)
Named function `f` with B (σ2) among its inputs and inductive C as output:
- Add C to σ2
- Add `fLiftedCstr` to C' with arg types lifted

### struct σ2→σ2
If F ∈ σ2 and inductive T has a constructor field of type F:
- Add T to σ2
- No extra constructor; T' gets its original constructors structurally lifted

### struct arr→σ2
If Ar ∈ arrow lifting set and inductive T has a constructor field of type Ar:
- Add T to σ2
- No extra constructor; T' gets its original constructors structurally lifted

### relation extra ctor
For the `removeFnPos` relation R with input mode positions (types T_i1, ..., T_ik) and output mode position j (type T_j):
- Add constructor `RAnj : T_i1'' → ... → T_ik'' → T_j'` (or `→ fnTypeK`) to the lifted version of T_j
- Arg types lifted: σ2 → T', arrow → fnTypeK, else unchanged

---

## Key Points

- Constructor fields of a lifted type do NOT automatically get lifted; the implication is bottom-up: if F ∈ σ2 and T has a constructor field of type F → add T to σ2 (not the reverse)
- There is no separate "extra ctor (fn)" rule — a2i/a2a/i2a/i2i(fn) each encode both the lifting set expansion AND the constructor addition
- Arrow-type args in extra constructors use fnTypeK (the named wrapper inductive), not the raw arrow type
- The a2a rule (fn with arrow input AND arrow output) must be checked explicitly

---

## Worked Example: ImpSem evalCmd

Derivation is done on `evalCmdremoveFnPos`, which for this example is essentially a rename of `evalCmd` (no var-app or closed-lambda substitutions occur):

```
evalCmdremoveFnPos : (nat→nat) → cmd → (nat→nat) → Prop
```

Named functions appearing in constructors: `set : (nat→nat) → nat → nat → (nat→nat)`, `evalExp : (nat→nat) → exp → nat`  
(`eqFnexp` is in scope but never appears in any constructor — ignored)

**Initial lifting set** from signature: `arrow = {nat→nat}`, `σ2 = {cmd}`  
**Seeds**: `{nat→nat, cmd}` + `nat` (from equality premise `evalExp vs e = 0`)

### Round 1 — from `nat→nat` in arrow

| Rule | | Effect |
|---|---|---|
| a2i | evalExp: arrow input `nat→nat`, output `nat` | add **nat** to σ2; `evalExpLiftedCstr : fnType0 → exp' → nat'` added to nat' |
| a2a | set: arrow input `nat→nat`, output `nat→nat` | self-loop; `setLiftedCstr : fnType0 → nat' → nat' → fnType0` added to fnType0 |
| struct arr→σ2 | no inductive has `nat→nat` as constructor field | nothing |

`arrow = {nat→nat}`, `σ2 = {cmd, nat}`

### Round 2 — from `nat` in σ2

| Rule | | Effect |
|---|---|---|
| i2a | set: σ2 input `nat`, output `nat→nat` | nat→nat already in arrow |
| i2i (fn) | set output is `nat→nat` (arrow, not inductive) | skip |
| struct σ2→σ2 | `Const : nat → exp`, `Var : nat → exp` | add **exp** to σ2 |

`arrow = {nat→nat}`, `σ2 = {cmd, nat, exp}`

### Round 3 — from `exp` in σ2

| Rule | | Effect |
|---|---|---|
| i2i (fn) | evalExp: σ2 input `exp`, output `nat` | nat already in σ2 |
| struct σ2→σ2 | `While : exp → cmd → cmd`, `Assign : nat → exp → cmd` | cmd already in σ2 |

Fixpoint.

**Final**: `arrow = {nat→nat}`, `σ2 = {cmd, nat, exp}`

**Relation extra ctor**: evalCmdremoveFnPos has input types `(nat→nat, cmd)` and output type `nat→nat` at position 2 → add `evalCmdremoveFnPosAn2 : fnType0 → cmd' → fnType0` to fnType0

### Lifted relation

```
CoInductive evalCmdremoveFnPos' : fnType0 → cmd' → fnType0 → Prop :=
| EvalAssignremoveFnPos' : ∀ (vs' : fnType0) (v' : nat') (e' : exp'),
    evalCmdremoveFnPos' vs' (Assign' v' e') (setliftedFunc vs' v' (evalExpliftedFunc vs' e'))
| EvalSeqremoveFnPos' : ∀ (vs1' vs2' vs3' : fnType0) (c1' c2' : cmd'),
    evalCmdremoveFnPos' vs1' c1' vs2' ∧ evalCmdremoveFnPos' vs2' c2' vs3'
    → evalCmdremoveFnPos' vs1' (Seq' c1' c2') vs3'
| EvalWhileFalseremoveFnPos' : ∀ (vs' : fnType0) (e' : exp') (c' : cmd'),
    evalExpliftedFunc vs' e' = O'
    → evalCmdremoveFnPos' vs' (While' e' c') vs'
| EvalWhileTrueremoveFnPos' : ∀ (vs1' vs2' vs3' : fnType0) (e' : exp') (c' : cmd'),
    evalExpliftedFunc vs1' e' ≠ O'
    ∧ evalCmdremoveFnPos' vs1' c' vs2' ∧ evalCmdremoveFnPos' vs2' (While' e' c') vs3'
    → evalCmdremoveFnPos' vs1' (While' e' c') vs3'
| evalCmdremoveFnPos'Undef : ∀ (vs' : fnType0) (c' : cmd'),
    evalCmdremoveFnPos' vs' c' (evalCmdremoveFnPosAn2 vs' c')
```

**How named functions are substituted** (`sub_ty` in `make_lifted_relation_mind`):

`sub_ty` traverses the entire constructor type — both premise argument types (e.g. equality premises like `evalExp vs e = 0`) and index terms in the return type. The substitution rule is the same everywhere:

- Named function `f` in **application head position** (`tApp (tConst f_kn) args`) → replaced with `fliftedFunc args'`
- Named function `f` as a **value** (not applied), where `type(f)` is lifted to `fnTypeK` → replaced with `fnTypeKCstr f` (the basic embedding constructor, just wraps the original value)
- Named function `f` whose type is not in the lifting set → unchanged

`fnTypeKCstr` (e.g. `fnType0Cstr : (nat→nat) → fnType0`) is the plain embedding constructor. It is distinct from `fLiftedCstr` (e.g. `setLiftedCstr`), which encodes a specific function's lifted call pattern and is added by the a2i/a2a/i2a/i2i rules.

In ImpSem, `evalExp` and `set` both appear only in application position, so both become `liftedFunc` versions.

---

### Lifted types

```
nat'    : O' | S' : nat' → nat' | evalExpLiftedCstr : fnType0 → exp' → nat'

exp'    : Const' : nat' → exp'
        | Var'   : nat' → exp'
        | Plus'  : exp' → exp' → exp'

cmd'    : Assign' : nat' → exp' → cmd'
        | Seq'    : cmd' → cmd' → cmd'
        | While'  : exp' → cmd' → cmd'

fnType0 : fnType0Cstr              : (nat→nat) → fnType0
        | setLiftedCstr            : fnType0 → nat' → nat' → fnType0
        | evalCmdremoveFnPosAn2    : fnType0 → cmd' → fnType0
```
