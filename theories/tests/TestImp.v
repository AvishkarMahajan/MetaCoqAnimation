(** * TestImp: Imperative Language Semantics
    Tests animation of a simple imperative language (Assign / Seq / While).
    Two variants:
    - [ImpSem]:   relation maps initial state to final state
    - [ImpSemTr]: relation maps initial state to a trace (sequence of states) *)

Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.
Require Import Animation.EqualityResolution.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.

Require Import List.
From Stdlib Require Import Streams.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.

Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.

(* ------------------------------------------------------------------ *)
(** ** ImpSem: state → final state *)
Module ImpSem.

CoInductive co_vars : Type :=
| pure        : (nat -> nat) -> co_vars
| undefinedCoV : co_vars.

Definition set (vs : nat -> nat) (v n : nat) : nat -> nat :=
  fun v' => if Nat.eqb v v' then n else vs v'.

Inductive exp : Type :=
| Const : nat -> exp
| Var   : nat -> exp
| Plus  : exp -> exp -> exp.

Fixpoint evalExp (vs : nat -> nat) (e : exp) : nat :=
  match e with
  | Const n     => n
  | Var v       => vs v
  | Plus e1 e2  => evalExp vs e1 + evalExp vs e2
  end.

Inductive cmd : Type :=
| Assign : nat -> exp -> cmd
| Seq    : cmd -> cmd -> cmd
| While  : exp -> cmd -> cmd.

CoInductive evalCmd : co_vars -> cmd -> co_vars -> Prop :=
| EvalAssign     : forall vs' vs v e,
    vs' = pure vs
    -> evalCmd vs' (Assign v e) (pure (set vs v (evalExp vs e)))
| EvalSeq        : forall vs1 vs2 vs3 c1 c2,
    evalCmd vs1 c1 vs2 /\ evalCmd vs2 c2 vs3
    -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs' vs e c,
    vs' = pure vs /\ evalExp vs e = 0
    -> evalCmd vs' (While e c) vs'
| EvalWhileTrue  : forall vs1' vs2' vs3' vs1 e c,
    vs1' = pure vs1 /\ evalExp vs1 e <> 0
    /\ evalCmd vs1' c vs2' /\ evalCmd vs2' (While e c) vs3'
    -> evalCmd vs1' (While e c) vs3'
| EvalUndef      : forall c c', evalCmd c c' undefinedCoV.

Definition evalCmdRest := fun _ : (co_vars * cmd) => undefinedCoV.

MetaRocq Run (animateCoinductive evalCmd <? evalCmd ?>
  [("evalCmd", ([0;1], [2]))] 500).

(** While (var 4 != 0) { var 8 := 8 }, starting with all vars = n+1. *)
Definition prog  := While (Var 4) (Assign 8 (Const 8)).
Definition initFn := pure (fun m : nat => m + 1).

MetaRocq Run (r <- tmEval all
  (Str_nth 25 (evalCmdAnimatedTopFnStream (Success (co_vars * cmd) (initFn, prog)))) ;;
  tmPrint r).

(** While (var 0 != 0) { var 8 := 9 }, starting with all vars = 0 — terminates immediately. *)
Definition prog'  := While (Var 0) (Assign 8 (Const 9)).
Definition initFn' := pure (fun _ : nat => 0).

MetaRocq Run (r <- tmEval all
  (Str_nth 25 (evalCmdAnimatedTopFnStream (Success (co_vars * cmd) (initFn', prog')))) ;;
  tmPrint r).

End ImpSem.

(* ------------------------------------------------------------------ *)
(** ** ImpSemTr: state → execution trace *)
Module ImpSemTr.

CoInductive co_vars : Type :=
| empty        : co_vars
| pure         : (nat -> nat) -> co_vars
| undefinedCoV : co_vars.

CoInductive co_vars_tr : Type :=
| coVNil         : co_vars_tr
| covSeq         : co_vars -> co_vars_tr -> co_vars_tr
| undefinedCoVTr : co_vars_tr.

Definition set (vs : nat -> nat) (v n : nat) : nat -> nat :=
  fun v' => if Nat.eqb v v' then n else vs v'.

Inductive exp : Type :=
| Const : nat -> exp
| Var   : nat -> exp
| Plus  : exp -> exp -> exp.

Fixpoint evalExp (vs : nat -> nat) (e : exp) : nat :=
  match e with
  | Const n    => n
  | Var v      => vs v
  | Plus e1 e2 => evalExp vs e1 + evalExp vs e2
  end.

Inductive cmd : Type :=
| Assign : nat -> exp -> cmd
| Seq    : cmd -> cmd -> cmd
| While  : exp -> cmd -> cmd.

CoInductive evalCmd : co_vars -> cmd -> co_vars_tr -> Prop :=
| EvalEmpty      : forall c', evalCmd empty c' coVNil
| EvalAssign     : forall vs' vs v e,
    vs' = pure vs
    -> evalCmd vs' (Assign v e) (covSeq (pure (set vs v (evalExp vs e))) coVNil)
| EvalSeq        : forall vs1 vs2 vs2' vs3 vs4 c1 c2,
    evalCmd vs1 c1 vs2 /\ last vs2 vs2' /\ appTr vs2 vs3 vs4
    /\ evalCmd vs2' c2 vs3
    -> evalCmd vs1 (Seq c1 c2) vs4
| EvalWhileFalse : forall vs' vs e c,
    vs' = pure vs /\ evalExp vs e = 0
    -> evalCmd vs' (While e c) (covSeq vs' coVNil)
| EvalWhileTrue  : forall vs1' vs2' vs2'' vs3' vs1 vs4 e c,
    vs1' = pure vs1 /\ evalExp vs1 e <> 0
    /\ evalCmd vs1' c vs2' /\ last vs2' vs2''
    /\ evalCmd vs2'' (While e c) vs3' /\ appTr vs2' vs3' vs4
    -> evalCmd vs1' (While e c) vs4
| EvalUndef      : forall c c', evalCmd c c' undefinedCoVTr
with last : co_vars_tr -> co_vars -> Prop :=
| lastEmpty : last coVNil empty
| lastNil   : forall c c1, c1 = c -> last (covSeq c coVNil) c1
| lastSeq   : forall c c' ctr, last ctr c -> last (covSeq c' ctr) c
| lastUndef : forall ctr, last ctr undefinedCoV
with appTr : co_vars_tr -> co_vars_tr -> co_vars_tr -> Prop :=
| appNil  : forall ctr ctr', ctr' = ctr -> appTr coVNil ctr ctr
| appSeq  : forall c c1 ctr ctr' ctr'',
    appTr ctr ctr' ctr'' /\ c1 = c -> appTr (covSeq c ctr) ctr' (covSeq c1 ctr'')
| appUndef : forall ctr ctr1, appTr ctr ctr1 undefinedCoVTr.

Definition eqFnco_vars (c c1 : co_vars) : bool :=
  match c with empty => match c1 with empty => true | _ => false end | _ => false end.

Definition eqFnco_vars_tr (c c1 : co_vars_tr) : bool :=
  match c with coVNil => match c1 with coVNil => true | _ => false end | _ => false end.

Definition evalCmdRest := fun _ : (co_vars * cmd) => undefinedCoVTr.
Definition lastRest     := fun _ : co_vars_tr => undefinedCoV.
Definition appTrRest    := fun _ : (co_vars_tr * co_vars_tr) => undefinedCoVTr.

MetaRocq Run (animateCoinductive evalCmd <? evalCmd ?>
  [("evalCmd", ([0;1], [2])); ("last", ([0], [1])); ("appTr", ([0;1], [2]))] 500).

(** While (var 4 != 0) { var 8 := 8 }, all vars start at n+1 — diverges. *)
Definition prog   := While (Var 4) (Assign 8 (Const 8)).
Definition add1   := fun m : nat => m + 1.
Definition initFn := pure add1.

MetaRocq Run (r <- tmEval all
  (Str_nth 30 (evalCmdAnimatedTopFnStream (Success (co_vars * cmd) (initFn, prog)))) ;;
  tmPrint r).

(** Rotate registers: var4←var3, var3←var2, var2←var1, var1←var0. *)
Definition prog'   :=
  While (Var 4) (Seq (Assign 4 (Var 3)) (Seq (Assign 3 (Var 2))
    (Seq (Assign 2 (Var 1)) (Assign 1 (Var 0))))).
Definition initFn' := pure (fun m : nat => m).

MetaRocq Run (r <- tmEval all
  (Str_nth 40 (evalCmdAnimatedTopFnStream (Success (co_vars * cmd) (initFn', prog')))) ;;
  tmPrint r).

End ImpSemTr.
