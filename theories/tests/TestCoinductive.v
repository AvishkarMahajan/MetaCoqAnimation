(** * TestCoinductive: Coinductive Stream Relations
    Tests animation of coinductive relations over infinite streams.
    Covers integration, zipping, equality, filtering, and length. *)

Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.
Require Import Animation.EqualityResolution.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.

From Stdlib Require Import List.
From Stdlib Require Import Streams.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.

Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.


(** A stream of naturals, with explicit undefined and nil sentinels. *)
CoInductive stream : Type :=
| undefinedStm : stream
| nil : stream
| Seq : nat -> stream -> stream.

CoInductive counter : Type :=
| incr : counter -> counter.

Definition eqFncounter : counter -> counter -> bool := fun _ _ => true.

Definition eqFnstream (s1 s2 : stream) : bool :=
  match s1 with
  | nil => match s2 with nil => true | _ => false end
  | _   => false
  end.

CoFixpoint from (n : nat) : stream := Seq n (from (S n)).

(* ------------------------------------------------------------------ *)
(** ** Integrate *)

CoInductive Integrate : stream -> stream -> Prop :=
| integNil : Integrate nil nil
| integ : forall s2 s3 n s5, Integrate s2 s3 /\ addStm n s3 s5 -> Integrate (Seq n s2) (Seq n s5)
| integU : forall s, Integrate s undefinedStm
with addStm : nat -> stream -> stream -> Prop :=
| addStmNil : forall m, addStm m nil nil
| plusm : forall m s1 n s2, addStm m s1 s2 -> addStm m (Seq n s1) (Seq (m + n) s2)
| addStmU : forall m s, addStm m s undefinedStm.

Definition IntegrateRest := fun _ : stream => undefinedStm.
Definition addStmRest := fun _ : (nat * stream) => undefinedStm.

MetaRocq Run (animate_coinductive Integrate <? Integrate ?>
  [("Integrate", ([0], [1])); ("addStm", ([0;1], [2]))] 100).

(** Integrate [4, 5, 6, …] gives [4, 9, 15, …] (prefix sums). *)
MetaRocq Run (r <- tmEval all
  (Str_nth 15 (IntegrateAnimatedTopFnStream (Success stream (from 4)))) ;;
  tmPrint r).

MetaRocq Run (r <- tmEval all
  (Str_nth 15 (IntegrateAnimatedTopFnStream (Success stream (Seq 4 (Seq 3 (Seq 2 nil)))))) ;;
  tmPrint r).

(* ------------------------------------------------------------------ *)
(** ** Zip two streams *)

CoInductive zipSt : stream -> stream -> stream -> Prop :=
| zip : forall n m s1 s2 s3 s4 s5 s6,
    s1 = Seq n s2 /\ s3 = Seq m s4 /\ zipSt s2 s4 s5 /\ s6 = Seq n (Seq m s5)
    -> zipSt s1 s3 s6.

Definition zipStRest := fun _ : (stream * stream) => undefinedStm.

MetaRocq Run (animate_coinductive zipSt <? zipSt ?>
  [("zipSt", ([0;1], [2]))] 100).

Compute (Str_nth 6 (zipStAnimatedTopFnStream (Success (stream * stream) (from 7, from 9)))).

(* ------------------------------------------------------------------ *)
(** ** Stream equality *)

Inductive co_bool : Type :=
| coT : co_bool
| coF : co_bool
| undefinedB : co_bool.

CoInductive eqSt : stream -> stream -> co_bool -> Prop :=
| eqU1 : forall s, eqSt s undefinedStm undefinedB
| eqU2 : forall s, eqSt undefinedStm s undefinedB
| eqNil : eqSt nil nil coT
| eqC : forall n m s2 s4 u, n = m /\ eqSt s2 s4 u -> eqSt (Seq n s2) (Seq m s4) u
| neqC : forall n m s2 s4, false = Nat.eqb n m -> eqSt (Seq n s2) (Seq m s4) coF.

Definition eqStRest := fun _ : (stream * stream) => undefinedB.

MetaRocq Run (animate_coinductive eqSt <? eqSt ?>
  [("eqSt", ([0;1], [2]))] 100).

Compute (Str_nth 12 (eqStAnimatedTopFnStream (Success (stream * stream) (from 8, from 9)))).
Compute (Str_nth 0  (eqStAnimatedTopFnStream (Success (stream * stream) (from 5, from 9)))).

(* ------------------------------------------------------------------ *)
(** ** Filter even elements *)

Fixpoint isEven (n : nat) : bool :=
  match n with
  | 0     => true
  | 1     => false
  | S (S m) => isEven m
  end.

CoInductive filterEven : stream -> stream -> Prop :=
| filtU   : filterEven undefinedStm undefinedStm
| filtNil : filterEven nil nil
| filtE   : forall n s1 s2, true  = isEven n /\ filterEven s1 s2 -> filterEven (Seq n s1) (Seq n s2)
| filtOdd : forall n s1 s2, false = isEven n /\ filterEven s1 s2 -> filterEven (Seq n s1) s2.

Definition filterEvenRest := fun _ : stream => undefinedStm.

MetaRocq Run (animate_coinductive filterEven <? filterEven ?>
  [("filterEven", ([0], [1]))] 100).

Compute (Str_nth 10 (filterEvenAnimatedTopFnStream (Success stream (from 0)))).
Compute (Str_nth 10 (filterEvenAnimatedTopFnStream
  (Success stream (Seq 0 (Seq 2 (Seq 3 (Seq 6 (Seq 8 (Seq 10 (Seq 12 nil)))))))))).
