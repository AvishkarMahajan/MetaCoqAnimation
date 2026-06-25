(** * TestNat: Natural Number Relations
    Tests animation of simple inductive relations over natural numbers.
    Covers basic recursion, mutual induction, and multiple modes. *)

Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.
Require Import Animation.EqualityResolution.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.
From Stdlib Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.
Import MetaRocqNotations.
Local Open Scope nat_scope.
Open Scope bs.

(** ** Empty input mode *)
(* All arguments are outputs — the relation appears in both let-binding
   and boolean-guard position during compilation. *)

Inductive isGood2 : list nat -> nat -> Prop :=
| isG2 : forall n l, isGoodEmptyIn' l n /\ isGoodEmptyIn l n -> isGood2 l n
with isGoodEmptyIn : list nat -> nat -> Prop :=
| zeroCEmptyIn : isGoodEmptyIn [] 0
with isGoodEmptyIn' : list nat -> nat -> Prop :=
| zeroCEmptyIn' : isGoodEmptyIn' [] 1.

MetaRocq Run (animate_inductive isGood2 <? isGood2 ?>
  [("isGood2", ([], [0;1]));
   ("isGoodEmptyIn", ([], [0;1]));
   ("isGoodEmptyIn'", ([], [0;1]))] 500).

Example testIsGood2 :
  isGood2AnimatedTopFn 5 (Success bool true) = NoMatch (list nat * nat).
Proof. reflexivity. Qed.

(** ** Empty output mode *)
(* All arguments are inputs — no output positions. *)

Inductive isGood3 : list nat -> nat -> Prop :=
| isG3 : forall n l, isGoodEmptyIn'3 l n /\ isGoodEmptyIn3 l n -> isGood3 l n
with isGoodEmptyIn3 : list nat -> nat -> Prop :=
| zeroCEmptyIn3 : isGoodEmptyIn3 [] 0
with isGoodEmptyIn'3 : list nat -> nat -> Prop :=
| zeroCEmptyIn'3 : isGoodEmptyIn'3 [] 0.

MetaRocq Run (animate_inductive isGood3 <? isGood3 ?>
  [("isGood3", ([0;1], []));
   ("isGoodEmptyIn3", ([0;1], []));
   ("isGoodEmptyIn'3", ([0;1], []))] 500).

Example testIsGood3 :
  isGood3AnimatedTopFn 5 (Success (list nat * nat) ([1], 3)) = NoMatch bool.
Proof. reflexivity. Qed.

Example testIsGood3' :
  isGood3AnimatedTopFn 5 (Success (list nat * nat) ([], 0)) = Success bool true.
Proof. reflexivity. Qed.

(** ** Reverse usual modes *)

Inductive isGood : list nat -> nat -> Prop :=
| isG : forall n l, isGood' l n  -> isGood l n
with

isGood' : list nat -> nat -> Prop :=
| zeroC : isGood' [] 0.

MetaRocq Run (animate_inductive isGood <? isGood ?>
  [("isGood", ([1], [0])); ("isGood'", ([1], [0]))] 500).

Example testIsGood_0 :
  isGoodAnimatedTopFn 5 (Success nat 0) = Success (list nat) [].
Proof. reflexivity. Qed.

Example testIsGood_none :
  isGoodAnimatedTopFn 5 (Success nat 3) = NoMatch (list nat).
Proof. reflexivity. Qed.

(** ** Addition as a relation *)

Module Addition.

Inductive add : nat -> nat -> nat -> Prop :=
| add_zero : forall (n : nat), add 0 n n
| add_succ : forall (m n k : nat), add m n k -> add (S m) n (S k).

MetaRocq Run (animate_inductive add <?add?> [("add", ([0;1], [2]))] 100).

Example test_add_0_0 :
  addAnimatedTopFn 100 (Success (nat * nat) (0, 0)) = Success nat 0.
Proof. reflexivity. Qed.

Example test_add_0_5 :
  addAnimatedTopFn 100 (Success (nat * nat) (0, 5)) = Success nat 5.
Proof. reflexivity. Qed.

Example test_add_3_2 :
  addAnimatedTopFn 100 (Success (nat * nat) (3, 2)) = Success nat 5.
Proof. reflexivity. Qed.

Example test_add_1_0 :
  addAnimatedTopFn 100 (Success (nat * nat) (1, 0)) = Success nat 1.
Proof. reflexivity. Qed.

Example test_add_5_5 :
  addAnimatedTopFn 100 (Success (nat * nat) (5, 5)) = Success nat 10.
Proof. reflexivity. Qed.

Example test_add_fuel_error :
  addAnimatedTopFn 0 (Success (nat * nat) (3, 2)) = FuelError nat.
Proof. reflexivity. Qed.

End Addition.


(** ** Multiplication as a relation *)

Module Multiplication.

Inductive mul : nat -> nat -> nat -> Prop :=
| mul_zero : forall (n : nat), mul 0 n 0
| mul_succ : forall (m n k : nat), mul m n k -> mul (S m) n (n + k).

MetaRocq Run (animate_inductive mul <?mul?> [("mul", ([0;1], [2]))] 100).

Example test_mul_0_5 :
  mulAnimatedTopFn 100 (Success (nat * nat) (0, 5)) = Success nat 0.
Proof. reflexivity. Qed.

Example test_mul_1_5 :
  mulAnimatedTopFn 100 (Success (nat * nat) (1, 5)) = Success nat 5.
Proof. reflexivity. Qed.

Example test_mul_3_4 :
  mulAnimatedTopFn 100 (Success (nat * nat) (3, 4)) = Success nat 12.
Proof. reflexivity. Qed.

Example test_mul_2_0 :
  mulAnimatedTopFn 100 (Success (nat * nat) (2, 0)) = Success nat 0.
Proof. reflexivity. Qed.

End Multiplication.


(** ** Even/Odd as mutual relations *)

Module Parity.

Inductive even : nat -> bool -> Prop :=
| even0 : even 0 true
| evenSucc : forall (w : nat), odd w true -> even (S w) true
with odd : nat -> bool -> Prop :=
| oddSucc : forall (w : nat), even w true -> odd (S w) true.

MetaRocq Run (animate_inductive even <?even?> [("even", ([0], [1])); ("odd", ([0], [1]))] 100).

Example test_even_0 :
  evenAnimatedTopFn 30 (Success nat 0) = Success bool true.
Proof. reflexivity. Qed.

Example test_even_2 :
  evenAnimatedTopFn 30 (Success nat 2) = Success bool true.
Proof. reflexivity. Qed.

Example test_even_4 :
  evenAnimatedTopFn 30 (Success nat 4) = Success bool true.
Proof. reflexivity. Qed.

Example test_even_6 :
  evenAnimatedTopFn 30 (Success nat 6) = Success bool true.
Proof. reflexivity. Qed.

(* Odd inputs have no derivation in this relation, so animation returns noMatch *)
Example test_even_1 :
  evenAnimatedTopFn 30 (Success nat 1) = NoMatch bool.
Proof. reflexivity. Qed.

Example test_even_3 :
  evenAnimatedTopFn 30 (Success nat 3) = NoMatch bool.
Proof. reflexivity. Qed.

Example test_even_5 :
  evenAnimatedTopFn 30 (Success nat 5) = NoMatch bool.
Proof. reflexivity. Qed.

End Parity.


(** ** Less-than-or-equal as a relation *)

Module LessEq.

Inductive leq : nat -> nat -> bool -> Prop :=
| leq_zero : forall (n : nat), leq 0 n true
| leq_succ : forall (m n : nat) (b : bool), leq m n b -> leq (S m) (S n) b
| leq_fail : forall (m : nat), leq (S m) 0 false.

MetaRocq Run (animate_inductive leq <?leq?> [("leq", ([0;1], [2]))] 100).

Example test_leq_0_0 :
  leqAnimatedTopFn 100 (Success (nat * nat) (0, 0)) = Success bool true.
Proof. reflexivity. Qed.

Example test_leq_0_5 :
  leqAnimatedTopFn 100 (Success (nat * nat) (0, 5)) = Success bool true.
Proof. reflexivity. Qed.

Example test_leq_3_5 :
  leqAnimatedTopFn 100 (Success (nat * nat) (3, 5)) = Success bool true.
Proof. reflexivity. Qed.

Example test_leq_5_3 :
  leqAnimatedTopFn 100 (Success (nat * nat) (5, 3)) = Success bool false.
Proof. reflexivity. Qed.

Example test_leq_5_5 :
  leqAnimatedTopFn 100 (Success (nat * nat) (5, 5)) = Success bool true.
Proof. reflexivity. Qed.

Example test_leq_1_0 :
  leqAnimatedTopFn 100 (Success (nat * nat) (1, 0)) = Success bool false.
Proof. reflexivity. Qed.

End LessEq.
