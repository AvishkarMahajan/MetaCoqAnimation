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
(* Auxiliary relations in separate blocks; [isGood2] calls both. *)

Inductive isGoodEmptyIn : list nat -> nat -> Prop :=
| zeroCEmptyIn : isGoodEmptyIn [] 0.

Inductive isGoodEmptyIn' : list nat -> nat -> Prop :=
| zeroCEmptyIn' : isGoodEmptyIn' [] 1.

Inductive isGood2 : list nat -> nat -> Prop :=
| isG2 : forall n l, isGoodEmptyIn' l n /\ isGoodEmptyIn l n -> isGood2 l n.

MetaRocq Run (animate_inductive isGood2 <? isGood2 ?>
  [("isGood2", ([], [0;1]));
   ("isGoodEmptyIn", ([], [0;1]));
   ("isGoodEmptyIn'", ([], [0;1]))] 100).

Example testIsGood2 :
  isGood2AnimatedTopFn 5 (Success bool true) = NoMatch (list nat * nat).
Proof. reflexivity. Qed.

(** ** Empty output mode *)
(* Auxiliary relations in separate blocks; [isGood3] calls both. *)

Inductive isGoodEmptyIn3 : list nat -> nat -> Prop :=
| zeroCEmptyIn3 : isGoodEmptyIn3 [] 0.

Inductive isGoodEmptyIn'3 : list nat -> nat -> Prop :=
| zeroCEmptyIn'3 : isGoodEmptyIn'3 [] 0.

Inductive isGood3 : list nat -> nat -> Prop :=
| isG3 : forall n l, isGoodEmptyIn'3 l n /\ isGoodEmptyIn3 l n -> isGood3 l n.

MetaRocq Run (animate_inductive isGood3 <? isGood3 ?>
  [("isGood3", ([0;1], []));
   ("isGoodEmptyIn3", ([0;1], []));
   ("isGoodEmptyIn'3", ([0;1], []))] 100).

Example testIsGood3 :
  isGood3AnimatedTopFn 5 (Success (list nat * nat) ([1], 3)) = NoMatch bool.
Proof. reflexivity. Qed.

Example testIsGood3' :
  isGood3AnimatedTopFn 5 (Success (list nat * nat) ([], 0)) = Success bool true.
Proof. reflexivity. Qed.

(** ** Reverse usual modes *)
(* [isGood'] is a standalone block; [isGood] calls it from a separate block. *)

Inductive isGood' : list nat -> nat -> Prop :=
| zeroC : isGood' [] 0.

Inductive isGood : list nat -> nat -> Prop :=
| isG : forall n l, isGood' l n -> isGood l n.

MetaRocq Run (animate_inductive isGood <? isGood ?>
  [("isGood", ([1], [0])); ("isGood'", ([1], [0]))] 100).

Example testIsGood_0 :
  isGoodAnimatedTopFn 5 (Success nat 0) = Success (list nat) [].
Proof. reflexivity. Qed.

Example testIsGood_none :
  isGoodAnimatedTopFn 5 (Success nat 3) = NoMatch (list nat).
Proof. reflexivity. Qed.

(** ** Addition as a relation *)

Module Addition.

Inductive add : nat -> nat -> nat -> Prop :=
| add_zero : forall (x : nat), add 0 x x
| add_succ : forall (v0 x v1 : nat), add v0 x v1 -> add (S v0) x (S v1).

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


(** ** Even/Odd as mutual relations — single [with] block.
    [even] and [odd] are genuinely mutually recursive so they remain in
    one block; [animate_inductive] handles this correctly. *)

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


(** ** Mutual block + standalone block
    [triple2] is a standalone inductive.
    [evn4]/[od4] are a mutually recursive pair (same [with] block).
    [tripled_parity] calls both: it triples its input and checks the
    parity of the result. *)

Module MixedBlocksSolo.

(** Standalone: tripling relation. *)
Inductive triple2 : nat -> nat -> Prop :=
| t2_zero : triple2 0 0
| t2_succ : forall n m, triple2 n m -> triple2 (S n) (S (S (S m))).

(** Mutual block: parity check (only derives [true] outputs). *)
Inductive evn4 : nat -> bool -> Prop :=
| evn4_zero : evn4 0 true
| evn4_succ : forall n, od4 n true -> evn4 (S n) true
with od4 : nat -> bool -> Prop :=
| od4_succ : forall n, evn4 n true -> od4 (S n) true.

(** Top-level: given [n], compute [(3n, parity(3n))].
    Only succeeds when [3n] is even, i.e. when [n] is even. *)
Inductive tripled_parity : nat -> (nat * bool) -> Prop :=
| tp_rule : forall n t b,
    triple2 n t /\ evn4 t b -> tripled_parity n (t, b).

MetaRocq Run (animate_inductive tripled_parity <?tripled_parity?>
  [("tripled_parity", ([0], [1]));
   ("triple2",        ([0], [1]));
   ("evn4",           ([0], [1]));
   ("od4",            ([0], [1]))] 50).

(* 3*0 = 0, which is even *)
Example test_tp_0 :
  tripled_parityAnimatedTopFn 50 (Success nat 0)
  = Success (nat * bool) (0, true).
Proof. reflexivity. Qed.

(* 3*2 = 6, which is even *)
Example test_tp_2 :
  tripled_parityAnimatedTopFn 50 (Success nat 2)
  = Success (nat * bool) (6, true).
Proof. reflexivity. Qed.

(* 3*4 = 12, which is even — requires deeper recursion, needs more fuel *)
Example test_tp_4 :
  tripled_parityAnimatedTopFn 50 (Success nat 4)
  = Success (nat * bool) (12, true).
Proof. reflexivity. Qed.

(* 3*1 = 3, which is odd — no parity proof exists, returns NoMatch *)
Example test_tp_1_no_match :
  tripled_parityAnimatedTopFn 50 (Success nat 1)
  = NoMatch (nat * bool).
Proof. reflexivity. Qed.

End MixedBlocksSolo.


(** ** Two separate mutual blocks
    [evn5]/[od5] form one mutual [with] block (parity).
    [val_check]/[val_helper] form a second mutual [with] block (identity).
    [even_ident] calls one relation from each block: it is the identity
    function restricted to even inputs. *)

Module TwoMutualBlocks.

(** First mutual block: parity (only derives [true] outputs). *)
Inductive evn5 : nat -> bool -> Prop :=
| evn5_zero : evn5 0 true
| evn5_succ : forall n, od5 n true -> evn5 (S n) true
with od5 : nat -> bool -> Prop :=
| od5_succ : forall n, evn5 n true -> od5 (S n) true.



(** Top-level: identity on even naturals.
    Combines parity evidence ([evn5]) with value identity ([val_check]). *)
Inductive even_ident : nat -> nat -> Prop :=
| ei_rule : forall n m,
    evn5 n true /\ val_check n m -> even_ident n m
with val_check : nat -> nat -> Prop :=
| vc_zero : val_check 0 0
| vc_succ : forall n m, val_helper n m -> val_check (S n) (S m)
with val_helper : nat -> nat -> Prop :=
| vh_zero : val_helper 0 0
| vh_succ : forall n m, val_check n m -> val_helper (S n) (S m).
    

MetaRocq Run (animate_inductive even_ident <?even_ident?>
  [("even_ident",  ([0], [1]));
   ("evn5",        ([0], [1]));
   ("od5",         ([0], [1]));
   ("val_check",   ([0], [1]));
   ("val_helper",  ([0], [1]))] 30).

Example test_ei_0 :
  even_identAnimatedTopFn 30 (Success nat 0) = Success nat 0.
Proof. reflexivity. Qed.

Example test_ei_2 :
  even_identAnimatedTopFn 30 (Success nat 2) = Success nat 2.
Proof. reflexivity. Qed.

Example test_ei_4 :
  even_identAnimatedTopFn 30 (Success nat 4) = Success nat 4.
Proof. reflexivity. Qed.

(* Odd input: parity check fails, no derivation exists *)
Example test_ei_1_no_match :
  even_identAnimatedTopFn 30 (Success nat 1) = NoMatch nat.
Proof. reflexivity. Qed.

Example test_ei_3_no_match :
  even_identAnimatedTopFn 30 (Success nat 3) = NoMatch nat.
Proof. reflexivity. Qed.

End TwoMutualBlocks.


(** ** Pattern-match equality guard: [x = c] where [c] is a ground constructor.
     *)

Module PatternGuard.

Inductive newTp :Type :=
| nulCon : newTp
| unaCon : nat -> newTp -> newTp.

Inductive patGuard : newTp -> newTp -> Prop :=
| checkEq : forall w u, u = nulCon /\ unaCon 5 (unaCon 6 nulCon) = w /\ unaCon 5 nulCon = unaCon 5 nulCon -> patGuard w u.



MetaRocq Run (animate_inductive patGuard <?patGuard?>
  [("patGuard", ([0;1], []))] 100).

Example patGuard0 :
 patGuardAnimatedTopFn 10 (Success (newTp * newTp) (unaCon 5 (unaCon 6 nulCon), nulCon)) = Success bool true.

Proof. reflexivity. Qed.

Example patGuard1 :
 patGuardAnimatedTopFn 10 (Success (newTp * newTp) (unaCon 5 (unaCon 6 nulCon), unaCon 2 nulCon)) = NoMatch bool.

Proof. reflexivity. Qed.   

Example patGuard2 :
 patGuardAnimatedTopFn 10 (Success (newTp * newTp) (unaCon 2 nulCon, nulCon)) = NoMatch bool.

Proof. reflexivity. Qed.


Inductive patGuard' : newTp -> newTp -> Prop :=
| checkEq' : forall w u, u = nulCon /\ unaCon 5 (unaCon 6 nulCon) = w /\ unaCon 5 nulCon = nulCon -> patGuard' w u.



MetaRocq Run (animate_inductive patGuard' <?patGuard'?>
  [("patGuard'", ([0;1], []))] 100).

Example patGuard'0 :
 patGuard'AnimatedTopFn 10 (Success (newTp * newTp) (unaCon 5 (unaCon 6 nulCon), nulCon)) = NoMatch bool.

Proof. reflexivity. Qed.

(** ** Function-application equality guard: [f(x) = c] where [f] is a defined
    function, [x] a known variable, and [c] a ground constructor. *)

Definition wrap_nat (n : nat) : newTp :=
  match n with
  | 0   => nulCon
  | S k => unaCon k nulCon
  end.

Inductive patGuardFnApp : nat -> nat -> Prop :=
| pgfa_rule : forall n m, nulCon = wrap_nat n /\ wrap_nat m = nulCon   -> patGuardFnApp n m.

MetaRocq Run (animate_inductive patGuardFnApp <?patGuardFnApp?>
  [("patGuardFnApp", ([0;1], []))] 100).

Example patGuardFnApp_zero :
  patGuardFnAppAnimatedTopFn 10 (Success (nat * nat) (0,0)) = Success bool true.
Proof. reflexivity. Qed.

Example patGuardFnApp_one :
  patGuardFnAppAnimatedTopFn 10 (Success (nat * nat) (0,1)) = NoMatch bool.
Proof. reflexivity. Qed.

Example patGuardFnApp_five :
  patGuardFnAppAnimatedTopFn 10 (Success (nat * nat) (5,0)) = NoMatch bool.
Proof. reflexivity. Qed.

End PatternGuard.

(** ** Relation named [x;v2] with constructor variables [v0]/[v1].
    Exercises the renaming pass when the relation name itself is a potential
    clash candidate and the data variables are engine-internal names. *)

Module ClashRelName.
Inductive v2 : nat -> nat -> Prop :=
| vCon : forall x v3 , fuel x v3 -> v2 x v3
with x : nat -> nat -> Prop :=
| x_base : x 0 0
| x_step : forall (v0 v1 : nat), x v0 v1 -> x (S v0) (S v1)
with fuel : nat -> nat -> Prop :=

| v1_step : forall (v0 v2 : nat), x v0 v2 -> fuel (v0) (v2).


MetaRocq Run (animate_inductive x <?x?> [("x", ([0], [1])); ("fuel", ([0], [1])); ("v2", ([0], [1]))] 200).

Example test_v2_0 :
  v2AnimatedTopFn 50 (Success nat 0) = Success nat 0.
Proof. reflexivity. Qed.

Example test_v2_3 :
  v2AnimatedTopFn 50 (Success nat 3) = Success nat 3.
Proof. reflexivity. Qed.

Example test_v2_5 :
  v2AnimatedTopFn 50 (Success nat 5) = Success nat 5.
Proof. reflexivity. Qed.

End ClashRelName.
