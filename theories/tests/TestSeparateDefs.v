(** * TestSeparateDefs: Auxiliary relation in a separate inductive block
    Tests [animate_multi_def]'s two-phase cross-block compilation by animating
    a relation that calls an auxiliary predicate defined in a separate
    [Inductive] block (not the same [with] clause). *)

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

Module SeparateDefs.

(** ** Auxiliary relation: addition (standalone inductive block) *)

Inductive add_aux : nat -> nat -> nat -> Prop :=
| add_aux_zero : forall n, add_aux 0 n n
| add_aux_succ : forall m n k, add_aux m n k -> add_aux (S m) n (S k).

(** ** Main relation: calls add_aux from a separate block
    [double_via_add n k] holds iff [k = n + n]. *)

Inductive double_via_add : nat -> nat -> Prop :=
| double_rule : forall n k, add_aux n n k -> double_via_add n k.

MetaRocq Run (animate_multi_aux double_via_add <?double_via_add?> [<?add_aux?>]
  [("double_via_add", ([0], [1])); ("add_aux", ([0;1], [2]))] 100).

Example test_double_0 :
  double_via_addAnimatedTopFn 100 (Success nat 0) = Success nat 0.
Proof. reflexivity. Qed.

Example test_double_3 :
  double_via_addAnimatedTopFn 100 (Success nat 3) = Success nat 6.
Proof. reflexivity. Qed.

Example test_double_5 :
  double_via_addAnimatedTopFn 100 (Success nat 5) = Success nat 10.
Proof. reflexivity. Qed.

End SeparateDefs.
