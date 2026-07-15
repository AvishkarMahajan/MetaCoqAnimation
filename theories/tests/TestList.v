(** * TestList: List Operations as Relations
    Tests animation of inductive relations over lists.
    Covers list construction/deconstruction and multiple mode directions. *)

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


(** ** Append: list concatenation *)

Module Append.

Inductive append : list nat -> list nat -> list nat -> Prop :=
| appendNil : forall (l2 : list nat), append [] l2 l2
| appendCons : forall (w : nat) (l2 l3 l4 : list nat),
    append l2 l3 l4 -> append (w :: l2) l3 (w :: l4).

MetaRocq Run (animate_inductive <?append?> [("append", ([0;1], [2]))] 100).

Example test_append_nil_nil :
  appendAnimatedTopFn 100 (Success (list nat * list nat) ([], []))
  = Success (list nat) [].
Proof. reflexivity. Qed.

Example test_append_nil_123 :
  appendAnimatedTopFn 100 (Success (list nat * list nat) ([], [1;2;3]))
  = Success (list nat) [1;2;3].
Proof. reflexivity. Qed.

Example test_append_12_3 :
  appendAnimatedTopFn 100 (Success (list nat * list nat) ([1;2], [3]))
  = Success (list nat) [1;2;3].
Proof. reflexivity. Qed.

Example test_append_123_nil :
  appendAnimatedTopFn 100 (Success (list nat * list nat) ([1;2;3], []))
  = Success (list nat) [1;2;3].
Proof. reflexivity. Qed.

Example test_append_12_34 :
  appendAnimatedTopFn 100 (Success (list nat * list nat) ([1;2], [3;4]))
  = Success (list nat) [1;2;3;4].
Proof. reflexivity. Qed.

End Append.


(** ** Length: list length as a relation *)

Module Length.

Inductive length_rel : list nat -> nat -> Prop :=
| length_nil : length_rel [] 0
| length_cons : forall (w : nat) (l : list nat) (n : nat),
    length_rel l n -> length_rel (w :: l) (S n).

MetaRocq Run (animate_inductive <?length_rel?> [("length_rel", ([0], [1]))] 100).

Example test_length_nil :
  length_relAnimatedTopFn 100 (Success (list nat) [])
  = Success nat 0.
Proof. reflexivity. Qed.

Example test_length_1 :
  length_relAnimatedTopFn 100 (Success (list nat) [42])
  = Success nat 1.
Proof. reflexivity. Qed.

Example test_length_3 :
  length_relAnimatedTopFn 100 (Success (list nat) [1;2;3])
  = Success nat 3.
Proof. reflexivity. Qed.

Example test_length_5 :
  length_relAnimatedTopFn 100 (Success (list nat) [10;20;30;40;50])
  = Success nat 5.
Proof. reflexivity. Qed.

End Length.


(** ** Suffix: extracting a suffix from a list *)

Module Suffix.

Inductive suffix : list nat -> list nat -> list nat -> Prop :=
| suffixNil : forall (l2 : list nat), suffix [] l2 l2
| suffixCons : forall (w : nat) (l2 l3 l4 : list nat),
    suffix l2 l3 l4 -> suffix (w :: l2) l3 (w :: l4).

MetaRocq Run (animate_inductive <?suffix?> [("suffix", ([0;2], [1]))] 100).

Example test_suffix_nil :
  suffixAnimatedTopFn 50 (Success (list nat * list nat) ([], [1;2;3]))
  = Success (list nat) [1;2;3].
Proof. reflexivity. Qed.

Example test_suffix_prefix :
  suffixAnimatedTopFn 50 (Success (list nat * list nat) ([8;7], [8;7;9;7;8]))
  = Success (list nat) [9;7;8].
Proof. reflexivity. Qed.

Example test_suffix_full :
  suffixAnimatedTopFn 50 (Success (list nat * list nat) ([1;2;3], [1;2;3]))
  = Success (list nat) [].
Proof. reflexivity. Qed.

(* Head mismatch: prefix [1] vs full list starting with 2 *)
Example test_suffix_head_mismatch :
  suffixAnimatedTopFn 50 (Success (list nat * list nat) ([1], [2;3]))
  = NoMatch (list nat).
Proof. reflexivity. Qed.

(* Prefix longer than full list: no suffix exists *)
Example test_suffix_prefix_too_long :
  suffixAnimatedTopFn 50 (Success (list nat * list nat) ([1;2;3], [1;2]))
  = NoMatch (list nat).
Proof. reflexivity. Qed.

End Suffix.


(** ** Reverse: list reversal with accumulator *)

Module Reverse.

Inductive rev_acc : list nat -> list nat -> list nat -> Prop :=
| rev_nil : forall (acc : list nat), rev_acc [] acc acc
| rev_cons : forall (w : nat) (l acc res : list nat),
    rev_acc l (w :: acc) res -> rev_acc (w :: l) acc res.

MetaRocq Run (animate_inductive <?rev_acc?> [("rev_acc", ([0;1], [2]))] 100).

Example test_rev_nil :
  rev_accAnimatedTopFn 100 (Success (list nat * list nat) ([], []))
  = Success (list nat) [].
Proof. reflexivity. Qed.

Example test_rev_123 :
  rev_accAnimatedTopFn 100 (Success (list nat * list nat) ([1;2;3], []))
  = Success (list nat) [3;2;1].
Proof. reflexivity. Qed.

Example test_rev_singleton :
  rev_accAnimatedTopFn 100 (Success (list nat * list nat) ([42], []))
  = Success (list nat) [42].
Proof. reflexivity. Qed.

Example test_rev_12345 :
  rev_accAnimatedTopFn 100 (Success (list nat * list nat) ([1;2;3;4;5], []))
  = Success (list nat) [5;4;3;2;1].
Proof. reflexivity. Qed.

End Reverse.
