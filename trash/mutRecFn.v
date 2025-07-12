From Stdlib Require Import List.




Require Import PeanoNat.
Local Open Scope nat_scope.


Inductive recFnBlock : Set :=
| even : recFnBlock
| odd : recFnBlock.

Fixpoint eval (f : recFnBlock) (n : nat) : bool :=
 match f with
  | even => match n with
             | 0 => true
             | S m => eval odd m
             end
  | odd => match n with
            | 0 => false
            | S m => eval even m
            end
 end.
 
Compute (eval odd 3). 
 







