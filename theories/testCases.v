From Stdlib Require Import List.

Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.

Require Import Animation.animationModules.
Import utils.MetaRocqNotations.

Require Import PeanoNat.
Local Open Scope nat_scope.
Open Scope bs.


(* 
Definition soundness' (f : (nat -> nat -> option (list nat))) (n1 : nat) (n2 : nat) : Type :=
 let r := (f n1 n2) in 
   match r with
    | Some ([n3 ; n4 ; n5]) => forall h1, forall h2, forall h3, h1 = g1 -> h2 = g2 -> h3 = g3 -> (foo n1 n2 n3 n4 n5) 
    | None => forall h1, forall h2, forall h3, h1 = g1 -> h2 = g2 -> h3 = g3 ->  (forall n3 n4 n5 : nat, (foo n1 n2 n3 n4 n5 -> False))
 (*  (forall n3 n4 n5 : nat, (foo n1 n2 n3 n4 n5 -> False)) *)
    | _ => False
    end. 
Definition soundness'' (f : (nat -> nat -> option (list nat))) : Type :=
 forall n1 n2, soundness' f n1 n2 .       



Lemma beq_nat_eq : forall n m, true = (n =? m) -> n = m. Proof. Admitted.
Lemma beq_nat_neq : forall n m, false = (n =? m) -> (n = m -> False). Proof. Admitted.

Definition animate'' (conjs : term) (inputVars : (list string)) (fuel : nat) : TemplateMonad unit :=
  t' <- DB.deBruijn (genFun conjs inputVars fuel)  ;;
  f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) t' ;;
  lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;;
  tmMsg "done".*)