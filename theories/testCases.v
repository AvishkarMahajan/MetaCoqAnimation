From Stdlib Require Import List.

Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.

Require Import Animation.animationModules.
Require Import Animation.utils.

Import utils.MetaRocqNotations.

Require Import PeanoNat.
Local Open Scope nat_scope.
Open Scope bs.

(* 1 *)
Section s.
(*
Variable g1 : nat -> nat.
Variable g2 : nat -> nat.
Variable g3 : nat -> nat -> nat.
*)

(* Can also use context ? *) 
Context (g1 : nat -> nat) (g2 : nat -> nat) (g3 : nat -> nat -> nat) (g4 : nat -> nat -> nat -> nat -> nat).

Lemma beq_nat_eq : forall n m, true = (n =? m) -> n = m. Proof. Admitted.
Lemma beq_nat_neq : forall n m, false = (n =? m) -> (n = m -> False). Proof. Admitted.


(* a, b designated as input, c d e designated as output *)
Inductive foo : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr : forall a b c d e, (e = b /\ d = c /\ c = (g3 a e) /\ g1 d = g2 a) -> foo a b c d e.
 






Definition soundness' (f : (nat -> nat -> option (list nat))) (n1 : nat) (n2 : nat) : Type :=
 let r := (f n1 n2) in 
   match r with
    | Some ([n3 ; n4 ; n5]) => (* forall h1, forall h2, forall h3, h1 = g1 -> h2 = g2 -> h3 = g3 -> *) (foo n1 n2 n3 n4 n5) 
    | None => (forall n3 n4 n5 : nat, (foo n1 n2 n3 n4 n5 -> False))
 (*  (forall n3 n4 n5 : nat, (foo n1 n2 n3 n4 n5 -> False)) *)
    | _ => False
    end. 
Definition soundness'' (f : (nat -> nat -> option (list nat))) : Type :=
 forall n1 n2, soundness' f n1 n2 .
 

(* Check foo. 
Check soundness''. *) 
 
  
Definition animate'' (kn : kername) (inputVars : (list string)) (outputVars : list string) (fuel : nat) : TemplateMonad unit :=
  conjs <- general.animate2 kn ;;
  t' <- DB.deBruijn (animateEqual.genFun conjs inputVars outputVars fuel)  ;; 
  f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) t' ;; tmPrint f ;; tmDefinition (String.append (snd kn) "Fn") f ;;
  lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;;
  tmMsg "done".
  



MetaRocq Run (animate'' <? foo ?> ["a"; "b"] ["c"; "d";"e"] 10).

Next Obligation.
Proof. unfold soundness'. (* exists ((fun n1 n2 => if Nat.eqb (g1 (g3 n1 n2)) (g2 n1) then Some [g3 n1 n2; g3 n1 n2; n2] else None) n1 n2). *)
remember (Nat.eqb (g1 (g3 n1 n2)) (g2 n1)) as H. destruct H.
+ split.
++ (*apply cstr.*) apply beq_nat_eq in HeqH. rewrite -> HeqH.
auto. 
+ intros. inversion H ; subst. apply beq_nat_neq in HeqH.
*  auto.
* destruct H0. rewrite H0 in H1. destruct H1.
rewrite H1 in H2. destruct H2. rewrite H2 in H3. auto.
 Qed.

Inductive foo' : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr' : forall a b c d e, (g1 d = g2 a /\ d = c /\ c = (g3 a e) /\ e = b ) -> foo' a b c d e.
 

MetaRocq Run (animate'' <? foo' ?> ["a" ; "b"] ["c"; "d";"e"] 30).

Next Obligation.
Proof. unfold soundness'. (* exists ((fun n1 n2 => if Nat.eqb (g1 (g3 n1 n2)) (g2 n1) then Some [g3 n1 n2; g3 n1 n2; n2] else None) n1 n2). *)
remember (Nat.eqb (g1 (g3 n1 n2)) (g2 n1)) as H. destruct H.
+ split.
++ (*apply cstr.*) apply beq_nat_eq in HeqH. rewrite -> HeqH.
auto. 
+ intros. inversion H ; subst. apply beq_nat_neq in HeqH.
*  auto.
* destruct H0. rewrite H0 in H1. destruct H1.
rewrite H1 in H2. destruct H2. rewrite H2 in H3. auto.
 Qed.
     
(* known var 'b' is on LHS not RHS *)



Inductive foo'' : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr'' : forall a b c d e, (g1 d = g2 a /\ d = c /\ c = (g3 a e) /\ b = e ) -> foo'' a b c d e.
 




MetaRocq Run (animate'' <? foo'' ?> ["a" ; "b"] ["c"; "d";"e"] 30).
Next Obligation.
Proof. unfold soundness'. (* exists ((fun n1 n2 => if Nat.eqb (g1 (g3 n1 n2)) (g2 n1) then Some [g3 n1 n2; g3 n1 n2; n2] else None) n1 n2). *)
remember (Nat.eqb (g1 (g3 n1 n2)) (g2 n1)) as H. destruct H.
+ split.
++ (*apply cstr.*) apply beq_nat_eq in HeqH. rewrite -> HeqH.
auto. 
+ intros. inversion H ; subst. apply beq_nat_neq in HeqH.
*  auto.
* destruct H0. rewrite H0 in H1. destruct H1.
rewrite H1 in H2. destruct H2. rewrite H2 in H3. auto.
 Qed.


Inductive foo4 : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr4 : forall a b c d e, (g1 d = g2 a /\ d = b /\  (g4 a e a e) = c /\ b = e ) -> foo4 a b c d e.
 





Definition justAnimate (kn : kername) (inputVars : (list string)) (outputVars : list string) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
  conjs <- general.animate2 kn ;;
  t' <- DB.deBruijn (animateEqual.genFun conjs inputVars outputVars fuel)  ;; 
  f <- tmUnquote t' ;;
  (*tmPrint f ;;*)
  tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
  (* lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;; *)
  tmMsg "done". 


MetaRocq Run (justAnimate <? foo4 ?> ["a" ; "b"] ["c"; "d";"e"] "foo4Fn" 100). 
(*Use tmEval *)
Print foo4Fn.




(*MetaRocq Run (justAnimate <? foo4 ?> ["a" ; "d"] ["c"; "e"] 100). *)


Inductive foo5 : nat -> nat -> Prop :=
 | cstr5 : forall a b, a = b  -> foo5 a b.
 





MetaRocq Run (justAnimate <? foo5 ?> ["a"] ["b"] "foo5Fn" 100).

Print foo5Fn.

Example testfoo5 : foo5Fn 1 = Some [1]. 
Proof. reflexivity. Qed.
 
  

End s.

Check foo4Fn.

Parameter errorPath : prod modpath ident.

Definition getPathIdent (t : term) : prod modpath ident :=
 match t with
  | tInd p l => inductive_mind p
  | _ => errorPath
 end. 


          


Definition justAnimatePatMat {A : Type} (induct : A) (outputVar : list string) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
 indTm <- tmQuote induct ;; 
 termConj <- general.animate2 (getPathIdent indTm) ;; 
 termFull <- tmQuoteRecTransp  induct  false ;; 
 t <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption ((typeConstrPatMatch.removeopTm (typeConstrPatMatch.mkLamfromInd2 termConj termFull outputVar fuel))))) ;; 
 f <- tmUnquote t ;; 
 tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
 
 tmMsg "done".

 
  



Inductive tuple : nat -> nat -> (prod nat nat) -> Prop :=
 | tupleCon : forall (a : nat), forall (b : nat), forall (y : (prod nat nat)), (a, S b) = y -> tuple a b y. (*RHS of equality not v imp*)
 
MetaRocq Run (justAnimatePatMat tuple ["a" ; "b"] "tupleFn" 25).

Print tupleFn. 
         


Inductive singleton : nat -> list nat -> Prop :=
 | singletonCon : forall (a : nat), forall (y : list nat), (a :: [])  = y -> singleton a  y.  (*RHS of equality not v imp*)
 



(* 4 *)

Inductive myType' : Set :=
| mycr1' : nat -> myType'
| mycr2' : nat -> myType'.

Inductive myType : Set :=
| mycr2 : myType' -> nat -> myType
| mycr3 : myType.


Inductive baz' : nat -> nat -> myType -> Prop :=
 | bazCon' : forall (a : nat), forall (x : nat), forall (y : myType), mycr2 (mycr1' a) (S x) = y -> baz' a x y.  (*RHS of equality not v imp*)
 






Definition justAnimateElimConstr (kn : kername) (inputVars : list string) (outputVars : list string) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
  (* conjs <- general.animate2 kn ;; *)
  t <- general.animate2 kn ;;
  let conjs := (tApp <%and%> (typeConstrReduce.makeConjSimpl (typeConstrReduce.deconTypeConGen'' (typeConstrReduce.deConConj1 t) (typeConstrReduce.deConConj2 t) fuel))) in

  
  t' <- DB.deBruijn (animateEqual.genFun conjs inputVars outputVars fuel)  ;; 
  f <- tmUnquote t' ;; (* tmDefinition (String.append (snd kn) "Fn") f ;; *)
  tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
 
  
  (* lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;; *)
  tmMsg "done". 






Inductive fooCon : nat -> nat -> nat -> nat -> Prop :=
 | cstrCon : forall a b c d,  [S a ; S c]  = [S b ; d]  -> fooCon a b c d.
 
(* MetaRocq Run (t <- general.animate2 <? fooCon ?> ;;  justAnimate' <? fooCon ?> (tApp <%and%> (typeConstrReduce.makeConjSimpl (typeConstrReduce.deconTypeConGen'' (typeConstrReduce.deConConj1 t) (typeConstrReduce.deConConj2 t) 20))) ["a" ; "c"] ["b" ; "d"] 70) .
*)

MetaRocq Run (justAnimateElimConstr <? fooCon ?> ["a" ; "c"] ["b" ; "d"] "fooConFn" 50).
Print fooConFn.



(* Compute (typeConstrReduce.makeConjSimpl (typeConstrReduce.deconTypeConGen'' (typeConstrReduce.deConConj1 fooConTerm) (typeConstrReduce.deConConj2 fooConTerm) 20)).  *)

(* Returns conjuncts corresponding to : 0 = b , S c = d *)



Inductive fooCon' : nat -> nat -> nat -> nat -> Prop :=
 | cstrCon' : forall a b c d, [S b ; d] = [S a ; S c]  -> fooCon' a b c d.
 
(* MetaRocq Run (t <- general.animate2 <? fooCon' ?> ;;  justAnimate' <? fooCon' ?> (tApp <%and%> (typeConstrReduce.makeConjSimpl (typeConstrReduce.deconTypeConGen'' (typeConstrReduce.deConConj1 t) (typeConstrReduce.deConConj2 t) 20))) ["c" ; "b"] ["a" ; "d"] 70) .

Print fooCon'Fn. *)



(* Returns conjuncts corresponding to : b = 0 , d = S c *)



(* Recursive Predicate *)

Inductive recPred : nat -> nat -> Prop :=
 | recPredBase : recPred 1 3
 | recPredInd : forall a b, recPred a b  -> recPred (S a) (S b).
 
(* Desired output function with a as input, b as output *)

Fixpoint recPredfn (a : nat) : option nat :=
 match a with
 | 1 => Some 3
 | S a' => match recPredfn a' with
           | None => None
           | Some b' => Some (S b')
           end
 | _ => None          
 end. 
 
(* General case 

Clause : recPred a1 a2 -> recPred (cons1 a1 a2) (cons2 a1 a2) 

first argument input, second argument output.

=
Fixpoint recPredfn (a1 : nat) : option type 
...

 match a1 with
  | cons1 a1' a2' => match recPredfn a1' with
                      | Some x => if (Eqb a2' x) then Some (cons2 a1' a2') else None
                      | _  => None
  
1 Clause = 1 match statement 
*)                      
        
                                  
 

  
 



(*Definition animateAuto (kn : kername) (inputVars : (list string)) (outputVars : list string) (fuel : nat) : TemplateMonad unit :=
  mut <- tmQuoteInductive kn ;;
  match ind_bodies mut with
  | [ one ] =>
    conjs <- general.collect_conjuncts (ind_ctors one) ;;
    
    t' <- DB.deBruijn (animateEqual.genFun conj inputVars outputVars fuel)  ;; 
    f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) t' ;; tmPrint f ;;
    lemma1_name <- tmFreshName "lemma" ;;
    lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;;
    tmMsg "done"
    (* sepConj <- tAppDes conjuncts ;; *)
    (* there has to be something clever here *)
     (*ret conjuncts *)
  | _ => tmFail "Not one type in mutually inductive block." 
  end. *)






