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
 
  
Definition animate'' (conjs : term) (inputVars : (list string)) (outputVars : list string) (fuel : nat) : TemplateMonad unit :=
  t' <- DB.deBruijn (animateEqual.genFun conjs inputVars outputVars fuel)  ;; 
  f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) t' ;; tmPrint f ;;
  lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;;
  tmMsg "done".

MetaRocq Run (general.animate <? foo ?>).  


  


  
  

       


Definition fooTerm : term := 
 (tApp <%and%>
   [tApp <%eq%> [<%nat%>; tVar "e"; tVar "b"];
    tApp <%and%>
      [tApp <%eq%> [<%nat%>; tVar "d"; tVar "c"];
       tApp <%and%>
         [tApp <%eq%> [<%nat%>; tVar "c"; tApp (tVar "g3") [tVar "a"; tVar "e"]];
          tApp <%eq%> [<%nat%>; tApp (tVar "g1") [tVar "d"]; tApp (tVar "g2") [tVar "a"]]]]]).

(*MetaRocq Run (fooTerm <- general.animate2 <? foo ?> ;; animate'' fooTerm ["a"; "b"] ["c"; "d";"e"] 10). *)

MetaRocq Run (animate'' fooTerm ["a"; "b"] ["c"; "d";"e"] 10).

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
 
MetaRocq Run (general.animate <? foo' ?>).

Definition foo'Term : term := 
 (tApp <%and%>
   [tApp <%eq%> [<%nat%>; tApp (tVar "g1") [tVar "d"]; tApp (tVar "g2") [tVar "a"]];
    tApp <%and%>
      [tApp <%eq%> [<%nat%>; tVar "d"; tVar "c"];
       tApp <%and%>
         [tApp <%eq%> [<%nat%>; tVar "c"; tApp (tVar "g3") [tVar "a"; tVar "e"]];
          tApp <%eq%> [<%nat%>; tVar "e"; tVar "b"]]]]).



MetaRocq Run (animate'' foo'Term ["a" ; "b"] ["c"; "d";"e"] 30).

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
 
MetaRocq Run (general.animate <? foo'' ?>).

Definition foo''Term : term := 
(tApp <%and%>
   [tApp <%eq%> [<%nat%>; tApp (tVar "g1") [tVar "d"]; tApp (tVar "g2") [tVar "a"]];
    tApp <%and%>
      [tApp <%eq%> [<%nat%>; tVar "d"; tVar "c"];
       tApp <%and%>
         [tApp <%eq%> [<%nat%>; tVar "c"; tApp (tVar "g3") [tVar "a"; tVar "e"]];
          tApp <%eq%> [<%nat%>; tVar "b"; tVar "e"]]]]).




MetaRocq Run (animate'' foo''Term ["a" ; "b"] ["c"; "d";"e"] 30).
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
 
MetaRocq Run (general.animate <? foo4 ?>).

Definition foo4Term : term := 
 (tApp <%and%>
   [tApp <%eq%> [<%nat%>; tApp (tVar "g1") [tVar "d"]; tApp (tVar "g2") [tVar "a"]];
    tApp <%and%>
      [tApp <%eq%> [<%nat%>; tVar "d"; tVar "b"];
       tApp <%and%>
         [tApp <%eq%> [<%nat%>; tApp (tVar "g4") [tVar "a"; tVar "e"; tVar "a"; tVar "e"]; tVar "c"];
          tApp <%eq%> [<%nat%>; tVar "b"; tVar "e"]]]]).





Definition justAnimate (conjs : term) (inputVars : (list string)) (outputVars : list string) (fuel : nat) : TemplateMonad unit :=
  t' <- DB.deBruijn (animateEqual.genFun conjs inputVars outputVars fuel)  ;; 
  f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) t' ;; tmPrint f ;;
  (* lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;; *)
  tmMsg "done". 


MetaRocq Run (justAnimate foo4Term ["a" ; "b"] ["c"; "d";"e"] 100). 




MetaRocq Run (justAnimate foo4Term ["a" ; "d"] ["c"; "e"] 100). 


Inductive foo5 : nat -> nat -> Prop :=
 | cstr5 : forall a b, a = b  -> foo5 a b.
 
MetaRocq Run (general.animate <? foo5 ?>).

Definition foo5Term : term := 
 (tApp <%eq%> [<%nat%>; tVar "a"; tVar "b"]).


Definition justAnimate2 (conjs : term) (inputVars : (list string)) (outputVars : list string) (fuel : nat) : TemplateMonad unit :=
  t' <- DB.deBruijn (animateEqual.genFun conjs inputVars outputVars fuel)  ;; 
  f <- @tmUnquoteTyped (nat -> (option (list nat))) t' ;; tmPrint f ;;
  (* lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;; *)
  tmMsg "done". 


MetaRocq Run (justAnimate2 foo5Term ["a"] ["b"] 100). 
 
  

End s.

          


 
  



Inductive tuple : nat -> nat -> (prod nat nat) -> Prop :=
 | tupleCon : forall (a : nat), forall (b : nat), forall (y : (prod nat nat)), (a, S b) = y -> tuple a b y.  (*RHS of equality not v imp*)
         

MetaRocq Quote Recursively Definition tupleTerm := tuple.
MetaRocq Run (general.animate <? tuple ?>).

Definition tupleTermConj : term := 
 (tApp <%eq%>
   [tApp
      (tInd
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0 |}
         [])
      [<%nat%>; <%nat%>];
    tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0 |} 0
         [])
      [<%nat%>; <%nat%>; tVar "a";
       tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "b"]];
    tVar "y"]).



MetaRocq Run (t <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption ((typeConstrPatMatch.removeopTm (typeConstrPatMatch.mkLamfromInd2 tupleTermConj tupleTerm ["a" ; "b"] 25))))) ;; tmUnquote t >>= tmPrint).
(*Compute (* typeConstrPatMatch.removeopTm (DB.deBruijnOption) *) ((typeConstrPatMatch.removeopTm (typeConstrPatMatch.mkLamfromInd2 tupleTermConj tupleTerm ["a" ; "b"] 25))). *)



Inductive singleton : nat -> list nat -> Prop :=
 | singletonCon : forall (a : nat), forall (y : list nat), (a :: [])  = y -> singleton a  y.  (*RHS of equality not v imp*)
 
MetaRocq Quote Recursively Definition singletonTerm := singleton.
MetaRocq Run (general.animate <? singleton ?>).

Definition singletonTermConj : term :=
 (tApp <%eq%>
   [tApp
      (tInd
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |}
         [])
      [<%nat%>];
    tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1
         [])
      [<%nat%>; tVar "a";
       tApp
         (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
            |} 0 [])
         [<%nat%>]];
    tVar "y"]).

MetaRocq Run (t <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption ((typeConstrPatMatch.removeopTm (typeConstrPatMatch.mkLamfromInd2 singletonTermConj singletonTerm ["a"] 25))))) ;; tmUnquote t >>= tmPrint).

(* 4 *)

Inductive myType' : Set :=
| mycr1' : nat -> myType'
| mycr2' : nat -> myType'.

Inductive myType : Set :=
| mycr2 : myType' -> nat -> myType
| mycr3 : myType.


Inductive baz' : nat -> nat -> myType -> Prop :=
 | bazCon' : forall (a : nat), forall (x : nat), forall (y : myType), mycr2 (mycr1' a) (S x) = y -> baz' a x y.  (*RHS of equality not v imp*)
 

MetaRocq Quote Recursively Definition baz'Term := baz'. 
MetaRocq Run (general.animate <? baz' ?>).
Definition baz'TermConj : term :=
 (tApp <%eq%>
   [tInd {| inductive_mind := (MPfile ["testCases"; "Animation"], "myType"); inductive_ind := 0 |} [];
    tApp
      (tConstruct
         {| inductive_mind := (MPfile ["testCases"; "Animation"], "myType"); inductive_ind := 0 |} 0 [])
      [tApp
         (tConstruct
            {| inductive_mind := (MPfile ["testCases"; "Animation"], "myType'"); inductive_ind := 0 |} 0
            [])
         [tVar "a"];
       tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "x"]];
    tVar "y"]).




MetaRocq Run (t <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption ((typeConstrPatMatch.removeopTm (typeConstrPatMatch.mkLamfromInd2 baz'TermConj baz'Term ["x" ; "a"] 25))))) ;; tmUnquote t >>= tmPrint).

MetaRocq Run (t <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption ((typeConstrPatMatch.removeopTm (typeConstrPatMatch.mkLamfromInd2 baz'TermConj baz'Term ["a" ; "x"] 25))))) ;; tmUnquote t >>= tmPrint).











Inductive fooCon : nat -> nat -> nat -> nat -> Prop :=
 | cstrCon : forall a b c d,  [1 ; S c]  = [S b ; d]  -> fooCon a b c d.
 
MetaRocq Run (general.animate <? fooCon ?>).

Definition fooConTerm : term :=
 (tApp <%eq%>
   [tApp
      (tInd
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |}
         [])
      [<%nat%>];
    tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1
         [])
      [<%nat%>;
       tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
         [tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 0 []];
       tApp
         (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
            |} 1 [])
         [<%nat%>;
          tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "c"];
          tApp
            (tConstruct
               {|
                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
               |} 0 [])
            [<%nat%>]]];
    tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1
         [])
      [<%nat%>; tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "b"];
       tApp
         (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
            |} 1 [])
         [<%nat%>; tVar "d";
          tApp
            (tConstruct
               {|
                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
               |} 0 [])
            [<%nat%>]]]]).


Compute (typeConstrReduce.makeConjSimpl (typeConstrReduce.deconTypeConGen'' (typeConstrReduce.deConConj1 fooConTerm) (typeConstrReduce.deConConj2 fooConTerm) 20)).  

(* Returns conjuncts corresponding to : 0 = b , S c = d *)



Inductive fooCon' : nat -> nat -> nat -> nat -> Prop :=
 | cstrCon' : forall a b c d, [S b ; d] = [1 ; S c]  -> fooCon' a b c d.
 
MetaRocq Run (general.animate <? fooCon' ?>).

Definition fooCon'Term := 
 (tApp <%eq%>
   [tApp
      (tInd
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |}
         [])
      [<%nat%>];
    tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1
         [])
      [<%nat%>; tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "b"];
       tApp
         (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
            |} 1 [])
         [<%nat%>; tVar "d";
          tApp
            (tConstruct
               {|
                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
               |} 0 [])
            [<%nat%>]]];
    tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1
         [])
      [<%nat%>;
       tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
         [tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 0 []];
       tApp
         (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
            |} 1 [])
         [<%nat%>;
          tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "c"];
          tApp
            (tConstruct
               {|
                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
               |} 0 [])
            [<%nat%>]]]]).


Compute (typeConstrReduce.makeConjSimpl (typeConstrReduce.deconTypeConGen'' (typeConstrReduce.deConConj1 fooCon'Term) (typeConstrReduce.deConConj2 fooCon'Term) 20)).  

(* Returns conjuncts corresponding to : b = 0 , d = S c *)

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






