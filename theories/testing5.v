Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.


Require Import Animation.EqualityResolution.

Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.

Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.


Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.
Print option.

Print ind_tp.

CoInductive Stream : Set := Seq { hd : nat; tl : Stream }.
Print Seq.
Print animation_result.
(*
Definition map_outcome_poly (A : Type) (B : Type) (f : A -> B) (a : animation_result A) : animation_result B :=
match a with
| FuelError  => FuelError B 
| Success a' => Success B (f a')
| NoMatch => NoMatch B
end.
*)

(*

CoInductive result_stream (A : Type) := 
| Scons : A -> result_stream A -> result_stream A.

Compute Scons nat 4.

CoFixpoint makeStm (A : Type) (B : Type) (f : nat -> A -> B) (n0 : nat) (inp : A) : result_stream B :=
Scons B (f n0 inp) (makeStm A B f (S n0) inp). 

Definition streamFromFunction (A : Type) (B : Type) (f : nat -> A -> B) (inp : A) : result_stream B :=
makeStm A B f 0 inp.
 

  
Print hd.
*)

CoInductive Counter : Type :=
| incr : Counter -> Counter.


(*
Definition eqFnStream : Stream -> Stream -> bool := (fun s1 s2 => true).
Definition eqFnCounter : Counter -> Counter -> bool := (fun s1 s2 => true).
*)          


CoFixpoint from (n : nat) : Stream :=
Seq n (from (S n)).

Definition hdPoly {A : Type} (s : result_stream A) : A :=
match s with 
| Scons h0 t0 => h0
end.

Definition tlPoly {A : Type} (s : result_stream A) : result_stream A :=
match s with 
| Scons h0 t0 => t0
end.


Fixpoint streamNth {A : Type} (n : nat) (s : result_stream A) :  A :=
match n with
| 0 => hdPoly s
| S n => streamNth n (tlPoly s)
end.



CoInductive Integrate : Stream -> Stream -> Prop :=
| integ : forall s2 s3 n s5 ,Integrate s2 s3 /\ addStm n s3 s5 -> Integrate (Seq n s2) (Seq n s5)
with
addStm : nat -> Stream -> Stream -> Prop :=
| plusm : forall s m s1 n s2, s = Seq n s1 /\ addStm m s1 s2 -> addStm m s (Seq (m + n) s2).
Parameter IntegrateRest : Stream -> Stream.
Parameter addStmRest : (nat * Stream) -> Stream.
Parameter zipStRest : (Stream * Stream) -> Stream.

MetaRocq Run (animateCoinductive Integrate <? Integrate ?> [("Integrate", ([0], [1])); ("addStm", ([0;1], [2]))] 500).

Print IntegrateAnimatedTopFn.

MetaRocq Run (r <- tmEval all (streamNth 15 (IntegrateAnimatedTopFnStream (Success (Stream) ((from 0))))) ;; tmPrint r).


CoInductive zipSt : Stream -> Stream -> Stream -> Prop :=
 | zip: forall n m s1 s2 s3 s4 s5 s6, s1 = Seq n s2  /\ s3 = Seq m s4 /\ zipSt s2 s4 s5 /\ s6 = Seq n ((Seq m) s5)
                      -> zipSt s1 s3 s6. 


MetaRocq Run (animateCoinductive zipSt <? zipSt ?> [("zipSt", ([0;1], [2]))] 500).

Print zipStAnimatedTopFn.
    
Print zipStAnimatedTopFnStream.

Check zipStAnimatedTopFnStream.



Compute (streamNth 6 (zipStAnimatedTopFnStream (Success (Stream * Stream) ((from 7), (from 9))))).


Inductive coBool : Type :=
| coT : coBool
| coF : coBool.



CoInductive eqSt : Stream -> Stream -> bool -> Prop :=
 | eqC: forall n m s1 s2 s3 s4 u , s1 = Seq n s2  /\ s3 = Seq m s4 /\ n = m /\  eqSt s2 s4 u   -> eqSt s1 s3 u
 | neqC : forall n m s1 s2 s3 s4 u , s1 = Seq n s2  /\ s3 = Seq m s4 /\ Nat.eqb n m = false /\  u = false   -> eqSt s1 s3 u. 

Parameter eqStRest : (Stream * Stream) -> bool.
(*
Definition eqFncoBool (c1 : coBool) (c2 : coBool) : bool := true.
*)

MetaRocq Run (animateCoinductive eqSt <? eqSt ?> [("eqSt", ([0;1], [2]))] 500).

Compute (streamNth 10 (eqStAnimatedTopFnStream (Success (Stream * Stream) ((from 9), (from 9))))).

Compute (streamNth 0 (eqStAnimatedTopFnStream (Success (Stream * Stream) ((from 5), (from 9))))).

Compute (streamNth 7 (eqStAnimatedTopFnStream (Success (Stream * Stream) ((from 5), (from 9))))).








(*
CoFixpoint appStm (s : Stream) (s2 : Stream) :=
match s with
| Seq m s' => let o := Seq m (appStm s' s2) in o
end.

Definition clauseAn (A : Type) (B : Type) (topAnim' : A -> B) : A -> B. Admitted.

CoFixpoint topAnim (A : Type) (B: Type) : A -> B :=
clauseAn A B (topAnim A B).


 CoFixpoint topAnim (A : Type) (B: Type)  : A -> B :=
clauseAn A B (clauseAn A B (topAnim A B)).

 CoFixpoint topAnim (A : Type) (B: Type)  : A -> B :=
clauseAn A B (clauseAn A B (clauseAn A B (topAnim A B))). 

*)
(* Co-Inductive append animate *)





Definition clauseAn (s : Stream) (s2 : Stream) (topAnim : Stream -> Stream -> Stream) :=
match s with
| Seq m s' => let o := Seq m (topAnim s' s2) in o
end.

CoFixpoint topAnim (s : Stream) (s' : Stream) : Stream :=
clauseAn s s' topAnim.






CoInductive length : Stream -> Counter -> Prop :=
| plus1 : forall s c n s1 c1, s = Seq n s1 /\ length s1 c1 /\ c = incr c1 -> length s c. 


Parameter lengthRest : Stream -> Counter.

MetaRocq Run (animateCoinductive length <? length ?> [("length", ([0], [1]))] 500).

Compute (streamNth 20 (lengthAnimatedTopFnStream (Success (Stream) (from 5)))).


Fixpoint isEven (n : nat) : bool :=
match n with
| 0 => true
| 1 => false
| S (S m) => isEven m
end.

CoInductive filterEven : Stream -> Stream -> Prop :=
| filtE : forall s n s1 s2 s3 , s = Seq n s1 /\ (true = isEven n) /\ filterEven s1 s2 /\ s3 = Seq n s2 -> filterEven s s3
| filtOdd : forall s n s1 s2 , s = Seq n s1 /\ (false = isEven n) /\ filterEven s1 s2  -> filterEven s s2.

Parameter filterEvenRest : Stream -> Stream.

MetaRocq Run (animateCoinductive filterEven <? filterEven ?> [("filterEven", ([0], [1]))] 500).


Compute (streamNth 20 (filterEvenAnimatedTopFnStream (Success (Stream) (from 0)))).



(* Correctness criteria :

(One Success element in stream)

Co-Inductive or Inductive interpretation of R

given an input i to relation R, say (i,R) is 'order independent with result' if the following holds : there exists j (j might not be fixed) st. R(i,j) holds, where at each stage of the computation when solving for 
for some relation instance R'(i',j') the clauses in R' (where R' may be R itself) maybe applied in aribtrary order. 

Then given such an (i, R) if there exists n st. stmN n RTopFnAnimatedStream Success (i) = Success (F u RRest), then there exists some k st
R(i, F u k) holds. (i.e. u is guaranteed to be the prefix of j where R(i,j) holds.)

if there exists n st. stmN n RTopFnAnimatedStream Success (i) = Success (j) where j does not use the symbol RRest, then it must be the case that 
R (i,j) holds.

(one noMatch element in result stream)

Co-Inductive or Inductive interpretation of R 

Given R say R is 'order independent' if for any any input i there exists j (possibly not fixed) st. R (i,j) under arbitrary clause order of  the involved relations at each stage of the computation or 
it is always the case that there is no j st. R (i, j) regardless of the clause order used at each stage of the computation. 

Then given such an R and on some aribitrary input i, if there exists n st. stmN n RTopFnAnimatedStream Success (i) = NoMatch then there exists no j st. R(i,j).


(Constant Success stream)

Co-Inductive interpretation of R or Inductive interpretation of R with all inductive types : 

Given R is order independent if there exists m st. for all n>= m, stmN n RTopFnAnimatedStream Success (i) = Success j, for some fixed j where j does  not use the parameter RRest, then it must be the case that R(i,j).
(but not for inductive interpretation of a relation over co-inductive types, for eg. the inductive interpretation of zipSt is empty, but zipStAnimatedTopFnStream is not a stream of NoMatch)




(given an inductive interpretation of a relation involving only inductive types the output stream is guaranteed to become a constant stream without 
the symbol RRest after a finite n. Not the case for co-induction.) 



The statements can be simplified in case the clauses in R and all sub-relations are non-overlapping. Then R is guaranteed to be 
order independent. If in addition R is total then for every input i (i, R) is order independent with result

Note that the key difference between an inductive interpretation and co-inductive interpretion is wheter or not an input has a result at all, the statements are saying that if 
both interpretations produce a result for a given input, the result must have the same 'shape' 

*)




(*
Check rest
                   (Success Stream
                      ((cofix Fcofix (x : nat) : Stream := {| hd := x; tl := Fcofix (S x) |}) 5)).

Definition addOut {A:Type} {B : Type} (f : A -> B) (n : nat) (input : animation_result A): (animation_result B) :=
 match input with
 | Success input' => Success B (f input')
 | FuelError => FuelError B 
 | NoMatch => NoMatch B
end. 
Parameter errCounter : Counter.
Definition removeOut (x : animation_result Counter) : Counter :=
match x with
| Success x' => x'
| _ => errCounter
end.
MetaRocq Run (f' <- tmEval all (fun topFn s  => removeOut (plus1Animated  (addOut (topFn)) 5 (Success Stream s))) ;; tmDefinition "Plus1An" f').

Compute (fun f => Plus1An f).



Compute (fun f => Plus1An f (Seq 0 (Seq 1 (from 4)))).

Definition plus1An (topfn : Stream -> Counter) (s : Stream) : Counter :=
match s with
| Seq n s' => incr (topfn s' )
end.

 

CoFixpoint lengthAnimT  :=
(plus1An lengthAnimT).

CoFixpoint lengthAnimT'  :=
(Plus1An lengthAnimT').





Print lengthAnimatedTopFn.

*)










(*


Print appendStAnimatedTopFn.
CoFixpoint from (n:nat) : Stream := Seq n (from (S n)).
Definition tFun : nat -> animation_result (Stream × Stream) -> animation_result Stream := fun x y => Success Stream (from 7).




Compute appStAnimated tFun 5 (Success (Stream * Stream) ((from 13), (from 1))).

(*
Theorem try : appendStAnimatedTopFn 9 (Success (Stream * Stream) ((from 0), (from 1))) = FuelError Stream.
simpl. simpl. simpl. simpl. 
*)




CoFixpoint appStm (s : Stream) (s2 : Stream) :=
match s with
| Seq m s' => Seq m (appStm s' s2)
end.


CoInductive appendSt'' : Stream -> nat -> Stream -> Prop :=
 | appSt'': forall n s1 s2, s2 = Seq n s1  -> appendSt'' s1 n s2. 

MetaRocq Run (animateInductive appendSt'' <? appendSt'' ?> [("appendSt''", ([0;1], [2]))] 500).

Compute appendSt''AnimatedTopFn 5 (Success (Stream * nat) ((from 0), 1)).

CoInductive ilist : Type :=
| iCons : nat -> ilist -> ilist.
Search (bool -> bool -> bool).

Parameter eqFnilist : ilist -> ilist -> bool.

Axiom eqFnilistRed : forall il1 il2 m1 m2, m1 = m2 -> true = eqFnilist il1 il2 -> true = eqFnilist (iCons m1 il1) (iCons m2 il2).

CoInductive appendi : ilist -> ilist -> ilist -> Prop :=
 | appilist: forall n ilist1 ilist2 ilist3 ilist4 ilist5, ilist1 = iCons n ilist2 /\ appendi ilist2 ilist3 ilist4 /\ 
                     ilist5 = iCons n ilist4 -> appendi ilist1 ilist3 ilist5. 





CoInductive eqSt : Stream -> Stream -> bool -> Prop :=
 | eqC: forall n m s1 s2 s3 s4 b1 b2, s1 = Seq n s2  /\ s3 = Seq m s4 /\ n = m /\  eqSt s2 s4 b1 /\ b2 = (b1) -> eqSt s1 s3 b2. 


MetaRocq Run (animateInductive eqSt <? eqSt ?> [("eqSt", ([0;1], [2]))] 500).

Print eqStAnimatedTopFn.


Definition esatf :=
fix eqStAnimatedTopFn (fuel : nat) (input : animation_result (Stream × Stream)) {struct fuel} :
    animation_result Stream :=
  match fuel with
  | 0 => Success Stream s
  | 1 => Success Stream s
  | 2 => Success Stream s
  | S remFuel =>
      dispatch_outcome_poly_ext (Stream × Stream) Stream [eqCAnimated eqStAnimatedTopFn] remFuel input
  end
with dispatch_outcome_poly_ext
  (A B : Type) (lst : list (nat -> animation_result A -> animation_result B)) (fuel' : nat)
  (input' : animation_result A) {struct fuel'} : animation_result B :=
  match fuel' with
  | 0 => FuelError B
  | S remFuel' =>
      match lst with
      | [] => NoMatch B
      | h :: t =>
          match h remFuel' input' with
          | @NoMatch _ => dispatch_outcome_poly_ext A B t remFuel' input'
          | _ => h remFuel' input'
          end
      end
  end
for
eqStAnimatedTopFn.

Compute esatf 10 (Success (Stream * Stream) ((from 0), (from 1))).

Compute esatf 10 (Success (Stream * Stream) ((from 1), (from 1))).







*)                      
