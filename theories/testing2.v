Require Import Animation.animationModulesIntegration2.
Require Import Animation.animationModulesFixPt.


Require Import Animation.animationModulesSimplEq.

Require Import Animation.utils2.
Require Import Animation.animationModulesPatMat.

Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.


Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.

 

 
Inductive type : Type :=
| N : type
| Arr : type -> type -> type.
Inductive term : Type :=
| Con : nat -> term
| Add : term -> term -> term
| Var : nat -> term
| App : term -> term -> term
| Abs : type -> term -> term.

Fixpoint decEqType : forall (t1 t2 : type), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.
 
Fixpoint decEqTerm : forall (t1 t2 : term), {t1 = t2} + {t1 <> t2}.
Proof.

  decide equality. decide equality. decide equality. decide equality.
Defined.

Definition eqFntype (t1 t2 : type) : bool. Admitted.
(*
 :=
  if decEqType t1 t2 then true else false.
*)  
Definition eqFnterm (t1 t2 : term) : bool. Admitted.
(* :=
  if decEqTerm t1 t2 then true else false.
*)  
Print sumbool.  


(*    
Fixpoint eqFntype (t1 : type) (t2 : type) : bool :=


match t1 with
| N => match t2 with
        | N => true
        | _ => false
       end
| Arr t1' t1'' => match t2 with
                   | Arr t2' t2'' => if andb (eqFntype t1' t2') (eqFntype t1'' t2'') then true else false 
                   | _ => false
                  end
end.

Fixpoint eqFnterm (e1 : term) (e2 : term) : bool := 

 
match e1 with
| Con n => match e2 with
           | Con m => if Nat.eqb n m then true else false
           | _ => false
           end
                                      
| Add e1' e1'' => match e2 with
                  | Add e2' e2'' => if andb (eqFnterm e1' e2') (eqFnterm e1'' e2'') then true else false
                  | _ => false
                  end

| Var j => match e2 with
           | Var k => if Nat.eqb j k then true else false
           | _ => false
           end

| App e1' e1''  => match e2 with
                        | App e2' e2''  => if (andb (eqFnterm e1' e2') (eqFnterm e1'' e2''))  then true else false
                        | _ => false
                        end

| Abs t1 e1'  =>  match e2 with
                        | Abs t2 e2'  => if andb (eqFnterm e1' e2') (eqFntype t1 t2) then true else false
                        | _ => false
                        end
end.                                                
*)                                                     
(* Original paper 

Inductive typing Γ : term -> type -> Prop := (* Mode [0], [1]  = type inference, Mode [0;1] [] = type checking *) 
| TCon : forall n, typing Γ (Con n) N
| TAdd : forall e1 e2,
typing Γ e1 N -> typing Γ e2 N ->
typing Γ (Add e1 e2) N
| TAbs : forall e t1 t2,
typing (t1 :: Γ) e t2 ->
typing Γ (Abs t1 e) (Arr t1 t2)
| TVar : forall x t,
lookup Γ x t -> typing Γ (Var x) t
| TApp : forall e1 e2 t1 t2,
typing Γ e2 t1 -> typing Γ e1 (Arr t1 t2) ->
typing Γ (App e1 e2) t2.
*)






Inductive typing : list type -> term -> type -> Prop := (* Mode [0;1], [2]  = type inference, Mode [0;1;2] [] = type checking *) 
| TCon : forall (n : nat) (cxt : list type) (ttm : term) (tp : type), ttm = Con n /\ (N) = tp -> typing cxt ttm tp


| TAdd : forall (e1 e2 e3 : term) (cxt : list type) (tp : type),  tp = N  /\  
typing cxt e1 tp /\ typing cxt e2 tp /\ e3 = Add e1 e2 ->
typing cxt e3 tp


| TAbs : forall (e e2 : term) (t1 t2 t3 : type) (cxt cxt' : list type), cxt' = t1 :: cxt /\ e2 = Abs t1 e /\ t3 = Arr t1 t2 /\
typing cxt' e t2 ->
typing cxt e2 t3


| TVar : forall (j : nat) (e : term) (t : type) (cxt : list type),
lookup cxt j t /\ e = Var j -> typing cxt e t

| TApp : forall (e1 e2 e3 : term) (t1 t2 t3 : type) (cxt : list type), e3 = App e1 e2 /\ t3 = Arr t1 t2 /\
typing cxt e2 t1 /\ typing cxt e1 t3 ->
typing cxt e3 t2 

with lookup : list type -> nat -> type -> Prop :=
 | lookupFn0 : forall (n : nat) (cxt : list type) (t : type) , 0 = n /\ N = t -> lookup cxt n t
 | lookupFnRec : forall (n m : nat) (t t' : type) (cxt : list type) , n = S m /\ lookup cxt m t /\ t' = Arr N t -> lookup cxt n t'.  
 
MetaRocq Run (animAllCl typing <? typing ?> [("typing", ([0;1], [2]));("lookup", ([0;1], [2]))] 100).
Print typingAnimatedTopFn.

Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(Abs (N) (Con 5))))). 

Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(Abs (N) (Add (Con 5) (Var 0)))))).
 
Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(Abs (N) (Add (Con 5) (Var 1)))))).

Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],((Add (Con 5) (Var 1)))))).

Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(App (Abs (N) (Add (Con 5) (Var 0))) (Con 1))))).
 
Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(App (Abs (N) (Add (Con 5) (Var 0))) (Var 0))))).
 
Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(App (Abs (N) (Add (Con 5) (Var 0))) (Var 1))))).

Compute (typingAnimatedTopFn 50 (successPoly ((list type) * term) ([],(App (Abs (Arr N N) (Add (Con 5) (Var 0))) (Var 1))))).



Inductive even : nat -> bool -> Prop := (* mode = ([0], [1] *)
 | even0 : forall (w : nat) (b : bool) , w = 0 /\ b = true -> even w b 
 | evenSucc : forall (w w1 : nat) (b : bool) , odd w b /\ w1 = (S w) /\ b = true -> even w1 b
with odd : nat -> bool -> Prop :=
 | oddSucc : forall (w w1 : nat) (b : bool) , even w b /\ w1 = (S w) /\ b = true -> odd w1 b. 
 

MetaRocq Run (animAllCl even <? even ?> [("even", ([0], [1]));("odd", ([0], [1]))] 100).

Compute evenAnimatedTopFn 30 (successPoly nat 5).
Compute evenAnimatedTopFn 30 (successPoly nat 4).
Compute evenAnimatedTopFn 30 (successPoly nat 3).
Compute evenAnimatedTopFn 30 (successPoly nat 0).



Inductive suffix : list nat -> list nat -> list nat -> Prop := (* mode = ([0;2], [1] *)
 | suffixNil : forall (l1 l2  : list nat), l1 = [] -> suffix l1 l2 l2
 | suffixCons : forall (w : nat) (l1 l2 l3 l4 l5 : list nat), l1 = w :: l2 /\ suffix l2 l3 l4 /\ l5 = w :: l4 -> suffix l1 l3 l5.

MetaRocq Run (animAllCl suffix <? suffix ?> [("suffix", ([0;2], [1]))] 100).

Compute suffixAnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([8;7], [8;7;9;7;8])).
Compute suffixAnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([8;7;9;7;8], [8;7;9;7;8])).

Compute suffixAnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([8;7;9;7;5], [8;7;9;7;8])).
Compute suffixAnimatedTopFn 50 (successPoly ((list nat) * (list nat)) ([8;6], [8;7;9;7;8])).


Inductive prefix : list nat -> list nat -> list nat -> Prop := (* mode = ([0;2], [1] *)
 | prefixNil : forall (l1 l2  : list nat), l1 = [] -> prefix l1 l2 l2
 | prefixCons : forall (w : nat) (l1 l2 l3 l4 l5 : list nat), l1 = w :: l2 /\ prefix l2 l3 l4 /\ l5 = w :: l4 -> prefix l1 l3 l5.

MetaRocq Run (animAllCl prefix <? prefix ?> [("prefix", ([1;2], [0]))] 100).

Inductive append : list nat -> list nat -> list nat -> Prop := (* mode = ([0;1], [2] *)
 | appendNil : forall (l1 l2  : list nat), l1 = [] -> append l1 l2 l2
 | appendCons : forall (w : nat) (l1 l2 l3 l4 l5 : list nat), l1 = w :: l2 /\ append l2 l3 l4 /\ l5 = w :: l4 -> append l1 l3 l5.

MetaRocq Run (animAllCl append <? append ?> [("append", ([0;1], [2]))] 100).




   
