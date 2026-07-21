(** * TestCoinductive: Coinductive Stream Relations
    Tests animation of coinductive relations over infinite streams.
    Covers integration, zipping, equality, filtering, and length. *)

Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.
Require Import Animation.EqualityResolution.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.
Require Import Animation.coIndPreProc.
From Stdlib Require Import List.
From Stdlib Require Import Streams.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.

Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.
Print Stream.
Module prodRel.
(** prodRel: both mode positions are [list nat * list nat].
    Only the top-level [prod] is specialised; [list nat] is NOT independently
    in the lifting set, so [pair' : list nat -> list nat -> prodlistnatlistnat']. *)
Inductive prodRel : list nat * list nat -> list nat * list nat -> Prop :=
| pCons : forall l1 l2, prodRel (l1,l2) ((0 :: l1), (0 :: l2)).


MetaRocq Run (animate_coinductive_with_lift <? prodRel ?>
  [("prodRel", ([0], [1]))] 200).

Compute prodRelAnimatedTopFn 10 (Success (list nat * list nat) ([2;3],[8])).  
End prodRel.
(** mixedRel: index 0 is [list nat] (direct mode position → listnat enters lifting set)
    and index 1 is [list nat * list nat] (nested → prodlistnatlistnat enters lifting set).
    Because [listnat] is independently lifted, [prodlistnatlistnat'] should have
    [pair' : listnat' -> listnat' -> prodlistnatlistnat']. *)
Module mixedRel.
Inductive mixedRel : list nat -> list nat * list nat -> Prop :=
| mCons : forall l, mixedRel l (l, 0 :: l).

MetaRocq Run (animate_coinductive_with_lift <? mixedRel ?>
  [("mixedRel", ([0], [1]))] 200).
  
Compute mixedRelAnimatedTopFn 10 (Success (list nat) ([2;3])).  
End mixedRel. 

Module STLCStepTr.

Inductive ty : Type :=
| TBool : ty
| TArrow : ty -> ty -> ty.

Inductive tm : Type :=
| tvar : string -> tm
| tapp : tm -> tm -> tm
| tabs : string -> ty -> tm -> tm
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm.
(*
Definition isVal (t : tm) : nat :=
  match t with
  | tvar _ => 1
  | tabs _ _ _ => 1
  | ttrue => 1
  | tfalse => 1
  
  
  end.
*)
Fixpoint eqFnty (tp : ty) (tp2 : ty) : bool :=
match tp with
| TBool => match tp2 with
           | TBool => true
           | _ => false
           end
| TArrow t1 t2  => match tp2 with
                     | TBool => false
                     | TArrow t1' t2'  => andb (eqFnty t1 t1') (eqFnty t2 t2') 
                     end
end.           

CoInductive coLst : Type :=
| coNil : coLst
| coSeq : tm -> coLst -> coLst.



Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tvar y => if String.eqb x y then s else t
  | tabs y T t1 => if String.eqb x y then t else tabs y T (subst x s t1)
  | tapp t1 t2 => tapp (subst x s t1) (subst x s t2)
  | ttrue => ttrue
  | tfalse => tfalse
  | tif t1 t2 t3 => tif (subst x s t1) (subst x s t2) (subst x s t3)
  
  end.

(* [step] is a standalone block; [bigStepTr] calls it from a separate block. *)

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall (z : string) (T : ty) (t w  : tm),
   step (tapp (tabs z T t) w) (subst z w t)
| ST_App1 : forall (t1 t1' t2 : tm),
    step t1 t1' ->
    step (tapp t1 t2) (tapp t1' t2)
| ST_IfTrue : forall (t1 t2 : tm),
    step (tif ttrue t1 t2) t1
| ST_IfFalse : forall (t1 t2 : tm),
    step (tif tfalse t1 t2) t2
| ST_If : forall (t1 t1' t2 t3 : tm),
    step t1 t1' ->
    step (tif t1 t2 t3) (tif t1' t2 t3)
| ST_Val1 : forall s, step (tvar s) (tvar s)
| ST_Val2 : forall v1 v2 v3, step (tabs v1 v2 v3) (tabs v1 v2 v3)
| ST_Val3 : step ttrue ttrue
| ST_Val4 : step tfalse tfalse.

CoInductive bigStepTr : tm -> coLst -> Prop :=
| bigVal1 : forall s, bigStepTr (tvar s) ((coSeq (tvar s)) coNil) 
| bigVal2 : forall v1 v2 v3, bigStepTr (tabs v1 v2 v3) ((coSeq (tabs v1 v2 v3)) coNil)
| bigVal3 : bigStepTr ttrue ((coSeq ttrue) coNil)
| bigVal4 : bigStepTr tfalse ((coSeq tfalse) coNil)
| bigStep : forall t tr_lst t',
    step t t' /\ bigStepTr t' tr_lst -> bigStepTr t (coSeq t' tr_lst).
MetaRocq Run (animate_coinductive_with_lift <?bigStepTr?>
               [("bigStepTr", ([0],  [1])); ("step", ([0],  [1]))
                ]
               100).

Definition omega : tm :=
  tapp (tabs "x" TBool (tapp (tvar "x") (tvar "x")))
       (tabs "x" TBool (tapp (tvar "x") (tvar "x"))).
                      
Compute bigStepTrAnimatedTopFn 25 (Success tm omega). 
Compute bigStepTrAnimatedTopFn 25 (Success tm (tif (tapp (tabs "x" TBool (tvar "x")) ttrue) tfalse ttrue)).              
End STLCStepTr.

Module zip.

(** A stream of naturals, with explicit undefined and nil sentinels. *)
CoInductive stream : Type :=
| nil : stream
| Seq : nat -> stream -> stream.


CoFixpoint from (n : nat) : stream := Seq n (from (S n)).


(* ------------------------------------------------------------------ *)
(** ** Zip two streams *)

CoInductive zipSt : stream -> stream -> stream -> Prop :=
| zip : forall n m s1 s2 s3 s4 s5 s6,
    s1 = Seq n s2 /\ s3 = Seq m s4 /\ zipSt s2 s4 s5 /\ s6 = Seq n (Seq m s5)
    -> zipSt s1 s3 s6.



MetaRocq Run (animate_coinductive_with_lift <? zipSt ?>
  [("zipSt", ([0;1], [2]))] 100).

Compute  (zipStAnimatedTopFn 6 (Success (stream * stream) (from 7, from 9))).
End zip.
(* ------------------------------------------------------------------ *)
(** ** Stream equality *)

Module eqSt.
CoInductive stream : Type :=
| nil : stream
| Seq : nat -> stream -> stream.
CoFixpoint from (n : nat) : stream := Seq n (from (S n)).

CoInductive eqSt : stream -> stream -> bool -> Prop :=
| eqNil : eqSt nil nil true
| eqC : forall n m s2 s4 u, n = m /\ eqSt s2 s4 u -> eqSt (Seq n s2) (Seq m s4) u
| neqC : forall n m s2 s4, false = Nat.eqb n m -> eqSt (Seq n s2) (Seq m s4) false.



MetaRocq Run (animate_coinductive_with_lift <? eqSt ?>
  [("eqSt", ([0;1], [2]))] 100).

Compute (eqStAnimatedTopFn 12 (Success (stream * stream) (from 8, from 8))).
Compute (eqStAnimatedTopFn 12 (Success (stream * stream) (from 8, from 9))).
End eqSt.
(* ------------------------------------------------------------------ *)
Module isEven.
(** ** Filter even elements *)

Fixpoint isEven (n : nat) : bool :=
  match n with
  | 0     => true
  | 1     => false
  | S (S m) => isEven m
  end.

CoInductive stream : Type :=
| nil : stream
| Seq : nat -> stream -> stream.
CoFixpoint from (n : nat) : stream := Seq n (from (S n)).
  

CoInductive filterEven : stream -> stream -> Prop :=

| filtNil : filterEven nil nil
| filtE   : forall n s1 s2, true  = isEven n /\ filterEven s1 s2 -> filterEven (Seq n s1) (Seq n s2)
| filtOdd : forall n s1 s2, false = isEven n /\ filterEven s1 s2 -> filterEven (Seq n s1) s2.


MetaRocq Run (animate_coinductive_with_lift <? filterEven ?>
  [("filterEven", ([0], [1]))] 100).

Compute ((filterEvenAnimatedTopFn 30 (Success stream (from 0)))).
End isEven.

Module integrateStreams.
(** A stream of naturals, with explicit undefined and nil sentinels. *)
CoInductive stream : Type :=
| nil : stream
| Seq : nat -> stream -> stream.




CoFixpoint from (n : nat) : stream := Seq n (from (S n)).

(* ------------------------------------------------------------------ *)
(** ** Integrate *)

CoInductive Integrate : stream -> stream -> Prop :=
| integNil : Integrate nil nil
| integ : forall s2 s3 n s5, Integrate s2 s3 /\ addStm n s3 s5 -> Integrate (Seq n s2) (Seq n s5)

with addStm : nat -> stream -> stream -> Prop :=
| addStmNil : forall m, addStm m nil nil
| plusm : forall m s1 n s2, addStm m s1 s2 -> addStm m (Seq n s1) (Seq (m + n) s2).


MetaRocq Run (animate_coinductive_with_lift <? Integrate ?>
  [("Integrate", ([0], [1])); ("addStm", ([0;1], [2]))] 100).

(** Integrate [4, 5, 6, …] gives [4, 9, 15, …] (prefix sums). *)
Compute (IntegrateAnimatedTopFn 25 (Success stream (from 4))).
Compute (IntegrateAnimatedTopFn 25 (Success stream (Seq 4 (Seq 3 (Seq 2 nil))))).
End integrateStreams.  


Module ImpSem.

Inductive co_vars : Type :=
| pure        : (nat -> nat) -> co_vars.


Definition set (vs : nat -> nat) (v n : nat) : nat -> nat :=
  fun v' => if Nat.eqb v v' then n else vs v'.

Inductive exp : Type :=
| Const : nat -> exp
| Var   : nat -> exp
| Plus  : exp -> exp -> exp.

Fixpoint eqFnexp (e1: exp) (e2 : exp) : bool :=
match e1 with
| Const n => match e2 with
             | Const m => Nat.eqb n m
             | _ => false
             end
| Var n =>   match e2 with
             | Var m => Nat.eqb n m
             | _ => false
             end
| Plus e1' e1'' => match e2 with
                   | Plus e2' e2'' => andb (eqFnexp e1' e2') (eqFnexp e2' e2'')
                   | _ => false
                   end
end.                                             

Fixpoint evalExp (vs : nat -> nat) (e : exp) : nat :=
  match e with
  | Const n     => n
  | Var v       => vs v
  | Plus e1 e2  => evalExp vs e1 + evalExp vs e2
  end.

Inductive cmd : Type :=
| Assign : nat -> exp -> cmd
| Seq    : cmd -> cmd -> cmd
| While  : exp -> cmd -> cmd.

CoInductive evalCmd : co_vars -> cmd -> co_vars -> Prop :=
| EvalAssign     : forall vs' vs v e,
    vs' = pure vs
    -> evalCmd vs' (Assign v e) (pure (set vs v (evalExp vs e)))
| EvalSeq        : forall vs1 vs2 vs3 c1 c2,
    evalCmd vs1 c1 vs2 /\ evalCmd vs2 c2 vs3
    -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs' vs e c,
    vs' = pure vs /\ evalExp vs e = 0
    -> evalCmd vs' (While e c) vs'
| EvalWhileTrue  : forall vs1' vs2' vs3' vs1 e c,
    vs1' = pure vs1 /\ evalExp vs1 e <> 0
    /\ evalCmd vs1' c vs2' /\ evalCmd vs2' (While e c) vs3'
    -> evalCmd vs1' (While e c) vs3'.
    
MetaRocq Run (animate_coinductive_with_lift <? evalCmd ?>
  [("evalCmd", ([0;1], [2]))] 500).

Definition prog  := While (Var 4) (Assign 8 (Const 8)).
Definition initFn := pure (fun m : nat => m + 1).
Compute (evalCmdAnimatedTopFn 35 (Success (co_vars * cmd) (initFn, prog))).


Definition prog''   :=
  While (Var 4) (Seq (Assign 4 (Var 3)) (Seq (Assign 3 (Var 2))
    (Seq (Assign 2 (Var 1)) (Assign 1 (Var 0))))).
Definition initFn'' := pure (fun m : nat => m).

Compute (evalCmdAnimatedTopFn 35 (Success (co_vars * cmd) (initFn'', prog''))).

End ImpSem.


Module StackStep.
Definition total_map (A : Type) := string -> A.
Inductive state : Type :=
| stCtor : (string -> nat) -> state. 

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Fixpoint decEqsinstr : forall (t1 t2 : sinstr), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality. decide equality. decide equality. decide equality.
Defined.

Definition eqFnsinstr (t1 t2 : sinstr) : bool :=
  if decEqsinstr t1 t2 then true else false.

Definition stack := list nat.
Definition prog  := list sinstr.



Inductive stack_step : state -> list sinstr -> list nat -> list sinstr -> list nat -> Prop :=
| SS_Push  : forall st stk n p,
     stack_step st (SPush n :: p) stk p (n :: stk) 
| SS_Load  : forall fn stk i p,
     
     stack_step (stCtor fn) (SLoad i :: p)  stk p ((fn) i :: stk) 
   
| SS_Plus  : forall st stk n m p, stack_step st (SPlus :: p) (n :: m :: stk) p ((m + n) :: stk)
| SS_Minus : forall st stk n m p,
    stack_step st (SMinus :: p) (n :: m :: stk) p  ((m - n) :: stk)
| SS_Mult  : forall st stk n m p,
    stack_step st (SMult :: p) (n :: m :: stk) p  ((m * n) :: stk).

   
(* Product type version is VERY SLOW!! NEED TO INVESTIGATE *)
MetaRocq Run (animate_coinductive_with_lift <? stack_step ?>
  [("stack_step", ([0;1;2], [3;4]))] 200). 

Definition empty_state : state :=   (stCtor (fun (_ : string) => 0)).

 
Compute (stack_stepAnimatedTopFn 50
  (Success (state * (list sinstr * list nat))
    (empty_state, ([SPush 3; SPush 4; SPlus], [])))).  

End StackStep.



      

  
