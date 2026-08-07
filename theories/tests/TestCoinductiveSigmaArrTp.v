(** * TestCoinductiveTransparentSigma: Tests for animate_coinductive_transparent_sigma.
    Holes in the output are function-typed and wrapped in named inductive types
    (e.g. [zipStAn2Symb]) so that in the output it is clear which function each
    hole corresponds to.  coIndPush positions use [typeNmcoIndPushSymb] wrappers. *)

Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.
Require Import Animation.EqualityResolution.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.
Require Import Animation.HoleyResult.
Require Import Animation.coIndPreProcSigmaArrTp.
From Stdlib Require Import List.
From Stdlib Require Import Streams.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.
Import MetaRocqNotations.
Local Open Scope nat_scope.
Open Scope bs.

(* ------------------------------------------------------------------ *)

Module StackStep.



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




Inductive stack_step : (string -> nat) -> list sinstr -> list nat -> list sinstr -> list nat -> Prop :=
| SS_Push  : forall st stk n p,
     stack_step st (SPush n :: p) stk p (n :: stk) 
| SS_Load  : forall fn stk i p,
     
     stack_step (fn) (SLoad i :: p)  stk p ((fn) i :: stk) 
   
| SS_Plus  : forall st stk n m p, stack_step st (SPlus :: p) (n :: m :: stk) p (((fun x y => x + y) m n) :: stk)
| SS_Minus : forall st stk n m p,
    stack_step st (SMinus :: p) (n :: m :: stk) p  (((fun x y => x - y) m n) :: stk)
| SS_Mult  : forall st stk n m p,
    stack_step st (SMult :: p) (n :: m :: stk) p  (((fun x y => x * y) m n) :: stk).

   
(* Product type version is VERY SLOW!! NEED TO INVESTIGATE *)
MetaRocq Run (animate_coinductive_with_fn_pos <? stack_step ?>
  [("stack_step", ([0;1;2], [3;4]))] 200). Print fnType0.

Definition empty_state : state :=   (stCtor (fun (_ : string) => 0)).

 
Compute (stack_stepTransparentAnimatedTopFn 50
  (Success (state * (list sinstr * list nat))
    (empty_state, ([SPush 3; SPush 4; SPlus], [])))).  

End StackStep.





Module ImpSem.
(*
Inductive co_vars : Type :=
| pure        : (nat -> nat) -> co_vars.
*)

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

CoInductive evalCmd : (nat -> nat) -> cmd -> (nat -> nat) -> Prop :=
| EvalAssign     : forall  vs v e,
     evalCmd vs (Assign v e) ( (set vs v (evalExp vs e)))
| EvalSeq        : forall vs1 vs2 vs3 c1 c2,
    evalCmd vs1 c1 vs2 /\ evalCmd vs2 c2 vs3
    -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs e c,
     evalExp vs e = 0
    -> evalCmd vs (While e c) vs
| EvalWhileTrue  : forall vs1' vs2' vs3'  e c,
     evalExp vs1' e <> 0
    /\ evalCmd vs1' c vs2' /\ evalCmd vs2' (While e c) vs3'
    -> evalCmd vs1' (While e c) vs3'.
    
MetaRocq Run (animate_coinductive_with_fn_pos <? evalCmd ?>
  [("evalCmd", ([0;1], [2]))] 500).



Definition prog  := While (Var 4) (Assign 8 (Const 8)).
Definition initFn : nat -> nat := fun m : nat => m + 1.
Print evalCmdAnimatedTopFnProp.
Eval cbv -[HoleyResult.hlist_head evalCmdremoveFnPosAn2Symb_unwrap] in
  (evalCmdTransparentSigma2AnimatedTopFn 35 (Success ((nat -> nat) * cmd) (initFn, prog))).
 



Definition prog''   :=
  While (Var 4) (Seq (Assign 4 (Var 3)) (Seq (Assign 3 (Var 2))
    (Seq (Assign 2 (Var 1)) (Assign 1 (Var 0))))).
Definition initFn'' : nat -> nat := fun m : nat => m.

Eval cbv -[HoleyResult.hlist_head evalCmdremoveFnPosAn2Symb_unwrap] in
  (evalCmdTransparentSigma2AnimatedTopFn 35 (Success ((nat -> nat) * cmd) (initFn'', prog''))).

End ImpSem.

(** ** Simple coinductive stream zip relation *)
Module zip.

CoInductive stream : Type :=
| nil : stream
| Seq : nat -> stream -> stream.

CoFixpoint from (n : nat) : stream := Seq n (from (S n)).

CoInductive zipSt : stream -> stream -> stream -> Prop :=
| zip : forall n m s1 s2 s3 s4 s5 s6,
    s1 = Seq n s2 /\ s3 = Seq m s4 /\ zipSt s2 s4 s5 /\ s6 = Seq n (Seq m s5)
    -> zipSt s1 s3 s6.

MetaRocq Run (animate_coinductive_with_fn_pos <? zipSt ?>
  [("zipSt", ([0;1], [2]))] 100).

(* The output should have named wrapper holes (zipStAn..Symb) instead of raw holes. *)
Eval cbv -[HoleyResult.hlist_head HoleyResult.hlist_tail] in
  (zipStTransparentSigma2AnimatedTopFn 6 (Success (stream * stream) (from 7, from 9))).
  


Print zipStAnimatedTopFnProp.

Check zipStremoveFnPosAn2Symb_unwrap.

End zip.

(* ------------------------------------------------------------------ *)
(** ** Filter even elements — coinductive output, inductive input *)
Module isEven.

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

MetaRocq Run (animate_coinductive_with_fn_pos <? filterEven ?>
  [("filterEven", ([0], [1]))] 100).

Eval cbv -[HoleyResult.hlist_head] in
  (filterEvenTransparentSigma2AnimatedTopFn 20 (Success stream (from 0))).

(* The combined property covering all holes: An-hole equations + coIndPush equations. *)
Print filterEvenAnimatedTopFnProp.

End isEven.




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

MetaRocq Run (animate_coinductive_with_fn_pos <?bigStepTr?>
               [("bigStepTr", ([0],  [1])); ("step", ([0],  [1]))
                ]
               100).
               
Definition omega : tm :=
  tapp (tabs "x" TBool (tapp (tvar "x") (tvar "x")))
       (tabs "x" TBool (tapp (tvar "x") (tvar "x"))).
Eval cbv -[HoleyResult.hlist_head bigStepTrremoveFnPosAn1Symb_unwrap] in bigStepTrTransparentSigma2AnimatedTopFn 25 (Success tm omega).
Print bigStepTrAnimatedTopFnProp.  
Check (tapp (tabs "x" TBool (tapp (tvar "x") (tvar "x")))
                          (tabs "x" TBool (tapp (tvar "x") (tvar "x")))).
      

End STLCStepTr.




Module integrateStreams.
(** A stream of naturals, with explicit undefined and nil sentinels. *)
CoInductive stream : Type :=
| nil : stream
| Seq : nat -> stream -> stream.




CoFixpoint from (n : nat) : stream := Seq n (from (S n)).

Definition myAdd (n1 n2: nat) := n1 + n2.

(* ------------------------------------------------------------------ *)
(** ** Integrate *)

CoInductive Integrate : stream -> stream -> Prop :=
| integNil : Integrate nil nil
| integ : forall s2 s3 n s5, Integrate s2 s3 /\ addStm n s3 s5 -> Integrate (Seq n s2) (Seq n s5)

with addStm : nat -> stream -> stream -> Prop :=
| addStmNil : forall m, addStm m nil nil
| plusm : forall m s1 n s2, addStm m s1 s2 -> addStm m (Seq n s1) (Seq (myAdd m n) s2).


MetaRocq Run (animate_coinductive_with_fn_pos <? Integrate ?>
  [("Integrate", ([0], [1])); ("addStm", ([0;1], [2]))] 100).

(** Integrate [4, 5, 6, …] gives [4, 9, 15, …] (prefix sums). *)
Eval cbv -[HoleyResult.hlist_head HoleyResult.hlist_tail IntegrateremoveFnPosAn1Symb_unwrap addStmremoveFnPosAn2Symb_unwrap] in (IntegrateTransparentSigma2AnimatedTopFn 5 (Success stream (from 4))).
Print IntegrateAnimatedTopFnProp.
Compute (IntegrateTransparentSigma2AnimatedTopFn 25 (Success stream (Seq 4 (Seq 3 (Seq 2 nil))))).
End integrateStreams.  






