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
Require Import Animation.coIndPreProcSigma.
From Stdlib Require Import List.
From Stdlib Require Import Streams.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.
Import MetaRocqNotations.
Local Open Scope nat_scope.
Open Scope bs.

(* ------------------------------------------------------------------ *)
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

MetaRocq Run (animate_coinductive_transparent_sigma <? zipSt ?>
  [("zipSt", ([0;1], [2]))] 100).

(* The output should have named wrapper holes (zipStAn..Symb) instead of raw holes. *)
Eval cbv -[HoleyResult.hlist_head HoleyResult.hlist_tail streamcoIndPushSymb_unwrap] in
  (zipStTransparentSigmaAnimatedTopFn 6 (Success (stream * stream) (from 7, from 9))).
  
Print  streamcoIndPushSymb.  

Print zipStAnimatedTopFnProp.

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

MetaRocq Run (animate_coinductive_transparent_sigma <? filterEven ?>
  [("filterEven", ([0], [1]))] 100).

Eval cbv -[HoleyResult.hlist_head] in
  (filterEvenTransparentSigmaAnimatedTopFn 20 (Success stream (from 0))).

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
    
MetaRocq Run (animate_coinductive_transparent_sigma <?bigStepTr?>
               [("bigStepTr", ([0],  [1])); ("step", ([0],  [1]))
                ]
               100).

End STLCStepTr.
