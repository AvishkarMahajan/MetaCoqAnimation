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


Module STLC.
Open Scope bs.
Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Fixpoint decEqTerm : forall (t1 t2 : tm), {t1 = t2} + {t1 <> t2}.
Proof.

  decide equality. decide equality. decide equality. decide equality. decide equality. decide equality.
Defined.

Fixpoint decEqTy : forall (t1 t2 : ty), {t1 = t2} + {t1 <> t2}.
Proof.

  decide equality. Defined.
(*
Definition eqFntype (t1 t2 : type) : bool. Admitted.
(*
 :=
  if decEqType t1 t2 then true else false.
*)
*)  
Definition eqFntm (t1 t2 : tm) : bool :=

  if decEqTerm t1 t2 then true else false.

Definition eqFnty (t1 t2 : ty) : bool :=

  if decEqTy t1 t2 then true else false.  
    
Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.
Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.
Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.
Notation "<{{ x }}>" := x (x custom stlc_ty).
Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) : stlc_scope.
Notation "$( t )" := t (in custom stlc_ty at level 0, t constr) : stlc_scope.
Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0) : stlc_scope.
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc_tm at level 200,
                    x custom stlc_tm,
                    y custom stlc_tm,
                    z custom stlc_tm at level 200,
                    left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true (in custom stlc_tm at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom stlc_tm at level 0).
Check <{{ Bool }}>.
Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.
Notation "x y" := (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.

Definition testTm : tm :=
tm_app (tm_app (tm_abs "x" (Ty_Arrow Ty_Bool Ty_Bool) (tm_var "x"))
         (tm_abs "x" Ty_Bool (tm_if (tm_var "x")  tm_false tm_true)))
         tm_true.

(*
Arguments tm_var _%_string.
*)
(*
Notation idB :=
  <{ \ x: Bool, x }>.
Notation idBB :=
  <{ \x:Bool→Bool, x }>.
Notation idBBBB :=
  <{ \x: (Bool→Bool)→(Bool→Bool), x}>.
Notation k := <{ \x:Bool, \y:Bool, x }>.
Notation notB := <{ \x:Bool, if x then false else true }>.
*)
(*Original in SF 

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.
Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 [x:=s] t2}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if [x:=s] t1 then [x:=s] t2 else [x:=s] t3}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).
     
Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t v,
         value v ->
         <{(\x:T, t) v}> --> <{ [x:=v]t }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 /\
         t2 --> t2' ->
         <{v1 t2}> --> <{v1 t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').
*)
(*
Hint Constructors step : core.



Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
*)




(*

Inductive value : tm -> bool -> Prop :=
  | v_abs : forall x T2 t1 w b,
      w = <{\x:T2, t1}> /\ b = true -> value w b
  | v_true : forall w b,
      w = <{true}> /\ b = true -> value w b
  | v_false : forall w b,
      w = <{false}> /\ b = true -> value w b.
Hint Constructors value : core.
*)
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 [x:=s] t2}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if [x:=s] t1 then [x:=s] t2 else [x:=s] t3}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).
     
Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall z T t w b t1 t2, b = true /\ 
         value w b /\ t1 = <{(\z:T, t) w}> /\ t2 = <{ [z:=w]t }> ->
        t1 --> t2
  | ST_App1 : forall t1 t1' t2 t3 t4,
         t1 --> t1' /\ t3 = <{t1 t2}> /\ t4 = <{t1' t2}> ->
         t3 --> t4
  | ST_App2 : forall w t2 t2' b t3 t4,
         value w b /\ b=true /\
         t2 --> t2' /\ t3 =  <{w t2}> /\ t4 = <{w t2'}> ->
         t3 --> t4
  | ST_IfTrue : forall t1 t2 t3,
      t3 = <{if true then t1 else t2}> -> t3 --> t1
  | ST_IfFalse : forall t1 t2 t3,
      t3 = <{if false then t1 else t2}> -> t3 --> t2
  | ST_If : forall t1 t1' t2 t3 t4 t5,
      t1 --> t1' /\
      t4 = <{if t1 then t2 else t3}> /\ t5 = <{if t1' then t2 else t3}> -> t4 -->  t5
with value : tm -> bool -> Prop :=
  | v_abs : forall z T2 t1 w b,
      w = <{\z:T2, t1}> /\ b = true -> value w b
  | v_true : forall w b,
      w = <{true}> /\ b = true -> value w b
  | v_false : forall w b,
      w = <{false}> /\ b = true -> value w b      

where "t '-->' t'" := (step t t').




MetaRocq Run (animAllCl step <? step ?> [("step", ([0], [1]));("value", ([0], [1]))] 100).

Compute (stepAnimatedTopFn 20 (stepAnimatedTopFn 20 (stepAnimatedTopFn 20 (successPoly tm testTm)))).

Print testTm.


Definition testTm' : tm :=
tm_app (tm_abs "x" (Ty_Arrow Ty_Bool Ty_Bool) (tm_var "x")) (tm_app (tm_abs "x" (Ty_Arrow Ty_Bool Ty_Bool) (tm_var "x")) (tm_abs "x" (Ty_Bool) (tm_var "x"))).

Compute ((stepAnimatedTopFn 20 (stepAnimatedTopFn 20 (successPoly tm testTm')))).



