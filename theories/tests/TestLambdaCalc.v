(** * TestLambdaCalc: Untyped Lambda Calculus
    Tests animation of the untyped lambda calculus with de Bruijn indices.
    Small-step call-by-name (CBN) reduction via beta rule. *)

Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.
Require Import Animation.EqualityResolution.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.
From Stdlib Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.
Import MetaRocqNotations.
Local Open Scope nat_scope.
Open Scope bs.


(** ** Untyped Lambda Calculus with de Bruijn indices *)

Module UntypedCBN.

Inductive lam_tm : Type :=
| lvar : nat -> lam_tm
| lapp : lam_tm -> lam_tm -> lam_tm
| labs : lam_tm -> lam_tm.

Definition eqFnlam_tm (t1 t2 : lam_tm) : bool :=
  match t1, t2 with
  | labs _, labs _ => false
  | _, _ => false
  end.

Fixpoint lshift (d c : nat) (t : lam_tm) : lam_tm :=
  match t with
  | lvar n => if Nat.leb c n then lvar (n + d) else lvar n
  | lapp t1 t2 => lapp (lshift d c t1) (lshift d c t2)
  | labs t1 => labs (lshift d (S c) t1)
  end.

Fixpoint lsubst (n : nat) (s : lam_tm) (t : lam_tm) : lam_tm :=
  match t with
  | lvar m => if Nat.eqb m n then s else t
  | lapp t1 t2 => lapp (lsubst n s t1) (lsubst n s t2)
  | labs t1 => labs (lsubst (S n) (lshift 1 0 s) t1)
  end.

Inductive lam_step : lam_tm -> lam_tm -> Prop :=
| LS_Beta : forall (t1 t2 : lam_tm),
    lam_step (lapp (labs t1) t2) (lsubst 0 t2 t1)
| LS_App : forall (e1 e1' e2 : lam_tm),
    lam_step e1 e1' ->
    lam_step (lapp e1 e2) (lapp e1' e2).

MetaRocq Run (animate_inductive <?lam_step?> [("lam_step", ([0], [1]))] 200).

(* --- CBN reduction tests --- *)

(* Identity: (\. 0) x --> x *)
Example test_identity :
  lam_stepAnimatedTopFn 50
    (Success lam_tm (lapp (labs (lvar 0)) (lvar 42)))
  = Success lam_tm (lvar 42).
Proof. reflexivity. Qed.

(* Constant: (\. \. 1) x --> \. x  (with de Bruijn shift) *)
Example test_const :
  lam_stepAnimatedTopFn 50
    (Success lam_tm (lapp (labs (labs (lvar 1))) (lvar 42)))
  = Success lam_tm (labs (lvar 43)).
Proof. reflexivity. Qed.

(* Nested: CBN reduces outer redex first *)
Example test_nested :
  lam_stepAnimatedTopFn 50
    (Success lam_tm (lapp (lapp (labs (lvar 0)) (labs (lvar 0))) (lvar 7)))
  = Success lam_tm (lapp (labs (lvar 0)) (lvar 7)).
Proof. reflexivity. Qed.

(* Values cannot step *)
Example test_var_stuck :
  lam_stepAnimatedTopFn 50
    (Success lam_tm (lvar 0))
  = NoMatch lam_tm.
Proof. reflexivity. Qed.

Example test_lam_stuck :
  lam_stepAnimatedTopFn 50
    (Success lam_tm (labs (lvar 0)))
  = NoMatch lam_tm.
Proof. reflexivity. Qed.

Example test_app_vars_stuck :
  lam_stepAnimatedTopFn 50
    (Success lam_tm (lapp (lvar 0) (lvar 1)))
  = NoMatch lam_tm.
Proof. reflexivity. Qed.

End UntypedCBN.
