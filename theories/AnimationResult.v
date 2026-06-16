(** * AnimationResult — The [animation_result] Type and Its Combinators

    Defines the core result type for animated functions together with the
    combinators that compose, project, and compare such results.

    All other animation modules that produce or consume [animation_result]
    values depend on this file. *)

Require Import MetaRocq.Template.All.
From Stdlib Require Import List.

Open Scope bs.

(** Result type for animated functions: success with a value,
    fuel exhaustion, or no matching clause. *)
Inductive animation_result (A : Type) : Type :=
| FuelError : animation_result A
| Success : A -> animation_result A
| NoMatch : animation_result A.

(** Wrapper type that marks a value as coming from an inductive definition.
    Used to distinguish inductive values in animation result types. *)
Inductive ind_tp (A : Type) : Type :=
| indWrap : A -> ind_tp A.

(** Kleisli composition for animated functions: run [f] on the input, then feed
    its [Success] result into [f'], propagating [FuelError] and [NoMatch]. *)
Definition compose_outcome
  (A B C : Type)
  (f : nat -> animation_result A -> animation_result B)
  (f' : nat -> animation_result B -> animation_result C)
  : nat -> animation_result A -> animation_result C :=
  fun fuel input =>
    match f fuel input with
    | Success res => f' fuel (Success B res)
    | FuelError => FuelError C
    | _ => NoMatch C
    end.

(** Constant function that always returns fuel error.
    Used as a fallback when fuel is exhausted. *)
Definition fuel_error_fn (in_tp : Type)
  (out_tp' : Type)
  : in_tp -> animation_result out_tp' :=
  fun x : in_tp => FuelError out_tp'.

(** Adapt a function returning [animation_result (option B)] into one returning
    [animation_result B]: [Some v] becomes [Success v], [None] becomes [NoMatch]. *)
Definition option_to_result (A B : Type)
  (f : nat -> animation_result A ->
       animation_result (option B))
  : nat -> animation_result A -> animation_result B :=
  fun k k' =>
    match f k k' with
    | Success (Some res) => Success B res
    | Success None => NoMatch B
    | FuelError => FuelError B
    | _ => NoMatch B
    end.

(** Identity function on [animation_result]: used as the single-element join. *)
Definition join_unit (A: Type) (x : animation_result A) : animation_result A :=
x.

(** Applicative product of two animation results: succeeds with a pair iff both
    succeed; propagates [FuelError] over [NoMatch]. *)
Definition join_pair (A B : Type)
  (x : animation_result A) (y : animation_result B)
  : animation_result (prod A B) :=
  match x with
  | NoMatch => NoMatch (prod A B)
  | FuelError => FuelError (prod A B)
  | Success k => match y with
                        | NoMatch => NoMatch (prod A B)
                        | FuelError => FuelError (prod A B)
                        | Success j => Success (prod A B) (k,j)
                        end
  end.

(** Compare two [animation_result] values with [eqfn]: returns [Success true] if
    both succeed and are equal, [NoMatch] if unequal or one is [NoMatch],
    [FuelError] if either is a fuel error. *)
Definition eq_outcome (A : Type)
  (eqfn : A -> A -> bool)
  (x y : animation_result A)
  : animation_result bool :=
  match x with
  | Success j => match y with
                    | Success k => if eqfn j k then Success bool true else NoMatch bool
                    | NoMatch => NoMatch bool
                    | FuelError => FuelError bool
                   end
  | FuelError => FuelError bool
  | NoMatch =>  match y with
                    | FuelError => FuelError bool
                    | _ => NoMatch bool
                   end
  end.

(** Short-circuit conjunction of two boolean animation results: [Success true]
    only if both succeed with [true]; [FuelError] takes priority over [NoMatch]. *)
Definition and_outcome_bool
  (x y : animation_result bool)
  : animation_result bool :=
  match x with
  | FuelError  => FuelError bool
  | NoMatch => match y with
                   | FuelError => FuelError bool
                   | _ => NoMatch bool
                  end
  | Success true => match y with
                        | Success true => Success bool true
                        | Success false => NoMatch bool
                        | NoMatch => NoMatch bool
                        | FuelError => FuelError bool
                       end
  | Success false => match y with
                         | FuelError => FuelError bool
                         | _ => NoMatch bool
                        end
  end.

(** Project the first component of a paired [animation_result]: discards the second
    component on [Success], preserves [FuelError] and [NoMatch]. *)
Definition split_outcome_fst (A B : Type)
  (x : animation_result (A * B))
  : animation_result A :=
  match x with
  | Success (a,b) => Success A a
  | NoMatch => NoMatch A
  | FuelError => FuelError A
  end.

(** Project the second component of a paired [animation_result]: discards the first
    component on [Success], preserves [FuelError] and [NoMatch]. *)
Definition split_outcome_snd (A B : Type)
  (x : animation_result (A * B))
  : animation_result B :=
  match x with
  | Success (a,b) => Success B b
  | NoMatch => NoMatch B
  | FuelError => FuelError B
  end.
