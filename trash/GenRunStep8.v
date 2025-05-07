Require Import Coq.Lists.List.

Require Import MetaCoq.Template.All.
Import monad_utils.MCMonadNotation.

(* Name resolution *)
Notation "<? x ?>" :=
  (ltac:(let p y :=
            match y with
            | tInd {| inductive_mind := ?name |} _ =>
              exact name
            | tConst ?name _ =>
              exact name
            | _ => fail "not a type constructor or definition name" end in
        run_template_program (tmQuote x) p))
  (only parsing).

Open Scope bs.


Definition progTransIndRelPm6 (p : mutual_inductive_body) : option term :=
  match p with
  |{| ind_finite := inf
    ; ind_npars := n
    ; ind_params := ip
    ; ind_bodies :=
      {| ind_name := inn
        ; ind_indices := ii
        ; ind_sort := is
        ; ind_type := it
        ; ind_kelim := ik
        ; ind_ctors := {| cstr_name := cname
                        ; cstr_args := {| decl_name := dname
                                        ; decl_body := dbody
                                        ; decl_type := tApp te (a0 :: a1 :: tApp j1 j2 :: atail)
                                        |} :: bcarg
                        ; cstr_indices := ltm
                        ; cstr_type := ct
                        ; cstr_arity := j
                        |} :: bctors
        ; ind_projs := ipr
        ; ind_relevance := irl
        |} :: tb
    ; ind_universes := iu
    ; ind_variance := iv
    |}  => Some j1
  | _ => None
  end.


Parameter errorFun : nat -> nat.
MetaCoq Quote Definition errorFunTerm := errorFun.


Definition extractTerm (x : option term) : term :=
  match x with
  | Some t1 => t1
  | None => errorFunTerm
  end.

(** Definition unwrapOption (tm : option term) : option (nat -> nat):=
 match tm with
  | Some y =>  x <- tmUnquoteTyped (nat -> nat) y ;; Some x
  | None => None
 end. **)

Definition progTransIndRel6 (p : mutual_inductive_body) : term :=
  extractTerm (progTransIndRelPm6 p).




Inductive step : nat -> nat -> Prop :=
| decrement : forall x y, y = (fun a => a - 1) x -> step x y.

(** Check (option_map (tmUnquoteTyped (nat -> nat))). **)




Definition run_step_type' (f : nat -> nat) : Type :=
  forall e1 : nat, {o : nat | match o with
                              | e2 => ((step e1 e2 /\ o = f e1) \/ (f = errorFun))
                              end }.


Definition gen_run_step_sig
           (mut : mutual_inductive_body)
           : TemplateMonad (Type) :=
  f_out <- tmUnquoteTyped (nat -> nat) (progTransIndRel6 mut);;
  lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (run_step_type' f_out) ;;
  @tmReturn Type (run_step_type' (f_out)).




Definition animate (R_name : kername) : TemplateMonad unit :=
  mut <- tmQuoteInductive R_name ;;
  run_step_name <- tmFreshName "run_step" ;;
  f <- gen_run_step_sig mut ;;
  (** @tmDefinition run_step_name run_step_type f ;; **)
  tmDefinition run_step_name f ;;

  tmMsg "done".


 (** #[local] Obligation Tactic :=
  unfold run_step_branch_type;
  constructor. **)

MetaCoq Run (animate <? step ?>).

Next Obligation.
Proof. (** unfold run_step_type'. **) assert (H : forall n : nat, ((step n (n - 1) /\ (n - 1) = (n - 1)) \/ ((fun a : nat => a - 1) = errorFun)) ).
+ intro n. left. split.
++ apply decrement. reflexivity.
++ reflexivity.
+ exists (e1 -1). apply H. Qed.


Print run_step.

Compute run_step.



















(** Definition run_step_branch_type (e1 : nat) (o : nat) : Type :=
  match o with
  | e2 => step e1 e2

  end.

Definition run_step_branch_type' (f : nat -> nat) : Type :=
  forall n, (step n (f n)).



Definition run_step_type : Type :=
 forall e1 : nat,  {o : nat & (match o with
                                  | e2 => step e1 e2

                                 end) }.
Check (run_step_branch_type 0 0).
Check (fun n => run_step_branch_type n (n + 1)).

Parameter g : nat -> nat.

Check (fun n => run_step_branch_type n (g n)).

Print TemplateMonad. **)




(** Compute (run_step_type' 3 (fun a : nat => a - 1)).

Definition run_step_type'' : Type :=
forall (f : nat -> nat) (e1 : nat), {o : nat & (match o with
                                                  | e2 => (step e1 e2 /\ o = f e1)

                                                  end) }.
Compute (run_step_type' 3 (fun a : nat => a - 1)). **)
(** Definition gen_run_step'
           (mut : mutual_inductive_body)
           : TemplateMonad (nat -> Type) :=
  f_out <- tmUnquoteTyped (nat -> nat) (progTransIndRel6 mut);;
  @tmReturn (nat -> Type) (fun n => run_step_branch_type n (f_out n)). **)

(** Definition gen_run_step''
           (mut : mutual_inductive_body)
           : TemplateMonad (Type) :=
  f_out <- tmUnquoteTyped (nat -> nat) (progTransIndRel6 mut);;
  @tmReturn (Type) (forall n, exist _ ). **)


(** Definition gen_run_step_sig'
           (mut : mutual_inductive_body)
           : TemplateMonad (run_step_type'') :=
  f_out <- tmUnquoteTyped (nat -> nat) (progTransIndRel6 mut);;
  @tmReturn (run_step_type'') (run_step_type'' (f_out)). **)


(** Definition gen_run_step'
           (mut : mutual_inductive_body)
           : TemplateMonad (nat -> run_step_type) :=
  f_out <- tmUnquoteTyped (nat -> nat) (progTransIndRel6 mut);;
  @tmReturn (nat -> Type) (fun n => run_step_branch_type n (f_out n)). **)
