(** * AnimationDispatch — Unified Conjunction Dispatcher

    Integrates equality resolution and pattern-match compilation into a
    single dispatch layer.  Given a list of conjuncts from a constructor
    clause, this module separates them into let-binding equalities, guard
    predicates, and recursive calls, then animates each piece and
    assembles the final executable term via [animate_lets_and_guards].

    Depends on: [MetaRocqUtils], [PatternCompilation], [EqualityResolution]. *)

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

(** The polymorphic identity function, used as a placeholder in generated terms. *)
Definition id_fn (A : Type) (x : A) := x.

(** Animate any conjunction, handling both variable equalities and pattern matches.
    Dispatches to appropriate animation strategy based on conjunction structure. *)
Definition animate_let_binding {A : Type}
  (ind : A) (kn : kername)
  (conjunct' : tagged_conjunct)
  (inputTm : term) (inputTp : term)
  (inputVars : list string)
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  (allVarTpInf : list (string * term))
  (fuel : nat) : TemplateMonad term :=

outputTm <- tmEval all (tVar conjunct'.(tc_out_var)) ;;
outputTp <- tmEval all (conjunct'.(tc_out_type)) ;;
let conjunct := conjunct'.(tc_conjunct) in

match conjunct with
 | tApp <%eq%> [typeVar; t1; t2] => match t1 with
                                    | tVar str =>  match inputVars with
                                                    | [] => tmReturn (tApp <%Success%> [typeVar;t2])
                                                    | h :: rest =>
                                                      compile_let_clause ind kn conjunct
                                                        inputTm inputTp outputTm
                                                        outputTp inputVars fuel
                                                   end
                                    | tApp (tConstruct ind_type k lst) lstArgs =>
                                      compile_eq_binders_with_vars ind kn
                                        conjunct inputTm inputTp
                                        outputTm outputTp inputVars fuel
                                    | _ => tmFail "incorrect Conj shape"
                                    end

 | _ => match get_ind_name conjunct with
        | Some (indNm, _lstArgs) =>
            match fst (lookup_mode indNm modes) with
            | [] => animate_no_input ind kn conjunct' modes predTypeInf allVarTpInf fuel
            | _ => compile_clause ind kn conjunct' modes predTypeInf allVarTpInf fuel
            end
        | None => tmFail "incorrect Conj shape"
        end
end.

(** Wrap an animation function call in a [tLetIn] that binds the output variable,
    extending [partialLetfn].  Handles three cases: no inputs (direct value),
    a single input (apply with fuel + input), or multiple inputs (join first). *)
Definition build_let_chain_step
  (outputVarNm : string) (outputVarTp : term)
  (inputVarsLst : list (prod term term))
  (animationFn : term)
  (partialLetfn : term -> term) : (term -> term) :=
  match inputVarsLst with
  | [] =>
    (fun t => partialLetfn
      ((tLetIn
        {| binder_name := nNamed outputVarNm;
           binder_relevance := Relevant |}
        (animationFn)
        (tApp <%animation_result%> [outputVarTp]))
        t))
  | [h] =>
    (fun t => partialLetfn
      ((tLetIn
        {| binder_name := nNamed outputVarNm;
           binder_relevance := Relevant |}
        (tApp animationFn [(tVar "fuel"); fst h])
        (tApp <%animation_result%> [outputVarTp]))
        t))
  | _ =>
    (fun t => partialLetfn
      ((tLetIn
        {| binder_name := nNamed outputVarNm;
           binder_relevance := Relevant |}
        (tApp animationFn
          [(tVar "fuel");
           (tApp (mk_join_tm (map snd inputVarsLst))
              (map fst inputVarsLst))])
        (tApp <%animation_result%> [outputVarTp]))
        t))
  end.

(** Animate one conjunction as a let-binding step: compile [conjunct'] into
    a function and wrap it in a let that extends [partialLetfn]. *)
Definition animate_one_let {A : Type}
  (ind : A) (kn : kername)
  (conjunct' : tagged_conjunct)
  (inputVarsLst : list (prod string term))
  (partialLetfn : term -> term)
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  (allVarTpInf : list (string * term))
  (fuel : nat) : TemplateMonad (term -> term) :=
let inputTm := tele_to_prod_tm inputVarsLst in
let inputTp := tele_to_prod_tp inputVarsLst in
let inputVarsLstTm := pairs_to_terms inputVarsLst in
outputVarNm <- tmEval all (conjunct'.(tc_out_var)) ;;
outputVarTp <- tmEval all (conjunct'.(tc_out_type)) ;;
animationFn <- animate_let_binding (ind) (kn) (conjunct')
  (inputTm) (inputTp) (map fst inputVarsLst)
  (modes) (predTypeInf) (allVarTpInf) fuel ;;
tmReturn (build_let_chain_step (outputVarNm) (outputVarTp)
  (inputVarsLstTm) (animationFn) (partialLetfn)).

(** Animate one conjunction as a boolean predicate guard: compile [conjunct'] and
    produce a [and_outcome_bool] expression that extends [partialGuard]. *)
Definition animate_one_guard {A : Type}
  (ind : A) (kn : kername)
  (conjunct' : tagged_conjunct)
  (inputVarsLst : list (prod string term))
  (partialGuard : term)
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  (allVarTpInf : list (string * term))
  (fuel : nat) : TemplateMonad term :=
let inputTm := tele_to_prod_tm inputVarsLst in
let inputTp := tele_to_prod_tp inputVarsLst in
let inputVarsLstTm := pairs_to_terms inputVarsLst in
inputTm' <- tmEval all inputTm;;
inputTp' <- tmEval all inputTp;;
outputVarNm <- tmEval all (conjunct'.(tc_out_var)) ;;
outputVarTp <- tmEval all (conjunct'.(tc_out_type)) ;;

animationFn <- animate_let_binding (ind) (kn) (conjunct') (inputTm) (inputTp)
                                 (map fst inputVarsLst) (modes) (predTypeInf) (allVarTpInf) fuel ;;

tmReturn (tApp <%and_outcome_bool%>
  [partialGuard ;
   tApp (mk_eq_outcome_tm outputVarTp
     (type_to_eq_fn outputVarTp))
     [tVar outputVarNm ;
      (tApp animationFn
        [(tVar "fuel");
         (tApp (mk_join_tm (map snd inputVarsLst))
            (map fst inputVarsLstTm))])] ]).

(** Extract input or output variables from a conjunct using [eqProj] for
    equalities and [modeProj] for inductive predicate applications. *)
Definition conj_vars_by_role
  (eqProj : term -> term -> list string)
  (modeProj : (list nat * list nat) ->
    list term -> list term)
  (conjunct' : tagged_conjunct)
  (allVarTpInf : list (prod string term))
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  : list (prod string term) :=
let conjunct := conjunct'.(tc_conjunct) in
  match conjunct with
  | tApp <%eq%> [typeVar; t1; t2] => lookup_vars (eqProj t1 t2) allVarTpInf
  | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs =>
     let mode := lookup_mode indNm modes in
     lookup_vars (ordered_vars_of_list (modeProj mode lstArgs)) allVarTpInf
  | tApp (tVar indNm) lstArgs =>
     let mode := lookup_mode indNm modes in
     lookup_vars (ordered_vars_of_list (modeProj mode lstArgs)) allVarTpInf
  | _ => []
  end.

(** Get the input variable list for a conjunct: RHS variables of equalities,
    or in-mode arguments of inductive predicate applications. *)
Definition conj_input_vars :=
  conj_vars_by_role
    (fun _t1 t2 => ordered_vars t2)
    (fun mode lstArgs =>
      select_in_by_mode mode lstArgs).

(** Animate one let-clause by first computing its input variable list from
    context, then delegating to [animate_one_let]. *)
Definition animate_let_with_ctx {A : Type}
  (ind : A) (kn : kername)
  (conjunct' : tagged_conjunct)
  (partialLetfn : term -> term)
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  (allVarTpInf : list (string * term))
  (fuel : nat) : TemplateMonad (term -> term) :=
let  inputVarsLst := conj_input_vars conjunct' allVarTpInf (modes) (predTypeInf) in
animate_one_let ind kn conjunct' inputVarsLst partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel.

(** Animate one guard-predicate clause by first computing its input variable
    list from context, then delegating to [animate_one_guard]. *)
Definition animate_guard_with_ctx {A : Type}
  (ind : A) (kn : kername)
  (conjunct' : tagged_conjunct)
  (partialGuard : term)
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  (allVarTpInf : list (string * term))
  (fuel : nat) : TemplateMonad (term) :=

let  inputVarsLst := conj_input_vars conjunct' allVarTpInf (modes) (predTypeInf) in
animate_one_guard ind kn conjunct' inputVarsLst
  partialGuard (modes) (predTypeInf) (allVarTpInf) fuel.

(** Animate a list of let-binding conjuncts left-to-right, threading the
    accumulated let-binding function [partialLetfn] through each step. *)
Fixpoint animate_let_list {A : Type}
  (ind : A) (kn : kername)
  (conjs : list tagged_conjunct)
  (partialLetfn : term -> term)
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  (allVarTpInf : list (string * term))
  (fuel : nat) : TemplateMonad (term -> term) :=
  match conjs with
  | [] => tmReturn partialLetfn
  | h :: t =>
    lFn' <- animate_let_with_ctx ind kn h
      partialLetfn (modes) (predTypeInf)
      (allVarTpInf) fuel ;;
    animate_let_list ind kn t lFn'
      (modes) (predTypeInf) (allVarTpInf) fuel
  end.

(** Animate a list of predicate guard conjuncts, threading the accumulated
    boolean guard [partialGuard] through each step. *)
Fixpoint animate_guard_list {A : Type}
  (ind : A) (kn : kername)
  (conjs : list tagged_conjunct)
  (partialGuard : term)
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  (allVarTpInf : list (string * term))
  (fuel : nat) : TemplateMonad (term) :=
  match conjs with
  | [] => tmReturn partialGuard
  | h :: t =>
    pg <- animate_guard_with_ctx ind kn h
      partialGuard (modes) (predTypeInf)
      (allVarTpInf) fuel ;;
    animate_guard_list ind kn t pg
      (modes) (predTypeInf) (allVarTpInf) fuel
  end.

(** Combine a list of equality conjuncts into a single boolean guard expression
    by folding [animate_conj_guard] right-to-left, starting from [true]. *)
Fixpoint build_eq_guard_chain (conj : list term) : term :=
  match conj with
  | [] => <% true %>
  | h :: t =>
    match build_eq_guard_chain t with
    | gt => animate_conj_guard h gt
    end
  end.

(** Compile a guard-equality clause into an executable function: build a boolean
    guard from [gConjsEq] via [build_eq_guard_chain], wrap it in a
    [build_guarded_body] body, and generate a pattern-matching function. *)
Definition compile_guard_clause {A : Type}
  (induct : A) (kn : kername)
  (gConjsEq : list term)
  (inputTm : term) (inputTp : term)
  (outputTm : term) (outputTp : term)
  (fuel : nat) : TemplateMonad term :=

  (let postOut' := (build_guarded_body outputTm outputTp

    (build_eq_guard_chain (gConjsEq) )) in

    let postOutType' := tApp <% @option %> [outputTp] in

    let postInType' := inputTp in

    let postIn' := inputTm in

    let postIn := tApp <%Success%> [postInType'; postIn'] in
    let postInType := tApp <%animation_result%> [postInType'] in

    let postOut := tApp <%Success%> [postOutType'; postOut'] in
    let postOutType := tApp <%animation_result%> [postOutType'] in

     t0 <- compile_equality_clause induct postIn' postInType' postOut' postOutType'  fuel ;;

     let t1 := (tApp <%option_to_result%> [postInType'; outputTp; t0]) in
     t' <- tmEval all (typeConstrPatMatch.unwrap_option (DB.de_bruijn_option t1)) ;;
     tmReturn t').

(** Lift [compile_guard_clause] to work directly with variable
    type lists by computing the product input/output types from [allVarTpInf] and [outVars]. *)
Definition animate_guard_eq {A : Type}
  (induct : A) (kn : kername)
  (gConjsEq : list term)
  (allVarTpInf : list (prod string term))
  (outVars : list (prod string term))
  (fuel : nat) : TemplateMonad term :=
compile_guard_clause induct kn gConjsEq
  (tele_to_prod_tm allVarTpInf)
  (tele_to_prod_tp allVarTpInf)
  (tele_to_prod_tm outVars)
  (tele_to_prod_tp outVars) fuel.

(** Build a term that pattern-matches an [animation_result bool] guard and
    dispatches to one of four continuations: [succTrueRetTm] (guard true),
    [succFalseRetTm] (guard false), [noMatchRetTm], or [fuelErrorRetTm]. *)
Definition branch_on_bool
  (retType succTrueRetTm succFalseRetTm
   noMatchRetTm fuelErrorRetTm : term) : term :=
let splitSuccBinder := {| binder_name := nNamed "splitSuccCase"; binder_relevance := Relevant |} in
let gcPredBinder := {| binder_name := nNamed "gcPred"; binder_relevance := Relevant |} in
let boolCase :=
  tCase
    {| ci_ind := {| inductive_mind := <?bool?>; inductive_ind := 0 |};
       ci_npar := 0; ci_relevance := Relevant |}
    {| puinst := []; pparams := [];
       pcontext := [splitSuccBinder]; preturn := retType |}
    (tVar "splitSuccCase")
    [{| bcontext := []; bbody := succTrueRetTm |};
     {| bcontext := []; bbody := succFalseRetTm |}] in
tLam "gcPred" (tApp <%animation_result%> [<%bool%>])
  (tCase
    {| ci_ind := {| inductive_mind := (MPfile ["MetaRocqUtils"; "Animation"], "animation_result");
                     inductive_ind := 0 |};
       ci_npar := 1; ci_relevance := Relevant |}
    {| puinst := []; pparams := [<%bool%>];
       pcontext := [gcPredBinder]; preturn := retType |}
    (tVar "gcPred")
    [{| bcontext := []; bbody := fuelErrorRetTm |};
     {| bcontext := [splitSuccBinder]; bbody := boolCase |};
     {| bcontext := []; bbody := noMatchRetTm |}]).

(** Animate predicate guard conjuncts and branch on their boolean result:
    passes [guardConEqAn] (the equality guard) as the [true] branch and
    [NoMatch] as the [false] branch. *)
Definition animate_guard_bool_branch {A : Type}
  (ind : A) (kn : kername)
  (predGuardConjs : list tagged_conjunct)
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  (allVarTpInf : list (string * term))
  (outVars : list (prod string term))
  (guardConEqAn : term)
  (fuel : nat) : TemplateMonad (term) :=
predGuardCon <- animate_guard_list (ind) (kn)
  (predGuardConjs) <%Success bool true%>
  (modes) (predTypeInf) (allVarTpInf) (fuel) ;;
let brOutBool :=
  branch_on_bool
    (tApp <%animation_result%>
      [tele_to_prod_tp outVars])
    (guardConEqAn)
    (tApp <%NoMatch%> [tele_to_prod_tp outVars])
    (tApp <%NoMatch%> [tele_to_prod_tp outVars])
    (tApp <%FuelError%>
      [tele_to_prod_tp outVars]) in
tmReturn (tApp brOutBool [predGuardCon]).

(** Insert [tLetIn] bindings that split a product [inTerm] into individual
    variable names according to [inVars], using [split_outcome_fst]/[Snd]. *)
Fixpoint split_inputs (inVars : list (string * term)) (inTerm : term) (fnBody : term) : term :=
  match inVars with
  | [] => fnBody
  | [h] => (tLetIn {| binder_name := nNamed (fst h); binder_relevance := Relevant |}
                                 inTerm (tApp <%animation_result%> [(snd h)])) fnBody
  | h' :: rest' =>
    (tLetIn
      {| binder_name := nNamed (fst h');
         binder_relevance := Relevant |}
      (tApp <% split_outcome_fst %>
        [(snd h'); (tele_to_prod_tp rest');
         inTerm])
      (tApp <%animation_result%> [(snd h')]))
      (split_inputs rest'
        (tApp <% split_outcome_snd %>
          [(snd h'); (tele_to_prod_tp rest');
           inTerm])
        fnBody)
  end.
(** Convenience wrapper: split the [input] variable into [inVars] bindings,
    or leave [fnBody] unchanged if [inVars] is empty. *)
Definition split_inputs' (inVars : list (string * term)) (fnBody : term) : term :=
  match inVars with
  | [] => fnBody
  | _ => split_inputs inVars (tVar "input") fnBody
  end.

(** Assemble the full animated body of a constructor clause: animate the
    let-binding conjuncts [lConjs''], combine the equality guard [gConjsEq''] and
    predicate guards [gConjsPred''] into a single branching guard, and wrap
    everything in lambdas for the animated recursive functions and the input. *)
Definition animate_lets_and_guards {A : Type}
  (ind : A) (kn : kername)
  (lConjs'' : list tagged_conjunct)
  (gConjsEq'' : list term)
  (gConjsPred'' : list tagged_conjunct)
  (inVars : list (prod string term))
  (outVars : list (prod string term))
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  (allVarTpInf : list (string * term))
  (lhsPreds : list (string * term))
  (fuel : nat) : TemplateMonad term :=
lConjs <- tmEval all lConjs'';;
gConjsEq <- tmEval all gConjsEq'';;
gConjsPred <- tmEval all gConjsPred'';;
(* Animate let-binding conjuncts into a chain of let-in expressions *)
letBind <- animate_let_list (ind) kn lConjs
  (fun t : term => t) (modes) (predTypeInf)
  (allVarTpInf) (fuel) ;;
(* Animate equality guards into a boolean function *)
gFun <- animate_guard_eq ind kn gConjsEq allVarTpInf outVars fuel ;;
let guardConEqAn := (tApp gFun [tVar "fuel"; mk_output_prod_tm (allVarTpInf)]) in
(* Combine predicate guards with equality guard into a branching guard *)
combineGuard <- animate_guard_bool_branch (ind) (kn)
  (gConjsPred) (modes) (predTypeInf)
  (allVarTpInf) (outVars) (guardConEqAn) (fuel);;
  (* Wrap in lambdas for recursive function args, fuel, and input *)
  match inVars with
  | h :: rest =>
    tmReturn (mk_lam_chain
      (mk_animated_names lhsPreds ++ [("fuel", <%nat%>)])
      (tLam "input"
        (tApp <%animation_result%>
          [tele_to_prod_tp inVars])
        (split_inputs' inVars
          (letBind combineGuard))))
  | [] =>
    tmReturn (mk_lam_chain
      (mk_animated_names lhsPreds ++ [("fuel", <%nat%>)])
      (tLam "input"
        (tApp <%animation_result%> [<%bool%>])
        (split_inputs' inVars
          (letBind combineGuard))))

  end.

(** Keep only the equality ([eq]) conjuncts from a list, discarding predicates. *)
Fixpoint filter_conjs_eq (lst : list term) : list term :=
  match lst with
  | [] => []
  | (tApp <%eq%> [typeVar; t1; t2]) :: rest =>
    (tApp <%eq%> [typeVar; t1; t2])
      :: filter_conjs_eq rest

  | _h :: rest => filter_conjs_eq rest
  end.
(** Keep only inductive predicate application conjuncts from a list,
    discarding equalities and other forms. *)
Fixpoint filter_conjs_pred (lst : list term) : list term :=
  match lst with
  | [] => []
  | (tApp <%eq%> [typeVar; t1; t2]) :: rest =>  filter_conjs_pred rest

  | (tApp (tInd
      {| inductive_mind := (path, indNm);
         inductive_ind := 0 |} []) lstArgs)
      :: rest =>
    (tApp (tInd
      {| inductive_mind := (path, indNm);
         inductive_ind := 0 |} []) lstArgs)
      :: filter_conjs_pred rest

  | (tApp (tVar indNm) lstArgs) :: rest => (tApp (tVar indNm) lstArgs) :: filter_conjs_pred rest

  | _h :: rest => filter_conjs_pred rest
  end.

(** Check whether a term is a bare variable or a constructor application —
    shapes that can appear on the output side of a let-binding equation. *)
Definition has_right_shape (t : term) : bool :=
  match t with
  | tVar str => true
  | tApp (tConstruct ind_type k lst) lstArgs => true
  | _ => false
  end.

(** Build a product type from a list of (term * type) pairs; base case is [bool]. *)
Fixpoint mk_lhs_type_pure (lhsIndPre : list (term * term)) : term :=
  match lhsIndPre with
  | []      => <%bool%>
  | [h]     => snd h
  | h :: t  => tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; mk_lhs_type_pure t]
  end.

(** Build a product term from a list of (term * type) pairs; base case is [true]. *)
Fixpoint mk_lhs_term_pure (lhsIndPre : list (term * term)) : term :=
  match lhsIndPre with
  | []     => <%true%>
  | [h]    => fst h
  | h :: t => tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
                     [snd h; mk_lhs_type_pure t; fst h; mk_lhs_term_pure t]
  end.

(** Topologically sort and orient conjuncts by known variables [kv]:
    equalities where one side is fully known go to [sortedConjs] (let-bindings);
    equalities where both sides are known go to [guardConjs] (boolean guards);
    predicate applications ready to evaluate go to [sortedConjs];
    all others are deferred in [remConjs] for the next pass. *)
Fixpoint classify_premises
  (modes : mode_map)
  (currentConjs : list term)
  (remConjs : list term)
  (sortedConjs : list term)
  (guardConjs : list term)
  (kv : (list string))
  (fuel : nat)
  : TemplateMonad (prod (list term) (list term)) :=
  match fuel with
  | 0 =>
    if andb (is_nil remConjs) (is_nil currentConjs)
    then tmReturn (sortedConjs, guardConjs)
    else tmFail "insufficient fuel to sort conjs"
  | S n =>
    if (andb (is_nil remConjs) (is_nil currentConjs))
    then tmReturn (sortedConjs, guardConjs)
    else
           match currentConjs with
            | [] => classify_premises modes remConjs [] sortedConjs guardConjs kv n
            | conj' :: t =>
              match conj' with
              | tApp <%eq%> [typeVar; t1; t2] =>
                if andb
                  (is_subset_strings (ordered_vars t1) kv)
                  (is_subset_strings (ordered_vars t2) kv)
                then
                  classify_premises modes t remConjs
                    sortedConjs (conj' :: guardConjs)
                    kv n
                else
                (if (andb
                  (is_subset_strings (ordered_vars t1) kv)
                  (has_right_shape t2))
                then
                  classify_premises modes t remConjs
                    (tApp <%eq%>
                      [typeVar; t2; t1] :: sortedConjs)
                    (guardConjs)
                    (ordered_vars t2 ++ kv) n
                else
                (if (andb
                  (is_subset_strings (ordered_vars t2) kv)
                  (has_right_shape t1))
                then
                  classify_premises modes t remConjs
                    (tApp <%eq%>
                      [typeVar; t1; t2] :: sortedConjs)
                    (guardConjs)
                    (ordered_vars t1 ++ kv) n
                else
                (classify_premises modes t
                  (conj' :: remConjs) (sortedConjs)
                  (guardConjs) (kv) n)))
              | _ =>
                match get_ind_name conj' with
                | Some (indNm, lstArgs) =>
                  if is_subset_strings
                    (concat
                      (List.map ordered_vars lstArgs))
                    kv
                  then
                    classify_premises modes t remConjs
                      sortedConjs
                      (conj' :: guardConjs) kv n
                  else if is_subset_strings
                    (ordered_vars_of_list
                      (select_in_args indNm
                        modes lstArgs))
                    kv
                  then
                    classify_premises modes t remConjs
                      (conj' :: sortedConjs) guardConjs
                      (ordered_vars_of_list
                        (select_out_args indNm
                          modes lstArgs) ++ kv) n
                  else
                    classify_premises modes t
                      (conj' :: remConjs) sortedConjs
                      guardConjs kv n
                | None =>
                  tmFail "incorrect conj shape"
                end
              end
           end
  end.

(** Run [classify_premises] and extract one half of the result via [proj],
    optionally reversing (let-bindings are reversed to restore declaration order). *)
Definition get_classified
  (proj : list term * list term -> list term)
  (doReverse : bool)
  (modes : mode_map)
  (currentConjs : list term)
  (remConjs : list term)
  (sortedConjs : list term)
  (guardConjs : list term)
  (kv : (list string))
  (fuel : nat) : TemplateMonad (list term) :=
sConjs <- classify_premises modes (currentConjs)
  (remConjs) (sortedConjs) (guardConjs)
  (kv) (fuel) ;;
result <- tmEval all (if doReverse then rev (proj sConjs) else proj sConjs) ;;
tmReturn result.

(** Classify and extract the let-binding conjuncts (sorted, reversed to declaration order). *)
Definition get_sorted_lets := get_classified fst true.
(** Classify and extract the guard conjuncts (sorted, kept in natural order). *)
Definition get_sorted_guards := get_classified snd false.

(** Get all output variables introduced by a conjunct (LHS of an equality,
    or out-mode arguments of a predicate). *)
Definition conj_output_vars
  (conj : term)
  (allVarTpInf : list (prod string term))
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  : list (prod string term) :=
conj_vars_by_role
  (fun t1 _t2 => ordered_vars t1)
  (fun mode lstArgs =>
    select_out_by_mode mode lstArgs)
  {| tc_conjunct := conj; tc_out_var := ""%bs; tc_out_type := <%bool%> |}
  allVarTpInf modes predTypeInf.

(** Pair each conjunct in [lconjs] with the output variables it introduces. *)
Fixpoint attach_output_vars
  (lconjs : list term)
  (allVarTpInf : list (prod string term))
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  : (list (prod term (list (prod string term)))) :=
  match lconjs with
  | [] => []
  | h :: t =>
    (h, conj_output_vars h allVarTpInf
      modes predTypeInf)
      :: attach_output_vars t allVarTpInf
           modes predTypeInf
  end.

(** Tag a single conjunct term [lconjt] with each output variable in [lconjV],
    producing one [(conjunct, output_var)] pair per variable. *)
Fixpoint attach_var_to_conj (lconjt : term)
  (lconjV : (((list (string * term)))))
  : list tagged_conjunct :=
  match (lconjV) with
  | [] => []
  | (h :: rest) => {| tc_conjunct := lconjt; tc_out_var := fst h; tc_out_type := snd h |} :: attach_var_to_conj lconjt rest
  end.

(** Flatten a list of [(conjunct, output_vars)] pairs into a flat list of
    [(conjunct, output_var)] pairs by applying [attach_var_to_conj]. *)
Fixpoint attach_vars_to_conjs
  (lconjs : (list (prod term
    (list (prod string term)))))
  : list tagged_conjunct :=
  match lconjs with
  | [] => []
  | h :: rest => attach_var_to_conj (fst h) (snd h) ++ attach_vars_to_conjs rest
  end.
(** Convert a sorted conjunct list to a tagged [(conjunct, output_var)] list. *)
Definition attach_sorted_outputs
  (lconjs : list term)
  (allVarTpInf : list (prod string term))
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  : list tagged_conjunct :=
attach_vars_to_conjs (attach_output_vars lconjs allVarTpInf modes predTypeInf).

(** Remove conjuncts whose output variable already appears in [kv] (already defined),
    adding newly seen output variables to [kv] as they are encountered. *)
Fixpoint remove_dup_defs
  (lconjs : list tagged_conjunct)
  (kv : list string)
  : list tagged_conjunct :=
  match lconjs with
  | [] => []
  | h :: rest =>
    if (in_strings h.(tc_out_var) kv)
    then remove_dup_defs rest kv
    else h :: (remove_dup_defs rest
      (h.(tc_out_var) :: kv))
  end.

(** Keep only conjuncts whose output variable already appears in [kv] (duplicates),
    adding first occurrences to [kv] so subsequent duplicates are kept. *)
Fixpoint keep_dup_defs
  (lconjs : list tagged_conjunct)
  (kv : list string)
  : list tagged_conjunct :=
  match lconjs with
  | [] => []
  | h :: rest =>
    if (in_strings h.(tc_out_var) kv)
    then h :: (keep_dup_defs rest kv)
    else (keep_dup_defs rest
      (h.(tc_out_var) :: kv))
  end.

(** Keep only inductive predicate application entries from a tagged conjunct list,
    discarding equalities and other shapes. *)
Fixpoint filter_conjs_pred' (lst : list tagged_conjunct) : list tagged_conjunct :=
  match lst with
  | [] => []
  | h :: rest =>
    match h.(tc_conjunct) with
    | tApp <%eq%> [typeVar; t1; t2] => filter_conjs_pred' rest
    | tApp (tInd
        {| inductive_mind := (path, indNm);
           inductive_ind := 0 |} []) lstArgs =>
      h :: filter_conjs_pred' rest
    | tApp (tVar indNm) lstArgs =>
      h :: filter_conjs_pred' rest
    | _ => filter_conjs_pred' rest
    end
  end.
