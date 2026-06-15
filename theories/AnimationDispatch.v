(** * AnimationDispatch — Unified Conjunction Dispatcher

    Integrates equality resolution and pattern-match compilation into a
    single dispatch layer.  Given a list of conjuncts from a constructor
    clause, this module separates them into let-binding equalities, guard
    predicates, and recursive calls, then animates each piece and
    assembles the final executable term via [animate_list_let_and_pred_guard].

    Depends on: [MetaRocqUtils], [PatternCompilation], [EqualityResolution]. *)

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

(** The polymorphic identity function, used as a placeholder in generated terms. *)
Definition id_fn (A : Type) (x : A) := x.

(** Animate any conjunction, handling both variable equalities and pattern matches.
    Dispatches to appropriate animation strategy based on conjunction structure. *)
Definition animate_any_let {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (inputTm : term) (inputTp : term)
                                 (inputVars : list string) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term))  (fuel : nat) : TemplateMonad term :=

outputTm <- tmEval all (tVar (fst (snd conjunct'))) ;;
outputTp <- tmEval all ((snd (snd conjunct'))) ;;
let conjunct := fst conjunct' in

match conjunct with
 | tApp <%eq%> [typeVar; t1; t2] => match t1 with
                                    | tVar str =>  match inputVars with
                                                    | [] => tmReturn (tApp <%Success%> [typeVar;t2])
                                                    | h :: rest => gen_fun_animate_eq_partial_let_clause' ind kn conjunct inputTm inputTp outputTm outputTp inputVars fuel
                                                   end
                                    | tApp (tConstruct ind_type k lst) lstArgs => extract_pat_mat_binders_partial' ind kn conjunct inputTm inputTp outputTm outputTp inputVars fuel
                                    | _ => tmFail "incorrect Conj shape"
                                    end

 | _ => match extract_ind_name conjunct with
        | Some (indNm, _lstArgs) =>
            match fst (get_mode_fm_lst indNm modes) with
            | [] => animate_predicate_empty_in ind kn conjunct' modes predTypeInf allVarTpInf fuel
            | _ => compile_relation_clause ind kn conjunct' modes predTypeInf allVarTpInf fuel
            end
        | None => tmFail "incorrect Conj shape"
        end
end.

(** Wrap an animation function call in a [tLetIn] that binds the output variable,
    extending [partialLetfn].  Handles three cases: no inputs (direct value),
    a single input (apply with fuel + input), or multiple inputs (join first). *)
Definition animate_one_conj_any_let' (outputVarNm : string) (outputVarTp : term) (inputVarsLst : list (prod term term)) (animationFn : term) (partialLetfn : term -> term) : (term -> term) :=
  match inputVarsLst with
  | [] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (animationFn) (tApp <%animation_result%> [outputVarTp]))  t) )
  | [h] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); fst h]) (tApp <%animation_result%> [outputVarTp])) t ))
  | _ =>  (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); (tApp (mk_join_outcome_tm (map snd inputVarsLst)) (map fst inputVarsLst))]) (tApp <%animation_result%> [outputVarTp])) t))
  end.

(** Animate one conjunction as a let-binding step: compile [conjunct'] into
    a function and wrap it in a let that extends [partialLetfn]. *)
Definition animate_one_conj_any_let {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (inputVarsLst : list (prod string term)) (partialLetfn : term -> term)
                                           (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
let inputTm := telescope_to_prod_term inputVarsLst in
let inputTp := telescope_to_prod_type inputVarsLst in
let inputVarsLstTm := mk_lst_tm inputVarsLst in
outputVarNm <- tmEval all ((fst (snd conjunct'))) ;;
outputVarTp <- tmEval all ((snd (snd conjunct'))) ;;
animationFn <-  animate_any_let (ind) (kn) (conjunct') (inputTm) (inputTp) (map fst inputVarsLst) (modes) (predTypeInf) (allVarTpInf) fuel ;;
tmReturn (animate_one_conj_any_let' (outputVarNm) (outputVarTp) (inputVarsLstTm) (animationFn) (partialLetfn)).

(** Animate one conjunction as a boolean predicate guard: compile [conjunct'] and
    produce a [comp_outcome_bool] expression that extends [partialGuard]. *)
Definition animate_one_conj_pred_guard {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (inputVarsLst : list (prod string term)) (partialGuard : term)
                                           (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad term :=
let inputTm := telescope_to_prod_term inputVarsLst in
let inputTp := telescope_to_prod_type inputVarsLst in
let inputVarsLstTm := mk_lst_tm inputVarsLst in
inputTm' <- tmEval all inputTm;;
inputTp' <- tmEval all inputTp;;
outputVarNm <- tmEval all ((fst (snd conjunct'))) ;;
outputVarTp <- tmEval all ((snd (snd conjunct'))) ;;

animationFn <- animate_any_let (ind) (kn) (conjunct') (inputTm) (inputTp)
                                 (map fst inputVarsLst) (modes) (predTypeInf) (allVarTpInf) fuel ;;

                                 tmReturn (tApp <%comp_outcome_bool%> [partialGuard ; tApp (type_to_bool_eq_outcome outputVarTp (type_to_bool_eq outputVarTp)) [tVar outputVarNm ;
                                 (
                                 (tApp animationFn [(tVar "fuel"); (tApp (mk_join_outcome_tm (map snd inputVarsLst)) (map fst inputVarsLstTm))])) ]]).

(** Extract input or output variables from a conjunct using [eqProj] for
    equalities and [modeProj] for inductive predicate applications. *)
Definition get_conj_vars_by_role (eqProj : term -> term -> list string) (modeProj : (list nat * list nat) -> list term -> list term) (conjunct' : (term * (string * term))) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (prod string term) :=
let conjunct := fst conjunct' in
  match conjunct with
  | tApp <%eq%> [typeVar; t1; t2] => look_up_vars (eqProj t1 t2) allVarTpInf
  | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs =>
     let mode := get_mode_fm_lst indNm modes in
     look_up_vars (extract_ordered_vars_fm_lst (modeProj mode lstArgs)) allVarTpInf
  | tApp (tVar indNm) lstArgs =>
     let mode := get_mode_fm_lst indNm modes in
     look_up_vars (extract_ordered_vars_fm_lst (modeProj mode lstArgs)) allVarTpInf
  | _ => []
  end.

(** Get the input variable list for a conjunct: RHS variables of equalities,
    or in-mode arguments of inductive predicate applications. *)
Definition get_conj_input_var_lst := get_conj_vars_by_role (fun _t1 t2 => extract_ordered_vars t2) (fun mode lstArgs => get_in_args' mode lstArgs).

(** Animate one let-clause by first computing its input variable list from
    context, then delegating to [animate_one_conj_any_let]. *)
Definition animate_one_conj_let_cl {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
let  inputVarsLst := get_conj_input_var_lst conjunct' allVarTpInf (modes) (predTypeInf) in
animate_one_conj_any_let ind kn conjunct' inputVarsLst partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel.

(** Animate one guard-predicate clause by first computing its input variable
    list from context, then delegating to [animate_one_conj_pred_guard]. *)
Definition animate_one_conj_pred_guard_cl {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (partialGuard : term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term) :=

let  inputVarsLst := get_conj_input_var_lst conjunct' allVarTpInf (modes) (predTypeInf) in
animate_one_conj_pred_guard ind kn conjunct' inputVarsLst partialGuard (modes) (predTypeInf) (allVarTpInf) fuel.

(** Animate a list of let-binding conjuncts left-to-right, threading the
    accumulated let-binding function [partialLetfn] through each step. *)
Fixpoint animate_list_conj_let_cl {A : Type} (ind : A) (kn : kername) (conjs : list (term * (string * term))) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
  match conjs with
  | [] => tmReturn partialLetfn
  | h :: t => lFn' <- animate_one_conj_let_cl ind kn h partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel ;; animate_list_conj_let_cl ind kn t lFn' (modes) (predTypeInf) (allVarTpInf) fuel
  end.

(** Animate a list of predicate guard conjuncts, threading the accumulated
    boolean guard [partialGuard] through each step. *)
Fixpoint animate_list_conj_pred_guard_cl {A : Type} (ind : A) (kn : kername) (conjs : list (term * (string * term))) (partialGuard : term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term) :=
  match conjs with
  | [] => tmReturn partialGuard
  | h :: t => pg <- animate_one_conj_pred_guard_cl ind kn h partialGuard (modes) (predTypeInf) (allVarTpInf) fuel ;; animate_list_conj_pred_guard_cl ind kn t pg (modes) (predTypeInf) (allVarTpInf) fuel
  end.

(** Combine a list of equality conjuncts into a single boolean guard expression
    by folding [animate_one_conj_succ_guard] right-to-left, starting from [true]. *)
Fixpoint animate_list_conj_eq_guard (conj : list term) : term :=
  match conj with
  | [] => <% true %>
  | h :: t =>
    match animate_list_conj_eq_guard t with
    | gt => animate_one_conj_succ_guard h gt
    end
  end.

(** Compile a guard-equality clause into an executable function: build a boolean
    guard from [gConjsEq] via [animate_list_conj_eq_guard], wrap it in a
    [constr_fn_body_guard_con] body, and generate a pattern-matching function. *)
Definition gen_fun_animate_eq_partial_guard_con' {A : Type} (induct : A) (kn : kername) (gConjsEq : list term)  (inputTm : term) (inputTp : term)  (outputTm : term) (outputTp : term) (fuel : nat) : TemplateMonad term :=

  (let postOut' := (constr_fn_body_guard_con outputTm outputTp

    (animate_list_conj_eq_guard (gConjsEq) )) in

    let postOutType' := tApp <% @option %> [outputTp] in

    let postInType' := inputTp in

    let postIn' := inputTm in

    let postIn := tApp <%Success%> [postInType'; postIn'] in
    let postInType := tApp <%animation_result%> [postInType'] in

    let postOut := tApp <%Success%> [postOutType'; postOut'] in
    let postOutType := tApp <%animation_result%> [postOutType'] in

     t0 <- constr_fun_animate_eq induct postIn' postInType' postOut' postOutType'  fuel ;;

     let t1 := (tApp <%option_to_outcome%> [postInType'; outputTp; t0]) in
     t' <- tmEval all (typeConstrPatMatch.unwrap_option_term (DB.de_bruijn_option t1)) ;;
     tmReturn t').

(** Lift [gen_fun_animate_eq_partial_guard_con'] to work directly with variable
    type lists by computing the product input/output types from [allVarTpInf] and [outVars]. *)
Definition animate_list_conj_guard_eq {A : Type} (induct : A) (kn : kername) (gConjsEq : list term) (allVarTpInf : list (prod string term))  (outVars : list (prod string term)) (fuel : nat) : TemplateMonad term :=
gen_fun_animate_eq_partial_guard_con' induct kn gConjsEq  (telescope_to_prod_term allVarTpInf) (telescope_to_prod_type allVarTpInf) (telescope_to_prod_term outVars) (telescope_to_prod_type outVars) fuel.

(** Build a term that pattern-matches an [animation_result bool] guard and
    dispatches to one of four continuations: [succTrueRetTm] (guard true),
    [succFalseRetTm] (guard false), [noMatchRetTm], or [fuelErrorRetTm]. *)
Definition branch_outcome_bool_fn (retType succTrueRetTm succFalseRetTm noMatchRetTm fuelErrorRetTm : term) : term :=
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
Definition animate_list_conj_pred_guard_br_out_bool {A : Type} (ind : A) (kn : kername) (predGuardConjs : list (term × string × term))  (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (outVars : list (prod string term)) (guardConEqAn : term) (fuel : nat) : TemplateMonad (term) :=
predGuardCon <- animate_list_conj_pred_guard_cl (ind) (kn) (predGuardConjs) <%Success bool true%> (modes) (predTypeInf) (allVarTpInf) (fuel) ;;
let brOutBool := branch_outcome_bool_fn (tApp <%animation_result%> [telescope_to_prod_type outVars]) (guardConEqAn) (tApp <%NoMatch%> [telescope_to_prod_type outVars]) (tApp <%NoMatch%> [telescope_to_prod_type outVars]) (tApp <%FuelError%> [telescope_to_prod_type outVars]) in
tmReturn (tApp brOutBool [predGuardCon]).

(** Insert [tLetIn] bindings that split a product [inTerm] into individual
    variable names according to [inVars], using [split_outcome_poly_fst]/[Snd]. *)
Fixpoint split_inputs (inVars : list (string * term)) (inTerm : term) (fnBody : term) : term :=
  match inVars with
  | [] => fnBody
  | [h] => (tLetIn {| binder_name := nNamed (fst h); binder_relevance := Relevant |}
                                 inTerm (tApp <%animation_result%> [(snd h)])) fnBody
  | h' :: rest' =>  (tLetIn {| binder_name := nNamed (fst h'); binder_relevance := Relevant |}
                                 (tApp <% split_outcome_poly_fst %> [(snd h'); (telescope_to_prod_type rest'); inTerm])  (tApp <%animation_result%> [(snd h')])) (split_inputs rest' (tApp <% split_outcome_poly_snd %> [(snd h'); (telescope_to_prod_type rest'); inTerm]) fnBody)
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
Definition animate_list_let_and_pred_guard {A : Type} (ind : A) (kn : kername) (lConjs'' : list (term × (string × term))) (gConjsEq'' : list term) (gConjsPred'' : list (term × (string × term))) (inVars : list (prod string term)) (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=
lConjs <- tmEval all lConjs'';;
gConjsEq <- tmEval all gConjsEq'';;
gConjsPred <- tmEval all gConjsPred'';;
letBind <- animate_list_conj_let_cl  (ind) kn  lConjs  (fun t : term => t) (modes) (predTypeInf) (allVarTpInf) (fuel) ;;
gFun <- animate_list_conj_guard_eq ind kn gConjsEq allVarTpInf outVars fuel ;;
let guardConEqAn := (tApp gFun [tVar "fuel"; mk_out_poly_prod_tm (allVarTpInf)]) in
combineGuard <- animate_list_conj_pred_guard_br_out_bool (ind) (kn) (gConjsPred) (modes) (predTypeInf) (allVarTpInf) (outVars) (guardConEqAn) (fuel);;
  match inVars with
  | h :: rest => tmReturn (mk_lam_tp (app (mk_animated_fn_nm lhsPreds) [("fuel", <%nat%>)]) (tLam "input" (tApp <%animation_result%> [telescope_to_prod_type inVars])(split_inputs' inVars (letBind combineGuard))))
  | [] => tmReturn (mk_lam_tp (app (mk_animated_fn_nm lhsPreds) [("fuel", <%nat%>)]) (tLam "input" (tApp <%animation_result%> [<%bool%>]) (split_inputs' inVars (letBind combineGuard))))

  end.

(** Keep only the equality ([eq]) conjuncts from a list, discarding predicates. *)
Fixpoint filter_conjs_eq (lst : list term) : list term :=
  match lst with
  | [] => []
  | (tApp <%eq%> [typeVar; t1; t2]) :: rest =>  (tApp <%eq%> [typeVar; t1; t2]) :: filter_conjs_eq rest

  | _h :: rest => filter_conjs_eq rest
  end.
(** Keep only inductive predicate application conjuncts from a list,
    discarding equalities and other forms. *)
Fixpoint filter_conjs_pred (lst : list term) : list term :=
  match lst with
  | [] => []
  | (tApp <%eq%> [typeVar; t1; t2]) :: rest =>  filter_conjs_pred rest

  | (tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs) :: rest => (tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs) :: filter_conjs_pred rest

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
Fixpoint mk_lhs_prod_type2_non_monad (lhsIndPre : list (term * term)) : term :=
  match lhsIndPre with
  | []      => <%bool%>
  | [h]     => snd h
  | h :: t  => tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; mk_lhs_prod_type2_non_monad t]
  end.

(** Build a product term from a list of (term * type) pairs; base case is [true]. *)
Fixpoint mk_lhs_prod_tm2_non_monad (lhsIndPre : list (term * term)) : term :=
  match lhsIndPre with
  | []     => <%true%>
  | [h]    => fst h
  | h :: t => tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
                     [snd h; mk_lhs_prod_type2_non_monad t; fst h; mk_lhs_prod_tm2_non_monad t]
  end.

(** Look up the argument types for predicate [indNm] in [predTypeInf]. *)
Fixpoint get_pred_tp_fm_lst (indNm : string) (predTypeInf : list (string * (list term))) : list term :=
  match predTypeInf with
  | []         => []
  | h :: rest  => if String.eqb indNm (fst h) then snd h else get_pred_tp_fm_lst indNm rest
  end.

(** Rewrite a predicate conjunct into an equality against the animated function.
    Currently a stub — returns the conjunct unchanged. *)
Definition rewrite_pred_conj (conj' : term) (modes : list (string * (list nat * list nat))) (predTypeInf : list (string * (list term))) : term := conj'.

(** Topologically sort and orient conjuncts by known variables [kv]:
    equalities where one side is fully known go to [sortedConjs] (let-bindings);
    equalities where both sides are known go to [guardConjs] (boolean guards);
    predicate applications ready to evaluate go to [sortedConjs];
    all others are deferred in [remConjs] for the next pass. *)
Fixpoint classify_premises_by_mode (modes : list (string * ((list nat) * (list nat)))) (currentConjs : list term) (remConjs : list term) (sortedConjs : list term) (guardConjs : list term) (kv : (list string)) (fuel : nat) : TemplateMonad (prod (list term) (list term)) :=
  match fuel with
  | 0 => if andb (is_empty_lst remConjs) (is_empty_lst currentConjs) then tmReturn (sortedConjs, guardConjs) else tmFail "insufficient fuel to sort conjs"
  | S n => if (andb (is_empty_lst remConjs) (is_empty_lst currentConjs)) then tmReturn (sortedConjs, guardConjs) else
           match currentConjs with
            | [] => classify_premises_by_mode modes remConjs [] sortedConjs guardConjs kv n
            | conj' :: t => match conj' with
                        | tApp <%eq%> [typeVar; t1; t2] => if andb (is_list_sub_str (extract_ordered_vars t1) kv) (is_list_sub_str (extract_ordered_vars t2) kv) then
                                                            classify_premises_by_mode modes t remConjs sortedConjs (conj' :: guardConjs) kv n else
                                                            (if (andb (is_list_sub_str (extract_ordered_vars t1) kv) (has_right_shape t2)) then

                                                            classify_premises_by_mode modes t remConjs (tApp <%eq%> [typeVar; t2; t1] :: sortedConjs) (guardConjs) (app (extract_ordered_vars t2) kv) n else
                                                            (if  (andb (is_list_sub_str (extract_ordered_vars t2) kv) (has_right_shape t1)) then classify_premises_by_mode modes t remConjs (tApp <%eq%> [typeVar; t1; t2] :: sortedConjs) (guardConjs) (app (extract_ordered_vars t1) kv) n else
                                                            (classify_premises_by_mode modes t (conj' :: remConjs) (sortedConjs) (guardConjs) (kv) n)))

                        | _ => match extract_ind_name conj' with
                               | Some (indNm, lstArgs) =>
                                   if is_list_sub_str (concat (List.map extract_ordered_vars lstArgs)) kv then classify_premises_by_mode modes t remConjs sortedConjs (conj' :: guardConjs) kv n
                                   else if is_list_sub_str (extract_ordered_vars_fm_lst (get_in_args indNm modes lstArgs)) kv then classify_premises_by_mode modes t remConjs (conj' :: sortedConjs) guardConjs (app (extract_ordered_vars_fm_lst (get_out_args indNm modes lstArgs)) kv) n
                                   else classify_premises_by_mode modes t (conj' :: remConjs) sortedConjs guardConjs kv n
                               | None => tmFail "incorrect conj shape"
                               end
                        end
           end
  end.

(** Run [classify_premises_by_mode] and extract one half of the result via [proj],
    optionally reversing (let-bindings are reversed to restore declaration order). *)
Definition get_classified_conjs (proj : list term * list term -> list term) (doReverse : bool) (modes : list (string * ((list nat) * (list nat)))) (currentConjs : list term) (remConjs : list term) (sortedConjs : list term) (guardConjs : list term) (kv : (list string)) (fuel : nat) : TemplateMonad (list term) :=
sConjs <- classify_premises_by_mode modes (currentConjs) (remConjs) (sortedConjs) (guardConjs) (kv) (fuel) ;;
result <- tmEval all (if doReverse then rev (proj sConjs) else proj sConjs) ;;
tmReturn result.

(** Classify and extract the let-binding conjuncts (sorted, reversed to declaration order). *)
Definition get_sorted_oriented_conjs_let := get_classified_conjs fst true.
(** Classify and extract the guard conjuncts (sorted, kept in natural order). *)
Definition get_sorted_oriented_conjs_guard := get_classified_conjs snd false.

(** Get all output variables introduced by a conjunct (LHS of an equality,
    or out-mode arguments of a predicate). *)
Definition get_conj_all_output_vars (conj : term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (prod string term) :=
get_conj_vars_by_role (fun t1 _t2 => extract_ordered_vars t1) (fun mode lstArgs => get_out_args' mode lstArgs) (conj, (""%bs, <%bool%>)) allVarTpInf modes predTypeInf.

(** Pair each conjunct in [lconjs] with the output variables it introduces. *)
Fixpoint attach_output_var_lst (lconjs : list term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : (list (prod term (list (prod string term)))) :=
  match lconjs with
  | [] => []
  | h :: t => (h, get_conj_all_output_vars h allVarTpInf modes predTypeInf) :: attach_output_var_lst t allVarTpInf modes predTypeInf
  end.

(** Tag a single conjunct term [lconjt] with each output variable in [lconjV],
    producing one [(conjunct, output_var)] pair per variable. *)
Fixpoint attach_output_var' (lconjt : term) (lconjV : (((list (string * term))))) : list (term * (string * term)) :=
  match (lconjV) with
  | [] => []
  | (h :: rest) => ((lconjt), h) :: attach_output_var' lconjt rest
  end.

(** Flatten a list of [(conjunct, output_vars)] pairs into a flat list of
    [(conjunct, output_var)] pairs by applying [attach_output_var']. *)
Fixpoint attach_output_var (lconjs : (list (prod term (list (prod string term))))) : list (term * (string * term)) :=
  match lconjs with
  | [] => []
  | h :: rest => app (attach_output_var' (fst h) (snd h)) (attach_output_var rest)
  end.
(** Convert a sorted conjunct list to a tagged [(conjunct, output_var)] list. *)
Definition attach_output_var_to_sorted_conjs (lconjs : list term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (term * (string * term)) :=
attach_output_var (attach_output_var_lst lconjs allVarTpInf modes predTypeInf).

(** Remove conjuncts whose output variable already appears in [kv] (already defined),
    adding newly seen output variables to [kv] as they are encountered. *)
Fixpoint remove_duplicate_defs (lconjs : list (term * (string * term))) (kv : list string) : list (term * (string * term))  :=
  match lconjs with
  | [] => []
  | h :: rest => if (in_str_lst (fst (snd h)) kv) then remove_duplicate_defs rest kv  else h :: (remove_duplicate_defs rest ((fst (snd h)) :: kv))
  end.

(** Keep only conjuncts whose output variable already appears in [kv] (duplicates),
    adding first occurrences to [kv] so subsequent duplicates are kept. *)
Fixpoint keep_duplicate_defs (lconjs : list (term * (string * term))) (kv : list string) : list (term * (string * term))  :=
  match lconjs with
  | [] => []
  | h :: rest => if (in_str_lst (fst (snd h)) kv) then h :: (keep_duplicate_defs rest kv)  else (keep_duplicate_defs rest ((fst (snd h)) :: kv))
  end.

(** Keep only inductive predicate application entries from a tagged conjunct list,
    discarding equalities and other shapes. *)
Fixpoint filter_conjs_pred' (lst : list (term * (string * term))) : list (term * (string * term)) :=
  match lst with
  | [] => []
  | ((tApp <%eq%> [typeVar; t1; t2]), (str,t'')) :: rest => filter_conjs_pred' rest
  | ((tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs), (str, t2)) :: rest => ((tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs), (str, t2)) :: filter_conjs_pred' rest

  | ((tApp (tVar indNm) lstArgs), (str, t2)) :: rest => ((tApp (tVar indNm) lstArgs), (str, t2)) :: filter_conjs_pred' rest

  | _h :: rest => filter_conjs_pred' rest
  end.
