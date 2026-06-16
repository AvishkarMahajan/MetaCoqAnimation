(** * AnimationDispatch — Unified Conjunction Dispatcher

    Integrates equality resolution and pattern-match compilation into a
    single dispatch layer.  Given a list of conjuncts from a constructor
    clause, this module separates them into let-binding equalities, guard
    predicates, and recursive calls, then animates each piece and
    assembles the final executable term via [animate_lets_and_guards].

    Depends on: [MetaRocqUtils], [PatternCompilation], [EqualityResolution]. *)

Require Import Animation.AnimationTypes.
Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
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
  (in_tm : term) (in_tp : term)
  (in_vars : list string)
  (modes : mode_map)
  (pred_types : pred_type_map)
  (var_env : list (string * term))
  (fuel : nat) : TemplateMonad term :=

out_tm <- tmEval all (tVar conjunct'.(tc_out_var)) ;;
out_tp <- tmEval all (conjunct'.(tc_out_type)) ;;
let conjunct := conjunct'.(tc_conjunct) in

match conjunct with
 | tApp <%eq%> [typeVar; t1; t2] => match t1 with
                                    | tVar str =>  match in_vars with
                                                    | [] => tmReturn (tApp <%Success%> [typeVar;t2])
                                                    | h :: rest =>
                                                      compile_let_clause ind kn conjunct
                                                        in_tm in_tp out_tm
                                                        out_tp in_vars fuel
                                                   end
                                    | tApp (tConstruct ind_type k lst) lstArgs =>
                                      compile_eq_binders_with_vars ind kn
                                        conjunct in_tm in_tp
                                        out_tm out_tp in_vars fuel
                                    | _ => tmFail "incorrect Conj shape"
                                    end

 | _ => match get_ind_name conjunct with
        | Some (ind_nm, _lstArgs) =>
            match fst (lookup_mode ind_nm modes) with
            | [] => animate_no_input ind kn conjunct' modes pred_types var_env fuel
            | _ => compile_clause ind kn conjunct' modes pred_types var_env fuel
            end
        | None => tmFail "incorrect Conj shape"
        end
end.

(** Wrap an animation function call in a [tLetIn] that binds the output variable,
    extending [partial_fn].  Handles three cases: no inputs (direct value),
    a single input (apply with fuel + input), or multiple inputs (join first). *)
Definition build_let_chain_step
  (out_var_nm : string) (out_var_tp : term)
  (in_vars_lst : list (prod term term))
  (anim_fn : term)
  (partial_fn : term -> term) : (term -> term) :=
  match in_vars_lst with
  | [] =>
    (fun t => partial_fn
      ((tLetIn
        {| binder_name := nNamed out_var_nm;
           binder_relevance := Relevant |}
        (anim_fn)
        (tApp <%animation_result%> [out_var_tp]))
        t))
  | [h] =>
    (fun t => partial_fn
      ((tLetIn
        {| binder_name := nNamed out_var_nm;
           binder_relevance := Relevant |}
        (tApp anim_fn [(tVar "fuel"); fst h])
        (tApp <%animation_result%> [out_var_tp]))
        t))
  | _ =>
    (fun t => partial_fn
      ((tLetIn
        {| binder_name := nNamed out_var_nm;
           binder_relevance := Relevant |}
        (tApp anim_fn
          [(tVar "fuel");
           (tApp (mk_join_tm (map snd in_vars_lst))
              (map fst in_vars_lst))])
        (tApp <%animation_result%> [out_var_tp]))
        t))
  end.

(** Animate one conjunction as a let-binding step: compile [conjunct'] into
    a function and wrap it in a let that extends [partial_fn]. *)
Definition animate_one_let {A : Type}
  (ind : A) (kn : kername)
  (conjunct' : tagged_conjunct)
  (in_vars_lst : list (prod string term))
  (partial_fn : term -> term)
  (modes : mode_map)
  (pred_types : pred_type_map)
  (var_env : list (string * term))
  (fuel : nat) : TemplateMonad (term -> term) :=
let in_tm := tele_to_prod_tm in_vars_lst in
let in_tp := tele_to_prod_tp in_vars_lst in
let inputVarsLstTm := pairs_to_terms in_vars_lst in
out_var_nm <- tmEval all (conjunct'.(tc_out_var)) ;;
out_var_tp <- tmEval all (conjunct'.(tc_out_type)) ;;
anim_fn <- animate_let_binding (ind) (kn) (conjunct')
  (in_tm) (in_tp) (map fst in_vars_lst)
  (modes) (pred_types) (var_env) fuel ;;
tmReturn (build_let_chain_step (out_var_nm) (out_var_tp)
  (inputVarsLstTm) (anim_fn) (partial_fn)).

(** Animate one conjunction as a boolean predicate guard: compile [conjunct'] and
    produce a [and_outcome_bool] expression that extends [guard_acc]. *)
Definition animate_one_guard {A : Type}
  (ind : A) (kn : kername)
  (conjunct' : tagged_conjunct)
  (in_vars_lst : list (prod string term))
  (guard_acc : term)
  (modes : mode_map)
  (pred_types : pred_type_map)
  (var_env : list (string * term))
  (fuel : nat) : TemplateMonad term :=
let in_tm := tele_to_prod_tm in_vars_lst in
let in_tp := tele_to_prod_tp in_vars_lst in
let inputVarsLstTm := pairs_to_terms in_vars_lst in
in_tm' <- tmEval all in_tm;;
in_tp' <- tmEval all in_tp;;
out_var_nm <- tmEval all (conjunct'.(tc_out_var)) ;;
out_var_tp <- tmEval all (conjunct'.(tc_out_type)) ;;

anim_fn <- animate_let_binding (ind) (kn) (conjunct') (in_tm) (in_tp)
                                 (map fst in_vars_lst) (modes) (pred_types) (var_env) fuel ;;

tmReturn (tApp <%and_outcome_bool%>
  [guard_acc ;
   tApp (mk_eq_outcome_tm out_var_tp
     (type_to_eq_fn out_var_tp))
     [tVar out_var_nm ;
      (tApp anim_fn
        [(tVar "fuel");
         (tApp (mk_join_tm (map snd in_vars_lst))
            (map fst inputVarsLstTm))])] ]).

(** Extract input or output variables from a conjunct (named) using [eq_proj]
    for equalities and [mode_proj] for inductive predicate applications. *)
Definition conj_vars_by_role
  (eq_proj : named_term -> named_term -> list string)
  (mode_proj : (list nat * list nat) ->
    list term -> list term)
  (conjunct' : tagged_conjunct)
  (var_env : list (prod string term))
  (modes : mode_map)
  (pred_types : pred_type_map)
  : list (prod string term) :=
let conjunct := conjunct'.(tc_conjunct) in
  match conjunct with
  | tApp <%eq%> [typeVar; t1; t2] => lookup_vars (eq_proj t1 t2) var_env
  | tApp (tInd {| inductive_mind := (_path, ind_nm); inductive_ind := 0 |} []) lstArgs =>
     let mode := lookup_mode ind_nm modes in
     lookup_vars (ordered_vars_of_list (mode_proj mode lstArgs)) var_env
  | tApp (tVar ind_nm) lstArgs =>
     let mode := lookup_mode ind_nm modes in
     lookup_vars (ordered_vars_of_list (mode_proj mode lstArgs)) var_env
  | _ => []
  end.

(** Get the input variable list for a conjunct (named): RHS variables of
    equalities, or in-mode arguments of inductive predicate applications. *)
Definition conj_input_vars :=
  conj_vars_by_role
    (fun _t1 t2 => ordered_vars t2)
    (fun mode lstArgs =>
      select_in_by_mode mode lstArgs).

(** Animate one let-clause by first computing its input variable list (named)
    from context, then delegating to [animate_one_let].  Boundary: named to
    de Bruijn. *)
Definition animate_let_with_ctx {A : Type}
  (ind : A) (kn : kername)
  (conjunct' : tagged_conjunct)
  (partial_fn : term -> term)
  (modes : mode_map)
  (pred_types : pred_type_map)
  (var_env : list (string * term))
  (fuel : nat) : TemplateMonad (term -> term) :=
let  in_vars_lst := conj_input_vars conjunct' var_env (modes) (pred_types) in
animate_one_let ind kn conjunct' in_vars_lst partial_fn (modes) (pred_types) (var_env) fuel.

(** Animate one guard-predicate clause by first computing its input variable
    list (named) from context, then delegating to [animate_one_guard].
    Boundary: named to de Bruijn. *)
Definition animate_guard_with_ctx {A : Type}
  (ind : A) (kn : kername)
  (conjunct' : tagged_conjunct)
  (guard_acc : term)
  (modes : mode_map)
  (pred_types : pred_type_map)
  (var_env : list (string * term))
  (fuel : nat) : TemplateMonad (term) :=

let  in_vars_lst := conj_input_vars conjunct' var_env (modes) (pred_types) in
animate_one_guard ind kn conjunct' in_vars_lst
  guard_acc (modes) (pred_types) (var_env) fuel.

(** Animate a list of let-binding conjuncts left-to-right, threading the
    accumulated let-binding function [partial_fn] through each step. *)
Fixpoint animate_let_list {A : Type}
  (ind : A) (kn : kername)
  (conjs : list tagged_conjunct)
  (partial_fn : term -> term)
  (modes : mode_map)
  (pred_types : pred_type_map)
  (var_env : list (string * term))
  (fuel : nat) : TemplateMonad (term -> term) :=
  match conjs with
  | [] => tmReturn partial_fn
  | h :: t =>
    lFn' <- animate_let_with_ctx ind kn h
      partial_fn (modes) (pred_types)
      (var_env) fuel ;;
    animate_let_list ind kn t lFn'
      (modes) (pred_types) (var_env) fuel
  end.

(** Animate a list of predicate guard conjuncts, threading the accumulated
    boolean guard [guard_acc] through each step. *)
Fixpoint animate_guard_list {A : Type}
  (ind : A) (kn : kername)
  (conjs : list tagged_conjunct)
  (guard_acc : term)
  (modes : mode_map)
  (pred_types : pred_type_map)
  (var_env : list (string * term))
  (fuel : nat) : TemplateMonad (term) :=
  match conjs with
  | [] => tmReturn guard_acc
  | h :: t =>
    pg <- animate_guard_with_ctx ind kn h
      guard_acc (modes) (pred_types)
      (var_env) fuel ;;
    animate_guard_list ind kn t pg
      (modes) (pred_types) (var_env) fuel
  end.

(** Combine a list of equality conjuncts (named) into a single boolean guard
    expression (named) by folding [animate_conj_guard] right-to-left, starting
    from [true]. *)
Fixpoint build_eq_guard_chain (conj : list named_term) : named_term :=
  match conj with
  | [] => <% true %>
  | h :: t =>
    match build_eq_guard_chain t with
    | gt => animate_conj_guard h gt
    end
  end.

(** Compile a guard-equality clause into an executable function (de Bruijn):
    build a boolean guard from [g_conjs_eq] via [build_eq_guard_chain], wrap it
    in a [build_guarded_body] body, and generate a pattern-matching function.
    Type params [in_tm], [in_tp], [out_tm], [out_tp] are global. *)
Definition compile_guard_clause {A : Type}
  (induct : A) (kn : kername)
  (g_conjs_eq : list named_term)
  (in_tm : global_term) (in_tp : global_term)
  (out_tm : global_term) (out_tp : global_term)
  (fuel : nat) : TemplateMonad term :=

  (let post_out' := (build_guarded_body out_tm out_tp

    (build_eq_guard_chain (g_conjs_eq) )) in

    let post_out_tp' := tApp <% @option %> [out_tp] in

    let post_in_tp' := in_tp in

    let post_in' := in_tm in

    let post_in := tApp <%Success%> [post_in_tp'; post_in'] in
    let post_in_tp := tApp <%animation_result%> [post_in_tp'] in

    let post_out := tApp <%Success%> [post_out_tp'; post_out'] in
    let post_out_tp := tApp <%animation_result%> [post_out_tp'] in

     t0 <- compile_equality_clause induct post_in' post_in_tp' post_out' post_out_tp'  fuel ;;

     let t1 := (tApp <%option_to_result%> [post_in_tp'; out_tp; t0]) in
     match DB.de_bruijn_option t1 with
     | Some db_t1 =>
       t' <- tmEval all db_t1 ;;
       tmReturn t'
     | None => tmFail "de Bruijn conversion failed in compile_guard_clause"
     end).

(** Lift [compile_guard_clause] to work directly with variable type lists by
    computing the global product input/output types from [var_env] and
    [out_vars].  Returns a de Bruijn term. *)
Definition animate_guard_eq {A : Type}
  (induct : A) (kn : kername)
  (g_conjs_eq : list named_term)
  (var_env : list (prod string term))
  (out_vars : list (prod string term))
  (fuel : nat) : TemplateMonad term :=
compile_guard_clause induct kn g_conjs_eq
  (tele_to_prod_tm var_env)
  (tele_to_prod_tp var_env)
  (tele_to_prod_tm out_vars)
  (tele_to_prod_tp out_vars) fuel.

(** Build a de Bruijn term that pattern-matches an [animation_result bool] guard
    and dispatches to one of four continuations: [succ_true] (guard true),
    [succ_false] (guard false), [no_match], or [fuel_error].
    Returns a de Bruijn case expression. *)
Definition branch_on_bool
  (ret_tp succ_true succ_false
   no_match fuel_error : term) : term :=
let splitSuccBinder := {| binder_name := nNamed "splitSuccCase"; binder_relevance := Relevant |} in
let gcPredBinder := {| binder_name := nNamed "gcPred"; binder_relevance := Relevant |} in
let boolCase :=
  tCase
    {| ci_ind := {| inductive_mind := <?bool?>; inductive_ind := 0 |};
       ci_npar := 0; ci_relevance := Relevant |}
    {| puinst := []; pparams := [];
       pcontext := [splitSuccBinder]; preturn := ret_tp |}
    (tVar "splitSuccCase")
    [{| bcontext := []; bbody := succ_true |};
     {| bcontext := []; bbody := succ_false |}] in
tLam "gcPred" (tApp <%animation_result%> [<%bool%>])
  (tCase
    {| ci_ind := {| inductive_mind := (MPfile ["AnimationResult"; "Animation"], "animation_result");
                     inductive_ind := 0 |};
       ci_npar := 1; ci_relevance := Relevant |}
    {| puinst := []; pparams := [<%bool%>];
       pcontext := [gcPredBinder]; preturn := ret_tp |}
    (tVar "gcPred")
    [{| bcontext := []; bbody := fuel_error |};
     {| bcontext := [splitSuccBinder]; bbody := boolCase |};
     {| bcontext := []; bbody := no_match |}]).

(** Animate predicate guard conjuncts and branch on their boolean result:
    passes [guard_eq_an] (the equality guard) as the [true] branch and
    [NoMatch] as the [false] branch.  Type params are global.
    Returns a de Bruijn term. *)
Definition animate_guard_bool_branch {A : Type}
  (ind : A) (kn : kername)
  (pred_guard : list tagged_conjunct)
  (modes : mode_map)
  (pred_types : pred_type_map)
  (var_env : list (string * global_term))
  (out_vars : list (prod string global_term))
  (guard_eq_an : term)
  (fuel : nat) : TemplateMonad (term) :=
predGuardCon <- animate_guard_list (ind) (kn)
  (pred_guard) <%Success bool true%>
  (modes) (pred_types) (var_env) (fuel) ;;
let br_out_bool :=
  branch_on_bool
    (tApp <%animation_result%>
      [tele_to_prod_tp out_vars])
    (guard_eq_an)
    (tApp <%NoMatch%> [tele_to_prod_tp out_vars])
    (tApp <%NoMatch%> [tele_to_prod_tp out_vars])
    (tApp <%FuelError%>
      [tele_to_prod_tp out_vars]) in
tmReturn (tApp br_out_bool [predGuardCon]).

(** Insert [tLetIn] bindings that split a product [in_term] (de Bruijn) into
    individual variable names according to [in_vars], using
    [split_outcome_fst]/[Snd].  Returns a de Bruijn term. *)
Fixpoint split_inputs (in_vars : list (string * term)) (in_term : term) (body : term) : term :=
  match in_vars with
  | [] => body
  | [h] => (tLetIn {| binder_name := nNamed (fst h); binder_relevance := Relevant |}
                                 in_term (tApp <%animation_result%> [(snd h)])) body
  | h' :: rest' =>
    (tLetIn
      {| binder_name := nNamed (fst h');
         binder_relevance := Relevant |}
      (tApp <% split_outcome_fst %>
        [(snd h'); (tele_to_prod_tp rest');
         in_term])
      (tApp <%animation_result%> [(snd h')]))
      (split_inputs rest'
        (tApp <% split_outcome_snd %>
          [(snd h'); (tele_to_prod_tp rest');
           in_term])
        body)
  end.
(** Convenience wrapper: split the [input] variable into [in_vars] bindings
    (de Bruijn), or leave [body] unchanged if [in_vars] is empty. *)
Definition split_inputs' (in_vars : list (string * term)) (body : term) : term :=
  match in_vars with
  | [] => body
  | _ => split_inputs in_vars (tVar "input") body
  end.

(** Assemble the full animated body of a constructor clause: animate the
    let-binding conjuncts [l_conjs''], combine the equality guard [g_conjs_eq'']
    (named) and predicate guards [g_conjs_pred''] into a single branching guard,
    and wrap everything in lambdas for the animated recursive functions and the
    input.  Returns a de Bruijn term. *)
Definition animate_lets_and_guards {A : Type}
  (ind : A) (kn : kername)
  (l_conjs'' : list tagged_conjunct)
  (g_conjs_eq'' : list named_term)
  (g_conjs_pred'' : list tagged_conjunct)
  (in_vars : list (prod string term))
  (out_vars : list (prod string term))
  (modes : mode_map)
  (pred_types : pred_type_map)
  (var_env : list (string * term))
  (lhs_preds : list (string * term))
  (fuel : nat) : TemplateMonad term :=
l_conjs <- tmEval all l_conjs'';;
g_conjs_eq <- tmEval all g_conjs_eq'';;
g_conjs_pred <- tmEval all g_conjs_pred'';;
(* Animate let-binding conjuncts into a chain of let-in expressions *)
let_bind <- animate_let_list (ind) kn l_conjs
  (fun t : term => t) (modes) (pred_types)
  (var_env) (fuel) ;;
(* Animate equality guards into a boolean function *)
g_fn <- animate_guard_eq ind kn g_conjs_eq var_env out_vars fuel ;;
let guard_eq_an := (tApp g_fn [tVar "fuel"; mk_output_prod_tm (var_env)]) in
(* Combine predicate guards with equality guard into a branching guard *)
combined <- animate_guard_bool_branch (ind) (kn)
  (g_conjs_pred) (modes) (pred_types)
  (var_env) (out_vars) (guard_eq_an) (fuel);;
  (* Wrap in lambdas for recursive function args, fuel, and input *)
  match in_vars with
  | h :: rest =>
    tmReturn (mk_lam_chain
      (mk_animated_names lhs_preds ++ [("fuel", <%nat%>)])
      (tLam "input"
        (tApp <%animation_result%>
          [tele_to_prod_tp in_vars])
        (split_inputs' in_vars
          (let_bind combined))))
  | [] =>
    tmReturn (mk_lam_chain
      (mk_animated_names lhs_preds ++ [("fuel", <%nat%>)])
      (tLam "input"
        (tApp <%animation_result%> [<%bool%>])
        (split_inputs' in_vars
          (let_bind combined))))

  end.

(** Keep only the equality ([eq]) conjuncts (named) from a list, discarding
    predicates. *)
Fixpoint filter_conjs_eq (lst : list named_term) : list named_term :=
  match lst with
  | [] => []
  | (tApp <%eq%> [typeVar; t1; t2]) :: rest =>
    (tApp <%eq%> [typeVar; t1; t2])
      :: filter_conjs_eq rest

  | _h :: rest => filter_conjs_eq rest
  end.
(** Keep only inductive predicate application conjuncts (named) from a list,
    discarding equalities and other forms. *)
Fixpoint filter_conjs_pred (lst : list named_term) : list named_term :=
  match lst with
  | [] => []
  | (tApp <%eq%> [typeVar; t1; t2]) :: rest =>  filter_conjs_pred rest

  | (tApp (tInd
      {| inductive_mind := (path, ind_nm);
         inductive_ind := 0 |} []) lstArgs)
      :: rest =>
    (tApp (tInd
      {| inductive_mind := (path, ind_nm);
         inductive_ind := 0 |} []) lstArgs)
      :: filter_conjs_pred rest

  | (tApp (tVar ind_nm) lstArgs) :: rest => (tApp (tVar ind_nm) lstArgs) :: filter_conjs_pred rest

  | _h :: rest => filter_conjs_pred rest
  end.

(** Check whether a named term is a bare variable or a constructor application —
    shapes that can appear on the output side of a let-binding equation. *)
Definition has_right_shape (t : named_term) : bool :=
  match t with
  | tVar str => true
  | tApp (tConstruct ind_type k lst) lstArgs => true
  | _ => false
  end.

(** Build a de Bruijn product type from a list of (term * type) pairs;
    base case is [bool]. *)
Fixpoint mk_lhs_type_pure (lhs_preds : list (term * term)) : term :=
  match lhs_preds with
  | []      => <%bool%>
  | [h]     => snd h
  | h :: t  => tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; mk_lhs_type_pure t]
  end.

(** Build a de Bruijn product term from a list of (term * type) pairs;
    base case is [true]. *)
Fixpoint mk_lhs_term_pure (lhs_preds : list (term * term)) : term :=
  match lhs_preds with
  | []     => <%true%>
  | [h]    => fst h
  | h :: t => tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
                     [snd h; mk_lhs_type_pure t; fst h; mk_lhs_term_pure t]
  end.

(** Topologically sort and orient conjuncts (named) by known variables [kv]:
    equalities where one side is fully known go to [sorted_conjs] (let-bindings);
    equalities where both sides are known go to [guard_conjs] (boolean guards);
    predicate applications ready to evaluate go to [sorted_conjs];
    all others are deferred in [rem_conjs] for the next pass. *)
Fixpoint classify_premises
  (modes : mode_map)
  (curr_conjs : list named_term)
  (rem_conjs : list named_term)
  (sorted_conjs : list named_term)
  (guard_conjs : list named_term)
  (kv : (list string))
  (fuel : nat)
  : TemplateMonad (prod (list named_term) (list named_term)) :=
  match fuel with
  | 0 =>
    if andb (is_nil rem_conjs) (is_nil curr_conjs)
    then tmReturn (sorted_conjs, guard_conjs)
    else tmFail "insufficient fuel to sort conjs"
  | S n =>
    if (andb (is_nil rem_conjs) (is_nil curr_conjs))
    then tmReturn (sorted_conjs, guard_conjs)
    else
           match curr_conjs with
            | [] => classify_premises modes rem_conjs [] sorted_conjs guard_conjs kv n
            | conj' :: t =>
              match conj' with
              | tApp <%eq%> [typeVar; t1; t2] =>
                if andb
                  (is_subset_strings (ordered_vars t1) kv)
                  (is_subset_strings (ordered_vars t2) kv)
                then
                  classify_premises modes t rem_conjs
                    sorted_conjs (conj' :: guard_conjs)
                    kv n
                else
                (if (andb
                  (is_subset_strings (ordered_vars t1) kv)
                  (has_right_shape t2))
                then
                  classify_premises modes t rem_conjs
                    (tApp <%eq%>
                      [typeVar; t2; t1] :: sorted_conjs)
                    (guard_conjs)
                    (ordered_vars t2 ++ kv) n
                else
                (if (andb
                  (is_subset_strings (ordered_vars t2) kv)
                  (has_right_shape t1))
                then
                  classify_premises modes t rem_conjs
                    (tApp <%eq%>
                      [typeVar; t1; t2] :: sorted_conjs)
                    (guard_conjs)
                    (ordered_vars t1 ++ kv) n
                else
                (classify_premises modes t
                  (conj' :: rem_conjs) (sorted_conjs)
                  (guard_conjs) (kv) n)))
              | _ =>
                match get_ind_name conj' with
                | Some (ind_nm, lstArgs) =>
                  if is_subset_strings
                    (concat
                      (List.map ordered_vars lstArgs))
                    kv
                  then
                    classify_premises modes t rem_conjs
                      sorted_conjs
                      (conj' :: guard_conjs) kv n
                  else if is_subset_strings
                    (ordered_vars_of_list
                      (select_in_args ind_nm
                        modes lstArgs))
                    kv
                  then
                    classify_premises modes t rem_conjs
                      (conj' :: sorted_conjs) guard_conjs
                      (ordered_vars_of_list
                        (select_out_args ind_nm
                          modes lstArgs) ++ kv) n
                  else
                    classify_premises modes t
                      (conj' :: rem_conjs) sorted_conjs
                      guard_conjs kv n
                | None =>
                  tmFail "incorrect conj shape"
                end
              end
           end
  end.

(** Run [classify_premises] and extract one half of the result via [proj],
    optionally reversing (let-bindings are reversed to restore declaration order).
    All conjunct lists are named. *)
Definition get_classified
  (proj : list named_term * list named_term -> list named_term)
  (doReverse : bool)
  (modes : mode_map)
  (curr_conjs : list named_term)
  (rem_conjs : list named_term)
  (sorted_conjs : list named_term)
  (guard_conjs : list named_term)
  (kv : (list string))
  (fuel : nat) : TemplateMonad (list named_term) :=
sConjs <- classify_premises modes (curr_conjs)
  (rem_conjs) (sorted_conjs) (guard_conjs)
  (kv) (fuel) ;;
result <- tmEval all (if doReverse then rev (proj sConjs) else proj sConjs) ;;
tmReturn result.

(** Classify and extract the let-binding conjuncts (sorted, reversed to declaration order). *)
Definition get_sorted_lets := get_classified fst true.
(** Classify and extract the guard conjuncts (sorted, kept in natural order). *)
Definition get_sorted_guards := get_classified snd false.

(** Get all output variables introduced by a conjunct (named) (LHS of an
    equality, or out-mode arguments of a predicate). *)
Definition conj_output_vars
  (conj : named_term)
  (var_env : list (prod string term))
  (modes : mode_map)
  (pred_types : pred_type_map)
  : list (prod string term) :=
conj_vars_by_role
  (fun t1 _t2 => ordered_vars t1)
  (fun mode lstArgs =>
    select_out_by_mode mode lstArgs)
  {| tc_conjunct := conj; tc_out_var := ""%bs; tc_out_type := <%bool%> |}
  var_env modes pred_types.

(** Pair each conjunct (named) in [lconjs] with the output variables it
    introduces. *)
Fixpoint attach_output_vars
  (lconjs : list named_term)
  (var_env : list (prod string term))
  (modes : mode_map)
  (pred_types : pred_type_map)
  : (list (prod term (list (prod string term)))) :=
  match lconjs with
  | [] => []
  | h :: t =>
    (h, conj_output_vars h var_env
      modes pred_types)
      :: attach_output_vars t var_env
           modes pred_types
  end.

(** Tag a single conjunct term [lconj_t] (named) with each output variable in
    [lconj_v], producing one [(conjunct, output_var)] pair per variable. *)
Fixpoint attach_var_to_conj (lconj_t : named_term)
  (lconj_v : (((list (string * term)))))
  : list tagged_conjunct :=
  match (lconj_v) with
  | [] => []
  | (h :: rest) => {| tc_conjunct := lconj_t; tc_out_var := fst h; tc_out_type := snd h |} :: attach_var_to_conj lconj_t rest
  end.

(** Flatten a list of [(conjunct, output_vars)] pairs (named) into a flat list
    of [(conjunct, output_var)] pairs by applying [attach_var_to_conj]. *)
Fixpoint attach_vars_to_conjs
  (lconjs : (list (prod named_term
    (list (prod string term)))))
  : list tagged_conjunct :=
  match lconjs with
  | [] => []
  | h :: rest => attach_var_to_conj (fst h) (snd h) ++ attach_vars_to_conjs rest
  end.
(** Convert a sorted conjunct list (named) to a tagged [(conjunct, output_var)]
    list. *)
Definition attach_sorted_outputs
  (lconjs : list named_term)
  (var_env : list (prod string term))
  (modes : mode_map)
  (pred_types : pred_type_map)
  : list tagged_conjunct :=
attach_vars_to_conjs (attach_output_vars lconjs var_env modes pred_types).

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
        {| inductive_mind := (path, ind_nm);
           inductive_ind := 0 |} []) lstArgs =>
      h :: filter_conjs_pred' rest
    | tApp (tVar ind_nm) lstArgs =>
      h :: filter_conjs_pred' rest
    | _ => filter_conjs_pred' rest
    end
  end.
