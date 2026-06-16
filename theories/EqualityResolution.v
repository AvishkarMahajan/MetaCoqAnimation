(** * EqualityResolution — Equality-Based Clause Animation

    Handles the equality-resolution phase of animation: decomposing
    conjunctions into let-bindings, orienting equations so that the
    output variable is on the left, generating boolean equality functions
    for supported types, and compiling individual relation clauses via
    [compile_clause].

    Depends on: [MetaRocqUtils], [PatternCompilation]. *)

Require Import Animation.AnimationTypes.
Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.

From Stdlib Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.

Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.

(** Boolean equality on products, given equality functions for each component. *)
Definition eqb_prod (A : Type) (B : Type)
  (eq_a : A -> A -> bool) (eq_b : B -> B -> bool)
  (p1 : prod A B) (p2 : prod A B) : bool :=
andb (eq_a (fst p1) (fst p2)) (eq_b (snd p1) (snd p2)).

(** Boolean equality on [ind_tp], the wrapper type for inductive values. *)
Definition eqb_ind_tp (A : Type) (eq_a : A -> A -> bool) (a1 : ind_tp A) (a2 : ind_tp A) : bool :=
  match a1 with
  | indWrap a1' => match a2 with
                 | indWrap a2' => eq_a a1' a2'
                 end
  end.
(** Prefix prepended to an inductive name to form its boolean equality function name. *)
Definition eq_fn_prefix : string := "eqFn".

(** Map a type term (global) to its corresponding boolean equality function term (global).
    Handles [nat], [bool], [string], user-defined inductives, [list], [prod],
    and [ind_tp]; returns [false] (the trivially failing function) for unsupported types. *)
Fixpoint type_to_eq_fn (t : global_term) : global_term :=
  match t with
  | <%nat%> => <%Nat.eqb%>
  | <%bool%> => <%Bool.eqb%>
  | tInd
         {|
           inductive_mind := (MPdot (MPfile ["bytestring"; "Utils"; "MetaRocq"]) "String", "t");
           inductive_ind := 0
         |} [] => <%String.eqb%>
  | tInd {| inductive_mind := (defLoc, str);
            inductive_ind := _j |} [] =>
    tConst (defLoc, ((eq_fn_prefix ++ str))) []

  | tApp <%list%> [tp] => tApp <%@eqb_list%> [tp; (type_to_eq_fn tp)]
  | tApp <%prod%> [tp1 ; tp2] =>
    tApp <%eqb_prod%>
      [tp1; tp2; (type_to_eq_fn tp1); (type_to_eq_fn tp2)]
  | tApp
         (tInd {| inductive_mind :=
           (MPfile ["AnimationResult"; "Animation"],
            "ind_tp");
           inductive_ind := 0 |} [])
         [tp] => tApp <%eqb_ind_tp%> [tp; type_to_eq_fn tp]
  | _ => <% (false) %>
  end.

(** Check whether a type (global) has a supported boolean equality function.
    Returns [true] for all types handled by [type_to_eq_fn]. *)
Fixpoint has_eq_fn (t : global_term) : bool :=
  match t with
  | <%nat%> => true
  | <%bool%> => true
  | tInd
         {|
           inductive_mind := (MPdot (MPfile ["bytestring"; "Utils"; "MetaRocq"]) "String", "t");
           inductive_ind := 0
         |} [] => true
  | tInd {| inductive_mind := (_defLoc, _str); inductive_ind := _j |} [] => true
  | tApp <%list%> [tp] => has_eq_fn tp
  | tApp <%prod%> [tp1 ; tp2] => andb (has_eq_fn tp1) (has_eq_fn tp2)
  | tApp
         (tInd {| inductive_mind :=
           (MPfile ["AnimationResult"; "Animation"],
            "ind_tp");
           inductive_ind := 0 |} [])
         [tp] => has_eq_fn tp
  | _ => true
  end.

(** Flatten a conjunction (named) into a list of equality conjuncts (named)
    that will generate let-bindings. *)
Fixpoint collect_let_conjs (big_conj : named_term) : list named_term :=
  match big_conj with
  | tApp <%and%> ls => concat (map collect_let_conjs ls)
  | tApp <%eq%> [_; _; _] => [big_conj]
  | _ => []
  end.

(** Extract the inductive name and argument list from a named term that is either
    a quoted [tInd] application or a [tVar] application; returns [None] otherwise. *)
Definition get_ind_name (conjunct : named_term) : option (string * list named_term) :=
  match conjunct with
  | tApp (tInd {| inductive_mind := (_path, ind_nm);
                  inductive_ind := 0 |} [])
         lstArgs => Some (ind_nm, lstArgs)
  | tApp (tVar ind_nm) lstArgs => Some (ind_nm, lstArgs)
  | _ => None
  end.

(** Flatten a conjunction (named) into a list of guard conjuncts (named):
    equalities and inductive predicate applications (used for boolean guard generation). *)
Fixpoint collect_guard_conjs (big_conj : named_term) : list named_term :=
  match big_conj with
  | tApp <%and%> ls => concat (map collect_guard_conjs ls)
  | tApp <%eq%> [_; _; _] => [big_conj]
  | _ => match get_ind_name big_conj with
         | Some _ => [big_conj]
         | None => []
         end
  end.

(** Alias for [collect_guard_conjs]: extract all conjuncts (equalities and predicates). *)
Definition collect_all_conjs := collect_guard_conjs.

(** For each conjunct in [big_conj] (named), return whether its equality type is supported
    by [has_eq_fn] (used to decide if the whole clause can be animated). *)
Fixpoint classify_conj_types (big_conj : named_term) : list bool :=
  match big_conj with
  | tApp <%and%> ls => concat (map classify_conj_types ls)
  | tApp <%eq%> [typeT; _; _] => [has_eq_fn typeT]
  | _ => [false]
  end.

(** Extract variable names from a named term in the order they appear,
    with the equation's LHS variables listed before RHS variables. *)
Fixpoint ordered_vars (t : named_term) : list string :=
  match t with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => [str1 ; str2]
  | tApp <%eq%> [typeT; tVar str1; tApp fn lst] =>
    str1 :: (ordered_vars fn ++ concat (map ordered_vars lst))
  | tApp <%eq%> [typeT; tApp fn lst; tVar str1] =>
    ordered_vars fn ++ concat (map ordered_vars lst) ++ [str1]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] => [str1]
  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>  [str1]

  | tVar str  => [str]
  | tApp fn lst => ordered_vars fn ++ concat (map ordered_vars lst)
  | _ => []
  end.

(** Wrap one equality conjunct [conj] (named) into a [tLetIn], extending [partial_fn].
    Returns [Some f] if [conj] has a pattern we can orient, [None] otherwise. *)
Definition animate_conj_let (conj : named_term) (partial_fn : named_term -> named_term) : option (named_term -> named_term) :=
  match conj with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] =>
    Some (fun t => partial_fn
      ((tLetIn {| binder_name := nNamed str1;
                  binder_relevance := Relevant |}
               (tVar str2) typeT) t))

  | tApp <%eq%> [typeT; tVar str1; tApp fn lstTerm] =>
    Some (fun t => partial_fn
      ((tLetIn {| binder_name := nNamed str1%bs;
                  binder_relevance := Relevant |}
               (tApp fn lstTerm) typeT) t))

  | tApp <%eq%> [typeT; tApp fn lstTerm; tVar str1] =>
    Some (fun t => partial_fn
      ((tLetIn {| binder_name := nNamed str1%bs;
                  binder_relevance := Relevant |}
               (tApp fn lstTerm) typeT) t))

  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>
    Some (fun t => partial_fn
      ((tLetIn {| binder_name := nNamed str1%bs;
                  binder_relevance := Relevant |}
               (tConstruct ind_type k lst) typeT) t))

  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] =>
    Some (fun t => partial_fn
      ((tLetIn {| binder_name := nNamed str1%bs;
                  binder_relevance := Relevant |}
               (tConstruct ind_type k lst) typeT) t))

  | _ => None
  end.

(** Swap the two sides of an equality conjunct (named) so the output variable is on the
    left, enabling [animate_conj_let] to orient it correctly. *)
Definition flip_conj (conj : named_term) : named_term :=
  match conj with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => tApp <%eq%> [typeT; tVar str2; tVar str1]
  | tApp <%eq%> [typeT; tApp fn lstTerm; tVar str1] =>
    tApp <%eq%> [typeT; tVar str1; tApp fn lstTerm]
  | tApp <%eq%> [typeT;
      tConstruct ind_type k lst; tVar str1] =>
    tApp <%eq%>
      [typeT; tVar str1; tConstruct ind_type k lst]
  | t' => t'
  end.

(** Extend a boolean guard [guard_acc] (named) with a boolean equality check for
    the equality conjunct [conj] (named), producing [guard_acc && eqFn t1 t2]. *)
Definition animate_conj_guard (conj : named_term) (guard_acc : named_term)  :  named_term :=
  match conj with
  | tApp <%eq%> [typeT; t1; t2] =>
    tApp (tConst <? andb ?> [])
         [ guard_acc
         ; tApp (type_to_eq_fn typeT) [t1
         ; t2]]

  | _ => <% false %>
  end.

(** Try to orient and animate a single equality conjunct (named) given the currently
    known variables [knownVar].  Returns the extended known-variable set and
    the updated partial program if successful, or [None] if deferred. *)
Definition animate_one_conj (conj : named_term)
  (knownVar : list string)
  (partialProg : named_term -> named_term)
  : option (list string * (named_term -> named_term)) :=
  match conj with
  | tApp <%eq%> [typeT; t1; t2] =>
    if andb (is_subset_strings (ordered_vars t2) knownVar)
            (negb (is_subset_strings
                     (ordered_vars t1) knownVar))
    then

    (let t' := animate_conj_let conj partialProg in
      match t' with
      | Some t'' => Some (app knownVar (ordered_vars conj), t'')
      | None => None
      end)
    else (if andb
      (is_subset_strings (ordered_vars t1) knownVar)
      (negb (is_subset_strings
               (ordered_vars t2) knownVar))
    then

          (let t' := animate_conj_let (flip_conj conj) partialProg in
           match t' with
            | Some t'' => Some (app knownVar (ordered_vars (flip_conj conj)), t'')
            | None => None
           end)
         else None)

  | _ => None
  end.

(** Repeatedly attempt to animate a list of equality conjuncts (named), deferring
    those whose variables are not yet known and retrying on each pass.
    [fuel] bounds the number of retry rounds. *)
Fixpoint animate_conj_list (conjs : (list named_term)) (rem_conjs : (list named_term)) (knownVar : list string)
                         (fuel : nat) (partialProg : named_term -> named_term) : named_term -> named_term :=
  match fuel with
  | 0 => partialProg
  | S n =>
    match conjs with
    | [] =>
      match rem_conjs with
      | [] => partialProg
      | lst => animate_conj_list lst nil knownVar n partialProg
      end
    | h :: t =>
      let res := animate_one_conj h knownVar partialProg in
      match res with
      | Some res' => animate_conj_list t rem_conjs (fst res') n (snd res')
      | None => animate_conj_list t (h :: rem_conjs) knownVar n partialProg
      end
    end
  end.

(** Build [Some out_tm] as the success branch of a generated case expression (global). *)
Definition build_return_body (out_tm : global_term) (out_tp : global_term) : global_term :=
 tApp <% @Some %> [out_tp; out_tm].

(** Construct the body of an animated clause function: wrap [out_tm] (global) in
    [let_bind] (named) and a [if true then Some out_tm else None] case expression.
    Returns a de Bruijn term (the case expression uses tRel internally). *)
Definition build_fn_body  (out_tm : global_term) (out_tp : global_term) (let_bind : named_term -> named_term)  : term :=
 (let_bind (tCase {| ci_ind := {| inductive_mind := <? bool ?>; inductive_ind := 0 |}
                ; ci_npar := 0; ci_relevance := Relevant |}
               {| puinst := []
                ; pparams := []
                ; pcontext := [{| binder_name := nAnon; binder_relevance := Relevant |}]
                ; preturn := tApp <% @option %> [out_tp]
                |}
                <%true %>
                [{| bcontext := []
                  ; bbody :=

                          (build_return_body out_tm out_tp)
                   |};
                   {| bcontext := []
                    ; bbody :=
                       tApp <% @None %> [out_tp]
                   |}])).

(** Like [build_fn_body] but with an explicit boolean guard term [guardCon] (named)
    instead of the let-binding wrapper.  Returns a de Bruijn term. *)
Definition build_guarded_body  (out_tm : global_term) (out_tp : global_term) (guardCon : named_term) : term :=
 ((tCase {| ci_ind := {| inductive_mind := <? bool ?>; inductive_ind := 0 |}
                ; ci_npar := 0; ci_relevance := Relevant |}
               {| puinst := []
                ; pparams := []
                ; pcontext := [{| binder_name := nAnon; binder_relevance := Relevant |}]
                ; preturn := tApp <% @option %> [out_tp]
                |}
                guardCon
                [{| bcontext := []
                  ; bbody :=

                          (build_return_body out_tm out_tp)
                   |};
                   {| bcontext := []
                    ; bbody :=
                       tApp <% @None %> [out_tp]
                   |}])).

(** Generate a boolean equality function for a type and define it in the environment.
    Type parameters are global terms; returns a de Bruijn term. *)
Definition compile_equality_clause {A : Type} (induct : A)
                      (post_in' : global_term) (post_in_tp' : global_term) (post_out' : global_term) (post_out_tp' : global_term)
                        (fuel : nat) : TemplateMonad term :=

let post_in := tApp <%Success%> [post_in_tp'; post_in'] in
let post_in_tp := tApp <%animation_result%> [post_in_tp'] in

let post_out := tApp <%Success%> [post_out_tp'; post_out'] in
let post_out_tp := tApp <%animation_result%> [post_out_tp'] in

tBody' <-  mk_pattern_match_fn (induct)
  ([(post_in, (post_out));
    ((tApp <%FuelError%> [post_in_tp']),
     (tApp <%FuelError%> [post_out_tp']))])
  post_in_tp post_out_tp
  (tApp <%NoMatch%> [post_out_tp']) fuel ;;

let u :=
 (tLam "fuel" <%nat%>
            (tCase
               {|
                 ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                 ci_npar := 0;
                 ci_relevance := Relevant
               |}
               {|
                 puinst := [];
                 pparams := [];
                 pcontext := [{| binder_name := nNamed "fuel"; binder_relevance := Relevant |}];
                 preturn :=
                   (tProd {| binder_name := nAnon;
                             binder_relevance := Relevant |}
                          post_in_tp post_out_tp)

               |} (tVar "fuel")
               [{|
                  bcontext := [];
                  bbody :=
                    (tApp <%fuel_error_fn%> [post_in_tp; post_out_tp'])
                |};
                {|
                  bcontext := [{| binder_name := nNamed "rem_fuel"; binder_relevance := Relevant |}];
                  bbody := tBody'

                              |}]
                     )) in

ret u.

(** Animate a single equality clause: animate the let-bindings in [foo_tm] (named)
    into a pattern-matching function from [in_tp] (global) to [option out_tp] (global).
    Fails with an error if any equality has an unsupported type.
    Returns a de Bruijn term. *)
Definition compile_let_clause {A : Type}
  (induct : A) (kn : kername)
  (foo_tm : named_term)
  (in_tm : global_term) (in_tp : global_term)
  (out_tm : global_term) (out_tp : global_term)
  (in_vars : list string) (fuel : nat)
  : TemplateMonad term :=

  if forallb id (classify_conj_types foo_tm) then
  (let post_out' := (build_fn_body out_tm out_tp
    (animate_conj_list
       (collect_let_conjs foo_tm) nil (in_vars) fuel (fun t : named_term => t))
     ) in

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
     | None => tmFail "de Bruijn conversion failed in compile_let_clause"
     end)
     else tmFail "no boolean equality over some type".

(** Compile a single clause of an inductive relation into executable code,
    resolving equality premises and generating pattern matching.
    Type parameters in [pred_types] and [var_env] are global terms.
    Returns a de Bruijn term. *)
Definition compile_clause {A : Type}
  (induct : A) (kn : kername)
  (conjunct' : tagged_conjunct)
  (modes : mode_map) (pred_types : pred_type_map)
  (var_env : list (string * global_term))
  (fuel : nat) : TemplateMonad term :=

out_tm <- tmEval all (tVar conjunct'.(tc_out_var)) ;;
out_tp <- tmEval all (conjunct'.(tc_out_type)) ;;
let conjunct := conjunct'.(tc_conjunct) in

  match get_ind_name conjunct with
  | Some (ind_nm, lstArgs) =>
                     (* Look up the mode and partition arguments into input/output *)
                     let mode := lookup_mode ind_nm modes in
                     let predTp := lookup_pred_type ind_nm pred_types in
                     let predInArgsTm := select_in_by_mode mode lstArgs in
                     let predInArgsTp := select_in_by_mode mode predTp in
                     let predOutArgsTm := select_out_by_mode mode lstArgs in
                     let predOutArgsTp := select_out_by_mode mode predTp in
                     let in_vars := ordered_vars_of_list predInArgsTm in
                     let inputVarsTmTp := pairs_to_terms (lookup_vars in_vars var_env) in
                     let predInArgs := combine predInArgsTm predInArgsTp in
                     let predOutArgs := combine predOutArgsTm predOutArgsTp in
                     (* Build product types/terms for input vars and predicate args *)
                     inputVarProdTp <- mk_lhs_type inputVarsTmTp ;;
                     inputVarProdTm <- mk_lhs_term inputVarsTmTp ;;
                      predOutProdTp <- mk_lhs_type predOutArgs ;;
                      predOutProdTm <- mk_lhs_term predOutArgs ;;
                      predInProdTp <- mk_lhs_type predInArgs ;;
                      predInProdTm <- mk_lhs_term predInArgs ;;
                      (* Build the input-side pattern match: maps user input to predicate input *)
                      tIn' <- join_pattern_fueled induct
                        (inputVarProdTm) (inputVarProdTp)
                        predInProdTm predInProdTp
                        (snd kn ++ "IN")
                        fuel ;;
                      (* Compose: user input -> pred input ->
                         pred output (via recursive call) *)
                      let tIn :=
                        (tApp <%compose_outcome%>
                          [(inputVarProdTp); predInProdTp;
                           (predOutProdTp); tIn';
                           (tVar (ind_nm ++ top_fn_suffix))]) in
                      (* Build the output-side pattern match:
                         maps predicate output to user output *)
                      tOut <- join_pattern_fueled induct
                        predOutProdTm predOutProdTp
                        (out_tm) (out_tp)
                        (snd kn ++ "OUT")
                        fuel ;;
                      (* Final composition:
                         user input -> pred output ->
                         user output *)
                      let u :=
                        (tApp <%compose_outcome%>
                          [(inputVarProdTp); predOutProdTp;
                           (out_tp); tIn; tOut]) in
                      u'' <- tmEval all u ;;
                      match DB.de_bruijn_option u with
                      | Some db_u =>
                        u' <- tmEval all db_u ;;
                        tmReturn u'
                      | None => tmFail "de Bruijn conversion failed"
                      end

  | None => tmFail "incorrect inductive shape"
  end.

(** Build the product type (de Bruijn) of a list of [(term, type)] pairs, using [bool] as
    the base case.  Used for the empty-input mode where there are no inputs. *)
Fixpoint mk_lhs_type_monadic (lhs_preds : list (term * term)) : TemplateMonad term :=
  match lhs_preds with
  | [] => tmReturn <%bool%>
  | [h] => tmReturn (snd h)
  | h :: t =>
      res <- mk_lhs_type_monadic t ;;
      tmReturn (tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; res])
  end.

(** Build the product term (de Bruijn) of a list of [(term, type)] pairs, using [true] as
    the base case.  Companion to [mk_lhs_type_monadic]. *)
Fixpoint mk_lhs_term_monadic (lhs_preds : list (term * term)) : TemplateMonad term :=
  match lhs_preds with
  | [] => tmReturn <%true%>
  | [h] => tmReturn (fst h)
  | h :: t =>
      res <- mk_lhs_term_monadic t ;;
      resT <- mk_lhs_type_monadic t ;;
      tmReturn (tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
                     [snd h; resT; fst h; res])
  end.

(** Compile a single relation clause whose predicate has no input arguments
    (empty-input mode), using [mk_lhs_type_monadic]/[mk_lhs_term_monadic] as the product
    builders so that the trivial [bool] base case is inserted correctly.
    Type parameters in [pred_types] and [var_env] are global terms.
    Returns a de Bruijn term. *)
Definition animate_no_input {A : Type}
  (induct : A) (kn : kername)
  (conjunct' : tagged_conjunct)
  (modes : mode_map) (pred_types : pred_type_map)
  (var_env : list (string * global_term))
  (fuel : nat) : TemplateMonad term :=

out_tm <- tmEval all (tVar conjunct'.(tc_out_var)) ;;
out_tp <- tmEval all (conjunct'.(tc_out_type)) ;;
let conjunct := conjunct'.(tc_conjunct) in

  match get_ind_name conjunct with
  | Some (ind_nm, lstArgs) =>
                     let mode := lookup_mode ind_nm modes in
                     let predTp := lookup_pred_type ind_nm pred_types in
                     let predInArgsTm := select_in_by_mode mode lstArgs in
                     let predInArgsTp := select_in_by_mode mode predTp in
                     let predOutArgsTm := select_out_by_mode mode lstArgs in
                     let predOutArgsTp := select_out_by_mode mode predTp in
                     let in_vars := ordered_vars_of_list predInArgsTm in
                     let inputVarsTmTp := pairs_to_terms (lookup_vars in_vars var_env) in
                     let predInArgs := combine predInArgsTm predInArgsTp in
                     let predOutArgs := combine predOutArgsTm predOutArgsTp in

                     inputVarProdTp <- mk_lhs_type_monadic inputVarsTmTp ;;
                     inputVarProdTm <- mk_lhs_term_monadic inputVarsTmTp ;;
                      predOutProdTp <- mk_lhs_type_monadic predOutArgs ;;
                      predOutProdTm <- mk_lhs_term_monadic predOutArgs ;;
                      predInProdTp <- mk_lhs_type_monadic predInArgs ;;
                      predInProdTm <- mk_lhs_term_monadic predInArgs ;;
                      tIn' <- join_pattern_fueled induct
                        (inputVarProdTm) (inputVarProdTp)
                        predInProdTm predInProdTp
                        (snd kn ++ "IN")
                        fuel ;;
                      let tIn :=
                        (tApp <%compose_outcome%>
                          [(inputVarProdTp); predInProdTp;
                           (predOutProdTp); tIn';
                           (tLam "fuel" <%nat%>
                             (tLam "input"
                               <%animation_result bool%>
                               (tApp
                                 (tVar (ind_nm ++ top_fn_suffix))
                                 [tVar "fuel"])))]) in
                      tOut <- join_pattern_fueled induct
                        predOutProdTm predOutProdTp
                        (out_tm) (out_tp)
                        (snd kn ++ "OUT")
                        fuel ;;
                      let u :=
                        (tApp <%compose_outcome%>
                          [(inputVarProdTp); predOutProdTp;
                           (out_tp); tIn; tOut]) in
                      u'' <- tmEval all u ;;
                      match DB.de_bruijn_option u with
                      | Some db_u =>
                        u' <- tmEval all db_u ;;
                        tmReturn u'
                      | None => tmFail "de Bruijn conversion failed"
                      end

  | None => tmFail "incorrect inductive shape"
  end.

