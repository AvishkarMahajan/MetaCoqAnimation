(** * EqualityResolution — Equality-Based Clause Animation

    Handles the equality-resolution phase of animation: decomposing
    conjunctions into let-bindings, orienting equations so that the
    output variable is on the left, generating boolean equality functions
    for supported types, and compiling individual relation clauses via
    [compile_clause].

    Depends on: [MetaRocqUtils], [PatternCompilation]. *)

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
  (eqFnA : A -> A -> bool) (eqFnB : B -> B -> bool)
  (p1 : prod A B) (p2 : prod A B) : bool :=
andb (eqFnA (fst p1) (fst p2)) (eqFnB (snd p1) (snd p2)).

(** Boolean equality on [ind_tp], the wrapper type for inductive values. *)
Definition eqb_ind_tp (A : Type) (eqFnA : A -> A -> bool) (a1 : ind_tp A) (a2 : ind_tp A) : bool :=
  match a1 with
  | indWrap a1' => match a2 with
                 | indWrap a2' => eqFnA a1' a2'
                 end
  end.
(** Prefix prepended to an inductive name to form its boolean equality function name. *)
Definition eq_fn_prefix : string := "eqFn".

(** Map a type term to its corresponding boolean equality function term.
    Handles [nat], [bool], [string], user-defined inductives, [list], [prod],
    and [ind_tp]; returns [false] (the trivially failing function) for unsupported types. *)
Fixpoint type_to_eq_fn (t : term) : term :=
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
    tConst (defLoc, (String.append eq_fn_prefix str)) []

  | tApp <%list%> [tp] => tApp <%@eqb_list%> [tp; (type_to_eq_fn tp)]
  | tApp <%prod%> [tp1 ; tp2] =>
    tApp <%eqb_prod%>
      [tp1; tp2; (type_to_eq_fn tp1); (type_to_eq_fn tp2)]
  | tApp
         (tInd {| inductive_mind :=
           (MPfile ["MetaRocqUtils"; "Animation"],
            "ind_tp");
           inductive_ind := 0 |} [])
         [tp] => tApp <%eqb_ind_tp%> [tp; type_to_eq_fn tp]
  | _ => <% (false) %>
  end.

(** Check whether a type has a supported boolean equality function.
    Returns [true] for all types handled by [type_to_eq_fn]. *)
Fixpoint has_eq_fn (t : term) : bool :=
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
           (MPfile ["MetaRocqUtils"; "Animation"],
            "ind_tp");
           inductive_ind := 0 |} [])
         [tp] => has_eq_fn tp
  | _ => true
  end.

(** Flatten a conjunction into a list, keeping only equality conjuncts
    (those that will generate let-bindings). *)
Fixpoint collect_let_conjs (bigConj : term) : list term :=
  match bigConj with
  | tApp <%and%> ls => concat (map collect_let_conjs ls)
  | tApp <%eq%> [_; _; _] => [bigConj]
  | _ => []
  end.

(** Extract the inductive name and argument list from a term that is either
    a quoted [tInd] application or a [tVar] application; returns [None] otherwise. *)
Definition get_ind_name (conjunct : term) : option (string * list term) :=
  match conjunct with
  | tApp (tInd {| inductive_mind := (_path, indNm);
                  inductive_ind := 0 |} [])
         lstArgs => Some (indNm, lstArgs)
  | tApp (tVar indNm) lstArgs => Some (indNm, lstArgs)
  | _ => None
  end.

(** Flatten a conjunction into a list of guard conjuncts: equalities and
    inductive predicate applications (used for boolean guard generation). *)
Fixpoint collect_guard_conjs (bigConj : term) : list term :=
  match bigConj with
  | tApp <%and%> ls => concat (map collect_guard_conjs ls)
  | tApp <%eq%> [_; _; _] => [bigConj]
  | _ => match get_ind_name bigConj with
         | Some _ => [bigConj]
         | None => []
         end
  end.

(** Alias for [collect_guard_conjs]: extract all conjuncts (equalities and predicates). *)
Definition collect_all_conjs := collect_guard_conjs.

(** For each conjunct in [bigConj], return whether its equality type is supported
    by [has_eq_fn] (used to decide if the whole clause can be animated). *)
Fixpoint classify_conj_types (bigConj : term) : list bool :=
  match bigConj with
  | tApp <%and%> ls => concat (map classify_conj_types ls)
  | tApp <%eq%> [typeT; _; _] => [has_eq_fn typeT]
  | _ => [false]
  end.

(** Extract variable names from a term in the order they appear,
    with the equation's LHS variables listed before RHS variables. *)
Fixpoint ordered_vars (t : term) : list string :=
  match t with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => [str1 ; str2]
  | tApp <%eq%> [typeT; tVar str1; tApp fn lst] =>
    str1 :: (app (ordered_vars fn)
                 (concat (map ordered_vars lst)))
  | tApp <%eq%> [typeT; tApp fn lst; tVar str1] =>
    app (app (ordered_vars fn)
             (concat (map ordered_vars lst))) [str1]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] => [str1]
  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>  [str1]

  | tVar str  => [str]
  | tApp fn lst => app (ordered_vars fn) (concat (map ordered_vars lst))
  | _ => []
  end.

(** Wrap one equality conjunct [conj] into a [tLetIn], extending [partialLetfn].
    Returns [Some f] if [conj] has a pattern we can orient, [None] otherwise. *)
Definition animate_conj_let (conj : term) (partialLetfn : term -> term) : option (term -> term) :=
  match conj with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] =>
    Some (fun t => partialLetfn
      ((tLetIn {| binder_name := nNamed str1;
                  binder_relevance := Relevant |}
               (tVar str2) typeT) t))

  | tApp <%eq%> [typeT; tVar str1; tApp fn lstTerm] =>
    Some (fun t => partialLetfn
      ((tLetIn {| binder_name := nNamed str1%bs;
                  binder_relevance := Relevant |}
               (tApp fn lstTerm) typeT) t))

  | tApp <%eq%> [typeT; tApp fn lstTerm; tVar str1] =>
    Some (fun t => partialLetfn
      ((tLetIn {| binder_name := nNamed str1%bs;
                  binder_relevance := Relevant |}
               (tApp fn lstTerm) typeT) t))

  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>
    Some (fun t => partialLetfn
      ((tLetIn {| binder_name := nNamed str1%bs;
                  binder_relevance := Relevant |}
               (tConstruct ind_type k lst) typeT) t))

  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] =>
    Some (fun t => partialLetfn
      ((tLetIn {| binder_name := nNamed str1%bs;
                  binder_relevance := Relevant |}
               (tConstruct ind_type k lst) typeT) t))

  | _ => None
  end.

(** Swap the two sides of an equality conjunct so the output variable is on the
    left, enabling [animate_conj_let] to orient it correctly. *)
Definition flip_conj (conj : term) : term :=
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

(** Extend a boolean guard [partialGuard] with a boolean equality check for
    the equality conjunct [conj], producing [partialGuard && eqFn t1 t2]. *)
Definition animate_conj_guard (conj : term) (partialGuard : term)  :  term :=
  match conj with
  | tApp <%eq%> [typeT; t1; t2] =>
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (type_to_eq_fn typeT) [t1
         ; t2]]

  | _ => <% false %>
  end.

(** Try to orient and animate a single equality conjunct given the currently
    known variables [knownVar].  Returns the extended known-variable set and
    the updated partial program if successful, or [None] if deferred. *)
Definition animate_one_conj (conj : term)
  (knownVar : list string)
  (partialProg : term -> term)
  : option (list string * (term -> term)) :=
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

(** Repeatedly attempt to animate a list of equality conjuncts, deferring
    those whose variables are not yet known and retrying on each pass.
    [fuel] bounds the number of retry rounds. *)
Fixpoint animate_conj_list (conjs : (list term)) (remConjs : (list term)) (knownVar : list string)
                         (fuel : nat) (partialProg : term -> term) : term -> term :=
  match fuel with
  | 0 => partialProg
  | S n =>
    match conjs with
    | [] =>
      match remConjs with
      | [] => partialProg
      | lst => animate_conj_list lst nil knownVar n partialProg
      end
    | h :: t =>
      let res := animate_one_conj h knownVar partialProg in
      match res with
      | Some res' => animate_conj_list t remConjs (fst res') n (snd res')
      | None => animate_conj_list t (h :: remConjs) knownVar n partialProg
      end
    end
  end.

(** Build [Some outputTm] as the success branch of a generated case expression. *)
Definition build_return_body (outputTm : term) (outputTp : term) : term :=
 tApp <% @Some %> [outputTp; outputTm].

(** Construct the body of an animated clause function: wrap [outputTm] in
    [letBind] and a [if true then Some outputTm else None] case expression.
    The case on [true] is a guard placeholder filled in by pattern compilation. *)
Definition build_fn_body  (outputTm : term) (outputTp : term) (letBind : term -> term)  : term :=
 (letBind (tCase {| ci_ind := {| inductive_mind := <? bool ?>; inductive_ind := 0 |}
                ; ci_npar := 0; ci_relevance := Relevant |}
               {| puinst := []
                ; pparams := []
                ; pcontext := [{| binder_name := nAnon; binder_relevance := Relevant |}]
                ; preturn := tApp <% @option %> [outputTp]
                |}
                <%true %>
                [{| bcontext := []
                  ; bbody :=

                          (build_return_body outputTm outputTp)
                   |};
                   {| bcontext := []
                    ; bbody :=
                       tApp <% @None %> [outputTp]
                   |}])).

(** Like [build_fn_body] but with an explicit boolean guard term [guardCon]
    instead of the let-binding wrapper. *)
Definition build_guarded_body  (outputTm : term) (outputTp : term) (guardCon : term) : term :=
 ((tCase {| ci_ind := {| inductive_mind := <? bool ?>; inductive_ind := 0 |}
                ; ci_npar := 0; ci_relevance := Relevant |}
               {| puinst := []
                ; pparams := []
                ; pcontext := [{| binder_name := nAnon; binder_relevance := Relevant |}]
                ; preturn := tApp <% @option %> [outputTp]
                |}
                guardCon
                [{| bcontext := []
                  ; bbody :=

                          (build_return_body outputTm outputTp)
                   |};
                   {| bcontext := []
                    ; bbody :=
                       tApp <% @None %> [outputTp]
                   |}])).

(** Generate a boolean equality function for a type and define it in the environment. *)
Definition compile_equality_clause {A : Type} (induct : A)
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term)
                        (fuel : nat) : TemplateMonad term :=

let postIn := tApp <%Success%> [postInType'; postIn'] in
let postInType := tApp <%animation_result%> [postInType'] in

let postOut := tApp <%Success%> [postOutType'; postOut'] in
let postOutType := tApp <%animation_result%> [postOutType'] in

tBody' <-  mk_pattern_match_fn (induct)
  ([(postIn, (postOut));
    ((tApp <%FuelError%> [postInType']),
     (tApp <%FuelError%> [postOutType']))])
  postInType postOutType
  (tApp <%NoMatch%> [postOutType']) fuel ;;

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
                          postInType postOutType)

               |} (tVar "fuel")
               [{|
                  bcontext := [];
                  bbody :=
                    (tApp <%fuel_error_fn%> [postInType; postOutType'])
                |};
                {|
                  bcontext := [{| binder_name := nNamed "remFuel"; binder_relevance := Relevant |}];
                  bbody := tBody'

                              |}]
                     )) in

ret u.

(** Animate a single equality clause: animate the let-bindings in [fooTerm]
    into a pattern-matching function from [inputTp] to [option outputTp].
    Fails with an error if any equality has an unsupported type. *)
Definition compile_let_clause {A : Type}
  (induct : A) (kn : kername)
  (fooTerm : named_term)
  (inputTm : term) (inputTp : term)
  (outputTm : term) (outputTp : term)
  (inputVars : list string) (fuel : nat)
  : TemplateMonad term :=

  if forallb id (classify_conj_types fooTerm) then
  (let postOut' := (build_fn_body outputTm outputTp
    (animate_conj_list
       (collect_let_conjs fooTerm) nil (inputVars) fuel (fun t : term => t))
     ) in

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
     tmReturn t')
     else tmFail "no boolean equality over some type".

(** Compile a single clause of an inductive relation into executable code,
    resolving equality premises and generating pattern matching. *)
Definition compile_clause {A : Type}
  (induct : A) (kn : kername)
  (conjunct' : (term * (string * term)))
  (modes : mode_map) (predTypeInf : pred_type_map)
  (allVarTpInf : list (string * term))
  (fuel : nat) : TemplateMonad term :=

outputTm <- tmEval all (tVar (fst (snd conjunct'))) ;;
outputTp <- tmEval all ((snd (snd conjunct'))) ;;
let conjunct := fst conjunct' in

  match get_ind_name conjunct with
  | Some (indNm, lstArgs) =>
                     (* Look up the mode and partition arguments into input/output *)
                     let mode := lookup_mode indNm modes in
                     let predTp := lookup_pred_type indNm predTypeInf in
                     let predInArgsTm := select_in_by_mode mode lstArgs in
                     let predInArgsTp := select_in_by_mode mode predTp in
                     let predOutArgsTm := select_out_by_mode mode lstArgs in
                     let predOutArgsTp := select_out_by_mode mode predTp in
                     let inputVars := ordered_vars_of_list predInArgsTm in
                     let inputVarsTmTp := pairs_to_terms (lookup_vars inputVars allVarTpInf) in
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
                        (String.append (snd kn) "IN")
                        fuel ;;
                      (* Compose: user input -> pred input ->
                         pred output (via recursive call) *)
                      let tIn :=
                        (tApp <%compose_outcome%>
                          [(inputVarProdTp); predInProdTp;
                           (predOutProdTp); tIn';
                           (tVar (String.append
                              indNm top_fn_suffix))]) in
                      (* Build the output-side pattern match:
                         maps predicate output to user output *)
                      tOut <- join_pattern_fueled induct
                        predOutProdTm predOutProdTp
                        (outputTm) (outputTp)
                        (String.append (snd kn) "OUT")
                        fuel ;;
                      (* Final composition:
                         user input -> pred output ->
                         user output *)
                      let u :=
                        (tApp <%compose_outcome%>
                          [(inputVarProdTp); predOutProdTp;
                           (outputTp); tIn; tOut]) in
                      u'' <- tmEval all u ;;
                      u' <- tmEval all (typeConstrPatMatch.unwrap_option (DB.de_bruijn_option u)) ;;
                      tmReturn u'

  | None => tmFail "incorrect inductive shape"
  end.

(** Build the product type of a list of [(term, type)] pairs, using [bool] as
    the base case.  Used for the empty-input mode where there are no inputs. *)
Fixpoint mk_lhs_type_monadic (lhsIndPre : list (term * term)) : TemplateMonad term :=
  match lhsIndPre with
  | [] => tmReturn <%bool%>
  | [h] => tmReturn (snd h)
  | h :: t =>
      res <- mk_lhs_type_monadic t ;;
      tmReturn (tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; res])
  end.

(** Build the product term of a list of [(term, type)] pairs, using [true] as
    the base case.  Companion to [mk_lhs_type_monadic]. *)
Fixpoint mk_lhs_term_monadic (lhsIndPre : list (term * term)) : TemplateMonad term :=
  match lhsIndPre with
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
    builders so that the trivial [bool] base case is inserted correctly. *)
Definition animate_no_input {A : Type}
  (induct : A) (kn : kername)
  (conjunct' : (term * (string * term)))
  (modes : mode_map) (predTypeInf : pred_type_map)
  (allVarTpInf : list (string * term))
  (fuel : nat) : TemplateMonad term :=

outputTm <- tmEval all (tVar (fst (snd conjunct'))) ;;
outputTp <- tmEval all ((snd (snd conjunct'))) ;;
let conjunct := fst conjunct' in

  match get_ind_name conjunct with
  | Some (indNm, lstArgs) =>
                     let mode := lookup_mode indNm modes in
                     let predTp := lookup_pred_type indNm predTypeInf in
                     let predInArgsTm := select_in_by_mode mode lstArgs in
                     let predInArgsTp := select_in_by_mode mode predTp in
                     let predOutArgsTm := select_out_by_mode mode lstArgs in
                     let predOutArgsTp := select_out_by_mode mode predTp in
                     let inputVars := ordered_vars_of_list predInArgsTm in
                     let inputVarsTmTp := pairs_to_terms (lookup_vars inputVars allVarTpInf) in
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
                        (String.append (snd kn) "IN")
                        fuel ;;
                      let tIn :=
                        (tApp <%compose_outcome%>
                          [(inputVarProdTp); predInProdTp;
                           (predOutProdTp); tIn';
                           (tLam "fuel" <%nat%>
                             (tLam "input"
                               <%animation_result bool%>
                               (tApp (tVar
                                 (String.append indNm
                                   top_fn_suffix))
                                 [tVar "fuel"])))]) in
                      tOut <- join_pattern_fueled induct
                        predOutProdTm predOutProdTp
                        (outputTm) (outputTp)
                        (String.append (snd kn) "OUT")
                        fuel ;;
                      let u :=
                        (tApp <%compose_outcome%>
                          [(inputVarProdTp); predOutProdTp;
                           (outputTp); tIn; tOut]) in
                      u'' <- tmEval all u ;;
                      u' <- tmEval all (typeConstrPatMatch.unwrap_option (DB.de_bruijn_option u)) ;;
                      tmReturn u'

  | None => tmFail "incorrect inductive shape"
  end.

