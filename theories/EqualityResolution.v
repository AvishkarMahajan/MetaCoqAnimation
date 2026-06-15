(** * EqualityResolution — Equality-Based Clause Animation

    Handles the equality-resolution phase of animation: decomposing
    conjunctions into let-bindings, orienting equations so that the
    output variable is on the left, generating boolean equality functions
    for supported types, and compiling individual relation clauses via
    [compileRelationClause].

    Depends on: [MetaRocqUtils], [PatternCompilation]. *)

Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.

Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.

Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.

(** Boolean equality on products, given equality functions for each component. *)
Definition eqb_prod (A : Type) (B : Type) (eqFnA : A -> A -> bool) (eqFnB : B -> B -> bool) (p1 : prod A B) (p2 : prod A B) : bool :=
andb (eqFnA (fst p1) (fst p2)) (eqFnB (snd p1) (snd p2)).

(** Boolean equality on [indTp], the wrapper type for inductive values. *)
Definition eqb_indTp (A : Type) (eqFnA : A -> A -> bool) (a1 : indTp A) (a2 : indTp A) : bool :=
match a1 with
| indWrap a1' => match a2 with
                 | indWrap a2' => eqFnA a1' a2'
                 end
end.
(** Prefix prepended to an inductive name to form its boolean equality function name. *)
Definition eqFnPrefix : string := "eqFn".

(** Map a type term to its corresponding boolean equality function term.
    Handles [nat], [bool], [string], user-defined inductives, [list], [prod],
    and [indTp]; returns [false] (the trivially failing function) for unsupported types. *)
Fixpoint typeToBoolEq (t : term) : term :=
 match t with
  | <%nat%> => <%Nat.eqb%>
  | <%bool%> => <%Bool.eqb%>
  | tInd
         {|
           inductive_mind := (MPdot (MPfile ["bytestring"; "Utils"; "MetaRocq"]) "String", "t");
           inductive_ind := 0
         |} [] => <%String.eqb%>
  | tInd {| inductive_mind := (defLoc, str); inductive_ind := _j |} [] => tConst (defLoc, (String.append eqFnPrefix str)) []

  | tApp <%list%> [tp] => tApp <%@eqb_list%> [tp; (typeToBoolEq tp)]
  | tApp <%prod%> [tp1 ; tp2] => tApp <%eqb_prod%> [tp1; tp2; (typeToBoolEq tp1); (typeToBoolEq tp2)]
  | tApp
         (tInd {| inductive_mind := (MPfile ["MetaRocqUtils"; "Animation"], "indTp"); inductive_ind := 0 |} [])
         [tp] => tApp <%eqb_indTp%> [tp; typeToBoolEq tp]
  | _ => <% (false) %>
 end.

(** Check whether a type has a supported boolean equality function.
    Returns [true] for all types handled by [typeToBoolEq]. *)
Fixpoint chkEqType (t : term) : bool :=
  match t with
  | <%nat%> => true
  | <%bool%> => true
  | tInd
         {|
           inductive_mind := (MPdot (MPfile ["bytestring"; "Utils"; "MetaRocq"]) "String", "t");
           inductive_ind := 0
         |} [] => true
  | tInd {| inductive_mind := (_defLoc, _str); inductive_ind := _j |} [] => true
  | tApp <%list%> [tp] => chkEqType tp
  | tApp <%prod%> [tp1 ; tp2] => andb (chkEqType tp1) (chkEqType tp2)
  | tApp
         (tInd {| inductive_mind := (MPfile ["MetaRocqUtils"; "Animation"], "indTp"); inductive_ind := 0 |} [])
         [tp] => chkEqType tp
  | _ => true
 end.

(** Flatten a conjunction into a list, keeping only equality conjuncts
    (those that will generate let-bindings). *)
Fixpoint getListConjLetBind (bigConj : term) : list term :=
  match bigConj with
  | tApp <%and%> ls => concat (map getListConjLetBind ls)
  | tApp <%eq%> [_; _; _] => [bigConj]
  | _ => []
  end.

(** Extract the inductive name and argument list from a term that is either
    a quoted [tInd] application or a [tVar] application; returns [None] otherwise. *)
Definition extractIndName (conjunct : term) : option (string * list term) :=
match conjunct with
 | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => Some (indNm, lstArgs)
 | tApp (tVar indNm) lstArgs => Some (indNm, lstArgs)
 | _ => None
end.

(** Flatten a conjunction into a list of guard conjuncts: equalities and
    inductive predicate applications (used for boolean guard generation). *)
Fixpoint getListConjGuardCon (bigConj : term) : list term :=
  match bigConj with
  | tApp <%and%> ls => concat (map getListConjGuardCon ls)
  | tApp <%eq%> [_; _; _] => [bigConj]
  | _ => match extractIndName bigConj with
         | Some _ => [bigConj]
         | None => []
         end
  end.

(** Alias for [getListConjGuardCon]: extract all conjuncts (equalities and predicates). *)
Definition getListConjAll := getListConjGuardCon.

(** For each conjunct in [bigConj], return whether its equality type is supported
    by [chkEqType] (used to decide if the whole clause can be animated). *)
Fixpoint filterListConj (bigConj : term) : list bool :=
 match bigConj with
  | tApp <%and%> ls => concat (map filterListConj ls)
  | tApp <%eq%> [typeT; _; _] => [chkEqType typeT]
  | _ => [false]
 end.

(** Extract variable names from a term in the order they appear,
    with the equation's LHS variables listed before RHS variables. *)
Fixpoint extractOrderedVars (t : term) : list string :=
  match t with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => [str1 ; str2]
  | tApp <%eq%> [typeT; tVar str1; tApp fn lst] => str1 :: (app (extractOrderedVars fn) (concat (map extractOrderedVars lst)))
  | tApp <%eq%> [typeT; tApp fn lst; tVar str1] => app (app (extractOrderedVars fn) (concat (map extractOrderedVars lst))) [str1]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] => [str1]
  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>  [str1]

  | tVar str  => [str]
  | tApp fn lst => app (extractOrderedVars fn) (concat (map extractOrderedVars lst))
  | _ => []
  end.

(** Wrap one equality conjunct [conj] into a [tLetIn], extending [partialLetfn].
    Returns [Some f] if [conj] has a pattern we can orient, [None] otherwise. *)
Definition animateOneConjSucc (conj : term) (partialLetfn : term -> term) : option (term -> term) :=
  match conj with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1; binder_relevance := Relevant |}
                                 (tVar str2) typeT) t))

  | tApp <%eq%> [typeT; tVar str1; tApp fn lstTerm] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn lstTerm) typeT) t))

  | tApp <%eq%> [typeT; tApp fn lstTerm; tVar str1] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn lstTerm) typeT) t))

  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tConstruct ind_type k lst) typeT) t))

  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tConstruct ind_type k lst) typeT) t))

  | _ => None
 end.

(** Swap the two sides of an equality conjunct so the output variable is on the
    left, enabling [animateOneConjSucc] to orient it correctly. *)
Definition flipConj (conj : term) : term :=
 match conj with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => tApp <%eq%> [typeT; tVar str2; tVar str1]
  | tApp <%eq%> [typeT; tApp fn lstTerm; tVar str1] => tApp <%eq%> [typeT; tVar str1; tApp fn lstTerm]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] => tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst]
  | t' => t'
 end.

(** Extend a boolean guard [partialGuard] with a boolean equality check for
    the equality conjunct [conj], producing [partialGuard && eqFn t1 t2]. *)
Definition animateOneConjSuccGuard (conj : term) (partialGuard : term)  :  term :=
  match conj with
  | tApp <%eq%> [typeT; t1; t2] =>
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (typeToBoolEq typeT) [t1
         ; t2]]

  | _ => <% false %>
  end.

(** Try to orient and animate a single equality conjunct given the currently
    known variables [knownVar].  Returns the extended known-variable set and
    the updated partial program if successful, or [None] if deferred. *)
Definition animateOneConj (conj : term) (knownVar : list string) (partialProg : term -> term) : option (list string * (term -> term)) :=
 match conj with
  | tApp <%eq%> [typeT; t1; t2] => if andb (isListSubStr (extractOrderedVars t2 ) knownVar) (negb (isListSubStr (extractOrderedVars t1 ) knownVar)) then

    (let t' := animateOneConjSucc conj partialProg in
      match t' with
      | Some t'' => Some (app knownVar (extractOrderedVars conj), t'')
      | None => None
      end)
    else (if andb (isListSubStr (extractOrderedVars t1 ) knownVar) (negb (isListSubStr (extractOrderedVars t2 ) knownVar)) then

          (let t' := animateOneConjSucc (flipConj conj) partialProg in
           match t' with
            | Some t'' => Some (app knownVar (extractOrderedVars (flipConj conj)), t'')
            | None => None
           end)
         else None)

  | _ => None
 end.

(** Repeatedly attempt to animate a list of equality conjuncts, deferring
    those whose variables are not yet known and retrying on each pass.
    [fuel] bounds the number of retry rounds. *)
Fixpoint animateListConj (conjs : (list term)) (remConjs : (list term)) (knownVar : list string)
                         (fuel : nat) (partialProg : term -> term) : term -> term :=
  match fuel with
  | 0 => partialProg
  | S n =>
    match conjs with
    | [] =>
      match remConjs with
      | [] => partialProg
      | lst => animateListConj lst nil knownVar n partialProg
      end
    | h :: t =>
      let res := animateOneConj h knownVar partialProg in
      match res with
      | Some res' => animateListConj t remConjs (fst res') n (snd res')
      | None => animateListConj t (h :: remConjs) knownVar n partialProg
      end
    end
  end.

(** Build [Some outputTm] as the success branch of a generated case expression. *)
Definition constrRetBodylst (outputTm : term) (outputTp : term) : term :=
 tApp <% @Some %> [outputTp; outputTm].

(** Construct the body of an animated clause function: wrap [outputTm] in
    [letBind] and a [if true then Some outputTm else None] case expression.
    The case on [true] is a guard placeholder filled in by pattern compilation. *)
Definition constrFnBody  (outputTm : term) (outputTp : term) (letBind : term -> term)  : term :=
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

                          (constrRetBodylst outputTm outputTp)
                   |};
                   {| bcontext := []
                    ; bbody :=
                       tApp <% @None %> [outputTp]
                   |}])).

(** Like [constrFnBody] but with an explicit boolean guard term [guardCon]
    instead of the let-binding wrapper. *)
Definition constrFnBodyGuardCon  (outputTm : term) (outputTp : term) (guardCon : term) : term :=
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

                          (constrRetBodylst outputTm outputTp)
                   |};
                   {| bcontext := []
                    ; bbody :=
                       tApp <% @None %> [outputTp]
                   |}])).

(** Generate a boolean equality function for a type and define it in the environment. *)
Definition constrFunAnimateEq {A : Type} (induct : A)
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term)
                        (fuel : nat) : TemplateMonad term :=

let postIn := tApp <%Success%> [postInType'; postIn'] in
let postInType := tApp <%AnimationResult%> [postInType'] in

let postOut := tApp <%Success%> [postOutType'; postOut'] in
let postOutType := tApp <%AnimationResult%> [postOutType'] in

tBody' <-  mkMulPatMatFn (induct) ([(postIn, (postOut)); ((tApp <%FuelError%> [postInType']),(tApp <%FuelError%> [postOutType'])) ]) postInType postOutType (tApp <%NoMatch%> [postOutType']) fuel ;;

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
                 preturn := (tProd {| binder_name := nAnon; binder_relevance := Relevant |} postInType postOutType)

               |} (tVar "fuel")
               [{|
                  bcontext := [];
                  bbody :=
                    (tApp <%fuelErrorPolyCstFn%> [postInType; postOutType'])
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
Definition genFunAnimateEqPartialLetClause' {A : Type} (induct : A) (kn : kername) (fooTerm : named_term)  (inputTm : term) (inputTp : term)  (outputTm : term) (outputTp : term) (inputVars : list string) (fuel : nat) : TemplateMonad term :=

  if checkBool (filterListConj fooTerm) then
  (let postOut' := (constrFnBody outputTm outputTp
    (animateListConj
       (getListConjLetBind fooTerm) nil (inputVars) fuel (fun t : term => t))
     ) in

    let postOutType' := tApp <% @option %> [outputTp] in

    let postInType' := inputTp in

    let postIn' := inputTm in

    let postIn := tApp <%Success%> [postInType'; postIn'] in
    let postInType := tApp <%AnimationResult%> [postInType'] in

    let postOut := tApp <%Success%> [postOutType'; postOut'] in
    let postOutType := tApp <%AnimationResult%> [postOutType'] in

     t0 <- constrFunAnimateEq induct postIn' postInType' postOut' postOutType'  fuel ;;

     let t1 := (tApp <%optionToOutcome%> [postInType'; outputTp; t0]) in
     t' <- tmEval all (typeConstrPatMatch.unwrapOptionTerm (DB.deBruijnOption t1)) ;;
     tmReturn t')
     else tmFail "no boolean equality over some type".

(** Compile a single clause of an inductive relation into executable code,
    resolving equality premises and generating pattern matching. *)
Definition compileRelationClause {A : Type} (induct : A) (kn : kername) (conjunct' : (term * (string * term))) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad term :=

outputTm <- tmEval all (tVar (fst (snd conjunct'))) ;;
outputTp <- tmEval all ((snd (snd conjunct'))) ;;
let conjunct := fst conjunct' in

match extractIndName conjunct with
 | Some (indNm, lstArgs) =>
                     let mode := getModeFmLst indNm modes in
                     let predTp := getPredTp indNm predTypeInf in
                     let predInArgsTm := getInArgs' mode lstArgs in
                     let predInArgsTp := getInArgs' mode predTp in
                     let predOutArgsTm := getOutArgs' mode lstArgs in
                     let predOutArgsTp := getOutArgs' mode predTp in
                     let inputVars := extractOrderedVarsfmLst predInArgsTm in
                     let inputVarsTmTp := mkLstTm (lookUpVars inputVars allVarTpInf) in
                     let predInArgs := crossList predInArgsTm predInArgsTp in
                     let predOutArgs := crossList predOutArgsTm predOutArgsTp in

                     inputVarProdTp <- mklhsProdType inputVarsTmTp ;;
                     inputVarProdTm <- mklhsProdTm inputVarsTmTp ;;
                      predOutProdTp <- mklhsProdType predOutArgs ;;
                      predOutProdTm <- mklhsProdTm predOutArgs ;;
                      predInProdTp <- mklhsProdType predInArgs ;;
                      predInProdTm <- mklhsProdTm predInArgs ;;
                      tIn' <- joinPatMatPolyGenFuelAwareNoLHSTm induct (inputVarProdTm) (inputVarProdTp) predInProdTm predInProdTp (String.append (snd kn) "IN") fuel ;;
                      let tIn := (tApp <%composeOutcomePoly%> [(inputVarProdTp); predInProdTp ; (predOutProdTp) ; tIn' ; (tVar (String.append indNm animatedTopFnSuffix))]) in
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct predOutProdTm predOutProdTp (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;
                      let u := (tApp <%composeOutcomePoly%> [(inputVarProdTp); predOutProdTp ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      u' <- tmEval all (typeConstrPatMatch.unwrapOptionTerm (DB.deBruijnOption u)) ;;
                      tmReturn u'

 | None => tmFail "incorrect inductive shape"
 end.

(** Build the product type of a list of [(term, type)] pairs, using [bool] as
    the base case.  Used for the empty-input mode where there are no inputs. *)
Fixpoint mklhsProdType2 (lhsIndPre : list (term * term)) : TemplateMonad term :=
  match lhsIndPre with
  | [] => tmReturn <%bool%>
  | [h] => tmReturn (snd h)
  | h :: t =>
      res <- mklhsProdType2 t ;;
      tmReturn (tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; res])
  end.

(** Build the product term of a list of [(term, type)] pairs, using [true] as
    the base case.  Companion to [mklhsProdType2]. *)
Fixpoint mklhsProdTm2 (lhsIndPre : list (term * term)) : TemplateMonad term :=
  match lhsIndPre with
  | [] => tmReturn <%true%>
  | [h] => tmReturn (fst h)
  | h :: t =>
      res <- mklhsProdTm2 t ;;
      resT <- mklhsProdType2 t ;;
      tmReturn (tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
                     [snd h; resT; fst h; res])
  end.

(** Compile a single relation clause whose predicate has no input arguments
    (empty-input mode), using [mklhsProdType2]/[mklhsProdTm2] as the product
    builders so that the trivial [bool] base case is inserted correctly. *)
Definition animatePredicateEmptyIn {A : Type} (induct : A) (kn : kername) (conjunct' : (term * (string * term))) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad term :=

outputTm <- tmEval all (tVar (fst (snd conjunct'))) ;;
outputTp <- tmEval all ((snd (snd conjunct'))) ;;
let conjunct := fst conjunct' in

match extractIndName conjunct with
 | Some (indNm, lstArgs) =>
                     let mode := getModeFmLst indNm modes in
                     let predTp := getPredTp indNm predTypeInf in
                     let predInArgsTm := getInArgs' mode lstArgs in
                     let predInArgsTp := getInArgs' mode predTp in
                     let predOutArgsTm := getOutArgs' mode lstArgs in
                     let predOutArgsTp := getOutArgs' mode predTp in
                     let inputVars := extractOrderedVarsfmLst predInArgsTm in
                     let inputVarsTmTp := mkLstTm (lookUpVars inputVars allVarTpInf) in
                     let predInArgs := crossList predInArgsTm predInArgsTp in
                     let predOutArgs := crossList predOutArgsTm predOutArgsTp in

                     inputVarProdTp <- mklhsProdType2 inputVarsTmTp ;;
                     inputVarProdTm <- mklhsProdTm2 inputVarsTmTp ;;
                      predOutProdTp <- mklhsProdType2 predOutArgs ;;
                      predOutProdTm <- mklhsProdTm2 predOutArgs ;;
                      predInProdTp <- mklhsProdType2 predInArgs ;;
                      predInProdTm <- mklhsProdTm2 predInArgs ;;
                      tIn' <- joinPatMatPolyGenFuelAwareNoLHSTm induct (inputVarProdTm) (inputVarProdTp) predInProdTm predInProdTp (String.append (snd kn) "IN") fuel ;;
                      let tIn := (tApp <%composeOutcomePoly%> [(inputVarProdTp); predInProdTp ; (predOutProdTp) ; tIn' ; (tLam "fuel" <%nat%> (tLam "input" <%AnimationResult bool%> (tApp (tVar (String.append indNm animatedTopFnSuffix))[tVar "fuel"])))]) in
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct predOutProdTm predOutProdTp (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;
                      let u := (tApp <%composeOutcomePoly%> [(inputVarProdTp); predOutProdTp ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      u' <- tmEval all (typeConstrPatMatch.unwrapOptionTerm (DB.deBruijnOption u)) ;;
                      tmReturn u'

 | None => tmFail "incorrect inductive shape"
 end.

