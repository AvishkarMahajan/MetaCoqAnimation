(** * Animation Modules for MetaRocq
    This module provides tools for animating inductive predicates and
    generating executable functions from relational specifications. *)

From Stdlib Require Import List PeanoNat.

Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.

Require Import Animation.utils.
Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.

(** ** Module Path Notations
    Convenient notations for referring to standard library types. *)

Notation "<?and?>" := (MPfile ["Logic"; "Init"; "Corelib"], "and").
Notation "<?eq?>" := (MPfile ["Logic"; "Init"; "Corelib"], "eq").
Notation "<?nat?>" := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat").
Notation "<?list?>" := (MPfile ["Datatypes"; "Init"; "Corelib"], "list").
Notation "<?prod?>" := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod").
Notation "<?option?>" := (MPfile ["Datatypes"; "Init"; "Corelib"], "option").
Notation "<?bool?>" := (MPfile ["Datatypes"; "Init"; "Corelib"], "bool").

(** ** Inductive Type Notations
    Term-level representations of inductive types for meta-programming. *)

Notation "<%and%>" := (tInd {| inductive_mind := <?and?>; inductive_ind := 0 |} []).
Notation "<%eq%>" := (tInd {| inductive_mind := <?eq?>; inductive_ind := 0 |} []).
Notation "<%nat%>" := (tInd {| inductive_mind := <?nat?>; inductive_ind := 0 |} []).
Notation "<%list%>" := (tInd {| inductive_mind := <?list?>; inductive_ind := 0 |} []).
Notation "<%prod%>" := (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} []).
Notation "<%option%>" := (tInd {| inductive_mind := <?option?>; inductive_ind := 0 |} []).
Notation "<%bool%>" := (tInd {| inductive_mind := <?bool?>; inductive_ind := 0 |} []).

(** ** Outcome Type
    Represents the result of an animated function:
    - [fuelErrorPoly]: computation ran out of fuel
    - [successPoly]: successful computation with result
    - [noMatchPoly]: no pattern matched the input *)

Inductive outcomePoly (A : Type) : Type :=
| fuelErrorPoly : outcomePoly A
| successPoly : A -> outcomePoly A
| noMatchPoly : outcomePoly A.

(** ** Type Constructor Pattern Match Module
    This module contains utilities for extracting and manipulating
    pattern match data from inductive type declarations. *)

Module typeConstrPatMatch.

(** Extract the inductive declaration from a global declaration. *)
Definition extractIndDecl (x : global_decl) : option mutual_inductive_body :=
  match x with
  | InductiveDecl y => Some y
  | _ => None
  end.

(** Error values for partial functions. *)
Parameter error : kername * global_decl.
Parameter error2 : one_inductive_body.
Parameter error3 : constructor_body.
Parameter error4 : context_decl.
Parameter termErr : term.

(** Extract all inductive type declarations from a program. *)
Definition extractTypeData (p : program) : list (option mutual_inductive_body) :=
  map extractIndDecl ((map snd ((((declarations (fst p))))))).

(** Extract pattern match data from the first constructor of the first inductive in a program. *)
Definition extractPatMatData (p : program) : term :=
  let r :=
    option_map decl_type
      (option_map (hd error4)
         (option_map cstr_args
            (option_map (hd error3)
               (option_map ind_ctors
                  (option_map (hd error2)
                     (option_map ind_bodies
                        (extractIndDecl (snd (hd error (declarations (fst p))))))))))) in
     match r with
     | Some x => x
     | None => termErr
     end.

(** Generate a fresh variable name of the form "vN" where N is a number. *)
Definition genVar (n : nat) : string :=
  String.append "v" (string_of_nat (n)).

(** Generate a list of fresh variables paired with terms, starting from index s. *)
Fixpoint genVarlst (s : nat) (ls : list term) : list (string * term) :=
  match ls with
  | [] => []
  | h :: t => (genVar (s + 1), h) :: genVarlst (s + 1) t
  end.

(** Unfold one step of constructor applications in pattern matching.
    Takes an index counter, current terms to process, resolved terms, and remaining terms.
    Returns updated counter, unprocessed terms, resolved terms, and new remaining terms. *)
Definition unfoldConsStep
  (i : nat)
  (currTs : list (string * term))
  (resolvedTs : list ((string * term) * list string))
  (remTs : list (string * term))
  : (((nat *  list (string * term)) *
      list ((string * term) * list string)) * list (string * term)) :=
 match currTs with
 | [] => (i, remTs, resolvedTs, nil)
 | (str, tApp (tConstruct typeInfo cstrInd ls') args) :: t =>
     (i + (length args), t, (str, (tConstruct typeInfo cstrInd ls'), map fst (genVarlst i args)) :: resolvedTs, (app (genVarlst i args)  remTs))
 | (str, tRel k) :: t =>
     (i, t, (str, (tRel k), nil) :: resolvedTs, remTs)
 | (str, tVar varStr) :: t =>
     (i, t, (str, (tVar varStr ), nil) :: resolvedTs, remTs)
 (*| (str, (tApp (tInd indType ls') args)) :: t =>
     (i + (length args), t, ((str, (tInd indType ls'), (map fst (genVarlst i args))) :: resolvedTs), (app (genVarlst i args) remTs)) *)
 | (str, tConstruct typeInfo k []) :: t =>
     (i, t, (str, (tConstruct typeInfo k []), nil) :: resolvedTs, remTs)
 | (str, tApp <%eq%> args) :: t =>
     (i + length args, t, (str, <%eq%>, map fst (genVarlst i args)) :: resolvedTs, app (genVarlst i args) remTs) 

 | (str, tApp func args) :: t =>
     (i, t, (str, tApp func args, nil) :: resolvedTs, remTs)

 | (str, tInd indType ls') :: t =>
     (i, t, (str, tInd indType ls', nil) :: resolvedTs, remTs)
 | (str, _) :: t =>
     (i, t, resolvedTs, remTs)
 end.

(** Iterate the constructor unfolding step for a given amount of fuel.
    Processes terms by repeatedly applying unfoldConsStep. *)
Fixpoint unfoldConsStepIter
  (fuel : nat)
  (st : (((nat *  list (string * term)) *
            list ((string * term) * list string)) * list (string * term)))
  : (((nat *  list (string * term)) * list ((string * term) * list string)) * list (string * term)) :=
  match fuel with
  | 0 => st
  | S m => unfoldConsStepIter m
             (unfoldConsStep
                (fst (fst (fst st))) (snd (fst (fst st))) (snd (fst st)) (snd st))
  end.

(** Pre-process a constructor term by unfolding it into a list of variable-term pairs. *)
Definition preProcCons (fuel : nat) (t : term) : list ((string * term) * list string) :=
  rev (snd (fst (unfoldConsStepIter fuel (0, [("x"%bs, t)], [], [])))).

(** Reduce a natural number by 2 if possible. *)
Definition reduce2 (x : nat) : option nat :=
  match x with
  | S (S n) => Some n
  | _ => None
  end.

(** Check if all terms have been processed (no remaining terms). *)
Definition preProcConsRem (fuel : nat) (t : term) : bool :=
  let r := app (snd (unfoldConsStepIter fuel (0, [("x"%bs, t)], [], [])))
               (snd (fst (fst (unfoldConsStepIter fuel (0, [("x"%bs, t)], [], []))))) in
  match r with
  | [] => true
  | _ => false
  end.

(** Look up a single variable name in a list of resolved terms.
    Returns matching variable names and associated type terms. *)
Fixpoint lookUpVarsOne
  (str : string)
  (ls : list ((string * term) * list string))
  : list string * list term :=
  match ls with
  | [] => ([], [])
  | (h :: t) =>
      if String.eqb str (fst (fst h))
      then (let t := snd (fst h) in
            match t with
            | tConstruct typeInfo k js => ([str], [])
            | tApp (tInd typeInfo js) args => ([], [tApp (tInd typeInfo js) args])
            | tRel k => ([str], [])
            | tVar str'' => ([str], [])
            | tInd typeInfo js => ([], [(tInd typeInfo js)])
            | _ => ([], [])
            end)
      else lookUpVarsOne str t
  end.

(** Look up multiple variable names and collect their associated data. *)
Fixpoint lookUpVars
  (lsStr : list string)
  (ls : list ((string * term) * list string))
  : list string * list term :=
  match lsStr with
  | [] => ([], [])
  | (h :: t) =>
      match lookUpVarsOne h ls with
      | ([], []) => lookUpVars t ls
      | ([e], []) => (e :: (fst (lookUpVars t ls)), snd (lookUpVars t ls))
      | ([], [e]) => (fst (lookUpVars t ls),  e :: (snd (lookUpVars t ls)))
      | _ => lookUpVars t ls
      end
  end.

(** Pre-process constructor type variables, extracting relevant type information.
    Filters out equality constructors and enriches type constructor data. *)
Fixpoint preProcConsTypeVar
  (ls : list ((string * term) * list string))
  (ls' : list ((string * term) * list string))
  : list (((string * term) * list string) * list term) :=
  match ls' with
  | [] => []
  | (str1, <%eq%>, lstStr) :: t => preProcConsTypeVar ls t
  | (str1, (tConstruct typeInfo k js), lstStr) :: t =>
    (str1, (tConstruct typeInfo k js), fst (lookUpVars lstStr ls), snd (lookUpVars lstStr ls)) :: preProcConsTypeVar ls t
  | (_ :: t) => preProcConsTypeVar ls t
  end.

(** Generate a list of binder annotations with names of the form "nN". *)
Fixpoint genBinderNameList (n : nat) : list (binder_annot name) :=
 match n with
  | 0 => []
  | S m => {| binder_name := nNamed (String.append "n" (string_of_nat (S m))) ; binder_relevance := Relevant |} :: genBinderNameList m
 end.

(** Convert a list of string names into binder annotations. *)
Fixpoint genBinNmLsStr (ls : list string) : list (binder_annot name) :=
 match ls with
  | [] => []
  | h :: t => {| binder_name := nNamed h ; binder_relevance := Relevant |} :: genBinNmLsStr t
 end.



(** Create a branch with None as the body, used for non-matching constructor cases. *)
Definition mkNoneBr (cstrArity : nat) (noneVal : term) : branch term :=
  {| bcontext := genBinderNameList cstrArity
   ; bbody := noneVal
   |}.

(** Get the declaration name at a given De Bruijn index in a context. *)
Definition getDeclName (i : nat) (cxt : list context_decl) : option (binder_annot name) :=
  match nth_error cxt (i + 1) with
  | Some r => Some (decl_name r)
  | _ => None
  end.

(** Generate binder annotations from a list of De Bruijn indices and a context. *)
Fixpoint genBinderannot (ind : list term) (cxt : list context_decl) : option (list (binder_annot name)) :=
  match ind with
  | [] => Some ([])
  | tRel j :: t =>
      match getDeclName j cxt , genBinderannot t cxt with
      | Some b , Some bs => Some (b :: bs)
      | _ , _ => None
      end
  | _ => None
  end.

(** Extract the constructor arity information from an inductive body. *)
Definition getcsAr (o : one_inductive_body) : string * list nat :=
 (ind_name o, map cstr_arity (ind_ctors o)).

(** Extract constructor arities for all mutually inductive types. *)
Fixpoint extractTypeCsArlst (muts : list mutual_inductive_body) : list (string * list nat) :=
  match muts with
  | [] => []
  | h :: t => map getcsAr (ind_bodies h) ++ extractTypeCsArlst t
  end.

(** Error parameters for partial functions. *)
Parameter error_nat : nat.
Parameter errorInd : inductive.
Parameter errorStr : string.
Parameter errorlstNat : list nat.

(** Construct a term representing a list of nat variables. *)
Fixpoint retVarVals' (lst : list string) : term :=
  match lst with
  | [] =>  <% @nil nat %>
  | h :: rest => tApp <% @cons %> [<%nat%>; tVar h; retVarVals' rest]
  end.

(** Wrap a list of variables in Some constructor. *)
Definition retVarVals (lst : list string) : term :=
  tApp <% @Some %> [<% list nat %>; retVarVals' lst].

(** Sort binders by finding which variable maps to a given output variable. *)
Fixpoint sortBindersOne
  (outputVar : string)
  (lst': list ((string * term) * list string)) : list string :=
  match lst' with
  | [] => []
  | h :: rest =>
      match h with
      | (str1, (tVar y), _) =>
          if String.eqb y outputVar
          then [str1]
          else sortBindersOne outputVar rest
      | _ => sortBindersOne outputVar rest
      end
  end.

(** Sort all binders according to a list of output variables. *)
Definition sortBinders (outputVars : list string) (lst : list ((string * term) * list string)) : ((list string)) :=
  concat (map (fun x : string => sortBindersOne x lst) outputVars).
Compute (sortBinders ["a" ; "f"] ([("x", <%eq%>, ["v1"; "v2"; "v3"]);
        ("v6", tVar "a", [])])).

Compute (retVarVals ["v6"]).


(** Get the constructor index from a resolved term structure. *)
Definition getCstrIndex (s : ((string * term) * list string)) : nat :=
  match s with
   | (str, tConstruct typeInfo k ls, lsStr) => k
   | _ => error_nat
  end.

(** Get the inductive type from a resolved term structure. *)
Definition getType (s : ((string * term) * list string)) :=
  match s with
   | (str, tConstruct typeInfo k ls, lsStr) => typeInfo
   | _ => errorInd
  end.
Compute (getType (("x", <%eq%>, ["v1"; "v2"; "v3"]))).


(** Extract the type name from a constructor term. *)
Definition getTypeNm (s : (string * term) * list string) : string :=
 match s with
  | (str,
         tConstruct {| inductive_mind := (loc, nmStr); inductive_ind := j |}
           k ls, lsStr) => nmStr
  | _ => errorStr
 end.

(** Check if a string is a member of a list of strings. *)
Fixpoint chkMemberStr (s : string) (lStr : list string) : bool :=
 match lStr with
  | [] => false
  | (h :: t) => if (String.eqb s h) then true else chkMemberStr s t
 end.

(** Filter out terms that don't correspond to valid type constructors.
    Checks against the list of mutual inductive bodies. *)
Fixpoint filterTypeCon' (ls : list ((string * term) * list string)) (mut : list mutual_inductive_body) :
                         list ((string * term) * list string) :=
   match ls with
    | [] => []
    | h :: t => match h with
                 | (str,
                    tConstruct {| inductive_mind := (loc, nmStr); inductive_ind := j |}
                    k ls, lsStr) => if (chkMemberStr nmStr (map fst (extractTypeCsArlst mut))) then h :: (filterTypeCon' t mut) else (filterTypeCon' t mut)
                 | _ => (filterTypeCon' t mut)
                end
   end.

(** Filter type constructors (currently identity function). *)
Definition filterTypeCon (ls : list ((string * term) * list string)) (mut : list mutual_inductive_body) :
                         list ((string * term) * list string) := ls.











(** Look up the list of constructor arities for a given type name. *)
Fixpoint getCstrArityLst' (typeName : string) (r : list (string * list nat)) : list nat :=
  match r with
   | [] => errorlstNat
   | (h :: t) => if String.eqb typeName (fst h) then snd h else getCstrArityLst' typeName t
  end.

(** Get all constructor arities for a type by name from mutual inductives. *)
Definition getCstrArityLst (typeName : string) (muts : list mutual_inductive_body) : list nat :=
 getCstrArityLst' typeName (extractTypeCsArlst muts).

(** Create a branch that returns None for a non-matching constructor case. *)
Definition mkNoneBranch (n : nat) : branch term :=
  mkNoneBr n (tApp
               (tConstruct
                  {|
                    inductive_mind := <?option?>;
                    inductive_ind := 0
                  |} 1 [])
               [tApp
                  (tInd
                     {|
                       inductive_mind := <?list?>; inductive_ind := 0
                     |} [])
                  [<%nat%>]]).

(** Create a branch that returns Some with the given body. *)
Definition mkSomeBranch (l : list string) (t : term) : branch term :=
  {|
    bcontext := genBinNmLsStr l;
    bbody := t
  |}.

(** Return the first n elements of a list. *)
Fixpoint untilLst (n : nat) (l : list nat) : list nat :=
 match n with
  | 0 => []
  | S m => match l with
            | [] => []
            | h :: t => (h :: untilLst m t)
           end
 end.

(** Return the list starting after index n. *)
Fixpoint restLst (n : nat) (l : list nat) : list nat :=
 match n with
  | 0 => tl l
  | S m => match l with
            | [] => []
            | h :: t => restLst m t
           end
 end.

(** Create the list of branches for a pattern match:
    None branches before the matching constructor, a Some branch for the match,
    and None branches after. *)
Definition mkBrLst (s : (string * term) * list string) (l : list mutual_inductive_body) (t : term) : list (branch term) :=
  let csArlst := (getCstrArityLst (getTypeNm s) l) in
  let index := getCstrIndex s in
  map mkNoneBranch (untilLst index csArlst) ++ [mkSomeBranch (rev (snd s)) t] ++ map mkNoneBranch (restLst index csArlst).



(** Create a case expression (pattern match) term.
    Takes a scrutinee with type parameters, inductive bodies, and a body term. *)
Definition mkCase'  (s' : ((string * term) * list string) * list term ) (l : list mutual_inductive_body) (t : term)
                      : term :=
  let s := fst s' in
  (tCase
     {|
       ci_ind := getType s ;
       ci_npar := length (snd s');
       ci_relevance := Relevant
     |}
     {|
       puinst := [];
       pparams := (snd s');
       pcontext := [{| binder_name := nNamed (fst (fst s)); binder_relevance := Relevant |}];
       preturn :=
         (tApp
           (tInd
              {|
                inductive_mind := <?option?>;
                inductive_ind := 0
              |} [])
           [tApp
         (tInd
            {|
              inductive_mind := <?list?>; inductive_ind := 0
            |} [])
         [<%nat%>]])
     |} (tVar (fst (fst s))) (* Will be converted to De Bruijn index later *)
      (mkBrLst s l t)).



(** The identity function as a quoted term. *)
Definition idTerm := <%(fun A : Type => (fun x : A => x))%>.
MetaRocq Quote Definition oBoolT := (Some true).

(** Term representation of the polymorphic identity function. *)
Definition identityTerm : term := idTerm.

(** Create nested pattern matches recursively.
    Base case returns identity, single case returns value, multiple cases nest. *)
Fixpoint mkPmNested' (ls : list (((string * term) * list string) * list term)) (ls' : list (((string * term) * list string))) (outputVars : list (string))
            (mut : list mutual_inductive_body) : term :=
 match ls with
  | [] => identityTerm
  | (h :: nil) => mkCase' h mut (retVarVals (sortBinders outputVars (ls')))
  | (h :: t) => mkCase' h mut (mkPmNested' t ls' outputVars mut)
 end.

(** Create a nested pattern match structure from a list of constructor patterns. *)
Definition mkPmNested (ls' : list (((string * term) * list string))) (outputVars : list string)
            (mut : list mutual_inductive_body) : term :=
            mkPmNested' (preProcConsTypeVar ls' ls') ls' outputVars mut.

(** Remove None values from a list of options. *)
Fixpoint removeOpt {A : Type} (optls : list (option A)) : list A :=
 match optls with
  | [] => []
  | (Some x :: t) => (x :: removeOpt t)
  | (None :: t) => removeOpt t
 end.

(** Create a lambda abstraction wrapping the nested pattern match.
    Returns None if the structure doesn't match expected shape. *)
Definition mkLam' (ls : list (((string * term) * list string))) (outputVars : list string) (mut : list mutual_inductive_body) : option term :=
  match ls with
  | [] => None
  | (h :: ((str, typeInfo, []) :: t))  =>
      Some (tLambda {| binder_name := nNamed "v2"%bs; binder_relevance := Relevant |}
                    typeInfo (mkPmNested ls outputVars mut))
  | _ => None
  end.

(** Wrapper for mkLam' that filters out None options from mutual inductives. *)
Definition mkLam (ls : list (((string * term) * list string))) (outputVars : list string) (mut : list (option mutual_inductive_body)) : option term :=
  mkLam' ls outputVars (removeOpt mut).



(** Create a lambda term from an inductive by extracting and processing pattern match data.
    Checks that all terms are fully processed before constructing the lambda. *)
Definition mkLamfromInd (p : program) (outputVars : list string) (fuel : nat) : option term :=
 let td := extractTypeData p in
  let pmd := extractPatMatData p in
   if (preProcConsRem fuel pmd) then (mkLam (preProcCons fuel pmd) outputVars td) else None.

(** Similar to mkLamfromInd but takes an explicit conjunction term instead of extracting it. *)
Definition mkLamfromInd2 (conjTm : term) (p : program) (outputVars : list string) (fuel : nat) : option term :=
 let td := extractTypeData p in
  let pmd := conjTm in
   if (preProcConsRem fuel pmd) then (mkLam (preProcCons fuel pmd) outputVars td) else None.

(** Error term for partial functions. *)
Parameter errTm : term.

(** Unwrap an option term, returning error term if None. *)
Definition removeopTm (o : option term) : term :=
 match o with
  | Some t => t
  | None => errTm
 end.


(*
tApp
             (tConstruct
                {|
                  inductive_mind := <?option?>; inductive_ind := 0
                |} 0 [])
             [tApp
                (tInd
                   {|
                     inductive_mind := <?list?>; inductive_ind := 0
                   |} [])
                [<%nat%>];
              tApp
                (tConstruct
                   {|
                     inductive_mind := <?list?>; inductive_ind := 0
                   |} 1 [])
                [<%nat%>; tVar "y";
                 tApp
                   (tConstruct
                      {|
                        inductive_mind := <?list?>;
                        inductive_ind := 0
                      |} 1 [])
                   [<%nat%>; tVar "y";
                    tApp
                      (tConstruct
                         {|
                           inductive_mind := <?list?>;
                           inductive_ind := 0
                         |} 0 [])
                      [<%nat%>]]]]
*)

(** Error value for module path. *)
Parameter errorPath : prod modpath ident.

(** Extract the kernel name from an inductive term. *)
Definition getPathIdent (t : term) : prod modpath ident :=
 match t with
  | tInd p l => inductive_mind p
  | _ => errorPath
 end.

(** Main animation function: generates an executable pattern matching function
    from an inductive predicate.
    Takes the inductive, output variables, function name, and fuel limit.
    Produces a TemplateMonad computation that defines the animated function. *)
Definition justAnimatePatMat {A : Type} (induct : A) (outputVar : list string) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
 indTm <- tmQuote induct ;;
 termConj <- general.animate2 (getPathIdent indTm) ;;
 termFull <- tmQuoteRecTransp  induct  false ;;
 t <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption ((typeConstrPatMatch.removeopTm (typeConstrPatMatch.mkLamfromInd2 termConj termFull outputVar fuel))))) ;;
 f <- tmUnquote t ;;
 tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
 tmMsg "done".

End typeConstrPatMatch.

(** ** Example Inductive Predicates
    This section contains example predicates used for testing animation. *)

(** Example: Cases requiring function inversion.
    This predicate applies a function in the recursive call. *)
Inductive recPred' : nat -> nat -> Prop :=
 | recPred'Ind : forall a b, recPred' a b -> recPred' (a + S b) (S a + b).

(** Similar example with successor applications. *)
Inductive recPred'' : nat -> nat -> Prop :=
 | recPred''Ind : forall a b, recPred' a b -> recPred'' (S b) (S a).

(** Mutually recursive predicate example with base and inductive cases. *)
Inductive recPredFull : nat -> nat -> Prop :=
 | recPredFullBase : recPredFull 1 3
 | recPredFullCons : forall a b, recPredInd1 a b -> recPredFull (S a) (S b)

with recPredInd1 : nat -> nat -> Prop :=
 | recPredInd1Cons : forall a b, recPredFull a b  -> recPredInd1 a b.


(** Quote the recursive predicate for inspection. *)
MetaRocq Quote Recursively Definition recPredFull_syntax := recPredFull.

(** Term representation of the recPredFullCons constructor type. *)
Definition recPredFullConsTm : term :=
 tPro "a" <%nat%>
                     (tPro "b" <%nat%>
                        (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                           (tApp (tRel 2) [tRel 1; tRel 0])
                           (tApp (tRel 4)
                              [tApp
                                 (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
                                 [tRel 2];
                               tApp
                                 (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
                                 [tRel 1]]))).

(** Error term parameter. *)
Parameter errorTm : term.


(* MetaRocq Run (general.animate <? recPredFull ?>). *)


(** Sample input term showing the structure of a constructor clause. *)
Definition sampleInput : term :=
(tPro "a" <%nat%>
   (tPro "b" <%nat%>
      (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
         (tApp (tVar "recPredInd1") [tVar "a"; tVar "b"])
         (tApp (tVar "recPredFull")
            [tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "a"];
             tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "b"]])))).

(** Create a branch returning a wildcard value for non-matching cases. *)
Definition mkNoneBranch2 (wildCardRet : term) (n : nat)  : branch term :=
  typeConstrPatMatch.mkNoneBr n wildCardRet.


(** Create branch list with custom wildcard return value for non-matching cases. *)
Definition mkBrLst2 (s : (string * term) * list string) (l : list mutual_inductive_body) (t : term) (wildCardRet : term) : list (branch term) :=
 let csArlst := (typeConstrPatMatch.getCstrArityLst (typeConstrPatMatch.getTypeNm s) l) in
  let index := typeConstrPatMatch.getCstrIndex s in
  map (mkNoneBranch2 wildCardRet) (typeConstrPatMatch.untilLst index csArlst) ++ [typeConstrPatMatch.mkSomeBranch (rev (snd s)) t] ++ map (mkNoneBranch2 wildCardRet) (typeConstrPatMatch.restLst index csArlst).

(** Create a case expression with custom output type and wildcard return value. *)
Definition mkCase2'  (s' : ((string * term) * list string) * list term ) (l : list mutual_inductive_body) (t : term) (outputType : term) (wildCardRet : term)
                      : term :=
  let s := fst s' in
  (tCase
     {|
       ci_ind := typeConstrPatMatch.getType s ;
       ci_npar := length (snd s');
       ci_relevance := Relevant
     |}
     {|
       puinst := [];
       pparams := (snd s');
       pcontext := [{| binder_name := nNamed (fst (fst s)); binder_relevance := Relevant |}];
       preturn :=
       outputType
     |} (tVar (fst (fst s))) (* Should get changed to a tRel after deBruijning *)
      (mkBrLst2 s l t wildCardRet)).


(** Collect sets of variable names and bound variables from a pattern structure.
    Returns a pair of lists: variables with tVar terms, and all variable names. *)
Fixpoint collectVarSets (l : list ((string * term) * list string)) : list string * list string :=
 match l with
 | [] => ([], [])
 | h :: t => match snd (fst h) with
              | tVar str => (str :: (fst (collectVarSets t)), (app (snd h) (fst (fst h) :: snd (collectVarSets t))))
              | _ => ((fst (collectVarSets t)), (app (snd h) (fst (fst h) :: snd (collectVarSets t))))
             end
end.

(** Check that no element of l1 appears in l2 (no repeated variables). *)
Fixpoint noRepeat (l1 : list string) (l2 : list string) : bool :=
 match l1 with
  | [] => true
  | (h :: t) => negb (typeConstrPatMatch.chkMemberStr h (l2)) && (noRepeat t l2)
 end.


(** Extract a mapping from original variable names to their tVar references. *)
Fixpoint origVarsMap (l : list ((string * term) * list string)) : list (string * string) :=
match l with
 | [] => []
 | (str, tVar str1, lst) :: t => (str, str1) :: (origVarsMap t)
 | _ :: t => origVarsMap t
end.

(** Switch a single variable name according to a mapping. *)
Fixpoint switchOneVar (s : string) (map : list (string * string)) : string :=
 match map with
  | [] => s
  | (str, str1) :: t => if (String.eqb s str) then str1 else switchOneVar s t
 end.

(** Apply variable name switching to a term structure. *)
Definition switchVars  (d : list (string * string)) (o : ((string * term) * list string)) : ((string * term) * list string) :=
 match o with
  | (s, t, l) => ((switchOneVar s d), t, (map (fun s => switchOneVar s d) l))
 end.

(** Apply variable switching to a list of terms. *)
Definition switchVars' (d : list (string * string))  (l : list ((string * term) * list string)) :=
 (map (switchVars d) l).

(** Change all variables in a structure to their canonical names. *)
Definition changeVars (l : list ((string * term) * list string)) : list ((string * term) * list string) :=
 switchVars' (origVarsMap l) l.



(** Create nested pattern matches with custom output term, type, and wildcard.
    Version 2 with more flexibility than mkPmNested. *)
Fixpoint mkPmNested2' (ls : list (((string * term) * list string) * list term)) (ls' : list (((string * term) * list string))) (outputTerm : term) (outputType : term) (wildCardRet : term)
            (mut : list mutual_inductive_body)  : term :=
 match ls with
  | [] => typeConstrPatMatch.identityTerm
  | (h :: nil) => mkCase2' h mut (outputTerm) outputType wildCardRet
  | (h :: t) => mkCase2' h mut (mkPmNested2' t ls' outputTerm outputType wildCardRet mut) outputType wildCardRet
 end.

(** Wrapper for mkPmNested2' that pre-processes constructor type variables. *)
Definition mkPmNested2 (ls' : list (((string * term) * list string))) (outputTerm : term) (outputType : term) (wildCardRet : term)
            (mut : list mutual_inductive_body)  : term :=
            mkPmNested2' (typeConstrPatMatch.preProcConsTypeVar ls' ls') ls' outputTerm outputType wildCardRet mut.

(** Remove None values from a list of options (duplicate definition). *)
Fixpoint removeOpt {A : Type} (optls : list (option A)) : list A :=
 match optls with
  | [] => []
  | (Some x :: t) => (x :: removeOpt t)
  | (None :: t) => removeOpt t
 end.

(** Create a lambda abstraction wrapping nested pattern match (version 2).
    Requires specific structure with at least 3 elements. *)
Definition mkLam2' (ls : list (((string * term) * list string))) (outputTerm : term) (outputType : term) (wildCardRet : term) (mut : list mutual_inductive_body)  : option term :=
 match ls with
 | [] => None
 | (h :: ((str, typeInfo, []) :: ((str2, t', l') :: rest)))  => Some (tLambda {| binder_name := nNamed str2; binder_relevance := Relevant |}
                                 (typeInfo) (mkPmNested2 ls outputTerm outputType wildCardRet mut))
 | _ => None
 end.

(** Wrapper for mkLam2' that filters out None options. *)
Definition mkLam2 (ls : list (((string * term) * list string))) (outputTerm : term) (outputType : term) (wildCardRet : term) (mut : list (option mutual_inductive_body))  : option term :=
  mkLam2' ls outputTerm outputType wildCardRet (removeOpt mut).



(** Create lambda from inductive with custom conjunction term and multiple programs.
    Version 3 supporting multiple programs and custom output term/type. *)
Definition mkLamfromInd3 (conjTm : term) (lstP : list program) (outputTerm : term) (outputType : term) (wildCardRet : term) (fuel : nat) : option term :=
 let td := concat (map (typeConstrPatMatch.extractTypeData) lstP) in
  let pmd := conjTm in
   if (typeConstrPatMatch.preProcConsRem fuel pmd) then (mkLam2 (changeVars (typeConstrPatMatch.preProcCons fuel pmd)) outputTerm outputType wildCardRet td) else None.

(** Error term parameter (duplicate definition). *)
Parameter errTm : term.

(** Unwrap option term, returning error if None (duplicate definition). *)
Definition removeopTm (o : option term) : term :=
 match o with
  | Some t => t
  | None => errTm
 end.



(** Error path parameter (duplicate definition). *)
Parameter errorPath : prod modpath ident.

(** Extract kernel name from inductive term (duplicate definition). *)
Definition getPathIdent (t : term) : prod modpath ident :=
 match t with
  | tInd p l => inductive_mind p
  | _ => errorPath
 end.

(** Animate a pattern match with custom input/output terms and types (version 2).
    Checks for variable clashes before proceeding.
    Creates an equality constraint combining input term with a fresh variable. *)
Definition justAnimatePatMat2 {A : Type} (induct : A) (inputTerm' : term) (inputType : term) (outputTerm : term) (outputType : term) (wildCardRet : term) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
 termFull <- tmQuoteRecTransp  induct  false ;;
 let inputTerm := tApp <%eq%> [inputType; inputTerm'; tVar "v_init"] in
 if noRepeat (fst (collectVarSets (typeConstrPatMatch.preProcCons fuel inputTerm))) (snd (collectVarSets (typeConstrPatMatch.preProcCons fuel inputTerm))) then
 t <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption ((typeConstrPatMatch.removeopTm (mkLamfromInd3 inputTerm [termFull] outputTerm outputType wildCardRet fuel))))) ;;
 f <- tmUnquote t ;;
 tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
 tmMsg "done"
 else
 tmFail "found clashing variables".









(** Dispatch mechanism: try each function in the list until one returns Some.
    Returns None if all functions return None. *)
Fixpoint dispatchInternal (inT : Type) (outT : Type)
                            (listFn : list (inT -> option (outT))) : (inT -> (option outT)) :=
 fun x => match listFn with
           | [] => None
           | h :: t => let r := h x in
                       match r with
                       | None => (dispatchInternal inT outT t) x
                       | _ => r
                       end
          end .

(** Construct a term representing a list of terms with given element type. *)
Fixpoint mkLstTm' (lst : list term) (typeofTm : term) : term :=
 match lst with
  | [] => tApp
           (tConstruct
              {|
                inductive_mind := <?list?>; inductive_ind := 0
              |} 0 []) [typeofTm]
  | h :: t =>  tApp
               (tConstruct
               {| inductive_mind := <?list?>; inductive_ind := 0 |} 1 [])
               [typeofTm; h; (mkLstTm' t typeofTm)]
 end.

(** Provide a default value for an option-returning function. *)
Definition defaultVal (inputType : Type) (outputType : Type) (default : outputType) (f : inputType -> option (outputType)) : (inputType -> outputType) :=
 fun x => match f x with
           | Some y => y
           | None => default
          end.

(* Quote a list of values into a list of terms. *)
Fixpoint quoteList {A : Type} (l : list A) : TemplateMonad (list term) :=
  match l with
  | [] => ret []
  | h :: rest =>
      t <- tmQuote h ;;
      l' <- quoteList rest ;;
      tmReturn (t :: l')
  end.

(* Animation version 4: returns a term instead of defining it.
   Useful for building dispatch tables programmatically.
   Checks for variable clashes and sufficient fuel. *)
Definition justAnimatePatMat4
           {A : Type}
           (induct : A)
           (inputTerm' : term)
           (inputType : term)
           (outputTerm : term)
           (outputType : term)
           (wildCardRet : term)
           (fuel : nat)
  : TemplateMonad term :=
  termFull <- tmQuoteRecTransp induct false ;;
  outcomePolyProg <- tmQuoteRecTransp outcomePoly false ;;
  prodTpProg <- tmQuoteRecTransp prod false ;;
  let inputTerm := tApp <%eq%> [inputType; inputTerm'; tVar "v_init"] in
  if andb (noRepeat (fst (collectVarSets (typeConstrPatMatch.preProcCons fuel inputTerm)))
                    (snd (collectVarSets (typeConstrPatMatch.preProcCons fuel inputTerm))))
          (typeConstrPatMatch.preProcConsRem fuel inputTerm)
  then
    t <- tmEval all (typeConstrPatMatch.removeopTm
                      (DB.deBruijnOption
                        (typeConstrPatMatch.removeopTm
                          (mkLamfromInd3 inputTerm
                                        [termFull; outcomePolyProg; prodTpProg]
                                        outputTerm
                                        outputType
                                        wildCardRet
                                        fuel)))) ;;
    tmReturn t
  else
    tmFail "found clashing variables or insufficient fuel".

(** Quote option None for use as a term. *)
MetaRocq Quote Definition optNatTm := (@None nat).
Print optNatTm.

(* Animate multiple pattern branches for a single inductive predicate.
   Creates a list of animated functions, one per branch pattern. *)
Fixpoint justAnimateMultPat
         {A : Type}
         (induct : A)
         (branchData : list (prod term term))
         (inputType : term)
         (outputType : term)
         (fuel : nat)
  : TemplateMonad (list term) :=
  match branchData with
  | [] => tmFail "no Branch Data"
  | [h] =>
      t <- justAnimatePatMat4
             induct
             (fst h)
             inputType
             (tApp (tConstruct {| inductive_mind := <?option?>; inductive_ind := 0 |} 0 [])
                   [outputType; snd h])
             (tApp <%option%> [outputType])
             (tApp (tConstruct {| inductive_mind := <?option?>; inductive_ind := 0 |} 1 [])
                   [outputType])
             fuel ;;
      tmReturn [t]
  | h :: rest =>
      t <- justAnimatePatMat4
             induct
             (fst h)
             inputType
             (tApp (tConstruct {| inductive_mind := <?option?>; inductive_ind := 0 |} 0 [])
                   [outputType; snd h])
             (tApp <%option%> [outputType])
             (tApp (tConstruct {| inductive_mind := <?option?>; inductive_ind := 0 |} 1 [])
                   [outputType])
             fuel ;;
      lstT <- justAnimateMultPat induct rest inputType outputType fuel ;;
      tmReturn (t :: lstT)
  end.


(** Construct a dispatch function from a list of animated branch functions.
    Wraps with defaultVal to provide a fallback for unmatched inputs. *)
Definition mkMulPatMatFn' (fns : list term) (wildCardRet : term) (inputType : term) (outputType : term)  : term :=
 let fnType := tProd {| binder_name := nAnon; binder_relevance := Relevant |} inputType
         (tApp
            (tInd
               {|
                 inductive_mind := <?option?>;
                 inductive_ind := 0
               |} [])
            [outputType]) in
 (tApp <%defaultVal%> [inputType; outputType; wildCardRet; (tApp <%dispatchInternal%> [inputType; outputType; (mkLstTm' fns fnType)])]).

(* Create a multi-branch pattern match function with dispatch mechanism.
   Combines multiple animated branches into a single function with fallback. *)
Definition mkMulPatMatFn
           {A : Type}
           (induct : A)
           (branchData : list (prod term term))
           (inputType : term)
           (outputType : term)
           (wildCardRet : term)
           (fuel : nat)
  : TemplateMonad term :=
  subfns <- justAnimateMultPat induct branchData inputType outputType fuel ;;
  tmReturn (mkMulPatMatFn' subfns wildCardRet inputType outputType).

Check ([((tApp (tConstruct
            {|
              inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
              inductive_ind := 0
            |} 1 [])[tVar "b"]),   (tApp (tConstruct
            {|
              inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
              inductive_ind := 0
            |} 1 [])
         [tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
            [tVar "b"]]))]).












(* Join two pattern match animations in sequence (composition).
   Creates a function that transforms from preIn to postOut through an intermediate step.
   Wraps inputs/outputs in outcomePoly and handles fuel errors. *)
Definition joinPatMatPoly
           {A : Type}
           (induct : A)
           (preIn' : term)
           (preInType' : term)
           (preOut' : term)
           (preOutType' : term)
           (postIn' : term)
           (postInType' : term)
           (postOut' : term)
           (postOutType' : term)
           (nmFn : string)
           (fuel : nat)
  : TemplateMonad unit :=
  let preIn := tApp <%successPoly%> [preInType'; preIn'] in
  let preInType := tApp <%outcomePoly%> [preInType'] in
  let preOut := tApp <%successPoly%> [preOutType'; preOut'] in
  let preOutType := tApp <%outcomePoly%> [preOutType'] in
  let postIn := tApp <%successPoly%> [postInType'; postIn'] in
  let postInType := tApp <%outcomePoly%> [postInType'] in
  let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
  let postOutType := tApp <%outcomePoly%> [postOutType'] in
  let nmFnpreInpreOut := "animatePreConFn" in
  let preInpreOutFnType := (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                  preInType
                                  preOutType) in
  preOutTopostOutFn <- mkMulPatMatFn
                         induct
                         [(preOut, postOut);
                          (tApp <%fuelErrorPoly%> [preOutType'],
                           tApp <%fuelErrorPoly%> [postOutType'])]
                         preOutType
                         postOutType
                         (tApp <%noMatchPoly%> [postOutType'])
                         fuel ;;
  tBody <- mkMulPatMatFn
             induct
             [(postIn, tApp preOutTopostOutFn [tApp (tVar nmFnpreInpreOut) [preIn]]);
              (tApp <%fuelErrorPoly%> [postInType'],
               tApp <%fuelErrorPoly%> [postOutType'])]
             postInType
             postOutType
             (tApp <%noMatchPoly%> [postOutType'])
             fuel ;;
  t' <- tmEval all (removeopTm (DB.deBruijnOption (tLam nmFnpreInpreOut preInpreOutFnType tBody))) ;;
  f <- tmUnquote t' ;;
  tmEval hnf (my_projT2 f) >>=
  tmDefinitionRed_ false nmFn (Some hnf) ;;
  tmMsg "done".

(* Construct a product type from a list of type pairs (for multiple LHS predicates). *)
Fixpoint mklhsProdType (lhsIndPre : list (term * term)) : TemplateMonad term :=
  match lhsIndPre with
  | [] => tmFail "no predicates on LHS"
  | [h] => tmReturn (snd h)
  | h :: t =>
      res <- mklhsProdType t ;;
      tmReturn (tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; res])
  end.

(* Construct a product term from a list of term-type pairs. *)
Fixpoint mklhsProdTm (lhsIndPre : list (term * term)) : TemplateMonad term :=
  match lhsIndPre with
  | [] => tmFail "no predicates on LHS"
  | [h] => tmReturn (fst h)
  | h :: t =>
      res <- mklhsProdTm t ;;
      resT <- mklhsProdType t ;;
      tmReturn (tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
                     [snd h; resT; fst h; res])
  end.

(** Create product type for precondition predicates from LHS inductives. *)
Definition mkPreConProdType  (lhsInd : list ((((string * term) * term) * term) * term)) : TemplateMonad term :=
 mklhsProdType (map (fun tuple => ((snd (fst (fst (fst tuple)))), (snd (fst (fst tuple))))) lhsInd).

(** Create product term for precondition predicates from LHS inductives. *)
Definition mkPreConProdTm  (lhsInd : list ((((string * term) * term) * term) * term)) : TemplateMonad term :=
 mklhsProdTm (map (fun tuple => ((snd (fst (fst (fst tuple)))), (snd (fst (fst tuple))))) lhsInd).

(** Create product type for postcondition predicates from LHS inductives. *)
Definition mkPostConProdType  (lhsInd : list ((((string * term) * term) * term) * term)) : TemplateMonad term :=
 mklhsProdType (map (fun tuple => ((((snd (fst tuple)))), (((snd tuple))))) lhsInd).

(** Create product term for postcondition predicates from LHS inductives. *)
Definition mkPostConProdTm  (lhsInd : list ((((string * term) * term) * term) * term)) : TemplateMonad term :=
 mklhsProdTm (map (fun tuple => ((((snd (fst tuple)))), (((snd tuple))))) lhsInd).

(** Wrap pre/post conditions in outcomePoly success constructors. *)
Definition mkOutcome (lhsInd : ((((string * term) * term) * term) * term)) : ((((string * term) * term) * term) * term) :=
 match lhsInd with
  | ((((nm, preCon), preConT), postCon), postConT) => ((((nm, (tApp <%successPoly%> [preConT; preCon])), (tApp <%outcomePoly%> [preConT])), (tApp <%successPoly%> [postConT; postCon])), (tApp <%outcomePoly%> [postConT]))
 end.

(** Map mkOutcome over a list of LHS inductives. *)
Definition mkOutcomeProd (lhsInd : list ((((string * term) * term) * term) * term)) : list ((((string * term) * term) * term) * term) :=
 map (mkOutcome) lhsInd.


(* Construct a product of all animated function applications.
   Builds a term that applies each animated function to its precondition. *)
Fixpoint mkproductAllPreInToPreOutOutcome
         (lhsIndOutcome : list ((((string * term) * term) * term) * term))
  : TemplateMonad term :=
  match lhsIndOutcome with
  | [] => tmFail "no predicates on LHS"
  | [h] =>
      tmReturn (tApp (tVar (String.append (fst (fst (fst (fst h)))) "AnimatedTopFn"))
                     [tVar "remFuel"; snd (fst (fst (fst h)))])
  | h :: t =>
      res <- mkproductAllPreInToPreOutOutcome t ;;
      resT <- mkPostConProdType t ;;
      tmReturn (tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
                     [snd h;
                      resT;
                      tApp (tVar (String.append (fst (fst (fst (fst h)))) "AnimatedTopFn"))
                           [tVar "remFuel"; snd (fst (fst (fst h)))];
                      res])
  end.

(* Create nested lambdas over all outcome predicates.
   Wraps function body in lambda abstractions for all animated functions. *)
Fixpoint mklamOverAllOutcome
         (lhsIndOutcome : list ((((string * term) * term) * term) * term))
         (fnBody : term)
  : TemplateMonad term :=
  match lhsIndOutcome with
  | [] => tmFail "no predicates on LHS"
  | [h] =>
      tmReturn (tLambda
                 {| binder_name := nNamed (String.append (fst (fst (fst (fst h)))) "AnimatedTopFn");
                    binder_relevance := Relevant |}
                 (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                        <%nat%>
                        (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                               (snd (fst (fst h)))
                               (snd h)))
                 fnBody)
  | h :: t =>
      res <- mklamOverAllOutcome t fnBody ;;
      tmReturn (tLambda
                 {| binder_name := nNamed (String.append (fst (fst (fst (fst h)))) "AnimatedTopFn");
                    binder_relevance := Relevant |}
                 (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                        <%nat%>
                        (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                               (snd (fst (fst h)))
                               (snd h)))
                 res)
  end.

(** Constant function that always returns fuel error.
    Used as a fallback when fuel is exhausted. *)
Definition fuelErrorPolyCstFn (inputType : Type) (outputType' : Type) : (inputType -> (outcomePoly outputType') ) :=
 fun x : inputType => fuelErrorPoly outputType'.

(** Generate all possible fuel error pattern combinations.
    Creates patterns for handling fuel exhaustion in multi-predicate scenarios. *)
Fixpoint genFuelErrorPatMat (lhsInd : list (term * term)) (index : nat) : list (list (term * term)) :=
match index with
 | 0 => []
 | S index' => match lhsInd with
                | [] => []
                | [(tm, tmTp)] => [[(tVar (String.append "fuelErrorVar" (string_of_nat index)), (tApp (<%outcomePoly%>) [tmTp]))]; [((tApp (<%fuelErrorPoly%>) [tmTp]), (tApp (<%outcomePoly%>) [tmTp]))]]
                | (tm, tmTp) :: rest => app (map (fun l' => (((tVar (String.append "fuelErrorVar" (string_of_nat index))), (tApp (<%outcomePoly%>) [tmTp])) :: l'))  (genFuelErrorPatMat rest index')) (map (fun l' => ((tApp (<%fuelErrorPoly%>) [tmTp]), (tApp (<%outcomePoly%>) [tmTp])) :: l')  (genFuelErrorPatMat rest index'))
               end
end.

(* Create product terms for fuel error patterns. *)
Fixpoint mkProdTmFuelError (lhsIndl : list (list (term * term))) : TemplateMonad (list term) :=
  match lhsIndl with
  | [] => tmReturn []
  | [h] =>
      res <- mklhsProdTm h ;;
      tmReturn [res]
  | h :: t =>
      resTail <- mkProdTmFuelError t ;;
      res <- mklhsProdTm h ;;
      tmReturn (res :: resTail)
  end.

(* Create pattern match data for handling fuel errors. *)
Definition mkFuelErrorPatMatData
           (lhsInd : list (term * term))
           (fuelErrorOut : term)
  : TemplateMonad (list (term * term)) :=
  inData <- mkProdTmFuelError (tl (genFuelErrorPatMat lhsInd (S (length lhsInd)))) ;;
  tmReturn (map (fun s => (s, fuelErrorOut)) inData).










(* General fuel-aware join with LHS predicates.
   Composes multiple animated functions with proper fuel handling.
   Creates a function that maps from LHS postconditions to RHS postcondition. *)
Definition joinPatMatPolyGenFuelAware
           {A : Type}
           (induct : A)
           (lhsInd : list ((((string * term) * term) * term) * term))
           (postIn' : term)
           (postInType' : term)
           (postOut' : term)
           (postOutType' : term)
           (nmCon : string)
           (fuel : nat)
  : TemplateMonad unit :=
  let lhsIndOutcome := mkOutcomeProd lhsInd in
  let postIn := tApp <%successPoly%> [postInType'; postIn'] in
  let postInType := tApp <%outcomePoly%> [postInType'] in
  let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
  let postOutType := tApp <%outcomePoly%> [postOutType'] in
  lhsPostCondProdOutcomeTm <- mkPostConProdTm lhsIndOutcome ;;
  lhsPostCondProdTm <- mkPostConProdTm lhsInd ;;
  lhsPostCondProdType <- mkPostConProdType lhsInd ;;
  lhsPostCondProdOutcomeType <- mkPostConProdType lhsIndOutcome ;;
  lhsPostCondFuelErrorPatMat <- mkFuelErrorPatMatData
                                  (map (fun tup => (snd (fst tup), snd tup)) lhsInd)
                                  (tApp <%fuelErrorPoly%> [postOutType']) ;;
  productAllPreInToPreOutOutcome <- mkproductAllPreInToPreOutOutcome lhsIndOutcome ;;
  preOutTopostOutFn <- mkMulPatMatFn
                         induct
                         ((lhsPostCondProdOutcomeTm, postOut) :: lhsPostCondFuelErrorPatMat)
                         lhsPostCondProdOutcomeType
                         postOutType
                         (tApp <%noMatchPoly%> [postOutType'])
                         fuel ;;
  tBody' <- mkMulPatMatFn
              induct
              [(postIn, tApp preOutTopostOutFn [productAllPreInToPreOutOutcome]);
               (tApp <%fuelErrorPoly%> [postInType'],
                tApp <%fuelErrorPoly%> [postOutType'])]
              postInType
              postOutType
              (tApp <%noMatchPoly%> [postOutType'])
              fuel ;;
  let tBody :=
      (tLam "fuel" <%nat%>
         (tCase
            {| ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
               ci_npar := 0;
               ci_relevance := Relevant |}
            {| puinst := [];
               pparams := [];
               pcontext := [{| binder_name := nNamed "fuel"; binder_relevance := Relevant |}];
               preturn := (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                postInType
                                postOutType) |}
            (tVar "fuel")
            [{| bcontext := [];
                bbody := (tApp <%fuelErrorPolyCstFn%> [postInType; postOutType']) |};
             {| bcontext := [{| binder_name := nNamed "remFuel"; binder_relevance := Relevant |}];
                bbody := tBody' |}])) in
  u <- mklamOverAllOutcome lhsIndOutcome tBody ;;
  t' <- tmEval all (removeopTm (DB.deBruijnOption u)) ;;
  f <- tmUnquote t' ;;
  tmEval hnf (my_projT2 f) >>=
  tmDefinitionRed_ false (String.append nmCon "Animated") (Some hnf) ;;
  tmMsg "done".

(** Fuel-aware join without LHS predicates (base case).
    Simpler version for constructors with no recursive premises. *)
Definition joinPatMatPolyGenFuelAwareNoLHS {A : Type} (induct : A)
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term) (nmCon : string)
                        (fuel : nat) : TemplateMonad unit :=

let postIn := tApp <%successPoly%> [postInType'; postIn'] in
let postInType := tApp <%outcomePoly%> [postInType'] in

let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
let postOutType := tApp <%outcomePoly%> [postOutType'] in

tBody' <-  mkMulPatMatFn (induct) ([(postIn, (postOut)); ((tApp <%fuelErrorPoly%> [postInType']),(tApp <%fuelErrorPoly%> [postOutType'])) ]) postInType postOutType (tApp <%noMatchPoly%> [postOutType']) fuel ;;



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





t' <- tmEval all (removeopTm (DB.deBruijnOption u)) ;;

f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append nmCon "Animated") (Some hnf) ;; tmMsg "done".



Definition joinPatMatPolyGenFuelAwareNoLHSTm {A : Type} (induct : A)
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term) (nmCon : string)
                        (fuel : nat) : TemplateMonad term :=


let postIn := tApp <%successPoly%> [postInType'; postIn'] in
let postInType := tApp <%outcomePoly%> [postInType'] in

let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
let postOutType := tApp <%outcomePoly%> [postOutType'] in






tBody' <-  mkMulPatMatFn (induct) ([(postIn, (postOut)); ((tApp <%fuelErrorPoly%> [postInType']),(tApp <%fuelErrorPoly%> [postOutType'])) ]) postInType postOutType (tApp <%noMatchPoly%> [postOutType']) fuel ;;



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





t' <- tmEval all (removeopTm (DB.deBruijnOption u)) ;;

tmReturn t'.





Definition animateOneClause {A : Type} (induct : A) (lhsInd : list ((((string * term) * term) * term) * term))
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term) (nmCon : string)
                        (fuel : nat) : TemplateMonad unit :=
 match lhsInd with
  | [] =>  joinPatMatPolyGenFuelAwareNoLHS induct
                      (postIn') (postInType') (postOut') (postOutType') (nmCon)
                        (fuel)
  | lst =>  joinPatMatPolyGenFuelAware (induct) (lst)
                      (postIn') (postInType') (postOut') (postOutType') (nmCon)
                        (fuel)
 end.






(* __________________________Examples __________________________________ *)


(* Examples with multiple predicates on LHS *)

Inductive rel4 : (prod nat nat) -> (prod nat nat) -> Prop :=

 | rel4Cons : forall a b c d, rel5 a c /\ rel6 (b) d -> rel4 (a, S b) (c, S d)

with rel5 : nat -> nat -> Prop :=

| rel5Cons : forall u w, w = S u -> rel5 u w

with rel6 : nat -> nat -> Prop :=

| rel6Cons : forall u1 w1, w1 = S (S u1) -> rel6 u1 w1.




Definition pairNatTerm : term := tApp
         (tInd
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} [])
         [<%nat%>; <%nat%>].


Definition preInTPair : term := tApp (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])
         [<%nat%>; <%nat%>;  (tVar "a"); (tVar "b")].




Definition preOutTPair : term :=  tApp (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])
         [<%nat%>; <%nat%>;  (tVar "c"); (tVar "d")].



Definition postInTPair : term := tApp (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])
         [<%nat%>; <%nat%>;  (tVar "a"); (tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "b"])].



Definition postOutTPair : term := tApp (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])
         [<%nat%>; <%nat%>;  (tVar "c"); (tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "d"])].





MetaRocq Run (animateOneClause (rel4) ([(((("rel5", (tVar "a")), <%nat%>), (tVar "c")), <%nat%>); ((((("rel6", (tVar "b"))),
                           <%nat%>), (tVar "d")), <%nat%>)]) (postInTPair) (pairNatTerm) (postOutTPair)
                         (pairNatTerm) ("rel4Cons") (50)).
Print rel4ConsAnimated.

MetaRocq Run (animateOneClause (rel4) ([(((("rel5", (tVar "b")), <%nat%>), (tVar "c")), <%nat%>); ((((("rel6", (tVar "b"))),
                           <%nat%>), (tVar "d")), <%nat%>)]) (postInTPair) (pairNatTerm) (postOutTPair)
                         (pairNatTerm) ("rel4Cons2") (50)).
Print rel4Cons2Animated.


Definition rel5ConsAnimTop (fuel : nat) (inp : (outcomePoly nat)) : (outcomePoly nat) :=
 match fuel with
 | 0 => (fuelErrorPoly nat)
 | S m => match inp with
           | (successPoly k) => (successPoly nat (S k))
           | _ => noMatchPoly nat
          end
 end.



Definition rel6ConsAnimTop (fuel : nat) (inp : (outcomePoly nat)) : (outcomePoly nat) :=
 match fuel with
 | 0 => (fuelErrorPoly nat)
 | S m => match inp with
           | (successPoly k) => (successPoly nat (S (S k)))
           | _ => noMatchPoly nat
          end
 end.

Definition rel7ConsAnimTop (fuel : nat) (inp : (outcomePoly nat)) : (outcomePoly nat) :=
 match fuel with
 | 0 => (fuelErrorPoly nat)
 | S m => match inp with
           | (successPoly k) => (successPoly nat (S (S k)))
           | _ => noMatchPoly nat
          end
 end.


Compute (rel4Cons2Animated rel5ConsAnimTop rel6ConsAnimTop 30 (successPoly (prod nat nat) (13, 4))).

Compute (rel4Cons2Animated rel5ConsAnimTop rel6ConsAnimTop 30 (successPoly (prod nat nat) (10, 4))).


MetaRocq Run (animateOneClause (rel4) ([(((("rel5", (tVar "b")), <%nat%>), (tVar "c")), <%nat%>); ((((("rel6", (tVar "b"))),
                           <%nat%>), (tVar "d")), <%nat%>); ((((("rel7", (tVar "b"))),
                           <%nat%>), (tVar "e")), <%nat%>)]) (postInTPair) (pairNatTerm) (postOutTPair)
                         (pairNatTerm) ("rel4Cons3") (50)).




Compute (rel4Cons3Animated rel5ConsAnimTop rel6ConsAnimTop rel7ConsAnimTop 30 (successPoly (prod nat nat) (13, 4))).





Compute (rel4ConsAnimated rel5ConsAnimTop rel6ConsAnimTop 30 (successPoly (prod nat nat) (13, 4))).

Compute (rel4ConsAnimated rel5ConsAnimTop rel6ConsAnimTop 30 (successPoly (prod nat nat) (4, 0))).

Compute (rel4ConsAnimated rel5ConsAnimTop rel6ConsAnimTop 0 (successPoly (prod nat nat) (4, 5))).

(* Should say fuelError *)
Compute (rel4ConsAnimated rel5ConsAnimTop rel6ConsAnimTop 1 (successPoly (prod nat nat) (4, 5))).

MetaRocq Run (animateOneClause (recPredFull) ([]) (<%1%>) (<%nat%>) (<%3%>)
                         (<%nat%>) ("recPredBase") (50)).
Print recPredBaseAnimated.

MetaRocq Run (animateOneClause (recPredFull) ([]) (tVar "a") (<%nat%>) (<%3%>)
                         (<%nat%>) ("recPredBase2") (50)).
Print recPredBase2Animated.

Compute (recPredBase2Animated 5 (successPoly nat 1)).

Compute (recPredBase2Animated 5 (successPoly nat 4)).

Compute (recPredBaseAnimated 5 (successPoly nat 1)).

Compute (recPredBaseAnimated 5 (successPoly nat 4)).


(** ** Code for Composing All Animated Clauses
    This section contains the top-level functions for animating entire
    inductive predicates by composing animations of all constructors. *)

(** Animate all constructor clauses for an inductive predicate.
    Calls animateOneClause for each constructor. *)
Fixpoint animateAllClauses {A : Type} (topInduct : A) (cstrData : (list ((((( (list ((((string * term) * term) * term) * term)) *
                      (term)) * (term)) * (term)) * (term)) * (string))))
                        (fuel : nat) : TemplateMonad unit :=
 match cstrData with
  | [] => tmFail "no constructors in Inductive"
  | [h] => animateOneClause topInduct (fst (fst (fst (fst (fst h))))) (snd (fst (fst (fst (fst h))))) (snd (fst (fst (fst h)))) (snd (fst (fst h))) (snd (fst  h)) (snd h) fuel
  | h :: t =>  animateAllClauses topInduct t fuel ;; animateOneClause topInduct (fst (fst (fst (fst (fst h))))) (snd (fst (fst (fst (fst h))))) (snd (fst (fst (fst h)))) (snd (fst (fst h))) (snd (fst  h)) (snd h) fuel
 end.

(** Quote a constant from the current module. *)
Definition quoteConst (s : string) : term :=
tConst
         (MPfile ["animationModules"; "Animation"], s)
         [].

(** Quote a constant with a given kernel name. *)
Definition quoteConst' (kn : kername) (nm : string) :=
tConst (fst kn, nm) [].

(** Build list of terms applying top-level animated functions.
    Handles constructors with and without recursive premises. *)
Fixpoint applyTopFn (kn : kername) (clauseData : list (string * (list string))) : list term :=
match clauseData with
| [] => []
| (postConCons, preConInd) :: t => match preConInd with
                                   | [] => (quoteConst' kn (String.append postConCons "Animated")) :: applyTopFn kn t
                                   | l => tApp (quoteConst' kn (String.append postConCons "Animated")) (map (fun nm => (tVar (String.append nm "AnimatedTopFn"))) l) :: applyTopFn kn t
                                   end
end.

(** Dispatch function: try each function in the list until one returns Some.
    Takes fuel parameter for controlling recursion depth. *)
Fixpoint dispatch {A : Type} {B : Type} (lst : list (A -> nat -> option B)) : A -> nat -> option B :=
 match lst with
 | [] => (fun x y => None)
 | h :: t => fun x y => let g := h x y in
                         match g with
                         | None => dispatch t x y
                         | _ => g
                        end

 end.
(*
Fixpoint dispatchOutcomePolyExt {A : Type} {B : Type} (lst : list (nat -> outcomePoly A  -> outcomePoly B)) : nat -> outcomePoly A -> outcomePoly B :=
 match lst with
 | [] => (fun x y => (noMatchPoly B))
 | h :: t => fun x y => match (h x y) with
                         | (noMatchPoly) => dispatchOutcomePolyExt t x y
                         | _ => h x y
                        end


 end.

Fixpoint dispatchOutcomePolyExt' {A : Type} {B : Type} (lst : list (nat -> outcomePoly A  -> outcomePoly B)) (fuel : nat) (input' : outcomePoly A): outcomePoly B :=
 match fuel with
  | 0 => fuelErrorPoly B
  | S remFuel => match lst with
                  | [] => (noMatchPoly B)
                  | h :: t => match (h remFuel input') with
                         | (noMatchPoly) => dispatchOutcomePolyExt' t remFuel input'
                         | _ => h remFuel input'
                        end
                 end

 end.
*)


(** Default term definition for error cases. *)
Parameter default : (def term).

(** Extract the list of definitions from a fixpoint term. *)
Definition inspectFix (t : term) : list (def term) :=
 match t with
  | tFix l k => l
  | _ => []
 end.

(** Construct a list term from a list of variable names. *)
Fixpoint mkLstTm (eltType : term) (lst : list string) : term :=
 match lst with
  | [] => tApp
           (tConstruct
              {|
                inductive_mind := <?list?>; inductive_ind := 0
              |} 0 []) [eltType]
  | h :: t =>  tApp
               (tConstruct
               {| inductive_mind := <?list?>; inductive_ind := 0 |} 1 [])
               [eltType; tVar h; mkLstTm eltType t]
 end.

(** Create one fixpoint definition for a top-level animated inductive.
    Builds the dispatch function that tries each constructor case. *)
Definition mkOneIndTop (indNm : string) (inputType : term) (outputType : term) (clauseData : list (string * (list string))) (kn : kername) : def term :=

{|
     dname := {| binder_name := nNamed (String.append indNm "AnimatedTopFn") ; binder_relevance := Relevant |};
     dtype :=
       tPro "fuel" <%nat%> (tPro "input" (tApp (<%outcomePoly%>) [inputType])


            (tApp (<%outcomePoly%>) [outputType]));
     dbody :=


          tLam "fuel" <%nat%>

           (tLam "input" (tApp (<%outcomePoly%>) [inputType])
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
                 preturn := (tApp (<%outcomePoly%>) [inputType])

               |} (tVar "fuel")
               [{|
                  bcontext := [];
                  bbody :=
                    (tApp (<%fuelErrorPoly%>) [outputType])
                |};
                {|
                  bcontext := [{| binder_name := nNamed "remFuel"; binder_relevance := Relevant |}];
                  bbody := tApp (tVar "dispatchOutcomePolyExt") [inputType ; outputType; (mkLstTm' (applyTopFn kn clauseData) (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
         <%nat%> (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
        (tApp <%outcomePoly%> [inputType]) (tApp <%outcomePoly%> [outputType])) ) ); tVar "remFuel"; tVar "input"]

                              |}]
                     ))  ; rarg := 0 |}.




(** Construct a fixpoint term from a list of definitions. *)
Definition mkrecFn (ls : list (def term)) (j : nat) : term :=
 tFix ls j.

(** Create all top-level animated inductive definitions (auxiliary). *)
Fixpoint mkAllIndTop' (inductData : (list ((((string) * (term)) * (term)) * (list (string * (list string)))))) (kn : kername) : list (def term) :=
 match inductData with
  | [] => []
  | h :: t => (mkOneIndTop (fst (fst (fst h))) (snd (fst (fst h))) (snd (fst h)) (snd h) kn) :: mkAllIndTop' t kn
 end.

(** Add a definition to a recursive fixpoint block. *)
Definition addToRecBlk (recBlock : term) (t : def term) :=
 match recBlock with
  | tFix ls j => tFix (app ls [t]) j
  | _ => recBlock
 end.

(** Extended dispatch for outcomePoly types with fuel.
    Tries each function in the list, skipping noMatch results. *)
Fixpoint dispatchOutcomePolyExt
  (A B : Type) (lst : list (nat -> outcomePoly A -> outcomePoly B)) (fuel' : nat)
  (input' : outcomePoly A) {struct fuel'} : outcomePoly B :=
  match fuel' with
  | 0 => fuelErrorPoly B
  | S remFuel' =>
      match lst with
      | [] => noMatchPoly B
      | h :: t =>
          let res := h remFuel' input' in
          match res with
          | @noMatchPoly _ => dispatchOutcomePolyExt A B t remFuel' input'
          | _ => res
          end
      end
  end.

(** Quote the dispatch function for embedding in generated code. *)
MetaRocq Quote Definition dt := Eval compute in dispatchOutcomePolyExt.
MetaRocq Run (dt' <- DB.undeBruijn dt ;; tmDefinition "dispatchExtTm'" dt').

(** Extract the dispatch term for use in fixpoint generation. *)
Definition dispatchExtTm := hd default (inspectFix dispatchExtTm').

(** Create all top-level animated inductive definitions with dispatch. *)
Definition mkAllIndTop (inductData : (list ((((string) * (term)) * (term)) * (list (string * (list string)))))) (kn : kername) : list (def term) :=
app (mkAllIndTop' inductData kn) [dispatchExtTm].

(** Main entry point: animate an entire inductive predicate.
    Generates animated functions for all constructors and composes them into
    a mutually recursive fixpoint. *)
Definition animateInductivePredicate {A : Type} (topInduct : A) (nmTopInduct : string) (clauseData : (list ((((( (list ((((string * term) * term) * term) * term)) *
                      (term)) * (term)) * (term)) * (term)) * (string)))) (inductData : (list ((((string) * (term)) * (term)) * (list (string * (list string))))))
                        (kn : kername) (fuel : nat) : TemplateMonad unit :=
          animateAllClauses topInduct clauseData fuel ;;
          let u := (mkrecFn (mkAllIndTop (inductData) kn) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (removeopTm (DB.deBruijnOption u)) ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append nmTopInduct "AnimatedTopFn") (Some hnf) ;; tmMsg "done".




(** Build a product type from a list of output variable specs.
    Returns bool for empty list, single type for singleton, nested products otherwise. *)
Fixpoint mkProdTypeVars (outputData : list (string * term)) :  term :=
 match outputData with
  | [] => <%bool%>
  | [h] =>  (snd h)
  | h :: t => let res := mkProdTypeVars t in  (tApp
                                            (tInd
                                             {|
                                             inductive_mind := <?prod?>; inductive_ind := 0
                                              |} []) [(snd h) ; res])
 end.

(** Build a product term from a list of output variables.
    Constructs nested pairs of variables. *)
Fixpoint mkProdTmVars  (outputData : list (string * term )) : term :=
 match outputData with
  | [] => <%true%>
  | [h] => (tVar (fst h))
  | h :: t => let res := mkProdTmVars t in
                                        let resT := mkProdTypeVars t in (tApp (tConstruct
                                                  {|
                                                   inductive_mind := <?prod?>; inductive_ind := 0
                                                   |} 0 []) [(snd h); resT ; (tVar (fst h)) ; res])
 end.

(** Wrap output variables in a successPoly constructor. *)
Definition getOutputTerm (outputData : list (string * term))  : term :=
  tApp <% successPoly %> [mkProdTypeVars outputData; mkProdTmVars outputData].

(** Extract pattern match binders from an animated predicate.
    Utility function for simple predicates without LHS premises. *)
Definition extractPatMatBinders {A : Type} (kn : kername) (induct : A) (outputData : list (string * term )) (fuel : nat) : TemplateMonad unit :=
  t <- general.animate2 kn ;;
  match t with
  | tApp <%eq%> [typeInputVar; patMatTerm; tVar inputVar] =>
    joinPatMatPolyGenFuelAwareNoLHS induct patMatTerm typeInputVar (mkProdTmVars outputData) (mkProdTypeVars outputData) (snd kn) fuel
  | _ => tmFail "incorrect inductive shape"
  end ;;
  tmMsg "done".

Inductive tlRel : ((list nat) * nat) -> (nat * nat) -> Prop :=
| tlRelCons: forall (a : list nat) (b c d : nat),  [c ; d] = (b :: a) -> tlRel (a, b) (c, d).

MetaRocq Run (t <- general.animate2 <? tlRel ?>;; tmPrint t).

Definition composeOutcomePoly (A : Type) (B : Type) (C : Type) (f : nat -> outcomePoly A -> outcomePoly B) (f' : nat -> outcomePoly B -> outcomePoly C)
                                   : (nat -> outcomePoly A -> outcomePoly C) :=
 fun fuel input => match f fuel input with
                    | successPoly res => f' fuel  (successPoly B res)
                    | fuelErrorPoly => (fuelErrorPoly C)
                    | _ =>  (noMatchPoly C)
                   end.

(* OUTPUT from animation
Definition myFun := composeOutcomePoly (list nat * nat) (list nat) (nat * nat)
        (fun fuel : nat =>
         match fuel with
         | 0 => fuelErrorPolyCstFn (outcomePoly (list nat * nat)) (list nat)
         | S _ =>
             defaultVal (outcomePoly (list nat * nat)) (outcomePoly (list nat))
               (noMatchPoly (list nat))
               (dispatchInternal (outcomePoly (list nat * nat)) (outcomePoly (list nat))
                  [fun v2 : outcomePoly (list nat * nat) =>
                   match v2 with
                   | @successPoly _ (a, b) => Some (successPoly (list nat) (b :: a))
                   | _ => None
                   end;
                   fun v2 : outcomePoly (list nat * nat) =>
                   match v2 with
                   | @fuelErrorPoly _ => Some (fuelErrorPoly (list nat))
                   | _ => None
                   end])
         end)
        (fun fuel : nat =>
         match fuel with
         | 0 => fuelErrorPolyCstFn (outcomePoly (list nat)) (nat * nat)
         | S _ =>
             defaultVal (outcomePoly (list nat)) (outcomePoly (nat * nat)) (noMatchPoly (nat * nat))
               (dispatchInternal (outcomePoly (list nat)) (outcomePoly (nat * nat))
                  [fun v2 : outcomePoly (list nat) =>
                   match v2 with
                   | @successPoly _ [c] => None
                   | @successPoly _ [c; d] => Some (successPoly (nat * nat) (c, d))
                   | @successPoly _ (c :: d :: _ :: _) => None
                   | _ => None
                   end;
                   fun v2 : outcomePoly (list nat) =>
                   match v2 with
                   | @fuelErrorPoly _ => Some (fuelErrorPoly (nat * nat))
                   | _ => None
                   end])
         end).

Compute (myFun 10 (successPoly (list nat * nat) ([5; 6], 2))).

Compute (myFun 10 (successPoly (list nat * nat) ([5], 2))).
*)

Definition composeOutcomePolyImpl {A : Type} {B : Type} {C : Type} (f : nat -> outcomePoly A -> outcomePoly B) (f' : nat -> outcomePoly B -> outcomePoly C)
                                   : (nat -> outcomePoly A -> outcomePoly C) :=
 fun fuel input => match f fuel input with
                    | successPoly res => f' fuel  (successPoly B res)
                    | fuelErrorPoly => (fuelErrorPoly C)
                    | _ =>  (noMatchPoly C)
                   end.
Print tmDefinition.
Compute (Some hnf).
Print tmDefinitionRed_.
Definition mkDeffromTpTm (kn : kername) (t : typed_term) : TemplateMonad unit :=
x <- tmEval hnf (my_projT2 t) ;;
tmDefinitionRed_ false (String.append (snd kn) "Animated") (Some hnf) x ;; ret tt.




Definition orientEquality (t : term) (orientation : nat) : term :=
 match t with
 | tApp <%eq%> [typeVar; t1; t2] => match orientation with
                                             | 0 => tApp <%eq%> [typeVar; t1; t2]
                                             | S m => tApp <%eq%> [typeVar; t2; t1]
                                             end
 | _ => t
 end.




Definition extractPatMatBinders5 {A : Type} (kn : kername) (induct : A) (inputData : list (string * term ))  (outputData : list (string * term )) (orientation : nat) (fuel : nat) : TemplateMonad unit :=
t' <- general.animate2 kn ;;
let t'' := orientEquality t' orientation in
t <- tmEval all t'' ;;
match t with
 | tApp <%eq%> [typeVar; patMatTerm; tApp (func) lst] =>
                      tIn <- joinPatMatPolyGenFuelAwareNoLHSTm induct (mkProdTmVars inputData) (mkProdTypeVars inputData) (tApp (func) lst) typeVar (String.append (snd kn) "IN") fuel ;;
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  patMatTerm typeVar  (mkProdTmVars outputData) (mkProdTypeVars outputData) (String.append (snd kn) "OUT") fuel ;;
                      (*
                      gIn <- tmUnquote tIn ;;
                      gIn' <- tmEval hnf (my_projT2 gIn) ;;
                      gOut <- tmUnquote tOut ;;
                      gOut' <- tmEval hnf (my_projT2 gOut) ;;


                      tmDefinition (String.append (snd kn) "Animated") (composeOutcomePolyImpl gIn' gOut')

                      *)




                      let u :=
                       (tApp <%composeOutcomePoly%> [(mkProdTypeVars inputData); typeVar ; (mkProdTypeVars outputData) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      (*tmPrint u';; *)

                      u' <- DB.deBruijn u ;;

                      ftypeIn <- tmUnquoteTyped Type (mkProdTypeVars inputData) ;;
                      ftypeOut <- tmUnquoteTyped Type (mkProdTypeVars outputData) ;;
                      (*
                      f <- tmUnquoteTyped (nat -> outcomePoly ftypeIn -> outcomePoly ftypeOut) u' ;;
                      (*
                      tmPrint f
                      *)
                      (*
                      @tmDefinition (String.append (snd kn) "Animated") (nat -> outcomePoly ftypeIn -> outcomePoly ftypeOut) (f)
                     *)
                     tmDefinition (String.append (snd kn) "Animated")  (f)
                     *)

                     f <- tmUnquote u';;
                     tmPrint f ;;
                     (* tmDefinition (String.append (snd kn) "Animated")  (f)
                     *)

                     tmEval hnf (my_projT2 f) >>=
                     tmDefinitionRed_ false (String.append (snd kn) "Animated") (Some hnf ) ;; ret tt



 | tApp <%eq%> [typeVar; patMatTerm; tVar str] =>
                      tIn <- joinPatMatPolyGenFuelAwareNoLHSTm induct (mkProdTmVars inputData) (mkProdTypeVars inputData) (tVar str) typeVar (String.append (snd kn) "IN") fuel ;;
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  patMatTerm typeVar  (mkProdTmVars outputData) (mkProdTypeVars outputData) (String.append (snd kn) "OUT") fuel ;;
                      (*
                      gIn <- tmUnquote tIn ;;
                      gIn' <- tmEval hnf (my_projT2 gIn) ;;
                      gOut <- tmUnquote tOut ;;
                      gOut' <- tmEval hnf (my_projT2 gOut) ;;


                      tmDefinition (String.append (snd kn) "Animated") (composeOutcomePolyImpl gIn' gOut')

                      *)




                      let u :=
                       (tApp <%composeOutcomePoly%> [(mkProdTypeVars inputData); typeVar ; (mkProdTypeVars outputData) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      (*tmPrint u';; *)

                      u' <- DB.deBruijn u ;;

                      ftypeIn <- tmUnquoteTyped Type (mkProdTypeVars inputData) ;;
                      ftypeOut <- tmUnquoteTyped Type (mkProdTypeVars outputData) ;;
                      (*
                      f <- tmUnquoteTyped (nat -> outcomePoly ftypeIn -> outcomePoly ftypeOut) u' ;;
                      (*
                      tmPrint f
                      *)
                      (*
                      @tmDefinition (String.append (snd kn) "Animated") (nat -> outcomePoly ftypeIn -> outcomePoly ftypeOut) (f)
                     *)
                     tmDefinition (String.append (snd kn) "Animated")  (f)
                     *)

                     f <- tmUnquote u';;
                     tmPrint f ;;
                     (* tmDefinition (String.append (snd kn) "Animated")  (f)
                     *)

                     tmEval hnf (my_projT2 f) >>=
                     tmDefinitionRed_ false (String.append (snd kn) "Animated") (Some hnf ) ;; ret tt




 | _ => tmFail "incorrect inductive shape"
end ;; tmMsg "done".

MetaRocq Run (extractPatMatBinders5 <? tlRel ?> tlRel [("a", <%list nat%>); ("b", <%nat%>)] [("c", <%nat%>); ("d", <%nat%>)] 0 50).

Print tlRelAnimated.

Definition extractPatMatBinders6 {A : Type} (kn : kername) (induct : A) (inputTm : term) (inputTp : term) (outputTm : term) (outputTp : term)  (orientation : nat) (fuel : nat) : TemplateMonad unit :=
t' <- general.animate2 kn ;;
let t'' := orientEquality t' orientation in
t <- tmEval all t'' ;;
match t with
 | tApp <%eq%> [typeVar; patMatTerm; tApp (func) lst] =>
                      tIn <- joinPatMatPolyGenFuelAwareNoLHSTm induct (inputTm) (inputTp) (tApp (func) lst) typeVar (String.append (snd kn) "IN") fuel ;;
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  patMatTerm typeVar  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;
                      (*
                      gIn <- tmUnquote tIn ;;
                      gIn' <- tmEval hnf (my_projT2 gIn) ;;
                      gOut <- tmUnquote tOut ;;
                      gOut' <- tmEval hnf (my_projT2 gOut) ;;


                      tmDefinition (String.append (snd kn) "Animated") (composeOutcomePolyImpl gIn' gOut')

                      *)




                      let u :=
                       (tApp <%composeOutcomePoly%> [(inputTp); typeVar ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      (*tmPrint u';; *)

                      u' <- DB.deBruijn u ;;
                     (*
                      ftypeIn <- tmUnquoteTyped Type (mkProdTypeVars inputData) ;;
                      ftypeOut <- tmUnquoteTyped Type (mkProdTypeVars outputData) ;;
                      (*
                      f <- tmUnquoteTyped (nat -> outcomePoly ftypeIn -> outcomePoly ftypeOut) u' ;;
                      (*
                      tmPrint f
                      *)
                      (*
                      @tmDefinition (String.append (snd kn) "Animated") (nat -> outcomePoly ftypeIn -> outcomePoly ftypeOut) (f)
                     *)
                     tmDefinition (String.append (snd kn) "Animated")  (f)
                     *)
                     *)
                     f <- tmUnquote u';;
                     tmPrint f ;;
                     (* tmDefinition (String.append (snd kn) "Animated")  (f)
                     *)

                     tmEval hnf (my_projT2 f) >>=
                     tmDefinitionRed_ false (String.append (snd kn) "Animated") (Some hnf ) ;; ret tt



 | tApp <%eq%> [typeVar; patMatTerm; tVar str] =>
                      tIn <- joinPatMatPolyGenFuelAwareNoLHSTm induct (inputTm) (inputTp) (tVar str) typeVar (String.append (snd kn) "IN") fuel ;;
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  patMatTerm typeVar  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;
                      (*
                      gIn <- tmUnquote tIn ;;
                      gIn' <- tmEval hnf (my_projT2 gIn) ;;
                      gOut <- tmUnquote tOut ;;
                      gOut' <- tmEval hnf (my_projT2 gOut) ;;


                      tmDefinition (String.append (snd kn) "Animated") (composeOutcomePolyImpl gIn' gOut')

                      *)




                      let u :=
                       (tApp <%composeOutcomePoly%> [(inputTp); typeVar ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      (*tmPrint u';; *)

                      u' <- DB.deBruijn u ;;
                     (*
                      ftypeIn <- tmUnquoteTyped Type (mkProdTypeVars inputData) ;;
                      ftypeOut <- tmUnquoteTyped Type (mkProdTypeVars outputData) ;;
                      (*
                      f <- tmUnquoteTyped (nat -> outcomePoly ftypeIn -> outcomePoly ftypeOut) u' ;;
                      (*
                      tmPrint f
                      *)
                      (*
                      @tmDefinition (String.append (snd kn) "Animated") (nat -> outcomePoly ftypeIn -> outcomePoly ftypeOut) (f)
                     *)
                     tmDefinition (String.append (snd kn) "Animated")  (f)
                     *)
                     *)
                     f <- tmUnquote u';;
                     tmPrint f ;;
                     (* tmDefinition (String.append (snd kn) "Animated")  (f)
                     *)

                     tmEval hnf (my_projT2 f) >>=
                     tmDefinitionRed_ false (String.append (snd kn) "Animated") (Some hnf ) ;; ret tt




 | _ => tmFail "incorrect inductive shape"
end ;; tmMsg "done".






(** ** Full Example: rel8/rel9
    Complete working example of mutually recursive predicates on pairs. *)

Inductive rel8: (nat * nat) -> (nat * nat)  -> Prop :=
 | rel8Base : forall a, rel8 (1, a) (3, S a)
 | rel8Cons : forall a1 a2 b1 b2 b3 b4, rel8 (a1, a2) (b1, b3) /\ rel9 (a1, a2) (b4, b2) -> rel8 ((S a1), (S a2)) ((S b1), (S b2))

with rel9: (nat * nat) -> (nat * nat)  -> Prop :=
 | rel9Cons : forall a b, rel8 a b  -> rel9 a b.

(** Helper: construct a successor term. *)
Definition tS (t : term) : term :=
 tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
         [t].

(** Helper: construct a pair term. *)
Definition tP (t : term) (t' : term) : term :=
tApp
         (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])
         [<%nat%>; <%nat%>; t;
          t'].

(** Clause data for rel8/rel9 animation. *)
Definition clData :=
[([], tP <%1%> (tVar "a"), <%prod nat nat%>, tP <%3%> (tS (tVar "a")), <%prod nat nat%>, ("rel8Base"));

([("rel8", tP (tVar "a1") (tVar "a2"), <%prod nat nat%> , tP (tVar "b1") (tVar "b3"), <%prod nat nat%>); ("rel9", tP (tVar "a1") (tVar "a2"), <%prod nat nat%> , tP (tVar "b4") (tVar "b2"), <%prod nat nat%>)],
 tP (tS (tVar "a1")) (tS (tVar "a2")), <%prod nat nat%>, tP (tS (tVar "b1")) (tS (tVar "b2")), <%prod nat nat%>, ("rel8Cons"));

([("rel8", tVar "a", <%prod nat nat%>, tVar "b", <%prod nat nat%>)], tVar "a", <%prod nat nat%>, tVar "b", <%prod nat nat%>, "rel9Cons")].

(** Inductive data for rel8/rel9 animation. *)
Definition indData :=
[("rel8", <%prod nat nat%>, <%prod nat nat%>, [("rel8Base", []); ("rel8Cons", ["rel8"; "rel9"])]);
  ("rel9", <%prod nat nat%>, <%prod nat nat%>, [("rel9Cons",["rel8"])])].

(** Animate the rel8/rel9 predicates. *)
MetaRocq Run (animateInductivePredicate rel8 "rel8" clData indData <? rel8 ?> 50).
Print rel8AnimatedTopFn.

Definition rel8AnimatedTopFn' :=
fix rel8AnimatedTopFn' (fuel : nat) (input : outcomePoly (nat × nat)) {struct fuel} :
    outcomePoly (nat × nat) :=
  match fuel with
  | 0 => fuelErrorPoly (nat × nat)
  | S remFuel =>
      dispatchOutcomePolyExt (nat × nat) (nat × nat)
        [rel8BaseAnimated; rel8ConsAnimated rel8AnimatedTopFn rel9AnimatedTopFn] remFuel input
  end
with rel9AnimatedTopFn (fuel : nat) (input : outcomePoly (nat × nat)) {struct fuel} :
    outcomePoly (nat × nat) :=
  match fuel with
  | 0 => fuelErrorPoly (nat × nat)
  | S remFuel =>
      dispatchOutcomePolyExt (nat × nat) (nat × nat) [(fun g x y => g x y) rel8AnimatedTopFn] remFuel input
  end
with dispatchOutcomePolyExt
  (A B : Type) (lst : list (nat -> outcomePoly A -> outcomePoly B)) (fuel' : nat)
  (input' : outcomePoly A) {struct fuel'} : outcomePoly B :=
  match fuel' with
  | 0 => fuelErrorPoly B
  | S remFuel' =>
      match lst with
      | [] => noMatchPoly B
      | h :: t =>
          match h remFuel' input' with
          | @noMatchPoly _ => dispatchOutcomePolyExt A B t remFuel' input'
          | _ => h remFuel' input'
          end
      end
  end
for
rel8AnimatedTopFn'
     : nat -> outcomePoly (nat × nat) -> outcomePoly (nat × nat).

Print rel9ConsAnimated.

Compute rel9ConsAnimated rel8AnimatedTopFn 10 (successPoly (nat * nat) (2,4)).
Compute rel8AnimatedTopFn 9 (successPoly (nat * nat) (2,4)).

Compute (rel8AnimatedTopFn' 50 (successPoly (nat * nat) (7,9))).
Compute (rel8AnimatedTopFn' 100 (successPoly (nat * nat) (8,13))).


Compute (rel8AnimatedTopFn 70 (successPoly (nat * nat) (9,13))).
(*Takes very long
Compute (rel8AnimatedTopFn 70 (successPoly (nat * nat) (12,14))).
*)

Lemma testrel8 : True -> rel8 (7,9) (9,10) .
Proof. intro. Admitted.

Lemma testrel8' : True -> rel8 (8,13) (10,14).
Proof. Admitted.

Lemma testrel8'' : True -> rel8 (9,13) (11,14).
Proof. Admitted.

(** ** Mode-Based Animation
    This section implements animation with explicit input/output modes,
    allowing fine-grained control over which arguments are inputs vs outputs. *)

(** Example: rel28 with explicit modes.
    Mode: rel28 : [0 ; 2] input, [1; 3] output
          rel29 : [0;1] input, [2;3] output *)

Inductive rel28: nat -> nat -> nat -> nat -> Prop :=
 | rel28Base : forall a, rel28 1 3 a (S a)
 | rel28Cons : forall a1 a2 b1 b2 b3 b4, rel28 a1 b1 a2 b3 /\ rel29 a1 a2 b4 b2 -> rel28 (S a1) (S b1) (S a2) (S b2)
with rel29: nat -> nat -> nat -> nat -> Prop :=
 | rel29Cons : forall a b c d, rel28 a c b d  -> rel29 a b c d.

(** Quote rel28 for inspection. *)
MetaRocq Run (mut <- tmQuoteInductive <? rel28 ?> ;; tmPrint mut ;; tmDefinition "mutB" mut).

(** Error term for partial type functions. *)
Parameter errTpTm : term.

(** Extract inductive names from bodies. *)
Definition getIndNames (l : list one_inductive_body) :=
map (fun o => ind_name o) l.

(** Generate context from inductive names. *)
Definition genCxt (l : list one_inductive_body) :=
(map (fun s => nNamed s) (rev (getIndNames l))).

(** Extract all argument types from an inductive type. *)
Fixpoint getType (o : term) : list term :=
match o with
       | (tProd {| binder_name := nAnon; binder_relevance := Relevant |} t (tSort sProp)) => [t]
       | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1  t2 => t1 :: getType t2
       | _ => [errTpTm]
end.

(** Select types according to mode indices. *)
Definition getType' (mode : list nat) (l : list term) :=
map (fun n => nth n l errTpTm) mode.

(** Build product type from list of types (mode-based version). *)
Fixpoint mkProdTypeVars3 (outputData : list (term)) :  term :=
 match outputData with
  | [] => <%bool%>
  | [h] =>  (h)
  | h :: t => let res := mkProdTypeVars3 t in  (tApp
                                            (tInd
                                             {|
                                             inductive_mind := <?prod?>; inductive_ind := 0
                                              |} []) [(h) ; res])
 end.

(** Get input type according to mode. *)
Definition getInTp (inMode : list nat) (o : one_inductive_body) : term  :=
 let lstType := getType (ind_type o) in
 mkProdTypeVars3 (getType' inMode lstType).

(*
Definition getInTp (n : nat) (o : one_inductive_body) :=
match n with
 | 0 => match ind_type o with
         | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1  t2 => t1
         | _ => errTpTm
         end
 | S m => match ind_type o with
           | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1  t2 => match t2 with
                                                                                       |  tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1'  t2' => t1'

                                                                                       | _ => errTpTm
                                                                                       end

           | _ => errTpTm
          end
end.
*)
(*
Definition getOutTp (n : nat) (o : one_inductive_body) :=
 match n with
  | 0 => getInTp 1 o
  | S m => getInTp 0 o
 end.
 *)
(** Strip all top-level foralls/products from a term to get to the body. *)
Fixpoint reduceClauseTm (t : term) :=
 match t with
  | (tPro str typ t') => reduceClauseTm t'
  | t'' => t''
 end.

(** Extract preconditions (hypotheses) from a constructor clause. *)
Definition getPreCons (t : term) :=
match t with
 | (tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2) => [t1]
 | _ => []
end.

(** Process preconditions, splitting conjunctions. *)
Definition processPreCon (l : list term) :=
match l with
 | [] => []
 | [tApp <%and%> l'] => l'
 | [t'] => [t']
 | _ :: (h' :: _) => []
end.

(** Get the body (recursive premises) of a constructor clause. *)
Definition getClBody' (t : term) : list term :=
processPreCon (getPreCons (reduceClauseTm t)).

(** Get the head (conclusion) of a constructor clause. *)
Definition getClHead' (t : term) : term :=
 match reduceClauseTm t with
  | (tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2) => t2
  | t' => t'
 end.

(** Extract body from a constructor. *)
Definition getClBody (c : constructor_body) : list term :=
 getClBody' (cstr_type c).

(** Extract head from a constructor. *)
Definition getClHead (c : constructor_body) :  term :=
 getClHead' (cstr_type c).

(** Check if a string is in a list of strings. *)
Fixpoint inStrLst'' (s : string) (l1 : list string) : bool :=
  match l1 with
  | [] => false
  | h :: t => if String.eqb s h then true else inStrLst'' s t
  end.

(** Extract names of inductive predicates applied in a list of terms. *)
Fixpoint getIndApp (l : list term) (indNames : list string) : list string :=
 match l with
  | [] => []
  | h :: t => match h with
              | tApp (tVar str) args => if (inStrLst'' str indNames) then (str :: (getIndApp t indNames)) else (getIndApp t indNames)
              | _ => (getIndApp t indNames)
              end
 end.

(** Get input/output types for all inductives according to mode specifications. *)
Fixpoint getInOutTps (l : list (prod (list nat) (list nat))) (b : list one_inductive_body) : list ((string * term) * term) :=
 match l with
  | [] => []
  | h :: t => match b with
               | h' :: t' => (ind_name h', getInTp (fst h) h', getInTp (snd h) h') :: getInOutTps t t'
               | _ => []
              end
 end.

(** Change the next 2 functions to not always return the full clause data but only bits of it **)
Fixpoint mkNmTm (c : list constructor_body) (l : list name) :TemplateMonad (list (string * term)) :=
 match c with
  | [] => tmReturn []
  | (h :: t) => r <- DB.undeBruijn' l ((cstr_type h )) ;; r' <- tmEval all r ;; let hres := (cstr_name h, (reduceClauseTm r')) in rest <- mkNmTm t l ;; tmReturn (hres :: rest)
 end.


Fixpoint getData (lib : list one_inductive_body) (ln : list (prod (list nat) (list nat))) (nmCxt : list name) (inOutTps : list ((string * term) * term)) : TemplateMonad (list (((string * term) * term) * (list (string * term))))  :=

 match lib with
  | [] => tmReturn []
  | h' :: t' => match inOutTps with
                 | h :: t => dbth <- mkNmTm (ind_ctors h') nmCxt ;; rest <- getData t' (tl ln) nmCxt (tl inOutTps) ;; tmReturn ((h, dbth) :: rest)
                 | _ => tmReturn []
                 end

 end.
(* Change above 2 functions *)
Definition getData' (kn : kername) (ln : list (prod (list nat) (list nat))) : TemplateMonad (list (((string * term) * term) * (list (string * term))))  :=
mut <- tmQuoteInductive kn ;;
tmPrint mut ;;
let lib := ind_bodies mut in
let nmCxt := genCxt lib in
let inOutTps := getInOutTps ln lib in
getData lib ln nmCxt inOutTps.

MetaRocq Run (g <- getData' <? rel28 ?> [([0;2], [1;3]); ([0;1],[2;3])] ;; tmDefinition "data" g).

Compute (data).

Fixpoint getIndApp' (l : list (string * term)) (indNames : list string) : list (string * (list string)) :=
 match l with
  | [] => []
  | h :: t => (fst h, getIndApp (getClBody' (snd h)) indNames) :: getIndApp' t indNames
 end.

Fixpoint mkIndData (data : (list (((string * term) * term) * (list (string * term))))) (indNames : list string) :=
 match data with
  | [] => []
  | h :: t => match h with
               | (nm, inT, outT, lCons) => (nm, inT, outT, (getIndApp' lCons indNames)) :: mkIndData t indNames
              end
 end.

Definition mkIndData' (kn : kername) (ln : list (prod (list nat) (list nat))) :=
mut <- tmQuoteInductive kn ;;
let lib := ind_bodies mut in
let nmCxt := genCxt lib in
let inOutTps := getInOutTps ln lib in
data <- getData lib ln nmCxt inOutTps ;;
let indNames := map (fun d => (fst (fst (fst d)))) data in
tmReturn (mkIndData data indNames).

MetaRocq Run (inData <- mkIndData' <? rel28 ?> [([0;2], [1;3]); ([0;1],[2;3])] ;; tmDefinition "indInf" inData).

Compute indInf.

Fixpoint findIndex (s : string) (ls : list (((string * term) * term) * (list nat * list nat))) : option (list nat * list nat) :=
 match ls with
  | [] => None
  | (h :: t) => if (String.eqb s (fst (fst (fst h)))) then Some (snd h) else findIndex s t
 end.
Fixpoint findInType (s : string) (ls : list (((string * term) * term) * (list nat * list nat))) : option term :=
match ls with
  | [] => None
  | (h :: t) => if (String.eqb s (fst (fst (fst h)))) then Some (snd (fst (fst h))) else findInType s t
end.
(* ls is (nameOfInductive, inputType, outputType, modeInfo) *)
Fixpoint findOutType (s : string) (ls : list (((string * term) * term) * (list nat * list nat))) : option term :=
match ls with
  | [] => None
  | (h :: t) => if (String.eqb s (fst (fst (fst h)))) then Some ((snd (fst h))) else findOutType s t
end.

Definition mkProdTm3Helper (mode : list nat) (lsArgs : list term) : (list term) :=
map (fun n => nth n lsArgs errTpTm) mode.

Compute <% (true, (0,0))%>.

Fixpoint mkProdTm3' (lsArgs : list term) (tpTm : term) : term :=
match lsArgs with
 | [] => <%true%>
 | [h] => h
 | h' :: t => match tpTm with
               | (tApp <%prod%> [(tp1) ; res]) => tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0
                                                                                  |} 0 []) [tp1 ; res; h' ; (mkProdTm3' t res)]

               | _ => errTpTm
              end
 end.






Definition mkProdTm3 (mode : list nat) (lsArgs : list term) (tpTm : term) : term :=
mkProdTm3' (mkProdTm3Helper mode lsArgs) tpTm.
Fixpoint extractClinfo (ts : list term) (ls : list (((string * term) * term) * (list nat * list nat)))
                              : list ((((string * term) * term) * term) * term)  :=
(* output is list of (inductiveNm, inputTerm, inputType, outputTerm, outputType) one tuple per conjunct in precondition *)
match ts with
| [] => []
| h :: rest => match h with
                | tApp (tVar str) lstArgs => match findIndex str ls with
                                                | Some mode => match findInType str ls with
                                                             | Some tp => match findOutType str ls with
                                                                           | Some tp' => (str, (mkProdTm3 (fst mode) lstArgs tp), tp, (mkProdTm3 (snd mode) lstArgs tp'), tp') :: extractClinfo rest ls
                                                                           | _ => extractClinfo rest ls
                                                                           end
                                                             | _ => extractClinfo rest ls
                                                             end





                                                | _ => extractClinfo rest ls
                                               end

                | _ => extractClinfo rest ls
               end

end.

Parameter noClHdError :((((term) * term) * term) * term).

Definition extractClinfoHd (h : term) (ls : list (((string * term) * term) * (list nat * list nat)))
                              : ((((term) * term) * term) * term) :=
                match h with
                | tApp (tVar str) lstArgs => match findIndex str ls with
                                                | Some mode => match findInType str ls with
                                                             | Some tp => match findOutType str ls with
                                                                           | Some tp' => ((mkProdTm3 (fst mode) lstArgs tp), tp, (mkProdTm3 (snd mode) lstArgs tp'), tp')
                                                                           | _ => noClHdError
                                                                           end
                                                             | _ => noClHdError
                                                             end





                                                | _ => noClHdError
                                               end

                | _ => noClHdError
               end.

Definition mkClauseInfo  (ls : list (((string * term) * term) * (list nat * list nat))) (cl : (string * term)) :=
 match extractClinfoHd (getClHead' (snd cl)) ls with
  | (t1, t2, t3, t4) => ((extractClinfo (getClBody' (snd cl)) ls), t1, t2, t3, t4, (fst cl))
 end.

Fixpoint mkClauseInfoLst  (ls : list (((string * term) * term) * (list nat * list nat))) (clist : list (string * term)) :=
 match clist with
  | [] => []
  | h :: t => (mkClauseInfo ls h) :: mkClauseInfoLst ls t
 end.

Fixpoint appendIndex (ln : list (list nat * list nat)) (ls : list (((string * term) * term))) :=
match ln with
 | [] => []
 | h :: t => match ls with
             | [] => []
             | h' :: t' => match h' with
                            | (p1,p2,p3) => (p1,p2,p3,h) :: appendIndex t t'
             end            end
end.
(*
Check mkClauseInfo.

Search (forall A : Type, list (list A) -> list A).
*)
Search (string -> string -> string).
Definition mkClData' (kn : kername) (ln : list (list nat * list nat)) :=
mut <- tmQuoteInductive kn ;;
let lib := ind_bodies mut in
let nmCxt := genCxt lib in
let inOutTps := getInOutTps ln lib in
myData <- getData lib ln nmCxt inOutTps ;;
myData' <- tmEval all myData;;
tmDefinition (String.append (snd kn) "myData'") myData' ;;
let ls' := getInOutTps ln lib in
let ls'' := appendIndex ln ls' in
ls <- tmEval all ls'' ;;
(*tmPrint ls ;; *)
let lislisCons := map (fun p => snd p) myData in
let lisCons' := concat lislisCons in
lisCons <- tmEval all lisCons' ;;
(*tmPrint lisCons ;;*)

tmReturn (mkClauseInfoLst ls lisCons).


Definition animateInductivePredicate' {A : Type} (induct : A) (nm : string) (kn : kername) (modelst: list (list nat * list nat) ) (fuel : nat) :=
clData <- mkClData' kn modelst ;;
clData' <- tmEval all clData ;;
indData <- mkIndData' kn modelst ;;
indData' <- tmEval all indData ;;
animateInductivePredicate induct nm clData' indData' kn fuel.
(*
MetaRocq Run (clData <- mkClData' <? rel8 ?> [0;0] ;; tmDefinition "clInf" clData).

Compute clInf.
*)
(* MetaRocq Run (animateInductivePredicate rel8 "rel8" clData indData 50). *)





Definition tmHd {A : Type} (lst : list A) : (TemplateMonad A) :=
 match lst with
  | h :: rest => tmReturn h
  | _ => tmFail "no head of empty list"
  end.

Parameter datHdDef : (((((list ((((string * term) * term) * term) * term) * term) * term) * term) * term) * string).
Definition extractPatMatBinders7 {A : Type} (kn : kername) (induct : A) (mode :list (prod (list nat) (list nat))) (orientation : nat) (fuel : nat) : TemplateMonad unit :=
 d <- mkClData' kn mode ;;
 let elt := hd datHdDef d in
 let inputTm := snd (fst (fst (fst (fst elt)))) in
 let inputTp := snd ((fst (fst (fst elt)))) in
 let outputTm := snd (((fst (fst elt)))) in
 let outputTp := snd (((fst (elt)))) in
 extractPatMatBinders6 (kn) (induct) (inputTm) (inputTp) (outputTm) (outputTp)  (orientation) (fuel).



(** Examples  _______________ **)


Definition getIndRHSVar'' (lst : list (string * term)) : list term :=
 match lst with
  | [] => []
  | h :: t => match snd h with
               | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1'  (tApp t1 lst')  => lst'

               | _ => []
              end

 end.
Definition getIndRHSVar0 (lst : list (((string * term) * term) * list (string * term))) : list (string * term) :=
 match lst with
  | [] => []
  | h :: t =>  snd h

 end.

Check concat.
Check nth.


Fixpoint getIndRHSVar3 (t : term) : list string :=
match t with
 | tVar str => [str]
 | tApp fn lst => concat (map getIndRHSVar3 lst)
 | _ => []
end.

Definition getIndRHSVar4 (lst : list term) : list string :=
concat (map getIndRHSVar3 lst).

Fixpoint getIndRHSVar (lst : list (((string * term) * term) * list (string * term))) (ln : list nat) : list string :=
match ln with
 | [] => []
 | h :: t => (nth h (getIndRHSVar4 (getIndRHSVar'' (getIndRHSVar0 lst))) "defaultVar") :: getIndRHSVar lst t
end.














Module animateEqual.
Compute <%list nat%>.
Parameter y : nat.
Parameter ys : list nat.
Compute <% (y,ys) %>.
Fixpoint eqLstNat (l1 : list nat) (l2 : list nat) : bool :=
 match l1 with
  | [] => match l2 with
          | [] => true
          | _ => false
          end
  | (h :: t) => match l2 with
                 | [] => false
                 | (h' :: t') => if (Nat.eqb h h') then eqLstNat t t' else false
                end
  end.

Definition typeToBoolEq (t : term) : term :=
 match t with
  | (tInd {| inductive_mind := <?nat?>; inductive_ind := 0 |} []) => <%Nat.eqb%>
  | <%bool%> => <%Bool.eqb%>
  | (tApp
         (tInd
            {|
              inductive_mind := <?list?>; inductive_ind := 0
            |} [])
         [<%nat%>]) => <%eqLstNat%>
  | _ => <% (false) %>
 end.

Definition chkEqType (t : term) : bool :=
  match t with
  | (tInd {| inductive_mind := <?nat?>; inductive_ind := 0 |} []) => true
  | <%bool%> => true
  | (tApp
         (tInd
            {|
              inductive_mind := <?list?>; inductive_ind := 0
            |} [])
         [<%nat%>]) => true
  | _ => false
 end.

Parameter inValidConj : term.


Fixpoint inNatLst (a : nat) (l : list nat) : bool :=
 match l with
  | nil => false
  | (h :: t) => if (Nat.eqb h a) then true else (inNatLst a t)
 end.




Fixpoint isListSub (l1 l2 : list nat) : bool :=
  match l1 with
  | [] => true
  | h :: t => inNatLst h l2 && isListSub t l2
  end.

Fixpoint inStrLst (s : string) (l1 : list string) : bool :=
  match l1 with
  | [] => false
  | h :: t => if String.eqb s h then true else inStrLst s t
  end.

Fixpoint isListSubStr (l1 l2 : list string) : bool :=
  match l1 with
  | [] => true
  | h :: t => inStrLst h l2 && isListSubStr t l2
  end.


Check @fst.
(*
Fixpoint splitBigConj (bigConj : term) : list term :=
 | tApp <%and%> ls =>  concat (map splitBigConj ls)

  | tApp <%eq%> [typeT; tApp
         (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])[tp1; tp2; tm1; tm2] ; t'] => (tApp <%eq%> [tp1; tm1; tApp <%@fst%> [tp1;tp2;t']])  (getListConjLetBind (tApp <%eq%> [tp2; tm2; tApp <%@snd%> [tp1;tp2;t']]))
*)
(* Extracts list of conjuncts from big conjunction *)
Fixpoint getListConjLetBind (bigConj : term) : list term :=

     match bigConj with
     | tApp <%and%> ls => concat (map (getListConjLetBind) ls)

   (*  | tApp <%eq%> [typeT; tApp
         (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])[tp1; tp2; tm1; tm2] ; tApp
         (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])[tp1'; tp2'; tm1'; tm2'] ] => app (getListConjLetBind (tApp <%eq%> [tp1; tm1; tm1']))  (getListConjLetBind (tApp <%eq%> [tp2; tm2; tm2']))  *)

   (*  | tApp <%eq%> [typeT; t'; tApp
         (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])[tp1; tp2; tm1; tm2]] => app (getListConjLetBind m (tApp <%eq%> [tp1; tm1; tApp <%@fst%> [tp1;tp2;t']]))  (getListConjLetBind m (tApp <%eq%> [tp2; tm2; tApp <%@snd%> [tp1;tp2;t']]))  *)

     | tApp <%eq%> [typeT; tVar str1; tVar str2] => [tApp <% @eq %> [typeT; tVar str1; tVar str2]]

     | tApp <%eq%> [typeT; tVar str1; tApp fn lst] =>
      [tApp <%eq%> [typeT; tVar str1; tApp fn lst]]

     | tApp <%eq%> [typeT; tApp fn lst; tVar str1] =>
      [tApp <%eq%> [typeT; tApp fn lst; tVar str1]]

     | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>
      [tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst]]

     | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] =>
      [tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1]]




  (*| tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2]] =>
      [tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2]]] *)
     | _ => []
     end.


(*
Fixpoint splitBigConj (fuel : nat) (bigConj : term) : list term :=
 match fuel with
  | 0 => [bigConj]
  | S m  =>
     match bigConj with
     | tApp <%and%> ls => concat (map (splitBigConj m) ls)

    (* | tApp <%eq%> [typeT; tApp
         (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])[tp1; tp2; tm1; tm2] ; t'] => app (splitBigConj m (tApp <%eq%> [tp1; tm1; tApp <%@fst%> [tp1;tp2;t']]))  (splitBigConj m (tApp <%eq%> [tp2; tm2; tApp <%@snd%> [tp1;tp2;t']]))  *)

     | tApp <%eq%> [typeT; t'; tApp
         (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])[tp1; tp2; tm1; tm2]] => app (getListConjLetBind m (tApp <%eq%> [tp1; tm1; tApp <%@fst%> [tp1;tp2;t']]))  (getListConjLetBind m (tApp <%eq%> [tp2; tm2; tApp <%@snd%> [tp1;tp2;t']]))

     | t => [t]
     end
 end.
*)
(*
Fixpoint andSplit (l : list term) : list term :=
match l with
 | [] => []
 | (tApp <%and%> ls) :: rest => app ls (andSplit rest)
 | ls' => ls'
end.

Fixpoint prodSplitL (l : list term) : list term :=
 match l with
  | [] => []
  | tApp <%eq%> [typeT; tApp
         (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])[tp1; tp2; tm1; tm2] ; t'] :: rest =>  (tApp <%eq%> [tp1; tm1; tApp <%@fst%> [tp1;tp2;t']]) ::  (tApp <%eq%> [tp2; tm2; tApp <%@snd%> [tp1;tp2;t']]) :: prodSplitL rest
  | l' => l'
end.

Fixpoint prodSplitR (l : list term) : list term :=
 match l with
  | [] => []
  | tApp <%eq%> [typeT; t'; tApp
         (tConstruct
            {|
              inductive_mind := <?prod?>; inductive_ind := 0
            |} 0 [])[tp1; tp2; tm1; tm2]] :: rest =>  (tApp <%eq%> [tp1; tm1; tApp <%@fst%> [tp1;tp2;t']]) ::  (tApp <%eq%> [tp2; tm2; tApp <%@snd%> [tp1;tp2;t']]) :: prodSplitR rest
  | l' => l'
end.
(*
Fixpoint removeTaut (l : list term) : list term :=
match l with
| [] => []
| tApp <%eq%> [typeT ; tVar str1 ; tVar str2]

*)
*)
(* extract list of conjuncts from big conjunction *)
Fixpoint getListConjGuardCon (bigConj : term) : list term :=
  match bigConj with
  | tApp <%and%> ls => concat (map getListConjGuardCon ls)
  | tApp <%eq%> [typeT; t1; t2] =>
      [tApp <%eq%> [typeT; t1; t2]]

  | tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs => [tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs]
  
  | _ => []
 end.

Definition getListConjAll (bigConj : term) : list term :=
  match bigConj with
  | tApp <%and%> ls => concat (map getListConjGuardCon ls)
  | tApp <%eq%> [typeT; t1; t2] =>
      [tApp <%eq%> [typeT; t1; t2]]
  | tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs => [tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs]
  | _ => []
 end.

Fixpoint filterListConj (bigConj : term) : list bool :=
 match bigConj with
  | tApp <%and%> ls => concat (map filterListConj ls)

  | tApp <%eq%> [typeT; tVar str1; tVar str2] => [chkEqType typeT]

  | tApp <%eq%> [typeT; tVar str1; tApp fn lst] =>
      [chkEqType typeT]

  | tApp <%eq%> [typeT; tApp fn lst; tVar str1] =>
      [chkEqType typeT]

  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>
      [chkEqType typeT]

  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] =>
      [chkEqType typeT]


  | tApp <%eq%> [typeT; tApp fn1 lst1; tApp fn2 lst2] =>
      [chkEqType typeT]
  | tApp <%eq%> [typeT; tApp fn1 lst1; tConstruct ind_type k lst] =>
      [chkEqType typeT]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tApp fn1 lst1] =>
      [chkEqType typeT]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tConstruct ind_type2 k2 lst2] =>
      [chkEqType typeT]
  | _ => [false]
 end.

Fixpoint checkBool (lst : list bool) : bool :=
 match lst with
 | [] => true
 | h :: t => andb h (checkBool t)
end.






(*Compute (getListConjGuardCon fooTerm).*)

Fixpoint extractOrderedVarsHelper (ls : list term) : list string :=
 match ls with
 | [] => []
 | (tVar str) :: t => str :: (extractOrderedVarsHelper t)
 | _ :: t => (extractOrderedVarsHelper t)
 end.

Print Instance.t.



(* extract ordered list of vars from conjunct *)
Fixpoint extractOrderedVars (t : term) : list string :=
  match t with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => [str1 ; str2]
  | tApp <%eq%> [typeT; tVar str1; tApp fn lst] => str1 :: extractOrderedVarsHelper (lst)
  | tApp <%eq%> [typeT; tApp fn lst; tVar str1] => app (extractOrderedVarsHelper (lst)) [str1]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] => [str1]
  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>  [str1]

  (* Combine the pattern matches to handle fns of arbitrary arity *)

  | tVar str  => [str]
  | tApp _ lst => concat (map extractOrderedVars lst)
  | _ => []
  end.


(* Instantiate partialLetFun with identity *)

(* EDIT TO HANDLE CASE OF tuple of vars = blah.. *)

Definition animateOneConjSucc (conj : term) (partialLetfn : term -> term) : option (term -> term) :=
  match conj with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1; binder_relevance := Relevant |}
                                 (tVar str2) typeT) t))

  (*| tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2; tVar str3; tVar str4; tVar str5 ]] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn [tVar str2; tVar str3; tVar str4; tVar str5]) <%nat%>) t)) *)

  (*| tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2]] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn [tVar str2]) <%nat%>) t)) *)
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

Fixpoint animateOneConjSuccRec (conjs : list term) (partialLetfn : term -> term) : option (term -> term) :=
 match conjs with
  | [] => Some partialLetfn
  | h :: t => match animateOneConjSucc h partialLetfn with
               | Some partialLetfn' => animateOneConjSuccRec t partialLetfn'
               | _ => None
              end
 end.


Parameter noTerm : term.
Check nth.
(* return indicies of non Type args of typeCon and their types *)
Definition returnConsArgs (typeCon : term) : TemplateMonad (list (prod nat term)). Admitted.

(* return the list of functions that destruct a typeCon and return the ith argument *)
Definition returnDestructor (typeCon : term) (argIndex : list (nat)) : TemplateMonad (list term). Admitted.

Definition reduceTypConOne (conj : term) (argIndex : list nat) (invFnRetType :  list term) (invFnTm : list term) : list term :=
match conj with
 | (tApp <%eq%> [tp; t1 ; tApp (tConstruct indInfo k lst) lstArgs]) => map (fun index => ((tApp <%eq%> [(nth index invFnRetType noTerm); tApp (nth index invFnTm noTerm) [t1] ; nth index lstArgs noTerm]))) argIndex
 | t => [t]
end.

Definition reduceTypCon' (conj : term) : TemplateMonad (list term) :=
match conj with
 | (tApp <%eq%> [tp; t1 ; tApp (tConstruct indInfo k lst) lstArgs]) => argIndexTp <- returnConsArgs (tConstruct indInfo k lst) ;;
                                                                       let argIndex := map fst argIndexTp in
                                                                       let invFnRetType := map snd argIndexTp in
                                                                       invFnTm <- returnDestructor (tConstruct indInfo k lst) argIndex ;;
                                                                       tmReturn (reduceTypConOne conj argIndex invFnRetType invFnTm)
 | t => tmReturn [t]
end.

Fixpoint reduceTypCon (conjs : list term)  : TemplateMonad (list term) :=
match conjs with
 | [] => tmReturn []
 | h :: t => lsh <- reduceTypCon' h ;; lst <- reduceTypCon t ;; tmReturn (app lsh lst)
end.

Fixpoint reduceTypeConIter' (conjs : list term) (fuel : nat) : TemplateMonad (list term) :=
match fuel with
 | 0 => tmReturn conjs
 | S m => newConjs <- reduceTypCon conjs ;; reduceTypeConIter' newConjs m
end.

Definition reduceTypeConIter (conj : term) (fuel : nat) : TemplateMonad (list term) :=
reduceTypeConIter' [conj] fuel.

Fixpoint chkFullInv (conjs : list term) : TemplateMonad (list term) :=
 match conjs with
  | [] => tmReturn []
  | h :: t => match h with
               | (tApp <%eq%> [tp; t1 ; tApp (tConstruct indInfo k lst) lstArgs]) => tmFail "constructor not fully inverted"
               | _ => rest <- chkFullInv t ;; tmReturn (h :: rest)
              end
 end.



Definition flipConj (conj : term) : term :=
 match conj with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => tApp <%eq%> [typeT; tVar str2; tVar str1]
  | tApp <%eq%> [typeT; tApp fn lstTerm; tVar str1] => tApp <%eq%> [typeT; tVar str1; tApp fn lstTerm]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] => tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst]
  | t' => t'
 end.

(* Instantiate partialGuard with Identity * No need to check for known vars when animating guard condition since all
vars should be known at this point in the computation *)

 Definition animateOneConjSuccGuard (conj : term) (partialGuard : term)  :  term :=
  match conj with
  | tApp <%eq%> [typeT; t1; t2] =>
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (typeToBoolEq typeT) [t1
         ; t2]]
(* | tApp <%eq%> [typeT; tApp fn1 lst1; tConstruct ind_type k lst] =>
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (typeToBoolEq typeT) [tApp fn1 lst1
         ; tConstruct ind_type k lst]]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tApp fn1 lst1] =>
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (typeToBoolEq typeT) [tApp fn1 lst1
         ; tConstruct ind_type k lst]]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tConstruct ind_type2 k2 lst2] =>
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (typeToBoolEq typeT) [tConstruct ind_type2 k2 lst2
         ; tConstruct ind_type k lst]]  *)
  | _ => <% false %>
  end.
(*Change this to add a recursive case for first inverting constructor application and then handling the resulting conjs normally *)

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

(* NOT COMPILING : GIVES UNIVERSE ERROR
Definition animateOneConjNew (conj : term) (knownVar : list string) (partialProg : term -> term) (fuel : nat) : TemplateMonad (option (list string * (term -> term))) :=
  match conj with
   | (tApp <%eq%> [tp; t1 ; tApp (tConstruct indInfo k lst) lstArgs]) => if isListSubStr (extractOrderedVars t1) knownVar then
                                                                           conjs <- reduceTypeConIter conj fuel ;;
                                                                           conjs' <- chkFullInv conjs;;
                                                                           (let t' := animateOneConjSuccRec conjs' partialProg in
                                                                            match t' with
                                                                            | Some t'' => tmReturn (Some (app knownVar (extractOrderedVars conj), t''))
                                                                            | None => tmReturn (None)
                                                                             end)
                                                                           else
                                                                           match conj with
                                                                            | (tApp <%eq%> [tp; tApp (tConstruct indInfo' k' lst') lstArgs' ; t1']) => if isListSubStr (extractOrderedVars t1') knownVar then
                                                                                                                                                   let conj' := (tApp <%eq%> [tp; t1'; tApp (tConstruct indInfo' k' lst') lstArgs']) in
                                                                                                                                                   conjs <- reduceTypeConIter conj' fuel ;;
                                                                                                                                                   conjs' <- chkFullInv conjs;;
                                                                                                                                                   (let t' := animateOneConjSuccRec conjs' partialProg in
                                                                                                                                                    match t' with
                                                                                                                                                    | Some t'' => tmReturn (Some (app knownVar (extractOrderedVars conj), t''))
                                                                                                                                                    | None => tmReturn (None)
                                                                                                                                                    end)
                                                                                                                                                    else tmReturn None
                                                                            | _ => tmReturn None
                                                                           end



(*

   | (tApp <%eq%> [tp; tApp (tConstruct indInfo k lst) lstArgs; t1]) => if isListSubStr (extractOrderedVars t1) knownVar then
                                                                           let conj' := (tApp <%eq%> [tp; t1; tApp (tConstruct indInfo k lst) lstArgs]) in
                                                                           conjs <- reduceTypeConIter conj' fuel ;;
                                                                           conjs' <- chkFullInv conjs;;
                                                                           (let t' := animateOneConjSuccRec conjs' partialProg in
                                                                            match t' with
                                                                            | Some t'' => tmReturn (Some (app knownVar (extractOrderedVars conj), t''))
                                                                            | None => tmReturn (None)
                                                                             end)
                                                                           else
                                                                           match conj with
                                                                            | (tApp <%eq%> [tp; t1'; tApp (tConstruct indInfo' k' lst') lstArgs' ]) => if isListSubStr (extractOrderedVars t1') knownVar then
                                                                                                                                                   conjs <- reduceTypeConIter conj fuel ;;
                                                                                                                                                   conjs' <- chkFullInv conjs;;
                                                                                                                                                   (let t' := animateOneConjSuccRec conjs' partialProg in
                                                                                                                                                    match t' with
                                                                                                                                                    | Some t'' => tmReturn (Some (app knownVar (extractOrderedVars conj), t''))
                                                                                                                                                    | None => tmReturn (None)
                                                                                                                                                    end)
                                                                                                                                                    else tmReturn None
                                                                            | _ => tmReturn None
                                                                           end
*)

   | _ => if isListSubStr (tl (extractOrderedVars conj)) knownVar then
          (let t' := animateOneConjSucc conj partialProg in
            match t' with
            | Some t'' => tmReturn (Some (app knownVar (extractOrderedVars conj), t''))
            | None => tmReturn None
            end)
          else (if isListSubStr (tl (extractOrderedVars (flipConj conj))) knownVar then
          (let t' := animateOneConjSucc (flipConj conj) partialProg in
           match t' with
            | Some t'' => tmReturn (Some (app knownVar (extractOrderedVars (flipConj conj)), t''))
            | None => tmReturn (None)
           end)
         else tmReturn None)
end.


*)

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


Definition constrRetBodylst (outputTm : term) (outputTp : term) : term :=
 tApp <% @Some %> [outputTp; outputTm].

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

(*

Fixpoint animateOneConjGuardList (conj : list term) : term :=
  match conj with
  | [] => <% true %>
  | h :: t =>
    match animateOneConjGuardList t with
    | gt => animateOneConjSuccGuard h gt
    end
  end.
*)
(*
Check (Some (let b :=1 in let a := 2 in  b + a)).

Definition sillyFun (p : outcomePoly (prod nat nat)) : nat :=
 match p with
  | successPoly (a,b) => let c := a in let d := b in (c + d)
  | _ => 0
 end.
*)
(*

Definition soundness' (f : (nat -> nat -> option (list nat))) (induct : nat -> nat -> nat -> nat -> nat -> Prop) (n1 : nat) (n2 : nat) : Type :=
 let r := (f n1 n2) in
   match r with
    | Some ([n3 ; n4 ; n5]) => (* forall h1, forall h2, forall h3, h1 = g1 -> h2 = g2 -> h3 = g3 -> *) (induct n1 n2 n3 n4 n5)
    | None => (forall n3 n4 n5 : nat, (induct n1 n2 n3 n4 n5 -> False))
 (*  (forall n3 n4 n5 : nat, (foo n1 n2 n3 n4 n5 -> False)) *)
    | _ => False
    end.
Definition soundness'' (f : (nat -> nat -> option (list nat))) (induct : nat -> nat -> nat -> nat -> nat -> Prop) : Type :=
 forall n1 n2, soundness' f induct n1 n2 .


(* Check foo.
Check soundness''. *)


Definition animate'' (kn : kername) (induct : nat -> nat -> nat -> nat -> nat -> Prop)  (inputVars : (list string)) (outputVars : list string) (fuel : nat) : TemplateMonad unit :=
  conjs <- general.animate2 kn ;;
  r <- animateEqual.genFun conjs inputVars outputVars fuel  ;;

  t' <- DB.deBruijn r ;;

  f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) t' ;; tmPrint f ;; tmDefinition (String.append (snd kn) "Fn") f ;;
  lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f induct) ;;
  tmMsg "done".

*)
Definition constrFunAnimateEq {A : Type} (induct : A)
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term)
                        (fuel : nat) : TemplateMonad term :=


let postIn := tApp <%successPoly%> [postInType'; postIn'] in
let postInType := tApp <%outcomePoly%> [postInType'] in

let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
let postOutType := tApp <%outcomePoly%> [postOutType'] in






tBody' <-  mkMulPatMatFn (induct) ([(postIn, (postOut)); ((tApp <%fuelErrorPoly%> [postInType']),(tApp <%fuelErrorPoly%> [postOutType'])) ]) postInType postOutType (tApp <%noMatchPoly%> [postOutType']) fuel ;;
tmPrint tBody' ;;


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





(*t'' <- tmEval all (removeopTm (DB.deBruijnOption u)) ;; *)
ret u.
(*
f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append nmCon "Animated") (Some hnf) ;; tmMsg "done".


*)



Definition optionToOutcome (A : Type) (B : Type) (f : nat -> outcomePoly A -> outcomePoly (option B)) : (nat -> outcomePoly A -> outcomePoly B) :=
fun k k' => match f k k' with
             | successPoly (Some res) => successPoly B res
             | successPoly None => noMatchPoly B
             | fuelErrorPoly => fuelErrorPoly B
             | _ => noMatchPoly B
            end.

(*

Definition genFunAnimateEq {A : Type} (induct : A) (kn : kername) (inputTm : term) (inputTp : term)  (outputTm : term) (outputTp : term) (myData' : list (((string * term) * term) * list (string * term))) (inArgs : list nat) (fuel : nat) : TemplateMonad unit :=
  fooTerm <- general.animate2 kn ;;
  if checkBool (filterListConj fooTerm) then
  (let postOut' := (constrFnBody outputTm outputTp
    (animateListConj
       (getListConjLetBind fooTerm) nil (getIndRHSVar myData' inArgs) fuel (fun t : term => t))
    (animateOneConjGuardList (getListConjGuardCon fooTerm))) in
    (*
    po' <- tmEval all postOut' ;;
    tmPrint po' ;;
    *)

    let postOutType' := tApp <% @option %> [outputTp] in
    (*
    poT' <- tmEval all postOutType' ;;
    tmPrint poT' ;;
    *)
    let postInType' := inputTp in
    (*
    piT' <- tmEval all postInType' ;;
    tmPrint piT' ;;
    *)
    let postIn' := inputTm in
    (*
    pi' <- tmEval all postIn' ;;
    tmPrint pi' ;;
    *)
    let postIn := tApp <%successPoly%> [postInType'; postIn'] in
    let postInType := tApp <%outcomePoly%> [postInType'] in

    let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
    let postOutType := tApp <%outcomePoly%> [postOutType'] in




 (*

   animateOneClause induct [] postInTPairB postInType' postInTPairB postInType' (snd kn) fuel ;;
*)

     t0 <- constrFunAnimateEq induct postIn' postInType' postOut' postOutType'  fuel ;;
      (*
      tmPrint t0 ;;
      *)
     let t1 := (tApp <%optionToOutcome%> [postInType'; outputTp; t0]) in
     t' <- tmEval all (removeopTm (DB.deBruijnOption t1)) ;;

     f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append (snd kn) "Animated") (Some hnf) ;;  tmMsg "done") else tmFail "cannot process conj".

Check general.animate2.


Definition genFunAnimateEq7 {A : Type} (kn : kername) (induct : A) (mode :list (prod (list nat) (list nat))) (fuel : nat) : TemplateMonad unit :=
 d <- mkClData' kn mode ;;
 d'' <- tmEval all d ;;
 tmPrint d'' ;;
 mut <- tmQuoteInductive kn ;;
let lib := ind_bodies mut in
let nmCxt := genCxt lib in
let inOutTps := getInOutTps mode lib in
myData <- getData lib mode nmCxt inOutTps ;;
myData' <- tmEval all myData;;
tmPrint myData';;
 let elt := hd datHdDef d in
 let inputTm := snd (fst (fst (fst (fst elt)))) in
 let inputTp := snd ((fst (fst (fst elt)))) in
 let outputTm := snd (((fst (fst elt)))) in
 let outputTp := snd (((fst (elt)))) in
(*
tmPrint inputTm.
*)
 match mode with
  | [] => tmFail "no mode info"
  | h :: t => genFunAnimateEq (induct) (kn) (inputTm) (inputTp)  (outputTm) (outputTp) (myData') ((fst h)) (fuel)
 end.


Inductive foo'' : bool -> nat -> bool -> nat -> Prop :=
 | cstr'' : forall (b  d : bool) (e f : nat), d = b /\ e =  f /\ ((fun x => x) e) = ((fun x => x + 1) f) -> foo'' b (S f) d (S e).

MetaRocq Run (g <- general.animate2 <? foo'' ?> ;; tmDefinition "data''" g).
Compute data''.
Check getData.
*)
Definition genFunAnimateEqPartialLetClause' {A : Type} (induct : A) (kn : kername) (fooTerm : named_term)  (inputTm : term) (inputTp : term)  (outputTm : term) (outputTp : term) (inputVars : list string) (fuel : nat) : TemplateMonad term :=

  if checkBool (filterListConj fooTerm) then
  (let postOut' := (constrFnBody outputTm outputTp
    (animateListConj
       (getListConjLetBind fooTerm) nil (inputVars) fuel (fun t : term => t))
     ) in
    (*
    po' <- tmEval all postOut' ;;
    tmPrint po' ;;
    *)

    let postOutType' := tApp <% @option %> [outputTp] in
    (*
    poT' <- tmEval all postOutType' ;;
    tmPrint poT' ;;
    *)
    let postInType' := inputTp in
    (*
    piT' <- tmEval all postInType' ;;
    tmPrint piT' ;;
    *)
    let postIn' := inputTm in
    (*
    pi' <- tmEval all postIn' ;;
    tmPrint pi' ;;
    *)
    let postIn := tApp <%successPoly%> [postInType'; postIn'] in
    let postInType := tApp <%outcomePoly%> [postInType'] in

    let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
    let postOutType := tApp <%outcomePoly%> [postOutType'] in




 (*

   animateOneClause induct [] postInTPairB postInType' postInTPairB postInType' (snd kn) fuel ;;
*)

     t0 <- constrFunAnimateEq induct postIn' postInType' postOut' postOutType'  fuel ;;
      (*
      tmPrint t0 ;;
      *)
     let t1 := (tApp <%optionToOutcome%> [postInType'; outputTp; t0]) in
     t' <- tmEval all (removeopTm (DB.deBruijnOption t1)) ;;
     tmReturn t')
     (*
     f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append (snd kn) "Animated") (Some hnf) ;;  tmMsg "done") *) else tmFail "cannot process conj".





(*
Definition genFunAnimateEqPartial {A : Type} (kn : kername) (induct : A) (conjunct : named_term) (inputVars : list string)
                                  (d : (list (((((list ((((string * term) * term) * term) * term) * term) * term) * term) * term)
             * string))) (inOutTps : (list (((string * term) * term)))) (fuel : nat) : TemplateMonad unit :=

 d'' <- tmEval all d ;;
(* tmPrint d'' ;; *)
 mut <- tmQuoteInductive kn ;;
let lib := ind_bodies mut in
let nmCxt := genCxt lib in

nmCxt' <- tmEval all nmCxt ;;
inOutTps' <- tmEval all inOutTps ;;
tmPrint nmCxt';;
tmPrint inOutTps';;

(* tmPrint myData';; *)
 let elt := hd datHdDef d in
 let inputTm := snd (fst (fst (fst (fst elt)))) in
 let inputTp := snd ((fst (fst (fst elt)))) in
 let outputTm := snd (((fst (fst elt)))) in
 let outputTp := snd (((fst (elt)))) in
(*
tmPrint inputTm.
*)
genFunAnimateEqPartial' (induct) (kn) (conjunct) (inputTm) (inputTp)  (outputTm) (outputTp) (inputVars) (fuel).



Definition d : (list (((((list ((((string * term) * term) * term) * term) * term) * term) * term) * term)
             * string)) := [([], tVar "b",
  <%bool%>,
  tVar "d",
  <%bool%>,
  "cstr''")].

Definition myData : (list (((string * term) * term))) := [("foo''",
  <%bool%>,
  <%bool%>)].
(*
Definition myDataSimpl : (list (((string * term) * term) * list (string * term))) := [("foo''",
  <%bool%>,
  <%bool%>,
  [("cstr''",

      (
         tApp <%eq%>
            [tInd
               {|
                 inductive_mind := <?bool?>; inductive_ind := 0
               |} [];
             tVar "d"; tVar "b"]
          )
      )])].
*)
Definition conjunct : named_term := tApp <%eq%>
            [tInd
               {|
                 inductive_mind := <?bool?>; inductive_ind := 0
               |} [];
             tVar "d"; tVar "b"].

MetaRocq Run (animateEqual.genFunAnimateEqPartial' foo'' <? foo'' ?> conjunct (tVar "b") <%bool%> (tVar "d") <%bool%> ["b"] 50).


Print foo''Animated.

(** Examples ___________**)

(*
MetaRocq Run (mut <- tmQuoteInductive <? foo''' ?> ;; tmDefinition "mutFoo" mut).
MetaRocq Run (data <- getData' <? foo''' ?> [([0;2],[1;3])] ;; tmDefinition "dataFoo'''" data).
Compute dataFoo'''.
Parameter oib'' : one_inductive_body.
Compute (ind_type (hd oib'' (ind_bodies mutFoo))).

*)


*)



Definition extractPatMatBindersPartial'' {A : Type} (induct : A) (kn : kername) (conjunct : named_term) (inputTm : term) (inputTp : term) (outputTm : term) (outputTp : term) (fuel : nat) : TemplateMonad term :=

match conjunct with
 | tApp <%eq%> [typeVar; patMatTerm; tApp (func) lst] =>
                      tIn <- joinPatMatPolyGenFuelAwareNoLHSTm induct (inputTm) (inputTp) (tApp (func) lst) typeVar (String.append (snd kn) "IN") fuel ;;
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  patMatTerm typeVar  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;
                      (*
                      gIn <- tmUnquote tIn ;;
                      gIn' <- tmEval hnf (my_projT2 gIn) ;;
                      gOut <- tmUnquote tOut ;;
                      gOut' <- tmEval hnf (my_projT2 gOut) ;;


                      tmDefinition (String.append (snd kn) "Animated") (composeOutcomePolyImpl gIn' gOut')

                      *)




                      let u :=
                       (tApp <%composeOutcomePoly%> [(inputTp); typeVar ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      (*tmPrint u';; *)

                      u' <- DB.deBruijn u ;;
                      tmReturn u'
                     (*
                      ftypeIn <- tmUnquoteTyped Type (mkProdTypeVars inputData) ;;
                      ftypeOut <- tmUnquoteTyped Type (mkProdTypeVars outputData) ;;
                      (*
                      f <- tmUnquoteTyped (nat -> outcomePoly ftypeIn -> outcomePoly ftypeOut) u' ;;
                      (*
                      tmPrint f
                      *)
                      (*
                      @tmDefinition (String.append (snd kn) "Animated") (nat -> outcomePoly ftypeIn -> outcomePoly ftypeOut) (f)
                     *)
                     tmDefinition (String.append (snd kn) "Animated")  (f)
                     *)
                     *)
                     (*
                     f <- tmUnquote u';;
                     tmPrint f ;;
                     (* tmDefinition (String.append (snd kn) "Animated")  (f)
                     *)

                     tmEval hnf (my_projT2 f) >>=
                     tmDefinitionRed_ false (String.append (snd kn) "Animated") (Some hnf ) ;; ret tt
                     *)


 | tApp <%eq%> [typeVar; patMatTerm; tVar str] =>
                      tIn <- joinPatMatPolyGenFuelAwareNoLHSTm induct (inputTm) (inputTp) (tVar str) typeVar (String.append (snd kn) "IN") fuel ;;
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  patMatTerm typeVar  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;
                      (*
                      gIn <- tmUnquote tIn ;;
                      gIn' <- tmEval hnf (my_projT2 gIn) ;;
                      gOut <- tmUnquote tOut ;;
                      gOut' <- tmEval hnf (my_projT2 gOut) ;;


                      tmDefinition (String.append (snd kn) "Animated") (composeOutcomePolyImpl gIn' gOut')

                      *)




                      let u :=
                       (tApp <%composeOutcomePoly%> [(inputTp); typeVar ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      (*tmPrint u';; *)

                      u' <- DB.deBruijn u ;;
                      tmReturn u'
                     (*
                      ftypeIn <- tmUnquoteTyped Type (mkProdTypeVars inputData) ;;
                      ftypeOut <- tmUnquoteTyped Type (mkProdTypeVars outputData) ;;
                      (*
                      f <- tmUnquoteTyped (nat -> outcomePoly ftypeIn -> outcomePoly ftypeOut) u' ;;
                      (*
                      tmPrint f
                      *)
                      (*
                      @tmDefinition (String.append (snd kn) "Animated") (nat -> outcomePoly ftypeIn -> outcomePoly ftypeOut) (f)
                     *)
                     tmDefinition (String.append (snd kn) "Animated")  (f)
                     *)
                     *)
                     (*
                     f <- tmUnquote u';;
                     tmPrint f ;;
                     (* tmDefinition (String.append (snd kn) "Animated")  (f)
                     *)

                     tmEval hnf (my_projT2 f) >>=
                     tmDefinitionRed_ false (String.append (snd kn) "Animated") (Some hnf ) ;; ret tt
                     *)



 | _ => tmFail "incorrect inductive shape"
 end.

Check (let (a, b) := (1,2) in a).
Check ((nat -> term -> term) -> bool).




Definition extractPatMatBindersPartial' {A : Type} (induct : A) (kn : kername) (conjunct : named_term) (inputTm : term) (inputTp : term) (outputTm : term) (outputTp : term) (inputVars : list string) (fuel : nat) : TemplateMonad term :=
match conjunct with
| tApp <%eq%> [typeVar; t1; t2] => if isListSubStr (extractOrderedVars t1) inputVars then
                                   extractPatMatBindersPartial'' induct kn (tApp <%eq%> [typeVar; t2; t1]) inputTm inputTp outputTm outputTp fuel else (if isListSubStr (extractOrderedVars t2) inputVars then
                                   extractPatMatBindersPartial'' induct kn conjunct inputTm inputTp outputTm outputTp fuel else tmFail "incorrect inductive shape")
| _ => tmFail "incorrect inductive shape"
end.


Definition animatePredicate' {A : Type} (induct : A) (kn : kername) (conjunct : named_term) (inputVarProdTm : term) (inputVarProdTp : term) (predInArgs : list (term × term)) (predOutArgs : list (term × term))  (outputTm : term) (outputTp : term) (fuel : nat) : TemplateMonad term :=

match conjunct with
 | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => 
                      
                      
                      predOutProdTp <- mklhsProdType predOutArgs ;;
                      predOutProdTm <- mklhsProdTm predOutArgs ;;
                      predInProdTp <- mklhsProdType predInArgs ;;
                      predInProdTm <- mklhsProdTm predInArgs ;; 
                      tIn' <- joinPatMatPolyGenFuelAwareNoLHSTm induct (inputVarProdTm) (inputVarProdTp) predInProdTm predInProdTp (String.append (snd kn) "IN") fuel ;;
                                         
                      let tIn :=  (tApp <%composeOutcomePoly%> [(inputVarProdTp); predInProdTp ; (predOutProdTp) ; tIn' ;  (tVar (String.append indNm "AnimatedTopFn"))])   in 
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  predOutProdTm predOutProdTp  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;
                      



                      let u :=
                       (tApp <%composeOutcomePoly%> [(inputVarProdTp); predOutProdTp ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      
                      u' <- DB.deBruijn u ;;
                      tmReturn u'
                     




 | _ => tmFail "incorrect inductive shape"
 end.

Fixpoint extractOrderedVarsfmLst (l : list term) : list string :=
match l with
| [] => []
| h :: t => app (extractOrderedVars h) (extractOrderedVarsfmLst t)
end.
Fixpoint listSearch' {A : Type} (ind : nat) (l : list A) : list A :=
match ind with
| 0 => match l with
     | h :: t => [h]
     | [] => []
     end
| S m => listSearch' m (tl l)
end.     


Fixpoint listSearch {A : Type} (indLst : list nat) (l : list A) : list A :=
match indLst with 
| [] => []
| h :: t => app (listSearch' h l) (listSearch t l)
end. 

Fixpoint getInArgs (indNm : string) (modes : list (string * ((list nat) * (list nat)))) (lstArgs : list term) : list term :=
match modes with
| [] => []
| h :: t => if String.eqb indNm (fst h) then listSearch (fst (snd h)) lstArgs else getInArgs indNm t lstArgs
end. 

Fixpoint getOutArgs (indNm : string) (modes : list (string * ((list nat) * (list nat)))) (lstArgs : list term) : list term :=
match modes with
| [] => []
| h :: t => if String.eqb indNm (fst h) then listSearch (snd (snd h)) lstArgs else getOutArgs indNm t lstArgs
end.     

Search (list (term * term) -> TemplateMonad term).
Print tLam.


 
Fixpoint lookUpVarsOne (varNm: string) (allVarTpInf : list (prod string term)) : list (prod string term) :=
match allVarTpInf with
| [] => []
| h :: t => if String.eqb varNm (fst h) then [h] else lookUpVarsOne varNm t
end.

Fixpoint mkLstTm (lst : list (prod string term)) : list (prod term term) :=
match lst with
| [] => []
| (str,tp) :: t => (tVar str, tp) :: mkLstTm t
end.
Fixpoint lookUpVars (lst : list string) (allVarTpInf : list (prod string term)) : list (prod string term) :=
match lst with
| [] => []
| h :: t => match lookUpVarsOne h allVarTpInf with
             | [h'] => h' :: lookUpVars t allVarTpInf
             | _ =>  lookUpVars t allVarTpInf
            end
end.


Definition lookUpVarsOneDefBool (varNm: string) (allVarTpInf : list (prod string term)) : (term) :=
match lookUpVarsOne varNm allVarTpInf with
| [h] => snd h
| _ => <%bool%>
end.
Fixpoint getModeFmLst (indNm : string) (modes : list (string * ((list nat) * (list nat)))) : (list nat) * (list nat) :=
 match modes with
  | [] => ([],[])
  | h :: t => if String.eqb indNm (fst h) then (snd h) else getModeFmLst indNm t
 end.

Definition getInArgs'  (mode : (list nat) * (list nat)) (lstArgs : list term) : list term :=
listSearch (fst mode) lstArgs.
 
Definition getOutArgs'  (mode : (list nat) * (list nat)) (lstArgs : list term) : list term :=
listSearch (snd mode) lstArgs.
 
 

Search (list (term * term) -> TemplateMonad term).
Print tLam.

Fixpoint getPredTp (indNm : string) (predTypeInf : list (string * (list term))) : list term :=
match predTypeInf with
| [] => []
| h :: t => if String.eqb indNm (fst h) then snd h else getPredTp indNm t 
end. 

Fixpoint crossList {A : Type} {B : Type} (lst1 : list A) (lst2 : list B) : list (A * B) :=
match lst1 with
 | [] => []
 | (h :: t) => match lst2 with
                | [] => []
                | h' :: t' => (h,h') :: crossList t t'
               end  
end.
                

Definition animatePredicate {A : Type} (induct : A) (kn : kername) (conjunct : named_term) (outputTm : term) (outputTp : term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad term :=

match conjunct with
 | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => 
                     (*let outputTm := tVar outputVar in 
                     let outputTp := lookUpVarsOneDefBool outputVar allVarTpInf in *)
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
                                         
                      let tIn :=  (tApp <%composeOutcomePoly%> [(inputVarProdTp); predInProdTp ; (predOutProdTp) ; tIn' ;  (tVar (String.append indNm "AnimatedTopFn"))])   in 
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  predOutProdTm predOutProdTp  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;
                      



                      let u :=
                       (tApp <%composeOutcomePoly%> [(inputVarProdTp); predOutProdTp ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      
                      u' <- DB.deBruijn u ;;
                      tmReturn u'
                     




 | _ => tmFail "incorrect inductive shape"
 end. 





(** ** Integration of All Animation Pieces
    This section combines the various animation strategies into a unified framework
    that handles let-bindings, pattern matches, partial application, and complex conjunctions. *)

(** Check if a list is empty. *)
Definition isEmptyLst {A : Type} (lst : list A) : bool :=
match lst with
 | [] => true
 | _ => false
end.

(** Sort and orient conjunctions for animation.
    Separates guard conditions from let-binding equalities and orients equations
    so that known variables appear on the right. *)

Fixpoint getSortedOrientedConjs (modes : list (string * ((list nat) * (list nat)))) (currentConjs : list term) (remConjs : list term) (sortedConjs : list term) (guardConjs : list term) (kv : (list string)) (fuel : nat) : TemplateMonad (prod (list term) (list term)) :=
match fuel with
 | 0 => if andb (isEmptyLst remConjs) (isEmptyLst currentConjs) then tmReturn (sortedConjs, guardConjs) else tmFail "insufficient fuel to sort conjs"
 | S n => if (andb (isEmptyLst remConjs) (isEmptyLst currentConjs)) then tmReturn (sortedConjs, guardConjs) else
           match currentConjs with
            | [] => getSortedOrientedConjs modes remConjs [] sortedConjs guardConjs kv n
            | conj' :: t => match conj' with
                        | tApp <%eq%> [typeVar; t1; t2] => if andb (isListSubStr (extractOrderedVars t1) kv) (isListSubStr (extractOrderedVars t2) kv) then
                                                            getSortedOrientedConjs modes t remConjs sortedConjs (conj' :: guardConjs) kv n else
                                                            (if (isListSubStr (extractOrderedVars t1) kv) then getSortedOrientedConjs modes t remConjs (tApp <%eq%> [typeVar; t2; t1] :: sortedConjs) (guardConjs) (app (extractOrderedVars t2) kv) n else
                                                            (if  (isListSubStr (extractOrderedVars t2) kv) then getSortedOrientedConjs modes t remConjs (tApp <%eq%> [typeVar; t1; t2] :: sortedConjs) (guardConjs) (app (extractOrderedVars t1) kv) n else
                                                            (getSortedOrientedConjs modes t (conj' :: remConjs) (sortedConjs) (guardConjs) (kv) n)))
                        
                        | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => if isListSubStr (extractOrderedVars conj') kv then (getSortedOrientedConjs modes t (remConjs) (sortedConjs) (conj':: guardConjs) (kv) n) else
                                                                                                              if isListSubStr (extractOrderedVarsfmLst (getInArgs indNm modes lstArgs)) kv then getSortedOrientedConjs modes t remConjs (conj' :: sortedConjs) (guardConjs) (app (extractOrderedVarsfmLst (getOutArgs indNm modes lstArgs)) kv) n else 
                                                                                                              (getSortedOrientedConjs modes t (conj' :: remConjs) (sortedConjs) (guardConjs) (kv) n)                             
                        
                        
                        | _ => tmFail "incorrect conj shape"
                        end
           end
end.

(** Extract just the let-binding conjunctions (in sorted order). *)
Definition getSortedOrientedConjsLet (modes : list (string * ((list nat) * (list nat)))) (currentConjs : list term) (remConjs : list term) (sortedConjs : list term) (guardConjs : list term) (kv : (list string)) (fuel : nat) : TemplateMonad (list term) :=
sConjs <- getSortedOrientedConjs modes (currentConjs) (remConjs) (sortedConjs) (guardConjs) (kv) (fuel) ;;
lConjs <- tmEval all (rev (fst sConjs));;
tmReturn lConjs.

(** Extract just the guard conjunctions. *)
Definition getSortedOrientedConjsGuard (modes : list (string * ((list nat) * (list nat)))) (currentConjs : list term) (remConjs : list term) (sortedConjs : list term) (guardConjs : list term) (kv : (list string)) (fuel : nat) : TemplateMonad (list term) :=
sConjs <- getSortedOrientedConjs modes (currentConjs) (remConjs) (sortedConjs) (guardConjs) (kv) (fuel) ;;
gConjs <- tmEval all (snd sConjs);;
tmReturn gConjs.



(** Animate any conjunction, handling both variable equalities and pattern matches.
    Dispatches to appropriate animation strategy based on conjunction structure. *)
Definition animateAnyLet {A : Type} (ind : A) (kn : kername) (conj : term) (inputTm : term) (inputTp : term)
                                 (outputTm : term) (outputTp : term) (inputVars : list string) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term))  (fuel : nat) : TemplateMonad term :=
match conj with
 | tApp <%eq%> [typeVar; t1; t2] => match t1 with
                                    | tVar str =>  genFunAnimateEqPartialLetClause' ind kn conj inputTm inputTp outputTm outputTp inputVars fuel
                                    | tApp (tConstruct ind_type k lst) lstArgs => extractPatMatBindersPartial' ind kn conj inputTm inputTp outputTm outputTp inputVars fuel
                                    | _ => tmFail "incorrect Conj shape"
                                    end
 
 | tApp (tInd {| inductive_mind := (_path, _indNm); inductive_ind := 0 |} []) _lstArgs => animatePredicate (ind) (kn) (conj) (outputTm) (outputTp) (modes) (predTypeInf) (allVarTpInf) (fuel)

 
 | _ => tmFail "incorrect Conj shape"
end.






Definition joinOutcomeUnit (A: Type) (x : outcomePoly A) : outcomePoly A :=
x.

Definition joinOutcome (A : Type) (B : Type) (x : outcomePoly A) (y : outcomePoly B) : outcomePoly (prod A B) :=
 match x with
  | noMatchPoly => noMatchPoly (prod A B)
  | fuelErrorPoly => fuelErrorPoly (prod A B)
  | successPoly k => match y with
                        | noMatchPoly => noMatchPoly (prod A B)
                        | fuelErrorPoly => fuelErrorPoly (prod A B)
                        | successPoly j => successPoly (prod A B) (k,j)
                        end
 end.



Fixpoint prodTerm (lstTypes : list term) : term :=
match lstTypes with
 | [] => <%bool%>
 | [h] => h
 | h :: t => tApp
                     (tInd
                        {|
                          inductive_mind := <?prod?>;
                          inductive_ind := 0
                        |} []) [h ; (prodTerm t)]
end.

Fixpoint mkJoinOutcomeFnBody (lstTypes : list term) (n : nat) : term :=
match lstTypes with
 | [] => tApp <%joinOutcomeUnit%> [<%bool%>; tVar "o0"]
 | [h] => tApp <%joinOutcomeUnit%> [h; tVar (String.append "o" (string_of_nat n))]
 | [h ; h1] => tApp <%joinOutcome%> [h; h1; tVar (String.append "o" (string_of_nat n)); tVar (String.append "o" (string_of_nat (S n)))]
 | h :: t => tApp <%joinOutcome%> [h; (prodTerm t); tVar (String.append "o" (string_of_nat n)); mkJoinOutcomeFnBody t (S n)]
end.


Fixpoint mkJoinOutcomeLam (lstTypes : list term) (n : nat) (fnBody : term) : term :=
match lstTypes with
| [] => tLam "o0" (tApp <%outcomePoly%> [<%bool%>]) fnBody
| [h] => tLam (String.append "o" (string_of_nat n)) (tApp <%outcomePoly%> [h]) fnBody
| h :: t => tLam (String.append "o" (string_of_nat n)) (tApp <%outcomePoly%> [h]) (mkJoinOutcomeLam t (S n) fnBody)
end.

Definition mkJoinOutcomeTm (lstTypes : list term) : term :=
let fnBody := mkJoinOutcomeFnBody lstTypes 0 in
mkJoinOutcomeLam lstTypes 0 fnBody.


Definition animateOneConjAnyLet' (outputVarNm : string) (outputVarTp : term) (inputVarsLst : list (prod term term)) (animationFn : term) (partialLetfn : term -> term) : (term -> term) :=
 match inputVarsLst with
  | [] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [tVar "fuel"]) (tApp <%outcomePoly%> [outputVarTp]))  t) )
  | [h] => (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); fst h]) (tApp <%outcomePoly%> [outputVarTp])) t ))
  | _ =>  (fun t => partialLetfn ((tLetIn {| binder_name := nNamed outputVarNm; binder_relevance := Relevant |}
                                 (tApp animationFn [(tVar "fuel"); (tApp (mkJoinOutcomeTm (map snd inputVarsLst)) (map fst inputVarsLst))]) (tApp <%outcomePoly%> [outputVarTp])) t))
 end.



Definition animateOneConjAnyLet {A : Type} (ind : A) (kn : kername) (conj : term) (outputVarNm : string) (outputVarTp : term) (inputVarsLst : list (prod string term)) (partialLetfn : term -> term) 
                                           (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
let inputTm := mkProdTmVars inputVarsLst in
let inputTp := mkProdTypeVars inputVarsLst in
let inputVarsLstTm := mkLstTm inputVarsLst in
animationFn <-  animateAnyLet (ind) (kn) (conj) (inputTm) (inputTp)
                                 (tVar outputVarNm) (outputVarTp) (map fst inputVarsLst) (modes) (predTypeInf) (allVarTpInf) fuel ;;
tmReturn (animateOneConjAnyLet' (outputVarNm) (outputVarTp) (inputVarsLstTm) (animationFn) (partialLetfn)).





Definition getConjOutputVars (conj : term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (prod string term) :=
match conj with
 | tApp <%eq%> [typeVar; t1; t2] => lookUpVars (extractOrderedVars t1) allVarTpInf
 | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => let mode := getModeFmLst indNm modes in
                     
                                                                                        let predOutArgsTm := getOutArgs' mode lstArgs in
                     
                                                                                        lookUpVars (extractOrderedVarsfmLst predOutArgsTm) allVarTpInf 
 | _ => [] 
end.
Definition getConjInputVarLst (conj : term) (allVarTpInf : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) : list (prod string term) :=

match conj with
 | tApp <%eq%> [typeVar; t1; t2] => lookUpVars (extractOrderedVars t2) allVarTpInf
 | tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs => let mode := getModeFmLst indNm modes in
                     
                                                                                        let predInArgsTm := getInArgs' mode lstArgs in
                     
                                                                                        lookUpVars (extractOrderedVarsfmLst predInArgsTm) allVarTpInf 
 | _ => [] 
end.
Fixpoint animateOneConjAnyLetMult {A : Type} (ind : A) (kn : kername) (conj : term)
                                 (outputVars : list (prod string term)) (inputVarsLst : list (prod string term)) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
match outputVars with
 | [] => tmReturn partialLetfn
 | h :: t =>  lFn' <- animateOneConjAnyLet A kn conj (fst h) (snd h) inputVarsLst partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel ;; animateOneConjAnyLetMult ind kn conj t inputVarsLst  lFn' (modes) (predTypeInf) (allVarTpInf) fuel
end.


Definition animateOneConjLetCl {A : Type} (ind : A) (kn : kername) (conj : term) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
let outputVars := getConjOutputVars conj allVarTpInf (modes) (predTypeInf) in
let  inputVarsLst := getConjInputVarLst conj allVarTpInf (modes) (predTypeInf) in
animateOneConjAnyLetMult ind kn conj outputVars inputVarsLst partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel.

Fixpoint animateListConjLetCl {A : Type} (ind : A) (kn : kername) (conjs : list term) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
match conjs with
 | [] => tmReturn partialLetfn
 | h :: t => lFn' <- animateOneConjLetCl ind kn h partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel ;; animateListConjLetCl ind kn t lFn' (modes) (predTypeInf) (allVarTpInf) fuel
end.



Definition animateOneConjSuccGuard'' (conj : term) (partialGuard : term)  :  term :=
  match conj with
  | tApp <%eq%> [typeT; t1; t2] =>
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (typeToBoolEq typeT) [t1
         ; t2]]

  | _ => <% false %>
  end.

Fixpoint animateConjGuardList (conj : list term) : term :=
  match conj with
  | [] => <% true %>
  | h :: t =>
    match animateConjGuardList t with
    | gt => animateOneConjSuccGuard'' h gt
    end
  end.

Definition mkOutPolyProdTm (outVars : list (prod string term)) : term :=
tApp (mkJoinOutcomeTm (map snd outVars)) (map (fun e => tVar (fst e)) outVars).



Definition genFunAnimateEqPartialGuardCon' {A : Type} (induct : A) (kn : kername) (gConjs : list term)  (inputTm : term) (inputTp : term)  (outputTm : term) (outputTp : term) (fuel : nat) : TemplateMonad term :=


  (let postOut' := (constrFnBodyGuardCon outputTm outputTp

    (animateConjGuardList (gConjs) )) in
    

    let postOutType' := tApp <% @option %> [outputTp] in
    
    let postInType' := inputTp in
    
    let postIn' := inputTm in
    
    let postIn := tApp <%successPoly%> [postInType'; postIn'] in
    let postInType := tApp <%outcomePoly%> [postInType'] in

    let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
    let postOutType := tApp <%outcomePoly%> [postOutType'] in






     t0 <- constrFunAnimateEq induct postIn' postInType' postOut' postOutType'  fuel ;;
      
     let t1 := (tApp <%optionToOutcome%> [postInType'; outputTp; t0]) in
     t' <- tmEval all (removeopTm (DB.deBruijnOption t1)) ;;
     tmReturn t').

Definition animateListConjGuard {A : Type} (induct : A) (kn : kername) (gConjs : list term) (allVarTpInf : list (prod string term))  (outVars : list (prod string term)) (fuel : nat) : TemplateMonad term :=
genFunAnimateEqPartialGuardCon' induct kn gConjs  (mkProdTmVars allVarTpInf) (mkProdTypeVars allVarTpInf) (mkProdTmVars outVars) (mkProdTypeVars outVars) fuel.



Fixpoint animateListLetClLam (inVars : list (prod string term)) (fnBody : term) :=
match inVars with
| [] => fnBody

| h :: t => tLam (fst h) (tApp <%outcomePoly%> [snd h]) (animateListLetClLam t fnBody)
end.


Fixpoint mkLamTp (inVars : list (prod string term)) (fnBody : term) :=
match inVars with
| [] => fnBody

| h :: t => tLam (fst h) (snd h) (mkLamTp t fnBody)
end.

Fixpoint mkAnimatedFnNm (l : list (string * term)) : list (string * term) :=
match l with
| [] => []
| (s,tp) :: t => ((String.append s "AnimatedTopFn"), tp) :: mkAnimatedFnNm t
end.  
(*Print reductionStrategy. *)

Definition animateListLetAndGuard {A : Type} (ind : A) (kn : kername) (lConjs : list term) (gConjs : list term) (inVars : list (prod string term)) (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=
letBind <- animateListConjLetCl  (ind) kn  lConjs  (fun t : term => t) (modes) (predTypeInf) (allVarTpInf) (fuel) ;;
gFun <- animateListConjGuard ind kn gConjs allVarTpInf outVars fuel ;;
tmReturn (mkLamTp (app (mkAnimatedFnNm lhsPreds) [("fuel", <%nat%>)]) (animateListLetClLam inVars (letBind (tApp gFun [tVar "fuel"; mkOutPolyProdTm (allVarTpInf)])))).






(* Universe error


Definition animateListLetAndGuard'' {A : Type} (ind : A) (kn : kername) (inVars : list (prod string term))  (outVars : list (prod string term))  (allVarTpInf : list (prod string term)) (fuel : nat) : TemplateMonad term :=
bigConj <- general.animate2 kn ;;
let listAllConjs := getListConjAll bigConj in
lConjs' <- (getSortedOrientedConjsLet listAllConjs [] [] [] (map fst inVars) fuel) ;;
lConjs <- tmEval (all) lConjs' ;;
gConjs' <- (getSortedOrientedConjsGuard listAllConjs [] [] [] (map fst inVars) fuel) ;;
gConjs <- tmEval (all) gConjs' ;;
letBind <- animateListConjLetCl  (ind) kn  lConjs  allVarTpInf  (fun t : term => t) (fuel) ;;
gFun <- animateListConjGuard ind kn gConjs allVarTpInf outVars fuel ;;
t <- (animateListLetClLam inVars (letBind (tApp gFun [<%5%>; mkOutPolyProdTm (allVarTpInf)])));;


(*
t <- animateListLetAndGuard ind kn lConjs gConjs inVars outVars allVarTpInf fuel ;;
*)



t' <- tmEval all t ;;
t'' <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption t')) ;;
f <- tmUnquote t'' ;;
tmPrint f ;;
tmReturn t''.

*)

Unset Universe Checking.

Definition animateListLetAndGuard' {A : Type} (ind : A) (kn : kername) (inVars : list (prod string term))  (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=
bigConj <- general.animate2 kn ;;
let listAllConjs := getListConjAll bigConj in
lAC' <- tmEval all listAllConjs ;;
tmPrint lAC';;
lConjs' <- (getSortedOrientedConjsLet modes listAllConjs [] [] [] (map fst inVars) fuel) ;;
lConjs <- tmEval (all) lConjs' ;;
gConjs' <- (getSortedOrientedConjsGuard modes listAllConjs [] [] [] (map fst inVars) fuel) ;;
gConjs <- tmEval (all) gConjs' ;;
(*tmPrint lConjs;;*)
t <- animateListLetAndGuard ind kn lConjs gConjs inVars outVars (modes) (predTypeInf) (allVarTpInf) (lhsPreds) fuel ;;
t'' <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption t)) ;;
(*tmPrint t'';;*)
f <- tmUnquote t'' ;;
tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (String.append (snd kn) "Animated") (Some hnf) ;;

tmReturn t''.

Set Universe Checking.

Inductive genRel14 : nat -> nat -> nat -> nat -> Prop :=
 | genRelcstr14 : forall (a b c d : nat), a = b /\ c = d -> genRel14 a b c d. (* a c input b d output *)

Inductive genRel13 : nat -> list nat -> nat -> Prop :=
 | genRelcstr13 : forall (a d b c e f : nat) (l : list nat), d = c /\ a::l = [b;c] /\ b = c /\ genRel14 (S a) e d (S f)  -> genRel13 a l d .


MetaRocq Run (animateListLetAndGuard' genRel13 <? genRel13 ?>  [("a", <%nat%>); ("l", <%list nat%>)]  [("d", <%nat%>)] [("genRel14", ([0;2],[1;3])); ("genRel13",([0;1],[2]))] 
              [("genRel14", [<%nat%>;<%nat%>;<%nat%>;<%nat%>]); ("genRel13",[<%nat%>;<%list nat%>; <%nat%>])] [("d", <%nat%>); ("e", <%nat%>); ("f", <%nat%>); ("a", <%nat%>); ("b", <%nat%>); ("c", <%nat%>); ("l", <%list nat%>)] 
              [("genRel14",<% nat -> outcomePoly (nat * nat) -> outcomePoly (nat * nat)%>)] 50).
Print genRel13Animated.

End animateEqual.
(* Decidable equality typeclass ________________________ *)







Definition dec (P : Prop) : Type := { P } + { ~ P }.

Class DecEq (A : Type) : Type :=
  { dec_eq : forall (x y : A), dec (x = y) }.

#[export] Instance DecEq_nat : DecEq nat.
Proof. constructor. unfold dec. decide equality. Defined.

#[export] Instance DecEq_list (A : Type) `(DecEq A) : DecEq (list A).
Proof. constructor. unfold dec. decide equality. apply dec_eq. Defined.

MetaRocq Run (o <- tmInferInstance (Some all) (DecEq (list (list nat))) ;;
              match o with
              | my_Some f => tmPrint f
              | _ => tmFail "boo"
              end).
Check (DecEq_list nat).





Check @dec_eq.

MetaRocq Run (o <- tmInferInstance (Some all) (DecEq (list nat)) ;;
              match o with
              | my_Some f => tmEval all (@dec_eq _ f [1] [1]) >>= tmPrint
              | _ => tmFail "boo"
              end).

Check @tmDefinition.

Definition mkEqFn (A : Type) (nmTm : string) : TemplateMonad term :=
o <- tmInferInstance (Some all) (DecEq A) ;;
              match o with
              | my_Some f => let myFun : A -> A -> bool := (fun x y => match @dec_eq A f x y with
                                                                       | left _ => true
                                                                       | right _ => false
                                                                       end) in (tmPrint myFun ;; t' <- (tmQuote myFun) ;; t'' <- tmEval all t' ;; (* @tmDefinition nmTm term t'' ;; *) tmReturn t'')

              | _ => tmFail "boo"
              end.

MetaRocq Run (t <- mkEqFn (list nat) "listNatEq" ;; tmPrint t).

Definition mkEqFnTm (t : term) : TemplateMonad term :=
A <- tmUnquoteTyped Type t ;;
o <- tmInferInstance (Some all) (DecEq A) ;;
              match o with
              | my_Some f => let myFun : A -> A -> bool := (fun x y => match @dec_eq A f x y with
                                                                       | left _ => true
                                                                       | right _ => false
                                                                       end) in (tmPrint myFun ;; t' <- (tmQuote myFun) ;; t'' <- tmEval all t' ;; (* @tmDefinition nmTm term t'' ;; *) tmReturn t'')

              | _ => tmFail "boo"
              end.

MetaRocq Run (t <- mkEqFnTm <%list nat%>  ;; tmPrint t).

Compute (match dec_eq [1] [2] with
         | left _ => "yes"
         | right _ => "no"
         end).

Compute (match dec_eq [1] [2] with
         | left _ => true
         | right _ => false
         end).
Definition mkEqFn'' (B : Type) {A : DecEq B} : (B -> B -> bool) :=
 fun x y : B => match dec_eq x y with
                 | left _ => true
                 | right _ => false
                end.

