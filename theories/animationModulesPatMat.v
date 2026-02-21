Require Import Animation.animationModulesPathNotation.
Require Import Animation.utils2.


Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.


Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.

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


Parameter errorTm : term.



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




Definition extractPatMatBindersPartial'' {A : Type} (induct : A) (kn : kername) (conjunct : named_term) (inputTm : term) (inputTp : term) (outputTm : term) (outputTp : term) (fuel : nat) : TemplateMonad term :=

match conjunct with
 | tApp <%eq%> [typeVar; patMatTerm; tApp (func) lst] =>
                      tIn <- joinPatMatPolyGenFuelAwareNoLHSTm induct (inputTm) (inputTp) (tApp (func) lst) typeVar (String.append (snd kn) "IN") fuel ;;
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  patMatTerm typeVar  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;
                      


                      let u :=
                       (tApp <%composeOutcomePoly%> [(inputTp); typeVar ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      

                      u' <- DB.deBruijn u ;;
                      tmReturn u'
                     
                     


 | tApp <%eq%> [typeVar; patMatTerm; tVar str] =>
                      tIn <- joinPatMatPolyGenFuelAwareNoLHSTm induct (inputTm) (inputTp) (tVar str) typeVar (String.append (snd kn) "IN") fuel ;;
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  patMatTerm typeVar  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;
                      




                      let u :=
                       (tApp <%composeOutcomePoly%> [(inputTp); typeVar ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;
                      

                      u' <- DB.deBruijn u ;;
                      tmReturn u'
            



 | _ => tmFail "incorrect inductive shape"
 end.






Definition extractPatMatBindersPartial' {A : Type} (induct : A) (kn : kername) (conjunct : named_term) (inputTm : term) (inputTp : term) (outputTm : term) (outputTp : term) (inputVars : list string) (fuel : nat) : TemplateMonad term :=
match conjunct with
| tApp <%eq%> [typeVar; t1; t2] => if isListSubStr (extractOrderedVars t1) inputVars then
                                   extractPatMatBindersPartial'' induct kn (tApp <%eq%> [typeVar; t2; t1]) inputTm inputTp outputTm outputTp fuel else (if isListSubStr (extractOrderedVars t2) inputVars then
                                   extractPatMatBindersPartial'' induct kn conjunct inputTm inputTp outputTm outputTp fuel else tmFail "incorrect inductive shape")
| _ => tmFail "incorrect inductive shape"
end.



