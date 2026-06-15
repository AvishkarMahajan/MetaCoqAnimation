(** * PatternCompilation — Pattern-Match Animation

    Compiles constructor patterns of inductive types into executable
    term-level pattern matches.  The central function is
    [justAnimatePatMat4], which takes a constructor term and produces
    a function that matches against that pattern.  [mkMulPatMatFn]
    combines multiple branch functions into a single dispatching function.

    Depends on: [MetaRocqUtils]. *)

Require Import Animation.MetaRocqUtils.

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

(** Extract all inductive type declarations from a program. *)
Definition extractTypeData (p : program) : list (option mutual_inductive_body) :=
  map extractIndDecl ((map snd ((((declarations (fst p))))))).

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
 | (str, tConstruct typeInfo k lst) :: t =>
     (i, t, (str, (tConstruct typeInfo k lst), nil) :: resolvedTs, remTs)
 | (str, tApp <%eq%> args) :: t =>
     (i + length args, t, (str, <%eq%>, map fst (genVarlst i args)) :: resolvedTs, app (genVarlst i args) remTs)

 | (str, tApp func args) :: t =>
     (i, t, (str, tApp func args, nil) :: resolvedTs, remTs)

 | (str, tInd indType ls') :: t =>
     (i, t, (str, tInd indType ls', nil) :: resolvedTs, remTs)
 | (str, tConst indType ls') :: t =>
     (i, t, (str, tConst indType ls', nil) :: resolvedTs, remTs)
 | (str, tProd {| binder_name := nAnon; binder_relevance := Relevant |} tp1 tp2) :: t =>
     (i, t, (str, tProd {| binder_name := nAnon; binder_relevance := Relevant |} tp1 tp2, nil) :: resolvedTs, remTs)

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

(** Check if all terms have been processed (no remaining terms). *)
Definition preProcConsRem (fuel : nat) (t : term) : bool :=
  let st := unfoldConsStepIter fuel (0, [("x"%bs, t)], [], []) in
  let r := app (snd st) (snd (fst (fst st))) in
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
            | tApp (tConst typeInfo lst) args => ([], [tApp (tConst typeInfo lst) args])
            | tApp (tProd {| binder_name := nAnon; binder_relevance := Relevant |} tp1 tp2) args => ([], [tApp (tProd {| binder_name := nAnon; binder_relevance := Relevant |} tp1 tp2) args])

            | tRel k => ([str], [])
            | tVar str'' => ([str], [])
            | tInd typeInfo js => ([], [(tInd typeInfo js)])
            | tConst typeInfo lst => ([], [(tConst typeInfo lst)])
            | tProd {| binder_name := nAnon; binder_relevance := Relevant |} tp1 tp2 => ([], [(tProd {| binder_name := nAnon; binder_relevance := Relevant |} tp1 tp2)])
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
      | ([e], []) => let rest := lookUpVars t ls in (e :: (fst rest), snd rest)
      | ([], [e]) => let rest := lookUpVars t ls in (fst rest, e :: (snd rest))
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

(** Get the constructor index from a resolved term structure. *)
Definition getCstrIndex (s : ((string * term) * list string)) : nat :=
  match s with
   | (str, tConstruct typeInfo k ls, lsStr) => k
   | _ => sentinel_nat
  end.

(** Get the inductive type from a resolved term structure. *)
Definition getType (s : ((string * term) * list string)) :=
  match s with
   | (str, tConstruct typeInfo k ls, lsStr) => typeInfo
   | _ => sentinel_inductive
  end.

(** Extract the type name from a constructor term. *)
Definition getTypeNm (s : (string * term) * list string) : string :=
 match s with
  | (str,
         tConstruct {| inductive_mind := (loc, nmStr); inductive_ind := j |}
           k ls, lsStr) => nmStr
  | _ => sentinel_string
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

(** Look up the list of constructor arities for a given type name. *)
Fixpoint getCstrArityLst' (typeName : string) (r : list (string * list nat)) : list nat :=
  match r with
   | [] => sentinel_nat_list
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
Definition identityTerm := <%(fun A : Type => (fun x : A => x))%>.

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

(** Unwrap an option term, returning sentinel if None. *)
Definition unwrapOptionTerm (o : option term) : term :=
 match o with
  | Some t => t
  | None => sentinel_term
 end.

End typeConstrPatMatch.

(** Like [typeConstrPatMatch.mkNoneBr] but with a custom wildcard return term
    instead of the default [None]. *)
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

(** Build a lambda abstraction that pattern-matches the outermost constructor,
    using [mkPmNested2] for the body.  Returns [None] if the structure is empty
    or lacks a two-variable binding form. *)
Definition mkLam2' (ls : list (((string * term) * list string))) (outputTerm : term) (outputType : term) (wildCardRet : term) (mut : list mutual_inductive_body)  : option term :=
 match ls with
 | [] => None
 | (h :: ((str, typeInfo, []) :: ((str2, t', l') :: rest)))  => Some (tLambda {| binder_name := nNamed str2; binder_relevance := Relevant |}
                                 (typeInfo) (mkPmNested2 ls outputTerm outputType wildCardRet mut))
 | _ => None
 end.

(** Wrapper for [mkLam2'] that filters [None] entries from the mutual inductive list. *)
Definition mkLam2 (ls : list (((string * term) * list string))) (outputTerm : term) (outputType : term) (wildCardRet : term) (mut : list (option mutual_inductive_body))  : option term :=
  mkLam2' ls outputTerm outputType wildCardRet (typeConstrPatMatch.removeOpt mut).

(** Compile an inductive constructor pattern [conjTm] from quoted programs [lstP]
    into a lambda that pattern-matches [conjTm] and returns [outputTerm].
    Returns [None] if the constructor cannot be fully unfolded within [fuel] steps. *)
Definition mkLamfromInd3 (conjTm : term) (lstP : list program) (outputTerm : term) (outputType : term) (wildCardRet : term) (fuel : nat) : option term :=
 let td := concat (map (typeConstrPatMatch.extractTypeData) lstP) in
  let pmd := conjTm in
   if (typeConstrPatMatch.preProcConsRem fuel pmd) then (mkLam2 (changeVars (typeConstrPatMatch.preProcCons fuel pmd)) outputTerm outputType wildCardRet td) else None.

(** Compile a single constructor pattern [inputTerm'] against an existing
    [AnimationResult inputType] into a function returning [AnimationResult outputType].
    Quotes the inductive type, builds nested pattern matches, and converts to de Bruijn.
    Fails if constructor variables clash or fuel is insufficient. *)
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
  outcomePolyProg <- tmQuoteRecTransp AnimationResult false ;;
  prodTpProg <- tmQuoteRecTransp prod false ;;
  let inputTerm := tApp <%eq%> [inputType; inputTerm'; tVar "v_init"] in
  if andb (noRepeat (fst (collectVarSets (typeConstrPatMatch.preProcCons fuel inputTerm)))
                    (snd (collectVarSets (typeConstrPatMatch.preProcCons fuel inputTerm))))
          (typeConstrPatMatch.preProcConsRem fuel inputTerm)
  then
    t <- tmEval all (typeConstrPatMatch.unwrapOptionTerm
                      (DB.deBruijnOption
                        (typeConstrPatMatch.unwrapOptionTerm
                          (mkLamfromInd3 inputTerm
                                        [termFull; outcomePolyProg; prodTpProg]
                                        outputTerm
                                        outputType
                                        wildCardRet
                                        fuel)))) ;;
    tmReturn t
  else
    tmFail "found clashing variables or insufficient fuel".

(** Animate multiple pattern branches for a single inductive predicate. *)
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

(** Create a multi-branch pattern match function with dispatch mechanism. *)
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

(** Fuel-aware join without LHS predicates (base case).
    Simpler version for constructors with no recursive premises. *)
Definition joinPatMatPolyGenFuelAwareNoLHSTm {A : Type} (induct : A)
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term) (nmCon : string)
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

t' <- tmEval all (typeConstrPatMatch.unwrapOptionTerm (DB.deBruijnOption u)) ;;

tmReturn t'.

(** Compile a constructor-pattern equality [t_pattern = t_expr] into a composed
    [AnimationResult] function: first match the input against [t_expr] to get
    the pattern variables, then match those against [t_pattern] to produce the output. *)
Definition extractPatMatBindersPartial'' {A : Type} (induct : A) (kn : kername) (conjunct : named_term) (inputTm : term) (inputTp : term) (outputTm : term) (outputTp : term) (fuel : nat) : TemplateMonad term :=

match conjunct with
 | tApp <%eq%> [typeVar; patMatTerm; tApp (func) lst] =>
                      tIn <- joinPatMatPolyGenFuelAwareNoLHSTm induct (inputTm) (inputTp) (tApp (func) lst) typeVar (String.append (snd kn) "IN") fuel ;;
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  patMatTerm typeVar  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;

                      let u :=
                       (tApp <%composeOutcomePoly%> [(inputTp); typeVar ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;

                      u' <- tmEval all (typeConstrPatMatch.unwrapOptionTerm (DB.deBruijnOption u)) ;;

                      tmReturn u'

 | tApp <%eq%> [typeVar; patMatTerm; tVar str] =>
                      tIn <- joinPatMatPolyGenFuelAwareNoLHSTm induct (inputTm) (inputTp) (tVar str) typeVar (String.append (snd kn) "IN") fuel ;;
                      tOut <- joinPatMatPolyGenFuelAwareNoLHSTm induct  patMatTerm typeVar  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;

                      let u :=
                       (tApp <%composeOutcomePoly%> [(inputTp); typeVar ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;

                      u' <- tmEval all (typeConstrPatMatch.unwrapOptionTerm (DB.deBruijnOption u)) ;;
                      tmReturn u'

 | _ => tmFail "incorrect inductive shape"
 end.

(** Orient a constructor-pattern equality so the known-variable side is on the
    right, then delegate to [extractPatMatBindersPartial'']. *)
Definition extractPatMatBindersPartial' {A : Type} (induct : A) (kn : kername) (conjunct : named_term) (inputTm : term) (inputTp : term) (outputTm : term) (outputTp : term) (inputVars : list string) (fuel : nat) : TemplateMonad term :=
match conjunct with
| tApp <%eq%> [typeVar; t1; t2] => if isListSubStr (extractOrderedVars t1) inputVars then
                                   extractPatMatBindersPartial'' induct kn (tApp <%eq%> [typeVar; t2; t1]) inputTm inputTp outputTm outputTp fuel else (if isListSubStr (extractOrderedVars t2) inputVars then
                                   extractPatMatBindersPartial'' induct kn conjunct inputTm inputTp outputTm outputTp fuel else tmFail "incorrect inductive shape")
| _ => tmFail "incorrect inductive shape"
end.

