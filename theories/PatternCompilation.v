(** * PatternCompilation — Pattern-Match Animation

    Compiles constructor patterns of inductive types into executable
    term-level pattern matches.  The central function is
    [animate_one_pattern], which takes a constructor term and produces
    a function that matches against that pattern.  [mk_pattern_match_fn]
    combines multiple branch functions into a single dispatching function.

    Depends on: [MetaRocqUtils]. *)

Require Import Animation.AnimationTypes.
Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
Require Import Animation.MetaRocqUtils.

From Stdlib Require Import List.
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
Definition get_ind_body (x : global_decl) : option mutual_inductive_body :=
  match x with
  | InductiveDecl y => Some y
  | _ => None
  end.

(** Extract all inductive type declarations from a program. *)
Definition get_type_data (p : program) : list (option mutual_inductive_body) :=
  map get_ind_body ((map snd ((((declarations (fst p))))))).

(** Generate a fresh variable name of the form "vN" where N is a number. *)
Definition gen_var (n : nat) : string :=
  "v" ++ string_of_nat n.

(** Generate a list of fresh variables paired with terms, starting from index s. *)
Fixpoint gen_var_list (s : nat) (ls : list term) : list (string * term) :=
  match ls with
  | [] => []
  | h :: t => (gen_var (s + 1), h) :: gen_var_list (s + 1) t
  end.

(** Unfold one step of constructor applications in pattern matching.
    Takes an index counter, current terms to process, resolved terms, and remaining terms.
    Returns updated counter, unprocessed terms, resolved terms, and new remaining terms. *)
Definition unfold_cons
  (i : nat)
  (currTs : list (string * term))
  (resolvedTs : list resolved_var)
  (remTs : list (string * term))
  : (((nat *  list (string * term)) *
      list resolved_var) * list (string * term)) :=
 match currTs with
 | [] => (i, remTs, resolvedTs, nil)
 | (str, tApp (tConstruct typeInfo cstrInd ls') args) :: t =>
     (i + (length args), t,
      {| rv_name := str; rv_term := tConstruct typeInfo cstrInd ls';
         rv_bound := map fst (gen_var_list i args) |} :: resolvedTs,
      app (gen_var_list i args) remTs)
 | (str, tRel k) :: t =>
     (i, t, {| rv_name := str; rv_term := tRel k; rv_bound := [] |} :: resolvedTs, remTs)
 | (str, tVar varStr) :: t =>
     (i, t, {| rv_name := str; rv_term := tVar varStr; rv_bound := [] |} :: resolvedTs, remTs)
 | (str, tConstruct typeInfo k lst) :: t =>
     (i, t, {| rv_name := str; rv_term := tConstruct typeInfo k lst; rv_bound := [] |} :: resolvedTs, remTs)
 | (str, tApp <%eq%> args) :: t =>
     (i + length args, t,
      {| rv_name := str; rv_term := <%eq%>;
         rv_bound := map fst (gen_var_list i args) |} :: resolvedTs,
      app (gen_var_list i args) remTs)

 | (str, tApp func args) :: t =>
     (i, t, {| rv_name := str; rv_term := tApp func args; rv_bound := [] |} :: resolvedTs, remTs)

 | (str, tInd indType ls') :: t =>
     (i, t, {| rv_name := str; rv_term := tInd indType ls'; rv_bound := [] |} :: resolvedTs, remTs)
 | (str, tConst indType ls') :: t =>
     (i, t, {| rv_name := str; rv_term := tConst indType ls'; rv_bound := [] |} :: resolvedTs, remTs)
 | (str, tProd {| binder_name := nAnon; binder_relevance := Relevant |} tp1 tp2) :: t =>
     (i, t,
      {| rv_name := str;
         rv_term := tProd {| binder_name := nAnon; binder_relevance := Relevant |} tp1 tp2;
         rv_bound := [] |} :: resolvedTs, remTs)

 | (str, _) :: t =>
     (i, t, resolvedTs, remTs)
 end.

(** Iterate the constructor unfolding step for a given amount of fuel.
    Processes terms by repeatedly applying unfold_cons. *)
Fixpoint unfold_cons_iter
  (fuel : nat)
  (st : (((nat *  list (string * term)) *
            list resolved_var) * list (string * term)))
  : (((nat * list (string * term)) *
      list resolved_var) *
     list (string * term)) :=
  match fuel with
  | 0 => st
  | S m => unfold_cons_iter m
             (unfold_cons
                (fst (fst (fst st))) (snd (fst (fst st))) (snd (fst st)) (snd st))
  end.

(** Pre-process a constructor term by unfolding it into a list of variable-term pairs. *)
Definition preprocess_cons (fuel : nat) (t : term) : list resolved_var :=
  rev (snd (fst (unfold_cons_iter fuel (0, [("x"%bs, t)], [], [])))).

(** Check if all terms have been processed (no remaining terms). *)
Definition preprocess_remainder (fuel : nat) (t : term) : bool :=
  let st := unfold_cons_iter fuel (0, [("x"%bs, t)], [], []) in
  let r := app (snd st) (snd (fst (fst st))) in
  match r with
  | [] => true
  | _ => false
  end.

(** Look up a single variable name in a list of resolved terms.
    Returns matching variable names and associated type terms. *)
Fixpoint lookup_one_var
  (str : string)
  (ls : list resolved_var)
  : list string * list term :=
  match ls with
  | [] => ([], [])
  | (h :: t) =>
      if String.eqb str h.(rv_name)
      then (let tm := h.(rv_term) in
            match tm with
            | tConstruct typeInfo k js => ([str], [])
            | tApp (tInd typeInfo js) args => ([], [tApp (tInd typeInfo js) args])
            | tApp (tConst typeInfo lst) args => ([], [tApp (tConst typeInfo lst) args])
            | tApp (tProd
                {| binder_name := nAnon;
                   binder_relevance := Relevant |}
                tp1 tp2) args =>
              ([], [tApp (tProd
                {| binder_name := nAnon;
                   binder_relevance := Relevant |}
                tp1 tp2) args])

            | tRel k => ([str], [])
            | tVar str'' => ([str], [])
            | tInd typeInfo js => ([], [(tInd typeInfo js)])
            | tConst typeInfo lst => ([], [(tConst typeInfo lst)])
            | tProd
                {| binder_name := nAnon;
                   binder_relevance := Relevant |}
                tp1 tp2 =>
              ([], [(tProd
                {| binder_name := nAnon;
                   binder_relevance := Relevant |}
                tp1 tp2)])
            | _ => ([], [])
            end)
      else lookup_one_var str t
  end.

(** Look up multiple variable names and collect their associated data. *)
Fixpoint lookup_vars
  (lsStr : list string)
  (ls : list resolved_var)
  : list string * list term :=
  match lsStr with
  | [] => ([], [])
  | (h :: t) =>
      match lookup_one_var h ls with
      | ([], []) => lookup_vars t ls
      | ([e], []) => let rest := lookup_vars t ls in (e :: (fst rest), snd rest)
      | ([], [e]) => let rest := lookup_vars t ls in (fst rest, e :: (snd rest))
      | _ => lookup_vars t ls
      end
  end.

(** Pre-process constructor type variables, extracting relevant type information.
    Filters out equality constructors and enriches type constructor data. *)
Fixpoint preprocess_type_var
  (ls : list resolved_var)
  (ls' : list resolved_var)
  : list (resolved_var * list term) :=
  match ls' with
  | [] => []
  | h :: t =>
    match h.(rv_term) with
    | <%eq%> => preprocess_type_var ls t
    | tConstruct typeInfo k js =>
      let lv := lookup_vars h.(rv_bound) ls in
      ({| rv_name := h.(rv_name); rv_term := h.(rv_term); rv_bound := fst lv |},
       snd lv)
        :: preprocess_type_var ls t
    | _ => preprocess_type_var ls t
    end
  end.

(** Generate a list of binder annotations with names of the form "nN". *)
Fixpoint gen_binder_names (n : nat) : list (binder_annot name) :=
  match n with
  | 0 => []
  | S m =>
    {| binder_name :=
         nNamed ("n" ++ string_of_nat (S m));
       binder_relevance := Relevant |}
      :: gen_binder_names m
  end.

(** Convert a list of string names into binder annotations. *)
Fixpoint binders_from_strings (ls : list string) : list (binder_annot name) :=
  match ls with
  | [] => []
  | h :: t => {| binder_name := nNamed h ; binder_relevance := Relevant |} :: binders_from_strings t
  end.

(** Create a branch with None as the body, used for non-matching constructor cases. *)
Definition mk_wildcard_branch (cstrArity : nat) (noneVal : term) : branch term :=
  {| bcontext := gen_binder_names cstrArity
   ; bbody := noneVal
   |}.

(** Get the declaration name at a given De Bruijn index in a context. *)
Definition decl_name_at (i : nat) (cxt : list context_decl) : option (binder_annot name) :=
  match nth_error cxt (i + 1) with
  | Some r => Some (decl_name r)
  | _ => None
  end.

(** Generate binder annotations from a list of De Bruijn indices and a context. *)
Fixpoint gen_binder_annots
  (ind : list term)
  (cxt : list context_decl)
  : option (list (binder_annot name)) :=
  match ind with
  | [] => Some ([])
  | tRel j :: t =>
      match decl_name_at j cxt , gen_binder_annots t cxt with
      | Some b , Some bs => Some (b :: bs)
      | _ , _ => None
      end
  | _ => None
  end.

(** Extract the constructor arity information from an inductive body. *)
Definition get_cstr_arities (o : one_inductive_body) : string * list nat :=
 (ind_name o, map cstr_arity (ind_ctors o)).

(** Extract constructor arities for all mutually inductive types. *)
Fixpoint collect_cstr_arities (muts : list mutual_inductive_body) : list (string * list nat) :=
  match muts with
  | [] => []
  | h :: t => map get_cstr_arities (ind_bodies h) ++ collect_cstr_arities t
  end.

(** Construct a term representing a list of nat variables. *)
Fixpoint return_var_tuple_aux (lst : list string) : term :=
  match lst with
  | [] =>  <% @nil nat %>
  | h :: rest => tApp <% @cons %> [<%nat%>; tVar h; return_var_tuple_aux rest]
  end.

(** Wrap a list of variables in Some constructor. *)
Definition return_var_tuple (lst : list string) : term :=
  tApp <% @Some %> [<% list nat %>; return_var_tuple_aux lst].

(** Sort binders by finding which variable maps to a given output variable. *)
Fixpoint sort_binders_one
  (outputVar : string)
  (lst': list resolved_var) : list string :=
  match lst' with
  | [] => []
  | h :: rest =>
      match h.(rv_term) with
      | tVar y =>
          if String.eqb y outputVar
          then [h.(rv_name)]
          else sort_binders_one outputVar rest
      | _ => sort_binders_one outputVar rest
      end
  end.

(** Sort all binders according to a list of output variables. *)
Definition sort_binders
  (outputVars : list string)
  (lst : list resolved_var)
  : ((list string)) :=
  concat (map (fun x : string => sort_binders_one x lst) outputVars).

(** Get the constructor index from a resolved term structure. *)
Definition cstr_match_index (s : resolved_var) : option nat :=
  match s.(rv_term) with
   | tConstruct typeInfo k ls => Some k
   | _ => None
  end.

(** Get the inductive type from a resolved term structure. *)
Definition get_type (s : resolved_var) : option inductive :=
  match s.(rv_term) with
   | tConstruct typeInfo k ls => Some typeInfo
   | _ => None
  end.

(** Extract the type name from a constructor term. *)
Definition get_type_name (s : resolved_var) : option string :=
  match s.(rv_term) with
  | tConstruct {| inductive_mind := (loc, nmStr); inductive_ind := j |} k ls => Some nmStr
  | _ => None
  end.


(** Filter out terms that don't correspond to valid type constructors.
    Checks against the list of mutual inductive bodies. *)
Fixpoint filter_type_cstrs
  (ls : list resolved_var)
  (mut : list mutual_inductive_body)
  : list resolved_var :=
   match ls with
    | [] => []
    | h :: t =>
      match h.(rv_term) with
      | tConstruct {| inductive_mind := (loc, nmStr); inductive_ind := j |} k ls =>
        if (in_strings nmStr
              (map fst
                (collect_cstr_arities mut)))
        then h :: (filter_type_cstrs t mut)
        else (filter_type_cstrs t mut)
      | _ => (filter_type_cstrs t mut)
      end
   end.

(** Look up the list of constructor arities for a given type name. *)
Fixpoint lookup_arity_by_name (typeName : string) (r : list (string * list nat)) : list nat :=
  match r with
   | [] => []
   | (h :: t) => if String.eqb typeName (fst h) then snd h else lookup_arity_by_name typeName t
  end.

(** Get all constructor arities for a type by name from mutual inductives. *)
Definition get_arity_list (typeName : string) (muts : list mutual_inductive_body) : list nat :=
 lookup_arity_by_name typeName (collect_cstr_arities muts).

(** Create a branch that returns None for a non-matching constructor case. *)
Definition mk_option_none_branch (n : nat) : branch term :=
  mk_wildcard_branch n (tApp
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
Definition mk_option_some_branch (l : list string) (t : term) : branch term :=
  {|
    bcontext := binders_from_strings l;
    bbody := t
  |}.

(** Create the list of branches for a pattern match:
    None branches before the matching constructor, a Some branch for the match,
    and None branches after. *)
Definition mk_branch_list
  (s : resolved_var)
  (l : list mutual_inductive_body)
  (t : term) : option (list (branch term)) :=
  match get_type_name s, cstr_match_index s return option (list (branch term)) with
  | Some tn, Some index =>
    let csArlst := get_arity_list tn l in
    let branches := app (app (map mk_option_none_branch (firstn index csArlst))
      [mk_option_some_branch (rev s.(rv_bound)) t])
      (map mk_option_none_branch (skipn (S index) csArlst)) in
    Some branches
  | _, _ => None
  end.

(** Create a case expression (pattern match) term.
    Takes a scrutinee with type parameters, inductive bodies, and a body term. *)
Definition mk_case'
  (s' : resolved_var * list term)
  (l : list mutual_inductive_body)
  (t : term) : option term :=
  let s := fst s' in
  match get_type s, mk_branch_list s l t with
  | Some ind, Some branches =>
    Some (tCase
       {|
         ci_ind := ind ;
         ci_npar := length (snd s');
         ci_relevance := Relevant
       |}
       {|
         puinst := [];
         pparams := (snd s');
         pcontext := [{| binder_name := nNamed s.(rv_name); binder_relevance := Relevant |}];
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
       |} (tVar s.(rv_name))
        branches)
  | _, _ => None
  end.

(** The identity function as a quoted term. *)
Definition id_term := <%(fun A : Type => (fun x : A => x))%>.

(** Create nested pattern matches recursively.
    Base case returns identity, single case returns value, multiple cases nest. *)
Fixpoint mk_nested_match_aux
  (ls : list (resolved_var * list term))
  (ls' : list resolved_var)
  (outputVars : list (string))
  (mut : list mutual_inductive_body) : option term :=
 match ls with
  | [] => Some id_term
  | (h :: nil) => mk_case' h mut (return_var_tuple (sort_binders outputVars (ls')))
  | (h :: t) =>
    match mk_nested_match_aux t ls' outputVars mut with
    | Some inner => mk_case' h mut inner
    | None => None
    end
 end.

(** Create a nested pattern match structure from a list of constructor patterns. *)
Definition mk_nested_match (ls' : list resolved_var) (outputVars : list string)
            (mut : list mutual_inductive_body) : option term :=
            mk_nested_match_aux (preprocess_type_var ls' ls') ls' outputVars mut.

(** Remove None values from a list of options. *)
Fixpoint remove_opt {A : Type} (optls : list (option A)) : list A :=
  match optls with
  | [] => []
  | (Some x :: t) => (x :: remove_opt t)
  | (None :: t) => remove_opt t
  end.

End typeConstrPatMatch.

(** Like [typeConstrPatMatch.mk_wildcard_branch] but with a custom wildcard return term
    instead of the default [None]. *)
Definition mk_wildcard_ret_branch (wildCardRet : term) (n : nat)  : branch term :=
  typeConstrPatMatch.mk_wildcard_branch n wildCardRet.

(** Create branch list with custom wildcard return value for non-matching cases. *)
Definition mk_branch_list_wild
  (s : resolved_var)
  (l : list mutual_inductive_body)
  (t : term) (wildCardRet : term)
  : option (list (branch term)) :=
  match typeConstrPatMatch.get_type_name s, typeConstrPatMatch.cstr_match_index s with
  | Some tn, Some index =>
    let csArlst := typeConstrPatMatch.get_arity_list tn l in
    let branches := app (app (map (mk_wildcard_ret_branch wildCardRet) (firstn index csArlst))
      [typeConstrPatMatch.mk_option_some_branch (rev s.(rv_bound)) t])
      (map (mk_wildcard_ret_branch wildCardRet) (skipn (S index) csArlst)) in
    Some branches
  | _, _ => None
  end.

(** Create a case expression with custom output type and wildcard return value. *)
Definition mk_case_wild
  (s' : resolved_var * list term)
  (l : list mutual_inductive_body)
  (t : term) (outputType : term)
  (wildCardRet : term) : option term :=
  let s := fst s' in
  match typeConstrPatMatch.get_type s, mk_branch_list_wild s l t wildCardRet with
  | Some ind, Some branches =>
    Some (tCase
       {|
         ci_ind := ind ;
         ci_npar := length (snd s');
         ci_relevance := Relevant
       |}
       {|
         puinst := [];
         pparams := (snd s');
         pcontext := [{| binder_name := nNamed s.(rv_name); binder_relevance := Relevant |}];
         preturn :=
         outputType
       |} (tVar s.(rv_name))
        branches)
  | _, _ => None
  end.

(** Collect sets of variable names and bound variables from a pattern structure.
    Returns a pair of lists: variables with tVar terms, and all variable names. *)
Fixpoint collect_var_sets (l : list resolved_var) : list string * list string :=
  match l with
  | [] => ([], [])
  | h :: t => match h.(rv_term) with
              | tVar str =>
                (str :: fst (collect_var_sets t),
                 app h.(rv_bound) (h.(rv_name)
                   :: snd (collect_var_sets t)))
              | _ =>
                (fst (collect_var_sets t),
                 app h.(rv_bound) (h.(rv_name)
                   :: snd (collect_var_sets t)))
             end
  end.

(** Check that no element of l1 appears in l2 (no repeated variables). *)
Fixpoint no_repeat (l1 : list string) (l2 : list string) : bool :=
  match l1 with
  | [] => true
  | (h :: t) => negb (in_strings h (l2)) && (no_repeat t l2)
  end.

(** Extract a mapping from original variable names to their tVar references. *)
Fixpoint original_var_map (l : list resolved_var) : list (string * string) :=
  match l with
  | [] => []
  | h :: t =>
    match h.(rv_term) with
    | tVar str1 => (h.(rv_name), str1) :: (original_var_map t)
    | _ => original_var_map t
    end
  end.

(** Switch a single variable name according to a mapping. *)
Fixpoint switch_one_var (s : string) (map : list (string * string)) : string :=
  match map with
  | [] => s
  | (str, str1) :: t => if (String.eqb s str) then str1 else switch_one_var s t
  end.

(** Apply variable name switching to a term structure. *)
Definition switch_vars
  (d : list (string * string))
  (o : resolved_var)
  : resolved_var :=
  {| rv_name := switch_one_var o.(rv_name) d;
     rv_term := o.(rv_term);
     rv_bound := map (fun s => switch_one_var s d) o.(rv_bound) |}.

(** Apply variable switching to a list of terms. *)
Definition switch_vars' (d : list (string * string))  (l : list resolved_var) :=
 (map (switch_vars d) l).

(** Change all variables in a structure to their canonical names. *)
Definition change_vars
  (l : list resolved_var)
  : list resolved_var :=
 switch_vars' (original_var_map l) l.

(** Create nested pattern matches with custom output term, type, and wildcard.
    Version 2 with more flexibility than mk_nested_match. *)
Fixpoint mk_nested_match_wild_aux
  (ls : list (resolved_var * list term))
  (ls' : list resolved_var)
  (outputTerm : term) (outputType : term)
  (wildCardRet : term)
  (mut : list mutual_inductive_body) : option term :=
 match ls with
  | [] => Some typeConstrPatMatch.id_term
  | (h :: nil) => mk_case_wild h mut (outputTerm) outputType wildCardRet
  | (h :: t) =>
    match mk_nested_match_wild_aux t ls' outputTerm outputType wildCardRet mut with
    | Some inner => mk_case_wild h mut inner outputType wildCardRet
    | None => None
    end
 end.

(** Wrapper for mk_nested_match_wild_aux that pre-processes constructor type variables. *)
Definition mk_nested_match_wild
  (ls' : list resolved_var)
  (outputTerm : term) (outputType : term)
  (wildCardRet : term)
  (mut : list mutual_inductive_body) : option term :=
  mk_nested_match_wild_aux
    (typeConstrPatMatch.preprocess_type_var ls' ls')
    ls' outputTerm outputType wildCardRet mut.

(** Build a lambda abstraction that pattern-matches the outermost constructor,
    using [mk_nested_match_wild] for the body.  Returns [None] if the structure is empty
    or lacks a two-variable binding form. *)
Definition mk_lam_wild_unwrap
  (ls : list resolved_var)
  (outputTerm : term) (outputType : term)
  (wildCardRet : term)
  (mut : list mutual_inductive_body)
  : option term :=
  match ls with
  | [] => None
  | (h :: ({| rv_name := str; rv_term := typeInfo; rv_bound := [] |} ::
          ({| rv_name := str2; rv_term := t'; rv_bound := l' |} :: rest))) =>
    match mk_nested_match_wild ls outputTerm outputType wildCardRet mut with
    | Some body =>
      Some (tLambda
        {| binder_name := nNamed str2;
           binder_relevance := Relevant |}
        (typeInfo)
        body)
    | None => None
    end
  | _ => None
  end.

(** Wrapper for [mk_lam_wild_unwrap] that filters [None] entries from the mutual inductive list. *)
Definition mk_lam_wild
  (ls : list resolved_var)
  (outputTerm : term) (outputType : term)
  (wildCardRet : term)
  (mut : list (option mutual_inductive_body))
  : option term :=
  mk_lam_wild_unwrap ls outputTerm outputType wildCardRet (typeConstrPatMatch.remove_opt mut).

(** Compile an inductive constructor pattern [conjTm] from quoted programs [lstP]
    into a lambda that pattern-matches [conjTm] and returns [outputTerm].
    Returns [None] if the constructor cannot be fully unfolded within [fuel] steps. *)
Definition mk_lam_from_ind
  (conjTm : term) (lstP : list program)
  (outputTerm : term) (outputType : term)
  (wildCardRet : term) (fuel : nat)
  : option term :=
  let td :=
    concat (map (typeConstrPatMatch.get_type_data)
              lstP) in
  let pmd := conjTm in
  if (typeConstrPatMatch.preprocess_remainder
        fuel pmd)
  then
    (mk_lam_wild
       (change_vars
          (typeConstrPatMatch.preprocess_cons
             fuel pmd))
       outputTerm outputType wildCardRet td)
  else None.

(** Compile a single constructor pattern [inputTerm'] against an existing
    [animation_result inputType] into a function returning [animation_result outputType].
    Quotes the inductive type, builds nested pattern matches, and converts to de Bruijn.
    Fails if constructor variables clash or fuel is insufficient. *)
Definition animate_one_pattern
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
  outcomePolyProg <- tmQuoteRecTransp animation_result false ;;
  prodTpProg <- tmQuoteRecTransp prod false ;;
  let inputTerm := tApp <%eq%> [inputType; inputTerm'; tVar "v_init"] in
  if andb (no_repeat (fst (collect_var_sets (typeConstrPatMatch.preprocess_cons fuel inputTerm)))
                    (snd (collect_var_sets (typeConstrPatMatch.preprocess_cons fuel inputTerm))))
          (typeConstrPatMatch.preprocess_remainder fuel inputTerm)
  then
    match mk_lam_from_ind inputTerm
            [termFull; outcomePolyProg; prodTpProg]
            outputTerm outputType wildCardRet fuel with
    | Some named_t =>
      match DB.de_bruijn_option named_t with
      | Some db_t =>
        t <- tmEval all db_t ;;
        tmReturn t
      | None => tmFail "de Bruijn conversion failed in animate_one_pattern"
      end
    | None => tmFail "pattern compilation failed in animate_one_pattern"
    end
  else
    tmFail "found clashing variables or insufficient fuel".

(** Animate multiple pattern branches for a single inductive predicate. *)
Fixpoint animate_patterns
         {A : Type}
         (induct : A)
         (branchData : list (prod term term))
         (inputType : term)
         (outputType : term)
         (fuel : nat)
  : TemplateMonad (list term) :=
  match branchData with
  | [] => tmReturn []
  | h :: rest =>
      t <- animate_one_pattern
             induct
             (fst h)
             inputType
             (tApp (tConstruct {| inductive_mind := <?option?>; inductive_ind := 0 |} 0 [])
                   [outputType; snd h])
             (tApp <%option%> [outputType])
             (tApp (tConstruct {| inductive_mind := <?option?>; inductive_ind := 0 |} 1 [])
                   [outputType])
             fuel ;;
      lstT <- animate_patterns induct rest inputType outputType fuel ;;
      tmReturn (t :: lstT)
  end.

(** Construct a dispatch function from a list of animated branch functions.
    Wraps with with_default to provide a fallback for unmatched inputs. *)
Definition mk_pattern_fn_core
  (fns : list term) (wildCardRet : term)
  (inputType : term) (outputType : term) : term :=
 let fnType := tProd {| binder_name := nAnon; binder_relevance := Relevant |} inputType
         (tApp
            (tInd
               {|
                 inductive_mind := <?option?>;
                 inductive_ind := 0
               |} [])
            [outputType]) in
 (tApp <%with_default%>
   [inputType; outputType; wildCardRet;
    (tApp <%dispatch_clauses%>
       [inputType; outputType;
        (build_coq_list fns fnType)])]).

(** Create a multi-branch pattern match function with dispatch mechanism. *)
Definition mk_pattern_match_fn
           {A : Type}
           (induct : A)
           (branchData : list (prod term term))
           (inputType : term)
           (outputType : term)
           (wildCardRet : term)
           (fuel : nat)
  : TemplateMonad term :=
  subfns <- animate_patterns induct branchData inputType outputType fuel ;;
  tmReturn (mk_pattern_fn_core subfns wildCardRet inputType outputType).

(** Fuel-aware join without LHS predicates (base case).
    Simpler version for constructors with no recursive premises. *)
Definition join_pattern_fueled
  {A : Type} (induct : A)
  (postIn' : term) (postInType' : term)
  (postOut' : term) (postOutType' : term)
  (nmCon : string) (fuel : nat)
  : TemplateMonad term :=
(* Wrap raw terms in Success/animation_result for the pattern match fn *)
let postIn := tApp <%Success%> [postInType'; postIn'] in
let postInType := tApp <%animation_result%> [postInType'] in

let postOut := tApp <%Success%> [postOutType'; postOut'] in
let postOutType := tApp <%animation_result%> [postOutType'] in
(* Build a dispatch fn: Success input -> Success output, FuelError -> FuelError *)
tBody' <-
  mk_pattern_match_fn (induct)
    ([(postIn, (postOut));
      ((tApp <%FuelError%> [postInType']),
       (tApp <%FuelError%> [postOutType']))])
    postInType postOutType
    (tApp <%NoMatch%> [postOutType']) fuel ;;
(* Wrap in a fuel-decrementing case: 0 -> fuel_error, S n -> dispatch *)
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
                   (tProd
                     {| binder_name := nAnon;
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

match DB.de_bruijn_option u with
| Some db_t =>
  t' <- tmEval all db_t ;;
  tmReturn t'
| None => tmFail "de Bruijn conversion failed in join_pattern_fueled"
end.

(** Compile a constructor-pattern equality [t_pattern = t_expr] into a composed
    [animation_result] function: first match the input against [t_expr] to get
    the pattern variables, then match those against [t_pattern] to produce the output.
    The [rhsTerm] is the right-hand side of the equality (either a [tApp] or [tVar]). *)
Definition compile_eq_binders
  {A : Type} (induct : A) (kn : kername)
  (conjunct : named_term)
  (inputTm : term) (inputTp : term)
  (outputTm : term) (outputTp : term)
  (fuel : nat) : TemplateMonad term :=
  match conjunct with
  | tApp <%eq%> [typeVar; patMatTerm; rhsTerm] =>
      tIn <- join_pattern_fueled induct
               inputTm inputTp rhsTerm typeVar
               (snd kn ++ "IN")
               fuel ;;
      tOut <- join_pattern_fueled induct
                patMatTerm typeVar outputTm outputTp
                (snd kn ++ "OUT")
                fuel ;;
      let u := tApp <%compose_outcome%> [inputTp; typeVar; outputTp; tIn; tOut] in
      match DB.de_bruijn_option u with
      | Some db_u =>
        u' <- tmEval all db_u ;;
        tmReturn u'
      | None => tmFail "de Bruijn conversion failed in compile_eq_binders"
      end
  | _ => tmFail "incorrect inductive shape"
  end.

(** Orient a constructor-pattern equality so the known-variable side is on the
    right, then delegate to [compile_eq_binders]. *)
Definition compile_eq_binders_with_vars
  {A : Type} (induct : A) (kn : kername)
  (conjunct : named_term)
  (inputTm : term) (inputTp : term)
  (outputTm : term) (outputTp : term)
  (inputVars : list string) (fuel : nat)
  : TemplateMonad term :=
  match conjunct with
  | tApp <%eq%> [typeVar; t1; t2] =>
    if is_subset_strings (ordered_vars t1)
         inputVars
    then
      compile_eq_binders induct kn
        (tApp <%eq%> [typeVar; t2; t1])
        inputTm inputTp outputTm outputTp fuel
    else
      (if is_subset_strings (ordered_vars t2)
            inputVars
       then
         compile_eq_binders induct kn conjunct
           inputTm inputTp outputTm outputTp fuel
       else tmFail "incorrect inductive shape")
  | _ => tmFail "incorrect inductive shape"
  end.

