(** * PatternCompilation — Pattern-Match Animation

    Compiles constructor patterns of inductive types into executable
    term-level pattern matches.  The central function is
    [just_animate_pat_mat4], which takes a constructor term and produces
    a function that matches against that pattern.  [mk_mul_pat_mat_fn]
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
Definition extract_ind_decl (x : global_decl) : option mutual_inductive_body :=
  match x with
  | InductiveDecl y => Some y
  | _ => None
  end.

(** Extract all inductive type declarations from a program. *)
Definition extract_type_data (p : program) : list (option mutual_inductive_body) :=
  map extract_ind_decl ((map snd ((((declarations (fst p))))))).

(** Generate a fresh variable name of the form "vN" where N is a number. *)
Definition gen_var (n : nat) : string :=
  String.append "v" (string_of_nat (n)).

(** Generate a list of fresh variables paired with terms, starting from index s. *)
Fixpoint gen_var_lst (s : nat) (ls : list term) : list (string * term) :=
  match ls with
  | [] => []
  | h :: t => (gen_var (s + 1), h) :: gen_var_lst (s + 1) t
  end.

(** Unfold one step of constructor applications in pattern matching.
    Takes an index counter, current terms to process, resolved terms, and remaining terms.
    Returns updated counter, unprocessed terms, resolved terms, and new remaining terms. *)
Definition unfold_cons_step
  (i : nat)
  (currTs : list (string * term))
  (resolvedTs : list ((string * term) * list string))
  (remTs : list (string * term))
  : (((nat *  list (string * term)) *
      list ((string * term) * list string)) * list (string * term)) :=
 match currTs with
 | [] => (i, remTs, resolvedTs, nil)
 | (str, tApp (tConstruct typeInfo cstrInd ls') args) :: t =>
     (i + (length args), t, (str, (tConstruct typeInfo cstrInd ls'), map fst (gen_var_lst i args)) :: resolvedTs, (app (gen_var_lst i args)  remTs))
 | (str, tRel k) :: t =>
     (i, t, (str, (tRel k), nil) :: resolvedTs, remTs)
 | (str, tVar varStr) :: t =>
     (i, t, (str, (tVar varStr ), nil) :: resolvedTs, remTs)
 | (str, tConstruct typeInfo k lst) :: t =>
     (i, t, (str, (tConstruct typeInfo k lst), nil) :: resolvedTs, remTs)
 | (str, tApp <%eq%> args) :: t =>
     (i + length args, t, (str, <%eq%>, map fst (gen_var_lst i args)) :: resolvedTs, app (gen_var_lst i args) remTs)

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
    Processes terms by repeatedly applying unfold_cons_step. *)
Fixpoint unfold_cons_step_iter
  (fuel : nat)
  (st : (((nat *  list (string * term)) *
            list ((string * term) * list string)) * list (string * term)))
  : (((nat *  list (string * term)) * list ((string * term) * list string)) * list (string * term)) :=
  match fuel with
  | 0 => st
  | S m => unfold_cons_step_iter m
             (unfold_cons_step
                (fst (fst (fst st))) (snd (fst (fst st))) (snd (fst st)) (snd st))
  end.

(** Pre-process a constructor term by unfolding it into a list of variable-term pairs. *)
Definition pre_proc_cons (fuel : nat) (t : term) : list ((string * term) * list string) :=
  rev (snd (fst (unfold_cons_step_iter fuel (0, [("x"%bs, t)], [], [])))).

(** Check if all terms have been processed (no remaining terms). *)
Definition pre_proc_cons_rem (fuel : nat) (t : term) : bool :=
  let st := unfold_cons_step_iter fuel (0, [("x"%bs, t)], [], []) in
  let r := app (snd st) (snd (fst (fst st))) in
  match r with
  | [] => true
  | _ => false
  end.

(** Look up a single variable name in a list of resolved terms.
    Returns matching variable names and associated type terms. *)
Fixpoint look_up_vars_one
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
      else look_up_vars_one str t
  end.

(** Look up multiple variable names and collect their associated data. *)
Fixpoint look_up_vars
  (lsStr : list string)
  (ls : list ((string * term) * list string))
  : list string * list term :=
  match lsStr with
  | [] => ([], [])
  | (h :: t) =>
      match look_up_vars_one h ls with
      | ([], []) => look_up_vars t ls
      | ([e], []) => let rest := look_up_vars t ls in (e :: (fst rest), snd rest)
      | ([], [e]) => let rest := look_up_vars t ls in (fst rest, e :: (snd rest))
      | _ => look_up_vars t ls
      end
  end.

(** Pre-process constructor type variables, extracting relevant type information.
    Filters out equality constructors and enriches type constructor data. *)
Fixpoint pre_proc_cons_type_var
  (ls : list ((string * term) * list string))
  (ls' : list ((string * term) * list string))
  : list (((string * term) * list string) * list term) :=
  match ls' with
  | [] => []
  | (str1, <%eq%>, lstStr) :: t => pre_proc_cons_type_var ls t
  | (str1, (tConstruct typeInfo k js), lstStr) :: t =>
    (str1, (tConstruct typeInfo k js), fst (look_up_vars lstStr ls), snd (look_up_vars lstStr ls)) :: pre_proc_cons_type_var ls t
  | (_ :: t) => pre_proc_cons_type_var ls t
  end.

(** Generate a list of binder annotations with names of the form "nN". *)
Fixpoint gen_binder_name_list (n : nat) : list (binder_annot name) :=
  match n with
  | 0 => []
  | S m => {| binder_name := nNamed (String.append "n" (string_of_nat (S m))) ; binder_relevance := Relevant |} :: gen_binder_name_list m
  end.

(** Convert a list of string names into binder annotations. *)
Fixpoint gen_bin_nm_ls_str (ls : list string) : list (binder_annot name) :=
  match ls with
  | [] => []
  | h :: t => {| binder_name := nNamed h ; binder_relevance := Relevant |} :: gen_bin_nm_ls_str t
  end.

(** Create a branch with None as the body, used for non-matching constructor cases. *)
Definition mk_none_br (cstrArity : nat) (noneVal : term) : branch term :=
  {| bcontext := gen_binder_name_list cstrArity
   ; bbody := noneVal
   |}.

(** Get the declaration name at a given De Bruijn index in a context. *)
Definition get_decl_name (i : nat) (cxt : list context_decl) : option (binder_annot name) :=
  match nth_error cxt (i + 1) with
  | Some r => Some (decl_name r)
  | _ => None
  end.

(** Generate binder annotations from a list of De Bruijn indices and a context. *)
Fixpoint gen_binderannot (ind : list term) (cxt : list context_decl) : option (list (binder_annot name)) :=
  match ind with
  | [] => Some ([])
  | tRel j :: t =>
      match get_decl_name j cxt , gen_binderannot t cxt with
      | Some b , Some bs => Some (b :: bs)
      | _ , _ => None
      end
  | _ => None
  end.

(** Extract the constructor arity information from an inductive body. *)
Definition get_cs_ar (o : one_inductive_body) : string * list nat :=
 (ind_name o, map cstr_arity (ind_ctors o)).

(** Extract constructor arities for all mutually inductive types. *)
Fixpoint extract_type_cs_ar_lst (muts : list mutual_inductive_body) : list (string * list nat) :=
  match muts with
  | [] => []
  | h :: t => map get_cs_ar (ind_bodies h) ++ extract_type_cs_ar_lst t
  end.

(** Construct a term representing a list of nat variables. *)
Fixpoint ret_var_vals' (lst : list string) : term :=
  match lst with
  | [] =>  <% @nil nat %>
  | h :: rest => tApp <% @cons %> [<%nat%>; tVar h; ret_var_vals' rest]
  end.

(** Wrap a list of variables in Some constructor. *)
Definition ret_var_vals (lst : list string) : term :=
  tApp <% @Some %> [<% list nat %>; ret_var_vals' lst].

(** Sort binders by finding which variable maps to a given output variable. *)
Fixpoint sort_binders_one
  (outputVar : string)
  (lst': list ((string * term) * list string)) : list string :=
  match lst' with
  | [] => []
  | h :: rest =>
      match h with
      | (str1, (tVar y), _) =>
          if String.eqb y outputVar
          then [str1]
          else sort_binders_one outputVar rest
      | _ => sort_binders_one outputVar rest
      end
  end.

(** Sort all binders according to a list of output variables. *)
Definition sort_binders (outputVars : list string) (lst : list ((string * term) * list string)) : ((list string)) :=
  concat (map (fun x : string => sort_binders_one x lst) outputVars).

(** Get the constructor index from a resolved term structure. *)
Definition get_cstr_index (s : ((string * term) * list string)) : nat :=
  match s with
   | (str, tConstruct typeInfo k ls, lsStr) => k
   | _ => sentinel_nat
  end.

(** Get the inductive type from a resolved term structure. *)
Definition get_type (s : ((string * term) * list string)) :=
  match s with
   | (str, tConstruct typeInfo k ls, lsStr) => typeInfo
   | _ => sentinel_inductive
  end.

(** Extract the type name from a constructor term. *)
Definition get_type_nm (s : (string * term) * list string) : string :=
  match s with
  | (str,
         tConstruct {| inductive_mind := (loc, nmStr); inductive_ind := j |}
           k ls, lsStr) => nmStr
  | _ => sentinel_string
  end.

(** Check if a string is a member of a list of strings. *)
Fixpoint chk_member_str (s : string) (lStr : list string) : bool :=
  match lStr with
  | [] => false
  | (h :: t) => if (String.eqb s h) then true else chk_member_str s t
  end.

(** Filter out terms that don't correspond to valid type constructors.
    Checks against the list of mutual inductive bodies. *)
Fixpoint filter_type_con' (ls : list ((string * term) * list string)) (mut : list mutual_inductive_body) :
                         list ((string * term) * list string) :=
   match ls with
    | [] => []
    | h :: t => match h with
                 | (str,
                    tConstruct {| inductive_mind := (loc, nmStr); inductive_ind := j |}
                    k ls, lsStr) => if (chk_member_str nmStr (map fst (extract_type_cs_ar_lst mut))) then h :: (filter_type_con' t mut) else (filter_type_con' t mut)
                 | _ => (filter_type_con' t mut)
                end
   end.

(** Look up the list of constructor arities for a given type name. *)
Fixpoint get_cstr_arity_lst' (typeName : string) (r : list (string * list nat)) : list nat :=
  match r with
   | [] => sentinel_nat_list
   | (h :: t) => if String.eqb typeName (fst h) then snd h else get_cstr_arity_lst' typeName t
  end.

(** Get all constructor arities for a type by name from mutual inductives. *)
Definition get_cstr_arity_lst (typeName : string) (muts : list mutual_inductive_body) : list nat :=
 get_cstr_arity_lst' typeName (extract_type_cs_ar_lst muts).

(** Create a branch that returns None for a non-matching constructor case. *)
Definition mk_none_branch (n : nat) : branch term :=
  mk_none_br n (tApp
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
Definition mk_some_branch (l : list string) (t : term) : branch term :=
  {|
    bcontext := gen_bin_nm_ls_str l;
    bbody := t
  |}.

(** Return the first n elements of a list. *)
Fixpoint until_lst (n : nat) (l : list nat) : list nat :=
  match n with
  | 0 => []
  | S m => match l with
            | [] => []
            | h :: t => (h :: until_lst m t)
           end
  end.

(** Return the list starting after index n. *)
Fixpoint rest_lst (n : nat) (l : list nat) : list nat :=
  match n with
  | 0 => tl l
  | S m => match l with
            | [] => []
            | h :: t => rest_lst m t
           end
  end.

(** Create the list of branches for a pattern match:
    None branches before the matching constructor, a Some branch for the match,
    and None branches after. *)
Definition mk_br_lst (s : (string * term) * list string) (l : list mutual_inductive_body) (t : term) : list (branch term) :=
  let csArlst := (get_cstr_arity_lst (get_type_nm s) l) in
  let index := get_cstr_index s in
  map mk_none_branch (until_lst index csArlst) ++ [mk_some_branch (rev (snd s)) t] ++ map mk_none_branch (rest_lst index csArlst).

(** Create a case expression (pattern match) term.
    Takes a scrutinee with type parameters, inductive bodies, and a body term. *)
Definition mk_case'  (s' : ((string * term) * list string) * list term ) (l : list mutual_inductive_body) (t : term)
                      : term :=
  let s := fst s' in
  (tCase
     {|
       ci_ind := get_type s ;
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
      (mk_br_lst s l t)).

(** The identity function as a quoted term. *)
Definition identity_term := <%(fun A : Type => (fun x : A => x))%>.

(** Create nested pattern matches recursively.
    Base case returns identity, single case returns value, multiple cases nest. *)
Fixpoint mk_pm_nested' (ls : list (((string * term) * list string) * list term)) (ls' : list (((string * term) * list string))) (outputVars : list (string))
            (mut : list mutual_inductive_body) : term :=
 match ls with
  | [] => identity_term
  | (h :: nil) => mk_case' h mut (ret_var_vals (sort_binders outputVars (ls')))
  | (h :: t) => mk_case' h mut (mk_pm_nested' t ls' outputVars mut)
 end.

(** Create a nested pattern match structure from a list of constructor patterns. *)
Definition mk_pm_nested (ls' : list (((string * term) * list string))) (outputVars : list string)
            (mut : list mutual_inductive_body) : term :=
            mk_pm_nested' (pre_proc_cons_type_var ls' ls') ls' outputVars mut.

(** Remove None values from a list of options. *)
Fixpoint remove_opt {A : Type} (optls : list (option A)) : list A :=
  match optls with
  | [] => []
  | (Some x :: t) => (x :: remove_opt t)
  | (None :: t) => remove_opt t
  end.

(** Unwrap an option term, returning sentinel if None. *)
Definition unwrap_option_term (o : option term) : term :=
  match o with
  | Some t => t
  | None => sentinel_term
  end.

End typeConstrPatMatch.

(** Like [typeConstrPatMatch.mk_none_br] but with a custom wildcard return term
    instead of the default [None]. *)
Definition mk_none_branch2 (wildCardRet : term) (n : nat)  : branch term :=
  typeConstrPatMatch.mk_none_br n wildCardRet.

(** Create branch list with custom wildcard return value for non-matching cases. *)
Definition mk_br_lst2 (s : (string * term) * list string) (l : list mutual_inductive_body) (t : term) (wildCardRet : term) : list (branch term) :=
 let csArlst := (typeConstrPatMatch.get_cstr_arity_lst (typeConstrPatMatch.get_type_nm s) l) in
  let index := typeConstrPatMatch.get_cstr_index s in
  map (mk_none_branch2 wildCardRet) (typeConstrPatMatch.until_lst index csArlst) ++ [typeConstrPatMatch.mk_some_branch (rev (snd s)) t] ++ map (mk_none_branch2 wildCardRet) (typeConstrPatMatch.rest_lst index csArlst).

(** Create a case expression with custom output type and wildcard return value. *)
Definition mk_case2'  (s' : ((string * term) * list string) * list term ) (l : list mutual_inductive_body) (t : term) (outputType : term) (wildCardRet : term)
                      : term :=
  let s := fst s' in
  (tCase
     {|
       ci_ind := typeConstrPatMatch.get_type s ;
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
      (mk_br_lst2 s l t wildCardRet)).

(** Collect sets of variable names and bound variables from a pattern structure.
    Returns a pair of lists: variables with tVar terms, and all variable names. *)
Fixpoint collect_var_sets (l : list ((string * term) * list string)) : list string * list string :=
  match l with
  | [] => ([], [])
  | h :: t => match snd (fst h) with
              | tVar str => (str :: (fst (collect_var_sets t)), (app (snd h) (fst (fst h) :: snd (collect_var_sets t))))
              | _ => ((fst (collect_var_sets t)), (app (snd h) (fst (fst h) :: snd (collect_var_sets t))))
             end
  end.

(** Check that no element of l1 appears in l2 (no repeated variables). *)
Fixpoint no_repeat (l1 : list string) (l2 : list string) : bool :=
  match l1 with
  | [] => true
  | (h :: t) => negb (typeConstrPatMatch.chk_member_str h (l2)) && (no_repeat t l2)
  end.

(** Extract a mapping from original variable names to their tVar references. *)
Fixpoint orig_vars_map (l : list ((string * term) * list string)) : list (string * string) :=
  match l with
  | [] => []
  | (str, tVar str1, lst) :: t => (str, str1) :: (orig_vars_map t)
  | _ :: t => orig_vars_map t
  end.

(** Switch a single variable name according to a mapping. *)
Fixpoint switch_one_var (s : string) (map : list (string * string)) : string :=
  match map with
  | [] => s
  | (str, str1) :: t => if (String.eqb s str) then str1 else switch_one_var s t
  end.

(** Apply variable name switching to a term structure. *)
Definition switch_vars  (d : list (string * string)) (o : ((string * term) * list string)) : ((string * term) * list string) :=
  match o with
  | (s, t, l) => ((switch_one_var s d), t, (map (fun s => switch_one_var s d) l))
  end.

(** Apply variable switching to a list of terms. *)
Definition switch_vars' (d : list (string * string))  (l : list ((string * term) * list string)) :=
 (map (switch_vars d) l).

(** Change all variables in a structure to their canonical names. *)
Definition change_vars (l : list ((string * term) * list string)) : list ((string * term) * list string) :=
 switch_vars' (orig_vars_map l) l.

(** Create nested pattern matches with custom output term, type, and wildcard.
    Version 2 with more flexibility than mk_pm_nested. *)
Fixpoint mk_pm_nested2' (ls : list (((string * term) * list string) * list term)) (ls' : list (((string * term) * list string))) (outputTerm : term) (outputType : term) (wildCardRet : term)
            (mut : list mutual_inductive_body)  : term :=
 match ls with
  | [] => typeConstrPatMatch.identity_term
  | (h :: nil) => mk_case2' h mut (outputTerm) outputType wildCardRet
  | (h :: t) => mk_case2' h mut (mk_pm_nested2' t ls' outputTerm outputType wildCardRet mut) outputType wildCardRet
 end.

(** Wrapper for mk_pm_nested2' that pre-processes constructor type variables. *)
Definition mk_pm_nested2 (ls' : list (((string * term) * list string))) (outputTerm : term) (outputType : term) (wildCardRet : term)
            (mut : list mutual_inductive_body)  : term :=
            mk_pm_nested2' (typeConstrPatMatch.pre_proc_cons_type_var ls' ls') ls' outputTerm outputType wildCardRet mut.

(** Build a lambda abstraction that pattern-matches the outermost constructor,
    using [mk_pm_nested2] for the body.  Returns [None] if the structure is empty
    or lacks a two-variable binding form. *)
Definition mk_lam2' (ls : list (((string * term) * list string))) (outputTerm : term) (outputType : term) (wildCardRet : term) (mut : list mutual_inductive_body)  : option term :=
  match ls with
  | [] => None
  | (h :: ((str, typeInfo, []) :: ((str2, t', l') :: rest)))  => Some (tLambda {| binder_name := nNamed str2; binder_relevance := Relevant |}
                                 (typeInfo) (mk_pm_nested2 ls outputTerm outputType wildCardRet mut))
  | _ => None
  end.

(** Wrapper for [mk_lam2'] that filters [None] entries from the mutual inductive list. *)
Definition mk_lam2 (ls : list (((string * term) * list string))) (outputTerm : term) (outputType : term) (wildCardRet : term) (mut : list (option mutual_inductive_body))  : option term :=
  mk_lam2' ls outputTerm outputType wildCardRet (typeConstrPatMatch.remove_opt mut).

(** Compile an inductive constructor pattern [conjTm] from quoted programs [lstP]
    into a lambda that pattern-matches [conjTm] and returns [outputTerm].
    Returns [None] if the constructor cannot be fully unfolded within [fuel] steps. *)
Definition mk_lam_from_ind3 (conjTm : term) (lstP : list program) (outputTerm : term) (outputType : term) (wildCardRet : term) (fuel : nat) : option term :=
 let td := concat (map (typeConstrPatMatch.extract_type_data) lstP) in
  let pmd := conjTm in
   if (typeConstrPatMatch.pre_proc_cons_rem fuel pmd) then (mk_lam2 (change_vars (typeConstrPatMatch.pre_proc_cons fuel pmd)) outputTerm outputType wildCardRet td) else None.

(** Compile a single constructor pattern [inputTerm'] against an existing
    [animation_result inputType] into a function returning [animation_result outputType].
    Quotes the inductive type, builds nested pattern matches, and converts to de Bruijn.
    Fails if constructor variables clash or fuel is insufficient. *)
Definition just_animate_pat_mat4
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
  if andb (no_repeat (fst (collect_var_sets (typeConstrPatMatch.pre_proc_cons fuel inputTerm)))
                    (snd (collect_var_sets (typeConstrPatMatch.pre_proc_cons fuel inputTerm))))
          (typeConstrPatMatch.pre_proc_cons_rem fuel inputTerm)
  then
    t <- tmEval all (typeConstrPatMatch.unwrap_option_term
                      (DB.de_bruijn_option
                        (typeConstrPatMatch.unwrap_option_term
                          (mk_lam_from_ind3 inputTerm
                                        [termFull; outcomePolyProg; prodTpProg]
                                        outputTerm
                                        outputType
                                        wildCardRet
                                        fuel)))) ;;
    tmReturn t
  else
    tmFail "found clashing variables or insufficient fuel".

(** Animate multiple pattern branches for a single inductive predicate. *)
Fixpoint just_animate_mult_pat
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
      t <- just_animate_pat_mat4
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
      t <- just_animate_pat_mat4
             induct
             (fst h)
             inputType
             (tApp (tConstruct {| inductive_mind := <?option?>; inductive_ind := 0 |} 0 [])
                   [outputType; snd h])
             (tApp <%option%> [outputType])
             (tApp (tConstruct {| inductive_mind := <?option?>; inductive_ind := 0 |} 1 [])
                   [outputType])
             fuel ;;
      lstT <- just_animate_mult_pat induct rest inputType outputType fuel ;;
      tmReturn (t :: lstT)
  end.

(** Construct a dispatch function from a list of animated branch functions.
    Wraps with default_val to provide a fallback for unmatched inputs. *)
Definition mk_mul_pat_mat_fn' (fns : list term) (wildCardRet : term) (inputType : term) (outputType : term)  : term :=
 let fnType := tProd {| binder_name := nAnon; binder_relevance := Relevant |} inputType
         (tApp
            (tInd
               {|
                 inductive_mind := <?option?>;
                 inductive_ind := 0
               |} [])
            [outputType]) in
 (tApp <%default_val%> [inputType; outputType; wildCardRet; (tApp <%dispatch_internal%> [inputType; outputType; (mk_lst_tm' fns fnType)])]).

(** Create a multi-branch pattern match function with dispatch mechanism. *)
Definition mk_mul_pat_mat_fn
           {A : Type}
           (induct : A)
           (branchData : list (prod term term))
           (inputType : term)
           (outputType : term)
           (wildCardRet : term)
           (fuel : nat)
  : TemplateMonad term :=
  subfns <- just_animate_mult_pat induct branchData inputType outputType fuel ;;
  tmReturn (mk_mul_pat_mat_fn' subfns wildCardRet inputType outputType).

(** Fuel-aware join without LHS predicates (base case).
    Simpler version for constructors with no recursive premises. *)
Definition join_pat_mat_poly_gen_fuel_aware_no_lhs_tm {A : Type} (induct : A)
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term) (nmCon : string)
                        (fuel : nat) : TemplateMonad term :=

let postIn := tApp <%Success%> [postInType'; postIn'] in
let postInType := tApp <%animation_result%> [postInType'] in

let postOut := tApp <%Success%> [postOutType'; postOut'] in
let postOutType := tApp <%animation_result%> [postOutType'] in

tBody' <-  mk_mul_pat_mat_fn (induct) ([(postIn, (postOut)); ((tApp <%FuelError%> [postInType']),(tApp <%FuelError%> [postOutType'])) ]) postInType postOutType (tApp <%NoMatch%> [postOutType']) fuel ;;

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
                    (tApp <%fuel_error_poly_cst_fn%> [postInType; postOutType'])
                |};
                {|
                  bcontext := [{| binder_name := nNamed "remFuel"; binder_relevance := Relevant |}];
                  bbody := tBody'

                              |}]
                     )) in

t' <- tmEval all (typeConstrPatMatch.unwrap_option_term (DB.de_bruijn_option u)) ;;

tmReturn t'.

(** Compile a constructor-pattern equality [t_pattern = t_expr] into a composed
    [animation_result] function: first match the input against [t_expr] to get
    the pattern variables, then match those against [t_pattern] to produce the output. *)
Definition extract_pat_mat_binders_partial'' {A : Type} (induct : A) (kn : kername) (conjunct : named_term) (inputTm : term) (inputTp : term) (outputTm : term) (outputTp : term) (fuel : nat) : TemplateMonad term :=

  match conjunct with
  | tApp <%eq%> [typeVar; patMatTerm; tApp (func) lst] =>
                      tIn <- join_pat_mat_poly_gen_fuel_aware_no_lhs_tm induct (inputTm) (inputTp) (tApp (func) lst) typeVar (String.append (snd kn) "IN") fuel ;;
                      tOut <- join_pat_mat_poly_gen_fuel_aware_no_lhs_tm induct  patMatTerm typeVar  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;

                      let u :=
                       (tApp <%compose_outcome_poly%> [(inputTp); typeVar ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;

                      u' <- tmEval all (typeConstrPatMatch.unwrap_option_term (DB.de_bruijn_option u)) ;;

                      tmReturn u'

  | tApp <%eq%> [typeVar; patMatTerm; tVar str] =>
                      tIn <- join_pat_mat_poly_gen_fuel_aware_no_lhs_tm induct (inputTm) (inputTp) (tVar str) typeVar (String.append (snd kn) "IN") fuel ;;
                      tOut <- join_pat_mat_poly_gen_fuel_aware_no_lhs_tm induct  patMatTerm typeVar  (outputTm) (outputTp) (String.append (snd kn) "OUT") fuel ;;

                      let u :=
                       (tApp <%compose_outcome_poly%> [(inputTp); typeVar ; (outputTp) ; tIn ; tOut]) in
                      u'' <- tmEval all u ;;

                      u' <- tmEval all (typeConstrPatMatch.unwrap_option_term (DB.de_bruijn_option u)) ;;
                      tmReturn u'

  | _ => tmFail "incorrect inductive shape"
  end.

(** Orient a constructor-pattern equality so the known-variable side is on the
    right, then delegate to [extract_pat_mat_binders_partial'']. *)
Definition extract_pat_mat_binders_partial' {A : Type} (induct : A) (kn : kername) (conjunct : named_term) (inputTm : term) (inputTp : term) (outputTm : term) (outputTp : term) (inputVars : list string) (fuel : nat) : TemplateMonad term :=
  match conjunct with
  | tApp <%eq%> [typeVar; t1; t2] => if is_list_sub_str (extract_ordered_vars t1) inputVars then
                                   extract_pat_mat_binders_partial'' induct kn (tApp <%eq%> [typeVar; t2; t1]) inputTm inputTp outputTm outputTp fuel else (if is_list_sub_str (extract_ordered_vars t2) inputVars then
                                   extract_pat_mat_binders_partial'' induct kn conjunct inputTm inputTp outputTm outputTp fuel else tmFail "incorrect inductive shape")
  | _ => tmFail "incorrect inductive shape"
  end.

