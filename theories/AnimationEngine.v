(** * AnimationEngine — Main Animation Pipeline

    Top-level entry points [animate_inductive] and [animate_coinductive] that
    orchestrate the full animation pipeline: clause data extraction, term
    rewriting, clause-by-clause compilation via [compile_clause_body],
    and final fixpoint assembly into a quoted Rocq definition.

    Depends on: [MetaRocqUtils], [PatternCompilation], [EqualityResolution],
    [AnimationDispatch]. *)

Require Import Animation.AnimationDispatch.

Require Import Animation.EqualityResolution.

Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.

From Stdlib Require Import List.
From Stdlib Require Streams.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.

Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.

(** Replace any variable appearing in a function-position in [conjRHS] with
    an [id_fn] application, so that the variable is treated as data rather
    than as a function call during pattern compilation. *)
Fixpoint strip_fn_position_vars (conjRHS : term)  (allVarTpInf : list (string * term)) :=
  match conjRHS with
  | tApp (tVar str) lstArgs =>
      match lookup_one_var str allVarTpInf with
      | [h] =>
        tApp <%id_fn%>
          ((snd h) :: (tVar str)
            :: (map (fun arg =>
                  strip_fn_position_vars arg allVarTpInf)
                lstArgs))
      | _ =>
        tApp (tVar str)
          (map (fun arg =>
              strip_fn_position_vars arg allVarTpInf)
            lstArgs)
      end
  | tApp fn lstArgs =>
      tApp (strip_fn_position_vars fn allVarTpInf)
        (map (fun arg =>
            strip_fn_position_vars arg allVarTpInf)
          lstArgs)
  | _ => conjRHS
  end.

(** Apply [strip_fn_position_vars] to the RHS of an equality conjunct,
    leaving non-equality conjuncts unchanged. *)
Definition strip_fn_vars
  (conjunct' : tagged_conjunct)
  (allVarTpInf : list (string * term)) : tagged_conjunct :=
  match conjunct'.(tc_conjunct) with
  | tApp <%eq%> [typeVar; t1; t2] =>
      let newConj :=
        tApp <%eq%>
          [typeVar; t1;
           strip_fn_position_vars t2 allVarTpInf]
      in {| tc_conjunct := newConj;
            tc_out_var := conjunct'.(tc_out_var);
            tc_out_type := conjunct'.(tc_out_type) |}
  | _ => conjunct'
  end.

(** Functor map over [animation_result]: applies [f] to a [Success] value and
    propagates [FuelError] and [NoMatch] unchanged. *)
Definition map_outcome (A : Type) (B : Type)
  (f : A -> B) (a : animation_result A)
  : animation_result B :=
  match a with
  | FuelError  => FuelError B
  | Success a' => Success B (f a')
  | NoMatch => NoMatch B
  end.

(** Extract inductive names from bodies. *)
Definition ind_body_names (l : list one_inductive_body) :=
map (fun o => ind_name o) l.

(** Generate context from inductive names. *)
Definition gen_cxt (l : list one_inductive_body) :=
(map (fun s => nNamed s) (rev (ind_body_names l))).

(** Extract all argument types from an inductive type. *)
Fixpoint get_type (o : term) : list term :=
  match o with
       | (tProd {| binder_name := nAnon; binder_relevance := Relevant |} t (tSort sProp)) => [t]
       | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1  t2 => t1 :: get_type t2
       | _ => [sentinel_term]
  end.

(** Select types according to mode indices. *)
Definition get_type' (mode : list nat) (l : list term) :=
map (fun n => nth n l sentinel_term) mode.

(** Get input type according to mode. *)
Definition input_types (inMode : list nat) (o : one_inductive_body) : list term  :=
 let lstType := get_type (ind_type o) in
  (get_type' inMode lstType).

(** Strip all top-level foralls/products from a term to get to the body. *)
Fixpoint reduce_clause (t : term) :=
  match t with
  | (tPro str typ t') => reduce_clause t'
  | t'' => t''
  end.

(** Extract preconditions (hypotheses) from a constructor clause. *)
Definition get_preconditions (t : term) :=
  match t with
  | (tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2) => [t1]
  | _ => []
  end.

(** Process preconditions, splitting conjunctions. *)
Definition process_preconditions (l : list term) :=
  match l with
  | [] => []
  | [tApp <%and%> l'] => l'
  | [t'] => [t']
  | _ :: (h' :: _) => []
  end.

(** Get the body (recursive premises) of a constructor clause. *)
Definition clause_body_raw (t : term) : list term :=
process_preconditions (get_preconditions (reduce_clause t)).

(** Get the head (conclusion) of a constructor clause. *)
Definition clause_head_raw (t : term) : term :=
  match reduce_clause t with
  | (tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2) => t2
  | t' => t'
  end.

(** Extract body from a constructor. *)
Definition clause_body (c : constructor_body) : list term :=
 clause_body_raw (cstr_type c).

(** Extract head from a constructor. *)
Definition clause_head (c : constructor_body) :  term :=
 clause_head_raw (cstr_type c).

(** Extract names of inductive predicates applied in a list of terms. *)
Fixpoint ind_occurrences (l : list term) (indNames : list string) : list string :=
  match l with
  | [] => []
  | h :: t => match h with
              | tApp (tVar str) args =>
                  if (in_strings str indNames)
                  then (str :: (ind_occurrences t indNames))
                  else (ind_occurrences t indNames)
              | _ => (ind_occurrences t indNames)
              end
  end.

(** Annotate each clause with the inductive predicate names it applies. *)
Fixpoint ind_occurrences_named
  (l : list (string * term))
  (indNames : list string)
  : list (string * (list string)) :=
  match l with
  | [] => []
  | h :: t =>
      (fst h,
        ind_occurrences (clause_body_raw (snd h)) indNames)
      :: ind_occurrences_named t indNames
  end.

(** Get input/output types for all inductives according to mode specifications. *)
Fixpoint in_out_types_one
  (mode : (string * ((list nat) * (list nat))))
  (b : list one_inductive_body)
  : list ((string * list term) * list term) :=
  match b with
    | h' :: t' =>
        if String.eqb (fst mode) (ind_name h')
        then [(ind_name h',
               input_types (fst (snd mode)) h',
               input_types (snd (snd mode)) h')]
        else in_out_types_one mode t'
    | _ => []
    end.

(** Get input/output types for all inductives in the mode list. *)
Fixpoint in_out_types (modes : mode_map)
  (b : list one_inductive_body)
  : list ((string * list term) * list term) :=
  match modes with
  | [] => []
  | h :: t => in_out_types_one h b ++ in_out_types t b
  end.

(** Convert constructor bodies to named terms by unquoting from de Bruijn into
    the named context [l], returning [(constructor_name, clause_term)] pairs. *)
Fixpoint mk_nm_tm (c : list constructor_body)
  (l : list name)
  : TemplateMonad (list (string * term)) :=
  match c with
  | [] => tmReturn []
  | (h :: t) =>
      r <- DB.un_de_bruijn' l ((cstr_type h )) ;;
      r' <- tmEval all r ;;
      let hres := (cstr_name h, (reduce_clause r')) in
      rest <- mk_nm_tm t l ;;
      tmReturn (hres :: rest)
  end.

(** Retrieve clause data for all inductives in [lib]: for each body, convert
    constructors to named terms and pair them with their input/output type info. *)
Fixpoint get_data
  (lib : list one_inductive_body)
  (ln : mode_map) (nmCxt : list name)
  (inOutTps : list ((string * list term) * list term))
  : TemplateMonad (list clause_data) :=

  match lib with
  | [] => tmReturn []
  | h' :: t' => match inOutTps with
                 | h :: t =>
                     dbth <- mk_nm_tm (ind_ctors h') nmCxt ;;
                     rest <- get_data t' (ln) nmCxt (tl inOutTps) ;;
                     tmReturn ({| cd_ind_name := fst (fst h);
                                  cd_in_types := snd (fst h);
                                  cd_out_types := snd h;
                                  cd_clauses := dbth |} :: rest)
                 | _ => tmReturn []
                 end

  end.

(** Replace non-variable subterms in [l] with fresh variables (prefixed by
    [varPfix]), emitting equality constraints to bind the originals.
    Returns triples [(replacement_vars, equality_constraints, new_var_bindings)]. *)
Fixpoint subst_pattern_vars (l : list term)
  (varPfix : string) (n : nat) (argTps : list term)
  : list ((list term * list term)
          * list (string * term)) :=
  match l with
  | [] => []
  | (tVar str) :: rest =>
      (([(tVar str)], []), [])
      :: (subst_pattern_vars rest varPfix n (tl argTps))
  | t' :: rest =>
      let vn :=
        (varPfix ++ (string_of_nat n)) in
      (([(tVar vn)],
        [tApp <%eq%>
          [(hd <%bool%> argTps); (tVar vn); t']]),
       ([(vn, (hd <%bool%> argTps))]))
      :: (subst_pattern_vars rest varPfix (S n)
            (tl argTps))

  end.
(** Look up the argument types for predicate named [s] in the type environment. *)
Fixpoint find_tp (s : string) (allPredArgTps : pred_type_map) : list term :=
  match allPredArgTps with
  | [] => []
  | h :: t => if String.eqb s (fst h) then snd h else find_tp s t
  end.

(** For each conjunct in [l], replace non-variable arguments of predicates with
    fresh variables and collect the resulting equality side-conditions and
    new variable bindings.  Equality conjuncts are passed through unchanged. *)
Fixpoint resolve_conj_inputs (l : list term)
  (varPfix : string) (n : nat)
  (allPredArgTps : pred_type_map)
  : list ((term * list term) * list (string * term)) :=
  match l with
  | [] => []
  | (tApp <%eq%> lstArgs) :: rest =>
      (((tApp <%eq%> lstArgs) , []), [])
      :: resolve_conj_inputs (rest) (varPfix) (n)
           (allPredArgTps)
  | (tApp (tVar str) lstArgs) :: rest =>
      let result :=
        subst_pattern_vars lstArgs varPfix n
          (find_tp str allPredArgTps) in
      ((((tApp (tVar str)
            (concat (map (fun y => fst (fst y))
               result)))),
        (concat (map (fun y => snd (fst y)) result))),
       (concat (map snd result)))
      :: resolve_conj_inputs (rest) (varPfix)
           ((length lstArgs) + (S n)) (allPredArgTps)
  | (tApp (tInd {| inductive_mind := (_path, indNm);
       inductive_ind := 0 |} []) lstArgs) :: rest =>
      let result :=
        subst_pattern_vars lstArgs varPfix n
          (find_tp indNm allPredArgTps) in
      let ind := tInd {| inductive_mind := (_path, indNm);
                         inductive_ind := 0 |} [] in
      ((((tApp ind
            (concat (map (fun y => fst (fst y))
               result)))),
        (concat (map (fun y => snd (fst y)) result))),
       (concat (map snd result)))
      :: resolve_conj_inputs (rest) (varPfix)
           ((length lstArgs) + (S n)) (allPredArgTps)

  | t'' :: rest => ((t'', []), []) :: resolve_conj_inputs (rest) (varPfix) (n) (allPredArgTps)

  end.

(** Collect variable and inductive names from a term, with arguments listed
    before the function (used for computing fresh-variable prefix lengths). *)
Fixpoint ordered_vars_from_clause (t : term) : list string :=
  match t with
  | tVar str  => [str]
  | (tInd {| inductive_mind := (_path, str); inductive_ind := k |} []) => [str]
  | tApp fn lst => app (concat (map ordered_vars_from_clause lst)) (ordered_vars_from_clause fn)

  | tProd {| binder_name := nAnon;
             binder_relevance := Relevant |} t1 t2 =>
      ordered_vars_from_clause t1 ++
        ordered_vars_from_clause t2
  | _ => []
  end.

(** Build a fresh variable prefix of length [n+1] using the letter "j".
    Used to guarantee freshness: choose [n] larger than the longest existing name. *)
Fixpoint fresh_var_prefix (n : nat) : string :=
  match n with
  | 0 => "j"
  | S m => "j" ++ fresh_var_prefix m
  end.

(** Extract the [(name, type)] pairs for every inductive predicate. *)
Definition pred_arg_types_raw (allTpInf : list type_env_entry) : list (string * term) :=
map (fun y => (y.(te_pred_name), y.(te_pred_type))) allTpInf.

(** Build a [(name, arg_types)] environment for all inductive predicates by
    destructuring each predicate's type into its argument list. *)
Definition pred_arg_types (allTpInf : list type_env_entry) : list (string * list term) :=
map (fun y => (fst y, get_type (snd y))) (pred_arg_types_raw allTpInf).
(** Flatten a right-nested [and] tree into a list of conjuncts. *)
Fixpoint flatten_and (t : term) : list term :=
  match t with
  | tApp <%and%> [h;h1] => h :: (flatten_and h1)
  | t' => [t']
  end.

(** Split a clause of the form [P1 /\ P2 /\ ... -> conclusion] into the list
    [P1, P2, ..., conclusion]; handles a conjunction in the premise position. *)
Definition flatten_clause (t : term) : list term :=
  match t with
  | tProd {| binder_name := nAnon;
             binder_relevance := Relevant |}
      (tApp <%and%> lst) t' =>
      app ((flatten_and (tApp <%and%> lst))) [t']
  | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t'' t' =>  [t''; t']
  | t''' => [t''']
  end.
(** Rebuild a right-nested [and] term from a flat list of conjuncts. *)
Fixpoint build_and (l : list term) : term :=
  match l with
  | [] => sentinel_term
  | [h] => h
  | h :: rest => tApp <%and%> [h; build_and rest]
  end.
(** Inverse of [flatten_clause]: reassemble a flat list [P1, ..., Pn, conclusion]
    back into a single clause term. *)
Definition build_clause (ts : list term) : term :=
  match rev ts with
  | [] => sentinel_term
  | [h] => h
  | [h1; h2] => tProd {| binder_name := nAnon; binder_relevance := Relevant |} h2 h1
  | h :: t => tProd {| binder_name := nAnon; binder_relevance := Relevant |} (build_and (rev t)) h
  end.

(** Rewrite a clause by substituting non-variable predicate arguments with fresh
    variables and splicing in the resulting equality side-conditions. *)
Definition rewrite_cl (t : term) (allTpInf : list type_env_entry) : term :=
let prefix := fresh_var_prefix (S (list_max (map String.length (ordered_vars_from_clause t)))) in
let lstTm := flatten_clause t in
let allPredArgTp := pred_arg_types allTpInf in
let resolved := resolve_conj_inputs lstTm prefix 0 allPredArgTp in
build_clause
  (concat (map (fun y => snd (fst y)) resolved) ++
   map (fun y => fst (fst y)) resolved).

(** Collect the new variable-type bindings introduced by rewriting clause [t]. *)
Definition extra_type_info (t : term) (allTpInf : list type_env_entry) : list (string * term) :=

let prefix := fresh_var_prefix (S (list_max (map String.length (ordered_vars_from_clause t)))) in
let lstTm := flatten_clause t in
let allPredArgTp := pred_arg_types allTpInf in
(concat (map (fun y => (snd (y))) (resolve_conj_inputs lstTm prefix 0 allPredArgTp))).

(** Rewrite all clause terms in a flat [(constructor_name, clause)] list. *)
Fixpoint rewrite_cl_all1
  (allClauseData1 : list (string × term))
  (allTpInf : list type_env_entry)
  : (list (string × term)) :=
  match allClauseData1 with
  | [] => []
  | (cstrNm,t) :: rest => (cstrNm, rewrite_cl t allTpInf) :: (rewrite_cl_all1 rest allTpInf)
  end.

(** Rewrite the clause data block for a single inductive. *)
Definition rewrite_cl_all1'
  (allClauseData1 : clause_data)
  (allTpInf : list type_env_entry) : clause_data :=
  {| cd_ind_name := allClauseData1.(cd_ind_name);
     cd_in_types := allClauseData1.(cd_in_types);
     cd_out_types := allClauseData1.(cd_out_types);
     cd_clauses := rewrite_cl_all1 allClauseData1.(cd_clauses) allTpInf |}.

(** Rewrite all clause data blocks across all inductives. *)
Definition rewrite_cl_all
  (allClauseData : list clause_data)
  (allTpInf : list type_env_entry)
  : list clause_data :=
map (fun y => rewrite_cl_all1' y allTpInf) allClauseData.

(** Collect new variable-type bindings for each clause in a flat clause list. *)
Fixpoint extra_type_info_list
  (allClauseData1 : list (string × term))
  (allTpInf : list type_env_entry)
  : list (string * list (string * term)) :=
  match allClauseData1 with
  | [] => []
  | (cstrNm, t) :: rest =>
      (cstrNm, extra_type_info t allTpInf)
      :: extra_type_info_list rest allTpInf
  end.

(** Collect new variable-type bindings for every inductive's clause data. *)
Fixpoint all_extra_type_info
  (allClauseData : list clause_data)
  (allTpInf : list type_env_entry)
  : list (string *
          (list (string * list (string * term)))) :=
  match allClauseData with
  | [] => []
  | h :: rest =>
      (h.(cd_ind_name),
       extra_type_info_list h.(cd_clauses) allTpInf)
      :: (all_extra_type_info rest allTpInf)
  end.

(** Look up [cstrNm] in an association list of constructor-name → type bindings. *)
Fixpoint retrieve (cstrNm : string)
  (l : list (string × list (string × term)))
  : list (string * term) :=
  match l with
  | [] => []
  | h :: rest => if (String.eqb cstrNm (fst h)) then (snd h) else retrieve cstrNm rest
  end.

(** Retrieve the original type bindings for constructor [cstrNm] of [indNm]. *)
Fixpoint old_type_info (indNm : string)
  (cstrNm : string)
  (allTpInf : list type_env_entry)
  : list (string * term) :=
  match allTpInf with
  | [] => []
  | h :: rest =>
      if (String.eqb indNm h.(te_pred_name))
      then retrieve cstrNm h.(te_cstr_vars)
      else old_type_info indNm cstrNm rest
  end.

(** Retrieve the newly-introduced (fresh-variable) type bindings for
    constructor [cstrNm] of [indNm] after clause rewriting. *)
Fixpoint new_type_info (indNm : string)
  (cstrNm : string)
  (extraTpInf : list ((string) × list
    (string × list (string × term))))
  : list (string * term) :=
  match extraTpInf with
  | [] => []
  | (str, lst) :: rest =>
      if (String.eqb indNm str)
      then retrieve cstrNm lst
      else new_type_info indNm cstrNm rest
  end.
(** Merge original and fresh-variable type bindings for one inductive block. *)
Definition update_type_info
  (allTpInf1 : type_env_entry)
  (allTpInf : list type_env_entry)
  (extraTpInf : list ((string) × list
    (string × list (string × term)))) : type_env_entry :=
  let indNm := allTpInf1.(te_pred_name) in
  {| te_pred_name := indNm;
     te_pred_type := allTpInf1.(te_pred_type);
     te_cstr_vars :=
       map (fun y =>
         ((fst y),
          app (old_type_info indNm (fst y) allTpInf)
              (new_type_info indNm (fst y) extraTpInf)))
         allTpInf1.(te_cstr_vars) |}.

(** Apply [update_type_info] to every inductive block in [allTpInf1l]. *)
Definition update_type_info_list
  (allTpInf1l : list type_env_entry)
  (allTpInf : list type_env_entry)
  (extraTpInf : list ((string) × list
    (string × list (string × term)))) :=
map (fun y => update_type_info y allTpInf extraTpInf) allTpInf1l.

(** Self-update: merge each inductive block's extra type info into itself. *)
Definition finalize_type_info_one
  (allTpInf : list type_env_entry)
  (extraTpInf : list ((string) × list
    (string × list (string × term)))) :=
update_type_info_list allTpInf allTpInf extraTpInf.

(** Compute the final, fully-merged type environment after clause rewriting:
    derives extra bindings from [allClauseData] and folds them into [allTpInf]. *)
Definition finalize_type_info
  (allClauseData : list clause_data)
  (allTpInf : list type_env_entry)
  : (list type_env_entry) :=
finalize_type_info_one allTpInf  (all_extra_type_info allClauseData allTpInf).

(** Extract the list of definitions from a fixpoint term. *)
Definition inspect_fix (t : term) : list (def term) :=
  match t with
  | tFix l k => l
  | _ => []
  end.

(** Build a [tConst] reference to definition [nm] in the module of [kn]. *)
Definition quote_const' (kn : kername) (nm : string) :=
tConst (fst kn, nm) [].

(** For each clause, build the quoted reference to its compiled [Animated]
    definition, applied to the animated top-level functions of any predicates
    it calls recursively. *)
Fixpoint apply_top_fn (kn : kername) (clauseData : list (string * (list string))) : list term :=
  match clauseData with
  | [] => []
  | (postConCons, preConInd) :: t => match preConInd with
                                   | [] =>
                                       (quote_const' kn
                                         (postConCons ++ anim_suffix))
                                       :: apply_top_fn kn t
                                   | l =>
                                       tApp
                                         (quote_const' kn
                                           (postConCons ++ anim_suffix))
                                         (map (fun nm =>
                                           tVar (nm ++ top_fn_suffix)) l)
                                       :: apply_top_fn kn t
                                   end
  end.

(** Return the input-position indices for [indNm] in the mode list, or [[]]
    if [indNm] has no explicit input positions (empty-input mode). *)
Fixpoint lookup_mode_input (indNm : string) (modes : mode_map) :=
  match modes with
  | [] => []
  | (h :: rest) => if String.eqb indNm (fst h) then fst (snd h) else lookup_mode_input indNm rest
  end.
(** Shared base for building one fixpoint definition for a top-level animated inductive.
    Parameterized by the zero-fuel branch, dispatch construction, and whether input is explicit. *)
Definition mk_ind_top_base (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername)
  (zeroBranch : term) (mkDispatchBody : term -> term)
  (hasInput : bool) : def term :=
let fnListTp := tProd {| binder_name := nAnon; binder_relevance := Relevant |}
      <%nat%> (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
     (tApp <%animation_result%> [inputType]) (tApp <%animation_result%> [outputType])) in
let listTm := build_coq_list (apply_top_fn kn clauseData) fnListTp in
let caseExpr :=
  tCase
    {| ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
       ci_npar := 0; ci_relevance := Relevant |}
    {| puinst := []; pparams := [];
       pcontext := [{| binder_name := nNamed "fuel"; binder_relevance := Relevant |}];
       preturn := tApp <%animation_result%> [outputType] |}
    (tVar "fuel")
    [{| bcontext := []; bbody := zeroBranch |};
     {| bcontext := [{| binder_name := nNamed "remFuel"; binder_relevance := Relevant |}];
        bbody := mkDispatchBody listTm |}] in
let inputLam := tLam "input" (tApp <%animation_result%> [inputType]) caseExpr in
let body :=
  tLam "fuel" <%nat%>
    (if hasInput then inputLam else tApp inputLam [<%Success bool true%>]) in
let tp :=
  if hasInput
  then tPro "fuel" <%nat%> (tPro "input" (tApp <%animation_result%> [inputType])
         (tApp <%animation_result%> [outputType]))
  else tPro "fuel" <%nat%> (tApp <%animation_result%> [outputType]) in
{| dname := {| binder_name := nNamed ((indNm ++ top_fn_suffix));
               binder_relevance := Relevant |};
   dtype := tp; dbody := body; rarg := 0 |}.

(** Build a top-level fixpoint definition for an inductive with explicit input. *)
Definition mk_ind_top_body (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername) : def term :=
mk_ind_top_base indNm inputType outputType clauseData kn
  (tApp <%FuelError%> [outputType])
  (fun listTm => tApp (tVar "dispatch_ind_ext")
     [inputType; outputType; listTm; tVar "remFuel"; tVar "input"])
  true.

(** Build a top-level fixpoint definition for an inductive with no input
    (empty-input mode: the argument is always [Success bool true]). *)
Definition mk_ind_top_no_input (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername) : def term :=
mk_ind_top_base indNm inputType outputType clauseData kn
  (tApp <%FuelError%> [outputType])
  (fun listTm => tApp (tVar "dispatch_ind_ext")
     [inputType; outputType; listTm; tVar "remFuel"; tVar "input"])
  false.

(** Build a top-level fixpoint definition for a coinductive with explicit input,
    using [map_outcome Rest] as the zero-fuel branch. *)
Definition mk_coind_top_body (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername) : def term :=
let restFn := quote_const' kn ((indNm ++ "Rest")) in
mk_ind_top_base indNm inputType outputType clauseData kn
  (tApp <%map_outcome%> [inputType; outputType; restFn; tVar "input"])
  (fun listTm => tApp (tVar "dispatch_coind_ext")
     [inputType; outputType; restFn; listTm; tVar "remFuel"; tVar "input"])
  true.

(** Build a top-level fixpoint definition for a coinductive with no input,
    using [map_outcome Rest] as the zero-fuel branch. *)
Definition mk_coind_top_no_input (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername) : def term :=
let restFn := quote_const' kn ((indNm ++ "Rest")) in
mk_ind_top_base indNm inputType outputType clauseData kn
  (tApp <%map_outcome%> [inputType; outputType; restFn; tVar "input"])
  (fun listTm => tApp (tVar "dispatch_coind_ext")
     [inputType; outputType; restFn; listTm; tVar "remFuel"; tVar "input"])
  false.

(** Dispatch to [mk_ind_top_body] or [mk_ind_top_no_input] based on the mode for [indNm]. *)
Definition mk_ind_fixpoint (indNm : string)
  (inputType : term) (outputType : term)
  (clauseData : list (string * (list string)))
  (kn : kername) (modes : mode_map) : def term :=
  match lookup_mode_input indNm modes with
  | [] => mk_ind_top_no_input indNm inputType outputType clauseData kn
  | _ => mk_ind_top_body indNm inputType outputType clauseData kn
  end.

(** Dispatch to [mk_coind_top_body] or [mk_coind_top_no_input] based on mode. *)
Definition mk_coind_fixpoint (indNm : string)
  (inputType : term) (outputType : term)
  (clauseData : list (string * (list string)))
  (kn : kername) (modes : mode_map) : def term :=
  match lookup_mode_input indNm modes with
  | [] => mk_coind_top_no_input indNm inputType outputType clauseData kn
  | _ => mk_coind_top_body indNm inputType outputType clauseData kn
  end.

(** Construct a fixpoint term from a list of definitions. *)
Definition mk_rec_fn (ls : list (def term)) (j : nat) : term :=
 tFix ls j.

(** Apply [mkOneFn] to every inductive in [inductData], building the full list
    of fixpoint definitions for the mutual recursive block. *)
Definition mk_all_fixpoints
  (mkOneFn : string -> term -> term ->
    list (string * list string) -> kername ->
    list (string * (list nat * list nat)) ->
    def term)
  (inductData : list fixpoint_entry)
  (kn : kername) (modes : mode_map)
  : list (def term) :=
  map (fun h =>
    mkOneFn h.(fe_ind_name)
      h.(fe_in_type) h.(fe_out_type)
      h.(fe_cstr_preds) kn modes) inductData.

(** Extended dispatch for animation_result types with fuel.
    Tries each function in the list, skipping noMatch results. *)
Fixpoint dispatch_ind_ext
  (A B : Type) (lst : list (nat -> animation_result A -> animation_result B)) (fuel' : nat)
  (input' : animation_result A) {struct fuel'} : animation_result B :=
  match fuel' with
  | 0 => FuelError B
  | S remFuel' =>
      match lst with
      | [] => NoMatch B
      | h :: t =>
          let res := h remFuel' input' in
          match res with
          | @NoMatch _ => dispatch_ind_ext A B t remFuel' input'
          | _ => res
          end
      end
  end.

Fixpoint dispatch_coind_ext
  (A B : Type) (f : A -> B)
  (lst : list (nat -> animation_result A ->
    animation_result B)) (fuel' : nat)
  (input' : animation_result A) {struct fuel'} : animation_result B :=
  match fuel' with
  | 0 => map_outcome (A) (B) (f) (input')
  | S remFuel' =>
      match lst with
      | [] => NoMatch B
      | h :: t =>
          let res := h (S remFuel') input' in
          match res with
          | @NoMatch _ => dispatch_coind_ext A B f t remFuel' input'
          | @FuelError _ => map_outcome (A) (B) (f) (input')
          | _ => res
          end
      end
  end.

(** Quote the dispatch function for embedding in generated code. *)
MetaRocq Quote Definition dt := Eval compute in dispatch_ind_ext.
MetaRocq Run (dt' <- DB.un_de_bruijn dt ;; tmDefinition "dispatch_ext_tm'" dt').

MetaRocq Quote Definition dtCo := Eval compute in dispatch_coind_ext.
MetaRocq Run (dtCo' <- DB.un_de_bruijn dtCo ;; tmDefinition "dispatch_ext_tm_co_ind'" dtCo').

(** Extract the dispatch term for use in fixpoint generation. *)
Definition dispatch_ext_tm := hd sentinel_def_term (inspect_fix dispatch_ext_tm').
Definition dispatch_ext_tm_co_ind := hd sentinel_def_term (inspect_fix dispatch_ext_tm_co_ind').

(** Create all top-level animated inductive definitions with dispatch. *)
Definition mk_all_ind
  (inductData : (list fixpoint_entry))
  (kn : kername) (modes : mode_map)
  : list (def term) :=
mk_all_fixpoints mk_ind_fixpoint inductData kn modes ++ [dispatch_ext_tm].

(** Build all coinductive top-level definitions plus the coinductive dispatch term. *)
Definition mk_all_coind
  (inductData : (list fixpoint_entry))
  (kn : kername) (modes : mode_map)
  : list (def term) :=
mk_all_fixpoints mk_coind_fixpoint inductData kn modes ++ [dispatch_ext_tm_co_ind].

(** Annotate each inductive's clause list with the inductive names it calls,
    producing the [(inductive_data, recursive_calls)] structure used for
    building the mutual fixpoint. *)
Fixpoint mk_ind_data
  (data : list clause_data)
  (indNames : list string) :=
  match data with
  | [] => []
  | h :: t =>
      (h.(cd_ind_name), h.(cd_in_types), h.(cd_out_types),
       (ind_occurrences_named h.(cd_clauses) indNames))
      :: mk_ind_data t indNames
  end.

Unset Universe Checking.

(** Compile a constructor clause: classify premises, animate let-bindings and guard predicates,
    then assemble into a single executable term. *)
Definition compile_clause_body {A : Type}
  (ind : A) (kn : kername) (bigConj : term)
  (cstrNm : string)
  (inVars : list (prod string term))
  (outVars : list (prod string term))
  (modes : mode_map)
  (predTypeInf : pred_type_map)
  (allVarTpInf : list (string * term))
  (lhsPreds : list (string * term))
  (fuel : nat) : TemplateMonad term :=
(* Split the big conjunction into individual premises *)
let listAllConjs := collect_all_conjs bigConj in
(* Classify premises: guards check equality/predicates, lets bind outputs *)
gConjs' <- (get_sorted_guards modes listAllConjs [] [] [] (map fst inVars) fuel) ;;
(* Separate equality guards from predicate guards *)
gConjsEq <- tmEval all (filter_conjs_eq gConjs') ;;
(* Get the let-binding conjuncts (sorted by dependency order) *)
lConjs' <- (get_sorted_lets modes listAllConjs [] [] [] (map fst inVars) fuel) ;;
lc'' <- tmEval all lConjs' ;;
(* Attach output variable info, deduplicate, strip function-position vars *)
lConjs00 <- tmEval all
  (remove_dup_defs
    (attach_sorted_outputs lConjs'
      allVarTpInf modes predTypeInf)
    (map fst inVars)) ;;
lConjs <- tmEval all (map (fun lc => strip_fn_vars lc allVarTpInf) lConjs00) ;;
(* Collect predicate guard conjuncts from both guard and let sources *)
gConjsPred1 <- tmEval all
  (filter_conjs_pred'
    (attach_sorted_outputs gConjs'
      allVarTpInf modes predTypeInf));;
gConjsPred2 <- tmEval all
  ((keep_dup_defs
    (attach_sorted_outputs lConjs'
      allVarTpInf modes predTypeInf)
    (map fst inVars))) ;;
gConjsPred <- tmEval all (app gConjsPred1 gConjsPred2) ;;
(* Animate all let-bindings and guards into a single term *)
t <- animate_lets_and_guards ind kn lConjs
  gConjsEq gConjsPred inVars outVars
  (modes) (predTypeInf) (allVarTpInf)
  (lhsPreds) fuel ;;
(* Convert to de Bruijn, unquote, and register as a Rocq definition *)
t'' <- tmEval all  (typeConstrPatMatch.unwrap_option (DB.de_bruijn_option t)) ;;
f <- tmUnquote t'' ;;
tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false ((cstrNm ++ anim_suffix)) (Some hnf) ;;

tmReturn t''.

Set Universe Checking.

(** Quote the inductive at [kn] and extract clause data for all mode-specified
    constructors using [get_data]. *)
Definition get_data' (kn : kername)
  (modes : mode_map)
  : TemplateMonad (list clause_data) :=
mut <- tmQuoteInductive kn ;;

let lib := ind_bodies mut in
let nmCxt := gen_cxt lib in
let inOutTps := in_out_types modes lib in
get_data lib modes nmCxt inOutTps.

(** Extract [(name, type, constructors)] triples from inductive bodies. *)
Definition cstr_body_data
  (lo : list one_inductive_body)
  : list (string × term × list constructor_body) :=
map (fun (o : one_inductive_body) => ((ind_name o), ((ind_type o), (ind_ctors o)))) lo.

(** Convert a context declaration list to [(name, type)] pairs,
    dropping anonymous binders. *)
Fixpoint process_context (c : list context_decl) : list (string * term) :=
  match c with
  | [] => []
  | h :: t => match decl_name h with
             | {| binder_name := nNamed str;
                  binder_relevance := Relevant |} =>
                 (str, decl_type h) :: process_context t
             | _ =>  process_context t
            end
  end.

(** Process constructor data into [(inductive_name, type, [(cstr_name, arg_types)])] triples
    by converting each constructor's argument context. *)
Fixpoint cstr_type_data (inDat : list (string × term × list constructor_body)) : list type_env_entry :=
  match inDat with
  | [] => []
  | h :: t => match h with
            | (str, (tp, lst)) =>
                {| te_pred_name := str;
                   te_pred_type := tp;
                   te_cstr_vars := map (fun x =>
                     (cstr_name x,
                      process_context (cstr_args x)))
                     lst |}
                :: cstr_type_data t
            end
  end.

(** Extract full clause type information from a list of inductive bodies. *)
Definition clause_type_info (lo : list one_inductive_body) :=
cstr_type_data (cstr_body_data lo).

(** Extract the predicate-applications appearing as premises in a constructor clause. *)
Definition pred_occurrences (cstr : string * term) : list term :=
  match snd cstr with
  | tProd {| binder_name := nAnon;
             binder_relevance := Relevant |} t1 t2 =>
      filter_conjs_pred (collect_all_conjs t1)
  | _ => []
  end.
(** Remove duplicate strings from [l], accumulating unique elements in [l']. *)
Fixpoint dedup_strings (l : list string) (l' : list string) : list string :=
  match l with
  | [] => l'
  | h :: t => if in_strings h l' then dedup_strings t l' else dedup_strings t (h :: l')
  end.

(** Extract predicate names (possibly with duplicates) from a list of terms. *)
Fixpoint pred_names_aux (l : list term) : list string :=
  match l with
  | [] => []
  | (tApp (tInd {| inductive_mind := (path, indNm);
       inductive_ind := 0 |} []) lstArgs) :: rest =>
      indNm :: pred_names_aux rest
  | (tApp (tVar indNm) lstArgs) :: rest => indNm :: pred_names_aux rest
  | _ :: rest => pred_names_aux rest
  end.
(** Extract deduplicated predicate names from a list of terms. *)
Definition pred_names (l : list term) : list string :=
dedup_strings (pred_names_aux l) [].

(** Return [(constructor_name, predicate_names_called)] for one clause. *)
Definition cstr_pred_names (cstr : string * term) : string * list string :=
(fst cstr, pred_names (pred_occurrences cstr)).

(** Convert clause data to fixpoint-structure data by annotating each clause
    with the predicates it calls (for building the mutual recursive block). *)
Fixpoint fixpoint_data (data : list clause_data)
  : list (((string × list term) × list term)
          × list (string × list string)) :=
  match data with
  | [] => []
  | h :: t =>
      (((h.(cd_ind_name), h.(cd_in_types)), h.(cd_out_types)),
       (map cstr_pred_names h.(cd_clauses))) :: fixpoint_data t
  end.

(** Convert the input and output type lists in each inductive block to single
    product types, suitable for building the fixpoint signature. *)
Fixpoint prod_in_out
  (ls : list (((string × list term) × list term)
              × list (string × list string)))
  : ((list fixpoint_entry)) :=
  match ls with
  | [] => []
  | ((((p1,p2),p3), l4) :: rest) =>
      {| fe_ind_name := p1;
         fe_in_type := nested_prod_type p2;
         fe_out_type := nested_prod_type p3;
         fe_cstr_preds := l4 |}
      :: prod_in_out rest
  end.

(** Extract the premise (LHS) of a clause, or [true] if the clause has no premise. *)
Definition conj_lhs (c : ((string * string) * term)) : term :=
  match snd c with
  | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2 => t1
  | _ => <%true%>
  end.

(** Return the variable name at position [n] in [vArgs], or [[]] if absent. *)
Fixpoint var_names_at (n : nat) (vArgs : list term) : list string :=
  match vArgs with
  | [] => []
  | tVar str :: rest => match n with
                      | 0 => [str]
                      | S m => var_names_at m rest
                      end
  | _ :: rest =>        match n with
                      | 0 => []
                      | S m => var_names_at m rest
                      end
  end.

(** Collect variable names at a list of positions [l] from [vArgs]. *)
Fixpoint var_names (l : list nat) (vArgs : list term) : list string :=
  match l with
  | [] => []
  | h :: rest => var_names_at h vArgs ++ var_names rest vArgs
  end.

(** Extract variable names from a clause's conclusion according to the positions
    selected by [proj] (either [fst] for inputs or [snd] for outputs) in the mode list. *)
Fixpoint conj_vars_projected
  (proj : list nat * list nat -> list nat)
  (c : ((string * string) * term))
  (modes : mode_map) : list string :=
  match modes with
  | [] => []
  | h :: rest =>
      if String.eqb (fst h) (fst (fst c))
      then match snd c with
        | tProd {| binder_name := nAnon;
                   binder_relevance := Relevant |}
            t1 (tApp (tVar str) lstVar) =>
            var_names (proj (snd h)) lstVar
        | _ => []
        end
      else conj_vars_projected proj c rest
  end.

(** Names of the input variables of a clause according to the mode. *)
Definition conj_in_vars := conj_vars_projected fst.
(** Names of the output variables of a clause according to the mode. *)
Definition conj_out_vars := conj_vars_projected snd.

(** Look up all variable type bindings for the constructor [snd (fst c)] in [tpData]. *)
Fixpoint all_var_types_raw
  (c : ((string * string) * term))
  (tpData : list (string × list (string × term)))
  : list (string * term) :=
  match tpData with
  | [] => []
  | h :: rest =>
      if String.eqb (snd (fst c)) (fst h)
      then snd h
      else all_var_types_raw c rest
  end.

(** Retrieve all variable type bindings for a clause from the full type environment. *)
Definition all_var_types (c : ((string * string) * term)) (tpData : list type_env_entry) :=
all_var_types_raw c (concat (map (fun h => h.(te_cstr_vars)) tpData)).

(** Build a flat list of [(inductive_name, all_argument_types)] for every inductive,
    concatenating input and output types in order. *)
Definition all_ind_tp_data (data : list clause_data) : list (string * list term) :=
map (fun x =>
  (x.(cd_ind_name),
   app x.(cd_in_types) x.(cd_out_types))) data.

(** Compute the type of the animated top-level function for one inductive:
    [nat -> animation_result inputTp -> animation_result outputTp]. *)
Definition animation_type_one (data :  clause_data) :  (string * term) :=
(data.(cd_ind_name),
 (tProd {| binder_name := nAnon;
           binder_relevance := Relevant |}
   <%nat%>
   (tProd {| binder_name := nAnon;
             binder_relevance := Relevant |}
     (tApp <%animation_result%>
       [nested_prod_type data.(cd_in_types)])
     (tApp <%animation_result%>
       [nested_prod_type data.(cd_out_types)])))).

(** Compute animation types for all inductives in [data]. *)
Definition animation_types (data :  list clause_data) :  list (string * term) :=
map animation_type_one data.

(** Return the first [(k, v)] pair in [l'] with key [l], or [[]] if absent. *)
Fixpoint filter_by_name {A : Type} (l : string) (l' : list (string * A)) : list (string * A) :=
  match l' with
  | [] => []
  | h :: rest => if String.eqb l (fst h) then [h] else filter_by_name l rest
  end.

(** Retrieve all entries from [l'] whose keys appear in [l]. *)
Fixpoint filter_by_names {A : Type}
  (l : list string) (l' : list (string * A))
  : list (string * A) :=
  match l with
  | [] => []
  | h :: rest => filter_by_name h l' ++ filter_by_names rest l'
  end.

(** Look up the animation types of all predicates called by constructor [snd (fst c)]. *)
Fixpoint pred_animation_types_aux
  (c : ((string * string) * term))
  (fixptInf' : list (string × list string))
  (anTp : list (string * term))
  : list (string * term) :=
  match fixptInf' with
  | [] => []
  | h :: rest =>
      if String.eqb (snd (fst c)) (fst h)
      then (filter_by_names (snd h) anTp)
      else pred_animation_types_aux c rest anTp
  end.

(** Retrieve animation types for all predicates called by clause [c]. *)
Definition pred_animation_types (c : ((string * string) * term)) (fixptInf : list fixpoint_entry)
                        (anTp : list (string * term))  : list (string * term) :=

pred_animation_types_aux c (concat (map (fun h => h.(fe_cstr_preds)) fixptInf)) anTp.

(** Filter [listallVTp] to only include entries whose names are in [lstVar]. *)
Definition lookup_var_types (lstVar : list string)
  (listallVTp : list (string * term))
  : list (string * term) :=
filter_by_names lstVar listallVTp.

(** Tag each [(cstr_name, clause)] pair with its parent inductive name. *)
Fixpoint clauses_of_ind (indNm : string)
  (cstrs : list (string * term))
  : list ((string * string) * term) :=
  match cstrs with
  | [] => []
  | (str, t) :: rest => ((indNm, str), t) :: clauses_of_ind indNm rest
  end.

(** Convert a single inductive's data block to a tagged clause list. *)
Definition clauses_of_data (dataOne :   clause_data)
                         : list ((string * string) * term):=
clauses_of_ind dataOne.(cd_ind_name) dataOne.(cd_clauses).

(** Flatten all inductive data blocks into a single tagged clause list. *)
Definition all_clauses (data :   list clause_data) : list ((string * string) * term):=
concat (map clauses_of_data data).

(** Internal corecursive worker: produces [f n0 inp, f (n0+1) inp, …]. *)
CoFixpoint make_stream (A : Type) (B : Type)
  (f : nat -> A -> B) (n0 : nat) (inp : A)
  : Streams.Stream B :=
  Streams.Cons (f n0 inp) (make_stream A B f (S n0) inp).

(** Build an infinite [Streams.Stream] of results by applying [f] to [inp] with
    increasing fuel values starting from 0. *)
Definition stream_of_fn (A : Type) (B : Type) (f : nat -> A -> B) (inp : A) : Streams.Stream B :=
  make_stream A B f 0 inp.

(** Find an inductive by name in [inductData] and return [proj h] for its record,
    failing with [errMsg] if not found. *)
Fixpoint search_type_by_proj (proj : fixpoint_entry -> term)
  (inductData : list fixpoint_entry) (nm : string) (errMsg : string) : TemplateMonad term :=
match inductData with
 | [] => tmFail errMsg
 | h :: t =>
     if String.eqb h.(fe_ind_name) nm
     then tmReturn (proj h)
     else search_type_by_proj proj t nm errMsg
end.

(** Find the input type of a named inductive in the data. *)
Definition search_in_tp := search_type_by_proj (fun h => h.(fe_in_type)).
(** Find the output type of a named inductive in the data. *)
Definition search_out_tp := search_type_by_proj (fun h => h.(fe_out_type)).

Unset Universe Checking.

(** Compile a single clause [oneClause] of inductive [kn]: extract type and
    clause data, rewrite non-variable arguments, then call
    [compile_clause_body] to produce the compiled term. *)
Definition animate_one_clause {A : Type}
  (ind : A) (kn : kername)
  (oneClause : ((string * string) * term))
  (modes : mode_map) (fuel : nat)
  : TemplateMonad term :=
(* Step 1: gather clause data and type info from the inductive definition *)
allClauseData' <- get_data' kn modes ;;
mut <- tmQuoteInductive kn ;;
allTpData' <- tmEval all (clause_type_info (ind_bodies mut)) ;;
(* Step 2: rewrite clauses to normalize non-variable arguments *)
allClauseData <- tmEval all (rewrite_cl_all allClauseData' allTpData') ;;
allTpData <- tmEval all (finalize_type_info allClauseData' allTpData') ;;
cstrNm  <- tmEval all (snd (fst oneClause)) ;;
(* Step 3: compute fixpoint metadata and clause LHS *)
fixptData <- tmEval all (prod_in_out (fixpoint_data allClauseData)) ;;
conjlhs <- tmEval all (conj_lhs oneClause) ;;
(* Step 4: resolve variable types and partition into input/output *)
allVarTp <- tmEval all (all_var_types oneClause allTpData) ;;
inV <- tmEval all
  (lookup_var_types
    (conj_in_vars oneClause modes) (allVarTp)) ;;
outV <- tmEval all
  (lookup_var_types
    (conj_out_vars oneClause modes) (allVarTp));;
(* Step 5: gather predicate type info for recursive calls *)
predTps <- tmEval all (all_ind_tp_data allClauseData) ;;
predTpsAn <- tmEval all (animation_types allClauseData) ;;
predTpsOccAn <- tmEval all
  (pred_animation_types oneClause
    fixptData predTpsAn) ;;
(* Step 6: compile the clause body with all gathered info *)
(compile_clause_body ind kn conjlhs cstrNm inV outV modes predTps allVarTp predTpsOccAn fuel).

(** Compile every clause in [clLst] sequentially, collecting compiled terms. *)
Fixpoint animate_clause_list {A : Type}
  (ind : A) (kn : kername)
  (clLst : list ((string * string) * term))
  (modes : mode_map) (fuel : nat)
  : TemplateMonad (list term) :=

  match clLst with
  | [] => tmReturn []
  | c1 :: cRest =>
      c1An <- animate_one_clause ind kn c1 modes fuel ;;
      cRestAn <- animate_clause_list ind kn cRest modes fuel ;;
      tmReturn (c1An :: cRestAn)
  end.

(** Main entry point: animate an inductive relation into an executable function.
    Generates a fixpoint that tries each clause with bounded fuel. *)
Definition animate_inductive {A : Type}
  (ind : A) (kn : kername)
  (modes : mode_map) (fuel : nat)
  : TemplateMonad (list term) :=
(* Phase 1: extract clause structure and type info *)
allClauseData' <- get_data' kn modes ;;
mut <- tmQuoteInductive kn ;;
allTpData' <- tmEval all (clause_type_info (ind_bodies mut)) ;;
allClauseData <- tmEval all (rewrite_cl_all allClauseData' allTpData') ;;
allTpData <- tmEval all (finalize_type_info allClauseData' allTpData') ;;
(* Phase 2: compile each clause into a match-and-return term *)
clLst <- tmEval all (all_clauses allClauseData) ;;
tms <- animate_clause_list ind kn clLst modes fuel ;;
(* Phase 3: assemble the fixpoint that dispatches over compiled clauses *)
inductData <- tmEval all (prod_in_out (fixpoint_data allClauseData)) ;;
let u := (mk_rec_fn (mk_all_ind (inductData) kn modes) 0)  in
          u' <- tmEval all u ;;
          (* Convert named vars to de Bruijn, unquote, and register the definition *)
          t' <- tmEval all (typeConstrPatMatch.unwrap_option (DB.de_bruijn_option u)) ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false
                (((snd kn) ++ top_fn_suffix))
                (Some hnf) ;;
              tmReturn tms.

(** Main entry point: animate a coinductive relation into an executable corecursive stream.
    Generates both a fixpoint and a [Stream] for lazy enumeration. *)
Definition animate_coinductive {A : Type}
  (ind : A) (kn : kername)
  (modes : mode_map) (fuel : nat)
  : TemplateMonad (list term) :=
allClauseData' <- get_data' kn modes ;;
mut <- tmQuoteInductive kn ;;
allTpData' <- tmEval all (clause_type_info (ind_bodies mut)) ;;
allClauseData <- tmEval all (rewrite_cl_all allClauseData' allTpData') ;;
allTpData <- tmEval all (finalize_type_info allClauseData' allTpData') ;;

let clLst := all_clauses allClauseData in

tms <- animate_clause_list ind kn clLst modes fuel ;;

let inductData := prod_in_out (fixpoint_data allClauseData) in

let u := (mk_rec_fn (mk_all_coind (inductData) kn modes) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (typeConstrPatMatch.unwrap_option (DB.de_bruijn_option u)) ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (((snd kn) ++ top_fn_suffix)) (Some hnf) ;;
              fnInTp <- search_in_tp inductData (snd kn) "cannot find input type" ;;
              fnOutTp <- search_out_tp inductData (snd kn) "cannot find output type" ;;
              let tCoInd :=
                tApp <%stream_of_fn%>
                  [(tApp <%animation_result%> [fnInTp]);
                   (tApp <%animation_result%> [fnOutTp]);
                   t'] in
              tCoInd'' <- tmEval all tCoInd ;;
              fStm <- tmUnquote tCoInd'' ;;

              tmEval hnf (my_projT2 fStm) >>=
              tmDefinitionRed_ false (((snd kn) ++ stream_suffix)) (Some hnf) ;;

              tmReturn tms.

(** Compile all clauses for a list of mutually recursive inductives [knLst],
    returning the combined fixpoint structure data. *)
Fixpoint animate_multi_def {A : Type} (ind : A) (knLst : list kername)
 (modes : mode_map) (fuel : nat) : TemplateMonad ((list fixpoint_entry)) :=

match knLst with
| [] => tmReturn []
| kn :: t => allClauseData' <- get_data' kn modes ;;
             mut <- tmQuoteInductive kn ;;
             allTpData' <- tmEval all (clause_type_info (ind_bodies mut)) ;;
             allClauseData <- tmEval all (rewrite_cl_all allClauseData' allTpData') ;;
             allTpData <- tmEval all (finalize_type_info allClauseData' allTpData') ;;

             clLst <- tmEval all (all_clauses allClauseData) ;;

             animate_clause_list ind kn clLst modes fuel ;;

             inductData <- tmEval all (prod_in_out (fixpoint_data allClauseData)) ;;
             restDefs <- animate_multi_def ind t (modes) (fuel) ;;
             tmReturn (app inductData restDefs)

end.

(** Compile all clauses across a multi-definition mutual block ([topKn :: knLst]),
    assemble a single mutual fixpoint, and define it as [topKn.AnimatedTopFn]. *)
Definition animate_multi_aux {A : Type} (topInd : A) (topKn : kername) (knLst : list kername)
 (modes : mode_map) (fuel : nat) : TemplateMonad term:=

inductData'' <- animate_multi_def (topInd) (topKn :: knLst) (modes) (fuel);;
inductData <- tmEval all inductData'';;

let u := (mk_rec_fn (mk_all_ind (inductData) topKn modes) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (typeConstrPatMatch.unwrap_option (DB.de_bruijn_option u)) ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false
                (((snd topKn) ++ top_fn_suffix))
                (Some hnf) ;;
              tmReturn u'.

Set Universe Checking.
