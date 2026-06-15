(** * AnimationEngine — Main Animation Pipeline

    Top-level entry points [animateInductive] and [animateCoinductive] that
    orchestrate the full animation pipeline: clause data extraction, term
    rewriting, clause-by-clause compilation via [compileLetBindingsAndGuards],
    and final fixpoint assembly into a quoted Rocq definition.

    Depends on: [MetaRocqUtils], [PatternCompilation], [EqualityResolution],
    [AnimationDispatch]. *)

Require Import Animation.AnimationDispatch.

Require Import Animation.EqualityResolution.

Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.

Require Import List.
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
Fixpoint removeVarFromFnPosition (conjRHS : term)  (allVarTpInf : list (string * term)) :=
  match conjRHS with
  | tApp (tVar str) lstArgs =>                            match look_up_vars_one str allVarTpInf with
                                                         | [h] => tApp <%id_fn%> ((snd h) :: (tVar str) :: (map (fun arg => removeVarFromFnPosition arg allVarTpInf) lstArgs))
                                                         | _ => tApp (tVar str) (map (fun arg => removeVarFromFnPosition arg allVarTpInf) lstArgs)
                                                        end
  | tApp fn lstArgs => tApp (removeVarFromFnPosition fn allVarTpInf) (map (fun arg => removeVarFromFnPosition arg allVarTpInf) lstArgs)
  | _ => conjRHS
  end.

(** Apply [removeVarFromFnPosition] to the RHS of an equality conjunct,
    leaving non-equality conjuncts unchanged. *)
Definition remove_var_fm_fn_pos (conjunct' : (term * (string * term))) (allVarTpInf : list (string * term)) :=
  match fst conjunct' with
  | tApp <%eq%> [typeVar; t1; t2] => let newConj := tApp <%eq%> [typeVar; t1; removeVarFromFnPosition t2 allVarTpInf] in (newConj, (snd conjunct'))
  | _ => conjunct'
  end.

(** Functor map over [animation_result]: applies [f] to a [Success] value and
    propagates [FuelError] and [NoMatch] unchanged. *)
Definition map_outcome_poly (A : Type) (B : Type) (f : A -> B) (a : animation_result A) : animation_result B :=
  match a with
  | FuelError  => FuelError B
  | Success a' => Success B (f a')
  | NoMatch => NoMatch B
  end.

(** Extract inductive names from bodies. *)
Definition get_ind_names (l : list one_inductive_body) :=
map (fun o => ind_name o) l.

(** Generate context from inductive names. *)
Definition gen_cxt (l : list one_inductive_body) :=
(map (fun s => nNamed s) (rev (get_ind_names l))).

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
Definition get_in_tp (inMode : list nat) (o : one_inductive_body) : list term  :=
 let lstType := get_type (ind_type o) in
  (get_type' inMode lstType).

(** Strip all top-level foralls/products from a term to get to the body. *)
Fixpoint reduce_clause_tm (t : term) :=
  match t with
  | (tPro str typ t') => reduce_clause_tm t'
  | t'' => t''
  end.

(** Extract preconditions (hypotheses) from a constructor clause. *)
Definition get_pre_cons (t : term) :=
  match t with
  | (tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2) => [t1]
  | _ => []
  end.

(** Process preconditions, splitting conjunctions. *)
Definition process_pre_con (l : list term) :=
  match l with
  | [] => []
  | [tApp <%and%> l'] => l'
  | [t'] => [t']
  | _ :: (h' :: _) => []
  end.

(** Get the body (recursive premises) of a constructor clause. *)
Definition get_cl_body' (t : term) : list term :=
process_pre_con (get_pre_cons (reduce_clause_tm t)).

(** Get the head (conclusion) of a constructor clause. *)
Definition get_cl_head' (t : term) : term :=
  match reduce_clause_tm t with
  | (tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2) => t2
  | t' => t'
  end.

(** Extract body from a constructor. *)
Definition get_cl_body (c : constructor_body) : list term :=
 get_cl_body' (cstr_type c).

(** Extract head from a constructor. *)
Definition get_cl_head (c : constructor_body) :  term :=
 get_cl_head' (cstr_type c).

(** Check if a string is in a list of strings. *)
Fixpoint memberOfStringList (s : string) (l1 : list string) : bool :=
  match l1 with
  | [] => false
  | h :: t => if String.eqb s h then true else memberOfStringList s t
  end.

(** Extract names of inductive predicates applied in a list of terms. *)
Fixpoint get_ind_app (l : list term) (indNames : list string) : list string :=
  match l with
  | [] => []
  | h :: t => match h with
              | tApp (tVar str) args => if (memberOfStringList str indNames) then (str :: (get_ind_app t indNames)) else (get_ind_app t indNames)
              | _ => (get_ind_app t indNames)
              end
  end.

(** Annotate each clause with the inductive predicate names it applies. *)
Fixpoint get_ind_app' (l : list (string * term)) (indNames : list string) : list (string * (list string)) :=
  match l with
  | [] => []
  | h :: t => (fst h, get_ind_app (get_cl_body' (snd h)) indNames) :: get_ind_app' t indNames
  end.

(** Get input/output types for all inductives according to mode specifications. *)
Fixpoint get_in_out_tps_one (mode : (string * ((list nat) * (list nat)))) (b : list one_inductive_body) : list ((string * list term) * list term) :=
  match b with
    | h' :: t' => if String.eqb (fst mode) (ind_name h') then  [(ind_name h', get_in_tp (fst (snd mode)) h', get_in_tp (snd (snd mode)) h')] else get_in_out_tps_one mode t'
    | _ => []
    end.

(** Get input/output types for all inductives in the mode list. *)
Fixpoint get_in_out_tps (modes : list (string * ((list nat) * (list nat)))) (b : list one_inductive_body) : list ((string * list term) * list term) :=
  match modes with
  | [] => []
  | h :: t => app (get_in_out_tps_one h b) (get_in_out_tps t b)
  end.

(** Convert constructor bodies to named terms by unquoting from de Bruijn into
    the named context [l], returning [(constructor_name, clause_term)] pairs. *)
Fixpoint mk_nm_tm (c : list constructor_body) (l : list name) :TemplateMonad (list (string * term)) :=
  match c with
  | [] => tmReturn []
  | (h :: t) => r <- DB.undeBruijn' l ((cstr_type h )) ;; r' <- tmEval all r ;; let hres := (cstr_name h, (reduce_clause_tm r')) in rest <- mk_nm_tm t l ;; tmReturn (hres :: rest)
  end.

(** Retrieve clause data for all inductives in [lib]: for each body, convert
    constructors to named terms and pair them with their input/output type info. *)
Fixpoint get_data (lib : list one_inductive_body) (ln : list (string * ((list nat) * (list nat)))) (nmCxt : list name) (inOutTps : list ((string * list term) * list term)) : TemplateMonad (list (((string * list term) * list term) * (list (string * term))))  :=

  match lib with
  | [] => tmReturn []
  | h' :: t' => match inOutTps with
                 | h :: t => dbth <- mk_nm_tm (ind_ctors h') nmCxt ;; rest <- get_data t' (ln) nmCxt (tl inOutTps) ;; tmReturn ((h, dbth) :: rest)
                 | _ => tmReturn []
                 end

  end.

(** Replace non-variable subterms in [l] with fresh variables (prefixed by
    [varPfix]), emitting equality constraints to bind the originals.
    Returns triples [(replacement_vars, equality_constraints, new_var_bindings)]. *)
Fixpoint substitutePatternVariables (l : list term) (varPfix : string) (n : nat) (argTps : list term) : list ((list term * list term) * list (string * term)) :=
  match l with
  | [] => []
  | (tVar str) :: rest => (([(tVar str)], []), []) :: (substitutePatternVariables rest varPfix n (tl argTps))
  | t' :: rest =>
      (([(tVar (String.append varPfix (string_of_nat n)))], [tApp <%eq%> [(hd <%bool%> argTps) ; (tVar (String.append varPfix (string_of_nat n))); t']]) , ([(String.append varPfix (string_of_nat n),(hd <%bool%> argTps))]))  :: (substitutePatternVariables rest varPfix (S n) (tl argTps))

  end.
(** Look up the argument types for predicate named [s] in the type environment. *)
Fixpoint find_tp (s : string) (allPredArgTps : list (string * (list term))) : list term :=
  match allPredArgTps with
  | [] => []
  | h :: t => if String.eqb s (fst h) then snd h else find_tp s t
  end.

(** For each conjunct in [l], replace non-variable arguments of predicates with
    fresh variables and collect the resulting equality side-conditions and
    new variable bindings.  Equality conjuncts are passed through unchanged. *)
Fixpoint resolveConjunctionInputs (l : list term) (varPfix : string) (n : nat) (allPredArgTps : list (string * (list term))) :  list ((term * list term) * list (string * term)) :=
  match l with
  | [] => []
  | (tApp <%eq%> lstArgs) :: rest => (((tApp <%eq%> lstArgs) , []), []) :: resolveConjunctionInputs (rest) (varPfix) (n) (allPredArgTps)
  | (tApp (tVar str) lstArgs) :: rest =>  let result := substitutePatternVariables lstArgs varPfix n (find_tp str allPredArgTps) in ((((tApp (tVar str) (concat (map (fun y => fst (fst y)) result)))), (concat (map (fun y => snd (fst y)) result))), (concat (map snd result))) :: resolveConjunctionInputs (rest) (varPfix) ((length lstArgs) + (S n)) (allPredArgTps)
  | (tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) lstArgs) :: rest =>
     let result := substitutePatternVariables lstArgs varPfix n (find_tp indNm allPredArgTps) in ((((tApp (tInd {| inductive_mind := (_path, indNm); inductive_ind := 0 |} []) (concat (map (fun y => fst (fst y)) result)))), (concat (map (fun y => snd (fst y)) result))), (concat (map snd result))) :: resolveConjunctionInputs (rest) (varPfix) ((length lstArgs) + (S n)) (allPredArgTps)

  | t'' :: rest => ((t'', []), []) :: resolveConjunctionInputs (rest) (varPfix) (n) (allPredArgTps)

  end.

(** Collect variable and inductive names from a term, with arguments listed
    before the function (used for computing fresh-variable prefix lengths). *)
Fixpoint extract_ordered_vars2 (t : term) : list string :=
  match t with
  | tVar str  => [str]
  | (tInd {| inductive_mind := (_path, str); inductive_ind := k |} []) => [str]
  | tApp fn lst => app (concat (map extract_ordered_vars2 lst)) (extract_ordered_vars2 fn)

  | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2 => app (extract_ordered_vars2 t1) (extract_ordered_vars2 t2)
  | _ => []
  end.

(** Build a fresh variable prefix of length [n+1] using the letter "j".
    Used to guarantee freshness: choose [n] larger than the longest existing name. *)
Fixpoint mk_fresh_v_prefix (n : nat) : string :=
  match n with
  | 0 => "j"
  | S m => String.append "j" (mk_fresh_v_prefix m)
  end.

(** Extract the [(name, type)] pairs for every inductive predicate. *)
Definition find_pred_tps' (allTpInf : list ((string × term) × list (string × list (string × term)))) :=
map fst allTpInf.

(** Build a [(name, arg_types)] environment for all inductive predicates by
    destructuring each predicate's type into its argument list. *)
Definition find_pred_tps (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * list term) :=
map (fun y => (fst y , get_type (snd y))) (find_pred_tps' allTpInf).
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
  | tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tApp <%and%> lst) t' => app ((flatten_and (tApp <%and%> lst))) [t']
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
Definition rewrite_cl (t : term) (allTpInf : list ((string × term) × list (string × list (string × term)))) : term :=
let prefix := mk_fresh_v_prefix (S (list_max (map String.length (extract_ordered_vars2 t)))) in
let lstTm := flatten_clause t in
let allPredArgTp := find_pred_tps allTpInf in
let resolved := resolveConjunctionInputs lstTm prefix 0 allPredArgTp in
build_clause (app (concat (map (fun y => (snd (fst y))) resolved)) (map (fun y => (fst (fst y))) resolved)).

(** Collect the new variable-type bindings introduced by rewriting clause [t]. *)
Definition get_extra_tp_inf (t : term) (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * term) :=

let prefix := mk_fresh_v_prefix (S (list_max (map String.length (extract_ordered_vars2 t)))) in
let lstTm := flatten_clause t in
let allPredArgTp := find_pred_tps allTpInf in
(concat (map (fun y => (snd (y))) (resolveConjunctionInputs lstTm prefix 0 allPredArgTp))).

(** Rewrite all clause terms in a flat [(constructor_name, clause)] list. *)
Fixpoint rewrite_cl_all1 (allClauseData1 : list (string × term)) (allTpInf : list ((string × term) × list (string × list (string × term)))) : (list (string × term)) :=
  match allClauseData1 with
  | [] => []
  | (cstrNm,t) :: rest => (cstrNm, rewrite_cl t allTpInf) :: (rewrite_cl_all1 rest allTpInf)
  end.

(** Rewrite the clause data block for a single inductive. *)
Definition rewrite_cl_all1' (allClauseData1 : (((string × list term) × list term) × list (string × term))) (allTpInf : list ((string × term) × list (string × list (string × term)))) :  (((string × list term) × list term) × list (string × term)) :=
  match allClauseData1 with
  | (((indNm, inTps), outTps), cstrData) => (((indNm, inTps), outTps), (rewrite_cl_all1 cstrData allTpInf))
  end.

(** Rewrite all clause data blocks across all inductives. *)
Definition rewrite_cl_all (allClauseData : list (((string × list term) × list term) × list (string × term))) (allTpInf : list ((string × term) × list (string × list (string × term)))) :  list (((string × list term) × list term) × list (string × term)) :=
map (fun y => rewrite_cl_all1' y allTpInf) allClauseData.

(** Collect new variable-type bindings for each clause in a flat clause list. *)
Fixpoint get_extra_tp_inf_lst (allClauseData1 : list (string × term)) (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * list (string * term)) :=
  match allClauseData1 with
  | [] => []
  | (cstrNm, t) :: rest => (cstrNm, get_extra_tp_inf t allTpInf) :: get_extra_tp_inf_lst rest allTpInf
  end.

(** Collect new variable-type bindings for every inductive's clause data. *)
Fixpoint get_extra_tp_inf_lst_all (allClauseData : list (((string × list term) × list term) × list (string × term))) (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * (list (string * list (string * term)))) :=
  match allClauseData with
  | [] => []
  | (((indNm, inTps), outTps), listCons) :: rest => (indNm, get_extra_tp_inf_lst listCons allTpInf) :: (get_extra_tp_inf_lst_all rest allTpInf)
  end.

(** Look up [cstrNm] in an association list of constructor-name → type bindings. *)
Fixpoint retrieve (cstrNm : string) (l : list (string × list (string × term))) : list (string * term) :=
  match l with
  | [] => []
  | h :: rest => if (String.eqb cstrNm (fst h)) then (snd h) else retrieve cstrNm rest
  end.

(** Retrieve the original type bindings for constructor [cstrNm] of [indNm]. *)
Fixpoint get_old_tp_inf (indNm : string) (cstrNm : string) (allTpInf : list ((string × term) × list (string × list (string × term)))) : list (string * term) :=
  match allTpInf with
  | [] => []
  | (str, t, lst) :: rest => if (String.eqb indNm str) then retrieve cstrNm lst else get_old_tp_inf indNm cstrNm rest
  end.

(** Retrieve the newly-introduced (fresh-variable) type bindings for
    constructor [cstrNm] of [indNm] after clause rewriting. *)
Fixpoint get_new_tp_inf (indNm : string) (cstrNm : string) (extraTpInf : list ((string) × list (string × list (string × term)))) : list (string * term) :=
  match extraTpInf with
  | [] => []
  | (str, lst) :: rest => if (String.eqb indNm str) then retrieve cstrNm lst else get_new_tp_inf indNm cstrNm rest
  end.
(** Merge original and fresh-variable type bindings for one inductive block. *)
Definition update_tp_inf (allTpInf1 :  ((string × term) × list (string × list (string × term)))) (allTpInf :  list((string × term) × list (string × list (string × term)))) (extraTpInf : list ((string) × list (string × list (string × term)))) :=
  match allTpInf1 with

  | ((indNm, t), lst) => ((indNm, t), map (fun y => ((fst y), app (get_old_tp_inf indNm (fst y) allTpInf) (get_new_tp_inf indNm (fst y) extraTpInf))) lst)
  end.

(** Apply [update_tp_inf] to every inductive block in [allTpInf1l]. *)
Definition update_tp_inf_lst (allTpInf1l :  list ((string × term) × list (string × list (string × term)))) (allTpInf :  list((string × term) × list (string × list (string × term)))) (extraTpInf : list ((string) × list (string × list (string × term)))) :=
map (fun y => update_tp_inf y allTpInf extraTpInf) allTpInf1l.

(** Self-update: merge each inductive block's extra type info into itself. *)
Definition update_tp_inf_final' (allTpInf :  list ((string × term) × list (string × list (string × term)))) (extraTpInf : list ((string) × list (string × list (string × term)))) :=
update_tp_inf_lst allTpInf allTpInf extraTpInf.

(** Compute the final, fully-merged type environment after clause rewriting:
    derives extra bindings from [allClauseData] and folds them into [allTpInf]. *)
Definition update_tp_inf_final (allClauseData : list (((string × list term) × list term) × list (string × term))) (allTpInf : list ((string × term) × list (string × list (string × term)))) : (list ((string × term) × list (string × list (string × term)))) :=
update_tp_inf_final' allTpInf  (get_extra_tp_inf_lst_all allClauseData allTpInf).

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
                                   | [] => (quote_const' kn (String.append postConCons animatedSuffix)) :: apply_top_fn kn t
                                   | l => tApp (quote_const' kn (String.append postConCons animatedSuffix)) (map (fun nm => (tVar (String.append nm animatedTopFnSuffix))) l) :: apply_top_fn kn t
                                   end
  end.

(** Return the input-position indices for [indNm] in the mode list, or [[]]
    if [indNm] has no explicit input positions (empty-input mode). *)
Fixpoint get_mode_in (indNm : string) (modes : list (string * ((list nat) * (list nat)))) :=
  match modes with
  | [] => []
  | (h :: rest) => if String.eqb indNm (fst h) then fst (snd h) else get_mode_in indNm rest
  end.
(** Shared base for building one fixpoint definition for a top-level animated inductive.
    Parameterized by the zero-fuel branch, dispatch construction, and whether input is explicit. *)
Definition mk_one_ind_top_base (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername)
  (zeroBranch : term) (mkDispatchBody : term -> term)
  (hasInput : bool) : def term :=
let fnListTp := tProd {| binder_name := nAnon; binder_relevance := Relevant |}
      <%nat%> (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
     (tApp <%animation_result%> [inputType]) (tApp <%animation_result%> [outputType])) in
let listTm := mk_lst_tm' (apply_top_fn kn clauseData) fnListTp in
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
{| dname := {| binder_name := nNamed (String.append indNm animatedTopFnSuffix);
               binder_relevance := Relevant |};
   dtype := tp; dbody := body; rarg := 0 |}.

(** Build a top-level fixpoint definition for an inductive with explicit input. *)
Definition mk_one_ind_top' (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername) : def term :=
mk_one_ind_top_base indNm inputType outputType clauseData kn
  (tApp <%FuelError%> [outputType])
  (fun listTm => tApp (tVar "dispatch_outcome_poly_ext")
     [inputType; outputType; listTm; tVar "remFuel"; tVar "input"])
  true.

(** Build a top-level fixpoint definition for an inductive with no input
    (empty-input mode: the argument is always [Success bool true]). *)
Definition mk_one_ind_top_empty_in' (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername) : def term :=
mk_one_ind_top_base indNm inputType outputType clauseData kn
  (tApp <%FuelError%> [outputType])
  (fun listTm => tApp (tVar "dispatch_outcome_poly_ext")
     [inputType; outputType; listTm; tVar "remFuel"; tVar "input"])
  false.

(** Build a top-level fixpoint definition for a coinductive with explicit input,
    using [map_outcome_poly Rest] as the zero-fuel branch. *)
Definition mk_one_ind_top_co_ind' (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername) : def term :=
let restFn := quote_const' kn (String.append indNm "Rest") in
mk_one_ind_top_base indNm inputType outputType clauseData kn
  (tApp <%map_outcome_poly%> [inputType; outputType; restFn; tVar "input"])
  (fun listTm => tApp (tVar "dispatch_outcome_poly_ext_co_ind")
     [inputType; outputType; restFn; listTm; tVar "remFuel"; tVar "input"])
  true.

(** Build a top-level fixpoint definition for a coinductive with no input,
    using [map_outcome_poly Rest] as the zero-fuel branch. *)
Definition mk_one_ind_top_co_ind_empty_in' (indNm : string) (inputType outputType : term)
  (clauseData : list (string * (list string))) (kn : kername) : def term :=
let restFn := quote_const' kn (String.append indNm "Rest") in
mk_one_ind_top_base indNm inputType outputType clauseData kn
  (tApp <%map_outcome_poly%> [inputType; outputType; restFn; tVar "input"])
  (fun listTm => tApp (tVar "dispatch_outcome_poly_ext_co_ind")
     [inputType; outputType; restFn; listTm; tVar "remFuel"; tVar "input"])
  false.

(** Dispatch to [mk_one_ind_top'] or [mk_one_ind_top_empty_in'] based on the mode for [indNm]. *)
Definition mk_one_ind_top (indNm : string) (inputType : term) (outputType : term) (clauseData : list (string * (list string))) (kn : kername) (modes : list (string * ((list nat) * (list nat))))  : def term :=
  match get_mode_in indNm modes with
  | [] => mk_one_ind_top_empty_in' indNm inputType outputType clauseData kn
  | _ => mk_one_ind_top' indNm inputType outputType clauseData kn
  end.

(** Dispatch to [mk_one_ind_top_co_ind'] or [mk_one_ind_top_co_ind_empty_in'] based on mode. *)
Definition mk_one_ind_top_co_ind (indNm : string) (inputType : term) (outputType : term) (clauseData : list (string * (list string))) (kn : kername) (modes : list (string * ((list nat) * (list nat))))  : def term :=
  match get_mode_in indNm modes with
  | [] => mk_one_ind_top_co_ind_empty_in' indNm inputType outputType clauseData kn
  | _ => mk_one_ind_top_co_ind' indNm inputType outputType clauseData kn
  end.

(** Construct a fixpoint term from a list of definitions. *)
Definition mk_rec_fn (ls : list (def term)) (j : nat) : term :=
 tFix ls j.

(** Apply [mkOneFn] to every inductive in [inductData], building the full list
    of fixpoint definitions for the mutual recursive block. *)
Definition mk_all_ind_top_with (mkOneFn : string -> term -> term -> list (string * list string) -> kername -> list (string * (list nat * list nat)) -> def term)
  (inductData : list ((((string) * (term)) * (term)) * (list (string * (list string))))) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) : list (def term) :=
  map (fun h => mkOneFn (fst (fst (fst h))) (snd (fst (fst h))) (snd (fst h)) (snd h) kn modes) inductData.

(** Extended dispatch for animation_result types with fuel.
    Tries each function in the list, skipping noMatch results. *)
Fixpoint dispatch_outcome_poly_ext
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
          | @NoMatch _ => dispatch_outcome_poly_ext A B t remFuel' input'
          | _ => res
          end
      end
  end.

Fixpoint dispatch_outcome_poly_ext_co_ind
  (A B : Type) (f : A -> B) (lst : list (nat -> animation_result A -> animation_result B)) (fuel' : nat)
  (input' : animation_result A) {struct fuel'} : animation_result B :=
  match fuel' with
  | 0 => map_outcome_poly (A) (B) (f) (input')
  | S remFuel' =>
      match lst with
      | [] => NoMatch B
      | h :: t =>
          let res := h (S remFuel') input' in
          match res with
          | @NoMatch _ => dispatch_outcome_poly_ext_co_ind A B f t remFuel' input'
          | @FuelError _ => map_outcome_poly (A) (B) (f) (input')
          | _ => res
          end
      end
  end.

(** Quote the dispatch function for embedding in generated code. *)
MetaRocq Quote Definition dt := Eval compute in dispatch_outcome_poly_ext.
MetaRocq Run (dt' <- DB.undeBruijn dt ;; tmDefinition "dispatchExtTm'" dt').

MetaRocq Quote Definition dtCo := Eval compute in dispatch_outcome_poly_ext_co_ind.
MetaRocq Run (dtCo' <- DB.undeBruijn dtCo ;; tmDefinition "dispatchExtTmCoInd'" dtCo').

(** Extract the dispatch term for use in fixpoint generation. *)
Definition dispatchExtTm := hd sentinel_def_term (inspect_fix dispatchExtTm').
Definition dispatchExtTmCoInd := hd sentinel_def_term (inspect_fix dispatchExtTmCoInd').

(** Create all top-level animated inductive definitions with dispatch. *)
Definition mk_all_ind_top (inductData : (list ((((string) * (term)) * (term)) * (list (string * (list string)))))) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) : list (def term) :=
app (mk_all_ind_top_with mk_one_ind_top inductData kn modes) [dispatchExtTm].

(** Build all coinductive top-level definitions plus the coinductive dispatch term. *)
Definition mk_all_ind_top_co_ind (inductData : (list ((((string) * (term)) * (term)) * (list (string * (list string)))))) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) : list (def term) :=
app (mk_all_ind_top_with mk_one_ind_top_co_ind inductData kn modes) [dispatchExtTmCoInd].

(** Annotate each inductive's clause list with the inductive names it calls,
    producing the [(inductive_data, recursive_calls)] structure used for
    building the mutual fixpoint. *)
Fixpoint mk_ind_data (data : (list (((string * list term) * list term) * (list (string * term))))) (indNames : list string) :=
  match data with
  | [] => []
  | h :: t => match h with
               | (nm, linT, loutT, lCons) => (nm, linT, loutT, (get_ind_app' lCons indNames)) :: mk_ind_data t indNames
              end
  end.

Unset Universe Checking.

(** Compile a constructor clause: classify premises, animate let-bindings and guard predicates,
    then assemble into a single executable term. *)
Definition compileLetBindingsAndGuards {A : Type} (ind : A) (kn : kername) (bigConj : term) (cstrNm : string) (inVars : list (prod string term))  (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=
let listAllConjs := get_list_conj_all bigConj in
gConjs' <- (get_sorted_oriented_conjs_guard modes listAllConjs [] [] [] (map fst inVars) fuel) ;;

gConjsEq <- tmEval all (filter_conjs_eq gConjs') ;;

lConjs' <- (get_sorted_oriented_conjs_let modes listAllConjs [] [] [] (map fst inVars) fuel) ;;
lc'' <- tmEval all lConjs' ;;
lConjs00 <- tmEval all (remove_duplicate_defs (attach_output_var_to_sorted_conjs lConjs' allVarTpInf modes predTypeInf) (map fst inVars)) ;;
lConjs <- tmEval all (map (fun lc => remove_var_fm_fn_pos lc allVarTpInf) lConjs00) ;;

gConjsPred1 <- tmEval all (filter_conjs_pred' (attach_output_var_to_sorted_conjs gConjs' allVarTpInf modes predTypeInf));;
gConjsPred2 <- tmEval all ( (keep_duplicate_defs (attach_output_var_to_sorted_conjs lConjs' allVarTpInf modes predTypeInf) (map fst inVars))) ;;
gConjsPred <- tmEval all (app gConjsPred1 gConjsPred2) ;;

t <- animate_list_let_and_pred_guard ind kn lConjs gConjsEq gConjsPred inVars outVars (modes) (predTypeInf) (allVarTpInf) (lhsPreds) fuel ;;
t'' <- tmEval all  (typeConstrPatMatch.unwrap_option_term (DB.deBruijnOption t)) ;;

f <- tmUnquote t'' ;;
tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (String.append cstrNm animatedSuffix) (Some hnf) ;;

tmReturn t''.

Set Universe Checking.

(** Quote the inductive at [kn] and extract clause data for all mode-specified
    constructors using [get_data]. *)
Definition get_data' (kn : kername) (modes : list (string * ((list nat) * (list nat)))) : TemplateMonad (list (((string * list term) * list term) * (list (string * term))))  :=
mut <- tmQuoteInductive kn ;;

let lib := ind_bodies mut in
let nmCxt := gen_cxt lib in
let inOutTps := get_in_out_tps modes lib in
get_data lib modes nmCxt inOutTps.

(** Extract [(name, type, constructors)] triples from inductive bodies. *)
Definition getCstrData (lo : list one_inductive_body) : list (string × term × list constructor_body) :=
map (fun (o : one_inductive_body) => ((ind_name o), ((ind_type o), (ind_ctors o)))) lo.

(** Convert a context declaration list to [(name, type)] pairs,
    dropping anonymous binders. *)
Fixpoint procCxtDclLst (c : list context_decl) : list (string * term) :=
  match c with
  | [] => []
  | h :: t => match decl_name h with
             | {| binder_name := nNamed str; binder_relevance := Relevant |} => (str, decl_type h) :: procCxtDclLst t
             | _ =>  procCxtDclLst t
            end
  end.

(** Process constructor data into [(inductive_name, type, [(cstr_name, arg_types)])] triples
    by converting each constructor's argument context. *)
Fixpoint getCstrData' (inDat : list (string × term × list constructor_body)) :=
  match inDat with
  | [] => []
  | h :: t => match h with
            | (str, (tp, lst)) => (str, tp, (map (fun x => (cstr_name x, procCxtDclLst (cstr_args x))) lst)) :: getCstrData' t
            end
  end.

(** Extract full clause type information from a list of inductive bodies. *)
Definition getClauseTpInfo (lo : list one_inductive_body) :=
getCstrData' (getCstrData lo).

(** Extract the predicate-applications appearing as premises in a constructor clause. *)
Definition get_pred_occ (cstr : string * term) : list term :=
  match snd cstr with
  | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2 =>  filter_conjs_pred (get_list_conj_all t1)
  | _ => []
  end.
(** Remove duplicate strings from [l], accumulating unique elements in [l']. *)
Fixpoint remove_dup_str (l : list string) (l' : list string) : list string :=
  match l with
  | [] => l'
  | h :: t => if in_str_lst h l' then remove_dup_str t l' else remove_dup_str t (h :: l')
  end.

(** Extract predicate names (possibly with duplicates) from a list of terms. *)
Fixpoint get_pred_nms'' (l : list term) : list string :=
  match l with
  | [] => []
  | (tApp (tInd {| inductive_mind := (path, indNm); inductive_ind := 0 |} []) lstArgs) :: rest => indNm :: get_pred_nms'' rest
  | (tApp (tVar indNm) lstArgs) :: rest => indNm :: get_pred_nms'' rest
  | _ :: rest => get_pred_nms'' rest
  end.
(** Extract deduplicated predicate names from a list of terms. *)
Definition get_pred_nms (l : list term) : list string :=
remove_dup_str (get_pred_nms'' l) [].

(** Return [(constructor_name, predicate_names_called)] for one clause. *)
Definition get_cstr_pred_occ (cstr : string * term) : string * list string :=
(fst cstr, get_pred_nms (get_pred_occ cstr)).

(** Convert clause data to fixpoint-structure data by annotating each clause
    with the predicates it calls (for building the mutual recursive block). *)
Fixpoint get_fixpt_data (data : list (((string × list term) × list term) × list (string × term))) : list (((string × list term) × list term) × list (string × list string)) :=
  match data with
  | [] => []
  | h :: t => (fst h, (map get_cstr_pred_occ (snd h))) :: get_fixpt_data t
  end.

(** Convert the input and output type lists in each inductive block to single
    product types, suitable for building the fixpoint signature. *)
Fixpoint prod_in_out (ls : list (((string × list term) × list term) × list (string × list string))) : ((list (((string × term) × term) × list (string × list string)))) :=
  match ls with
  | [] => []
  | ((((p1,p2),p3), l4) :: rest) => ((((p1, (prod_term p2)), (prod_term p3)), l4) :: prod_in_out rest)
  end.

(** Extract the premise (LHS) of a clause, or [true] if the clause has no premise. *)
Definition conj_lhs (c : ((string * string) * term)) : term :=
  match snd c with
  | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 t2 => t1
  | _ => <%true%>
  end.

(** Return the variable name at position [n] in [vArgs], or [[]] if absent. *)
Fixpoint get_v_nms_one (n : nat) (vArgs : list term) : list string :=
  match vArgs with
  | [] => []
  | tVar str :: rest => match n with
                      | 0 => [str]
                      | S m => get_v_nms_one m rest
                      end
  | _ :: rest =>        match n with
                      | 0 => []
                      | S m => get_v_nms_one m rest
                      end
  end.

(** Collect variable names at a list of positions [l] from [vArgs]. *)
Fixpoint get_v_nms (l : list nat) (vArgs : list term) : list string :=
  match l with
  | [] => []
  | h :: rest => app (get_v_nms_one h vArgs) (get_v_nms rest vArgs)
  end.

(** Extract variable names from a clause's conclusion according to the positions
    selected by [proj] (either [fst] for inputs or [snd] for outputs) in the mode list. *)
Fixpoint conj_vars_by_projection (proj : list nat * list nat -> list nat) (c : ((string * string) * term)) (modes : list (string * ((list nat) * (list nat)))) : list string :=
  match modes with
  | [] => []
  | h :: rest => if String.eqb (fst h) (fst (fst c)) then match snd c with
                                                        | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1 (tApp (tVar str) lstVar) => get_v_nms (proj (snd h)) lstVar
                                                        | _ => []
                                                        end
                                                        else conj_vars_by_projection proj c rest
  end.

(** Names of the input variables of a clause according to the mode. *)
Definition conj_in_vars := conj_vars_by_projection fst.
(** Names of the output variables of a clause according to the mode. *)
Definition conj_out_vars := conj_vars_by_projection snd.

(** Look up all variable type bindings for the constructor [snd (fst c)] in [tpData]. *)
Fixpoint get_all_vars_tp_inf' (c : ((string * string) * term))  (tpData : list (string × list (string × term))) : list (string * term) :=
  match tpData with
  | [] => []
  | h :: rest => if String.eqb (snd (fst c)) (fst h) then snd h else   get_all_vars_tp_inf' c rest
  end.

(** Retrieve all variable type bindings for a clause from the full type environment. *)
Definition get_all_vars_tp_inf (c : ((string * string) * term)) (tpData : list ((string × term) × list (string × list (string × term)))) :=
get_all_vars_tp_inf' c (concat (map snd tpData)).

(** Build a flat list of [(inductive_name, all_argument_types)] for every inductive,
    concatenating input and output types in order. *)
Definition all_ind_tp_data (data : list (((string × list term) × list term) × list (string × term))) : list (string * list term) :=
map (fun x => (fst (fst (fst x)), app (snd (fst (fst x))) (snd (fst x )))) data.

(** Compute the type of the animated top-level function for one inductive:
    [nat -> animation_result inputTp -> animation_result outputTp]. *)
Definition animation_tp_one (data :  (((string × list term) × list term) × list (string × term))) :  (string * term) :=
((fst (fst (fst data))), (tProd {| binder_name := nAnon; binder_relevance := Relevant |} <%nat%> (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tApp <%animation_result%> [prod_term (snd (fst (fst data)))]) (tApp <%animation_result%> [prod_term ((snd (fst data)))])))).

(** Compute animation types for all inductives in [data]. *)
Definition animation_tp (data :  list (((string × list term) × list term) × list (string × term))) :  list (string * term) :=
map animation_tp_one data.

(** Return the first [(k, v)] pair in [l'] with key [l], or [[]] if absent. *)
Fixpoint get_fm_lst_one {A : Type} (l : string) (l' : list (string * A)) : list (string * A) :=
  match l' with
  | [] => []
  | h :: rest => if String.eqb l (fst h) then [h] else get_fm_lst_one l rest
  end.

(** Retrieve all entries from [l'] whose keys appear in [l]. *)
Fixpoint get_fm_lst {A : Type} (l : list string) (l' : list (string * A)) : list (string * A) :=
  match l with
  | [] => []
  | h :: rest => app (get_fm_lst_one h l') (get_fm_lst rest l')
  end.

(** Look up the animation types of all predicates called by constructor [snd (fst c)]. *)
Fixpoint get_pred_occ_an' (c : ((string * string) * term)) (fixptInf' : list (string × list string)) (anTp : list (string * term)) : list (string * term) :=
  match fixptInf' with
  | [] => []
  | h :: rest => if String.eqb (snd (fst c)) (fst h) then (get_fm_lst (snd h) anTp) else get_pred_occ_an' c rest anTp
  end.

(** Retrieve animation types for all predicates called by clause [c]. *)
Definition get_pred_occ_an (c : ((string * string) * term)) (fixptInf : list (((string × term) × term) × list (string × list string)))
                        (anTp : list (string * term))  : list (string * term) :=

get_pred_occ_an' c (concat (map snd fixptInf)) anTp.

(** Filter [listallVTp] to only include entries whose names are in [lstVar]. *)
Definition get_vars_tp (lstVar : list string) (listallVTp : list (string * term)) : list (string * term) :=
get_fm_lst lstVar listallVTp.

(** Tag each [(cstr_name, clause)] pair with its parent inductive name. *)
Fixpoint clause_lst_one'  (indNm :   string) (cstrs : list (string * term)) : list ((string * string) * term):=
  match cstrs with
  | [] => []
  | (str, t) :: rest => ((indNm, str), t) :: clause_lst_one' indNm rest
  end.

(** Convert a single inductive's data block to a tagged clause list. *)
Definition clause_lst_one'' (dataOne :   (((string × list term) × list term) × list (string × term)))
                         : list ((string * string) * term):=
clause_lst_one' (fst (fst (fst dataOne))) (snd dataOne).

(** Flatten all inductive data blocks into a single tagged clause list. *)
Definition clause_lst (data :   list (((string × list term) × list term) × list (string × term))) : list ((string * string) * term):=
concat (map clause_lst_one'' data).

(** Internal corecursive worker: produces [f n0 inp, f (n0+1) inp, …]. *)
CoFixpoint make_stream (A : Type) (B : Type) (f : nat -> A -> B) (n0 : nat) (inp : A) : Streams.Stream B :=
  Streams.Cons (f n0 inp) (make_stream A B f (S n0) inp).

(** Build an infinite [Streams.Stream] of results by applying [f] to [inp] with
    increasing fuel values starting from 0. *)
Definition streamFromFunction (A : Type) (B : Type) (f : nat -> A -> B) (inp : A) : Streams.Stream B :=
  make_stream A B f 0 inp.

(** Find an inductive by name in [inductData] and return [proj h] for its record,
    failing with [errMsg] if not found. *)
Fixpoint search_tp_by_projection (proj : (((string * term) * term) * list (string * list string)) -> term)
  (inductData : list ((((string) * (term)) * (term)) * (list (string * (list string))))) (nm : string) (errMsg : string) : TemplateMonad term :=
match inductData with
 | [] => tmFail errMsg
 | h :: t => if String.eqb (fst (fst (fst h))) nm then tmReturn (proj h) else search_tp_by_projection proj t nm errMsg
end.

(** Find the input type of a named inductive in the data. *)
Definition search_in_tp := search_tp_by_projection (fun h => snd (fst (fst h))).
(** Find the output type of a named inductive in the data. *)
Definition search_out_tp := search_tp_by_projection (fun h => snd (fst h)).

Unset Universe Checking.

(** Compile a single clause [oneClause] of inductive [kn]: extract type and
    clause data, rewrite non-variable arguments, then call
    [compileLetBindingsAndGuards] to produce the compiled term. *)
Definition an_one_cl {A : Type} (ind : A) (kn : kername)  (oneClause : ((string * string) * term)) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad term :=
allClauseData' <- get_data' kn modes ;;
mut <- tmQuoteInductive kn ;;
allTpData' <- tmEval all (getClauseTpInfo (ind_bodies mut)) ;;
allClauseData <- tmEval all (rewrite_cl_all allClauseData' allTpData') ;;
allTpData <- tmEval all (update_tp_inf_final allClauseData' allTpData') ;;
cstrNm  <- tmEval all (snd (fst oneClause)) ;;

fixptData <- tmEval all (prod_in_out (get_fixpt_data allClauseData)) ;;
conjlhs <- tmEval all (conj_lhs oneClause) ;;

allVarTp <- tmEval all (get_all_vars_tp_inf oneClause allTpData) ;;
inV <- tmEval all (get_vars_tp (conj_in_vars oneClause modes) (allVarTp)) ;;
outV <- tmEval all (get_vars_tp (conj_out_vars oneClause modes) (allVarTp));;
predTps <- tmEval all (all_ind_tp_data allClauseData) ;;
predTpsAn <- tmEval all (animation_tp allClauseData) ;;
predTpsOccAn <- tmEval all (get_pred_occ_an oneClause fixptData predTpsAn) ;;

(compileLetBindingsAndGuards ind kn conjlhs cstrNm inV outV modes predTps allVarTp predTpsOccAn fuel).

(** Compile every clause in [clLst] sequentially, collecting compiled terms. *)
Fixpoint anim_all_cl_lst {A : Type} (ind : A) (kn : kername) (clLst : list ((string * string) * term)) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad (list term) :=

  match clLst with
  | [] => tmReturn []
  | c1 :: cRest => c1An <- an_one_cl ind kn c1 modes fuel ;; cRestAn <- anim_all_cl_lst ind kn cRest modes fuel ;; tmReturn (c1An :: cRestAn)
  end.

(** Main entry point: animate an inductive relation into an executable function.
    Generates a fixpoint that tries each clause with bounded fuel. *)
Definition animateInductive {A : Type} (ind : A) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad (list term) :=
allClauseData' <- get_data' kn modes ;;
mut <- tmQuoteInductive kn ;;
allTpData' <- tmEval all (getClauseTpInfo (ind_bodies mut)) ;;
allClauseData <- tmEval all (rewrite_cl_all allClauseData' allTpData') ;;
allTpData <- tmEval all (update_tp_inf_final allClauseData' allTpData') ;;

clLst <- tmEval all (clause_lst allClauseData) ;;

tms <- anim_all_cl_lst ind kn clLst modes fuel ;;

inductData <- tmEval all (prod_in_out (get_fixpt_data allClauseData)) ;;

let u := (mk_rec_fn (mk_all_ind_top (inductData) kn modes) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (typeConstrPatMatch.unwrap_option_term (DB.deBruijnOption u)) ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append (snd kn) animatedTopFnSuffix) (Some hnf) ;; tmReturn tms.

(** Main entry point: animate a coinductive relation into an executable corecursive stream.
    Generates both a fixpoint and a [Stream] for lazy enumeration. *)
Definition animateCoinductive {A : Type} (ind : A) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad (list term) :=
allClauseData' <- get_data' kn modes ;;
mut <- tmQuoteInductive kn ;;
allTpData' <- tmEval all (getClauseTpInfo (ind_bodies mut)) ;;
allClauseData <- tmEval all (rewrite_cl_all allClauseData' allTpData') ;;
allTpData <- tmEval all (update_tp_inf_final allClauseData' allTpData') ;;

let clLst := clause_lst allClauseData in

tms <- anim_all_cl_lst ind kn clLst modes fuel ;;

let inductData := prod_in_out (get_fixpt_data allClauseData) in

let u := (mk_rec_fn (mk_all_ind_top_co_ind (inductData) kn modes) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (typeConstrPatMatch.unwrap_option_term (DB.deBruijnOption u)) ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append (snd kn) animatedTopFnSuffix) (Some hnf) ;;
              fnInTp <- search_in_tp inductData (snd kn) "cannot find input type" ;;
              fnOutTp <- search_out_tp inductData (snd kn) "cannot find output type" ;;
              let tCoInd := tApp <%streamFromFunction%> [(tApp <%animation_result%> [fnInTp]) ; (tApp <%animation_result%> [fnOutTp]); t'] in
              tCoInd'' <- tmEval all tCoInd ;;
              fStm <- tmUnquote tCoInd'' ;;

              tmEval hnf (my_projT2 fStm) >>=
              tmDefinitionRed_ false (String.append (snd kn) animatedStreamSuffix) (Some hnf) ;;

              tmReturn tms.

(** Compile all clauses for a list of mutually recursive inductives [knLst],
    returning the combined fixpoint structure data. *)
Fixpoint anim_all_cl_multi_def {A : Type} (ind : A) (knLst : list kername)
 (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad ((list (((string × term) × term) × list (string × list string)))) :=

match knLst with
| [] => tmReturn []
| kn :: t => allClauseData' <- get_data' kn modes ;;
             mut <- tmQuoteInductive kn ;;
             allTpData' <- tmEval all (getClauseTpInfo (ind_bodies mut)) ;;
             allClauseData <- tmEval all (rewrite_cl_all allClauseData' allTpData') ;;
             allTpData <- tmEval all (update_tp_inf_final allClauseData' allTpData') ;;

             clLst <- tmEval all (clause_lst allClauseData) ;;

             anim_all_cl_lst ind kn clLst modes fuel ;;

             inductData <- tmEval all (prod_in_out (get_fixpt_data allClauseData)) ;;
             restDefs <- anim_all_cl_multi_def  ind  t  (modes) (fuel) ;; tmReturn (app inductData restDefs)

end.

(** Compile all clauses across a multi-definition mutual block ([topKn :: knLst]),
    assemble a single mutual fixpoint, and define it as [topKn.AnimatedTopFn]. *)
Definition anim_all_cl_multi_def' {A : Type} (topInd : A) (topKn : kername) (knLst : list kername)
 (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad term:=

inductData'' <- anim_all_cl_multi_def (topInd) (topKn :: knLst) (modes) (fuel);;
inductData <- tmEval all inductData'';;

let u := (mk_rec_fn (mk_all_ind_top (inductData) topKn modes) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (typeConstrPatMatch.unwrap_option_term (DB.deBruijnOption u)) ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append (snd topKn) animatedTopFnSuffix) (Some hnf) ;; tmReturn u'.

Set Universe Checking.
