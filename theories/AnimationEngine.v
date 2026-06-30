(** * AnimationEngine — Main Animation Pipeline

    Top-level entry points [animate_inductive] and [animate_coinductive] that
    orchestrate the full animation pipeline: clause data extraction, term
    rewriting, clause-by-clause compilation via [compile_clause_body],
    and final fixpoint assembly into a quoted Rocq definition.

    Depends on: [MetaRocqUtils], [PatternCompilation], [EqualityResolution],
    [AnimationDispatch]. *)

Require Import Animation.AnimationTypes.
Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
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

(** Replace any variable appearing in a function-position in [conj_rhs] (named) with
    an [id_fn] application, so that the variable is treated as data rather
    than as a function call during pattern compilation. *)
Fixpoint strip_fn_position_vars (conj_rhs : named_term)  (var_env : list (string * term)) : named_term :=
  match conj_rhs with
  | tApp (tVar str) lstArgs =>
      match lookup_one_var str var_env with
      | [h] =>
        tApp <%id_fn%>
          ((snd h) :: (tVar str)
            :: (map (fun arg =>
                  strip_fn_position_vars arg var_env)
                lstArgs))
      | _ =>
        tApp (tVar str)
          (map (fun arg =>
              strip_fn_position_vars arg var_env)
            lstArgs)
      end
  | tApp fn lstArgs =>
      tApp (strip_fn_position_vars fn var_env)
        (map (fun arg =>
            strip_fn_position_vars arg var_env)
          lstArgs)
  | _ => conj_rhs
  end.

(** Apply [strip_fn_position_vars] to the RHS of an equality conjunct,
    leaving non-equality conjuncts unchanged. *)
Definition strip_fn_vars
  (conjunct' : tagged_conjunct)
  (var_env : list (string * term)) : tagged_conjunct :=
  match conjunct'.(tc_conjunct) with
  | tApp <%eq%> [typeVar; t1; t2] =>
      let newConj :=
        tApp <%eq%>
          [typeVar; t1 ;
           strip_fn_position_vars t2 var_env]
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
map ind_name l.

(** Generate context from inductive names. *)
Definition gen_cxt (l : list one_inductive_body) :=
map nNamed (rev (ind_body_names l)).

(** Extract all argument types from an inductive type (de Bruijn). *)
Fixpoint get_type (o : term) : option (list term) :=
  match o with
       | (tProd {| binder_name := nAnon; binder_relevance := Relevant |} t (tSort sProp)) => Some [t]
       | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t1  t2 =>
         match get_type t2 with
         | Some rest => Some (t1 :: rest)
         | None => None
         end
       | _ => None
  end.

(** Select types according to mode indices. *)
Definition get_type' (mode : list nat) (l : list term) : option (list term) :=
  let fix go (ms : list nat) : option (list term) :=
    match ms with
    | [] => Some []
    | n :: rest =>
      match nth_error l n, go rest with
      | Some t, Some ts => Some (t :: ts)
      | _, _ => None
      end
    end in
  go mode.

(** Get input type according to mode. *)
Definition input_types (in_mode : list nat) (o : one_inductive_body) : option (list term) :=
  match get_type (ind_type o) with
  | Some lstType => get_type' in_mode lstType
  | None => None
  end.

(** Strip all top-level foralls/products from a de Bruijn term to get to the body. *)
Fixpoint reduce_clause (t : term) :=
  match t with
  | (tPro str typ t') => reduce_clause t'
  | t'' => t''
  end.

(** Extract preconditions (hypotheses) from a constructor clause (de Bruijn). *)
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

(** Get the body (recursive premises) of a constructor clause (de Bruijn). *)
Definition clause_body_raw (t : term) : list term :=
process_preconditions (get_preconditions (reduce_clause t)).

(** Get the head (conclusion) of a constructor clause (de Bruijn). *)
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
Fixpoint ind_occurrences (l : list named_term) (indNames : list string) : list string :=
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
  (l : list (string * named_term))
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
  : option (list in_out_entry) :=
  match b with
    | h' :: t' =>
        if String.eqb (fst mode) (ind_name h')
        then match input_types (fst (snd mode)) h',
                   input_types (snd (snd mode)) h' with
             | Some inTps, Some outTps =>
               Some [{| ioe_name := ind_name h';
                        ioe_in_types := inTps;
                        ioe_out_types := outTps |}]
             | _, _ => None
             end
        else in_out_types_one mode t'
    | _ => Some []
    end.

(** Get input/output types for all inductives in the mode list. *)
Fixpoint in_out_types (modes : mode_map)
  (b : list one_inductive_body)
  : option (list in_out_entry) :=
  match modes with
  | [] => Some []
  | h :: t =>
    match in_out_types_one h b, in_out_types t b with
    | Some l1, Some l2 => Some (app l1 l2)
    | _, _ => None
    end
  end.

(** Convert constructor bodies from de Bruijn to named terms by unquoting into
    the named context [l], returning [(constructor_name, named_clause)] pairs. *)
Fixpoint mk_nm_tm (c : list constructor_body)
  (l : list name)
  : TemplateMonad (list (string * named_term)) :=
  match c with
  | [] => tmReturn []
  | (h :: t) =>
      r <- DB.un_de_bruijn' l (cstr_type h) ;;
      r' <- tmEval all r ;;
      let hres := (cstr_name h, (reduce_clause r')) in
      rest <- mk_nm_tm t l ;;
      tmReturn (hres :: rest)
  end.

(** Retrieve clause data for all inductives in [lib]: for each body, convert
    constructors to named terms and pair them with their input/output type info. *)
Definition find_in_out_entry (name : string)
  (entries : list in_out_entry)
  : option in_out_entry :=
  List.find (fun e => String.eqb (ioe_name e) name) entries.

Fixpoint get_data
  (lib : list one_inductive_body)
  (ln : mode_map) (nm_ctx : list name)
  (entries : list in_out_entry)
  : TemplateMonad (list clause_data) :=

  match lib with
  | [] => tmReturn []
  | h' :: t' =>
      match find_in_out_entry (ind_name h') entries with
      | Some e =>
          dbth <- mk_nm_tm (ind_ctors h') nm_ctx ;;
          rest <- get_data t' ln nm_ctx entries ;;
          tmReturn ({| cd_ind_name := ioe_name e;
                       cd_in_types := ioe_in_types e;
                       cd_out_types := ioe_out_types e;
                       cd_clauses := dbth |} :: rest)
      | None => tmReturn []
      end
  end.

(** Replace non-variable subterms in [l] with fresh variables (prefixed by
    [var_pfx]), emitting equality constraints to bind the originals.
    Returns triples [(replacement_vars, equality_constraints, new_var_bindings)]. *)
Fixpoint subst_pattern_vars (l : list named_term)
  (var_pfx : string) (n : nat) (argTps : list term)
  : list ((list named_term * list named_term)
          * list (string * term)) :=
  match l with
  | [] => []
  | (tVar str) :: rest =>
      (([(tVar str)], []), [])
      :: (subst_pattern_vars rest var_pfx n (tl argTps))
  | t' :: rest =>
      let vn :=
        (var_pfx ++ (string_of_nat n)) in
      (([(tVar vn)],
        [tApp <%eq%>
          [(hd <%bool%> argTps); (tVar vn); t']]),
       ([(vn, (hd <%bool%> argTps))]))
      :: (subst_pattern_vars rest var_pfx (S n)
            (tl argTps))

  end.
(** Look up the argument types for predicate named [s] in the type environment. *)
Fixpoint find_tp (s : string) (pred_arg_tps : pred_type_map) : list term :=
  match pred_arg_tps with
  | [] => []
  | h :: t => if String.eqb s (fst h) then snd h else find_tp s t
  end.

(** For each conjunct in [l], replace non-variable arguments of predicates with
    fresh variables and collect the resulting equality side-conditions and
    new variable bindings.  Equality conjuncts are passed through unchanged. *)
Fixpoint resolve_conj_inputs (l : list named_term)
  (var_pfx : string) (n : nat)
  (pred_arg_tps : pred_type_map)
  : list ((named_term * list named_term) * list (string * term)) :=
  match l with
  | [] => []
  | (tApp <%eq%> lstArgs) :: rest =>
      (((tApp <%eq%> lstArgs) , []), [])
      :: resolve_conj_inputs rest var_pfx n
           pred_arg_tps
  | (tApp (tVar str) lstArgs) :: rest =>
      let result :=
        subst_pattern_vars lstArgs var_pfx n
          (find_tp str pred_arg_tps) in
      ((((tApp (tVar str)
            (concat (map (fun y => fst (fst y))
               result)))),
        (concat (map (fun y => snd (fst y)) result))),
       (concat (map snd result)))
      :: resolve_conj_inputs rest var_pfx
           (length lstArgs + S n) pred_arg_tps
  | (tApp (tInd {| inductive_mind := (_path, ind_nm);
       inductive_ind := 0 |} []) lstArgs) :: rest =>
      let result :=
        subst_pattern_vars lstArgs var_pfx n
          (find_tp ind_nm pred_arg_tps) in
      let ind := tInd {| inductive_mind := (_path, ind_nm);
                         inductive_ind := 0 |} [] in
      ((((tApp ind
            (concat (map (fun y => fst (fst y))
               result)))),
        (concat (map (fun y => snd (fst y)) result))),
       (concat (map snd result)))
      :: resolve_conj_inputs rest var_pfx
           (length lstArgs + S n) pred_arg_tps

  | t'' :: rest => ((t'', []), []) :: resolve_conj_inputs rest var_pfx n pred_arg_tps

  end.

(** Collect variable and inductive names from a term, with arguments listed
    before the function (used for computing fresh-variable prefix lengths). *)
Fixpoint ordered_vars_from_clause (t : named_term) : list string :=
  match t with
  | tVar str  => [str]
  | (tInd {| inductive_mind := (_path, str); inductive_ind := k |} []) => [str]
  | tApp fn lst => flat_map ordered_vars_from_clause lst ++ ordered_vars_from_clause fn

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
Definition pred_arg_types_raw (tp_env : list type_env_entry) : list (string * term) :=
map (fun y => (y.(te_pred_name), y.(te_pred_type))) tp_env.

(** Build a [(name, arg_types)] environment for all inductive predicates by
    destructuring each predicate's type into its argument list. *)
Definition pred_arg_types (tp_env : list type_env_entry) : list (string * list term) :=
  flat_map (fun y =>
    match get_type (snd y) with
    | Some tps => [(fst y, tps)]
    | None => []
    end) (pred_arg_types_raw tp_env).
(** Flatten a right-nested [and] tree into a list of conjuncts (named). *)
Fixpoint flatten_and (t : named_term) : list named_term :=
  match t with
  | tApp <%and%> [h;h1] => h :: (flatten_and h1)
  | t' => [t']
  end.

(** Split a clause of the form [P1 /\ P2 /\ ... -> conclusion] into the list
    [P1, P2, ..., conclusion]; handles a conjunction in the premise position. *)
Definition flatten_clause (t : named_term) : list named_term :=
  match t with
  | tProd {| binder_name := nAnon;
             binder_relevance := Relevant |}
      (tApp <%and%> lst) t' =>
      app (flatten_and (tApp <%and%> lst)) [t']
  | tProd {| binder_name := nAnon; binder_relevance := Relevant |} t'' t' =>  [t''; t']
  | t''' => [t''']
  end.
(** Rebuild a right-nested [and] term from a flat list of conjuncts (named). *)
Fixpoint build_and (l : list named_term) : option named_term :=
  match l with
  | [] => None
  | [h] => Some h
  | h :: rest =>
    match build_and rest with
    | Some t => Some (tApp <%and%> [h; t])
    | None => None
    end
  end.
(** Inverse of [flatten_clause]: reassemble a flat list [P1, ..., Pn, conclusion]
    back into a single clause term. *)
Definition build_clause (ts : list named_term) : option named_term :=
  match rev ts with
  | [] => None
  | [h] => Some h
  | [h1; h2] => Some (tProd {| binder_name := nAnon; binder_relevance := Relevant |} h2 h1)
  | h :: t =>
    match build_and (rev t) with
    | Some conjunction => Some (tProd {| binder_name := nAnon; binder_relevance := Relevant |} conjunction h)
    | None => None
    end
  end.

(** Rewrite a clause by substituting non-variable predicate arguments with fresh
    variables and splicing in the resulting equality side-conditions. *)
Definition rewrite_cl (t : named_term) (tp_env : list type_env_entry) : option named_term :=
let prefix := fresh_var_prefix (S (list_max (map String.length (ordered_vars_from_clause t)))) in
let lstTm := flatten_clause t in
let pred_arg_tp := pred_arg_types tp_env in
let resolved := resolve_conj_inputs lstTm prefix 0 pred_arg_tp in
build_clause
  (concat (map (fun y => snd (fst y)) resolved) ++
   map (fun y => fst (fst y)) resolved).

(** Collect the new variable-type bindings introduced by rewriting clause [t]. *)
Definition extra_type_info (t : named_term) (tp_env : list type_env_entry) : list (string * term) :=

let prefix := fresh_var_prefix (S (list_max (map String.length (ordered_vars_from_clause t)))) in
let lstTm := flatten_clause t in
let pred_arg_tp := pred_arg_types tp_env in
concat (map snd (resolve_conj_inputs lstTm prefix 0 pred_arg_tp)).

(** Rewrite all clause terms in a flat [(constructor_name, named_clause)] list. *)
Fixpoint rewrite_cl_all1
  (all_cdata1 : list (string × named_term))
  (tp_env : list type_env_entry)
  : option (list (string × named_term)) :=
  match all_cdata1 with
  | [] => Some []
  | (cstr_nm,t) :: rest =>
    match rewrite_cl t tp_env, rewrite_cl_all1 rest tp_env with
    | Some t', Some rest' => Some ((cstr_nm, t') :: rest')
    | _, _ => None
    end
  end.

(** Rewrite the clause data block for a single inductive. *)
Definition rewrite_cl_all1'
  (all_cdata1 : clause_data)
  (tp_env : list type_env_entry) : option clause_data :=
  match rewrite_cl_all1 all_cdata1.(cd_clauses) tp_env with
  | Some cls =>
    Some {| cd_ind_name := all_cdata1.(cd_ind_name);
       cd_in_types := all_cdata1.(cd_in_types);
       cd_out_types := all_cdata1.(cd_out_types);
       cd_clauses := cls |}
  | None => None
  end.

(** Rewrite all clause data blocks across all inductives (named terms throughout). *)
Fixpoint rewrite_cl_all
  (all_cdata : list clause_data)
  (tp_env : list type_env_entry)
  : option (list clause_data) :=
  match all_cdata with
  | [] => Some []
  | y :: rest =>
    match rewrite_cl_all1' y tp_env, rewrite_cl_all rest tp_env with
    | Some y', Some rest' => Some (y' :: rest')
    | _, _ => None
    end
  end.

(** Collect new variable-type bindings for each clause in a flat clause list. *)
Fixpoint extra_type_info_list
  (all_cdata1 : list (string × named_term))
  (tp_env : list type_env_entry)
  : list (string * list (string * term)) :=
  match all_cdata1 with
  | [] => []
  | (cstr_nm, t) :: rest =>
      (cstr_nm, extra_type_info t tp_env)
      :: extra_type_info_list rest tp_env
  end.

(** Collect new variable-type bindings for every inductive's clause data. *)
Fixpoint all_extra_type_info
  (all_cdata : list clause_data)
  (tp_env : list type_env_entry)
  : list (string *
          (list (string * list (string * term)))) :=
  match all_cdata with
  | [] => []
  | h :: rest =>
      (h.(cd_ind_name),
       extra_type_info_list h.(cd_clauses) tp_env)
      :: (all_extra_type_info rest tp_env)
  end.

(** Look up [cstr_nm] in an association list of constructor-name → type bindings. *)
Fixpoint retrieve (cstr_nm : string)
  (l : list (string × list (string × term)))
  : list (string * term) :=
  match l with
  | [] => []
  | h :: rest => if (String.eqb cstr_nm (fst h)) then (snd h) else retrieve cstr_nm rest
  end.

(** Retrieve the original type bindings for constructor [cstr_nm] of [ind_nm]. *)
Fixpoint old_type_info (ind_nm : string)
  (cstr_nm : string)
  (tp_env : list type_env_entry)
  : list (string * term) :=
  match tp_env with
  | [] => []
  | h :: rest =>
      if (String.eqb ind_nm h.(te_pred_name))
      then retrieve cstr_nm h.(te_cstr_vars)
      else old_type_info ind_nm cstr_nm rest
  end.

(** Retrieve the newly-introduced (fresh-variable) type bindings for
    constructor [cstr_nm] of [ind_nm] after clause rewriting. *)
Fixpoint new_type_info (ind_nm : string)
  (cstr_nm : string)
  (extra_tp : list ((string) × list
    (string × list (string × term))))
  : list (string * term) :=
  match extra_tp with
  | [] => []
  | (str, lst) :: rest =>
      if (String.eqb ind_nm str)
      then retrieve cstr_nm lst
      else new_type_info ind_nm cstr_nm rest
  end.
(** Merge original and fresh-variable type bindings for one inductive block. *)
Definition update_type_info
  (tp_env1 : type_env_entry)
  (tp_env : list type_env_entry)
  (extra_tp : list ((string) × list
    (string × list (string × term)))) : type_env_entry :=
  let ind_nm := tp_env1.(te_pred_name) in
  {| te_pred_name := ind_nm;
     te_pred_type := tp_env1.(te_pred_type);
     te_cstr_vars :=
       map (fun y =>
         ((fst y),
          app (old_type_info ind_nm (fst y) tp_env)
              (new_type_info ind_nm (fst y) extra_tp)))
         tp_env1.(te_cstr_vars) |}.

(** Apply [update_type_info] to every inductive block in [tp_env1l]. *)
Definition update_type_info_list
  (tp_env1l : list type_env_entry)
  (tp_env : list type_env_entry)
  (extra_tp : list ((string) × list
    (string × list (string × term)))) :=
map (fun y => update_type_info y tp_env extra_tp) tp_env1l.

(** Self-update: merge each inductive block's extra type info into itself. *)
Definition finalize_type_info_one
  (tp_env : list type_env_entry)
  (extra_tp : list ((string) × list
    (string × list (string × term)))) :=
update_type_info_list tp_env tp_env extra_tp.

(** Compute the final, fully-merged type environment after clause rewriting:
    derives extra bindings from [all_cdata] and folds them into [tp_env]. *)
Definition finalize_type_info
  (all_cdata : list clause_data)
  (tp_env : list type_env_entry)
  : (list type_env_entry) :=
finalize_type_info_one tp_env  (all_extra_type_info all_cdata tp_env).

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
Fixpoint apply_top_fn (kn : kername) (cdata : list (string * (list string))) : list global_term :=
  match cdata with
  | [] => []
  | (post_con_cons, pre_con_ind) :: t => match pre_con_ind with
                                   | [] =>
                                       (quote_const' kn
                                         (post_con_cons ++ anim_suffix))
                                       :: apply_top_fn kn t
                                   | l =>
                                       tApp
                                         (quote_const' kn
                                           (post_con_cons ++ anim_suffix))
                                         (map (fun nm =>
                                           tVar (nm ++ top_fn_suffix)) l)
                                       :: apply_top_fn kn t
                                   end
  end.

(** Return the input-position indices for [ind_nm] in the mode list, or [[]]
    if [ind_nm] has no explicit input positions (empty-input mode). *)
Fixpoint lookup_mode_input (ind_nm : string) (modes : mode_map) :=
  match modes with
  | [] => []
  | (h :: rest) => if String.eqb ind_nm (fst h) then fst (snd h) else lookup_mode_input ind_nm rest
  end.
(** Shared base for building one fixpoint definition for a top-level animated inductive.
    Parameterized by the zero-fuel branch, dispatch construction, and whether input is explicit. *)
Definition mk_ind_top_base (ind_nm : string) (in_tp out_tp : global_term)
  (cdata : list (string * (list string))) (kn : kername)
  (zero_br : term) (mk_dispatch : term -> term)
  (has_input : bool) : def term :=
let fn_list_tp := tProd {| binder_name := nAnon; binder_relevance := Relevant |}
      <%nat%> (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
     (tApp <%animation_result%> [in_tp]) (tApp <%animation_result%> [out_tp])) in
let list_tm := build_coq_list (apply_top_fn kn cdata) fn_list_tp in
let case_expr :=
  tCase
    {| ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
       ci_npar := 0; ci_relevance := Relevant |}
    {| puinst := []; pparams := [];
       pcontext := [{| binder_name := nNamed "fuel"; binder_relevance := Relevant |}];
       preturn := tApp <%animation_result%> [out_tp] |}
    (tVar "fuel")
    [{| bcontext := []; bbody := zero_br |};
     {| bcontext := [{| binder_name := nNamed "rem_fuel"; binder_relevance := Relevant |}];
        bbody := mk_dispatch list_tm |}] in
let input_lam := tLam "input" (tApp <%animation_result%> [in_tp]) case_expr in
let body :=
  tLam "fuel" <%nat%>
    (if has_input then input_lam else tApp input_lam [<%Success bool true%>]) in
let tp :=
  if has_input
  then tPro "fuel" <%nat%> (tPro "input" (tApp <%animation_result%> [in_tp])
         (tApp <%animation_result%> [out_tp]))
  else tPro "fuel" <%nat%> (tApp <%animation_result%> [out_tp]) in
{| dname := {| binder_name := nNamed ((ind_nm ++ top_fn_suffix));
               binder_relevance := Relevant |};
   dtype := tp; dbody := body; rarg := 0 |}.

(** Build a top-level fixpoint definition for an inductive with explicit input. *)
Definition mk_ind_top_body (ind_nm : string) (in_tp out_tp : global_term)
  (cdata : list (string * (list string))) (kn : kername) : def term :=
mk_ind_top_base ind_nm in_tp out_tp cdata kn
  (tApp <%FuelError%> [out_tp])
  (fun list_tm => tApp (tVar "dispatch_ind_ext")
     [in_tp; out_tp; list_tm; tVar "rem_fuel"; tVar "input"])
  true.

(** Build a top-level fixpoint definition for an inductive with no input
    (empty-input mode: the argument is always [Success bool true]). *)
Definition mk_ind_top_no_input (ind_nm : string) (in_tp out_tp : global_term)
  (cdata : list (string * (list string))) (kn : kername) : def term :=
mk_ind_top_base ind_nm in_tp out_tp cdata kn
  (tApp <%FuelError%> [out_tp])
  (fun list_tm => tApp (tVar "dispatch_ind_ext")
     [in_tp; out_tp; list_tm; tVar "rem_fuel"; tVar "input"])
  false.

(** Build a top-level fixpoint definition for a coinductive with explicit input,
    using [map_outcome Rest] as the zero-fuel branch. *)
Definition mk_coind_top_body (ind_nm : string) (in_tp out_tp : global_term)
  (cdata : list (string * (list string))) (kn : kername) : def term :=
let rest_fn := quote_const' kn ((ind_nm ++ "Rest")) in
mk_ind_top_base ind_nm in_tp out_tp cdata kn
  (tApp <%map_outcome%> [in_tp; out_tp; rest_fn; tVar "input"])
  (fun list_tm => tApp (tVar "dispatch_coind_ext")
     [in_tp; out_tp; rest_fn; list_tm; tVar "rem_fuel"; tVar "input"])
  true.

(** Build a top-level fixpoint definition for a coinductive with no input,
    using [map_outcome Rest] as the zero-fuel branch. *)
Definition mk_coind_top_no_input (ind_nm : string) (in_tp out_tp : global_term)
  (cdata : list (string * (list string))) (kn : kername) : def term :=
let rest_fn := quote_const' kn ((ind_nm ++ "Rest")) in
mk_ind_top_base ind_nm in_tp out_tp cdata kn
  (tApp <%map_outcome%> [in_tp; out_tp; rest_fn; tVar "input"])
  (fun list_tm => tApp (tVar "dispatch_coind_ext")
     [in_tp; out_tp; rest_fn; list_tm; tVar "rem_fuel"; tVar "input"])
  false.

(** Dispatch to [mk_ind_top_body] or [mk_ind_top_no_input] based on the mode for [ind_nm]. *)
Definition mk_ind_fixpoint (ind_nm : string)
  (in_tp : global_term) (out_tp : global_term)
  (cdata : list (string * (list string)))
  (kn : kername) (modes : mode_map) : def term :=
  match lookup_mode_input ind_nm modes with
  | [] => mk_ind_top_body ind_nm in_tp out_tp cdata kn
  | _ => mk_ind_top_body ind_nm in_tp out_tp cdata kn
  end.

(** Dispatch to [mk_coind_top_body] or [mk_coind_top_no_input] based on mode. *)
Definition mk_coind_fixpoint (ind_nm : string)
  (in_tp : global_term) (out_tp : global_term)
  (cdata : list (string * (list string)))
  (kn : kername) (modes : mode_map) : def term :=
  match lookup_mode_input ind_nm modes with
  | [] =>  mk_coind_top_body ind_nm in_tp out_tp cdata kn
  | _ => mk_coind_top_body ind_nm in_tp out_tp cdata kn
  end.

(** Construct a fixpoint term from a list of definitions. *)
Definition mk_rec_fn (ls : list (def term)) (j : nat) : term :=
 tFix ls j.

(** Apply [mk_one] to every inductive in [ind_data], building the full list
    of fixpoint definitions for the mutual recursive block. *)
Definition mk_all_fixpoints
  (mk_one : string -> term -> term ->
    list (string * list string) -> kername ->
    list (string * (list nat * list nat)) ->
    def term)
  (ind_data : list fixpoint_entry)
  (kn : kername) (modes : mode_map)
  : list (def term) :=
  map (fun h =>
    mk_one h.(fe_ind_name)
      h.(fe_in_type) h.(fe_out_type)
      h.(fe_cstr_preds) kn modes) ind_data.

(** Extended dispatch for animation_result types with fuel.
    Tries each function in the list, skipping noMatch results. *)
Fixpoint dispatch_ind_ext
  (A B : Type) (lst : list (nat -> animation_result A -> animation_result B)) (fuel' : nat)
  (input' : animation_result A) {struct fuel'} : animation_result B :=
  match fuel' with
  | 0 => FuelError B
  | S rem_fuel' =>
      match lst with
      | [] => NoMatch B
      | h :: t =>
          let res := h rem_fuel' input' in
          match res with
          | @NoMatch _ => dispatch_ind_ext A B t rem_fuel' input'
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
  | 0 => map_outcome A B f input'
  | S rem_fuel' =>
      match lst with
      | [] => NoMatch B
      | h :: t =>
          let res := h (S rem_fuel') input' in
          match res with
          | @NoMatch _ => dispatch_coind_ext A B f t rem_fuel' input'
          | @FuelError _ => map_outcome A B f input'
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
Definition dispatch_ext_tm : option (def term) :=
  match inspect_fix dispatch_ext_tm' with
  | d :: _ => Some d
  | [] => None
  end.
Definition dispatch_ext_tm_co_ind : option (def term) :=
  match inspect_fix dispatch_ext_tm_co_ind' with
  | d :: _ => Some d
  | [] => None
  end.

(** Create all top-level animated inductive definitions with dispatch. *)
Definition mk_all_ind
  (ind_data : (list fixpoint_entry))
  (kn : kername) (modes : mode_map)
  : option (list (def term)) :=
  match dispatch_ext_tm with
  | Some d => Some (app (mk_all_fixpoints mk_ind_fixpoint ind_data kn modes) [d])
  | None => None
  end.

(** Build all coinductive top-level definitions plus the coinductive dispatch term. *)
Definition mk_all_coind
  (ind_data : (list fixpoint_entry))
  (kn : kername) (modes : mode_map)
  : option (list (def term)) :=
  match dispatch_ext_tm_co_ind with
  | Some d => Some (app (mk_all_fixpoints mk_coind_fixpoint ind_data kn modes) [d])
  | None => None
  end.

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



(** Compile a constructor clause (named input -> de Bruijn output): classify premises,
    animate let-bindings and guard predicates, then assemble into a single executable term. *)
Definition compile_clause_body {A : Type}
  (ind : A) (kn : kername) (big_conj : named_term)
  (cstr_nm : string)
  (in_vars : list (prod string term))
  (out_vars : list (prod string term))
  (modes : mode_map)
  (pred_types : pred_type_map)
  (var_env : list (string * term))
  (lhs_preds : list (string * term))
  (fuel : nat) : TemplateMonad term :=
(* Split the big conjunction into individual premises *)
let listAllConjs := collect_all_conjs big_conj in
(* Classify premises: guards check equality/predicates, lets bind outputs *)
gConjs' <- (get_sorted_guards modes listAllConjs [] [] [] (map fst in_vars) fuel) ;;
(* Separate equality guards from predicate guards *)
g_conjs_eq <- tmEval all (filter_conjs_eq gConjs' modes) ;;
(* Get the let-binding conjuncts (sorted by dependency order) *)
l_conjs' <- (get_sorted_lets modes listAllConjs [] [] [] (map fst in_vars) fuel) ;;
lc'' <- tmEval all l_conjs' ;;
(* Attach output variable info, deduplicate, strip function-position vars *)
l_conjs00 <- tmEval all
  (remove_dup_defs
    (attach_sorted_outputs l_conjs'
      var_env modes pred_types)
    (map fst in_vars)) ;;
l_conjs <- tmEval all (map (fun lc => strip_fn_vars lc var_env) l_conjs00) ;;

(* Collect predicate guard conjuncts from both guard and let sources *)
g_conjs_pred1 <- tmEval all
  (filter_conjs_pred'
    (attach_sorted_outputs gConjs'
      var_env modes pred_types));;
g_conjs_pred2 <- tmEval all
  ((keep_dup_defs
    (attach_sorted_outputs l_conjs'
      var_env modes pred_types)
    (map fst in_vars))) ;;
g_conjs_pred <- tmEval all (app g_conjs_pred1 g_conjs_pred2) ;;
(* Animate all let-bindings and guards into a single term *)
t <- animate_lets_and_guards ind kn l_conjs
  g_conjs_eq g_conjs_pred in_vars out_vars
  (modes) (pred_types) (var_env)
  (lhs_preds) fuel ;;
(* Convert to de Bruijn, unquote, and register as a Rocq definition *)
match DB.de_bruijn_option t with
| Some db_t =>
t'' <- tmEval all db_t ;;
f <- tmUnquote t'' ;;
tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false ((cstr_nm ++ anim_suffix)) (Some hnf) ;;

tmReturn t''
| None => tmFail "de Bruijn conversion failed in animate_one_clause"
end.

Set Universe Checking.

(** Quote the inductive at [kn] and extract clause data for all mode-specified
    constructors using [get_data]. *)
Definition get_data' (kn : kername)
  (modes : mode_map)
  : TemplateMonad (list clause_data) :=
mut <- tmQuoteInductive kn ;;

let lib := ind_bodies mut in
let nm_ctx := gen_cxt lib in
match in_out_types modes lib with
| Some inOutTps => get_data lib modes nm_ctx inOutTps
| None => tmFail "failed to extract input/output types from mode"
end.

(** Extract [(name, type, constructors)] triples from inductive bodies. *)
Definition cstr_body_data
  (lo : list one_inductive_body)
  : list (string × term × list constructor_body) :=
map (fun o => (ind_name o, (ind_type o, ind_ctors o))) lo.

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
  | (tApp (tInd {| inductive_mind := (path, ind_nm);
       inductive_ind := 0 |} []) lstArgs) :: rest =>
      ind_nm :: pred_names_aux rest
  | (tApp (tVar ind_nm) lstArgs) :: rest => ind_nm :: pred_names_aux rest
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
    [nat -> animation_result in_tp -> animation_result out_tp]. *)
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
Fixpoint clauses_of_ind (ind_nm : string)
  (cstrs : list (string * term))
  : list ((string * string) * term) :=
  match cstrs with
  | [] => []
  | (str, t) :: rest => ((ind_nm, str), t) :: clauses_of_ind ind_nm rest
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

(** Find an inductive by name in [ind_data] and return [proj h] for its record,
    failing with [errMsg] if not found. *)
Fixpoint search_type_by_proj (proj : fixpoint_entry -> term)
  (ind_data : list fixpoint_entry) (nm : string) (errMsg : string) : TemplateMonad term :=
match ind_data with
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

(** Compile a single clause [one_clause] of inductive [kn] (named input -> de Bruijn output):
    extract type and clause data, rewrite non-variable arguments, then call
    [compile_clause_body] to produce the compiled de Bruijn term. *)
Definition animate_one_clause {A : Type}
  (ind : A) (kn : kername)
  (one_clause : ((string * string) * named_term))
  (modes : mode_map) (fuel : nat)
  : TemplateMonad term :=
(* Step 1: gather clause data and type info from the inductive definition *)
all_cdata' <- get_data' kn modes ;;
mut <- tmQuoteInductive kn ;;
tp_data' <- tmEval all (clause_type_info (ind_bodies mut)) ;;
(* Step 2: rewrite clauses to normalize non-variable arguments *)
all_cdata <- match rewrite_cl_all all_cdata' tp_data' with
                 | Some d => tmEval all d
                 | None => tmFail "clause rewriting failed"
                 end ;;
tp_data <- tmEval all (finalize_type_info all_cdata' tp_data') ;;
cstr_nm  <- tmEval all (snd (fst one_clause)) ;;
(* Step 3: compute fixpoint metadata and clause LHS *)
fixpt_data <- tmEval all (prod_in_out (fixpoint_data all_cdata)) ;;
conj_lhs <- tmEval all (conj_lhs one_clause) ;;
(* Step 4: resolve variable types and partition into input/output *)
var_tp <- tmEval all (all_var_types one_clause tp_data) ;;
inV <- tmEval all
  (lookup_var_types
    (conj_in_vars one_clause modes) (var_tp)) ;;
outV <- tmEval all
  (lookup_var_types
    (conj_out_vars one_clause modes) (var_tp));;
(* Step 5: gather predicate type info for recursive calls *)
pred_tps <- tmEval all (all_ind_tp_data all_cdata) ;;
(*tmPrint pred_tps ;;*)
pred_tps_an <- tmEval all (animation_types all_cdata) ;;
pred_tps_occ <- tmEval all
  (pred_animation_types one_clause
    fixpt_data pred_tps_an) ;;
(* Step 6: compile the clause body with all gathered info *)
(compile_clause_body ind kn conj_lhs cstr_nm inV outV modes pred_tps var_tp pred_tps_occ fuel).

(** Compile every clause in [cl_lst] sequentially, collecting compiled terms. *)
Fixpoint animate_clause_list {A : Type}
  (ind : A) (kn : kername)
  (cl_lst : list ((string * string) * term))
  (modes : mode_map) (fuel : nat)
  : TemplateMonad (list term) :=

  match cl_lst with
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
all_cdata' <- get_data' kn modes ;;
mut <- tmQuoteInductive kn ;;
tp_data' <- tmEval all (clause_type_info (ind_bodies mut)) ;;
all_cdata <- match rewrite_cl_all all_cdata' tp_data' with
                 | Some d => tmEval all d
                 | None => tmFail "clause rewriting failed"
                 end ;;
tp_data <- tmEval all (finalize_type_info all_cdata' tp_data') ;;
(*tmPrint all_cdata;;
tmPrint tp_data;;*)
(* Phase 2: compile each clause into a match-and-return term *)
cl_lst <- tmEval all (all_clauses all_cdata) ;;
tms <- animate_clause_list ind kn cl_lst modes fuel ;;
(* Phase 3: assemble the fixpoint that dispatches over compiled clauses *)
ind_data <- tmEval all (prod_in_out (fixpoint_data all_cdata)) ;;
match mk_all_ind ind_data kn modes with
| Some defs =>
  let u := mk_rec_fn defs 0 in
          u' <- tmEval all u ;;
          match DB.de_bruijn_option u with
          | Some db_u =>
            t' <- tmEval all db_u ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false
                (snd kn ++ top_fn_suffix)
                (Some hnf) ;;
              tmReturn tms
          | None => tmFail "de Bruijn conversion failed in animate_inductive"
          end
| None => tmFail "dispatch term extraction failed in animate_inductive"
end.

(** Main entry point: animate a coinductive relation into an executable corecursive stream.
    Generates both a fixpoint and a [Stream] for lazy enumeration. *)
Definition animate_coinductive {A : Type}
  (ind : A) (kn : kername)
  (modes : mode_map) (fuel : nat)
  : TemplateMonad (list term) :=
all_cdata' <- get_data' kn modes ;;
mut <- tmQuoteInductive kn ;;
tp_data' <- tmEval all (clause_type_info (ind_bodies mut)) ;;
all_cdata <- match rewrite_cl_all all_cdata' tp_data' with
                 | Some d => tmEval all d
                 | None => tmFail "clause rewriting failed"
                 end ;;
tp_data <- tmEval all (finalize_type_info all_cdata' tp_data') ;;

let cl_lst := all_clauses all_cdata in

tms <- animate_clause_list ind kn cl_lst modes fuel ;;

let ind_data := prod_in_out (fixpoint_data all_cdata) in

match mk_all_coind ind_data kn modes with
| Some defs =>
  let u := mk_rec_fn defs 0 in
          u' <- tmEval all u ;;
          match DB.de_bruijn_option u with
          | Some db_u =>
            t' <- tmEval all db_u ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (snd kn ++ top_fn_suffix) (Some hnf) ;;
              fn_in_tp <- search_in_tp ind_data (snd kn) "cannot find input type" ;;

              fn_out_tp <- search_out_tp ind_data (snd kn) "cannot find output type" ;;
              let t_coind :=
                tApp <%stream_of_fn%>
                  [(tApp <%animation_result%> [fn_in_tp]);
                   (tApp <%animation_result%> [fn_out_tp]);
                   t'] in
              t_coind'' <- tmEval all t_coind ;;
              f_stm <- tmUnquote t_coind'' ;;

              tmEval hnf (my_projT2 f_stm) >>=
              tmDefinitionRed_ false (snd kn ++ stream_suffix) (Some hnf) ;;

              tmReturn tms
          | None => tmFail "de Bruijn conversion failed in animate_coinductive"
          end
| None => tmFail "dispatch term extraction failed in animate_coinductive"
end.

(** Collect and merge raw clause data from every kn in [knLst]. *)
Fixpoint collect_all_cdata (knLst : list kername) (modes : mode_map)
  : TemplateMonad (list clause_data) :=
  match knLst with
  | [] => tmReturn []
  | kn :: rest => raw_cdata <- get_data' kn modes ;;
                  rest_cdata <- collect_all_cdata rest modes ;;
                  tmReturn (app raw_cdata rest_cdata)
  end.

(** Collect and merge type environments from every kn in [knLst]. *)
Fixpoint collect_all_tp_data (knLst : list kername)
  : TemplateMonad (list type_env_entry) :=
  match knLst with
  | [] => tmReturn []
  | kn :: rest => mut <- tmQuoteInductive kn ;;
                  rest_tp <- collect_all_tp_data rest ;;
                  tmReturn (app (clause_type_info (ind_bodies mut)) rest_tp)
  end.

(** Like [animate_one_clause] but receives pre-computed, merged [all_cdata] and
    [tp_data] covering every inductive block.  Eliminates the single-[kn]
    re-derivation that caused cross-block predicate references to produce free
    variables in the generated term. *)
Definition animate_one_clause_with_data {A : Type}
  (ind : A) (kn : kername)
  (one_clause : ((string * string) * named_term))
  (modes : mode_map) (fuel : nat)
  (all_cdata : list clause_data)
  (tp_data : list type_env_entry)
  : TemplateMonad term :=
cstr_nm      <- tmEval all (snd (fst one_clause)) ;;
fixpt_data   <- tmEval all (prod_in_out (fixpoint_data all_cdata)) ;;
clause_lhs   <- tmEval all (conj_lhs one_clause) ;;
var_tp       <- tmEval all (all_var_types one_clause tp_data) ;;
inV          <- tmEval all (lookup_var_types (conj_in_vars one_clause modes) var_tp) ;;
outV         <- tmEval all (lookup_var_types (conj_out_vars one_clause modes) var_tp) ;;
pred_tps     <- tmEval all (all_ind_tp_data all_cdata) ;;
pred_tps_an  <- tmEval all (animation_types all_cdata) ;;
pred_tps_occ <- tmEval all (pred_animation_types one_clause fixpt_data pred_tps_an) ;;
compile_clause_body ind kn clause_lhs cstr_nm inV outV modes pred_tps var_tp pred_tps_occ fuel.

(** Like [animate_clause_list] but uses [animate_one_clause_with_data]. *)
Fixpoint animate_clause_list_with_data {A : Type}
  (ind : A) (kn : kername)
  (cl_lst : list ((string * string) * term))
  (modes : mode_map) (fuel : nat)
  (all_cdata : list clause_data)
  (tp_data : list type_env_entry)
  : TemplateMonad (list term) :=
  match cl_lst with
  | [] => tmReturn []
  | c1 :: cRest =>
      c1An    <- animate_one_clause_with_data ind kn c1 modes fuel all_cdata tp_data ;;
      cRestAn <- animate_clause_list_with_data ind kn cRest modes fuel all_cdata tp_data ;;
      tmReturn (c1An :: cRestAn)
  end.

(** Compile all clauses for a list of separately-defined inductive blocks,
    returning the combined fixpoint structure data.

    Phase 1: collect raw data from every block in [knLst], merge the type
    environments, and rewrite all clauses with the unified type info so that
    cross-block predicate argument types are resolved correctly.

    Phase 2: animate every clause using the merged context so that predicates
    from other blocks appear in [pred_tps_an] and the lambda chain for
    [lhs_preds] is built correctly — preventing the free-variable error that
    arose when [pred_tps_occ] was empty for cross-block calls. *)
Definition animate_multi_def {A : Type} (ind : A) (knLst : list kername)
 (modes : mode_map) (fuel : nat) : TemplateMonad (list fixpoint_entry) :=
match knLst with
| [] => tmReturn []
| topKn :: _ =>
  all_cdata_raw    <- collect_all_cdata knLst modes ;;
  tp_data_raw      <- collect_all_tp_data knLst ;;
  all_cdata_merged  <- match rewrite_cl_all all_cdata_raw tp_data_raw with
                       | Some d => tmEval all d
                       | None   => tmFail "clause rewriting failed in animate_multi_def"
                       end ;;
  let tp_data_merged := finalize_type_info all_cdata_raw tp_data_raw in
  let cl_lst         := all_clauses all_cdata_merged in
  animate_clause_list_with_data ind topKn cl_lst modes fuel
    all_cdata_merged tp_data_merged ;;
  tmReturn (prod_in_out (fixpoint_data all_cdata_merged))
end.

(** Compile all clauses across a multi-definition mutual block ([topKn :: knLst]),
    assemble a single mutual fixpoint, and define it as [topKn.AnimatedTopFn]. *)
Definition animate_multi_aux {A : Type} (topInd : A) (topKn : kername) (knLst : list kername)
 (modes : mode_map) (fuel : nat) : TemplateMonad term:=

ind_data'' <- animate_multi_def topInd (topKn :: knLst) modes fuel ;;
ind_data <- tmEval all ind_data'';;

match mk_all_ind ind_data topKn modes with
| Some defs =>
  let u := mk_rec_fn defs 0 in
          u' <- tmEval all u ;;
          match DB.de_bruijn_option u with
          | Some db_u =>
            t' <- tmEval all db_u ;;
               f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false
                (snd topKn ++ top_fn_suffix)
                (Some hnf) ;;
              tmReturn db_u
          | None => tmFail "de Bruijn conversion failed in animate_multi_aux"
          end
| None => tmFail "dispatch term extraction failed in animate_multi_aux"
end.

Set Universe Checking.
