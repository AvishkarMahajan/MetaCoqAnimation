(** * TermUtils — Quoted-Term Builders, Mode Lookups, and Sentinels

    Utilities for constructing quoted MetaRocq terms, looking up modes,
    building join and lambda chains, and sentinel/suffix constants used
    throughout the animation pipeline. *)

Require Import Animation.AnimationTypes.
Require Import Animation.AnimationResult.
Require Import MetaRocq.Template.All.
From Stdlib Require Import List PeanoNat.
Import monad_utils.MRMonadNotation
       ListNotations.

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

(** Build a product type from a list of output variable specs.
    Returns bool for empty list, single type for singleton, nested products otherwise. *)
Fixpoint tele_to_prod_tp (out_data : list (string * term)) : term :=
  match out_data with
  | [] => <%bool%>
  | [h] => snd h
  | h :: t =>
    let res := tele_to_prod_tp t in
    tApp <%prod%> [snd h; res]
  end.

(** Build a product term from a list of output variables.
    Constructs nested pairs of variables. *)
Fixpoint tele_to_prod_tm (out_data : list (string * term)) : named_term :=
  match out_data with
  | [] => <%true%>
  | [h] => tVar (fst h)
  | h :: t =>
    let res := tele_to_prod_tm t in
    let resT := tele_to_prod_tp t in
    tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
         [snd h; resT; tVar (fst h); res]
  end.

(** Build the product type of a non-empty list of [(term, type)] pairs.
    Fails if the list is empty; returns a single type for singletons. *)
Fixpoint mk_lhs_type (lhs_preds : list (term * term)) : TemplateMonad term :=
  match lhs_preds with
  | [] => tmFail "no predicates on LHS0"
  | [h] => tmReturn (snd h)
  | h :: t =>
      res <- mk_lhs_type t ;;
      tmReturn (tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; res])
  end.

(** Build the product term of a non-empty list of [(term, type)] pairs.
    Companion to [mk_lhs_type]; fails on empty input. *)
Fixpoint mk_lhs_term (lhs_preds : list (term * term)) : TemplateMonad term :=
  match lhs_preds with
  | [] => tmFail "no predicates on LHS1"
  | [h] => tmReturn (fst h)
  | h :: t =>
      res <- mk_lhs_term t ;;
      resT <- mk_lhs_type t ;;
      tmReturn (tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
                     [snd h; resT; fst h; res])
  end.

(** Test whether string [s] occurs in list [l]. *)
Definition in_strings (s : string) (l : list string) : bool :=
  existsb (String.eqb s) l.

(** Test whether every element of string list [l1] occurs in [l2]. *)
Definition is_subset_strings (l1 l2 : list string) : bool :=
  forallb (fun s => existsb (String.eqb s) l2) l1.

(** Return [true] iff [lst] is empty. *)
Definition is_nil {A : Type} (lst : list A) : bool :=
  match lst with
  | [] => true
  | _ => false
  end.

(** Build a quoted [list term] literal from [lst], with element type [elem_tp]. *)
Fixpoint build_coq_list (lst : list global_term) (elem_tp : global_term) : global_term :=
  match lst with
  | [] => tApp
           (tConstruct
              {|
                inductive_mind := <?list?>; inductive_ind := 0
              |} 0 []) [elem_tp]
  | h :: t =>  tApp
               (tConstruct
               {| inductive_mind := <?list?>; inductive_ind := 0 |} 1 [])
               [elem_tp; h; build_coq_list t elem_tp]
  end.

(** Dispatch mechanism: try each function in the list until one returns Some.
    Returns None if all functions return None. *)
Fixpoint dispatch_clauses (inT : Type) (outT : Type)
                            (fns : list (inT -> option outT)) : inT -> option outT :=
 fun x => match fns with
           | [] => None
           | h :: t => let r := h x in
                       match r with
                       | None => dispatch_clauses inT outT t x
                       | _ => r
                       end
          end .

(** Provide a default value for an option-returning function. *)
Definition with_default (in_tp out_tp : Type)
  (default : out_tp)
  (f : in_tp -> option out_tp)
  : in_tp -> out_tp :=
  fun x =>
    match f x with
    | Some y => y
    | None => default
    end.

(** Quote each element of [l] into a MetaRocq term using [tmQuote]. *)
Fixpoint quote_list {A : Type} (l : list A) : TemplateMonad (list term) :=
  match l with
  | [] => ret []
  | h :: rest =>
      t <- tmQuote h ;;
      l' <- quote_list rest ;;
      tmReturn (t :: l')
  end.

(** Extract variable names from a flat list of terms (non-[tVar] terms are dropped). *)
Fixpoint ordered_vars_aux (ls : list named_term) : list string :=
  match ls with
  | [] => []
  | tVar str :: t => str :: ordered_vars_aux t
  | _ :: t => ordered_vars_aux t
  end.

(** Extract variable names from a term in declaration order.
    For equality terms, lists known-side variables before unknown-side variables. *)
Fixpoint ordered_vars (t : named_term) : list string :=
  match t with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => [str1 ; str2]
  | tApp <%eq%> [typeT; tVar str1; tApp fn lst] => str1 :: ordered_vars_aux lst
  | tApp <%eq%> [typeT; tApp fn lst; tVar str1] => app (ordered_vars_aux lst) [str1]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] => [str1]
  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>  [str1]

  | tVar str  => [str]
  | tApp _ lst => flat_map ordered_vars lst
  | _ => []
  end.

(** Apply [ordered_vars] to each element of [l] and concatenate the results. *)
Definition ordered_vars_of_list : list named_term -> list string :=
  flat_map ordered_vars.

(** Return a singleton list containing element [ind] of [l], or [[]] if out of bounds. *)
Fixpoint select_from_index {A : Type} (ind : nat) (l : list A) : list A :=
  match ind with
  | 0 => match l with
     | h :: t => [h]
     | [] => []
     end
  | S m => select_from_index m (tl l)
  end.

(** Select elements at positions [indLst] from list [l]. *)
Fixpoint select_by_indices {A : Type} (indLst : list nat) (l : list A) : list A :=
  match indLst with
  | [] => []
  | h :: t => select_from_index h l ++ select_by_indices t l
  end.

(** Select the input arguments of predicate [ind_nm] from [lstArgs] according to its mode. *)
Fixpoint select_in_args (ind_nm : string) (modes : mode_map) (lstArgs : list term) : list term :=
  match modes with
  | [] => []
  | h :: t =>
    if String.eqb ind_nm (fst h)
    then select_by_indices (fst (snd h)) lstArgs
    else select_in_args ind_nm t lstArgs
  end.

(** Select the output arguments of predicate [ind_nm]
    from [lstArgs] according to its mode. *)
Fixpoint select_out_args (ind_nm : string)
  (modes : mode_map) (lstArgs : list term)
  : list term :=
  match modes with
  | [] => []
  | h :: t =>
    if String.eqb ind_nm (fst h)
    then select_by_indices (snd (snd h)) lstArgs
    else select_out_args ind_nm t lstArgs
  end.

Fixpoint lookup_one_var (var_nm : string)
  (var_env : list (prod string term))
  : list (prod string term) :=
  match var_env with
  | [] => []
  | h :: t => if String.eqb var_nm (fst h) then [h] else lookup_one_var var_nm t
  end.

(** Convert a [(variable_name, type)] list to a [(tVar name, type)] list. *)
Definition pairs_to_terms (lst : list (prod string term)) : list (prod named_term term) :=
  map (fun '(str, tp) => (tVar str, tp)) lst.

(** Look up each variable name in [lst] in the type environment, dropping missing entries. *)
Fixpoint lookup_vars (lst : list string)
  (var_env : list (prod string term))
  : list (prod string term) :=
  match lst with
  | [] => []
  | h :: t => match lookup_one_var h var_env with
             | [h'] => h' :: lookup_vars t var_env
             | _ =>  lookup_vars t var_env
            end
  end.

(** Look up the mode (input-position list, output-position list) for [ind_nm],
    returning ([],[]) if not found. *)
Fixpoint lookup_mode (ind_nm : string) (modes : mode_map) : list nat * list nat :=
  match modes with
  | [] => ([],[])
  | h :: t => if String.eqb ind_nm (fst h) then (snd h) else lookup_mode ind_nm t
  end.

(** Select the input arguments from [lstArgs] using a pre-looked-up [mode] pair. *)
Definition select_in_by_mode (mode : list nat * list nat) (lstArgs : list term) : list term :=
select_by_indices (fst mode) lstArgs.

(** Select the output arguments from [lstArgs] using a pre-looked-up [mode] pair. *)
Definition select_out_by_mode (mode : list nat * list nat) (lstArgs : list term) : list term :=
select_by_indices (snd mode) lstArgs.

(** Look up the argument types for predicate [ind_nm] in a type-info table. *)
Fixpoint lookup_pred_type (ind_nm : string) (pred_types : pred_type_map) : list term :=
  match pred_types with
  | [] => []
  | h :: t => if String.eqb ind_nm (fst h) then snd h else lookup_pred_type ind_nm t
  end.

(** Build the right-nested product type of a list of types, using [bool] as the
    empty-list base case. *)
Fixpoint nested_prod_type (types : list term) : global_term :=
  match types with
  | [] => <%bool%>
  | [h] => h
  | h :: t => tApp <%prod%> [h; nested_prod_type t]
  end.

(** Build the body of a join function for [types]: folds [join_pair] over
    variables named "o0", "o1", …, starting at index [n]. *)
Fixpoint mk_join_body (types : list term) (n : nat) : named_term :=
  match types with
  | [] => <%Success bool true%>
  | [h] => tApp <%join_unit%> [h; tVar ("o" ++ string_of_nat n)]
  | [h ; h1] =>
    tApp <%join_pair%>
      [h; h1;
       tVar ("o" ++ string_of_nat n);
       tVar ("o" ++ string_of_nat (S n))]
  | h :: t =>
    tApp <%join_pair%>
      [h; nested_prod_type t;
       tVar ("o" ++ string_of_nat n);
       mk_join_body t (S n)]
  end.

(** Wrap [body] in lambdas "o0 : animation_result T0",
    "o1 : ...", etc. for each type in [types]. *)
Fixpoint mk_join_lam (types : list term)
  (n : nat) (body : term) : named_term :=
  match types with
  | [] => body
  | [h] =>
    tLam ("o" ++ string_of_nat n)
      (tApp <%animation_result%> [h]) body
  | h :: t =>
    tLam ("o" ++ string_of_nat n)
      (tApp <%animation_result%> [h])
      (mk_join_lam t (S n) body)
  end.

(** Build a quoted function that joins multiple [animation_result] values into one
    product result, combining [mk_join_body] and [mk_join_lam]. *)
Definition mk_join_tm (types : list term) : named_term :=
let body := mk_join_body types 0 in
mk_join_lam types 0 body.

(** Build a quoted term [eq_outcome tpTm tp_eq_fn]: the equality function on
    [animation_result tpTm] using the boolean equality [tp_eq_fn] on the base type. *)
Definition mk_eq_outcome_tm (tpTm tp_eq_fn : global_term)
  : global_term :=
  tApp <%eq_outcome%> [tpTm; tp_eq_fn].

(** Build a quoted term that joins the [animation_result] values of all output
    variables [out_vars] into a single product result using [mk_join_tm]. *)
Definition mk_output_prod_tm (out_vars : list (prod string term)) : named_term :=
tApp (mk_join_tm (map snd out_vars)) (map (fun e => tVar (fst e)) out_vars).

(** Wrap [body] in a sequence of lambda abstractions, one for each [(name, type)]
    pair in [in_vars], building innermost-first. *)
Fixpoint mk_lam_chain (in_vars : list (prod string term)) (body : term) : term :=
  match in_vars with
  | [] => body
  | h :: t => tLam (fst h) (snd h) (mk_lam_chain t body)
  end.

(** String constants for generated definition names. *)
Definition top_fn_suffix : string := "AnimatedTopFn".
Definition stream_suffix : string := "AnimatedTopFnStream".
Definition anim_suffix : string := "Animated".

(** Append [top_fn_suffix] to every function name in the [(name, type)] list,
    producing the names used for the generated animated definitions. *)
Definition mk_animated_names (l : list (string * term)) : list (string * term) :=
  map (fun '(s, tp) => (s ++ top_fn_suffix, tp)) l.
