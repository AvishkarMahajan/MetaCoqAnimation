(** * AnimationTypes — Core Data Types for the Animation Pipeline

    Record types and type aliases shared across all animation modules.
    Kept separate from [MetaRocqUtils] because these types describe the
    animation domain (clauses, variables, fixpoints), not MetaRocq plumbing.

    All other animation modules depend on this file indirectly via [MetaRocqUtils]. *)

Require Import MetaRocq.Template.All.
From Stdlib Require Import List.

Open Scope bs.

(** ** Term Representation Aliases

    The animation pipeline distinguishes three uses of [term]:
    - [named_term]: local variables use [tVar id] (named representation).
      Produced by [DB.un_de_bruijn], consumed by substitution and clause manipulation.
    - [global_term]: contains no local variables at all (type constructors, quoted constants).
      Safe to embed in either named or de Bruijn contexts.
    - [term] (unqualified): local variables use [tRel n] (de Bruijn representation).
      Produced by [tmQuote], consumed by [tmUnquote]. *)

Definition named_term : Type := term.
Definition global_term : Type := term.

(** ** Simple Type Aliases

    These three aliases are just [list (string * _)] tables; they are aliases
    rather than records because a single level of [fst]/[snd] is clear enough. *)

(** Maps each predicate name to its (input_positions, output_positions) mode. *)
Definition mode_map := list (string * (list nat * list nat))%type.

(** Maps predicate names to their full argument-type lists. *)
Definition pred_type_map := list (string * list term)%type.

(** Maps variable names to their types in a local clause context. *)
Definition var_type_map := list (string * term)%type.

(** ** Record Types

    Five records that eliminate nested [fst]/[snd] chains throughout the pipeline. *)

(** A conjunct annotated with the output variable it produces.
    Built by [attach_var_to_conj] and consumed by [animate_let_binding] and friends. *)
Record tagged_conjunct := {
  (** The premise (named representation): an equality, predicate application, or guard condition. *)
  tc_conjunct : named_term;
  (** Name of the output variable this conjunct binds. *)
  tc_out_var  : string;
  (** Type of [tc_out_var] (named representation), used to annotate the generated let-binding. *)
  tc_out_type : named_term
}.

(** One constructor argument after unfolding in pattern compilation.
    Produced by [unfold_cons] and consumed by [mk_case'] and [preprocess_type_var]. *)
Record resolved_var := {
  (** Variable name assigned to this argument position. *)
  rv_name  : string;
  (** The constructor or [tVar] this variable was matched against (named representation). *)
  rv_term  : named_term;
  (** Names of the fresh sub-variables bound by this constructor's own arguments. *)
  rv_bound : list string
}.

(** Input/output type information for one inductive relation, extracted from
    the mode specification before constructor bodies are processed. *)
Record in_out_entry := {
  (** Name of the inductive predicate. *)
  ioe_name      : string;
  (** Types of the input arguments (de Bruijn), selected by the mode. *)
  ioe_in_types  : list term;
  (** Types of the output arguments (de Bruijn), selected by the mode. *)
  ioe_out_types : list term
}.

(** All data needed to compile one inductive relation:
    extracted once by [get_data] and threaded through the entire pipeline. *)
Record clause_data := {
  (** Name of the inductive predicate. *)
  cd_ind_name  : string;
  (** Types of the input arguments (de Bruijn), selected by the mode. *)
  cd_in_types  : list term;
  (** Types of the output arguments (de Bruijn), selected by the mode. *)
  cd_out_types : list term;
  (** Constructor clauses as [(constructor_name, clause_body)] pairs (named representation). *)
  cd_clauses   : list (string * named_term)
}.

(** Type information for one inductive predicate:
    built by [cstr_type_data] and used to rewrite clauses and look up variable types. *)
Record type_env_entry := {
  (** Name of the inductive predicate. *)
  te_pred_name : string;
  (** Full type of the predicate (de Bruijn), used to extract its argument types. *)
  te_pred_type : term;
  (** Per-constructor variable environments: [(cstr_name, [(var_name, var_type)])].
      Types are de Bruijn. *)
  te_cstr_vars : list (string * list (string * term))
}.

(** One arm of the generated mutual fixpoint:
    produced by [prod_in_out] and consumed by [mk_all_fixpoints]. *)
Record fixpoint_entry := {
  (** Name of the inductive predicate this fixpoint arm implements. *)
  fe_ind_name   : string;
  (** Right-nested product type of all input arguments (global — no local variables). *)
  fe_in_type    : global_term;
  (** Right-nested product type of all output arguments (global — no local variables). *)
  fe_out_type   : global_term;
  (** Per-constructor lists of recursive predicate calls: [(cstr_name, [pred_name])]. *)
  fe_cstr_preds : list (string * list string)
}.
