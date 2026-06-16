(** * MetaRocqUtils — Core MetaRocq Utilities

    Foundational utilities shared by the entire animation pipeline:
    notation macros, De Bruijn conversion, term substitution, type-level
    helpers ([animation_result], [ind_tp], sentinels), and term-construction
    combinators ([pairs_to_terms], [tele_to_prod_tp], [compose_outcome], …).

    All other animation modules depend on this file. *)

Require Import MetaRocq.Template.All.
From Stdlib Require Import List PeanoNat.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.

Module MetaRocqNotations.
  (* Recursive quoting *)
  Notation "<%% x %%>" :=
    ((ltac:(let p y := exact y in run_template_program (tmQuoteRec x) p)))
    (only parsing).
  (* Check <%% nat %%>. *)

  (* Splicing / top level antiquotation *)
  Notation "~( x )" :=
    (ltac:(let p y :=
              let e := eval unfold my_projT2 in (my_projT2 y) in
              exact e in
          run_template_program (tmUnquote x) p))
    (only parsing).
  (* Check (~( <% fun (x : bool) => if x then false else true  %>)). *)
  (* Compute (~(<% fun (x : bool) => if x then false else true %>) false). *)

  (* Name resolution *)
  Notation "<? x ?>" :=
    (ltac:(let p y :=
              match y with
              | tInd {| inductive_mind := ?name |} _ =>
                exact name
              | tConst ?name _ =>
                exact name
              | _ => fail "not a type constructor or definition name" end in
          run_template_program (tmQuote x) p))
    (only parsing).
  (* Compute <? option ?>. *)
End MetaRocqNotations.

Local Open Scope nat_scope.

(* Warning: MetaRocq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MRMonadNotation
       ListNotations
       MetaRocqNotations.

(** Alias for [term] values that use named variables rather than de Bruijn indices. *)
Definition named_term : Type := term.
(** Alias for [term] values that contain no local variables, safe to embed in
    either named or de Bruijn contexts. *)
Definition global_term : Type := term.

(** Decision procedure for identifier equality, returning a [bool]. *)
Definition ident_eq (x y : ident) : bool :=
  match compare_ident x y with
  | Eq => true
  | _ => false
  end.

(** ** De Bruijn Conversion

    Utilities for converting between named-variable and de Bruijn representations.
    Inspired by code written by John Li. *)
Module DB.
  (** Convert a named-variable term to de Bruijn representation given an outer
      context [ctx].  Free variables (not in [ctx]) are left as [tVar]. *)
  Definition de_bruijn' (ctx : list name) (t : named_term) : TemplateMonad term :=
    let fix find_in_ctx (count : nat) (id : ident) (ctx : list name) : option nat :=
      match ctx with
      | nil => None
      | nAnon :: ns => find_in_ctx (S count) id ns
      | (nNamed id') :: ns =>
        if ident_eq id id' then Some count else find_in_ctx (S count) id ns
      end in
    let fix go (ctx : list name) (t : named_term) : TemplateMonad term :=
        let go_mfix (mf : mfixpoint named_term) : TemplateMonad (mfixpoint term) :=
          let ctx' := map (fun x => binder_name (dname x)) mf in
          monad_map (fun def =>
                       dtype' <- go ctx def.(dtype) ;;
                       dbody' <- go (rev ctx' ++ ctx) def.(dbody) ;;
                       ret (mkdef _ def.(dname) dtype' dbody' def.(rarg))) mf in
        let go_branches (branches : list (branch named_term))
                        : TemplateMonad (list (branch term)):=
          monad_map (fun br =>
              t' <- go (map binder_name (bcontext br) ++ ctx) (bbody br) ;;
              ret {| bcontext := bcontext br; bbody := t' |}) branches in
        match t with
        | tRel n => ret t
        | tVar id =>
            match find_in_ctx O id ctx with
            | Some i => ret (tRel i)
            | None => ret t (* could be a free variable *)
            end
        | tEvar ev args =>
            args' <- monad_map (go ctx) args ;;
            ret (tEvar ev args')
        | tSort s =>
          ret t
        | tCast t kind v =>
            t' <- go ctx t ;;
            v' <- go ctx v ;;
            ret (tCast t' kind v')
        | tProd na ty body =>
            ty' <- go ctx ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            ret (tProd na ty' body')
        | tLambda na ty body =>
            ty' <- go ctx ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            ret (tLambda na ty' body')
        | tLetIn na def def_ty body =>
            def' <- go ctx def ;;
            def_ty' <- go ctx def_ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            ret (tLetIn na def' def_ty' body')
        | tApp f args =>
            f' <- go ctx f ;;
            args' <- monad_map (go ctx) args ;;
            ret (tApp f' args')
        | tConst c u => ret t
        | tInd ind u => ret t
        | tConstruct ind idx u => ret t
        | tCase ind_nbparams_relevance type_info discr branches =>
            preturn' <- go ctx (preturn type_info) ;;
            pparams' <- monad_map (go ctx) (pparams type_info) ;;
            let type_info' :=
              {| puinst := puinst type_info
               ; pparams := pparams'
               ; pcontext := pcontext type_info
               ; preturn := preturn'
               |} in
            discr' <- go ctx discr ;;
            branches' <- go_branches branches ;;
            ret (tCase ind_nbparams_relevance type_info' discr' branches')
        | tProj proj t =>
            t' <- go ctx t ;;
            ret (tProj proj t')
        | tFix mfix idx =>
            mfix' <- go_mfix mfix ;;
            ret (tFix mfix' idx)
        | tCoFix mfix idx =>
            mfix' <- go_mfix mfix ;;
            ret (tCoFix mfix' idx)
        | tInt p => ret (tInt p)
        | tFloat p => ret (tFloat p)
        | tArray u arr default type =>
             arr' <- monad_map (go ctx) arr ;;
             default' <- go ctx default ;;
             type' <- go ctx type ;;
             ret (tArray u arr' default' type')
        | tString s => ret (tString s)
        end
    in go ctx t.

  (** Convert a named-variable term to de Bruijn representation with no outer context. *)
  Definition de_bruijn (t : named_term) : TemplateMonad term := de_bruijn' nil t.

  (** Pure (non-monadic) variant of [de_bruijn']; returns [None] on failure. *)
Definition named_to_debruijn (ctx : list name) (t : named_term) : option term :=
    let fix find_in_ctx (count : nat) (id : ident) (ctx : list name) : option nat :=
      match ctx with
      | nil => None
      | nAnon :: ns => find_in_ctx (S count) id ns
      | (nNamed id') :: ns =>
        if ident_eq id id' then Some count else find_in_ctx (S count) id ns
      end in
    let fix go (ctx : list name) (t : named_term) : option term :=
        let go_mfix (mf : mfixpoint named_term) : option (mfixpoint term) :=
          let ctx' := map (fun x => binder_name (dname x)) mf in
          monad_map (fun def =>
                       dtype' <- go ctx def.(dtype) ;;
                       dbody' <- go (rev ctx' ++ ctx) def.(dbody) ;;
                       Some (mkdef _ def.(dname) dtype' dbody' def.(rarg))) mf in
        let go_branches (branches : list (branch named_term))
                        : option (list (branch term)):=
          monad_map (fun br =>
              t' <- go (map binder_name (bcontext br) ++ ctx) (bbody br) ;;
              Some {| bcontext := bcontext br; bbody := t' |}) branches in
        match t with
        | tRel n => Some t
        | tVar id =>
            match find_in_ctx O id ctx with
            | Some i => Some (tRel i)
            | None => Some t (* could be a free variable *)
            end
        | tEvar ev args =>
            args' <- monad_map (go ctx) args ;;
            Some (tEvar ev args')
        | tSort s =>
          Some t
        | tCast t kind v =>
            t' <- go ctx t ;;
            v' <- go ctx v ;;
            Some (tCast t' kind v')
        | tProd na ty body =>
            ty' <- go ctx ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            Some (tProd na ty' body')
        | tLambda na ty body =>
            ty' <- go ctx ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            Some (tLambda na ty' body')
        | tLetIn na def def_ty body =>
            def' <- go ctx def ;;
            def_ty' <- go ctx def_ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            Some (tLetIn na def' def_ty' body')
        | tApp f args =>
            f' <- go ctx f ;;
            args' <- monad_map (go ctx) args ;;
            Some (tApp f' args')
        | tConst c u => Some t
        | tInd ind u => Some t
        | tConstruct ind idx u => Some t
        | tCase ind_nbparams_relevance type_info discr branches =>
            preturn' <- go ctx (preturn type_info) ;;
            pparams' <- monad_map (go ctx) (pparams type_info) ;;
            let type_info' :=
              {| puinst := puinst type_info
               ; pparams := pparams'
               ; pcontext := pcontext type_info
               ; preturn := preturn'
               |} in
            discr' <- go ctx discr ;;
            branches' <- go_branches branches ;;
            Some (tCase ind_nbparams_relevance type_info' discr' branches')
        | tProj proj t =>
            t' <- go ctx t ;;
            Some (tProj proj t')
        | tFix mfix idx =>
            mfix' <- go_mfix mfix ;;
            Some (tFix mfix' idx)
        | tCoFix mfix idx =>
            mfix' <- go_mfix mfix ;;
            Some (tCoFix mfix' idx)
        | tInt p => Some (tInt p)
        | tFloat p => Some (tFloat p)
        | tArray u arr default type =>
             arr' <- monad_map (go ctx) arr ;;
             default' <- go ctx default ;;
             type' <- go ctx type ;;
             Some (tArray u arr' default' type')
        | tString s => Some (tString s)
        end
    in go ctx t.

  (** Pure variant of [de_bruijn] with no outer context. *)
  Definition de_bruijn_option (t : named_term) : option term := named_to_debruijn nil t.

  (** Convert a de Bruijn term back to named representation given context [ctx]:
      replaces [tRel n] with [tVar id] where [ctx !! n = nNamed id]. *)
  Definition un_de_bruijn' (ctx : list name) (t : term) : TemplateMonad named_term :=
    let fix go (ctx : list name) (t : term) : TemplateMonad named_term :=
        let go_mfix (mf : mfixpoint term) : TemplateMonad (mfixpoint named_term) :=
          let ctx' := map (fun x => binder_name (dname x)) mf in
          monad_map (fun def =>
                       dtype' <- go ctx def.(dtype) ;;
                       dbody' <- go (rev ctx' ++ ctx) def.(dbody) ;;
                       ret (mkdef _ def.(dname) dtype' dbody' def.(rarg))) mf in
        let go_branches (branches : list (branch term))
                        : TemplateMonad (list (branch named_term)):=
          monad_map (fun br =>
              t' <- go (map binder_name (bcontext br) ++ ctx) (bbody br) ;;
              ret {| bcontext := bcontext br; bbody := t' |}) branches in
        match t with
        | tRel n =>
            match nth_error ctx n with
            | None => ret t
            | Some nAnon => tmFail "Reference to anonymous binding"%bs
            | Some (nNamed id) => ret (tVar id)
            end
        | tVar id => ret t
        | tEvar ev args =>
            args' <- monad_map (go ctx) args ;;
            ret (tEvar ev args')
        | tSort s =>
          ret t
        | tCast t kind v =>
            t' <- go ctx t ;;
            v' <- go ctx v ;;
            ret (tCast t' kind v')
        | tProd na ty body =>
            ty' <- go ctx ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            ret (tProd na ty' body')
        | tLambda na ty body =>
            ty' <- go ctx ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            ret (tLambda na ty' body')
        | tLetIn na def def_ty body =>
            def' <- go ctx def ;;
            def_ty' <- go ctx def_ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            ret (tLetIn na def' def_ty' body')
        | tApp f args =>
            f' <- go ctx f ;;
            args' <- monad_map (go ctx) args ;;
            ret (tApp f' args')
        | tConst c u => ret t
        | tInd ind u => ret t
        | tConstruct ind idx u => ret t
        | tCase ind_nbparams_relevance type_info discr branches =>
            preturn' <- go ctx (preturn type_info) ;;
            pparams' <- monad_map (go ctx) (pparams type_info) ;;
            let type_info' :=
              {| puinst := puinst type_info
               ; pparams := pparams'
               ; pcontext := pcontext type_info
               ; preturn := preturn'
               |} in
            discr' <- go ctx discr ;;
            branches' <- go_branches branches ;;
            ret (tCase ind_nbparams_relevance type_info' discr' branches')
        | tProj proj t =>
            t' <- go ctx t ;;
            ret (tProj proj t')
        | tFix mfix idx =>
            mfix' <- go_mfix mfix ;;
            ret (tFix mfix' idx)
        | tCoFix mfix idx =>
            mfix' <- go_mfix mfix ;;
            ret (tCoFix mfix' idx)
        | tInt p => ret (tInt p)
        | tFloat p => ret (tFloat p)
        | tArray u arr default type =>
             arr' <- monad_map (go ctx) arr ;;
             default' <- go ctx default ;;
             type' <- go ctx type ;;
             ret (tArray u arr' default' type')
        | tString s => ret (tString s)
        end
    in go ctx t.

  (** Convert a de Bruijn term to named representation with no outer context. *)
  Definition un_de_bruijn (t : term) : TemplateMonad named_term :=
    un_de_bruijn' nil t.

  (* Example usage for de_bruijn:

   MetaRocq Run (t <- DB.de_bruijn
                      (tLambda (mkBindAnn (nNamed "x") Relevant)
                                <% bool %> (tVar "x"))%string ;;
                t' <- tmUnquoteTyped (bool -> bool) t ;;
                tmPrint t).
  *)

  (* Example usage for un_de_bruijn:

   MetaRocq Run (t <- DB.un_de_bruijn <% fun (x : bool) => x %> ;;
                tmPrint t).
  *)

  (* Round trip test:

  MetaRocq Run (t <- DB.un_de_bruijn
                      <% fix f (x y : nat) :=
                           match x with S x' => f x' (S y) | O => y end %> ;;
               t <- DB.de_bruijn t ;;
               t' <- tmUnquoteTyped (nat -> nat -> nat) t ;;
               tmPrint t').
  *)

End DB.

(** ** Named-Variable Substitution

    Capturing substitution for [named_term].  Only safe when [t] is a
    [global_term] with no free local variables. *)
Module Substitution.
  (** Substitute [t] for all free occurrences of identifier [x] in [u].
      Stops substituting under binders that shadow [x]. *)
  Fixpoint named_subst (t : global_term) (x : ident) (u : named_term) {struct u} : named_term :=
    match u with
    | tVar id => if ident_eq id x then t else u
    | tEvar ev args => tEvar ev (map (named_subst t x) args)
    | tCast c kind ty => tCast (named_subst t x c) kind (named_subst t x ty)
    | tProd (mkBindAnn (nNamed id) rel) A B =>
      if ident_eq x id
      then tProd (mkBindAnn (nNamed id) rel) (named_subst t x A) B
      else tProd (mkBindAnn (nNamed id) rel) (named_subst t x A) (named_subst t x B)
    | tProd na A B => tProd na (named_subst t x A) (named_subst t x B)
    | tLambda (mkBindAnn (nNamed id) rel) T M =>
      if ident_eq x id
      then tLambda (mkBindAnn (nNamed id) rel) (named_subst t x T) M
      else tLambda (mkBindAnn (nNamed id) rel) (named_subst t x T) (named_subst t x M)
    | tLambda na T M => tLambda na (named_subst t x T) (named_subst t x M)
    | tLetIn (mkBindAnn (nNamed id) rel) b ty b' =>
      if ident_eq x id
      then tLetIn (mkBindAnn (nNamed id) rel) (named_subst t x b) (named_subst t x ty) b'
      else
        tLetIn (mkBindAnn (nNamed id) rel)
          (named_subst t x b)
          (named_subst t x ty)
          (named_subst t x b')
    | tLetIn na b ty b' =>
      tLetIn na (named_subst t x b)
        (named_subst t x ty) (named_subst t x b')
    | tApp u0 v =>
      mkApps (named_subst t x u0) (map (named_subst t x) v)
    | tCase ind p c brs =>
        let p' :=
          {| puinst := puinst p
           ; pparams := map (named_subst t x) (pparams p)
           ; pcontext := pcontext p
           ; preturn := named_subst t x (preturn p)
           |} in
        let brs' :=
          map (fun br =>
            {| bcontext := bcontext br
             ; bbody := named_subst t x (bbody br)
             |}) brs in
        tCase ind p' (named_subst t x c) brs'
    | tProj p c => tProj p (named_subst t x c)
    | tFix mfix idx =>
      let mfix' :=
        map (map_def (named_subst t x) (named_subst t x)) mfix
      in tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' :=
        map (map_def (named_subst t x) (named_subst t x)) mfix
      in tCoFix mfix' idx
    | _ => u
    end.

  Fixpoint named_subst_all
    (l : list (ident * named_term))
    (u : named_term) : named_term :=
    match l with
    | nil => u
    | (id, t) :: l' => named_subst_all l' (named_subst t id u)
    end.
End Substitution.

Module ConstSubstitution.
  Fixpoint named_subst (t : global_term) (x : kername)
    (u : named_term) {struct u} : named_term :=
    match u with
    | tConst kn _ => if eq_kername x kn then t else u
    | tVar id => u
    | tEvar ev args =>
      tEvar ev (map (named_subst t x) args)
    | tCast c kind ty =>
      tCast (named_subst t x c) kind (named_subst t x ty)
    | tProd (mkBindAnn (nNamed id) rel) A B =>
      tProd (mkBindAnn (nNamed id) rel)
        (named_subst t x A) (named_subst t x B)
    | tProd na A B =>
      tProd na (named_subst t x A) (named_subst t x B)
    | tLambda (mkBindAnn (nNamed id) rel) T M =>
      tLambda (mkBindAnn (nNamed id) rel)
        (named_subst t x T) (named_subst t x M)
    | tLambda na T M =>
      tLambda na (named_subst t x T) (named_subst t x M)
    | tLetIn (mkBindAnn (nNamed id) rel) b ty b' =>
      tLetIn (mkBindAnn (nNamed id) rel)
        (named_subst t x b)
        (named_subst t x ty)
        (named_subst t x b')
    | tLetIn na b ty b' =>
      tLetIn na (named_subst t x b)
        (named_subst t x ty) (named_subst t x b')
    | tApp u0 v =>
      mkApps (named_subst t x u0) (map (named_subst t x) v)
    | tCase ind p c brs =>
        let p' :=
          {| puinst := puinst p
           ; pparams := map (named_subst t x) (pparams p)
           ; pcontext := pcontext p
           ; preturn := named_subst t x (preturn p)
           |} in
        let brs' :=
          map (fun br =>
            {| bcontext := bcontext br
             ; bbody := named_subst t x (bbody br)
             |}) brs in
        tCase ind p' (named_subst t x c) brs'
    | tProj p c => tProj p (named_subst t x c)
    | tFix mfix idx => (* FIXME *)
      let mfix' := map (map_def (named_subst t x) (named_subst t x)) mfix in
      tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := map (map_def (named_subst t x) (named_subst t x)) mfix in
      tCoFix mfix' idx
    | _ => u
    end.

  (** Apply a list of [(kername, replacement)] substitutions to [u] in order. *)
  Fixpoint named_subst_all (l : list (kername * named_term)) (u : named_term) : named_term :=
    match l with
    | nil => u
    | (id, t) :: l' => named_subst_all l' (named_subst t id u)
    end.
End ConstSubstitution.

(** Result type for animated functions: success with a value,
    fuel exhaustion, or no matching clause. *)
Inductive animation_result (A : Type) : Type :=
| FuelError : animation_result A
| Success : A -> animation_result A
| NoMatch : animation_result A.

(** Wrapper type that marks a value as coming from an inductive definition.
    Used to distinguish inductive values in animation result types. *)
Inductive ind_tp (A : Type) : Type :=
| indWrap : A -> ind_tp A.

(** ** Type Aliases and Records for Common Data Shapes *)

(** Mode specification: maps each predicate name to its
    (input_positions, output_positions). *)
Definition mode_map :=
  list (string * (list nat * list nat))%type.

(** Maps predicate names to their argument type lists. *)
Definition pred_type_map := list (string * list term)%type.

(** Maps variable names to their types. *)
Definition var_type_map := list (string * term)%type.

(** Per-inductive clause data: [(name, in_types, out_types, constructors)].
    Transparent alias for the nested tuple used throughout the pipeline. *)
Definition clause_data :=
  (((string * list term) * list term) * list (string * term))%type.

(** Per-inductive type environment entry:
    [(pred_name, pred_type, [(cstr_name, [(var_name, var_type)])])]. *)
Definition type_env_entry :=
  ((string * term) * list (string * list (string * term)))%type.

(** Per-inductive fixpoint entry after [prod_in_out]:
    [(name, in_type, out_type, [(cstr_name, [pred_names])])]. *)
Definition fixpoint_entry :=
  (((string * term) * term) * list (string * list string))%type.

(** Build a product type from a list of output variable specs.
    Returns bool for empty list, single type for singleton, nested products otherwise. *)
Fixpoint tele_to_prod_tp (outputData : list (string * term)) :  term :=
  match outputData with
  | [] => <%bool%>
  | [h] =>  (snd h)
  | h :: t => let res := tele_to_prod_tp t in  (tApp
                                            (tInd
                                             {|
                                             inductive_mind := <?prod?>; inductive_ind := 0
                                              |} []) [(snd h) ; res])
  end.

(** Build a product term from a list of output variables.
    Constructs nested pairs of variables. *)
Fixpoint tele_to_prod_tm  (outputData : list (string * term )) : term :=
  match outputData with
  | [] => <%true%>
  | [h] => (tVar (fst h))
  | h :: t => let res := tele_to_prod_tm t in
                                        let resT := tele_to_prod_tp t in (tApp (tConstruct
                                                  {|
                                                   inductive_mind := <?prod?>; inductive_ind := 0
                                                   |} 0 []) [(snd h); resT ; (tVar (fst h)) ; res])
  end.

(** Kleisli composition for animated functions: run [f] on the input, then feed
    its [Success] result into [f'], propagating [FuelError] and [NoMatch]. *)
Definition compose_outcome
  (A B C : Type)
  (f : nat -> animation_result A -> animation_result B)
  (f' : nat -> animation_result B -> animation_result C)
  : nat -> animation_result A -> animation_result C :=
  fun fuel input =>
    match f fuel input with
    | Success res => f' fuel (Success B res)
    | FuelError => FuelError C
    | _ => NoMatch C
    end.

Open Scope bs.

(** Build the product type of a non-empty list of [(term, type)] pairs.
    Fails if the list is empty; returns a single type for singletons. *)
Fixpoint mk_lhs_type (lhsIndPre : list (term * term)) : TemplateMonad term :=
  match lhsIndPre with
  | [] => tmFail "no predicates on LHS0"
  | [h] => tmReturn (snd h)
  | h :: t =>
      res <- mk_lhs_type t ;;
      tmReturn (tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; res])
  end.

(** Build the product term of a non-empty list of [(term, type)] pairs.
    Companion to [mk_lhs_type]; fails on empty input. *)
Fixpoint mk_lhs_term (lhsIndPre : list (term * term)) : TemplateMonad term :=
  match lhsIndPre with
  | [] => tmFail "no predicates on LHS1"
  | [h] => tmReturn (fst h)
  | h :: t =>
      res <- mk_lhs_term t ;;
      resT <- mk_lhs_type t ;;
      tmReturn (tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
                     [snd h; resT; fst h; res])
  end.

(** Constant function that always returns fuel error.
    Used as a fallback when fuel is exhausted. *)
Definition fuel_error_fn (inputType : Type)
  (outputType' : Type)
  : inputType -> animation_result outputType' :=
  fun x : inputType => FuelError outputType'.

(** Test whether string [s] occurs in list [l]. *)
Definition in_strings (s : string) (l : list string) : bool :=
  existsb (String.eqb s) l.

(** Test whether every element of string list [l1] occurs in [l2]. *)
Definition is_subset_strings (l1 l2 : list string) : bool :=
  forallb (fun s => existsb (String.eqb s) l2) l1.


(** Adapt a function returning [animation_result (option B)] into one returning
    [animation_result B]: [Some v] becomes [Success v], [None] becomes [NoMatch]. *)
Definition option_to_result (A B : Type)
  (f : nat -> animation_result A ->
       animation_result (option B))
  : nat -> animation_result A -> animation_result B :=
  fun k k' =>
    match f k k' with
    | Success (Some res) => Success B res
    | Success None => NoMatch B
    | FuelError => FuelError B
    | _ => NoMatch B
    end.

(** Return [true] iff [lst] is empty. *)
Definition is_nil {A : Type} (lst : list A) : bool :=
  match lst with
  | [] => true
  | _ => false
  end.

(** Build a quoted [list term] literal from [lst], with element type [typeofTm]. *)
Fixpoint build_coq_list (lst : list term) (typeofTm : term) : term :=
  match lst with
  | [] => tApp
           (tConstruct
              {|
                inductive_mind := <?list?>; inductive_ind := 0
              |} 0 []) [typeofTm]
  | h :: t =>  tApp
               (tConstruct
               {| inductive_mind := <?list?>; inductive_ind := 0 |} 1 [])
               [typeofTm; h; (build_coq_list t typeofTm)]
  end.

(** Dispatch mechanism: try each function in the list until one returns Some.
    Returns None if all functions return None. *)

Fixpoint dispatch_clauses (inT : Type) (outT : Type)
                            (listFn : list (inT -> option (outT))) : (inT -> (option outT)) :=
 fun x => match listFn with
           | [] => None
           | h :: t => let r := h x in
                       match r with
                       | None => (dispatch_clauses inT outT t) x
                       | _ => r
                       end
          end .

(** Provide a default value for an option-returning function. *)
Definition with_default (inputType outputType : Type)
  (default : outputType)
  (f : inputType -> option outputType)
  : inputType -> outputType :=
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
Fixpoint ordered_vars_aux (ls : list term) : list string :=
  match ls with
  | [] => []
  | (tVar str) :: t => str :: (ordered_vars_aux t)
  | _ :: t => (ordered_vars_aux t)
  end.

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

(** Extract variable names from a term in declaration order.
    For equality terms, lists known-side variables before unknown-side variables. *)
Fixpoint ordered_vars (t : term) : list string :=
  match t with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => [str1 ; str2]
  | tApp <%eq%> [typeT; tVar str1; tApp fn lst] => str1 :: ordered_vars_aux (lst)
  | tApp <%eq%> [typeT; tApp fn lst; tVar str1] => app (ordered_vars_aux (lst)) [str1]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] => [str1]
  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>  [str1]

  | tVar str  => [str]
  | tApp _ lst => concat (map ordered_vars lst)
  | _ => []
  end.

(** Apply [ordered_vars] to each element of [l] and concatenate the results. *)
Fixpoint ordered_vars_of_list (l : list term) : list string :=
  match l with
  | [] => []
  | h :: t => app (ordered_vars h) (ordered_vars_of_list t)
  end.
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
  | h :: t => app (select_from_index h l) (select_by_indices t l)
  end.

(** Select the input arguments of predicate [indNm] from [lstArgs] according to its mode. *)
Fixpoint select_in_args (indNm : string) (modes : mode_map) (lstArgs : list term) : list term :=
  match modes with
  | [] => []
  | h :: t =>
    if String.eqb indNm (fst h)
    then select_by_indices (fst (snd h)) lstArgs
    else select_in_args indNm t lstArgs
  end.

(** Select the output arguments of predicate [indNm]
    from [lstArgs] according to its mode. *)
Fixpoint select_out_args (indNm : string)
  (modes : mode_map) (lstArgs : list term)
  : list term :=
  match modes with
  | [] => []
  | h :: t =>
    if String.eqb indNm (fst h)
    then select_by_indices (snd (snd h)) lstArgs
    else select_out_args indNm t lstArgs
  end.

Fixpoint lookup_one_var (varNm : string)
  (allVarTpInf : list (prod string term))
  : list (prod string term) :=
  match allVarTpInf with
  | [] => []
  | h :: t => if String.eqb varNm (fst h) then [h] else lookup_one_var varNm t
  end.

(** Convert a [(variable_name, type)] list to a [(tVar name, type)] list. *)
Fixpoint pairs_to_terms (lst : list (prod string term)) : list (prod term term) :=
  match lst with
  | [] => []
  | (str,tp) :: t => (tVar str, tp) :: pairs_to_terms t
  end.
(** Look up each variable name in [lst] in the type environment, dropping missing entries. *)
Fixpoint lookup_vars (lst : list string)
  (allVarTpInf : list (prod string term))
  : list (prod string term) :=
  match lst with
  | [] => []
  | h :: t => match lookup_one_var h allVarTpInf with
             | [h'] => h' :: lookup_vars t allVarTpInf
             | _ =>  lookup_vars t allVarTpInf
            end
  end.

(** Look up the mode (input-position list, output-position list) for [indNm],
    returning ([],[]) if not found. *)
Fixpoint lookup_mode (indNm : string) (modes : mode_map) : (list nat) * (list nat) :=
  match modes with
  | [] => ([],[])
  | h :: t => if String.eqb indNm (fst h) then (snd h) else lookup_mode indNm t
  end.

(** Select the input arguments from [lstArgs] using a pre-looked-up [mode] pair. *)
Definition select_in_by_mode  (mode : (list nat) * (list nat)) (lstArgs : list term) : list term :=
select_by_indices (fst mode) lstArgs.

(** Select the output arguments from [lstArgs] using a pre-looked-up [mode] pair. *)
Definition select_out_by_mode  (mode : (list nat) * (list nat)) (lstArgs : list term) : list term :=
select_by_indices (snd mode) lstArgs.

(** Look up the argument types for predicate [indNm] in a type-info table. *)
Fixpoint lookup_pred_type (indNm : string) (predTypeInf : pred_type_map) : list term :=
  match predTypeInf with
  | [] => []
  | h :: t => if String.eqb indNm (fst h) then snd h else lookup_pred_type indNm t
  end.

(** Build the right-nested product type of a list of types, using [bool] as the
    empty-list base case. *)
Fixpoint nested_prod_type (lstTypes : list term) : term :=
  match lstTypes with
  | [] => <%bool%>
  | [h] => h
  | h :: t => tApp
                     (tInd
                        {|
                          inductive_mind := <?prod?>;
                          inductive_ind := 0
                        |} []) [h ; (nested_prod_type t)]
  end.

(** Identity function on [animation_result]: used as the single-element join. *)
Definition join_unit (A: Type) (x : animation_result A) : animation_result A :=
x.

(** Applicative product of two animation results: succeeds with a pair iff both
    succeed; propagates [FuelError] over [NoMatch]. *)
Definition join_pair (A B : Type)
  (x : animation_result A) (y : animation_result B)
  : animation_result (prod A B) :=
  match x with
  | NoMatch => NoMatch (prod A B)
  | FuelError => FuelError (prod A B)
  | Success k => match y with
                        | NoMatch => NoMatch (prod A B)
                        | FuelError => FuelError (prod A B)
                        | Success j => Success (prod A B) (k,j)
                        end
  end.

(** Build the body of a join function for [lstTypes]: folds [join_pair] over
    variables named "o0", "o1", …, starting at index [n]. *)
Fixpoint mk_join_body (lstTypes : list term) (n : nat) : term :=
  match lstTypes with
  | [] => <%Success bool true%>
  | [h] => tApp <%join_unit%> [h; tVar (String.append "o" (string_of_nat n))]
  | [h ; h1] =>
    tApp <%join_pair%>
      [h; h1;
       tVar (String.append "o" (string_of_nat n));
       tVar (String.append "o" (string_of_nat (S n)))]
  | h :: t =>
    tApp <%join_pair%>
      [h; nested_prod_type t;
       tVar (String.append "o" (string_of_nat n));
       mk_join_body t (S n)]
  end.

(** Wrap [fnBody] in lambdas "o0 : animation_result T0",
    "o1 : ...", etc. for each type in [lstTypes]. *)
Fixpoint mk_join_lam (lstTypes : list term)
  (n : nat) (fnBody : term) : term :=
  match lstTypes with
  | [] => fnBody
  | [h] =>
    tLam (String.append "o" (string_of_nat n))
      (tApp <%animation_result%> [h]) fnBody
  | h :: t =>
    tLam (String.append "o" (string_of_nat n))
      (tApp <%animation_result%> [h])
      (mk_join_lam t (S n) fnBody)
  end.

(** Build a quoted function that joins multiple [animation_result] values into one
    product result, combining [mk_join_body] and [mk_join_lam]. *)
Definition mk_join_tm (lstTypes : list term) : term :=
let fnBody := mk_join_body lstTypes 0 in
mk_join_lam lstTypes 0 fnBody.

(** Compare two [animation_result] values with [eqfn]: returns [Success true] if
    both succeed and are equal, [NoMatch] if unequal or one is [NoMatch],
    [FuelError] if either is a fuel error. *)
Definition eq_outcome (A : Type)
  (eqfn : A -> A -> bool)
  (x y : animation_result A)
  : animation_result bool :=
  match x with
  | Success j => match y with
                    | Success k => if eqfn j k then (Success bool true) else (NoMatch bool)
                    | NoMatch => NoMatch bool
                    | FuelError => FuelError bool
                   end
  | FuelError => FuelError bool
  | NoMatch =>  match y with
                    | FuelError => FuelError bool
                    | _ => NoMatch bool
                   end
  end.

(** Build a quoted term [eq_outcome tpTm tpEqFn]: the equality function on
    [animation_result tpTm] using the boolean equality [tpEqFn] on the base type. *)
Definition mk_eq_outcome_tm (tpTm tpEqFn : term)
  : term :=
  tApp <%eq_outcome%> [tpTm; tpEqFn].

(** Short-circuit conjunction of two boolean animation results: [Success true]
    only if both succeed with [true]; [FuelError] takes priority over [NoMatch]. *)
Definition and_outcome_bool
  (x y : animation_result bool)
  : animation_result bool :=
  match x with
  | FuelError  => FuelError bool
  | NoMatch => match y with
                   | FuelError => FuelError bool
                   | _ => NoMatch bool
                  end
  | Success true => match y with
                        | Success true => Success bool true
                        | Success false => NoMatch bool
                        | NoMatch => NoMatch bool
                        | FuelError => FuelError bool
                       end
  | Success false => match y with
                         | FuelError => FuelError bool
                         | _ => NoMatch bool
                        end
  end.

(** Build a quoted term that joins the [animation_result] values of all output
    variables [outVars] into a single product result using [mk_join_tm]. *)
Definition mk_output_prod_tm (outVars : list (prod string term)) : term :=
tApp (mk_join_tm (map snd outVars)) (map (fun e => tVar (fst e)) outVars).

(** Wrap [fnBody] in a sequence of lambda abstractions, one for each [(name, type)]
    pair in [inVars], building innermost-first. *)
Fixpoint mk_lam_chain (inVars : list (prod string term)) (fnBody : term) :=
  match inVars with
  | [] => fnBody

  | h :: t => tLam (fst h) (snd h) (mk_lam_chain t fnBody)
  end.

(** Sentinel values for partial functions — used as defaults in match fallbacks. *)
Parameter sentinel_term : term.
Parameter sentinel_nat : nat.
Parameter sentinel_inductive : inductive.
Parameter sentinel_string : string.
Parameter sentinel_nat_list : list nat.
Parameter sentinel_def_term : def term.

(** String constants for generated definition names. *)
Definition top_fn_suffix : string := "AnimatedTopFn".
Definition stream_suffix : string := "AnimatedTopFnStream".
Definition anim_suffix : string := "Animated".

(** Append [top_fn_suffix] to every function name in the [(name, type)] list,
    producing the names used for the generated animated definitions. *)
Fixpoint mk_animated_names (l : list (string * term)) : list (string * term) :=
  match l with
  | [] => []
  | (s,tp) :: t => ((String.append s top_fn_suffix), tp) :: mk_animated_names t
  end.

(** Project the first component of a paired [animation_result]: discards the second
    component on [Success], preserves [FuelError] and [NoMatch]. *)
Definition split_outcome_fst (A B : Type)
  (x : animation_result (A * B))
  : animation_result A :=
  match x with
  | Success (a,b) => Success A a
  | NoMatch => NoMatch A
  | FuelError => FuelError A
  end.

(** Project the second component of a paired [animation_result]: discards the first
    component on [Success], preserves [FuelError] and [NoMatch]. *)
Definition split_outcome_snd (A B : Type)
  (x : animation_result (A * B))
  : animation_result B :=
  match x with
  | Success (a,b) => Success B b
  | NoMatch => NoMatch B
  | FuelError => FuelError B
  end.
