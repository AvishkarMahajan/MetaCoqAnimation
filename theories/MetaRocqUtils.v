(** * MetaRocqUtils — Core MetaRocq Utilities

    Foundational utilities shared by the entire animation pipeline:
    notation macros, De Bruijn conversion, term substitution, type-level
    helpers ([AnimationResult], [indTp], sentinels), and term-construction
    combinators ([mkLstTm], [telescopeToProdType], [composeOutcomePoly], …).

    All other animation modules depend on this file. *)

Require Import List.
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
  Definition deBruijn' (ctx : list name) (t : named_term) : TemplateMonad term :=
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
  Definition deBruijn (t : named_term) : TemplateMonad term := deBruijn' nil t.

  (** Pure (non-monadic) variant of [deBruijn']; returns [None] on failure. *)
Definition deBruijn'Option (ctx : list name) (t : named_term) : option term :=
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

  (** Pure variant of [deBruijn] with no outer context. *)
  Definition deBruijnOption (t : named_term) : option term := deBruijn'Option nil t.

  (** Convert a de Bruijn term back to named representation given context [ctx]:
      replaces [tRel n] with [tVar id] where [ctx !! n = nNamed id]. *)
  Definition undeBruijn' (ctx : list name) (t : term) : TemplateMonad named_term :=
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
  Definition undeBruijn (t : term) : TemplateMonad named_term :=
    undeBruijn' nil t.

  (* Example usage for deBruijn:

   MetaRocq Run (t <- DB.deBruijn
                      (tLambda (mkBindAnn (nNamed "x") Relevant)
                                <% bool %> (tVar "x"))%string ;;
                t' <- tmUnquoteTyped (bool -> bool) t ;;
                tmPrint t).
  *)

  (* Example usage for undeBruijn:

   MetaRocq Run (t <- DB.undeBruijn <% fun (x : bool) => x %> ;;
                tmPrint t).
  *)

  (* Round trip test:

  MetaRocq Run (t <- DB.undeBruijn
                      <% fix f (x y : nat) :=
                           match x with S x' => f x' (S y) | O => y end %> ;;
               t <- DB.deBruijn t ;;
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
      else tLetIn (mkBindAnn (nNamed id) rel) (named_subst t x b) (named_subst t x ty) (named_subst t x b')
    | tLetIn na b ty b' => tLetIn na (named_subst t x b) (named_subst t x ty) (named_subst t x b')
    | tApp u0 v => mkApps (named_subst t x u0) (map (named_subst t x) v)
    | tCase ind p c brs =>
        let p' := {| puinst := puinst p
                   ; pparams := map (named_subst t x) (pparams p)
                   ; pcontext := pcontext p
                   ; preturn := named_subst t x (preturn p)
                   |} in
        let brs' := map (fun br => {| bcontext := bcontext br ; bbody := named_subst t x (bbody br) |} ) brs in
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

  (** Apply a list of [(identifier, replacement)] substitutions to [u] in order. *)
  Fixpoint named_subst_all (l : list (ident * named_term)) (u : named_term) : named_term :=
    match l with
    | nil => u
    | (id, t) :: l' => named_subst_all l' (named_subst t id u)
    end.
End Substitution.

(** ** Constant Substitution

    Substitution of a [global_term] for all references to a specific [kername]. *)
Module ConstSubstitution.
  (** Replace all [tConst kn _] references matching [x] with [t]. *)
  Fixpoint named_subst (t : global_term) (x : kername) (u : named_term) {struct u} : named_term :=
    match u with
    | tConst kn _ => if eq_kername x kn then t else u
    | tVar id => u
    | tEvar ev args => tEvar ev (map (named_subst t x) args)
    | tCast c kind ty => tCast (named_subst t x c) kind (named_subst t x ty)
    | tProd (mkBindAnn (nNamed id) rel) A B =>
      tProd (mkBindAnn (nNamed id) rel) (named_subst t x A) (named_subst t x B)
    | tProd na A B => tProd na (named_subst t x A) (named_subst t x B)
    | tLambda (mkBindAnn (nNamed id) rel) T M =>
      tLambda (mkBindAnn (nNamed id) rel) (named_subst t x T) (named_subst t x M)
    | tLambda na T M => tLambda na (named_subst t x T) (named_subst t x M)
    | tLetIn (mkBindAnn (nNamed id) rel) b ty b' =>
      tLetIn (mkBindAnn (nNamed id) rel) (named_subst t x b) (named_subst t x ty) (named_subst t x b')
    | tLetIn na b ty b' => tLetIn na (named_subst t x b) (named_subst t x ty) (named_subst t x b')
    | tApp u0 v => mkApps (named_subst t x u0) (map (named_subst t x) v)
    | tCase ind p c brs =>
        let p' := {| puinst := puinst p
                   ; pparams := map (named_subst t x) (pparams p)
                   ; pcontext := pcontext p
                   ; preturn := named_subst t x (preturn p)
                   |} in
        let brs' := map (fun br => {| bcontext := bcontext br ; bbody := named_subst t x (bbody br) |} ) brs in
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

(** Result type for animated functions: success with a value, fuel exhaustion, or no matching clause. *)
Inductive AnimationResult (A : Type) : Type :=
| FuelError : AnimationResult A
| Success : A -> AnimationResult A
| NoMatch : AnimationResult A.

(** Wrapper type that marks a value as coming from an inductive definition.
    Used to distinguish inductive values in animation result types. *)
Inductive indTp (A : Type) : Type :=
| indWrap : A -> indTp A.

(** Build a product type from a list of output variable specs.
    Returns bool for empty list, single type for singleton, nested products otherwise. *)
Fixpoint telescopeToProdType (outputData : list (string * term)) :  term :=
 match outputData with
  | [] => <%bool%>
  | [h] =>  (snd h)
  | h :: t => let res := telescopeToProdType t in  (tApp
                                            (tInd
                                             {|
                                             inductive_mind := <?prod?>; inductive_ind := 0
                                              |} []) [(snd h) ; res])
 end.

(** Build a product term from a list of output variables.
    Constructs nested pairs of variables. *)
Fixpoint telescopeToProdTerm  (outputData : list (string * term )) : term :=
 match outputData with
  | [] => <%true%>
  | [h] => (tVar (fst h))
  | h :: t => let res := telescopeToProdTerm t in
                                        let resT := telescopeToProdType t in (tApp (tConstruct
                                                  {|
                                                   inductive_mind := <?prod?>; inductive_ind := 0
                                                   |} 0 []) [(snd h); resT ; (tVar (fst h)) ; res])
 end.

(** Kleisli composition for animated functions: run [f] on the input, then feed
    its [Success] result into [f'], propagating [FuelError] and [NoMatch]. *)
Definition composeOutcomePoly (A : Type) (B : Type) (C : Type) (f : nat -> AnimationResult A -> AnimationResult B) (f' : nat -> AnimationResult B -> AnimationResult C)
                                   : (nat -> AnimationResult A -> AnimationResult C) :=
 fun fuel input => match f fuel input with
                    | Success res => f' fuel  (Success B res)
                    | FuelError => (FuelError C)
                    | _ =>  (NoMatch C)
                   end.

Open Scope bs.

(** Build the product type of a non-empty list of [(term, type)] pairs.
    Fails if the list is empty; returns a single type for singletons. *)
Fixpoint mklhsProdType (lhsIndPre : list (term * term)) : TemplateMonad term :=
  match lhsIndPre with
  | [] => tmFail "no predicates on LHS0"
  | [h] => tmReturn (snd h)
  | h :: t =>
      res <- mklhsProdType t ;;
      tmReturn (tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; res])
  end.

(** Build the product term of a non-empty list of [(term, type)] pairs.
    Companion to [mklhsProdType]; fails on empty input. *)
Fixpoint mklhsProdTm (lhsIndPre : list (term * term)) : TemplateMonad term :=
  match lhsIndPre with
  | [] => tmFail "no predicates on LHS1"
  | [h] => tmReturn (fst h)
  | h :: t =>
      res <- mklhsProdTm t ;;
      resT <- mklhsProdType t ;;
      tmReturn (tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
                     [snd h; resT; fst h; res])
  end.

(** Constant function that always returns fuel error.
    Used as a fallback when fuel is exhausted. *)
Definition fuelErrorPolyCstFn (inputType : Type) (outputType' : Type) : (inputType -> (AnimationResult outputType') ) :=
 fun x : inputType => FuelError outputType'.

(** Test whether nat [a] occurs in list [l]. *)
Fixpoint inNatLst (a : nat) (l : list nat) : bool :=
 match l with
  | nil => false
  | (h :: t) => if (Nat.eqb h a) then true else (inNatLst a t)
 end.

(** Test whether every element of [l1] occurs in [l2] (multiset subset). *)
Fixpoint isListSub (l1 l2 : list nat) : bool :=
  match l1 with
  | [] => true
  | h :: t => inNatLst h l2 && isListSub t l2
  end.

(** Test whether string [s] occurs in list [l1]. *)
Fixpoint inStrLst (s : string) (l1 : list string) : bool :=
  match l1 with
  | [] => false
  | h :: t => if String.eqb s h then true else inStrLst s t
  end.

(** Test whether every element of string list [l1] occurs in [l2]. *)
Fixpoint isListSubStr (l1 l2 : list string) : bool :=
  match l1 with
  | [] => true
  | h :: t => inStrLst h l2 && isListSubStr t l2
  end.

(** Return [true] iff every element of [lst] is [true] (conjunction). *)
Fixpoint checkBool (lst : list bool) : bool :=
 match lst with
 | [] => true
 | h :: t => andb h (checkBool t)
end.

(** Decide pointwise equality of two [nat] lists. *)
Fixpoint eqLstNat (l1 : list nat) (l2 : list nat) : bool :=
 match l1 with
  | [] => match l2 with
          | [] => true
          | _ => false
          end
  | (h :: t) => match l2 with
                 | [] => false
                 | (h' :: t') => if (Nat.eqb h h') then eqLstNat t t' else false
                end
  end.

(** Adapt a function returning [AnimationResult (option B)] into one returning
    [AnimationResult B]: [Some v] becomes [Success v], [None] becomes [NoMatch]. *)
Definition optionToOutcome (A : Type) (B : Type) (f : nat -> AnimationResult A -> AnimationResult (option B)) : (nat -> AnimationResult A -> AnimationResult B) :=
fun k k' => match f k k' with
             | Success (Some res) => Success B res
             | Success None => NoMatch B
             | FuelError => FuelError B
             | _ => NoMatch B
            end.

(** Return [true] iff [lst] is empty. *)
Definition isEmptyLst {A : Type} (lst : list A) : bool :=
match lst with
 | [] => true
 | _ => false
end.

(** Build a quoted [list term] literal from [lst], with element type [typeofTm]. *)
Fixpoint mkLstTm' (lst : list term) (typeofTm : term) : term :=
 match lst with
  | [] => tApp
           (tConstruct
              {|
                inductive_mind := <?list?>; inductive_ind := 0
              |} 0 []) [typeofTm]
  | h :: t =>  tApp
               (tConstruct
               {| inductive_mind := <?list?>; inductive_ind := 0 |} 1 [])
               [typeofTm; h; (mkLstTm' t typeofTm)]
 end.

(** Dispatch mechanism: try each function in the list until one returns Some.
    Returns None if all functions return None. *)

Fixpoint dispatchInternal (inT : Type) (outT : Type)
                            (listFn : list (inT -> option (outT))) : (inT -> (option outT)) :=
 fun x => match listFn with
           | [] => None
           | h :: t => let r := h x in
                       match r with
                       | None => (dispatchInternal inT outT t) x
                       | _ => r
                       end
          end .

(** Provide a default value for an option-returning function. *)
Definition defaultVal (inputType : Type) (outputType : Type) (default : outputType) (f : inputType -> option (outputType)) : (inputType -> outputType) :=
 fun x => match f x with
           | Some y => y
           | None => default
          end.

(** Quote each element of [l] into a MetaRocq term using [tmQuote]. *)
Fixpoint quoteList {A : Type} (l : list A) : TemplateMonad (list term) :=
  match l with
  | [] => ret []
  | h :: rest =>
      t <- tmQuote h ;;
      l' <- quoteList rest ;;
      tmReturn (t :: l')
  end.

(** Extract variable names from a flat list of terms (non-[tVar] terms are dropped). *)
Fixpoint extractOrderedVarsHelper (ls : list term) : list string :=
 match ls with
 | [] => []
 | (tVar str) :: t => str :: (extractOrderedVarsHelper t)
 | _ :: t => (extractOrderedVarsHelper t)
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
Fixpoint extractOrderedVars (t : term) : list string :=
  match t with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => [str1 ; str2]
  | tApp <%eq%> [typeT; tVar str1; tApp fn lst] => str1 :: extractOrderedVarsHelper (lst)
  | tApp <%eq%> [typeT; tApp fn lst; tVar str1] => app (extractOrderedVarsHelper (lst)) [str1]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] => [str1]
  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>  [str1]

  | tVar str  => [str]
  | tApp _ lst => concat (map extractOrderedVars lst)
  | _ => []
  end.

(** Apply [extractOrderedVars] to each element of [l] and concatenate the results. *)
Fixpoint extractOrderedVarsfmLst (l : list term) : list string :=
match l with
| [] => []
| h :: t => app (extractOrderedVars h) (extractOrderedVarsfmLst t)
end.
(** Return a singleton list containing element [ind] of [l], or [[]] if out of bounds. *)
Fixpoint listSearch' {A : Type} (ind : nat) (l : list A) : list A :=
match ind with
| 0 => match l with
     | h :: t => [h]
     | [] => []
     end
| S m => listSearch' m (tl l)
end.

(** Select elements at positions [indLst] from list [l]. *)
Fixpoint listSearch {A : Type} (indLst : list nat) (l : list A) : list A :=
match indLst with
| [] => []
| h :: t => app (listSearch' h l) (listSearch t l)
end.

(** Select the input arguments of predicate [indNm] from [lstArgs] according to its mode. *)
Fixpoint getInArgs (indNm : string) (modes : list (string * ((list nat) * (list nat)))) (lstArgs : list term) : list term :=
match modes with
| [] => []
| h :: t => if String.eqb indNm (fst h) then listSearch (fst (snd h)) lstArgs else getInArgs indNm t lstArgs
end.

(** Select the output arguments of predicate [indNm] from [lstArgs] according to its mode. *)
Fixpoint getOutArgs (indNm : string) (modes : list (string * ((list nat) * (list nat)))) (lstArgs : list term) : list term :=
match modes with
| [] => []
| h :: t => if String.eqb indNm (fst h) then listSearch (snd (snd h)) lstArgs else getOutArgs indNm t lstArgs
end.

(** Return the singleton entry for variable [varNm] in the type environment,
    or [[]] if not found. *)
Fixpoint lookUpVarsOne (varNm: string) (allVarTpInf : list (prod string term)) : list (prod string term) :=
match allVarTpInf with
| [] => []
| h :: t => if String.eqb varNm (fst h) then [h] else lookUpVarsOne varNm t
end.

(** Convert a [(variable_name, type)] list to a [(tVar name, type)] list. *)
Fixpoint mkLstTm (lst : list (prod string term)) : list (prod term term) :=
match lst with
| [] => []
| (str,tp) :: t => (tVar str, tp) :: mkLstTm t
end.
(** Look up each variable name in [lst] in the type environment, dropping missing entries. *)
Fixpoint lookUpVars (lst : list string) (allVarTpInf : list (prod string term)) : list (prod string term) :=
match lst with
| [] => []
| h :: t => match lookUpVarsOne h allVarTpInf with
             | [h'] => h' :: lookUpVars t allVarTpInf
             | _ =>  lookUpVars t allVarTpInf
            end
end.

(** Look up the mode (input-position list, output-position list) for [indNm],
    returning ([],[]) if not found. *)
Fixpoint getModeFmLst (indNm : string) (modes : list (string * ((list nat) * (list nat)))) : (list nat) * (list nat) :=
 match modes with
  | [] => ([],[])
  | h :: t => if String.eqb indNm (fst h) then (snd h) else getModeFmLst indNm t
 end.

(** Select the input arguments from [lstArgs] using a pre-looked-up [mode] pair. *)
Definition getInArgs'  (mode : (list nat) * (list nat)) (lstArgs : list term) : list term :=
listSearch (fst mode) lstArgs.

(** Select the output arguments from [lstArgs] using a pre-looked-up [mode] pair. *)
Definition getOutArgs'  (mode : (list nat) * (list nat)) (lstArgs : list term) : list term :=
listSearch (snd mode) lstArgs.

(** Look up the argument types for predicate [indNm] in a type-info table. *)
Fixpoint getPredTp (indNm : string) (predTypeInf : list (string * (list term))) : list term :=
match predTypeInf with
| [] => []
| h :: t => if String.eqb indNm (fst h) then snd h else getPredTp indNm t
end.

(** Zip two lists into a list of pairs, stopping at the shorter one. *)
Fixpoint crossList {A : Type} {B : Type} (lst1 : list A) (lst2 : list B) : list (A * B) :=
match lst1 with
 | [] => []
 | (h :: t) => match lst2 with
                | [] => []
                | h' :: t' => (h,h') :: crossList t t'
               end
end.

(** Build the right-nested product type of a list of types, using [bool] as the
    empty-list base case. *)
Fixpoint prodTerm (lstTypes : list term) : term :=
match lstTypes with
 | [] => <%bool%>
 | [h] => h
 | h :: t => tApp
                     (tInd
                        {|
                          inductive_mind := <?prod?>;
                          inductive_ind := 0
                        |} []) [h ; (prodTerm t)]
end.

(** Identity function on [AnimationResult]: used as the single-element join. *)
Definition joinOutcomeUnit (A: Type) (x : AnimationResult A) : AnimationResult A :=
x.

(** Applicative product of two animation results: succeeds with a pair iff both
    succeed; propagates [FuelError] over [NoMatch]. *)
Definition joinOutcome (A : Type) (B : Type) (x : AnimationResult A) (y : AnimationResult B) : AnimationResult (prod A B) :=
 match x with
  | NoMatch => NoMatch (prod A B)
  | FuelError => FuelError (prod A B)
  | Success k => match y with
                        | NoMatch => NoMatch (prod A B)
                        | FuelError => FuelError (prod A B)
                        | Success j => Success (prod A B) (k,j)
                        end
 end.

(** Build the body of a join function for [lstTypes]: folds [joinOutcome] over
    variables named "o0", "o1", …, starting at index [n]. *)
Fixpoint mkJoinOutcomeFnBody (lstTypes : list term) (n : nat) : term :=
match lstTypes with
 | [] => <%Success bool true%>
 | [h] => tApp <%joinOutcomeUnit%> [h; tVar (String.append "o" (string_of_nat n))]
 | [h ; h1] => tApp <%joinOutcome%> [h; h1; tVar (String.append "o" (string_of_nat n)); tVar (String.append "o" (string_of_nat (S n)))]
 | h :: t => tApp <%joinOutcome%> [h; (prodTerm t); tVar (String.append "o" (string_of_nat n)); mkJoinOutcomeFnBody t (S n)]
end.

(** Wrap [fnBody] in lambdas "o0 : AnimationResult T0", "o1 : …", etc. for each type in [lstTypes]. *)
Fixpoint mkJoinOutcomeLam (lstTypes : list term) (n : nat) (fnBody : term) : term :=
match lstTypes with
| [] => fnBody
| [h] => tLam (String.append "o" (string_of_nat n)) (tApp <%AnimationResult%> [h]) fnBody
| h :: t => tLam (String.append "o" (string_of_nat n)) (tApp <%AnimationResult%> [h]) (mkJoinOutcomeLam t (S n) fnBody)
end.

(** Build a quoted function that joins multiple [AnimationResult] values into one
    product result, combining [mkJoinOutcomeFnBody] and [mkJoinOutcomeLam]. *)
Definition mkJoinOutcomeTm (lstTypes : list term) : term :=
let fnBody := mkJoinOutcomeFnBody lstTypes 0 in
mkJoinOutcomeLam lstTypes 0 fnBody.

(** Compare two [AnimationResult] values with [eqfn]: returns [Success true] if
    both succeed and are equal, [NoMatch] if unequal or one is [NoMatch],
    [FuelError] if either is a fuel error. *)
Definition eqOutcomeTp (A : Type) (eqfn : A -> A -> bool) (x: AnimationResult A) (y : AnimationResult A) : AnimationResult bool :=
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

(** Build a quoted term [eqOutcomeTp tpTm tpEqFn]: the equality function on
    [AnimationResult tpTm] using the boolean equality [tpEqFn] on the base type. *)
Definition typeToBoolEqOutcome (tpTm : term) (tpEqFn : term) : term := tApp <%eqOutcomeTp%> [tpTm; tpEqFn].

(** Short-circuit conjunction of two boolean animation results: [Success true]
    only if both succeed with [true]; [FuelError] takes priority over [NoMatch]. *)
Definition compOutcomeBool (x : AnimationResult bool) (y : AnimationResult bool) : AnimationResult bool :=
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

(** Build a quoted term that joins the [AnimationResult] values of all output
    variables [outVars] into a single product result using [mkJoinOutcomeTm]. *)
Definition mkOutPolyProdTm (outVars : list (prod string term)) : term :=
tApp (mkJoinOutcomeTm (map snd outVars)) (map (fun e => tVar (fst e)) outVars).

(** Wrap [fnBody] in a sequence of lambda abstractions, one for each [(name, type)]
    pair in [inVars], building innermost-first. *)
Fixpoint mkLamTp (inVars : list (prod string term)) (fnBody : term) :=
match inVars with
| [] => fnBody

| h :: t => tLam (fst h) (snd h) (mkLamTp t fnBody)
end.

(** Sentinel values for partial functions — used as defaults in match fallbacks. *)
Parameter sentinel_term : term.
Parameter sentinel_nat : nat.
Parameter sentinel_inductive : inductive.
Parameter sentinel_string : string.
Parameter sentinel_nat_list : list nat.
Parameter sentinel_def_term : def term.

(** String constants for generated definition names. *)
Definition animatedTopFnSuffix : string := "AnimatedTopFn".
Definition animatedStreamSuffix : string := "AnimatedTopFnStream".
Definition animatedSuffix : string := "Animated".

(** Append [animatedTopFnSuffix] to every function name in the [(name, type)] list,
    producing the names used for the generated animated definitions. *)
Fixpoint mkAnimatedFnNm (l : list (string * term)) : list (string * term) :=
match l with
| [] => []
| (s,tp) :: t => ((String.append s animatedTopFnSuffix), tp) :: mkAnimatedFnNm t
end.

(** Project the first component of a paired [AnimationResult]: discards the second
    component on [Success], preserves [FuelError] and [NoMatch]. *)
Definition splitOutcomePolyFst (A : Type) (B : Type) (x : AnimationResult (A * B)) : AnimationResult A :=
match x with
 | Success (a,b) => Success A a
 | NoMatch => NoMatch A
 | FuelError => FuelError A
end.

(** Project the second component of a paired [AnimationResult]: discards the first
    component on [Success], preserves [FuelError] and [NoMatch]. *)
Definition splitOutcomePolySnd (A : Type) (B : Type) (x : AnimationResult (A * B)) : AnimationResult B :=
match x with
 | Success (a,b) => Success B b
 | NoMatch => NoMatch B
 | FuelError => FuelError B
end.
