(** * MetaRocqUtils — MetaRocq Notation Macros, De Bruijn Conversion, and Substitution

    Provides notation macros ([MetaRocqNotations]), De Bruijn conversion utilities
    ([DB]), named-variable substitution ([Substitution]), and constant substitution
    ([ConstSubstitution]).

    Animation-domain record types are in [AnimationTypes].
    The [animation_result] type and its combinators are in [AnimationResult].
    Quoted-term builders, mode lookups, and sentinels are in [TermUtils].
    All other animation modules depend on this file. *)

Require Import Animation.AnimationTypes.
Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
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
