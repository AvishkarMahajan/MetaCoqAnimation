Require Import List.
Require Import MetaRocq.Template.All.

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

(* Warning: MetaRocq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MRMonadNotation
       ListNotations
       MetaRocqNotations.

(* Alias to distinguish terms that are NOT in de Bruijn notation. *)
Definition named_term : Type := term.
(* Alias for terms that do not contain references to local variables,
   therefore can be used in either [term]s in de Bruijn notation
   and [named_term]s in named notation. *)
Definition global_term : Type := term.
(* Alias to denote that a function works with
   either [term], [named_term] or [global_term]. *)
Definition any_term : Type := term.

Definition ident_eq (x y : ident) : bool :=
  match compare_ident x y with
  | Eq => true
  | _ => false
  end.

Module DB.
 (* Inspired by code written by John Li but changed slightly.
     We should eventually consider making a MetaRocq_utils module. *)
  (* Takes a named representation and converts it into the de Bruijn representation. *)
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

  Definition deBruijn (t : named_term) : TemplateMonad term := deBruijn' nil t.
  
  

  (* Takes a de Bruijn representation and changes [tRel]s to [tVar]s. *)
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

Module Substitution.
  (* Capturing substitution for named terms, only use for global terms. *)
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

  (* Substitute multiple [named_term]s into a [named_term]. *)
  Fixpoint named_subst_all (l : list (ident * named_term)) (u : named_term) : named_term :=
    match l with
    | nil => u
    | (id, t) :: l' => named_subst_all l' (named_subst t id u)
    end.
End Substitution.

Module ConstSubstitution.
  Fixpoint named_subst (t : global_term) (x : kername) (u : named_term) {struct u} : named_term :=
    match u with
    | tConst kn _ => if eq_kername x kn then t else u
    | tVar id => t
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

  (* Substitute multiple [named_term]s into a [named_term]. *)
  Fixpoint named_subst_all (l : list (kername * named_term)) (u : named_term) : named_term :=
    match l with
    | nil => u
    | (id, t) :: l' => named_subst_all l' (named_subst t id u)
    end.
End ConstSubstitution.
