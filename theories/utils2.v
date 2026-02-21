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

Check monad_map.


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

  Definition deBruijnOption (t : named_term) : option term := deBruijn'Option nil t.
  
  

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
Print name.
Print ident.
    

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

Module general. 

Open Scope bs.
Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.

Lemma functional_extensionality {A B} (f g : A -> B) :
  (forall x, f x = g x) -> f = g. Proof. Admitted.





Definition test : TemplateMonad unit :=
  t <- @tmQuote bool ((fun (n : nat) =>
                         match n with
                         | O => true
                         | S n' => false
                         end) 5) ;;
  t' <- DB.undeBruijn t ;;
  t'' <- DB.deBruijn t' ;;
  tmMsg "BEFORE" ;;
  tmPrint t ;;
  tmMsg "AFTER" ;;
  tmPrint t' ;;
  tmMsg "ROUND TRIP" ;;
  tmPrint t''.


Definition animate_conjunct
           (c : constructor_body) (conjunct : context_decl) : TemplateMonad named_term :=
  (* t is the MetaRocq term for the conjunct like (e = b /\ d = c /\ c = a + e) *)
  let t : term := decl_type conjunct in
  (* tl here only works because we assume there is only one, large, nested "and" conjunct *)
  t_named <- DB.undeBruijn' (tl (map (fun arg => binder_name (decl_name arg)) (cstr_args c))) t ;;
  (* now you can work with the named representation, as you can see below: *)
  (*tmPrint t_named*) 
  ret t_named.

Fixpoint collect_conjuncts (cs : list constructor_body) : TemplateMonad (list named_term) :=
  match cs with
  | [] => ret []
  | c :: cs =>
      match cstr_args c with
      | conjunct :: _ =>
          conjunct' <- animate_conjunct c conjunct ;;
          cs' <- collect_conjuncts cs ;;
          ret (conjunct' :: cs')
      | _ => tmFail "No arguments for constructor c"
      end
  end.



Definition animate (kn : kername) : TemplateMonad unit :=
  mut <- tmQuoteInductive kn ;;
  match ind_bodies mut with
  | [ one ] =>
    conjuncts <- collect_conjuncts (ind_ctors one) ;;
    (* sepConj <- tAppDes conjuncts ;; *)
    (* there has to be something clever here *)
     ret conjuncts
  | _ => tmFail "Not one type in mutually inductive block."
  end ;;
  ret tt. 
 
 
 Definition animate2 (kn : kername) : TemplateMonad (named_term):=
  mut <- tmQuoteInductive kn ;;
  match ind_bodies mut with
  | [ one ] =>
    conjuncts <- collect_conjuncts (ind_ctors one) ;;
    (* sepConj <- tAppDes conjuncts ;; *)
    (* there has to be something clever here *)
    match conjuncts with
     | [single] => ret single
     | _ => tmFail "Not one type in mutually inductive block."
    end 
  | _ => tmFail "Not one type in mutually inductive block."
  end.  


(* Definition animate2 (kn : kername) : TemplateMonad (list named_term) :=
  mut <- tmQuoteInductive kn ;;
  match ind_bodies mut with
  | [ one ] =>
    conjuncts <- collect_conjuncts (ind_ctors one) ;;
    (*tmPrint conjuncts ;;*)
    (* sepConj <- tAppDes conjuncts ;; *)
    (* there has to be something clever here *)
     ret (conjuncts)
  | _ => tmFail "Not one type in mutually inductive block."
  end. (*;;
  ret tt.*)  *) 
End general. 

Inductive outcomePoly (A : Type) : Type :=
| fuelErrorPoly : outcomePoly A
| successPoly : A -> outcomePoly A
| noMatchPoly : outcomePoly A.



(** Build a product type from a list of output variable specs.
    Returns bool for empty list, single type for singleton, nested products otherwise. *)
Fixpoint mkProdTypeVars (outputData : list (string * term)) :  term :=
 match outputData with
  | [] => <%bool%>
  | [h] =>  (snd h)
  | h :: t => let res := mkProdTypeVars t in  (tApp
                                            (tInd
                                             {|
                                             inductive_mind := <?prod?>; inductive_ind := 0
                                              |} []) [(snd h) ; res])
 end.

(** Build a product term from a list of output variables.
    Constructs nested pairs of variables. *)
Fixpoint mkProdTmVars  (outputData : list (string * term )) : term :=
 match outputData with
  | [] => <%true%>
  | [h] => (tVar (fst h))
  | h :: t => let res := mkProdTmVars t in
                                        let resT := mkProdTypeVars t in (tApp (tConstruct
                                                  {|
                                                   inductive_mind := <?prod?>; inductive_ind := 0
                                                   |} 0 []) [(snd h); resT ; (tVar (fst h)) ; res])
 end.






Definition composeOutcomePoly (A : Type) (B : Type) (C : Type) (f : nat -> outcomePoly A -> outcomePoly B) (f' : nat -> outcomePoly B -> outcomePoly C)
                                   : (nat -> outcomePoly A -> outcomePoly C) :=
 fun fuel input => match f fuel input with
                    | successPoly res => f' fuel  (successPoly B res)
                    | fuelErrorPoly => (fuelErrorPoly C)
                    | _ =>  (noMatchPoly C)
                   end.
 
 


Definition composeOutcomePolyImpl {A : Type} {B : Type} {C : Type} (f : nat -> outcomePoly A -> outcomePoly B) (f' : nat -> outcomePoly B -> outcomePoly C)
                                   : (nat -> outcomePoly A -> outcomePoly C) :=
 fun fuel input => match f fuel input with
                    | successPoly res => f' fuel  (successPoly B res)
                    | fuelErrorPoly => (fuelErrorPoly C)
                    | _ =>  (noMatchPoly C)
                   end. 
     






Open Scope bs.


(* Construct a product type from a list of type pairs (for multiple LHS predicates). *)
Fixpoint mklhsProdType (lhsIndPre : list (term * term)) : TemplateMonad term :=
  match lhsIndPre with
  | [] => tmFail "no predicates on LHS0"
  | [h] => tmReturn (snd h)
  | h :: t =>
      res <- mklhsProdType t ;;
      tmReturn (tApp (tInd {| inductive_mind := <?prod?>; inductive_ind := 0 |} [])
                     [snd h; res])
  end.

(* Construct a product term from a list of term-type pairs. *)
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

(** Create product type for precondition predicates from LHS inductives. *)
Definition mkPreConProdType  (lhsInd : list ((((string * term) * term) * term) * term)) : TemplateMonad term :=
 mklhsProdType (map (fun tuple => ((snd (fst (fst (fst tuple)))), (snd (fst (fst tuple))))) lhsInd).

(** Create product term for precondition predicates from LHS inductives. *)
Definition mkPreConProdTm  (lhsInd : list ((((string * term) * term) * term) * term)) : TemplateMonad term :=
 mklhsProdTm (map (fun tuple => ((snd (fst (fst (fst tuple)))), (snd (fst (fst tuple))))) lhsInd).

(** Create product type for postcondition predicates from LHS inductives. *)
Definition mkPostConProdType  (lhsInd : list ((((string * term) * term) * term) * term)) : TemplateMonad term :=
 mklhsProdType (map (fun tuple => ((((snd (fst tuple)))), (((snd tuple))))) lhsInd).

(** Create product term for postcondition predicates from LHS inductives. *)
Definition mkPostConProdTm  (lhsInd : list ((((string * term) * term) * term) * term)) : TemplateMonad term :=
 mklhsProdTm (map (fun tuple => ((((snd (fst tuple)))), (((snd tuple))))) lhsInd).

(** Wrap pre/post conditions in outcomePoly success constructors. *)
Definition mkOutcome (lhsInd : ((((string * term) * term) * term) * term)) : ((((string * term) * term) * term) * term) :=
 match lhsInd with
  | ((((nm, preCon), preConT), postCon), postConT) => ((((nm, (tApp <%successPoly%> [preConT; preCon])), (tApp <%outcomePoly%> [preConT])), (tApp <%successPoly%> [postConT; postCon])), (tApp <%outcomePoly%> [postConT]))
 end.

(** Map mkOutcome over a list of LHS inductives. *)
Definition mkOutcomeProd (lhsInd : list ((((string * term) * term) * term) * term)) : list ((((string * term) * term) * term) * term) :=
 map (mkOutcome) lhsInd.
 
 

(** Constant function that always returns fuel error.
    Used as a fallback when fuel is exhausted. *)
Definition fuelErrorPolyCstFn (inputType : Type) (outputType' : Type) : (inputType -> (outcomePoly outputType') ) :=
 fun x : inputType => fuelErrorPoly outputType'.
 
 
 
Fixpoint inNatLst (a : nat) (l : list nat) : bool :=
 match l with
  | nil => false
  | (h :: t) => if (Nat.eqb h a) then true else (inNatLst a t)
 end.




Fixpoint isListSub (l1 l2 : list nat) : bool :=
  match l1 with
  | [] => true
  | h :: t => inNatLst h l2 && isListSub t l2
  end.

Fixpoint inStrLst (s : string) (l1 : list string) : bool :=
  match l1 with
  | [] => false
  | h :: t => if String.eqb s h then true else inStrLst s t
  end.

Fixpoint isListSubStr (l1 l2 : list string) : bool :=
  match l1 with
  | [] => true
  | h :: t => inStrLst h l2 && isListSubStr t l2
  end.

Fixpoint checkBool (lst : list bool) : bool :=
 match lst with
 | [] => true
 | h :: t => andb h (checkBool t)
end.


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
  
Definition optionToOutcome (A : Type) (B : Type) (f : nat -> outcomePoly A -> outcomePoly (option B)) : (nat -> outcomePoly A -> outcomePoly B) :=
fun k k' => match f k k' with
             | successPoly (Some res) => successPoly B res
             | successPoly None => noMatchPoly B
             | fuelErrorPoly => fuelErrorPoly B
             | _ => noMatchPoly B
            end.


Definition isEmptyLst {A : Type} (lst : list A) : bool :=
match lst with
 | [] => true
 | _ => false
end.
   
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

(* Quote a list of values into a list of terms. *)
Fixpoint quoteList {A : Type} (l : list A) : TemplateMonad (list term) :=
  match l with
  | [] => ret []
  | h :: rest =>
      t <- tmQuote h ;;
      l' <- quoteList rest ;;
      tmReturn (t :: l')
  end. 
  
  
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

(* extract ordered list of vars from conjunct *)
Fixpoint extractOrderedVars (t : term) : list string :=
  match t with
  | tApp <%eq%> [typeT; tVar str1; tVar str2] => [str1 ; str2]
  | tApp <%eq%> [typeT; tVar str1; tApp fn lst] => str1 :: extractOrderedVarsHelper (lst)
  | tApp <%eq%> [typeT; tApp fn lst; tVar str1] => app (extractOrderedVarsHelper (lst)) [str1]
  | tApp <%eq%> [typeT; tConstruct ind_type k lst; tVar str1] => [str1]
  | tApp <%eq%> [typeT; tVar str1; tConstruct ind_type k lst] =>  [str1]

  (* Combine the pattern matches to handle fns of arbitrary arity *)

  | tVar str  => [str]
  | tApp _ lst => concat (map extractOrderedVars lst)
  | _ => []
  end.  


Fixpoint extractOrderedVarsfmLst (l : list term) : list string :=
match l with
| [] => []
| h :: t => app (extractOrderedVars h) (extractOrderedVarsfmLst t)
end.
Fixpoint listSearch' {A : Type} (ind : nat) (l : list A) : list A :=
match ind with
| 0 => match l with
     | h :: t => [h]
     | [] => []
     end
| S m => listSearch' m (tl l)
end.     


Fixpoint listSearch {A : Type} (indLst : list nat) (l : list A) : list A :=
match indLst with 
| [] => []
| h :: t => app (listSearch' h l) (listSearch t l)
end. 

Fixpoint getInArgs (indNm : string) (modes : list (string * ((list nat) * (list nat)))) (lstArgs : list term) : list term :=
match modes with
| [] => []
| h :: t => if String.eqb indNm (fst h) then listSearch (fst (snd h)) lstArgs else getInArgs indNm t lstArgs
end. 

Fixpoint getOutArgs (indNm : string) (modes : list (string * ((list nat) * (list nat)))) (lstArgs : list term) : list term :=
match modes with
| [] => []
| h :: t => if String.eqb indNm (fst h) then listSearch (snd (snd h)) lstArgs else getOutArgs indNm t lstArgs
end.     


Print tLam.


 
Fixpoint lookUpVarsOne (varNm: string) (allVarTpInf : list (prod string term)) : list (prod string term) :=
match allVarTpInf with
| [] => []
| h :: t => if String.eqb varNm (fst h) then [h] else lookUpVarsOne varNm t
end.

Fixpoint mkLstTm (lst : list (prod string term)) : list (prod term term) :=
match lst with
| [] => []
| (str,tp) :: t => (tVar str, tp) :: mkLstTm t
end.
Fixpoint lookUpVars (lst : list string) (allVarTpInf : list (prod string term)) : list (prod string term) :=
match lst with
| [] => []
| h :: t => match lookUpVarsOne h allVarTpInf with
             | [h'] => h' :: lookUpVars t allVarTpInf
             | _ =>  lookUpVars t allVarTpInf
            end
end.


Definition lookUpVarsOneDefBool (varNm: string) (allVarTpInf : list (prod string term)) : (term) :=
match lookUpVarsOne varNm allVarTpInf with
| [h] => snd h
| _ => <%bool%>
end.
Fixpoint getModeFmLst (indNm : string) (modes : list (string * ((list nat) * (list nat)))) : (list nat) * (list nat) :=
 match modes with
  | [] => ([],[])
  | h :: t => if String.eqb indNm (fst h) then (snd h) else getModeFmLst indNm t
 end.

Definition getInArgs'  (mode : (list nat) * (list nat)) (lstArgs : list term) : list term :=
listSearch (fst mode) lstArgs.
 
Definition getOutArgs'  (mode : (list nat) * (list nat)) (lstArgs : list term) : list term :=
listSearch (snd mode) lstArgs.
 
 

Search (list (term * term) -> TemplateMonad term).
Print tLam.

Fixpoint getPredTp (indNm : string) (predTypeInf : list (string * (list term))) : list term :=
match predTypeInf with
| [] => []
| h :: t => if String.eqb indNm (fst h) then snd h else getPredTp indNm t 
end. 

Fixpoint crossList {A : Type} {B : Type} (lst1 : list A) (lst2 : list B) : list (A * B) :=
match lst1 with
 | [] => []
 | (h :: t) => match lst2 with
                | [] => []
                | h' :: t' => (h,h') :: crossList t t'
               end  
end.
                
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


Definition joinOutcomeUnit (A: Type) (x : outcomePoly A) : outcomePoly A :=
x.

Definition joinOutcome (A : Type) (B : Type) (x : outcomePoly A) (y : outcomePoly B) : outcomePoly (prod A B) :=
 match x with
  | noMatchPoly => noMatchPoly (prod A B)
  | fuelErrorPoly => fuelErrorPoly (prod A B)
  | successPoly k => match y with
                        | noMatchPoly => noMatchPoly (prod A B)
                        | fuelErrorPoly => fuelErrorPoly (prod A B)
                        | successPoly j => successPoly (prod A B) (k,j)
                        end
 end.




Fixpoint mkJoinOutcomeFnBody (lstTypes : list term) (n : nat) : term :=
match lstTypes with
 | [] => tApp <%joinOutcomeUnit%> [<%bool%>; tVar "o0"]
 | [h] => tApp <%joinOutcomeUnit%> [h; tVar (String.append "o" (string_of_nat n))]
 | [h ; h1] => tApp <%joinOutcome%> [h; h1; tVar (String.append "o" (string_of_nat n)); tVar (String.append "o" (string_of_nat (S n)))]
 | h :: t => tApp <%joinOutcome%> [h; (prodTerm t); tVar (String.append "o" (string_of_nat n)); mkJoinOutcomeFnBody t (S n)]
end.


Fixpoint mkJoinOutcomeLam (lstTypes : list term) (n : nat) (fnBody : term) : term :=
match lstTypes with
| [] => tLam "o0" (tApp <%outcomePoly%> [<%bool%>]) fnBody
| [h] => tLam (String.append "o" (string_of_nat n)) (tApp <%outcomePoly%> [h]) fnBody
| h :: t => tLam (String.append "o" (string_of_nat n)) (tApp <%outcomePoly%> [h]) (mkJoinOutcomeLam t (S n) fnBody)
end.

Definition mkJoinOutcomeTm (lstTypes : list term) : term :=
let fnBody := mkJoinOutcomeFnBody lstTypes 0 in
mkJoinOutcomeLam lstTypes 0 fnBody.

Definition eqOutcomeTp (A : Type) (eqfn : A -> A -> bool) (x: outcomePoly A) (y : outcomePoly A) : outcomePoly bool :=
match x with
| successPoly j => match y with
                    | successPoly k => if eqfn j k then (successPoly bool true) else (noMatchPoly bool) 
                    | noMatchPoly => noMatchPoly bool
                    | fuelErrorPoly => fuelErrorPoly bool
                   end
| fuelErrorPoly => fuelErrorPoly bool
| noMatchPoly =>  match y with
                    | fuelErrorPoly => fuelErrorPoly bool
                    | _ => noMatchPoly bool
                   end
end.                                                           


Definition typeToBoolEqOutcome (tpTm : term) (tpEqFn : term) : term := tApp <%eqOutcomeTp%> [tpTm; tpEqFn]. 

Definition compOutcomeBool (x : outcomePoly bool) (y : outcomePoly bool) : outcomePoly bool :=
match x with
 | fuelErrorPoly  => fuelErrorPoly bool
 | noMatchPoly => match y with
                   | fuelErrorPoly => fuelErrorPoly bool
                   | _ => noMatchPoly bool
                  end
 | successPoly true => match y with 
                        | successPoly true => successPoly bool true
                        | successPoly false => noMatchPoly bool
                        | noMatchPoly => noMatchPoly bool
                        | fuelErrorPoly => fuelErrorPoly bool
                       end
 | successPoly false => match y with
                         | fuelErrorPoly => fuelErrorPoly bool
                         | _ => noMatchPoly bool
                        end
end.  


Definition mkOutPolyProdTm (outVars : list (prod string term)) : term :=
tApp (mkJoinOutcomeTm (map snd outVars)) (map (fun e => tVar (fst e)) outVars).


Fixpoint mkLamTp (inVars : list (prod string term)) (fnBody : term) :=
match inVars with
| [] => fnBody

| h :: t => tLam (fst h) (snd h) (mkLamTp t fnBody)
end.

Fixpoint mkAnimatedFnNm (l : list (string * term)) : list (string * term) :=
match l with
| [] => []
| (s,tp) :: t => ((String.append s "AnimatedTopFn"), tp) :: mkAnimatedFnNm t
end.  


Definition splitOutcomePolyFst (A : Type) (B : Type) (x : outcomePoly (A * B)) : outcomePoly A :=
match x with
 | successPoly (a,b) => successPoly A a
 | noMatchPoly => noMatchPoly A
 | fuelErrorPoly => fuelErrorPoly A
end. 

Definition splitOutcomePolySnd (A : Type) (B : Type) (x : outcomePoly (A * B)) : outcomePoly B :=
match x with
 | successPoly (a,b) => successPoly B b
 | noMatchPoly => noMatchPoly B
 | fuelErrorPoly => fuelErrorPoly B
end.
                                 
