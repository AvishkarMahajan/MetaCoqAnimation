Require Import Coq.Lists.List.
Require Import List.
            
Require Import MetaCoq.Template.All.
Import monad_utils.MCMonadNotation.
(* Import MetaCoqNotations. *)


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
Compute <? option ?>.




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
     We should eventually consider making a MetaCoq_utils module. *)
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

   MetaCoq Run (t <- DB.deBruijn
                      (tLambda (mkBindAnn (nNamed "x") Relevant)
                                <% bool %> (tVar "x"))%string ;;
                t' <- tmUnquoteTyped (bool -> bool) t ;;
                tmPrint t).
  
Parameter prog' : list nat.
Parameter progBool : nat -> nat -> nat -> bool.

Definition boolFn (a b c : nat) : bool :=
 (progBool a b c) && (Nat.eqb (a + 2) (b + 3)).  *) 

End DB.

(* Require Import utils. *)

Open Scope bs.

Fixpoint inNatLst (a : nat) (l : list nat) : bool :=
 match l with
  | nil => false
  | (h :: t) => if (Nat.eqb h a) then true else (inNatLst a t)
 end.
 
Parameter g1 : nat -> nat.
Parameter g2 : nat -> nat. 
Parameter g3 : nat -> nat -> nat.

(* a, b designated as input, c d e designated as output *)
Inductive foo : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr : forall a b c d e, (e = b /\ d = c /\ c = (g3 a e) /\ g1 d = g2 a) -> foo a b c d e.


Check (tmQuoteInductive).
Print TemplateMonad.
Print one_inductive_body.
MetaCoq Run (t <- tmQuoteInductive <? foo ?> ;; tmPrint t).

Definition animate_conjunct
           (c : constructor_body) (conjunct : context_decl) : TemplateMonad named_term :=
  (* t is the MetaCoq term for the conjunct like (e = b /\ d = c /\ c = a + e) *) 
  let t : term := decl_type conjunct in
  (* tl here only works because we assume there is only one, large, nested "and" conjunct *)
  t_named <- DB.undeBruijn' (tl (map (fun arg => binder_name (decl_name arg)) (cstr_args c))) t ;;
  (* now you can work with the named representation, as you can see below: *)
  tmPrint t_named ;;
  ret hole.

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

MetaCoq Run (animate <? foo ?>).

Definition fooTerm : term := 
 (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "and"); inductive_ind := 0 |} [])
   [tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
      [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [];
       tVar "e"; tVar "b"];
    tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "and"); inductive_ind := 0 |} [])
      [tApp
         (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
         [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
            []; tVar "d"; tVar "c"];
       tApp
         (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "and"); inductive_ind := 0 |} [])
         [tApp
            (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
            [tInd
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
               []; tVar "c"; tApp (tConst (MPfile ["animationFullEx"], "g3") []) [tVar "a"; tVar "e"]];
          tApp
            (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
            [tInd
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
               []; tApp (tConst (MPfile ["animationFullEx"], "g1") []) [tVar "d"];
             tApp (tConst (MPfile ["animationFullEx"], "g2") []) [tVar "a"]]]]]).
 
            


Fixpoint isListSub (l1 l2 : list nat) : bool :=
 match l1 with
  | nil => true
  | (h :: t) => (inNatLst h l2) && (isListSub t l2)
 end. 

Fixpoint listConcat {A: Type} (l1 : list A) (l2 : list A) : list A :=
 match l1 with
  | nil => l2
  | (h :: t) => listConcat t (h :: l2)
 end. 
 

 



Definition lstCheckEmpty {A : Type} (l : list A) : bool :=
  match l with
  | nil => true
  | _ => false
  end.




 
Fixpoint listCombine {A : Type} (outerList : list (list A)) : list A :=
 match outerList with
  | nil => nil
  | l1 :: l2 => listConcat l1 (listCombine l2)
  
 end. 


 


Fixpoint isListSubStr (l1 l2 : list string) : bool. Admitted.
 




Fixpoint getListConj (bigConj : term) : (list term) := (* extract list of conjuncts from big conjunction *)
 match bigConj with
  |(tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "and"); inductive_ind := 0 |} []) ls) => 
         listCombine (map getListConj ls)
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} []) ls' => 
              [tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} []) ls']
  | _ => nil
 end. 


Fixpoint getListConjLetBind (bigConj : term) : (list term) := (* extract list of conjuncts from big conjunction *)
 match bigConj with
  |(tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "and"); inductive_ind := 0 |} []) ls) => 
         listCombine (map getListConjLetBind ls)
  
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tVar str2] => [tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tVar str2]]
  
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp (tConst (loc , fnStr) []) [tVar str2; tVar str3]] => [tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp (tConst (loc, fnStr) []) [tVar str2; tVar str3]]]
             
            
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp (tConst (loc, fnStr) []) [tVar str2]] => [tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp (tConst (loc, fnStr) []) [tVar str2]]]
  | _ => nil           
 end. 

Fixpoint getListConjGuardCon (bigConj : term) : (list term) := (* extract list of conjuncts from big conjunction *)
 match bigConj with
  |(tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "and"); inductive_ind := 0 |} []) ls) => 
         listCombine (map getListConjGuardCon ls)
  
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             [];
           tApp (tConst (loc1, fnStr1) [])
             [tVar varStr1];
           tApp (tConst (loc2, fnStr2) [])
             [tVar varStr2]] => [tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             [];
           tApp (tConst (loc1, fnStr1) [])
             [tVar varStr1];
           tApp (tConst (loc2, fnStr2) [])
             [tVar varStr2]]]
               
  | _ => nil           
 end. 

 

Definition extractOrderedVars (t : term) : (list string) := (* extract ordered list of vars from conjunct *)
 match t with 
 | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tVar str2] => [str1 ; str2]
 | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp (tConst (loc, fnStr) []) [tVar str2; tVar str3]] => [str1 ; str2 ; str3]
 

(* Combine the pattern matches to handle fns of arbirary arity *)
 | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp (tConst (loc, fnStr) []) [tVar str2]] => [str1 ; str2]

 | _ => nil
 end.


(* Instantiate partialLetFun with identity*)

Definition animateOneConjSucc (conj : term) (partialLetfn : term -> term) : option (term -> term) :=
 match conj with
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tVar str2] => Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |} 
            (tVar str2%bs)
            (tInd
               {|
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
                 inductive_ind := 0
               |} []) ) t))
  
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp (tConst (loc, fnStr) []) [tVar str2; tVar str3]] =>
             Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
         (tApp (tConst (loc, fnStr%bs) []) [tVar str2%bs; tVar str3%bs])
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
              inductive_ind := 0
            |} []) ) t))
            
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp (tConst (loc, fnStr) []) [tVar str2]] =>
             Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
         (tApp (tConst (loc, fnStr%bs) []) [tVar str2%bs])
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
              inductive_ind := 0
            |} []) ) t))         
     
  
  
  
  
  | _ => None
 end. 
 
(* Instantiate partialGuard with Identity * No need to check for known vars when animating guard condition since all
vars should be known at this point in the computation *)
 
 Definition animateOneConjSuccGuard (conj : term) (partialGuard : term ) : option term :=
  match conj with
   | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             [];
           tApp (tConst (loc1, fnStr1) [])
             [tVar varStr1];
           tApp (tConst (loc2, fnStr2) [])
             [tVar varStr2]] => 
               Some (tApp (tConst (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "andb"%bs) []) [partialGuard ; 
                         tApp (tConst (MPfile ["Nat"%bs; "Init"%bs; "Coq"%bs], "eqb"%bs) []) [tApp (tConst (loc1, fnStr1) [])
             [tVar varStr1];
           tApp (tConst (loc2, fnStr2) [])
             [tVar varStr2]]])
   | _ => None
 end.                       
               

 



Definition animateOneConj (conj : term) (knownVar : list string) (partialProg : term -> term) : option (list string × (term -> term)) :=
 if (isListSubStr (tl (extractOrderedVars conj)) knownVar) then 
  let t' := (animateOneConjSucc conj partialProg) in
    match t' with
     | Some t'' => Some ((listConcat knownVar (extractOrderedVars conj)), t'')
     | None => None
    end  
    
    else None.  



Fixpoint animateListConj (conjs : (list term)) (remConjs : (list term)) (knownVar : list string)
                           (fuel : nat) (partialProg : term -> term) : term -> term :=
 match fuel with 
  | 0 => partialProg
  | S n => match conjs with
           | nil => match remConjs with
                     | nil => partialProg
                     | lst => animateListConj lst nil knownVar n partialProg
                    end  
           | (h :: t) => let res := (animateOneConj h knownVar partialProg) in 
                             match res with
                              | Some res' => animateListConj t remConjs (fst res') n  (snd res')  
                              | None => animateListConj t (h :: remConjs) knownVar n partialProg 
                             end 
                         
           end
 end.                         

(* Construct final function of shape fun a b : nat => ... option ([c ; d ; e]) *)

Definition constrFn (letBind : term -> term) (guardCon : term) : term :=
 (tLambda {| binder_name := nNamed "a"%bs; binder_relevance := Relevant |} (tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} [])
   (tLambda {| binder_name := nNamed "b"%bs; binder_relevance := Relevant |} (tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} [])
    (letBind (tCase {| ci_ind := {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "bool"%bs); inductive_ind := 0 |}; ci_npar := 0; ci_relevance := Relevant |}
                  {|
                    puinst :=
                      puinst
                        {|
                          puinst := [];
                          pparams := [];
                          pcontext := [{| binder_name := nAnon; binder_relevance := Relevant |}];
                          preturn :=
                            tApp (tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "option"%bs); inductive_ind := 0 |} [])
                              [tApp (tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} [])
                                 [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []]]
                        |};
                    pparams := [];
                    pcontext :=
                      pcontext
                        {|
                          puinst := [];
                          pparams := [];
                          pcontext := [{| binder_name := nAnon; binder_relevance := Relevant |}];
                          preturn :=
                            tApp (tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "option"%bs); inductive_ind := 0 |} [])
                              [tApp (tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} [])
                                 [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []]]
                        |};
                    preturn :=
                      tApp (tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "option"%bs); inductive_ind := 0 |} [])
                        [tApp (tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} [])
                           [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []]]
                  |} (guardCon) [{|
                     bcontext :=
                       bcontext
                         {|
                           bcontext := [];
                           bbody :=
                             tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "option"%bs); inductive_ind := 0 |} 0 [])
                               [tApp (tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} [])
                                  [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []];
                                tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} 1 [])
                                  [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []; tRel 2;
                                   tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} 1 [])
                                     [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []; tRel 0;
                                      tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} 1 [])
                                        [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []; tRel 1;
                                         tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} 0 [])
                                           [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []]]]]]
                         |};
                     bbody :=
                       tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "option"%bs); inductive_ind := 0 |} 0 [])
                         [tApp (tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} [])
                            [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []];
                          tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} 1 [])
                            [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []; tVar "c"%bs;
                             tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} 1 [])
                               [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []; tVar "d"%bs;
                                tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} 1 [])
                                  [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []; tVar "e"%bs;
                                   tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} 0 [])
                                     [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []]]]]]
                   |};
                   {|
                     bcontext :=
                       bcontext
                         {|
                           bcontext := [];
                           bbody :=
                             tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "option"%bs); inductive_ind := 0 |} 1 [])
                               [tApp (tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} [])
                                  [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []]]
                         |};
                     bbody :=
                       tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "option"%bs); inductive_ind := 0 |} 1 [])
                         [tApp (tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs); inductive_ind := 0 |} [])
                            [tInd {| inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs); inductive_ind := 0 |} []]]
                   |}])))).

Fixpoint animateOneConjGuardList (conj : list term) : option term :=
 match conj with 
  | nil => Some (<% true %>)
  | h :: t => match (animateOneConjGuardList t) with 
               | Some gt => (animateOneConjSuccGuard h gt)
               | None => None
              end   
  end.

(*animateOneConjSuccGuard *)
  
Compute (animateOneConjGuardList (getListConjGuardCon fooTerm)).

(* animateListConj (conjs : (list term)) (remConjs : (list term)) (knownVar : list string)
                           (fuel : nat) (partialProg : term -> term) : term -> term := *)


Compute (animateListConj (getListConjLetBind fooTerm) nil ["a" ; "b"] 10 (fun t : term => t)).

(* Definition constrFnOpt (optLetBind : (option (term -> term))) (optGuardCon : option term) : option term :=
 match optLetBind with
  | Some t' => match optGuardCon with
                | Some t'' => Some (constrFn t' t'')
                | None => None
                end
  | None => None             
  end. *)
  
Compute (constrFn (animateListConj (getListConjLetBind fooTerm) nil ["a" ; "b"] 10 (fun t : term => t)) ( (tApp (tConst (MPfile ["Datatypes"; "Init"; "Coq"], "andb") [])
            [tConstruct
               {|
                 inductive_mind :=
                   (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                 inductive_ind := 0
               |} 0 [];
             tApp (tConst (MPfile ["Nat"; "Init"; "Coq"], "eqb") [])
               [tApp (tConst (MPfile ["animationFullEx"], "g1") []) [tVar "d"];
                tApp (tConst (MPfile ["animationFullEx"], "g2") []) [tVar "a"]]]))).  


                     
 



Definition animate' (t : term) : TemplateMonad (nat -> nat -> (option (list nat))) :=
  f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) (t) ;; tmPrint f ;; tmReturn f.
  



MetaCoq Run (animate' (constrFn (animateListConj (getListConjLetBind fooTerm) nil ["a" ; "b"] 10 (fun t : term => t)) ( (tApp (tConst (MPfile ["Datatypes"; "Init"; "Coq"], "andb") [])
            [tConstruct
               {|
                 inductive_mind :=
                   (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                 inductive_ind := 0
               |} 0 [];
             tApp (tConst (MPfile ["Nat"; "Init"; "Coq"], "eqb") [])
               [tApp (tConst (MPfile ["animationFullEx"], "g1") []) [tVar "d"];
                tApp (tConst (MPfile ["animationFullEx"], "g2") []) [tVar "a"]]])))).

     
     
     

 
    
 
