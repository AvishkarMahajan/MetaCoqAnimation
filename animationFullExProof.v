Require Import Coq.Lists.List.
Require Import List.


Require Import MetaCoq.Template.All.
Import monad_utils.MCMonadNotation.
(* Import MetaCoqNotations. *)

Require Import PeanoNat.
Local Open Scope nat_scope.


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
 (tApp <% and %>
   [tApp <% @eq %>
      [<% nat %>; tVar "e"; tVar "b"];
    tApp <% and %>
      [tApp
         <% @eq %>
         [<% nat %>; tVar "d"; tVar "c"];
       tApp
         <% and %>
         [tApp
            <% @eq %>
            [<% nat %>; tVar "c";
             tApp (tConst (MPfile ["animationFullExProof"], "g3") []) [tVar "a"; tVar "e"]];
          tApp
            <% @eq %>
            [<% nat %>; tApp (tConst (MPfile ["animationFullExProof"], "g1") []) [tVar "d"];
             tApp (tConst (MPfile ["animationFullExProof"], "g2") []) [tVar "a"]]]]]).

Fixpoint isListSub (l1 l2 : list nat) : bool :=
 match l1 with
  | nil => true
  | (h :: t) => (inNatLst h l2) && (isListSub t l2)
 end.

Fixpoint inStrLst (s : string) (l1 : list string) : bool :=
 match l1 with
  | nil => false
  | h :: t => if (String.eqb s h) then true else (inStrLst s t)
 end.

Fixpoint isListSubStr (l1 l2 : list string) : bool :=
 match l1 with
  | nil => true
  | h :: t => (inStrLst h l2) && (isListSubStr t l2)
 end.

(* String.eqb: string -> string -> bool *)


(*Fixpoint getListConj (bigConj : term) : (list term) := (* extract list of conjuncts from big conjunction *)
 match bigConj with
  |(tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "and"); inductive_ind := 0 |} []) ls) =>
         concat (map getListConj ls)
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} []) ls' =>
              [tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} []) ls']
  | _ => nil
 end. *)

(* Extracts list of conjuncts from big conjunction *)
Fixpoint getListConjLetBind (bigConj : term) : list term := 
 match bigConj with
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "and"); inductive_ind := 0 |} []) ls =>
    concat (map getListConjLetBind ls)

  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
         [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tVar str2] => [tApp <% @eq %>
          [<% nat %>; tVar str1; tVar str2]]

  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
         [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp fn [tVar str2; tVar str3]] =>
      [tApp <% @eq %>
          [<% nat %>; tVar str1; tApp fn [tVar str2; tVar str3]]]


  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
         [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp fn [tVar str2]] =>
      [tApp <% @eq %>
          [<% nat %>; tVar str1; tApp fn [tVar str2]]]
  | _ => nil
 end.

Fixpoint getListConjGuardCon (bigConj : term) : (list term) := (* extract list of conjuncts from big conjunction *)
 match bigConj with
  |(tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "and"); inductive_ind := 0 |} []) ls) =>
         concat (map getListConjGuardCon ls)

  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             [];
           tApp fn1
             [tVar varStr1];
           tApp fn2
             [tVar varStr2]] => [tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             [];
           tApp fn1
             [tVar varStr1];
           tApp fn2
             [tVar varStr2]]]

  | _ => nil
 end.

Compute (getListConjGuardCon fooTerm).



Definition extractOrderedVars (t : term) : (list string) := (* extract ordered list of vars from conjunct *)
 match t with
 | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tVar str2] => [str1 ; str2]
 | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp fn [tVar str2; tVar str3]] => [str1 ; str2 ; str3]


(* Combine the pattern matches to handle fns of arbirary arity *)
 | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp fn [tVar str2]] => [str1 ; str2]

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
             []; tVar str1; tApp fn [tVar str2; tVar str3]] =>
             Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
         (tApp fn [tVar str2%bs; tVar str3%bs])
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
              inductive_ind := 0
            |} []) ) t))

  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp fn [tVar str2]] =>
             Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
         (tApp fn [tVar str2%bs])
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
              inductive_ind := 0
            |} []) ) t))





  | _ => None
 end.

(* Instantiate partialGuard with Identity * No need to check for known vars when animating guard condition since all
vars should be known at this point in the computation *)

 Definition animateOneConjSuccGuard (conj : term) (partialGuard : term ) :  term :=
  match conj with
   | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             [];
           tApp fn1
             [tVar varStr1];
           tApp fn2
             [tVar varStr2]] =>
                (tApp (tConst (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "andb"%bs) []) [partialGuard ;
                         tApp (tConst (MPfile ["Nat"%bs; "Init"%bs; "Coq"%bs], "eqb"%bs) []) [tApp fn1
             [tVar varStr1];
           tApp fn2
             [tVar varStr2]]])
   | _ => <% false %>
 end.






Definition animateOneConj (conj : term) (knownVar : list string) (partialProg : term -> term) : option (list string × (term -> term)) :=
 if (isListSubStr (tl (extractOrderedVars conj)) knownVar) then
  let t' := (animateOneConjSucc conj partialProg) in
    match t' with
     | Some t'' => Some ((app knownVar (extractOrderedVars conj)), t'')
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

Fixpoint animateOneConjGuardList (conj : list term) : term :=
 match conj with
  | nil => (<% true %>)
  | h :: t => match (animateOneConjGuardList t) with
               | gt => (animateOneConjSuccGuard h gt)

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
  t' <- DB.deBruijn t ;; f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) t' ;; tmPrint f ;; tmReturn f.

Definition genFun (fooTerm : term) (inputVars : list string) (fuel : nat) : term :=
  constrFn
    (animateListConj
       (getListConjLetBind fooTerm) nil inputVars fuel (fun t : term => t))
    (animateOneConjGuardList (getListConjGuardCon fooTerm)). 


(* Definition soundness (f : (nat -> nat -> option (list nat))) : Type :=
  forall n1 n2 : nat,
    {l : (option (list nat)) |
     match l with
     | Some ([n3 ; n4 ; n5]) => (foo n1 n2 n3 n4 n5  /\ Some ([n3 ; n4 ; n5]) = f n1 n2)
     | None => ((forall n3 n4 n5 : nat, (foo n1 n2 n3 n4 n5 -> False)) /\ None = f n1 n2)
     | _   => False
     end}. *)


Definition soundness' (f : (nat -> nat -> option (list nat))) (n1 : nat) (n2 : nat) : Type :=
 let r := (f n1 n2) in 
   match r with
    | Some ([n3 ; n4 ; n5]) => (foo n1 n2 n3 n4 n5)
    | None =>  (forall n3 n4 n5 : nat, (foo n1 n2 n3 n4 n5 -> False))
    | _ => False
    end. 
Definition soundness'' (f : (nat -> nat -> option (list nat))) : Type :=
 forall n1 n2, soundness' f n1 n2 .       

(** Definition animate'' (kn : kername) (inputVars : (list string)) (fuel : nat) : TemplateMonad unit :=
  mut <- tmQuoteInductive kn ;;
  conjs <- (match ind_bodies mut with
             | [ one ] =>
               conjuncts <- collect_conjuncts (ind_ctors one) ;;
                (* sepConj <- tAppDes conjuncts ;; *)
                (* there has to be something clever here *)
                ret conjuncts
             | _ => tmFail "Not one type in mutually inductive block."
              end) ;;
  t' <- DB.deBruijn (genFun conjs inputVars fuel)  ;;
  f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) t' ;;
  tmPrint f ;;
  tmMsg "done". **)

Lemma beq_nat_eq : forall n m, true = (n =? m) -> n = m. Proof. Admitted.
Lemma beq_nat_neq : forall n m, false = (n =? m) -> (n = m -> False). Proof. Admitted.

Definition animate'' (conjs : term) (inputVars : (list string)) (fuel : nat) : TemplateMonad unit :=

  t' <- DB.deBruijn (genFun conjs inputVars fuel)  ;;
  f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) t' ;;
  lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;;
  tmMsg "done".



MetaCoq Run (animate'' fooTerm ["a" ; "b"] 10).


Next Obligation.
Proof. unfold soundness'. (* exists ((fun n1 n2 => if Nat.eqb (g1 (g3 n1 n2)) (g2 n1) then Some [g3 n1 n2; g3 n1 n2; n2] else None) n1 n2). *)
remember (Nat.eqb (g1 (g3 n1 n2)) (g2 n1)) as H. destruct H.
+ split.
++ (*apply cstr.*) apply beq_nat_eq in HeqH. rewrite -> HeqH.
auto. 
+ intros. inversion H ; subst. apply beq_nat_neq in HeqH.
*  auto.
* destruct H0. rewrite H0 in H1. destruct H1.
rewrite H1 in H2. destruct H2. rewrite H2 in H3. auto.
 Qed.



(* Definition isSome {A : Type} (y : (option A)) : bool := 
 match y with
  | Some z => true
  | None => false
 end.  

Fixpoint trySucc {A : Type} {B : Type} (x : A) (lstFn : list (A -> (option B))) : option B :=
 match lstFn with 
  | [] => None
  | [elt] => elt x
  | (h :: t) => if (isSome (h x)) then (h x) else trySucc x t
 end.  

Definition trySuccFn {A : Type} {B : Type} (lstFn : list (A -> (option B))) : (A -> (option B)) :=
 fun x => trySucc x lstFn. *)
 
(* Parameter typeCstr : Type -> Type -> Type. *)


(* Inductive fooCon : (typeCstr nat nat) -> nat -> nat -> Prop :=
 | cstrCon : forall a b c, [b ; c] = a -> fooCon a b c. *)


Parameter f1 : nat -> nat.
Parameter f2 : nat -> nat.

Inductive fooCon : nat -> nat -> nat -> nat -> Prop :=
 | cstrCon : forall a b c d,  f1 a = f2 b  -> fooCon a b c d.



MetaCoq Run (animate <? fooCon ?>).
 

 
 

(* Fixpoint deconTypeCon (conj : term) : list (option string) :=
 match conj with
  | tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list"); inductive_ind := 0 |} 1 [])
      ((tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} []) ::
       (tVar str :: [rest])) => (Some str :: deconTypeCon rest)
  | _ => [None] 
  end. 
  
Fixpoint deconTypeConGen (conj : term) : list (option string) :=
 match conj with
  | tApp
      (tConstruct
         tc1 tc2 tc3)
      [tVar str] => [Some str] 
  
  | tApp
      (tConstruct
         tc1 tc2 tc3)
      (tInd x y :: (tVar str :: [rest])) => (Some str :: deconTypeConGen rest)
  
  | tApp
      (tConstruct
         tc1 tc2 tc3)
      (tInd x y :: (rest')) => (concat (map deconTypeConGen rest'))    
  
  | _ => [None] 
  end. *)
 

Fixpoint deconTypeConGen' (t1 : list term) (t2 : list term) (fuel : nat) : list (list term) :=
 match fuel with
  | 0 => [t1 ; t2]
  | S m => match t1 with
            | [tApp (tConstruct x y z) l] => match t2 with
                                               | [tApp (tConstruct x y z) l'] => deconTypeConGen' l l' m
                                               | _ => [t1 ; t2]
                                              end
  
            | tInd x y :: rest => match t2 with
                                   | tInd x y :: rest' => deconTypeConGen' rest rest' m
                                   | _ => [t1 ; t2] 
                                   end
                                                         
  
            | [tVar str1] => [t1 ; t2] 
  
            | _ => [t1 ; t2]
           end
 end.

Check concat. 


Fixpoint deconTypeConGen'' (t1 : list term) (t2 : list term) (fuel : nat) : list (list term) :=
 match fuel with
  | 0 => [t1 ; t2]
  | S m => match t1 with
            | tApp (tConstruct x y z) l :: rest => match t2 with
                                                    | tApp (tConstruct x y z) l':: rest' => 
                                                                   deconTypeConGen'' (l ++ rest) (l' ++ rest') m
                                                    | h :: rest' => [tApp (tConstruct x y z) l] :: ([h] :: (deconTypeConGen'' rest rest' m)) 
                                                    | _ => [t1 ; t2]
                                                    end
  
            | tInd x y :: rest => match t2 with
                                   | tInd x y :: rest' => deconTypeConGen'' rest rest' m
                                   | h :: rest' => ([tInd x y] ::  ([h] :: (deconTypeConGen'' rest rest' m )))
                                   | _ => [t1 ; t2] 
                                   end
                                                         
  
            | tVar str1 :: rest => match t2 with
                                    | h :: rest' => ([tVar str1] :: ([h] :: (deconTypeConGen'' rest rest' m)))
                                    | _ => [t1 ; t2] 
                                   end 
  
            | (h1 :: rest1) => match t2 with
                                | h2 :: rest2 => ([h1] :: ([h2] :: (deconTypeConGen'' rest1 rest2 m)))
                                | _ => [t1 ; t2] 
                               end 
            
            | _ => [t1 ; t2]
           end
 end.



  

(* Compute (deconTypeConGen ( tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list"); inductive_ind := 0 |} 1 [])
      [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [];
       tApp
         (tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 1
            []) [tVar "a"];
       tApp
         (tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list"); inductive_ind := 0 |} 1
            [])
         [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
            [];
          tApp
            (tConstruct
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
               1 []) [tVar "b"];
          tApp
            (tConstruct
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list"); inductive_ind := 0 |}
               0 [])
            [tInd
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
               []]]])). *)

Definition deConConj1 (t : term) : (list term) :=
 match t with
  | (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} []) (h :: (t1 :: t2))) 
                   => [t1]
  | _ => nil
 end.  

Definition deConConj2 (t : term) : (list term) :=
 match t with
  | (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} []) (h :: (t1 :: (t2 :: t3)))) 
                   => [t2]
  | _ => nil
 end. 
 
(* trialTerm = Inductive fooCon : nat -> nat -> nat -> nat -> Prop :=
 | cstrCon : forall a b c d,  f1 a = f2 b  -> fooCon a b c d. *)
Definition trialTerm : term :=
 (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
   [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [];
    tApp (tConst (MPfile ["animationFullExProof"], "f1") []) [tVar "a"];
    tApp (tConst (MPfile ["animationFullExProof"], "f2") []) [tVar "b"]]).

 


(* trial2 = Inductive fooCon : nat -> nat -> nat -> nat -> Prop :=
 | cstrCon : forall a b c d,  [1 ; S c]  = [S b ; d]  -> fooCon a b c d.
*)

Definition trial2 : term :=
(tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
   [tApp
      (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list"); inductive_ind := 0 |} [])
      [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} []];
    tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list"); inductive_ind := 0 |} 1 [])
      [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [];
       tApp
         (tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 1
            [])
         [tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 0
            []];
       tApp
         (tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list"); inductive_ind := 0 |} 1
            [])
         [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
            [];
          tApp
            (tConstruct
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
               1 []) [tVar "c"];
          tApp
            (tConstruct
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list"); inductive_ind := 0 |}
               0 [])
            [tInd
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
               []]]];
    tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list"); inductive_ind := 0 |} 1 [])
      [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [];
       tApp
         (tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 1
            []) [tVar "b"];
       tApp
         (tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list"); inductive_ind := 0 |} 1
            [])
         [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
            []; tVar "d";
          tApp
            (tConstruct
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list"); inductive_ind := 0 |}
               0 [])
            [tInd
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
               []]]]]).




Compute (deconTypeConGen'' (deConConj1 trialTerm) (deConConj2 trialTerm) 10). 

(* Fixpoint makeConj (l1 : list (list term)) : list term :=
 match l1 with
  | nil => nil
  | [_h] => nil
  | [tVar str1] :: ([tVar str2] :: t) => (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
   [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [];
    tVar str1; tVar str2]) :: (makeConj t)
  
  
  | [tVar str1] :: ([tApp (tConstruct
                         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 1
                            []) y] :: t) => 
                              (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
                              [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [];
                              tVar str1;
                              tApp
                                (tConstruct
                                    {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 1 [])
                                         y]) :: makeConj t
  
  
  |([tApp (tConstruct
                         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 1
                            []) y] :: ([tVar str1] :: t)) => 
                            (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
                              [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [];
                              tVar str1;
                              tApp
                                (tConstruct
                                    {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 1 [])
                                         y]) :: makeConj t
  
  
  | ([h1]) :: (([h2]) :: t) =>
                          (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
                          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [];
                          h1;
                          h2]) :: makeConj t  (* Is this clause too general?*)

  | ([]) :: (([]) :: t) => makeConj t                            
  
  | _ => nil
 end. *)

(* Check @nil (term). *)


Fixpoint makeConjSimpl (l1 : list (list term)) : list term :=
 match l1 with
  | nil => nil
  | [_h] => nil
  | ([h1]) :: (([h2]) :: t) =>
                          (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
                          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [];
                          h1;
                          h2]) :: makeConjSimpl t (* Is this clause too general *)
                          
  | ([]) :: (([]) :: t) => makeConjSimpl t
  | _ => nil                        

 end.
 
Compute (makeConjSimpl (deconTypeConGen'' (deConConj1 trial2) (deConConj2 trial2) 20)).  


Definition deCons (a : nat) : list nat :=
 let r := [a ; 2] in 
 match r with 
 | [S c ; S d] => [c ; d]
 | _ => []
 end.

Definition deCons' (x : (list nat)) : list nat :=
 let r := x in
 match r with
 | [S c ; S d] => [c ; d]
 | _ => []
 end.

(* Error 
Definition deCons'' (x : (list nat)) : list nat :=
 let [a ; b] := x in [b ; a]. *) 

Check list.
Check (cons nat). 

Parameter consFn : nat -> nat.

Definition deCons'' (x : nat) : option nat :=
 match x with
 | S c => Some c 
 | _ => None
 end.
 
MetaCoq Quote Definition t := (fun x => match x with
                                        | S c => Some c
                                        | _ => None
                                       end).
MetaCoq Run (t' <- DB.undeBruijn t ;; tmPrint t'). 


(*Parameter myType2 : Type.*)

Inductive myType : Set :=
| mycr2 : nat -> myType
| mycr4 : string -> nat -> myType
| mycr1 : string -> nat -> myType
| mycr3 : myType. 


Parameter str1 : string.
Parameter str2 : string.
Parameter str3 : string.
Parameter fstr : forall A : Type, list A -> string.




(* Pattern match for 0 element list*) 

MetaCoq Quote Definition u0 := (fun myList => match myList with
                                                | []  =>  Some myList 
                                                | y :: l => None
                                                
                                                end).                                              
(* MetaCoq Run (t''' <- DB.undeBruijn t'' ;; tmPrint t'''). *)

Print u0.

(* Pattern match for 1 element list *)
MetaCoq Quote Definition u1 := (fun myList => match myList with
                                                | []  =>  None 
                                                | y0 :: l0 => match l0 with
                                                             | [] => Some myList
                                                             | y :: l => None
                                                             end 
                                                
                                                end).
Print u1.


(* Pattern match for 2 element list *)
MetaCoq Quote Definition u2 := (fun myList => match myList with
                                                | []  =>  None 
                                                | y1 :: l1 => match l1 with
                                                             | [] => None
                                                             | y0 :: l0 => match l0 with
                                                                            | [] => Some (myList)
                                                                            | y :: l => None
                                                                           end 
                                                             end 
                                                
                                                end).
Print u2.


MetaCoq Run (u2' <- DB.undeBruijn u2 ;; tmPrint u2'). 



(* Compare u0 and u1 and u2 *) 

MetaCoq Quote Definition t2 := (fun m P (PO : P 0) (PS : forall n, P (S n)) => 
                                   match m as n return P n with
                                    | 0 => PO
                                    | S n => PS n
                                    end).
MetaCoq Run (t2' <- DB.undeBruijn t2 ;; tmPrint t2'). 

Print bcontext.


(* (fun x => match x with
                                        | mycr1 a  =>  a 
                                        | _ => 0
                                       end). *)

Definition myTypeFnTerm := 
 (tLambda {| binder_name := nNamed "x"; binder_relevance := Relevant |}
   (tInd {| inductive_mind := (MPfile ["animationFullExProof"], "myType"); inductive_ind := 0 |} [])
   (tCase
      {|
        ci_ind :=
          {| inductive_mind := (MPfile ["animationFullExProof"], "myType"); inductive_ind := 0 |};
        ci_npar := 0;
        ci_relevance := Relevant
      |}
      {|
        puinst :=
          puinst
            {|
              puinst := [];
              pparams := [];
              pcontext := [{| binder_name := nNamed "x"; binder_relevance := Relevant |}];
              preturn :=
                tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0
                  |} []
            |};
        pparams := [];
        pcontext :=
          pcontext
            {|
              puinst := [];
              pparams := [];
              pcontext := [{| binder_name := nNamed "x"; binder_relevance := Relevant |}];
              preturn :=
                tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0
                  |} []
            |};
        preturn :=
          tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
            []
      |} (tVar "x")
      [{|
         bcontext :=
           bcontext
             {|
               bcontext := [{| binder_name := nNamed "a"; binder_relevance := Relevant |}];
               bbody := tRel 0
             |};
         bbody := tVar "a"
       |};
       {|
         bcontext :=
           bcontext
             {|
               bcontext := [{| binder_name := nNamed "n"; binder_relevance := Relevant |}];
               bbody :=
                 tConstruct
                   {|
                     inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0
                   |} 0 []
             |};
         bbody :=
           tConstruct
             {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} 0
             []
       |}])).




Inductive baz : nat -> myType -> string -> Prop :=
 | bazCon : forall (a : nat), forall (x : myType), forall (b : string), mycr1 b a = x -> baz a x b.  (*RHS of equality not v imp*)
 
Print TemplateMonad.

MetaCoq Quote Recursively Definition bazTerm := baz.

Print bazTerm. 

Print program.
Print global_env.
Print global_decl.

Parameter error : kername × global_decl.


Parameter error2 : one_inductive_body.

Parameter error3 : constructor_body.

Print one_inductive_body.

Check tl.

Definition extractIndDecl (x : global_decl) : option mutual_inductive_body :=
 match x with
  | InductiveDecl y => Some y
  | _ => None
 end.
Compute (option_map ind_ctors (option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (tl (tl ((declarations (fst bazTerm))))))))))).

(* Compute (option_map cstr_type (option_map (hd error3) (option_map ind_ctors(option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (declarations (fst bazTerm)))))))))). *)

Compute (option_map cstr_args (option_map (hd error3) (option_map ind_ctors(option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (declarations (fst bazTerm)))))))))).
(* 1st and 3rd computations should have all info needed to build patternmatch fn *)

MetaCoq Quote Definition con3 := (fun x => match x with
                                                | mycr1 a b  =>  Some (a, b)
                                                | _ => None
                                               end).
Print con3. 

MetaCoq Run (animate <? baz ?>).

Fixpoint lstPatternmatch {A : Type} (n : nat) (x : (list A)) : option (list A) :=
 match n with
 | 0 => match x with 
        | [] => Some x
        | _ => None
        end
 
 | S m => match x with
           | [] => None
           | (h :: t) => let r := lstPatternmatch m t in match r with
                                                            | Some l' => Some (h :: l')
                                                            | None => None
                                                            end
           
           end                         
  end.


Compute (lstPatternmatch 4 [1 ; 2 ; 3 ; 4]).




                                                                               
                                         
  
            
 

     
  
   

