From Stdlib Require Import List.

Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.

Require Import Animation.utils.
Import MetaRocqNotations.

Require Import PeanoNat.
Local Open Scope nat_scope.
Open Scope bs.

Notation "<?and?>" := (MPfile ["Logic"; "Init"; "Corelib"], "and").
Notation "<?eq?>" := (MPfile ["Logic"; "Init"; "Corelib"], "eq").
Notation "<?nat?>" := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat").
Notation "<%and%>" := (tInd {| inductive_mind := <?and?>; inductive_ind := 0 |} []).
Notation "<%eq%>" := (tInd {| inductive_mind := <?eq?>; inductive_ind := 0 |} []).
Notation "<%nat%>" := (tInd {| inductive_mind := <?nat?>; inductive_ind := 0 |} []).

(* 
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
  ret tt. *) 
  
(* MetaRocq Run (t <- tmQuote ((fun x : nat => match x with
                                            | S y  => Some [y; y]
                                            | _ => None  
                                            end))  ;; t' <- DB.undeBruijn t ;; tmPrint t').*)  




Module animateEqual.



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


(* Extracts list of conjuncts from big conjunction *)
Fixpoint getListConjLetBind (bigConj : term) : list term := 
  match bigConj with
  | tApp <%and%> ls => concat (map getListConjLetBind ls)

  | tApp <%eq%> [<%nat%>; tVar str1; tVar str2] => [tApp <% @eq %> [<%nat%>; tVar str1; tVar str2]]

  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn lst] =>
      [tApp <%eq%> [<%nat%>; tVar str1; tApp fn lst]]
  
  | tApp <%eq%> [<%nat%>; tApp fn lst; tVar str1] =>
      [tApp <%eq%> [<%nat%>; tApp fn lst; tVar str1]]    

  (*| tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2]] =>
      [tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2]]] *)
  | _ => []
 end.

(* extract list of conjuncts from big conjunction *)
Fixpoint getListConjGuardCon (bigConj : term) : list term := 
  match bigConj with
  | tApp <%and%> ls => concat (map getListConjGuardCon ls)
  | tApp <%eq%> [<%nat%>; tApp fn1 lst1; tApp fn2 lst2] =>
      [tApp <%eq%> [<%nat%>; tApp fn1 lst1; tApp fn2 lst2]] 
  | _ => []
 end.

(*Compute (getListConjGuardCon fooTerm).*)

Fixpoint extractOrderedVarsHelper (ls : list term) : list string :=
 match ls with 
 | [] => []
 | (tVar str) :: t => str :: (extractOrderedVarsHelper t)
 | _ :: t => (extractOrderedVarsHelper t)
 end. 
 


(* extract ordered list of vars from conjunct *)
Definition extractOrderedVars (t : term) : list string := 
  match t with
  | tApp <%eq%> [<%nat%>; tVar str1; tVar str2] => [str1 ; str2]
  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn lst] => str1 :: extractOrderedVarsHelper (lst)
  | tApp <%eq%> [<%nat%>; tApp fn lst; tVar str1] => app (extractOrderedVarsHelper (lst)) [str1]
  
  (* Combine the pattern matches to handle fns of arbitrary arity *)
  
  | _ => nil
  end.


(* Instantiate partialLetFun with identity *)

Definition animateOneConjSucc (conj : term) (partialLetfn : term -> term) : option (term -> term) :=
  match conj with
  | tApp <%eq%> [<%nat%>; tVar str1; tVar str2] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1; binder_relevance := Relevant |}
                                 (tVar str2) <%nat%>) t))

  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2; tVar str3; tVar str4; tVar str5 ]] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn [tVar str2; tVar str3; tVar str4; tVar str5]) <%nat%>) t))

  (*| tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2]] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn [tVar str2]) <%nat%>) t)) *)
  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn lstTerm] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn lstTerm) <%nat%>) t))
  
  | _ => None
 end.
 
Definition flipConj (conj : term) : term :=
 match conj with
  | tApp <%eq%> [<%nat%>; tVar str1; tVar str2] => tApp <%eq%> [<%nat%>; tVar str2; tVar str1] 
  | tApp <%eq%> [<%nat%>; tApp fn lstTerm; tVar str1] => tApp <%eq%> [<%nat%>; tVar str1; tApp fn lstTerm]
  | t' => t'
 end. 

(* Instantiate partialGuard with Identity * No need to check for known vars when animating guard condition since all
vars should be known at this point in the computation *)

 Definition animateOneConjSuccGuard (conj : term) (partialGuard : term) :  term :=
  match conj with
  | tApp <%eq%> [<%nat%>; tApp fn1 lstStr1; tApp fn2 lstStr2] =>
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (tConst <? Nat.eqb ?> []) [tApp fn1 lstStr1
         ; tApp fn2 lstStr2]]
  | _ => <% false %>
  end.

Definition animateOneConj (conj : term) (knownVar : list string) (partialProg : term -> term) : option (list string * (term -> term)) :=
  if isListSubStr (tl (extractOrderedVars conj)) knownVar then
  (let t' := animateOneConjSucc conj partialProg in
    match t' with
    | Some t'' => Some (app knownVar (extractOrderedVars conj), t'')
    | None => None
    end)
  else (if isListSubStr (tl (extractOrderedVars (flipConj conj))) knownVar then
          (let t' := animateOneConjSucc (flipConj conj) partialProg in
           match t' with
            | Some t'' => Some (app knownVar (extractOrderedVars (flipConj conj)), t'')
            | None => None
           end) 
         else None).   
 


Fixpoint animateListConj (conjs : (list term)) (remConjs : (list term)) (knownVar : list string)
                         (fuel : nat) (partialProg : term -> term) : term -> term :=
  match fuel with
  | 0 => partialProg
  | S n =>
    match conjs with
    | [] =>
      match remConjs with
      | [] => partialProg
      | lst => animateListConj lst nil knownVar n partialProg
      end
    | h :: t =>
      let res := animateOneConj h knownVar partialProg in
      match res with
      | Some res' => animateListConj t remConjs (fst res') n (snd res')
      | None => animateListConj t (h :: remConjs) knownVar n partialProg
      end
    end
  end.

(* Construct final function of shape fun a b : nat => ... option ([c ; d ; e]) *)

Fixpoint constrFnStart (inputVars : list string) : term -> term :=
 match inputVars with
 | [] => fun t : term => t
 | str :: rest => fun t => tLambda {| binder_name := nNamed str %bs; binder_relevance := Relevant |} <%nat%> ((constrFnStart rest) t)
 end.

Fixpoint constrRetBodylst (outputVars : list string) : term :=
 match outputVars with
  | [] => tApp (tConstruct {| inductive_mind := <? list ?>; inductive_ind := 0 |} 0 [])
                                     [<%nat%>]
(*| [str] => tApp (tConstruct {| inductive_mind := <? list ?>; inductive_ind := 0 |} 1 [])
                                  [<%nat%>; tVar str;
                                   tApp (tConstruct {| inductive_mind := <? list ?>; inductive_ind := 0 |} 0 [])
                                     [<%nat%>]] *)
  | str' :: rest =>  tApp (tConstruct {| inductive_mind := <? list ?>; inductive_ind := 0 |} 1 [])
                               [<%nat%>; tVar str'; constrRetBodylst rest] 
 end.                                                               

Definition constrFn (inputVars : list string) (outputVars : list string) (letBind : term -> term) (guardCon : term) : term :=
 (constrFnStart inputVars) (letBind (tCase {| ci_ind := {| inductive_mind := <? bool ?>; inductive_ind := 0 |}
                ; ci_npar := 0; ci_relevance := Relevant |}
               {| puinst := []
                ; pparams := []
                ; pcontext := [{| binder_name := nAnon; binder_relevance := Relevant |}]
                ; preturn := tApp <% @option %> [tApp <% @list %> [<%nat%>]]
                |}
                guardCon
                [{| bcontext := []
                  ; bbody :=
                       tApp (tConstruct {| inductive_mind := <? option ?>; inductive_ind := 0 |} 0 [])
                         [tApp <% @list %> [<%nat%>];
                          (constrRetBodylst outputVars)]
                   |};
                   {| bcontext := []
                    ; bbody :=
                       tApp (tConstruct {| inductive_mind := <? option ?>; inductive_ind := 0 |} 1 [])
                         [tApp <% @list %> [<%nat%>]]
                   |}])). 




Fixpoint animateOneConjGuardList (conj : list term) : term :=
  match conj with
  | [] => <% true %>
  | h :: t =>
    match animateOneConjGuardList t with
    | gt => animateOneConjSuccGuard h gt
    end
  end.


Definition genFun (fooTerm : term) (inputVars : list string) (outputVars : list string) (fuel : nat) : term :=
  constrFn inputVars outputVars
    (animateListConj
       (getListConjLetBind fooTerm) nil inputVars fuel (fun t : term => t))
    (animateOneConjGuardList (getListConjGuardCon fooTerm)). 


Definition soundness' (f : (nat -> nat -> option (list nat))) (induct : nat -> nat -> nat -> nat -> nat -> Prop) (n1 : nat) (n2 : nat) : Type :=
 let r := (f n1 n2) in 
   match r with
    | Some ([n3 ; n4 ; n5]) => (* forall h1, forall h2, forall h3, h1 = g1 -> h2 = g2 -> h3 = g3 -> *) (induct n1 n2 n3 n4 n5) 
    | None => (forall n3 n4 n5 : nat, (induct n1 n2 n3 n4 n5 -> False))
 (*  (forall n3 n4 n5 : nat, (foo n1 n2 n3 n4 n5 -> False)) *)
    | _ => False
    end. 
Definition soundness'' (f : (nat -> nat -> option (list nat))) (induct : nat -> nat -> nat -> nat -> nat -> Prop) : Type :=
 forall n1 n2, soundness' f induct n1 n2 .
 

(* Check foo. 
Check soundness''. *) 
 
  
Definition animate'' (kn : kername) (induct : nat -> nat -> nat -> nat -> nat -> Prop)  (inputVars : (list string)) (outputVars : list string) (fuel : nat) : TemplateMonad unit :=
  conjs <- general.animate2 kn ;;
  t' <- DB.deBruijn (animateEqual.genFun conjs inputVars outputVars fuel)  ;; 
  f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) t' ;; tmPrint f ;; tmDefinition (String.append (snd kn) "Fn") f ;;
  lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f induct) ;;
  tmMsg "done".
      


Definition justAnimate (kn : kername) (inputVars : (list string)) (outputVars : list string) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
  conjs <- general.animate2 kn ;;
  t' <- DB.deBruijn (animateEqual.genFun conjs inputVars outputVars fuel)  ;; 
  f <- tmUnquote t' ;;
  (*tmPrint f ;;*)
  tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
  (* lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;; *)
  tmMsg "done". 

End animateEqual.


Module typeConstrPatMatch.

Definition extractIndDecl (x : global_decl) : option mutual_inductive_body :=
 match x with
  | InductiveDecl y => Some y
  | _ => None
 end.
 
Parameter error : kername × global_decl.


Parameter error2 : one_inductive_body.

Parameter error3 : constructor_body.

Parameter error4 : context_decl.
Parameter termErr : term.



Definition extractTypeData (p : program) : list (option mutual_inductive_body) := 
 (map extractIndDecl ((map snd ((tl (tl (declarations (fst p)))))))).

Definition extractPatMatData (p : program) : term :=
 let r := 
     (option_map decl_type (option_map (hd error4) (option_map cstr_args (option_map (hd error3) (option_map ind_ctors (option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (declarations (fst p)))))))))))) in
     match r with
      | Some x => x
      | None => termErr
     end.    
(* 1st and 3rd computations should have all info needed to build patternmatch fn *)



Definition genVar (n : nat) : string :=
 String.append "v" (string_of_nat (n)).

Fixpoint genVarlst (s : nat) (ls : list term) : list (string × term) :=
 match ls with
  | [] => []
  | h :: t => ((genVar (s + 1)), h) :: (genVarlst (s + 1) t)
 end.   
 


Definition unfoldConsStep (i : nat) (currTs : list (string × term)) (resolvedTs : list ((string × term) × list string)) 
       (remTs :list (string × term)) : (((nat ×  list (string × term)) × 
                                       list ((string × term) × list string)) × list (string × term))  :=
 match currTs with
 | [] => (i, remTs, resolvedTs, nil)
 | (str, ((tApp (tConstruct typeInfo cstrInd ls') args)))  :: t => (i + (length args), t, ((str, (tConstruct typeInfo cstrInd ls'), (map fst (genVarlst i args))) :: resolvedTs), (app (genVarlst i args)  remTs))
 | (str, (tRel k)) :: t => (i, t, (((str, (tRel k), nil)) :: resolvedTs), remTs)
 | (str, (tVar varStr)) :: t => (i, t, (((str, (tVar varStr ), nil)) :: resolvedTs), remTs)
 (*| (str, (tApp (tInd indType ls') args)) :: t => (i + (length args), t, ((str, (tInd indType ls'), (map fst (genVarlst i args))) :: resolvedTs), (app (genVarlst i args) remTs)) *)
 | (str, (tConstruct typeInfo k [])) :: t => (i, t, (((str, (tConstruct typeInfo k []), nil)) :: resolvedTs), remTs)
 | (str, (tApp <%eq%> args)) :: t => (i + (length args), t, ((str, (<%eq%>), (map fst (genVarlst i args))) :: resolvedTs), (app (genVarlst i args)  remTs)) 

 | (str, (tApp func args)) :: t => (i, t, (((str, (tApp func args), nil)) :: resolvedTs), remTs)           
 
 (*| (str, (tApp func args)) :: t => (i + (length args), t, ((str, (func), (map fst (genVarlst i args))) :: resolvedTs), (app (genVarlst i args)  remTs)) *)
 | (str, (tInd indType ls')) :: t => (i, t, (((str, (tInd indType ls'), nil)) :: resolvedTs), remTs)
 | (str, _) :: t => (i, t, resolvedTs, remTs) 
 end. 
 
Fixpoint unfoldConsStepIter (fuel : nat) (st : (((nat ×  list (string × term)) × 
                                       list ((string × term) × list string)) × list (string × term))) : (((nat ×  list (string × term)) × 
                                       list ((string × term) × list string)) × list (string × term)) :=
  match fuel with
   | 0 => st
   | S m => unfoldConsStepIter m (unfoldConsStep  (fst (fst (fst st))) (snd (fst (fst st))) (snd (fst st)) (snd st))
 end.  

Definition preProcCons (fuel : nat) (t : term) :=
 rev (snd (fst (unfoldConsStepIter fuel (0, [("x"%bs, t)], [], [])))).
 


Definition reduce2 (x : nat) : (option nat) :=
 match x with
  | S m => match m with
            | S n => Some n
            | _ => None
           end
  | _ => None
 end.           




 



Definition preProcConsRem (fuel : nat) (t : term) : bool :=
 let r := app (snd ((unfoldConsStepIter fuel (0, [("x"%bs, t)], [], [])))) (snd (fst (fst (unfoldConsStepIter fuel (0, [("x"%bs, t)], [], []))))) in
  match r with
  | [] => true
  | _ => false
  end.
   
     
 


(* Print bazTerm. *)

Fixpoint lookUpVarsOne (str : string) (ls : list ((string × term) × list string)) : list string × list term :=
 match ls with
  | [] => ([], [])
  | (h :: t) => if (String.eqb str (fst (fst h))) then (let t := snd (fst h) in 
                                                         match t with
                                                          | tConstruct typeInfo k js => ([str], [])
                                                          | tApp (tInd typeInfo js) args => ([], [tApp (tInd typeInfo js) args])
                                                          | tRel k => ([str], [])
                                                          | tVar str'' => ([str], [])
                                                          | tInd typeInfo js => ([], [(tInd typeInfo js)])
                                                          | _ => ([], [])
                                                         end) 
                                                         else lookUpVarsOne str t
 end.

Fixpoint lookUpVars (lsStr : list string) (ls : list ((string × term) × list string)) : list string × list term :=
 match lsStr with
  | [] => ([], [])
  | (h :: t) => match lookUpVarsOne h ls with
                 | ([], []) => lookUpVars t ls
                 | ([e], []) => (e :: (fst (lookUpVars t ls)), snd (lookUpVars t ls))
                 | ([], [e]) => (fst (lookUpVars t ls),  e :: (snd (lookUpVars t ls)))
                 | _ => lookUpVars t ls
                end
 end.                                                               

Fixpoint preProcConsTypeVar (ls : list ((string × term) × list string)) (ls' : list ((string × term) × list string)) : 
                                     list (((string × term) × list string) × list term) :=
  match ls' with
   | [] => []
   | (str1, <%eq%>, lstStr) :: t => preProcConsTypeVar ls t
   | (str1, (tConstruct typeInfo k js), lstStr) :: t => 
          (str1, (tConstruct typeInfo k js), fst (lookUpVars lstStr ls), snd (lookUpVars lstStr ls)) :: preProcConsTypeVar ls t   
   | (_ :: t) => preProcConsTypeVar ls t
  end. 


      
 


Fixpoint genBinderNameList (n : nat) : list (binder_annot name) :=
 match n with 
  | 0 => []
  | S m => {| binder_name := nNamed (String.append "n" (string_of_nat (S m))) ; binder_relevance := Relevant |} :: genBinderNameList m
 end. 

Fixpoint genBinNmLsStr (ls : list string) : list (binder_annot name) :=
 match ls with
  | [] => []
  | h :: t => {| binder_name := nNamed h ; binder_relevance := Relevant |} :: genBinNmLsStr t
 end. 



Definition mkNoneBr (cstrArity : nat) (noneVal : term) : branch term :=
  {|
    bcontext :=
    genBinderNameList cstrArity;
    bbody :=
    noneVal
      |}. 

Definition getDeclName (i : nat) (cxt : list context_decl) : option (binder_annot name) :=
 match (nth_error cxt (i + 1)) with
  | Some r => Some (decl_name r)
  | _ => None
 end. 
(* Compute (nth_error [1;2;3] 0). *)       
 
Fixpoint genBinderannot (ind : list term) (cxt : list context_decl) : option (list (binder_annot name)) :=
 match ind with
  | [] => Some ([])
  | (tRel j :: t) => match (getDeclName j cxt) with
                       | Some b => match (genBinderannot t cxt) with
                                   | Some bs => Some (b :: bs)
                                   | None => None 
                                  end 
                       | _ => None
                       end
  | _ => None 
 end.                         
      
      
      
      
      
      

          
 

Definition getcsAr (o : one_inductive_body) : string × list nat :=
 (ind_name o, (map cstr_arity (ind_ctors o))).
                 
Fixpoint extractTypeCsArlst (muts : list mutual_inductive_body) : list (string × list nat) :=
  match muts with
   | [] => []
   | (h :: t) => map getcsAr (ind_bodies h) ++ extractTypeCsArlst t
  end.  
   
   
   
Parameter error_nat : nat.
Parameter errorInd : inductive.
Parameter errorStr : string.
Parameter errorlstNat : list nat.


Fixpoint retVarVals' (lst : list string) : term :=
 match lst with
 | [] =>  tApp (tConstruct
                         {|
                           inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list");
                           inductive_ind := 0
                         |} 0 [])
                      [<%nat%>]
 | h :: rest => tApp
                   (tConstruct
                      {|
                        inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list");
                        inductive_ind := 0
                      |} 1 [])
                   [<%nat%>; tVar h; retVarVals' rest]                     
                      
 end.

Definition retVarVals (lst : list string) : term :=
 tApp (tConstruct
                {|
                  inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option"); inductive_ind := 0
                |} 0 [])
             [tApp
                (tInd
                   {|
                     inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
                   |} [])
                [<%nat%>]; (retVarVals' lst)].
             
Fixpoint sortBindersOne (outputVar : string) (lst': list ((string × term) × list string)) : (list string) :=
 match lst' with
  | [] => []
  | (h :: rest) => match h with
                    | (str1, (tVar y), _) => if (String.eqb y outputVar) then [str1] else sortBindersOne outputVar rest 
                    | _ => sortBindersOne outputVar rest
                   end 
 end.
(* Check concat. 
Check map.*)
 
Definition sortBinders (outputVars : list string) (lst : list ((string × term) × list string)) : ((list string)) :=
  concat (map (fun x : string => sortBindersOne x lst) outputVars). 
(* Compute (sortBinders ["a" ; "f"] ([("x", <%eq%>, ["v1"; "v2"; "v3"]);
        ("v6", tVar "a", [])])). *) 
        
Compute (retVarVals ["v6"]).                      
 
      
Definition getCstrIndex (s : ((string × term) × list string)) : nat := (* Get index of typeCon *)
  
  match s with
   | (str,
         tConstruct typeInfo
           k ls, lsStr)     => k
           
   | _ => error_nat        
  end. 

Definition getType (s : ((string × term) × list string)) :=  (*Get type of scrutinee var*)
  
  match s with
   | (str,
         tConstruct typeInfo
           k ls, lsStr)  => typeInfo
   | _ => errorInd
  end.         



Definition getTypeNm (s : (string × term) × list string) : string := (* Get name of type *)
 match s with 
  | (str,
         tConstruct {| inductive_mind := (loc, nmStr); inductive_ind := j |}
           k ls, lsStr)     => nmStr
  | _ => errorStr
 end.           

Fixpoint chkMemberStr (s : string) (lStr : list string) : bool :=
 match lStr with
  | [] => false
  | (h :: t) => if (String.eqb s h) then true else chkMemberStr s t
 end.   

Fixpoint filterTypeCon' (ls : list ((string × term) × list string)) (mut : list mutual_inductive_body) : 
                         list ((string × term) × list string) := (* Delete terms not corresponding to a valid typeCon *)
   match ls with
    | [] => []
    | h :: t => match h with 
                 | (str,
                    tConstruct {| inductive_mind := (loc, nmStr); inductive_ind := j |}
                    k ls, lsStr) => if (chkMemberStr nmStr (map fst (extractTypeCsArlst mut))) then h :: (filterTypeCon' t mut) else (filterTypeCon' t mut) 
                 | _ => (filterTypeCon' t mut) 
                end        
   end.


Definition filterTypeCon (ls : list ((string × term) × list string)) (mut : list mutual_inductive_body) : 
                         list ((string × term) × list string) := ls.
  










Fixpoint getCstrArityLst' (typeName : string) (r : list (string × list nat)) : list nat := (* use String.eqb *)
 
  match r with
   | [] => errorlstNat
   | (h :: t) => if String.eqb typeName (fst h) then snd h else getCstrArityLst' typeName t
  end. 
  
Definition getCstrArityLst (typeName : string) (muts : list mutual_inductive_body) : list nat :=
 getCstrArityLst' typeName (extractTypeCsArlst muts).
 
(* Compute (<% list nat %>). *)
   

Definition mkNoneBranch (n : nat) : branch term := mkNoneBr n (tApp
                   (tConstruct
                      {|
                        inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                        inductive_ind := 0
                      |} 1 [])
                   [tApp
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
            |} [])
         [<%nat%>]]). (* Takes a arity and produces a branch term where return value is none *)

Definition mkSomeBranch (l : list string) (t : term) : branch term := 
  {|
    bcontext :=
    genBinNmLsStr l;
    bbody :=
    t
      |}.
            (* Takes a list of binder names and a return val and produces
a branch term *) 

Fixpoint untilLst (n : nat) (l : list nat) : list nat :=
 match n with
  | 0 => []
  | S m => match l with
            | [] => []
            | h :: t => (h :: untilLst m t)
           end
 
 end.         (* Return l upto the index before n *)

Fixpoint restLst (n : nat) (l : list nat) : list nat :=
 match n with 
  | 0 => tl l
  | S m => match l with
            | [] => []
            | h :: t => restLst m t
           end  (* Return l from the index after n *)
 end.

Definition mkBrLst (s : (string × term) × list string) (l : list mutual_inductive_body) (t : term) : list (branch term) :=
 
 let csArlst := (getCstrArityLst (getTypeNm s) l) in
  let index := getCstrIndex s in
  map mkNoneBranch (untilLst index csArlst) ++ [mkSomeBranch (rev (snd s)) t] ++ map mkNoneBranch (restLst index csArlst).  
   
  
      
Definition mkCase'  (s' : ((string × term) × list string) × list term ) (l : list mutual_inductive_body) (t : term)  
                      : term :=
  let s := fst s' in 
  (tCase
     {|
       ci_ind := getType s ;
       ci_npar := length (snd s');
       ci_relevance := Relevant
     |}
     {|
       puinst := [];
       pparams := (snd s');
       pcontext := [{| binder_name := nNamed (fst (fst s)); binder_relevance := Relevant |}];
       preturn :=
         (tApp
           (tInd
              {|
                inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                inductive_ind := 0
              |} [])
           [tApp
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
            |} [])
         [<%nat%>]])
     |} (tVar (fst (fst s))) (* Should get changed to a tRel after deBruijning *)                                                                                                        
      (mkBrLst s l t)). 


Definition idTerm := <%(fun A : Type => (fun x : A => x))%>.
MetaRocq Quote Definition oBoolT := (Some true).
      
Definition identityTerm : term := idTerm. (* term rep of id function*)

(*Definition optBoolTrue : term := oBoolT. (* term rep of some true *)*)



(* Need to modify *)      


Fixpoint mkPmNested' (ls : list (((string × term) × list string) × list term)) (ls' : list (((string × term) × list string))) (outputVars : list string) 
            (mut : list mutual_inductive_body) : term :=
 match ls with
  | [] => identityTerm
  | (h :: nil) => mkCase' h mut (retVarVals (sortBinders outputVars (ls')))  
  | (h :: t) => mkCase' h mut (mkPmNested' t ls' outputVars mut)
 end. 
Definition mkPmNested (ls' : list (((string × term) × list string))) (outputVars : list string) 
            (mut : list mutual_inductive_body) : term :=
            mkPmNested' (preProcConsTypeVar ls' ls') ls' outputVars mut.
 
(*Definition mkPmNested (ls : list ((string × term) × list string)) (mut : list mutual_inductive_body) : term :=
   mkPmNested'  (filterTypeCon ls mut) mut.*)

Fixpoint removeOpt {A : Type} (optls : list (option A)) : list A :=
 match optls with
  | [] => []
  | (Some x :: t) => (x :: removeOpt t)
  | (None :: t) => removeOpt t
 end. 
 
(* Need to modify*) 
(*Definition getTypeVarVal (s : list string) : list term. Admitted.*)

Definition mkLam' (ls : list (((string × term) × list string))) (outputVars : list string) (mut : list mutual_inductive_body) : option term :=
 match ls with 
 | [] => None
 | (h :: ((str, typeInfo, []) :: t))  => Some (tLambda {| binder_name := nNamed "v2"%bs; binder_relevance := Relevant |}
                                 (typeInfo) (mkPmNested ls outputVars mut))

 
 
 | _ => None                                
 end.
 
Definition mkLam (ls : list (((string × term) × list string))) (outputVars : list string) (mut : list (option mutual_inductive_body)) : option term :=
  mkLam' ls outputVars (removeOpt mut).    
 


Definition mkLamfromInd (p : program) (outputVars : list string) (fuel : nat) : option term :=
 let td := extractTypeData p in
  let pmd := extractPatMatData p in
   if (preProcConsRem fuel pmd) then (mkLam (preProcCons fuel pmd) outputVars td) else None. 

Definition mkLamfromInd2 (conjTm : term) (p : program) (outputVars : list string) (fuel : nat) : option term :=
 let td := extractTypeData p in
  let pmd := conjTm in
   if (preProcConsRem fuel pmd) then (mkLam (preProcCons fuel pmd) outputVars td) else None. 
      
   
(* Compute (mkLamfromInd baz'Term 20).*)

Parameter errTm : term.

Definition removeopTm (o : option term) : term :=
 match o with
  | Some t => t
  | None => errTm
 end. 
 
(* 
tApp
             (tConstruct
                {|
                  inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option"); inductive_ind := 0
                |} 0 [])
             [tApp
                (tInd
                   {|
                     inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
                   |} [])
                [<%nat%>];
              tApp
                (tConstruct
                   {|
                     inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
                   |} 1 [])
                [<%nat%>; tVar "y";
                 tApp
                   (tConstruct
                      {|
                        inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list");
                        inductive_ind := 0
                      |} 1 [])
                   [<%nat%>; tVar "y";
                    tApp
                      (tConstruct
                         {|
                           inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list");
                           inductive_ind := 0
                         |} 0 [])
                      [<%nat%>]]]] 
*)                      

Parameter errorPath : prod modpath ident.

Definition getPathIdent (t : term) : prod modpath ident :=
 match t with
  | tInd p l => inductive_mind p
  | _ => errorPath
 end. 


          


Definition justAnimatePatMat {A : Type} (induct : A) (outputVar : list string) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
 indTm <- tmQuote induct ;; 
 termConj <- general.animate2 (getPathIdent indTm) ;; 
 termFull <- tmQuoteRecTransp  induct  false ;; 
 t <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption ((typeConstrPatMatch.removeopTm (typeConstrPatMatch.mkLamfromInd2 termConj termFull outputVar fuel))))) ;; 
 f <- tmUnquote t ;; 
 tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
 
 tmMsg "done".

  
                        
End typeConstrPatMatch.

Module typeConstrReduce.

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
 
 
Definition deConConj1 (t : term) : (list term) :=
 match t with
  | (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} []) (h :: (t1 :: t2))) 
                   => [t1]
  | _ => nil
 end.  

Definition deConConj2 (t : term) : (list term) :=
 match t with
  | (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} []) (h :: (t1 :: (t2 :: t3)))) 
                   => [t2]
  | _ => nil
 end. 
 
Fixpoint makeConjSimpl (l1 : list (list term)) : list term :=
 match l1 with
  | nil => nil
  | [_h] => nil
  | ([h1]) :: (([h2]) :: t) =>
                          (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} [])
                          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} [];
                          h1;
                          h2]) :: makeConjSimpl t (* Is this clause too general *)
                          
  | ([]) :: (([]) :: t) => makeConjSimpl t
  | _ => nil                        

 end.
 
Definition justAnimateElimConstr (kn : kername) (inputVars : list string) (outputVars : list string) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
  (* conjs <- general.animate2 kn ;; *)
  t <- general.animate2 kn ;;
  let conjs := (tApp <%and%> (typeConstrReduce.makeConjSimpl (typeConstrReduce.deconTypeConGen'' (typeConstrReduce.deConConj1 t) (typeConstrReduce.deConConj2 t) fuel))) in

  
  t' <- DB.deBruijn (animateEqual.genFun conjs inputVars outputVars fuel)  ;; 
  f <- tmUnquote t' ;; (* tmDefinition (String.append (snd kn) "Fn") f ;; *)
  tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
 
  
  (* lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;; *)
  tmMsg "done". 

 
End typeConstrReduce.  


(*

(* Recursive Predicate *)

Inductive recPred : nat -> nat -> Prop :=
 | recPredBase : recPred 1 3
 | recPredInd : forall a b, recPred a b  -> recPred (S a) (S b).
 
(* Desired output function with a as input, b as output *)

Fixpoint recPredfn (a : nat) : option nat :=
 match a with
 | 1 => Some 3
 | S a' => match recPredfn a' with
           | None => None
           | Some b' => Some (S b')
           end
 | _ => None          
 end. 
 
(* General case 

Clause : recPred a1 a2 -> recPred (cons1 a1 a2) (cons2 a1 a2) 

first argument input, second argument output.

=
Fixpoint recPredfn (a1 : nat) : option type 
...

 match a1 with
  | cons1 a1' a2' => match recPredfn a1' with
                      | Some x => if (Eqb a2' x) then Some (cons2 a1' a2') else None
                      | _  => None
  
1 Clause = 1 match statement 
*)                      
        
                                  
*)






