From Stdlib Require Import List.

Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.

Require Import Animation.utils.
Import MetaRocqNotations.
Unset MetaRocq Strict Unquote Universe Mode.
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

Inductive outcomePoly (A : Type) : Type :=
 | fuelErrorPoly
 | successPoly (x:A)
 | noMatchPoly.

Compute (fst (1,2,3)).


Module animateEqual.


Parameter inValidConj : term.


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
      
  | tApp <%eq%> [<%nat%>; tVar str1; tConstruct ind_type k lst] =>
      [tApp <%eq%> [<%nat%>; tVar str1; tConstruct ind_type k lst]]
  
  | tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tVar str1] =>
      [tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tVar str1]]    
         

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
  | tApp <%eq%> [<%nat%>; tApp fn1 lst1; tConstruct ind_type k lst] =>
      [tApp <%eq%> [<%nat%>; tApp fn1 lst1; tConstruct ind_type k lst]]
  
  | tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tApp fn1 lst1] =>
      [tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tApp fn1 lst1]]    
             
  | tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tConstruct ind_type2 k2 lst2] =>
      [tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tConstruct ind_type2 k2 lst2]]    
                        
  | _ => []
 end.

Fixpoint filterListConj (bigConj : term) : list bool :=
 match bigConj with
  | tApp <%and%> ls => concat (map filterListConj ls)

  | tApp <%eq%> [<%nat%>; tVar str1; tVar str2] => [true]

  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn lst] =>
      [true]
  
  | tApp <%eq%> [<%nat%>; tApp fn lst; tVar str1] =>
      [true]
      
  | tApp <%eq%> [<%nat%>; tVar str1; tConstruct ind_type k lst] =>
      [true]
  
  | tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tVar str1] =>
      [true] 

  
  | tApp <%eq%> [<%nat%>; tApp fn1 lst1; tApp fn2 lst2] =>
      [true]  
  | tApp <%eq%> [<%nat%>; tApp fn1 lst1; tConstruct ind_type k lst] =>
      [true]
  | tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tApp fn1 lst1] =>
      [true]      
  | tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tConstruct ind_type2 k2 lst2] =>
      [true]                
  | _ => [false]
 end.
 
Fixpoint checkBool (lst : list bool) : bool :=
 match lst with
 | [] => true
 | h :: t => andb h (checkBool t)
end. 


 
 


(*Compute (getListConjGuardCon fooTerm).*)

Fixpoint extractOrderedVarsHelper (ls : list term) : list string :=
 match ls with 
 | [] => []
 | (tVar str) :: t => str :: (extractOrderedVarsHelper t)
 | _ :: t => (extractOrderedVarsHelper t)
 end. 
 
Print Instance.t.
 


(* extract ordered list of vars from conjunct *)
Definition extractOrderedVars (t : term) : list string := 
  match t with
  | tApp <%eq%> [<%nat%>; tVar str1; tVar str2] => [str1 ; str2]
  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn lst] => str1 :: extractOrderedVarsHelper (lst)
  | tApp <%eq%> [<%nat%>; tApp fn lst; tVar str1] => app (extractOrderedVarsHelper (lst)) [str1]
  | tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tVar str1] => [str1]
  | tApp <%eq%> [<%nat%>; tVar str1; tConstruct ind_type k lst] =>  [str1]
 
  (* Combine the pattern matches to handle fns of arbitrary arity *)
  
  | _ => nil
  end.


(* Instantiate partialLetFun with identity *)

Definition animateOneConjSucc (conj : term) (partialLetfn : term -> term) : option (term -> term) :=
  match conj with
  | tApp <%eq%> [<%nat%>; tVar str1; tVar str2] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1; binder_relevance := Relevant |}
                                 (tVar str2) <%nat%>) t))

  (*| tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2; tVar str3; tVar str4; tVar str5 ]] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn [tVar str2; tVar str3; tVar str4; tVar str5]) <%nat%>) t)) *)

  (*| tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2]] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn [tVar str2]) <%nat%>) t)) *)
  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn lstTerm] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn lstTerm) <%nat%>) t))
  
  | tApp <%eq%> [<%nat%>; tApp fn lstTerm; tVar str1] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn lstTerm) <%nat%>) t))                               
  
  | tApp <%eq%> [<%nat%>; tVar str1; tConstruct ind_type k lst] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tConstruct ind_type k lst) <%nat%>) t))
  
  | tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tVar str1] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tConstruct ind_type k lst) <%nat%>) t))                               
  
  
  | _ => None
 end.
 
Definition flipConj (conj : term) : term :=
 match conj with
  | tApp <%eq%> [<%nat%>; tVar str1; tVar str2] => tApp <%eq%> [<%nat%>; tVar str2; tVar str1] 
  | tApp <%eq%> [<%nat%>; tApp fn lstTerm; tVar str1] => tApp <%eq%> [<%nat%>; tVar str1; tApp fn lstTerm]
  | tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tVar str1] => tApp <%eq%> [<%nat%>; tVar str1; tConstruct ind_type k lst]
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
  | tApp <%eq%> [<%nat%>; tApp fn1 lst1; tConstruct ind_type k lst] => 
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (tConst <? Nat.eqb ?> []) [tApp fn1 lst1
         ; tConstruct ind_type k lst]]
  | tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tApp fn1 lst1] => 
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (tConst <? Nat.eqb ?> []) [tApp fn1 lst1
         ; tConstruct ind_type k lst]]    
  | tApp <%eq%> [<%nat%>; tConstruct ind_type k lst; tConstruct ind_type2 k2 lst2] => 
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (tConst <? Nat.eqb ?> []) [tConstruct ind_type2 k2 lst2
         ; tConstruct ind_type k lst]]              
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


Definition genFun (fooTerm : term) (inputVars : list string) (outputVars : list string) (fuel : nat) : TemplateMonad term :=
  if checkBool (filterListConj fooTerm) then
  ret (constrFn inputVars outputVars
    (animateListConj
       (getListConjLetBind fooTerm) nil inputVars fuel (fun t : term => t))
    (animateOneConjGuardList (getListConjGuardCon fooTerm))) else tmFail "cannot process conj".


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
  r <- animateEqual.genFun conjs inputVars outputVars fuel  ;; 
  
  t' <- DB.deBruijn r ;;
  
  f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) t' ;; tmPrint f ;; tmDefinition (String.append (snd kn) "Fn") f ;;
  lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f induct) ;;
  tmMsg "done".
      


Definition justAnimate (kn : kername) (inputVars : (list string)) (outputVars : list string) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
  conjs <- general.animate2 kn ;;
  
  r <- animateEqual.genFun conjs inputVars outputVars fuel  ;;
  t' <- DB.deBruijn r  ;; 
  f <- tmUnquote t' ;;
  (*tmPrint f ;;*)
  tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
  (* lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;; *)
  tmMsg "done". 
  


(*
MetaRocq Quote Definition constTm := 2.
Print constTm. *)  
(*
Definition justAnimateFmConj (conjs : term) (inputVars : (list string)) (outputVars : list string) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
  (*conjs <- general.animate2 kn ;;*)
  t' <- DB.deBruijn (animateEqual.genFun conjs inputVars outputVars fuel)  ;; 
  f <- tmUnquote t' ;;
  (*tmPrint f ;;*)
  tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
  (* lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;; *)
  tmMsg "done". 

*)
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
 (map extractIndDecl ((map snd ((((declarations (fst p)))))))).

(*
Definition extractTypeData (p : program) : list (option mutual_inductive_body) := 
 (map extractIndDecl ((map snd ((tl (tl (declarations (fst p)))))))).
*)
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
Compute (sortBinders ["a" ; "f"] ([("x", <%eq%>, ["v1"; "v2"; "v3"]);
        ("v6", tVar "a", [])])). 
        
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
Compute (getType (("x", <%eq%>, ["v1"; "v2"; "v3"]))).


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



Fixpoint mkPmNested' (ls : list (((string × term) × list string) × list term)) (ls' : list (((string × term) × list string))) (outputVars : list (string)) 
            (mut : list mutual_inductive_body) : term :=
 match ls with
  | [] => identityTerm
 (* | (h :: nil) => mkCase' h mut (genOutputTerm (transformOutputVars outputVars ls')) *)
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

Definition mkBigConj (lst : list term) : term :=
 match lst with 
  | [] => <%true%>
  | [elt] => elt
  | xs => (tApp <%and%> xs)
 end. 
 
Definition justAnimateElimConstr (kn : kername) (inputVars : list string) (outputVars : list string) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
  (* conjs <- general.animate2 kn ;; *)
  t <- general.animate2 kn ;;
  let conjs := (mkBigConj (typeConstrReduce.makeConjSimpl (typeConstrReduce.deconTypeConGen'' (typeConstrReduce.deConConj1 t) (typeConstrReduce.deConConj2 t) fuel))) in
  r <- animateEqual.genFun conjs inputVars outputVars fuel ;;     
  
  t' <- DB.deBruijn r  ;; 
  f <- tmUnquote t' ;; (* tmDefinition (String.append (snd kn) "Fn") f ;; *)
  tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
 
  
  (* lemma1_name <- tmFreshName "lemma" ;;
  lemma1 <- tmQuote =<< tmLemma lemma1_name (soundness'' f) ;; *)
  tmMsg "done". 
  
(*  
Definition justAnimateElimConstr' (kn : kername) (inputVars : list string) (outputVars : list string) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
  (* conjs <- general.animate2 kn ;; *)
  t <- general.animate2 kn ;;
  let conjs := (mkBigConj (typeConstrReduce.makeConjSimpl (typeConstrReduce.deconTypeConGen'' (typeConstrReduce.deConConj1 t) (typeConstrReduce.deConConj2 t) fuel))) in

  
  animateEqual.justAnimateFmConj conjs inputVars outputVars nameFn fuel. 
*) 
End typeConstrReduce. 




(* Cases requiring function inversion *)
Inductive recPred' : nat -> nat -> Prop :=
 | recPred'Ind : forall a b, recPred' a b -> recPred' (a + S b) (S a + b).

(* Need to know how to invert the function fun x y => x + S y *) 

Inductive recPred'' : nat -> nat -> Prop :=
 | recPred''Ind : forall a b, recPred' a b -> recPred'' (S b) (S a).



Inductive recPredFull : nat -> nat -> Prop :=
 | recPredFullBase : recPredFull 1 3 
 | recPredFullCons : forall a b, recPredInd1 a b -> recPredFull (S a) (S b)

with recPredInd1 : nat -> nat -> Prop :=  
 | recPredInd1Cons : forall a b, recPredFull a b  -> recPredInd1 a b.


MetaRocq Quote Recursively Definition recPredFull_syntax := recPredFull.

Compute (option_map ind_bodies (typeConstrPatMatch.extractIndDecl (snd (hd (typeConstrPatMatch.error) (declarations (fst recPredFull_syntax)))))).

Print TemplateMonad.

MetaRocq Run (t <- tmQuoteInductive <? recPredFull ?> ;; tmPrint t).
Definition recPredFullConsTm : term :=
 tPro "a" <%nat%>
                     (tPro "b" <%nat%>
                        (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                           (tApp (tRel 2) [tRel 1; tRel 0])
                           (tApp (tRel 4)
                              [tApp
                                 (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
                                 [tRel 2];
                               tApp
                                 (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
                                 [tRel 1]]))).
MetaRocq Run (t <- DB.undeBruijn recPredFullConsTm ;; tmPrint t).

Parameter errorTm : term.


Print global_declarations.

(* MetaRocq Run (general.animate <? recPredFull ?>). *)  
 
 


 



 
Print list.
  
 



Definition sampleInput : term := 
(tPro "a" <%nat%>
   (tPro "b" <%nat%>
      (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
         (tApp (tVar "recPredInd1") [tVar "a"; tVar "b"])
         (tApp (tVar "recPredFull")
            [tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "a"];
             tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "b"]])))).



Definition mkNoneBranch2 (wildCardRet : term) (n : nat)  : branch term := typeConstrPatMatch.mkNoneBr n wildCardRet. (* Takes a arity and produces a branch term where return value is none *)


Definition mkBrLst2 (s : (string × term) × list string) (l : list mutual_inductive_body) (t : term) (wildCardRet : term) : list (branch term) :=
 
 let csArlst := (typeConstrPatMatch.getCstrArityLst (typeConstrPatMatch.getTypeNm s) l) in
  let index := typeConstrPatMatch.getCstrIndex s in
  map (mkNoneBranch2 wildCardRet) (typeConstrPatMatch.untilLst index csArlst) ++ [typeConstrPatMatch.mkSomeBranch (rev (snd s)) t] ++ map (mkNoneBranch2 wildCardRet) (typeConstrPatMatch.restLst index csArlst).  
   
 
Definition mkCase2'  (s' : ((string × term) × list string) × list term ) (l : list mutual_inductive_body) (t : term) (outputType : term) (wildCardRet : term) 
                      : term :=
  let s := fst s' in 
  (tCase
     {|
       ci_ind := typeConstrPatMatch.getType s ;
       ci_npar := length (snd s');
       ci_relevance := Relevant
     |}
     {|
       puinst := [];
       pparams := (snd s');
       pcontext := [{| binder_name := nNamed (fst (fst s)); binder_relevance := Relevant |}];
       preturn :=
       outputType
     |} (tVar (fst (fst s))) (* Should get changed to a tRel after deBruijning *)                                                                                                        
      (mkBrLst2 s l t wildCardRet)). 
      
      
Fixpoint collectVarSets (l : list ((string × term) × list string)) : list string × list string :=
 match l with
 | [] => ([], [])
 | h :: t => match snd (fst h) with
              | tVar str => (str :: (fst (collectVarSets t)), (app (snd h) (fst (fst h) :: snd (collectVarSets t))))
              | _ => ((fst (collectVarSets t)), (app (snd h) (fst (fst h) :: snd (collectVarSets t))))
             end  
end. 
(* Compute (typeConstrPatMatch.preProcCons 30 term1''). *)

Search (string -> list string -> bool).
Fixpoint noRepeat (l1 : list string) (l2 : list string) : bool :=
 match l1 with
  | [] => true
  | (h :: t) => negb (typeConstrPatMatch.chkMemberStr h (l2)) && (noRepeat t l2)
 end. 


Fixpoint origVarsMap (l : list ((string × term) × list string)) : list (string × string) :=
match l with
 | [] => []
 | (str, tVar str1, lst) :: t => (str, str1) :: (origVarsMap t)
 | _ :: t => origVarsMap t
end.



Fixpoint switchOneVar (s : string) (map : list (string × string)) : string :=
 match map with
  | [] => s
  | (str, str1) :: t => if (String.eqb s str) then str1 else switchOneVar s t
 end.  
 
(*Compute (typeConstrPatMatch.preProcCons 30 term1''). 
Check map. *)

Definition switchVars  (d : list (string × string)) (o : ((string × term) × list string)) : ((string × term) × list string) :=
 match o with
  | (s, t, l) => ((switchOneVar s d), t, (map (fun s => switchOneVar s d) l))
 end. 
 
Definition switchVars' (d : list (string × string))  (l : list ((string × term) × list string)) := 
 (map (switchVars d) l).
 
Definition changeVars (l : list ((string × term) × list string)) : list ((string × term) × list string) :=
 switchVars' (origVarsMap l) l.
        


Fixpoint mkPmNested2' (ls : list (((string × term) × list string) × list term)) (ls' : list (((string × term) × list string))) (outputTerm : term) (outputType : term) (wildCardRet : term)
            (mut : list mutual_inductive_body)  : term :=
 match ls with
  | [] => typeConstrPatMatch.identityTerm
  | (h :: nil) => mkCase2' h mut (outputTerm) outputType wildCardRet
  | (h :: t) => mkCase2' h mut (mkPmNested2' t ls' outputTerm outputType wildCardRet mut) outputType wildCardRet
 end. 
 
 
Definition mkPmNested2 (ls' : list (((string × term) × list string))) (outputTerm : term) (outputType : term) (wildCardRet : term)
            (mut : list mutual_inductive_body)  : term :=
            mkPmNested2' (typeConstrPatMatch.preProcConsTypeVar ls' ls') ls' outputTerm outputType wildCardRet mut.
 
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

Definition mkLam2' (ls : list (((string × term) × list string))) (outputTerm : term) (outputType : term) (wildCardRet : term) (mut : list mutual_inductive_body)  : option term :=
 match ls with 
 | [] => None
 | (h :: ((str, typeInfo, []) :: ((str2, t', l') :: rest)))  => Some (tLambda {| binder_name := nNamed str2; binder_relevance := Relevant |}
                                 (typeInfo) (mkPmNested2 ls outputTerm outputType wildCardRet mut))

 
 
 | _ => None                                
 end.
 
Definition mkLam2 (ls : list (((string × term) × list string))) (outputTerm : term) (outputType : term) (wildCardRet : term) (mut : list (option mutual_inductive_body))  : option term :=
  mkLam2' ls outputTerm outputType wildCardRet (removeOpt mut).    
 


Definition mkLamfromInd3 (conjTm : term) (lstP : list program) (outputTerm : term) (outputType : term) (wildCardRet : term) (fuel : nat) : option term :=
 let td := concat (map (typeConstrPatMatch.extractTypeData) lstP) in
  let pmd := conjTm in
   if (typeConstrPatMatch.preProcConsRem fuel pmd) then (mkLam2 (changeVars (typeConstrPatMatch.preProcCons fuel pmd)) outputTerm outputType wildCardRet td) else None. 
            
  
(* Compute (mkLamfromInd baz'Term 20).*)

Parameter errTm : term.

Definition removeopTm (o : option term) : term :=
 match o with
  | Some t => t
  | None => errTm
 end. 
 
                     

Parameter errorPath : prod modpath ident.

Definition getPathIdent (t : term) : prod modpath ident :=
 match t with
  | tInd p l => inductive_mind p
  | _ => errorPath
 end. 


          


Definition justAnimatePatMat2 {A : Type} (induct : A) (inputTerm' : term) (inputType : term) (outputTerm : term) (outputType : term) (wildCardRet : term) (nameFn : string) (fuel : nat) : TemplateMonad unit :=
 (*
 indTm <- tmQuote induct ;; 
 
 termConj <- general.animate2 (getPathIdent indTm) ;;
 *) 
 termFull <- tmQuoteRecTransp  induct  false ;;
 
 let inputTerm := tApp <%eq%> [inputType; inputTerm'; tVar "v_init"] in 
 if noRepeat (fst (collectVarSets (typeConstrPatMatch.preProcCons fuel inputTerm))) (snd (collectVarSets (typeConstrPatMatch.preProcCons fuel inputTerm))) then 
 
 t <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption ((typeConstrPatMatch.removeopTm (mkLamfromInd3 inputTerm [termFull] outputTerm outputType wildCardRet fuel))))) ;; 
 

 
 f <- tmUnquote t ;; 
 tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
 
 tmMsg "done"
 else
 tmFail "found clashing variables".
 




Parameter c : case_info.
Parameter p : predicate term.
Parameter l : list (branch term).

Definition caseTm : term := tCase c p (tApp (tVar "g") [tVar "a"]) l.








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
Compute <%(nat -> option nat)%>.
Search ((list term) -> term).

Fixpoint mkLstTm' (lst : list term) (typeofTm : term) : term := 
 match lst with
  | [] => tApp
           (tConstruct
              {|
                inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
              |} 0 []) [typeofTm]
  
  | h :: t =>  tApp
               (tConstruct
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1 [])
               [typeofTm; h; (mkLstTm' t typeofTm)]
 end.              


Definition defaultVal (inputType : Type) (outputType : Type) (default : outputType) (f : inputType -> option (outputType)) : (inputType -> outputType) :=
 fun x => match f x with
           | Some y => y
           | None => default
          end. 

 
Fixpoint quoteList {A : Type} (l : list A) : TemplateMonad (list term) :=
 match l with
  | [] => ret []
  | h :: rest => (t <- tmQuote h ;; l' <- quoteList rest ;; tmReturn (t :: l'))
 end.  
 
Search (bool -> bool -> bool). 

Definition justAnimatePatMat4 {A : Type} (induct : A) (inputTerm' : term) (inputType : term) (outputTerm : term) (outputType : term) (wildCardRet : term)  (fuel : nat) : TemplateMonad term :=
 (*
 indTm <- tmQuote induct ;; 
 
 termConj <- general.animate2 (getPathIdent indTm) ;;
 *) 
 termFull <- tmQuoteRecTransp  induct  false ;;
(* outcome'Prog <- tmQuoteRecTransp  outcome'  false ;; *)
 outcomePolyProg <- tmQuoteRecTransp  outcomePoly  false ;;
 
 let inputTerm := tApp <%eq%> [inputType; inputTerm'; tVar "v_init"] in 
 if andb (noRepeat (fst (collectVarSets (typeConstrPatMatch.preProcCons fuel inputTerm))) (snd (collectVarSets (typeConstrPatMatch.preProcCons fuel inputTerm))))  (typeConstrPatMatch.preProcConsRem fuel inputTerm) then 
 
 t <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption ((typeConstrPatMatch.removeopTm (mkLamfromInd3 inputTerm [termFull; outcomePolyProg (* ; outcome'Prog *)] outputTerm outputType wildCardRet fuel))))) ;; 
 tmReturn t

 
 
 else
 tmFail "found clashing variables or insufficient fuel".
 
MetaRocq Quote Definition optNatTm := (@None nat).
Print optNatTm. 
  
 
Fixpoint justAnimateMultPat {A : Type} (induct : A) (branchData : list ((prod term term))) (inputType : term)  (outputType : term) (fuel : nat) : TemplateMonad (list term) :=
 match branchData with
  | [] => tmFail "no Branch Data"
  | [h] => t <- justAnimatePatMat4 induct (fst (h)) inputType (tApp
         (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option"); inductive_ind := 0
            |} 0 [])
         [outputType; (snd (h))]) (tApp
                        (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option"); inductive_ind := 0 |}
                         [])[outputType]) 
                         (tApp (tConstruct
                         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option"); inductive_ind := 0 |} 1
                          []) [outputType]) fuel ;; tmReturn [t]
  | h :: rest => t <- justAnimatePatMat4 induct (fst (h)) inputType (tApp
         (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option"); inductive_ind := 0
            |} 0 [])
         [outputType; (snd (h))]) (tApp
                        (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option"); inductive_ind := 0 |}
                         [])[outputType]) 
                         (tApp (tConstruct
                         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option"); inductive_ind := 0 |} 1
                          []) [outputType]) fuel ;; lstT <- justAnimateMultPat induct rest inputType outputType fuel ;; tmReturn (t :: lstT)  
 end.

 
Definition mkMulPatMatFn' (fns : list term) (wildCardRet : term) (inputType : term) (outputType : term)  : term :=
 let fnType := tProd {| binder_name := nAnon; binder_relevance := Relevant |} inputType
         (tApp
            (tInd
               {|
                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                 inductive_ind := 0
               |} [])
            [outputType]) in
 (tApp <%defaultVal%> [inputType; outputType; wildCardRet; (tApp <%dispatchInternal%> [inputType; outputType; (mkLstTm' fns fnType)])]).
 
 
Definition mkMulPatMatFn {A : Type} (induct : A) (branchData : list ((prod term term))) (inputType : term)  (outputType : term) (wildCardRet : term) (fuel : nat) : TemplateMonad term :=
 subfns <- justAnimateMultPat induct branchData inputType outputType fuel ;;
tmReturn (mkMulPatMatFn' subfns wildCardRet inputType outputType). 

Check ([((tApp (tConstruct
            {|
              inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
              inductive_ind := 0
            |} 1 [])[tVar "b"]),   (tApp (tConstruct
            {|
              inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
              inductive_ind := 0
            |} 1 [])
         [tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
            [tVar "b"]]))]).












Definition joinPatMatPoly {A : Type} (induct : A) (preIn' : term) (preInType' : term) (preOut' : term) (preOutType' : term)
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term) (nmFn : string)
                        (fuel : nat) : TemplateMonad unit :=
let preIn := tApp <%successPoly%> [preInType'; preIn'] in
let preInType := tApp <%outcomePoly%> [preInType'] in                      

let preOut := tApp <%successPoly%> [preOutType'; preOut'] in
let preOutType := tApp <%outcomePoly%> [preOutType'] in                      

let postIn := tApp <%successPoly%> [postInType'; postIn'] in
let postInType := tApp <%outcomePoly%> [postInType'] in                      

let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
let postOutType := tApp <%outcomePoly%> [postOutType'] in 

(* let wildCardRet := <%noMatchPoly%> in *)
let nmFnpreInpreOut := "animatePreConFn" in                    

let preInpreOutFnType := (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (preInType) (preOutType)) in
preOutTopostOutFn <- mkMulPatMatFn (induct) ([(preOut, postOut); ((tApp <%fuelErrorPoly%> [preOutType']),(tApp <%fuelErrorPoly%> [postOutType'])) ]) (preOutType)  (postOutType) (tApp <%noMatchPoly%> [postOutType'])  (fuel) ;;

tBody <-  mkMulPatMatFn (induct) ([(postIn, ((tApp preOutTopostOutFn [tApp (tVar nmFnpreInpreOut)[preIn]]))); ((tApp <%fuelErrorPoly%> [postInType']),(tApp <%fuelErrorPoly%> [postOutType'])) ]) postInType postOutType (tApp <%noMatchPoly%> [postOutType']) fuel ;;



t' <- tmEval all (removeopTm (DB.deBruijnOption (tLam nmFnpreInpreOut preInpreOutFnType tBody))) ;;

f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (nmFn) (Some hnf) ;; tmMsg "done".
              

Fixpoint mklhsProdType (lhsIndPre : list (term × term)) : TemplateMonad term :=
 match lhsIndPre with 
  | [] => tmFail "no predicates on LHS"
  | [h] => tmReturn (snd h)
  | h :: t => res <- mklhsProdType t ;; tmReturn (tApp
                                            (tInd
                                             {|
                                             inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0
                                              |} []) [(snd h) ; res])
 end.                                             
  



Fixpoint mklhsProdTm  (lhsIndPre : list (term × term )) : TemplateMonad term :=
 match lhsIndPre with 
  | [] => tmFail "no predicates on LHS"
  | [h] => tmReturn (fst h)
  | h :: t => res <- mklhsProdTm t ;; resT <- mklhsProdType t ;; tmReturn (tApp (tConstruct
                                                  {|
                                                   inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0
                                                   |} 0 []) [(snd h); resT ; (fst h) ; res])
 end. 
Compute <% (0,(0,0)) %>. 


Definition mkPreConProdType  (lhsInd : list ((((string × term) × term) × term) × term)) : TemplateMonad term :=
 mklhsProdType (map (fun tuple => ((snd (fst (fst (fst tuple)))), (snd (fst (fst tuple))))) lhsInd). 
 
Definition mkPreConProdTm  (lhsInd : list ((((string × term) × term) × term) × term)) : TemplateMonad term :=
 mklhsProdTm (map (fun tuple => ((snd (fst (fst (fst tuple)))), (snd (fst (fst tuple))))) lhsInd). 
 
Definition mkPostConProdType  (lhsInd : list ((((string × term) × term) × term) × term)) : TemplateMonad term :=
 mklhsProdType (map (fun tuple => ((((snd (fst tuple)))), (((snd tuple))))) lhsInd). 
 
Definition mkPostConProdTm  (lhsInd : list ((((string × term) × term) × term) × term)) : TemplateMonad term :=
 mklhsProdTm (map (fun tuple => ((((snd (fst tuple)))), (((snd tuple))))) lhsInd). 

Definition mkOutcome (lhsInd : ((((string × term) × term) × term) × term)) : ((((string × term) × term) × term) × term) :=
 match lhsInd with
  | ((((nm, preCon), preConT), postCon), postConT) => ((((nm, (tApp <%successPoly%> [preConT; preCon])), (tApp <%outcomePoly%> [preConT])), (tApp <%successPoly%> [postConT; postCon])), (tApp <%outcomePoly%> [postConT]))
 end.

Definition mkOutcomeProd (lhsInd : list ((((string × term) × term) × term) × term)) : list ((((string × term) × term) × term) × term) :=
 map (mkOutcome) lhsInd.
 

Fixpoint mkproductAllPreInToPreOutOutcome (lhsIndOutcome : list ((((string × term) × term) × term) × term)) : TemplateMonad term :=
match lhsIndOutcome with
 | [] => tmFail "no predicates on LHS"
 | [h] =>  tmReturn (tApp (tVar (String.append (fst (fst (fst (fst h)))) "AnimatedTopFn")) [tVar "remFuel"; snd (fst (fst (fst h)))])
                                                                        
 | h :: t => res <- mkproductAllPreInToPreOutOutcome t ;; resT <- mkPostConProdType t ;; tmReturn (tApp (tConstruct
                                                  {|
                                                   inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0
                                                   |} 0 []) [(snd h); resT ; (tApp (tVar (String.append (fst (fst (fst (fst h)))) "AnimatedTopFn")) [tVar "remFuel"; snd (fst (fst (fst h)))])
                                                                        ; res])

 end.
 


 
Fixpoint mklamOverAllOutcome  (lhsIndOutcome : list ((((string × term) × term) × term) × term)) (fnBody : term) : TemplateMonad term :=
 match lhsIndOutcome with
  | [] => tmFail "no predicates on LHS"
  | [h] => tmReturn (tLambda {| binder_name := nNamed (String.append (fst (fst (fst (fst h)))) "AnimatedTopFn") ; binder_relevance := Relevant |} (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (<%nat%>) (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (snd (fst (fst h))) (snd h)))  fnBody)
  | (h :: t) => res <- mklamOverAllOutcome t fnBody ;; tmReturn ((tLambda {| binder_name := nNamed (String.append (fst (fst (fst (fst h)))) "AnimatedTopFn") ; binder_relevance := Relevant |} (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (<%nat%>) (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (snd (fst (fst h))) (snd h))) res))
 end.
                                                   




Definition fuelErrorPolyCstFn (inputType : Type) (outputType' : Type) : (inputType -> (outcomePoly outputType') ) :=
 fun x : inputType => fuelErrorPoly outputType'.



Fixpoint genFuelErrorPatMat (lhsInd : list (term × term)) (index : nat) : list (list (term × term)) :=
match index with
 | 0 => []
 | S index' => match lhsInd with
                | [] => []
                | [(tm, tmTp)] => [[(tVar (String.append "fuelErrorVar" (string_of_nat index)), (tApp (<%outcomePoly%>) [tmTp]))]; [((tApp (<%fuelErrorPoly%>) [tmTp]), (tApp (<%outcomePoly%>) [tmTp]))]]
                | (tm, tmTp) :: rest => app (map (fun l' => (((tVar (String.append "fuelErrorVar" (string_of_nat index))), (tApp (<%outcomePoly%>) [tmTp])) :: l'))  (genFuelErrorPatMat rest index')) (map (fun l' => ((tApp (<%fuelErrorPoly%>) [tmTp]), (tApp (<%outcomePoly%>) [tmTp])) :: l')  (genFuelErrorPatMat rest index'))  
               end
end.


Fixpoint mkProdTmFuelError (lhsIndl : list (list (term × term))) : TemplateMonad (list term) :=

  match lhsIndl with
   | [] => tmReturn []
   | [h] => res <- mklhsProdTm h ;; tmReturn [res]
   | h :: t => resTail <- mkProdTmFuelError t ;; res <- mklhsProdTm h ;; tmReturn (res :: resTail)
  end.

Definition mkFuelErrorPatMatData (lhsInd : list (term × term)) (fuelErrorOut : term) : TemplateMonad (list (term × term)) :=
inData <- mkProdTmFuelError ( (*rev*) (tl (genFuelErrorPatMat lhsInd (S (length lhsInd))))) ;;

tmReturn (map (fun s => (s, fuelErrorOut)) inData). 
   
 








Definition joinPatMatPolyGenFuelAware {A : Type} (induct : A) (lhsInd : list ((((string × term) × term) × term) × term))
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term) (nmCon : string)
                        (fuel : nat) : TemplateMonad unit :=

let lhsIndOutcome := mkOutcomeProd lhsInd in
let postIn := tApp <%successPoly%> [postInType'; postIn'] in
let postInType := tApp <%outcomePoly%> [postInType'] in                      

let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
let postOutType := tApp <%outcomePoly%> [postOutType'] in 
lhsPostCondProdOutcomeTm <- mkPostConProdTm lhsIndOutcome ;;
lhsPostCondProdTm <- mkPostConProdTm lhsInd ;;

lhsPostCondProdType <- mkPostConProdType lhsInd ;;
lhsPostCondProdOutcomeType <- mkPostConProdType lhsIndOutcome ;;
lhsPostCondFuelErrorPatMat <- mkFuelErrorPatMatData (map (fun tup => ((snd (fst tup)), (snd tup))) lhsInd) (tApp <%fuelErrorPoly%> [postOutType']) ;; 
(* tmPrint lhsPostCondFuelErrorPatMat ;; *)
productAllPreInToPreOutOutcome <- mkproductAllPreInToPreOutOutcome lhsIndOutcome;;



preOutTopostOutFn <- mkMulPatMatFn (induct) (((lhsPostCondProdOutcomeTm), postOut) :: (lhsPostCondFuelErrorPatMat)) (lhsPostCondProdOutcomeType)  (postOutType) (tApp <%noMatchPoly%> [postOutType'])  (fuel) ;;


tBody' <-  mkMulPatMatFn (induct) ([(postIn, ((tApp preOutTopostOutFn [productAllPreInToPreOutOutcome]))); ((tApp <%fuelErrorPoly%> [postInType']),(tApp <%fuelErrorPoly%> [postOutType'])) ]) postInType postOutType (tApp <%noMatchPoly%> [postOutType']) fuel ;;



let tBody := 
 (tLam "fuel" <%nat%>
            (tCase
               {|
                 ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                 ci_npar := 0;
                 ci_relevance := Relevant
               |}
               {|
                 puinst := [];
                 pparams := [];
                 pcontext := [{| binder_name := nNamed "fuel"; binder_relevance := Relevant |}];
                 preturn := (tProd {| binder_name := nAnon; binder_relevance := Relevant |} postInType postOutType) 
                  
               |} (tVar "fuel")
               [{|
                  bcontext := [];
                  bbody :=
                    (tApp <%fuelErrorPolyCstFn%> [postInType; postOutType'])
                |};
                {|
                  bcontext := [{| binder_name := nNamed "remFuel"; binder_relevance := Relevant |}];
                  bbody := tBody'
                                    
                              |}]
                     )) in


u <- mklamOverAllOutcome lhsIndOutcome tBody ;;


t' <- tmEval all (removeopTm (DB.deBruijnOption u)) ;;

f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append nmCon "Animated") (Some hnf) ;; tmMsg "done".
           
                        




Definition joinPatMatPolyGenFuelAwareNoLHS {A : Type} (induct : A) 
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term) (nmCon : string)
                        (fuel : nat) : TemplateMonad unit :=


let postIn := tApp <%successPoly%> [postInType'; postIn'] in
let postInType := tApp <%outcomePoly%> [postInType'] in                      

let postOut := tApp <%successPoly%> [postOutType'; postOut'] in
let postOutType := tApp <%outcomePoly%> [postOutType'] in 






tBody' <-  mkMulPatMatFn (induct) ([(postIn, (postOut)); ((tApp <%fuelErrorPoly%> [postInType']),(tApp <%fuelErrorPoly%> [postOutType'])) ]) postInType postOutType (tApp <%noMatchPoly%> [postOutType']) fuel ;;



let u := 
 (tLam "fuel" <%nat%>
            (tCase
               {|
                 ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                 ci_npar := 0;
                 ci_relevance := Relevant
               |}
               {|
                 puinst := [];
                 pparams := [];
                 pcontext := [{| binder_name := nNamed "fuel"; binder_relevance := Relevant |}];
                 preturn := (tProd {| binder_name := nAnon; binder_relevance := Relevant |} postInType postOutType) 
                  
               |} (tVar "fuel")
               [{|
                  bcontext := [];
                  bbody :=
                    (tApp <%fuelErrorPolyCstFn%> [postInType; postOutType'])
                |};
                {|
                  bcontext := [{| binder_name := nNamed "remFuel"; binder_relevance := Relevant |}];
                  bbody := tBody'
                                    
                              |}]
                     )) in





t' <- tmEval all (removeopTm (DB.deBruijnOption u)) ;;

f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append nmCon "Animated") (Some hnf) ;; tmMsg "done".
           
                        
                        
Definition animateOneClause {A : Type} (induct : A) (lhsInd : list ((((string × term) × term) × term) × term))
                      (postIn' : term) (postInType' : term) (postOut' : term) (postOutType' : term) (nmCon : string)
                        (fuel : nat) : TemplateMonad unit :=
 match lhsInd with
  | [] =>  joinPatMatPolyGenFuelAwareNoLHS induct  
                      (postIn') (postInType') (postOut') (postOutType') (nmCon)
                        (fuel)
  | lst =>  joinPatMatPolyGenFuelAware (induct) (lst)
                      (postIn') (postInType') (postOut') (postOutType') (nmCon)
                        (fuel)                                              
 end.                       

 

       
 
             
(* __________________________Examples __________________________________ *) 


(* Examples with multiple predicates on LHS *)            
              
Inductive rel4 : (prod nat nat) -> (prod nat nat) -> Prop :=

 | rel4Cons : forall a b c d, rel5 a c /\ rel6 (b) d -> rel4 (a, S b) (c, S d)
 
with rel5 : nat -> nat -> Prop :=

| rel5Cons : forall u w, w = S u -> rel5 u w

with rel6 : nat -> nat -> Prop :=

| rel6Cons : forall u1 w1, w1 = S (S u1) -> rel6 u1 w1.




Definition pairNatTerm : term := tApp
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0
            |} [])
         [<%nat%>; <%nat%>].


Definition preInTPair : term := tApp (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0
            |} 0 [])
         [<%nat%>; <%nat%>;  (tVar "a"); (tVar "b")].




Definition preOutTPair : term :=  tApp (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0
            |} 0 [])
         [<%nat%>; <%nat%>;  (tVar "c"); (tVar "d")].



Definition postInTPair : term := tApp (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0
            |} 0 [])
         [<%nat%>; <%nat%>;  (tVar "a"); (tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "b"])].
         
         
         
Definition postOutTPair : term := tApp (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0
            |} 0 [])
         [<%nat%>; <%nat%>;  (tVar "c"); (tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "d"])].
         
 



MetaRocq Run (animateOneClause (rel4) ([(((("rel5", (tVar "a")), <%nat%>), (tVar "c")), <%nat%>); ((((("rel6", (tVar "b"))), 
                           <%nat%>), (tVar "d")), <%nat%>)]) (postInTPair) (pairNatTerm) (postOutTPair) 
                         (pairNatTerm) ("rel4Cons") (50)).
Print rel4ConsAnimated.                         

MetaRocq Run (animateOneClause (rel4) ([(((("rel5", (tVar "b")), <%nat%>), (tVar "c")), <%nat%>); ((((("rel6", (tVar "b"))), 
                           <%nat%>), (tVar "d")), <%nat%>)]) (postInTPair) (pairNatTerm) (postOutTPair) 
                         (pairNatTerm) ("rel4Cons2") (50)).
Print rel4Cons2Animated.                         


Definition rel5ConsAnimTop (fuel : nat) (inp : (outcomePoly nat)) : (outcomePoly nat) :=
 match fuel with
 | 0 => (fuelErrorPoly nat)
 | S m => match inp with
           | (successPoly k) => (successPoly nat (S k))
           | _ => noMatchPoly nat  
          end                        
 end.
 


Definition rel6ConsAnimTop (fuel : nat) (inp : (outcomePoly nat)) : (outcomePoly nat) :=
 match fuel with
 | 0 => (fuelErrorPoly nat)
 | S m => match inp with
           | (successPoly k) => (successPoly nat (S (S k)))
           | _ => noMatchPoly nat  
          end                        
 end.
 
Definition rel7ConsAnimTop (fuel : nat) (inp : (outcomePoly nat)) : (outcomePoly nat) :=
 match fuel with
 | 0 => (fuelErrorPoly nat)
 | S m => match inp with
           | (successPoly k) => (successPoly nat (S (S k)))
           | _ => noMatchPoly nat  
          end                        
 end. 
 
 
Compute (rel4Cons2Animated rel5ConsAnimTop rel6ConsAnimTop 30 (successPoly (prod nat nat) (13, 4))).  

Compute (rel4Cons2Animated rel5ConsAnimTop rel6ConsAnimTop 30 (successPoly (prod nat nat) (10, 4))).  


MetaRocq Run (animateOneClause (rel4) ([(((("rel5", (tVar "b")), <%nat%>), (tVar "c")), <%nat%>); ((((("rel6", (tVar "b"))), 
                           <%nat%>), (tVar "d")), <%nat%>); ((((("rel7", (tVar "b"))), 
                           <%nat%>), (tVar "e")), <%nat%>)]) (postInTPair) (pairNatTerm) (postOutTPair) 
                         (pairNatTerm) ("rel4Cons3") (50)). 
 



Compute (rel4Cons3Animated rel5ConsAnimTop rel6ConsAnimTop rel7ConsAnimTop 30 (successPoly (prod nat nat) (13, 4))).  





Compute (rel4ConsAnimated rel5ConsAnimTop rel6ConsAnimTop 30 (successPoly (prod nat nat) (13, 4))).  

Compute (rel4ConsAnimated rel5ConsAnimTop rel6ConsAnimTop 30 (successPoly (prod nat nat) (4, 0))).

Compute (rel4ConsAnimated rel5ConsAnimTop rel6ConsAnimTop 0 (successPoly (prod nat nat) (4, 5))).

(* Should say fuelError *)
Compute (rel4ConsAnimated rel5ConsAnimTop rel6ConsAnimTop 1 (successPoly (prod nat nat) (4, 5))).

MetaRocq Run (animateOneClause (recPredFull) ([]) (<%1%>) (<%nat%>) (<%3%>) 
                         (<%nat%>) ("recPredBase") (50)).
Print recPredBaseAnimated.

MetaRocq Run (animateOneClause (recPredFull) ([]) (tVar "a") (<%nat%>) (<%3%>) 
                         (<%nat%>) ("recPredBase2") (50)).
Print recPredBase2Animated.

Compute (recPredBase2Animated 5 (successPoly nat 1)). 

Compute (recPredBase2Animated 5 (successPoly nat 4)). 

Compute (recPredBaseAnimated 5 (successPoly nat 1)). 

Compute (recPredBaseAnimated 5 (successPoly nat 4)). 
  

(* CODE FOR GLUING EVERYTHING TOGETHER * ________________________________________________________________ *)






Fixpoint animateAllClauses {A : Type} (topInduct : A) (cstrData : (list ((((( (list ((((string × term) × term) × term) × term)) ×
                      (term)) × (term)) × (term)) × (term)) × (string))))
                        (fuel : nat) : TemplateMonad unit := 
 match cstrData with
  | [] => tmFail "no constructors in Inductive"
  | [h] => animateOneClause topInduct (fst (fst (fst (fst (fst h))))) (snd (fst (fst (fst (fst h))))) (snd (fst (fst (fst h)))) (snd (fst (fst h))) (snd (fst  h)) (snd h) fuel  
  | h :: t =>  animateAllClauses topInduct t fuel ;; animateOneClause topInduct (fst (fst (fst (fst (fst h))))) (snd (fst (fst (fst (fst h))))) (snd (fst (fst (fst h)))) (snd (fst (fst h))) (snd (fst  h)) (snd h) fuel  
 end.       





Definition quoteConst (s : string) : term :=
tConst
         (MPfile ["animationModules"; "Animation"], s)
         [].
 

Fixpoint applyTopFn (clauseData : list (string × (list string))) : list term :=
match clauseData with
| [] => []
| (postConCons, preConInd) :: t => match preConInd with
                                   | [] => (quoteConst (String.append postConCons "Animated")) :: applyTopFn t
                                   | l => tApp (quoteConst (String.append postConCons "Animated")) (map (fun nm => (tVar (String.append nm "AnimatedTopFn"))) l) :: applyTopFn t
                                   end
end.


MetaRocq Run (f <- tmUnquote (quoteConst "applyTopFn");; tmPrint f).
                     




Fixpoint dispatch {A : Type} {B : Type} (lst : list (A -> nat -> option B)) : A -> nat -> option B :=
 match lst with
 | [] => (fun x y => None)
 | h :: t => fun x y => let g := h x y in 
                         match g with
                         | None => dispatch t x y
                         | _ => g
                        end 
 
 end.
(*
Fixpoint dispatchOutcomePolyExt {A : Type} {B : Type} (lst : list (nat -> outcomePoly A  -> outcomePoly B)) : nat -> outcomePoly A -> outcomePoly B :=
 match lst with
 | [] => (fun x y => (noMatchPoly B))
 | h :: t => fun x y => match (h x y) with
                         | (noMatchPoly) => dispatchOutcomePolyExt t x y
                         | _ => h x y
                        end 
                         
 
 end.

Fixpoint dispatchOutcomePolyExt' {A : Type} {B : Type} (lst : list (nat -> outcomePoly A  -> outcomePoly B)) (fuel : nat) (input' : outcomePoly A): outcomePoly B :=
 match fuel with
  | 0 => fuelErrorPoly B
  | S remFuel => match lst with
                  | [] => (noMatchPoly B)
                  | h :: t => match (h remFuel input') with
                         | (noMatchPoly) => dispatchOutcomePolyExt' t remFuel input'
                         | _ => h remFuel input'
                        end 
                 end       
 
 end.  
*) 


Parameter default : (def term).

Definition inspectFix (t : term) : list (def term) :=
 match t with 
  | tFix l k => l
  | _ => []
 end.  


Fixpoint mkLstTm (eltType : term) (lst : list string) : term := 
 match lst with
  | [] => tApp
           (tConstruct
              {|
                inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0
              |} 0 []) [eltType]
  
  | h :: t =>  tApp
               (tConstruct
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1 [])
               [eltType; tVar h; mkLstTm eltType t]
 end.                        


Print tPro.

Compute <% (nat -> prod nat nat -> prod nat nat) %>.


Definition mkOneIndTop (indNm : string) (inputType : term) (outputType : term) (clauseData : list (string × (list string))) : def term :=
  
{|
     dname := {| binder_name := nNamed (String.append indNm "AnimatedTopFn") ; binder_relevance := Relevant |};
     dtype :=
       tPro "fuel" <%nat%> (tPro "input" (tApp (<%outcomePoly%>) [inputType]) 
         
       
            (tApp (<%outcomePoly%>) [outputType]));
     dbody :=
       
         
          tLam "fuel" <%nat%> 
           
           (tLam "input" (tApp (<%outcomePoly%>) [inputType])
            (tCase
               {|
                 ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                 ci_npar := 0;
                 ci_relevance := Relevant
               |}
               {|
                 puinst := [];
                 pparams := [];
                 pcontext := [{| binder_name := nNamed "fuel"; binder_relevance := Relevant |}];
                 preturn := (tApp (<%outcomePoly%>) [inputType])
                  
               |} (tVar "fuel")
               [{|
                  bcontext := [];
                  bbody :=
                    (tApp (<%fuelErrorPoly%>) [outputType])
                |};
                {|
                  bcontext := [{| binder_name := nNamed "remFuel"; binder_relevance := Relevant |}];
                  bbody := tApp (tVar "dispatchOutcomePolyExt") [inputType ; outputType; (mkLstTm' (applyTopFn clauseData) (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
         <%nat%> (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
        (tApp <%outcomePoly%> [inputType]) (tApp <%outcomePoly%> [outputType])) ) ); tVar "remFuel"; tVar "input"]  
                                    
                              |}]
                     ))  ; rarg := 0 |}.

 

 
Definition mkrecFn (ls : list (def term)) (j : nat) : term :=
 tFix ls j.
 
Fixpoint mkAllIndTop' (inductData : (list ((((string) × (term)) × (term)) × (list (string × (list string)))))) : list (def term) :=  
 match inductData with 
  | [] => []
  | h :: t => (mkOneIndTop (fst (fst (fst h))) (snd (fst (fst h))) (snd (fst h)) (snd h)) :: mkAllIndTop' t
 end.
Definition addToRecBlk (recBlock : term) (t : def term) := 
 match recBlock with
  | tFix ls j => tFix (app ls [t]) j
  | _ => recBlock
 end.   
 
Fixpoint dispatchOutcomePolyExt
  (A B : Type) (lst : list (nat -> outcomePoly A -> outcomePoly B)) (fuel' : nat)
  (input' : outcomePoly A) {struct fuel'} : outcomePoly B :=
  match fuel' with
  | 0 => fuelErrorPoly B
  | S remFuel' =>
      match lst with
      | [] => noMatchPoly B
      | h :: t =>
          let res := h remFuel' input' in
          match res with
          | @noMatchPoly _ => dispatchOutcomePolyExt A B t remFuel' input'
          | _ => res
          end
      end
  end. 

MetaRocq Quote Definition dt := Eval compute in dispatchOutcomePolyExt.
Print dt.
MetaRocq Run (dt' <- DB.undeBruijn dt ;; tmDefinition "dispatchExtTm'" dt'). 

Definition dispatchExtTm := hd default (inspectFix dispatchExtTm'). 

 
Definition mkAllIndTop (inductData : (list ((((string) × (term)) × (term)) × (list (string × (list string)))))) : list (def term) := 
app (mkAllIndTop' inductData) [dispatchExtTm]. 
Print reductionStrategy.

Definition animateInductivePredicate {A : Type} (topInduct : A) (nmTopInduct : string) (clauseData : (list ((((( (list ((((string × term) × term) × term) × term)) ×
                      (term)) × (term)) × (term)) × (term)) × (string)))) (inductData : (list ((((string) × (term)) × (term)) × (list (string × (list string)))))) 
                        (fuel : nat) : TemplateMonad unit :=
          animateAllClauses topInduct clauseData fuel ;;
          let u := (mkrecFn (mkAllIndTop (inductData)) 0)  in
          u' <- tmEval all u ;;  
          (* tmPrint u' ;; *)
          
          t' <- tmEval all (removeopTm (DB.deBruijnOption u)) ;;
          (*tmPrint t' ;; *)
          

               f <- tmUnquote t';;
              (* tmMsg "done". *) 
               
              (* tmPrint f ;; *)
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append nmTopInduct "AnimatedTopFn") (Some hnf) ;; tmMsg "done".




Fixpoint mkProdTypeVars (outputData : list (string × term)) :  term :=
 match outputData with 
  | [] => <%bool%>
  | [h] =>  (snd h)
  | h :: t => let res := mkProdTypeVars t in  (tApp
                                            (tInd
                                             {|
                                             inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0
                                              |} []) [(snd h) ; res])
 end.                                             
  



Fixpoint mkProdTmVars  (outputData : list (string × term )) : term :=
 match outputData with 
  | [] => <%true%>
  | [h] => (tVar (fst h))
  | h :: t => let res := mkProdTmVars t in
                                        let resT := mkProdTypeVars t in (tApp (tConstruct
                                                  {|
                                                   inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0
                                                   |} 0 []) [(snd h); resT ; (tVar (fst h)) ; res])
 end. 



Definition getOutputTerm (outputData : list (string × term))  : term :=
tApp <% successPoly %> [mkProdTypeVars outputData; mkProdTmVars outputData].
Print ident.

Definition extractPatMatBinders {A : Type} (kn : kername) (induct : A) (outputData : list (string × term )) (fuel : nat) : TemplateMonad unit :=
t <- general.animate2 kn ;;
match t with
 | tApp <%eq%> [typeInputVar; patMatTerm; tVar inputVar] => 
                      joinPatMatPolyGenFuelAwareNoLHS induct patMatTerm typeInputVar (mkProdTmVars outputData) (mkProdTypeVars outputData) (snd kn) fuel
 | _ => tmFail "incorrect inductive shape" 
end ;; tmMsg "done".                       


    
   
(* Full example *)

Inductive rel8: (nat × nat) -> (nat × nat)  -> Prop :=
 | rel8Base : forall a, rel8 (1, a) (3, S a) 
 | rel8Cons : forall a1 a2 b1 b2 b3 b4, rel8 (a1, a2) (b1, b3) /\ rel9 (a1, a2) (b4, b2) -> rel8 ((S a1), (S a2)) ((S b1), (S b2))

with rel9: (nat × nat) -> (nat × nat)  -> Prop := 
 | rel9Cons : forall a b, rel8 a b  -> rel9 a b.

       
Definition tS (t : term) : term :=
 tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
         [t].
         
Definition tP (t : term) (t' : term) : term :=
tApp
         (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0
            |} 0 [])
         [<%nat%>; <%nat%>; t;
          t'].
          
Definition clData := 
[([], tP <%1%> (tVar "a"), <%prod nat nat%>, tP <%3%> (tS (tVar "a")), <%prod nat nat%>, ("rel8Base")); 

([("rel8", tP (tVar "a1") (tVar "a2"), <%prod nat nat%> , tP (tVar "b1") (tVar "b3"), <%prod nat nat%>); ("rel9", tP (tVar "a1") (tVar "a2"), <%prod nat nat%> , tP (tVar "b4") (tVar "b2"), <%prod nat nat%>)],
 tP (tS (tVar "a1")) (tS (tVar "a2")), <%prod nat nat%>, tP (tS (tVar "b1")) (tS (tVar "b2")), <%prod nat nat%>, ("rel8Cons"));
 
([("rel8", tVar "a", <%prod nat nat%>, tVar "b", <%prod nat nat%>)], tVar "a", <%prod nat nat%>, tVar "b", <%prod nat nat%>, "rel9Cons")]. 

Definition indData := 
[("rel8", <%prod nat nat%>, <%prod nat nat%>, [("rel8Base", []); ("rel8Cons", ["rel8"; "rel9"])]); 
  ("rel9", <%prod nat nat%>, <%prod nat nat%>, [("rel9Cons",["rel8"])])]. 

MetaRocq Run (animateInductivePredicate rel8 "rel8" clData indData 50).
Print rel8AnimatedTopFn.


Compute (rel8AnimatedTopFn 50 (successPoly (nat × nat) (7,9))).
Compute (rel8AnimatedTopFn 100 (successPoly (nat × nat) (8,13))).


Compute (rel8AnimatedTopFn 70 (successPoly (nat × nat) (9,13))).
(*Takes very long 
Compute (rel8AnimatedTopFn 70 (successPoly (nat × nat) (12,14))).
*)

Lemma testrel8 : True -> rel8 (7,9) (9,10) .
Proof. intro. Admitted.

Lemma testrel8' : True -> rel8 (8,13) (10,14).
Proof. Admitted.
  
Lemma testrel8'' : True -> rel8 (9,13) (11,14).
Proof. Admitted.
  
Print tmQuote.

MetaRocq Run (mut <- tmQuoteInductive <? rel8 ?> ;; tmPrint mut).
MetaRocq Run (t' <- DB.undeBruijn (tPro "a" <%nat%>
                (tApp (tRel 2)
                   [tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0 |} 0 [])
                      [<%nat%>; <%nat%>;
                       tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
                         [tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 0 []];
                       tRel 0];
                    tApp (tConstruct {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "prod"); inductive_ind := 0 |} 0 [])
                      [<%nat%>; <%nat%>;
                       tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
                         [tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
                            [tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
                               [tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 0 []]]];
                       tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tRel 0]]])) ;; tmPrint t').
(*            
Print constructor_body.
Print context.
Print context_decl.
Print program.
Print global_env.
Print Retroknowledge.t.
Print global_declarations.
Print global_decl.
Print constant_body.
Print mutual_inductive_body.
Print one_inductive_body.
Print constructor_body.
Print context_decl.
Definition getGlobDecls (p : program) : list (global_decl) :=
 match p with
  | (gEnv, t) => map snd (declarations gEnv) 
 end.

Fixpoint getMutIndBodies (l : list (global_decl)) : list mutual_inductive_body :=
 match l with
  | [] => []
  | ConstantDecl b :: t => getMutIndBodies t
  | InductiveDecl b :: t => b :: getMutIndBodies t
 end. 
 
*)  
                   
(*


Fixpoint rel8AnimatedTopFn (fuel : nat) (input : outcomePoly (prod nat nat)):  outcomePoly (prod nat nat)  :=
  match fuel with
  | 0 => fuelErrorPoly (prod nat nat) 
  | S remFuel => (dispatchOutcomePolyExt (prod nat nat) (prod nat nat) [rel8BaseAnimated; rel8ConsAnimated rel8AnimatedTopFn rel9AnimatedTopFn]) remFuel input
  end 
with rel9AnimatedTopFn (fuel : nat) (input : outcomePoly (prod nat nat)) :  outcomePoly (prod nat nat) :=
  match fuel with 
  | 0 => fuelErrorPoly (prod nat nat) 
  | S remFuel => (dispatchOutcomePolyExt (prod nat nat) (prod nat nat) [rel9ConsAnimated rel8AnimatedTopFn]) remFuel input
  end
with dispatchOutcomePolyExt (A : Type) (B : Type) (lst : list (nat -> outcomePoly A  -> outcomePoly B)) (fuel' : nat) (input' : outcomePoly A) : outcomePoly B :=
 match fuel' with
  | 0 => fuelErrorPoly B
  | S remFuel' => match lst with
                  | [] => (noMatchPoly B)
                  | h :: t => match (h remFuel' input') with
                         | (noMatchPoly) => dispatchOutcomePolyExt A B t remFuel' input'
                         | _ => h remFuel' input'
                        end 
                 end       
 
 end.  

*)
(*
Cannot guess decreasing arg. Definition of dispatch needs to be inlined...
Fixpoint rel8AnimatedTopFn (fuel : nat) (input : outcomePoly (prod nat nat)):  outcomePoly (prod nat nat)  :=
  match fuel with
  | 0 => fuelErrorPoly (prod nat nat) 
  | S remFuel => (@dispatchOutcomePolyExt' (prod nat nat) (prod nat nat) [rel8BaseAnimated; rel8ConsAnimated rel8AnimatedTopFn rel9AnimatedTopFn]) remFuel input
  end 
with rel9AnimatedTopFn (fuel : nat) (input : outcomePoly (prod nat nat)) :  outcomePoly (prod nat nat) :=
  match fuel with 
  | 0 => fuelErrorPoly (prod nat nat) 
  | S remFuel => (@dispatchOutcomePolyExt' (prod nat nat) (prod nat nat) [rel9ConsAnimated rel8AnimatedTopFn]) remFuel input
  end.

*) 


(*
Fixpoint dispatchOutcomePolyExt (A : Type) (B : Type) (lst : list (nat -> outcomePoly A  -> outcomePoly B)) (fuel' : nat) (input' : outcomePoly A) : outcomePoly B :=
 match fuel' with
  | 0 => fuelErrorPoly B
  | S remFuel' => match lst with
                  | [] => (noMatchPoly B)
                  | h :: t => match (h remFuel' input') with
                         | (noMatchPoly) => dispatchOutcomePolyExt A B t remFuel' input'
                         | _ => h remFuel' input'
                        end 
                 end       
 
 end.  
 

*)                             
    
       
(*
Definition recPred2IndFn
  (recPredTopFn : nat -> nat -> option outcome')
  (recPred2TopFn : nat -> nat -> option outcome')
  (a : nat) (c : nat) : option outcome' :=  
 match c with  
  | 0 => Some error'
  | S m =>   match recPredTopFn a m with
              | Some (success' ( b)) => Some (success' ((b)))
              | None => None
              | _ => Some (error')
             end 
              
 end.
*)
(*
Fixpoint recPredTopFn (a : nat) (c : nat) :  option outcome'  :=
  match c with
  | 0 => Some error'
  | S m => (dispatch [recPredBaseFn recPredTopFn recPred2TopFn
                    ; recPredIndFn recPredTopFn recPred2TopFn]) a m
  end 
with recPred2TopFn (a : nat) (c : nat) : option outcome'  :=
  match c with 
  | 0 => Some error'
  | S m => (dispatch [recPred2IndFn recPredTopFn recPred2TopFn]) a m
  end.
*)



