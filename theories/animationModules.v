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

(* Need to know how to invert functions  
Fixpoint recPred''fn (a : nat) : option nat :=
 match a with
 
 | S b => match recPred''fn (inv) b with
           | None => None
           | Some a' => Some (S a')
           end
 | _ => None          
 end. 
 
*)

(* Semms like the most general case that can be handled (for now) is :

recPred (typeCons1 inputVars) typeCons2 (outputVars) -> recPred (typeCons1' inputVars) (typeCons2' outputVars) 

i.e. no mixing of input output vars in the type constructors and no functions 

=

Fixpoint recPredFn...
 match x with
  | typeCons1' inputVars => match recPredFn (typeCons1 inputVars) with
                             | typeCons2 outputVars => typeCons2' outputVars 
                             ...
                                   
So typeCons1 blah needs to always give a subterm typeCons1' blah otherwise this is no longer structurally recursive

*)                                   












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
  
 



                    



(*Definition extractTypeData2 (p : program) : list (option mutual_inductive_body) := 
 (map typeConstrPatMatch.extractIndDecl ((map snd (( ( (declarations (fst p)))))))).
*)

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
 
 

Inductive outcome : Set :=
 | error : outcome
 | success : outcome.
 
Inductive outcome' : Set :=
 | error' : outcome'
 | success' : (nat) -> outcome'. 
 
 
Definition targetFn
  
  (recPred2TopFn : nat -> option outcome')
  (input : nat) : option outcome' := 

   match input with 
             | S a => match recPred2TopFn a with
                        | Some (success' (b)) => Some (success' ((S b)))
                        | None => None
                        | _ => Some error'
                        end 
             | _  => None
            end.  


(* Given inductive and input term need to produce targetFn *)

MetaRocq Quote Definition targetFnTerm := Eval compute in targetFn.
Print targetFnTerm.
MetaRocq Run (t' <- DB.undeBruijn targetFnTerm ;; t'' <- tmEval all t' ;; tmPrint t'').

Check tCase.
(*
bbody :=
              tCase
                {|
                  ci_ind :=
                    {|
                      inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                      inductive_ind := 0
                    |};
                  ci_npar := 1;
                  ci_relevance := Relevant
                |}
                {|
                  puinst := [];
                  pparams :=
                    [tInd
                       {|
                         inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                         inductive_ind := 0
                       |} []];
                  pcontext := [{| binder_name := nNamed "x"; binder_relevance := Relevant |}];
                  preturn :=
                    tApp
                      (tInd
                         {|
                           inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                           inductive_ind := 0
                         |} [])
                      [tInd
                         {|
                           inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                           inductive_ind := 0
                         |} []]
                |} (tApp (tVar "recPred2TopFn") [tVar "a"])
*)


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
 

(*
Definition mkLamfromInd (p : program) (outputVars : list string) (fuel : nat) : option term :=
 let td := extractTypeData p in
  let pmd := extractPatMatData p in
   if (preProcConsRem fuel pmd) then (mkLam (preProcCons fuel pmd) outputVars td) else None. 
*)
Definition mkLamfromInd3 (conjTm : term) (p : program) (outputTerm : term) (outputType : term) (wildCardRet : term) (fuel : nat) : option term :=
 let td := typeConstrPatMatch.extractTypeData p in
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
 
 t <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption ((typeConstrPatMatch.removeopTm (mkLamfromInd3 inputTerm termFull outputTerm outputType wildCardRet fuel))))) ;; 
 

 
 f <- tmUnquote t ;; 
 tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
 
 tmMsg "done"
 else
 tmFail "found clashing variables".
 



Parameter g : nat -> option outcome'.
MetaRocq Quote Definition gterm := g.
Print gterm.

Parameter c : case_info.
Parameter p : predicate term.
Parameter l : list (branch term).

Definition caseTm : term := tCase c p (tApp (tVar "g") [tVar "a"]) l.


Definition outerFn (input : nat) : option outcome' :=
 match input with
  | S a => g a
  | _ => None
 end.

MetaRocq Quote Definition outerFnTerm := Eval compute in outerFn.

Print outerFnTerm. 

Definition term1 : term :=
tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "a"].
  
  

       
  
Definition term2 : term :=
tApp (tConst (MPfile ["animationModules"; "Animation"], "g") []) [tVar "a"]. 

MetaRocq Run (t <- tmQuote (option outcome') ;; tmDefinition "retType" t).
MetaRocq Run (t <- tmQuote (@None outcome') ;; tmDefinition "wildCardRet" t).

Print retType.

MetaRocq Run (justAnimatePatMat2 recPredFull term1 <%nat%> term2 retType wildCardRet "result" 50).

Print result.

Compute <%success'%>.

Inductive recPredFullOut' : nat -> outcome' -> Prop :=
 | recPredFullBaseOut' : recPredFullOut' 1 (success' 3)  
 | recPredFullConsOut' : forall a b, recPredInd1Out' a (success' b) -> recPredFullOut' (S a) (success' (S b))

with recPredInd1Out' : nat -> outcome' -> Prop :=  
 | recPredInd1ConsOut' : forall a b, recPredFullOut' a (success' b)  -> recPredInd1Out' a (success' b).



MetaRocq Run (justAnimatePatMat2 (recPredFullOut') (tApp (tConstruct
            {|
              inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
              inductive_ind := 0
            |} 1 [])[tVar "b"]) <%outcome'%>    (tApp (tConstruct
            {|
              inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
              inductive_ind := 0
            |} 1 [])
         [tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
            [tVar "b"]]) <%outcome'%>  <%error'%> "result2" (50)). 

Print result2.

Definition recPredIndFnSimpl
  
  (recPred2TopFn : nat -> option outcome')
  (a : nat) : option outcome' := 

  
                     
                       match recPred2TopFn a with
                        | Some (success' (b)) => Some (success' ((S b)))
                        | None => None
                        | _ => Some error'
                        end.
                         
MetaRocq Quote Definition simplTerm := Eval compute in recPredIndFnSimpl.

MetaRocq Run (t' <- DB.undeBruijn simplTerm ;; t'' <- tmEval all t' ;; tmPrint t'').
   
             
           
Definition recPredIndFnSimpl'
  
 
  (res : option outcome') : option outcome' := 

  
                     
                       match res with
                        | Some (success' (b)) => Some (success' ((S b)))
                        | None => None
                        | _ => Some error'
                        end.


Definition compositeTerm : term :=
(tLam "recPred2TopFn"
   (tProd {| binder_name := nAnon; binder_relevance := Relevant |} <%nat%>
      (tApp
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option"); inductive_ind := 0
            |} [])
         [tInd
            {|
              inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
              inductive_ind := 0
            |} []]))
   (tLam "a" <%nat%> (tApp <%recPredIndFnSimpl'%> [(tApp (tVar "recPred2TopFn") [tVar "a"])]))).  

MetaRocq Run (t' <- DB.deBruijn compositeTerm ;; t'' <- tmEval all t' ;; f <- tmUnquote t'' ;; tmPrint f).
                        
                         
MetaRocq Quote Definition simplTerm' := Eval compute in recPredIndFnSimpl'.

MetaRocq Run (t' <- DB.undeBruijn simplTerm' ;; t'' <- tmEval all t' ;; tmPrint t'').
(*   
Fixpoint dispatchInternal (inT : Type) (outT : Type) (wildCardVal : outT) (eqChk : outT -> bool)
                            (listFn : list (inT -> outT)) : (inT -> outT) :=
 fun x => match listFn with
           | [] => wildCardVal
           | h :: t => if (eqChk (h x)) then (dispatchInternal inT outT wildCardVal eqChk t) x else (h x)
          end .
          
MetaRocq Run (t <- tmQuote (dispatchInternal nat nat 0);; tmPrint t).          
            
*)             

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
 
 let inputTerm := tApp <%eq%> [inputType; inputTerm'; tVar "v_init"] in 
 if andb (noRepeat (fst (collectVarSets (typeConstrPatMatch.preProcCons fuel inputTerm))) (snd (collectVarSets (typeConstrPatMatch.preProcCons fuel inputTerm))))  (typeConstrPatMatch.preProcConsRem fuel inputTerm) then 
 
 t <- tmEval all  (typeConstrPatMatch.removeopTm (DB.deBruijnOption ((typeConstrPatMatch.removeopTm (mkLamfromInd3 inputTerm termFull outputTerm outputType wildCardRet fuel))))) ;; 
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
(* 
Definition mkMulPatMatFn' (fns : list term) (wildCardRet : term) (inputType : term) (outputType : term) (nameFn : string)  : TemplateMonad unit :=
f <- tmUnquote (tApp <%defaultVal%> [inputType; outputType; wildCardRet; (tApp <%dispatchInternal%> [inputType; outputType; (mkLstTm' fns)])])  ;; 
 tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (nameFn) (Some hnf) ;;
 
 tmMsg "done".
 
Definition mkMulPatMatFn {A : Type} (induct : A) (branchData : list ((prod term term))) (inputType : term)  (outputType : term) (wildCardRet : term) (nmFn : string) (fuel : nat) : TemplateMonad unit :=
 subfns <- justAnimateMultPat induct branchData inputType outputType fuel ;;
 mkMulPatMatFn' subfns wildCardRet inputType outputType nmFn.
 
 *)
 
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





MetaRocq Run (t <- tmQuote (fun a : nat => S a) ;; tmPrint t).

Print outcome'.

(* (tApp <%recPredIndFnSimpl'%> [(tApp (tVar "recPred2TopFn") [tVar "a"])]))).  
*)
(*
Definition joinPatMat (preOutToPostOutFn : term) (preIn : term) (postIn : term) (nmFnPreInPreOut : string) : term
 tmLam nmFnPreInPreOut typeInfo (mkFn postIn (tApp preOutToPostOutFn)[tApp (tVar nmFnPreInPreOut)[preIn]).
 
 with preOuttopostOutFn = mkFn preOut postOut   

*)
(*
target : 
targetfn (f : nat -> option') (input : nat) : (option') :=
 match input with
 | S a => match f a with
           | success b => success (S b)
           | _  => error

 | _ => error
 
 preIn :  a
 postIn : S a
 preOut : b --> success b
 postOut : S b ---> success S b
*)

Print tLam.

MetaRocq Quote Definition fnT := (nat -> (list nat)).
Print fnT.



Definition prLstToLstPr (l1 : list term) (l2: list term) (wildCardRetVal : term) : list (prod term term). Admitted.


Definition joinPatMat {A : Type} (induct : A) (preIn : term) (preInType : term) (preOut : term) (preOutType : term)
                      (postIn : term) (postInType : term) (postOut : term) (postOutType : term)  (wildCardRet : term) (nmFn : string)
                      (nmFnpreInpreOut : string)  (fuel : nat) : TemplateMonad unit :=
 
let preInpreOutFnType := (tProd {| binder_name := nAnon; binder_relevance := Relevant |} preInType preOutType) in
preOutTopostOutFn <- mkMulPatMatFn (induct) ([(preOut, postOut)]) (preOutType)  (postOutType) (wildCardRet)  (fuel) ;;

tBody <-  mkMulPatMatFn (induct) ([(postIn, ((tApp preOutTopostOutFn [tApp (tVar nmFnpreInpreOut)[preIn]])))]) postInType postOutType wildCardRet fuel ;;




t' <- tmEval all (removeopTm (DB.deBruijnOption (tLam nmFnpreInpreOut preInpreOutFnType tBody))) ;;

f <- tmUnquote t';;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (nmFn) (Some hnf) ;; tmMsg "done".
              
              
       
Check error'.

Parameter v : nat.

Compute <% (success' (S v))%>.
Compute <% (Some v) %>.

Definition preInT : term :=  (tVar "a").
Definition preOutT : term := (tApp (tConstruct {| inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'"); inductive_ind := 0 |} 1 []) [tVar "b"]). 
Definition postInT : term := (tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 []) [tVar "a"]).
Definition postOutT : term :=  (tApp (tConstruct
            {|
              inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
              inductive_ind := 0
            |} 1 [])
         [tApp (tConstruct {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
            [tVar "b"]]).
            
MetaRocq Run (t <- justAnimatePatMat4 recPredFullOut' preOutT <%outcome'%> (tApp
         (tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option"); inductive_ind := 0
            |} 0 [])
         [<%outcome'%>; postOutT]) (tApp
                        (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option"); inductive_ind := 0 |}
                         [])[<%outcome'%>]) 
                         (tApp (tConstruct
                         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option"); inductive_ind := 0 |} 1
                          []) [<%outcome'%>]) 50 ;; tmPrint t).            

MetaRocq Run (t <- mkMulPatMatFn (recPredFullOut') [(preOutT, postOutT)] <%outcome'%> <%outcome'%> <%error'%> 50 ;; tmPrint t).
   
MetaRocq Run (joinPatMat (recPredFullOut') (preInT) (<%nat%>) (preOutT) (<%outcome'%>) (postInT) (<%nat%>) (postOutT) 
                         (<%outcome'%>) (<%error'%>) ("result3") ("func") (50)).
                         
Print result3.                         

Compute (result3 (fun x : nat => success' (S (S x))) 8).

Compute (result3 (fun x : nat => success' (S (S x))) 0).



Compute <%(hd 0 [1;2;3])%>.





(* CODE FOR GLUING EVERYTHING TOGETHER * ________________________________________________________________ *)














 

(*
tLam "v2" <%nat%>
            (tCase
               {|
                 ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                 ci_npar := 0;
                 ci_relevance := Relevant
               |}
               {|
                 puinst := [];
                 pparams := [];
                 pcontext := [{| binder_name := nNamed "v3"; binder_relevance := Relevant |}];
                 preturn :=
                   tApp
                     (tInd
                        {|
                          inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                          inductive_ind := 0
                        |} [])
                     [tInd
                        {|
                          inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                          inductive_ind := 0
                        |} []]
               |} (tVar "v3")
               [{|
                  bcontext := [];
                  bbody :=
                    tApp
                      (tConstruct
                         {|
                           inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                           inductive_ind := 0
                         |} 1 [])
                      [tApp
                         (tInd
                            {|
                              inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list");
                              inductive_ind := 0
                            |} [])
                         [<%nat%>]]
                |};
                {|
                  bcontext := [{| binder_name := nNamed "v4"; binder_relevance := Relevant |}];
                  bbody := tApp (tConst (MPfile ["animationModules"; "Animation"], "g") []) [tVar "v4"]
                |}])
       
    
    
tLam "input" <%nat%>
  (tCase
     {|
       ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
       ci_npar := 0;
       ci_relevance := Relevant
     |}
     {|
       puinst := [];
       pparams := [];
       pcontext := [{| binder_name := nNamed "input"; binder_relevance := Relevant |}];
       preturn :=
         tApp
           (tInd
              {|
                inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                inductive_ind := 0
              |} [])
           [tInd
              {|
                inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                inductive_ind := 0
              |} []]
     |} (tRel 0)
     [{|
        bcontext := [];
        bbody :=
          tApp
            (tConstruct
               {|
                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                 inductive_ind := 0
               |} 1 [])
            [tInd
               {|
                 inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                 inductive_ind := 0
               |} []]
      |};
      {|
        bcontext := [{| binder_name := nNamed "a"; binder_relevance := Relevant |}];
        bbody := tApp (tConst (MPfile ["animationModules"; "Animation"], "g") []) [tRel 0]
      |}])       
 *)      
MetaRocq Run (t <- tmQuoteRecTransp  recPredFull  true ;; tmDefinition "termFull" t). 
Print termFull.

(* Goal : outerFn *) 

Parameter x : nat.
Parameter a : nat.
(*MetaRocq Quote Definition term1' := (x = a).

Print term1'. *)
(*

Compute ((mkLamfromInd3 term1' termFull term2 retType 30)). 
Print term.

Compute (typeConstrPatMatch.preProcCons 30 term1').

Compute (replaceVarsTm term2 (typeConstrPatMatch.preProcCons 30 term1') 30).


Compute (mkLam2 (typeConstrPatMatch.preProcCons 30 term1') term2 retType (extractTypeData2 termFull) 30). 
  
(** PROBLEM !! RETURNING EMPTY LIST **)

Search (list _ -> option _).
Search (string -> string -> bool).

Compute ((typeConstrPatMatch.extractTypeData termFull)).
Compute (map typeConstrPatMatch.extractIndDecl ((map snd (( ((declarations (fst termFull)))))))).

*)



Fixpoint dispatch {A : Type} {B : Type} (lst : list (A -> nat -> option B)) : A -> nat -> option B :=
 match lst with
 | [] => (fun x y => None)
 | h :: t => fun x y => let g := h x y in 
                         match g with
                         | None => dispatch t x y
                         | _ => g
                        end 
 
 end.



(* Inline dispatch fn
Fixpoint recPredTopFn (a : nat) (c : nat) :  option outcome'  :=


match c with
 | 0 => Some error'
 | S m => (dispatch' [recPredBaseFn ; recPredIndFn] m) a m
end 

with recPredBaseFn (a : nat) (c : nat) : option outcome' :=     
 match c with
  | 0 => Some error'
  | S m =>   match a with
                | 1 => Some (success' (3))
                | _ => None
              end
 end           
with recPredIndFn (a : nat) (c : nat) : option outcome' := 
 match c with 
  | 0 => Some error'
  | S m =>  match a with 
             | S a' => match recPred2TopFn a' m with
                        | Some (success' (b)) => Some (success' ((S b)))
                        | None => None
                        | _ => Some error'
                        end 
             | _  => None
            end 
           
 end 
            
                                   
 
with recPred2TopFn (a : nat) (c : nat) : option outcome'  :=


match c with 
 | 0 => Some error'
 | S m => (dispatch' [recPred2IndFn] m) a m
end 
  
with recPred2IndFn (a : nat) (c : nat) : option outcome' :=  
 match c with  
  | 0 => Some error'
  | S m =>   match recPredTopFn a m with
              | Some (success' ( b)) => Some (success' ((b)))
              | None => None
              | _ => Some (error')
             end 
              
 end

with dispatch' (lst : list (nat -> nat -> option outcome')) (c : nat) : nat -> nat -> option outcome' :=
 match c with
  | 0 => (fun x y => (Some error'))
  | S m => match lst with
            | [] => (fun x y => None)
            | h :: t => fun x y => let g := h x y in 
                         
                         match g with
                         | None => (dispatch' t m) x y
                         | _ => g
                         end 
 
           end 
 end.

*) 

(*
Fixpoint recPredTopFn (a : nat) (c : nat) :  option outcome'  :=


match c with
 | 0 => Some error'
 | S m => (dispatch [recPredBaseFn ; recPredIndFn]) a m
end 

with recPredBaseFn (a : nat) (c : nat) : option outcome' :=     
 match c with
  | 0 => Some error'
  | S m =>   match a with
                | 1 => Some (success' (3))
                | _ => None
              end
 end           
with recPredIndFn (a : nat) (c : nat) : option outcome' := 
 match c with 
  | 0 => Some error'
  | S m =>  match a with 
             | S a' => match recPred2TopFn a' m with
                        | Some (success' (b)) => Some (success' ((S b)))
                        | None => None
                        | _ => Some error'
                        end 
             | _  => None
            end 
           
 end 
            
                                   
 
with recPred2TopFn (a : nat) (c : nat) : option outcome'  :=


match c with 
 | 0 => Some error'
 | S m => (dispatch [recPred2IndFn]) a m
end 
  
with recPred2IndFn (a : nat) (c : nat) : option outcome' :=  
 match c with  
  | 0 => Some error'
  | S m =>   match recPredTopFn a m with
              | Some (success' ( b)) => Some (success' ((b)))
              | None => None
              | _ => Some (error')
             end 
              
 end.
*)

Definition recPredBaseFn
  (recPredTopFn : nat -> nat -> option outcome')
  (recPred2TopFn : nat -> nat -> option outcome')
  (a : nat) (c : nat) : option outcome' :=     
 match c with
  | 0 => Some error'
  | S m =>   match a with
                | 1 => Some (success' (3))
                | _ => None
              end
 end .          
Definition recPredIndFn
  (recPredTopFn : nat -> nat -> option outcome')
  (recPred2TopFn : nat -> nat -> option outcome')
  (a : nat) (c : nat) : option outcome' := 

 match c with 
  | 0 => Some error'
  | S m =>  match a with 
             | S a' => match recPred2TopFn a' m with
                        | Some (success' (b)) => Some (success' ((S b)))
                        | None => None
                        | _ => Some error'
                        end 
             | _  => None
            end 
           
 end.
  
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


Fixpoint recPredTopFn' (ind : nat) (a : nat) (fuel : nat) :  option outcome'  :=
  match ind with 
   | 0 => match fuel with
          | 0 => Some error'
          | S m => (dispatch [recPredBaseFn (recPredTopFn' 0) (recPredTopFn' 1)
                    ; recPredIndFn (recPredTopFn' 0) (recPredTopFn' 1)]) a m
  
          end 
  
   | 1 => match fuel with 
           | 0 => Some error'
           | S m => (dispatch [recPred2IndFn (recPredTopFn' 0) (recPredTopFn' 1)]) a m
          end
  
   | _ => None
  end.  









Compute (recPredTopFn' 0 7 40).  

MetaRocq Quote Definition topFnTerm := Eval compute in recPredTopFn.

MetaRocq Run (t <- DB.undeBruijn topFnTerm ;; t' <- tmEval all t ;; tmDefinition "topFnTm" t').

Print topFnTm. 

Definition dummy (ind : nat) : bool :=
 match ind with 
  | 0 => true
  | 1 => true
  | 2 => true
  | _ => false
 end.

MetaRocq Quote Definition dummy_syntax := Eval compute in dummy.
 
MetaRocq Run (t <- DB.undeBruijn dummy_syntax ;; t' <- tmEval all t ;; tmDefinition "dummyTm" t').

Print dummyTm.

Search (string -> string -> string).
Search (nat -> string).


Definition mkName (n : nat) : string :=
 String.append "n" (string_of_nat n).
 

Fixpoint natPatMatchBr (outputType : term) (wildCardRet : term) (retVals : list term) (index : nat) : list (branch term) :=
 match retVals with
  | [] => [{|
        bcontext := [];
        bbody :=
         wildCardRet
      |};
      {|
        bcontext := [{| binder_name := nNamed (mkName index); binder_relevance := Relevant |}];
        bbody := wildCardRet |}]
  
  | [h] =>  [{|
        bcontext := [];
        bbody :=
         h
      |};
      {|
        bcontext := [{| binder_name := nNamed (mkName index); binder_relevance := Relevant |}];
        bbody := wildCardRet |}]     
 
 
 
  
  | h' :: t' => [{|
        bcontext := [];
        bbody :=
          h'
      |};
      {|
        bcontext := [{| binder_name := nNamed (mkName index); binder_relevance := Relevant |}];
        bbody :=
          tCase
            {|
              ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
              ci_npar := 0;
              ci_relevance := Relevant
            |}
            {|
              puinst := [];
              pparams := [];
              pcontext := [{| binder_name := nNamed (mkName index); binder_relevance := Relevant |}];
              preturn :=
                outputType
            |} (tVar (mkName index)) (natPatMatchBr (outputType) (wildCardRet) t' (index + 1)) |}]
 end.                         
        

Definition natPatMatch (outputType : term) (wildCardRet : term) (retVals : list term) : term :=
 tLam "ind" <%nat%>
  (tCase
     {|
       ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
       ci_npar := 0;
       ci_relevance := Relevant
     |}
     {|
       puinst := [];
       pparams := [];
       pcontext := [{| binder_name := nNamed "ind"; binder_relevance := Relevant |}];
       preturn :=
         outputType
     |} (tVar "ind") (natPatMatchBr (outputType) (wildCardRet) (retVals) 0)).
     
 
  
 
Parameter default : (def term).

Definition getlst (t : term) : list (def term) :=
 match t with 
  | tFix l k => l
  | _ => []
 end.  

(* 
Compute (hd default (getlst topFnTm)). 

MetaRocq Quote Definition zeroList := [0; 0; 0].
Print zeroList.

*)

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

MetaRocq Quote Definition fnTypeTm := (nat -> nat -> (option outcome')).

(* Print fnTypeTm. *)

MetaRocq Quote Definition dispatchTm := (@dispatch nat outcome').
(* Print dispatchTm. *) 

Definition myTerm : named_term :=
tFix
  [{|
     dname := {| binder_name := nNamed "recPredTopFn"; binder_relevance := Relevant |};
     dtype :=
       tPro "a" <%nat%>
         (tPro "c" <%nat%>
            (tApp
               (tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                    inductive_ind := 0
                  |} [])
               [tInd
                  {|
                    inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                    inductive_ind := 0
                  |} []]));
     dbody :=
       tLam "a" <%nat%>
         (tLam "c" <%nat%>
            (tCase
               {|
                 ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                 ci_npar := 0;
                 ci_relevance := Relevant
               |}
               {|
                 puinst := [];
                 pparams := [];
                 pcontext := [{| binder_name := nNamed "c"; binder_relevance := Relevant |}];
                 preturn :=
                   tApp
                     (tInd
                        {|
                          inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                          inductive_ind := 0
                        |} [])
                     [tInd
                        {|
                          inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                          inductive_ind := 0
                        |} []]
               |} (tVar "c")
               [{|
                  bcontext := [];
                  bbody :=
                    tApp
                      (tConstruct
                         {|
                           inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                           inductive_ind := 0
                         |} 0 [])
                      [tInd
                         {|
                           inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                           inductive_ind := 0
                         |} [];
                       tConstruct
                         {|
                           inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                           inductive_ind := 0
                         |} 0 []]
                |};
                {|
                  bcontext := [{| binder_name := nNamed "m"; binder_relevance := Relevant |}];
                  bbody := tApp (tApp dispatchTm ([mkLstTm fnTypeTm ["recPredBaseFn"; "recPredIndFn"]])) [tVar "a"; tVar "m"]  
                                    
                              |}]
                     )); rarg := 1 |} (* USE dispatchTm  instead of unfolding dispatch function *)
                
     
   
                      
                
     
   ;
   {|
     dname := {| binder_name := nNamed "recPredBaseFn"; binder_relevance := Relevant |};
     dtype :=
       tPro "a" <%nat%>
         (tPro "c" <%nat%>
            (tApp
               (tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                    inductive_ind := 0
                  |} [])
               [tInd
                  {|
                    inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                    inductive_ind := 0
                  |} []]));
     dbody :=
       tLam "a" <%nat%>
         (tLam "c" <%nat%>
            (tCase
               {|
                 ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                 ci_npar := 0;
                 ci_relevance := Relevant
               |}
               {|
                 puinst := [];
                 pparams := [];
                 pcontext := [{| binder_name := nNamed "c"; binder_relevance := Relevant |}];
                 preturn :=
                   tApp
                     (tInd
                        {|
                          inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                          inductive_ind := 0
                        |} [])
                     [tInd
                        {|
                          inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                          inductive_ind := 0
                        |} []]
               |} (tVar "c")
               [{|
                  bcontext := [];
                  bbody :=
                    tApp
                      (tConstruct
                         {|
                           inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                           inductive_ind := 0
                         |} 0 [])
                      [tInd
                         {|
                           inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                           inductive_ind := 0
                         |} [];
                       tConstruct
                         {|
                           inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                           inductive_ind := 0
                         |} 0 []]
                |};
                {|
                  bcontext := [{| binder_name := nNamed "m"; binder_relevance := Relevant |}];
                  bbody :=
                    tCase
                      {|
                        ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                        ci_npar := 0;
                        ci_relevance := Relevant
                      |}
                      {|
                        puinst := [];
                        pparams := [];
                        pcontext := [{| binder_name := nNamed "a"; binder_relevance := Relevant |}];
                        preturn :=
                          tApp
                            (tInd
                               {|
                                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                 inductive_ind := 0
                               |} [])
                            [tInd
                               {|
                                 inductive_mind :=
                                   (MPfile ["animationModules"; "Animation"], "outcome'");
                                 inductive_ind := 0
                               |} []]
                      |} (tVar "a")
                      [{|
                         bcontext := [];
                         bbody :=
                           tApp
                             (tConstruct
                                {|
                                  inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                  inductive_ind := 0
                                |} 1 [])
                             [tInd
                                {|
                                  inductive_mind :=
                                    (MPfile ["animationModules"; "Animation"], "outcome'");
                                  inductive_ind := 0
                                |} []]
                       |};
                       {|
                         bcontext := [{| binder_name := nNamed "n"; binder_relevance := Relevant |}];
                         bbody :=
                           tCase
                             {|
                               ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                               ci_npar := 0;
                               ci_relevance := Relevant
                             |}
                             {|
                               puinst := [];
                               pparams := [];
                               pcontext :=
                                 [{| binder_name := nNamed "n"; binder_relevance := Relevant |}];
                               preturn :=
                                 tApp
                                   (tInd
                                      {|
                                        inductive_mind :=
                                          (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                        inductive_ind := 0
                                      |} [])
                                   [tInd
                                      {|
                                        inductive_mind :=
                                          (MPfile ["animationModules"; "Animation"], "outcome'");
                                        inductive_ind := 0
                                      |} []]
                             |} (tVar "n")
                             [{|
                                bcontext := [];
                                bbody :=
                                  tApp
                                    (tConstruct
                                       {|
                                         inductive_mind :=
                                           (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                         inductive_ind := 0
                                       |} 0 [])
                                    [tInd
                                       {|
                                         inductive_mind :=
                                           (MPfile ["animationModules"; "Animation"], "outcome'");
                                         inductive_ind := 0
                                       |} [];
                                     tApp
                                       (tConstruct
                                          {|
                                            inductive_mind :=
                                              (MPfile ["animationModules"; "Animation"], "outcome'");
                                            inductive_ind := 0
                                          |} 1 [])
                                       [tApp
                                          (tConstruct
                                             {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
                                          [tApp
                                             (tConstruct
                                                {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1 [])
                                             [tApp
                                                (tConstruct
                                                   {| inductive_mind := <?nat?>; inductive_ind := 0 |} 1
                                                   [])
                                                [tConstruct
                                                   {| inductive_mind := <?nat?>; inductive_ind := 0 |} 0
                                                   []]]]]]
                              |};
                              {|
                                bcontext :=
                                  [{| binder_name := nNamed "n0"; binder_relevance := Relevant |}];
                                bbody :=
                                  tApp
                                    (tConstruct
                                       {|
                                         inductive_mind :=
                                           (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                         inductive_ind := 0
                                       |} 1 [])
                                    [tInd
                                       {|
                                         inductive_mind :=
                                           (MPfile ["animationModules"; "Animation"], "outcome'");
                                         inductive_ind := 0
                                       |} []]
                              |}]
                       |}]
                |}]));
     rarg := 1
   |};
   {|
     dname := {| binder_name := nNamed "recPredIndFn"; binder_relevance := Relevant |};
     dtype :=
       tPro "a" <%nat%>
         (tPro "c" <%nat%>
            (tApp
               (tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                    inductive_ind := 0
                  |} [])
               [tInd
                  {|
                    inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                    inductive_ind := 0
                  |} []]));
     dbody :=
       tLam "a" <%nat%>
         (tLam "c" <%nat%>
            (tCase
               {|
                 ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                 ci_npar := 0;
                 ci_relevance := Relevant
               |}
               {|
                 puinst := [];
                 pparams := [];
                 pcontext := [{| binder_name := nNamed "c"; binder_relevance := Relevant |}];
                 preturn :=
                   tApp
                     (tInd
                        {|
                          inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                          inductive_ind := 0
                        |} [])
                     [tInd
                        {|
                          inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                          inductive_ind := 0
                        |} []]
               |} (tVar "c")
               [{|
                  bcontext := [];
                  bbody :=
                    tApp
                      (tConstruct
                         {|
                           inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                           inductive_ind := 0
                         |} 0 [])
                      [tInd
                         {|
                           inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                           inductive_ind := 0
                         |} [];
                       tConstruct
                         {|
                           inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                           inductive_ind := 0
                         |} 0 []]
                |};
                {|
                  bcontext := [{| binder_name := nNamed "m"; binder_relevance := Relevant |}];
                  bbody :=
                    tCase
                      {|
                        ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                        ci_npar := 0;
                        ci_relevance := Relevant
                      |}
                      {|
                        puinst := [];
                        pparams := [];
                        pcontext := [{| binder_name := nNamed "a"; binder_relevance := Relevant |}];
                        preturn :=
                          tApp
                            (tInd
                               {|
                                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                 inductive_ind := 0
                               |} [])
                            [tInd
                               {|
                                 inductive_mind :=
                                   (MPfile ["animationModules"; "Animation"], "outcome'");
                                 inductive_ind := 0
                               |} []]
                      |} (tVar "a")
                      [{|
                         bcontext := [];
                         bbody :=
                           tApp
                             (tConstruct
                                {|
                                  inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                  inductive_ind := 0
                                |} 1 [])
                             [tInd
                                {|
                                  inductive_mind :=
                                    (MPfile ["animationModules"; "Animation"], "outcome'");
                                  inductive_ind := 0
                                |} []]
                       |};
                       {|
                         bcontext := [{| binder_name := nNamed "a'"; binder_relevance := Relevant |}];
                         bbody :=
                           tCase
                             {|
                               ci_ind :=
                                 {|
                                   inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                   inductive_ind := 0
                                 |};
                               ci_npar := 1;
                               ci_relevance := Relevant
                             |}
                             {|
                               puinst := [];
                               pparams :=
                                 [tInd
                                    {|
                                      inductive_mind :=
                                        (MPfile ["animationModules"; "Animation"], "outcome'");
                                      inductive_ind := 0
                                    |} []];
                               pcontext :=
                                 [{| binder_name := nNamed "x"; binder_relevance := Relevant |}];
                               preturn :=
                                 tApp
                                   (tInd
                                      {|
                                        inductive_mind :=
                                          (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                        inductive_ind := 0
                                      |} [])
                                   [tInd
                                      {|
                                        inductive_mind :=
                                          (MPfile ["animationModules"; "Animation"], "outcome'");
                                        inductive_ind := 0
                                      |} []]
                             |} (tApp (tVar "recPred2TopFn") [tVar "a'"; tVar "m"])
                             [{|
                                bcontext :=
                                  [{| binder_name := nNamed "o"; binder_relevance := Relevant |}];
                                bbody :=
                                  tCase
                                    {|
                                      ci_ind :=
                                        {|
                                          inductive_mind :=
                                            (MPfile ["animationModules"; "Animation"], "outcome'");
                                          inductive_ind := 0
                                        |};
                                      ci_npar := 0;
                                      ci_relevance := Relevant
                                    |}
                                    {|
                                      puinst := [];
                                      pparams := [];
                                      pcontext :=
                                        [{| binder_name := nNamed "o"; binder_relevance := Relevant |}];
                                      preturn :=
                                        tApp
                                          (tInd
                                             {|
                                               inductive_mind :=
                                                 (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                               inductive_ind := 0
                                             |} [])
                                          [tInd
                                             {|
                                               inductive_mind :=
                                                 (MPfile ["animationModules"; "Animation"], "outcome'");
                                               inductive_ind := 0
                                             |} []]
                                    |} (tVar "o")
                                    [{|
                                       bcontext := [];
                                       bbody :=
                                         tApp
                                           (tConstruct
                                              {|
                                                inductive_mind :=
                                                  (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                                inductive_ind := 0
                                              |} 0 [])
                                           [tInd
                                              {|
                                                inductive_mind :=
                                                  (MPfile ["animationModules"; "Animation"], "outcome'");
                                                inductive_ind := 0
                                              |} [];
                                            tConstruct
                                              {|
                                                inductive_mind :=
                                                  (MPfile ["animationModules"; "Animation"], "outcome'");
                                                inductive_ind := 0
                                              |} 0 []]
                                     |};
                                     {|
                                       bcontext :=
                                         [{| binder_name := nNamed "b"; binder_relevance := Relevant |}];
                                       bbody :=
                                         tApp
                                           (tConstruct
                                              {|
                                                inductive_mind :=
                                                  (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                                inductive_ind := 0
                                              |} 0 [])
                                           [tInd
                                              {|
                                                inductive_mind :=
                                                  (MPfile ["animationModules"; "Animation"], "outcome'");
                                                inductive_ind := 0
                                              |} [];
                                            tApp
                                              (tConstruct
                                                 {|
                                                   inductive_mind :=
                                                     (MPfile ["animationModules"; "Animation"],
                                                      "outcome'");
                                                   inductive_ind := 0
                                                 |} 1 [])
                                              [tApp
                                                 (tConstruct
                                                    {| inductive_mind := <?nat?>; inductive_ind := 0 |}
                                                    1 [])
                                                 [tVar "b"]]]
                                     |}]
                              |};
                              {|
                                bcontext := [];
                                bbody :=
                                  tApp
                                    (tConstruct
                                       {|
                                         inductive_mind :=
                                           (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                         inductive_ind := 0
                                       |} 1 [])
                                    [tInd
                                       {|
                                         inductive_mind :=
                                           (MPfile ["animationModules"; "Animation"], "outcome'");
                                         inductive_ind := 0
                                       |} []]
                              |}]
                       |}]
                |}]));
     rarg := 1
   |};
   {|
     dname := {| binder_name := nNamed "recPred2TopFn"; binder_relevance := Relevant |};
     dtype :=
       tPro "a" <%nat%>
         (tPro "c" <%nat%>
            (tApp
               (tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                    inductive_ind := 0
                  |} [])
               [tInd
                  {|
                    inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                    inductive_ind := 0
                  |} []]));
     dbody :=
       tLam "a" <%nat%>
         (tLam "c" <%nat%>
            (tCase
               {|
                 ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                 ci_npar := 0;
                 ci_relevance := Relevant
               |}
               {|
                 puinst := [];
                 pparams := [];
                 pcontext := [{| binder_name := nNamed "c"; binder_relevance := Relevant |}];
                 preturn :=
                   tApp
                     (tInd
                        {|
                          inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                          inductive_ind := 0
                        |} [])
                     [tInd
                        {|
                          inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                          inductive_ind := 0
                        |} []]
               |} (tVar "c")
               [{|
                  bcontext := [];
                  bbody :=
                    tApp
                      (tConstruct
                         {|
                           inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                           inductive_ind := 0
                         |} 0 [])
                      [tInd
                         {|
                           inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                           inductive_ind := 0
                         |} [];
                       tConstruct
                         {|
                           inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                           inductive_ind := 0
                         |} 0 []]
                |};
                {|
                  bcontext := [{| binder_name := nNamed "m"; binder_relevance := Relevant |}];
                  bbody :=
                    tCase
                      {|
                        ci_ind :=
                          {|
                            inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                            inductive_ind := 0
                          |};
                        ci_npar := 1;
                        ci_relevance := Relevant
                      |}
                      {|
                        puinst := [];
                        pparams :=
                          [tInd
                             {|
                               inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                               inductive_ind := 0
                             |} []];
                        pcontext := [{| binder_name := nNamed "g"; binder_relevance := Relevant |}];
                        preturn :=
                          tApp
                            (tInd
                               {|
                                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                 inductive_ind := 0
                               |} [])
                            [tInd
                               {|
                                 inductive_mind :=
                                   (MPfile ["animationModules"; "Animation"], "outcome'");
                                 inductive_ind := 0
                               |} []]
                      |} (tApp (tVar "recPred2IndFn") [tVar "a"; tVar "m"])
                      [{|
                         bcontext := [{| binder_name := nNamed "b"; binder_relevance := Relevant |}];
                         bbody := tApp (tVar "recPred2IndFn") [tVar "a"; tVar "m"]
                       |};
                       {|
                         bcontext := [];
                         bbody :=
                           tApp
                             (tConstruct
                                {|
                                  inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                  inductive_ind := 0
                                |} 1 [])
                             [tInd
                                {|
                                  inductive_mind :=
                                    (MPfile ["animationModules"; "Animation"], "outcome'");
                                  inductive_ind := 0
                                |} []]
                       |}]
                |}]));
     rarg := 1
   |};
   {|
     dname := {| binder_name := nNamed "recPred2IndFn"; binder_relevance := Relevant |};
     dtype :=
       tPro "a" <%nat%>
         (tPro "c" <%nat%>
            (tApp
               (tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                    inductive_ind := 0
                  |} [])
               [tInd
                  {|
                    inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                    inductive_ind := 0
                  |} []]));
     dbody :=
       tLam "a" <%nat%>
         (tLam "c" <%nat%>
            (tCase
               {|
                 ci_ind := {| inductive_mind := <?nat?>; inductive_ind := 0 |};
                 ci_npar := 0;
                 ci_relevance := Relevant
               |}
               {|
                 puinst := [];
                 pparams := [];
                 pcontext := [{| binder_name := nNamed "c"; binder_relevance := Relevant |}];
                 preturn :=
                   tApp
                     (tInd
                        {|
                          inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                          inductive_ind := 0
                        |} [])
                     [tInd
                        {|
                          inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                          inductive_ind := 0
                        |} []]
               |} (tVar "c")
               [{|
                  bcontext := [];
                  bbody :=
                    tApp
                      (tConstruct
                         {|
                           inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                           inductive_ind := 0
                         |} 0 [])
                      [tInd
                         {|
                           inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                           inductive_ind := 0
                         |} [];
                       tConstruct
                         {|
                           inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                           inductive_ind := 0
                         |} 0 []]
                |};
                {|
                  bcontext := [{| binder_name := nNamed "m"; binder_relevance := Relevant |}];
                  bbody :=
                    tCase
                      {|
                        ci_ind :=
                          {|
                            inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                            inductive_ind := 0
                          |};
                        ci_npar := 1;
                        ci_relevance := Relevant
                      |}
                      {|
                        puinst := [];
                        pparams :=
                          [tInd
                             {|
                               inductive_mind := (MPfile ["animationModules"; "Animation"], "outcome'");
                               inductive_ind := 0
                             |} []];
                        pcontext := [{| binder_name := nNamed "x"; binder_relevance := Relevant |}];
                        preturn :=
                          tApp
                            (tInd
                               {|
                                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                 inductive_ind := 0
                               |} [])
                            [tInd
                               {|
                                 inductive_mind :=
                                   (MPfile ["animationModules"; "Animation"], "outcome'");
                                 inductive_ind := 0
                               |} []]
                      |} (tApp (tVar "recPredTopFn") [tVar "a"; tVar "m"])
                      [{|
                         bcontext := [{| binder_name := nNamed "o"; binder_relevance := Relevant |}];
                         bbody :=
                           tCase
                             {|
                               ci_ind :=
                                 {|
                                   inductive_mind :=
                                     (MPfile ["animationModules"; "Animation"], "outcome'");
                                   inductive_ind := 0
                                 |};
                               ci_npar := 0;
                               ci_relevance := Relevant
                             |}
                             {|
                               puinst := [];
                               pparams := [];
                               pcontext :=
                                 [{| binder_name := nNamed "o"; binder_relevance := Relevant |}];
                               preturn :=
                                 tApp
                                   (tInd
                                      {|
                                        inductive_mind :=
                                          (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                        inductive_ind := 0
                                      |} [])
                                   [tInd
                                      {|
                                        inductive_mind :=
                                          (MPfile ["animationModules"; "Animation"], "outcome'");
                                        inductive_ind := 0
                                      |} []]
                             |} (tVar "o")
                             [{|
                                bcontext := [];
                                bbody :=
                                  tApp
                                    (tConstruct
                                       {|
                                         inductive_mind :=
                                           (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                         inductive_ind := 0
                                       |} 0 [])
                                    [tInd
                                       {|
                                         inductive_mind :=
                                           (MPfile ["animationModules"; "Animation"], "outcome'");
                                         inductive_ind := 0
                                       |} [];
                                     tConstruct
                                       {|
                                         inductive_mind :=
                                           (MPfile ["animationModules"; "Animation"], "outcome'");
                                         inductive_ind := 0
                                       |} 0 []]
                              |};
                              {|
                                bcontext :=
                                  [{| binder_name := nNamed "b"; binder_relevance := Relevant |}];
                                bbody :=
                                  tApp
                                    (tConstruct
                                       {|
                                         inductive_mind :=
                                           (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                         inductive_ind := 0
                                       |} 0 [])
                                    [tInd
                                       {|
                                         inductive_mind :=
                                           (MPfile ["animationModules"; "Animation"], "outcome'");
                                         inductive_ind := 0
                                       |} [];
                                     tApp
                                       (tConstruct
                                          {|
                                            inductive_mind :=
                                              (MPfile ["animationModules"; "Animation"], "outcome'");
                                            inductive_ind := 0
                                          |} 1 [])
                                       [tVar "b"]]
                              |}]
                       |};
                       {|
                         bcontext := [];
                         bbody :=
                           tApp
                             (tConstruct
                                {|
                                  inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "option");
                                  inductive_ind := 0
                                |} 1 [])
                             [tInd
                                {|
                                  inductive_mind :=
                                    (MPfile ["animationModules"; "Animation"], "outcome'");
                                  inductive_ind := 0
                                |} []]
                       |}]
                |}]));
     rarg := 1
   |}]
  0.

MetaRocq Run (t <- DB.deBruijn myTerm ;; f <- tmUnquote t ;; tmPrint f).


Compute (hd default (tl (getlst myTerm))).

Definition mkConsFunTerm (nmFn : string) (inputType: term) (outputType: term) (fuelError : term) (activeMatch : term) : def term :=
 {|
         dname := {| binder_name := nNamed nmFn; binder_relevance := Relevant |};
         dtype :=
           tPro "input" inputType
             (tPro "fuel" <%nat%>
                outputType);
         dbody :=
           tLam "input" inputType
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
                     preturn :=
                       outputType
                   |} (tVar "fuel")
                   [{|
                      bcontext := [];
                      bbody :=
                        fuelError
                    |};
                    {|
                      bcontext := [{| binder_name := nNamed "m"; binder_relevance := Relevant |}];
                      bbody :=
                       activeMatch
                       
                    |}]));
         rarg := 1
       |}.

Definition mkTopFnTerm (nmFn : string) (consFnName : list string) (dispatchFnTm : term) (inputType : term) (outputType : term)
           (fuelError : term) : def term :=
 
 {|
         dname := {| binder_name := nNamed nmFn; binder_relevance := Relevant |};
         dtype :=
           tPro "input" inputType
             (tPro "fuel" <%nat%>
                outputType);
         dbody :=
           tLam "input" inputType
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
                     preturn :=
                       outputType
                   |} (tVar "fuel")
                   [{|
                      bcontext := [];
                      bbody :=
                        fuelError
                    |};
                    {|
                      bcontext := [{| binder_name := nNamed "m"; binder_relevance := Relevant |}];
                      bbody :=
                        tApp (tApp dispatchFnTm ([mkLstTm (tProd {| binder_name := nAnon; binder_relevance := Relevant |} inputType outputType)  consFnName])) [tVar "input"; tVar "m"]  
                
                    |}]));
         rarg := 1
       |}.

Parameter A : Type.
Parameter B : Type.
MetaRocq Quote Definition fnTm := (A -> B).
Print fnTm.   

Check map. 
Check app.


Definition composeClause (nameTopFn : string) (animateClauses : list (prod string term)) (inputType : term) (outputType : term) (fuelError : term) (dispatchFn : term) 
                                     : (list (def term)) :=
  (mkTopFnTerm nameTopFn (map fst animateClauses) dispatchFn inputType outputType fuelError) :: (map (fun p => mkConsFunTerm (fst p)  (inputType) (outputType) (fuelError) (snd p)) animateClauses).                                   
                                     
 
Fixpoint composeInductives (inds : list (prod string (list (prod string term)))) (inputType : term) (outputType : term) (fuelError : term) (dispatchFn : term) 
                                     : (list (def term)) := 
   match inds with
    | [] => []
    | h :: t => app (composeClause (fst h) (snd h) inputType outputType fuelError dispatchFn) (composeInductives t inputType outputType fuelError dispatchFn)
   end.                                   

 
Definition mkrecFn (ls : list (def term)) (j : nat) : term :=
 tFix ls j.
          
          
          
(*
(*
Fixpoint replaceVars (l : list term)  (dict : string -> string) (fuel : nat) : list term :=
 match fuel with
  | 0 => []
  | S m => match l with
            | [] => []
            | (tVar str) :: t => (tVar (dict str)) :: replaceVars t dict m 
            | [tApp t t'] => [tApp t (replaceVars t' dict m)]
            | [tCase c p t l] => match replaceVars [t] dict m with
                                  | [t'] => [tCase c p t' l]
                                  | _ => [tCase c p t l]
                                 end 
     
            |  other => other
           end 
       
    
 end. 
 *)

Print predicate.


Fixpoint replaceVars (l : list term)  (dict : string -> string) (fuel : nat) : list term :=
 match fuel with
  | 0 => []
  | S m => match l with
            | [] => []
            | (tVar str) :: t => (tVar (dict str)) :: replaceVars t dict m 
            | [tApp t t'] => [tApp t (replaceVars t' dict m)]
            | [tCase c p t l] => match replaceVars [t] dict m with
                                  | [t'] => [tCase c p t' l]
                                  | _ => [tCase c p t l]
                                 end 
     
            |  other => other
           end 
       
    
 end. 
 
Fixpoint sortBindersOne (outputVar : string) (lst': list ((string × term) × list string)) : (list string) :=
 match lst' with
  | [] => []
  | (h :: rest) => match h with
                    | (str1, (tVar y), _) => if (String.eqb y outputVar) then [str1] else sortBindersOne outputVar rest 
                    | _ => sortBindersOne outputVar rest
                   end 
 end.

Definition dict (lst': list ((string × term) × list string)) (var : string) : string :=
 match sortBindersOne var lst' with
  | [] => var
  | h :: t => h
 end.
 
Definition replaceVars' (l : list term) (lst': list ((string × term) × list string)) (fuel : nat) : list term :=
 replaceVars l (dict lst') fuel.
 
Definition replaceVarsTm (t : term) (lst': list ((string × term) × list string)) (fuel : nat)  : term :=
 match replaceVars' [t] lst' fuel with
  | [] => errorTm
  | [h] => h
  | _ => errorTm
 end.                                                  

*)


