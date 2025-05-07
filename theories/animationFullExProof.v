From Stdlib Require Import List.

Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.

Require Import Animation.utils.
Import MetaRocqNotations.

Require Import PeanoNat.
Local Open Scope nat_scope.
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

Print TemplateMonad.

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

MetaRocq Run test.

Check (tmQuoteInductive).
Print one_inductive_body.
MetaRocq Run (t <- tmQuoteInductive <? foo ?> ;; tmPrint t).

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
  ret tt.

MetaRocq Run (animate <? foo ?>).

Definition fooTerm : term :=
 (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "and"); inductive_ind := 0 |} [])
   [tApp
      (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} [])
      [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}
         [];
       tVar "e"; tVar "b"];
    tApp
      (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "and"); inductive_ind := 0 |} [])
      [tApp
         (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |}
            [])
         [tInd
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}
            [];
          tVar "d"; tVar "c"];
       tApp
         (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "and"); inductive_ind := 0 |}
            [])
         [tApp
            (tInd
               {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |}
               [])
            [tInd
               {|
                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0
               |} [];
             tVar "c";
             tApp (tConst (MPfile ["animationFullExProof"; "Animation"], "g3") []) [tVar "a"; tVar "e"]];
          tApp
            (tInd
               {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |}
               [])
            [tInd
               {|
                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0
               |} [];
             tApp (tConst (MPfile ["animationFullExProof"; "Animation"], "g1") []) [tVar "d"];
             tApp (tConst (MPfile ["animationFullExProof"; "Animation"], "g2") []) [tVar "a"]]]]]).

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

(* String.eqb: string -> string -> bool *)


(*Fixpoint getListConj (bigConj : term) : (list term) := (* extract list of conjuncts from big conjunction *)
 match bigConj with
  |(tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "and"); inductive_ind := 0 |} []) ls) =>
         concat (map getListConj ls)
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} []) ls' =>
              [tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} []) ls']
  | _ => nil
 end. *)


Notation "<?and?>" := (MPfile ["Logic"; "Init"; "Corelib"], "and").
Notation "<?eq?>" := (MPfile ["Logic"; "Init"; "Corelib"], "eq").
Notation "<?nat?>" := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat").
Notation "<%and%>" := (tInd {| inductive_mind := <?and?>; inductive_ind := 0 |} []).
Notation "<%eq%>" := (tInd {| inductive_mind := <?eq?>; inductive_ind := 0 |} []).
Notation "<%nat%>" := (tInd {| inductive_mind := <?nat?>; inductive_ind := 0 |} []).

(* Extracts list of conjuncts from big conjunction *)
Fixpoint getListConjLetBind (bigConj : term) : list term := 
  match bigConj with
  | tApp <%and%> ls => concat (map getListConjLetBind ls)

  | tApp <%eq%> [<%nat%>; tVar str1; tVar str2] => [tApp <% @eq %> [<%nat%>; tVar str1; tVar str2]]

  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2; tVar str3]] =>
      [tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2; tVar str3]]]

  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2]] =>
      [tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2]]]
  | _ => []
 end.

(* extract list of conjuncts from big conjunction *)
Fixpoint getListConjGuardCon (bigConj : term) : list term := 
  match bigConj with
  | tApp <%and%> ls => concat (map getListConjGuardCon ls)
  | tApp <%eq%> [<%nat%>; tApp fn1 [tVar varStr1]; tApp fn2 [tVar varStr2]] =>
      [tApp <%eq%> [<%nat%>; tApp fn1 [tVar varStr1]; tApp fn2 [tVar varStr2]]] 
  | _ => []
 end.

Compute (getListConjGuardCon fooTerm).


(* extract ordered list of vars from conjunct *)
Definition extractOrderedVars (t : term) : list string := 
  match t with
  | tApp <%eq%> [<%nat%>; tVar str1; tVar str2] => [str1 ; str2]
  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2; tVar str3]] => [str1 ; str2 ; str3]

  (* Combine the pattern matches to handle fns of arbitrary arity *)
  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2]] => [str1 ; str2]

  | _ => nil
  end.


(* Instantiate partialLetFun with identity *)

Definition animateOneConjSucc (conj : term) (partialLetfn : term -> term) : option (term -> term) :=
  match conj with
  | tApp <%eq%> [<%nat%>; tVar str1; tVar str2] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1; binder_relevance := Relevant |}
                                 (tVar str2%bs) <%nat%>) t))

  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2; tVar str3]] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn [tVar str2%bs; tVar str3%bs]) <%nat%>) t))

  | tApp <%eq%> [<%nat%>; tVar str1; tApp fn [tVar str2]] =>
    Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
                                 (tApp fn [tVar str2%bs]) <%nat%>) t))

  | _ => None
 end.

(* Instantiate partialGuard with Identity * No need to check for known vars when animating guard condition since all
vars should be known at this point in the computation *)

 Definition animateOneConjSuccGuard (conj : term) (partialGuard : term) :  term :=
  match conj with
  | tApp <%eq%> [<%nat%>; tApp fn1 [tVar varStr1]; tApp fn2 [tVar varStr2]] =>
    tApp (tConst <? andb ?> [])
         [ partialGuard
         ; tApp (tConst <? Nat.eqb ?> []) [tApp fn1 [tVar varStr1]
         ; tApp fn2 [tVar varStr2]]]
  | _ => <% false %>
  end.

Definition animateOneConj (conj : term) (knownVar : list string) (partialProg : term -> term) : option (list string * (term -> term)) :=
  if isListSubStr (tl (extractOrderedVars conj)) knownVar then
  (let t' := animateOneConjSucc conj partialProg in
    match t' with
    | Some t'' => Some (app knownVar (extractOrderedVars conj), t'')
    | None => None
    end)
  else None.


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

Definition constrFn (letBind : term -> term) (guardCon : term) : term :=
  tLambda {| binder_name := nNamed "a"%bs; binder_relevance := Relevant |} <%nat%>
    (tLambda {| binder_name := nNamed "b"%bs; binder_relevance := Relevant |} (<%nat%>)
      (letBind
        (tCase {| ci_ind := {| inductive_mind := <? bool ?>; inductive_ind := 0 |}
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
                          tApp (tConstruct {| inductive_mind := <? list ?>; inductive_ind := 0 |} 1 [])
                            [<%nat%>; tVar "c"%bs;
                             tApp (tConstruct {| inductive_mind := <? list ?>; inductive_ind := 0 |} 1 [])
                               [<%nat%>; tVar "d"%bs;
                                tApp (tConstruct {| inductive_mind := <? list ?>; inductive_ind := 0 |} 1 [])
                                  [<%nat%>; tVar "e"%bs;
                                   tApp (tConstruct {| inductive_mind := <? list ?>; inductive_ind := 0 |} 0 [])
                                     [<%nat%>]]]]]
                   |};
                   {| bcontext := []
                    ; bbody :=
                       tApp (tConstruct {| inductive_mind := <? option ?>; inductive_ind := 0 |} 1 [])
                         [tApp <% @list %> [<%nat%>]]
                   |}]))).

Fixpoint animateOneConjGuardList (conj : list term) : term :=
  match conj with
  | [] => <% true %>
  | h :: t =>
    match animateOneConjGuardList t with
    | gt => animateOneConjSuccGuard h gt
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

Compute (constrFn (animateListConj (getListConjLetBind fooTerm) nil ["a" ; "b"] 10 (fun t : term => t))
           ((tApp <% andb %>
              [<% true %>;
               tApp <% Nat.eqb %>
                 [tApp (tConst (MPfile ["animationFullEx"], "g1") []) [tVar "d"];
                  tApp (tConst (MPfile ["animationFullEx"], "g2") []) [tVar "a"]]]))).

Definition animate' (t : term) : TemplateMonad (nat -> nat -> (option (list nat))) :=
  t' <- DB.deBruijn t ;;
  f <- @tmUnquoteTyped (nat -> nat -> (option (list nat))) t' ;;
  tmPrint f ;;
  ret f.

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



(*ERROR below:
Error:
Anomaly
"Constant animationFullExProof.g3 does not appear in the environment."
Please report at http://coq.inria.fr/bugs/.
*)
MetaRocq Run (animate'' fooTerm ["a" ; "b"] 10).
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



MetaRocq Run (animate <? fooCon ?>).
 

(* Fixpoint deconTypeCon (conj : term) : list (option string) :=
 match conj with
  | tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1 [])
      ((tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} []) ::
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
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1 [])
      [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} [];
       tApp
         (tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} 1
            []) [tVar "a"];
       tApp
         (tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1
            [])
         [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}
            [];
          tApp
            (tConstruct
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}
               1 []) [tVar "b"];
          tApp
            (tConstruct
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |}
               0 [])
            [tInd
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}
               []]]])). *)

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
 
(* trialTerm = Inductive fooCon : nat -> nat -> nat -> nat -> Prop :=
 | cstrCon : forall a b c d,  f1 a = f2 b  -> fooCon a b c d. *)
Definition trialTerm : term :=
 (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} [])
   [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} [];
    tApp (tConst (MPfile ["animationFullExProof"], "f1") []) [tVar "a"];
    tApp (tConst (MPfile ["animationFullExProof"], "f2") []) [tVar "b"]]).

 


(* trial2 = Inductive fooCon : nat -> nat -> nat -> nat -> Prop :=
 | cstrCon : forall a b c d,  [1 ; S c]  = [S b ; d]  -> fooCon a b c d.
*)

Definition trial2 : term :=
(tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} [])
   [tApp
      (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} [])
      [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} []];
    tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1 [])
      [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} [];
       tApp
         (tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} 1
            [])
         [tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} 0
            []];
       tApp
         (tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1
            [])
         [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}
            [];
          tApp
            (tConstruct
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}
               1 []) [tVar "c"];
          tApp
            (tConstruct
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |}
               0 [])
            [tInd
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}
               []]]];
    tApp
      (tConstruct
         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1 [])
      [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} [];
       tApp
         (tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} 1
            []) [tVar "b"];
       tApp
         (tConstruct
            {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |} 1
            [])
         [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}
            []; tVar "d";
          tApp
            (tConstruct
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "list"); inductive_ind := 0 |}
               0 [])
            [tInd
               {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}
               []]]]]).




Compute (deconTypeConGen'' (deConConj1 trialTerm) (deConConj2 trialTerm) 10). 

(* Fixpoint makeConj (l1 : list (list term)) : list term :=
 match l1 with
  | nil => nil
  | [_h] => nil
  | [tVar str1] :: ([tVar str2] :: t) => (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} [])
   [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} [];
    tVar str1; tVar str2]) :: (makeConj t)
  
  
  | [tVar str1] :: ([tApp (tConstruct
                         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} 1
                            []) y] :: t) => 
                              (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} [])
                              [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} [];
                              tVar str1;
                              tApp
                                (tConstruct
                                    {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} 1 [])
                                         y]) :: makeConj t
  
  
  |([tApp (tConstruct
                         {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} 1
                            []) y] :: ([tVar str1] :: t)) => 
                            (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} [])
                              [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} [];
                              tVar str1;
                              tApp
                                (tConstruct
                                    {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} 1 [])
                                         y]) :: makeConj t
  
  
  | ([h1]) :: (([h2]) :: t) =>
                          (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} [])
                          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} [];
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
                          (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |} [])
                          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} [];
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
 
MetaRocq Quote Definition t := (fun x => match x with
                                        | S c => Some c
                                        | _ => None
                                       end).
MetaRocq Run (t' <- DB.undeBruijn t ;; tmPrint t'). 


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




(* Pattern match for 0 element list

MetaRocq Quote Definition u0 := (fun myList => match myList with
                                                | []  =>  Some myList 
                                                | y :: l => None
                                                
                                                end).                                              
(* MetaRocq Run (t''' <- DB.undeBruijn t'' ;; tmPrint t'''). *)

Print u0.

(* Pattern match for 1 element list *)
MetaRocq Quote Definition u1 := (fun myList => match myList with
                                                | []  =>  None 
                                                | y0 :: l0 => match l0 with
                                                             | [] => Some myList
                                                             | y :: l => None
                                                             end 
                                                
                                                end).
Print u1.


(* Pattern match for 2 element list *)
MetaRocq Quote Definition u2 := (fun myList => match myList with
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


(* MetaRocq Run (u2' <- DB.undeBruijn u2 ;; tmPrint u2').  *)



(* Compare u0 and u1 and u2 *) 

MetaRocq Quote Definition t2 := (fun m P (PO : P 0) (PS : forall n, P (S n)) => 
                                   match m as n return P n with
                                    | 0 => PO
                                    | S n => PS n
                                    end).
(* MetaRocq Run (t2' <- DB.undeBruijn t2 ;; tmPrint t2').  *)

Print bcontext.


(* (fun x => match x with
                                        | mycr1 a  =>  a 
                                        | _ => 0
                                       end). *)
                                       
 *)                                      

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
        puinst := [];
        pparams := [];
        pcontext := [{| binder_name := nNamed "x"; binder_relevance := Relevant |}];
        preturn := <%nat%>
      |} (tVar "x")
      [{|
         bcontext := [{| binder_name := nNamed "a"; binder_relevance := Relevant |}];
         bbody := tVar "a"
       |};
       {|
         bcontext := [{| binder_name := nNamed "n"; binder_relevance := Relevant |}];
         bbody := <% O %>
       |}])).




Inductive baz : nat -> myType -> string -> Prop :=
 | bazCon : forall (a : nat), forall (x : myType), forall (b : string), mycr1 b a = x -> baz a x b.  (*RHS of equality not v imp*)
 
Print TemplateMonad.

MetaRocq Quote Recursively Definition bazTerm := baz.

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

MetaRocq Quote Definition con3 := (fun x => match x with
                                                | mycr1 a b  =>  Some (a, b)
                                                | _ => None
                                               end).
Print con3. 

MetaRocq Run (animate <? baz ?>).

Fixpoint lstPatternmatch {A : Type} (n : nat) (x : (list A)) : option (list A) :=
 match n with
 | 0 => match x with 
        | [] => Some x
        | _ => None
        end
 
 | S m => match x with
          | [] => None
          | h :: t =>
              let r := lstPatternmatch m t in
              match r with
              | Some l' => Some (h :: l')
              | None => None
              end
           end                         
  end.


Compute (lstPatternmatch 4 [1 ; 2 ; 3 ; 4]).



MetaRocq Run (t <- DB.deBruijn (tLambda {| binder_name := nNamed "v2"%bs; binder_relevance := Relevant |}
            (tInd {| inductive_mind := (MPfile ["typeConNest2"%bs], "myType"%bs); inductive_ind := 0 |} [])
            (tCase
               {| ci_ind := {| inductive_mind := (MPfile ["typeConNest2"%bs], "myType"%bs); inductive_ind := 0 |}; ci_npar := 0; ci_relevance := Relevant |}
               {|
                 puinst := [];
                 pparams := [];
                 pcontext := [{| binder_name := nNamed "v2"%bs; binder_relevance := Relevant |}];
                 preturn := tApp <% @option %> [<%bool%>]
               |}
               (tVar "v2"%bs)
               [{|
                  bcontext :=
                    [{| binder_name := nNamed "v5"%bs; binder_relevance := Relevant |}; {| binder_name := nNamed "v4"%bs; binder_relevance := Relevant |}];
                  bbody :=
                    tCase
                      {|
                        ci_ind := {| inductive_mind := (MPfile ["typeConNest2"%bs], "myType'"%bs); inductive_ind := 0 |};
                        ci_npar := 0;
                        ci_relevance := Relevant
                      |}
                      {|
                        puinst := [];
                        pparams := [];
                        pcontext := [{| binder_name := nNamed "v4"%bs; binder_relevance := Relevant |}];
                        preturn := <% option bool %>
                      |} (tVar "v4"%bs)
                      [{|
                         bcontext := [{| binder_name := nNamed "v6"%bs; binder_relevance := Relevant |}];
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
                               pcontext := [{| binder_name := nNamed "v5"%bs; binder_relevance := Relevant |}];
                               preturn := <% option bool %>
                             |} (tVar "v5"%bs)
                             [{|
                                bcontext := [];
                                bbody := <% Some true %>
                              |};
                              {|
                                bcontext := [{| binder_name := nNamed "v7"%bs; binder_relevance := Relevant |}];
                                bbody := <% Some true %>
                              |}]
                       |};
                       {|
                         bcontext := [{| binder_name := nNamed "n1"%bs; binder_relevance := Relevant |}];
                         bbody := <% Some true %>
                       |}]
                |};
                {|
                  bcontext := [];
                  bbody := <% Some true %>
                |}])) ;; tmEval all t >>= tmPrint).
